/-
Copyright (c) 2026 Elliot Glazer and NFNotWPP contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elliot Glazer and NFNotWPP contributors
-/

module

public import LeanPool.NFWeakPartition.Certificates.NAR4C061C001Block001

/-! Nominal proof certificates grouped in dependency order. -/


public section

/-! Certificates from `NAR4C061C001Part003`. -/


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

/-- Checked nominal proof certificate identified upstream as `nb061_split_alpha_0000`. -/
@[expose]
noncomputable def nb061SplitAlpha0000 (x : Var) (r : Var) (a : Var) :
    TAlphaWff
      [((nb061AlphaDummy021), (nb061AlphaDummy024 r a)),
        ((nb061AlphaDummy020), (nb061AlphaDummy023 r a)),
        ((nb061AlphaDummy019), (nb061AlphaDummy022 r a)),
        ((nb061AlphaDummy017), (nb061AlphaDummy018 r a)),
        ((nb061AlphaDummy013), (nb061AlphaDummy015 r a)),
        ((nb061AlphaDummy014), (nb061AlphaDummy016 r a)),
        ((nb061AlphaDummy006), (nb061AlphaDummy008 r a)),
        ((nb061AlphaDummy005), (nb061AlphaDummy007 r a)),
        ((nb061AlphaDummy011), (nb061AlphaDummy012 r a)),
        ((nb061AlphaDummy009), (nb061AlphaDummy010 r a)),
        ((nb061AlphaDummy000), a), ((nb061AlphaDummy001), r),
        ((nb061AlphaDummy003), (nb061AlphaDummy004 x r a))]
      (Wff.imp (Wff.classEq
          (synCin (Class.cv (nb061AlphaDummy020)) (Class.cv (nb061AlphaDummy021)))
          (synC0)) (Wff.neg (Wff.classEq (Class.cv (nb061AlphaDummy019))
            (synCun (Class.cv (nb061AlphaDummy020)) (Class.cv (nb061AlphaDummy021))))))
      (Wff.imp (Wff.classEq (synCin (Class.cv (nb061AlphaDummy023 r a))
            (Class.cv (nb061AlphaDummy024 r a))) (synC0)) (Wff.neg
          (Wff.classEq (Class.cv (nb061AlphaDummy022 r a))
            (synCun (Class.cv (nb061AlphaDummy023 r a))
              (Class.cv (nb061AlphaDummy024 r a)))))) :=
  (TAlphaWff.imp (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.neg (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (Nat.ne_of_lt (mem_lt_freshVar (nb061_support_mem_0018) 0))
                          (Nat.ne_of_lt (mem_lt_freshVar (nb061_support_mem_0019 r a) 0))
                          (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb061_support_mem_0016) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb061_support_mem_0017 r a) 0))
                            (TAlphaVar.there (freshVar_injective
                                (((Class.cv (nb061AlphaDummy013))).fv ∪ ((synC1c)).fv)
                                (by decide)) (freshVar_injective
                                (((Class.cv (nb061AlphaDummy015 r a))).fv ∪ ((synC1c)).fv)
                                (by decide)) (TAlphaVar.here _ _ _))))))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (Nat.ne_of_lt (mem_lt_freshVar (nb061_support_mem_0022) 0))
                          (Nat.ne_of_lt (mem_lt_freshVar (nb061_support_mem_0023 r a) 0))
                          (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb061_support_mem_0020) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb061_support_mem_0021 r a) 0))
                            (TAlphaVar.here _ _ _)))))))))
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.neg (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (Nat.ne_of_lt (mem_lt_freshVar (nb061_support_mem_0018) 0))
                          (Nat.ne_of_lt (mem_lt_freshVar (nb061_support_mem_0019 r a) 0))
                          (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb061_support_mem_0016) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb061_support_mem_0017 r a) 0))
                            (TAlphaVar.there (freshVar_injective
                                (((Class.cv (nb061AlphaDummy013))).fv ∪ ((synC1c)).fv)
                                (by decide)) (freshVar_injective
                                (((Class.cv (nb061AlphaDummy015 r a))).fv ∪ ((synC1c)).fv)
                                (by decide)) (TAlphaVar.here _ _ _))))))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (Nat.ne_of_lt (mem_lt_freshVar (nb061_support_mem_0022) 0))
                          (Nat.ne_of_lt (mem_lt_freshVar (nb061_support_mem_0023 r a) 0))
                          (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb061_support_mem_0020) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb061_support_mem_0021 r a) 0))
                            (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.reflOfClosed
        [((nb061AlphaDummy021), (nb061AlphaDummy024 r a)),
          ((nb061AlphaDummy020), (nb061AlphaDummy023 r a)),
          ((nb061AlphaDummy019), (nb061AlphaDummy022 r a)),
          ((nb061AlphaDummy017), (nb061AlphaDummy018 r a)),
          ((nb061AlphaDummy013), (nb061AlphaDummy015 r a)),
          ((nb061AlphaDummy014), (nb061AlphaDummy016 r a)),
          ((nb061AlphaDummy006), (nb061AlphaDummy008 r a)),
          ((nb061AlphaDummy005), (nb061AlphaDummy007 r a)),
          ((nb061AlphaDummy011), (nb061AlphaDummy012 r a)),
          ((nb061AlphaDummy009), (nb061AlphaDummy010 r a)),
          ((nb061AlphaDummy000), a), ((nb061AlphaDummy001), r),
          ((nb061AlphaDummy003), (nb061AlphaDummy004 x r a))]
        (synC0) (by simp only [fv_syn_c0]))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv
          (TAlphaVar.there
            (freshVar_injective (((Class.cv (nb061AlphaDummy013))).fv ∪ ((synC1c)).fv)
              (by decide)) (freshVar_injective
              (((Class.cv (nb061AlphaDummy015 r a))).fv ∪ ((synC1c)).fv) (by decide))
            (TAlphaVar.there (freshVar_injective
                (((Class.cv (nb061AlphaDummy013))).fv ∪ ((synC1c)).fv) (by decide))
              (freshVar_injective (((Class.cv (nb061AlphaDummy015 r a))).fv ∪ ((synC1c)).fv)
                (by decide)) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg
            (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb061_support_mem_0026) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb061_support_mem_0027 r a) 0))
                            (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar (nb061_support_mem_0024) 0))
                              (Nat.ne_of_lt (mem_lt_freshVar (nb061_support_mem_0025 r a) 0))
                              (TAlphaVar.there (freshVar_injective
                                  (((Class.cv (nb061AlphaDummy013))).fv ∪ ((synC1c)).fv)
                                  (by decide)) (freshVar_injective
                                  (((Class.cv (nb061AlphaDummy015 r a))).fv ∪ ((synC1c)).fv)
                                  (by decide)) (TAlphaVar.here _ _ _))))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb061_support_mem_0026) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb061_support_mem_0027 r a) 0))
                            (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar (nb061_support_mem_0024) 0))
                              (Nat.ne_of_lt (mem_lt_freshVar (nb061_support_mem_0025 r a) 0))
                              (TAlphaVar.there (freshVar_injective
                                  (((Class.cv (nb061AlphaDummy013))).fv ∪ ((synC1c)).fv)
                                  (by decide)) (freshVar_injective
                                  (((Class.cv (nb061AlphaDummy015 r a))).fv ∪ ((synC1c)).fv)
                                  (by decide)) (TAlphaVar.here _ _ _))))))))))
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                  (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb061_support_mem_0030) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb061_support_mem_0031 r a) 0))
                            (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar (nb061_support_mem_0028) 0))
                              (Nat.ne_of_lt (mem_lt_freshVar (nb061_support_mem_0029 r a) 0))
                              (TAlphaVar.here _ _ _)))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb061_support_mem_0030) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb061_support_mem_0031 r a) 0))
                            (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar (nb061_support_mem_0028) 0))
                              (Nat.ne_of_lt (mem_lt_freshVar (nb061_support_mem_0029 r a) 0))
                              (TAlphaVar.here _ _ _)))))))))))))))

/-- Checked nominal proof certificate identified upstream as `nb061_split_alpha_0001`. -/
@[expose]
noncomputable def nb061SplitAlpha0001 (x : Var) (r : Var) (a : Var) (dv_a_r : a ≠ r) :
    TAlphaWff
      [((nb061AlphaDummy006), (nb061AlphaDummy008 r a)),
        ((nb061AlphaDummy005), (nb061AlphaDummy007 r a)),
        ((nb061AlphaDummy011), (nb061AlphaDummy012 r a)),
        ((nb061AlphaDummy009), (nb061AlphaDummy010 r a)),
        ((nb061AlphaDummy000), a), ((nb061AlphaDummy001), r),
        ((nb061AlphaDummy003), (nb061AlphaDummy004 x r a))]
      (Wff.imp (Wff.classMem (Class.cv (nb061AlphaDummy006))
          (Class.cv (nb061AlphaDummy001))) (Wff.neg
          (Wff.classEq (Class.cv (nb061AlphaDummy005))
            (synCphi (Class.cv (nb061AlphaDummy006))))))
      (Wff.imp (Wff.classMem (Class.cv (nb061AlphaDummy008 r a)) (Class.cv r)) (Wff.neg
          (Wff.classEq (Class.cv (nb061AlphaDummy007 r a))
            (synCphi (Class.cv (nb061AlphaDummy008 r a)))))) :=
  (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb061_support_mem_0004) 1))
          (Nat.ne_of_lt (mem_lt_freshVar (nb061_support_mem_0006 r a) 1))
          (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb061_support_mem_0004) 0))
            (Nat.ne_of_lt (mem_lt_freshVar (nb061_support_mem_0006 r a) 0))
            (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb061_support_mem_0008) 0))
              (Nat.ne_of_lt (mem_lt_freshVar (nb061_support_mem_0009 r a) 0))
              (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb061_support_mem_0005) 0))
                (Nat.ne_of_lt (mem_lt_freshVar (nb061_support_mem_0007 r a) 0))
                (TAlphaVar.there (freshVar_injective ((∅ : Finset Var)) (by decide))
                  (Ne.symm dv_a_r) (TAlphaVar.here _ _ _)))))))) (TAlphaWff.neg
      (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective
              (((Class.cv (nb061AlphaDummy001))).fv ∪
                ((Class.cv (nb061AlphaDummy000))).fv) (by decide))
            (freshVar_injective (((Class.cv r)).fv ∪ ((Class.cv a)).fv) (by decide))
            (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                  (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb061_support_mem_0010) 0))
                    (Nat.ne_of_lt (mem_lt_freshVar (nb061_support_mem_0011 r a) 0))
                    (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb061_support_mem_0010) 1))
                      (Nat.ne_of_lt (mem_lt_freshVar (nb061_support_mem_0011 r a) 1))
                      (TAlphaVar.here _ _ _))))) (TAlphaWff.classEq (TAlphaClass.cv
                  (TAlphaVar.there (freshVar_injective (((Class.cv (nb061AlphaDummy006))).fv)
                      (by decide))
                    (freshVar_injective (((Class.cv (nb061AlphaDummy008 r a))).fv)
                      (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp
                    (TAlphaWff.neg (TAlphaWff.conj
                        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                          (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
                                  (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                                    (TAlphaVar.there (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb061_support_mem_0014) 1))
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb061_support_mem_0015 r a) 1))
                                      (TAlphaVar.there (Nat.ne_of_lt
        (mem_lt_freshVar (nb061_support_mem_0014) 0)) (Nat.ne_of_lt
        (mem_lt_freshVar (nb061_support_mem_0015 r a) 0)) (TAlphaVar.there (Nat.ne_of_lt
        (mem_lt_freshVar (nb061_support_mem_0012) 0)) (Nat.ne_of_lt
        (mem_lt_freshVar (nb061_support_mem_0013 r a) 0)) (TAlphaVar.here _ _ _))))))
                                (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
                                      (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                      (TAlphaClass.reflOfClosed [((nb061AlphaDummy021),
        (nb061AlphaDummy024 r a)), ((nb061AlphaDummy020), (nb061AlphaDummy023 r a)),
        ((nb061AlphaDummy019), (nb061AlphaDummy022 r a)), ((nb061AlphaDummy017),
        (nb061AlphaDummy018 r a)), ((nb061AlphaDummy013), (nb061AlphaDummy015 r a)),
        ((nb061AlphaDummy014), (nb061AlphaDummy016 r a)), ((nb061AlphaDummy006),
        (nb061AlphaDummy008 r a)), ((nb061AlphaDummy005), (nb061AlphaDummy007 r a)),
        ((nb061AlphaDummy011), (nb061AlphaDummy012 r a)), ((nb061AlphaDummy009),
        (nb061AlphaDummy010 r a)), ((nb061AlphaDummy000), a),
        ((nb061AlphaDummy001), r), ((nb061AlphaDummy003), (nb061AlphaDummy004 x r a))]
                                        (synC1c) (by simp only [fv_syn_c1c])))
                                    (TAlphaWff.neg (nb061SplitAlpha0000 x r a))))))))
                        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar (nb061_support_mem_0012) 0))
                              (Nat.ne_of_lt (mem_lt_freshVar (nb061_support_mem_0013 r a) 0))
                              (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
                            [((nb061AlphaDummy017), (nb061AlphaDummy018 r a)),
                              ((nb061AlphaDummy013), (nb061AlphaDummy015 r a)),
                              ((nb061AlphaDummy014), (nb061AlphaDummy016 r a)),
                              ((nb061AlphaDummy006), (nb061AlphaDummy008 r a)),
                              ((nb061AlphaDummy005), (nb061AlphaDummy007 r a)),
                              ((nb061AlphaDummy011), (nb061AlphaDummy012 r a)),
                              ((nb061AlphaDummy009), (nb061AlphaDummy010 r a)),
                              ((nb061AlphaDummy000), a), ((nb061AlphaDummy001), r),
                              ((nb061AlphaDummy003), (nb061AlphaDummy004 x r a))]
                            (synCnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb061_support_mem_0012) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb061_support_mem_0013 r a) 0))
                            (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.classMem
                          (TAlphaClass.cv (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar (nb061_support_mem_0012) 0))
                              (Nat.ne_of_lt (mem_lt_freshVar (nb061_support_mem_0013 r a) 0))
                              (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
                            [((nb061AlphaDummy017), (nb061AlphaDummy018 r a)),
                              ((nb061AlphaDummy013), (nb061AlphaDummy015 r a)),
                              ((nb061AlphaDummy014), (nb061AlphaDummy016 r a)),
                              ((nb061AlphaDummy006), (nb061AlphaDummy008 r a)),
                              ((nb061AlphaDummy005), (nb061AlphaDummy007 r a)),
                              ((nb061AlphaDummy011), (nb061AlphaDummy012 r a)),
                              ((nb061AlphaDummy009), (nb061AlphaDummy010 r a)),
                              ((nb061AlphaDummy000), a), ((nb061AlphaDummy001), r),
                              ((nb061AlphaDummy003), (nb061AlphaDummy004 x r a))]
                            (synCnnc) (by simp only [fv_syn_cnnc]))))))))))))))

/-- Checked nominal proof certificate identified upstream as `nb061_split_alpha_0002`. -/
@[expose]
noncomputable def nb061SplitAlpha0002 (x : Var) (r : Var) (a : Var) :
    TAlphaWff
      [((nb061AlphaDummy021), (nb061AlphaDummy024 r a)),
        ((nb061AlphaDummy020), (nb061AlphaDummy023 r a)),
        ((nb061AlphaDummy019), (nb061AlphaDummy022 r a)),
        ((nb061AlphaDummy017), (nb061AlphaDummy018 r a)),
        ((nb061AlphaDummy013), (nb061AlphaDummy015 r a)),
        ((nb061AlphaDummy014), (nb061AlphaDummy016 r a)),
        ((nb061AlphaDummy039), (nb061AlphaDummy040 r a)),
        ((nb061AlphaDummy037), (nb061AlphaDummy038 r a)),
        ((nb061AlphaDummy006), (nb061AlphaDummy008 r a)),
        ((nb061AlphaDummy005), (nb061AlphaDummy007 r a)),
        ((nb061AlphaDummy035), (nb061AlphaDummy036 r a)),
        ((nb061AlphaDummy009), (nb061AlphaDummy010 r a)),
        ((nb061AlphaDummy000), a), ((nb061AlphaDummy001), r),
        ((nb061AlphaDummy003), (nb061AlphaDummy004 x r a))]
      (Wff.imp (Wff.classEq
          (synCin (Class.cv (nb061AlphaDummy020)) (Class.cv (nb061AlphaDummy021)))
          (synC0)) (Wff.neg (Wff.classEq (Class.cv (nb061AlphaDummy019))
            (synCun (Class.cv (nb061AlphaDummy020)) (Class.cv (nb061AlphaDummy021))))))
      (Wff.imp (Wff.classEq (synCin (Class.cv (nb061AlphaDummy023 r a))
            (Class.cv (nb061AlphaDummy024 r a))) (synC0)) (Wff.neg
          (Wff.classEq (Class.cv (nb061AlphaDummy022 r a))
            (synCun (Class.cv (nb061AlphaDummy023 r a))
              (Class.cv (nb061AlphaDummy024 r a)))))) :=
  (TAlphaWff.imp (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.neg (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (Nat.ne_of_lt (mem_lt_freshVar (nb061_support_mem_0018) 0))
                          (Nat.ne_of_lt (mem_lt_freshVar (nb061_support_mem_0019 r a) 0))
                          (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb061_support_mem_0016) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb061_support_mem_0017 r a) 0))
                            (TAlphaVar.there (freshVar_injective
                                (((Class.cv (nb061AlphaDummy013))).fv ∪ ((synC1c)).fv)
                                (by decide)) (freshVar_injective
                                (((Class.cv (nb061AlphaDummy015 r a))).fv ∪ ((synC1c)).fv)
                                (by decide)) (TAlphaVar.here _ _ _))))))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (Nat.ne_of_lt (mem_lt_freshVar (nb061_support_mem_0022) 0))
                          (Nat.ne_of_lt (mem_lt_freshVar (nb061_support_mem_0023 r a) 0))
                          (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb061_support_mem_0020) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb061_support_mem_0021 r a) 0))
                            (TAlphaVar.here _ _ _)))))))))
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.neg (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (Nat.ne_of_lt (mem_lt_freshVar (nb061_support_mem_0018) 0))
                          (Nat.ne_of_lt (mem_lt_freshVar (nb061_support_mem_0019 r a) 0))
                          (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb061_support_mem_0016) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb061_support_mem_0017 r a) 0))
                            (TAlphaVar.there (freshVar_injective
                                (((Class.cv (nb061AlphaDummy013))).fv ∪ ((synC1c)).fv)
                                (by decide)) (freshVar_injective
                                (((Class.cv (nb061AlphaDummy015 r a))).fv ∪ ((synC1c)).fv)
                                (by decide)) (TAlphaVar.here _ _ _))))))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (Nat.ne_of_lt (mem_lt_freshVar (nb061_support_mem_0022) 0))
                          (Nat.ne_of_lt (mem_lt_freshVar (nb061_support_mem_0023 r a) 0))
                          (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb061_support_mem_0020) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb061_support_mem_0021 r a) 0))
                            (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.reflOfClosed
        [((nb061AlphaDummy021), (nb061AlphaDummy024 r a)),
          ((nb061AlphaDummy020), (nb061AlphaDummy023 r a)),
          ((nb061AlphaDummy019), (nb061AlphaDummy022 r a)),
          ((nb061AlphaDummy017), (nb061AlphaDummy018 r a)),
          ((nb061AlphaDummy013), (nb061AlphaDummy015 r a)),
          ((nb061AlphaDummy014), (nb061AlphaDummy016 r a)),
          ((nb061AlphaDummy039), (nb061AlphaDummy040 r a)),
          ((nb061AlphaDummy037), (nb061AlphaDummy038 r a)),
          ((nb061AlphaDummy006), (nb061AlphaDummy008 r a)),
          ((nb061AlphaDummy005), (nb061AlphaDummy007 r a)),
          ((nb061AlphaDummy035), (nb061AlphaDummy036 r a)),
          ((nb061AlphaDummy009), (nb061AlphaDummy010 r a)),
          ((nb061AlphaDummy000), a), ((nb061AlphaDummy001), r),
          ((nb061AlphaDummy003), (nb061AlphaDummy004 x r a))]
        (synC0) (by simp only [fv_syn_c0]))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv
          (TAlphaVar.there
            (freshVar_injective (((Class.cv (nb061AlphaDummy013))).fv ∪ ((synC1c)).fv)
              (by decide)) (freshVar_injective
              (((Class.cv (nb061AlphaDummy015 r a))).fv ∪ ((synC1c)).fv) (by decide))
            (TAlphaVar.there (freshVar_injective
                (((Class.cv (nb061AlphaDummy013))).fv ∪ ((synC1c)).fv) (by decide))
              (freshVar_injective (((Class.cv (nb061AlphaDummy015 r a))).fv ∪ ((synC1c)).fv)
                (by decide)) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg
            (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb061_support_mem_0026) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb061_support_mem_0027 r a) 0))
                            (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar (nb061_support_mem_0024) 0))
                              (Nat.ne_of_lt (mem_lt_freshVar (nb061_support_mem_0025 r a) 0))
                              (TAlphaVar.there (freshVar_injective
                                  (((Class.cv (nb061AlphaDummy013))).fv ∪ ((synC1c)).fv)
                                  (by decide)) (freshVar_injective
                                  (((Class.cv (nb061AlphaDummy015 r a))).fv ∪ ((synC1c)).fv)
                                  (by decide)) (TAlphaVar.here _ _ _))))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb061_support_mem_0026) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb061_support_mem_0027 r a) 0))
                            (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar (nb061_support_mem_0024) 0))
                              (Nat.ne_of_lt (mem_lt_freshVar (nb061_support_mem_0025 r a) 0))
                              (TAlphaVar.there (freshVar_injective
                                  (((Class.cv (nb061AlphaDummy013))).fv ∪ ((synC1c)).fv)
                                  (by decide)) (freshVar_injective
                                  (((Class.cv (nb061AlphaDummy015 r a))).fv ∪ ((synC1c)).fv)
                                  (by decide)) (TAlphaVar.here _ _ _))))))))))
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                  (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb061_support_mem_0030) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb061_support_mem_0031 r a) 0))
                            (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar (nb061_support_mem_0028) 0))
                              (Nat.ne_of_lt (mem_lt_freshVar (nb061_support_mem_0029 r a) 0))
                              (TAlphaVar.here _ _ _)))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb061_support_mem_0030) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb061_support_mem_0031 r a) 0))
                            (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar (nb061_support_mem_0028) 0))
                              (Nat.ne_of_lt (mem_lt_freshVar (nb061_support_mem_0029 r a) 0))
                              (TAlphaVar.here _ _ _)))))))))))))))


end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired

end

/-! Certificates from `NAR4C061C001Part004`. -/


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

/-- Checked nominal proof certificate identified upstream as `nb061_split_alpha_0003`. -/
@[expose]
noncomputable def nb061SplitAlpha0003 (x : Var) (r : Var) (a : Var) :
    TAlphaWff
      [((nb061AlphaDummy039), (nb061AlphaDummy040 r a)),
        ((nb061AlphaDummy037), (nb061AlphaDummy038 r a)),
        ((nb061AlphaDummy006), (nb061AlphaDummy008 r a)),
        ((nb061AlphaDummy005), (nb061AlphaDummy007 r a)),
        ((nb061AlphaDummy035), (nb061AlphaDummy036 r a)),
        ((nb061AlphaDummy009), (nb061AlphaDummy010 r a)),
        ((nb061AlphaDummy000), a), ((nb061AlphaDummy001), r),
        ((nb061AlphaDummy003), (nb061AlphaDummy004 x r a))]
      (Wff.imp (Wff.classMem (Class.cv (nb061AlphaDummy039))
          (synCphi (Class.cv (nb061AlphaDummy006)))) (Wff.neg
          (Wff.classMem (Class.cv (nb061AlphaDummy039))
            (synCphi (Class.cv (nb061AlphaDummy006))))))
      (Wff.imp (Wff.classMem (Class.cv (nb061AlphaDummy040 r a))
          (synCphi (Class.cv (nb061AlphaDummy008 r a)))) (Wff.neg
          (Wff.classMem (Class.cv (nb061AlphaDummy040 r a))
            (synCphi (Class.cv (nb061AlphaDummy008 r a)))))) :=
  (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.ex (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb061_support_mem_0010) 0))
                  (Nat.ne_of_lt (mem_lt_freshVar (nb061_support_mem_0011 r a) 0))
                  (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb061_support_mem_0010) 1))
                    (Nat.ne_of_lt (mem_lt_freshVar (nb061_support_mem_0011 r a) 1))
                    (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb061_support_mem_0040) 0))
                      (Nat.ne_of_lt (mem_lt_freshVar (nb061_support_mem_0041 r a) 0))
                      (TAlphaVar.there
                        (Nat.ne_of_lt (mem_lt_freshVar (nb061_support_mem_0038) 0))
                        (Nat.ne_of_lt (mem_lt_freshVar (nb061_support_mem_0039 r a) 0))
                        (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
                (TAlphaVar.there (freshVar_injective (((Class.cv (nb061AlphaDummy006))).fv)
                    (by decide))
                  (freshVar_injective (((Class.cv (nb061AlphaDummy008 r a))).fv) (by decide))
                  (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp (TAlphaWff.neg
                    (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb061_support_mem_0014) 1))
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb061_support_mem_0015 r a) 1))
                                    (TAlphaVar.there (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb061_support_mem_0014) 0))
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb061_support_mem_0015 r a) 0))
                                      (TAlphaVar.there (Nat.ne_of_lt
        (mem_lt_freshVar (nb061_support_mem_0012) 0)) (Nat.ne_of_lt
        (mem_lt_freshVar (nb061_support_mem_0013 r a) 0)) (TAlphaVar.here _ _ _))))))
                              (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
                                    (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                    (TAlphaClass.reflOfClosed [((nb061AlphaDummy021),
        (nb061AlphaDummy024 r a)), ((nb061AlphaDummy020), (nb061AlphaDummy023 r a)),
                                        ((nb061AlphaDummy019), (nb061AlphaDummy022 r a)),
                                        ((nb061AlphaDummy017), (nb061AlphaDummy018 r a)),
                                        ((nb061AlphaDummy013), (nb061AlphaDummy015 r a)),
                                        ((nb061AlphaDummy014), (nb061AlphaDummy016 r a)),
                                        ((nb061AlphaDummy039), (nb061AlphaDummy040 r a)),
                                        ((nb061AlphaDummy037), (nb061AlphaDummy038 r a)),
                                        ((nb061AlphaDummy006), (nb061AlphaDummy008 r a)),
                                        ((nb061AlphaDummy005), (nb061AlphaDummy007 r a)),
                                        ((nb061AlphaDummy035), (nb061AlphaDummy036 r a)),
                                        ((nb061AlphaDummy009), (nb061AlphaDummy010 r a)),
                                        ((nb061AlphaDummy000), a),
                                        ((nb061AlphaDummy001), r), ((nb061AlphaDummy003),
        (nb061AlphaDummy004 x r a))] (synC1c) (by simp only [fv_syn_c1c])))
                                  (TAlphaWff.neg (nb061SplitAlpha0002 x r a))))))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb061_support_mem_0012) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb061_support_mem_0013 r a) 0))
                            (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
                          [((nb061AlphaDummy017), (nb061AlphaDummy018 r a)),
                            ((nb061AlphaDummy013), (nb061AlphaDummy015 r a)),
                            ((nb061AlphaDummy014), (nb061AlphaDummy016 r a)),
                            ((nb061AlphaDummy039), (nb061AlphaDummy040 r a)),
                            ((nb061AlphaDummy037), (nb061AlphaDummy038 r a)),
                            ((nb061AlphaDummy006), (nb061AlphaDummy008 r a)),
                            ((nb061AlphaDummy005), (nb061AlphaDummy007 r a)),
                            ((nb061AlphaDummy035), (nb061AlphaDummy036 r a)),
                            ((nb061AlphaDummy009), (nb061AlphaDummy010 r a)),
                            ((nb061AlphaDummy000), a), ((nb061AlphaDummy001), r),
                            ((nb061AlphaDummy003), (nb061AlphaDummy004 x r a))]
                          (synCnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (Nat.ne_of_lt (mem_lt_freshVar (nb061_support_mem_0012) 0))
                          (Nat.ne_of_lt (mem_lt_freshVar (nb061_support_mem_0013 r a) 0))
                          (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.classMem
                        (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb061_support_mem_0012) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb061_support_mem_0013 r a) 0))
                            (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
                          [((nb061AlphaDummy017), (nb061AlphaDummy018 r a)),
                            ((nb061AlphaDummy013), (nb061AlphaDummy015 r a)),
                            ((nb061AlphaDummy014), (nb061AlphaDummy016 r a)),
                            ((nb061AlphaDummy039), (nb061AlphaDummy040 r a)),
                            ((nb061AlphaDummy037), (nb061AlphaDummy038 r a)),
                            ((nb061AlphaDummy006), (nb061AlphaDummy008 r a)),
                            ((nb061AlphaDummy005), (nb061AlphaDummy007 r a)),
                            ((nb061AlphaDummy035), (nb061AlphaDummy036 r a)),
                            ((nb061AlphaDummy009), (nb061AlphaDummy010 r a)),
                            ((nb061AlphaDummy000), a), ((nb061AlphaDummy001), r),
                            ((nb061AlphaDummy003), (nb061AlphaDummy004 x r a))]
                          (synCnnc) (by simp only [fv_syn_cnnc])))))))))))) (TAlphaWff.neg
      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.ex
            (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                (TAlphaClass.cv (TAlphaVar.there
                    (Nat.ne_of_lt (mem_lt_freshVar (nb061_support_mem_0010) 0))
                    (Nat.ne_of_lt (mem_lt_freshVar (nb061_support_mem_0011 r a) 0))
                    (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb061_support_mem_0010) 1))
                      (Nat.ne_of_lt (mem_lt_freshVar (nb061_support_mem_0011 r a) 1))
                      (TAlphaVar.there
                        (Nat.ne_of_lt (mem_lt_freshVar (nb061_support_mem_0040) 0))
                        (Nat.ne_of_lt (mem_lt_freshVar (nb061_support_mem_0041 r a) 0))
                        (TAlphaVar.there
                          (Nat.ne_of_lt (mem_lt_freshVar (nb061_support_mem_0038) 0))
                          (Nat.ne_of_lt (mem_lt_freshVar (nb061_support_mem_0039 r a) 0))
                          (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
                  (TAlphaVar.there (freshVar_injective (((Class.cv (nb061AlphaDummy006))).fv)
                      (by decide))
                    (freshVar_injective (((Class.cv (nb061AlphaDummy008 r a))).fv)
                      (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp
                    (TAlphaWff.neg (TAlphaWff.conj
                        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                          (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
                                  (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                                    (TAlphaVar.there (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb061_support_mem_0014) 1))
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb061_support_mem_0015 r a) 1))
                                      (TAlphaVar.there (Nat.ne_of_lt
        (mem_lt_freshVar (nb061_support_mem_0014) 0)) (Nat.ne_of_lt
        (mem_lt_freshVar (nb061_support_mem_0015 r a) 0)) (TAlphaVar.there (Nat.ne_of_lt
        (mem_lt_freshVar (nb061_support_mem_0012) 0)) (Nat.ne_of_lt
        (mem_lt_freshVar (nb061_support_mem_0013 r a) 0)) (TAlphaVar.here _ _ _))))))
                                (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
                                      (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                      (TAlphaClass.reflOfClosed [((nb061AlphaDummy021),
        (nb061AlphaDummy024 r a)), ((nb061AlphaDummy020), (nb061AlphaDummy023 r a)),
        ((nb061AlphaDummy019), (nb061AlphaDummy022 r a)), ((nb061AlphaDummy017),
        (nb061AlphaDummy018 r a)), ((nb061AlphaDummy013), (nb061AlphaDummy015 r a)),
        ((nb061AlphaDummy014), (nb061AlphaDummy016 r a)), ((nb061AlphaDummy039),
        (nb061AlphaDummy040 r a)), ((nb061AlphaDummy037), (nb061AlphaDummy038 r a)),
        ((nb061AlphaDummy006), (nb061AlphaDummy008 r a)), ((nb061AlphaDummy005),
        (nb061AlphaDummy007 r a)), ((nb061AlphaDummy035), (nb061AlphaDummy036 r a)),
        ((nb061AlphaDummy009), (nb061AlphaDummy010 r a)), ((nb061AlphaDummy000), a),
        ((nb061AlphaDummy001), r), ((nb061AlphaDummy003), (nb061AlphaDummy004 x r a))]
                                        (synC1c) (by simp only [fv_syn_c1c])))
                                    (TAlphaWff.neg (nb061SplitAlpha0002 x r a))))))))
                        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar (nb061_support_mem_0012) 0))
                              (Nat.ne_of_lt (mem_lt_freshVar (nb061_support_mem_0013 r a) 0))
                              (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
                            [((nb061AlphaDummy017), (nb061AlphaDummy018 r a)),
                              ((nb061AlphaDummy013), (nb061AlphaDummy015 r a)),
                              ((nb061AlphaDummy014), (nb061AlphaDummy016 r a)),
                              ((nb061AlphaDummy039), (nb061AlphaDummy040 r a)),
                              ((nb061AlphaDummy037), (nb061AlphaDummy038 r a)),
                              ((nb061AlphaDummy006), (nb061AlphaDummy008 r a)),
                              ((nb061AlphaDummy005), (nb061AlphaDummy007 r a)),
                              ((nb061AlphaDummy035), (nb061AlphaDummy036 r a)),
                              ((nb061AlphaDummy009), (nb061AlphaDummy010 r a)),
                              ((nb061AlphaDummy000), a), ((nb061AlphaDummy001), r),
                              ((nb061AlphaDummy003), (nb061AlphaDummy004 x r a))]
                            (synCnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb061_support_mem_0012) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb061_support_mem_0013 r a) 0))
                            (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.classMem
                          (TAlphaClass.cv (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar (nb061_support_mem_0012) 0))
                              (Nat.ne_of_lt (mem_lt_freshVar (nb061_support_mem_0013 r a) 0))
                              (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
                            [((nb061AlphaDummy017), (nb061AlphaDummy018 r a)),
                              ((nb061AlphaDummy013), (nb061AlphaDummy015 r a)),
                              ((nb061AlphaDummy014), (nb061AlphaDummy016 r a)),
                              ((nb061AlphaDummy039), (nb061AlphaDummy040 r a)),
                              ((nb061AlphaDummy037), (nb061AlphaDummy038 r a)),
                              ((nb061AlphaDummy006), (nb061AlphaDummy008 r a)),
                              ((nb061AlphaDummy005), (nb061AlphaDummy007 r a)),
                              ((nb061AlphaDummy035), (nb061AlphaDummy036 r a)),
                              ((nb061AlphaDummy009), (nb061AlphaDummy010 r a)),
                              ((nb061AlphaDummy000), a), ((nb061AlphaDummy001), r),
                              ((nb061AlphaDummy003), (nb061AlphaDummy004 x r a))]
                            (synCnnc) (by simp only [fv_syn_cnnc]))))))))))))))

/-- Checked nominal proof certificate identified upstream as `nb061_split_alpha_0004`. -/
@[expose]
noncomputable def nb061SplitAlpha0004 (x : Var) (r : Var) (a : Var) (dv_a_r : a ≠ r) :
    TAlphaWff
      [((nb061AlphaDummy000), a), ((nb061AlphaDummy001), r),
        ((nb061AlphaDummy003), (nb061AlphaDummy004 x r a))]
      (Wff.classEq (Class.cv (nb061AlphaDummy003))
        (synCop (Class.cv (nb061AlphaDummy001)) (Class.cv (nb061AlphaDummy000))))
      (Wff.classEq (Class.cv (nb061AlphaDummy004 x r a))
        (synCop (Class.cv r) (Class.cv a))) :=
  (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there
        (Ne.symm (Nat.ne_of_lt (mem_lt_freshVar (nb061_support_mem_0002) 0)))
        (Ne.symm (Nat.ne_of_lt (mem_lt_freshVar (nb061_support_mem_0003 x r a) 0)))
        (TAlphaVar.there (Ne.symm (Nat.ne_of_lt (mem_lt_freshVar (nb061_support_mem_0000) 0)))
          (Ne.symm (Nat.ne_of_lt (mem_lt_freshVar (nb061_support_mem_0001 x r a) 0)))
          (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
          (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
              (TAlphaWff.neg (TAlphaWff.conj
                  (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                      (TAlphaWff.ex (TAlphaWff.neg (nb061SplitAlpha0001 x r a dv_a_r)))))
                  (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                      (TAlphaWff.ex (TAlphaWff.neg (nb061SplitAlpha0001 x r a dv_a_r)))))))))
          (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
              (TAlphaWff.neg (TAlphaWff.conj
                  (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                      (TAlphaWff.ex (TAlphaWff.conj
                          (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                            (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb061_support_mem_0032) 1)) (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb061_support_mem_0034 r a) 1))
                                (TAlphaVar.there (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb061_support_mem_0032) 0)) (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb061_support_mem_0034 r a) 0))
                                  (TAlphaVar.there (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb061_support_mem_0036) 0))
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb061_support_mem_0037 r a) 0))
                                    (TAlphaVar.there (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb061_support_mem_0033) 0))
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb061_support_mem_0035 r a) 0))
                                      (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq
                            (TAlphaClass.cv (TAlphaVar.there (freshVar_injective
                                  (((Class.cv (nb061AlphaDummy001))).fv ∪
                                    ((Class.cv (nb061AlphaDummy000))).fv) (by decide))
                                (freshVar_injective
                                  (((Class.cv r)).fv ∪ ((Class.cv a)).fv) (by decide))
                                (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.neg
                                (TAlphaWff.conj (TAlphaWff.classMem
                                    (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                                      (TAlphaWff.neg
                                        (TAlphaWff.neg (nb061SplitAlpha0003 x r a)))))
                                  (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                    (TAlphaClass.reflOfClosed [((nb061AlphaDummy037),
        (nb061AlphaDummy038 r a)), ((nb061AlphaDummy006), (nb061AlphaDummy008 r a)),
                                        ((nb061AlphaDummy005), (nb061AlphaDummy007 r a)),
                                        ((nb061AlphaDummy035), (nb061AlphaDummy036 r a)),
                                        ((nb061AlphaDummy009), (nb061AlphaDummy010 r a)),
                                        ((nb061AlphaDummy000), a),
                                        ((nb061AlphaDummy001), r), ((nb061AlphaDummy003),
        (nb061AlphaDummy004 x r a))] (synCcompl (synCsn (synC0c))) (by
                                        simp only [fv_syn_ccompl, fv_syn_csn,
                                          fv_syn_c0c])))))))))))
                  (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                      (TAlphaWff.ex (TAlphaWff.conj
                          (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                            (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb061_support_mem_0032) 1)) (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb061_support_mem_0034 r a) 1))
                                (TAlphaVar.there (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb061_support_mem_0032) 0)) (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb061_support_mem_0034 r a) 0))
                                  (TAlphaVar.there (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb061_support_mem_0036) 0))
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb061_support_mem_0037 r a) 0))
                                    (TAlphaVar.there (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb061_support_mem_0033) 0))
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb061_support_mem_0035 r a) 0))
                                      (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq
                            (TAlphaClass.cv (TAlphaVar.there (freshVar_injective
                                  (((Class.cv (nb061AlphaDummy001))).fv ∪
                                    ((Class.cv (nb061AlphaDummy000))).fv) (by decide))
                                (freshVar_injective
                                  (((Class.cv r)).fv ∪ ((Class.cv a)).fv) (by decide))
                                (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.neg
                                (TAlphaWff.conj (TAlphaWff.classMem
                                    (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                                      (TAlphaWff.neg
                                        (TAlphaWff.neg (nb061SplitAlpha0003 x r a)))))
                                  (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                    (TAlphaClass.reflOfClosed [((nb061AlphaDummy037),
        (nb061AlphaDummy038 r a)), ((nb061AlphaDummy006), (nb061AlphaDummy008 r a)),
                                        ((nb061AlphaDummy005), (nb061AlphaDummy007 r a)),
                                        ((nb061AlphaDummy035), (nb061AlphaDummy036 r a)),
                                        ((nb061AlphaDummy009), (nb061AlphaDummy010 r a)),
                                        ((nb061AlphaDummy000), a),
                                        ((nb061AlphaDummy001), r), ((nb061AlphaDummy003),
        (nb061AlphaDummy004 x r a))] (synCcompl (synCsn (synC0c))) (by
                                        simp only [fv_syn_ccompl, fv_syn_csn,
                                          fv_syn_c0c])))))))))))))))))))

/-- Checked nominal proof certificate identified upstream as `nb061_split_alpha_0005`. -/
@[expose]
noncomputable def nb061SplitAlpha0005 (x : Var) (r : Var) (a : Var) :
    TAlphaWff
      [((nb061AlphaDummy057), (nb061AlphaDummy060 x)),
        ((nb061AlphaDummy056), (nb061AlphaDummy059 x)),
        ((nb061AlphaDummy055), (nb061AlphaDummy058 x)),
        ((nb061AlphaDummy053), (nb061AlphaDummy054 x)),
        ((nb061AlphaDummy049), (nb061AlphaDummy051 x)),
        ((nb061AlphaDummy050), (nb061AlphaDummy052 x)),
        ((nb061AlphaDummy042), (nb061AlphaDummy044 x)),
        ((nb061AlphaDummy041), (nb061AlphaDummy043 x)),
        ((nb061AlphaDummy047), (nb061AlphaDummy048 x)),
        ((nb061AlphaDummy045), (nb061AlphaDummy046 x)),
        ((nb061AlphaDummy002), x), ((nb061AlphaDummy000), a),
        ((nb061AlphaDummy001), r),
        ((nb061AlphaDummy003), (nb061AlphaDummy004 x r a))]
      (Wff.imp (Wff.classEq
          (synCin (Class.cv (nb061AlphaDummy056)) (Class.cv (nb061AlphaDummy057)))
          (synC0)) (Wff.neg (Wff.classEq (Class.cv (nb061AlphaDummy055))
            (synCun (Class.cv (nb061AlphaDummy056)) (Class.cv (nb061AlphaDummy057))))))
      (Wff.imp (Wff.classEq (synCin (Class.cv (nb061AlphaDummy059 x))
            (Class.cv (nb061AlphaDummy060 x))) (synC0)) (Wff.neg
          (Wff.classEq (Class.cv (nb061AlphaDummy058 x))
            (synCun (Class.cv (nb061AlphaDummy059 x))
              (Class.cv (nb061AlphaDummy060 x)))))) :=
  (TAlphaWff.imp (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.neg (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (Nat.ne_of_lt (mem_lt_freshVar (nb061_support_mem_0056) 0))
                          (Nat.ne_of_lt (mem_lt_freshVar (nb061_support_mem_0057 x) 0))
                          (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb061_support_mem_0054) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb061_support_mem_0055 x) 0))
                            (TAlphaVar.there (freshVar_injective
                                (((Class.cv (nb061AlphaDummy049))).fv ∪ ((synC1c)).fv)
                                (by decide)) (freshVar_injective
                                (((Class.cv (nb061AlphaDummy051 x))).fv ∪ ((synC1c)).fv)
                                (by decide)) (TAlphaVar.here _ _ _))))))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (Nat.ne_of_lt (mem_lt_freshVar (nb061_support_mem_0060) 0))
                          (Nat.ne_of_lt (mem_lt_freshVar (nb061_support_mem_0061 x) 0))
                          (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb061_support_mem_0058) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb061_support_mem_0059 x) 0))
                            (TAlphaVar.here _ _ _)))))))))
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.neg (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (Nat.ne_of_lt (mem_lt_freshVar (nb061_support_mem_0056) 0))
                          (Nat.ne_of_lt (mem_lt_freshVar (nb061_support_mem_0057 x) 0))
                          (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb061_support_mem_0054) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb061_support_mem_0055 x) 0))
                            (TAlphaVar.there (freshVar_injective
                                (((Class.cv (nb061AlphaDummy049))).fv ∪ ((synC1c)).fv)
                                (by decide)) (freshVar_injective
                                (((Class.cv (nb061AlphaDummy051 x))).fv ∪ ((synC1c)).fv)
                                (by decide)) (TAlphaVar.here _ _ _))))))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (Nat.ne_of_lt (mem_lt_freshVar (nb061_support_mem_0060) 0))
                          (Nat.ne_of_lt (mem_lt_freshVar (nb061_support_mem_0061 x) 0))
                          (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb061_support_mem_0058) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb061_support_mem_0059 x) 0))
                            (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.reflOfClosed
        [((nb061AlphaDummy057), (nb061AlphaDummy060 x)),
          ((nb061AlphaDummy056), (nb061AlphaDummy059 x)),
          ((nb061AlphaDummy055), (nb061AlphaDummy058 x)),
          ((nb061AlphaDummy053), (nb061AlphaDummy054 x)),
          ((nb061AlphaDummy049), (nb061AlphaDummy051 x)),
          ((nb061AlphaDummy050), (nb061AlphaDummy052 x)),
          ((nb061AlphaDummy042), (nb061AlphaDummy044 x)),
          ((nb061AlphaDummy041), (nb061AlphaDummy043 x)),
          ((nb061AlphaDummy047), (nb061AlphaDummy048 x)),
          ((nb061AlphaDummy045), (nb061AlphaDummy046 x)),
          ((nb061AlphaDummy002), x), ((nb061AlphaDummy000), a),
          ((nb061AlphaDummy001), r),
          ((nb061AlphaDummy003), (nb061AlphaDummy004 x r a))]
        (synC0) (by simp only [fv_syn_c0]))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv
          (TAlphaVar.there
            (freshVar_injective (((Class.cv (nb061AlphaDummy049))).fv ∪ ((synC1c)).fv)
              (by decide)) (freshVar_injective
              (((Class.cv (nb061AlphaDummy051 x))).fv ∪ ((synC1c)).fv) (by decide))
            (TAlphaVar.there (freshVar_injective
                (((Class.cv (nb061AlphaDummy049))).fv ∪ ((synC1c)).fv) (by decide))
              (freshVar_injective
                (((Class.cv (nb061AlphaDummy051 x))).fv ∪ ((synC1c)).fv) (by decide))
              (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                  (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb061_support_mem_0064) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb061_support_mem_0065 x) 0))
                            (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar (nb061_support_mem_0062) 0))
                              (Nat.ne_of_lt (mem_lt_freshVar (nb061_support_mem_0063 x) 0))
                              (TAlphaVar.there (freshVar_injective
                                  (((Class.cv (nb061AlphaDummy049))).fv ∪ ((synC1c)).fv)
                                  (by decide)) (freshVar_injective
                                  (((Class.cv (nb061AlphaDummy051 x))).fv ∪ ((synC1c)).fv)
                                  (by decide)) (TAlphaVar.here _ _ _))))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb061_support_mem_0064) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb061_support_mem_0065 x) 0))
                            (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar (nb061_support_mem_0062) 0))
                              (Nat.ne_of_lt (mem_lt_freshVar (nb061_support_mem_0063 x) 0))
                              (TAlphaVar.there (freshVar_injective
                                  (((Class.cv (nb061AlphaDummy049))).fv ∪ ((synC1c)).fv)
                                  (by decide)) (freshVar_injective
                                  (((Class.cv (nb061AlphaDummy051 x))).fv ∪ ((synC1c)).fv)
                                  (by decide)) (TAlphaVar.here _ _ _))))))))))
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                  (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb061_support_mem_0068) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb061_support_mem_0069 x) 0))
                            (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar (nb061_support_mem_0066) 0))
                              (Nat.ne_of_lt (mem_lt_freshVar (nb061_support_mem_0067 x) 0))
                              (TAlphaVar.here _ _ _)))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb061_support_mem_0068) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb061_support_mem_0069 x) 0))
                            (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar (nb061_support_mem_0066) 0))
                              (Nat.ne_of_lt (mem_lt_freshVar (nb061_support_mem_0067 x) 0))
                              (TAlphaVar.here _ _ _)))))))))))))))

/-- Checked nominal proof certificate identified upstream as `nb061_split_alpha_0006`. -/
@[expose]
noncomputable def nb061SplitAlpha0006 (x : Var) (r : Var) (a : Var) :
    TAlphaWff
      [((nb061AlphaDummy042), (nb061AlphaDummy044 x)),
        ((nb061AlphaDummy041), (nb061AlphaDummy043 x)),
        ((nb061AlphaDummy047), (nb061AlphaDummy048 x)),
        ((nb061AlphaDummy045), (nb061AlphaDummy046 x)),
        ((nb061AlphaDummy002), x), ((nb061AlphaDummy000), a),
        ((nb061AlphaDummy001), r),
        ((nb061AlphaDummy003), (nb061AlphaDummy004 x r a))]
      (Wff.imp (Wff.classMem (Class.cv (nb061AlphaDummy042))
          (Class.cv (nb061AlphaDummy002))) (Wff.neg
          (Wff.classEq (Class.cv (nb061AlphaDummy041))
            (synCphi (Class.cv (nb061AlphaDummy042))))))
      (Wff.imp (Wff.classMem (Class.cv (nb061AlphaDummy044 x)) (Class.cv x)) (Wff.neg
          (Wff.classEq (Class.cv (nb061AlphaDummy043 x))
            (synCphi (Class.cv (nb061AlphaDummy044 x)))))) :=
  (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb061_support_mem_0042) 1))
          (Nat.ne_of_lt (mem_lt_freshVar (nb061_support_mem_0044 x) 1))
          (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb061_support_mem_0042) 0))
            (Nat.ne_of_lt (mem_lt_freshVar (nb061_support_mem_0044 x) 0))
            (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb061_support_mem_0046) 0))
              (Nat.ne_of_lt (mem_lt_freshVar (nb061_support_mem_0047 x) 0))
              (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb061_support_mem_0043) 0))
                (Nat.ne_of_lt (mem_lt_freshVar (nb061_support_mem_0045 x) 0))
                (TAlphaVar.here _ _ _))))))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv
          (TAlphaVar.there (freshVar_injective (((Class.cv (nb061AlphaDummy002))).fv ∪
                ((Class.cv (nb061AlphaDummy002))).fv) (by decide))
            (freshVar_injective (((Class.cv x)).fv ∪ ((Class.cv x)).fv) (by decide))
            (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                  (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb061_support_mem_0048) 0))
                    (Nat.ne_of_lt (mem_lt_freshVar (nb061_support_mem_0049 x) 0))
                    (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb061_support_mem_0048) 1))
                      (Nat.ne_of_lt (mem_lt_freshVar (nb061_support_mem_0049 x) 1))
                      (TAlphaVar.here _ _ _))))) (TAlphaWff.classEq (TAlphaClass.cv
                  (TAlphaVar.there (freshVar_injective (((Class.cv (nb061AlphaDummy042))).fv)
                      (by decide))
                    (freshVar_injective (((Class.cv (nb061AlphaDummy044 x))).fv) (by decide))
                    (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp (TAlphaWff.neg
                      (TAlphaWff.conj
                        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                          (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
                                  (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                                    (TAlphaVar.there (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb061_support_mem_0052) 1))
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb061_support_mem_0053 x) 1))
                                      (TAlphaVar.there (Nat.ne_of_lt
        (mem_lt_freshVar (nb061_support_mem_0052) 0)) (Nat.ne_of_lt
        (mem_lt_freshVar (nb061_support_mem_0053 x) 0)) (TAlphaVar.there (Nat.ne_of_lt
        (mem_lt_freshVar (nb061_support_mem_0050) 0)) (Nat.ne_of_lt
        (mem_lt_freshVar (nb061_support_mem_0051 x) 0)) (TAlphaVar.here _ _ _))))))
                                (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
                                      (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                      (TAlphaClass.reflOfClosed [((nb061AlphaDummy057),
        (nb061AlphaDummy060 x)), ((nb061AlphaDummy056), (nb061AlphaDummy059 x)),
        ((nb061AlphaDummy055), (nb061AlphaDummy058 x)), ((nb061AlphaDummy053),
        (nb061AlphaDummy054 x)), ((nb061AlphaDummy049), (nb061AlphaDummy051 x)),
        ((nb061AlphaDummy050), (nb061AlphaDummy052 x)), ((nb061AlphaDummy042),
        (nb061AlphaDummy044 x)), ((nb061AlphaDummy041), (nb061AlphaDummy043 x)),
        ((nb061AlphaDummy047), (nb061AlphaDummy048 x)), ((nb061AlphaDummy045),
        (nb061AlphaDummy046 x)), ((nb061AlphaDummy002), x), ((nb061AlphaDummy000), a),
        ((nb061AlphaDummy001), r), ((nb061AlphaDummy003), (nb061AlphaDummy004 x r a))]
                                        (synC1c) (by simp only [fv_syn_c1c])))
                                    (TAlphaWff.neg (nb061SplitAlpha0005 x r a))))))))
                        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar (nb061_support_mem_0050) 0))
                              (Nat.ne_of_lt (mem_lt_freshVar (nb061_support_mem_0051 x) 0))
                              (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
                            [((nb061AlphaDummy053), (nb061AlphaDummy054 x)),
                              ((nb061AlphaDummy049), (nb061AlphaDummy051 x)),
                              ((nb061AlphaDummy050), (nb061AlphaDummy052 x)),
                              ((nb061AlphaDummy042), (nb061AlphaDummy044 x)),
                              ((nb061AlphaDummy041), (nb061AlphaDummy043 x)),
                              ((nb061AlphaDummy047), (nb061AlphaDummy048 x)),
                              ((nb061AlphaDummy045), (nb061AlphaDummy046 x)),
                              ((nb061AlphaDummy002), x), ((nb061AlphaDummy000), a),
                              ((nb061AlphaDummy001), r),
                              ((nb061AlphaDummy003), (nb061AlphaDummy004 x r a))]
                            (synCnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb061_support_mem_0050) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb061_support_mem_0051 x) 0))
                            (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.classMem
                          (TAlphaClass.cv (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar (nb061_support_mem_0050) 0))
                              (Nat.ne_of_lt (mem_lt_freshVar (nb061_support_mem_0051 x) 0))
                              (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
                            [((nb061AlphaDummy053), (nb061AlphaDummy054 x)),
                              ((nb061AlphaDummy049), (nb061AlphaDummy051 x)),
                              ((nb061AlphaDummy050), (nb061AlphaDummy052 x)),
                              ((nb061AlphaDummy042), (nb061AlphaDummy044 x)),
                              ((nb061AlphaDummy041), (nb061AlphaDummy043 x)),
                              ((nb061AlphaDummy047), (nb061AlphaDummy048 x)),
                              ((nb061AlphaDummy045), (nb061AlphaDummy046 x)),
                              ((nb061AlphaDummy002), x), ((nb061AlphaDummy000), a),
                              ((nb061AlphaDummy001), r),
                              ((nb061AlphaDummy003), (nb061AlphaDummy004 x r a))]
                            (synCnnc) (by simp only [fv_syn_cnnc]))))))))))))))


end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired

end

/-! Certificates from `NAR4C061C001Part005`. -/


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

/-- Checked nominal proof certificate identified upstream as `nb061_split_alpha_0007`. -/
@[expose]
noncomputable def nb061SplitAlpha0007 (x : Var) (r : Var) (a : Var) :
    TAlphaWff
      [((nb061AlphaDummy057), (nb061AlphaDummy060 x)),
        ((nb061AlphaDummy056), (nb061AlphaDummy059 x)),
        ((nb061AlphaDummy055), (nb061AlphaDummy058 x)),
        ((nb061AlphaDummy053), (nb061AlphaDummy054 x)),
        ((nb061AlphaDummy049), (nb061AlphaDummy051 x)),
        ((nb061AlphaDummy050), (nb061AlphaDummy052 x)),
        ((nb061AlphaDummy075), (nb061AlphaDummy076 x)),
        ((nb061AlphaDummy073), (nb061AlphaDummy074 x)),
        ((nb061AlphaDummy042), (nb061AlphaDummy044 x)),
        ((nb061AlphaDummy041), (nb061AlphaDummy043 x)),
        ((nb061AlphaDummy071), (nb061AlphaDummy072 x)),
        ((nb061AlphaDummy045), (nb061AlphaDummy046 x)),
        ((nb061AlphaDummy002), x), ((nb061AlphaDummy000), a),
        ((nb061AlphaDummy001), r),
        ((nb061AlphaDummy003), (nb061AlphaDummy004 x r a))]
      (Wff.imp (Wff.classEq
          (synCin (Class.cv (nb061AlphaDummy056)) (Class.cv (nb061AlphaDummy057)))
          (synC0)) (Wff.neg (Wff.classEq (Class.cv (nb061AlphaDummy055))
            (synCun (Class.cv (nb061AlphaDummy056)) (Class.cv (nb061AlphaDummy057))))))
      (Wff.imp (Wff.classEq (synCin (Class.cv (nb061AlphaDummy059 x))
            (Class.cv (nb061AlphaDummy060 x))) (synC0)) (Wff.neg
          (Wff.classEq (Class.cv (nb061AlphaDummy058 x))
            (synCun (Class.cv (nb061AlphaDummy059 x))
              (Class.cv (nb061AlphaDummy060 x)))))) :=
  (TAlphaWff.imp (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.neg (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (Nat.ne_of_lt (mem_lt_freshVar (nb061_support_mem_0056) 0))
                          (Nat.ne_of_lt (mem_lt_freshVar (nb061_support_mem_0057 x) 0))
                          (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb061_support_mem_0054) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb061_support_mem_0055 x) 0))
                            (TAlphaVar.there (freshVar_injective
                                (((Class.cv (nb061AlphaDummy049))).fv ∪ ((synC1c)).fv)
                                (by decide)) (freshVar_injective
                                (((Class.cv (nb061AlphaDummy051 x))).fv ∪ ((synC1c)).fv)
                                (by decide)) (TAlphaVar.here _ _ _))))))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (Nat.ne_of_lt (mem_lt_freshVar (nb061_support_mem_0060) 0))
                          (Nat.ne_of_lt (mem_lt_freshVar (nb061_support_mem_0061 x) 0))
                          (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb061_support_mem_0058) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb061_support_mem_0059 x) 0))
                            (TAlphaVar.here _ _ _)))))))))
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.neg (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (Nat.ne_of_lt (mem_lt_freshVar (nb061_support_mem_0056) 0))
                          (Nat.ne_of_lt (mem_lt_freshVar (nb061_support_mem_0057 x) 0))
                          (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb061_support_mem_0054) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb061_support_mem_0055 x) 0))
                            (TAlphaVar.there (freshVar_injective
                                (((Class.cv (nb061AlphaDummy049))).fv ∪ ((synC1c)).fv)
                                (by decide)) (freshVar_injective
                                (((Class.cv (nb061AlphaDummy051 x))).fv ∪ ((synC1c)).fv)
                                (by decide)) (TAlphaVar.here _ _ _))))))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (Nat.ne_of_lt (mem_lt_freshVar (nb061_support_mem_0060) 0))
                          (Nat.ne_of_lt (mem_lt_freshVar (nb061_support_mem_0061 x) 0))
                          (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb061_support_mem_0058) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb061_support_mem_0059 x) 0))
                            (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.reflOfClosed
        [((nb061AlphaDummy057), (nb061AlphaDummy060 x)),
          ((nb061AlphaDummy056), (nb061AlphaDummy059 x)),
          ((nb061AlphaDummy055), (nb061AlphaDummy058 x)),
          ((nb061AlphaDummy053), (nb061AlphaDummy054 x)),
          ((nb061AlphaDummy049), (nb061AlphaDummy051 x)),
          ((nb061AlphaDummy050), (nb061AlphaDummy052 x)),
          ((nb061AlphaDummy075), (nb061AlphaDummy076 x)),
          ((nb061AlphaDummy073), (nb061AlphaDummy074 x)),
          ((nb061AlphaDummy042), (nb061AlphaDummy044 x)),
          ((nb061AlphaDummy041), (nb061AlphaDummy043 x)),
          ((nb061AlphaDummy071), (nb061AlphaDummy072 x)),
          ((nb061AlphaDummy045), (nb061AlphaDummy046 x)),
          ((nb061AlphaDummy002), x), ((nb061AlphaDummy000), a),
          ((nb061AlphaDummy001), r),
          ((nb061AlphaDummy003), (nb061AlphaDummy004 x r a))]
        (synC0) (by simp only [fv_syn_c0]))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv
          (TAlphaVar.there
            (freshVar_injective (((Class.cv (nb061AlphaDummy049))).fv ∪ ((synC1c)).fv)
              (by decide)) (freshVar_injective
              (((Class.cv (nb061AlphaDummy051 x))).fv ∪ ((synC1c)).fv) (by decide))
            (TAlphaVar.there (freshVar_injective
                (((Class.cv (nb061AlphaDummy049))).fv ∪ ((synC1c)).fv) (by decide))
              (freshVar_injective
                (((Class.cv (nb061AlphaDummy051 x))).fv ∪ ((synC1c)).fv) (by decide))
              (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                  (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb061_support_mem_0064) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb061_support_mem_0065 x) 0))
                            (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar (nb061_support_mem_0062) 0))
                              (Nat.ne_of_lt (mem_lt_freshVar (nb061_support_mem_0063 x) 0))
                              (TAlphaVar.there (freshVar_injective
                                  (((Class.cv (nb061AlphaDummy049))).fv ∪ ((synC1c)).fv)
                                  (by decide)) (freshVar_injective
                                  (((Class.cv (nb061AlphaDummy051 x))).fv ∪ ((synC1c)).fv)
                                  (by decide)) (TAlphaVar.here _ _ _))))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb061_support_mem_0064) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb061_support_mem_0065 x) 0))
                            (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar (nb061_support_mem_0062) 0))
                              (Nat.ne_of_lt (mem_lt_freshVar (nb061_support_mem_0063 x) 0))
                              (TAlphaVar.there (freshVar_injective
                                  (((Class.cv (nb061AlphaDummy049))).fv ∪ ((synC1c)).fv)
                                  (by decide)) (freshVar_injective
                                  (((Class.cv (nb061AlphaDummy051 x))).fv ∪ ((synC1c)).fv)
                                  (by decide)) (TAlphaVar.here _ _ _))))))))))
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                  (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb061_support_mem_0068) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb061_support_mem_0069 x) 0))
                            (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar (nb061_support_mem_0066) 0))
                              (Nat.ne_of_lt (mem_lt_freshVar (nb061_support_mem_0067 x) 0))
                              (TAlphaVar.here _ _ _)))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb061_support_mem_0068) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb061_support_mem_0069 x) 0))
                            (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar (nb061_support_mem_0066) 0))
                              (Nat.ne_of_lt (mem_lt_freshVar (nb061_support_mem_0067 x) 0))
                              (TAlphaVar.here _ _ _)))))))))))))))

/-- Checked nominal proof certificate identified upstream as `nb061_split_alpha_0008`. -/
@[expose]
noncomputable def nb061SplitAlpha0008 (x : Var) (r : Var) (a : Var) :
    TAlphaWff
      [((nb061AlphaDummy075), (nb061AlphaDummy076 x)),
        ((nb061AlphaDummy073), (nb061AlphaDummy074 x)),
        ((nb061AlphaDummy042), (nb061AlphaDummy044 x)),
        ((nb061AlphaDummy041), (nb061AlphaDummy043 x)),
        ((nb061AlphaDummy071), (nb061AlphaDummy072 x)),
        ((nb061AlphaDummy045), (nb061AlphaDummy046 x)),
        ((nb061AlphaDummy002), x), ((nb061AlphaDummy000), a),
        ((nb061AlphaDummy001), r),
        ((nb061AlphaDummy003), (nb061AlphaDummy004 x r a))]
      (Wff.classMem (Class.cv (nb061AlphaDummy075))
        (synCphi (Class.cv (nb061AlphaDummy042))))
      (Wff.classMem (Class.cv (nb061AlphaDummy076 x))
        (synCphi (Class.cv (nb061AlphaDummy044 x)))) :=
  (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.ex
        (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
            (TAlphaClass.cv
              (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb061_support_mem_0048) 0))
                (Nat.ne_of_lt (mem_lt_freshVar (nb061_support_mem_0049 x) 0)) (TAlphaVar.there
                  (Nat.ne_of_lt (mem_lt_freshVar (nb061_support_mem_0048) 1))
                  (Nat.ne_of_lt (mem_lt_freshVar (nb061_support_mem_0049 x) 1)) (TAlphaVar.there
                    (Nat.ne_of_lt (mem_lt_freshVar (nb061_support_mem_0074) 0))
                    (Nat.ne_of_lt (mem_lt_freshVar (nb061_support_mem_0075 x) 0))
                    (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb061_support_mem_0072) 0))
                      (Nat.ne_of_lt (mem_lt_freshVar (nb061_support_mem_0073 x) 0))
                      (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
              (TAlphaVar.there
                (freshVar_injective (((Class.cv (nb061AlphaDummy042))).fv) (by decide))
                (freshVar_injective (((Class.cv (nb061AlphaDummy044 x))).fv) (by decide))
                (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp (TAlphaWff.neg
                  (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                      (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb061_support_mem_0052) 1)) (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb061_support_mem_0053 x) 1))
                                  (TAlphaVar.there (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb061_support_mem_0052) 0))
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb061_support_mem_0053 x) 0))
                                    (TAlphaVar.there (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb061_support_mem_0050) 0))
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb061_support_mem_0051 x) 0))
                                      (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
                                (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                  (TAlphaClass.reflOfClosed
                                    [((nb061AlphaDummy057), (nb061AlphaDummy060 x)),
                                      ((nb061AlphaDummy056), (nb061AlphaDummy059 x)),
                                      ((nb061AlphaDummy055), (nb061AlphaDummy058 x)),
                                      ((nb061AlphaDummy053), (nb061AlphaDummy054 x)),
                                      ((nb061AlphaDummy049), (nb061AlphaDummy051 x)),
                                      ((nb061AlphaDummy050), (nb061AlphaDummy052 x)),
                                      ((nb061AlphaDummy075), (nb061AlphaDummy076 x)),
                                      ((nb061AlphaDummy073), (nb061AlphaDummy074 x)),
                                      ((nb061AlphaDummy042), (nb061AlphaDummy044 x)),
                                      ((nb061AlphaDummy041), (nb061AlphaDummy043 x)),
                                      ((nb061AlphaDummy071), (nb061AlphaDummy072 x)),
                                      ((nb061AlphaDummy045), (nb061AlphaDummy046 x)),
                                      ((nb061AlphaDummy002), x),
                                      ((nb061AlphaDummy000), a),
                                      ((nb061AlphaDummy001), r), ((nb061AlphaDummy003),
                                        (nb061AlphaDummy004 x r a))]
                                    (synC1c) (by simp only [fv_syn_c1c])))
                                (TAlphaWff.neg (nb061SplitAlpha0007 x r a))))))))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there
                          (Nat.ne_of_lt (mem_lt_freshVar (nb061_support_mem_0050) 0))
                          (Nat.ne_of_lt (mem_lt_freshVar (nb061_support_mem_0051 x) 0))
                          (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
                        [((nb061AlphaDummy053), (nb061AlphaDummy054 x)),
                          ((nb061AlphaDummy049), (nb061AlphaDummy051 x)),
                          ((nb061AlphaDummy050), (nb061AlphaDummy052 x)),
                          ((nb061AlphaDummy075), (nb061AlphaDummy076 x)),
                          ((nb061AlphaDummy073), (nb061AlphaDummy074 x)),
                          ((nb061AlphaDummy042), (nb061AlphaDummy044 x)),
                          ((nb061AlphaDummy041), (nb061AlphaDummy043 x)),
                          ((nb061AlphaDummy071), (nb061AlphaDummy072 x)),
                          ((nb061AlphaDummy045), (nb061AlphaDummy046 x)),
                          ((nb061AlphaDummy002), x), ((nb061AlphaDummy000), a),
                          ((nb061AlphaDummy001), r),
                          ((nb061AlphaDummy003), (nb061AlphaDummy004 x r a))]
                        (synCnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
                  (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                      (TAlphaVar.there
                        (Nat.ne_of_lt (mem_lt_freshVar (nb061_support_mem_0050) 0))
                        (Nat.ne_of_lt (mem_lt_freshVar (nb061_support_mem_0051 x) 0))
                        (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.classMem
                      (TAlphaClass.cv (TAlphaVar.there
                          (Nat.ne_of_lt (mem_lt_freshVar (nb061_support_mem_0050) 0))
                          (Nat.ne_of_lt (mem_lt_freshVar (nb061_support_mem_0051 x) 0))
                          (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
                        [((nb061AlphaDummy053), (nb061AlphaDummy054 x)),
                          ((nb061AlphaDummy049), (nb061AlphaDummy051 x)),
                          ((nb061AlphaDummy050), (nb061AlphaDummy052 x)),
                          ((nb061AlphaDummy075), (nb061AlphaDummy076 x)),
                          ((nb061AlphaDummy073), (nb061AlphaDummy074 x)),
                          ((nb061AlphaDummy042), (nb061AlphaDummy044 x)),
                          ((nb061AlphaDummy041), (nb061AlphaDummy043 x)),
                          ((nb061AlphaDummy071), (nb061AlphaDummy072 x)),
                          ((nb061AlphaDummy045), (nb061AlphaDummy046 x)),
                          ((nb061AlphaDummy002), x), ((nb061AlphaDummy000), a),
                          ((nb061AlphaDummy001), r),
                          ((nb061AlphaDummy003), (nb061AlphaDummy004 x r a))]
                        (synCnnc) (by simp only [fv_syn_cnnc]))))))))))))

/-- Checked nominal proof certificate identified upstream as `nb061_split_alpha_0009`. -/
@[expose]
noncomputable def nb061SplitAlpha0009 (x : Var) (r : Var) (a : Var) (dv_a_r : a ≠ r)
    (dv_r_x : r ≠ x) :
    TAlphaWff
      [((nb061AlphaDummy002), x), ((nb061AlphaDummy000), a),
        ((nb061AlphaDummy001), r),
        ((nb061AlphaDummy003), (nb061AlphaDummy004 x r a))]
      (Wff.classMem
        (synCop (Class.cv (nb061AlphaDummy002)) (Class.cv (nb061AlphaDummy002)))
        (Class.cv (nb061AlphaDummy001)))
      (Wff.classMem (synCop (Class.cv x) (Class.cv x)) (Class.cv r)) :=
  (TAlphaWff.classMem (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
          (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
              (TAlphaWff.neg (TAlphaWff.conj
                  (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                      (TAlphaWff.ex (TAlphaWff.neg (nb061SplitAlpha0006 x r a)))))
                  (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                      (TAlphaWff.ex (TAlphaWff.neg (nb061SplitAlpha0006 x r a)))))))))
          (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
              (TAlphaWff.neg (TAlphaWff.conj
                  (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                      (TAlphaWff.ex (TAlphaWff.conj
                          (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                            (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb061_support_mem_0042) 1)) (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb061_support_mem_0044 x) 1))
                                (TAlphaVar.there (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb061_support_mem_0042) 0)) (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb061_support_mem_0044 x) 0))
                                  (TAlphaVar.there (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb061_support_mem_0070) 0))
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb061_support_mem_0071 x) 0))
                                    (TAlphaVar.there (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb061_support_mem_0043) 0))
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb061_support_mem_0045 x) 0))
                                      (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq
                            (TAlphaClass.cv (TAlphaVar.there (freshVar_injective
                                  (((Class.cv (nb061AlphaDummy002))).fv ∪
                                    ((Class.cv (nb061AlphaDummy002))).fv) (by decide))
                                (freshVar_injective
                                  (((Class.cv x)).fv ∪ ((Class.cv x)).fv) (by decide))
                                (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.neg
                                (TAlphaWff.conj (TAlphaWff.classMem
                                    (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                                      (TAlphaWff.neg
                                        (TAlphaWff.conj (nb061SplitAlpha0008 x r a)
        (nb061SplitAlpha0008 x r a))))) (TAlphaWff.classMem
                                    (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                    (TAlphaClass.reflOfClosed [((nb061AlphaDummy073),
        (nb061AlphaDummy074 x)), ((nb061AlphaDummy042), (nb061AlphaDummy044 x)),
                                        ((nb061AlphaDummy041), (nb061AlphaDummy043 x)),
                                        ((nb061AlphaDummy071), (nb061AlphaDummy072 x)),
                                        ((nb061AlphaDummy045), (nb061AlphaDummy046 x)),
                                        ((nb061AlphaDummy002), x),
                                        ((nb061AlphaDummy000), a),
                                        ((nb061AlphaDummy001), r), ((nb061AlphaDummy003),
        (nb061AlphaDummy004 x r a))] (synCcompl (synCsn (synC0c))) (by
                                        simp only [fv_syn_ccompl, fv_syn_csn,
                                          fv_syn_c0c])))))))))))
                  (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                      (TAlphaWff.ex (TAlphaWff.conj
                          (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                            (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb061_support_mem_0042) 1)) (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb061_support_mem_0044 x) 1))
                                (TAlphaVar.there (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb061_support_mem_0042) 0)) (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb061_support_mem_0044 x) 0))
                                  (TAlphaVar.there (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb061_support_mem_0070) 0))
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb061_support_mem_0071 x) 0))
                                    (TAlphaVar.there (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb061_support_mem_0043) 0))
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb061_support_mem_0045 x) 0))
                                      (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq
                            (TAlphaClass.cv (TAlphaVar.there (freshVar_injective
                                  (((Class.cv (nb061AlphaDummy002))).fv ∪
                                    ((Class.cv (nb061AlphaDummy002))).fv) (by decide))
                                (freshVar_injective
                                  (((Class.cv x)).fv ∪ ((Class.cv x)).fv) (by decide))
                                (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.neg
                                (TAlphaWff.conj (TAlphaWff.classMem
                                    (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                                      (TAlphaWff.neg
                                        (TAlphaWff.conj (nb061SplitAlpha0008 x r a)
        (nb061SplitAlpha0008 x r a))))) (TAlphaWff.classMem
                                    (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                    (TAlphaClass.reflOfClosed [((nb061AlphaDummy073),
        (nb061AlphaDummy074 x)), ((nb061AlphaDummy042), (nb061AlphaDummy044 x)),
                                        ((nb061AlphaDummy041), (nb061AlphaDummy043 x)),
                                        ((nb061AlphaDummy071), (nb061AlphaDummy072 x)),
                                        ((nb061AlphaDummy045), (nb061AlphaDummy046 x)),
                                        ((nb061AlphaDummy002), x),
                                        ((nb061AlphaDummy000), a),
                                        ((nb061AlphaDummy001), r), ((nb061AlphaDummy003),
        (nb061AlphaDummy004 x r a))] (synCcompl (synCsn (synC0c))) (by
                                        simp only [fv_syn_ccompl, fv_syn_csn,
                                          fv_syn_c0c])))))))))))))))))) (TAlphaClass.cv
      (TAlphaVar.there (freshVar_injective ((∅ : Finset Var)) (by decide)) dv_r_x
        (TAlphaVar.there (freshVar_injective ((∅ : Finset Var)) (by decide))
          (Ne.symm dv_a_r) (TAlphaVar.here _ _ _)))))

/-- Checked nominal proof certificate identified upstream as `nominal_df_ref`. -/
@[expose]
noncomputable def nominalDfRef (x : Var) (r : Var) (a : Var) (dv_a_r : a ≠ r)
    (dv_a_x : a ≠ x) (dv_r_x : r ≠ x) :
    Nominal.NPrf
      (.classEq (synCref)
        (synCopab r a (synWral x (.cv a) (synWbr (.cv x) (.cv r) (.cv x))))) :=
  by
  exact
    Nominal.alphaClassEq
      (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.ex
            (TAlphaWff.conj (nb061SplitAlpha0004 x r a dv_a_r) (TAlphaWff.all (TAlphaWff.imp
                  (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                      (TAlphaVar.there (freshVar_injective ((∅ : Finset Var)) (by decide))
                        dv_a_x (TAlphaVar.here _ _ _))))
                  (nb061SplitAlpha0009 x r a dv_a_r dv_r_x)))))))

end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired

end
