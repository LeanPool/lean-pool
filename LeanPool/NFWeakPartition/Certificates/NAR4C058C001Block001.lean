/-
Copyright (c) 2026 Elliot Glazer and NFNotWPP contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elliot Glazer and NFNotWPP contributors
-/

module

public import LeanPool.NFWeakPartition.AlphaSupport.NAR4C058C001Part002Stage1

/-! Nominal proof certificates grouped in dependency order. -/


public section

/-! Certificates from `NAR4C058C001Part002`. -/


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

/-- Checked nominal proof certificate identified upstream as `nb058_split_alpha_0000`. -/
@[expose]
noncomputable def nb058SplitAlpha0000 (x : Var) :
    TAlphaWff
      [((nb058AlphaDummy021), (nb058AlphaDummy024 x)),
        ((nb058AlphaDummy020), (nb058AlphaDummy023 x)),
        ((nb058AlphaDummy019), (nb058AlphaDummy022 x)),
        ((nb058AlphaDummy017), (nb058AlphaDummy018 x)),
        ((nb058AlphaDummy013), (nb058AlphaDummy015 x)),
        ((nb058AlphaDummy014), (nb058AlphaDummy016 x)),
        ((nb058AlphaDummy006), (nb058AlphaDummy008 x)),
        ((nb058AlphaDummy005), (nb058AlphaDummy007 x)),
        ((nb058AlphaDummy011), (nb058AlphaDummy012 x)),
        ((nb058AlphaDummy009), (nb058AlphaDummy010 x)),
        ((nb058AlphaDummy001), (nb058AlphaDummy002 x)),
        ((nb058AlphaDummy000), x),
        ((nb058AlphaDummy003), (nb058AlphaDummy004 x))]
      (Wff.imp (Wff.classEq
          (synCin (Class.cv (nb058AlphaDummy020)) (Class.cv (nb058AlphaDummy021)))
          (synC0)) (Wff.neg (Wff.classEq (Class.cv (nb058AlphaDummy019))
            (synCun (Class.cv (nb058AlphaDummy020)) (Class.cv (nb058AlphaDummy021))))))
      (Wff.imp (Wff.classEq (synCin (Class.cv (nb058AlphaDummy023 x))
            (Class.cv (nb058AlphaDummy024 x))) (synC0)) (Wff.neg
          (Wff.classEq (Class.cv (nb058AlphaDummy022 x))
            (synCun (Class.cv (nb058AlphaDummy023 x))
              (Class.cv (nb058AlphaDummy024 x)))))) :=
  (TAlphaWff.imp (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.neg (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (Nat.ne_of_lt (mem_lt_freshVar (nb058_support_mem_0020) 0))
                          (Nat.ne_of_lt (mem_lt_freshVar (nb058_support_mem_0021 x) 0))
                          (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb058_support_mem_0018) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb058_support_mem_0019 x) 0))
                            (TAlphaVar.there (freshVar_injective
                                (((Class.cv (nb058AlphaDummy013))).fv ∪ ((synC1c)).fv)
                                (by decide)) (freshVar_injective
                                (((Class.cv (nb058AlphaDummy015 x))).fv ∪ ((synC1c)).fv)
                                (by decide)) (TAlphaVar.here _ _ _))))))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (Nat.ne_of_lt (mem_lt_freshVar (nb058_support_mem_0024) 0))
                          (Nat.ne_of_lt (mem_lt_freshVar (nb058_support_mem_0025 x) 0))
                          (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb058_support_mem_0022) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb058_support_mem_0023 x) 0))
                            (TAlphaVar.here _ _ _)))))))))
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.neg (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (Nat.ne_of_lt (mem_lt_freshVar (nb058_support_mem_0020) 0))
                          (Nat.ne_of_lt (mem_lt_freshVar (nb058_support_mem_0021 x) 0))
                          (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb058_support_mem_0018) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb058_support_mem_0019 x) 0))
                            (TAlphaVar.there (freshVar_injective
                                (((Class.cv (nb058AlphaDummy013))).fv ∪ ((synC1c)).fv)
                                (by decide)) (freshVar_injective
                                (((Class.cv (nb058AlphaDummy015 x))).fv ∪ ((synC1c)).fv)
                                (by decide)) (TAlphaVar.here _ _ _))))))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (Nat.ne_of_lt (mem_lt_freshVar (nb058_support_mem_0024) 0))
                          (Nat.ne_of_lt (mem_lt_freshVar (nb058_support_mem_0025 x) 0))
                          (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb058_support_mem_0022) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb058_support_mem_0023 x) 0))
                            (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.reflOfClosed
        [((nb058AlphaDummy021), (nb058AlphaDummy024 x)),
          ((nb058AlphaDummy020), (nb058AlphaDummy023 x)),
          ((nb058AlphaDummy019), (nb058AlphaDummy022 x)),
          ((nb058AlphaDummy017), (nb058AlphaDummy018 x)),
          ((nb058AlphaDummy013), (nb058AlphaDummy015 x)),
          ((nb058AlphaDummy014), (nb058AlphaDummy016 x)),
          ((nb058AlphaDummy006), (nb058AlphaDummy008 x)),
          ((nb058AlphaDummy005), (nb058AlphaDummy007 x)),
          ((nb058AlphaDummy011), (nb058AlphaDummy012 x)),
          ((nb058AlphaDummy009), (nb058AlphaDummy010 x)),
          ((nb058AlphaDummy001), (nb058AlphaDummy002 x)), ((nb058AlphaDummy000), x),
          ((nb058AlphaDummy003), (nb058AlphaDummy004 x))]
        (synC0) (by simp only [fv_syn_c0]))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv
          (TAlphaVar.there
            (freshVar_injective (((Class.cv (nb058AlphaDummy013))).fv ∪ ((synC1c)).fv)
              (by decide)) (freshVar_injective
              (((Class.cv (nb058AlphaDummy015 x))).fv ∪ ((synC1c)).fv) (by decide))
            (TAlphaVar.there (freshVar_injective
                (((Class.cv (nb058AlphaDummy013))).fv ∪ ((synC1c)).fv) (by decide))
              (freshVar_injective
                (((Class.cv (nb058AlphaDummy015 x))).fv ∪ ((synC1c)).fv) (by decide))
              (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                  (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb058_support_mem_0028) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb058_support_mem_0029 x) 0))
                            (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar (nb058_support_mem_0026) 0))
                              (Nat.ne_of_lt (mem_lt_freshVar (nb058_support_mem_0027 x) 0))
                              (TAlphaVar.there (freshVar_injective
                                  (((Class.cv (nb058AlphaDummy013))).fv ∪ ((synC1c)).fv)
                                  (by decide)) (freshVar_injective
                                  (((Class.cv (nb058AlphaDummy015 x))).fv ∪ ((synC1c)).fv)
                                  (by decide)) (TAlphaVar.here _ _ _))))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb058_support_mem_0028) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb058_support_mem_0029 x) 0))
                            (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar (nb058_support_mem_0026) 0))
                              (Nat.ne_of_lt (mem_lt_freshVar (nb058_support_mem_0027 x) 0))
                              (TAlphaVar.there (freshVar_injective
                                  (((Class.cv (nb058AlphaDummy013))).fv ∪ ((synC1c)).fv)
                                  (by decide)) (freshVar_injective
                                  (((Class.cv (nb058AlphaDummy015 x))).fv ∪ ((synC1c)).fv)
                                  (by decide)) (TAlphaVar.here _ _ _))))))))))
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                  (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb058_support_mem_0032) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb058_support_mem_0033 x) 0))
                            (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar (nb058_support_mem_0030) 0))
                              (Nat.ne_of_lt (mem_lt_freshVar (nb058_support_mem_0031 x) 0))
                              (TAlphaVar.here _ _ _)))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb058_support_mem_0032) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb058_support_mem_0033 x) 0))
                            (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar (nb058_support_mem_0030) 0))
                              (Nat.ne_of_lt (mem_lt_freshVar (nb058_support_mem_0031 x) 0))
                              (TAlphaVar.here _ _ _)))))))))))))))

/-- Checked nominal proof certificate identified upstream as `nb058_split_alpha_0001`. -/
@[expose]
noncomputable def nb058SplitAlpha0001 (x : Var) :
    TAlphaWff
      [((nb058AlphaDummy006), (nb058AlphaDummy008 x)),
        ((nb058AlphaDummy005), (nb058AlphaDummy007 x)),
        ((nb058AlphaDummy011), (nb058AlphaDummy012 x)),
        ((nb058AlphaDummy009), (nb058AlphaDummy010 x)),
        ((nb058AlphaDummy001), (nb058AlphaDummy002 x)),
        ((nb058AlphaDummy000), x),
        ((nb058AlphaDummy003), (nb058AlphaDummy004 x))]
      (Wff.imp (Wff.classMem (Class.cv (nb058AlphaDummy006))
          (Class.cv (nb058AlphaDummy000))) (Wff.neg
          (Wff.classEq (Class.cv (nb058AlphaDummy005))
            (synCphi (Class.cv (nb058AlphaDummy006))))))
      (Wff.imp (Wff.classMem (Class.cv (nb058AlphaDummy008 x)) (Class.cv x)) (Wff.neg
          (Wff.classEq (Class.cv (nb058AlphaDummy007 x))
            (synCphi (Class.cv (nb058AlphaDummy008 x)))))) :=
  (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb058_support_mem_0006) 1))
          (Nat.ne_of_lt (mem_lt_freshVar (nb058_support_mem_0008 x) 1))
          (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb058_support_mem_0006) 0))
            (Nat.ne_of_lt (mem_lt_freshVar (nb058_support_mem_0008 x) 0))
            (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb058_support_mem_0010) 0))
              (Nat.ne_of_lt (mem_lt_freshVar (nb058_support_mem_0011 x) 0))
              (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb058_support_mem_0007) 0))
                (Nat.ne_of_lt (mem_lt_freshVar (nb058_support_mem_0009 x) 0)) (TAlphaVar.there
                  (Nat.ne_of_lt (mem_lt_freshVar (nb058_support_mem_0004) 0))
                  (Nat.ne_of_lt (mem_lt_freshVar (nb058_support_mem_0005 x) 0))
                  (TAlphaVar.here _ _ _)))))))) (TAlphaWff.neg (TAlphaWff.classEq
        (TAlphaClass.cv (TAlphaVar.there (freshVar_injective
              (((Class.cv (nb058AlphaDummy000))).fv ∪
                ((Class.cv (nb058AlphaDummy001))).fv) (by decide)) (freshVar_injective
              (((Class.cv x)).fv ∪ ((Class.cv (nb058AlphaDummy002 x))).fv) (by decide))
            (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                  (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb058_support_mem_0012) 0))
                    (Nat.ne_of_lt (mem_lt_freshVar (nb058_support_mem_0013 x) 0))
                    (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb058_support_mem_0012) 1))
                      (Nat.ne_of_lt (mem_lt_freshVar (nb058_support_mem_0013 x) 1))
                      (TAlphaVar.here _ _ _))))) (TAlphaWff.classEq (TAlphaClass.cv
                  (TAlphaVar.there (freshVar_injective (((Class.cv (nb058AlphaDummy006))).fv)
                      (by decide))
                    (freshVar_injective (((Class.cv (nb058AlphaDummy008 x))).fv) (by decide))
                    (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp (TAlphaWff.neg
                      (TAlphaWff.conj
                        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                          (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
                                  (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                                    (TAlphaVar.there (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb058_support_mem_0016) 1))
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb058_support_mem_0017 x) 1))
                                      (TAlphaVar.there (Nat.ne_of_lt
        (mem_lt_freshVar (nb058_support_mem_0016) 0)) (Nat.ne_of_lt
        (mem_lt_freshVar (nb058_support_mem_0017 x) 0)) (TAlphaVar.there (Nat.ne_of_lt
        (mem_lt_freshVar (nb058_support_mem_0014) 0)) (Nat.ne_of_lt
        (mem_lt_freshVar (nb058_support_mem_0015 x) 0)) (TAlphaVar.here _ _ _))))))
                                (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
                                      (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                      (TAlphaClass.reflOfClosed [((nb058AlphaDummy021),
        (nb058AlphaDummy024 x)), ((nb058AlphaDummy020), (nb058AlphaDummy023 x)),
        ((nb058AlphaDummy019), (nb058AlphaDummy022 x)), ((nb058AlphaDummy017),
        (nb058AlphaDummy018 x)), ((nb058AlphaDummy013), (nb058AlphaDummy015 x)),
        ((nb058AlphaDummy014), (nb058AlphaDummy016 x)), ((nb058AlphaDummy006),
        (nb058AlphaDummy008 x)), ((nb058AlphaDummy005), (nb058AlphaDummy007 x)),
        ((nb058AlphaDummy011), (nb058AlphaDummy012 x)), ((nb058AlphaDummy009),
        (nb058AlphaDummy010 x)), ((nb058AlphaDummy001), (nb058AlphaDummy002 x)),
        ((nb058AlphaDummy000), x), ((nb058AlphaDummy003), (nb058AlphaDummy004 x))]
                                        (synC1c) (by simp only [fv_syn_c1c])))
                                    (TAlphaWff.neg (nb058SplitAlpha0000 x))))))))
                        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar (nb058_support_mem_0014) 0))
                              (Nat.ne_of_lt (mem_lt_freshVar (nb058_support_mem_0015 x) 0))
                              (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
                            [((nb058AlphaDummy017), (nb058AlphaDummy018 x)),
                              ((nb058AlphaDummy013), (nb058AlphaDummy015 x)),
                              ((nb058AlphaDummy014), (nb058AlphaDummy016 x)),
                              ((nb058AlphaDummy006), (nb058AlphaDummy008 x)),
                              ((nb058AlphaDummy005), (nb058AlphaDummy007 x)),
                              ((nb058AlphaDummy011), (nb058AlphaDummy012 x)),
                              ((nb058AlphaDummy009), (nb058AlphaDummy010 x)),
                              ((nb058AlphaDummy001), (nb058AlphaDummy002 x)),
                              ((nb058AlphaDummy000), x),
                              ((nb058AlphaDummy003), (nb058AlphaDummy004 x))]
                            (synCnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb058_support_mem_0014) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb058_support_mem_0015 x) 0))
                            (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.classMem
                          (TAlphaClass.cv (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar (nb058_support_mem_0014) 0))
                              (Nat.ne_of_lt (mem_lt_freshVar (nb058_support_mem_0015 x) 0))
                              (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
                            [((nb058AlphaDummy017), (nb058AlphaDummy018 x)),
                              ((nb058AlphaDummy013), (nb058AlphaDummy015 x)),
                              ((nb058AlphaDummy014), (nb058AlphaDummy016 x)),
                              ((nb058AlphaDummy006), (nb058AlphaDummy008 x)),
                              ((nb058AlphaDummy005), (nb058AlphaDummy007 x)),
                              ((nb058AlphaDummy011), (nb058AlphaDummy012 x)),
                              ((nb058AlphaDummy009), (nb058AlphaDummy010 x)),
                              ((nb058AlphaDummy001), (nb058AlphaDummy002 x)),
                              ((nb058AlphaDummy000), x),
                              ((nb058AlphaDummy003), (nb058AlphaDummy004 x))]
                            (synCnnc) (by simp only [fv_syn_cnnc]))))))))))))))


end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired

end

/-! Certificates from `NAR4C058C001Part003`. -/


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

/-- Checked nominal proof certificate identified upstream as `nb058_split_alpha_0002`. -/
@[expose]
noncomputable def nb058SplitAlpha0002 (x : Var) :
    TAlphaWff
      [((nb058AlphaDummy021), (nb058AlphaDummy024 x)),
        ((nb058AlphaDummy020), (nb058AlphaDummy023 x)),
        ((nb058AlphaDummy019), (nb058AlphaDummy022 x)),
        ((nb058AlphaDummy017), (nb058AlphaDummy018 x)),
        ((nb058AlphaDummy013), (nb058AlphaDummy015 x)),
        ((nb058AlphaDummy014), (nb058AlphaDummy016 x)),
        ((nb058AlphaDummy039), (nb058AlphaDummy040 x)),
        ((nb058AlphaDummy037), (nb058AlphaDummy038 x)),
        ((nb058AlphaDummy006), (nb058AlphaDummy008 x)),
        ((nb058AlphaDummy005), (nb058AlphaDummy007 x)),
        ((nb058AlphaDummy035), (nb058AlphaDummy036 x)),
        ((nb058AlphaDummy009), (nb058AlphaDummy010 x)),
        ((nb058AlphaDummy001), (nb058AlphaDummy002 x)),
        ((nb058AlphaDummy000), x),
        ((nb058AlphaDummy003), (nb058AlphaDummy004 x))]
      (Wff.imp (Wff.classEq
          (synCin (Class.cv (nb058AlphaDummy020)) (Class.cv (nb058AlphaDummy021)))
          (synC0)) (Wff.neg (Wff.classEq (Class.cv (nb058AlphaDummy019))
            (synCun (Class.cv (nb058AlphaDummy020)) (Class.cv (nb058AlphaDummy021))))))
      (Wff.imp (Wff.classEq (synCin (Class.cv (nb058AlphaDummy023 x))
            (Class.cv (nb058AlphaDummy024 x))) (synC0)) (Wff.neg
          (Wff.classEq (Class.cv (nb058AlphaDummy022 x))
            (synCun (Class.cv (nb058AlphaDummy023 x))
              (Class.cv (nb058AlphaDummy024 x)))))) :=
  (TAlphaWff.imp (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.neg (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (Nat.ne_of_lt (mem_lt_freshVar (nb058_support_mem_0020) 0))
                          (Nat.ne_of_lt (mem_lt_freshVar (nb058_support_mem_0021 x) 0))
                          (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb058_support_mem_0018) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb058_support_mem_0019 x) 0))
                            (TAlphaVar.there (freshVar_injective
                                (((Class.cv (nb058AlphaDummy013))).fv ∪ ((synC1c)).fv)
                                (by decide)) (freshVar_injective
                                (((Class.cv (nb058AlphaDummy015 x))).fv ∪ ((synC1c)).fv)
                                (by decide)) (TAlphaVar.here _ _ _))))))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (Nat.ne_of_lt (mem_lt_freshVar (nb058_support_mem_0024) 0))
                          (Nat.ne_of_lt (mem_lt_freshVar (nb058_support_mem_0025 x) 0))
                          (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb058_support_mem_0022) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb058_support_mem_0023 x) 0))
                            (TAlphaVar.here _ _ _)))))))))
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.neg (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (Nat.ne_of_lt (mem_lt_freshVar (nb058_support_mem_0020) 0))
                          (Nat.ne_of_lt (mem_lt_freshVar (nb058_support_mem_0021 x) 0))
                          (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb058_support_mem_0018) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb058_support_mem_0019 x) 0))
                            (TAlphaVar.there (freshVar_injective
                                (((Class.cv (nb058AlphaDummy013))).fv ∪ ((synC1c)).fv)
                                (by decide)) (freshVar_injective
                                (((Class.cv (nb058AlphaDummy015 x))).fv ∪ ((synC1c)).fv)
                                (by decide)) (TAlphaVar.here _ _ _))))))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (Nat.ne_of_lt (mem_lt_freshVar (nb058_support_mem_0024) 0))
                          (Nat.ne_of_lt (mem_lt_freshVar (nb058_support_mem_0025 x) 0))
                          (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb058_support_mem_0022) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb058_support_mem_0023 x) 0))
                            (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.reflOfClosed
        [((nb058AlphaDummy021), (nb058AlphaDummy024 x)),
          ((nb058AlphaDummy020), (nb058AlphaDummy023 x)),
          ((nb058AlphaDummy019), (nb058AlphaDummy022 x)),
          ((nb058AlphaDummy017), (nb058AlphaDummy018 x)),
          ((nb058AlphaDummy013), (nb058AlphaDummy015 x)),
          ((nb058AlphaDummy014), (nb058AlphaDummy016 x)),
          ((nb058AlphaDummy039), (nb058AlphaDummy040 x)),
          ((nb058AlphaDummy037), (nb058AlphaDummy038 x)),
          ((nb058AlphaDummy006), (nb058AlphaDummy008 x)),
          ((nb058AlphaDummy005), (nb058AlphaDummy007 x)),
          ((nb058AlphaDummy035), (nb058AlphaDummy036 x)),
          ((nb058AlphaDummy009), (nb058AlphaDummy010 x)),
          ((nb058AlphaDummy001), (nb058AlphaDummy002 x)), ((nb058AlphaDummy000), x),
          ((nb058AlphaDummy003), (nb058AlphaDummy004 x))]
        (synC0) (by simp only [fv_syn_c0]))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv
          (TAlphaVar.there
            (freshVar_injective (((Class.cv (nb058AlphaDummy013))).fv ∪ ((synC1c)).fv)
              (by decide)) (freshVar_injective
              (((Class.cv (nb058AlphaDummy015 x))).fv ∪ ((synC1c)).fv) (by decide))
            (TAlphaVar.there (freshVar_injective
                (((Class.cv (nb058AlphaDummy013))).fv ∪ ((synC1c)).fv) (by decide))
              (freshVar_injective
                (((Class.cv (nb058AlphaDummy015 x))).fv ∪ ((synC1c)).fv) (by decide))
              (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                  (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb058_support_mem_0028) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb058_support_mem_0029 x) 0))
                            (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar (nb058_support_mem_0026) 0))
                              (Nat.ne_of_lt (mem_lt_freshVar (nb058_support_mem_0027 x) 0))
                              (TAlphaVar.there (freshVar_injective
                                  (((Class.cv (nb058AlphaDummy013))).fv ∪ ((synC1c)).fv)
                                  (by decide)) (freshVar_injective
                                  (((Class.cv (nb058AlphaDummy015 x))).fv ∪ ((synC1c)).fv)
                                  (by decide)) (TAlphaVar.here _ _ _))))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb058_support_mem_0028) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb058_support_mem_0029 x) 0))
                            (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar (nb058_support_mem_0026) 0))
                              (Nat.ne_of_lt (mem_lt_freshVar (nb058_support_mem_0027 x) 0))
                              (TAlphaVar.there (freshVar_injective
                                  (((Class.cv (nb058AlphaDummy013))).fv ∪ ((synC1c)).fv)
                                  (by decide)) (freshVar_injective
                                  (((Class.cv (nb058AlphaDummy015 x))).fv ∪ ((synC1c)).fv)
                                  (by decide)) (TAlphaVar.here _ _ _))))))))))
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                  (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb058_support_mem_0032) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb058_support_mem_0033 x) 0))
                            (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar (nb058_support_mem_0030) 0))
                              (Nat.ne_of_lt (mem_lt_freshVar (nb058_support_mem_0031 x) 0))
                              (TAlphaVar.here _ _ _)))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb058_support_mem_0032) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb058_support_mem_0033 x) 0))
                            (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar (nb058_support_mem_0030) 0))
                              (Nat.ne_of_lt (mem_lt_freshVar (nb058_support_mem_0031 x) 0))
                              (TAlphaVar.here _ _ _)))))))))))))))

/-- Checked nominal proof certificate identified upstream as `nb058_split_alpha_0003`. -/
@[expose]
noncomputable def nb058SplitAlpha0003 (x : Var) :
    TAlphaWff
      [((nb058AlphaDummy039), (nb058AlphaDummy040 x)),
        ((nb058AlphaDummy037), (nb058AlphaDummy038 x)),
        ((nb058AlphaDummy006), (nb058AlphaDummy008 x)),
        ((nb058AlphaDummy005), (nb058AlphaDummy007 x)),
        ((nb058AlphaDummy035), (nb058AlphaDummy036 x)),
        ((nb058AlphaDummy009), (nb058AlphaDummy010 x)),
        ((nb058AlphaDummy001), (nb058AlphaDummy002 x)),
        ((nb058AlphaDummy000), x),
        ((nb058AlphaDummy003), (nb058AlphaDummy004 x))]
      (Wff.classMem (Class.cv (nb058AlphaDummy039))
        (synCphi (Class.cv (nb058AlphaDummy006))))
      (Wff.classMem (Class.cv (nb058AlphaDummy040 x))
        (synCphi (Class.cv (nb058AlphaDummy008 x)))) :=
  (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.ex
        (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
            (TAlphaClass.cv
              (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb058_support_mem_0012) 0))
                (Nat.ne_of_lt (mem_lt_freshVar (nb058_support_mem_0013 x) 0)) (TAlphaVar.there
                  (Nat.ne_of_lt (mem_lt_freshVar (nb058_support_mem_0012) 1))
                  (Nat.ne_of_lt (mem_lt_freshVar (nb058_support_mem_0013 x) 1)) (TAlphaVar.there
                    (Nat.ne_of_lt (mem_lt_freshVar (nb058_support_mem_0042) 0))
                    (Nat.ne_of_lt (mem_lt_freshVar (nb058_support_mem_0043 x) 0))
                    (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb058_support_mem_0040) 0))
                      (Nat.ne_of_lt (mem_lt_freshVar (nb058_support_mem_0041 x) 0))
                      (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
              (TAlphaVar.there
                (freshVar_injective (((Class.cv (nb058AlphaDummy006))).fv) (by decide))
                (freshVar_injective (((Class.cv (nb058AlphaDummy008 x))).fv) (by decide))
                (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp (TAlphaWff.neg
                  (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                      (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb058_support_mem_0016) 1)) (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb058_support_mem_0017 x) 1))
                                  (TAlphaVar.there (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb058_support_mem_0016) 0))
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb058_support_mem_0017 x) 0))
                                    (TAlphaVar.there (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb058_support_mem_0014) 0))
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb058_support_mem_0015 x) 0))
                                      (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
                                (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                  (TAlphaClass.reflOfClosed
                                    [((nb058AlphaDummy021), (nb058AlphaDummy024 x)),
                                      ((nb058AlphaDummy020), (nb058AlphaDummy023 x)),
                                      ((nb058AlphaDummy019), (nb058AlphaDummy022 x)),
                                      ((nb058AlphaDummy017), (nb058AlphaDummy018 x)),
                                      ((nb058AlphaDummy013), (nb058AlphaDummy015 x)),
                                      ((nb058AlphaDummy014), (nb058AlphaDummy016 x)),
                                      ((nb058AlphaDummy039), (nb058AlphaDummy040 x)),
                                      ((nb058AlphaDummy037), (nb058AlphaDummy038 x)),
                                      ((nb058AlphaDummy006), (nb058AlphaDummy008 x)),
                                      ((nb058AlphaDummy005), (nb058AlphaDummy007 x)),
                                      ((nb058AlphaDummy035), (nb058AlphaDummy036 x)),
                                      ((nb058AlphaDummy009), (nb058AlphaDummy010 x)),
                                      ((nb058AlphaDummy001), (nb058AlphaDummy002 x)),
                                      ((nb058AlphaDummy000), x), ((nb058AlphaDummy003),
                                        (nb058AlphaDummy004 x))]
                                    (synC1c) (by simp only [fv_syn_c1c])))
                                (TAlphaWff.neg (nb058SplitAlpha0002 x))))))))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there
                          (Nat.ne_of_lt (mem_lt_freshVar (nb058_support_mem_0014) 0))
                          (Nat.ne_of_lt (mem_lt_freshVar (nb058_support_mem_0015 x) 0))
                          (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
                        [((nb058AlphaDummy017), (nb058AlphaDummy018 x)),
                          ((nb058AlphaDummy013), (nb058AlphaDummy015 x)),
                          ((nb058AlphaDummy014), (nb058AlphaDummy016 x)),
                          ((nb058AlphaDummy039), (nb058AlphaDummy040 x)),
                          ((nb058AlphaDummy037), (nb058AlphaDummy038 x)),
                          ((nb058AlphaDummy006), (nb058AlphaDummy008 x)),
                          ((nb058AlphaDummy005), (nb058AlphaDummy007 x)),
                          ((nb058AlphaDummy035), (nb058AlphaDummy036 x)),
                          ((nb058AlphaDummy009), (nb058AlphaDummy010 x)),
                          ((nb058AlphaDummy001), (nb058AlphaDummy002 x)),
                          ((nb058AlphaDummy000), x),
                          ((nb058AlphaDummy003), (nb058AlphaDummy004 x))]
                        (synCnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
                  (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                      (TAlphaVar.there
                        (Nat.ne_of_lt (mem_lt_freshVar (nb058_support_mem_0014) 0))
                        (Nat.ne_of_lt (mem_lt_freshVar (nb058_support_mem_0015 x) 0))
                        (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.classMem
                      (TAlphaClass.cv (TAlphaVar.there
                          (Nat.ne_of_lt (mem_lt_freshVar (nb058_support_mem_0014) 0))
                          (Nat.ne_of_lt (mem_lt_freshVar (nb058_support_mem_0015 x) 0))
                          (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
                        [((nb058AlphaDummy017), (nb058AlphaDummy018 x)),
                          ((nb058AlphaDummy013), (nb058AlphaDummy015 x)),
                          ((nb058AlphaDummy014), (nb058AlphaDummy016 x)),
                          ((nb058AlphaDummy039), (nb058AlphaDummy040 x)),
                          ((nb058AlphaDummy037), (nb058AlphaDummy038 x)),
                          ((nb058AlphaDummy006), (nb058AlphaDummy008 x)),
                          ((nb058AlphaDummy005), (nb058AlphaDummy007 x)),
                          ((nb058AlphaDummy035), (nb058AlphaDummy036 x)),
                          ((nb058AlphaDummy009), (nb058AlphaDummy010 x)),
                          ((nb058AlphaDummy001), (nb058AlphaDummy002 x)),
                          ((nb058AlphaDummy000), x),
                          ((nb058AlphaDummy003), (nb058AlphaDummy004 x))]
                        (synCnnc) (by simp only [fv_syn_cnnc]))))))))))))

/-- Checked nominal proof certificate identified upstream as `nb058_split_alpha_0004`. -/
@[expose]
noncomputable def nb058SplitAlpha0004 (x : Var) :
    TAlphaWff
      [((nb058AlphaDummy001), (nb058AlphaDummy002 x)), ((nb058AlphaDummy000), x),
        ((nb058AlphaDummy003), (nb058AlphaDummy004 x))]
      (Wff.classEq (Class.cv (nb058AlphaDummy003))
        (synCop (Class.cv (nb058AlphaDummy000)) (Class.cv (nb058AlphaDummy001))))
      (Wff.classEq (Class.cv (nb058AlphaDummy004 x))
        (synCop (Class.cv x) (Class.cv (nb058AlphaDummy002 x)))) :=
  (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there
        (Ne.symm (Nat.ne_of_lt (mem_lt_freshVar (nb058_support_mem_0002) 0)))
        (Ne.symm (Nat.ne_of_lt (mem_lt_freshVar (nb058_support_mem_0003 x) 0))) (TAlphaVar.there
          (Ne.symm (Nat.ne_of_lt (mem_lt_freshVar (nb058_support_mem_0000) 0)))
          (Ne.symm (Nat.ne_of_lt (mem_lt_freshVar (nb058_support_mem_0001 x) 0)))
          (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
          (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
              (TAlphaWff.neg (TAlphaWff.conj
                  (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                      (TAlphaWff.ex (TAlphaWff.neg (nb058SplitAlpha0001 x)))))
                  (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                      (TAlphaWff.ex (TAlphaWff.neg (nb058SplitAlpha0001 x)))))))))
          (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
              (TAlphaWff.neg (TAlphaWff.conj
                  (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                      (TAlphaWff.ex (TAlphaWff.conj
                          (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                            (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb058_support_mem_0034) 1)) (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb058_support_mem_0036 x) 1))
                                (TAlphaVar.there (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb058_support_mem_0034) 0)) (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb058_support_mem_0036 x) 0))
                                  (TAlphaVar.there (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb058_support_mem_0038) 0))
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb058_support_mem_0039 x) 0))
                                    (TAlphaVar.there (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb058_support_mem_0035) 0))
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb058_support_mem_0037 x) 0))
                                      (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq
                            (TAlphaClass.cv (TAlphaVar.there (freshVar_injective
                                  (((Class.cv (nb058AlphaDummy000))).fv ∪
                                    ((Class.cv (nb058AlphaDummy001))).fv) (by decide))
                                (freshVar_injective (((Class.cv x)).fv ∪
                                    ((Class.cv (nb058AlphaDummy002 x))).fv) (by decide))
                                (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.neg
                                (TAlphaWff.conj (TAlphaWff.classMem
                                    (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                                      (TAlphaWff.neg (TAlphaWff.conj (nb058SplitAlpha0003 x)
        (nb058SplitAlpha0003 x))))) (TAlphaWff.classMem
                                    (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                    (TAlphaClass.reflOfClosed [((nb058AlphaDummy037),
        (nb058AlphaDummy038 x)), ((nb058AlphaDummy006), (nb058AlphaDummy008 x)),
                                        ((nb058AlphaDummy005), (nb058AlphaDummy007 x)),
                                        ((nb058AlphaDummy035), (nb058AlphaDummy036 x)),
                                        ((nb058AlphaDummy009), (nb058AlphaDummy010 x)),
                                        ((nb058AlphaDummy001), (nb058AlphaDummy002 x)),
                                        ((nb058AlphaDummy000), x), ((nb058AlphaDummy003),
        (nb058AlphaDummy004 x))] (synCcompl (synCsn (synC0c))) (by
                                        simp only [fv_syn_ccompl, fv_syn_csn,
                                          fv_syn_c0c])))))))))))
                  (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                      (TAlphaWff.ex (TAlphaWff.conj
                          (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                            (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb058_support_mem_0034) 1)) (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb058_support_mem_0036 x) 1))
                                (TAlphaVar.there (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb058_support_mem_0034) 0)) (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb058_support_mem_0036 x) 0))
                                  (TAlphaVar.there (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb058_support_mem_0038) 0))
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb058_support_mem_0039 x) 0))
                                    (TAlphaVar.there (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb058_support_mem_0035) 0))
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb058_support_mem_0037 x) 0))
                                      (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq
                            (TAlphaClass.cv (TAlphaVar.there (freshVar_injective
                                  (((Class.cv (nb058AlphaDummy000))).fv ∪
                                    ((Class.cv (nb058AlphaDummy001))).fv) (by decide))
                                (freshVar_injective (((Class.cv x)).fv ∪
                                    ((Class.cv (nb058AlphaDummy002 x))).fv) (by decide))
                                (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.neg
                                (TAlphaWff.conj (TAlphaWff.classMem
                                    (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                                      (TAlphaWff.neg (TAlphaWff.conj (nb058SplitAlpha0003 x)
        (nb058SplitAlpha0003 x))))) (TAlphaWff.classMem
                                    (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                    (TAlphaClass.reflOfClosed [((nb058AlphaDummy037),
        (nb058AlphaDummy038 x)), ((nb058AlphaDummy006), (nb058AlphaDummy008 x)),
                                        ((nb058AlphaDummy005), (nb058AlphaDummy007 x)),
                                        ((nb058AlphaDummy035), (nb058AlphaDummy036 x)),
                                        ((nb058AlphaDummy009), (nb058AlphaDummy010 x)),
                                        ((nb058AlphaDummy001), (nb058AlphaDummy002 x)),
                                        ((nb058AlphaDummy000), x), ((nb058AlphaDummy003),
        (nb058AlphaDummy004 x))] (synCcompl (synCsn (synC0c))) (by
                                        simp only [fv_syn_ccompl, fv_syn_csn,
                                          fv_syn_c0c])))))))))))))))))))

/-- Checked nominal proof certificate identified upstream as `nb058_split_alpha_0005`. -/
@[expose]
noncomputable def nb058SplitAlpha0005 (x : Var) :
    TAlphaWff
      [((nb058AlphaDummy043), (nb058AlphaDummy044 x)),
        ((nb058AlphaDummy041), (nb058AlphaDummy042 x)),
        ((nb058AlphaDummy001), (nb058AlphaDummy002 x)),
        ((nb058AlphaDummy000), x),
        ((nb058AlphaDummy003), (nb058AlphaDummy004 x))]
      (Wff.classMem (Class.cv (nb058AlphaDummy043))
        (synCpw (synCuni (Class.cv (nb058AlphaDummy000)))))
      (Wff.classMem (Class.cv (nb058AlphaDummy044 x)) (synCpw (synCuni (Class.cv x)))) :=
  (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
      (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                  (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb058_support_mem_0046) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb058_support_mem_0047 x) 0))
                            (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar (nb058_support_mem_0044) 0))
                              (Nat.ne_of_lt (mem_lt_freshVar (nb058_support_mem_0045 x) 0))
                              (TAlphaVar.here _ _ _)))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.objMem
                                (TAlphaVar.there (freshVar_injective
                                    (((Class.cv (nb058AlphaDummy000))).fv) (by decide))
                                  (freshVar_injective (((Class.cv x)).fv) (by decide))
                                  (TAlphaVar.here _ _ _)) (TAlphaVar.here _ _ _))
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb058_support_mem_0058) 1))
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb058_support_mem_0059 x) 1))
                                    (TAlphaVar.there (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb058_support_mem_0058) 0))
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb058_support_mem_0059 x) 0))
                                      (TAlphaVar.there (Nat.ne_of_lt
        (mem_lt_freshVar (nb058_support_mem_0056) 0)) (Nat.ne_of_lt
        (mem_lt_freshVar (nb058_support_mem_0057 x) 0)) (TAlphaVar.there (Nat.ne_of_lt
        (mem_lt_freshVar (nb058_support_mem_0054) 0)) (Nat.ne_of_lt
        (mem_lt_freshVar (nb058_support_mem_0055 x) 0)) (TAlphaVar.there (Nat.ne_of_lt
        (mem_lt_freshVar (nb058_support_mem_0052) 0)) (Nat.ne_of_lt
        (mem_lt_freshVar (nb058_support_mem_0053 x) 0)) (TAlphaVar.there (Nat.ne_of_lt
        (mem_lt_freshVar (nb058_support_mem_0050) 0)) (Nat.ne_of_lt (mem_lt_freshVar
        (nb058_support_mem_0051 x) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar
        (nb058_support_mem_0048) 0)) (Nat.ne_of_lt (mem_lt_freshVar
        (nb058_support_mem_0049 x) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar
        (nb058_support_mem_0004) 0)) (Nat.ne_of_lt (mem_lt_freshVar
        (nb058_support_mem_0005 x) 0)) (TAlphaVar.here _ _ _)))))))))))))))))))
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                  (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb058_support_mem_0046) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb058_support_mem_0047 x) 0))
                            (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar (nb058_support_mem_0044) 0))
                              (Nat.ne_of_lt (mem_lt_freshVar (nb058_support_mem_0045 x) 0))
                              (TAlphaVar.here _ _ _)))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.objMem
                                (TAlphaVar.there (freshVar_injective
                                    (((Class.cv (nb058AlphaDummy000))).fv) (by decide))
                                  (freshVar_injective (((Class.cv x)).fv) (by decide))
                                  (TAlphaVar.here _ _ _)) (TAlphaVar.here _ _ _))
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb058_support_mem_0058) 1))
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb058_support_mem_0059 x) 1))
                                    (TAlphaVar.there (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb058_support_mem_0058) 0))
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb058_support_mem_0059 x) 0))
                                      (TAlphaVar.there (Nat.ne_of_lt
        (mem_lt_freshVar (nb058_support_mem_0056) 0)) (Nat.ne_of_lt
        (mem_lt_freshVar (nb058_support_mem_0057 x) 0)) (TAlphaVar.there (Nat.ne_of_lt
        (mem_lt_freshVar (nb058_support_mem_0054) 0)) (Nat.ne_of_lt
        (mem_lt_freshVar (nb058_support_mem_0055 x) 0)) (TAlphaVar.there (Nat.ne_of_lt
        (mem_lt_freshVar (nb058_support_mem_0052) 0)) (Nat.ne_of_lt
        (mem_lt_freshVar (nb058_support_mem_0053 x) 0)) (TAlphaVar.there (Nat.ne_of_lt
        (mem_lt_freshVar (nb058_support_mem_0050) 0)) (Nat.ne_of_lt (mem_lt_freshVar
        (nb058_support_mem_0051 x) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar
        (nb058_support_mem_0048) 0)) (Nat.ne_of_lt (mem_lt_freshVar
        (nb058_support_mem_0049 x) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar
        (nb058_support_mem_0004) 0)) (Nat.ne_of_lt (mem_lt_freshVar
        (nb058_support_mem_0005 x) 0)) (TAlphaVar.here _ _ _))))))))))))))))))))))
        (TAlphaClass.cv (TAlphaVar.here _ _ _)))))

/-- Checked nominal proof certificate identified upstream as `nominal_df_pw1fn`. -/
@[expose]
noncomputable def nominalDfPw1fn (x : Var) :
    Nominal.NPrf
      (.classEq (synCpw1fn) (synCmpt x (synC1c) (synCpw1 (synCuni (.cv x))))) :=
  by
  exact
    Nominal.alphaClassEq
      (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.ex (TAlphaWff.conj (nb058SplitAlpha0004 x)
              (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there
                      (Nat.ne_of_lt (mem_lt_freshVar (nb058_support_mem_0004) 0))
                      (Nat.ne_of_lt (mem_lt_freshVar (nb058_support_mem_0005 x) 0))
                      (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
                    [((nb058AlphaDummy001), (nb058AlphaDummy002 x)),
                      ((nb058AlphaDummy000), x),
                      ((nb058AlphaDummy003), (nb058AlphaDummy004 x))]
                    (synC1c) (by simp only [fv_syn_c1c])))
                (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                    (TAlphaWff.neg (TAlphaWff.conj
                        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                          (TAlphaClass.cab (TAlphaWff.neg
                              (TAlphaWff.conj (nb058SplitAlpha0005 x) (TAlphaWff.classMem
                                  (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                  (TAlphaClass.reflOfClosed
                                    [((nb058AlphaDummy043), (nb058AlphaDummy044 x)),
                                      ((nb058AlphaDummy041), (nb058AlphaDummy042 x)),
                                      ((nb058AlphaDummy001), (nb058AlphaDummy002 x)),
                                      ((nb058AlphaDummy000), x), ((nb058AlphaDummy003),
                                        (nb058AlphaDummy004 x))]
                                    (synC1c) (by simp only [fv_syn_c1c])))))))
                        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                          (TAlphaClass.cab (TAlphaWff.neg
                              (TAlphaWff.conj (nb058SplitAlpha0005 x) (TAlphaWff.classMem
                                  (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                  (TAlphaClass.reflOfClosed
                                    [((nb058AlphaDummy043), (nb058AlphaDummy044 x)),
                                      ((nb058AlphaDummy041), (nb058AlphaDummy042 x)),
                                      ((nb058AlphaDummy001), (nb058AlphaDummy002 x)),
                                      ((nb058AlphaDummy000), x), ((nb058AlphaDummy003),
                                        (nb058AlphaDummy004 x))]
                                    (synC1c) (by simp only [fv_syn_c1c]))))))))))))))))

end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired

end
