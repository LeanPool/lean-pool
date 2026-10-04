/-
Copyright (c) 2026 Elliot Glazer and NFNotWPP contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elliot Glazer and NFNotWPP contributors
-/

module

public import LeanPool.NFWeakPartition.AlphaSupport.NAR4C057C001Part017Stage1

/-! Nominal proof certificates grouped in dependency order. -/


public section

/-! Certificates from `NAR4C057C001Part017`. -/


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

/-- Checked nominal proof certificate identified upstream as `nb057_wpp_refl_0042`. -/
@[expose]
noncomputable def nb057WppRefl0042 (f : Var) (a : Var) :
    TReflOn
      [((nb057AlphaDummy042), (nb057AlphaDummy043 f)),
        ((nb057AlphaDummy040), (nb057AlphaDummy041 f)),
        ((nb057AlphaDummy000), a), ((nb057AlphaDummy001), f),
        ((nb057AlphaDummy002), (nb057AlphaDummy003 f a))]
      ((synCid)).fv :=
  TEnvFresh.reflOn (nb057_compact_envfresh_0042 f a)

/-- Checked nominal proof certificate identified upstream as `nb057_function_binder_occurrence`. -/
@[expose]
noncomputable def nb057FunctionBinderOccurrence (f a : Var) :
    TAlphaClass
      [(nb057AlphaDummy045, (nb057AlphaDummy048 f)),
        (nb057AlphaDummy044, (nb057AlphaDummy047 f)),
        (nb057AlphaDummy050, (nb057AlphaDummy051 f)),
        (nb057AlphaDummy042, (nb057AlphaDummy043 f)),
        (nb057AlphaDummy040, (nb057AlphaDummy041 f)), (nb057AlphaDummy000, a),
        (nb057AlphaDummy001, f), (nb057AlphaDummy002, (nb057AlphaDummy003 f a))]
      (Class.cv nb057AlphaDummy050) (Class.cv (nb057AlphaDummy051 f)) :=
  by
  have freshness0 : nb057AlphaDummy050 ≠ nb057AlphaDummy045 :=
    by
    unfold nb057AlphaDummy050
    with_reducible
      exact (Ne.symm (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0044) 0)))
  have freshness1 : (nb057AlphaDummy051 f) ≠ (nb057AlphaDummy048 f) :=
    by
    unfold nb057AlphaDummy051
    with_reducible
      exact (Ne.symm (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0045 f) 0)))
  have freshness2 : nb057AlphaDummy050 ≠ nb057AlphaDummy044 :=
    by
    unfold nb057AlphaDummy050
    with_reducible
      exact (Ne.symm (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0042) 0)))
  have freshness3 : (nb057AlphaDummy051 f) ≠ (nb057AlphaDummy047 f) :=
    by
    unfold nb057AlphaDummy051
    with_reducible
      exact (Ne.symm (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0043 f) 0)))
  with_reducible
    exact
      (TAlphaClass.cv (TAlphaVar.there freshness0 freshness1
          (TAlphaVar.there freshness2 freshness3 (TAlphaVar.here _ _ _))))

/-- Checked nominal proof certificate identified upstream as `nb057_split_alpha_0032`. -/
@[expose]
noncomputable def nb057SplitAlpha0032 (f : Var) (a : Var) (dv_a_f : a ≠ f) :
    TAlphaWff
      [((nb057AlphaDummy040), (nb057AlphaDummy041 f)), ((nb057AlphaDummy000), a),
        ((nb057AlphaDummy001), f),
        ((nb057AlphaDummy002), (nb057AlphaDummy003 f a))]
      (Wff.imp (Wff.classMem (Class.cv (nb057AlphaDummy040)) (synCnin
            (synCcom (Class.cv (nb057AlphaDummy001))
              (synCcnv (Class.cv (nb057AlphaDummy001)))) (synCid))) (Wff.neg
          (Wff.classMem (Class.cv (nb057AlphaDummy040)) (synCnin
              (synCcom (Class.cv (nb057AlphaDummy001))
                (synCcnv (Class.cv (nb057AlphaDummy001)))) (synCid)))))
      (Wff.imp (Wff.classMem (Class.cv (nb057AlphaDummy041 f))
          (synCnin (synCcom (Class.cv f) (synCcnv (Class.cv f))) (synCid))) (Wff.neg
          (Wff.classMem (Class.cv (nb057AlphaDummy041 f))
            (synCnin (synCcom (Class.cv f) (synCcnv (Class.cv f))) (synCid))))) :=
  (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.ex (TAlphaWff.ex (TAlphaWff.conj
                      (TAlphaWff.classEq (nb057FunctionBinderOccurrence f a) (TAlphaClass.cab
                          (TAlphaWff.neg (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
                                      (TAlphaWff.classMem
                                        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt
        (mem_lt_freshVar (nb057_support_mem_0046) 1)) (Nat.ne_of_lt (mem_lt_freshVar
        (nb057_support_mem_0048 f) 1)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar
        (nb057_support_mem_0046) 0)) (Nat.ne_of_lt (mem_lt_freshVar
        (nb057_support_mem_0048 f) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar
        (nb057_support_mem_0050) 0)) (Nat.ne_of_lt (mem_lt_freshVar
        (nb057_support_mem_0051 f) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar
        (nb057_support_mem_0047) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0049 f)
        0)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb057AlphaDummy001))).fv ∪
        ((synCcnv (Class.cv (nb057AlphaDummy001)))).fv) (by decide)) (freshVar_injective
        (((Class.cv f)).fv ∪ ((synCcnv (Class.cv f))).fv) (by decide))
        (TAlphaVar.here _ _ _)))))))) (nb057SplitAlpha0006 f a))))) (TAlphaWff.classMem
                                        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt
        (mem_lt_freshVar (nb057_support_mem_0046) 1)) (Nat.ne_of_lt (mem_lt_freshVar
        (nb057_support_mem_0048 f) 1)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar
        (nb057_support_mem_0046) 0)) (Nat.ne_of_lt (mem_lt_freshVar
        (nb057_support_mem_0048 f) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar
        (nb057_support_mem_0050) 0)) (Nat.ne_of_lt (mem_lt_freshVar
        (nb057_support_mem_0051 f) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar
        (nb057_support_mem_0047) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0049 f)
        0)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb057AlphaDummy001))).fv ∪
        ((synCcnv (Class.cv (nb057AlphaDummy001)))).fv) (by decide)) (freshVar_injective
        (((Class.cv f)).fv ∪ ((synCcnv (Class.cv f))).fv) (by decide))
        (TAlphaVar.here _ _ _)))))))) (nb057SplitAlpha0006 f a)))))))))
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cab (TAlphaWff.neg
                                    (TAlphaWff.neg (nb057SplitAlpha0009 f a)))))))))
                      (TAlphaWff.ex (TAlphaWff.neg (nb057SplitAlpha0031 f a dv_a_f))))))))
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
              (TAlphaClass.reflOfReflOn [((nb057AlphaDummy042), (nb057AlphaDummy043 f)),
                  ((nb057AlphaDummy040), (nb057AlphaDummy041 f)),
                  ((nb057AlphaDummy000), a), ((nb057AlphaDummy001), f),
                  ((nb057AlphaDummy002), (nb057AlphaDummy003 f a))]
                (synCid) (nb057WppRefl0042 f a))))))) (TAlphaWff.neg
      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
          (TAlphaWff.neg (TAlphaWff.conj
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                  (TAlphaWff.ex (TAlphaWff.ex (TAlphaWff.conj
                        (TAlphaWff.classEq (nb057FunctionBinderOccurrence f a)
                          (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
                                  (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                                    (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0046) 1))
        (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0048 f) 1)) (TAlphaVar.there
        (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0046) 0)) (Nat.ne_of_lt
        (mem_lt_freshVar (nb057_support_mem_0048 f) 0)) (TAlphaVar.there (Nat.ne_of_lt
        (mem_lt_freshVar (nb057_support_mem_0050) 0)) (Nat.ne_of_lt (mem_lt_freshVar
        (nb057_support_mem_0051 f) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar
        (nb057_support_mem_0047) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0049 f)
        0)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb057AlphaDummy001))).fv ∪
        ((synCcnv (Class.cv (nb057AlphaDummy001)))).fv) (by decide)) (freshVar_injective
        (((Class.cv f)).fv ∪ ((synCcnv (Class.cv f))).fv) (by decide)) (TAlphaVar.here _ _
        _)))))))) (nb057SplitAlpha0006 f a))))) (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0046) 1))
        (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0048 f) 1)) (TAlphaVar.there
        (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0046) 0)) (Nat.ne_of_lt
        (mem_lt_freshVar (nb057_support_mem_0048 f) 0)) (TAlphaVar.there (Nat.ne_of_lt
        (mem_lt_freshVar (nb057_support_mem_0050) 0)) (Nat.ne_of_lt (mem_lt_freshVar
        (nb057_support_mem_0051 f) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar
        (nb057_support_mem_0047) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0049 f)
        0)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb057AlphaDummy001))).fv ∪
        ((synCcnv (Class.cv (nb057AlphaDummy001)))).fv) (by decide)) (freshVar_injective
        (((Class.cv f)).fv ∪ ((synCcnv (Class.cv f))).fv) (by decide)) (TAlphaVar.here _ _
        _)))))))) (nb057SplitAlpha0006 f a))))))))) (TAlphaWff.classMem
                                  (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                                    (TAlphaWff.neg
                                      (TAlphaWff.neg (nb057SplitAlpha0009 f a)))))))))
                        (TAlphaWff.ex (TAlphaWff.neg (nb057SplitAlpha0031 f a dv_a_f))))))))
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                (TAlphaClass.reflOfReflOn
                  [((nb057AlphaDummy042), (nb057AlphaDummy043 f)),
                    ((nb057AlphaDummy040), (nb057AlphaDummy041 f)),
                    ((nb057AlphaDummy000), a), ((nb057AlphaDummy001), f),
                    ((nb057AlphaDummy002), (nb057AlphaDummy003 f a))]
                  (synCid) (nb057WppRefl0042 f a)))))))))

/-- Checked nominal proof certificate identified upstream as `nb057_split_alpha_0033`. -/
@[expose]
noncomputable def nb057SplitAlpha0033 (f : Var) (a : Var) :
    TAlphaWff
      [((nb057AlphaDummy068), (nb057AlphaDummy071 f)),
        ((nb057AlphaDummy067), (nb057AlphaDummy070 f)),
        ((nb057AlphaDummy066), (nb057AlphaDummy069 f)),
        ((nb057AlphaDummy064), (nb057AlphaDummy065 f)),
        ((nb057AlphaDummy060), (nb057AlphaDummy062 f)),
        ((nb057AlphaDummy061), (nb057AlphaDummy063 f)),
        ((nb057AlphaDummy053), (nb057AlphaDummy055 f)),
        ((nb057AlphaDummy052), (nb057AlphaDummy054 f)),
        ((nb057AlphaDummy058), (nb057AlphaDummy059 f)),
        ((nb057AlphaDummy056), (nb057AlphaDummy057 f)),
        ((nb057AlphaDummy045), (nb057AlphaDummy048 f)),
        ((nb057AlphaDummy044), (nb057AlphaDummy047 f)),
        ((nb057AlphaDummy050), (nb057AlphaDummy051 f)),
        ((nb057AlphaDummy000), a), ((nb057AlphaDummy001), f),
        ((nb057AlphaDummy002), (nb057AlphaDummy003 f a))]
      (Wff.imp (Wff.classEq
          (synCin (Class.cv (nb057AlphaDummy067)) (Class.cv (nb057AlphaDummy068)))
          (synC0)) (Wff.neg (Wff.classEq (Class.cv (nb057AlphaDummy066))
            (synCun (Class.cv (nb057AlphaDummy067)) (Class.cv (nb057AlphaDummy068))))))
      (Wff.imp (Wff.classEq (synCin (Class.cv (nb057AlphaDummy070 f))
            (Class.cv (nb057AlphaDummy071 f))) (synC0)) (Wff.neg
          (Wff.classEq (Class.cv (nb057AlphaDummy069 f))
            (synCun (Class.cv (nb057AlphaDummy070 f))
              (Class.cv (nb057AlphaDummy071 f)))))) :=
  (TAlphaWff.imp (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.neg (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0060) 0))
                          (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0061 f) 0))
                          (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0058) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0059 f) 0))
                            (TAlphaVar.there (freshVar_injective
                                (((Class.cv (nb057AlphaDummy060))).fv ∪ ((synC1c)).fv)
                                (by decide)) (freshVar_injective
                                (((Class.cv (nb057AlphaDummy062 f))).fv ∪ ((synC1c)).fv)
                                (by decide)) (TAlphaVar.here _ _ _))))))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0064) 0))
                          (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0065 f) 0))
                          (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0062) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0063 f) 0))
                            (TAlphaVar.here _ _ _)))))))))
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.neg (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0060) 0))
                          (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0061 f) 0))
                          (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0058) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0059 f) 0))
                            (TAlphaVar.there (freshVar_injective
                                (((Class.cv (nb057AlphaDummy060))).fv ∪ ((synC1c)).fv)
                                (by decide)) (freshVar_injective
                                (((Class.cv (nb057AlphaDummy062 f))).fv ∪ ((synC1c)).fv)
                                (by decide)) (TAlphaVar.here _ _ _))))))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0064) 0))
                          (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0065 f) 0))
                          (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0062) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0063 f) 0))
                            (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.reflOfClosed
        [((nb057AlphaDummy068), (nb057AlphaDummy071 f)),
          ((nb057AlphaDummy067), (nb057AlphaDummy070 f)),
          ((nb057AlphaDummy066), (nb057AlphaDummy069 f)),
          ((nb057AlphaDummy064), (nb057AlphaDummy065 f)),
          ((nb057AlphaDummy060), (nb057AlphaDummy062 f)),
          ((nb057AlphaDummy061), (nb057AlphaDummy063 f)),
          ((nb057AlphaDummy053), (nb057AlphaDummy055 f)),
          ((nb057AlphaDummy052), (nb057AlphaDummy054 f)),
          ((nb057AlphaDummy058), (nb057AlphaDummy059 f)),
          ((nb057AlphaDummy056), (nb057AlphaDummy057 f)),
          ((nb057AlphaDummy045), (nb057AlphaDummy048 f)),
          ((nb057AlphaDummy044), (nb057AlphaDummy047 f)),
          ((nb057AlphaDummy050), (nb057AlphaDummy051 f)),
          ((nb057AlphaDummy000), a), ((nb057AlphaDummy001), f),
          ((nb057AlphaDummy002), (nb057AlphaDummy003 f a))]
        (synC0) (by simp only [fv_syn_c0]))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv
          (TAlphaVar.there
            (freshVar_injective (((Class.cv (nb057AlphaDummy060))).fv ∪ ((synC1c)).fv)
              (by decide)) (freshVar_injective
              (((Class.cv (nb057AlphaDummy062 f))).fv ∪ ((synC1c)).fv) (by decide))
            (TAlphaVar.there (freshVar_injective
                (((Class.cv (nb057AlphaDummy060))).fv ∪ ((synC1c)).fv) (by decide))
              (freshVar_injective
                (((Class.cv (nb057AlphaDummy062 f))).fv ∪ ((synC1c)).fv) (by decide))
              (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                  (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0068) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0069 f) 0))
                            (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0066) 0))
                              (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0067 f) 0))
                              (TAlphaVar.there (freshVar_injective
                                  (((Class.cv (nb057AlphaDummy060))).fv ∪ ((synC1c)).fv)
                                  (by decide)) (freshVar_injective
                                  (((Class.cv (nb057AlphaDummy062 f))).fv ∪ ((synC1c)).fv)
                                  (by decide)) (TAlphaVar.here _ _ _))))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0068) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0069 f) 0))
                            (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0066) 0))
                              (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0067 f) 0))
                              (TAlphaVar.there (freshVar_injective
                                  (((Class.cv (nb057AlphaDummy060))).fv ∪ ((synC1c)).fv)
                                  (by decide)) (freshVar_injective
                                  (((Class.cv (nb057AlphaDummy062 f))).fv ∪ ((synC1c)).fv)
                                  (by decide)) (TAlphaVar.here _ _ _))))))))))
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                  (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0072) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0073 f) 0))
                            (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0070) 0))
                              (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0071 f) 0))
                              (TAlphaVar.here _ _ _)))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0072) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0073 f) 0))
                            (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0070) 0))
                              (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0071 f) 0))
                              (TAlphaVar.here _ _ _)))))))))))))))

/-- Checked nominal proof certificate identified upstream as `nb057_split_alpha_0034`. -/
@[expose]
noncomputable def nb057SplitAlpha0034 (f : Var) (a : Var) :
    TAlphaWff
      [((nb057AlphaDummy053), (nb057AlphaDummy055 f)),
        ((nb057AlphaDummy052), (nb057AlphaDummy054 f)),
        ((nb057AlphaDummy058), (nb057AlphaDummy059 f)),
        ((nb057AlphaDummy056), (nb057AlphaDummy057 f)),
        ((nb057AlphaDummy045), (nb057AlphaDummy048 f)),
        ((nb057AlphaDummy044), (nb057AlphaDummy047 f)),
        ((nb057AlphaDummy050), (nb057AlphaDummy051 f)),
        ((nb057AlphaDummy000), a), ((nb057AlphaDummy001), f),
        ((nb057AlphaDummy002), (nb057AlphaDummy003 f a))]
      (Wff.classEq (Class.cv (nb057AlphaDummy052))
        (synCphi (Class.cv (nb057AlphaDummy053))))
      (Wff.classEq (Class.cv (nb057AlphaDummy054 f))
        (synCphi (Class.cv (nb057AlphaDummy055 f)))) :=
  (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective
          (((Class.cv (nb057AlphaDummy044))).fv ∪ ((Class.cv (nb057AlphaDummy045))).fv)
          (by decide)) (freshVar_injective (((Class.cv (nb057AlphaDummy047 f))).fv ∪
            ((Class.cv (nb057AlphaDummy048 f))).fv) (by decide)) (TAlphaVar.here _ _ _)))
    (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
          (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
              (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0052) 0))
                (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0053 f) 0)) (TAlphaVar.there
                  (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0052) 1))
                  (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0053 f) 1))
                  (TAlphaVar.here _ _ _))))) (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there
                (freshVar_injective (((Class.cv (nb057AlphaDummy053))).fv) (by decide))
                (freshVar_injective (((Class.cv (nb057AlphaDummy055 f))).fv) (by decide))
                (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp (TAlphaWff.neg
                  (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                      (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb057_support_mem_0056) 1)) (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb057_support_mem_0057 f) 1))
                                  (TAlphaVar.there (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb057_support_mem_0056) 0))
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb057_support_mem_0057 f) 0))
                                    (TAlphaVar.there (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb057_support_mem_0054) 0))
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb057_support_mem_0055 f) 0))
                                      (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
                                (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                  (TAlphaClass.reflOfClosed
                                    [((nb057AlphaDummy068), (nb057AlphaDummy071 f)),
                                      ((nb057AlphaDummy067), (nb057AlphaDummy070 f)),
                                      ((nb057AlphaDummy066), (nb057AlphaDummy069 f)),
                                      ((nb057AlphaDummy064), (nb057AlphaDummy065 f)),
                                      ((nb057AlphaDummy060), (nb057AlphaDummy062 f)),
                                      ((nb057AlphaDummy061), (nb057AlphaDummy063 f)),
                                      ((nb057AlphaDummy053), (nb057AlphaDummy055 f)),
                                      ((nb057AlphaDummy052), (nb057AlphaDummy054 f)),
                                      ((nb057AlphaDummy058), (nb057AlphaDummy059 f)),
                                      ((nb057AlphaDummy056), (nb057AlphaDummy057 f)),
                                      ((nb057AlphaDummy045), (nb057AlphaDummy048 f)),
                                      ((nb057AlphaDummy044), (nb057AlphaDummy047 f)),
                                      ((nb057AlphaDummy050), (nb057AlphaDummy051 f)),
                                      ((nb057AlphaDummy000), a),
                                      ((nb057AlphaDummy001), f), ((nb057AlphaDummy002),
                                        (nb057AlphaDummy003 f a))]
                                    (synC1c) (by simp only [fv_syn_c1c])))
                                (TAlphaWff.neg (nb057SplitAlpha0033 f a))))))))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there
                          (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0054) 0))
                          (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0055 f) 0))
                          (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
                        [((nb057AlphaDummy064), (nb057AlphaDummy065 f)),
                          ((nb057AlphaDummy060), (nb057AlphaDummy062 f)),
                          ((nb057AlphaDummy061), (nb057AlphaDummy063 f)),
                          ((nb057AlphaDummy053), (nb057AlphaDummy055 f)),
                          ((nb057AlphaDummy052), (nb057AlphaDummy054 f)),
                          ((nb057AlphaDummy058), (nb057AlphaDummy059 f)),
                          ((nb057AlphaDummy056), (nb057AlphaDummy057 f)),
                          ((nb057AlphaDummy045), (nb057AlphaDummy048 f)),
                          ((nb057AlphaDummy044), (nb057AlphaDummy047 f)),
                          ((nb057AlphaDummy050), (nb057AlphaDummy051 f)),
                          ((nb057AlphaDummy000), a), ((nb057AlphaDummy001), f),
                          ((nb057AlphaDummy002), (nb057AlphaDummy003 f a))]
                        (synCnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
                  (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                      (TAlphaVar.there
                        (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0054) 0))
                        (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0055 f) 0))
                        (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.classMem
                      (TAlphaClass.cv (TAlphaVar.there
                          (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0054) 0))
                          (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0055 f) 0))
                          (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
                        [((nb057AlphaDummy064), (nb057AlphaDummy065 f)),
                          ((nb057AlphaDummy060), (nb057AlphaDummy062 f)),
                          ((nb057AlphaDummy061), (nb057AlphaDummy063 f)),
                          ((nb057AlphaDummy053), (nb057AlphaDummy055 f)),
                          ((nb057AlphaDummy052), (nb057AlphaDummy054 f)),
                          ((nb057AlphaDummy058), (nb057AlphaDummy059 f)),
                          ((nb057AlphaDummy056), (nb057AlphaDummy057 f)),
                          ((nb057AlphaDummy045), (nb057AlphaDummy048 f)),
                          ((nb057AlphaDummy044), (nb057AlphaDummy047 f)),
                          ((nb057AlphaDummy050), (nb057AlphaDummy051 f)),
                          ((nb057AlphaDummy000), a), ((nb057AlphaDummy001), f),
                          ((nb057AlphaDummy002), (nb057AlphaDummy003 f a))]
                        (synCnnc) (by simp only [fv_syn_cnnc]))))))))))))


end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired

end

/-! Certificates from `NAR4C057C001Part018`. -/


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

/-- Checked nominal proof certificate identified upstream as `nb057_split_alpha_0035`. -/
@[expose]
noncomputable def nb057SplitAlpha0035 (f : Var) (a : Var) :
    TAlphaWff
      [((nb057AlphaDummy068), (nb057AlphaDummy071 f)),
        ((nb057AlphaDummy067), (nb057AlphaDummy070 f)),
        ((nb057AlphaDummy066), (nb057AlphaDummy069 f)),
        ((nb057AlphaDummy064), (nb057AlphaDummy065 f)),
        ((nb057AlphaDummy060), (nb057AlphaDummy062 f)),
        ((nb057AlphaDummy061), (nb057AlphaDummy063 f)),
        ((nb057AlphaDummy086), (nb057AlphaDummy087 f)),
        ((nb057AlphaDummy084), (nb057AlphaDummy085 f)),
        ((nb057AlphaDummy053), (nb057AlphaDummy055 f)),
        ((nb057AlphaDummy052), (nb057AlphaDummy054 f)),
        ((nb057AlphaDummy082), (nb057AlphaDummy083 f)),
        ((nb057AlphaDummy056), (nb057AlphaDummy057 f)),
        ((nb057AlphaDummy045), (nb057AlphaDummy048 f)),
        ((nb057AlphaDummy044), (nb057AlphaDummy047 f)),
        ((nb057AlphaDummy050), (nb057AlphaDummy051 f)),
        ((nb057AlphaDummy000), a), ((nb057AlphaDummy001), f),
        ((nb057AlphaDummy002), (nb057AlphaDummy003 f a))]
      (Wff.imp (Wff.classEq
          (synCin (Class.cv (nb057AlphaDummy067)) (Class.cv (nb057AlphaDummy068)))
          (synC0)) (Wff.neg (Wff.classEq (Class.cv (nb057AlphaDummy066))
            (synCun (Class.cv (nb057AlphaDummy067)) (Class.cv (nb057AlphaDummy068))))))
      (Wff.imp (Wff.classEq (synCin (Class.cv (nb057AlphaDummy070 f))
            (Class.cv (nb057AlphaDummy071 f))) (synC0)) (Wff.neg
          (Wff.classEq (Class.cv (nb057AlphaDummy069 f))
            (synCun (Class.cv (nb057AlphaDummy070 f))
              (Class.cv (nb057AlphaDummy071 f)))))) :=
  (TAlphaWff.imp (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.neg (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0060) 0))
                          (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0061 f) 0))
                          (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0058) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0059 f) 0))
                            (TAlphaVar.there (freshVar_injective
                                (((Class.cv (nb057AlphaDummy060))).fv ∪ ((synC1c)).fv)
                                (by decide)) (freshVar_injective
                                (((Class.cv (nb057AlphaDummy062 f))).fv ∪ ((synC1c)).fv)
                                (by decide)) (TAlphaVar.here _ _ _))))))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0064) 0))
                          (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0065 f) 0))
                          (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0062) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0063 f) 0))
                            (TAlphaVar.here _ _ _)))))))))
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.neg (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0060) 0))
                          (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0061 f) 0))
                          (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0058) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0059 f) 0))
                            (TAlphaVar.there (freshVar_injective
                                (((Class.cv (nb057AlphaDummy060))).fv ∪ ((synC1c)).fv)
                                (by decide)) (freshVar_injective
                                (((Class.cv (nb057AlphaDummy062 f))).fv ∪ ((synC1c)).fv)
                                (by decide)) (TAlphaVar.here _ _ _))))))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0064) 0))
                          (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0065 f) 0))
                          (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0062) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0063 f) 0))
                            (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.reflOfClosed
        [((nb057AlphaDummy068), (nb057AlphaDummy071 f)),
          ((nb057AlphaDummy067), (nb057AlphaDummy070 f)),
          ((nb057AlphaDummy066), (nb057AlphaDummy069 f)),
          ((nb057AlphaDummy064), (nb057AlphaDummy065 f)),
          ((nb057AlphaDummy060), (nb057AlphaDummy062 f)),
          ((nb057AlphaDummy061), (nb057AlphaDummy063 f)),
          ((nb057AlphaDummy086), (nb057AlphaDummy087 f)),
          ((nb057AlphaDummy084), (nb057AlphaDummy085 f)),
          ((nb057AlphaDummy053), (nb057AlphaDummy055 f)),
          ((nb057AlphaDummy052), (nb057AlphaDummy054 f)),
          ((nb057AlphaDummy082), (nb057AlphaDummy083 f)),
          ((nb057AlphaDummy056), (nb057AlphaDummy057 f)),
          ((nb057AlphaDummy045), (nb057AlphaDummy048 f)),
          ((nb057AlphaDummy044), (nb057AlphaDummy047 f)),
          ((nb057AlphaDummy050), (nb057AlphaDummy051 f)),
          ((nb057AlphaDummy000), a), ((nb057AlphaDummy001), f),
          ((nb057AlphaDummy002), (nb057AlphaDummy003 f a))]
        (synC0) (by simp only [fv_syn_c0]))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv
          (TAlphaVar.there
            (freshVar_injective (((Class.cv (nb057AlphaDummy060))).fv ∪ ((synC1c)).fv)
              (by decide)) (freshVar_injective
              (((Class.cv (nb057AlphaDummy062 f))).fv ∪ ((synC1c)).fv) (by decide))
            (TAlphaVar.there (freshVar_injective
                (((Class.cv (nb057AlphaDummy060))).fv ∪ ((synC1c)).fv) (by decide))
              (freshVar_injective
                (((Class.cv (nb057AlphaDummy062 f))).fv ∪ ((synC1c)).fv) (by decide))
              (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                  (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0068) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0069 f) 0))
                            (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0066) 0))
                              (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0067 f) 0))
                              (TAlphaVar.there (freshVar_injective
                                  (((Class.cv (nb057AlphaDummy060))).fv ∪ ((synC1c)).fv)
                                  (by decide)) (freshVar_injective
                                  (((Class.cv (nb057AlphaDummy062 f))).fv ∪ ((synC1c)).fv)
                                  (by decide)) (TAlphaVar.here _ _ _))))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0068) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0069 f) 0))
                            (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0066) 0))
                              (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0067 f) 0))
                              (TAlphaVar.there (freshVar_injective
                                  (((Class.cv (nb057AlphaDummy060))).fv ∪ ((synC1c)).fv)
                                  (by decide)) (freshVar_injective
                                  (((Class.cv (nb057AlphaDummy062 f))).fv ∪ ((synC1c)).fv)
                                  (by decide)) (TAlphaVar.here _ _ _))))))))))
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                  (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0072) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0073 f) 0))
                            (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0070) 0))
                              (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0071 f) 0))
                              (TAlphaVar.here _ _ _)))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0072) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0073 f) 0))
                            (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0070) 0))
                              (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0071 f) 0))
                              (TAlphaVar.here _ _ _)))))))))))))))

/-- Checked nominal proof certificate identified upstream as `nb057_split_alpha_0036`. -/
@[expose]
noncomputable def nb057SplitAlpha0036 (f : Var) (a : Var) :
    TAlphaWff
      [((nb057AlphaDummy060), (nb057AlphaDummy062 f)),
        ((nb057AlphaDummy061), (nb057AlphaDummy063 f)),
        ((nb057AlphaDummy086), (nb057AlphaDummy087 f)),
        ((nb057AlphaDummy084), (nb057AlphaDummy085 f)),
        ((nb057AlphaDummy053), (nb057AlphaDummy055 f)),
        ((nb057AlphaDummy052), (nb057AlphaDummy054 f)),
        ((nb057AlphaDummy082), (nb057AlphaDummy083 f)),
        ((nb057AlphaDummy056), (nb057AlphaDummy057 f)),
        ((nb057AlphaDummy045), (nb057AlphaDummy048 f)),
        ((nb057AlphaDummy044), (nb057AlphaDummy047 f)),
        ((nb057AlphaDummy050), (nb057AlphaDummy051 f)),
        ((nb057AlphaDummy000), a), ((nb057AlphaDummy001), f),
        ((nb057AlphaDummy002), (nb057AlphaDummy003 f a))]
      (Wff.imp (Wff.classMem (Class.cv (nb057AlphaDummy060))
          (Class.cv (nb057AlphaDummy053))) (Wff.neg
          (Wff.classEq (Class.cv (nb057AlphaDummy061))
            (synCif (Wff.classMem (Class.cv (nb057AlphaDummy060)) (synCnnc))
              (synCplc (Class.cv (nb057AlphaDummy060)) (synC1c))
              (Class.cv (nb057AlphaDummy060))))))
      (Wff.imp (Wff.classMem (Class.cv (nb057AlphaDummy062 f))
          (Class.cv (nb057AlphaDummy055 f))) (Wff.neg
          (Wff.classEq (Class.cv (nb057AlphaDummy063 f))
            (synCif (Wff.classMem (Class.cv (nb057AlphaDummy062 f)) (synCnnc))
              (synCplc (Class.cv (nb057AlphaDummy062 f)) (synC1c))
              (Class.cv (nb057AlphaDummy062 f)))))) :=
  (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0052) 0))
          (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0053 f) 0))
          (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0052) 1))
            (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0053 f) 1))
            (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0082) 0))
              (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0083 f) 0))
              (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0080) 0))
                (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0081 f) 0))
                (TAlphaVar.here _ _ _))))))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv
          (TAlphaVar.there
            (freshVar_injective (((Class.cv (nb057AlphaDummy053))).fv) (by decide))
            (freshVar_injective (((Class.cv (nb057AlphaDummy055 f))).fv) (by decide))
            (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp (TAlphaWff.neg
              (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                  (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                          (TAlphaClass.cv (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0056) 1))
                              (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0057 f) 1))
                              (TAlphaVar.there (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb057_support_mem_0056) 0)) (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb057_support_mem_0057 f) 0))
                                (TAlphaVar.there (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb057_support_mem_0054) 0)) (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb057_support_mem_0055 f) 0))
                                  (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.reflOfClosed
                                [((nb057AlphaDummy068), (nb057AlphaDummy071 f)),
                                  ((nb057AlphaDummy067), (nb057AlphaDummy070 f)),
                                  ((nb057AlphaDummy066), (nb057AlphaDummy069 f)),
                                  ((nb057AlphaDummy064), (nb057AlphaDummy065 f)),
                                  ((nb057AlphaDummy060), (nb057AlphaDummy062 f)),
                                  ((nb057AlphaDummy061), (nb057AlphaDummy063 f)),
                                  ((nb057AlphaDummy086), (nb057AlphaDummy087 f)),
                                  ((nb057AlphaDummy084), (nb057AlphaDummy085 f)),
                                  ((nb057AlphaDummy053), (nb057AlphaDummy055 f)),
                                  ((nb057AlphaDummy052), (nb057AlphaDummy054 f)),
                                  ((nb057AlphaDummy082), (nb057AlphaDummy083 f)),
                                  ((nb057AlphaDummy056), (nb057AlphaDummy057 f)),
                                  ((nb057AlphaDummy045), (nb057AlphaDummy048 f)),
                                  ((nb057AlphaDummy044), (nb057AlphaDummy047 f)),
                                  ((nb057AlphaDummy050), (nb057AlphaDummy051 f)),
                                  ((nb057AlphaDummy000), a), ((nb057AlphaDummy001), f),
                                  ((nb057AlphaDummy002), (nb057AlphaDummy003 f a))]
                                (synC1c) (by simp only [fv_syn_c1c])))
                            (TAlphaWff.neg (nb057SplitAlpha0035 f a))))))))
                (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there
                      (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0054) 0))
                      (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0055 f) 0))
                      (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
                    [((nb057AlphaDummy064), (nb057AlphaDummy065 f)),
                      ((nb057AlphaDummy060), (nb057AlphaDummy062 f)),
                      ((nb057AlphaDummy061), (nb057AlphaDummy063 f)),
                      ((nb057AlphaDummy086), (nb057AlphaDummy087 f)),
                      ((nb057AlphaDummy084), (nb057AlphaDummy085 f)),
                      ((nb057AlphaDummy053), (nb057AlphaDummy055 f)),
                      ((nb057AlphaDummy052), (nb057AlphaDummy054 f)),
                      ((nb057AlphaDummy082), (nb057AlphaDummy083 f)),
                      ((nb057AlphaDummy056), (nb057AlphaDummy057 f)),
                      ((nb057AlphaDummy045), (nb057AlphaDummy048 f)),
                      ((nb057AlphaDummy044), (nb057AlphaDummy047 f)),
                      ((nb057AlphaDummy050), (nb057AlphaDummy051 f)),
                      ((nb057AlphaDummy000), a), ((nb057AlphaDummy001), f),
                      ((nb057AlphaDummy002), (nb057AlphaDummy003 f a))]
                    (synCnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                  (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0054) 0))
                    (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0055 f) 0))
                    (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv
                    (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0054) 0))
                      (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0055 f) 0))
                      (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
                    [((nb057AlphaDummy064), (nb057AlphaDummy065 f)),
                      ((nb057AlphaDummy060), (nb057AlphaDummy062 f)),
                      ((nb057AlphaDummy061), (nb057AlphaDummy063 f)),
                      ((nb057AlphaDummy086), (nb057AlphaDummy087 f)),
                      ((nb057AlphaDummy084), (nb057AlphaDummy085 f)),
                      ((nb057AlphaDummy053), (nb057AlphaDummy055 f)),
                      ((nb057AlphaDummy052), (nb057AlphaDummy054 f)),
                      ((nb057AlphaDummy082), (nb057AlphaDummy083 f)),
                      ((nb057AlphaDummy056), (nb057AlphaDummy057 f)),
                      ((nb057AlphaDummy045), (nb057AlphaDummy048 f)),
                      ((nb057AlphaDummy044), (nb057AlphaDummy047 f)),
                      ((nb057AlphaDummy050), (nb057AlphaDummy051 f)),
                      ((nb057AlphaDummy000), a), ((nb057AlphaDummy001), f),
                      ((nb057AlphaDummy002), (nb057AlphaDummy003 f a))]
                    (synCnnc) (by simp only [fv_syn_cnnc]))))))))))

/-- Checked nominal proof certificate identified upstream as `nb057_split_alpha_0037`. -/
@[expose]
noncomputable def nb057SplitAlpha0037 (f : Var) (a : Var) :
    TAlphaWff
      [((nb057AlphaDummy082), (nb057AlphaDummy083 f)),
        ((nb057AlphaDummy056), (nb057AlphaDummy057 f)),
        ((nb057AlphaDummy045), (nb057AlphaDummy048 f)),
        ((nb057AlphaDummy044), (nb057AlphaDummy047 f)),
        ((nb057AlphaDummy050), (nb057AlphaDummy051 f)),
        ((nb057AlphaDummy000), a), ((nb057AlphaDummy001), f),
        ((nb057AlphaDummy002), (nb057AlphaDummy003 f a))]
      (Wff.imp (Wff.classMem (Class.cv (nb057AlphaDummy082))
          (Class.cab (nb057AlphaDummy052)
            (synWrex (nb057AlphaDummy053) (Class.cv (nb057AlphaDummy045))
              (Wff.classEq (Class.cv (nb057AlphaDummy052))
                (synCun (synCphi (Class.cv (nb057AlphaDummy053))) (synCsn (synC0c)))))))
        (Wff.neg (Wff.classMem (Class.cv (nb057AlphaDummy082))
            (Class.cab (nb057AlphaDummy052)
              (synWrex (nb057AlphaDummy053) (Class.cv (nb057AlphaDummy045))
                (Wff.classEq (Class.cv (nb057AlphaDummy052))
                  (synCun (synCphi (Class.cv (nb057AlphaDummy053)))
                    (synCsn (synC0c)))))))))
      (Wff.imp (Wff.classMem (Class.cv (nb057AlphaDummy083 f))
          (Class.cab (nb057AlphaDummy054 f)
            (synWrex (nb057AlphaDummy055 f) (Class.cv (nb057AlphaDummy048 f))
              (Wff.classEq (Class.cv (nb057AlphaDummy054 f))
                (synCun (synCphi (Class.cv (nb057AlphaDummy055 f)))
                  (synCsn (synC0c))))))) (Wff.neg
          (Wff.classMem (Class.cv (nb057AlphaDummy083 f))
            (Class.cab (nb057AlphaDummy054 f)
              (synWrex (nb057AlphaDummy055 f) (Class.cv (nb057AlphaDummy048 f))
                (Wff.classEq (Class.cv (nb057AlphaDummy054 f))
                  (synCun (synCphi (Class.cv (nb057AlphaDummy055 f)))
                    (synCsn (synC0c))))))))) :=
  (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.ex (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0074) 1))
                  (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0076 f) 1)) (TAlphaVar.there
                    (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0074) 0))
                    (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0076 f) 0))
                    (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0078) 0))
                      (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0079 f) 0))
                      (TAlphaVar.there
                        (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0075) 0))
                        (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0077 f) 0))
                        (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
                (TAlphaVar.there (freshVar_injective (((Class.cv (nb057AlphaDummy044))).fv ∪
                      ((Class.cv (nb057AlphaDummy045))).fv) (by decide)) (freshVar_injective
                    (((Class.cv (nb057AlphaDummy047 f))).fv ∪
                      ((Class.cv (nb057AlphaDummy048 f))).fv) (by decide))
                  (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                        (TAlphaWff.neg (TAlphaWff.conj
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cab (TAlphaWff.ex
                                  (TAlphaWff.neg (nb057SplitAlpha0036 f a)))))
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cab (TAlphaWff.ex
                                  (TAlphaWff.neg (nb057SplitAlpha0036 f a)))))))))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                      (TAlphaClass.reflOfClosed
                        [((nb057AlphaDummy084), (nb057AlphaDummy085 f)),
                          ((nb057AlphaDummy053), (nb057AlphaDummy055 f)),
                          ((nb057AlphaDummy052), (nb057AlphaDummy054 f)),
                          ((nb057AlphaDummy082), (nb057AlphaDummy083 f)),
                          ((nb057AlphaDummy056), (nb057AlphaDummy057 f)),
                          ((nb057AlphaDummy045), (nb057AlphaDummy048 f)),
                          ((nb057AlphaDummy044), (nb057AlphaDummy047 f)),
                          ((nb057AlphaDummy050), (nb057AlphaDummy051 f)),
                          ((nb057AlphaDummy000), a), ((nb057AlphaDummy001), f),
                          ((nb057AlphaDummy002), (nb057AlphaDummy003 f a))]
                        (synCcompl (synCsn (synC0c)))
                        (by simp only [fv_syn_ccompl, fv_syn_csn, fv_syn_c0c])))))))))))
    (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
          (TAlphaWff.ex (TAlphaWff.conj
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                  (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0074) 1))
                    (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0076 f) 1))
                    (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0074) 0))
                      (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0076 f) 0))
                      (TAlphaVar.there
                        (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0078) 0))
                        (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0079 f) 0))
                        (TAlphaVar.there
                          (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0075) 0))
                          (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0077 f) 0))
                          (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
                  (TAlphaVar.there (freshVar_injective
                      (((Class.cv (nb057AlphaDummy044))).fv ∪
                        ((Class.cv (nb057AlphaDummy045))).fv) (by decide))
                    (freshVar_injective (((Class.cv (nb057AlphaDummy047 f))).fv ∪
                        ((Class.cv (nb057AlphaDummy048 f))).fv) (by decide))
                    (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cab (TAlphaWff.ex
                                    (TAlphaWff.neg (nb057SplitAlpha0036 f a)))))
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cab (TAlphaWff.ex
                                    (TAlphaWff.neg (nb057SplitAlpha0036 f a)))))))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.reflOfClosed
                          [((nb057AlphaDummy084), (nb057AlphaDummy085 f)),
                            ((nb057AlphaDummy053), (nb057AlphaDummy055 f)),
                            ((nb057AlphaDummy052), (nb057AlphaDummy054 f)),
                            ((nb057AlphaDummy082), (nb057AlphaDummy083 f)),
                            ((nb057AlphaDummy056), (nb057AlphaDummy057 f)),
                            ((nb057AlphaDummy045), (nb057AlphaDummy048 f)),
                            ((nb057AlphaDummy044), (nb057AlphaDummy047 f)),
                            ((nb057AlphaDummy050), (nb057AlphaDummy051 f)),
                            ((nb057AlphaDummy000), a), ((nb057AlphaDummy001), f),
                            ((nb057AlphaDummy002), (nb057AlphaDummy003 f a))]
                          (synCcompl (synCsn (synC0c))) (by
                            simp only [fv_syn_ccompl, fv_syn_csn, fv_syn_c0c])))))))))))))

/-- Checked nominal proof certificate identified upstream as `nb057_split_alpha_0038`. -/
@[expose]
noncomputable def nb057SplitAlpha0038 (f : Var) (a : Var) :
    TAlphaWff
      [((nb057AlphaDummy104), (nb057AlphaDummy107 f)),
        ((nb057AlphaDummy103), (nb057AlphaDummy106 f)),
        ((nb057AlphaDummy102), (nb057AlphaDummy105 f)),
        ((nb057AlphaDummy100), (nb057AlphaDummy101 f)),
        ((nb057AlphaDummy096), (nb057AlphaDummy098 f)),
        ((nb057AlphaDummy097), (nb057AlphaDummy099 f)),
        ((nb057AlphaDummy089), (nb057AlphaDummy091 f)),
        ((nb057AlphaDummy088), (nb057AlphaDummy090 f)),
        ((nb057AlphaDummy094), (nb057AlphaDummy095 f)),
        ((nb057AlphaDummy092), (nb057AlphaDummy093 f)),
        ((nb057AlphaDummy046), (nb057AlphaDummy049 f)),
        ((nb057AlphaDummy045), (nb057AlphaDummy048 f)),
        ((nb057AlphaDummy044), (nb057AlphaDummy047 f)),
        ((nb057AlphaDummy050), (nb057AlphaDummy051 f)),
        ((nb057AlphaDummy000), a), ((nb057AlphaDummy001), f),
        ((nb057AlphaDummy002), (nb057AlphaDummy003 f a))]
      (Wff.imp (Wff.classEq
          (synCin (Class.cv (nb057AlphaDummy103)) (Class.cv (nb057AlphaDummy104)))
          (synC0)) (Wff.neg (Wff.classEq (Class.cv (nb057AlphaDummy102))
            (synCun (Class.cv (nb057AlphaDummy103)) (Class.cv (nb057AlphaDummy104))))))
      (Wff.imp (Wff.classEq (synCin (Class.cv (nb057AlphaDummy106 f))
            (Class.cv (nb057AlphaDummy107 f))) (synC0)) (Wff.neg
          (Wff.classEq (Class.cv (nb057AlphaDummy105 f))
            (synCun (Class.cv (nb057AlphaDummy106 f))
              (Class.cv (nb057AlphaDummy107 f)))))) :=
  (TAlphaWff.imp (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.neg (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0098) 0))
                          (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0099 f) 0))
                          (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0096) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0097 f) 0))
                            (TAlphaVar.there (freshVar_injective
                                (((Class.cv (nb057AlphaDummy096))).fv ∪ ((synC1c)).fv)
                                (by decide)) (freshVar_injective
                                (((Class.cv (nb057AlphaDummy098 f))).fv ∪ ((synC1c)).fv)
                                (by decide)) (TAlphaVar.here _ _ _))))))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0102) 0))
                          (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0103 f) 0))
                          (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0100) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0101 f) 0))
                            (TAlphaVar.here _ _ _)))))))))
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.neg (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0098) 0))
                          (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0099 f) 0))
                          (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0096) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0097 f) 0))
                            (TAlphaVar.there (freshVar_injective
                                (((Class.cv (nb057AlphaDummy096))).fv ∪ ((synC1c)).fv)
                                (by decide)) (freshVar_injective
                                (((Class.cv (nb057AlphaDummy098 f))).fv ∪ ((synC1c)).fv)
                                (by decide)) (TAlphaVar.here _ _ _))))))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0102) 0))
                          (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0103 f) 0))
                          (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0100) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0101 f) 0))
                            (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.reflOfClosed
        [((nb057AlphaDummy104), (nb057AlphaDummy107 f)),
          ((nb057AlphaDummy103), (nb057AlphaDummy106 f)),
          ((nb057AlphaDummy102), (nb057AlphaDummy105 f)),
          ((nb057AlphaDummy100), (nb057AlphaDummy101 f)),
          ((nb057AlphaDummy096), (nb057AlphaDummy098 f)),
          ((nb057AlphaDummy097), (nb057AlphaDummy099 f)),
          ((nb057AlphaDummy089), (nb057AlphaDummy091 f)),
          ((nb057AlphaDummy088), (nb057AlphaDummy090 f)),
          ((nb057AlphaDummy094), (nb057AlphaDummy095 f)),
          ((nb057AlphaDummy092), (nb057AlphaDummy093 f)),
          ((nb057AlphaDummy046), (nb057AlphaDummy049 f)),
          ((nb057AlphaDummy045), (nb057AlphaDummy048 f)),
          ((nb057AlphaDummy044), (nb057AlphaDummy047 f)),
          ((nb057AlphaDummy050), (nb057AlphaDummy051 f)),
          ((nb057AlphaDummy000), a), ((nb057AlphaDummy001), f),
          ((nb057AlphaDummy002), (nb057AlphaDummy003 f a))]
        (synC0) (by simp only [fv_syn_c0]))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv
          (TAlphaVar.there
            (freshVar_injective (((Class.cv (nb057AlphaDummy096))).fv ∪ ((synC1c)).fv)
              (by decide)) (freshVar_injective
              (((Class.cv (nb057AlphaDummy098 f))).fv ∪ ((synC1c)).fv) (by decide))
            (TAlphaVar.there (freshVar_injective
                (((Class.cv (nb057AlphaDummy096))).fv ∪ ((synC1c)).fv) (by decide))
              (freshVar_injective
                (((Class.cv (nb057AlphaDummy098 f))).fv ∪ ((synC1c)).fv) (by decide))
              (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                  (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0106) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0107 f) 0))
                            (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0104) 0))
                              (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0105 f) 0))
                              (TAlphaVar.there (freshVar_injective
                                  (((Class.cv (nb057AlphaDummy096))).fv ∪ ((synC1c)).fv)
                                  (by decide)) (freshVar_injective
                                  (((Class.cv (nb057AlphaDummy098 f))).fv ∪ ((synC1c)).fv)
                                  (by decide)) (TAlphaVar.here _ _ _))))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0106) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0107 f) 0))
                            (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0104) 0))
                              (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0105 f) 0))
                              (TAlphaVar.there (freshVar_injective
                                  (((Class.cv (nb057AlphaDummy096))).fv ∪ ((synC1c)).fv)
                                  (by decide)) (freshVar_injective
                                  (((Class.cv (nb057AlphaDummy098 f))).fv ∪ ((synC1c)).fv)
                                  (by decide)) (TAlphaVar.here _ _ _))))))))))
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                  (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0110) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0111 f) 0))
                            (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0108) 0))
                              (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0109 f) 0))
                              (TAlphaVar.here _ _ _)))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0110) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0111 f) 0))
                            (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0108) 0))
                              (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0109 f) 0))
                              (TAlphaVar.here _ _ _)))))))))))))))

/-- Checked nominal proof certificate identified upstream as `nb057_split_alpha_0039`. -/
@[expose]
noncomputable def nb057SplitAlpha0039 (f : Var) (a : Var) :
    TAlphaWff
      [((nb057AlphaDummy089), (nb057AlphaDummy091 f)),
        ((nb057AlphaDummy088), (nb057AlphaDummy090 f)),
        ((nb057AlphaDummy094), (nb057AlphaDummy095 f)),
        ((nb057AlphaDummy092), (nb057AlphaDummy093 f)),
        ((nb057AlphaDummy046), (nb057AlphaDummy049 f)),
        ((nb057AlphaDummy045), (nb057AlphaDummy048 f)),
        ((nb057AlphaDummy044), (nb057AlphaDummy047 f)),
        ((nb057AlphaDummy050), (nb057AlphaDummy051 f)),
        ((nb057AlphaDummy000), a), ((nb057AlphaDummy001), f),
        ((nb057AlphaDummy002), (nb057AlphaDummy003 f a))]
      (Wff.classEq (Class.cv (nb057AlphaDummy088))
        (synCphi (Class.cv (nb057AlphaDummy089))))
      (Wff.classEq (Class.cv (nb057AlphaDummy090 f))
        (synCphi (Class.cv (nb057AlphaDummy091 f)))) :=
  (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective
          (((Class.cv (nb057AlphaDummy044))).fv ∪ ((Class.cv (nb057AlphaDummy046))).fv)
          (by decide)) (freshVar_injective (((Class.cv (nb057AlphaDummy047 f))).fv ∪
            ((Class.cv (nb057AlphaDummy049 f))).fv) (by decide)) (TAlphaVar.here _ _ _)))
    (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
          (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
              (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0090) 0))
                (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0091 f) 0)) (TAlphaVar.there
                  (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0090) 1))
                  (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0091 f) 1))
                  (TAlphaVar.here _ _ _))))) (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there
                (freshVar_injective (((Class.cv (nb057AlphaDummy089))).fv) (by decide))
                (freshVar_injective (((Class.cv (nb057AlphaDummy091 f))).fv) (by decide))
                (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp (TAlphaWff.neg
                  (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                      (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb057_support_mem_0094) 1)) (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb057_support_mem_0095 f) 1))
                                  (TAlphaVar.there (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb057_support_mem_0094) 0))
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb057_support_mem_0095 f) 0))
                                    (TAlphaVar.there (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb057_support_mem_0092) 0))
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb057_support_mem_0093 f) 0))
                                      (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
                                (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                  (TAlphaClass.reflOfClosed
                                    [((nb057AlphaDummy104), (nb057AlphaDummy107 f)),
                                      ((nb057AlphaDummy103), (nb057AlphaDummy106 f)),
                                      ((nb057AlphaDummy102), (nb057AlphaDummy105 f)),
                                      ((nb057AlphaDummy100), (nb057AlphaDummy101 f)),
                                      ((nb057AlphaDummy096), (nb057AlphaDummy098 f)),
                                      ((nb057AlphaDummy097), (nb057AlphaDummy099 f)),
                                      ((nb057AlphaDummy089), (nb057AlphaDummy091 f)),
                                      ((nb057AlphaDummy088), (nb057AlphaDummy090 f)),
                                      ((nb057AlphaDummy094), (nb057AlphaDummy095 f)),
                                      ((nb057AlphaDummy092), (nb057AlphaDummy093 f)),
                                      ((nb057AlphaDummy046), (nb057AlphaDummy049 f)),
                                      ((nb057AlphaDummy045), (nb057AlphaDummy048 f)),
                                      ((nb057AlphaDummy044), (nb057AlphaDummy047 f)),
                                      ((nb057AlphaDummy050), (nb057AlphaDummy051 f)),
                                      ((nb057AlphaDummy000), a),
                                      ((nb057AlphaDummy001), f), ((nb057AlphaDummy002),
                                        (nb057AlphaDummy003 f a))]
                                    (synC1c) (by simp only [fv_syn_c1c])))
                                (TAlphaWff.neg (nb057SplitAlpha0038 f a))))))))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there
                          (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0092) 0))
                          (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0093 f) 0))
                          (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
                        [((nb057AlphaDummy100), (nb057AlphaDummy101 f)),
                          ((nb057AlphaDummy096), (nb057AlphaDummy098 f)),
                          ((nb057AlphaDummy097), (nb057AlphaDummy099 f)),
                          ((nb057AlphaDummy089), (nb057AlphaDummy091 f)),
                          ((nb057AlphaDummy088), (nb057AlphaDummy090 f)),
                          ((nb057AlphaDummy094), (nb057AlphaDummy095 f)),
                          ((nb057AlphaDummy092), (nb057AlphaDummy093 f)),
                          ((nb057AlphaDummy046), (nb057AlphaDummy049 f)),
                          ((nb057AlphaDummy045), (nb057AlphaDummy048 f)),
                          ((nb057AlphaDummy044), (nb057AlphaDummy047 f)),
                          ((nb057AlphaDummy050), (nb057AlphaDummy051 f)),
                          ((nb057AlphaDummy000), a), ((nb057AlphaDummy001), f),
                          ((nb057AlphaDummy002), (nb057AlphaDummy003 f a))]
                        (synCnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
                  (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                      (TAlphaVar.there
                        (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0092) 0))
                        (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0093 f) 0))
                        (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.classMem
                      (TAlphaClass.cv (TAlphaVar.there
                          (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0092) 0))
                          (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0093 f) 0))
                          (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
                        [((nb057AlphaDummy100), (nb057AlphaDummy101 f)),
                          ((nb057AlphaDummy096), (nb057AlphaDummy098 f)),
                          ((nb057AlphaDummy097), (nb057AlphaDummy099 f)),
                          ((nb057AlphaDummy089), (nb057AlphaDummy091 f)),
                          ((nb057AlphaDummy088), (nb057AlphaDummy090 f)),
                          ((nb057AlphaDummy094), (nb057AlphaDummy095 f)),
                          ((nb057AlphaDummy092), (nb057AlphaDummy093 f)),
                          ((nb057AlphaDummy046), (nb057AlphaDummy049 f)),
                          ((nb057AlphaDummy045), (nb057AlphaDummy048 f)),
                          ((nb057AlphaDummy044), (nb057AlphaDummy047 f)),
                          ((nb057AlphaDummy050), (nb057AlphaDummy051 f)),
                          ((nb057AlphaDummy000), a), ((nb057AlphaDummy001), f),
                          ((nb057AlphaDummy002), (nb057AlphaDummy003 f a))]
                        (synCnnc) (by simp only [fv_syn_cnnc]))))))))))))


end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired

end

/-! Certificates from `NAR4C057C001Part019`. -/


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

/-- Checked nominal proof certificate identified upstream as `nb057_split_alpha_0040`. -/
@[expose]
noncomputable def nb057SplitAlpha0040 (f : Var) (a : Var) :
    TAlphaWff
      [((nb057AlphaDummy104), (nb057AlphaDummy107 f)),
        ((nb057AlphaDummy103), (nb057AlphaDummy106 f)),
        ((nb057AlphaDummy102), (nb057AlphaDummy105 f)),
        ((nb057AlphaDummy100), (nb057AlphaDummy101 f)),
        ((nb057AlphaDummy096), (nb057AlphaDummy098 f)),
        ((nb057AlphaDummy097), (nb057AlphaDummy099 f)),
        ((nb057AlphaDummy122), (nb057AlphaDummy123 f)),
        ((nb057AlphaDummy120), (nb057AlphaDummy121 f)),
        ((nb057AlphaDummy089), (nb057AlphaDummy091 f)),
        ((nb057AlphaDummy088), (nb057AlphaDummy090 f)),
        ((nb057AlphaDummy118), (nb057AlphaDummy119 f)),
        ((nb057AlphaDummy092), (nb057AlphaDummy093 f)),
        ((nb057AlphaDummy046), (nb057AlphaDummy049 f)),
        ((nb057AlphaDummy045), (nb057AlphaDummy048 f)),
        ((nb057AlphaDummy044), (nb057AlphaDummy047 f)),
        ((nb057AlphaDummy050), (nb057AlphaDummy051 f)),
        ((nb057AlphaDummy000), a), ((nb057AlphaDummy001), f),
        ((nb057AlphaDummy002), (nb057AlphaDummy003 f a))]
      (Wff.imp (Wff.classEq
          (synCin (Class.cv (nb057AlphaDummy103)) (Class.cv (nb057AlphaDummy104)))
          (synC0)) (Wff.neg (Wff.classEq (Class.cv (nb057AlphaDummy102))
            (synCun (Class.cv (nb057AlphaDummy103)) (Class.cv (nb057AlphaDummy104))))))
      (Wff.imp (Wff.classEq (synCin (Class.cv (nb057AlphaDummy106 f))
            (Class.cv (nb057AlphaDummy107 f))) (synC0)) (Wff.neg
          (Wff.classEq (Class.cv (nb057AlphaDummy105 f))
            (synCun (Class.cv (nb057AlphaDummy106 f))
              (Class.cv (nb057AlphaDummy107 f)))))) :=
  (TAlphaWff.imp (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.neg (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0098) 0))
                          (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0099 f) 0))
                          (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0096) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0097 f) 0))
                            (TAlphaVar.there (freshVar_injective
                                (((Class.cv (nb057AlphaDummy096))).fv ∪ ((synC1c)).fv)
                                (by decide)) (freshVar_injective
                                (((Class.cv (nb057AlphaDummy098 f))).fv ∪ ((synC1c)).fv)
                                (by decide)) (TAlphaVar.here _ _ _))))))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0102) 0))
                          (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0103 f) 0))
                          (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0100) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0101 f) 0))
                            (TAlphaVar.here _ _ _)))))))))
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.neg (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0098) 0))
                          (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0099 f) 0))
                          (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0096) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0097 f) 0))
                            (TAlphaVar.there (freshVar_injective
                                (((Class.cv (nb057AlphaDummy096))).fv ∪ ((synC1c)).fv)
                                (by decide)) (freshVar_injective
                                (((Class.cv (nb057AlphaDummy098 f))).fv ∪ ((synC1c)).fv)
                                (by decide)) (TAlphaVar.here _ _ _))))))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0102) 0))
                          (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0103 f) 0))
                          (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0100) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0101 f) 0))
                            (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.reflOfClosed
        [((nb057AlphaDummy104), (nb057AlphaDummy107 f)),
          ((nb057AlphaDummy103), (nb057AlphaDummy106 f)),
          ((nb057AlphaDummy102), (nb057AlphaDummy105 f)),
          ((nb057AlphaDummy100), (nb057AlphaDummy101 f)),
          ((nb057AlphaDummy096), (nb057AlphaDummy098 f)),
          ((nb057AlphaDummy097), (nb057AlphaDummy099 f)),
          ((nb057AlphaDummy122), (nb057AlphaDummy123 f)),
          ((nb057AlphaDummy120), (nb057AlphaDummy121 f)),
          ((nb057AlphaDummy089), (nb057AlphaDummy091 f)),
          ((nb057AlphaDummy088), (nb057AlphaDummy090 f)),
          ((nb057AlphaDummy118), (nb057AlphaDummy119 f)),
          ((nb057AlphaDummy092), (nb057AlphaDummy093 f)),
          ((nb057AlphaDummy046), (nb057AlphaDummy049 f)),
          ((nb057AlphaDummy045), (nb057AlphaDummy048 f)),
          ((nb057AlphaDummy044), (nb057AlphaDummy047 f)),
          ((nb057AlphaDummy050), (nb057AlphaDummy051 f)),
          ((nb057AlphaDummy000), a), ((nb057AlphaDummy001), f),
          ((nb057AlphaDummy002), (nb057AlphaDummy003 f a))]
        (synC0) (by simp only [fv_syn_c0]))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv
          (TAlphaVar.there
            (freshVar_injective (((Class.cv (nb057AlphaDummy096))).fv ∪ ((synC1c)).fv)
              (by decide)) (freshVar_injective
              (((Class.cv (nb057AlphaDummy098 f))).fv ∪ ((synC1c)).fv) (by decide))
            (TAlphaVar.there (freshVar_injective
                (((Class.cv (nb057AlphaDummy096))).fv ∪ ((synC1c)).fv) (by decide))
              (freshVar_injective
                (((Class.cv (nb057AlphaDummy098 f))).fv ∪ ((synC1c)).fv) (by decide))
              (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                  (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0106) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0107 f) 0))
                            (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0104) 0))
                              (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0105 f) 0))
                              (TAlphaVar.there (freshVar_injective
                                  (((Class.cv (nb057AlphaDummy096))).fv ∪ ((synC1c)).fv)
                                  (by decide)) (freshVar_injective
                                  (((Class.cv (nb057AlphaDummy098 f))).fv ∪ ((synC1c)).fv)
                                  (by decide)) (TAlphaVar.here _ _ _))))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0106) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0107 f) 0))
                            (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0104) 0))
                              (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0105 f) 0))
                              (TAlphaVar.there (freshVar_injective
                                  (((Class.cv (nb057AlphaDummy096))).fv ∪ ((synC1c)).fv)
                                  (by decide)) (freshVar_injective
                                  (((Class.cv (nb057AlphaDummy098 f))).fv ∪ ((synC1c)).fv)
                                  (by decide)) (TAlphaVar.here _ _ _))))))))))
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                  (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0110) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0111 f) 0))
                            (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0108) 0))
                              (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0109 f) 0))
                              (TAlphaVar.here _ _ _)))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0110) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0111 f) 0))
                            (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0108) 0))
                              (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0109 f) 0))
                              (TAlphaVar.here _ _ _)))))))))))))))

/-- Checked nominal proof certificate identified upstream as `nb057_split_alpha_0041`. -/
@[expose]
noncomputable def nb057SplitAlpha0041 (f : Var) (a : Var) :
    TAlphaWff
      [((nb057AlphaDummy096), (nb057AlphaDummy098 f)),
        ((nb057AlphaDummy097), (nb057AlphaDummy099 f)),
        ((nb057AlphaDummy122), (nb057AlphaDummy123 f)),
        ((nb057AlphaDummy120), (nb057AlphaDummy121 f)),
        ((nb057AlphaDummy089), (nb057AlphaDummy091 f)),
        ((nb057AlphaDummy088), (nb057AlphaDummy090 f)),
        ((nb057AlphaDummy118), (nb057AlphaDummy119 f)),
        ((nb057AlphaDummy092), (nb057AlphaDummy093 f)),
        ((nb057AlphaDummy046), (nb057AlphaDummy049 f)),
        ((nb057AlphaDummy045), (nb057AlphaDummy048 f)),
        ((nb057AlphaDummy044), (nb057AlphaDummy047 f)),
        ((nb057AlphaDummy050), (nb057AlphaDummy051 f)),
        ((nb057AlphaDummy000), a), ((nb057AlphaDummy001), f),
        ((nb057AlphaDummy002), (nb057AlphaDummy003 f a))]
      (Wff.imp (Wff.classMem (Class.cv (nb057AlphaDummy096))
          (Class.cv (nb057AlphaDummy089))) (Wff.neg
          (Wff.classEq (Class.cv (nb057AlphaDummy097))
            (synCif (Wff.classMem (Class.cv (nb057AlphaDummy096)) (synCnnc))
              (synCplc (Class.cv (nb057AlphaDummy096)) (synC1c))
              (Class.cv (nb057AlphaDummy096))))))
      (Wff.imp (Wff.classMem (Class.cv (nb057AlphaDummy098 f))
          (Class.cv (nb057AlphaDummy091 f))) (Wff.neg
          (Wff.classEq (Class.cv (nb057AlphaDummy099 f))
            (synCif (Wff.classMem (Class.cv (nb057AlphaDummy098 f)) (synCnnc))
              (synCplc (Class.cv (nb057AlphaDummy098 f)) (synC1c))
              (Class.cv (nb057AlphaDummy098 f)))))) :=
  (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0090) 0))
          (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0091 f) 0))
          (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0090) 1))
            (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0091 f) 1))
            (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0120) 0))
              (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0121 f) 0))
              (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0118) 0))
                (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0119 f) 0))
                (TAlphaVar.here _ _ _))))))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv
          (TAlphaVar.there
            (freshVar_injective (((Class.cv (nb057AlphaDummy089))).fv) (by decide))
            (freshVar_injective (((Class.cv (nb057AlphaDummy091 f))).fv) (by decide))
            (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp (TAlphaWff.neg
              (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                  (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                          (TAlphaClass.cv (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0094) 1))
                              (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0095 f) 1))
                              (TAlphaVar.there (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb057_support_mem_0094) 0)) (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb057_support_mem_0095 f) 0))
                                (TAlphaVar.there (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb057_support_mem_0092) 0)) (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb057_support_mem_0093 f) 0))
                                  (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.reflOfClosed
                                [((nb057AlphaDummy104), (nb057AlphaDummy107 f)),
                                  ((nb057AlphaDummy103), (nb057AlphaDummy106 f)),
                                  ((nb057AlphaDummy102), (nb057AlphaDummy105 f)),
                                  ((nb057AlphaDummy100), (nb057AlphaDummy101 f)),
                                  ((nb057AlphaDummy096), (nb057AlphaDummy098 f)),
                                  ((nb057AlphaDummy097), (nb057AlphaDummy099 f)),
                                  ((nb057AlphaDummy122), (nb057AlphaDummy123 f)),
                                  ((nb057AlphaDummy120), (nb057AlphaDummy121 f)),
                                  ((nb057AlphaDummy089), (nb057AlphaDummy091 f)),
                                  ((nb057AlphaDummy088), (nb057AlphaDummy090 f)),
                                  ((nb057AlphaDummy118), (nb057AlphaDummy119 f)),
                                  ((nb057AlphaDummy092), (nb057AlphaDummy093 f)),
                                  ((nb057AlphaDummy046), (nb057AlphaDummy049 f)),
                                  ((nb057AlphaDummy045), (nb057AlphaDummy048 f)),
                                  ((nb057AlphaDummy044), (nb057AlphaDummy047 f)),
                                  ((nb057AlphaDummy050), (nb057AlphaDummy051 f)),
                                  ((nb057AlphaDummy000), a), ((nb057AlphaDummy001), f),
                                  ((nb057AlphaDummy002), (nb057AlphaDummy003 f a))]
                                (synC1c) (by simp only [fv_syn_c1c])))
                            (TAlphaWff.neg (nb057SplitAlpha0040 f a))))))))
                (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there
                      (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0092) 0))
                      (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0093 f) 0))
                      (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
                    [((nb057AlphaDummy100), (nb057AlphaDummy101 f)),
                      ((nb057AlphaDummy096), (nb057AlphaDummy098 f)),
                      ((nb057AlphaDummy097), (nb057AlphaDummy099 f)),
                      ((nb057AlphaDummy122), (nb057AlphaDummy123 f)),
                      ((nb057AlphaDummy120), (nb057AlphaDummy121 f)),
                      ((nb057AlphaDummy089), (nb057AlphaDummy091 f)),
                      ((nb057AlphaDummy088), (nb057AlphaDummy090 f)),
                      ((nb057AlphaDummy118), (nb057AlphaDummy119 f)),
                      ((nb057AlphaDummy092), (nb057AlphaDummy093 f)),
                      ((nb057AlphaDummy046), (nb057AlphaDummy049 f)),
                      ((nb057AlphaDummy045), (nb057AlphaDummy048 f)),
                      ((nb057AlphaDummy044), (nb057AlphaDummy047 f)),
                      ((nb057AlphaDummy050), (nb057AlphaDummy051 f)),
                      ((nb057AlphaDummy000), a), ((nb057AlphaDummy001), f),
                      ((nb057AlphaDummy002), (nb057AlphaDummy003 f a))]
                    (synCnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                  (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0092) 0))
                    (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0093 f) 0))
                    (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv
                    (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0092) 0))
                      (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0093 f) 0))
                      (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
                    [((nb057AlphaDummy100), (nb057AlphaDummy101 f)),
                      ((nb057AlphaDummy096), (nb057AlphaDummy098 f)),
                      ((nb057AlphaDummy097), (nb057AlphaDummy099 f)),
                      ((nb057AlphaDummy122), (nb057AlphaDummy123 f)),
                      ((nb057AlphaDummy120), (nb057AlphaDummy121 f)),
                      ((nb057AlphaDummy089), (nb057AlphaDummy091 f)),
                      ((nb057AlphaDummy088), (nb057AlphaDummy090 f)),
                      ((nb057AlphaDummy118), (nb057AlphaDummy119 f)),
                      ((nb057AlphaDummy092), (nb057AlphaDummy093 f)),
                      ((nb057AlphaDummy046), (nb057AlphaDummy049 f)),
                      ((nb057AlphaDummy045), (nb057AlphaDummy048 f)),
                      ((nb057AlphaDummy044), (nb057AlphaDummy047 f)),
                      ((nb057AlphaDummy050), (nb057AlphaDummy051 f)),
                      ((nb057AlphaDummy000), a), ((nb057AlphaDummy001), f),
                      ((nb057AlphaDummy002), (nb057AlphaDummy003 f a))]
                    (synCnnc) (by simp only [fv_syn_cnnc]))))))))))

/-- Checked nominal proof certificate identified upstream as `nb057_split_alpha_0042`. -/
@[expose]
noncomputable def nb057SplitAlpha0042 (f : Var) (a : Var) :
    TAlphaWff
      [((nb057AlphaDummy118), (nb057AlphaDummy119 f)),
        ((nb057AlphaDummy092), (nb057AlphaDummy093 f)),
        ((nb057AlphaDummy046), (nb057AlphaDummy049 f)),
        ((nb057AlphaDummy045), (nb057AlphaDummy048 f)),
        ((nb057AlphaDummy044), (nb057AlphaDummy047 f)),
        ((nb057AlphaDummy050), (nb057AlphaDummy051 f)),
        ((nb057AlphaDummy000), a), ((nb057AlphaDummy001), f),
        ((nb057AlphaDummy002), (nb057AlphaDummy003 f a))]
      (Wff.imp (Wff.classMem (Class.cv (nb057AlphaDummy118))
          (Class.cab (nb057AlphaDummy088)
            (synWrex (nb057AlphaDummy089) (Class.cv (nb057AlphaDummy046))
              (Wff.classEq (Class.cv (nb057AlphaDummy088))
                (synCun (synCphi (Class.cv (nb057AlphaDummy089))) (synCsn (synC0c)))))))
        (Wff.neg (Wff.classMem (Class.cv (nb057AlphaDummy118))
            (Class.cab (nb057AlphaDummy088)
              (synWrex (nb057AlphaDummy089) (Class.cv (nb057AlphaDummy046))
                (Wff.classEq (Class.cv (nb057AlphaDummy088))
                  (synCun (synCphi (Class.cv (nb057AlphaDummy089)))
                    (synCsn (synC0c)))))))))
      (Wff.imp (Wff.classMem (Class.cv (nb057AlphaDummy119 f))
          (Class.cab (nb057AlphaDummy090 f)
            (synWrex (nb057AlphaDummy091 f) (Class.cv (nb057AlphaDummy049 f))
              (Wff.classEq (Class.cv (nb057AlphaDummy090 f))
                (synCun (synCphi (Class.cv (nb057AlphaDummy091 f)))
                  (synCsn (synC0c))))))) (Wff.neg
          (Wff.classMem (Class.cv (nb057AlphaDummy119 f))
            (Class.cab (nb057AlphaDummy090 f)
              (synWrex (nb057AlphaDummy091 f) (Class.cv (nb057AlphaDummy049 f))
                (Wff.classEq (Class.cv (nb057AlphaDummy090 f))
                  (synCun (synCphi (Class.cv (nb057AlphaDummy091 f)))
                    (synCsn (synC0c))))))))) :=
  (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.ex (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0112) 1))
                  (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0114 f) 1)) (TAlphaVar.there
                    (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0112) 0))
                    (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0114 f) 0))
                    (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0116) 0))
                      (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0117 f) 0))
                      (TAlphaVar.there
                        (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0113) 0))
                        (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0115 f) 0))
                        (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
                (TAlphaVar.there (freshVar_injective (((Class.cv (nb057AlphaDummy044))).fv ∪
                      ((Class.cv (nb057AlphaDummy046))).fv) (by decide)) (freshVar_injective
                    (((Class.cv (nb057AlphaDummy047 f))).fv ∪
                      ((Class.cv (nb057AlphaDummy049 f))).fv) (by decide))
                  (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                        (TAlphaWff.neg (TAlphaWff.conj
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cab (TAlphaWff.ex
                                  (TAlphaWff.neg (nb057SplitAlpha0041 f a)))))
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cab (TAlphaWff.ex
                                  (TAlphaWff.neg (nb057SplitAlpha0041 f a)))))))))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                      (TAlphaClass.reflOfClosed
                        [((nb057AlphaDummy120), (nb057AlphaDummy121 f)),
                          ((nb057AlphaDummy089), (nb057AlphaDummy091 f)),
                          ((nb057AlphaDummy088), (nb057AlphaDummy090 f)),
                          ((nb057AlphaDummy118), (nb057AlphaDummy119 f)),
                          ((nb057AlphaDummy092), (nb057AlphaDummy093 f)),
                          ((nb057AlphaDummy046), (nb057AlphaDummy049 f)),
                          ((nb057AlphaDummy045), (nb057AlphaDummy048 f)),
                          ((nb057AlphaDummy044), (nb057AlphaDummy047 f)),
                          ((nb057AlphaDummy050), (nb057AlphaDummy051 f)),
                          ((nb057AlphaDummy000), a), ((nb057AlphaDummy001), f),
                          ((nb057AlphaDummy002), (nb057AlphaDummy003 f a))]
                        (synCcompl (synCsn (synC0c)))
                        (by simp only [fv_syn_ccompl, fv_syn_csn, fv_syn_c0c])))))))))))
    (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
          (TAlphaWff.ex (TAlphaWff.conj
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                  (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0112) 1))
                    (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0114 f) 1))
                    (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0112) 0))
                      (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0114 f) 0))
                      (TAlphaVar.there
                        (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0116) 0))
                        (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0117 f) 0))
                        (TAlphaVar.there
                          (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0113) 0))
                          (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0115 f) 0))
                          (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
                  (TAlphaVar.there (freshVar_injective
                      (((Class.cv (nb057AlphaDummy044))).fv ∪
                        ((Class.cv (nb057AlphaDummy046))).fv) (by decide))
                    (freshVar_injective (((Class.cv (nb057AlphaDummy047 f))).fv ∪
                        ((Class.cv (nb057AlphaDummy049 f))).fv) (by decide))
                    (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cab (TAlphaWff.ex
                                    (TAlphaWff.neg (nb057SplitAlpha0041 f a)))))
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cab (TAlphaWff.ex
                                    (TAlphaWff.neg (nb057SplitAlpha0041 f a)))))))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.reflOfClosed
                          [((nb057AlphaDummy120), (nb057AlphaDummy121 f)),
                            ((nb057AlphaDummy089), (nb057AlphaDummy091 f)),
                            ((nb057AlphaDummy088), (nb057AlphaDummy090 f)),
                            ((nb057AlphaDummy118), (nb057AlphaDummy119 f)),
                            ((nb057AlphaDummy092), (nb057AlphaDummy093 f)),
                            ((nb057AlphaDummy046), (nb057AlphaDummy049 f)),
                            ((nb057AlphaDummy045), (nb057AlphaDummy048 f)),
                            ((nb057AlphaDummy044), (nb057AlphaDummy047 f)),
                            ((nb057AlphaDummy050), (nb057AlphaDummy051 f)),
                            ((nb057AlphaDummy000), a), ((nb057AlphaDummy001), f),
                            ((nb057AlphaDummy002), (nb057AlphaDummy003 f a))]
                          (synCcompl (synCsn (synC0c))) (by
                            simp only [fv_syn_ccompl, fv_syn_csn, fv_syn_c0c])))))))))))))

/-- Checked nominal proof certificate identified upstream as `nb057_split_alpha_0043`. -/
@[expose]
noncomputable def nb057SplitAlpha0043 (f : Var) (a : Var) :
    TAlphaWff
      [((nb057AlphaDummy146), (nb057AlphaDummy149 f)),
        ((nb057AlphaDummy145), (nb057AlphaDummy148 f)),
        ((nb057AlphaDummy144), (nb057AlphaDummy147 f)),
        ((nb057AlphaDummy142), (nb057AlphaDummy143 f)),
        ((nb057AlphaDummy138), (nb057AlphaDummy140 f)),
        ((nb057AlphaDummy139), (nb057AlphaDummy141 f)),
        ((nb057AlphaDummy131), (nb057AlphaDummy133 f)),
        ((nb057AlphaDummy130), (nb057AlphaDummy132 f)),
        ((nb057AlphaDummy136), (nb057AlphaDummy137 f)),
        ((nb057AlphaDummy134), (nb057AlphaDummy135 f)),
        ((nb057AlphaDummy125), (nb057AlphaDummy127 f)),
        ((nb057AlphaDummy124), (nb057AlphaDummy126 f)),
        ((nb057AlphaDummy128), (nb057AlphaDummy129 f)),
        ((nb057AlphaDummy046), (nb057AlphaDummy049 f)),
        ((nb057AlphaDummy045), (nb057AlphaDummy048 f)),
        ((nb057AlphaDummy044), (nb057AlphaDummy047 f)),
        ((nb057AlphaDummy050), (nb057AlphaDummy051 f)),
        ((nb057AlphaDummy000), a), ((nb057AlphaDummy001), f),
        ((nb057AlphaDummy002), (nb057AlphaDummy003 f a))]
      (Wff.imp (Wff.classEq
          (synCin (Class.cv (nb057AlphaDummy145)) (Class.cv (nb057AlphaDummy146)))
          (synC0)) (Wff.neg (Wff.classEq (Class.cv (nb057AlphaDummy144))
            (synCun (Class.cv (nb057AlphaDummy145)) (Class.cv (nb057AlphaDummy146))))))
      (Wff.imp (Wff.classEq (synCin (Class.cv (nb057AlphaDummy148 f))
            (Class.cv (nb057AlphaDummy149 f))) (synC0)) (Wff.neg
          (Wff.classEq (Class.cv (nb057AlphaDummy147 f))
            (synCun (Class.cv (nb057AlphaDummy148 f))
              (Class.cv (nb057AlphaDummy149 f)))))) :=
  (TAlphaWff.imp (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.neg (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0140) 0))
                          (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0141 f) 0))
                          (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0138) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0139 f) 0))
                            (TAlphaVar.there (freshVar_injective
                                (((Class.cv (nb057AlphaDummy138))).fv ∪ ((synC1c)).fv)
                                (by decide)) (freshVar_injective
                                (((Class.cv (nb057AlphaDummy140 f))).fv ∪ ((synC1c)).fv)
                                (by decide)) (TAlphaVar.here _ _ _))))))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0144) 0))
                          (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0145 f) 0))
                          (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0142) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0143 f) 0))
                            (TAlphaVar.here _ _ _)))))))))
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.neg (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0140) 0))
                          (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0141 f) 0))
                          (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0138) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0139 f) 0))
                            (TAlphaVar.there (freshVar_injective
                                (((Class.cv (nb057AlphaDummy138))).fv ∪ ((synC1c)).fv)
                                (by decide)) (freshVar_injective
                                (((Class.cv (nb057AlphaDummy140 f))).fv ∪ ((synC1c)).fv)
                                (by decide)) (TAlphaVar.here _ _ _))))))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0144) 0))
                          (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0145 f) 0))
                          (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0142) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0143 f) 0))
                            (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.reflOfClosed
        [((nb057AlphaDummy146), (nb057AlphaDummy149 f)),
          ((nb057AlphaDummy145), (nb057AlphaDummy148 f)),
          ((nb057AlphaDummy144), (nb057AlphaDummy147 f)),
          ((nb057AlphaDummy142), (nb057AlphaDummy143 f)),
          ((nb057AlphaDummy138), (nb057AlphaDummy140 f)),
          ((nb057AlphaDummy139), (nb057AlphaDummy141 f)),
          ((nb057AlphaDummy131), (nb057AlphaDummy133 f)),
          ((nb057AlphaDummy130), (nb057AlphaDummy132 f)),
          ((nb057AlphaDummy136), (nb057AlphaDummy137 f)),
          ((nb057AlphaDummy134), (nb057AlphaDummy135 f)),
          ((nb057AlphaDummy125), (nb057AlphaDummy127 f)),
          ((nb057AlphaDummy124), (nb057AlphaDummy126 f)),
          ((nb057AlphaDummy128), (nb057AlphaDummy129 f)),
          ((nb057AlphaDummy046), (nb057AlphaDummy049 f)),
          ((nb057AlphaDummy045), (nb057AlphaDummy048 f)),
          ((nb057AlphaDummy044), (nb057AlphaDummy047 f)),
          ((nb057AlphaDummy050), (nb057AlphaDummy051 f)),
          ((nb057AlphaDummy000), a), ((nb057AlphaDummy001), f),
          ((nb057AlphaDummy002), (nb057AlphaDummy003 f a))]
        (synC0) (by simp only [fv_syn_c0]))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv
          (TAlphaVar.there
            (freshVar_injective (((Class.cv (nb057AlphaDummy138))).fv ∪ ((synC1c)).fv)
              (by decide)) (freshVar_injective
              (((Class.cv (nb057AlphaDummy140 f))).fv ∪ ((synC1c)).fv) (by decide))
            (TAlphaVar.there (freshVar_injective
                (((Class.cv (nb057AlphaDummy138))).fv ∪ ((synC1c)).fv) (by decide))
              (freshVar_injective
                (((Class.cv (nb057AlphaDummy140 f))).fv ∪ ((synC1c)).fv) (by decide))
              (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                  (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0148) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0149 f) 0))
                            (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0146) 0))
                              (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0147 f) 0))
                              (TAlphaVar.there (freshVar_injective
                                  (((Class.cv (nb057AlphaDummy138))).fv ∪ ((synC1c)).fv)
                                  (by decide)) (freshVar_injective
                                  (((Class.cv (nb057AlphaDummy140 f))).fv ∪ ((synC1c)).fv)
                                  (by decide)) (TAlphaVar.here _ _ _))))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0148) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0149 f) 0))
                            (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0146) 0))
                              (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0147 f) 0))
                              (TAlphaVar.there (freshVar_injective
                                  (((Class.cv (nb057AlphaDummy138))).fv ∪ ((synC1c)).fv)
                                  (by decide)) (freshVar_injective
                                  (((Class.cv (nb057AlphaDummy140 f))).fv ∪ ((synC1c)).fv)
                                  (by decide)) (TAlphaVar.here _ _ _))))))))))
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                  (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0152) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0153 f) 0))
                            (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0150) 0))
                              (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0151 f) 0))
                              (TAlphaVar.here _ _ _)))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0152) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0153 f) 0))
                            (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0150) 0))
                              (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0151 f) 0))
                              (TAlphaVar.here _ _ _)))))))))))))))


end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired

end

/-! Certificates from `NAR4C057C001Part020`. -/


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

/-- Checked nominal proof certificate identified upstream as `nb057_split_alpha_0044`. -/
@[expose]
noncomputable def nb057SplitAlpha0044 (f : Var) (a : Var) :
    TAlphaWff
      [((nb057AlphaDummy138), (nb057AlphaDummy140 f)),
        ((nb057AlphaDummy139), (nb057AlphaDummy141 f)),
        ((nb057AlphaDummy131), (nb057AlphaDummy133 f)),
        ((nb057AlphaDummy130), (nb057AlphaDummy132 f)),
        ((nb057AlphaDummy136), (nb057AlphaDummy137 f)),
        ((nb057AlphaDummy134), (nb057AlphaDummy135 f)),
        ((nb057AlphaDummy125), (nb057AlphaDummy127 f)),
        ((nb057AlphaDummy124), (nb057AlphaDummy126 f)),
        ((nb057AlphaDummy128), (nb057AlphaDummy129 f)),
        ((nb057AlphaDummy046), (nb057AlphaDummy049 f)),
        ((nb057AlphaDummy045), (nb057AlphaDummy048 f)),
        ((nb057AlphaDummy044), (nb057AlphaDummy047 f)),
        ((nb057AlphaDummy050), (nb057AlphaDummy051 f)),
        ((nb057AlphaDummy000), a), ((nb057AlphaDummy001), f),
        ((nb057AlphaDummy002), (nb057AlphaDummy003 f a))]
      (Wff.imp (Wff.classMem (Class.cv (nb057AlphaDummy138))
          (Class.cv (nb057AlphaDummy131))) (Wff.neg
          (Wff.classEq (Class.cv (nb057AlphaDummy139))
            (synCif (Wff.classMem (Class.cv (nb057AlphaDummy138)) (synCnnc))
              (synCplc (Class.cv (nb057AlphaDummy138)) (synC1c))
              (Class.cv (nb057AlphaDummy138))))))
      (Wff.imp (Wff.classMem (Class.cv (nb057AlphaDummy140 f))
          (Class.cv (nb057AlphaDummy133 f))) (Wff.neg
          (Wff.classEq (Class.cv (nb057AlphaDummy141 f))
            (synCif (Wff.classMem (Class.cv (nb057AlphaDummy140 f)) (synCnnc))
              (synCplc (Class.cv (nb057AlphaDummy140 f)) (synC1c))
              (Class.cv (nb057AlphaDummy140 f)))))) :=
  (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0132) 0))
          (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0133 f) 0))
          (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0132) 1))
            (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0133 f) 1))
            (TAlphaVar.here _ _ _))))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv
          (TAlphaVar.there
            (freshVar_injective (((Class.cv (nb057AlphaDummy131))).fv) (by decide))
            (freshVar_injective (((Class.cv (nb057AlphaDummy133 f))).fv) (by decide))
            (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp (TAlphaWff.neg
              (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                  (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                          (TAlphaClass.cv (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0136) 1))
                              (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0137 f) 1))
                              (TAlphaVar.there (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb057_support_mem_0136) 0)) (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb057_support_mem_0137 f) 0))
                                (TAlphaVar.there (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb057_support_mem_0134) 0)) (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb057_support_mem_0135 f) 0))
                                  (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.reflOfClosed
                                [((nb057AlphaDummy146), (nb057AlphaDummy149 f)),
                                  ((nb057AlphaDummy145), (nb057AlphaDummy148 f)),
                                  ((nb057AlphaDummy144), (nb057AlphaDummy147 f)),
                                  ((nb057AlphaDummy142), (nb057AlphaDummy143 f)),
                                  ((nb057AlphaDummy138), (nb057AlphaDummy140 f)),
                                  ((nb057AlphaDummy139), (nb057AlphaDummy141 f)),
                                  ((nb057AlphaDummy131), (nb057AlphaDummy133 f)),
                                  ((nb057AlphaDummy130), (nb057AlphaDummy132 f)),
                                  ((nb057AlphaDummy136), (nb057AlphaDummy137 f)),
                                  ((nb057AlphaDummy134), (nb057AlphaDummy135 f)),
                                  ((nb057AlphaDummy125), (nb057AlphaDummy127 f)),
                                  ((nb057AlphaDummy124), (nb057AlphaDummy126 f)),
                                  ((nb057AlphaDummy128), (nb057AlphaDummy129 f)),
                                  ((nb057AlphaDummy046), (nb057AlphaDummy049 f)),
                                  ((nb057AlphaDummy045), (nb057AlphaDummy048 f)),
                                  ((nb057AlphaDummy044), (nb057AlphaDummy047 f)),
                                  ((nb057AlphaDummy050), (nb057AlphaDummy051 f)),
                                  ((nb057AlphaDummy000), a), ((nb057AlphaDummy001), f),
                                  ((nb057AlphaDummy002), (nb057AlphaDummy003 f a))]
                                (synC1c) (by simp only [fv_syn_c1c])))
                            (TAlphaWff.neg (nb057SplitAlpha0043 f a))))))))
                (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there
                      (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0134) 0))
                      (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0135 f) 0))
                      (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
                    [((nb057AlphaDummy142), (nb057AlphaDummy143 f)),
                      ((nb057AlphaDummy138), (nb057AlphaDummy140 f)),
                      ((nb057AlphaDummy139), (nb057AlphaDummy141 f)),
                      ((nb057AlphaDummy131), (nb057AlphaDummy133 f)),
                      ((nb057AlphaDummy130), (nb057AlphaDummy132 f)),
                      ((nb057AlphaDummy136), (nb057AlphaDummy137 f)),
                      ((nb057AlphaDummy134), (nb057AlphaDummy135 f)),
                      ((nb057AlphaDummy125), (nb057AlphaDummy127 f)),
                      ((nb057AlphaDummy124), (nb057AlphaDummy126 f)),
                      ((nb057AlphaDummy128), (nb057AlphaDummy129 f)),
                      ((nb057AlphaDummy046), (nb057AlphaDummy049 f)),
                      ((nb057AlphaDummy045), (nb057AlphaDummy048 f)),
                      ((nb057AlphaDummy044), (nb057AlphaDummy047 f)),
                      ((nb057AlphaDummy050), (nb057AlphaDummy051 f)),
                      ((nb057AlphaDummy000), a), ((nb057AlphaDummy001), f),
                      ((nb057AlphaDummy002), (nb057AlphaDummy003 f a))]
                    (synCnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                  (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0134) 0))
                    (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0135 f) 0))
                    (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv
                    (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0134) 0))
                      (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0135 f) 0))
                      (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
                    [((nb057AlphaDummy142), (nb057AlphaDummy143 f)),
                      ((nb057AlphaDummy138), (nb057AlphaDummy140 f)),
                      ((nb057AlphaDummy139), (nb057AlphaDummy141 f)),
                      ((nb057AlphaDummy131), (nb057AlphaDummy133 f)),
                      ((nb057AlphaDummy130), (nb057AlphaDummy132 f)),
                      ((nb057AlphaDummy136), (nb057AlphaDummy137 f)),
                      ((nb057AlphaDummy134), (nb057AlphaDummy135 f)),
                      ((nb057AlphaDummy125), (nb057AlphaDummy127 f)),
                      ((nb057AlphaDummy124), (nb057AlphaDummy126 f)),
                      ((nb057AlphaDummy128), (nb057AlphaDummy129 f)),
                      ((nb057AlphaDummy046), (nb057AlphaDummy049 f)),
                      ((nb057AlphaDummy045), (nb057AlphaDummy048 f)),
                      ((nb057AlphaDummy044), (nb057AlphaDummy047 f)),
                      ((nb057AlphaDummy050), (nb057AlphaDummy051 f)),
                      ((nb057AlphaDummy000), a), ((nb057AlphaDummy001), f),
                      ((nb057AlphaDummy002), (nb057AlphaDummy003 f a))]
                    (synCnnc) (by simp only [fv_syn_cnnc]))))))))))

/-- Checked nominal proof certificate identified upstream as `nb057_split_alpha_0045`. -/
@[expose]
noncomputable def nb057SplitAlpha0045 (f : Var) (a : Var) :
    TAlphaWff
      [((nb057AlphaDummy146), (nb057AlphaDummy149 f)),
        ((nb057AlphaDummy145), (nb057AlphaDummy148 f)),
        ((nb057AlphaDummy144), (nb057AlphaDummy147 f)),
        ((nb057AlphaDummy142), (nb057AlphaDummy143 f)),
        ((nb057AlphaDummy138), (nb057AlphaDummy140 f)),
        ((nb057AlphaDummy139), (nb057AlphaDummy141 f)),
        ((nb057AlphaDummy164), (nb057AlphaDummy165 f)),
        ((nb057AlphaDummy162), (nb057AlphaDummy163 f)),
        ((nb057AlphaDummy131), (nb057AlphaDummy133 f)),
        ((nb057AlphaDummy130), (nb057AlphaDummy132 f)),
        ((nb057AlphaDummy160), (nb057AlphaDummy161 f)),
        ((nb057AlphaDummy134), (nb057AlphaDummy135 f)),
        ((nb057AlphaDummy125), (nb057AlphaDummy127 f)),
        ((nb057AlphaDummy124), (nb057AlphaDummy126 f)),
        ((nb057AlphaDummy128), (nb057AlphaDummy129 f)),
        ((nb057AlphaDummy046), (nb057AlphaDummy049 f)),
        ((nb057AlphaDummy045), (nb057AlphaDummy048 f)),
        ((nb057AlphaDummy044), (nb057AlphaDummy047 f)),
        ((nb057AlphaDummy050), (nb057AlphaDummy051 f)),
        ((nb057AlphaDummy000), a), ((nb057AlphaDummy001), f),
        ((nb057AlphaDummy002), (nb057AlphaDummy003 f a))]
      (Wff.imp (Wff.classEq
          (synCin (Class.cv (nb057AlphaDummy145)) (Class.cv (nb057AlphaDummy146)))
          (synC0)) (Wff.neg (Wff.classEq (Class.cv (nb057AlphaDummy144))
            (synCun (Class.cv (nb057AlphaDummy145)) (Class.cv (nb057AlphaDummy146))))))
      (Wff.imp (Wff.classEq (synCin (Class.cv (nb057AlphaDummy148 f))
            (Class.cv (nb057AlphaDummy149 f))) (synC0)) (Wff.neg
          (Wff.classEq (Class.cv (nb057AlphaDummy147 f))
            (synCun (Class.cv (nb057AlphaDummy148 f))
              (Class.cv (nb057AlphaDummy149 f)))))) :=
  (TAlphaWff.imp (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.neg (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0140) 0))
                          (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0141 f) 0))
                          (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0138) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0139 f) 0))
                            (TAlphaVar.there (freshVar_injective
                                (((Class.cv (nb057AlphaDummy138))).fv ∪ ((synC1c)).fv)
                                (by decide)) (freshVar_injective
                                (((Class.cv (nb057AlphaDummy140 f))).fv ∪ ((synC1c)).fv)
                                (by decide)) (TAlphaVar.here _ _ _))))))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0144) 0))
                          (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0145 f) 0))
                          (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0142) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0143 f) 0))
                            (TAlphaVar.here _ _ _)))))))))
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.neg (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0140) 0))
                          (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0141 f) 0))
                          (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0138) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0139 f) 0))
                            (TAlphaVar.there (freshVar_injective
                                (((Class.cv (nb057AlphaDummy138))).fv ∪ ((synC1c)).fv)
                                (by decide)) (freshVar_injective
                                (((Class.cv (nb057AlphaDummy140 f))).fv ∪ ((synC1c)).fv)
                                (by decide)) (TAlphaVar.here _ _ _))))))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0144) 0))
                          (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0145 f) 0))
                          (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0142) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0143 f) 0))
                            (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.reflOfClosed
        [((nb057AlphaDummy146), (nb057AlphaDummy149 f)),
          ((nb057AlphaDummy145), (nb057AlphaDummy148 f)),
          ((nb057AlphaDummy144), (nb057AlphaDummy147 f)),
          ((nb057AlphaDummy142), (nb057AlphaDummy143 f)),
          ((nb057AlphaDummy138), (nb057AlphaDummy140 f)),
          ((nb057AlphaDummy139), (nb057AlphaDummy141 f)),
          ((nb057AlphaDummy164), (nb057AlphaDummy165 f)),
          ((nb057AlphaDummy162), (nb057AlphaDummy163 f)),
          ((nb057AlphaDummy131), (nb057AlphaDummy133 f)),
          ((nb057AlphaDummy130), (nb057AlphaDummy132 f)),
          ((nb057AlphaDummy160), (nb057AlphaDummy161 f)),
          ((nb057AlphaDummy134), (nb057AlphaDummy135 f)),
          ((nb057AlphaDummy125), (nb057AlphaDummy127 f)),
          ((nb057AlphaDummy124), (nb057AlphaDummy126 f)),
          ((nb057AlphaDummy128), (nb057AlphaDummy129 f)),
          ((nb057AlphaDummy046), (nb057AlphaDummy049 f)),
          ((nb057AlphaDummy045), (nb057AlphaDummy048 f)),
          ((nb057AlphaDummy044), (nb057AlphaDummy047 f)),
          ((nb057AlphaDummy050), (nb057AlphaDummy051 f)),
          ((nb057AlphaDummy000), a), ((nb057AlphaDummy001), f),
          ((nb057AlphaDummy002), (nb057AlphaDummy003 f a))]
        (synC0) (by simp only [fv_syn_c0]))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv
          (TAlphaVar.there
            (freshVar_injective (((Class.cv (nb057AlphaDummy138))).fv ∪ ((synC1c)).fv)
              (by decide)) (freshVar_injective
              (((Class.cv (nb057AlphaDummy140 f))).fv ∪ ((synC1c)).fv) (by decide))
            (TAlphaVar.there (freshVar_injective
                (((Class.cv (nb057AlphaDummy138))).fv ∪ ((synC1c)).fv) (by decide))
              (freshVar_injective
                (((Class.cv (nb057AlphaDummy140 f))).fv ∪ ((synC1c)).fv) (by decide))
              (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                  (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0148) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0149 f) 0))
                            (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0146) 0))
                              (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0147 f) 0))
                              (TAlphaVar.there (freshVar_injective
                                  (((Class.cv (nb057AlphaDummy138))).fv ∪ ((synC1c)).fv)
                                  (by decide)) (freshVar_injective
                                  (((Class.cv (nb057AlphaDummy140 f))).fv ∪ ((synC1c)).fv)
                                  (by decide)) (TAlphaVar.here _ _ _))))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0148) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0149 f) 0))
                            (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0146) 0))
                              (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0147 f) 0))
                              (TAlphaVar.there (freshVar_injective
                                  (((Class.cv (nb057AlphaDummy138))).fv ∪ ((synC1c)).fv)
                                  (by decide)) (freshVar_injective
                                  (((Class.cv (nb057AlphaDummy140 f))).fv ∪ ((synC1c)).fv)
                                  (by decide)) (TAlphaVar.here _ _ _))))))))))
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                  (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0152) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0153 f) 0))
                            (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0150) 0))
                              (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0151 f) 0))
                              (TAlphaVar.here _ _ _)))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0152) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0153 f) 0))
                            (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0150) 0))
                              (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0151 f) 0))
                              (TAlphaVar.here _ _ _)))))))))))))))

/-- Checked nominal proof certificate identified upstream as `nb057_split_alpha_0046`. -/
@[expose]
noncomputable def nb057SplitAlpha0046 (f : Var) (a : Var) :
    TAlphaWff
      [((nb057AlphaDummy138), (nb057AlphaDummy140 f)),
        ((nb057AlphaDummy139), (nb057AlphaDummy141 f)),
        ((nb057AlphaDummy164), (nb057AlphaDummy165 f)),
        ((nb057AlphaDummy162), (nb057AlphaDummy163 f)),
        ((nb057AlphaDummy131), (nb057AlphaDummy133 f)),
        ((nb057AlphaDummy130), (nb057AlphaDummy132 f)),
        ((nb057AlphaDummy160), (nb057AlphaDummy161 f)),
        ((nb057AlphaDummy134), (nb057AlphaDummy135 f)),
        ((nb057AlphaDummy125), (nb057AlphaDummy127 f)),
        ((nb057AlphaDummy124), (nb057AlphaDummy126 f)),
        ((nb057AlphaDummy128), (nb057AlphaDummy129 f)),
        ((nb057AlphaDummy046), (nb057AlphaDummy049 f)),
        ((nb057AlphaDummy045), (nb057AlphaDummy048 f)),
        ((nb057AlphaDummy044), (nb057AlphaDummy047 f)),
        ((nb057AlphaDummy050), (nb057AlphaDummy051 f)),
        ((nb057AlphaDummy000), a), ((nb057AlphaDummy001), f),
        ((nb057AlphaDummy002), (nb057AlphaDummy003 f a))]
      (Wff.imp (Wff.classMem (Class.cv (nb057AlphaDummy138))
          (Class.cv (nb057AlphaDummy131))) (Wff.neg
          (Wff.classEq (Class.cv (nb057AlphaDummy139))
            (synCif (Wff.classMem (Class.cv (nb057AlphaDummy138)) (synCnnc))
              (synCplc (Class.cv (nb057AlphaDummy138)) (synC1c))
              (Class.cv (nb057AlphaDummy138))))))
      (Wff.imp (Wff.classMem (Class.cv (nb057AlphaDummy140 f))
          (Class.cv (nb057AlphaDummy133 f))) (Wff.neg
          (Wff.classEq (Class.cv (nb057AlphaDummy141 f))
            (synCif (Wff.classMem (Class.cv (nb057AlphaDummy140 f)) (synCnnc))
              (synCplc (Class.cv (nb057AlphaDummy140 f)) (synC1c))
              (Class.cv (nb057AlphaDummy140 f)))))) :=
  (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0132) 0))
          (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0133 f) 0))
          (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0132) 1))
            (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0133 f) 1))
            (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0162) 0))
              (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0163 f) 0))
              (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0160) 0))
                (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0161 f) 0))
                (TAlphaVar.here _ _ _))))))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv
          (TAlphaVar.there
            (freshVar_injective (((Class.cv (nb057AlphaDummy131))).fv) (by decide))
            (freshVar_injective (((Class.cv (nb057AlphaDummy133 f))).fv) (by decide))
            (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp (TAlphaWff.neg
              (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                  (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                          (TAlphaClass.cv (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0136) 1))
                              (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0137 f) 1))
                              (TAlphaVar.there (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb057_support_mem_0136) 0)) (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb057_support_mem_0137 f) 0))
                                (TAlphaVar.there (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb057_support_mem_0134) 0)) (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb057_support_mem_0135 f) 0))
                                  (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.reflOfClosed
                                [((nb057AlphaDummy146), (nb057AlphaDummy149 f)),
                                  ((nb057AlphaDummy145), (nb057AlphaDummy148 f)),
                                  ((nb057AlphaDummy144), (nb057AlphaDummy147 f)),
                                  ((nb057AlphaDummy142), (nb057AlphaDummy143 f)),
                                  ((nb057AlphaDummy138), (nb057AlphaDummy140 f)),
                                  ((nb057AlphaDummy139), (nb057AlphaDummy141 f)),
                                  ((nb057AlphaDummy164), (nb057AlphaDummy165 f)),
                                  ((nb057AlphaDummy162), (nb057AlphaDummy163 f)),
                                  ((nb057AlphaDummy131), (nb057AlphaDummy133 f)),
                                  ((nb057AlphaDummy130), (nb057AlphaDummy132 f)),
                                  ((nb057AlphaDummy160), (nb057AlphaDummy161 f)),
                                  ((nb057AlphaDummy134), (nb057AlphaDummy135 f)),
                                  ((nb057AlphaDummy125), (nb057AlphaDummy127 f)),
                                  ((nb057AlphaDummy124), (nb057AlphaDummy126 f)),
                                  ((nb057AlphaDummy128), (nb057AlphaDummy129 f)),
                                  ((nb057AlphaDummy046), (nb057AlphaDummy049 f)),
                                  ((nb057AlphaDummy045), (nb057AlphaDummy048 f)),
                                  ((nb057AlphaDummy044), (nb057AlphaDummy047 f)),
                                  ((nb057AlphaDummy050), (nb057AlphaDummy051 f)),
                                  ((nb057AlphaDummy000), a), ((nb057AlphaDummy001), f),
                                  ((nb057AlphaDummy002), (nb057AlphaDummy003 f a))]
                                (synC1c) (by simp only [fv_syn_c1c])))
                            (TAlphaWff.neg (nb057SplitAlpha0045 f a))))))))
                (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there
                      (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0134) 0))
                      (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0135 f) 0))
                      (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
                    [((nb057AlphaDummy142), (nb057AlphaDummy143 f)),
                      ((nb057AlphaDummy138), (nb057AlphaDummy140 f)),
                      ((nb057AlphaDummy139), (nb057AlphaDummy141 f)),
                      ((nb057AlphaDummy164), (nb057AlphaDummy165 f)),
                      ((nb057AlphaDummy162), (nb057AlphaDummy163 f)),
                      ((nb057AlphaDummy131), (nb057AlphaDummy133 f)),
                      ((nb057AlphaDummy130), (nb057AlphaDummy132 f)),
                      ((nb057AlphaDummy160), (nb057AlphaDummy161 f)),
                      ((nb057AlphaDummy134), (nb057AlphaDummy135 f)),
                      ((nb057AlphaDummy125), (nb057AlphaDummy127 f)),
                      ((nb057AlphaDummy124), (nb057AlphaDummy126 f)),
                      ((nb057AlphaDummy128), (nb057AlphaDummy129 f)),
                      ((nb057AlphaDummy046), (nb057AlphaDummy049 f)),
                      ((nb057AlphaDummy045), (nb057AlphaDummy048 f)),
                      ((nb057AlphaDummy044), (nb057AlphaDummy047 f)),
                      ((nb057AlphaDummy050), (nb057AlphaDummy051 f)),
                      ((nb057AlphaDummy000), a), ((nb057AlphaDummy001), f),
                      ((nb057AlphaDummy002), (nb057AlphaDummy003 f a))]
                    (synCnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                  (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0134) 0))
                    (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0135 f) 0))
                    (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv
                    (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0134) 0))
                      (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0135 f) 0))
                      (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
                    [((nb057AlphaDummy142), (nb057AlphaDummy143 f)),
                      ((nb057AlphaDummy138), (nb057AlphaDummy140 f)),
                      ((nb057AlphaDummy139), (nb057AlphaDummy141 f)),
                      ((nb057AlphaDummy164), (nb057AlphaDummy165 f)),
                      ((nb057AlphaDummy162), (nb057AlphaDummy163 f)),
                      ((nb057AlphaDummy131), (nb057AlphaDummy133 f)),
                      ((nb057AlphaDummy130), (nb057AlphaDummy132 f)),
                      ((nb057AlphaDummy160), (nb057AlphaDummy161 f)),
                      ((nb057AlphaDummy134), (nb057AlphaDummy135 f)),
                      ((nb057AlphaDummy125), (nb057AlphaDummy127 f)),
                      ((nb057AlphaDummy124), (nb057AlphaDummy126 f)),
                      ((nb057AlphaDummy128), (nb057AlphaDummy129 f)),
                      ((nb057AlphaDummy046), (nb057AlphaDummy049 f)),
                      ((nb057AlphaDummy045), (nb057AlphaDummy048 f)),
                      ((nb057AlphaDummy044), (nb057AlphaDummy047 f)),
                      ((nb057AlphaDummy050), (nb057AlphaDummy051 f)),
                      ((nb057AlphaDummy000), a), ((nb057AlphaDummy001), f),
                      ((nb057AlphaDummy002), (nb057AlphaDummy003 f a))]
                    (synCnnc) (by simp only [fv_syn_cnnc]))))))))))

/-- Checked nominal proof certificate identified upstream as `nb057_split_alpha_0047`. -/
@[expose]
noncomputable def nb057SplitAlpha0047 (f : Var) (a : Var) :
    TAlphaWff
      [((nb057AlphaDummy160), (nb057AlphaDummy161 f)),
        ((nb057AlphaDummy134), (nb057AlphaDummy135 f)),
        ((nb057AlphaDummy125), (nb057AlphaDummy127 f)),
        ((nb057AlphaDummy124), (nb057AlphaDummy126 f)),
        ((nb057AlphaDummy128), (nb057AlphaDummy129 f)),
        ((nb057AlphaDummy046), (nb057AlphaDummy049 f)),
        ((nb057AlphaDummy045), (nb057AlphaDummy048 f)),
        ((nb057AlphaDummy044), (nb057AlphaDummy047 f)),
        ((nb057AlphaDummy050), (nb057AlphaDummy051 f)),
        ((nb057AlphaDummy000), a), ((nb057AlphaDummy001), f),
        ((nb057AlphaDummy002), (nb057AlphaDummy003 f a))]
      (Wff.imp (Wff.classMem (Class.cv (nb057AlphaDummy160))
          (Class.cab (nb057AlphaDummy130)
            (synWrex (nb057AlphaDummy131) (Class.cv (nb057AlphaDummy125))
              (Wff.classEq (Class.cv (nb057AlphaDummy130))
                (synCun (synCphi (Class.cv (nb057AlphaDummy131))) (synCsn (synC0c)))))))
        (Wff.neg (Wff.classMem (Class.cv (nb057AlphaDummy160))
            (Class.cab (nb057AlphaDummy130)
              (synWrex (nb057AlphaDummy131) (Class.cv (nb057AlphaDummy125))
                (Wff.classEq (Class.cv (nb057AlphaDummy130))
                  (synCun (synCphi (Class.cv (nb057AlphaDummy131)))
                    (synCsn (synC0c)))))))))
      (Wff.imp (Wff.classMem (Class.cv (nb057AlphaDummy161 f))
          (Class.cab (nb057AlphaDummy132 f)
            (synWrex (nb057AlphaDummy133 f) (Class.cv (nb057AlphaDummy127 f))
              (Wff.classEq (Class.cv (nb057AlphaDummy132 f))
                (synCun (synCphi (Class.cv (nb057AlphaDummy133 f)))
                  (synCsn (synC0c))))))) (Wff.neg
          (Wff.classMem (Class.cv (nb057AlphaDummy161 f))
            (Class.cab (nb057AlphaDummy132 f)
              (synWrex (nb057AlphaDummy133 f) (Class.cv (nb057AlphaDummy127 f))
                (Wff.classEq (Class.cv (nb057AlphaDummy132 f))
                  (synCun (synCphi (Class.cv (nb057AlphaDummy133 f)))
                    (synCsn (synC0c))))))))) :=
  (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.ex (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0154) 1))
                  (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0156 f) 1)) (TAlphaVar.there
                    (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0154) 0))
                    (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0156 f) 0))
                    (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0158) 0))
                      (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0159 f) 0))
                      (TAlphaVar.there
                        (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0155) 0))
                        (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0157 f) 0))
                        (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
                (TAlphaVar.there (freshVar_injective (((Class.cv (nb057AlphaDummy124))).fv ∪
                      ((Class.cv (nb057AlphaDummy125))).fv) (by decide)) (freshVar_injective
                    (((Class.cv (nb057AlphaDummy126 f))).fv ∪
                      ((Class.cv (nb057AlphaDummy127 f))).fv) (by decide))
                  (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                        (TAlphaWff.neg (TAlphaWff.conj
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cab (TAlphaWff.ex
                                  (TAlphaWff.neg (nb057SplitAlpha0046 f a)))))
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cab (TAlphaWff.ex
                                  (TAlphaWff.neg (nb057SplitAlpha0046 f a)))))))))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                      (TAlphaClass.reflOfClosed
                        [((nb057AlphaDummy162), (nb057AlphaDummy163 f)),
                          ((nb057AlphaDummy131), (nb057AlphaDummy133 f)),
                          ((nb057AlphaDummy130), (nb057AlphaDummy132 f)),
                          ((nb057AlphaDummy160), (nb057AlphaDummy161 f)),
                          ((nb057AlphaDummy134), (nb057AlphaDummy135 f)),
                          ((nb057AlphaDummy125), (nb057AlphaDummy127 f)),
                          ((nb057AlphaDummy124), (nb057AlphaDummy126 f)),
                          ((nb057AlphaDummy128), (nb057AlphaDummy129 f)),
                          ((nb057AlphaDummy046), (nb057AlphaDummy049 f)),
                          ((nb057AlphaDummy045), (nb057AlphaDummy048 f)),
                          ((nb057AlphaDummy044), (nb057AlphaDummy047 f)),
                          ((nb057AlphaDummy050), (nb057AlphaDummy051 f)),
                          ((nb057AlphaDummy000), a), ((nb057AlphaDummy001), f),
                          ((nb057AlphaDummy002), (nb057AlphaDummy003 f a))]
                        (synCcompl (synCsn (synC0c)))
                        (by simp only [fv_syn_ccompl, fv_syn_csn, fv_syn_c0c])))))))))))
    (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
          (TAlphaWff.ex (TAlphaWff.conj
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                  (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0154) 1))
                    (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0156 f) 1))
                    (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0154) 0))
                      (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0156 f) 0))
                      (TAlphaVar.there
                        (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0158) 0))
                        (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0159 f) 0))
                        (TAlphaVar.there
                          (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0155) 0))
                          (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0157 f) 0))
                          (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
                  (TAlphaVar.there (freshVar_injective
                      (((Class.cv (nb057AlphaDummy124))).fv ∪
                        ((Class.cv (nb057AlphaDummy125))).fv) (by decide))
                    (freshVar_injective (((Class.cv (nb057AlphaDummy126 f))).fv ∪
                        ((Class.cv (nb057AlphaDummy127 f))).fv) (by decide))
                    (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cab (TAlphaWff.ex
                                    (TAlphaWff.neg (nb057SplitAlpha0046 f a)))))
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cab (TAlphaWff.ex
                                    (TAlphaWff.neg (nb057SplitAlpha0046 f a)))))))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.reflOfClosed
                          [((nb057AlphaDummy162), (nb057AlphaDummy163 f)),
                            ((nb057AlphaDummy131), (nb057AlphaDummy133 f)),
                            ((nb057AlphaDummy130), (nb057AlphaDummy132 f)),
                            ((nb057AlphaDummy160), (nb057AlphaDummy161 f)),
                            ((nb057AlphaDummy134), (nb057AlphaDummy135 f)),
                            ((nb057AlphaDummy125), (nb057AlphaDummy127 f)),
                            ((nb057AlphaDummy124), (nb057AlphaDummy126 f)),
                            ((nb057AlphaDummy128), (nb057AlphaDummy129 f)),
                            ((nb057AlphaDummy046), (nb057AlphaDummy049 f)),
                            ((nb057AlphaDummy045), (nb057AlphaDummy048 f)),
                            ((nb057AlphaDummy044), (nb057AlphaDummy047 f)),
                            ((nb057AlphaDummy050), (nb057AlphaDummy051 f)),
                            ((nb057AlphaDummy000), a), ((nb057AlphaDummy001), f),
                            ((nb057AlphaDummy002), (nb057AlphaDummy003 f a))]
                          (synCcompl (synCsn (synC0c))) (by
                            simp only [fv_syn_ccompl, fv_syn_csn, fv_syn_c0c])))))))))))))


end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired

end

/-! Certificates from `NAR4C057C001Part021`. -/


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

/-- Checked nominal proof certificate identified upstream as `nb057_split_alpha_0048`. -/
@[expose]
noncomputable def nb057SplitAlpha0048 (f : Var) (a : Var) :
    TAlphaWff
      [((nb057AlphaDummy182), (nb057AlphaDummy185 f)),
        ((nb057AlphaDummy181), (nb057AlphaDummy184 f)),
        ((nb057AlphaDummy180), (nb057AlphaDummy183 f)),
        ((nb057AlphaDummy178), (nb057AlphaDummy179 f)),
        ((nb057AlphaDummy174), (nb057AlphaDummy176 f)),
        ((nb057AlphaDummy175), (nb057AlphaDummy177 f)),
        ((nb057AlphaDummy167), (nb057AlphaDummy169 f)),
        ((nb057AlphaDummy166), (nb057AlphaDummy168 f)),
        ((nb057AlphaDummy172), (nb057AlphaDummy173 f)),
        ((nb057AlphaDummy170), (nb057AlphaDummy171 f)),
        ((nb057AlphaDummy125), (nb057AlphaDummy127 f)),
        ((nb057AlphaDummy124), (nb057AlphaDummy126 f)),
        ((nb057AlphaDummy128), (nb057AlphaDummy129 f)),
        ((nb057AlphaDummy046), (nb057AlphaDummy049 f)),
        ((nb057AlphaDummy045), (nb057AlphaDummy048 f)),
        ((nb057AlphaDummy044), (nb057AlphaDummy047 f)),
        ((nb057AlphaDummy050), (nb057AlphaDummy051 f)),
        ((nb057AlphaDummy000), a), ((nb057AlphaDummy001), f),
        ((nb057AlphaDummy002), (nb057AlphaDummy003 f a))]
      (Wff.imp (Wff.classEq
          (synCin (Class.cv (nb057AlphaDummy181)) (Class.cv (nb057AlphaDummy182)))
          (synC0)) (Wff.neg (Wff.classEq (Class.cv (nb057AlphaDummy180))
            (synCun (Class.cv (nb057AlphaDummy181)) (Class.cv (nb057AlphaDummy182))))))
      (Wff.imp (Wff.classEq (synCin (Class.cv (nb057AlphaDummy184 f))
            (Class.cv (nb057AlphaDummy185 f))) (synC0)) (Wff.neg
          (Wff.classEq (Class.cv (nb057AlphaDummy183 f))
            (synCun (Class.cv (nb057AlphaDummy184 f))
              (Class.cv (nb057AlphaDummy185 f)))))) :=
  (TAlphaWff.imp (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.neg (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0178) 0))
                          (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0179 f) 0))
                          (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0176) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0177 f) 0))
                            (TAlphaVar.there (freshVar_injective
                                (((Class.cv (nb057AlphaDummy174))).fv ∪ ((synC1c)).fv)
                                (by decide)) (freshVar_injective
                                (((Class.cv (nb057AlphaDummy176 f))).fv ∪ ((synC1c)).fv)
                                (by decide)) (TAlphaVar.here _ _ _))))))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0182) 0))
                          (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0183 f) 0))
                          (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0180) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0181 f) 0))
                            (TAlphaVar.here _ _ _)))))))))
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.neg (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0178) 0))
                          (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0179 f) 0))
                          (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0176) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0177 f) 0))
                            (TAlphaVar.there (freshVar_injective
                                (((Class.cv (nb057AlphaDummy174))).fv ∪ ((synC1c)).fv)
                                (by decide)) (freshVar_injective
                                (((Class.cv (nb057AlphaDummy176 f))).fv ∪ ((synC1c)).fv)
                                (by decide)) (TAlphaVar.here _ _ _))))))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0182) 0))
                          (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0183 f) 0))
                          (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0180) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0181 f) 0))
                            (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.reflOfClosed
        [((nb057AlphaDummy182), (nb057AlphaDummy185 f)),
          ((nb057AlphaDummy181), (nb057AlphaDummy184 f)),
          ((nb057AlphaDummy180), (nb057AlphaDummy183 f)),
          ((nb057AlphaDummy178), (nb057AlphaDummy179 f)),
          ((nb057AlphaDummy174), (nb057AlphaDummy176 f)),
          ((nb057AlphaDummy175), (nb057AlphaDummy177 f)),
          ((nb057AlphaDummy167), (nb057AlphaDummy169 f)),
          ((nb057AlphaDummy166), (nb057AlphaDummy168 f)),
          ((nb057AlphaDummy172), (nb057AlphaDummy173 f)),
          ((nb057AlphaDummy170), (nb057AlphaDummy171 f)),
          ((nb057AlphaDummy125), (nb057AlphaDummy127 f)),
          ((nb057AlphaDummy124), (nb057AlphaDummy126 f)),
          ((nb057AlphaDummy128), (nb057AlphaDummy129 f)),
          ((nb057AlphaDummy046), (nb057AlphaDummy049 f)),
          ((nb057AlphaDummy045), (nb057AlphaDummy048 f)),
          ((nb057AlphaDummy044), (nb057AlphaDummy047 f)),
          ((nb057AlphaDummy050), (nb057AlphaDummy051 f)),
          ((nb057AlphaDummy000), a), ((nb057AlphaDummy001), f),
          ((nb057AlphaDummy002), (nb057AlphaDummy003 f a))]
        (synC0) (by simp only [fv_syn_c0]))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv
          (TAlphaVar.there
            (freshVar_injective (((Class.cv (nb057AlphaDummy174))).fv ∪ ((synC1c)).fv)
              (by decide)) (freshVar_injective
              (((Class.cv (nb057AlphaDummy176 f))).fv ∪ ((synC1c)).fv) (by decide))
            (TAlphaVar.there (freshVar_injective
                (((Class.cv (nb057AlphaDummy174))).fv ∪ ((synC1c)).fv) (by decide))
              (freshVar_injective
                (((Class.cv (nb057AlphaDummy176 f))).fv ∪ ((synC1c)).fv) (by decide))
              (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                  (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0186) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0187 f) 0))
                            (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0184) 0))
                              (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0185 f) 0))
                              (TAlphaVar.there (freshVar_injective
                                  (((Class.cv (nb057AlphaDummy174))).fv ∪ ((synC1c)).fv)
                                  (by decide)) (freshVar_injective
                                  (((Class.cv (nb057AlphaDummy176 f))).fv ∪ ((synC1c)).fv)
                                  (by decide)) (TAlphaVar.here _ _ _))))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0186) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0187 f) 0))
                            (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0184) 0))
                              (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0185 f) 0))
                              (TAlphaVar.there (freshVar_injective
                                  (((Class.cv (nb057AlphaDummy174))).fv ∪ ((synC1c)).fv)
                                  (by decide)) (freshVar_injective
                                  (((Class.cv (nb057AlphaDummy176 f))).fv ∪ ((synC1c)).fv)
                                  (by decide)) (TAlphaVar.here _ _ _))))))))))
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                  (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0190) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0191 f) 0))
                            (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0188) 0))
                              (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0189 f) 0))
                              (TAlphaVar.here _ _ _)))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0190) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0191 f) 0))
                            (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0188) 0))
                              (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0189 f) 0))
                              (TAlphaVar.here _ _ _)))))))))))))))

/-- Checked nominal proof certificate identified upstream as `nb057_split_alpha_0049`. -/
@[expose]
noncomputable def nb057SplitAlpha0049 (f : Var) (a : Var) :
    TAlphaWff
      [((nb057AlphaDummy174), (nb057AlphaDummy176 f)),
        ((nb057AlphaDummy175), (nb057AlphaDummy177 f)),
        ((nb057AlphaDummy167), (nb057AlphaDummy169 f)),
        ((nb057AlphaDummy166), (nb057AlphaDummy168 f)),
        ((nb057AlphaDummy172), (nb057AlphaDummy173 f)),
        ((nb057AlphaDummy170), (nb057AlphaDummy171 f)),
        ((nb057AlphaDummy125), (nb057AlphaDummy127 f)),
        ((nb057AlphaDummy124), (nb057AlphaDummy126 f)),
        ((nb057AlphaDummy128), (nb057AlphaDummy129 f)),
        ((nb057AlphaDummy046), (nb057AlphaDummy049 f)),
        ((nb057AlphaDummy045), (nb057AlphaDummy048 f)),
        ((nb057AlphaDummy044), (nb057AlphaDummy047 f)),
        ((nb057AlphaDummy050), (nb057AlphaDummy051 f)),
        ((nb057AlphaDummy000), a), ((nb057AlphaDummy001), f),
        ((nb057AlphaDummy002), (nb057AlphaDummy003 f a))]
      (Wff.imp (Wff.classMem (Class.cv (nb057AlphaDummy174))
          (Class.cv (nb057AlphaDummy167))) (Wff.neg
          (Wff.classEq (Class.cv (nb057AlphaDummy175))
            (synCif (Wff.classMem (Class.cv (nb057AlphaDummy174)) (synCnnc))
              (synCplc (Class.cv (nb057AlphaDummy174)) (synC1c))
              (Class.cv (nb057AlphaDummy174))))))
      (Wff.imp (Wff.classMem (Class.cv (nb057AlphaDummy176 f))
          (Class.cv (nb057AlphaDummy169 f))) (Wff.neg
          (Wff.classEq (Class.cv (nb057AlphaDummy177 f))
            (synCif (Wff.classMem (Class.cv (nb057AlphaDummy176 f)) (synCnnc))
              (synCplc (Class.cv (nb057AlphaDummy176 f)) (synC1c))
              (Class.cv (nb057AlphaDummy176 f)))))) :=
  (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0170) 0))
          (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0171 f) 0))
          (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0170) 1))
            (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0171 f) 1))
            (TAlphaVar.here _ _ _))))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv
          (TAlphaVar.there
            (freshVar_injective (((Class.cv (nb057AlphaDummy167))).fv) (by decide))
            (freshVar_injective (((Class.cv (nb057AlphaDummy169 f))).fv) (by decide))
            (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp (TAlphaWff.neg
              (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                  (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                          (TAlphaClass.cv (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0174) 1))
                              (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0175 f) 1))
                              (TAlphaVar.there (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb057_support_mem_0174) 0)) (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb057_support_mem_0175 f) 0))
                                (TAlphaVar.there (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb057_support_mem_0172) 0)) (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb057_support_mem_0173 f) 0))
                                  (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.reflOfClosed
                                [((nb057AlphaDummy182), (nb057AlphaDummy185 f)),
                                  ((nb057AlphaDummy181), (nb057AlphaDummy184 f)),
                                  ((nb057AlphaDummy180), (nb057AlphaDummy183 f)),
                                  ((nb057AlphaDummy178), (nb057AlphaDummy179 f)),
                                  ((nb057AlphaDummy174), (nb057AlphaDummy176 f)),
                                  ((nb057AlphaDummy175), (nb057AlphaDummy177 f)),
                                  ((nb057AlphaDummy167), (nb057AlphaDummy169 f)),
                                  ((nb057AlphaDummy166), (nb057AlphaDummy168 f)),
                                  ((nb057AlphaDummy172), (nb057AlphaDummy173 f)),
                                  ((nb057AlphaDummy170), (nb057AlphaDummy171 f)),
                                  ((nb057AlphaDummy125), (nb057AlphaDummy127 f)),
                                  ((nb057AlphaDummy124), (nb057AlphaDummy126 f)),
                                  ((nb057AlphaDummy128), (nb057AlphaDummy129 f)),
                                  ((nb057AlphaDummy046), (nb057AlphaDummy049 f)),
                                  ((nb057AlphaDummy045), (nb057AlphaDummy048 f)),
                                  ((nb057AlphaDummy044), (nb057AlphaDummy047 f)),
                                  ((nb057AlphaDummy050), (nb057AlphaDummy051 f)),
                                  ((nb057AlphaDummy000), a), ((nb057AlphaDummy001), f),
                                  ((nb057AlphaDummy002), (nb057AlphaDummy003 f a))]
                                (synC1c) (by simp only [fv_syn_c1c])))
                            (TAlphaWff.neg (nb057SplitAlpha0048 f a))))))))
                (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there
                      (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0172) 0))
                      (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0173 f) 0))
                      (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
                    [((nb057AlphaDummy178), (nb057AlphaDummy179 f)),
                      ((nb057AlphaDummy174), (nb057AlphaDummy176 f)),
                      ((nb057AlphaDummy175), (nb057AlphaDummy177 f)),
                      ((nb057AlphaDummy167), (nb057AlphaDummy169 f)),
                      ((nb057AlphaDummy166), (nb057AlphaDummy168 f)),
                      ((nb057AlphaDummy172), (nb057AlphaDummy173 f)),
                      ((nb057AlphaDummy170), (nb057AlphaDummy171 f)),
                      ((nb057AlphaDummy125), (nb057AlphaDummy127 f)),
                      ((nb057AlphaDummy124), (nb057AlphaDummy126 f)),
                      ((nb057AlphaDummy128), (nb057AlphaDummy129 f)),
                      ((nb057AlphaDummy046), (nb057AlphaDummy049 f)),
                      ((nb057AlphaDummy045), (nb057AlphaDummy048 f)),
                      ((nb057AlphaDummy044), (nb057AlphaDummy047 f)),
                      ((nb057AlphaDummy050), (nb057AlphaDummy051 f)),
                      ((nb057AlphaDummy000), a), ((nb057AlphaDummy001), f),
                      ((nb057AlphaDummy002), (nb057AlphaDummy003 f a))]
                    (synCnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                  (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0172) 0))
                    (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0173 f) 0))
                    (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv
                    (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0172) 0))
                      (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0173 f) 0))
                      (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
                    [((nb057AlphaDummy178), (nb057AlphaDummy179 f)),
                      ((nb057AlphaDummy174), (nb057AlphaDummy176 f)),
                      ((nb057AlphaDummy175), (nb057AlphaDummy177 f)),
                      ((nb057AlphaDummy167), (nb057AlphaDummy169 f)),
                      ((nb057AlphaDummy166), (nb057AlphaDummy168 f)),
                      ((nb057AlphaDummy172), (nb057AlphaDummy173 f)),
                      ((nb057AlphaDummy170), (nb057AlphaDummy171 f)),
                      ((nb057AlphaDummy125), (nb057AlphaDummy127 f)),
                      ((nb057AlphaDummy124), (nb057AlphaDummy126 f)),
                      ((nb057AlphaDummy128), (nb057AlphaDummy129 f)),
                      ((nb057AlphaDummy046), (nb057AlphaDummy049 f)),
                      ((nb057AlphaDummy045), (nb057AlphaDummy048 f)),
                      ((nb057AlphaDummy044), (nb057AlphaDummy047 f)),
                      ((nb057AlphaDummy050), (nb057AlphaDummy051 f)),
                      ((nb057AlphaDummy000), a), ((nb057AlphaDummy001), f),
                      ((nb057AlphaDummy002), (nb057AlphaDummy003 f a))]
                    (synCnnc) (by simp only [fv_syn_cnnc]))))))))))

/-- Checked nominal proof certificate identified upstream as `nb057_split_alpha_0050`. -/
@[expose]
noncomputable def nb057SplitAlpha0050 (f : Var) (a : Var) :
    TAlphaWff
      [((nb057AlphaDummy182), (nb057AlphaDummy185 f)),
        ((nb057AlphaDummy181), (nb057AlphaDummy184 f)),
        ((nb057AlphaDummy180), (nb057AlphaDummy183 f)),
        ((nb057AlphaDummy178), (nb057AlphaDummy179 f)),
        ((nb057AlphaDummy174), (nb057AlphaDummy176 f)),
        ((nb057AlphaDummy175), (nb057AlphaDummy177 f)),
        ((nb057AlphaDummy200), (nb057AlphaDummy201 f)),
        ((nb057AlphaDummy198), (nb057AlphaDummy199 f)),
        ((nb057AlphaDummy167), (nb057AlphaDummy169 f)),
        ((nb057AlphaDummy166), (nb057AlphaDummy168 f)),
        ((nb057AlphaDummy196), (nb057AlphaDummy197 f)),
        ((nb057AlphaDummy170), (nb057AlphaDummy171 f)),
        ((nb057AlphaDummy125), (nb057AlphaDummy127 f)),
        ((nb057AlphaDummy124), (nb057AlphaDummy126 f)),
        ((nb057AlphaDummy128), (nb057AlphaDummy129 f)),
        ((nb057AlphaDummy046), (nb057AlphaDummy049 f)),
        ((nb057AlphaDummy045), (nb057AlphaDummy048 f)),
        ((nb057AlphaDummy044), (nb057AlphaDummy047 f)),
        ((nb057AlphaDummy050), (nb057AlphaDummy051 f)),
        ((nb057AlphaDummy000), a), ((nb057AlphaDummy001), f),
        ((nb057AlphaDummy002), (nb057AlphaDummy003 f a))]
      (Wff.imp (Wff.classEq
          (synCin (Class.cv (nb057AlphaDummy181)) (Class.cv (nb057AlphaDummy182)))
          (synC0)) (Wff.neg (Wff.classEq (Class.cv (nb057AlphaDummy180))
            (synCun (Class.cv (nb057AlphaDummy181)) (Class.cv (nb057AlphaDummy182))))))
      (Wff.imp (Wff.classEq (synCin (Class.cv (nb057AlphaDummy184 f))
            (Class.cv (nb057AlphaDummy185 f))) (synC0)) (Wff.neg
          (Wff.classEq (Class.cv (nb057AlphaDummy183 f))
            (synCun (Class.cv (nb057AlphaDummy184 f))
              (Class.cv (nb057AlphaDummy185 f)))))) :=
  (TAlphaWff.imp (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.neg (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0178) 0))
                          (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0179 f) 0))
                          (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0176) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0177 f) 0))
                            (TAlphaVar.there (freshVar_injective
                                (((Class.cv (nb057AlphaDummy174))).fv ∪ ((synC1c)).fv)
                                (by decide)) (freshVar_injective
                                (((Class.cv (nb057AlphaDummy176 f))).fv ∪ ((synC1c)).fv)
                                (by decide)) (TAlphaVar.here _ _ _))))))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0182) 0))
                          (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0183 f) 0))
                          (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0180) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0181 f) 0))
                            (TAlphaVar.here _ _ _)))))))))
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.neg (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0178) 0))
                          (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0179 f) 0))
                          (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0176) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0177 f) 0))
                            (TAlphaVar.there (freshVar_injective
                                (((Class.cv (nb057AlphaDummy174))).fv ∪ ((synC1c)).fv)
                                (by decide)) (freshVar_injective
                                (((Class.cv (nb057AlphaDummy176 f))).fv ∪ ((synC1c)).fv)
                                (by decide)) (TAlphaVar.here _ _ _))))))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0182) 0))
                          (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0183 f) 0))
                          (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0180) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0181 f) 0))
                            (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.reflOfClosed
        [((nb057AlphaDummy182), (nb057AlphaDummy185 f)),
          ((nb057AlphaDummy181), (nb057AlphaDummy184 f)),
          ((nb057AlphaDummy180), (nb057AlphaDummy183 f)),
          ((nb057AlphaDummy178), (nb057AlphaDummy179 f)),
          ((nb057AlphaDummy174), (nb057AlphaDummy176 f)),
          ((nb057AlphaDummy175), (nb057AlphaDummy177 f)),
          ((nb057AlphaDummy200), (nb057AlphaDummy201 f)),
          ((nb057AlphaDummy198), (nb057AlphaDummy199 f)),
          ((nb057AlphaDummy167), (nb057AlphaDummy169 f)),
          ((nb057AlphaDummy166), (nb057AlphaDummy168 f)),
          ((nb057AlphaDummy196), (nb057AlphaDummy197 f)),
          ((nb057AlphaDummy170), (nb057AlphaDummy171 f)),
          ((nb057AlphaDummy125), (nb057AlphaDummy127 f)),
          ((nb057AlphaDummy124), (nb057AlphaDummy126 f)),
          ((nb057AlphaDummy128), (nb057AlphaDummy129 f)),
          ((nb057AlphaDummy046), (nb057AlphaDummy049 f)),
          ((nb057AlphaDummy045), (nb057AlphaDummy048 f)),
          ((nb057AlphaDummy044), (nb057AlphaDummy047 f)),
          ((nb057AlphaDummy050), (nb057AlphaDummy051 f)),
          ((nb057AlphaDummy000), a), ((nb057AlphaDummy001), f),
          ((nb057AlphaDummy002), (nb057AlphaDummy003 f a))]
        (synC0) (by simp only [fv_syn_c0]))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv
          (TAlphaVar.there
            (freshVar_injective (((Class.cv (nb057AlphaDummy174))).fv ∪ ((synC1c)).fv)
              (by decide)) (freshVar_injective
              (((Class.cv (nb057AlphaDummy176 f))).fv ∪ ((synC1c)).fv) (by decide))
            (TAlphaVar.there (freshVar_injective
                (((Class.cv (nb057AlphaDummy174))).fv ∪ ((synC1c)).fv) (by decide))
              (freshVar_injective
                (((Class.cv (nb057AlphaDummy176 f))).fv ∪ ((synC1c)).fv) (by decide))
              (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                  (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0186) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0187 f) 0))
                            (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0184) 0))
                              (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0185 f) 0))
                              (TAlphaVar.there (freshVar_injective
                                  (((Class.cv (nb057AlphaDummy174))).fv ∪ ((synC1c)).fv)
                                  (by decide)) (freshVar_injective
                                  (((Class.cv (nb057AlphaDummy176 f))).fv ∪ ((synC1c)).fv)
                                  (by decide)) (TAlphaVar.here _ _ _))))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0186) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0187 f) 0))
                            (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0184) 0))
                              (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0185 f) 0))
                              (TAlphaVar.there (freshVar_injective
                                  (((Class.cv (nb057AlphaDummy174))).fv ∪ ((synC1c)).fv)
                                  (by decide)) (freshVar_injective
                                  (((Class.cv (nb057AlphaDummy176 f))).fv ∪ ((synC1c)).fv)
                                  (by decide)) (TAlphaVar.here _ _ _))))))))))
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                  (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0190) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0191 f) 0))
                            (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0188) 0))
                              (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0189 f) 0))
                              (TAlphaVar.here _ _ _)))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0190) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0191 f) 0))
                            (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0188) 0))
                              (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0189 f) 0))
                              (TAlphaVar.here _ _ _)))))))))))))))

/-- Checked nominal proof certificate identified upstream as `nb057_split_alpha_0051`. -/
@[expose]
noncomputable def nb057SplitAlpha0051 (f : Var) (a : Var) :
    TAlphaWff
      [((nb057AlphaDummy174), (nb057AlphaDummy176 f)),
        ((nb057AlphaDummy175), (nb057AlphaDummy177 f)),
        ((nb057AlphaDummy200), (nb057AlphaDummy201 f)),
        ((nb057AlphaDummy198), (nb057AlphaDummy199 f)),
        ((nb057AlphaDummy167), (nb057AlphaDummy169 f)),
        ((nb057AlphaDummy166), (nb057AlphaDummy168 f)),
        ((nb057AlphaDummy196), (nb057AlphaDummy197 f)),
        ((nb057AlphaDummy170), (nb057AlphaDummy171 f)),
        ((nb057AlphaDummy125), (nb057AlphaDummy127 f)),
        ((nb057AlphaDummy124), (nb057AlphaDummy126 f)),
        ((nb057AlphaDummy128), (nb057AlphaDummy129 f)),
        ((nb057AlphaDummy046), (nb057AlphaDummy049 f)),
        ((nb057AlphaDummy045), (nb057AlphaDummy048 f)),
        ((nb057AlphaDummy044), (nb057AlphaDummy047 f)),
        ((nb057AlphaDummy050), (nb057AlphaDummy051 f)),
        ((nb057AlphaDummy000), a), ((nb057AlphaDummy001), f),
        ((nb057AlphaDummy002), (nb057AlphaDummy003 f a))]
      (Wff.imp (Wff.classMem (Class.cv (nb057AlphaDummy174))
          (Class.cv (nb057AlphaDummy167))) (Wff.neg
          (Wff.classEq (Class.cv (nb057AlphaDummy175))
            (synCif (Wff.classMem (Class.cv (nb057AlphaDummy174)) (synCnnc))
              (synCplc (Class.cv (nb057AlphaDummy174)) (synC1c))
              (Class.cv (nb057AlphaDummy174))))))
      (Wff.imp (Wff.classMem (Class.cv (nb057AlphaDummy176 f))
          (Class.cv (nb057AlphaDummy169 f))) (Wff.neg
          (Wff.classEq (Class.cv (nb057AlphaDummy177 f))
            (synCif (Wff.classMem (Class.cv (nb057AlphaDummy176 f)) (synCnnc))
              (synCplc (Class.cv (nb057AlphaDummy176 f)) (synC1c))
              (Class.cv (nb057AlphaDummy176 f)))))) :=
  (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0170) 0))
          (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0171 f) 0))
          (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0170) 1))
            (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0171 f) 1))
            (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0200) 0))
              (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0201 f) 0))
              (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0198) 0))
                (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0199 f) 0))
                (TAlphaVar.here _ _ _))))))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv
          (TAlphaVar.there
            (freshVar_injective (((Class.cv (nb057AlphaDummy167))).fv) (by decide))
            (freshVar_injective (((Class.cv (nb057AlphaDummy169 f))).fv) (by decide))
            (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp (TAlphaWff.neg
              (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                  (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                          (TAlphaClass.cv (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0174) 1))
                              (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0175 f) 1))
                              (TAlphaVar.there (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb057_support_mem_0174) 0)) (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb057_support_mem_0175 f) 0))
                                (TAlphaVar.there (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb057_support_mem_0172) 0)) (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb057_support_mem_0173 f) 0))
                                  (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.reflOfClosed
                                [((nb057AlphaDummy182), (nb057AlphaDummy185 f)),
                                  ((nb057AlphaDummy181), (nb057AlphaDummy184 f)),
                                  ((nb057AlphaDummy180), (nb057AlphaDummy183 f)),
                                  ((nb057AlphaDummy178), (nb057AlphaDummy179 f)),
                                  ((nb057AlphaDummy174), (nb057AlphaDummy176 f)),
                                  ((nb057AlphaDummy175), (nb057AlphaDummy177 f)),
                                  ((nb057AlphaDummy200), (nb057AlphaDummy201 f)),
                                  ((nb057AlphaDummy198), (nb057AlphaDummy199 f)),
                                  ((nb057AlphaDummy167), (nb057AlphaDummy169 f)),
                                  ((nb057AlphaDummy166), (nb057AlphaDummy168 f)),
                                  ((nb057AlphaDummy196), (nb057AlphaDummy197 f)),
                                  ((nb057AlphaDummy170), (nb057AlphaDummy171 f)),
                                  ((nb057AlphaDummy125), (nb057AlphaDummy127 f)),
                                  ((nb057AlphaDummy124), (nb057AlphaDummy126 f)),
                                  ((nb057AlphaDummy128), (nb057AlphaDummy129 f)),
                                  ((nb057AlphaDummy046), (nb057AlphaDummy049 f)),
                                  ((nb057AlphaDummy045), (nb057AlphaDummy048 f)),
                                  ((nb057AlphaDummy044), (nb057AlphaDummy047 f)),
                                  ((nb057AlphaDummy050), (nb057AlphaDummy051 f)),
                                  ((nb057AlphaDummy000), a), ((nb057AlphaDummy001), f),
                                  ((nb057AlphaDummy002), (nb057AlphaDummy003 f a))]
                                (synC1c) (by simp only [fv_syn_c1c])))
                            (TAlphaWff.neg (nb057SplitAlpha0050 f a))))))))
                (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there
                      (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0172) 0))
                      (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0173 f) 0))
                      (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
                    [((nb057AlphaDummy178), (nb057AlphaDummy179 f)),
                      ((nb057AlphaDummy174), (nb057AlphaDummy176 f)),
                      ((nb057AlphaDummy175), (nb057AlphaDummy177 f)),
                      ((nb057AlphaDummy200), (nb057AlphaDummy201 f)),
                      ((nb057AlphaDummy198), (nb057AlphaDummy199 f)),
                      ((nb057AlphaDummy167), (nb057AlphaDummy169 f)),
                      ((nb057AlphaDummy166), (nb057AlphaDummy168 f)),
                      ((nb057AlphaDummy196), (nb057AlphaDummy197 f)),
                      ((nb057AlphaDummy170), (nb057AlphaDummy171 f)),
                      ((nb057AlphaDummy125), (nb057AlphaDummy127 f)),
                      ((nb057AlphaDummy124), (nb057AlphaDummy126 f)),
                      ((nb057AlphaDummy128), (nb057AlphaDummy129 f)),
                      ((nb057AlphaDummy046), (nb057AlphaDummy049 f)),
                      ((nb057AlphaDummy045), (nb057AlphaDummy048 f)),
                      ((nb057AlphaDummy044), (nb057AlphaDummy047 f)),
                      ((nb057AlphaDummy050), (nb057AlphaDummy051 f)),
                      ((nb057AlphaDummy000), a), ((nb057AlphaDummy001), f),
                      ((nb057AlphaDummy002), (nb057AlphaDummy003 f a))]
                    (synCnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                  (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0172) 0))
                    (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0173 f) 0))
                    (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv
                    (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0172) 0))
                      (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0173 f) 0))
                      (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
                    [((nb057AlphaDummy178), (nb057AlphaDummy179 f)),
                      ((nb057AlphaDummy174), (nb057AlphaDummy176 f)),
                      ((nb057AlphaDummy175), (nb057AlphaDummy177 f)),
                      ((nb057AlphaDummy200), (nb057AlphaDummy201 f)),
                      ((nb057AlphaDummy198), (nb057AlphaDummy199 f)),
                      ((nb057AlphaDummy167), (nb057AlphaDummy169 f)),
                      ((nb057AlphaDummy166), (nb057AlphaDummy168 f)),
                      ((nb057AlphaDummy196), (nb057AlphaDummy197 f)),
                      ((nb057AlphaDummy170), (nb057AlphaDummy171 f)),
                      ((nb057AlphaDummy125), (nb057AlphaDummy127 f)),
                      ((nb057AlphaDummy124), (nb057AlphaDummy126 f)),
                      ((nb057AlphaDummy128), (nb057AlphaDummy129 f)),
                      ((nb057AlphaDummy046), (nb057AlphaDummy049 f)),
                      ((nb057AlphaDummy045), (nb057AlphaDummy048 f)),
                      ((nb057AlphaDummy044), (nb057AlphaDummy047 f)),
                      ((nb057AlphaDummy050), (nb057AlphaDummy051 f)),
                      ((nb057AlphaDummy000), a), ((nb057AlphaDummy001), f),
                      ((nb057AlphaDummy002), (nb057AlphaDummy003 f a))]
                    (synCnnc) (by simp only [fv_syn_cnnc]))))))))))


end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired

end

/-! Certificates from `NAR4C057C001Part022`. -/


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

/-- Checked nominal proof certificate identified upstream as `nb057_split_alpha_0052`. -/
@[expose]
noncomputable def nb057SplitAlpha0052 (f : Var) (a : Var) :
    TAlphaWff
      [((nb057AlphaDummy196), (nb057AlphaDummy197 f)),
        ((nb057AlphaDummy170), (nb057AlphaDummy171 f)),
        ((nb057AlphaDummy125), (nb057AlphaDummy127 f)),
        ((nb057AlphaDummy124), (nb057AlphaDummy126 f)),
        ((nb057AlphaDummy128), (nb057AlphaDummy129 f)),
        ((nb057AlphaDummy046), (nb057AlphaDummy049 f)),
        ((nb057AlphaDummy045), (nb057AlphaDummy048 f)),
        ((nb057AlphaDummy044), (nb057AlphaDummy047 f)),
        ((nb057AlphaDummy050), (nb057AlphaDummy051 f)),
        ((nb057AlphaDummy000), a), ((nb057AlphaDummy001), f),
        ((nb057AlphaDummy002), (nb057AlphaDummy003 f a))]
      (Wff.imp (Wff.classMem (Class.cv (nb057AlphaDummy196))
          (Class.cab (nb057AlphaDummy166)
            (synWrex (nb057AlphaDummy167) (Class.cv (nb057AlphaDummy124))
              (Wff.classEq (Class.cv (nb057AlphaDummy166))
                (synCun (synCphi (Class.cv (nb057AlphaDummy167))) (synCsn (synC0c)))))))
        (Wff.neg (Wff.classMem (Class.cv (nb057AlphaDummy196))
            (Class.cab (nb057AlphaDummy166)
              (synWrex (nb057AlphaDummy167) (Class.cv (nb057AlphaDummy124))
                (Wff.classEq (Class.cv (nb057AlphaDummy166))
                  (synCun (synCphi (Class.cv (nb057AlphaDummy167)))
                    (synCsn (synC0c)))))))))
      (Wff.imp (Wff.classMem (Class.cv (nb057AlphaDummy197 f))
          (Class.cab (nb057AlphaDummy168 f)
            (synWrex (nb057AlphaDummy169 f) (Class.cv (nb057AlphaDummy126 f))
              (Wff.classEq (Class.cv (nb057AlphaDummy168 f))
                (synCun (synCphi (Class.cv (nb057AlphaDummy169 f)))
                  (synCsn (synC0c))))))) (Wff.neg
          (Wff.classMem (Class.cv (nb057AlphaDummy197 f))
            (Class.cab (nb057AlphaDummy168 f)
              (synWrex (nb057AlphaDummy169 f) (Class.cv (nb057AlphaDummy126 f))
                (Wff.classEq (Class.cv (nb057AlphaDummy168 f))
                  (synCun (synCphi (Class.cv (nb057AlphaDummy169 f)))
                    (synCsn (synC0c))))))))) :=
  (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.ex (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0192) 1))
                  (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0194 f) 1)) (TAlphaVar.there
                    (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0192) 0))
                    (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0194 f) 0))
                    (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0196) 0))
                      (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0197 f) 0))
                      (TAlphaVar.there
                        (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0193) 0))
                        (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0195 f) 0))
                        (TAlphaVar.there
                          (freshVar_injective (((Class.cv (nb057AlphaDummy001))).fv)
                            (by decide)) (freshVar_injective (((Class.cv f)).fv) (by decide))
                          (TAlphaVar.here _ _ _)))))))) (TAlphaWff.classEq (TAlphaClass.cv
                (TAlphaVar.there (freshVar_injective (((Class.cv (nb057AlphaDummy125))).fv ∪
                      ((Class.cv (nb057AlphaDummy124))).fv) (by decide)) (freshVar_injective
                    (((Class.cv (nb057AlphaDummy127 f))).fv ∪
                      ((Class.cv (nb057AlphaDummy126 f))).fv) (by decide))
                  (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                        (TAlphaWff.neg (TAlphaWff.conj
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cab (TAlphaWff.ex
                                  (TAlphaWff.neg (nb057SplitAlpha0051 f a)))))
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cab (TAlphaWff.ex
                                  (TAlphaWff.neg (nb057SplitAlpha0051 f a)))))))))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                      (TAlphaClass.reflOfClosed
                        [((nb057AlphaDummy198), (nb057AlphaDummy199 f)),
                          ((nb057AlphaDummy167), (nb057AlphaDummy169 f)),
                          ((nb057AlphaDummy166), (nb057AlphaDummy168 f)),
                          ((nb057AlphaDummy196), (nb057AlphaDummy197 f)),
                          ((nb057AlphaDummy170), (nb057AlphaDummy171 f)),
                          ((nb057AlphaDummy125), (nb057AlphaDummy127 f)),
                          ((nb057AlphaDummy124), (nb057AlphaDummy126 f)),
                          ((nb057AlphaDummy128), (nb057AlphaDummy129 f)),
                          ((nb057AlphaDummy046), (nb057AlphaDummy049 f)),
                          ((nb057AlphaDummy045), (nb057AlphaDummy048 f)),
                          ((nb057AlphaDummy044), (nb057AlphaDummy047 f)),
                          ((nb057AlphaDummy050), (nb057AlphaDummy051 f)),
                          ((nb057AlphaDummy000), a), ((nb057AlphaDummy001), f),
                          ((nb057AlphaDummy002), (nb057AlphaDummy003 f a))]
                        (synCcompl (synCsn (synC0c)))
                        (by simp only [fv_syn_ccompl, fv_syn_csn, fv_syn_c0c])))))))))))
    (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
          (TAlphaWff.ex (TAlphaWff.conj
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                  (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0192) 1))
                    (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0194 f) 1))
                    (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0192) 0))
                      (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0194 f) 0))
                      (TAlphaVar.there
                        (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0196) 0))
                        (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0197 f) 0))
                        (TAlphaVar.there
                          (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0193) 0))
                          (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0195 f) 0))
                          (TAlphaVar.there
                            (freshVar_injective (((Class.cv (nb057AlphaDummy001))).fv)
                              (by decide)) (freshVar_injective (((Class.cv f)).fv) (by decide))
                            (TAlphaVar.here _ _ _)))))))) (TAlphaWff.classEq (TAlphaClass.cv
                  (TAlphaVar.there (freshVar_injective
                      (((Class.cv (nb057AlphaDummy125))).fv ∪
                        ((Class.cv (nb057AlphaDummy124))).fv) (by decide))
                    (freshVar_injective (((Class.cv (nb057AlphaDummy127 f))).fv ∪
                        ((Class.cv (nb057AlphaDummy126 f))).fv) (by decide))
                    (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cab (TAlphaWff.ex
                                    (TAlphaWff.neg (nb057SplitAlpha0051 f a)))))
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cab (TAlphaWff.ex
                                    (TAlphaWff.neg (nb057SplitAlpha0051 f a)))))))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.reflOfClosed
                          [((nb057AlphaDummy198), (nb057AlphaDummy199 f)),
                            ((nb057AlphaDummy167), (nb057AlphaDummy169 f)),
                            ((nb057AlphaDummy166), (nb057AlphaDummy168 f)),
                            ((nb057AlphaDummy196), (nb057AlphaDummy197 f)),
                            ((nb057AlphaDummy170), (nb057AlphaDummy171 f)),
                            ((nb057AlphaDummy125), (nb057AlphaDummy127 f)),
                            ((nb057AlphaDummy124), (nb057AlphaDummy126 f)),
                            ((nb057AlphaDummy128), (nb057AlphaDummy129 f)),
                            ((nb057AlphaDummy046), (nb057AlphaDummy049 f)),
                            ((nb057AlphaDummy045), (nb057AlphaDummy048 f)),
                            ((nb057AlphaDummy044), (nb057AlphaDummy047 f)),
                            ((nb057AlphaDummy050), (nb057AlphaDummy051 f)),
                            ((nb057AlphaDummy000), a), ((nb057AlphaDummy001), f),
                            ((nb057AlphaDummy002), (nb057AlphaDummy003 f a))]
                          (synCcompl (synCsn (synC0c))) (by
                            simp only [fv_syn_ccompl, fv_syn_csn, fv_syn_c0c])))))))))))))

/-- Checked nominal proof certificate identified upstream as
`nb057_direct_function_variable_occurrence`.
-/
@[expose]
noncomputable def nb057DirectFunctionVariableOccurrence (f : Var) (a : Var)
    (dv_a_f : a ≠ f) :
    TAlphaClass
      [((nb057AlphaDummy125), (nb057AlphaDummy127 f)),
        ((nb057AlphaDummy124), (nb057AlphaDummy126 f)),
        ((nb057AlphaDummy128), (nb057AlphaDummy129 f)),
        ((nb057AlphaDummy046), (nb057AlphaDummy049 f)),
        ((nb057AlphaDummy045), (nb057AlphaDummy048 f)),
        ((nb057AlphaDummy044), (nb057AlphaDummy047 f)),
        ((nb057AlphaDummy050), (nb057AlphaDummy051 f)),
        ((nb057AlphaDummy000), a), ((nb057AlphaDummy001), f),
        ((nb057AlphaDummy002), (nb057AlphaDummy003 f a))]
      (Class.cv (nb057AlphaDummy001)) (Class.cv f) :=
  by
  have freshness0 : (nb057AlphaDummy001) ≠ (nb057AlphaDummy125) :=
    by
    unfold nb057AlphaDummy125
    with_reducible exact (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0212) 1))
  have freshness1 : f ≠ (nb057AlphaDummy127 f) :=
    by
    unfold nb057AlphaDummy127
    with_reducible exact (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0213 f) 1))
  have freshness2 : (nb057AlphaDummy001) ≠ (nb057AlphaDummy124) :=
    by
    unfold nb057AlphaDummy124
    with_reducible exact (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0212) 0))
  have freshness3 : f ≠ (nb057AlphaDummy126 f) :=
    by
    unfold nb057AlphaDummy126
    with_reducible exact (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0213 f) 0))
  have freshness4 : (nb057AlphaDummy001) ≠ (nb057AlphaDummy128) :=
    by
    unfold nb057AlphaDummy128
    with_reducible exact (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0210) 0))
  have freshness5 : f ≠ (nb057AlphaDummy129 f) :=
    by
    unfold nb057AlphaDummy129
    with_reducible exact (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0211 f) 0))
  have freshness6 : (nb057AlphaDummy001) ≠ (nb057AlphaDummy046) :=
    by
    unfold nb057AlphaDummy046
    with_reducible exact (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0206) 2))
  have freshness7 : f ≠ (nb057AlphaDummy049 f) :=
    by
    unfold nb057AlphaDummy049
    with_reducible exact (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0208 f) 2))
  have freshness8 : (nb057AlphaDummy001) ≠ (nb057AlphaDummy045) :=
    by
    unfold nb057AlphaDummy045
    with_reducible exact (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0206) 1))
  have freshness9 : f ≠ (nb057AlphaDummy048 f) :=
    by
    unfold nb057AlphaDummy048
    with_reducible exact (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0208 f) 1))
  have freshness10 : (nb057AlphaDummy001) ≠ (nb057AlphaDummy044) :=
    by
    unfold nb057AlphaDummy044
    with_reducible exact (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0206) 0))
  have freshness11 : f ≠ (nb057AlphaDummy047 f) :=
    by
    unfold nb057AlphaDummy047
    with_reducible exact (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0208 f) 0))
  have freshness12 : (nb057AlphaDummy001) ≠ (nb057AlphaDummy050) :=
    by
    unfold nb057AlphaDummy050
    with_reducible exact (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0207) 0))
  have freshness13 : f ≠ (nb057AlphaDummy051 f) :=
    by
    unfold nb057AlphaDummy051
    with_reducible exact (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0209 f) 0))
  have freshness14 : (nb057AlphaDummy001) ≠ (nb057AlphaDummy000) :=
    by
    unfold nb057AlphaDummy001 nb057AlphaDummy000
    with_reducible exact (freshVar_injective ((∅ : Finset Var)) (by decide))
  have freshness15 : f ≠ a := by exact (Ne.symm dv_a_f)
  with_reducible
    exact
      (TAlphaClass.cv (TAlphaVar.there freshness0 freshness1
          (TAlphaVar.there freshness2 freshness3 (TAlphaVar.there freshness4 freshness5
              (TAlphaVar.there freshness6 freshness7 (TAlphaVar.there freshness8 freshness9
                  (TAlphaVar.there freshness10 freshness11
                    (TAlphaVar.there freshness12 freshness13
                      (TAlphaVar.there freshness14 freshness15 (TAlphaVar.here _ _ _))))))))))

/-- Checked nominal proof certificate identified upstream as `nb057_split_alpha_0053`. -/
@[expose]
noncomputable def nb057SplitAlpha0053 (f : Var) (a : Var) (dv_a_f : a ≠ f) :
    TAlphaWff
      [((nb057AlphaDummy125), (nb057AlphaDummy127 f)),
        ((nb057AlphaDummy124), (nb057AlphaDummy126 f)),
        ((nb057AlphaDummy128), (nb057AlphaDummy129 f)),
        ((nb057AlphaDummy046), (nb057AlphaDummy049 f)),
        ((nb057AlphaDummy045), (nb057AlphaDummy048 f)),
        ((nb057AlphaDummy044), (nb057AlphaDummy047 f)),
        ((nb057AlphaDummy050), (nb057AlphaDummy051 f)),
        ((nb057AlphaDummy000), a), ((nb057AlphaDummy001), f),
        ((nb057AlphaDummy002), (nb057AlphaDummy003 f a))]
      (Wff.imp (Wff.classEq (Class.cv (nb057AlphaDummy128))
          (synCop (Class.cv (nb057AlphaDummy124)) (Class.cv (nb057AlphaDummy125))))
        (Wff.neg (synWbr (Class.cv (nb057AlphaDummy125)) (Class.cv (nb057AlphaDummy001))
            (Class.cv (nb057AlphaDummy124)))))
      (Wff.imp (Wff.classEq (Class.cv (nb057AlphaDummy129 f))
          (synCop (Class.cv (nb057AlphaDummy126 f)) (Class.cv (nb057AlphaDummy127 f))))
        (Wff.neg (synWbr (Class.cv (nb057AlphaDummy127 f)) (Class.cv f)
            (Class.cv (nb057AlphaDummy126 f))))) :=
  (TAlphaWff.imp (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there
          (Ne.symm (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0124) 0)))
          (Ne.symm (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0125 f) 0)))
          (TAlphaVar.there (Ne.symm (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0122) 0)))
            (Ne.symm (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0123 f) 0)))
            (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.neg (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                        (TAlphaWff.ex (TAlphaWff.conj
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb057_support_mem_0126) 1)) (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb057_support_mem_0128 f) 1))
                                  (TAlphaVar.there (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb057_support_mem_0126) 0))
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb057_support_mem_0128 f) 0))
                                    (TAlphaVar.there (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb057_support_mem_0130) 0))
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb057_support_mem_0131 f) 0))
                                      (TAlphaVar.there (Nat.ne_of_lt
        (mem_lt_freshVar (nb057_support_mem_0127) 0)) (Nat.ne_of_lt
        (mem_lt_freshVar (nb057_support_mem_0129 f) 0)) (TAlphaVar.there (freshVar_injective
        (((Class.cv (nb057AlphaDummy001))).fv) (by decide))
        (freshVar_injective (((Class.cv f)).fv) (by decide)) (TAlphaVar.here _ _ _))))))))
                            (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there
                                  (freshVar_injective (((Class.cv (nb057AlphaDummy124))).fv ∪
                                      ((Class.cv (nb057AlphaDummy125))).fv) (by decide))
                                  (freshVar_injective
                                    (((Class.cv (nb057AlphaDummy126 f))).fv ∪
                                      ((Class.cv (nb057AlphaDummy127 f))).fv) (by decide))
                                  (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.ex
                                  (TAlphaWff.neg (nb057SplitAlpha0044 f a)))))))))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                        (TAlphaWff.ex (TAlphaWff.conj
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb057_support_mem_0126) 1)) (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb057_support_mem_0128 f) 1))
                                  (TAlphaVar.there (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb057_support_mem_0126) 0))
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb057_support_mem_0128 f) 0))
                                    (TAlphaVar.there (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb057_support_mem_0130) 0))
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb057_support_mem_0131 f) 0))
                                      (TAlphaVar.there (Nat.ne_of_lt
        (mem_lt_freshVar (nb057_support_mem_0127) 0)) (Nat.ne_of_lt
        (mem_lt_freshVar (nb057_support_mem_0129 f) 0)) (TAlphaVar.there (freshVar_injective
        (((Class.cv (nb057AlphaDummy001))).fv) (by decide))
        (freshVar_injective (((Class.cv f)).fv) (by decide)) (TAlphaVar.here _ _ _))))))))
                            (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there
                                  (freshVar_injective (((Class.cv (nb057AlphaDummy124))).fv ∪
                                      ((Class.cv (nb057AlphaDummy125))).fv) (by decide))
                                  (freshVar_injective
                                    (((Class.cv (nb057AlphaDummy126 f))).fv ∪
                                      ((Class.cv (nb057AlphaDummy127 f))).fv) (by decide))
                                  (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.ex
                                  (TAlphaWff.neg (nb057SplitAlpha0044 f a)))))))))))))
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.neg (TAlphaWff.neg (nb057SplitAlpha0047 f a)))))))))
    (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                  (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb057_support_mem_0164) 1))
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb057_support_mem_0166 f) 1))
                                    (TAlphaVar.there (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb057_support_mem_0164) 0))
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb057_support_mem_0166 f) 0))
                                      (TAlphaVar.there (Nat.ne_of_lt
        (mem_lt_freshVar (nb057_support_mem_0168) 0)) (Nat.ne_of_lt
        (mem_lt_freshVar (nb057_support_mem_0169 f) 0)) (TAlphaVar.there (Nat.ne_of_lt
        (mem_lt_freshVar (nb057_support_mem_0165) 0)) (Nat.ne_of_lt
        (mem_lt_freshVar (nb057_support_mem_0167 f) 0)) (TAlphaVar.here _ _ _)))))))
                              (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there
                                    (freshVar_injective
                                      (((Class.cv (nb057AlphaDummy125))).fv ∪
                                        ((Class.cv (nb057AlphaDummy124))).fv) (by decide))
                                    (freshVar_injective
                                      (((Class.cv (nb057AlphaDummy127 f))).fv ∪
                                        ((Class.cv (nb057AlphaDummy126 f))).fv) (by decide))
                                    (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.ex
                                    (TAlphaWff.neg (nb057SplitAlpha0049 f a)))))))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb057_support_mem_0164) 1))
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb057_support_mem_0166 f) 1))
                                    (TAlphaVar.there (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb057_support_mem_0164) 0))
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb057_support_mem_0166 f) 0))
                                      (TAlphaVar.there (Nat.ne_of_lt
        (mem_lt_freshVar (nb057_support_mem_0168) 0)) (Nat.ne_of_lt
        (mem_lt_freshVar (nb057_support_mem_0169 f) 0)) (TAlphaVar.there (Nat.ne_of_lt
        (mem_lt_freshVar (nb057_support_mem_0165) 0)) (Nat.ne_of_lt
        (mem_lt_freshVar (nb057_support_mem_0167 f) 0)) (TAlphaVar.here _ _ _)))))))
                              (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there
                                    (freshVar_injective
                                      (((Class.cv (nb057AlphaDummy125))).fv ∪
                                        ((Class.cv (nb057AlphaDummy124))).fv) (by decide))
                                    (freshVar_injective
                                      (((Class.cv (nb057AlphaDummy127 f))).fv ∪
                                        ((Class.cv (nb057AlphaDummy126 f))).fv) (by decide))
                                    (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.ex
                                    (TAlphaWff.neg (nb057SplitAlpha0049 f a)))))))))))))
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                  (TAlphaWff.neg (TAlphaWff.neg (nb057SplitAlpha0052 f a))))))))
        (nb057DirectFunctionVariableOccurrence f a dv_a_f))))

/-- Checked nominal proof certificate identified upstream as `nb057_split_alpha_0054`. -/
@[expose]
noncomputable def nb057SplitAlpha0054 (f : Var) (a : Var) :
    TAlphaWff
      [((nb057AlphaDummy218), (nb057AlphaDummy221 f)),
        ((nb057AlphaDummy217), (nb057AlphaDummy220 f)),
        ((nb057AlphaDummy216), (nb057AlphaDummy219 f)),
        ((nb057AlphaDummy214), (nb057AlphaDummy215 f)),
        ((nb057AlphaDummy210), (nb057AlphaDummy212 f)),
        ((nb057AlphaDummy211), (nb057AlphaDummy213 f)),
        ((nb057AlphaDummy203), (nb057AlphaDummy205 f)),
        ((nb057AlphaDummy202), (nb057AlphaDummy204 f)),
        ((nb057AlphaDummy208), (nb057AlphaDummy209 f)),
        ((nb057AlphaDummy206), (nb057AlphaDummy207 f)),
        ((nb057AlphaDummy046), (nb057AlphaDummy049 f)),
        ((nb057AlphaDummy045), (nb057AlphaDummy048 f)),
        ((nb057AlphaDummy044), (nb057AlphaDummy047 f)),
        ((nb057AlphaDummy050), (nb057AlphaDummy051 f)),
        ((nb057AlphaDummy000), a), ((nb057AlphaDummy001), f),
        ((nb057AlphaDummy002), (nb057AlphaDummy003 f a))]
      (Wff.imp (Wff.classEq
          (synCin (Class.cv (nb057AlphaDummy217)) (Class.cv (nb057AlphaDummy218)))
          (synC0)) (Wff.neg (Wff.classEq (Class.cv (nb057AlphaDummy216))
            (synCun (Class.cv (nb057AlphaDummy217)) (Class.cv (nb057AlphaDummy218))))))
      (Wff.imp (Wff.classEq (synCin (Class.cv (nb057AlphaDummy220 f))
            (Class.cv (nb057AlphaDummy221 f))) (synC0)) (Wff.neg
          (Wff.classEq (Class.cv (nb057AlphaDummy219 f))
            (synCun (Class.cv (nb057AlphaDummy220 f))
              (Class.cv (nb057AlphaDummy221 f)))))) :=
  (TAlphaWff.imp (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.neg (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0228) 0))
                          (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0229 f) 0))
                          (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0226) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0227 f) 0))
                            (TAlphaVar.there (freshVar_injective
                                (((Class.cv (nb057AlphaDummy210))).fv ∪ ((synC1c)).fv)
                                (by decide)) (freshVar_injective
                                (((Class.cv (nb057AlphaDummy212 f))).fv ∪ ((synC1c)).fv)
                                (by decide)) (TAlphaVar.here _ _ _))))))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0232) 0))
                          (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0233 f) 0))
                          (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0230) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0231 f) 0))
                            (TAlphaVar.here _ _ _)))))))))
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.neg (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0228) 0))
                          (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0229 f) 0))
                          (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0226) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0227 f) 0))
                            (TAlphaVar.there (freshVar_injective
                                (((Class.cv (nb057AlphaDummy210))).fv ∪ ((synC1c)).fv)
                                (by decide)) (freshVar_injective
                                (((Class.cv (nb057AlphaDummy212 f))).fv ∪ ((synC1c)).fv)
                                (by decide)) (TAlphaVar.here _ _ _))))))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0232) 0))
                          (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0233 f) 0))
                          (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0230) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0231 f) 0))
                            (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.reflOfClosed
        [((nb057AlphaDummy218), (nb057AlphaDummy221 f)),
          ((nb057AlphaDummy217), (nb057AlphaDummy220 f)),
          ((nb057AlphaDummy216), (nb057AlphaDummy219 f)),
          ((nb057AlphaDummy214), (nb057AlphaDummy215 f)),
          ((nb057AlphaDummy210), (nb057AlphaDummy212 f)),
          ((nb057AlphaDummy211), (nb057AlphaDummy213 f)),
          ((nb057AlphaDummy203), (nb057AlphaDummy205 f)),
          ((nb057AlphaDummy202), (nb057AlphaDummy204 f)),
          ((nb057AlphaDummy208), (nb057AlphaDummy209 f)),
          ((nb057AlphaDummy206), (nb057AlphaDummy207 f)),
          ((nb057AlphaDummy046), (nb057AlphaDummy049 f)),
          ((nb057AlphaDummy045), (nb057AlphaDummy048 f)),
          ((nb057AlphaDummy044), (nb057AlphaDummy047 f)),
          ((nb057AlphaDummy050), (nb057AlphaDummy051 f)),
          ((nb057AlphaDummy000), a), ((nb057AlphaDummy001), f),
          ((nb057AlphaDummy002), (nb057AlphaDummy003 f a))]
        (synC0) (by simp only [fv_syn_c0]))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv
          (TAlphaVar.there
            (freshVar_injective (((Class.cv (nb057AlphaDummy210))).fv ∪ ((synC1c)).fv)
              (by decide)) (freshVar_injective
              (((Class.cv (nb057AlphaDummy212 f))).fv ∪ ((synC1c)).fv) (by decide))
            (TAlphaVar.there (freshVar_injective
                (((Class.cv (nb057AlphaDummy210))).fv ∪ ((synC1c)).fv) (by decide))
              (freshVar_injective
                (((Class.cv (nb057AlphaDummy212 f))).fv ∪ ((synC1c)).fv) (by decide))
              (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                  (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0236) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0237 f) 0))
                            (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0234) 0))
                              (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0235 f) 0))
                              (TAlphaVar.there (freshVar_injective
                                  (((Class.cv (nb057AlphaDummy210))).fv ∪ ((synC1c)).fv)
                                  (by decide)) (freshVar_injective
                                  (((Class.cv (nb057AlphaDummy212 f))).fv ∪ ((synC1c)).fv)
                                  (by decide)) (TAlphaVar.here _ _ _))))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0236) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0237 f) 0))
                            (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0234) 0))
                              (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0235 f) 0))
                              (TAlphaVar.there (freshVar_injective
                                  (((Class.cv (nb057AlphaDummy210))).fv ∪ ((synC1c)).fv)
                                  (by decide)) (freshVar_injective
                                  (((Class.cv (nb057AlphaDummy212 f))).fv ∪ ((synC1c)).fv)
                                  (by decide)) (TAlphaVar.here _ _ _))))))))))
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                  (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0240) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0241 f) 0))
                            (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0238) 0))
                              (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0239 f) 0))
                              (TAlphaVar.here _ _ _)))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0240) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0241 f) 0))
                            (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0238) 0))
                              (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0239 f) 0))
                              (TAlphaVar.here _ _ _)))))))))))))))

/-- Checked nominal proof certificate identified upstream as `nb057_split_alpha_0055`. -/
@[expose]
noncomputable def nb057SplitAlpha0055 (f : Var) (a : Var) :
    TAlphaWff
      [((nb057AlphaDummy203), (nb057AlphaDummy205 f)),
        ((nb057AlphaDummy202), (nb057AlphaDummy204 f)),
        ((nb057AlphaDummy208), (nb057AlphaDummy209 f)),
        ((nb057AlphaDummy206), (nb057AlphaDummy207 f)),
        ((nb057AlphaDummy046), (nb057AlphaDummy049 f)),
        ((nb057AlphaDummy045), (nb057AlphaDummy048 f)),
        ((nb057AlphaDummy044), (nb057AlphaDummy047 f)),
        ((nb057AlphaDummy050), (nb057AlphaDummy051 f)),
        ((nb057AlphaDummy000), a), ((nb057AlphaDummy001), f),
        ((nb057AlphaDummy002), (nb057AlphaDummy003 f a))]
      (Wff.classEq (Class.cv (nb057AlphaDummy202))
        (synCphi (Class.cv (nb057AlphaDummy203))))
      (Wff.classEq (Class.cv (nb057AlphaDummy204 f))
        (synCphi (Class.cv (nb057AlphaDummy205 f)))) :=
  (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective
          (((Class.cv (nb057AlphaDummy046))).fv ∪ ((Class.cv (nb057AlphaDummy045))).fv)
          (by decide)) (freshVar_injective (((Class.cv (nb057AlphaDummy049 f))).fv ∪
            ((Class.cv (nb057AlphaDummy048 f))).fv) (by decide)) (TAlphaVar.here _ _ _)))
    (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
          (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
              (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0220) 0))
                (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0221 f) 0)) (TAlphaVar.there
                  (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0220) 1))
                  (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0221 f) 1))
                  (TAlphaVar.here _ _ _))))) (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there
                (freshVar_injective (((Class.cv (nb057AlphaDummy203))).fv) (by decide))
                (freshVar_injective (((Class.cv (nb057AlphaDummy205 f))).fv) (by decide))
                (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp (TAlphaWff.neg
                  (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                      (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb057_support_mem_0224) 1)) (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb057_support_mem_0225 f) 1))
                                  (TAlphaVar.there (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb057_support_mem_0224) 0))
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb057_support_mem_0225 f) 0))
                                    (TAlphaVar.there (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb057_support_mem_0222) 0))
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb057_support_mem_0223 f) 0))
                                      (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
                                (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                  (TAlphaClass.reflOfClosed
                                    [((nb057AlphaDummy218), (nb057AlphaDummy221 f)),
                                      ((nb057AlphaDummy217), (nb057AlphaDummy220 f)),
                                      ((nb057AlphaDummy216), (nb057AlphaDummy219 f)),
                                      ((nb057AlphaDummy214), (nb057AlphaDummy215 f)),
                                      ((nb057AlphaDummy210), (nb057AlphaDummy212 f)),
                                      ((nb057AlphaDummy211), (nb057AlphaDummy213 f)),
                                      ((nb057AlphaDummy203), (nb057AlphaDummy205 f)),
                                      ((nb057AlphaDummy202), (nb057AlphaDummy204 f)),
                                      ((nb057AlphaDummy208), (nb057AlphaDummy209 f)),
                                      ((nb057AlphaDummy206), (nb057AlphaDummy207 f)),
                                      ((nb057AlphaDummy046), (nb057AlphaDummy049 f)),
                                      ((nb057AlphaDummy045), (nb057AlphaDummy048 f)),
                                      ((nb057AlphaDummy044), (nb057AlphaDummy047 f)),
                                      ((nb057AlphaDummy050), (nb057AlphaDummy051 f)),
                                      ((nb057AlphaDummy000), a),
                                      ((nb057AlphaDummy001), f), ((nb057AlphaDummy002),
                                        (nb057AlphaDummy003 f a))]
                                    (synC1c) (by simp only [fv_syn_c1c])))
                                (TAlphaWff.neg (nb057SplitAlpha0054 f a))))))))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there
                          (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0222) 0))
                          (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0223 f) 0))
                          (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
                        [((nb057AlphaDummy214), (nb057AlphaDummy215 f)),
                          ((nb057AlphaDummy210), (nb057AlphaDummy212 f)),
                          ((nb057AlphaDummy211), (nb057AlphaDummy213 f)),
                          ((nb057AlphaDummy203), (nb057AlphaDummy205 f)),
                          ((nb057AlphaDummy202), (nb057AlphaDummy204 f)),
                          ((nb057AlphaDummy208), (nb057AlphaDummy209 f)),
                          ((nb057AlphaDummy206), (nb057AlphaDummy207 f)),
                          ((nb057AlphaDummy046), (nb057AlphaDummy049 f)),
                          ((nb057AlphaDummy045), (nb057AlphaDummy048 f)),
                          ((nb057AlphaDummy044), (nb057AlphaDummy047 f)),
                          ((nb057AlphaDummy050), (nb057AlphaDummy051 f)),
                          ((nb057AlphaDummy000), a), ((nb057AlphaDummy001), f),
                          ((nb057AlphaDummy002), (nb057AlphaDummy003 f a))]
                        (synCnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
                  (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                      (TAlphaVar.there
                        (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0222) 0))
                        (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0223 f) 0))
                        (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.classMem
                      (TAlphaClass.cv (TAlphaVar.there
                          (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0222) 0))
                          (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0223 f) 0))
                          (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
                        [((nb057AlphaDummy214), (nb057AlphaDummy215 f)),
                          ((nb057AlphaDummy210), (nb057AlphaDummy212 f)),
                          ((nb057AlphaDummy211), (nb057AlphaDummy213 f)),
                          ((nb057AlphaDummy203), (nb057AlphaDummy205 f)),
                          ((nb057AlphaDummy202), (nb057AlphaDummy204 f)),
                          ((nb057AlphaDummy208), (nb057AlphaDummy209 f)),
                          ((nb057AlphaDummy206), (nb057AlphaDummy207 f)),
                          ((nb057AlphaDummy046), (nb057AlphaDummy049 f)),
                          ((nb057AlphaDummy045), (nb057AlphaDummy048 f)),
                          ((nb057AlphaDummy044), (nb057AlphaDummy047 f)),
                          ((nb057AlphaDummy050), (nb057AlphaDummy051 f)),
                          ((nb057AlphaDummy000), a), ((nb057AlphaDummy001), f),
                          ((nb057AlphaDummy002), (nb057AlphaDummy003 f a))]
                        (synCnnc) (by simp only [fv_syn_cnnc]))))))))))))

/-- Checked nominal proof certificate identified upstream as `nb057_split_alpha_0056`. -/
@[expose]
noncomputable def nb057SplitAlpha0056 (f : Var) (a : Var) :
    TAlphaWff
      [((nb057AlphaDummy218), (nb057AlphaDummy221 f)),
        ((nb057AlphaDummy217), (nb057AlphaDummy220 f)),
        ((nb057AlphaDummy216), (nb057AlphaDummy219 f)),
        ((nb057AlphaDummy214), (nb057AlphaDummy215 f)),
        ((nb057AlphaDummy210), (nb057AlphaDummy212 f)),
        ((nb057AlphaDummy211), (nb057AlphaDummy213 f)),
        ((nb057AlphaDummy236), (nb057AlphaDummy237 f)),
        ((nb057AlphaDummy234), (nb057AlphaDummy235 f)),
        ((nb057AlphaDummy203), (nb057AlphaDummy205 f)),
        ((nb057AlphaDummy202), (nb057AlphaDummy204 f)),
        ((nb057AlphaDummy232), (nb057AlphaDummy233 f)),
        ((nb057AlphaDummy206), (nb057AlphaDummy207 f)),
        ((nb057AlphaDummy046), (nb057AlphaDummy049 f)),
        ((nb057AlphaDummy045), (nb057AlphaDummy048 f)),
        ((nb057AlphaDummy044), (nb057AlphaDummy047 f)),
        ((nb057AlphaDummy050), (nb057AlphaDummy051 f)),
        ((nb057AlphaDummy000), a), ((nb057AlphaDummy001), f),
        ((nb057AlphaDummy002), (nb057AlphaDummy003 f a))]
      (Wff.imp (Wff.classEq
          (synCin (Class.cv (nb057AlphaDummy217)) (Class.cv (nb057AlphaDummy218)))
          (synC0)) (Wff.neg (Wff.classEq (Class.cv (nb057AlphaDummy216))
            (synCun (Class.cv (nb057AlphaDummy217)) (Class.cv (nb057AlphaDummy218))))))
      (Wff.imp (Wff.classEq (synCin (Class.cv (nb057AlphaDummy220 f))
            (Class.cv (nb057AlphaDummy221 f))) (synC0)) (Wff.neg
          (Wff.classEq (Class.cv (nb057AlphaDummy219 f))
            (synCun (Class.cv (nb057AlphaDummy220 f))
              (Class.cv (nb057AlphaDummy221 f)))))) :=
  (TAlphaWff.imp (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.neg (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0228) 0))
                          (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0229 f) 0))
                          (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0226) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0227 f) 0))
                            (TAlphaVar.there (freshVar_injective
                                (((Class.cv (nb057AlphaDummy210))).fv ∪ ((synC1c)).fv)
                                (by decide)) (freshVar_injective
                                (((Class.cv (nb057AlphaDummy212 f))).fv ∪ ((synC1c)).fv)
                                (by decide)) (TAlphaVar.here _ _ _))))))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0232) 0))
                          (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0233 f) 0))
                          (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0230) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0231 f) 0))
                            (TAlphaVar.here _ _ _)))))))))
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.neg (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0228) 0))
                          (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0229 f) 0))
                          (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0226) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0227 f) 0))
                            (TAlphaVar.there (freshVar_injective
                                (((Class.cv (nb057AlphaDummy210))).fv ∪ ((synC1c)).fv)
                                (by decide)) (freshVar_injective
                                (((Class.cv (nb057AlphaDummy212 f))).fv ∪ ((synC1c)).fv)
                                (by decide)) (TAlphaVar.here _ _ _))))))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0232) 0))
                          (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0233 f) 0))
                          (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0230) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0231 f) 0))
                            (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.reflOfClosed
        [((nb057AlphaDummy218), (nb057AlphaDummy221 f)),
          ((nb057AlphaDummy217), (nb057AlphaDummy220 f)),
          ((nb057AlphaDummy216), (nb057AlphaDummy219 f)),
          ((nb057AlphaDummy214), (nb057AlphaDummy215 f)),
          ((nb057AlphaDummy210), (nb057AlphaDummy212 f)),
          ((nb057AlphaDummy211), (nb057AlphaDummy213 f)),
          ((nb057AlphaDummy236), (nb057AlphaDummy237 f)),
          ((nb057AlphaDummy234), (nb057AlphaDummy235 f)),
          ((nb057AlphaDummy203), (nb057AlphaDummy205 f)),
          ((nb057AlphaDummy202), (nb057AlphaDummy204 f)),
          ((nb057AlphaDummy232), (nb057AlphaDummy233 f)),
          ((nb057AlphaDummy206), (nb057AlphaDummy207 f)),
          ((nb057AlphaDummy046), (nb057AlphaDummy049 f)),
          ((nb057AlphaDummy045), (nb057AlphaDummy048 f)),
          ((nb057AlphaDummy044), (nb057AlphaDummy047 f)),
          ((nb057AlphaDummy050), (nb057AlphaDummy051 f)),
          ((nb057AlphaDummy000), a), ((nb057AlphaDummy001), f),
          ((nb057AlphaDummy002), (nb057AlphaDummy003 f a))]
        (synC0) (by simp only [fv_syn_c0]))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv
          (TAlphaVar.there
            (freshVar_injective (((Class.cv (nb057AlphaDummy210))).fv ∪ ((synC1c)).fv)
              (by decide)) (freshVar_injective
              (((Class.cv (nb057AlphaDummy212 f))).fv ∪ ((synC1c)).fv) (by decide))
            (TAlphaVar.there (freshVar_injective
                (((Class.cv (nb057AlphaDummy210))).fv ∪ ((synC1c)).fv) (by decide))
              (freshVar_injective
                (((Class.cv (nb057AlphaDummy212 f))).fv ∪ ((synC1c)).fv) (by decide))
              (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                  (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0236) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0237 f) 0))
                            (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0234) 0))
                              (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0235 f) 0))
                              (TAlphaVar.there (freshVar_injective
                                  (((Class.cv (nb057AlphaDummy210))).fv ∪ ((synC1c)).fv)
                                  (by decide)) (freshVar_injective
                                  (((Class.cv (nb057AlphaDummy212 f))).fv ∪ ((synC1c)).fv)
                                  (by decide)) (TAlphaVar.here _ _ _))))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0236) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0237 f) 0))
                            (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0234) 0))
                              (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0235 f) 0))
                              (TAlphaVar.there (freshVar_injective
                                  (((Class.cv (nb057AlphaDummy210))).fv ∪ ((synC1c)).fv)
                                  (by decide)) (freshVar_injective
                                  (((Class.cv (nb057AlphaDummy212 f))).fv ∪ ((synC1c)).fv)
                                  (by decide)) (TAlphaVar.here _ _ _))))))))))
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                  (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0240) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0241 f) 0))
                            (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0238) 0))
                              (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0239 f) 0))
                              (TAlphaVar.here _ _ _)))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0240) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0241 f) 0))
                            (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0238) 0))
                              (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0239 f) 0))
                              (TAlphaVar.here _ _ _)))))))))))))))

end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired

end

/-! Certificates from `NAR4C057C001Part023`. -/


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

/-- Checked nominal proof certificate identified upstream as `nb057_split_alpha_0057`. -/
@[expose]
noncomputable def nb057SplitAlpha0057 (f : Var) (a : Var) :
    TAlphaWff
      [((nb057AlphaDummy210), (nb057AlphaDummy212 f)),
        ((nb057AlphaDummy211), (nb057AlphaDummy213 f)),
        ((nb057AlphaDummy236), (nb057AlphaDummy237 f)),
        ((nb057AlphaDummy234), (nb057AlphaDummy235 f)),
        ((nb057AlphaDummy203), (nb057AlphaDummy205 f)),
        ((nb057AlphaDummy202), (nb057AlphaDummy204 f)),
        ((nb057AlphaDummy232), (nb057AlphaDummy233 f)),
        ((nb057AlphaDummy206), (nb057AlphaDummy207 f)),
        ((nb057AlphaDummy046), (nb057AlphaDummy049 f)),
        ((nb057AlphaDummy045), (nb057AlphaDummy048 f)),
        ((nb057AlphaDummy044), (nb057AlphaDummy047 f)),
        ((nb057AlphaDummy050), (nb057AlphaDummy051 f)),
        ((nb057AlphaDummy000), a), ((nb057AlphaDummy001), f),
        ((nb057AlphaDummy002), (nb057AlphaDummy003 f a))]
      (Wff.imp (Wff.classMem (Class.cv (nb057AlphaDummy210))
          (Class.cv (nb057AlphaDummy203))) (Wff.neg
          (Wff.classEq (Class.cv (nb057AlphaDummy211))
            (synCif (Wff.classMem (Class.cv (nb057AlphaDummy210)) (synCnnc))
              (synCplc (Class.cv (nb057AlphaDummy210)) (synC1c))
              (Class.cv (nb057AlphaDummy210))))))
      (Wff.imp (Wff.classMem (Class.cv (nb057AlphaDummy212 f))
          (Class.cv (nb057AlphaDummy205 f))) (Wff.neg
          (Wff.classEq (Class.cv (nb057AlphaDummy213 f))
            (synCif (Wff.classMem (Class.cv (nb057AlphaDummy212 f)) (synCnnc))
              (synCplc (Class.cv (nb057AlphaDummy212 f)) (synC1c))
              (Class.cv (nb057AlphaDummy212 f)))))) :=
  (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0220) 0))
          (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0221 f) 0))
          (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0220) 1))
            (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0221 f) 1))
            (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0250) 0))
              (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0251 f) 0))
              (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0248) 0))
                (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0249 f) 0))
                (TAlphaVar.here _ _ _))))))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv
          (TAlphaVar.there
            (freshVar_injective (((Class.cv (nb057AlphaDummy203))).fv) (by decide))
            (freshVar_injective (((Class.cv (nb057AlphaDummy205 f))).fv) (by decide))
            (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp (TAlphaWff.neg
              (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                  (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                          (TAlphaClass.cv (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0224) 1))
                              (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0225 f) 1))
                              (TAlphaVar.there (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb057_support_mem_0224) 0)) (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb057_support_mem_0225 f) 0))
                                (TAlphaVar.there (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb057_support_mem_0222) 0)) (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb057_support_mem_0223 f) 0))
                                  (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.reflOfClosed
                                [((nb057AlphaDummy218), (nb057AlphaDummy221 f)),
                                  ((nb057AlphaDummy217), (nb057AlphaDummy220 f)),
                                  ((nb057AlphaDummy216), (nb057AlphaDummy219 f)),
                                  ((nb057AlphaDummy214), (nb057AlphaDummy215 f)),
                                  ((nb057AlphaDummy210), (nb057AlphaDummy212 f)),
                                  ((nb057AlphaDummy211), (nb057AlphaDummy213 f)),
                                  ((nb057AlphaDummy236), (nb057AlphaDummy237 f)),
                                  ((nb057AlphaDummy234), (nb057AlphaDummy235 f)),
                                  ((nb057AlphaDummy203), (nb057AlphaDummy205 f)),
                                  ((nb057AlphaDummy202), (nb057AlphaDummy204 f)),
                                  ((nb057AlphaDummy232), (nb057AlphaDummy233 f)),
                                  ((nb057AlphaDummy206), (nb057AlphaDummy207 f)),
                                  ((nb057AlphaDummy046), (nb057AlphaDummy049 f)),
                                  ((nb057AlphaDummy045), (nb057AlphaDummy048 f)),
                                  ((nb057AlphaDummy044), (nb057AlphaDummy047 f)),
                                  ((nb057AlphaDummy050), (nb057AlphaDummy051 f)),
                                  ((nb057AlphaDummy000), a), ((nb057AlphaDummy001), f),
                                  ((nb057AlphaDummy002), (nb057AlphaDummy003 f a))]
                                (synC1c) (by simp only [fv_syn_c1c])))
                            (TAlphaWff.neg (nb057SplitAlpha0056 f a))))))))
                (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there
                      (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0222) 0))
                      (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0223 f) 0))
                      (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
                    [((nb057AlphaDummy214), (nb057AlphaDummy215 f)),
                      ((nb057AlphaDummy210), (nb057AlphaDummy212 f)),
                      ((nb057AlphaDummy211), (nb057AlphaDummy213 f)),
                      ((nb057AlphaDummy236), (nb057AlphaDummy237 f)),
                      ((nb057AlphaDummy234), (nb057AlphaDummy235 f)),
                      ((nb057AlphaDummy203), (nb057AlphaDummy205 f)),
                      ((nb057AlphaDummy202), (nb057AlphaDummy204 f)),
                      ((nb057AlphaDummy232), (nb057AlphaDummy233 f)),
                      ((nb057AlphaDummy206), (nb057AlphaDummy207 f)),
                      ((nb057AlphaDummy046), (nb057AlphaDummy049 f)),
                      ((nb057AlphaDummy045), (nb057AlphaDummy048 f)),
                      ((nb057AlphaDummy044), (nb057AlphaDummy047 f)),
                      ((nb057AlphaDummy050), (nb057AlphaDummy051 f)),
                      ((nb057AlphaDummy000), a), ((nb057AlphaDummy001), f),
                      ((nb057AlphaDummy002), (nb057AlphaDummy003 f a))]
                    (synCnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                  (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0222) 0))
                    (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0223 f) 0))
                    (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv
                    (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0222) 0))
                      (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0223 f) 0))
                      (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
                    [((nb057AlphaDummy214), (nb057AlphaDummy215 f)),
                      ((nb057AlphaDummy210), (nb057AlphaDummy212 f)),
                      ((nb057AlphaDummy211), (nb057AlphaDummy213 f)),
                      ((nb057AlphaDummy236), (nb057AlphaDummy237 f)),
                      ((nb057AlphaDummy234), (nb057AlphaDummy235 f)),
                      ((nb057AlphaDummy203), (nb057AlphaDummy205 f)),
                      ((nb057AlphaDummy202), (nb057AlphaDummy204 f)),
                      ((nb057AlphaDummy232), (nb057AlphaDummy233 f)),
                      ((nb057AlphaDummy206), (nb057AlphaDummy207 f)),
                      ((nb057AlphaDummy046), (nb057AlphaDummy049 f)),
                      ((nb057AlphaDummy045), (nb057AlphaDummy048 f)),
                      ((nb057AlphaDummy044), (nb057AlphaDummy047 f)),
                      ((nb057AlphaDummy050), (nb057AlphaDummy051 f)),
                      ((nb057AlphaDummy000), a), ((nb057AlphaDummy001), f),
                      ((nb057AlphaDummy002), (nb057AlphaDummy003 f a))]
                    (synCnnc) (by simp only [fv_syn_cnnc]))))))))))

/-- Checked nominal proof certificate identified upstream as `nb057_split_alpha_0058`. -/
@[expose]
noncomputable def nb057SplitAlpha0058 (f : Var) (a : Var) :
    TAlphaWff
      [((nb057AlphaDummy232), (nb057AlphaDummy233 f)),
        ((nb057AlphaDummy206), (nb057AlphaDummy207 f)),
        ((nb057AlphaDummy046), (nb057AlphaDummy049 f)),
        ((nb057AlphaDummy045), (nb057AlphaDummy048 f)),
        ((nb057AlphaDummy044), (nb057AlphaDummy047 f)),
        ((nb057AlphaDummy050), (nb057AlphaDummy051 f)),
        ((nb057AlphaDummy000), a), ((nb057AlphaDummy001), f),
        ((nb057AlphaDummy002), (nb057AlphaDummy003 f a))]
      (Wff.imp (Wff.classMem (Class.cv (nb057AlphaDummy232))
          (Class.cab (nb057AlphaDummy202)
            (synWrex (nb057AlphaDummy203) (Class.cv (nb057AlphaDummy045))
              (Wff.classEq (Class.cv (nb057AlphaDummy202))
                (synCun (synCphi (Class.cv (nb057AlphaDummy203))) (synCsn (synC0c)))))))
        (Wff.neg (Wff.classMem (Class.cv (nb057AlphaDummy232))
            (Class.cab (nb057AlphaDummy202)
              (synWrex (nb057AlphaDummy203) (Class.cv (nb057AlphaDummy045))
                (Wff.classEq (Class.cv (nb057AlphaDummy202))
                  (synCun (synCphi (Class.cv (nb057AlphaDummy203)))
                    (synCsn (synC0c)))))))))
      (Wff.imp (Wff.classMem (Class.cv (nb057AlphaDummy233 f))
          (Class.cab (nb057AlphaDummy204 f)
            (synWrex (nb057AlphaDummy205 f) (Class.cv (nb057AlphaDummy048 f))
              (Wff.classEq (Class.cv (nb057AlphaDummy204 f))
                (synCun (synCphi (Class.cv (nb057AlphaDummy205 f)))
                  (synCsn (synC0c))))))) (Wff.neg
          (Wff.classMem (Class.cv (nb057AlphaDummy233 f))
            (Class.cab (nb057AlphaDummy204 f)
              (synWrex (nb057AlphaDummy205 f) (Class.cv (nb057AlphaDummy048 f))
                (Wff.classEq (Class.cv (nb057AlphaDummy204 f))
                  (synCun (synCphi (Class.cv (nb057AlphaDummy205 f)))
                    (synCsn (synC0c))))))))) :=
  (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.ex (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0242) 1))
                  (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0244 f) 1)) (TAlphaVar.there
                    (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0242) 0))
                    (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0244 f) 0))
                    (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0246) 0))
                      (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0247 f) 0))
                      (TAlphaVar.there
                        (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0243) 0))
                        (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0245 f) 0))
                        (TAlphaVar.there (freshVar_injective
                            (((Class.cv (nb057AlphaDummy001))).fv ∪
                              ((synCcnv (Class.cv (nb057AlphaDummy001)))).fv) (by decide))
                          (freshVar_injective (((Class.cv f)).fv ∪ ((synCcnv (Class.cv f))).fv)
                            (by decide)) (TAlphaVar.here _ _ _)))))))) (TAlphaWff.classEq
              (TAlphaClass.cv (TAlphaVar.there (freshVar_injective
                    (((Class.cv (nb057AlphaDummy046))).fv ∪
                      ((Class.cv (nb057AlphaDummy045))).fv) (by decide)) (freshVar_injective
                    (((Class.cv (nb057AlphaDummy049 f))).fv ∪
                      ((Class.cv (nb057AlphaDummy048 f))).fv) (by decide))
                  (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                        (TAlphaWff.neg (TAlphaWff.conj
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cab (TAlphaWff.ex
                                  (TAlphaWff.neg (nb057SplitAlpha0057 f a)))))
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cab (TAlphaWff.ex
                                  (TAlphaWff.neg (nb057SplitAlpha0057 f a)))))))))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                      (TAlphaClass.reflOfClosed
                        [((nb057AlphaDummy234), (nb057AlphaDummy235 f)),
                          ((nb057AlphaDummy203), (nb057AlphaDummy205 f)),
                          ((nb057AlphaDummy202), (nb057AlphaDummy204 f)),
                          ((nb057AlphaDummy232), (nb057AlphaDummy233 f)),
                          ((nb057AlphaDummy206), (nb057AlphaDummy207 f)),
                          ((nb057AlphaDummy046), (nb057AlphaDummy049 f)),
                          ((nb057AlphaDummy045), (nb057AlphaDummy048 f)),
                          ((nb057AlphaDummy044), (nb057AlphaDummy047 f)),
                          ((nb057AlphaDummy050), (nb057AlphaDummy051 f)),
                          ((nb057AlphaDummy000), a), ((nb057AlphaDummy001), f),
                          ((nb057AlphaDummy002), (nb057AlphaDummy003 f a))]
                        (synCcompl (synCsn (synC0c)))
                        (by simp only [fv_syn_ccompl, fv_syn_csn, fv_syn_c0c])))))))))))
    (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
          (TAlphaWff.ex (TAlphaWff.conj
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                  (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0242) 1))
                    (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0244 f) 1))
                    (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0242) 0))
                      (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0244 f) 0))
                      (TAlphaVar.there
                        (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0246) 0))
                        (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0247 f) 0))
                        (TAlphaVar.there
                          (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0243) 0))
                          (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0245 f) 0))
                          (TAlphaVar.there (freshVar_injective
                              (((Class.cv (nb057AlphaDummy001))).fv ∪
                                ((synCcnv (Class.cv (nb057AlphaDummy001)))).fv) (by decide))
                            (freshVar_injective
                              (((Class.cv f)).fv ∪ ((synCcnv (Class.cv f))).fv) (by decide))
                            (TAlphaVar.here _ _ _)))))))) (TAlphaWff.classEq (TAlphaClass.cv
                  (TAlphaVar.there (freshVar_injective
                      (((Class.cv (nb057AlphaDummy046))).fv ∪
                        ((Class.cv (nb057AlphaDummy045))).fv) (by decide))
                    (freshVar_injective (((Class.cv (nb057AlphaDummy049 f))).fv ∪
                        ((Class.cv (nb057AlphaDummy048 f))).fv) (by decide))
                    (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cab (TAlphaWff.ex
                                    (TAlphaWff.neg (nb057SplitAlpha0057 f a)))))
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cab (TAlphaWff.ex
                                    (TAlphaWff.neg (nb057SplitAlpha0057 f a)))))))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.reflOfClosed
                          [((nb057AlphaDummy234), (nb057AlphaDummy235 f)),
                            ((nb057AlphaDummy203), (nb057AlphaDummy205 f)),
                            ((nb057AlphaDummy202), (nb057AlphaDummy204 f)),
                            ((nb057AlphaDummy232), (nb057AlphaDummy233 f)),
                            ((nb057AlphaDummy206), (nb057AlphaDummy207 f)),
                            ((nb057AlphaDummy046), (nb057AlphaDummy049 f)),
                            ((nb057AlphaDummy045), (nb057AlphaDummy048 f)),
                            ((nb057AlphaDummy044), (nb057AlphaDummy047 f)),
                            ((nb057AlphaDummy050), (nb057AlphaDummy051 f)),
                            ((nb057AlphaDummy000), a), ((nb057AlphaDummy001), f),
                            ((nb057AlphaDummy002), (nb057AlphaDummy003 f a))]
                          (synCcompl (synCsn (synC0c))) (by
                            simp only [fv_syn_ccompl, fv_syn_csn, fv_syn_c0c])))))))))))))

/-- Checked nominal proof certificate identified upstream as
`nb057_direct_composition_variable_occurrence`.
-/
@[expose]
noncomputable def nb057DirectCompositionVariableOccurrence (f : Var) (a : Var)
    (dv_a_f : a ≠ f) :
    TAlphaClass
      [((nb057AlphaDummy046), (nb057AlphaDummy049 f)),
        ((nb057AlphaDummy045), (nb057AlphaDummy048 f)),
        ((nb057AlphaDummy044), (nb057AlphaDummy047 f)),
        ((nb057AlphaDummy050), (nb057AlphaDummy051 f)),
        ((nb057AlphaDummy000), a), ((nb057AlphaDummy001), f),
        ((nb057AlphaDummy002), (nb057AlphaDummy003 f a))]
      (Class.cv (nb057AlphaDummy001)) (Class.cv f) :=
  by
  have freshness0 : (nb057AlphaDummy001) ≠ (nb057AlphaDummy046) :=
    by
    unfold nb057AlphaDummy046
    with_reducible exact (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0206) 2))
  have freshness1 : f ≠ (nb057AlphaDummy049 f) :=
    by
    unfold nb057AlphaDummy049
    with_reducible exact (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0208 f) 2))
  have freshness2 : (nb057AlphaDummy001) ≠ (nb057AlphaDummy045) :=
    by
    unfold nb057AlphaDummy045
    with_reducible exact (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0206) 1))
  have freshness3 : f ≠ (nb057AlphaDummy048 f) :=
    by
    unfold nb057AlphaDummy048
    with_reducible exact (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0208 f) 1))
  have freshness4 : (nb057AlphaDummy001) ≠ (nb057AlphaDummy044) :=
    by
    unfold nb057AlphaDummy044
    with_reducible exact (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0206) 0))
  have freshness5 : f ≠ (nb057AlphaDummy047 f) :=
    by
    unfold nb057AlphaDummy047
    with_reducible exact (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0208 f) 0))
  have freshness6 : (nb057AlphaDummy001) ≠ (nb057AlphaDummy050) :=
    by
    unfold nb057AlphaDummy050
    with_reducible exact (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0207) 0))
  have freshness7 : f ≠ (nb057AlphaDummy051 f) :=
    by
    unfold nb057AlphaDummy051
    with_reducible exact (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0209 f) 0))
  have freshness8 : (nb057AlphaDummy001) ≠ (nb057AlphaDummy000) :=
    by
    unfold nb057AlphaDummy001 nb057AlphaDummy000
    with_reducible exact (freshVar_injective ((∅ : Finset Var)) (by decide))
  have freshness9 : f ≠ a := by exact (Ne.symm dv_a_f)
  with_reducible
    exact
      (TAlphaClass.cv (TAlphaVar.there freshness0 freshness1
          (TAlphaVar.there freshness2 freshness3 (TAlphaVar.there freshness4 freshness5
              (TAlphaVar.there freshness6 freshness7
                (TAlphaVar.there freshness8 freshness9 (TAlphaVar.here _ _ _)))))))

/-- Checked nominal proof certificate identified upstream as `nb057_split_alpha_0059`. -/
@[expose]
noncomputable def nb057SplitAlpha0059 (f : Var) (a : Var) (dv_a_f : a ≠ f) :
    TAlphaWff
      [((nb057AlphaDummy046), (nb057AlphaDummy049 f)),
        ((nb057AlphaDummy045), (nb057AlphaDummy048 f)),
        ((nb057AlphaDummy044), (nb057AlphaDummy047 f)),
        ((nb057AlphaDummy050), (nb057AlphaDummy051 f)),
        ((nb057AlphaDummy000), a), ((nb057AlphaDummy001), f),
        ((nb057AlphaDummy002), (nb057AlphaDummy003 f a))]
      (Wff.imp (synWbr (Class.cv (nb057AlphaDummy044))
          (synCcnv (Class.cv (nb057AlphaDummy001))) (Class.cv (nb057AlphaDummy046)))
        (Wff.neg (synWbr (Class.cv (nb057AlphaDummy046)) (Class.cv (nb057AlphaDummy001))
            (Class.cv (nb057AlphaDummy045)))))
      (Wff.imp (synWbr (Class.cv (nb057AlphaDummy047 f)) (synCcnv (Class.cv f))
          (Class.cv (nb057AlphaDummy049 f))) (Wff.neg
          (synWbr (Class.cv (nb057AlphaDummy049 f)) (Class.cv f)
            (Class.cv (nb057AlphaDummy048 f))))) :=
  (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.neg (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                        (TAlphaWff.ex (TAlphaWff.conj
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb057_support_mem_0084) 1)) (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb057_support_mem_0086 f) 1))
                                  (TAlphaVar.there (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb057_support_mem_0084) 0))
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb057_support_mem_0086 f) 0))
                                    (TAlphaVar.there (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb057_support_mem_0088) 0))
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb057_support_mem_0089 f) 0))
                                      (TAlphaVar.there (Nat.ne_of_lt
        (mem_lt_freshVar (nb057_support_mem_0085) 0)) (Nat.ne_of_lt
        (mem_lt_freshVar (nb057_support_mem_0087 f) 0)) (TAlphaVar.there (freshVar_injective
        (((Class.cv (nb057AlphaDummy001))).fv ∪ ((synCcnv
        (Class.cv (nb057AlphaDummy001)))).fv) (by decide)) (freshVar_injective
        (((Class.cv f)).fv ∪ ((synCcnv (Class.cv f))).fv) (by decide)) (TAlphaVar.there
        (freshVar_injective (((Class.cv (nb057AlphaDummy001))).fv ∪ ((synCcnv (Class.cv
        (nb057AlphaDummy001)))).fv) (by decide)) (freshVar_injective (((Class.cv f)).fv ∪
        ((synCcnv (Class.cv f))).fv) (by decide)) (TAlphaVar.here _ _ _)))))))))
                            (nb057SplitAlpha0039 f a)))))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                        (TAlphaWff.ex (TAlphaWff.conj
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb057_support_mem_0084) 1)) (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb057_support_mem_0086 f) 1))
                                  (TAlphaVar.there (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb057_support_mem_0084) 0))
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb057_support_mem_0086 f) 0))
                                    (TAlphaVar.there (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb057_support_mem_0088) 0))
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb057_support_mem_0089 f) 0))
                                      (TAlphaVar.there (Nat.ne_of_lt
        (mem_lt_freshVar (nb057_support_mem_0085) 0)) (Nat.ne_of_lt
        (mem_lt_freshVar (nb057_support_mem_0087 f) 0)) (TAlphaVar.there (freshVar_injective
        (((Class.cv (nb057AlphaDummy001))).fv ∪ ((synCcnv
        (Class.cv (nb057AlphaDummy001)))).fv) (by decide)) (freshVar_injective
        (((Class.cv f)).fv ∪ ((synCcnv (Class.cv f))).fv) (by decide)) (TAlphaVar.there
        (freshVar_injective (((Class.cv (nb057AlphaDummy001))).fv ∪ ((synCcnv (Class.cv
        (nb057AlphaDummy001)))).fv) (by decide)) (freshVar_injective (((Class.cv f)).fv ∪
        ((synCcnv (Class.cv f))).fv) (by decide)) (TAlphaVar.here _ _ _)))))))))
                            (nb057SplitAlpha0039 f a)))))))))
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.neg (TAlphaWff.neg (nb057SplitAlpha0042 f a))))))))
      (TAlphaClass.cab (TAlphaWff.ex
          (TAlphaWff.ex (TAlphaWff.neg (nb057SplitAlpha0053 f a dv_a_f)))))) (TAlphaWff.neg
      (TAlphaWff.classMem (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                  (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb057_support_mem_0214) 1))
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb057_support_mem_0216 f) 1))
                                    (TAlphaVar.there (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb057_support_mem_0214) 0))
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb057_support_mem_0216 f) 0))
                                      (TAlphaVar.there (Nat.ne_of_lt
        (mem_lt_freshVar (nb057_support_mem_0218) 0)) (Nat.ne_of_lt
        (mem_lt_freshVar (nb057_support_mem_0219 f) 0)) (TAlphaVar.there (Nat.ne_of_lt
        (mem_lt_freshVar (nb057_support_mem_0215) 0)) (Nat.ne_of_lt
        (mem_lt_freshVar (nb057_support_mem_0217 f) 0)) (TAlphaVar.here _ _ _)))))))
                              (nb057SplitAlpha0055 f a)))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cv (TAlphaVar.there (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb057_support_mem_0214) 1))
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb057_support_mem_0216 f) 1))
                                    (TAlphaVar.there (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb057_support_mem_0214) 0))
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb057_support_mem_0216 f) 0))
                                      (TAlphaVar.there (Nat.ne_of_lt
        (mem_lt_freshVar (nb057_support_mem_0218) 0)) (Nat.ne_of_lt
        (mem_lt_freshVar (nb057_support_mem_0219 f) 0)) (TAlphaVar.there (Nat.ne_of_lt
        (mem_lt_freshVar (nb057_support_mem_0215) 0)) (Nat.ne_of_lt
        (mem_lt_freshVar (nb057_support_mem_0217 f) 0)) (TAlphaVar.here _ _ _)))))))
                              (nb057SplitAlpha0055 f a)))))))))
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                  (TAlphaWff.neg (TAlphaWff.neg (nb057SplitAlpha0058 f a))))))))
        (nb057DirectCompositionVariableOccurrence f a dv_a_f))))

/-- Checked nominal proof certificate identified upstream as `nb057_split_alpha_0060`. -/
@[expose]
noncomputable def nb057SplitAlpha0060 (f : Var) (a : Var) :
    TAlphaWff
      [((nb057AlphaDummy258), (nb057AlphaDummy261 f)),
        ((nb057AlphaDummy257), (nb057AlphaDummy260 f)),
        ((nb057AlphaDummy256), (nb057AlphaDummy259 f)),
        ((nb057AlphaDummy254), (nb057AlphaDummy255 f)),
        ((nb057AlphaDummy250), (nb057AlphaDummy252 f)),
        ((nb057AlphaDummy251), (nb057AlphaDummy253 f)),
        ((nb057AlphaDummy243), (nb057AlphaDummy245 f)),
        ((nb057AlphaDummy242), (nb057AlphaDummy244 f)),
        ((nb057AlphaDummy248), (nb057AlphaDummy249 f)),
        ((nb057AlphaDummy246), (nb057AlphaDummy247 f)),
        ((nb057AlphaDummy239), (nb057AlphaDummy241 f)),
        ((nb057AlphaDummy238), (nb057AlphaDummy240 f)),
        ((nb057AlphaDummy000), a), ((nb057AlphaDummy001), f),
        ((nb057AlphaDummy002), (nb057AlphaDummy003 f a))]
      (Wff.imp (Wff.classEq
          (synCin (Class.cv (nb057AlphaDummy257)) (Class.cv (nb057AlphaDummy258)))
          (synC0)) (Wff.neg (Wff.classEq (Class.cv (nb057AlphaDummy256))
            (synCun (Class.cv (nb057AlphaDummy257)) (Class.cv (nb057AlphaDummy258))))))
      (Wff.imp (Wff.classEq (synCin (Class.cv (nb057AlphaDummy260 f))
            (Class.cv (nb057AlphaDummy261 f))) (synC0)) (Wff.neg
          (Wff.classEq (Class.cv (nb057AlphaDummy259 f))
            (synCun (Class.cv (nb057AlphaDummy260 f))
              (Class.cv (nb057AlphaDummy261 f)))))) :=
  (TAlphaWff.imp (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.neg (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0266) 0))
                          (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0267 f) 0))
                          (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0264) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0265 f) 0))
                            (TAlphaVar.there (freshVar_injective
                                (((Class.cv (nb057AlphaDummy250))).fv ∪ ((synC1c)).fv)
                                (by decide)) (freshVar_injective
                                (((Class.cv (nb057AlphaDummy252 f))).fv ∪ ((synC1c)).fv)
                                (by decide)) (TAlphaVar.here _ _ _))))))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0270) 0))
                          (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0271 f) 0))
                          (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0268) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0269 f) 0))
                            (TAlphaVar.here _ _ _)))))))))
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.neg (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0266) 0))
                          (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0267 f) 0))
                          (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0264) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0265 f) 0))
                            (TAlphaVar.there (freshVar_injective
                                (((Class.cv (nb057AlphaDummy250))).fv ∪ ((synC1c)).fv)
                                (by decide)) (freshVar_injective
                                (((Class.cv (nb057AlphaDummy252 f))).fv ∪ ((synC1c)).fv)
                                (by decide)) (TAlphaVar.here _ _ _))))))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0270) 0))
                          (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0271 f) 0))
                          (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0268) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0269 f) 0))
                            (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.reflOfClosed
        [((nb057AlphaDummy258), (nb057AlphaDummy261 f)),
          ((nb057AlphaDummy257), (nb057AlphaDummy260 f)),
          ((nb057AlphaDummy256), (nb057AlphaDummy259 f)),
          ((nb057AlphaDummy254), (nb057AlphaDummy255 f)),
          ((nb057AlphaDummy250), (nb057AlphaDummy252 f)),
          ((nb057AlphaDummy251), (nb057AlphaDummy253 f)),
          ((nb057AlphaDummy243), (nb057AlphaDummy245 f)),
          ((nb057AlphaDummy242), (nb057AlphaDummy244 f)),
          ((nb057AlphaDummy248), (nb057AlphaDummy249 f)),
          ((nb057AlphaDummy246), (nb057AlphaDummy247 f)),
          ((nb057AlphaDummy239), (nb057AlphaDummy241 f)),
          ((nb057AlphaDummy238), (nb057AlphaDummy240 f)),
          ((nb057AlphaDummy000), a), ((nb057AlphaDummy001), f),
          ((nb057AlphaDummy002), (nb057AlphaDummy003 f a))]
        (synC0) (by simp only [fv_syn_c0]))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv
          (TAlphaVar.there
            (freshVar_injective (((Class.cv (nb057AlphaDummy250))).fv ∪ ((synC1c)).fv)
              (by decide)) (freshVar_injective
              (((Class.cv (nb057AlphaDummy252 f))).fv ∪ ((synC1c)).fv) (by decide))
            (TAlphaVar.there (freshVar_injective
                (((Class.cv (nb057AlphaDummy250))).fv ∪ ((synC1c)).fv) (by decide))
              (freshVar_injective
                (((Class.cv (nb057AlphaDummy252 f))).fv ∪ ((synC1c)).fv) (by decide))
              (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                  (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0274) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0275 f) 0))
                            (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0272) 0))
                              (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0273 f) 0))
                              (TAlphaVar.there (freshVar_injective
                                  (((Class.cv (nb057AlphaDummy250))).fv ∪ ((synC1c)).fv)
                                  (by decide)) (freshVar_injective
                                  (((Class.cv (nb057AlphaDummy252 f))).fv ∪ ((synC1c)).fv)
                                  (by decide)) (TAlphaVar.here _ _ _))))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0274) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0275 f) 0))
                            (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0272) 0))
                              (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0273 f) 0))
                              (TAlphaVar.there (freshVar_injective
                                  (((Class.cv (nb057AlphaDummy250))).fv ∪ ((synC1c)).fv)
                                  (by decide)) (freshVar_injective
                                  (((Class.cv (nb057AlphaDummy252 f))).fv ∪ ((synC1c)).fv)
                                  (by decide)) (TAlphaVar.here _ _ _))))))))))
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                  (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0278) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0279 f) 0))
                            (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0276) 0))
                              (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0277 f) 0))
                              (TAlphaVar.here _ _ _)))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0278) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0279 f) 0))
                            (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0276) 0))
                              (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0277 f) 0))
                              (TAlphaVar.here _ _ _)))))))))))))))


end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired

end

/-! Certificates from `NAR4C057C001Part024`. -/


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

/-- Checked nominal proof certificate identified upstream as `nb057_split_alpha_0061`. -/
@[expose]
noncomputable def nb057SplitAlpha0061 (f : Var) (a : Var) :
    TAlphaWff
      [((nb057AlphaDummy243), (nb057AlphaDummy245 f)),
        ((nb057AlphaDummy242), (nb057AlphaDummy244 f)),
        ((nb057AlphaDummy248), (nb057AlphaDummy249 f)),
        ((nb057AlphaDummy246), (nb057AlphaDummy247 f)),
        ((nb057AlphaDummy239), (nb057AlphaDummy241 f)),
        ((nb057AlphaDummy238), (nb057AlphaDummy240 f)),
        ((nb057AlphaDummy000), a), ((nb057AlphaDummy001), f),
        ((nb057AlphaDummy002), (nb057AlphaDummy003 f a))]
      (Wff.imp (Wff.classMem (Class.cv (nb057AlphaDummy243))
          (Class.cv (nb057AlphaDummy239))) (Wff.neg
          (Wff.classEq (Class.cv (nb057AlphaDummy242))
            (synCphi (Class.cv (nb057AlphaDummy243))))))
      (Wff.imp (Wff.classMem (Class.cv (nb057AlphaDummy245 f))
          (Class.cv (nb057AlphaDummy241 f))) (Wff.neg
          (Wff.classEq (Class.cv (nb057AlphaDummy244 f))
            (synCphi (Class.cv (nb057AlphaDummy245 f)))))) :=
  (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0252) 1))
          (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0254 f) 1))
          (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0252) 0))
            (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0254 f) 0))
            (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0256) 0))
              (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0257 f) 0))
              (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0253) 0))
                (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0255 f) 0))
                (TAlphaVar.here _ _ _))))))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv
          (TAlphaVar.there (freshVar_injective (((Class.cv (nb057AlphaDummy239))).fv ∪
                ((Class.cv (nb057AlphaDummy238))).fv) (by decide)) (freshVar_injective
              (((Class.cv (nb057AlphaDummy241 f))).fv ∪
                ((Class.cv (nb057AlphaDummy240 f))).fv) (by decide)) (TAlphaVar.here _ _ _)))
        (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                  (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0258) 0))
                    (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0259 f) 0))
                    (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0258) 1))
                      (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0259 f) 1))
                      (TAlphaVar.here _ _ _))))) (TAlphaWff.classEq (TAlphaClass.cv
                  (TAlphaVar.there (freshVar_injective (((Class.cv (nb057AlphaDummy243))).fv)
                      (by decide))
                    (freshVar_injective (((Class.cv (nb057AlphaDummy245 f))).fv) (by decide))
                    (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp (TAlphaWff.neg
                      (TAlphaWff.conj
                        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                          (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
                                  (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                                    (TAlphaVar.there (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb057_support_mem_0262) 1))
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb057_support_mem_0263 f) 1))
                                      (TAlphaVar.there (Nat.ne_of_lt
        (mem_lt_freshVar (nb057_support_mem_0262) 0)) (Nat.ne_of_lt
        (mem_lt_freshVar (nb057_support_mem_0263 f) 0)) (TAlphaVar.there (Nat.ne_of_lt
        (mem_lt_freshVar (nb057_support_mem_0260) 0)) (Nat.ne_of_lt
        (mem_lt_freshVar (nb057_support_mem_0261 f) 0)) (TAlphaVar.here _ _ _))))))
                                (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
                                      (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                      (TAlphaClass.reflOfClosed [((nb057AlphaDummy258),
        (nb057AlphaDummy261 f)), ((nb057AlphaDummy257), (nb057AlphaDummy260 f)),
        ((nb057AlphaDummy256), (nb057AlphaDummy259 f)), ((nb057AlphaDummy254),
        (nb057AlphaDummy255 f)), ((nb057AlphaDummy250), (nb057AlphaDummy252 f)),
        ((nb057AlphaDummy251), (nb057AlphaDummy253 f)), ((nb057AlphaDummy243),
        (nb057AlphaDummy245 f)), ((nb057AlphaDummy242), (nb057AlphaDummy244 f)),
        ((nb057AlphaDummy248), (nb057AlphaDummy249 f)), ((nb057AlphaDummy246),
        (nb057AlphaDummy247 f)), ((nb057AlphaDummy239), (nb057AlphaDummy241 f)),
        ((nb057AlphaDummy238), (nb057AlphaDummy240 f)), ((nb057AlphaDummy000), a),
        ((nb057AlphaDummy001), f), ((nb057AlphaDummy002), (nb057AlphaDummy003 f a))]
                                        (synC1c) (by simp only [fv_syn_c1c])))
                                    (TAlphaWff.neg (nb057SplitAlpha0060 f a))))))))
                        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0260) 0))
                              (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0261 f) 0))
                              (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
                            [((nb057AlphaDummy254), (nb057AlphaDummy255 f)),
                              ((nb057AlphaDummy250), (nb057AlphaDummy252 f)),
                              ((nb057AlphaDummy251), (nb057AlphaDummy253 f)),
                              ((nb057AlphaDummy243), (nb057AlphaDummy245 f)),
                              ((nb057AlphaDummy242), (nb057AlphaDummy244 f)),
                              ((nb057AlphaDummy248), (nb057AlphaDummy249 f)),
                              ((nb057AlphaDummy246), (nb057AlphaDummy247 f)),
                              ((nb057AlphaDummy239), (nb057AlphaDummy241 f)),
                              ((nb057AlphaDummy238), (nb057AlphaDummy240 f)),
                              ((nb057AlphaDummy000), a), ((nb057AlphaDummy001), f),
                              ((nb057AlphaDummy002), (nb057AlphaDummy003 f a))]
                            (synCnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0260) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0261 f) 0))
                            (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.classMem
                          (TAlphaClass.cv (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0260) 0))
                              (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0261 f) 0))
                              (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
                            [((nb057AlphaDummy254), (nb057AlphaDummy255 f)),
                              ((nb057AlphaDummy250), (nb057AlphaDummy252 f)),
                              ((nb057AlphaDummy251), (nb057AlphaDummy253 f)),
                              ((nb057AlphaDummy243), (nb057AlphaDummy245 f)),
                              ((nb057AlphaDummy242), (nb057AlphaDummy244 f)),
                              ((nb057AlphaDummy248), (nb057AlphaDummy249 f)),
                              ((nb057AlphaDummy246), (nb057AlphaDummy247 f)),
                              ((nb057AlphaDummy239), (nb057AlphaDummy241 f)),
                              ((nb057AlphaDummy238), (nb057AlphaDummy240 f)),
                              ((nb057AlphaDummy000), a), ((nb057AlphaDummy001), f),
                              ((nb057AlphaDummy002), (nb057AlphaDummy003 f a))]
                            (synCnnc) (by simp only [fv_syn_cnnc]))))))))))))))

/-- Checked nominal proof certificate identified upstream as `nb057_split_alpha_0062`. -/
@[expose]
noncomputable def nb057SplitAlpha0062 (f : Var) (a : Var) :
    TAlphaWff
      [((nb057AlphaDummy258), (nb057AlphaDummy261 f)),
        ((nb057AlphaDummy257), (nb057AlphaDummy260 f)),
        ((nb057AlphaDummy256), (nb057AlphaDummy259 f)),
        ((nb057AlphaDummy254), (nb057AlphaDummy255 f)),
        ((nb057AlphaDummy250), (nb057AlphaDummy252 f)),
        ((nb057AlphaDummy251), (nb057AlphaDummy253 f)),
        ((nb057AlphaDummy276), (nb057AlphaDummy277 f)),
        ((nb057AlphaDummy274), (nb057AlphaDummy275 f)),
        ((nb057AlphaDummy243), (nb057AlphaDummy245 f)),
        ((nb057AlphaDummy242), (nb057AlphaDummy244 f)),
        ((nb057AlphaDummy272), (nb057AlphaDummy273 f)),
        ((nb057AlphaDummy246), (nb057AlphaDummy247 f)),
        ((nb057AlphaDummy239), (nb057AlphaDummy241 f)),
        ((nb057AlphaDummy238), (nb057AlphaDummy240 f)),
        ((nb057AlphaDummy000), a), ((nb057AlphaDummy001), f),
        ((nb057AlphaDummy002), (nb057AlphaDummy003 f a))]
      (Wff.imp (Wff.classEq
          (synCin (Class.cv (nb057AlphaDummy257)) (Class.cv (nb057AlphaDummy258)))
          (synC0)) (Wff.neg (Wff.classEq (Class.cv (nb057AlphaDummy256))
            (synCun (Class.cv (nb057AlphaDummy257)) (Class.cv (nb057AlphaDummy258))))))
      (Wff.imp (Wff.classEq (synCin (Class.cv (nb057AlphaDummy260 f))
            (Class.cv (nb057AlphaDummy261 f))) (synC0)) (Wff.neg
          (Wff.classEq (Class.cv (nb057AlphaDummy259 f))
            (synCun (Class.cv (nb057AlphaDummy260 f))
              (Class.cv (nb057AlphaDummy261 f)))))) :=
  (TAlphaWff.imp (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.neg (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0266) 0))
                          (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0267 f) 0))
                          (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0264) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0265 f) 0))
                            (TAlphaVar.there (freshVar_injective
                                (((Class.cv (nb057AlphaDummy250))).fv ∪ ((synC1c)).fv)
                                (by decide)) (freshVar_injective
                                (((Class.cv (nb057AlphaDummy252 f))).fv ∪ ((synC1c)).fv)
                                (by decide)) (TAlphaVar.here _ _ _))))))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0270) 0))
                          (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0271 f) 0))
                          (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0268) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0269 f) 0))
                            (TAlphaVar.here _ _ _)))))))))
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.neg (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0266) 0))
                          (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0267 f) 0))
                          (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0264) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0265 f) 0))
                            (TAlphaVar.there (freshVar_injective
                                (((Class.cv (nb057AlphaDummy250))).fv ∪ ((synC1c)).fv)
                                (by decide)) (freshVar_injective
                                (((Class.cv (nb057AlphaDummy252 f))).fv ∪ ((synC1c)).fv)
                                (by decide)) (TAlphaVar.here _ _ _))))))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0270) 0))
                          (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0271 f) 0))
                          (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0268) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0269 f) 0))
                            (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.reflOfClosed
        [((nb057AlphaDummy258), (nb057AlphaDummy261 f)),
          ((nb057AlphaDummy257), (nb057AlphaDummy260 f)),
          ((nb057AlphaDummy256), (nb057AlphaDummy259 f)),
          ((nb057AlphaDummy254), (nb057AlphaDummy255 f)),
          ((nb057AlphaDummy250), (nb057AlphaDummy252 f)),
          ((nb057AlphaDummy251), (nb057AlphaDummy253 f)),
          ((nb057AlphaDummy276), (nb057AlphaDummy277 f)),
          ((nb057AlphaDummy274), (nb057AlphaDummy275 f)),
          ((nb057AlphaDummy243), (nb057AlphaDummy245 f)),
          ((nb057AlphaDummy242), (nb057AlphaDummy244 f)),
          ((nb057AlphaDummy272), (nb057AlphaDummy273 f)),
          ((nb057AlphaDummy246), (nb057AlphaDummy247 f)),
          ((nb057AlphaDummy239), (nb057AlphaDummy241 f)),
          ((nb057AlphaDummy238), (nb057AlphaDummy240 f)),
          ((nb057AlphaDummy000), a), ((nb057AlphaDummy001), f),
          ((nb057AlphaDummy002), (nb057AlphaDummy003 f a))]
        (synC0) (by simp only [fv_syn_c0]))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv
          (TAlphaVar.there
            (freshVar_injective (((Class.cv (nb057AlphaDummy250))).fv ∪ ((synC1c)).fv)
              (by decide)) (freshVar_injective
              (((Class.cv (nb057AlphaDummy252 f))).fv ∪ ((synC1c)).fv) (by decide))
            (TAlphaVar.there (freshVar_injective
                (((Class.cv (nb057AlphaDummy250))).fv ∪ ((synC1c)).fv) (by decide))
              (freshVar_injective
                (((Class.cv (nb057AlphaDummy252 f))).fv ∪ ((synC1c)).fv) (by decide))
              (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                  (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0274) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0275 f) 0))
                            (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0272) 0))
                              (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0273 f) 0))
                              (TAlphaVar.there (freshVar_injective
                                  (((Class.cv (nb057AlphaDummy250))).fv ∪ ((synC1c)).fv)
                                  (by decide)) (freshVar_injective
                                  (((Class.cv (nb057AlphaDummy252 f))).fv ∪ ((synC1c)).fv)
                                  (by decide)) (TAlphaVar.here _ _ _))))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0274) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0275 f) 0))
                            (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0272) 0))
                              (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0273 f) 0))
                              (TAlphaVar.there (freshVar_injective
                                  (((Class.cv (nb057AlphaDummy250))).fv ∪ ((synC1c)).fv)
                                  (by decide)) (freshVar_injective
                                  (((Class.cv (nb057AlphaDummy252 f))).fv ∪ ((synC1c)).fv)
                                  (by decide)) (TAlphaVar.here _ _ _))))))))))
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                  (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0278) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0279 f) 0))
                            (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0276) 0))
                              (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0277 f) 0))
                              (TAlphaVar.here _ _ _)))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0278) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0279 f) 0))
                            (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0276) 0))
                              (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0277 f) 0))
                              (TAlphaVar.here _ _ _)))))))))))))))

/-- Checked nominal proof certificate identified upstream as `nb057_split_alpha_0063`. -/
@[expose]
noncomputable def nb057SplitAlpha0063 (f : Var) (a : Var) :
    TAlphaWff
      [((nb057AlphaDummy250), (nb057AlphaDummy252 f)),
        ((nb057AlphaDummy251), (nb057AlphaDummy253 f)),
        ((nb057AlphaDummy276), (nb057AlphaDummy277 f)),
        ((nb057AlphaDummy274), (nb057AlphaDummy275 f)),
        ((nb057AlphaDummy243), (nb057AlphaDummy245 f)),
        ((nb057AlphaDummy242), (nb057AlphaDummy244 f)),
        ((nb057AlphaDummy272), (nb057AlphaDummy273 f)),
        ((nb057AlphaDummy246), (nb057AlphaDummy247 f)),
        ((nb057AlphaDummy239), (nb057AlphaDummy241 f)),
        ((nb057AlphaDummy238), (nb057AlphaDummy240 f)),
        ((nb057AlphaDummy000), a), ((nb057AlphaDummy001), f),
        ((nb057AlphaDummy002), (nb057AlphaDummy003 f a))]
      (Wff.imp (Wff.classMem (Class.cv (nb057AlphaDummy250))
          (Class.cv (nb057AlphaDummy243))) (Wff.neg
          (Wff.classEq (Class.cv (nb057AlphaDummy251))
            (synCif (Wff.classMem (Class.cv (nb057AlphaDummy250)) (synCnnc))
              (synCplc (Class.cv (nb057AlphaDummy250)) (synC1c))
              (Class.cv (nb057AlphaDummy250))))))
      (Wff.imp (Wff.classMem (Class.cv (nb057AlphaDummy252 f))
          (Class.cv (nb057AlphaDummy245 f))) (Wff.neg
          (Wff.classEq (Class.cv (nb057AlphaDummy253 f))
            (synCif (Wff.classMem (Class.cv (nb057AlphaDummy252 f)) (synCnnc))
              (synCplc (Class.cv (nb057AlphaDummy252 f)) (synC1c))
              (Class.cv (nb057AlphaDummy252 f)))))) :=
  (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0258) 0))
          (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0259 f) 0))
          (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0258) 1))
            (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0259 f) 1))
            (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0288) 0))
              (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0289 f) 0))
              (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0286) 0))
                (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0287 f) 0))
                (TAlphaVar.here _ _ _))))))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv
          (TAlphaVar.there
            (freshVar_injective (((Class.cv (nb057AlphaDummy243))).fv) (by decide))
            (freshVar_injective (((Class.cv (nb057AlphaDummy245 f))).fv) (by decide))
            (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp (TAlphaWff.neg
              (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                  (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                          (TAlphaClass.cv (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0262) 1))
                              (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0263 f) 1))
                              (TAlphaVar.there (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb057_support_mem_0262) 0)) (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb057_support_mem_0263 f) 0))
                                (TAlphaVar.there (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb057_support_mem_0260) 0)) (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb057_support_mem_0261 f) 0))
                                  (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.reflOfClosed
                                [((nb057AlphaDummy258), (nb057AlphaDummy261 f)),
                                  ((nb057AlphaDummy257), (nb057AlphaDummy260 f)),
                                  ((nb057AlphaDummy256), (nb057AlphaDummy259 f)),
                                  ((nb057AlphaDummy254), (nb057AlphaDummy255 f)),
                                  ((nb057AlphaDummy250), (nb057AlphaDummy252 f)),
                                  ((nb057AlphaDummy251), (nb057AlphaDummy253 f)),
                                  ((nb057AlphaDummy276), (nb057AlphaDummy277 f)),
                                  ((nb057AlphaDummy274), (nb057AlphaDummy275 f)),
                                  ((nb057AlphaDummy243), (nb057AlphaDummy245 f)),
                                  ((nb057AlphaDummy242), (nb057AlphaDummy244 f)),
                                  ((nb057AlphaDummy272), (nb057AlphaDummy273 f)),
                                  ((nb057AlphaDummy246), (nb057AlphaDummy247 f)),
                                  ((nb057AlphaDummy239), (nb057AlphaDummy241 f)),
                                  ((nb057AlphaDummy238), (nb057AlphaDummy240 f)),
                                  ((nb057AlphaDummy000), a), ((nb057AlphaDummy001), f),
                                  ((nb057AlphaDummy002), (nb057AlphaDummy003 f a))]
                                (synC1c) (by simp only [fv_syn_c1c])))
                            (TAlphaWff.neg (nb057SplitAlpha0062 f a))))))))
                (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there
                      (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0260) 0))
                      (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0261 f) 0))
                      (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
                    [((nb057AlphaDummy254), (nb057AlphaDummy255 f)),
                      ((nb057AlphaDummy250), (nb057AlphaDummy252 f)),
                      ((nb057AlphaDummy251), (nb057AlphaDummy253 f)),
                      ((nb057AlphaDummy276), (nb057AlphaDummy277 f)),
                      ((nb057AlphaDummy274), (nb057AlphaDummy275 f)),
                      ((nb057AlphaDummy243), (nb057AlphaDummy245 f)),
                      ((nb057AlphaDummy242), (nb057AlphaDummy244 f)),
                      ((nb057AlphaDummy272), (nb057AlphaDummy273 f)),
                      ((nb057AlphaDummy246), (nb057AlphaDummy247 f)),
                      ((nb057AlphaDummy239), (nb057AlphaDummy241 f)),
                      ((nb057AlphaDummy238), (nb057AlphaDummy240 f)),
                      ((nb057AlphaDummy000), a), ((nb057AlphaDummy001), f),
                      ((nb057AlphaDummy002), (nb057AlphaDummy003 f a))]
                    (synCnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                  (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0260) 0))
                    (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0261 f) 0))
                    (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv
                    (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0260) 0))
                      (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0261 f) 0))
                      (TAlphaVar.here _ _ _))) (TAlphaClass.reflOfClosed
                    [((nb057AlphaDummy254), (nb057AlphaDummy255 f)),
                      ((nb057AlphaDummy250), (nb057AlphaDummy252 f)),
                      ((nb057AlphaDummy251), (nb057AlphaDummy253 f)),
                      ((nb057AlphaDummy276), (nb057AlphaDummy277 f)),
                      ((nb057AlphaDummy274), (nb057AlphaDummy275 f)),
                      ((nb057AlphaDummy243), (nb057AlphaDummy245 f)),
                      ((nb057AlphaDummy242), (nb057AlphaDummy244 f)),
                      ((nb057AlphaDummy272), (nb057AlphaDummy273 f)),
                      ((nb057AlphaDummy246), (nb057AlphaDummy247 f)),
                      ((nb057AlphaDummy239), (nb057AlphaDummy241 f)),
                      ((nb057AlphaDummy238), (nb057AlphaDummy240 f)),
                      ((nb057AlphaDummy000), a), ((nb057AlphaDummy001), f),
                      ((nb057AlphaDummy002), (nb057AlphaDummy003 f a))]
                    (synCnnc) (by simp only [fv_syn_cnnc]))))))))))

/-- Checked nominal proof certificate identified upstream as `nb057_split_alpha_0064`. -/
@[expose]
noncomputable def nb057SplitAlpha0064 (f : Var) (a : Var) :
    TAlphaWff
      [((nb057AlphaDummy272), (nb057AlphaDummy273 f)),
        ((nb057AlphaDummy246), (nb057AlphaDummy247 f)),
        ((nb057AlphaDummy239), (nb057AlphaDummy241 f)),
        ((nb057AlphaDummy238), (nb057AlphaDummy240 f)),
        ((nb057AlphaDummy000), a), ((nb057AlphaDummy001), f),
        ((nb057AlphaDummy002), (nb057AlphaDummy003 f a))]
      (Wff.imp (Wff.classMem (Class.cv (nb057AlphaDummy272))
          (Class.cab (nb057AlphaDummy242)
            (synWrex (nb057AlphaDummy243) (Class.cv (nb057AlphaDummy238))
              (Wff.classEq (Class.cv (nb057AlphaDummy242))
                (synCun (synCphi (Class.cv (nb057AlphaDummy243))) (synCsn (synC0c)))))))
        (Wff.neg (Wff.classMem (Class.cv (nb057AlphaDummy272))
            (Class.cab (nb057AlphaDummy242)
              (synWrex (nb057AlphaDummy243) (Class.cv (nb057AlphaDummy238))
                (Wff.classEq (Class.cv (nb057AlphaDummy242))
                  (synCun (synCphi (Class.cv (nb057AlphaDummy243)))
                    (synCsn (synC0c)))))))))
      (Wff.imp (Wff.classMem (Class.cv (nb057AlphaDummy273 f))
          (Class.cab (nb057AlphaDummy244 f)
            (synWrex (nb057AlphaDummy245 f) (Class.cv (nb057AlphaDummy240 f))
              (Wff.classEq (Class.cv (nb057AlphaDummy244 f))
                (synCun (synCphi (Class.cv (nb057AlphaDummy245 f)))
                  (synCsn (synC0c))))))) (Wff.neg
          (Wff.classMem (Class.cv (nb057AlphaDummy273 f))
            (Class.cab (nb057AlphaDummy244 f)
              (synWrex (nb057AlphaDummy245 f) (Class.cv (nb057AlphaDummy240 f))
                (Wff.classEq (Class.cv (nb057AlphaDummy244 f))
                  (synCun (synCphi (Class.cv (nb057AlphaDummy245 f)))
                    (synCsn (synC0c))))))))) :=
  (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.ex (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0280) 1))
                  (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0282 f) 1)) (TAlphaVar.there
                    (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0280) 0))
                    (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0282 f) 0))
                    (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0284) 0))
                      (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0285 f) 0))
                      (TAlphaVar.there
                        (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0281) 0))
                        (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0283 f) 0))
                        (TAlphaVar.there (freshVar_injective
                            (((synCcnv (Class.cv (nb057AlphaDummy001)))).fv ∪
                              ((synCvv)).fv) (by decide)) (freshVar_injective
                            (((synCcnv (Class.cv f))).fv ∪ ((synCvv)).fv) (by decide))
                          (TAlphaVar.here _ _ _)))))))) (TAlphaWff.classEq (TAlphaClass.cv
                (TAlphaVar.there (freshVar_injective (((Class.cv (nb057AlphaDummy239))).fv ∪
                      ((Class.cv (nb057AlphaDummy238))).fv) (by decide)) (freshVar_injective
                    (((Class.cv (nb057AlphaDummy241 f))).fv ∪
                      ((Class.cv (nb057AlphaDummy240 f))).fv) (by decide))
                  (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                        (TAlphaWff.neg (TAlphaWff.conj
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cab (TAlphaWff.ex
                                  (TAlphaWff.neg (nb057SplitAlpha0063 f a)))))
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cab (TAlphaWff.ex
                                  (TAlphaWff.neg (nb057SplitAlpha0063 f a)))))))))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                      (TAlphaClass.reflOfClosed
                        [((nb057AlphaDummy274), (nb057AlphaDummy275 f)),
                          ((nb057AlphaDummy243), (nb057AlphaDummy245 f)),
                          ((nb057AlphaDummy242), (nb057AlphaDummy244 f)),
                          ((nb057AlphaDummy272), (nb057AlphaDummy273 f)),
                          ((nb057AlphaDummy246), (nb057AlphaDummy247 f)),
                          ((nb057AlphaDummy239), (nb057AlphaDummy241 f)),
                          ((nb057AlphaDummy238), (nb057AlphaDummy240 f)),
                          ((nb057AlphaDummy000), a), ((nb057AlphaDummy001), f),
                          ((nb057AlphaDummy002), (nb057AlphaDummy003 f a))]
                        (synCcompl (synCsn (synC0c)))
                        (by simp only [fv_syn_ccompl, fv_syn_csn, fv_syn_c0c])))))))))))
    (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
          (TAlphaWff.ex (TAlphaWff.conj
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                  (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0280) 1))
                    (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0282 f) 1))
                    (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0280) 0))
                      (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0282 f) 0))
                      (TAlphaVar.there
                        (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0284) 0))
                        (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0285 f) 0))
                        (TAlphaVar.there
                          (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0281) 0))
                          (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0283 f) 0))
                          (TAlphaVar.there (freshVar_injective
                              (((synCcnv (Class.cv (nb057AlphaDummy001)))).fv ∪
                                ((synCvv)).fv) (by decide)) (freshVar_injective
                              (((synCcnv (Class.cv f))).fv ∪ ((synCvv)).fv) (by decide))
                            (TAlphaVar.here _ _ _)))))))) (TAlphaWff.classEq (TAlphaClass.cv
                  (TAlphaVar.there (freshVar_injective
                      (((Class.cv (nb057AlphaDummy239))).fv ∪
                        ((Class.cv (nb057AlphaDummy238))).fv) (by decide))
                    (freshVar_injective (((Class.cv (nb057AlphaDummy241 f))).fv ∪
                        ((Class.cv (nb057AlphaDummy240 f))).fv) (by decide))
                    (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cab (TAlphaWff.ex
                                    (TAlphaWff.neg (nb057SplitAlpha0063 f a)))))
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cab (TAlphaWff.ex
                                    (TAlphaWff.neg (nb057SplitAlpha0063 f a)))))))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.reflOfClosed
                          [((nb057AlphaDummy274), (nb057AlphaDummy275 f)),
                            ((nb057AlphaDummy243), (nb057AlphaDummy245 f)),
                            ((nb057AlphaDummy242), (nb057AlphaDummy244 f)),
                            ((nb057AlphaDummy272), (nb057AlphaDummy273 f)),
                            ((nb057AlphaDummy246), (nb057AlphaDummy247 f)),
                            ((nb057AlphaDummy239), (nb057AlphaDummy241 f)),
                            ((nb057AlphaDummy238), (nb057AlphaDummy240 f)),
                            ((nb057AlphaDummy000), a), ((nb057AlphaDummy001), f),
                            ((nb057AlphaDummy002), (nb057AlphaDummy003 f a))]
                          (synCcompl (synCsn (synC0c))) (by
                            simp only [fv_syn_ccompl, fv_syn_csn, fv_syn_c0c])))))))))))))


end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired

end
