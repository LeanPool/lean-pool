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

@[expose]
noncomputable def nb057_wpp_refl_0042 (f : Var) (a : Var) :
    TReflOn
      [((nb057_alpha_dummy_042), (nb057_alpha_dummy_043 f)),
        ((nb057_alpha_dummy_040), (nb057_alpha_dummy_041 f)),
        ((nb057_alpha_dummy_000), a), ((nb057_alpha_dummy_001), f),
        ((nb057_alpha_dummy_002), (nb057_alpha_dummy_003 f a))]
      ((syn_cid)).fv :=
  TEnvFresh.reflOn (nb057_compact_envfresh_0042 f a)

@[expose]
noncomputable def nb057_function_binder_occurrence (f a : Var) :
    TAlphaClass
      [(nb057_alpha_dummy_045, (nb057_alpha_dummy_048 f)),
        (nb057_alpha_dummy_044, (nb057_alpha_dummy_047 f)),
        (nb057_alpha_dummy_050, (nb057_alpha_dummy_051 f)),
        (nb057_alpha_dummy_042, (nb057_alpha_dummy_043 f)),
        (nb057_alpha_dummy_040, (nb057_alpha_dummy_041 f)), (nb057_alpha_dummy_000, a),
        (nb057_alpha_dummy_001, f), (nb057_alpha_dummy_002, (nb057_alpha_dummy_003 f a))]
      (Class.cv nb057_alpha_dummy_050) (Class.cv (nb057_alpha_dummy_051 f)) :=
  by
  have freshness0 : nb057_alpha_dummy_050 ≠ nb057_alpha_dummy_045 :=
    by
    unfold nb057_alpha_dummy_050
    with_reducible
      exact (Ne.symm (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0044) 0)))
  have freshness1 : (nb057_alpha_dummy_051 f) ≠ (nb057_alpha_dummy_048 f) :=
    by
    unfold nb057_alpha_dummy_051
    with_reducible
      exact (Ne.symm (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0045 f) 0)))
  have freshness2 : nb057_alpha_dummy_050 ≠ nb057_alpha_dummy_044 :=
    by
    unfold nb057_alpha_dummy_050
    with_reducible
      exact (Ne.symm (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0042) 0)))
  have freshness3 : (nb057_alpha_dummy_051 f) ≠ (nb057_alpha_dummy_047 f) :=
    by
    unfold nb057_alpha_dummy_051
    with_reducible
      exact (Ne.symm (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0043 f) 0)))
  with_reducible
    exact
      (TAlphaClass.cv (TAlphaVar.there freshness0 freshness1
          (TAlphaVar.there freshness2 freshness3 (TAlphaVar.here _ _ _))))

@[expose]
noncomputable def nb057_split_alpha_0032 (f : Var) (a : Var) (dv_a_f : a ≠ f) :
    TAlphaWff
      [((nb057_alpha_dummy_040), (nb057_alpha_dummy_041 f)), ((nb057_alpha_dummy_000), a),
        ((nb057_alpha_dummy_001), f),
        ((nb057_alpha_dummy_002), (nb057_alpha_dummy_003 f a))]
      (Wff.imp (Wff.classMem (Class.cv (nb057_alpha_dummy_040)) (syn_cnin
            (syn_ccom (Class.cv (nb057_alpha_dummy_001))
              (syn_ccnv (Class.cv (nb057_alpha_dummy_001)))) (syn_cid))) (Wff.neg
          (Wff.classMem (Class.cv (nb057_alpha_dummy_040)) (syn_cnin
              (syn_ccom (Class.cv (nb057_alpha_dummy_001))
                (syn_ccnv (Class.cv (nb057_alpha_dummy_001)))) (syn_cid)))))
      (Wff.imp (Wff.classMem (Class.cv (nb057_alpha_dummy_041 f))
          (syn_cnin (syn_ccom (Class.cv f) (syn_ccnv (Class.cv f))) (syn_cid))) (Wff.neg
          (Wff.classMem (Class.cv (nb057_alpha_dummy_041 f))
            (syn_cnin (syn_ccom (Class.cv f) (syn_ccnv (Class.cv f))) (syn_cid))))) :=
  (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.ex (TAlphaWff.ex (TAlphaWff.conj
                      (TAlphaWff.classEq (nb057_function_binder_occurrence f a) (TAlphaClass.cab
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
        0)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb057_alpha_dummy_001))).fv ∪
        ((syn_ccnv (Class.cv (nb057_alpha_dummy_001)))).fv) (by decide)) (freshVar_injective
        (((Class.cv f)).fv ∪ ((syn_ccnv (Class.cv f))).fv) (by decide))
        (TAlphaVar.here _ _ _)))))))) (nb057_split_alpha_0006 f a))))) (TAlphaWff.classMem
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
        0)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb057_alpha_dummy_001))).fv ∪
        ((syn_ccnv (Class.cv (nb057_alpha_dummy_001)))).fv) (by decide)) (freshVar_injective
        (((Class.cv f)).fv ∪ ((syn_ccnv (Class.cv f))).fv) (by decide))
        (TAlphaVar.here _ _ _)))))))) (nb057_split_alpha_0006 f a)))))))))
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cab (TAlphaWff.neg
                                    (TAlphaWff.neg (nb057_split_alpha_0009 f a)))))))))
                      (TAlphaWff.ex (TAlphaWff.neg (nb057_split_alpha_0031 f a dv_a_f))))))))
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
              (TAlphaClass.refl_of_reflOn [((nb057_alpha_dummy_042), (nb057_alpha_dummy_043 f)),
                  ((nb057_alpha_dummy_040), (nb057_alpha_dummy_041 f)),
                  ((nb057_alpha_dummy_000), a), ((nb057_alpha_dummy_001), f),
                  ((nb057_alpha_dummy_002), (nb057_alpha_dummy_003 f a))]
                (syn_cid) (nb057_wpp_refl_0042 f a))))))) (TAlphaWff.neg
      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
          (TAlphaWff.neg (TAlphaWff.conj
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                  (TAlphaWff.ex (TAlphaWff.ex (TAlphaWff.conj
                        (TAlphaWff.classEq (nb057_function_binder_occurrence f a)
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
        0)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb057_alpha_dummy_001))).fv ∪
        ((syn_ccnv (Class.cv (nb057_alpha_dummy_001)))).fv) (by decide)) (freshVar_injective
        (((Class.cv f)).fv ∪ ((syn_ccnv (Class.cv f))).fv) (by decide)) (TAlphaVar.here _ _
        _)))))))) (nb057_split_alpha_0006 f a))))) (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0046) 1))
        (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0048 f) 1)) (TAlphaVar.there
        (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0046) 0)) (Nat.ne_of_lt
        (mem_lt_freshVar (nb057_support_mem_0048 f) 0)) (TAlphaVar.there (Nat.ne_of_lt
        (mem_lt_freshVar (nb057_support_mem_0050) 0)) (Nat.ne_of_lt (mem_lt_freshVar
        (nb057_support_mem_0051 f) 0)) (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar
        (nb057_support_mem_0047) 0)) (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0049 f)
        0)) (TAlphaVar.there (freshVar_injective (((Class.cv (nb057_alpha_dummy_001))).fv ∪
        ((syn_ccnv (Class.cv (nb057_alpha_dummy_001)))).fv) (by decide)) (freshVar_injective
        (((Class.cv f)).fv ∪ ((syn_ccnv (Class.cv f))).fv) (by decide)) (TAlphaVar.here _ _
        _)))))))) (nb057_split_alpha_0006 f a))))))))) (TAlphaWff.classMem
                                  (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                                    (TAlphaWff.neg
                                      (TAlphaWff.neg (nb057_split_alpha_0009 f a)))))))))
                        (TAlphaWff.ex (TAlphaWff.neg (nb057_split_alpha_0031 f a dv_a_f))))))))
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                (TAlphaClass.refl_of_reflOn
                  [((nb057_alpha_dummy_042), (nb057_alpha_dummy_043 f)),
                    ((nb057_alpha_dummy_040), (nb057_alpha_dummy_041 f)),
                    ((nb057_alpha_dummy_000), a), ((nb057_alpha_dummy_001), f),
                    ((nb057_alpha_dummy_002), (nb057_alpha_dummy_003 f a))]
                  (syn_cid) (nb057_wpp_refl_0042 f a)))))))))

@[expose]
noncomputable def nb057_split_alpha_0033 (f : Var) (a : Var) :
    TAlphaWff
      [((nb057_alpha_dummy_068), (nb057_alpha_dummy_071 f)),
        ((nb057_alpha_dummy_067), (nb057_alpha_dummy_070 f)),
        ((nb057_alpha_dummy_066), (nb057_alpha_dummy_069 f)),
        ((nb057_alpha_dummy_064), (nb057_alpha_dummy_065 f)),
        ((nb057_alpha_dummy_060), (nb057_alpha_dummy_062 f)),
        ((nb057_alpha_dummy_061), (nb057_alpha_dummy_063 f)),
        ((nb057_alpha_dummy_053), (nb057_alpha_dummy_055 f)),
        ((nb057_alpha_dummy_052), (nb057_alpha_dummy_054 f)),
        ((nb057_alpha_dummy_058), (nb057_alpha_dummy_059 f)),
        ((nb057_alpha_dummy_056), (nb057_alpha_dummy_057 f)),
        ((nb057_alpha_dummy_045), (nb057_alpha_dummy_048 f)),
        ((nb057_alpha_dummy_044), (nb057_alpha_dummy_047 f)),
        ((nb057_alpha_dummy_050), (nb057_alpha_dummy_051 f)),
        ((nb057_alpha_dummy_000), a), ((nb057_alpha_dummy_001), f),
        ((nb057_alpha_dummy_002), (nb057_alpha_dummy_003 f a))]
      (Wff.imp (Wff.classEq
          (syn_cin (Class.cv (nb057_alpha_dummy_067)) (Class.cv (nb057_alpha_dummy_068)))
          (syn_c0)) (Wff.neg (Wff.classEq (Class.cv (nb057_alpha_dummy_066))
            (syn_cun (Class.cv (nb057_alpha_dummy_067)) (Class.cv (nb057_alpha_dummy_068))))))
      (Wff.imp (Wff.classEq (syn_cin (Class.cv (nb057_alpha_dummy_070 f))
            (Class.cv (nb057_alpha_dummy_071 f))) (syn_c0)) (Wff.neg
          (Wff.classEq (Class.cv (nb057_alpha_dummy_069 f))
            (syn_cun (Class.cv (nb057_alpha_dummy_070 f))
              (Class.cv (nb057_alpha_dummy_071 f)))))) :=
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
                                (((Class.cv (nb057_alpha_dummy_060))).fv ∪ ((syn_c1c)).fv)
                                (by decide)) (freshVar_injective
                                (((Class.cv (nb057_alpha_dummy_062 f))).fv ∪ ((syn_c1c)).fv)
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
                                (((Class.cv (nb057_alpha_dummy_060))).fv ∪ ((syn_c1c)).fv)
                                (by decide)) (freshVar_injective
                                (((Class.cv (nb057_alpha_dummy_062 f))).fv ∪ ((syn_c1c)).fv)
                                (by decide)) (TAlphaVar.here _ _ _))))))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0064) 0))
                          (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0065 f) 0))
                          (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0062) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0063 f) 0))
                            (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.refl_of_closed
        [((nb057_alpha_dummy_068), (nb057_alpha_dummy_071 f)),
          ((nb057_alpha_dummy_067), (nb057_alpha_dummy_070 f)),
          ((nb057_alpha_dummy_066), (nb057_alpha_dummy_069 f)),
          ((nb057_alpha_dummy_064), (nb057_alpha_dummy_065 f)),
          ((nb057_alpha_dummy_060), (nb057_alpha_dummy_062 f)),
          ((nb057_alpha_dummy_061), (nb057_alpha_dummy_063 f)),
          ((nb057_alpha_dummy_053), (nb057_alpha_dummy_055 f)),
          ((nb057_alpha_dummy_052), (nb057_alpha_dummy_054 f)),
          ((nb057_alpha_dummy_058), (nb057_alpha_dummy_059 f)),
          ((nb057_alpha_dummy_056), (nb057_alpha_dummy_057 f)),
          ((nb057_alpha_dummy_045), (nb057_alpha_dummy_048 f)),
          ((nb057_alpha_dummy_044), (nb057_alpha_dummy_047 f)),
          ((nb057_alpha_dummy_050), (nb057_alpha_dummy_051 f)),
          ((nb057_alpha_dummy_000), a), ((nb057_alpha_dummy_001), f),
          ((nb057_alpha_dummy_002), (nb057_alpha_dummy_003 f a))]
        (syn_c0) (by simp only [fv_syn_c0]))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv
          (TAlphaVar.there
            (freshVar_injective (((Class.cv (nb057_alpha_dummy_060))).fv ∪ ((syn_c1c)).fv)
              (by decide)) (freshVar_injective
              (((Class.cv (nb057_alpha_dummy_062 f))).fv ∪ ((syn_c1c)).fv) (by decide))
            (TAlphaVar.there (freshVar_injective
                (((Class.cv (nb057_alpha_dummy_060))).fv ∪ ((syn_c1c)).fv) (by decide))
              (freshVar_injective
                (((Class.cv (nb057_alpha_dummy_062 f))).fv ∪ ((syn_c1c)).fv) (by decide))
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
                                  (((Class.cv (nb057_alpha_dummy_060))).fv ∪ ((syn_c1c)).fv)
                                  (by decide)) (freshVar_injective
                                  (((Class.cv (nb057_alpha_dummy_062 f))).fv ∪ ((syn_c1c)).fv)
                                  (by decide)) (TAlphaVar.here _ _ _))))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0068) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0069 f) 0))
                            (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0066) 0))
                              (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0067 f) 0))
                              (TAlphaVar.there (freshVar_injective
                                  (((Class.cv (nb057_alpha_dummy_060))).fv ∪ ((syn_c1c)).fv)
                                  (by decide)) (freshVar_injective
                                  (((Class.cv (nb057_alpha_dummy_062 f))).fv ∪ ((syn_c1c)).fv)
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

@[expose]
noncomputable def nb057_split_alpha_0034 (f : Var) (a : Var) :
    TAlphaWff
      [((nb057_alpha_dummy_053), (nb057_alpha_dummy_055 f)),
        ((nb057_alpha_dummy_052), (nb057_alpha_dummy_054 f)),
        ((nb057_alpha_dummy_058), (nb057_alpha_dummy_059 f)),
        ((nb057_alpha_dummy_056), (nb057_alpha_dummy_057 f)),
        ((nb057_alpha_dummy_045), (nb057_alpha_dummy_048 f)),
        ((nb057_alpha_dummy_044), (nb057_alpha_dummy_047 f)),
        ((nb057_alpha_dummy_050), (nb057_alpha_dummy_051 f)),
        ((nb057_alpha_dummy_000), a), ((nb057_alpha_dummy_001), f),
        ((nb057_alpha_dummy_002), (nb057_alpha_dummy_003 f a))]
      (Wff.classEq (Class.cv (nb057_alpha_dummy_052))
        (syn_cphi (Class.cv (nb057_alpha_dummy_053))))
      (Wff.classEq (Class.cv (nb057_alpha_dummy_054 f))
        (syn_cphi (Class.cv (nb057_alpha_dummy_055 f)))) :=
  (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective
          (((Class.cv (nb057_alpha_dummy_044))).fv ∪ ((Class.cv (nb057_alpha_dummy_045))).fv)
          (by decide)) (freshVar_injective (((Class.cv (nb057_alpha_dummy_047 f))).fv ∪
            ((Class.cv (nb057_alpha_dummy_048 f))).fv) (by decide)) (TAlphaVar.here _ _ _)))
    (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
          (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
              (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0052) 0))
                (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0053 f) 0)) (TAlphaVar.there
                  (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0052) 1))
                  (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0053 f) 1))
                  (TAlphaVar.here _ _ _))))) (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there
                (freshVar_injective (((Class.cv (nb057_alpha_dummy_053))).fv) (by decide))
                (freshVar_injective (((Class.cv (nb057_alpha_dummy_055 f))).fv) (by decide))
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
                                  (TAlphaClass.refl_of_closed
                                    [((nb057_alpha_dummy_068), (nb057_alpha_dummy_071 f)),
                                      ((nb057_alpha_dummy_067), (nb057_alpha_dummy_070 f)),
                                      ((nb057_alpha_dummy_066), (nb057_alpha_dummy_069 f)),
                                      ((nb057_alpha_dummy_064), (nb057_alpha_dummy_065 f)),
                                      ((nb057_alpha_dummy_060), (nb057_alpha_dummy_062 f)),
                                      ((nb057_alpha_dummy_061), (nb057_alpha_dummy_063 f)),
                                      ((nb057_alpha_dummy_053), (nb057_alpha_dummy_055 f)),
                                      ((nb057_alpha_dummy_052), (nb057_alpha_dummy_054 f)),
                                      ((nb057_alpha_dummy_058), (nb057_alpha_dummy_059 f)),
                                      ((nb057_alpha_dummy_056), (nb057_alpha_dummy_057 f)),
                                      ((nb057_alpha_dummy_045), (nb057_alpha_dummy_048 f)),
                                      ((nb057_alpha_dummy_044), (nb057_alpha_dummy_047 f)),
                                      ((nb057_alpha_dummy_050), (nb057_alpha_dummy_051 f)),
                                      ((nb057_alpha_dummy_000), a),
                                      ((nb057_alpha_dummy_001), f), ((nb057_alpha_dummy_002),
                                        (nb057_alpha_dummy_003 f a))]
                                    (syn_c1c) (by simp only [fv_syn_c1c])))
                                (TAlphaWff.neg (nb057_split_alpha_0033 f a))))))))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there
                          (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0054) 0))
                          (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0055 f) 0))
                          (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
                        [((nb057_alpha_dummy_064), (nb057_alpha_dummy_065 f)),
                          ((nb057_alpha_dummy_060), (nb057_alpha_dummy_062 f)),
                          ((nb057_alpha_dummy_061), (nb057_alpha_dummy_063 f)),
                          ((nb057_alpha_dummy_053), (nb057_alpha_dummy_055 f)),
                          ((nb057_alpha_dummy_052), (nb057_alpha_dummy_054 f)),
                          ((nb057_alpha_dummy_058), (nb057_alpha_dummy_059 f)),
                          ((nb057_alpha_dummy_056), (nb057_alpha_dummy_057 f)),
                          ((nb057_alpha_dummy_045), (nb057_alpha_dummy_048 f)),
                          ((nb057_alpha_dummy_044), (nb057_alpha_dummy_047 f)),
                          ((nb057_alpha_dummy_050), (nb057_alpha_dummy_051 f)),
                          ((nb057_alpha_dummy_000), a), ((nb057_alpha_dummy_001), f),
                          ((nb057_alpha_dummy_002), (nb057_alpha_dummy_003 f a))]
                        (syn_cnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
                  (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                      (TAlphaVar.there
                        (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0054) 0))
                        (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0055 f) 0))
                        (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.classMem
                      (TAlphaClass.cv (TAlphaVar.there
                          (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0054) 0))
                          (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0055 f) 0))
                          (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
                        [((nb057_alpha_dummy_064), (nb057_alpha_dummy_065 f)),
                          ((nb057_alpha_dummy_060), (nb057_alpha_dummy_062 f)),
                          ((nb057_alpha_dummy_061), (nb057_alpha_dummy_063 f)),
                          ((nb057_alpha_dummy_053), (nb057_alpha_dummy_055 f)),
                          ((nb057_alpha_dummy_052), (nb057_alpha_dummy_054 f)),
                          ((nb057_alpha_dummy_058), (nb057_alpha_dummy_059 f)),
                          ((nb057_alpha_dummy_056), (nb057_alpha_dummy_057 f)),
                          ((nb057_alpha_dummy_045), (nb057_alpha_dummy_048 f)),
                          ((nb057_alpha_dummy_044), (nb057_alpha_dummy_047 f)),
                          ((nb057_alpha_dummy_050), (nb057_alpha_dummy_051 f)),
                          ((nb057_alpha_dummy_000), a), ((nb057_alpha_dummy_001), f),
                          ((nb057_alpha_dummy_002), (nb057_alpha_dummy_003 f a))]
                        (syn_cnnc) (by simp only [fv_syn_cnnc]))))))))))))


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

@[expose]
noncomputable def nb057_split_alpha_0035 (f : Var) (a : Var) :
    TAlphaWff
      [((nb057_alpha_dummy_068), (nb057_alpha_dummy_071 f)),
        ((nb057_alpha_dummy_067), (nb057_alpha_dummy_070 f)),
        ((nb057_alpha_dummy_066), (nb057_alpha_dummy_069 f)),
        ((nb057_alpha_dummy_064), (nb057_alpha_dummy_065 f)),
        ((nb057_alpha_dummy_060), (nb057_alpha_dummy_062 f)),
        ((nb057_alpha_dummy_061), (nb057_alpha_dummy_063 f)),
        ((nb057_alpha_dummy_086), (nb057_alpha_dummy_087 f)),
        ((nb057_alpha_dummy_084), (nb057_alpha_dummy_085 f)),
        ((nb057_alpha_dummy_053), (nb057_alpha_dummy_055 f)),
        ((nb057_alpha_dummy_052), (nb057_alpha_dummy_054 f)),
        ((nb057_alpha_dummy_082), (nb057_alpha_dummy_083 f)),
        ((nb057_alpha_dummy_056), (nb057_alpha_dummy_057 f)),
        ((nb057_alpha_dummy_045), (nb057_alpha_dummy_048 f)),
        ((nb057_alpha_dummy_044), (nb057_alpha_dummy_047 f)),
        ((nb057_alpha_dummy_050), (nb057_alpha_dummy_051 f)),
        ((nb057_alpha_dummy_000), a), ((nb057_alpha_dummy_001), f),
        ((nb057_alpha_dummy_002), (nb057_alpha_dummy_003 f a))]
      (Wff.imp (Wff.classEq
          (syn_cin (Class.cv (nb057_alpha_dummy_067)) (Class.cv (nb057_alpha_dummy_068)))
          (syn_c0)) (Wff.neg (Wff.classEq (Class.cv (nb057_alpha_dummy_066))
            (syn_cun (Class.cv (nb057_alpha_dummy_067)) (Class.cv (nb057_alpha_dummy_068))))))
      (Wff.imp (Wff.classEq (syn_cin (Class.cv (nb057_alpha_dummy_070 f))
            (Class.cv (nb057_alpha_dummy_071 f))) (syn_c0)) (Wff.neg
          (Wff.classEq (Class.cv (nb057_alpha_dummy_069 f))
            (syn_cun (Class.cv (nb057_alpha_dummy_070 f))
              (Class.cv (nb057_alpha_dummy_071 f)))))) :=
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
                                (((Class.cv (nb057_alpha_dummy_060))).fv ∪ ((syn_c1c)).fv)
                                (by decide)) (freshVar_injective
                                (((Class.cv (nb057_alpha_dummy_062 f))).fv ∪ ((syn_c1c)).fv)
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
                                (((Class.cv (nb057_alpha_dummy_060))).fv ∪ ((syn_c1c)).fv)
                                (by decide)) (freshVar_injective
                                (((Class.cv (nb057_alpha_dummy_062 f))).fv ∪ ((syn_c1c)).fv)
                                (by decide)) (TAlphaVar.here _ _ _))))))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0064) 0))
                          (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0065 f) 0))
                          (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0062) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0063 f) 0))
                            (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.refl_of_closed
        [((nb057_alpha_dummy_068), (nb057_alpha_dummy_071 f)),
          ((nb057_alpha_dummy_067), (nb057_alpha_dummy_070 f)),
          ((nb057_alpha_dummy_066), (nb057_alpha_dummy_069 f)),
          ((nb057_alpha_dummy_064), (nb057_alpha_dummy_065 f)),
          ((nb057_alpha_dummy_060), (nb057_alpha_dummy_062 f)),
          ((nb057_alpha_dummy_061), (nb057_alpha_dummy_063 f)),
          ((nb057_alpha_dummy_086), (nb057_alpha_dummy_087 f)),
          ((nb057_alpha_dummy_084), (nb057_alpha_dummy_085 f)),
          ((nb057_alpha_dummy_053), (nb057_alpha_dummy_055 f)),
          ((nb057_alpha_dummy_052), (nb057_alpha_dummy_054 f)),
          ((nb057_alpha_dummy_082), (nb057_alpha_dummy_083 f)),
          ((nb057_alpha_dummy_056), (nb057_alpha_dummy_057 f)),
          ((nb057_alpha_dummy_045), (nb057_alpha_dummy_048 f)),
          ((nb057_alpha_dummy_044), (nb057_alpha_dummy_047 f)),
          ((nb057_alpha_dummy_050), (nb057_alpha_dummy_051 f)),
          ((nb057_alpha_dummy_000), a), ((nb057_alpha_dummy_001), f),
          ((nb057_alpha_dummy_002), (nb057_alpha_dummy_003 f a))]
        (syn_c0) (by simp only [fv_syn_c0]))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv
          (TAlphaVar.there
            (freshVar_injective (((Class.cv (nb057_alpha_dummy_060))).fv ∪ ((syn_c1c)).fv)
              (by decide)) (freshVar_injective
              (((Class.cv (nb057_alpha_dummy_062 f))).fv ∪ ((syn_c1c)).fv) (by decide))
            (TAlphaVar.there (freshVar_injective
                (((Class.cv (nb057_alpha_dummy_060))).fv ∪ ((syn_c1c)).fv) (by decide))
              (freshVar_injective
                (((Class.cv (nb057_alpha_dummy_062 f))).fv ∪ ((syn_c1c)).fv) (by decide))
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
                                  (((Class.cv (nb057_alpha_dummy_060))).fv ∪ ((syn_c1c)).fv)
                                  (by decide)) (freshVar_injective
                                  (((Class.cv (nb057_alpha_dummy_062 f))).fv ∪ ((syn_c1c)).fv)
                                  (by decide)) (TAlphaVar.here _ _ _))))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0068) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0069 f) 0))
                            (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0066) 0))
                              (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0067 f) 0))
                              (TAlphaVar.there (freshVar_injective
                                  (((Class.cv (nb057_alpha_dummy_060))).fv ∪ ((syn_c1c)).fv)
                                  (by decide)) (freshVar_injective
                                  (((Class.cv (nb057_alpha_dummy_062 f))).fv ∪ ((syn_c1c)).fv)
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

@[expose]
noncomputable def nb057_split_alpha_0036 (f : Var) (a : Var) :
    TAlphaWff
      [((nb057_alpha_dummy_060), (nb057_alpha_dummy_062 f)),
        ((nb057_alpha_dummy_061), (nb057_alpha_dummy_063 f)),
        ((nb057_alpha_dummy_086), (nb057_alpha_dummy_087 f)),
        ((nb057_alpha_dummy_084), (nb057_alpha_dummy_085 f)),
        ((nb057_alpha_dummy_053), (nb057_alpha_dummy_055 f)),
        ((nb057_alpha_dummy_052), (nb057_alpha_dummy_054 f)),
        ((nb057_alpha_dummy_082), (nb057_alpha_dummy_083 f)),
        ((nb057_alpha_dummy_056), (nb057_alpha_dummy_057 f)),
        ((nb057_alpha_dummy_045), (nb057_alpha_dummy_048 f)),
        ((nb057_alpha_dummy_044), (nb057_alpha_dummy_047 f)),
        ((nb057_alpha_dummy_050), (nb057_alpha_dummy_051 f)),
        ((nb057_alpha_dummy_000), a), ((nb057_alpha_dummy_001), f),
        ((nb057_alpha_dummy_002), (nb057_alpha_dummy_003 f a))]
      (Wff.imp (Wff.classMem (Class.cv (nb057_alpha_dummy_060))
          (Class.cv (nb057_alpha_dummy_053))) (Wff.neg
          (Wff.classEq (Class.cv (nb057_alpha_dummy_061))
            (syn_cif (Wff.classMem (Class.cv (nb057_alpha_dummy_060)) (syn_cnnc))
              (syn_cplc (Class.cv (nb057_alpha_dummy_060)) (syn_c1c))
              (Class.cv (nb057_alpha_dummy_060))))))
      (Wff.imp (Wff.classMem (Class.cv (nb057_alpha_dummy_062 f))
          (Class.cv (nb057_alpha_dummy_055 f))) (Wff.neg
          (Wff.classEq (Class.cv (nb057_alpha_dummy_063 f))
            (syn_cif (Wff.classMem (Class.cv (nb057_alpha_dummy_062 f)) (syn_cnnc))
              (syn_cplc (Class.cv (nb057_alpha_dummy_062 f)) (syn_c1c))
              (Class.cv (nb057_alpha_dummy_062 f)))))) :=
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
            (freshVar_injective (((Class.cv (nb057_alpha_dummy_053))).fv) (by decide))
            (freshVar_injective (((Class.cv (nb057_alpha_dummy_055 f))).fv) (by decide))
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
                              (TAlphaClass.refl_of_closed
                                [((nb057_alpha_dummy_068), (nb057_alpha_dummy_071 f)),
                                  ((nb057_alpha_dummy_067), (nb057_alpha_dummy_070 f)),
                                  ((nb057_alpha_dummy_066), (nb057_alpha_dummy_069 f)),
                                  ((nb057_alpha_dummy_064), (nb057_alpha_dummy_065 f)),
                                  ((nb057_alpha_dummy_060), (nb057_alpha_dummy_062 f)),
                                  ((nb057_alpha_dummy_061), (nb057_alpha_dummy_063 f)),
                                  ((nb057_alpha_dummy_086), (nb057_alpha_dummy_087 f)),
                                  ((nb057_alpha_dummy_084), (nb057_alpha_dummy_085 f)),
                                  ((nb057_alpha_dummy_053), (nb057_alpha_dummy_055 f)),
                                  ((nb057_alpha_dummy_052), (nb057_alpha_dummy_054 f)),
                                  ((nb057_alpha_dummy_082), (nb057_alpha_dummy_083 f)),
                                  ((nb057_alpha_dummy_056), (nb057_alpha_dummy_057 f)),
                                  ((nb057_alpha_dummy_045), (nb057_alpha_dummy_048 f)),
                                  ((nb057_alpha_dummy_044), (nb057_alpha_dummy_047 f)),
                                  ((nb057_alpha_dummy_050), (nb057_alpha_dummy_051 f)),
                                  ((nb057_alpha_dummy_000), a), ((nb057_alpha_dummy_001), f),
                                  ((nb057_alpha_dummy_002), (nb057_alpha_dummy_003 f a))]
                                (syn_c1c) (by simp only [fv_syn_c1c])))
                            (TAlphaWff.neg (nb057_split_alpha_0035 f a))))))))
                (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there
                      (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0054) 0))
                      (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0055 f) 0))
                      (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
                    [((nb057_alpha_dummy_064), (nb057_alpha_dummy_065 f)),
                      ((nb057_alpha_dummy_060), (nb057_alpha_dummy_062 f)),
                      ((nb057_alpha_dummy_061), (nb057_alpha_dummy_063 f)),
                      ((nb057_alpha_dummy_086), (nb057_alpha_dummy_087 f)),
                      ((nb057_alpha_dummy_084), (nb057_alpha_dummy_085 f)),
                      ((nb057_alpha_dummy_053), (nb057_alpha_dummy_055 f)),
                      ((nb057_alpha_dummy_052), (nb057_alpha_dummy_054 f)),
                      ((nb057_alpha_dummy_082), (nb057_alpha_dummy_083 f)),
                      ((nb057_alpha_dummy_056), (nb057_alpha_dummy_057 f)),
                      ((nb057_alpha_dummy_045), (nb057_alpha_dummy_048 f)),
                      ((nb057_alpha_dummy_044), (nb057_alpha_dummy_047 f)),
                      ((nb057_alpha_dummy_050), (nb057_alpha_dummy_051 f)),
                      ((nb057_alpha_dummy_000), a), ((nb057_alpha_dummy_001), f),
                      ((nb057_alpha_dummy_002), (nb057_alpha_dummy_003 f a))]
                    (syn_cnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                  (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0054) 0))
                    (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0055 f) 0))
                    (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv
                    (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0054) 0))
                      (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0055 f) 0))
                      (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
                    [((nb057_alpha_dummy_064), (nb057_alpha_dummy_065 f)),
                      ((nb057_alpha_dummy_060), (nb057_alpha_dummy_062 f)),
                      ((nb057_alpha_dummy_061), (nb057_alpha_dummy_063 f)),
                      ((nb057_alpha_dummy_086), (nb057_alpha_dummy_087 f)),
                      ((nb057_alpha_dummy_084), (nb057_alpha_dummy_085 f)),
                      ((nb057_alpha_dummy_053), (nb057_alpha_dummy_055 f)),
                      ((nb057_alpha_dummy_052), (nb057_alpha_dummy_054 f)),
                      ((nb057_alpha_dummy_082), (nb057_alpha_dummy_083 f)),
                      ((nb057_alpha_dummy_056), (nb057_alpha_dummy_057 f)),
                      ((nb057_alpha_dummy_045), (nb057_alpha_dummy_048 f)),
                      ((nb057_alpha_dummy_044), (nb057_alpha_dummy_047 f)),
                      ((nb057_alpha_dummy_050), (nb057_alpha_dummy_051 f)),
                      ((nb057_alpha_dummy_000), a), ((nb057_alpha_dummy_001), f),
                      ((nb057_alpha_dummy_002), (nb057_alpha_dummy_003 f a))]
                    (syn_cnnc) (by simp only [fv_syn_cnnc]))))))))))

@[expose]
noncomputable def nb057_split_alpha_0037 (f : Var) (a : Var) :
    TAlphaWff
      [((nb057_alpha_dummy_082), (nb057_alpha_dummy_083 f)),
        ((nb057_alpha_dummy_056), (nb057_alpha_dummy_057 f)),
        ((nb057_alpha_dummy_045), (nb057_alpha_dummy_048 f)),
        ((nb057_alpha_dummy_044), (nb057_alpha_dummy_047 f)),
        ((nb057_alpha_dummy_050), (nb057_alpha_dummy_051 f)),
        ((nb057_alpha_dummy_000), a), ((nb057_alpha_dummy_001), f),
        ((nb057_alpha_dummy_002), (nb057_alpha_dummy_003 f a))]
      (Wff.imp (Wff.classMem (Class.cv (nb057_alpha_dummy_082))
          (Class.cab (nb057_alpha_dummy_052)
            (syn_wrex (nb057_alpha_dummy_053) (Class.cv (nb057_alpha_dummy_045))
              (Wff.classEq (Class.cv (nb057_alpha_dummy_052))
                (syn_cun (syn_cphi (Class.cv (nb057_alpha_dummy_053))) (syn_csn (syn_c0c)))))))
        (Wff.neg (Wff.classMem (Class.cv (nb057_alpha_dummy_082))
            (Class.cab (nb057_alpha_dummy_052)
              (syn_wrex (nb057_alpha_dummy_053) (Class.cv (nb057_alpha_dummy_045))
                (Wff.classEq (Class.cv (nb057_alpha_dummy_052))
                  (syn_cun (syn_cphi (Class.cv (nb057_alpha_dummy_053)))
                    (syn_csn (syn_c0c)))))))))
      (Wff.imp (Wff.classMem (Class.cv (nb057_alpha_dummy_083 f))
          (Class.cab (nb057_alpha_dummy_054 f)
            (syn_wrex (nb057_alpha_dummy_055 f) (Class.cv (nb057_alpha_dummy_048 f))
              (Wff.classEq (Class.cv (nb057_alpha_dummy_054 f))
                (syn_cun (syn_cphi (Class.cv (nb057_alpha_dummy_055 f)))
                  (syn_csn (syn_c0c))))))) (Wff.neg
          (Wff.classMem (Class.cv (nb057_alpha_dummy_083 f))
            (Class.cab (nb057_alpha_dummy_054 f)
              (syn_wrex (nb057_alpha_dummy_055 f) (Class.cv (nb057_alpha_dummy_048 f))
                (Wff.classEq (Class.cv (nb057_alpha_dummy_054 f))
                  (syn_cun (syn_cphi (Class.cv (nb057_alpha_dummy_055 f)))
                    (syn_csn (syn_c0c))))))))) :=
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
                (TAlphaVar.there (freshVar_injective (((Class.cv (nb057_alpha_dummy_044))).fv ∪
                      ((Class.cv (nb057_alpha_dummy_045))).fv) (by decide)) (freshVar_injective
                    (((Class.cv (nb057_alpha_dummy_047 f))).fv ∪
                      ((Class.cv (nb057_alpha_dummy_048 f))).fv) (by decide))
                  (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                        (TAlphaWff.neg (TAlphaWff.conj
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cab (TAlphaWff.ex
                                  (TAlphaWff.neg (nb057_split_alpha_0036 f a)))))
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cab (TAlphaWff.ex
                                  (TAlphaWff.neg (nb057_split_alpha_0036 f a)))))))))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                      (TAlphaClass.refl_of_closed
                        [((nb057_alpha_dummy_084), (nb057_alpha_dummy_085 f)),
                          ((nb057_alpha_dummy_053), (nb057_alpha_dummy_055 f)),
                          ((nb057_alpha_dummy_052), (nb057_alpha_dummy_054 f)),
                          ((nb057_alpha_dummy_082), (nb057_alpha_dummy_083 f)),
                          ((nb057_alpha_dummy_056), (nb057_alpha_dummy_057 f)),
                          ((nb057_alpha_dummy_045), (nb057_alpha_dummy_048 f)),
                          ((nb057_alpha_dummy_044), (nb057_alpha_dummy_047 f)),
                          ((nb057_alpha_dummy_050), (nb057_alpha_dummy_051 f)),
                          ((nb057_alpha_dummy_000), a), ((nb057_alpha_dummy_001), f),
                          ((nb057_alpha_dummy_002), (nb057_alpha_dummy_003 f a))]
                        (syn_ccompl (syn_csn (syn_c0c)))
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
                      (((Class.cv (nb057_alpha_dummy_044))).fv ∪
                        ((Class.cv (nb057_alpha_dummy_045))).fv) (by decide))
                    (freshVar_injective (((Class.cv (nb057_alpha_dummy_047 f))).fv ∪
                        ((Class.cv (nb057_alpha_dummy_048 f))).fv) (by decide))
                    (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cab (TAlphaWff.ex
                                    (TAlphaWff.neg (nb057_split_alpha_0036 f a)))))
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cab (TAlphaWff.ex
                                    (TAlphaWff.neg (nb057_split_alpha_0036 f a)))))))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.refl_of_closed
                          [((nb057_alpha_dummy_084), (nb057_alpha_dummy_085 f)),
                            ((nb057_alpha_dummy_053), (nb057_alpha_dummy_055 f)),
                            ((nb057_alpha_dummy_052), (nb057_alpha_dummy_054 f)),
                            ((nb057_alpha_dummy_082), (nb057_alpha_dummy_083 f)),
                            ((nb057_alpha_dummy_056), (nb057_alpha_dummy_057 f)),
                            ((nb057_alpha_dummy_045), (nb057_alpha_dummy_048 f)),
                            ((nb057_alpha_dummy_044), (nb057_alpha_dummy_047 f)),
                            ((nb057_alpha_dummy_050), (nb057_alpha_dummy_051 f)),
                            ((nb057_alpha_dummy_000), a), ((nb057_alpha_dummy_001), f),
                            ((nb057_alpha_dummy_002), (nb057_alpha_dummy_003 f a))]
                          (syn_ccompl (syn_csn (syn_c0c))) (by
                            simp only [fv_syn_ccompl, fv_syn_csn, fv_syn_c0c])))))))))))))

@[expose]
noncomputable def nb057_split_alpha_0038 (f : Var) (a : Var) :
    TAlphaWff
      [((nb057_alpha_dummy_104), (nb057_alpha_dummy_107 f)),
        ((nb057_alpha_dummy_103), (nb057_alpha_dummy_106 f)),
        ((nb057_alpha_dummy_102), (nb057_alpha_dummy_105 f)),
        ((nb057_alpha_dummy_100), (nb057_alpha_dummy_101 f)),
        ((nb057_alpha_dummy_096), (nb057_alpha_dummy_098 f)),
        ((nb057_alpha_dummy_097), (nb057_alpha_dummy_099 f)),
        ((nb057_alpha_dummy_089), (nb057_alpha_dummy_091 f)),
        ((nb057_alpha_dummy_088), (nb057_alpha_dummy_090 f)),
        ((nb057_alpha_dummy_094), (nb057_alpha_dummy_095 f)),
        ((nb057_alpha_dummy_092), (nb057_alpha_dummy_093 f)),
        ((nb057_alpha_dummy_046), (nb057_alpha_dummy_049 f)),
        ((nb057_alpha_dummy_045), (nb057_alpha_dummy_048 f)),
        ((nb057_alpha_dummy_044), (nb057_alpha_dummy_047 f)),
        ((nb057_alpha_dummy_050), (nb057_alpha_dummy_051 f)),
        ((nb057_alpha_dummy_000), a), ((nb057_alpha_dummy_001), f),
        ((nb057_alpha_dummy_002), (nb057_alpha_dummy_003 f a))]
      (Wff.imp (Wff.classEq
          (syn_cin (Class.cv (nb057_alpha_dummy_103)) (Class.cv (nb057_alpha_dummy_104)))
          (syn_c0)) (Wff.neg (Wff.classEq (Class.cv (nb057_alpha_dummy_102))
            (syn_cun (Class.cv (nb057_alpha_dummy_103)) (Class.cv (nb057_alpha_dummy_104))))))
      (Wff.imp (Wff.classEq (syn_cin (Class.cv (nb057_alpha_dummy_106 f))
            (Class.cv (nb057_alpha_dummy_107 f))) (syn_c0)) (Wff.neg
          (Wff.classEq (Class.cv (nb057_alpha_dummy_105 f))
            (syn_cun (Class.cv (nb057_alpha_dummy_106 f))
              (Class.cv (nb057_alpha_dummy_107 f)))))) :=
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
                                (((Class.cv (nb057_alpha_dummy_096))).fv ∪ ((syn_c1c)).fv)
                                (by decide)) (freshVar_injective
                                (((Class.cv (nb057_alpha_dummy_098 f))).fv ∪ ((syn_c1c)).fv)
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
                                (((Class.cv (nb057_alpha_dummy_096))).fv ∪ ((syn_c1c)).fv)
                                (by decide)) (freshVar_injective
                                (((Class.cv (nb057_alpha_dummy_098 f))).fv ∪ ((syn_c1c)).fv)
                                (by decide)) (TAlphaVar.here _ _ _))))))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0102) 0))
                          (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0103 f) 0))
                          (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0100) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0101 f) 0))
                            (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.refl_of_closed
        [((nb057_alpha_dummy_104), (nb057_alpha_dummy_107 f)),
          ((nb057_alpha_dummy_103), (nb057_alpha_dummy_106 f)),
          ((nb057_alpha_dummy_102), (nb057_alpha_dummy_105 f)),
          ((nb057_alpha_dummy_100), (nb057_alpha_dummy_101 f)),
          ((nb057_alpha_dummy_096), (nb057_alpha_dummy_098 f)),
          ((nb057_alpha_dummy_097), (nb057_alpha_dummy_099 f)),
          ((nb057_alpha_dummy_089), (nb057_alpha_dummy_091 f)),
          ((nb057_alpha_dummy_088), (nb057_alpha_dummy_090 f)),
          ((nb057_alpha_dummy_094), (nb057_alpha_dummy_095 f)),
          ((nb057_alpha_dummy_092), (nb057_alpha_dummy_093 f)),
          ((nb057_alpha_dummy_046), (nb057_alpha_dummy_049 f)),
          ((nb057_alpha_dummy_045), (nb057_alpha_dummy_048 f)),
          ((nb057_alpha_dummy_044), (nb057_alpha_dummy_047 f)),
          ((nb057_alpha_dummy_050), (nb057_alpha_dummy_051 f)),
          ((nb057_alpha_dummy_000), a), ((nb057_alpha_dummy_001), f),
          ((nb057_alpha_dummy_002), (nb057_alpha_dummy_003 f a))]
        (syn_c0) (by simp only [fv_syn_c0]))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv
          (TAlphaVar.there
            (freshVar_injective (((Class.cv (nb057_alpha_dummy_096))).fv ∪ ((syn_c1c)).fv)
              (by decide)) (freshVar_injective
              (((Class.cv (nb057_alpha_dummy_098 f))).fv ∪ ((syn_c1c)).fv) (by decide))
            (TAlphaVar.there (freshVar_injective
                (((Class.cv (nb057_alpha_dummy_096))).fv ∪ ((syn_c1c)).fv) (by decide))
              (freshVar_injective
                (((Class.cv (nb057_alpha_dummy_098 f))).fv ∪ ((syn_c1c)).fv) (by decide))
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
                                  (((Class.cv (nb057_alpha_dummy_096))).fv ∪ ((syn_c1c)).fv)
                                  (by decide)) (freshVar_injective
                                  (((Class.cv (nb057_alpha_dummy_098 f))).fv ∪ ((syn_c1c)).fv)
                                  (by decide)) (TAlphaVar.here _ _ _))))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0106) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0107 f) 0))
                            (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0104) 0))
                              (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0105 f) 0))
                              (TAlphaVar.there (freshVar_injective
                                  (((Class.cv (nb057_alpha_dummy_096))).fv ∪ ((syn_c1c)).fv)
                                  (by decide)) (freshVar_injective
                                  (((Class.cv (nb057_alpha_dummy_098 f))).fv ∪ ((syn_c1c)).fv)
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

@[expose]
noncomputable def nb057_split_alpha_0039 (f : Var) (a : Var) :
    TAlphaWff
      [((nb057_alpha_dummy_089), (nb057_alpha_dummy_091 f)),
        ((nb057_alpha_dummy_088), (nb057_alpha_dummy_090 f)),
        ((nb057_alpha_dummy_094), (nb057_alpha_dummy_095 f)),
        ((nb057_alpha_dummy_092), (nb057_alpha_dummy_093 f)),
        ((nb057_alpha_dummy_046), (nb057_alpha_dummy_049 f)),
        ((nb057_alpha_dummy_045), (nb057_alpha_dummy_048 f)),
        ((nb057_alpha_dummy_044), (nb057_alpha_dummy_047 f)),
        ((nb057_alpha_dummy_050), (nb057_alpha_dummy_051 f)),
        ((nb057_alpha_dummy_000), a), ((nb057_alpha_dummy_001), f),
        ((nb057_alpha_dummy_002), (nb057_alpha_dummy_003 f a))]
      (Wff.classEq (Class.cv (nb057_alpha_dummy_088))
        (syn_cphi (Class.cv (nb057_alpha_dummy_089))))
      (Wff.classEq (Class.cv (nb057_alpha_dummy_090 f))
        (syn_cphi (Class.cv (nb057_alpha_dummy_091 f)))) :=
  (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective
          (((Class.cv (nb057_alpha_dummy_044))).fv ∪ ((Class.cv (nb057_alpha_dummy_046))).fv)
          (by decide)) (freshVar_injective (((Class.cv (nb057_alpha_dummy_047 f))).fv ∪
            ((Class.cv (nb057_alpha_dummy_049 f))).fv) (by decide)) (TAlphaVar.here _ _ _)))
    (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
          (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
              (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0090) 0))
                (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0091 f) 0)) (TAlphaVar.there
                  (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0090) 1))
                  (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0091 f) 1))
                  (TAlphaVar.here _ _ _))))) (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there
                (freshVar_injective (((Class.cv (nb057_alpha_dummy_089))).fv) (by decide))
                (freshVar_injective (((Class.cv (nb057_alpha_dummy_091 f))).fv) (by decide))
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
                                  (TAlphaClass.refl_of_closed
                                    [((nb057_alpha_dummy_104), (nb057_alpha_dummy_107 f)),
                                      ((nb057_alpha_dummy_103), (nb057_alpha_dummy_106 f)),
                                      ((nb057_alpha_dummy_102), (nb057_alpha_dummy_105 f)),
                                      ((nb057_alpha_dummy_100), (nb057_alpha_dummy_101 f)),
                                      ((nb057_alpha_dummy_096), (nb057_alpha_dummy_098 f)),
                                      ((nb057_alpha_dummy_097), (nb057_alpha_dummy_099 f)),
                                      ((nb057_alpha_dummy_089), (nb057_alpha_dummy_091 f)),
                                      ((nb057_alpha_dummy_088), (nb057_alpha_dummy_090 f)),
                                      ((nb057_alpha_dummy_094), (nb057_alpha_dummy_095 f)),
                                      ((nb057_alpha_dummy_092), (nb057_alpha_dummy_093 f)),
                                      ((nb057_alpha_dummy_046), (nb057_alpha_dummy_049 f)),
                                      ((nb057_alpha_dummy_045), (nb057_alpha_dummy_048 f)),
                                      ((nb057_alpha_dummy_044), (nb057_alpha_dummy_047 f)),
                                      ((nb057_alpha_dummy_050), (nb057_alpha_dummy_051 f)),
                                      ((nb057_alpha_dummy_000), a),
                                      ((nb057_alpha_dummy_001), f), ((nb057_alpha_dummy_002),
                                        (nb057_alpha_dummy_003 f a))]
                                    (syn_c1c) (by simp only [fv_syn_c1c])))
                                (TAlphaWff.neg (nb057_split_alpha_0038 f a))))))))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there
                          (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0092) 0))
                          (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0093 f) 0))
                          (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
                        [((nb057_alpha_dummy_100), (nb057_alpha_dummy_101 f)),
                          ((nb057_alpha_dummy_096), (nb057_alpha_dummy_098 f)),
                          ((nb057_alpha_dummy_097), (nb057_alpha_dummy_099 f)),
                          ((nb057_alpha_dummy_089), (nb057_alpha_dummy_091 f)),
                          ((nb057_alpha_dummy_088), (nb057_alpha_dummy_090 f)),
                          ((nb057_alpha_dummy_094), (nb057_alpha_dummy_095 f)),
                          ((nb057_alpha_dummy_092), (nb057_alpha_dummy_093 f)),
                          ((nb057_alpha_dummy_046), (nb057_alpha_dummy_049 f)),
                          ((nb057_alpha_dummy_045), (nb057_alpha_dummy_048 f)),
                          ((nb057_alpha_dummy_044), (nb057_alpha_dummy_047 f)),
                          ((nb057_alpha_dummy_050), (nb057_alpha_dummy_051 f)),
                          ((nb057_alpha_dummy_000), a), ((nb057_alpha_dummy_001), f),
                          ((nb057_alpha_dummy_002), (nb057_alpha_dummy_003 f a))]
                        (syn_cnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
                  (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                      (TAlphaVar.there
                        (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0092) 0))
                        (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0093 f) 0))
                        (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.classMem
                      (TAlphaClass.cv (TAlphaVar.there
                          (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0092) 0))
                          (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0093 f) 0))
                          (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
                        [((nb057_alpha_dummy_100), (nb057_alpha_dummy_101 f)),
                          ((nb057_alpha_dummy_096), (nb057_alpha_dummy_098 f)),
                          ((nb057_alpha_dummy_097), (nb057_alpha_dummy_099 f)),
                          ((nb057_alpha_dummy_089), (nb057_alpha_dummy_091 f)),
                          ((nb057_alpha_dummy_088), (nb057_alpha_dummy_090 f)),
                          ((nb057_alpha_dummy_094), (nb057_alpha_dummy_095 f)),
                          ((nb057_alpha_dummy_092), (nb057_alpha_dummy_093 f)),
                          ((nb057_alpha_dummy_046), (nb057_alpha_dummy_049 f)),
                          ((nb057_alpha_dummy_045), (nb057_alpha_dummy_048 f)),
                          ((nb057_alpha_dummy_044), (nb057_alpha_dummy_047 f)),
                          ((nb057_alpha_dummy_050), (nb057_alpha_dummy_051 f)),
                          ((nb057_alpha_dummy_000), a), ((nb057_alpha_dummy_001), f),
                          ((nb057_alpha_dummy_002), (nb057_alpha_dummy_003 f a))]
                        (syn_cnnc) (by simp only [fv_syn_cnnc]))))))))))))


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

@[expose]
noncomputable def nb057_split_alpha_0040 (f : Var) (a : Var) :
    TAlphaWff
      [((nb057_alpha_dummy_104), (nb057_alpha_dummy_107 f)),
        ((nb057_alpha_dummy_103), (nb057_alpha_dummy_106 f)),
        ((nb057_alpha_dummy_102), (nb057_alpha_dummy_105 f)),
        ((nb057_alpha_dummy_100), (nb057_alpha_dummy_101 f)),
        ((nb057_alpha_dummy_096), (nb057_alpha_dummy_098 f)),
        ((nb057_alpha_dummy_097), (nb057_alpha_dummy_099 f)),
        ((nb057_alpha_dummy_122), (nb057_alpha_dummy_123 f)),
        ((nb057_alpha_dummy_120), (nb057_alpha_dummy_121 f)),
        ((nb057_alpha_dummy_089), (nb057_alpha_dummy_091 f)),
        ((nb057_alpha_dummy_088), (nb057_alpha_dummy_090 f)),
        ((nb057_alpha_dummy_118), (nb057_alpha_dummy_119 f)),
        ((nb057_alpha_dummy_092), (nb057_alpha_dummy_093 f)),
        ((nb057_alpha_dummy_046), (nb057_alpha_dummy_049 f)),
        ((nb057_alpha_dummy_045), (nb057_alpha_dummy_048 f)),
        ((nb057_alpha_dummy_044), (nb057_alpha_dummy_047 f)),
        ((nb057_alpha_dummy_050), (nb057_alpha_dummy_051 f)),
        ((nb057_alpha_dummy_000), a), ((nb057_alpha_dummy_001), f),
        ((nb057_alpha_dummy_002), (nb057_alpha_dummy_003 f a))]
      (Wff.imp (Wff.classEq
          (syn_cin (Class.cv (nb057_alpha_dummy_103)) (Class.cv (nb057_alpha_dummy_104)))
          (syn_c0)) (Wff.neg (Wff.classEq (Class.cv (nb057_alpha_dummy_102))
            (syn_cun (Class.cv (nb057_alpha_dummy_103)) (Class.cv (nb057_alpha_dummy_104))))))
      (Wff.imp (Wff.classEq (syn_cin (Class.cv (nb057_alpha_dummy_106 f))
            (Class.cv (nb057_alpha_dummy_107 f))) (syn_c0)) (Wff.neg
          (Wff.classEq (Class.cv (nb057_alpha_dummy_105 f))
            (syn_cun (Class.cv (nb057_alpha_dummy_106 f))
              (Class.cv (nb057_alpha_dummy_107 f)))))) :=
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
                                (((Class.cv (nb057_alpha_dummy_096))).fv ∪ ((syn_c1c)).fv)
                                (by decide)) (freshVar_injective
                                (((Class.cv (nb057_alpha_dummy_098 f))).fv ∪ ((syn_c1c)).fv)
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
                                (((Class.cv (nb057_alpha_dummy_096))).fv ∪ ((syn_c1c)).fv)
                                (by decide)) (freshVar_injective
                                (((Class.cv (nb057_alpha_dummy_098 f))).fv ∪ ((syn_c1c)).fv)
                                (by decide)) (TAlphaVar.here _ _ _))))))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0102) 0))
                          (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0103 f) 0))
                          (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0100) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0101 f) 0))
                            (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.refl_of_closed
        [((nb057_alpha_dummy_104), (nb057_alpha_dummy_107 f)),
          ((nb057_alpha_dummy_103), (nb057_alpha_dummy_106 f)),
          ((nb057_alpha_dummy_102), (nb057_alpha_dummy_105 f)),
          ((nb057_alpha_dummy_100), (nb057_alpha_dummy_101 f)),
          ((nb057_alpha_dummy_096), (nb057_alpha_dummy_098 f)),
          ((nb057_alpha_dummy_097), (nb057_alpha_dummy_099 f)),
          ((nb057_alpha_dummy_122), (nb057_alpha_dummy_123 f)),
          ((nb057_alpha_dummy_120), (nb057_alpha_dummy_121 f)),
          ((nb057_alpha_dummy_089), (nb057_alpha_dummy_091 f)),
          ((nb057_alpha_dummy_088), (nb057_alpha_dummy_090 f)),
          ((nb057_alpha_dummy_118), (nb057_alpha_dummy_119 f)),
          ((nb057_alpha_dummy_092), (nb057_alpha_dummy_093 f)),
          ((nb057_alpha_dummy_046), (nb057_alpha_dummy_049 f)),
          ((nb057_alpha_dummy_045), (nb057_alpha_dummy_048 f)),
          ((nb057_alpha_dummy_044), (nb057_alpha_dummy_047 f)),
          ((nb057_alpha_dummy_050), (nb057_alpha_dummy_051 f)),
          ((nb057_alpha_dummy_000), a), ((nb057_alpha_dummy_001), f),
          ((nb057_alpha_dummy_002), (nb057_alpha_dummy_003 f a))]
        (syn_c0) (by simp only [fv_syn_c0]))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv
          (TAlphaVar.there
            (freshVar_injective (((Class.cv (nb057_alpha_dummy_096))).fv ∪ ((syn_c1c)).fv)
              (by decide)) (freshVar_injective
              (((Class.cv (nb057_alpha_dummy_098 f))).fv ∪ ((syn_c1c)).fv) (by decide))
            (TAlphaVar.there (freshVar_injective
                (((Class.cv (nb057_alpha_dummy_096))).fv ∪ ((syn_c1c)).fv) (by decide))
              (freshVar_injective
                (((Class.cv (nb057_alpha_dummy_098 f))).fv ∪ ((syn_c1c)).fv) (by decide))
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
                                  (((Class.cv (nb057_alpha_dummy_096))).fv ∪ ((syn_c1c)).fv)
                                  (by decide)) (freshVar_injective
                                  (((Class.cv (nb057_alpha_dummy_098 f))).fv ∪ ((syn_c1c)).fv)
                                  (by decide)) (TAlphaVar.here _ _ _))))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0106) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0107 f) 0))
                            (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0104) 0))
                              (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0105 f) 0))
                              (TAlphaVar.there (freshVar_injective
                                  (((Class.cv (nb057_alpha_dummy_096))).fv ∪ ((syn_c1c)).fv)
                                  (by decide)) (freshVar_injective
                                  (((Class.cv (nb057_alpha_dummy_098 f))).fv ∪ ((syn_c1c)).fv)
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

@[expose]
noncomputable def nb057_split_alpha_0041 (f : Var) (a : Var) :
    TAlphaWff
      [((nb057_alpha_dummy_096), (nb057_alpha_dummy_098 f)),
        ((nb057_alpha_dummy_097), (nb057_alpha_dummy_099 f)),
        ((nb057_alpha_dummy_122), (nb057_alpha_dummy_123 f)),
        ((nb057_alpha_dummy_120), (nb057_alpha_dummy_121 f)),
        ((nb057_alpha_dummy_089), (nb057_alpha_dummy_091 f)),
        ((nb057_alpha_dummy_088), (nb057_alpha_dummy_090 f)),
        ((nb057_alpha_dummy_118), (nb057_alpha_dummy_119 f)),
        ((nb057_alpha_dummy_092), (nb057_alpha_dummy_093 f)),
        ((nb057_alpha_dummy_046), (nb057_alpha_dummy_049 f)),
        ((nb057_alpha_dummy_045), (nb057_alpha_dummy_048 f)),
        ((nb057_alpha_dummy_044), (nb057_alpha_dummy_047 f)),
        ((nb057_alpha_dummy_050), (nb057_alpha_dummy_051 f)),
        ((nb057_alpha_dummy_000), a), ((nb057_alpha_dummy_001), f),
        ((nb057_alpha_dummy_002), (nb057_alpha_dummy_003 f a))]
      (Wff.imp (Wff.classMem (Class.cv (nb057_alpha_dummy_096))
          (Class.cv (nb057_alpha_dummy_089))) (Wff.neg
          (Wff.classEq (Class.cv (nb057_alpha_dummy_097))
            (syn_cif (Wff.classMem (Class.cv (nb057_alpha_dummy_096)) (syn_cnnc))
              (syn_cplc (Class.cv (nb057_alpha_dummy_096)) (syn_c1c))
              (Class.cv (nb057_alpha_dummy_096))))))
      (Wff.imp (Wff.classMem (Class.cv (nb057_alpha_dummy_098 f))
          (Class.cv (nb057_alpha_dummy_091 f))) (Wff.neg
          (Wff.classEq (Class.cv (nb057_alpha_dummy_099 f))
            (syn_cif (Wff.classMem (Class.cv (nb057_alpha_dummy_098 f)) (syn_cnnc))
              (syn_cplc (Class.cv (nb057_alpha_dummy_098 f)) (syn_c1c))
              (Class.cv (nb057_alpha_dummy_098 f)))))) :=
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
            (freshVar_injective (((Class.cv (nb057_alpha_dummy_089))).fv) (by decide))
            (freshVar_injective (((Class.cv (nb057_alpha_dummy_091 f))).fv) (by decide))
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
                              (TAlphaClass.refl_of_closed
                                [((nb057_alpha_dummy_104), (nb057_alpha_dummy_107 f)),
                                  ((nb057_alpha_dummy_103), (nb057_alpha_dummy_106 f)),
                                  ((nb057_alpha_dummy_102), (nb057_alpha_dummy_105 f)),
                                  ((nb057_alpha_dummy_100), (nb057_alpha_dummy_101 f)),
                                  ((nb057_alpha_dummy_096), (nb057_alpha_dummy_098 f)),
                                  ((nb057_alpha_dummy_097), (nb057_alpha_dummy_099 f)),
                                  ((nb057_alpha_dummy_122), (nb057_alpha_dummy_123 f)),
                                  ((nb057_alpha_dummy_120), (nb057_alpha_dummy_121 f)),
                                  ((nb057_alpha_dummy_089), (nb057_alpha_dummy_091 f)),
                                  ((nb057_alpha_dummy_088), (nb057_alpha_dummy_090 f)),
                                  ((nb057_alpha_dummy_118), (nb057_alpha_dummy_119 f)),
                                  ((nb057_alpha_dummy_092), (nb057_alpha_dummy_093 f)),
                                  ((nb057_alpha_dummy_046), (nb057_alpha_dummy_049 f)),
                                  ((nb057_alpha_dummy_045), (nb057_alpha_dummy_048 f)),
                                  ((nb057_alpha_dummy_044), (nb057_alpha_dummy_047 f)),
                                  ((nb057_alpha_dummy_050), (nb057_alpha_dummy_051 f)),
                                  ((nb057_alpha_dummy_000), a), ((nb057_alpha_dummy_001), f),
                                  ((nb057_alpha_dummy_002), (nb057_alpha_dummy_003 f a))]
                                (syn_c1c) (by simp only [fv_syn_c1c])))
                            (TAlphaWff.neg (nb057_split_alpha_0040 f a))))))))
                (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there
                      (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0092) 0))
                      (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0093 f) 0))
                      (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
                    [((nb057_alpha_dummy_100), (nb057_alpha_dummy_101 f)),
                      ((nb057_alpha_dummy_096), (nb057_alpha_dummy_098 f)),
                      ((nb057_alpha_dummy_097), (nb057_alpha_dummy_099 f)),
                      ((nb057_alpha_dummy_122), (nb057_alpha_dummy_123 f)),
                      ((nb057_alpha_dummy_120), (nb057_alpha_dummy_121 f)),
                      ((nb057_alpha_dummy_089), (nb057_alpha_dummy_091 f)),
                      ((nb057_alpha_dummy_088), (nb057_alpha_dummy_090 f)),
                      ((nb057_alpha_dummy_118), (nb057_alpha_dummy_119 f)),
                      ((nb057_alpha_dummy_092), (nb057_alpha_dummy_093 f)),
                      ((nb057_alpha_dummy_046), (nb057_alpha_dummy_049 f)),
                      ((nb057_alpha_dummy_045), (nb057_alpha_dummy_048 f)),
                      ((nb057_alpha_dummy_044), (nb057_alpha_dummy_047 f)),
                      ((nb057_alpha_dummy_050), (nb057_alpha_dummy_051 f)),
                      ((nb057_alpha_dummy_000), a), ((nb057_alpha_dummy_001), f),
                      ((nb057_alpha_dummy_002), (nb057_alpha_dummy_003 f a))]
                    (syn_cnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                  (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0092) 0))
                    (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0093 f) 0))
                    (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv
                    (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0092) 0))
                      (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0093 f) 0))
                      (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
                    [((nb057_alpha_dummy_100), (nb057_alpha_dummy_101 f)),
                      ((nb057_alpha_dummy_096), (nb057_alpha_dummy_098 f)),
                      ((nb057_alpha_dummy_097), (nb057_alpha_dummy_099 f)),
                      ((nb057_alpha_dummy_122), (nb057_alpha_dummy_123 f)),
                      ((nb057_alpha_dummy_120), (nb057_alpha_dummy_121 f)),
                      ((nb057_alpha_dummy_089), (nb057_alpha_dummy_091 f)),
                      ((nb057_alpha_dummy_088), (nb057_alpha_dummy_090 f)),
                      ((nb057_alpha_dummy_118), (nb057_alpha_dummy_119 f)),
                      ((nb057_alpha_dummy_092), (nb057_alpha_dummy_093 f)),
                      ((nb057_alpha_dummy_046), (nb057_alpha_dummy_049 f)),
                      ((nb057_alpha_dummy_045), (nb057_alpha_dummy_048 f)),
                      ((nb057_alpha_dummy_044), (nb057_alpha_dummy_047 f)),
                      ((nb057_alpha_dummy_050), (nb057_alpha_dummy_051 f)),
                      ((nb057_alpha_dummy_000), a), ((nb057_alpha_dummy_001), f),
                      ((nb057_alpha_dummy_002), (nb057_alpha_dummy_003 f a))]
                    (syn_cnnc) (by simp only [fv_syn_cnnc]))))))))))

@[expose]
noncomputable def nb057_split_alpha_0042 (f : Var) (a : Var) :
    TAlphaWff
      [((nb057_alpha_dummy_118), (nb057_alpha_dummy_119 f)),
        ((nb057_alpha_dummy_092), (nb057_alpha_dummy_093 f)),
        ((nb057_alpha_dummy_046), (nb057_alpha_dummy_049 f)),
        ((nb057_alpha_dummy_045), (nb057_alpha_dummy_048 f)),
        ((nb057_alpha_dummy_044), (nb057_alpha_dummy_047 f)),
        ((nb057_alpha_dummy_050), (nb057_alpha_dummy_051 f)),
        ((nb057_alpha_dummy_000), a), ((nb057_alpha_dummy_001), f),
        ((nb057_alpha_dummy_002), (nb057_alpha_dummy_003 f a))]
      (Wff.imp (Wff.classMem (Class.cv (nb057_alpha_dummy_118))
          (Class.cab (nb057_alpha_dummy_088)
            (syn_wrex (nb057_alpha_dummy_089) (Class.cv (nb057_alpha_dummy_046))
              (Wff.classEq (Class.cv (nb057_alpha_dummy_088))
                (syn_cun (syn_cphi (Class.cv (nb057_alpha_dummy_089))) (syn_csn (syn_c0c)))))))
        (Wff.neg (Wff.classMem (Class.cv (nb057_alpha_dummy_118))
            (Class.cab (nb057_alpha_dummy_088)
              (syn_wrex (nb057_alpha_dummy_089) (Class.cv (nb057_alpha_dummy_046))
                (Wff.classEq (Class.cv (nb057_alpha_dummy_088))
                  (syn_cun (syn_cphi (Class.cv (nb057_alpha_dummy_089)))
                    (syn_csn (syn_c0c)))))))))
      (Wff.imp (Wff.classMem (Class.cv (nb057_alpha_dummy_119 f))
          (Class.cab (nb057_alpha_dummy_090 f)
            (syn_wrex (nb057_alpha_dummy_091 f) (Class.cv (nb057_alpha_dummy_049 f))
              (Wff.classEq (Class.cv (nb057_alpha_dummy_090 f))
                (syn_cun (syn_cphi (Class.cv (nb057_alpha_dummy_091 f)))
                  (syn_csn (syn_c0c))))))) (Wff.neg
          (Wff.classMem (Class.cv (nb057_alpha_dummy_119 f))
            (Class.cab (nb057_alpha_dummy_090 f)
              (syn_wrex (nb057_alpha_dummy_091 f) (Class.cv (nb057_alpha_dummy_049 f))
                (Wff.classEq (Class.cv (nb057_alpha_dummy_090 f))
                  (syn_cun (syn_cphi (Class.cv (nb057_alpha_dummy_091 f)))
                    (syn_csn (syn_c0c))))))))) :=
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
                (TAlphaVar.there (freshVar_injective (((Class.cv (nb057_alpha_dummy_044))).fv ∪
                      ((Class.cv (nb057_alpha_dummy_046))).fv) (by decide)) (freshVar_injective
                    (((Class.cv (nb057_alpha_dummy_047 f))).fv ∪
                      ((Class.cv (nb057_alpha_dummy_049 f))).fv) (by decide))
                  (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                        (TAlphaWff.neg (TAlphaWff.conj
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cab (TAlphaWff.ex
                                  (TAlphaWff.neg (nb057_split_alpha_0041 f a)))))
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cab (TAlphaWff.ex
                                  (TAlphaWff.neg (nb057_split_alpha_0041 f a)))))))))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                      (TAlphaClass.refl_of_closed
                        [((nb057_alpha_dummy_120), (nb057_alpha_dummy_121 f)),
                          ((nb057_alpha_dummy_089), (nb057_alpha_dummy_091 f)),
                          ((nb057_alpha_dummy_088), (nb057_alpha_dummy_090 f)),
                          ((nb057_alpha_dummy_118), (nb057_alpha_dummy_119 f)),
                          ((nb057_alpha_dummy_092), (nb057_alpha_dummy_093 f)),
                          ((nb057_alpha_dummy_046), (nb057_alpha_dummy_049 f)),
                          ((nb057_alpha_dummy_045), (nb057_alpha_dummy_048 f)),
                          ((nb057_alpha_dummy_044), (nb057_alpha_dummy_047 f)),
                          ((nb057_alpha_dummy_050), (nb057_alpha_dummy_051 f)),
                          ((nb057_alpha_dummy_000), a), ((nb057_alpha_dummy_001), f),
                          ((nb057_alpha_dummy_002), (nb057_alpha_dummy_003 f a))]
                        (syn_ccompl (syn_csn (syn_c0c)))
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
                      (((Class.cv (nb057_alpha_dummy_044))).fv ∪
                        ((Class.cv (nb057_alpha_dummy_046))).fv) (by decide))
                    (freshVar_injective (((Class.cv (nb057_alpha_dummy_047 f))).fv ∪
                        ((Class.cv (nb057_alpha_dummy_049 f))).fv) (by decide))
                    (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cab (TAlphaWff.ex
                                    (TAlphaWff.neg (nb057_split_alpha_0041 f a)))))
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cab (TAlphaWff.ex
                                    (TAlphaWff.neg (nb057_split_alpha_0041 f a)))))))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.refl_of_closed
                          [((nb057_alpha_dummy_120), (nb057_alpha_dummy_121 f)),
                            ((nb057_alpha_dummy_089), (nb057_alpha_dummy_091 f)),
                            ((nb057_alpha_dummy_088), (nb057_alpha_dummy_090 f)),
                            ((nb057_alpha_dummy_118), (nb057_alpha_dummy_119 f)),
                            ((nb057_alpha_dummy_092), (nb057_alpha_dummy_093 f)),
                            ((nb057_alpha_dummy_046), (nb057_alpha_dummy_049 f)),
                            ((nb057_alpha_dummy_045), (nb057_alpha_dummy_048 f)),
                            ((nb057_alpha_dummy_044), (nb057_alpha_dummy_047 f)),
                            ((nb057_alpha_dummy_050), (nb057_alpha_dummy_051 f)),
                            ((nb057_alpha_dummy_000), a), ((nb057_alpha_dummy_001), f),
                            ((nb057_alpha_dummy_002), (nb057_alpha_dummy_003 f a))]
                          (syn_ccompl (syn_csn (syn_c0c))) (by
                            simp only [fv_syn_ccompl, fv_syn_csn, fv_syn_c0c])))))))))))))

@[expose]
noncomputable def nb057_split_alpha_0043 (f : Var) (a : Var) :
    TAlphaWff
      [((nb057_alpha_dummy_146), (nb057_alpha_dummy_149 f)),
        ((nb057_alpha_dummy_145), (nb057_alpha_dummy_148 f)),
        ((nb057_alpha_dummy_144), (nb057_alpha_dummy_147 f)),
        ((nb057_alpha_dummy_142), (nb057_alpha_dummy_143 f)),
        ((nb057_alpha_dummy_138), (nb057_alpha_dummy_140 f)),
        ((nb057_alpha_dummy_139), (nb057_alpha_dummy_141 f)),
        ((nb057_alpha_dummy_131), (nb057_alpha_dummy_133 f)),
        ((nb057_alpha_dummy_130), (nb057_alpha_dummy_132 f)),
        ((nb057_alpha_dummy_136), (nb057_alpha_dummy_137 f)),
        ((nb057_alpha_dummy_134), (nb057_alpha_dummy_135 f)),
        ((nb057_alpha_dummy_125), (nb057_alpha_dummy_127 f)),
        ((nb057_alpha_dummy_124), (nb057_alpha_dummy_126 f)),
        ((nb057_alpha_dummy_128), (nb057_alpha_dummy_129 f)),
        ((nb057_alpha_dummy_046), (nb057_alpha_dummy_049 f)),
        ((nb057_alpha_dummy_045), (nb057_alpha_dummy_048 f)),
        ((nb057_alpha_dummy_044), (nb057_alpha_dummy_047 f)),
        ((nb057_alpha_dummy_050), (nb057_alpha_dummy_051 f)),
        ((nb057_alpha_dummy_000), a), ((nb057_alpha_dummy_001), f),
        ((nb057_alpha_dummy_002), (nb057_alpha_dummy_003 f a))]
      (Wff.imp (Wff.classEq
          (syn_cin (Class.cv (nb057_alpha_dummy_145)) (Class.cv (nb057_alpha_dummy_146)))
          (syn_c0)) (Wff.neg (Wff.classEq (Class.cv (nb057_alpha_dummy_144))
            (syn_cun (Class.cv (nb057_alpha_dummy_145)) (Class.cv (nb057_alpha_dummy_146))))))
      (Wff.imp (Wff.classEq (syn_cin (Class.cv (nb057_alpha_dummy_148 f))
            (Class.cv (nb057_alpha_dummy_149 f))) (syn_c0)) (Wff.neg
          (Wff.classEq (Class.cv (nb057_alpha_dummy_147 f))
            (syn_cun (Class.cv (nb057_alpha_dummy_148 f))
              (Class.cv (nb057_alpha_dummy_149 f)))))) :=
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
                                (((Class.cv (nb057_alpha_dummy_138))).fv ∪ ((syn_c1c)).fv)
                                (by decide)) (freshVar_injective
                                (((Class.cv (nb057_alpha_dummy_140 f))).fv ∪ ((syn_c1c)).fv)
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
                                (((Class.cv (nb057_alpha_dummy_138))).fv ∪ ((syn_c1c)).fv)
                                (by decide)) (freshVar_injective
                                (((Class.cv (nb057_alpha_dummy_140 f))).fv ∪ ((syn_c1c)).fv)
                                (by decide)) (TAlphaVar.here _ _ _))))))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0144) 0))
                          (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0145 f) 0))
                          (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0142) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0143 f) 0))
                            (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.refl_of_closed
        [((nb057_alpha_dummy_146), (nb057_alpha_dummy_149 f)),
          ((nb057_alpha_dummy_145), (nb057_alpha_dummy_148 f)),
          ((nb057_alpha_dummy_144), (nb057_alpha_dummy_147 f)),
          ((nb057_alpha_dummy_142), (nb057_alpha_dummy_143 f)),
          ((nb057_alpha_dummy_138), (nb057_alpha_dummy_140 f)),
          ((nb057_alpha_dummy_139), (nb057_alpha_dummy_141 f)),
          ((nb057_alpha_dummy_131), (nb057_alpha_dummy_133 f)),
          ((nb057_alpha_dummy_130), (nb057_alpha_dummy_132 f)),
          ((nb057_alpha_dummy_136), (nb057_alpha_dummy_137 f)),
          ((nb057_alpha_dummy_134), (nb057_alpha_dummy_135 f)),
          ((nb057_alpha_dummy_125), (nb057_alpha_dummy_127 f)),
          ((nb057_alpha_dummy_124), (nb057_alpha_dummy_126 f)),
          ((nb057_alpha_dummy_128), (nb057_alpha_dummy_129 f)),
          ((nb057_alpha_dummy_046), (nb057_alpha_dummy_049 f)),
          ((nb057_alpha_dummy_045), (nb057_alpha_dummy_048 f)),
          ((nb057_alpha_dummy_044), (nb057_alpha_dummy_047 f)),
          ((nb057_alpha_dummy_050), (nb057_alpha_dummy_051 f)),
          ((nb057_alpha_dummy_000), a), ((nb057_alpha_dummy_001), f),
          ((nb057_alpha_dummy_002), (nb057_alpha_dummy_003 f a))]
        (syn_c0) (by simp only [fv_syn_c0]))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv
          (TAlphaVar.there
            (freshVar_injective (((Class.cv (nb057_alpha_dummy_138))).fv ∪ ((syn_c1c)).fv)
              (by decide)) (freshVar_injective
              (((Class.cv (nb057_alpha_dummy_140 f))).fv ∪ ((syn_c1c)).fv) (by decide))
            (TAlphaVar.there (freshVar_injective
                (((Class.cv (nb057_alpha_dummy_138))).fv ∪ ((syn_c1c)).fv) (by decide))
              (freshVar_injective
                (((Class.cv (nb057_alpha_dummy_140 f))).fv ∪ ((syn_c1c)).fv) (by decide))
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
                                  (((Class.cv (nb057_alpha_dummy_138))).fv ∪ ((syn_c1c)).fv)
                                  (by decide)) (freshVar_injective
                                  (((Class.cv (nb057_alpha_dummy_140 f))).fv ∪ ((syn_c1c)).fv)
                                  (by decide)) (TAlphaVar.here _ _ _))))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0148) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0149 f) 0))
                            (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0146) 0))
                              (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0147 f) 0))
                              (TAlphaVar.there (freshVar_injective
                                  (((Class.cv (nb057_alpha_dummy_138))).fv ∪ ((syn_c1c)).fv)
                                  (by decide)) (freshVar_injective
                                  (((Class.cv (nb057_alpha_dummy_140 f))).fv ∪ ((syn_c1c)).fv)
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

@[expose]
noncomputable def nb057_split_alpha_0044 (f : Var) (a : Var) :
    TAlphaWff
      [((nb057_alpha_dummy_138), (nb057_alpha_dummy_140 f)),
        ((nb057_alpha_dummy_139), (nb057_alpha_dummy_141 f)),
        ((nb057_alpha_dummy_131), (nb057_alpha_dummy_133 f)),
        ((nb057_alpha_dummy_130), (nb057_alpha_dummy_132 f)),
        ((nb057_alpha_dummy_136), (nb057_alpha_dummy_137 f)),
        ((nb057_alpha_dummy_134), (nb057_alpha_dummy_135 f)),
        ((nb057_alpha_dummy_125), (nb057_alpha_dummy_127 f)),
        ((nb057_alpha_dummy_124), (nb057_alpha_dummy_126 f)),
        ((nb057_alpha_dummy_128), (nb057_alpha_dummy_129 f)),
        ((nb057_alpha_dummy_046), (nb057_alpha_dummy_049 f)),
        ((nb057_alpha_dummy_045), (nb057_alpha_dummy_048 f)),
        ((nb057_alpha_dummy_044), (nb057_alpha_dummy_047 f)),
        ((nb057_alpha_dummy_050), (nb057_alpha_dummy_051 f)),
        ((nb057_alpha_dummy_000), a), ((nb057_alpha_dummy_001), f),
        ((nb057_alpha_dummy_002), (nb057_alpha_dummy_003 f a))]
      (Wff.imp (Wff.classMem (Class.cv (nb057_alpha_dummy_138))
          (Class.cv (nb057_alpha_dummy_131))) (Wff.neg
          (Wff.classEq (Class.cv (nb057_alpha_dummy_139))
            (syn_cif (Wff.classMem (Class.cv (nb057_alpha_dummy_138)) (syn_cnnc))
              (syn_cplc (Class.cv (nb057_alpha_dummy_138)) (syn_c1c))
              (Class.cv (nb057_alpha_dummy_138))))))
      (Wff.imp (Wff.classMem (Class.cv (nb057_alpha_dummy_140 f))
          (Class.cv (nb057_alpha_dummy_133 f))) (Wff.neg
          (Wff.classEq (Class.cv (nb057_alpha_dummy_141 f))
            (syn_cif (Wff.classMem (Class.cv (nb057_alpha_dummy_140 f)) (syn_cnnc))
              (syn_cplc (Class.cv (nb057_alpha_dummy_140 f)) (syn_c1c))
              (Class.cv (nb057_alpha_dummy_140 f)))))) :=
  (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0132) 0))
          (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0133 f) 0))
          (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0132) 1))
            (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0133 f) 1))
            (TAlphaVar.here _ _ _))))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv
          (TAlphaVar.there
            (freshVar_injective (((Class.cv (nb057_alpha_dummy_131))).fv) (by decide))
            (freshVar_injective (((Class.cv (nb057_alpha_dummy_133 f))).fv) (by decide))
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
                              (TAlphaClass.refl_of_closed
                                [((nb057_alpha_dummy_146), (nb057_alpha_dummy_149 f)),
                                  ((nb057_alpha_dummy_145), (nb057_alpha_dummy_148 f)),
                                  ((nb057_alpha_dummy_144), (nb057_alpha_dummy_147 f)),
                                  ((nb057_alpha_dummy_142), (nb057_alpha_dummy_143 f)),
                                  ((nb057_alpha_dummy_138), (nb057_alpha_dummy_140 f)),
                                  ((nb057_alpha_dummy_139), (nb057_alpha_dummy_141 f)),
                                  ((nb057_alpha_dummy_131), (nb057_alpha_dummy_133 f)),
                                  ((nb057_alpha_dummy_130), (nb057_alpha_dummy_132 f)),
                                  ((nb057_alpha_dummy_136), (nb057_alpha_dummy_137 f)),
                                  ((nb057_alpha_dummy_134), (nb057_alpha_dummy_135 f)),
                                  ((nb057_alpha_dummy_125), (nb057_alpha_dummy_127 f)),
                                  ((nb057_alpha_dummy_124), (nb057_alpha_dummy_126 f)),
                                  ((nb057_alpha_dummy_128), (nb057_alpha_dummy_129 f)),
                                  ((nb057_alpha_dummy_046), (nb057_alpha_dummy_049 f)),
                                  ((nb057_alpha_dummy_045), (nb057_alpha_dummy_048 f)),
                                  ((nb057_alpha_dummy_044), (nb057_alpha_dummy_047 f)),
                                  ((nb057_alpha_dummy_050), (nb057_alpha_dummy_051 f)),
                                  ((nb057_alpha_dummy_000), a), ((nb057_alpha_dummy_001), f),
                                  ((nb057_alpha_dummy_002), (nb057_alpha_dummy_003 f a))]
                                (syn_c1c) (by simp only [fv_syn_c1c])))
                            (TAlphaWff.neg (nb057_split_alpha_0043 f a))))))))
                (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there
                      (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0134) 0))
                      (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0135 f) 0))
                      (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
                    [((nb057_alpha_dummy_142), (nb057_alpha_dummy_143 f)),
                      ((nb057_alpha_dummy_138), (nb057_alpha_dummy_140 f)),
                      ((nb057_alpha_dummy_139), (nb057_alpha_dummy_141 f)),
                      ((nb057_alpha_dummy_131), (nb057_alpha_dummy_133 f)),
                      ((nb057_alpha_dummy_130), (nb057_alpha_dummy_132 f)),
                      ((nb057_alpha_dummy_136), (nb057_alpha_dummy_137 f)),
                      ((nb057_alpha_dummy_134), (nb057_alpha_dummy_135 f)),
                      ((nb057_alpha_dummy_125), (nb057_alpha_dummy_127 f)),
                      ((nb057_alpha_dummy_124), (nb057_alpha_dummy_126 f)),
                      ((nb057_alpha_dummy_128), (nb057_alpha_dummy_129 f)),
                      ((nb057_alpha_dummy_046), (nb057_alpha_dummy_049 f)),
                      ((nb057_alpha_dummy_045), (nb057_alpha_dummy_048 f)),
                      ((nb057_alpha_dummy_044), (nb057_alpha_dummy_047 f)),
                      ((nb057_alpha_dummy_050), (nb057_alpha_dummy_051 f)),
                      ((nb057_alpha_dummy_000), a), ((nb057_alpha_dummy_001), f),
                      ((nb057_alpha_dummy_002), (nb057_alpha_dummy_003 f a))]
                    (syn_cnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                  (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0134) 0))
                    (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0135 f) 0))
                    (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv
                    (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0134) 0))
                      (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0135 f) 0))
                      (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
                    [((nb057_alpha_dummy_142), (nb057_alpha_dummy_143 f)),
                      ((nb057_alpha_dummy_138), (nb057_alpha_dummy_140 f)),
                      ((nb057_alpha_dummy_139), (nb057_alpha_dummy_141 f)),
                      ((nb057_alpha_dummy_131), (nb057_alpha_dummy_133 f)),
                      ((nb057_alpha_dummy_130), (nb057_alpha_dummy_132 f)),
                      ((nb057_alpha_dummy_136), (nb057_alpha_dummy_137 f)),
                      ((nb057_alpha_dummy_134), (nb057_alpha_dummy_135 f)),
                      ((nb057_alpha_dummy_125), (nb057_alpha_dummy_127 f)),
                      ((nb057_alpha_dummy_124), (nb057_alpha_dummy_126 f)),
                      ((nb057_alpha_dummy_128), (nb057_alpha_dummy_129 f)),
                      ((nb057_alpha_dummy_046), (nb057_alpha_dummy_049 f)),
                      ((nb057_alpha_dummy_045), (nb057_alpha_dummy_048 f)),
                      ((nb057_alpha_dummy_044), (nb057_alpha_dummy_047 f)),
                      ((nb057_alpha_dummy_050), (nb057_alpha_dummy_051 f)),
                      ((nb057_alpha_dummy_000), a), ((nb057_alpha_dummy_001), f),
                      ((nb057_alpha_dummy_002), (nb057_alpha_dummy_003 f a))]
                    (syn_cnnc) (by simp only [fv_syn_cnnc]))))))))))

@[expose]
noncomputable def nb057_split_alpha_0045 (f : Var) (a : Var) :
    TAlphaWff
      [((nb057_alpha_dummy_146), (nb057_alpha_dummy_149 f)),
        ((nb057_alpha_dummy_145), (nb057_alpha_dummy_148 f)),
        ((nb057_alpha_dummy_144), (nb057_alpha_dummy_147 f)),
        ((nb057_alpha_dummy_142), (nb057_alpha_dummy_143 f)),
        ((nb057_alpha_dummy_138), (nb057_alpha_dummy_140 f)),
        ((nb057_alpha_dummy_139), (nb057_alpha_dummy_141 f)),
        ((nb057_alpha_dummy_164), (nb057_alpha_dummy_165 f)),
        ((nb057_alpha_dummy_162), (nb057_alpha_dummy_163 f)),
        ((nb057_alpha_dummy_131), (nb057_alpha_dummy_133 f)),
        ((nb057_alpha_dummy_130), (nb057_alpha_dummy_132 f)),
        ((nb057_alpha_dummy_160), (nb057_alpha_dummy_161 f)),
        ((nb057_alpha_dummy_134), (nb057_alpha_dummy_135 f)),
        ((nb057_alpha_dummy_125), (nb057_alpha_dummy_127 f)),
        ((nb057_alpha_dummy_124), (nb057_alpha_dummy_126 f)),
        ((nb057_alpha_dummy_128), (nb057_alpha_dummy_129 f)),
        ((nb057_alpha_dummy_046), (nb057_alpha_dummy_049 f)),
        ((nb057_alpha_dummy_045), (nb057_alpha_dummy_048 f)),
        ((nb057_alpha_dummy_044), (nb057_alpha_dummy_047 f)),
        ((nb057_alpha_dummy_050), (nb057_alpha_dummy_051 f)),
        ((nb057_alpha_dummy_000), a), ((nb057_alpha_dummy_001), f),
        ((nb057_alpha_dummy_002), (nb057_alpha_dummy_003 f a))]
      (Wff.imp (Wff.classEq
          (syn_cin (Class.cv (nb057_alpha_dummy_145)) (Class.cv (nb057_alpha_dummy_146)))
          (syn_c0)) (Wff.neg (Wff.classEq (Class.cv (nb057_alpha_dummy_144))
            (syn_cun (Class.cv (nb057_alpha_dummy_145)) (Class.cv (nb057_alpha_dummy_146))))))
      (Wff.imp (Wff.classEq (syn_cin (Class.cv (nb057_alpha_dummy_148 f))
            (Class.cv (nb057_alpha_dummy_149 f))) (syn_c0)) (Wff.neg
          (Wff.classEq (Class.cv (nb057_alpha_dummy_147 f))
            (syn_cun (Class.cv (nb057_alpha_dummy_148 f))
              (Class.cv (nb057_alpha_dummy_149 f)))))) :=
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
                                (((Class.cv (nb057_alpha_dummy_138))).fv ∪ ((syn_c1c)).fv)
                                (by decide)) (freshVar_injective
                                (((Class.cv (nb057_alpha_dummy_140 f))).fv ∪ ((syn_c1c)).fv)
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
                                (((Class.cv (nb057_alpha_dummy_138))).fv ∪ ((syn_c1c)).fv)
                                (by decide)) (freshVar_injective
                                (((Class.cv (nb057_alpha_dummy_140 f))).fv ∪ ((syn_c1c)).fv)
                                (by decide)) (TAlphaVar.here _ _ _))))))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0144) 0))
                          (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0145 f) 0))
                          (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0142) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0143 f) 0))
                            (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.refl_of_closed
        [((nb057_alpha_dummy_146), (nb057_alpha_dummy_149 f)),
          ((nb057_alpha_dummy_145), (nb057_alpha_dummy_148 f)),
          ((nb057_alpha_dummy_144), (nb057_alpha_dummy_147 f)),
          ((nb057_alpha_dummy_142), (nb057_alpha_dummy_143 f)),
          ((nb057_alpha_dummy_138), (nb057_alpha_dummy_140 f)),
          ((nb057_alpha_dummy_139), (nb057_alpha_dummy_141 f)),
          ((nb057_alpha_dummy_164), (nb057_alpha_dummy_165 f)),
          ((nb057_alpha_dummy_162), (nb057_alpha_dummy_163 f)),
          ((nb057_alpha_dummy_131), (nb057_alpha_dummy_133 f)),
          ((nb057_alpha_dummy_130), (nb057_alpha_dummy_132 f)),
          ((nb057_alpha_dummy_160), (nb057_alpha_dummy_161 f)),
          ((nb057_alpha_dummy_134), (nb057_alpha_dummy_135 f)),
          ((nb057_alpha_dummy_125), (nb057_alpha_dummy_127 f)),
          ((nb057_alpha_dummy_124), (nb057_alpha_dummy_126 f)),
          ((nb057_alpha_dummy_128), (nb057_alpha_dummy_129 f)),
          ((nb057_alpha_dummy_046), (nb057_alpha_dummy_049 f)),
          ((nb057_alpha_dummy_045), (nb057_alpha_dummy_048 f)),
          ((nb057_alpha_dummy_044), (nb057_alpha_dummy_047 f)),
          ((nb057_alpha_dummy_050), (nb057_alpha_dummy_051 f)),
          ((nb057_alpha_dummy_000), a), ((nb057_alpha_dummy_001), f),
          ((nb057_alpha_dummy_002), (nb057_alpha_dummy_003 f a))]
        (syn_c0) (by simp only [fv_syn_c0]))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv
          (TAlphaVar.there
            (freshVar_injective (((Class.cv (nb057_alpha_dummy_138))).fv ∪ ((syn_c1c)).fv)
              (by decide)) (freshVar_injective
              (((Class.cv (nb057_alpha_dummy_140 f))).fv ∪ ((syn_c1c)).fv) (by decide))
            (TAlphaVar.there (freshVar_injective
                (((Class.cv (nb057_alpha_dummy_138))).fv ∪ ((syn_c1c)).fv) (by decide))
              (freshVar_injective
                (((Class.cv (nb057_alpha_dummy_140 f))).fv ∪ ((syn_c1c)).fv) (by decide))
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
                                  (((Class.cv (nb057_alpha_dummy_138))).fv ∪ ((syn_c1c)).fv)
                                  (by decide)) (freshVar_injective
                                  (((Class.cv (nb057_alpha_dummy_140 f))).fv ∪ ((syn_c1c)).fv)
                                  (by decide)) (TAlphaVar.here _ _ _))))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0148) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0149 f) 0))
                            (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0146) 0))
                              (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0147 f) 0))
                              (TAlphaVar.there (freshVar_injective
                                  (((Class.cv (nb057_alpha_dummy_138))).fv ∪ ((syn_c1c)).fv)
                                  (by decide)) (freshVar_injective
                                  (((Class.cv (nb057_alpha_dummy_140 f))).fv ∪ ((syn_c1c)).fv)
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

@[expose]
noncomputable def nb057_split_alpha_0046 (f : Var) (a : Var) :
    TAlphaWff
      [((nb057_alpha_dummy_138), (nb057_alpha_dummy_140 f)),
        ((nb057_alpha_dummy_139), (nb057_alpha_dummy_141 f)),
        ((nb057_alpha_dummy_164), (nb057_alpha_dummy_165 f)),
        ((nb057_alpha_dummy_162), (nb057_alpha_dummy_163 f)),
        ((nb057_alpha_dummy_131), (nb057_alpha_dummy_133 f)),
        ((nb057_alpha_dummy_130), (nb057_alpha_dummy_132 f)),
        ((nb057_alpha_dummy_160), (nb057_alpha_dummy_161 f)),
        ((nb057_alpha_dummy_134), (nb057_alpha_dummy_135 f)),
        ((nb057_alpha_dummy_125), (nb057_alpha_dummy_127 f)),
        ((nb057_alpha_dummy_124), (nb057_alpha_dummy_126 f)),
        ((nb057_alpha_dummy_128), (nb057_alpha_dummy_129 f)),
        ((nb057_alpha_dummy_046), (nb057_alpha_dummy_049 f)),
        ((nb057_alpha_dummy_045), (nb057_alpha_dummy_048 f)),
        ((nb057_alpha_dummy_044), (nb057_alpha_dummy_047 f)),
        ((nb057_alpha_dummy_050), (nb057_alpha_dummy_051 f)),
        ((nb057_alpha_dummy_000), a), ((nb057_alpha_dummy_001), f),
        ((nb057_alpha_dummy_002), (nb057_alpha_dummy_003 f a))]
      (Wff.imp (Wff.classMem (Class.cv (nb057_alpha_dummy_138))
          (Class.cv (nb057_alpha_dummy_131))) (Wff.neg
          (Wff.classEq (Class.cv (nb057_alpha_dummy_139))
            (syn_cif (Wff.classMem (Class.cv (nb057_alpha_dummy_138)) (syn_cnnc))
              (syn_cplc (Class.cv (nb057_alpha_dummy_138)) (syn_c1c))
              (Class.cv (nb057_alpha_dummy_138))))))
      (Wff.imp (Wff.classMem (Class.cv (nb057_alpha_dummy_140 f))
          (Class.cv (nb057_alpha_dummy_133 f))) (Wff.neg
          (Wff.classEq (Class.cv (nb057_alpha_dummy_141 f))
            (syn_cif (Wff.classMem (Class.cv (nb057_alpha_dummy_140 f)) (syn_cnnc))
              (syn_cplc (Class.cv (nb057_alpha_dummy_140 f)) (syn_c1c))
              (Class.cv (nb057_alpha_dummy_140 f)))))) :=
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
            (freshVar_injective (((Class.cv (nb057_alpha_dummy_131))).fv) (by decide))
            (freshVar_injective (((Class.cv (nb057_alpha_dummy_133 f))).fv) (by decide))
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
                              (TAlphaClass.refl_of_closed
                                [((nb057_alpha_dummy_146), (nb057_alpha_dummy_149 f)),
                                  ((nb057_alpha_dummy_145), (nb057_alpha_dummy_148 f)),
                                  ((nb057_alpha_dummy_144), (nb057_alpha_dummy_147 f)),
                                  ((nb057_alpha_dummy_142), (nb057_alpha_dummy_143 f)),
                                  ((nb057_alpha_dummy_138), (nb057_alpha_dummy_140 f)),
                                  ((nb057_alpha_dummy_139), (nb057_alpha_dummy_141 f)),
                                  ((nb057_alpha_dummy_164), (nb057_alpha_dummy_165 f)),
                                  ((nb057_alpha_dummy_162), (nb057_alpha_dummy_163 f)),
                                  ((nb057_alpha_dummy_131), (nb057_alpha_dummy_133 f)),
                                  ((nb057_alpha_dummy_130), (nb057_alpha_dummy_132 f)),
                                  ((nb057_alpha_dummy_160), (nb057_alpha_dummy_161 f)),
                                  ((nb057_alpha_dummy_134), (nb057_alpha_dummy_135 f)),
                                  ((nb057_alpha_dummy_125), (nb057_alpha_dummy_127 f)),
                                  ((nb057_alpha_dummy_124), (nb057_alpha_dummy_126 f)),
                                  ((nb057_alpha_dummy_128), (nb057_alpha_dummy_129 f)),
                                  ((nb057_alpha_dummy_046), (nb057_alpha_dummy_049 f)),
                                  ((nb057_alpha_dummy_045), (nb057_alpha_dummy_048 f)),
                                  ((nb057_alpha_dummy_044), (nb057_alpha_dummy_047 f)),
                                  ((nb057_alpha_dummy_050), (nb057_alpha_dummy_051 f)),
                                  ((nb057_alpha_dummy_000), a), ((nb057_alpha_dummy_001), f),
                                  ((nb057_alpha_dummy_002), (nb057_alpha_dummy_003 f a))]
                                (syn_c1c) (by simp only [fv_syn_c1c])))
                            (TAlphaWff.neg (nb057_split_alpha_0045 f a))))))))
                (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there
                      (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0134) 0))
                      (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0135 f) 0))
                      (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
                    [((nb057_alpha_dummy_142), (nb057_alpha_dummy_143 f)),
                      ((nb057_alpha_dummy_138), (nb057_alpha_dummy_140 f)),
                      ((nb057_alpha_dummy_139), (nb057_alpha_dummy_141 f)),
                      ((nb057_alpha_dummy_164), (nb057_alpha_dummy_165 f)),
                      ((nb057_alpha_dummy_162), (nb057_alpha_dummy_163 f)),
                      ((nb057_alpha_dummy_131), (nb057_alpha_dummy_133 f)),
                      ((nb057_alpha_dummy_130), (nb057_alpha_dummy_132 f)),
                      ((nb057_alpha_dummy_160), (nb057_alpha_dummy_161 f)),
                      ((nb057_alpha_dummy_134), (nb057_alpha_dummy_135 f)),
                      ((nb057_alpha_dummy_125), (nb057_alpha_dummy_127 f)),
                      ((nb057_alpha_dummy_124), (nb057_alpha_dummy_126 f)),
                      ((nb057_alpha_dummy_128), (nb057_alpha_dummy_129 f)),
                      ((nb057_alpha_dummy_046), (nb057_alpha_dummy_049 f)),
                      ((nb057_alpha_dummy_045), (nb057_alpha_dummy_048 f)),
                      ((nb057_alpha_dummy_044), (nb057_alpha_dummy_047 f)),
                      ((nb057_alpha_dummy_050), (nb057_alpha_dummy_051 f)),
                      ((nb057_alpha_dummy_000), a), ((nb057_alpha_dummy_001), f),
                      ((nb057_alpha_dummy_002), (nb057_alpha_dummy_003 f a))]
                    (syn_cnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                  (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0134) 0))
                    (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0135 f) 0))
                    (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv
                    (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0134) 0))
                      (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0135 f) 0))
                      (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
                    [((nb057_alpha_dummy_142), (nb057_alpha_dummy_143 f)),
                      ((nb057_alpha_dummy_138), (nb057_alpha_dummy_140 f)),
                      ((nb057_alpha_dummy_139), (nb057_alpha_dummy_141 f)),
                      ((nb057_alpha_dummy_164), (nb057_alpha_dummy_165 f)),
                      ((nb057_alpha_dummy_162), (nb057_alpha_dummy_163 f)),
                      ((nb057_alpha_dummy_131), (nb057_alpha_dummy_133 f)),
                      ((nb057_alpha_dummy_130), (nb057_alpha_dummy_132 f)),
                      ((nb057_alpha_dummy_160), (nb057_alpha_dummy_161 f)),
                      ((nb057_alpha_dummy_134), (nb057_alpha_dummy_135 f)),
                      ((nb057_alpha_dummy_125), (nb057_alpha_dummy_127 f)),
                      ((nb057_alpha_dummy_124), (nb057_alpha_dummy_126 f)),
                      ((nb057_alpha_dummy_128), (nb057_alpha_dummy_129 f)),
                      ((nb057_alpha_dummy_046), (nb057_alpha_dummy_049 f)),
                      ((nb057_alpha_dummy_045), (nb057_alpha_dummy_048 f)),
                      ((nb057_alpha_dummy_044), (nb057_alpha_dummy_047 f)),
                      ((nb057_alpha_dummy_050), (nb057_alpha_dummy_051 f)),
                      ((nb057_alpha_dummy_000), a), ((nb057_alpha_dummy_001), f),
                      ((nb057_alpha_dummy_002), (nb057_alpha_dummy_003 f a))]
                    (syn_cnnc) (by simp only [fv_syn_cnnc]))))))))))

@[expose]
noncomputable def nb057_split_alpha_0047 (f : Var) (a : Var) :
    TAlphaWff
      [((nb057_alpha_dummy_160), (nb057_alpha_dummy_161 f)),
        ((nb057_alpha_dummy_134), (nb057_alpha_dummy_135 f)),
        ((nb057_alpha_dummy_125), (nb057_alpha_dummy_127 f)),
        ((nb057_alpha_dummy_124), (nb057_alpha_dummy_126 f)),
        ((nb057_alpha_dummy_128), (nb057_alpha_dummy_129 f)),
        ((nb057_alpha_dummy_046), (nb057_alpha_dummy_049 f)),
        ((nb057_alpha_dummy_045), (nb057_alpha_dummy_048 f)),
        ((nb057_alpha_dummy_044), (nb057_alpha_dummy_047 f)),
        ((nb057_alpha_dummy_050), (nb057_alpha_dummy_051 f)),
        ((nb057_alpha_dummy_000), a), ((nb057_alpha_dummy_001), f),
        ((nb057_alpha_dummy_002), (nb057_alpha_dummy_003 f a))]
      (Wff.imp (Wff.classMem (Class.cv (nb057_alpha_dummy_160))
          (Class.cab (nb057_alpha_dummy_130)
            (syn_wrex (nb057_alpha_dummy_131) (Class.cv (nb057_alpha_dummy_125))
              (Wff.classEq (Class.cv (nb057_alpha_dummy_130))
                (syn_cun (syn_cphi (Class.cv (nb057_alpha_dummy_131))) (syn_csn (syn_c0c)))))))
        (Wff.neg (Wff.classMem (Class.cv (nb057_alpha_dummy_160))
            (Class.cab (nb057_alpha_dummy_130)
              (syn_wrex (nb057_alpha_dummy_131) (Class.cv (nb057_alpha_dummy_125))
                (Wff.classEq (Class.cv (nb057_alpha_dummy_130))
                  (syn_cun (syn_cphi (Class.cv (nb057_alpha_dummy_131)))
                    (syn_csn (syn_c0c)))))))))
      (Wff.imp (Wff.classMem (Class.cv (nb057_alpha_dummy_161 f))
          (Class.cab (nb057_alpha_dummy_132 f)
            (syn_wrex (nb057_alpha_dummy_133 f) (Class.cv (nb057_alpha_dummy_127 f))
              (Wff.classEq (Class.cv (nb057_alpha_dummy_132 f))
                (syn_cun (syn_cphi (Class.cv (nb057_alpha_dummy_133 f)))
                  (syn_csn (syn_c0c))))))) (Wff.neg
          (Wff.classMem (Class.cv (nb057_alpha_dummy_161 f))
            (Class.cab (nb057_alpha_dummy_132 f)
              (syn_wrex (nb057_alpha_dummy_133 f) (Class.cv (nb057_alpha_dummy_127 f))
                (Wff.classEq (Class.cv (nb057_alpha_dummy_132 f))
                  (syn_cun (syn_cphi (Class.cv (nb057_alpha_dummy_133 f)))
                    (syn_csn (syn_c0c))))))))) :=
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
                (TAlphaVar.there (freshVar_injective (((Class.cv (nb057_alpha_dummy_124))).fv ∪
                      ((Class.cv (nb057_alpha_dummy_125))).fv) (by decide)) (freshVar_injective
                    (((Class.cv (nb057_alpha_dummy_126 f))).fv ∪
                      ((Class.cv (nb057_alpha_dummy_127 f))).fv) (by decide))
                  (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                        (TAlphaWff.neg (TAlphaWff.conj
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cab (TAlphaWff.ex
                                  (TAlphaWff.neg (nb057_split_alpha_0046 f a)))))
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cab (TAlphaWff.ex
                                  (TAlphaWff.neg (nb057_split_alpha_0046 f a)))))))))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                      (TAlphaClass.refl_of_closed
                        [((nb057_alpha_dummy_162), (nb057_alpha_dummy_163 f)),
                          ((nb057_alpha_dummy_131), (nb057_alpha_dummy_133 f)),
                          ((nb057_alpha_dummy_130), (nb057_alpha_dummy_132 f)),
                          ((nb057_alpha_dummy_160), (nb057_alpha_dummy_161 f)),
                          ((nb057_alpha_dummy_134), (nb057_alpha_dummy_135 f)),
                          ((nb057_alpha_dummy_125), (nb057_alpha_dummy_127 f)),
                          ((nb057_alpha_dummy_124), (nb057_alpha_dummy_126 f)),
                          ((nb057_alpha_dummy_128), (nb057_alpha_dummy_129 f)),
                          ((nb057_alpha_dummy_046), (nb057_alpha_dummy_049 f)),
                          ((nb057_alpha_dummy_045), (nb057_alpha_dummy_048 f)),
                          ((nb057_alpha_dummy_044), (nb057_alpha_dummy_047 f)),
                          ((nb057_alpha_dummy_050), (nb057_alpha_dummy_051 f)),
                          ((nb057_alpha_dummy_000), a), ((nb057_alpha_dummy_001), f),
                          ((nb057_alpha_dummy_002), (nb057_alpha_dummy_003 f a))]
                        (syn_ccompl (syn_csn (syn_c0c)))
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
                      (((Class.cv (nb057_alpha_dummy_124))).fv ∪
                        ((Class.cv (nb057_alpha_dummy_125))).fv) (by decide))
                    (freshVar_injective (((Class.cv (nb057_alpha_dummy_126 f))).fv ∪
                        ((Class.cv (nb057_alpha_dummy_127 f))).fv) (by decide))
                    (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cab (TAlphaWff.ex
                                    (TAlphaWff.neg (nb057_split_alpha_0046 f a)))))
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cab (TAlphaWff.ex
                                    (TAlphaWff.neg (nb057_split_alpha_0046 f a)))))))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.refl_of_closed
                          [((nb057_alpha_dummy_162), (nb057_alpha_dummy_163 f)),
                            ((nb057_alpha_dummy_131), (nb057_alpha_dummy_133 f)),
                            ((nb057_alpha_dummy_130), (nb057_alpha_dummy_132 f)),
                            ((nb057_alpha_dummy_160), (nb057_alpha_dummy_161 f)),
                            ((nb057_alpha_dummy_134), (nb057_alpha_dummy_135 f)),
                            ((nb057_alpha_dummy_125), (nb057_alpha_dummy_127 f)),
                            ((nb057_alpha_dummy_124), (nb057_alpha_dummy_126 f)),
                            ((nb057_alpha_dummy_128), (nb057_alpha_dummy_129 f)),
                            ((nb057_alpha_dummy_046), (nb057_alpha_dummy_049 f)),
                            ((nb057_alpha_dummy_045), (nb057_alpha_dummy_048 f)),
                            ((nb057_alpha_dummy_044), (nb057_alpha_dummy_047 f)),
                            ((nb057_alpha_dummy_050), (nb057_alpha_dummy_051 f)),
                            ((nb057_alpha_dummy_000), a), ((nb057_alpha_dummy_001), f),
                            ((nb057_alpha_dummy_002), (nb057_alpha_dummy_003 f a))]
                          (syn_ccompl (syn_csn (syn_c0c))) (by
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

@[expose]
noncomputable def nb057_split_alpha_0048 (f : Var) (a : Var) :
    TAlphaWff
      [((nb057_alpha_dummy_182), (nb057_alpha_dummy_185 f)),
        ((nb057_alpha_dummy_181), (nb057_alpha_dummy_184 f)),
        ((nb057_alpha_dummy_180), (nb057_alpha_dummy_183 f)),
        ((nb057_alpha_dummy_178), (nb057_alpha_dummy_179 f)),
        ((nb057_alpha_dummy_174), (nb057_alpha_dummy_176 f)),
        ((nb057_alpha_dummy_175), (nb057_alpha_dummy_177 f)),
        ((nb057_alpha_dummy_167), (nb057_alpha_dummy_169 f)),
        ((nb057_alpha_dummy_166), (nb057_alpha_dummy_168 f)),
        ((nb057_alpha_dummy_172), (nb057_alpha_dummy_173 f)),
        ((nb057_alpha_dummy_170), (nb057_alpha_dummy_171 f)),
        ((nb057_alpha_dummy_125), (nb057_alpha_dummy_127 f)),
        ((nb057_alpha_dummy_124), (nb057_alpha_dummy_126 f)),
        ((nb057_alpha_dummy_128), (nb057_alpha_dummy_129 f)),
        ((nb057_alpha_dummy_046), (nb057_alpha_dummy_049 f)),
        ((nb057_alpha_dummy_045), (nb057_alpha_dummy_048 f)),
        ((nb057_alpha_dummy_044), (nb057_alpha_dummy_047 f)),
        ((nb057_alpha_dummy_050), (nb057_alpha_dummy_051 f)),
        ((nb057_alpha_dummy_000), a), ((nb057_alpha_dummy_001), f),
        ((nb057_alpha_dummy_002), (nb057_alpha_dummy_003 f a))]
      (Wff.imp (Wff.classEq
          (syn_cin (Class.cv (nb057_alpha_dummy_181)) (Class.cv (nb057_alpha_dummy_182)))
          (syn_c0)) (Wff.neg (Wff.classEq (Class.cv (nb057_alpha_dummy_180))
            (syn_cun (Class.cv (nb057_alpha_dummy_181)) (Class.cv (nb057_alpha_dummy_182))))))
      (Wff.imp (Wff.classEq (syn_cin (Class.cv (nb057_alpha_dummy_184 f))
            (Class.cv (nb057_alpha_dummy_185 f))) (syn_c0)) (Wff.neg
          (Wff.classEq (Class.cv (nb057_alpha_dummy_183 f))
            (syn_cun (Class.cv (nb057_alpha_dummy_184 f))
              (Class.cv (nb057_alpha_dummy_185 f)))))) :=
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
                                (((Class.cv (nb057_alpha_dummy_174))).fv ∪ ((syn_c1c)).fv)
                                (by decide)) (freshVar_injective
                                (((Class.cv (nb057_alpha_dummy_176 f))).fv ∪ ((syn_c1c)).fv)
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
                                (((Class.cv (nb057_alpha_dummy_174))).fv ∪ ((syn_c1c)).fv)
                                (by decide)) (freshVar_injective
                                (((Class.cv (nb057_alpha_dummy_176 f))).fv ∪ ((syn_c1c)).fv)
                                (by decide)) (TAlphaVar.here _ _ _))))))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0182) 0))
                          (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0183 f) 0))
                          (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0180) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0181 f) 0))
                            (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.refl_of_closed
        [((nb057_alpha_dummy_182), (nb057_alpha_dummy_185 f)),
          ((nb057_alpha_dummy_181), (nb057_alpha_dummy_184 f)),
          ((nb057_alpha_dummy_180), (nb057_alpha_dummy_183 f)),
          ((nb057_alpha_dummy_178), (nb057_alpha_dummy_179 f)),
          ((nb057_alpha_dummy_174), (nb057_alpha_dummy_176 f)),
          ((nb057_alpha_dummy_175), (nb057_alpha_dummy_177 f)),
          ((nb057_alpha_dummy_167), (nb057_alpha_dummy_169 f)),
          ((nb057_alpha_dummy_166), (nb057_alpha_dummy_168 f)),
          ((nb057_alpha_dummy_172), (nb057_alpha_dummy_173 f)),
          ((nb057_alpha_dummy_170), (nb057_alpha_dummy_171 f)),
          ((nb057_alpha_dummy_125), (nb057_alpha_dummy_127 f)),
          ((nb057_alpha_dummy_124), (nb057_alpha_dummy_126 f)),
          ((nb057_alpha_dummy_128), (nb057_alpha_dummy_129 f)),
          ((nb057_alpha_dummy_046), (nb057_alpha_dummy_049 f)),
          ((nb057_alpha_dummy_045), (nb057_alpha_dummy_048 f)),
          ((nb057_alpha_dummy_044), (nb057_alpha_dummy_047 f)),
          ((nb057_alpha_dummy_050), (nb057_alpha_dummy_051 f)),
          ((nb057_alpha_dummy_000), a), ((nb057_alpha_dummy_001), f),
          ((nb057_alpha_dummy_002), (nb057_alpha_dummy_003 f a))]
        (syn_c0) (by simp only [fv_syn_c0]))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv
          (TAlphaVar.there
            (freshVar_injective (((Class.cv (nb057_alpha_dummy_174))).fv ∪ ((syn_c1c)).fv)
              (by decide)) (freshVar_injective
              (((Class.cv (nb057_alpha_dummy_176 f))).fv ∪ ((syn_c1c)).fv) (by decide))
            (TAlphaVar.there (freshVar_injective
                (((Class.cv (nb057_alpha_dummy_174))).fv ∪ ((syn_c1c)).fv) (by decide))
              (freshVar_injective
                (((Class.cv (nb057_alpha_dummy_176 f))).fv ∪ ((syn_c1c)).fv) (by decide))
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
                                  (((Class.cv (nb057_alpha_dummy_174))).fv ∪ ((syn_c1c)).fv)
                                  (by decide)) (freshVar_injective
                                  (((Class.cv (nb057_alpha_dummy_176 f))).fv ∪ ((syn_c1c)).fv)
                                  (by decide)) (TAlphaVar.here _ _ _))))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0186) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0187 f) 0))
                            (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0184) 0))
                              (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0185 f) 0))
                              (TAlphaVar.there (freshVar_injective
                                  (((Class.cv (nb057_alpha_dummy_174))).fv ∪ ((syn_c1c)).fv)
                                  (by decide)) (freshVar_injective
                                  (((Class.cv (nb057_alpha_dummy_176 f))).fv ∪ ((syn_c1c)).fv)
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

@[expose]
noncomputable def nb057_split_alpha_0049 (f : Var) (a : Var) :
    TAlphaWff
      [((nb057_alpha_dummy_174), (nb057_alpha_dummy_176 f)),
        ((nb057_alpha_dummy_175), (nb057_alpha_dummy_177 f)),
        ((nb057_alpha_dummy_167), (nb057_alpha_dummy_169 f)),
        ((nb057_alpha_dummy_166), (nb057_alpha_dummy_168 f)),
        ((nb057_alpha_dummy_172), (nb057_alpha_dummy_173 f)),
        ((nb057_alpha_dummy_170), (nb057_alpha_dummy_171 f)),
        ((nb057_alpha_dummy_125), (nb057_alpha_dummy_127 f)),
        ((nb057_alpha_dummy_124), (nb057_alpha_dummy_126 f)),
        ((nb057_alpha_dummy_128), (nb057_alpha_dummy_129 f)),
        ((nb057_alpha_dummy_046), (nb057_alpha_dummy_049 f)),
        ((nb057_alpha_dummy_045), (nb057_alpha_dummy_048 f)),
        ((nb057_alpha_dummy_044), (nb057_alpha_dummy_047 f)),
        ((nb057_alpha_dummy_050), (nb057_alpha_dummy_051 f)),
        ((nb057_alpha_dummy_000), a), ((nb057_alpha_dummy_001), f),
        ((nb057_alpha_dummy_002), (nb057_alpha_dummy_003 f a))]
      (Wff.imp (Wff.classMem (Class.cv (nb057_alpha_dummy_174))
          (Class.cv (nb057_alpha_dummy_167))) (Wff.neg
          (Wff.classEq (Class.cv (nb057_alpha_dummy_175))
            (syn_cif (Wff.classMem (Class.cv (nb057_alpha_dummy_174)) (syn_cnnc))
              (syn_cplc (Class.cv (nb057_alpha_dummy_174)) (syn_c1c))
              (Class.cv (nb057_alpha_dummy_174))))))
      (Wff.imp (Wff.classMem (Class.cv (nb057_alpha_dummy_176 f))
          (Class.cv (nb057_alpha_dummy_169 f))) (Wff.neg
          (Wff.classEq (Class.cv (nb057_alpha_dummy_177 f))
            (syn_cif (Wff.classMem (Class.cv (nb057_alpha_dummy_176 f)) (syn_cnnc))
              (syn_cplc (Class.cv (nb057_alpha_dummy_176 f)) (syn_c1c))
              (Class.cv (nb057_alpha_dummy_176 f)))))) :=
  (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0170) 0))
          (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0171 f) 0))
          (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0170) 1))
            (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0171 f) 1))
            (TAlphaVar.here _ _ _))))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv
          (TAlphaVar.there
            (freshVar_injective (((Class.cv (nb057_alpha_dummy_167))).fv) (by decide))
            (freshVar_injective (((Class.cv (nb057_alpha_dummy_169 f))).fv) (by decide))
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
                              (TAlphaClass.refl_of_closed
                                [((nb057_alpha_dummy_182), (nb057_alpha_dummy_185 f)),
                                  ((nb057_alpha_dummy_181), (nb057_alpha_dummy_184 f)),
                                  ((nb057_alpha_dummy_180), (nb057_alpha_dummy_183 f)),
                                  ((nb057_alpha_dummy_178), (nb057_alpha_dummy_179 f)),
                                  ((nb057_alpha_dummy_174), (nb057_alpha_dummy_176 f)),
                                  ((nb057_alpha_dummy_175), (nb057_alpha_dummy_177 f)),
                                  ((nb057_alpha_dummy_167), (nb057_alpha_dummy_169 f)),
                                  ((nb057_alpha_dummy_166), (nb057_alpha_dummy_168 f)),
                                  ((nb057_alpha_dummy_172), (nb057_alpha_dummy_173 f)),
                                  ((nb057_alpha_dummy_170), (nb057_alpha_dummy_171 f)),
                                  ((nb057_alpha_dummy_125), (nb057_alpha_dummy_127 f)),
                                  ((nb057_alpha_dummy_124), (nb057_alpha_dummy_126 f)),
                                  ((nb057_alpha_dummy_128), (nb057_alpha_dummy_129 f)),
                                  ((nb057_alpha_dummy_046), (nb057_alpha_dummy_049 f)),
                                  ((nb057_alpha_dummy_045), (nb057_alpha_dummy_048 f)),
                                  ((nb057_alpha_dummy_044), (nb057_alpha_dummy_047 f)),
                                  ((nb057_alpha_dummy_050), (nb057_alpha_dummy_051 f)),
                                  ((nb057_alpha_dummy_000), a), ((nb057_alpha_dummy_001), f),
                                  ((nb057_alpha_dummy_002), (nb057_alpha_dummy_003 f a))]
                                (syn_c1c) (by simp only [fv_syn_c1c])))
                            (TAlphaWff.neg (nb057_split_alpha_0048 f a))))))))
                (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there
                      (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0172) 0))
                      (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0173 f) 0))
                      (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
                    [((nb057_alpha_dummy_178), (nb057_alpha_dummy_179 f)),
                      ((nb057_alpha_dummy_174), (nb057_alpha_dummy_176 f)),
                      ((nb057_alpha_dummy_175), (nb057_alpha_dummy_177 f)),
                      ((nb057_alpha_dummy_167), (nb057_alpha_dummy_169 f)),
                      ((nb057_alpha_dummy_166), (nb057_alpha_dummy_168 f)),
                      ((nb057_alpha_dummy_172), (nb057_alpha_dummy_173 f)),
                      ((nb057_alpha_dummy_170), (nb057_alpha_dummy_171 f)),
                      ((nb057_alpha_dummy_125), (nb057_alpha_dummy_127 f)),
                      ((nb057_alpha_dummy_124), (nb057_alpha_dummy_126 f)),
                      ((nb057_alpha_dummy_128), (nb057_alpha_dummy_129 f)),
                      ((nb057_alpha_dummy_046), (nb057_alpha_dummy_049 f)),
                      ((nb057_alpha_dummy_045), (nb057_alpha_dummy_048 f)),
                      ((nb057_alpha_dummy_044), (nb057_alpha_dummy_047 f)),
                      ((nb057_alpha_dummy_050), (nb057_alpha_dummy_051 f)),
                      ((nb057_alpha_dummy_000), a), ((nb057_alpha_dummy_001), f),
                      ((nb057_alpha_dummy_002), (nb057_alpha_dummy_003 f a))]
                    (syn_cnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                  (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0172) 0))
                    (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0173 f) 0))
                    (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv
                    (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0172) 0))
                      (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0173 f) 0))
                      (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
                    [((nb057_alpha_dummy_178), (nb057_alpha_dummy_179 f)),
                      ((nb057_alpha_dummy_174), (nb057_alpha_dummy_176 f)),
                      ((nb057_alpha_dummy_175), (nb057_alpha_dummy_177 f)),
                      ((nb057_alpha_dummy_167), (nb057_alpha_dummy_169 f)),
                      ((nb057_alpha_dummy_166), (nb057_alpha_dummy_168 f)),
                      ((nb057_alpha_dummy_172), (nb057_alpha_dummy_173 f)),
                      ((nb057_alpha_dummy_170), (nb057_alpha_dummy_171 f)),
                      ((nb057_alpha_dummy_125), (nb057_alpha_dummy_127 f)),
                      ((nb057_alpha_dummy_124), (nb057_alpha_dummy_126 f)),
                      ((nb057_alpha_dummy_128), (nb057_alpha_dummy_129 f)),
                      ((nb057_alpha_dummy_046), (nb057_alpha_dummy_049 f)),
                      ((nb057_alpha_dummy_045), (nb057_alpha_dummy_048 f)),
                      ((nb057_alpha_dummy_044), (nb057_alpha_dummy_047 f)),
                      ((nb057_alpha_dummy_050), (nb057_alpha_dummy_051 f)),
                      ((nb057_alpha_dummy_000), a), ((nb057_alpha_dummy_001), f),
                      ((nb057_alpha_dummy_002), (nb057_alpha_dummy_003 f a))]
                    (syn_cnnc) (by simp only [fv_syn_cnnc]))))))))))

@[expose]
noncomputable def nb057_split_alpha_0050 (f : Var) (a : Var) :
    TAlphaWff
      [((nb057_alpha_dummy_182), (nb057_alpha_dummy_185 f)),
        ((nb057_alpha_dummy_181), (nb057_alpha_dummy_184 f)),
        ((nb057_alpha_dummy_180), (nb057_alpha_dummy_183 f)),
        ((nb057_alpha_dummy_178), (nb057_alpha_dummy_179 f)),
        ((nb057_alpha_dummy_174), (nb057_alpha_dummy_176 f)),
        ((nb057_alpha_dummy_175), (nb057_alpha_dummy_177 f)),
        ((nb057_alpha_dummy_200), (nb057_alpha_dummy_201 f)),
        ((nb057_alpha_dummy_198), (nb057_alpha_dummy_199 f)),
        ((nb057_alpha_dummy_167), (nb057_alpha_dummy_169 f)),
        ((nb057_alpha_dummy_166), (nb057_alpha_dummy_168 f)),
        ((nb057_alpha_dummy_196), (nb057_alpha_dummy_197 f)),
        ((nb057_alpha_dummy_170), (nb057_alpha_dummy_171 f)),
        ((nb057_alpha_dummy_125), (nb057_alpha_dummy_127 f)),
        ((nb057_alpha_dummy_124), (nb057_alpha_dummy_126 f)),
        ((nb057_alpha_dummy_128), (nb057_alpha_dummy_129 f)),
        ((nb057_alpha_dummy_046), (nb057_alpha_dummy_049 f)),
        ((nb057_alpha_dummy_045), (nb057_alpha_dummy_048 f)),
        ((nb057_alpha_dummy_044), (nb057_alpha_dummy_047 f)),
        ((nb057_alpha_dummy_050), (nb057_alpha_dummy_051 f)),
        ((nb057_alpha_dummy_000), a), ((nb057_alpha_dummy_001), f),
        ((nb057_alpha_dummy_002), (nb057_alpha_dummy_003 f a))]
      (Wff.imp (Wff.classEq
          (syn_cin (Class.cv (nb057_alpha_dummy_181)) (Class.cv (nb057_alpha_dummy_182)))
          (syn_c0)) (Wff.neg (Wff.classEq (Class.cv (nb057_alpha_dummy_180))
            (syn_cun (Class.cv (nb057_alpha_dummy_181)) (Class.cv (nb057_alpha_dummy_182))))))
      (Wff.imp (Wff.classEq (syn_cin (Class.cv (nb057_alpha_dummy_184 f))
            (Class.cv (nb057_alpha_dummy_185 f))) (syn_c0)) (Wff.neg
          (Wff.classEq (Class.cv (nb057_alpha_dummy_183 f))
            (syn_cun (Class.cv (nb057_alpha_dummy_184 f))
              (Class.cv (nb057_alpha_dummy_185 f)))))) :=
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
                                (((Class.cv (nb057_alpha_dummy_174))).fv ∪ ((syn_c1c)).fv)
                                (by decide)) (freshVar_injective
                                (((Class.cv (nb057_alpha_dummy_176 f))).fv ∪ ((syn_c1c)).fv)
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
                                (((Class.cv (nb057_alpha_dummy_174))).fv ∪ ((syn_c1c)).fv)
                                (by decide)) (freshVar_injective
                                (((Class.cv (nb057_alpha_dummy_176 f))).fv ∪ ((syn_c1c)).fv)
                                (by decide)) (TAlphaVar.here _ _ _))))))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0182) 0))
                          (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0183 f) 0))
                          (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0180) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0181 f) 0))
                            (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.refl_of_closed
        [((nb057_alpha_dummy_182), (nb057_alpha_dummy_185 f)),
          ((nb057_alpha_dummy_181), (nb057_alpha_dummy_184 f)),
          ((nb057_alpha_dummy_180), (nb057_alpha_dummy_183 f)),
          ((nb057_alpha_dummy_178), (nb057_alpha_dummy_179 f)),
          ((nb057_alpha_dummy_174), (nb057_alpha_dummy_176 f)),
          ((nb057_alpha_dummy_175), (nb057_alpha_dummy_177 f)),
          ((nb057_alpha_dummy_200), (nb057_alpha_dummy_201 f)),
          ((nb057_alpha_dummy_198), (nb057_alpha_dummy_199 f)),
          ((nb057_alpha_dummy_167), (nb057_alpha_dummy_169 f)),
          ((nb057_alpha_dummy_166), (nb057_alpha_dummy_168 f)),
          ((nb057_alpha_dummy_196), (nb057_alpha_dummy_197 f)),
          ((nb057_alpha_dummy_170), (nb057_alpha_dummy_171 f)),
          ((nb057_alpha_dummy_125), (nb057_alpha_dummy_127 f)),
          ((nb057_alpha_dummy_124), (nb057_alpha_dummy_126 f)),
          ((nb057_alpha_dummy_128), (nb057_alpha_dummy_129 f)),
          ((nb057_alpha_dummy_046), (nb057_alpha_dummy_049 f)),
          ((nb057_alpha_dummy_045), (nb057_alpha_dummy_048 f)),
          ((nb057_alpha_dummy_044), (nb057_alpha_dummy_047 f)),
          ((nb057_alpha_dummy_050), (nb057_alpha_dummy_051 f)),
          ((nb057_alpha_dummy_000), a), ((nb057_alpha_dummy_001), f),
          ((nb057_alpha_dummy_002), (nb057_alpha_dummy_003 f a))]
        (syn_c0) (by simp only [fv_syn_c0]))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv
          (TAlphaVar.there
            (freshVar_injective (((Class.cv (nb057_alpha_dummy_174))).fv ∪ ((syn_c1c)).fv)
              (by decide)) (freshVar_injective
              (((Class.cv (nb057_alpha_dummy_176 f))).fv ∪ ((syn_c1c)).fv) (by decide))
            (TAlphaVar.there (freshVar_injective
                (((Class.cv (nb057_alpha_dummy_174))).fv ∪ ((syn_c1c)).fv) (by decide))
              (freshVar_injective
                (((Class.cv (nb057_alpha_dummy_176 f))).fv ∪ ((syn_c1c)).fv) (by decide))
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
                                  (((Class.cv (nb057_alpha_dummy_174))).fv ∪ ((syn_c1c)).fv)
                                  (by decide)) (freshVar_injective
                                  (((Class.cv (nb057_alpha_dummy_176 f))).fv ∪ ((syn_c1c)).fv)
                                  (by decide)) (TAlphaVar.here _ _ _))))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0186) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0187 f) 0))
                            (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0184) 0))
                              (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0185 f) 0))
                              (TAlphaVar.there (freshVar_injective
                                  (((Class.cv (nb057_alpha_dummy_174))).fv ∪ ((syn_c1c)).fv)
                                  (by decide)) (freshVar_injective
                                  (((Class.cv (nb057_alpha_dummy_176 f))).fv ∪ ((syn_c1c)).fv)
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

@[expose]
noncomputable def nb057_split_alpha_0051 (f : Var) (a : Var) :
    TAlphaWff
      [((nb057_alpha_dummy_174), (nb057_alpha_dummy_176 f)),
        ((nb057_alpha_dummy_175), (nb057_alpha_dummy_177 f)),
        ((nb057_alpha_dummy_200), (nb057_alpha_dummy_201 f)),
        ((nb057_alpha_dummy_198), (nb057_alpha_dummy_199 f)),
        ((nb057_alpha_dummy_167), (nb057_alpha_dummy_169 f)),
        ((nb057_alpha_dummy_166), (nb057_alpha_dummy_168 f)),
        ((nb057_alpha_dummy_196), (nb057_alpha_dummy_197 f)),
        ((nb057_alpha_dummy_170), (nb057_alpha_dummy_171 f)),
        ((nb057_alpha_dummy_125), (nb057_alpha_dummy_127 f)),
        ((nb057_alpha_dummy_124), (nb057_alpha_dummy_126 f)),
        ((nb057_alpha_dummy_128), (nb057_alpha_dummy_129 f)),
        ((nb057_alpha_dummy_046), (nb057_alpha_dummy_049 f)),
        ((nb057_alpha_dummy_045), (nb057_alpha_dummy_048 f)),
        ((nb057_alpha_dummy_044), (nb057_alpha_dummy_047 f)),
        ((nb057_alpha_dummy_050), (nb057_alpha_dummy_051 f)),
        ((nb057_alpha_dummy_000), a), ((nb057_alpha_dummy_001), f),
        ((nb057_alpha_dummy_002), (nb057_alpha_dummy_003 f a))]
      (Wff.imp (Wff.classMem (Class.cv (nb057_alpha_dummy_174))
          (Class.cv (nb057_alpha_dummy_167))) (Wff.neg
          (Wff.classEq (Class.cv (nb057_alpha_dummy_175))
            (syn_cif (Wff.classMem (Class.cv (nb057_alpha_dummy_174)) (syn_cnnc))
              (syn_cplc (Class.cv (nb057_alpha_dummy_174)) (syn_c1c))
              (Class.cv (nb057_alpha_dummy_174))))))
      (Wff.imp (Wff.classMem (Class.cv (nb057_alpha_dummy_176 f))
          (Class.cv (nb057_alpha_dummy_169 f))) (Wff.neg
          (Wff.classEq (Class.cv (nb057_alpha_dummy_177 f))
            (syn_cif (Wff.classMem (Class.cv (nb057_alpha_dummy_176 f)) (syn_cnnc))
              (syn_cplc (Class.cv (nb057_alpha_dummy_176 f)) (syn_c1c))
              (Class.cv (nb057_alpha_dummy_176 f)))))) :=
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
            (freshVar_injective (((Class.cv (nb057_alpha_dummy_167))).fv) (by decide))
            (freshVar_injective (((Class.cv (nb057_alpha_dummy_169 f))).fv) (by decide))
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
                              (TAlphaClass.refl_of_closed
                                [((nb057_alpha_dummy_182), (nb057_alpha_dummy_185 f)),
                                  ((nb057_alpha_dummy_181), (nb057_alpha_dummy_184 f)),
                                  ((nb057_alpha_dummy_180), (nb057_alpha_dummy_183 f)),
                                  ((nb057_alpha_dummy_178), (nb057_alpha_dummy_179 f)),
                                  ((nb057_alpha_dummy_174), (nb057_alpha_dummy_176 f)),
                                  ((nb057_alpha_dummy_175), (nb057_alpha_dummy_177 f)),
                                  ((nb057_alpha_dummy_200), (nb057_alpha_dummy_201 f)),
                                  ((nb057_alpha_dummy_198), (nb057_alpha_dummy_199 f)),
                                  ((nb057_alpha_dummy_167), (nb057_alpha_dummy_169 f)),
                                  ((nb057_alpha_dummy_166), (nb057_alpha_dummy_168 f)),
                                  ((nb057_alpha_dummy_196), (nb057_alpha_dummy_197 f)),
                                  ((nb057_alpha_dummy_170), (nb057_alpha_dummy_171 f)),
                                  ((nb057_alpha_dummy_125), (nb057_alpha_dummy_127 f)),
                                  ((nb057_alpha_dummy_124), (nb057_alpha_dummy_126 f)),
                                  ((nb057_alpha_dummy_128), (nb057_alpha_dummy_129 f)),
                                  ((nb057_alpha_dummy_046), (nb057_alpha_dummy_049 f)),
                                  ((nb057_alpha_dummy_045), (nb057_alpha_dummy_048 f)),
                                  ((nb057_alpha_dummy_044), (nb057_alpha_dummy_047 f)),
                                  ((nb057_alpha_dummy_050), (nb057_alpha_dummy_051 f)),
                                  ((nb057_alpha_dummy_000), a), ((nb057_alpha_dummy_001), f),
                                  ((nb057_alpha_dummy_002), (nb057_alpha_dummy_003 f a))]
                                (syn_c1c) (by simp only [fv_syn_c1c])))
                            (TAlphaWff.neg (nb057_split_alpha_0050 f a))))))))
                (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there
                      (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0172) 0))
                      (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0173 f) 0))
                      (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
                    [((nb057_alpha_dummy_178), (nb057_alpha_dummy_179 f)),
                      ((nb057_alpha_dummy_174), (nb057_alpha_dummy_176 f)),
                      ((nb057_alpha_dummy_175), (nb057_alpha_dummy_177 f)),
                      ((nb057_alpha_dummy_200), (nb057_alpha_dummy_201 f)),
                      ((nb057_alpha_dummy_198), (nb057_alpha_dummy_199 f)),
                      ((nb057_alpha_dummy_167), (nb057_alpha_dummy_169 f)),
                      ((nb057_alpha_dummy_166), (nb057_alpha_dummy_168 f)),
                      ((nb057_alpha_dummy_196), (nb057_alpha_dummy_197 f)),
                      ((nb057_alpha_dummy_170), (nb057_alpha_dummy_171 f)),
                      ((nb057_alpha_dummy_125), (nb057_alpha_dummy_127 f)),
                      ((nb057_alpha_dummy_124), (nb057_alpha_dummy_126 f)),
                      ((nb057_alpha_dummy_128), (nb057_alpha_dummy_129 f)),
                      ((nb057_alpha_dummy_046), (nb057_alpha_dummy_049 f)),
                      ((nb057_alpha_dummy_045), (nb057_alpha_dummy_048 f)),
                      ((nb057_alpha_dummy_044), (nb057_alpha_dummy_047 f)),
                      ((nb057_alpha_dummy_050), (nb057_alpha_dummy_051 f)),
                      ((nb057_alpha_dummy_000), a), ((nb057_alpha_dummy_001), f),
                      ((nb057_alpha_dummy_002), (nb057_alpha_dummy_003 f a))]
                    (syn_cnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                  (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0172) 0))
                    (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0173 f) 0))
                    (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv
                    (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0172) 0))
                      (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0173 f) 0))
                      (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
                    [((nb057_alpha_dummy_178), (nb057_alpha_dummy_179 f)),
                      ((nb057_alpha_dummy_174), (nb057_alpha_dummy_176 f)),
                      ((nb057_alpha_dummy_175), (nb057_alpha_dummy_177 f)),
                      ((nb057_alpha_dummy_200), (nb057_alpha_dummy_201 f)),
                      ((nb057_alpha_dummy_198), (nb057_alpha_dummy_199 f)),
                      ((nb057_alpha_dummy_167), (nb057_alpha_dummy_169 f)),
                      ((nb057_alpha_dummy_166), (nb057_alpha_dummy_168 f)),
                      ((nb057_alpha_dummy_196), (nb057_alpha_dummy_197 f)),
                      ((nb057_alpha_dummy_170), (nb057_alpha_dummy_171 f)),
                      ((nb057_alpha_dummy_125), (nb057_alpha_dummy_127 f)),
                      ((nb057_alpha_dummy_124), (nb057_alpha_dummy_126 f)),
                      ((nb057_alpha_dummy_128), (nb057_alpha_dummy_129 f)),
                      ((nb057_alpha_dummy_046), (nb057_alpha_dummy_049 f)),
                      ((nb057_alpha_dummy_045), (nb057_alpha_dummy_048 f)),
                      ((nb057_alpha_dummy_044), (nb057_alpha_dummy_047 f)),
                      ((nb057_alpha_dummy_050), (nb057_alpha_dummy_051 f)),
                      ((nb057_alpha_dummy_000), a), ((nb057_alpha_dummy_001), f),
                      ((nb057_alpha_dummy_002), (nb057_alpha_dummy_003 f a))]
                    (syn_cnnc) (by simp only [fv_syn_cnnc]))))))))))


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

@[expose]
noncomputable def nb057_split_alpha_0052 (f : Var) (a : Var) :
    TAlphaWff
      [((nb057_alpha_dummy_196), (nb057_alpha_dummy_197 f)),
        ((nb057_alpha_dummy_170), (nb057_alpha_dummy_171 f)),
        ((nb057_alpha_dummy_125), (nb057_alpha_dummy_127 f)),
        ((nb057_alpha_dummy_124), (nb057_alpha_dummy_126 f)),
        ((nb057_alpha_dummy_128), (nb057_alpha_dummy_129 f)),
        ((nb057_alpha_dummy_046), (nb057_alpha_dummy_049 f)),
        ((nb057_alpha_dummy_045), (nb057_alpha_dummy_048 f)),
        ((nb057_alpha_dummy_044), (nb057_alpha_dummy_047 f)),
        ((nb057_alpha_dummy_050), (nb057_alpha_dummy_051 f)),
        ((nb057_alpha_dummy_000), a), ((nb057_alpha_dummy_001), f),
        ((nb057_alpha_dummy_002), (nb057_alpha_dummy_003 f a))]
      (Wff.imp (Wff.classMem (Class.cv (nb057_alpha_dummy_196))
          (Class.cab (nb057_alpha_dummy_166)
            (syn_wrex (nb057_alpha_dummy_167) (Class.cv (nb057_alpha_dummy_124))
              (Wff.classEq (Class.cv (nb057_alpha_dummy_166))
                (syn_cun (syn_cphi (Class.cv (nb057_alpha_dummy_167))) (syn_csn (syn_c0c)))))))
        (Wff.neg (Wff.classMem (Class.cv (nb057_alpha_dummy_196))
            (Class.cab (nb057_alpha_dummy_166)
              (syn_wrex (nb057_alpha_dummy_167) (Class.cv (nb057_alpha_dummy_124))
                (Wff.classEq (Class.cv (nb057_alpha_dummy_166))
                  (syn_cun (syn_cphi (Class.cv (nb057_alpha_dummy_167)))
                    (syn_csn (syn_c0c)))))))))
      (Wff.imp (Wff.classMem (Class.cv (nb057_alpha_dummy_197 f))
          (Class.cab (nb057_alpha_dummy_168 f)
            (syn_wrex (nb057_alpha_dummy_169 f) (Class.cv (nb057_alpha_dummy_126 f))
              (Wff.classEq (Class.cv (nb057_alpha_dummy_168 f))
                (syn_cun (syn_cphi (Class.cv (nb057_alpha_dummy_169 f)))
                  (syn_csn (syn_c0c))))))) (Wff.neg
          (Wff.classMem (Class.cv (nb057_alpha_dummy_197 f))
            (Class.cab (nb057_alpha_dummy_168 f)
              (syn_wrex (nb057_alpha_dummy_169 f) (Class.cv (nb057_alpha_dummy_126 f))
                (Wff.classEq (Class.cv (nb057_alpha_dummy_168 f))
                  (syn_cun (syn_cphi (Class.cv (nb057_alpha_dummy_169 f)))
                    (syn_csn (syn_c0c))))))))) :=
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
                          (freshVar_injective (((Class.cv (nb057_alpha_dummy_001))).fv)
                            (by decide)) (freshVar_injective (((Class.cv f)).fv) (by decide))
                          (TAlphaVar.here _ _ _)))))))) (TAlphaWff.classEq (TAlphaClass.cv
                (TAlphaVar.there (freshVar_injective (((Class.cv (nb057_alpha_dummy_125))).fv ∪
                      ((Class.cv (nb057_alpha_dummy_124))).fv) (by decide)) (freshVar_injective
                    (((Class.cv (nb057_alpha_dummy_127 f))).fv ∪
                      ((Class.cv (nb057_alpha_dummy_126 f))).fv) (by decide))
                  (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                        (TAlphaWff.neg (TAlphaWff.conj
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cab (TAlphaWff.ex
                                  (TAlphaWff.neg (nb057_split_alpha_0051 f a)))))
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cab (TAlphaWff.ex
                                  (TAlphaWff.neg (nb057_split_alpha_0051 f a)))))))))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                      (TAlphaClass.refl_of_closed
                        [((nb057_alpha_dummy_198), (nb057_alpha_dummy_199 f)),
                          ((nb057_alpha_dummy_167), (nb057_alpha_dummy_169 f)),
                          ((nb057_alpha_dummy_166), (nb057_alpha_dummy_168 f)),
                          ((nb057_alpha_dummy_196), (nb057_alpha_dummy_197 f)),
                          ((nb057_alpha_dummy_170), (nb057_alpha_dummy_171 f)),
                          ((nb057_alpha_dummy_125), (nb057_alpha_dummy_127 f)),
                          ((nb057_alpha_dummy_124), (nb057_alpha_dummy_126 f)),
                          ((nb057_alpha_dummy_128), (nb057_alpha_dummy_129 f)),
                          ((nb057_alpha_dummy_046), (nb057_alpha_dummy_049 f)),
                          ((nb057_alpha_dummy_045), (nb057_alpha_dummy_048 f)),
                          ((nb057_alpha_dummy_044), (nb057_alpha_dummy_047 f)),
                          ((nb057_alpha_dummy_050), (nb057_alpha_dummy_051 f)),
                          ((nb057_alpha_dummy_000), a), ((nb057_alpha_dummy_001), f),
                          ((nb057_alpha_dummy_002), (nb057_alpha_dummy_003 f a))]
                        (syn_ccompl (syn_csn (syn_c0c)))
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
                            (freshVar_injective (((Class.cv (nb057_alpha_dummy_001))).fv)
                              (by decide)) (freshVar_injective (((Class.cv f)).fv) (by decide))
                            (TAlphaVar.here _ _ _)))))))) (TAlphaWff.classEq (TAlphaClass.cv
                  (TAlphaVar.there (freshVar_injective
                      (((Class.cv (nb057_alpha_dummy_125))).fv ∪
                        ((Class.cv (nb057_alpha_dummy_124))).fv) (by decide))
                    (freshVar_injective (((Class.cv (nb057_alpha_dummy_127 f))).fv ∪
                        ((Class.cv (nb057_alpha_dummy_126 f))).fv) (by decide))
                    (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cab (TAlphaWff.ex
                                    (TAlphaWff.neg (nb057_split_alpha_0051 f a)))))
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cab (TAlphaWff.ex
                                    (TAlphaWff.neg (nb057_split_alpha_0051 f a)))))))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.refl_of_closed
                          [((nb057_alpha_dummy_198), (nb057_alpha_dummy_199 f)),
                            ((nb057_alpha_dummy_167), (nb057_alpha_dummy_169 f)),
                            ((nb057_alpha_dummy_166), (nb057_alpha_dummy_168 f)),
                            ((nb057_alpha_dummy_196), (nb057_alpha_dummy_197 f)),
                            ((nb057_alpha_dummy_170), (nb057_alpha_dummy_171 f)),
                            ((nb057_alpha_dummy_125), (nb057_alpha_dummy_127 f)),
                            ((nb057_alpha_dummy_124), (nb057_alpha_dummy_126 f)),
                            ((nb057_alpha_dummy_128), (nb057_alpha_dummy_129 f)),
                            ((nb057_alpha_dummy_046), (nb057_alpha_dummy_049 f)),
                            ((nb057_alpha_dummy_045), (nb057_alpha_dummy_048 f)),
                            ((nb057_alpha_dummy_044), (nb057_alpha_dummy_047 f)),
                            ((nb057_alpha_dummy_050), (nb057_alpha_dummy_051 f)),
                            ((nb057_alpha_dummy_000), a), ((nb057_alpha_dummy_001), f),
                            ((nb057_alpha_dummy_002), (nb057_alpha_dummy_003 f a))]
                          (syn_ccompl (syn_csn (syn_c0c))) (by
                            simp only [fv_syn_ccompl, fv_syn_csn, fv_syn_c0c])))))))))))))

@[expose]
noncomputable def nb057_direct_function_variable_occurrence (f : Var) (a : Var)
    (dv_a_f : a ≠ f) :
    TAlphaClass
      [((nb057_alpha_dummy_125), (nb057_alpha_dummy_127 f)),
        ((nb057_alpha_dummy_124), (nb057_alpha_dummy_126 f)),
        ((nb057_alpha_dummy_128), (nb057_alpha_dummy_129 f)),
        ((nb057_alpha_dummy_046), (nb057_alpha_dummy_049 f)),
        ((nb057_alpha_dummy_045), (nb057_alpha_dummy_048 f)),
        ((nb057_alpha_dummy_044), (nb057_alpha_dummy_047 f)),
        ((nb057_alpha_dummy_050), (nb057_alpha_dummy_051 f)),
        ((nb057_alpha_dummy_000), a), ((nb057_alpha_dummy_001), f),
        ((nb057_alpha_dummy_002), (nb057_alpha_dummy_003 f a))]
      (Class.cv (nb057_alpha_dummy_001)) (Class.cv f) :=
  by
  have freshness0 : (nb057_alpha_dummy_001) ≠ (nb057_alpha_dummy_125) :=
    by
    unfold nb057_alpha_dummy_125
    with_reducible exact (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0212) 1))
  have freshness1 : f ≠ (nb057_alpha_dummy_127 f) :=
    by
    unfold nb057_alpha_dummy_127
    with_reducible exact (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0213 f) 1))
  have freshness2 : (nb057_alpha_dummy_001) ≠ (nb057_alpha_dummy_124) :=
    by
    unfold nb057_alpha_dummy_124
    with_reducible exact (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0212) 0))
  have freshness3 : f ≠ (nb057_alpha_dummy_126 f) :=
    by
    unfold nb057_alpha_dummy_126
    with_reducible exact (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0213 f) 0))
  have freshness4 : (nb057_alpha_dummy_001) ≠ (nb057_alpha_dummy_128) :=
    by
    unfold nb057_alpha_dummy_128
    with_reducible exact (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0210) 0))
  have freshness5 : f ≠ (nb057_alpha_dummy_129 f) :=
    by
    unfold nb057_alpha_dummy_129
    with_reducible exact (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0211 f) 0))
  have freshness6 : (nb057_alpha_dummy_001) ≠ (nb057_alpha_dummy_046) :=
    by
    unfold nb057_alpha_dummy_046
    with_reducible exact (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0206) 2))
  have freshness7 : f ≠ (nb057_alpha_dummy_049 f) :=
    by
    unfold nb057_alpha_dummy_049
    with_reducible exact (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0208 f) 2))
  have freshness8 : (nb057_alpha_dummy_001) ≠ (nb057_alpha_dummy_045) :=
    by
    unfold nb057_alpha_dummy_045
    with_reducible exact (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0206) 1))
  have freshness9 : f ≠ (nb057_alpha_dummy_048 f) :=
    by
    unfold nb057_alpha_dummy_048
    with_reducible exact (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0208 f) 1))
  have freshness10 : (nb057_alpha_dummy_001) ≠ (nb057_alpha_dummy_044) :=
    by
    unfold nb057_alpha_dummy_044
    with_reducible exact (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0206) 0))
  have freshness11 : f ≠ (nb057_alpha_dummy_047 f) :=
    by
    unfold nb057_alpha_dummy_047
    with_reducible exact (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0208 f) 0))
  have freshness12 : (nb057_alpha_dummy_001) ≠ (nb057_alpha_dummy_050) :=
    by
    unfold nb057_alpha_dummy_050
    with_reducible exact (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0207) 0))
  have freshness13 : f ≠ (nb057_alpha_dummy_051 f) :=
    by
    unfold nb057_alpha_dummy_051
    with_reducible exact (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0209 f) 0))
  have freshness14 : (nb057_alpha_dummy_001) ≠ (nb057_alpha_dummy_000) :=
    by
    unfold nb057_alpha_dummy_001 nb057_alpha_dummy_000
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

@[expose]
noncomputable def nb057_split_alpha_0053 (f : Var) (a : Var) (dv_a_f : a ≠ f) :
    TAlphaWff
      [((nb057_alpha_dummy_125), (nb057_alpha_dummy_127 f)),
        ((nb057_alpha_dummy_124), (nb057_alpha_dummy_126 f)),
        ((nb057_alpha_dummy_128), (nb057_alpha_dummy_129 f)),
        ((nb057_alpha_dummy_046), (nb057_alpha_dummy_049 f)),
        ((nb057_alpha_dummy_045), (nb057_alpha_dummy_048 f)),
        ((nb057_alpha_dummy_044), (nb057_alpha_dummy_047 f)),
        ((nb057_alpha_dummy_050), (nb057_alpha_dummy_051 f)),
        ((nb057_alpha_dummy_000), a), ((nb057_alpha_dummy_001), f),
        ((nb057_alpha_dummy_002), (nb057_alpha_dummy_003 f a))]
      (Wff.imp (Wff.classEq (Class.cv (nb057_alpha_dummy_128))
          (syn_cop (Class.cv (nb057_alpha_dummy_124)) (Class.cv (nb057_alpha_dummy_125))))
        (Wff.neg (syn_wbr (Class.cv (nb057_alpha_dummy_125)) (Class.cv (nb057_alpha_dummy_001))
            (Class.cv (nb057_alpha_dummy_124)))))
      (Wff.imp (Wff.classEq (Class.cv (nb057_alpha_dummy_129 f))
          (syn_cop (Class.cv (nb057_alpha_dummy_126 f)) (Class.cv (nb057_alpha_dummy_127 f))))
        (Wff.neg (syn_wbr (Class.cv (nb057_alpha_dummy_127 f)) (Class.cv f)
            (Class.cv (nb057_alpha_dummy_126 f))))) :=
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
        (((Class.cv (nb057_alpha_dummy_001))).fv) (by decide))
        (freshVar_injective (((Class.cv f)).fv) (by decide)) (TAlphaVar.here _ _ _))))))))
                            (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there
                                  (freshVar_injective (((Class.cv (nb057_alpha_dummy_124))).fv ∪
                                      ((Class.cv (nb057_alpha_dummy_125))).fv) (by decide))
                                  (freshVar_injective
                                    (((Class.cv (nb057_alpha_dummy_126 f))).fv ∪
                                      ((Class.cv (nb057_alpha_dummy_127 f))).fv) (by decide))
                                  (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.ex
                                  (TAlphaWff.neg (nb057_split_alpha_0044 f a)))))))))
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
        (((Class.cv (nb057_alpha_dummy_001))).fv) (by decide))
        (freshVar_injective (((Class.cv f)).fv) (by decide)) (TAlphaVar.here _ _ _))))))))
                            (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there
                                  (freshVar_injective (((Class.cv (nb057_alpha_dummy_124))).fv ∪
                                      ((Class.cv (nb057_alpha_dummy_125))).fv) (by decide))
                                  (freshVar_injective
                                    (((Class.cv (nb057_alpha_dummy_126 f))).fv ∪
                                      ((Class.cv (nb057_alpha_dummy_127 f))).fv) (by decide))
                                  (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.ex
                                  (TAlphaWff.neg (nb057_split_alpha_0044 f a)))))))))))))
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.neg (TAlphaWff.neg (nb057_split_alpha_0047 f a)))))))))
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
                                      (((Class.cv (nb057_alpha_dummy_125))).fv ∪
                                        ((Class.cv (nb057_alpha_dummy_124))).fv) (by decide))
                                    (freshVar_injective
                                      (((Class.cv (nb057_alpha_dummy_127 f))).fv ∪
                                        ((Class.cv (nb057_alpha_dummy_126 f))).fv) (by decide))
                                    (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.ex
                                    (TAlphaWff.neg (nb057_split_alpha_0049 f a)))))))))
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
                                      (((Class.cv (nb057_alpha_dummy_125))).fv ∪
                                        ((Class.cv (nb057_alpha_dummy_124))).fv) (by decide))
                                    (freshVar_injective
                                      (((Class.cv (nb057_alpha_dummy_127 f))).fv ∪
                                        ((Class.cv (nb057_alpha_dummy_126 f))).fv) (by decide))
                                    (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.ex
                                    (TAlphaWff.neg (nb057_split_alpha_0049 f a)))))))))))))
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                  (TAlphaWff.neg (TAlphaWff.neg (nb057_split_alpha_0052 f a))))))))
        (nb057_direct_function_variable_occurrence f a dv_a_f))))

@[expose]
noncomputable def nb057_split_alpha_0054 (f : Var) (a : Var) :
    TAlphaWff
      [((nb057_alpha_dummy_218), (nb057_alpha_dummy_221 f)),
        ((nb057_alpha_dummy_217), (nb057_alpha_dummy_220 f)),
        ((nb057_alpha_dummy_216), (nb057_alpha_dummy_219 f)),
        ((nb057_alpha_dummy_214), (nb057_alpha_dummy_215 f)),
        ((nb057_alpha_dummy_210), (nb057_alpha_dummy_212 f)),
        ((nb057_alpha_dummy_211), (nb057_alpha_dummy_213 f)),
        ((nb057_alpha_dummy_203), (nb057_alpha_dummy_205 f)),
        ((nb057_alpha_dummy_202), (nb057_alpha_dummy_204 f)),
        ((nb057_alpha_dummy_208), (nb057_alpha_dummy_209 f)),
        ((nb057_alpha_dummy_206), (nb057_alpha_dummy_207 f)),
        ((nb057_alpha_dummy_046), (nb057_alpha_dummy_049 f)),
        ((nb057_alpha_dummy_045), (nb057_alpha_dummy_048 f)),
        ((nb057_alpha_dummy_044), (nb057_alpha_dummy_047 f)),
        ((nb057_alpha_dummy_050), (nb057_alpha_dummy_051 f)),
        ((nb057_alpha_dummy_000), a), ((nb057_alpha_dummy_001), f),
        ((nb057_alpha_dummy_002), (nb057_alpha_dummy_003 f a))]
      (Wff.imp (Wff.classEq
          (syn_cin (Class.cv (nb057_alpha_dummy_217)) (Class.cv (nb057_alpha_dummy_218)))
          (syn_c0)) (Wff.neg (Wff.classEq (Class.cv (nb057_alpha_dummy_216))
            (syn_cun (Class.cv (nb057_alpha_dummy_217)) (Class.cv (nb057_alpha_dummy_218))))))
      (Wff.imp (Wff.classEq (syn_cin (Class.cv (nb057_alpha_dummy_220 f))
            (Class.cv (nb057_alpha_dummy_221 f))) (syn_c0)) (Wff.neg
          (Wff.classEq (Class.cv (nb057_alpha_dummy_219 f))
            (syn_cun (Class.cv (nb057_alpha_dummy_220 f))
              (Class.cv (nb057_alpha_dummy_221 f)))))) :=
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
                                (((Class.cv (nb057_alpha_dummy_210))).fv ∪ ((syn_c1c)).fv)
                                (by decide)) (freshVar_injective
                                (((Class.cv (nb057_alpha_dummy_212 f))).fv ∪ ((syn_c1c)).fv)
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
                                (((Class.cv (nb057_alpha_dummy_210))).fv ∪ ((syn_c1c)).fv)
                                (by decide)) (freshVar_injective
                                (((Class.cv (nb057_alpha_dummy_212 f))).fv ∪ ((syn_c1c)).fv)
                                (by decide)) (TAlphaVar.here _ _ _))))))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0232) 0))
                          (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0233 f) 0))
                          (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0230) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0231 f) 0))
                            (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.refl_of_closed
        [((nb057_alpha_dummy_218), (nb057_alpha_dummy_221 f)),
          ((nb057_alpha_dummy_217), (nb057_alpha_dummy_220 f)),
          ((nb057_alpha_dummy_216), (nb057_alpha_dummy_219 f)),
          ((nb057_alpha_dummy_214), (nb057_alpha_dummy_215 f)),
          ((nb057_alpha_dummy_210), (nb057_alpha_dummy_212 f)),
          ((nb057_alpha_dummy_211), (nb057_alpha_dummy_213 f)),
          ((nb057_alpha_dummy_203), (nb057_alpha_dummy_205 f)),
          ((nb057_alpha_dummy_202), (nb057_alpha_dummy_204 f)),
          ((nb057_alpha_dummy_208), (nb057_alpha_dummy_209 f)),
          ((nb057_alpha_dummy_206), (nb057_alpha_dummy_207 f)),
          ((nb057_alpha_dummy_046), (nb057_alpha_dummy_049 f)),
          ((nb057_alpha_dummy_045), (nb057_alpha_dummy_048 f)),
          ((nb057_alpha_dummy_044), (nb057_alpha_dummy_047 f)),
          ((nb057_alpha_dummy_050), (nb057_alpha_dummy_051 f)),
          ((nb057_alpha_dummy_000), a), ((nb057_alpha_dummy_001), f),
          ((nb057_alpha_dummy_002), (nb057_alpha_dummy_003 f a))]
        (syn_c0) (by simp only [fv_syn_c0]))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv
          (TAlphaVar.there
            (freshVar_injective (((Class.cv (nb057_alpha_dummy_210))).fv ∪ ((syn_c1c)).fv)
              (by decide)) (freshVar_injective
              (((Class.cv (nb057_alpha_dummy_212 f))).fv ∪ ((syn_c1c)).fv) (by decide))
            (TAlphaVar.there (freshVar_injective
                (((Class.cv (nb057_alpha_dummy_210))).fv ∪ ((syn_c1c)).fv) (by decide))
              (freshVar_injective
                (((Class.cv (nb057_alpha_dummy_212 f))).fv ∪ ((syn_c1c)).fv) (by decide))
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
                                  (((Class.cv (nb057_alpha_dummy_210))).fv ∪ ((syn_c1c)).fv)
                                  (by decide)) (freshVar_injective
                                  (((Class.cv (nb057_alpha_dummy_212 f))).fv ∪ ((syn_c1c)).fv)
                                  (by decide)) (TAlphaVar.here _ _ _))))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0236) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0237 f) 0))
                            (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0234) 0))
                              (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0235 f) 0))
                              (TAlphaVar.there (freshVar_injective
                                  (((Class.cv (nb057_alpha_dummy_210))).fv ∪ ((syn_c1c)).fv)
                                  (by decide)) (freshVar_injective
                                  (((Class.cv (nb057_alpha_dummy_212 f))).fv ∪ ((syn_c1c)).fv)
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

@[expose]
noncomputable def nb057_split_alpha_0055 (f : Var) (a : Var) :
    TAlphaWff
      [((nb057_alpha_dummy_203), (nb057_alpha_dummy_205 f)),
        ((nb057_alpha_dummy_202), (nb057_alpha_dummy_204 f)),
        ((nb057_alpha_dummy_208), (nb057_alpha_dummy_209 f)),
        ((nb057_alpha_dummy_206), (nb057_alpha_dummy_207 f)),
        ((nb057_alpha_dummy_046), (nb057_alpha_dummy_049 f)),
        ((nb057_alpha_dummy_045), (nb057_alpha_dummy_048 f)),
        ((nb057_alpha_dummy_044), (nb057_alpha_dummy_047 f)),
        ((nb057_alpha_dummy_050), (nb057_alpha_dummy_051 f)),
        ((nb057_alpha_dummy_000), a), ((nb057_alpha_dummy_001), f),
        ((nb057_alpha_dummy_002), (nb057_alpha_dummy_003 f a))]
      (Wff.classEq (Class.cv (nb057_alpha_dummy_202))
        (syn_cphi (Class.cv (nb057_alpha_dummy_203))))
      (Wff.classEq (Class.cv (nb057_alpha_dummy_204 f))
        (syn_cphi (Class.cv (nb057_alpha_dummy_205 f)))) :=
  (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there (freshVar_injective
          (((Class.cv (nb057_alpha_dummy_046))).fv ∪ ((Class.cv (nb057_alpha_dummy_045))).fv)
          (by decide)) (freshVar_injective (((Class.cv (nb057_alpha_dummy_049 f))).fv ∪
            ((Class.cv (nb057_alpha_dummy_048 f))).fv) (by decide)) (TAlphaVar.here _ _ _)))
    (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
          (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
              (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0220) 0))
                (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0221 f) 0)) (TAlphaVar.there
                  (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0220) 1))
                  (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0221 f) 1))
                  (TAlphaVar.here _ _ _))))) (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there
                (freshVar_injective (((Class.cv (nb057_alpha_dummy_203))).fv) (by decide))
                (freshVar_injective (((Class.cv (nb057_alpha_dummy_205 f))).fv) (by decide))
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
                                  (TAlphaClass.refl_of_closed
                                    [((nb057_alpha_dummy_218), (nb057_alpha_dummy_221 f)),
                                      ((nb057_alpha_dummy_217), (nb057_alpha_dummy_220 f)),
                                      ((nb057_alpha_dummy_216), (nb057_alpha_dummy_219 f)),
                                      ((nb057_alpha_dummy_214), (nb057_alpha_dummy_215 f)),
                                      ((nb057_alpha_dummy_210), (nb057_alpha_dummy_212 f)),
                                      ((nb057_alpha_dummy_211), (nb057_alpha_dummy_213 f)),
                                      ((nb057_alpha_dummy_203), (nb057_alpha_dummy_205 f)),
                                      ((nb057_alpha_dummy_202), (nb057_alpha_dummy_204 f)),
                                      ((nb057_alpha_dummy_208), (nb057_alpha_dummy_209 f)),
                                      ((nb057_alpha_dummy_206), (nb057_alpha_dummy_207 f)),
                                      ((nb057_alpha_dummy_046), (nb057_alpha_dummy_049 f)),
                                      ((nb057_alpha_dummy_045), (nb057_alpha_dummy_048 f)),
                                      ((nb057_alpha_dummy_044), (nb057_alpha_dummy_047 f)),
                                      ((nb057_alpha_dummy_050), (nb057_alpha_dummy_051 f)),
                                      ((nb057_alpha_dummy_000), a),
                                      ((nb057_alpha_dummy_001), f), ((nb057_alpha_dummy_002),
                                        (nb057_alpha_dummy_003 f a))]
                                    (syn_c1c) (by simp only [fv_syn_c1c])))
                                (TAlphaWff.neg (nb057_split_alpha_0054 f a))))))))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there
                          (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0222) 0))
                          (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0223 f) 0))
                          (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
                        [((nb057_alpha_dummy_214), (nb057_alpha_dummy_215 f)),
                          ((nb057_alpha_dummy_210), (nb057_alpha_dummy_212 f)),
                          ((nb057_alpha_dummy_211), (nb057_alpha_dummy_213 f)),
                          ((nb057_alpha_dummy_203), (nb057_alpha_dummy_205 f)),
                          ((nb057_alpha_dummy_202), (nb057_alpha_dummy_204 f)),
                          ((nb057_alpha_dummy_208), (nb057_alpha_dummy_209 f)),
                          ((nb057_alpha_dummy_206), (nb057_alpha_dummy_207 f)),
                          ((nb057_alpha_dummy_046), (nb057_alpha_dummy_049 f)),
                          ((nb057_alpha_dummy_045), (nb057_alpha_dummy_048 f)),
                          ((nb057_alpha_dummy_044), (nb057_alpha_dummy_047 f)),
                          ((nb057_alpha_dummy_050), (nb057_alpha_dummy_051 f)),
                          ((nb057_alpha_dummy_000), a), ((nb057_alpha_dummy_001), f),
                          ((nb057_alpha_dummy_002), (nb057_alpha_dummy_003 f a))]
                        (syn_cnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
                  (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                      (TAlphaVar.there
                        (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0222) 0))
                        (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0223 f) 0))
                        (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.classMem
                      (TAlphaClass.cv (TAlphaVar.there
                          (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0222) 0))
                          (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0223 f) 0))
                          (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
                        [((nb057_alpha_dummy_214), (nb057_alpha_dummy_215 f)),
                          ((nb057_alpha_dummy_210), (nb057_alpha_dummy_212 f)),
                          ((nb057_alpha_dummy_211), (nb057_alpha_dummy_213 f)),
                          ((nb057_alpha_dummy_203), (nb057_alpha_dummy_205 f)),
                          ((nb057_alpha_dummy_202), (nb057_alpha_dummy_204 f)),
                          ((nb057_alpha_dummy_208), (nb057_alpha_dummy_209 f)),
                          ((nb057_alpha_dummy_206), (nb057_alpha_dummy_207 f)),
                          ((nb057_alpha_dummy_046), (nb057_alpha_dummy_049 f)),
                          ((nb057_alpha_dummy_045), (nb057_alpha_dummy_048 f)),
                          ((nb057_alpha_dummy_044), (nb057_alpha_dummy_047 f)),
                          ((nb057_alpha_dummy_050), (nb057_alpha_dummy_051 f)),
                          ((nb057_alpha_dummy_000), a), ((nb057_alpha_dummy_001), f),
                          ((nb057_alpha_dummy_002), (nb057_alpha_dummy_003 f a))]
                        (syn_cnnc) (by simp only [fv_syn_cnnc]))))))))))))

@[expose]
noncomputable def nb057_split_alpha_0056 (f : Var) (a : Var) :
    TAlphaWff
      [((nb057_alpha_dummy_218), (nb057_alpha_dummy_221 f)),
        ((nb057_alpha_dummy_217), (nb057_alpha_dummy_220 f)),
        ((nb057_alpha_dummy_216), (nb057_alpha_dummy_219 f)),
        ((nb057_alpha_dummy_214), (nb057_alpha_dummy_215 f)),
        ((nb057_alpha_dummy_210), (nb057_alpha_dummy_212 f)),
        ((nb057_alpha_dummy_211), (nb057_alpha_dummy_213 f)),
        ((nb057_alpha_dummy_236), (nb057_alpha_dummy_237 f)),
        ((nb057_alpha_dummy_234), (nb057_alpha_dummy_235 f)),
        ((nb057_alpha_dummy_203), (nb057_alpha_dummy_205 f)),
        ((nb057_alpha_dummy_202), (nb057_alpha_dummy_204 f)),
        ((nb057_alpha_dummy_232), (nb057_alpha_dummy_233 f)),
        ((nb057_alpha_dummy_206), (nb057_alpha_dummy_207 f)),
        ((nb057_alpha_dummy_046), (nb057_alpha_dummy_049 f)),
        ((nb057_alpha_dummy_045), (nb057_alpha_dummy_048 f)),
        ((nb057_alpha_dummy_044), (nb057_alpha_dummy_047 f)),
        ((nb057_alpha_dummy_050), (nb057_alpha_dummy_051 f)),
        ((nb057_alpha_dummy_000), a), ((nb057_alpha_dummy_001), f),
        ((nb057_alpha_dummy_002), (nb057_alpha_dummy_003 f a))]
      (Wff.imp (Wff.classEq
          (syn_cin (Class.cv (nb057_alpha_dummy_217)) (Class.cv (nb057_alpha_dummy_218)))
          (syn_c0)) (Wff.neg (Wff.classEq (Class.cv (nb057_alpha_dummy_216))
            (syn_cun (Class.cv (nb057_alpha_dummy_217)) (Class.cv (nb057_alpha_dummy_218))))))
      (Wff.imp (Wff.classEq (syn_cin (Class.cv (nb057_alpha_dummy_220 f))
            (Class.cv (nb057_alpha_dummy_221 f))) (syn_c0)) (Wff.neg
          (Wff.classEq (Class.cv (nb057_alpha_dummy_219 f))
            (syn_cun (Class.cv (nb057_alpha_dummy_220 f))
              (Class.cv (nb057_alpha_dummy_221 f)))))) :=
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
                                (((Class.cv (nb057_alpha_dummy_210))).fv ∪ ((syn_c1c)).fv)
                                (by decide)) (freshVar_injective
                                (((Class.cv (nb057_alpha_dummy_212 f))).fv ∪ ((syn_c1c)).fv)
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
                                (((Class.cv (nb057_alpha_dummy_210))).fv ∪ ((syn_c1c)).fv)
                                (by decide)) (freshVar_injective
                                (((Class.cv (nb057_alpha_dummy_212 f))).fv ∪ ((syn_c1c)).fv)
                                (by decide)) (TAlphaVar.here _ _ _))))))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0232) 0))
                          (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0233 f) 0))
                          (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0230) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0231 f) 0))
                            (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.refl_of_closed
        [((nb057_alpha_dummy_218), (nb057_alpha_dummy_221 f)),
          ((nb057_alpha_dummy_217), (nb057_alpha_dummy_220 f)),
          ((nb057_alpha_dummy_216), (nb057_alpha_dummy_219 f)),
          ((nb057_alpha_dummy_214), (nb057_alpha_dummy_215 f)),
          ((nb057_alpha_dummy_210), (nb057_alpha_dummy_212 f)),
          ((nb057_alpha_dummy_211), (nb057_alpha_dummy_213 f)),
          ((nb057_alpha_dummy_236), (nb057_alpha_dummy_237 f)),
          ((nb057_alpha_dummy_234), (nb057_alpha_dummy_235 f)),
          ((nb057_alpha_dummy_203), (nb057_alpha_dummy_205 f)),
          ((nb057_alpha_dummy_202), (nb057_alpha_dummy_204 f)),
          ((nb057_alpha_dummy_232), (nb057_alpha_dummy_233 f)),
          ((nb057_alpha_dummy_206), (nb057_alpha_dummy_207 f)),
          ((nb057_alpha_dummy_046), (nb057_alpha_dummy_049 f)),
          ((nb057_alpha_dummy_045), (nb057_alpha_dummy_048 f)),
          ((nb057_alpha_dummy_044), (nb057_alpha_dummy_047 f)),
          ((nb057_alpha_dummy_050), (nb057_alpha_dummy_051 f)),
          ((nb057_alpha_dummy_000), a), ((nb057_alpha_dummy_001), f),
          ((nb057_alpha_dummy_002), (nb057_alpha_dummy_003 f a))]
        (syn_c0) (by simp only [fv_syn_c0]))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv
          (TAlphaVar.there
            (freshVar_injective (((Class.cv (nb057_alpha_dummy_210))).fv ∪ ((syn_c1c)).fv)
              (by decide)) (freshVar_injective
              (((Class.cv (nb057_alpha_dummy_212 f))).fv ∪ ((syn_c1c)).fv) (by decide))
            (TAlphaVar.there (freshVar_injective
                (((Class.cv (nb057_alpha_dummy_210))).fv ∪ ((syn_c1c)).fv) (by decide))
              (freshVar_injective
                (((Class.cv (nb057_alpha_dummy_212 f))).fv ∪ ((syn_c1c)).fv) (by decide))
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
                                  (((Class.cv (nb057_alpha_dummy_210))).fv ∪ ((syn_c1c)).fv)
                                  (by decide)) (freshVar_injective
                                  (((Class.cv (nb057_alpha_dummy_212 f))).fv ∪ ((syn_c1c)).fv)
                                  (by decide)) (TAlphaVar.here _ _ _))))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0236) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0237 f) 0))
                            (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0234) 0))
                              (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0235 f) 0))
                              (TAlphaVar.there (freshVar_injective
                                  (((Class.cv (nb057_alpha_dummy_210))).fv ∪ ((syn_c1c)).fv)
                                  (by decide)) (freshVar_injective
                                  (((Class.cv (nb057_alpha_dummy_212 f))).fv ∪ ((syn_c1c)).fv)
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

@[expose]
noncomputable def nb057_split_alpha_0057 (f : Var) (a : Var) :
    TAlphaWff
      [((nb057_alpha_dummy_210), (nb057_alpha_dummy_212 f)),
        ((nb057_alpha_dummy_211), (nb057_alpha_dummy_213 f)),
        ((nb057_alpha_dummy_236), (nb057_alpha_dummy_237 f)),
        ((nb057_alpha_dummy_234), (nb057_alpha_dummy_235 f)),
        ((nb057_alpha_dummy_203), (nb057_alpha_dummy_205 f)),
        ((nb057_alpha_dummy_202), (nb057_alpha_dummy_204 f)),
        ((nb057_alpha_dummy_232), (nb057_alpha_dummy_233 f)),
        ((nb057_alpha_dummy_206), (nb057_alpha_dummy_207 f)),
        ((nb057_alpha_dummy_046), (nb057_alpha_dummy_049 f)),
        ((nb057_alpha_dummy_045), (nb057_alpha_dummy_048 f)),
        ((nb057_alpha_dummy_044), (nb057_alpha_dummy_047 f)),
        ((nb057_alpha_dummy_050), (nb057_alpha_dummy_051 f)),
        ((nb057_alpha_dummy_000), a), ((nb057_alpha_dummy_001), f),
        ((nb057_alpha_dummy_002), (nb057_alpha_dummy_003 f a))]
      (Wff.imp (Wff.classMem (Class.cv (nb057_alpha_dummy_210))
          (Class.cv (nb057_alpha_dummy_203))) (Wff.neg
          (Wff.classEq (Class.cv (nb057_alpha_dummy_211))
            (syn_cif (Wff.classMem (Class.cv (nb057_alpha_dummy_210)) (syn_cnnc))
              (syn_cplc (Class.cv (nb057_alpha_dummy_210)) (syn_c1c))
              (Class.cv (nb057_alpha_dummy_210))))))
      (Wff.imp (Wff.classMem (Class.cv (nb057_alpha_dummy_212 f))
          (Class.cv (nb057_alpha_dummy_205 f))) (Wff.neg
          (Wff.classEq (Class.cv (nb057_alpha_dummy_213 f))
            (syn_cif (Wff.classMem (Class.cv (nb057_alpha_dummy_212 f)) (syn_cnnc))
              (syn_cplc (Class.cv (nb057_alpha_dummy_212 f)) (syn_c1c))
              (Class.cv (nb057_alpha_dummy_212 f)))))) :=
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
            (freshVar_injective (((Class.cv (nb057_alpha_dummy_203))).fv) (by decide))
            (freshVar_injective (((Class.cv (nb057_alpha_dummy_205 f))).fv) (by decide))
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
                              (TAlphaClass.refl_of_closed
                                [((nb057_alpha_dummy_218), (nb057_alpha_dummy_221 f)),
                                  ((nb057_alpha_dummy_217), (nb057_alpha_dummy_220 f)),
                                  ((nb057_alpha_dummy_216), (nb057_alpha_dummy_219 f)),
                                  ((nb057_alpha_dummy_214), (nb057_alpha_dummy_215 f)),
                                  ((nb057_alpha_dummy_210), (nb057_alpha_dummy_212 f)),
                                  ((nb057_alpha_dummy_211), (nb057_alpha_dummy_213 f)),
                                  ((nb057_alpha_dummy_236), (nb057_alpha_dummy_237 f)),
                                  ((nb057_alpha_dummy_234), (nb057_alpha_dummy_235 f)),
                                  ((nb057_alpha_dummy_203), (nb057_alpha_dummy_205 f)),
                                  ((nb057_alpha_dummy_202), (nb057_alpha_dummy_204 f)),
                                  ((nb057_alpha_dummy_232), (nb057_alpha_dummy_233 f)),
                                  ((nb057_alpha_dummy_206), (nb057_alpha_dummy_207 f)),
                                  ((nb057_alpha_dummy_046), (nb057_alpha_dummy_049 f)),
                                  ((nb057_alpha_dummy_045), (nb057_alpha_dummy_048 f)),
                                  ((nb057_alpha_dummy_044), (nb057_alpha_dummy_047 f)),
                                  ((nb057_alpha_dummy_050), (nb057_alpha_dummy_051 f)),
                                  ((nb057_alpha_dummy_000), a), ((nb057_alpha_dummy_001), f),
                                  ((nb057_alpha_dummy_002), (nb057_alpha_dummy_003 f a))]
                                (syn_c1c) (by simp only [fv_syn_c1c])))
                            (TAlphaWff.neg (nb057_split_alpha_0056 f a))))))))
                (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there
                      (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0222) 0))
                      (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0223 f) 0))
                      (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
                    [((nb057_alpha_dummy_214), (nb057_alpha_dummy_215 f)),
                      ((nb057_alpha_dummy_210), (nb057_alpha_dummy_212 f)),
                      ((nb057_alpha_dummy_211), (nb057_alpha_dummy_213 f)),
                      ((nb057_alpha_dummy_236), (nb057_alpha_dummy_237 f)),
                      ((nb057_alpha_dummy_234), (nb057_alpha_dummy_235 f)),
                      ((nb057_alpha_dummy_203), (nb057_alpha_dummy_205 f)),
                      ((nb057_alpha_dummy_202), (nb057_alpha_dummy_204 f)),
                      ((nb057_alpha_dummy_232), (nb057_alpha_dummy_233 f)),
                      ((nb057_alpha_dummy_206), (nb057_alpha_dummy_207 f)),
                      ((nb057_alpha_dummy_046), (nb057_alpha_dummy_049 f)),
                      ((nb057_alpha_dummy_045), (nb057_alpha_dummy_048 f)),
                      ((nb057_alpha_dummy_044), (nb057_alpha_dummy_047 f)),
                      ((nb057_alpha_dummy_050), (nb057_alpha_dummy_051 f)),
                      ((nb057_alpha_dummy_000), a), ((nb057_alpha_dummy_001), f),
                      ((nb057_alpha_dummy_002), (nb057_alpha_dummy_003 f a))]
                    (syn_cnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                  (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0222) 0))
                    (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0223 f) 0))
                    (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv
                    (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0222) 0))
                      (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0223 f) 0))
                      (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
                    [((nb057_alpha_dummy_214), (nb057_alpha_dummy_215 f)),
                      ((nb057_alpha_dummy_210), (nb057_alpha_dummy_212 f)),
                      ((nb057_alpha_dummy_211), (nb057_alpha_dummy_213 f)),
                      ((nb057_alpha_dummy_236), (nb057_alpha_dummy_237 f)),
                      ((nb057_alpha_dummy_234), (nb057_alpha_dummy_235 f)),
                      ((nb057_alpha_dummy_203), (nb057_alpha_dummy_205 f)),
                      ((nb057_alpha_dummy_202), (nb057_alpha_dummy_204 f)),
                      ((nb057_alpha_dummy_232), (nb057_alpha_dummy_233 f)),
                      ((nb057_alpha_dummy_206), (nb057_alpha_dummy_207 f)),
                      ((nb057_alpha_dummy_046), (nb057_alpha_dummy_049 f)),
                      ((nb057_alpha_dummy_045), (nb057_alpha_dummy_048 f)),
                      ((nb057_alpha_dummy_044), (nb057_alpha_dummy_047 f)),
                      ((nb057_alpha_dummy_050), (nb057_alpha_dummy_051 f)),
                      ((nb057_alpha_dummy_000), a), ((nb057_alpha_dummy_001), f),
                      ((nb057_alpha_dummy_002), (nb057_alpha_dummy_003 f a))]
                    (syn_cnnc) (by simp only [fv_syn_cnnc]))))))))))

@[expose]
noncomputable def nb057_split_alpha_0058 (f : Var) (a : Var) :
    TAlphaWff
      [((nb057_alpha_dummy_232), (nb057_alpha_dummy_233 f)),
        ((nb057_alpha_dummy_206), (nb057_alpha_dummy_207 f)),
        ((nb057_alpha_dummy_046), (nb057_alpha_dummy_049 f)),
        ((nb057_alpha_dummy_045), (nb057_alpha_dummy_048 f)),
        ((nb057_alpha_dummy_044), (nb057_alpha_dummy_047 f)),
        ((nb057_alpha_dummy_050), (nb057_alpha_dummy_051 f)),
        ((nb057_alpha_dummy_000), a), ((nb057_alpha_dummy_001), f),
        ((nb057_alpha_dummy_002), (nb057_alpha_dummy_003 f a))]
      (Wff.imp (Wff.classMem (Class.cv (nb057_alpha_dummy_232))
          (Class.cab (nb057_alpha_dummy_202)
            (syn_wrex (nb057_alpha_dummy_203) (Class.cv (nb057_alpha_dummy_045))
              (Wff.classEq (Class.cv (nb057_alpha_dummy_202))
                (syn_cun (syn_cphi (Class.cv (nb057_alpha_dummy_203))) (syn_csn (syn_c0c)))))))
        (Wff.neg (Wff.classMem (Class.cv (nb057_alpha_dummy_232))
            (Class.cab (nb057_alpha_dummy_202)
              (syn_wrex (nb057_alpha_dummy_203) (Class.cv (nb057_alpha_dummy_045))
                (Wff.classEq (Class.cv (nb057_alpha_dummy_202))
                  (syn_cun (syn_cphi (Class.cv (nb057_alpha_dummy_203)))
                    (syn_csn (syn_c0c)))))))))
      (Wff.imp (Wff.classMem (Class.cv (nb057_alpha_dummy_233 f))
          (Class.cab (nb057_alpha_dummy_204 f)
            (syn_wrex (nb057_alpha_dummy_205 f) (Class.cv (nb057_alpha_dummy_048 f))
              (Wff.classEq (Class.cv (nb057_alpha_dummy_204 f))
                (syn_cun (syn_cphi (Class.cv (nb057_alpha_dummy_205 f)))
                  (syn_csn (syn_c0c))))))) (Wff.neg
          (Wff.classMem (Class.cv (nb057_alpha_dummy_233 f))
            (Class.cab (nb057_alpha_dummy_204 f)
              (syn_wrex (nb057_alpha_dummy_205 f) (Class.cv (nb057_alpha_dummy_048 f))
                (Wff.classEq (Class.cv (nb057_alpha_dummy_204 f))
                  (syn_cun (syn_cphi (Class.cv (nb057_alpha_dummy_205 f)))
                    (syn_csn (syn_c0c))))))))) :=
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
                            (((Class.cv (nb057_alpha_dummy_001))).fv ∪
                              ((syn_ccnv (Class.cv (nb057_alpha_dummy_001)))).fv) (by decide))
                          (freshVar_injective (((Class.cv f)).fv ∪ ((syn_ccnv (Class.cv f))).fv)
                            (by decide)) (TAlphaVar.here _ _ _)))))))) (TAlphaWff.classEq
              (TAlphaClass.cv (TAlphaVar.there (freshVar_injective
                    (((Class.cv (nb057_alpha_dummy_046))).fv ∪
                      ((Class.cv (nb057_alpha_dummy_045))).fv) (by decide)) (freshVar_injective
                    (((Class.cv (nb057_alpha_dummy_049 f))).fv ∪
                      ((Class.cv (nb057_alpha_dummy_048 f))).fv) (by decide))
                  (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                        (TAlphaWff.neg (TAlphaWff.conj
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cab (TAlphaWff.ex
                                  (TAlphaWff.neg (nb057_split_alpha_0057 f a)))))
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cab (TAlphaWff.ex
                                  (TAlphaWff.neg (nb057_split_alpha_0057 f a)))))))))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                      (TAlphaClass.refl_of_closed
                        [((nb057_alpha_dummy_234), (nb057_alpha_dummy_235 f)),
                          ((nb057_alpha_dummy_203), (nb057_alpha_dummy_205 f)),
                          ((nb057_alpha_dummy_202), (nb057_alpha_dummy_204 f)),
                          ((nb057_alpha_dummy_232), (nb057_alpha_dummy_233 f)),
                          ((nb057_alpha_dummy_206), (nb057_alpha_dummy_207 f)),
                          ((nb057_alpha_dummy_046), (nb057_alpha_dummy_049 f)),
                          ((nb057_alpha_dummy_045), (nb057_alpha_dummy_048 f)),
                          ((nb057_alpha_dummy_044), (nb057_alpha_dummy_047 f)),
                          ((nb057_alpha_dummy_050), (nb057_alpha_dummy_051 f)),
                          ((nb057_alpha_dummy_000), a), ((nb057_alpha_dummy_001), f),
                          ((nb057_alpha_dummy_002), (nb057_alpha_dummy_003 f a))]
                        (syn_ccompl (syn_csn (syn_c0c)))
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
                              (((Class.cv (nb057_alpha_dummy_001))).fv ∪
                                ((syn_ccnv (Class.cv (nb057_alpha_dummy_001)))).fv) (by decide))
                            (freshVar_injective
                              (((Class.cv f)).fv ∪ ((syn_ccnv (Class.cv f))).fv) (by decide))
                            (TAlphaVar.here _ _ _)))))))) (TAlphaWff.classEq (TAlphaClass.cv
                  (TAlphaVar.there (freshVar_injective
                      (((Class.cv (nb057_alpha_dummy_046))).fv ∪
                        ((Class.cv (nb057_alpha_dummy_045))).fv) (by decide))
                    (freshVar_injective (((Class.cv (nb057_alpha_dummy_049 f))).fv ∪
                        ((Class.cv (nb057_alpha_dummy_048 f))).fv) (by decide))
                    (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cab (TAlphaWff.ex
                                    (TAlphaWff.neg (nb057_split_alpha_0057 f a)))))
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cab (TAlphaWff.ex
                                    (TAlphaWff.neg (nb057_split_alpha_0057 f a)))))))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.refl_of_closed
                          [((nb057_alpha_dummy_234), (nb057_alpha_dummy_235 f)),
                            ((nb057_alpha_dummy_203), (nb057_alpha_dummy_205 f)),
                            ((nb057_alpha_dummy_202), (nb057_alpha_dummy_204 f)),
                            ((nb057_alpha_dummy_232), (nb057_alpha_dummy_233 f)),
                            ((nb057_alpha_dummy_206), (nb057_alpha_dummy_207 f)),
                            ((nb057_alpha_dummy_046), (nb057_alpha_dummy_049 f)),
                            ((nb057_alpha_dummy_045), (nb057_alpha_dummy_048 f)),
                            ((nb057_alpha_dummy_044), (nb057_alpha_dummy_047 f)),
                            ((nb057_alpha_dummy_050), (nb057_alpha_dummy_051 f)),
                            ((nb057_alpha_dummy_000), a), ((nb057_alpha_dummy_001), f),
                            ((nb057_alpha_dummy_002), (nb057_alpha_dummy_003 f a))]
                          (syn_ccompl (syn_csn (syn_c0c))) (by
                            simp only [fv_syn_ccompl, fv_syn_csn, fv_syn_c0c])))))))))))))

@[expose]
noncomputable def nb057_direct_composition_variable_occurrence (f : Var) (a : Var)
    (dv_a_f : a ≠ f) :
    TAlphaClass
      [((nb057_alpha_dummy_046), (nb057_alpha_dummy_049 f)),
        ((nb057_alpha_dummy_045), (nb057_alpha_dummy_048 f)),
        ((nb057_alpha_dummy_044), (nb057_alpha_dummy_047 f)),
        ((nb057_alpha_dummy_050), (nb057_alpha_dummy_051 f)),
        ((nb057_alpha_dummy_000), a), ((nb057_alpha_dummy_001), f),
        ((nb057_alpha_dummy_002), (nb057_alpha_dummy_003 f a))]
      (Class.cv (nb057_alpha_dummy_001)) (Class.cv f) :=
  by
  have freshness0 : (nb057_alpha_dummy_001) ≠ (nb057_alpha_dummy_046) :=
    by
    unfold nb057_alpha_dummy_046
    with_reducible exact (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0206) 2))
  have freshness1 : f ≠ (nb057_alpha_dummy_049 f) :=
    by
    unfold nb057_alpha_dummy_049
    with_reducible exact (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0208 f) 2))
  have freshness2 : (nb057_alpha_dummy_001) ≠ (nb057_alpha_dummy_045) :=
    by
    unfold nb057_alpha_dummy_045
    with_reducible exact (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0206) 1))
  have freshness3 : f ≠ (nb057_alpha_dummy_048 f) :=
    by
    unfold nb057_alpha_dummy_048
    with_reducible exact (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0208 f) 1))
  have freshness4 : (nb057_alpha_dummy_001) ≠ (nb057_alpha_dummy_044) :=
    by
    unfold nb057_alpha_dummy_044
    with_reducible exact (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0206) 0))
  have freshness5 : f ≠ (nb057_alpha_dummy_047 f) :=
    by
    unfold nb057_alpha_dummy_047
    with_reducible exact (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0208 f) 0))
  have freshness6 : (nb057_alpha_dummy_001) ≠ (nb057_alpha_dummy_050) :=
    by
    unfold nb057_alpha_dummy_050
    with_reducible exact (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0207) 0))
  have freshness7 : f ≠ (nb057_alpha_dummy_051 f) :=
    by
    unfold nb057_alpha_dummy_051
    with_reducible exact (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0209 f) 0))
  have freshness8 : (nb057_alpha_dummy_001) ≠ (nb057_alpha_dummy_000) :=
    by
    unfold nb057_alpha_dummy_001 nb057_alpha_dummy_000
    with_reducible exact (freshVar_injective ((∅ : Finset Var)) (by decide))
  have freshness9 : f ≠ a := by exact (Ne.symm dv_a_f)
  with_reducible
    exact
      (TAlphaClass.cv (TAlphaVar.there freshness0 freshness1
          (TAlphaVar.there freshness2 freshness3 (TAlphaVar.there freshness4 freshness5
              (TAlphaVar.there freshness6 freshness7
                (TAlphaVar.there freshness8 freshness9 (TAlphaVar.here _ _ _)))))))

@[expose]
noncomputable def nb057_split_alpha_0059 (f : Var) (a : Var) (dv_a_f : a ≠ f) :
    TAlphaWff
      [((nb057_alpha_dummy_046), (nb057_alpha_dummy_049 f)),
        ((nb057_alpha_dummy_045), (nb057_alpha_dummy_048 f)),
        ((nb057_alpha_dummy_044), (nb057_alpha_dummy_047 f)),
        ((nb057_alpha_dummy_050), (nb057_alpha_dummy_051 f)),
        ((nb057_alpha_dummy_000), a), ((nb057_alpha_dummy_001), f),
        ((nb057_alpha_dummy_002), (nb057_alpha_dummy_003 f a))]
      (Wff.imp (syn_wbr (Class.cv (nb057_alpha_dummy_044))
          (syn_ccnv (Class.cv (nb057_alpha_dummy_001))) (Class.cv (nb057_alpha_dummy_046)))
        (Wff.neg (syn_wbr (Class.cv (nb057_alpha_dummy_046)) (Class.cv (nb057_alpha_dummy_001))
            (Class.cv (nb057_alpha_dummy_045)))))
      (Wff.imp (syn_wbr (Class.cv (nb057_alpha_dummy_047 f)) (syn_ccnv (Class.cv f))
          (Class.cv (nb057_alpha_dummy_049 f))) (Wff.neg
          (syn_wbr (Class.cv (nb057_alpha_dummy_049 f)) (Class.cv f)
            (Class.cv (nb057_alpha_dummy_048 f))))) :=
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
        (((Class.cv (nb057_alpha_dummy_001))).fv ∪ ((syn_ccnv
        (Class.cv (nb057_alpha_dummy_001)))).fv) (by decide)) (freshVar_injective
        (((Class.cv f)).fv ∪ ((syn_ccnv (Class.cv f))).fv) (by decide)) (TAlphaVar.there
        (freshVar_injective (((Class.cv (nb057_alpha_dummy_001))).fv ∪ ((syn_ccnv (Class.cv
        (nb057_alpha_dummy_001)))).fv) (by decide)) (freshVar_injective (((Class.cv f)).fv ∪
        ((syn_ccnv (Class.cv f))).fv) (by decide)) (TAlphaVar.here _ _ _)))))))))
                            (nb057_split_alpha_0039 f a)))))
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
        (((Class.cv (nb057_alpha_dummy_001))).fv ∪ ((syn_ccnv
        (Class.cv (nb057_alpha_dummy_001)))).fv) (by decide)) (freshVar_injective
        (((Class.cv f)).fv ∪ ((syn_ccnv (Class.cv f))).fv) (by decide)) (TAlphaVar.there
        (freshVar_injective (((Class.cv (nb057_alpha_dummy_001))).fv ∪ ((syn_ccnv (Class.cv
        (nb057_alpha_dummy_001)))).fv) (by decide)) (freshVar_injective (((Class.cv f)).fv ∪
        ((syn_ccnv (Class.cv f))).fv) (by decide)) (TAlphaVar.here _ _ _)))))))))
                            (nb057_split_alpha_0039 f a)))))))))
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.neg (TAlphaWff.neg (nb057_split_alpha_0042 f a))))))))
      (TAlphaClass.cab (TAlphaWff.ex
          (TAlphaWff.ex (TAlphaWff.neg (nb057_split_alpha_0053 f a dv_a_f)))))) (TAlphaWff.neg
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
                              (nb057_split_alpha_0055 f a)))))
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
                              (nb057_split_alpha_0055 f a)))))))))
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                  (TAlphaWff.neg (TAlphaWff.neg (nb057_split_alpha_0058 f a))))))))
        (nb057_direct_composition_variable_occurrence f a dv_a_f))))

@[expose]
noncomputable def nb057_split_alpha_0060 (f : Var) (a : Var) :
    TAlphaWff
      [((nb057_alpha_dummy_258), (nb057_alpha_dummy_261 f)),
        ((nb057_alpha_dummy_257), (nb057_alpha_dummy_260 f)),
        ((nb057_alpha_dummy_256), (nb057_alpha_dummy_259 f)),
        ((nb057_alpha_dummy_254), (nb057_alpha_dummy_255 f)),
        ((nb057_alpha_dummy_250), (nb057_alpha_dummy_252 f)),
        ((nb057_alpha_dummy_251), (nb057_alpha_dummy_253 f)),
        ((nb057_alpha_dummy_243), (nb057_alpha_dummy_245 f)),
        ((nb057_alpha_dummy_242), (nb057_alpha_dummy_244 f)),
        ((nb057_alpha_dummy_248), (nb057_alpha_dummy_249 f)),
        ((nb057_alpha_dummy_246), (nb057_alpha_dummy_247 f)),
        ((nb057_alpha_dummy_239), (nb057_alpha_dummy_241 f)),
        ((nb057_alpha_dummy_238), (nb057_alpha_dummy_240 f)),
        ((nb057_alpha_dummy_000), a), ((nb057_alpha_dummy_001), f),
        ((nb057_alpha_dummy_002), (nb057_alpha_dummy_003 f a))]
      (Wff.imp (Wff.classEq
          (syn_cin (Class.cv (nb057_alpha_dummy_257)) (Class.cv (nb057_alpha_dummy_258)))
          (syn_c0)) (Wff.neg (Wff.classEq (Class.cv (nb057_alpha_dummy_256))
            (syn_cun (Class.cv (nb057_alpha_dummy_257)) (Class.cv (nb057_alpha_dummy_258))))))
      (Wff.imp (Wff.classEq (syn_cin (Class.cv (nb057_alpha_dummy_260 f))
            (Class.cv (nb057_alpha_dummy_261 f))) (syn_c0)) (Wff.neg
          (Wff.classEq (Class.cv (nb057_alpha_dummy_259 f))
            (syn_cun (Class.cv (nb057_alpha_dummy_260 f))
              (Class.cv (nb057_alpha_dummy_261 f)))))) :=
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
                                (((Class.cv (nb057_alpha_dummy_250))).fv ∪ ((syn_c1c)).fv)
                                (by decide)) (freshVar_injective
                                (((Class.cv (nb057_alpha_dummy_252 f))).fv ∪ ((syn_c1c)).fv)
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
                                (((Class.cv (nb057_alpha_dummy_250))).fv ∪ ((syn_c1c)).fv)
                                (by decide)) (freshVar_injective
                                (((Class.cv (nb057_alpha_dummy_252 f))).fv ∪ ((syn_c1c)).fv)
                                (by decide)) (TAlphaVar.here _ _ _))))))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0270) 0))
                          (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0271 f) 0))
                          (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0268) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0269 f) 0))
                            (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.refl_of_closed
        [((nb057_alpha_dummy_258), (nb057_alpha_dummy_261 f)),
          ((nb057_alpha_dummy_257), (nb057_alpha_dummy_260 f)),
          ((nb057_alpha_dummy_256), (nb057_alpha_dummy_259 f)),
          ((nb057_alpha_dummy_254), (nb057_alpha_dummy_255 f)),
          ((nb057_alpha_dummy_250), (nb057_alpha_dummy_252 f)),
          ((nb057_alpha_dummy_251), (nb057_alpha_dummy_253 f)),
          ((nb057_alpha_dummy_243), (nb057_alpha_dummy_245 f)),
          ((nb057_alpha_dummy_242), (nb057_alpha_dummy_244 f)),
          ((nb057_alpha_dummy_248), (nb057_alpha_dummy_249 f)),
          ((nb057_alpha_dummy_246), (nb057_alpha_dummy_247 f)),
          ((nb057_alpha_dummy_239), (nb057_alpha_dummy_241 f)),
          ((nb057_alpha_dummy_238), (nb057_alpha_dummy_240 f)),
          ((nb057_alpha_dummy_000), a), ((nb057_alpha_dummy_001), f),
          ((nb057_alpha_dummy_002), (nb057_alpha_dummy_003 f a))]
        (syn_c0) (by simp only [fv_syn_c0]))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv
          (TAlphaVar.there
            (freshVar_injective (((Class.cv (nb057_alpha_dummy_250))).fv ∪ ((syn_c1c)).fv)
              (by decide)) (freshVar_injective
              (((Class.cv (nb057_alpha_dummy_252 f))).fv ∪ ((syn_c1c)).fv) (by decide))
            (TAlphaVar.there (freshVar_injective
                (((Class.cv (nb057_alpha_dummy_250))).fv ∪ ((syn_c1c)).fv) (by decide))
              (freshVar_injective
                (((Class.cv (nb057_alpha_dummy_252 f))).fv ∪ ((syn_c1c)).fv) (by decide))
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
                                  (((Class.cv (nb057_alpha_dummy_250))).fv ∪ ((syn_c1c)).fv)
                                  (by decide)) (freshVar_injective
                                  (((Class.cv (nb057_alpha_dummy_252 f))).fv ∪ ((syn_c1c)).fv)
                                  (by decide)) (TAlphaVar.here _ _ _))))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0274) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0275 f) 0))
                            (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0272) 0))
                              (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0273 f) 0))
                              (TAlphaVar.there (freshVar_injective
                                  (((Class.cv (nb057_alpha_dummy_250))).fv ∪ ((syn_c1c)).fv)
                                  (by decide)) (freshVar_injective
                                  (((Class.cv (nb057_alpha_dummy_252 f))).fv ∪ ((syn_c1c)).fv)
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

@[expose]
noncomputable def nb057_split_alpha_0061 (f : Var) (a : Var) :
    TAlphaWff
      [((nb057_alpha_dummy_243), (nb057_alpha_dummy_245 f)),
        ((nb057_alpha_dummy_242), (nb057_alpha_dummy_244 f)),
        ((nb057_alpha_dummy_248), (nb057_alpha_dummy_249 f)),
        ((nb057_alpha_dummy_246), (nb057_alpha_dummy_247 f)),
        ((nb057_alpha_dummy_239), (nb057_alpha_dummy_241 f)),
        ((nb057_alpha_dummy_238), (nb057_alpha_dummy_240 f)),
        ((nb057_alpha_dummy_000), a), ((nb057_alpha_dummy_001), f),
        ((nb057_alpha_dummy_002), (nb057_alpha_dummy_003 f a))]
      (Wff.imp (Wff.classMem (Class.cv (nb057_alpha_dummy_243))
          (Class.cv (nb057_alpha_dummy_239))) (Wff.neg
          (Wff.classEq (Class.cv (nb057_alpha_dummy_242))
            (syn_cphi (Class.cv (nb057_alpha_dummy_243))))))
      (Wff.imp (Wff.classMem (Class.cv (nb057_alpha_dummy_245 f))
          (Class.cv (nb057_alpha_dummy_241 f))) (Wff.neg
          (Wff.classEq (Class.cv (nb057_alpha_dummy_244 f))
            (syn_cphi (Class.cv (nb057_alpha_dummy_245 f)))))) :=
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
          (TAlphaVar.there (freshVar_injective (((Class.cv (nb057_alpha_dummy_239))).fv ∪
                ((Class.cv (nb057_alpha_dummy_238))).fv) (by decide)) (freshVar_injective
              (((Class.cv (nb057_alpha_dummy_241 f))).fv ∪
                ((Class.cv (nb057_alpha_dummy_240 f))).fv) (by decide)) (TAlphaVar.here _ _ _)))
        (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                  (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0258) 0))
                    (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0259 f) 0))
                    (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0258) 1))
                      (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0259 f) 1))
                      (TAlphaVar.here _ _ _))))) (TAlphaWff.classEq (TAlphaClass.cv
                  (TAlphaVar.there (freshVar_injective (((Class.cv (nb057_alpha_dummy_243))).fv)
                      (by decide))
                    (freshVar_injective (((Class.cv (nb057_alpha_dummy_245 f))).fv) (by decide))
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
                                      (TAlphaClass.refl_of_closed [((nb057_alpha_dummy_258),
        (nb057_alpha_dummy_261 f)), ((nb057_alpha_dummy_257), (nb057_alpha_dummy_260 f)),
        ((nb057_alpha_dummy_256), (nb057_alpha_dummy_259 f)), ((nb057_alpha_dummy_254),
        (nb057_alpha_dummy_255 f)), ((nb057_alpha_dummy_250), (nb057_alpha_dummy_252 f)),
        ((nb057_alpha_dummy_251), (nb057_alpha_dummy_253 f)), ((nb057_alpha_dummy_243),
        (nb057_alpha_dummy_245 f)), ((nb057_alpha_dummy_242), (nb057_alpha_dummy_244 f)),
        ((nb057_alpha_dummy_248), (nb057_alpha_dummy_249 f)), ((nb057_alpha_dummy_246),
        (nb057_alpha_dummy_247 f)), ((nb057_alpha_dummy_239), (nb057_alpha_dummy_241 f)),
        ((nb057_alpha_dummy_238), (nb057_alpha_dummy_240 f)), ((nb057_alpha_dummy_000), a),
        ((nb057_alpha_dummy_001), f), ((nb057_alpha_dummy_002), (nb057_alpha_dummy_003 f a))]
                                        (syn_c1c) (by simp only [fv_syn_c1c])))
                                    (TAlphaWff.neg (nb057_split_alpha_0060 f a))))))))
                        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0260) 0))
                              (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0261 f) 0))
                              (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
                            [((nb057_alpha_dummy_254), (nb057_alpha_dummy_255 f)),
                              ((nb057_alpha_dummy_250), (nb057_alpha_dummy_252 f)),
                              ((nb057_alpha_dummy_251), (nb057_alpha_dummy_253 f)),
                              ((nb057_alpha_dummy_243), (nb057_alpha_dummy_245 f)),
                              ((nb057_alpha_dummy_242), (nb057_alpha_dummy_244 f)),
                              ((nb057_alpha_dummy_248), (nb057_alpha_dummy_249 f)),
                              ((nb057_alpha_dummy_246), (nb057_alpha_dummy_247 f)),
                              ((nb057_alpha_dummy_239), (nb057_alpha_dummy_241 f)),
                              ((nb057_alpha_dummy_238), (nb057_alpha_dummy_240 f)),
                              ((nb057_alpha_dummy_000), a), ((nb057_alpha_dummy_001), f),
                              ((nb057_alpha_dummy_002), (nb057_alpha_dummy_003 f a))]
                            (syn_cnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0260) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0261 f) 0))
                            (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.classMem
                          (TAlphaClass.cv (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0260) 0))
                              (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0261 f) 0))
                              (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
                            [((nb057_alpha_dummy_254), (nb057_alpha_dummy_255 f)),
                              ((nb057_alpha_dummy_250), (nb057_alpha_dummy_252 f)),
                              ((nb057_alpha_dummy_251), (nb057_alpha_dummy_253 f)),
                              ((nb057_alpha_dummy_243), (nb057_alpha_dummy_245 f)),
                              ((nb057_alpha_dummy_242), (nb057_alpha_dummy_244 f)),
                              ((nb057_alpha_dummy_248), (nb057_alpha_dummy_249 f)),
                              ((nb057_alpha_dummy_246), (nb057_alpha_dummy_247 f)),
                              ((nb057_alpha_dummy_239), (nb057_alpha_dummy_241 f)),
                              ((nb057_alpha_dummy_238), (nb057_alpha_dummy_240 f)),
                              ((nb057_alpha_dummy_000), a), ((nb057_alpha_dummy_001), f),
                              ((nb057_alpha_dummy_002), (nb057_alpha_dummy_003 f a))]
                            (syn_cnnc) (by simp only [fv_syn_cnnc]))))))))))))))

@[expose]
noncomputable def nb057_split_alpha_0062 (f : Var) (a : Var) :
    TAlphaWff
      [((nb057_alpha_dummy_258), (nb057_alpha_dummy_261 f)),
        ((nb057_alpha_dummy_257), (nb057_alpha_dummy_260 f)),
        ((nb057_alpha_dummy_256), (nb057_alpha_dummy_259 f)),
        ((nb057_alpha_dummy_254), (nb057_alpha_dummy_255 f)),
        ((nb057_alpha_dummy_250), (nb057_alpha_dummy_252 f)),
        ((nb057_alpha_dummy_251), (nb057_alpha_dummy_253 f)),
        ((nb057_alpha_dummy_276), (nb057_alpha_dummy_277 f)),
        ((nb057_alpha_dummy_274), (nb057_alpha_dummy_275 f)),
        ((nb057_alpha_dummy_243), (nb057_alpha_dummy_245 f)),
        ((nb057_alpha_dummy_242), (nb057_alpha_dummy_244 f)),
        ((nb057_alpha_dummy_272), (nb057_alpha_dummy_273 f)),
        ((nb057_alpha_dummy_246), (nb057_alpha_dummy_247 f)),
        ((nb057_alpha_dummy_239), (nb057_alpha_dummy_241 f)),
        ((nb057_alpha_dummy_238), (nb057_alpha_dummy_240 f)),
        ((nb057_alpha_dummy_000), a), ((nb057_alpha_dummy_001), f),
        ((nb057_alpha_dummy_002), (nb057_alpha_dummy_003 f a))]
      (Wff.imp (Wff.classEq
          (syn_cin (Class.cv (nb057_alpha_dummy_257)) (Class.cv (nb057_alpha_dummy_258)))
          (syn_c0)) (Wff.neg (Wff.classEq (Class.cv (nb057_alpha_dummy_256))
            (syn_cun (Class.cv (nb057_alpha_dummy_257)) (Class.cv (nb057_alpha_dummy_258))))))
      (Wff.imp (Wff.classEq (syn_cin (Class.cv (nb057_alpha_dummy_260 f))
            (Class.cv (nb057_alpha_dummy_261 f))) (syn_c0)) (Wff.neg
          (Wff.classEq (Class.cv (nb057_alpha_dummy_259 f))
            (syn_cun (Class.cv (nb057_alpha_dummy_260 f))
              (Class.cv (nb057_alpha_dummy_261 f)))))) :=
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
                                (((Class.cv (nb057_alpha_dummy_250))).fv ∪ ((syn_c1c)).fv)
                                (by decide)) (freshVar_injective
                                (((Class.cv (nb057_alpha_dummy_252 f))).fv ∪ ((syn_c1c)).fv)
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
                                (((Class.cv (nb057_alpha_dummy_250))).fv ∪ ((syn_c1c)).fv)
                                (by decide)) (freshVar_injective
                                (((Class.cv (nb057_alpha_dummy_252 f))).fv ∪ ((syn_c1c)).fv)
                                (by decide)) (TAlphaVar.here _ _ _))))))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0270) 0))
                          (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0271 f) 0))
                          (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0268) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0269 f) 0))
                            (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.refl_of_closed
        [((nb057_alpha_dummy_258), (nb057_alpha_dummy_261 f)),
          ((nb057_alpha_dummy_257), (nb057_alpha_dummy_260 f)),
          ((nb057_alpha_dummy_256), (nb057_alpha_dummy_259 f)),
          ((nb057_alpha_dummy_254), (nb057_alpha_dummy_255 f)),
          ((nb057_alpha_dummy_250), (nb057_alpha_dummy_252 f)),
          ((nb057_alpha_dummy_251), (nb057_alpha_dummy_253 f)),
          ((nb057_alpha_dummy_276), (nb057_alpha_dummy_277 f)),
          ((nb057_alpha_dummy_274), (nb057_alpha_dummy_275 f)),
          ((nb057_alpha_dummy_243), (nb057_alpha_dummy_245 f)),
          ((nb057_alpha_dummy_242), (nb057_alpha_dummy_244 f)),
          ((nb057_alpha_dummy_272), (nb057_alpha_dummy_273 f)),
          ((nb057_alpha_dummy_246), (nb057_alpha_dummy_247 f)),
          ((nb057_alpha_dummy_239), (nb057_alpha_dummy_241 f)),
          ((nb057_alpha_dummy_238), (nb057_alpha_dummy_240 f)),
          ((nb057_alpha_dummy_000), a), ((nb057_alpha_dummy_001), f),
          ((nb057_alpha_dummy_002), (nb057_alpha_dummy_003 f a))]
        (syn_c0) (by simp only [fv_syn_c0]))) (TAlphaWff.neg (TAlphaWff.classEq (TAlphaClass.cv
          (TAlphaVar.there
            (freshVar_injective (((Class.cv (nb057_alpha_dummy_250))).fv ∪ ((syn_c1c)).fv)
              (by decide)) (freshVar_injective
              (((Class.cv (nb057_alpha_dummy_252 f))).fv ∪ ((syn_c1c)).fv) (by decide))
            (TAlphaVar.there (freshVar_injective
                (((Class.cv (nb057_alpha_dummy_250))).fv ∪ ((syn_c1c)).fv) (by decide))
              (freshVar_injective
                (((Class.cv (nb057_alpha_dummy_252 f))).fv ∪ ((syn_c1c)).fv) (by decide))
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
                                  (((Class.cv (nb057_alpha_dummy_250))).fv ∪ ((syn_c1c)).fv)
                                  (by decide)) (freshVar_injective
                                  (((Class.cv (nb057_alpha_dummy_252 f))).fv ∪ ((syn_c1c)).fv)
                                  (by decide)) (TAlphaVar.here _ _ _))))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0274) 0))
                            (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0275 f) 0))
                            (TAlphaVar.there
                              (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0272) 0))
                              (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0273 f) 0))
                              (TAlphaVar.there (freshVar_injective
                                  (((Class.cv (nb057_alpha_dummy_250))).fv ∪ ((syn_c1c)).fv)
                                  (by decide)) (freshVar_injective
                                  (((Class.cv (nb057_alpha_dummy_252 f))).fv ∪ ((syn_c1c)).fv)
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

@[expose]
noncomputable def nb057_split_alpha_0063 (f : Var) (a : Var) :
    TAlphaWff
      [((nb057_alpha_dummy_250), (nb057_alpha_dummy_252 f)),
        ((nb057_alpha_dummy_251), (nb057_alpha_dummy_253 f)),
        ((nb057_alpha_dummy_276), (nb057_alpha_dummy_277 f)),
        ((nb057_alpha_dummy_274), (nb057_alpha_dummy_275 f)),
        ((nb057_alpha_dummy_243), (nb057_alpha_dummy_245 f)),
        ((nb057_alpha_dummy_242), (nb057_alpha_dummy_244 f)),
        ((nb057_alpha_dummy_272), (nb057_alpha_dummy_273 f)),
        ((nb057_alpha_dummy_246), (nb057_alpha_dummy_247 f)),
        ((nb057_alpha_dummy_239), (nb057_alpha_dummy_241 f)),
        ((nb057_alpha_dummy_238), (nb057_alpha_dummy_240 f)),
        ((nb057_alpha_dummy_000), a), ((nb057_alpha_dummy_001), f),
        ((nb057_alpha_dummy_002), (nb057_alpha_dummy_003 f a))]
      (Wff.imp (Wff.classMem (Class.cv (nb057_alpha_dummy_250))
          (Class.cv (nb057_alpha_dummy_243))) (Wff.neg
          (Wff.classEq (Class.cv (nb057_alpha_dummy_251))
            (syn_cif (Wff.classMem (Class.cv (nb057_alpha_dummy_250)) (syn_cnnc))
              (syn_cplc (Class.cv (nb057_alpha_dummy_250)) (syn_c1c))
              (Class.cv (nb057_alpha_dummy_250))))))
      (Wff.imp (Wff.classMem (Class.cv (nb057_alpha_dummy_252 f))
          (Class.cv (nb057_alpha_dummy_245 f))) (Wff.neg
          (Wff.classEq (Class.cv (nb057_alpha_dummy_253 f))
            (syn_cif (Wff.classMem (Class.cv (nb057_alpha_dummy_252 f)) (syn_cnnc))
              (syn_cplc (Class.cv (nb057_alpha_dummy_252 f)) (syn_c1c))
              (Class.cv (nb057_alpha_dummy_252 f)))))) :=
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
            (freshVar_injective (((Class.cv (nb057_alpha_dummy_243))).fv) (by decide))
            (freshVar_injective (((Class.cv (nb057_alpha_dummy_245 f))).fv) (by decide))
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
                              (TAlphaClass.refl_of_closed
                                [((nb057_alpha_dummy_258), (nb057_alpha_dummy_261 f)),
                                  ((nb057_alpha_dummy_257), (nb057_alpha_dummy_260 f)),
                                  ((nb057_alpha_dummy_256), (nb057_alpha_dummy_259 f)),
                                  ((nb057_alpha_dummy_254), (nb057_alpha_dummy_255 f)),
                                  ((nb057_alpha_dummy_250), (nb057_alpha_dummy_252 f)),
                                  ((nb057_alpha_dummy_251), (nb057_alpha_dummy_253 f)),
                                  ((nb057_alpha_dummy_276), (nb057_alpha_dummy_277 f)),
                                  ((nb057_alpha_dummy_274), (nb057_alpha_dummy_275 f)),
                                  ((nb057_alpha_dummy_243), (nb057_alpha_dummy_245 f)),
                                  ((nb057_alpha_dummy_242), (nb057_alpha_dummy_244 f)),
                                  ((nb057_alpha_dummy_272), (nb057_alpha_dummy_273 f)),
                                  ((nb057_alpha_dummy_246), (nb057_alpha_dummy_247 f)),
                                  ((nb057_alpha_dummy_239), (nb057_alpha_dummy_241 f)),
                                  ((nb057_alpha_dummy_238), (nb057_alpha_dummy_240 f)),
                                  ((nb057_alpha_dummy_000), a), ((nb057_alpha_dummy_001), f),
                                  ((nb057_alpha_dummy_002), (nb057_alpha_dummy_003 f a))]
                                (syn_c1c) (by simp only [fv_syn_c1c])))
                            (TAlphaWff.neg (nb057_split_alpha_0062 f a))))))))
                (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there
                      (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0260) 0))
                      (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0261 f) 0))
                      (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
                    [((nb057_alpha_dummy_254), (nb057_alpha_dummy_255 f)),
                      ((nb057_alpha_dummy_250), (nb057_alpha_dummy_252 f)),
                      ((nb057_alpha_dummy_251), (nb057_alpha_dummy_253 f)),
                      ((nb057_alpha_dummy_276), (nb057_alpha_dummy_277 f)),
                      ((nb057_alpha_dummy_274), (nb057_alpha_dummy_275 f)),
                      ((nb057_alpha_dummy_243), (nb057_alpha_dummy_245 f)),
                      ((nb057_alpha_dummy_242), (nb057_alpha_dummy_244 f)),
                      ((nb057_alpha_dummy_272), (nb057_alpha_dummy_273 f)),
                      ((nb057_alpha_dummy_246), (nb057_alpha_dummy_247 f)),
                      ((nb057_alpha_dummy_239), (nb057_alpha_dummy_241 f)),
                      ((nb057_alpha_dummy_238), (nb057_alpha_dummy_240 f)),
                      ((nb057_alpha_dummy_000), a), ((nb057_alpha_dummy_001), f),
                      ((nb057_alpha_dummy_002), (nb057_alpha_dummy_003 f a))]
                    (syn_cnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                  (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0260) 0))
                    (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0261 f) 0))
                    (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv
                    (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0260) 0))
                      (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0261 f) 0))
                      (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
                    [((nb057_alpha_dummy_254), (nb057_alpha_dummy_255 f)),
                      ((nb057_alpha_dummy_250), (nb057_alpha_dummy_252 f)),
                      ((nb057_alpha_dummy_251), (nb057_alpha_dummy_253 f)),
                      ((nb057_alpha_dummy_276), (nb057_alpha_dummy_277 f)),
                      ((nb057_alpha_dummy_274), (nb057_alpha_dummy_275 f)),
                      ((nb057_alpha_dummy_243), (nb057_alpha_dummy_245 f)),
                      ((nb057_alpha_dummy_242), (nb057_alpha_dummy_244 f)),
                      ((nb057_alpha_dummy_272), (nb057_alpha_dummy_273 f)),
                      ((nb057_alpha_dummy_246), (nb057_alpha_dummy_247 f)),
                      ((nb057_alpha_dummy_239), (nb057_alpha_dummy_241 f)),
                      ((nb057_alpha_dummy_238), (nb057_alpha_dummy_240 f)),
                      ((nb057_alpha_dummy_000), a), ((nb057_alpha_dummy_001), f),
                      ((nb057_alpha_dummy_002), (nb057_alpha_dummy_003 f a))]
                    (syn_cnnc) (by simp only [fv_syn_cnnc]))))))))))

@[expose]
noncomputable def nb057_split_alpha_0064 (f : Var) (a : Var) :
    TAlphaWff
      [((nb057_alpha_dummy_272), (nb057_alpha_dummy_273 f)),
        ((nb057_alpha_dummy_246), (nb057_alpha_dummy_247 f)),
        ((nb057_alpha_dummy_239), (nb057_alpha_dummy_241 f)),
        ((nb057_alpha_dummy_238), (nb057_alpha_dummy_240 f)),
        ((nb057_alpha_dummy_000), a), ((nb057_alpha_dummy_001), f),
        ((nb057_alpha_dummy_002), (nb057_alpha_dummy_003 f a))]
      (Wff.imp (Wff.classMem (Class.cv (nb057_alpha_dummy_272))
          (Class.cab (nb057_alpha_dummy_242)
            (syn_wrex (nb057_alpha_dummy_243) (Class.cv (nb057_alpha_dummy_238))
              (Wff.classEq (Class.cv (nb057_alpha_dummy_242))
                (syn_cun (syn_cphi (Class.cv (nb057_alpha_dummy_243))) (syn_csn (syn_c0c)))))))
        (Wff.neg (Wff.classMem (Class.cv (nb057_alpha_dummy_272))
            (Class.cab (nb057_alpha_dummy_242)
              (syn_wrex (nb057_alpha_dummy_243) (Class.cv (nb057_alpha_dummy_238))
                (Wff.classEq (Class.cv (nb057_alpha_dummy_242))
                  (syn_cun (syn_cphi (Class.cv (nb057_alpha_dummy_243)))
                    (syn_csn (syn_c0c)))))))))
      (Wff.imp (Wff.classMem (Class.cv (nb057_alpha_dummy_273 f))
          (Class.cab (nb057_alpha_dummy_244 f)
            (syn_wrex (nb057_alpha_dummy_245 f) (Class.cv (nb057_alpha_dummy_240 f))
              (Wff.classEq (Class.cv (nb057_alpha_dummy_244 f))
                (syn_cun (syn_cphi (Class.cv (nb057_alpha_dummy_245 f)))
                  (syn_csn (syn_c0c))))))) (Wff.neg
          (Wff.classMem (Class.cv (nb057_alpha_dummy_273 f))
            (Class.cab (nb057_alpha_dummy_244 f)
              (syn_wrex (nb057_alpha_dummy_245 f) (Class.cv (nb057_alpha_dummy_240 f))
                (Wff.classEq (Class.cv (nb057_alpha_dummy_244 f))
                  (syn_cun (syn_cphi (Class.cv (nb057_alpha_dummy_245 f)))
                    (syn_csn (syn_c0c))))))))) :=
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
                            (((syn_ccnv (Class.cv (nb057_alpha_dummy_001)))).fv ∪
                              ((syn_cvv)).fv) (by decide)) (freshVar_injective
                            (((syn_ccnv (Class.cv f))).fv ∪ ((syn_cvv)).fv) (by decide))
                          (TAlphaVar.here _ _ _)))))))) (TAlphaWff.classEq (TAlphaClass.cv
                (TAlphaVar.there (freshVar_injective (((Class.cv (nb057_alpha_dummy_239))).fv ∪
                      ((Class.cv (nb057_alpha_dummy_238))).fv) (by decide)) (freshVar_injective
                    (((Class.cv (nb057_alpha_dummy_241 f))).fv ∪
                      ((Class.cv (nb057_alpha_dummy_240 f))).fv) (by decide))
                  (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                        (TAlphaWff.neg (TAlphaWff.conj
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cab (TAlphaWff.ex
                                  (TAlphaWff.neg (nb057_split_alpha_0063 f a)))))
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cab (TAlphaWff.ex
                                  (TAlphaWff.neg (nb057_split_alpha_0063 f a)))))))))
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                      (TAlphaClass.refl_of_closed
                        [((nb057_alpha_dummy_274), (nb057_alpha_dummy_275 f)),
                          ((nb057_alpha_dummy_243), (nb057_alpha_dummy_245 f)),
                          ((nb057_alpha_dummy_242), (nb057_alpha_dummy_244 f)),
                          ((nb057_alpha_dummy_272), (nb057_alpha_dummy_273 f)),
                          ((nb057_alpha_dummy_246), (nb057_alpha_dummy_247 f)),
                          ((nb057_alpha_dummy_239), (nb057_alpha_dummy_241 f)),
                          ((nb057_alpha_dummy_238), (nb057_alpha_dummy_240 f)),
                          ((nb057_alpha_dummy_000), a), ((nb057_alpha_dummy_001), f),
                          ((nb057_alpha_dummy_002), (nb057_alpha_dummy_003 f a))]
                        (syn_ccompl (syn_csn (syn_c0c)))
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
                              (((syn_ccnv (Class.cv (nb057_alpha_dummy_001)))).fv ∪
                                ((syn_cvv)).fv) (by decide)) (freshVar_injective
                              (((syn_ccnv (Class.cv f))).fv ∪ ((syn_cvv)).fv) (by decide))
                            (TAlphaVar.here _ _ _)))))))) (TAlphaWff.classEq (TAlphaClass.cv
                  (TAlphaVar.there (freshVar_injective
                      (((Class.cv (nb057_alpha_dummy_239))).fv ∪
                        ((Class.cv (nb057_alpha_dummy_238))).fv) (by decide))
                    (freshVar_injective (((Class.cv (nb057_alpha_dummy_241 f))).fv ∪
                        ((Class.cv (nb057_alpha_dummy_240 f))).fv) (by decide))
                    (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cab (TAlphaWff.ex
                                    (TAlphaWff.neg (nb057_split_alpha_0063 f a)))))
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cab (TAlphaWff.ex
                                    (TAlphaWff.neg (nb057_split_alpha_0063 f a)))))))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.refl_of_closed
                          [((nb057_alpha_dummy_274), (nb057_alpha_dummy_275 f)),
                            ((nb057_alpha_dummy_243), (nb057_alpha_dummy_245 f)),
                            ((nb057_alpha_dummy_242), (nb057_alpha_dummy_244 f)),
                            ((nb057_alpha_dummy_272), (nb057_alpha_dummy_273 f)),
                            ((nb057_alpha_dummy_246), (nb057_alpha_dummy_247 f)),
                            ((nb057_alpha_dummy_239), (nb057_alpha_dummy_241 f)),
                            ((nb057_alpha_dummy_238), (nb057_alpha_dummy_240 f)),
                            ((nb057_alpha_dummy_000), a), ((nb057_alpha_dummy_001), f),
                            ((nb057_alpha_dummy_002), (nb057_alpha_dummy_003 f a))]
                          (syn_ccompl (syn_csn (syn_c0c))) (by
                            simp only [fv_syn_ccompl, fv_syn_csn, fv_syn_c0c])))))))))))))


end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired

end
