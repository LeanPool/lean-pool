/-
Copyright (c) 2026 Elliot Glazer and NFNotWPP contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elliot Glazer and NFNotWPP contributors
-/

module

public import LeanPool.NFWeakPartition.Certificates.NAR4C057C001Block002

/-! NF weak partition development: NAR4C057C001Part007. -/


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

theorem nb057_support_mem_0246 :
    (nb057AlphaDummy045) ∈
      (((Class.cab (nb057AlphaDummy202)
            (synWrex (nb057AlphaDummy203) (Class.cv (nb057AlphaDummy045))
              (Wff.classEq (Class.cv (nb057AlphaDummy202))
                (synCun (synCphi (Class.cv (nb057AlphaDummy203)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb057AlphaDummy202)
            (synWrex (nb057AlphaDummy203) (Class.cv (nb057AlphaDummy045))
              (Wff.classEq (Class.cv (nb057AlphaDummy202))
                (synCun (synCphi (Class.cv (nb057AlphaDummy203)))
                  (synCsn (synC0c))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0242) 0))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0242) 1))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb057_support_mem_0247 (f : Var) :
    (nb057AlphaDummy048 f) ∈
      (((Class.cab (nb057AlphaDummy204 f)
            (synWrex (nb057AlphaDummy205 f) (Class.cv (nb057AlphaDummy048 f))
              (Wff.classEq (Class.cv (nb057AlphaDummy204 f))
                (synCun (synCphi (Class.cv (nb057AlphaDummy205 f)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb057AlphaDummy204 f)
            (synWrex (nb057AlphaDummy205 f) (Class.cv (nb057AlphaDummy048 f))
              (Wff.classEq (Class.cv (nb057AlphaDummy204 f))
                (synCun (synCphi (Class.cv (nb057AlphaDummy205 f)))
                  (synCsn (synC0c))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0244 f) 0))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0244 f) 1))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb057_support_mem_0248 :
    (nb057AlphaDummy203) ∈
      (((synCcompl (synCphi (Class.cv (nb057AlphaDummy203))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb057_support_mem_0249 (f : Var) :
    (nb057AlphaDummy205 f) ∈
      (((synCcompl (synCphi (Class.cv (nb057AlphaDummy205 f))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb057_support_mem_0250 :
    (nb057AlphaDummy203) ∈
      (((synCphi (Class.cv (nb057AlphaDummy203)))).fv ∪
        ((synCphi (Class.cv (nb057AlphaDummy203)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb057_support_mem_0251 (f : Var) :
    (nb057AlphaDummy205 f) ∈
      (((synCphi (Class.cv (nb057AlphaDummy205 f)))).fv ∪
        ((synCphi (Class.cv (nb057AlphaDummy205 f)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb057_support_mem_0252 :
    (nb057AlphaDummy239) ∈
      (((Class.cv (nb057AlphaDummy239))).fv ∪ ((Class.cv (nb057AlphaDummy238))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb057_support_mem_0253 :
    (nb057AlphaDummy239) ∈
      (((synCcompl (Class.cab (nb057AlphaDummy242)
              (synWrex (nb057AlphaDummy243) (Class.cv (nb057AlphaDummy239))
                (Wff.classEq (Class.cv (nb057AlphaDummy242))
                  (synCphi (Class.cv (nb057AlphaDummy243)))))))).fv ∪ ((synCcompl
            (Class.cab (nb057AlphaDummy242)
              (synWrex (nb057AlphaDummy243) (Class.cv (nb057AlphaDummy238))
                (Wff.classEq (Class.cv (nb057AlphaDummy242))
                  (synCun (synCphi (Class.cv (nb057AlphaDummy243)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0252) 0))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0252) 1))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb057_support_mem_0254 (f : Var) :
    (nb057AlphaDummy241 f) ∈
      (((Class.cv (nb057AlphaDummy241 f))).fv ∪ ((Class.cv (nb057AlphaDummy240 f))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb057_support_mem_0255 (f : Var) :
    (nb057AlphaDummy241 f) ∈
      (((synCcompl (Class.cab (nb057AlphaDummy244 f)
              (synWrex (nb057AlphaDummy245 f) (Class.cv (nb057AlphaDummy241 f))
                (Wff.classEq (Class.cv (nb057AlphaDummy244 f))
                  (synCphi (Class.cv (nb057AlphaDummy245 f)))))))).fv ∪ ((synCcompl
            (Class.cab (nb057AlphaDummy244 f)
              (synWrex (nb057AlphaDummy245 f) (Class.cv (nb057AlphaDummy240 f))
                (Wff.classEq (Class.cv (nb057AlphaDummy244 f))
                  (synCun (synCphi (Class.cv (nb057AlphaDummy245 f)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0254 f) 0))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0254 f) 1))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb057_support_mem_0256 :
    (nb057AlphaDummy239) ∈
      (((Class.cab (nb057AlphaDummy242)
            (synWrex (nb057AlphaDummy243) (Class.cv (nb057AlphaDummy239))
              (Wff.classEq (Class.cv (nb057AlphaDummy242))
                (synCphi (Class.cv (nb057AlphaDummy243))))))).fv ∪
        ((Class.cab (nb057AlphaDummy242)
            (synWrex (nb057AlphaDummy243) (Class.cv (nb057AlphaDummy239))
              (Wff.classEq (Class.cv (nb057AlphaDummy242))
                (synCphi (Class.cv (nb057AlphaDummy243))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0252) 0))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0252) 1))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb057_support_mem_0257 (f : Var) :
    (nb057AlphaDummy241 f) ∈
      (((Class.cab (nb057AlphaDummy244 f)
            (synWrex (nb057AlphaDummy245 f) (Class.cv (nb057AlphaDummy241 f))
              (Wff.classEq (Class.cv (nb057AlphaDummy244 f))
                (synCphi (Class.cv (nb057AlphaDummy245 f))))))).fv ∪
        ((Class.cab (nb057AlphaDummy244 f)
            (synWrex (nb057AlphaDummy245 f) (Class.cv (nb057AlphaDummy241 f))
              (Wff.classEq (Class.cv (nb057AlphaDummy244 f))
                (synCphi (Class.cv (nb057AlphaDummy245 f))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0254 f) 0))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0254 f) 1))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb057_support_mem_0258 :
    (nb057AlphaDummy243) ∈ (((Class.cv (nb057AlphaDummy243))).fv) :=
  by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb057_support_mem_0259 (f : Var) :
    (nb057AlphaDummy245 f) ∈ (((Class.cv (nb057AlphaDummy245 f))).fv) :=
  by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb057_support_mem_0260 :
    (nb057AlphaDummy250) ∈
      (((Wff.classMem (Class.cv (nb057AlphaDummy250)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb057AlphaDummy250)) (synC1c))).fv ∪
        ((Class.cv (nb057AlphaDummy250))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_wff_classMem]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb057_support_mem_0261 (f : Var) :
    (nb057AlphaDummy252 f) ∈
      (((Wff.classMem (Class.cv (nb057AlphaDummy252 f)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb057AlphaDummy252 f)) (synC1c))).fv ∪
        ((Class.cv (nb057AlphaDummy252 f))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_wff_classMem]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb057_support_mem_0262 :
    (nb057AlphaDummy250) ∈
      (((Class.cv (nb057AlphaDummy250))).fv ∪ ((synC1c)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb057_support_mem_0263 (f : Var) :
    (nb057AlphaDummy252 f) ∈
      (((Class.cv (nb057AlphaDummy252 f))).fv ∪ ((synC1c)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb057_support_mem_0264 :
    (nb057AlphaDummy257) ∈
      (((synCnin (Class.cv (nb057AlphaDummy257)) (Class.cv (nb057AlphaDummy258)))).fv ∪
        ((synCnin (Class.cv (nb057AlphaDummy257))
            (Class.cv (nb057AlphaDummy258)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb057_support_mem_0265 (f : Var) :
    (nb057AlphaDummy260 f) ∈
      (((synCnin (Class.cv (nb057AlphaDummy260 f))
            (Class.cv (nb057AlphaDummy261 f)))).fv ∪
        ((synCnin (Class.cv (nb057AlphaDummy260 f))
            (Class.cv (nb057AlphaDummy261 f)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb057_support_mem_0266 :
    (nb057AlphaDummy257) ∈
      (((Class.cv (nb057AlphaDummy257))).fv ∪ ((Class.cv (nb057AlphaDummy258))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb057_support_mem_0267 (f : Var) :
    (nb057AlphaDummy260 f) ∈
      (((Class.cv (nb057AlphaDummy260 f))).fv ∪ ((Class.cv (nb057AlphaDummy261 f))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb057_support_mem_0268 :
    (nb057AlphaDummy258) ∈
      (((synCnin (Class.cv (nb057AlphaDummy257)) (Class.cv (nb057AlphaDummy258)))).fv ∪
        ((synCnin (Class.cv (nb057AlphaDummy257))
            (Class.cv (nb057AlphaDummy258)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb057_support_mem_0269 (f : Var) :
    (nb057AlphaDummy261 f) ∈
      (((synCnin (Class.cv (nb057AlphaDummy260 f))
            (Class.cv (nb057AlphaDummy261 f)))).fv ∪
        ((synCnin (Class.cv (nb057AlphaDummy260 f))
            (Class.cv (nb057AlphaDummy261 f)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb057_support_mem_0270 :
    (nb057AlphaDummy258) ∈
      (((Class.cv (nb057AlphaDummy257))).fv ∪ ((Class.cv (nb057AlphaDummy258))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb057_support_mem_0271 (f : Var) :
    (nb057AlphaDummy261 f) ∈
      (((Class.cv (nb057AlphaDummy260 f))).fv ∪ ((Class.cv (nb057AlphaDummy261 f))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb057_support_mem_0272 :
    (nb057AlphaDummy257) ∈
      (((synCcompl (Class.cv (nb057AlphaDummy257)))).fv ∪
        ((synCcompl (Class.cv (nb057AlphaDummy258)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb057_support_mem_0273 (f : Var) :
    (nb057AlphaDummy260 f) ∈
      (((synCcompl (Class.cv (nb057AlphaDummy260 f)))).fv ∪
        ((synCcompl (Class.cv (nb057AlphaDummy261 f)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb057_support_mem_0274 :
    (nb057AlphaDummy257) ∈
      (((Class.cv (nb057AlphaDummy257))).fv ∪ ((Class.cv (nb057AlphaDummy257))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb057_support_mem_0275 (f : Var) :
    (nb057AlphaDummy260 f) ∈
      (((Class.cv (nb057AlphaDummy260 f))).fv ∪ ((Class.cv (nb057AlphaDummy260 f))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb057_support_mem_0276 :
    (nb057AlphaDummy258) ∈
      (((synCcompl (Class.cv (nb057AlphaDummy257)))).fv ∪
        ((synCcompl (Class.cv (nb057AlphaDummy258)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb057_support_mem_0277 (f : Var) :
    (nb057AlphaDummy261 f) ∈
      (((synCcompl (Class.cv (nb057AlphaDummy260 f)))).fv ∪
        ((synCcompl (Class.cv (nb057AlphaDummy261 f)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb057_support_mem_0278 :
    (nb057AlphaDummy258) ∈
      (((Class.cv (nb057AlphaDummy258))).fv ∪ ((Class.cv (nb057AlphaDummy258))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb057_support_mem_0279 (f : Var) :
    (nb057AlphaDummy261 f) ∈
      (((Class.cv (nb057AlphaDummy261 f))).fv ∪ ((Class.cv (nb057AlphaDummy261 f))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb057_support_mem_0280 :
    (nb057AlphaDummy238) ∈
      (((Class.cv (nb057AlphaDummy239))).fv ∪ ((Class.cv (nb057AlphaDummy238))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb057_support_mem_0281 :
    (nb057AlphaDummy238) ∈
      (((synCcompl (Class.cab (nb057AlphaDummy242)
              (synWrex (nb057AlphaDummy243) (Class.cv (nb057AlphaDummy239))
                (Wff.classEq (Class.cv (nb057AlphaDummy242))
                  (synCphi (Class.cv (nb057AlphaDummy243)))))))).fv ∪ ((synCcompl
            (Class.cab (nb057AlphaDummy242)
              (synWrex (nb057AlphaDummy243) (Class.cv (nb057AlphaDummy238))
                (Wff.classEq (Class.cv (nb057AlphaDummy242))
                  (synCun (synCphi (Class.cv (nb057AlphaDummy243)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0280) 0))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0280) 1))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb057_support_mem_0282 (f : Var) :
    (nb057AlphaDummy240 f) ∈
      (((Class.cv (nb057AlphaDummy241 f))).fv ∪ ((Class.cv (nb057AlphaDummy240 f))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb057_support_mem_0283 (f : Var) :
    (nb057AlphaDummy240 f) ∈
      (((synCcompl (Class.cab (nb057AlphaDummy244 f)
              (synWrex (nb057AlphaDummy245 f) (Class.cv (nb057AlphaDummy241 f))
                (Wff.classEq (Class.cv (nb057AlphaDummy244 f))
                  (synCphi (Class.cv (nb057AlphaDummy245 f)))))))).fv ∪ ((synCcompl
            (Class.cab (nb057AlphaDummy244 f)
              (synWrex (nb057AlphaDummy245 f) (Class.cv (nb057AlphaDummy240 f))
                (Wff.classEq (Class.cv (nb057AlphaDummy244 f))
                  (synCun (synCphi (Class.cv (nb057AlphaDummy245 f)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0282 f) 0))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0282 f) 1))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb057_support_mem_0284 :
    (nb057AlphaDummy238) ∈
      (((Class.cab (nb057AlphaDummy242)
            (synWrex (nb057AlphaDummy243) (Class.cv (nb057AlphaDummy238))
              (Wff.classEq (Class.cv (nb057AlphaDummy242))
                (synCun (synCphi (Class.cv (nb057AlphaDummy243)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb057AlphaDummy242)
            (synWrex (nb057AlphaDummy243) (Class.cv (nb057AlphaDummy238))
              (Wff.classEq (Class.cv (nb057AlphaDummy242))
                (synCun (synCphi (Class.cv (nb057AlphaDummy243)))
                  (synCsn (synC0c))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0280) 0))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0280) 1))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb057_support_mem_0285 (f : Var) :
    (nb057AlphaDummy240 f) ∈
      (((Class.cab (nb057AlphaDummy244 f)
            (synWrex (nb057AlphaDummy245 f) (Class.cv (nb057AlphaDummy240 f))
              (Wff.classEq (Class.cv (nb057AlphaDummy244 f))
                (synCun (synCphi (Class.cv (nb057AlphaDummy245 f)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb057AlphaDummy244 f)
            (synWrex (nb057AlphaDummy245 f) (Class.cv (nb057AlphaDummy240 f))
              (Wff.classEq (Class.cv (nb057AlphaDummy244 f))
                (synCun (synCphi (Class.cv (nb057AlphaDummy245 f)))
                  (synCsn (synC0c))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0282 f) 0))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0282 f) 1))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb057_support_mem_0286 :
    (nb057AlphaDummy243) ∈
      (((synCcompl (synCphi (Class.cv (nb057AlphaDummy243))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb057_support_mem_0287 (f : Var) :
    (nb057AlphaDummy245 f) ∈
      (((synCcompl (synCphi (Class.cv (nb057AlphaDummy245 f))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb057_support_mem_0288 :
    (nb057AlphaDummy243) ∈
      (((synCphi (Class.cv (nb057AlphaDummy243)))).fv ∪
        ((synCphi (Class.cv (nb057AlphaDummy243)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb057_support_mem_0289 (f : Var) :
    (nb057AlphaDummy245 f) ∈
      (((synCphi (Class.cv (nb057AlphaDummy245 f)))).fv ∪
        ((synCphi (Class.cv (nb057AlphaDummy245 f)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb057_support_mem_0290 :
    (nb057AlphaDummy001) ∈
      (((synCcnv (Class.cv (nb057AlphaDummy001)))).fv ∪ ((synCvv)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccnv]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb057_support_mem_0291 (f : Var) :
    f ∈ (((synCcnv (Class.cv f))).fv ∪ ((synCvv)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccnv]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb057_compact_fv_empty_0020 : (nb057AlphaDummy000) ∉ (∅ : Finset Var) :=
  by
  intro hmem
  cases hmem

theorem nb057_compact_fv_empty_0021 (a : Var) : a ∉ (∅ : Finset Var) :=
  by
  intro hmem
  cases hmem

theorem nb057_compact_fv_empty_0022 : (nb057AlphaDummy001) ∉ (∅ : Finset Var) :=
  by
  intro hmem
  cases hmem

theorem nb057_compact_fv_empty_0023 (f : Var) : f ∉ (∅ : Finset Var) :=
  by
  intro hmem
  cases hmem

theorem nb057_compact_fv_empty_0024 : (nb057AlphaDummy002) ∉ (∅ : Finset Var) :=
  by
  intro hmem
  cases hmem

theorem nb057_compact_fv_empty_0025 (f : Var) (a : Var) :
    (nb057AlphaDummy003 f a) ∉ (∅ : Finset Var) :=
  by
  intro hmem
  cases hmem


end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired
