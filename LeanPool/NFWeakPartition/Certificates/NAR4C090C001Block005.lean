/-
Copyright (c) 2026 Elliot Glazer and NFNotWPP contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elliot Glazer and NFNotWPP contributors
-/

module

public import LeanPool.NFWeakPartition.Certificates.NAR4C090C001Block004

/-! Nominal proof certificates grouped in dependency order. -/


public section

/-! Certificates from `NAR4C090C001Part017`. -/


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

theorem nb090_support_mem_0217 (h : Var) :
    (nb090AlphaDummy054 h) ∈
      (((synCcompl (Class.cab (nb090AlphaDummy209 h)
              (synWrex (nb090AlphaDummy210 h) (Class.cv (nb090AlphaDummy054 h))
                (Wff.classEq (Class.cv (nb090AlphaDummy209 h))
                  (synCphi (Class.cv (nb090AlphaDummy210 h)))))))).fv ∪ ((synCcompl
            (Class.cab (nb090AlphaDummy209 h)
              (synWrex (nb090AlphaDummy210 h) (Class.cv (nb090AlphaDummy053 h))
                (Wff.classEq (Class.cv (nb090AlphaDummy209 h))
                  (synCun (synCphi (Class.cv (nb090AlphaDummy210 h)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb090AlphaDummy054 h) ≠ (nb090AlphaDummy209 h) from (by
          unfold nb090AlphaDummy209;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0216 h) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb090AlphaDummy054 h) ≠ (nb090AlphaDummy210 h) from (by
            unfold nb090AlphaDummy210;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0216 h) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb090_support_mem_0218 (A : Class) :
    (nb090AlphaDummy051 A) ∈
      (((Class.cab (nb090AlphaDummy207 A)
            (synWrex (nb090AlphaDummy208 A) (Class.cv (nb090AlphaDummy051 A))
              (Wff.classEq (Class.cv (nb090AlphaDummy207 A))
                (synCphi (Class.cv (nb090AlphaDummy208 A))))))).fv ∪
        ((Class.cab (nb090AlphaDummy207 A)
            (synWrex (nb090AlphaDummy208 A) (Class.cv (nb090AlphaDummy051 A))
              (Wff.classEq (Class.cv (nb090AlphaDummy207 A))
                (synCphi (Class.cv (nb090AlphaDummy208 A))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb090AlphaDummy051 A) ≠ (nb090AlphaDummy207 A) from (by
          unfold nb090AlphaDummy207;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0214 A) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb090AlphaDummy051 A) ≠ (nb090AlphaDummy208 A) from (by
            unfold nb090AlphaDummy208;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0214 A) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb090_support_mem_0219 (h : Var) :
    (nb090AlphaDummy054 h) ∈
      (((Class.cab (nb090AlphaDummy209 h)
            (synWrex (nb090AlphaDummy210 h) (Class.cv (nb090AlphaDummy054 h))
              (Wff.classEq (Class.cv (nb090AlphaDummy209 h))
                (synCphi (Class.cv (nb090AlphaDummy210 h))))))).fv ∪
        ((Class.cab (nb090AlphaDummy209 h)
            (synWrex (nb090AlphaDummy210 h) (Class.cv (nb090AlphaDummy054 h))
              (Wff.classEq (Class.cv (nb090AlphaDummy209 h))
                (synCphi (Class.cv (nb090AlphaDummy210 h))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb090AlphaDummy054 h) ≠ (nb090AlphaDummy209 h) from (by
          unfold nb090AlphaDummy209;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0216 h) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb090AlphaDummy054 h) ≠ (nb090AlphaDummy210 h) from (by
            unfold nb090AlphaDummy210;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0216 h) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb090_support_mem_0220 (A : Class) :
    (nb090AlphaDummy208 A) ∈ (((Class.cv (nb090AlphaDummy208 A))).fv) :=
  by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0221 (h : Var) :
    (nb090AlphaDummy210 h) ∈ (((Class.cv (nb090AlphaDummy210 h))).fv) :=
  by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0222 (A : Class) :
    (nb090AlphaDummy215 A) ∈
      (((Wff.classMem (Class.cv (nb090AlphaDummy215 A)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb090AlphaDummy215 A)) (synC1c))).fv ∪
        ((Class.cv (nb090AlphaDummy215 A))).fv) :=
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

theorem nb090_support_mem_0223 (h : Var) :
    (nb090AlphaDummy217 h) ∈
      (((Wff.classMem (Class.cv (nb090AlphaDummy217 h)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb090AlphaDummy217 h)) (synC1c))).fv ∪
        ((Class.cv (nb090AlphaDummy217 h))).fv) :=
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

theorem nb090_support_mem_0224 (A : Class) :
    (nb090AlphaDummy215 A) ∈
      (((Class.cv (nb090AlphaDummy215 A))).fv ∪ ((synC1c)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0225 (h : Var) :
    (nb090AlphaDummy217 h) ∈
      (((Class.cv (nb090AlphaDummy217 h))).fv ∪ ((synC1c)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0226 (A : Class) :
    (nb090AlphaDummy222 A) ∈
      (((synCnin (Class.cv (nb090AlphaDummy222 A))
            (Class.cv (nb090AlphaDummy223 A)))).fv ∪
        ((synCnin (Class.cv (nb090AlphaDummy222 A))
            (Class.cv (nb090AlphaDummy223 A)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0227 (h : Var) :
    (nb090AlphaDummy225 h) ∈
      (((synCnin (Class.cv (nb090AlphaDummy225 h))
            (Class.cv (nb090AlphaDummy226 h)))).fv ∪
        ((synCnin (Class.cv (nb090AlphaDummy225 h))
            (Class.cv (nb090AlphaDummy226 h)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0228 (A : Class) :
    (nb090AlphaDummy222 A) ∈
      (((Class.cv (nb090AlphaDummy222 A))).fv ∪ ((Class.cv (nb090AlphaDummy223 A))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0229 (h : Var) :
    (nb090AlphaDummy225 h) ∈
      (((Class.cv (nb090AlphaDummy225 h))).fv ∪ ((Class.cv (nb090AlphaDummy226 h))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0230 (A : Class) :
    (nb090AlphaDummy223 A) ∈
      (((synCnin (Class.cv (nb090AlphaDummy222 A))
            (Class.cv (nb090AlphaDummy223 A)))).fv ∪
        ((synCnin (Class.cv (nb090AlphaDummy222 A))
            (Class.cv (nb090AlphaDummy223 A)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0231 (h : Var) :
    (nb090AlphaDummy226 h) ∈
      (((synCnin (Class.cv (nb090AlphaDummy225 h))
            (Class.cv (nb090AlphaDummy226 h)))).fv ∪
        ((synCnin (Class.cv (nb090AlphaDummy225 h))
            (Class.cv (nb090AlphaDummy226 h)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0232 (A : Class) :
    (nb090AlphaDummy223 A) ∈
      (((Class.cv (nb090AlphaDummy222 A))).fv ∪ ((Class.cv (nb090AlphaDummy223 A))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0233 (h : Var) :
    (nb090AlphaDummy226 h) ∈
      (((Class.cv (nb090AlphaDummy225 h))).fv ∪ ((Class.cv (nb090AlphaDummy226 h))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0234 (A : Class) :
    (nb090AlphaDummy222 A) ∈
      (((synCcompl (Class.cv (nb090AlphaDummy222 A)))).fv ∪
        ((synCcompl (Class.cv (nb090AlphaDummy223 A)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0235 (h : Var) :
    (nb090AlphaDummy225 h) ∈
      (((synCcompl (Class.cv (nb090AlphaDummy225 h)))).fv ∪
        ((synCcompl (Class.cv (nb090AlphaDummy226 h)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0236 (A : Class) :
    (nb090AlphaDummy222 A) ∈
      (((Class.cv (nb090AlphaDummy222 A))).fv ∪ ((Class.cv (nb090AlphaDummy222 A))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0237 (h : Var) :
    (nb090AlphaDummy225 h) ∈
      (((Class.cv (nb090AlphaDummy225 h))).fv ∪ ((Class.cv (nb090AlphaDummy225 h))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0238 (A : Class) :
    (nb090AlphaDummy223 A) ∈
      (((synCcompl (Class.cv (nb090AlphaDummy222 A)))).fv ∪
        ((synCcompl (Class.cv (nb090AlphaDummy223 A)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0239 (h : Var) :
    (nb090AlphaDummy226 h) ∈
      (((synCcompl (Class.cv (nb090AlphaDummy225 h)))).fv ∪
        ((synCcompl (Class.cv (nb090AlphaDummy226 h)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0240 (A : Class) :
    (nb090AlphaDummy223 A) ∈
      (((Class.cv (nb090AlphaDummy223 A))).fv ∪ ((Class.cv (nb090AlphaDummy223 A))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0241 (h : Var) :
    (nb090AlphaDummy226 h) ∈
      (((Class.cv (nb090AlphaDummy226 h))).fv ∪ ((Class.cv (nb090AlphaDummy226 h))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0242 (A : Class) :
    (nb090AlphaDummy050 A) ∈
      (((Class.cv (nb090AlphaDummy051 A))).fv ∪ ((Class.cv (nb090AlphaDummy050 A))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0243 (A : Class) :
    (nb090AlphaDummy050 A) ∈
      (((synCcompl (Class.cab (nb090AlphaDummy207 A)
              (synWrex (nb090AlphaDummy208 A) (Class.cv (nb090AlphaDummy051 A))
                (Wff.classEq (Class.cv (nb090AlphaDummy207 A))
                  (synCphi (Class.cv (nb090AlphaDummy208 A)))))))).fv ∪ ((synCcompl
            (Class.cab (nb090AlphaDummy207 A)
              (synWrex (nb090AlphaDummy208 A) (Class.cv (nb090AlphaDummy050 A))
                (Wff.classEq (Class.cv (nb090AlphaDummy207 A))
                  (synCun (synCphi (Class.cv (nb090AlphaDummy208 A)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb090AlphaDummy050 A) ≠ (nb090AlphaDummy207 A) from (by
          unfold nb090AlphaDummy207;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0242 A) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb090AlphaDummy050 A) ≠ (nb090AlphaDummy208 A) from (by
            unfold nb090AlphaDummy208;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0242 A) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb090_support_mem_0244 (h : Var) :
    (nb090AlphaDummy053 h) ∈
      (((Class.cv (nb090AlphaDummy054 h))).fv ∪ ((Class.cv (nb090AlphaDummy053 h))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0245 (h : Var) :
    (nb090AlphaDummy053 h) ∈
      (((synCcompl (Class.cab (nb090AlphaDummy209 h)
              (synWrex (nb090AlphaDummy210 h) (Class.cv (nb090AlphaDummy054 h))
                (Wff.classEq (Class.cv (nb090AlphaDummy209 h))
                  (synCphi (Class.cv (nb090AlphaDummy210 h)))))))).fv ∪ ((synCcompl
            (Class.cab (nb090AlphaDummy209 h)
              (synWrex (nb090AlphaDummy210 h) (Class.cv (nb090AlphaDummy053 h))
                (Wff.classEq (Class.cv (nb090AlphaDummy209 h))
                  (synCun (synCphi (Class.cv (nb090AlphaDummy210 h)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb090AlphaDummy053 h) ≠ (nb090AlphaDummy209 h) from (by
          unfold nb090AlphaDummy209;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0244 h) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb090AlphaDummy053 h) ≠ (nb090AlphaDummy210 h) from (by
            unfold nb090AlphaDummy210;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0244 h) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb090_support_mem_0246 (A : Class) :
    (nb090AlphaDummy050 A) ∈
      (((Class.cab (nb090AlphaDummy207 A)
            (synWrex (nb090AlphaDummy208 A) (Class.cv (nb090AlphaDummy050 A))
              (Wff.classEq (Class.cv (nb090AlphaDummy207 A))
                (synCun (synCphi (Class.cv (nb090AlphaDummy208 A)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb090AlphaDummy207 A)
            (synWrex (nb090AlphaDummy208 A) (Class.cv (nb090AlphaDummy050 A))
              (Wff.classEq (Class.cv (nb090AlphaDummy207 A))
                (synCun (synCphi (Class.cv (nb090AlphaDummy208 A)))
                  (synCsn (synC0c))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb090AlphaDummy050 A) ≠ (nb090AlphaDummy207 A) from (by
          unfold nb090AlphaDummy207;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0242 A) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb090AlphaDummy050 A) ≠ (nb090AlphaDummy208 A) from (by
            unfold nb090AlphaDummy208;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0242 A) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb090_support_mem_0247 (h : Var) :
    (nb090AlphaDummy053 h) ∈
      (((Class.cab (nb090AlphaDummy209 h)
            (synWrex (nb090AlphaDummy210 h) (Class.cv (nb090AlphaDummy053 h))
              (Wff.classEq (Class.cv (nb090AlphaDummy209 h))
                (synCun (synCphi (Class.cv (nb090AlphaDummy210 h)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb090AlphaDummy209 h)
            (synWrex (nb090AlphaDummy210 h) (Class.cv (nb090AlphaDummy053 h))
              (Wff.classEq (Class.cv (nb090AlphaDummy209 h))
                (synCun (synCphi (Class.cv (nb090AlphaDummy210 h)))
                  (synCsn (synC0c))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb090AlphaDummy053 h) ≠ (nb090AlphaDummy209 h) from (by
          unfold nb090AlphaDummy209;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0244 h) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb090AlphaDummy053 h) ≠ (nb090AlphaDummy210 h) from (by
            unfold nb090AlphaDummy210;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0244 h) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb090_support_mem_0248 (A : Class) :
    (nb090AlphaDummy208 A) ∈
      (((synCcompl (synCphi (Class.cv (nb090AlphaDummy208 A))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0249 (h : Var) :
    (nb090AlphaDummy210 h) ∈
      (((synCcompl (synCphi (Class.cv (nb090AlphaDummy210 h))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0250 (A : Class) :
    (nb090AlphaDummy208 A) ∈
      (((synCphi (Class.cv (nb090AlphaDummy208 A)))).fv ∪
        ((synCphi (Class.cv (nb090AlphaDummy208 A)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0251 (h : Var) :
    (nb090AlphaDummy210 h) ∈
      (((synCphi (Class.cv (nb090AlphaDummy210 h)))).fv ∪
        ((synCphi (Class.cv (nb090AlphaDummy210 h)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0252 (A : Class) :
    (nb090AlphaDummy244 A) ∈
      (((Class.cv (nb090AlphaDummy244 A))).fv ∪ ((Class.cv (nb090AlphaDummy243 A))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0253 (A : Class) :
    (nb090AlphaDummy244 A) ∈
      (((synCcompl (Class.cab (nb090AlphaDummy247 A)
              (synWrex (nb090AlphaDummy248 A) (Class.cv (nb090AlphaDummy244 A))
                (Wff.classEq (Class.cv (nb090AlphaDummy247 A))
                  (synCphi (Class.cv (nb090AlphaDummy248 A)))))))).fv ∪ ((synCcompl
            (Class.cab (nb090AlphaDummy247 A)
              (synWrex (nb090AlphaDummy248 A) (Class.cv (nb090AlphaDummy243 A))
                (Wff.classEq (Class.cv (nb090AlphaDummy247 A))
                  (synCun (synCphi (Class.cv (nb090AlphaDummy248 A)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb090AlphaDummy244 A) ≠ (nb090AlphaDummy247 A) from (by
          unfold nb090AlphaDummy247;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0252 A) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb090AlphaDummy244 A) ≠ (nb090AlphaDummy248 A) from (by
            unfold nb090AlphaDummy248;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0252 A) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb090_support_mem_0254 (h : Var) :
    (nb090AlphaDummy246 h) ∈
      (((Class.cv (nb090AlphaDummy246 h))).fv ∪ ((Class.cv (nb090AlphaDummy245 h))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0255 (h : Var) :
    (nb090AlphaDummy246 h) ∈
      (((synCcompl (Class.cab (nb090AlphaDummy249 h)
              (synWrex (nb090AlphaDummy250 h) (Class.cv (nb090AlphaDummy246 h))
                (Wff.classEq (Class.cv (nb090AlphaDummy249 h))
                  (synCphi (Class.cv (nb090AlphaDummy250 h)))))))).fv ∪ ((synCcompl
            (Class.cab (nb090AlphaDummy249 h)
              (synWrex (nb090AlphaDummy250 h) (Class.cv (nb090AlphaDummy245 h))
                (Wff.classEq (Class.cv (nb090AlphaDummy249 h))
                  (synCun (synCphi (Class.cv (nb090AlphaDummy250 h)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb090AlphaDummy246 h) ≠ (nb090AlphaDummy249 h) from (by
          unfold nb090AlphaDummy249;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0254 h) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb090AlphaDummy246 h) ≠ (nb090AlphaDummy250 h) from (by
            unfold nb090AlphaDummy250;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0254 h) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb090_support_mem_0256 (A : Class) :
    (nb090AlphaDummy244 A) ∈
      (((Class.cab (nb090AlphaDummy247 A)
            (synWrex (nb090AlphaDummy248 A) (Class.cv (nb090AlphaDummy244 A))
              (Wff.classEq (Class.cv (nb090AlphaDummy247 A))
                (synCphi (Class.cv (nb090AlphaDummy248 A))))))).fv ∪
        ((Class.cab (nb090AlphaDummy247 A)
            (synWrex (nb090AlphaDummy248 A) (Class.cv (nb090AlphaDummy244 A))
              (Wff.classEq (Class.cv (nb090AlphaDummy247 A))
                (synCphi (Class.cv (nb090AlphaDummy248 A))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb090AlphaDummy244 A) ≠ (nb090AlphaDummy247 A) from (by
          unfold nb090AlphaDummy247;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0252 A) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb090AlphaDummy244 A) ≠ (nb090AlphaDummy248 A) from (by
            unfold nb090AlphaDummy248;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0252 A) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb090_support_mem_0257 (h : Var) :
    (nb090AlphaDummy246 h) ∈
      (((Class.cab (nb090AlphaDummy249 h)
            (synWrex (nb090AlphaDummy250 h) (Class.cv (nb090AlphaDummy246 h))
              (Wff.classEq (Class.cv (nb090AlphaDummy249 h))
                (synCphi (Class.cv (nb090AlphaDummy250 h))))))).fv ∪
        ((Class.cab (nb090AlphaDummy249 h)
            (synWrex (nb090AlphaDummy250 h) (Class.cv (nb090AlphaDummy246 h))
              (Wff.classEq (Class.cv (nb090AlphaDummy249 h))
                (synCphi (Class.cv (nb090AlphaDummy250 h))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb090AlphaDummy246 h) ≠ (nb090AlphaDummy249 h) from (by
          unfold nb090AlphaDummy249;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0254 h) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb090AlphaDummy246 h) ≠ (nb090AlphaDummy250 h) from (by
            unfold nb090AlphaDummy250;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0254 h) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb090_support_mem_0258 (A : Class) :
    (nb090AlphaDummy248 A) ∈ (((Class.cv (nb090AlphaDummy248 A))).fv) :=
  by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0259 (h : Var) :
    (nb090AlphaDummy250 h) ∈ (((Class.cv (nb090AlphaDummy250 h))).fv) :=
  by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0260 (A : Class) :
    (nb090AlphaDummy255 A) ∈
      (((Wff.classMem (Class.cv (nb090AlphaDummy255 A)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb090AlphaDummy255 A)) (synC1c))).fv ∪
        ((Class.cv (nb090AlphaDummy255 A))).fv) :=
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

theorem nb090_support_mem_0261 (h : Var) :
    (nb090AlphaDummy257 h) ∈
      (((Wff.classMem (Class.cv (nb090AlphaDummy257 h)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb090AlphaDummy257 h)) (synC1c))).fv ∪
        ((Class.cv (nb090AlphaDummy257 h))).fv) :=
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

theorem nb090_support_mem_0262 (A : Class) :
    (nb090AlphaDummy255 A) ∈
      (((Class.cv (nb090AlphaDummy255 A))).fv ∪ ((synC1c)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0263 (h : Var) :
    (nb090AlphaDummy257 h) ∈
      (((Class.cv (nb090AlphaDummy257 h))).fv ∪ ((synC1c)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0264 (A : Class) :
    (nb090AlphaDummy262 A) ∈
      (((synCnin (Class.cv (nb090AlphaDummy262 A))
            (Class.cv (nb090AlphaDummy263 A)))).fv ∪
        ((synCnin (Class.cv (nb090AlphaDummy262 A))
            (Class.cv (nb090AlphaDummy263 A)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0265 (h : Var) :
    (nb090AlphaDummy265 h) ∈
      (((synCnin (Class.cv (nb090AlphaDummy265 h))
            (Class.cv (nb090AlphaDummy266 h)))).fv ∪
        ((synCnin (Class.cv (nb090AlphaDummy265 h))
            (Class.cv (nb090AlphaDummy266 h)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0266 (A : Class) :
    (nb090AlphaDummy262 A) ∈
      (((Class.cv (nb090AlphaDummy262 A))).fv ∪ ((Class.cv (nb090AlphaDummy263 A))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0267 (h : Var) :
    (nb090AlphaDummy265 h) ∈
      (((Class.cv (nb090AlphaDummy265 h))).fv ∪ ((Class.cv (nb090AlphaDummy266 h))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0268 (A : Class) :
    (nb090AlphaDummy263 A) ∈
      (((synCnin (Class.cv (nb090AlphaDummy262 A))
            (Class.cv (nb090AlphaDummy263 A)))).fv ∪
        ((synCnin (Class.cv (nb090AlphaDummy262 A))
            (Class.cv (nb090AlphaDummy263 A)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0269 (h : Var) :
    (nb090AlphaDummy266 h) ∈
      (((synCnin (Class.cv (nb090AlphaDummy265 h))
            (Class.cv (nb090AlphaDummy266 h)))).fv ∪
        ((synCnin (Class.cv (nb090AlphaDummy265 h))
            (Class.cv (nb090AlphaDummy266 h)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0270 (A : Class) :
    (nb090AlphaDummy263 A) ∈
      (((Class.cv (nb090AlphaDummy262 A))).fv ∪ ((Class.cv (nb090AlphaDummy263 A))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0271 (h : Var) :
    (nb090AlphaDummy266 h) ∈
      (((Class.cv (nb090AlphaDummy265 h))).fv ∪ ((Class.cv (nb090AlphaDummy266 h))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0272 (A : Class) :
    (nb090AlphaDummy262 A) ∈
      (((synCcompl (Class.cv (nb090AlphaDummy262 A)))).fv ∪
        ((synCcompl (Class.cv (nb090AlphaDummy263 A)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0273 (h : Var) :
    (nb090AlphaDummy265 h) ∈
      (((synCcompl (Class.cv (nb090AlphaDummy265 h)))).fv ∪
        ((synCcompl (Class.cv (nb090AlphaDummy266 h)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0274 (A : Class) :
    (nb090AlphaDummy262 A) ∈
      (((Class.cv (nb090AlphaDummy262 A))).fv ∪ ((Class.cv (nb090AlphaDummy262 A))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0275 (h : Var) :
    (nb090AlphaDummy265 h) ∈
      (((Class.cv (nb090AlphaDummy265 h))).fv ∪ ((Class.cv (nb090AlphaDummy265 h))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0276 (A : Class) :
    (nb090AlphaDummy263 A) ∈
      (((synCcompl (Class.cv (nb090AlphaDummy262 A)))).fv ∪
        ((synCcompl (Class.cv (nb090AlphaDummy263 A)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0277 (h : Var) :
    (nb090AlphaDummy266 h) ∈
      (((synCcompl (Class.cv (nb090AlphaDummy265 h)))).fv ∪
        ((synCcompl (Class.cv (nb090AlphaDummy266 h)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0278 (A : Class) :
    (nb090AlphaDummy263 A) ∈
      (((Class.cv (nb090AlphaDummy263 A))).fv ∪ ((Class.cv (nb090AlphaDummy263 A))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0279 (h : Var) :
    (nb090AlphaDummy266 h) ∈
      (((Class.cv (nb090AlphaDummy266 h))).fv ∪ ((Class.cv (nb090AlphaDummy266 h))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0280 (A : Class) :
    (nb090AlphaDummy243 A) ∈
      (((Class.cv (nb090AlphaDummy244 A))).fv ∪ ((Class.cv (nb090AlphaDummy243 A))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0281 (A : Class) :
    (nb090AlphaDummy243 A) ∈
      (((synCcompl (Class.cab (nb090AlphaDummy247 A)
              (synWrex (nb090AlphaDummy248 A) (Class.cv (nb090AlphaDummy244 A))
                (Wff.classEq (Class.cv (nb090AlphaDummy247 A))
                  (synCphi (Class.cv (nb090AlphaDummy248 A)))))))).fv ∪ ((synCcompl
            (Class.cab (nb090AlphaDummy247 A)
              (synWrex (nb090AlphaDummy248 A) (Class.cv (nb090AlphaDummy243 A))
                (Wff.classEq (Class.cv (nb090AlphaDummy247 A))
                  (synCun (synCphi (Class.cv (nb090AlphaDummy248 A)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb090AlphaDummy243 A) ≠ (nb090AlphaDummy247 A) from (by
          unfold nb090AlphaDummy247;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0280 A) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb090AlphaDummy243 A) ≠ (nb090AlphaDummy248 A) from (by
            unfold nb090AlphaDummy248;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0280 A) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb090_support_mem_0282 (h : Var) :
    (nb090AlphaDummy245 h) ∈
      (((Class.cv (nb090AlphaDummy246 h))).fv ∪ ((Class.cv (nb090AlphaDummy245 h))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0283 (h : Var) :
    (nb090AlphaDummy245 h) ∈
      (((synCcompl (Class.cab (nb090AlphaDummy249 h)
              (synWrex (nb090AlphaDummy250 h) (Class.cv (nb090AlphaDummy246 h))
                (Wff.classEq (Class.cv (nb090AlphaDummy249 h))
                  (synCphi (Class.cv (nb090AlphaDummy250 h)))))))).fv ∪ ((synCcompl
            (Class.cab (nb090AlphaDummy249 h)
              (synWrex (nb090AlphaDummy250 h) (Class.cv (nb090AlphaDummy245 h))
                (Wff.classEq (Class.cv (nb090AlphaDummy249 h))
                  (synCun (synCphi (Class.cv (nb090AlphaDummy250 h)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb090AlphaDummy245 h) ≠ (nb090AlphaDummy249 h) from (by
          unfold nb090AlphaDummy249;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0282 h) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb090AlphaDummy245 h) ≠ (nb090AlphaDummy250 h) from (by
            unfold nb090AlphaDummy250;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0282 h) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb090_support_mem_0284 (A : Class) :
    (nb090AlphaDummy243 A) ∈
      (((Class.cab (nb090AlphaDummy247 A)
            (synWrex (nb090AlphaDummy248 A) (Class.cv (nb090AlphaDummy243 A))
              (Wff.classEq (Class.cv (nb090AlphaDummy247 A))
                (synCun (synCphi (Class.cv (nb090AlphaDummy248 A)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb090AlphaDummy247 A)
            (synWrex (nb090AlphaDummy248 A) (Class.cv (nb090AlphaDummy243 A))
              (Wff.classEq (Class.cv (nb090AlphaDummy247 A))
                (synCun (synCphi (Class.cv (nb090AlphaDummy248 A)))
                  (synCsn (synC0c))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb090AlphaDummy243 A) ≠ (nb090AlphaDummy247 A) from (by
          unfold nb090AlphaDummy247;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0280 A) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb090AlphaDummy243 A) ≠ (nb090AlphaDummy248 A) from (by
            unfold nb090AlphaDummy248;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0280 A) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb090_support_mem_0285 (h : Var) :
    (nb090AlphaDummy245 h) ∈
      (((Class.cab (nb090AlphaDummy249 h)
            (synWrex (nb090AlphaDummy250 h) (Class.cv (nb090AlphaDummy245 h))
              (Wff.classEq (Class.cv (nb090AlphaDummy249 h))
                (synCun (synCphi (Class.cv (nb090AlphaDummy250 h)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb090AlphaDummy249 h)
            (synWrex (nb090AlphaDummy250 h) (Class.cv (nb090AlphaDummy245 h))
              (Wff.classEq (Class.cv (nb090AlphaDummy249 h))
                (synCun (synCphi (Class.cv (nb090AlphaDummy250 h)))
                  (synCsn (synC0c))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb090AlphaDummy245 h) ≠ (nb090AlphaDummy249 h) from (by
          unfold nb090AlphaDummy249;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0282 h) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb090AlphaDummy245 h) ≠ (nb090AlphaDummy250 h) from (by
            unfold nb090AlphaDummy250;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0282 h) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb090_support_mem_0286 (A : Class) :
    (nb090AlphaDummy248 A) ∈
      (((synCcompl (synCphi (Class.cv (nb090AlphaDummy248 A))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0287 (h : Var) :
    (nb090AlphaDummy250 h) ∈
      (((synCcompl (synCphi (Class.cv (nb090AlphaDummy250 h))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0288 (A : Class) :
    (nb090AlphaDummy248 A) ∈
      (((synCphi (Class.cv (nb090AlphaDummy248 A)))).fv ∪
        ((synCphi (Class.cv (nb090AlphaDummy248 A)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0289 (h : Var) :
    (nb090AlphaDummy250 h) ∈
      (((synCphi (Class.cv (nb090AlphaDummy250 h)))).fv ∪
        ((synCphi (Class.cv (nb090AlphaDummy250 h)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0290 (A : Class) :
    (nb090AlphaDummy000 A) ∈
      (((synCcnv (Class.cv (nb090AlphaDummy000 A)))).fv ∪ ((synCvv)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccnv]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0291 (h : Var) :
    h ∈ (((synCcnv (Class.cv h))).fv ∪ ((synCvv)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccnv]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0292 (A : Class) :
    (nb090AlphaDummy001 A) ∈
      (((synC2nd)).fv ∪ ((Class.cv (nb090AlphaDummy001 A))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0293 (A : Class) :
    (nb090AlphaDummy001 A) ∈
      (({(nb090AlphaDummy283 A)} : Finset Var) ∪
        ((synWbr (Class.cv (nb090AlphaDummy001 A)) (synC2nd)
            (Class.cv (nb090AlphaDummy283 A)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_wbr]
  with_reducible rw [Finset.mem_union]
  left
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0294 (A : Class) :
    (nb090AlphaDummy001 A) ∈
      (((Class.cab (nb090AlphaDummy285 A) (Wff.classEq (Class.cab (nb090AlphaDummy283 A)
              (synWbr (Class.cv (nb090AlphaDummy001 A)) (synC2nd)
                (Class.cv (nb090AlphaDummy283 A))))
            (synCsn (Class.cv (nb090AlphaDummy285 A)))))).fv) :=
  by
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb090AlphaDummy001 A) ≠ (nb090AlphaDummy285 A) from (by
          unfold nb090AlphaDummy285;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0293 A) 0))))
  · rw [fv_wff_classEq]
    with_reducible rw [Finset.mem_union]
    left
    rw [fv_class_cab]
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb090AlphaDummy001 A) ≠ (nb090AlphaDummy283 A) from (by
            unfold nb090AlphaDummy283;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0292 A) 0))))
    · rw [fv_syn_wbr]
      with_reducible rw [Finset.mem_union]
      left
      with_reducible rw [Finset.mem_union]
      left
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb090_support_mem_0295 (u : Var) : u ∈ (((synC2nd)).fv ∪ ((Class.cv u)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0296 (u : Var) :
    u ∈
      (({(nb090AlphaDummy284 u)} : Finset Var) ∪
        ((synWbr (Class.cv u) (synC2nd) (Class.cv (nb090AlphaDummy284 u)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_wbr]
  with_reducible rw [Finset.mem_union]
  left
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0297 (u : Var) :
    u ∈
      (((Class.cab (nb090AlphaDummy286 u) (Wff.classEq (Class.cab (nb090AlphaDummy284 u)
              (synWbr (Class.cv u) (synC2nd) (Class.cv (nb090AlphaDummy284 u))))
            (synCsn (Class.cv (nb090AlphaDummy286 u)))))).fv) :=
  by
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show u ≠ (nb090AlphaDummy286 u) from (by
          unfold nb090AlphaDummy286;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0296 u) 0))))
  · rw [fv_wff_classEq]
    with_reducible rw [Finset.mem_union]
    left
    rw [fv_class_cab]
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show u ≠ (nb090AlphaDummy284 u) from (by
            unfold nb090AlphaDummy284;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0295 u) 0))))
    · rw [fv_syn_wbr]
      with_reducible rw [Finset.mem_union]
      left
      with_reducible rw [Finset.mem_union]
      left
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb090_support_mem_0298 (A : Class) :
    (nb090AlphaDummy001 A) ∈
      (((Class.cv (nb090AlphaDummy001 A))).fv ∪ ((Class.cv (nb090AlphaDummy283 A))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0299 (A : Class) :
    (nb090AlphaDummy001 A) ∈
      (((synCcompl (Class.cab (nb090AlphaDummy291 A)
              (synWrex (nb090AlphaDummy292 A) (Class.cv (nb090AlphaDummy001 A))
                (Wff.classEq (Class.cv (nb090AlphaDummy291 A))
                  (synCphi (Class.cv (nb090AlphaDummy292 A)))))))).fv ∪ ((synCcompl
            (Class.cab (nb090AlphaDummy291 A)
              (synWrex (nb090AlphaDummy292 A) (Class.cv (nb090AlphaDummy283 A))
                (Wff.classEq (Class.cv (nb090AlphaDummy291 A))
                  (synCun (synCphi (Class.cv (nb090AlphaDummy292 A)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb090AlphaDummy001 A) ≠ (nb090AlphaDummy291 A) from (by
          unfold nb090AlphaDummy291;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0298 A) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb090AlphaDummy001 A) ≠ (nb090AlphaDummy292 A) from (by
            unfold nb090AlphaDummy292;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0298 A) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb090_support_mem_0300 (u : Var) :
    u ∈ (((Class.cv u)).fv ∪ ((Class.cv (nb090AlphaDummy284 u))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0301 (u : Var) :
    u ∈
      (((synCcompl (Class.cab (nb090AlphaDummy293 u)
              (synWrex (nb090AlphaDummy294 u) (Class.cv u)
                (Wff.classEq (Class.cv (nb090AlphaDummy293 u))
                  (synCphi (Class.cv (nb090AlphaDummy294 u)))))))).fv ∪ ((synCcompl
            (Class.cab (nb090AlphaDummy293 u)
              (synWrex (nb090AlphaDummy294 u) (Class.cv (nb090AlphaDummy284 u))
                (Wff.classEq (Class.cv (nb090AlphaDummy293 u))
                  (synCun (synCphi (Class.cv (nb090AlphaDummy294 u)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show u ≠ (nb090AlphaDummy293 u) from (by
          unfold nb090AlphaDummy293;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0300 u) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show u ≠ (nb090AlphaDummy294 u) from (by
            unfold nb090AlphaDummy294;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0300 u) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb090_support_mem_0302 (A : Class) :
    (nb090AlphaDummy001 A) ∈
      (((Class.cab (nb090AlphaDummy291 A)
            (synWrex (nb090AlphaDummy292 A) (Class.cv (nb090AlphaDummy001 A))
              (Wff.classEq (Class.cv (nb090AlphaDummy291 A))
                (synCphi (Class.cv (nb090AlphaDummy292 A))))))).fv ∪
        ((Class.cab (nb090AlphaDummy291 A)
            (synWrex (nb090AlphaDummy292 A) (Class.cv (nb090AlphaDummy001 A))
              (Wff.classEq (Class.cv (nb090AlphaDummy291 A))
                (synCphi (Class.cv (nb090AlphaDummy292 A))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb090AlphaDummy001 A) ≠ (nb090AlphaDummy291 A) from (by
          unfold nb090AlphaDummy291;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0298 A) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb090AlphaDummy001 A) ≠ (nb090AlphaDummy292 A) from (by
            unfold nb090AlphaDummy292;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0298 A) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb090_support_mem_0303 (u : Var) :
    u ∈
      (((Class.cab (nb090AlphaDummy293 u) (synWrex (nb090AlphaDummy294 u) (Class.cv u)
              (Wff.classEq (Class.cv (nb090AlphaDummy293 u))
                (synCphi (Class.cv (nb090AlphaDummy294 u))))))).fv ∪
        ((Class.cab (nb090AlphaDummy293 u) (synWrex (nb090AlphaDummy294 u) (Class.cv u)
              (Wff.classEq (Class.cv (nb090AlphaDummy293 u))
                (synCphi (Class.cv (nb090AlphaDummy294 u))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show u ≠ (nb090AlphaDummy293 u) from (by
          unfold nb090AlphaDummy293;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0300 u) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show u ≠ (nb090AlphaDummy294 u) from (by
            unfold nb090AlphaDummy294;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0300 u) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb090_support_mem_0304 (A : Class) :
    (nb090AlphaDummy292 A) ∈ (((Class.cv (nb090AlphaDummy292 A))).fv) :=
  by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0305 (u : Var) :
    (nb090AlphaDummy294 u) ∈ (((Class.cv (nb090AlphaDummy294 u))).fv) :=
  by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0306 (A : Class) :
    (nb090AlphaDummy299 A) ∈
      (((Wff.classMem (Class.cv (nb090AlphaDummy299 A)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb090AlphaDummy299 A)) (synC1c))).fv ∪
        ((Class.cv (nb090AlphaDummy299 A))).fv) :=
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

theorem nb090_support_mem_0307 (u : Var) :
    (nb090AlphaDummy301 u) ∈
      (((Wff.classMem (Class.cv (nb090AlphaDummy301 u)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb090AlphaDummy301 u)) (synC1c))).fv ∪
        ((Class.cv (nb090AlphaDummy301 u))).fv) :=
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

theorem nb090_support_mem_0308 (A : Class) :
    (nb090AlphaDummy299 A) ∈
      (((Class.cv (nb090AlphaDummy299 A))).fv ∪ ((synC1c)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0309 (u : Var) :
    (nb090AlphaDummy301 u) ∈
      (((Class.cv (nb090AlphaDummy301 u))).fv ∪ ((synC1c)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0310 (A : Class) :
    (nb090AlphaDummy306 A) ∈
      (((synCnin (Class.cv (nb090AlphaDummy306 A))
            (Class.cv (nb090AlphaDummy307 A)))).fv ∪
        ((synCnin (Class.cv (nb090AlphaDummy306 A))
            (Class.cv (nb090AlphaDummy307 A)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0311 (u : Var) :
    (nb090AlphaDummy309 u) ∈
      (((synCnin (Class.cv (nb090AlphaDummy309 u))
            (Class.cv (nb090AlphaDummy310 u)))).fv ∪
        ((synCnin (Class.cv (nb090AlphaDummy309 u))
            (Class.cv (nb090AlphaDummy310 u)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0312 (A : Class) :
    (nb090AlphaDummy306 A) ∈
      (((Class.cv (nb090AlphaDummy306 A))).fv ∪ ((Class.cv (nb090AlphaDummy307 A))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0313 (u : Var) :
    (nb090AlphaDummy309 u) ∈
      (((Class.cv (nb090AlphaDummy309 u))).fv ∪ ((Class.cv (nb090AlphaDummy310 u))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0314 (A : Class) :
    (nb090AlphaDummy307 A) ∈
      (((synCnin (Class.cv (nb090AlphaDummy306 A))
            (Class.cv (nb090AlphaDummy307 A)))).fv ∪
        ((synCnin (Class.cv (nb090AlphaDummy306 A))
            (Class.cv (nb090AlphaDummy307 A)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0315 (u : Var) :
    (nb090AlphaDummy310 u) ∈
      (((synCnin (Class.cv (nb090AlphaDummy309 u))
            (Class.cv (nb090AlphaDummy310 u)))).fv ∪
        ((synCnin (Class.cv (nb090AlphaDummy309 u))
            (Class.cv (nb090AlphaDummy310 u)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0316 (A : Class) :
    (nb090AlphaDummy307 A) ∈
      (((Class.cv (nb090AlphaDummy306 A))).fv ∪ ((Class.cv (nb090AlphaDummy307 A))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0317 (u : Var) :
    (nb090AlphaDummy310 u) ∈
      (((Class.cv (nb090AlphaDummy309 u))).fv ∪ ((Class.cv (nb090AlphaDummy310 u))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0318 (A : Class) :
    (nb090AlphaDummy306 A) ∈
      (((synCcompl (Class.cv (nb090AlphaDummy306 A)))).fv ∪
        ((synCcompl (Class.cv (nb090AlphaDummy307 A)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0319 (u : Var) :
    (nb090AlphaDummy309 u) ∈
      (((synCcompl (Class.cv (nb090AlphaDummy309 u)))).fv ∪
        ((synCcompl (Class.cv (nb090AlphaDummy310 u)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0320 (A : Class) :
    (nb090AlphaDummy306 A) ∈
      (((Class.cv (nb090AlphaDummy306 A))).fv ∪ ((Class.cv (nb090AlphaDummy306 A))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0321 (u : Var) :
    (nb090AlphaDummy309 u) ∈
      (((Class.cv (nb090AlphaDummy309 u))).fv ∪ ((Class.cv (nb090AlphaDummy309 u))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0322 (A : Class) :
    (nb090AlphaDummy307 A) ∈
      (((synCcompl (Class.cv (nb090AlphaDummy306 A)))).fv ∪
        ((synCcompl (Class.cv (nb090AlphaDummy307 A)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0323 (u : Var) :
    (nb090AlphaDummy310 u) ∈
      (((synCcompl (Class.cv (nb090AlphaDummy309 u)))).fv ∪
        ((synCcompl (Class.cv (nb090AlphaDummy310 u)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0324 (A : Class) :
    (nb090AlphaDummy307 A) ∈
      (((Class.cv (nb090AlphaDummy307 A))).fv ∪ ((Class.cv (nb090AlphaDummy307 A))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0325 (u : Var) :
    (nb090AlphaDummy310 u) ∈
      (((Class.cv (nb090AlphaDummy310 u))).fv ∪ ((Class.cv (nb090AlphaDummy310 u))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0326 (A : Class) :
    (nb090AlphaDummy283 A) ∈
      (((Class.cv (nb090AlphaDummy001 A))).fv ∪ ((Class.cv (nb090AlphaDummy283 A))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0327 (A : Class) :
    (nb090AlphaDummy283 A) ∈
      (((synCcompl (Class.cab (nb090AlphaDummy291 A)
              (synWrex (nb090AlphaDummy292 A) (Class.cv (nb090AlphaDummy001 A))
                (Wff.classEq (Class.cv (nb090AlphaDummy291 A))
                  (synCphi (Class.cv (nb090AlphaDummy292 A)))))))).fv ∪ ((synCcompl
            (Class.cab (nb090AlphaDummy291 A)
              (synWrex (nb090AlphaDummy292 A) (Class.cv (nb090AlphaDummy283 A))
                (Wff.classEq (Class.cv (nb090AlphaDummy291 A))
                  (synCun (synCphi (Class.cv (nb090AlphaDummy292 A)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb090AlphaDummy283 A) ≠ (nb090AlphaDummy291 A) from (by
          unfold nb090AlphaDummy291;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0326 A) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb090AlphaDummy283 A) ≠ (nb090AlphaDummy292 A) from (by
            unfold nb090AlphaDummy292;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0326 A) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb090_support_mem_0328 (u : Var) :
    (nb090AlphaDummy284 u) ∈
      (((Class.cv u)).fv ∪ ((Class.cv (nb090AlphaDummy284 u))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0329 (u : Var) :
    (nb090AlphaDummy284 u) ∈
      (((synCcompl (Class.cab (nb090AlphaDummy293 u)
              (synWrex (nb090AlphaDummy294 u) (Class.cv u)
                (Wff.classEq (Class.cv (nb090AlphaDummy293 u))
                  (synCphi (Class.cv (nb090AlphaDummy294 u)))))))).fv ∪ ((synCcompl
            (Class.cab (nb090AlphaDummy293 u)
              (synWrex (nb090AlphaDummy294 u) (Class.cv (nb090AlphaDummy284 u))
                (Wff.classEq (Class.cv (nb090AlphaDummy293 u))
                  (synCun (synCphi (Class.cv (nb090AlphaDummy294 u)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb090AlphaDummy284 u) ≠ (nb090AlphaDummy293 u) from (by
          unfold nb090AlphaDummy293;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0328 u) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb090AlphaDummy284 u) ≠ (nb090AlphaDummy294 u) from (by
            unfold nb090AlphaDummy294;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0328 u) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb090_support_mem_0330 (A : Class) :
    (nb090AlphaDummy283 A) ∈
      (((Class.cab (nb090AlphaDummy291 A)
            (synWrex (nb090AlphaDummy292 A) (Class.cv (nb090AlphaDummy283 A))
              (Wff.classEq (Class.cv (nb090AlphaDummy291 A))
                (synCun (synCphi (Class.cv (nb090AlphaDummy292 A)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb090AlphaDummy291 A)
            (synWrex (nb090AlphaDummy292 A) (Class.cv (nb090AlphaDummy283 A))
              (Wff.classEq (Class.cv (nb090AlphaDummy291 A))
                (synCun (synCphi (Class.cv (nb090AlphaDummy292 A)))
                  (synCsn (synC0c))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb090AlphaDummy283 A) ≠ (nb090AlphaDummy291 A) from (by
          unfold nb090AlphaDummy291;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0326 A) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb090AlphaDummy283 A) ≠ (nb090AlphaDummy292 A) from (by
            unfold nb090AlphaDummy292;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0326 A) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb090_support_mem_0331 (u : Var) :
    (nb090AlphaDummy284 u) ∈
      (((Class.cab (nb090AlphaDummy293 u)
            (synWrex (nb090AlphaDummy294 u) (Class.cv (nb090AlphaDummy284 u))
              (Wff.classEq (Class.cv (nb090AlphaDummy293 u))
                (synCun (synCphi (Class.cv (nb090AlphaDummy294 u)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb090AlphaDummy293 u)
            (synWrex (nb090AlphaDummy294 u) (Class.cv (nb090AlphaDummy284 u))
              (Wff.classEq (Class.cv (nb090AlphaDummy293 u))
                (synCun (synCphi (Class.cv (nb090AlphaDummy294 u)))
                  (synCsn (synC0c))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb090AlphaDummy284 u) ≠ (nb090AlphaDummy293 u) from (by
          unfold nb090AlphaDummy293;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0328 u) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb090AlphaDummy284 u) ≠ (nb090AlphaDummy294 u) from (by
            unfold nb090AlphaDummy294;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0328 u) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb090_support_mem_0332 (A : Class) :
    (nb090AlphaDummy292 A) ∈
      (((synCcompl (synCphi (Class.cv (nb090AlphaDummy292 A))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0333 (u : Var) :
    (nb090AlphaDummy294 u) ∈
      (((synCcompl (synCphi (Class.cv (nb090AlphaDummy294 u))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0334 (A : Class) :
    (nb090AlphaDummy292 A) ∈
      (((synCphi (Class.cv (nb090AlphaDummy292 A)))).fv ∪
        ((synCphi (Class.cv (nb090AlphaDummy292 A)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0335 (u : Var) :
    (nb090AlphaDummy294 u) ∈
      (((synCphi (Class.cv (nb090AlphaDummy294 u)))).fv ∪
        ((synCphi (Class.cv (nb090AlphaDummy294 u)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0336 (A : Class) :
    (nb090AlphaDummy285 A) ∈ (((Class.cv (nb090AlphaDummy285 A))).fv) :=
  by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0337 (u : Var) :
    (nb090AlphaDummy286 u) ∈ (((Class.cv (nb090AlphaDummy286 u))).fv) :=
  by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0338 (A : Class) :
    (nb090AlphaDummy334 A) ∈
      (((Class.cv (nb090AlphaDummy334 A))).fv ∪ ((Class.cv (nb090AlphaDummy333 A))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0339 (A : Class) :
    (nb090AlphaDummy334 A) ∈
      (((synCcompl (Class.cab (nb090AlphaDummy337 A)
              (synWrex (nb090AlphaDummy338 A) (Class.cv (nb090AlphaDummy334 A))
                (Wff.classEq (Class.cv (nb090AlphaDummy337 A))
                  (synCphi (Class.cv (nb090AlphaDummy338 A)))))))).fv ∪ ((synCcompl
            (Class.cab (nb090AlphaDummy337 A)
              (synWrex (nb090AlphaDummy338 A) (Class.cv (nb090AlphaDummy333 A))
                (Wff.classEq (Class.cv (nb090AlphaDummy337 A))
                  (synCun (synCphi (Class.cv (nb090AlphaDummy338 A)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb090AlphaDummy334 A) ≠ (nb090AlphaDummy337 A) from (by
          unfold nb090AlphaDummy337;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0338 A) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb090AlphaDummy334 A) ≠ (nb090AlphaDummy338 A) from (by
            unfold nb090AlphaDummy338;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0338 A) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb090_support_mem_0340 (h : Var) :
    (nb090AlphaDummy336 h) ∈
      (((Class.cv (nb090AlphaDummy336 h))).fv ∪ ((Class.cv (nb090AlphaDummy335 h))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0341 (h : Var) :
    (nb090AlphaDummy336 h) ∈
      (((synCcompl (Class.cab (nb090AlphaDummy339 h)
              (synWrex (nb090AlphaDummy340 h) (Class.cv (nb090AlphaDummy336 h))
                (Wff.classEq (Class.cv (nb090AlphaDummy339 h))
                  (synCphi (Class.cv (nb090AlphaDummy340 h)))))))).fv ∪ ((synCcompl
            (Class.cab (nb090AlphaDummy339 h)
              (synWrex (nb090AlphaDummy340 h) (Class.cv (nb090AlphaDummy335 h))
                (Wff.classEq (Class.cv (nb090AlphaDummy339 h))
                  (synCun (synCphi (Class.cv (nb090AlphaDummy340 h)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb090AlphaDummy336 h) ≠ (nb090AlphaDummy339 h) from (by
          unfold nb090AlphaDummy339;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0340 h) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb090AlphaDummy336 h) ≠ (nb090AlphaDummy340 h) from (by
            unfold nb090AlphaDummy340;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0340 h) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb090_support_mem_0342 (A : Class) :
    (nb090AlphaDummy334 A) ∈
      (((Class.cab (nb090AlphaDummy337 A)
            (synWrex (nb090AlphaDummy338 A) (Class.cv (nb090AlphaDummy334 A))
              (Wff.classEq (Class.cv (nb090AlphaDummy337 A))
                (synCphi (Class.cv (nb090AlphaDummy338 A))))))).fv ∪
        ((Class.cab (nb090AlphaDummy337 A)
            (synWrex (nb090AlphaDummy338 A) (Class.cv (nb090AlphaDummy334 A))
              (Wff.classEq (Class.cv (nb090AlphaDummy337 A))
                (synCphi (Class.cv (nb090AlphaDummy338 A))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb090AlphaDummy334 A) ≠ (nb090AlphaDummy337 A) from (by
          unfold nb090AlphaDummy337;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0338 A) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb090AlphaDummy334 A) ≠ (nb090AlphaDummy338 A) from (by
            unfold nb090AlphaDummy338;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0338 A) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb090_support_mem_0343 (h : Var) :
    (nb090AlphaDummy336 h) ∈
      (((Class.cab (nb090AlphaDummy339 h)
            (synWrex (nb090AlphaDummy340 h) (Class.cv (nb090AlphaDummy336 h))
              (Wff.classEq (Class.cv (nb090AlphaDummy339 h))
                (synCphi (Class.cv (nb090AlphaDummy340 h))))))).fv ∪
        ((Class.cab (nb090AlphaDummy339 h)
            (synWrex (nb090AlphaDummy340 h) (Class.cv (nb090AlphaDummy336 h))
              (Wff.classEq (Class.cv (nb090AlphaDummy339 h))
                (synCphi (Class.cv (nb090AlphaDummy340 h))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb090AlphaDummy336 h) ≠ (nb090AlphaDummy339 h) from (by
          unfold nb090AlphaDummy339;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0340 h) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb090AlphaDummy336 h) ≠ (nb090AlphaDummy340 h) from (by
            unfold nb090AlphaDummy340;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0340 h) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb090_support_mem_0344 (A : Class) :
    (nb090AlphaDummy338 A) ∈ (((Class.cv (nb090AlphaDummy338 A))).fv) :=
  by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0345 (h : Var) :
    (nb090AlphaDummy340 h) ∈ (((Class.cv (nb090AlphaDummy340 h))).fv) :=
  by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0346 (A : Class) :
    (nb090AlphaDummy345 A) ∈
      (((Wff.classMem (Class.cv (nb090AlphaDummy345 A)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb090AlphaDummy345 A)) (synC1c))).fv ∪
        ((Class.cv (nb090AlphaDummy345 A))).fv) :=
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

theorem nb090_support_mem_0347 (h : Var) :
    (nb090AlphaDummy347 h) ∈
      (((Wff.classMem (Class.cv (nb090AlphaDummy347 h)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb090AlphaDummy347 h)) (synC1c))).fv ∪
        ((Class.cv (nb090AlphaDummy347 h))).fv) :=
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

theorem nb090_support_mem_0348 (A : Class) :
    (nb090AlphaDummy345 A) ∈
      (((Class.cv (nb090AlphaDummy345 A))).fv ∪ ((synC1c)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0349 (h : Var) :
    (nb090AlphaDummy347 h) ∈
      (((Class.cv (nb090AlphaDummy347 h))).fv ∪ ((synC1c)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0350 (A : Class) :
    (nb090AlphaDummy352 A) ∈
      (((synCnin (Class.cv (nb090AlphaDummy352 A))
            (Class.cv (nb090AlphaDummy353 A)))).fv ∪
        ((synCnin (Class.cv (nb090AlphaDummy352 A))
            (Class.cv (nb090AlphaDummy353 A)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0351 (h : Var) :
    (nb090AlphaDummy355 h) ∈
      (((synCnin (Class.cv (nb090AlphaDummy355 h))
            (Class.cv (nb090AlphaDummy356 h)))).fv ∪
        ((synCnin (Class.cv (nb090AlphaDummy355 h))
            (Class.cv (nb090AlphaDummy356 h)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0352 (A : Class) :
    (nb090AlphaDummy352 A) ∈
      (((Class.cv (nb090AlphaDummy352 A))).fv ∪ ((Class.cv (nb090AlphaDummy353 A))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0353 (h : Var) :
    (nb090AlphaDummy355 h) ∈
      (((Class.cv (nb090AlphaDummy355 h))).fv ∪ ((Class.cv (nb090AlphaDummy356 h))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0354 (A : Class) :
    (nb090AlphaDummy353 A) ∈
      (((synCnin (Class.cv (nb090AlphaDummy352 A))
            (Class.cv (nb090AlphaDummy353 A)))).fv ∪
        ((synCnin (Class.cv (nb090AlphaDummy352 A))
            (Class.cv (nb090AlphaDummy353 A)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0355 (h : Var) :
    (nb090AlphaDummy356 h) ∈
      (((synCnin (Class.cv (nb090AlphaDummy355 h))
            (Class.cv (nb090AlphaDummy356 h)))).fv ∪
        ((synCnin (Class.cv (nb090AlphaDummy355 h))
            (Class.cv (nb090AlphaDummy356 h)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired

end

/-! Certificates from `NAR4C090C001Part018`. -/


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

theorem nb090_support_mem_0356 (A : Class) :
    (nb090AlphaDummy353 A) ∈
      (((Class.cv (nb090AlphaDummy352 A))).fv ∪ ((Class.cv (nb090AlphaDummy353 A))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0357 (h : Var) :
    (nb090AlphaDummy356 h) ∈
      (((Class.cv (nb090AlphaDummy355 h))).fv ∪ ((Class.cv (nb090AlphaDummy356 h))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0358 (A : Class) :
    (nb090AlphaDummy352 A) ∈
      (((synCcompl (Class.cv (nb090AlphaDummy352 A)))).fv ∪
        ((synCcompl (Class.cv (nb090AlphaDummy353 A)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0359 (h : Var) :
    (nb090AlphaDummy355 h) ∈
      (((synCcompl (Class.cv (nb090AlphaDummy355 h)))).fv ∪
        ((synCcompl (Class.cv (nb090AlphaDummy356 h)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0360 (A : Class) :
    (nb090AlphaDummy352 A) ∈
      (((Class.cv (nb090AlphaDummy352 A))).fv ∪ ((Class.cv (nb090AlphaDummy352 A))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0361 (h : Var) :
    (nb090AlphaDummy355 h) ∈
      (((Class.cv (nb090AlphaDummy355 h))).fv ∪ ((Class.cv (nb090AlphaDummy355 h))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0362 (A : Class) :
    (nb090AlphaDummy353 A) ∈
      (((synCcompl (Class.cv (nb090AlphaDummy352 A)))).fv ∪
        ((synCcompl (Class.cv (nb090AlphaDummy353 A)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0363 (h : Var) :
    (nb090AlphaDummy356 h) ∈
      (((synCcompl (Class.cv (nb090AlphaDummy355 h)))).fv ∪
        ((synCcompl (Class.cv (nb090AlphaDummy356 h)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0364 (A : Class) :
    (nb090AlphaDummy353 A) ∈
      (((Class.cv (nb090AlphaDummy353 A))).fv ∪ ((Class.cv (nb090AlphaDummy353 A))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0365 (h : Var) :
    (nb090AlphaDummy356 h) ∈
      (((Class.cv (nb090AlphaDummy356 h))).fv ∪ ((Class.cv (nb090AlphaDummy356 h))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0366 (A : Class) :
    (nb090AlphaDummy333 A) ∈
      (((Class.cv (nb090AlphaDummy334 A))).fv ∪ ((Class.cv (nb090AlphaDummy333 A))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0367 (A : Class) :
    (nb090AlphaDummy333 A) ∈
      (((synCcompl (Class.cab (nb090AlphaDummy337 A)
              (synWrex (nb090AlphaDummy338 A) (Class.cv (nb090AlphaDummy334 A))
                (Wff.classEq (Class.cv (nb090AlphaDummy337 A))
                  (synCphi (Class.cv (nb090AlphaDummy338 A)))))))).fv ∪ ((synCcompl
            (Class.cab (nb090AlphaDummy337 A)
              (synWrex (nb090AlphaDummy338 A) (Class.cv (nb090AlphaDummy333 A))
                (Wff.classEq (Class.cv (nb090AlphaDummy337 A))
                  (synCun (synCphi (Class.cv (nb090AlphaDummy338 A)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb090AlphaDummy333 A) ≠ (nb090AlphaDummy337 A) from (by
          unfold nb090AlphaDummy337;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0366 A) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb090AlphaDummy333 A) ≠ (nb090AlphaDummy338 A) from (by
            unfold nb090AlphaDummy338;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0366 A) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb090_support_mem_0368 (h : Var) :
    (nb090AlphaDummy335 h) ∈
      (((Class.cv (nb090AlphaDummy336 h))).fv ∪ ((Class.cv (nb090AlphaDummy335 h))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0369 (h : Var) :
    (nb090AlphaDummy335 h) ∈
      (((synCcompl (Class.cab (nb090AlphaDummy339 h)
              (synWrex (nb090AlphaDummy340 h) (Class.cv (nb090AlphaDummy336 h))
                (Wff.classEq (Class.cv (nb090AlphaDummy339 h))
                  (synCphi (Class.cv (nb090AlphaDummy340 h)))))))).fv ∪ ((synCcompl
            (Class.cab (nb090AlphaDummy339 h)
              (synWrex (nb090AlphaDummy340 h) (Class.cv (nb090AlphaDummy335 h))
                (Wff.classEq (Class.cv (nb090AlphaDummy339 h))
                  (synCun (synCphi (Class.cv (nb090AlphaDummy340 h)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb090AlphaDummy335 h) ≠ (nb090AlphaDummy339 h) from (by
          unfold nb090AlphaDummy339;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0368 h) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb090AlphaDummy335 h) ≠ (nb090AlphaDummy340 h) from (by
            unfold nb090AlphaDummy340;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0368 h) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb090_support_mem_0370 (A : Class) :
    (nb090AlphaDummy333 A) ∈
      (((Class.cab (nb090AlphaDummy337 A)
            (synWrex (nb090AlphaDummy338 A) (Class.cv (nb090AlphaDummy333 A))
              (Wff.classEq (Class.cv (nb090AlphaDummy337 A))
                (synCun (synCphi (Class.cv (nb090AlphaDummy338 A)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb090AlphaDummy337 A)
            (synWrex (nb090AlphaDummy338 A) (Class.cv (nb090AlphaDummy333 A))
              (Wff.classEq (Class.cv (nb090AlphaDummy337 A))
                (synCun (synCphi (Class.cv (nb090AlphaDummy338 A)))
                  (synCsn (synC0c))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb090AlphaDummy333 A) ≠ (nb090AlphaDummy337 A) from (by
          unfold nb090AlphaDummy337;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0366 A) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb090AlphaDummy333 A) ≠ (nb090AlphaDummy338 A) from (by
            unfold nb090AlphaDummy338;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0366 A) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb090_support_mem_0371 (h : Var) :
    (nb090AlphaDummy335 h) ∈
      (((Class.cab (nb090AlphaDummy339 h)
            (synWrex (nb090AlphaDummy340 h) (Class.cv (nb090AlphaDummy335 h))
              (Wff.classEq (Class.cv (nb090AlphaDummy339 h))
                (synCun (synCphi (Class.cv (nb090AlphaDummy340 h)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb090AlphaDummy339 h)
            (synWrex (nb090AlphaDummy340 h) (Class.cv (nb090AlphaDummy335 h))
              (Wff.classEq (Class.cv (nb090AlphaDummy339 h))
                (synCun (synCphi (Class.cv (nb090AlphaDummy340 h)))
                  (synCsn (synC0c))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb090AlphaDummy335 h) ≠ (nb090AlphaDummy339 h) from (by
          unfold nb090AlphaDummy339;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0368 h) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb090AlphaDummy335 h) ≠ (nb090AlphaDummy340 h) from (by
            unfold nb090AlphaDummy340;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0368 h) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb090_support_mem_0372 (A : Class) :
    (nb090AlphaDummy338 A) ∈
      (((synCcompl (synCphi (Class.cv (nb090AlphaDummy338 A))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0373 (h : Var) :
    (nb090AlphaDummy340 h) ∈
      (((synCcompl (synCphi (Class.cv (nb090AlphaDummy340 h))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0374 (A : Class) :
    (nb090AlphaDummy338 A) ∈
      (((synCphi (Class.cv (nb090AlphaDummy338 A)))).fv ∪
        ((synCphi (Class.cv (nb090AlphaDummy338 A)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0375 (h : Var) :
    (nb090AlphaDummy340 h) ∈
      (((synCphi (Class.cv (nb090AlphaDummy340 h)))).fv ∪
        ((synCphi (Class.cv (nb090AlphaDummy340 h)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0376 (A : Class) :
    (nb090AlphaDummy000 A) ∈
      (((synCnin (synCrn (Class.cv (nb090AlphaDummy000 A)))
            (synCfv (synC2nd) (Class.cv (nb090AlphaDummy002 A))))).fv ∪
        ((synCnin (synCrn (Class.cv (nb090AlphaDummy000 A)))
            (synCfv (synC2nd) (Class.cv (nb090AlphaDummy002 A))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_crn]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0377 (v : Var) (h : Var) :
    h ∈
      (((synCnin (synCrn (Class.cv h)) (synCfv (synC2nd) (Class.cv v)))).fv ∪
        ((synCnin (synCrn (Class.cv h)) (synCfv (synC2nd) (Class.cv v)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_crn]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0378 (A : Class) :
    (nb090AlphaDummy000 A) ∈
      (((synCrn (Class.cv (nb090AlphaDummy000 A)))).fv ∪
        ((synCfv (synC2nd) (Class.cv (nb090AlphaDummy002 A)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_crn]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0379 (v : Var) (h : Var) :
    h ∈ (((synCrn (Class.cv h))).fv ∪ ((synCfv (synC2nd) (Class.cv v))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_crn]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0380 (A : Class) :
    (nb090AlphaDummy000 A) ∈
      (((Class.cv (nb090AlphaDummy000 A))).fv ∪ ((synCvv)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0381 (h : Var) : h ∈ (((Class.cv h)).fv ∪ ((synCvv)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0382 (A : Class) :
    (nb090AlphaDummy002 A) ∈
      (((synCnin (synCrn (Class.cv (nb090AlphaDummy000 A)))
            (synCfv (synC2nd) (Class.cv (nb090AlphaDummy002 A))))).fv ∪
        ((synCnin (synCrn (Class.cv (nb090AlphaDummy000 A)))
            (synCfv (synC2nd) (Class.cv (nb090AlphaDummy002 A))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_cfv]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0383 (v : Var) (h : Var) :
    v ∈
      (((synCnin (synCrn (Class.cv h)) (synCfv (synC2nd) (Class.cv v)))).fv ∪
        ((synCnin (synCrn (Class.cv h)) (synCfv (synC2nd) (Class.cv v)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_cfv]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0384 (A : Class) :
    (nb090AlphaDummy002 A) ∈
      (((synCrn (Class.cv (nb090AlphaDummy000 A)))).fv ∪
        ((synCfv (synC2nd) (Class.cv (nb090AlphaDummy002 A)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_cfv]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0385 (v : Var) (h : Var) :
    v ∈ (((synCrn (Class.cv h))).fv ∪ ((synCfv (synC2nd) (Class.cv v))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_cfv]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0386 (A : Class) :
    (nb090AlphaDummy002 A) ∈
      (((synC2nd)).fv ∪ ((Class.cv (nb090AlphaDummy002 A))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0387 (A : Class) :
    (nb090AlphaDummy002 A) ∈
      (({(nb090AlphaDummy373 A)} : Finset Var) ∪
        ((synWbr (Class.cv (nb090AlphaDummy002 A)) (synC2nd)
            (Class.cv (nb090AlphaDummy373 A)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_wbr]
  with_reducible rw [Finset.mem_union]
  left
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0388 (A : Class) :
    (nb090AlphaDummy002 A) ∈
      (((Class.cab (nb090AlphaDummy375 A) (Wff.classEq (Class.cab (nb090AlphaDummy373 A)
              (synWbr (Class.cv (nb090AlphaDummy002 A)) (synC2nd)
                (Class.cv (nb090AlphaDummy373 A))))
            (synCsn (Class.cv (nb090AlphaDummy375 A)))))).fv) :=
  by
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb090AlphaDummy002 A) ≠ (nb090AlphaDummy375 A) from (by
          unfold nb090AlphaDummy375;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0387 A) 0))))
  · rw [fv_wff_classEq]
    with_reducible rw [Finset.mem_union]
    left
    rw [fv_class_cab]
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb090AlphaDummy002 A) ≠ (nb090AlphaDummy373 A) from (by
            unfold nb090AlphaDummy373;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0386 A) 0))))
    · rw [fv_syn_wbr]
      with_reducible rw [Finset.mem_union]
      left
      with_reducible rw [Finset.mem_union]
      left
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb090_support_mem_0389 (v : Var) : v ∈ (((synC2nd)).fv ∪ ((Class.cv v)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0390 (v : Var) :
    v ∈
      (({(nb090AlphaDummy374 v)} : Finset Var) ∪
        ((synWbr (Class.cv v) (synC2nd) (Class.cv (nb090AlphaDummy374 v)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_wbr]
  with_reducible rw [Finset.mem_union]
  left
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0391 (v : Var) :
    v ∈
      (((Class.cab (nb090AlphaDummy376 v) (Wff.classEq (Class.cab (nb090AlphaDummy374 v)
              (synWbr (Class.cv v) (synC2nd) (Class.cv (nb090AlphaDummy374 v))))
            (synCsn (Class.cv (nb090AlphaDummy376 v)))))).fv) :=
  by
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show v ≠ (nb090AlphaDummy376 v) from (by
          unfold nb090AlphaDummy376;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0390 v) 0))))
  · rw [fv_wff_classEq]
    with_reducible rw [Finset.mem_union]
    left
    rw [fv_class_cab]
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show v ≠ (nb090AlphaDummy374 v) from (by
            unfold nb090AlphaDummy374;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0389 v) 0))))
    · rw [fv_syn_wbr]
      with_reducible rw [Finset.mem_union]
      left
      with_reducible rw [Finset.mem_union]
      left
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb090_support_mem_0392 (A : Class) :
    (nb090AlphaDummy002 A) ∈
      (((Class.cv (nb090AlphaDummy002 A))).fv ∪ ((Class.cv (nb090AlphaDummy373 A))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0393 (A : Class) :
    (nb090AlphaDummy002 A) ∈
      (((synCcompl (Class.cab (nb090AlphaDummy381 A)
              (synWrex (nb090AlphaDummy382 A) (Class.cv (nb090AlphaDummy002 A))
                (Wff.classEq (Class.cv (nb090AlphaDummy381 A))
                  (synCphi (Class.cv (nb090AlphaDummy382 A)))))))).fv ∪ ((synCcompl
            (Class.cab (nb090AlphaDummy381 A)
              (synWrex (nb090AlphaDummy382 A) (Class.cv (nb090AlphaDummy373 A))
                (Wff.classEq (Class.cv (nb090AlphaDummy381 A))
                  (synCun (synCphi (Class.cv (nb090AlphaDummy382 A)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb090AlphaDummy002 A) ≠ (nb090AlphaDummy381 A) from (by
          unfold nb090AlphaDummy381;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0392 A) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb090AlphaDummy002 A) ≠ (nb090AlphaDummy382 A) from (by
            unfold nb090AlphaDummy382;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0392 A) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb090_support_mem_0394 (v : Var) :
    v ∈ (((Class.cv v)).fv ∪ ((Class.cv (nb090AlphaDummy374 v))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0395 (v : Var) :
    v ∈
      (((synCcompl (Class.cab (nb090AlphaDummy383 v)
              (synWrex (nb090AlphaDummy384 v) (Class.cv v)
                (Wff.classEq (Class.cv (nb090AlphaDummy383 v))
                  (synCphi (Class.cv (nb090AlphaDummy384 v)))))))).fv ∪ ((synCcompl
            (Class.cab (nb090AlphaDummy383 v)
              (synWrex (nb090AlphaDummy384 v) (Class.cv (nb090AlphaDummy374 v))
                (Wff.classEq (Class.cv (nb090AlphaDummy383 v))
                  (synCun (synCphi (Class.cv (nb090AlphaDummy384 v)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show v ≠ (nb090AlphaDummy383 v) from (by
          unfold nb090AlphaDummy383;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0394 v) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show v ≠ (nb090AlphaDummy384 v) from (by
            unfold nb090AlphaDummy384;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0394 v) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb090_support_mem_0396 (A : Class) :
    (nb090AlphaDummy002 A) ∈
      (((Class.cab (nb090AlphaDummy381 A)
            (synWrex (nb090AlphaDummy382 A) (Class.cv (nb090AlphaDummy002 A))
              (Wff.classEq (Class.cv (nb090AlphaDummy381 A))
                (synCphi (Class.cv (nb090AlphaDummy382 A))))))).fv ∪
        ((Class.cab (nb090AlphaDummy381 A)
            (synWrex (nb090AlphaDummy382 A) (Class.cv (nb090AlphaDummy002 A))
              (Wff.classEq (Class.cv (nb090AlphaDummy381 A))
                (synCphi (Class.cv (nb090AlphaDummy382 A))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb090AlphaDummy002 A) ≠ (nb090AlphaDummy381 A) from (by
          unfold nb090AlphaDummy381;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0392 A) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb090AlphaDummy002 A) ≠ (nb090AlphaDummy382 A) from (by
            unfold nb090AlphaDummy382;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0392 A) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb090_support_mem_0397 (v : Var) :
    v ∈
      (((Class.cab (nb090AlphaDummy383 v) (synWrex (nb090AlphaDummy384 v) (Class.cv v)
              (Wff.classEq (Class.cv (nb090AlphaDummy383 v))
                (synCphi (Class.cv (nb090AlphaDummy384 v))))))).fv ∪
        ((Class.cab (nb090AlphaDummy383 v) (synWrex (nb090AlphaDummy384 v) (Class.cv v)
              (Wff.classEq (Class.cv (nb090AlphaDummy383 v))
                (synCphi (Class.cv (nb090AlphaDummy384 v))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show v ≠ (nb090AlphaDummy383 v) from (by
          unfold nb090AlphaDummy383;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0394 v) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show v ≠ (nb090AlphaDummy384 v) from (by
            unfold nb090AlphaDummy384;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0394 v) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb090_support_mem_0398 (A : Class) :
    (nb090AlphaDummy382 A) ∈ (((Class.cv (nb090AlphaDummy382 A))).fv) :=
  by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0399 (v : Var) :
    (nb090AlphaDummy384 v) ∈ (((Class.cv (nb090AlphaDummy384 v))).fv) :=
  by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0400 (A : Class) :
    (nb090AlphaDummy389 A) ∈
      (((Wff.classMem (Class.cv (nb090AlphaDummy389 A)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb090AlphaDummy389 A)) (synC1c))).fv ∪
        ((Class.cv (nb090AlphaDummy389 A))).fv) :=
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

theorem nb090_support_mem_0401 (v : Var) :
    (nb090AlphaDummy391 v) ∈
      (((Wff.classMem (Class.cv (nb090AlphaDummy391 v)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb090AlphaDummy391 v)) (synC1c))).fv ∪
        ((Class.cv (nb090AlphaDummy391 v))).fv) :=
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

theorem nb090_support_mem_0402 (A : Class) :
    (nb090AlphaDummy389 A) ∈
      (((Class.cv (nb090AlphaDummy389 A))).fv ∪ ((synC1c)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0403 (v : Var) :
    (nb090AlphaDummy391 v) ∈
      (((Class.cv (nb090AlphaDummy391 v))).fv ∪ ((synC1c)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0404 (A : Class) :
    (nb090AlphaDummy396 A) ∈
      (((synCnin (Class.cv (nb090AlphaDummy396 A))
            (Class.cv (nb090AlphaDummy397 A)))).fv ∪
        ((synCnin (Class.cv (nb090AlphaDummy396 A))
            (Class.cv (nb090AlphaDummy397 A)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0405 (v : Var) :
    (nb090AlphaDummy399 v) ∈
      (((synCnin (Class.cv (nb090AlphaDummy399 v))
            (Class.cv (nb090AlphaDummy400 v)))).fv ∪
        ((synCnin (Class.cv (nb090AlphaDummy399 v))
            (Class.cv (nb090AlphaDummy400 v)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0406 (A : Class) :
    (nb090AlphaDummy396 A) ∈
      (((Class.cv (nb090AlphaDummy396 A))).fv ∪ ((Class.cv (nb090AlphaDummy397 A))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0407 (v : Var) :
    (nb090AlphaDummy399 v) ∈
      (((Class.cv (nb090AlphaDummy399 v))).fv ∪ ((Class.cv (nb090AlphaDummy400 v))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0408 (A : Class) :
    (nb090AlphaDummy397 A) ∈
      (((synCnin (Class.cv (nb090AlphaDummy396 A))
            (Class.cv (nb090AlphaDummy397 A)))).fv ∪
        ((synCnin (Class.cv (nb090AlphaDummy396 A))
            (Class.cv (nb090AlphaDummy397 A)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0409 (v : Var) :
    (nb090AlphaDummy400 v) ∈
      (((synCnin (Class.cv (nb090AlphaDummy399 v))
            (Class.cv (nb090AlphaDummy400 v)))).fv ∪
        ((synCnin (Class.cv (nb090AlphaDummy399 v))
            (Class.cv (nb090AlphaDummy400 v)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0410 (A : Class) :
    (nb090AlphaDummy397 A) ∈
      (((Class.cv (nb090AlphaDummy396 A))).fv ∪ ((Class.cv (nb090AlphaDummy397 A))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0411 (v : Var) :
    (nb090AlphaDummy400 v) ∈
      (((Class.cv (nb090AlphaDummy399 v))).fv ∪ ((Class.cv (nb090AlphaDummy400 v))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0412 (A : Class) :
    (nb090AlphaDummy396 A) ∈
      (((synCcompl (Class.cv (nb090AlphaDummy396 A)))).fv ∪
        ((synCcompl (Class.cv (nb090AlphaDummy397 A)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0413 (v : Var) :
    (nb090AlphaDummy399 v) ∈
      (((synCcompl (Class.cv (nb090AlphaDummy399 v)))).fv ∪
        ((synCcompl (Class.cv (nb090AlphaDummy400 v)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0414 (A : Class) :
    (nb090AlphaDummy396 A) ∈
      (((Class.cv (nb090AlphaDummy396 A))).fv ∪ ((Class.cv (nb090AlphaDummy396 A))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0415 (v : Var) :
    (nb090AlphaDummy399 v) ∈
      (((Class.cv (nb090AlphaDummy399 v))).fv ∪ ((Class.cv (nb090AlphaDummy399 v))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0416 (A : Class) :
    (nb090AlphaDummy397 A) ∈
      (((synCcompl (Class.cv (nb090AlphaDummy396 A)))).fv ∪
        ((synCcompl (Class.cv (nb090AlphaDummy397 A)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0417 (v : Var) :
    (nb090AlphaDummy400 v) ∈
      (((synCcompl (Class.cv (nb090AlphaDummy399 v)))).fv ∪
        ((synCcompl (Class.cv (nb090AlphaDummy400 v)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0418 (A : Class) :
    (nb090AlphaDummy397 A) ∈
      (((Class.cv (nb090AlphaDummy397 A))).fv ∪ ((Class.cv (nb090AlphaDummy397 A))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0419 (v : Var) :
    (nb090AlphaDummy400 v) ∈
      (((Class.cv (nb090AlphaDummy400 v))).fv ∪ ((Class.cv (nb090AlphaDummy400 v))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0420 (A : Class) :
    (nb090AlphaDummy373 A) ∈
      (((Class.cv (nb090AlphaDummy002 A))).fv ∪ ((Class.cv (nb090AlphaDummy373 A))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0421 (A : Class) :
    (nb090AlphaDummy373 A) ∈
      (((synCcompl (Class.cab (nb090AlphaDummy381 A)
              (synWrex (nb090AlphaDummy382 A) (Class.cv (nb090AlphaDummy002 A))
                (Wff.classEq (Class.cv (nb090AlphaDummy381 A))
                  (synCphi (Class.cv (nb090AlphaDummy382 A)))))))).fv ∪ ((synCcompl
            (Class.cab (nb090AlphaDummy381 A)
              (synWrex (nb090AlphaDummy382 A) (Class.cv (nb090AlphaDummy373 A))
                (Wff.classEq (Class.cv (nb090AlphaDummy381 A))
                  (synCun (synCphi (Class.cv (nb090AlphaDummy382 A)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb090AlphaDummy373 A) ≠ (nb090AlphaDummy381 A) from (by
          unfold nb090AlphaDummy381;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0420 A) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb090AlphaDummy373 A) ≠ (nb090AlphaDummy382 A) from (by
            unfold nb090AlphaDummy382;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0420 A) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb090_support_mem_0422 (v : Var) :
    (nb090AlphaDummy374 v) ∈
      (((Class.cv v)).fv ∪ ((Class.cv (nb090AlphaDummy374 v))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0423 (v : Var) :
    (nb090AlphaDummy374 v) ∈
      (((synCcompl (Class.cab (nb090AlphaDummy383 v)
              (synWrex (nb090AlphaDummy384 v) (Class.cv v)
                (Wff.classEq (Class.cv (nb090AlphaDummy383 v))
                  (synCphi (Class.cv (nb090AlphaDummy384 v)))))))).fv ∪ ((synCcompl
            (Class.cab (nb090AlphaDummy383 v)
              (synWrex (nb090AlphaDummy384 v) (Class.cv (nb090AlphaDummy374 v))
                (Wff.classEq (Class.cv (nb090AlphaDummy383 v))
                  (synCun (synCphi (Class.cv (nb090AlphaDummy384 v)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb090AlphaDummy374 v) ≠ (nb090AlphaDummy383 v) from (by
          unfold nb090AlphaDummy383;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0422 v) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb090AlphaDummy374 v) ≠ (nb090AlphaDummy384 v) from (by
            unfold nb090AlphaDummy384;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0422 v) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb090_support_mem_0424 (A : Class) :
    (nb090AlphaDummy373 A) ∈
      (((Class.cab (nb090AlphaDummy381 A)
            (synWrex (nb090AlphaDummy382 A) (Class.cv (nb090AlphaDummy373 A))
              (Wff.classEq (Class.cv (nb090AlphaDummy381 A))
                (synCun (synCphi (Class.cv (nb090AlphaDummy382 A)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb090AlphaDummy381 A)
            (synWrex (nb090AlphaDummy382 A) (Class.cv (nb090AlphaDummy373 A))
              (Wff.classEq (Class.cv (nb090AlphaDummy381 A))
                (synCun (synCphi (Class.cv (nb090AlphaDummy382 A)))
                  (synCsn (synC0c))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb090AlphaDummy373 A) ≠ (nb090AlphaDummy381 A) from (by
          unfold nb090AlphaDummy381;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0420 A) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb090AlphaDummy373 A) ≠ (nb090AlphaDummy382 A) from (by
            unfold nb090AlphaDummy382;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0420 A) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb090_support_mem_0425 (v : Var) :
    (nb090AlphaDummy374 v) ∈
      (((Class.cab (nb090AlphaDummy383 v)
            (synWrex (nb090AlphaDummy384 v) (Class.cv (nb090AlphaDummy374 v))
              (Wff.classEq (Class.cv (nb090AlphaDummy383 v))
                (synCun (synCphi (Class.cv (nb090AlphaDummy384 v)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb090AlphaDummy383 v)
            (synWrex (nb090AlphaDummy384 v) (Class.cv (nb090AlphaDummy374 v))
              (Wff.classEq (Class.cv (nb090AlphaDummy383 v))
                (synCun (synCphi (Class.cv (nb090AlphaDummy384 v)))
                  (synCsn (synC0c))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb090AlphaDummy374 v) ≠ (nb090AlphaDummy383 v) from (by
          unfold nb090AlphaDummy383;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0422 v) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb090AlphaDummy374 v) ≠ (nb090AlphaDummy384 v) from (by
            unfold nb090AlphaDummy384;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0422 v) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb090_support_mem_0426 (A : Class) :
    (nb090AlphaDummy382 A) ∈
      (((synCcompl (synCphi (Class.cv (nb090AlphaDummy382 A))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0427 (v : Var) :
    (nb090AlphaDummy384 v) ∈
      (((synCcompl (synCphi (Class.cv (nb090AlphaDummy384 v))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0428 (A : Class) :
    (nb090AlphaDummy382 A) ∈
      (((synCphi (Class.cv (nb090AlphaDummy382 A)))).fv ∪
        ((synCphi (Class.cv (nb090AlphaDummy382 A)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0429 (v : Var) :
    (nb090AlphaDummy384 v) ∈
      (((synCphi (Class.cv (nb090AlphaDummy384 v)))).fv ∪
        ((synCphi (Class.cv (nb090AlphaDummy384 v)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0430 (A : Class) :
    (nb090AlphaDummy375 A) ∈ (((Class.cv (nb090AlphaDummy375 A))).fv) :=
  by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0431 (v : Var) :
    (nb090AlphaDummy376 v) ∈ (((Class.cv (nb090AlphaDummy376 v))).fv) :=
  by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0432 (A : Class) :
    (nb090AlphaDummy423 A) ∈
      (({(nb090AlphaDummy423 A)} : Finset Var) ∪ ({(nb090AlphaDummy424 A)} : Finset Var) ∪
        ((synWex (nb090AlphaDummy425 A) (synWa
              (synWbr (Class.cv (nb090AlphaDummy423 A))
                (synCcnv (synCcnv (Class.cv (nb090AlphaDummy000 A))))
                (Class.cv (nb090AlphaDummy425 A)))
              (synWbr (Class.cv (nb090AlphaDummy425 A))
                (synCcnv (Class.cv (nb090AlphaDummy000 A)))
                (Class.cv (nb090AlphaDummy424 A)))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  with_reducible rw [Finset.mem_union]
  left
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0433 (h : Var) :
    (nb090AlphaDummy426 h) ∈
      (({(nb090AlphaDummy426 h)} : Finset Var) ∪ ({(nb090AlphaDummy427 h)} : Finset Var) ∪
        ((synWex (nb090AlphaDummy428 h) (synWa
              (synWbr (Class.cv (nb090AlphaDummy426 h))
                (synCcnv (synCcnv (Class.cv h))) (Class.cv (nb090AlphaDummy428 h)))
              (synWbr (Class.cv (nb090AlphaDummy428 h)) (synCcnv (Class.cv h))
                (Class.cv (nb090AlphaDummy427 h)))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  with_reducible rw [Finset.mem_union]
  left
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0434 (A : Class) :
    (nb090AlphaDummy424 A) ∈
      (({(nb090AlphaDummy423 A)} : Finset Var) ∪ ({(nb090AlphaDummy424 A)} : Finset Var) ∪
        ((synWex (nb090AlphaDummy425 A) (synWa
              (synWbr (Class.cv (nb090AlphaDummy423 A))
                (synCcnv (synCcnv (Class.cv (nb090AlphaDummy000 A))))
                (Class.cv (nb090AlphaDummy425 A)))
              (synWbr (Class.cv (nb090AlphaDummy425 A))
                (synCcnv (Class.cv (nb090AlphaDummy000 A)))
                (Class.cv (nb090AlphaDummy424 A)))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  with_reducible rw [Finset.mem_union]
  right
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0435 (h : Var) :
    (nb090AlphaDummy427 h) ∈
      (({(nb090AlphaDummy426 h)} : Finset Var) ∪ ({(nb090AlphaDummy427 h)} : Finset Var) ∪
        ((synWex (nb090AlphaDummy428 h) (synWa
              (synWbr (Class.cv (nb090AlphaDummy426 h))
                (synCcnv (synCcnv (Class.cv h))) (Class.cv (nb090AlphaDummy428 h)))
              (synWbr (Class.cv (nb090AlphaDummy428 h)) (synCcnv (Class.cv h))
                (Class.cv (nb090AlphaDummy427 h)))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  with_reducible rw [Finset.mem_union]
  right
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0436 (A : Class) :
    (nb090AlphaDummy423 A) ∈
      (((Class.cv (nb090AlphaDummy423 A))).fv ∪ ((Class.cv (nb090AlphaDummy424 A))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0437 (A : Class) :
    (nb090AlphaDummy423 A) ∈
      (((synCcompl (Class.cab (nb090AlphaDummy431 A)
              (synWrex (nb090AlphaDummy432 A) (Class.cv (nb090AlphaDummy423 A))
                (Wff.classEq (Class.cv (nb090AlphaDummy431 A))
                  (synCphi (Class.cv (nb090AlphaDummy432 A)))))))).fv ∪ ((synCcompl
            (Class.cab (nb090AlphaDummy431 A)
              (synWrex (nb090AlphaDummy432 A) (Class.cv (nb090AlphaDummy424 A))
                (Wff.classEq (Class.cv (nb090AlphaDummy431 A))
                  (synCun (synCphi (Class.cv (nb090AlphaDummy432 A)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb090AlphaDummy423 A) ≠ (nb090AlphaDummy431 A) from (by
          unfold nb090AlphaDummy431;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0436 A) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb090AlphaDummy423 A) ≠ (nb090AlphaDummy432 A) from (by
            unfold nb090AlphaDummy432;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0436 A) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb090_support_mem_0438 (h : Var) :
    (nb090AlphaDummy426 h) ∈
      (((Class.cv (nb090AlphaDummy426 h))).fv ∪ ((Class.cv (nb090AlphaDummy427 h))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0439 (h : Var) :
    (nb090AlphaDummy426 h) ∈
      (((synCcompl (Class.cab (nb090AlphaDummy433 h)
              (synWrex (nb090AlphaDummy434 h) (Class.cv (nb090AlphaDummy426 h))
                (Wff.classEq (Class.cv (nb090AlphaDummy433 h))
                  (synCphi (Class.cv (nb090AlphaDummy434 h)))))))).fv ∪ ((synCcompl
            (Class.cab (nb090AlphaDummy433 h)
              (synWrex (nb090AlphaDummy434 h) (Class.cv (nb090AlphaDummy427 h))
                (Wff.classEq (Class.cv (nb090AlphaDummy433 h))
                  (synCun (synCphi (Class.cv (nb090AlphaDummy434 h)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb090AlphaDummy426 h) ≠ (nb090AlphaDummy433 h) from (by
          unfold nb090AlphaDummy433;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0438 h) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb090AlphaDummy426 h) ≠ (nb090AlphaDummy434 h) from (by
            unfold nb090AlphaDummy434;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0438 h) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb090_support_mem_0440 (A : Class) :
    (nb090AlphaDummy423 A) ∈
      (((Class.cab (nb090AlphaDummy431 A)
            (synWrex (nb090AlphaDummy432 A) (Class.cv (nb090AlphaDummy423 A))
              (Wff.classEq (Class.cv (nb090AlphaDummy431 A))
                (synCphi (Class.cv (nb090AlphaDummy432 A))))))).fv ∪
        ((Class.cab (nb090AlphaDummy431 A)
            (synWrex (nb090AlphaDummy432 A) (Class.cv (nb090AlphaDummy423 A))
              (Wff.classEq (Class.cv (nb090AlphaDummy431 A))
                (synCphi (Class.cv (nb090AlphaDummy432 A))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb090AlphaDummy423 A) ≠ (nb090AlphaDummy431 A) from (by
          unfold nb090AlphaDummy431;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0436 A) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb090AlphaDummy423 A) ≠ (nb090AlphaDummy432 A) from (by
            unfold nb090AlphaDummy432;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0436 A) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb090_support_mem_0441 (h : Var) :
    (nb090AlphaDummy426 h) ∈
      (((Class.cab (nb090AlphaDummy433 h)
            (synWrex (nb090AlphaDummy434 h) (Class.cv (nb090AlphaDummy426 h))
              (Wff.classEq (Class.cv (nb090AlphaDummy433 h))
                (synCphi (Class.cv (nb090AlphaDummy434 h))))))).fv ∪
        ((Class.cab (nb090AlphaDummy433 h)
            (synWrex (nb090AlphaDummy434 h) (Class.cv (nb090AlphaDummy426 h))
              (Wff.classEq (Class.cv (nb090AlphaDummy433 h))
                (synCphi (Class.cv (nb090AlphaDummy434 h))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb090AlphaDummy426 h) ≠ (nb090AlphaDummy433 h) from (by
          unfold nb090AlphaDummy433;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0438 h) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb090AlphaDummy426 h) ≠ (nb090AlphaDummy434 h) from (by
            unfold nb090AlphaDummy434;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0438 h) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb090_support_mem_0442 (A : Class) :
    (nb090AlphaDummy432 A) ∈ (((Class.cv (nb090AlphaDummy432 A))).fv) :=
  by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0443 (h : Var) :
    (nb090AlphaDummy434 h) ∈ (((Class.cv (nb090AlphaDummy434 h))).fv) :=
  by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0444 (A : Class) :
    (nb090AlphaDummy439 A) ∈
      (((Wff.classMem (Class.cv (nb090AlphaDummy439 A)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb090AlphaDummy439 A)) (synC1c))).fv ∪
        ((Class.cv (nb090AlphaDummy439 A))).fv) :=
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

theorem nb090_support_mem_0445 (h : Var) :
    (nb090AlphaDummy441 h) ∈
      (((Wff.classMem (Class.cv (nb090AlphaDummy441 h)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb090AlphaDummy441 h)) (synC1c))).fv ∪
        ((Class.cv (nb090AlphaDummy441 h))).fv) :=
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

theorem nb090_support_mem_0446 (A : Class) :
    (nb090AlphaDummy439 A) ∈
      (((Class.cv (nb090AlphaDummy439 A))).fv ∪ ((synC1c)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0447 (h : Var) :
    (nb090AlphaDummy441 h) ∈
      (((Class.cv (nb090AlphaDummy441 h))).fv ∪ ((synC1c)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0448 (A : Class) :
    (nb090AlphaDummy446 A) ∈
      (((synCnin (Class.cv (nb090AlphaDummy446 A))
            (Class.cv (nb090AlphaDummy447 A)))).fv ∪
        ((synCnin (Class.cv (nb090AlphaDummy446 A))
            (Class.cv (nb090AlphaDummy447 A)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0449 (h : Var) :
    (nb090AlphaDummy449 h) ∈
      (((synCnin (Class.cv (nb090AlphaDummy449 h))
            (Class.cv (nb090AlphaDummy450 h)))).fv ∪
        ((synCnin (Class.cv (nb090AlphaDummy449 h))
            (Class.cv (nb090AlphaDummy450 h)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0450 (A : Class) :
    (nb090AlphaDummy446 A) ∈
      (((Class.cv (nb090AlphaDummy446 A))).fv ∪ ((Class.cv (nb090AlphaDummy447 A))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0451 (h : Var) :
    (nb090AlphaDummy449 h) ∈
      (((Class.cv (nb090AlphaDummy449 h))).fv ∪ ((Class.cv (nb090AlphaDummy450 h))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0452 (A : Class) :
    (nb090AlphaDummy447 A) ∈
      (((synCnin (Class.cv (nb090AlphaDummy446 A))
            (Class.cv (nb090AlphaDummy447 A)))).fv ∪
        ((synCnin (Class.cv (nb090AlphaDummy446 A))
            (Class.cv (nb090AlphaDummy447 A)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0453 (h : Var) :
    (nb090AlphaDummy450 h) ∈
      (((synCnin (Class.cv (nb090AlphaDummy449 h))
            (Class.cv (nb090AlphaDummy450 h)))).fv ∪
        ((synCnin (Class.cv (nb090AlphaDummy449 h))
            (Class.cv (nb090AlphaDummy450 h)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0454 (A : Class) :
    (nb090AlphaDummy447 A) ∈
      (((Class.cv (nb090AlphaDummy446 A))).fv ∪ ((Class.cv (nb090AlphaDummy447 A))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0455 (h : Var) :
    (nb090AlphaDummy450 h) ∈
      (((Class.cv (nb090AlphaDummy449 h))).fv ∪ ((Class.cv (nb090AlphaDummy450 h))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0456 (A : Class) :
    (nb090AlphaDummy446 A) ∈
      (((synCcompl (Class.cv (nb090AlphaDummy446 A)))).fv ∪
        ((synCcompl (Class.cv (nb090AlphaDummy447 A)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0457 (h : Var) :
    (nb090AlphaDummy449 h) ∈
      (((synCcompl (Class.cv (nb090AlphaDummy449 h)))).fv ∪
        ((synCcompl (Class.cv (nb090AlphaDummy450 h)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0458 (A : Class) :
    (nb090AlphaDummy446 A) ∈
      (((Class.cv (nb090AlphaDummy446 A))).fv ∪ ((Class.cv (nb090AlphaDummy446 A))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0459 (h : Var) :
    (nb090AlphaDummy449 h) ∈
      (((Class.cv (nb090AlphaDummy449 h))).fv ∪ ((Class.cv (nb090AlphaDummy449 h))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0460 (A : Class) :
    (nb090AlphaDummy447 A) ∈
      (((synCcompl (Class.cv (nb090AlphaDummy446 A)))).fv ∪
        ((synCcompl (Class.cv (nb090AlphaDummy447 A)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0461 (h : Var) :
    (nb090AlphaDummy450 h) ∈
      (((synCcompl (Class.cv (nb090AlphaDummy449 h)))).fv ∪
        ((synCcompl (Class.cv (nb090AlphaDummy450 h)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0462 (A : Class) :
    (nb090AlphaDummy447 A) ∈
      (((Class.cv (nb090AlphaDummy447 A))).fv ∪ ((Class.cv (nb090AlphaDummy447 A))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0463 (h : Var) :
    (nb090AlphaDummy450 h) ∈
      (((Class.cv (nb090AlphaDummy450 h))).fv ∪ ((Class.cv (nb090AlphaDummy450 h))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0464 (A : Class) :
    (nb090AlphaDummy424 A) ∈
      (((Class.cv (nb090AlphaDummy423 A))).fv ∪ ((Class.cv (nb090AlphaDummy424 A))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0465 (A : Class) :
    (nb090AlphaDummy424 A) ∈
      (((synCcompl (Class.cab (nb090AlphaDummy431 A)
              (synWrex (nb090AlphaDummy432 A) (Class.cv (nb090AlphaDummy423 A))
                (Wff.classEq (Class.cv (nb090AlphaDummy431 A))
                  (synCphi (Class.cv (nb090AlphaDummy432 A)))))))).fv ∪ ((synCcompl
            (Class.cab (nb090AlphaDummy431 A)
              (synWrex (nb090AlphaDummy432 A) (Class.cv (nb090AlphaDummy424 A))
                (Wff.classEq (Class.cv (nb090AlphaDummy431 A))
                  (synCun (synCphi (Class.cv (nb090AlphaDummy432 A)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb090AlphaDummy424 A) ≠ (nb090AlphaDummy431 A) from (by
          unfold nb090AlphaDummy431;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0464 A) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb090AlphaDummy424 A) ≠ (nb090AlphaDummy432 A) from (by
            unfold nb090AlphaDummy432;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0464 A) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb090_support_mem_0466 (h : Var) :
    (nb090AlphaDummy427 h) ∈
      (((Class.cv (nb090AlphaDummy426 h))).fv ∪ ((Class.cv (nb090AlphaDummy427 h))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0467 (h : Var) :
    (nb090AlphaDummy427 h) ∈
      (((synCcompl (Class.cab (nb090AlphaDummy433 h)
              (synWrex (nb090AlphaDummy434 h) (Class.cv (nb090AlphaDummy426 h))
                (Wff.classEq (Class.cv (nb090AlphaDummy433 h))
                  (synCphi (Class.cv (nb090AlphaDummy434 h)))))))).fv ∪ ((synCcompl
            (Class.cab (nb090AlphaDummy433 h)
              (synWrex (nb090AlphaDummy434 h) (Class.cv (nb090AlphaDummy427 h))
                (Wff.classEq (Class.cv (nb090AlphaDummy433 h))
                  (synCun (synCphi (Class.cv (nb090AlphaDummy434 h)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb090AlphaDummy427 h) ≠ (nb090AlphaDummy433 h) from (by
          unfold nb090AlphaDummy433;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0466 h) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb090AlphaDummy427 h) ≠ (nb090AlphaDummy434 h) from (by
            unfold nb090AlphaDummy434;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0466 h) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb090_support_mem_0468 (A : Class) :
    (nb090AlphaDummy424 A) ∈
      (((Class.cab (nb090AlphaDummy431 A)
            (synWrex (nb090AlphaDummy432 A) (Class.cv (nb090AlphaDummy424 A))
              (Wff.classEq (Class.cv (nb090AlphaDummy431 A))
                (synCun (synCphi (Class.cv (nb090AlphaDummy432 A)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb090AlphaDummy431 A)
            (synWrex (nb090AlphaDummy432 A) (Class.cv (nb090AlphaDummy424 A))
              (Wff.classEq (Class.cv (nb090AlphaDummy431 A))
                (synCun (synCphi (Class.cv (nb090AlphaDummy432 A)))
                  (synCsn (synC0c))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb090AlphaDummy424 A) ≠ (nb090AlphaDummy431 A) from (by
          unfold nb090AlphaDummy431;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0464 A) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb090AlphaDummy424 A) ≠ (nb090AlphaDummy432 A) from (by
            unfold nb090AlphaDummy432;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0464 A) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb090_support_mem_0469 (h : Var) :
    (nb090AlphaDummy427 h) ∈
      (((Class.cab (nb090AlphaDummy433 h)
            (synWrex (nb090AlphaDummy434 h) (Class.cv (nb090AlphaDummy427 h))
              (Wff.classEq (Class.cv (nb090AlphaDummy433 h))
                (synCun (synCphi (Class.cv (nb090AlphaDummy434 h)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb090AlphaDummy433 h)
            (synWrex (nb090AlphaDummy434 h) (Class.cv (nb090AlphaDummy427 h))
              (Wff.classEq (Class.cv (nb090AlphaDummy433 h))
                (synCun (synCphi (Class.cv (nb090AlphaDummy434 h)))
                  (synCsn (synC0c))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb090AlphaDummy427 h) ≠ (nb090AlphaDummy433 h) from (by
          unfold nb090AlphaDummy433;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0466 h) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb090AlphaDummy427 h) ≠ (nb090AlphaDummy434 h) from (by
            unfold nb090AlphaDummy434;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0466 h) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb090_support_mem_0470 (A : Class) :
    (nb090AlphaDummy432 A) ∈
      (((synCcompl (synCphi (Class.cv (nb090AlphaDummy432 A))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0471 (h : Var) :
    (nb090AlphaDummy434 h) ∈
      (((synCcompl (synCphi (Class.cv (nb090AlphaDummy434 h))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0472 (A : Class) :
    (nb090AlphaDummy432 A) ∈
      (((synCphi (Class.cv (nb090AlphaDummy432 A)))).fv ∪
        ((synCphi (Class.cv (nb090AlphaDummy432 A)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0473 (h : Var) :
    (nb090AlphaDummy434 h) ∈
      (((synCphi (Class.cv (nb090AlphaDummy434 h)))).fv ∪
        ((synCphi (Class.cv (nb090AlphaDummy434 h)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0474 (A : Class) :
    (nb090AlphaDummy423 A) ∈
      (((Class.cv (nb090AlphaDummy423 A))).fv ∪ ((Class.cv (nb090AlphaDummy425 A))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0475 (A : Class) :
    (nb090AlphaDummy423 A) ∈
      (((synCcompl (Class.cab (nb090AlphaDummy467 A)
              (synWrex (nb090AlphaDummy468 A) (Class.cv (nb090AlphaDummy423 A))
                (Wff.classEq (Class.cv (nb090AlphaDummy467 A))
                  (synCphi (Class.cv (nb090AlphaDummy468 A)))))))).fv ∪ ((synCcompl
            (Class.cab (nb090AlphaDummy467 A)
              (synWrex (nb090AlphaDummy468 A) (Class.cv (nb090AlphaDummy425 A))
                (Wff.classEq (Class.cv (nb090AlphaDummy467 A))
                  (synCun (synCphi (Class.cv (nb090AlphaDummy468 A)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb090AlphaDummy423 A) ≠ (nb090AlphaDummy467 A) from (by
          unfold nb090AlphaDummy467;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0474 A) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb090AlphaDummy423 A) ≠ (nb090AlphaDummy468 A) from (by
            unfold nb090AlphaDummy468;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0474 A) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb090_support_mem_0476 (h : Var) :
    (nb090AlphaDummy426 h) ∈
      (((Class.cv (nb090AlphaDummy426 h))).fv ∪ ((Class.cv (nb090AlphaDummy428 h))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0477 (h : Var) :
    (nb090AlphaDummy426 h) ∈
      (((synCcompl (Class.cab (nb090AlphaDummy469 h)
              (synWrex (nb090AlphaDummy470 h) (Class.cv (nb090AlphaDummy426 h))
                (Wff.classEq (Class.cv (nb090AlphaDummy469 h))
                  (synCphi (Class.cv (nb090AlphaDummy470 h)))))))).fv ∪ ((synCcompl
            (Class.cab (nb090AlphaDummy469 h)
              (synWrex (nb090AlphaDummy470 h) (Class.cv (nb090AlphaDummy428 h))
                (Wff.classEq (Class.cv (nb090AlphaDummy469 h))
                  (synCun (synCphi (Class.cv (nb090AlphaDummy470 h)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb090AlphaDummy426 h) ≠ (nb090AlphaDummy469 h) from (by
          unfold nb090AlphaDummy469;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0476 h) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb090AlphaDummy426 h) ≠ (nb090AlphaDummy470 h) from (by
            unfold nb090AlphaDummy470;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0476 h) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb090_support_mem_0478 (A : Class) :
    (nb090AlphaDummy423 A) ∈
      (((Class.cab (nb090AlphaDummy467 A)
            (synWrex (nb090AlphaDummy468 A) (Class.cv (nb090AlphaDummy423 A))
              (Wff.classEq (Class.cv (nb090AlphaDummy467 A))
                (synCphi (Class.cv (nb090AlphaDummy468 A))))))).fv ∪
        ((Class.cab (nb090AlphaDummy467 A)
            (synWrex (nb090AlphaDummy468 A) (Class.cv (nb090AlphaDummy423 A))
              (Wff.classEq (Class.cv (nb090AlphaDummy467 A))
                (synCphi (Class.cv (nb090AlphaDummy468 A))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb090AlphaDummy423 A) ≠ (nb090AlphaDummy467 A) from (by
          unfold nb090AlphaDummy467;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0474 A) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb090AlphaDummy423 A) ≠ (nb090AlphaDummy468 A) from (by
            unfold nb090AlphaDummy468;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0474 A) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb090_support_mem_0479 (h : Var) :
    (nb090AlphaDummy426 h) ∈
      (((Class.cab (nb090AlphaDummy469 h)
            (synWrex (nb090AlphaDummy470 h) (Class.cv (nb090AlphaDummy426 h))
              (Wff.classEq (Class.cv (nb090AlphaDummy469 h))
                (synCphi (Class.cv (nb090AlphaDummy470 h))))))).fv ∪
        ((Class.cab (nb090AlphaDummy469 h)
            (synWrex (nb090AlphaDummy470 h) (Class.cv (nb090AlphaDummy426 h))
              (Wff.classEq (Class.cv (nb090AlphaDummy469 h))
                (synCphi (Class.cv (nb090AlphaDummy470 h))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb090AlphaDummy426 h) ≠ (nb090AlphaDummy469 h) from (by
          unfold nb090AlphaDummy469;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0476 h) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb090AlphaDummy426 h) ≠ (nb090AlphaDummy470 h) from (by
            unfold nb090AlphaDummy470;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0476 h) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb090_support_mem_0480 (A : Class) :
    (nb090AlphaDummy468 A) ∈ (((Class.cv (nb090AlphaDummy468 A))).fv) :=
  by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0481 (h : Var) :
    (nb090AlphaDummy470 h) ∈ (((Class.cv (nb090AlphaDummy470 h))).fv) :=
  by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0482 (A : Class) :
    (nb090AlphaDummy475 A) ∈
      (((Wff.classMem (Class.cv (nb090AlphaDummy475 A)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb090AlphaDummy475 A)) (synC1c))).fv ∪
        ((Class.cv (nb090AlphaDummy475 A))).fv) :=
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

theorem nb090_support_mem_0483 (h : Var) :
    (nb090AlphaDummy477 h) ∈
      (((Wff.classMem (Class.cv (nb090AlphaDummy477 h)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb090AlphaDummy477 h)) (synC1c))).fv ∪
        ((Class.cv (nb090AlphaDummy477 h))).fv) :=
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

theorem nb090_support_mem_0484 (A : Class) :
    (nb090AlphaDummy475 A) ∈
      (((Class.cv (nb090AlphaDummy475 A))).fv ∪ ((synC1c)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0485 (h : Var) :
    (nb090AlphaDummy477 h) ∈
      (((Class.cv (nb090AlphaDummy477 h))).fv ∪ ((synC1c)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0486 (A : Class) :
    (nb090AlphaDummy482 A) ∈
      (((synCnin (Class.cv (nb090AlphaDummy482 A))
            (Class.cv (nb090AlphaDummy483 A)))).fv ∪
        ((synCnin (Class.cv (nb090AlphaDummy482 A))
            (Class.cv (nb090AlphaDummy483 A)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0487 (h : Var) :
    (nb090AlphaDummy485 h) ∈
      (((synCnin (Class.cv (nb090AlphaDummy485 h))
            (Class.cv (nb090AlphaDummy486 h)))).fv ∪
        ((synCnin (Class.cv (nb090AlphaDummy485 h))
            (Class.cv (nb090AlphaDummy486 h)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0488 (A : Class) :
    (nb090AlphaDummy482 A) ∈
      (((Class.cv (nb090AlphaDummy482 A))).fv ∪ ((Class.cv (nb090AlphaDummy483 A))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0489 (h : Var) :
    (nb090AlphaDummy485 h) ∈
      (((Class.cv (nb090AlphaDummy485 h))).fv ∪ ((Class.cv (nb090AlphaDummy486 h))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0490 (A : Class) :
    (nb090AlphaDummy483 A) ∈
      (((synCnin (Class.cv (nb090AlphaDummy482 A))
            (Class.cv (nb090AlphaDummy483 A)))).fv ∪
        ((synCnin (Class.cv (nb090AlphaDummy482 A))
            (Class.cv (nb090AlphaDummy483 A)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0491 (h : Var) :
    (nb090AlphaDummy486 h) ∈
      (((synCnin (Class.cv (nb090AlphaDummy485 h))
            (Class.cv (nb090AlphaDummy486 h)))).fv ∪
        ((synCnin (Class.cv (nb090AlphaDummy485 h))
            (Class.cv (nb090AlphaDummy486 h)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0492 (A : Class) :
    (nb090AlphaDummy483 A) ∈
      (((Class.cv (nb090AlphaDummy482 A))).fv ∪ ((Class.cv (nb090AlphaDummy483 A))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0493 (h : Var) :
    (nb090AlphaDummy486 h) ∈
      (((Class.cv (nb090AlphaDummy485 h))).fv ∪ ((Class.cv (nb090AlphaDummy486 h))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0494 (A : Class) :
    (nb090AlphaDummy482 A) ∈
      (((synCcompl (Class.cv (nb090AlphaDummy482 A)))).fv ∪
        ((synCcompl (Class.cv (nb090AlphaDummy483 A)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0495 (h : Var) :
    (nb090AlphaDummy485 h) ∈
      (((synCcompl (Class.cv (nb090AlphaDummy485 h)))).fv ∪
        ((synCcompl (Class.cv (nb090AlphaDummy486 h)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0496 (A : Class) :
    (nb090AlphaDummy482 A) ∈
      (((Class.cv (nb090AlphaDummy482 A))).fv ∪ ((Class.cv (nb090AlphaDummy482 A))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired

end

/-! Certificates from `NAR4C090C001Part019`. -/


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

theorem nb090_support_mem_0497 (h : Var) :
    (nb090AlphaDummy485 h) ∈
      (((Class.cv (nb090AlphaDummy485 h))).fv ∪ ((Class.cv (nb090AlphaDummy485 h))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0498 (A : Class) :
    (nb090AlphaDummy483 A) ∈
      (((synCcompl (Class.cv (nb090AlphaDummy482 A)))).fv ∪
        ((synCcompl (Class.cv (nb090AlphaDummy483 A)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0499 (h : Var) :
    (nb090AlphaDummy486 h) ∈
      (((synCcompl (Class.cv (nb090AlphaDummy485 h)))).fv ∪
        ((synCcompl (Class.cv (nb090AlphaDummy486 h)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0500 (A : Class) :
    (nb090AlphaDummy483 A) ∈
      (((Class.cv (nb090AlphaDummy483 A))).fv ∪ ((Class.cv (nb090AlphaDummy483 A))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0501 (h : Var) :
    (nb090AlphaDummy486 h) ∈
      (((Class.cv (nb090AlphaDummy486 h))).fv ∪ ((Class.cv (nb090AlphaDummy486 h))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0502 (A : Class) :
    (nb090AlphaDummy425 A) ∈
      (((Class.cv (nb090AlphaDummy423 A))).fv ∪ ((Class.cv (nb090AlphaDummy425 A))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0503 (A : Class) :
    (nb090AlphaDummy425 A) ∈
      (((synCcompl (Class.cab (nb090AlphaDummy467 A)
              (synWrex (nb090AlphaDummy468 A) (Class.cv (nb090AlphaDummy423 A))
                (Wff.classEq (Class.cv (nb090AlphaDummy467 A))
                  (synCphi (Class.cv (nb090AlphaDummy468 A)))))))).fv ∪ ((synCcompl
            (Class.cab (nb090AlphaDummy467 A)
              (synWrex (nb090AlphaDummy468 A) (Class.cv (nb090AlphaDummy425 A))
                (Wff.classEq (Class.cv (nb090AlphaDummy467 A))
                  (synCun (synCphi (Class.cv (nb090AlphaDummy468 A)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb090AlphaDummy425 A) ≠ (nb090AlphaDummy467 A) from (by
          unfold nb090AlphaDummy467;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0502 A) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb090AlphaDummy425 A) ≠ (nb090AlphaDummy468 A) from (by
            unfold nb090AlphaDummy468;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0502 A) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb090_support_mem_0504 (h : Var) :
    (nb090AlphaDummy428 h) ∈
      (((Class.cv (nb090AlphaDummy426 h))).fv ∪ ((Class.cv (nb090AlphaDummy428 h))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0505 (h : Var) :
    (nb090AlphaDummy428 h) ∈
      (((synCcompl (Class.cab (nb090AlphaDummy469 h)
              (synWrex (nb090AlphaDummy470 h) (Class.cv (nb090AlphaDummy426 h))
                (Wff.classEq (Class.cv (nb090AlphaDummy469 h))
                  (synCphi (Class.cv (nb090AlphaDummy470 h)))))))).fv ∪ ((synCcompl
            (Class.cab (nb090AlphaDummy469 h)
              (synWrex (nb090AlphaDummy470 h) (Class.cv (nb090AlphaDummy428 h))
                (Wff.classEq (Class.cv (nb090AlphaDummy469 h))
                  (synCun (synCphi (Class.cv (nb090AlphaDummy470 h)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb090AlphaDummy428 h) ≠ (nb090AlphaDummy469 h) from (by
          unfold nb090AlphaDummy469;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0504 h) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb090AlphaDummy428 h) ≠ (nb090AlphaDummy470 h) from (by
            unfold nb090AlphaDummy470;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0504 h) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb090_support_mem_0506 (A : Class) :
    (nb090AlphaDummy425 A) ∈
      (((Class.cab (nb090AlphaDummy467 A)
            (synWrex (nb090AlphaDummy468 A) (Class.cv (nb090AlphaDummy425 A))
              (Wff.classEq (Class.cv (nb090AlphaDummy467 A))
                (synCun (synCphi (Class.cv (nb090AlphaDummy468 A)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb090AlphaDummy467 A)
            (synWrex (nb090AlphaDummy468 A) (Class.cv (nb090AlphaDummy425 A))
              (Wff.classEq (Class.cv (nb090AlphaDummy467 A))
                (synCun (synCphi (Class.cv (nb090AlphaDummy468 A)))
                  (synCsn (synC0c))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb090AlphaDummy425 A) ≠ (nb090AlphaDummy467 A) from (by
          unfold nb090AlphaDummy467;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0502 A) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb090AlphaDummy425 A) ≠ (nb090AlphaDummy468 A) from (by
            unfold nb090AlphaDummy468;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0502 A) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb090_support_mem_0507 (h : Var) :
    (nb090AlphaDummy428 h) ∈
      (((Class.cab (nb090AlphaDummy469 h)
            (synWrex (nb090AlphaDummy470 h) (Class.cv (nb090AlphaDummy428 h))
              (Wff.classEq (Class.cv (nb090AlphaDummy469 h))
                (synCun (synCphi (Class.cv (nb090AlphaDummy470 h)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb090AlphaDummy469 h)
            (synWrex (nb090AlphaDummy470 h) (Class.cv (nb090AlphaDummy428 h))
              (Wff.classEq (Class.cv (nb090AlphaDummy469 h))
                (synCun (synCphi (Class.cv (nb090AlphaDummy470 h)))
                  (synCsn (synC0c))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb090AlphaDummy428 h) ≠ (nb090AlphaDummy469 h) from (by
          unfold nb090AlphaDummy469;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0504 h) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb090AlphaDummy428 h) ≠ (nb090AlphaDummy470 h) from (by
            unfold nb090AlphaDummy470;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0504 h) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb090_support_mem_0508 (A : Class) :
    (nb090AlphaDummy468 A) ∈
      (((synCcompl (synCphi (Class.cv (nb090AlphaDummy468 A))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0509 (h : Var) :
    (nb090AlphaDummy470 h) ∈
      (((synCcompl (synCphi (Class.cv (nb090AlphaDummy470 h))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0510 (A : Class) :
    (nb090AlphaDummy468 A) ∈
      (((synCphi (Class.cv (nb090AlphaDummy468 A)))).fv ∪
        ((synCphi (Class.cv (nb090AlphaDummy468 A)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0511 (h : Var) :
    (nb090AlphaDummy470 h) ∈
      (((synCphi (Class.cv (nb090AlphaDummy470 h)))).fv ∪
        ((synCphi (Class.cv (nb090AlphaDummy470 h)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0512 (A : Class) :
    (nb090AlphaDummy503 A) ∈
      (({(nb090AlphaDummy503 A)} : Finset Var) ∪ ({(nb090AlphaDummy504 A)} : Finset Var) ∪
        ((synWbr (Class.cv (nb090AlphaDummy504 A))
            (synCcnv (Class.cv (nb090AlphaDummy000 A)))
            (Class.cv (nb090AlphaDummy503 A)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  with_reducible rw [Finset.mem_union]
  left
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0513 (h : Var) :
    (nb090AlphaDummy505 h) ∈
      (({(nb090AlphaDummy505 h)} : Finset Var) ∪ ({(nb090AlphaDummy506 h)} : Finset Var) ∪
        ((synWbr (Class.cv (nb090AlphaDummy506 h)) (synCcnv (Class.cv h))
            (Class.cv (nb090AlphaDummy505 h)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  with_reducible rw [Finset.mem_union]
  left
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0514 (A : Class) :
    (nb090AlphaDummy504 A) ∈
      (({(nb090AlphaDummy503 A)} : Finset Var) ∪ ({(nb090AlphaDummy504 A)} : Finset Var) ∪
        ((synWbr (Class.cv (nb090AlphaDummy504 A))
            (synCcnv (Class.cv (nb090AlphaDummy000 A)))
            (Class.cv (nb090AlphaDummy503 A)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  with_reducible rw [Finset.mem_union]
  right
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0515 (h : Var) :
    (nb090AlphaDummy506 h) ∈
      (({(nb090AlphaDummy505 h)} : Finset Var) ∪ ({(nb090AlphaDummy506 h)} : Finset Var) ∪
        ((synWbr (Class.cv (nb090AlphaDummy506 h)) (synCcnv (Class.cv h))
            (Class.cv (nb090AlphaDummy505 h)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  with_reducible rw [Finset.mem_union]
  right
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0516 (A : Class) :
    (nb090AlphaDummy503 A) ∈
      (((Class.cv (nb090AlphaDummy503 A))).fv ∪ ((Class.cv (nb090AlphaDummy504 A))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0517 (A : Class) :
    (nb090AlphaDummy503 A) ∈
      (((synCcompl (Class.cab (nb090AlphaDummy509 A)
              (synWrex (nb090AlphaDummy510 A) (Class.cv (nb090AlphaDummy503 A))
                (Wff.classEq (Class.cv (nb090AlphaDummy509 A))
                  (synCphi (Class.cv (nb090AlphaDummy510 A)))))))).fv ∪ ((synCcompl
            (Class.cab (nb090AlphaDummy509 A)
              (synWrex (nb090AlphaDummy510 A) (Class.cv (nb090AlphaDummy504 A))
                (Wff.classEq (Class.cv (nb090AlphaDummy509 A))
                  (synCun (synCphi (Class.cv (nb090AlphaDummy510 A)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb090AlphaDummy503 A) ≠ (nb090AlphaDummy509 A) from (by
          unfold nb090AlphaDummy509;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0516 A) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb090AlphaDummy503 A) ≠ (nb090AlphaDummy510 A) from (by
            unfold nb090AlphaDummy510;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0516 A) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb090_support_mem_0518 (h : Var) :
    (nb090AlphaDummy505 h) ∈
      (((Class.cv (nb090AlphaDummy505 h))).fv ∪ ((Class.cv (nb090AlphaDummy506 h))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0519 (h : Var) :
    (nb090AlphaDummy505 h) ∈
      (((synCcompl (Class.cab (nb090AlphaDummy511 h)
              (synWrex (nb090AlphaDummy512 h) (Class.cv (nb090AlphaDummy505 h))
                (Wff.classEq (Class.cv (nb090AlphaDummy511 h))
                  (synCphi (Class.cv (nb090AlphaDummy512 h)))))))).fv ∪ ((synCcompl
            (Class.cab (nb090AlphaDummy511 h)
              (synWrex (nb090AlphaDummy512 h) (Class.cv (nb090AlphaDummy506 h))
                (Wff.classEq (Class.cv (nb090AlphaDummy511 h))
                  (synCun (synCphi (Class.cv (nb090AlphaDummy512 h)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb090AlphaDummy505 h) ≠ (nb090AlphaDummy511 h) from (by
          unfold nb090AlphaDummy511;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0518 h) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb090AlphaDummy505 h) ≠ (nb090AlphaDummy512 h) from (by
            unfold nb090AlphaDummy512;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0518 h) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb090_support_mem_0520 (A : Class) :
    (nb090AlphaDummy503 A) ∈
      (((Class.cab (nb090AlphaDummy509 A)
            (synWrex (nb090AlphaDummy510 A) (Class.cv (nb090AlphaDummy503 A))
              (Wff.classEq (Class.cv (nb090AlphaDummy509 A))
                (synCphi (Class.cv (nb090AlphaDummy510 A))))))).fv ∪
        ((Class.cab (nb090AlphaDummy509 A)
            (synWrex (nb090AlphaDummy510 A) (Class.cv (nb090AlphaDummy503 A))
              (Wff.classEq (Class.cv (nb090AlphaDummy509 A))
                (synCphi (Class.cv (nb090AlphaDummy510 A))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb090AlphaDummy503 A) ≠ (nb090AlphaDummy509 A) from (by
          unfold nb090AlphaDummy509;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0516 A) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb090AlphaDummy503 A) ≠ (nb090AlphaDummy510 A) from (by
            unfold nb090AlphaDummy510;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0516 A) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb090_support_mem_0521 (h : Var) :
    (nb090AlphaDummy505 h) ∈
      (((Class.cab (nb090AlphaDummy511 h)
            (synWrex (nb090AlphaDummy512 h) (Class.cv (nb090AlphaDummy505 h))
              (Wff.classEq (Class.cv (nb090AlphaDummy511 h))
                (synCphi (Class.cv (nb090AlphaDummy512 h))))))).fv ∪
        ((Class.cab (nb090AlphaDummy511 h)
            (synWrex (nb090AlphaDummy512 h) (Class.cv (nb090AlphaDummy505 h))
              (Wff.classEq (Class.cv (nb090AlphaDummy511 h))
                (synCphi (Class.cv (nb090AlphaDummy512 h))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb090AlphaDummy505 h) ≠ (nb090AlphaDummy511 h) from (by
          unfold nb090AlphaDummy511;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0518 h) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb090AlphaDummy505 h) ≠ (nb090AlphaDummy512 h) from (by
            unfold nb090AlphaDummy512;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0518 h) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb090_support_mem_0522 (A : Class) :
    (nb090AlphaDummy510 A) ∈ (((Class.cv (nb090AlphaDummy510 A))).fv) :=
  by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0523 (h : Var) :
    (nb090AlphaDummy512 h) ∈ (((Class.cv (nb090AlphaDummy512 h))).fv) :=
  by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0524 (A : Class) :
    (nb090AlphaDummy517 A) ∈
      (((Wff.classMem (Class.cv (nb090AlphaDummy517 A)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb090AlphaDummy517 A)) (synC1c))).fv ∪
        ((Class.cv (nb090AlphaDummy517 A))).fv) :=
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

theorem nb090_support_mem_0525 (h : Var) :
    (nb090AlphaDummy519 h) ∈
      (((Wff.classMem (Class.cv (nb090AlphaDummy519 h)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb090AlphaDummy519 h)) (synC1c))).fv ∪
        ((Class.cv (nb090AlphaDummy519 h))).fv) :=
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

theorem nb090_support_mem_0526 (A : Class) :
    (nb090AlphaDummy517 A) ∈
      (((Class.cv (nb090AlphaDummy517 A))).fv ∪ ((synC1c)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0527 (h : Var) :
    (nb090AlphaDummy519 h) ∈
      (((Class.cv (nb090AlphaDummy519 h))).fv ∪ ((synC1c)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0528 (A : Class) :
    (nb090AlphaDummy524 A) ∈
      (((synCnin (Class.cv (nb090AlphaDummy524 A))
            (Class.cv (nb090AlphaDummy525 A)))).fv ∪
        ((synCnin (Class.cv (nb090AlphaDummy524 A))
            (Class.cv (nb090AlphaDummy525 A)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0529 (h : Var) :
    (nb090AlphaDummy527 h) ∈
      (((synCnin (Class.cv (nb090AlphaDummy527 h))
            (Class.cv (nb090AlphaDummy528 h)))).fv ∪
        ((synCnin (Class.cv (nb090AlphaDummy527 h))
            (Class.cv (nb090AlphaDummy528 h)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0530 (A : Class) :
    (nb090AlphaDummy524 A) ∈
      (((Class.cv (nb090AlphaDummy524 A))).fv ∪ ((Class.cv (nb090AlphaDummy525 A))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0531 (h : Var) :
    (nb090AlphaDummy527 h) ∈
      (((Class.cv (nb090AlphaDummy527 h))).fv ∪ ((Class.cv (nb090AlphaDummy528 h))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0532 (A : Class) :
    (nb090AlphaDummy525 A) ∈
      (((synCnin (Class.cv (nb090AlphaDummy524 A))
            (Class.cv (nb090AlphaDummy525 A)))).fv ∪
        ((synCnin (Class.cv (nb090AlphaDummy524 A))
            (Class.cv (nb090AlphaDummy525 A)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0533 (h : Var) :
    (nb090AlphaDummy528 h) ∈
      (((synCnin (Class.cv (nb090AlphaDummy527 h))
            (Class.cv (nb090AlphaDummy528 h)))).fv ∪
        ((synCnin (Class.cv (nb090AlphaDummy527 h))
            (Class.cv (nb090AlphaDummy528 h)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0534 (A : Class) :
    (nb090AlphaDummy525 A) ∈
      (((Class.cv (nb090AlphaDummy524 A))).fv ∪ ((Class.cv (nb090AlphaDummy525 A))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0535 (h : Var) :
    (nb090AlphaDummy528 h) ∈
      (((Class.cv (nb090AlphaDummy527 h))).fv ∪ ((Class.cv (nb090AlphaDummy528 h))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0536 (A : Class) :
    (nb090AlphaDummy524 A) ∈
      (((synCcompl (Class.cv (nb090AlphaDummy524 A)))).fv ∪
        ((synCcompl (Class.cv (nb090AlphaDummy525 A)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0537 (h : Var) :
    (nb090AlphaDummy527 h) ∈
      (((synCcompl (Class.cv (nb090AlphaDummy527 h)))).fv ∪
        ((synCcompl (Class.cv (nb090AlphaDummy528 h)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0538 (A : Class) :
    (nb090AlphaDummy524 A) ∈
      (((Class.cv (nb090AlphaDummy524 A))).fv ∪ ((Class.cv (nb090AlphaDummy524 A))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0539 (h : Var) :
    (nb090AlphaDummy527 h) ∈
      (((Class.cv (nb090AlphaDummy527 h))).fv ∪ ((Class.cv (nb090AlphaDummy527 h))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0540 (A : Class) :
    (nb090AlphaDummy525 A) ∈
      (((synCcompl (Class.cv (nb090AlphaDummy524 A)))).fv ∪
        ((synCcompl (Class.cv (nb090AlphaDummy525 A)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0541 (h : Var) :
    (nb090AlphaDummy528 h) ∈
      (((synCcompl (Class.cv (nb090AlphaDummy527 h)))).fv ∪
        ((synCcompl (Class.cv (nb090AlphaDummy528 h)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0542 (A : Class) :
    (nb090AlphaDummy525 A) ∈
      (((Class.cv (nb090AlphaDummy525 A))).fv ∪ ((Class.cv (nb090AlphaDummy525 A))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0543 (h : Var) :
    (nb090AlphaDummy528 h) ∈
      (((Class.cv (nb090AlphaDummy528 h))).fv ∪ ((Class.cv (nb090AlphaDummy528 h))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0544 (A : Class) :
    (nb090AlphaDummy504 A) ∈
      (((Class.cv (nb090AlphaDummy503 A))).fv ∪ ((Class.cv (nb090AlphaDummy504 A))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0545 (A : Class) :
    (nb090AlphaDummy504 A) ∈
      (((synCcompl (Class.cab (nb090AlphaDummy509 A)
              (synWrex (nb090AlphaDummy510 A) (Class.cv (nb090AlphaDummy503 A))
                (Wff.classEq (Class.cv (nb090AlphaDummy509 A))
                  (synCphi (Class.cv (nb090AlphaDummy510 A)))))))).fv ∪ ((synCcompl
            (Class.cab (nb090AlphaDummy509 A)
              (synWrex (nb090AlphaDummy510 A) (Class.cv (nb090AlphaDummy504 A))
                (Wff.classEq (Class.cv (nb090AlphaDummy509 A))
                  (synCun (synCphi (Class.cv (nb090AlphaDummy510 A)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb090AlphaDummy504 A) ≠ (nb090AlphaDummy509 A) from (by
          unfold nb090AlphaDummy509;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0544 A) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb090AlphaDummy504 A) ≠ (nb090AlphaDummy510 A) from (by
            unfold nb090AlphaDummy510;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0544 A) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb090_support_mem_0546 (h : Var) :
    (nb090AlphaDummy506 h) ∈
      (((Class.cv (nb090AlphaDummy505 h))).fv ∪ ((Class.cv (nb090AlphaDummy506 h))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0547 (h : Var) :
    (nb090AlphaDummy506 h) ∈
      (((synCcompl (Class.cab (nb090AlphaDummy511 h)
              (synWrex (nb090AlphaDummy512 h) (Class.cv (nb090AlphaDummy505 h))
                (Wff.classEq (Class.cv (nb090AlphaDummy511 h))
                  (synCphi (Class.cv (nb090AlphaDummy512 h)))))))).fv ∪ ((synCcompl
            (Class.cab (nb090AlphaDummy511 h)
              (synWrex (nb090AlphaDummy512 h) (Class.cv (nb090AlphaDummy506 h))
                (Wff.classEq (Class.cv (nb090AlphaDummy511 h))
                  (synCun (synCphi (Class.cv (nb090AlphaDummy512 h)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb090AlphaDummy506 h) ≠ (nb090AlphaDummy511 h) from (by
          unfold nb090AlphaDummy511;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0546 h) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb090AlphaDummy506 h) ≠ (nb090AlphaDummy512 h) from (by
            unfold nb090AlphaDummy512;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0546 h) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb090_support_mem_0548 (A : Class) :
    (nb090AlphaDummy504 A) ∈
      (((Class.cab (nb090AlphaDummy509 A)
            (synWrex (nb090AlphaDummy510 A) (Class.cv (nb090AlphaDummy504 A))
              (Wff.classEq (Class.cv (nb090AlphaDummy509 A))
                (synCun (synCphi (Class.cv (nb090AlphaDummy510 A)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb090AlphaDummy509 A)
            (synWrex (nb090AlphaDummy510 A) (Class.cv (nb090AlphaDummy504 A))
              (Wff.classEq (Class.cv (nb090AlphaDummy509 A))
                (synCun (synCphi (Class.cv (nb090AlphaDummy510 A)))
                  (synCsn (synC0c))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb090AlphaDummy504 A) ≠ (nb090AlphaDummy509 A) from (by
          unfold nb090AlphaDummy509;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0544 A) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb090AlphaDummy504 A) ≠ (nb090AlphaDummy510 A) from (by
            unfold nb090AlphaDummy510;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0544 A) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb090_support_mem_0549 (h : Var) :
    (nb090AlphaDummy506 h) ∈
      (((Class.cab (nb090AlphaDummy511 h)
            (synWrex (nb090AlphaDummy512 h) (Class.cv (nb090AlphaDummy506 h))
              (Wff.classEq (Class.cv (nb090AlphaDummy511 h))
                (synCun (synCphi (Class.cv (nb090AlphaDummy512 h)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb090AlphaDummy511 h)
            (synWrex (nb090AlphaDummy512 h) (Class.cv (nb090AlphaDummy506 h))
              (Wff.classEq (Class.cv (nb090AlphaDummy511 h))
                (synCun (synCphi (Class.cv (nb090AlphaDummy512 h)))
                  (synCsn (synC0c))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb090AlphaDummy506 h) ≠ (nb090AlphaDummy511 h) from (by
          unfold nb090AlphaDummy511;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0546 h) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb090AlphaDummy506 h) ≠ (nb090AlphaDummy512 h) from (by
            unfold nb090AlphaDummy512;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0546 h) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb090_support_mem_0550 (A : Class) :
    (nb090AlphaDummy510 A) ∈
      (((synCcompl (synCphi (Class.cv (nb090AlphaDummy510 A))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0551 (h : Var) :
    (nb090AlphaDummy512 h) ∈
      (((synCcompl (synCphi (Class.cv (nb090AlphaDummy512 h))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0552 (A : Class) :
    (nb090AlphaDummy510 A) ∈
      (((synCphi (Class.cv (nb090AlphaDummy510 A)))).fv ∪
        ((synCphi (Class.cv (nb090AlphaDummy510 A)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0553 (h : Var) :
    (nb090AlphaDummy512 h) ∈
      (((synCphi (Class.cv (nb090AlphaDummy512 h)))).fv ∪
        ((synCphi (Class.cv (nb090AlphaDummy512 h)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0554 (A : Class) :
    (nb090AlphaDummy504 A) ∈
      (((Class.cv (nb090AlphaDummy504 A))).fv ∪ ((Class.cv (nb090AlphaDummy503 A))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0555 (A : Class) :
    (nb090AlphaDummy504 A) ∈
      (((synCcompl (Class.cab (nb090AlphaDummy545 A)
              (synWrex (nb090AlphaDummy546 A) (Class.cv (nb090AlphaDummy504 A))
                (Wff.classEq (Class.cv (nb090AlphaDummy545 A))
                  (synCphi (Class.cv (nb090AlphaDummy546 A)))))))).fv ∪ ((synCcompl
            (Class.cab (nb090AlphaDummy545 A)
              (synWrex (nb090AlphaDummy546 A) (Class.cv (nb090AlphaDummy503 A))
                (Wff.classEq (Class.cv (nb090AlphaDummy545 A))
                  (synCun (synCphi (Class.cv (nb090AlphaDummy546 A)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb090AlphaDummy504 A) ≠ (nb090AlphaDummy545 A) from (by
          unfold nb090AlphaDummy545;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0554 A) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb090AlphaDummy504 A) ≠ (nb090AlphaDummy546 A) from (by
            unfold nb090AlphaDummy546;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0554 A) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb090_support_mem_0556 (h : Var) :
    (nb090AlphaDummy506 h) ∈
      (((Class.cv (nb090AlphaDummy506 h))).fv ∪ ((Class.cv (nb090AlphaDummy505 h))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0557 (h : Var) :
    (nb090AlphaDummy506 h) ∈
      (((synCcompl (Class.cab (nb090AlphaDummy547 h)
              (synWrex (nb090AlphaDummy548 h) (Class.cv (nb090AlphaDummy506 h))
                (Wff.classEq (Class.cv (nb090AlphaDummy547 h))
                  (synCphi (Class.cv (nb090AlphaDummy548 h)))))))).fv ∪ ((synCcompl
            (Class.cab (nb090AlphaDummy547 h)
              (synWrex (nb090AlphaDummy548 h) (Class.cv (nb090AlphaDummy505 h))
                (Wff.classEq (Class.cv (nb090AlphaDummy547 h))
                  (synCun (synCphi (Class.cv (nb090AlphaDummy548 h)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb090AlphaDummy506 h) ≠ (nb090AlphaDummy547 h) from (by
          unfold nb090AlphaDummy547;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0556 h) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb090AlphaDummy506 h) ≠ (nb090AlphaDummy548 h) from (by
            unfold nb090AlphaDummy548;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0556 h) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb090_support_mem_0558 (A : Class) :
    (nb090AlphaDummy504 A) ∈
      (((Class.cab (nb090AlphaDummy545 A)
            (synWrex (nb090AlphaDummy546 A) (Class.cv (nb090AlphaDummy504 A))
              (Wff.classEq (Class.cv (nb090AlphaDummy545 A))
                (synCphi (Class.cv (nb090AlphaDummy546 A))))))).fv ∪
        ((Class.cab (nb090AlphaDummy545 A)
            (synWrex (nb090AlphaDummy546 A) (Class.cv (nb090AlphaDummy504 A))
              (Wff.classEq (Class.cv (nb090AlphaDummy545 A))
                (synCphi (Class.cv (nb090AlphaDummy546 A))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb090AlphaDummy504 A) ≠ (nb090AlphaDummy545 A) from (by
          unfold nb090AlphaDummy545;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0554 A) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb090AlphaDummy504 A) ≠ (nb090AlphaDummy546 A) from (by
            unfold nb090AlphaDummy546;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0554 A) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb090_support_mem_0559 (h : Var) :
    (nb090AlphaDummy506 h) ∈
      (((Class.cab (nb090AlphaDummy547 h)
            (synWrex (nb090AlphaDummy548 h) (Class.cv (nb090AlphaDummy506 h))
              (Wff.classEq (Class.cv (nb090AlphaDummy547 h))
                (synCphi (Class.cv (nb090AlphaDummy548 h))))))).fv ∪
        ((Class.cab (nb090AlphaDummy547 h)
            (synWrex (nb090AlphaDummy548 h) (Class.cv (nb090AlphaDummy506 h))
              (Wff.classEq (Class.cv (nb090AlphaDummy547 h))
                (synCphi (Class.cv (nb090AlphaDummy548 h))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb090AlphaDummy506 h) ≠ (nb090AlphaDummy547 h) from (by
          unfold nb090AlphaDummy547;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0556 h) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb090AlphaDummy506 h) ≠ (nb090AlphaDummy548 h) from (by
            unfold nb090AlphaDummy548;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0556 h) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb090_support_mem_0560 (A : Class) :
    (nb090AlphaDummy546 A) ∈ (((Class.cv (nb090AlphaDummy546 A))).fv) :=
  by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0561 (h : Var) :
    (nb090AlphaDummy548 h) ∈ (((Class.cv (nb090AlphaDummy548 h))).fv) :=
  by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0562 (A : Class) :
    (nb090AlphaDummy553 A) ∈
      (((Wff.classMem (Class.cv (nb090AlphaDummy553 A)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb090AlphaDummy553 A)) (synC1c))).fv ∪
        ((Class.cv (nb090AlphaDummy553 A))).fv) :=
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

theorem nb090_support_mem_0563 (h : Var) :
    (nb090AlphaDummy555 h) ∈
      (((Wff.classMem (Class.cv (nb090AlphaDummy555 h)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb090AlphaDummy555 h)) (synC1c))).fv ∪
        ((Class.cv (nb090AlphaDummy555 h))).fv) :=
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

theorem nb090_support_mem_0564 (A : Class) :
    (nb090AlphaDummy553 A) ∈
      (((Class.cv (nb090AlphaDummy553 A))).fv ∪ ((synC1c)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0565 (h : Var) :
    (nb090AlphaDummy555 h) ∈
      (((Class.cv (nb090AlphaDummy555 h))).fv ∪ ((synC1c)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0566 (A : Class) :
    (nb090AlphaDummy560 A) ∈
      (((synCnin (Class.cv (nb090AlphaDummy560 A))
            (Class.cv (nb090AlphaDummy561 A)))).fv ∪
        ((synCnin (Class.cv (nb090AlphaDummy560 A))
            (Class.cv (nb090AlphaDummy561 A)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0567 (h : Var) :
    (nb090AlphaDummy563 h) ∈
      (((synCnin (Class.cv (nb090AlphaDummy563 h))
            (Class.cv (nb090AlphaDummy564 h)))).fv ∪
        ((synCnin (Class.cv (nb090AlphaDummy563 h))
            (Class.cv (nb090AlphaDummy564 h)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0568 (A : Class) :
    (nb090AlphaDummy560 A) ∈
      (((Class.cv (nb090AlphaDummy560 A))).fv ∪ ((Class.cv (nb090AlphaDummy561 A))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0569 (h : Var) :
    (nb090AlphaDummy563 h) ∈
      (((Class.cv (nb090AlphaDummy563 h))).fv ∪ ((Class.cv (nb090AlphaDummy564 h))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0570 (A : Class) :
    (nb090AlphaDummy561 A) ∈
      (((synCnin (Class.cv (nb090AlphaDummy560 A))
            (Class.cv (nb090AlphaDummy561 A)))).fv ∪
        ((synCnin (Class.cv (nb090AlphaDummy560 A))
            (Class.cv (nb090AlphaDummy561 A)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0571 (h : Var) :
    (nb090AlphaDummy564 h) ∈
      (((synCnin (Class.cv (nb090AlphaDummy563 h))
            (Class.cv (nb090AlphaDummy564 h)))).fv ∪
        ((synCnin (Class.cv (nb090AlphaDummy563 h))
            (Class.cv (nb090AlphaDummy564 h)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0572 (A : Class) :
    (nb090AlphaDummy561 A) ∈
      (((Class.cv (nb090AlphaDummy560 A))).fv ∪ ((Class.cv (nb090AlphaDummy561 A))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0573 (h : Var) :
    (nb090AlphaDummy564 h) ∈
      (((Class.cv (nb090AlphaDummy563 h))).fv ∪ ((Class.cv (nb090AlphaDummy564 h))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0574 (A : Class) :
    (nb090AlphaDummy560 A) ∈
      (((synCcompl (Class.cv (nb090AlphaDummy560 A)))).fv ∪
        ((synCcompl (Class.cv (nb090AlphaDummy561 A)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0575 (h : Var) :
    (nb090AlphaDummy563 h) ∈
      (((synCcompl (Class.cv (nb090AlphaDummy563 h)))).fv ∪
        ((synCcompl (Class.cv (nb090AlphaDummy564 h)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0576 (A : Class) :
    (nb090AlphaDummy560 A) ∈
      (((Class.cv (nb090AlphaDummy560 A))).fv ∪ ((Class.cv (nb090AlphaDummy560 A))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0577 (h : Var) :
    (nb090AlphaDummy563 h) ∈
      (((Class.cv (nb090AlphaDummy563 h))).fv ∪ ((Class.cv (nb090AlphaDummy563 h))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0578 (A : Class) :
    (nb090AlphaDummy561 A) ∈
      (((synCcompl (Class.cv (nb090AlphaDummy560 A)))).fv ∪
        ((synCcompl (Class.cv (nb090AlphaDummy561 A)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0579 (h : Var) :
    (nb090AlphaDummy564 h) ∈
      (((synCcompl (Class.cv (nb090AlphaDummy563 h)))).fv ∪
        ((synCcompl (Class.cv (nb090AlphaDummy564 h)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0580 (A : Class) :
    (nb090AlphaDummy561 A) ∈
      (((Class.cv (nb090AlphaDummy561 A))).fv ∪ ((Class.cv (nb090AlphaDummy561 A))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0581 (h : Var) :
    (nb090AlphaDummy564 h) ∈
      (((Class.cv (nb090AlphaDummy564 h))).fv ∪ ((Class.cv (nb090AlphaDummy564 h))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0582 (A : Class) :
    (nb090AlphaDummy503 A) ∈
      (((Class.cv (nb090AlphaDummy504 A))).fv ∪ ((Class.cv (nb090AlphaDummy503 A))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0583 (A : Class) :
    (nb090AlphaDummy503 A) ∈
      (((synCcompl (Class.cab (nb090AlphaDummy545 A)
              (synWrex (nb090AlphaDummy546 A) (Class.cv (nb090AlphaDummy504 A))
                (Wff.classEq (Class.cv (nb090AlphaDummy545 A))
                  (synCphi (Class.cv (nb090AlphaDummy546 A)))))))).fv ∪ ((synCcompl
            (Class.cab (nb090AlphaDummy545 A)
              (synWrex (nb090AlphaDummy546 A) (Class.cv (nb090AlphaDummy503 A))
                (Wff.classEq (Class.cv (nb090AlphaDummy545 A))
                  (synCun (synCphi (Class.cv (nb090AlphaDummy546 A)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb090AlphaDummy503 A) ≠ (nb090AlphaDummy545 A) from (by
          unfold nb090AlphaDummy545;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0582 A) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb090AlphaDummy503 A) ≠ (nb090AlphaDummy546 A) from (by
            unfold nb090AlphaDummy546;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0582 A) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb090_support_mem_0584 (h : Var) :
    (nb090AlphaDummy505 h) ∈
      (((Class.cv (nb090AlphaDummy506 h))).fv ∪ ((Class.cv (nb090AlphaDummy505 h))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0585 (h : Var) :
    (nb090AlphaDummy505 h) ∈
      (((synCcompl (Class.cab (nb090AlphaDummy547 h)
              (synWrex (nb090AlphaDummy548 h) (Class.cv (nb090AlphaDummy506 h))
                (Wff.classEq (Class.cv (nb090AlphaDummy547 h))
                  (synCphi (Class.cv (nb090AlphaDummy548 h)))))))).fv ∪ ((synCcompl
            (Class.cab (nb090AlphaDummy547 h)
              (synWrex (nb090AlphaDummy548 h) (Class.cv (nb090AlphaDummy505 h))
                (Wff.classEq (Class.cv (nb090AlphaDummy547 h))
                  (synCun (synCphi (Class.cv (nb090AlphaDummy548 h)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb090AlphaDummy505 h) ≠ (nb090AlphaDummy547 h) from (by
          unfold nb090AlphaDummy547;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0584 h) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb090AlphaDummy505 h) ≠ (nb090AlphaDummy548 h) from (by
            unfold nb090AlphaDummy548;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0584 h) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb090_support_mem_0586 (A : Class) :
    (nb090AlphaDummy503 A) ∈
      (((Class.cab (nb090AlphaDummy545 A)
            (synWrex (nb090AlphaDummy546 A) (Class.cv (nb090AlphaDummy503 A))
              (Wff.classEq (Class.cv (nb090AlphaDummy545 A))
                (synCun (synCphi (Class.cv (nb090AlphaDummy546 A)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb090AlphaDummy545 A)
            (synWrex (nb090AlphaDummy546 A) (Class.cv (nb090AlphaDummy503 A))
              (Wff.classEq (Class.cv (nb090AlphaDummy545 A))
                (synCun (synCphi (Class.cv (nb090AlphaDummy546 A)))
                  (synCsn (synC0c))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb090AlphaDummy503 A) ≠ (nb090AlphaDummy545 A) from (by
          unfold nb090AlphaDummy545;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0582 A) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb090AlphaDummy503 A) ≠ (nb090AlphaDummy546 A) from (by
            unfold nb090AlphaDummy546;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0582 A) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb090_support_mem_0587 (h : Var) :
    (nb090AlphaDummy505 h) ∈
      (((Class.cab (nb090AlphaDummy547 h)
            (synWrex (nb090AlphaDummy548 h) (Class.cv (nb090AlphaDummy505 h))
              (Wff.classEq (Class.cv (nb090AlphaDummy547 h))
                (synCun (synCphi (Class.cv (nb090AlphaDummy548 h)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb090AlphaDummy547 h)
            (synWrex (nb090AlphaDummy548 h) (Class.cv (nb090AlphaDummy505 h))
              (Wff.classEq (Class.cv (nb090AlphaDummy547 h))
                (synCun (synCphi (Class.cv (nb090AlphaDummy548 h)))
                  (synCsn (synC0c))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb090AlphaDummy505 h) ≠ (nb090AlphaDummy547 h) from (by
          unfold nb090AlphaDummy547;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0584 h) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb090AlphaDummy505 h) ≠ (nb090AlphaDummy548 h) from (by
            unfold nb090AlphaDummy548;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0584 h) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb090_support_mem_0588 (A : Class) :
    (nb090AlphaDummy546 A) ∈
      (((synCcompl (synCphi (Class.cv (nb090AlphaDummy546 A))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0589 (h : Var) :
    (nb090AlphaDummy548 h) ∈
      (((synCcompl (synCphi (Class.cv (nb090AlphaDummy548 h))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0590 (A : Class) :
    (nb090AlphaDummy546 A) ∈
      (((synCphi (Class.cv (nb090AlphaDummy546 A)))).fv ∪
        ((synCphi (Class.cv (nb090AlphaDummy546 A)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0591 (h : Var) :
    (nb090AlphaDummy548 h) ∈
      (((synCphi (Class.cv (nb090AlphaDummy548 h)))).fv ∪
        ((synCphi (Class.cv (nb090AlphaDummy548 h)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0592 (A : Class) :
    (nb090AlphaDummy000 A) ∈
      (((synCnin (synCcom (synCcnv (Class.cv (nb090AlphaDummy000 A)))
              (synCcnv (synCcnv (Class.cv (nb090AlphaDummy000 A))))) (synCid))).fv ∪
        ((synCnin (synCcom (synCcnv (Class.cv (nb090AlphaDummy000 A)))
              (synCcnv (synCcnv (Class.cv (nb090AlphaDummy000 A))))) (synCid))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccom]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccnv]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0593 (h : Var) :
    h ∈
      (((synCnin (synCcom (synCcnv (Class.cv h)) (synCcnv (synCcnv (Class.cv h))))
            (synCid))).fv ∪
        ((synCnin (synCcom (synCcnv (Class.cv h)) (synCcnv (synCcnv (Class.cv h))))
            (synCid))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccom]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccnv]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0594 (A : Class) :
    (nb090AlphaDummy000 A) ∈
      (((synCcom (synCcnv (Class.cv (nb090AlphaDummy000 A)))
            (synCcnv (synCcnv (Class.cv (nb090AlphaDummy000 A)))))).fv ∪ ((synCid)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccom]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccnv]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0595 (h : Var) :
    h ∈
      (((synCcom (synCcnv (Class.cv h)) (synCcnv (synCcnv (Class.cv h))))).fv ∪
        ((synCid)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccom]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccnv]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0596 (A : Class) :
    (nb090AlphaDummy000 A) ∈
      (((synCcnv (Class.cv (nb090AlphaDummy000 A)))).fv ∪
        ((synCcnv (synCcnv (Class.cv (nb090AlphaDummy000 A))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccnv]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0597 (A : Class) :
    (nb090AlphaDummy000 A) ∈
      (({(nb090AlphaDummy423 A)} : Finset Var) ∪ ({(nb090AlphaDummy424 A)} : Finset Var) ∪
        ((synWex (nb090AlphaDummy425 A) (synWa
              (synWbr (Class.cv (nb090AlphaDummy423 A))
                (synCcnv (synCcnv (Class.cv (nb090AlphaDummy000 A))))
                (Class.cv (nb090AlphaDummy425 A)))
              (synWbr (Class.cv (nb090AlphaDummy425 A))
                (synCcnv (Class.cv (nb090AlphaDummy000 A)))
                (Class.cv (nb090AlphaDummy424 A)))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_wex]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb090AlphaDummy000 A) ≠ (nb090AlphaDummy425 A) from (by
          unfold nb090AlphaDummy425;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0596 A) 2))))
  · rw [fv_syn_wa]
    with_reducible rw [Finset.mem_union]
    left
    rw [fv_syn_wbr]
    with_reducible rw [Finset.mem_union]
    right
    rw [fv_syn_ccnv]
    rw [fv_syn_ccnv]
    rw [fv_class_cv]
    exact Finset.mem_singleton_self _

theorem nb090_support_mem_0598 (h : Var) :
    h ∈ (((synCcnv (Class.cv h))).fv ∪ ((synCcnv (synCcnv (Class.cv h)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccnv]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0599 (h : Var) :
    h ∈
      (({(nb090AlphaDummy426 h)} : Finset Var) ∪ ({(nb090AlphaDummy427 h)} : Finset Var) ∪
        ((synWex (nb090AlphaDummy428 h) (synWa
              (synWbr (Class.cv (nb090AlphaDummy426 h))
                (synCcnv (synCcnv (Class.cv h))) (Class.cv (nb090AlphaDummy428 h)))
              (synWbr (Class.cv (nb090AlphaDummy428 h)) (synCcnv (Class.cv h))
                (Class.cv (nb090AlphaDummy427 h)))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_wex]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show h ≠ (nb090AlphaDummy428 h) from (by
          unfold nb090AlphaDummy428;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0598 h) 2))))
  · rw [fv_syn_wa]
    with_reducible rw [Finset.mem_union]
    left
    rw [fv_syn_wbr]
    with_reducible rw [Finset.mem_union]
    right
    rw [fv_syn_ccnv]
    rw [fv_syn_ccnv]
    rw [fv_class_cv]
    exact Finset.mem_singleton_self _

theorem nb090_support_mem_0600 (A : Class) :
    (nb090AlphaDummy000 A) ∈
      (({(nb090AlphaDummy503 A)} : Finset Var) ∪ ({(nb090AlphaDummy504 A)} : Finset Var) ∪
        ((synWbr (Class.cv (nb090AlphaDummy504 A))
            (synCcnv (Class.cv (nb090AlphaDummy000 A)))
            (Class.cv (nb090AlphaDummy503 A)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_wbr]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccnv]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0601 (h : Var) :
    h ∈
      (({(nb090AlphaDummy505 h)} : Finset Var) ∪ ({(nb090AlphaDummy506 h)} : Finset Var) ∪
        ((synWbr (Class.cv (nb090AlphaDummy506 h)) (synCcnv (Class.cv h))
            (Class.cv (nb090AlphaDummy505 h)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_wbr]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccnv]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0602 (A : Class) :
    (nb090AlphaDummy000 A) ∈ (((synCcnv (Class.cv (nb090AlphaDummy000 A)))).fv) :=
  by
  rw [fv_syn_ccnv]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0603 (h : Var) : h ∈ (((synCcnv (Class.cv h))).fv) :=
  by
  rw [fv_syn_ccnv]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0604 (A : Class) :
    (nb090AlphaDummy425 A) ∈
      (((Class.cv (nb090AlphaDummy425 A))).fv ∪ ((Class.cv (nb090AlphaDummy424 A))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0605 (A : Class) :
    (nb090AlphaDummy425 A) ∈
      (((synCcompl (Class.cab (nb090AlphaDummy581 A)
              (synWrex (nb090AlphaDummy582 A) (Class.cv (nb090AlphaDummy425 A))
                (Wff.classEq (Class.cv (nb090AlphaDummy581 A))
                  (synCphi (Class.cv (nb090AlphaDummy582 A)))))))).fv ∪ ((synCcompl
            (Class.cab (nb090AlphaDummy581 A)
              (synWrex (nb090AlphaDummy582 A) (Class.cv (nb090AlphaDummy424 A))
                (Wff.classEq (Class.cv (nb090AlphaDummy581 A))
                  (synCun (synCphi (Class.cv (nb090AlphaDummy582 A)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb090AlphaDummy425 A) ≠ (nb090AlphaDummy581 A) from (by
          unfold nb090AlphaDummy581;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0604 A) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb090AlphaDummy425 A) ≠ (nb090AlphaDummy582 A) from (by
            unfold nb090AlphaDummy582;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0604 A) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb090_support_mem_0606 (h : Var) :
    (nb090AlphaDummy428 h) ∈
      (((Class.cv (nb090AlphaDummy428 h))).fv ∪ ((Class.cv (nb090AlphaDummy427 h))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0607 (h : Var) :
    (nb090AlphaDummy428 h) ∈
      (((synCcompl (Class.cab (nb090AlphaDummy583 h)
              (synWrex (nb090AlphaDummy584 h) (Class.cv (nb090AlphaDummy428 h))
                (Wff.classEq (Class.cv (nb090AlphaDummy583 h))
                  (synCphi (Class.cv (nb090AlphaDummy584 h)))))))).fv ∪ ((synCcompl
            (Class.cab (nb090AlphaDummy583 h)
              (synWrex (nb090AlphaDummy584 h) (Class.cv (nb090AlphaDummy427 h))
                (Wff.classEq (Class.cv (nb090AlphaDummy583 h))
                  (synCun (synCphi (Class.cv (nb090AlphaDummy584 h)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb090AlphaDummy428 h) ≠ (nb090AlphaDummy583 h) from (by
          unfold nb090AlphaDummy583;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0606 h) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb090AlphaDummy428 h) ≠ (nb090AlphaDummy584 h) from (by
            unfold nb090AlphaDummy584;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0606 h) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb090_support_mem_0608 (A : Class) :
    (nb090AlphaDummy425 A) ∈
      (((Class.cab (nb090AlphaDummy581 A)
            (synWrex (nb090AlphaDummy582 A) (Class.cv (nb090AlphaDummy425 A))
              (Wff.classEq (Class.cv (nb090AlphaDummy581 A))
                (synCphi (Class.cv (nb090AlphaDummy582 A))))))).fv ∪
        ((Class.cab (nb090AlphaDummy581 A)
            (synWrex (nb090AlphaDummy582 A) (Class.cv (nb090AlphaDummy425 A))
              (Wff.classEq (Class.cv (nb090AlphaDummy581 A))
                (synCphi (Class.cv (nb090AlphaDummy582 A))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb090AlphaDummy425 A) ≠ (nb090AlphaDummy581 A) from (by
          unfold nb090AlphaDummy581;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0604 A) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb090AlphaDummy425 A) ≠ (nb090AlphaDummy582 A) from (by
            unfold nb090AlphaDummy582;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0604 A) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb090_support_mem_0609 (h : Var) :
    (nb090AlphaDummy428 h) ∈
      (((Class.cab (nb090AlphaDummy583 h)
            (synWrex (nb090AlphaDummy584 h) (Class.cv (nb090AlphaDummy428 h))
              (Wff.classEq (Class.cv (nb090AlphaDummy583 h))
                (synCphi (Class.cv (nb090AlphaDummy584 h))))))).fv ∪
        ((Class.cab (nb090AlphaDummy583 h)
            (synWrex (nb090AlphaDummy584 h) (Class.cv (nb090AlphaDummy428 h))
              (Wff.classEq (Class.cv (nb090AlphaDummy583 h))
                (synCphi (Class.cv (nb090AlphaDummy584 h))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb090AlphaDummy428 h) ≠ (nb090AlphaDummy583 h) from (by
          unfold nb090AlphaDummy583;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0606 h) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb090AlphaDummy428 h) ≠ (nb090AlphaDummy584 h) from (by
            unfold nb090AlphaDummy584;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0606 h) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb090_support_mem_0610 (A : Class) :
    (nb090AlphaDummy582 A) ∈ (((Class.cv (nb090AlphaDummy582 A))).fv) :=
  by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0611 (h : Var) :
    (nb090AlphaDummy584 h) ∈ (((Class.cv (nb090AlphaDummy584 h))).fv) :=
  by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0612 (A : Class) :
    (nb090AlphaDummy589 A) ∈
      (((Wff.classMem (Class.cv (nb090AlphaDummy589 A)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb090AlphaDummy589 A)) (synC1c))).fv ∪
        ((Class.cv (nb090AlphaDummy589 A))).fv) :=
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

theorem nb090_support_mem_0613 (h : Var) :
    (nb090AlphaDummy591 h) ∈
      (((Wff.classMem (Class.cv (nb090AlphaDummy591 h)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb090AlphaDummy591 h)) (synC1c))).fv ∪
        ((Class.cv (nb090AlphaDummy591 h))).fv) :=
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

theorem nb090_support_mem_0614 (A : Class) :
    (nb090AlphaDummy589 A) ∈
      (((Class.cv (nb090AlphaDummy589 A))).fv ∪ ((synC1c)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0615 (h : Var) :
    (nb090AlphaDummy591 h) ∈
      (((Class.cv (nb090AlphaDummy591 h))).fv ∪ ((synC1c)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0616 (A : Class) :
    (nb090AlphaDummy596 A) ∈
      (((synCnin (Class.cv (nb090AlphaDummy596 A))
            (Class.cv (nb090AlphaDummy597 A)))).fv ∪
        ((synCnin (Class.cv (nb090AlphaDummy596 A))
            (Class.cv (nb090AlphaDummy597 A)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0617 (h : Var) :
    (nb090AlphaDummy599 h) ∈
      (((synCnin (Class.cv (nb090AlphaDummy599 h))
            (Class.cv (nb090AlphaDummy600 h)))).fv ∪
        ((synCnin (Class.cv (nb090AlphaDummy599 h))
            (Class.cv (nb090AlphaDummy600 h)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0618 (A : Class) :
    (nb090AlphaDummy596 A) ∈
      (((Class.cv (nb090AlphaDummy596 A))).fv ∪ ((Class.cv (nb090AlphaDummy597 A))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0619 (h : Var) :
    (nb090AlphaDummy599 h) ∈
      (((Class.cv (nb090AlphaDummy599 h))).fv ∪ ((Class.cv (nb090AlphaDummy600 h))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0620 (A : Class) :
    (nb090AlphaDummy597 A) ∈
      (((synCnin (Class.cv (nb090AlphaDummy596 A))
            (Class.cv (nb090AlphaDummy597 A)))).fv ∪
        ((synCnin (Class.cv (nb090AlphaDummy596 A))
            (Class.cv (nb090AlphaDummy597 A)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0621 (h : Var) :
    (nb090AlphaDummy600 h) ∈
      (((synCnin (Class.cv (nb090AlphaDummy599 h))
            (Class.cv (nb090AlphaDummy600 h)))).fv ∪
        ((synCnin (Class.cv (nb090AlphaDummy599 h))
            (Class.cv (nb090AlphaDummy600 h)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0622 (A : Class) :
    (nb090AlphaDummy597 A) ∈
      (((Class.cv (nb090AlphaDummy596 A))).fv ∪ ((Class.cv (nb090AlphaDummy597 A))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0623 (h : Var) :
    (nb090AlphaDummy600 h) ∈
      (((Class.cv (nb090AlphaDummy599 h))).fv ∪ ((Class.cv (nb090AlphaDummy600 h))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0624 (A : Class) :
    (nb090AlphaDummy596 A) ∈
      (((synCcompl (Class.cv (nb090AlphaDummy596 A)))).fv ∪
        ((synCcompl (Class.cv (nb090AlphaDummy597 A)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0625 (h : Var) :
    (nb090AlphaDummy599 h) ∈
      (((synCcompl (Class.cv (nb090AlphaDummy599 h)))).fv ∪
        ((synCcompl (Class.cv (nb090AlphaDummy600 h)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0626 (A : Class) :
    (nb090AlphaDummy596 A) ∈
      (((Class.cv (nb090AlphaDummy596 A))).fv ∪ ((Class.cv (nb090AlphaDummy596 A))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0627 (h : Var) :
    (nb090AlphaDummy599 h) ∈
      (((Class.cv (nb090AlphaDummy599 h))).fv ∪ ((Class.cv (nb090AlphaDummy599 h))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0628 (A : Class) :
    (nb090AlphaDummy597 A) ∈
      (((synCcompl (Class.cv (nb090AlphaDummy596 A)))).fv ∪
        ((synCcompl (Class.cv (nb090AlphaDummy597 A)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0629 (h : Var) :
    (nb090AlphaDummy600 h) ∈
      (((synCcompl (Class.cv (nb090AlphaDummy599 h)))).fv ∪
        ((synCcompl (Class.cv (nb090AlphaDummy600 h)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0630 (A : Class) :
    (nb090AlphaDummy597 A) ∈
      (((Class.cv (nb090AlphaDummy597 A))).fv ∪ ((Class.cv (nb090AlphaDummy597 A))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0631 (h : Var) :
    (nb090AlphaDummy600 h) ∈
      (((Class.cv (nb090AlphaDummy600 h))).fv ∪ ((Class.cv (nb090AlphaDummy600 h))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0632 (A : Class) :
    (nb090AlphaDummy424 A) ∈
      (((Class.cv (nb090AlphaDummy425 A))).fv ∪ ((Class.cv (nb090AlphaDummy424 A))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0633 (A : Class) :
    (nb090AlphaDummy424 A) ∈
      (((synCcompl (Class.cab (nb090AlphaDummy581 A)
              (synWrex (nb090AlphaDummy582 A) (Class.cv (nb090AlphaDummy425 A))
                (Wff.classEq (Class.cv (nb090AlphaDummy581 A))
                  (synCphi (Class.cv (nb090AlphaDummy582 A)))))))).fv ∪ ((synCcompl
            (Class.cab (nb090AlphaDummy581 A)
              (synWrex (nb090AlphaDummy582 A) (Class.cv (nb090AlphaDummy424 A))
                (Wff.classEq (Class.cv (nb090AlphaDummy581 A))
                  (synCun (synCphi (Class.cv (nb090AlphaDummy582 A)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb090AlphaDummy424 A) ≠ (nb090AlphaDummy581 A) from (by
          unfold nb090AlphaDummy581;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0632 A) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb090AlphaDummy424 A) ≠ (nb090AlphaDummy582 A) from (by
            unfold nb090AlphaDummy582;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0632 A) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb090_support_mem_0634 (h : Var) :
    (nb090AlphaDummy427 h) ∈
      (((Class.cv (nb090AlphaDummy428 h))).fv ∪ ((Class.cv (nb090AlphaDummy427 h))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired

end
