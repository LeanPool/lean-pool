/-
Copyright (c) 2026 Elliot Glazer and NFNotWPP contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elliot Glazer and NFNotWPP contributors
-/

module

public import LeanPool.NFWeakPartition.Certificates.NominalWPPReplayChunk017Compact001Block018

/-! Nominal proof certificates grouped in dependency order. -/


public section

/-! Certificates from `NominalWPPReplayChunk017Compact001Part080`. -/


section

namespace NFChoice.DirectNominalPrf.WPPReplay

open scoped Fol
open NFChoice.Foundation
open NFChoice.SemanticCore
open NFChoice.ReplaySupport
open NFChoice.Compiler.CompactSourceSyntax

@[expose]
noncomputable def g_hnwcutambfactorranbrimpndv (x : Var) (z : Var) (u : Var) (A : Class)
    (dv_A_u : u ∉ A.fv) (dv_A_x : x ∉ A.fv) (dv_u_x : u ≠ x) (dv_x_z : x ≠ z)
    (hyp_hnwcutambfactorranbrimpndv_1 : Nominal.NPrf (.classMem A (syn_cvv))) :
    Nominal.NPrf
      (.imp (.classMem (.cv u) (syn_chwcn A)) (syn_wb (.classMem (.cv z) (syn_crn
              (syn_ccom (syn_chnqmap1 A) (syn_csi (syn_chnwcutrel (syn_cfv (syn_c1st) (.cv u))
                    (syn_cfv (syn_c2nd) (.cv u))))))) (syn_wrex x (syn_cfv (syn_c2nd) (.cv u))
            (.classEq (syn_cec
                (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u))
                  (.cv x)) (syn_chwniso A)) (.cv z))))) :=
  by
  let proofSupport : Finset Var :=
    ({ x } : Finset Var) ∪ ({ z } : Finset Var) ∪ ({ u } : Finset Var) ∪ A.fv
  let p : Var := freshVar proofSupport 0
  let q : Var := freshVar proofSupport 1
  have fresh_p : p ∉ proofSupport :=
    by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_p_ne_x : p ≠ x := by
    intro h
    exact
      fresh_p
        (Finset.mem_union_left _ (Finset.mem_union_left _
            (Finset.mem_union_left _ (Finset.mem_singleton.mpr h))))
  have fresh_x_ne_p : x ≠ p := Ne.symm fresh_p_ne_x
  have fresh_p_ne_z : p ≠ z := by
    intro h
    exact
      fresh_p
        (Finset.mem_union_left _ (Finset.mem_union_left _
            (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))))
  have fresh_p_ne_u : p ≠ u := by
    intro h
    exact
      fresh_p
        (Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_singleton.mpr h)))
  have fresh_p_not_A : p ∉ A.fv := by
    intro h
    exact fresh_p (Finset.mem_union_right _ (h))
  have fresh_q : q ∉ proofSupport :=
    by
    change freshVar proofSupport 1 ∉ proofSupport
    exact freshVar_not_mem proofSupport 1
  have fresh_q_ne_x : q ≠ x := by
    intro h
    exact
      fresh_q
        (Finset.mem_union_left _ (Finset.mem_union_left _
            (Finset.mem_union_left _ (Finset.mem_singleton.mpr h))))
  have fresh_q_ne_z : q ≠ z := by
    intro h
    exact
      fresh_q
        (Finset.mem_union_left _ (Finset.mem_union_left _
            (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))))
  have fresh_q_ne_u : q ≠ u := by
    intro h
    exact
      fresh_q
        (Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_singleton.mpr h)))
  have fresh_q_not_A : q ∉ A.fv := by
    intro h
    exact fresh_q (Finset.mem_union_right _ (h))
  have fresh_p_ne_q : p ≠ q :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have fresh_q_ne_p : q ≠ p := Ne.symm fresh_p_ne_q
  have dv_cache_0001 : u ∉ (A).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : u ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_A_u, not_false_eq_true])
  have dv_cache_0002 : p ∉ ((syn_cpw1 (syn_cpw1 (syn_cfv (syn_c2nd) (.cv u))))).fv :=
    by
    clear dv_cache_0001
    exact
      (by
        have compact_fv_not_mem_empty : p ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c2nd,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, fresh_p_ne_u, compact_fv_not_mem_empty, or_false,
          not_false_eq_true])
  have dv_cache_0003 : p ∉ ((Class.cv z)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact
      (by
        have compact_fv_not_mem_empty : p ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_p_ne_z, not_false_eq_true])
  have dv_cache_0004 :
    p ∉
      ((syn_ccom (syn_chnqmap1 A) (syn_csi (syn_chnwcutrel (syn_cfv (syn_c1st) (.cv u))
              (syn_cfv (syn_c2nd) (.cv u)))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact
      (by
        have compact_fv_not_mem_empty : p ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccom,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chnqmap1,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csi,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chnwcutrel,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1st,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c2nd, Finset.mem_union,
          Finset.mem_singleton, fresh_p_not_A, fresh_p_ne_u, compact_fv_not_mem_empty,
          or_false, not_false_eq_true])
  have dv_cache_0005 : p ∉ (A).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact
      (by
        have compact_fv_not_mem_empty : p ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_p_not_A, not_false_eq_true])
  have dv_cache_0006 : p ≠ u :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact (show p ≠ u from (by exact fresh_p_ne_u))
  have dv_cache_0007 : Disjoint ((Class.cv x)).fv ((syn_cfv (syn_c1st) (.cv u))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006
    exact
      (show Disjoint ((Class.cv x)).fv ((syn_cfv (syn_c1st) (.cv u))).fv from (by
          rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv,
            NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv];
          exact
            (show
              Disjoint (({ x } : Finset Var)) ((((Class.cv u)).fv) ∪ (((syn_c1st)).fv))
              from
              (Finset.disjoint_union_right.mpr
                ⟨(show Disjoint (({ x } : Finset Var)) (((Class.cv u)).fv) from
                    (by
                      rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv];
                      exact
                        (show Disjoint (({ x } : Finset Var)) (({ u } : Finset Var)) from
                          (Finset.disjoint_singleton_left.mpr
                            (show x ∉ ({ u } : Finset Var) from
                              (by
                                simpa only [Finset.mem_singleton] using
                                  (show x ≠ u from (by exact Ne.symm dv_u_x)))))))),
                  (show Disjoint (({ x } : Finset Var)) (((syn_c1st)).fv) from
                    (by
                      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1st];
                      exact
                        (show Disjoint (({ x } : Finset Var)) ((∅ : Finset Var)) from
                          (by simp))))⟩))))
  have dv_cache_0008 : x ∉ ((syn_cuni (syn_cuni (.cv p)))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cuni,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton, fresh_x_ne_p,
          not_false_eq_true])
  have dv_cache_0009 : x ∉ ((syn_cfv (syn_c2nd) (.cv u))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c2nd,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, (Ne.symm dv_u_x), compact_fv_not_mem_empty, or_false,
          not_false_eq_true])
  have dv_cache_0010 :
    x ∉
      ((Wff.classEq (syn_cec
            (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u))
              (syn_cuni (syn_cuni (.cv p)))) (syn_chwniso A)) (.cv z))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cec,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chnwcutcode,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1st,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c2nd,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cuni,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwniso, Finset.mem_union,
          Finset.mem_singleton, fresh_x_ne_p, (Ne.symm dv_u_x), dv_A_x, dv_x_z,
          compact_fv_not_mem_empty, or_false, not_false_eq_true])
  have dv_cache_0011 :
    x ∉
      ((syn_wa (.classMem (.cv u) (syn_chwcn A))
          (syn_wa (.classMem (.cv p) (syn_cpw1 (syn_cpw1 (syn_cfv (syn_c2nd) (.cv u)))))
            (.classEq (syn_cfv (syn_ccom (syn_chnqmap1 A) (syn_csi
                    (syn_chnwcutrel (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)))))
                (.cv p)) (.cv z))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwcn,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c2nd,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccom,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chnqmap1,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csi,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chnwcutrel,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1st, Finset.mem_union,
          Finset.mem_singleton, (Ne.symm dv_u_x), dv_A_x, fresh_x_ne_p, dv_x_z,
          compact_fv_not_mem_empty, or_false, not_false_eq_true])
  have dv_cache_0012 :
    p ∉
      ((syn_wrex x (syn_cfv (syn_c2nd) (.cv u)) (.classEq (syn_cec
              (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u))
                (.cv x)) (syn_chwniso A)) (.cv z)))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
    exact
      (by
        have compact_fv_not_mem_empty : p ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wrex,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c2nd,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cec,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chnwcutcode,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1st,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwniso, Finset.mem_union,
          Finset.mem_erase, Finset.mem_singleton, fresh_p_ne_u, fresh_p_ne_x,
          fresh_p_not_A, fresh_p_ne_z, compact_fv_not_mem_empty, or_false, and_false,
          not_false_eq_true])
  have dv_cache_0013 : p ∉ ((Wff.classMem (.cv u) (syn_chwcn A))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012
    exact
      (by
        have compact_fv_not_mem_empty : p ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwcn, Finset.mem_union,
          Finset.mem_singleton, fresh_p_ne_u, fresh_p_not_A, or_false, not_false_eq_true])
  have dv_cache_0014 : q ∉ ((syn_csn (syn_csn (.cv x)))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013
    exact
      (by
        have compact_fv_not_mem_empty : q ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton, fresh_q_ne_x,
          not_false_eq_true])
  have dv_cache_0015 : q ∉ (A).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014
    exact
      (by
        have compact_fv_not_mem_empty : q ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_q_not_A, not_false_eq_true])
  have dv_cache_0016 : q ≠ u :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015
    exact (show q ≠ u from (by exact fresh_q_ne_u))
  have dv_cache_0017 :
    Disjoint ((syn_cuni (syn_cuni (.cv q)))).fv ((syn_cfv (syn_c1st) (.cv u))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016
    exact
      (show Disjoint ((syn_cuni (syn_cuni (.cv q)))).fv ((syn_cfv (syn_c1st) (.cv u))).fv from
        (by
          rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cuni,
            NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv];
          exact
            (show
              Disjoint (((syn_cuni (.cv q))).fv) ((((Class.cv u)).fv) ∪ (((syn_c1st)).fv))
              from
              (Finset.disjoint_union_right.mpr
                ⟨(show Disjoint (((syn_cuni (.cv q))).fv) (((Class.cv u)).fv) from
                    (by
                      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cuni];
                      exact
                        (show Disjoint (((Class.cv q)).fv) (((Class.cv u)).fv) from
                          (by
                            rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv];
                            exact
                              (show Disjoint (({ q } : Finset Var)) (((Class.cv u)).fv)
                                from
                                (by
                                  rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv];
                                  exact
                                    (show
                                      Disjoint (({ q } : Finset Var))
                                        (({ u } : Finset Var))
                                      from
                                      (Finset.disjoint_singleton_left.mpr
                                        (show q ∉ ({ u } : Finset Var) from
                                          (by
                                            simpa only [Finset.mem_singleton] using
                                              (show q ≠ u from
                                                (by exact fresh_q_ne_u)))))))))))),
                  (show Disjoint (((syn_cuni (.cv q))).fv) (((syn_c1st)).fv) from
                    (by
                      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cuni];
                      exact
                        (show Disjoint (((Class.cv q)).fv) (((syn_c1st)).fv) from
                          (by
                            rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv];
                            exact
                              (show Disjoint (({ q } : Finset Var)) (((syn_c1st)).fv) from
                                (by
                                  rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1st];
                                  exact
                                    (show
                                      Disjoint (({ q } : Finset Var)) ((∅ : Finset Var))
                                      from (by simp))))))))⟩))))
  have dv_cache_0018 : p ∉ ((Class.cv q)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
    exact
      (by
        have compact_fv_not_mem_empty : p ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_p_ne_q, not_false_eq_true])
  have dv_cache_0019 :
    p ∉
      ((Wff.classEq (syn_cfv (syn_ccom (syn_chnqmap1 A) (syn_csi
                (syn_chnwcutrel (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)))))
            (.cv q)) (.cv z))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018
    exact
      (by
        have compact_fv_not_mem_empty : p ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccom,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chnqmap1,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csi,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chnwcutrel,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1st,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c2nd, Finset.mem_union,
          Finset.mem_singleton, fresh_p_ne_q, fresh_p_not_A, fresh_p_ne_u, fresh_p_ne_z,
          compact_fv_not_mem_empty, or_false, not_false_eq_true])
  have dv_cache_0020 :
    q ∉
      ((syn_wrex p (syn_cpw1 (syn_cpw1 (syn_cfv (syn_c2nd) (.cv u)))) (.classEq (syn_cfv
              (syn_ccom (syn_chnqmap1 A) (syn_csi (syn_chnwcutrel (syn_cfv (syn_c1st) (.cv u))
                    (syn_cfv (syn_c2nd) (.cv u))))) (.cv p)) (.cv z)))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019
    exact
      (by
        have compact_fv_not_mem_empty : q ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wrex,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c2nd,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccom,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chnqmap1,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csi,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chnwcutrel,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1st, Finset.mem_union,
          Finset.mem_erase, Finset.mem_singleton, fresh_q_ne_u, fresh_q_ne_p,
          fresh_q_not_A, fresh_q_ne_z, compact_fv_not_mem_empty, or_false, and_false,
          not_false_eq_true])
  have dv_cache_0021 :
    q ∉
      ((syn_wa (syn_wa (.classMem (.cv u) (syn_chwcn A))
            (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u)))) (.classEq (syn_cec
              (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u))
                (.cv x)) (syn_chwniso A)) (.cv z)))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020
    exact
      (by
        have compact_fv_not_mem_empty : q ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwcn,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c2nd,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cec,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chnwcutcode,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1st,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwniso, Finset.mem_union,
          Finset.mem_singleton, fresh_q_ne_u, fresh_q_not_A, fresh_q_ne_x, fresh_q_ne_z,
          compact_fv_not_mem_empty, or_false, not_false_eq_true])
  have dv_cache_0022 :
    x ∉
      ((syn_wrex p (syn_cpw1 (syn_cpw1 (syn_cfv (syn_c2nd) (.cv u)))) (.classEq (syn_cfv
              (syn_ccom (syn_chnqmap1 A) (syn_csi (syn_chnwcutrel (syn_cfv (syn_c1st) (.cv u))
                    (syn_cfv (syn_c2nd) (.cv u))))) (.cv p)) (.cv z)))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wrex,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c2nd,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccom,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chnqmap1,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csi,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chnwcutrel,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1st, Finset.mem_union,
          Finset.mem_erase, Finset.mem_singleton, (Ne.symm dv_u_x), fresh_x_ne_p, dv_A_x,
          dv_x_z, compact_fv_not_mem_empty, or_false, and_false, not_false_eq_true])
  have dv_cache_0023 : x ∉ ((Wff.classMem (.cv u) (syn_chwcn A))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwcn, Finset.mem_union,
          Finset.mem_singleton, (Ne.symm dv_u_x), dv_A_x, or_false, not_false_eq_true])
  have p0000 :=
    @g_hnwcutambfactorf1impndv u A dv_cache_0001 hyp_hnwcutambfactorranbrimpndv_1
  have p0001 :=
    @g_f1fn (syn_cpw1 (syn_cpw1 (syn_cfv (syn_c2nd) (.cv u)))) (syn_chnord A)
      (syn_ccom (syn_chnqmap1 A) (syn_csi
          (syn_chnwcutrel (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)))))
  have p0002 :=
    @g_syl (.classMem (.cv u) (syn_chwcn A))
      (syn_wf1 (syn_ccom (syn_chnqmap1 A) (syn_csi
            (syn_chnwcutrel (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)))))
        (syn_cpw1 (syn_cpw1 (syn_cfv (syn_c2nd) (.cv u)))) (syn_chnord A))
      (syn_wfn (syn_ccom (syn_chnqmap1 A) (syn_csi
            (syn_chnwcutrel (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)))))
        (syn_cpw1 (syn_cpw1 (syn_cfv (syn_c2nd) (.cv u)))))
      p0000 p0001
  have p0003 :=
    @g_fvelrnb p (syn_cpw1 (syn_cpw1 (syn_cfv (syn_c2nd) (.cv u)))) (.cv z)
      (syn_ccom (syn_chnqmap1 A) (syn_csi
          (syn_chnwcutrel (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)))))
      dv_cache_0002 dv_cache_0003 dv_cache_0004
  have p0004 :=
    @g_syl (.classMem (.cv u) (syn_chwcn A))
      (syn_wfn (syn_ccom (syn_chnqmap1 A) (syn_csi
            (syn_chnwcutrel (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)))))
        (syn_cpw1 (syn_cpw1 (syn_cfv (syn_c2nd) (.cv u)))))
      (syn_wb (.classMem (.cv z) (syn_crn (syn_ccom (syn_chnqmap1 A) (syn_csi
                (syn_chnwcutrel (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)))))))
        (syn_wrex p (syn_cpw1 (syn_cpw1 (syn_cfv (syn_c2nd) (.cv u)))) (.classEq (syn_cfv
              (syn_ccom (syn_chnqmap1 A) (syn_csi (syn_chnwcutrel (syn_cfv (syn_c1st) (.cv u))
                    (syn_cfv (syn_c2nd) (.cv u))))) (.cv p)) (.cv z))))
      p0002 p0003
  have p0005 :=
    @g_simpr (.classMem (.cv u) (syn_chwcn A))
      (syn_wa (.classMem (.cv p) (syn_cpw1 (syn_cpw1 (syn_cfv (syn_c2nd) (.cv u))))) (.classEq
          (syn_cfv (syn_ccom (syn_chnqmap1 A) (syn_csi
                (syn_chnwcutrel (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)))))
            (.cv p)) (.cv z)))
  have p0006 :=
    @g_simpl (.classMem (.cv p) (syn_cpw1 (syn_cpw1 (syn_cfv (syn_c2nd) (.cv u)))))
      (.classEq (syn_cfv (syn_ccom (syn_chnqmap1 A) (syn_csi
              (syn_chnwcutrel (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)))))
          (.cv p)) (.cv z))
  have p0007 :=
    @g_syl
      (syn_wa (.classMem (.cv u) (syn_chwcn A))
        (syn_wa (.classMem (.cv p) (syn_cpw1 (syn_cpw1 (syn_cfv (syn_c2nd) (.cv u))))) (.classEq
            (syn_cfv (syn_ccom (syn_chnqmap1 A) (syn_csi
                  (syn_chnwcutrel (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)))))
              (.cv p)) (.cv z))))
      (syn_wa (.classMem (.cv p) (syn_cpw1 (syn_cpw1 (syn_cfv (syn_c2nd) (.cv u))))) (.classEq
          (syn_cfv (syn_ccom (syn_chnqmap1 A) (syn_csi
                (syn_chnwcutrel (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)))))
            (.cv p)) (.cv z)))
      (.classMem (.cv p) (syn_cpw1 (syn_cpw1 (syn_cfv (syn_c2nd) (.cv u))))) p0005 p0006
  have p0008 :=
    @g_simpl (.classMem (.cv u) (syn_chwcn A))
      (syn_wa (.classMem (.cv p) (syn_cpw1 (syn_cpw1 (syn_cfv (syn_c2nd) (.cv u))))) (.classEq
          (syn_cfv (syn_ccom (syn_chnqmap1 A) (syn_csi
                (syn_chnwcutrel (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)))))
            (.cv p)) (.cv z)))
  have p0009 :=
    @g_hnwcutambfactorvalimpndv u A p dv_cache_0005 dv_cache_0001 dv_cache_0006
      hyp_hnwcutambfactorranbrimpndv_1
  have p0010 :=
    @g_syl
      (syn_wa (.classMem (.cv u) (syn_chwcn A))
        (syn_wa (.classMem (.cv p) (syn_cpw1 (syn_cpw1 (syn_cfv (syn_c2nd) (.cv u))))) (.classEq
            (syn_cfv (syn_ccom (syn_chnqmap1 A) (syn_csi
                  (syn_chnwcutrel (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)))))
              (.cv p)) (.cv z))))
      (.classMem (.cv u) (syn_chwcn A))
      (.imp (.classMem (.cv p) (syn_cpw1 (syn_cpw1 (syn_cfv (syn_c2nd) (.cv u))))) (.classEq
          (syn_cfv (syn_ccom (syn_chnqmap1 A) (syn_csi
                (syn_chnwcutrel (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)))))
            (.cv p)) (syn_cec
            (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u))
              (syn_cuni (syn_cuni (.cv p)))) (syn_chwniso A))))
      p0008 p0009
  have p0011 :=
    @g_mpd
      (syn_wa (.classMem (.cv u) (syn_chwcn A))
        (syn_wa (.classMem (.cv p) (syn_cpw1 (syn_cpw1 (syn_cfv (syn_c2nd) (.cv u))))) (.classEq
            (syn_cfv (syn_ccom (syn_chnqmap1 A) (syn_csi
                  (syn_chnwcutrel (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)))))
              (.cv p)) (.cv z))))
      (.classMem (.cv p) (syn_cpw1 (syn_cpw1 (syn_cfv (syn_c2nd) (.cv u)))))
      (.classEq (syn_cfv (syn_ccom (syn_chnqmap1 A) (syn_csi
              (syn_chnwcutrel (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)))))
          (.cv p)) (syn_cec
          (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u))
            (syn_cuni (syn_cuni (.cv p)))) (syn_chwniso A)))
      p0007 p0010
  have p0013 :=
    @g_simpr (.classMem (.cv p) (syn_cpw1 (syn_cpw1 (syn_cfv (syn_c2nd) (.cv u)))))
      (.classEq (syn_cfv (syn_ccom (syn_chnqmap1 A) (syn_csi
              (syn_chnwcutrel (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)))))
          (.cv p)) (.cv z))
  have p0014 :=
    @g_syl
      (syn_wa (.classMem (.cv u) (syn_chwcn A))
        (syn_wa (.classMem (.cv p) (syn_cpw1 (syn_cpw1 (syn_cfv (syn_c2nd) (.cv u))))) (.classEq
            (syn_cfv (syn_ccom (syn_chnqmap1 A) (syn_csi
                  (syn_chnwcutrel (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)))))
              (.cv p)) (.cv z))))
      (syn_wa (.classMem (.cv p) (syn_cpw1 (syn_cpw1 (syn_cfv (syn_c2nd) (.cv u))))) (.classEq
          (syn_cfv (syn_ccom (syn_chnqmap1 A) (syn_csi
                (syn_chnwcutrel (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)))))
            (.cv p)) (.cv z)))
      (.classEq (syn_cfv (syn_ccom (syn_chnqmap1 A) (syn_csi
              (syn_chnwcutrel (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)))))
          (.cv p)) (.cv z))
      p0005 p0013
  have p0015 :=
    @g_eqtr3d
      (syn_wa (.classMem (.cv u) (syn_chwcn A))
        (syn_wa (.classMem (.cv p) (syn_cpw1 (syn_cpw1 (syn_cfv (syn_c2nd) (.cv u))))) (.classEq
            (syn_cfv (syn_ccom (syn_chnqmap1 A) (syn_csi
                  (syn_chnwcutrel (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)))))
              (.cv p)) (.cv z))))
      (syn_cfv (syn_ccom (syn_chnqmap1 A) (syn_csi
            (syn_chnwcutrel (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)))))
        (.cv p))
      (syn_cec (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u))
          (syn_cuni (syn_cuni (.cv p)))) (syn_chwniso A))
      (.cv z) p0011 p0014
  have p0019 := @g_pw12argcl (.cv p) (syn_cfv (syn_c2nd) (.cv u))
  have p0020 :=
    @g_syl
      (syn_wa (.classMem (.cv u) (syn_chwcn A))
        (syn_wa (.classMem (.cv p) (syn_cpw1 (syn_cpw1 (syn_cfv (syn_c2nd) (.cv u))))) (.classEq
            (syn_cfv (syn_ccom (syn_chnqmap1 A) (syn_csi
                  (syn_chnwcutrel (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)))))
              (.cv p)) (.cv z))))
      (.classMem (.cv p) (syn_cpw1 (syn_cpw1 (syn_cfv (syn_c2nd) (.cv u)))))
      (syn_wa (.classMem (syn_cuni (syn_cuni (.cv p))) (syn_cfv (syn_c2nd) (.cv u)))
        (.classEq (.cv p) (syn_csn (syn_csn (syn_cuni (syn_cuni (.cv p)))))))
      p0007 p0019
  have p0021 :=
    @g_simpld
      (syn_wa (.classMem (.cv u) (syn_chwcn A))
        (syn_wa (.classMem (.cv p) (syn_cpw1 (syn_cpw1 (syn_cfv (syn_c2nd) (.cv u))))) (.classEq
            (syn_cfv (syn_ccom (syn_chnqmap1 A) (syn_csi
                  (syn_chnwcutrel (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)))))
              (.cv p)) (.cv z))))
      (.classMem (syn_cuni (syn_cuni (.cv p))) (syn_cfv (syn_c2nd) (.cv u)))
      (.classEq (.cv p) (syn_csn (syn_csn (syn_cuni (syn_cuni (.cv p)))))) p0020
  have p0022 :=
    @g_simpr
      (syn_wa (.classMem (.cv u) (syn_chwcn A))
        (syn_wa (.classMem (.cv p) (syn_cpw1 (syn_cpw1 (syn_cfv (syn_c2nd) (.cv u))))) (.classEq
            (syn_cfv (syn_ccom (syn_chnqmap1 A) (syn_csi
                  (syn_chnwcutrel (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)))))
              (.cv p)) (.cv z))))
      (.classEq (.cv x) (syn_cuni (syn_cuni (.cv p))))
  have p0023 :=
    @g_hnwcutcodeeq3 (.cv x) (syn_cuni (syn_cuni (.cv p))) (syn_cfv (syn_c2nd) (.cv u))
      (syn_cfv (syn_c1st) (.cv u)) dv_cache_0007
  have p0024 :=
    @g_syl
      (syn_wa (syn_wa (.classMem (.cv u) (syn_chwcn A))
          (syn_wa (.classMem (.cv p) (syn_cpw1 (syn_cpw1 (syn_cfv (syn_c2nd) (.cv u)))))
            (.classEq (syn_cfv (syn_ccom (syn_chnqmap1 A) (syn_csi
                    (syn_chnwcutrel (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)))))
                (.cv p)) (.cv z)))) (.classEq (.cv x) (syn_cuni (syn_cuni (.cv p)))))
      (.classEq (.cv x) (syn_cuni (syn_cuni (.cv p))))
      (.classEq (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u))
          (.cv x)) (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u))
          (syn_cuni (syn_cuni (.cv p)))))
      p0022 p0023
  have p0025 :=
    @g_eceq1
      (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv x))
      (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u))
        (syn_cuni (syn_cuni (.cv p))))
      (syn_chwniso A)
  have p0026 :=
    @g_syl
      (syn_wa (syn_wa (.classMem (.cv u) (syn_chwcn A))
          (syn_wa (.classMem (.cv p) (syn_cpw1 (syn_cpw1 (syn_cfv (syn_c2nd) (.cv u)))))
            (.classEq (syn_cfv (syn_ccom (syn_chnqmap1 A) (syn_csi
                    (syn_chnwcutrel (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)))))
                (.cv p)) (.cv z)))) (.classEq (.cv x) (syn_cuni (syn_cuni (.cv p)))))
      (.classEq (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u))
          (.cv x)) (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u))
          (syn_cuni (syn_cuni (.cv p)))))
      (.classEq (syn_cec
          (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv x))
          (syn_chwniso A)) (syn_cec
          (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u))
            (syn_cuni (syn_cuni (.cv p)))) (syn_chwniso A)))
      p0024 p0025
  have p0027 :=
    @g_eqeq1d
      (syn_wa (syn_wa (.classMem (.cv u) (syn_chwcn A))
          (syn_wa (.classMem (.cv p) (syn_cpw1 (syn_cpw1 (syn_cfv (syn_c2nd) (.cv u)))))
            (.classEq (syn_cfv (syn_ccom (syn_chnqmap1 A) (syn_csi
                    (syn_chnwcutrel (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)))))
                (.cv p)) (.cv z)))) (.classEq (.cv x) (syn_cuni (syn_cuni (.cv p)))))
      (syn_cec (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u))
          (.cv x)) (syn_chwniso A))
      (syn_cec (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u))
          (syn_cuni (syn_cuni (.cv p)))) (syn_chwniso A))
      (.cv z) p0026
  have p0028 :=
    @g_rspcedv
      (syn_wa (.classMem (.cv u) (syn_chwcn A))
        (syn_wa (.classMem (.cv p) (syn_cpw1 (syn_cpw1 (syn_cfv (syn_c2nd) (.cv u))))) (.classEq
            (syn_cfv (syn_ccom (syn_chnqmap1 A) (syn_csi
                  (syn_chnwcutrel (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)))))
              (.cv p)) (.cv z))))
      (.classEq (syn_cec
          (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv x))
          (syn_chwniso A)) (.cv z))
      (.classEq (syn_cec
          (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u))
            (syn_cuni (syn_cuni (.cv p)))) (syn_chwniso A)) (.cv z))
      x (syn_cuni (syn_cuni (.cv p))) (syn_cfv (syn_c2nd) (.cv u)) dv_cache_0008
      dv_cache_0009 dv_cache_0010 dv_cache_0011 p0021 p0027
  have p0029 :=
    @g_mpd
      (syn_wa (.classMem (.cv u) (syn_chwcn A))
        (syn_wa (.classMem (.cv p) (syn_cpw1 (syn_cpw1 (syn_cfv (syn_c2nd) (.cv u))))) (.classEq
            (syn_cfv (syn_ccom (syn_chnqmap1 A) (syn_csi
                  (syn_chnwcutrel (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)))))
              (.cv p)) (.cv z))))
      (.classEq (syn_cec
          (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u))
            (syn_cuni (syn_cuni (.cv p)))) (syn_chwniso A)) (.cv z))
      (syn_wrex x (syn_cfv (syn_c2nd) (.cv u)) (.classEq (syn_cec
            (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv x))
            (syn_chwniso A)) (.cv z)))
      p0015 p0028
  have p0030 :=
    @g_n_3impb (.classMem (.cv u) (syn_chwcn A))
      (.classMem (.cv p) (syn_cpw1 (syn_cpw1 (syn_cfv (syn_c2nd) (.cv u)))))
      (.classEq (syn_cfv (syn_ccom (syn_chnqmap1 A) (syn_csi
              (syn_chnwcutrel (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)))))
          (.cv p)) (.cv z))
      (syn_wrex x (syn_cfv (syn_c2nd) (.cv u)) (.classEq (syn_cec
            (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv x))
            (syn_chwniso A)) (.cv z)))
      p0029
  have p0031 :=
    @g_n_3exp (.classMem (.cv u) (syn_chwcn A))
      (.classMem (.cv p) (syn_cpw1 (syn_cpw1 (syn_cfv (syn_c2nd) (.cv u)))))
      (.classEq (syn_cfv (syn_ccom (syn_chnqmap1 A) (syn_csi
              (syn_chnwcutrel (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)))))
          (.cv p)) (.cv z))
      (syn_wrex x (syn_cfv (syn_c2nd) (.cv u)) (.classEq (syn_cec
            (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv x))
            (syn_chwniso A)) (.cv z)))
      p0030
  have p0032 :=
    @g_rexlimdv (.classMem (.cv u) (syn_chwcn A))
      (.classEq (syn_cfv (syn_ccom (syn_chnqmap1 A) (syn_csi
              (syn_chnwcutrel (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)))))
          (.cv p)) (.cv z))
      (syn_wrex x (syn_cfv (syn_c2nd) (.cv u)) (.classEq (syn_cec
            (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv x))
            (syn_chwniso A)) (.cv z)))
      p (syn_cpw1 (syn_cpw1 (syn_cfv (syn_c2nd) (.cv u)))) dv_cache_0012 dv_cache_0013
      p0031
  have p0033 :=
    @g_imp (.classMem (.cv u) (syn_chwcn A))
      (syn_wrex p (syn_cpw1 (syn_cpw1 (syn_cfv (syn_c2nd) (.cv u)))) (.classEq (syn_cfv
            (syn_ccom (syn_chnqmap1 A) (syn_csi (syn_chnwcutrel (syn_cfv (syn_c1st) (.cv u))
                  (syn_cfv (syn_c2nd) (.cv u))))) (.cv p)) (.cv z)))
      (syn_wrex x (syn_cfv (syn_c2nd) (.cv u)) (.classEq (syn_cec
            (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv x))
            (syn_chwniso A)) (.cv z)))
      p0032
  have p0034 := @g_snex (syn_csn (.cv x))
  have p0035 := @g_isseti q (syn_csn (syn_csn (.cv x))) dv_cache_0014 p0034
  have p0036 :=
    @g_a1i (syn_wex q (.classEq (.cv q) (syn_csn (syn_csn (.cv x)))))
      (syn_wa (syn_wa (.classMem (.cv u) (syn_chwcn A))
          (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u)))) (.classEq (syn_cec
            (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv x))
            (syn_chwniso A)) (.cv z)))
      p0035
  have p0037 :=
    @g_simpl
      (syn_wa (syn_wa (.classMem (.cv u) (syn_chwcn A))
          (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u)))) (.classEq (syn_cec
            (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv x))
            (syn_chwniso A)) (.cv z)))
      (.classEq (.cv q) (syn_csn (syn_csn (.cv x))))
  have p0038 :=
    @g_simpl
      (syn_wa (.classMem (.cv u) (syn_chwcn A))
        (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u))))
      (.classEq (syn_cec
          (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv x))
          (syn_chwniso A)) (.cv z))
  have p0039 :=
    @g_syl
      (syn_wa (syn_wa (syn_wa (.classMem (.cv u) (syn_chwcn A))
            (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u)))) (.classEq (syn_cec
              (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u))
                (.cv x)) (syn_chwniso A)) (.cv z)))
        (.classEq (.cv q) (syn_csn (syn_csn (.cv x)))))
      (syn_wa (syn_wa (.classMem (.cv u) (syn_chwcn A))
          (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u)))) (.classEq (syn_cec
            (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv x))
            (syn_chwniso A)) (.cv z)))
      (syn_wa (.classMem (.cv u) (syn_chwcn A))
        (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u))))
      p0037 p0038
  have p0040 :=
    @g_simpr (.classMem (.cv u) (syn_chwcn A))
      (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u)))
  have p0041 := @g_snelpw1 (.cv x) (syn_cfv (syn_c2nd) (.cv u))
  have p0042 :=
    @g_a1i
      (syn_wb (.classMem (syn_csn (.cv x)) (syn_cpw1 (syn_cfv (syn_c2nd) (.cv u))))
        (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u))))
      (syn_wa (.classMem (.cv u) (syn_chwcn A))
        (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u))))
      p0041
  have p0043 :=
    @g_mpbird
      (syn_wa (.classMem (.cv u) (syn_chwcn A))
        (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u))))
      (.classMem (syn_csn (.cv x)) (syn_cpw1 (syn_cfv (syn_c2nd) (.cv u))))
      (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u))) p0040 p0042
  have p0044 := @g_snelpw1 (syn_csn (.cv x)) (syn_cpw1 (syn_cfv (syn_c2nd) (.cv u)))
  have p0045 :=
    @g_a1i
      (syn_wb (.classMem (syn_csn (syn_csn (.cv x)))
          (syn_cpw1 (syn_cpw1 (syn_cfv (syn_c2nd) (.cv u)))))
        (.classMem (syn_csn (.cv x)) (syn_cpw1 (syn_cfv (syn_c2nd) (.cv u)))))
      (syn_wa (.classMem (.cv u) (syn_chwcn A))
        (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u))))
      p0044
  have p0046 :=
    @g_mpbird
      (syn_wa (.classMem (.cv u) (syn_chwcn A))
        (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u))))
      (.classMem (syn_csn (syn_csn (.cv x))) (syn_cpw1 (syn_cpw1 (syn_cfv (syn_c2nd) (.cv u)))))
      (.classMem (syn_csn (.cv x)) (syn_cpw1 (syn_cfv (syn_c2nd) (.cv u)))) p0043 p0045
  have p0047 :=
    @g_syl
      (syn_wa (syn_wa (syn_wa (.classMem (.cv u) (syn_chwcn A))
            (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u)))) (.classEq (syn_cec
              (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u))
                (.cv x)) (syn_chwniso A)) (.cv z)))
        (.classEq (.cv q) (syn_csn (syn_csn (.cv x)))))
      (syn_wa (.classMem (.cv u) (syn_chwcn A))
        (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u))))
      (.classMem (syn_csn (syn_csn (.cv x))) (syn_cpw1 (syn_cpw1 (syn_cfv (syn_c2nd) (.cv u)))))
      p0039 p0046
  have p0048 :=
    @g_simpr
      (syn_wa (syn_wa (.classMem (.cv u) (syn_chwcn A))
          (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u)))) (.classEq (syn_cec
            (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv x))
            (syn_chwniso A)) (.cv z)))
      (.classEq (.cv q) (syn_csn (syn_csn (.cv x))))
  have p0049 :=
    @g_eleq1d
      (syn_wa (syn_wa (syn_wa (.classMem (.cv u) (syn_chwcn A))
            (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u)))) (.classEq (syn_cec
              (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u))
                (.cv x)) (syn_chwniso A)) (.cv z)))
        (.classEq (.cv q) (syn_csn (syn_csn (.cv x)))))
      (.cv q) (syn_csn (syn_csn (.cv x)))
      (syn_cpw1 (syn_cpw1 (syn_cfv (syn_c2nd) (.cv u)))) p0048
  have p0050 :=
    @g_mpbird
      (syn_wa (syn_wa (syn_wa (.classMem (.cv u) (syn_chwcn A))
            (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u)))) (.classEq (syn_cec
              (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u))
                (.cv x)) (syn_chwniso A)) (.cv z)))
        (.classEq (.cv q) (syn_csn (syn_csn (.cv x)))))
      (.classMem (.cv q) (syn_cpw1 (syn_cpw1 (syn_cfv (syn_c2nd) (.cv u)))))
      (.classMem (syn_csn (syn_csn (.cv x))) (syn_cpw1 (syn_cpw1 (syn_cfv (syn_c2nd) (.cv u)))))
      p0047 p0049
  have p0068 :=
    @g_simpl (.classMem (.cv u) (syn_chwcn A))
      (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u)))
  have p0069 :=
    @g_syl
      (syn_wa (syn_wa (syn_wa (.classMem (.cv u) (syn_chwcn A))
            (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u)))) (.classEq (syn_cec
              (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u))
                (.cv x)) (syn_chwniso A)) (.cv z)))
        (.classEq (.cv q) (syn_csn (syn_csn (.cv x)))))
      (syn_wa (.classMem (.cv u) (syn_chwcn A))
        (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u))))
      (.classMem (.cv u) (syn_chwcn A)) p0039 p0068
  have p0070 :=
    @g_hnwcutambfactorvalimpndv u A q dv_cache_0015 dv_cache_0001 dv_cache_0016
      hyp_hnwcutambfactorranbrimpndv_1
  have p0071 :=
    @g_syl
      (syn_wa (syn_wa (syn_wa (.classMem (.cv u) (syn_chwcn A))
            (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u)))) (.classEq (syn_cec
              (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u))
                (.cv x)) (syn_chwniso A)) (.cv z)))
        (.classEq (.cv q) (syn_csn (syn_csn (.cv x)))))
      (.classMem (.cv u) (syn_chwcn A))
      (.imp (.classMem (.cv q) (syn_cpw1 (syn_cpw1 (syn_cfv (syn_c2nd) (.cv u))))) (.classEq
          (syn_cfv (syn_ccom (syn_chnqmap1 A) (syn_csi
                (syn_chnwcutrel (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)))))
            (.cv q)) (syn_cec
            (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u))
              (syn_cuni (syn_cuni (.cv q)))) (syn_chwniso A))))
      p0069 p0070
  have p0072 :=
    @g_mpd
      (syn_wa (syn_wa (syn_wa (.classMem (.cv u) (syn_chwcn A))
            (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u)))) (.classEq (syn_cec
              (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u))
                (.cv x)) (syn_chwniso A)) (.cv z)))
        (.classEq (.cv q) (syn_csn (syn_csn (.cv x)))))
      (.classMem (.cv q) (syn_cpw1 (syn_cpw1 (syn_cfv (syn_c2nd) (.cv u)))))
      (.classEq (syn_cfv (syn_ccom (syn_chnqmap1 A) (syn_csi
              (syn_chnwcutrel (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)))))
          (.cv q)) (syn_cec
          (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u))
            (syn_cuni (syn_cuni (.cv q)))) (syn_chwniso A)))
      p0050 p0071
  have p0074 :=
    @g_unieqd
      (syn_wa (syn_wa (syn_wa (.classMem (.cv u) (syn_chwcn A))
            (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u)))) (.classEq (syn_cec
              (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u))
                (.cv x)) (syn_chwniso A)) (.cv z)))
        (.classEq (.cv q) (syn_csn (syn_csn (.cv x)))))
      (.cv q) (syn_csn (syn_csn (.cv x))) p0048
  have p0075 :=
    @g_unieqd
      (syn_wa (syn_wa (syn_wa (.classMem (.cv u) (syn_chwcn A))
            (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u)))) (.classEq (syn_cec
              (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u))
                (.cv x)) (syn_chwniso A)) (.cv z)))
        (.classEq (.cv q) (syn_csn (syn_csn (.cv x)))))
      (syn_cuni (.cv q)) (syn_cuni (syn_csn (syn_csn (.cv x)))) p0074
  have p0076 := @g_snex (.cv x)
  have p0077 := @g_unisn (syn_csn (.cv x)) p0076
  have p0078 := @g_unieqi (syn_cuni (syn_csn (syn_csn (.cv x)))) (syn_csn (.cv x)) p0077
  have p0079 := @g_vex x
  have p0080 := @g_unisn (.cv x) p0079
  have p0081 :=
    @g_eqtri (syn_cuni (syn_cuni (syn_csn (syn_csn (.cv x)))))
      (syn_cuni (syn_csn (.cv x))) (.cv x) p0078 p0080
  have p0082 :=
    @g_a1i (.classEq (syn_cuni (syn_cuni (syn_csn (syn_csn (.cv x))))) (.cv x))
      (syn_wa (syn_wa (syn_wa (.classMem (.cv u) (syn_chwcn A))
            (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u)))) (.classEq (syn_cec
              (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u))
                (.cv x)) (syn_chwniso A)) (.cv z)))
        (.classEq (.cv q) (syn_csn (syn_csn (.cv x)))))
      p0081
  have p0083 :=
    @g_eqtrd
      (syn_wa (syn_wa (syn_wa (.classMem (.cv u) (syn_chwcn A))
            (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u)))) (.classEq (syn_cec
              (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u))
                (.cv x)) (syn_chwniso A)) (.cv z)))
        (.classEq (.cv q) (syn_csn (syn_csn (.cv x)))))
      (syn_cuni (syn_cuni (.cv q))) (syn_cuni (syn_cuni (syn_csn (syn_csn (.cv x)))))
      (.cv x) p0075 p0082
  have p0084 :=
    @g_hnwcutcodeeq3 (syn_cuni (syn_cuni (.cv q))) (.cv x) (syn_cfv (syn_c2nd) (.cv u))
      (syn_cfv (syn_c1st) (.cv u)) dv_cache_0017
  have p0085 :=
    @g_syl
      (syn_wa (syn_wa (syn_wa (.classMem (.cv u) (syn_chwcn A))
            (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u)))) (.classEq (syn_cec
              (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u))
                (.cv x)) (syn_chwniso A)) (.cv z)))
        (.classEq (.cv q) (syn_csn (syn_csn (.cv x)))))
      (.classEq (syn_cuni (syn_cuni (.cv q))) (.cv x))
      (.classEq (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u))
          (syn_cuni (syn_cuni (.cv q))))
        (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv x)))
      p0083 p0084
  have p0086 :=
    @g_eceq1
      (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u))
        (syn_cuni (syn_cuni (.cv q))))
      (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv x))
      (syn_chwniso A)
  have p0087 :=
    @g_syl
      (syn_wa (syn_wa (syn_wa (.classMem (.cv u) (syn_chwcn A))
            (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u)))) (.classEq (syn_cec
              (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u))
                (.cv x)) (syn_chwniso A)) (.cv z)))
        (.classEq (.cv q) (syn_csn (syn_csn (.cv x)))))
      (.classEq (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u))
          (syn_cuni (syn_cuni (.cv q))))
        (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv x)))
      (.classEq (syn_cec
          (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u))
            (syn_cuni (syn_cuni (.cv q)))) (syn_chwniso A)) (syn_cec
          (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv x))
          (syn_chwniso A)))
      p0085 p0086
  have p0088 :=
    @g_eqtrd
      (syn_wa (syn_wa (syn_wa (.classMem (.cv u) (syn_chwcn A))
            (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u)))) (.classEq (syn_cec
              (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u))
                (.cv x)) (syn_chwniso A)) (.cv z)))
        (.classEq (.cv q) (syn_csn (syn_csn (.cv x)))))
      (syn_cfv (syn_ccom (syn_chnqmap1 A) (syn_csi
            (syn_chnwcutrel (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)))))
        (.cv q))
      (syn_cec (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u))
          (syn_cuni (syn_cuni (.cv q)))) (syn_chwniso A))
      (syn_cec (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u))
          (.cv x)) (syn_chwniso A))
      p0072 p0087
  have p0090 :=
    @g_simpr
      (syn_wa (.classMem (.cv u) (syn_chwcn A))
        (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u))))
      (.classEq (syn_cec
          (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv x))
          (syn_chwniso A)) (.cv z))
  have p0091 :=
    @g_syl
      (syn_wa (syn_wa (syn_wa (.classMem (.cv u) (syn_chwcn A))
            (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u)))) (.classEq (syn_cec
              (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u))
                (.cv x)) (syn_chwniso A)) (.cv z)))
        (.classEq (.cv q) (syn_csn (syn_csn (.cv x)))))
      (syn_wa (syn_wa (.classMem (.cv u) (syn_chwcn A))
          (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u)))) (.classEq (syn_cec
            (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv x))
            (syn_chwniso A)) (.cv z)))
      (.classEq (syn_cec
          (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv x))
          (syn_chwniso A)) (.cv z))
      p0037 p0090
  have p0092 :=
    @g_eqtrd
      (syn_wa (syn_wa (syn_wa (.classMem (.cv u) (syn_chwcn A))
            (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u)))) (.classEq (syn_cec
              (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u))
                (.cv x)) (syn_chwniso A)) (.cv z)))
        (.classEq (.cv q) (syn_csn (syn_csn (.cv x)))))
      (syn_cfv (syn_ccom (syn_chnqmap1 A) (syn_csi
            (syn_chnwcutrel (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)))))
        (.cv q))
      (syn_cec (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u))
          (.cv x)) (syn_chwniso A))
      (.cv z) p0088 p0091
  have p0093 :=
    @g_jca
      (syn_wa (syn_wa (syn_wa (.classMem (.cv u) (syn_chwcn A))
            (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u)))) (.classEq (syn_cec
              (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u))
                (.cv x)) (syn_chwniso A)) (.cv z)))
        (.classEq (.cv q) (syn_csn (syn_csn (.cv x)))))
      (.classMem (.cv q) (syn_cpw1 (syn_cpw1 (syn_cfv (syn_c2nd) (.cv u)))))
      (.classEq (syn_cfv (syn_ccom (syn_chnqmap1 A) (syn_csi
              (syn_chnwcutrel (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)))))
          (.cv q)) (.cv z))
      p0050 p0092
  have p0094 := @g_id (.classEq (.cv p) (.cv q))
  have p0095 :=
    @g_fveq2d (.classEq (.cv p) (.cv q)) (.cv p) (.cv q)
      (syn_ccom (syn_chnqmap1 A) (syn_csi
          (syn_chnwcutrel (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)))))
      p0094
  have p0096 :=
    @g_eqeq1d (.classEq (.cv p) (.cv q))
      (syn_cfv (syn_ccom (syn_chnqmap1 A) (syn_csi
            (syn_chnwcutrel (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)))))
        (.cv p))
      (syn_cfv (syn_ccom (syn_chnqmap1 A) (syn_csi
            (syn_chnwcutrel (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)))))
        (.cv q))
      (.cv z) p0095
  have p0097 :=
    @g_rspcev
      (.classEq (syn_cfv (syn_ccom (syn_chnqmap1 A) (syn_csi
              (syn_chnwcutrel (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)))))
          (.cv p)) (.cv z))
      (.classEq (syn_cfv (syn_ccom (syn_chnqmap1 A) (syn_csi
              (syn_chnwcutrel (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)))))
          (.cv q)) (.cv z))
      p (.cv q) (syn_cpw1 (syn_cpw1 (syn_cfv (syn_c2nd) (.cv u)))) dv_cache_0018
      dv_cache_0002 dv_cache_0019 p0096
  have p0098 :=
    @g_syl
      (syn_wa (syn_wa (syn_wa (.classMem (.cv u) (syn_chwcn A))
            (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u)))) (.classEq (syn_cec
              (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u))
                (.cv x)) (syn_chwniso A)) (.cv z)))
        (.classEq (.cv q) (syn_csn (syn_csn (.cv x)))))
      (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_cpw1 (syn_cfv (syn_c2nd) (.cv u))))) (.classEq
          (syn_cfv (syn_ccom (syn_chnqmap1 A) (syn_csi
                (syn_chnwcutrel (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)))))
            (.cv q)) (.cv z)))
      (syn_wrex p (syn_cpw1 (syn_cpw1 (syn_cfv (syn_c2nd) (.cv u)))) (.classEq (syn_cfv
            (syn_ccom (syn_chnqmap1 A) (syn_csi (syn_chnwcutrel (syn_cfv (syn_c1st) (.cv u))
                  (syn_cfv (syn_c2nd) (.cv u))))) (.cv p)) (.cv z)))
      p0093 p0097
  have p0099 :=
    @g_exlimddv
      (syn_wa (syn_wa (.classMem (.cv u) (syn_chwcn A))
          (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u)))) (.classEq (syn_cec
            (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv x))
            (syn_chwniso A)) (.cv z)))
      (.classEq (.cv q) (syn_csn (syn_csn (.cv x))))
      (syn_wrex p (syn_cpw1 (syn_cpw1 (syn_cfv (syn_c2nd) (.cv u)))) (.classEq (syn_cfv
            (syn_ccom (syn_chnqmap1 A) (syn_csi (syn_chnwcutrel (syn_cfv (syn_c1st) (.cv u))
                  (syn_cfv (syn_c2nd) (.cv u))))) (.cv p)) (.cv z)))
      q dv_cache_0020 dv_cache_0021 p0036 p0098
  have p0100 :=
    @g_ex
      (syn_wa (.classMem (.cv u) (syn_chwcn A))
        (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u))))
      (.classEq (syn_cec
          (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv x))
          (syn_chwniso A)) (.cv z))
      (syn_wrex p (syn_cpw1 (syn_cpw1 (syn_cfv (syn_c2nd) (.cv u)))) (.classEq (syn_cfv
            (syn_ccom (syn_chnqmap1 A) (syn_csi (syn_chnwcutrel (syn_cfv (syn_c1st) (.cv u))
                  (syn_cfv (syn_c2nd) (.cv u))))) (.cv p)) (.cv z)))
      p0099
  have p0101 :=
    @g_ex (.classMem (.cv u) (syn_chwcn A))
      (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u)))
      (.imp (.classEq (syn_cec
            (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv x))
            (syn_chwniso A)) (.cv z))
        (syn_wrex p (syn_cpw1 (syn_cpw1 (syn_cfv (syn_c2nd) (.cv u)))) (.classEq (syn_cfv
              (syn_ccom (syn_chnqmap1 A) (syn_csi (syn_chnwcutrel (syn_cfv (syn_c1st) (.cv u))
                    (syn_cfv (syn_c2nd) (.cv u))))) (.cv p)) (.cv z))))
      p0100
  have p0102 :=
    @g_rexlimdv (.classMem (.cv u) (syn_chwcn A))
      (.classEq (syn_cec
          (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv x))
          (syn_chwniso A)) (.cv z))
      (syn_wrex p (syn_cpw1 (syn_cpw1 (syn_cfv (syn_c2nd) (.cv u)))) (.classEq (syn_cfv
            (syn_ccom (syn_chnqmap1 A) (syn_csi (syn_chnwcutrel (syn_cfv (syn_c1st) (.cv u))
                  (syn_cfv (syn_c2nd) (.cv u))))) (.cv p)) (.cv z)))
      x (syn_cfv (syn_c2nd) (.cv u)) dv_cache_0022 dv_cache_0023 p0101
  have p0103 :=
    @g_imp (.classMem (.cv u) (syn_chwcn A))
      (syn_wrex x (syn_cfv (syn_c2nd) (.cv u)) (.classEq (syn_cec
            (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv x))
            (syn_chwniso A)) (.cv z)))
      (syn_wrex p (syn_cpw1 (syn_cpw1 (syn_cfv (syn_c2nd) (.cv u)))) (.classEq (syn_cfv
            (syn_ccom (syn_chnqmap1 A) (syn_csi (syn_chnwcutrel (syn_cfv (syn_c1st) (.cv u))
                  (syn_cfv (syn_c2nd) (.cv u))))) (.cv p)) (.cv z)))
      p0102
  have p0104 :=
    @g_impbida (.classMem (.cv u) (syn_chwcn A))
      (syn_wrex p (syn_cpw1 (syn_cpw1 (syn_cfv (syn_c2nd) (.cv u)))) (.classEq (syn_cfv
            (syn_ccom (syn_chnqmap1 A) (syn_csi (syn_chnwcutrel (syn_cfv (syn_c1st) (.cv u))
                  (syn_cfv (syn_c2nd) (.cv u))))) (.cv p)) (.cv z)))
      (syn_wrex x (syn_cfv (syn_c2nd) (.cv u)) (.classEq (syn_cec
            (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv x))
            (syn_chwniso A)) (.cv z)))
      p0033 p0103
  have p0105 :=
    @g_bitrd (.classMem (.cv u) (syn_chwcn A))
      (.classMem (.cv z) (syn_crn (syn_ccom (syn_chnqmap1 A) (syn_csi
              (syn_chnwcutrel (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)))))))
      (syn_wrex p (syn_cpw1 (syn_cpw1 (syn_cfv (syn_c2nd) (.cv u)))) (.classEq (syn_cfv
            (syn_ccom (syn_chnqmap1 A) (syn_csi (syn_chnwcutrel (syn_cfv (syn_c1st) (.cv u))
                  (syn_cfv (syn_c2nd) (.cv u))))) (.cv p)) (.cv z)))
      (syn_wrex x (syn_cfv (syn_c2nd) (.cv u)) (.classEq (syn_cec
            (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv x))
            (syn_chwniso A)) (.cv z)))
      p0004 p0104
  exact p0105


end NFChoice.DirectNominalPrf.WPPReplay

end

/-! Certificates from `NominalWPPReplayChunk017Compact001Part081`. -/


section

namespace NFChoice.DirectNominalPrf.WPPReplay

open scoped Fol
open NFChoice.Foundation
open NFChoice.SemanticCore
open NFChoice.ReplaySupport
open NFChoice.Compiler.CompactSourceSyntax

@[expose]
noncomputable def g_hnwcutambstrictsegranimpndv (u : Var) (A : Class) (r : Var)
    (dv_A_r : r ∉ A.fv) (dv_A_u : u ∉ A.fv) (_dv_r_u : r ≠ u)
    (hyp_hnwcutstrictsegimp_1 : Nominal.NPrf (.classMem A (syn_cvv))) :
    Nominal.NPrf
      (.imp (syn_wa (.classEq (.cv r) (syn_chncodecmpset A)) (.classMem (.cv u) (syn_chwcn A)))
        (.classEq (syn_crn (syn_ccom (syn_chnqmap1 A) (syn_csi
                (syn_chnwcutrel (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u))))))
          (syn_cin (syn_chnord A)
            (syn_cima (syn_ccnv (syn_cdif (syn_clnqord (.cv r) (syn_chwcn A)) (syn_cid)))
              (syn_csn (syn_cec (.cv u) (syn_chwniso A))))))) :=
  by
  let proofSupport : Finset Var := ({ u } : Finset Var) ∪ A.fv ∪ ({ r } : Finset Var)
  let z : Var := freshVar proofSupport 0
  let x : Var := freshVar proofSupport 1
  let v : Var := freshVar proofSupport 2
  let w : Var := freshVar proofSupport 3
  let y : Var := freshVar proofSupport 4
  have fresh_z : z ∉ proofSupport :=
    by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_z_ne_u : z ≠ u := by
    intro h
    exact
      fresh_z
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_singleton.mpr h)))
  have fresh_z_not_A : z ∉ A.fv := by
    intro h
    exact fresh_z (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_z_ne_r : z ≠ r := by
    intro h
    exact fresh_z (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))
  have fresh_x : x ∉ proofSupport :=
    by
    change freshVar proofSupport 1 ∉ proofSupport
    exact freshVar_not_mem proofSupport 1
  have fresh_x_ne_u : x ≠ u := by
    intro h
    exact
      fresh_x
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_singleton.mpr h)))
  have fresh_u_ne_x : u ≠ x := Ne.symm fresh_x_ne_u
  have fresh_x_not_A : x ∉ A.fv := by
    intro h
    exact fresh_x (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_x_ne_r : x ≠ r := by
    intro h
    exact fresh_x (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))
  have fresh_v : v ∉ proofSupport :=
    by
    change freshVar proofSupport 2 ∉ proofSupport
    exact freshVar_not_mem proofSupport 2
  have fresh_v_ne_u : v ≠ u := by
    intro h
    exact
      fresh_v
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_singleton.mpr h)))
  have fresh_v_not_A : v ∉ A.fv := by
    intro h
    exact fresh_v (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_v_ne_r : v ≠ r := by
    intro h
    exact fresh_v (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))
  have fresh_w : w ∉ proofSupport :=
    by
    change freshVar proofSupport 3 ∉ proofSupport
    exact freshVar_not_mem proofSupport 3
  have fresh_w_ne_u : w ≠ u := by
    intro h
    exact
      fresh_w
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_singleton.mpr h)))
  have fresh_w_not_A : w ∉ A.fv := by
    intro h
    exact fresh_w (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_w_ne_r : w ≠ r := by
    intro h
    exact fresh_w (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))
  have fresh_y : y ∉ proofSupport :=
    by
    change freshVar proofSupport 4 ∉ proofSupport
    exact freshVar_not_mem proofSupport 4
  have fresh_y_ne_u : y ≠ u := by
    intro h
    exact
      fresh_y
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_singleton.mpr h)))
  have fresh_u_ne_y : u ≠ y := Ne.symm fresh_y_ne_u
  have fresh_y_not_A : y ∉ A.fv := by
    intro h
    exact fresh_y (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_y_ne_r : y ≠ r := by
    intro h
    exact fresh_y (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))
  have fresh_z_ne_x : z ≠ x :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have fresh_x_ne_z : x ≠ z := Ne.symm fresh_z_ne_x
  have fresh_z_ne_v : z ≠ v :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 2
    exact freshVar_injective proofSupport (i := 0) (j := 2) (by decide)
  have fresh_v_ne_z : v ≠ z := Ne.symm fresh_z_ne_v
  have fresh_x_ne_v : x ≠ v :=
    by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 2
    exact freshVar_injective proofSupport (i := 1) (j := 2) (by decide)
  have fresh_v_ne_x : v ≠ x := Ne.symm fresh_x_ne_v
  have fresh_x_ne_w : x ≠ w :=
    by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 3
    exact freshVar_injective proofSupport (i := 1) (j := 3) (by decide)
  have fresh_w_ne_x : w ≠ x := Ne.symm fresh_x_ne_w
  have fresh_x_ne_y : x ≠ y :=
    by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 4
    exact freshVar_injective proofSupport (i := 1) (j := 4) (by decide)
  have fresh_y_ne_x : y ≠ x := Ne.symm fresh_x_ne_y
  have fresh_w_ne_y : w ≠ y :=
    by
    change freshVar proofSupport 3 ≠ freshVar proofSupport 4
    exact freshVar_injective proofSupport (i := 3) (j := 4) (by decide)
  have fresh_y_ne_w : y ≠ w := Ne.symm fresh_w_ne_y
  have dv_cache_0001 : u ∉ (A).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : u ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_A_u, not_false_eq_true])
  have dv_cache_0002 : x ∉ (A).fv :=
    by
    clear dv_cache_0001
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_x_not_A, not_false_eq_true])
  have dv_cache_0003 : u ≠ x :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact (show u ≠ x from (by exact fresh_u_ne_x))
  have dv_cache_0004 : x ≠ z :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact (show x ≠ z from (by exact fresh_x_ne_z))
  have dv_cache_0005 : v ∉ (A).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact
      (by
        have compact_fv_not_mem_empty : v ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_v_not_A, not_false_eq_true])
  have dv_cache_0006 : v ∉ ((Class.cv z)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact
      (by
        have compact_fv_not_mem_empty : v ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_v_ne_z, not_false_eq_true])
  have dv_cache_0007 : r ∉ (A).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006
    exact
      (by
        have compact_fv_not_mem_empty : r ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_A_r, not_false_eq_true])
  have dv_cache_0008 : v ≠ u :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007
    exact (show v ≠ u from (by exact fresh_v_ne_u))
  have dv_cache_0009 : v ≠ x :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008
    exact (show v ≠ x from (by exact fresh_v_ne_x))
  have dv_cache_0010 :
    x ∉
      ((syn_wa (syn_wa (syn_wa (.classEq (.cv r) (syn_chncodecmpset A))
              (.classMem (.cv u) (syn_chwcn A))) (.classMem (.cv z) (syn_cin (syn_chnord A)
                (syn_cima (syn_ccnv (syn_cdif (syn_clnqord (.cv r) (syn_chwcn A)) (syn_cid)))
                  (syn_csn (syn_cec (.cv u) (syn_chwniso A)))))))
          (syn_wa (.classMem (.cv v) (syn_chwcn A))
            (.classEq (.cv z) (syn_cec (.cv v) (syn_chwniso A)))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chncodecmpset,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwcn,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chnord,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cima,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdif,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_clnqord,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cid,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cec,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwniso, Finset.mem_union,
          Finset.mem_singleton, fresh_x_ne_r, fresh_x_not_A, fresh_x_ne_u, fresh_x_ne_z,
          fresh_x_ne_v, compact_fv_not_mem_empty, or_false, not_false_eq_true])
  have dv_cache_0011 :
    v ∉
      ((syn_wrex x (syn_cfv (syn_c2nd) (.cv u)) (.classEq (syn_cec
              (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u))
                (.cv x)) (syn_chwniso A)) (.cv z)))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010
    exact
      (by
        have compact_fv_not_mem_empty : v ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wrex,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c2nd,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cec,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chnwcutcode,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1st,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwniso, Finset.mem_union,
          Finset.mem_erase, Finset.mem_singleton, fresh_v_ne_u, fresh_v_ne_x,
          fresh_v_not_A, fresh_v_ne_z, compact_fv_not_mem_empty, or_false, and_false,
          not_false_eq_true])
  have dv_cache_0012 :
    v ∉
      ((syn_wa (syn_wa (.classEq (.cv r) (syn_chncodecmpset A))
            (.classMem (.cv u) (syn_chwcn A))) (.classMem (.cv z) (syn_cin (syn_chnord A)
              (syn_cima (syn_ccnv (syn_cdif (syn_clnqord (.cv r) (syn_chwcn A)) (syn_cid)))
                (syn_csn (syn_cec (.cv u) (syn_chwniso A)))))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
    exact
      (by
        have compact_fv_not_mem_empty : v ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chncodecmpset,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwcn,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chnord,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cima,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdif,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_clnqord,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cid,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cec,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwniso, Finset.mem_union,
          Finset.mem_singleton, fresh_v_ne_r, fresh_v_not_A, fresh_v_ne_u, fresh_v_ne_z,
          compact_fv_not_mem_empty, or_false, not_false_eq_true])
  have dv_cache_0013 :
    w ∉
      ((syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u))
          (.cv x))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012
    exact
      (by
        have compact_fv_not_mem_empty : w ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chnwcutcode,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1st,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c2nd, Finset.mem_union,
          Finset.mem_singleton, fresh_w_ne_x, fresh_w_ne_u, compact_fv_not_mem_empty,
          or_false, not_false_eq_true])
  have dv_cache_0014 : w ∉ (A).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013
    exact
      (by
        have compact_fv_not_mem_empty : w ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_w_not_A, not_false_eq_true])
  have dv_cache_0015 : Disjoint ((Class.cv y)).fv ((syn_cfv (syn_c1st) (.cv u))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014
    exact
      (show Disjoint ((Class.cv y)).fv ((syn_cfv (syn_c1st) (.cv u))).fv from (by
          rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv,
            NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv];
          exact
            (show
              Disjoint (({ y } : Finset Var)) ((((Class.cv u)).fv) ∪ (((syn_c1st)).fv))
              from
              (Finset.disjoint_union_right.mpr
                ⟨(show Disjoint (({ y } : Finset Var)) (((Class.cv u)).fv) from
                    (by
                      rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv];
                      exact
                        (show Disjoint (({ y } : Finset Var)) (({ u } : Finset Var)) from
                          (Finset.disjoint_singleton_left.mpr
                            (show y ∉ ({ u } : Finset Var) from
                              (by
                                simpa only [Finset.mem_singleton] using
                                  (show y ≠ u from (by exact fresh_y_ne_u)))))))),
                  (show Disjoint (({ y } : Finset Var)) (((syn_c1st)).fv) from
                    (by
                      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1st];
                      exact
                        (show Disjoint (({ y } : Finset Var)) ((∅ : Finset Var)) from
                          (by simp))))⟩))))
  have dv_cache_0016 : y ∉ ((Class.cv x)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_y_ne_x, not_false_eq_true])
  have dv_cache_0017 : y ∉ ((syn_cfv (syn_c2nd) (.cv u))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c2nd,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, fresh_y_ne_u, compact_fv_not_mem_empty, or_false,
          not_false_eq_true])
  have dv_cache_0018 :
    y ∉
      ((syn_wbr (.cv w) (syn_chwniso A)
          (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u))
            (.cv x)))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwniso,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chnwcutcode,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1st,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c2nd, Finset.mem_union,
          Finset.mem_singleton, fresh_y_ne_w, fresh_y_ne_x, fresh_y_ne_u, fresh_y_not_A,
          compact_fv_not_mem_empty, or_false, not_false_eq_true])
  have dv_cache_0019 :
    y ∉
      ((syn_wa (syn_wa (syn_wa (.classEq (.cv r) (syn_chncodecmpset A))
              (.classMem (.cv u) (syn_chwcn A)))
            (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u)))) (.classEq (.cv w)
            (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u))
              (.cv x))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chncodecmpset,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwcn,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c2nd,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chnwcutcode,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1st, Finset.mem_union,
          Finset.mem_singleton, fresh_y_ne_r, fresh_y_not_A, fresh_y_ne_u, fresh_y_ne_x,
          fresh_y_ne_w, compact_fv_not_mem_empty, or_false, not_false_eq_true])
  have dv_cache_0020 : y ∉ (A).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_y_not_A, not_false_eq_true])
  have dv_cache_0021 : w ≠ u :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020
    exact (show w ≠ u from (by exact fresh_w_ne_u))
  have dv_cache_0022 : w ≠ y :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021
    exact (show w ≠ y from (by exact fresh_w_ne_y))
  have dv_cache_0023 : u ≠ y :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022
    exact (show u ≠ y from (by exact fresh_u_ne_y))
  have dv_cache_0024 :
    w ∉
      ((syn_wbr (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u))
            (.cv x)) (syn_cdif (syn_chncodecmpset A) (syn_ccnv (syn_chncodecmpset A)))
          (.cv u))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
    exact
      (by
        have compact_fv_not_mem_empty : w ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chnwcutcode,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1st,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c2nd,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdif,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chncodecmpset,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv, Finset.mem_union,
          Finset.mem_singleton, fresh_w_ne_x, fresh_w_ne_u, fresh_w_not_A,
          compact_fv_not_mem_empty, or_false, not_false_eq_true])
  have dv_cache_0025 :
    w ∉
      ((syn_wa (syn_wa (.classEq (.cv r) (syn_chncodecmpset A))
            (.classMem (.cv u) (syn_chwcn A)))
          (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024
    exact
      (by
        have compact_fv_not_mem_empty : w ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chncodecmpset,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwcn,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c2nd, Finset.mem_union,
          Finset.mem_singleton, fresh_w_ne_r, fresh_w_not_A, fresh_w_ne_u, fresh_w_ne_x,
          compact_fv_not_mem_empty, or_false, not_false_eq_true])
  have dv_cache_0026 :
    x ∉
      ((Wff.classMem (.cv z) (syn_cin (syn_chnord A)
            (syn_cima (syn_ccnv (syn_cdif (syn_clnqord (.cv r) (syn_chwcn A)) (syn_cid)))
              (syn_csn (syn_cec (.cv u) (syn_chwniso A))))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chnord,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cima,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdif,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_clnqord,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwcn,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cid,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cec,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwniso, Finset.mem_union,
          Finset.mem_singleton, fresh_x_ne_z, fresh_x_not_A, fresh_x_ne_r, fresh_x_ne_u,
          compact_fv_not_mem_empty, or_false, not_false_eq_true])
  have dv_cache_0027 :
    x ∉
      ((syn_wa (.classEq (.cv r) (syn_chncodecmpset A))
          (.classMem (.cv u) (syn_chwcn A)))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chncodecmpset,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwcn, Finset.mem_union,
          Finset.mem_singleton, fresh_x_ne_r, fresh_x_not_A, fresh_x_ne_u, or_false,
          not_false_eq_true])
  have dv_cache_0028 :
    z ∉
      ((syn_crn (syn_ccom (syn_chnqmap1 A) (syn_csi (syn_chnwcutrel (syn_cfv (syn_c1st) (.cv u))
                (syn_cfv (syn_c2nd) (.cv u))))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027
    exact
      (by
        have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_crn,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccom,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chnqmap1,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csi,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chnwcutrel,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1st,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c2nd, Finset.mem_union,
          Finset.mem_singleton, fresh_z_not_A, fresh_z_ne_u, compact_fv_not_mem_empty,
          or_false, not_false_eq_true])
  have dv_cache_0029 :
    z ∉
      ((syn_cin (syn_chnord A)
          (syn_cima (syn_ccnv (syn_cdif (syn_clnqord (.cv r) (syn_chwcn A)) (syn_cid)))
            (syn_csn (syn_cec (.cv u) (syn_chwniso A)))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028
    exact
      (by
        have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chnord,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cima,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdif,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_clnqord,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwcn,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cid,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cec,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwniso, Finset.mem_union,
          Finset.mem_singleton, fresh_z_not_A, fresh_z_ne_r, fresh_z_ne_u,
          compact_fv_not_mem_empty, or_false, not_false_eq_true])
  have dv_cache_0030 :
    z ∉
      ((syn_wa (.classEq (.cv r) (syn_chncodecmpset A))
          (.classMem (.cv u) (syn_chwcn A)))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
    exact
      (by
        have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chncodecmpset,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwcn, Finset.mem_union,
          Finset.mem_singleton, fresh_z_ne_r, fresh_z_not_A, fresh_z_ne_u, or_false,
          not_false_eq_true])
  have p0000 :=
    @g_simpr (.classEq (.cv r) (syn_chncodecmpset A)) (.classMem (.cv u) (syn_chwcn A))
  have p0001 :=
    @g_hnwcutambfactorranbrimpndv x z u A dv_cache_0001 dv_cache_0002 dv_cache_0003
      dv_cache_0004 hyp_hnwcutstrictsegimp_1
  have p0002 :=
    @g_syl
      (syn_wa (.classEq (.cv r) (syn_chncodecmpset A)) (.classMem (.cv u) (syn_chwcn A)))
      (.classMem (.cv u) (syn_chwcn A))
      (syn_wb (.classMem (.cv z) (syn_crn (syn_ccom (syn_chnqmap1 A) (syn_csi
                (syn_chnwcutrel (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)))))))
        (syn_wrex x (syn_cfv (syn_c2nd) (.cv u)) (.classEq (syn_cec
              (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u))
                (.cv x)) (syn_chwniso A)) (.cv z))))
      p0000 p0001
  have p0003 :=
    @g_simpr
      (syn_wa (.classEq (.cv r) (syn_chncodecmpset A)) (.classMem (.cv u) (syn_chwcn A)))
      (.classMem (.cv z) (syn_cin (syn_chnord A)
          (syn_cima (syn_ccnv (syn_cdif (syn_clnqord (.cv r) (syn_chwcn A)) (syn_cid)))
            (syn_csn (syn_cec (.cv u) (syn_chwniso A))))))
  have p0004 :=
    @g_elin (.cv z) (syn_chnord A)
      (syn_cima (syn_ccnv (syn_cdif (syn_clnqord (.cv r) (syn_chwcn A)) (syn_cid)))
        (syn_csn (syn_cec (.cv u) (syn_chwniso A))))
  have p0005 :=
    @g_biimpi
      (.classMem (.cv z) (syn_cin (syn_chnord A)
          (syn_cima (syn_ccnv (syn_cdif (syn_clnqord (.cv r) (syn_chwcn A)) (syn_cid)))
            (syn_csn (syn_cec (.cv u) (syn_chwniso A))))))
      (syn_wa (.classMem (.cv z) (syn_chnord A)) (.classMem (.cv z)
          (syn_cima (syn_ccnv (syn_cdif (syn_clnqord (.cv r) (syn_chwcn A)) (syn_cid)))
            (syn_csn (syn_cec (.cv u) (syn_chwniso A))))))
      p0004
  have p0006 :=
    @g_simpl (.classMem (.cv z) (syn_chnord A))
      (.classMem (.cv z)
        (syn_cima (syn_ccnv (syn_cdif (syn_clnqord (.cv r) (syn_chwcn A)) (syn_cid)))
          (syn_csn (syn_cec (.cv u) (syn_chwniso A)))))
  have p0007 :=
    @g_syl
      (.classMem (.cv z) (syn_cin (syn_chnord A)
          (syn_cima (syn_ccnv (syn_cdif (syn_clnqord (.cv r) (syn_chwcn A)) (syn_cid)))
            (syn_csn (syn_cec (.cv u) (syn_chwniso A))))))
      (syn_wa (.classMem (.cv z) (syn_chnord A)) (.classMem (.cv z)
          (syn_cima (syn_ccnv (syn_cdif (syn_clnqord (.cv r) (syn_chwcn A)) (syn_cid)))
            (syn_csn (syn_cec (.cv u) (syn_chwniso A))))))
      (.classMem (.cv z) (syn_chnord A)) p0005 p0006
  have p0008 :=
    @g_syl
      (syn_wa (syn_wa (.classEq (.cv r) (syn_chncodecmpset A))
          (.classMem (.cv u) (syn_chwcn A))) (.classMem (.cv z) (syn_cin (syn_chnord A)
            (syn_cima (syn_ccnv (syn_cdif (syn_clnqord (.cv r) (syn_chwcn A)) (syn_cid)))
              (syn_csn (syn_cec (.cv u) (syn_chwniso A)))))))
      (.classMem (.cv z) (syn_cin (syn_chnord A)
          (syn_cima (syn_ccnv (syn_cdif (syn_clnqord (.cv r) (syn_chwcn A)) (syn_cid)))
            (syn_csn (syn_cec (.cv u) (syn_chwniso A))))))
      (.classMem (.cv z) (syn_chnord A)) p0003 p0007
  have p0009 := @g_vex z
  have p0010 := @g_elhnordclndv v A (.cv z) dv_cache_0005 dv_cache_0006
  have p0011 := Nominal.mp p0009 p0010
  have p0012 :=
    @g_a1i
      (syn_wb (.classMem (.cv z) (syn_chnord A))
        (syn_wrex v (syn_chwcn A) (.classEq (.cv z) (syn_cec (.cv v) (syn_chwniso A)))))
      (syn_wa (syn_wa (.classEq (.cv r) (syn_chncodecmpset A))
          (.classMem (.cv u) (syn_chwcn A))) (.classMem (.cv z) (syn_cin (syn_chnord A)
            (syn_cima (syn_ccnv (syn_cdif (syn_clnqord (.cv r) (syn_chwcn A)) (syn_cid)))
              (syn_csn (syn_cec (.cv u) (syn_chwniso A)))))))
      p0011
  have p0013 :=
    @g_mpbid
      (syn_wa (syn_wa (.classEq (.cv r) (syn_chncodecmpset A))
          (.classMem (.cv u) (syn_chwcn A))) (.classMem (.cv z) (syn_cin (syn_chnord A)
            (syn_cima (syn_ccnv (syn_cdif (syn_clnqord (.cv r) (syn_chwcn A)) (syn_cid)))
              (syn_csn (syn_cec (.cv u) (syn_chwniso A)))))))
      (.classMem (.cv z) (syn_chnord A))
      (syn_wrex v (syn_chwcn A) (.classEq (.cv z) (syn_cec (.cv v) (syn_chwniso A))))
      p0008 p0012
  have p0014 :=
    @g_simpl
      (syn_wa (syn_wa (.classEq (.cv r) (syn_chncodecmpset A))
          (.classMem (.cv u) (syn_chwcn A))) (.classMem (.cv z) (syn_cin (syn_chnord A)
            (syn_cima (syn_ccnv (syn_cdif (syn_clnqord (.cv r) (syn_chwcn A)) (syn_cid)))
              (syn_csn (syn_cec (.cv u) (syn_chwniso A)))))))
      (syn_wa (.classMem (.cv v) (syn_chwcn A))
        (.classEq (.cv z) (syn_cec (.cv v) (syn_chwniso A))))
  have p0018 :=
    @g_simpr (.classMem (.cv z) (syn_chnord A))
      (.classMem (.cv z)
        (syn_cima (syn_ccnv (syn_cdif (syn_clnqord (.cv r) (syn_chwcn A)) (syn_cid)))
          (syn_csn (syn_cec (.cv u) (syn_chwniso A)))))
  have p0019 :=
    @g_syl
      (.classMem (.cv z) (syn_cin (syn_chnord A)
          (syn_cima (syn_ccnv (syn_cdif (syn_clnqord (.cv r) (syn_chwcn A)) (syn_cid)))
            (syn_csn (syn_cec (.cv u) (syn_chwniso A))))))
      (syn_wa (.classMem (.cv z) (syn_chnord A)) (.classMem (.cv z)
          (syn_cima (syn_ccnv (syn_cdif (syn_clnqord (.cv r) (syn_chwcn A)) (syn_cid)))
            (syn_csn (syn_cec (.cv u) (syn_chwniso A))))))
      (.classMem (.cv z)
        (syn_cima (syn_ccnv (syn_cdif (syn_clnqord (.cv r) (syn_chwcn A)) (syn_cid)))
          (syn_csn (syn_cec (.cv u) (syn_chwniso A)))))
      p0005 p0018
  have p0020 :=
    @g_eliniseg (syn_cdif (syn_clnqord (.cv r) (syn_chwcn A)) (syn_cid))
      (syn_cec (.cv u) (syn_chwniso A)) (.cv z)
  have p0021 :=
    @g_biimpi
      (.classMem (.cv z)
        (syn_cima (syn_ccnv (syn_cdif (syn_clnqord (.cv r) (syn_chwcn A)) (syn_cid)))
          (syn_csn (syn_cec (.cv u) (syn_chwniso A)))))
      (syn_wbr (.cv z) (syn_cdif (syn_clnqord (.cv r) (syn_chwcn A)) (syn_cid))
        (syn_cec (.cv u) (syn_chwniso A)))
      p0020
  have p0022 :=
    @g_syl
      (.classMem (.cv z) (syn_cin (syn_chnord A)
          (syn_cima (syn_ccnv (syn_cdif (syn_clnqord (.cv r) (syn_chwcn A)) (syn_cid)))
            (syn_csn (syn_cec (.cv u) (syn_chwniso A))))))
      (.classMem (.cv z)
        (syn_cima (syn_ccnv (syn_cdif (syn_clnqord (.cv r) (syn_chwcn A)) (syn_cid)))
          (syn_csn (syn_cec (.cv u) (syn_chwniso A)))))
      (syn_wbr (.cv z) (syn_cdif (syn_clnqord (.cv r) (syn_chwcn A)) (syn_cid))
        (syn_cec (.cv u) (syn_chwniso A)))
      p0019 p0021
  have p0023 :=
    @g_syl
      (syn_wa (syn_wa (.classEq (.cv r) (syn_chncodecmpset A))
          (.classMem (.cv u) (syn_chwcn A))) (.classMem (.cv z) (syn_cin (syn_chnord A)
            (syn_cima (syn_ccnv (syn_cdif (syn_clnqord (.cv r) (syn_chwcn A)) (syn_cid)))
              (syn_csn (syn_cec (.cv u) (syn_chwniso A)))))))
      (.classMem (.cv z) (syn_cin (syn_chnord A)
          (syn_cima (syn_ccnv (syn_cdif (syn_clnqord (.cv r) (syn_chwcn A)) (syn_cid)))
            (syn_csn (syn_cec (.cv u) (syn_chwniso A))))))
      (syn_wbr (.cv z) (syn_cdif (syn_clnqord (.cv r) (syn_chwcn A)) (syn_cid))
        (syn_cec (.cv u) (syn_chwniso A)))
      p0003 p0022
  have p0024 :=
    @g_syl
      (syn_wa (syn_wa (syn_wa (.classEq (.cv r) (syn_chncodecmpset A))
            (.classMem (.cv u) (syn_chwcn A))) (.classMem (.cv z) (syn_cin (syn_chnord A)
              (syn_cima (syn_ccnv (syn_cdif (syn_clnqord (.cv r) (syn_chwcn A)) (syn_cid)))
                (syn_csn (syn_cec (.cv u) (syn_chwniso A)))))))
        (syn_wa (.classMem (.cv v) (syn_chwcn A))
          (.classEq (.cv z) (syn_cec (.cv v) (syn_chwniso A)))))
      (syn_wa (syn_wa (.classEq (.cv r) (syn_chncodecmpset A))
          (.classMem (.cv u) (syn_chwcn A))) (.classMem (.cv z) (syn_cin (syn_chnord A)
            (syn_cima (syn_ccnv (syn_cdif (syn_clnqord (.cv r) (syn_chwcn A)) (syn_cid)))
              (syn_csn (syn_cec (.cv u) (syn_chwniso A)))))))
      (syn_wbr (.cv z) (syn_cdif (syn_clnqord (.cv r) (syn_chwcn A)) (syn_cid))
        (syn_cec (.cv u) (syn_chwniso A)))
      p0014 p0023
  have p0025 :=
    @g_simpr
      (syn_wa (syn_wa (.classEq (.cv r) (syn_chncodecmpset A))
          (.classMem (.cv u) (syn_chwcn A))) (.classMem (.cv z) (syn_cin (syn_chnord A)
            (syn_cima (syn_ccnv (syn_cdif (syn_clnqord (.cv r) (syn_chwcn A)) (syn_cid)))
              (syn_csn (syn_cec (.cv u) (syn_chwniso A)))))))
      (syn_wa (.classMem (.cv v) (syn_chwcn A))
        (.classEq (.cv z) (syn_cec (.cv v) (syn_chwniso A))))
  have p0026 :=
    @g_simprd
      (syn_wa (syn_wa (syn_wa (.classEq (.cv r) (syn_chncodecmpset A))
            (.classMem (.cv u) (syn_chwcn A))) (.classMem (.cv z) (syn_cin (syn_chnord A)
              (syn_cima (syn_ccnv (syn_cdif (syn_clnqord (.cv r) (syn_chwcn A)) (syn_cid)))
                (syn_csn (syn_cec (.cv u) (syn_chwniso A)))))))
        (syn_wa (.classMem (.cv v) (syn_chwcn A))
          (.classEq (.cv z) (syn_cec (.cv v) (syn_chwniso A)))))
      (.classMem (.cv v) (syn_chwcn A))
      (.classEq (.cv z) (syn_cec (.cv v) (syn_chwniso A))) p0025
  have p0027 :=
    @g_breq1d
      (syn_wa (syn_wa (syn_wa (.classEq (.cv r) (syn_chncodecmpset A))
            (.classMem (.cv u) (syn_chwcn A))) (.classMem (.cv z) (syn_cin (syn_chnord A)
              (syn_cima (syn_ccnv (syn_cdif (syn_clnqord (.cv r) (syn_chwcn A)) (syn_cid)))
                (syn_csn (syn_cec (.cv u) (syn_chwniso A)))))))
        (syn_wa (.classMem (.cv v) (syn_chwcn A))
          (.classEq (.cv z) (syn_cec (.cv v) (syn_chwniso A)))))
      (.cv z) (syn_cec (.cv v) (syn_chwniso A)) (syn_cec (.cv u) (syn_chwniso A))
      (syn_cdif (syn_clnqord (.cv r) (syn_chwcn A)) (syn_cid)) p0026
  have p0028 :=
    @g_mpbid
      (syn_wa (syn_wa (syn_wa (.classEq (.cv r) (syn_chncodecmpset A))
            (.classMem (.cv u) (syn_chwcn A))) (.classMem (.cv z) (syn_cin (syn_chnord A)
              (syn_cima (syn_ccnv (syn_cdif (syn_clnqord (.cv r) (syn_chwcn A)) (syn_cid)))
                (syn_csn (syn_cec (.cv u) (syn_chwniso A)))))))
        (syn_wa (.classMem (.cv v) (syn_chwcn A))
          (.classEq (.cv z) (syn_cec (.cv v) (syn_chwniso A)))))
      (syn_wbr (.cv z) (syn_cdif (syn_clnqord (.cv r) (syn_chwcn A)) (syn_cid))
        (syn_cec (.cv u) (syn_chwniso A)))
      (syn_wbr (syn_cec (.cv v) (syn_chwniso A))
        (syn_cdif (syn_clnqord (.cv r) (syn_chwcn A)) (syn_cid))
        (syn_cec (.cv u) (syn_chwniso A)))
      p0024 p0027
  have p0030 :=
    @g_simpl
      (syn_wa (.classEq (.cv r) (syn_chncodecmpset A)) (.classMem (.cv u) (syn_chwcn A)))
      (.classMem (.cv z) (syn_cin (syn_chnord A)
          (syn_cima (syn_ccnv (syn_cdif (syn_clnqord (.cv r) (syn_chwcn A)) (syn_cid)))
            (syn_csn (syn_cec (.cv u) (syn_chwniso A))))))
  have p0031 :=
    @g_syl
      (syn_wa (syn_wa (syn_wa (.classEq (.cv r) (syn_chncodecmpset A))
            (.classMem (.cv u) (syn_chwcn A))) (.classMem (.cv z) (syn_cin (syn_chnord A)
              (syn_cima (syn_ccnv (syn_cdif (syn_clnqord (.cv r) (syn_chwcn A)) (syn_cid)))
                (syn_csn (syn_cec (.cv u) (syn_chwniso A)))))))
        (syn_wa (.classMem (.cv v) (syn_chwcn A))
          (.classEq (.cv z) (syn_cec (.cv v) (syn_chwniso A)))))
      (syn_wa (syn_wa (.classEq (.cv r) (syn_chncodecmpset A))
          (.classMem (.cv u) (syn_chwcn A))) (.classMem (.cv z) (syn_cin (syn_chnord A)
            (syn_cima (syn_ccnv (syn_cdif (syn_clnqord (.cv r) (syn_chwcn A)) (syn_cid)))
              (syn_csn (syn_cec (.cv u) (syn_chwniso A)))))))
      (syn_wa (.classEq (.cv r) (syn_chncodecmpset A)) (.classMem (.cv u) (syn_chwcn A)))
      p0014 p0030
  have p0032 :=
    @g_simpl (.classEq (.cv r) (syn_chncodecmpset A)) (.classMem (.cv u) (syn_chwcn A))
  have p0033 :=
    @g_syl
      (syn_wa (syn_wa (syn_wa (.classEq (.cv r) (syn_chncodecmpset A))
            (.classMem (.cv u) (syn_chwcn A))) (.classMem (.cv z) (syn_cin (syn_chnord A)
              (syn_cima (syn_ccnv (syn_cdif (syn_clnqord (.cv r) (syn_chwcn A)) (syn_cid)))
                (syn_csn (syn_cec (.cv u) (syn_chwniso A)))))))
        (syn_wa (.classMem (.cv v) (syn_chwcn A))
          (.classEq (.cv z) (syn_cec (.cv v) (syn_chwniso A)))))
      (syn_wa (.classEq (.cv r) (syn_chncodecmpset A)) (.classMem (.cv u) (syn_chwcn A)))
      (.classEq (.cv r) (syn_chncodecmpset A)) p0031 p0032
  have p0035 :=
    @g_simpld
      (syn_wa (syn_wa (syn_wa (.classEq (.cv r) (syn_chncodecmpset A))
            (.classMem (.cv u) (syn_chwcn A))) (.classMem (.cv z) (syn_cin (syn_chnord A)
              (syn_cima (syn_ccnv (syn_cdif (syn_clnqord (.cv r) (syn_chwcn A)) (syn_cid)))
                (syn_csn (syn_cec (.cv u) (syn_chwniso A)))))))
        (syn_wa (.classMem (.cv v) (syn_chwcn A))
          (.classEq (.cv z) (syn_cec (.cv v) (syn_chwniso A)))))
      (.classMem (.cv v) (syn_chwcn A))
      (.classEq (.cv z) (syn_cec (.cv v) (syn_chwniso A))) p0025
  have p0040 :=
    @g_syl
      (syn_wa (syn_wa (syn_wa (.classEq (.cv r) (syn_chncodecmpset A))
            (.classMem (.cv u) (syn_chwcn A))) (.classMem (.cv z) (syn_cin (syn_chnord A)
              (syn_cima (syn_ccnv (syn_cdif (syn_clnqord (.cv r) (syn_chwcn A)) (syn_cid)))
                (syn_csn (syn_cec (.cv u) (syn_chwniso A)))))))
        (syn_wa (.classMem (.cv v) (syn_chwcn A))
          (.classEq (.cv z) (syn_cec (.cv v) (syn_chwniso A)))))
      (syn_wa (.classEq (.cv r) (syn_chncodecmpset A)) (.classMem (.cv u) (syn_chwcn A)))
      (.classMem (.cv u) (syn_chwcn A)) p0031 p0000
  have p0041 :=
    @g_jca
      (syn_wa (syn_wa (syn_wa (.classEq (.cv r) (syn_chncodecmpset A))
            (.classMem (.cv u) (syn_chwcn A))) (.classMem (.cv z) (syn_cin (syn_chnord A)
              (syn_cima (syn_ccnv (syn_cdif (syn_clnqord (.cv r) (syn_chwcn A)) (syn_cid)))
                (syn_csn (syn_cec (.cv u) (syn_chwniso A)))))))
        (syn_wa (.classMem (.cv v) (syn_chwcn A))
          (.classEq (.cv z) (syn_cec (.cv v) (syn_chwniso A)))))
      (.classMem (.cv v) (syn_chwcn A)) (.classMem (.cv u) (syn_chwcn A)) p0035 p0040
  have p0042 :=
    @g_jca
      (syn_wa (syn_wa (syn_wa (.classEq (.cv r) (syn_chncodecmpset A))
            (.classMem (.cv u) (syn_chwcn A))) (.classMem (.cv z) (syn_cin (syn_chnord A)
              (syn_cima (syn_ccnv (syn_cdif (syn_clnqord (.cv r) (syn_chwcn A)) (syn_cid)))
                (syn_csn (syn_cec (.cv u) (syn_chwniso A)))))))
        (syn_wa (.classMem (.cv v) (syn_chwcn A))
          (.classEq (.cv z) (syn_cec (.cv v) (syn_chwniso A)))))
      (.classEq (.cv r) (syn_chncodecmpset A))
      (syn_wa (.classMem (.cv v) (syn_chwcn A)) (.classMem (.cv u) (syn_chwcn A))) p0033
      p0041
  have p0043 :=
    @g_hncodecmpquotstrictbrproxyimpclndv A (.cv v) (.cv u) r dv_cache_0007
      hyp_hnwcutstrictsegimp_1
  have p0044 :=
    @g_syl
      (syn_wa (syn_wa (syn_wa (.classEq (.cv r) (syn_chncodecmpset A))
            (.classMem (.cv u) (syn_chwcn A))) (.classMem (.cv z) (syn_cin (syn_chnord A)
              (syn_cima (syn_ccnv (syn_cdif (syn_clnqord (.cv r) (syn_chwcn A)) (syn_cid)))
                (syn_csn (syn_cec (.cv u) (syn_chwniso A)))))))
        (syn_wa (.classMem (.cv v) (syn_chwcn A))
          (.classEq (.cv z) (syn_cec (.cv v) (syn_chwniso A)))))
      (syn_wa (.classEq (.cv r) (syn_chncodecmpset A))
        (syn_wa (.classMem (.cv v) (syn_chwcn A)) (.classMem (.cv u) (syn_chwcn A))))
      (syn_wb (syn_wbr (syn_cec (.cv v) (syn_chwniso A))
          (syn_cdif (syn_clnqord (.cv r) (syn_chwcn A)) (syn_cid))
          (syn_cec (.cv u) (syn_chwniso A)))
        (syn_wbr (.cv v) (syn_cdif (syn_chncodecmpset A) (syn_ccnv (syn_chncodecmpset A)))
          (.cv u)))
      p0042 p0043
  have p0045 :=
    @g_mpbid
      (syn_wa (syn_wa (syn_wa (.classEq (.cv r) (syn_chncodecmpset A))
            (.classMem (.cv u) (syn_chwcn A))) (.classMem (.cv z) (syn_cin (syn_chnord A)
              (syn_cima (syn_ccnv (syn_cdif (syn_clnqord (.cv r) (syn_chwcn A)) (syn_cid)))
                (syn_csn (syn_cec (.cv u) (syn_chwniso A)))))))
        (syn_wa (.classMem (.cv v) (syn_chwcn A))
          (.classEq (.cv z) (syn_cec (.cv v) (syn_chwniso A)))))
      (syn_wbr (syn_cec (.cv v) (syn_chwniso A))
        (syn_cdif (syn_clnqord (.cv r) (syn_chwcn A)) (syn_cid))
        (syn_cec (.cv u) (syn_chwniso A)))
      (syn_wbr (.cv v) (syn_cdif (syn_chncodecmpset A) (syn_ccnv (syn_chncodecmpset A)))
        (.cv u))
      p0028 p0044
  have p0046 :=
    @g_a1i (.classMem A (syn_cvv))
      (syn_wa (syn_wa (syn_wa (.classEq (.cv r) (syn_chncodecmpset A))
            (.classMem (.cv u) (syn_chwcn A))) (.classMem (.cv z) (syn_cin (syn_chnord A)
              (syn_cima (syn_ccnv (syn_cdif (syn_clnqord (.cv r) (syn_chwcn A)) (syn_cid)))
                (syn_csn (syn_cec (.cv u) (syn_chwniso A)))))))
        (syn_wa (.classMem (.cv v) (syn_chwcn A))
          (.classEq (.cv z) (syn_cec (.cv v) (syn_chwniso A)))))
      hyp_hnwcutstrictsegimp_1
  have p0055 :=
    @g_jca
      (syn_wa (syn_wa (syn_wa (.classEq (.cv r) (syn_chncodecmpset A))
            (.classMem (.cv u) (syn_chwcn A))) (.classMem (.cv z) (syn_cin (syn_chnord A)
              (syn_cima (syn_ccnv (syn_cdif (syn_clnqord (.cv r) (syn_chwcn A)) (syn_cid)))
                (syn_csn (syn_cec (.cv u) (syn_chwniso A)))))))
        (syn_wa (.classMem (.cv v) (syn_chwcn A))
          (.classEq (.cv z) (syn_cec (.cv v) (syn_chwniso A)))))
      (.classMem A (syn_cvv))
      (syn_wa (.classMem (.cv v) (syn_chwcn A)) (.classMem (.cv u) (syn_chwcn A))) p0046
      p0041
  have p0056 :=
    @g_hncodecmpstrictbrndv x u v A dv_cache_0005 dv_cache_0001 dv_cache_0002
      dv_cache_0008 dv_cache_0009 dv_cache_0003
  have p0057 :=
    @g_syl
      (syn_wa (syn_wa (syn_wa (.classEq (.cv r) (syn_chncodecmpset A))
            (.classMem (.cv u) (syn_chwcn A))) (.classMem (.cv z) (syn_cin (syn_chnord A)
              (syn_cima (syn_ccnv (syn_cdif (syn_clnqord (.cv r) (syn_chwcn A)) (syn_cid)))
                (syn_csn (syn_cec (.cv u) (syn_chwniso A)))))))
        (syn_wa (.classMem (.cv v) (syn_chwcn A))
          (.classEq (.cv z) (syn_cec (.cv v) (syn_chwniso A)))))
      (syn_wa (.classMem A (syn_cvv))
        (syn_wa (.classMem (.cv v) (syn_chwcn A)) (.classMem (.cv u) (syn_chwcn A))))
      (syn_wb (syn_wbr (.cv v) (syn_cdif (syn_chncodecmpset A) (syn_ccnv (syn_chncodecmpset A)))
          (.cv u)) (syn_wrex x (syn_cfv (syn_c2nd) (.cv u)) (syn_wbr (.cv v) (syn_chwniso A)
            (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u))
              (.cv x)))))
      p0055 p0056
  have p0058 :=
    @g_mpbid
      (syn_wa (syn_wa (syn_wa (.classEq (.cv r) (syn_chncodecmpset A))
            (.classMem (.cv u) (syn_chwcn A))) (.classMem (.cv z) (syn_cin (syn_chnord A)
              (syn_cima (syn_ccnv (syn_cdif (syn_clnqord (.cv r) (syn_chwcn A)) (syn_cid)))
                (syn_csn (syn_cec (.cv u) (syn_chwniso A)))))))
        (syn_wa (.classMem (.cv v) (syn_chwcn A))
          (.classEq (.cv z) (syn_cec (.cv v) (syn_chwniso A)))))
      (syn_wbr (.cv v) (syn_cdif (syn_chncodecmpset A) (syn_ccnv (syn_chncodecmpset A)))
        (.cv u))
      (syn_wrex x (syn_cfv (syn_c2nd) (.cv u)) (syn_wbr (.cv v) (syn_chwniso A)
          (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv x))))
      p0045 p0057
  have p0059 :=
    @g_simpr
      (syn_wa (syn_wa (syn_wa (syn_wa (.classEq (.cv r) (syn_chncodecmpset A))
              (.classMem (.cv u) (syn_chwcn A))) (.classMem (.cv z) (syn_cin (syn_chnord A)
                (syn_cima (syn_ccnv (syn_cdif (syn_clnqord (.cv r) (syn_chwcn A)) (syn_cid)))
                  (syn_csn (syn_cec (.cv u) (syn_chwniso A)))))))
          (syn_wa (.classMem (.cv v) (syn_chwcn A))
            (.classEq (.cv z) (syn_cec (.cv v) (syn_chwniso A)))))
        (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u))))
      (syn_wbr (.cv v) (syn_chwniso A)
        (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv x)))
  have p0060 :=
    @g_simpl
      (syn_wa (syn_wa (syn_wa (syn_wa (.classEq (.cv r) (syn_chncodecmpset A))
              (.classMem (.cv u) (syn_chwcn A))) (.classMem (.cv z) (syn_cin (syn_chnord A)
                (syn_cima (syn_ccnv (syn_cdif (syn_clnqord (.cv r) (syn_chwcn A)) (syn_cid)))
                  (syn_csn (syn_cec (.cv u) (syn_chwniso A)))))))
          (syn_wa (.classMem (.cv v) (syn_chwcn A))
            (.classEq (.cv z) (syn_cec (.cv v) (syn_chwniso A)))))
        (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u))))
      (syn_wbr (.cv v) (syn_chwniso A)
        (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv x)))
  have p0061 :=
    @g_simpl
      (syn_wa (syn_wa (syn_wa (.classEq (.cv r) (syn_chncodecmpset A))
            (.classMem (.cv u) (syn_chwcn A))) (.classMem (.cv z) (syn_cin (syn_chnord A)
              (syn_cima (syn_ccnv (syn_cdif (syn_clnqord (.cv r) (syn_chwcn A)) (syn_cid)))
                (syn_csn (syn_cec (.cv u) (syn_chwniso A)))))))
        (syn_wa (.classMem (.cv v) (syn_chwcn A))
          (.classEq (.cv z) (syn_cec (.cv v) (syn_chwniso A)))))
      (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u)))
  have p0062 :=
    @g_syl
      (syn_wa (syn_wa (syn_wa (syn_wa (syn_wa (.classEq (.cv r) (syn_chncodecmpset A))
                (.classMem (.cv u) (syn_chwcn A))) (.classMem (.cv z) (syn_cin (syn_chnord A)
                  (syn_cima (syn_ccnv (syn_cdif (syn_clnqord (.cv r) (syn_chwcn A)) (syn_cid)))
                    (syn_csn (syn_cec (.cv u) (syn_chwniso A)))))))
            (syn_wa (.classMem (.cv v) (syn_chwcn A))
              (.classEq (.cv z) (syn_cec (.cv v) (syn_chwniso A)))))
          (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u)))) (syn_wbr (.cv v) (syn_chwniso A)
          (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv x))))
      (syn_wa (syn_wa (syn_wa (syn_wa (.classEq (.cv r) (syn_chncodecmpset A))
              (.classMem (.cv u) (syn_chwcn A))) (.classMem (.cv z) (syn_cin (syn_chnord A)
                (syn_cima (syn_ccnv (syn_cdif (syn_clnqord (.cv r) (syn_chwcn A)) (syn_cid)))
                  (syn_csn (syn_cec (.cv u) (syn_chwniso A)))))))
          (syn_wa (.classMem (.cv v) (syn_chwcn A))
            (.classEq (.cv z) (syn_cec (.cv v) (syn_chwniso A)))))
        (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u))))
      (syn_wa (syn_wa (syn_wa (.classEq (.cv r) (syn_chncodecmpset A))
            (.classMem (.cv u) (syn_chwcn A))) (.classMem (.cv z) (syn_cin (syn_chnord A)
              (syn_cima (syn_ccnv (syn_cdif (syn_clnqord (.cv r) (syn_chwcn A)) (syn_cid)))
                (syn_csn (syn_cec (.cv u) (syn_chwniso A)))))))
        (syn_wa (.classMem (.cv v) (syn_chwcn A))
          (.classEq (.cv z) (syn_cec (.cv v) (syn_chwniso A)))))
      p0060 p0061
  have p0065 :=
    @g_syl
      (syn_wa (syn_wa (syn_wa (syn_wa (syn_wa (.classEq (.cv r) (syn_chncodecmpset A))
                (.classMem (.cv u) (syn_chwcn A))) (.classMem (.cv z) (syn_cin (syn_chnord A)
                  (syn_cima (syn_ccnv (syn_cdif (syn_clnqord (.cv r) (syn_chwcn A)) (syn_cid)))
                    (syn_csn (syn_cec (.cv u) (syn_chwniso A)))))))
            (syn_wa (.classMem (.cv v) (syn_chwcn A))
              (.classEq (.cv z) (syn_cec (.cv v) (syn_chwniso A)))))
          (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u)))) (syn_wbr (.cv v) (syn_chwniso A)
          (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv x))))
      (syn_wa (syn_wa (syn_wa (.classEq (.cv r) (syn_chncodecmpset A))
            (.classMem (.cv u) (syn_chwcn A))) (.classMem (.cv z) (syn_cin (syn_chnord A)
              (syn_cima (syn_ccnv (syn_cdif (syn_clnqord (.cv r) (syn_chwcn A)) (syn_cid)))
                (syn_csn (syn_cec (.cv u) (syn_chwniso A)))))))
        (syn_wa (.classMem (.cv v) (syn_chwcn A))
          (.classEq (.cv z) (syn_cec (.cv v) (syn_chwniso A)))))
      (.classMem (.cv v) (syn_chwcn A)) p0062 p0035
  have p0074 :=
    @g_syl
      (syn_wa (syn_wa (syn_wa (syn_wa (syn_wa (.classEq (.cv r) (syn_chncodecmpset A))
                (.classMem (.cv u) (syn_chwcn A))) (.classMem (.cv z) (syn_cin (syn_chnord A)
                  (syn_cima (syn_ccnv (syn_cdif (syn_clnqord (.cv r) (syn_chwcn A)) (syn_cid)))
                    (syn_csn (syn_cec (.cv u) (syn_chwniso A)))))))
            (syn_wa (.classMem (.cv v) (syn_chwcn A))
              (.classEq (.cv z) (syn_cec (.cv v) (syn_chwniso A)))))
          (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u)))) (syn_wbr (.cv v) (syn_chwniso A)
          (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv x))))
      (syn_wa (syn_wa (syn_wa (.classEq (.cv r) (syn_chncodecmpset A))
            (.classMem (.cv u) (syn_chwcn A))) (.classMem (.cv z) (syn_cin (syn_chnord A)
              (syn_cima (syn_ccnv (syn_cdif (syn_clnqord (.cv r) (syn_chwcn A)) (syn_cid)))
                (syn_csn (syn_cec (.cv u) (syn_chwniso A)))))))
        (syn_wa (.classMem (.cv v) (syn_chwcn A))
          (.classEq (.cv z) (syn_cec (.cv v) (syn_chwniso A)))))
      (.classMem (.cv u) (syn_chwcn A)) p0062 p0040
  have p0076 :=
    @g_simpr
      (syn_wa (syn_wa (syn_wa (.classEq (.cv r) (syn_chncodecmpset A))
            (.classMem (.cv u) (syn_chwcn A))) (.classMem (.cv z) (syn_cin (syn_chnord A)
              (syn_cima (syn_ccnv (syn_cdif (syn_clnqord (.cv r) (syn_chwcn A)) (syn_cid)))
                (syn_csn (syn_cec (.cv u) (syn_chwniso A)))))))
        (syn_wa (.classMem (.cv v) (syn_chwcn A))
          (.classEq (.cv z) (syn_cec (.cv v) (syn_chwniso A)))))
      (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u)))
  have p0077 :=
    @g_syl
      (syn_wa (syn_wa (syn_wa (syn_wa (syn_wa (.classEq (.cv r) (syn_chncodecmpset A))
                (.classMem (.cv u) (syn_chwcn A))) (.classMem (.cv z) (syn_cin (syn_chnord A)
                  (syn_cima (syn_ccnv (syn_cdif (syn_clnqord (.cv r) (syn_chwcn A)) (syn_cid)))
                    (syn_csn (syn_cec (.cv u) (syn_chwniso A)))))))
            (syn_wa (.classMem (.cv v) (syn_chwcn A))
              (.classEq (.cv z) (syn_cec (.cv v) (syn_chwniso A)))))
          (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u)))) (syn_wbr (.cv v) (syn_chwniso A)
          (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv x))))
      (syn_wa (syn_wa (syn_wa (syn_wa (.classEq (.cv r) (syn_chncodecmpset A))
              (.classMem (.cv u) (syn_chwcn A))) (.classMem (.cv z) (syn_cin (syn_chnord A)
                (syn_cima (syn_ccnv (syn_cdif (syn_clnqord (.cv r) (syn_chwcn A)) (syn_cid)))
                  (syn_csn (syn_cec (.cv u) (syn_chwniso A)))))))
          (syn_wa (.classMem (.cv v) (syn_chwcn A))
            (.classEq (.cv z) (syn_cec (.cv v) (syn_chwniso A)))))
        (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u))))
      (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u))) p0060 p0076
  have p0078 :=
    @g_jca
      (syn_wa (syn_wa (syn_wa (syn_wa (syn_wa (.classEq (.cv r) (syn_chncodecmpset A))
                (.classMem (.cv u) (syn_chwcn A))) (.classMem (.cv z) (syn_cin (syn_chnord A)
                  (syn_cima (syn_ccnv (syn_cdif (syn_clnqord (.cv r) (syn_chwcn A)) (syn_cid)))
                    (syn_csn (syn_cec (.cv u) (syn_chwniso A)))))))
            (syn_wa (.classMem (.cv v) (syn_chwcn A))
              (.classEq (.cv z) (syn_cec (.cv v) (syn_chwniso A)))))
          (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u)))) (syn_wbr (.cv v) (syn_chwniso A)
          (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv x))))
      (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u)))
      p0074 p0077
  have p0079 := @g_hnwcutcodeambientclndv u A (.cv x) dv_cache_0001
  have p0080 :=
    @g_syl
      (syn_wa (syn_wa (syn_wa (syn_wa (syn_wa (.classEq (.cv r) (syn_chncodecmpset A))
                (.classMem (.cv u) (syn_chwcn A))) (.classMem (.cv z) (syn_cin (syn_chnord A)
                  (syn_cima (syn_ccnv (syn_cdif (syn_clnqord (.cv r) (syn_chwcn A)) (syn_cid)))
                    (syn_csn (syn_cec (.cv u) (syn_chwniso A)))))))
            (syn_wa (.classMem (.cv v) (syn_chwcn A))
              (.classEq (.cv z) (syn_cec (.cv v) (syn_chwniso A)))))
          (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u)))) (syn_wbr (.cv v) (syn_chwniso A)
          (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv x))))
      (syn_wa (.classMem (.cv u) (syn_chwcn A))
        (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u))))
      (.classMem (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u))
          (.cv x)) (syn_chwcn A))
      p0078 p0079
  have p0081 :=
    @g_jca
      (syn_wa (syn_wa (syn_wa (syn_wa (syn_wa (.classEq (.cv r) (syn_chncodecmpset A))
                (.classMem (.cv u) (syn_chwcn A))) (.classMem (.cv z) (syn_cin (syn_chnord A)
                  (syn_cima (syn_ccnv (syn_cdif (syn_clnqord (.cv r) (syn_chwcn A)) (syn_cid)))
                    (syn_csn (syn_cec (.cv u) (syn_chwniso A)))))))
            (syn_wa (.classMem (.cv v) (syn_chwcn A))
              (.classEq (.cv z) (syn_cec (.cv v) (syn_chwniso A)))))
          (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u)))) (syn_wbr (.cv v) (syn_chwniso A)
          (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv x))))
      (.classMem (.cv v) (syn_chwcn A))
      (.classMem (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u))
          (.cv x)) (syn_chwcn A))
      p0065 p0080
  have p0082 :=
    @g_hwnisoclasseqbcl A (.cv v)
      (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv x))
      hyp_hnwcutstrictsegimp_1
  have p0083 :=
    @g_syl
      (syn_wa (syn_wa (syn_wa (syn_wa (syn_wa (.classEq (.cv r) (syn_chncodecmpset A))
                (.classMem (.cv u) (syn_chwcn A))) (.classMem (.cv z) (syn_cin (syn_chnord A)
                  (syn_cima (syn_ccnv (syn_cdif (syn_clnqord (.cv r) (syn_chwcn A)) (syn_cid)))
                    (syn_csn (syn_cec (.cv u) (syn_chwniso A)))))))
            (syn_wa (.classMem (.cv v) (syn_chwcn A))
              (.classEq (.cv z) (syn_cec (.cv v) (syn_chwniso A)))))
          (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u)))) (syn_wbr (.cv v) (syn_chwniso A)
          (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv x))))
      (syn_wa (.classMem (.cv v) (syn_chwcn A)) (.classMem
          (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv x))
          (syn_chwcn A)))
      (syn_wb (.classEq (syn_cec (.cv v) (syn_chwniso A)) (syn_cec
            (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv x))
            (syn_chwniso A))) (syn_wbr (.cv v) (syn_chwniso A)
          (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv x))))
      p0081 p0082
  have p0084 :=
    @g_mpbird
      (syn_wa (syn_wa (syn_wa (syn_wa (syn_wa (.classEq (.cv r) (syn_chncodecmpset A))
                (.classMem (.cv u) (syn_chwcn A))) (.classMem (.cv z) (syn_cin (syn_chnord A)
                  (syn_cima (syn_ccnv (syn_cdif (syn_clnqord (.cv r) (syn_chwcn A)) (syn_cid)))
                    (syn_csn (syn_cec (.cv u) (syn_chwniso A)))))))
            (syn_wa (.classMem (.cv v) (syn_chwcn A))
              (.classEq (.cv z) (syn_cec (.cv v) (syn_chwniso A)))))
          (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u)))) (syn_wbr (.cv v) (syn_chwniso A)
          (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv x))))
      (.classEq (syn_cec (.cv v) (syn_chwniso A)) (syn_cec
          (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv x))
          (syn_chwniso A)))
      (syn_wbr (.cv v) (syn_chwniso A)
        (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv x)))
      p0059 p0083
  have p0085 :=
    @g_eqcomd
      (syn_wa (syn_wa (syn_wa (syn_wa (syn_wa (.classEq (.cv r) (syn_chncodecmpset A))
                (.classMem (.cv u) (syn_chwcn A))) (.classMem (.cv z) (syn_cin (syn_chnord A)
                  (syn_cima (syn_ccnv (syn_cdif (syn_clnqord (.cv r) (syn_chwcn A)) (syn_cid)))
                    (syn_csn (syn_cec (.cv u) (syn_chwniso A)))))))
            (syn_wa (.classMem (.cv v) (syn_chwcn A))
              (.classEq (.cv z) (syn_cec (.cv v) (syn_chwniso A)))))
          (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u)))) (syn_wbr (.cv v) (syn_chwniso A)
          (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv x))))
      (syn_cec (.cv v) (syn_chwniso A))
      (syn_cec (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u))
          (.cv x)) (syn_chwniso A))
      p0084
  have p0091 :=
    @g_syl
      (syn_wa (syn_wa (syn_wa (syn_wa (syn_wa (.classEq (.cv r) (syn_chncodecmpset A))
                (.classMem (.cv u) (syn_chwcn A))) (.classMem (.cv z) (syn_cin (syn_chnord A)
                  (syn_cima (syn_ccnv (syn_cdif (syn_clnqord (.cv r) (syn_chwcn A)) (syn_cid)))
                    (syn_csn (syn_cec (.cv u) (syn_chwniso A)))))))
            (syn_wa (.classMem (.cv v) (syn_chwcn A))
              (.classEq (.cv z) (syn_cec (.cv v) (syn_chwniso A)))))
          (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u)))) (syn_wbr (.cv v) (syn_chwniso A)
          (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv x))))
      (syn_wa (syn_wa (syn_wa (.classEq (.cv r) (syn_chncodecmpset A))
            (.classMem (.cv u) (syn_chwcn A))) (.classMem (.cv z) (syn_cin (syn_chnord A)
              (syn_cima (syn_ccnv (syn_cdif (syn_clnqord (.cv r) (syn_chwcn A)) (syn_cid)))
                (syn_csn (syn_cec (.cv u) (syn_chwniso A)))))))
        (syn_wa (.classMem (.cv v) (syn_chwcn A))
          (.classEq (.cv z) (syn_cec (.cv v) (syn_chwniso A)))))
      (.classEq (.cv z) (syn_cec (.cv v) (syn_chwniso A))) p0062 p0026
  have p0092 :=
    @g_eqtr4d
      (syn_wa (syn_wa (syn_wa (syn_wa (syn_wa (.classEq (.cv r) (syn_chncodecmpset A))
                (.classMem (.cv u) (syn_chwcn A))) (.classMem (.cv z) (syn_cin (syn_chnord A)
                  (syn_cima (syn_ccnv (syn_cdif (syn_clnqord (.cv r) (syn_chwcn A)) (syn_cid)))
                    (syn_csn (syn_cec (.cv u) (syn_chwniso A)))))))
            (syn_wa (.classMem (.cv v) (syn_chwcn A))
              (.classEq (.cv z) (syn_cec (.cv v) (syn_chwniso A)))))
          (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u)))) (syn_wbr (.cv v) (syn_chwniso A)
          (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv x))))
      (syn_cec (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u))
          (.cv x)) (syn_chwniso A))
      (syn_cec (.cv v) (syn_chwniso A)) (.cv z) p0085 p0091
  have p0093 :=
    @g_ex
      (syn_wa (syn_wa (syn_wa (syn_wa (.classEq (.cv r) (syn_chncodecmpset A))
              (.classMem (.cv u) (syn_chwcn A))) (.classMem (.cv z) (syn_cin (syn_chnord A)
                (syn_cima (syn_ccnv (syn_cdif (syn_clnqord (.cv r) (syn_chwcn A)) (syn_cid)))
                  (syn_csn (syn_cec (.cv u) (syn_chwniso A)))))))
          (syn_wa (.classMem (.cv v) (syn_chwcn A))
            (.classEq (.cv z) (syn_cec (.cv v) (syn_chwniso A)))))
        (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u))))
      (syn_wbr (.cv v) (syn_chwniso A)
        (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv x)))
      (.classEq (syn_cec
          (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv x))
          (syn_chwniso A)) (.cv z))
      p0092
  have p0094 :=
    @g_reximdva
      (syn_wa (syn_wa (syn_wa (.classEq (.cv r) (syn_chncodecmpset A))
            (.classMem (.cv u) (syn_chwcn A))) (.classMem (.cv z) (syn_cin (syn_chnord A)
              (syn_cima (syn_ccnv (syn_cdif (syn_clnqord (.cv r) (syn_chwcn A)) (syn_cid)))
                (syn_csn (syn_cec (.cv u) (syn_chwniso A)))))))
        (syn_wa (.classMem (.cv v) (syn_chwcn A))
          (.classEq (.cv z) (syn_cec (.cv v) (syn_chwniso A)))))
      (syn_wbr (.cv v) (syn_chwniso A)
        (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv x)))
      (.classEq (syn_cec
          (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv x))
          (syn_chwniso A)) (.cv z))
      x (syn_cfv (syn_c2nd) (.cv u)) dv_cache_0010 p0093
  have p0095 :=
    @g_mpd
      (syn_wa (syn_wa (syn_wa (.classEq (.cv r) (syn_chncodecmpset A))
            (.classMem (.cv u) (syn_chwcn A))) (.classMem (.cv z) (syn_cin (syn_chnord A)
              (syn_cima (syn_ccnv (syn_cdif (syn_clnqord (.cv r) (syn_chwcn A)) (syn_cid)))
                (syn_csn (syn_cec (.cv u) (syn_chwniso A)))))))
        (syn_wa (.classMem (.cv v) (syn_chwcn A))
          (.classEq (.cv z) (syn_cec (.cv v) (syn_chwniso A)))))
      (syn_wrex x (syn_cfv (syn_c2nd) (.cv u)) (syn_wbr (.cv v) (syn_chwniso A)
          (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv x))))
      (syn_wrex x (syn_cfv (syn_c2nd) (.cv u)) (.classEq (syn_cec
            (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv x))
            (syn_chwniso A)) (.cv z)))
      p0058 p0094
  have p0096 :=
    @g_rexlimddv
      (syn_wa (syn_wa (.classEq (.cv r) (syn_chncodecmpset A))
          (.classMem (.cv u) (syn_chwcn A))) (.classMem (.cv z) (syn_cin (syn_chnord A)
            (syn_cima (syn_ccnv (syn_cdif (syn_clnqord (.cv r) (syn_chwcn A)) (syn_cid)))
              (syn_csn (syn_cec (.cv u) (syn_chwniso A)))))))
      (.classEq (.cv z) (syn_cec (.cv v) (syn_chwniso A)))
      (syn_wrex x (syn_cfv (syn_c2nd) (.cv u)) (.classEq (syn_cec
            (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv x))
            (syn_chwniso A)) (.cv z)))
      v (syn_chwcn A) dv_cache_0011 dv_cache_0012 p0013 p0095
  have p0097 :=
    @g_ex
      (syn_wa (.classEq (.cv r) (syn_chncodecmpset A)) (.classMem (.cv u) (syn_chwcn A)))
      (.classMem (.cv z) (syn_cin (syn_chnord A)
          (syn_cima (syn_ccnv (syn_cdif (syn_clnqord (.cv r) (syn_chwcn A)) (syn_cid)))
            (syn_csn (syn_cec (.cv u) (syn_chwniso A))))))
      (syn_wrex x (syn_cfv (syn_c2nd) (.cv u)) (.classEq (syn_cec
            (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv x))
            (syn_chwniso A)) (.cv z)))
      p0096
  have p0098 :=
    @g_simpl
      (syn_wa (syn_wa (.classEq (.cv r) (syn_chncodecmpset A))
          (.classMem (.cv u) (syn_chwcn A))) (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u))))
      (.classEq (syn_cec
          (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv x))
          (syn_chwniso A)) (.cv z))
  have p0099 :=
    @g_simpl
      (syn_wa (.classEq (.cv r) (syn_chncodecmpset A)) (.classMem (.cv u) (syn_chwcn A)))
      (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u)))
  have p0101 :=
    @g_syl
      (syn_wa (syn_wa (.classEq (.cv r) (syn_chncodecmpset A))
          (.classMem (.cv u) (syn_chwcn A))) (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u))))
      (syn_wa (.classEq (.cv r) (syn_chncodecmpset A)) (.classMem (.cv u) (syn_chwcn A)))
      (.classMem (.cv u) (syn_chwcn A)) p0099 p0000
  have p0102 :=
    @g_simpr
      (syn_wa (.classEq (.cv r) (syn_chncodecmpset A)) (.classMem (.cv u) (syn_chwcn A)))
      (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u)))
  have p0103 :=
    @g_jca
      (syn_wa (syn_wa (.classEq (.cv r) (syn_chncodecmpset A))
          (.classMem (.cv u) (syn_chwcn A))) (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u))))
      (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u)))
      p0101 p0102
  have p0105 :=
    @g_syl
      (syn_wa (syn_wa (.classEq (.cv r) (syn_chncodecmpset A))
          (.classMem (.cv u) (syn_chwcn A))) (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u))))
      (syn_wa (.classMem (.cv u) (syn_chwcn A))
        (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u))))
      (.classMem (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u))
          (.cv x)) (syn_chwcn A))
      p0103 p0079
  have p0106 :=
    @g_hwnisoclasselhnordcl A
      (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv x))
      hyp_hnwcutstrictsegimp_1
  have p0107 :=
    @g_syl
      (syn_wa (syn_wa (.classEq (.cv r) (syn_chncodecmpset A))
          (.classMem (.cv u) (syn_chwcn A))) (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u))))
      (.classMem (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u))
          (.cv x)) (syn_chwcn A))
      (.classMem (syn_cec
          (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv x))
          (syn_chwniso A)) (syn_chnord A))
      p0105 p0106
  have p0115 :=
    @g_elex
      (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv x))
      (syn_chwcn A)
  have p0116 :=
    @g_syl
      (syn_wa (syn_wa (.classEq (.cv r) (syn_chncodecmpset A))
          (.classMem (.cv u) (syn_chwcn A))) (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u))))
      (.classMem (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u))
          (.cv x)) (syn_chwcn A))
      (.classMem (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u))
          (.cv x)) (syn_cvv))
      p0105 p0115
  have p0117 :=
    @g_isset w
      (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv x))
      dv_cache_0013
  have p0118 :=
    @g_a1i
      (syn_wb (.classMem
          (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv x))
          (syn_cvv)) (syn_wex w (.classEq (.cv w)
            (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u))
              (.cv x)))))
      (syn_wa (syn_wa (.classEq (.cv r) (syn_chncodecmpset A))
          (.classMem (.cv u) (syn_chwcn A))) (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u))))
      p0117
  have p0119 :=
    @g_mpbid
      (syn_wa (syn_wa (.classEq (.cv r) (syn_chncodecmpset A))
          (.classMem (.cv u) (syn_chwcn A))) (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u))))
      (.classMem (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u))
          (.cv x)) (syn_cvv))
      (syn_wex w (.classEq (.cv w)
          (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv x))))
      p0116 p0118
  have p0120 :=
    @g_simpl
      (syn_wa (syn_wa (.classEq (.cv r) (syn_chncodecmpset A))
          (.classMem (.cv u) (syn_chwcn A))) (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u))))
      (.classEq (.cv w)
        (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv x)))
  have p0128 :=
    @g_syl
      (syn_wa (syn_wa (syn_wa (.classEq (.cv r) (syn_chncodecmpset A))
            (.classMem (.cv u) (syn_chwcn A))) (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u))))
        (.classEq (.cv w)
          (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv x))))
      (syn_wa (syn_wa (.classEq (.cv r) (syn_chncodecmpset A))
          (.classMem (.cv u) (syn_chwcn A))) (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u))))
      (.classMem (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u))
          (.cv x)) (syn_chwcn A))
      p0120 p0105
  have p0129 :=
    @g_simpr
      (syn_wa (syn_wa (.classEq (.cv r) (syn_chncodecmpset A))
          (.classMem (.cv u) (syn_chwcn A))) (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u))))
      (.classEq (.cv w)
        (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv x)))
  have p0130 :=
    @g_eleq1d
      (syn_wa (syn_wa (syn_wa (.classEq (.cv r) (syn_chncodecmpset A))
            (.classMem (.cv u) (syn_chwcn A))) (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u))))
        (.classEq (.cv w)
          (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv x))))
      (.cv w)
      (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv x))
      (syn_chwcn A) p0129
  have p0131 :=
    @g_mpbird
      (syn_wa (syn_wa (syn_wa (.classEq (.cv r) (syn_chncodecmpset A))
            (.classMem (.cv u) (syn_chwcn A))) (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u))))
        (.classEq (.cv w)
          (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv x))))
      (.classMem (.cv w) (syn_chwcn A))
      (.classMem (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u))
          (.cv x)) (syn_chwcn A))
      p0128 p0130
  have p0132 := @g_hwnisorefli w A dv_cache_0014
  have p0133 :=
    @g_syl
      (syn_wa (syn_wa (syn_wa (.classEq (.cv r) (syn_chncodecmpset A))
            (.classMem (.cv u) (syn_chwcn A))) (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u))))
        (.classEq (.cv w)
          (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv x))))
      (.classMem (.cv w) (syn_chwcn A)) (syn_wbr (.cv w) (syn_chwniso A) (.cv w)) p0131
      p0132
  have p0135 :=
    @g_breq2d
      (syn_wa (syn_wa (syn_wa (.classEq (.cv r) (syn_chncodecmpset A))
            (.classMem (.cv u) (syn_chwcn A))) (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u))))
        (.classEq (.cv w)
          (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv x))))
      (.cv w)
      (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv x))
      (.cv w) (syn_chwniso A) p0129
  have p0136 :=
    @g_mpbid
      (syn_wa (syn_wa (syn_wa (.classEq (.cv r) (syn_chncodecmpset A))
            (.classMem (.cv u) (syn_chwcn A))) (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u))))
        (.classEq (.cv w)
          (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv x))))
      (syn_wbr (.cv w) (syn_chwniso A) (.cv w))
      (syn_wbr (.cv w) (syn_chwniso A)
        (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv x)))
      p0133 p0135
  have p0139 :=
    @g_syl
      (syn_wa (syn_wa (syn_wa (.classEq (.cv r) (syn_chncodecmpset A))
            (.classMem (.cv u) (syn_chwcn A))) (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u))))
        (.classEq (.cv w)
          (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv x))))
      (syn_wa (syn_wa (.classEq (.cv r) (syn_chncodecmpset A))
          (.classMem (.cv u) (syn_chwcn A))) (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u))))
      (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u))) p0120 p0102
  have p0140 :=
    @g_simpr
      (syn_wa (syn_wa (syn_wa (.classEq (.cv r) (syn_chncodecmpset A))
            (.classMem (.cv u) (syn_chwcn A))) (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u))))
        (.classEq (.cv w)
          (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv x))))
      (.classEq (.cv y) (.cv x))
  have p0141 :=
    @g_hnwcutcodeeq3 (.cv y) (.cv x) (syn_cfv (syn_c2nd) (.cv u))
      (syn_cfv (syn_c1st) (.cv u)) dv_cache_0015
  have p0142 :=
    @g_syl
      (syn_wa (syn_wa (syn_wa (syn_wa (.classEq (.cv r) (syn_chncodecmpset A))
              (.classMem (.cv u) (syn_chwcn A)))
            (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u)))) (.classEq (.cv w)
            (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u))
              (.cv x)))) (.classEq (.cv y) (.cv x)))
      (.classEq (.cv y) (.cv x))
      (.classEq (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u))
          (.cv y)) (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u))
          (.cv x)))
      p0140 p0141
  have p0143 :=
    @g_breq2d
      (syn_wa (syn_wa (syn_wa (syn_wa (.classEq (.cv r) (syn_chncodecmpset A))
              (.classMem (.cv u) (syn_chwcn A)))
            (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u)))) (.classEq (.cv w)
            (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u))
              (.cv x)))) (.classEq (.cv y) (.cv x)))
      (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv y))
      (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv x))
      (.cv w) (syn_chwniso A) p0142
  have p0144 :=
    @g_rspcedv
      (syn_wa (syn_wa (syn_wa (.classEq (.cv r) (syn_chncodecmpset A))
            (.classMem (.cv u) (syn_chwcn A))) (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u))))
        (.classEq (.cv w)
          (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv x))))
      (syn_wbr (.cv w) (syn_chwniso A)
        (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv y)))
      (syn_wbr (.cv w) (syn_chwniso A)
        (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv x)))
      y (.cv x) (syn_cfv (syn_c2nd) (.cv u)) dv_cache_0016 dv_cache_0017 dv_cache_0018
      dv_cache_0019 p0139 p0143
  have p0145 :=
    @g_mpd
      (syn_wa (syn_wa (syn_wa (.classEq (.cv r) (syn_chncodecmpset A))
            (.classMem (.cv u) (syn_chwcn A))) (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u))))
        (.classEq (.cv w)
          (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv x))))
      (syn_wbr (.cv w) (syn_chwniso A)
        (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv x)))
      (syn_wrex y (syn_cfv (syn_c2nd) (.cv u)) (syn_wbr (.cv w) (syn_chwniso A)
          (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv y))))
      p0136 p0144
  have p0146 :=
    @g_a1i (.classMem A (syn_cvv))
      (syn_wa (syn_wa (syn_wa (.classEq (.cv r) (syn_chncodecmpset A))
            (.classMem (.cv u) (syn_chwcn A))) (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u))))
        (.classEq (.cv w)
          (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv x))))
      hyp_hnwcutstrictsegimp_1
  have p0163 :=
    @g_syl
      (syn_wa (syn_wa (syn_wa (.classEq (.cv r) (syn_chncodecmpset A))
            (.classMem (.cv u) (syn_chwcn A))) (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u))))
        (.classEq (.cv w)
          (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv x))))
      (syn_wa (syn_wa (.classEq (.cv r) (syn_chncodecmpset A))
          (.classMem (.cv u) (syn_chwcn A))) (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u))))
      (.classMem (.cv u) (syn_chwcn A)) p0120 p0101
  have p0164 :=
    @g_jca
      (syn_wa (syn_wa (syn_wa (.classEq (.cv r) (syn_chncodecmpset A))
            (.classMem (.cv u) (syn_chwcn A))) (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u))))
        (.classEq (.cv w)
          (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv x))))
      (.classMem (.cv w) (syn_chwcn A)) (.classMem (.cv u) (syn_chwcn A)) p0131 p0163
  have p0165 :=
    @g_jca
      (syn_wa (syn_wa (syn_wa (.classEq (.cv r) (syn_chncodecmpset A))
            (.classMem (.cv u) (syn_chwcn A))) (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u))))
        (.classEq (.cv w)
          (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv x))))
      (.classMem A (syn_cvv))
      (syn_wa (.classMem (.cv w) (syn_chwcn A)) (.classMem (.cv u) (syn_chwcn A))) p0146
      p0164
  have p0166 :=
    @g_hncodecmpstrictbrndv y u w A dv_cache_0014 dv_cache_0001 dv_cache_0020
      dv_cache_0021 dv_cache_0022 dv_cache_0023
  have p0167 :=
    @g_syl
      (syn_wa (syn_wa (syn_wa (.classEq (.cv r) (syn_chncodecmpset A))
            (.classMem (.cv u) (syn_chwcn A))) (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u))))
        (.classEq (.cv w)
          (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv x))))
      (syn_wa (.classMem A (syn_cvv))
        (syn_wa (.classMem (.cv w) (syn_chwcn A)) (.classMem (.cv u) (syn_chwcn A))))
      (syn_wb (syn_wbr (.cv w) (syn_cdif (syn_chncodecmpset A) (syn_ccnv (syn_chncodecmpset A)))
          (.cv u)) (syn_wrex y (syn_cfv (syn_c2nd) (.cv u)) (syn_wbr (.cv w) (syn_chwniso A)
            (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u))
              (.cv y)))))
      p0165 p0166
  have p0168 :=
    @g_mpbird
      (syn_wa (syn_wa (syn_wa (.classEq (.cv r) (syn_chncodecmpset A))
            (.classMem (.cv u) (syn_chwcn A))) (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u))))
        (.classEq (.cv w)
          (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv x))))
      (syn_wbr (.cv w) (syn_cdif (syn_chncodecmpset A) (syn_ccnv (syn_chncodecmpset A)))
        (.cv u))
      (syn_wrex y (syn_cfv (syn_c2nd) (.cv u)) (syn_wbr (.cv w) (syn_chwniso A)
          (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv y))))
      p0145 p0167
  have p0170 :=
    @g_breq1d
      (syn_wa (syn_wa (syn_wa (.classEq (.cv r) (syn_chncodecmpset A))
            (.classMem (.cv u) (syn_chwcn A))) (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u))))
        (.classEq (.cv w)
          (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv x))))
      (.cv w)
      (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv x))
      (.cv u) (syn_cdif (syn_chncodecmpset A) (syn_ccnv (syn_chncodecmpset A))) p0129
  have p0171 :=
    @g_mpbid
      (syn_wa (syn_wa (syn_wa (.classEq (.cv r) (syn_chncodecmpset A))
            (.classMem (.cv u) (syn_chwcn A))) (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u))))
        (.classEq (.cv w)
          (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv x))))
      (syn_wbr (.cv w) (syn_cdif (syn_chncodecmpset A) (syn_ccnv (syn_chncodecmpset A)))
        (.cv u))
      (syn_wbr (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u))
          (.cv x)) (syn_cdif (syn_chncodecmpset A) (syn_ccnv (syn_chncodecmpset A))) (.cv u))
      p0168 p0170
  have p0172 :=
    @g_exlimddv
      (syn_wa (syn_wa (.classEq (.cv r) (syn_chncodecmpset A))
          (.classMem (.cv u) (syn_chwcn A))) (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u))))
      (.classEq (.cv w)
        (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv x)))
      (syn_wbr (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u))
          (.cv x)) (syn_cdif (syn_chncodecmpset A) (syn_ccnv (syn_chncodecmpset A))) (.cv u))
      w dv_cache_0024 dv_cache_0025 p0119 p0171
  have p0175 :=
    @g_syl
      (syn_wa (syn_wa (.classEq (.cv r) (syn_chncodecmpset A))
          (.classMem (.cv u) (syn_chwcn A))) (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u))))
      (syn_wa (.classEq (.cv r) (syn_chncodecmpset A)) (.classMem (.cv u) (syn_chwcn A)))
      (.classEq (.cv r) (syn_chncodecmpset A)) p0099 p0032
  have p0186 :=
    @g_jca
      (syn_wa (syn_wa (.classEq (.cv r) (syn_chncodecmpset A))
          (.classMem (.cv u) (syn_chwcn A))) (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u))))
      (.classMem (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u))
          (.cv x)) (syn_chwcn A))
      (.classMem (.cv u) (syn_chwcn A)) p0105 p0101
  have p0187 :=
    @g_jca
      (syn_wa (syn_wa (.classEq (.cv r) (syn_chncodecmpset A))
          (.classMem (.cv u) (syn_chwcn A))) (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u))))
      (.classEq (.cv r) (syn_chncodecmpset A))
      (syn_wa (.classMem
          (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv x))
          (syn_chwcn A)) (.classMem (.cv u) (syn_chwcn A)))
      p0175 p0186
  have p0188 :=
    @g_hncodecmpquotstrictbrproxyimpclndv A
      (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv x))
      (.cv u) r dv_cache_0007 hyp_hnwcutstrictsegimp_1
  have p0189 :=
    @g_syl
      (syn_wa (syn_wa (.classEq (.cv r) (syn_chncodecmpset A))
          (.classMem (.cv u) (syn_chwcn A))) (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u))))
      (syn_wa (.classEq (.cv r) (syn_chncodecmpset A)) (syn_wa (.classMem
            (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv x))
            (syn_chwcn A)) (.classMem (.cv u) (syn_chwcn A))))
      (syn_wb (syn_wbr (syn_cec
            (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv x))
            (syn_chwniso A)) (syn_cdif (syn_clnqord (.cv r) (syn_chwcn A)) (syn_cid))
          (syn_cec (.cv u) (syn_chwniso A))) (syn_wbr
          (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv x))
          (syn_cdif (syn_chncodecmpset A) (syn_ccnv (syn_chncodecmpset A))) (.cv u)))
      p0187 p0188
  have p0190 :=
    @g_mpbird
      (syn_wa (syn_wa (.classEq (.cv r) (syn_chncodecmpset A))
          (.classMem (.cv u) (syn_chwcn A))) (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u))))
      (syn_wbr (syn_cec
          (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv x))
          (syn_chwniso A)) (syn_cdif (syn_clnqord (.cv r) (syn_chwcn A)) (syn_cid))
        (syn_cec (.cv u) (syn_chwniso A)))
      (syn_wbr (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u))
          (.cv x)) (syn_cdif (syn_chncodecmpset A) (syn_ccnv (syn_chncodecmpset A))) (.cv u))
      p0172 p0189
  have p0191 :=
    @g_eliniseg (syn_cdif (syn_clnqord (.cv r) (syn_chwcn A)) (syn_cid))
      (syn_cec (.cv u) (syn_chwniso A))
      (syn_cec (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u))
          (.cv x)) (syn_chwniso A))
  have p0192 :=
    @g_a1i
      (syn_wb (.classMem (syn_cec
            (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv x))
            (syn_chwniso A))
          (syn_cima (syn_ccnv (syn_cdif (syn_clnqord (.cv r) (syn_chwcn A)) (syn_cid)))
            (syn_csn (syn_cec (.cv u) (syn_chwniso A))))) (syn_wbr (syn_cec
            (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv x))
            (syn_chwniso A)) (syn_cdif (syn_clnqord (.cv r) (syn_chwcn A)) (syn_cid))
          (syn_cec (.cv u) (syn_chwniso A))))
      (syn_wa (syn_wa (.classEq (.cv r) (syn_chncodecmpset A))
          (.classMem (.cv u) (syn_chwcn A))) (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u))))
      p0191
  have p0193 :=
    @g_mpbird
      (syn_wa (syn_wa (.classEq (.cv r) (syn_chncodecmpset A))
          (.classMem (.cv u) (syn_chwcn A))) (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u))))
      (.classMem (syn_cec
          (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv x))
          (syn_chwniso A))
        (syn_cima (syn_ccnv (syn_cdif (syn_clnqord (.cv r) (syn_chwcn A)) (syn_cid)))
          (syn_csn (syn_cec (.cv u) (syn_chwniso A)))))
      (syn_wbr (syn_cec
          (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv x))
          (syn_chwniso A)) (syn_cdif (syn_clnqord (.cv r) (syn_chwcn A)) (syn_cid))
        (syn_cec (.cv u) (syn_chwniso A)))
      p0190 p0192
  have p0194 :=
    @g_jca
      (syn_wa (syn_wa (.classEq (.cv r) (syn_chncodecmpset A))
          (.classMem (.cv u) (syn_chwcn A))) (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u))))
      (.classMem (syn_cec
          (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv x))
          (syn_chwniso A)) (syn_chnord A))
      (.classMem (syn_cec
          (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv x))
          (syn_chwniso A))
        (syn_cima (syn_ccnv (syn_cdif (syn_clnqord (.cv r) (syn_chwcn A)) (syn_cid)))
          (syn_csn (syn_cec (.cv u) (syn_chwniso A)))))
      p0107 p0193
  have p0195 :=
    @g_elin
      (syn_cec (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u))
          (.cv x)) (syn_chwniso A))
      (syn_chnord A)
      (syn_cima (syn_ccnv (syn_cdif (syn_clnqord (.cv r) (syn_chwcn A)) (syn_cid)))
        (syn_csn (syn_cec (.cv u) (syn_chwniso A))))
  have p0196 :=
    @g_a1i
      (syn_wb (.classMem (syn_cec
            (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv x))
            (syn_chwniso A)) (syn_cin (syn_chnord A)
            (syn_cima (syn_ccnv (syn_cdif (syn_clnqord (.cv r) (syn_chwcn A)) (syn_cid)))
              (syn_csn (syn_cec (.cv u) (syn_chwniso A)))))) (syn_wa (.classMem (syn_cec
              (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u))
                (.cv x)) (syn_chwniso A)) (syn_chnord A)) (.classMem (syn_cec
              (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u))
                (.cv x)) (syn_chwniso A))
            (syn_cima (syn_ccnv (syn_cdif (syn_clnqord (.cv r) (syn_chwcn A)) (syn_cid)))
              (syn_csn (syn_cec (.cv u) (syn_chwniso A)))))))
      (syn_wa (syn_wa (.classEq (.cv r) (syn_chncodecmpset A))
          (.classMem (.cv u) (syn_chwcn A))) (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u))))
      p0195
  have p0197 :=
    @g_mpbird
      (syn_wa (syn_wa (.classEq (.cv r) (syn_chncodecmpset A))
          (.classMem (.cv u) (syn_chwcn A))) (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u))))
      (.classMem (syn_cec
          (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv x))
          (syn_chwniso A)) (syn_cin (syn_chnord A)
          (syn_cima (syn_ccnv (syn_cdif (syn_clnqord (.cv r) (syn_chwcn A)) (syn_cid)))
            (syn_csn (syn_cec (.cv u) (syn_chwniso A))))))
      (syn_wa (.classMem (syn_cec
            (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv x))
            (syn_chwniso A)) (syn_chnord A)) (.classMem (syn_cec
            (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv x))
            (syn_chwniso A))
          (syn_cima (syn_ccnv (syn_cdif (syn_clnqord (.cv r) (syn_chwcn A)) (syn_cid)))
            (syn_csn (syn_cec (.cv u) (syn_chwniso A))))))
      p0194 p0196
  have p0198 :=
    @g_syl
      (syn_wa (syn_wa (syn_wa (.classEq (.cv r) (syn_chncodecmpset A))
            (.classMem (.cv u) (syn_chwcn A))) (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u))))
        (.classEq (syn_cec
            (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv x))
            (syn_chwniso A)) (.cv z)))
      (syn_wa (syn_wa (.classEq (.cv r) (syn_chncodecmpset A))
          (.classMem (.cv u) (syn_chwcn A))) (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u))))
      (.classMem (syn_cec
          (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv x))
          (syn_chwniso A)) (syn_cin (syn_chnord A)
          (syn_cima (syn_ccnv (syn_cdif (syn_clnqord (.cv r) (syn_chwcn A)) (syn_cid)))
            (syn_csn (syn_cec (.cv u) (syn_chwniso A))))))
      p0098 p0197
  have p0199 :=
    @g_simpr
      (syn_wa (syn_wa (.classEq (.cv r) (syn_chncodecmpset A))
          (.classMem (.cv u) (syn_chwcn A))) (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u))))
      (.classEq (syn_cec
          (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv x))
          (syn_chwniso A)) (.cv z))
  have p0200 :=
    @g_eleq1d
      (syn_wa (syn_wa (syn_wa (.classEq (.cv r) (syn_chncodecmpset A))
            (.classMem (.cv u) (syn_chwcn A))) (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u))))
        (.classEq (syn_cec
            (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv x))
            (syn_chwniso A)) (.cv z)))
      (syn_cec (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u))
          (.cv x)) (syn_chwniso A))
      (.cv z)
      (syn_cin (syn_chnord A)
        (syn_cima (syn_ccnv (syn_cdif (syn_clnqord (.cv r) (syn_chwcn A)) (syn_cid)))
          (syn_csn (syn_cec (.cv u) (syn_chwniso A)))))
      p0199
  have p0201 :=
    @g_mpbid
      (syn_wa (syn_wa (syn_wa (.classEq (.cv r) (syn_chncodecmpset A))
            (.classMem (.cv u) (syn_chwcn A))) (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u))))
        (.classEq (syn_cec
            (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv x))
            (syn_chwniso A)) (.cv z)))
      (.classMem (syn_cec
          (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv x))
          (syn_chwniso A)) (syn_cin (syn_chnord A)
          (syn_cima (syn_ccnv (syn_cdif (syn_clnqord (.cv r) (syn_chwcn A)) (syn_cid)))
            (syn_csn (syn_cec (.cv u) (syn_chwniso A))))))
      (.classMem (.cv z) (syn_cin (syn_chnord A)
          (syn_cima (syn_ccnv (syn_cdif (syn_clnqord (.cv r) (syn_chwcn A)) (syn_cid)))
            (syn_csn (syn_cec (.cv u) (syn_chwniso A))))))
      p0198 p0200
  have p0202 :=
    @g_ex
      (syn_wa (syn_wa (.classEq (.cv r) (syn_chncodecmpset A))
          (.classMem (.cv u) (syn_chwcn A))) (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u))))
      (.classEq (syn_cec
          (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv x))
          (syn_chwniso A)) (.cv z))
      (.classMem (.cv z) (syn_cin (syn_chnord A)
          (syn_cima (syn_ccnv (syn_cdif (syn_clnqord (.cv r) (syn_chwcn A)) (syn_cid)))
            (syn_csn (syn_cec (.cv u) (syn_chwniso A))))))
      p0201
  have p0203 :=
    @g_rexlimdva
      (syn_wa (.classEq (.cv r) (syn_chncodecmpset A)) (.classMem (.cv u) (syn_chwcn A)))
      (.classEq (syn_cec
          (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv x))
          (syn_chwniso A)) (.cv z))
      (.classMem (.cv z) (syn_cin (syn_chnord A)
          (syn_cima (syn_ccnv (syn_cdif (syn_clnqord (.cv r) (syn_chwcn A)) (syn_cid)))
            (syn_csn (syn_cec (.cv u) (syn_chwniso A))))))
      x (syn_cfv (syn_c2nd) (.cv u)) dv_cache_0026 dv_cache_0027 p0202
  have p0204 :=
    @g_impbid
      (syn_wa (.classEq (.cv r) (syn_chncodecmpset A)) (.classMem (.cv u) (syn_chwcn A)))
      (.classMem (.cv z) (syn_cin (syn_chnord A)
          (syn_cima (syn_ccnv (syn_cdif (syn_clnqord (.cv r) (syn_chwcn A)) (syn_cid)))
            (syn_csn (syn_cec (.cv u) (syn_chwniso A))))))
      (syn_wrex x (syn_cfv (syn_c2nd) (.cv u)) (.classEq (syn_cec
            (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv x))
            (syn_chwniso A)) (.cv z)))
      p0097 p0203
  have p0205 :=
    @g_bitr4d
      (syn_wa (.classEq (.cv r) (syn_chncodecmpset A)) (.classMem (.cv u) (syn_chwcn A)))
      (.classMem (.cv z) (syn_crn (syn_ccom (syn_chnqmap1 A) (syn_csi
              (syn_chnwcutrel (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)))))))
      (syn_wrex x (syn_cfv (syn_c2nd) (.cv u)) (.classEq (syn_cec
            (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv x))
            (syn_chwniso A)) (.cv z)))
      (.classMem (.cv z) (syn_cin (syn_chnord A)
          (syn_cima (syn_ccnv (syn_cdif (syn_clnqord (.cv r) (syn_chwcn A)) (syn_cid)))
            (syn_csn (syn_cec (.cv u) (syn_chwniso A))))))
      p0002 p0204
  have p0206 :=
    @g_eqrdv
      (syn_wa (.classEq (.cv r) (syn_chncodecmpset A)) (.classMem (.cv u) (syn_chwcn A)))
      z
      (syn_crn (syn_ccom (syn_chnqmap1 A) (syn_csi
            (syn_chnwcutrel (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u))))))
      (syn_cin (syn_chnord A)
        (syn_cima (syn_ccnv (syn_cdif (syn_clnqord (.cv r) (syn_chwcn A)) (syn_cid)))
          (syn_csn (syn_cec (.cv u) (syn_chwniso A)))))
      dv_cache_0028 dv_cache_0029 dv_cache_0030 p0205
  exact p0206


end NFChoice.DirectNominalPrf.WPPReplay

end

/-! Certificates from `NominalWPPReplayChunk017Compact001Part082`. -/


section

namespace NFChoice.DirectNominalPrf.WPPReplay

open scoped Fol
open NFChoice.Foundation
open NFChoice.SemanticCore
open NFChoice.ReplaySupport
open NFChoice.Compiler.CompactSourceSyntax

@[expose]
noncomputable def g_hnwcutambstrictsegresisomralias0ndv (u : Var) (A : Class) (r : Var)
    (dv_A_r : r ∉ A.fv) (dv_A_u : u ∉ A.fv) (dv_r_u : r ≠ u)
    (hyp_hnwcutambstrictsegresisomralias0ndv_1 : Nominal.NPrf (.classMem A (syn_cvv))) :
    Nominal.NPrf
      (.imp (syn_wa (.classEq (.cv r) (syn_chncodecmpset A)) (.classMem (.cv u) (syn_chwcn A)))
        (syn_wiso (syn_ccom (syn_chnqmap1 A) (syn_csi
              (syn_chnwcutrel (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)))))
          (syn_csi (syn_csi (syn_cfv (syn_c1st) (.cv u))))
          (syn_cin (syn_clnqord (.cv r) (syn_chwcn A)) (syn_cxp (syn_cin (syn_chnord A)
                (syn_cima (syn_ccnv (syn_cdif (syn_clnqord (.cv r) (syn_chwcn A)) (syn_cid)))
                  (syn_csn (syn_cec (.cv u) (syn_chwniso A))))) (syn_cin (syn_chnord A)
                (syn_cima (syn_ccnv (syn_cdif (syn_clnqord (.cv r) (syn_chwcn A)) (syn_cid)))
                  (syn_csn (syn_cec (.cv u) (syn_chwniso A)))))))
          (syn_cpw1 (syn_cpw1 (syn_cfv (syn_c2nd) (.cv u)))) (syn_cin (syn_chnord A)
            (syn_cima (syn_ccnv (syn_cdif (syn_clnqord (.cv r) (syn_chwcn A)) (syn_cid)))
              (syn_csn (syn_cec (.cv u) (syn_chwniso A))))))) :=
  by
  let proofSupport : Finset Var := ({ u } : Finset Var) ∪ A.fv ∪ ({ r } : Finset Var)
  let p : Var := freshVar proofSupport 0
  let q : Var := freshVar proofSupport 1
  have fresh_p : p ∉ proofSupport :=
    by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_p_ne_u : p ≠ u := by
    intro h
    exact
      fresh_p
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_singleton.mpr h)))
  have fresh_p_not_A : p ∉ A.fv := by
    intro h
    exact fresh_p (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_p_ne_r : p ≠ r := by
    intro h
    exact fresh_p (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))
  have fresh_q : q ∉ proofSupport :=
    by
    change freshVar proofSupport 1 ∉ proofSupport
    exact freshVar_not_mem proofSupport 1
  have fresh_q_ne_u : q ≠ u := by
    intro h
    exact
      fresh_q
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_singleton.mpr h)))
  have fresh_q_not_A : q ∉ A.fv := by
    intro h
    exact fresh_q (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_q_ne_r : q ≠ r := by
    intro h
    exact fresh_q (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))
  have fresh_p_ne_q : p ≠ q :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have dv_cache_0001 : u ∉ (A).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : u ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_A_u, not_false_eq_true])
  have dv_cache_0002 : r ∉ (A).fv :=
    by
    clear dv_cache_0001
    exact
      (by
        have compact_fv_not_mem_empty : r ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_A_r, not_false_eq_true])
  have dv_cache_0003 : r ≠ u :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact (show r ≠ u from (by exact dv_r_u))
  have dv_cache_0004 : p ∉ (A).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact
      (by
        have compact_fv_not_mem_empty : p ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_p_not_A, not_false_eq_true])
  have dv_cache_0005 : q ∉ (A).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact
      (by
        have compact_fv_not_mem_empty : q ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_q_not_A, not_false_eq_true])
  have dv_cache_0006 : p ≠ q :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact (show p ≠ q from (by exact fresh_p_ne_q))
  have dv_cache_0007 : p ≠ r :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006
    exact (show p ≠ r from (by exact fresh_p_ne_r))
  have dv_cache_0008 : p ≠ u :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007
    exact (show p ≠ u from (by exact fresh_p_ne_u))
  have dv_cache_0009 : q ≠ r :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008
    exact (show q ≠ r from (by exact fresh_q_ne_r))
  have dv_cache_0010 : q ≠ u :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009
    exact (show q ≠ u from (by exact fresh_q_ne_u))
  have dv_cache_0011 : q ∉ ((syn_cpw1 (syn_cpw1 (syn_cfv (syn_c2nd) (.cv u))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010
    exact
      (by
        have compact_fv_not_mem_empty : q ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c2nd,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, fresh_q_ne_u, compact_fv_not_mem_empty, or_false,
          not_false_eq_true])
  have dv_cache_0012 :
    p ∉
      ((syn_wa (.classEq (.cv r) (syn_chncodecmpset A))
          (.classMem (.cv u) (syn_chwcn A)))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
    exact
      (by
        have compact_fv_not_mem_empty : p ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chncodecmpset,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwcn, Finset.mem_union,
          Finset.mem_singleton, fresh_p_ne_r, fresh_p_not_A, fresh_p_ne_u, or_false,
          not_false_eq_true])
  have dv_cache_0013 :
    q ∉
      ((syn_wa (.classEq (.cv r) (syn_chncodecmpset A))
          (.classMem (.cv u) (syn_chwcn A)))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012
    exact
      (by
        have compact_fv_not_mem_empty : q ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chncodecmpset,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwcn, Finset.mem_union,
          Finset.mem_singleton, fresh_q_ne_r, fresh_q_not_A, fresh_q_ne_u, or_false,
          not_false_eq_true])
  have dv_cache_0014 : p ∉ ((syn_cpw1 (syn_cpw1 (syn_cfv (syn_c2nd) (.cv u))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013
    exact
      (by
        have compact_fv_not_mem_empty : p ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c2nd,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, fresh_p_ne_u, compact_fv_not_mem_empty, or_false,
          not_false_eq_true])
  have dv_cache_0015 :
    p ∉
      ((syn_cin (syn_chnord A)
          (syn_cima (syn_ccnv (syn_cdif (syn_clnqord (.cv r) (syn_chwcn A)) (syn_cid)))
            (syn_csn (syn_cec (.cv u) (syn_chwniso A)))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014
    exact
      (by
        have compact_fv_not_mem_empty : p ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chnord,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cima,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdif,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_clnqord,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwcn,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cid,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cec,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwniso, Finset.mem_union,
          Finset.mem_singleton, fresh_p_not_A, fresh_p_ne_r, fresh_p_ne_u,
          compact_fv_not_mem_empty, or_false, not_false_eq_true])
  have dv_cache_0016 :
    q ∉
      ((syn_cin (syn_chnord A)
          (syn_cima (syn_ccnv (syn_cdif (syn_clnqord (.cv r) (syn_chwcn A)) (syn_cid)))
            (syn_csn (syn_cec (.cv u) (syn_chwniso A)))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015
    exact
      (by
        have compact_fv_not_mem_empty : q ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chnord,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cima,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdif,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_clnqord,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwcn,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cid,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cec,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwniso, Finset.mem_union,
          Finset.mem_singleton, fresh_q_not_A, fresh_q_ne_r, fresh_q_ne_u,
          compact_fv_not_mem_empty, or_false, not_false_eq_true])
  have dv_cache_0017 :
    p ∉
      ((syn_ccom (syn_chnqmap1 A) (syn_csi (syn_chnwcutrel (syn_cfv (syn_c1st) (.cv u))
              (syn_cfv (syn_c2nd) (.cv u)))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016
    exact
      (by
        have compact_fv_not_mem_empty : p ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccom,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chnqmap1,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csi,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chnwcutrel,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1st,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c2nd, Finset.mem_union,
          Finset.mem_singleton, fresh_p_not_A, fresh_p_ne_u, compact_fv_not_mem_empty,
          or_false, not_false_eq_true])
  have dv_cache_0018 :
    q ∉
      ((syn_ccom (syn_chnqmap1 A) (syn_csi (syn_chnwcutrel (syn_cfv (syn_c1st) (.cv u))
              (syn_cfv (syn_c2nd) (.cv u)))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
    exact
      (by
        have compact_fv_not_mem_empty : q ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccom,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chnqmap1,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csi,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chnwcutrel,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1st,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c2nd, Finset.mem_union,
          Finset.mem_singleton, fresh_q_not_A, fresh_q_ne_u, compact_fv_not_mem_empty,
          or_false, not_false_eq_true])
  have dv_cache_0019 : p ∉ ((syn_csi (syn_csi (syn_cfv (syn_c1st) (.cv u))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018
    exact
      (by
        have compact_fv_not_mem_empty : p ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csi,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1st,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, fresh_p_ne_u, compact_fv_not_mem_empty, or_false,
          not_false_eq_true])
  have dv_cache_0020 : q ∉ ((syn_csi (syn_csi (syn_cfv (syn_c1st) (.cv u))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019
    exact
      (by
        have compact_fv_not_mem_empty : q ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csi,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1st,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, fresh_q_ne_u, compact_fv_not_mem_empty, or_false,
          not_false_eq_true])
  have dv_cache_0021 : p ∉ ((syn_clnqord (.cv r) (syn_chwcn A))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020
    exact
      (by
        have compact_fv_not_mem_empty : p ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_clnqord,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwcn, Finset.mem_union,
          Finset.mem_singleton, fresh_p_not_A, fresh_p_ne_r, or_false, not_false_eq_true])
  have dv_cache_0022 : q ∉ ((syn_clnqord (.cv r) (syn_chwcn A))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021
    exact
      (by
        have compact_fv_not_mem_empty : q ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_clnqord,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwcn, Finset.mem_union,
          Finset.mem_singleton, fresh_q_not_A, fresh_q_ne_r, or_false, not_false_eq_true])
  have p0000 :=
    @g_simpr (.classEq (.cv r) (syn_chncodecmpset A)) (.classMem (.cv u) (syn_chwcn A))
  have p0001 :=
    @g_hnwcutambfactorf1impndv u A dv_cache_0001 hyp_hnwcutambstrictsegresisomralias0ndv_1
  have p0002 :=
    @g_syl
      (syn_wa (.classEq (.cv r) (syn_chncodecmpset A)) (.classMem (.cv u) (syn_chwcn A)))
      (.classMem (.cv u) (syn_chwcn A))
      (syn_wf1 (syn_ccom (syn_chnqmap1 A) (syn_csi
            (syn_chnwcutrel (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)))))
        (syn_cpw1 (syn_cpw1 (syn_cfv (syn_c2nd) (.cv u)))) (syn_chnord A))
      p0000 p0001
  have p0003 :=
    @g_f1f1orn (syn_cpw1 (syn_cpw1 (syn_cfv (syn_c2nd) (.cv u)))) (syn_chnord A)
      (syn_ccom (syn_chnqmap1 A) (syn_csi
          (syn_chnwcutrel (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)))))
  have p0004 :=
    @g_syl
      (syn_wa (.classEq (.cv r) (syn_chncodecmpset A)) (.classMem (.cv u) (syn_chwcn A)))
      (syn_wf1 (syn_ccom (syn_chnqmap1 A) (syn_csi
            (syn_chnwcutrel (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)))))
        (syn_cpw1 (syn_cpw1 (syn_cfv (syn_c2nd) (.cv u)))) (syn_chnord A))
      (syn_wf1o (syn_ccom (syn_chnqmap1 A) (syn_csi
            (syn_chnwcutrel (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)))))
        (syn_cpw1 (syn_cpw1 (syn_cfv (syn_c2nd) (.cv u)))) (syn_crn (syn_ccom (syn_chnqmap1 A)
            (syn_csi (syn_chnwcutrel (syn_cfv (syn_c1st) (.cv u))
                (syn_cfv (syn_c2nd) (.cv u)))))))
      p0002 p0003
  have p0005 :=
    @g_hnwcutambstrictsegranimpndv u A r dv_cache_0002 dv_cache_0001 dv_cache_0003
      hyp_hnwcutambstrictsegresisomralias0ndv_1
  have p0006 :=
    @g_f1oeq3
      (syn_crn (syn_ccom (syn_chnqmap1 A) (syn_csi
            (syn_chnwcutrel (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u))))))
      (syn_cin (syn_chnord A)
        (syn_cima (syn_ccnv (syn_cdif (syn_clnqord (.cv r) (syn_chwcn A)) (syn_cid)))
          (syn_csn (syn_cec (.cv u) (syn_chwniso A)))))
      (syn_cpw1 (syn_cpw1 (syn_cfv (syn_c2nd) (.cv u))))
      (syn_ccom (syn_chnqmap1 A) (syn_csi
          (syn_chnwcutrel (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)))))
  have p0007 :=
    @g_syl
      (syn_wa (.classEq (.cv r) (syn_chncodecmpset A)) (.classMem (.cv u) (syn_chwcn A)))
      (.classEq (syn_crn (syn_ccom (syn_chnqmap1 A) (syn_csi
              (syn_chnwcutrel (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u))))))
        (syn_cin (syn_chnord A)
          (syn_cima (syn_ccnv (syn_cdif (syn_clnqord (.cv r) (syn_chwcn A)) (syn_cid)))
            (syn_csn (syn_cec (.cv u) (syn_chwniso A))))))
      (syn_wb (syn_wf1o (syn_ccom (syn_chnqmap1 A) (syn_csi
              (syn_chnwcutrel (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)))))
          (syn_cpw1 (syn_cpw1 (syn_cfv (syn_c2nd) (.cv u)))) (syn_crn (syn_ccom (syn_chnqmap1 A)
              (syn_csi (syn_chnwcutrel (syn_cfv (syn_c1st) (.cv u))
                  (syn_cfv (syn_c2nd) (.cv u))))))) (syn_wf1o (syn_ccom (syn_chnqmap1 A)
            (syn_csi
              (syn_chnwcutrel (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)))))
          (syn_cpw1 (syn_cpw1 (syn_cfv (syn_c2nd) (.cv u)))) (syn_cin (syn_chnord A)
            (syn_cima (syn_ccnv (syn_cdif (syn_clnqord (.cv r) (syn_chwcn A)) (syn_cid)))
              (syn_csn (syn_cec (.cv u) (syn_chwniso A)))))))
      p0005 p0006
  have p0008 :=
    @g_mpbid
      (syn_wa (.classEq (.cv r) (syn_chncodecmpset A)) (.classMem (.cv u) (syn_chwcn A)))
      (syn_wf1o (syn_ccom (syn_chnqmap1 A) (syn_csi
            (syn_chnwcutrel (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)))))
        (syn_cpw1 (syn_cpw1 (syn_cfv (syn_c2nd) (.cv u)))) (syn_crn (syn_ccom (syn_chnqmap1 A)
            (syn_csi (syn_chnwcutrel (syn_cfv (syn_c1st) (.cv u))
                (syn_cfv (syn_c2nd) (.cv u)))))))
      (syn_wf1o (syn_ccom (syn_chnqmap1 A) (syn_csi
            (syn_chnwcutrel (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)))))
        (syn_cpw1 (syn_cpw1 (syn_cfv (syn_c2nd) (.cv u)))) (syn_cin (syn_chnord A)
          (syn_cima (syn_ccnv (syn_cdif (syn_clnqord (.cv r) (syn_chwcn A)) (syn_cid)))
            (syn_csn (syn_cec (.cv u) (syn_chwniso A))))))
      p0004 p0007
  have p0009 :=
    @g_hnwcutambordbrproxyimpndv u A r q p dv_cache_0004 dv_cache_0005 dv_cache_0002
      dv_cache_0001 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010
      dv_cache_0003 hyp_hnwcutambstrictsegresisomralias0ndv_1
  have p0010 :=
    @g_ralrimivva
      (syn_wa (.classEq (.cv r) (syn_chncodecmpset A)) (.classMem (.cv u) (syn_chwcn A)))
      (syn_wb (syn_wbr (.cv p) (syn_csi (syn_csi (syn_cfv (syn_c1st) (.cv u)))) (.cv q))
        (syn_wbr (syn_cfv (syn_ccom (syn_chnqmap1 A) (syn_csi
                (syn_chnwcutrel (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)))))
            (.cv p)) (syn_clnqord (.cv r) (syn_chwcn A)) (syn_cfv (syn_ccom (syn_chnqmap1 A)
              (syn_csi (syn_chnwcutrel (syn_cfv (syn_c1st) (.cv u))
                  (syn_cfv (syn_c2nd) (.cv u))))) (.cv q))))
      p q (syn_cpw1 (syn_cpw1 (syn_cfv (syn_c2nd) (.cv u))))
      (syn_cpw1 (syn_cpw1 (syn_cfv (syn_c2nd) (.cv u)))) dv_cache_0011 dv_cache_0012
      dv_cache_0013 dv_cache_0006 p0009
  have p0011 :=
    @g_jca
      (syn_wa (.classEq (.cv r) (syn_chncodecmpset A)) (.classMem (.cv u) (syn_chwcn A)))
      (syn_wf1o (syn_ccom (syn_chnqmap1 A) (syn_csi
            (syn_chnwcutrel (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)))))
        (syn_cpw1 (syn_cpw1 (syn_cfv (syn_c2nd) (.cv u)))) (syn_cin (syn_chnord A)
          (syn_cima (syn_ccnv (syn_cdif (syn_clnqord (.cv r) (syn_chwcn A)) (syn_cid)))
            (syn_csn (syn_cec (.cv u) (syn_chwniso A))))))
      (syn_wral p (syn_cpw1 (syn_cpw1 (syn_cfv (syn_c2nd) (.cv u))))
        (syn_wral q (syn_cpw1 (syn_cpw1 (syn_cfv (syn_c2nd) (.cv u)))) (syn_wb
            (syn_wbr (.cv p) (syn_csi (syn_csi (syn_cfv (syn_c1st) (.cv u)))) (.cv q)) (syn_wbr
              (syn_cfv (syn_ccom (syn_chnqmap1 A) (syn_csi
                    (syn_chnwcutrel (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)))))
                (.cv p)) (syn_clnqord (.cv r) (syn_chwcn A)) (syn_cfv (syn_ccom (syn_chnqmap1 A)
                  (syn_csi (syn_chnwcutrel (syn_cfv (syn_c1st) (.cv u))
                      (syn_cfv (syn_c2nd) (.cv u))))) (.cv q))))))
      p0008 p0010
  have p0012 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominal_df_iso p q
      (syn_cpw1 (syn_cpw1 (syn_cfv (syn_c2nd) (.cv u))))
      (syn_cin (syn_chnord A)
        (syn_cima (syn_ccnv (syn_cdif (syn_clnqord (.cv r) (syn_chwcn A)) (syn_cid)))
          (syn_csn (syn_cec (.cv u) (syn_chwniso A)))))
      (syn_csi (syn_csi (syn_cfv (syn_c1st) (.cv u)))) (syn_clnqord (.cv r) (syn_chwcn A))
      (syn_ccom (syn_chnqmap1 A) (syn_csi
          (syn_chnwcutrel (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)))))
      dv_cache_0014 dv_cache_0011 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018
      dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0006
  have p0013 :=
    @g_biimpri
      (syn_wiso (syn_ccom (syn_chnqmap1 A) (syn_csi
            (syn_chnwcutrel (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)))))
        (syn_csi (syn_csi (syn_cfv (syn_c1st) (.cv u)))) (syn_clnqord (.cv r) (syn_chwcn A))
        (syn_cpw1 (syn_cpw1 (syn_cfv (syn_c2nd) (.cv u)))) (syn_cin (syn_chnord A)
          (syn_cima (syn_ccnv (syn_cdif (syn_clnqord (.cv r) (syn_chwcn A)) (syn_cid)))
            (syn_csn (syn_cec (.cv u) (syn_chwniso A))))))
      (syn_wa (syn_wf1o (syn_ccom (syn_chnqmap1 A) (syn_csi
              (syn_chnwcutrel (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)))))
          (syn_cpw1 (syn_cpw1 (syn_cfv (syn_c2nd) (.cv u)))) (syn_cin (syn_chnord A)
            (syn_cima (syn_ccnv (syn_cdif (syn_clnqord (.cv r) (syn_chwcn A)) (syn_cid)))
              (syn_csn (syn_cec (.cv u) (syn_chwniso A))))))
        (syn_wral p (syn_cpw1 (syn_cpw1 (syn_cfv (syn_c2nd) (.cv u))))
          (syn_wral q (syn_cpw1 (syn_cpw1 (syn_cfv (syn_c2nd) (.cv u)))) (syn_wb
              (syn_wbr (.cv p) (syn_csi (syn_csi (syn_cfv (syn_c1st) (.cv u)))) (.cv q))
              (syn_wbr (syn_cfv (syn_ccom (syn_chnqmap1 A) (syn_csi
                      (syn_chnwcutrel (syn_cfv (syn_c1st) (.cv u))
                        (syn_cfv (syn_c2nd) (.cv u))))) (.cv p))
                (syn_clnqord (.cv r) (syn_chwcn A)) (syn_cfv (syn_ccom (syn_chnqmap1 A) (syn_csi
                      (syn_chnwcutrel (syn_cfv (syn_c1st) (.cv u))
                        (syn_cfv (syn_c2nd) (.cv u))))) (.cv q)))))))
      p0012
  have p0014 :=
    @g_syl
      (syn_wa (.classEq (.cv r) (syn_chncodecmpset A)) (.classMem (.cv u) (syn_chwcn A)))
      (syn_wa (syn_wf1o (syn_ccom (syn_chnqmap1 A) (syn_csi
              (syn_chnwcutrel (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)))))
          (syn_cpw1 (syn_cpw1 (syn_cfv (syn_c2nd) (.cv u)))) (syn_cin (syn_chnord A)
            (syn_cima (syn_ccnv (syn_cdif (syn_clnqord (.cv r) (syn_chwcn A)) (syn_cid)))
              (syn_csn (syn_cec (.cv u) (syn_chwniso A))))))
        (syn_wral p (syn_cpw1 (syn_cpw1 (syn_cfv (syn_c2nd) (.cv u))))
          (syn_wral q (syn_cpw1 (syn_cpw1 (syn_cfv (syn_c2nd) (.cv u)))) (syn_wb
              (syn_wbr (.cv p) (syn_csi (syn_csi (syn_cfv (syn_c1st) (.cv u)))) (.cv q))
              (syn_wbr (syn_cfv (syn_ccom (syn_chnqmap1 A) (syn_csi
                      (syn_chnwcutrel (syn_cfv (syn_c1st) (.cv u))
                        (syn_cfv (syn_c2nd) (.cv u))))) (.cv p))
                (syn_clnqord (.cv r) (syn_chwcn A)) (syn_cfv (syn_ccom (syn_chnqmap1 A) (syn_csi
                      (syn_chnwcutrel (syn_cfv (syn_c1st) (.cv u))
                        (syn_cfv (syn_c2nd) (.cv u))))) (.cv q)))))))
      (syn_wiso (syn_ccom (syn_chnqmap1 A) (syn_csi
            (syn_chnwcutrel (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)))))
        (syn_csi (syn_csi (syn_cfv (syn_c1st) (.cv u)))) (syn_clnqord (.cv r) (syn_chwcn A))
        (syn_cpw1 (syn_cpw1 (syn_cfv (syn_c2nd) (.cv u)))) (syn_cin (syn_chnord A)
          (syn_cima (syn_ccnv (syn_cdif (syn_clnqord (.cv r) (syn_chwcn A)) (syn_cid)))
            (syn_csn (syn_cec (.cv u) (syn_chwniso A))))))
      p0011 p0013
  have p0015 :=
    @g_isores2 (syn_cpw1 (syn_cpw1 (syn_cfv (syn_c2nd) (.cv u))))
      (syn_cin (syn_chnord A)
        (syn_cima (syn_ccnv (syn_cdif (syn_clnqord (.cv r) (syn_chwcn A)) (syn_cid)))
          (syn_csn (syn_cec (.cv u) (syn_chwniso A)))))
      (syn_csi (syn_csi (syn_cfv (syn_c1st) (.cv u)))) (syn_clnqord (.cv r) (syn_chwcn A))
      (syn_ccom (syn_chnqmap1 A) (syn_csi
          (syn_chnwcutrel (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)))))
  have p0016 :=
    @g_a1i
      (syn_wb (syn_wiso (syn_ccom (syn_chnqmap1 A) (syn_csi
              (syn_chnwcutrel (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)))))
          (syn_csi (syn_csi (syn_cfv (syn_c1st) (.cv u)))) (syn_clnqord (.cv r) (syn_chwcn A))
          (syn_cpw1 (syn_cpw1 (syn_cfv (syn_c2nd) (.cv u)))) (syn_cin (syn_chnord A)
            (syn_cima (syn_ccnv (syn_cdif (syn_clnqord (.cv r) (syn_chwcn A)) (syn_cid)))
              (syn_csn (syn_cec (.cv u) (syn_chwniso A)))))) (syn_wiso
          (syn_ccom (syn_chnqmap1 A) (syn_csi
              (syn_chnwcutrel (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)))))
          (syn_csi (syn_csi (syn_cfv (syn_c1st) (.cv u))))
          (syn_cin (syn_clnqord (.cv r) (syn_chwcn A)) (syn_cxp (syn_cin (syn_chnord A)
                (syn_cima (syn_ccnv (syn_cdif (syn_clnqord (.cv r) (syn_chwcn A)) (syn_cid)))
                  (syn_csn (syn_cec (.cv u) (syn_chwniso A))))) (syn_cin (syn_chnord A)
                (syn_cima (syn_ccnv (syn_cdif (syn_clnqord (.cv r) (syn_chwcn A)) (syn_cid)))
                  (syn_csn (syn_cec (.cv u) (syn_chwniso A)))))))
          (syn_cpw1 (syn_cpw1 (syn_cfv (syn_c2nd) (.cv u)))) (syn_cin (syn_chnord A)
            (syn_cima (syn_ccnv (syn_cdif (syn_clnqord (.cv r) (syn_chwcn A)) (syn_cid)))
              (syn_csn (syn_cec (.cv u) (syn_chwniso A)))))))
      (syn_wa (.classEq (.cv r) (syn_chncodecmpset A)) (.classMem (.cv u) (syn_chwcn A)))
      p0015
  have p0017 :=
    @g_mpbid
      (syn_wa (.classEq (.cv r) (syn_chncodecmpset A)) (.classMem (.cv u) (syn_chwcn A)))
      (syn_wiso (syn_ccom (syn_chnqmap1 A) (syn_csi
            (syn_chnwcutrel (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)))))
        (syn_csi (syn_csi (syn_cfv (syn_c1st) (.cv u)))) (syn_clnqord (.cv r) (syn_chwcn A))
        (syn_cpw1 (syn_cpw1 (syn_cfv (syn_c2nd) (.cv u)))) (syn_cin (syn_chnord A)
          (syn_cima (syn_ccnv (syn_cdif (syn_clnqord (.cv r) (syn_chwcn A)) (syn_cid)))
            (syn_csn (syn_cec (.cv u) (syn_chwniso A))))))
      (syn_wiso (syn_ccom (syn_chnqmap1 A) (syn_csi
            (syn_chnwcutrel (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)))))
        (syn_csi (syn_csi (syn_cfv (syn_c1st) (.cv u))))
        (syn_cin (syn_clnqord (.cv r) (syn_chwcn A)) (syn_cxp (syn_cin (syn_chnord A) (syn_cima
                (syn_ccnv (syn_cdif (syn_clnqord (.cv r) (syn_chwcn A)) (syn_cid)))
                (syn_csn (syn_cec (.cv u) (syn_chwniso A))))) (syn_cin (syn_chnord A) (syn_cima
                (syn_ccnv (syn_cdif (syn_clnqord (.cv r) (syn_chwcn A)) (syn_cid)))
                (syn_csn (syn_cec (.cv u) (syn_chwniso A)))))))
        (syn_cpw1 (syn_cpw1 (syn_cfv (syn_c2nd) (.cv u)))) (syn_cin (syn_chnord A)
          (syn_cima (syn_ccnv (syn_cdif (syn_clnqord (.cv r) (syn_chwcn A)) (syn_cid)))
            (syn_csn (syn_cec (.cv u) (syn_chwniso A))))))
      p0014 p0016
  exact p0017

@[expose]
noncomputable def g_hnwcutambstrictsegresisomraliasdndv (u : Var) (A : Class) (r : Var)
    (dv_A_r : r ∉ A.fv) (dv_A_u : u ∉ A.fv) (dv_r_u : r ≠ u)
    (hyp_hnwcutambstrictsegresisomraliasdndv_1 : Nominal.NPrf (.classMem A (syn_cvv))) :
    Nominal.NPrf
      (.imp (.classEq (.cv r) (syn_chncodecmpset A)) (.imp (.classMem (.cv u) (syn_chwcn A))
          (syn_wiso (syn_ccom (syn_chnqmap1 A) (syn_csi
                (syn_chnwcutrel (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)))))
            (syn_csi (syn_csi (syn_cfv (syn_c1st) (.cv u))))
            (syn_cin (syn_clnqord (.cv r) (syn_chwcn A)) (syn_cxp (syn_cin (syn_chnord A)
                  (syn_cima (syn_ccnv (syn_cdif (syn_clnqord (.cv r) (syn_chwcn A)) (syn_cid)))
                    (syn_csn (syn_cec (.cv u) (syn_chwniso A))))) (syn_cin (syn_chnord A)
                  (syn_cima (syn_ccnv (syn_cdif (syn_clnqord (.cv r) (syn_chwcn A)) (syn_cid)))
                    (syn_csn (syn_cec (.cv u) (syn_chwniso A)))))))
            (syn_cpw1 (syn_cpw1 (syn_cfv (syn_c2nd) (.cv u)))) (syn_cin (syn_chnord A) (syn_cima
                (syn_ccnv (syn_cdif (syn_clnqord (.cv r) (syn_chwcn A)) (syn_cid)))
                (syn_csn (syn_cec (.cv u) (syn_chwniso A)))))))) :=
  by
  have dv_cache_0001 : r ∉ (A).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : r ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_A_r, not_false_eq_true])
  have dv_cache_0002 : u ∉ (A).fv :=
    by
    clear dv_cache_0001
    exact
      (by
        have compact_fv_not_mem_empty : u ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_A_u, not_false_eq_true])
  have dv_cache_0003 : r ≠ u :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact (show r ≠ u from (by exact dv_r_u))
  have p0000 :=
    @g_hnwcutambstrictsegresisomralias0ndv u A r dv_cache_0001 dv_cache_0002 dv_cache_0003
      hyp_hnwcutambstrictsegresisomraliasdndv_1
  have p0001 :=
    @g_ex (.classEq (.cv r) (syn_chncodecmpset A)) (.classMem (.cv u) (syn_chwcn A))
      (syn_wiso (syn_ccom (syn_chnqmap1 A) (syn_csi
            (syn_chnwcutrel (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)))))
        (syn_csi (syn_csi (syn_cfv (syn_c1st) (.cv u))))
        (syn_cin (syn_clnqord (.cv r) (syn_chwcn A)) (syn_cxp (syn_cin (syn_chnord A) (syn_cima
                (syn_ccnv (syn_cdif (syn_clnqord (.cv r) (syn_chwcn A)) (syn_cid)))
                (syn_csn (syn_cec (.cv u) (syn_chwniso A))))) (syn_cin (syn_chnord A) (syn_cima
                (syn_ccnv (syn_cdif (syn_clnqord (.cv r) (syn_chwcn A)) (syn_cid)))
                (syn_csn (syn_cec (.cv u) (syn_chwniso A)))))))
        (syn_cpw1 (syn_cpw1 (syn_cfv (syn_c2nd) (.cv u)))) (syn_cin (syn_chnord A)
          (syn_cima (syn_ccnv (syn_cdif (syn_clnqord (.cv r) (syn_chwcn A)) (syn_cid)))
            (syn_csn (syn_cec (.cv u) (syn_chwniso A))))))
      p0000
  exact p0001


end NFChoice.DirectNominalPrf.WPPReplay

end
