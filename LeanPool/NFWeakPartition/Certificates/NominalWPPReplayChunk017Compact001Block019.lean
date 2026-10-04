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

/-- Checked nominal proof certificate identified upstream as `g_hnwcutambfactorranbrimpndv`. -/
@[expose]
noncomputable def gHnwcutambfactorranbrimpndv (x : Var) (z : Var) (u : Var) (A : Class)
    (dv_A_u : u ∉ A.fv) (dv_A_x : x ∉ A.fv) (dv_u_x : u ≠ x) (dv_x_z : x ≠ z)
    (hyp_hnwcutambfactorranbrimpndv_1 : Nominal.NPrf (.classMem A (synCvv))) :
    Nominal.NPrf
      (.imp (.classMem (.cv u) (synChwcn A)) (synWb (.classMem (.cv z) (synCrn
              (synCcom (synChnqmap1 A) (synCsi (synChnwcutrel (synCfv (synC1st) (.cv u))
                    (synCfv (synC2nd) (.cv u))))))) (synWrex x (synCfv (synC2nd) (.cv u))
            (.classEq (synCec
                (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u))
                  (.cv x)) (synChwniso A)) (.cv z))))) :=
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
  have dv_cache_0002 : p ∉ ((synCpw1 (synCpw1 (synCfv (synC2nd) (.cv u))))).fv :=
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
      ((synCcom (synChnqmap1 A) (synCsi (synChnwcutrel (synCfv (synC1st) (.cv u))
              (synCfv (synC2nd) (.cv u)))))).fv :=
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
  have dv_cache_0007 : Disjoint ((Class.cv x)).fv ((synCfv (synC1st) (.cv u))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006
    exact
      (show Disjoint ((Class.cv x)).fv ((synCfv (synC1st) (.cv u))).fv from (by
          rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv,
            NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv];
          exact
            (show
              Disjoint (({ x } : Finset Var)) ((((Class.cv u)).fv) ∪ (((synC1st)).fv))
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
                  (show Disjoint (({ x } : Finset Var)) (((synC1st)).fv) from
                    (by
                      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1st];
                      exact
                        (show Disjoint (({ x } : Finset Var)) ((∅ : Finset Var)) from
                          (by simp))))⟩))))
  have dv_cache_0008 : x ∉ ((synCuni (synCuni (.cv p)))).fv :=
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
  have dv_cache_0009 : x ∉ ((synCfv (synC2nd) (.cv u))).fv :=
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
      ((Wff.classEq (synCec
            (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u))
              (synCuni (synCuni (.cv p)))) (synChwniso A)) (.cv z))).fv :=
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
      ((synWa (.classMem (.cv u) (synChwcn A))
          (synWa (.classMem (.cv p) (synCpw1 (synCpw1 (synCfv (synC2nd) (.cv u)))))
            (.classEq (synCfv (synCcom (synChnqmap1 A) (synCsi
                    (synChnwcutrel (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u)))))
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
      ((synWrex x (synCfv (synC2nd) (.cv u)) (.classEq (synCec
              (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u))
                (.cv x)) (synChwniso A)) (.cv z)))).fv :=
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
  have dv_cache_0013 : p ∉ ((Wff.classMem (.cv u) (synChwcn A))).fv :=
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
  have dv_cache_0014 : q ∉ ((synCsn (synCsn (.cv x)))).fv :=
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
    Disjoint ((synCuni (synCuni (.cv q)))).fv ((synCfv (synC1st) (.cv u))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016
    exact
      (show Disjoint ((synCuni (synCuni (.cv q)))).fv ((synCfv (synC1st) (.cv u))).fv from
        (by
          rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cuni,
            NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv];
          exact
            (show
              Disjoint (((synCuni (.cv q))).fv) ((((Class.cv u)).fv) ∪ (((synC1st)).fv))
              from
              (Finset.disjoint_union_right.mpr
                ⟨(show Disjoint (((synCuni (.cv q))).fv) (((Class.cv u)).fv) from
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
                  (show Disjoint (((synCuni (.cv q))).fv) (((synC1st)).fv) from
                    (by
                      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cuni];
                      exact
                        (show Disjoint (((Class.cv q)).fv) (((synC1st)).fv) from
                          (by
                            rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv];
                            exact
                              (show Disjoint (({ q } : Finset Var)) (((synC1st)).fv) from
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
      ((Wff.classEq (synCfv (synCcom (synChnqmap1 A) (synCsi
                (synChnwcutrel (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u)))))
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
      ((synWrex p (synCpw1 (synCpw1 (synCfv (synC2nd) (.cv u)))) (.classEq (synCfv
              (synCcom (synChnqmap1 A) (synCsi (synChnwcutrel (synCfv (synC1st) (.cv u))
                    (synCfv (synC2nd) (.cv u))))) (.cv p)) (.cv z)))).fv :=
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
      ((synWa (synWa (.classMem (.cv u) (synChwcn A))
            (.classMem (.cv x) (synCfv (synC2nd) (.cv u)))) (.classEq (synCec
              (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u))
                (.cv x)) (synChwniso A)) (.cv z)))).fv :=
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
      ((synWrex p (synCpw1 (synCpw1 (synCfv (synC2nd) (.cv u)))) (.classEq (synCfv
              (synCcom (synChnqmap1 A) (synCsi (synChnwcutrel (synCfv (synC1st) (.cv u))
                    (synCfv (synC2nd) (.cv u))))) (.cv p)) (.cv z)))).fv :=
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
  have dv_cache_0023 : x ∉ ((Wff.classMem (.cv u) (synChwcn A))).fv :=
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
    @gHnwcutambfactorf1impndv u A dv_cache_0001 hyp_hnwcutambfactorranbrimpndv_1
  have p0001 :=
    @gF1fn (synCpw1 (synCpw1 (synCfv (synC2nd) (.cv u)))) (synChnord A)
      (synCcom (synChnqmap1 A) (synCsi
          (synChnwcutrel (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u)))))
  have p0002 :=
    @gSyl (.classMem (.cv u) (synChwcn A))
      (synWf1 (synCcom (synChnqmap1 A) (synCsi
            (synChnwcutrel (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u)))))
        (synCpw1 (synCpw1 (synCfv (synC2nd) (.cv u)))) (synChnord A))
      (synWfn (synCcom (synChnqmap1 A) (synCsi
            (synChnwcutrel (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u)))))
        (synCpw1 (synCpw1 (synCfv (synC2nd) (.cv u)))))
      p0000 p0001
  have p0003 :=
    @gFvelrnb p (synCpw1 (synCpw1 (synCfv (synC2nd) (.cv u)))) (.cv z)
      (synCcom (synChnqmap1 A) (synCsi
          (synChnwcutrel (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u)))))
      dv_cache_0002 dv_cache_0003 dv_cache_0004
  have p0004 :=
    @gSyl (.classMem (.cv u) (synChwcn A))
      (synWfn (synCcom (synChnqmap1 A) (synCsi
            (synChnwcutrel (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u)))))
        (synCpw1 (synCpw1 (synCfv (synC2nd) (.cv u)))))
      (synWb (.classMem (.cv z) (synCrn (synCcom (synChnqmap1 A) (synCsi
                (synChnwcutrel (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u)))))))
        (synWrex p (synCpw1 (synCpw1 (synCfv (synC2nd) (.cv u)))) (.classEq (synCfv
              (synCcom (synChnqmap1 A) (synCsi (synChnwcutrel (synCfv (synC1st) (.cv u))
                    (synCfv (synC2nd) (.cv u))))) (.cv p)) (.cv z))))
      p0002 p0003
  have p0005 :=
    @gSimpr (.classMem (.cv u) (synChwcn A))
      (synWa (.classMem (.cv p) (synCpw1 (synCpw1 (synCfv (synC2nd) (.cv u))))) (.classEq
          (synCfv (synCcom (synChnqmap1 A) (synCsi
                (synChnwcutrel (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u)))))
            (.cv p)) (.cv z)))
  have p0006 :=
    @gSimpl (.classMem (.cv p) (synCpw1 (synCpw1 (synCfv (synC2nd) (.cv u)))))
      (.classEq (synCfv (synCcom (synChnqmap1 A) (synCsi
              (synChnwcutrel (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u)))))
          (.cv p)) (.cv z))
  have p0007 :=
    @gSyl
      (synWa (.classMem (.cv u) (synChwcn A))
        (synWa (.classMem (.cv p) (synCpw1 (synCpw1 (synCfv (synC2nd) (.cv u))))) (.classEq
            (synCfv (synCcom (synChnqmap1 A) (synCsi
                  (synChnwcutrel (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u)))))
              (.cv p)) (.cv z))))
      (synWa (.classMem (.cv p) (synCpw1 (synCpw1 (synCfv (synC2nd) (.cv u))))) (.classEq
          (synCfv (synCcom (synChnqmap1 A) (synCsi
                (synChnwcutrel (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u)))))
            (.cv p)) (.cv z)))
      (.classMem (.cv p) (synCpw1 (synCpw1 (synCfv (synC2nd) (.cv u))))) p0005 p0006
  have p0008 :=
    @gSimpl (.classMem (.cv u) (synChwcn A))
      (synWa (.classMem (.cv p) (synCpw1 (synCpw1 (synCfv (synC2nd) (.cv u))))) (.classEq
          (synCfv (synCcom (synChnqmap1 A) (synCsi
                (synChnwcutrel (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u)))))
            (.cv p)) (.cv z)))
  have p0009 :=
    @gHnwcutambfactorvalimpndv u A p dv_cache_0005 dv_cache_0001 dv_cache_0006
      hyp_hnwcutambfactorranbrimpndv_1
  have p0010 :=
    @gSyl
      (synWa (.classMem (.cv u) (synChwcn A))
        (synWa (.classMem (.cv p) (synCpw1 (synCpw1 (synCfv (synC2nd) (.cv u))))) (.classEq
            (synCfv (synCcom (synChnqmap1 A) (synCsi
                  (synChnwcutrel (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u)))))
              (.cv p)) (.cv z))))
      (.classMem (.cv u) (synChwcn A))
      (.imp (.classMem (.cv p) (synCpw1 (synCpw1 (synCfv (synC2nd) (.cv u))))) (.classEq
          (synCfv (synCcom (synChnqmap1 A) (synCsi
                (synChnwcutrel (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u)))))
            (.cv p)) (synCec
            (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u))
              (synCuni (synCuni (.cv p)))) (synChwniso A))))
      p0008 p0009
  have p0011 :=
    @gMpd
      (synWa (.classMem (.cv u) (synChwcn A))
        (synWa (.classMem (.cv p) (synCpw1 (synCpw1 (synCfv (synC2nd) (.cv u))))) (.classEq
            (synCfv (synCcom (synChnqmap1 A) (synCsi
                  (synChnwcutrel (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u)))))
              (.cv p)) (.cv z))))
      (.classMem (.cv p) (synCpw1 (synCpw1 (synCfv (synC2nd) (.cv u)))))
      (.classEq (synCfv (synCcom (synChnqmap1 A) (synCsi
              (synChnwcutrel (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u)))))
          (.cv p)) (synCec
          (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u))
            (synCuni (synCuni (.cv p)))) (synChwniso A)))
      p0007 p0010
  have p0013 :=
    @gSimpr (.classMem (.cv p) (synCpw1 (synCpw1 (synCfv (synC2nd) (.cv u)))))
      (.classEq (synCfv (synCcom (synChnqmap1 A) (synCsi
              (synChnwcutrel (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u)))))
          (.cv p)) (.cv z))
  have p0014 :=
    @gSyl
      (synWa (.classMem (.cv u) (synChwcn A))
        (synWa (.classMem (.cv p) (synCpw1 (synCpw1 (synCfv (synC2nd) (.cv u))))) (.classEq
            (synCfv (synCcom (synChnqmap1 A) (synCsi
                  (synChnwcutrel (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u)))))
              (.cv p)) (.cv z))))
      (synWa (.classMem (.cv p) (synCpw1 (synCpw1 (synCfv (synC2nd) (.cv u))))) (.classEq
          (synCfv (synCcom (synChnqmap1 A) (synCsi
                (synChnwcutrel (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u)))))
            (.cv p)) (.cv z)))
      (.classEq (synCfv (synCcom (synChnqmap1 A) (synCsi
              (synChnwcutrel (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u)))))
          (.cv p)) (.cv z))
      p0005 p0013
  have p0015 :=
    @gEqtr3d
      (synWa (.classMem (.cv u) (synChwcn A))
        (synWa (.classMem (.cv p) (synCpw1 (synCpw1 (synCfv (synC2nd) (.cv u))))) (.classEq
            (synCfv (synCcom (synChnqmap1 A) (synCsi
                  (synChnwcutrel (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u)))))
              (.cv p)) (.cv z))))
      (synCfv (synCcom (synChnqmap1 A) (synCsi
            (synChnwcutrel (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u)))))
        (.cv p))
      (synCec (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u))
          (synCuni (synCuni (.cv p)))) (synChwniso A))
      (.cv z) p0011 p0014
  have p0019 := @gPw12argcl (.cv p) (synCfv (synC2nd) (.cv u))
  have p0020 :=
    @gSyl
      (synWa (.classMem (.cv u) (synChwcn A))
        (synWa (.classMem (.cv p) (synCpw1 (synCpw1 (synCfv (synC2nd) (.cv u))))) (.classEq
            (synCfv (synCcom (synChnqmap1 A) (synCsi
                  (synChnwcutrel (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u)))))
              (.cv p)) (.cv z))))
      (.classMem (.cv p) (synCpw1 (synCpw1 (synCfv (synC2nd) (.cv u)))))
      (synWa (.classMem (synCuni (synCuni (.cv p))) (synCfv (synC2nd) (.cv u)))
        (.classEq (.cv p) (synCsn (synCsn (synCuni (synCuni (.cv p)))))))
      p0007 p0019
  have p0021 :=
    @gSimpld
      (synWa (.classMem (.cv u) (synChwcn A))
        (synWa (.classMem (.cv p) (synCpw1 (synCpw1 (synCfv (synC2nd) (.cv u))))) (.classEq
            (synCfv (synCcom (synChnqmap1 A) (synCsi
                  (synChnwcutrel (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u)))))
              (.cv p)) (.cv z))))
      (.classMem (synCuni (synCuni (.cv p))) (synCfv (synC2nd) (.cv u)))
      (.classEq (.cv p) (synCsn (synCsn (synCuni (synCuni (.cv p)))))) p0020
  have p0022 :=
    @gSimpr
      (synWa (.classMem (.cv u) (synChwcn A))
        (synWa (.classMem (.cv p) (synCpw1 (synCpw1 (synCfv (synC2nd) (.cv u))))) (.classEq
            (synCfv (synCcom (synChnqmap1 A) (synCsi
                  (synChnwcutrel (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u)))))
              (.cv p)) (.cv z))))
      (.classEq (.cv x) (synCuni (synCuni (.cv p))))
  have p0023 :=
    @gHnwcutcodeeq3 (.cv x) (synCuni (synCuni (.cv p))) (synCfv (synC2nd) (.cv u))
      (synCfv (synC1st) (.cv u)) dv_cache_0007
  have p0024 :=
    @gSyl
      (synWa (synWa (.classMem (.cv u) (synChwcn A))
          (synWa (.classMem (.cv p) (synCpw1 (synCpw1 (synCfv (synC2nd) (.cv u)))))
            (.classEq (synCfv (synCcom (synChnqmap1 A) (synCsi
                    (synChnwcutrel (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u)))))
                (.cv p)) (.cv z)))) (.classEq (.cv x) (synCuni (synCuni (.cv p)))))
      (.classEq (.cv x) (synCuni (synCuni (.cv p))))
      (.classEq (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u))
          (.cv x)) (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u))
          (synCuni (synCuni (.cv p)))))
      p0022 p0023
  have p0025 :=
    @gEceq1
      (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u)) (.cv x))
      (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u))
        (synCuni (synCuni (.cv p))))
      (synChwniso A)
  have p0026 :=
    @gSyl
      (synWa (synWa (.classMem (.cv u) (synChwcn A))
          (synWa (.classMem (.cv p) (synCpw1 (synCpw1 (synCfv (synC2nd) (.cv u)))))
            (.classEq (synCfv (synCcom (synChnqmap1 A) (synCsi
                    (synChnwcutrel (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u)))))
                (.cv p)) (.cv z)))) (.classEq (.cv x) (synCuni (synCuni (.cv p)))))
      (.classEq (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u))
          (.cv x)) (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u))
          (synCuni (synCuni (.cv p)))))
      (.classEq (synCec
          (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u)) (.cv x))
          (synChwniso A)) (synCec
          (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u))
            (synCuni (synCuni (.cv p)))) (synChwniso A)))
      p0024 p0025
  have p0027 :=
    @gEqeq1d
      (synWa (synWa (.classMem (.cv u) (synChwcn A))
          (synWa (.classMem (.cv p) (synCpw1 (synCpw1 (synCfv (synC2nd) (.cv u)))))
            (.classEq (synCfv (synCcom (synChnqmap1 A) (synCsi
                    (synChnwcutrel (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u)))))
                (.cv p)) (.cv z)))) (.classEq (.cv x) (synCuni (synCuni (.cv p)))))
      (synCec (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u))
          (.cv x)) (synChwniso A))
      (synCec (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u))
          (synCuni (synCuni (.cv p)))) (synChwniso A))
      (.cv z) p0026
  have p0028 :=
    @gRspcedv
      (synWa (.classMem (.cv u) (synChwcn A))
        (synWa (.classMem (.cv p) (synCpw1 (synCpw1 (synCfv (synC2nd) (.cv u))))) (.classEq
            (synCfv (synCcom (synChnqmap1 A) (synCsi
                  (synChnwcutrel (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u)))))
              (.cv p)) (.cv z))))
      (.classEq (synCec
          (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u)) (.cv x))
          (synChwniso A)) (.cv z))
      (.classEq (synCec
          (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u))
            (synCuni (synCuni (.cv p)))) (synChwniso A)) (.cv z))
      x (synCuni (synCuni (.cv p))) (synCfv (synC2nd) (.cv u)) dv_cache_0008
      dv_cache_0009 dv_cache_0010 dv_cache_0011 p0021 p0027
  have p0029 :=
    @gMpd
      (synWa (.classMem (.cv u) (synChwcn A))
        (synWa (.classMem (.cv p) (synCpw1 (synCpw1 (synCfv (synC2nd) (.cv u))))) (.classEq
            (synCfv (synCcom (synChnqmap1 A) (synCsi
                  (synChnwcutrel (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u)))))
              (.cv p)) (.cv z))))
      (.classEq (synCec
          (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u))
            (synCuni (synCuni (.cv p)))) (synChwniso A)) (.cv z))
      (synWrex x (synCfv (synC2nd) (.cv u)) (.classEq (synCec
            (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u)) (.cv x))
            (synChwniso A)) (.cv z)))
      p0015 p0028
  have p0030 :=
    @gN3impb (.classMem (.cv u) (synChwcn A))
      (.classMem (.cv p) (synCpw1 (synCpw1 (synCfv (synC2nd) (.cv u)))))
      (.classEq (synCfv (synCcom (synChnqmap1 A) (synCsi
              (synChnwcutrel (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u)))))
          (.cv p)) (.cv z))
      (synWrex x (synCfv (synC2nd) (.cv u)) (.classEq (synCec
            (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u)) (.cv x))
            (synChwniso A)) (.cv z)))
      p0029
  have p0031 :=
    @gN3exp (.classMem (.cv u) (synChwcn A))
      (.classMem (.cv p) (synCpw1 (synCpw1 (synCfv (synC2nd) (.cv u)))))
      (.classEq (synCfv (synCcom (synChnqmap1 A) (synCsi
              (synChnwcutrel (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u)))))
          (.cv p)) (.cv z))
      (synWrex x (synCfv (synC2nd) (.cv u)) (.classEq (synCec
            (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u)) (.cv x))
            (synChwniso A)) (.cv z)))
      p0030
  have p0032 :=
    @gRexlimdv (.classMem (.cv u) (synChwcn A))
      (.classEq (synCfv (synCcom (synChnqmap1 A) (synCsi
              (synChnwcutrel (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u)))))
          (.cv p)) (.cv z))
      (synWrex x (synCfv (synC2nd) (.cv u)) (.classEq (synCec
            (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u)) (.cv x))
            (synChwniso A)) (.cv z)))
      p (synCpw1 (synCpw1 (synCfv (synC2nd) (.cv u)))) dv_cache_0012 dv_cache_0013
      p0031
  have p0033 :=
    @gImp (.classMem (.cv u) (synChwcn A))
      (synWrex p (synCpw1 (synCpw1 (synCfv (synC2nd) (.cv u)))) (.classEq (synCfv
            (synCcom (synChnqmap1 A) (synCsi (synChnwcutrel (synCfv (synC1st) (.cv u))
                  (synCfv (synC2nd) (.cv u))))) (.cv p)) (.cv z)))
      (synWrex x (synCfv (synC2nd) (.cv u)) (.classEq (synCec
            (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u)) (.cv x))
            (synChwniso A)) (.cv z)))
      p0032
  have p0034 := @gSnex (synCsn (.cv x))
  have p0035 := @gIsseti q (synCsn (synCsn (.cv x))) dv_cache_0014 p0034
  have p0036 :=
    @gA1i (synWex q (.classEq (.cv q) (synCsn (synCsn (.cv x)))))
      (synWa (synWa (.classMem (.cv u) (synChwcn A))
          (.classMem (.cv x) (synCfv (synC2nd) (.cv u)))) (.classEq (synCec
            (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u)) (.cv x))
            (synChwniso A)) (.cv z)))
      p0035
  have p0037 :=
    @gSimpl
      (synWa (synWa (.classMem (.cv u) (synChwcn A))
          (.classMem (.cv x) (synCfv (synC2nd) (.cv u)))) (.classEq (synCec
            (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u)) (.cv x))
            (synChwniso A)) (.cv z)))
      (.classEq (.cv q) (synCsn (synCsn (.cv x))))
  have p0038 :=
    @gSimpl
      (synWa (.classMem (.cv u) (synChwcn A))
        (.classMem (.cv x) (synCfv (synC2nd) (.cv u))))
      (.classEq (synCec
          (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u)) (.cv x))
          (synChwniso A)) (.cv z))
  have p0039 :=
    @gSyl
      (synWa (synWa (synWa (.classMem (.cv u) (synChwcn A))
            (.classMem (.cv x) (synCfv (synC2nd) (.cv u)))) (.classEq (synCec
              (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u))
                (.cv x)) (synChwniso A)) (.cv z)))
        (.classEq (.cv q) (synCsn (synCsn (.cv x)))))
      (synWa (synWa (.classMem (.cv u) (synChwcn A))
          (.classMem (.cv x) (synCfv (synC2nd) (.cv u)))) (.classEq (synCec
            (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u)) (.cv x))
            (synChwniso A)) (.cv z)))
      (synWa (.classMem (.cv u) (synChwcn A))
        (.classMem (.cv x) (synCfv (synC2nd) (.cv u))))
      p0037 p0038
  have p0040 :=
    @gSimpr (.classMem (.cv u) (synChwcn A))
      (.classMem (.cv x) (synCfv (synC2nd) (.cv u)))
  have p0041 := @gSnelpw1 (.cv x) (synCfv (synC2nd) (.cv u))
  have p0042 :=
    @gA1i
      (synWb (.classMem (synCsn (.cv x)) (synCpw1 (synCfv (synC2nd) (.cv u))))
        (.classMem (.cv x) (synCfv (synC2nd) (.cv u))))
      (synWa (.classMem (.cv u) (synChwcn A))
        (.classMem (.cv x) (synCfv (synC2nd) (.cv u))))
      p0041
  have p0043 :=
    @gMpbird
      (synWa (.classMem (.cv u) (synChwcn A))
        (.classMem (.cv x) (synCfv (synC2nd) (.cv u))))
      (.classMem (synCsn (.cv x)) (synCpw1 (synCfv (synC2nd) (.cv u))))
      (.classMem (.cv x) (synCfv (synC2nd) (.cv u))) p0040 p0042
  have p0044 := @gSnelpw1 (synCsn (.cv x)) (synCpw1 (synCfv (synC2nd) (.cv u)))
  have p0045 :=
    @gA1i
      (synWb (.classMem (synCsn (synCsn (.cv x)))
          (synCpw1 (synCpw1 (synCfv (synC2nd) (.cv u)))))
        (.classMem (synCsn (.cv x)) (synCpw1 (synCfv (synC2nd) (.cv u)))))
      (synWa (.classMem (.cv u) (synChwcn A))
        (.classMem (.cv x) (synCfv (synC2nd) (.cv u))))
      p0044
  have p0046 :=
    @gMpbird
      (synWa (.classMem (.cv u) (synChwcn A))
        (.classMem (.cv x) (synCfv (synC2nd) (.cv u))))
      (.classMem (synCsn (synCsn (.cv x))) (synCpw1 (synCpw1 (synCfv (synC2nd) (.cv u)))))
      (.classMem (synCsn (.cv x)) (synCpw1 (synCfv (synC2nd) (.cv u)))) p0043 p0045
  have p0047 :=
    @gSyl
      (synWa (synWa (synWa (.classMem (.cv u) (synChwcn A))
            (.classMem (.cv x) (synCfv (synC2nd) (.cv u)))) (.classEq (synCec
              (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u))
                (.cv x)) (synChwniso A)) (.cv z)))
        (.classEq (.cv q) (synCsn (synCsn (.cv x)))))
      (synWa (.classMem (.cv u) (synChwcn A))
        (.classMem (.cv x) (synCfv (synC2nd) (.cv u))))
      (.classMem (synCsn (synCsn (.cv x))) (synCpw1 (synCpw1 (synCfv (synC2nd) (.cv u)))))
      p0039 p0046
  have p0048 :=
    @gSimpr
      (synWa (synWa (.classMem (.cv u) (synChwcn A))
          (.classMem (.cv x) (synCfv (synC2nd) (.cv u)))) (.classEq (synCec
            (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u)) (.cv x))
            (synChwniso A)) (.cv z)))
      (.classEq (.cv q) (synCsn (synCsn (.cv x))))
  have p0049 :=
    @gEleq1d
      (synWa (synWa (synWa (.classMem (.cv u) (synChwcn A))
            (.classMem (.cv x) (synCfv (synC2nd) (.cv u)))) (.classEq (synCec
              (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u))
                (.cv x)) (synChwniso A)) (.cv z)))
        (.classEq (.cv q) (synCsn (synCsn (.cv x)))))
      (.cv q) (synCsn (synCsn (.cv x)))
      (synCpw1 (synCpw1 (synCfv (synC2nd) (.cv u)))) p0048
  have p0050 :=
    @gMpbird
      (synWa (synWa (synWa (.classMem (.cv u) (synChwcn A))
            (.classMem (.cv x) (synCfv (synC2nd) (.cv u)))) (.classEq (synCec
              (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u))
                (.cv x)) (synChwniso A)) (.cv z)))
        (.classEq (.cv q) (synCsn (synCsn (.cv x)))))
      (.classMem (.cv q) (synCpw1 (synCpw1 (synCfv (synC2nd) (.cv u)))))
      (.classMem (synCsn (synCsn (.cv x))) (synCpw1 (synCpw1 (synCfv (synC2nd) (.cv u)))))
      p0047 p0049
  have p0068 :=
    @gSimpl (.classMem (.cv u) (synChwcn A))
      (.classMem (.cv x) (synCfv (synC2nd) (.cv u)))
  have p0069 :=
    @gSyl
      (synWa (synWa (synWa (.classMem (.cv u) (synChwcn A))
            (.classMem (.cv x) (synCfv (synC2nd) (.cv u)))) (.classEq (synCec
              (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u))
                (.cv x)) (synChwniso A)) (.cv z)))
        (.classEq (.cv q) (synCsn (synCsn (.cv x)))))
      (synWa (.classMem (.cv u) (synChwcn A))
        (.classMem (.cv x) (synCfv (synC2nd) (.cv u))))
      (.classMem (.cv u) (synChwcn A)) p0039 p0068
  have p0070 :=
    @gHnwcutambfactorvalimpndv u A q dv_cache_0015 dv_cache_0001 dv_cache_0016
      hyp_hnwcutambfactorranbrimpndv_1
  have p0071 :=
    @gSyl
      (synWa (synWa (synWa (.classMem (.cv u) (synChwcn A))
            (.classMem (.cv x) (synCfv (synC2nd) (.cv u)))) (.classEq (synCec
              (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u))
                (.cv x)) (synChwniso A)) (.cv z)))
        (.classEq (.cv q) (synCsn (synCsn (.cv x)))))
      (.classMem (.cv u) (synChwcn A))
      (.imp (.classMem (.cv q) (synCpw1 (synCpw1 (synCfv (synC2nd) (.cv u))))) (.classEq
          (synCfv (synCcom (synChnqmap1 A) (synCsi
                (synChnwcutrel (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u)))))
            (.cv q)) (synCec
            (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u))
              (synCuni (synCuni (.cv q)))) (synChwniso A))))
      p0069 p0070
  have p0072 :=
    @gMpd
      (synWa (synWa (synWa (.classMem (.cv u) (synChwcn A))
            (.classMem (.cv x) (synCfv (synC2nd) (.cv u)))) (.classEq (synCec
              (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u))
                (.cv x)) (synChwniso A)) (.cv z)))
        (.classEq (.cv q) (synCsn (synCsn (.cv x)))))
      (.classMem (.cv q) (synCpw1 (synCpw1 (synCfv (synC2nd) (.cv u)))))
      (.classEq (synCfv (synCcom (synChnqmap1 A) (synCsi
              (synChnwcutrel (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u)))))
          (.cv q)) (synCec
          (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u))
            (synCuni (synCuni (.cv q)))) (synChwniso A)))
      p0050 p0071
  have p0074 :=
    @gUnieqd
      (synWa (synWa (synWa (.classMem (.cv u) (synChwcn A))
            (.classMem (.cv x) (synCfv (synC2nd) (.cv u)))) (.classEq (synCec
              (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u))
                (.cv x)) (synChwniso A)) (.cv z)))
        (.classEq (.cv q) (synCsn (synCsn (.cv x)))))
      (.cv q) (synCsn (synCsn (.cv x))) p0048
  have p0075 :=
    @gUnieqd
      (synWa (synWa (synWa (.classMem (.cv u) (synChwcn A))
            (.classMem (.cv x) (synCfv (synC2nd) (.cv u)))) (.classEq (synCec
              (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u))
                (.cv x)) (synChwniso A)) (.cv z)))
        (.classEq (.cv q) (synCsn (synCsn (.cv x)))))
      (synCuni (.cv q)) (synCuni (synCsn (synCsn (.cv x)))) p0074
  have p0076 := @gSnex (.cv x)
  have p0077 := @gUnisn (synCsn (.cv x)) p0076
  have p0078 := @gUnieqi (synCuni (synCsn (synCsn (.cv x)))) (synCsn (.cv x)) p0077
  have p0079 := @gVex x
  have p0080 := @gUnisn (.cv x) p0079
  have p0081 :=
    @gEqtri (synCuni (synCuni (synCsn (synCsn (.cv x)))))
      (synCuni (synCsn (.cv x))) (.cv x) p0078 p0080
  have p0082 :=
    @gA1i (.classEq (synCuni (synCuni (synCsn (synCsn (.cv x))))) (.cv x))
      (synWa (synWa (synWa (.classMem (.cv u) (synChwcn A))
            (.classMem (.cv x) (synCfv (synC2nd) (.cv u)))) (.classEq (synCec
              (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u))
                (.cv x)) (synChwniso A)) (.cv z)))
        (.classEq (.cv q) (synCsn (synCsn (.cv x)))))
      p0081
  have p0083 :=
    @gEqtrd
      (synWa (synWa (synWa (.classMem (.cv u) (synChwcn A))
            (.classMem (.cv x) (synCfv (synC2nd) (.cv u)))) (.classEq (synCec
              (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u))
                (.cv x)) (synChwniso A)) (.cv z)))
        (.classEq (.cv q) (synCsn (synCsn (.cv x)))))
      (synCuni (synCuni (.cv q))) (synCuni (synCuni (synCsn (synCsn (.cv x)))))
      (.cv x) p0075 p0082
  have p0084 :=
    @gHnwcutcodeeq3 (synCuni (synCuni (.cv q))) (.cv x) (synCfv (synC2nd) (.cv u))
      (synCfv (synC1st) (.cv u)) dv_cache_0017
  have p0085 :=
    @gSyl
      (synWa (synWa (synWa (.classMem (.cv u) (synChwcn A))
            (.classMem (.cv x) (synCfv (synC2nd) (.cv u)))) (.classEq (synCec
              (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u))
                (.cv x)) (synChwniso A)) (.cv z)))
        (.classEq (.cv q) (synCsn (synCsn (.cv x)))))
      (.classEq (synCuni (synCuni (.cv q))) (.cv x))
      (.classEq (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u))
          (synCuni (synCuni (.cv q))))
        (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u)) (.cv x)))
      p0083 p0084
  have p0086 :=
    @gEceq1
      (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u))
        (synCuni (synCuni (.cv q))))
      (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u)) (.cv x))
      (synChwniso A)
  have p0087 :=
    @gSyl
      (synWa (synWa (synWa (.classMem (.cv u) (synChwcn A))
            (.classMem (.cv x) (synCfv (synC2nd) (.cv u)))) (.classEq (synCec
              (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u))
                (.cv x)) (synChwniso A)) (.cv z)))
        (.classEq (.cv q) (synCsn (synCsn (.cv x)))))
      (.classEq (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u))
          (synCuni (synCuni (.cv q))))
        (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u)) (.cv x)))
      (.classEq (synCec
          (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u))
            (synCuni (synCuni (.cv q)))) (synChwniso A)) (synCec
          (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u)) (.cv x))
          (synChwniso A)))
      p0085 p0086
  have p0088 :=
    @gEqtrd
      (synWa (synWa (synWa (.classMem (.cv u) (synChwcn A))
            (.classMem (.cv x) (synCfv (synC2nd) (.cv u)))) (.classEq (synCec
              (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u))
                (.cv x)) (synChwniso A)) (.cv z)))
        (.classEq (.cv q) (synCsn (synCsn (.cv x)))))
      (synCfv (synCcom (synChnqmap1 A) (synCsi
            (synChnwcutrel (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u)))))
        (.cv q))
      (synCec (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u))
          (synCuni (synCuni (.cv q)))) (synChwniso A))
      (synCec (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u))
          (.cv x)) (synChwniso A))
      p0072 p0087
  have p0090 :=
    @gSimpr
      (synWa (.classMem (.cv u) (synChwcn A))
        (.classMem (.cv x) (synCfv (synC2nd) (.cv u))))
      (.classEq (synCec
          (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u)) (.cv x))
          (synChwniso A)) (.cv z))
  have p0091 :=
    @gSyl
      (synWa (synWa (synWa (.classMem (.cv u) (synChwcn A))
            (.classMem (.cv x) (synCfv (synC2nd) (.cv u)))) (.classEq (synCec
              (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u))
                (.cv x)) (synChwniso A)) (.cv z)))
        (.classEq (.cv q) (synCsn (synCsn (.cv x)))))
      (synWa (synWa (.classMem (.cv u) (synChwcn A))
          (.classMem (.cv x) (synCfv (synC2nd) (.cv u)))) (.classEq (synCec
            (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u)) (.cv x))
            (synChwniso A)) (.cv z)))
      (.classEq (synCec
          (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u)) (.cv x))
          (synChwniso A)) (.cv z))
      p0037 p0090
  have p0092 :=
    @gEqtrd
      (synWa (synWa (synWa (.classMem (.cv u) (synChwcn A))
            (.classMem (.cv x) (synCfv (synC2nd) (.cv u)))) (.classEq (synCec
              (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u))
                (.cv x)) (synChwniso A)) (.cv z)))
        (.classEq (.cv q) (synCsn (synCsn (.cv x)))))
      (synCfv (synCcom (synChnqmap1 A) (synCsi
            (synChnwcutrel (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u)))))
        (.cv q))
      (synCec (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u))
          (.cv x)) (synChwniso A))
      (.cv z) p0088 p0091
  have p0093 :=
    @gJca
      (synWa (synWa (synWa (.classMem (.cv u) (synChwcn A))
            (.classMem (.cv x) (synCfv (synC2nd) (.cv u)))) (.classEq (synCec
              (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u))
                (.cv x)) (synChwniso A)) (.cv z)))
        (.classEq (.cv q) (synCsn (synCsn (.cv x)))))
      (.classMem (.cv q) (synCpw1 (synCpw1 (synCfv (synC2nd) (.cv u)))))
      (.classEq (synCfv (synCcom (synChnqmap1 A) (synCsi
              (synChnwcutrel (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u)))))
          (.cv q)) (.cv z))
      p0050 p0092
  have p0094 := @gId (.classEq (.cv p) (.cv q))
  have p0095 :=
    @gFveq2d (.classEq (.cv p) (.cv q)) (.cv p) (.cv q)
      (synCcom (synChnqmap1 A) (synCsi
          (synChnwcutrel (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u)))))
      p0094
  have p0096 :=
    @gEqeq1d (.classEq (.cv p) (.cv q))
      (synCfv (synCcom (synChnqmap1 A) (synCsi
            (synChnwcutrel (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u)))))
        (.cv p))
      (synCfv (synCcom (synChnqmap1 A) (synCsi
            (synChnwcutrel (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u)))))
        (.cv q))
      (.cv z) p0095
  have p0097 :=
    @gRspcev
      (.classEq (synCfv (synCcom (synChnqmap1 A) (synCsi
              (synChnwcutrel (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u)))))
          (.cv p)) (.cv z))
      (.classEq (synCfv (synCcom (synChnqmap1 A) (synCsi
              (synChnwcutrel (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u)))))
          (.cv q)) (.cv z))
      p (.cv q) (synCpw1 (synCpw1 (synCfv (synC2nd) (.cv u)))) dv_cache_0018
      dv_cache_0002 dv_cache_0019 p0096
  have p0098 :=
    @gSyl
      (synWa (synWa (synWa (.classMem (.cv u) (synChwcn A))
            (.classMem (.cv x) (synCfv (synC2nd) (.cv u)))) (.classEq (synCec
              (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u))
                (.cv x)) (synChwniso A)) (.cv z)))
        (.classEq (.cv q) (synCsn (synCsn (.cv x)))))
      (synWa (.classMem (.cv q) (synCpw1 (synCpw1 (synCfv (synC2nd) (.cv u))))) (.classEq
          (synCfv (synCcom (synChnqmap1 A) (synCsi
                (synChnwcutrel (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u)))))
            (.cv q)) (.cv z)))
      (synWrex p (synCpw1 (synCpw1 (synCfv (synC2nd) (.cv u)))) (.classEq (synCfv
            (synCcom (synChnqmap1 A) (synCsi (synChnwcutrel (synCfv (synC1st) (.cv u))
                  (synCfv (synC2nd) (.cv u))))) (.cv p)) (.cv z)))
      p0093 p0097
  have p0099 :=
    @gExlimddv
      (synWa (synWa (.classMem (.cv u) (synChwcn A))
          (.classMem (.cv x) (synCfv (synC2nd) (.cv u)))) (.classEq (synCec
            (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u)) (.cv x))
            (synChwniso A)) (.cv z)))
      (.classEq (.cv q) (synCsn (synCsn (.cv x))))
      (synWrex p (synCpw1 (synCpw1 (synCfv (synC2nd) (.cv u)))) (.classEq (synCfv
            (synCcom (synChnqmap1 A) (synCsi (synChnwcutrel (synCfv (synC1st) (.cv u))
                  (synCfv (synC2nd) (.cv u))))) (.cv p)) (.cv z)))
      q dv_cache_0020 dv_cache_0021 p0036 p0098
  have p0100 :=
    @gEx
      (synWa (.classMem (.cv u) (synChwcn A))
        (.classMem (.cv x) (synCfv (synC2nd) (.cv u))))
      (.classEq (synCec
          (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u)) (.cv x))
          (synChwniso A)) (.cv z))
      (synWrex p (synCpw1 (synCpw1 (synCfv (synC2nd) (.cv u)))) (.classEq (synCfv
            (synCcom (synChnqmap1 A) (synCsi (synChnwcutrel (synCfv (synC1st) (.cv u))
                  (synCfv (synC2nd) (.cv u))))) (.cv p)) (.cv z)))
      p0099
  have p0101 :=
    @gEx (.classMem (.cv u) (synChwcn A))
      (.classMem (.cv x) (synCfv (synC2nd) (.cv u)))
      (.imp (.classEq (synCec
            (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u)) (.cv x))
            (synChwniso A)) (.cv z))
        (synWrex p (synCpw1 (synCpw1 (synCfv (synC2nd) (.cv u)))) (.classEq (synCfv
              (synCcom (synChnqmap1 A) (synCsi (synChnwcutrel (synCfv (synC1st) (.cv u))
                    (synCfv (synC2nd) (.cv u))))) (.cv p)) (.cv z))))
      p0100
  have p0102 :=
    @gRexlimdv (.classMem (.cv u) (synChwcn A))
      (.classEq (synCec
          (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u)) (.cv x))
          (synChwniso A)) (.cv z))
      (synWrex p (synCpw1 (synCpw1 (synCfv (synC2nd) (.cv u)))) (.classEq (synCfv
            (synCcom (synChnqmap1 A) (synCsi (synChnwcutrel (synCfv (synC1st) (.cv u))
                  (synCfv (synC2nd) (.cv u))))) (.cv p)) (.cv z)))
      x (synCfv (synC2nd) (.cv u)) dv_cache_0022 dv_cache_0023 p0101
  have p0103 :=
    @gImp (.classMem (.cv u) (synChwcn A))
      (synWrex x (synCfv (synC2nd) (.cv u)) (.classEq (synCec
            (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u)) (.cv x))
            (synChwniso A)) (.cv z)))
      (synWrex p (synCpw1 (synCpw1 (synCfv (synC2nd) (.cv u)))) (.classEq (synCfv
            (synCcom (synChnqmap1 A) (synCsi (synChnwcutrel (synCfv (synC1st) (.cv u))
                  (synCfv (synC2nd) (.cv u))))) (.cv p)) (.cv z)))
      p0102
  have p0104 :=
    @gImpbida (.classMem (.cv u) (synChwcn A))
      (synWrex p (synCpw1 (synCpw1 (synCfv (synC2nd) (.cv u)))) (.classEq (synCfv
            (synCcom (synChnqmap1 A) (synCsi (synChnwcutrel (synCfv (synC1st) (.cv u))
                  (synCfv (synC2nd) (.cv u))))) (.cv p)) (.cv z)))
      (synWrex x (synCfv (synC2nd) (.cv u)) (.classEq (synCec
            (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u)) (.cv x))
            (synChwniso A)) (.cv z)))
      p0033 p0103
  have p0105 :=
    @gBitrd (.classMem (.cv u) (synChwcn A))
      (.classMem (.cv z) (synCrn (synCcom (synChnqmap1 A) (synCsi
              (synChnwcutrel (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u)))))))
      (synWrex p (synCpw1 (synCpw1 (synCfv (synC2nd) (.cv u)))) (.classEq (synCfv
            (synCcom (synChnqmap1 A) (synCsi (synChnwcutrel (synCfv (synC1st) (.cv u))
                  (synCfv (synC2nd) (.cv u))))) (.cv p)) (.cv z)))
      (synWrex x (synCfv (synC2nd) (.cv u)) (.classEq (synCec
            (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u)) (.cv x))
            (synChwniso A)) (.cv z)))
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

/-- Checked nominal proof certificate identified upstream as `g_hnwcutambstrictsegranimpndv`. -/
@[expose]
noncomputable def gHnwcutambstrictsegranimpndv (u : Var) (A : Class) (r : Var)
    (dv_A_r : r ∉ A.fv) (dv_A_u : u ∉ A.fv) (_dv_r_u : r ≠ u)
    (hyp_hnwcutstrictsegimp_1 : Nominal.NPrf (.classMem A (synCvv))) :
    Nominal.NPrf
      (.imp (synWa (.classEq (.cv r) (synChncodecmpset A)) (.classMem (.cv u) (synChwcn A)))
        (.classEq (synCrn (synCcom (synChnqmap1 A) (synCsi
                (synChnwcutrel (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u))))))
          (synCin (synChnord A)
            (synCima (synCcnv (synCdif (synClnqord (.cv r) (synChwcn A)) (synCid)))
              (synCsn (synCec (.cv u) (synChwniso A))))))) :=
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
      ((synWa (synWa (synWa (.classEq (.cv r) (synChncodecmpset A))
              (.classMem (.cv u) (synChwcn A))) (.classMem (.cv z) (synCin (synChnord A)
                (synCima (synCcnv (synCdif (synClnqord (.cv r) (synChwcn A)) (synCid)))
                  (synCsn (synCec (.cv u) (synChwniso A)))))))
          (synWa (.classMem (.cv v) (synChwcn A))
            (.classEq (.cv z) (synCec (.cv v) (synChwniso A)))))).fv :=
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
      ((synWrex x (synCfv (synC2nd) (.cv u)) (.classEq (synCec
              (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u))
                (.cv x)) (synChwniso A)) (.cv z)))).fv :=
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
      ((synWa (synWa (.classEq (.cv r) (synChncodecmpset A))
            (.classMem (.cv u) (synChwcn A))) (.classMem (.cv z) (synCin (synChnord A)
              (synCima (synCcnv (synCdif (synClnqord (.cv r) (synChwcn A)) (synCid)))
                (synCsn (synCec (.cv u) (synChwniso A)))))))).fv :=
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
      ((synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u))
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
  have dv_cache_0015 : Disjoint ((Class.cv y)).fv ((synCfv (synC1st) (.cv u))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014
    exact
      (show Disjoint ((Class.cv y)).fv ((synCfv (synC1st) (.cv u))).fv from (by
          rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv,
            NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv];
          exact
            (show
              Disjoint (({ y } : Finset Var)) ((((Class.cv u)).fv) ∪ (((synC1st)).fv))
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
                  (show Disjoint (({ y } : Finset Var)) (((synC1st)).fv) from
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
  have dv_cache_0017 : y ∉ ((synCfv (synC2nd) (.cv u))).fv :=
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
      ((synWbr (.cv w) (synChwniso A)
          (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u))
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
      ((synWa (synWa (synWa (.classEq (.cv r) (synChncodecmpset A))
              (.classMem (.cv u) (synChwcn A)))
            (.classMem (.cv x) (synCfv (synC2nd) (.cv u)))) (.classEq (.cv w)
            (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u))
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
      ((synWbr (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u))
            (.cv x)) (synCdif (synChncodecmpset A) (synCcnv (synChncodecmpset A)))
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
      ((synWa (synWa (.classEq (.cv r) (synChncodecmpset A))
            (.classMem (.cv u) (synChwcn A)))
          (.classMem (.cv x) (synCfv (synC2nd) (.cv u))))).fv :=
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
      ((Wff.classMem (.cv z) (synCin (synChnord A)
            (synCima (synCcnv (synCdif (synClnqord (.cv r) (synChwcn A)) (synCid)))
              (synCsn (synCec (.cv u) (synChwniso A))))))).fv :=
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
      ((synWa (.classEq (.cv r) (synChncodecmpset A))
          (.classMem (.cv u) (synChwcn A)))).fv :=
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
      ((synCrn (synCcom (synChnqmap1 A) (synCsi (synChnwcutrel (synCfv (synC1st) (.cv u))
                (synCfv (synC2nd) (.cv u))))))).fv :=
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
      ((synCin (synChnord A)
          (synCima (synCcnv (synCdif (synClnqord (.cv r) (synChwcn A)) (synCid)))
            (synCsn (synCec (.cv u) (synChwniso A)))))).fv :=
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
      ((synWa (.classEq (.cv r) (synChncodecmpset A))
          (.classMem (.cv u) (synChwcn A)))).fv :=
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
    @gSimpr (.classEq (.cv r) (synChncodecmpset A)) (.classMem (.cv u) (synChwcn A))
  have p0001 :=
    @gHnwcutambfactorranbrimpndv x z u A dv_cache_0001 dv_cache_0002 dv_cache_0003
      dv_cache_0004 hyp_hnwcutstrictsegimp_1
  have p0002 :=
    @gSyl
      (synWa (.classEq (.cv r) (synChncodecmpset A)) (.classMem (.cv u) (synChwcn A)))
      (.classMem (.cv u) (synChwcn A))
      (synWb (.classMem (.cv z) (synCrn (synCcom (synChnqmap1 A) (synCsi
                (synChnwcutrel (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u)))))))
        (synWrex x (synCfv (synC2nd) (.cv u)) (.classEq (synCec
              (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u))
                (.cv x)) (synChwniso A)) (.cv z))))
      p0000 p0001
  have p0003 :=
    @gSimpr
      (synWa (.classEq (.cv r) (synChncodecmpset A)) (.classMem (.cv u) (synChwcn A)))
      (.classMem (.cv z) (synCin (synChnord A)
          (synCima (synCcnv (synCdif (synClnqord (.cv r) (synChwcn A)) (synCid)))
            (synCsn (synCec (.cv u) (synChwniso A))))))
  have p0004 :=
    @gElin (.cv z) (synChnord A)
      (synCima (synCcnv (synCdif (synClnqord (.cv r) (synChwcn A)) (synCid)))
        (synCsn (synCec (.cv u) (synChwniso A))))
  have p0005 :=
    @gBiimpi
      (.classMem (.cv z) (synCin (synChnord A)
          (synCima (synCcnv (synCdif (synClnqord (.cv r) (synChwcn A)) (synCid)))
            (synCsn (synCec (.cv u) (synChwniso A))))))
      (synWa (.classMem (.cv z) (synChnord A)) (.classMem (.cv z)
          (synCima (synCcnv (synCdif (synClnqord (.cv r) (synChwcn A)) (synCid)))
            (synCsn (synCec (.cv u) (synChwniso A))))))
      p0004
  have p0006 :=
    @gSimpl (.classMem (.cv z) (synChnord A))
      (.classMem (.cv z)
        (synCima (synCcnv (synCdif (synClnqord (.cv r) (synChwcn A)) (synCid)))
          (synCsn (synCec (.cv u) (synChwniso A)))))
  have p0007 :=
    @gSyl
      (.classMem (.cv z) (synCin (synChnord A)
          (synCima (synCcnv (synCdif (synClnqord (.cv r) (synChwcn A)) (synCid)))
            (synCsn (synCec (.cv u) (synChwniso A))))))
      (synWa (.classMem (.cv z) (synChnord A)) (.classMem (.cv z)
          (synCima (synCcnv (synCdif (synClnqord (.cv r) (synChwcn A)) (synCid)))
            (synCsn (synCec (.cv u) (synChwniso A))))))
      (.classMem (.cv z) (synChnord A)) p0005 p0006
  have p0008 :=
    @gSyl
      (synWa (synWa (.classEq (.cv r) (synChncodecmpset A))
          (.classMem (.cv u) (synChwcn A))) (.classMem (.cv z) (synCin (synChnord A)
            (synCima (synCcnv (synCdif (synClnqord (.cv r) (synChwcn A)) (synCid)))
              (synCsn (synCec (.cv u) (synChwniso A)))))))
      (.classMem (.cv z) (synCin (synChnord A)
          (synCima (synCcnv (synCdif (synClnqord (.cv r) (synChwcn A)) (synCid)))
            (synCsn (synCec (.cv u) (synChwniso A))))))
      (.classMem (.cv z) (synChnord A)) p0003 p0007
  have p0009 := @gVex z
  have p0010 := @gElhnordclndv v A (.cv z) dv_cache_0005 dv_cache_0006
  have p0011 := Nominal.mp p0009 p0010
  have p0012 :=
    @gA1i
      (synWb (.classMem (.cv z) (synChnord A))
        (synWrex v (synChwcn A) (.classEq (.cv z) (synCec (.cv v) (synChwniso A)))))
      (synWa (synWa (.classEq (.cv r) (synChncodecmpset A))
          (.classMem (.cv u) (synChwcn A))) (.classMem (.cv z) (synCin (synChnord A)
            (synCima (synCcnv (synCdif (synClnqord (.cv r) (synChwcn A)) (synCid)))
              (synCsn (synCec (.cv u) (synChwniso A)))))))
      p0011
  have p0013 :=
    @gMpbid
      (synWa (synWa (.classEq (.cv r) (synChncodecmpset A))
          (.classMem (.cv u) (synChwcn A))) (.classMem (.cv z) (synCin (synChnord A)
            (synCima (synCcnv (synCdif (synClnqord (.cv r) (synChwcn A)) (synCid)))
              (synCsn (synCec (.cv u) (synChwniso A)))))))
      (.classMem (.cv z) (synChnord A))
      (synWrex v (synChwcn A) (.classEq (.cv z) (synCec (.cv v) (synChwniso A))))
      p0008 p0012
  have p0014 :=
    @gSimpl
      (synWa (synWa (.classEq (.cv r) (synChncodecmpset A))
          (.classMem (.cv u) (synChwcn A))) (.classMem (.cv z) (synCin (synChnord A)
            (synCima (synCcnv (synCdif (synClnqord (.cv r) (synChwcn A)) (synCid)))
              (synCsn (synCec (.cv u) (synChwniso A)))))))
      (synWa (.classMem (.cv v) (synChwcn A))
        (.classEq (.cv z) (synCec (.cv v) (synChwniso A))))
  have p0018 :=
    @gSimpr (.classMem (.cv z) (synChnord A))
      (.classMem (.cv z)
        (synCima (synCcnv (synCdif (synClnqord (.cv r) (synChwcn A)) (synCid)))
          (synCsn (synCec (.cv u) (synChwniso A)))))
  have p0019 :=
    @gSyl
      (.classMem (.cv z) (synCin (synChnord A)
          (synCima (synCcnv (synCdif (synClnqord (.cv r) (synChwcn A)) (synCid)))
            (synCsn (synCec (.cv u) (synChwniso A))))))
      (synWa (.classMem (.cv z) (synChnord A)) (.classMem (.cv z)
          (synCima (synCcnv (synCdif (synClnqord (.cv r) (synChwcn A)) (synCid)))
            (synCsn (synCec (.cv u) (synChwniso A))))))
      (.classMem (.cv z)
        (synCima (synCcnv (synCdif (synClnqord (.cv r) (synChwcn A)) (synCid)))
          (synCsn (synCec (.cv u) (synChwniso A)))))
      p0005 p0018
  have p0020 :=
    @gEliniseg (synCdif (synClnqord (.cv r) (synChwcn A)) (synCid))
      (synCec (.cv u) (synChwniso A)) (.cv z)
  have p0021 :=
    @gBiimpi
      (.classMem (.cv z)
        (synCima (synCcnv (synCdif (synClnqord (.cv r) (synChwcn A)) (synCid)))
          (synCsn (synCec (.cv u) (synChwniso A)))))
      (synWbr (.cv z) (synCdif (synClnqord (.cv r) (synChwcn A)) (synCid))
        (synCec (.cv u) (synChwniso A)))
      p0020
  have p0022 :=
    @gSyl
      (.classMem (.cv z) (synCin (synChnord A)
          (synCima (synCcnv (synCdif (synClnqord (.cv r) (synChwcn A)) (synCid)))
            (synCsn (synCec (.cv u) (synChwniso A))))))
      (.classMem (.cv z)
        (synCima (synCcnv (synCdif (synClnqord (.cv r) (synChwcn A)) (synCid)))
          (synCsn (synCec (.cv u) (synChwniso A)))))
      (synWbr (.cv z) (synCdif (synClnqord (.cv r) (synChwcn A)) (synCid))
        (synCec (.cv u) (synChwniso A)))
      p0019 p0021
  have p0023 :=
    @gSyl
      (synWa (synWa (.classEq (.cv r) (synChncodecmpset A))
          (.classMem (.cv u) (synChwcn A))) (.classMem (.cv z) (synCin (synChnord A)
            (synCima (synCcnv (synCdif (synClnqord (.cv r) (synChwcn A)) (synCid)))
              (synCsn (synCec (.cv u) (synChwniso A)))))))
      (.classMem (.cv z) (synCin (synChnord A)
          (synCima (synCcnv (synCdif (synClnqord (.cv r) (synChwcn A)) (synCid)))
            (synCsn (synCec (.cv u) (synChwniso A))))))
      (synWbr (.cv z) (synCdif (synClnqord (.cv r) (synChwcn A)) (synCid))
        (synCec (.cv u) (synChwniso A)))
      p0003 p0022
  have p0024 :=
    @gSyl
      (synWa (synWa (synWa (.classEq (.cv r) (synChncodecmpset A))
            (.classMem (.cv u) (synChwcn A))) (.classMem (.cv z) (synCin (synChnord A)
              (synCima (synCcnv (synCdif (synClnqord (.cv r) (synChwcn A)) (synCid)))
                (synCsn (synCec (.cv u) (synChwniso A)))))))
        (synWa (.classMem (.cv v) (synChwcn A))
          (.classEq (.cv z) (synCec (.cv v) (synChwniso A)))))
      (synWa (synWa (.classEq (.cv r) (synChncodecmpset A))
          (.classMem (.cv u) (synChwcn A))) (.classMem (.cv z) (synCin (synChnord A)
            (synCima (synCcnv (synCdif (synClnqord (.cv r) (synChwcn A)) (synCid)))
              (synCsn (synCec (.cv u) (synChwniso A)))))))
      (synWbr (.cv z) (synCdif (synClnqord (.cv r) (synChwcn A)) (synCid))
        (synCec (.cv u) (synChwniso A)))
      p0014 p0023
  have p0025 :=
    @gSimpr
      (synWa (synWa (.classEq (.cv r) (synChncodecmpset A))
          (.classMem (.cv u) (synChwcn A))) (.classMem (.cv z) (synCin (synChnord A)
            (synCima (synCcnv (synCdif (synClnqord (.cv r) (synChwcn A)) (synCid)))
              (synCsn (synCec (.cv u) (synChwniso A)))))))
      (synWa (.classMem (.cv v) (synChwcn A))
        (.classEq (.cv z) (synCec (.cv v) (synChwniso A))))
  have p0026 :=
    @gSimprd
      (synWa (synWa (synWa (.classEq (.cv r) (synChncodecmpset A))
            (.classMem (.cv u) (synChwcn A))) (.classMem (.cv z) (synCin (synChnord A)
              (synCima (synCcnv (synCdif (synClnqord (.cv r) (synChwcn A)) (synCid)))
                (synCsn (synCec (.cv u) (synChwniso A)))))))
        (synWa (.classMem (.cv v) (synChwcn A))
          (.classEq (.cv z) (synCec (.cv v) (synChwniso A)))))
      (.classMem (.cv v) (synChwcn A))
      (.classEq (.cv z) (synCec (.cv v) (synChwniso A))) p0025
  have p0027 :=
    @gBreq1d
      (synWa (synWa (synWa (.classEq (.cv r) (synChncodecmpset A))
            (.classMem (.cv u) (synChwcn A))) (.classMem (.cv z) (synCin (synChnord A)
              (synCima (synCcnv (synCdif (synClnqord (.cv r) (synChwcn A)) (synCid)))
                (synCsn (synCec (.cv u) (synChwniso A)))))))
        (synWa (.classMem (.cv v) (synChwcn A))
          (.classEq (.cv z) (synCec (.cv v) (synChwniso A)))))
      (.cv z) (synCec (.cv v) (synChwniso A)) (synCec (.cv u) (synChwniso A))
      (synCdif (synClnqord (.cv r) (synChwcn A)) (synCid)) p0026
  have p0028 :=
    @gMpbid
      (synWa (synWa (synWa (.classEq (.cv r) (synChncodecmpset A))
            (.classMem (.cv u) (synChwcn A))) (.classMem (.cv z) (synCin (synChnord A)
              (synCima (synCcnv (synCdif (synClnqord (.cv r) (synChwcn A)) (synCid)))
                (synCsn (synCec (.cv u) (synChwniso A)))))))
        (synWa (.classMem (.cv v) (synChwcn A))
          (.classEq (.cv z) (synCec (.cv v) (synChwniso A)))))
      (synWbr (.cv z) (synCdif (synClnqord (.cv r) (synChwcn A)) (synCid))
        (synCec (.cv u) (synChwniso A)))
      (synWbr (synCec (.cv v) (synChwniso A))
        (synCdif (synClnqord (.cv r) (synChwcn A)) (synCid))
        (synCec (.cv u) (synChwniso A)))
      p0024 p0027
  have p0030 :=
    @gSimpl
      (synWa (.classEq (.cv r) (synChncodecmpset A)) (.classMem (.cv u) (synChwcn A)))
      (.classMem (.cv z) (synCin (synChnord A)
          (synCima (synCcnv (synCdif (synClnqord (.cv r) (synChwcn A)) (synCid)))
            (synCsn (synCec (.cv u) (synChwniso A))))))
  have p0031 :=
    @gSyl
      (synWa (synWa (synWa (.classEq (.cv r) (synChncodecmpset A))
            (.classMem (.cv u) (synChwcn A))) (.classMem (.cv z) (synCin (synChnord A)
              (synCima (synCcnv (synCdif (synClnqord (.cv r) (synChwcn A)) (synCid)))
                (synCsn (synCec (.cv u) (synChwniso A)))))))
        (synWa (.classMem (.cv v) (synChwcn A))
          (.classEq (.cv z) (synCec (.cv v) (synChwniso A)))))
      (synWa (synWa (.classEq (.cv r) (synChncodecmpset A))
          (.classMem (.cv u) (synChwcn A))) (.classMem (.cv z) (synCin (synChnord A)
            (synCima (synCcnv (synCdif (synClnqord (.cv r) (synChwcn A)) (synCid)))
              (synCsn (synCec (.cv u) (synChwniso A)))))))
      (synWa (.classEq (.cv r) (synChncodecmpset A)) (.classMem (.cv u) (synChwcn A)))
      p0014 p0030
  have p0032 :=
    @gSimpl (.classEq (.cv r) (synChncodecmpset A)) (.classMem (.cv u) (synChwcn A))
  have p0033 :=
    @gSyl
      (synWa (synWa (synWa (.classEq (.cv r) (synChncodecmpset A))
            (.classMem (.cv u) (synChwcn A))) (.classMem (.cv z) (synCin (synChnord A)
              (synCima (synCcnv (synCdif (synClnqord (.cv r) (synChwcn A)) (synCid)))
                (synCsn (synCec (.cv u) (synChwniso A)))))))
        (synWa (.classMem (.cv v) (synChwcn A))
          (.classEq (.cv z) (synCec (.cv v) (synChwniso A)))))
      (synWa (.classEq (.cv r) (synChncodecmpset A)) (.classMem (.cv u) (synChwcn A)))
      (.classEq (.cv r) (synChncodecmpset A)) p0031 p0032
  have p0035 :=
    @gSimpld
      (synWa (synWa (synWa (.classEq (.cv r) (synChncodecmpset A))
            (.classMem (.cv u) (synChwcn A))) (.classMem (.cv z) (synCin (synChnord A)
              (synCima (synCcnv (synCdif (synClnqord (.cv r) (synChwcn A)) (synCid)))
                (synCsn (synCec (.cv u) (synChwniso A)))))))
        (synWa (.classMem (.cv v) (synChwcn A))
          (.classEq (.cv z) (synCec (.cv v) (synChwniso A)))))
      (.classMem (.cv v) (synChwcn A))
      (.classEq (.cv z) (synCec (.cv v) (synChwniso A))) p0025
  have p0040 :=
    @gSyl
      (synWa (synWa (synWa (.classEq (.cv r) (synChncodecmpset A))
            (.classMem (.cv u) (synChwcn A))) (.classMem (.cv z) (synCin (synChnord A)
              (synCima (synCcnv (synCdif (synClnqord (.cv r) (synChwcn A)) (synCid)))
                (synCsn (synCec (.cv u) (synChwniso A)))))))
        (synWa (.classMem (.cv v) (synChwcn A))
          (.classEq (.cv z) (synCec (.cv v) (synChwniso A)))))
      (synWa (.classEq (.cv r) (synChncodecmpset A)) (.classMem (.cv u) (synChwcn A)))
      (.classMem (.cv u) (synChwcn A)) p0031 p0000
  have p0041 :=
    @gJca
      (synWa (synWa (synWa (.classEq (.cv r) (synChncodecmpset A))
            (.classMem (.cv u) (synChwcn A))) (.classMem (.cv z) (synCin (synChnord A)
              (synCima (synCcnv (synCdif (synClnqord (.cv r) (synChwcn A)) (synCid)))
                (synCsn (synCec (.cv u) (synChwniso A)))))))
        (synWa (.classMem (.cv v) (synChwcn A))
          (.classEq (.cv z) (synCec (.cv v) (synChwniso A)))))
      (.classMem (.cv v) (synChwcn A)) (.classMem (.cv u) (synChwcn A)) p0035 p0040
  have p0042 :=
    @gJca
      (synWa (synWa (synWa (.classEq (.cv r) (synChncodecmpset A))
            (.classMem (.cv u) (synChwcn A))) (.classMem (.cv z) (synCin (synChnord A)
              (synCima (synCcnv (synCdif (synClnqord (.cv r) (synChwcn A)) (synCid)))
                (synCsn (synCec (.cv u) (synChwniso A)))))))
        (synWa (.classMem (.cv v) (synChwcn A))
          (.classEq (.cv z) (synCec (.cv v) (synChwniso A)))))
      (.classEq (.cv r) (synChncodecmpset A))
      (synWa (.classMem (.cv v) (synChwcn A)) (.classMem (.cv u) (synChwcn A))) p0033
      p0041
  have p0043 :=
    @gHncodecmpquotstrictbrproxyimpclndv A (.cv v) (.cv u) r dv_cache_0007
      hyp_hnwcutstrictsegimp_1
  have p0044 :=
    @gSyl
      (synWa (synWa (synWa (.classEq (.cv r) (synChncodecmpset A))
            (.classMem (.cv u) (synChwcn A))) (.classMem (.cv z) (synCin (synChnord A)
              (synCima (synCcnv (synCdif (synClnqord (.cv r) (synChwcn A)) (synCid)))
                (synCsn (synCec (.cv u) (synChwniso A)))))))
        (synWa (.classMem (.cv v) (synChwcn A))
          (.classEq (.cv z) (synCec (.cv v) (synChwniso A)))))
      (synWa (.classEq (.cv r) (synChncodecmpset A))
        (synWa (.classMem (.cv v) (synChwcn A)) (.classMem (.cv u) (synChwcn A))))
      (synWb (synWbr (synCec (.cv v) (synChwniso A))
          (synCdif (synClnqord (.cv r) (synChwcn A)) (synCid))
          (synCec (.cv u) (synChwniso A)))
        (synWbr (.cv v) (synCdif (synChncodecmpset A) (synCcnv (synChncodecmpset A)))
          (.cv u)))
      p0042 p0043
  have p0045 :=
    @gMpbid
      (synWa (synWa (synWa (.classEq (.cv r) (synChncodecmpset A))
            (.classMem (.cv u) (synChwcn A))) (.classMem (.cv z) (synCin (synChnord A)
              (synCima (synCcnv (synCdif (synClnqord (.cv r) (synChwcn A)) (synCid)))
                (synCsn (synCec (.cv u) (synChwniso A)))))))
        (synWa (.classMem (.cv v) (synChwcn A))
          (.classEq (.cv z) (synCec (.cv v) (synChwniso A)))))
      (synWbr (synCec (.cv v) (synChwniso A))
        (synCdif (synClnqord (.cv r) (synChwcn A)) (synCid))
        (synCec (.cv u) (synChwniso A)))
      (synWbr (.cv v) (synCdif (synChncodecmpset A) (synCcnv (synChncodecmpset A)))
        (.cv u))
      p0028 p0044
  have p0046 :=
    @gA1i (.classMem A (synCvv))
      (synWa (synWa (synWa (.classEq (.cv r) (synChncodecmpset A))
            (.classMem (.cv u) (synChwcn A))) (.classMem (.cv z) (synCin (synChnord A)
              (synCima (synCcnv (synCdif (synClnqord (.cv r) (synChwcn A)) (synCid)))
                (synCsn (synCec (.cv u) (synChwniso A)))))))
        (synWa (.classMem (.cv v) (synChwcn A))
          (.classEq (.cv z) (synCec (.cv v) (synChwniso A)))))
      hyp_hnwcutstrictsegimp_1
  have p0055 :=
    @gJca
      (synWa (synWa (synWa (.classEq (.cv r) (synChncodecmpset A))
            (.classMem (.cv u) (synChwcn A))) (.classMem (.cv z) (synCin (synChnord A)
              (synCima (synCcnv (synCdif (synClnqord (.cv r) (synChwcn A)) (synCid)))
                (synCsn (synCec (.cv u) (synChwniso A)))))))
        (synWa (.classMem (.cv v) (synChwcn A))
          (.classEq (.cv z) (synCec (.cv v) (synChwniso A)))))
      (.classMem A (synCvv))
      (synWa (.classMem (.cv v) (synChwcn A)) (.classMem (.cv u) (synChwcn A))) p0046
      p0041
  have p0056 :=
    @gHncodecmpstrictbrndv x u v A dv_cache_0005 dv_cache_0001 dv_cache_0002
      dv_cache_0008 dv_cache_0009 dv_cache_0003
  have p0057 :=
    @gSyl
      (synWa (synWa (synWa (.classEq (.cv r) (synChncodecmpset A))
            (.classMem (.cv u) (synChwcn A))) (.classMem (.cv z) (synCin (synChnord A)
              (synCima (synCcnv (synCdif (synClnqord (.cv r) (synChwcn A)) (synCid)))
                (synCsn (synCec (.cv u) (synChwniso A)))))))
        (synWa (.classMem (.cv v) (synChwcn A))
          (.classEq (.cv z) (synCec (.cv v) (synChwniso A)))))
      (synWa (.classMem A (synCvv))
        (synWa (.classMem (.cv v) (synChwcn A)) (.classMem (.cv u) (synChwcn A))))
      (synWb (synWbr (.cv v) (synCdif (synChncodecmpset A) (synCcnv (synChncodecmpset A)))
          (.cv u)) (synWrex x (synCfv (synC2nd) (.cv u)) (synWbr (.cv v) (synChwniso A)
            (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u))
              (.cv x)))))
      p0055 p0056
  have p0058 :=
    @gMpbid
      (synWa (synWa (synWa (.classEq (.cv r) (synChncodecmpset A))
            (.classMem (.cv u) (synChwcn A))) (.classMem (.cv z) (synCin (synChnord A)
              (synCima (synCcnv (synCdif (synClnqord (.cv r) (synChwcn A)) (synCid)))
                (synCsn (synCec (.cv u) (synChwniso A)))))))
        (synWa (.classMem (.cv v) (synChwcn A))
          (.classEq (.cv z) (synCec (.cv v) (synChwniso A)))))
      (synWbr (.cv v) (synCdif (synChncodecmpset A) (synCcnv (synChncodecmpset A)))
        (.cv u))
      (synWrex x (synCfv (synC2nd) (.cv u)) (synWbr (.cv v) (synChwniso A)
          (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u)) (.cv x))))
      p0045 p0057
  have p0059 :=
    @gSimpr
      (synWa (synWa (synWa (synWa (.classEq (.cv r) (synChncodecmpset A))
              (.classMem (.cv u) (synChwcn A))) (.classMem (.cv z) (synCin (synChnord A)
                (synCima (synCcnv (synCdif (synClnqord (.cv r) (synChwcn A)) (synCid)))
                  (synCsn (synCec (.cv u) (synChwniso A)))))))
          (synWa (.classMem (.cv v) (synChwcn A))
            (.classEq (.cv z) (synCec (.cv v) (synChwniso A)))))
        (.classMem (.cv x) (synCfv (synC2nd) (.cv u))))
      (synWbr (.cv v) (synChwniso A)
        (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u)) (.cv x)))
  have p0060 :=
    @gSimpl
      (synWa (synWa (synWa (synWa (.classEq (.cv r) (synChncodecmpset A))
              (.classMem (.cv u) (synChwcn A))) (.classMem (.cv z) (synCin (synChnord A)
                (synCima (synCcnv (synCdif (synClnqord (.cv r) (synChwcn A)) (synCid)))
                  (synCsn (synCec (.cv u) (synChwniso A)))))))
          (synWa (.classMem (.cv v) (synChwcn A))
            (.classEq (.cv z) (synCec (.cv v) (synChwniso A)))))
        (.classMem (.cv x) (synCfv (synC2nd) (.cv u))))
      (synWbr (.cv v) (synChwniso A)
        (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u)) (.cv x)))
  have p0061 :=
    @gSimpl
      (synWa (synWa (synWa (.classEq (.cv r) (synChncodecmpset A))
            (.classMem (.cv u) (synChwcn A))) (.classMem (.cv z) (synCin (synChnord A)
              (synCima (synCcnv (synCdif (synClnqord (.cv r) (synChwcn A)) (synCid)))
                (synCsn (synCec (.cv u) (synChwniso A)))))))
        (synWa (.classMem (.cv v) (synChwcn A))
          (.classEq (.cv z) (synCec (.cv v) (synChwniso A)))))
      (.classMem (.cv x) (synCfv (synC2nd) (.cv u)))
  have p0062 :=
    @gSyl
      (synWa (synWa (synWa (synWa (synWa (.classEq (.cv r) (synChncodecmpset A))
                (.classMem (.cv u) (synChwcn A))) (.classMem (.cv z) (synCin (synChnord A)
                  (synCima (synCcnv (synCdif (synClnqord (.cv r) (synChwcn A)) (synCid)))
                    (synCsn (synCec (.cv u) (synChwniso A)))))))
            (synWa (.classMem (.cv v) (synChwcn A))
              (.classEq (.cv z) (synCec (.cv v) (synChwniso A)))))
          (.classMem (.cv x) (synCfv (synC2nd) (.cv u)))) (synWbr (.cv v) (synChwniso A)
          (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u)) (.cv x))))
      (synWa (synWa (synWa (synWa (.classEq (.cv r) (synChncodecmpset A))
              (.classMem (.cv u) (synChwcn A))) (.classMem (.cv z) (synCin (synChnord A)
                (synCima (synCcnv (synCdif (synClnqord (.cv r) (synChwcn A)) (synCid)))
                  (synCsn (synCec (.cv u) (synChwniso A)))))))
          (synWa (.classMem (.cv v) (synChwcn A))
            (.classEq (.cv z) (synCec (.cv v) (synChwniso A)))))
        (.classMem (.cv x) (synCfv (synC2nd) (.cv u))))
      (synWa (synWa (synWa (.classEq (.cv r) (synChncodecmpset A))
            (.classMem (.cv u) (synChwcn A))) (.classMem (.cv z) (synCin (synChnord A)
              (synCima (synCcnv (synCdif (synClnqord (.cv r) (synChwcn A)) (synCid)))
                (synCsn (synCec (.cv u) (synChwniso A)))))))
        (synWa (.classMem (.cv v) (synChwcn A))
          (.classEq (.cv z) (synCec (.cv v) (synChwniso A)))))
      p0060 p0061
  have p0065 :=
    @gSyl
      (synWa (synWa (synWa (synWa (synWa (.classEq (.cv r) (synChncodecmpset A))
                (.classMem (.cv u) (synChwcn A))) (.classMem (.cv z) (synCin (synChnord A)
                  (synCima (synCcnv (synCdif (synClnqord (.cv r) (synChwcn A)) (synCid)))
                    (synCsn (synCec (.cv u) (synChwniso A)))))))
            (synWa (.classMem (.cv v) (synChwcn A))
              (.classEq (.cv z) (synCec (.cv v) (synChwniso A)))))
          (.classMem (.cv x) (synCfv (synC2nd) (.cv u)))) (synWbr (.cv v) (synChwniso A)
          (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u)) (.cv x))))
      (synWa (synWa (synWa (.classEq (.cv r) (synChncodecmpset A))
            (.classMem (.cv u) (synChwcn A))) (.classMem (.cv z) (synCin (synChnord A)
              (synCima (synCcnv (synCdif (synClnqord (.cv r) (synChwcn A)) (synCid)))
                (synCsn (synCec (.cv u) (synChwniso A)))))))
        (synWa (.classMem (.cv v) (synChwcn A))
          (.classEq (.cv z) (synCec (.cv v) (synChwniso A)))))
      (.classMem (.cv v) (synChwcn A)) p0062 p0035
  have p0074 :=
    @gSyl
      (synWa (synWa (synWa (synWa (synWa (.classEq (.cv r) (synChncodecmpset A))
                (.classMem (.cv u) (synChwcn A))) (.classMem (.cv z) (synCin (synChnord A)
                  (synCima (synCcnv (synCdif (synClnqord (.cv r) (synChwcn A)) (synCid)))
                    (synCsn (synCec (.cv u) (synChwniso A)))))))
            (synWa (.classMem (.cv v) (synChwcn A))
              (.classEq (.cv z) (synCec (.cv v) (synChwniso A)))))
          (.classMem (.cv x) (synCfv (synC2nd) (.cv u)))) (synWbr (.cv v) (synChwniso A)
          (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u)) (.cv x))))
      (synWa (synWa (synWa (.classEq (.cv r) (synChncodecmpset A))
            (.classMem (.cv u) (synChwcn A))) (.classMem (.cv z) (synCin (synChnord A)
              (synCima (synCcnv (synCdif (synClnqord (.cv r) (synChwcn A)) (synCid)))
                (synCsn (synCec (.cv u) (synChwniso A)))))))
        (synWa (.classMem (.cv v) (synChwcn A))
          (.classEq (.cv z) (synCec (.cv v) (synChwniso A)))))
      (.classMem (.cv u) (synChwcn A)) p0062 p0040
  have p0076 :=
    @gSimpr
      (synWa (synWa (synWa (.classEq (.cv r) (synChncodecmpset A))
            (.classMem (.cv u) (synChwcn A))) (.classMem (.cv z) (synCin (synChnord A)
              (synCima (synCcnv (synCdif (synClnqord (.cv r) (synChwcn A)) (synCid)))
                (synCsn (synCec (.cv u) (synChwniso A)))))))
        (synWa (.classMem (.cv v) (synChwcn A))
          (.classEq (.cv z) (synCec (.cv v) (synChwniso A)))))
      (.classMem (.cv x) (synCfv (synC2nd) (.cv u)))
  have p0077 :=
    @gSyl
      (synWa (synWa (synWa (synWa (synWa (.classEq (.cv r) (synChncodecmpset A))
                (.classMem (.cv u) (synChwcn A))) (.classMem (.cv z) (synCin (synChnord A)
                  (synCima (synCcnv (synCdif (synClnqord (.cv r) (synChwcn A)) (synCid)))
                    (synCsn (synCec (.cv u) (synChwniso A)))))))
            (synWa (.classMem (.cv v) (synChwcn A))
              (.classEq (.cv z) (synCec (.cv v) (synChwniso A)))))
          (.classMem (.cv x) (synCfv (synC2nd) (.cv u)))) (synWbr (.cv v) (synChwniso A)
          (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u)) (.cv x))))
      (synWa (synWa (synWa (synWa (.classEq (.cv r) (synChncodecmpset A))
              (.classMem (.cv u) (synChwcn A))) (.classMem (.cv z) (synCin (synChnord A)
                (synCima (synCcnv (synCdif (synClnqord (.cv r) (synChwcn A)) (synCid)))
                  (synCsn (synCec (.cv u) (synChwniso A)))))))
          (synWa (.classMem (.cv v) (synChwcn A))
            (.classEq (.cv z) (synCec (.cv v) (synChwniso A)))))
        (.classMem (.cv x) (synCfv (synC2nd) (.cv u))))
      (.classMem (.cv x) (synCfv (synC2nd) (.cv u))) p0060 p0076
  have p0078 :=
    @gJca
      (synWa (synWa (synWa (synWa (synWa (.classEq (.cv r) (synChncodecmpset A))
                (.classMem (.cv u) (synChwcn A))) (.classMem (.cv z) (synCin (synChnord A)
                  (synCima (synCcnv (synCdif (synClnqord (.cv r) (synChwcn A)) (synCid)))
                    (synCsn (synCec (.cv u) (synChwniso A)))))))
            (synWa (.classMem (.cv v) (synChwcn A))
              (.classEq (.cv z) (synCec (.cv v) (synChwniso A)))))
          (.classMem (.cv x) (synCfv (synC2nd) (.cv u)))) (synWbr (.cv v) (synChwniso A)
          (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u)) (.cv x))))
      (.classMem (.cv u) (synChwcn A)) (.classMem (.cv x) (synCfv (synC2nd) (.cv u)))
      p0074 p0077
  have p0079 := @gHnwcutcodeambientclndv u A (.cv x) dv_cache_0001
  have p0080 :=
    @gSyl
      (synWa (synWa (synWa (synWa (synWa (.classEq (.cv r) (synChncodecmpset A))
                (.classMem (.cv u) (synChwcn A))) (.classMem (.cv z) (synCin (synChnord A)
                  (synCima (synCcnv (synCdif (synClnqord (.cv r) (synChwcn A)) (synCid)))
                    (synCsn (synCec (.cv u) (synChwniso A)))))))
            (synWa (.classMem (.cv v) (synChwcn A))
              (.classEq (.cv z) (synCec (.cv v) (synChwniso A)))))
          (.classMem (.cv x) (synCfv (synC2nd) (.cv u)))) (synWbr (.cv v) (synChwniso A)
          (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u)) (.cv x))))
      (synWa (.classMem (.cv u) (synChwcn A))
        (.classMem (.cv x) (synCfv (synC2nd) (.cv u))))
      (.classMem (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u))
          (.cv x)) (synChwcn A))
      p0078 p0079
  have p0081 :=
    @gJca
      (synWa (synWa (synWa (synWa (synWa (.classEq (.cv r) (synChncodecmpset A))
                (.classMem (.cv u) (synChwcn A))) (.classMem (.cv z) (synCin (synChnord A)
                  (synCima (synCcnv (synCdif (synClnqord (.cv r) (synChwcn A)) (synCid)))
                    (synCsn (synCec (.cv u) (synChwniso A)))))))
            (synWa (.classMem (.cv v) (synChwcn A))
              (.classEq (.cv z) (synCec (.cv v) (synChwniso A)))))
          (.classMem (.cv x) (synCfv (synC2nd) (.cv u)))) (synWbr (.cv v) (synChwniso A)
          (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u)) (.cv x))))
      (.classMem (.cv v) (synChwcn A))
      (.classMem (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u))
          (.cv x)) (synChwcn A))
      p0065 p0080
  have p0082 :=
    @gHwnisoclasseqbcl A (.cv v)
      (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u)) (.cv x))
      hyp_hnwcutstrictsegimp_1
  have p0083 :=
    @gSyl
      (synWa (synWa (synWa (synWa (synWa (.classEq (.cv r) (synChncodecmpset A))
                (.classMem (.cv u) (synChwcn A))) (.classMem (.cv z) (synCin (synChnord A)
                  (synCima (synCcnv (synCdif (synClnqord (.cv r) (synChwcn A)) (synCid)))
                    (synCsn (synCec (.cv u) (synChwniso A)))))))
            (synWa (.classMem (.cv v) (synChwcn A))
              (.classEq (.cv z) (synCec (.cv v) (synChwniso A)))))
          (.classMem (.cv x) (synCfv (synC2nd) (.cv u)))) (synWbr (.cv v) (synChwniso A)
          (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u)) (.cv x))))
      (synWa (.classMem (.cv v) (synChwcn A)) (.classMem
          (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u)) (.cv x))
          (synChwcn A)))
      (synWb (.classEq (synCec (.cv v) (synChwniso A)) (synCec
            (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u)) (.cv x))
            (synChwniso A))) (synWbr (.cv v) (synChwniso A)
          (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u)) (.cv x))))
      p0081 p0082
  have p0084 :=
    @gMpbird
      (synWa (synWa (synWa (synWa (synWa (.classEq (.cv r) (synChncodecmpset A))
                (.classMem (.cv u) (synChwcn A))) (.classMem (.cv z) (synCin (synChnord A)
                  (synCima (synCcnv (synCdif (synClnqord (.cv r) (synChwcn A)) (synCid)))
                    (synCsn (synCec (.cv u) (synChwniso A)))))))
            (synWa (.classMem (.cv v) (synChwcn A))
              (.classEq (.cv z) (synCec (.cv v) (synChwniso A)))))
          (.classMem (.cv x) (synCfv (synC2nd) (.cv u)))) (synWbr (.cv v) (synChwniso A)
          (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u)) (.cv x))))
      (.classEq (synCec (.cv v) (synChwniso A)) (synCec
          (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u)) (.cv x))
          (synChwniso A)))
      (synWbr (.cv v) (synChwniso A)
        (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u)) (.cv x)))
      p0059 p0083
  have p0085 :=
    @gEqcomd
      (synWa (synWa (synWa (synWa (synWa (.classEq (.cv r) (synChncodecmpset A))
                (.classMem (.cv u) (synChwcn A))) (.classMem (.cv z) (synCin (synChnord A)
                  (synCima (synCcnv (synCdif (synClnqord (.cv r) (synChwcn A)) (synCid)))
                    (synCsn (synCec (.cv u) (synChwniso A)))))))
            (synWa (.classMem (.cv v) (synChwcn A))
              (.classEq (.cv z) (synCec (.cv v) (synChwniso A)))))
          (.classMem (.cv x) (synCfv (synC2nd) (.cv u)))) (synWbr (.cv v) (synChwniso A)
          (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u)) (.cv x))))
      (synCec (.cv v) (synChwniso A))
      (synCec (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u))
          (.cv x)) (synChwniso A))
      p0084
  have p0091 :=
    @gSyl
      (synWa (synWa (synWa (synWa (synWa (.classEq (.cv r) (synChncodecmpset A))
                (.classMem (.cv u) (synChwcn A))) (.classMem (.cv z) (synCin (synChnord A)
                  (synCima (synCcnv (synCdif (synClnqord (.cv r) (synChwcn A)) (synCid)))
                    (synCsn (synCec (.cv u) (synChwniso A)))))))
            (synWa (.classMem (.cv v) (synChwcn A))
              (.classEq (.cv z) (synCec (.cv v) (synChwniso A)))))
          (.classMem (.cv x) (synCfv (synC2nd) (.cv u)))) (synWbr (.cv v) (synChwniso A)
          (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u)) (.cv x))))
      (synWa (synWa (synWa (.classEq (.cv r) (synChncodecmpset A))
            (.classMem (.cv u) (synChwcn A))) (.classMem (.cv z) (synCin (synChnord A)
              (synCima (synCcnv (synCdif (synClnqord (.cv r) (synChwcn A)) (synCid)))
                (synCsn (synCec (.cv u) (synChwniso A)))))))
        (synWa (.classMem (.cv v) (synChwcn A))
          (.classEq (.cv z) (synCec (.cv v) (synChwniso A)))))
      (.classEq (.cv z) (synCec (.cv v) (synChwniso A))) p0062 p0026
  have p0092 :=
    @gEqtr4d
      (synWa (synWa (synWa (synWa (synWa (.classEq (.cv r) (synChncodecmpset A))
                (.classMem (.cv u) (synChwcn A))) (.classMem (.cv z) (synCin (synChnord A)
                  (synCima (synCcnv (synCdif (synClnqord (.cv r) (synChwcn A)) (synCid)))
                    (synCsn (synCec (.cv u) (synChwniso A)))))))
            (synWa (.classMem (.cv v) (synChwcn A))
              (.classEq (.cv z) (synCec (.cv v) (synChwniso A)))))
          (.classMem (.cv x) (synCfv (synC2nd) (.cv u)))) (synWbr (.cv v) (synChwniso A)
          (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u)) (.cv x))))
      (synCec (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u))
          (.cv x)) (synChwniso A))
      (synCec (.cv v) (synChwniso A)) (.cv z) p0085 p0091
  have p0093 :=
    @gEx
      (synWa (synWa (synWa (synWa (.classEq (.cv r) (synChncodecmpset A))
              (.classMem (.cv u) (synChwcn A))) (.classMem (.cv z) (synCin (synChnord A)
                (synCima (synCcnv (synCdif (synClnqord (.cv r) (synChwcn A)) (synCid)))
                  (synCsn (synCec (.cv u) (synChwniso A)))))))
          (synWa (.classMem (.cv v) (synChwcn A))
            (.classEq (.cv z) (synCec (.cv v) (synChwniso A)))))
        (.classMem (.cv x) (synCfv (synC2nd) (.cv u))))
      (synWbr (.cv v) (synChwniso A)
        (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u)) (.cv x)))
      (.classEq (synCec
          (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u)) (.cv x))
          (synChwniso A)) (.cv z))
      p0092
  have p0094 :=
    @gReximdva
      (synWa (synWa (synWa (.classEq (.cv r) (synChncodecmpset A))
            (.classMem (.cv u) (synChwcn A))) (.classMem (.cv z) (synCin (synChnord A)
              (synCima (synCcnv (synCdif (synClnqord (.cv r) (synChwcn A)) (synCid)))
                (synCsn (synCec (.cv u) (synChwniso A)))))))
        (synWa (.classMem (.cv v) (synChwcn A))
          (.classEq (.cv z) (synCec (.cv v) (synChwniso A)))))
      (synWbr (.cv v) (synChwniso A)
        (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u)) (.cv x)))
      (.classEq (synCec
          (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u)) (.cv x))
          (synChwniso A)) (.cv z))
      x (synCfv (synC2nd) (.cv u)) dv_cache_0010 p0093
  have p0095 :=
    @gMpd
      (synWa (synWa (synWa (.classEq (.cv r) (synChncodecmpset A))
            (.classMem (.cv u) (synChwcn A))) (.classMem (.cv z) (synCin (synChnord A)
              (synCima (synCcnv (synCdif (synClnqord (.cv r) (synChwcn A)) (synCid)))
                (synCsn (synCec (.cv u) (synChwniso A)))))))
        (synWa (.classMem (.cv v) (synChwcn A))
          (.classEq (.cv z) (synCec (.cv v) (synChwniso A)))))
      (synWrex x (synCfv (synC2nd) (.cv u)) (synWbr (.cv v) (synChwniso A)
          (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u)) (.cv x))))
      (synWrex x (synCfv (synC2nd) (.cv u)) (.classEq (synCec
            (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u)) (.cv x))
            (synChwniso A)) (.cv z)))
      p0058 p0094
  have p0096 :=
    @gRexlimddv
      (synWa (synWa (.classEq (.cv r) (synChncodecmpset A))
          (.classMem (.cv u) (synChwcn A))) (.classMem (.cv z) (synCin (synChnord A)
            (synCima (synCcnv (synCdif (synClnqord (.cv r) (synChwcn A)) (synCid)))
              (synCsn (synCec (.cv u) (synChwniso A)))))))
      (.classEq (.cv z) (synCec (.cv v) (synChwniso A)))
      (synWrex x (synCfv (synC2nd) (.cv u)) (.classEq (synCec
            (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u)) (.cv x))
            (synChwniso A)) (.cv z)))
      v (synChwcn A) dv_cache_0011 dv_cache_0012 p0013 p0095
  have p0097 :=
    @gEx
      (synWa (.classEq (.cv r) (synChncodecmpset A)) (.classMem (.cv u) (synChwcn A)))
      (.classMem (.cv z) (synCin (synChnord A)
          (synCima (synCcnv (synCdif (synClnqord (.cv r) (synChwcn A)) (synCid)))
            (synCsn (synCec (.cv u) (synChwniso A))))))
      (synWrex x (synCfv (synC2nd) (.cv u)) (.classEq (synCec
            (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u)) (.cv x))
            (synChwniso A)) (.cv z)))
      p0096
  have p0098 :=
    @gSimpl
      (synWa (synWa (.classEq (.cv r) (synChncodecmpset A))
          (.classMem (.cv u) (synChwcn A))) (.classMem (.cv x) (synCfv (synC2nd) (.cv u))))
      (.classEq (synCec
          (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u)) (.cv x))
          (synChwniso A)) (.cv z))
  have p0099 :=
    @gSimpl
      (synWa (.classEq (.cv r) (synChncodecmpset A)) (.classMem (.cv u) (synChwcn A)))
      (.classMem (.cv x) (synCfv (synC2nd) (.cv u)))
  have p0101 :=
    @gSyl
      (synWa (synWa (.classEq (.cv r) (synChncodecmpset A))
          (.classMem (.cv u) (synChwcn A))) (.classMem (.cv x) (synCfv (synC2nd) (.cv u))))
      (synWa (.classEq (.cv r) (synChncodecmpset A)) (.classMem (.cv u) (synChwcn A)))
      (.classMem (.cv u) (synChwcn A)) p0099 p0000
  have p0102 :=
    @gSimpr
      (synWa (.classEq (.cv r) (synChncodecmpset A)) (.classMem (.cv u) (synChwcn A)))
      (.classMem (.cv x) (synCfv (synC2nd) (.cv u)))
  have p0103 :=
    @gJca
      (synWa (synWa (.classEq (.cv r) (synChncodecmpset A))
          (.classMem (.cv u) (synChwcn A))) (.classMem (.cv x) (synCfv (synC2nd) (.cv u))))
      (.classMem (.cv u) (synChwcn A)) (.classMem (.cv x) (synCfv (synC2nd) (.cv u)))
      p0101 p0102
  have p0105 :=
    @gSyl
      (synWa (synWa (.classEq (.cv r) (synChncodecmpset A))
          (.classMem (.cv u) (synChwcn A))) (.classMem (.cv x) (synCfv (synC2nd) (.cv u))))
      (synWa (.classMem (.cv u) (synChwcn A))
        (.classMem (.cv x) (synCfv (synC2nd) (.cv u))))
      (.classMem (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u))
          (.cv x)) (synChwcn A))
      p0103 p0079
  have p0106 :=
    @gHwnisoclasselhnordcl A
      (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u)) (.cv x))
      hyp_hnwcutstrictsegimp_1
  have p0107 :=
    @gSyl
      (synWa (synWa (.classEq (.cv r) (synChncodecmpset A))
          (.classMem (.cv u) (synChwcn A))) (.classMem (.cv x) (synCfv (synC2nd) (.cv u))))
      (.classMem (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u))
          (.cv x)) (synChwcn A))
      (.classMem (synCec
          (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u)) (.cv x))
          (synChwniso A)) (synChnord A))
      p0105 p0106
  have p0115 :=
    @gElex
      (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u)) (.cv x))
      (synChwcn A)
  have p0116 :=
    @gSyl
      (synWa (synWa (.classEq (.cv r) (synChncodecmpset A))
          (.classMem (.cv u) (synChwcn A))) (.classMem (.cv x) (synCfv (synC2nd) (.cv u))))
      (.classMem (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u))
          (.cv x)) (synChwcn A))
      (.classMem (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u))
          (.cv x)) (synCvv))
      p0105 p0115
  have p0117 :=
    @gIsset w
      (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u)) (.cv x))
      dv_cache_0013
  have p0118 :=
    @gA1i
      (synWb (.classMem
          (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u)) (.cv x))
          (synCvv)) (synWex w (.classEq (.cv w)
            (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u))
              (.cv x)))))
      (synWa (synWa (.classEq (.cv r) (synChncodecmpset A))
          (.classMem (.cv u) (synChwcn A))) (.classMem (.cv x) (synCfv (synC2nd) (.cv u))))
      p0117
  have p0119 :=
    @gMpbid
      (synWa (synWa (.classEq (.cv r) (synChncodecmpset A))
          (.classMem (.cv u) (synChwcn A))) (.classMem (.cv x) (synCfv (synC2nd) (.cv u))))
      (.classMem (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u))
          (.cv x)) (synCvv))
      (synWex w (.classEq (.cv w)
          (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u)) (.cv x))))
      p0116 p0118
  have p0120 :=
    @gSimpl
      (synWa (synWa (.classEq (.cv r) (synChncodecmpset A))
          (.classMem (.cv u) (synChwcn A))) (.classMem (.cv x) (synCfv (synC2nd) (.cv u))))
      (.classEq (.cv w)
        (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u)) (.cv x)))
  have p0128 :=
    @gSyl
      (synWa (synWa (synWa (.classEq (.cv r) (synChncodecmpset A))
            (.classMem (.cv u) (synChwcn A))) (.classMem (.cv x) (synCfv (synC2nd) (.cv u))))
        (.classEq (.cv w)
          (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u)) (.cv x))))
      (synWa (synWa (.classEq (.cv r) (synChncodecmpset A))
          (.classMem (.cv u) (synChwcn A))) (.classMem (.cv x) (synCfv (synC2nd) (.cv u))))
      (.classMem (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u))
          (.cv x)) (synChwcn A))
      p0120 p0105
  have p0129 :=
    @gSimpr
      (synWa (synWa (.classEq (.cv r) (synChncodecmpset A))
          (.classMem (.cv u) (synChwcn A))) (.classMem (.cv x) (synCfv (synC2nd) (.cv u))))
      (.classEq (.cv w)
        (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u)) (.cv x)))
  have p0130 :=
    @gEleq1d
      (synWa (synWa (synWa (.classEq (.cv r) (synChncodecmpset A))
            (.classMem (.cv u) (synChwcn A))) (.classMem (.cv x) (synCfv (synC2nd) (.cv u))))
        (.classEq (.cv w)
          (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u)) (.cv x))))
      (.cv w)
      (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u)) (.cv x))
      (synChwcn A) p0129
  have p0131 :=
    @gMpbird
      (synWa (synWa (synWa (.classEq (.cv r) (synChncodecmpset A))
            (.classMem (.cv u) (synChwcn A))) (.classMem (.cv x) (synCfv (synC2nd) (.cv u))))
        (.classEq (.cv w)
          (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u)) (.cv x))))
      (.classMem (.cv w) (synChwcn A))
      (.classMem (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u))
          (.cv x)) (synChwcn A))
      p0128 p0130
  have p0132 := @gHwnisorefli w A dv_cache_0014
  have p0133 :=
    @gSyl
      (synWa (synWa (synWa (.classEq (.cv r) (synChncodecmpset A))
            (.classMem (.cv u) (synChwcn A))) (.classMem (.cv x) (synCfv (synC2nd) (.cv u))))
        (.classEq (.cv w)
          (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u)) (.cv x))))
      (.classMem (.cv w) (synChwcn A)) (synWbr (.cv w) (synChwniso A) (.cv w)) p0131
      p0132
  have p0135 :=
    @gBreq2d
      (synWa (synWa (synWa (.classEq (.cv r) (synChncodecmpset A))
            (.classMem (.cv u) (synChwcn A))) (.classMem (.cv x) (synCfv (synC2nd) (.cv u))))
        (.classEq (.cv w)
          (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u)) (.cv x))))
      (.cv w)
      (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u)) (.cv x))
      (.cv w) (synChwniso A) p0129
  have p0136 :=
    @gMpbid
      (synWa (synWa (synWa (.classEq (.cv r) (synChncodecmpset A))
            (.classMem (.cv u) (synChwcn A))) (.classMem (.cv x) (synCfv (synC2nd) (.cv u))))
        (.classEq (.cv w)
          (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u)) (.cv x))))
      (synWbr (.cv w) (synChwniso A) (.cv w))
      (synWbr (.cv w) (synChwniso A)
        (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u)) (.cv x)))
      p0133 p0135
  have p0139 :=
    @gSyl
      (synWa (synWa (synWa (.classEq (.cv r) (synChncodecmpset A))
            (.classMem (.cv u) (synChwcn A))) (.classMem (.cv x) (synCfv (synC2nd) (.cv u))))
        (.classEq (.cv w)
          (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u)) (.cv x))))
      (synWa (synWa (.classEq (.cv r) (synChncodecmpset A))
          (.classMem (.cv u) (synChwcn A))) (.classMem (.cv x) (synCfv (synC2nd) (.cv u))))
      (.classMem (.cv x) (synCfv (synC2nd) (.cv u))) p0120 p0102
  have p0140 :=
    @gSimpr
      (synWa (synWa (synWa (.classEq (.cv r) (synChncodecmpset A))
            (.classMem (.cv u) (synChwcn A))) (.classMem (.cv x) (synCfv (synC2nd) (.cv u))))
        (.classEq (.cv w)
          (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u)) (.cv x))))
      (.classEq (.cv y) (.cv x))
  have p0141 :=
    @gHnwcutcodeeq3 (.cv y) (.cv x) (synCfv (synC2nd) (.cv u))
      (synCfv (synC1st) (.cv u)) dv_cache_0015
  have p0142 :=
    @gSyl
      (synWa (synWa (synWa (synWa (.classEq (.cv r) (synChncodecmpset A))
              (.classMem (.cv u) (synChwcn A)))
            (.classMem (.cv x) (synCfv (synC2nd) (.cv u)))) (.classEq (.cv w)
            (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u))
              (.cv x)))) (.classEq (.cv y) (.cv x)))
      (.classEq (.cv y) (.cv x))
      (.classEq (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u))
          (.cv y)) (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u))
          (.cv x)))
      p0140 p0141
  have p0143 :=
    @gBreq2d
      (synWa (synWa (synWa (synWa (.classEq (.cv r) (synChncodecmpset A))
              (.classMem (.cv u) (synChwcn A)))
            (.classMem (.cv x) (synCfv (synC2nd) (.cv u)))) (.classEq (.cv w)
            (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u))
              (.cv x)))) (.classEq (.cv y) (.cv x)))
      (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u)) (.cv y))
      (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u)) (.cv x))
      (.cv w) (synChwniso A) p0142
  have p0144 :=
    @gRspcedv
      (synWa (synWa (synWa (.classEq (.cv r) (synChncodecmpset A))
            (.classMem (.cv u) (synChwcn A))) (.classMem (.cv x) (synCfv (synC2nd) (.cv u))))
        (.classEq (.cv w)
          (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u)) (.cv x))))
      (synWbr (.cv w) (synChwniso A)
        (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u)) (.cv y)))
      (synWbr (.cv w) (synChwniso A)
        (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u)) (.cv x)))
      y (.cv x) (synCfv (synC2nd) (.cv u)) dv_cache_0016 dv_cache_0017 dv_cache_0018
      dv_cache_0019 p0139 p0143
  have p0145 :=
    @gMpd
      (synWa (synWa (synWa (.classEq (.cv r) (synChncodecmpset A))
            (.classMem (.cv u) (synChwcn A))) (.classMem (.cv x) (synCfv (synC2nd) (.cv u))))
        (.classEq (.cv w)
          (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u)) (.cv x))))
      (synWbr (.cv w) (synChwniso A)
        (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u)) (.cv x)))
      (synWrex y (synCfv (synC2nd) (.cv u)) (synWbr (.cv w) (synChwniso A)
          (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u)) (.cv y))))
      p0136 p0144
  have p0146 :=
    @gA1i (.classMem A (synCvv))
      (synWa (synWa (synWa (.classEq (.cv r) (synChncodecmpset A))
            (.classMem (.cv u) (synChwcn A))) (.classMem (.cv x) (synCfv (synC2nd) (.cv u))))
        (.classEq (.cv w)
          (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u)) (.cv x))))
      hyp_hnwcutstrictsegimp_1
  have p0163 :=
    @gSyl
      (synWa (synWa (synWa (.classEq (.cv r) (synChncodecmpset A))
            (.classMem (.cv u) (synChwcn A))) (.classMem (.cv x) (synCfv (synC2nd) (.cv u))))
        (.classEq (.cv w)
          (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u)) (.cv x))))
      (synWa (synWa (.classEq (.cv r) (synChncodecmpset A))
          (.classMem (.cv u) (synChwcn A))) (.classMem (.cv x) (synCfv (synC2nd) (.cv u))))
      (.classMem (.cv u) (synChwcn A)) p0120 p0101
  have p0164 :=
    @gJca
      (synWa (synWa (synWa (.classEq (.cv r) (synChncodecmpset A))
            (.classMem (.cv u) (synChwcn A))) (.classMem (.cv x) (synCfv (synC2nd) (.cv u))))
        (.classEq (.cv w)
          (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u)) (.cv x))))
      (.classMem (.cv w) (synChwcn A)) (.classMem (.cv u) (synChwcn A)) p0131 p0163
  have p0165 :=
    @gJca
      (synWa (synWa (synWa (.classEq (.cv r) (synChncodecmpset A))
            (.classMem (.cv u) (synChwcn A))) (.classMem (.cv x) (synCfv (synC2nd) (.cv u))))
        (.classEq (.cv w)
          (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u)) (.cv x))))
      (.classMem A (synCvv))
      (synWa (.classMem (.cv w) (synChwcn A)) (.classMem (.cv u) (synChwcn A))) p0146
      p0164
  have p0166 :=
    @gHncodecmpstrictbrndv y u w A dv_cache_0014 dv_cache_0001 dv_cache_0020
      dv_cache_0021 dv_cache_0022 dv_cache_0023
  have p0167 :=
    @gSyl
      (synWa (synWa (synWa (.classEq (.cv r) (synChncodecmpset A))
            (.classMem (.cv u) (synChwcn A))) (.classMem (.cv x) (synCfv (synC2nd) (.cv u))))
        (.classEq (.cv w)
          (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u)) (.cv x))))
      (synWa (.classMem A (synCvv))
        (synWa (.classMem (.cv w) (synChwcn A)) (.classMem (.cv u) (synChwcn A))))
      (synWb (synWbr (.cv w) (synCdif (synChncodecmpset A) (synCcnv (synChncodecmpset A)))
          (.cv u)) (synWrex y (synCfv (synC2nd) (.cv u)) (synWbr (.cv w) (synChwniso A)
            (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u))
              (.cv y)))))
      p0165 p0166
  have p0168 :=
    @gMpbird
      (synWa (synWa (synWa (.classEq (.cv r) (synChncodecmpset A))
            (.classMem (.cv u) (synChwcn A))) (.classMem (.cv x) (synCfv (synC2nd) (.cv u))))
        (.classEq (.cv w)
          (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u)) (.cv x))))
      (synWbr (.cv w) (synCdif (synChncodecmpset A) (synCcnv (synChncodecmpset A)))
        (.cv u))
      (synWrex y (synCfv (synC2nd) (.cv u)) (synWbr (.cv w) (synChwniso A)
          (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u)) (.cv y))))
      p0145 p0167
  have p0170 :=
    @gBreq1d
      (synWa (synWa (synWa (.classEq (.cv r) (synChncodecmpset A))
            (.classMem (.cv u) (synChwcn A))) (.classMem (.cv x) (synCfv (synC2nd) (.cv u))))
        (.classEq (.cv w)
          (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u)) (.cv x))))
      (.cv w)
      (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u)) (.cv x))
      (.cv u) (synCdif (synChncodecmpset A) (synCcnv (synChncodecmpset A))) p0129
  have p0171 :=
    @gMpbid
      (synWa (synWa (synWa (.classEq (.cv r) (synChncodecmpset A))
            (.classMem (.cv u) (synChwcn A))) (.classMem (.cv x) (synCfv (synC2nd) (.cv u))))
        (.classEq (.cv w)
          (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u)) (.cv x))))
      (synWbr (.cv w) (synCdif (synChncodecmpset A) (synCcnv (synChncodecmpset A)))
        (.cv u))
      (synWbr (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u))
          (.cv x)) (synCdif (synChncodecmpset A) (synCcnv (synChncodecmpset A))) (.cv u))
      p0168 p0170
  have p0172 :=
    @gExlimddv
      (synWa (synWa (.classEq (.cv r) (synChncodecmpset A))
          (.classMem (.cv u) (synChwcn A))) (.classMem (.cv x) (synCfv (synC2nd) (.cv u))))
      (.classEq (.cv w)
        (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u)) (.cv x)))
      (synWbr (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u))
          (.cv x)) (synCdif (synChncodecmpset A) (synCcnv (synChncodecmpset A))) (.cv u))
      w dv_cache_0024 dv_cache_0025 p0119 p0171
  have p0175 :=
    @gSyl
      (synWa (synWa (.classEq (.cv r) (synChncodecmpset A))
          (.classMem (.cv u) (synChwcn A))) (.classMem (.cv x) (synCfv (synC2nd) (.cv u))))
      (synWa (.classEq (.cv r) (synChncodecmpset A)) (.classMem (.cv u) (synChwcn A)))
      (.classEq (.cv r) (synChncodecmpset A)) p0099 p0032
  have p0186 :=
    @gJca
      (synWa (synWa (.classEq (.cv r) (synChncodecmpset A))
          (.classMem (.cv u) (synChwcn A))) (.classMem (.cv x) (synCfv (synC2nd) (.cv u))))
      (.classMem (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u))
          (.cv x)) (synChwcn A))
      (.classMem (.cv u) (synChwcn A)) p0105 p0101
  have p0187 :=
    @gJca
      (synWa (synWa (.classEq (.cv r) (synChncodecmpset A))
          (.classMem (.cv u) (synChwcn A))) (.classMem (.cv x) (synCfv (synC2nd) (.cv u))))
      (.classEq (.cv r) (synChncodecmpset A))
      (synWa (.classMem
          (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u)) (.cv x))
          (synChwcn A)) (.classMem (.cv u) (synChwcn A)))
      p0175 p0186
  have p0188 :=
    @gHncodecmpquotstrictbrproxyimpclndv A
      (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u)) (.cv x))
      (.cv u) r dv_cache_0007 hyp_hnwcutstrictsegimp_1
  have p0189 :=
    @gSyl
      (synWa (synWa (.classEq (.cv r) (synChncodecmpset A))
          (.classMem (.cv u) (synChwcn A))) (.classMem (.cv x) (synCfv (synC2nd) (.cv u))))
      (synWa (.classEq (.cv r) (synChncodecmpset A)) (synWa (.classMem
            (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u)) (.cv x))
            (synChwcn A)) (.classMem (.cv u) (synChwcn A))))
      (synWb (synWbr (synCec
            (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u)) (.cv x))
            (synChwniso A)) (synCdif (synClnqord (.cv r) (synChwcn A)) (synCid))
          (synCec (.cv u) (synChwniso A))) (synWbr
          (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u)) (.cv x))
          (synCdif (synChncodecmpset A) (synCcnv (synChncodecmpset A))) (.cv u)))
      p0187 p0188
  have p0190 :=
    @gMpbird
      (synWa (synWa (.classEq (.cv r) (synChncodecmpset A))
          (.classMem (.cv u) (synChwcn A))) (.classMem (.cv x) (synCfv (synC2nd) (.cv u))))
      (synWbr (synCec
          (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u)) (.cv x))
          (synChwniso A)) (synCdif (synClnqord (.cv r) (synChwcn A)) (synCid))
        (synCec (.cv u) (synChwniso A)))
      (synWbr (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u))
          (.cv x)) (synCdif (synChncodecmpset A) (synCcnv (synChncodecmpset A))) (.cv u))
      p0172 p0189
  have p0191 :=
    @gEliniseg (synCdif (synClnqord (.cv r) (synChwcn A)) (synCid))
      (synCec (.cv u) (synChwniso A))
      (synCec (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u))
          (.cv x)) (synChwniso A))
  have p0192 :=
    @gA1i
      (synWb (.classMem (synCec
            (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u)) (.cv x))
            (synChwniso A))
          (synCima (synCcnv (synCdif (synClnqord (.cv r) (synChwcn A)) (synCid)))
            (synCsn (synCec (.cv u) (synChwniso A))))) (synWbr (synCec
            (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u)) (.cv x))
            (synChwniso A)) (synCdif (synClnqord (.cv r) (synChwcn A)) (synCid))
          (synCec (.cv u) (synChwniso A))))
      (synWa (synWa (.classEq (.cv r) (synChncodecmpset A))
          (.classMem (.cv u) (synChwcn A))) (.classMem (.cv x) (synCfv (synC2nd) (.cv u))))
      p0191
  have p0193 :=
    @gMpbird
      (synWa (synWa (.classEq (.cv r) (synChncodecmpset A))
          (.classMem (.cv u) (synChwcn A))) (.classMem (.cv x) (synCfv (synC2nd) (.cv u))))
      (.classMem (synCec
          (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u)) (.cv x))
          (synChwniso A))
        (synCima (synCcnv (synCdif (synClnqord (.cv r) (synChwcn A)) (synCid)))
          (synCsn (synCec (.cv u) (synChwniso A)))))
      (synWbr (synCec
          (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u)) (.cv x))
          (synChwniso A)) (synCdif (synClnqord (.cv r) (synChwcn A)) (synCid))
        (synCec (.cv u) (synChwniso A)))
      p0190 p0192
  have p0194 :=
    @gJca
      (synWa (synWa (.classEq (.cv r) (synChncodecmpset A))
          (.classMem (.cv u) (synChwcn A))) (.classMem (.cv x) (synCfv (synC2nd) (.cv u))))
      (.classMem (synCec
          (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u)) (.cv x))
          (synChwniso A)) (synChnord A))
      (.classMem (synCec
          (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u)) (.cv x))
          (synChwniso A))
        (synCima (synCcnv (synCdif (synClnqord (.cv r) (synChwcn A)) (synCid)))
          (synCsn (synCec (.cv u) (synChwniso A)))))
      p0107 p0193
  have p0195 :=
    @gElin
      (synCec (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u))
          (.cv x)) (synChwniso A))
      (synChnord A)
      (synCima (synCcnv (synCdif (synClnqord (.cv r) (synChwcn A)) (synCid)))
        (synCsn (synCec (.cv u) (synChwniso A))))
  have p0196 :=
    @gA1i
      (synWb (.classMem (synCec
            (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u)) (.cv x))
            (synChwniso A)) (synCin (synChnord A)
            (synCima (synCcnv (synCdif (synClnqord (.cv r) (synChwcn A)) (synCid)))
              (synCsn (synCec (.cv u) (synChwniso A)))))) (synWa (.classMem (synCec
              (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u))
                (.cv x)) (synChwniso A)) (synChnord A)) (.classMem (synCec
              (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u))
                (.cv x)) (synChwniso A))
            (synCima (synCcnv (synCdif (synClnqord (.cv r) (synChwcn A)) (synCid)))
              (synCsn (synCec (.cv u) (synChwniso A)))))))
      (synWa (synWa (.classEq (.cv r) (synChncodecmpset A))
          (.classMem (.cv u) (synChwcn A))) (.classMem (.cv x) (synCfv (synC2nd) (.cv u))))
      p0195
  have p0197 :=
    @gMpbird
      (synWa (synWa (.classEq (.cv r) (synChncodecmpset A))
          (.classMem (.cv u) (synChwcn A))) (.classMem (.cv x) (synCfv (synC2nd) (.cv u))))
      (.classMem (synCec
          (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u)) (.cv x))
          (synChwniso A)) (synCin (synChnord A)
          (synCima (synCcnv (synCdif (synClnqord (.cv r) (synChwcn A)) (synCid)))
            (synCsn (synCec (.cv u) (synChwniso A))))))
      (synWa (.classMem (synCec
            (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u)) (.cv x))
            (synChwniso A)) (synChnord A)) (.classMem (synCec
            (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u)) (.cv x))
            (synChwniso A))
          (synCima (synCcnv (synCdif (synClnqord (.cv r) (synChwcn A)) (synCid)))
            (synCsn (synCec (.cv u) (synChwniso A))))))
      p0194 p0196
  have p0198 :=
    @gSyl
      (synWa (synWa (synWa (.classEq (.cv r) (synChncodecmpset A))
            (.classMem (.cv u) (synChwcn A))) (.classMem (.cv x) (synCfv (synC2nd) (.cv u))))
        (.classEq (synCec
            (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u)) (.cv x))
            (synChwniso A)) (.cv z)))
      (synWa (synWa (.classEq (.cv r) (synChncodecmpset A))
          (.classMem (.cv u) (synChwcn A))) (.classMem (.cv x) (synCfv (synC2nd) (.cv u))))
      (.classMem (synCec
          (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u)) (.cv x))
          (synChwniso A)) (synCin (synChnord A)
          (synCima (synCcnv (synCdif (synClnqord (.cv r) (synChwcn A)) (synCid)))
            (synCsn (synCec (.cv u) (synChwniso A))))))
      p0098 p0197
  have p0199 :=
    @gSimpr
      (synWa (synWa (.classEq (.cv r) (synChncodecmpset A))
          (.classMem (.cv u) (synChwcn A))) (.classMem (.cv x) (synCfv (synC2nd) (.cv u))))
      (.classEq (synCec
          (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u)) (.cv x))
          (synChwniso A)) (.cv z))
  have p0200 :=
    @gEleq1d
      (synWa (synWa (synWa (.classEq (.cv r) (synChncodecmpset A))
            (.classMem (.cv u) (synChwcn A))) (.classMem (.cv x) (synCfv (synC2nd) (.cv u))))
        (.classEq (synCec
            (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u)) (.cv x))
            (synChwniso A)) (.cv z)))
      (synCec (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u))
          (.cv x)) (synChwniso A))
      (.cv z)
      (synCin (synChnord A)
        (synCima (synCcnv (synCdif (synClnqord (.cv r) (synChwcn A)) (synCid)))
          (synCsn (synCec (.cv u) (synChwniso A)))))
      p0199
  have p0201 :=
    @gMpbid
      (synWa (synWa (synWa (.classEq (.cv r) (synChncodecmpset A))
            (.classMem (.cv u) (synChwcn A))) (.classMem (.cv x) (synCfv (synC2nd) (.cv u))))
        (.classEq (synCec
            (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u)) (.cv x))
            (synChwniso A)) (.cv z)))
      (.classMem (synCec
          (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u)) (.cv x))
          (synChwniso A)) (synCin (synChnord A)
          (synCima (synCcnv (synCdif (synClnqord (.cv r) (synChwcn A)) (synCid)))
            (synCsn (synCec (.cv u) (synChwniso A))))))
      (.classMem (.cv z) (synCin (synChnord A)
          (synCima (synCcnv (synCdif (synClnqord (.cv r) (synChwcn A)) (synCid)))
            (synCsn (synCec (.cv u) (synChwniso A))))))
      p0198 p0200
  have p0202 :=
    @gEx
      (synWa (synWa (.classEq (.cv r) (synChncodecmpset A))
          (.classMem (.cv u) (synChwcn A))) (.classMem (.cv x) (synCfv (synC2nd) (.cv u))))
      (.classEq (synCec
          (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u)) (.cv x))
          (synChwniso A)) (.cv z))
      (.classMem (.cv z) (synCin (synChnord A)
          (synCima (synCcnv (synCdif (synClnqord (.cv r) (synChwcn A)) (synCid)))
            (synCsn (synCec (.cv u) (synChwniso A))))))
      p0201
  have p0203 :=
    @gRexlimdva
      (synWa (.classEq (.cv r) (synChncodecmpset A)) (.classMem (.cv u) (synChwcn A)))
      (.classEq (synCec
          (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u)) (.cv x))
          (synChwniso A)) (.cv z))
      (.classMem (.cv z) (synCin (synChnord A)
          (synCima (synCcnv (synCdif (synClnqord (.cv r) (synChwcn A)) (synCid)))
            (synCsn (synCec (.cv u) (synChwniso A))))))
      x (synCfv (synC2nd) (.cv u)) dv_cache_0026 dv_cache_0027 p0202
  have p0204 :=
    @gImpbid
      (synWa (.classEq (.cv r) (synChncodecmpset A)) (.classMem (.cv u) (synChwcn A)))
      (.classMem (.cv z) (synCin (synChnord A)
          (synCima (synCcnv (synCdif (synClnqord (.cv r) (synChwcn A)) (synCid)))
            (synCsn (synCec (.cv u) (synChwniso A))))))
      (synWrex x (synCfv (synC2nd) (.cv u)) (.classEq (synCec
            (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u)) (.cv x))
            (synChwniso A)) (.cv z)))
      p0097 p0203
  have p0205 :=
    @gBitr4d
      (synWa (.classEq (.cv r) (synChncodecmpset A)) (.classMem (.cv u) (synChwcn A)))
      (.classMem (.cv z) (synCrn (synCcom (synChnqmap1 A) (synCsi
              (synChnwcutrel (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u)))))))
      (synWrex x (synCfv (synC2nd) (.cv u)) (.classEq (synCec
            (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u)) (.cv x))
            (synChwniso A)) (.cv z)))
      (.classMem (.cv z) (synCin (synChnord A)
          (synCima (synCcnv (synCdif (synClnqord (.cv r) (synChwcn A)) (synCid)))
            (synCsn (synCec (.cv u) (synChwniso A))))))
      p0002 p0204
  have p0206 :=
    @gEqrdv
      (synWa (.classEq (.cv r) (synChncodecmpset A)) (.classMem (.cv u) (synChwcn A)))
      z
      (synCrn (synCcom (synChnqmap1 A) (synCsi
            (synChnwcutrel (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u))))))
      (synCin (synChnord A)
        (synCima (synCcnv (synCdif (synClnqord (.cv r) (synChwcn A)) (synCid)))
          (synCsn (synCec (.cv u) (synChwniso A)))))
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

/-- Checked nominal proof certificate identified upstream as
`g_hnwcutambstrictsegresisomralias0ndv`.
-/
@[expose]
noncomputable def gHnwcutambstrictsegresisomralias0ndv (u : Var) (A : Class) (r : Var)
    (dv_A_r : r ∉ A.fv) (dv_A_u : u ∉ A.fv) (dv_r_u : r ≠ u)
    (hyp_hnwcutambstrictsegresisomralias0ndv_1 : Nominal.NPrf (.classMem A (synCvv))) :
    Nominal.NPrf
      (.imp (synWa (.classEq (.cv r) (synChncodecmpset A)) (.classMem (.cv u) (synChwcn A)))
        (synWiso (synCcom (synChnqmap1 A) (synCsi
              (synChnwcutrel (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u)))))
          (synCsi (synCsi (synCfv (synC1st) (.cv u))))
          (synCin (synClnqord (.cv r) (synChwcn A)) (synCxp (synCin (synChnord A)
                (synCima (synCcnv (synCdif (synClnqord (.cv r) (synChwcn A)) (synCid)))
                  (synCsn (synCec (.cv u) (synChwniso A))))) (synCin (synChnord A)
                (synCima (synCcnv (synCdif (synClnqord (.cv r) (synChwcn A)) (synCid)))
                  (synCsn (synCec (.cv u) (synChwniso A)))))))
          (synCpw1 (synCpw1 (synCfv (synC2nd) (.cv u)))) (synCin (synChnord A)
            (synCima (synCcnv (synCdif (synClnqord (.cv r) (synChwcn A)) (synCid)))
              (synCsn (synCec (.cv u) (synChwniso A))))))) :=
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
  have dv_cache_0011 : q ∉ ((synCpw1 (synCpw1 (synCfv (synC2nd) (.cv u))))).fv :=
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
      ((synWa (.classEq (.cv r) (synChncodecmpset A))
          (.classMem (.cv u) (synChwcn A)))).fv :=
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
      ((synWa (.classEq (.cv r) (synChncodecmpset A))
          (.classMem (.cv u) (synChwcn A)))).fv :=
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
  have dv_cache_0014 : p ∉ ((synCpw1 (synCpw1 (synCfv (synC2nd) (.cv u))))).fv :=
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
      ((synCin (synChnord A)
          (synCima (synCcnv (synCdif (synClnqord (.cv r) (synChwcn A)) (synCid)))
            (synCsn (synCec (.cv u) (synChwniso A)))))).fv :=
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
      ((synCin (synChnord A)
          (synCima (synCcnv (synCdif (synClnqord (.cv r) (synChwcn A)) (synCid)))
            (synCsn (synCec (.cv u) (synChwniso A)))))).fv :=
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
      ((synCcom (synChnqmap1 A) (synCsi (synChnwcutrel (synCfv (synC1st) (.cv u))
              (synCfv (synC2nd) (.cv u)))))).fv :=
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
      ((synCcom (synChnqmap1 A) (synCsi (synChnwcutrel (synCfv (synC1st) (.cv u))
              (synCfv (synC2nd) (.cv u)))))).fv :=
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
  have dv_cache_0019 : p ∉ ((synCsi (synCsi (synCfv (synC1st) (.cv u))))).fv :=
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
  have dv_cache_0020 : q ∉ ((synCsi (synCsi (synCfv (synC1st) (.cv u))))).fv :=
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
  have dv_cache_0021 : p ∉ ((synClnqord (.cv r) (synChwcn A))).fv :=
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
  have dv_cache_0022 : q ∉ ((synClnqord (.cv r) (synChwcn A))).fv :=
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
    @gSimpr (.classEq (.cv r) (synChncodecmpset A)) (.classMem (.cv u) (synChwcn A))
  have p0001 :=
    @gHnwcutambfactorf1impndv u A dv_cache_0001 hyp_hnwcutambstrictsegresisomralias0ndv_1
  have p0002 :=
    @gSyl
      (synWa (.classEq (.cv r) (synChncodecmpset A)) (.classMem (.cv u) (synChwcn A)))
      (.classMem (.cv u) (synChwcn A))
      (synWf1 (synCcom (synChnqmap1 A) (synCsi
            (synChnwcutrel (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u)))))
        (synCpw1 (synCpw1 (synCfv (synC2nd) (.cv u)))) (synChnord A))
      p0000 p0001
  have p0003 :=
    @gF1f1orn (synCpw1 (synCpw1 (synCfv (synC2nd) (.cv u)))) (synChnord A)
      (synCcom (synChnqmap1 A) (synCsi
          (synChnwcutrel (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u)))))
  have p0004 :=
    @gSyl
      (synWa (.classEq (.cv r) (synChncodecmpset A)) (.classMem (.cv u) (synChwcn A)))
      (synWf1 (synCcom (synChnqmap1 A) (synCsi
            (synChnwcutrel (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u)))))
        (synCpw1 (synCpw1 (synCfv (synC2nd) (.cv u)))) (synChnord A))
      (synWf1o (synCcom (synChnqmap1 A) (synCsi
            (synChnwcutrel (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u)))))
        (synCpw1 (synCpw1 (synCfv (synC2nd) (.cv u)))) (synCrn (synCcom (synChnqmap1 A)
            (synCsi (synChnwcutrel (synCfv (synC1st) (.cv u))
                (synCfv (synC2nd) (.cv u)))))))
      p0002 p0003
  have p0005 :=
    @gHnwcutambstrictsegranimpndv u A r dv_cache_0002 dv_cache_0001 dv_cache_0003
      hyp_hnwcutambstrictsegresisomralias0ndv_1
  have p0006 :=
    @gF1oeq3
      (synCrn (synCcom (synChnqmap1 A) (synCsi
            (synChnwcutrel (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u))))))
      (synCin (synChnord A)
        (synCima (synCcnv (synCdif (synClnqord (.cv r) (synChwcn A)) (synCid)))
          (synCsn (synCec (.cv u) (synChwniso A)))))
      (synCpw1 (synCpw1 (synCfv (synC2nd) (.cv u))))
      (synCcom (synChnqmap1 A) (synCsi
          (synChnwcutrel (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u)))))
  have p0007 :=
    @gSyl
      (synWa (.classEq (.cv r) (synChncodecmpset A)) (.classMem (.cv u) (synChwcn A)))
      (.classEq (synCrn (synCcom (synChnqmap1 A) (synCsi
              (synChnwcutrel (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u))))))
        (synCin (synChnord A)
          (synCima (synCcnv (synCdif (synClnqord (.cv r) (synChwcn A)) (synCid)))
            (synCsn (synCec (.cv u) (synChwniso A))))))
      (synWb (synWf1o (synCcom (synChnqmap1 A) (synCsi
              (synChnwcutrel (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u)))))
          (synCpw1 (synCpw1 (synCfv (synC2nd) (.cv u)))) (synCrn (synCcom (synChnqmap1 A)
              (synCsi (synChnwcutrel (synCfv (synC1st) (.cv u))
                  (synCfv (synC2nd) (.cv u))))))) (synWf1o (synCcom (synChnqmap1 A)
            (synCsi
              (synChnwcutrel (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u)))))
          (synCpw1 (synCpw1 (synCfv (synC2nd) (.cv u)))) (synCin (synChnord A)
            (synCima (synCcnv (synCdif (synClnqord (.cv r) (synChwcn A)) (synCid)))
              (synCsn (synCec (.cv u) (synChwniso A)))))))
      p0005 p0006
  have p0008 :=
    @gMpbid
      (synWa (.classEq (.cv r) (synChncodecmpset A)) (.classMem (.cv u) (synChwcn A)))
      (synWf1o (synCcom (synChnqmap1 A) (synCsi
            (synChnwcutrel (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u)))))
        (synCpw1 (synCpw1 (synCfv (synC2nd) (.cv u)))) (synCrn (synCcom (synChnqmap1 A)
            (synCsi (synChnwcutrel (synCfv (synC1st) (.cv u))
                (synCfv (synC2nd) (.cv u)))))))
      (synWf1o (synCcom (synChnqmap1 A) (synCsi
            (synChnwcutrel (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u)))))
        (synCpw1 (synCpw1 (synCfv (synC2nd) (.cv u)))) (synCin (synChnord A)
          (synCima (synCcnv (synCdif (synClnqord (.cv r) (synChwcn A)) (synCid)))
            (synCsn (synCec (.cv u) (synChwniso A))))))
      p0004 p0007
  have p0009 :=
    @gHnwcutambordbrproxyimpndv u A r q p dv_cache_0004 dv_cache_0005 dv_cache_0002
      dv_cache_0001 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010
      dv_cache_0003 hyp_hnwcutambstrictsegresisomralias0ndv_1
  have p0010 :=
    @gRalrimivva
      (synWa (.classEq (.cv r) (synChncodecmpset A)) (.classMem (.cv u) (synChwcn A)))
      (synWb (synWbr (.cv p) (synCsi (synCsi (synCfv (synC1st) (.cv u)))) (.cv q))
        (synWbr (synCfv (synCcom (synChnqmap1 A) (synCsi
                (synChnwcutrel (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u)))))
            (.cv p)) (synClnqord (.cv r) (synChwcn A)) (synCfv (synCcom (synChnqmap1 A)
              (synCsi (synChnwcutrel (synCfv (synC1st) (.cv u))
                  (synCfv (synC2nd) (.cv u))))) (.cv q))))
      p q (synCpw1 (synCpw1 (synCfv (synC2nd) (.cv u))))
      (synCpw1 (synCpw1 (synCfv (synC2nd) (.cv u)))) dv_cache_0011 dv_cache_0012
      dv_cache_0013 dv_cache_0006 p0009
  have p0011 :=
    @gJca
      (synWa (.classEq (.cv r) (synChncodecmpset A)) (.classMem (.cv u) (synChwcn A)))
      (synWf1o (synCcom (synChnqmap1 A) (synCsi
            (synChnwcutrel (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u)))))
        (synCpw1 (synCpw1 (synCfv (synC2nd) (.cv u)))) (synCin (synChnord A)
          (synCima (synCcnv (synCdif (synClnqord (.cv r) (synChwcn A)) (synCid)))
            (synCsn (synCec (.cv u) (synChwniso A))))))
      (synWral p (synCpw1 (synCpw1 (synCfv (synC2nd) (.cv u))))
        (synWral q (synCpw1 (synCpw1 (synCfv (synC2nd) (.cv u)))) (synWb
            (synWbr (.cv p) (synCsi (synCsi (synCfv (synC1st) (.cv u)))) (.cv q)) (synWbr
              (synCfv (synCcom (synChnqmap1 A) (synCsi
                    (synChnwcutrel (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u)))))
                (.cv p)) (synClnqord (.cv r) (synChwcn A)) (synCfv (synCcom (synChnqmap1 A)
                  (synCsi (synChnwcutrel (synCfv (synC1st) (.cv u))
                      (synCfv (synC2nd) (.cv u))))) (.cv q))))))
      p0008 p0010
  have p0012 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominalDfIso p q
      (synCpw1 (synCpw1 (synCfv (synC2nd) (.cv u))))
      (synCin (synChnord A)
        (synCima (synCcnv (synCdif (synClnqord (.cv r) (synChwcn A)) (synCid)))
          (synCsn (synCec (.cv u) (synChwniso A)))))
      (synCsi (synCsi (synCfv (synC1st) (.cv u)))) (synClnqord (.cv r) (synChwcn A))
      (synCcom (synChnqmap1 A) (synCsi
          (synChnwcutrel (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u)))))
      dv_cache_0014 dv_cache_0011 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018
      dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0006
  have p0013 :=
    @gBiimpri
      (synWiso (synCcom (synChnqmap1 A) (synCsi
            (synChnwcutrel (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u)))))
        (synCsi (synCsi (synCfv (synC1st) (.cv u)))) (synClnqord (.cv r) (synChwcn A))
        (synCpw1 (synCpw1 (synCfv (synC2nd) (.cv u)))) (synCin (synChnord A)
          (synCima (synCcnv (synCdif (synClnqord (.cv r) (synChwcn A)) (synCid)))
            (synCsn (synCec (.cv u) (synChwniso A))))))
      (synWa (synWf1o (synCcom (synChnqmap1 A) (synCsi
              (synChnwcutrel (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u)))))
          (synCpw1 (synCpw1 (synCfv (synC2nd) (.cv u)))) (synCin (synChnord A)
            (synCima (synCcnv (synCdif (synClnqord (.cv r) (synChwcn A)) (synCid)))
              (synCsn (synCec (.cv u) (synChwniso A))))))
        (synWral p (synCpw1 (synCpw1 (synCfv (synC2nd) (.cv u))))
          (synWral q (synCpw1 (synCpw1 (synCfv (synC2nd) (.cv u)))) (synWb
              (synWbr (.cv p) (synCsi (synCsi (synCfv (synC1st) (.cv u)))) (.cv q))
              (synWbr (synCfv (synCcom (synChnqmap1 A) (synCsi
                      (synChnwcutrel (synCfv (synC1st) (.cv u))
                        (synCfv (synC2nd) (.cv u))))) (.cv p))
                (synClnqord (.cv r) (synChwcn A)) (synCfv (synCcom (synChnqmap1 A) (synCsi
                      (synChnwcutrel (synCfv (synC1st) (.cv u))
                        (synCfv (synC2nd) (.cv u))))) (.cv q)))))))
      p0012
  have p0014 :=
    @gSyl
      (synWa (.classEq (.cv r) (synChncodecmpset A)) (.classMem (.cv u) (synChwcn A)))
      (synWa (synWf1o (synCcom (synChnqmap1 A) (synCsi
              (synChnwcutrel (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u)))))
          (synCpw1 (synCpw1 (synCfv (synC2nd) (.cv u)))) (synCin (synChnord A)
            (synCima (synCcnv (synCdif (synClnqord (.cv r) (synChwcn A)) (synCid)))
              (synCsn (synCec (.cv u) (synChwniso A))))))
        (synWral p (synCpw1 (synCpw1 (synCfv (synC2nd) (.cv u))))
          (synWral q (synCpw1 (synCpw1 (synCfv (synC2nd) (.cv u)))) (synWb
              (synWbr (.cv p) (synCsi (synCsi (synCfv (synC1st) (.cv u)))) (.cv q))
              (synWbr (synCfv (synCcom (synChnqmap1 A) (synCsi
                      (synChnwcutrel (synCfv (synC1st) (.cv u))
                        (synCfv (synC2nd) (.cv u))))) (.cv p))
                (synClnqord (.cv r) (synChwcn A)) (synCfv (synCcom (synChnqmap1 A) (synCsi
                      (synChnwcutrel (synCfv (synC1st) (.cv u))
                        (synCfv (synC2nd) (.cv u))))) (.cv q)))))))
      (synWiso (synCcom (synChnqmap1 A) (synCsi
            (synChnwcutrel (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u)))))
        (synCsi (synCsi (synCfv (synC1st) (.cv u)))) (synClnqord (.cv r) (synChwcn A))
        (synCpw1 (synCpw1 (synCfv (synC2nd) (.cv u)))) (synCin (synChnord A)
          (synCima (synCcnv (synCdif (synClnqord (.cv r) (synChwcn A)) (synCid)))
            (synCsn (synCec (.cv u) (synChwniso A))))))
      p0011 p0013
  have p0015 :=
    @gIsores2 (synCpw1 (synCpw1 (synCfv (synC2nd) (.cv u))))
      (synCin (synChnord A)
        (synCima (synCcnv (synCdif (synClnqord (.cv r) (synChwcn A)) (synCid)))
          (synCsn (synCec (.cv u) (synChwniso A)))))
      (synCsi (synCsi (synCfv (synC1st) (.cv u)))) (synClnqord (.cv r) (synChwcn A))
      (synCcom (synChnqmap1 A) (synCsi
          (synChnwcutrel (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u)))))
  have p0016 :=
    @gA1i
      (synWb (synWiso (synCcom (synChnqmap1 A) (synCsi
              (synChnwcutrel (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u)))))
          (synCsi (synCsi (synCfv (synC1st) (.cv u)))) (synClnqord (.cv r) (synChwcn A))
          (synCpw1 (synCpw1 (synCfv (synC2nd) (.cv u)))) (synCin (synChnord A)
            (synCima (synCcnv (synCdif (synClnqord (.cv r) (synChwcn A)) (synCid)))
              (synCsn (synCec (.cv u) (synChwniso A)))))) (synWiso
          (synCcom (synChnqmap1 A) (synCsi
              (synChnwcutrel (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u)))))
          (synCsi (synCsi (synCfv (synC1st) (.cv u))))
          (synCin (synClnqord (.cv r) (synChwcn A)) (synCxp (synCin (synChnord A)
                (synCima (synCcnv (synCdif (synClnqord (.cv r) (synChwcn A)) (synCid)))
                  (synCsn (synCec (.cv u) (synChwniso A))))) (synCin (synChnord A)
                (synCima (synCcnv (synCdif (synClnqord (.cv r) (synChwcn A)) (synCid)))
                  (synCsn (synCec (.cv u) (synChwniso A)))))))
          (synCpw1 (synCpw1 (synCfv (synC2nd) (.cv u)))) (synCin (synChnord A)
            (synCima (synCcnv (synCdif (synClnqord (.cv r) (synChwcn A)) (synCid)))
              (synCsn (synCec (.cv u) (synChwniso A)))))))
      (synWa (.classEq (.cv r) (synChncodecmpset A)) (.classMem (.cv u) (synChwcn A)))
      p0015
  have p0017 :=
    @gMpbid
      (synWa (.classEq (.cv r) (synChncodecmpset A)) (.classMem (.cv u) (synChwcn A)))
      (synWiso (synCcom (synChnqmap1 A) (synCsi
            (synChnwcutrel (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u)))))
        (synCsi (synCsi (synCfv (synC1st) (.cv u)))) (synClnqord (.cv r) (synChwcn A))
        (synCpw1 (synCpw1 (synCfv (synC2nd) (.cv u)))) (synCin (synChnord A)
          (synCima (synCcnv (synCdif (synClnqord (.cv r) (synChwcn A)) (synCid)))
            (synCsn (synCec (.cv u) (synChwniso A))))))
      (synWiso (synCcom (synChnqmap1 A) (synCsi
            (synChnwcutrel (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u)))))
        (synCsi (synCsi (synCfv (synC1st) (.cv u))))
        (synCin (synClnqord (.cv r) (synChwcn A)) (synCxp (synCin (synChnord A) (synCima
                (synCcnv (synCdif (synClnqord (.cv r) (synChwcn A)) (synCid)))
                (synCsn (synCec (.cv u) (synChwniso A))))) (synCin (synChnord A) (synCima
                (synCcnv (synCdif (synClnqord (.cv r) (synChwcn A)) (synCid)))
                (synCsn (synCec (.cv u) (synChwniso A)))))))
        (synCpw1 (synCpw1 (synCfv (synC2nd) (.cv u)))) (synCin (synChnord A)
          (synCima (synCcnv (synCdif (synClnqord (.cv r) (synChwcn A)) (synCid)))
            (synCsn (synCec (.cv u) (synChwniso A))))))
      p0014 p0016
  exact p0017

/-- Checked nominal proof certificate identified upstream as
`g_hnwcutambstrictsegresisomraliasdndv`.
-/
@[expose]
noncomputable def gHnwcutambstrictsegresisomraliasdndv (u : Var) (A : Class) (r : Var)
    (dv_A_r : r ∉ A.fv) (dv_A_u : u ∉ A.fv) (dv_r_u : r ≠ u)
    (hyp_hnwcutambstrictsegresisomraliasdndv_1 : Nominal.NPrf (.classMem A (synCvv))) :
    Nominal.NPrf
      (.imp (.classEq (.cv r) (synChncodecmpset A)) (.imp (.classMem (.cv u) (synChwcn A))
          (synWiso (synCcom (synChnqmap1 A) (synCsi
                (synChnwcutrel (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u)))))
            (synCsi (synCsi (synCfv (synC1st) (.cv u))))
            (synCin (synClnqord (.cv r) (synChwcn A)) (synCxp (synCin (synChnord A)
                  (synCima (synCcnv (synCdif (synClnqord (.cv r) (synChwcn A)) (synCid)))
                    (synCsn (synCec (.cv u) (synChwniso A))))) (synCin (synChnord A)
                  (synCima (synCcnv (synCdif (synClnqord (.cv r) (synChwcn A)) (synCid)))
                    (synCsn (synCec (.cv u) (synChwniso A)))))))
            (synCpw1 (synCpw1 (synCfv (synC2nd) (.cv u)))) (synCin (synChnord A) (synCima
                (synCcnv (synCdif (synClnqord (.cv r) (synChwcn A)) (synCid)))
                (synCsn (synCec (.cv u) (synChwniso A)))))))) :=
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
    @gHnwcutambstrictsegresisomralias0ndv u A r dv_cache_0001 dv_cache_0002 dv_cache_0003
      hyp_hnwcutambstrictsegresisomraliasdndv_1
  have p0001 :=
    @gEx (.classEq (.cv r) (synChncodecmpset A)) (.classMem (.cv u) (synChwcn A))
      (synWiso (synCcom (synChnqmap1 A) (synCsi
            (synChnwcutrel (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u)))))
        (synCsi (synCsi (synCfv (synC1st) (.cv u))))
        (synCin (synClnqord (.cv r) (synChwcn A)) (synCxp (synCin (synChnord A) (synCima
                (synCcnv (synCdif (synClnqord (.cv r) (synChwcn A)) (synCid)))
                (synCsn (synCec (.cv u) (synChwniso A))))) (synCin (synChnord A) (synCima
                (synCcnv (synCdif (synClnqord (.cv r) (synChwcn A)) (synCid)))
                (synCsn (synCec (.cv u) (synChwniso A)))))))
        (synCpw1 (synCpw1 (synCfv (synC2nd) (.cv u)))) (synCin (synChnord A)
          (synCima (synCcnv (synCdif (synClnqord (.cv r) (synChwcn A)) (synCid)))
            (synCsn (synCec (.cv u) (synChwniso A))))))
      p0000
  exact p0001


end NFChoice.DirectNominalPrf.WPPReplay

end
