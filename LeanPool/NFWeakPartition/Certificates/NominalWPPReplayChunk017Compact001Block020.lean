/-
Copyright (c) 2026 Elliot Glazer and NFNotWPP contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elliot Glazer and NFNotWPP contributors
-/

module

public import LeanPool.NFWeakPartition.NominalWPPReplayChunk017Compact001Part083

/-! Nominal proof certificates grouped in dependency order. -/


public section

/-! Certificates from `NominalWPPReplayChunk017Compact001Part084`. -/


section

namespace NFChoice.DirectNominalPrf.WPPReplay

open scoped Fol
open NFChoice.Foundation
open NFChoice.SemanticCore
open NFChoice.ReplaySupport
open NFChoice.Compiler.CompactSourceSyntax

@[expose]
noncomputable def g_hninjraisedselfcutcmpndv (x : Var) (u : Var) (A : Class) (f : Var)
    (dv_A_f : f ∉ A.fv) (dv_A_u : u ∉ A.fv) (dv_A_x : x ∉ A.fv) (dv_f_u : f ≠ u)
    (dv_f_x : f ≠ x) (dv_u_x : u ≠ x)
    (hyp_hninjraisedselfcutcmpndv_1 : Nominal.NPrf (.classMem A (syn_cvv))) :
    Nominal.NPrf
      (.imp (syn_wf1 (.cv f) (syn_chnord A) (syn_cpw1 (syn_cpw1 A)))
        (syn_wrex u (syn_chwcn (syn_cpw1 (syn_cpw1 A))) (syn_wrex x (syn_cfv (syn_c2nd) (.cv u))
            (syn_wbr (.cv u) (syn_chwniso (syn_cpw1 (syn_cpw1 A)))
              (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u))
                (.cv x)))))) :=
  by
  let proofSupport : Finset Var :=
    ({ x } : Finset Var) ∪ ({ u } : Finset Var) ∪ A.fv ∪ ({ f } : Finset Var)
  let r : Var := freshVar proofSupport 0
  let s : Var := freshVar proofSupport 1
  have fresh_r : r ∉ proofSupport :=
    by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_r_ne_x : r ≠ x := by
    intro h
    exact
      fresh_r
        (Finset.mem_union_left _ (Finset.mem_union_left _
            (Finset.mem_union_left _ (Finset.mem_singleton.mpr h))))
  have fresh_r_ne_u : r ≠ u := by
    intro h
    exact
      fresh_r
        (Finset.mem_union_left _ (Finset.mem_union_left _
            (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))))
  have fresh_r_not_A : r ∉ A.fv := by
    intro h
    exact fresh_r (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_r_ne_f : r ≠ f := by
    intro h
    exact fresh_r (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))
  have fresh_f_ne_r : f ≠ r := Ne.symm fresh_r_ne_f
  have fresh_s : s ∉ proofSupport :=
    by
    change freshVar proofSupport 1 ∉ proofSupport
    exact freshVar_not_mem proofSupport 1
  have fresh_s_ne_x : s ≠ x := by
    intro h
    exact
      fresh_s
        (Finset.mem_union_left _ (Finset.mem_union_left _
            (Finset.mem_union_left _ (Finset.mem_singleton.mpr h))))
  have fresh_s_ne_u : s ≠ u := by
    intro h
    exact
      fresh_s
        (Finset.mem_union_left _ (Finset.mem_union_left _
            (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))))
  have fresh_s_not_A : s ∉ A.fv := by
    intro h
    exact fresh_s (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_s_ne_f : s ≠ f := by
    intro h
    exact fresh_s (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))
  have fresh_f_ne_s : f ≠ s := Ne.symm fresh_s_ne_f
  have fresh_r_ne_s : r ≠ s :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have fresh_s_ne_r : s ≠ r := Ne.symm fresh_r_ne_s
  have dv_cache_0001 : r ∉ ((syn_chncodecmpset A)).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : r ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chncodecmpset,
          fresh_r_not_A, not_false_eq_true])
  have dv_cache_0002 : Disjoint ((syn_chwcn A)).fv ((Class.cv r)).fv :=
    by
    clear dv_cache_0001
    exact
      (show Disjoint ((syn_chwcn A)).fv ((Class.cv r)).fv from (by
          rw [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwcn,
            NFChoice.Compiler.CoreFVSimp.fv_class_cv];
          exact
            (show Disjoint ((A).fv) (({ r } : Finset Var)) from
              (Finset.disjoint_singleton_right.mpr
                (show r ∉ (A).fv from (by exact fresh_r_not_A))))))
  have dv_cache_0003 : s ∉ ((syn_clnqord (.cv r) (syn_chwcn A))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact
      (by
        have compact_fv_not_mem_empty : s ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_clnqord,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwcn, Finset.mem_union,
          Finset.mem_singleton, fresh_s_not_A, fresh_s_ne_r, or_false, not_false_eq_true])
  have dv_cache_0004 : f ∉ (A).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact
      (by
        have compact_fv_not_mem_empty : f ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_A_f, not_false_eq_true])
  have dv_cache_0005 : r ∉ (A).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact
      (by
        have compact_fv_not_mem_empty : r ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_r_not_A, not_false_eq_true])
  have dv_cache_0006 : s ∉ (A).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact
      (by
        have compact_fv_not_mem_empty : s ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_s_not_A, not_false_eq_true])
  have dv_cache_0007 : u ∉ (A).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006
    exact
      (by
        have compact_fv_not_mem_empty : u ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_A_u, not_false_eq_true])
  have dv_cache_0008 : x ∉ (A).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_A_x, not_false_eq_true])
  have dv_cache_0009 : f ≠ r :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008
    exact (show f ≠ r from (by exact fresh_f_ne_r))
  have dv_cache_0010 : f ≠ s :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009
    exact (show f ≠ s from (by exact fresh_f_ne_s))
  have dv_cache_0011 : f ≠ u :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010
    exact (show f ≠ u from (by exact dv_f_u))
  have dv_cache_0012 : f ≠ x :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
    exact (show f ≠ x from (by exact dv_f_x))
  have dv_cache_0013 : r ≠ s :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012
    exact (show r ≠ s from (by exact fresh_r_ne_s))
  have dv_cache_0014 : r ≠ u :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013
    exact (show r ≠ u from (by exact fresh_r_ne_u))
  have dv_cache_0015 : r ≠ x :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014
    exact (show r ≠ x from (by exact fresh_r_ne_x))
  have dv_cache_0016 : s ≠ u :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015
    exact (show s ≠ u from (by exact fresh_s_ne_u))
  have dv_cache_0017 : s ≠ x :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016
    exact (show s ≠ x from (by exact fresh_s_ne_x))
  have dv_cache_0018 : u ≠ x :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
    exact (show u ≠ x from (by exact dv_u_x))
  have dv_cache_0019 :
    s ∉
      ((syn_wrex u (syn_chwcn (syn_cpw1 (syn_cpw1 A))) (syn_wrex x (syn_cfv (syn_c2nd) (.cv u))
            (syn_wbr (.cv u) (syn_chwniso (syn_cpw1 (syn_cpw1 A)))
              (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u))
                (.cv x)))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018
    exact
      (by
        have compact_fv_not_mem_empty : s ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wrex,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwcn,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c2nd,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwniso,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chnwcutcode,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1st, Finset.mem_union,
          Finset.mem_erase, Finset.mem_singleton, fresh_s_not_A, fresh_s_ne_u,
          fresh_s_ne_x, compact_fv_not_mem_empty, or_false, and_false, not_false_eq_true])
  have dv_cache_0020 :
    s ∉
      ((syn_wa (syn_wf1 (.cv f) (syn_chnord A) (syn_cpw1 (syn_cpw1 A)))
          (.classEq (.cv r) (syn_chncodecmpset A)))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019
    exact
      (by
        have compact_fv_not_mem_empty : s ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wf1,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chnord,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chncodecmpset,
          Finset.mem_union, Finset.mem_singleton, fresh_s_not_A, fresh_s_ne_f,
          fresh_s_ne_r, or_false, not_false_eq_true])
  have dv_cache_0021 :
    r ∉
      ((syn_wrex u (syn_chwcn (syn_cpw1 (syn_cpw1 A))) (syn_wrex x (syn_cfv (syn_c2nd) (.cv u))
            (syn_wbr (.cv u) (syn_chwniso (syn_cpw1 (syn_cpw1 A)))
              (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u))
                (.cv x)))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020
    exact
      (by
        have compact_fv_not_mem_empty : r ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wrex,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwcn,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c2nd,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwniso,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chnwcutcode,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1st, Finset.mem_union,
          Finset.mem_erase, Finset.mem_singleton, fresh_r_not_A, fresh_r_ne_u,
          fresh_r_ne_x, compact_fv_not_mem_empty, or_false, and_false, not_false_eq_true])
  have dv_cache_0022 :
    r ∉ ((syn_wf1 (.cv f) (syn_chnord A) (syn_cpw1 (syn_cpw1 A)))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021
    exact
      (by
        have compact_fv_not_mem_empty : r ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wf1,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chnord,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1, Finset.mem_union,
          Finset.mem_singleton, fresh_r_not_A, fresh_r_ne_f, or_false, not_false_eq_true])
  have p0000 := @g_hncodecmpsetexg A
  have p0001 := Nominal.mp hyp_hninjraisedselfcutcmpndv_1 p0000
  have p0002 := @g_isset r (syn_chncodecmpset A) dv_cache_0001
  have p0003 :=
    @g_mpbi (.classMem (syn_chncodecmpset A) (syn_cvv))
      (syn_wex r (.classEq (.cv r) (syn_chncodecmpset A))) p0001 p0002
  have p0004 :=
    @g_a1i (syn_wex r (.classEq (.cv r) (syn_chncodecmpset A)))
      (syn_wf1 (.cv f) (syn_chnord A) (syn_cpw1 (syn_cpw1 A))) p0003
  have p0007 :=
    @g_a1i (.classMem (syn_chncodecmpset A) (syn_cvv))
      (syn_wa (syn_wf1 (.cv f) (syn_chnord A) (syn_cpw1 (syn_cpw1 A)))
        (.classEq (.cv r) (syn_chncodecmpset A)))
      p0001
  have p0008 :=
    @g_simpr (syn_wf1 (.cv f) (syn_chnord A) (syn_cpw1 (syn_cpw1 A)))
      (.classEq (.cv r) (syn_chncodecmpset A))
  have p0009 :=
    @g_eleq1d
      (syn_wa (syn_wf1 (.cv f) (syn_chnord A) (syn_cpw1 (syn_cpw1 A)))
        (.classEq (.cv r) (syn_chncodecmpset A)))
      (.cv r) (syn_chncodecmpset A) (syn_cvv) p0008
  have p0010 :=
    @g_mpbird
      (syn_wa (syn_wf1 (.cv f) (syn_chnord A) (syn_cpw1 (syn_cpw1 A)))
        (.classEq (.cv r) (syn_chncodecmpset A)))
      (.classMem (.cv r) (syn_cvv)) (.classMem (syn_chncodecmpset A) (syn_cvv)) p0007
      p0009
  have p0011 := @g_hwcnex A hyp_hninjraisedselfcutcmpndv_1
  have p0012 :=
    @g_a1i (.classMem (syn_chwcn A) (syn_cvv))
      (syn_wa (syn_wf1 (.cv f) (syn_chnord A) (syn_cpw1 (syn_cpw1 A)))
        (.classEq (.cv r) (syn_chncodecmpset A)))
      p0011
  have p0013 :=
    @g_jca
      (syn_wa (syn_wf1 (.cv f) (syn_chnord A) (syn_cpw1 (syn_cpw1 A)))
        (.classEq (.cv r) (syn_chncodecmpset A)))
      (.classMem (.cv r) (syn_cvv)) (.classMem (syn_chwcn A) (syn_cvv)) p0010 p0012
  have p0014 := @g_lnqordexg (syn_chwcn A) (.cv r) dv_cache_0002
  have p0015 :=
    @g_syl
      (syn_wa (syn_wf1 (.cv f) (syn_chnord A) (syn_cpw1 (syn_cpw1 A)))
        (.classEq (.cv r) (syn_chncodecmpset A)))
      (syn_wa (.classMem (.cv r) (syn_cvv)) (.classMem (syn_chwcn A) (syn_cvv)))
      (.classMem (syn_clnqord (.cv r) (syn_chwcn A)) (syn_cvv)) p0013 p0014
  have p0016 := @g_isset s (syn_clnqord (.cv r) (syn_chwcn A)) dv_cache_0003
  have p0017 :=
    @g_a1i
      (syn_wb (.classMem (syn_clnqord (.cv r) (syn_chwcn A)) (syn_cvv))
        (syn_wex s (.classEq (.cv s) (syn_clnqord (.cv r) (syn_chwcn A)))))
      (syn_wa (syn_wf1 (.cv f) (syn_chnord A) (syn_cpw1 (syn_cpw1 A)))
        (.classEq (.cv r) (syn_chncodecmpset A)))
      p0016
  have p0018 :=
    @g_mpbid
      (syn_wa (syn_wf1 (.cv f) (syn_chnord A) (syn_cpw1 (syn_cpw1 A)))
        (.classEq (.cv r) (syn_chncodecmpset A)))
      (.classMem (syn_clnqord (.cv r) (syn_chwcn A)) (syn_cvv))
      (syn_wex s (.classEq (.cv s) (syn_clnqord (.cv r) (syn_chwcn A)))) p0015 p0017
  have p0019 :=
    @g_hninjraisedselfcutalldndv x u A f s r dv_cache_0004 dv_cache_0005 dv_cache_0006
      dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012
      dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018
      hyp_hninjraisedselfcutcmpndv_1
  have p0020 :=
    @g_anassrs (syn_wf1 (.cv f) (syn_chnord A) (syn_cpw1 (syn_cpw1 A)))
      (.classEq (.cv r) (syn_chncodecmpset A))
      (.classEq (.cv s) (syn_clnqord (.cv r) (syn_chwcn A)))
      (syn_wrex u (syn_chwcn (syn_cpw1 (syn_cpw1 A))) (syn_wrex x (syn_cfv (syn_c2nd) (.cv u))
          (syn_wbr (.cv u) (syn_chwniso (syn_cpw1 (syn_cpw1 A)))
            (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u))
              (.cv x)))))
      p0019
  have p0021 :=
    @g_exlimddv
      (syn_wa (syn_wf1 (.cv f) (syn_chnord A) (syn_cpw1 (syn_cpw1 A)))
        (.classEq (.cv r) (syn_chncodecmpset A)))
      (.classEq (.cv s) (syn_clnqord (.cv r) (syn_chwcn A)))
      (syn_wrex u (syn_chwcn (syn_cpw1 (syn_cpw1 A))) (syn_wrex x (syn_cfv (syn_c2nd) (.cv u))
          (syn_wbr (.cv u) (syn_chwniso (syn_cpw1 (syn_cpw1 A)))
            (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u))
              (.cv x)))))
      s dv_cache_0019 dv_cache_0020 p0018 p0020
  have p0022 :=
    @g_exlimddv (syn_wf1 (.cv f) (syn_chnord A) (syn_cpw1 (syn_cpw1 A)))
      (.classEq (.cv r) (syn_chncodecmpset A))
      (syn_wrex u (syn_chwcn (syn_cpw1 (syn_cpw1 A))) (syn_wrex x (syn_cfv (syn_c2nd) (.cv u))
          (syn_wbr (.cv u) (syn_chwniso (syn_cpw1 (syn_cpw1 A)))
            (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u))
              (.cv x)))))
      r dv_cache_0021 dv_cache_0022 p0004 p0021
  exact p0022

@[expose]
noncomputable def g_hnselfcutnoex2ndv (x : Var) (u : Var) (A : Class) (dv_A_u : u ∉ A.fv)
    (dv_A_x : x ∉ A.fv) (dv_u_x : u ≠ x) :
    Nominal.NPrf
      (.neg (syn_wrex u (syn_chwcn A) (syn_wrex x (syn_cfv (syn_c2nd) (.cv u))
            (syn_wbr (.cv u) (syn_chwniso A)
              (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u))
                (.cv x)))))) :=
  by
  have dv_cache_0001 : u ∉ (A).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : u ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_A_u, not_false_eq_true])
  have dv_cache_0002 : x ∉ ((Wff.classMem (.cv u) (syn_chwcn A))).fv :=
    by
    clear dv_cache_0001
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
  have p0000 := @g_hnwcutcodeselfnoisondv x u A dv_cache_0001
  have p0001 :=
    @g_nrexdv (.classMem (.cv u) (syn_chwcn A))
      (syn_wbr (.cv u) (syn_chwniso A)
        (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv x)))
      x (syn_cfv (syn_c2nd) (.cv u)) dv_cache_0002 p0000
  have p0002 :=
    @g_nrex
      (syn_wrex x (syn_cfv (syn_c2nd) (.cv u)) (syn_wbr (.cv u) (syn_chwniso A)
          (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv x))))
      u (syn_chwcn A) p0001
  exact p0002

@[expose]
noncomputable def g_hncardtc2nodomndv (A : Class)
    (hyp_hncardtc2nodomndv_1 : Nominal.NPrf (.classMem A (syn_cvv))) :
    Nominal.NPrf
      (.neg (syn_wbr (syn_chncard A) (syn_clec) (syn_ctc (syn_ctc (syn_cnc A))))) :=
  by
  let proofSupport : Finset Var := A.fv
  let f : Var := freshVar proofSupport 0
  let u : Var := freshVar proofSupport 1
  let x : Var := freshVar proofSupport 2
  have fresh_f : f ∉ proofSupport :=
    by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_f_not_A : f ∉ A.fv := by
    intro h
    exact fresh_f (h)
  have fresh_u : u ∉ proofSupport :=
    by
    change freshVar proofSupport 1 ∉ proofSupport
    exact freshVar_not_mem proofSupport 1
  have fresh_u_not_A : u ∉ A.fv := by
    intro h
    exact fresh_u (h)
  have fresh_x : x ∉ proofSupport :=
    by
    change freshVar proofSupport 2 ∉ proofSupport
    exact freshVar_not_mem proofSupport 2
  have fresh_x_not_A : x ∉ A.fv := by
    intro h
    exact fresh_x (h)
  have fresh_f_ne_u : f ≠ u :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have fresh_f_ne_x : f ≠ x :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 2
    exact freshVar_injective proofSupport (i := 0) (j := 2) (by decide)
  have fresh_u_ne_x : u ≠ x :=
    by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 2
    exact freshVar_injective proofSupport (i := 1) (j := 2) (by decide)
  have dv_cache_0001 : u ∉ ((syn_cpw1 (syn_cpw1 A))).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : u ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1, fresh_u_not_A,
          not_false_eq_true])
  have dv_cache_0002 : x ∉ ((syn_cpw1 (syn_cpw1 A))).fv :=
    by
    clear dv_cache_0001
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1, fresh_x_not_A,
          not_false_eq_true])
  have dv_cache_0003 : u ≠ x :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact (show u ≠ x from (by exact fresh_u_ne_x))
  have dv_cache_0004 : f ∉ (A).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact
      (by
        have compact_fv_not_mem_empty : f ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_f_not_A, not_false_eq_true])
  have dv_cache_0005 : u ∉ (A).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact
      (by
        have compact_fv_not_mem_empty : u ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_u_not_A, not_false_eq_true])
  have dv_cache_0006 : x ∉ (A).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_x_not_A, not_false_eq_true])
  have dv_cache_0007 : f ≠ u :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006
    exact (show f ≠ u from (by exact fresh_f_ne_u))
  have dv_cache_0008 : f ≠ x :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007
    exact (show f ≠ x from (by exact fresh_f_ne_x))
  have dv_cache_0009 : f ∉ ((syn_chnord A)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008
    exact
      (by
        have compact_fv_not_mem_empty : f ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chnord,
          fresh_f_not_A, not_false_eq_true])
  have dv_cache_0010 : f ∉ ((syn_cpw1 (syn_cpw1 A))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009
    exact
      (by
        have compact_fv_not_mem_empty : f ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1, fresh_f_not_A,
          not_false_eq_true])
  have p0000 :=
    @g_hnselfcutnoex2ndv x u (syn_cpw1 (syn_cpw1 A)) dv_cache_0001 dv_cache_0002
      dv_cache_0003
  have p0001 :=
    @g_hninjraisedselfcutcmpndv x u A f dv_cache_0004 dv_cache_0005 dv_cache_0006
      dv_cache_0007 dv_cache_0008 dv_cache_0003 hyp_hncardtc2nodomndv_1
  have p0002 :=
    @g_con3i (syn_wf1 (.cv f) (syn_chnord A) (syn_cpw1 (syn_cpw1 A)))
      (syn_wrex u (syn_chwcn (syn_cpw1 (syn_cpw1 A))) (syn_wrex x (syn_cfv (syn_c2nd) (.cv u))
          (syn_wbr (.cv u) (syn_chwniso (syn_cpw1 (syn_cpw1 A)))
            (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u))
              (.cv x)))))
      p0001
  have p0003 := Nominal.mp p0000 p0002
  have p0004 := @g_nex (syn_wf1 (.cv f) (syn_chnord A) (syn_cpw1 (syn_cpw1 A))) f p0003
  have p0005 := @g_hnordex A hyp_hncardtc2nodomndv_1
  have p0006 := @g_pw1ex A hyp_hncardtc2nodomndv_1
  have p0007 := @g_pw1ex (syn_cpw1 A) p0006
  have p0008 :=
    @g_nclenc (syn_chnord A) (syn_cpw1 (syn_cpw1 A)) f dv_cache_0009 dv_cache_0010 p0005
      p0007
  have p0009 :=
    @g_notbii
      (syn_wbr (syn_cnc (syn_chnord A)) (syn_clec) (syn_cnc (syn_cpw1 (syn_cpw1 A))))
      (syn_wex f (syn_wf1 (.cv f) (syn_chnord A) (syn_cpw1 (syn_cpw1 A)))) p0008
  have p0010 :=
    @g_mpbir
      (.neg (syn_wbr (syn_cnc (syn_chnord A)) (syn_clec) (syn_cnc (syn_cpw1 (syn_cpw1 A)))))
      (.neg (syn_wex f (syn_wf1 (.cv f) (syn_chnord A) (syn_cpw1 (syn_cpw1 A))))) p0004
      p0009
  have p0011 := (Nominal.classEqRefl (syn_chncard A))
  have p0012 := @g_tc2nc A hyp_hncardtc2nodomndv_1
  have p0013 :=
    @g_breq12i (syn_chncard A) (syn_cnc (syn_chnord A)) (syn_ctc (syn_ctc (syn_cnc A)))
      (syn_cnc (syn_cpw1 (syn_cpw1 A))) (syn_clec) p0011 p0012
  have p0014 :=
    @g_notbii (syn_wbr (syn_chncard A) (syn_clec) (syn_ctc (syn_ctc (syn_cnc A))))
      (syn_wbr (syn_cnc (syn_chnord A)) (syn_clec) (syn_cnc (syn_cpw1 (syn_cpw1 A))))
      p0013
  have p0015 :=
    @g_mpbir (.neg (syn_wbr (syn_chncard A) (syn_clec) (syn_ctc (syn_ctc (syn_cnc A)))))
      (.neg (syn_wbr (syn_cnc (syn_chnord A)) (syn_clec) (syn_cnc (syn_cpw1 (syn_cpw1 A)))))
      p0010 p0014
  exact p0015

@[expose]
noncomputable def g_wppconcrete6representedmonondv (X : Class) (Y : Class)
    (hyp_wppconcrete6representedmonondv_1 : Nominal.NPrf (.classMem X (syn_cvv)))
    (hyp_wppconcrete6representedmonondv_2 : Nominal.NPrf (.classMem Y (syn_cvv))) :
    Nominal.NPrf
      (.imp (syn_wbr (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_cnc X)))))))
          (syn_clec) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_cnc Y))))))))
        (syn_wbr (syn_cfv (syn_cwppconcrete6fn)
            (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_cnc X)))))))) (syn_clec)
          (syn_cfv (syn_cwppconcrete6fn)
            (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_cnc Y)))))))))) :=
  by
  have p0000 := @g_ncelncsi X hyp_wppconcrete6representedmonondv_1
  have p0001 := @g_ncelncsi Y hyp_wppconcrete6representedmonondv_2
  have p0002 := @g_tc6lecan (syn_cnc X) (syn_cnc Y) p0000 p0001
  have p0003 :=
    @g_ncpw2le X Y hyp_wppconcrete6representedmonondv_1
      hyp_wppconcrete6representedmonondv_2
  have p0004 :=
    @g_syl
      (syn_wbr (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_cnc X)))))))
        (syn_clec) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_cnc Y))))))))
      (syn_wbr (syn_cnc X) (syn_clec) (syn_cnc Y))
      (syn_wbr (syn_cnc (syn_cpw (syn_cpw X))) (syn_clec) (syn_cnc (syn_cpw (syn_cpw Y))))
      p0002 p0003
  have p0005 := @g_pwex X hyp_wppconcrete6representedmonondv_1
  have p0006 := @g_pwex (syn_cpw X) p0005
  have p0007 := @g_pwex Y hyp_wppconcrete6representedmonondv_2
  have p0008 := @g_pwex (syn_cpw Y) p0007
  have p0009 :=
    @g_hnordcardnclecndv (syn_cpw (syn_cpw Y)) (syn_cpw (syn_cpw X)) p0006 p0008
  have p0010 :=
    @g_syl
      (syn_wbr (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_cnc X)))))))
        (syn_clec) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_cnc Y))))))))
      (syn_wbr (syn_cnc (syn_cpw (syn_cpw X))) (syn_clec) (syn_cnc (syn_cpw (syn_cpw Y))))
      (syn_wbr (syn_cnc (syn_chnord (syn_cpw (syn_cpw X)))) (syn_clec)
        (syn_cnc (syn_chnord (syn_cpw (syn_cpw Y)))))
      p0004 p0009
  have p0013 := @g_hnordex (syn_cpw (syn_cpw X)) p0006
  have p0016 := @g_hnordex (syn_cpw (syn_cpw Y)) p0008
  have p0017 :=
    @g_hncardnclecndv (syn_chnord (syn_cpw (syn_cpw Y)))
      (syn_chnord (syn_cpw (syn_cpw X))) p0013 p0016
  have p0018 :=
    @g_syl
      (syn_wbr (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_cnc X)))))))
        (syn_clec) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_cnc Y))))))))
      (syn_wbr (syn_cnc (syn_chnord (syn_cpw (syn_cpw X)))) (syn_clec)
        (syn_cnc (syn_chnord (syn_cpw (syn_cpw Y)))))
      (syn_wbr (syn_chncard (syn_chnord (syn_cpw (syn_cpw X)))) (syn_clec)
        (syn_chncard (syn_chnord (syn_cpw (syn_cpw Y)))))
      p0010 p0017
  have p0019 := @g_wppconcrete6fnvalndv X hyp_wppconcrete6representedmonondv_1
  have p0020 := @g_wppconcrete6fnvalndv Y hyp_wppconcrete6representedmonondv_2
  have p0021 :=
    @g_breq12i
      (syn_cfv (syn_cwppconcrete6fn)
        (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_cnc X))))))))
      (syn_chncard (syn_chnord (syn_cpw (syn_cpw X))))
      (syn_cfv (syn_cwppconcrete6fn)
        (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_cnc Y))))))))
      (syn_chncard (syn_chnord (syn_cpw (syn_cpw Y)))) (syn_clec) p0019 p0020
  have p0022 :=
    @g_biimpri
      (syn_wbr (syn_cfv (syn_cwppconcrete6fn)
          (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_cnc X)))))))) (syn_clec)
        (syn_cfv (syn_cwppconcrete6fn)
          (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_cnc Y)))))))))
      (syn_wbr (syn_chncard (syn_chnord (syn_cpw (syn_cpw X)))) (syn_clec)
        (syn_chncard (syn_chnord (syn_cpw (syn_cpw Y)))))
      p0021
  have p0023 :=
    @g_syl
      (syn_wbr (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_cnc X)))))))
        (syn_clec) (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_cnc Y))))))))
      (syn_wbr (syn_chncard (syn_chnord (syn_cpw (syn_cpw X)))) (syn_clec)
        (syn_chncard (syn_chnord (syn_cpw (syn_cpw Y)))))
      (syn_wbr (syn_cfv (syn_cwppconcrete6fn)
          (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_cnc X)))))))) (syn_clec)
        (syn_cfv (syn_cwppconcrete6fn)
          (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_cnc Y)))))))))
      p0018 p0022
  exact p0023

@[expose]
noncomputable def g_letc6ncrepdv (z : Var) (M : Class) (N : Class) (dv_M_z : z ∉ M.fv)
    (dv_N_z : z ∉ N.fv) :
    Nominal.NPrf
      (.imp (syn_w3a (.classMem M (syn_cncs)) (.classMem N (syn_cncs)) (syn_wbr M (syn_clec)
            (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc N)))))))) (syn_wex z
          (.classEq M (syn_ctc
              (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_cnc (.cv z))))))))))) :=
  by
  let proofSupport : Finset Var := ({ z } : Finset Var) ∪ M.fv ∪ N.fv
  let p : Var := freshVar proofSupport 0
  have fresh_p : p ∉ proofSupport :=
    by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_p_ne_z : p ≠ z := by
    intro h
    exact
      fresh_p
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_singleton.mpr h)))
  have fresh_z_ne_p : z ≠ p := Ne.symm fresh_p_ne_z
  have fresh_p_not_M : p ∉ M.fv := by
    intro h
    exact fresh_p (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_p_not_N : p ∉ N.fv := by
    intro h
    exact fresh_p (Finset.mem_union_right _ (h))
  have dv_cache_0001 : p ∉ (M).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : p ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_p_not_M, not_false_eq_true])
  have dv_cache_0002 : p ∉ (N).fv :=
    by
    clear dv_cache_0001
    exact
      (by
        have compact_fv_not_mem_empty : p ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_p_not_N, not_false_eq_true])
  have dv_cache_0003 : z ∉ ((Class.cv p)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact
      (by
        have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_z_ne_p, not_false_eq_true])
  have dv_cache_0004 :
    z ∉
      ((syn_wa (syn_wa (syn_w3a (.classMem M (syn_cncs)) (.classMem N (syn_cncs))
              (syn_wbr M (syn_clec)
                (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc N))))))))
            (.classMem (.cv p) (syn_cncs))) (.classEq M
            (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (.cv p)))))))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact
      (by
        have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_w3a,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cncs,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_clec,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ctc,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, Finset.mem_union,
          Finset.mem_singleton, dv_M_z, dv_N_z, fresh_z_ne_p, compact_fv_not_mem_empty,
          or_false, not_false_eq_true])
  have dv_cache_0005 :
    p ∉
      ((syn_wex z (.classEq M (syn_ctc (syn_ctc
                (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_cnc (.cv z))))))))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact
      (by
        have compact_fv_not_mem_empty : p ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wex,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ctc,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnc,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase,
          Finset.mem_singleton, fresh_p_not_M, fresh_p_ne_z, or_false, and_false,
          not_false_eq_true])
  have dv_cache_0006 :
    p ∉
      ((syn_w3a (.classMem M (syn_cncs)) (.classMem N (syn_cncs)) (syn_wbr M (syn_clec)
            (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc N))))))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact
      (by
        have compact_fv_not_mem_empty : p ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_w3a,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cncs,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_clec,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ctc, Finset.mem_union,
          fresh_p_not_M, fresh_p_not_N, compact_fv_not_mem_empty, or_false,
          not_false_eq_true])
  have p0000 := @g_letc6w6ndv M N p dv_cache_0001 dv_cache_0002
  have p0001 :=
    @g_simpl
      (syn_wa (syn_w3a (.classMem M (syn_cncs)) (.classMem N (syn_cncs)) (syn_wbr M (syn_clec)
            (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc N))))))))
        (.classMem (.cv p) (syn_cncs)))
      (.classEq M (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (.cv p))))))))
  have p0002 :=
    @g_simpr
      (syn_w3a (.classMem M (syn_cncs)) (.classMem N (syn_cncs)) (syn_wbr M (syn_clec)
          (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc N))))))))
      (.classMem (.cv p) (syn_cncs))
  have p0003 :=
    @g_syl
      (syn_wa (syn_wa (syn_w3a (.classMem M (syn_cncs)) (.classMem N (syn_cncs))
            (syn_wbr M (syn_clec)
              (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc N))))))))
          (.classMem (.cv p) (syn_cncs)))
        (.classEq M (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (.cv p)))))))))
      (syn_wa (syn_w3a (.classMem M (syn_cncs)) (.classMem N (syn_cncs)) (syn_wbr M (syn_clec)
            (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc N))))))))
        (.classMem (.cv p) (syn_cncs)))
      (.classMem (.cv p) (syn_cncs)) p0001 p0002
  have p0004 := @g_elncs z (.cv p) dv_cache_0003
  have p0005 :=
    @g_biimpi (.classMem (.cv p) (syn_cncs))
      (syn_wex z (.classEq (.cv p) (syn_cnc (.cv z)))) p0004
  have p0006 :=
    @g_syl
      (syn_wa (syn_wa (syn_w3a (.classMem M (syn_cncs)) (.classMem N (syn_cncs))
            (syn_wbr M (syn_clec)
              (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc N))))))))
          (.classMem (.cv p) (syn_cncs)))
        (.classEq M (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (.cv p)))))))))
      (.classMem (.cv p) (syn_cncs)) (syn_wex z (.classEq (.cv p) (syn_cnc (.cv z))))
      p0003 p0005
  have p0007 :=
    @g_simpl
      (syn_wa (syn_wa (syn_w3a (.classMem M (syn_cncs)) (.classMem N (syn_cncs))
            (syn_wbr M (syn_clec)
              (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc N))))))))
          (.classMem (.cv p) (syn_cncs)))
        (.classEq M (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (.cv p)))))))))
      (.classEq (.cv p) (syn_cnc (.cv z)))
  have p0008 :=
    @g_simpr
      (syn_wa (syn_w3a (.classMem M (syn_cncs)) (.classMem N (syn_cncs)) (syn_wbr M (syn_clec)
            (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc N))))))))
        (.classMem (.cv p) (syn_cncs)))
      (.classEq M (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (.cv p))))))))
  have p0009 :=
    @g_syl
      (syn_wa (syn_wa (syn_wa (syn_w3a (.classMem M (syn_cncs)) (.classMem N (syn_cncs))
              (syn_wbr M (syn_clec)
                (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc N))))))))
            (.classMem (.cv p) (syn_cncs))) (.classEq M
            (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (.cv p)))))))))
        (.classEq (.cv p) (syn_cnc (.cv z))))
      (syn_wa (syn_wa (syn_w3a (.classMem M (syn_cncs)) (.classMem N (syn_cncs))
            (syn_wbr M (syn_clec)
              (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc N))))))))
          (.classMem (.cv p) (syn_cncs)))
        (.classEq M (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (.cv p)))))))))
      (.classEq M (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (.cv p))))))))
      p0007 p0008
  have p0010 :=
    @g_simpr
      (syn_wa (syn_wa (syn_w3a (.classMem M (syn_cncs)) (.classMem N (syn_cncs))
            (syn_wbr M (syn_clec)
              (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc N))))))))
          (.classMem (.cv p) (syn_cncs)))
        (.classEq M (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (.cv p)))))))))
      (.classEq (.cv p) (syn_cnc (.cv z)))
  have p0011 := @g_tceq (.cv p) (syn_cnc (.cv z))
  have p0012 :=
    @g_syl
      (syn_wa (syn_wa (syn_wa (syn_w3a (.classMem M (syn_cncs)) (.classMem N (syn_cncs))
              (syn_wbr M (syn_clec)
                (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc N))))))))
            (.classMem (.cv p) (syn_cncs))) (.classEq M
            (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (.cv p)))))))))
        (.classEq (.cv p) (syn_cnc (.cv z))))
      (.classEq (.cv p) (syn_cnc (.cv z)))
      (.classEq (syn_ctc (.cv p)) (syn_ctc (syn_cnc (.cv z)))) p0010 p0011
  have p0013 := @g_tceq (syn_ctc (.cv p)) (syn_ctc (syn_cnc (.cv z)))
  have p0014 :=
    @g_syl
      (syn_wa (syn_wa (syn_wa (syn_w3a (.classMem M (syn_cncs)) (.classMem N (syn_cncs))
              (syn_wbr M (syn_clec)
                (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc N))))))))
            (.classMem (.cv p) (syn_cncs))) (.classEq M
            (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (.cv p)))))))))
        (.classEq (.cv p) (syn_cnc (.cv z))))
      (.classEq (syn_ctc (.cv p)) (syn_ctc (syn_cnc (.cv z))))
      (.classEq (syn_ctc (syn_ctc (.cv p))) (syn_ctc (syn_ctc (syn_cnc (.cv z))))) p0012
      p0013
  have p0015 := @g_tceq (syn_ctc (syn_ctc (.cv p))) (syn_ctc (syn_ctc (syn_cnc (.cv z))))
  have p0016 :=
    @g_syl
      (syn_wa (syn_wa (syn_wa (syn_w3a (.classMem M (syn_cncs)) (.classMem N (syn_cncs))
              (syn_wbr M (syn_clec)
                (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc N))))))))
            (.classMem (.cv p) (syn_cncs))) (.classEq M
            (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (.cv p)))))))))
        (.classEq (.cv p) (syn_cnc (.cv z))))
      (.classEq (syn_ctc (syn_ctc (.cv p))) (syn_ctc (syn_ctc (syn_cnc (.cv z)))))
      (.classEq (syn_ctc (syn_ctc (syn_ctc (.cv p))))
        (syn_ctc (syn_ctc (syn_ctc (syn_cnc (.cv z))))))
      p0014 p0015
  have p0017 :=
    @g_tceq (syn_ctc (syn_ctc (syn_ctc (.cv p))))
      (syn_ctc (syn_ctc (syn_ctc (syn_cnc (.cv z)))))
  have p0018 :=
    @g_syl
      (syn_wa (syn_wa (syn_wa (syn_w3a (.classMem M (syn_cncs)) (.classMem N (syn_cncs))
              (syn_wbr M (syn_clec)
                (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc N))))))))
            (.classMem (.cv p) (syn_cncs))) (.classEq M
            (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (.cv p)))))))))
        (.classEq (.cv p) (syn_cnc (.cv z))))
      (.classEq (syn_ctc (syn_ctc (syn_ctc (.cv p))))
        (syn_ctc (syn_ctc (syn_ctc (syn_cnc (.cv z))))))
      (.classEq (syn_ctc (syn_ctc (syn_ctc (syn_ctc (.cv p)))))
        (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_cnc (.cv z)))))))
      p0016 p0017
  have p0019 :=
    @g_tceq (syn_ctc (syn_ctc (syn_ctc (syn_ctc (.cv p)))))
      (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_cnc (.cv z))))))
  have p0020 :=
    @g_syl
      (syn_wa (syn_wa (syn_wa (syn_w3a (.classMem M (syn_cncs)) (.classMem N (syn_cncs))
              (syn_wbr M (syn_clec)
                (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc N))))))))
            (.classMem (.cv p) (syn_cncs))) (.classEq M
            (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (.cv p)))))))))
        (.classEq (.cv p) (syn_cnc (.cv z))))
      (.classEq (syn_ctc (syn_ctc (syn_ctc (syn_ctc (.cv p)))))
        (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_cnc (.cv z)))))))
      (.classEq (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (.cv p))))))
        (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_cnc (.cv z))))))))
      p0018 p0019
  have p0021 :=
    @g_tceq (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (.cv p))))))
      (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_cnc (.cv z)))))))
  have p0022 :=
    @g_syl
      (syn_wa (syn_wa (syn_wa (syn_w3a (.classMem M (syn_cncs)) (.classMem N (syn_cncs))
              (syn_wbr M (syn_clec)
                (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc N))))))))
            (.classMem (.cv p) (syn_cncs))) (.classEq M
            (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (.cv p)))))))))
        (.classEq (.cv p) (syn_cnc (.cv z))))
      (.classEq (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (.cv p))))))
        (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_cnc (.cv z))))))))
      (.classEq (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (.cv p)))))))
        (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_cnc (.cv z)))))))))
      p0020 p0021
  have p0023 :=
    @g_eqtrd
      (syn_wa (syn_wa (syn_wa (syn_w3a (.classMem M (syn_cncs)) (.classMem N (syn_cncs))
              (syn_wbr M (syn_clec)
                (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc N))))))))
            (.classMem (.cv p) (syn_cncs))) (.classEq M
            (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (.cv p)))))))))
        (.classEq (.cv p) (syn_cnc (.cv z))))
      M (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (.cv p)))))))
      (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_cnc (.cv z)))))))) p0009
      p0022
  have p0024 :=
    @g_ex
      (syn_wa (syn_wa (syn_w3a (.classMem M (syn_cncs)) (.classMem N (syn_cncs))
            (syn_wbr M (syn_clec)
              (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc N))))))))
          (.classMem (.cv p) (syn_cncs)))
        (.classEq M (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (.cv p)))))))))
      (.classEq (.cv p) (syn_cnc (.cv z)))
      (.classEq M (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_cnc (.cv z)))))))))
      p0023
  have p0025 :=
    @g_eximdv
      (syn_wa (syn_wa (syn_w3a (.classMem M (syn_cncs)) (.classMem N (syn_cncs))
            (syn_wbr M (syn_clec)
              (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc N))))))))
          (.classMem (.cv p) (syn_cncs)))
        (.classEq M (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (.cv p)))))))))
      (.classEq (.cv p) (syn_cnc (.cv z)))
      (.classEq M (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_cnc (.cv z)))))))))
      z dv_cache_0004 p0024
  have p0026 :=
    @g_mpd
      (syn_wa (syn_wa (syn_w3a (.classMem M (syn_cncs)) (.classMem N (syn_cncs))
            (syn_wbr M (syn_clec)
              (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc N))))))))
          (.classMem (.cv p) (syn_cncs)))
        (.classEq M (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (.cv p)))))))))
      (syn_wex z (.classEq (.cv p) (syn_cnc (.cv z))))
      (syn_wex z (.classEq M
          (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_cnc (.cv z))))))))))
      p0006 p0025
  have p0027 :=
    @g_ex
      (syn_wa (syn_w3a (.classMem M (syn_cncs)) (.classMem N (syn_cncs)) (syn_wbr M (syn_clec)
            (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc N))))))))
        (.classMem (.cv p) (syn_cncs)))
      (.classEq M (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (.cv p))))))))
      (syn_wex z (.classEq M
          (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_cnc (.cv z))))))))))
      p0026
  have p0028 :=
    @g_rexlimdva
      (syn_w3a (.classMem M (syn_cncs)) (.classMem N (syn_cncs)) (syn_wbr M (syn_clec)
          (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc N))))))))
      (.classEq M (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (.cv p))))))))
      (syn_wex z (.classEq M
          (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_cnc (.cv z))))))))))
      p (syn_cncs) dv_cache_0005 dv_cache_0006 p0027
  have p0029 :=
    @g_mpd
      (syn_w3a (.classMem M (syn_cncs)) (.classMem N (syn_cncs)) (syn_wbr M (syn_clec)
          (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc N))))))))
      (syn_wrex p (syn_cncs)
        (.classEq M (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (.cv p)))))))))
      (syn_wex z (.classEq M
          (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_cnc (.cv z))))))))))
      p0000 p0028
  exact p0029

@[expose]
noncomputable def g_wppconcrete6tcvalncndv :
    Nominal.NPrf
      (.classMem (syn_cfv (syn_cwppconcrete6fn) (syn_ctc (syn_ctc
              (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c))))))))))
        (syn_cncs)) :=
  by
  have p0000 := (Nominal.classEqRefl (syn_chncard (syn_c1c)))
  have p0001 := @g_tceq (syn_chncard (syn_c1c)) (syn_cnc (syn_chnord (syn_c1c)))
  have p0002 := Nominal.mp p0000 p0001
  have p0003 := @g_n_1cex
  have p0004 := @g_hnordex (syn_c1c) p0003
  have p0005 := @g_tcnc (syn_chnord (syn_c1c)) p0004
  have p0006 :=
    @g_eqtri (syn_ctc (syn_chncard (syn_c1c))) (syn_ctc (syn_cnc (syn_chnord (syn_c1c))))
      (syn_cnc (syn_cpw1 (syn_chnord (syn_c1c)))) p0002 p0005
  have p0007 :=
    @g_tceq (syn_ctc (syn_chncard (syn_c1c))) (syn_cnc (syn_cpw1 (syn_chnord (syn_c1c))))
  have p0008 := Nominal.mp p0006 p0007
  have p0009 :=
    @g_tceq (syn_ctc (syn_ctc (syn_chncard (syn_c1c))))
      (syn_ctc (syn_cnc (syn_cpw1 (syn_chnord (syn_c1c)))))
  have p0010 := Nominal.mp p0008 p0009
  have p0011 :=
    @g_tceq (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c)))))
      (syn_ctc (syn_ctc (syn_cnc (syn_cpw1 (syn_chnord (syn_c1c))))))
  have p0012 := Nominal.mp p0010 p0011
  have p0013 :=
    @g_tceq (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c))))))
      (syn_ctc (syn_ctc (syn_ctc (syn_cnc (syn_cpw1 (syn_chnord (syn_c1c)))))))
  have p0014 := Nominal.mp p0012 p0013
  have p0015 :=
    @g_tceq (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c)))))))
      (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_cnc (syn_cpw1 (syn_chnord (syn_c1c))))))))
  have p0016 := Nominal.mp p0014 p0015
  have p0017 :=
    @g_tceq
      (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c))))))))
      (syn_ctc (syn_ctc
          (syn_ctc (syn_ctc (syn_ctc (syn_cnc (syn_cpw1 (syn_chnord (syn_c1c)))))))))
  have p0018 := Nominal.mp p0016 p0017
  have p0019 :=
    @g_fveq2i
      (syn_ctc (syn_ctc
          (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c)))))))))
      (syn_ctc (syn_ctc (syn_ctc
            (syn_ctc (syn_ctc (syn_ctc (syn_cnc (syn_cpw1 (syn_chnord (syn_c1c))))))))))
      (syn_cwppconcrete6fn) p0018
  have p0022 := @g_pw1ex (syn_chnord (syn_c1c)) p0004
  have p0023 := @g_wppconcrete6fnvalndv (syn_cpw1 (syn_chnord (syn_c1c))) p0022
  have p0024 :=
    @g_eqtri
      (syn_cfv (syn_cwppconcrete6fn) (syn_ctc (syn_ctc
            (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c))))))))))
      (syn_cfv (syn_cwppconcrete6fn) (syn_ctc (syn_ctc (syn_ctc (syn_ctc
                (syn_ctc (syn_ctc (syn_cnc (syn_cpw1 (syn_chnord (syn_c1c)))))))))))
      (syn_chncard (syn_chnord (syn_cpw (syn_cpw (syn_cpw1 (syn_chnord (syn_c1c)))))))
      p0019 p0023
  have p0028 := @g_pwex (syn_cpw1 (syn_chnord (syn_c1c))) p0022
  have p0029 := @g_pwex (syn_cpw (syn_cpw1 (syn_chnord (syn_c1c)))) p0028
  have p0030 := @g_hnordex (syn_cpw (syn_cpw (syn_cpw1 (syn_chnord (syn_c1c))))) p0029
  have p0031 :=
    @g_hncardnc (syn_chnord (syn_cpw (syn_cpw (syn_cpw1 (syn_chnord (syn_c1c))))))
  have p0032 := Nominal.mp p0030 p0031
  have p0033 :=
    @g_eqeltri
      (syn_cfv (syn_cwppconcrete6fn) (syn_ctc (syn_ctc
            (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c))))))))))
      (syn_chncard (syn_chnord (syn_cpw (syn_cpw (syn_cpw1 (syn_chnord (syn_c1c)))))))
      (syn_cncs) p0024 p0032
  exact p0033


end NFChoice.DirectNominalPrf.WPPReplay

end

/-! Certificates from `NominalWPPReplayChunk017Compact001Part085`. -/


section

namespace NFChoice.DirectNominalPrf.WPPReplay

open scoped Fol
open NFChoice.Foundation
open NFChoice.SemanticCore
open NFChoice.ReplaySupport
open NFChoice.Compiler.CompactSourceSyntax

@[expose]
noncomputable def g_wppconcrete6tcbandgrowthfrompointhwclecdndv (y : Var)
    (hyp_wppconcrete6tcbandgrowthfrompointhwclecdndv_1 : Nominal.NPrf (.imp (syn_wwpp) (syn_wbr
            (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c))))))))
            (syn_clec) (syn_cfv (syn_cwppconcrete6fn) (syn_ctc (syn_ctc (syn_ctc (syn_ctc
                      (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c))))))))))))) :
    Nominal.NPrf
      (.imp (.classMem (.cv y) (syn_chwcards (syn_cvv))) (.imp (syn_wbr (.cv y) (syn_clec)
            (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c)))))))))
          (.imp (syn_wwpp) (.imp (syn_wbr (syn_ctc (syn_ctc (syn_ctc
                      (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c)))))))))
                (syn_clec) (.cv y)) (syn_wbr (syn_ctc (syn_ctc
                    (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c))))))))
                (syn_clec) (syn_cfv (syn_cwppconcrete6fn) (.cv y))))))) :=
  by
  let proofSupport : Finset Var := ({ y } : Finset Var)
  let z : Var := freshVar proofSupport 0
  have fresh_z : z ∉ proofSupport :=
    by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_z_ne_y : z ≠ y := by
    intro h
    exact fresh_z (Finset.mem_singleton.mpr h)
  have dv_cache_0001 : z ∉ ((Class.cv y)).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_z_ne_y, not_false_eq_true])
  have dv_cache_0002 : z ∉ ((syn_chncard (syn_c1c))).fv :=
    by
    clear dv_cache_0001
    exact
      (by
        have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chncard,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c, compact_fv_not_mem_empty,
          not_false_eq_true])
  have dv_cache_0003 :
    z ∉
      ((syn_wbr (syn_ctc (syn_ctc
              (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c)))))))))
          (syn_clec) (.cv y))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact
      (by
        have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ctc,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chncard,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_clec,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, fresh_z_ne_y, compact_fv_not_mem_empty, or_false,
          not_false_eq_true])
  have dv_cache_0004 :
    z ∉
      ((syn_wbr (syn_cfv (syn_cwppconcrete6fn) (syn_ctc (syn_ctc (syn_ctc
                  (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c))))))))))
          (syn_clec) (syn_cfv (syn_cwppconcrete6fn) (.cv y)))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact
      (by
        have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwppconcrete6fn,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ctc,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chncard,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_clec,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, fresh_z_ne_y, compact_fv_not_mem_empty, or_false,
          not_false_eq_true])
  have dv_cache_0005 :
    z ∉ ((Wff.classMem (syn_cfv (syn_cwppconcrete6fn) (.cv y)) (syn_cncs))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact
      (by
        have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwppconcrete6fn,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cncs, Finset.mem_union,
          Finset.mem_singleton, fresh_z_ne_y, compact_fv_not_mem_empty, or_false,
          not_false_eq_true])
  have p0000 :=
    @g_id
      (syn_wa (syn_wwpp) (syn_wbr (syn_ctc (syn_ctc
              (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c)))))))))
          (syn_clec) (.cv y)))
  have p0001 :=
    @g_a1i
      (.imp (syn_wa (syn_wwpp) (syn_wbr (syn_ctc (syn_ctc (syn_ctc
                  (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c)))))))))
            (syn_clec) (.cv y))) (syn_wa (syn_wwpp) (syn_wbr (syn_ctc (syn_ctc (syn_ctc
                  (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c)))))))))
            (syn_clec) (.cv y))))
      (syn_wbr (.cv y) (syn_clec) (syn_ctc
          (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c)))))))))
      p0000
  have p0002 :=
    @g_simpl (syn_wwpp)
      (syn_wbr (syn_ctc (syn_ctc
            (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c)))))))))
        (syn_clec) (.cv y))
  have p0003 :=
    @g_syl
      (syn_wa (syn_wwpp) (syn_wbr (syn_ctc (syn_ctc
              (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c)))))))))
          (syn_clec) (.cv y)))
      (syn_wwpp)
      (syn_wbr (syn_ctc
          (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c)))))))) (syn_clec)
        (syn_cfv (syn_cwppconcrete6fn) (syn_ctc (syn_ctc (syn_ctc
                (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c)))))))))))
      p0002 hyp_wppconcrete6tcbandgrowthfrompointhwclecdndv_1
  have p0004 :=
    @g_simpr (syn_wwpp)
      (syn_wbr (syn_ctc (syn_ctc
            (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c)))))))))
        (syn_clec) (.cv y))
  have p0005 :=
    @g_id
      (syn_wbr (.cv y) (syn_clec) (syn_ctc
          (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c)))))))))
  have p0006 := @g_hwcardssnc (syn_cvv)
  have p0007 := @g_sseli (syn_chwcards (syn_cvv)) (syn_cncs) (.cv y) p0006
  have p0008 := @g_id (.classMem (.cv y) (syn_chwcards (syn_cvv)))
  have p0009 :=
    @g_a1ii
      (.imp (.classMem (.cv y) (syn_chwcards (syn_cvv))) (.classMem (.cv y) (syn_cncs)))
      (.imp (.classMem (.cv y) (syn_chwcards (syn_cvv)))
        (.classMem (.cv y) (syn_chwcards (syn_cvv))))
      p0007 p0008
  have p0010 := @g_hncardnc1ndv
  have p0011 :=
    @g_jctir (.classMem (.cv y) (syn_chwcards (syn_cvv))) (.classMem (.cv y) (syn_cncs))
      (.classMem (syn_chncard (syn_c1c)) (syn_cncs)) p0009 p0010
  have p0012 :=
    @g_biantrurd (.classMem (.cv y) (syn_chwcards (syn_cvv)))
      (syn_wa (.classMem (.cv y) (syn_cncs)) (.classMem (syn_chncard (syn_c1c)) (syn_cncs)))
      (syn_wbr (.cv y) (syn_clec) (syn_ctc
          (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c)))))))))
      p0011
  have p0013 :=
    (Nominal.biimpRefl (syn_w3a (.classMem (.cv y) (syn_cncs))
        (.classMem (syn_chncard (syn_c1c)) (syn_cncs)) (syn_wbr (.cv y) (syn_clec) (syn_ctc
            (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c)))))))))))
  have p0014 :=
    @g_syl6rbbr (.classMem (.cv y) (syn_chwcards (syn_cvv)))
      (syn_wbr (.cv y) (syn_clec) (syn_ctc
          (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c)))))))))
      (syn_wa (syn_wa (.classMem (.cv y) (syn_cncs))
          (.classMem (syn_chncard (syn_c1c)) (syn_cncs))) (syn_wbr (.cv y) (syn_clec) (syn_ctc
            (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c))))))))))
      (syn_w3a (.classMem (.cv y) (syn_cncs)) (.classMem (syn_chncard (syn_c1c)) (syn_cncs))
        (syn_wbr (.cv y) (syn_clec) (syn_ctc
            (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c))))))))))
      p0012 p0013
  have p0015 :=
    @g_syl5ibr
      (syn_wbr (.cv y) (syn_clec) (syn_ctc
          (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c)))))))))
      (syn_w3a (.classMem (.cv y) (syn_cncs)) (.classMem (syn_chncard (syn_c1c)) (syn_cncs))
        (syn_wbr (.cv y) (syn_clec) (syn_ctc
            (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c))))))))))
      (.classMem (.cv y) (syn_chwcards (syn_cvv)))
      (syn_wbr (.cv y) (syn_clec) (syn_ctc
          (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c)))))))))
      p0005 p0014
  have p0016 :=
    @g_letc6ncrepdv z (.cv y) (syn_chncard (syn_c1c)) dv_cache_0001 dv_cache_0002
  have p0017 :=
    @g_syl6 (.classMem (.cv y) (syn_chwcards (syn_cvv)))
      (syn_wbr (.cv y) (syn_clec) (syn_ctc
          (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c)))))))))
      (syn_w3a (.classMem (.cv y) (syn_cncs)) (.classMem (syn_chncard (syn_c1c)) (syn_cncs))
        (syn_wbr (.cv y) (syn_clec) (syn_ctc
            (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c))))))))))
      (syn_wex z (.classEq (.cv y)
          (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_cnc (.cv z))))))))))
      p0015 p0016
  have p0018 :=
    @g_a1dd (.classMem (.cv y) (syn_chwcards (syn_cvv)))
      (syn_wbr (.cv y) (syn_clec) (syn_ctc
          (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c)))))))))
      (syn_wex z (.classEq (.cv y)
          (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_cnc (.cv z))))))))))
      (syn_wbr (syn_ctc (syn_ctc
            (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c)))))))))
        (syn_clec) (.cv y))
      p0017
  have p0019 :=
    @g_nfv
      (syn_wbr (syn_ctc (syn_ctc
            (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c)))))))))
        (syn_clec) (.cv y))
      z dv_cache_0003
  have p0020 :=
    @g_nfv
      (syn_wbr (syn_cfv (syn_cwppconcrete6fn) (syn_ctc (syn_ctc
              (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c))))))))))
        (syn_clec) (syn_cfv (syn_cwppconcrete6fn) (.cv y)))
      z dv_cache_0004
  have p0021 :=
    @g_simpl
      (syn_wbr (syn_ctc (syn_ctc
            (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c)))))))))
        (syn_clec) (.cv y))
      (.classEq (.cv y)
        (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_cnc (.cv z)))))))))
  have p0022 := (Nominal.classEqRefl (syn_chncard (syn_c1c)))
  have p0023 := @g_tceq (syn_chncard (syn_c1c)) (syn_cnc (syn_chnord (syn_c1c)))
  have p0024 := Nominal.mp p0022 p0023
  have p0025 := @g_n_1cex
  have p0026 := @g_hnordex (syn_c1c) p0025
  have p0027 := @g_tcnc (syn_chnord (syn_c1c)) p0026
  have p0028 :=
    @g_eqtri (syn_ctc (syn_chncard (syn_c1c))) (syn_ctc (syn_cnc (syn_chnord (syn_c1c))))
      (syn_cnc (syn_cpw1 (syn_chnord (syn_c1c)))) p0024 p0027
  have p0029 :=
    @g_tceq (syn_ctc (syn_chncard (syn_c1c))) (syn_cnc (syn_cpw1 (syn_chnord (syn_c1c))))
  have p0030 := Nominal.mp p0028 p0029
  have p0031 :=
    @g_tceq (syn_ctc (syn_ctc (syn_chncard (syn_c1c))))
      (syn_ctc (syn_cnc (syn_cpw1 (syn_chnord (syn_c1c)))))
  have p0032 := Nominal.mp p0030 p0031
  have p0033 :=
    @g_tceq (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c)))))
      (syn_ctc (syn_ctc (syn_cnc (syn_cpw1 (syn_chnord (syn_c1c))))))
  have p0034 := Nominal.mp p0032 p0033
  have p0035 :=
    @g_tceq (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c))))))
      (syn_ctc (syn_ctc (syn_ctc (syn_cnc (syn_cpw1 (syn_chnord (syn_c1c)))))))
  have p0036 := Nominal.mp p0034 p0035
  have p0037 :=
    @g_tceq (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c)))))))
      (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_cnc (syn_cpw1 (syn_chnord (syn_c1c))))))))
  have p0038 := Nominal.mp p0036 p0037
  have p0039 :=
    @g_tceq
      (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c))))))))
      (syn_ctc (syn_ctc
          (syn_ctc (syn_ctc (syn_ctc (syn_cnc (syn_cpw1 (syn_chnord (syn_c1c)))))))))
  have p0040 := Nominal.mp p0038 p0039
  have p0041 :=
    @g_a1i
      (.classEq (syn_ctc (syn_ctc
            (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c))))))))) (syn_ctc
          (syn_ctc (syn_ctc (syn_ctc
                (syn_ctc (syn_ctc (syn_cnc (syn_cpw1 (syn_chnord (syn_c1c)))))))))))
      (syn_wa (syn_wbr (syn_ctc (syn_ctc
              (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c)))))))))
          (syn_clec) (.cv y)) (.classEq (.cv y)
          (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_cnc (.cv z))))))))))
      p0040
  have p0042 :=
    @g_simpr
      (syn_wbr (syn_ctc (syn_ctc
            (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c)))))))))
        (syn_clec) (.cv y))
      (.classEq (.cv y)
        (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_cnc (.cv z)))))))))
  have p0043 :=
    @g_breq12d
      (syn_wa (syn_wbr (syn_ctc (syn_ctc
              (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c)))))))))
          (syn_clec) (.cv y)) (.classEq (.cv y)
          (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_cnc (.cv z))))))))))
      (syn_ctc (syn_ctc
          (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c)))))))))
      (syn_ctc (syn_ctc (syn_ctc
            (syn_ctc (syn_ctc (syn_ctc (syn_cnc (syn_cpw1 (syn_chnord (syn_c1c))))))))))
      (.cv y)
      (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_cnc (.cv z))))))))
      (syn_clec) p0041 p0042
  have p0044 :=
    @g_mpbid
      (syn_wa (syn_wbr (syn_ctc (syn_ctc
              (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c)))))))))
          (syn_clec) (.cv y)) (.classEq (.cv y)
          (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_cnc (.cv z))))))))))
      (syn_wbr (syn_ctc (syn_ctc
            (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c)))))))))
        (syn_clec) (.cv y))
      (syn_wbr (syn_ctc (syn_ctc (syn_ctc
              (syn_ctc (syn_ctc (syn_ctc (syn_cnc (syn_cpw1 (syn_chnord (syn_c1c))))))))))
        (syn_clec)
        (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_cnc (.cv z)))))))))
      p0021 p0043
  have p0047 := @g_pw1ex (syn_chnord (syn_c1c)) p0026
  have p0048 := @g_vex z
  have p0049 :=
    @g_wppconcrete6representedmonondv (syn_cpw1 (syn_chnord (syn_c1c))) (.cv z) p0047
      p0048
  have p0050 :=
    @g_syl
      (syn_wa (syn_wbr (syn_ctc (syn_ctc
              (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c)))))))))
          (syn_clec) (.cv y)) (.classEq (.cv y)
          (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_cnc (.cv z))))))))))
      (syn_wbr (syn_ctc (syn_ctc (syn_ctc
              (syn_ctc (syn_ctc (syn_ctc (syn_cnc (syn_cpw1 (syn_chnord (syn_c1c))))))))))
        (syn_clec)
        (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_cnc (.cv z)))))))))
      (syn_wbr (syn_cfv (syn_cwppconcrete6fn) (syn_ctc (syn_ctc (syn_ctc (syn_ctc
                  (syn_ctc (syn_ctc (syn_cnc (syn_cpw1 (syn_chnord (syn_c1c)))))))))))
        (syn_clec) (syn_cfv (syn_cwppconcrete6fn)
          (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_cnc (.cv z))))))))))
      p0044 p0049
  have p0070 :=
    @g_fveq2i
      (syn_ctc (syn_ctc
          (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c)))))))))
      (syn_ctc (syn_ctc (syn_ctc
            (syn_ctc (syn_ctc (syn_ctc (syn_cnc (syn_cpw1 (syn_chnord (syn_c1c))))))))))
      (syn_cwppconcrete6fn) p0040
  have p0071 :=
    @g_a1i
      (.classEq (syn_cfv (syn_cwppconcrete6fn) (syn_ctc (syn_ctc
              (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c))))))))))
        (syn_cfv (syn_cwppconcrete6fn) (syn_ctc (syn_ctc (syn_ctc (syn_ctc
                  (syn_ctc (syn_ctc (syn_cnc (syn_cpw1 (syn_chnord (syn_c1c))))))))))))
      (syn_wa (syn_wbr (syn_ctc (syn_ctc
              (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c)))))))))
          (syn_clec) (.cv y)) (.classEq (.cv y)
          (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_cnc (.cv z))))))))))
      p0070
  have p0073 :=
    @g_fveq2d
      (syn_wa (syn_wbr (syn_ctc (syn_ctc
              (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c)))))))))
          (syn_clec) (.cv y)) (.classEq (.cv y)
          (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_cnc (.cv z))))))))))
      (.cv y)
      (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_cnc (.cv z))))))))
      (syn_cwppconcrete6fn) p0042
  have p0074 :=
    @g_breq12d
      (syn_wa (syn_wbr (syn_ctc (syn_ctc
              (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c)))))))))
          (syn_clec) (.cv y)) (.classEq (.cv y)
          (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_cnc (.cv z))))))))))
      (syn_cfv (syn_cwppconcrete6fn) (syn_ctc (syn_ctc
            (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c))))))))))
      (syn_cfv (syn_cwppconcrete6fn) (syn_ctc (syn_ctc (syn_ctc (syn_ctc
                (syn_ctc (syn_ctc (syn_cnc (syn_cpw1 (syn_chnord (syn_c1c)))))))))))
      (syn_cfv (syn_cwppconcrete6fn) (.cv y))
      (syn_cfv (syn_cwppconcrete6fn)
        (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_cnc (.cv z)))))))))
      (syn_clec) p0071 p0073
  have p0075 :=
    @g_mpbird
      (syn_wa (syn_wbr (syn_ctc (syn_ctc
              (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c)))))))))
          (syn_clec) (.cv y)) (.classEq (.cv y)
          (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_cnc (.cv z))))))))))
      (syn_wbr (syn_cfv (syn_cwppconcrete6fn) (syn_ctc (syn_ctc
              (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c))))))))))
        (syn_clec) (syn_cfv (syn_cwppconcrete6fn) (.cv y)))
      (syn_wbr (syn_cfv (syn_cwppconcrete6fn) (syn_ctc (syn_ctc (syn_ctc (syn_ctc
                  (syn_ctc (syn_ctc (syn_cnc (syn_cpw1 (syn_chnord (syn_c1c)))))))))))
        (syn_clec) (syn_cfv (syn_cwppconcrete6fn)
          (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_cnc (.cv z))))))))))
      p0050 p0074
  have p0076 :=
    @g_ex
      (syn_wbr (syn_ctc (syn_ctc
            (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c)))))))))
        (syn_clec) (.cv y))
      (.classEq (.cv y)
        (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_cnc (.cv z)))))))))
      (syn_wbr (syn_cfv (syn_cwppconcrete6fn) (syn_ctc (syn_ctc
              (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c))))))))))
        (syn_clec) (syn_cfv (syn_cwppconcrete6fn) (.cv y)))
      p0075
  have p0077 :=
    @g_exlimd
      (syn_wbr (syn_ctc (syn_ctc
            (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c)))))))))
        (syn_clec) (.cv y))
      (.classEq (.cv y)
        (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_cnc (.cv z)))))))))
      (syn_wbr (syn_cfv (syn_cwppconcrete6fn) (syn_ctc (syn_ctc
              (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c))))))))))
        (syn_clec) (syn_cfv (syn_cwppconcrete6fn) (.cv y)))
      z p0019 p0020 p0076
  have p0078 :=
    @g_a2i
      (syn_wbr (syn_ctc (syn_ctc
            (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c)))))))))
        (syn_clec) (.cv y))
      (syn_wex z (.classEq (.cv y)
          (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_cnc (.cv z))))))))))
      (syn_wbr (syn_cfv (syn_cwppconcrete6fn) (syn_ctc (syn_ctc
              (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c))))))))))
        (syn_clec) (syn_cfv (syn_cwppconcrete6fn) (.cv y)))
      p0077
  have p0079 :=
    @g_syl6 (.classMem (.cv y) (syn_chwcards (syn_cvv)))
      (syn_wbr (.cv y) (syn_clec) (syn_ctc
          (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c)))))))))
      (.imp (syn_wbr (syn_ctc (syn_ctc
              (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c)))))))))
          (syn_clec) (.cv y)) (syn_wex z (.classEq (.cv y) (syn_ctc
              (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_cnc (.cv z)))))))))))
      (.imp (syn_wbr (syn_ctc (syn_ctc
              (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c)))))))))
          (syn_clec) (.cv y)) (syn_wbr (syn_cfv (syn_cwppconcrete6fn) (syn_ctc (syn_ctc (syn_ctc
                  (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c))))))))))
          (syn_clec) (syn_cfv (syn_cwppconcrete6fn) (.cv y))))
      p0018 p0078
  have p0080 :=
    @g_syl7
      (syn_wa (syn_wwpp) (syn_wbr (syn_ctc (syn_ctc
              (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c)))))))))
          (syn_clec) (.cv y)))
      (syn_wbr (syn_ctc (syn_ctc
            (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c)))))))))
        (syn_clec) (.cv y))
      (.classMem (.cv y) (syn_chwcards (syn_cvv)))
      (syn_wbr (.cv y) (syn_clec) (syn_ctc
          (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c)))))))))
      (syn_wbr (syn_cfv (syn_cwppconcrete6fn) (syn_ctc (syn_ctc
              (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c))))))))))
        (syn_clec) (syn_cfv (syn_cwppconcrete6fn) (.cv y)))
      p0004 p0079
  have p0081 :=
    @g_a1dd (.classMem (.cv y) (syn_chwcards (syn_cvv)))
      (syn_wbr (.cv y) (syn_clec) (syn_ctc
          (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c)))))))))
      (.imp (syn_wa (syn_wwpp) (syn_wbr (syn_ctc (syn_ctc (syn_ctc
                  (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c)))))))))
            (syn_clec) (.cv y))) (syn_wbr (syn_cfv (syn_cwppconcrete6fn) (syn_ctc (syn_ctc
                (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c))))))))))
          (syn_clec) (syn_cfv (syn_cwppconcrete6fn) (.cv y))))
      (syn_wbr (syn_ctc
          (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c)))))))) (syn_clec)
        (syn_cfv (syn_cwppconcrete6fn) (syn_ctc (syn_ctc (syn_ctc
                (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c)))))))))))
      p0080
  have p0082 :=
    @g_pm3_2
      (syn_wbr (syn_ctc
          (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c)))))))) (syn_clec)
        (syn_cfv (syn_cwppconcrete6fn) (syn_ctc (syn_ctc (syn_ctc
                (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c)))))))))))
      (syn_wbr (syn_cfv (syn_cwppconcrete6fn) (syn_ctc (syn_ctc
              (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c))))))))))
        (syn_clec) (syn_cfv (syn_cwppconcrete6fn) (.cv y)))
  have p0083 :=
    @g_a1i
      (.imp (syn_wbr (syn_ctc
            (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c))))))))
          (syn_clec) (syn_cfv (syn_cwppconcrete6fn) (syn_ctc (syn_ctc (syn_ctc
                  (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c))))))))))) (.imp
          (syn_wbr (syn_cfv (syn_cwppconcrete6fn) (syn_ctc (syn_ctc (syn_ctc
                    (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c))))))))))
            (syn_clec) (syn_cfv (syn_cwppconcrete6fn) (.cv y))) (syn_wa (syn_wbr (syn_ctc
                (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c))))))))
              (syn_clec) (syn_cfv (syn_cwppconcrete6fn) (syn_ctc (syn_ctc (syn_ctc
                      (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c)))))))))))
            (syn_wbr (syn_cfv (syn_cwppconcrete6fn) (syn_ctc (syn_ctc (syn_ctc
                      (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c))))))))))
              (syn_clec) (syn_cfv (syn_cwppconcrete6fn) (.cv y))))))
      (syn_wbr (.cv y) (syn_clec) (syn_ctc
          (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c)))))))))
      p0082
  have p0084 :=
    @g_imim2
      (syn_wbr (syn_cfv (syn_cwppconcrete6fn) (syn_ctc (syn_ctc
              (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c))))))))))
        (syn_clec) (syn_cfv (syn_cwppconcrete6fn) (.cv y)))
      (syn_wa (syn_wbr (syn_ctc
            (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c))))))))
          (syn_clec) (syn_cfv (syn_cwppconcrete6fn) (syn_ctc (syn_ctc (syn_ctc
                  (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c))))))))))) (syn_wbr
          (syn_cfv (syn_cwppconcrete6fn) (syn_ctc (syn_ctc (syn_ctc
                  (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c))))))))))
          (syn_clec) (syn_cfv (syn_cwppconcrete6fn) (.cv y))))
      (syn_wa (syn_wwpp) (syn_wbr (syn_ctc (syn_ctc
              (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c)))))))))
          (syn_clec) (.cv y)))
  have p0085 :=
    @g_syl6
      (syn_wbr (.cv y) (syn_clec) (syn_ctc
          (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c)))))))))
      (syn_wbr (syn_ctc
          (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c)))))))) (syn_clec)
        (syn_cfv (syn_cwppconcrete6fn) (syn_ctc (syn_ctc (syn_ctc
                (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c)))))))))))
      (.imp (syn_wbr (syn_cfv (syn_cwppconcrete6fn) (syn_ctc (syn_ctc (syn_ctc
                  (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c))))))))))
          (syn_clec) (syn_cfv (syn_cwppconcrete6fn) (.cv y))) (syn_wa (syn_wbr (syn_ctc
              (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c))))))))
            (syn_clec) (syn_cfv (syn_cwppconcrete6fn) (syn_ctc (syn_ctc (syn_ctc
                    (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c)))))))))))
          (syn_wbr (syn_cfv (syn_cwppconcrete6fn) (syn_ctc (syn_ctc (syn_ctc
                    (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c))))))))))
            (syn_clec) (syn_cfv (syn_cwppconcrete6fn) (.cv y)))))
      (.imp (.imp (syn_wa (syn_wwpp) (syn_wbr (syn_ctc (syn_ctc (syn_ctc
                    (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c)))))))))
              (syn_clec) (.cv y))) (syn_wbr (syn_cfv (syn_cwppconcrete6fn) (syn_ctc (syn_ctc
                  (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c))))))))))
            (syn_clec) (syn_cfv (syn_cwppconcrete6fn) (.cv y)))) (.imp (syn_wa (syn_wwpp)
            (syn_wbr (syn_ctc (syn_ctc (syn_ctc
                    (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c)))))))))
              (syn_clec) (.cv y))) (syn_wa (syn_wbr (syn_ctc
                (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c))))))))
              (syn_clec) (syn_cfv (syn_cwppconcrete6fn) (syn_ctc (syn_ctc (syn_ctc
                      (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c)))))))))))
            (syn_wbr (syn_cfv (syn_cwppconcrete6fn) (syn_ctc (syn_ctc (syn_ctc
                      (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c))))))))))
              (syn_clec) (syn_cfv (syn_cwppconcrete6fn) (.cv y))))))
      p0083 p0084
  have p0086 :=
    @g_a2d
      (syn_wbr (.cv y) (syn_clec) (syn_ctc
          (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c)))))))))
      (syn_wbr (syn_ctc
          (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c)))))))) (syn_clec)
        (syn_cfv (syn_cwppconcrete6fn) (syn_ctc (syn_ctc (syn_ctc
                (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c)))))))))))
      (.imp (syn_wa (syn_wwpp) (syn_wbr (syn_ctc (syn_ctc (syn_ctc
                  (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c)))))))))
            (syn_clec) (.cv y))) (syn_wbr (syn_cfv (syn_cwppconcrete6fn) (syn_ctc (syn_ctc
                (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c))))))))))
          (syn_clec) (syn_cfv (syn_cwppconcrete6fn) (.cv y))))
      (.imp (syn_wa (syn_wwpp) (syn_wbr (syn_ctc (syn_ctc (syn_ctc
                  (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c)))))))))
            (syn_clec) (.cv y))) (syn_wa (syn_wbr (syn_ctc
              (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c))))))))
            (syn_clec) (syn_cfv (syn_cwppconcrete6fn) (syn_ctc (syn_ctc (syn_ctc
                    (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c)))))))))))
          (syn_wbr (syn_cfv (syn_cwppconcrete6fn) (syn_ctc (syn_ctc (syn_ctc
                    (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c))))))))))
            (syn_clec) (syn_cfv (syn_cwppconcrete6fn) (.cv y)))))
      p0085
  have p0087 :=
    @g_sylcom (.classMem (.cv y) (syn_chwcards (syn_cvv)))
      (syn_wbr (.cv y) (syn_clec) (syn_ctc
          (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c)))))))))
      (.imp (syn_wbr (syn_ctc
            (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c))))))))
          (syn_clec) (syn_cfv (syn_cwppconcrete6fn) (syn_ctc (syn_ctc (syn_ctc
                  (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c))))))))))) (.imp
          (syn_wa (syn_wwpp) (syn_wbr (syn_ctc (syn_ctc (syn_ctc
                    (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c)))))))))
              (syn_clec) (.cv y))) (syn_wbr (syn_cfv (syn_cwppconcrete6fn) (syn_ctc (syn_ctc
                  (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c))))))))))
            (syn_clec) (syn_cfv (syn_cwppconcrete6fn) (.cv y)))))
      (.imp (syn_wbr (syn_ctc
            (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c))))))))
          (syn_clec) (syn_cfv (syn_cwppconcrete6fn) (syn_ctc (syn_ctc (syn_ctc
                  (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c))))))))))) (.imp
          (syn_wa (syn_wwpp) (syn_wbr (syn_ctc (syn_ctc (syn_ctc
                    (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c)))))))))
              (syn_clec) (.cv y))) (syn_wa (syn_wbr (syn_ctc
                (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c))))))))
              (syn_clec) (syn_cfv (syn_cwppconcrete6fn) (syn_ctc (syn_ctc (syn_ctc
                      (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c)))))))))))
            (syn_wbr (syn_cfv (syn_cwppconcrete6fn) (syn_ctc (syn_ctc (syn_ctc
                      (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c))))))))))
              (syn_clec) (syn_cfv (syn_cwppconcrete6fn) (.cv y))))))
      p0081 p0086
  have p0088 :=
    @g_syl7
      (syn_wa (syn_wwpp) (syn_wbr (syn_ctc (syn_ctc
              (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c)))))))))
          (syn_clec) (.cv y)))
      (syn_wbr (syn_ctc
          (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c)))))))) (syn_clec)
        (syn_cfv (syn_cwppconcrete6fn) (syn_ctc (syn_ctc (syn_ctc
                (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c)))))))))))
      (.classMem (.cv y) (syn_chwcards (syn_cvv)))
      (syn_wbr (.cv y) (syn_clec) (syn_ctc
          (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c)))))))))
      (.imp (syn_wa (syn_wwpp) (syn_wbr (syn_ctc (syn_ctc (syn_ctc
                  (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c)))))))))
            (syn_clec) (.cv y))) (syn_wa (syn_wbr (syn_ctc
              (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c))))))))
            (syn_clec) (syn_cfv (syn_cwppconcrete6fn) (syn_ctc (syn_ctc (syn_ctc
                    (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c)))))))))))
          (syn_wbr (syn_cfv (syn_cwppconcrete6fn) (syn_ctc (syn_ctc (syn_ctc
                    (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c))))))))))
            (syn_clec) (syn_cfv (syn_cwppconcrete6fn) (.cv y)))))
      p0003 p0087
  have p0089 :=
    Nominal.ax2
      (syn_wa (syn_wwpp) (syn_wbr (syn_ctc (syn_ctc
              (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c)))))))))
          (syn_clec) (.cv y)))
      (syn_wa (syn_wwpp) (syn_wbr (syn_ctc (syn_ctc
              (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c)))))))))
          (syn_clec) (.cv y)))
      (syn_wa (syn_wbr (syn_ctc
            (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c))))))))
          (syn_clec) (syn_cfv (syn_cwppconcrete6fn) (syn_ctc (syn_ctc (syn_ctc
                  (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c))))))))))) (syn_wbr
          (syn_cfv (syn_cwppconcrete6fn) (syn_ctc (syn_ctc (syn_ctc
                  (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c))))))))))
          (syn_clec) (syn_cfv (syn_cwppconcrete6fn) (.cv y))))
  have p0090 :=
    @g_syl6 (.classMem (.cv y) (syn_chwcards (syn_cvv)))
      (syn_wbr (.cv y) (syn_clec) (syn_ctc
          (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c)))))))))
      (.imp (syn_wa (syn_wwpp) (syn_wbr (syn_ctc (syn_ctc (syn_ctc
                  (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c)))))))))
            (syn_clec) (.cv y))) (.imp (syn_wa (syn_wwpp) (syn_wbr (syn_ctc (syn_ctc (syn_ctc
                    (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c)))))))))
              (syn_clec) (.cv y))) (syn_wa (syn_wbr (syn_ctc
                (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c))))))))
              (syn_clec) (syn_cfv (syn_cwppconcrete6fn) (syn_ctc (syn_ctc (syn_ctc
                      (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c)))))))))))
            (syn_wbr (syn_cfv (syn_cwppconcrete6fn) (syn_ctc (syn_ctc (syn_ctc
                      (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c))))))))))
              (syn_clec) (syn_cfv (syn_cwppconcrete6fn) (.cv y))))))
      (.imp (.imp (syn_wa (syn_wwpp) (syn_wbr (syn_ctc (syn_ctc (syn_ctc
                    (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c)))))))))
              (syn_clec) (.cv y))) (syn_wa (syn_wwpp) (syn_wbr (syn_ctc (syn_ctc (syn_ctc
                    (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c)))))))))
              (syn_clec) (.cv y)))) (.imp (syn_wa (syn_wwpp) (syn_wbr (syn_ctc (syn_ctc (syn_ctc
                    (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c)))))))))
              (syn_clec) (.cv y))) (syn_wa (syn_wbr (syn_ctc
                (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c))))))))
              (syn_clec) (syn_cfv (syn_cwppconcrete6fn) (syn_ctc (syn_ctc (syn_ctc
                      (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c)))))))))))
            (syn_wbr (syn_cfv (syn_cwppconcrete6fn) (syn_ctc (syn_ctc (syn_ctc
                      (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c))))))))))
              (syn_clec) (syn_cfv (syn_cwppconcrete6fn) (.cv y))))))
      p0088 p0089
  have p0091 :=
    @g_mpdi (.classMem (.cv y) (syn_chwcards (syn_cvv)))
      (syn_wbr (.cv y) (syn_clec) (syn_ctc
          (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c)))))))))
      (.imp (syn_wa (syn_wwpp) (syn_wbr (syn_ctc (syn_ctc (syn_ctc
                  (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c)))))))))
            (syn_clec) (.cv y))) (syn_wa (syn_wwpp) (syn_wbr (syn_ctc (syn_ctc (syn_ctc
                  (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c)))))))))
            (syn_clec) (.cv y))))
      (.imp (syn_wa (syn_wwpp) (syn_wbr (syn_ctc (syn_ctc (syn_ctc
                  (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c)))))))))
            (syn_clec) (.cv y))) (syn_wa (syn_wbr (syn_ctc
              (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c))))))))
            (syn_clec) (syn_cfv (syn_cwppconcrete6fn) (syn_ctc (syn_ctc (syn_ctc
                    (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c)))))))))))
          (syn_wbr (syn_cfv (syn_cwppconcrete6fn) (syn_ctc (syn_ctc (syn_ctc
                    (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c))))))))))
            (syn_clec) (syn_cfv (syn_cwppconcrete6fn) (.cv y)))))
      p0001 p0090
  have p0092 :=
    @g_id
      (.classEq (.cv y)
        (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_cnc (.cv z)))))))))
  have p0093 :=
    @g_fveq2d
      (.classEq (.cv y)
        (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_cnc (.cv z)))))))))
      (.cv y)
      (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_cnc (.cv z))))))))
      (syn_cwppconcrete6fn) p0092
  have p0095 := @g_wppconcrete6fnvalndv (.cv z) p0048
  have p0097 := @g_pwex (.cv z) p0048
  have p0098 := @g_pwex (syn_cpw (.cv z)) p0097
  have p0099 := @g_hnordex (syn_cpw (syn_cpw (.cv z))) p0098
  have p0100 := @g_hncardnc (syn_chnord (syn_cpw (syn_cpw (.cv z))))
  have p0101 := Nominal.mp p0099 p0100
  have p0102 :=
    @g_eqeltri
      (syn_cfv (syn_cwppconcrete6fn)
        (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_cnc (.cv z)))))))))
      (syn_chncard (syn_chnord (syn_cpw (syn_cpw (.cv z))))) (syn_cncs) p0095 p0101
  have p0103 :=
    @g_a1i
      (.classMem (syn_cfv (syn_cwppconcrete6fn)
          (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_cnc (.cv z)))))))))
        (syn_cncs))
      (.classEq (.cv y)
        (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_cnc (.cv z)))))))))
      p0102
  have p0104 :=
    @g_eqeltrd
      (.classEq (.cv y)
        (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_cnc (.cv z)))))))))
      (syn_cfv (syn_cwppconcrete6fn) (.cv y))
      (syn_cfv (syn_cwppconcrete6fn)
        (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_cnc (.cv z)))))))))
      (syn_cncs) p0093 p0103
  have p0105 :=
    @g_exlimiv
      (.classEq (.cv y)
        (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_cnc (.cv z)))))))))
      (.classMem (syn_cfv (syn_cwppconcrete6fn) (.cv y)) (syn_cncs)) z dv_cache_0005 p0104
  have p0106 :=
    @g_syl6 (.classMem (.cv y) (syn_chwcards (syn_cvv)))
      (syn_wbr (.cv y) (syn_clec) (syn_ctc
          (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c)))))))))
      (syn_wex z (.classEq (.cv y)
          (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_cnc (.cv z))))))))))
      (.classMem (syn_cfv (syn_cwppconcrete6fn) (.cv y)) (syn_cncs)) p0017 p0105
  have p0107 :=
    (Nominal.biimpRefl (syn_w3a (.classMem (syn_ctc
            (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c))))))))
          (syn_cncs)) (.classMem (syn_cfv (syn_cwppconcrete6fn) (syn_ctc (syn_ctc (syn_ctc
                  (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c))))))))))
          (syn_cncs)) (.classMem (syn_cfv (syn_cwppconcrete6fn) (.cv y)) (syn_cncs))))
  have p0109 := @g_tccl (syn_chncard (syn_c1c))
  have p0110 := Nominal.mp p0010 p0109
  have p0111 := @g_tccl (syn_ctc (syn_chncard (syn_c1c)))
  have p0112 := Nominal.mp p0110 p0111
  have p0113 := @g_tccl (syn_ctc (syn_ctc (syn_chncard (syn_c1c))))
  have p0114 := Nominal.mp p0112 p0113
  have p0115 := @g_tccl (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c)))))
  have p0116 := Nominal.mp p0114 p0115
  have p0117 := @g_tccl (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c))))))
  have p0118 := Nominal.mp p0116 p0117
  have p0119 :=
    @g_tccl (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c)))))))
  have p0120 := Nominal.mp p0118 p0119
  have p0121 := @g_wppconcrete6tcvalncndv
  have p0122 :=
    @g_pm3_2i
      (.classMem (syn_ctc
          (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c)))))))) (syn_cncs))
      (.classMem (syn_cfv (syn_cwppconcrete6fn) (syn_ctc (syn_ctc
              (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c))))))))))
        (syn_cncs))
      p0120 p0121
  have p0123 :=
    @g_biantrur
      (syn_wa (.classMem (syn_ctc
            (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c))))))))
          (syn_cncs)) (.classMem (syn_cfv (syn_cwppconcrete6fn) (syn_ctc (syn_ctc (syn_ctc
                  (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c))))))))))
          (syn_cncs)))
      (.classMem (syn_cfv (syn_cwppconcrete6fn) (.cv y)) (syn_cncs)) p0122
  have p0124 :=
    @g_bitr4i
      (syn_w3a (.classMem (syn_ctc
            (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c))))))))
          (syn_cncs)) (.classMem (syn_cfv (syn_cwppconcrete6fn) (syn_ctc (syn_ctc (syn_ctc
                  (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c))))))))))
          (syn_cncs)) (.classMem (syn_cfv (syn_cwppconcrete6fn) (.cv y)) (syn_cncs)))
      (syn_wa (syn_wa (.classMem (syn_ctc
              (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c))))))))
            (syn_cncs)) (.classMem (syn_cfv (syn_cwppconcrete6fn) (syn_ctc (syn_ctc (syn_ctc
                    (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c))))))))))
            (syn_cncs))) (.classMem (syn_cfv (syn_cwppconcrete6fn) (.cv y)) (syn_cncs)))
      (.classMem (syn_cfv (syn_cwppconcrete6fn) (.cv y)) (syn_cncs)) p0107 p0123
  have p0125 :=
    @g_a1i
      (syn_wb (syn_w3a (.classMem (syn_ctc
              (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c))))))))
            (syn_cncs)) (.classMem (syn_cfv (syn_cwppconcrete6fn) (syn_ctc (syn_ctc (syn_ctc
                    (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c))))))))))
            (syn_cncs)) (.classMem (syn_cfv (syn_cwppconcrete6fn) (.cv y)) (syn_cncs)))
        (.classMem (syn_cfv (syn_cwppconcrete6fn) (.cv y)) (syn_cncs)))
      (syn_wbr (.cv y) (syn_clec) (syn_ctc
          (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c)))))))))
      p0124
  have p0126 :=
    @g_biimprd
      (syn_wbr (.cv y) (syn_clec) (syn_ctc
          (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c)))))))))
      (syn_w3a (.classMem (syn_ctc
            (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c))))))))
          (syn_cncs)) (.classMem (syn_cfv (syn_cwppconcrete6fn) (syn_ctc (syn_ctc (syn_ctc
                  (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c))))))))))
          (syn_cncs)) (.classMem (syn_cfv (syn_cwppconcrete6fn) (.cv y)) (syn_cncs)))
      (.classMem (syn_cfv (syn_cwppconcrete6fn) (.cv y)) (syn_cncs)) p0125
  have p0127 :=
    @g_sylcom (.classMem (.cv y) (syn_chwcards (syn_cvv)))
      (syn_wbr (.cv y) (syn_clec) (syn_ctc
          (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c)))))))))
      (.classMem (syn_cfv (syn_cwppconcrete6fn) (.cv y)) (syn_cncs))
      (syn_w3a (.classMem (syn_ctc
            (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c))))))))
          (syn_cncs)) (.classMem (syn_cfv (syn_cwppconcrete6fn) (syn_ctc (syn_ctc (syn_ctc
                  (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c))))))))))
          (syn_cncs)) (.classMem (syn_cfv (syn_cwppconcrete6fn) (.cv y)) (syn_cncs)))
      p0106 p0126
  have p0128 :=
    @g_lectr
      (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c))))))))
      (syn_cfv (syn_cwppconcrete6fn) (syn_ctc (syn_ctc
            (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c))))))))))
      (syn_cfv (syn_cwppconcrete6fn) (.cv y))
  have p0129 :=
    @g_syl6 (.classMem (.cv y) (syn_chwcards (syn_cvv)))
      (syn_wbr (.cv y) (syn_clec) (syn_ctc
          (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c)))))))))
      (syn_w3a (.classMem (syn_ctc
            (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c))))))))
          (syn_cncs)) (.classMem (syn_cfv (syn_cwppconcrete6fn) (syn_ctc (syn_ctc (syn_ctc
                  (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c))))))))))
          (syn_cncs)) (.classMem (syn_cfv (syn_cwppconcrete6fn) (.cv y)) (syn_cncs)))
      (.imp (syn_wa (syn_wbr (syn_ctc
              (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c))))))))
            (syn_clec) (syn_cfv (syn_cwppconcrete6fn) (syn_ctc (syn_ctc (syn_ctc
                    (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c)))))))))))
          (syn_wbr (syn_cfv (syn_cwppconcrete6fn) (syn_ctc (syn_ctc (syn_ctc
                    (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c))))))))))
            (syn_clec) (syn_cfv (syn_cwppconcrete6fn) (.cv y)))) (syn_wbr (syn_ctc
            (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c))))))))
          (syn_clec) (syn_cfv (syn_cwppconcrete6fn) (.cv y))))
      p0127 p0128
  have p0130 :=
    @g_syldd (.classMem (.cv y) (syn_chwcards (syn_cvv)))
      (syn_wbr (.cv y) (syn_clec) (syn_ctc
          (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c)))))))))
      (syn_wa (syn_wwpp) (syn_wbr (syn_ctc (syn_ctc
              (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c)))))))))
          (syn_clec) (.cv y)))
      (syn_wa (syn_wbr (syn_ctc
            (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c))))))))
          (syn_clec) (syn_cfv (syn_cwppconcrete6fn) (syn_ctc (syn_ctc (syn_ctc
                  (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c))))))))))) (syn_wbr
          (syn_cfv (syn_cwppconcrete6fn) (syn_ctc (syn_ctc (syn_ctc
                  (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c))))))))))
          (syn_clec) (syn_cfv (syn_cwppconcrete6fn) (.cv y))))
      (syn_wbr (syn_ctc
          (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c))))))))
        (syn_clec) (syn_cfv (syn_cwppconcrete6fn) (.cv y)))
      p0091 p0129
  have p0131 :=
    @g_exp4a (.classMem (.cv y) (syn_chwcards (syn_cvv)))
      (syn_wbr (.cv y) (syn_clec) (syn_ctc
          (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c)))))))))
      (syn_wwpp)
      (syn_wbr (syn_ctc (syn_ctc
            (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c)))))))))
        (syn_clec) (.cv y))
      (syn_wbr (syn_ctc
          (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c))))))))
        (syn_clec) (syn_cfv (syn_cwppconcrete6fn) (.cv y)))
      p0130
  exact p0131


end NFChoice.DirectNominalPrf.WPPReplay

end

/-! Certificates from `NominalWPPReplayChunk017Compact001Part086`. -/


section

namespace NFChoice.DirectNominalPrf.WPPReplay

open scoped Fol
open NFChoice.Foundation
open NFChoice.SemanticCore
open NFChoice.ReplaySupport
open NFChoice.Compiler.CompactSourceSyntax

@[expose]
noncomputable def g_wppconcrete6stoppedgrowthfrompointndv (y : Var)
    (hyp_wppconcrete6stoppedgrowthfrompointndv_1 : Nominal.NPrf (.imp (syn_wwpp) (syn_wbr
            (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c))))))))
            (syn_clec) (syn_cfv (syn_cwppconcrete6fn) (syn_ctc (syn_ctc (syn_ctc (syn_ctc
                      (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c))))))))))))) :
    Nominal.NPrf
      (.imp (syn_wwpp) (syn_wral y (syn_cdm (syn_cwppstopstep (syn_cwppconcrete6fn) (syn_ctc
                (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c))))))))))
          (.imp (syn_wbr (syn_ctc (syn_ctc (syn_ctc
                    (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c)))))))))
              (syn_clec) (.cv y)) (syn_wbr (syn_ctc
                (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c))))))))
              (syn_clec) (syn_cfv (syn_cwppstopstep (syn_cwppconcrete6fn) (syn_ctc (syn_ctc
                      (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c)))))))))
                (.cv y)))))) :=
  by
  let proofSupport : Finset Var := ({ y } : Finset Var)
  let p : Var := freshVar proofSupport 0
  have fresh_p : p ∉ proofSupport :=
    by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_p_ne_y : p ≠ y := by
    intro h
    exact fresh_p (Finset.mem_singleton.mpr h)
  have dv_cache_0001 : p ∉ ((Class.cv y)).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : p ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_p_ne_y, not_false_eq_true])
  have dv_cache_0002 : p ∉ ((syn_chwcards (syn_cvv))).fv :=
    by
    clear dv_cache_0001
    exact
      (by
        have compact_fv_not_mem_empty : p ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwcards,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv, compact_fv_not_mem_empty,
          not_false_eq_true])
  have dv_cache_0003 :
    p ∉
      ((Wff.imp (syn_wbr (.cv y) (syn_clec) (syn_ctc
              (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c)))))))))
          (.classMem (.cv y) (syn_cdm (syn_cwppconcrete6fn))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact
      (by
        have compact_fv_not_mem_empty : p ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_clec,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ctc,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chncard,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdm,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwppconcrete6fn,
          Finset.mem_union, Finset.mem_singleton, fresh_p_ne_y, compact_fv_not_mem_empty,
          or_false, not_false_eq_true])
  have dv_cache_0004 : y ∉ ((syn_wwpp)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_wwpp,
          compact_fv_not_mem_empty, not_false_eq_true])
  have p0000 :=
    @g_n_3simpc (syn_wwpp)
      (.classMem (.cv y) (syn_cdm (syn_cwppstopstep (syn_cwppconcrete6fn) (syn_ctc (syn_ctc
                (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c)))))))))))
      (syn_wbr (syn_ctc (syn_ctc
            (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c)))))))))
        (syn_clec) (.cv y))
  have p0001 :=
    @g_simpr
      (.classMem (.cv y) (syn_cdm (syn_cwppstopstep (syn_cwppconcrete6fn) (syn_ctc (syn_ctc
                (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c)))))))))))
      (syn_wbr (syn_ctc (syn_ctc
            (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c)))))))))
        (syn_clec) (.cv y))
  have p0002 :=
    @g_syl
      (syn_w3a (syn_wwpp) (.classMem (.cv y) (syn_cdm (syn_cwppstopstep (syn_cwppconcrete6fn)
              (syn_ctc (syn_ctc
                  (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c))))))))))) (syn_wbr
          (syn_ctc (syn_ctc
              (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c)))))))))
          (syn_clec) (.cv y)))
      (syn_wa (.classMem (.cv y) (syn_cdm (syn_cwppstopstep (syn_cwppconcrete6fn) (syn_ctc
                (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c)))))))))))
        (syn_wbr (syn_ctc (syn_ctc
              (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c)))))))))
          (syn_clec) (.cv y)))
      (syn_wbr (syn_ctc (syn_ctc
            (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c)))))))))
        (syn_clec) (.cv y))
      p0000 p0001
  have p0003 :=
    @g_n_3simpa (syn_wwpp)
      (.classMem (.cv y) (syn_cdm (syn_cwppstopstep (syn_cwppconcrete6fn) (syn_ctc (syn_ctc
                (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c)))))))))))
      (syn_wbr (syn_ctc (syn_ctc
            (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c)))))))))
        (syn_clec) (.cv y))
  have p0004 :=
    @g_simpl (syn_wwpp)
      (.classMem (.cv y) (syn_cdm (syn_cwppstopstep (syn_cwppconcrete6fn) (syn_ctc (syn_ctc
                (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c)))))))))))
  have p0005 :=
    @g_syl
      (syn_w3a (syn_wwpp) (.classMem (.cv y) (syn_cdm (syn_cwppstopstep (syn_cwppconcrete6fn)
              (syn_ctc (syn_ctc
                  (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c))))))))))) (syn_wbr
          (syn_ctc (syn_ctc
              (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c)))))))))
          (syn_clec) (.cv y)))
      (syn_wa (syn_wwpp) (.classMem (.cv y) (syn_cdm (syn_cwppstopstep (syn_cwppconcrete6fn)
              (syn_ctc (syn_ctc
                  (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c))))))))))))
      (syn_wwpp) p0003 p0004
  have p0007 :=
    @g_simpr (syn_wwpp)
      (.classMem (.cv y) (syn_cdm (syn_cwppstopstep (syn_cwppconcrete6fn) (syn_ctc (syn_ctc
                (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c)))))))))))
  have p0008 :=
    @g_syl
      (syn_w3a (syn_wwpp) (.classMem (.cv y) (syn_cdm (syn_cwppstopstep (syn_cwppconcrete6fn)
              (syn_ctc (syn_ctc
                  (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c))))))))))) (syn_wbr
          (syn_ctc (syn_ctc
              (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c)))))))))
          (syn_clec) (.cv y)))
      (syn_wa (syn_wwpp) (.classMem (.cv y) (syn_cdm (syn_cwppstopstep (syn_cwppconcrete6fn)
              (syn_ctc (syn_ctc
                  (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c))))))))))))
      (.classMem (.cv y) (syn_cdm (syn_cwppstopstep (syn_cwppconcrete6fn) (syn_ctc (syn_ctc
                (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c)))))))))))
      p0003 p0007
  have p0009 := @g_wppconcrete6fnfunsndv
  have p0010 := @g_wppconcrete6rnhwcardsndv
  have p0011 :=
    @g_wppstopstepdmndv
      (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c))))))))
      (syn_cwppconcrete6fn) p0009 p0010
  have p0012 :=
    @g_eleq2i
      (syn_cdm (syn_cwppstopstep (syn_cwppconcrete6fn) (syn_ctc
            (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c))))))))))
      (syn_chwcards (syn_cvv)) (.cv y) p0011
  have p0013 :=
    @g_biimpi
      (.classMem (.cv y) (syn_cdm (syn_cwppstopstep (syn_cwppconcrete6fn) (syn_ctc (syn_ctc
                (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c)))))))))))
      (.classMem (.cv y) (syn_chwcards (syn_cvv))) p0012
  have p0014 :=
    @g_syl
      (syn_w3a (syn_wwpp) (.classMem (.cv y) (syn_cdm (syn_cwppstopstep (syn_cwppconcrete6fn)
              (syn_ctc (syn_ctc
                  (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c))))))))))) (syn_wbr
          (syn_ctc (syn_ctc
              (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c)))))))))
          (syn_clec) (.cv y)))
      (.classMem (.cv y) (syn_cdm (syn_cwppstopstep (syn_cwppconcrete6fn) (syn_ctc (syn_ctc
                (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c)))))))))))
      (.classMem (.cv y) (syn_chwcards (syn_cvv))) p0008 p0013
  have p0015 :=
    @g_wppconcrete6tcbandgrowthfrompointhwclecdndv y
      hyp_wppconcrete6stoppedgrowthfrompointndv_1
  have p0016 :=
    @g_syl
      (syn_w3a (syn_wwpp) (.classMem (.cv y) (syn_cdm (syn_cwppstopstep (syn_cwppconcrete6fn)
              (syn_ctc (syn_ctc
                  (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c))))))))))) (syn_wbr
          (syn_ctc (syn_ctc
              (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c)))))))))
          (syn_clec) (.cv y)))
      (.classMem (.cv y) (syn_chwcards (syn_cvv)))
      (.imp (syn_wbr (.cv y) (syn_clec) (syn_ctc
            (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c)))))))))
        (.imp (syn_wwpp) (.imp (syn_wbr (syn_ctc (syn_ctc (syn_ctc
                    (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c)))))))))
              (syn_clec) (.cv y)) (syn_wbr (syn_ctc
                (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c))))))))
              (syn_clec) (syn_cfv (syn_cwppconcrete6fn) (.cv y))))))
      p0014 p0015
  have p0017 :=
    @g_mpid
      (syn_w3a (syn_wwpp) (.classMem (.cv y) (syn_cdm (syn_cwppstopstep (syn_cwppconcrete6fn)
              (syn_ctc (syn_ctc
                  (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c))))))))))) (syn_wbr
          (syn_ctc (syn_ctc
              (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c)))))))))
          (syn_clec) (.cv y)))
      (syn_wbr (.cv y) (syn_clec) (syn_ctc
          (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c)))))))))
      (syn_wwpp)
      (.imp (syn_wbr (syn_ctc (syn_ctc
              (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c)))))))))
          (syn_clec) (.cv y)) (syn_wbr (syn_ctc
            (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c))))))))
          (syn_clec) (syn_cfv (syn_cwppconcrete6fn) (.cv y))))
      p0005 p0016
  have p0018 :=
    @g_mpid
      (syn_w3a (syn_wwpp) (.classMem (.cv y) (syn_cdm (syn_cwppstopstep (syn_cwppconcrete6fn)
              (syn_ctc (syn_ctc
                  (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c))))))))))) (syn_wbr
          (syn_ctc (syn_ctc
              (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c)))))))))
          (syn_clec) (.cv y)))
      (syn_wbr (.cv y) (syn_clec) (syn_ctc
          (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c)))))))))
      (syn_wbr (syn_ctc (syn_ctc
            (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c)))))))))
        (syn_clec) (.cv y))
      (syn_wbr (syn_ctc
          (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c))))))))
        (syn_clec) (syn_cfv (syn_cwppconcrete6fn) (.cv y)))
      p0002 p0017
  have p0019 :=
    @g_imp
      (syn_w3a (syn_wwpp) (.classMem (.cv y) (syn_cdm (syn_cwppstopstep (syn_cwppconcrete6fn)
              (syn_ctc (syn_ctc
                  (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c))))))))))) (syn_wbr
          (syn_ctc (syn_ctc
              (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c)))))))))
          (syn_clec) (.cv y)))
      (syn_wbr (.cv y) (syn_clec) (syn_ctc
          (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c)))))))))
      (syn_wbr (syn_ctc
          (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c))))))))
        (syn_clec) (syn_cfv (syn_cwppconcrete6fn) (.cv y)))
      p0018
  have p0038 := @g_wppconcrete6hncard1dmcovndv p
  have p0039 := @g_id (.classEq (.cv p) (.cv y))
  have p0040 :=
    @g_breq1d (.classEq (.cv p) (.cv y)) (.cv p) (.cv y)
      (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c))))))))
      (syn_clec) p0039
  have p0042 :=
    @g_eleq1d (.classEq (.cv p) (.cv y)) (.cv p) (.cv y) (syn_cdm (syn_cwppconcrete6fn))
      p0039
  have p0043 :=
    @g_imbi12d (.classEq (.cv p) (.cv y))
      (syn_wbr (.cv p) (syn_clec) (syn_ctc
          (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c)))))))))
      (syn_wbr (.cv y) (syn_clec) (syn_ctc
          (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c)))))))))
      (.classMem (.cv p) (syn_cdm (syn_cwppconcrete6fn)))
      (.classMem (.cv y) (syn_cdm (syn_cwppconcrete6fn))) p0040 p0042
  have p0044 :=
    @g_rspcv
      (.imp (syn_wbr (.cv p) (syn_clec) (syn_ctc
            (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c)))))))))
        (.classMem (.cv p) (syn_cdm (syn_cwppconcrete6fn))))
      (.imp (syn_wbr (.cv y) (syn_clec) (syn_ctc
            (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c)))))))))
        (.classMem (.cv y) (syn_cdm (syn_cwppconcrete6fn))))
      p (.cv y) (syn_chwcards (syn_cvv)) dv_cache_0001 dv_cache_0002 dv_cache_0003 p0043
  have p0045 :=
    @g_mpi (.classMem (.cv y) (syn_chwcards (syn_cvv)))
      (syn_wral p (syn_chwcards (syn_cvv)) (.imp (syn_wbr (.cv p) (syn_clec) (syn_ctc
              (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c)))))))))
          (.classMem (.cv p) (syn_cdm (syn_cwppconcrete6fn)))))
      (.imp (syn_wbr (.cv y) (syn_clec) (syn_ctc
            (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c)))))))))
        (.classMem (.cv y) (syn_cdm (syn_cwppconcrete6fn))))
      p0038 p0044
  have p0046 :=
    @g_syl
      (syn_w3a (syn_wwpp) (.classMem (.cv y) (syn_cdm (syn_cwppstopstep (syn_cwppconcrete6fn)
              (syn_ctc (syn_ctc
                  (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c))))))))))) (syn_wbr
          (syn_ctc (syn_ctc
              (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c)))))))))
          (syn_clec) (.cv y)))
      (.classMem (.cv y) (syn_chwcards (syn_cvv)))
      (.imp (syn_wbr (.cv y) (syn_clec) (syn_ctc
            (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c)))))))))
        (.classMem (.cv y) (syn_cdm (syn_cwppconcrete6fn))))
      p0014 p0045
  have p0047 :=
    @g_jca
      (syn_w3a (syn_wwpp) (.classMem (.cv y) (syn_cdm (syn_cwppstopstep (syn_cwppconcrete6fn)
              (syn_ctc (syn_ctc
                  (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c))))))))))) (syn_wbr
          (syn_ctc (syn_ctc
              (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c)))))))))
          (syn_clec) (.cv y)))
      (.classMem (.cv y) (syn_chwcards (syn_cvv)))
      (.imp (syn_wbr (.cv y) (syn_clec) (syn_ctc
            (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c)))))))))
        (.classMem (.cv y) (syn_cdm (syn_cwppconcrete6fn))))
      p0014 p0046
  have p0050 :=
    @g_wppstopstepfvlecdndv (.cv y)
      (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c))))))))
      (syn_cwppconcrete6fn) p0009 p0010
  have p0051 :=
    @g_syl
      (syn_w3a (syn_wwpp) (.classMem (.cv y) (syn_cdm (syn_cwppstopstep (syn_cwppconcrete6fn)
              (syn_ctc (syn_ctc
                  (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c))))))))))) (syn_wbr
          (syn_ctc (syn_ctc
              (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c)))))))))
          (syn_clec) (.cv y)))
      (syn_wa (.classMem (.cv y) (syn_chwcards (syn_cvv))) (.imp (syn_wbr (.cv y) (syn_clec)
            (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c)))))))))
          (.classMem (.cv y) (syn_cdm (syn_cwppconcrete6fn)))))
      (.imp (syn_wbr (.cv y) (syn_clec) (syn_ctc
            (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c)))))))))
        (.classEq (syn_cfv (syn_cwppstopstep (syn_cwppconcrete6fn) (syn_ctc (syn_ctc
                  (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c))))))))) (.cv y))
          (syn_cfv (syn_cwppconcrete6fn) (.cv y))))
      p0047 p0050
  have p0052 :=
    @g_imp
      (syn_w3a (syn_wwpp) (.classMem (.cv y) (syn_cdm (syn_cwppstopstep (syn_cwppconcrete6fn)
              (syn_ctc (syn_ctc
                  (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c))))))))))) (syn_wbr
          (syn_ctc (syn_ctc
              (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c)))))))))
          (syn_clec) (.cv y)))
      (syn_wbr (.cv y) (syn_clec) (syn_ctc
          (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c)))))))))
      (.classEq (syn_cfv (syn_cwppstopstep (syn_cwppconcrete6fn) (syn_ctc
              (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c)))))))))
          (.cv y)) (syn_cfv (syn_cwppconcrete6fn) (.cv y)))
      p0051
  have p0053 :=
    @g_breq2d
      (syn_wa (syn_w3a (syn_wwpp) (.classMem (.cv y) (syn_cdm
              (syn_cwppstopstep (syn_cwppconcrete6fn) (syn_ctc (syn_ctc
                    (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c)))))))))))
          (syn_wbr (syn_ctc (syn_ctc (syn_ctc
                  (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c)))))))))
            (syn_clec) (.cv y))) (syn_wbr (.cv y) (syn_clec) (syn_ctc
            (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c))))))))))
      (syn_cfv (syn_cwppstopstep (syn_cwppconcrete6fn) (syn_ctc
            (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c))))))))) (.cv y))
      (syn_cfv (syn_cwppconcrete6fn) (.cv y))
      (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c))))))))
      (syn_clec) p0052
  have p0054 :=
    @g_biimprd
      (syn_wa (syn_w3a (syn_wwpp) (.classMem (.cv y) (syn_cdm
              (syn_cwppstopstep (syn_cwppconcrete6fn) (syn_ctc (syn_ctc
                    (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c)))))))))))
          (syn_wbr (syn_ctc (syn_ctc (syn_ctc
                  (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c)))))))))
            (syn_clec) (.cv y))) (syn_wbr (.cv y) (syn_clec) (syn_ctc
            (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c))))))))))
      (syn_wbr (syn_ctc
          (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c)))))))) (syn_clec)
        (syn_cfv (syn_cwppstopstep (syn_cwppconcrete6fn) (syn_ctc
              (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c)))))))))
          (.cv y)))
      (syn_wbr (syn_ctc
          (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c))))))))
        (syn_clec) (syn_cfv (syn_cwppconcrete6fn) (.cv y)))
      p0053
  have p0055 :=
    @g_mpd
      (syn_wa (syn_w3a (syn_wwpp) (.classMem (.cv y) (syn_cdm
              (syn_cwppstopstep (syn_cwppconcrete6fn) (syn_ctc (syn_ctc
                    (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c)))))))))))
          (syn_wbr (syn_ctc (syn_ctc (syn_ctc
                  (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c)))))))))
            (syn_clec) (.cv y))) (syn_wbr (.cv y) (syn_clec) (syn_ctc
            (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c))))))))))
      (syn_wbr (syn_ctc
          (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c))))))))
        (syn_clec) (syn_cfv (syn_cwppconcrete6fn) (.cv y)))
      (syn_wbr (syn_ctc
          (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c)))))))) (syn_clec)
        (syn_cfv (syn_cwppstopstep (syn_cwppconcrete6fn) (syn_ctc
              (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c)))))))))
          (.cv y)))
      p0019 p0054
  have p0056 :=
    @g_ex
      (syn_w3a (syn_wwpp) (.classMem (.cv y) (syn_cdm (syn_cwppstopstep (syn_cwppconcrete6fn)
              (syn_ctc (syn_ctc
                  (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c))))))))))) (syn_wbr
          (syn_ctc (syn_ctc
              (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c)))))))))
          (syn_clec) (.cv y)))
      (syn_wbr (.cv y) (syn_clec) (syn_ctc
          (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c)))))))))
      (syn_wbr (syn_ctc
          (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c)))))))) (syn_clec)
        (syn_cfv (syn_cwppstopstep (syn_cwppconcrete6fn) (syn_ctc
              (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c)))))))))
          (.cv y)))
      p0055
  have p0066 := @g_wppconcrete6thresholdhwcardsndv
  have p0067 :=
    @g_a1i
      (.classMem (syn_ctc
          (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c))))))))
        (syn_chwcards (syn_cvv)))
      (syn_w3a (syn_wwpp) (.classMem (.cv y) (syn_cdm (syn_cwppstopstep (syn_cwppconcrete6fn)
              (syn_ctc (syn_ctc
                  (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c))))))))))) (syn_wbr
          (syn_ctc (syn_ctc
              (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c)))))))))
          (syn_clec) (.cv y)))
      p0066
  have p0068 :=
    @g_jca
      (syn_w3a (syn_wwpp) (.classMem (.cv y) (syn_cdm (syn_cwppstopstep (syn_cwppconcrete6fn)
              (syn_ctc (syn_ctc
                  (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c))))))))))) (syn_wbr
          (syn_ctc (syn_ctc
              (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c)))))))))
          (syn_clec) (.cv y)))
      (.classMem (.cv y) (syn_chwcards (syn_cvv)))
      (.classMem (syn_ctc
          (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c))))))))
        (syn_chwcards (syn_cvv)))
      p0014 p0067
  have p0069 :=
    @g_hwcardslecconnexndv (.cv y)
      (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c))))))))
  have p0070 :=
    @g_syl
      (syn_w3a (syn_wwpp) (.classMem (.cv y) (syn_cdm (syn_cwppstopstep (syn_cwppconcrete6fn)
              (syn_ctc (syn_ctc
                  (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c))))))))))) (syn_wbr
          (syn_ctc (syn_ctc
              (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c)))))))))
          (syn_clec) (.cv y)))
      (syn_wa (.classMem (.cv y) (syn_chwcards (syn_cvv))) (.classMem (syn_ctc
            (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c))))))))
          (syn_chwcards (syn_cvv))))
      (syn_wo (syn_wbr (.cv y) (syn_clec) (syn_ctc
            (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c))))))))) (syn_wbr
          (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c))))))))
          (syn_clec) (.cv y)))
      p0068 p0069
  have p0071 :=
    @g_ord
      (syn_w3a (syn_wwpp) (.classMem (.cv y) (syn_cdm (syn_cwppstopstep (syn_cwppconcrete6fn)
              (syn_ctc (syn_ctc
                  (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c))))))))))) (syn_wbr
          (syn_ctc (syn_ctc
              (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c)))))))))
          (syn_clec) (.cv y)))
      (syn_wbr (.cv y) (syn_clec) (syn_ctc
          (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c)))))))))
      (syn_wbr (syn_ctc
          (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c))))))))
        (syn_clec) (.cv y))
      p0070
  have p0072 :=
    @g_imp
      (syn_w3a (syn_wwpp) (.classMem (.cv y) (syn_cdm (syn_cwppstopstep (syn_cwppconcrete6fn)
              (syn_ctc (syn_ctc
                  (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c))))))))))) (syn_wbr
          (syn_ctc (syn_ctc
              (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c)))))))))
          (syn_clec) (.cv y)))
      (.neg (syn_wbr (.cv y) (syn_clec) (syn_ctc
            (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c))))))))))
      (syn_wbr (syn_ctc
          (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c))))))))
        (syn_clec) (.cv y))
      p0071
  have p0103 :=
    @g_wppstopstepfvnlecdndv (.cv y)
      (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c))))))))
      (syn_cwppconcrete6fn) p0009 p0010
  have p0104 :=
    @g_syl
      (syn_w3a (syn_wwpp) (.classMem (.cv y) (syn_cdm (syn_cwppstopstep (syn_cwppconcrete6fn)
              (syn_ctc (syn_ctc
                  (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c))))))))))) (syn_wbr
          (syn_ctc (syn_ctc
              (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c)))))))))
          (syn_clec) (.cv y)))
      (syn_wa (.classMem (.cv y) (syn_chwcards (syn_cvv))) (.imp (syn_wbr (.cv y) (syn_clec)
            (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c)))))))))
          (.classMem (.cv y) (syn_cdm (syn_cwppconcrete6fn)))))
      (.imp (.neg (syn_wbr (.cv y) (syn_clec) (syn_ctc
              (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c))))))))))
        (.classEq (syn_cfv (syn_cwppstopstep (syn_cwppconcrete6fn) (syn_ctc (syn_ctc
                  (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c))))))))) (.cv y))
          (.cv y)))
      p0047 p0103
  have p0105 :=
    @g_imp
      (syn_w3a (syn_wwpp) (.classMem (.cv y) (syn_cdm (syn_cwppstopstep (syn_cwppconcrete6fn)
              (syn_ctc (syn_ctc
                  (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c))))))))))) (syn_wbr
          (syn_ctc (syn_ctc
              (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c)))))))))
          (syn_clec) (.cv y)))
      (.neg (syn_wbr (.cv y) (syn_clec) (syn_ctc
            (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c))))))))))
      (.classEq (syn_cfv (syn_cwppstopstep (syn_cwppconcrete6fn) (syn_ctc
              (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c)))))))))
          (.cv y)) (.cv y))
      p0104
  have p0106 :=
    @g_breq2d
      (syn_wa (syn_w3a (syn_wwpp) (.classMem (.cv y) (syn_cdm
              (syn_cwppstopstep (syn_cwppconcrete6fn) (syn_ctc (syn_ctc
                    (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c)))))))))))
          (syn_wbr (syn_ctc (syn_ctc (syn_ctc
                  (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c)))))))))
            (syn_clec) (.cv y))) (.neg (syn_wbr (.cv y) (syn_clec) (syn_ctc (syn_ctc
                (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c)))))))))))
      (syn_cfv (syn_cwppstopstep (syn_cwppconcrete6fn) (syn_ctc
            (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c))))))))) (.cv y))
      (.cv y)
      (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c))))))))
      (syn_clec) p0105
  have p0107 :=
    @g_biimprd
      (syn_wa (syn_w3a (syn_wwpp) (.classMem (.cv y) (syn_cdm
              (syn_cwppstopstep (syn_cwppconcrete6fn) (syn_ctc (syn_ctc
                    (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c)))))))))))
          (syn_wbr (syn_ctc (syn_ctc (syn_ctc
                  (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c)))))))))
            (syn_clec) (.cv y))) (.neg (syn_wbr (.cv y) (syn_clec) (syn_ctc (syn_ctc
                (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c)))))))))))
      (syn_wbr (syn_ctc
          (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c)))))))) (syn_clec)
        (syn_cfv (syn_cwppstopstep (syn_cwppconcrete6fn) (syn_ctc
              (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c)))))))))
          (.cv y)))
      (syn_wbr (syn_ctc
          (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c))))))))
        (syn_clec) (.cv y))
      p0106
  have p0108 :=
    @g_mpd
      (syn_wa (syn_w3a (syn_wwpp) (.classMem (.cv y) (syn_cdm
              (syn_cwppstopstep (syn_cwppconcrete6fn) (syn_ctc (syn_ctc
                    (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c)))))))))))
          (syn_wbr (syn_ctc (syn_ctc (syn_ctc
                  (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c)))))))))
            (syn_clec) (.cv y))) (.neg (syn_wbr (.cv y) (syn_clec) (syn_ctc (syn_ctc
                (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c)))))))))))
      (syn_wbr (syn_ctc
          (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c))))))))
        (syn_clec) (.cv y))
      (syn_wbr (syn_ctc
          (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c)))))))) (syn_clec)
        (syn_cfv (syn_cwppstopstep (syn_cwppconcrete6fn) (syn_ctc
              (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c)))))))))
          (.cv y)))
      p0072 p0107
  have p0109 :=
    @g_ex
      (syn_w3a (syn_wwpp) (.classMem (.cv y) (syn_cdm (syn_cwppstopstep (syn_cwppconcrete6fn)
              (syn_ctc (syn_ctc
                  (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c))))))))))) (syn_wbr
          (syn_ctc (syn_ctc
              (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c)))))))))
          (syn_clec) (.cv y)))
      (.neg (syn_wbr (.cv y) (syn_clec) (syn_ctc
            (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c))))))))))
      (syn_wbr (syn_ctc
          (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c)))))))) (syn_clec)
        (syn_cfv (syn_cwppstopstep (syn_cwppconcrete6fn) (syn_ctc
              (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c)))))))))
          (.cv y)))
      p0108
  have p0110 :=
    @g_pm2_61d
      (syn_w3a (syn_wwpp) (.classMem (.cv y) (syn_cdm (syn_cwppstopstep (syn_cwppconcrete6fn)
              (syn_ctc (syn_ctc
                  (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c))))))))))) (syn_wbr
          (syn_ctc (syn_ctc
              (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c)))))))))
          (syn_clec) (.cv y)))
      (syn_wbr (.cv y) (syn_clec) (syn_ctc
          (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c)))))))))
      (syn_wbr (syn_ctc
          (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c)))))))) (syn_clec)
        (syn_cfv (syn_cwppstopstep (syn_cwppconcrete6fn) (syn_ctc
              (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c)))))))))
          (.cv y)))
      p0056 p0109
  have p0111 :=
    @g_n_3exp (syn_wwpp)
      (.classMem (.cv y) (syn_cdm (syn_cwppstopstep (syn_cwppconcrete6fn) (syn_ctc (syn_ctc
                (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c)))))))))))
      (syn_wbr (syn_ctc (syn_ctc
            (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c)))))))))
        (syn_clec) (.cv y))
      (syn_wbr (syn_ctc
          (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c)))))))) (syn_clec)
        (syn_cfv (syn_cwppstopstep (syn_cwppconcrete6fn) (syn_ctc
              (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c)))))))))
          (.cv y)))
      p0110
  have p0112 :=
    @g_ralrimiv (syn_wwpp)
      (.imp (syn_wbr (syn_ctc (syn_ctc
              (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c)))))))))
          (syn_clec) (.cv y)) (syn_wbr (syn_ctc
            (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c))))))))
          (syn_clec) (syn_cfv (syn_cwppstopstep (syn_cwppconcrete6fn) (syn_ctc (syn_ctc
                  (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c))))))))) (.cv y))))
      y
      (syn_cdm (syn_cwppstopstep (syn_cwppconcrete6fn) (syn_ctc
            (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c))))))))))
      dv_cache_0004 p0111
  exact p0112

@[expose]
noncomputable def g_wppconcrete6notwppfrompointndv
    (hyp_wppconcrete6notwppfrompointndv_1 : Nominal.NPrf (.imp (syn_wwpp) (syn_wbr (syn_ctc
              (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c))))))))
            (syn_clec) (syn_cfv (syn_cwppconcrete6fn) (syn_ctc (syn_ctc (syn_ctc (syn_ctc
                      (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c))))))))))))) :
    Nominal.NPrf (.neg (syn_wwpp)) :=
  by
  let proofSupport : Finset Var := (∅ : Finset Var)
  let y : Var := freshVar proofSupport 0
  have p0000 := @g_eqid (syn_c0c)
  have p0001 := @g_notnoti (.classEq (syn_c0c) (syn_c0c)) p0000
  have p0002 :=
    @g_wppconcrete6stoppedgrowthfrompointndv y hyp_wppconcrete6notwppfrompointndv_1
  have p0003 := @g_n_1cex
  have p0004 := @g_pw1ex (syn_c1c) p0003
  have p0005 := @g_pw1ex (syn_cpw1 (syn_c1c)) p0004
  have p0006 := @g_pw1ex (syn_cpw1 (syn_cpw1 (syn_c1c))) p0005
  have p0007 := @g_pw1ex (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))) p0006
  have p0008 := @g_pw1ex (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))) p0007
  have p0009 :=
    @g_pw1ex (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))) p0008
  have p0010 :=
    @g_hncardtc2nodomndv
      (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))) p0009
  have p0011 := @g_wppconcrete6stoppedgammacontrgrowthstagedndv y p0010
  have p0012 :=
    @g_syl (syn_wwpp)
      (syn_wral y (syn_cdm (syn_cwppstopstep (syn_cwppconcrete6fn) (syn_ctc
              (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c)))))))))) (.imp
          (syn_wbr (syn_ctc (syn_ctc (syn_ctc
                  (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c)))))))))
            (syn_clec) (.cv y)) (syn_wbr (syn_ctc
              (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c))))))))
            (syn_clec) (syn_cfv (syn_cwppstopstep (syn_cwppconcrete6fn) (syn_ctc (syn_ctc
                    (syn_ctc (syn_ctc (syn_ctc (syn_ctc (syn_chncard (syn_c1c)))))))))
              (.cv y)))))
      (.neg (.classEq (syn_c0c) (syn_c0c))) p0002 p0011
  have p0013 := @g_mto (syn_wwpp) (.neg (.classEq (syn_c0c) (syn_c0c))) p0001 p0012
  exact p0013

@[expose]
noncomputable def g_hwcnselfbasendv (u : Var) (A : Class) (dv_A_u : u ∉ A.fv) :
    Nominal.NPrf
      (.imp (.classMem (.cv u) (syn_chwcn A))
        (.classMem (.cv u) (syn_chwcn (syn_cfv (syn_c2nd) (.cv u))))) :=
  by
  have dv_cache_0001 : u ∉ (A).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : u ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_A_u, not_false_eq_true])
  have p0000 := @g_hwcnwendv u A dv_cache_0001
  have p0001 := @g_ssid (syn_cfv (syn_c2nd) (.cv u))
  have p0002 :=
    @g_a1i (syn_wss (syn_cfv (syn_c2nd) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)))
      (.classMem (.cv u) (syn_chwcn A)) p0001
  have p0003 :=
    @g_jca (.classMem (.cv u) (syn_chwcn A))
      (syn_wbr (syn_cfv (syn_c1st) (.cv u)) (syn_cwe) (syn_cfv (syn_c2nd) (.cv u)))
      (syn_wss (syn_cfv (syn_c2nd) (.cv u)) (syn_cfv (syn_c2nd) (.cv u))) p0000 p0002
  have p0004 := @g_fvex (.cv u) (syn_c1st)
  have p0005 := @g_fvex (.cv u) (syn_c2nd)
  have p0006 :=
    @g_elhwcodesclndv (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u))
      (syn_cfv (syn_c2nd) (.cv u)) p0004 p0005
  have p0007 :=
    @g_sylibr (.classMem (.cv u) (syn_chwcn A))
      (syn_wa (syn_wbr (syn_cfv (syn_c1st) (.cv u)) (syn_cwe) (syn_cfv (syn_c2nd) (.cv u)))
        (syn_wss (syn_cfv (syn_c2nd) (.cv u)) (syn_cfv (syn_c2nd) (.cv u))))
      (.classMem (syn_cop (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)))
        (syn_chwcodes (syn_cfv (syn_c2nd) (.cv u))))
      p0003 p0006
  have p0008 := @g_hwcnpair u A
  have p0009 :=
    @g_eleq1d (.classMem (.cv u) (syn_chwcn A)) (.cv u)
      (syn_cop (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)))
      (syn_chwcodes (syn_cfv (syn_c2nd) (.cv u))) p0008
  have p0010 :=
    @g_mpbird (.classMem (.cv u) (syn_chwcn A))
      (.classMem (.cv u) (syn_chwcodes (syn_cfv (syn_c2nd) (.cv u))))
      (.classMem (syn_cop (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)))
        (syn_chwcodes (syn_cfv (syn_c2nd) (.cv u))))
      p0007 p0009
  have p0011 := @g_hwcnsupp u A
  have p0012 :=
    @g_jca (.classMem (.cv u) (syn_chwcn A))
      (.classMem (.cv u) (syn_chwcodes (syn_cfv (syn_c2nd) (.cv u))))
      (syn_wss (syn_cfv (syn_c1st) (.cv u))
        (syn_cxp (syn_cfv (syn_c2nd) (.cv u)) (syn_cfv (syn_c2nd) (.cv u))))
      p0010 p0011
  have p0013 := @g_elex (.cv u) (syn_chwcn A)
  have p0014 := @g_elhwcncl (syn_cfv (syn_c2nd) (.cv u)) (.cv u)
  have p0015 :=
    @g_syl (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv u) (syn_cvv))
      (syn_wb (.classMem (.cv u) (syn_chwcn (syn_cfv (syn_c2nd) (.cv u))))
        (syn_wa (.classMem (.cv u) (syn_chwcodes (syn_cfv (syn_c2nd) (.cv u))))
          (syn_wss (syn_cfv (syn_c1st) (.cv u))
            (syn_cxp (syn_cfv (syn_c2nd) (.cv u)) (syn_cfv (syn_c2nd) (.cv u))))))
      p0013 p0014
  have p0016 :=
    @g_mpbird (.classMem (.cv u) (syn_chwcn A))
      (.classMem (.cv u) (syn_chwcn (syn_cfv (syn_c2nd) (.cv u))))
      (syn_wa (.classMem (.cv u) (syn_chwcodes (syn_cfv (syn_c2nd) (.cv u))))
        (syn_wss (syn_cfv (syn_c1st) (.cv u))
          (syn_cxp (syn_cfv (syn_c2nd) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)))))
      p0012 p0015
  exact p0016

@[expose]
noncomputable def g_hnpw13quoshiftf1ondv (A : Class)
    (hyp_hnpw13quoshiftf1ondv_1 : Nominal.NPrf (.classMem A (syn_cvv))) :
    Nominal.NPrf
      (syn_wf1o (syn_ccom (syn_chnsiquomap (syn_cpw1 (syn_cpw1 A)))
          (syn_ccom (syn_csi (syn_chnsiquomap (syn_cpw1 A)))
            (syn_csi (syn_csi (syn_chnsiquomap A)))))
        (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_chnord A))))
        (syn_chnord (syn_cpw1 (syn_cpw1 (syn_cpw1 A))))) :=
  by
  have p0000 := @g_pw1ex A hyp_hnpw13quoshiftf1ondv_1
  have p0001 := @g_pw1ex (syn_cpw1 A) p0000
  have p0002 := @g_hnsiquomapf1ondv (syn_cpw1 (syn_cpw1 A)) p0001
  have p0004 := @g_hnsiquomapf1ondv (syn_cpw1 A) p0000
  have p0005 :=
    @g_pw1sif1omapndv (syn_cpw1 (syn_chnord (syn_cpw1 A)))
      (syn_chnord (syn_cpw1 (syn_cpw1 A))) (syn_chnsiquomap (syn_cpw1 A))
  have p0006 := Nominal.mp p0004 p0005
  have p0007 := @g_hnsiquomapf1ondv A hyp_hnpw13quoshiftf1ondv_1
  have p0008 :=
    @g_pw1sif1omapndv (syn_cpw1 (syn_chnord A)) (syn_chnord (syn_cpw1 A))
      (syn_chnsiquomap A)
  have p0009 := Nominal.mp p0007 p0008
  have p0010 :=
    @g_pw1sif1omapndv (syn_cpw1 (syn_cpw1 (syn_chnord A)))
      (syn_cpw1 (syn_chnord (syn_cpw1 A))) (syn_csi (syn_chnsiquomap A))
  have p0011 := Nominal.mp p0009 p0010
  have p0012 :=
    @g_pm3_2i
      (syn_wf1o (syn_csi (syn_chnsiquomap (syn_cpw1 A)))
        (syn_cpw1 (syn_cpw1 (syn_chnord (syn_cpw1 A))))
        (syn_cpw1 (syn_chnord (syn_cpw1 (syn_cpw1 A)))))
      (syn_wf1o (syn_csi (syn_csi (syn_chnsiquomap A)))
        (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_chnord A))))
        (syn_cpw1 (syn_cpw1 (syn_chnord (syn_cpw1 A)))))
      p0006 p0011
  have p0013 :=
    @g_f1oco (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_chnord A))))
      (syn_cpw1 (syn_cpw1 (syn_chnord (syn_cpw1 A))))
      (syn_cpw1 (syn_chnord (syn_cpw1 (syn_cpw1 A))))
      (syn_csi (syn_chnsiquomap (syn_cpw1 A))) (syn_csi (syn_csi (syn_chnsiquomap A)))
  have p0014 := Nominal.mp p0012 p0013
  have p0015 :=
    @g_pm3_2i
      (syn_wf1o (syn_chnsiquomap (syn_cpw1 (syn_cpw1 A)))
        (syn_cpw1 (syn_chnord (syn_cpw1 (syn_cpw1 A))))
        (syn_chnord (syn_cpw1 (syn_cpw1 (syn_cpw1 A)))))
      (syn_wf1o (syn_ccom (syn_csi (syn_chnsiquomap (syn_cpw1 A)))
          (syn_csi (syn_csi (syn_chnsiquomap A))))
        (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_chnord A))))
        (syn_cpw1 (syn_chnord (syn_cpw1 (syn_cpw1 A)))))
      p0002 p0014
  have p0016 :=
    @g_f1oco (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_chnord A))))
      (syn_cpw1 (syn_chnord (syn_cpw1 (syn_cpw1 A))))
      (syn_chnord (syn_cpw1 (syn_cpw1 (syn_cpw1 A))))
      (syn_chnsiquomap (syn_cpw1 (syn_cpw1 A)))
      (syn_ccom (syn_csi (syn_chnsiquomap (syn_cpw1 A)))
        (syn_csi (syn_csi (syn_chnsiquomap A))))
  have p0017 := Nominal.mp p0015 p0016
  exact p0017

@[expose]
noncomputable def g_hnqcommonprecoverinjndv (D : Class) (S : Class) (E : Class)
    (J : Class) (hyp_hnqcommonprecoverinjndv_1 : Nominal.NPrf (.classMem D (syn_cvv)))
    (hyp_hnqcommonprecoverinjndv_2 : Nominal.NPrf (.classMem E (syn_cvv)))
    (hyp_hnqcommonprecoverinjndv_3 : Nominal.NPrf (syn_wf1 J S (syn_chnord D))) :
    Nominal.NPrf
      (.imp (syn_wss (syn_cima (syn_ccom (syn_chnqinc D (syn_cun D E)) J) S)
          (syn_crn (syn_chnqinc E (syn_cun D E)))) (syn_wf1 (syn_cres
            (syn_ccom (syn_ccnv (syn_chnqinc E (syn_cun D E)))
              (syn_ccom (syn_chnqinc D (syn_cun D E)) J)) S) S (syn_chnord E))) :=
  by
  have p0000 := @g_ssun2 E D
  have p0001 := @g_unex D E hyp_hnqcommonprecoverinjndv_1 hyp_hnqcommonprecoverinjndv_2
  have p0002 := @g_hnqincf1 (syn_cun D E) E p0000 hyp_hnqcommonprecoverinjndv_2 p0001
  have p0003 :=
    @g_f1cnv (syn_chnord E) (syn_chnord (syn_cun D E)) (syn_chnqinc E (syn_cun D E))
  have p0004 := Nominal.mp p0002 p0003
  have p0005 :=
    @g_f1of1 (syn_crn (syn_chnqinc E (syn_cun D E))) (syn_chnord E)
      (syn_ccnv (syn_chnqinc E (syn_cun D E)))
  have p0006 := Nominal.mp p0004 p0005
  have p0007 :=
    @g_a1i
      (syn_wf1 (syn_ccnv (syn_chnqinc E (syn_cun D E)))
        (syn_crn (syn_chnqinc E (syn_cun D E))) (syn_chnord E))
      (syn_wss (syn_cima (syn_ccom (syn_chnqinc D (syn_cun D E)) J) S)
        (syn_crn (syn_chnqinc E (syn_cun D E))))
      p0006
  have p0008 := @g_ssun1 D E
  have p0010 := @g_hnqincf1 (syn_cun D E) D p0008 hyp_hnqcommonprecoverinjndv_1 p0001
  have p0011 :=
    @g_pm3_2i
      (syn_wf1 (syn_chnqinc D (syn_cun D E)) (syn_chnord D) (syn_chnord (syn_cun D E)))
      (syn_wf1 J S (syn_chnord D)) p0010 hyp_hnqcommonprecoverinjndv_3
  have p0012 :=
    @g_f1co S (syn_chnord D) (syn_chnord (syn_cun D E)) (syn_chnqinc D (syn_cun D E)) J
  have p0013 := Nominal.mp p0011 p0012
  have p0014 := @g_ssid S
  have p0015 :=
    @g_pm3_2i
      (syn_wf1 (syn_ccom (syn_chnqinc D (syn_cun D E)) J) S (syn_chnord (syn_cun D E)))
      (syn_wss S S) p0013 p0014
  have p0016 :=
    @g_f1ores S (syn_chnord (syn_cun D E)) S (syn_ccom (syn_chnqinc D (syn_cun D E)) J)
  have p0017 := Nominal.mp p0015 p0016
  have p0018 :=
    @g_f1of1 S (syn_cima (syn_ccom (syn_chnqinc D (syn_cun D E)) J) S)
      (syn_cres (syn_ccom (syn_chnqinc D (syn_cun D E)) J) S)
  have p0019 := Nominal.mp p0017 p0018
  have p0020 :=
    @g_a1i
      (syn_wf1 (syn_cres (syn_ccom (syn_chnqinc D (syn_cun D E)) J) S) S
        (syn_cima (syn_ccom (syn_chnqinc D (syn_cun D E)) J) S))
      (syn_wss (syn_cima (syn_ccom (syn_chnqinc D (syn_cun D E)) J) S)
        (syn_crn (syn_chnqinc E (syn_cun D E))))
      p0019
  have p0021 :=
    @g_id
      (syn_wss (syn_cima (syn_ccom (syn_chnqinc D (syn_cun D E)) J) S)
        (syn_crn (syn_chnqinc E (syn_cun D E))))
  have p0022 :=
    @g_jca
      (syn_wss (syn_cima (syn_ccom (syn_chnqinc D (syn_cun D E)) J) S)
        (syn_crn (syn_chnqinc E (syn_cun D E))))
      (syn_wf1 (syn_cres (syn_ccom (syn_chnqinc D (syn_cun D E)) J) S) S
        (syn_cima (syn_ccom (syn_chnqinc D (syn_cun D E)) J) S))
      (syn_wss (syn_cima (syn_ccom (syn_chnqinc D (syn_cun D E)) J) S)
        (syn_crn (syn_chnqinc E (syn_cun D E))))
      p0020 p0021
  have p0023 :=
    @g_f1ss S (syn_cima (syn_ccom (syn_chnqinc D (syn_cun D E)) J) S)
      (syn_crn (syn_chnqinc E (syn_cun D E)))
      (syn_cres (syn_ccom (syn_chnqinc D (syn_cun D E)) J) S)
  have p0024 :=
    @g_syl
      (syn_wss (syn_cima (syn_ccom (syn_chnqinc D (syn_cun D E)) J) S)
        (syn_crn (syn_chnqinc E (syn_cun D E))))
      (syn_wa (syn_wf1 (syn_cres (syn_ccom (syn_chnqinc D (syn_cun D E)) J) S) S
          (syn_cima (syn_ccom (syn_chnqinc D (syn_cun D E)) J) S))
        (syn_wss (syn_cima (syn_ccom (syn_chnqinc D (syn_cun D E)) J) S)
          (syn_crn (syn_chnqinc E (syn_cun D E)))))
      (syn_wf1 (syn_cres (syn_ccom (syn_chnqinc D (syn_cun D E)) J) S) S
        (syn_crn (syn_chnqinc E (syn_cun D E))))
      p0022 p0023
  have p0025 :=
    @g_jca
      (syn_wss (syn_cima (syn_ccom (syn_chnqinc D (syn_cun D E)) J) S)
        (syn_crn (syn_chnqinc E (syn_cun D E))))
      (syn_wf1 (syn_ccnv (syn_chnqinc E (syn_cun D E)))
        (syn_crn (syn_chnqinc E (syn_cun D E))) (syn_chnord E))
      (syn_wf1 (syn_cres (syn_ccom (syn_chnqinc D (syn_cun D E)) J) S) S
        (syn_crn (syn_chnqinc E (syn_cun D E))))
      p0007 p0024
  have p0026 :=
    @g_f1co S (syn_crn (syn_chnqinc E (syn_cun D E))) (syn_chnord E)
      (syn_ccnv (syn_chnqinc E (syn_cun D E)))
      (syn_cres (syn_ccom (syn_chnqinc D (syn_cun D E)) J) S)
  have p0027 :=
    @g_syl
      (syn_wss (syn_cima (syn_ccom (syn_chnqinc D (syn_cun D E)) J) S)
        (syn_crn (syn_chnqinc E (syn_cun D E))))
      (syn_wa (syn_wf1 (syn_ccnv (syn_chnqinc E (syn_cun D E)))
          (syn_crn (syn_chnqinc E (syn_cun D E))) (syn_chnord E))
        (syn_wf1 (syn_cres (syn_ccom (syn_chnqinc D (syn_cun D E)) J) S) S
          (syn_crn (syn_chnqinc E (syn_cun D E)))))
      (syn_wf1 (syn_ccom (syn_ccnv (syn_chnqinc E (syn_cun D E)))
          (syn_cres (syn_ccom (syn_chnqinc D (syn_cun D E)) J) S)) S (syn_chnord E))
      p0025 p0026
  have p0028 :=
    @g_resco (syn_ccnv (syn_chnqinc E (syn_cun D E)))
      (syn_ccom (syn_chnqinc D (syn_cun D E)) J) S
  have p0029 :=
    @g_f1eq1 S (syn_chnord E)
      (syn_cres (syn_ccom (syn_ccnv (syn_chnqinc E (syn_cun D E)))
          (syn_ccom (syn_chnqinc D (syn_cun D E)) J)) S)
      (syn_ccom (syn_ccnv (syn_chnqinc E (syn_cun D E)))
        (syn_cres (syn_ccom (syn_chnqinc D (syn_cun D E)) J) S))
  have p0030 := Nominal.mp p0028 p0029
  have p0031 :=
    @g_sylibr
      (syn_wss (syn_cima (syn_ccom (syn_chnqinc D (syn_cun D E)) J) S)
        (syn_crn (syn_chnqinc E (syn_cun D E))))
      (syn_wf1 (syn_ccom (syn_ccnv (syn_chnqinc E (syn_cun D E)))
          (syn_cres (syn_ccom (syn_chnqinc D (syn_cun D E)) J) S)) S (syn_chnord E))
      (syn_wf1 (syn_cres (syn_ccom (syn_ccnv (syn_chnqinc E (syn_cun D E)))
            (syn_ccom (syn_chnqinc D (syn_cun D E)) J)) S) S (syn_chnord E))
      p0027 p0030
  exact p0031


end NFChoice.DirectNominalPrf.WPPReplay

end

/-! Certificates from `NominalWPPReplayChunk017Compact001Part087`. -/


section

namespace NFChoice.DirectNominalPrf.WPPReplay

open scoped Fol
open NFChoice.Foundation
open NFChoice.SemanticCore
open NFChoice.ReplaySupport
open NFChoice.Compiler.CompactSourceSyntax

@[expose]
noncomputable def g_ncwehwcardsndv (D : Class) (R : Class) :
    Nominal.NPrf
      (.imp (syn_wbr R (syn_cwe) D) (.classMem (syn_cnc D) (syn_chwcards (syn_cvv)))) :=
  by
  let proofSupport : Finset Var := D.fv ∪ R.fv
  let s : Var := freshVar proofSupport 0
  let d : Var := freshVar proofSupport 1
  have fresh_s : s ∉ proofSupport :=
    by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_s_not_D : s ∉ D.fv := by
    intro h
    exact fresh_s (Finset.mem_union_left _ (h))
  have fresh_s_not_R : s ∉ R.fv := by
    intro h
    exact fresh_s (Finset.mem_union_right _ (h))
  have fresh_d : d ∉ proofSupport :=
    by
    change freshVar proofSupport 1 ∉ proofSupport
    exact freshVar_not_mem proofSupport 1
  have fresh_d_not_D : d ∉ D.fv := by
    intro h
    exact fresh_d (Finset.mem_union_left _ (h))
  have fresh_d_not_R : d ∉ R.fv := by
    intro h
    exact fresh_d (Finset.mem_union_right _ (h))
  have fresh_s_ne_d : s ≠ d :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have fresh_d_ne_s : d ≠ s := Ne.symm fresh_s_ne_d
  have dv_cache_0001 : d ∉ (D).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : d ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_d_not_D, not_false_eq_true])
  have dv_cache_0002 : s ∉ (D).fv :=
    by
    clear dv_cache_0001
    exact
      (by
        have compact_fv_not_mem_empty : s ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_s_not_D, not_false_eq_true])
  have dv_cache_0003 : d ∉ (R).fv :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact
      (by
        have compact_fv_not_mem_empty : d ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_d_not_R, not_false_eq_true])
  have dv_cache_0004 : s ∉ (R).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact
      (by
        have compact_fv_not_mem_empty : s ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_s_not_R, not_false_eq_true])
  have dv_cache_0005 : d ∉ ((syn_wbr R (syn_cwe) D)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact
      (by
        have compact_fv_not_mem_empty : d ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cwe, Finset.mem_union,
          fresh_d_not_R, fresh_d_not_D, compact_fv_not_mem_empty, or_false,
          not_false_eq_true])
  have dv_cache_0006 : s ∉ ((syn_wbr R (syn_cwe) D)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact
      (by
        have compact_fv_not_mem_empty : s ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cwe, Finset.mem_union,
          fresh_s_not_R, fresh_s_not_D, compact_fv_not_mem_empty, or_false,
          not_false_eq_true])
  have dv_cache_0007 : d ≠ s :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006
    exact (show d ≠ s from (by exact fresh_d_ne_s))
  have dv_cache_0008 : d ∉ ((syn_cnc D)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007
    exact
      (by
        have compact_fv_not_mem_empty : d ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnc, fresh_d_not_D,
          not_false_eq_true])
  have dv_cache_0009 : s ∉ ((syn_cnc D)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008
    exact
      (by
        have compact_fv_not_mem_empty : s ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnc, fresh_s_not_D,
          not_false_eq_true])
  have p0000 := @g_brex R D (syn_cwe)
  have p0001 :=
    @g_ancomd (syn_wbr R (syn_cwe) D) (.classMem R (syn_cvv)) (.classMem D (syn_cvv))
      p0000
  have p0002 := @g_simpl (.classEq (.cv d) D) (.classEq (.cv s) R)
  have p0003 :=
    @g_eqcomd (syn_wa (.classEq (.cv d) D) (.classEq (.cv s) R)) (.cv d) D p0002
  have p0004 :=
    @g_nceqd (syn_wa (.classEq (.cv d) D) (.classEq (.cv s) R)) D (.cv d) p0003
  have p0005 :=
    @g_biantrud (syn_wa (.classEq (.cv d) D) (.classEq (.cv s) R))
      (.classEq (syn_cnc D) (syn_cnc (.cv d))) (syn_wbr (.cv s) (syn_cwe) (.cv d)) p0004
  have p0006 :=
    @g_bicomd (syn_wa (.classEq (.cv d) D) (.classEq (.cv s) R))
      (syn_wbr (.cv s) (syn_cwe) (.cv d))
      (syn_wa (syn_wbr (.cv s) (syn_cwe) (.cv d)) (.classEq (syn_cnc D) (syn_cnc (.cv d))))
      p0005
  have p0007 := @g_simpr (.classEq (.cv d) D) (.classEq (.cv s) R)
  have p0009 :=
    @g_breq12d (syn_wa (.classEq (.cv d) D) (.classEq (.cv s) R)) (.cv s) R (.cv d) D
      (syn_cwe) p0007 p0002
  have p0010 :=
    @g_bitrd (syn_wa (.classEq (.cv d) D) (.classEq (.cv s) R))
      (syn_wa (syn_wbr (.cv s) (syn_cwe) (.cv d)) (.classEq (syn_cnc D) (syn_cnc (.cv d))))
      (syn_wbr (.cv s) (syn_cwe) (.cv d)) (syn_wbr R (syn_cwe) D) p0006 p0009
  have p0011 :=
    @g_spc2egv
      (syn_wa (syn_wbr (.cv s) (syn_cwe) (.cv d)) (.classEq (syn_cnc D) (syn_cnc (.cv d))))
      (syn_wbr R (syn_cwe) D) d s D R (syn_cvv) (syn_cvv) dv_cache_0001 dv_cache_0002
      dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 p0010
  have p0012 :=
    @g_syl (syn_wbr R (syn_cwe) D)
      (syn_wa (.classMem D (syn_cvv)) (.classMem R (syn_cvv)))
      (.imp (syn_wbr R (syn_cwe) D) (syn_wex d (syn_wex s
            (syn_wa (syn_wbr (.cv s) (syn_cwe) (.cv d))
              (.classEq (syn_cnc D) (syn_cnc (.cv d)))))))
      p0001 p0011
  have p0013 :=
    @g_pm2_43i (syn_wbr R (syn_cwe) D)
      (syn_wex d (syn_wex s (syn_wa (syn_wbr (.cv s) (syn_cwe) (.cv d))
            (.classEq (syn_cnc D) (syn_cnc (.cv d))))))
      p0012
  have p0014 := @g_ncex D
  have p0015 :=
    @g_elhwcardsweclndv (syn_cnc D) s d dv_cache_0008 dv_cache_0009 dv_cache_0007
  have p0016 := Nominal.mp p0014 p0015
  have p0017 :=
    @g_sylibr (syn_wbr R (syn_cwe) D)
      (syn_wex d (syn_wex s (syn_wa (syn_wbr (.cv s) (syn_cwe) (.cv d))
            (.classEq (syn_cnc D) (syn_cnc (.cv d))))))
      (.classMem (syn_cnc D) (syn_chwcards (syn_cvv))) p0013 p0016
  exact p0017

@[expose]
noncomputable def g_hnsiquomaprepvalcl3ndv (A : Class) (C : Class) (Q : Class)
    (hyp_hnsiquomaprepvalcl3ndv_1 : Nominal.NPrf (.classMem A (syn_cvv))) :
    Nominal.NPrf
      (.imp (syn_wa (.classMem Q (syn_cpw1 (syn_chnord A))) (syn_wa (.classMem C (syn_chwcn A))
            (.classEq (syn_cuni Q) (syn_cec C (syn_chwniso A)))))
        (.classEq (syn_cfv (syn_chnsiquomap A) Q)
          (syn_cec (syn_cfv (syn_chnsicodemap A) (syn_csn C)) (syn_chwniso (syn_cpw1 A))))) :=
  by
  let proofSupport : Finset Var := A.fv ∪ C.fv ∪ Q.fv
  let q : Var := freshVar proofSupport 0
  have fresh_q : q ∉ proofSupport :=
    by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_q_not_A : q ∉ A.fv := by
    intro h
    exact fresh_q (Finset.mem_union_left _ (Finset.mem_union_left _ (h)))
  have fresh_q_not_C : q ∉ C.fv := by
    intro h
    exact fresh_q (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_q_not_Q : q ∉ Q.fv := by
    intro h
    exact fresh_q (Finset.mem_union_right _ (h))
  have dv_cache_0001 : q ∉ (A).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : q ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_q_not_A, not_false_eq_true])
  have dv_cache_0002 : q ∉ (Q).fv :=
    by
    clear dv_cache_0001
    exact
      (by
        have compact_fv_not_mem_empty : q ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_q_not_Q, not_false_eq_true])
  have dv_cache_0003 :
    q ∉
      ((Wff.imp (syn_wa (.classMem Q (syn_cpw1 (syn_chnord A)))
            (syn_wa (.classMem C (syn_chwcn A))
              (.classEq (syn_cuni Q) (syn_cec C (syn_chwniso A)))))
          (.classEq (syn_cfv (syn_chnsiquomap A) Q)
            (syn_cec (syn_cfv (syn_chnsicodemap A) (syn_csn C))
              (syn_chwniso (syn_cpw1 A)))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact
      (by
        have compact_fv_not_mem_empty : q ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chnord,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwcn,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cuni,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cec,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwniso,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chnsiquomap,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chnsicodemap,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, Finset.mem_union,
          fresh_q_not_Q, fresh_q_not_A, fresh_q_not_C, or_false, not_false_eq_true])
  have p0000 :=
    @g_simpl (.classMem Q (syn_cpw1 (syn_chnord A)))
      (syn_wa (.classMem C (syn_chwcn A)) (.classEq (syn_cuni Q) (syn_cec C (syn_chwniso A))))
  have p0001 := @g_elex Q (syn_cpw1 (syn_chnord A))
  have p0002 :=
    @g_syl
      (syn_wa (.classMem Q (syn_cpw1 (syn_chnord A))) (syn_wa (.classMem C (syn_chwcn A))
          (.classEq (syn_cuni Q) (syn_cec C (syn_chwniso A)))))
      (.classMem Q (syn_cpw1 (syn_chnord A))) (.classMem Q (syn_cvv)) p0000 p0001
  have p0003 := @g_id (.classEq (.cv q) Q)
  have p0004 := @g_eleq1d (.classEq (.cv q) Q) (.cv q) Q (syn_cpw1 (syn_chnord A)) p0003
  have p0005 := @g_biid (.classMem C (syn_chwcn A))
  have p0006 :=
    @g_a1i (syn_wb (.classMem C (syn_chwcn A)) (.classMem C (syn_chwcn A)))
      (.classEq (.cv q) Q) p0005
  have p0008 := @g_unieqd (.classEq (.cv q) Q) (.cv q) Q p0003
  have p0009 :=
    @g_eqeq1d (.classEq (.cv q) Q) (syn_cuni (.cv q)) (syn_cuni Q)
      (syn_cec C (syn_chwniso A)) p0008
  have p0010 :=
    @g_anbi12d (.classEq (.cv q) Q) (.classMem C (syn_chwcn A))
      (.classMem C (syn_chwcn A))
      (.classEq (syn_cuni (.cv q)) (syn_cec C (syn_chwniso A)))
      (.classEq (syn_cuni Q) (syn_cec C (syn_chwniso A))) p0006 p0009
  have p0011 :=
    @g_anbi12d (.classEq (.cv q) Q) (.classMem (.cv q) (syn_cpw1 (syn_chnord A)))
      (.classMem Q (syn_cpw1 (syn_chnord A)))
      (syn_wa (.classMem C (syn_chwcn A))
        (.classEq (syn_cuni (.cv q)) (syn_cec C (syn_chwniso A))))
      (syn_wa (.classMem C (syn_chwcn A)) (.classEq (syn_cuni Q) (syn_cec C (syn_chwniso A))))
      p0004 p0010
  have p0013 := @g_fveq2d (.classEq (.cv q) Q) (.cv q) Q (syn_chnsiquomap A) p0003
  have p0014 :=
    @g_eqeq1d (.classEq (.cv q) Q) (syn_cfv (syn_chnsiquomap A) (.cv q))
      (syn_cfv (syn_chnsiquomap A) Q)
      (syn_cec (syn_cfv (syn_chnsicodemap A) (syn_csn C)) (syn_chwniso (syn_cpw1 A)))
      p0013
  have p0015 :=
    @g_imbi12d (.classEq (.cv q) Q)
      (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_chnord A))) (syn_wa (.classMem C (syn_chwcn A))
          (.classEq (syn_cuni (.cv q)) (syn_cec C (syn_chwniso A)))))
      (syn_wa (.classMem Q (syn_cpw1 (syn_chnord A))) (syn_wa (.classMem C (syn_chwcn A))
          (.classEq (syn_cuni Q) (syn_cec C (syn_chwniso A)))))
      (.classEq (syn_cfv (syn_chnsiquomap A) (.cv q))
        (syn_cec (syn_cfv (syn_chnsicodemap A) (syn_csn C)) (syn_chwniso (syn_cpw1 A))))
      (.classEq (syn_cfv (syn_chnsiquomap A) Q)
        (syn_cec (syn_cfv (syn_chnsicodemap A) (syn_csn C)) (syn_chwniso (syn_cpw1 A))))
      p0011 p0014
  have p0016 := @g_hnsiquomaprepvalcl2ndv A C q dv_cache_0001 hyp_hnsiquomaprepvalcl3ndv_1
  have p0017 :=
    @g_vtoclg
      (.imp (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_chnord A)))
          (syn_wa (.classMem C (syn_chwcn A))
            (.classEq (syn_cuni (.cv q)) (syn_cec C (syn_chwniso A)))))
        (.classEq (syn_cfv (syn_chnsiquomap A) (.cv q))
          (syn_cec (syn_cfv (syn_chnsicodemap A) (syn_csn C)) (syn_chwniso (syn_cpw1 A)))))
      (.imp (syn_wa (.classMem Q (syn_cpw1 (syn_chnord A))) (syn_wa (.classMem C (syn_chwcn A))
            (.classEq (syn_cuni Q) (syn_cec C (syn_chwniso A)))))
        (.classEq (syn_cfv (syn_chnsiquomap A) Q)
          (syn_cec (syn_cfv (syn_chnsicodemap A) (syn_csn C)) (syn_chwniso (syn_cpw1 A)))))
      q Q (syn_cvv) dv_cache_0002 dv_cache_0003 p0015 p0016
  have p0018 :=
    @g_syl
      (syn_wa (.classMem Q (syn_cpw1 (syn_chnord A))) (syn_wa (.classMem C (syn_chwcn A))
          (.classEq (syn_cuni Q) (syn_cec C (syn_chwniso A)))))
      (.classMem Q (syn_cvv))
      (.imp (syn_wa (.classMem Q (syn_cpw1 (syn_chnord A))) (syn_wa (.classMem C (syn_chwcn A))
            (.classEq (syn_cuni Q) (syn_cec C (syn_chwniso A)))))
        (.classEq (syn_cfv (syn_chnsiquomap A) Q)
          (syn_cec (syn_cfv (syn_chnsicodemap A) (syn_csn C)) (syn_chwniso (syn_cpw1 A)))))
      p0002 p0017
  have p0019 :=
    @g_pm2_43i
      (syn_wa (.classMem Q (syn_cpw1 (syn_chnord A))) (syn_wa (.classMem C (syn_chwcn A))
          (.classEq (syn_cuni Q) (syn_cec C (syn_chwniso A)))))
      (.classEq (syn_cfv (syn_chnsiquomap A) Q)
        (syn_cec (syn_cfv (syn_chnsicodemap A) (syn_csn C)) (syn_chwniso (syn_cpw1 A))))
      p0018
  exact p0019


end NFChoice.DirectNominalPrf.WPPReplay

end
