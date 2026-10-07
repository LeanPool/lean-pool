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

/-- Checked nominal proof certificate identified upstream as `g_hninjraisedselfcutcmpndv`. -/
@[expose]
noncomputable def gHninjraisedselfcutcmpndv (x : Var) (u : Var) (A : Class) (f : Var)
    (dv_A_f : f ∉ A.fv) (dv_A_u : u ∉ A.fv) (dv_A_x : x ∉ A.fv) (dv_f_u : f ≠ u)
    (dv_f_x : f ≠ x) (dv_u_x : u ≠ x)
    (hyp_hninjraisedselfcutcmpndv_1 : Nominal.NPrf (.classMem A (synCvv))) :
    Nominal.NPrf
      (.imp (synWf1 (.cv f) (synChnord A) (synCpw1 (synCpw1 A)))
        (synWrex u (synChwcn (synCpw1 (synCpw1 A))) (synWrex x (synCfv (synC2nd) (.cv u))
            (synWbr (.cv u) (synChwniso (synCpw1 (synCpw1 A)))
              (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u))
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
  have dv_cache_0001 : r ∉ ((synChncodecmpset A)).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : r ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chncodecmpset,
          fresh_r_not_A, not_false_eq_true])
  have dv_cache_0002 : Disjoint ((synChwcn A)).fv ((Class.cv r)).fv :=
    by
    clear dv_cache_0001
    exact
      (show Disjoint ((synChwcn A)).fv ((Class.cv r)).fv from (by
          rw [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwcn,
            NFChoice.Compiler.CoreFVSimp.fv_class_cv];
          exact
            (show Disjoint ((A).fv) (({ r } : Finset Var)) from
              (Finset.disjoint_singleton_right.mpr
                (show r ∉ (A).fv from (by exact fresh_r_not_A))))))
  have dv_cache_0003 : s ∉ ((synClnqord (.cv r) (synChwcn A))).fv :=
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
      ((synWrex u (synChwcn (synCpw1 (synCpw1 A))) (synWrex x (synCfv (synC2nd) (.cv u))
            (synWbr (.cv u) (synChwniso (synCpw1 (synCpw1 A)))
              (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u))
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
      ((synWa (synWf1 (.cv f) (synChnord A) (synCpw1 (synCpw1 A)))
          (.classEq (.cv r) (synChncodecmpset A)))).fv :=
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
      ((synWrex u (synChwcn (synCpw1 (synCpw1 A))) (synWrex x (synCfv (synC2nd) (.cv u))
            (synWbr (.cv u) (synChwniso (synCpw1 (synCpw1 A)))
              (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u))
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
    r ∉ ((synWf1 (.cv f) (synChnord A) (synCpw1 (synCpw1 A)))).fv :=
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
  have p0000 := @gHncodecmpsetexg A
  have p0001 := Nominal.mp hyp_hninjraisedselfcutcmpndv_1 p0000
  have p0002 := @gIsset r (synChncodecmpset A) dv_cache_0001
  have p0003 :=
    @gMpbi (.classMem (synChncodecmpset A) (synCvv))
      (synWex r (.classEq (.cv r) (synChncodecmpset A))) p0001 p0002
  have p0004 :=
    @gA1i (synWex r (.classEq (.cv r) (synChncodecmpset A)))
      (synWf1 (.cv f) (synChnord A) (synCpw1 (synCpw1 A))) p0003
  have p0007 :=
    @gA1i (.classMem (synChncodecmpset A) (synCvv))
      (synWa (synWf1 (.cv f) (synChnord A) (synCpw1 (synCpw1 A)))
        (.classEq (.cv r) (synChncodecmpset A)))
      p0001
  have p0008 :=
    @gSimpr (synWf1 (.cv f) (synChnord A) (synCpw1 (synCpw1 A)))
      (.classEq (.cv r) (synChncodecmpset A))
  have p0009 :=
    @gEleq1d
      (synWa (synWf1 (.cv f) (synChnord A) (synCpw1 (synCpw1 A)))
        (.classEq (.cv r) (synChncodecmpset A)))
      (.cv r) (synChncodecmpset A) (synCvv) p0008
  have p0010 :=
    @gMpbird
      (synWa (synWf1 (.cv f) (synChnord A) (synCpw1 (synCpw1 A)))
        (.classEq (.cv r) (synChncodecmpset A)))
      (.classMem (.cv r) (synCvv)) (.classMem (synChncodecmpset A) (synCvv)) p0007
      p0009
  have p0011 := @gHwcnex A hyp_hninjraisedselfcutcmpndv_1
  have p0012 :=
    @gA1i (.classMem (synChwcn A) (synCvv))
      (synWa (synWf1 (.cv f) (synChnord A) (synCpw1 (synCpw1 A)))
        (.classEq (.cv r) (synChncodecmpset A)))
      p0011
  have p0013 :=
    @gJca
      (synWa (synWf1 (.cv f) (synChnord A) (synCpw1 (synCpw1 A)))
        (.classEq (.cv r) (synChncodecmpset A)))
      (.classMem (.cv r) (synCvv)) (.classMem (synChwcn A) (synCvv)) p0010 p0012
  have p0014 := @gLnqordexg (synChwcn A) (.cv r) dv_cache_0002
  have p0015 :=
    @gSyl
      (synWa (synWf1 (.cv f) (synChnord A) (synCpw1 (synCpw1 A)))
        (.classEq (.cv r) (synChncodecmpset A)))
      (synWa (.classMem (.cv r) (synCvv)) (.classMem (synChwcn A) (synCvv)))
      (.classMem (synClnqord (.cv r) (synChwcn A)) (synCvv)) p0013 p0014
  have p0016 := @gIsset s (synClnqord (.cv r) (synChwcn A)) dv_cache_0003
  have p0017 :=
    @gA1i
      (synWb (.classMem (synClnqord (.cv r) (synChwcn A)) (synCvv))
        (synWex s (.classEq (.cv s) (synClnqord (.cv r) (synChwcn A)))))
      (synWa (synWf1 (.cv f) (synChnord A) (synCpw1 (synCpw1 A)))
        (.classEq (.cv r) (synChncodecmpset A)))
      p0016
  have p0018 :=
    @gMpbid
      (synWa (synWf1 (.cv f) (synChnord A) (synCpw1 (synCpw1 A)))
        (.classEq (.cv r) (synChncodecmpset A)))
      (.classMem (synClnqord (.cv r) (synChwcn A)) (synCvv))
      (synWex s (.classEq (.cv s) (synClnqord (.cv r) (synChwcn A)))) p0015 p0017
  have p0019 :=
    @gHninjraisedselfcutalldndv x u A f s r dv_cache_0004 dv_cache_0005 dv_cache_0006
      dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012
      dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018
      hyp_hninjraisedselfcutcmpndv_1
  have p0020 :=
    @gAnassrs (synWf1 (.cv f) (synChnord A) (synCpw1 (synCpw1 A)))
      (.classEq (.cv r) (synChncodecmpset A))
      (.classEq (.cv s) (synClnqord (.cv r) (synChwcn A)))
      (synWrex u (synChwcn (synCpw1 (synCpw1 A))) (synWrex x (synCfv (synC2nd) (.cv u))
          (synWbr (.cv u) (synChwniso (synCpw1 (synCpw1 A)))
            (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u))
              (.cv x)))))
      p0019
  have p0021 :=
    @gExlimddv
      (synWa (synWf1 (.cv f) (synChnord A) (synCpw1 (synCpw1 A)))
        (.classEq (.cv r) (synChncodecmpset A)))
      (.classEq (.cv s) (synClnqord (.cv r) (synChwcn A)))
      (synWrex u (synChwcn (synCpw1 (synCpw1 A))) (synWrex x (synCfv (synC2nd) (.cv u))
          (synWbr (.cv u) (synChwniso (synCpw1 (synCpw1 A)))
            (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u))
              (.cv x)))))
      s dv_cache_0019 dv_cache_0020 p0018 p0020
  have p0022 :=
    @gExlimddv (synWf1 (.cv f) (synChnord A) (synCpw1 (synCpw1 A)))
      (.classEq (.cv r) (synChncodecmpset A))
      (synWrex u (synChwcn (synCpw1 (synCpw1 A))) (synWrex x (synCfv (synC2nd) (.cv u))
          (synWbr (.cv u) (synChwniso (synCpw1 (synCpw1 A)))
            (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u))
              (.cv x)))))
      r dv_cache_0021 dv_cache_0022 p0004 p0021
  exact p0022

/-- Checked nominal proof certificate identified upstream as `g_hnselfcutnoex2ndv`. -/
@[expose]
noncomputable def gHnselfcutnoex2ndv (x : Var) (u : Var) (A : Class) (dv_A_u : u ∉ A.fv)
    (dv_A_x : x ∉ A.fv) (dv_u_x : u ≠ x) :
    Nominal.NPrf
      (.neg (synWrex u (synChwcn A) (synWrex x (synCfv (synC2nd) (.cv u))
            (synWbr (.cv u) (synChwniso A)
              (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u))
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
  have dv_cache_0002 : x ∉ ((Wff.classMem (.cv u) (synChwcn A))).fv :=
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
  have p0000 := @gHnwcutcodeselfnoisondv x u A dv_cache_0001
  have p0001 :=
    @gNrexdv (.classMem (.cv u) (synChwcn A))
      (synWbr (.cv u) (synChwniso A)
        (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u)) (.cv x)))
      x (synCfv (synC2nd) (.cv u)) dv_cache_0002 p0000
  have p0002 :=
    @gNrex
      (synWrex x (synCfv (synC2nd) (.cv u)) (synWbr (.cv u) (synChwniso A)
          (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u)) (.cv x))))
      u (synChwcn A) p0001
  exact p0002

/-- Checked nominal proof certificate identified upstream as `g_hncardtc2nodomndv`. -/
@[expose]
noncomputable def gHncardtc2nodomndv (A : Class)
    (hyp_hncardtc2nodomndv_1 : Nominal.NPrf (.classMem A (synCvv))) :
    Nominal.NPrf
      (.neg (synWbr (synChncard A) (synClec) (synCtc (synCtc (synCnc A))))) :=
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
  have dv_cache_0001 : u ∉ ((synCpw1 (synCpw1 A))).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : u ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1, fresh_u_not_A,
          not_false_eq_true])
  have dv_cache_0002 : x ∉ ((synCpw1 (synCpw1 A))).fv :=
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
  have dv_cache_0009 : f ∉ ((synChnord A)).fv :=
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
  have dv_cache_0010 : f ∉ ((synCpw1 (synCpw1 A))).fv :=
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
    @gHnselfcutnoex2ndv x u (synCpw1 (synCpw1 A)) dv_cache_0001 dv_cache_0002
      dv_cache_0003
  have p0001 :=
    @gHninjraisedselfcutcmpndv x u A f dv_cache_0004 dv_cache_0005 dv_cache_0006
      dv_cache_0007 dv_cache_0008 dv_cache_0003 hyp_hncardtc2nodomndv_1
  have p0002 :=
    @gCon3i (synWf1 (.cv f) (synChnord A) (synCpw1 (synCpw1 A)))
      (synWrex u (synChwcn (synCpw1 (synCpw1 A))) (synWrex x (synCfv (synC2nd) (.cv u))
          (synWbr (.cv u) (synChwniso (synCpw1 (synCpw1 A)))
            (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u))
              (.cv x)))))
      p0001
  have p0003 := Nominal.mp p0000 p0002
  have p0004 := @gNex (synWf1 (.cv f) (synChnord A) (synCpw1 (synCpw1 A))) f p0003
  have p0005 := @gHnordex A hyp_hncardtc2nodomndv_1
  have p0006 := @gPw1ex A hyp_hncardtc2nodomndv_1
  have p0007 := @gPw1ex (synCpw1 A) p0006
  have p0008 :=
    @gNclenc (synChnord A) (synCpw1 (synCpw1 A)) f dv_cache_0009 dv_cache_0010 p0005
      p0007
  have p0009 :=
    @gNotbii
      (synWbr (synCnc (synChnord A)) (synClec) (synCnc (synCpw1 (synCpw1 A))))
      (synWex f (synWf1 (.cv f) (synChnord A) (synCpw1 (synCpw1 A)))) p0008
  have p0010 :=
    @gMpbir
      (.neg (synWbr (synCnc (synChnord A)) (synClec) (synCnc (synCpw1 (synCpw1 A)))))
      (.neg (synWex f (synWf1 (.cv f) (synChnord A) (synCpw1 (synCpw1 A))))) p0004
      p0009
  have p0011 := (Nominal.classEqRefl (synChncard A))
  have p0012 := @gTc2nc A hyp_hncardtc2nodomndv_1
  have p0013 :=
    @gBreq12i (synChncard A) (synCnc (synChnord A)) (synCtc (synCtc (synCnc A)))
      (synCnc (synCpw1 (synCpw1 A))) (synClec) p0011 p0012
  have p0014 :=
    @gNotbii (synWbr (synChncard A) (synClec) (synCtc (synCtc (synCnc A))))
      (synWbr (synCnc (synChnord A)) (synClec) (synCnc (synCpw1 (synCpw1 A))))
      p0013
  have p0015 :=
    @gMpbir (.neg (synWbr (synChncard A) (synClec) (synCtc (synCtc (synCnc A)))))
      (.neg (synWbr (synCnc (synChnord A)) (synClec) (synCnc (synCpw1 (synCpw1 A)))))
      p0010 p0014
  exact p0015

/-- Checked nominal proof certificate identified upstream as `g_wppconcrete6representedmonondv`. -/
@[expose]
noncomputable def gWppconcrete6representedmonondv (X : Class) (Y : Class)
    (hyp_wppconcrete6representedmonondv_1 : Nominal.NPrf (.classMem X (synCvv)))
    (hyp_wppconcrete6representedmonondv_2 : Nominal.NPrf (.classMem Y (synCvv))) :
    Nominal.NPrf
      (.imp (synWbr (synCtc (synCtc (synCtc (synCtc (synCtc (synCtc (synCnc X)))))))
          (synClec) (synCtc (synCtc (synCtc (synCtc (synCtc (synCtc (synCnc Y))))))))
        (synWbr (synCfv (synCwppconcrete6fn)
            (synCtc (synCtc (synCtc (synCtc (synCtc (synCtc (synCnc X)))))))) (synClec)
          (synCfv (synCwppconcrete6fn)
            (synCtc (synCtc (synCtc (synCtc (synCtc (synCtc (synCnc Y)))))))))) :=
  by
  have p0000 := @gNcelncsi X hyp_wppconcrete6representedmonondv_1
  have p0001 := @gNcelncsi Y hyp_wppconcrete6representedmonondv_2
  have p0002 := @gTc6lecan (synCnc X) (synCnc Y) p0000 p0001
  have p0003 :=
    @gNcpw2le X Y hyp_wppconcrete6representedmonondv_1
      hyp_wppconcrete6representedmonondv_2
  have p0004 :=
    @gSyl
      (synWbr (synCtc (synCtc (synCtc (synCtc (synCtc (synCtc (synCnc X)))))))
        (synClec) (synCtc (synCtc (synCtc (synCtc (synCtc (synCtc (synCnc Y))))))))
      (synWbr (synCnc X) (synClec) (synCnc Y))
      (synWbr (synCnc (synCpw (synCpw X))) (synClec) (synCnc (synCpw (synCpw Y))))
      p0002 p0003
  have p0005 := @gPwex X hyp_wppconcrete6representedmonondv_1
  have p0006 := @gPwex (synCpw X) p0005
  have p0007 := @gPwex Y hyp_wppconcrete6representedmonondv_2
  have p0008 := @gPwex (synCpw Y) p0007
  have p0009 :=
    @gHnordcardnclecndv (synCpw (synCpw Y)) (synCpw (synCpw X)) p0006 p0008
  have p0010 :=
    @gSyl
      (synWbr (synCtc (synCtc (synCtc (synCtc (synCtc (synCtc (synCnc X)))))))
        (synClec) (synCtc (synCtc (synCtc (synCtc (synCtc (synCtc (synCnc Y))))))))
      (synWbr (synCnc (synCpw (synCpw X))) (synClec) (synCnc (synCpw (synCpw Y))))
      (synWbr (synCnc (synChnord (synCpw (synCpw X)))) (synClec)
        (synCnc (synChnord (synCpw (synCpw Y)))))
      p0004 p0009
  have p0013 := @gHnordex (synCpw (synCpw X)) p0006
  have p0016 := @gHnordex (synCpw (synCpw Y)) p0008
  have p0017 :=
    @gHncardnclecndv (synChnord (synCpw (synCpw Y)))
      (synChnord (synCpw (synCpw X))) p0013 p0016
  have p0018 :=
    @gSyl
      (synWbr (synCtc (synCtc (synCtc (synCtc (synCtc (synCtc (synCnc X)))))))
        (synClec) (synCtc (synCtc (synCtc (synCtc (synCtc (synCtc (synCnc Y))))))))
      (synWbr (synCnc (synChnord (synCpw (synCpw X)))) (synClec)
        (synCnc (synChnord (synCpw (synCpw Y)))))
      (synWbr (synChncard (synChnord (synCpw (synCpw X)))) (synClec)
        (synChncard (synChnord (synCpw (synCpw Y)))))
      p0010 p0017
  have p0019 := @gWppconcrete6fnvalndv X hyp_wppconcrete6representedmonondv_1
  have p0020 := @gWppconcrete6fnvalndv Y hyp_wppconcrete6representedmonondv_2
  have p0021 :=
    @gBreq12i
      (synCfv (synCwppconcrete6fn)
        (synCtc (synCtc (synCtc (synCtc (synCtc (synCtc (synCnc X))))))))
      (synChncard (synChnord (synCpw (synCpw X))))
      (synCfv (synCwppconcrete6fn)
        (synCtc (synCtc (synCtc (synCtc (synCtc (synCtc (synCnc Y))))))))
      (synChncard (synChnord (synCpw (synCpw Y)))) (synClec) p0019 p0020
  have p0022 :=
    @gBiimpri
      (synWbr (synCfv (synCwppconcrete6fn)
          (synCtc (synCtc (synCtc (synCtc (synCtc (synCtc (synCnc X)))))))) (synClec)
        (synCfv (synCwppconcrete6fn)
          (synCtc (synCtc (synCtc (synCtc (synCtc (synCtc (synCnc Y)))))))))
      (synWbr (synChncard (synChnord (synCpw (synCpw X)))) (synClec)
        (synChncard (synChnord (synCpw (synCpw Y)))))
      p0021
  have p0023 :=
    @gSyl
      (synWbr (synCtc (synCtc (synCtc (synCtc (synCtc (synCtc (synCnc X)))))))
        (synClec) (synCtc (synCtc (synCtc (synCtc (synCtc (synCtc (synCnc Y))))))))
      (synWbr (synChncard (synChnord (synCpw (synCpw X)))) (synClec)
        (synChncard (synChnord (synCpw (synCpw Y)))))
      (synWbr (synCfv (synCwppconcrete6fn)
          (synCtc (synCtc (synCtc (synCtc (synCtc (synCtc (synCnc X)))))))) (synClec)
        (synCfv (synCwppconcrete6fn)
          (synCtc (synCtc (synCtc (synCtc (synCtc (synCtc (synCnc Y)))))))))
      p0018 p0022
  exact p0023

/-- Checked nominal proof certificate identified upstream as `g_letc6ncrepdv`. -/
@[expose]
noncomputable def gLetc6ncrepdv (z : Var) (M : Class) (N : Class) (dv_M_z : z ∉ M.fv)
    (dv_N_z : z ∉ N.fv) :
    Nominal.NPrf
      (.imp (synW3a (.classMem M (synCncs)) (.classMem N (synCncs)) (synWbr M (synClec)
            (synCtc (synCtc (synCtc (synCtc (synCtc (synCtc N)))))))) (synWex z
          (.classEq M (synCtc
              (synCtc (synCtc (synCtc (synCtc (synCtc (synCnc (.cv z))))))))))) :=
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
      ((synWa (synWa (synW3a (.classMem M (synCncs)) (.classMem N (synCncs))
              (synWbr M (synClec)
                (synCtc (synCtc (synCtc (synCtc (synCtc (synCtc N))))))))
            (.classMem (.cv p) (synCncs))) (.classEq M
            (synCtc (synCtc (synCtc (synCtc (synCtc (synCtc (.cv p)))))))))).fv :=
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
      ((synWex z (.classEq M (synCtc (synCtc
                (synCtc (synCtc (synCtc (synCtc (synCnc (.cv z))))))))))).fv :=
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
      ((synW3a (.classMem M (synCncs)) (.classMem N (synCncs)) (synWbr M (synClec)
            (synCtc (synCtc (synCtc (synCtc (synCtc (synCtc N))))))))).fv :=
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
  have p0000 := @gLetc6w6ndv M N p dv_cache_0001 dv_cache_0002
  have p0001 :=
    @gSimpl
      (synWa (synW3a (.classMem M (synCncs)) (.classMem N (synCncs)) (synWbr M (synClec)
            (synCtc (synCtc (synCtc (synCtc (synCtc (synCtc N))))))))
        (.classMem (.cv p) (synCncs)))
      (.classEq M (synCtc (synCtc (synCtc (synCtc (synCtc (synCtc (.cv p))))))))
  have p0002 :=
    @gSimpr
      (synW3a (.classMem M (synCncs)) (.classMem N (synCncs)) (synWbr M (synClec)
          (synCtc (synCtc (synCtc (synCtc (synCtc (synCtc N))))))))
      (.classMem (.cv p) (synCncs))
  have p0003 :=
    @gSyl
      (synWa (synWa (synW3a (.classMem M (synCncs)) (.classMem N (synCncs))
            (synWbr M (synClec)
              (synCtc (synCtc (synCtc (synCtc (synCtc (synCtc N))))))))
          (.classMem (.cv p) (synCncs)))
        (.classEq M (synCtc (synCtc (synCtc (synCtc (synCtc (synCtc (.cv p)))))))))
      (synWa (synW3a (.classMem M (synCncs)) (.classMem N (synCncs)) (synWbr M (synClec)
            (synCtc (synCtc (synCtc (synCtc (synCtc (synCtc N))))))))
        (.classMem (.cv p) (synCncs)))
      (.classMem (.cv p) (synCncs)) p0001 p0002
  have p0004 := @gElncs z (.cv p) dv_cache_0003
  have p0005 :=
    @gBiimpi (.classMem (.cv p) (synCncs))
      (synWex z (.classEq (.cv p) (synCnc (.cv z)))) p0004
  have p0006 :=
    @gSyl
      (synWa (synWa (synW3a (.classMem M (synCncs)) (.classMem N (synCncs))
            (synWbr M (synClec)
              (synCtc (synCtc (synCtc (synCtc (synCtc (synCtc N))))))))
          (.classMem (.cv p) (synCncs)))
        (.classEq M (synCtc (synCtc (synCtc (synCtc (synCtc (synCtc (.cv p)))))))))
      (.classMem (.cv p) (synCncs)) (synWex z (.classEq (.cv p) (synCnc (.cv z))))
      p0003 p0005
  have p0007 :=
    @gSimpl
      (synWa (synWa (synW3a (.classMem M (synCncs)) (.classMem N (synCncs))
            (synWbr M (synClec)
              (synCtc (synCtc (synCtc (synCtc (synCtc (synCtc N))))))))
          (.classMem (.cv p) (synCncs)))
        (.classEq M (synCtc (synCtc (synCtc (synCtc (synCtc (synCtc (.cv p)))))))))
      (.classEq (.cv p) (synCnc (.cv z)))
  have p0008 :=
    @gSimpr
      (synWa (synW3a (.classMem M (synCncs)) (.classMem N (synCncs)) (synWbr M (synClec)
            (synCtc (synCtc (synCtc (synCtc (synCtc (synCtc N))))))))
        (.classMem (.cv p) (synCncs)))
      (.classEq M (synCtc (synCtc (synCtc (synCtc (synCtc (synCtc (.cv p))))))))
  have p0009 :=
    @gSyl
      (synWa (synWa (synWa (synW3a (.classMem M (synCncs)) (.classMem N (synCncs))
              (synWbr M (synClec)
                (synCtc (synCtc (synCtc (synCtc (synCtc (synCtc N))))))))
            (.classMem (.cv p) (synCncs))) (.classEq M
            (synCtc (synCtc (synCtc (synCtc (synCtc (synCtc (.cv p)))))))))
        (.classEq (.cv p) (synCnc (.cv z))))
      (synWa (synWa (synW3a (.classMem M (synCncs)) (.classMem N (synCncs))
            (synWbr M (synClec)
              (synCtc (synCtc (synCtc (synCtc (synCtc (synCtc N))))))))
          (.classMem (.cv p) (synCncs)))
        (.classEq M (synCtc (synCtc (synCtc (synCtc (synCtc (synCtc (.cv p)))))))))
      (.classEq M (synCtc (synCtc (synCtc (synCtc (synCtc (synCtc (.cv p))))))))
      p0007 p0008
  have p0010 :=
    @gSimpr
      (synWa (synWa (synW3a (.classMem M (synCncs)) (.classMem N (synCncs))
            (synWbr M (synClec)
              (synCtc (synCtc (synCtc (synCtc (synCtc (synCtc N))))))))
          (.classMem (.cv p) (synCncs)))
        (.classEq M (synCtc (synCtc (synCtc (synCtc (synCtc (synCtc (.cv p)))))))))
      (.classEq (.cv p) (synCnc (.cv z)))
  have p0011 := @gTceq (.cv p) (synCnc (.cv z))
  have p0012 :=
    @gSyl
      (synWa (synWa (synWa (synW3a (.classMem M (synCncs)) (.classMem N (synCncs))
              (synWbr M (synClec)
                (synCtc (synCtc (synCtc (synCtc (synCtc (synCtc N))))))))
            (.classMem (.cv p) (synCncs))) (.classEq M
            (synCtc (synCtc (synCtc (synCtc (synCtc (synCtc (.cv p)))))))))
        (.classEq (.cv p) (synCnc (.cv z))))
      (.classEq (.cv p) (synCnc (.cv z)))
      (.classEq (synCtc (.cv p)) (synCtc (synCnc (.cv z)))) p0010 p0011
  have p0013 := @gTceq (synCtc (.cv p)) (synCtc (synCnc (.cv z)))
  have p0014 :=
    @gSyl
      (synWa (synWa (synWa (synW3a (.classMem M (synCncs)) (.classMem N (synCncs))
              (synWbr M (synClec)
                (synCtc (synCtc (synCtc (synCtc (synCtc (synCtc N))))))))
            (.classMem (.cv p) (synCncs))) (.classEq M
            (synCtc (synCtc (synCtc (synCtc (synCtc (synCtc (.cv p)))))))))
        (.classEq (.cv p) (synCnc (.cv z))))
      (.classEq (synCtc (.cv p)) (synCtc (synCnc (.cv z))))
      (.classEq (synCtc (synCtc (.cv p))) (synCtc (synCtc (synCnc (.cv z))))) p0012
      p0013
  have p0015 := @gTceq (synCtc (synCtc (.cv p))) (synCtc (synCtc (synCnc (.cv z))))
  have p0016 :=
    @gSyl
      (synWa (synWa (synWa (synW3a (.classMem M (synCncs)) (.classMem N (synCncs))
              (synWbr M (synClec)
                (synCtc (synCtc (synCtc (synCtc (synCtc (synCtc N))))))))
            (.classMem (.cv p) (synCncs))) (.classEq M
            (synCtc (synCtc (synCtc (synCtc (synCtc (synCtc (.cv p)))))))))
        (.classEq (.cv p) (synCnc (.cv z))))
      (.classEq (synCtc (synCtc (.cv p))) (synCtc (synCtc (synCnc (.cv z)))))
      (.classEq (synCtc (synCtc (synCtc (.cv p))))
        (synCtc (synCtc (synCtc (synCnc (.cv z))))))
      p0014 p0015
  have p0017 :=
    @gTceq (synCtc (synCtc (synCtc (.cv p))))
      (synCtc (synCtc (synCtc (synCnc (.cv z)))))
  have p0018 :=
    @gSyl
      (synWa (synWa (synWa (synW3a (.classMem M (synCncs)) (.classMem N (synCncs))
              (synWbr M (synClec)
                (synCtc (synCtc (synCtc (synCtc (synCtc (synCtc N))))))))
            (.classMem (.cv p) (synCncs))) (.classEq M
            (synCtc (synCtc (synCtc (synCtc (synCtc (synCtc (.cv p)))))))))
        (.classEq (.cv p) (synCnc (.cv z))))
      (.classEq (synCtc (synCtc (synCtc (.cv p))))
        (synCtc (synCtc (synCtc (synCnc (.cv z))))))
      (.classEq (synCtc (synCtc (synCtc (synCtc (.cv p)))))
        (synCtc (synCtc (synCtc (synCtc (synCnc (.cv z)))))))
      p0016 p0017
  have p0019 :=
    @gTceq (synCtc (synCtc (synCtc (synCtc (.cv p)))))
      (synCtc (synCtc (synCtc (synCtc (synCnc (.cv z))))))
  have p0020 :=
    @gSyl
      (synWa (synWa (synWa (synW3a (.classMem M (synCncs)) (.classMem N (synCncs))
              (synWbr M (synClec)
                (synCtc (synCtc (synCtc (synCtc (synCtc (synCtc N))))))))
            (.classMem (.cv p) (synCncs))) (.classEq M
            (synCtc (synCtc (synCtc (synCtc (synCtc (synCtc (.cv p)))))))))
        (.classEq (.cv p) (synCnc (.cv z))))
      (.classEq (synCtc (synCtc (synCtc (synCtc (.cv p)))))
        (synCtc (synCtc (synCtc (synCtc (synCnc (.cv z)))))))
      (.classEq (synCtc (synCtc (synCtc (synCtc (synCtc (.cv p))))))
        (synCtc (synCtc (synCtc (synCtc (synCtc (synCnc (.cv z))))))))
      p0018 p0019
  have p0021 :=
    @gTceq (synCtc (synCtc (synCtc (synCtc (synCtc (.cv p))))))
      (synCtc (synCtc (synCtc (synCtc (synCtc (synCnc (.cv z)))))))
  have p0022 :=
    @gSyl
      (synWa (synWa (synWa (synW3a (.classMem M (synCncs)) (.classMem N (synCncs))
              (synWbr M (synClec)
                (synCtc (synCtc (synCtc (synCtc (synCtc (synCtc N))))))))
            (.classMem (.cv p) (synCncs))) (.classEq M
            (synCtc (synCtc (synCtc (synCtc (synCtc (synCtc (.cv p)))))))))
        (.classEq (.cv p) (synCnc (.cv z))))
      (.classEq (synCtc (synCtc (synCtc (synCtc (synCtc (.cv p))))))
        (synCtc (synCtc (synCtc (synCtc (synCtc (synCnc (.cv z))))))))
      (.classEq (synCtc (synCtc (synCtc (synCtc (synCtc (synCtc (.cv p)))))))
        (synCtc (synCtc (synCtc (synCtc (synCtc (synCtc (synCnc (.cv z)))))))))
      p0020 p0021
  have p0023 :=
    @gEqtrd
      (synWa (synWa (synWa (synW3a (.classMem M (synCncs)) (.classMem N (synCncs))
              (synWbr M (synClec)
                (synCtc (synCtc (synCtc (synCtc (synCtc (synCtc N))))))))
            (.classMem (.cv p) (synCncs))) (.classEq M
            (synCtc (synCtc (synCtc (synCtc (synCtc (synCtc (.cv p)))))))))
        (.classEq (.cv p) (synCnc (.cv z))))
      M (synCtc (synCtc (synCtc (synCtc (synCtc (synCtc (.cv p)))))))
      (synCtc (synCtc (synCtc (synCtc (synCtc (synCtc (synCnc (.cv z)))))))) p0009
      p0022
  have p0024 :=
    @gEx
      (synWa (synWa (synW3a (.classMem M (synCncs)) (.classMem N (synCncs))
            (synWbr M (synClec)
              (synCtc (synCtc (synCtc (synCtc (synCtc (synCtc N))))))))
          (.classMem (.cv p) (synCncs)))
        (.classEq M (synCtc (synCtc (synCtc (synCtc (synCtc (synCtc (.cv p)))))))))
      (.classEq (.cv p) (synCnc (.cv z)))
      (.classEq M (synCtc (synCtc (synCtc (synCtc (synCtc (synCtc (synCnc (.cv z)))))))))
      p0023
  have p0025 :=
    @gEximdv
      (synWa (synWa (synW3a (.classMem M (synCncs)) (.classMem N (synCncs))
            (synWbr M (synClec)
              (synCtc (synCtc (synCtc (synCtc (synCtc (synCtc N))))))))
          (.classMem (.cv p) (synCncs)))
        (.classEq M (synCtc (synCtc (synCtc (synCtc (synCtc (synCtc (.cv p)))))))))
      (.classEq (.cv p) (synCnc (.cv z)))
      (.classEq M (synCtc (synCtc (synCtc (synCtc (synCtc (synCtc (synCnc (.cv z)))))))))
      z dv_cache_0004 p0024
  have p0026 :=
    @gMpd
      (synWa (synWa (synW3a (.classMem M (synCncs)) (.classMem N (synCncs))
            (synWbr M (synClec)
              (synCtc (synCtc (synCtc (synCtc (synCtc (synCtc N))))))))
          (.classMem (.cv p) (synCncs)))
        (.classEq M (synCtc (synCtc (synCtc (synCtc (synCtc (synCtc (.cv p)))))))))
      (synWex z (.classEq (.cv p) (synCnc (.cv z))))
      (synWex z (.classEq M
          (synCtc (synCtc (synCtc (synCtc (synCtc (synCtc (synCnc (.cv z))))))))))
      p0006 p0025
  have p0027 :=
    @gEx
      (synWa (synW3a (.classMem M (synCncs)) (.classMem N (synCncs)) (synWbr M (synClec)
            (synCtc (synCtc (synCtc (synCtc (synCtc (synCtc N))))))))
        (.classMem (.cv p) (synCncs)))
      (.classEq M (synCtc (synCtc (synCtc (synCtc (synCtc (synCtc (.cv p))))))))
      (synWex z (.classEq M
          (synCtc (synCtc (synCtc (synCtc (synCtc (synCtc (synCnc (.cv z))))))))))
      p0026
  have p0028 :=
    @gRexlimdva
      (synW3a (.classMem M (synCncs)) (.classMem N (synCncs)) (synWbr M (synClec)
          (synCtc (synCtc (synCtc (synCtc (synCtc (synCtc N))))))))
      (.classEq M (synCtc (synCtc (synCtc (synCtc (synCtc (synCtc (.cv p))))))))
      (synWex z (.classEq M
          (synCtc (synCtc (synCtc (synCtc (synCtc (synCtc (synCnc (.cv z))))))))))
      p (synCncs) dv_cache_0005 dv_cache_0006 p0027
  have p0029 :=
    @gMpd
      (synW3a (.classMem M (synCncs)) (.classMem N (synCncs)) (synWbr M (synClec)
          (synCtc (synCtc (synCtc (synCtc (synCtc (synCtc N))))))))
      (synWrex p (synCncs)
        (.classEq M (synCtc (synCtc (synCtc (synCtc (synCtc (synCtc (.cv p)))))))))
      (synWex z (.classEq M
          (synCtc (synCtc (synCtc (synCtc (synCtc (synCtc (synCnc (.cv z))))))))))
      p0000 p0028
  exact p0029

/-- Checked nominal proof certificate identified upstream as `g_wppconcrete6tcvalncndv`. -/
@[expose]
noncomputable def gWppconcrete6tcvalncndv :
    Nominal.NPrf
      (.classMem (synCfv (synCwppconcrete6fn) (synCtc (synCtc
              (synCtc (synCtc (synCtc (synCtc (synCtc (synChncard (synC1c))))))))))
        (synCncs)) :=
  by
  have p0000 := (Nominal.classEqRefl (synChncard (synC1c)))
  have p0001 := @gTceq (synChncard (synC1c)) (synCnc (synChnord (synC1c)))
  have p0002 := Nominal.mp p0000 p0001
  have p0003 := @gN1cex
  have p0004 := @gHnordex (synC1c) p0003
  have p0005 := @gTcnc (synChnord (synC1c)) p0004
  have p0006 :=
    @gEqtri (synCtc (synChncard (synC1c))) (synCtc (synCnc (synChnord (synC1c))))
      (synCnc (synCpw1 (synChnord (synC1c)))) p0002 p0005
  have p0007 :=
    @gTceq (synCtc (synChncard (synC1c))) (synCnc (synCpw1 (synChnord (synC1c))))
  have p0008 := Nominal.mp p0006 p0007
  have p0009 :=
    @gTceq (synCtc (synCtc (synChncard (synC1c))))
      (synCtc (synCnc (synCpw1 (synChnord (synC1c)))))
  have p0010 := Nominal.mp p0008 p0009
  have p0011 :=
    @gTceq (synCtc (synCtc (synCtc (synChncard (synC1c)))))
      (synCtc (synCtc (synCnc (synCpw1 (synChnord (synC1c))))))
  have p0012 := Nominal.mp p0010 p0011
  have p0013 :=
    @gTceq (synCtc (synCtc (synCtc (synCtc (synChncard (synC1c))))))
      (synCtc (synCtc (synCtc (synCnc (synCpw1 (synChnord (synC1c)))))))
  have p0014 := Nominal.mp p0012 p0013
  have p0015 :=
    @gTceq (synCtc (synCtc (synCtc (synCtc (synCtc (synChncard (synC1c)))))))
      (synCtc (synCtc (synCtc (synCtc (synCnc (synCpw1 (synChnord (synC1c))))))))
  have p0016 := Nominal.mp p0014 p0015
  have p0017 :=
    @gTceq
      (synCtc (synCtc (synCtc (synCtc (synCtc (synCtc (synChncard (synC1c))))))))
      (synCtc (synCtc
          (synCtc (synCtc (synCtc (synCnc (synCpw1 (synChnord (synC1c)))))))))
  have p0018 := Nominal.mp p0016 p0017
  have p0019 :=
    @gFveq2i
      (synCtc (synCtc
          (synCtc (synCtc (synCtc (synCtc (synCtc (synChncard (synC1c)))))))))
      (synCtc (synCtc (synCtc
            (synCtc (synCtc (synCtc (synCnc (synCpw1 (synChnord (synC1c))))))))))
      (synCwppconcrete6fn) p0018
  have p0022 := @gPw1ex (synChnord (synC1c)) p0004
  have p0023 := @gWppconcrete6fnvalndv (synCpw1 (synChnord (synC1c))) p0022
  have p0024 :=
    @gEqtri
      (synCfv (synCwppconcrete6fn) (synCtc (synCtc
            (synCtc (synCtc (synCtc (synCtc (synCtc (synChncard (synC1c))))))))))
      (synCfv (synCwppconcrete6fn) (synCtc (synCtc (synCtc (synCtc
                (synCtc (synCtc (synCnc (synCpw1 (synChnord (synC1c)))))))))))
      (synChncard (synChnord (synCpw (synCpw (synCpw1 (synChnord (synC1c)))))))
      p0019 p0023
  have p0028 := @gPwex (synCpw1 (synChnord (synC1c))) p0022
  have p0029 := @gPwex (synCpw (synCpw1 (synChnord (synC1c)))) p0028
  have p0030 := @gHnordex (synCpw (synCpw (synCpw1 (synChnord (synC1c))))) p0029
  have p0031 :=
    @gHncardnc (synChnord (synCpw (synCpw (synCpw1 (synChnord (synC1c))))))
  have p0032 := Nominal.mp p0030 p0031
  have p0033 :=
    @gEqeltri
      (synCfv (synCwppconcrete6fn) (synCtc (synCtc
            (synCtc (synCtc (synCtc (synCtc (synCtc (synChncard (synC1c))))))))))
      (synChncard (synChnord (synCpw (synCpw (synCpw1 (synChnord (synC1c)))))))
      (synCncs) p0024 p0032
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

/-- Checked nominal proof certificate identified upstream as
`g_wppconcrete6tcbandgrowthfrompointhwclecdndv`.
-/
@[expose]
noncomputable def gWppconcrete6tcbandgrowthfrompointhwclecdndv (y : Var)
    (hyp_wppconcrete6tcbandgrowthfrompointhwclecdndv_1 : Nominal.NPrf (.imp (synWwpp) (synWbr
            (synCtc (synCtc (synCtc (synCtc (synCtc (synCtc (synChncard (synC1c))))))))
            (synClec) (synCfv (synCwppconcrete6fn) (synCtc (synCtc (synCtc (synCtc
                      (synCtc (synCtc (synCtc (synChncard (synC1c))))))))))))) :
    Nominal.NPrf
      (.imp (.classMem (.cv y) (synChwcards (synCvv))) (.imp (synWbr (.cv y) (synClec)
            (synCtc (synCtc (synCtc (synCtc (synCtc (synCtc (synChncard (synC1c)))))))))
          (.imp (synWwpp) (.imp (synWbr (synCtc (synCtc (synCtc
                      (synCtc (synCtc (synCtc (synCtc (synChncard (synC1c)))))))))
                (synClec) (.cv y)) (synWbr (synCtc (synCtc
                    (synCtc (synCtc (synCtc (synCtc (synChncard (synC1c))))))))
                (synClec) (synCfv (synCwppconcrete6fn) (.cv y))))))) :=
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
  have dv_cache_0002 : z ∉ ((synChncard (synC1c))).fv :=
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
      ((synWbr (synCtc (synCtc
              (synCtc (synCtc (synCtc (synCtc (synCtc (synChncard (synC1c)))))))))
          (synClec) (.cv y))).fv :=
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
      ((synWbr (synCfv (synCwppconcrete6fn) (synCtc (synCtc (synCtc
                  (synCtc (synCtc (synCtc (synCtc (synChncard (synC1c))))))))))
          (synClec) (synCfv (synCwppconcrete6fn) (.cv y)))).fv :=
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
    z ∉ ((Wff.classMem (synCfv (synCwppconcrete6fn) (.cv y)) (synCncs))).fv :=
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
    @gId
      (synWa (synWwpp) (synWbr (synCtc (synCtc
              (synCtc (synCtc (synCtc (synCtc (synCtc (synChncard (synC1c)))))))))
          (synClec) (.cv y)))
  have p0001 :=
    @gA1i
      (.imp (synWa (synWwpp) (synWbr (synCtc (synCtc (synCtc
                  (synCtc (synCtc (synCtc (synCtc (synChncard (synC1c)))))))))
            (synClec) (.cv y))) (synWa (synWwpp) (synWbr (synCtc (synCtc (synCtc
                  (synCtc (synCtc (synCtc (synCtc (synChncard (synC1c)))))))))
            (synClec) (.cv y))))
      (synWbr (.cv y) (synClec) (synCtc
          (synCtc (synCtc (synCtc (synCtc (synCtc (synChncard (synC1c)))))))))
      p0000
  have p0002 :=
    @gSimpl (synWwpp)
      (synWbr (synCtc (synCtc
            (synCtc (synCtc (synCtc (synCtc (synCtc (synChncard (synC1c)))))))))
        (synClec) (.cv y))
  have p0003 :=
    @gSyl
      (synWa (synWwpp) (synWbr (synCtc (synCtc
              (synCtc (synCtc (synCtc (synCtc (synCtc (synChncard (synC1c)))))))))
          (synClec) (.cv y)))
      (synWwpp)
      (synWbr (synCtc
          (synCtc (synCtc (synCtc (synCtc (synCtc (synChncard (synC1c)))))))) (synClec)
        (synCfv (synCwppconcrete6fn) (synCtc (synCtc (synCtc
                (synCtc (synCtc (synCtc (synCtc (synChncard (synC1c)))))))))))
      p0002 hyp_wppconcrete6tcbandgrowthfrompointhwclecdndv_1
  have p0004 :=
    @gSimpr (synWwpp)
      (synWbr (synCtc (synCtc
            (synCtc (synCtc (synCtc (synCtc (synCtc (synChncard (synC1c)))))))))
        (synClec) (.cv y))
  have p0005 :=
    @gId
      (synWbr (.cv y) (synClec) (synCtc
          (synCtc (synCtc (synCtc (synCtc (synCtc (synChncard (synC1c)))))))))
  have p0006 := @gHwcardssnc (synCvv)
  have p0007 := @gSseli (synChwcards (synCvv)) (synCncs) (.cv y) p0006
  have p0008 := @gId (.classMem (.cv y) (synChwcards (synCvv)))
  have p0009 :=
    @gA1ii
      (.imp (.classMem (.cv y) (synChwcards (synCvv))) (.classMem (.cv y) (synCncs)))
      (.imp (.classMem (.cv y) (synChwcards (synCvv)))
        (.classMem (.cv y) (synChwcards (synCvv))))
      p0007 p0008
  have p0010 := @gHncardnc1ndv
  have p0011 :=
    @gJctir (.classMem (.cv y) (synChwcards (synCvv))) (.classMem (.cv y) (synCncs))
      (.classMem (synChncard (synC1c)) (synCncs)) p0009 p0010
  have p0012 :=
    @gBiantrurd (.classMem (.cv y) (synChwcards (synCvv)))
      (synWa (.classMem (.cv y) (synCncs)) (.classMem (synChncard (synC1c)) (synCncs)))
      (synWbr (.cv y) (synClec) (synCtc
          (synCtc (synCtc (synCtc (synCtc (synCtc (synChncard (synC1c)))))))))
      p0011
  have p0013 :=
    (Nominal.biimpRefl (synW3a (.classMem (.cv y) (synCncs))
        (.classMem (synChncard (synC1c)) (synCncs)) (synWbr (.cv y) (synClec) (synCtc
            (synCtc (synCtc (synCtc (synCtc (synCtc (synChncard (synC1c)))))))))))
  have p0014 :=
    @gSyl6rbbr (.classMem (.cv y) (synChwcards (synCvv)))
      (synWbr (.cv y) (synClec) (synCtc
          (synCtc (synCtc (synCtc (synCtc (synCtc (synChncard (synC1c)))))))))
      (synWa (synWa (.classMem (.cv y) (synCncs))
          (.classMem (synChncard (synC1c)) (synCncs))) (synWbr (.cv y) (synClec) (synCtc
            (synCtc (synCtc (synCtc (synCtc (synCtc (synChncard (synC1c))))))))))
      (synW3a (.classMem (.cv y) (synCncs)) (.classMem (synChncard (synC1c)) (synCncs))
        (synWbr (.cv y) (synClec) (synCtc
            (synCtc (synCtc (synCtc (synCtc (synCtc (synChncard (synC1c))))))))))
      p0012 p0013
  have p0015 :=
    @gSyl5ibr
      (synWbr (.cv y) (synClec) (synCtc
          (synCtc (synCtc (synCtc (synCtc (synCtc (synChncard (synC1c)))))))))
      (synW3a (.classMem (.cv y) (synCncs)) (.classMem (synChncard (synC1c)) (synCncs))
        (synWbr (.cv y) (synClec) (synCtc
            (synCtc (synCtc (synCtc (synCtc (synCtc (synChncard (synC1c))))))))))
      (.classMem (.cv y) (synChwcards (synCvv)))
      (synWbr (.cv y) (synClec) (synCtc
          (synCtc (synCtc (synCtc (synCtc (synCtc (synChncard (synC1c)))))))))
      p0005 p0014
  have p0016 :=
    @gLetc6ncrepdv z (.cv y) (synChncard (synC1c)) dv_cache_0001 dv_cache_0002
  have p0017 :=
    @gSyl6 (.classMem (.cv y) (synChwcards (synCvv)))
      (synWbr (.cv y) (synClec) (synCtc
          (synCtc (synCtc (synCtc (synCtc (synCtc (synChncard (synC1c)))))))))
      (synW3a (.classMem (.cv y) (synCncs)) (.classMem (synChncard (synC1c)) (synCncs))
        (synWbr (.cv y) (synClec) (synCtc
            (synCtc (synCtc (synCtc (synCtc (synCtc (synChncard (synC1c))))))))))
      (synWex z (.classEq (.cv y)
          (synCtc (synCtc (synCtc (synCtc (synCtc (synCtc (synCnc (.cv z))))))))))
      p0015 p0016
  have p0018 :=
    @gA1dd (.classMem (.cv y) (synChwcards (synCvv)))
      (synWbr (.cv y) (synClec) (synCtc
          (synCtc (synCtc (synCtc (synCtc (synCtc (synChncard (synC1c)))))))))
      (synWex z (.classEq (.cv y)
          (synCtc (synCtc (synCtc (synCtc (synCtc (synCtc (synCnc (.cv z))))))))))
      (synWbr (synCtc (synCtc
            (synCtc (synCtc (synCtc (synCtc (synCtc (synChncard (synC1c)))))))))
        (synClec) (.cv y))
      p0017
  have p0019 :=
    @gNfv
      (synWbr (synCtc (synCtc
            (synCtc (synCtc (synCtc (synCtc (synCtc (synChncard (synC1c)))))))))
        (synClec) (.cv y))
      z dv_cache_0003
  have p0020 :=
    @gNfv
      (synWbr (synCfv (synCwppconcrete6fn) (synCtc (synCtc
              (synCtc (synCtc (synCtc (synCtc (synCtc (synChncard (synC1c))))))))))
        (synClec) (synCfv (synCwppconcrete6fn) (.cv y)))
      z dv_cache_0004
  have p0021 :=
    @gSimpl
      (synWbr (synCtc (synCtc
            (synCtc (synCtc (synCtc (synCtc (synCtc (synChncard (synC1c)))))))))
        (synClec) (.cv y))
      (.classEq (.cv y)
        (synCtc (synCtc (synCtc (synCtc (synCtc (synCtc (synCnc (.cv z)))))))))
  have p0022 := (Nominal.classEqRefl (synChncard (synC1c)))
  have p0023 := @gTceq (synChncard (synC1c)) (synCnc (synChnord (synC1c)))
  have p0024 := Nominal.mp p0022 p0023
  have p0025 := @gN1cex
  have p0026 := @gHnordex (synC1c) p0025
  have p0027 := @gTcnc (synChnord (synC1c)) p0026
  have p0028 :=
    @gEqtri (synCtc (synChncard (synC1c))) (synCtc (synCnc (synChnord (synC1c))))
      (synCnc (synCpw1 (synChnord (synC1c)))) p0024 p0027
  have p0029 :=
    @gTceq (synCtc (synChncard (synC1c))) (synCnc (synCpw1 (synChnord (synC1c))))
  have p0030 := Nominal.mp p0028 p0029
  have p0031 :=
    @gTceq (synCtc (synCtc (synChncard (synC1c))))
      (synCtc (synCnc (synCpw1 (synChnord (synC1c)))))
  have p0032 := Nominal.mp p0030 p0031
  have p0033 :=
    @gTceq (synCtc (synCtc (synCtc (synChncard (synC1c)))))
      (synCtc (synCtc (synCnc (synCpw1 (synChnord (synC1c))))))
  have p0034 := Nominal.mp p0032 p0033
  have p0035 :=
    @gTceq (synCtc (synCtc (synCtc (synCtc (synChncard (synC1c))))))
      (synCtc (synCtc (synCtc (synCnc (synCpw1 (synChnord (synC1c)))))))
  have p0036 := Nominal.mp p0034 p0035
  have p0037 :=
    @gTceq (synCtc (synCtc (synCtc (synCtc (synCtc (synChncard (synC1c)))))))
      (synCtc (synCtc (synCtc (synCtc (synCnc (synCpw1 (synChnord (synC1c))))))))
  have p0038 := Nominal.mp p0036 p0037
  have p0039 :=
    @gTceq
      (synCtc (synCtc (synCtc (synCtc (synCtc (synCtc (synChncard (synC1c))))))))
      (synCtc (synCtc
          (synCtc (synCtc (synCtc (synCnc (synCpw1 (synChnord (synC1c)))))))))
  have p0040 := Nominal.mp p0038 p0039
  have p0041 :=
    @gA1i
      (.classEq (synCtc (synCtc
            (synCtc (synCtc (synCtc (synCtc (synCtc (synChncard (synC1c))))))))) (synCtc
          (synCtc (synCtc (synCtc
                (synCtc (synCtc (synCnc (synCpw1 (synChnord (synC1c)))))))))))
      (synWa (synWbr (synCtc (synCtc
              (synCtc (synCtc (synCtc (synCtc (synCtc (synChncard (synC1c)))))))))
          (synClec) (.cv y)) (.classEq (.cv y)
          (synCtc (synCtc (synCtc (synCtc (synCtc (synCtc (synCnc (.cv z))))))))))
      p0040
  have p0042 :=
    @gSimpr
      (synWbr (synCtc (synCtc
            (synCtc (synCtc (synCtc (synCtc (synCtc (synChncard (synC1c)))))))))
        (synClec) (.cv y))
      (.classEq (.cv y)
        (synCtc (synCtc (synCtc (synCtc (synCtc (synCtc (synCnc (.cv z)))))))))
  have p0043 :=
    @gBreq12d
      (synWa (synWbr (synCtc (synCtc
              (synCtc (synCtc (synCtc (synCtc (synCtc (synChncard (synC1c)))))))))
          (synClec) (.cv y)) (.classEq (.cv y)
          (synCtc (synCtc (synCtc (synCtc (synCtc (synCtc (synCnc (.cv z))))))))))
      (synCtc (synCtc
          (synCtc (synCtc (synCtc (synCtc (synCtc (synChncard (synC1c)))))))))
      (synCtc (synCtc (synCtc
            (synCtc (synCtc (synCtc (synCnc (synCpw1 (synChnord (synC1c))))))))))
      (.cv y)
      (synCtc (synCtc (synCtc (synCtc (synCtc (synCtc (synCnc (.cv z))))))))
      (synClec) p0041 p0042
  have p0044 :=
    @gMpbid
      (synWa (synWbr (synCtc (synCtc
              (synCtc (synCtc (synCtc (synCtc (synCtc (synChncard (synC1c)))))))))
          (synClec) (.cv y)) (.classEq (.cv y)
          (synCtc (synCtc (synCtc (synCtc (synCtc (synCtc (synCnc (.cv z))))))))))
      (synWbr (synCtc (synCtc
            (synCtc (synCtc (synCtc (synCtc (synCtc (synChncard (synC1c)))))))))
        (synClec) (.cv y))
      (synWbr (synCtc (synCtc (synCtc
              (synCtc (synCtc (synCtc (synCnc (synCpw1 (synChnord (synC1c))))))))))
        (synClec)
        (synCtc (synCtc (synCtc (synCtc (synCtc (synCtc (synCnc (.cv z)))))))))
      p0021 p0043
  have p0047 := @gPw1ex (synChnord (synC1c)) p0026
  have p0048 := @gVex z
  have p0049 :=
    @gWppconcrete6representedmonondv (synCpw1 (synChnord (synC1c))) (.cv z) p0047
      p0048
  have p0050 :=
    @gSyl
      (synWa (synWbr (synCtc (synCtc
              (synCtc (synCtc (synCtc (synCtc (synCtc (synChncard (synC1c)))))))))
          (synClec) (.cv y)) (.classEq (.cv y)
          (synCtc (synCtc (synCtc (synCtc (synCtc (synCtc (synCnc (.cv z))))))))))
      (synWbr (synCtc (synCtc (synCtc
              (synCtc (synCtc (synCtc (synCnc (synCpw1 (synChnord (synC1c))))))))))
        (synClec)
        (synCtc (synCtc (synCtc (synCtc (synCtc (synCtc (synCnc (.cv z)))))))))
      (synWbr (synCfv (synCwppconcrete6fn) (synCtc (synCtc (synCtc (synCtc
                  (synCtc (synCtc (synCnc (synCpw1 (synChnord (synC1c)))))))))))
        (synClec) (synCfv (synCwppconcrete6fn)
          (synCtc (synCtc (synCtc (synCtc (synCtc (synCtc (synCnc (.cv z))))))))))
      p0044 p0049
  have p0070 :=
    @gFveq2i
      (synCtc (synCtc
          (synCtc (synCtc (synCtc (synCtc (synCtc (synChncard (synC1c)))))))))
      (synCtc (synCtc (synCtc
            (synCtc (synCtc (synCtc (synCnc (synCpw1 (synChnord (synC1c))))))))))
      (synCwppconcrete6fn) p0040
  have p0071 :=
    @gA1i
      (.classEq (synCfv (synCwppconcrete6fn) (synCtc (synCtc
              (synCtc (synCtc (synCtc (synCtc (synCtc (synChncard (synC1c))))))))))
        (synCfv (synCwppconcrete6fn) (synCtc (synCtc (synCtc (synCtc
                  (synCtc (synCtc (synCnc (synCpw1 (synChnord (synC1c))))))))))))
      (synWa (synWbr (synCtc (synCtc
              (synCtc (synCtc (synCtc (synCtc (synCtc (synChncard (synC1c)))))))))
          (synClec) (.cv y)) (.classEq (.cv y)
          (synCtc (synCtc (synCtc (synCtc (synCtc (synCtc (synCnc (.cv z))))))))))
      p0070
  have p0073 :=
    @gFveq2d
      (synWa (synWbr (synCtc (synCtc
              (synCtc (synCtc (synCtc (synCtc (synCtc (synChncard (synC1c)))))))))
          (synClec) (.cv y)) (.classEq (.cv y)
          (synCtc (synCtc (synCtc (synCtc (synCtc (synCtc (synCnc (.cv z))))))))))
      (.cv y)
      (synCtc (synCtc (synCtc (synCtc (synCtc (synCtc (synCnc (.cv z))))))))
      (synCwppconcrete6fn) p0042
  have p0074 :=
    @gBreq12d
      (synWa (synWbr (synCtc (synCtc
              (synCtc (synCtc (synCtc (synCtc (synCtc (synChncard (synC1c)))))))))
          (synClec) (.cv y)) (.classEq (.cv y)
          (synCtc (synCtc (synCtc (synCtc (synCtc (synCtc (synCnc (.cv z))))))))))
      (synCfv (synCwppconcrete6fn) (synCtc (synCtc
            (synCtc (synCtc (synCtc (synCtc (synCtc (synChncard (synC1c))))))))))
      (synCfv (synCwppconcrete6fn) (synCtc (synCtc (synCtc (synCtc
                (synCtc (synCtc (synCnc (synCpw1 (synChnord (synC1c)))))))))))
      (synCfv (synCwppconcrete6fn) (.cv y))
      (synCfv (synCwppconcrete6fn)
        (synCtc (synCtc (synCtc (synCtc (synCtc (synCtc (synCnc (.cv z)))))))))
      (synClec) p0071 p0073
  have p0075 :=
    @gMpbird
      (synWa (synWbr (synCtc (synCtc
              (synCtc (synCtc (synCtc (synCtc (synCtc (synChncard (synC1c)))))))))
          (synClec) (.cv y)) (.classEq (.cv y)
          (synCtc (synCtc (synCtc (synCtc (synCtc (synCtc (synCnc (.cv z))))))))))
      (synWbr (synCfv (synCwppconcrete6fn) (synCtc (synCtc
              (synCtc (synCtc (synCtc (synCtc (synCtc (synChncard (synC1c))))))))))
        (synClec) (synCfv (synCwppconcrete6fn) (.cv y)))
      (synWbr (synCfv (synCwppconcrete6fn) (synCtc (synCtc (synCtc (synCtc
                  (synCtc (synCtc (synCnc (synCpw1 (synChnord (synC1c)))))))))))
        (synClec) (synCfv (synCwppconcrete6fn)
          (synCtc (synCtc (synCtc (synCtc (synCtc (synCtc (synCnc (.cv z))))))))))
      p0050 p0074
  have p0076 :=
    @gEx
      (synWbr (synCtc (synCtc
            (synCtc (synCtc (synCtc (synCtc (synCtc (synChncard (synC1c)))))))))
        (synClec) (.cv y))
      (.classEq (.cv y)
        (synCtc (synCtc (synCtc (synCtc (synCtc (synCtc (synCnc (.cv z)))))))))
      (synWbr (synCfv (synCwppconcrete6fn) (synCtc (synCtc
              (synCtc (synCtc (synCtc (synCtc (synCtc (synChncard (synC1c))))))))))
        (synClec) (synCfv (synCwppconcrete6fn) (.cv y)))
      p0075
  have p0077 :=
    @gExlimd
      (synWbr (synCtc (synCtc
            (synCtc (synCtc (synCtc (synCtc (synCtc (synChncard (synC1c)))))))))
        (synClec) (.cv y))
      (.classEq (.cv y)
        (synCtc (synCtc (synCtc (synCtc (synCtc (synCtc (synCnc (.cv z)))))))))
      (synWbr (synCfv (synCwppconcrete6fn) (synCtc (synCtc
              (synCtc (synCtc (synCtc (synCtc (synCtc (synChncard (synC1c))))))))))
        (synClec) (synCfv (synCwppconcrete6fn) (.cv y)))
      z p0019 p0020 p0076
  have p0078 :=
    @gA2i
      (synWbr (synCtc (synCtc
            (synCtc (synCtc (synCtc (synCtc (synCtc (synChncard (synC1c)))))))))
        (synClec) (.cv y))
      (synWex z (.classEq (.cv y)
          (synCtc (synCtc (synCtc (synCtc (synCtc (synCtc (synCnc (.cv z))))))))))
      (synWbr (synCfv (synCwppconcrete6fn) (synCtc (synCtc
              (synCtc (synCtc (synCtc (synCtc (synCtc (synChncard (synC1c))))))))))
        (synClec) (synCfv (synCwppconcrete6fn) (.cv y)))
      p0077
  have p0079 :=
    @gSyl6 (.classMem (.cv y) (synChwcards (synCvv)))
      (synWbr (.cv y) (synClec) (synCtc
          (synCtc (synCtc (synCtc (synCtc (synCtc (synChncard (synC1c)))))))))
      (.imp (synWbr (synCtc (synCtc
              (synCtc (synCtc (synCtc (synCtc (synCtc (synChncard (synC1c)))))))))
          (synClec) (.cv y)) (synWex z (.classEq (.cv y) (synCtc
              (synCtc (synCtc (synCtc (synCtc (synCtc (synCnc (.cv z)))))))))))
      (.imp (synWbr (synCtc (synCtc
              (synCtc (synCtc (synCtc (synCtc (synCtc (synChncard (synC1c)))))))))
          (synClec) (.cv y)) (synWbr (synCfv (synCwppconcrete6fn) (synCtc (synCtc (synCtc
                  (synCtc (synCtc (synCtc (synCtc (synChncard (synC1c))))))))))
          (synClec) (synCfv (synCwppconcrete6fn) (.cv y))))
      p0018 p0078
  have p0080 :=
    @gSyl7
      (synWa (synWwpp) (synWbr (synCtc (synCtc
              (synCtc (synCtc (synCtc (synCtc (synCtc (synChncard (synC1c)))))))))
          (synClec) (.cv y)))
      (synWbr (synCtc (synCtc
            (synCtc (synCtc (synCtc (synCtc (synCtc (synChncard (synC1c)))))))))
        (synClec) (.cv y))
      (.classMem (.cv y) (synChwcards (synCvv)))
      (synWbr (.cv y) (synClec) (synCtc
          (synCtc (synCtc (synCtc (synCtc (synCtc (synChncard (synC1c)))))))))
      (synWbr (synCfv (synCwppconcrete6fn) (synCtc (synCtc
              (synCtc (synCtc (synCtc (synCtc (synCtc (synChncard (synC1c))))))))))
        (synClec) (synCfv (synCwppconcrete6fn) (.cv y)))
      p0004 p0079
  have p0081 :=
    @gA1dd (.classMem (.cv y) (synChwcards (synCvv)))
      (synWbr (.cv y) (synClec) (synCtc
          (synCtc (synCtc (synCtc (synCtc (synCtc (synChncard (synC1c)))))))))
      (.imp (synWa (synWwpp) (synWbr (synCtc (synCtc (synCtc
                  (synCtc (synCtc (synCtc (synCtc (synChncard (synC1c)))))))))
            (synClec) (.cv y))) (synWbr (synCfv (synCwppconcrete6fn) (synCtc (synCtc
                (synCtc (synCtc (synCtc (synCtc (synCtc (synChncard (synC1c))))))))))
          (synClec) (synCfv (synCwppconcrete6fn) (.cv y))))
      (synWbr (synCtc
          (synCtc (synCtc (synCtc (synCtc (synCtc (synChncard (synC1c)))))))) (synClec)
        (synCfv (synCwppconcrete6fn) (synCtc (synCtc (synCtc
                (synCtc (synCtc (synCtc (synCtc (synChncard (synC1c)))))))))))
      p0080
  have p0082 :=
    @g_pm3_2
      (synWbr (synCtc
          (synCtc (synCtc (synCtc (synCtc (synCtc (synChncard (synC1c)))))))) (synClec)
        (synCfv (synCwppconcrete6fn) (synCtc (synCtc (synCtc
                (synCtc (synCtc (synCtc (synCtc (synChncard (synC1c)))))))))))
      (synWbr (synCfv (synCwppconcrete6fn) (synCtc (synCtc
              (synCtc (synCtc (synCtc (synCtc (synCtc (synChncard (synC1c))))))))))
        (synClec) (synCfv (synCwppconcrete6fn) (.cv y)))
  have p0083 :=
    @gA1i
      (.imp (synWbr (synCtc
            (synCtc (synCtc (synCtc (synCtc (synCtc (synChncard (synC1c))))))))
          (synClec) (synCfv (synCwppconcrete6fn) (synCtc (synCtc (synCtc
                  (synCtc (synCtc (synCtc (synCtc (synChncard (synC1c))))))))))) (.imp
          (synWbr (synCfv (synCwppconcrete6fn) (synCtc (synCtc (synCtc
                    (synCtc (synCtc (synCtc (synCtc (synChncard (synC1c))))))))))
            (synClec) (synCfv (synCwppconcrete6fn) (.cv y))) (synWa (synWbr (synCtc
                (synCtc (synCtc (synCtc (synCtc (synCtc (synChncard (synC1c))))))))
              (synClec) (synCfv (synCwppconcrete6fn) (synCtc (synCtc (synCtc
                      (synCtc (synCtc (synCtc (synCtc (synChncard (synC1c)))))))))))
            (synWbr (synCfv (synCwppconcrete6fn) (synCtc (synCtc (synCtc
                      (synCtc (synCtc (synCtc (synCtc (synChncard (synC1c))))))))))
              (synClec) (synCfv (synCwppconcrete6fn) (.cv y))))))
      (synWbr (.cv y) (synClec) (synCtc
          (synCtc (synCtc (synCtc (synCtc (synCtc (synChncard (synC1c)))))))))
      p0082
  have p0084 :=
    @gImim2
      (synWbr (synCfv (synCwppconcrete6fn) (synCtc (synCtc
              (synCtc (synCtc (synCtc (synCtc (synCtc (synChncard (synC1c))))))))))
        (synClec) (synCfv (synCwppconcrete6fn) (.cv y)))
      (synWa (synWbr (synCtc
            (synCtc (synCtc (synCtc (synCtc (synCtc (synChncard (synC1c))))))))
          (synClec) (synCfv (synCwppconcrete6fn) (synCtc (synCtc (synCtc
                  (synCtc (synCtc (synCtc (synCtc (synChncard (synC1c))))))))))) (synWbr
          (synCfv (synCwppconcrete6fn) (synCtc (synCtc (synCtc
                  (synCtc (synCtc (synCtc (synCtc (synChncard (synC1c))))))))))
          (synClec) (synCfv (synCwppconcrete6fn) (.cv y))))
      (synWa (synWwpp) (synWbr (synCtc (synCtc
              (synCtc (synCtc (synCtc (synCtc (synCtc (synChncard (synC1c)))))))))
          (synClec) (.cv y)))
  have p0085 :=
    @gSyl6
      (synWbr (.cv y) (synClec) (synCtc
          (synCtc (synCtc (synCtc (synCtc (synCtc (synChncard (synC1c)))))))))
      (synWbr (synCtc
          (synCtc (synCtc (synCtc (synCtc (synCtc (synChncard (synC1c)))))))) (synClec)
        (synCfv (synCwppconcrete6fn) (synCtc (synCtc (synCtc
                (synCtc (synCtc (synCtc (synCtc (synChncard (synC1c)))))))))))
      (.imp (synWbr (synCfv (synCwppconcrete6fn) (synCtc (synCtc (synCtc
                  (synCtc (synCtc (synCtc (synCtc (synChncard (synC1c))))))))))
          (synClec) (synCfv (synCwppconcrete6fn) (.cv y))) (synWa (synWbr (synCtc
              (synCtc (synCtc (synCtc (synCtc (synCtc (synChncard (synC1c))))))))
            (synClec) (synCfv (synCwppconcrete6fn) (synCtc (synCtc (synCtc
                    (synCtc (synCtc (synCtc (synCtc (synChncard (synC1c)))))))))))
          (synWbr (synCfv (synCwppconcrete6fn) (synCtc (synCtc (synCtc
                    (synCtc (synCtc (synCtc (synCtc (synChncard (synC1c))))))))))
            (synClec) (synCfv (synCwppconcrete6fn) (.cv y)))))
      (.imp (.imp (synWa (synWwpp) (synWbr (synCtc (synCtc (synCtc
                    (synCtc (synCtc (synCtc (synCtc (synChncard (synC1c)))))))))
              (synClec) (.cv y))) (synWbr (synCfv (synCwppconcrete6fn) (synCtc (synCtc
                  (synCtc (synCtc (synCtc (synCtc (synCtc (synChncard (synC1c))))))))))
            (synClec) (synCfv (synCwppconcrete6fn) (.cv y)))) (.imp (synWa (synWwpp)
            (synWbr (synCtc (synCtc (synCtc
                    (synCtc (synCtc (synCtc (synCtc (synChncard (synC1c)))))))))
              (synClec) (.cv y))) (synWa (synWbr (synCtc
                (synCtc (synCtc (synCtc (synCtc (synCtc (synChncard (synC1c))))))))
              (synClec) (synCfv (synCwppconcrete6fn) (synCtc (synCtc (synCtc
                      (synCtc (synCtc (synCtc (synCtc (synChncard (synC1c)))))))))))
            (synWbr (synCfv (synCwppconcrete6fn) (synCtc (synCtc (synCtc
                      (synCtc (synCtc (synCtc (synCtc (synChncard (synC1c))))))))))
              (synClec) (synCfv (synCwppconcrete6fn) (.cv y))))))
      p0083 p0084
  have p0086 :=
    @gA2d
      (synWbr (.cv y) (synClec) (synCtc
          (synCtc (synCtc (synCtc (synCtc (synCtc (synChncard (synC1c)))))))))
      (synWbr (synCtc
          (synCtc (synCtc (synCtc (synCtc (synCtc (synChncard (synC1c)))))))) (synClec)
        (synCfv (synCwppconcrete6fn) (synCtc (synCtc (synCtc
                (synCtc (synCtc (synCtc (synCtc (synChncard (synC1c)))))))))))
      (.imp (synWa (synWwpp) (synWbr (synCtc (synCtc (synCtc
                  (synCtc (synCtc (synCtc (synCtc (synChncard (synC1c)))))))))
            (synClec) (.cv y))) (synWbr (synCfv (synCwppconcrete6fn) (synCtc (synCtc
                (synCtc (synCtc (synCtc (synCtc (synCtc (synChncard (synC1c))))))))))
          (synClec) (synCfv (synCwppconcrete6fn) (.cv y))))
      (.imp (synWa (synWwpp) (synWbr (synCtc (synCtc (synCtc
                  (synCtc (synCtc (synCtc (synCtc (synChncard (synC1c)))))))))
            (synClec) (.cv y))) (synWa (synWbr (synCtc
              (synCtc (synCtc (synCtc (synCtc (synCtc (synChncard (synC1c))))))))
            (synClec) (synCfv (synCwppconcrete6fn) (synCtc (synCtc (synCtc
                    (synCtc (synCtc (synCtc (synCtc (synChncard (synC1c)))))))))))
          (synWbr (synCfv (synCwppconcrete6fn) (synCtc (synCtc (synCtc
                    (synCtc (synCtc (synCtc (synCtc (synChncard (synC1c))))))))))
            (synClec) (synCfv (synCwppconcrete6fn) (.cv y)))))
      p0085
  have p0087 :=
    @gSylcom (.classMem (.cv y) (synChwcards (synCvv)))
      (synWbr (.cv y) (synClec) (synCtc
          (synCtc (synCtc (synCtc (synCtc (synCtc (synChncard (synC1c)))))))))
      (.imp (synWbr (synCtc
            (synCtc (synCtc (synCtc (synCtc (synCtc (synChncard (synC1c))))))))
          (synClec) (synCfv (synCwppconcrete6fn) (synCtc (synCtc (synCtc
                  (synCtc (synCtc (synCtc (synCtc (synChncard (synC1c))))))))))) (.imp
          (synWa (synWwpp) (synWbr (synCtc (synCtc (synCtc
                    (synCtc (synCtc (synCtc (synCtc (synChncard (synC1c)))))))))
              (synClec) (.cv y))) (synWbr (synCfv (synCwppconcrete6fn) (synCtc (synCtc
                  (synCtc (synCtc (synCtc (synCtc (synCtc (synChncard (synC1c))))))))))
            (synClec) (synCfv (synCwppconcrete6fn) (.cv y)))))
      (.imp (synWbr (synCtc
            (synCtc (synCtc (synCtc (synCtc (synCtc (synChncard (synC1c))))))))
          (synClec) (synCfv (synCwppconcrete6fn) (synCtc (synCtc (synCtc
                  (synCtc (synCtc (synCtc (synCtc (synChncard (synC1c))))))))))) (.imp
          (synWa (synWwpp) (synWbr (synCtc (synCtc (synCtc
                    (synCtc (synCtc (synCtc (synCtc (synChncard (synC1c)))))))))
              (synClec) (.cv y))) (synWa (synWbr (synCtc
                (synCtc (synCtc (synCtc (synCtc (synCtc (synChncard (synC1c))))))))
              (synClec) (synCfv (synCwppconcrete6fn) (synCtc (synCtc (synCtc
                      (synCtc (synCtc (synCtc (synCtc (synChncard (synC1c)))))))))))
            (synWbr (synCfv (synCwppconcrete6fn) (synCtc (synCtc (synCtc
                      (synCtc (synCtc (synCtc (synCtc (synChncard (synC1c))))))))))
              (synClec) (synCfv (synCwppconcrete6fn) (.cv y))))))
      p0081 p0086
  have p0088 :=
    @gSyl7
      (synWa (synWwpp) (synWbr (synCtc (synCtc
              (synCtc (synCtc (synCtc (synCtc (synCtc (synChncard (synC1c)))))))))
          (synClec) (.cv y)))
      (synWbr (synCtc
          (synCtc (synCtc (synCtc (synCtc (synCtc (synChncard (synC1c)))))))) (synClec)
        (synCfv (synCwppconcrete6fn) (synCtc (synCtc (synCtc
                (synCtc (synCtc (synCtc (synCtc (synChncard (synC1c)))))))))))
      (.classMem (.cv y) (synChwcards (synCvv)))
      (synWbr (.cv y) (synClec) (synCtc
          (synCtc (synCtc (synCtc (synCtc (synCtc (synChncard (synC1c)))))))))
      (.imp (synWa (synWwpp) (synWbr (synCtc (synCtc (synCtc
                  (synCtc (synCtc (synCtc (synCtc (synChncard (synC1c)))))))))
            (synClec) (.cv y))) (synWa (synWbr (synCtc
              (synCtc (synCtc (synCtc (synCtc (synCtc (synChncard (synC1c))))))))
            (synClec) (synCfv (synCwppconcrete6fn) (synCtc (synCtc (synCtc
                    (synCtc (synCtc (synCtc (synCtc (synChncard (synC1c)))))))))))
          (synWbr (synCfv (synCwppconcrete6fn) (synCtc (synCtc (synCtc
                    (synCtc (synCtc (synCtc (synCtc (synChncard (synC1c))))))))))
            (synClec) (synCfv (synCwppconcrete6fn) (.cv y)))))
      p0003 p0087
  have p0089 :=
    Nominal.ax2
      (synWa (synWwpp) (synWbr (synCtc (synCtc
              (synCtc (synCtc (synCtc (synCtc (synCtc (synChncard (synC1c)))))))))
          (synClec) (.cv y)))
      (synWa (synWwpp) (synWbr (synCtc (synCtc
              (synCtc (synCtc (synCtc (synCtc (synCtc (synChncard (synC1c)))))))))
          (synClec) (.cv y)))
      (synWa (synWbr (synCtc
            (synCtc (synCtc (synCtc (synCtc (synCtc (synChncard (synC1c))))))))
          (synClec) (synCfv (synCwppconcrete6fn) (synCtc (synCtc (synCtc
                  (synCtc (synCtc (synCtc (synCtc (synChncard (synC1c))))))))))) (synWbr
          (synCfv (synCwppconcrete6fn) (synCtc (synCtc (synCtc
                  (synCtc (synCtc (synCtc (synCtc (synChncard (synC1c))))))))))
          (synClec) (synCfv (synCwppconcrete6fn) (.cv y))))
  have p0090 :=
    @gSyl6 (.classMem (.cv y) (synChwcards (synCvv)))
      (synWbr (.cv y) (synClec) (synCtc
          (synCtc (synCtc (synCtc (synCtc (synCtc (synChncard (synC1c)))))))))
      (.imp (synWa (synWwpp) (synWbr (synCtc (synCtc (synCtc
                  (synCtc (synCtc (synCtc (synCtc (synChncard (synC1c)))))))))
            (synClec) (.cv y))) (.imp (synWa (synWwpp) (synWbr (synCtc (synCtc (synCtc
                    (synCtc (synCtc (synCtc (synCtc (synChncard (synC1c)))))))))
              (synClec) (.cv y))) (synWa (synWbr (synCtc
                (synCtc (synCtc (synCtc (synCtc (synCtc (synChncard (synC1c))))))))
              (synClec) (synCfv (synCwppconcrete6fn) (synCtc (synCtc (synCtc
                      (synCtc (synCtc (synCtc (synCtc (synChncard (synC1c)))))))))))
            (synWbr (synCfv (synCwppconcrete6fn) (synCtc (synCtc (synCtc
                      (synCtc (synCtc (synCtc (synCtc (synChncard (synC1c))))))))))
              (synClec) (synCfv (synCwppconcrete6fn) (.cv y))))))
      (.imp (.imp (synWa (synWwpp) (synWbr (synCtc (synCtc (synCtc
                    (synCtc (synCtc (synCtc (synCtc (synChncard (synC1c)))))))))
              (synClec) (.cv y))) (synWa (synWwpp) (synWbr (synCtc (synCtc (synCtc
                    (synCtc (synCtc (synCtc (synCtc (synChncard (synC1c)))))))))
              (synClec) (.cv y)))) (.imp (synWa (synWwpp) (synWbr (synCtc (synCtc (synCtc
                    (synCtc (synCtc (synCtc (synCtc (synChncard (synC1c)))))))))
              (synClec) (.cv y))) (synWa (synWbr (synCtc
                (synCtc (synCtc (synCtc (synCtc (synCtc (synChncard (synC1c))))))))
              (synClec) (synCfv (synCwppconcrete6fn) (synCtc (synCtc (synCtc
                      (synCtc (synCtc (synCtc (synCtc (synChncard (synC1c)))))))))))
            (synWbr (synCfv (synCwppconcrete6fn) (synCtc (synCtc (synCtc
                      (synCtc (synCtc (synCtc (synCtc (synChncard (synC1c))))))))))
              (synClec) (synCfv (synCwppconcrete6fn) (.cv y))))))
      p0088 p0089
  have p0091 :=
    @gMpdi (.classMem (.cv y) (synChwcards (synCvv)))
      (synWbr (.cv y) (synClec) (synCtc
          (synCtc (synCtc (synCtc (synCtc (synCtc (synChncard (synC1c)))))))))
      (.imp (synWa (synWwpp) (synWbr (synCtc (synCtc (synCtc
                  (synCtc (synCtc (synCtc (synCtc (synChncard (synC1c)))))))))
            (synClec) (.cv y))) (synWa (synWwpp) (synWbr (synCtc (synCtc (synCtc
                  (synCtc (synCtc (synCtc (synCtc (synChncard (synC1c)))))))))
            (synClec) (.cv y))))
      (.imp (synWa (synWwpp) (synWbr (synCtc (synCtc (synCtc
                  (synCtc (synCtc (synCtc (synCtc (synChncard (synC1c)))))))))
            (synClec) (.cv y))) (synWa (synWbr (synCtc
              (synCtc (synCtc (synCtc (synCtc (synCtc (synChncard (synC1c))))))))
            (synClec) (synCfv (synCwppconcrete6fn) (synCtc (synCtc (synCtc
                    (synCtc (synCtc (synCtc (synCtc (synChncard (synC1c)))))))))))
          (synWbr (synCfv (synCwppconcrete6fn) (synCtc (synCtc (synCtc
                    (synCtc (synCtc (synCtc (synCtc (synChncard (synC1c))))))))))
            (synClec) (synCfv (synCwppconcrete6fn) (.cv y)))))
      p0001 p0090
  have p0092 :=
    @gId
      (.classEq (.cv y)
        (synCtc (synCtc (synCtc (synCtc (synCtc (synCtc (synCnc (.cv z)))))))))
  have p0093 :=
    @gFveq2d
      (.classEq (.cv y)
        (synCtc (synCtc (synCtc (synCtc (synCtc (synCtc (synCnc (.cv z)))))))))
      (.cv y)
      (synCtc (synCtc (synCtc (synCtc (synCtc (synCtc (synCnc (.cv z))))))))
      (synCwppconcrete6fn) p0092
  have p0095 := @gWppconcrete6fnvalndv (.cv z) p0048
  have p0097 := @gPwex (.cv z) p0048
  have p0098 := @gPwex (synCpw (.cv z)) p0097
  have p0099 := @gHnordex (synCpw (synCpw (.cv z))) p0098
  have p0100 := @gHncardnc (synChnord (synCpw (synCpw (.cv z))))
  have p0101 := Nominal.mp p0099 p0100
  have p0102 :=
    @gEqeltri
      (synCfv (synCwppconcrete6fn)
        (synCtc (synCtc (synCtc (synCtc (synCtc (synCtc (synCnc (.cv z)))))))))
      (synChncard (synChnord (synCpw (synCpw (.cv z))))) (synCncs) p0095 p0101
  have p0103 :=
    @gA1i
      (.classMem (synCfv (synCwppconcrete6fn)
          (synCtc (synCtc (synCtc (synCtc (synCtc (synCtc (synCnc (.cv z)))))))))
        (synCncs))
      (.classEq (.cv y)
        (synCtc (synCtc (synCtc (synCtc (synCtc (synCtc (synCnc (.cv z)))))))))
      p0102
  have p0104 :=
    @gEqeltrd
      (.classEq (.cv y)
        (synCtc (synCtc (synCtc (synCtc (synCtc (synCtc (synCnc (.cv z)))))))))
      (synCfv (synCwppconcrete6fn) (.cv y))
      (synCfv (synCwppconcrete6fn)
        (synCtc (synCtc (synCtc (synCtc (synCtc (synCtc (synCnc (.cv z)))))))))
      (synCncs) p0093 p0103
  have p0105 :=
    @gExlimiv
      (.classEq (.cv y)
        (synCtc (synCtc (synCtc (synCtc (synCtc (synCtc (synCnc (.cv z)))))))))
      (.classMem (synCfv (synCwppconcrete6fn) (.cv y)) (synCncs)) z dv_cache_0005 p0104
  have p0106 :=
    @gSyl6 (.classMem (.cv y) (synChwcards (synCvv)))
      (synWbr (.cv y) (synClec) (synCtc
          (synCtc (synCtc (synCtc (synCtc (synCtc (synChncard (synC1c)))))))))
      (synWex z (.classEq (.cv y)
          (synCtc (synCtc (synCtc (synCtc (synCtc (synCtc (synCnc (.cv z))))))))))
      (.classMem (synCfv (synCwppconcrete6fn) (.cv y)) (synCncs)) p0017 p0105
  have p0107 :=
    (Nominal.biimpRefl (synW3a (.classMem (synCtc
            (synCtc (synCtc (synCtc (synCtc (synCtc (synChncard (synC1c))))))))
          (synCncs)) (.classMem (synCfv (synCwppconcrete6fn) (synCtc (synCtc (synCtc
                  (synCtc (synCtc (synCtc (synCtc (synChncard (synC1c))))))))))
          (synCncs)) (.classMem (synCfv (synCwppconcrete6fn) (.cv y)) (synCncs))))
  have p0109 := @gTccl (synChncard (synC1c))
  have p0110 := Nominal.mp p0010 p0109
  have p0111 := @gTccl (synCtc (synChncard (synC1c)))
  have p0112 := Nominal.mp p0110 p0111
  have p0113 := @gTccl (synCtc (synCtc (synChncard (synC1c))))
  have p0114 := Nominal.mp p0112 p0113
  have p0115 := @gTccl (synCtc (synCtc (synCtc (synChncard (synC1c)))))
  have p0116 := Nominal.mp p0114 p0115
  have p0117 := @gTccl (synCtc (synCtc (synCtc (synCtc (synChncard (synC1c))))))
  have p0118 := Nominal.mp p0116 p0117
  have p0119 :=
    @gTccl (synCtc (synCtc (synCtc (synCtc (synCtc (synChncard (synC1c)))))))
  have p0120 := Nominal.mp p0118 p0119
  have p0121 := @gWppconcrete6tcvalncndv
  have p0122 :=
    @gPm32i
      (.classMem (synCtc
          (synCtc (synCtc (synCtc (synCtc (synCtc (synChncard (synC1c)))))))) (synCncs))
      (.classMem (synCfv (synCwppconcrete6fn) (synCtc (synCtc
              (synCtc (synCtc (synCtc (synCtc (synCtc (synChncard (synC1c))))))))))
        (synCncs))
      p0120 p0121
  have p0123 :=
    @gBiantrur
      (synWa (.classMem (synCtc
            (synCtc (synCtc (synCtc (synCtc (synCtc (synChncard (synC1c))))))))
          (synCncs)) (.classMem (synCfv (synCwppconcrete6fn) (synCtc (synCtc (synCtc
                  (synCtc (synCtc (synCtc (synCtc (synChncard (synC1c))))))))))
          (synCncs)))
      (.classMem (synCfv (synCwppconcrete6fn) (.cv y)) (synCncs)) p0122
  have p0124 :=
    @gBitr4i
      (synW3a (.classMem (synCtc
            (synCtc (synCtc (synCtc (synCtc (synCtc (synChncard (synC1c))))))))
          (synCncs)) (.classMem (synCfv (synCwppconcrete6fn) (synCtc (synCtc (synCtc
                  (synCtc (synCtc (synCtc (synCtc (synChncard (synC1c))))))))))
          (synCncs)) (.classMem (synCfv (synCwppconcrete6fn) (.cv y)) (synCncs)))
      (synWa (synWa (.classMem (synCtc
              (synCtc (synCtc (synCtc (synCtc (synCtc (synChncard (synC1c))))))))
            (synCncs)) (.classMem (synCfv (synCwppconcrete6fn) (synCtc (synCtc (synCtc
                    (synCtc (synCtc (synCtc (synCtc (synChncard (synC1c))))))))))
            (synCncs))) (.classMem (synCfv (synCwppconcrete6fn) (.cv y)) (synCncs)))
      (.classMem (synCfv (synCwppconcrete6fn) (.cv y)) (synCncs)) p0107 p0123
  have p0125 :=
    @gA1i
      (synWb (synW3a (.classMem (synCtc
              (synCtc (synCtc (synCtc (synCtc (synCtc (synChncard (synC1c))))))))
            (synCncs)) (.classMem (synCfv (synCwppconcrete6fn) (synCtc (synCtc (synCtc
                    (synCtc (synCtc (synCtc (synCtc (synChncard (synC1c))))))))))
            (synCncs)) (.classMem (synCfv (synCwppconcrete6fn) (.cv y)) (synCncs)))
        (.classMem (synCfv (synCwppconcrete6fn) (.cv y)) (synCncs)))
      (synWbr (.cv y) (synClec) (synCtc
          (synCtc (synCtc (synCtc (synCtc (synCtc (synChncard (synC1c)))))))))
      p0124
  have p0126 :=
    @gBiimprd
      (synWbr (.cv y) (synClec) (synCtc
          (synCtc (synCtc (synCtc (synCtc (synCtc (synChncard (synC1c)))))))))
      (synW3a (.classMem (synCtc
            (synCtc (synCtc (synCtc (synCtc (synCtc (synChncard (synC1c))))))))
          (synCncs)) (.classMem (synCfv (synCwppconcrete6fn) (synCtc (synCtc (synCtc
                  (synCtc (synCtc (synCtc (synCtc (synChncard (synC1c))))))))))
          (synCncs)) (.classMem (synCfv (synCwppconcrete6fn) (.cv y)) (synCncs)))
      (.classMem (synCfv (synCwppconcrete6fn) (.cv y)) (synCncs)) p0125
  have p0127 :=
    @gSylcom (.classMem (.cv y) (synChwcards (synCvv)))
      (synWbr (.cv y) (synClec) (synCtc
          (synCtc (synCtc (synCtc (synCtc (synCtc (synChncard (synC1c)))))))))
      (.classMem (synCfv (synCwppconcrete6fn) (.cv y)) (synCncs))
      (synW3a (.classMem (synCtc
            (synCtc (synCtc (synCtc (synCtc (synCtc (synChncard (synC1c))))))))
          (synCncs)) (.classMem (synCfv (synCwppconcrete6fn) (synCtc (synCtc (synCtc
                  (synCtc (synCtc (synCtc (synCtc (synChncard (synC1c))))))))))
          (synCncs)) (.classMem (synCfv (synCwppconcrete6fn) (.cv y)) (synCncs)))
      p0106 p0126
  have p0128 :=
    @gLectr
      (synCtc (synCtc (synCtc (synCtc (synCtc (synCtc (synChncard (synC1c))))))))
      (synCfv (synCwppconcrete6fn) (synCtc (synCtc
            (synCtc (synCtc (synCtc (synCtc (synCtc (synChncard (synC1c))))))))))
      (synCfv (synCwppconcrete6fn) (.cv y))
  have p0129 :=
    @gSyl6 (.classMem (.cv y) (synChwcards (synCvv)))
      (synWbr (.cv y) (synClec) (synCtc
          (synCtc (synCtc (synCtc (synCtc (synCtc (synChncard (synC1c)))))))))
      (synW3a (.classMem (synCtc
            (synCtc (synCtc (synCtc (synCtc (synCtc (synChncard (synC1c))))))))
          (synCncs)) (.classMem (synCfv (synCwppconcrete6fn) (synCtc (synCtc (synCtc
                  (synCtc (synCtc (synCtc (synCtc (synChncard (synC1c))))))))))
          (synCncs)) (.classMem (synCfv (synCwppconcrete6fn) (.cv y)) (synCncs)))
      (.imp (synWa (synWbr (synCtc
              (synCtc (synCtc (synCtc (synCtc (synCtc (synChncard (synC1c))))))))
            (synClec) (synCfv (synCwppconcrete6fn) (synCtc (synCtc (synCtc
                    (synCtc (synCtc (synCtc (synCtc (synChncard (synC1c)))))))))))
          (synWbr (synCfv (synCwppconcrete6fn) (synCtc (synCtc (synCtc
                    (synCtc (synCtc (synCtc (synCtc (synChncard (synC1c))))))))))
            (synClec) (synCfv (synCwppconcrete6fn) (.cv y)))) (synWbr (synCtc
            (synCtc (synCtc (synCtc (synCtc (synCtc (synChncard (synC1c))))))))
          (synClec) (synCfv (synCwppconcrete6fn) (.cv y))))
      p0127 p0128
  have p0130 :=
    @gSyldd (.classMem (.cv y) (synChwcards (synCvv)))
      (synWbr (.cv y) (synClec) (synCtc
          (synCtc (synCtc (synCtc (synCtc (synCtc (synChncard (synC1c)))))))))
      (synWa (synWwpp) (synWbr (synCtc (synCtc
              (synCtc (synCtc (synCtc (synCtc (synCtc (synChncard (synC1c)))))))))
          (synClec) (.cv y)))
      (synWa (synWbr (synCtc
            (synCtc (synCtc (synCtc (synCtc (synCtc (synChncard (synC1c))))))))
          (synClec) (synCfv (synCwppconcrete6fn) (synCtc (synCtc (synCtc
                  (synCtc (synCtc (synCtc (synCtc (synChncard (synC1c))))))))))) (synWbr
          (synCfv (synCwppconcrete6fn) (synCtc (synCtc (synCtc
                  (synCtc (synCtc (synCtc (synCtc (synChncard (synC1c))))))))))
          (synClec) (synCfv (synCwppconcrete6fn) (.cv y))))
      (synWbr (synCtc
          (synCtc (synCtc (synCtc (synCtc (synCtc (synChncard (synC1c))))))))
        (synClec) (synCfv (synCwppconcrete6fn) (.cv y)))
      p0091 p0129
  have p0131 :=
    @gExp4a (.classMem (.cv y) (synChwcards (synCvv)))
      (synWbr (.cv y) (synClec) (synCtc
          (synCtc (synCtc (synCtc (synCtc (synCtc (synChncard (synC1c)))))))))
      (synWwpp)
      (synWbr (synCtc (synCtc
            (synCtc (synCtc (synCtc (synCtc (synCtc (synChncard (synC1c)))))))))
        (synClec) (.cv y))
      (synWbr (synCtc
          (synCtc (synCtc (synCtc (synCtc (synCtc (synChncard (synC1c))))))))
        (synClec) (synCfv (synCwppconcrete6fn) (.cv y)))
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

/-- Checked nominal proof certificate identified upstream as
`g_wppconcrete6stoppedgrowthfrompointndv`.
-/
@[expose]
noncomputable def gWppconcrete6stoppedgrowthfrompointndv (y : Var)
    (hyp_wppconcrete6stoppedgrowthfrompointndv_1 : Nominal.NPrf (.imp (synWwpp) (synWbr
            (synCtc (synCtc (synCtc (synCtc (synCtc (synCtc (synChncard (synC1c))))))))
            (synClec) (synCfv (synCwppconcrete6fn) (synCtc (synCtc (synCtc (synCtc
                      (synCtc (synCtc (synCtc (synChncard (synC1c))))))))))))) :
    Nominal.NPrf
      (.imp (synWwpp) (synWral y (synCdm (synCwppstopstep (synCwppconcrete6fn) (synCtc
                (synCtc (synCtc (synCtc (synCtc (synCtc (synChncard (synC1c))))))))))
          (.imp (synWbr (synCtc (synCtc (synCtc
                    (synCtc (synCtc (synCtc (synCtc (synChncard (synC1c)))))))))
              (synClec) (.cv y)) (synWbr (synCtc
                (synCtc (synCtc (synCtc (synCtc (synCtc (synChncard (synC1c))))))))
              (synClec) (synCfv (synCwppstopstep (synCwppconcrete6fn) (synCtc (synCtc
                      (synCtc (synCtc (synCtc (synCtc (synChncard (synC1c)))))))))
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
  have dv_cache_0002 : p ∉ ((synChwcards (synCvv))).fv :=
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
      ((Wff.imp (synWbr (.cv y) (synClec) (synCtc
              (synCtc (synCtc (synCtc (synCtc (synCtc (synChncard (synC1c)))))))))
          (.classMem (.cv y) (synCdm (synCwppconcrete6fn))))).fv :=
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
  have dv_cache_0004 : y ∉ ((synWwpp)).fv :=
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
    @gN3simpc (synWwpp)
      (.classMem (.cv y) (synCdm (synCwppstopstep (synCwppconcrete6fn) (synCtc (synCtc
                (synCtc (synCtc (synCtc (synCtc (synChncard (synC1c)))))))))))
      (synWbr (synCtc (synCtc
            (synCtc (synCtc (synCtc (synCtc (synCtc (synChncard (synC1c)))))))))
        (synClec) (.cv y))
  have p0001 :=
    @gSimpr
      (.classMem (.cv y) (synCdm (synCwppstopstep (synCwppconcrete6fn) (synCtc (synCtc
                (synCtc (synCtc (synCtc (synCtc (synChncard (synC1c)))))))))))
      (synWbr (synCtc (synCtc
            (synCtc (synCtc (synCtc (synCtc (synCtc (synChncard (synC1c)))))))))
        (synClec) (.cv y))
  have p0002 :=
    @gSyl
      (synW3a (synWwpp) (.classMem (.cv y) (synCdm (synCwppstopstep (synCwppconcrete6fn)
              (synCtc (synCtc
                  (synCtc (synCtc (synCtc (synCtc (synChncard (synC1c))))))))))) (synWbr
          (synCtc (synCtc
              (synCtc (synCtc (synCtc (synCtc (synCtc (synChncard (synC1c)))))))))
          (synClec) (.cv y)))
      (synWa (.classMem (.cv y) (synCdm (synCwppstopstep (synCwppconcrete6fn) (synCtc
                (synCtc (synCtc (synCtc (synCtc (synCtc (synChncard (synC1c)))))))))))
        (synWbr (synCtc (synCtc
              (synCtc (synCtc (synCtc (synCtc (synCtc (synChncard (synC1c)))))))))
          (synClec) (.cv y)))
      (synWbr (synCtc (synCtc
            (synCtc (synCtc (synCtc (synCtc (synCtc (synChncard (synC1c)))))))))
        (synClec) (.cv y))
      p0000 p0001
  have p0003 :=
    @gN3simpa (synWwpp)
      (.classMem (.cv y) (synCdm (synCwppstopstep (synCwppconcrete6fn) (synCtc (synCtc
                (synCtc (synCtc (synCtc (synCtc (synChncard (synC1c)))))))))))
      (synWbr (synCtc (synCtc
            (synCtc (synCtc (synCtc (synCtc (synCtc (synChncard (synC1c)))))))))
        (synClec) (.cv y))
  have p0004 :=
    @gSimpl (synWwpp)
      (.classMem (.cv y) (synCdm (synCwppstopstep (synCwppconcrete6fn) (synCtc (synCtc
                (synCtc (synCtc (synCtc (synCtc (synChncard (synC1c)))))))))))
  have p0005 :=
    @gSyl
      (synW3a (synWwpp) (.classMem (.cv y) (synCdm (synCwppstopstep (synCwppconcrete6fn)
              (synCtc (synCtc
                  (synCtc (synCtc (synCtc (synCtc (synChncard (synC1c))))))))))) (synWbr
          (synCtc (synCtc
              (synCtc (synCtc (synCtc (synCtc (synCtc (synChncard (synC1c)))))))))
          (synClec) (.cv y)))
      (synWa (synWwpp) (.classMem (.cv y) (synCdm (synCwppstopstep (synCwppconcrete6fn)
              (synCtc (synCtc
                  (synCtc (synCtc (synCtc (synCtc (synChncard (synC1c))))))))))))
      (synWwpp) p0003 p0004
  have p0007 :=
    @gSimpr (synWwpp)
      (.classMem (.cv y) (synCdm (synCwppstopstep (synCwppconcrete6fn) (synCtc (synCtc
                (synCtc (synCtc (synCtc (synCtc (synChncard (synC1c)))))))))))
  have p0008 :=
    @gSyl
      (synW3a (synWwpp) (.classMem (.cv y) (synCdm (synCwppstopstep (synCwppconcrete6fn)
              (synCtc (synCtc
                  (synCtc (synCtc (synCtc (synCtc (synChncard (synC1c))))))))))) (synWbr
          (synCtc (synCtc
              (synCtc (synCtc (synCtc (synCtc (synCtc (synChncard (synC1c)))))))))
          (synClec) (.cv y)))
      (synWa (synWwpp) (.classMem (.cv y) (synCdm (synCwppstopstep (synCwppconcrete6fn)
              (synCtc (synCtc
                  (synCtc (synCtc (synCtc (synCtc (synChncard (synC1c))))))))))))
      (.classMem (.cv y) (synCdm (synCwppstopstep (synCwppconcrete6fn) (synCtc (synCtc
                (synCtc (synCtc (synCtc (synCtc (synChncard (synC1c)))))))))))
      p0003 p0007
  have p0009 := @gWppconcrete6fnfunsndv
  have p0010 := @gWppconcrete6rnhwcardsndv
  have p0011 :=
    @gWppstopstepdmndv
      (synCtc (synCtc (synCtc (synCtc (synCtc (synCtc (synChncard (synC1c))))))))
      (synCwppconcrete6fn) p0009 p0010
  have p0012 :=
    @gEleq2i
      (synCdm (synCwppstopstep (synCwppconcrete6fn) (synCtc
            (synCtc (synCtc (synCtc (synCtc (synCtc (synChncard (synC1c))))))))))
      (synChwcards (synCvv)) (.cv y) p0011
  have p0013 :=
    @gBiimpi
      (.classMem (.cv y) (synCdm (synCwppstopstep (synCwppconcrete6fn) (synCtc (synCtc
                (synCtc (synCtc (synCtc (synCtc (synChncard (synC1c)))))))))))
      (.classMem (.cv y) (synChwcards (synCvv))) p0012
  have p0014 :=
    @gSyl
      (synW3a (synWwpp) (.classMem (.cv y) (synCdm (synCwppstopstep (synCwppconcrete6fn)
              (synCtc (synCtc
                  (synCtc (synCtc (synCtc (synCtc (synChncard (synC1c))))))))))) (synWbr
          (synCtc (synCtc
              (synCtc (synCtc (synCtc (synCtc (synCtc (synChncard (synC1c)))))))))
          (synClec) (.cv y)))
      (.classMem (.cv y) (synCdm (synCwppstopstep (synCwppconcrete6fn) (synCtc (synCtc
                (synCtc (synCtc (synCtc (synCtc (synChncard (synC1c)))))))))))
      (.classMem (.cv y) (synChwcards (synCvv))) p0008 p0013
  have p0015 :=
    @gWppconcrete6tcbandgrowthfrompointhwclecdndv y
      hyp_wppconcrete6stoppedgrowthfrompointndv_1
  have p0016 :=
    @gSyl
      (synW3a (synWwpp) (.classMem (.cv y) (synCdm (synCwppstopstep (synCwppconcrete6fn)
              (synCtc (synCtc
                  (synCtc (synCtc (synCtc (synCtc (synChncard (synC1c))))))))))) (synWbr
          (synCtc (synCtc
              (synCtc (synCtc (synCtc (synCtc (synCtc (synChncard (synC1c)))))))))
          (synClec) (.cv y)))
      (.classMem (.cv y) (synChwcards (synCvv)))
      (.imp (synWbr (.cv y) (synClec) (synCtc
            (synCtc (synCtc (synCtc (synCtc (synCtc (synChncard (synC1c)))))))))
        (.imp (synWwpp) (.imp (synWbr (synCtc (synCtc (synCtc
                    (synCtc (synCtc (synCtc (synCtc (synChncard (synC1c)))))))))
              (synClec) (.cv y)) (synWbr (synCtc
                (synCtc (synCtc (synCtc (synCtc (synCtc (synChncard (synC1c))))))))
              (synClec) (synCfv (synCwppconcrete6fn) (.cv y))))))
      p0014 p0015
  have p0017 :=
    @gMpid
      (synW3a (synWwpp) (.classMem (.cv y) (synCdm (synCwppstopstep (synCwppconcrete6fn)
              (synCtc (synCtc
                  (synCtc (synCtc (synCtc (synCtc (synChncard (synC1c))))))))))) (synWbr
          (synCtc (synCtc
              (synCtc (synCtc (synCtc (synCtc (synCtc (synChncard (synC1c)))))))))
          (synClec) (.cv y)))
      (synWbr (.cv y) (synClec) (synCtc
          (synCtc (synCtc (synCtc (synCtc (synCtc (synChncard (synC1c)))))))))
      (synWwpp)
      (.imp (synWbr (synCtc (synCtc
              (synCtc (synCtc (synCtc (synCtc (synCtc (synChncard (synC1c)))))))))
          (synClec) (.cv y)) (synWbr (synCtc
            (synCtc (synCtc (synCtc (synCtc (synCtc (synChncard (synC1c))))))))
          (synClec) (synCfv (synCwppconcrete6fn) (.cv y))))
      p0005 p0016
  have p0018 :=
    @gMpid
      (synW3a (synWwpp) (.classMem (.cv y) (synCdm (synCwppstopstep (synCwppconcrete6fn)
              (synCtc (synCtc
                  (synCtc (synCtc (synCtc (synCtc (synChncard (synC1c))))))))))) (synWbr
          (synCtc (synCtc
              (synCtc (synCtc (synCtc (synCtc (synCtc (synChncard (synC1c)))))))))
          (synClec) (.cv y)))
      (synWbr (.cv y) (synClec) (synCtc
          (synCtc (synCtc (synCtc (synCtc (synCtc (synChncard (synC1c)))))))))
      (synWbr (synCtc (synCtc
            (synCtc (synCtc (synCtc (synCtc (synCtc (synChncard (synC1c)))))))))
        (synClec) (.cv y))
      (synWbr (synCtc
          (synCtc (synCtc (synCtc (synCtc (synCtc (synChncard (synC1c))))))))
        (synClec) (synCfv (synCwppconcrete6fn) (.cv y)))
      p0002 p0017
  have p0019 :=
    @gImp
      (synW3a (synWwpp) (.classMem (.cv y) (synCdm (synCwppstopstep (synCwppconcrete6fn)
              (synCtc (synCtc
                  (synCtc (synCtc (synCtc (synCtc (synChncard (synC1c))))))))))) (synWbr
          (synCtc (synCtc
              (synCtc (synCtc (synCtc (synCtc (synCtc (synChncard (synC1c)))))))))
          (synClec) (.cv y)))
      (synWbr (.cv y) (synClec) (synCtc
          (synCtc (synCtc (synCtc (synCtc (synCtc (synChncard (synC1c)))))))))
      (synWbr (synCtc
          (synCtc (synCtc (synCtc (synCtc (synCtc (synChncard (synC1c))))))))
        (synClec) (synCfv (synCwppconcrete6fn) (.cv y)))
      p0018
  have p0038 := @gWppconcrete6hncard1dmcovndv p
  have p0039 := @gId (.classEq (.cv p) (.cv y))
  have p0040 :=
    @gBreq1d (.classEq (.cv p) (.cv y)) (.cv p) (.cv y)
      (synCtc (synCtc (synCtc (synCtc (synCtc (synCtc (synChncard (synC1c))))))))
      (synClec) p0039
  have p0042 :=
    @gEleq1d (.classEq (.cv p) (.cv y)) (.cv p) (.cv y) (synCdm (synCwppconcrete6fn))
      p0039
  have p0043 :=
    @gImbi12d (.classEq (.cv p) (.cv y))
      (synWbr (.cv p) (synClec) (synCtc
          (synCtc (synCtc (synCtc (synCtc (synCtc (synChncard (synC1c)))))))))
      (synWbr (.cv y) (synClec) (synCtc
          (synCtc (synCtc (synCtc (synCtc (synCtc (synChncard (synC1c)))))))))
      (.classMem (.cv p) (synCdm (synCwppconcrete6fn)))
      (.classMem (.cv y) (synCdm (synCwppconcrete6fn))) p0040 p0042
  have p0044 :=
    @gRspcv
      (.imp (synWbr (.cv p) (synClec) (synCtc
            (synCtc (synCtc (synCtc (synCtc (synCtc (synChncard (synC1c)))))))))
        (.classMem (.cv p) (synCdm (synCwppconcrete6fn))))
      (.imp (synWbr (.cv y) (synClec) (synCtc
            (synCtc (synCtc (synCtc (synCtc (synCtc (synChncard (synC1c)))))))))
        (.classMem (.cv y) (synCdm (synCwppconcrete6fn))))
      p (.cv y) (synChwcards (synCvv)) dv_cache_0001 dv_cache_0002 dv_cache_0003 p0043
  have p0045 :=
    @gMpi (.classMem (.cv y) (synChwcards (synCvv)))
      (synWral p (synChwcards (synCvv)) (.imp (synWbr (.cv p) (synClec) (synCtc
              (synCtc (synCtc (synCtc (synCtc (synCtc (synChncard (synC1c)))))))))
          (.classMem (.cv p) (synCdm (synCwppconcrete6fn)))))
      (.imp (synWbr (.cv y) (synClec) (synCtc
            (synCtc (synCtc (synCtc (synCtc (synCtc (synChncard (synC1c)))))))))
        (.classMem (.cv y) (synCdm (synCwppconcrete6fn))))
      p0038 p0044
  have p0046 :=
    @gSyl
      (synW3a (synWwpp) (.classMem (.cv y) (synCdm (synCwppstopstep (synCwppconcrete6fn)
              (synCtc (synCtc
                  (synCtc (synCtc (synCtc (synCtc (synChncard (synC1c))))))))))) (synWbr
          (synCtc (synCtc
              (synCtc (synCtc (synCtc (synCtc (synCtc (synChncard (synC1c)))))))))
          (synClec) (.cv y)))
      (.classMem (.cv y) (synChwcards (synCvv)))
      (.imp (synWbr (.cv y) (synClec) (synCtc
            (synCtc (synCtc (synCtc (synCtc (synCtc (synChncard (synC1c)))))))))
        (.classMem (.cv y) (synCdm (synCwppconcrete6fn))))
      p0014 p0045
  have p0047 :=
    @gJca
      (synW3a (synWwpp) (.classMem (.cv y) (synCdm (synCwppstopstep (synCwppconcrete6fn)
              (synCtc (synCtc
                  (synCtc (synCtc (synCtc (synCtc (synChncard (synC1c))))))))))) (synWbr
          (synCtc (synCtc
              (synCtc (synCtc (synCtc (synCtc (synCtc (synChncard (synC1c)))))))))
          (synClec) (.cv y)))
      (.classMem (.cv y) (synChwcards (synCvv)))
      (.imp (synWbr (.cv y) (synClec) (synCtc
            (synCtc (synCtc (synCtc (synCtc (synCtc (synChncard (synC1c)))))))))
        (.classMem (.cv y) (synCdm (synCwppconcrete6fn))))
      p0014 p0046
  have p0050 :=
    @gWppstopstepfvlecdndv (.cv y)
      (synCtc (synCtc (synCtc (synCtc (synCtc (synCtc (synChncard (synC1c))))))))
      (synCwppconcrete6fn) p0009 p0010
  have p0051 :=
    @gSyl
      (synW3a (synWwpp) (.classMem (.cv y) (synCdm (synCwppstopstep (synCwppconcrete6fn)
              (synCtc (synCtc
                  (synCtc (synCtc (synCtc (synCtc (synChncard (synC1c))))))))))) (synWbr
          (synCtc (synCtc
              (synCtc (synCtc (synCtc (synCtc (synCtc (synChncard (synC1c)))))))))
          (synClec) (.cv y)))
      (synWa (.classMem (.cv y) (synChwcards (synCvv))) (.imp (synWbr (.cv y) (synClec)
            (synCtc (synCtc (synCtc (synCtc (synCtc (synCtc (synChncard (synC1c)))))))))
          (.classMem (.cv y) (synCdm (synCwppconcrete6fn)))))
      (.imp (synWbr (.cv y) (synClec) (synCtc
            (synCtc (synCtc (synCtc (synCtc (synCtc (synChncard (synC1c)))))))))
        (.classEq (synCfv (synCwppstopstep (synCwppconcrete6fn) (synCtc (synCtc
                  (synCtc (synCtc (synCtc (synCtc (synChncard (synC1c))))))))) (.cv y))
          (synCfv (synCwppconcrete6fn) (.cv y))))
      p0047 p0050
  have p0052 :=
    @gImp
      (synW3a (synWwpp) (.classMem (.cv y) (synCdm (synCwppstopstep (synCwppconcrete6fn)
              (synCtc (synCtc
                  (synCtc (synCtc (synCtc (synCtc (synChncard (synC1c))))))))))) (synWbr
          (synCtc (synCtc
              (synCtc (synCtc (synCtc (synCtc (synCtc (synChncard (synC1c)))))))))
          (synClec) (.cv y)))
      (synWbr (.cv y) (synClec) (synCtc
          (synCtc (synCtc (synCtc (synCtc (synCtc (synChncard (synC1c)))))))))
      (.classEq (synCfv (synCwppstopstep (synCwppconcrete6fn) (synCtc
              (synCtc (synCtc (synCtc (synCtc (synCtc (synChncard (synC1c)))))))))
          (.cv y)) (synCfv (synCwppconcrete6fn) (.cv y)))
      p0051
  have p0053 :=
    @gBreq2d
      (synWa (synW3a (synWwpp) (.classMem (.cv y) (synCdm
              (synCwppstopstep (synCwppconcrete6fn) (synCtc (synCtc
                    (synCtc (synCtc (synCtc (synCtc (synChncard (synC1c)))))))))))
          (synWbr (synCtc (synCtc (synCtc
                  (synCtc (synCtc (synCtc (synCtc (synChncard (synC1c)))))))))
            (synClec) (.cv y))) (synWbr (.cv y) (synClec) (synCtc
            (synCtc (synCtc (synCtc (synCtc (synCtc (synChncard (synC1c))))))))))
      (synCfv (synCwppstopstep (synCwppconcrete6fn) (synCtc
            (synCtc (synCtc (synCtc (synCtc (synCtc (synChncard (synC1c))))))))) (.cv y))
      (synCfv (synCwppconcrete6fn) (.cv y))
      (synCtc (synCtc (synCtc (synCtc (synCtc (synCtc (synChncard (synC1c))))))))
      (synClec) p0052
  have p0054 :=
    @gBiimprd
      (synWa (synW3a (synWwpp) (.classMem (.cv y) (synCdm
              (synCwppstopstep (synCwppconcrete6fn) (synCtc (synCtc
                    (synCtc (synCtc (synCtc (synCtc (synChncard (synC1c)))))))))))
          (synWbr (synCtc (synCtc (synCtc
                  (synCtc (synCtc (synCtc (synCtc (synChncard (synC1c)))))))))
            (synClec) (.cv y))) (synWbr (.cv y) (synClec) (synCtc
            (synCtc (synCtc (synCtc (synCtc (synCtc (synChncard (synC1c))))))))))
      (synWbr (synCtc
          (synCtc (synCtc (synCtc (synCtc (synCtc (synChncard (synC1c)))))))) (synClec)
        (synCfv (synCwppstopstep (synCwppconcrete6fn) (synCtc
              (synCtc (synCtc (synCtc (synCtc (synCtc (synChncard (synC1c)))))))))
          (.cv y)))
      (synWbr (synCtc
          (synCtc (synCtc (synCtc (synCtc (synCtc (synChncard (synC1c))))))))
        (synClec) (synCfv (synCwppconcrete6fn) (.cv y)))
      p0053
  have p0055 :=
    @gMpd
      (synWa (synW3a (synWwpp) (.classMem (.cv y) (synCdm
              (synCwppstopstep (synCwppconcrete6fn) (synCtc (synCtc
                    (synCtc (synCtc (synCtc (synCtc (synChncard (synC1c)))))))))))
          (synWbr (synCtc (synCtc (synCtc
                  (synCtc (synCtc (synCtc (synCtc (synChncard (synC1c)))))))))
            (synClec) (.cv y))) (synWbr (.cv y) (synClec) (synCtc
            (synCtc (synCtc (synCtc (synCtc (synCtc (synChncard (synC1c))))))))))
      (synWbr (synCtc
          (synCtc (synCtc (synCtc (synCtc (synCtc (synChncard (synC1c))))))))
        (synClec) (synCfv (synCwppconcrete6fn) (.cv y)))
      (synWbr (synCtc
          (synCtc (synCtc (synCtc (synCtc (synCtc (synChncard (synC1c)))))))) (synClec)
        (synCfv (synCwppstopstep (synCwppconcrete6fn) (synCtc
              (synCtc (synCtc (synCtc (synCtc (synCtc (synChncard (synC1c)))))))))
          (.cv y)))
      p0019 p0054
  have p0056 :=
    @gEx
      (synW3a (synWwpp) (.classMem (.cv y) (synCdm (synCwppstopstep (synCwppconcrete6fn)
              (synCtc (synCtc
                  (synCtc (synCtc (synCtc (synCtc (synChncard (synC1c))))))))))) (synWbr
          (synCtc (synCtc
              (synCtc (synCtc (synCtc (synCtc (synCtc (synChncard (synC1c)))))))))
          (synClec) (.cv y)))
      (synWbr (.cv y) (synClec) (synCtc
          (synCtc (synCtc (synCtc (synCtc (synCtc (synChncard (synC1c)))))))))
      (synWbr (synCtc
          (synCtc (synCtc (synCtc (synCtc (synCtc (synChncard (synC1c)))))))) (synClec)
        (synCfv (synCwppstopstep (synCwppconcrete6fn) (synCtc
              (synCtc (synCtc (synCtc (synCtc (synCtc (synChncard (synC1c)))))))))
          (.cv y)))
      p0055
  have p0066 := @gWppconcrete6thresholdhwcardsndv
  have p0067 :=
    @gA1i
      (.classMem (synCtc
          (synCtc (synCtc (synCtc (synCtc (synCtc (synChncard (synC1c))))))))
        (synChwcards (synCvv)))
      (synW3a (synWwpp) (.classMem (.cv y) (synCdm (synCwppstopstep (synCwppconcrete6fn)
              (synCtc (synCtc
                  (synCtc (synCtc (synCtc (synCtc (synChncard (synC1c))))))))))) (synWbr
          (synCtc (synCtc
              (synCtc (synCtc (synCtc (synCtc (synCtc (synChncard (synC1c)))))))))
          (synClec) (.cv y)))
      p0066
  have p0068 :=
    @gJca
      (synW3a (synWwpp) (.classMem (.cv y) (synCdm (synCwppstopstep (synCwppconcrete6fn)
              (synCtc (synCtc
                  (synCtc (synCtc (synCtc (synCtc (synChncard (synC1c))))))))))) (synWbr
          (synCtc (synCtc
              (synCtc (synCtc (synCtc (synCtc (synCtc (synChncard (synC1c)))))))))
          (synClec) (.cv y)))
      (.classMem (.cv y) (synChwcards (synCvv)))
      (.classMem (synCtc
          (synCtc (synCtc (synCtc (synCtc (synCtc (synChncard (synC1c))))))))
        (synChwcards (synCvv)))
      p0014 p0067
  have p0069 :=
    @gHwcardslecconnexndv (.cv y)
      (synCtc (synCtc (synCtc (synCtc (synCtc (synCtc (synChncard (synC1c))))))))
  have p0070 :=
    @gSyl
      (synW3a (synWwpp) (.classMem (.cv y) (synCdm (synCwppstopstep (synCwppconcrete6fn)
              (synCtc (synCtc
                  (synCtc (synCtc (synCtc (synCtc (synChncard (synC1c))))))))))) (synWbr
          (synCtc (synCtc
              (synCtc (synCtc (synCtc (synCtc (synCtc (synChncard (synC1c)))))))))
          (synClec) (.cv y)))
      (synWa (.classMem (.cv y) (synChwcards (synCvv))) (.classMem (synCtc
            (synCtc (synCtc (synCtc (synCtc (synCtc (synChncard (synC1c))))))))
          (synChwcards (synCvv))))
      (synWo (synWbr (.cv y) (synClec) (synCtc
            (synCtc (synCtc (synCtc (synCtc (synCtc (synChncard (synC1c))))))))) (synWbr
          (synCtc (synCtc (synCtc (synCtc (synCtc (synCtc (synChncard (synC1c))))))))
          (synClec) (.cv y)))
      p0068 p0069
  have p0071 :=
    @gOrd
      (synW3a (synWwpp) (.classMem (.cv y) (synCdm (synCwppstopstep (synCwppconcrete6fn)
              (synCtc (synCtc
                  (synCtc (synCtc (synCtc (synCtc (synChncard (synC1c))))))))))) (synWbr
          (synCtc (synCtc
              (synCtc (synCtc (synCtc (synCtc (synCtc (synChncard (synC1c)))))))))
          (synClec) (.cv y)))
      (synWbr (.cv y) (synClec) (synCtc
          (synCtc (synCtc (synCtc (synCtc (synCtc (synChncard (synC1c)))))))))
      (synWbr (synCtc
          (synCtc (synCtc (synCtc (synCtc (synCtc (synChncard (synC1c))))))))
        (synClec) (.cv y))
      p0070
  have p0072 :=
    @gImp
      (synW3a (synWwpp) (.classMem (.cv y) (synCdm (synCwppstopstep (synCwppconcrete6fn)
              (synCtc (synCtc
                  (synCtc (synCtc (synCtc (synCtc (synChncard (synC1c))))))))))) (synWbr
          (synCtc (synCtc
              (synCtc (synCtc (synCtc (synCtc (synCtc (synChncard (synC1c)))))))))
          (synClec) (.cv y)))
      (.neg (synWbr (.cv y) (synClec) (synCtc
            (synCtc (synCtc (synCtc (synCtc (synCtc (synChncard (synC1c))))))))))
      (synWbr (synCtc
          (synCtc (synCtc (synCtc (synCtc (synCtc (synChncard (synC1c))))))))
        (synClec) (.cv y))
      p0071
  have p0103 :=
    @gWppstopstepfvnlecdndv (.cv y)
      (synCtc (synCtc (synCtc (synCtc (synCtc (synCtc (synChncard (synC1c))))))))
      (synCwppconcrete6fn) p0009 p0010
  have p0104 :=
    @gSyl
      (synW3a (synWwpp) (.classMem (.cv y) (synCdm (synCwppstopstep (synCwppconcrete6fn)
              (synCtc (synCtc
                  (synCtc (synCtc (synCtc (synCtc (synChncard (synC1c))))))))))) (synWbr
          (synCtc (synCtc
              (synCtc (synCtc (synCtc (synCtc (synCtc (synChncard (synC1c)))))))))
          (synClec) (.cv y)))
      (synWa (.classMem (.cv y) (synChwcards (synCvv))) (.imp (synWbr (.cv y) (synClec)
            (synCtc (synCtc (synCtc (synCtc (synCtc (synCtc (synChncard (synC1c)))))))))
          (.classMem (.cv y) (synCdm (synCwppconcrete6fn)))))
      (.imp (.neg (synWbr (.cv y) (synClec) (synCtc
              (synCtc (synCtc (synCtc (synCtc (synCtc (synChncard (synC1c))))))))))
        (.classEq (synCfv (synCwppstopstep (synCwppconcrete6fn) (synCtc (synCtc
                  (synCtc (synCtc (synCtc (synCtc (synChncard (synC1c))))))))) (.cv y))
          (.cv y)))
      p0047 p0103
  have p0105 :=
    @gImp
      (synW3a (synWwpp) (.classMem (.cv y) (synCdm (synCwppstopstep (synCwppconcrete6fn)
              (synCtc (synCtc
                  (synCtc (synCtc (synCtc (synCtc (synChncard (synC1c))))))))))) (synWbr
          (synCtc (synCtc
              (synCtc (synCtc (synCtc (synCtc (synCtc (synChncard (synC1c)))))))))
          (synClec) (.cv y)))
      (.neg (synWbr (.cv y) (synClec) (synCtc
            (synCtc (synCtc (synCtc (synCtc (synCtc (synChncard (synC1c))))))))))
      (.classEq (synCfv (synCwppstopstep (synCwppconcrete6fn) (synCtc
              (synCtc (synCtc (synCtc (synCtc (synCtc (synChncard (synC1c)))))))))
          (.cv y)) (.cv y))
      p0104
  have p0106 :=
    @gBreq2d
      (synWa (synW3a (synWwpp) (.classMem (.cv y) (synCdm
              (synCwppstopstep (synCwppconcrete6fn) (synCtc (synCtc
                    (synCtc (synCtc (synCtc (synCtc (synChncard (synC1c)))))))))))
          (synWbr (synCtc (synCtc (synCtc
                  (synCtc (synCtc (synCtc (synCtc (synChncard (synC1c)))))))))
            (synClec) (.cv y))) (.neg (synWbr (.cv y) (synClec) (synCtc (synCtc
                (synCtc (synCtc (synCtc (synCtc (synChncard (synC1c)))))))))))
      (synCfv (synCwppstopstep (synCwppconcrete6fn) (synCtc
            (synCtc (synCtc (synCtc (synCtc (synCtc (synChncard (synC1c))))))))) (.cv y))
      (.cv y)
      (synCtc (synCtc (synCtc (synCtc (synCtc (synCtc (synChncard (synC1c))))))))
      (synClec) p0105
  have p0107 :=
    @gBiimprd
      (synWa (synW3a (synWwpp) (.classMem (.cv y) (synCdm
              (synCwppstopstep (synCwppconcrete6fn) (synCtc (synCtc
                    (synCtc (synCtc (synCtc (synCtc (synChncard (synC1c)))))))))))
          (synWbr (synCtc (synCtc (synCtc
                  (synCtc (synCtc (synCtc (synCtc (synChncard (synC1c)))))))))
            (synClec) (.cv y))) (.neg (synWbr (.cv y) (synClec) (synCtc (synCtc
                (synCtc (synCtc (synCtc (synCtc (synChncard (synC1c)))))))))))
      (synWbr (synCtc
          (synCtc (synCtc (synCtc (synCtc (synCtc (synChncard (synC1c)))))))) (synClec)
        (synCfv (synCwppstopstep (synCwppconcrete6fn) (synCtc
              (synCtc (synCtc (synCtc (synCtc (synCtc (synChncard (synC1c)))))))))
          (.cv y)))
      (synWbr (synCtc
          (synCtc (synCtc (synCtc (synCtc (synCtc (synChncard (synC1c))))))))
        (synClec) (.cv y))
      p0106
  have p0108 :=
    @gMpd
      (synWa (synW3a (synWwpp) (.classMem (.cv y) (synCdm
              (synCwppstopstep (synCwppconcrete6fn) (synCtc (synCtc
                    (synCtc (synCtc (synCtc (synCtc (synChncard (synC1c)))))))))))
          (synWbr (synCtc (synCtc (synCtc
                  (synCtc (synCtc (synCtc (synCtc (synChncard (synC1c)))))))))
            (synClec) (.cv y))) (.neg (synWbr (.cv y) (synClec) (synCtc (synCtc
                (synCtc (synCtc (synCtc (synCtc (synChncard (synC1c)))))))))))
      (synWbr (synCtc
          (synCtc (synCtc (synCtc (synCtc (synCtc (synChncard (synC1c))))))))
        (synClec) (.cv y))
      (synWbr (synCtc
          (synCtc (synCtc (synCtc (synCtc (synCtc (synChncard (synC1c)))))))) (synClec)
        (synCfv (synCwppstopstep (synCwppconcrete6fn) (synCtc
              (synCtc (synCtc (synCtc (synCtc (synCtc (synChncard (synC1c)))))))))
          (.cv y)))
      p0072 p0107
  have p0109 :=
    @gEx
      (synW3a (synWwpp) (.classMem (.cv y) (synCdm (synCwppstopstep (synCwppconcrete6fn)
              (synCtc (synCtc
                  (synCtc (synCtc (synCtc (synCtc (synChncard (synC1c))))))))))) (synWbr
          (synCtc (synCtc
              (synCtc (synCtc (synCtc (synCtc (synCtc (synChncard (synC1c)))))))))
          (synClec) (.cv y)))
      (.neg (synWbr (.cv y) (synClec) (synCtc
            (synCtc (synCtc (synCtc (synCtc (synCtc (synChncard (synC1c))))))))))
      (synWbr (synCtc
          (synCtc (synCtc (synCtc (synCtc (synCtc (synChncard (synC1c)))))))) (synClec)
        (synCfv (synCwppstopstep (synCwppconcrete6fn) (synCtc
              (synCtc (synCtc (synCtc (synCtc (synCtc (synChncard (synC1c)))))))))
          (.cv y)))
      p0108
  have p0110 :=
    @gPm261d
      (synW3a (synWwpp) (.classMem (.cv y) (synCdm (synCwppstopstep (synCwppconcrete6fn)
              (synCtc (synCtc
                  (synCtc (synCtc (synCtc (synCtc (synChncard (synC1c))))))))))) (synWbr
          (synCtc (synCtc
              (synCtc (synCtc (synCtc (synCtc (synCtc (synChncard (synC1c)))))))))
          (synClec) (.cv y)))
      (synWbr (.cv y) (synClec) (synCtc
          (synCtc (synCtc (synCtc (synCtc (synCtc (synChncard (synC1c)))))))))
      (synWbr (synCtc
          (synCtc (synCtc (synCtc (synCtc (synCtc (synChncard (synC1c)))))))) (synClec)
        (synCfv (synCwppstopstep (synCwppconcrete6fn) (synCtc
              (synCtc (synCtc (synCtc (synCtc (synCtc (synChncard (synC1c)))))))))
          (.cv y)))
      p0056 p0109
  have p0111 :=
    @gN3exp (synWwpp)
      (.classMem (.cv y) (synCdm (synCwppstopstep (synCwppconcrete6fn) (synCtc (synCtc
                (synCtc (synCtc (synCtc (synCtc (synChncard (synC1c)))))))))))
      (synWbr (synCtc (synCtc
            (synCtc (synCtc (synCtc (synCtc (synCtc (synChncard (synC1c)))))))))
        (synClec) (.cv y))
      (synWbr (synCtc
          (synCtc (synCtc (synCtc (synCtc (synCtc (synChncard (synC1c)))))))) (synClec)
        (synCfv (synCwppstopstep (synCwppconcrete6fn) (synCtc
              (synCtc (synCtc (synCtc (synCtc (synCtc (synChncard (synC1c)))))))))
          (.cv y)))
      p0110
  have p0112 :=
    @gRalrimiv (synWwpp)
      (.imp (synWbr (synCtc (synCtc
              (synCtc (synCtc (synCtc (synCtc (synCtc (synChncard (synC1c)))))))))
          (synClec) (.cv y)) (synWbr (synCtc
            (synCtc (synCtc (synCtc (synCtc (synCtc (synChncard (synC1c))))))))
          (synClec) (synCfv (synCwppstopstep (synCwppconcrete6fn) (synCtc (synCtc
                  (synCtc (synCtc (synCtc (synCtc (synChncard (synC1c))))))))) (.cv y))))
      y
      (synCdm (synCwppstopstep (synCwppconcrete6fn) (synCtc
            (synCtc (synCtc (synCtc (synCtc (synCtc (synChncard (synC1c))))))))))
      dv_cache_0004 p0111
  exact p0112

/-- Checked nominal proof certificate identified upstream as `g_wppconcrete6notwppfrompointndv`. -/
@[expose]
noncomputable def gWppconcrete6notwppfrompointndv
    (hyp_wppconcrete6notwppfrompointndv_1 : Nominal.NPrf (.imp (synWwpp) (synWbr (synCtc
              (synCtc (synCtc (synCtc (synCtc (synCtc (synChncard (synC1c))))))))
            (synClec) (synCfv (synCwppconcrete6fn) (synCtc (synCtc (synCtc (synCtc
                      (synCtc (synCtc (synCtc (synChncard (synC1c))))))))))))) :
    Nominal.NPrf (.neg (synWwpp)) :=
  by
  let proofSupport : Finset Var := (∅ : Finset Var)
  let y : Var := freshVar proofSupport 0
  have p0000 := @gEqid (synC0c)
  have p0001 := @gNotnoti (.classEq (synC0c) (synC0c)) p0000
  have p0002 :=
    @gWppconcrete6stoppedgrowthfrompointndv y hyp_wppconcrete6notwppfrompointndv_1
  have p0003 := @gN1cex
  have p0004 := @gPw1ex (synC1c) p0003
  have p0005 := @gPw1ex (synCpw1 (synC1c)) p0004
  have p0006 := @gPw1ex (synCpw1 (synCpw1 (synC1c))) p0005
  have p0007 := @gPw1ex (synCpw1 (synCpw1 (synCpw1 (synC1c)))) p0006
  have p0008 := @gPw1ex (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c))))) p0007
  have p0009 :=
    @gPw1ex (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c)))))) p0008
  have p0010 :=
    @gHncardtc2nodomndv
      (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c))))))) p0009
  have p0011 := @gWppconcrete6stoppedgammacontrgrowthstagedndv y p0010
  have p0012 :=
    @gSyl (synWwpp)
      (synWral y (synCdm (synCwppstopstep (synCwppconcrete6fn) (synCtc
              (synCtc (synCtc (synCtc (synCtc (synCtc (synChncard (synC1c)))))))))) (.imp
          (synWbr (synCtc (synCtc (synCtc
                  (synCtc (synCtc (synCtc (synCtc (synChncard (synC1c)))))))))
            (synClec) (.cv y)) (synWbr (synCtc
              (synCtc (synCtc (synCtc (synCtc (synCtc (synChncard (synC1c))))))))
            (synClec) (synCfv (synCwppstopstep (synCwppconcrete6fn) (synCtc (synCtc
                    (synCtc (synCtc (synCtc (synCtc (synChncard (synC1c)))))))))
              (.cv y)))))
      (.neg (.classEq (synC0c) (synC0c))) p0002 p0011
  have p0013 := @gMto (synWwpp) (.neg (.classEq (synC0c) (synC0c))) p0001 p0012
  exact p0013

/-- Checked nominal proof certificate identified upstream as `g_hwcnselfbasendv`. -/
@[expose]
noncomputable def gHwcnselfbasendv (u : Var) (A : Class) (dv_A_u : u ∉ A.fv) :
    Nominal.NPrf
      (.imp (.classMem (.cv u) (synChwcn A))
        (.classMem (.cv u) (synChwcn (synCfv (synC2nd) (.cv u))))) :=
  by
  have dv_cache_0001 : u ∉ (A).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : u ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_A_u, not_false_eq_true])
  have p0000 := @gHwcnwendv u A dv_cache_0001
  have p0001 := @gSsid (synCfv (synC2nd) (.cv u))
  have p0002 :=
    @gA1i (synWss (synCfv (synC2nd) (.cv u)) (synCfv (synC2nd) (.cv u)))
      (.classMem (.cv u) (synChwcn A)) p0001
  have p0003 :=
    @gJca (.classMem (.cv u) (synChwcn A))
      (synWbr (synCfv (synC1st) (.cv u)) (synCwe) (synCfv (synC2nd) (.cv u)))
      (synWss (synCfv (synC2nd) (.cv u)) (synCfv (synC2nd) (.cv u))) p0000 p0002
  have p0004 := @gFvex (.cv u) (synC1st)
  have p0005 := @gFvex (.cv u) (synC2nd)
  have p0006 :=
    @gElhwcodesclndv (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u))
      (synCfv (synC2nd) (.cv u)) p0004 p0005
  have p0007 :=
    @gSylibr (.classMem (.cv u) (synChwcn A))
      (synWa (synWbr (synCfv (synC1st) (.cv u)) (synCwe) (synCfv (synC2nd) (.cv u)))
        (synWss (synCfv (synC2nd) (.cv u)) (synCfv (synC2nd) (.cv u))))
      (.classMem (synCop (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u)))
        (synChwcodes (synCfv (synC2nd) (.cv u))))
      p0003 p0006
  have p0008 := @gHwcnpair u A
  have p0009 :=
    @gEleq1d (.classMem (.cv u) (synChwcn A)) (.cv u)
      (synCop (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u)))
      (synChwcodes (synCfv (synC2nd) (.cv u))) p0008
  have p0010 :=
    @gMpbird (.classMem (.cv u) (synChwcn A))
      (.classMem (.cv u) (synChwcodes (synCfv (synC2nd) (.cv u))))
      (.classMem (synCop (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u)))
        (synChwcodes (synCfv (synC2nd) (.cv u))))
      p0007 p0009
  have p0011 := @gHwcnsupp u A
  have p0012 :=
    @gJca (.classMem (.cv u) (synChwcn A))
      (.classMem (.cv u) (synChwcodes (synCfv (synC2nd) (.cv u))))
      (synWss (synCfv (synC1st) (.cv u))
        (synCxp (synCfv (synC2nd) (.cv u)) (synCfv (synC2nd) (.cv u))))
      p0010 p0011
  have p0013 := @gElex (.cv u) (synChwcn A)
  have p0014 := @gElhwcncl (synCfv (synC2nd) (.cv u)) (.cv u)
  have p0015 :=
    @gSyl (.classMem (.cv u) (synChwcn A)) (.classMem (.cv u) (synCvv))
      (synWb (.classMem (.cv u) (synChwcn (synCfv (synC2nd) (.cv u))))
        (synWa (.classMem (.cv u) (synChwcodes (synCfv (synC2nd) (.cv u))))
          (synWss (synCfv (synC1st) (.cv u))
            (synCxp (synCfv (synC2nd) (.cv u)) (synCfv (synC2nd) (.cv u))))))
      p0013 p0014
  have p0016 :=
    @gMpbird (.classMem (.cv u) (synChwcn A))
      (.classMem (.cv u) (synChwcn (synCfv (synC2nd) (.cv u))))
      (synWa (.classMem (.cv u) (synChwcodes (synCfv (synC2nd) (.cv u))))
        (synWss (synCfv (synC1st) (.cv u))
          (synCxp (synCfv (synC2nd) (.cv u)) (synCfv (synC2nd) (.cv u)))))
      p0012 p0015
  exact p0016

/-- Checked nominal proof certificate identified upstream as `g_hnpw13quoshiftf1ondv`. -/
@[expose]
noncomputable def gHnpw13quoshiftf1ondv (A : Class)
    (hyp_hnpw13quoshiftf1ondv_1 : Nominal.NPrf (.classMem A (synCvv))) :
    Nominal.NPrf
      (synWf1o (synCcom (synChnsiquomap (synCpw1 (synCpw1 A)))
          (synCcom (synCsi (synChnsiquomap (synCpw1 A)))
            (synCsi (synCsi (synChnsiquomap A)))))
        (synCpw1 (synCpw1 (synCpw1 (synChnord A))))
        (synChnord (synCpw1 (synCpw1 (synCpw1 A))))) :=
  by
  have p0000 := @gPw1ex A hyp_hnpw13quoshiftf1ondv_1
  have p0001 := @gPw1ex (synCpw1 A) p0000
  have p0002 := @gHnsiquomapf1ondv (synCpw1 (synCpw1 A)) p0001
  have p0004 := @gHnsiquomapf1ondv (synCpw1 A) p0000
  have p0005 :=
    @gPw1sif1omapndv (synCpw1 (synChnord (synCpw1 A)))
      (synChnord (synCpw1 (synCpw1 A))) (synChnsiquomap (synCpw1 A))
  have p0006 := Nominal.mp p0004 p0005
  have p0007 := @gHnsiquomapf1ondv A hyp_hnpw13quoshiftf1ondv_1
  have p0008 :=
    @gPw1sif1omapndv (synCpw1 (synChnord A)) (synChnord (synCpw1 A))
      (synChnsiquomap A)
  have p0009 := Nominal.mp p0007 p0008
  have p0010 :=
    @gPw1sif1omapndv (synCpw1 (synCpw1 (synChnord A)))
      (synCpw1 (synChnord (synCpw1 A))) (synCsi (synChnsiquomap A))
  have p0011 := Nominal.mp p0009 p0010
  have p0012 :=
    @gPm32i
      (synWf1o (synCsi (synChnsiquomap (synCpw1 A)))
        (synCpw1 (synCpw1 (synChnord (synCpw1 A))))
        (synCpw1 (synChnord (synCpw1 (synCpw1 A)))))
      (synWf1o (synCsi (synCsi (synChnsiquomap A)))
        (synCpw1 (synCpw1 (synCpw1 (synChnord A))))
        (synCpw1 (synCpw1 (synChnord (synCpw1 A)))))
      p0006 p0011
  have p0013 :=
    @gF1oco (synCpw1 (synCpw1 (synCpw1 (synChnord A))))
      (synCpw1 (synCpw1 (synChnord (synCpw1 A))))
      (synCpw1 (synChnord (synCpw1 (synCpw1 A))))
      (synCsi (synChnsiquomap (synCpw1 A))) (synCsi (synCsi (synChnsiquomap A)))
  have p0014 := Nominal.mp p0012 p0013
  have p0015 :=
    @gPm32i
      (synWf1o (synChnsiquomap (synCpw1 (synCpw1 A)))
        (synCpw1 (synChnord (synCpw1 (synCpw1 A))))
        (synChnord (synCpw1 (synCpw1 (synCpw1 A)))))
      (synWf1o (synCcom (synCsi (synChnsiquomap (synCpw1 A)))
          (synCsi (synCsi (synChnsiquomap A))))
        (synCpw1 (synCpw1 (synCpw1 (synChnord A))))
        (synCpw1 (synChnord (synCpw1 (synCpw1 A)))))
      p0002 p0014
  have p0016 :=
    @gF1oco (synCpw1 (synCpw1 (synCpw1 (synChnord A))))
      (synCpw1 (synChnord (synCpw1 (synCpw1 A))))
      (synChnord (synCpw1 (synCpw1 (synCpw1 A))))
      (synChnsiquomap (synCpw1 (synCpw1 A)))
      (synCcom (synCsi (synChnsiquomap (synCpw1 A)))
        (synCsi (synCsi (synChnsiquomap A))))
  have p0017 := Nominal.mp p0015 p0016
  exact p0017

/-- Checked nominal proof certificate identified upstream as `g_hnqcommonprecoverinjndv`. -/
@[expose]
noncomputable def gHnqcommonprecoverinjndv (D : Class) (S : Class) (E : Class)
    (J : Class) (hyp_hnqcommonprecoverinjndv_1 : Nominal.NPrf (.classMem D (synCvv)))
    (hyp_hnqcommonprecoverinjndv_2 : Nominal.NPrf (.classMem E (synCvv)))
    (hyp_hnqcommonprecoverinjndv_3 : Nominal.NPrf (synWf1 J S (synChnord D))) :
    Nominal.NPrf
      (.imp (synWss (synCima (synCcom (synChnqinc D (synCun D E)) J) S)
          (synCrn (synChnqinc E (synCun D E)))) (synWf1 (synCres
            (synCcom (synCcnv (synChnqinc E (synCun D E)))
              (synCcom (synChnqinc D (synCun D E)) J)) S) S (synChnord E))) :=
  by
  have p0000 := @gSsun2 E D
  have p0001 := @gUnex D E hyp_hnqcommonprecoverinjndv_1 hyp_hnqcommonprecoverinjndv_2
  have p0002 := @gHnqincf1 (synCun D E) E p0000 hyp_hnqcommonprecoverinjndv_2 p0001
  have p0003 :=
    @gF1cnv (synChnord E) (synChnord (synCun D E)) (synChnqinc E (synCun D E))
  have p0004 := Nominal.mp p0002 p0003
  have p0005 :=
    @gF1of1 (synCrn (synChnqinc E (synCun D E))) (synChnord E)
      (synCcnv (synChnqinc E (synCun D E)))
  have p0006 := Nominal.mp p0004 p0005
  have p0007 :=
    @gA1i
      (synWf1 (synCcnv (synChnqinc E (synCun D E)))
        (synCrn (synChnqinc E (synCun D E))) (synChnord E))
      (synWss (synCima (synCcom (synChnqinc D (synCun D E)) J) S)
        (synCrn (synChnqinc E (synCun D E))))
      p0006
  have p0008 := @gSsun1 D E
  have p0010 := @gHnqincf1 (synCun D E) D p0008 hyp_hnqcommonprecoverinjndv_1 p0001
  have p0011 :=
    @gPm32i
      (synWf1 (synChnqinc D (synCun D E)) (synChnord D) (synChnord (synCun D E)))
      (synWf1 J S (synChnord D)) p0010 hyp_hnqcommonprecoverinjndv_3
  have p0012 :=
    @gF1co S (synChnord D) (synChnord (synCun D E)) (synChnqinc D (synCun D E)) J
  have p0013 := Nominal.mp p0011 p0012
  have p0014 := @gSsid S
  have p0015 :=
    @gPm32i
      (synWf1 (synCcom (synChnqinc D (synCun D E)) J) S (synChnord (synCun D E)))
      (synWss S S) p0013 p0014
  have p0016 :=
    @gF1ores S (synChnord (synCun D E)) S (synCcom (synChnqinc D (synCun D E)) J)
  have p0017 := Nominal.mp p0015 p0016
  have p0018 :=
    @gF1of1 S (synCima (synCcom (synChnqinc D (synCun D E)) J) S)
      (synCres (synCcom (synChnqinc D (synCun D E)) J) S)
  have p0019 := Nominal.mp p0017 p0018
  have p0020 :=
    @gA1i
      (synWf1 (synCres (synCcom (synChnqinc D (synCun D E)) J) S) S
        (synCima (synCcom (synChnqinc D (synCun D E)) J) S))
      (synWss (synCima (synCcom (synChnqinc D (synCun D E)) J) S)
        (synCrn (synChnqinc E (synCun D E))))
      p0019
  have p0021 :=
    @gId
      (synWss (synCima (synCcom (synChnqinc D (synCun D E)) J) S)
        (synCrn (synChnqinc E (synCun D E))))
  have p0022 :=
    @gJca
      (synWss (synCima (synCcom (synChnqinc D (synCun D E)) J) S)
        (synCrn (synChnqinc E (synCun D E))))
      (synWf1 (synCres (synCcom (synChnqinc D (synCun D E)) J) S) S
        (synCima (synCcom (synChnqinc D (synCun D E)) J) S))
      (synWss (synCima (synCcom (synChnqinc D (synCun D E)) J) S)
        (synCrn (synChnqinc E (synCun D E))))
      p0020 p0021
  have p0023 :=
    @gF1ss S (synCima (synCcom (synChnqinc D (synCun D E)) J) S)
      (synCrn (synChnqinc E (synCun D E)))
      (synCres (synCcom (synChnqinc D (synCun D E)) J) S)
  have p0024 :=
    @gSyl
      (synWss (synCima (synCcom (synChnqinc D (synCun D E)) J) S)
        (synCrn (synChnqinc E (synCun D E))))
      (synWa (synWf1 (synCres (synCcom (synChnqinc D (synCun D E)) J) S) S
          (synCima (synCcom (synChnqinc D (synCun D E)) J) S))
        (synWss (synCima (synCcom (synChnqinc D (synCun D E)) J) S)
          (synCrn (synChnqinc E (synCun D E)))))
      (synWf1 (synCres (synCcom (synChnqinc D (synCun D E)) J) S) S
        (synCrn (synChnqinc E (synCun D E))))
      p0022 p0023
  have p0025 :=
    @gJca
      (synWss (synCima (synCcom (synChnqinc D (synCun D E)) J) S)
        (synCrn (synChnqinc E (synCun D E))))
      (synWf1 (synCcnv (synChnqinc E (synCun D E)))
        (synCrn (synChnqinc E (synCun D E))) (synChnord E))
      (synWf1 (synCres (synCcom (synChnqinc D (synCun D E)) J) S) S
        (synCrn (synChnqinc E (synCun D E))))
      p0007 p0024
  have p0026 :=
    @gF1co S (synCrn (synChnqinc E (synCun D E))) (synChnord E)
      (synCcnv (synChnqinc E (synCun D E)))
      (synCres (synCcom (synChnqinc D (synCun D E)) J) S)
  have p0027 :=
    @gSyl
      (synWss (synCima (synCcom (synChnqinc D (synCun D E)) J) S)
        (synCrn (synChnqinc E (synCun D E))))
      (synWa (synWf1 (synCcnv (synChnqinc E (synCun D E)))
          (synCrn (synChnqinc E (synCun D E))) (synChnord E))
        (synWf1 (synCres (synCcom (synChnqinc D (synCun D E)) J) S) S
          (synCrn (synChnqinc E (synCun D E)))))
      (synWf1 (synCcom (synCcnv (synChnqinc E (synCun D E)))
          (synCres (synCcom (synChnqinc D (synCun D E)) J) S)) S (synChnord E))
      p0025 p0026
  have p0028 :=
    @gResco (synCcnv (synChnqinc E (synCun D E)))
      (synCcom (synChnqinc D (synCun D E)) J) S
  have p0029 :=
    @gF1eq1 S (synChnord E)
      (synCres (synCcom (synCcnv (synChnqinc E (synCun D E)))
          (synCcom (synChnqinc D (synCun D E)) J)) S)
      (synCcom (synCcnv (synChnqinc E (synCun D E)))
        (synCres (synCcom (synChnqinc D (synCun D E)) J) S))
  have p0030 := Nominal.mp p0028 p0029
  have p0031 :=
    @gSylibr
      (synWss (synCima (synCcom (synChnqinc D (synCun D E)) J) S)
        (synCrn (synChnqinc E (synCun D E))))
      (synWf1 (synCcom (synCcnv (synChnqinc E (synCun D E)))
          (synCres (synCcom (synChnqinc D (synCun D E)) J) S)) S (synChnord E))
      (synWf1 (synCres (synCcom (synCcnv (synChnqinc E (synCun D E)))
            (synCcom (synChnqinc D (synCun D E)) J)) S) S (synChnord E))
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

/-- Checked nominal proof certificate identified upstream as `g_ncwehwcardsndv`. -/
@[expose]
noncomputable def gNcwehwcardsndv (D : Class) (R : Class) :
    Nominal.NPrf
      (.imp (synWbr R (synCwe) D) (.classMem (synCnc D) (synChwcards (synCvv)))) :=
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
  have dv_cache_0005 : d ∉ ((synWbr R (synCwe) D)).fv :=
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
  have dv_cache_0006 : s ∉ ((synWbr R (synCwe) D)).fv :=
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
  have dv_cache_0008 : d ∉ ((synCnc D)).fv :=
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
  have dv_cache_0009 : s ∉ ((synCnc D)).fv :=
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
  have p0000 := @gBrex R D (synCwe)
  have p0001 :=
    @gAncomd (synWbr R (synCwe) D) (.classMem R (synCvv)) (.classMem D (synCvv))
      p0000
  have p0002 := @gSimpl (.classEq (.cv d) D) (.classEq (.cv s) R)
  have p0003 :=
    @gEqcomd (synWa (.classEq (.cv d) D) (.classEq (.cv s) R)) (.cv d) D p0002
  have p0004 :=
    @gNceqd (synWa (.classEq (.cv d) D) (.classEq (.cv s) R)) D (.cv d) p0003
  have p0005 :=
    @gBiantrud (synWa (.classEq (.cv d) D) (.classEq (.cv s) R))
      (.classEq (synCnc D) (synCnc (.cv d))) (synWbr (.cv s) (synCwe) (.cv d)) p0004
  have p0006 :=
    @gBicomd (synWa (.classEq (.cv d) D) (.classEq (.cv s) R))
      (synWbr (.cv s) (synCwe) (.cv d))
      (synWa (synWbr (.cv s) (synCwe) (.cv d)) (.classEq (synCnc D) (synCnc (.cv d))))
      p0005
  have p0007 := @gSimpr (.classEq (.cv d) D) (.classEq (.cv s) R)
  have p0009 :=
    @gBreq12d (synWa (.classEq (.cv d) D) (.classEq (.cv s) R)) (.cv s) R (.cv d) D
      (synCwe) p0007 p0002
  have p0010 :=
    @gBitrd (synWa (.classEq (.cv d) D) (.classEq (.cv s) R))
      (synWa (synWbr (.cv s) (synCwe) (.cv d)) (.classEq (synCnc D) (synCnc (.cv d))))
      (synWbr (.cv s) (synCwe) (.cv d)) (synWbr R (synCwe) D) p0006 p0009
  have p0011 :=
    @gSpc2egv
      (synWa (synWbr (.cv s) (synCwe) (.cv d)) (.classEq (synCnc D) (synCnc (.cv d))))
      (synWbr R (synCwe) D) d s D R (synCvv) (synCvv) dv_cache_0001 dv_cache_0002
      dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 p0010
  have p0012 :=
    @gSyl (synWbr R (synCwe) D)
      (synWa (.classMem D (synCvv)) (.classMem R (synCvv)))
      (.imp (synWbr R (synCwe) D) (synWex d (synWex s
            (synWa (synWbr (.cv s) (synCwe) (.cv d))
              (.classEq (synCnc D) (synCnc (.cv d)))))))
      p0001 p0011
  have p0013 :=
    @gPm243i (synWbr R (synCwe) D)
      (synWex d (synWex s (synWa (synWbr (.cv s) (synCwe) (.cv d))
            (.classEq (synCnc D) (synCnc (.cv d))))))
      p0012
  have p0014 := @gNcex D
  have p0015 :=
    @gElhwcardsweclndv (synCnc D) s d dv_cache_0008 dv_cache_0009 dv_cache_0007
  have p0016 := Nominal.mp p0014 p0015
  have p0017 :=
    @gSylibr (synWbr R (synCwe) D)
      (synWex d (synWex s (synWa (synWbr (.cv s) (synCwe) (.cv d))
            (.classEq (synCnc D) (synCnc (.cv d))))))
      (.classMem (synCnc D) (synChwcards (synCvv))) p0013 p0016
  exact p0017

/-- Checked nominal proof certificate identified upstream as `g_hnsiquomaprepvalcl3ndv`. -/
@[expose]
noncomputable def gHnsiquomaprepvalcl3ndv (A : Class) (C : Class) (Q : Class)
    (hyp_hnsiquomaprepvalcl3ndv_1 : Nominal.NPrf (.classMem A (synCvv))) :
    Nominal.NPrf
      (.imp (synWa (.classMem Q (synCpw1 (synChnord A))) (synWa (.classMem C (synChwcn A))
            (.classEq (synCuni Q) (synCec C (synChwniso A)))))
        (.classEq (synCfv (synChnsiquomap A) Q)
          (synCec (synCfv (synChnsicodemap A) (synCsn C)) (synChwniso (synCpw1 A))))) :=
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
      ((Wff.imp (synWa (.classMem Q (synCpw1 (synChnord A)))
            (synWa (.classMem C (synChwcn A))
              (.classEq (synCuni Q) (synCec C (synChwniso A)))))
          (.classEq (synCfv (synChnsiquomap A) Q)
            (synCec (synCfv (synChnsicodemap A) (synCsn C))
              (synChwniso (synCpw1 A)))))).fv :=
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
    @gSimpl (.classMem Q (synCpw1 (synChnord A)))
      (synWa (.classMem C (synChwcn A)) (.classEq (synCuni Q) (synCec C (synChwniso A))))
  have p0001 := @gElex Q (synCpw1 (synChnord A))
  have p0002 :=
    @gSyl
      (synWa (.classMem Q (synCpw1 (synChnord A))) (synWa (.classMem C (synChwcn A))
          (.classEq (synCuni Q) (synCec C (synChwniso A)))))
      (.classMem Q (synCpw1 (synChnord A))) (.classMem Q (synCvv)) p0000 p0001
  have p0003 := @gId (.classEq (.cv q) Q)
  have p0004 := @gEleq1d (.classEq (.cv q) Q) (.cv q) Q (synCpw1 (synChnord A)) p0003
  have p0005 := @gBiid (.classMem C (synChwcn A))
  have p0006 :=
    @gA1i (synWb (.classMem C (synChwcn A)) (.classMem C (synChwcn A)))
      (.classEq (.cv q) Q) p0005
  have p0008 := @gUnieqd (.classEq (.cv q) Q) (.cv q) Q p0003
  have p0009 :=
    @gEqeq1d (.classEq (.cv q) Q) (synCuni (.cv q)) (synCuni Q)
      (synCec C (synChwniso A)) p0008
  have p0010 :=
    @gAnbi12d (.classEq (.cv q) Q) (.classMem C (synChwcn A))
      (.classMem C (synChwcn A))
      (.classEq (synCuni (.cv q)) (synCec C (synChwniso A)))
      (.classEq (synCuni Q) (synCec C (synChwniso A))) p0006 p0009
  have p0011 :=
    @gAnbi12d (.classEq (.cv q) Q) (.classMem (.cv q) (synCpw1 (synChnord A)))
      (.classMem Q (synCpw1 (synChnord A)))
      (synWa (.classMem C (synChwcn A))
        (.classEq (synCuni (.cv q)) (synCec C (synChwniso A))))
      (synWa (.classMem C (synChwcn A)) (.classEq (synCuni Q) (synCec C (synChwniso A))))
      p0004 p0010
  have p0013 := @gFveq2d (.classEq (.cv q) Q) (.cv q) Q (synChnsiquomap A) p0003
  have p0014 :=
    @gEqeq1d (.classEq (.cv q) Q) (synCfv (synChnsiquomap A) (.cv q))
      (synCfv (synChnsiquomap A) Q)
      (synCec (synCfv (synChnsicodemap A) (synCsn C)) (synChwniso (synCpw1 A)))
      p0013
  have p0015 :=
    @gImbi12d (.classEq (.cv q) Q)
      (synWa (.classMem (.cv q) (synCpw1 (synChnord A))) (synWa (.classMem C (synChwcn A))
          (.classEq (synCuni (.cv q)) (synCec C (synChwniso A)))))
      (synWa (.classMem Q (synCpw1 (synChnord A))) (synWa (.classMem C (synChwcn A))
          (.classEq (synCuni Q) (synCec C (synChwniso A)))))
      (.classEq (synCfv (synChnsiquomap A) (.cv q))
        (synCec (synCfv (synChnsicodemap A) (synCsn C)) (synChwniso (synCpw1 A))))
      (.classEq (synCfv (synChnsiquomap A) Q)
        (synCec (synCfv (synChnsicodemap A) (synCsn C)) (synChwniso (synCpw1 A))))
      p0011 p0014
  have p0016 := @gHnsiquomaprepvalcl2ndv A C q dv_cache_0001 hyp_hnsiquomaprepvalcl3ndv_1
  have p0017 :=
    @gVtoclg
      (.imp (synWa (.classMem (.cv q) (synCpw1 (synChnord A)))
          (synWa (.classMem C (synChwcn A))
            (.classEq (synCuni (.cv q)) (synCec C (synChwniso A)))))
        (.classEq (synCfv (synChnsiquomap A) (.cv q))
          (synCec (synCfv (synChnsicodemap A) (synCsn C)) (synChwniso (synCpw1 A)))))
      (.imp (synWa (.classMem Q (synCpw1 (synChnord A))) (synWa (.classMem C (synChwcn A))
            (.classEq (synCuni Q) (synCec C (synChwniso A)))))
        (.classEq (synCfv (synChnsiquomap A) Q)
          (synCec (synCfv (synChnsicodemap A) (synCsn C)) (synChwniso (synCpw1 A)))))
      q Q (synCvv) dv_cache_0002 dv_cache_0003 p0015 p0016
  have p0018 :=
    @gSyl
      (synWa (.classMem Q (synCpw1 (synChnord A))) (synWa (.classMem C (synChwcn A))
          (.classEq (synCuni Q) (synCec C (synChwniso A)))))
      (.classMem Q (synCvv))
      (.imp (synWa (.classMem Q (synCpw1 (synChnord A))) (synWa (.classMem C (synChwcn A))
            (.classEq (synCuni Q) (synCec C (synChwniso A)))))
        (.classEq (synCfv (synChnsiquomap A) Q)
          (synCec (synCfv (synChnsicodemap A) (synCsn C)) (synChwniso (synCpw1 A)))))
      p0002 p0017
  have p0019 :=
    @gPm243i
      (synWa (.classMem Q (synCpw1 (synChnord A))) (synWa (.classMem C (synChwcn A))
          (.classEq (synCuni Q) (synCec C (synChwniso A)))))
      (.classEq (synCfv (synChnsiquomap A) Q)
        (synCec (synCfv (synChnsicodemap A) (synCsn C)) (synChwniso (synCpw1 A))))
      p0018
  exact p0019


end NFChoice.DirectNominalPrf.WPPReplay

end
