/-
Copyright (c) 2026 Elliot Glazer and NFNotWPP contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elliot Glazer and NFNotWPP contributors
-/

module

public import LeanPool.NFWeakPartition.Certificates.NominalWPPReplayChunk014Compact001Block007

/-! Nominal proof certificates grouped in dependency order. -/


public section

/-! Certificates from `NominalWPPReplayChunk014Compact001Part035`. -/


section

namespace NFChoice.DirectNominalPrf.WPPReplay

open scoped Fol
open NFChoice.Foundation
open NFChoice.SemanticCore
open NFChoice.ReplaySupport
open NFChoice.Compiler.CompactSourceSyntax

@[expose]
noncomputable def g_hwtrnbrd (x : Var) (y : Var) (f : Var) (r : Var) (_dv_f_x : f ≠ x)
    (_dv_f_y : f ≠ y) :
    Nominal.NPrf
      (.imp (syn_wfun (syn_ccnv (.cv f))) (syn_wb
          (syn_wbr (.cv x) (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f))) (.cv y))
          (syn_wa (syn_wa (.classMem (.cv x) (syn_crn (.cv f)))
              (.classMem (.cv y) (syn_crn (.cv f))))
            (syn_wbr (syn_cfv (syn_ccnv (.cv f)) (.cv x)) (.cv r)
              (syn_cfv (syn_ccnv (.cv f)) (.cv y)))))) :=
  by
  let proofSupport : Finset Var :=
    ({ x } : Finset Var) ∪ ({ y } : Finset Var) ∪ ({ f } : Finset Var) ∪
      ({ r } : Finset Var)
  let z : Var := freshVar proofSupport 0
  let w : Var := freshVar proofSupport 1
  have fresh_z : z ∉ proofSupport :=
    by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_z_ne_x : z ≠ x := by
    intro h
    exact
      fresh_z
        (Finset.mem_union_left _ (Finset.mem_union_left _
            (Finset.mem_union_left _ (Finset.mem_singleton.mpr h))))
  have fresh_z_ne_y : z ≠ y := by
    intro h
    exact
      fresh_z
        (Finset.mem_union_left _ (Finset.mem_union_left _
            (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))))
  have fresh_z_ne_f : z ≠ f := by
    intro h
    exact
      fresh_z
        (Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_singleton.mpr h)))
  have fresh_z_ne_r : z ≠ r := by
    intro h
    exact fresh_z (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))
  have fresh_w : w ∉ proofSupport :=
    by
    change freshVar proofSupport 1 ∉ proofSupport
    exact freshVar_not_mem proofSupport 1
  have fresh_w_ne_x : w ≠ x := by
    intro h
    exact
      fresh_w
        (Finset.mem_union_left _ (Finset.mem_union_left _
            (Finset.mem_union_left _ (Finset.mem_singleton.mpr h))))
  have fresh_w_ne_y : w ≠ y := by
    intro h
    exact
      fresh_w
        (Finset.mem_union_left _ (Finset.mem_union_left _
            (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))))
  have fresh_w_ne_f : w ≠ f := by
    intro h
    exact
      fresh_w
        (Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_singleton.mpr h)))
  have fresh_w_ne_r : w ≠ r := by
    intro h
    exact fresh_w (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))
  have dv_cache_0001 : z ∉ ((Class.cv x)).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_z_ne_x, not_false_eq_true])
  have dv_cache_0002 : z ∉ ((Class.cv y)).fv :=
    by
    clear dv_cache_0001
    exact
      (by
        have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_z_ne_y, not_false_eq_true])
  have dv_cache_0003 : z ∉ ((syn_ccom (.cv f) (.cv r))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact
      (by
        have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccom,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, fresh_z_ne_f, fresh_z_ne_r, or_false, not_false_eq_true])
  have dv_cache_0004 : z ∉ ((syn_ccnv (.cv f))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact
      (by
        have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton, fresh_z_ne_f,
          not_false_eq_true])
  have dv_cache_0005 : z ∉ ((syn_wfun (syn_ccnv (.cv f)))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact
      (by
        have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wfun,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton, fresh_z_ne_f,
          not_false_eq_true])
  have dv_cache_0006 : z ∉ ((Wff.classMem (.cv x) (syn_cdm (syn_ccnv (.cv f))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact
      (by
        have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdm,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv, Finset.mem_union,
          Finset.mem_singleton, fresh_z_ne_x, fresh_z_ne_f, or_false, not_false_eq_true])
  have dv_cache_0007 : z ∉ ((syn_cfv (syn_ccnv (.cv f)) (.cv x))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006
    exact
      (by
        have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, fresh_z_ne_x, fresh_z_ne_f, or_false, not_false_eq_true])
  have dv_cache_0008 :
    z ∉
      ((syn_wbr (syn_cfv (syn_ccnv (.cv f)) (.cv x)) (syn_ccom (.cv f) (.cv r)) (.cv y))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007
    exact
      (by
        have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccom, Finset.mem_union,
          Finset.mem_singleton, fresh_z_ne_x, fresh_z_ne_f, fresh_z_ne_y, fresh_z_ne_r,
          or_false, not_false_eq_true])
  have dv_cache_0009 : w ∉ ((syn_cfv (syn_ccnv (.cv f)) (.cv x))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008
    exact
      (by
        have compact_fv_not_mem_empty : w ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, fresh_w_ne_x, fresh_w_ne_f, or_false, not_false_eq_true])
  have dv_cache_0010 : w ∉ ((Class.cv y)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009
    exact
      (by
        have compact_fv_not_mem_empty : w ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_w_ne_y, not_false_eq_true])
  have dv_cache_0011 : w ∉ ((Class.cv f)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010
    exact
      (by
        have compact_fv_not_mem_empty : w ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_w_ne_f, not_false_eq_true])
  have dv_cache_0012 : w ∉ ((Class.cv r)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
    exact
      (by
        have compact_fv_not_mem_empty : w ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_w_ne_r, not_false_eq_true])
  have dv_cache_0013 : w ∉ ((syn_wfun (syn_ccnv (.cv f)))).fv :=
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
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wfun,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton, fresh_w_ne_f,
          not_false_eq_true])
  have dv_cache_0014 : w ∉ ((Wff.classMem (.cv y) (syn_cdm (syn_ccnv (.cv f))))).fv :=
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
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdm,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv, Finset.mem_union,
          Finset.mem_singleton, fresh_w_ne_y, fresh_w_ne_f, or_false, not_false_eq_true])
  have dv_cache_0015 : w ∉ ((syn_cfv (syn_ccnv (.cv f)) (.cv y))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014
    exact
      (by
        have compact_fv_not_mem_empty : w ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, fresh_w_ne_y, fresh_w_ne_f, or_false, not_false_eq_true])
  have dv_cache_0016 :
    w ∉
      ((syn_wbr (syn_cfv (syn_ccnv (.cv f)) (.cv x)) (.cv r)
          (syn_cfv (syn_ccnv (.cv f)) (.cv y)))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015
    exact
      (by
        have compact_fv_not_mem_empty : w ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, fresh_w_ne_x, fresh_w_ne_f, fresh_w_ne_y, fresh_w_ne_r,
          or_false, not_false_eq_true])
  have p0000 :=
    @g_brco z (.cv x) (.cv y) (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f)) dv_cache_0001
      dv_cache_0002 dv_cache_0003 dv_cache_0004
  have p0001 :=
    @g_a1i
      (syn_wb (syn_wbr (.cv x) (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f))) (.cv y))
        (syn_wex z (syn_wa (syn_wbr (.cv x) (syn_ccnv (.cv f)) (.cv z))
            (syn_wbr (.cv z) (syn_ccom (.cv f) (.cv r)) (.cv y)))))
      (syn_wfun (syn_ccnv (.cv f))) p0000
  have p0002 := @g_funbrfv2b (.cv x) (.cv z) (syn_ccnv (.cv f))
  have p0003 :=
    @g_anbi1d (syn_wfun (syn_ccnv (.cv f))) (syn_wbr (.cv x) (syn_ccnv (.cv f)) (.cv z))
      (syn_wa (.classMem (.cv x) (syn_cdm (syn_ccnv (.cv f))))
        (.classEq (syn_cfv (syn_ccnv (.cv f)) (.cv x)) (.cv z)))
      (syn_wbr (.cv z) (syn_ccom (.cv f) (.cv r)) (.cv y)) p0002
  have p0004 :=
    @g_exbidv (syn_wfun (syn_ccnv (.cv f)))
      (syn_wa (syn_wbr (.cv x) (syn_ccnv (.cv f)) (.cv z))
        (syn_wbr (.cv z) (syn_ccom (.cv f) (.cv r)) (.cv y)))
      (syn_wa (syn_wa (.classMem (.cv x) (syn_cdm (syn_ccnv (.cv f))))
          (.classEq (syn_cfv (syn_ccnv (.cv f)) (.cv x)) (.cv z)))
        (syn_wbr (.cv z) (syn_ccom (.cv f) (.cv r)) (.cv y)))
      z dv_cache_0005 p0003
  have p0005 :=
    @g_anass (.classMem (.cv x) (syn_cdm (syn_ccnv (.cv f))))
      (.classEq (syn_cfv (syn_ccnv (.cv f)) (.cv x)) (.cv z))
      (syn_wbr (.cv z) (syn_ccom (.cv f) (.cv r)) (.cv y))
  have p0006 :=
    @g_a1i
      (syn_wb (syn_wa (syn_wa (.classMem (.cv x) (syn_cdm (syn_ccnv (.cv f))))
            (.classEq (syn_cfv (syn_ccnv (.cv f)) (.cv x)) (.cv z)))
          (syn_wbr (.cv z) (syn_ccom (.cv f) (.cv r)) (.cv y)))
        (syn_wa (.classMem (.cv x) (syn_cdm (syn_ccnv (.cv f))))
          (syn_wa (.classEq (syn_cfv (syn_ccnv (.cv f)) (.cv x)) (.cv z))
            (syn_wbr (.cv z) (syn_ccom (.cv f) (.cv r)) (.cv y)))))
      (syn_wfun (syn_ccnv (.cv f))) p0005
  have p0007 :=
    @g_exbidv (syn_wfun (syn_ccnv (.cv f)))
      (syn_wa (syn_wa (.classMem (.cv x) (syn_cdm (syn_ccnv (.cv f))))
          (.classEq (syn_cfv (syn_ccnv (.cv f)) (.cv x)) (.cv z)))
        (syn_wbr (.cv z) (syn_ccom (.cv f) (.cv r)) (.cv y)))
      (syn_wa (.classMem (.cv x) (syn_cdm (syn_ccnv (.cv f))))
        (syn_wa (.classEq (syn_cfv (syn_ccnv (.cv f)) (.cv x)) (.cv z))
          (syn_wbr (.cv z) (syn_ccom (.cv f) (.cv r)) (.cv y))))
      z dv_cache_0005 p0006
  have p0008 :=
    @g_bitrd (syn_wfun (syn_ccnv (.cv f)))
      (syn_wex z (syn_wa (syn_wbr (.cv x) (syn_ccnv (.cv f)) (.cv z))
          (syn_wbr (.cv z) (syn_ccom (.cv f) (.cv r)) (.cv y))))
      (syn_wex z (syn_wa (syn_wa (.classMem (.cv x) (syn_cdm (syn_ccnv (.cv f))))
            (.classEq (syn_cfv (syn_ccnv (.cv f)) (.cv x)) (.cv z)))
          (syn_wbr (.cv z) (syn_ccom (.cv f) (.cv r)) (.cv y))))
      (syn_wex z (syn_wa (.classMem (.cv x) (syn_cdm (syn_ccnv (.cv f))))
          (syn_wa (.classEq (syn_cfv (syn_ccnv (.cv f)) (.cv x)) (.cv z))
            (syn_wbr (.cv z) (syn_ccom (.cv f) (.cv r)) (.cv y)))))
      p0004 p0007
  have p0009 :=
    @g_n_19_42v (.classMem (.cv x) (syn_cdm (syn_ccnv (.cv f))))
      (syn_wa (.classEq (syn_cfv (syn_ccnv (.cv f)) (.cv x)) (.cv z))
        (syn_wbr (.cv z) (syn_ccom (.cv f) (.cv r)) (.cv y)))
      z dv_cache_0006
  have p0010 :=
    @g_a1i
      (syn_wb (syn_wex z (syn_wa (.classMem (.cv x) (syn_cdm (syn_ccnv (.cv f))))
            (syn_wa (.classEq (syn_cfv (syn_ccnv (.cv f)) (.cv x)) (.cv z))
              (syn_wbr (.cv z) (syn_ccom (.cv f) (.cv r)) (.cv y)))))
        (syn_wa (.classMem (.cv x) (syn_cdm (syn_ccnv (.cv f)))) (syn_wex z
            (syn_wa (.classEq (syn_cfv (syn_ccnv (.cv f)) (.cv x)) (.cv z))
              (syn_wbr (.cv z) (syn_ccom (.cv f) (.cv r)) (.cv y))))))
      (syn_wfun (syn_ccnv (.cv f))) p0009
  have p0011 :=
    @g_bitrd (syn_wfun (syn_ccnv (.cv f)))
      (syn_wex z (syn_wa (syn_wbr (.cv x) (syn_ccnv (.cv f)) (.cv z))
          (syn_wbr (.cv z) (syn_ccom (.cv f) (.cv r)) (.cv y))))
      (syn_wex z (syn_wa (.classMem (.cv x) (syn_cdm (syn_ccnv (.cv f))))
          (syn_wa (.classEq (syn_cfv (syn_ccnv (.cv f)) (.cv x)) (.cv z))
            (syn_wbr (.cv z) (syn_ccom (.cv f) (.cv r)) (.cv y)))))
      (syn_wa (.classMem (.cv x) (syn_cdm (syn_ccnv (.cv f)))) (syn_wex z
          (syn_wa (.classEq (syn_cfv (syn_ccnv (.cv f)) (.cv x)) (.cv z))
            (syn_wbr (.cv z) (syn_ccom (.cv f) (.cv r)) (.cv y)))))
      p0008 p0010
  have p0012 := @g_eqcom (syn_cfv (syn_ccnv (.cv f)) (.cv x)) (.cv z)
  have p0013 :=
    @g_anbi1i (.classEq (syn_cfv (syn_ccnv (.cv f)) (.cv x)) (.cv z))
      (.classEq (.cv z) (syn_cfv (syn_ccnv (.cv f)) (.cv x)))
      (syn_wbr (.cv z) (syn_ccom (.cv f) (.cv r)) (.cv y)) p0012
  have p0014 :=
    @g_exbii
      (syn_wa (.classEq (syn_cfv (syn_ccnv (.cv f)) (.cv x)) (.cv z))
        (syn_wbr (.cv z) (syn_ccom (.cv f) (.cv r)) (.cv y)))
      (syn_wa (.classEq (.cv z) (syn_cfv (syn_ccnv (.cv f)) (.cv x)))
        (syn_wbr (.cv z) (syn_ccom (.cv f) (.cv r)) (.cv y)))
      z p0013
  have p0015 := @g_fvex (.cv x) (syn_ccnv (.cv f))
  have p0016 :=
    @g_breq1 (.cv z) (syn_cfv (syn_ccnv (.cv f)) (.cv x)) (.cv y)
      (syn_ccom (.cv f) (.cv r))
  have p0017 :=
    @g_ceqsexv (syn_wbr (.cv z) (syn_ccom (.cv f) (.cv r)) (.cv y))
      (syn_wbr (syn_cfv (syn_ccnv (.cv f)) (.cv x)) (syn_ccom (.cv f) (.cv r)) (.cv y)) z
      (syn_cfv (syn_ccnv (.cv f)) (.cv x)) dv_cache_0007 dv_cache_0008 p0015 p0016
  have p0018 :=
    @g_bitri
      (syn_wex z (syn_wa (.classEq (syn_cfv (syn_ccnv (.cv f)) (.cv x)) (.cv z))
          (syn_wbr (.cv z) (syn_ccom (.cv f) (.cv r)) (.cv y))))
      (syn_wex z (syn_wa (.classEq (.cv z) (syn_cfv (syn_ccnv (.cv f)) (.cv x)))
          (syn_wbr (.cv z) (syn_ccom (.cv f) (.cv r)) (.cv y))))
      (syn_wbr (syn_cfv (syn_ccnv (.cv f)) (.cv x)) (syn_ccom (.cv f) (.cv r)) (.cv y))
      p0014 p0017
  have p0019 :=
    @g_anbi2i
      (syn_wex z (syn_wa (.classEq (syn_cfv (syn_ccnv (.cv f)) (.cv x)) (.cv z))
          (syn_wbr (.cv z) (syn_ccom (.cv f) (.cv r)) (.cv y))))
      (syn_wbr (syn_cfv (syn_ccnv (.cv f)) (.cv x)) (syn_ccom (.cv f) (.cv r)) (.cv y))
      (.classMem (.cv x) (syn_cdm (syn_ccnv (.cv f)))) p0018
  have p0020 :=
    @g_a1i
      (syn_wb (syn_wa (.classMem (.cv x) (syn_cdm (syn_ccnv (.cv f)))) (syn_wex z
            (syn_wa (.classEq (syn_cfv (syn_ccnv (.cv f)) (.cv x)) (.cv z))
              (syn_wbr (.cv z) (syn_ccom (.cv f) (.cv r)) (.cv y)))))
        (syn_wa (.classMem (.cv x) (syn_cdm (syn_ccnv (.cv f))))
          (syn_wbr (syn_cfv (syn_ccnv (.cv f)) (.cv x)) (syn_ccom (.cv f) (.cv r)) (.cv y))))
      (syn_wfun (syn_ccnv (.cv f))) p0019
  have p0021 :=
    @g_bitrd (syn_wfun (syn_ccnv (.cv f)))
      (syn_wex z (syn_wa (syn_wbr (.cv x) (syn_ccnv (.cv f)) (.cv z))
          (syn_wbr (.cv z) (syn_ccom (.cv f) (.cv r)) (.cv y))))
      (syn_wa (.classMem (.cv x) (syn_cdm (syn_ccnv (.cv f)))) (syn_wex z
          (syn_wa (.classEq (syn_cfv (syn_ccnv (.cv f)) (.cv x)) (.cv z))
            (syn_wbr (.cv z) (syn_ccom (.cv f) (.cv r)) (.cv y)))))
      (syn_wa (.classMem (.cv x) (syn_cdm (syn_ccnv (.cv f))))
        (syn_wbr (syn_cfv (syn_ccnv (.cv f)) (.cv x)) (syn_ccom (.cv f) (.cv r)) (.cv y)))
      p0011 p0020
  have p0022 := @g_dfrn4 (.cv f)
  have p0023 := @g_eleq2i (syn_crn (.cv f)) (syn_cdm (syn_ccnv (.cv f))) (.cv x) p0022
  have p0024 :=
    @g_bicomi (.classMem (.cv x) (syn_crn (.cv f)))
      (.classMem (.cv x) (syn_cdm (syn_ccnv (.cv f)))) p0023
  have p0025 :=
    @g_anbi1i (.classMem (.cv x) (syn_cdm (syn_ccnv (.cv f))))
      (.classMem (.cv x) (syn_crn (.cv f)))
      (syn_wbr (syn_cfv (syn_ccnv (.cv f)) (.cv x)) (syn_ccom (.cv f) (.cv r)) (.cv y))
      p0024
  have p0026 :=
    @g_a1i
      (syn_wb (syn_wa (.classMem (.cv x) (syn_cdm (syn_ccnv (.cv f))))
          (syn_wbr (syn_cfv (syn_ccnv (.cv f)) (.cv x)) (syn_ccom (.cv f) (.cv r)) (.cv y)))
        (syn_wa (.classMem (.cv x) (syn_crn (.cv f)))
          (syn_wbr (syn_cfv (syn_ccnv (.cv f)) (.cv x)) (syn_ccom (.cv f) (.cv r)) (.cv y))))
      (syn_wfun (syn_ccnv (.cv f))) p0025
  have p0027 :=
    @g_bitrd (syn_wfun (syn_ccnv (.cv f)))
      (syn_wex z (syn_wa (syn_wbr (.cv x) (syn_ccnv (.cv f)) (.cv z))
          (syn_wbr (.cv z) (syn_ccom (.cv f) (.cv r)) (.cv y))))
      (syn_wa (.classMem (.cv x) (syn_cdm (syn_ccnv (.cv f))))
        (syn_wbr (syn_cfv (syn_ccnv (.cv f)) (.cv x)) (syn_ccom (.cv f) (.cv r)) (.cv y)))
      (syn_wa (.classMem (.cv x) (syn_crn (.cv f)))
        (syn_wbr (syn_cfv (syn_ccnv (.cv f)) (.cv x)) (syn_ccom (.cv f) (.cv r)) (.cv y)))
      p0021 p0026
  have p0028 :=
    @g_bitrd (syn_wfun (syn_ccnv (.cv f)))
      (syn_wbr (.cv x) (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f))) (.cv y))
      (syn_wex z (syn_wa (syn_wbr (.cv x) (syn_ccnv (.cv f)) (.cv z))
          (syn_wbr (.cv z) (syn_ccom (.cv f) (.cv r)) (.cv y))))
      (syn_wa (.classMem (.cv x) (syn_crn (.cv f)))
        (syn_wbr (syn_cfv (syn_ccnv (.cv f)) (.cv x)) (syn_ccom (.cv f) (.cv r)) (.cv y)))
      p0001 p0027
  have p0029 :=
    @g_brco w (syn_cfv (syn_ccnv (.cv f)) (.cv x)) (.cv y) (.cv f) (.cv r) dv_cache_0009
      dv_cache_0010 dv_cache_0011 dv_cache_0012
  have p0030 :=
    @g_a1i
      (syn_wb (syn_wbr (syn_cfv (syn_ccnv (.cv f)) (.cv x)) (syn_ccom (.cv f) (.cv r)) (.cv y))
        (syn_wex w (syn_wa (syn_wbr (syn_cfv (syn_ccnv (.cv f)) (.cv x)) (.cv r) (.cv w))
            (syn_wbr (.cv w) (.cv f) (.cv y)))))
      (syn_wfun (syn_ccnv (.cv f))) p0029
  have p0031 := @g_brcnv (.cv y) (.cv w) (.cv f)
  have p0032 :=
    @g_bicomi (syn_wbr (.cv y) (syn_ccnv (.cv f)) (.cv w))
      (syn_wbr (.cv w) (.cv f) (.cv y)) p0031
  have p0033 :=
    @g_a1i
      (syn_wb (syn_wbr (.cv w) (.cv f) (.cv y)) (syn_wbr (.cv y) (syn_ccnv (.cv f)) (.cv w)))
      (syn_wfun (syn_ccnv (.cv f))) p0032
  have p0034 := @g_funbrfv2b (.cv y) (.cv w) (syn_ccnv (.cv f))
  have p0035 :=
    @g_bitrd (syn_wfun (syn_ccnv (.cv f))) (syn_wbr (.cv w) (.cv f) (.cv y))
      (syn_wbr (.cv y) (syn_ccnv (.cv f)) (.cv w))
      (syn_wa (.classMem (.cv y) (syn_cdm (syn_ccnv (.cv f))))
        (.classEq (syn_cfv (syn_ccnv (.cv f)) (.cv y)) (.cv w)))
      p0033 p0034
  have p0036 :=
    @g_anbi2d (syn_wfun (syn_ccnv (.cv f))) (syn_wbr (.cv w) (.cv f) (.cv y))
      (syn_wa (.classMem (.cv y) (syn_cdm (syn_ccnv (.cv f))))
        (.classEq (syn_cfv (syn_ccnv (.cv f)) (.cv y)) (.cv w)))
      (syn_wbr (syn_cfv (syn_ccnv (.cv f)) (.cv x)) (.cv r) (.cv w)) p0035
  have p0037 :=
    @g_exbidv (syn_wfun (syn_ccnv (.cv f)))
      (syn_wa (syn_wbr (syn_cfv (syn_ccnv (.cv f)) (.cv x)) (.cv r) (.cv w))
        (syn_wbr (.cv w) (.cv f) (.cv y)))
      (syn_wa (syn_wbr (syn_cfv (syn_ccnv (.cv f)) (.cv x)) (.cv r) (.cv w))
        (syn_wa (.classMem (.cv y) (syn_cdm (syn_ccnv (.cv f))))
          (.classEq (syn_cfv (syn_ccnv (.cv f)) (.cv y)) (.cv w))))
      w dv_cache_0013 p0036
  have p0038 :=
    @g_ancom (syn_wbr (syn_cfv (syn_ccnv (.cv f)) (.cv x)) (.cv r) (.cv w))
      (syn_wa (.classMem (.cv y) (syn_cdm (syn_ccnv (.cv f))))
        (.classEq (syn_cfv (syn_ccnv (.cv f)) (.cv y)) (.cv w)))
  have p0039 :=
    @g_anass (.classMem (.cv y) (syn_cdm (syn_ccnv (.cv f))))
      (.classEq (syn_cfv (syn_ccnv (.cv f)) (.cv y)) (.cv w))
      (syn_wbr (syn_cfv (syn_ccnv (.cv f)) (.cv x)) (.cv r) (.cv w))
  have p0040 :=
    @g_bitri
      (syn_wa (syn_wbr (syn_cfv (syn_ccnv (.cv f)) (.cv x)) (.cv r) (.cv w))
        (syn_wa (.classMem (.cv y) (syn_cdm (syn_ccnv (.cv f))))
          (.classEq (syn_cfv (syn_ccnv (.cv f)) (.cv y)) (.cv w))))
      (syn_wa (syn_wa (.classMem (.cv y) (syn_cdm (syn_ccnv (.cv f))))
          (.classEq (syn_cfv (syn_ccnv (.cv f)) (.cv y)) (.cv w)))
        (syn_wbr (syn_cfv (syn_ccnv (.cv f)) (.cv x)) (.cv r) (.cv w)))
      (syn_wa (.classMem (.cv y) (syn_cdm (syn_ccnv (.cv f))))
        (syn_wa (.classEq (syn_cfv (syn_ccnv (.cv f)) (.cv y)) (.cv w))
          (syn_wbr (syn_cfv (syn_ccnv (.cv f)) (.cv x)) (.cv r) (.cv w))))
      p0038 p0039
  have p0041 :=
    @g_a1i
      (syn_wb (syn_wa (syn_wbr (syn_cfv (syn_ccnv (.cv f)) (.cv x)) (.cv r) (.cv w))
          (syn_wa (.classMem (.cv y) (syn_cdm (syn_ccnv (.cv f))))
            (.classEq (syn_cfv (syn_ccnv (.cv f)) (.cv y)) (.cv w))))
        (syn_wa (.classMem (.cv y) (syn_cdm (syn_ccnv (.cv f))))
          (syn_wa (.classEq (syn_cfv (syn_ccnv (.cv f)) (.cv y)) (.cv w))
            (syn_wbr (syn_cfv (syn_ccnv (.cv f)) (.cv x)) (.cv r) (.cv w)))))
      (syn_wfun (syn_ccnv (.cv f))) p0040
  have p0042 :=
    @g_exbidv (syn_wfun (syn_ccnv (.cv f)))
      (syn_wa (syn_wbr (syn_cfv (syn_ccnv (.cv f)) (.cv x)) (.cv r) (.cv w))
        (syn_wa (.classMem (.cv y) (syn_cdm (syn_ccnv (.cv f))))
          (.classEq (syn_cfv (syn_ccnv (.cv f)) (.cv y)) (.cv w))))
      (syn_wa (.classMem (.cv y) (syn_cdm (syn_ccnv (.cv f))))
        (syn_wa (.classEq (syn_cfv (syn_ccnv (.cv f)) (.cv y)) (.cv w))
          (syn_wbr (syn_cfv (syn_ccnv (.cv f)) (.cv x)) (.cv r) (.cv w))))
      w dv_cache_0013 p0041
  have p0043 :=
    @g_bitrd (syn_wfun (syn_ccnv (.cv f)))
      (syn_wex w (syn_wa (syn_wbr (syn_cfv (syn_ccnv (.cv f)) (.cv x)) (.cv r) (.cv w))
          (syn_wbr (.cv w) (.cv f) (.cv y))))
      (syn_wex w (syn_wa (syn_wbr (syn_cfv (syn_ccnv (.cv f)) (.cv x)) (.cv r) (.cv w))
          (syn_wa (.classMem (.cv y) (syn_cdm (syn_ccnv (.cv f))))
            (.classEq (syn_cfv (syn_ccnv (.cv f)) (.cv y)) (.cv w)))))
      (syn_wex w (syn_wa (.classMem (.cv y) (syn_cdm (syn_ccnv (.cv f))))
          (syn_wa (.classEq (syn_cfv (syn_ccnv (.cv f)) (.cv y)) (.cv w))
            (syn_wbr (syn_cfv (syn_ccnv (.cv f)) (.cv x)) (.cv r) (.cv w)))))
      p0037 p0042
  have p0044 :=
    @g_n_19_42v (.classMem (.cv y) (syn_cdm (syn_ccnv (.cv f))))
      (syn_wa (.classEq (syn_cfv (syn_ccnv (.cv f)) (.cv y)) (.cv w))
        (syn_wbr (syn_cfv (syn_ccnv (.cv f)) (.cv x)) (.cv r) (.cv w)))
      w dv_cache_0014
  have p0045 :=
    @g_a1i
      (syn_wb (syn_wex w (syn_wa (.classMem (.cv y) (syn_cdm (syn_ccnv (.cv f))))
            (syn_wa (.classEq (syn_cfv (syn_ccnv (.cv f)) (.cv y)) (.cv w))
              (syn_wbr (syn_cfv (syn_ccnv (.cv f)) (.cv x)) (.cv r) (.cv w)))))
        (syn_wa (.classMem (.cv y) (syn_cdm (syn_ccnv (.cv f)))) (syn_wex w
            (syn_wa (.classEq (syn_cfv (syn_ccnv (.cv f)) (.cv y)) (.cv w))
              (syn_wbr (syn_cfv (syn_ccnv (.cv f)) (.cv x)) (.cv r) (.cv w))))))
      (syn_wfun (syn_ccnv (.cv f))) p0044
  have p0046 :=
    @g_bitrd (syn_wfun (syn_ccnv (.cv f)))
      (syn_wex w (syn_wa (syn_wbr (syn_cfv (syn_ccnv (.cv f)) (.cv x)) (.cv r) (.cv w))
          (syn_wbr (.cv w) (.cv f) (.cv y))))
      (syn_wex w (syn_wa (.classMem (.cv y) (syn_cdm (syn_ccnv (.cv f))))
          (syn_wa (.classEq (syn_cfv (syn_ccnv (.cv f)) (.cv y)) (.cv w))
            (syn_wbr (syn_cfv (syn_ccnv (.cv f)) (.cv x)) (.cv r) (.cv w)))))
      (syn_wa (.classMem (.cv y) (syn_cdm (syn_ccnv (.cv f)))) (syn_wex w
          (syn_wa (.classEq (syn_cfv (syn_ccnv (.cv f)) (.cv y)) (.cv w))
            (syn_wbr (syn_cfv (syn_ccnv (.cv f)) (.cv x)) (.cv r) (.cv w)))))
      p0043 p0045
  have p0047 := @g_eqcom (syn_cfv (syn_ccnv (.cv f)) (.cv y)) (.cv w)
  have p0048 :=
    @g_anbi1i (.classEq (syn_cfv (syn_ccnv (.cv f)) (.cv y)) (.cv w))
      (.classEq (.cv w) (syn_cfv (syn_ccnv (.cv f)) (.cv y)))
      (syn_wbr (syn_cfv (syn_ccnv (.cv f)) (.cv x)) (.cv r) (.cv w)) p0047
  have p0049 :=
    @g_exbii
      (syn_wa (.classEq (syn_cfv (syn_ccnv (.cv f)) (.cv y)) (.cv w))
        (syn_wbr (syn_cfv (syn_ccnv (.cv f)) (.cv x)) (.cv r) (.cv w)))
      (syn_wa (.classEq (.cv w) (syn_cfv (syn_ccnv (.cv f)) (.cv y)))
        (syn_wbr (syn_cfv (syn_ccnv (.cv f)) (.cv x)) (.cv r) (.cv w)))
      w p0048
  have p0050 := @g_fvex (.cv y) (syn_ccnv (.cv f))
  have p0051 :=
    @g_breq2 (.cv w) (syn_cfv (syn_ccnv (.cv f)) (.cv y))
      (syn_cfv (syn_ccnv (.cv f)) (.cv x)) (.cv r)
  have p0052 :=
    @g_ceqsexv (syn_wbr (syn_cfv (syn_ccnv (.cv f)) (.cv x)) (.cv r) (.cv w))
      (syn_wbr (syn_cfv (syn_ccnv (.cv f)) (.cv x)) (.cv r)
        (syn_cfv (syn_ccnv (.cv f)) (.cv y)))
      w (syn_cfv (syn_ccnv (.cv f)) (.cv y)) dv_cache_0015 dv_cache_0016 p0050 p0051
  have p0053 :=
    @g_bitri
      (syn_wex w (syn_wa (.classEq (syn_cfv (syn_ccnv (.cv f)) (.cv y)) (.cv w))
          (syn_wbr (syn_cfv (syn_ccnv (.cv f)) (.cv x)) (.cv r) (.cv w))))
      (syn_wex w (syn_wa (.classEq (.cv w) (syn_cfv (syn_ccnv (.cv f)) (.cv y)))
          (syn_wbr (syn_cfv (syn_ccnv (.cv f)) (.cv x)) (.cv r) (.cv w))))
      (syn_wbr (syn_cfv (syn_ccnv (.cv f)) (.cv x)) (.cv r)
        (syn_cfv (syn_ccnv (.cv f)) (.cv y)))
      p0049 p0052
  have p0054 :=
    @g_anbi2i
      (syn_wex w (syn_wa (.classEq (syn_cfv (syn_ccnv (.cv f)) (.cv y)) (.cv w))
          (syn_wbr (syn_cfv (syn_ccnv (.cv f)) (.cv x)) (.cv r) (.cv w))))
      (syn_wbr (syn_cfv (syn_ccnv (.cv f)) (.cv x)) (.cv r)
        (syn_cfv (syn_ccnv (.cv f)) (.cv y)))
      (.classMem (.cv y) (syn_cdm (syn_ccnv (.cv f)))) p0053
  have p0055 :=
    @g_a1i
      (syn_wb (syn_wa (.classMem (.cv y) (syn_cdm (syn_ccnv (.cv f)))) (syn_wex w
            (syn_wa (.classEq (syn_cfv (syn_ccnv (.cv f)) (.cv y)) (.cv w))
              (syn_wbr (syn_cfv (syn_ccnv (.cv f)) (.cv x)) (.cv r) (.cv w)))))
        (syn_wa (.classMem (.cv y) (syn_cdm (syn_ccnv (.cv f))))
          (syn_wbr (syn_cfv (syn_ccnv (.cv f)) (.cv x)) (.cv r)
            (syn_cfv (syn_ccnv (.cv f)) (.cv y)))))
      (syn_wfun (syn_ccnv (.cv f))) p0054
  have p0056 :=
    @g_bitrd (syn_wfun (syn_ccnv (.cv f)))
      (syn_wex w (syn_wa (syn_wbr (syn_cfv (syn_ccnv (.cv f)) (.cv x)) (.cv r) (.cv w))
          (syn_wbr (.cv w) (.cv f) (.cv y))))
      (syn_wa (.classMem (.cv y) (syn_cdm (syn_ccnv (.cv f)))) (syn_wex w
          (syn_wa (.classEq (syn_cfv (syn_ccnv (.cv f)) (.cv y)) (.cv w))
            (syn_wbr (syn_cfv (syn_ccnv (.cv f)) (.cv x)) (.cv r) (.cv w)))))
      (syn_wa (.classMem (.cv y) (syn_cdm (syn_ccnv (.cv f))))
        (syn_wbr (syn_cfv (syn_ccnv (.cv f)) (.cv x)) (.cv r)
          (syn_cfv (syn_ccnv (.cv f)) (.cv y))))
      p0046 p0055
  have p0058 := @g_eleq2i (syn_crn (.cv f)) (syn_cdm (syn_ccnv (.cv f))) (.cv y) p0022
  have p0059 :=
    @g_bicomi (.classMem (.cv y) (syn_crn (.cv f)))
      (.classMem (.cv y) (syn_cdm (syn_ccnv (.cv f)))) p0058
  have p0060 :=
    @g_anbi1i (.classMem (.cv y) (syn_cdm (syn_ccnv (.cv f))))
      (.classMem (.cv y) (syn_crn (.cv f)))
      (syn_wbr (syn_cfv (syn_ccnv (.cv f)) (.cv x)) (.cv r)
        (syn_cfv (syn_ccnv (.cv f)) (.cv y)))
      p0059
  have p0061 :=
    @g_a1i
      (syn_wb (syn_wa (.classMem (.cv y) (syn_cdm (syn_ccnv (.cv f))))
          (syn_wbr (syn_cfv (syn_ccnv (.cv f)) (.cv x)) (.cv r)
            (syn_cfv (syn_ccnv (.cv f)) (.cv y)))) (syn_wa (.classMem (.cv y) (syn_crn (.cv f)))
          (syn_wbr (syn_cfv (syn_ccnv (.cv f)) (.cv x)) (.cv r)
            (syn_cfv (syn_ccnv (.cv f)) (.cv y)))))
      (syn_wfun (syn_ccnv (.cv f))) p0060
  have p0062 :=
    @g_bitrd (syn_wfun (syn_ccnv (.cv f)))
      (syn_wex w (syn_wa (syn_wbr (syn_cfv (syn_ccnv (.cv f)) (.cv x)) (.cv r) (.cv w))
          (syn_wbr (.cv w) (.cv f) (.cv y))))
      (syn_wa (.classMem (.cv y) (syn_cdm (syn_ccnv (.cv f))))
        (syn_wbr (syn_cfv (syn_ccnv (.cv f)) (.cv x)) (.cv r)
          (syn_cfv (syn_ccnv (.cv f)) (.cv y))))
      (syn_wa (.classMem (.cv y) (syn_crn (.cv f)))
        (syn_wbr (syn_cfv (syn_ccnv (.cv f)) (.cv x)) (.cv r)
          (syn_cfv (syn_ccnv (.cv f)) (.cv y))))
      p0056 p0061
  have p0063 :=
    @g_bitrd (syn_wfun (syn_ccnv (.cv f)))
      (syn_wbr (syn_cfv (syn_ccnv (.cv f)) (.cv x)) (syn_ccom (.cv f) (.cv r)) (.cv y))
      (syn_wex w (syn_wa (syn_wbr (syn_cfv (syn_ccnv (.cv f)) (.cv x)) (.cv r) (.cv w))
          (syn_wbr (.cv w) (.cv f) (.cv y))))
      (syn_wa (.classMem (.cv y) (syn_crn (.cv f)))
        (syn_wbr (syn_cfv (syn_ccnv (.cv f)) (.cv x)) (.cv r)
          (syn_cfv (syn_ccnv (.cv f)) (.cv y))))
      p0030 p0062
  have p0064 :=
    @g_anbi2d (syn_wfun (syn_ccnv (.cv f)))
      (syn_wbr (syn_cfv (syn_ccnv (.cv f)) (.cv x)) (syn_ccom (.cv f) (.cv r)) (.cv y))
      (syn_wa (.classMem (.cv y) (syn_crn (.cv f)))
        (syn_wbr (syn_cfv (syn_ccnv (.cv f)) (.cv x)) (.cv r)
          (syn_cfv (syn_ccnv (.cv f)) (.cv y))))
      (.classMem (.cv x) (syn_crn (.cv f))) p0063
  have p0065 :=
    @g_bitrd (syn_wfun (syn_ccnv (.cv f)))
      (syn_wbr (.cv x) (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f))) (.cv y))
      (syn_wa (.classMem (.cv x) (syn_crn (.cv f)))
        (syn_wbr (syn_cfv (syn_ccnv (.cv f)) (.cv x)) (syn_ccom (.cv f) (.cv r)) (.cv y)))
      (syn_wa (.classMem (.cv x) (syn_crn (.cv f)))
        (syn_wa (.classMem (.cv y) (syn_crn (.cv f)))
          (syn_wbr (syn_cfv (syn_ccnv (.cv f)) (.cv x)) (.cv r)
            (syn_cfv (syn_ccnv (.cv f)) (.cv y)))))
      p0028 p0064
  have p0066 :=
    @g_anass (.classMem (.cv x) (syn_crn (.cv f))) (.classMem (.cv y) (syn_crn (.cv f)))
      (syn_wbr (syn_cfv (syn_ccnv (.cv f)) (.cv x)) (.cv r)
        (syn_cfv (syn_ccnv (.cv f)) (.cv y)))
  have p0067 :=
    @g_bicomi
      (syn_wa (syn_wa (.classMem (.cv x) (syn_crn (.cv f)))
          (.classMem (.cv y) (syn_crn (.cv f))))
        (syn_wbr (syn_cfv (syn_ccnv (.cv f)) (.cv x)) (.cv r)
          (syn_cfv (syn_ccnv (.cv f)) (.cv y))))
      (syn_wa (.classMem (.cv x) (syn_crn (.cv f)))
        (syn_wa (.classMem (.cv y) (syn_crn (.cv f)))
          (syn_wbr (syn_cfv (syn_ccnv (.cv f)) (.cv x)) (.cv r)
            (syn_cfv (syn_ccnv (.cv f)) (.cv y)))))
      p0066
  have p0068 :=
    @g_a1i
      (syn_wb (syn_wa (.classMem (.cv x) (syn_crn (.cv f)))
          (syn_wa (.classMem (.cv y) (syn_crn (.cv f)))
            (syn_wbr (syn_cfv (syn_ccnv (.cv f)) (.cv x)) (.cv r)
              (syn_cfv (syn_ccnv (.cv f)) (.cv y))))) (syn_wa
          (syn_wa (.classMem (.cv x) (syn_crn (.cv f))) (.classMem (.cv y) (syn_crn (.cv f))))
          (syn_wbr (syn_cfv (syn_ccnv (.cv f)) (.cv x)) (.cv r)
            (syn_cfv (syn_ccnv (.cv f)) (.cv y)))))
      (syn_wfun (syn_ccnv (.cv f))) p0067
  have p0069 :=
    @g_bitrd (syn_wfun (syn_ccnv (.cv f)))
      (syn_wbr (.cv x) (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f))) (.cv y))
      (syn_wa (.classMem (.cv x) (syn_crn (.cv f)))
        (syn_wa (.classMem (.cv y) (syn_crn (.cv f)))
          (syn_wbr (syn_cfv (syn_ccnv (.cv f)) (.cv x)) (.cv r)
            (syn_cfv (syn_ccnv (.cv f)) (.cv y)))))
      (syn_wa (syn_wa (.classMem (.cv x) (syn_crn (.cv f)))
          (.classMem (.cv y) (syn_crn (.cv f))))
        (syn_wbr (syn_cfv (syn_ccnv (.cv f)) (.cv x)) (.cv r)
          (syn_cfv (syn_ccnv (.cv f)) (.cv y))))
      p0065 p0068
  exact p0069


end NFChoice.DirectNominalPrf.WPPReplay

end

/-! Certificates from `NominalWPPReplayChunk014Compact001Part036`. -/


section

namespace NFChoice.DirectNominalPrf.WPPReplay

open scoped Fol
open NFChoice.Foundation
open NFChoice.SemanticCore
open NFChoice.ReplaySupport
open NFChoice.Compiler.CompactSourceSyntax

@[expose]
noncomputable def g_hwtrnisob (f : Var) (r : Var) :
    Nominal.NPrf
      (syn_wb (syn_wf1o (.cv f) (syn_cdm (.cv f)) (syn_crn (.cv f)))
        (syn_wiso (.cv f) (.cv r) (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f)))
          (syn_cdm (.cv f)) (syn_crn (.cv f)))) :=
  by
  let proofSupport : Finset Var := ({ f } : Finset Var) ∪ ({ r } : Finset Var)
  let z : Var := freshVar proofSupport 0
  let w : Var := freshVar proofSupport 1
  let x : Var := freshVar proofSupport 2
  let y : Var := freshVar proofSupport 3
  have fresh_z : z ∉ proofSupport :=
    by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_z_ne_f : z ≠ f := by
    intro h
    exact fresh_z (Finset.mem_union_left _ (Finset.mem_singleton.mpr h))
  have fresh_z_ne_r : z ≠ r := by
    intro h
    exact fresh_z (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))
  have fresh_w : w ∉ proofSupport :=
    by
    change freshVar proofSupport 1 ∉ proofSupport
    exact freshVar_not_mem proofSupport 1
  have fresh_w_ne_f : w ≠ f := by
    intro h
    exact fresh_w (Finset.mem_union_left _ (Finset.mem_singleton.mpr h))
  have fresh_w_ne_r : w ≠ r := by
    intro h
    exact fresh_w (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))
  have fresh_x : x ∉ proofSupport :=
    by
    change freshVar proofSupport 2 ∉ proofSupport
    exact freshVar_not_mem proofSupport 2
  have fresh_x_ne_f : x ≠ f := by
    intro h
    exact fresh_x (Finset.mem_union_left _ (Finset.mem_singleton.mpr h))
  have fresh_x_ne_r : x ≠ r := by
    intro h
    exact fresh_x (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))
  have fresh_y : y ∉ proofSupport :=
    by
    change freshVar proofSupport 3 ∉ proofSupport
    exact freshVar_not_mem proofSupport 3
  have fresh_y_ne_f : y ≠ f := by
    intro h
    exact fresh_y (Finset.mem_union_left _ (Finset.mem_singleton.mpr h))
  have fresh_y_ne_r : y ≠ r := by
    intro h
    exact fresh_y (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))
  have fresh_z_ne_w : z ≠ w :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have fresh_z_ne_x : z ≠ x :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 2
    exact freshVar_injective proofSupport (i := 0) (j := 2) (by decide)
  have fresh_x_ne_z : x ≠ z := Ne.symm fresh_z_ne_x
  have fresh_z_ne_y : z ≠ y :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 3
    exact freshVar_injective proofSupport (i := 0) (j := 3) (by decide)
  have fresh_y_ne_z : y ≠ z := Ne.symm fresh_z_ne_y
  have fresh_w_ne_x : w ≠ x :=
    by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 2
    exact freshVar_injective proofSupport (i := 1) (j := 2) (by decide)
  have fresh_x_ne_w : x ≠ w := Ne.symm fresh_w_ne_x
  have fresh_w_ne_y : w ≠ y :=
    by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 3
    exact freshVar_injective proofSupport (i := 1) (j := 3) (by decide)
  have fresh_y_ne_w : y ≠ w := Ne.symm fresh_w_ne_y
  have fresh_x_ne_y : x ≠ y :=
    by
    change freshVar proofSupport 2 ≠ freshVar proofSupport 3
    exact freshVar_injective proofSupport (i := 2) (j := 3) (by decide)
  have dv_cache_0001 : z ∉ ((syn_cdm (.cv f))).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdm,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton, fresh_z_ne_f,
          not_false_eq_true])
  have dv_cache_0002 : w ∉ ((syn_cdm (.cv f))).fv :=
    by
    clear dv_cache_0001
    exact
      (by
        have compact_fv_not_mem_empty : w ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdm,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton, fresh_w_ne_f,
          not_false_eq_true])
  have dv_cache_0003 : z ∉ ((syn_crn (.cv f))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact
      (by
        have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_crn,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton, fresh_z_ne_f,
          not_false_eq_true])
  have dv_cache_0004 : w ∉ ((syn_crn (.cv f))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact
      (by
        have compact_fv_not_mem_empty : w ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_crn,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton, fresh_w_ne_f,
          not_false_eq_true])
  have dv_cache_0005 : z ∉ ((Class.cv f)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact
      (by
        have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_z_ne_f, not_false_eq_true])
  have dv_cache_0006 : w ∉ ((Class.cv f)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact
      (by
        have compact_fv_not_mem_empty : w ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_w_ne_f, not_false_eq_true])
  have dv_cache_0007 : z ∉ ((Class.cv r)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006
    exact
      (by
        have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_z_ne_r, not_false_eq_true])
  have dv_cache_0008 : w ∉ ((Class.cv r)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007
    exact
      (by
        have compact_fv_not_mem_empty : w ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_w_ne_r, not_false_eq_true])
  have dv_cache_0009 : z ≠ w :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008
    exact (show z ≠ w from (by exact fresh_z_ne_w))
  have dv_cache_0010 : z ∉ ((Class.cv x)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009
    exact
      (by
        have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_z_ne_x, not_false_eq_true])
  have dv_cache_0011 : z ∉ ((Class.cv y)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010
    exact
      (by
        have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_z_ne_y, not_false_eq_true])
  have dv_cache_0012 : z ∉ ((syn_ccom (.cv f) (.cv r))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
    exact
      (by
        have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccom,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, fresh_z_ne_f, fresh_z_ne_r, or_false, not_false_eq_true])
  have dv_cache_0013 : z ∉ ((syn_ccnv (.cv f))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012
    exact
      (by
        have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton, fresh_z_ne_f,
          not_false_eq_true])
  have dv_cache_0014 : z ∉ ((syn_wfun (syn_ccnv (.cv f)))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013
    exact
      (by
        have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wfun,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton, fresh_z_ne_f,
          not_false_eq_true])
  have dv_cache_0015 : z ∉ ((Wff.classMem (.cv x) (syn_cdm (syn_ccnv (.cv f))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014
    exact
      (by
        have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdm,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv, Finset.mem_union,
          Finset.mem_singleton, fresh_z_ne_x, fresh_z_ne_f, or_false, not_false_eq_true])
  have dv_cache_0016 : z ∉ ((syn_cfv (syn_ccnv (.cv f)) (.cv x))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015
    exact
      (by
        have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, fresh_z_ne_x, fresh_z_ne_f, or_false, not_false_eq_true])
  have dv_cache_0017 :
    z ∉
      ((syn_wbr (syn_cfv (syn_ccnv (.cv f)) (.cv x)) (syn_ccom (.cv f) (.cv r)) (.cv y))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016
    exact
      (by
        have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccom, Finset.mem_union,
          Finset.mem_singleton, fresh_z_ne_x, fresh_z_ne_f, fresh_z_ne_y, fresh_z_ne_r,
          or_false, not_false_eq_true])
  have dv_cache_0018 : w ∉ ((syn_cfv (syn_ccnv (.cv f)) (.cv x))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
    exact
      (by
        have compact_fv_not_mem_empty : w ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, fresh_w_ne_x, fresh_w_ne_f, or_false, not_false_eq_true])
  have dv_cache_0019 : w ∉ ((Class.cv y)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018
    exact
      (by
        have compact_fv_not_mem_empty : w ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_w_ne_y, not_false_eq_true])
  have dv_cache_0020 : w ∉ ((syn_wfun (syn_ccnv (.cv f)))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019
    exact
      (by
        have compact_fv_not_mem_empty : w ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wfun,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton, fresh_w_ne_f,
          not_false_eq_true])
  have dv_cache_0021 : w ∉ ((Wff.classMem (.cv y) (syn_cdm (syn_ccnv (.cv f))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020
    exact
      (by
        have compact_fv_not_mem_empty : w ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdm,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv, Finset.mem_union,
          Finset.mem_singleton, fresh_w_ne_y, fresh_w_ne_f, or_false, not_false_eq_true])
  have dv_cache_0022 : w ∉ ((syn_cfv (syn_ccnv (.cv f)) (.cv y))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021
    exact
      (by
        have compact_fv_not_mem_empty : w ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, fresh_w_ne_y, fresh_w_ne_f, or_false, not_false_eq_true])
  have dv_cache_0023 :
    w ∉
      ((syn_wbr (syn_cfv (syn_ccnv (.cv f)) (.cv x)) (.cv r)
          (syn_cfv (syn_ccnv (.cv f)) (.cv y)))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022
    exact
      (by
        have compact_fv_not_mem_empty : w ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, fresh_w_ne_x, fresh_w_ne_f, fresh_w_ne_y, fresh_w_ne_r,
          or_false, not_false_eq_true])
  have dv_cache_0024 : w ∉ ((Class.cv x)).fv :=
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
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_w_ne_x, not_false_eq_true])
  have dv_cache_0025 :
    z ∉
      ((syn_wa (syn_wa (.classMem (.cv x) (syn_crn (.cv f)))
            (.classMem (.cv y) (syn_crn (.cv f))))
          (syn_wbr (syn_cfv (syn_ccnv (.cv f)) (.cv x)) (.cv r)
            (syn_cfv (syn_ccnv (.cv f)) (.cv y))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024
    exact
      (by
        have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_crn,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv, Finset.mem_union,
          Finset.mem_singleton, fresh_z_ne_x, fresh_z_ne_f, fresh_z_ne_y, fresh_z_ne_r,
          or_false, not_false_eq_true])
  have dv_cache_0026 :
    w ∉
      ((syn_wa (syn_wa (.classMem (.cv x) (syn_crn (.cv f)))
            (.classMem (.cv y) (syn_crn (.cv f))))
          (syn_wbr (syn_cfv (syn_ccnv (.cv f)) (.cv x)) (.cv r)
            (syn_cfv (syn_ccnv (.cv f)) (.cv y))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025
    exact
      (by
        have compact_fv_not_mem_empty : w ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_crn,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv, Finset.mem_union,
          Finset.mem_singleton, fresh_w_ne_x, fresh_w_ne_f, fresh_w_ne_y, fresh_w_ne_r,
          or_false, not_false_eq_true])
  have dv_cache_0027 :
    x ∉ ((syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f)))).fv :=
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
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccom,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv, Finset.mem_union,
          Finset.mem_singleton, fresh_x_ne_f, fresh_x_ne_r, or_false, not_false_eq_true])
  have dv_cache_0028 :
    y ∉ ((syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f)))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccom,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv, Finset.mem_union,
          Finset.mem_singleton, fresh_y_ne_f, fresh_y_ne_r, or_false, not_false_eq_true])
  have dv_cache_0029 :
    x ∉
      ((syn_copab z w (syn_wa (syn_wa (.classMem (.cv z) (syn_crn (.cv f)))
              (.classMem (.cv w) (syn_crn (.cv f))))
            (syn_wbr (syn_cfv (syn_ccnv (.cv f)) (.cv z)) (.cv r)
              (syn_cfv (syn_ccnv (.cv f)) (.cv w)))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_copab,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_crn,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv, Finset.mem_union,
          Finset.mem_erase, Finset.mem_singleton, fresh_x_ne_z, fresh_x_ne_f,
          fresh_x_ne_w, fresh_x_ne_r, or_false, and_false, not_false_eq_true])
  have dv_cache_0030 :
    y ∉
      ((syn_copab z w (syn_wa (syn_wa (.classMem (.cv z) (syn_crn (.cv f)))
              (.classMem (.cv w) (syn_crn (.cv f))))
            (syn_wbr (syn_cfv (syn_ccnv (.cv f)) (.cv z)) (.cv r)
              (syn_cfv (syn_ccnv (.cv f)) (.cv w)))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_copab,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_crn,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv, Finset.mem_union,
          Finset.mem_erase, Finset.mem_singleton, fresh_y_ne_z, fresh_y_ne_f,
          fresh_y_ne_w, fresh_y_ne_r, or_false, and_false, not_false_eq_true])
  have dv_cache_0031 : x ∉ ((syn_wfun (syn_ccnv (.cv f)))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
      dv_cache_0030
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wfun,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton, fresh_x_ne_f,
          not_false_eq_true])
  have dv_cache_0032 : y ∉ ((syn_wfun (syn_ccnv (.cv f)))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
      dv_cache_0030 dv_cache_0031
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wfun,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton, fresh_y_ne_f,
          not_false_eq_true])
  have dv_cache_0033 : x ≠ y :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
      dv_cache_0030 dv_cache_0031 dv_cache_0032
    exact (show x ≠ y from (by exact fresh_x_ne_y))
  have p0000 :=
    @g_eqid
      (syn_copab z w (syn_wa (syn_wa (.classMem (.cv z) (syn_crn (.cv f)))
            (.classMem (.cv w) (syn_crn (.cv f))))
          (syn_wbr (syn_cfv (syn_ccnv (.cv f)) (.cv z)) (.cv r)
            (syn_cfv (syn_ccnv (.cv f)) (.cv w)))))
  have p0001 :=
    @g_f1oiso2 z w (syn_cdm (.cv f)) (syn_crn (.cv f)) (.cv r)
      (syn_copab z w (syn_wa (syn_wa (.classMem (.cv z) (syn_crn (.cv f)))
            (.classMem (.cv w) (syn_crn (.cv f))))
          (syn_wbr (syn_cfv (syn_ccnv (.cv f)) (.cv z)) (.cv r)
            (syn_cfv (syn_ccnv (.cv f)) (.cv w)))))
      (.cv f) dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 p0000
  have p0002 := @g_f1ocnv (syn_cdm (.cv f)) (syn_crn (.cv f)) (.cv f)
  have p0003 := @g_f1ofun (syn_crn (.cv f)) (syn_cdm (.cv f)) (syn_ccnv (.cv f))
  have p0004 :=
    @g_syl (syn_wf1o (.cv f) (syn_cdm (.cv f)) (syn_crn (.cv f)))
      (syn_wf1o (syn_ccnv (.cv f)) (syn_crn (.cv f)) (syn_cdm (.cv f)))
      (syn_wfun (syn_ccnv (.cv f))) p0002 p0003
  have p0005 :=
    (Nominal.biimpRefl
      (syn_wbr (.cv x) (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f))) (.cv y)))
  have p0006 :=
    @g_bicomi
      (syn_wbr (.cv x) (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f))) (.cv y))
      (.classMem (syn_cop (.cv x) (.cv y))
        (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f))))
      p0005
  have p0007 :=
    @g_a1i
      (syn_wb (.classMem (syn_cop (.cv x) (.cv y))
          (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f))))
        (syn_wbr (.cv x) (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f))) (.cv y)))
      (syn_wfun (syn_ccnv (.cv f))) p0006
  have p0008 :=
    @g_brco z (.cv x) (.cv y) (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f)) dv_cache_0010
      dv_cache_0011 dv_cache_0012 dv_cache_0013
  have p0009 :=
    @g_a1i
      (syn_wb (syn_wbr (.cv x) (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f))) (.cv y))
        (syn_wex z (syn_wa (syn_wbr (.cv x) (syn_ccnv (.cv f)) (.cv z))
            (syn_wbr (.cv z) (syn_ccom (.cv f) (.cv r)) (.cv y)))))
      (syn_wfun (syn_ccnv (.cv f))) p0008
  have p0010 := @g_funbrfv2b (.cv x) (.cv z) (syn_ccnv (.cv f))
  have p0011 :=
    @g_anbi1d (syn_wfun (syn_ccnv (.cv f))) (syn_wbr (.cv x) (syn_ccnv (.cv f)) (.cv z))
      (syn_wa (.classMem (.cv x) (syn_cdm (syn_ccnv (.cv f))))
        (.classEq (syn_cfv (syn_ccnv (.cv f)) (.cv x)) (.cv z)))
      (syn_wbr (.cv z) (syn_ccom (.cv f) (.cv r)) (.cv y)) p0010
  have p0012 :=
    @g_exbidv (syn_wfun (syn_ccnv (.cv f)))
      (syn_wa (syn_wbr (.cv x) (syn_ccnv (.cv f)) (.cv z))
        (syn_wbr (.cv z) (syn_ccom (.cv f) (.cv r)) (.cv y)))
      (syn_wa (syn_wa (.classMem (.cv x) (syn_cdm (syn_ccnv (.cv f))))
          (.classEq (syn_cfv (syn_ccnv (.cv f)) (.cv x)) (.cv z)))
        (syn_wbr (.cv z) (syn_ccom (.cv f) (.cv r)) (.cv y)))
      z dv_cache_0014 p0011
  have p0013 :=
    @g_anass (.classMem (.cv x) (syn_cdm (syn_ccnv (.cv f))))
      (.classEq (syn_cfv (syn_ccnv (.cv f)) (.cv x)) (.cv z))
      (syn_wbr (.cv z) (syn_ccom (.cv f) (.cv r)) (.cv y))
  have p0014 :=
    @g_a1i
      (syn_wb (syn_wa (syn_wa (.classMem (.cv x) (syn_cdm (syn_ccnv (.cv f))))
            (.classEq (syn_cfv (syn_ccnv (.cv f)) (.cv x)) (.cv z)))
          (syn_wbr (.cv z) (syn_ccom (.cv f) (.cv r)) (.cv y)))
        (syn_wa (.classMem (.cv x) (syn_cdm (syn_ccnv (.cv f))))
          (syn_wa (.classEq (syn_cfv (syn_ccnv (.cv f)) (.cv x)) (.cv z))
            (syn_wbr (.cv z) (syn_ccom (.cv f) (.cv r)) (.cv y)))))
      (syn_wfun (syn_ccnv (.cv f))) p0013
  have p0015 :=
    @g_exbidv (syn_wfun (syn_ccnv (.cv f)))
      (syn_wa (syn_wa (.classMem (.cv x) (syn_cdm (syn_ccnv (.cv f))))
          (.classEq (syn_cfv (syn_ccnv (.cv f)) (.cv x)) (.cv z)))
        (syn_wbr (.cv z) (syn_ccom (.cv f) (.cv r)) (.cv y)))
      (syn_wa (.classMem (.cv x) (syn_cdm (syn_ccnv (.cv f))))
        (syn_wa (.classEq (syn_cfv (syn_ccnv (.cv f)) (.cv x)) (.cv z))
          (syn_wbr (.cv z) (syn_ccom (.cv f) (.cv r)) (.cv y))))
      z dv_cache_0014 p0014
  have p0016 :=
    @g_bitrd (syn_wfun (syn_ccnv (.cv f)))
      (syn_wex z (syn_wa (syn_wbr (.cv x) (syn_ccnv (.cv f)) (.cv z))
          (syn_wbr (.cv z) (syn_ccom (.cv f) (.cv r)) (.cv y))))
      (syn_wex z (syn_wa (syn_wa (.classMem (.cv x) (syn_cdm (syn_ccnv (.cv f))))
            (.classEq (syn_cfv (syn_ccnv (.cv f)) (.cv x)) (.cv z)))
          (syn_wbr (.cv z) (syn_ccom (.cv f) (.cv r)) (.cv y))))
      (syn_wex z (syn_wa (.classMem (.cv x) (syn_cdm (syn_ccnv (.cv f))))
          (syn_wa (.classEq (syn_cfv (syn_ccnv (.cv f)) (.cv x)) (.cv z))
            (syn_wbr (.cv z) (syn_ccom (.cv f) (.cv r)) (.cv y)))))
      p0012 p0015
  have p0017 :=
    @g_n_19_42v (.classMem (.cv x) (syn_cdm (syn_ccnv (.cv f))))
      (syn_wa (.classEq (syn_cfv (syn_ccnv (.cv f)) (.cv x)) (.cv z))
        (syn_wbr (.cv z) (syn_ccom (.cv f) (.cv r)) (.cv y)))
      z dv_cache_0015
  have p0018 :=
    @g_a1i
      (syn_wb (syn_wex z (syn_wa (.classMem (.cv x) (syn_cdm (syn_ccnv (.cv f))))
            (syn_wa (.classEq (syn_cfv (syn_ccnv (.cv f)) (.cv x)) (.cv z))
              (syn_wbr (.cv z) (syn_ccom (.cv f) (.cv r)) (.cv y)))))
        (syn_wa (.classMem (.cv x) (syn_cdm (syn_ccnv (.cv f)))) (syn_wex z
            (syn_wa (.classEq (syn_cfv (syn_ccnv (.cv f)) (.cv x)) (.cv z))
              (syn_wbr (.cv z) (syn_ccom (.cv f) (.cv r)) (.cv y))))))
      (syn_wfun (syn_ccnv (.cv f))) p0017
  have p0019 :=
    @g_bitrd (syn_wfun (syn_ccnv (.cv f)))
      (syn_wex z (syn_wa (syn_wbr (.cv x) (syn_ccnv (.cv f)) (.cv z))
          (syn_wbr (.cv z) (syn_ccom (.cv f) (.cv r)) (.cv y))))
      (syn_wex z (syn_wa (.classMem (.cv x) (syn_cdm (syn_ccnv (.cv f))))
          (syn_wa (.classEq (syn_cfv (syn_ccnv (.cv f)) (.cv x)) (.cv z))
            (syn_wbr (.cv z) (syn_ccom (.cv f) (.cv r)) (.cv y)))))
      (syn_wa (.classMem (.cv x) (syn_cdm (syn_ccnv (.cv f)))) (syn_wex z
          (syn_wa (.classEq (syn_cfv (syn_ccnv (.cv f)) (.cv x)) (.cv z))
            (syn_wbr (.cv z) (syn_ccom (.cv f) (.cv r)) (.cv y)))))
      p0016 p0018
  have p0020 := @g_eqcom (syn_cfv (syn_ccnv (.cv f)) (.cv x)) (.cv z)
  have p0021 :=
    @g_anbi1i (.classEq (syn_cfv (syn_ccnv (.cv f)) (.cv x)) (.cv z))
      (.classEq (.cv z) (syn_cfv (syn_ccnv (.cv f)) (.cv x)))
      (syn_wbr (.cv z) (syn_ccom (.cv f) (.cv r)) (.cv y)) p0020
  have p0022 :=
    @g_exbii
      (syn_wa (.classEq (syn_cfv (syn_ccnv (.cv f)) (.cv x)) (.cv z))
        (syn_wbr (.cv z) (syn_ccom (.cv f) (.cv r)) (.cv y)))
      (syn_wa (.classEq (.cv z) (syn_cfv (syn_ccnv (.cv f)) (.cv x)))
        (syn_wbr (.cv z) (syn_ccom (.cv f) (.cv r)) (.cv y)))
      z p0021
  have p0023 := @g_fvex (.cv x) (syn_ccnv (.cv f))
  have p0024 :=
    @g_breq1 (.cv z) (syn_cfv (syn_ccnv (.cv f)) (.cv x)) (.cv y)
      (syn_ccom (.cv f) (.cv r))
  have p0025 :=
    @g_ceqsexv (syn_wbr (.cv z) (syn_ccom (.cv f) (.cv r)) (.cv y))
      (syn_wbr (syn_cfv (syn_ccnv (.cv f)) (.cv x)) (syn_ccom (.cv f) (.cv r)) (.cv y)) z
      (syn_cfv (syn_ccnv (.cv f)) (.cv x)) dv_cache_0016 dv_cache_0017 p0023 p0024
  have p0026 :=
    @g_bitri
      (syn_wex z (syn_wa (.classEq (syn_cfv (syn_ccnv (.cv f)) (.cv x)) (.cv z))
          (syn_wbr (.cv z) (syn_ccom (.cv f) (.cv r)) (.cv y))))
      (syn_wex z (syn_wa (.classEq (.cv z) (syn_cfv (syn_ccnv (.cv f)) (.cv x)))
          (syn_wbr (.cv z) (syn_ccom (.cv f) (.cv r)) (.cv y))))
      (syn_wbr (syn_cfv (syn_ccnv (.cv f)) (.cv x)) (syn_ccom (.cv f) (.cv r)) (.cv y))
      p0022 p0025
  have p0027 :=
    @g_anbi2i
      (syn_wex z (syn_wa (.classEq (syn_cfv (syn_ccnv (.cv f)) (.cv x)) (.cv z))
          (syn_wbr (.cv z) (syn_ccom (.cv f) (.cv r)) (.cv y))))
      (syn_wbr (syn_cfv (syn_ccnv (.cv f)) (.cv x)) (syn_ccom (.cv f) (.cv r)) (.cv y))
      (.classMem (.cv x) (syn_cdm (syn_ccnv (.cv f)))) p0026
  have p0028 :=
    @g_a1i
      (syn_wb (syn_wa (.classMem (.cv x) (syn_cdm (syn_ccnv (.cv f)))) (syn_wex z
            (syn_wa (.classEq (syn_cfv (syn_ccnv (.cv f)) (.cv x)) (.cv z))
              (syn_wbr (.cv z) (syn_ccom (.cv f) (.cv r)) (.cv y)))))
        (syn_wa (.classMem (.cv x) (syn_cdm (syn_ccnv (.cv f))))
          (syn_wbr (syn_cfv (syn_ccnv (.cv f)) (.cv x)) (syn_ccom (.cv f) (.cv r)) (.cv y))))
      (syn_wfun (syn_ccnv (.cv f))) p0027
  have p0029 :=
    @g_bitrd (syn_wfun (syn_ccnv (.cv f)))
      (syn_wex z (syn_wa (syn_wbr (.cv x) (syn_ccnv (.cv f)) (.cv z))
          (syn_wbr (.cv z) (syn_ccom (.cv f) (.cv r)) (.cv y))))
      (syn_wa (.classMem (.cv x) (syn_cdm (syn_ccnv (.cv f)))) (syn_wex z
          (syn_wa (.classEq (syn_cfv (syn_ccnv (.cv f)) (.cv x)) (.cv z))
            (syn_wbr (.cv z) (syn_ccom (.cv f) (.cv r)) (.cv y)))))
      (syn_wa (.classMem (.cv x) (syn_cdm (syn_ccnv (.cv f))))
        (syn_wbr (syn_cfv (syn_ccnv (.cv f)) (.cv x)) (syn_ccom (.cv f) (.cv r)) (.cv y)))
      p0019 p0028
  have p0030 := @g_dfrn4 (.cv f)
  have p0031 := @g_eleq2i (syn_crn (.cv f)) (syn_cdm (syn_ccnv (.cv f))) (.cv x) p0030
  have p0032 :=
    @g_bicomi (.classMem (.cv x) (syn_crn (.cv f)))
      (.classMem (.cv x) (syn_cdm (syn_ccnv (.cv f)))) p0031
  have p0033 :=
    @g_anbi1i (.classMem (.cv x) (syn_cdm (syn_ccnv (.cv f))))
      (.classMem (.cv x) (syn_crn (.cv f)))
      (syn_wbr (syn_cfv (syn_ccnv (.cv f)) (.cv x)) (syn_ccom (.cv f) (.cv r)) (.cv y))
      p0032
  have p0034 :=
    @g_a1i
      (syn_wb (syn_wa (.classMem (.cv x) (syn_cdm (syn_ccnv (.cv f))))
          (syn_wbr (syn_cfv (syn_ccnv (.cv f)) (.cv x)) (syn_ccom (.cv f) (.cv r)) (.cv y)))
        (syn_wa (.classMem (.cv x) (syn_crn (.cv f)))
          (syn_wbr (syn_cfv (syn_ccnv (.cv f)) (.cv x)) (syn_ccom (.cv f) (.cv r)) (.cv y))))
      (syn_wfun (syn_ccnv (.cv f))) p0033
  have p0035 :=
    @g_bitrd (syn_wfun (syn_ccnv (.cv f)))
      (syn_wex z (syn_wa (syn_wbr (.cv x) (syn_ccnv (.cv f)) (.cv z))
          (syn_wbr (.cv z) (syn_ccom (.cv f) (.cv r)) (.cv y))))
      (syn_wa (.classMem (.cv x) (syn_cdm (syn_ccnv (.cv f))))
        (syn_wbr (syn_cfv (syn_ccnv (.cv f)) (.cv x)) (syn_ccom (.cv f) (.cv r)) (.cv y)))
      (syn_wa (.classMem (.cv x) (syn_crn (.cv f)))
        (syn_wbr (syn_cfv (syn_ccnv (.cv f)) (.cv x)) (syn_ccom (.cv f) (.cv r)) (.cv y)))
      p0029 p0034
  have p0036 :=
    @g_bitrd (syn_wfun (syn_ccnv (.cv f)))
      (syn_wbr (.cv x) (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f))) (.cv y))
      (syn_wex z (syn_wa (syn_wbr (.cv x) (syn_ccnv (.cv f)) (.cv z))
          (syn_wbr (.cv z) (syn_ccom (.cv f) (.cv r)) (.cv y))))
      (syn_wa (.classMem (.cv x) (syn_crn (.cv f)))
        (syn_wbr (syn_cfv (syn_ccnv (.cv f)) (.cv x)) (syn_ccom (.cv f) (.cv r)) (.cv y)))
      p0009 p0035
  have p0037 :=
    @g_brco w (syn_cfv (syn_ccnv (.cv f)) (.cv x)) (.cv y) (.cv f) (.cv r) dv_cache_0018
      dv_cache_0019 dv_cache_0006 dv_cache_0008
  have p0038 :=
    @g_a1i
      (syn_wb (syn_wbr (syn_cfv (syn_ccnv (.cv f)) (.cv x)) (syn_ccom (.cv f) (.cv r)) (.cv y))
        (syn_wex w (syn_wa (syn_wbr (syn_cfv (syn_ccnv (.cv f)) (.cv x)) (.cv r) (.cv w))
            (syn_wbr (.cv w) (.cv f) (.cv y)))))
      (syn_wfun (syn_ccnv (.cv f))) p0037
  have p0039 := @g_brcnv (.cv y) (.cv w) (.cv f)
  have p0040 :=
    @g_bicomi (syn_wbr (.cv y) (syn_ccnv (.cv f)) (.cv w))
      (syn_wbr (.cv w) (.cv f) (.cv y)) p0039
  have p0041 :=
    @g_a1i
      (syn_wb (syn_wbr (.cv w) (.cv f) (.cv y)) (syn_wbr (.cv y) (syn_ccnv (.cv f)) (.cv w)))
      (syn_wfun (syn_ccnv (.cv f))) p0040
  have p0042 := @g_funbrfv2b (.cv y) (.cv w) (syn_ccnv (.cv f))
  have p0043 :=
    @g_bitrd (syn_wfun (syn_ccnv (.cv f))) (syn_wbr (.cv w) (.cv f) (.cv y))
      (syn_wbr (.cv y) (syn_ccnv (.cv f)) (.cv w))
      (syn_wa (.classMem (.cv y) (syn_cdm (syn_ccnv (.cv f))))
        (.classEq (syn_cfv (syn_ccnv (.cv f)) (.cv y)) (.cv w)))
      p0041 p0042
  have p0044 :=
    @g_anbi2d (syn_wfun (syn_ccnv (.cv f))) (syn_wbr (.cv w) (.cv f) (.cv y))
      (syn_wa (.classMem (.cv y) (syn_cdm (syn_ccnv (.cv f))))
        (.classEq (syn_cfv (syn_ccnv (.cv f)) (.cv y)) (.cv w)))
      (syn_wbr (syn_cfv (syn_ccnv (.cv f)) (.cv x)) (.cv r) (.cv w)) p0043
  have p0045 :=
    @g_exbidv (syn_wfun (syn_ccnv (.cv f)))
      (syn_wa (syn_wbr (syn_cfv (syn_ccnv (.cv f)) (.cv x)) (.cv r) (.cv w))
        (syn_wbr (.cv w) (.cv f) (.cv y)))
      (syn_wa (syn_wbr (syn_cfv (syn_ccnv (.cv f)) (.cv x)) (.cv r) (.cv w))
        (syn_wa (.classMem (.cv y) (syn_cdm (syn_ccnv (.cv f))))
          (.classEq (syn_cfv (syn_ccnv (.cv f)) (.cv y)) (.cv w))))
      w dv_cache_0020 p0044
  have p0046 :=
    @g_ancom (syn_wbr (syn_cfv (syn_ccnv (.cv f)) (.cv x)) (.cv r) (.cv w))
      (syn_wa (.classMem (.cv y) (syn_cdm (syn_ccnv (.cv f))))
        (.classEq (syn_cfv (syn_ccnv (.cv f)) (.cv y)) (.cv w)))
  have p0047 :=
    @g_anass (.classMem (.cv y) (syn_cdm (syn_ccnv (.cv f))))
      (.classEq (syn_cfv (syn_ccnv (.cv f)) (.cv y)) (.cv w))
      (syn_wbr (syn_cfv (syn_ccnv (.cv f)) (.cv x)) (.cv r) (.cv w))
  have p0048 :=
    @g_bitri
      (syn_wa (syn_wbr (syn_cfv (syn_ccnv (.cv f)) (.cv x)) (.cv r) (.cv w))
        (syn_wa (.classMem (.cv y) (syn_cdm (syn_ccnv (.cv f))))
          (.classEq (syn_cfv (syn_ccnv (.cv f)) (.cv y)) (.cv w))))
      (syn_wa (syn_wa (.classMem (.cv y) (syn_cdm (syn_ccnv (.cv f))))
          (.classEq (syn_cfv (syn_ccnv (.cv f)) (.cv y)) (.cv w)))
        (syn_wbr (syn_cfv (syn_ccnv (.cv f)) (.cv x)) (.cv r) (.cv w)))
      (syn_wa (.classMem (.cv y) (syn_cdm (syn_ccnv (.cv f))))
        (syn_wa (.classEq (syn_cfv (syn_ccnv (.cv f)) (.cv y)) (.cv w))
          (syn_wbr (syn_cfv (syn_ccnv (.cv f)) (.cv x)) (.cv r) (.cv w))))
      p0046 p0047
  have p0049 :=
    @g_a1i
      (syn_wb (syn_wa (syn_wbr (syn_cfv (syn_ccnv (.cv f)) (.cv x)) (.cv r) (.cv w))
          (syn_wa (.classMem (.cv y) (syn_cdm (syn_ccnv (.cv f))))
            (.classEq (syn_cfv (syn_ccnv (.cv f)) (.cv y)) (.cv w))))
        (syn_wa (.classMem (.cv y) (syn_cdm (syn_ccnv (.cv f))))
          (syn_wa (.classEq (syn_cfv (syn_ccnv (.cv f)) (.cv y)) (.cv w))
            (syn_wbr (syn_cfv (syn_ccnv (.cv f)) (.cv x)) (.cv r) (.cv w)))))
      (syn_wfun (syn_ccnv (.cv f))) p0048
  have p0050 :=
    @g_exbidv (syn_wfun (syn_ccnv (.cv f)))
      (syn_wa (syn_wbr (syn_cfv (syn_ccnv (.cv f)) (.cv x)) (.cv r) (.cv w))
        (syn_wa (.classMem (.cv y) (syn_cdm (syn_ccnv (.cv f))))
          (.classEq (syn_cfv (syn_ccnv (.cv f)) (.cv y)) (.cv w))))
      (syn_wa (.classMem (.cv y) (syn_cdm (syn_ccnv (.cv f))))
        (syn_wa (.classEq (syn_cfv (syn_ccnv (.cv f)) (.cv y)) (.cv w))
          (syn_wbr (syn_cfv (syn_ccnv (.cv f)) (.cv x)) (.cv r) (.cv w))))
      w dv_cache_0020 p0049
  have p0051 :=
    @g_bitrd (syn_wfun (syn_ccnv (.cv f)))
      (syn_wex w (syn_wa (syn_wbr (syn_cfv (syn_ccnv (.cv f)) (.cv x)) (.cv r) (.cv w))
          (syn_wbr (.cv w) (.cv f) (.cv y))))
      (syn_wex w (syn_wa (syn_wbr (syn_cfv (syn_ccnv (.cv f)) (.cv x)) (.cv r) (.cv w))
          (syn_wa (.classMem (.cv y) (syn_cdm (syn_ccnv (.cv f))))
            (.classEq (syn_cfv (syn_ccnv (.cv f)) (.cv y)) (.cv w)))))
      (syn_wex w (syn_wa (.classMem (.cv y) (syn_cdm (syn_ccnv (.cv f))))
          (syn_wa (.classEq (syn_cfv (syn_ccnv (.cv f)) (.cv y)) (.cv w))
            (syn_wbr (syn_cfv (syn_ccnv (.cv f)) (.cv x)) (.cv r) (.cv w)))))
      p0045 p0050
  have p0052 :=
    @g_n_19_42v (.classMem (.cv y) (syn_cdm (syn_ccnv (.cv f))))
      (syn_wa (.classEq (syn_cfv (syn_ccnv (.cv f)) (.cv y)) (.cv w))
        (syn_wbr (syn_cfv (syn_ccnv (.cv f)) (.cv x)) (.cv r) (.cv w)))
      w dv_cache_0021
  have p0053 :=
    @g_a1i
      (syn_wb (syn_wex w (syn_wa (.classMem (.cv y) (syn_cdm (syn_ccnv (.cv f))))
            (syn_wa (.classEq (syn_cfv (syn_ccnv (.cv f)) (.cv y)) (.cv w))
              (syn_wbr (syn_cfv (syn_ccnv (.cv f)) (.cv x)) (.cv r) (.cv w)))))
        (syn_wa (.classMem (.cv y) (syn_cdm (syn_ccnv (.cv f)))) (syn_wex w
            (syn_wa (.classEq (syn_cfv (syn_ccnv (.cv f)) (.cv y)) (.cv w))
              (syn_wbr (syn_cfv (syn_ccnv (.cv f)) (.cv x)) (.cv r) (.cv w))))))
      (syn_wfun (syn_ccnv (.cv f))) p0052
  have p0054 :=
    @g_bitrd (syn_wfun (syn_ccnv (.cv f)))
      (syn_wex w (syn_wa (syn_wbr (syn_cfv (syn_ccnv (.cv f)) (.cv x)) (.cv r) (.cv w))
          (syn_wbr (.cv w) (.cv f) (.cv y))))
      (syn_wex w (syn_wa (.classMem (.cv y) (syn_cdm (syn_ccnv (.cv f))))
          (syn_wa (.classEq (syn_cfv (syn_ccnv (.cv f)) (.cv y)) (.cv w))
            (syn_wbr (syn_cfv (syn_ccnv (.cv f)) (.cv x)) (.cv r) (.cv w)))))
      (syn_wa (.classMem (.cv y) (syn_cdm (syn_ccnv (.cv f)))) (syn_wex w
          (syn_wa (.classEq (syn_cfv (syn_ccnv (.cv f)) (.cv y)) (.cv w))
            (syn_wbr (syn_cfv (syn_ccnv (.cv f)) (.cv x)) (.cv r) (.cv w)))))
      p0051 p0053
  have p0055 := @g_eqcom (syn_cfv (syn_ccnv (.cv f)) (.cv y)) (.cv w)
  have p0056 :=
    @g_anbi1i (.classEq (syn_cfv (syn_ccnv (.cv f)) (.cv y)) (.cv w))
      (.classEq (.cv w) (syn_cfv (syn_ccnv (.cv f)) (.cv y)))
      (syn_wbr (syn_cfv (syn_ccnv (.cv f)) (.cv x)) (.cv r) (.cv w)) p0055
  have p0057 :=
    @g_exbii
      (syn_wa (.classEq (syn_cfv (syn_ccnv (.cv f)) (.cv y)) (.cv w))
        (syn_wbr (syn_cfv (syn_ccnv (.cv f)) (.cv x)) (.cv r) (.cv w)))
      (syn_wa (.classEq (.cv w) (syn_cfv (syn_ccnv (.cv f)) (.cv y)))
        (syn_wbr (syn_cfv (syn_ccnv (.cv f)) (.cv x)) (.cv r) (.cv w)))
      w p0056
  have p0058 := @g_fvex (.cv y) (syn_ccnv (.cv f))
  have p0059 :=
    @g_breq2 (.cv w) (syn_cfv (syn_ccnv (.cv f)) (.cv y))
      (syn_cfv (syn_ccnv (.cv f)) (.cv x)) (.cv r)
  have p0060 :=
    @g_ceqsexv (syn_wbr (syn_cfv (syn_ccnv (.cv f)) (.cv x)) (.cv r) (.cv w))
      (syn_wbr (syn_cfv (syn_ccnv (.cv f)) (.cv x)) (.cv r)
        (syn_cfv (syn_ccnv (.cv f)) (.cv y)))
      w (syn_cfv (syn_ccnv (.cv f)) (.cv y)) dv_cache_0022 dv_cache_0023 p0058 p0059
  have p0061 :=
    @g_bitri
      (syn_wex w (syn_wa (.classEq (syn_cfv (syn_ccnv (.cv f)) (.cv y)) (.cv w))
          (syn_wbr (syn_cfv (syn_ccnv (.cv f)) (.cv x)) (.cv r) (.cv w))))
      (syn_wex w (syn_wa (.classEq (.cv w) (syn_cfv (syn_ccnv (.cv f)) (.cv y)))
          (syn_wbr (syn_cfv (syn_ccnv (.cv f)) (.cv x)) (.cv r) (.cv w))))
      (syn_wbr (syn_cfv (syn_ccnv (.cv f)) (.cv x)) (.cv r)
        (syn_cfv (syn_ccnv (.cv f)) (.cv y)))
      p0057 p0060
  have p0062 :=
    @g_anbi2i
      (syn_wex w (syn_wa (.classEq (syn_cfv (syn_ccnv (.cv f)) (.cv y)) (.cv w))
          (syn_wbr (syn_cfv (syn_ccnv (.cv f)) (.cv x)) (.cv r) (.cv w))))
      (syn_wbr (syn_cfv (syn_ccnv (.cv f)) (.cv x)) (.cv r)
        (syn_cfv (syn_ccnv (.cv f)) (.cv y)))
      (.classMem (.cv y) (syn_cdm (syn_ccnv (.cv f)))) p0061
  have p0063 :=
    @g_a1i
      (syn_wb (syn_wa (.classMem (.cv y) (syn_cdm (syn_ccnv (.cv f)))) (syn_wex w
            (syn_wa (.classEq (syn_cfv (syn_ccnv (.cv f)) (.cv y)) (.cv w))
              (syn_wbr (syn_cfv (syn_ccnv (.cv f)) (.cv x)) (.cv r) (.cv w)))))
        (syn_wa (.classMem (.cv y) (syn_cdm (syn_ccnv (.cv f))))
          (syn_wbr (syn_cfv (syn_ccnv (.cv f)) (.cv x)) (.cv r)
            (syn_cfv (syn_ccnv (.cv f)) (.cv y)))))
      (syn_wfun (syn_ccnv (.cv f))) p0062
  have p0064 :=
    @g_bitrd (syn_wfun (syn_ccnv (.cv f)))
      (syn_wex w (syn_wa (syn_wbr (syn_cfv (syn_ccnv (.cv f)) (.cv x)) (.cv r) (.cv w))
          (syn_wbr (.cv w) (.cv f) (.cv y))))
      (syn_wa (.classMem (.cv y) (syn_cdm (syn_ccnv (.cv f)))) (syn_wex w
          (syn_wa (.classEq (syn_cfv (syn_ccnv (.cv f)) (.cv y)) (.cv w))
            (syn_wbr (syn_cfv (syn_ccnv (.cv f)) (.cv x)) (.cv r) (.cv w)))))
      (syn_wa (.classMem (.cv y) (syn_cdm (syn_ccnv (.cv f))))
        (syn_wbr (syn_cfv (syn_ccnv (.cv f)) (.cv x)) (.cv r)
          (syn_cfv (syn_ccnv (.cv f)) (.cv y))))
      p0054 p0063
  have p0066 := @g_eleq2i (syn_crn (.cv f)) (syn_cdm (syn_ccnv (.cv f))) (.cv y) p0030
  have p0067 :=
    @g_bicomi (.classMem (.cv y) (syn_crn (.cv f)))
      (.classMem (.cv y) (syn_cdm (syn_ccnv (.cv f)))) p0066
  have p0068 :=
    @g_anbi1i (.classMem (.cv y) (syn_cdm (syn_ccnv (.cv f))))
      (.classMem (.cv y) (syn_crn (.cv f)))
      (syn_wbr (syn_cfv (syn_ccnv (.cv f)) (.cv x)) (.cv r)
        (syn_cfv (syn_ccnv (.cv f)) (.cv y)))
      p0067
  have p0069 :=
    @g_a1i
      (syn_wb (syn_wa (.classMem (.cv y) (syn_cdm (syn_ccnv (.cv f))))
          (syn_wbr (syn_cfv (syn_ccnv (.cv f)) (.cv x)) (.cv r)
            (syn_cfv (syn_ccnv (.cv f)) (.cv y)))) (syn_wa (.classMem (.cv y) (syn_crn (.cv f)))
          (syn_wbr (syn_cfv (syn_ccnv (.cv f)) (.cv x)) (.cv r)
            (syn_cfv (syn_ccnv (.cv f)) (.cv y)))))
      (syn_wfun (syn_ccnv (.cv f))) p0068
  have p0070 :=
    @g_bitrd (syn_wfun (syn_ccnv (.cv f)))
      (syn_wex w (syn_wa (syn_wbr (syn_cfv (syn_ccnv (.cv f)) (.cv x)) (.cv r) (.cv w))
          (syn_wbr (.cv w) (.cv f) (.cv y))))
      (syn_wa (.classMem (.cv y) (syn_cdm (syn_ccnv (.cv f))))
        (syn_wbr (syn_cfv (syn_ccnv (.cv f)) (.cv x)) (.cv r)
          (syn_cfv (syn_ccnv (.cv f)) (.cv y))))
      (syn_wa (.classMem (.cv y) (syn_crn (.cv f)))
        (syn_wbr (syn_cfv (syn_ccnv (.cv f)) (.cv x)) (.cv r)
          (syn_cfv (syn_ccnv (.cv f)) (.cv y))))
      p0064 p0069
  have p0071 :=
    @g_bitrd (syn_wfun (syn_ccnv (.cv f)))
      (syn_wbr (syn_cfv (syn_ccnv (.cv f)) (.cv x)) (syn_ccom (.cv f) (.cv r)) (.cv y))
      (syn_wex w (syn_wa (syn_wbr (syn_cfv (syn_ccnv (.cv f)) (.cv x)) (.cv r) (.cv w))
          (syn_wbr (.cv w) (.cv f) (.cv y))))
      (syn_wa (.classMem (.cv y) (syn_crn (.cv f)))
        (syn_wbr (syn_cfv (syn_ccnv (.cv f)) (.cv x)) (.cv r)
          (syn_cfv (syn_ccnv (.cv f)) (.cv y))))
      p0038 p0070
  have p0072 :=
    @g_anbi2d (syn_wfun (syn_ccnv (.cv f)))
      (syn_wbr (syn_cfv (syn_ccnv (.cv f)) (.cv x)) (syn_ccom (.cv f) (.cv r)) (.cv y))
      (syn_wa (.classMem (.cv y) (syn_crn (.cv f)))
        (syn_wbr (syn_cfv (syn_ccnv (.cv f)) (.cv x)) (.cv r)
          (syn_cfv (syn_ccnv (.cv f)) (.cv y))))
      (.classMem (.cv x) (syn_crn (.cv f))) p0071
  have p0073 :=
    @g_bitrd (syn_wfun (syn_ccnv (.cv f)))
      (syn_wbr (.cv x) (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f))) (.cv y))
      (syn_wa (.classMem (.cv x) (syn_crn (.cv f)))
        (syn_wbr (syn_cfv (syn_ccnv (.cv f)) (.cv x)) (syn_ccom (.cv f) (.cv r)) (.cv y)))
      (syn_wa (.classMem (.cv x) (syn_crn (.cv f)))
        (syn_wa (.classMem (.cv y) (syn_crn (.cv f)))
          (syn_wbr (syn_cfv (syn_ccnv (.cv f)) (.cv x)) (.cv r)
            (syn_cfv (syn_ccnv (.cv f)) (.cv y)))))
      p0036 p0072
  have p0074 :=
    @g_anass (.classMem (.cv x) (syn_crn (.cv f))) (.classMem (.cv y) (syn_crn (.cv f)))
      (syn_wbr (syn_cfv (syn_ccnv (.cv f)) (.cv x)) (.cv r)
        (syn_cfv (syn_ccnv (.cv f)) (.cv y)))
  have p0075 :=
    @g_bicomi
      (syn_wa (syn_wa (.classMem (.cv x) (syn_crn (.cv f)))
          (.classMem (.cv y) (syn_crn (.cv f))))
        (syn_wbr (syn_cfv (syn_ccnv (.cv f)) (.cv x)) (.cv r)
          (syn_cfv (syn_ccnv (.cv f)) (.cv y))))
      (syn_wa (.classMem (.cv x) (syn_crn (.cv f)))
        (syn_wa (.classMem (.cv y) (syn_crn (.cv f)))
          (syn_wbr (syn_cfv (syn_ccnv (.cv f)) (.cv x)) (.cv r)
            (syn_cfv (syn_ccnv (.cv f)) (.cv y)))))
      p0074
  have p0076 :=
    @g_a1i
      (syn_wb (syn_wa (.classMem (.cv x) (syn_crn (.cv f)))
          (syn_wa (.classMem (.cv y) (syn_crn (.cv f)))
            (syn_wbr (syn_cfv (syn_ccnv (.cv f)) (.cv x)) (.cv r)
              (syn_cfv (syn_ccnv (.cv f)) (.cv y))))) (syn_wa
          (syn_wa (.classMem (.cv x) (syn_crn (.cv f))) (.classMem (.cv y) (syn_crn (.cv f))))
          (syn_wbr (syn_cfv (syn_ccnv (.cv f)) (.cv x)) (.cv r)
            (syn_cfv (syn_ccnv (.cv f)) (.cv y)))))
      (syn_wfun (syn_ccnv (.cv f))) p0075
  have p0077 :=
    @g_bitrd (syn_wfun (syn_ccnv (.cv f)))
      (syn_wbr (.cv x) (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f))) (.cv y))
      (syn_wa (.classMem (.cv x) (syn_crn (.cv f)))
        (syn_wa (.classMem (.cv y) (syn_crn (.cv f)))
          (syn_wbr (syn_cfv (syn_ccnv (.cv f)) (.cv x)) (.cv r)
            (syn_cfv (syn_ccnv (.cv f)) (.cv y)))))
      (syn_wa (syn_wa (.classMem (.cv x) (syn_crn (.cv f)))
          (.classMem (.cv y) (syn_crn (.cv f))))
        (syn_wbr (syn_cfv (syn_ccnv (.cv f)) (.cv x)) (.cv r)
          (syn_cfv (syn_ccnv (.cv f)) (.cv y))))
      p0073 p0076
  have p0078 := @g_vex x
  have p0079 := @g_vex y
  have p0080 := @g_simpl (.classEq (.cv z) (.cv x)) (.classEq (.cv w) (.cv y))
  have p0081 :=
    @g_eleq1d (syn_wa (.classEq (.cv z) (.cv x)) (.classEq (.cv w) (.cv y))) (.cv z)
      (.cv x) (syn_crn (.cv f)) p0080
  have p0082 := @g_simpr (.classEq (.cv z) (.cv x)) (.classEq (.cv w) (.cv y))
  have p0083 :=
    @g_eleq1d (syn_wa (.classEq (.cv z) (.cv x)) (.classEq (.cv w) (.cv y))) (.cv w)
      (.cv y) (syn_crn (.cv f)) p0082
  have p0084 :=
    @g_anbi12d (syn_wa (.classEq (.cv z) (.cv x)) (.classEq (.cv w) (.cv y)))
      (.classMem (.cv z) (syn_crn (.cv f))) (.classMem (.cv x) (syn_crn (.cv f)))
      (.classMem (.cv w) (syn_crn (.cv f))) (.classMem (.cv y) (syn_crn (.cv f))) p0081
      p0083
  have p0086 :=
    @g_fveq2d (syn_wa (.classEq (.cv z) (.cv x)) (.classEq (.cv w) (.cv y))) (.cv z)
      (.cv x) (syn_ccnv (.cv f)) p0080
  have p0088 :=
    @g_fveq2d (syn_wa (.classEq (.cv z) (.cv x)) (.classEq (.cv w) (.cv y))) (.cv w)
      (.cv y) (syn_ccnv (.cv f)) p0082
  have p0089 :=
    @g_breq12d (syn_wa (.classEq (.cv z) (.cv x)) (.classEq (.cv w) (.cv y)))
      (syn_cfv (syn_ccnv (.cv f)) (.cv z)) (syn_cfv (syn_ccnv (.cv f)) (.cv x))
      (syn_cfv (syn_ccnv (.cv f)) (.cv w)) (syn_cfv (syn_ccnv (.cv f)) (.cv y)) (.cv r)
      p0086 p0088
  have p0090 :=
    @g_anbi12d (syn_wa (.classEq (.cv z) (.cv x)) (.classEq (.cv w) (.cv y)))
      (syn_wa (.classMem (.cv z) (syn_crn (.cv f))) (.classMem (.cv w) (syn_crn (.cv f))))
      (syn_wa (.classMem (.cv x) (syn_crn (.cv f))) (.classMem (.cv y) (syn_crn (.cv f))))
      (syn_wbr (syn_cfv (syn_ccnv (.cv f)) (.cv z)) (.cv r)
        (syn_cfv (syn_ccnv (.cv f)) (.cv w)))
      (syn_wbr (syn_cfv (syn_ccnv (.cv f)) (.cv x)) (.cv r)
        (syn_cfv (syn_ccnv (.cv f)) (.cv y)))
      p0084 p0089
  have p0092 :=
    @g_braba
      (syn_wa (syn_wa (.classMem (.cv z) (syn_crn (.cv f)))
          (.classMem (.cv w) (syn_crn (.cv f))))
        (syn_wbr (syn_cfv (syn_ccnv (.cv f)) (.cv z)) (.cv r)
          (syn_cfv (syn_ccnv (.cv f)) (.cv w))))
      (syn_wa (syn_wa (.classMem (.cv x) (syn_crn (.cv f)))
          (.classMem (.cv y) (syn_crn (.cv f))))
        (syn_wbr (syn_cfv (syn_ccnv (.cv f)) (.cv x)) (.cv r)
          (syn_cfv (syn_ccnv (.cv f)) (.cv y))))
      z w (.cv x) (.cv y)
      (syn_copab z w (syn_wa (syn_wa (.classMem (.cv z) (syn_crn (.cv f)))
            (.classMem (.cv w) (syn_crn (.cv f))))
          (syn_wbr (syn_cfv (syn_ccnv (.cv f)) (.cv z)) (.cv r)
            (syn_cfv (syn_ccnv (.cv f)) (.cv w)))))
      dv_cache_0010 dv_cache_0024 dv_cache_0011 dv_cache_0019 dv_cache_0025 dv_cache_0026
      dv_cache_0009 p0078 p0079 p0090 p0000
  have p0093 :=
    @g_bicomi
      (syn_wbr (.cv x) (syn_copab z w (syn_wa (syn_wa (.classMem (.cv z) (syn_crn (.cv f)))
              (.classMem (.cv w) (syn_crn (.cv f))))
            (syn_wbr (syn_cfv (syn_ccnv (.cv f)) (.cv z)) (.cv r)
              (syn_cfv (syn_ccnv (.cv f)) (.cv w))))) (.cv y))
      (syn_wa (syn_wa (.classMem (.cv x) (syn_crn (.cv f)))
          (.classMem (.cv y) (syn_crn (.cv f))))
        (syn_wbr (syn_cfv (syn_ccnv (.cv f)) (.cv x)) (.cv r)
          (syn_cfv (syn_ccnv (.cv f)) (.cv y))))
      p0092
  have p0094 :=
    @g_a1i
      (syn_wb (syn_wa (syn_wa (.classMem (.cv x) (syn_crn (.cv f)))
            (.classMem (.cv y) (syn_crn (.cv f))))
          (syn_wbr (syn_cfv (syn_ccnv (.cv f)) (.cv x)) (.cv r)
            (syn_cfv (syn_ccnv (.cv f)) (.cv y)))) (syn_wbr (.cv x) (syn_copab z w (syn_wa
              (syn_wa (.classMem (.cv z) (syn_crn (.cv f)))
                (.classMem (.cv w) (syn_crn (.cv f))))
              (syn_wbr (syn_cfv (syn_ccnv (.cv f)) (.cv z)) (.cv r)
                (syn_cfv (syn_ccnv (.cv f)) (.cv w))))) (.cv y)))
      (syn_wfun (syn_ccnv (.cv f))) p0093
  have p0095 :=
    @g_bitrd (syn_wfun (syn_ccnv (.cv f)))
      (syn_wbr (.cv x) (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f))) (.cv y))
      (syn_wa (syn_wa (.classMem (.cv x) (syn_crn (.cv f)))
          (.classMem (.cv y) (syn_crn (.cv f))))
        (syn_wbr (syn_cfv (syn_ccnv (.cv f)) (.cv x)) (.cv r)
          (syn_cfv (syn_ccnv (.cv f)) (.cv y))))
      (syn_wbr (.cv x) (syn_copab z w (syn_wa (syn_wa (.classMem (.cv z) (syn_crn (.cv f)))
              (.classMem (.cv w) (syn_crn (.cv f))))
            (syn_wbr (syn_cfv (syn_ccnv (.cv f)) (.cv z)) (.cv r)
              (syn_cfv (syn_ccnv (.cv f)) (.cv w))))) (.cv y))
      p0077 p0094
  have p0096 :=
    @g_bitrd (syn_wfun (syn_ccnv (.cv f)))
      (.classMem (syn_cop (.cv x) (.cv y))
        (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f))))
      (syn_wbr (.cv x) (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f))) (.cv y))
      (syn_wbr (.cv x) (syn_copab z w (syn_wa (syn_wa (.classMem (.cv z) (syn_crn (.cv f)))
              (.classMem (.cv w) (syn_crn (.cv f))))
            (syn_wbr (syn_cfv (syn_ccnv (.cv f)) (.cv z)) (.cv r)
              (syn_cfv (syn_ccnv (.cv f)) (.cv w))))) (.cv y))
      p0007 p0095
  have p0097 :=
    (Nominal.biimpRefl (syn_wbr (.cv x) (syn_copab z w (syn_wa
            (syn_wa (.classMem (.cv z) (syn_crn (.cv f))) (.classMem (.cv w) (syn_crn (.cv f))))
            (syn_wbr (syn_cfv (syn_ccnv (.cv f)) (.cv z)) (.cv r)
              (syn_cfv (syn_ccnv (.cv f)) (.cv w))))) (.cv y)))
  have p0098 :=
    @g_a1i
      (syn_wb (syn_wbr (.cv x) (syn_copab z w (syn_wa
              (syn_wa (.classMem (.cv z) (syn_crn (.cv f)))
                (.classMem (.cv w) (syn_crn (.cv f))))
              (syn_wbr (syn_cfv (syn_ccnv (.cv f)) (.cv z)) (.cv r)
                (syn_cfv (syn_ccnv (.cv f)) (.cv w))))) (.cv y))
        (.classMem (syn_cop (.cv x) (.cv y)) (syn_copab z w (syn_wa
              (syn_wa (.classMem (.cv z) (syn_crn (.cv f)))
                (.classMem (.cv w) (syn_crn (.cv f))))
              (syn_wbr (syn_cfv (syn_ccnv (.cv f)) (.cv z)) (.cv r)
                (syn_cfv (syn_ccnv (.cv f)) (.cv w)))))))
      (syn_wfun (syn_ccnv (.cv f))) p0097
  have p0099 :=
    @g_bitrd (syn_wfun (syn_ccnv (.cv f)))
      (.classMem (syn_cop (.cv x) (.cv y))
        (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f))))
      (syn_wbr (.cv x) (syn_copab z w (syn_wa (syn_wa (.classMem (.cv z) (syn_crn (.cv f)))
              (.classMem (.cv w) (syn_crn (.cv f))))
            (syn_wbr (syn_cfv (syn_ccnv (.cv f)) (.cv z)) (.cv r)
              (syn_cfv (syn_ccnv (.cv f)) (.cv w))))) (.cv y))
      (.classMem (syn_cop (.cv x) (.cv y)) (syn_copab z w (syn_wa
            (syn_wa (.classMem (.cv z) (syn_crn (.cv f))) (.classMem (.cv w) (syn_crn (.cv f))))
            (syn_wbr (syn_cfv (syn_ccnv (.cv f)) (.cv z)) (.cv r)
              (syn_cfv (syn_ccnv (.cv f)) (.cv w))))))
      p0096 p0098
  have p0100 :=
    @g_eqrelrdv (syn_wfun (syn_ccnv (.cv f))) x y
      (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f)))
      (syn_copab z w (syn_wa (syn_wa (.classMem (.cv z) (syn_crn (.cv f)))
            (.classMem (.cv w) (syn_crn (.cv f))))
          (syn_wbr (syn_cfv (syn_ccnv (.cv f)) (.cv z)) (.cv r)
            (syn_cfv (syn_ccnv (.cv f)) (.cv w)))))
      dv_cache_0027 dv_cache_0028 dv_cache_0029 dv_cache_0030 dv_cache_0031 dv_cache_0032
      dv_cache_0033 p0099
  have p0101 :=
    @g_syl (syn_wf1o (.cv f) (syn_cdm (.cv f)) (syn_crn (.cv f)))
      (syn_wfun (syn_ccnv (.cv f)))
      (.classEq (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f))) (syn_copab z w (syn_wa
            (syn_wa (.classMem (.cv z) (syn_crn (.cv f))) (.classMem (.cv w) (syn_crn (.cv f))))
            (syn_wbr (syn_cfv (syn_ccnv (.cv f)) (.cv z)) (.cv r)
              (syn_cfv (syn_ccnv (.cv f)) (.cv w))))))
      p0004 p0100
  have p0102 :=
    @g_eqcomd (syn_wf1o (.cv f) (syn_cdm (.cv f)) (syn_crn (.cv f)))
      (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f)))
      (syn_copab z w (syn_wa (syn_wa (.classMem (.cv z) (syn_crn (.cv f)))
            (.classMem (.cv w) (syn_crn (.cv f))))
          (syn_wbr (syn_cfv (syn_ccnv (.cv f)) (.cv z)) (.cv r)
            (syn_cfv (syn_ccnv (.cv f)) (.cv w)))))
      p0101
  have p0103 :=
    @g_isoeq3 (syn_cdm (.cv f)) (syn_crn (.cv f)) (.cv r)
      (syn_copab z w (syn_wa (syn_wa (.classMem (.cv z) (syn_crn (.cv f)))
            (.classMem (.cv w) (syn_crn (.cv f))))
          (syn_wbr (syn_cfv (syn_ccnv (.cv f)) (.cv z)) (.cv r)
            (syn_cfv (syn_ccnv (.cv f)) (.cv w)))))
      (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f))) (.cv f)
  have p0104 :=
    @g_syl (syn_wf1o (.cv f) (syn_cdm (.cv f)) (syn_crn (.cv f)))
      (.classEq (syn_copab z w (syn_wa (syn_wa (.classMem (.cv z) (syn_crn (.cv f)))
              (.classMem (.cv w) (syn_crn (.cv f))))
            (syn_wbr (syn_cfv (syn_ccnv (.cv f)) (.cv z)) (.cv r)
              (syn_cfv (syn_ccnv (.cv f)) (.cv w)))))
        (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f))))
      (syn_wb (syn_wiso (.cv f) (.cv r) (syn_copab z w (syn_wa
              (syn_wa (.classMem (.cv z) (syn_crn (.cv f)))
                (.classMem (.cv w) (syn_crn (.cv f))))
              (syn_wbr (syn_cfv (syn_ccnv (.cv f)) (.cv z)) (.cv r)
                (syn_cfv (syn_ccnv (.cv f)) (.cv w))))) (syn_cdm (.cv f)) (syn_crn (.cv f)))
        (syn_wiso (.cv f) (.cv r) (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f)))
          (syn_cdm (.cv f)) (syn_crn (.cv f))))
      p0102 p0103
  have p0105 :=
    @g_mpbid (syn_wf1o (.cv f) (syn_cdm (.cv f)) (syn_crn (.cv f)))
      (syn_wiso (.cv f) (.cv r) (syn_copab z w (syn_wa
            (syn_wa (.classMem (.cv z) (syn_crn (.cv f))) (.classMem (.cv w) (syn_crn (.cv f))))
            (syn_wbr (syn_cfv (syn_ccnv (.cv f)) (.cv z)) (.cv r)
              (syn_cfv (syn_ccnv (.cv f)) (.cv w))))) (syn_cdm (.cv f)) (syn_crn (.cv f)))
      (syn_wiso (.cv f) (.cv r) (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f)))
        (syn_cdm (.cv f)) (syn_crn (.cv f)))
      p0001 p0104
  have p0106 :=
    @g_isof1o (syn_cdm (.cv f)) (syn_crn (.cv f)) (.cv r)
      (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f))) (.cv f)
  have p0107 :=
    @g_impbii (syn_wf1o (.cv f) (syn_cdm (.cv f)) (syn_crn (.cv f)))
      (syn_wiso (.cv f) (.cv r) (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f)))
        (syn_cdm (.cv f)) (syn_crn (.cv f)))
      p0105 p0106
  exact p0107


end NFChoice.DirectNominalPrf.WPPReplay

end

/-! Certificates from `NominalWPPReplayChunk014Compact001Part037`. -/


section

namespace NFChoice.DirectNominalPrf.WPPReplay

open scoped Fol
open NFChoice.Foundation
open NFChoice.SemanticCore
open NFChoice.ReplaySupport
open NFChoice.Compiler.CompactSourceSyntax

@[expose]
noncomputable def g_isotargettransport (A : Class) (B : Class) (S : Class) (f : Var)
    (r : Var) (_dv_A_f : f ∉ A.fv) (_dv_B_f : f ∉ B.fv) (_dv_S_f : f ∉ S.fv)
    (_dv_f_r : f ≠ r) :
    Nominal.NPrf
      (.imp (syn_wa (syn_wiso (.cv f) (.cv r) S A B) (syn_wss S (syn_cxp B B)))
        (.classEq S (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f))))) :=
  by
  let proofSupport : Finset Var :=
    A.fv ∪ B.fv ∪ S.fv ∪ ({ f } : Finset Var) ∪ ({ r } : Finset Var)
  let x : Var := freshVar proofSupport 0
  let y : Var := freshVar proofSupport 1
  have fresh_x : x ∉ proofSupport :=
    by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_x_not_A : x ∉ A.fv := by
    intro h
    exact
      fresh_x
        (Finset.mem_union_left _ (Finset.mem_union_left _
            (Finset.mem_union_left _ (Finset.mem_union_left _ (h)))))
  have fresh_x_not_B : x ∉ B.fv := by
    intro h
    exact
      fresh_x
        (Finset.mem_union_left _ (Finset.mem_union_left _
            (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))))
  have fresh_x_not_S : x ∉ S.fv := by
    intro h
    exact
      fresh_x
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))
  have fresh_x_ne_f : x ≠ f := by
    intro h
    exact
      fresh_x
        (Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_singleton.mpr h)))
  have fresh_f_ne_x : f ≠ x := Ne.symm fresh_x_ne_f
  have fresh_x_ne_r : x ≠ r := by
    intro h
    exact fresh_x (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))
  have fresh_y : y ∉ proofSupport :=
    by
    change freshVar proofSupport 1 ∉ proofSupport
    exact freshVar_not_mem proofSupport 1
  have fresh_y_not_A : y ∉ A.fv := by
    intro h
    exact
      fresh_y
        (Finset.mem_union_left _ (Finset.mem_union_left _
            (Finset.mem_union_left _ (Finset.mem_union_left _ (h)))))
  have fresh_y_not_B : y ∉ B.fv := by
    intro h
    exact
      fresh_y
        (Finset.mem_union_left _ (Finset.mem_union_left _
            (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))))
  have fresh_y_not_S : y ∉ S.fv := by
    intro h
    exact
      fresh_y
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))
  have fresh_y_ne_f : y ≠ f := by
    intro h
    exact
      fresh_y
        (Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_singleton.mpr h)))
  have fresh_f_ne_y : f ≠ y := Ne.symm fresh_y_ne_f
  have fresh_y_ne_r : y ≠ r := by
    intro h
    exact fresh_y (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))
  have fresh_x_ne_y : x ≠ y :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have dv_cache_0001 : f ≠ x := by exact (show f ≠ x from (by exact fresh_f_ne_x))
  have dv_cache_0002 : f ≠ y := by
    clear dv_cache_0001
    exact (show f ≠ y from (by exact fresh_f_ne_y))
  have dv_cache_0003 : x ∉ (S).fv :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_x_not_S, not_false_eq_true])
  have dv_cache_0004 : y ∉ (S).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_y_not_S, not_false_eq_true])
  have dv_cache_0005 :
    x ∉ ((syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f)))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccom,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv, Finset.mem_union,
          Finset.mem_singleton, fresh_x_ne_f, fresh_x_ne_r, or_false, not_false_eq_true])
  have dv_cache_0006 :
    y ∉ ((syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f)))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccom,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv, Finset.mem_union,
          Finset.mem_singleton, fresh_y_ne_f, fresh_y_ne_r, or_false, not_false_eq_true])
  have dv_cache_0007 :
    x ∉ ((syn_wa (syn_wiso (.cv f) (.cv r) S A B) (syn_wss S (syn_cxp B B)))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_wiso,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wss,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxp, Finset.mem_union,
          Finset.mem_singleton, fresh_x_not_A, fresh_x_not_B, fresh_x_ne_f, fresh_x_ne_r,
          fresh_x_not_S, or_false, not_false_eq_true])
  have dv_cache_0008 :
    y ∉ ((syn_wa (syn_wiso (.cv f) (.cv r) S A B) (syn_wss S (syn_cxp B B)))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_wiso,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wss,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxp, Finset.mem_union,
          Finset.mem_singleton, fresh_y_not_A, fresh_y_not_B, fresh_y_ne_f, fresh_y_ne_r,
          fresh_y_not_S, or_false, not_false_eq_true])
  have dv_cache_0009 : x ≠ y :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008
    exact (show x ≠ y from (by exact fresh_x_ne_y))
  have p0000 := @g_simpr (syn_wiso (.cv f) (.cv r) S A B) (syn_wss S (syn_cxp B B))
  have p0001 :=
    @g_ssbrd (syn_wa (syn_wiso (.cv f) (.cv r) S A B) (syn_wss S (syn_cxp B B))) S
      (syn_cxp B B) (.cv x) (.cv y) p0000
  have p0002 := @g_brxp (.cv x) (.cv y) B B
  have p0003 :=
    @g_a1i
      (syn_wb (syn_wbr (.cv x) (syn_cxp B B) (.cv y))
        (syn_wa (.classMem (.cv x) B) (.classMem (.cv y) B)))
      (syn_wa (syn_wiso (.cv f) (.cv r) S A B) (syn_wss S (syn_cxp B B))) p0002
  have p0004 :=
    @g_sylibd (syn_wa (syn_wiso (.cv f) (.cv r) S A B) (syn_wss S (syn_cxp B B)))
      (syn_wbr (.cv x) S (.cv y)) (syn_wbr (.cv x) (syn_cxp B B) (.cv y))
      (syn_wa (.classMem (.cv x) B) (.classMem (.cv y) B)) p0001 p0003
  have p0010 := @g_simpl (syn_wiso (.cv f) (.cv r) S A B) (syn_wss S (syn_cxp B B))
  have p0011 :=
    @g_adantr (syn_wa (syn_wiso (.cv f) (.cv r) S A B) (syn_wss S (syn_cxp B B)))
      (syn_wiso (.cv f) (.cv r) S A B)
      (syn_wa (.classMem (.cv x) B) (.classMem (.cv y) B)) p0010
  have p0012 :=
    @g_simpr (syn_wa (syn_wiso (.cv f) (.cv r) S A B) (syn_wss S (syn_cxp B B)))
      (syn_wa (.classMem (.cv x) B) (.classMem (.cv y) B))
  have p0013 :=
    @g_jca
      (syn_wa (syn_wa (syn_wiso (.cv f) (.cv r) S A B) (syn_wss S (syn_cxp B B)))
        (syn_wa (.classMem (.cv x) B) (.classMem (.cv y) B)))
      (syn_wiso (.cv f) (.cv r) S A B)
      (syn_wa (.classMem (.cv x) B) (.classMem (.cv y) B)) p0011 p0012
  have p0014 := @g_isocnv A B (.cv r) S (.cv f)
  have p0015 :=
    @g_anim1i (syn_wiso (.cv f) (.cv r) S A B) (syn_wiso (syn_ccnv (.cv f)) S (.cv r) B A)
      (syn_wa (.classMem (.cv x) B) (.classMem (.cv y) B)) p0014
  have p0016 := @g_isorel B A (.cv x) (.cv y) S (.cv r) (syn_ccnv (.cv f))
  have p0017 :=
    @g_syl
      (syn_wa (syn_wiso (.cv f) (.cv r) S A B)
        (syn_wa (.classMem (.cv x) B) (.classMem (.cv y) B)))
      (syn_wa (syn_wiso (syn_ccnv (.cv f)) S (.cv r) B A)
        (syn_wa (.classMem (.cv x) B) (.classMem (.cv y) B)))
      (syn_wb (syn_wbr (.cv x) S (.cv y)) (syn_wbr (syn_cfv (syn_ccnv (.cv f)) (.cv x)) (.cv r)
          (syn_cfv (syn_ccnv (.cv f)) (.cv y))))
      p0015 p0016
  have p0018 :=
    @g_syl
      (syn_wa (syn_wa (syn_wiso (.cv f) (.cv r) S A B) (syn_wss S (syn_cxp B B)))
        (syn_wa (.classMem (.cv x) B) (.classMem (.cv y) B)))
      (syn_wa (syn_wiso (.cv f) (.cv r) S A B)
        (syn_wa (.classMem (.cv x) B) (.classMem (.cv y) B)))
      (syn_wb (syn_wbr (.cv x) S (.cv y)) (syn_wbr (syn_cfv (syn_ccnv (.cv f)) (.cv x)) (.cv r)
          (syn_cfv (syn_ccnv (.cv f)) (.cv y))))
      p0013 p0017
  have p0019 :=
    @g_ex (syn_wa (syn_wiso (.cv f) (.cv r) S A B) (syn_wss S (syn_cxp B B)))
      (syn_wa (.classMem (.cv x) B) (.classMem (.cv y) B))
      (syn_wb (syn_wbr (.cv x) S (.cv y)) (syn_wbr (syn_cfv (syn_ccnv (.cv f)) (.cv x)) (.cv r)
          (syn_cfv (syn_ccnv (.cv f)) (.cv y))))
      p0018
  have p0020 :=
    @g_bi1 (syn_wbr (.cv x) S (.cv y))
      (syn_wbr (syn_cfv (syn_ccnv (.cv f)) (.cv x)) (.cv r)
        (syn_cfv (syn_ccnv (.cv f)) (.cv y)))
  have p0021 :=
    @g_syl6 (syn_wa (syn_wiso (.cv f) (.cv r) S A B) (syn_wss S (syn_cxp B B)))
      (syn_wa (.classMem (.cv x) B) (.classMem (.cv y) B))
      (syn_wb (syn_wbr (.cv x) S (.cv y)) (syn_wbr (syn_cfv (syn_ccnv (.cv f)) (.cv x)) (.cv r)
          (syn_cfv (syn_ccnv (.cv f)) (.cv y))))
      (.imp (syn_wbr (.cv x) S (.cv y)) (syn_wbr (syn_cfv (syn_ccnv (.cv f)) (.cv x)) (.cv r)
          (syn_cfv (syn_ccnv (.cv f)) (.cv y))))
      p0019 p0020
  have p0022 :=
    @g_com23 (syn_wa (syn_wiso (.cv f) (.cv r) S A B) (syn_wss S (syn_cxp B B)))
      (syn_wa (.classMem (.cv x) B) (.classMem (.cv y) B)) (syn_wbr (.cv x) S (.cv y))
      (syn_wbr (syn_cfv (syn_ccnv (.cv f)) (.cv x)) (.cv r)
        (syn_cfv (syn_ccnv (.cv f)) (.cv y)))
      p0021
  have p0023 :=
    @g_mpdd (syn_wa (syn_wiso (.cv f) (.cv r) S A B) (syn_wss S (syn_cxp B B)))
      (syn_wbr (.cv x) S (.cv y)) (syn_wa (.classMem (.cv x) B) (.classMem (.cv y) B))
      (syn_wbr (syn_cfv (syn_ccnv (.cv f)) (.cv x)) (.cv r)
        (syn_cfv (syn_ccnv (.cv f)) (.cv y)))
      p0004 p0022
  have p0024 :=
    @g_jcad (syn_wa (syn_wiso (.cv f) (.cv r) S A B) (syn_wss S (syn_cxp B B)))
      (syn_wbr (.cv x) S (.cv y)) (syn_wa (.classMem (.cv x) B) (.classMem (.cv y) B))
      (syn_wbr (syn_cfv (syn_ccnv (.cv f)) (.cv x)) (.cv r)
        (syn_cfv (syn_ccnv (.cv f)) (.cv y)))
      p0004 p0023
  have p0035 :=
    @g_bi2 (syn_wbr (.cv x) S (.cv y))
      (syn_wbr (syn_cfv (syn_ccnv (.cv f)) (.cv x)) (.cv r)
        (syn_cfv (syn_ccnv (.cv f)) (.cv y)))
  have p0036 :=
    @g_syl6 (syn_wa (syn_wiso (.cv f) (.cv r) S A B) (syn_wss S (syn_cxp B B)))
      (syn_wa (.classMem (.cv x) B) (.classMem (.cv y) B))
      (syn_wb (syn_wbr (.cv x) S (.cv y)) (syn_wbr (syn_cfv (syn_ccnv (.cv f)) (.cv x)) (.cv r)
          (syn_cfv (syn_ccnv (.cv f)) (.cv y))))
      (.imp (syn_wbr (syn_cfv (syn_ccnv (.cv f)) (.cv x)) (.cv r)
          (syn_cfv (syn_ccnv (.cv f)) (.cv y))) (syn_wbr (.cv x) S (.cv y)))
      p0019 p0035
  have p0037 :=
    @g_imp3a (syn_wa (syn_wiso (.cv f) (.cv r) S A B) (syn_wss S (syn_cxp B B)))
      (syn_wa (.classMem (.cv x) B) (.classMem (.cv y) B))
      (syn_wbr (syn_cfv (syn_ccnv (.cv f)) (.cv x)) (.cv r)
        (syn_cfv (syn_ccnv (.cv f)) (.cv y)))
      (syn_wbr (.cv x) S (.cv y)) p0036
  have p0038 :=
    @g_impbid (syn_wa (syn_wiso (.cv f) (.cv r) S A B) (syn_wss S (syn_cxp B B)))
      (syn_wbr (.cv x) S (.cv y))
      (syn_wa (syn_wa (.classMem (.cv x) B) (.classMem (.cv y) B))
        (syn_wbr (syn_cfv (syn_ccnv (.cv f)) (.cv x)) (.cv r)
          (syn_cfv (syn_ccnv (.cv f)) (.cv y))))
      p0024 p0037
  have p0040 := @g_isof1o A B (.cv r) S (.cv f)
  have p0041 :=
    @g_syl (syn_wa (syn_wiso (.cv f) (.cv r) S A B) (syn_wss S (syn_cxp B B)))
      (syn_wiso (.cv f) (.cv r) S A B) (syn_wf1o (.cv f) A B) p0010 p0040
  have p0042 := @g_f1ocnv A B (.cv f)
  have p0043 :=
    @g_syl (syn_wa (syn_wiso (.cv f) (.cv r) S A B) (syn_wss S (syn_cxp B B)))
      (syn_wf1o (.cv f) A B) (syn_wf1o (syn_ccnv (.cv f)) B A) p0041 p0042
  have p0044 := @g_f1ofun B A (syn_ccnv (.cv f))
  have p0045 :=
    @g_syl (syn_wa (syn_wiso (.cv f) (.cv r) S A B) (syn_wss S (syn_cxp B B)))
      (syn_wf1o (syn_ccnv (.cv f)) B A) (syn_wfun (syn_ccnv (.cv f))) p0043 p0044
  have p0046 := @g_hwtrnbrd x y f r dv_cache_0001 dv_cache_0002
  have p0047 :=
    @g_syl (syn_wa (syn_wiso (.cv f) (.cv r) S A B) (syn_wss S (syn_cxp B B)))
      (syn_wfun (syn_ccnv (.cv f)))
      (syn_wb (syn_wbr (.cv x) (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f))) (.cv y))
        (syn_wa (syn_wa (.classMem (.cv x) (syn_crn (.cv f)))
            (.classMem (.cv y) (syn_crn (.cv f))))
          (syn_wbr (syn_cfv (syn_ccnv (.cv f)) (.cv x)) (.cv r)
            (syn_cfv (syn_ccnv (.cv f)) (.cv y)))))
      p0045 p0046
  have p0051 := @g_f1ofo A B (.cv f)
  have p0052 :=
    @g_syl (syn_wa (syn_wiso (.cv f) (.cv r) S A B) (syn_wss S (syn_cxp B B)))
      (syn_wf1o (.cv f) A B) (syn_wfo (.cv f) A B) p0041 p0051
  have p0053 := @g_forn A B (.cv f)
  have p0054 :=
    @g_syl (syn_wa (syn_wiso (.cv f) (.cv r) S A B) (syn_wss S (syn_cxp B B)))
      (syn_wfo (.cv f) A B) (.classEq (syn_crn (.cv f)) B) p0052 p0053
  have p0055 :=
    @g_eleq2d (syn_wa (syn_wiso (.cv f) (.cv r) S A B) (syn_wss S (syn_cxp B B)))
      (syn_crn (.cv f)) B (.cv x) p0054
  have p0063 :=
    @g_eleq2d (syn_wa (syn_wiso (.cv f) (.cv r) S A B) (syn_wss S (syn_cxp B B)))
      (syn_crn (.cv f)) B (.cv y) p0054
  have p0064 :=
    @g_anbi12d (syn_wa (syn_wiso (.cv f) (.cv r) S A B) (syn_wss S (syn_cxp B B)))
      (.classMem (.cv x) (syn_crn (.cv f))) (.classMem (.cv x) B)
      (.classMem (.cv y) (syn_crn (.cv f))) (.classMem (.cv y) B) p0055 p0063
  have p0065 :=
    @g_anbi1d (syn_wa (syn_wiso (.cv f) (.cv r) S A B) (syn_wss S (syn_cxp B B)))
      (syn_wa (.classMem (.cv x) (syn_crn (.cv f))) (.classMem (.cv y) (syn_crn (.cv f))))
      (syn_wa (.classMem (.cv x) B) (.classMem (.cv y) B))
      (syn_wbr (syn_cfv (syn_ccnv (.cv f)) (.cv x)) (.cv r)
        (syn_cfv (syn_ccnv (.cv f)) (.cv y)))
      p0064
  have p0066 :=
    @g_bitrd (syn_wa (syn_wiso (.cv f) (.cv r) S A B) (syn_wss S (syn_cxp B B)))
      (syn_wbr (.cv x) (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f))) (.cv y))
      (syn_wa (syn_wa (.classMem (.cv x) (syn_crn (.cv f)))
          (.classMem (.cv y) (syn_crn (.cv f))))
        (syn_wbr (syn_cfv (syn_ccnv (.cv f)) (.cv x)) (.cv r)
          (syn_cfv (syn_ccnv (.cv f)) (.cv y))))
      (syn_wa (syn_wa (.classMem (.cv x) B) (.classMem (.cv y) B))
        (syn_wbr (syn_cfv (syn_ccnv (.cv f)) (.cv x)) (.cv r)
          (syn_cfv (syn_ccnv (.cv f)) (.cv y))))
      p0047 p0065
  have p0067 :=
    @g_bitr4d (syn_wa (syn_wiso (.cv f) (.cv r) S A B) (syn_wss S (syn_cxp B B)))
      (syn_wbr (.cv x) S (.cv y))
      (syn_wa (syn_wa (.classMem (.cv x) B) (.classMem (.cv y) B))
        (syn_wbr (syn_cfv (syn_ccnv (.cv f)) (.cv x)) (.cv r)
          (syn_cfv (syn_ccnv (.cv f)) (.cv y))))
      (syn_wbr (.cv x) (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f))) (.cv y))
      p0038 p0066
  have p0068 := (Nominal.biimpRefl (syn_wbr (.cv x) S (.cv y)))
  have p0069 :=
    @g_bicomi (syn_wbr (.cv x) S (.cv y)) (.classMem (syn_cop (.cv x) (.cv y)) S) p0068
  have p0070 :=
    @g_a1i (syn_wb (.classMem (syn_cop (.cv x) (.cv y)) S) (syn_wbr (.cv x) S (.cv y)))
      (syn_wa (syn_wiso (.cv f) (.cv r) S A B) (syn_wss S (syn_cxp B B))) p0069
  have p0071 :=
    (Nominal.biimpRefl
      (syn_wbr (.cv x) (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f))) (.cv y)))
  have p0072 :=
    @g_bicomi
      (syn_wbr (.cv x) (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f))) (.cv y))
      (.classMem (syn_cop (.cv x) (.cv y))
        (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f))))
      p0071
  have p0073 :=
    @g_a1i
      (syn_wb (.classMem (syn_cop (.cv x) (.cv y))
          (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f))))
        (syn_wbr (.cv x) (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f))) (.cv y)))
      (syn_wa (syn_wiso (.cv f) (.cv r) S A B) (syn_wss S (syn_cxp B B))) p0072
  have p0074 :=
    @g_n_3bitr4d (syn_wa (syn_wiso (.cv f) (.cv r) S A B) (syn_wss S (syn_cxp B B)))
      (syn_wbr (.cv x) S (.cv y))
      (syn_wbr (.cv x) (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f))) (.cv y))
      (.classMem (syn_cop (.cv x) (.cv y)) S)
      (.classMem (syn_cop (.cv x) (.cv y))
        (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f))))
      p0067 p0070 p0073
  have p0075 :=
    @g_eqrelrdv (syn_wa (syn_wiso (.cv f) (.cv r) S A B) (syn_wss S (syn_cxp B B))) x y S
      (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f))) dv_cache_0003 dv_cache_0004
      dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 p0074
  exact p0075

@[expose]
noncomputable def g_elhwnisogeniso (v : Var) (u : Var) (A : Class) (f : Var) (r : Var)
    (dv_A_f : f ∉ A.fv) (dv_A_r : r ∉ A.fv) (dv_f_r : f ≠ r) (dv_f_u : f ≠ u)
    (dv_f_v : f ≠ v) (dv_r_u : r ≠ u) (dv_r_v : r ≠ v) :
    Nominal.NPrf
      (syn_wb (syn_wbr (.cv u) (syn_chwniso A) (.cv v)) (syn_wa
          (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))
          (syn_wex f (syn_wrex r (syn_cvv) (syn_wa (syn_wiso (.cv f) (.cv r)
                  (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f)))
                  (syn_cdm (.cv f)) (syn_crn (.cv f)))
                (syn_wa (.classEq (syn_cop (.cv r) (syn_cdm (.cv f))) (.cv u)) (.classEq
                    (syn_cop (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f)))
                      (syn_crn (.cv f))) (.cv v)))))))) :=
  by
  have dv_cache_0001 : f ∉ (A).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : f ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_A_f, not_false_eq_true])
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
  have dv_cache_0003 : f ≠ r :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact (show f ≠ r from (by exact dv_f_r))
  have dv_cache_0004 : f ≠ u :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact (show f ≠ u from (by exact dv_f_u))
  have dv_cache_0005 : f ≠ v :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact (show f ≠ v from (by exact dv_f_v))
  have dv_cache_0006 : r ≠ u :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact (show r ≠ u from (by exact dv_r_u))
  have dv_cache_0007 : r ≠ v :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006
    exact (show r ≠ v from (by exact dv_r_v))
  have dv_cache_0008 : r ∉ ((syn_wf1o (.cv f) (syn_cdm (.cv f)) (syn_crn (.cv f)))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007
    exact
      (by
        have compact_fv_not_mem_empty : r ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wf1o,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdm,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_crn, Finset.mem_union,
          Finset.mem_singleton, (Ne.symm dv_f_r), or_false, not_false_eq_true])
  have p0000 :=
    @g_elhwnisogenf1o v u A f r dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
      dv_cache_0005 dv_cache_0006 dv_cache_0007
  have p0001 :=
    @g_r19_42v (syn_wf1o (.cv f) (syn_cdm (.cv f)) (syn_crn (.cv f)))
      (syn_wa (.classEq (syn_cop (.cv r) (syn_cdm (.cv f))) (.cv u)) (.classEq
          (syn_cop (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f))) (syn_crn (.cv f)))
          (.cv v)))
      r (syn_cvv) dv_cache_0008
  have p0002 :=
    @g_bicomi
      (syn_wrex r (syn_cvv) (syn_wa (syn_wf1o (.cv f) (syn_cdm (.cv f)) (syn_crn (.cv f)))
          (syn_wa (.classEq (syn_cop (.cv r) (syn_cdm (.cv f))) (.cv u)) (.classEq
              (syn_cop (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f)))
                (syn_crn (.cv f))) (.cv v)))))
      (syn_wa (syn_wf1o (.cv f) (syn_cdm (.cv f)) (syn_crn (.cv f))) (syn_wrex r (syn_cvv)
          (syn_wa (.classEq (syn_cop (.cv r) (syn_cdm (.cv f))) (.cv u)) (.classEq
              (syn_cop (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f)))
                (syn_crn (.cv f))) (.cv v)))))
      p0001
  have p0003 := @g_hwtrnisob f r
  have p0004 :=
    @g_anbi1i (syn_wf1o (.cv f) (syn_cdm (.cv f)) (syn_crn (.cv f)))
      (syn_wiso (.cv f) (.cv r) (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f)))
        (syn_cdm (.cv f)) (syn_crn (.cv f)))
      (syn_wa (.classEq (syn_cop (.cv r) (syn_cdm (.cv f))) (.cv u)) (.classEq
          (syn_cop (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f))) (syn_crn (.cv f)))
          (.cv v)))
      p0003
  have p0005 :=
    @g_rexbii
      (syn_wa (syn_wf1o (.cv f) (syn_cdm (.cv f)) (syn_crn (.cv f)))
        (syn_wa (.classEq (syn_cop (.cv r) (syn_cdm (.cv f))) (.cv u)) (.classEq
            (syn_cop (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f))) (syn_crn (.cv f)))
            (.cv v))))
      (syn_wa (syn_wiso (.cv f) (.cv r) (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f)))
          (syn_cdm (.cv f)) (syn_crn (.cv f)))
        (syn_wa (.classEq (syn_cop (.cv r) (syn_cdm (.cv f))) (.cv u)) (.classEq
            (syn_cop (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f))) (syn_crn (.cv f)))
            (.cv v))))
      r (syn_cvv) p0004
  have p0006 :=
    @g_bitri
      (syn_wa (syn_wf1o (.cv f) (syn_cdm (.cv f)) (syn_crn (.cv f))) (syn_wrex r (syn_cvv)
          (syn_wa (.classEq (syn_cop (.cv r) (syn_cdm (.cv f))) (.cv u)) (.classEq
              (syn_cop (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f)))
                (syn_crn (.cv f))) (.cv v)))))
      (syn_wrex r (syn_cvv) (syn_wa (syn_wf1o (.cv f) (syn_cdm (.cv f)) (syn_crn (.cv f)))
          (syn_wa (.classEq (syn_cop (.cv r) (syn_cdm (.cv f))) (.cv u)) (.classEq
              (syn_cop (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f)))
                (syn_crn (.cv f))) (.cv v)))))
      (syn_wrex r (syn_cvv) (syn_wa (syn_wiso (.cv f) (.cv r)
            (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f))) (syn_cdm (.cv f))
            (syn_crn (.cv f))) (syn_wa (.classEq (syn_cop (.cv r) (syn_cdm (.cv f))) (.cv u))
            (.classEq (syn_cop (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f)))
                (syn_crn (.cv f))) (.cv v)))))
      p0002 p0005
  have p0007 :=
    @g_exbii
      (syn_wa (syn_wf1o (.cv f) (syn_cdm (.cv f)) (syn_crn (.cv f))) (syn_wrex r (syn_cvv)
          (syn_wa (.classEq (syn_cop (.cv r) (syn_cdm (.cv f))) (.cv u)) (.classEq
              (syn_cop (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f)))
                (syn_crn (.cv f))) (.cv v)))))
      (syn_wrex r (syn_cvv) (syn_wa (syn_wiso (.cv f) (.cv r)
            (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f))) (syn_cdm (.cv f))
            (syn_crn (.cv f))) (syn_wa (.classEq (syn_cop (.cv r) (syn_cdm (.cv f))) (.cv u))
            (.classEq (syn_cop (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f)))
                (syn_crn (.cv f))) (.cv v)))))
      f p0006
  have p0008 :=
    @g_anbi2i
      (syn_wex f (syn_wa (syn_wf1o (.cv f) (syn_cdm (.cv f)) (syn_crn (.cv f)))
          (syn_wrex r (syn_cvv) (syn_wa (.classEq (syn_cop (.cv r) (syn_cdm (.cv f))) (.cv u))
              (.classEq (syn_cop (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f)))
                  (syn_crn (.cv f))) (.cv v))))))
      (syn_wex f (syn_wrex r (syn_cvv) (syn_wa (syn_wiso (.cv f) (.cv r)
              (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f))) (syn_cdm (.cv f))
              (syn_crn (.cv f))) (syn_wa (.classEq (syn_cop (.cv r) (syn_cdm (.cv f))) (.cv u))
              (.classEq (syn_cop (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f)))
                  (syn_crn (.cv f))) (.cv v))))))
      (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A))) p0007
  have p0009 :=
    @g_bitri (syn_wbr (.cv u) (syn_chwniso A) (.cv v))
      (syn_wa (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))
        (syn_wex f (syn_wa (syn_wf1o (.cv f) (syn_cdm (.cv f)) (syn_crn (.cv f)))
            (syn_wrex r (syn_cvv) (syn_wa (.classEq (syn_cop (.cv r) (syn_cdm (.cv f))) (.cv u))
                (.classEq (syn_cop (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f)))
                    (syn_crn (.cv f))) (.cv v)))))))
      (syn_wa (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))
        (syn_wex f (syn_wrex r (syn_cvv) (syn_wa (syn_wiso (.cv f) (.cv r)
                (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f))) (syn_cdm (.cv f))
                (syn_crn (.cv f)))
              (syn_wa (.classEq (syn_cop (.cv r) (syn_cdm (.cv f))) (.cv u)) (.classEq
                  (syn_cop (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f)))
                    (syn_crn (.cv f))) (.cv v)))))))
      p0000 p0008
  exact p0009

@[expose]
noncomputable def g_hwcnraw (u : Var) (A : Class) :
    Nominal.NPrf
      (.imp (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv u) (syn_chwcodes A))) :=
  by
  have p0000 := @g_elhwcn u A
  have p0001 :=
    @g_biimpi (.classMem (.cv u) (syn_chwcn A))
      (syn_wa (.classMem (.cv u) (syn_chwcodes A)) (syn_wss (syn_cfv (syn_c1st) (.cv u))
          (syn_cxp (syn_cfv (syn_c2nd) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)))))
      p0000
  have p0002 :=
    @g_simpld (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv u) (syn_chwcodes A))
      (syn_wss (syn_cfv (syn_c1st) (.cv u))
        (syn_cxp (syn_cfv (syn_c2nd) (.cv u)) (syn_cfv (syn_c2nd) (.cv u))))
      p0001
  exact p0002

@[expose]
noncomputable def g_hwcnsupp (u : Var) (A : Class) :
    Nominal.NPrf
      (.imp (.classMem (.cv u) (syn_chwcn A)) (syn_wss (syn_cfv (syn_c1st) (.cv u))
          (syn_cxp (syn_cfv (syn_c2nd) (.cv u)) (syn_cfv (syn_c2nd) (.cv u))))) :=
  by
  have p0000 := @g_elhwcn u A
  have p0001 :=
    @g_biimpi (.classMem (.cv u) (syn_chwcn A))
      (syn_wa (.classMem (.cv u) (syn_chwcodes A)) (syn_wss (syn_cfv (syn_c1st) (.cv u))
          (syn_cxp (syn_cfv (syn_c2nd) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)))))
      p0000
  have p0002 :=
    @g_simprd (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv u) (syn_chwcodes A))
      (syn_wss (syn_cfv (syn_c1st) (.cv u))
        (syn_cxp (syn_cfv (syn_c2nd) (.cv u)) (syn_cfv (syn_c2nd) (.cv u))))
      p0001
  exact p0002

@[expose]
noncomputable def g_hwcnpair (u : Var) (A : Class) :
    Nominal.NPrf
      (.imp (.classMem (.cv u) (syn_chwcn A)) (.classEq (.cv u)
          (syn_cop (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u))))) :=
  by
  have p0000 := @g_elhwcn u A
  have p0001 :=
    @g_biimpi (.classMem (.cv u) (syn_chwcn A))
      (syn_wa (.classMem (.cv u) (syn_chwcodes A)) (syn_wss (syn_cfv (syn_c1st) (.cv u))
          (syn_cxp (syn_cfv (syn_c2nd) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)))))
      p0000
  have p0002 :=
    @g_simpld (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv u) (syn_chwcodes A))
      (syn_wss (syn_cfv (syn_c1st) (.cv u))
        (syn_cxp (syn_cfv (syn_c2nd) (.cv u)) (syn_cfv (syn_c2nd) (.cv u))))
      p0001
  have p0003 := (Nominal.classEqRefl (syn_chwcodes A))
  have p0004 :=
    @g_eleq2i (syn_chwcodes A) (syn_cin (syn_cwe) (syn_cxp (syn_cvv) (syn_cpw A))) (.cv u)
      p0003
  have p0005 :=
    @g_biimpi (.classMem (.cv u) (syn_chwcodes A))
      (.classMem (.cv u) (syn_cin (syn_cwe) (syn_cxp (syn_cvv) (syn_cpw A)))) p0004
  have p0006 :=
    @g_syl (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv u) (syn_chwcodes A))
      (.classMem (.cv u) (syn_cin (syn_cwe) (syn_cxp (syn_cvv) (syn_cpw A)))) p0002 p0005
  have p0007 := @g_elin (.cv u) (syn_cwe) (syn_cxp (syn_cvv) (syn_cpw A))
  have p0008 :=
    @g_biimpi (.classMem (.cv u) (syn_cin (syn_cwe) (syn_cxp (syn_cvv) (syn_cpw A))))
      (syn_wa (.classMem (.cv u) (syn_cwe)) (.classMem (.cv u) (syn_cxp (syn_cvv) (syn_cpw A))))
      p0007
  have p0009 :=
    @g_syl (.classMem (.cv u) (syn_chwcn A))
      (.classMem (.cv u) (syn_cin (syn_cwe) (syn_cxp (syn_cvv) (syn_cpw A))))
      (syn_wa (.classMem (.cv u) (syn_cwe)) (.classMem (.cv u) (syn_cxp (syn_cvv) (syn_cpw A))))
      p0006 p0008
  have p0010 :=
    @g_simprd (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv u) (syn_cwe))
      (.classMem (.cv u) (syn_cxp (syn_cvv) (syn_cpw A))) p0009
  have p0011 := @g_n_1st2nd2 (.cv u) (syn_cvv) (syn_cpw A)
  have p0012 :=
    @g_syl (.classMem (.cv u) (syn_chwcn A))
      (.classMem (.cv u) (syn_cxp (syn_cvv) (syn_cpw A)))
      (.classEq (.cv u) (syn_cop (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u))))
      p0010 p0011
  exact p0012


end NFChoice.DirectNominalPrf.WPPReplay

end

/-! Certificates from `NominalWPPReplayChunk014Compact001Part038`. -/


section

namespace NFChoice.DirectNominalPrf.WPPReplay

open scoped Fol
open NFChoice.Foundation
open NFChoice.SemanticCore
open NFChoice.ReplaySupport
open NFChoice.Compiler.CompactSourceSyntax

@[expose]
noncomputable def g_hwnisorawgeni (v : Var) (u : Var) (A : Class) (f : Var) (r : Var)
    (_dv_A_f : f ∉ A.fv) (dv_A_r : r ∉ A.fv) (dv_f_r : f ≠ r) (dv_f_u : f ≠ u)
    (dv_f_v : f ≠ v) (dv_r_u : r ≠ u) (dv_r_v : r ≠ v) (_dv_u_v : u ≠ v) :
    Nominal.NPrf
      (.imp (syn_wa (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))
          (syn_wiso (.cv f) (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c1st) (.cv v))
            (syn_cfv (syn_c2nd) (.cv u)) (syn_cfv (syn_c2nd) (.cv v)))) (syn_wrex r (syn_cvv)
          (syn_wa (syn_wiso (.cv f) (.cv r)
              (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f))) (syn_cdm (.cv f))
              (syn_crn (.cv f))) (syn_wa (.classEq (syn_cop (.cv r) (syn_cdm (.cv f))) (.cv u))
              (.classEq (syn_cop (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f)))
                  (syn_crn (.cv f))) (.cv v)))))) :=
  by
  have dv_cache_0001 : r ∉ ((syn_cfv (syn_c1st) (.cv u))).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : r ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1st,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, dv_r_u, compact_fv_not_mem_empty, or_false,
          not_false_eq_true])
  have dv_cache_0002 : r ∉ ((syn_cvv)).fv :=
    by
    clear dv_cache_0001
    exact
      (by
        have compact_fv_not_mem_empty : r ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv,
          compact_fv_not_mem_empty, not_false_eq_true])
  have dv_cache_0003 : f ∉ ((syn_cfv (syn_c2nd) (.cv u))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact
      (by
        have compact_fv_not_mem_empty : f ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c2nd,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, dv_f_u, compact_fv_not_mem_empty, or_false,
          not_false_eq_true])
  have dv_cache_0004 : f ∉ ((syn_cfv (syn_c2nd) (.cv v))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact
      (by
        have compact_fv_not_mem_empty : f ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c2nd,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, dv_f_v, compact_fv_not_mem_empty, or_false,
          not_false_eq_true])
  have dv_cache_0005 : f ∉ ((syn_cfv (syn_c1st) (.cv v))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact
      (by
        have compact_fv_not_mem_empty : f ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1st,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, dv_f_v, compact_fv_not_mem_empty, or_false,
          not_false_eq_true])
  have dv_cache_0006 : f ≠ r :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact (show f ≠ r from (by exact dv_f_r))
  have dv_cache_0007 :
    r ∉
      ((syn_wa (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))
          (syn_wiso (.cv f) (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c1st) (.cv v))
            (syn_cfv (syn_c2nd) (.cv u)) (syn_cfv (syn_c2nd) (.cv v))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006
    exact
      (by
        have compact_fv_not_mem_empty : r ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwcn,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_wiso,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1st,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c2nd, Finset.mem_union,
          Finset.mem_singleton, dv_r_u, dv_A_r, dv_r_v, (Ne.symm dv_f_r),
          compact_fv_not_mem_empty, or_false, not_false_eq_true])
  have p0000 := @g_fvex (.cv u) (syn_c1st)
  have p0001 :=
    @g_risset r (syn_cfv (syn_c1st) (.cv u)) (syn_cvv) dv_cache_0001 dv_cache_0002
  have p0002 :=
    @g_mpbi (.classMem (syn_cfv (syn_c1st) (.cv u)) (syn_cvv))
      (syn_wrex r (syn_cvv) (.classEq (.cv r) (syn_cfv (syn_c1st) (.cv u)))) p0000 p0001
  have p0003 :=
    @g_a1i (syn_wrex r (syn_cvv) (.classEq (.cv r) (syn_cfv (syn_c1st) (.cv u))))
      (syn_wa (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))
        (syn_wiso (.cv f) (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c1st) (.cv v))
          (syn_cfv (syn_c2nd) (.cv u)) (syn_cfv (syn_c2nd) (.cv v))))
      p0002
  have p0004 :=
    @g_simpl
      (syn_wa (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))
        (syn_wiso (.cv f) (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c1st) (.cv v))
          (syn_cfv (syn_c2nd) (.cv u)) (syn_cfv (syn_c2nd) (.cv v))))
      (.classEq (.cv r) (syn_cfv (syn_c1st) (.cv u)))
  have p0005 :=
    @g_simpr (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))
      (syn_wiso (.cv f) (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c1st) (.cv v))
        (syn_cfv (syn_c2nd) (.cv u)) (syn_cfv (syn_c2nd) (.cv v)))
  have p0006 :=
    @g_syl
      (syn_wa (syn_wa
          (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))
          (syn_wiso (.cv f) (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c1st) (.cv v))
            (syn_cfv (syn_c2nd) (.cv u)) (syn_cfv (syn_c2nd) (.cv v))))
        (.classEq (.cv r) (syn_cfv (syn_c1st) (.cv u))))
      (syn_wa (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))
        (syn_wiso (.cv f) (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c1st) (.cv v))
          (syn_cfv (syn_c2nd) (.cv u)) (syn_cfv (syn_c2nd) (.cv v))))
      (syn_wiso (.cv f) (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c1st) (.cv v))
        (syn_cfv (syn_c2nd) (.cv u)) (syn_cfv (syn_c2nd) (.cv v)))
      p0004 p0005
  have p0007 :=
    @g_simpr
      (syn_wa (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))
        (syn_wiso (.cv f) (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c1st) (.cv v))
          (syn_cfv (syn_c2nd) (.cv u)) (syn_cfv (syn_c2nd) (.cv v))))
      (.classEq (.cv r) (syn_cfv (syn_c1st) (.cv u)))
  have p0008 :=
    @g_isoeq2 (syn_cfv (syn_c2nd) (.cv u)) (syn_cfv (syn_c2nd) (.cv v)) (.cv r)
      (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c1st) (.cv u)) (.cv f)
  have p0009 :=
    @g_syl
      (syn_wa (syn_wa
          (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))
          (syn_wiso (.cv f) (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c1st) (.cv v))
            (syn_cfv (syn_c2nd) (.cv u)) (syn_cfv (syn_c2nd) (.cv v))))
        (.classEq (.cv r) (syn_cfv (syn_c1st) (.cv u))))
      (.classEq (.cv r) (syn_cfv (syn_c1st) (.cv u)))
      (syn_wb (syn_wiso (.cv f) (.cv r) (syn_cfv (syn_c1st) (.cv v))
          (syn_cfv (syn_c2nd) (.cv u)) (syn_cfv (syn_c2nd) (.cv v)))
        (syn_wiso (.cv f) (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c1st) (.cv v))
          (syn_cfv (syn_c2nd) (.cv u)) (syn_cfv (syn_c2nd) (.cv v))))
      p0007 p0008
  have p0010 :=
    @g_biimprd
      (syn_wa (syn_wa
          (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))
          (syn_wiso (.cv f) (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c1st) (.cv v))
            (syn_cfv (syn_c2nd) (.cv u)) (syn_cfv (syn_c2nd) (.cv v))))
        (.classEq (.cv r) (syn_cfv (syn_c1st) (.cv u))))
      (syn_wiso (.cv f) (.cv r) (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv u))
        (syn_cfv (syn_c2nd) (.cv v)))
      (syn_wiso (.cv f) (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c1st) (.cv v))
        (syn_cfv (syn_c2nd) (.cv u)) (syn_cfv (syn_c2nd) (.cv v)))
      p0009
  have p0011 :=
    @g_mpd
      (syn_wa (syn_wa
          (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))
          (syn_wiso (.cv f) (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c1st) (.cv v))
            (syn_cfv (syn_c2nd) (.cv u)) (syn_cfv (syn_c2nd) (.cv v))))
        (.classEq (.cv r) (syn_cfv (syn_c1st) (.cv u))))
      (syn_wiso (.cv f) (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c1st) (.cv v))
        (syn_cfv (syn_c2nd) (.cv u)) (syn_cfv (syn_c2nd) (.cv v)))
      (syn_wiso (.cv f) (.cv r) (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv u))
        (syn_cfv (syn_c2nd) (.cv v)))
      p0006 p0010
  have p0021 :=
    @g_simpl (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))
      (syn_wiso (.cv f) (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c1st) (.cv v))
        (syn_cfv (syn_c2nd) (.cv u)) (syn_cfv (syn_c2nd) (.cv v)))
  have p0022 :=
    @g_simpr (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A))
  have p0023 :=
    @g_syl
      (syn_wa (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))
        (syn_wiso (.cv f) (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c1st) (.cv v))
          (syn_cfv (syn_c2nd) (.cv u)) (syn_cfv (syn_c2nd) (.cv v))))
      (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))
      (.classMem (.cv v) (syn_chwcn A)) p0021 p0022
  have p0024 := @g_hwcnsupp v A
  have p0025 :=
    @g_syl
      (syn_wa (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))
        (syn_wiso (.cv f) (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c1st) (.cv v))
          (syn_cfv (syn_c2nd) (.cv u)) (syn_cfv (syn_c2nd) (.cv v))))
      (.classMem (.cv v) (syn_chwcn A))
      (syn_wss (syn_cfv (syn_c1st) (.cv v))
        (syn_cxp (syn_cfv (syn_c2nd) (.cv v)) (syn_cfv (syn_c2nd) (.cv v))))
      p0023 p0024
  have p0026 :=
    @g_syl
      (syn_wa (syn_wa
          (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))
          (syn_wiso (.cv f) (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c1st) (.cv v))
            (syn_cfv (syn_c2nd) (.cv u)) (syn_cfv (syn_c2nd) (.cv v))))
        (.classEq (.cv r) (syn_cfv (syn_c1st) (.cv u))))
      (syn_wa (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))
        (syn_wiso (.cv f) (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c1st) (.cv v))
          (syn_cfv (syn_c2nd) (.cv u)) (syn_cfv (syn_c2nd) (.cv v))))
      (syn_wss (syn_cfv (syn_c1st) (.cv v))
        (syn_cxp (syn_cfv (syn_c2nd) (.cv v)) (syn_cfv (syn_c2nd) (.cv v))))
      p0004 p0025
  have p0027 :=
    @g_jca
      (syn_wa (syn_wa
          (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))
          (syn_wiso (.cv f) (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c1st) (.cv v))
            (syn_cfv (syn_c2nd) (.cv u)) (syn_cfv (syn_c2nd) (.cv v))))
        (.classEq (.cv r) (syn_cfv (syn_c1st) (.cv u))))
      (syn_wiso (.cv f) (.cv r) (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv u))
        (syn_cfv (syn_c2nd) (.cv v)))
      (syn_wss (syn_cfv (syn_c1st) (.cv v))
        (syn_cxp (syn_cfv (syn_c2nd) (.cv v)) (syn_cfv (syn_c2nd) (.cv v))))
      p0011 p0026
  have p0028 :=
    @g_isotargettransport (syn_cfv (syn_c2nd) (.cv u)) (syn_cfv (syn_c2nd) (.cv v))
      (syn_cfv (syn_c1st) (.cv v)) f r dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006
  have p0029 :=
    @g_syl
      (syn_wa (syn_wa
          (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))
          (syn_wiso (.cv f) (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c1st) (.cv v))
            (syn_cfv (syn_c2nd) (.cv u)) (syn_cfv (syn_c2nd) (.cv v))))
        (.classEq (.cv r) (syn_cfv (syn_c1st) (.cv u))))
      (syn_wa (syn_wiso (.cv f) (.cv r) (syn_cfv (syn_c1st) (.cv v))
          (syn_cfv (syn_c2nd) (.cv u)) (syn_cfv (syn_c2nd) (.cv v)))
        (syn_wss (syn_cfv (syn_c1st) (.cv v))
          (syn_cxp (syn_cfv (syn_c2nd) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)))))
      (.classEq (syn_cfv (syn_c1st) (.cv v))
        (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f))))
      p0027 p0028
  have p0030 :=
    @g_isoeq3 (syn_cfv (syn_c2nd) (.cv u)) (syn_cfv (syn_c2nd) (.cv v)) (.cv r)
      (syn_cfv (syn_c1st) (.cv v))
      (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f))) (.cv f)
  have p0031 :=
    @g_syl
      (syn_wa (syn_wa
          (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))
          (syn_wiso (.cv f) (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c1st) (.cv v))
            (syn_cfv (syn_c2nd) (.cv u)) (syn_cfv (syn_c2nd) (.cv v))))
        (.classEq (.cv r) (syn_cfv (syn_c1st) (.cv u))))
      (.classEq (syn_cfv (syn_c1st) (.cv v))
        (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f))))
      (syn_wb (syn_wiso (.cv f) (.cv r) (syn_cfv (syn_c1st) (.cv v))
          (syn_cfv (syn_c2nd) (.cv u)) (syn_cfv (syn_c2nd) (.cv v)))
        (syn_wiso (.cv f) (.cv r) (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f)))
          (syn_cfv (syn_c2nd) (.cv u)) (syn_cfv (syn_c2nd) (.cv v))))
      p0029 p0030
  have p0034 :=
    @g_isof1o (syn_cfv (syn_c2nd) (.cv u)) (syn_cfv (syn_c2nd) (.cv v))
      (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c1st) (.cv v)) (.cv f)
  have p0035 :=
    @g_syl
      (syn_wa (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))
        (syn_wiso (.cv f) (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c1st) (.cv v))
          (syn_cfv (syn_c2nd) (.cv u)) (syn_cfv (syn_c2nd) (.cv v))))
      (syn_wiso (.cv f) (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c1st) (.cv v))
        (syn_cfv (syn_c2nd) (.cv u)) (syn_cfv (syn_c2nd) (.cv v)))
      (syn_wf1o (.cv f) (syn_cfv (syn_c2nd) (.cv u)) (syn_cfv (syn_c2nd) (.cv v))) p0005
      p0034
  have p0036 := @g_f1odm (syn_cfv (syn_c2nd) (.cv u)) (syn_cfv (syn_c2nd) (.cv v)) (.cv f)
  have p0037 :=
    @g_syl
      (syn_wa (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))
        (syn_wiso (.cv f) (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c1st) (.cv v))
          (syn_cfv (syn_c2nd) (.cv u)) (syn_cfv (syn_c2nd) (.cv v))))
      (syn_wf1o (.cv f) (syn_cfv (syn_c2nd) (.cv u)) (syn_cfv (syn_c2nd) (.cv v)))
      (.classEq (syn_cdm (.cv f)) (syn_cfv (syn_c2nd) (.cv u))) p0035 p0036
  have p0038 :=
    @g_syl
      (syn_wa (syn_wa
          (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))
          (syn_wiso (.cv f) (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c1st) (.cv v))
            (syn_cfv (syn_c2nd) (.cv u)) (syn_cfv (syn_c2nd) (.cv v))))
        (.classEq (.cv r) (syn_cfv (syn_c1st) (.cv u))))
      (syn_wa (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))
        (syn_wiso (.cv f) (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c1st) (.cv v))
          (syn_cfv (syn_c2nd) (.cv u)) (syn_cfv (syn_c2nd) (.cv v))))
      (.classEq (syn_cdm (.cv f)) (syn_cfv (syn_c2nd) (.cv u))) p0004 p0037
  have p0039 :=
    @g_eqcomd
      (syn_wa (syn_wa
          (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))
          (syn_wiso (.cv f) (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c1st) (.cv v))
            (syn_cfv (syn_c2nd) (.cv u)) (syn_cfv (syn_c2nd) (.cv v))))
        (.classEq (.cv r) (syn_cfv (syn_c1st) (.cv u))))
      (syn_cdm (.cv f)) (syn_cfv (syn_c2nd) (.cv u)) p0038
  have p0040 :=
    @g_isoeq4 (syn_cfv (syn_c2nd) (.cv u)) (syn_cfv (syn_c2nd) (.cv v)) (syn_cdm (.cv f))
      (.cv r) (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f))) (.cv f)
  have p0041 :=
    @g_syl
      (syn_wa (syn_wa
          (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))
          (syn_wiso (.cv f) (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c1st) (.cv v))
            (syn_cfv (syn_c2nd) (.cv u)) (syn_cfv (syn_c2nd) (.cv v))))
        (.classEq (.cv r) (syn_cfv (syn_c1st) (.cv u))))
      (.classEq (syn_cfv (syn_c2nd) (.cv u)) (syn_cdm (.cv f)))
      (syn_wb (syn_wiso (.cv f) (.cv r) (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f)))
          (syn_cfv (syn_c2nd) (.cv u)) (syn_cfv (syn_c2nd) (.cv v)))
        (syn_wiso (.cv f) (.cv r) (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f)))
          (syn_cdm (.cv f)) (syn_cfv (syn_c2nd) (.cv v))))
      p0039 p0040
  have p0042 :=
    @g_bitrd
      (syn_wa (syn_wa
          (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))
          (syn_wiso (.cv f) (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c1st) (.cv v))
            (syn_cfv (syn_c2nd) (.cv u)) (syn_cfv (syn_c2nd) (.cv v))))
        (.classEq (.cv r) (syn_cfv (syn_c1st) (.cv u))))
      (syn_wiso (.cv f) (.cv r) (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv u))
        (syn_cfv (syn_c2nd) (.cv v)))
      (syn_wiso (.cv f) (.cv r) (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f)))
        (syn_cfv (syn_c2nd) (.cv u)) (syn_cfv (syn_c2nd) (.cv v)))
      (syn_wiso (.cv f) (.cv r) (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f)))
        (syn_cdm (.cv f)) (syn_cfv (syn_c2nd) (.cv v)))
      p0031 p0041
  have p0047 := @g_f1ofo (syn_cfv (syn_c2nd) (.cv u)) (syn_cfv (syn_c2nd) (.cv v)) (.cv f)
  have p0048 :=
    @g_syl
      (syn_wa (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))
        (syn_wiso (.cv f) (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c1st) (.cv v))
          (syn_cfv (syn_c2nd) (.cv u)) (syn_cfv (syn_c2nd) (.cv v))))
      (syn_wf1o (.cv f) (syn_cfv (syn_c2nd) (.cv u)) (syn_cfv (syn_c2nd) (.cv v)))
      (syn_wfo (.cv f) (syn_cfv (syn_c2nd) (.cv u)) (syn_cfv (syn_c2nd) (.cv v))) p0035
      p0047
  have p0049 := @g_forn (syn_cfv (syn_c2nd) (.cv u)) (syn_cfv (syn_c2nd) (.cv v)) (.cv f)
  have p0050 :=
    @g_syl
      (syn_wa (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))
        (syn_wiso (.cv f) (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c1st) (.cv v))
          (syn_cfv (syn_c2nd) (.cv u)) (syn_cfv (syn_c2nd) (.cv v))))
      (syn_wfo (.cv f) (syn_cfv (syn_c2nd) (.cv u)) (syn_cfv (syn_c2nd) (.cv v)))
      (.classEq (syn_crn (.cv f)) (syn_cfv (syn_c2nd) (.cv v))) p0048 p0049
  have p0051 :=
    @g_syl
      (syn_wa (syn_wa
          (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))
          (syn_wiso (.cv f) (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c1st) (.cv v))
            (syn_cfv (syn_c2nd) (.cv u)) (syn_cfv (syn_c2nd) (.cv v))))
        (.classEq (.cv r) (syn_cfv (syn_c1st) (.cv u))))
      (syn_wa (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))
        (syn_wiso (.cv f) (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c1st) (.cv v))
          (syn_cfv (syn_c2nd) (.cv u)) (syn_cfv (syn_c2nd) (.cv v))))
      (.classEq (syn_crn (.cv f)) (syn_cfv (syn_c2nd) (.cv v))) p0004 p0050
  have p0052 :=
    @g_eqcomd
      (syn_wa (syn_wa
          (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))
          (syn_wiso (.cv f) (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c1st) (.cv v))
            (syn_cfv (syn_c2nd) (.cv u)) (syn_cfv (syn_c2nd) (.cv v))))
        (.classEq (.cv r) (syn_cfv (syn_c1st) (.cv u))))
      (syn_crn (.cv f)) (syn_cfv (syn_c2nd) (.cv v)) p0051
  have p0053 :=
    @g_isoeq5 (syn_cdm (.cv f)) (syn_cfv (syn_c2nd) (.cv v)) (syn_crn (.cv f)) (.cv r)
      (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f))) (.cv f)
  have p0054 :=
    @g_syl
      (syn_wa (syn_wa
          (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))
          (syn_wiso (.cv f) (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c1st) (.cv v))
            (syn_cfv (syn_c2nd) (.cv u)) (syn_cfv (syn_c2nd) (.cv v))))
        (.classEq (.cv r) (syn_cfv (syn_c1st) (.cv u))))
      (.classEq (syn_cfv (syn_c2nd) (.cv v)) (syn_crn (.cv f)))
      (syn_wb (syn_wiso (.cv f) (.cv r) (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f)))
          (syn_cdm (.cv f)) (syn_cfv (syn_c2nd) (.cv v)))
        (syn_wiso (.cv f) (.cv r) (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f)))
          (syn_cdm (.cv f)) (syn_crn (.cv f))))
      p0052 p0053
  have p0055 :=
    @g_bitrd
      (syn_wa (syn_wa
          (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))
          (syn_wiso (.cv f) (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c1st) (.cv v))
            (syn_cfv (syn_c2nd) (.cv u)) (syn_cfv (syn_c2nd) (.cv v))))
        (.classEq (.cv r) (syn_cfv (syn_c1st) (.cv u))))
      (syn_wiso (.cv f) (.cv r) (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv u))
        (syn_cfv (syn_c2nd) (.cv v)))
      (syn_wiso (.cv f) (.cv r) (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f)))
        (syn_cdm (.cv f)) (syn_cfv (syn_c2nd) (.cv v)))
      (syn_wiso (.cv f) (.cv r) (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f)))
        (syn_cdm (.cv f)) (syn_crn (.cv f)))
      p0042 p0054
  have p0056 :=
    @g_biimpd
      (syn_wa (syn_wa
          (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))
          (syn_wiso (.cv f) (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c1st) (.cv v))
            (syn_cfv (syn_c2nd) (.cv u)) (syn_cfv (syn_c2nd) (.cv v))))
        (.classEq (.cv r) (syn_cfv (syn_c1st) (.cv u))))
      (syn_wiso (.cv f) (.cv r) (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv u))
        (syn_cfv (syn_c2nd) (.cv v)))
      (syn_wiso (.cv f) (.cv r) (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f)))
        (syn_cdm (.cv f)) (syn_crn (.cv f)))
      p0055
  have p0057 :=
    @g_mpd
      (syn_wa (syn_wa
          (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))
          (syn_wiso (.cv f) (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c1st) (.cv v))
            (syn_cfv (syn_c2nd) (.cv u)) (syn_cfv (syn_c2nd) (.cv v))))
        (.classEq (.cv r) (syn_cfv (syn_c1st) (.cv u))))
      (syn_wiso (.cv f) (.cv r) (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv u))
        (syn_cfv (syn_c2nd) (.cv v)))
      (syn_wiso (.cv f) (.cv r) (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f)))
        (syn_cdm (.cv f)) (syn_crn (.cv f)))
      p0011 p0056
  have p0066 :=
    @g_jca
      (syn_wa (syn_wa
          (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))
          (syn_wiso (.cv f) (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c1st) (.cv v))
            (syn_cfv (syn_c2nd) (.cv u)) (syn_cfv (syn_c2nd) (.cv v))))
        (.classEq (.cv r) (syn_cfv (syn_c1st) (.cv u))))
      (.classEq (.cv r) (syn_cfv (syn_c1st) (.cv u)))
      (.classEq (syn_cdm (.cv f)) (syn_cfv (syn_c2nd) (.cv u))) p0007 p0038
  have p0067 :=
    @g_opeq12 (.cv r) (syn_cfv (syn_c1st) (.cv u)) (syn_cdm (.cv f))
      (syn_cfv (syn_c2nd) (.cv u))
  have p0068 :=
    @g_syl
      (syn_wa (syn_wa
          (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))
          (syn_wiso (.cv f) (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c1st) (.cv v))
            (syn_cfv (syn_c2nd) (.cv u)) (syn_cfv (syn_c2nd) (.cv v))))
        (.classEq (.cv r) (syn_cfv (syn_c1st) (.cv u))))
      (syn_wa (.classEq (.cv r) (syn_cfv (syn_c1st) (.cv u)))
        (.classEq (syn_cdm (.cv f)) (syn_cfv (syn_c2nd) (.cv u))))
      (.classEq (syn_cop (.cv r) (syn_cdm (.cv f)))
        (syn_cop (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u))))
      p0066 p0067
  have p0071 :=
    @g_simpl (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A))
  have p0072 :=
    @g_syl
      (syn_wa (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))
        (syn_wiso (.cv f) (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c1st) (.cv v))
          (syn_cfv (syn_c2nd) (.cv u)) (syn_cfv (syn_c2nd) (.cv v))))
      (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))
      (.classMem (.cv u) (syn_chwcn A)) p0021 p0071
  have p0073 := @g_hwcnpair u A
  have p0074 :=
    @g_syl
      (syn_wa (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))
        (syn_wiso (.cv f) (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c1st) (.cv v))
          (syn_cfv (syn_c2nd) (.cv u)) (syn_cfv (syn_c2nd) (.cv v))))
      (.classMem (.cv u) (syn_chwcn A))
      (.classEq (.cv u) (syn_cop (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u))))
      p0072 p0073
  have p0075 :=
    @g_syl
      (syn_wa (syn_wa
          (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))
          (syn_wiso (.cv f) (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c1st) (.cv v))
            (syn_cfv (syn_c2nd) (.cv u)) (syn_cfv (syn_c2nd) (.cv v))))
        (.classEq (.cv r) (syn_cfv (syn_c1st) (.cv u))))
      (syn_wa (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))
        (syn_wiso (.cv f) (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c1st) (.cv v))
          (syn_cfv (syn_c2nd) (.cv u)) (syn_cfv (syn_c2nd) (.cv v))))
      (.classEq (.cv u) (syn_cop (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u))))
      p0004 p0074
  have p0076 :=
    @g_eqtr4d
      (syn_wa (syn_wa
          (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))
          (syn_wiso (.cv f) (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c1st) (.cv v))
            (syn_cfv (syn_c2nd) (.cv u)) (syn_cfv (syn_c2nd) (.cv v))))
        (.classEq (.cv r) (syn_cfv (syn_c1st) (.cv u))))
      (syn_cop (.cv r) (syn_cdm (.cv f)))
      (syn_cop (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u))) (.cv u) p0068
      p0075
  have p0095 :=
    @g_eqcomd
      (syn_wa (syn_wa
          (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))
          (syn_wiso (.cv f) (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c1st) (.cv v))
            (syn_cfv (syn_c2nd) (.cv u)) (syn_cfv (syn_c2nd) (.cv v))))
        (.classEq (.cv r) (syn_cfv (syn_c1st) (.cv u))))
      (syn_cfv (syn_c1st) (.cv v))
      (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f))) p0029
  have p0105 :=
    @g_jca
      (syn_wa (syn_wa
          (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))
          (syn_wiso (.cv f) (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c1st) (.cv v))
            (syn_cfv (syn_c2nd) (.cv u)) (syn_cfv (syn_c2nd) (.cv v))))
        (.classEq (.cv r) (syn_cfv (syn_c1st) (.cv u))))
      (.classEq (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f)))
        (syn_cfv (syn_c1st) (.cv v)))
      (.classEq (syn_crn (.cv f)) (syn_cfv (syn_c2nd) (.cv v))) p0095 p0051
  have p0106 :=
    @g_opeq12 (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f)))
      (syn_cfv (syn_c1st) (.cv v)) (syn_crn (.cv f)) (syn_cfv (syn_c2nd) (.cv v))
  have p0107 :=
    @g_syl
      (syn_wa (syn_wa
          (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))
          (syn_wiso (.cv f) (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c1st) (.cv v))
            (syn_cfv (syn_c2nd) (.cv u)) (syn_cfv (syn_c2nd) (.cv v))))
        (.classEq (.cv r) (syn_cfv (syn_c1st) (.cv u))))
      (syn_wa (.classEq (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f)))
          (syn_cfv (syn_c1st) (.cv v)))
        (.classEq (syn_crn (.cv f)) (syn_cfv (syn_c2nd) (.cv v))))
      (.classEq (syn_cop (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f)))
          (syn_crn (.cv f)))
        (syn_cop (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v))))
      p0105 p0106
  have p0112 := @g_hwcnpair v A
  have p0113 :=
    @g_syl
      (syn_wa (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))
        (syn_wiso (.cv f) (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c1st) (.cv v))
          (syn_cfv (syn_c2nd) (.cv u)) (syn_cfv (syn_c2nd) (.cv v))))
      (.classMem (.cv v) (syn_chwcn A))
      (.classEq (.cv v) (syn_cop (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v))))
      p0023 p0112
  have p0114 :=
    @g_syl
      (syn_wa (syn_wa
          (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))
          (syn_wiso (.cv f) (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c1st) (.cv v))
            (syn_cfv (syn_c2nd) (.cv u)) (syn_cfv (syn_c2nd) (.cv v))))
        (.classEq (.cv r) (syn_cfv (syn_c1st) (.cv u))))
      (syn_wa (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))
        (syn_wiso (.cv f) (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c1st) (.cv v))
          (syn_cfv (syn_c2nd) (.cv u)) (syn_cfv (syn_c2nd) (.cv v))))
      (.classEq (.cv v) (syn_cop (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v))))
      p0004 p0113
  have p0115 :=
    @g_eqtr4d
      (syn_wa (syn_wa
          (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))
          (syn_wiso (.cv f) (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c1st) (.cv v))
            (syn_cfv (syn_c2nd) (.cv u)) (syn_cfv (syn_c2nd) (.cv v))))
        (.classEq (.cv r) (syn_cfv (syn_c1st) (.cv u))))
      (syn_cop (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f))) (syn_crn (.cv f)))
      (syn_cop (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v))) (.cv v) p0107
      p0114
  have p0116 :=
    @g_jca
      (syn_wa (syn_wa
          (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))
          (syn_wiso (.cv f) (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c1st) (.cv v))
            (syn_cfv (syn_c2nd) (.cv u)) (syn_cfv (syn_c2nd) (.cv v))))
        (.classEq (.cv r) (syn_cfv (syn_c1st) (.cv u))))
      (.classEq (syn_cop (.cv r) (syn_cdm (.cv f))) (.cv u))
      (.classEq (syn_cop (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f)))
          (syn_crn (.cv f))) (.cv v))
      p0076 p0115
  have p0117 :=
    @g_jca
      (syn_wa (syn_wa
          (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))
          (syn_wiso (.cv f) (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c1st) (.cv v))
            (syn_cfv (syn_c2nd) (.cv u)) (syn_cfv (syn_c2nd) (.cv v))))
        (.classEq (.cv r) (syn_cfv (syn_c1st) (.cv u))))
      (syn_wiso (.cv f) (.cv r) (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f)))
        (syn_cdm (.cv f)) (syn_crn (.cv f)))
      (syn_wa (.classEq (syn_cop (.cv r) (syn_cdm (.cv f))) (.cv u)) (.classEq
          (syn_cop (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f))) (syn_crn (.cv f)))
          (.cv v)))
      p0057 p0116
  have p0118 :=
    @g_ex
      (syn_wa (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))
        (syn_wiso (.cv f) (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c1st) (.cv v))
          (syn_cfv (syn_c2nd) (.cv u)) (syn_cfv (syn_c2nd) (.cv v))))
      (.classEq (.cv r) (syn_cfv (syn_c1st) (.cv u)))
      (syn_wa (syn_wiso (.cv f) (.cv r) (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f)))
          (syn_cdm (.cv f)) (syn_crn (.cv f)))
        (syn_wa (.classEq (syn_cop (.cv r) (syn_cdm (.cv f))) (.cv u)) (.classEq
            (syn_cop (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f))) (syn_crn (.cv f)))
            (.cv v))))
      p0117
  have p0119 :=
    @g_reximdv
      (syn_wa (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))
        (syn_wiso (.cv f) (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c1st) (.cv v))
          (syn_cfv (syn_c2nd) (.cv u)) (syn_cfv (syn_c2nd) (.cv v))))
      (.classEq (.cv r) (syn_cfv (syn_c1st) (.cv u)))
      (syn_wa (syn_wiso (.cv f) (.cv r) (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f)))
          (syn_cdm (.cv f)) (syn_crn (.cv f)))
        (syn_wa (.classEq (syn_cop (.cv r) (syn_cdm (.cv f))) (.cv u)) (.classEq
            (syn_cop (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f))) (syn_crn (.cv f)))
            (.cv v))))
      r (syn_cvv) dv_cache_0007 p0118
  have p0120 :=
    @g_mpd
      (syn_wa (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))
        (syn_wiso (.cv f) (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c1st) (.cv v))
          (syn_cfv (syn_c2nd) (.cv u)) (syn_cfv (syn_c2nd) (.cv v))))
      (syn_wrex r (syn_cvv) (.classEq (.cv r) (syn_cfv (syn_c1st) (.cv u))))
      (syn_wrex r (syn_cvv) (syn_wa (syn_wiso (.cv f) (.cv r)
            (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f))) (syn_cdm (.cv f))
            (syn_crn (.cv f))) (syn_wa (.classEq (syn_cop (.cv r) (syn_cdm (.cv f))) (.cv u))
            (.classEq (syn_cop (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f)))
                (syn_crn (.cv f))) (.cv v)))))
      p0003 p0119
  exact p0120


end NFChoice.DirectNominalPrf.WPPReplay

end

/-! Certificates from `NominalWPPReplayChunk014Compact001Part039`. -/


section

namespace NFChoice.DirectNominalPrf.WPPReplay

open scoped Fol
open NFChoice.Foundation
open NFChoice.SemanticCore
open NFChoice.ReplaySupport
open NFChoice.Compiler.CompactSourceSyntax

@[expose]
noncomputable def g_hwnisogenrawi (v : Var) (u : Var) (A : Class) (f : Var) (r : Var)
    (_dv_A_f : f ∉ A.fv) (_dv_A_r : r ∉ A.fv) (_dv_f_r : f ≠ r) (_dv_f_u : f ≠ u)
    (_dv_f_v : f ≠ v) (_dv_r_u : r ≠ u) (_dv_r_v : r ≠ v) (_dv_u_v : u ≠ v) :
    Nominal.NPrf
      (.imp (syn_wa (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))
          (syn_wa (syn_wiso (.cv f) (.cv r)
              (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f))) (syn_cdm (.cv f))
              (syn_crn (.cv f))) (syn_wa (.classEq (syn_cop (.cv r) (syn_cdm (.cv f))) (.cv u))
              (.classEq (syn_cop (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f)))
                  (syn_crn (.cv f))) (.cv v)))))
        (syn_wiso (.cv f) (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c1st) (.cv v))
          (syn_cfv (syn_c2nd) (.cv u)) (syn_cfv (syn_c2nd) (.cv v)))) :=
  by
  have p0000 :=
    @g_simpr (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))
      (syn_wa (syn_wiso (.cv f) (.cv r) (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f)))
          (syn_cdm (.cv f)) (syn_crn (.cv f)))
        (syn_wa (.classEq (syn_cop (.cv r) (syn_cdm (.cv f))) (.cv u)) (.classEq
            (syn_cop (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f))) (syn_crn (.cv f)))
            (.cv v))))
  have p0001 :=
    @g_simpl
      (syn_wiso (.cv f) (.cv r) (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f)))
        (syn_cdm (.cv f)) (syn_crn (.cv f)))
      (syn_wa (.classEq (syn_cop (.cv r) (syn_cdm (.cv f))) (.cv u)) (.classEq
          (syn_cop (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f))) (syn_crn (.cv f)))
          (.cv v)))
  have p0002 :=
    @g_syl
      (syn_wa (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))
        (syn_wa (syn_wiso (.cv f) (.cv r)
            (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f))) (syn_cdm (.cv f))
            (syn_crn (.cv f))) (syn_wa (.classEq (syn_cop (.cv r) (syn_cdm (.cv f))) (.cv u))
            (.classEq (syn_cop (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f)))
                (syn_crn (.cv f))) (.cv v)))))
      (syn_wa (syn_wiso (.cv f) (.cv r) (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f)))
          (syn_cdm (.cv f)) (syn_crn (.cv f)))
        (syn_wa (.classEq (syn_cop (.cv r) (syn_cdm (.cv f))) (.cv u)) (.classEq
            (syn_cop (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f))) (syn_crn (.cv f)))
            (.cv v))))
      (syn_wiso (.cv f) (.cv r) (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f)))
        (syn_cdm (.cv f)) (syn_crn (.cv f)))
      p0000 p0001
  have p0004 :=
    @g_simpr
      (syn_wiso (.cv f) (.cv r) (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f)))
        (syn_cdm (.cv f)) (syn_crn (.cv f)))
      (syn_wa (.classEq (syn_cop (.cv r) (syn_cdm (.cv f))) (.cv u)) (.classEq
          (syn_cop (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f))) (syn_crn (.cv f)))
          (.cv v)))
  have p0005 :=
    @g_syl
      (syn_wa (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))
        (syn_wa (syn_wiso (.cv f) (.cv r)
            (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f))) (syn_cdm (.cv f))
            (syn_crn (.cv f))) (syn_wa (.classEq (syn_cop (.cv r) (syn_cdm (.cv f))) (.cv u))
            (.classEq (syn_cop (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f)))
                (syn_crn (.cv f))) (.cv v)))))
      (syn_wa (syn_wiso (.cv f) (.cv r) (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f)))
          (syn_cdm (.cv f)) (syn_crn (.cv f)))
        (syn_wa (.classEq (syn_cop (.cv r) (syn_cdm (.cv f))) (.cv u)) (.classEq
            (syn_cop (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f))) (syn_crn (.cv f)))
            (.cv v))))
      (syn_wa (.classEq (syn_cop (.cv r) (syn_cdm (.cv f))) (.cv u)) (.classEq
          (syn_cop (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f))) (syn_crn (.cv f)))
          (.cv v)))
      p0000 p0004
  have p0006 :=
    @g_simpl (.classEq (syn_cop (.cv r) (syn_cdm (.cv f))) (.cv u))
      (.classEq (syn_cop (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f)))
          (syn_crn (.cv f))) (.cv v))
  have p0007 :=
    @g_syl
      (syn_wa (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))
        (syn_wa (syn_wiso (.cv f) (.cv r)
            (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f))) (syn_cdm (.cv f))
            (syn_crn (.cv f))) (syn_wa (.classEq (syn_cop (.cv r) (syn_cdm (.cv f))) (.cv u))
            (.classEq (syn_cop (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f)))
                (syn_crn (.cv f))) (.cv v)))))
      (syn_wa (.classEq (syn_cop (.cv r) (syn_cdm (.cv f))) (.cv u)) (.classEq
          (syn_cop (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f))) (syn_crn (.cv f)))
          (.cv v)))
      (.classEq (syn_cop (.cv r) (syn_cdm (.cv f))) (.cv u)) p0005 p0006
  have p0008 :=
    @g_simpl (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))
      (syn_wa (syn_wiso (.cv f) (.cv r) (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f)))
          (syn_cdm (.cv f)) (syn_crn (.cv f)))
        (syn_wa (.classEq (syn_cop (.cv r) (syn_cdm (.cv f))) (.cv u)) (.classEq
            (syn_cop (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f))) (syn_crn (.cv f)))
            (.cv v))))
  have p0009 :=
    @g_simpl (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A))
  have p0010 :=
    @g_syl
      (syn_wa (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))
        (syn_wa (syn_wiso (.cv f) (.cv r)
            (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f))) (syn_cdm (.cv f))
            (syn_crn (.cv f))) (syn_wa (.classEq (syn_cop (.cv r) (syn_cdm (.cv f))) (.cv u))
            (.classEq (syn_cop (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f)))
                (syn_crn (.cv f))) (.cv v)))))
      (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))
      (.classMem (.cv u) (syn_chwcn A)) p0008 p0009
  have p0011 := @g_hwcnpair u A
  have p0012 :=
    @g_syl
      (syn_wa (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))
        (syn_wa (syn_wiso (.cv f) (.cv r)
            (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f))) (syn_cdm (.cv f))
            (syn_crn (.cv f))) (syn_wa (.classEq (syn_cop (.cv r) (syn_cdm (.cv f))) (.cv u))
            (.classEq (syn_cop (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f)))
                (syn_crn (.cv f))) (.cv v)))))
      (.classMem (.cv u) (syn_chwcn A))
      (.classEq (.cv u) (syn_cop (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u))))
      p0010 p0011
  have p0013 :=
    @g_eqtrd
      (syn_wa (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))
        (syn_wa (syn_wiso (.cv f) (.cv r)
            (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f))) (syn_cdm (.cv f))
            (syn_crn (.cv f))) (syn_wa (.classEq (syn_cop (.cv r) (syn_cdm (.cv f))) (.cv u))
            (.classEq (syn_cop (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f)))
                (syn_crn (.cv f))) (.cv v)))))
      (syn_cop (.cv r) (syn_cdm (.cv f))) (.cv u)
      (syn_cop (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u))) p0007 p0012
  have p0014 :=
    @g_opth (.cv r) (syn_cdm (.cv f)) (syn_cfv (syn_c1st) (.cv u))
      (syn_cfv (syn_c2nd) (.cv u))
  have p0015 :=
    @g_biimpi
      (.classEq (syn_cop (.cv r) (syn_cdm (.cv f)))
        (syn_cop (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u))))
      (syn_wa (.classEq (.cv r) (syn_cfv (syn_c1st) (.cv u)))
        (.classEq (syn_cdm (.cv f)) (syn_cfv (syn_c2nd) (.cv u))))
      p0014
  have p0016 :=
    @g_syl
      (syn_wa (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))
        (syn_wa (syn_wiso (.cv f) (.cv r)
            (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f))) (syn_cdm (.cv f))
            (syn_crn (.cv f))) (syn_wa (.classEq (syn_cop (.cv r) (syn_cdm (.cv f))) (.cv u))
            (.classEq (syn_cop (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f)))
                (syn_crn (.cv f))) (.cv v)))))
      (.classEq (syn_cop (.cv r) (syn_cdm (.cv f)))
        (syn_cop (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u))))
      (syn_wa (.classEq (.cv r) (syn_cfv (syn_c1st) (.cv u)))
        (.classEq (syn_cdm (.cv f)) (syn_cfv (syn_c2nd) (.cv u))))
      p0013 p0015
  have p0017 :=
    @g_simpl (.classEq (.cv r) (syn_cfv (syn_c1st) (.cv u)))
      (.classEq (syn_cdm (.cv f)) (syn_cfv (syn_c2nd) (.cv u)))
  have p0018 :=
    @g_syl
      (syn_wa (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))
        (syn_wa (syn_wiso (.cv f) (.cv r)
            (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f))) (syn_cdm (.cv f))
            (syn_crn (.cv f))) (syn_wa (.classEq (syn_cop (.cv r) (syn_cdm (.cv f))) (.cv u))
            (.classEq (syn_cop (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f)))
                (syn_crn (.cv f))) (.cv v)))))
      (syn_wa (.classEq (.cv r) (syn_cfv (syn_c1st) (.cv u)))
        (.classEq (syn_cdm (.cv f)) (syn_cfv (syn_c2nd) (.cv u))))
      (.classEq (.cv r) (syn_cfv (syn_c1st) (.cv u))) p0016 p0017
  have p0019 :=
    @g_isoeq2 (syn_cdm (.cv f)) (syn_crn (.cv f)) (.cv r)
      (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f)))
      (syn_cfv (syn_c1st) (.cv u)) (.cv f)
  have p0020 :=
    @g_syl
      (syn_wa (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))
        (syn_wa (syn_wiso (.cv f) (.cv r)
            (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f))) (syn_cdm (.cv f))
            (syn_crn (.cv f))) (syn_wa (.classEq (syn_cop (.cv r) (syn_cdm (.cv f))) (.cv u))
            (.classEq (syn_cop (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f)))
                (syn_crn (.cv f))) (.cv v)))))
      (.classEq (.cv r) (syn_cfv (syn_c1st) (.cv u)))
      (syn_wb (syn_wiso (.cv f) (.cv r) (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f)))
          (syn_cdm (.cv f)) (syn_crn (.cv f))) (syn_wiso (.cv f) (syn_cfv (syn_c1st) (.cv u))
          (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f))) (syn_cdm (.cv f))
          (syn_crn (.cv f))))
      p0018 p0019
  have p0024 :=
    @g_simpr (.classEq (syn_cop (.cv r) (syn_cdm (.cv f))) (.cv u))
      (.classEq (syn_cop (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f)))
          (syn_crn (.cv f))) (.cv v))
  have p0025 :=
    @g_syl
      (syn_wa (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))
        (syn_wa (syn_wiso (.cv f) (.cv r)
            (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f))) (syn_cdm (.cv f))
            (syn_crn (.cv f))) (syn_wa (.classEq (syn_cop (.cv r) (syn_cdm (.cv f))) (.cv u))
            (.classEq (syn_cop (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f)))
                (syn_crn (.cv f))) (.cv v)))))
      (syn_wa (.classEq (syn_cop (.cv r) (syn_cdm (.cv f))) (.cv u)) (.classEq
          (syn_cop (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f))) (syn_crn (.cv f)))
          (.cv v)))
      (.classEq (syn_cop (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f)))
          (syn_crn (.cv f))) (.cv v))
      p0005 p0024
  have p0027 :=
    @g_simpr (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A))
  have p0028 :=
    @g_syl
      (syn_wa (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))
        (syn_wa (syn_wiso (.cv f) (.cv r)
            (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f))) (syn_cdm (.cv f))
            (syn_crn (.cv f))) (syn_wa (.classEq (syn_cop (.cv r) (syn_cdm (.cv f))) (.cv u))
            (.classEq (syn_cop (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f)))
                (syn_crn (.cv f))) (.cv v)))))
      (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))
      (.classMem (.cv v) (syn_chwcn A)) p0008 p0027
  have p0029 := @g_hwcnpair v A
  have p0030 :=
    @g_syl
      (syn_wa (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))
        (syn_wa (syn_wiso (.cv f) (.cv r)
            (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f))) (syn_cdm (.cv f))
            (syn_crn (.cv f))) (syn_wa (.classEq (syn_cop (.cv r) (syn_cdm (.cv f))) (.cv u))
            (.classEq (syn_cop (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f)))
                (syn_crn (.cv f))) (.cv v)))))
      (.classMem (.cv v) (syn_chwcn A))
      (.classEq (.cv v) (syn_cop (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v))))
      p0028 p0029
  have p0031 :=
    @g_eqtrd
      (syn_wa (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))
        (syn_wa (syn_wiso (.cv f) (.cv r)
            (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f))) (syn_cdm (.cv f))
            (syn_crn (.cv f))) (syn_wa (.classEq (syn_cop (.cv r) (syn_cdm (.cv f))) (.cv u))
            (.classEq (syn_cop (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f)))
                (syn_crn (.cv f))) (.cv v)))))
      (syn_cop (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f))) (syn_crn (.cv f)))
      (.cv v) (syn_cop (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v))) p0025
      p0030
  have p0032 :=
    @g_opth (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f))) (syn_crn (.cv f))
      (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v))
  have p0033 :=
    @g_biimpi
      (.classEq (syn_cop (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f)))
          (syn_crn (.cv f)))
        (syn_cop (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v))))
      (syn_wa (.classEq (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f)))
          (syn_cfv (syn_c1st) (.cv v)))
        (.classEq (syn_crn (.cv f)) (syn_cfv (syn_c2nd) (.cv v))))
      p0032
  have p0034 :=
    @g_syl
      (syn_wa (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))
        (syn_wa (syn_wiso (.cv f) (.cv r)
            (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f))) (syn_cdm (.cv f))
            (syn_crn (.cv f))) (syn_wa (.classEq (syn_cop (.cv r) (syn_cdm (.cv f))) (.cv u))
            (.classEq (syn_cop (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f)))
                (syn_crn (.cv f))) (.cv v)))))
      (.classEq (syn_cop (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f)))
          (syn_crn (.cv f)))
        (syn_cop (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v))))
      (syn_wa (.classEq (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f)))
          (syn_cfv (syn_c1st) (.cv v)))
        (.classEq (syn_crn (.cv f)) (syn_cfv (syn_c2nd) (.cv v))))
      p0031 p0033
  have p0035 :=
    @g_simpl
      (.classEq (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f)))
        (syn_cfv (syn_c1st) (.cv v)))
      (.classEq (syn_crn (.cv f)) (syn_cfv (syn_c2nd) (.cv v)))
  have p0036 :=
    @g_syl
      (syn_wa (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))
        (syn_wa (syn_wiso (.cv f) (.cv r)
            (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f))) (syn_cdm (.cv f))
            (syn_crn (.cv f))) (syn_wa (.classEq (syn_cop (.cv r) (syn_cdm (.cv f))) (.cv u))
            (.classEq (syn_cop (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f)))
                (syn_crn (.cv f))) (.cv v)))))
      (syn_wa (.classEq (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f)))
          (syn_cfv (syn_c1st) (.cv v)))
        (.classEq (syn_crn (.cv f)) (syn_cfv (syn_c2nd) (.cv v))))
      (.classEq (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f)))
        (syn_cfv (syn_c1st) (.cv v)))
      p0034 p0035
  have p0037 :=
    @g_isoeq3 (syn_cdm (.cv f)) (syn_crn (.cv f)) (syn_cfv (syn_c1st) (.cv u))
      (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f)))
      (syn_cfv (syn_c1st) (.cv v)) (.cv f)
  have p0038 :=
    @g_syl
      (syn_wa (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))
        (syn_wa (syn_wiso (.cv f) (.cv r)
            (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f))) (syn_cdm (.cv f))
            (syn_crn (.cv f))) (syn_wa (.classEq (syn_cop (.cv r) (syn_cdm (.cv f))) (.cv u))
            (.classEq (syn_cop (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f)))
                (syn_crn (.cv f))) (.cv v)))))
      (.classEq (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f)))
        (syn_cfv (syn_c1st) (.cv v)))
      (syn_wb (syn_wiso (.cv f) (syn_cfv (syn_c1st) (.cv u))
          (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f))) (syn_cdm (.cv f))
          (syn_crn (.cv f)))
        (syn_wiso (.cv f) (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c1st) (.cv v))
          (syn_cdm (.cv f)) (syn_crn (.cv f))))
      p0036 p0037
  have p0039 :=
    @g_bitrd
      (syn_wa (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))
        (syn_wa (syn_wiso (.cv f) (.cv r)
            (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f))) (syn_cdm (.cv f))
            (syn_crn (.cv f))) (syn_wa (.classEq (syn_cop (.cv r) (syn_cdm (.cv f))) (.cv u))
            (.classEq (syn_cop (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f)))
                (syn_crn (.cv f))) (.cv v)))))
      (syn_wiso (.cv f) (.cv r) (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f)))
        (syn_cdm (.cv f)) (syn_crn (.cv f)))
      (syn_wiso (.cv f) (syn_cfv (syn_c1st) (.cv u))
        (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f))) (syn_cdm (.cv f))
        (syn_crn (.cv f)))
      (syn_wiso (.cv f) (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c1st) (.cv v))
        (syn_cdm (.cv f)) (syn_crn (.cv f)))
      p0020 p0038
  have p0054 :=
    @g_simpr (.classEq (.cv r) (syn_cfv (syn_c1st) (.cv u)))
      (.classEq (syn_cdm (.cv f)) (syn_cfv (syn_c2nd) (.cv u)))
  have p0055 :=
    @g_syl
      (syn_wa (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))
        (syn_wa (syn_wiso (.cv f) (.cv r)
            (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f))) (syn_cdm (.cv f))
            (syn_crn (.cv f))) (syn_wa (.classEq (syn_cop (.cv r) (syn_cdm (.cv f))) (.cv u))
            (.classEq (syn_cop (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f)))
                (syn_crn (.cv f))) (.cv v)))))
      (syn_wa (.classEq (.cv r) (syn_cfv (syn_c1st) (.cv u)))
        (.classEq (syn_cdm (.cv f)) (syn_cfv (syn_c2nd) (.cv u))))
      (.classEq (syn_cdm (.cv f)) (syn_cfv (syn_c2nd) (.cv u))) p0016 p0054
  have p0056 :=
    @g_isoeq4 (syn_cdm (.cv f)) (syn_crn (.cv f)) (syn_cfv (syn_c2nd) (.cv u))
      (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c1st) (.cv v)) (.cv f)
  have p0057 :=
    @g_syl
      (syn_wa (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))
        (syn_wa (syn_wiso (.cv f) (.cv r)
            (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f))) (syn_cdm (.cv f))
            (syn_crn (.cv f))) (syn_wa (.classEq (syn_cop (.cv r) (syn_cdm (.cv f))) (.cv u))
            (.classEq (syn_cop (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f)))
                (syn_crn (.cv f))) (.cv v)))))
      (.classEq (syn_cdm (.cv f)) (syn_cfv (syn_c2nd) (.cv u)))
      (syn_wb (syn_wiso (.cv f) (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c1st) (.cv v))
          (syn_cdm (.cv f)) (syn_crn (.cv f)))
        (syn_wiso (.cv f) (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c1st) (.cv v))
          (syn_cfv (syn_c2nd) (.cv u)) (syn_crn (.cv f))))
      p0055 p0056
  have p0058 :=
    @g_bitrd
      (syn_wa (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))
        (syn_wa (syn_wiso (.cv f) (.cv r)
            (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f))) (syn_cdm (.cv f))
            (syn_crn (.cv f))) (syn_wa (.classEq (syn_cop (.cv r) (syn_cdm (.cv f))) (.cv u))
            (.classEq (syn_cop (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f)))
                (syn_crn (.cv f))) (.cv v)))))
      (syn_wiso (.cv f) (.cv r) (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f)))
        (syn_cdm (.cv f)) (syn_crn (.cv f)))
      (syn_wiso (.cv f) (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c1st) (.cv v))
        (syn_cdm (.cv f)) (syn_crn (.cv f)))
      (syn_wiso (.cv f) (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c1st) (.cv v))
        (syn_cfv (syn_c2nd) (.cv u)) (syn_crn (.cv f)))
      p0039 p0057
  have p0073 :=
    @g_simpr
      (.classEq (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f)))
        (syn_cfv (syn_c1st) (.cv v)))
      (.classEq (syn_crn (.cv f)) (syn_cfv (syn_c2nd) (.cv v)))
  have p0074 :=
    @g_syl
      (syn_wa (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))
        (syn_wa (syn_wiso (.cv f) (.cv r)
            (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f))) (syn_cdm (.cv f))
            (syn_crn (.cv f))) (syn_wa (.classEq (syn_cop (.cv r) (syn_cdm (.cv f))) (.cv u))
            (.classEq (syn_cop (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f)))
                (syn_crn (.cv f))) (.cv v)))))
      (syn_wa (.classEq (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f)))
          (syn_cfv (syn_c1st) (.cv v)))
        (.classEq (syn_crn (.cv f)) (syn_cfv (syn_c2nd) (.cv v))))
      (.classEq (syn_crn (.cv f)) (syn_cfv (syn_c2nd) (.cv v))) p0034 p0073
  have p0075 :=
    @g_isoeq5 (syn_cfv (syn_c2nd) (.cv u)) (syn_crn (.cv f)) (syn_cfv (syn_c2nd) (.cv v))
      (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c1st) (.cv v)) (.cv f)
  have p0076 :=
    @g_syl
      (syn_wa (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))
        (syn_wa (syn_wiso (.cv f) (.cv r)
            (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f))) (syn_cdm (.cv f))
            (syn_crn (.cv f))) (syn_wa (.classEq (syn_cop (.cv r) (syn_cdm (.cv f))) (.cv u))
            (.classEq (syn_cop (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f)))
                (syn_crn (.cv f))) (.cv v)))))
      (.classEq (syn_crn (.cv f)) (syn_cfv (syn_c2nd) (.cv v)))
      (syn_wb (syn_wiso (.cv f) (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c1st) (.cv v))
          (syn_cfv (syn_c2nd) (.cv u)) (syn_crn (.cv f)))
        (syn_wiso (.cv f) (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c1st) (.cv v))
          (syn_cfv (syn_c2nd) (.cv u)) (syn_cfv (syn_c2nd) (.cv v))))
      p0074 p0075
  have p0077 :=
    @g_bitrd
      (syn_wa (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))
        (syn_wa (syn_wiso (.cv f) (.cv r)
            (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f))) (syn_cdm (.cv f))
            (syn_crn (.cv f))) (syn_wa (.classEq (syn_cop (.cv r) (syn_cdm (.cv f))) (.cv u))
            (.classEq (syn_cop (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f)))
                (syn_crn (.cv f))) (.cv v)))))
      (syn_wiso (.cv f) (.cv r) (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f)))
        (syn_cdm (.cv f)) (syn_crn (.cv f)))
      (syn_wiso (.cv f) (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c1st) (.cv v))
        (syn_cfv (syn_c2nd) (.cv u)) (syn_crn (.cv f)))
      (syn_wiso (.cv f) (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c1st) (.cv v))
        (syn_cfv (syn_c2nd) (.cv u)) (syn_cfv (syn_c2nd) (.cv v)))
      p0058 p0076
  have p0078 :=
    @g_biimpd
      (syn_wa (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))
        (syn_wa (syn_wiso (.cv f) (.cv r)
            (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f))) (syn_cdm (.cv f))
            (syn_crn (.cv f))) (syn_wa (.classEq (syn_cop (.cv r) (syn_cdm (.cv f))) (.cv u))
            (.classEq (syn_cop (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f)))
                (syn_crn (.cv f))) (.cv v)))))
      (syn_wiso (.cv f) (.cv r) (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f)))
        (syn_cdm (.cv f)) (syn_crn (.cv f)))
      (syn_wiso (.cv f) (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c1st) (.cv v))
        (syn_cfv (syn_c2nd) (.cv u)) (syn_cfv (syn_c2nd) (.cv v)))
      p0077
  have p0079 :=
    @g_mpd
      (syn_wa (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))
        (syn_wa (syn_wiso (.cv f) (.cv r)
            (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f))) (syn_cdm (.cv f))
            (syn_crn (.cv f))) (syn_wa (.classEq (syn_cop (.cv r) (syn_cdm (.cv f))) (.cv u))
            (.classEq (syn_cop (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f)))
                (syn_crn (.cv f))) (.cv v)))))
      (syn_wiso (.cv f) (.cv r) (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f)))
        (syn_cdm (.cv f)) (syn_crn (.cv f)))
      (syn_wiso (.cv f) (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c1st) (.cv v))
        (syn_cfv (syn_c2nd) (.cv u)) (syn_cfv (syn_c2nd) (.cv v)))
      p0002 p0078
  exact p0079

@[expose]
noncomputable def g_hwnisowitnessb (v : Var) (u : Var) (A : Class) (f : Var) (r : Var)
    (dv_A_f : f ∉ A.fv) (dv_A_r : r ∉ A.fv) (dv_f_r : f ≠ r) (dv_f_u : f ≠ u)
    (dv_f_v : f ≠ v) (dv_r_u : r ≠ u) (dv_r_v : r ≠ v) (dv_u_v : u ≠ v) :
    Nominal.NPrf
      (.imp (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A))) (syn_wb
          (syn_wex f (syn_wrex r (syn_cvv) (syn_wa (syn_wiso (.cv f) (.cv r)
                  (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f)))
                  (syn_cdm (.cv f)) (syn_crn (.cv f)))
                (syn_wa (.classEq (syn_cop (.cv r) (syn_cdm (.cv f))) (.cv u)) (.classEq
                    (syn_cop (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f)))
                      (syn_crn (.cv f))) (.cv v)))))) (syn_wex f
            (syn_wiso (.cv f) (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c1st) (.cv v))
              (syn_cfv (syn_c2nd) (.cv u)) (syn_cfv (syn_c2nd) (.cv v)))))) :=
  by
  have dv_cache_0001 : f ∉ (A).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : f ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_A_f, not_false_eq_true])
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
  have dv_cache_0003 : f ≠ r :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact (show f ≠ r from (by exact dv_f_r))
  have dv_cache_0004 : f ≠ u :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact (show f ≠ u from (by exact dv_f_u))
  have dv_cache_0005 : f ≠ v :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact (show f ≠ v from (by exact dv_f_v))
  have dv_cache_0006 : r ≠ u :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact (show r ≠ u from (by exact dv_r_u))
  have dv_cache_0007 : r ≠ v :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006
    exact (show r ≠ v from (by exact dv_r_v))
  have dv_cache_0008 : u ≠ v :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007
    exact (show u ≠ v from (by exact dv_u_v))
  have dv_cache_0009 :
    r ∉
      ((syn_wiso (.cv f) (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c1st) (.cv v))
          (syn_cfv (syn_c2nd) (.cv u)) (syn_cfv (syn_c2nd) (.cv v)))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008
    exact
      (by
        have compact_fv_not_mem_empty : r ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_wiso,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1st,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c2nd, Finset.mem_union,
          Finset.mem_singleton, dv_r_u, dv_r_v, (Ne.symm dv_f_r),
          compact_fv_not_mem_empty, or_false, not_false_eq_true])
  have dv_cache_0010 :
    r ∉
      ((syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009
    exact
      (by
        have compact_fv_not_mem_empty : r ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwcn, Finset.mem_union,
          Finset.mem_singleton, dv_r_u, dv_A_r, dv_r_v, or_false, not_false_eq_true])
  have dv_cache_0011 :
    f ∉
      ((syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010
    exact
      (by
        have compact_fv_not_mem_empty : f ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwcn, Finset.mem_union,
          Finset.mem_singleton, dv_f_u, dv_A_f, dv_f_v, or_false, not_false_eq_true])
  have p0000 :=
    @g_hwnisogenrawi v u A f r dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
      dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008
  have p0001 :=
    @g_ex (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))
      (syn_wa (syn_wiso (.cv f) (.cv r) (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f)))
          (syn_cdm (.cv f)) (syn_crn (.cv f)))
        (syn_wa (.classEq (syn_cop (.cv r) (syn_cdm (.cv f))) (.cv u)) (.classEq
            (syn_cop (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f))) (syn_crn (.cv f)))
            (.cv v))))
      (syn_wiso (.cv f) (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c1st) (.cv v))
        (syn_cfv (syn_c2nd) (.cv u)) (syn_cfv (syn_c2nd) (.cv v)))
      p0000
  have p0002 :=
    @g_rexlimdvw
      (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))
      (syn_wa (syn_wiso (.cv f) (.cv r) (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f)))
          (syn_cdm (.cv f)) (syn_crn (.cv f)))
        (syn_wa (.classEq (syn_cop (.cv r) (syn_cdm (.cv f))) (.cv u)) (.classEq
            (syn_cop (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f))) (syn_crn (.cv f)))
            (.cv v))))
      (syn_wiso (.cv f) (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c1st) (.cv v))
        (syn_cfv (syn_c2nd) (.cv u)) (syn_cfv (syn_c2nd) (.cv v)))
      r (syn_cvv) dv_cache_0009 dv_cache_0010 p0001
  have p0003 :=
    @g_hwnisorawgeni v u A f r dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
      dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008
  have p0004 :=
    @g_ex (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))
      (syn_wiso (.cv f) (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c1st) (.cv v))
        (syn_cfv (syn_c2nd) (.cv u)) (syn_cfv (syn_c2nd) (.cv v)))
      (syn_wrex r (syn_cvv) (syn_wa (syn_wiso (.cv f) (.cv r)
            (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f))) (syn_cdm (.cv f))
            (syn_crn (.cv f))) (syn_wa (.classEq (syn_cop (.cv r) (syn_cdm (.cv f))) (.cv u))
            (.classEq (syn_cop (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f)))
                (syn_crn (.cv f))) (.cv v)))))
      p0003
  have p0005 :=
    @g_impbid (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))
      (syn_wrex r (syn_cvv) (syn_wa (syn_wiso (.cv f) (.cv r)
            (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f))) (syn_cdm (.cv f))
            (syn_crn (.cv f))) (syn_wa (.classEq (syn_cop (.cv r) (syn_cdm (.cv f))) (.cv u))
            (.classEq (syn_cop (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f)))
                (syn_crn (.cv f))) (.cv v)))))
      (syn_wiso (.cv f) (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c1st) (.cv v))
        (syn_cfv (syn_c2nd) (.cv u)) (syn_cfv (syn_c2nd) (.cv v)))
      p0002 p0004
  have p0006 :=
    @g_exbidv (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))
      (syn_wrex r (syn_cvv) (syn_wa (syn_wiso (.cv f) (.cv r)
            (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f))) (syn_cdm (.cv f))
            (syn_crn (.cv f))) (syn_wa (.classEq (syn_cop (.cv r) (syn_cdm (.cv f))) (.cv u))
            (.classEq (syn_cop (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f)))
                (syn_crn (.cv f))) (.cv v)))))
      (syn_wiso (.cv f) (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c1st) (.cv v))
        (syn_cfv (syn_c2nd) (.cv u)) (syn_cfv (syn_c2nd) (.cv v)))
      f dv_cache_0011 p0005
  exact p0006

@[expose]
noncomputable def g_hwnisohwisob (v : Var) (u : Var) (A : Class) (dv_u_v : u ≠ v) :
    Nominal.NPrf
      (syn_wb (syn_wbr (.cv u) (syn_chwniso A) (.cv v)) (syn_wa
          (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))
          (syn_wbr (.cv u) (syn_chwiso A) (.cv v)))) :=
  by
  let proofSupport : Finset Var := ({ v } : Finset Var) ∪ ({ u } : Finset Var) ∪ A.fv
  let f : Var := freshVar proofSupport 0
  let r : Var := freshVar proofSupport 1
  have fresh_f : f ∉ proofSupport :=
    by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_f_ne_v : f ≠ v := by
    intro h
    exact
      fresh_f
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_singleton.mpr h)))
  have fresh_f_ne_u : f ≠ u := by
    intro h
    exact
      fresh_f
        (Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_singleton.mpr h)))
  have fresh_f_not_A : f ∉ A.fv := by
    intro h
    exact fresh_f (Finset.mem_union_right _ (h))
  have fresh_r : r ∉ proofSupport :=
    by
    change freshVar proofSupport 1 ∉ proofSupport
    exact freshVar_not_mem proofSupport 1
  have fresh_r_ne_v : r ≠ v := by
    intro h
    exact
      fresh_r
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_singleton.mpr h)))
  have fresh_r_ne_u : r ≠ u := by
    intro h
    exact
      fresh_r
        (Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_singleton.mpr h)))
  have fresh_r_not_A : r ∉ A.fv := by
    intro h
    exact fresh_r (Finset.mem_union_right _ (h))
  have fresh_f_ne_r : f ≠ r :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have dv_cache_0001 : f ∉ (A).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : f ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_f_not_A, not_false_eq_true])
  have dv_cache_0002 : r ∉ (A).fv :=
    by
    clear dv_cache_0001
    exact
      (by
        have compact_fv_not_mem_empty : r ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_r_not_A, not_false_eq_true])
  have dv_cache_0003 : f ≠ r :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact (show f ≠ r from (by exact fresh_f_ne_r))
  have dv_cache_0004 : f ≠ u :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact (show f ≠ u from (by exact fresh_f_ne_u))
  have dv_cache_0005 : f ≠ v :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact (show f ≠ v from (by exact fresh_f_ne_v))
  have dv_cache_0006 : r ≠ u :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact (show r ≠ u from (by exact fresh_r_ne_u))
  have dv_cache_0007 : r ≠ v :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006
    exact (show r ≠ v from (by exact fresh_r_ne_v))
  have dv_cache_0008 : u ≠ v :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007
    exact (show u ≠ v from (by exact dv_u_v))
  have p0000 :=
    @g_elhwnisogeniso v u A f r dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
      dv_cache_0005 dv_cache_0006 dv_cache_0007
  have p0001 :=
    @g_hwnisowitnessb v u A f r dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
      dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008
  have p0002 :=
    @g_pm5_32i
      (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))
      (syn_wex f (syn_wrex r (syn_cvv) (syn_wa (syn_wiso (.cv f) (.cv r)
              (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f))) (syn_cdm (.cv f))
              (syn_crn (.cv f))) (syn_wa (.classEq (syn_cop (.cv r) (syn_cdm (.cv f))) (.cv u))
              (.classEq (syn_cop (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f)))
                  (syn_crn (.cv f))) (.cv v))))))
      (syn_wex f (syn_wiso (.cv f) (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c1st) (.cv v))
          (syn_cfv (syn_c2nd) (.cv u)) (syn_cfv (syn_c2nd) (.cv v))))
      p0001
  have p0003 :=
    @g_bitri (syn_wbr (.cv u) (syn_chwniso A) (.cv v))
      (syn_wa (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))
        (syn_wex f (syn_wrex r (syn_cvv) (syn_wa (syn_wiso (.cv f) (.cv r)
                (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f))) (syn_cdm (.cv f))
                (syn_crn (.cv f)))
              (syn_wa (.classEq (syn_cop (.cv r) (syn_cdm (.cv f))) (.cv u)) (.classEq
                  (syn_cop (syn_ccom (syn_ccom (.cv f) (.cv r)) (syn_ccnv (.cv f)))
                    (syn_crn (.cv f))) (.cv v)))))))
      (syn_wa (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))
        (syn_wex f (syn_wiso (.cv f) (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c1st) (.cv v))
            (syn_cfv (syn_c2nd) (.cv u)) (syn_cfv (syn_c2nd) (.cv v)))))
      p0000 p0002
  have p0004 :=
    @g_simpl (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A))
  have p0005 := @g_hwcnraw u A
  have p0006 :=
    @g_syl (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))
      (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv u) (syn_chwcodes A)) p0004 p0005
  have p0007 :=
    @g_simpr (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A))
  have p0008 := @g_hwcnraw v A
  have p0009 :=
    @g_syl (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))
      (.classMem (.cv v) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcodes A)) p0007 p0008
  have p0010 :=
    @g_jca (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))
      (.classMem (.cv u) (syn_chwcodes A)) (.classMem (.cv v) (syn_chwcodes A)) p0006
      p0009
  have p0011 :=
    @g_biantrurd
      (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))
      (syn_wa (.classMem (.cv u) (syn_chwcodes A)) (.classMem (.cv v) (syn_chwcodes A)))
      (syn_wex f (syn_wiso (.cv f) (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c1st) (.cv v))
          (syn_cfv (syn_c2nd) (.cv u)) (syn_cfv (syn_c2nd) (.cv v))))
      p0010
  have p0012 := @g_brhwisoany v u A f dv_cache_0001 dv_cache_0004 dv_cache_0005
  have p0013 :=
    @g_bicomi (syn_wbr (.cv u) (syn_chwiso A) (.cv v))
      (syn_wa (syn_wa (.classMem (.cv u) (syn_chwcodes A)) (.classMem (.cv v) (syn_chwcodes A)))
        (syn_wex f (syn_wiso (.cv f) (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c1st) (.cv v))
            (syn_cfv (syn_c2nd) (.cv u)) (syn_cfv (syn_c2nd) (.cv v)))))
      p0012
  have p0014 :=
    @g_a1i
      (syn_wb (syn_wa (syn_wa (.classMem (.cv u) (syn_chwcodes A))
            (.classMem (.cv v) (syn_chwcodes A))) (syn_wex f
            (syn_wiso (.cv f) (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c1st) (.cv v))
              (syn_cfv (syn_c2nd) (.cv u)) (syn_cfv (syn_c2nd) (.cv v)))))
        (syn_wbr (.cv u) (syn_chwiso A) (.cv v)))
      (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A))) p0013
  have p0015 :=
    @g_bitrd (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))
      (syn_wex f (syn_wiso (.cv f) (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c1st) (.cv v))
          (syn_cfv (syn_c2nd) (.cv u)) (syn_cfv (syn_c2nd) (.cv v))))
      (syn_wa (syn_wa (.classMem (.cv u) (syn_chwcodes A)) (.classMem (.cv v) (syn_chwcodes A)))
        (syn_wex f (syn_wiso (.cv f) (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c1st) (.cv v))
            (syn_cfv (syn_c2nd) (.cv u)) (syn_cfv (syn_c2nd) (.cv v)))))
      (syn_wbr (.cv u) (syn_chwiso A) (.cv v)) p0011 p0014
  have p0016 :=
    @g_pm5_32i
      (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))
      (syn_wex f (syn_wiso (.cv f) (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c1st) (.cv v))
          (syn_cfv (syn_c2nd) (.cv u)) (syn_cfv (syn_c2nd) (.cv v))))
      (syn_wbr (.cv u) (syn_chwiso A) (.cv v)) p0015
  have p0017 :=
    @g_bitri (syn_wbr (.cv u) (syn_chwniso A) (.cv v))
      (syn_wa (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))
        (syn_wex f (syn_wiso (.cv f) (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c1st) (.cv v))
            (syn_cfv (syn_c2nd) (.cv u)) (syn_cfv (syn_c2nd) (.cv v)))))
      (syn_wa (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))
        (syn_wbr (.cv u) (syn_chwiso A) (.cv v)))
      p0003 p0016
  exact p0017

@[expose]
noncomputable def g_hwcnexg (A : Class) :
    Nominal.NPrf (.imp (.classMem A (syn_cvv)) (.classMem (syn_chwcn A) (syn_cvv))) :=
  by
  have p0000 := (Nominal.classEqRefl (syn_chwcn A))
  have p0001 := @g_hwcodesexg A (syn_cvv)
  have p0002 := @g_hwrelsex
  have p0003 := @g_a1i (.classMem (syn_chwrels) (syn_cvv)) (.classMem A (syn_cvv)) p0002
  have p0004 :=
    @g_jca (.classMem A (syn_cvv)) (.classMem (syn_chwcodes A) (syn_cvv))
      (.classMem (syn_chwrels) (syn_cvv)) p0001 p0003
  have p0005 := @g_inexg (syn_chwcodes A) (syn_chwrels) (syn_cvv) (syn_cvv)
  have p0006 :=
    @g_syl (.classMem A (syn_cvv))
      (syn_wa (.classMem (syn_chwcodes A) (syn_cvv)) (.classMem (syn_chwrels) (syn_cvv)))
      (.classMem (syn_cin (syn_chwcodes A) (syn_chwrels)) (syn_cvv)) p0004 p0005
  have p0007 :=
    @g_syl5eqel (.classMem A (syn_cvv)) (syn_chwcn A)
      (syn_cin (syn_chwcodes A) (syn_chwrels)) (syn_cvv) p0000 p0006
  exact p0007

@[expose]
noncomputable def g_hwnisoexg (A : Class) :
    Nominal.NPrf (.imp (.classMem A (syn_cvv)) (.classMem (syn_chwniso A) (syn_cvv))) :=
  by
  have p0000 := (Nominal.classEqRefl (syn_chwniso A))
  have p0001 := @g_hwgenex
  have p0002 := @g_hwbijex
  have p0003 := @g_vvex
  have p0004 := @g_xpex (syn_chwbij) (syn_cvv) p0002 p0003
  have p0005 := @g_imaex (syn_chwgen) (syn_cxp (syn_chwbij) (syn_cvv)) p0001 p0004
  have p0006 :=
    @g_a1i (.classMem (syn_cima (syn_chwgen) (syn_cxp (syn_chwbij) (syn_cvv))) (syn_cvv))
      (.classMem A (syn_cvv)) p0005
  have p0007 := (Nominal.classEqRefl (syn_chwcn A))
  have p0008 := @g_hwcodesexg A (syn_cvv)
  have p0009 := @g_hwrelsex
  have p0010 := @g_a1i (.classMem (syn_chwrels) (syn_cvv)) (.classMem A (syn_cvv)) p0009
  have p0011 :=
    @g_jca (.classMem A (syn_cvv)) (.classMem (syn_chwcodes A) (syn_cvv))
      (.classMem (syn_chwrels) (syn_cvv)) p0008 p0010
  have p0012 := @g_inexg (syn_chwcodes A) (syn_chwrels) (syn_cvv) (syn_cvv)
  have p0013 :=
    @g_syl (.classMem A (syn_cvv))
      (syn_wa (.classMem (syn_chwcodes A) (syn_cvv)) (.classMem (syn_chwrels) (syn_cvv)))
      (.classMem (syn_cin (syn_chwcodes A) (syn_chwrels)) (syn_cvv)) p0011 p0012
  have p0014 :=
    @g_syl5eqel (.classMem A (syn_cvv)) (syn_chwcn A)
      (syn_cin (syn_chwcodes A) (syn_chwrels)) (syn_cvv) p0007 p0013
  have p0023 :=
    @g_jca (.classMem A (syn_cvv)) (.classMem (syn_chwcn A) (syn_cvv))
      (.classMem (syn_chwcn A) (syn_cvv)) p0014 p0014
  have p0024 := @g_xpexg (syn_chwcn A) (syn_chwcn A) (syn_cvv) (syn_cvv)
  have p0025 :=
    @g_syl (.classMem A (syn_cvv))
      (syn_wa (.classMem (syn_chwcn A) (syn_cvv)) (.classMem (syn_chwcn A) (syn_cvv)))
      (.classMem (syn_cxp (syn_chwcn A) (syn_chwcn A)) (syn_cvv)) p0023 p0024
  have p0026 :=
    @g_jca (.classMem A (syn_cvv))
      (.classMem (syn_cima (syn_chwgen) (syn_cxp (syn_chwbij) (syn_cvv))) (syn_cvv))
      (.classMem (syn_cxp (syn_chwcn A) (syn_chwcn A)) (syn_cvv)) p0006 p0025
  have p0027 :=
    @g_inexg (syn_cima (syn_chwgen) (syn_cxp (syn_chwbij) (syn_cvv)))
      (syn_cxp (syn_chwcn A) (syn_chwcn A)) (syn_cvv) (syn_cvv)
  have p0028 :=
    @g_syl (.classMem A (syn_cvv))
      (syn_wa (.classMem (syn_cima (syn_chwgen) (syn_cxp (syn_chwbij) (syn_cvv))) (syn_cvv))
        (.classMem (syn_cxp (syn_chwcn A) (syn_chwcn A)) (syn_cvv)))
      (.classMem (syn_cin (syn_cima (syn_chwgen) (syn_cxp (syn_chwbij) (syn_cvv)))
          (syn_cxp (syn_chwcn A) (syn_chwcn A))) (syn_cvv))
      p0026 p0027
  have p0029 :=
    @g_syl5eqel (.classMem A (syn_cvv)) (syn_chwniso A)
      (syn_cin (syn_cima (syn_chwgen) (syn_cxp (syn_chwbij) (syn_cvv)))
        (syn_cxp (syn_chwcn A) (syn_chwcn A)))
      (syn_cvv) p0000 p0028
  exact p0029


end NFChoice.DirectNominalPrf.WPPReplay

end

/-! Certificates from `NominalWPPReplayChunk014Compact001Part040`. -/


section

namespace NFChoice.DirectNominalPrf.WPPReplay

open scoped Fol
open NFChoice.Foundation
open NFChoice.SemanticCore
open NFChoice.ReplaySupport
open NFChoice.Compiler.CompactSourceSyntax

@[expose]
noncomputable def g_hwnisosymi (v : Var) (u : Var) (A : Class) (dv_A_u : u ∉ A.fv)
    (dv_A_v : v ∉ A.fv) (dv_u_v : u ≠ v) :
    Nominal.NPrf
      (.imp (syn_wbr (.cv u) (syn_chwniso A) (.cv v))
        (syn_wbr (.cv v) (syn_chwniso A) (.cv u))) :=
  by
  have dv_cache_0001 : u ≠ v := by exact (show u ≠ v from (by exact dv_u_v))
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
  have dv_cache_0003 : v ∉ (A).fv :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact
      (by
        have compact_fv_not_mem_empty : v ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_A_v, not_false_eq_true])
  have dv_cache_0004 : v ≠ u :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact (show v ≠ u from (by exact Ne.symm dv_u_v))
  have p0000 := @g_hwnisohwisob v u A dv_cache_0001
  have p0001 :=
    @g_biimpi (syn_wbr (.cv u) (syn_chwniso A) (.cv v))
      (syn_wa (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))
        (syn_wbr (.cv u) (syn_chwiso A) (.cv v)))
      p0000
  have p0002 :=
    @g_simpld (syn_wbr (.cv u) (syn_chwniso A) (.cv v))
      (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))
      (syn_wbr (.cv u) (syn_chwiso A) (.cv v)) p0001
  have p0003 :=
    @g_ancom (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A))
  have p0004 :=
    @g_biimpi (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))
      (syn_wa (.classMem (.cv v) (syn_chwcn A)) (.classMem (.cv u) (syn_chwcn A))) p0003
  have p0005 :=
    @g_syl (syn_wbr (.cv u) (syn_chwniso A) (.cv v))
      (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))
      (syn_wa (.classMem (.cv v) (syn_chwcn A)) (.classMem (.cv u) (syn_chwcn A))) p0002
      p0004
  have p0008 :=
    @g_simprd (syn_wbr (.cv u) (syn_chwniso A) (.cv v))
      (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))
      (syn_wbr (.cv u) (syn_chwiso A) (.cv v)) p0001
  have p0009 := @g_hwisosymi v u A dv_cache_0002 dv_cache_0003 dv_cache_0001
  have p0010 :=
    @g_syl (syn_wbr (.cv u) (syn_chwniso A) (.cv v))
      (syn_wbr (.cv u) (syn_chwiso A) (.cv v)) (syn_wbr (.cv v) (syn_chwiso A) (.cv u))
      p0008 p0009
  have p0011 :=
    @g_jca (syn_wbr (.cv u) (syn_chwniso A) (.cv v))
      (syn_wa (.classMem (.cv v) (syn_chwcn A)) (.classMem (.cv u) (syn_chwcn A)))
      (syn_wbr (.cv v) (syn_chwiso A) (.cv u)) p0005 p0010
  have p0012 := @g_hwnisohwisob u v A dv_cache_0004
  have p0013 :=
    @g_biimpri (syn_wbr (.cv v) (syn_chwniso A) (.cv u))
      (syn_wa (syn_wa (.classMem (.cv v) (syn_chwcn A)) (.classMem (.cv u) (syn_chwcn A)))
        (syn_wbr (.cv v) (syn_chwiso A) (.cv u)))
      p0012
  have p0014 :=
    @g_syl (syn_wbr (.cv u) (syn_chwniso A) (.cv v))
      (syn_wa (syn_wa (.classMem (.cv v) (syn_chwcn A)) (.classMem (.cv u) (syn_chwcn A)))
        (syn_wbr (.cv v) (syn_chwiso A) (.cv u)))
      (syn_wbr (.cv v) (syn_chwniso A) (.cv u)) p0011 p0013
  exact p0014

@[expose]
noncomputable def g_hwnisotri (w : Var) (v : Var) (u : Var) (A : Class)
    (dv_A_u : u ∉ A.fv) (dv_A_v : v ∉ A.fv) (dv_A_w : w ∉ A.fv) (dv_u_v : u ≠ v)
    (dv_u_w : u ≠ w) (dv_v_w : v ≠ w) :
    Nominal.NPrf
      (.imp (syn_wa (syn_wbr (.cv u) (syn_chwniso A) (.cv v))
          (syn_wbr (.cv v) (syn_chwniso A) (.cv w)))
        (syn_wbr (.cv u) (syn_chwniso A) (.cv w))) :=
  by
  have dv_cache_0001 : u ≠ v := by exact (show u ≠ v from (by exact dv_u_v))
  have dv_cache_0002 : v ≠ w := by
    clear dv_cache_0001
    exact (show v ≠ w from (by exact dv_v_w))
  have dv_cache_0003 : u ∉ (A).fv :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact
      (by
        have compact_fv_not_mem_empty : u ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_A_u, not_false_eq_true])
  have dv_cache_0004 : v ∉ (A).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact
      (by
        have compact_fv_not_mem_empty : v ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_A_v, not_false_eq_true])
  have dv_cache_0005 : w ∉ (A).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact
      (by
        have compact_fv_not_mem_empty : w ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_A_w, not_false_eq_true])
  have dv_cache_0006 : u ≠ w :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact (show u ≠ w from (by exact dv_u_w))
  have p0000 :=
    @g_simpl (syn_wbr (.cv u) (syn_chwniso A) (.cv v))
      (syn_wbr (.cv v) (syn_chwniso A) (.cv w))
  have p0001 := @g_hwnisohwisob v u A dv_cache_0001
  have p0002 :=
    @g_biimpi (syn_wbr (.cv u) (syn_chwniso A) (.cv v))
      (syn_wa (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))
        (syn_wbr (.cv u) (syn_chwiso A) (.cv v)))
      p0001
  have p0003 :=
    @g_syl
      (syn_wa (syn_wbr (.cv u) (syn_chwniso A) (.cv v))
        (syn_wbr (.cv v) (syn_chwniso A) (.cv w)))
      (syn_wbr (.cv u) (syn_chwniso A) (.cv v))
      (syn_wa (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))
        (syn_wbr (.cv u) (syn_chwiso A) (.cv v)))
      p0000 p0002
  have p0004 :=
    @g_simpl (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))
      (syn_wbr (.cv u) (syn_chwiso A) (.cv v))
  have p0005 :=
    @g_syl
      (syn_wa (syn_wbr (.cv u) (syn_chwniso A) (.cv v))
        (syn_wbr (.cv v) (syn_chwniso A) (.cv w)))
      (syn_wa (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))
        (syn_wbr (.cv u) (syn_chwiso A) (.cv v)))
      (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A))) p0003
      p0004
  have p0006 :=
    @g_simpl (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A))
  have p0007 :=
    @g_syl
      (syn_wa (syn_wbr (.cv u) (syn_chwniso A) (.cv v))
        (syn_wbr (.cv v) (syn_chwniso A) (.cv w)))
      (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))
      (.classMem (.cv u) (syn_chwcn A)) p0005 p0006
  have p0008 :=
    @g_simpr (syn_wbr (.cv u) (syn_chwniso A) (.cv v))
      (syn_wbr (.cv v) (syn_chwniso A) (.cv w))
  have p0009 := @g_hwnisohwisob w v A dv_cache_0002
  have p0010 :=
    @g_biimpi (syn_wbr (.cv v) (syn_chwniso A) (.cv w))
      (syn_wa (syn_wa (.classMem (.cv v) (syn_chwcn A)) (.classMem (.cv w) (syn_chwcn A)))
        (syn_wbr (.cv v) (syn_chwiso A) (.cv w)))
      p0009
  have p0011 :=
    @g_syl
      (syn_wa (syn_wbr (.cv u) (syn_chwniso A) (.cv v))
        (syn_wbr (.cv v) (syn_chwniso A) (.cv w)))
      (syn_wbr (.cv v) (syn_chwniso A) (.cv w))
      (syn_wa (syn_wa (.classMem (.cv v) (syn_chwcn A)) (.classMem (.cv w) (syn_chwcn A)))
        (syn_wbr (.cv v) (syn_chwiso A) (.cv w)))
      p0008 p0010
  have p0012 :=
    @g_simpl (syn_wa (.classMem (.cv v) (syn_chwcn A)) (.classMem (.cv w) (syn_chwcn A)))
      (syn_wbr (.cv v) (syn_chwiso A) (.cv w))
  have p0013 :=
    @g_syl
      (syn_wa (syn_wbr (.cv u) (syn_chwniso A) (.cv v))
        (syn_wbr (.cv v) (syn_chwniso A) (.cv w)))
      (syn_wa (syn_wa (.classMem (.cv v) (syn_chwcn A)) (.classMem (.cv w) (syn_chwcn A)))
        (syn_wbr (.cv v) (syn_chwiso A) (.cv w)))
      (syn_wa (.classMem (.cv v) (syn_chwcn A)) (.classMem (.cv w) (syn_chwcn A))) p0011
      p0012
  have p0014 :=
    @g_simpr (.classMem (.cv v) (syn_chwcn A)) (.classMem (.cv w) (syn_chwcn A))
  have p0015 :=
    @g_syl
      (syn_wa (syn_wbr (.cv u) (syn_chwniso A) (.cv v))
        (syn_wbr (.cv v) (syn_chwniso A) (.cv w)))
      (syn_wa (.classMem (.cv v) (syn_chwcn A)) (.classMem (.cv w) (syn_chwcn A)))
      (.classMem (.cv w) (syn_chwcn A)) p0013 p0014
  have p0016 :=
    @g_jca
      (syn_wa (syn_wbr (.cv u) (syn_chwniso A) (.cv v))
        (syn_wbr (.cv v) (syn_chwniso A) (.cv w)))
      (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv w) (syn_chwcn A)) p0007 p0015
  have p0021 :=
    @g_simpr (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))
      (syn_wbr (.cv u) (syn_chwiso A) (.cv v))
  have p0022 :=
    @g_syl
      (syn_wa (syn_wbr (.cv u) (syn_chwniso A) (.cv v))
        (syn_wbr (.cv v) (syn_chwniso A) (.cv w)))
      (syn_wa (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))
        (syn_wbr (.cv u) (syn_chwiso A) (.cv v)))
      (syn_wbr (.cv u) (syn_chwiso A) (.cv v)) p0003 p0021
  have p0027 :=
    @g_simpr (syn_wa (.classMem (.cv v) (syn_chwcn A)) (.classMem (.cv w) (syn_chwcn A)))
      (syn_wbr (.cv v) (syn_chwiso A) (.cv w))
  have p0028 :=
    @g_syl
      (syn_wa (syn_wbr (.cv u) (syn_chwniso A) (.cv v))
        (syn_wbr (.cv v) (syn_chwniso A) (.cv w)))
      (syn_wa (syn_wa (.classMem (.cv v) (syn_chwcn A)) (.classMem (.cv w) (syn_chwcn A)))
        (syn_wbr (.cv v) (syn_chwiso A) (.cv w)))
      (syn_wbr (.cv v) (syn_chwiso A) (.cv w)) p0011 p0027
  have p0029 :=
    @g_jca
      (syn_wa (syn_wbr (.cv u) (syn_chwniso A) (.cv v))
        (syn_wbr (.cv v) (syn_chwniso A) (.cv w)))
      (syn_wbr (.cv u) (syn_chwiso A) (.cv v)) (syn_wbr (.cv v) (syn_chwiso A) (.cv w))
      p0022 p0028
  have p0030 :=
    @g_hwisotri w v u A dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0001
      dv_cache_0006 dv_cache_0002
  have p0031 :=
    @g_syl
      (syn_wa (syn_wbr (.cv u) (syn_chwniso A) (.cv v))
        (syn_wbr (.cv v) (syn_chwniso A) (.cv w)))
      (syn_wa (syn_wbr (.cv u) (syn_chwiso A) (.cv v)) (syn_wbr (.cv v) (syn_chwiso A) (.cv w)))
      (syn_wbr (.cv u) (syn_chwiso A) (.cv w)) p0029 p0030
  have p0032 :=
    @g_jca
      (syn_wa (syn_wbr (.cv u) (syn_chwniso A) (.cv v))
        (syn_wbr (.cv v) (syn_chwniso A) (.cv w)))
      (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv w) (syn_chwcn A)))
      (syn_wbr (.cv u) (syn_chwiso A) (.cv w)) p0016 p0031
  have p0033 := @g_hwnisohwisob w u A dv_cache_0006
  have p0034 :=
    @g_biimpri (syn_wbr (.cv u) (syn_chwniso A) (.cv w))
      (syn_wa (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv w) (syn_chwcn A)))
        (syn_wbr (.cv u) (syn_chwiso A) (.cv w)))
      p0033
  have p0035 :=
    @g_syl
      (syn_wa (syn_wbr (.cv u) (syn_chwniso A) (.cv v))
        (syn_wbr (.cv v) (syn_chwniso A) (.cv w)))
      (syn_wa (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv w) (syn_chwcn A)))
        (syn_wbr (.cv u) (syn_chwiso A) (.cv w)))
      (syn_wbr (.cv u) (syn_chwniso A) (.cv w)) p0032 p0034
  exact p0035

@[expose]
noncomputable def g_hwnisoer (A : Class) :
    Nominal.NPrf
      (.imp (.classMem A (syn_cvv)) (syn_wbr (syn_chwniso A) (syn_cer) (syn_chwcn A))) :=
  by
  let proofSupport : Finset Var := A.fv
  let u : Var := freshVar proofSupport 0
  let v : Var := freshVar proofSupport 1
  let w : Var := freshVar proofSupport 2
  have fresh_u : u ∉ proofSupport :=
    by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_u_not_A : u ∉ A.fv := by
    intro h
    exact fresh_u (h)
  have fresh_v : v ∉ proofSupport :=
    by
    change freshVar proofSupport 1 ∉ proofSupport
    exact freshVar_not_mem proofSupport 1
  have fresh_v_not_A : v ∉ A.fv := by
    intro h
    exact fresh_v (h)
  have fresh_w : w ∉ proofSupport :=
    by
    change freshVar proofSupport 2 ∉ proofSupport
    exact freshVar_not_mem proofSupport 2
  have fresh_w_not_A : w ∉ A.fv := by
    intro h
    exact fresh_w (h)
  have fresh_u_ne_v : u ≠ v :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have fresh_v_ne_u : v ≠ u := Ne.symm fresh_u_ne_v
  have fresh_u_ne_w : u ≠ w :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 2
    exact freshVar_injective proofSupport (i := 0) (j := 2) (by decide)
  have fresh_v_ne_w : v ≠ w :=
    by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 2
    exact freshVar_injective proofSupport (i := 1) (j := 2) (by decide)
  have dv_cache_0001 : u ≠ v := by exact (show u ≠ v from (by exact fresh_u_ne_v))
  have dv_cache_0002 : u ∉ (A).fv :=
    by
    clear dv_cache_0001
    exact
      (by
        have compact_fv_not_mem_empty : u ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_u_not_A, not_false_eq_true])
  have dv_cache_0003 : v ∉ (A).fv :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact
      (by
        have compact_fv_not_mem_empty : v ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_v_not_A, not_false_eq_true])
  have dv_cache_0004 : v ≠ u :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact (show v ≠ u from (by exact fresh_v_ne_u))
  have dv_cache_0005 : v ≠ w :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact (show v ≠ w from (by exact fresh_v_ne_w))
  have dv_cache_0006 : w ∉ (A).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact
      (by
        have compact_fv_not_mem_empty : w ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_w_not_A, not_false_eq_true])
  have dv_cache_0007 : u ≠ w :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006
    exact (show u ≠ w from (by exact fresh_u_ne_w))
  have dv_cache_0008 : u ∉ ((syn_chwcn A)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007
    exact
      (by
        have compact_fv_not_mem_empty : u ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwcn,
          fresh_u_not_A, not_false_eq_true])
  have dv_cache_0009 : v ∉ ((syn_chwcn A)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008
    exact
      (by
        have compact_fv_not_mem_empty : v ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwcn,
          fresh_v_not_A, not_false_eq_true])
  have dv_cache_0010 : w ∉ ((syn_chwcn A)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009
    exact
      (by
        have compact_fv_not_mem_empty : w ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwcn,
          fresh_w_not_A, not_false_eq_true])
  have dv_cache_0011 : u ∉ ((syn_chwniso A)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010
    exact
      (by
        have compact_fv_not_mem_empty : u ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwniso,
          fresh_u_not_A, not_false_eq_true])
  have dv_cache_0012 : v ∉ ((syn_chwniso A)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
    exact
      (by
        have compact_fv_not_mem_empty : v ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwniso,
          fresh_v_not_A, not_false_eq_true])
  have dv_cache_0013 : w ∉ ((syn_chwniso A)).fv :=
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
        simp only [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwniso,
          fresh_w_not_A, not_false_eq_true])
  have dv_cache_0014 : u ∉ ((Wff.classMem A (syn_cvv))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013
    exact
      (by
        have compact_fv_not_mem_empty : u ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv, Finset.mem_union,
          fresh_u_not_A, compact_fv_not_mem_empty, or_false, not_false_eq_true])
  have dv_cache_0015 : v ∉ ((Wff.classMem A (syn_cvv))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014
    exact
      (by
        have compact_fv_not_mem_empty : v ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv, Finset.mem_union,
          fresh_v_not_A, compact_fv_not_mem_empty, or_false, not_false_eq_true])
  have dv_cache_0016 : w ∉ ((Wff.classMem A (syn_cvv))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015
    exact
      (by
        have compact_fv_not_mem_empty : w ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv, Finset.mem_union,
          fresh_w_not_A, compact_fv_not_mem_empty, or_false, not_false_eq_true])
  have p0000 := (Nominal.classEqRefl (syn_chwniso A))
  have p0001 := @g_hwgenex
  have p0002 := @g_hwbijex
  have p0003 := @g_vvex
  have p0004 := @g_xpex (syn_chwbij) (syn_cvv) p0002 p0003
  have p0005 := @g_imaex (syn_chwgen) (syn_cxp (syn_chwbij) (syn_cvv)) p0001 p0004
  have p0006 :=
    @g_a1i (.classMem (syn_cima (syn_chwgen) (syn_cxp (syn_chwbij) (syn_cvv))) (syn_cvv))
      (.classMem A (syn_cvv)) p0005
  have p0007 := (Nominal.classEqRefl (syn_chwcn A))
  have p0008 := @g_hwcodesexg A (syn_cvv)
  have p0009 := @g_hwrelsex
  have p0010 := @g_a1i (.classMem (syn_chwrels) (syn_cvv)) (.classMem A (syn_cvv)) p0009
  have p0011 :=
    @g_jca (.classMem A (syn_cvv)) (.classMem (syn_chwcodes A) (syn_cvv))
      (.classMem (syn_chwrels) (syn_cvv)) p0008 p0010
  have p0012 := @g_inexg (syn_chwcodes A) (syn_chwrels) (syn_cvv) (syn_cvv)
  have p0013 :=
    @g_syl (.classMem A (syn_cvv))
      (syn_wa (.classMem (syn_chwcodes A) (syn_cvv)) (.classMem (syn_chwrels) (syn_cvv)))
      (.classMem (syn_cin (syn_chwcodes A) (syn_chwrels)) (syn_cvv)) p0011 p0012
  have p0014 :=
    @g_syl5eqel (.classMem A (syn_cvv)) (syn_chwcn A)
      (syn_cin (syn_chwcodes A) (syn_chwrels)) (syn_cvv) p0007 p0013
  have p0023 :=
    @g_jca (.classMem A (syn_cvv)) (.classMem (syn_chwcn A) (syn_cvv))
      (.classMem (syn_chwcn A) (syn_cvv)) p0014 p0014
  have p0024 := @g_xpexg (syn_chwcn A) (syn_chwcn A) (syn_cvv) (syn_cvv)
  have p0025 :=
    @g_syl (.classMem A (syn_cvv))
      (syn_wa (.classMem (syn_chwcn A) (syn_cvv)) (.classMem (syn_chwcn A) (syn_cvv)))
      (.classMem (syn_cxp (syn_chwcn A) (syn_chwcn A)) (syn_cvv)) p0023 p0024
  have p0026 :=
    @g_jca (.classMem A (syn_cvv))
      (.classMem (syn_cima (syn_chwgen) (syn_cxp (syn_chwbij) (syn_cvv))) (syn_cvv))
      (.classMem (syn_cxp (syn_chwcn A) (syn_chwcn A)) (syn_cvv)) p0006 p0025
  have p0027 :=
    @g_inexg (syn_cima (syn_chwgen) (syn_cxp (syn_chwbij) (syn_cvv)))
      (syn_cxp (syn_chwcn A) (syn_chwcn A)) (syn_cvv) (syn_cvv)
  have p0028 :=
    @g_syl (.classMem A (syn_cvv))
      (syn_wa (.classMem (syn_cima (syn_chwgen) (syn_cxp (syn_chwbij) (syn_cvv))) (syn_cvv))
        (.classMem (syn_cxp (syn_chwcn A) (syn_chwcn A)) (syn_cvv)))
      (.classMem (syn_cin (syn_cima (syn_chwgen) (syn_cxp (syn_chwbij) (syn_cvv)))
          (syn_cxp (syn_chwcn A) (syn_chwcn A))) (syn_cvv))
      p0026 p0027
  have p0029 :=
    @g_syl5eqel (.classMem A (syn_cvv)) (syn_chwniso A)
      (syn_cin (syn_cima (syn_chwgen) (syn_cxp (syn_chwbij) (syn_cvv)))
        (syn_cxp (syn_chwcn A) (syn_chwcn A)))
      (syn_cvv) p0000 p0028
  have p0038 := @g_hwnisohwisob v u A dv_cache_0001
  have p0039 :=
    @g_biimpi (syn_wbr (.cv u) (syn_chwniso A) (.cv v))
      (syn_wa (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))
        (syn_wbr (.cv u) (syn_chwiso A) (.cv v)))
      p0038
  have p0040 :=
    @g_simpld (syn_wbr (.cv u) (syn_chwniso A) (.cv v))
      (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))
      (syn_wbr (.cv u) (syn_chwiso A) (.cv v)) p0039
  have p0041 :=
    @g_ancom (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A))
  have p0042 :=
    @g_biimpi (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))
      (syn_wa (.classMem (.cv v) (syn_chwcn A)) (.classMem (.cv u) (syn_chwcn A))) p0041
  have p0043 :=
    @g_syl (syn_wbr (.cv u) (syn_chwniso A) (.cv v))
      (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))
      (syn_wa (.classMem (.cv v) (syn_chwcn A)) (.classMem (.cv u) (syn_chwcn A))) p0040
      p0042
  have p0046 :=
    @g_simprd (syn_wbr (.cv u) (syn_chwniso A) (.cv v))
      (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))
      (syn_wbr (.cv u) (syn_chwiso A) (.cv v)) p0039
  have p0047 := @g_hwisosymi v u A dv_cache_0002 dv_cache_0003 dv_cache_0001
  have p0048 :=
    @g_syl (syn_wbr (.cv u) (syn_chwniso A) (.cv v))
      (syn_wbr (.cv u) (syn_chwiso A) (.cv v)) (syn_wbr (.cv v) (syn_chwiso A) (.cv u))
      p0046 p0047
  have p0049 :=
    @g_jca (syn_wbr (.cv u) (syn_chwniso A) (.cv v))
      (syn_wa (.classMem (.cv v) (syn_chwcn A)) (.classMem (.cv u) (syn_chwcn A)))
      (syn_wbr (.cv v) (syn_chwiso A) (.cv u)) p0043 p0048
  have p0050 := @g_hwnisohwisob u v A dv_cache_0004
  have p0051 :=
    @g_biimpri (syn_wbr (.cv v) (syn_chwniso A) (.cv u))
      (syn_wa (syn_wa (.classMem (.cv v) (syn_chwcn A)) (.classMem (.cv u) (syn_chwcn A)))
        (syn_wbr (.cv v) (syn_chwiso A) (.cv u)))
      p0050
  have p0052 :=
    @g_syl (syn_wbr (.cv u) (syn_chwniso A) (.cv v))
      (syn_wa (syn_wa (.classMem (.cv v) (syn_chwcn A)) (.classMem (.cv u) (syn_chwcn A)))
        (syn_wbr (.cv v) (syn_chwiso A) (.cv u)))
      (syn_wbr (.cv v) (syn_chwniso A) (.cv u)) p0049 p0051
  have p0053 :=
    @g_n_3ad2ant3 (syn_wbr (.cv u) (syn_chwniso A) (.cv v)) (.classMem A (syn_cvv))
      (syn_wbr (.cv v) (syn_chwniso A) (.cv u))
      (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A))) p0052
  have p0054 :=
    @g_simpl (syn_wbr (.cv u) (syn_chwniso A) (.cv v))
      (syn_wbr (.cv v) (syn_chwniso A) (.cv w))
  have p0057 :=
    @g_syl
      (syn_wa (syn_wbr (.cv u) (syn_chwniso A) (.cv v))
        (syn_wbr (.cv v) (syn_chwniso A) (.cv w)))
      (syn_wbr (.cv u) (syn_chwniso A) (.cv v))
      (syn_wa (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))
        (syn_wbr (.cv u) (syn_chwiso A) (.cv v)))
      p0054 p0039
  have p0058 :=
    @g_simpl (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))
      (syn_wbr (.cv u) (syn_chwiso A) (.cv v))
  have p0059 :=
    @g_syl
      (syn_wa (syn_wbr (.cv u) (syn_chwniso A) (.cv v))
        (syn_wbr (.cv v) (syn_chwniso A) (.cv w)))
      (syn_wa (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))
        (syn_wbr (.cv u) (syn_chwiso A) (.cv v)))
      (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A))) p0057
      p0058
  have p0060 :=
    @g_simpl (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A))
  have p0061 :=
    @g_syl
      (syn_wa (syn_wbr (.cv u) (syn_chwniso A) (.cv v))
        (syn_wbr (.cv v) (syn_chwniso A) (.cv w)))
      (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))
      (.classMem (.cv u) (syn_chwcn A)) p0059 p0060
  have p0062 :=
    @g_simpr (syn_wbr (.cv u) (syn_chwniso A) (.cv v))
      (syn_wbr (.cv v) (syn_chwniso A) (.cv w))
  have p0063 := @g_hwnisohwisob w v A dv_cache_0005
  have p0064 :=
    @g_biimpi (syn_wbr (.cv v) (syn_chwniso A) (.cv w))
      (syn_wa (syn_wa (.classMem (.cv v) (syn_chwcn A)) (.classMem (.cv w) (syn_chwcn A)))
        (syn_wbr (.cv v) (syn_chwiso A) (.cv w)))
      p0063
  have p0065 :=
    @g_syl
      (syn_wa (syn_wbr (.cv u) (syn_chwniso A) (.cv v))
        (syn_wbr (.cv v) (syn_chwniso A) (.cv w)))
      (syn_wbr (.cv v) (syn_chwniso A) (.cv w))
      (syn_wa (syn_wa (.classMem (.cv v) (syn_chwcn A)) (.classMem (.cv w) (syn_chwcn A)))
        (syn_wbr (.cv v) (syn_chwiso A) (.cv w)))
      p0062 p0064
  have p0066 :=
    @g_simpl (syn_wa (.classMem (.cv v) (syn_chwcn A)) (.classMem (.cv w) (syn_chwcn A)))
      (syn_wbr (.cv v) (syn_chwiso A) (.cv w))
  have p0067 :=
    @g_syl
      (syn_wa (syn_wbr (.cv u) (syn_chwniso A) (.cv v))
        (syn_wbr (.cv v) (syn_chwniso A) (.cv w)))
      (syn_wa (syn_wa (.classMem (.cv v) (syn_chwcn A)) (.classMem (.cv w) (syn_chwcn A)))
        (syn_wbr (.cv v) (syn_chwiso A) (.cv w)))
      (syn_wa (.classMem (.cv v) (syn_chwcn A)) (.classMem (.cv w) (syn_chwcn A))) p0065
      p0066
  have p0068 :=
    @g_simpr (.classMem (.cv v) (syn_chwcn A)) (.classMem (.cv w) (syn_chwcn A))
  have p0069 :=
    @g_syl
      (syn_wa (syn_wbr (.cv u) (syn_chwniso A) (.cv v))
        (syn_wbr (.cv v) (syn_chwniso A) (.cv w)))
      (syn_wa (.classMem (.cv v) (syn_chwcn A)) (.classMem (.cv w) (syn_chwcn A)))
      (.classMem (.cv w) (syn_chwcn A)) p0067 p0068
  have p0070 :=
    @g_jca
      (syn_wa (syn_wbr (.cv u) (syn_chwniso A) (.cv v))
        (syn_wbr (.cv v) (syn_chwniso A) (.cv w)))
      (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv w) (syn_chwcn A)) p0061 p0069
  have p0075 :=
    @g_simpr (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))
      (syn_wbr (.cv u) (syn_chwiso A) (.cv v))
  have p0076 :=
    @g_syl
      (syn_wa (syn_wbr (.cv u) (syn_chwniso A) (.cv v))
        (syn_wbr (.cv v) (syn_chwniso A) (.cv w)))
      (syn_wa (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))
        (syn_wbr (.cv u) (syn_chwiso A) (.cv v)))
      (syn_wbr (.cv u) (syn_chwiso A) (.cv v)) p0057 p0075
  have p0081 :=
    @g_simpr (syn_wa (.classMem (.cv v) (syn_chwcn A)) (.classMem (.cv w) (syn_chwcn A)))
      (syn_wbr (.cv v) (syn_chwiso A) (.cv w))
  have p0082 :=
    @g_syl
      (syn_wa (syn_wbr (.cv u) (syn_chwniso A) (.cv v))
        (syn_wbr (.cv v) (syn_chwniso A) (.cv w)))
      (syn_wa (syn_wa (.classMem (.cv v) (syn_chwcn A)) (.classMem (.cv w) (syn_chwcn A)))
        (syn_wbr (.cv v) (syn_chwiso A) (.cv w)))
      (syn_wbr (.cv v) (syn_chwiso A) (.cv w)) p0065 p0081
  have p0083 :=
    @g_jca
      (syn_wa (syn_wbr (.cv u) (syn_chwniso A) (.cv v))
        (syn_wbr (.cv v) (syn_chwniso A) (.cv w)))
      (syn_wbr (.cv u) (syn_chwiso A) (.cv v)) (syn_wbr (.cv v) (syn_chwiso A) (.cv w))
      p0076 p0082
  have p0084 :=
    @g_hwisotri w v u A dv_cache_0002 dv_cache_0003 dv_cache_0006 dv_cache_0001
      dv_cache_0007 dv_cache_0005
  have p0085 :=
    @g_syl
      (syn_wa (syn_wbr (.cv u) (syn_chwniso A) (.cv v))
        (syn_wbr (.cv v) (syn_chwniso A) (.cv w)))
      (syn_wa (syn_wbr (.cv u) (syn_chwiso A) (.cv v)) (syn_wbr (.cv v) (syn_chwiso A) (.cv w)))
      (syn_wbr (.cv u) (syn_chwiso A) (.cv w)) p0083 p0084
  have p0086 :=
    @g_jca
      (syn_wa (syn_wbr (.cv u) (syn_chwniso A) (.cv v))
        (syn_wbr (.cv v) (syn_chwniso A) (.cv w)))
      (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv w) (syn_chwcn A)))
      (syn_wbr (.cv u) (syn_chwiso A) (.cv w)) p0070 p0085
  have p0087 := @g_hwnisohwisob w u A dv_cache_0007
  have p0088 :=
    @g_biimpri (syn_wbr (.cv u) (syn_chwniso A) (.cv w))
      (syn_wa (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv w) (syn_chwcn A)))
        (syn_wbr (.cv u) (syn_chwiso A) (.cv w)))
      p0087
  have p0089 :=
    @g_syl
      (syn_wa (syn_wbr (.cv u) (syn_chwniso A) (.cv v))
        (syn_wbr (.cv v) (syn_chwniso A) (.cv w)))
      (syn_wa (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv w) (syn_chwcn A)))
        (syn_wbr (.cv u) (syn_chwiso A) (.cv w)))
      (syn_wbr (.cv u) (syn_chwniso A) (.cv w)) p0086 p0088
  have p0090 :=
    @g_n_3ad2ant3
      (syn_wa (syn_wbr (.cv u) (syn_chwniso A) (.cv v))
        (syn_wbr (.cv v) (syn_chwniso A) (.cv w)))
      (.classMem A (syn_cvv)) (syn_wbr (.cv u) (syn_chwniso A) (.cv w))
      (syn_w3a (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A))
        (.classMem (.cv w) (syn_chwcn A)))
      p0089
  have p0091 :=
    @g_iserd (.classMem A (syn_cvv)) u v w (syn_chwcn A) (syn_chwniso A) (syn_cvv)
      (syn_cvv) dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012
      dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0001 dv_cache_0007
      dv_cache_0005 p0029 p0014 p0053 p0090
  exact p0091

@[expose]
noncomputable def g_hwnisorefli (u : Var) (A : Class) (dv_A_u : u ∉ A.fv) :
    Nominal.NPrf
      (.imp (.classMem (.cv u) (syn_chwcn A)) (syn_wbr (.cv u) (syn_chwniso A) (.cv u))) :=
  by
  let proofSupport : Finset Var := ({ u } : Finset Var) ∪ A.fv
  let v : Var := freshVar proofSupport 0
  have fresh_v : v ∉ proofSupport :=
    by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_v_ne_u : v ≠ u := by
    intro h
    exact fresh_v (Finset.mem_union_left _ (Finset.mem_singleton.mpr h))
  have fresh_u_ne_v : u ≠ v := Ne.symm fresh_v_ne_u
  have fresh_v_not_A : v ∉ A.fv := by
    intro h
    exact fresh_v (Finset.mem_union_right _ (h))
  have dv_cache_0001 : u ∉ (A).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : u ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_A_u, not_false_eq_true])
  have dv_cache_0002 : u ≠ v := by
    clear dv_cache_0001
    exact (show u ≠ v from (by exact fresh_u_ne_v))
  have dv_cache_0003 : v ∉ ((Class.cv u)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact
      (by
        have compact_fv_not_mem_empty : v ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_v_ne_u, not_false_eq_true])
  have dv_cache_0004 :
    v ∉
      ((syn_wb (syn_wbr (.cv u) (syn_chwniso A) (.cv u)) (syn_wa
            (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv u) (syn_chwcn A)))
            (syn_wbr (.cv u) (syn_chwiso A) (.cv u))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact
      (by
        have compact_fv_not_mem_empty : v ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wb,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwniso,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwcn,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwiso, Finset.mem_union,
          Finset.mem_singleton, fresh_v_ne_u, fresh_v_not_A, or_false, not_false_eq_true])
  have p0000 := @g_pm4_24 (.classMem (.cv u) (syn_chwcn A))
  have p0001 :=
    @g_biimpi (.classMem (.cv u) (syn_chwcn A))
      (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv u) (syn_chwcn A))) p0000
  have p0002 := @g_hwcnraw u A
  have p0003 := @g_hwisorefl u A dv_cache_0001
  have p0004 :=
    @g_syl (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv u) (syn_chwcodes A))
      (syn_wbr (.cv u) (syn_chwiso A) (.cv u)) p0002 p0003
  have p0005 :=
    @g_jca (.classMem (.cv u) (syn_chwcn A))
      (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv u) (syn_chwcn A)))
      (syn_wbr (.cv u) (syn_chwiso A) (.cv u)) p0001 p0004
  have p0006 := @g_elex (.cv u) (syn_chwcn A)
  have p0007 := @g_breq2 (.cv v) (.cv u) (.cv u) (syn_chwniso A)
  have p0008 := @g_eleq1 (.cv v) (.cv u) (syn_chwcn A)
  have p0009 :=
    @g_anbi2d (.classEq (.cv v) (.cv u)) (.classMem (.cv v) (syn_chwcn A))
      (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv u) (syn_chwcn A)) p0008
  have p0010 := @g_breq2 (.cv v) (.cv u) (.cv u) (syn_chwiso A)
  have p0011 :=
    @g_anbi12d (.classEq (.cv v) (.cv u))
      (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))
      (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv u) (syn_chwcn A)))
      (syn_wbr (.cv u) (syn_chwiso A) (.cv v)) (syn_wbr (.cv u) (syn_chwiso A) (.cv u))
      p0009 p0010
  have p0012 :=
    @g_bibi12d (.classEq (.cv v) (.cv u)) (syn_wbr (.cv u) (syn_chwniso A) (.cv v))
      (syn_wbr (.cv u) (syn_chwniso A) (.cv u))
      (syn_wa (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))
        (syn_wbr (.cv u) (syn_chwiso A) (.cv v)))
      (syn_wa (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv u) (syn_chwcn A)))
        (syn_wbr (.cv u) (syn_chwiso A) (.cv u)))
      p0007 p0011
  have p0013 := @g_hwnisohwisob v u A dv_cache_0002
  have p0014 :=
    @g_vtoclg
      (syn_wb (syn_wbr (.cv u) (syn_chwniso A) (.cv v)) (syn_wa
          (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))
          (syn_wbr (.cv u) (syn_chwiso A) (.cv v))))
      (syn_wb (syn_wbr (.cv u) (syn_chwniso A) (.cv u)) (syn_wa
          (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv u) (syn_chwcn A)))
          (syn_wbr (.cv u) (syn_chwiso A) (.cv u))))
      v (.cv u) (syn_cvv) dv_cache_0003 dv_cache_0004 p0012 p0013
  have p0015 :=
    @g_syl (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv u) (syn_cvv))
      (syn_wb (syn_wbr (.cv u) (syn_chwniso A) (.cv u)) (syn_wa
          (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv u) (syn_chwcn A)))
          (syn_wbr (.cv u) (syn_chwiso A) (.cv u))))
      p0006 p0014
  have p0016 :=
    @g_mpbird (.classMem (.cv u) (syn_chwcn A)) (syn_wbr (.cv u) (syn_chwniso A) (.cv u))
      (syn_wa (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv u) (syn_chwcn A)))
        (syn_wbr (.cv u) (syn_chwiso A) (.cv u)))
      p0005 p0015
  exact p0016

@[expose]
noncomputable def g_hwnisoerv (A : Class) :
    Nominal.NPrf
      (.imp (.classMem A (syn_cvv)) (syn_wbr (syn_chwniso A) (syn_cer) (syn_cvv))) :=
  by
  let proofSupport : Finset Var := A.fv
  let u : Var := freshVar proofSupport 0
  let v : Var := freshVar proofSupport 1
  let w : Var := freshVar proofSupport 2
  have fresh_u : u ∉ proofSupport :=
    by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_u_not_A : u ∉ A.fv := by
    intro h
    exact fresh_u (h)
  have fresh_v : v ∉ proofSupport :=
    by
    change freshVar proofSupport 1 ∉ proofSupport
    exact freshVar_not_mem proofSupport 1
  have fresh_v_not_A : v ∉ A.fv := by
    intro h
    exact fresh_v (h)
  have fresh_w : w ∉ proofSupport :=
    by
    change freshVar proofSupport 2 ∉ proofSupport
    exact freshVar_not_mem proofSupport 2
  have fresh_w_not_A : w ∉ A.fv := by
    intro h
    exact fresh_w (h)
  have fresh_u_ne_v : u ≠ v :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have fresh_u_ne_w : u ≠ w :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 2
    exact freshVar_injective proofSupport (i := 0) (j := 2) (by decide)
  have fresh_v_ne_w : v ≠ w :=
    by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 2
    exact freshVar_injective proofSupport (i := 1) (j := 2) (by decide)
  have dv_cache_0001 : u ∉ (A).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : u ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_u_not_A, not_false_eq_true])
  have dv_cache_0002 : v ∉ (A).fv :=
    by
    clear dv_cache_0001
    exact
      (by
        have compact_fv_not_mem_empty : v ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_v_not_A, not_false_eq_true])
  have dv_cache_0003 : u ≠ v :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact (show u ≠ v from (by exact fresh_u_ne_v))
  have dv_cache_0004 : w ∉ (A).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact
      (by
        have compact_fv_not_mem_empty : w ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_w_not_A, not_false_eq_true])
  have dv_cache_0005 : u ≠ w :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact (show u ≠ w from (by exact fresh_u_ne_w))
  have dv_cache_0006 : v ≠ w :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact (show v ≠ w from (by exact fresh_v_ne_w))
  have dv_cache_0007 : u ∉ ((syn_cvv)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006
    exact
      (by
        have compact_fv_not_mem_empty : u ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv,
          compact_fv_not_mem_empty, not_false_eq_true])
  have dv_cache_0008 : v ∉ ((syn_cvv)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007
    exact
      (by
        have compact_fv_not_mem_empty : v ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv,
          compact_fv_not_mem_empty, not_false_eq_true])
  have dv_cache_0009 : w ∉ ((syn_cvv)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008
    exact
      (by
        have compact_fv_not_mem_empty : w ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv,
          compact_fv_not_mem_empty, not_false_eq_true])
  have dv_cache_0010 : u ∉ ((syn_chwniso A)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009
    exact
      (by
        have compact_fv_not_mem_empty : u ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwniso,
          fresh_u_not_A, not_false_eq_true])
  have dv_cache_0011 : v ∉ ((syn_chwniso A)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010
    exact
      (by
        have compact_fv_not_mem_empty : v ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwniso,
          fresh_v_not_A, not_false_eq_true])
  have dv_cache_0012 : w ∉ ((syn_chwniso A)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
    exact
      (by
        have compact_fv_not_mem_empty : w ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwniso,
          fresh_w_not_A, not_false_eq_true])
  have dv_cache_0013 : u ∉ ((Wff.classMem A (syn_cvv))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012
    exact
      (by
        have compact_fv_not_mem_empty : u ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv, Finset.mem_union,
          fresh_u_not_A, compact_fv_not_mem_empty, or_false, not_false_eq_true])
  have dv_cache_0014 : v ∉ ((Wff.classMem A (syn_cvv))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013
    exact
      (by
        have compact_fv_not_mem_empty : v ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv, Finset.mem_union,
          fresh_v_not_A, compact_fv_not_mem_empty, or_false, not_false_eq_true])
  have dv_cache_0015 : w ∉ ((Wff.classMem A (syn_cvv))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014
    exact
      (by
        have compact_fv_not_mem_empty : w ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv, Finset.mem_union,
          fresh_w_not_A, compact_fv_not_mem_empty, or_false, not_false_eq_true])
  have p0000 := @g_hwnisoexg A
  have p0001 := @g_vvex
  have p0002 := @g_a1i (.classMem (syn_cvv) (syn_cvv)) (.classMem A (syn_cvv)) p0001
  have p0003 := @g_hwnisosymi v u A dv_cache_0001 dv_cache_0002 dv_cache_0003
  have p0004 :=
    @g_n_3ad2ant3 (syn_wbr (.cv u) (syn_chwniso A) (.cv v)) (.classMem A (syn_cvv))
      (syn_wbr (.cv v) (syn_chwniso A) (.cv u))
      (syn_wa (.classMem (.cv u) (syn_cvv)) (.classMem (.cv v) (syn_cvv))) p0003
  have p0005 :=
    @g_hwnisotri w v u A dv_cache_0001 dv_cache_0002 dv_cache_0004 dv_cache_0003
      dv_cache_0005 dv_cache_0006
  have p0006 :=
    @g_n_3ad2ant3
      (syn_wa (syn_wbr (.cv u) (syn_chwniso A) (.cv v))
        (syn_wbr (.cv v) (syn_chwniso A) (.cv w)))
      (.classMem A (syn_cvv)) (syn_wbr (.cv u) (syn_chwniso A) (.cv w))
      (syn_w3a (.classMem (.cv u) (syn_cvv)) (.classMem (.cv v) (syn_cvv))
        (.classMem (.cv w) (syn_cvv)))
      p0005
  have p0007 :=
    @g_iserd (.classMem A (syn_cvv)) u v w (syn_cvv) (syn_chwniso A) (syn_cvv) (syn_cvv)
      dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012
      dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0003 dv_cache_0005 dv_cache_0006
      p0000 p0002 p0004 p0006
  exact p0007


end NFChoice.DirectNominalPrf.WPPReplay

end
