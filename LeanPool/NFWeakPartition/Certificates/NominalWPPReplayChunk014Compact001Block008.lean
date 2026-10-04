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

/-- Checked nominal proof certificate identified upstream as `g_hwtrnbrd`. -/
@[expose]
noncomputable def gHwtrnbrd (x : Var) (y : Var) (f : Var) (r : Var) (_dv_f_x : f ≠ x)
    (_dv_f_y : f ≠ y) :
    Nominal.NPrf
      (.imp (synWfun (synCcnv (.cv f))) (synWb
          (synWbr (.cv x) (synCcom (synCcom (.cv f) (.cv r)) (synCcnv (.cv f))) (.cv y))
          (synWa (synWa (.classMem (.cv x) (synCrn (.cv f)))
              (.classMem (.cv y) (synCrn (.cv f))))
            (synWbr (synCfv (synCcnv (.cv f)) (.cv x)) (.cv r)
              (synCfv (synCcnv (.cv f)) (.cv y)))))) :=
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
  have dv_cache_0003 : z ∉ ((synCcom (.cv f) (.cv r))).fv :=
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
  have dv_cache_0004 : z ∉ ((synCcnv (.cv f))).fv :=
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
  have dv_cache_0005 : z ∉ ((synWfun (synCcnv (.cv f)))).fv :=
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
  have dv_cache_0006 : z ∉ ((Wff.classMem (.cv x) (synCdm (synCcnv (.cv f))))).fv :=
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
  have dv_cache_0007 : z ∉ ((synCfv (synCcnv (.cv f)) (.cv x))).fv :=
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
      ((synWbr (synCfv (synCcnv (.cv f)) (.cv x)) (synCcom (.cv f) (.cv r)) (.cv y))).fv :=
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
  have dv_cache_0009 : w ∉ ((synCfv (synCcnv (.cv f)) (.cv x))).fv :=
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
  have dv_cache_0013 : w ∉ ((synWfun (synCcnv (.cv f)))).fv :=
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
  have dv_cache_0014 : w ∉ ((Wff.classMem (.cv y) (synCdm (synCcnv (.cv f))))).fv :=
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
  have dv_cache_0015 : w ∉ ((synCfv (synCcnv (.cv f)) (.cv y))).fv :=
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
      ((synWbr (synCfv (synCcnv (.cv f)) (.cv x)) (.cv r)
          (synCfv (synCcnv (.cv f)) (.cv y)))).fv :=
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
    @gBrco z (.cv x) (.cv y) (synCcom (.cv f) (.cv r)) (synCcnv (.cv f)) dv_cache_0001
      dv_cache_0002 dv_cache_0003 dv_cache_0004
  have p0001 :=
    @gA1i
      (synWb (synWbr (.cv x) (synCcom (synCcom (.cv f) (.cv r)) (synCcnv (.cv f))) (.cv y))
        (synWex z (synWa (synWbr (.cv x) (synCcnv (.cv f)) (.cv z))
            (synWbr (.cv z) (synCcom (.cv f) (.cv r)) (.cv y)))))
      (synWfun (synCcnv (.cv f))) p0000
  have p0002 := @gFunbrfv2b (.cv x) (.cv z) (synCcnv (.cv f))
  have p0003 :=
    @gAnbi1d (synWfun (synCcnv (.cv f))) (synWbr (.cv x) (synCcnv (.cv f)) (.cv z))
      (synWa (.classMem (.cv x) (synCdm (synCcnv (.cv f))))
        (.classEq (synCfv (synCcnv (.cv f)) (.cv x)) (.cv z)))
      (synWbr (.cv z) (synCcom (.cv f) (.cv r)) (.cv y)) p0002
  have p0004 :=
    @gExbidv (synWfun (synCcnv (.cv f)))
      (synWa (synWbr (.cv x) (synCcnv (.cv f)) (.cv z))
        (synWbr (.cv z) (synCcom (.cv f) (.cv r)) (.cv y)))
      (synWa (synWa (.classMem (.cv x) (synCdm (synCcnv (.cv f))))
          (.classEq (synCfv (synCcnv (.cv f)) (.cv x)) (.cv z)))
        (synWbr (.cv z) (synCcom (.cv f) (.cv r)) (.cv y)))
      z dv_cache_0005 p0003
  have p0005 :=
    @gAnass (.classMem (.cv x) (synCdm (synCcnv (.cv f))))
      (.classEq (synCfv (synCcnv (.cv f)) (.cv x)) (.cv z))
      (synWbr (.cv z) (synCcom (.cv f) (.cv r)) (.cv y))
  have p0006 :=
    @gA1i
      (synWb (synWa (synWa (.classMem (.cv x) (synCdm (synCcnv (.cv f))))
            (.classEq (synCfv (synCcnv (.cv f)) (.cv x)) (.cv z)))
          (synWbr (.cv z) (synCcom (.cv f) (.cv r)) (.cv y)))
        (synWa (.classMem (.cv x) (synCdm (synCcnv (.cv f))))
          (synWa (.classEq (synCfv (synCcnv (.cv f)) (.cv x)) (.cv z))
            (synWbr (.cv z) (synCcom (.cv f) (.cv r)) (.cv y)))))
      (synWfun (synCcnv (.cv f))) p0005
  have p0007 :=
    @gExbidv (synWfun (synCcnv (.cv f)))
      (synWa (synWa (.classMem (.cv x) (synCdm (synCcnv (.cv f))))
          (.classEq (synCfv (synCcnv (.cv f)) (.cv x)) (.cv z)))
        (synWbr (.cv z) (synCcom (.cv f) (.cv r)) (.cv y)))
      (synWa (.classMem (.cv x) (synCdm (synCcnv (.cv f))))
        (synWa (.classEq (synCfv (synCcnv (.cv f)) (.cv x)) (.cv z))
          (synWbr (.cv z) (synCcom (.cv f) (.cv r)) (.cv y))))
      z dv_cache_0005 p0006
  have p0008 :=
    @gBitrd (synWfun (synCcnv (.cv f)))
      (synWex z (synWa (synWbr (.cv x) (synCcnv (.cv f)) (.cv z))
          (synWbr (.cv z) (synCcom (.cv f) (.cv r)) (.cv y))))
      (synWex z (synWa (synWa (.classMem (.cv x) (synCdm (synCcnv (.cv f))))
            (.classEq (synCfv (synCcnv (.cv f)) (.cv x)) (.cv z)))
          (synWbr (.cv z) (synCcom (.cv f) (.cv r)) (.cv y))))
      (synWex z (synWa (.classMem (.cv x) (synCdm (synCcnv (.cv f))))
          (synWa (.classEq (synCfv (synCcnv (.cv f)) (.cv x)) (.cv z))
            (synWbr (.cv z) (synCcom (.cv f) (.cv r)) (.cv y)))))
      p0004 p0007
  have p0009 :=
    @gN1942v (.classMem (.cv x) (synCdm (synCcnv (.cv f))))
      (synWa (.classEq (synCfv (synCcnv (.cv f)) (.cv x)) (.cv z))
        (synWbr (.cv z) (synCcom (.cv f) (.cv r)) (.cv y)))
      z dv_cache_0006
  have p0010 :=
    @gA1i
      (synWb (synWex z (synWa (.classMem (.cv x) (synCdm (synCcnv (.cv f))))
            (synWa (.classEq (synCfv (synCcnv (.cv f)) (.cv x)) (.cv z))
              (synWbr (.cv z) (synCcom (.cv f) (.cv r)) (.cv y)))))
        (synWa (.classMem (.cv x) (synCdm (synCcnv (.cv f)))) (synWex z
            (synWa (.classEq (synCfv (synCcnv (.cv f)) (.cv x)) (.cv z))
              (synWbr (.cv z) (synCcom (.cv f) (.cv r)) (.cv y))))))
      (synWfun (synCcnv (.cv f))) p0009
  have p0011 :=
    @gBitrd (synWfun (synCcnv (.cv f)))
      (synWex z (synWa (synWbr (.cv x) (synCcnv (.cv f)) (.cv z))
          (synWbr (.cv z) (synCcom (.cv f) (.cv r)) (.cv y))))
      (synWex z (synWa (.classMem (.cv x) (synCdm (synCcnv (.cv f))))
          (synWa (.classEq (synCfv (synCcnv (.cv f)) (.cv x)) (.cv z))
            (synWbr (.cv z) (synCcom (.cv f) (.cv r)) (.cv y)))))
      (synWa (.classMem (.cv x) (synCdm (synCcnv (.cv f)))) (synWex z
          (synWa (.classEq (synCfv (synCcnv (.cv f)) (.cv x)) (.cv z))
            (synWbr (.cv z) (synCcom (.cv f) (.cv r)) (.cv y)))))
      p0008 p0010
  have p0012 := @gEqcom (synCfv (synCcnv (.cv f)) (.cv x)) (.cv z)
  have p0013 :=
    @gAnbi1i (.classEq (synCfv (synCcnv (.cv f)) (.cv x)) (.cv z))
      (.classEq (.cv z) (synCfv (synCcnv (.cv f)) (.cv x)))
      (synWbr (.cv z) (synCcom (.cv f) (.cv r)) (.cv y)) p0012
  have p0014 :=
    @gExbii
      (synWa (.classEq (synCfv (synCcnv (.cv f)) (.cv x)) (.cv z))
        (synWbr (.cv z) (synCcom (.cv f) (.cv r)) (.cv y)))
      (synWa (.classEq (.cv z) (synCfv (synCcnv (.cv f)) (.cv x)))
        (synWbr (.cv z) (synCcom (.cv f) (.cv r)) (.cv y)))
      z p0013
  have p0015 := @gFvex (.cv x) (synCcnv (.cv f))
  have p0016 :=
    @gBreq1 (.cv z) (synCfv (synCcnv (.cv f)) (.cv x)) (.cv y)
      (synCcom (.cv f) (.cv r))
  have p0017 :=
    @gCeqsexv (synWbr (.cv z) (synCcom (.cv f) (.cv r)) (.cv y))
      (synWbr (synCfv (synCcnv (.cv f)) (.cv x)) (synCcom (.cv f) (.cv r)) (.cv y)) z
      (synCfv (synCcnv (.cv f)) (.cv x)) dv_cache_0007 dv_cache_0008 p0015 p0016
  have p0018 :=
    @gBitri
      (synWex z (synWa (.classEq (synCfv (synCcnv (.cv f)) (.cv x)) (.cv z))
          (synWbr (.cv z) (synCcom (.cv f) (.cv r)) (.cv y))))
      (synWex z (synWa (.classEq (.cv z) (synCfv (synCcnv (.cv f)) (.cv x)))
          (synWbr (.cv z) (synCcom (.cv f) (.cv r)) (.cv y))))
      (synWbr (synCfv (synCcnv (.cv f)) (.cv x)) (synCcom (.cv f) (.cv r)) (.cv y))
      p0014 p0017
  have p0019 :=
    @gAnbi2i
      (synWex z (synWa (.classEq (synCfv (synCcnv (.cv f)) (.cv x)) (.cv z))
          (synWbr (.cv z) (synCcom (.cv f) (.cv r)) (.cv y))))
      (synWbr (synCfv (synCcnv (.cv f)) (.cv x)) (synCcom (.cv f) (.cv r)) (.cv y))
      (.classMem (.cv x) (synCdm (synCcnv (.cv f)))) p0018
  have p0020 :=
    @gA1i
      (synWb (synWa (.classMem (.cv x) (synCdm (synCcnv (.cv f)))) (synWex z
            (synWa (.classEq (synCfv (synCcnv (.cv f)) (.cv x)) (.cv z))
              (synWbr (.cv z) (synCcom (.cv f) (.cv r)) (.cv y)))))
        (synWa (.classMem (.cv x) (synCdm (synCcnv (.cv f))))
          (synWbr (synCfv (synCcnv (.cv f)) (.cv x)) (synCcom (.cv f) (.cv r)) (.cv y))))
      (synWfun (synCcnv (.cv f))) p0019
  have p0021 :=
    @gBitrd (synWfun (synCcnv (.cv f)))
      (synWex z (synWa (synWbr (.cv x) (synCcnv (.cv f)) (.cv z))
          (synWbr (.cv z) (synCcom (.cv f) (.cv r)) (.cv y))))
      (synWa (.classMem (.cv x) (synCdm (synCcnv (.cv f)))) (synWex z
          (synWa (.classEq (synCfv (synCcnv (.cv f)) (.cv x)) (.cv z))
            (synWbr (.cv z) (synCcom (.cv f) (.cv r)) (.cv y)))))
      (synWa (.classMem (.cv x) (synCdm (synCcnv (.cv f))))
        (synWbr (synCfv (synCcnv (.cv f)) (.cv x)) (synCcom (.cv f) (.cv r)) (.cv y)))
      p0011 p0020
  have p0022 := @gDfrn4 (.cv f)
  have p0023 := @gEleq2i (synCrn (.cv f)) (synCdm (synCcnv (.cv f))) (.cv x) p0022
  have p0024 :=
    @gBicomi (.classMem (.cv x) (synCrn (.cv f)))
      (.classMem (.cv x) (synCdm (synCcnv (.cv f)))) p0023
  have p0025 :=
    @gAnbi1i (.classMem (.cv x) (synCdm (synCcnv (.cv f))))
      (.classMem (.cv x) (synCrn (.cv f)))
      (synWbr (synCfv (synCcnv (.cv f)) (.cv x)) (synCcom (.cv f) (.cv r)) (.cv y))
      p0024
  have p0026 :=
    @gA1i
      (synWb (synWa (.classMem (.cv x) (synCdm (synCcnv (.cv f))))
          (synWbr (synCfv (synCcnv (.cv f)) (.cv x)) (synCcom (.cv f) (.cv r)) (.cv y)))
        (synWa (.classMem (.cv x) (synCrn (.cv f)))
          (synWbr (synCfv (synCcnv (.cv f)) (.cv x)) (synCcom (.cv f) (.cv r)) (.cv y))))
      (synWfun (synCcnv (.cv f))) p0025
  have p0027 :=
    @gBitrd (synWfun (synCcnv (.cv f)))
      (synWex z (synWa (synWbr (.cv x) (synCcnv (.cv f)) (.cv z))
          (synWbr (.cv z) (synCcom (.cv f) (.cv r)) (.cv y))))
      (synWa (.classMem (.cv x) (synCdm (synCcnv (.cv f))))
        (synWbr (synCfv (synCcnv (.cv f)) (.cv x)) (synCcom (.cv f) (.cv r)) (.cv y)))
      (synWa (.classMem (.cv x) (synCrn (.cv f)))
        (synWbr (synCfv (synCcnv (.cv f)) (.cv x)) (synCcom (.cv f) (.cv r)) (.cv y)))
      p0021 p0026
  have p0028 :=
    @gBitrd (synWfun (synCcnv (.cv f)))
      (synWbr (.cv x) (synCcom (synCcom (.cv f) (.cv r)) (synCcnv (.cv f))) (.cv y))
      (synWex z (synWa (synWbr (.cv x) (synCcnv (.cv f)) (.cv z))
          (synWbr (.cv z) (synCcom (.cv f) (.cv r)) (.cv y))))
      (synWa (.classMem (.cv x) (synCrn (.cv f)))
        (synWbr (synCfv (synCcnv (.cv f)) (.cv x)) (synCcom (.cv f) (.cv r)) (.cv y)))
      p0001 p0027
  have p0029 :=
    @gBrco w (synCfv (synCcnv (.cv f)) (.cv x)) (.cv y) (.cv f) (.cv r) dv_cache_0009
      dv_cache_0010 dv_cache_0011 dv_cache_0012
  have p0030 :=
    @gA1i
      (synWb (synWbr (synCfv (synCcnv (.cv f)) (.cv x)) (synCcom (.cv f) (.cv r)) (.cv y))
        (synWex w (synWa (synWbr (synCfv (synCcnv (.cv f)) (.cv x)) (.cv r) (.cv w))
            (synWbr (.cv w) (.cv f) (.cv y)))))
      (synWfun (synCcnv (.cv f))) p0029
  have p0031 := @gBrcnv (.cv y) (.cv w) (.cv f)
  have p0032 :=
    @gBicomi (synWbr (.cv y) (synCcnv (.cv f)) (.cv w))
      (synWbr (.cv w) (.cv f) (.cv y)) p0031
  have p0033 :=
    @gA1i
      (synWb (synWbr (.cv w) (.cv f) (.cv y)) (synWbr (.cv y) (synCcnv (.cv f)) (.cv w)))
      (synWfun (synCcnv (.cv f))) p0032
  have p0034 := @gFunbrfv2b (.cv y) (.cv w) (synCcnv (.cv f))
  have p0035 :=
    @gBitrd (synWfun (synCcnv (.cv f))) (synWbr (.cv w) (.cv f) (.cv y))
      (synWbr (.cv y) (synCcnv (.cv f)) (.cv w))
      (synWa (.classMem (.cv y) (synCdm (synCcnv (.cv f))))
        (.classEq (synCfv (synCcnv (.cv f)) (.cv y)) (.cv w)))
      p0033 p0034
  have p0036 :=
    @gAnbi2d (synWfun (synCcnv (.cv f))) (synWbr (.cv w) (.cv f) (.cv y))
      (synWa (.classMem (.cv y) (synCdm (synCcnv (.cv f))))
        (.classEq (synCfv (synCcnv (.cv f)) (.cv y)) (.cv w)))
      (synWbr (synCfv (synCcnv (.cv f)) (.cv x)) (.cv r) (.cv w)) p0035
  have p0037 :=
    @gExbidv (synWfun (synCcnv (.cv f)))
      (synWa (synWbr (synCfv (synCcnv (.cv f)) (.cv x)) (.cv r) (.cv w))
        (synWbr (.cv w) (.cv f) (.cv y)))
      (synWa (synWbr (synCfv (synCcnv (.cv f)) (.cv x)) (.cv r) (.cv w))
        (synWa (.classMem (.cv y) (synCdm (synCcnv (.cv f))))
          (.classEq (synCfv (synCcnv (.cv f)) (.cv y)) (.cv w))))
      w dv_cache_0013 p0036
  have p0038 :=
    @gAncom (synWbr (synCfv (synCcnv (.cv f)) (.cv x)) (.cv r) (.cv w))
      (synWa (.classMem (.cv y) (synCdm (synCcnv (.cv f))))
        (.classEq (synCfv (synCcnv (.cv f)) (.cv y)) (.cv w)))
  have p0039 :=
    @gAnass (.classMem (.cv y) (synCdm (synCcnv (.cv f))))
      (.classEq (synCfv (synCcnv (.cv f)) (.cv y)) (.cv w))
      (synWbr (synCfv (synCcnv (.cv f)) (.cv x)) (.cv r) (.cv w))
  have p0040 :=
    @gBitri
      (synWa (synWbr (synCfv (synCcnv (.cv f)) (.cv x)) (.cv r) (.cv w))
        (synWa (.classMem (.cv y) (synCdm (synCcnv (.cv f))))
          (.classEq (synCfv (synCcnv (.cv f)) (.cv y)) (.cv w))))
      (synWa (synWa (.classMem (.cv y) (synCdm (synCcnv (.cv f))))
          (.classEq (synCfv (synCcnv (.cv f)) (.cv y)) (.cv w)))
        (synWbr (synCfv (synCcnv (.cv f)) (.cv x)) (.cv r) (.cv w)))
      (synWa (.classMem (.cv y) (synCdm (synCcnv (.cv f))))
        (synWa (.classEq (synCfv (synCcnv (.cv f)) (.cv y)) (.cv w))
          (synWbr (synCfv (synCcnv (.cv f)) (.cv x)) (.cv r) (.cv w))))
      p0038 p0039
  have p0041 :=
    @gA1i
      (synWb (synWa (synWbr (synCfv (synCcnv (.cv f)) (.cv x)) (.cv r) (.cv w))
          (synWa (.classMem (.cv y) (synCdm (synCcnv (.cv f))))
            (.classEq (synCfv (synCcnv (.cv f)) (.cv y)) (.cv w))))
        (synWa (.classMem (.cv y) (synCdm (synCcnv (.cv f))))
          (synWa (.classEq (synCfv (synCcnv (.cv f)) (.cv y)) (.cv w))
            (synWbr (synCfv (synCcnv (.cv f)) (.cv x)) (.cv r) (.cv w)))))
      (synWfun (synCcnv (.cv f))) p0040
  have p0042 :=
    @gExbidv (synWfun (synCcnv (.cv f)))
      (synWa (synWbr (synCfv (synCcnv (.cv f)) (.cv x)) (.cv r) (.cv w))
        (synWa (.classMem (.cv y) (synCdm (synCcnv (.cv f))))
          (.classEq (synCfv (synCcnv (.cv f)) (.cv y)) (.cv w))))
      (synWa (.classMem (.cv y) (synCdm (synCcnv (.cv f))))
        (synWa (.classEq (synCfv (synCcnv (.cv f)) (.cv y)) (.cv w))
          (synWbr (synCfv (synCcnv (.cv f)) (.cv x)) (.cv r) (.cv w))))
      w dv_cache_0013 p0041
  have p0043 :=
    @gBitrd (synWfun (synCcnv (.cv f)))
      (synWex w (synWa (synWbr (synCfv (synCcnv (.cv f)) (.cv x)) (.cv r) (.cv w))
          (synWbr (.cv w) (.cv f) (.cv y))))
      (synWex w (synWa (synWbr (synCfv (synCcnv (.cv f)) (.cv x)) (.cv r) (.cv w))
          (synWa (.classMem (.cv y) (synCdm (synCcnv (.cv f))))
            (.classEq (synCfv (synCcnv (.cv f)) (.cv y)) (.cv w)))))
      (synWex w (synWa (.classMem (.cv y) (synCdm (synCcnv (.cv f))))
          (synWa (.classEq (synCfv (synCcnv (.cv f)) (.cv y)) (.cv w))
            (synWbr (synCfv (synCcnv (.cv f)) (.cv x)) (.cv r) (.cv w)))))
      p0037 p0042
  have p0044 :=
    @gN1942v (.classMem (.cv y) (synCdm (synCcnv (.cv f))))
      (synWa (.classEq (synCfv (synCcnv (.cv f)) (.cv y)) (.cv w))
        (synWbr (synCfv (synCcnv (.cv f)) (.cv x)) (.cv r) (.cv w)))
      w dv_cache_0014
  have p0045 :=
    @gA1i
      (synWb (synWex w (synWa (.classMem (.cv y) (synCdm (synCcnv (.cv f))))
            (synWa (.classEq (synCfv (synCcnv (.cv f)) (.cv y)) (.cv w))
              (synWbr (synCfv (synCcnv (.cv f)) (.cv x)) (.cv r) (.cv w)))))
        (synWa (.classMem (.cv y) (synCdm (synCcnv (.cv f)))) (synWex w
            (synWa (.classEq (synCfv (synCcnv (.cv f)) (.cv y)) (.cv w))
              (synWbr (synCfv (synCcnv (.cv f)) (.cv x)) (.cv r) (.cv w))))))
      (synWfun (synCcnv (.cv f))) p0044
  have p0046 :=
    @gBitrd (synWfun (synCcnv (.cv f)))
      (synWex w (synWa (synWbr (synCfv (synCcnv (.cv f)) (.cv x)) (.cv r) (.cv w))
          (synWbr (.cv w) (.cv f) (.cv y))))
      (synWex w (synWa (.classMem (.cv y) (synCdm (synCcnv (.cv f))))
          (synWa (.classEq (synCfv (synCcnv (.cv f)) (.cv y)) (.cv w))
            (synWbr (synCfv (synCcnv (.cv f)) (.cv x)) (.cv r) (.cv w)))))
      (synWa (.classMem (.cv y) (synCdm (synCcnv (.cv f)))) (synWex w
          (synWa (.classEq (synCfv (synCcnv (.cv f)) (.cv y)) (.cv w))
            (synWbr (synCfv (synCcnv (.cv f)) (.cv x)) (.cv r) (.cv w)))))
      p0043 p0045
  have p0047 := @gEqcom (synCfv (synCcnv (.cv f)) (.cv y)) (.cv w)
  have p0048 :=
    @gAnbi1i (.classEq (synCfv (synCcnv (.cv f)) (.cv y)) (.cv w))
      (.classEq (.cv w) (synCfv (synCcnv (.cv f)) (.cv y)))
      (synWbr (synCfv (synCcnv (.cv f)) (.cv x)) (.cv r) (.cv w)) p0047
  have p0049 :=
    @gExbii
      (synWa (.classEq (synCfv (synCcnv (.cv f)) (.cv y)) (.cv w))
        (synWbr (synCfv (synCcnv (.cv f)) (.cv x)) (.cv r) (.cv w)))
      (synWa (.classEq (.cv w) (synCfv (synCcnv (.cv f)) (.cv y)))
        (synWbr (synCfv (synCcnv (.cv f)) (.cv x)) (.cv r) (.cv w)))
      w p0048
  have p0050 := @gFvex (.cv y) (synCcnv (.cv f))
  have p0051 :=
    @gBreq2 (.cv w) (synCfv (synCcnv (.cv f)) (.cv y))
      (synCfv (synCcnv (.cv f)) (.cv x)) (.cv r)
  have p0052 :=
    @gCeqsexv (synWbr (synCfv (synCcnv (.cv f)) (.cv x)) (.cv r) (.cv w))
      (synWbr (synCfv (synCcnv (.cv f)) (.cv x)) (.cv r)
        (synCfv (synCcnv (.cv f)) (.cv y)))
      w (synCfv (synCcnv (.cv f)) (.cv y)) dv_cache_0015 dv_cache_0016 p0050 p0051
  have p0053 :=
    @gBitri
      (synWex w (synWa (.classEq (synCfv (synCcnv (.cv f)) (.cv y)) (.cv w))
          (synWbr (synCfv (synCcnv (.cv f)) (.cv x)) (.cv r) (.cv w))))
      (synWex w (synWa (.classEq (.cv w) (synCfv (synCcnv (.cv f)) (.cv y)))
          (synWbr (synCfv (synCcnv (.cv f)) (.cv x)) (.cv r) (.cv w))))
      (synWbr (synCfv (synCcnv (.cv f)) (.cv x)) (.cv r)
        (synCfv (synCcnv (.cv f)) (.cv y)))
      p0049 p0052
  have p0054 :=
    @gAnbi2i
      (synWex w (synWa (.classEq (synCfv (synCcnv (.cv f)) (.cv y)) (.cv w))
          (synWbr (synCfv (synCcnv (.cv f)) (.cv x)) (.cv r) (.cv w))))
      (synWbr (synCfv (synCcnv (.cv f)) (.cv x)) (.cv r)
        (synCfv (synCcnv (.cv f)) (.cv y)))
      (.classMem (.cv y) (synCdm (synCcnv (.cv f)))) p0053
  have p0055 :=
    @gA1i
      (synWb (synWa (.classMem (.cv y) (synCdm (synCcnv (.cv f)))) (synWex w
            (synWa (.classEq (synCfv (synCcnv (.cv f)) (.cv y)) (.cv w))
              (synWbr (synCfv (synCcnv (.cv f)) (.cv x)) (.cv r) (.cv w)))))
        (synWa (.classMem (.cv y) (synCdm (synCcnv (.cv f))))
          (synWbr (synCfv (synCcnv (.cv f)) (.cv x)) (.cv r)
            (synCfv (synCcnv (.cv f)) (.cv y)))))
      (synWfun (synCcnv (.cv f))) p0054
  have p0056 :=
    @gBitrd (synWfun (synCcnv (.cv f)))
      (synWex w (synWa (synWbr (synCfv (synCcnv (.cv f)) (.cv x)) (.cv r) (.cv w))
          (synWbr (.cv w) (.cv f) (.cv y))))
      (synWa (.classMem (.cv y) (synCdm (synCcnv (.cv f)))) (synWex w
          (synWa (.classEq (synCfv (synCcnv (.cv f)) (.cv y)) (.cv w))
            (synWbr (synCfv (synCcnv (.cv f)) (.cv x)) (.cv r) (.cv w)))))
      (synWa (.classMem (.cv y) (synCdm (synCcnv (.cv f))))
        (synWbr (synCfv (synCcnv (.cv f)) (.cv x)) (.cv r)
          (synCfv (synCcnv (.cv f)) (.cv y))))
      p0046 p0055
  have p0058 := @gEleq2i (synCrn (.cv f)) (synCdm (synCcnv (.cv f))) (.cv y) p0022
  have p0059 :=
    @gBicomi (.classMem (.cv y) (synCrn (.cv f)))
      (.classMem (.cv y) (synCdm (synCcnv (.cv f)))) p0058
  have p0060 :=
    @gAnbi1i (.classMem (.cv y) (synCdm (synCcnv (.cv f))))
      (.classMem (.cv y) (synCrn (.cv f)))
      (synWbr (synCfv (synCcnv (.cv f)) (.cv x)) (.cv r)
        (synCfv (synCcnv (.cv f)) (.cv y)))
      p0059
  have p0061 :=
    @gA1i
      (synWb (synWa (.classMem (.cv y) (synCdm (synCcnv (.cv f))))
          (synWbr (synCfv (synCcnv (.cv f)) (.cv x)) (.cv r)
            (synCfv (synCcnv (.cv f)) (.cv y)))) (synWa (.classMem (.cv y) (synCrn (.cv f)))
          (synWbr (synCfv (synCcnv (.cv f)) (.cv x)) (.cv r)
            (synCfv (synCcnv (.cv f)) (.cv y)))))
      (synWfun (synCcnv (.cv f))) p0060
  have p0062 :=
    @gBitrd (synWfun (synCcnv (.cv f)))
      (synWex w (synWa (synWbr (synCfv (synCcnv (.cv f)) (.cv x)) (.cv r) (.cv w))
          (synWbr (.cv w) (.cv f) (.cv y))))
      (synWa (.classMem (.cv y) (synCdm (synCcnv (.cv f))))
        (synWbr (synCfv (synCcnv (.cv f)) (.cv x)) (.cv r)
          (synCfv (synCcnv (.cv f)) (.cv y))))
      (synWa (.classMem (.cv y) (synCrn (.cv f)))
        (synWbr (synCfv (synCcnv (.cv f)) (.cv x)) (.cv r)
          (synCfv (synCcnv (.cv f)) (.cv y))))
      p0056 p0061
  have p0063 :=
    @gBitrd (synWfun (synCcnv (.cv f)))
      (synWbr (synCfv (synCcnv (.cv f)) (.cv x)) (synCcom (.cv f) (.cv r)) (.cv y))
      (synWex w (synWa (synWbr (synCfv (synCcnv (.cv f)) (.cv x)) (.cv r) (.cv w))
          (synWbr (.cv w) (.cv f) (.cv y))))
      (synWa (.classMem (.cv y) (synCrn (.cv f)))
        (synWbr (synCfv (synCcnv (.cv f)) (.cv x)) (.cv r)
          (synCfv (synCcnv (.cv f)) (.cv y))))
      p0030 p0062
  have p0064 :=
    @gAnbi2d (synWfun (synCcnv (.cv f)))
      (synWbr (synCfv (synCcnv (.cv f)) (.cv x)) (synCcom (.cv f) (.cv r)) (.cv y))
      (synWa (.classMem (.cv y) (synCrn (.cv f)))
        (synWbr (synCfv (synCcnv (.cv f)) (.cv x)) (.cv r)
          (synCfv (synCcnv (.cv f)) (.cv y))))
      (.classMem (.cv x) (synCrn (.cv f))) p0063
  have p0065 :=
    @gBitrd (synWfun (synCcnv (.cv f)))
      (synWbr (.cv x) (synCcom (synCcom (.cv f) (.cv r)) (synCcnv (.cv f))) (.cv y))
      (synWa (.classMem (.cv x) (synCrn (.cv f)))
        (synWbr (synCfv (synCcnv (.cv f)) (.cv x)) (synCcom (.cv f) (.cv r)) (.cv y)))
      (synWa (.classMem (.cv x) (synCrn (.cv f)))
        (synWa (.classMem (.cv y) (synCrn (.cv f)))
          (synWbr (synCfv (synCcnv (.cv f)) (.cv x)) (.cv r)
            (synCfv (synCcnv (.cv f)) (.cv y)))))
      p0028 p0064
  have p0066 :=
    @gAnass (.classMem (.cv x) (synCrn (.cv f))) (.classMem (.cv y) (synCrn (.cv f)))
      (synWbr (synCfv (synCcnv (.cv f)) (.cv x)) (.cv r)
        (synCfv (synCcnv (.cv f)) (.cv y)))
  have p0067 :=
    @gBicomi
      (synWa (synWa (.classMem (.cv x) (synCrn (.cv f)))
          (.classMem (.cv y) (synCrn (.cv f))))
        (synWbr (synCfv (synCcnv (.cv f)) (.cv x)) (.cv r)
          (synCfv (synCcnv (.cv f)) (.cv y))))
      (synWa (.classMem (.cv x) (synCrn (.cv f)))
        (synWa (.classMem (.cv y) (synCrn (.cv f)))
          (synWbr (synCfv (synCcnv (.cv f)) (.cv x)) (.cv r)
            (synCfv (synCcnv (.cv f)) (.cv y)))))
      p0066
  have p0068 :=
    @gA1i
      (synWb (synWa (.classMem (.cv x) (synCrn (.cv f)))
          (synWa (.classMem (.cv y) (synCrn (.cv f)))
            (synWbr (synCfv (synCcnv (.cv f)) (.cv x)) (.cv r)
              (synCfv (synCcnv (.cv f)) (.cv y))))) (synWa
          (synWa (.classMem (.cv x) (synCrn (.cv f))) (.classMem (.cv y) (synCrn (.cv f))))
          (synWbr (synCfv (synCcnv (.cv f)) (.cv x)) (.cv r)
            (synCfv (synCcnv (.cv f)) (.cv y)))))
      (synWfun (synCcnv (.cv f))) p0067
  have p0069 :=
    @gBitrd (synWfun (synCcnv (.cv f)))
      (synWbr (.cv x) (synCcom (synCcom (.cv f) (.cv r)) (synCcnv (.cv f))) (.cv y))
      (synWa (.classMem (.cv x) (synCrn (.cv f)))
        (synWa (.classMem (.cv y) (synCrn (.cv f)))
          (synWbr (synCfv (synCcnv (.cv f)) (.cv x)) (.cv r)
            (synCfv (synCcnv (.cv f)) (.cv y)))))
      (synWa (synWa (.classMem (.cv x) (synCrn (.cv f)))
          (.classMem (.cv y) (synCrn (.cv f))))
        (synWbr (synCfv (synCcnv (.cv f)) (.cv x)) (.cv r)
          (synCfv (synCcnv (.cv f)) (.cv y))))
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

/-- Checked nominal proof certificate identified upstream as `g_hwtrnisob`. -/
@[expose]
noncomputable def gHwtrnisob (f : Var) (r : Var) :
    Nominal.NPrf
      (synWb (synWf1o (.cv f) (synCdm (.cv f)) (synCrn (.cv f)))
        (synWiso (.cv f) (.cv r) (synCcom (synCcom (.cv f) (.cv r)) (synCcnv (.cv f)))
          (synCdm (.cv f)) (synCrn (.cv f)))) :=
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
  have dv_cache_0001 : z ∉ ((synCdm (.cv f))).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdm,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton, fresh_z_ne_f,
          not_false_eq_true])
  have dv_cache_0002 : w ∉ ((synCdm (.cv f))).fv :=
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
  have dv_cache_0003 : z ∉ ((synCrn (.cv f))).fv :=
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
  have dv_cache_0004 : w ∉ ((synCrn (.cv f))).fv :=
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
  have dv_cache_0012 : z ∉ ((synCcom (.cv f) (.cv r))).fv :=
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
  have dv_cache_0013 : z ∉ ((synCcnv (.cv f))).fv :=
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
  have dv_cache_0014 : z ∉ ((synWfun (synCcnv (.cv f)))).fv :=
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
  have dv_cache_0015 : z ∉ ((Wff.classMem (.cv x) (synCdm (synCcnv (.cv f))))).fv :=
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
  have dv_cache_0016 : z ∉ ((synCfv (synCcnv (.cv f)) (.cv x))).fv :=
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
      ((synWbr (synCfv (synCcnv (.cv f)) (.cv x)) (synCcom (.cv f) (.cv r)) (.cv y))).fv :=
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
  have dv_cache_0018 : w ∉ ((synCfv (synCcnv (.cv f)) (.cv x))).fv :=
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
  have dv_cache_0020 : w ∉ ((synWfun (synCcnv (.cv f)))).fv :=
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
  have dv_cache_0021 : w ∉ ((Wff.classMem (.cv y) (synCdm (synCcnv (.cv f))))).fv :=
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
  have dv_cache_0022 : w ∉ ((synCfv (synCcnv (.cv f)) (.cv y))).fv :=
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
      ((synWbr (synCfv (synCcnv (.cv f)) (.cv x)) (.cv r)
          (synCfv (synCcnv (.cv f)) (.cv y)))).fv :=
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
      ((synWa (synWa (.classMem (.cv x) (synCrn (.cv f)))
            (.classMem (.cv y) (synCrn (.cv f))))
          (synWbr (synCfv (synCcnv (.cv f)) (.cv x)) (.cv r)
            (synCfv (synCcnv (.cv f)) (.cv y))))).fv :=
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
      ((synWa (synWa (.classMem (.cv x) (synCrn (.cv f)))
            (.classMem (.cv y) (synCrn (.cv f))))
          (synWbr (synCfv (synCcnv (.cv f)) (.cv x)) (.cv r)
            (synCfv (synCcnv (.cv f)) (.cv y))))).fv :=
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
    x ∉ ((synCcom (synCcom (.cv f) (.cv r)) (synCcnv (.cv f)))).fv :=
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
    y ∉ ((synCcom (synCcom (.cv f) (.cv r)) (synCcnv (.cv f)))).fv :=
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
      ((synCopab z w (synWa (synWa (.classMem (.cv z) (synCrn (.cv f)))
              (.classMem (.cv w) (synCrn (.cv f))))
            (synWbr (synCfv (synCcnv (.cv f)) (.cv z)) (.cv r)
              (synCfv (synCcnv (.cv f)) (.cv w)))))).fv :=
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
      ((synCopab z w (synWa (synWa (.classMem (.cv z) (synCrn (.cv f)))
              (.classMem (.cv w) (synCrn (.cv f))))
            (synWbr (synCfv (synCcnv (.cv f)) (.cv z)) (.cv r)
              (synCfv (synCcnv (.cv f)) (.cv w)))))).fv :=
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
  have dv_cache_0031 : x ∉ ((synWfun (synCcnv (.cv f)))).fv :=
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
  have dv_cache_0032 : y ∉ ((synWfun (synCcnv (.cv f)))).fv :=
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
    @gEqid
      (synCopab z w (synWa (synWa (.classMem (.cv z) (synCrn (.cv f)))
            (.classMem (.cv w) (synCrn (.cv f))))
          (synWbr (synCfv (synCcnv (.cv f)) (.cv z)) (.cv r)
            (synCfv (synCcnv (.cv f)) (.cv w)))))
  have p0001 :=
    @gF1oiso2 z w (synCdm (.cv f)) (synCrn (.cv f)) (.cv r)
      (synCopab z w (synWa (synWa (.classMem (.cv z) (synCrn (.cv f)))
            (.classMem (.cv w) (synCrn (.cv f))))
          (synWbr (synCfv (synCcnv (.cv f)) (.cv z)) (.cv r)
            (synCfv (synCcnv (.cv f)) (.cv w)))))
      (.cv f) dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 p0000
  have p0002 := @gF1ocnv (synCdm (.cv f)) (synCrn (.cv f)) (.cv f)
  have p0003 := @gF1ofun (synCrn (.cv f)) (synCdm (.cv f)) (synCcnv (.cv f))
  have p0004 :=
    @gSyl (synWf1o (.cv f) (synCdm (.cv f)) (synCrn (.cv f)))
      (synWf1o (synCcnv (.cv f)) (synCrn (.cv f)) (synCdm (.cv f)))
      (synWfun (synCcnv (.cv f))) p0002 p0003
  have p0005 :=
    (Nominal.biimpRefl
      (synWbr (.cv x) (synCcom (synCcom (.cv f) (.cv r)) (synCcnv (.cv f))) (.cv y)))
  have p0006 :=
    @gBicomi
      (synWbr (.cv x) (synCcom (synCcom (.cv f) (.cv r)) (synCcnv (.cv f))) (.cv y))
      (.classMem (synCop (.cv x) (.cv y))
        (synCcom (synCcom (.cv f) (.cv r)) (synCcnv (.cv f))))
      p0005
  have p0007 :=
    @gA1i
      (synWb (.classMem (synCop (.cv x) (.cv y))
          (synCcom (synCcom (.cv f) (.cv r)) (synCcnv (.cv f))))
        (synWbr (.cv x) (synCcom (synCcom (.cv f) (.cv r)) (synCcnv (.cv f))) (.cv y)))
      (synWfun (synCcnv (.cv f))) p0006
  have p0008 :=
    @gBrco z (.cv x) (.cv y) (synCcom (.cv f) (.cv r)) (synCcnv (.cv f)) dv_cache_0010
      dv_cache_0011 dv_cache_0012 dv_cache_0013
  have p0009 :=
    @gA1i
      (synWb (synWbr (.cv x) (synCcom (synCcom (.cv f) (.cv r)) (synCcnv (.cv f))) (.cv y))
        (synWex z (synWa (synWbr (.cv x) (synCcnv (.cv f)) (.cv z))
            (synWbr (.cv z) (synCcom (.cv f) (.cv r)) (.cv y)))))
      (synWfun (synCcnv (.cv f))) p0008
  have p0010 := @gFunbrfv2b (.cv x) (.cv z) (synCcnv (.cv f))
  have p0011 :=
    @gAnbi1d (synWfun (synCcnv (.cv f))) (synWbr (.cv x) (synCcnv (.cv f)) (.cv z))
      (synWa (.classMem (.cv x) (synCdm (synCcnv (.cv f))))
        (.classEq (synCfv (synCcnv (.cv f)) (.cv x)) (.cv z)))
      (synWbr (.cv z) (synCcom (.cv f) (.cv r)) (.cv y)) p0010
  have p0012 :=
    @gExbidv (synWfun (synCcnv (.cv f)))
      (synWa (synWbr (.cv x) (synCcnv (.cv f)) (.cv z))
        (synWbr (.cv z) (synCcom (.cv f) (.cv r)) (.cv y)))
      (synWa (synWa (.classMem (.cv x) (synCdm (synCcnv (.cv f))))
          (.classEq (synCfv (synCcnv (.cv f)) (.cv x)) (.cv z)))
        (synWbr (.cv z) (synCcom (.cv f) (.cv r)) (.cv y)))
      z dv_cache_0014 p0011
  have p0013 :=
    @gAnass (.classMem (.cv x) (synCdm (synCcnv (.cv f))))
      (.classEq (synCfv (synCcnv (.cv f)) (.cv x)) (.cv z))
      (synWbr (.cv z) (synCcom (.cv f) (.cv r)) (.cv y))
  have p0014 :=
    @gA1i
      (synWb (synWa (synWa (.classMem (.cv x) (synCdm (synCcnv (.cv f))))
            (.classEq (synCfv (synCcnv (.cv f)) (.cv x)) (.cv z)))
          (synWbr (.cv z) (synCcom (.cv f) (.cv r)) (.cv y)))
        (synWa (.classMem (.cv x) (synCdm (synCcnv (.cv f))))
          (synWa (.classEq (synCfv (synCcnv (.cv f)) (.cv x)) (.cv z))
            (synWbr (.cv z) (synCcom (.cv f) (.cv r)) (.cv y)))))
      (synWfun (synCcnv (.cv f))) p0013
  have p0015 :=
    @gExbidv (synWfun (synCcnv (.cv f)))
      (synWa (synWa (.classMem (.cv x) (synCdm (synCcnv (.cv f))))
          (.classEq (synCfv (synCcnv (.cv f)) (.cv x)) (.cv z)))
        (synWbr (.cv z) (synCcom (.cv f) (.cv r)) (.cv y)))
      (synWa (.classMem (.cv x) (synCdm (synCcnv (.cv f))))
        (synWa (.classEq (synCfv (synCcnv (.cv f)) (.cv x)) (.cv z))
          (synWbr (.cv z) (synCcom (.cv f) (.cv r)) (.cv y))))
      z dv_cache_0014 p0014
  have p0016 :=
    @gBitrd (synWfun (synCcnv (.cv f)))
      (synWex z (synWa (synWbr (.cv x) (synCcnv (.cv f)) (.cv z))
          (synWbr (.cv z) (synCcom (.cv f) (.cv r)) (.cv y))))
      (synWex z (synWa (synWa (.classMem (.cv x) (synCdm (synCcnv (.cv f))))
            (.classEq (synCfv (synCcnv (.cv f)) (.cv x)) (.cv z)))
          (synWbr (.cv z) (synCcom (.cv f) (.cv r)) (.cv y))))
      (synWex z (synWa (.classMem (.cv x) (synCdm (synCcnv (.cv f))))
          (synWa (.classEq (synCfv (synCcnv (.cv f)) (.cv x)) (.cv z))
            (synWbr (.cv z) (synCcom (.cv f) (.cv r)) (.cv y)))))
      p0012 p0015
  have p0017 :=
    @gN1942v (.classMem (.cv x) (synCdm (synCcnv (.cv f))))
      (synWa (.classEq (synCfv (synCcnv (.cv f)) (.cv x)) (.cv z))
        (synWbr (.cv z) (synCcom (.cv f) (.cv r)) (.cv y)))
      z dv_cache_0015
  have p0018 :=
    @gA1i
      (synWb (synWex z (synWa (.classMem (.cv x) (synCdm (synCcnv (.cv f))))
            (synWa (.classEq (synCfv (synCcnv (.cv f)) (.cv x)) (.cv z))
              (synWbr (.cv z) (synCcom (.cv f) (.cv r)) (.cv y)))))
        (synWa (.classMem (.cv x) (synCdm (synCcnv (.cv f)))) (synWex z
            (synWa (.classEq (synCfv (synCcnv (.cv f)) (.cv x)) (.cv z))
              (synWbr (.cv z) (synCcom (.cv f) (.cv r)) (.cv y))))))
      (synWfun (synCcnv (.cv f))) p0017
  have p0019 :=
    @gBitrd (synWfun (synCcnv (.cv f)))
      (synWex z (synWa (synWbr (.cv x) (synCcnv (.cv f)) (.cv z))
          (synWbr (.cv z) (synCcom (.cv f) (.cv r)) (.cv y))))
      (synWex z (synWa (.classMem (.cv x) (synCdm (synCcnv (.cv f))))
          (synWa (.classEq (synCfv (synCcnv (.cv f)) (.cv x)) (.cv z))
            (synWbr (.cv z) (synCcom (.cv f) (.cv r)) (.cv y)))))
      (synWa (.classMem (.cv x) (synCdm (synCcnv (.cv f)))) (synWex z
          (synWa (.classEq (synCfv (synCcnv (.cv f)) (.cv x)) (.cv z))
            (synWbr (.cv z) (synCcom (.cv f) (.cv r)) (.cv y)))))
      p0016 p0018
  have p0020 := @gEqcom (synCfv (synCcnv (.cv f)) (.cv x)) (.cv z)
  have p0021 :=
    @gAnbi1i (.classEq (synCfv (synCcnv (.cv f)) (.cv x)) (.cv z))
      (.classEq (.cv z) (synCfv (synCcnv (.cv f)) (.cv x)))
      (synWbr (.cv z) (synCcom (.cv f) (.cv r)) (.cv y)) p0020
  have p0022 :=
    @gExbii
      (synWa (.classEq (synCfv (synCcnv (.cv f)) (.cv x)) (.cv z))
        (synWbr (.cv z) (synCcom (.cv f) (.cv r)) (.cv y)))
      (synWa (.classEq (.cv z) (synCfv (synCcnv (.cv f)) (.cv x)))
        (synWbr (.cv z) (synCcom (.cv f) (.cv r)) (.cv y)))
      z p0021
  have p0023 := @gFvex (.cv x) (synCcnv (.cv f))
  have p0024 :=
    @gBreq1 (.cv z) (synCfv (synCcnv (.cv f)) (.cv x)) (.cv y)
      (synCcom (.cv f) (.cv r))
  have p0025 :=
    @gCeqsexv (synWbr (.cv z) (synCcom (.cv f) (.cv r)) (.cv y))
      (synWbr (synCfv (synCcnv (.cv f)) (.cv x)) (synCcom (.cv f) (.cv r)) (.cv y)) z
      (synCfv (synCcnv (.cv f)) (.cv x)) dv_cache_0016 dv_cache_0017 p0023 p0024
  have p0026 :=
    @gBitri
      (synWex z (synWa (.classEq (synCfv (synCcnv (.cv f)) (.cv x)) (.cv z))
          (synWbr (.cv z) (synCcom (.cv f) (.cv r)) (.cv y))))
      (synWex z (synWa (.classEq (.cv z) (synCfv (synCcnv (.cv f)) (.cv x)))
          (synWbr (.cv z) (synCcom (.cv f) (.cv r)) (.cv y))))
      (synWbr (synCfv (synCcnv (.cv f)) (.cv x)) (synCcom (.cv f) (.cv r)) (.cv y))
      p0022 p0025
  have p0027 :=
    @gAnbi2i
      (synWex z (synWa (.classEq (synCfv (synCcnv (.cv f)) (.cv x)) (.cv z))
          (synWbr (.cv z) (synCcom (.cv f) (.cv r)) (.cv y))))
      (synWbr (synCfv (synCcnv (.cv f)) (.cv x)) (synCcom (.cv f) (.cv r)) (.cv y))
      (.classMem (.cv x) (synCdm (synCcnv (.cv f)))) p0026
  have p0028 :=
    @gA1i
      (synWb (synWa (.classMem (.cv x) (synCdm (synCcnv (.cv f)))) (synWex z
            (synWa (.classEq (synCfv (synCcnv (.cv f)) (.cv x)) (.cv z))
              (synWbr (.cv z) (synCcom (.cv f) (.cv r)) (.cv y)))))
        (synWa (.classMem (.cv x) (synCdm (synCcnv (.cv f))))
          (synWbr (synCfv (synCcnv (.cv f)) (.cv x)) (synCcom (.cv f) (.cv r)) (.cv y))))
      (synWfun (synCcnv (.cv f))) p0027
  have p0029 :=
    @gBitrd (synWfun (synCcnv (.cv f)))
      (synWex z (synWa (synWbr (.cv x) (synCcnv (.cv f)) (.cv z))
          (synWbr (.cv z) (synCcom (.cv f) (.cv r)) (.cv y))))
      (synWa (.classMem (.cv x) (synCdm (synCcnv (.cv f)))) (synWex z
          (synWa (.classEq (synCfv (synCcnv (.cv f)) (.cv x)) (.cv z))
            (synWbr (.cv z) (synCcom (.cv f) (.cv r)) (.cv y)))))
      (synWa (.classMem (.cv x) (synCdm (synCcnv (.cv f))))
        (synWbr (synCfv (synCcnv (.cv f)) (.cv x)) (synCcom (.cv f) (.cv r)) (.cv y)))
      p0019 p0028
  have p0030 := @gDfrn4 (.cv f)
  have p0031 := @gEleq2i (synCrn (.cv f)) (synCdm (synCcnv (.cv f))) (.cv x) p0030
  have p0032 :=
    @gBicomi (.classMem (.cv x) (synCrn (.cv f)))
      (.classMem (.cv x) (synCdm (synCcnv (.cv f)))) p0031
  have p0033 :=
    @gAnbi1i (.classMem (.cv x) (synCdm (synCcnv (.cv f))))
      (.classMem (.cv x) (synCrn (.cv f)))
      (synWbr (synCfv (synCcnv (.cv f)) (.cv x)) (synCcom (.cv f) (.cv r)) (.cv y))
      p0032
  have p0034 :=
    @gA1i
      (synWb (synWa (.classMem (.cv x) (synCdm (synCcnv (.cv f))))
          (synWbr (synCfv (synCcnv (.cv f)) (.cv x)) (synCcom (.cv f) (.cv r)) (.cv y)))
        (synWa (.classMem (.cv x) (synCrn (.cv f)))
          (synWbr (synCfv (synCcnv (.cv f)) (.cv x)) (synCcom (.cv f) (.cv r)) (.cv y))))
      (synWfun (synCcnv (.cv f))) p0033
  have p0035 :=
    @gBitrd (synWfun (synCcnv (.cv f)))
      (synWex z (synWa (synWbr (.cv x) (synCcnv (.cv f)) (.cv z))
          (synWbr (.cv z) (synCcom (.cv f) (.cv r)) (.cv y))))
      (synWa (.classMem (.cv x) (synCdm (synCcnv (.cv f))))
        (synWbr (synCfv (synCcnv (.cv f)) (.cv x)) (synCcom (.cv f) (.cv r)) (.cv y)))
      (synWa (.classMem (.cv x) (synCrn (.cv f)))
        (synWbr (synCfv (synCcnv (.cv f)) (.cv x)) (synCcom (.cv f) (.cv r)) (.cv y)))
      p0029 p0034
  have p0036 :=
    @gBitrd (synWfun (synCcnv (.cv f)))
      (synWbr (.cv x) (synCcom (synCcom (.cv f) (.cv r)) (synCcnv (.cv f))) (.cv y))
      (synWex z (synWa (synWbr (.cv x) (synCcnv (.cv f)) (.cv z))
          (synWbr (.cv z) (synCcom (.cv f) (.cv r)) (.cv y))))
      (synWa (.classMem (.cv x) (synCrn (.cv f)))
        (synWbr (synCfv (synCcnv (.cv f)) (.cv x)) (synCcom (.cv f) (.cv r)) (.cv y)))
      p0009 p0035
  have p0037 :=
    @gBrco w (synCfv (synCcnv (.cv f)) (.cv x)) (.cv y) (.cv f) (.cv r) dv_cache_0018
      dv_cache_0019 dv_cache_0006 dv_cache_0008
  have p0038 :=
    @gA1i
      (synWb (synWbr (synCfv (synCcnv (.cv f)) (.cv x)) (synCcom (.cv f) (.cv r)) (.cv y))
        (synWex w (synWa (synWbr (synCfv (synCcnv (.cv f)) (.cv x)) (.cv r) (.cv w))
            (synWbr (.cv w) (.cv f) (.cv y)))))
      (synWfun (synCcnv (.cv f))) p0037
  have p0039 := @gBrcnv (.cv y) (.cv w) (.cv f)
  have p0040 :=
    @gBicomi (synWbr (.cv y) (synCcnv (.cv f)) (.cv w))
      (synWbr (.cv w) (.cv f) (.cv y)) p0039
  have p0041 :=
    @gA1i
      (synWb (synWbr (.cv w) (.cv f) (.cv y)) (synWbr (.cv y) (synCcnv (.cv f)) (.cv w)))
      (synWfun (synCcnv (.cv f))) p0040
  have p0042 := @gFunbrfv2b (.cv y) (.cv w) (synCcnv (.cv f))
  have p0043 :=
    @gBitrd (synWfun (synCcnv (.cv f))) (synWbr (.cv w) (.cv f) (.cv y))
      (synWbr (.cv y) (synCcnv (.cv f)) (.cv w))
      (synWa (.classMem (.cv y) (synCdm (synCcnv (.cv f))))
        (.classEq (synCfv (synCcnv (.cv f)) (.cv y)) (.cv w)))
      p0041 p0042
  have p0044 :=
    @gAnbi2d (synWfun (synCcnv (.cv f))) (synWbr (.cv w) (.cv f) (.cv y))
      (synWa (.classMem (.cv y) (synCdm (synCcnv (.cv f))))
        (.classEq (synCfv (synCcnv (.cv f)) (.cv y)) (.cv w)))
      (synWbr (synCfv (synCcnv (.cv f)) (.cv x)) (.cv r) (.cv w)) p0043
  have p0045 :=
    @gExbidv (synWfun (synCcnv (.cv f)))
      (synWa (synWbr (synCfv (synCcnv (.cv f)) (.cv x)) (.cv r) (.cv w))
        (synWbr (.cv w) (.cv f) (.cv y)))
      (synWa (synWbr (synCfv (synCcnv (.cv f)) (.cv x)) (.cv r) (.cv w))
        (synWa (.classMem (.cv y) (synCdm (synCcnv (.cv f))))
          (.classEq (synCfv (synCcnv (.cv f)) (.cv y)) (.cv w))))
      w dv_cache_0020 p0044
  have p0046 :=
    @gAncom (synWbr (synCfv (synCcnv (.cv f)) (.cv x)) (.cv r) (.cv w))
      (synWa (.classMem (.cv y) (synCdm (synCcnv (.cv f))))
        (.classEq (synCfv (synCcnv (.cv f)) (.cv y)) (.cv w)))
  have p0047 :=
    @gAnass (.classMem (.cv y) (synCdm (synCcnv (.cv f))))
      (.classEq (synCfv (synCcnv (.cv f)) (.cv y)) (.cv w))
      (synWbr (synCfv (synCcnv (.cv f)) (.cv x)) (.cv r) (.cv w))
  have p0048 :=
    @gBitri
      (synWa (synWbr (synCfv (synCcnv (.cv f)) (.cv x)) (.cv r) (.cv w))
        (synWa (.classMem (.cv y) (synCdm (synCcnv (.cv f))))
          (.classEq (synCfv (synCcnv (.cv f)) (.cv y)) (.cv w))))
      (synWa (synWa (.classMem (.cv y) (synCdm (synCcnv (.cv f))))
          (.classEq (synCfv (synCcnv (.cv f)) (.cv y)) (.cv w)))
        (synWbr (synCfv (synCcnv (.cv f)) (.cv x)) (.cv r) (.cv w)))
      (synWa (.classMem (.cv y) (synCdm (synCcnv (.cv f))))
        (synWa (.classEq (synCfv (synCcnv (.cv f)) (.cv y)) (.cv w))
          (synWbr (synCfv (synCcnv (.cv f)) (.cv x)) (.cv r) (.cv w))))
      p0046 p0047
  have p0049 :=
    @gA1i
      (synWb (synWa (synWbr (synCfv (synCcnv (.cv f)) (.cv x)) (.cv r) (.cv w))
          (synWa (.classMem (.cv y) (synCdm (synCcnv (.cv f))))
            (.classEq (synCfv (synCcnv (.cv f)) (.cv y)) (.cv w))))
        (synWa (.classMem (.cv y) (synCdm (synCcnv (.cv f))))
          (synWa (.classEq (synCfv (synCcnv (.cv f)) (.cv y)) (.cv w))
            (synWbr (synCfv (synCcnv (.cv f)) (.cv x)) (.cv r) (.cv w)))))
      (synWfun (synCcnv (.cv f))) p0048
  have p0050 :=
    @gExbidv (synWfun (synCcnv (.cv f)))
      (synWa (synWbr (synCfv (synCcnv (.cv f)) (.cv x)) (.cv r) (.cv w))
        (synWa (.classMem (.cv y) (synCdm (synCcnv (.cv f))))
          (.classEq (synCfv (synCcnv (.cv f)) (.cv y)) (.cv w))))
      (synWa (.classMem (.cv y) (synCdm (synCcnv (.cv f))))
        (synWa (.classEq (synCfv (synCcnv (.cv f)) (.cv y)) (.cv w))
          (synWbr (synCfv (synCcnv (.cv f)) (.cv x)) (.cv r) (.cv w))))
      w dv_cache_0020 p0049
  have p0051 :=
    @gBitrd (synWfun (synCcnv (.cv f)))
      (synWex w (synWa (synWbr (synCfv (synCcnv (.cv f)) (.cv x)) (.cv r) (.cv w))
          (synWbr (.cv w) (.cv f) (.cv y))))
      (synWex w (synWa (synWbr (synCfv (synCcnv (.cv f)) (.cv x)) (.cv r) (.cv w))
          (synWa (.classMem (.cv y) (synCdm (synCcnv (.cv f))))
            (.classEq (synCfv (synCcnv (.cv f)) (.cv y)) (.cv w)))))
      (synWex w (synWa (.classMem (.cv y) (synCdm (synCcnv (.cv f))))
          (synWa (.classEq (synCfv (synCcnv (.cv f)) (.cv y)) (.cv w))
            (synWbr (synCfv (synCcnv (.cv f)) (.cv x)) (.cv r) (.cv w)))))
      p0045 p0050
  have p0052 :=
    @gN1942v (.classMem (.cv y) (synCdm (synCcnv (.cv f))))
      (synWa (.classEq (synCfv (synCcnv (.cv f)) (.cv y)) (.cv w))
        (synWbr (synCfv (synCcnv (.cv f)) (.cv x)) (.cv r) (.cv w)))
      w dv_cache_0021
  have p0053 :=
    @gA1i
      (synWb (synWex w (synWa (.classMem (.cv y) (synCdm (synCcnv (.cv f))))
            (synWa (.classEq (synCfv (synCcnv (.cv f)) (.cv y)) (.cv w))
              (synWbr (synCfv (synCcnv (.cv f)) (.cv x)) (.cv r) (.cv w)))))
        (synWa (.classMem (.cv y) (synCdm (synCcnv (.cv f)))) (synWex w
            (synWa (.classEq (synCfv (synCcnv (.cv f)) (.cv y)) (.cv w))
              (synWbr (synCfv (synCcnv (.cv f)) (.cv x)) (.cv r) (.cv w))))))
      (synWfun (synCcnv (.cv f))) p0052
  have p0054 :=
    @gBitrd (synWfun (synCcnv (.cv f)))
      (synWex w (synWa (synWbr (synCfv (synCcnv (.cv f)) (.cv x)) (.cv r) (.cv w))
          (synWbr (.cv w) (.cv f) (.cv y))))
      (synWex w (synWa (.classMem (.cv y) (synCdm (synCcnv (.cv f))))
          (synWa (.classEq (synCfv (synCcnv (.cv f)) (.cv y)) (.cv w))
            (synWbr (synCfv (synCcnv (.cv f)) (.cv x)) (.cv r) (.cv w)))))
      (synWa (.classMem (.cv y) (synCdm (synCcnv (.cv f)))) (synWex w
          (synWa (.classEq (synCfv (synCcnv (.cv f)) (.cv y)) (.cv w))
            (synWbr (synCfv (synCcnv (.cv f)) (.cv x)) (.cv r) (.cv w)))))
      p0051 p0053
  have p0055 := @gEqcom (synCfv (synCcnv (.cv f)) (.cv y)) (.cv w)
  have p0056 :=
    @gAnbi1i (.classEq (synCfv (synCcnv (.cv f)) (.cv y)) (.cv w))
      (.classEq (.cv w) (synCfv (synCcnv (.cv f)) (.cv y)))
      (synWbr (synCfv (synCcnv (.cv f)) (.cv x)) (.cv r) (.cv w)) p0055
  have p0057 :=
    @gExbii
      (synWa (.classEq (synCfv (synCcnv (.cv f)) (.cv y)) (.cv w))
        (synWbr (synCfv (synCcnv (.cv f)) (.cv x)) (.cv r) (.cv w)))
      (synWa (.classEq (.cv w) (synCfv (synCcnv (.cv f)) (.cv y)))
        (synWbr (synCfv (synCcnv (.cv f)) (.cv x)) (.cv r) (.cv w)))
      w p0056
  have p0058 := @gFvex (.cv y) (synCcnv (.cv f))
  have p0059 :=
    @gBreq2 (.cv w) (synCfv (synCcnv (.cv f)) (.cv y))
      (synCfv (synCcnv (.cv f)) (.cv x)) (.cv r)
  have p0060 :=
    @gCeqsexv (synWbr (synCfv (synCcnv (.cv f)) (.cv x)) (.cv r) (.cv w))
      (synWbr (synCfv (synCcnv (.cv f)) (.cv x)) (.cv r)
        (synCfv (synCcnv (.cv f)) (.cv y)))
      w (synCfv (synCcnv (.cv f)) (.cv y)) dv_cache_0022 dv_cache_0023 p0058 p0059
  have p0061 :=
    @gBitri
      (synWex w (synWa (.classEq (synCfv (synCcnv (.cv f)) (.cv y)) (.cv w))
          (synWbr (synCfv (synCcnv (.cv f)) (.cv x)) (.cv r) (.cv w))))
      (synWex w (synWa (.classEq (.cv w) (synCfv (synCcnv (.cv f)) (.cv y)))
          (synWbr (synCfv (synCcnv (.cv f)) (.cv x)) (.cv r) (.cv w))))
      (synWbr (synCfv (synCcnv (.cv f)) (.cv x)) (.cv r)
        (synCfv (synCcnv (.cv f)) (.cv y)))
      p0057 p0060
  have p0062 :=
    @gAnbi2i
      (synWex w (synWa (.classEq (synCfv (synCcnv (.cv f)) (.cv y)) (.cv w))
          (synWbr (synCfv (synCcnv (.cv f)) (.cv x)) (.cv r) (.cv w))))
      (synWbr (synCfv (synCcnv (.cv f)) (.cv x)) (.cv r)
        (synCfv (synCcnv (.cv f)) (.cv y)))
      (.classMem (.cv y) (synCdm (synCcnv (.cv f)))) p0061
  have p0063 :=
    @gA1i
      (synWb (synWa (.classMem (.cv y) (synCdm (synCcnv (.cv f)))) (synWex w
            (synWa (.classEq (synCfv (synCcnv (.cv f)) (.cv y)) (.cv w))
              (synWbr (synCfv (synCcnv (.cv f)) (.cv x)) (.cv r) (.cv w)))))
        (synWa (.classMem (.cv y) (synCdm (synCcnv (.cv f))))
          (synWbr (synCfv (synCcnv (.cv f)) (.cv x)) (.cv r)
            (synCfv (synCcnv (.cv f)) (.cv y)))))
      (synWfun (synCcnv (.cv f))) p0062
  have p0064 :=
    @gBitrd (synWfun (synCcnv (.cv f)))
      (synWex w (synWa (synWbr (synCfv (synCcnv (.cv f)) (.cv x)) (.cv r) (.cv w))
          (synWbr (.cv w) (.cv f) (.cv y))))
      (synWa (.classMem (.cv y) (synCdm (synCcnv (.cv f)))) (synWex w
          (synWa (.classEq (synCfv (synCcnv (.cv f)) (.cv y)) (.cv w))
            (synWbr (synCfv (synCcnv (.cv f)) (.cv x)) (.cv r) (.cv w)))))
      (synWa (.classMem (.cv y) (synCdm (synCcnv (.cv f))))
        (synWbr (synCfv (synCcnv (.cv f)) (.cv x)) (.cv r)
          (synCfv (synCcnv (.cv f)) (.cv y))))
      p0054 p0063
  have p0066 := @gEleq2i (synCrn (.cv f)) (synCdm (synCcnv (.cv f))) (.cv y) p0030
  have p0067 :=
    @gBicomi (.classMem (.cv y) (synCrn (.cv f)))
      (.classMem (.cv y) (synCdm (synCcnv (.cv f)))) p0066
  have p0068 :=
    @gAnbi1i (.classMem (.cv y) (synCdm (synCcnv (.cv f))))
      (.classMem (.cv y) (synCrn (.cv f)))
      (synWbr (synCfv (synCcnv (.cv f)) (.cv x)) (.cv r)
        (synCfv (synCcnv (.cv f)) (.cv y)))
      p0067
  have p0069 :=
    @gA1i
      (synWb (synWa (.classMem (.cv y) (synCdm (synCcnv (.cv f))))
          (synWbr (synCfv (synCcnv (.cv f)) (.cv x)) (.cv r)
            (synCfv (synCcnv (.cv f)) (.cv y)))) (synWa (.classMem (.cv y) (synCrn (.cv f)))
          (synWbr (synCfv (synCcnv (.cv f)) (.cv x)) (.cv r)
            (synCfv (synCcnv (.cv f)) (.cv y)))))
      (synWfun (synCcnv (.cv f))) p0068
  have p0070 :=
    @gBitrd (synWfun (synCcnv (.cv f)))
      (synWex w (synWa (synWbr (synCfv (synCcnv (.cv f)) (.cv x)) (.cv r) (.cv w))
          (synWbr (.cv w) (.cv f) (.cv y))))
      (synWa (.classMem (.cv y) (synCdm (synCcnv (.cv f))))
        (synWbr (synCfv (synCcnv (.cv f)) (.cv x)) (.cv r)
          (synCfv (synCcnv (.cv f)) (.cv y))))
      (synWa (.classMem (.cv y) (synCrn (.cv f)))
        (synWbr (synCfv (synCcnv (.cv f)) (.cv x)) (.cv r)
          (synCfv (synCcnv (.cv f)) (.cv y))))
      p0064 p0069
  have p0071 :=
    @gBitrd (synWfun (synCcnv (.cv f)))
      (synWbr (synCfv (synCcnv (.cv f)) (.cv x)) (synCcom (.cv f) (.cv r)) (.cv y))
      (synWex w (synWa (synWbr (synCfv (synCcnv (.cv f)) (.cv x)) (.cv r) (.cv w))
          (synWbr (.cv w) (.cv f) (.cv y))))
      (synWa (.classMem (.cv y) (synCrn (.cv f)))
        (synWbr (synCfv (synCcnv (.cv f)) (.cv x)) (.cv r)
          (synCfv (synCcnv (.cv f)) (.cv y))))
      p0038 p0070
  have p0072 :=
    @gAnbi2d (synWfun (synCcnv (.cv f)))
      (synWbr (synCfv (synCcnv (.cv f)) (.cv x)) (synCcom (.cv f) (.cv r)) (.cv y))
      (synWa (.classMem (.cv y) (synCrn (.cv f)))
        (synWbr (synCfv (synCcnv (.cv f)) (.cv x)) (.cv r)
          (synCfv (synCcnv (.cv f)) (.cv y))))
      (.classMem (.cv x) (synCrn (.cv f))) p0071
  have p0073 :=
    @gBitrd (synWfun (synCcnv (.cv f)))
      (synWbr (.cv x) (synCcom (synCcom (.cv f) (.cv r)) (synCcnv (.cv f))) (.cv y))
      (synWa (.classMem (.cv x) (synCrn (.cv f)))
        (synWbr (synCfv (synCcnv (.cv f)) (.cv x)) (synCcom (.cv f) (.cv r)) (.cv y)))
      (synWa (.classMem (.cv x) (synCrn (.cv f)))
        (synWa (.classMem (.cv y) (synCrn (.cv f)))
          (synWbr (synCfv (synCcnv (.cv f)) (.cv x)) (.cv r)
            (synCfv (synCcnv (.cv f)) (.cv y)))))
      p0036 p0072
  have p0074 :=
    @gAnass (.classMem (.cv x) (synCrn (.cv f))) (.classMem (.cv y) (synCrn (.cv f)))
      (synWbr (synCfv (synCcnv (.cv f)) (.cv x)) (.cv r)
        (synCfv (synCcnv (.cv f)) (.cv y)))
  have p0075 :=
    @gBicomi
      (synWa (synWa (.classMem (.cv x) (synCrn (.cv f)))
          (.classMem (.cv y) (synCrn (.cv f))))
        (synWbr (synCfv (synCcnv (.cv f)) (.cv x)) (.cv r)
          (synCfv (synCcnv (.cv f)) (.cv y))))
      (synWa (.classMem (.cv x) (synCrn (.cv f)))
        (synWa (.classMem (.cv y) (synCrn (.cv f)))
          (synWbr (synCfv (synCcnv (.cv f)) (.cv x)) (.cv r)
            (synCfv (synCcnv (.cv f)) (.cv y)))))
      p0074
  have p0076 :=
    @gA1i
      (synWb (synWa (.classMem (.cv x) (synCrn (.cv f)))
          (synWa (.classMem (.cv y) (synCrn (.cv f)))
            (synWbr (synCfv (synCcnv (.cv f)) (.cv x)) (.cv r)
              (synCfv (synCcnv (.cv f)) (.cv y))))) (synWa
          (synWa (.classMem (.cv x) (synCrn (.cv f))) (.classMem (.cv y) (synCrn (.cv f))))
          (synWbr (synCfv (synCcnv (.cv f)) (.cv x)) (.cv r)
            (synCfv (synCcnv (.cv f)) (.cv y)))))
      (synWfun (synCcnv (.cv f))) p0075
  have p0077 :=
    @gBitrd (synWfun (synCcnv (.cv f)))
      (synWbr (.cv x) (synCcom (synCcom (.cv f) (.cv r)) (synCcnv (.cv f))) (.cv y))
      (synWa (.classMem (.cv x) (synCrn (.cv f)))
        (synWa (.classMem (.cv y) (synCrn (.cv f)))
          (synWbr (synCfv (synCcnv (.cv f)) (.cv x)) (.cv r)
            (synCfv (synCcnv (.cv f)) (.cv y)))))
      (synWa (synWa (.classMem (.cv x) (synCrn (.cv f)))
          (.classMem (.cv y) (synCrn (.cv f))))
        (synWbr (synCfv (synCcnv (.cv f)) (.cv x)) (.cv r)
          (synCfv (synCcnv (.cv f)) (.cv y))))
      p0073 p0076
  have p0078 := @gVex x
  have p0079 := @gVex y
  have p0080 := @gSimpl (.classEq (.cv z) (.cv x)) (.classEq (.cv w) (.cv y))
  have p0081 :=
    @gEleq1d (synWa (.classEq (.cv z) (.cv x)) (.classEq (.cv w) (.cv y))) (.cv z)
      (.cv x) (synCrn (.cv f)) p0080
  have p0082 := @gSimpr (.classEq (.cv z) (.cv x)) (.classEq (.cv w) (.cv y))
  have p0083 :=
    @gEleq1d (synWa (.classEq (.cv z) (.cv x)) (.classEq (.cv w) (.cv y))) (.cv w)
      (.cv y) (synCrn (.cv f)) p0082
  have p0084 :=
    @gAnbi12d (synWa (.classEq (.cv z) (.cv x)) (.classEq (.cv w) (.cv y)))
      (.classMem (.cv z) (synCrn (.cv f))) (.classMem (.cv x) (synCrn (.cv f)))
      (.classMem (.cv w) (synCrn (.cv f))) (.classMem (.cv y) (synCrn (.cv f))) p0081
      p0083
  have p0086 :=
    @gFveq2d (synWa (.classEq (.cv z) (.cv x)) (.classEq (.cv w) (.cv y))) (.cv z)
      (.cv x) (synCcnv (.cv f)) p0080
  have p0088 :=
    @gFveq2d (synWa (.classEq (.cv z) (.cv x)) (.classEq (.cv w) (.cv y))) (.cv w)
      (.cv y) (synCcnv (.cv f)) p0082
  have p0089 :=
    @gBreq12d (synWa (.classEq (.cv z) (.cv x)) (.classEq (.cv w) (.cv y)))
      (synCfv (synCcnv (.cv f)) (.cv z)) (synCfv (synCcnv (.cv f)) (.cv x))
      (synCfv (synCcnv (.cv f)) (.cv w)) (synCfv (synCcnv (.cv f)) (.cv y)) (.cv r)
      p0086 p0088
  have p0090 :=
    @gAnbi12d (synWa (.classEq (.cv z) (.cv x)) (.classEq (.cv w) (.cv y)))
      (synWa (.classMem (.cv z) (synCrn (.cv f))) (.classMem (.cv w) (synCrn (.cv f))))
      (synWa (.classMem (.cv x) (synCrn (.cv f))) (.classMem (.cv y) (synCrn (.cv f))))
      (synWbr (synCfv (synCcnv (.cv f)) (.cv z)) (.cv r)
        (synCfv (synCcnv (.cv f)) (.cv w)))
      (synWbr (synCfv (synCcnv (.cv f)) (.cv x)) (.cv r)
        (synCfv (synCcnv (.cv f)) (.cv y)))
      p0084 p0089
  have p0092 :=
    @gBraba
      (synWa (synWa (.classMem (.cv z) (synCrn (.cv f)))
          (.classMem (.cv w) (synCrn (.cv f))))
        (synWbr (synCfv (synCcnv (.cv f)) (.cv z)) (.cv r)
          (synCfv (synCcnv (.cv f)) (.cv w))))
      (synWa (synWa (.classMem (.cv x) (synCrn (.cv f)))
          (.classMem (.cv y) (synCrn (.cv f))))
        (synWbr (synCfv (synCcnv (.cv f)) (.cv x)) (.cv r)
          (synCfv (synCcnv (.cv f)) (.cv y))))
      z w (.cv x) (.cv y)
      (synCopab z w (synWa (synWa (.classMem (.cv z) (synCrn (.cv f)))
            (.classMem (.cv w) (synCrn (.cv f))))
          (synWbr (synCfv (synCcnv (.cv f)) (.cv z)) (.cv r)
            (synCfv (synCcnv (.cv f)) (.cv w)))))
      dv_cache_0010 dv_cache_0024 dv_cache_0011 dv_cache_0019 dv_cache_0025 dv_cache_0026
      dv_cache_0009 p0078 p0079 p0090 p0000
  have p0093 :=
    @gBicomi
      (synWbr (.cv x) (synCopab z w (synWa (synWa (.classMem (.cv z) (synCrn (.cv f)))
              (.classMem (.cv w) (synCrn (.cv f))))
            (synWbr (synCfv (synCcnv (.cv f)) (.cv z)) (.cv r)
              (synCfv (synCcnv (.cv f)) (.cv w))))) (.cv y))
      (synWa (synWa (.classMem (.cv x) (synCrn (.cv f)))
          (.classMem (.cv y) (synCrn (.cv f))))
        (synWbr (synCfv (synCcnv (.cv f)) (.cv x)) (.cv r)
          (synCfv (synCcnv (.cv f)) (.cv y))))
      p0092
  have p0094 :=
    @gA1i
      (synWb (synWa (synWa (.classMem (.cv x) (synCrn (.cv f)))
            (.classMem (.cv y) (synCrn (.cv f))))
          (synWbr (synCfv (synCcnv (.cv f)) (.cv x)) (.cv r)
            (synCfv (synCcnv (.cv f)) (.cv y)))) (synWbr (.cv x) (synCopab z w (synWa
              (synWa (.classMem (.cv z) (synCrn (.cv f)))
                (.classMem (.cv w) (synCrn (.cv f))))
              (synWbr (synCfv (synCcnv (.cv f)) (.cv z)) (.cv r)
                (synCfv (synCcnv (.cv f)) (.cv w))))) (.cv y)))
      (synWfun (synCcnv (.cv f))) p0093
  have p0095 :=
    @gBitrd (synWfun (synCcnv (.cv f)))
      (synWbr (.cv x) (synCcom (synCcom (.cv f) (.cv r)) (synCcnv (.cv f))) (.cv y))
      (synWa (synWa (.classMem (.cv x) (synCrn (.cv f)))
          (.classMem (.cv y) (synCrn (.cv f))))
        (synWbr (synCfv (synCcnv (.cv f)) (.cv x)) (.cv r)
          (synCfv (synCcnv (.cv f)) (.cv y))))
      (synWbr (.cv x) (synCopab z w (synWa (synWa (.classMem (.cv z) (synCrn (.cv f)))
              (.classMem (.cv w) (synCrn (.cv f))))
            (synWbr (synCfv (synCcnv (.cv f)) (.cv z)) (.cv r)
              (synCfv (synCcnv (.cv f)) (.cv w))))) (.cv y))
      p0077 p0094
  have p0096 :=
    @gBitrd (synWfun (synCcnv (.cv f)))
      (.classMem (synCop (.cv x) (.cv y))
        (synCcom (synCcom (.cv f) (.cv r)) (synCcnv (.cv f))))
      (synWbr (.cv x) (synCcom (synCcom (.cv f) (.cv r)) (synCcnv (.cv f))) (.cv y))
      (synWbr (.cv x) (synCopab z w (synWa (synWa (.classMem (.cv z) (synCrn (.cv f)))
              (.classMem (.cv w) (synCrn (.cv f))))
            (synWbr (synCfv (synCcnv (.cv f)) (.cv z)) (.cv r)
              (synCfv (synCcnv (.cv f)) (.cv w))))) (.cv y))
      p0007 p0095
  have p0097 :=
    (Nominal.biimpRefl (synWbr (.cv x) (synCopab z w (synWa
            (synWa (.classMem (.cv z) (synCrn (.cv f))) (.classMem (.cv w) (synCrn (.cv f))))
            (synWbr (synCfv (synCcnv (.cv f)) (.cv z)) (.cv r)
              (synCfv (synCcnv (.cv f)) (.cv w))))) (.cv y)))
  have p0098 :=
    @gA1i
      (synWb (synWbr (.cv x) (synCopab z w (synWa
              (synWa (.classMem (.cv z) (synCrn (.cv f)))
                (.classMem (.cv w) (synCrn (.cv f))))
              (synWbr (synCfv (synCcnv (.cv f)) (.cv z)) (.cv r)
                (synCfv (synCcnv (.cv f)) (.cv w))))) (.cv y))
        (.classMem (synCop (.cv x) (.cv y)) (synCopab z w (synWa
              (synWa (.classMem (.cv z) (synCrn (.cv f)))
                (.classMem (.cv w) (synCrn (.cv f))))
              (synWbr (synCfv (synCcnv (.cv f)) (.cv z)) (.cv r)
                (synCfv (synCcnv (.cv f)) (.cv w)))))))
      (synWfun (synCcnv (.cv f))) p0097
  have p0099 :=
    @gBitrd (synWfun (synCcnv (.cv f)))
      (.classMem (synCop (.cv x) (.cv y))
        (synCcom (synCcom (.cv f) (.cv r)) (synCcnv (.cv f))))
      (synWbr (.cv x) (synCopab z w (synWa (synWa (.classMem (.cv z) (synCrn (.cv f)))
              (.classMem (.cv w) (synCrn (.cv f))))
            (synWbr (synCfv (synCcnv (.cv f)) (.cv z)) (.cv r)
              (synCfv (synCcnv (.cv f)) (.cv w))))) (.cv y))
      (.classMem (synCop (.cv x) (.cv y)) (synCopab z w (synWa
            (synWa (.classMem (.cv z) (synCrn (.cv f))) (.classMem (.cv w) (synCrn (.cv f))))
            (synWbr (synCfv (synCcnv (.cv f)) (.cv z)) (.cv r)
              (synCfv (synCcnv (.cv f)) (.cv w))))))
      p0096 p0098
  have p0100 :=
    @gEqrelrdv (synWfun (synCcnv (.cv f))) x y
      (synCcom (synCcom (.cv f) (.cv r)) (synCcnv (.cv f)))
      (synCopab z w (synWa (synWa (.classMem (.cv z) (synCrn (.cv f)))
            (.classMem (.cv w) (synCrn (.cv f))))
          (synWbr (synCfv (synCcnv (.cv f)) (.cv z)) (.cv r)
            (synCfv (synCcnv (.cv f)) (.cv w)))))
      dv_cache_0027 dv_cache_0028 dv_cache_0029 dv_cache_0030 dv_cache_0031 dv_cache_0032
      dv_cache_0033 p0099
  have p0101 :=
    @gSyl (synWf1o (.cv f) (synCdm (.cv f)) (synCrn (.cv f)))
      (synWfun (synCcnv (.cv f)))
      (.classEq (synCcom (synCcom (.cv f) (.cv r)) (synCcnv (.cv f))) (synCopab z w (synWa
            (synWa (.classMem (.cv z) (synCrn (.cv f))) (.classMem (.cv w) (synCrn (.cv f))))
            (synWbr (synCfv (synCcnv (.cv f)) (.cv z)) (.cv r)
              (synCfv (synCcnv (.cv f)) (.cv w))))))
      p0004 p0100
  have p0102 :=
    @gEqcomd (synWf1o (.cv f) (synCdm (.cv f)) (synCrn (.cv f)))
      (synCcom (synCcom (.cv f) (.cv r)) (synCcnv (.cv f)))
      (synCopab z w (synWa (synWa (.classMem (.cv z) (synCrn (.cv f)))
            (.classMem (.cv w) (synCrn (.cv f))))
          (synWbr (synCfv (synCcnv (.cv f)) (.cv z)) (.cv r)
            (synCfv (synCcnv (.cv f)) (.cv w)))))
      p0101
  have p0103 :=
    @gIsoeq3 (synCdm (.cv f)) (synCrn (.cv f)) (.cv r)
      (synCopab z w (synWa (synWa (.classMem (.cv z) (synCrn (.cv f)))
            (.classMem (.cv w) (synCrn (.cv f))))
          (synWbr (synCfv (synCcnv (.cv f)) (.cv z)) (.cv r)
            (synCfv (synCcnv (.cv f)) (.cv w)))))
      (synCcom (synCcom (.cv f) (.cv r)) (synCcnv (.cv f))) (.cv f)
  have p0104 :=
    @gSyl (synWf1o (.cv f) (synCdm (.cv f)) (synCrn (.cv f)))
      (.classEq (synCopab z w (synWa (synWa (.classMem (.cv z) (synCrn (.cv f)))
              (.classMem (.cv w) (synCrn (.cv f))))
            (synWbr (synCfv (synCcnv (.cv f)) (.cv z)) (.cv r)
              (synCfv (synCcnv (.cv f)) (.cv w)))))
        (synCcom (synCcom (.cv f) (.cv r)) (synCcnv (.cv f))))
      (synWb (synWiso (.cv f) (.cv r) (synCopab z w (synWa
              (synWa (.classMem (.cv z) (synCrn (.cv f)))
                (.classMem (.cv w) (synCrn (.cv f))))
              (synWbr (synCfv (synCcnv (.cv f)) (.cv z)) (.cv r)
                (synCfv (synCcnv (.cv f)) (.cv w))))) (synCdm (.cv f)) (synCrn (.cv f)))
        (synWiso (.cv f) (.cv r) (synCcom (synCcom (.cv f) (.cv r)) (synCcnv (.cv f)))
          (synCdm (.cv f)) (synCrn (.cv f))))
      p0102 p0103
  have p0105 :=
    @gMpbid (synWf1o (.cv f) (synCdm (.cv f)) (synCrn (.cv f)))
      (synWiso (.cv f) (.cv r) (synCopab z w (synWa
            (synWa (.classMem (.cv z) (synCrn (.cv f))) (.classMem (.cv w) (synCrn (.cv f))))
            (synWbr (synCfv (synCcnv (.cv f)) (.cv z)) (.cv r)
              (synCfv (synCcnv (.cv f)) (.cv w))))) (synCdm (.cv f)) (synCrn (.cv f)))
      (synWiso (.cv f) (.cv r) (synCcom (synCcom (.cv f) (.cv r)) (synCcnv (.cv f)))
        (synCdm (.cv f)) (synCrn (.cv f)))
      p0001 p0104
  have p0106 :=
    @gIsof1o (synCdm (.cv f)) (synCrn (.cv f)) (.cv r)
      (synCcom (synCcom (.cv f) (.cv r)) (synCcnv (.cv f))) (.cv f)
  have p0107 :=
    @gImpbii (synWf1o (.cv f) (synCdm (.cv f)) (synCrn (.cv f)))
      (synWiso (.cv f) (.cv r) (synCcom (synCcom (.cv f) (.cv r)) (synCcnv (.cv f)))
        (synCdm (.cv f)) (synCrn (.cv f)))
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

/-- Checked nominal proof certificate identified upstream as `g_isotargettransport`. -/
@[expose]
noncomputable def gIsotargettransport (A : Class) (B : Class) (S : Class) (f : Var)
    (r : Var) (_dv_A_f : f ∉ A.fv) (_dv_B_f : f ∉ B.fv) (_dv_S_f : f ∉ S.fv)
    (_dv_f_r : f ≠ r) :
    Nominal.NPrf
      (.imp (synWa (synWiso (.cv f) (.cv r) S A B) (synWss S (synCxp B B)))
        (.classEq S (synCcom (synCcom (.cv f) (.cv r)) (synCcnv (.cv f))))) :=
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
    x ∉ ((synCcom (synCcom (.cv f) (.cv r)) (synCcnv (.cv f)))).fv :=
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
    y ∉ ((synCcom (synCcom (.cv f) (.cv r)) (synCcnv (.cv f)))).fv :=
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
    x ∉ ((synWa (synWiso (.cv f) (.cv r) S A B) (synWss S (synCxp B B)))).fv :=
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
    y ∉ ((synWa (synWiso (.cv f) (.cv r) S A B) (synWss S (synCxp B B)))).fv :=
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
  have p0000 := @gSimpr (synWiso (.cv f) (.cv r) S A B) (synWss S (synCxp B B))
  have p0001 :=
    @gSsbrd (synWa (synWiso (.cv f) (.cv r) S A B) (synWss S (synCxp B B))) S
      (synCxp B B) (.cv x) (.cv y) p0000
  have p0002 := @gBrxp (.cv x) (.cv y) B B
  have p0003 :=
    @gA1i
      (synWb (synWbr (.cv x) (synCxp B B) (.cv y))
        (synWa (.classMem (.cv x) B) (.classMem (.cv y) B)))
      (synWa (synWiso (.cv f) (.cv r) S A B) (synWss S (synCxp B B))) p0002
  have p0004 :=
    @gSylibd (synWa (synWiso (.cv f) (.cv r) S A B) (synWss S (synCxp B B)))
      (synWbr (.cv x) S (.cv y)) (synWbr (.cv x) (synCxp B B) (.cv y))
      (synWa (.classMem (.cv x) B) (.classMem (.cv y) B)) p0001 p0003
  have p0010 := @gSimpl (synWiso (.cv f) (.cv r) S A B) (synWss S (synCxp B B))
  have p0011 :=
    @gAdantr (synWa (synWiso (.cv f) (.cv r) S A B) (synWss S (synCxp B B)))
      (synWiso (.cv f) (.cv r) S A B)
      (synWa (.classMem (.cv x) B) (.classMem (.cv y) B)) p0010
  have p0012 :=
    @gSimpr (synWa (synWiso (.cv f) (.cv r) S A B) (synWss S (synCxp B B)))
      (synWa (.classMem (.cv x) B) (.classMem (.cv y) B))
  have p0013 :=
    @gJca
      (synWa (synWa (synWiso (.cv f) (.cv r) S A B) (synWss S (synCxp B B)))
        (synWa (.classMem (.cv x) B) (.classMem (.cv y) B)))
      (synWiso (.cv f) (.cv r) S A B)
      (synWa (.classMem (.cv x) B) (.classMem (.cv y) B)) p0011 p0012
  have p0014 := @gIsocnv A B (.cv r) S (.cv f)
  have p0015 :=
    @gAnim1i (synWiso (.cv f) (.cv r) S A B) (synWiso (synCcnv (.cv f)) S (.cv r) B A)
      (synWa (.classMem (.cv x) B) (.classMem (.cv y) B)) p0014
  have p0016 := @gIsorel B A (.cv x) (.cv y) S (.cv r) (synCcnv (.cv f))
  have p0017 :=
    @gSyl
      (synWa (synWiso (.cv f) (.cv r) S A B)
        (synWa (.classMem (.cv x) B) (.classMem (.cv y) B)))
      (synWa (synWiso (synCcnv (.cv f)) S (.cv r) B A)
        (synWa (.classMem (.cv x) B) (.classMem (.cv y) B)))
      (synWb (synWbr (.cv x) S (.cv y)) (synWbr (synCfv (synCcnv (.cv f)) (.cv x)) (.cv r)
          (synCfv (synCcnv (.cv f)) (.cv y))))
      p0015 p0016
  have p0018 :=
    @gSyl
      (synWa (synWa (synWiso (.cv f) (.cv r) S A B) (synWss S (synCxp B B)))
        (synWa (.classMem (.cv x) B) (.classMem (.cv y) B)))
      (synWa (synWiso (.cv f) (.cv r) S A B)
        (synWa (.classMem (.cv x) B) (.classMem (.cv y) B)))
      (synWb (synWbr (.cv x) S (.cv y)) (synWbr (synCfv (synCcnv (.cv f)) (.cv x)) (.cv r)
          (synCfv (synCcnv (.cv f)) (.cv y))))
      p0013 p0017
  have p0019 :=
    @gEx (synWa (synWiso (.cv f) (.cv r) S A B) (synWss S (synCxp B B)))
      (synWa (.classMem (.cv x) B) (.classMem (.cv y) B))
      (synWb (synWbr (.cv x) S (.cv y)) (synWbr (synCfv (synCcnv (.cv f)) (.cv x)) (.cv r)
          (synCfv (synCcnv (.cv f)) (.cv y))))
      p0018
  have p0020 :=
    @gBi1 (synWbr (.cv x) S (.cv y))
      (synWbr (synCfv (synCcnv (.cv f)) (.cv x)) (.cv r)
        (synCfv (synCcnv (.cv f)) (.cv y)))
  have p0021 :=
    @gSyl6 (synWa (synWiso (.cv f) (.cv r) S A B) (synWss S (synCxp B B)))
      (synWa (.classMem (.cv x) B) (.classMem (.cv y) B))
      (synWb (synWbr (.cv x) S (.cv y)) (synWbr (synCfv (synCcnv (.cv f)) (.cv x)) (.cv r)
          (synCfv (synCcnv (.cv f)) (.cv y))))
      (.imp (synWbr (.cv x) S (.cv y)) (synWbr (synCfv (synCcnv (.cv f)) (.cv x)) (.cv r)
          (synCfv (synCcnv (.cv f)) (.cv y))))
      p0019 p0020
  have p0022 :=
    @gCom23 (synWa (synWiso (.cv f) (.cv r) S A B) (synWss S (synCxp B B)))
      (synWa (.classMem (.cv x) B) (.classMem (.cv y) B)) (synWbr (.cv x) S (.cv y))
      (synWbr (synCfv (synCcnv (.cv f)) (.cv x)) (.cv r)
        (synCfv (synCcnv (.cv f)) (.cv y)))
      p0021
  have p0023 :=
    @gMpdd (synWa (synWiso (.cv f) (.cv r) S A B) (synWss S (synCxp B B)))
      (synWbr (.cv x) S (.cv y)) (synWa (.classMem (.cv x) B) (.classMem (.cv y) B))
      (synWbr (synCfv (synCcnv (.cv f)) (.cv x)) (.cv r)
        (synCfv (synCcnv (.cv f)) (.cv y)))
      p0004 p0022
  have p0024 :=
    @gJcad (synWa (synWiso (.cv f) (.cv r) S A B) (synWss S (synCxp B B)))
      (synWbr (.cv x) S (.cv y)) (synWa (.classMem (.cv x) B) (.classMem (.cv y) B))
      (synWbr (synCfv (synCcnv (.cv f)) (.cv x)) (.cv r)
        (synCfv (synCcnv (.cv f)) (.cv y)))
      p0004 p0023
  have p0035 :=
    @gBi2 (synWbr (.cv x) S (.cv y))
      (synWbr (synCfv (synCcnv (.cv f)) (.cv x)) (.cv r)
        (synCfv (synCcnv (.cv f)) (.cv y)))
  have p0036 :=
    @gSyl6 (synWa (synWiso (.cv f) (.cv r) S A B) (synWss S (synCxp B B)))
      (synWa (.classMem (.cv x) B) (.classMem (.cv y) B))
      (synWb (synWbr (.cv x) S (.cv y)) (synWbr (synCfv (synCcnv (.cv f)) (.cv x)) (.cv r)
          (synCfv (synCcnv (.cv f)) (.cv y))))
      (.imp (synWbr (synCfv (synCcnv (.cv f)) (.cv x)) (.cv r)
          (synCfv (synCcnv (.cv f)) (.cv y))) (synWbr (.cv x) S (.cv y)))
      p0019 p0035
  have p0037 :=
    @gImp3a (synWa (synWiso (.cv f) (.cv r) S A B) (synWss S (synCxp B B)))
      (synWa (.classMem (.cv x) B) (.classMem (.cv y) B))
      (synWbr (synCfv (synCcnv (.cv f)) (.cv x)) (.cv r)
        (synCfv (synCcnv (.cv f)) (.cv y)))
      (synWbr (.cv x) S (.cv y)) p0036
  have p0038 :=
    @gImpbid (synWa (synWiso (.cv f) (.cv r) S A B) (synWss S (synCxp B B)))
      (synWbr (.cv x) S (.cv y))
      (synWa (synWa (.classMem (.cv x) B) (.classMem (.cv y) B))
        (synWbr (synCfv (synCcnv (.cv f)) (.cv x)) (.cv r)
          (synCfv (synCcnv (.cv f)) (.cv y))))
      p0024 p0037
  have p0040 := @gIsof1o A B (.cv r) S (.cv f)
  have p0041 :=
    @gSyl (synWa (synWiso (.cv f) (.cv r) S A B) (synWss S (synCxp B B)))
      (synWiso (.cv f) (.cv r) S A B) (synWf1o (.cv f) A B) p0010 p0040
  have p0042 := @gF1ocnv A B (.cv f)
  have p0043 :=
    @gSyl (synWa (synWiso (.cv f) (.cv r) S A B) (synWss S (synCxp B B)))
      (synWf1o (.cv f) A B) (synWf1o (synCcnv (.cv f)) B A) p0041 p0042
  have p0044 := @gF1ofun B A (synCcnv (.cv f))
  have p0045 :=
    @gSyl (synWa (synWiso (.cv f) (.cv r) S A B) (synWss S (synCxp B B)))
      (synWf1o (synCcnv (.cv f)) B A) (synWfun (synCcnv (.cv f))) p0043 p0044
  have p0046 := @gHwtrnbrd x y f r dv_cache_0001 dv_cache_0002
  have p0047 :=
    @gSyl (synWa (synWiso (.cv f) (.cv r) S A B) (synWss S (synCxp B B)))
      (synWfun (synCcnv (.cv f)))
      (synWb (synWbr (.cv x) (synCcom (synCcom (.cv f) (.cv r)) (synCcnv (.cv f))) (.cv y))
        (synWa (synWa (.classMem (.cv x) (synCrn (.cv f)))
            (.classMem (.cv y) (synCrn (.cv f))))
          (synWbr (synCfv (synCcnv (.cv f)) (.cv x)) (.cv r)
            (synCfv (synCcnv (.cv f)) (.cv y)))))
      p0045 p0046
  have p0051 := @gF1ofo A B (.cv f)
  have p0052 :=
    @gSyl (synWa (synWiso (.cv f) (.cv r) S A B) (synWss S (synCxp B B)))
      (synWf1o (.cv f) A B) (synWfo (.cv f) A B) p0041 p0051
  have p0053 := @gForn A B (.cv f)
  have p0054 :=
    @gSyl (synWa (synWiso (.cv f) (.cv r) S A B) (synWss S (synCxp B B)))
      (synWfo (.cv f) A B) (.classEq (synCrn (.cv f)) B) p0052 p0053
  have p0055 :=
    @gEleq2d (synWa (synWiso (.cv f) (.cv r) S A B) (synWss S (synCxp B B)))
      (synCrn (.cv f)) B (.cv x) p0054
  have p0063 :=
    @gEleq2d (synWa (synWiso (.cv f) (.cv r) S A B) (synWss S (synCxp B B)))
      (synCrn (.cv f)) B (.cv y) p0054
  have p0064 :=
    @gAnbi12d (synWa (synWiso (.cv f) (.cv r) S A B) (synWss S (synCxp B B)))
      (.classMem (.cv x) (synCrn (.cv f))) (.classMem (.cv x) B)
      (.classMem (.cv y) (synCrn (.cv f))) (.classMem (.cv y) B) p0055 p0063
  have p0065 :=
    @gAnbi1d (synWa (synWiso (.cv f) (.cv r) S A B) (synWss S (synCxp B B)))
      (synWa (.classMem (.cv x) (synCrn (.cv f))) (.classMem (.cv y) (synCrn (.cv f))))
      (synWa (.classMem (.cv x) B) (.classMem (.cv y) B))
      (synWbr (synCfv (synCcnv (.cv f)) (.cv x)) (.cv r)
        (synCfv (synCcnv (.cv f)) (.cv y)))
      p0064
  have p0066 :=
    @gBitrd (synWa (synWiso (.cv f) (.cv r) S A B) (synWss S (synCxp B B)))
      (synWbr (.cv x) (synCcom (synCcom (.cv f) (.cv r)) (synCcnv (.cv f))) (.cv y))
      (synWa (synWa (.classMem (.cv x) (synCrn (.cv f)))
          (.classMem (.cv y) (synCrn (.cv f))))
        (synWbr (synCfv (synCcnv (.cv f)) (.cv x)) (.cv r)
          (synCfv (synCcnv (.cv f)) (.cv y))))
      (synWa (synWa (.classMem (.cv x) B) (.classMem (.cv y) B))
        (synWbr (synCfv (synCcnv (.cv f)) (.cv x)) (.cv r)
          (synCfv (synCcnv (.cv f)) (.cv y))))
      p0047 p0065
  have p0067 :=
    @gBitr4d (synWa (synWiso (.cv f) (.cv r) S A B) (synWss S (synCxp B B)))
      (synWbr (.cv x) S (.cv y))
      (synWa (synWa (.classMem (.cv x) B) (.classMem (.cv y) B))
        (synWbr (synCfv (synCcnv (.cv f)) (.cv x)) (.cv r)
          (synCfv (synCcnv (.cv f)) (.cv y))))
      (synWbr (.cv x) (synCcom (synCcom (.cv f) (.cv r)) (synCcnv (.cv f))) (.cv y))
      p0038 p0066
  have p0068 := (Nominal.biimpRefl (synWbr (.cv x) S (.cv y)))
  have p0069 :=
    @gBicomi (synWbr (.cv x) S (.cv y)) (.classMem (synCop (.cv x) (.cv y)) S) p0068
  have p0070 :=
    @gA1i (synWb (.classMem (synCop (.cv x) (.cv y)) S) (synWbr (.cv x) S (.cv y)))
      (synWa (synWiso (.cv f) (.cv r) S A B) (synWss S (synCxp B B))) p0069
  have p0071 :=
    (Nominal.biimpRefl
      (synWbr (.cv x) (synCcom (synCcom (.cv f) (.cv r)) (synCcnv (.cv f))) (.cv y)))
  have p0072 :=
    @gBicomi
      (synWbr (.cv x) (synCcom (synCcom (.cv f) (.cv r)) (synCcnv (.cv f))) (.cv y))
      (.classMem (synCop (.cv x) (.cv y))
        (synCcom (synCcom (.cv f) (.cv r)) (synCcnv (.cv f))))
      p0071
  have p0073 :=
    @gA1i
      (synWb (.classMem (synCop (.cv x) (.cv y))
          (synCcom (synCcom (.cv f) (.cv r)) (synCcnv (.cv f))))
        (synWbr (.cv x) (synCcom (synCcom (.cv f) (.cv r)) (synCcnv (.cv f))) (.cv y)))
      (synWa (synWiso (.cv f) (.cv r) S A B) (synWss S (synCxp B B))) p0072
  have p0074 :=
    @gN3bitr4d (synWa (synWiso (.cv f) (.cv r) S A B) (synWss S (synCxp B B)))
      (synWbr (.cv x) S (.cv y))
      (synWbr (.cv x) (synCcom (synCcom (.cv f) (.cv r)) (synCcnv (.cv f))) (.cv y))
      (.classMem (synCop (.cv x) (.cv y)) S)
      (.classMem (synCop (.cv x) (.cv y))
        (synCcom (synCcom (.cv f) (.cv r)) (synCcnv (.cv f))))
      p0067 p0070 p0073
  have p0075 :=
    @gEqrelrdv (synWa (synWiso (.cv f) (.cv r) S A B) (synWss S (synCxp B B))) x y S
      (synCcom (synCcom (.cv f) (.cv r)) (synCcnv (.cv f))) dv_cache_0003 dv_cache_0004
      dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 p0074
  exact p0075

/-- Checked nominal proof certificate identified upstream as `g_elhwnisogeniso`. -/
@[expose]
noncomputable def gElhwnisogeniso (v : Var) (u : Var) (A : Class) (f : Var) (r : Var)
    (dv_A_f : f ∉ A.fv) (dv_A_r : r ∉ A.fv) (dv_f_r : f ≠ r) (dv_f_u : f ≠ u)
    (dv_f_v : f ≠ v) (dv_r_u : r ≠ u) (dv_r_v : r ≠ v) :
    Nominal.NPrf
      (synWb (synWbr (.cv u) (synChwniso A) (.cv v)) (synWa
          (synWa (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A)))
          (synWex f (synWrex r (synCvv) (synWa (synWiso (.cv f) (.cv r)
                  (synCcom (synCcom (.cv f) (.cv r)) (synCcnv (.cv f)))
                  (synCdm (.cv f)) (synCrn (.cv f)))
                (synWa (.classEq (synCop (.cv r) (synCdm (.cv f))) (.cv u)) (.classEq
                    (synCop (synCcom (synCcom (.cv f) (.cv r)) (synCcnv (.cv f)))
                      (synCrn (.cv f))) (.cv v)))))))) :=
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
  have dv_cache_0008 : r ∉ ((synWf1o (.cv f) (synCdm (.cv f)) (synCrn (.cv f)))).fv :=
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
    @gElhwnisogenf1o v u A f r dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
      dv_cache_0005 dv_cache_0006 dv_cache_0007
  have p0001 :=
    @gR1942v (synWf1o (.cv f) (synCdm (.cv f)) (synCrn (.cv f)))
      (synWa (.classEq (synCop (.cv r) (synCdm (.cv f))) (.cv u)) (.classEq
          (synCop (synCcom (synCcom (.cv f) (.cv r)) (synCcnv (.cv f))) (synCrn (.cv f)))
          (.cv v)))
      r (synCvv) dv_cache_0008
  have p0002 :=
    @gBicomi
      (synWrex r (synCvv) (synWa (synWf1o (.cv f) (synCdm (.cv f)) (synCrn (.cv f)))
          (synWa (.classEq (synCop (.cv r) (synCdm (.cv f))) (.cv u)) (.classEq
              (synCop (synCcom (synCcom (.cv f) (.cv r)) (synCcnv (.cv f)))
                (synCrn (.cv f))) (.cv v)))))
      (synWa (synWf1o (.cv f) (synCdm (.cv f)) (synCrn (.cv f))) (synWrex r (synCvv)
          (synWa (.classEq (synCop (.cv r) (synCdm (.cv f))) (.cv u)) (.classEq
              (synCop (synCcom (synCcom (.cv f) (.cv r)) (synCcnv (.cv f)))
                (synCrn (.cv f))) (.cv v)))))
      p0001
  have p0003 := @gHwtrnisob f r
  have p0004 :=
    @gAnbi1i (synWf1o (.cv f) (synCdm (.cv f)) (synCrn (.cv f)))
      (synWiso (.cv f) (.cv r) (synCcom (synCcom (.cv f) (.cv r)) (synCcnv (.cv f)))
        (synCdm (.cv f)) (synCrn (.cv f)))
      (synWa (.classEq (synCop (.cv r) (synCdm (.cv f))) (.cv u)) (.classEq
          (synCop (synCcom (synCcom (.cv f) (.cv r)) (synCcnv (.cv f))) (synCrn (.cv f)))
          (.cv v)))
      p0003
  have p0005 :=
    @gRexbii
      (synWa (synWf1o (.cv f) (synCdm (.cv f)) (synCrn (.cv f)))
        (synWa (.classEq (synCop (.cv r) (synCdm (.cv f))) (.cv u)) (.classEq
            (synCop (synCcom (synCcom (.cv f) (.cv r)) (synCcnv (.cv f))) (synCrn (.cv f)))
            (.cv v))))
      (synWa (synWiso (.cv f) (.cv r) (synCcom (synCcom (.cv f) (.cv r)) (synCcnv (.cv f)))
          (synCdm (.cv f)) (synCrn (.cv f)))
        (synWa (.classEq (synCop (.cv r) (synCdm (.cv f))) (.cv u)) (.classEq
            (synCop (synCcom (synCcom (.cv f) (.cv r)) (synCcnv (.cv f))) (synCrn (.cv f)))
            (.cv v))))
      r (synCvv) p0004
  have p0006 :=
    @gBitri
      (synWa (synWf1o (.cv f) (synCdm (.cv f)) (synCrn (.cv f))) (synWrex r (synCvv)
          (synWa (.classEq (synCop (.cv r) (synCdm (.cv f))) (.cv u)) (.classEq
              (synCop (synCcom (synCcom (.cv f) (.cv r)) (synCcnv (.cv f)))
                (synCrn (.cv f))) (.cv v)))))
      (synWrex r (synCvv) (synWa (synWf1o (.cv f) (synCdm (.cv f)) (synCrn (.cv f)))
          (synWa (.classEq (synCop (.cv r) (synCdm (.cv f))) (.cv u)) (.classEq
              (synCop (synCcom (synCcom (.cv f) (.cv r)) (synCcnv (.cv f)))
                (synCrn (.cv f))) (.cv v)))))
      (synWrex r (synCvv) (synWa (synWiso (.cv f) (.cv r)
            (synCcom (synCcom (.cv f) (.cv r)) (synCcnv (.cv f))) (synCdm (.cv f))
            (synCrn (.cv f))) (synWa (.classEq (synCop (.cv r) (synCdm (.cv f))) (.cv u))
            (.classEq (synCop (synCcom (synCcom (.cv f) (.cv r)) (synCcnv (.cv f)))
                (synCrn (.cv f))) (.cv v)))))
      p0002 p0005
  have p0007 :=
    @gExbii
      (synWa (synWf1o (.cv f) (synCdm (.cv f)) (synCrn (.cv f))) (synWrex r (synCvv)
          (synWa (.classEq (synCop (.cv r) (synCdm (.cv f))) (.cv u)) (.classEq
              (synCop (synCcom (synCcom (.cv f) (.cv r)) (synCcnv (.cv f)))
                (synCrn (.cv f))) (.cv v)))))
      (synWrex r (synCvv) (synWa (synWiso (.cv f) (.cv r)
            (synCcom (synCcom (.cv f) (.cv r)) (synCcnv (.cv f))) (synCdm (.cv f))
            (synCrn (.cv f))) (synWa (.classEq (synCop (.cv r) (synCdm (.cv f))) (.cv u))
            (.classEq (synCop (synCcom (synCcom (.cv f) (.cv r)) (synCcnv (.cv f)))
                (synCrn (.cv f))) (.cv v)))))
      f p0006
  have p0008 :=
    @gAnbi2i
      (synWex f (synWa (synWf1o (.cv f) (synCdm (.cv f)) (synCrn (.cv f)))
          (synWrex r (synCvv) (synWa (.classEq (synCop (.cv r) (synCdm (.cv f))) (.cv u))
              (.classEq (synCop (synCcom (synCcom (.cv f) (.cv r)) (synCcnv (.cv f)))
                  (synCrn (.cv f))) (.cv v))))))
      (synWex f (synWrex r (synCvv) (synWa (synWiso (.cv f) (.cv r)
              (synCcom (synCcom (.cv f) (.cv r)) (synCcnv (.cv f))) (synCdm (.cv f))
              (synCrn (.cv f))) (synWa (.classEq (synCop (.cv r) (synCdm (.cv f))) (.cv u))
              (.classEq (synCop (synCcom (synCcom (.cv f) (.cv r)) (synCcnv (.cv f)))
                  (synCrn (.cv f))) (.cv v))))))
      (synWa (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A))) p0007
  have p0009 :=
    @gBitri (synWbr (.cv u) (synChwniso A) (.cv v))
      (synWa (synWa (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A)))
        (synWex f (synWa (synWf1o (.cv f) (synCdm (.cv f)) (synCrn (.cv f)))
            (synWrex r (synCvv) (synWa (.classEq (synCop (.cv r) (synCdm (.cv f))) (.cv u))
                (.classEq (synCop (synCcom (synCcom (.cv f) (.cv r)) (synCcnv (.cv f)))
                    (synCrn (.cv f))) (.cv v)))))))
      (synWa (synWa (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A)))
        (synWex f (synWrex r (synCvv) (synWa (synWiso (.cv f) (.cv r)
                (synCcom (synCcom (.cv f) (.cv r)) (synCcnv (.cv f))) (synCdm (.cv f))
                (synCrn (.cv f)))
              (synWa (.classEq (synCop (.cv r) (synCdm (.cv f))) (.cv u)) (.classEq
                  (synCop (synCcom (synCcom (.cv f) (.cv r)) (synCcnv (.cv f)))
                    (synCrn (.cv f))) (.cv v)))))))
      p0000 p0008
  exact p0009

/-- Checked nominal proof certificate identified upstream as `g_hwcnraw`. -/
@[expose]
noncomputable def gHwcnraw (u : Var) (A : Class) :
    Nominal.NPrf
      (.imp (.classMem (.cv u) (synChwcn A)) (.classMem (.cv u) (synChwcodes A))) :=
  by
  have p0000 := @gElhwcn u A
  have p0001 :=
    @gBiimpi (.classMem (.cv u) (synChwcn A))
      (synWa (.classMem (.cv u) (synChwcodes A)) (synWss (synCfv (synC1st) (.cv u))
          (synCxp (synCfv (synC2nd) (.cv u)) (synCfv (synC2nd) (.cv u)))))
      p0000
  have p0002 :=
    @gSimpld (.classMem (.cv u) (synChwcn A)) (.classMem (.cv u) (synChwcodes A))
      (synWss (synCfv (synC1st) (.cv u))
        (synCxp (synCfv (synC2nd) (.cv u)) (synCfv (synC2nd) (.cv u))))
      p0001
  exact p0002

/-- Checked nominal proof certificate identified upstream as `g_hwcnsupp`. -/
@[expose]
noncomputable def gHwcnsupp (u : Var) (A : Class) :
    Nominal.NPrf
      (.imp (.classMem (.cv u) (synChwcn A)) (synWss (synCfv (synC1st) (.cv u))
          (synCxp (synCfv (synC2nd) (.cv u)) (synCfv (synC2nd) (.cv u))))) :=
  by
  have p0000 := @gElhwcn u A
  have p0001 :=
    @gBiimpi (.classMem (.cv u) (synChwcn A))
      (synWa (.classMem (.cv u) (synChwcodes A)) (synWss (synCfv (synC1st) (.cv u))
          (synCxp (synCfv (synC2nd) (.cv u)) (synCfv (synC2nd) (.cv u)))))
      p0000
  have p0002 :=
    @gSimprd (.classMem (.cv u) (synChwcn A)) (.classMem (.cv u) (synChwcodes A))
      (synWss (synCfv (synC1st) (.cv u))
        (synCxp (synCfv (synC2nd) (.cv u)) (synCfv (synC2nd) (.cv u))))
      p0001
  exact p0002

/-- Checked nominal proof certificate identified upstream as `g_hwcnpair`. -/
@[expose]
noncomputable def gHwcnpair (u : Var) (A : Class) :
    Nominal.NPrf
      (.imp (.classMem (.cv u) (synChwcn A)) (.classEq (.cv u)
          (synCop (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u))))) :=
  by
  have p0000 := @gElhwcn u A
  have p0001 :=
    @gBiimpi (.classMem (.cv u) (synChwcn A))
      (synWa (.classMem (.cv u) (synChwcodes A)) (synWss (synCfv (synC1st) (.cv u))
          (synCxp (synCfv (synC2nd) (.cv u)) (synCfv (synC2nd) (.cv u)))))
      p0000
  have p0002 :=
    @gSimpld (.classMem (.cv u) (synChwcn A)) (.classMem (.cv u) (synChwcodes A))
      (synWss (synCfv (synC1st) (.cv u))
        (synCxp (synCfv (synC2nd) (.cv u)) (synCfv (synC2nd) (.cv u))))
      p0001
  have p0003 := (Nominal.classEqRefl (synChwcodes A))
  have p0004 :=
    @gEleq2i (synChwcodes A) (synCin (synCwe) (synCxp (synCvv) (synCpw A))) (.cv u)
      p0003
  have p0005 :=
    @gBiimpi (.classMem (.cv u) (synChwcodes A))
      (.classMem (.cv u) (synCin (synCwe) (synCxp (synCvv) (synCpw A)))) p0004
  have p0006 :=
    @gSyl (.classMem (.cv u) (synChwcn A)) (.classMem (.cv u) (synChwcodes A))
      (.classMem (.cv u) (synCin (synCwe) (synCxp (synCvv) (synCpw A)))) p0002 p0005
  have p0007 := @gElin (.cv u) (synCwe) (synCxp (synCvv) (synCpw A))
  have p0008 :=
    @gBiimpi (.classMem (.cv u) (synCin (synCwe) (synCxp (synCvv) (synCpw A))))
      (synWa (.classMem (.cv u) (synCwe)) (.classMem (.cv u) (synCxp (synCvv) (synCpw A))))
      p0007
  have p0009 :=
    @gSyl (.classMem (.cv u) (synChwcn A))
      (.classMem (.cv u) (synCin (synCwe) (synCxp (synCvv) (synCpw A))))
      (synWa (.classMem (.cv u) (synCwe)) (.classMem (.cv u) (synCxp (synCvv) (synCpw A))))
      p0006 p0008
  have p0010 :=
    @gSimprd (.classMem (.cv u) (synChwcn A)) (.classMem (.cv u) (synCwe))
      (.classMem (.cv u) (synCxp (synCvv) (synCpw A))) p0009
  have p0011 := @gN1st2nd2 (.cv u) (synCvv) (synCpw A)
  have p0012 :=
    @gSyl (.classMem (.cv u) (synChwcn A))
      (.classMem (.cv u) (synCxp (synCvv) (synCpw A)))
      (.classEq (.cv u) (synCop (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u))))
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

/-- Checked nominal proof certificate identified upstream as `g_hwnisorawgeni`. -/
@[expose]
noncomputable def gHwnisorawgeni (v : Var) (u : Var) (A : Class) (f : Var) (r : Var)
    (_dv_A_f : f ∉ A.fv) (dv_A_r : r ∉ A.fv) (dv_f_r : f ≠ r) (dv_f_u : f ≠ u)
    (dv_f_v : f ≠ v) (dv_r_u : r ≠ u) (dv_r_v : r ≠ v) (_dv_u_v : u ≠ v) :
    Nominal.NPrf
      (.imp (synWa (synWa (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A)))
          (synWiso (.cv f) (synCfv (synC1st) (.cv u)) (synCfv (synC1st) (.cv v))
            (synCfv (synC2nd) (.cv u)) (synCfv (synC2nd) (.cv v)))) (synWrex r (synCvv)
          (synWa (synWiso (.cv f) (.cv r)
              (synCcom (synCcom (.cv f) (.cv r)) (synCcnv (.cv f))) (synCdm (.cv f))
              (synCrn (.cv f))) (synWa (.classEq (synCop (.cv r) (synCdm (.cv f))) (.cv u))
              (.classEq (synCop (synCcom (synCcom (.cv f) (.cv r)) (synCcnv (.cv f)))
                  (synCrn (.cv f))) (.cv v)))))) :=
  by
  have dv_cache_0001 : r ∉ ((synCfv (synC1st) (.cv u))).fv := by
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
  have dv_cache_0002 : r ∉ ((synCvv)).fv :=
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
  have dv_cache_0003 : f ∉ ((synCfv (synC2nd) (.cv u))).fv :=
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
  have dv_cache_0004 : f ∉ ((synCfv (synC2nd) (.cv v))).fv :=
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
  have dv_cache_0005 : f ∉ ((synCfv (synC1st) (.cv v))).fv :=
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
      ((synWa (synWa (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A)))
          (synWiso (.cv f) (synCfv (synC1st) (.cv u)) (synCfv (synC1st) (.cv v))
            (synCfv (synC2nd) (.cv u)) (synCfv (synC2nd) (.cv v))))).fv :=
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
  have p0000 := @gFvex (.cv u) (synC1st)
  have p0001 :=
    @gRisset r (synCfv (synC1st) (.cv u)) (synCvv) dv_cache_0001 dv_cache_0002
  have p0002 :=
    @gMpbi (.classMem (synCfv (synC1st) (.cv u)) (synCvv))
      (synWrex r (synCvv) (.classEq (.cv r) (synCfv (synC1st) (.cv u)))) p0000 p0001
  have p0003 :=
    @gA1i (synWrex r (synCvv) (.classEq (.cv r) (synCfv (synC1st) (.cv u))))
      (synWa (synWa (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A)))
        (synWiso (.cv f) (synCfv (synC1st) (.cv u)) (synCfv (synC1st) (.cv v))
          (synCfv (synC2nd) (.cv u)) (synCfv (synC2nd) (.cv v))))
      p0002
  have p0004 :=
    @gSimpl
      (synWa (synWa (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A)))
        (synWiso (.cv f) (synCfv (synC1st) (.cv u)) (synCfv (synC1st) (.cv v))
          (synCfv (synC2nd) (.cv u)) (synCfv (synC2nd) (.cv v))))
      (.classEq (.cv r) (synCfv (synC1st) (.cv u)))
  have p0005 :=
    @gSimpr (synWa (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A)))
      (synWiso (.cv f) (synCfv (synC1st) (.cv u)) (synCfv (synC1st) (.cv v))
        (synCfv (synC2nd) (.cv u)) (synCfv (synC2nd) (.cv v)))
  have p0006 :=
    @gSyl
      (synWa (synWa
          (synWa (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A)))
          (synWiso (.cv f) (synCfv (synC1st) (.cv u)) (synCfv (synC1st) (.cv v))
            (synCfv (synC2nd) (.cv u)) (synCfv (synC2nd) (.cv v))))
        (.classEq (.cv r) (synCfv (synC1st) (.cv u))))
      (synWa (synWa (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A)))
        (synWiso (.cv f) (synCfv (synC1st) (.cv u)) (synCfv (synC1st) (.cv v))
          (synCfv (synC2nd) (.cv u)) (synCfv (synC2nd) (.cv v))))
      (synWiso (.cv f) (synCfv (synC1st) (.cv u)) (synCfv (synC1st) (.cv v))
        (synCfv (synC2nd) (.cv u)) (synCfv (synC2nd) (.cv v)))
      p0004 p0005
  have p0007 :=
    @gSimpr
      (synWa (synWa (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A)))
        (synWiso (.cv f) (synCfv (synC1st) (.cv u)) (synCfv (synC1st) (.cv v))
          (synCfv (synC2nd) (.cv u)) (synCfv (synC2nd) (.cv v))))
      (.classEq (.cv r) (synCfv (synC1st) (.cv u)))
  have p0008 :=
    @gIsoeq2 (synCfv (synC2nd) (.cv u)) (synCfv (synC2nd) (.cv v)) (.cv r)
      (synCfv (synC1st) (.cv v)) (synCfv (synC1st) (.cv u)) (.cv f)
  have p0009 :=
    @gSyl
      (synWa (synWa
          (synWa (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A)))
          (synWiso (.cv f) (synCfv (synC1st) (.cv u)) (synCfv (synC1st) (.cv v))
            (synCfv (synC2nd) (.cv u)) (synCfv (synC2nd) (.cv v))))
        (.classEq (.cv r) (synCfv (synC1st) (.cv u))))
      (.classEq (.cv r) (synCfv (synC1st) (.cv u)))
      (synWb (synWiso (.cv f) (.cv r) (synCfv (synC1st) (.cv v))
          (synCfv (synC2nd) (.cv u)) (synCfv (synC2nd) (.cv v)))
        (synWiso (.cv f) (synCfv (synC1st) (.cv u)) (synCfv (synC1st) (.cv v))
          (synCfv (synC2nd) (.cv u)) (synCfv (synC2nd) (.cv v))))
      p0007 p0008
  have p0010 :=
    @gBiimprd
      (synWa (synWa
          (synWa (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A)))
          (synWiso (.cv f) (synCfv (synC1st) (.cv u)) (synCfv (synC1st) (.cv v))
            (synCfv (synC2nd) (.cv u)) (synCfv (synC2nd) (.cv v))))
        (.classEq (.cv r) (synCfv (synC1st) (.cv u))))
      (synWiso (.cv f) (.cv r) (synCfv (synC1st) (.cv v)) (synCfv (synC2nd) (.cv u))
        (synCfv (synC2nd) (.cv v)))
      (synWiso (.cv f) (synCfv (synC1st) (.cv u)) (synCfv (synC1st) (.cv v))
        (synCfv (synC2nd) (.cv u)) (synCfv (synC2nd) (.cv v)))
      p0009
  have p0011 :=
    @gMpd
      (synWa (synWa
          (synWa (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A)))
          (synWiso (.cv f) (synCfv (synC1st) (.cv u)) (synCfv (synC1st) (.cv v))
            (synCfv (synC2nd) (.cv u)) (synCfv (synC2nd) (.cv v))))
        (.classEq (.cv r) (synCfv (synC1st) (.cv u))))
      (synWiso (.cv f) (synCfv (synC1st) (.cv u)) (synCfv (synC1st) (.cv v))
        (synCfv (synC2nd) (.cv u)) (synCfv (synC2nd) (.cv v)))
      (synWiso (.cv f) (.cv r) (synCfv (synC1st) (.cv v)) (synCfv (synC2nd) (.cv u))
        (synCfv (synC2nd) (.cv v)))
      p0006 p0010
  have p0021 :=
    @gSimpl (synWa (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A)))
      (synWiso (.cv f) (synCfv (synC1st) (.cv u)) (synCfv (synC1st) (.cv v))
        (synCfv (synC2nd) (.cv u)) (synCfv (synC2nd) (.cv v)))
  have p0022 :=
    @gSimpr (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A))
  have p0023 :=
    @gSyl
      (synWa (synWa (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A)))
        (synWiso (.cv f) (synCfv (synC1st) (.cv u)) (synCfv (synC1st) (.cv v))
          (synCfv (synC2nd) (.cv u)) (synCfv (synC2nd) (.cv v))))
      (synWa (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A)))
      (.classMem (.cv v) (synChwcn A)) p0021 p0022
  have p0024 := @gHwcnsupp v A
  have p0025 :=
    @gSyl
      (synWa (synWa (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A)))
        (synWiso (.cv f) (synCfv (synC1st) (.cv u)) (synCfv (synC1st) (.cv v))
          (synCfv (synC2nd) (.cv u)) (synCfv (synC2nd) (.cv v))))
      (.classMem (.cv v) (synChwcn A))
      (synWss (synCfv (synC1st) (.cv v))
        (synCxp (synCfv (synC2nd) (.cv v)) (synCfv (synC2nd) (.cv v))))
      p0023 p0024
  have p0026 :=
    @gSyl
      (synWa (synWa
          (synWa (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A)))
          (synWiso (.cv f) (synCfv (synC1st) (.cv u)) (synCfv (synC1st) (.cv v))
            (synCfv (synC2nd) (.cv u)) (synCfv (synC2nd) (.cv v))))
        (.classEq (.cv r) (synCfv (synC1st) (.cv u))))
      (synWa (synWa (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A)))
        (synWiso (.cv f) (synCfv (synC1st) (.cv u)) (synCfv (synC1st) (.cv v))
          (synCfv (synC2nd) (.cv u)) (synCfv (synC2nd) (.cv v))))
      (synWss (synCfv (synC1st) (.cv v))
        (synCxp (synCfv (synC2nd) (.cv v)) (synCfv (synC2nd) (.cv v))))
      p0004 p0025
  have p0027 :=
    @gJca
      (synWa (synWa
          (synWa (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A)))
          (synWiso (.cv f) (synCfv (synC1st) (.cv u)) (synCfv (synC1st) (.cv v))
            (synCfv (synC2nd) (.cv u)) (synCfv (synC2nd) (.cv v))))
        (.classEq (.cv r) (synCfv (synC1st) (.cv u))))
      (synWiso (.cv f) (.cv r) (synCfv (synC1st) (.cv v)) (synCfv (synC2nd) (.cv u))
        (synCfv (synC2nd) (.cv v)))
      (synWss (synCfv (synC1st) (.cv v))
        (synCxp (synCfv (synC2nd) (.cv v)) (synCfv (synC2nd) (.cv v))))
      p0011 p0026
  have p0028 :=
    @gIsotargettransport (synCfv (synC2nd) (.cv u)) (synCfv (synC2nd) (.cv v))
      (synCfv (synC1st) (.cv v)) f r dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006
  have p0029 :=
    @gSyl
      (synWa (synWa
          (synWa (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A)))
          (synWiso (.cv f) (synCfv (synC1st) (.cv u)) (synCfv (synC1st) (.cv v))
            (synCfv (synC2nd) (.cv u)) (synCfv (synC2nd) (.cv v))))
        (.classEq (.cv r) (synCfv (synC1st) (.cv u))))
      (synWa (synWiso (.cv f) (.cv r) (synCfv (synC1st) (.cv v))
          (synCfv (synC2nd) (.cv u)) (synCfv (synC2nd) (.cv v)))
        (synWss (synCfv (synC1st) (.cv v))
          (synCxp (synCfv (synC2nd) (.cv v)) (synCfv (synC2nd) (.cv v)))))
      (.classEq (synCfv (synC1st) (.cv v))
        (synCcom (synCcom (.cv f) (.cv r)) (synCcnv (.cv f))))
      p0027 p0028
  have p0030 :=
    @gIsoeq3 (synCfv (synC2nd) (.cv u)) (synCfv (synC2nd) (.cv v)) (.cv r)
      (synCfv (synC1st) (.cv v))
      (synCcom (synCcom (.cv f) (.cv r)) (synCcnv (.cv f))) (.cv f)
  have p0031 :=
    @gSyl
      (synWa (synWa
          (synWa (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A)))
          (synWiso (.cv f) (synCfv (synC1st) (.cv u)) (synCfv (synC1st) (.cv v))
            (synCfv (synC2nd) (.cv u)) (synCfv (synC2nd) (.cv v))))
        (.classEq (.cv r) (synCfv (synC1st) (.cv u))))
      (.classEq (synCfv (synC1st) (.cv v))
        (synCcom (synCcom (.cv f) (.cv r)) (synCcnv (.cv f))))
      (synWb (synWiso (.cv f) (.cv r) (synCfv (synC1st) (.cv v))
          (synCfv (synC2nd) (.cv u)) (synCfv (synC2nd) (.cv v)))
        (synWiso (.cv f) (.cv r) (synCcom (synCcom (.cv f) (.cv r)) (synCcnv (.cv f)))
          (synCfv (synC2nd) (.cv u)) (synCfv (synC2nd) (.cv v))))
      p0029 p0030
  have p0034 :=
    @gIsof1o (synCfv (synC2nd) (.cv u)) (synCfv (synC2nd) (.cv v))
      (synCfv (synC1st) (.cv u)) (synCfv (synC1st) (.cv v)) (.cv f)
  have p0035 :=
    @gSyl
      (synWa (synWa (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A)))
        (synWiso (.cv f) (synCfv (synC1st) (.cv u)) (synCfv (synC1st) (.cv v))
          (synCfv (synC2nd) (.cv u)) (synCfv (synC2nd) (.cv v))))
      (synWiso (.cv f) (synCfv (synC1st) (.cv u)) (synCfv (synC1st) (.cv v))
        (synCfv (synC2nd) (.cv u)) (synCfv (synC2nd) (.cv v)))
      (synWf1o (.cv f) (synCfv (synC2nd) (.cv u)) (synCfv (synC2nd) (.cv v))) p0005
      p0034
  have p0036 := @gF1odm (synCfv (synC2nd) (.cv u)) (synCfv (synC2nd) (.cv v)) (.cv f)
  have p0037 :=
    @gSyl
      (synWa (synWa (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A)))
        (synWiso (.cv f) (synCfv (synC1st) (.cv u)) (synCfv (synC1st) (.cv v))
          (synCfv (synC2nd) (.cv u)) (synCfv (synC2nd) (.cv v))))
      (synWf1o (.cv f) (synCfv (synC2nd) (.cv u)) (synCfv (synC2nd) (.cv v)))
      (.classEq (synCdm (.cv f)) (synCfv (synC2nd) (.cv u))) p0035 p0036
  have p0038 :=
    @gSyl
      (synWa (synWa
          (synWa (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A)))
          (synWiso (.cv f) (synCfv (synC1st) (.cv u)) (synCfv (synC1st) (.cv v))
            (synCfv (synC2nd) (.cv u)) (synCfv (synC2nd) (.cv v))))
        (.classEq (.cv r) (synCfv (synC1st) (.cv u))))
      (synWa (synWa (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A)))
        (synWiso (.cv f) (synCfv (synC1st) (.cv u)) (synCfv (synC1st) (.cv v))
          (synCfv (synC2nd) (.cv u)) (synCfv (synC2nd) (.cv v))))
      (.classEq (synCdm (.cv f)) (synCfv (synC2nd) (.cv u))) p0004 p0037
  have p0039 :=
    @gEqcomd
      (synWa (synWa
          (synWa (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A)))
          (synWiso (.cv f) (synCfv (synC1st) (.cv u)) (synCfv (synC1st) (.cv v))
            (synCfv (synC2nd) (.cv u)) (synCfv (synC2nd) (.cv v))))
        (.classEq (.cv r) (synCfv (synC1st) (.cv u))))
      (synCdm (.cv f)) (synCfv (synC2nd) (.cv u)) p0038
  have p0040 :=
    @gIsoeq4 (synCfv (synC2nd) (.cv u)) (synCfv (synC2nd) (.cv v)) (synCdm (.cv f))
      (.cv r) (synCcom (synCcom (.cv f) (.cv r)) (synCcnv (.cv f))) (.cv f)
  have p0041 :=
    @gSyl
      (synWa (synWa
          (synWa (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A)))
          (synWiso (.cv f) (synCfv (synC1st) (.cv u)) (synCfv (synC1st) (.cv v))
            (synCfv (synC2nd) (.cv u)) (synCfv (synC2nd) (.cv v))))
        (.classEq (.cv r) (synCfv (synC1st) (.cv u))))
      (.classEq (synCfv (synC2nd) (.cv u)) (synCdm (.cv f)))
      (synWb (synWiso (.cv f) (.cv r) (synCcom (synCcom (.cv f) (.cv r)) (synCcnv (.cv f)))
          (synCfv (synC2nd) (.cv u)) (synCfv (synC2nd) (.cv v)))
        (synWiso (.cv f) (.cv r) (synCcom (synCcom (.cv f) (.cv r)) (synCcnv (.cv f)))
          (synCdm (.cv f)) (synCfv (synC2nd) (.cv v))))
      p0039 p0040
  have p0042 :=
    @gBitrd
      (synWa (synWa
          (synWa (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A)))
          (synWiso (.cv f) (synCfv (synC1st) (.cv u)) (synCfv (synC1st) (.cv v))
            (synCfv (synC2nd) (.cv u)) (synCfv (synC2nd) (.cv v))))
        (.classEq (.cv r) (synCfv (synC1st) (.cv u))))
      (synWiso (.cv f) (.cv r) (synCfv (synC1st) (.cv v)) (synCfv (synC2nd) (.cv u))
        (synCfv (synC2nd) (.cv v)))
      (synWiso (.cv f) (.cv r) (synCcom (synCcom (.cv f) (.cv r)) (synCcnv (.cv f)))
        (synCfv (synC2nd) (.cv u)) (synCfv (synC2nd) (.cv v)))
      (synWiso (.cv f) (.cv r) (synCcom (synCcom (.cv f) (.cv r)) (synCcnv (.cv f)))
        (synCdm (.cv f)) (synCfv (synC2nd) (.cv v)))
      p0031 p0041
  have p0047 := @gF1ofo (synCfv (synC2nd) (.cv u)) (synCfv (synC2nd) (.cv v)) (.cv f)
  have p0048 :=
    @gSyl
      (synWa (synWa (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A)))
        (synWiso (.cv f) (synCfv (synC1st) (.cv u)) (synCfv (synC1st) (.cv v))
          (synCfv (synC2nd) (.cv u)) (synCfv (synC2nd) (.cv v))))
      (synWf1o (.cv f) (synCfv (synC2nd) (.cv u)) (synCfv (synC2nd) (.cv v)))
      (synWfo (.cv f) (synCfv (synC2nd) (.cv u)) (synCfv (synC2nd) (.cv v))) p0035
      p0047
  have p0049 := @gForn (synCfv (synC2nd) (.cv u)) (synCfv (synC2nd) (.cv v)) (.cv f)
  have p0050 :=
    @gSyl
      (synWa (synWa (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A)))
        (synWiso (.cv f) (synCfv (synC1st) (.cv u)) (synCfv (synC1st) (.cv v))
          (synCfv (synC2nd) (.cv u)) (synCfv (synC2nd) (.cv v))))
      (synWfo (.cv f) (synCfv (synC2nd) (.cv u)) (synCfv (synC2nd) (.cv v)))
      (.classEq (synCrn (.cv f)) (synCfv (synC2nd) (.cv v))) p0048 p0049
  have p0051 :=
    @gSyl
      (synWa (synWa
          (synWa (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A)))
          (synWiso (.cv f) (synCfv (synC1st) (.cv u)) (synCfv (synC1st) (.cv v))
            (synCfv (synC2nd) (.cv u)) (synCfv (synC2nd) (.cv v))))
        (.classEq (.cv r) (synCfv (synC1st) (.cv u))))
      (synWa (synWa (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A)))
        (synWiso (.cv f) (synCfv (synC1st) (.cv u)) (synCfv (synC1st) (.cv v))
          (synCfv (synC2nd) (.cv u)) (synCfv (synC2nd) (.cv v))))
      (.classEq (synCrn (.cv f)) (synCfv (synC2nd) (.cv v))) p0004 p0050
  have p0052 :=
    @gEqcomd
      (synWa (synWa
          (synWa (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A)))
          (synWiso (.cv f) (synCfv (synC1st) (.cv u)) (synCfv (synC1st) (.cv v))
            (synCfv (synC2nd) (.cv u)) (synCfv (synC2nd) (.cv v))))
        (.classEq (.cv r) (synCfv (synC1st) (.cv u))))
      (synCrn (.cv f)) (synCfv (synC2nd) (.cv v)) p0051
  have p0053 :=
    @gIsoeq5 (synCdm (.cv f)) (synCfv (synC2nd) (.cv v)) (synCrn (.cv f)) (.cv r)
      (synCcom (synCcom (.cv f) (.cv r)) (synCcnv (.cv f))) (.cv f)
  have p0054 :=
    @gSyl
      (synWa (synWa
          (synWa (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A)))
          (synWiso (.cv f) (synCfv (synC1st) (.cv u)) (synCfv (synC1st) (.cv v))
            (synCfv (synC2nd) (.cv u)) (synCfv (synC2nd) (.cv v))))
        (.classEq (.cv r) (synCfv (synC1st) (.cv u))))
      (.classEq (synCfv (synC2nd) (.cv v)) (synCrn (.cv f)))
      (synWb (synWiso (.cv f) (.cv r) (synCcom (synCcom (.cv f) (.cv r)) (synCcnv (.cv f)))
          (synCdm (.cv f)) (synCfv (synC2nd) (.cv v)))
        (synWiso (.cv f) (.cv r) (synCcom (synCcom (.cv f) (.cv r)) (synCcnv (.cv f)))
          (synCdm (.cv f)) (synCrn (.cv f))))
      p0052 p0053
  have p0055 :=
    @gBitrd
      (synWa (synWa
          (synWa (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A)))
          (synWiso (.cv f) (synCfv (synC1st) (.cv u)) (synCfv (synC1st) (.cv v))
            (synCfv (synC2nd) (.cv u)) (synCfv (synC2nd) (.cv v))))
        (.classEq (.cv r) (synCfv (synC1st) (.cv u))))
      (synWiso (.cv f) (.cv r) (synCfv (synC1st) (.cv v)) (synCfv (synC2nd) (.cv u))
        (synCfv (synC2nd) (.cv v)))
      (synWiso (.cv f) (.cv r) (synCcom (synCcom (.cv f) (.cv r)) (synCcnv (.cv f)))
        (synCdm (.cv f)) (synCfv (synC2nd) (.cv v)))
      (synWiso (.cv f) (.cv r) (synCcom (synCcom (.cv f) (.cv r)) (synCcnv (.cv f)))
        (synCdm (.cv f)) (synCrn (.cv f)))
      p0042 p0054
  have p0056 :=
    @gBiimpd
      (synWa (synWa
          (synWa (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A)))
          (synWiso (.cv f) (synCfv (synC1st) (.cv u)) (synCfv (synC1st) (.cv v))
            (synCfv (synC2nd) (.cv u)) (synCfv (synC2nd) (.cv v))))
        (.classEq (.cv r) (synCfv (synC1st) (.cv u))))
      (synWiso (.cv f) (.cv r) (synCfv (synC1st) (.cv v)) (synCfv (synC2nd) (.cv u))
        (synCfv (synC2nd) (.cv v)))
      (synWiso (.cv f) (.cv r) (synCcom (synCcom (.cv f) (.cv r)) (synCcnv (.cv f)))
        (synCdm (.cv f)) (synCrn (.cv f)))
      p0055
  have p0057 :=
    @gMpd
      (synWa (synWa
          (synWa (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A)))
          (synWiso (.cv f) (synCfv (synC1st) (.cv u)) (synCfv (synC1st) (.cv v))
            (synCfv (synC2nd) (.cv u)) (synCfv (synC2nd) (.cv v))))
        (.classEq (.cv r) (synCfv (synC1st) (.cv u))))
      (synWiso (.cv f) (.cv r) (synCfv (synC1st) (.cv v)) (synCfv (synC2nd) (.cv u))
        (synCfv (synC2nd) (.cv v)))
      (synWiso (.cv f) (.cv r) (synCcom (synCcom (.cv f) (.cv r)) (synCcnv (.cv f)))
        (synCdm (.cv f)) (synCrn (.cv f)))
      p0011 p0056
  have p0066 :=
    @gJca
      (synWa (synWa
          (synWa (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A)))
          (synWiso (.cv f) (synCfv (synC1st) (.cv u)) (synCfv (synC1st) (.cv v))
            (synCfv (synC2nd) (.cv u)) (synCfv (synC2nd) (.cv v))))
        (.classEq (.cv r) (synCfv (synC1st) (.cv u))))
      (.classEq (.cv r) (synCfv (synC1st) (.cv u)))
      (.classEq (synCdm (.cv f)) (synCfv (synC2nd) (.cv u))) p0007 p0038
  have p0067 :=
    @gOpeq12 (.cv r) (synCfv (synC1st) (.cv u)) (synCdm (.cv f))
      (synCfv (synC2nd) (.cv u))
  have p0068 :=
    @gSyl
      (synWa (synWa
          (synWa (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A)))
          (synWiso (.cv f) (synCfv (synC1st) (.cv u)) (synCfv (synC1st) (.cv v))
            (synCfv (synC2nd) (.cv u)) (synCfv (synC2nd) (.cv v))))
        (.classEq (.cv r) (synCfv (synC1st) (.cv u))))
      (synWa (.classEq (.cv r) (synCfv (synC1st) (.cv u)))
        (.classEq (synCdm (.cv f)) (synCfv (synC2nd) (.cv u))))
      (.classEq (synCop (.cv r) (synCdm (.cv f)))
        (synCop (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u))))
      p0066 p0067
  have p0071 :=
    @gSimpl (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A))
  have p0072 :=
    @gSyl
      (synWa (synWa (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A)))
        (synWiso (.cv f) (synCfv (synC1st) (.cv u)) (synCfv (synC1st) (.cv v))
          (synCfv (synC2nd) (.cv u)) (synCfv (synC2nd) (.cv v))))
      (synWa (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A)))
      (.classMem (.cv u) (synChwcn A)) p0021 p0071
  have p0073 := @gHwcnpair u A
  have p0074 :=
    @gSyl
      (synWa (synWa (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A)))
        (synWiso (.cv f) (synCfv (synC1st) (.cv u)) (synCfv (synC1st) (.cv v))
          (synCfv (synC2nd) (.cv u)) (synCfv (synC2nd) (.cv v))))
      (.classMem (.cv u) (synChwcn A))
      (.classEq (.cv u) (synCop (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u))))
      p0072 p0073
  have p0075 :=
    @gSyl
      (synWa (synWa
          (synWa (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A)))
          (synWiso (.cv f) (synCfv (synC1st) (.cv u)) (synCfv (synC1st) (.cv v))
            (synCfv (synC2nd) (.cv u)) (synCfv (synC2nd) (.cv v))))
        (.classEq (.cv r) (synCfv (synC1st) (.cv u))))
      (synWa (synWa (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A)))
        (synWiso (.cv f) (synCfv (synC1st) (.cv u)) (synCfv (synC1st) (.cv v))
          (synCfv (synC2nd) (.cv u)) (synCfv (synC2nd) (.cv v))))
      (.classEq (.cv u) (synCop (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u))))
      p0004 p0074
  have p0076 :=
    @gEqtr4d
      (synWa (synWa
          (synWa (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A)))
          (synWiso (.cv f) (synCfv (synC1st) (.cv u)) (synCfv (synC1st) (.cv v))
            (synCfv (synC2nd) (.cv u)) (synCfv (synC2nd) (.cv v))))
        (.classEq (.cv r) (synCfv (synC1st) (.cv u))))
      (synCop (.cv r) (synCdm (.cv f)))
      (synCop (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u))) (.cv u) p0068
      p0075
  have p0095 :=
    @gEqcomd
      (synWa (synWa
          (synWa (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A)))
          (synWiso (.cv f) (synCfv (synC1st) (.cv u)) (synCfv (synC1st) (.cv v))
            (synCfv (synC2nd) (.cv u)) (synCfv (synC2nd) (.cv v))))
        (.classEq (.cv r) (synCfv (synC1st) (.cv u))))
      (synCfv (synC1st) (.cv v))
      (synCcom (synCcom (.cv f) (.cv r)) (synCcnv (.cv f))) p0029
  have p0105 :=
    @gJca
      (synWa (synWa
          (synWa (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A)))
          (synWiso (.cv f) (synCfv (synC1st) (.cv u)) (synCfv (synC1st) (.cv v))
            (synCfv (synC2nd) (.cv u)) (synCfv (synC2nd) (.cv v))))
        (.classEq (.cv r) (synCfv (synC1st) (.cv u))))
      (.classEq (synCcom (synCcom (.cv f) (.cv r)) (synCcnv (.cv f)))
        (synCfv (synC1st) (.cv v)))
      (.classEq (synCrn (.cv f)) (synCfv (synC2nd) (.cv v))) p0095 p0051
  have p0106 :=
    @gOpeq12 (synCcom (synCcom (.cv f) (.cv r)) (synCcnv (.cv f)))
      (synCfv (synC1st) (.cv v)) (synCrn (.cv f)) (synCfv (synC2nd) (.cv v))
  have p0107 :=
    @gSyl
      (synWa (synWa
          (synWa (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A)))
          (synWiso (.cv f) (synCfv (synC1st) (.cv u)) (synCfv (synC1st) (.cv v))
            (synCfv (synC2nd) (.cv u)) (synCfv (synC2nd) (.cv v))))
        (.classEq (.cv r) (synCfv (synC1st) (.cv u))))
      (synWa (.classEq (synCcom (synCcom (.cv f) (.cv r)) (synCcnv (.cv f)))
          (synCfv (synC1st) (.cv v)))
        (.classEq (synCrn (.cv f)) (synCfv (synC2nd) (.cv v))))
      (.classEq (synCop (synCcom (synCcom (.cv f) (.cv r)) (synCcnv (.cv f)))
          (synCrn (.cv f)))
        (synCop (synCfv (synC1st) (.cv v)) (synCfv (synC2nd) (.cv v))))
      p0105 p0106
  have p0112 := @gHwcnpair v A
  have p0113 :=
    @gSyl
      (synWa (synWa (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A)))
        (synWiso (.cv f) (synCfv (synC1st) (.cv u)) (synCfv (synC1st) (.cv v))
          (synCfv (synC2nd) (.cv u)) (synCfv (synC2nd) (.cv v))))
      (.classMem (.cv v) (synChwcn A))
      (.classEq (.cv v) (synCop (synCfv (synC1st) (.cv v)) (synCfv (synC2nd) (.cv v))))
      p0023 p0112
  have p0114 :=
    @gSyl
      (synWa (synWa
          (synWa (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A)))
          (synWiso (.cv f) (synCfv (synC1st) (.cv u)) (synCfv (synC1st) (.cv v))
            (synCfv (synC2nd) (.cv u)) (synCfv (synC2nd) (.cv v))))
        (.classEq (.cv r) (synCfv (synC1st) (.cv u))))
      (synWa (synWa (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A)))
        (synWiso (.cv f) (synCfv (synC1st) (.cv u)) (synCfv (synC1st) (.cv v))
          (synCfv (synC2nd) (.cv u)) (synCfv (synC2nd) (.cv v))))
      (.classEq (.cv v) (synCop (synCfv (synC1st) (.cv v)) (synCfv (synC2nd) (.cv v))))
      p0004 p0113
  have p0115 :=
    @gEqtr4d
      (synWa (synWa
          (synWa (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A)))
          (synWiso (.cv f) (synCfv (synC1st) (.cv u)) (synCfv (synC1st) (.cv v))
            (synCfv (synC2nd) (.cv u)) (synCfv (synC2nd) (.cv v))))
        (.classEq (.cv r) (synCfv (synC1st) (.cv u))))
      (synCop (synCcom (synCcom (.cv f) (.cv r)) (synCcnv (.cv f))) (synCrn (.cv f)))
      (synCop (synCfv (synC1st) (.cv v)) (synCfv (synC2nd) (.cv v))) (.cv v) p0107
      p0114
  have p0116 :=
    @gJca
      (synWa (synWa
          (synWa (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A)))
          (synWiso (.cv f) (synCfv (synC1st) (.cv u)) (synCfv (synC1st) (.cv v))
            (synCfv (synC2nd) (.cv u)) (synCfv (synC2nd) (.cv v))))
        (.classEq (.cv r) (synCfv (synC1st) (.cv u))))
      (.classEq (synCop (.cv r) (synCdm (.cv f))) (.cv u))
      (.classEq (synCop (synCcom (synCcom (.cv f) (.cv r)) (synCcnv (.cv f)))
          (synCrn (.cv f))) (.cv v))
      p0076 p0115
  have p0117 :=
    @gJca
      (synWa (synWa
          (synWa (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A)))
          (synWiso (.cv f) (synCfv (synC1st) (.cv u)) (synCfv (synC1st) (.cv v))
            (synCfv (synC2nd) (.cv u)) (synCfv (synC2nd) (.cv v))))
        (.classEq (.cv r) (synCfv (synC1st) (.cv u))))
      (synWiso (.cv f) (.cv r) (synCcom (synCcom (.cv f) (.cv r)) (synCcnv (.cv f)))
        (synCdm (.cv f)) (synCrn (.cv f)))
      (synWa (.classEq (synCop (.cv r) (synCdm (.cv f))) (.cv u)) (.classEq
          (synCop (synCcom (synCcom (.cv f) (.cv r)) (synCcnv (.cv f))) (synCrn (.cv f)))
          (.cv v)))
      p0057 p0116
  have p0118 :=
    @gEx
      (synWa (synWa (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A)))
        (synWiso (.cv f) (synCfv (synC1st) (.cv u)) (synCfv (synC1st) (.cv v))
          (synCfv (synC2nd) (.cv u)) (synCfv (synC2nd) (.cv v))))
      (.classEq (.cv r) (synCfv (synC1st) (.cv u)))
      (synWa (synWiso (.cv f) (.cv r) (synCcom (synCcom (.cv f) (.cv r)) (synCcnv (.cv f)))
          (synCdm (.cv f)) (synCrn (.cv f)))
        (synWa (.classEq (synCop (.cv r) (synCdm (.cv f))) (.cv u)) (.classEq
            (synCop (synCcom (synCcom (.cv f) (.cv r)) (synCcnv (.cv f))) (synCrn (.cv f)))
            (.cv v))))
      p0117
  have p0119 :=
    @gReximdv
      (synWa (synWa (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A)))
        (synWiso (.cv f) (synCfv (synC1st) (.cv u)) (synCfv (synC1st) (.cv v))
          (synCfv (synC2nd) (.cv u)) (synCfv (synC2nd) (.cv v))))
      (.classEq (.cv r) (synCfv (synC1st) (.cv u)))
      (synWa (synWiso (.cv f) (.cv r) (synCcom (synCcom (.cv f) (.cv r)) (synCcnv (.cv f)))
          (synCdm (.cv f)) (synCrn (.cv f)))
        (synWa (.classEq (synCop (.cv r) (synCdm (.cv f))) (.cv u)) (.classEq
            (synCop (synCcom (synCcom (.cv f) (.cv r)) (synCcnv (.cv f))) (synCrn (.cv f)))
            (.cv v))))
      r (synCvv) dv_cache_0007 p0118
  have p0120 :=
    @gMpd
      (synWa (synWa (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A)))
        (synWiso (.cv f) (synCfv (synC1st) (.cv u)) (synCfv (synC1st) (.cv v))
          (synCfv (synC2nd) (.cv u)) (synCfv (synC2nd) (.cv v))))
      (synWrex r (synCvv) (.classEq (.cv r) (synCfv (synC1st) (.cv u))))
      (synWrex r (synCvv) (synWa (synWiso (.cv f) (.cv r)
            (synCcom (synCcom (.cv f) (.cv r)) (synCcnv (.cv f))) (synCdm (.cv f))
            (synCrn (.cv f))) (synWa (.classEq (synCop (.cv r) (synCdm (.cv f))) (.cv u))
            (.classEq (synCop (synCcom (synCcom (.cv f) (.cv r)) (synCcnv (.cv f)))
                (synCrn (.cv f))) (.cv v)))))
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

/-- Checked nominal proof certificate identified upstream as `g_hwnisogenrawi`. -/
@[expose]
noncomputable def gHwnisogenrawi (v : Var) (u : Var) (A : Class) (f : Var) (r : Var)
    (_dv_A_f : f ∉ A.fv) (_dv_A_r : r ∉ A.fv) (_dv_f_r : f ≠ r) (_dv_f_u : f ≠ u)
    (_dv_f_v : f ≠ v) (_dv_r_u : r ≠ u) (_dv_r_v : r ≠ v) (_dv_u_v : u ≠ v) :
    Nominal.NPrf
      (.imp (synWa (synWa (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A)))
          (synWa (synWiso (.cv f) (.cv r)
              (synCcom (synCcom (.cv f) (.cv r)) (synCcnv (.cv f))) (synCdm (.cv f))
              (synCrn (.cv f))) (synWa (.classEq (synCop (.cv r) (synCdm (.cv f))) (.cv u))
              (.classEq (synCop (synCcom (synCcom (.cv f) (.cv r)) (synCcnv (.cv f)))
                  (synCrn (.cv f))) (.cv v)))))
        (synWiso (.cv f) (synCfv (synC1st) (.cv u)) (synCfv (synC1st) (.cv v))
          (synCfv (synC2nd) (.cv u)) (synCfv (synC2nd) (.cv v)))) :=
  by
  have p0000 :=
    @gSimpr (synWa (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A)))
      (synWa (synWiso (.cv f) (.cv r) (synCcom (synCcom (.cv f) (.cv r)) (synCcnv (.cv f)))
          (synCdm (.cv f)) (synCrn (.cv f)))
        (synWa (.classEq (synCop (.cv r) (synCdm (.cv f))) (.cv u)) (.classEq
            (synCop (synCcom (synCcom (.cv f) (.cv r)) (synCcnv (.cv f))) (synCrn (.cv f)))
            (.cv v))))
  have p0001 :=
    @gSimpl
      (synWiso (.cv f) (.cv r) (synCcom (synCcom (.cv f) (.cv r)) (synCcnv (.cv f)))
        (synCdm (.cv f)) (synCrn (.cv f)))
      (synWa (.classEq (synCop (.cv r) (synCdm (.cv f))) (.cv u)) (.classEq
          (synCop (synCcom (synCcom (.cv f) (.cv r)) (synCcnv (.cv f))) (synCrn (.cv f)))
          (.cv v)))
  have p0002 :=
    @gSyl
      (synWa (synWa (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A)))
        (synWa (synWiso (.cv f) (.cv r)
            (synCcom (synCcom (.cv f) (.cv r)) (synCcnv (.cv f))) (synCdm (.cv f))
            (synCrn (.cv f))) (synWa (.classEq (synCop (.cv r) (synCdm (.cv f))) (.cv u))
            (.classEq (synCop (synCcom (synCcom (.cv f) (.cv r)) (synCcnv (.cv f)))
                (synCrn (.cv f))) (.cv v)))))
      (synWa (synWiso (.cv f) (.cv r) (synCcom (synCcom (.cv f) (.cv r)) (synCcnv (.cv f)))
          (synCdm (.cv f)) (synCrn (.cv f)))
        (synWa (.classEq (synCop (.cv r) (synCdm (.cv f))) (.cv u)) (.classEq
            (synCop (synCcom (synCcom (.cv f) (.cv r)) (synCcnv (.cv f))) (synCrn (.cv f)))
            (.cv v))))
      (synWiso (.cv f) (.cv r) (synCcom (synCcom (.cv f) (.cv r)) (synCcnv (.cv f)))
        (synCdm (.cv f)) (synCrn (.cv f)))
      p0000 p0001
  have p0004 :=
    @gSimpr
      (synWiso (.cv f) (.cv r) (synCcom (synCcom (.cv f) (.cv r)) (synCcnv (.cv f)))
        (synCdm (.cv f)) (synCrn (.cv f)))
      (synWa (.classEq (synCop (.cv r) (synCdm (.cv f))) (.cv u)) (.classEq
          (synCop (synCcom (synCcom (.cv f) (.cv r)) (synCcnv (.cv f))) (synCrn (.cv f)))
          (.cv v)))
  have p0005 :=
    @gSyl
      (synWa (synWa (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A)))
        (synWa (synWiso (.cv f) (.cv r)
            (synCcom (synCcom (.cv f) (.cv r)) (synCcnv (.cv f))) (synCdm (.cv f))
            (synCrn (.cv f))) (synWa (.classEq (synCop (.cv r) (synCdm (.cv f))) (.cv u))
            (.classEq (synCop (synCcom (synCcom (.cv f) (.cv r)) (synCcnv (.cv f)))
                (synCrn (.cv f))) (.cv v)))))
      (synWa (synWiso (.cv f) (.cv r) (synCcom (synCcom (.cv f) (.cv r)) (synCcnv (.cv f)))
          (synCdm (.cv f)) (synCrn (.cv f)))
        (synWa (.classEq (synCop (.cv r) (synCdm (.cv f))) (.cv u)) (.classEq
            (synCop (synCcom (synCcom (.cv f) (.cv r)) (synCcnv (.cv f))) (synCrn (.cv f)))
            (.cv v))))
      (synWa (.classEq (synCop (.cv r) (synCdm (.cv f))) (.cv u)) (.classEq
          (synCop (synCcom (synCcom (.cv f) (.cv r)) (synCcnv (.cv f))) (synCrn (.cv f)))
          (.cv v)))
      p0000 p0004
  have p0006 :=
    @gSimpl (.classEq (synCop (.cv r) (synCdm (.cv f))) (.cv u))
      (.classEq (synCop (synCcom (synCcom (.cv f) (.cv r)) (synCcnv (.cv f)))
          (synCrn (.cv f))) (.cv v))
  have p0007 :=
    @gSyl
      (synWa (synWa (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A)))
        (synWa (synWiso (.cv f) (.cv r)
            (synCcom (synCcom (.cv f) (.cv r)) (synCcnv (.cv f))) (synCdm (.cv f))
            (synCrn (.cv f))) (synWa (.classEq (synCop (.cv r) (synCdm (.cv f))) (.cv u))
            (.classEq (synCop (synCcom (synCcom (.cv f) (.cv r)) (synCcnv (.cv f)))
                (synCrn (.cv f))) (.cv v)))))
      (synWa (.classEq (synCop (.cv r) (synCdm (.cv f))) (.cv u)) (.classEq
          (synCop (synCcom (synCcom (.cv f) (.cv r)) (synCcnv (.cv f))) (synCrn (.cv f)))
          (.cv v)))
      (.classEq (synCop (.cv r) (synCdm (.cv f))) (.cv u)) p0005 p0006
  have p0008 :=
    @gSimpl (synWa (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A)))
      (synWa (synWiso (.cv f) (.cv r) (synCcom (synCcom (.cv f) (.cv r)) (synCcnv (.cv f)))
          (synCdm (.cv f)) (synCrn (.cv f)))
        (synWa (.classEq (synCop (.cv r) (synCdm (.cv f))) (.cv u)) (.classEq
            (synCop (synCcom (synCcom (.cv f) (.cv r)) (synCcnv (.cv f))) (synCrn (.cv f)))
            (.cv v))))
  have p0009 :=
    @gSimpl (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A))
  have p0010 :=
    @gSyl
      (synWa (synWa (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A)))
        (synWa (synWiso (.cv f) (.cv r)
            (synCcom (synCcom (.cv f) (.cv r)) (synCcnv (.cv f))) (synCdm (.cv f))
            (synCrn (.cv f))) (synWa (.classEq (synCop (.cv r) (synCdm (.cv f))) (.cv u))
            (.classEq (synCop (synCcom (synCcom (.cv f) (.cv r)) (synCcnv (.cv f)))
                (synCrn (.cv f))) (.cv v)))))
      (synWa (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A)))
      (.classMem (.cv u) (synChwcn A)) p0008 p0009
  have p0011 := @gHwcnpair u A
  have p0012 :=
    @gSyl
      (synWa (synWa (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A)))
        (synWa (synWiso (.cv f) (.cv r)
            (synCcom (synCcom (.cv f) (.cv r)) (synCcnv (.cv f))) (synCdm (.cv f))
            (synCrn (.cv f))) (synWa (.classEq (synCop (.cv r) (synCdm (.cv f))) (.cv u))
            (.classEq (synCop (synCcom (synCcom (.cv f) (.cv r)) (synCcnv (.cv f)))
                (synCrn (.cv f))) (.cv v)))))
      (.classMem (.cv u) (synChwcn A))
      (.classEq (.cv u) (synCop (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u))))
      p0010 p0011
  have p0013 :=
    @gEqtrd
      (synWa (synWa (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A)))
        (synWa (synWiso (.cv f) (.cv r)
            (synCcom (synCcom (.cv f) (.cv r)) (synCcnv (.cv f))) (synCdm (.cv f))
            (synCrn (.cv f))) (synWa (.classEq (synCop (.cv r) (synCdm (.cv f))) (.cv u))
            (.classEq (synCop (synCcom (synCcom (.cv f) (.cv r)) (synCcnv (.cv f)))
                (synCrn (.cv f))) (.cv v)))))
      (synCop (.cv r) (synCdm (.cv f))) (.cv u)
      (synCop (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u))) p0007 p0012
  have p0014 :=
    @gOpth (.cv r) (synCdm (.cv f)) (synCfv (synC1st) (.cv u))
      (synCfv (synC2nd) (.cv u))
  have p0015 :=
    @gBiimpi
      (.classEq (synCop (.cv r) (synCdm (.cv f)))
        (synCop (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u))))
      (synWa (.classEq (.cv r) (synCfv (synC1st) (.cv u)))
        (.classEq (synCdm (.cv f)) (synCfv (synC2nd) (.cv u))))
      p0014
  have p0016 :=
    @gSyl
      (synWa (synWa (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A)))
        (synWa (synWiso (.cv f) (.cv r)
            (synCcom (synCcom (.cv f) (.cv r)) (synCcnv (.cv f))) (synCdm (.cv f))
            (synCrn (.cv f))) (synWa (.classEq (synCop (.cv r) (synCdm (.cv f))) (.cv u))
            (.classEq (synCop (synCcom (synCcom (.cv f) (.cv r)) (synCcnv (.cv f)))
                (synCrn (.cv f))) (.cv v)))))
      (.classEq (synCop (.cv r) (synCdm (.cv f)))
        (synCop (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u))))
      (synWa (.classEq (.cv r) (synCfv (synC1st) (.cv u)))
        (.classEq (synCdm (.cv f)) (synCfv (synC2nd) (.cv u))))
      p0013 p0015
  have p0017 :=
    @gSimpl (.classEq (.cv r) (synCfv (synC1st) (.cv u)))
      (.classEq (synCdm (.cv f)) (synCfv (synC2nd) (.cv u)))
  have p0018 :=
    @gSyl
      (synWa (synWa (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A)))
        (synWa (synWiso (.cv f) (.cv r)
            (synCcom (synCcom (.cv f) (.cv r)) (synCcnv (.cv f))) (synCdm (.cv f))
            (synCrn (.cv f))) (synWa (.classEq (synCop (.cv r) (synCdm (.cv f))) (.cv u))
            (.classEq (synCop (synCcom (synCcom (.cv f) (.cv r)) (synCcnv (.cv f)))
                (synCrn (.cv f))) (.cv v)))))
      (synWa (.classEq (.cv r) (synCfv (synC1st) (.cv u)))
        (.classEq (synCdm (.cv f)) (synCfv (synC2nd) (.cv u))))
      (.classEq (.cv r) (synCfv (synC1st) (.cv u))) p0016 p0017
  have p0019 :=
    @gIsoeq2 (synCdm (.cv f)) (synCrn (.cv f)) (.cv r)
      (synCcom (synCcom (.cv f) (.cv r)) (synCcnv (.cv f)))
      (synCfv (synC1st) (.cv u)) (.cv f)
  have p0020 :=
    @gSyl
      (synWa (synWa (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A)))
        (synWa (synWiso (.cv f) (.cv r)
            (synCcom (synCcom (.cv f) (.cv r)) (synCcnv (.cv f))) (synCdm (.cv f))
            (synCrn (.cv f))) (synWa (.classEq (synCop (.cv r) (synCdm (.cv f))) (.cv u))
            (.classEq (synCop (synCcom (synCcom (.cv f) (.cv r)) (synCcnv (.cv f)))
                (synCrn (.cv f))) (.cv v)))))
      (.classEq (.cv r) (synCfv (synC1st) (.cv u)))
      (synWb (synWiso (.cv f) (.cv r) (synCcom (synCcom (.cv f) (.cv r)) (synCcnv (.cv f)))
          (synCdm (.cv f)) (synCrn (.cv f))) (synWiso (.cv f) (synCfv (synC1st) (.cv u))
          (synCcom (synCcom (.cv f) (.cv r)) (synCcnv (.cv f))) (synCdm (.cv f))
          (synCrn (.cv f))))
      p0018 p0019
  have p0024 :=
    @gSimpr (.classEq (synCop (.cv r) (synCdm (.cv f))) (.cv u))
      (.classEq (synCop (synCcom (synCcom (.cv f) (.cv r)) (synCcnv (.cv f)))
          (synCrn (.cv f))) (.cv v))
  have p0025 :=
    @gSyl
      (synWa (synWa (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A)))
        (synWa (synWiso (.cv f) (.cv r)
            (synCcom (synCcom (.cv f) (.cv r)) (synCcnv (.cv f))) (synCdm (.cv f))
            (synCrn (.cv f))) (synWa (.classEq (synCop (.cv r) (synCdm (.cv f))) (.cv u))
            (.classEq (synCop (synCcom (synCcom (.cv f) (.cv r)) (synCcnv (.cv f)))
                (synCrn (.cv f))) (.cv v)))))
      (synWa (.classEq (synCop (.cv r) (synCdm (.cv f))) (.cv u)) (.classEq
          (synCop (synCcom (synCcom (.cv f) (.cv r)) (synCcnv (.cv f))) (synCrn (.cv f)))
          (.cv v)))
      (.classEq (synCop (synCcom (synCcom (.cv f) (.cv r)) (synCcnv (.cv f)))
          (synCrn (.cv f))) (.cv v))
      p0005 p0024
  have p0027 :=
    @gSimpr (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A))
  have p0028 :=
    @gSyl
      (synWa (synWa (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A)))
        (synWa (synWiso (.cv f) (.cv r)
            (synCcom (synCcom (.cv f) (.cv r)) (synCcnv (.cv f))) (synCdm (.cv f))
            (synCrn (.cv f))) (synWa (.classEq (synCop (.cv r) (synCdm (.cv f))) (.cv u))
            (.classEq (synCop (synCcom (synCcom (.cv f) (.cv r)) (synCcnv (.cv f)))
                (synCrn (.cv f))) (.cv v)))))
      (synWa (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A)))
      (.classMem (.cv v) (synChwcn A)) p0008 p0027
  have p0029 := @gHwcnpair v A
  have p0030 :=
    @gSyl
      (synWa (synWa (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A)))
        (synWa (synWiso (.cv f) (.cv r)
            (synCcom (synCcom (.cv f) (.cv r)) (synCcnv (.cv f))) (synCdm (.cv f))
            (synCrn (.cv f))) (synWa (.classEq (synCop (.cv r) (synCdm (.cv f))) (.cv u))
            (.classEq (synCop (synCcom (synCcom (.cv f) (.cv r)) (synCcnv (.cv f)))
                (synCrn (.cv f))) (.cv v)))))
      (.classMem (.cv v) (synChwcn A))
      (.classEq (.cv v) (synCop (synCfv (synC1st) (.cv v)) (synCfv (synC2nd) (.cv v))))
      p0028 p0029
  have p0031 :=
    @gEqtrd
      (synWa (synWa (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A)))
        (synWa (synWiso (.cv f) (.cv r)
            (synCcom (synCcom (.cv f) (.cv r)) (synCcnv (.cv f))) (synCdm (.cv f))
            (synCrn (.cv f))) (synWa (.classEq (synCop (.cv r) (synCdm (.cv f))) (.cv u))
            (.classEq (synCop (synCcom (synCcom (.cv f) (.cv r)) (synCcnv (.cv f)))
                (synCrn (.cv f))) (.cv v)))))
      (synCop (synCcom (synCcom (.cv f) (.cv r)) (synCcnv (.cv f))) (synCrn (.cv f)))
      (.cv v) (synCop (synCfv (synC1st) (.cv v)) (synCfv (synC2nd) (.cv v))) p0025
      p0030
  have p0032 :=
    @gOpth (synCcom (synCcom (.cv f) (.cv r)) (synCcnv (.cv f))) (synCrn (.cv f))
      (synCfv (synC1st) (.cv v)) (synCfv (synC2nd) (.cv v))
  have p0033 :=
    @gBiimpi
      (.classEq (synCop (synCcom (synCcom (.cv f) (.cv r)) (synCcnv (.cv f)))
          (synCrn (.cv f)))
        (synCop (synCfv (synC1st) (.cv v)) (synCfv (synC2nd) (.cv v))))
      (synWa (.classEq (synCcom (synCcom (.cv f) (.cv r)) (synCcnv (.cv f)))
          (synCfv (synC1st) (.cv v)))
        (.classEq (synCrn (.cv f)) (synCfv (synC2nd) (.cv v))))
      p0032
  have p0034 :=
    @gSyl
      (synWa (synWa (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A)))
        (synWa (synWiso (.cv f) (.cv r)
            (synCcom (synCcom (.cv f) (.cv r)) (synCcnv (.cv f))) (synCdm (.cv f))
            (synCrn (.cv f))) (synWa (.classEq (synCop (.cv r) (synCdm (.cv f))) (.cv u))
            (.classEq (synCop (synCcom (synCcom (.cv f) (.cv r)) (synCcnv (.cv f)))
                (synCrn (.cv f))) (.cv v)))))
      (.classEq (synCop (synCcom (synCcom (.cv f) (.cv r)) (synCcnv (.cv f)))
          (synCrn (.cv f)))
        (synCop (synCfv (synC1st) (.cv v)) (synCfv (synC2nd) (.cv v))))
      (synWa (.classEq (synCcom (synCcom (.cv f) (.cv r)) (synCcnv (.cv f)))
          (synCfv (synC1st) (.cv v)))
        (.classEq (synCrn (.cv f)) (synCfv (synC2nd) (.cv v))))
      p0031 p0033
  have p0035 :=
    @gSimpl
      (.classEq (synCcom (synCcom (.cv f) (.cv r)) (synCcnv (.cv f)))
        (synCfv (synC1st) (.cv v)))
      (.classEq (synCrn (.cv f)) (synCfv (synC2nd) (.cv v)))
  have p0036 :=
    @gSyl
      (synWa (synWa (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A)))
        (synWa (synWiso (.cv f) (.cv r)
            (synCcom (synCcom (.cv f) (.cv r)) (synCcnv (.cv f))) (synCdm (.cv f))
            (synCrn (.cv f))) (synWa (.classEq (synCop (.cv r) (synCdm (.cv f))) (.cv u))
            (.classEq (synCop (synCcom (synCcom (.cv f) (.cv r)) (synCcnv (.cv f)))
                (synCrn (.cv f))) (.cv v)))))
      (synWa (.classEq (synCcom (synCcom (.cv f) (.cv r)) (synCcnv (.cv f)))
          (synCfv (synC1st) (.cv v)))
        (.classEq (synCrn (.cv f)) (synCfv (synC2nd) (.cv v))))
      (.classEq (synCcom (synCcom (.cv f) (.cv r)) (synCcnv (.cv f)))
        (synCfv (synC1st) (.cv v)))
      p0034 p0035
  have p0037 :=
    @gIsoeq3 (synCdm (.cv f)) (synCrn (.cv f)) (synCfv (synC1st) (.cv u))
      (synCcom (synCcom (.cv f) (.cv r)) (synCcnv (.cv f)))
      (synCfv (synC1st) (.cv v)) (.cv f)
  have p0038 :=
    @gSyl
      (synWa (synWa (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A)))
        (synWa (synWiso (.cv f) (.cv r)
            (synCcom (synCcom (.cv f) (.cv r)) (synCcnv (.cv f))) (synCdm (.cv f))
            (synCrn (.cv f))) (synWa (.classEq (synCop (.cv r) (synCdm (.cv f))) (.cv u))
            (.classEq (synCop (synCcom (synCcom (.cv f) (.cv r)) (synCcnv (.cv f)))
                (synCrn (.cv f))) (.cv v)))))
      (.classEq (synCcom (synCcom (.cv f) (.cv r)) (synCcnv (.cv f)))
        (synCfv (synC1st) (.cv v)))
      (synWb (synWiso (.cv f) (synCfv (synC1st) (.cv u))
          (synCcom (synCcom (.cv f) (.cv r)) (synCcnv (.cv f))) (synCdm (.cv f))
          (synCrn (.cv f)))
        (synWiso (.cv f) (synCfv (synC1st) (.cv u)) (synCfv (synC1st) (.cv v))
          (synCdm (.cv f)) (synCrn (.cv f))))
      p0036 p0037
  have p0039 :=
    @gBitrd
      (synWa (synWa (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A)))
        (synWa (synWiso (.cv f) (.cv r)
            (synCcom (synCcom (.cv f) (.cv r)) (synCcnv (.cv f))) (synCdm (.cv f))
            (synCrn (.cv f))) (synWa (.classEq (synCop (.cv r) (synCdm (.cv f))) (.cv u))
            (.classEq (synCop (synCcom (synCcom (.cv f) (.cv r)) (synCcnv (.cv f)))
                (synCrn (.cv f))) (.cv v)))))
      (synWiso (.cv f) (.cv r) (synCcom (synCcom (.cv f) (.cv r)) (synCcnv (.cv f)))
        (synCdm (.cv f)) (synCrn (.cv f)))
      (synWiso (.cv f) (synCfv (synC1st) (.cv u))
        (synCcom (synCcom (.cv f) (.cv r)) (synCcnv (.cv f))) (synCdm (.cv f))
        (synCrn (.cv f)))
      (synWiso (.cv f) (synCfv (synC1st) (.cv u)) (synCfv (synC1st) (.cv v))
        (synCdm (.cv f)) (synCrn (.cv f)))
      p0020 p0038
  have p0054 :=
    @gSimpr (.classEq (.cv r) (synCfv (synC1st) (.cv u)))
      (.classEq (synCdm (.cv f)) (synCfv (synC2nd) (.cv u)))
  have p0055 :=
    @gSyl
      (synWa (synWa (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A)))
        (synWa (synWiso (.cv f) (.cv r)
            (synCcom (synCcom (.cv f) (.cv r)) (synCcnv (.cv f))) (synCdm (.cv f))
            (synCrn (.cv f))) (synWa (.classEq (synCop (.cv r) (synCdm (.cv f))) (.cv u))
            (.classEq (synCop (synCcom (synCcom (.cv f) (.cv r)) (synCcnv (.cv f)))
                (synCrn (.cv f))) (.cv v)))))
      (synWa (.classEq (.cv r) (synCfv (synC1st) (.cv u)))
        (.classEq (synCdm (.cv f)) (synCfv (synC2nd) (.cv u))))
      (.classEq (synCdm (.cv f)) (synCfv (synC2nd) (.cv u))) p0016 p0054
  have p0056 :=
    @gIsoeq4 (synCdm (.cv f)) (synCrn (.cv f)) (synCfv (synC2nd) (.cv u))
      (synCfv (synC1st) (.cv u)) (synCfv (synC1st) (.cv v)) (.cv f)
  have p0057 :=
    @gSyl
      (synWa (synWa (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A)))
        (synWa (synWiso (.cv f) (.cv r)
            (synCcom (synCcom (.cv f) (.cv r)) (synCcnv (.cv f))) (synCdm (.cv f))
            (synCrn (.cv f))) (synWa (.classEq (synCop (.cv r) (synCdm (.cv f))) (.cv u))
            (.classEq (synCop (synCcom (synCcom (.cv f) (.cv r)) (synCcnv (.cv f)))
                (synCrn (.cv f))) (.cv v)))))
      (.classEq (synCdm (.cv f)) (synCfv (synC2nd) (.cv u)))
      (synWb (synWiso (.cv f) (synCfv (synC1st) (.cv u)) (synCfv (synC1st) (.cv v))
          (synCdm (.cv f)) (synCrn (.cv f)))
        (synWiso (.cv f) (synCfv (synC1st) (.cv u)) (synCfv (synC1st) (.cv v))
          (synCfv (synC2nd) (.cv u)) (synCrn (.cv f))))
      p0055 p0056
  have p0058 :=
    @gBitrd
      (synWa (synWa (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A)))
        (synWa (synWiso (.cv f) (.cv r)
            (synCcom (synCcom (.cv f) (.cv r)) (synCcnv (.cv f))) (synCdm (.cv f))
            (synCrn (.cv f))) (synWa (.classEq (synCop (.cv r) (synCdm (.cv f))) (.cv u))
            (.classEq (synCop (synCcom (synCcom (.cv f) (.cv r)) (synCcnv (.cv f)))
                (synCrn (.cv f))) (.cv v)))))
      (synWiso (.cv f) (.cv r) (synCcom (synCcom (.cv f) (.cv r)) (synCcnv (.cv f)))
        (synCdm (.cv f)) (synCrn (.cv f)))
      (synWiso (.cv f) (synCfv (synC1st) (.cv u)) (synCfv (synC1st) (.cv v))
        (synCdm (.cv f)) (synCrn (.cv f)))
      (synWiso (.cv f) (synCfv (synC1st) (.cv u)) (synCfv (synC1st) (.cv v))
        (synCfv (synC2nd) (.cv u)) (synCrn (.cv f)))
      p0039 p0057
  have p0073 :=
    @gSimpr
      (.classEq (synCcom (synCcom (.cv f) (.cv r)) (synCcnv (.cv f)))
        (synCfv (synC1st) (.cv v)))
      (.classEq (synCrn (.cv f)) (synCfv (synC2nd) (.cv v)))
  have p0074 :=
    @gSyl
      (synWa (synWa (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A)))
        (synWa (synWiso (.cv f) (.cv r)
            (synCcom (synCcom (.cv f) (.cv r)) (synCcnv (.cv f))) (synCdm (.cv f))
            (synCrn (.cv f))) (synWa (.classEq (synCop (.cv r) (synCdm (.cv f))) (.cv u))
            (.classEq (synCop (synCcom (synCcom (.cv f) (.cv r)) (synCcnv (.cv f)))
                (synCrn (.cv f))) (.cv v)))))
      (synWa (.classEq (synCcom (synCcom (.cv f) (.cv r)) (synCcnv (.cv f)))
          (synCfv (synC1st) (.cv v)))
        (.classEq (synCrn (.cv f)) (synCfv (synC2nd) (.cv v))))
      (.classEq (synCrn (.cv f)) (synCfv (synC2nd) (.cv v))) p0034 p0073
  have p0075 :=
    @gIsoeq5 (synCfv (synC2nd) (.cv u)) (synCrn (.cv f)) (synCfv (synC2nd) (.cv v))
      (synCfv (synC1st) (.cv u)) (synCfv (synC1st) (.cv v)) (.cv f)
  have p0076 :=
    @gSyl
      (synWa (synWa (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A)))
        (synWa (synWiso (.cv f) (.cv r)
            (synCcom (synCcom (.cv f) (.cv r)) (synCcnv (.cv f))) (synCdm (.cv f))
            (synCrn (.cv f))) (synWa (.classEq (synCop (.cv r) (synCdm (.cv f))) (.cv u))
            (.classEq (synCop (synCcom (synCcom (.cv f) (.cv r)) (synCcnv (.cv f)))
                (synCrn (.cv f))) (.cv v)))))
      (.classEq (synCrn (.cv f)) (synCfv (synC2nd) (.cv v)))
      (synWb (synWiso (.cv f) (synCfv (synC1st) (.cv u)) (synCfv (synC1st) (.cv v))
          (synCfv (synC2nd) (.cv u)) (synCrn (.cv f)))
        (synWiso (.cv f) (synCfv (synC1st) (.cv u)) (synCfv (synC1st) (.cv v))
          (synCfv (synC2nd) (.cv u)) (synCfv (synC2nd) (.cv v))))
      p0074 p0075
  have p0077 :=
    @gBitrd
      (synWa (synWa (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A)))
        (synWa (synWiso (.cv f) (.cv r)
            (synCcom (synCcom (.cv f) (.cv r)) (synCcnv (.cv f))) (synCdm (.cv f))
            (synCrn (.cv f))) (synWa (.classEq (synCop (.cv r) (synCdm (.cv f))) (.cv u))
            (.classEq (synCop (synCcom (synCcom (.cv f) (.cv r)) (synCcnv (.cv f)))
                (synCrn (.cv f))) (.cv v)))))
      (synWiso (.cv f) (.cv r) (synCcom (synCcom (.cv f) (.cv r)) (synCcnv (.cv f)))
        (synCdm (.cv f)) (synCrn (.cv f)))
      (synWiso (.cv f) (synCfv (synC1st) (.cv u)) (synCfv (synC1st) (.cv v))
        (synCfv (synC2nd) (.cv u)) (synCrn (.cv f)))
      (synWiso (.cv f) (synCfv (synC1st) (.cv u)) (synCfv (synC1st) (.cv v))
        (synCfv (synC2nd) (.cv u)) (synCfv (synC2nd) (.cv v)))
      p0058 p0076
  have p0078 :=
    @gBiimpd
      (synWa (synWa (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A)))
        (synWa (synWiso (.cv f) (.cv r)
            (synCcom (synCcom (.cv f) (.cv r)) (synCcnv (.cv f))) (synCdm (.cv f))
            (synCrn (.cv f))) (synWa (.classEq (synCop (.cv r) (synCdm (.cv f))) (.cv u))
            (.classEq (synCop (synCcom (synCcom (.cv f) (.cv r)) (synCcnv (.cv f)))
                (synCrn (.cv f))) (.cv v)))))
      (synWiso (.cv f) (.cv r) (synCcom (synCcom (.cv f) (.cv r)) (synCcnv (.cv f)))
        (synCdm (.cv f)) (synCrn (.cv f)))
      (synWiso (.cv f) (synCfv (synC1st) (.cv u)) (synCfv (synC1st) (.cv v))
        (synCfv (synC2nd) (.cv u)) (synCfv (synC2nd) (.cv v)))
      p0077
  have p0079 :=
    @gMpd
      (synWa (synWa (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A)))
        (synWa (synWiso (.cv f) (.cv r)
            (synCcom (synCcom (.cv f) (.cv r)) (synCcnv (.cv f))) (synCdm (.cv f))
            (synCrn (.cv f))) (synWa (.classEq (synCop (.cv r) (synCdm (.cv f))) (.cv u))
            (.classEq (synCop (synCcom (synCcom (.cv f) (.cv r)) (synCcnv (.cv f)))
                (synCrn (.cv f))) (.cv v)))))
      (synWiso (.cv f) (.cv r) (synCcom (synCcom (.cv f) (.cv r)) (synCcnv (.cv f)))
        (synCdm (.cv f)) (synCrn (.cv f)))
      (synWiso (.cv f) (synCfv (synC1st) (.cv u)) (synCfv (synC1st) (.cv v))
        (synCfv (synC2nd) (.cv u)) (synCfv (synC2nd) (.cv v)))
      p0002 p0078
  exact p0079

/-- Checked nominal proof certificate identified upstream as `g_hwnisowitnessb`. -/
@[expose]
noncomputable def gHwnisowitnessb (v : Var) (u : Var) (A : Class) (f : Var) (r : Var)
    (dv_A_f : f ∉ A.fv) (dv_A_r : r ∉ A.fv) (dv_f_r : f ≠ r) (dv_f_u : f ≠ u)
    (dv_f_v : f ≠ v) (dv_r_u : r ≠ u) (dv_r_v : r ≠ v) (dv_u_v : u ≠ v) :
    Nominal.NPrf
      (.imp (synWa (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A))) (synWb
          (synWex f (synWrex r (synCvv) (synWa (synWiso (.cv f) (.cv r)
                  (synCcom (synCcom (.cv f) (.cv r)) (synCcnv (.cv f)))
                  (synCdm (.cv f)) (synCrn (.cv f)))
                (synWa (.classEq (synCop (.cv r) (synCdm (.cv f))) (.cv u)) (.classEq
                    (synCop (synCcom (synCcom (.cv f) (.cv r)) (synCcnv (.cv f)))
                      (synCrn (.cv f))) (.cv v)))))) (synWex f
            (synWiso (.cv f) (synCfv (synC1st) (.cv u)) (synCfv (synC1st) (.cv v))
              (synCfv (synC2nd) (.cv u)) (synCfv (synC2nd) (.cv v)))))) :=
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
      ((synWiso (.cv f) (synCfv (synC1st) (.cv u)) (synCfv (synC1st) (.cv v))
          (synCfv (synC2nd) (.cv u)) (synCfv (synC2nd) (.cv v)))).fv :=
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
      ((synWa (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A)))).fv :=
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
      ((synWa (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A)))).fv :=
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
    @gHwnisogenrawi v u A f r dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
      dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008
  have p0001 :=
    @gEx (synWa (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A)))
      (synWa (synWiso (.cv f) (.cv r) (synCcom (synCcom (.cv f) (.cv r)) (synCcnv (.cv f)))
          (synCdm (.cv f)) (synCrn (.cv f)))
        (synWa (.classEq (synCop (.cv r) (synCdm (.cv f))) (.cv u)) (.classEq
            (synCop (synCcom (synCcom (.cv f) (.cv r)) (synCcnv (.cv f))) (synCrn (.cv f)))
            (.cv v))))
      (synWiso (.cv f) (synCfv (synC1st) (.cv u)) (synCfv (synC1st) (.cv v))
        (synCfv (synC2nd) (.cv u)) (synCfv (synC2nd) (.cv v)))
      p0000
  have p0002 :=
    @gRexlimdvw
      (synWa (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A)))
      (synWa (synWiso (.cv f) (.cv r) (synCcom (synCcom (.cv f) (.cv r)) (synCcnv (.cv f)))
          (synCdm (.cv f)) (synCrn (.cv f)))
        (synWa (.classEq (synCop (.cv r) (synCdm (.cv f))) (.cv u)) (.classEq
            (synCop (synCcom (synCcom (.cv f) (.cv r)) (synCcnv (.cv f))) (synCrn (.cv f)))
            (.cv v))))
      (synWiso (.cv f) (synCfv (synC1st) (.cv u)) (synCfv (synC1st) (.cv v))
        (synCfv (synC2nd) (.cv u)) (synCfv (synC2nd) (.cv v)))
      r (synCvv) dv_cache_0009 dv_cache_0010 p0001
  have p0003 :=
    @gHwnisorawgeni v u A f r dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
      dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008
  have p0004 :=
    @gEx (synWa (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A)))
      (synWiso (.cv f) (synCfv (synC1st) (.cv u)) (synCfv (synC1st) (.cv v))
        (synCfv (synC2nd) (.cv u)) (synCfv (synC2nd) (.cv v)))
      (synWrex r (synCvv) (synWa (synWiso (.cv f) (.cv r)
            (synCcom (synCcom (.cv f) (.cv r)) (synCcnv (.cv f))) (synCdm (.cv f))
            (synCrn (.cv f))) (synWa (.classEq (synCop (.cv r) (synCdm (.cv f))) (.cv u))
            (.classEq (synCop (synCcom (synCcom (.cv f) (.cv r)) (synCcnv (.cv f)))
                (synCrn (.cv f))) (.cv v)))))
      p0003
  have p0005 :=
    @gImpbid (synWa (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A)))
      (synWrex r (synCvv) (synWa (synWiso (.cv f) (.cv r)
            (synCcom (synCcom (.cv f) (.cv r)) (synCcnv (.cv f))) (synCdm (.cv f))
            (synCrn (.cv f))) (synWa (.classEq (synCop (.cv r) (synCdm (.cv f))) (.cv u))
            (.classEq (synCop (synCcom (synCcom (.cv f) (.cv r)) (synCcnv (.cv f)))
                (synCrn (.cv f))) (.cv v)))))
      (synWiso (.cv f) (synCfv (synC1st) (.cv u)) (synCfv (synC1st) (.cv v))
        (synCfv (synC2nd) (.cv u)) (synCfv (synC2nd) (.cv v)))
      p0002 p0004
  have p0006 :=
    @gExbidv (synWa (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A)))
      (synWrex r (synCvv) (synWa (synWiso (.cv f) (.cv r)
            (synCcom (synCcom (.cv f) (.cv r)) (synCcnv (.cv f))) (synCdm (.cv f))
            (synCrn (.cv f))) (synWa (.classEq (synCop (.cv r) (synCdm (.cv f))) (.cv u))
            (.classEq (synCop (synCcom (synCcom (.cv f) (.cv r)) (synCcnv (.cv f)))
                (synCrn (.cv f))) (.cv v)))))
      (synWiso (.cv f) (synCfv (synC1st) (.cv u)) (synCfv (synC1st) (.cv v))
        (synCfv (synC2nd) (.cv u)) (synCfv (synC2nd) (.cv v)))
      f dv_cache_0011 p0005
  exact p0006

/-- Checked nominal proof certificate identified upstream as `g_hwnisohwisob`. -/
@[expose]
noncomputable def gHwnisohwisob (v : Var) (u : Var) (A : Class) (dv_u_v : u ≠ v) :
    Nominal.NPrf
      (synWb (synWbr (.cv u) (synChwniso A) (.cv v)) (synWa
          (synWa (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A)))
          (synWbr (.cv u) (synChwiso A) (.cv v)))) :=
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
    @gElhwnisogeniso v u A f r dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
      dv_cache_0005 dv_cache_0006 dv_cache_0007
  have p0001 :=
    @gHwnisowitnessb v u A f r dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
      dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008
  have p0002 :=
    @gPm532i
      (synWa (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A)))
      (synWex f (synWrex r (synCvv) (synWa (synWiso (.cv f) (.cv r)
              (synCcom (synCcom (.cv f) (.cv r)) (synCcnv (.cv f))) (synCdm (.cv f))
              (synCrn (.cv f))) (synWa (.classEq (synCop (.cv r) (synCdm (.cv f))) (.cv u))
              (.classEq (synCop (synCcom (synCcom (.cv f) (.cv r)) (synCcnv (.cv f)))
                  (synCrn (.cv f))) (.cv v))))))
      (synWex f (synWiso (.cv f) (synCfv (synC1st) (.cv u)) (synCfv (synC1st) (.cv v))
          (synCfv (synC2nd) (.cv u)) (synCfv (synC2nd) (.cv v))))
      p0001
  have p0003 :=
    @gBitri (synWbr (.cv u) (synChwniso A) (.cv v))
      (synWa (synWa (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A)))
        (synWex f (synWrex r (synCvv) (synWa (synWiso (.cv f) (.cv r)
                (synCcom (synCcom (.cv f) (.cv r)) (synCcnv (.cv f))) (synCdm (.cv f))
                (synCrn (.cv f)))
              (synWa (.classEq (synCop (.cv r) (synCdm (.cv f))) (.cv u)) (.classEq
                  (synCop (synCcom (synCcom (.cv f) (.cv r)) (synCcnv (.cv f)))
                    (synCrn (.cv f))) (.cv v)))))))
      (synWa (synWa (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A)))
        (synWex f (synWiso (.cv f) (synCfv (synC1st) (.cv u)) (synCfv (synC1st) (.cv v))
            (synCfv (synC2nd) (.cv u)) (synCfv (synC2nd) (.cv v)))))
      p0000 p0002
  have p0004 :=
    @gSimpl (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A))
  have p0005 := @gHwcnraw u A
  have p0006 :=
    @gSyl (synWa (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A)))
      (.classMem (.cv u) (synChwcn A)) (.classMem (.cv u) (synChwcodes A)) p0004 p0005
  have p0007 :=
    @gSimpr (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A))
  have p0008 := @gHwcnraw v A
  have p0009 :=
    @gSyl (synWa (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A)))
      (.classMem (.cv v) (synChwcn A)) (.classMem (.cv v) (synChwcodes A)) p0007 p0008
  have p0010 :=
    @gJca (synWa (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A)))
      (.classMem (.cv u) (synChwcodes A)) (.classMem (.cv v) (synChwcodes A)) p0006
      p0009
  have p0011 :=
    @gBiantrurd
      (synWa (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A)))
      (synWa (.classMem (.cv u) (synChwcodes A)) (.classMem (.cv v) (synChwcodes A)))
      (synWex f (synWiso (.cv f) (synCfv (synC1st) (.cv u)) (synCfv (synC1st) (.cv v))
          (synCfv (synC2nd) (.cv u)) (synCfv (synC2nd) (.cv v))))
      p0010
  have p0012 := @gBrhwisoany v u A f dv_cache_0001 dv_cache_0004 dv_cache_0005
  have p0013 :=
    @gBicomi (synWbr (.cv u) (synChwiso A) (.cv v))
      (synWa (synWa (.classMem (.cv u) (synChwcodes A)) (.classMem (.cv v) (synChwcodes A)))
        (synWex f (synWiso (.cv f) (synCfv (synC1st) (.cv u)) (synCfv (synC1st) (.cv v))
            (synCfv (synC2nd) (.cv u)) (synCfv (synC2nd) (.cv v)))))
      p0012
  have p0014 :=
    @gA1i
      (synWb (synWa (synWa (.classMem (.cv u) (synChwcodes A))
            (.classMem (.cv v) (synChwcodes A))) (synWex f
            (synWiso (.cv f) (synCfv (synC1st) (.cv u)) (synCfv (synC1st) (.cv v))
              (synCfv (synC2nd) (.cv u)) (synCfv (synC2nd) (.cv v)))))
        (synWbr (.cv u) (synChwiso A) (.cv v)))
      (synWa (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A))) p0013
  have p0015 :=
    @gBitrd (synWa (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A)))
      (synWex f (synWiso (.cv f) (synCfv (synC1st) (.cv u)) (synCfv (synC1st) (.cv v))
          (synCfv (synC2nd) (.cv u)) (synCfv (synC2nd) (.cv v))))
      (synWa (synWa (.classMem (.cv u) (synChwcodes A)) (.classMem (.cv v) (synChwcodes A)))
        (synWex f (synWiso (.cv f) (synCfv (synC1st) (.cv u)) (synCfv (synC1st) (.cv v))
            (synCfv (synC2nd) (.cv u)) (synCfv (synC2nd) (.cv v)))))
      (synWbr (.cv u) (synChwiso A) (.cv v)) p0011 p0014
  have p0016 :=
    @gPm532i
      (synWa (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A)))
      (synWex f (synWiso (.cv f) (synCfv (synC1st) (.cv u)) (synCfv (synC1st) (.cv v))
          (synCfv (synC2nd) (.cv u)) (synCfv (synC2nd) (.cv v))))
      (synWbr (.cv u) (synChwiso A) (.cv v)) p0015
  have p0017 :=
    @gBitri (synWbr (.cv u) (synChwniso A) (.cv v))
      (synWa (synWa (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A)))
        (synWex f (synWiso (.cv f) (synCfv (synC1st) (.cv u)) (synCfv (synC1st) (.cv v))
            (synCfv (synC2nd) (.cv u)) (synCfv (synC2nd) (.cv v)))))
      (synWa (synWa (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A)))
        (synWbr (.cv u) (synChwiso A) (.cv v)))
      p0003 p0016
  exact p0017

/-- Checked nominal proof certificate identified upstream as `g_hwcnexg`. -/
@[expose]
noncomputable def gHwcnexg (A : Class) :
    Nominal.NPrf (.imp (.classMem A (synCvv)) (.classMem (synChwcn A) (synCvv))) :=
  by
  have p0000 := (Nominal.classEqRefl (synChwcn A))
  have p0001 := @gHwcodesexg A (synCvv)
  have p0002 := @gHwrelsex
  have p0003 := @gA1i (.classMem (synChwrels) (synCvv)) (.classMem A (synCvv)) p0002
  have p0004 :=
    @gJca (.classMem A (synCvv)) (.classMem (synChwcodes A) (synCvv))
      (.classMem (synChwrels) (synCvv)) p0001 p0003
  have p0005 := @gInexg (synChwcodes A) (synChwrels) (synCvv) (synCvv)
  have p0006 :=
    @gSyl (.classMem A (synCvv))
      (synWa (.classMem (synChwcodes A) (synCvv)) (.classMem (synChwrels) (synCvv)))
      (.classMem (synCin (synChwcodes A) (synChwrels)) (synCvv)) p0004 p0005
  have p0007 :=
    @gSyl5eqel (.classMem A (synCvv)) (synChwcn A)
      (synCin (synChwcodes A) (synChwrels)) (synCvv) p0000 p0006
  exact p0007

/-- Checked nominal proof certificate identified upstream as `g_hwnisoexg`. -/
@[expose]
noncomputable def gHwnisoexg (A : Class) :
    Nominal.NPrf (.imp (.classMem A (synCvv)) (.classMem (synChwniso A) (synCvv))) :=
  by
  have p0000 := (Nominal.classEqRefl (synChwniso A))
  have p0001 := @gHwgenex
  have p0002 := @gHwbijex
  have p0003 := @gVvex
  have p0004 := @gXpex (synChwbij) (synCvv) p0002 p0003
  have p0005 := @gImaex (synChwgen) (synCxp (synChwbij) (synCvv)) p0001 p0004
  have p0006 :=
    @gA1i (.classMem (synCima (synChwgen) (synCxp (synChwbij) (synCvv))) (synCvv))
      (.classMem A (synCvv)) p0005
  have p0007 := (Nominal.classEqRefl (synChwcn A))
  have p0008 := @gHwcodesexg A (synCvv)
  have p0009 := @gHwrelsex
  have p0010 := @gA1i (.classMem (synChwrels) (synCvv)) (.classMem A (synCvv)) p0009
  have p0011 :=
    @gJca (.classMem A (synCvv)) (.classMem (synChwcodes A) (synCvv))
      (.classMem (synChwrels) (synCvv)) p0008 p0010
  have p0012 := @gInexg (synChwcodes A) (synChwrels) (synCvv) (synCvv)
  have p0013 :=
    @gSyl (.classMem A (synCvv))
      (synWa (.classMem (synChwcodes A) (synCvv)) (.classMem (synChwrels) (synCvv)))
      (.classMem (synCin (synChwcodes A) (synChwrels)) (synCvv)) p0011 p0012
  have p0014 :=
    @gSyl5eqel (.classMem A (synCvv)) (synChwcn A)
      (synCin (synChwcodes A) (synChwrels)) (synCvv) p0007 p0013
  have p0023 :=
    @gJca (.classMem A (synCvv)) (.classMem (synChwcn A) (synCvv))
      (.classMem (synChwcn A) (synCvv)) p0014 p0014
  have p0024 := @gXpexg (synChwcn A) (synChwcn A) (synCvv) (synCvv)
  have p0025 :=
    @gSyl (.classMem A (synCvv))
      (synWa (.classMem (synChwcn A) (synCvv)) (.classMem (synChwcn A) (synCvv)))
      (.classMem (synCxp (synChwcn A) (synChwcn A)) (synCvv)) p0023 p0024
  have p0026 :=
    @gJca (.classMem A (synCvv))
      (.classMem (synCima (synChwgen) (synCxp (synChwbij) (synCvv))) (synCvv))
      (.classMem (synCxp (synChwcn A) (synChwcn A)) (synCvv)) p0006 p0025
  have p0027 :=
    @gInexg (synCima (synChwgen) (synCxp (synChwbij) (synCvv)))
      (synCxp (synChwcn A) (synChwcn A)) (synCvv) (synCvv)
  have p0028 :=
    @gSyl (.classMem A (synCvv))
      (synWa (.classMem (synCima (synChwgen) (synCxp (synChwbij) (synCvv))) (synCvv))
        (.classMem (synCxp (synChwcn A) (synChwcn A)) (synCvv)))
      (.classMem (synCin (synCima (synChwgen) (synCxp (synChwbij) (synCvv)))
          (synCxp (synChwcn A) (synChwcn A))) (synCvv))
      p0026 p0027
  have p0029 :=
    @gSyl5eqel (.classMem A (synCvv)) (synChwniso A)
      (synCin (synCima (synChwgen) (synCxp (synChwbij) (synCvv)))
        (synCxp (synChwcn A) (synChwcn A)))
      (synCvv) p0000 p0028
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

/-- Checked nominal proof certificate identified upstream as `g_hwnisosymi`. -/
@[expose]
noncomputable def gHwnisosymi (v : Var) (u : Var) (A : Class) (dv_A_u : u ∉ A.fv)
    (dv_A_v : v ∉ A.fv) (dv_u_v : u ≠ v) :
    Nominal.NPrf
      (.imp (synWbr (.cv u) (synChwniso A) (.cv v))
        (synWbr (.cv v) (synChwniso A) (.cv u))) :=
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
  have p0000 := @gHwnisohwisob v u A dv_cache_0001
  have p0001 :=
    @gBiimpi (synWbr (.cv u) (synChwniso A) (.cv v))
      (synWa (synWa (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A)))
        (synWbr (.cv u) (synChwiso A) (.cv v)))
      p0000
  have p0002 :=
    @gSimpld (synWbr (.cv u) (synChwniso A) (.cv v))
      (synWa (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A)))
      (synWbr (.cv u) (synChwiso A) (.cv v)) p0001
  have p0003 :=
    @gAncom (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A))
  have p0004 :=
    @gBiimpi (synWa (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A)))
      (synWa (.classMem (.cv v) (synChwcn A)) (.classMem (.cv u) (synChwcn A))) p0003
  have p0005 :=
    @gSyl (synWbr (.cv u) (synChwniso A) (.cv v))
      (synWa (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A)))
      (synWa (.classMem (.cv v) (synChwcn A)) (.classMem (.cv u) (synChwcn A))) p0002
      p0004
  have p0008 :=
    @gSimprd (synWbr (.cv u) (synChwniso A) (.cv v))
      (synWa (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A)))
      (synWbr (.cv u) (synChwiso A) (.cv v)) p0001
  have p0009 := @gHwisosymi v u A dv_cache_0002 dv_cache_0003 dv_cache_0001
  have p0010 :=
    @gSyl (synWbr (.cv u) (synChwniso A) (.cv v))
      (synWbr (.cv u) (synChwiso A) (.cv v)) (synWbr (.cv v) (synChwiso A) (.cv u))
      p0008 p0009
  have p0011 :=
    @gJca (synWbr (.cv u) (synChwniso A) (.cv v))
      (synWa (.classMem (.cv v) (synChwcn A)) (.classMem (.cv u) (synChwcn A)))
      (synWbr (.cv v) (synChwiso A) (.cv u)) p0005 p0010
  have p0012 := @gHwnisohwisob u v A dv_cache_0004
  have p0013 :=
    @gBiimpri (synWbr (.cv v) (synChwniso A) (.cv u))
      (synWa (synWa (.classMem (.cv v) (synChwcn A)) (.classMem (.cv u) (synChwcn A)))
        (synWbr (.cv v) (synChwiso A) (.cv u)))
      p0012
  have p0014 :=
    @gSyl (synWbr (.cv u) (synChwniso A) (.cv v))
      (synWa (synWa (.classMem (.cv v) (synChwcn A)) (.classMem (.cv u) (synChwcn A)))
        (synWbr (.cv v) (synChwiso A) (.cv u)))
      (synWbr (.cv v) (synChwniso A) (.cv u)) p0011 p0013
  exact p0014

/-- Checked nominal proof certificate identified upstream as `g_hwnisotri`. -/
@[expose]
noncomputable def gHwnisotri (w : Var) (v : Var) (u : Var) (A : Class)
    (dv_A_u : u ∉ A.fv) (dv_A_v : v ∉ A.fv) (dv_A_w : w ∉ A.fv) (dv_u_v : u ≠ v)
    (dv_u_w : u ≠ w) (dv_v_w : v ≠ w) :
    Nominal.NPrf
      (.imp (synWa (synWbr (.cv u) (synChwniso A) (.cv v))
          (synWbr (.cv v) (synChwniso A) (.cv w)))
        (synWbr (.cv u) (synChwniso A) (.cv w))) :=
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
    @gSimpl (synWbr (.cv u) (synChwniso A) (.cv v))
      (synWbr (.cv v) (synChwniso A) (.cv w))
  have p0001 := @gHwnisohwisob v u A dv_cache_0001
  have p0002 :=
    @gBiimpi (synWbr (.cv u) (synChwniso A) (.cv v))
      (synWa (synWa (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A)))
        (synWbr (.cv u) (synChwiso A) (.cv v)))
      p0001
  have p0003 :=
    @gSyl
      (synWa (synWbr (.cv u) (synChwniso A) (.cv v))
        (synWbr (.cv v) (synChwniso A) (.cv w)))
      (synWbr (.cv u) (synChwniso A) (.cv v))
      (synWa (synWa (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A)))
        (synWbr (.cv u) (synChwiso A) (.cv v)))
      p0000 p0002
  have p0004 :=
    @gSimpl (synWa (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A)))
      (synWbr (.cv u) (synChwiso A) (.cv v))
  have p0005 :=
    @gSyl
      (synWa (synWbr (.cv u) (synChwniso A) (.cv v))
        (synWbr (.cv v) (synChwniso A) (.cv w)))
      (synWa (synWa (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A)))
        (synWbr (.cv u) (synChwiso A) (.cv v)))
      (synWa (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A))) p0003
      p0004
  have p0006 :=
    @gSimpl (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A))
  have p0007 :=
    @gSyl
      (synWa (synWbr (.cv u) (synChwniso A) (.cv v))
        (synWbr (.cv v) (synChwniso A) (.cv w)))
      (synWa (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A)))
      (.classMem (.cv u) (synChwcn A)) p0005 p0006
  have p0008 :=
    @gSimpr (synWbr (.cv u) (synChwniso A) (.cv v))
      (synWbr (.cv v) (synChwniso A) (.cv w))
  have p0009 := @gHwnisohwisob w v A dv_cache_0002
  have p0010 :=
    @gBiimpi (synWbr (.cv v) (synChwniso A) (.cv w))
      (synWa (synWa (.classMem (.cv v) (synChwcn A)) (.classMem (.cv w) (synChwcn A)))
        (synWbr (.cv v) (synChwiso A) (.cv w)))
      p0009
  have p0011 :=
    @gSyl
      (synWa (synWbr (.cv u) (synChwniso A) (.cv v))
        (synWbr (.cv v) (synChwniso A) (.cv w)))
      (synWbr (.cv v) (synChwniso A) (.cv w))
      (synWa (synWa (.classMem (.cv v) (synChwcn A)) (.classMem (.cv w) (synChwcn A)))
        (synWbr (.cv v) (synChwiso A) (.cv w)))
      p0008 p0010
  have p0012 :=
    @gSimpl (synWa (.classMem (.cv v) (synChwcn A)) (.classMem (.cv w) (synChwcn A)))
      (synWbr (.cv v) (synChwiso A) (.cv w))
  have p0013 :=
    @gSyl
      (synWa (synWbr (.cv u) (synChwniso A) (.cv v))
        (synWbr (.cv v) (synChwniso A) (.cv w)))
      (synWa (synWa (.classMem (.cv v) (synChwcn A)) (.classMem (.cv w) (synChwcn A)))
        (synWbr (.cv v) (synChwiso A) (.cv w)))
      (synWa (.classMem (.cv v) (synChwcn A)) (.classMem (.cv w) (synChwcn A))) p0011
      p0012
  have p0014 :=
    @gSimpr (.classMem (.cv v) (synChwcn A)) (.classMem (.cv w) (synChwcn A))
  have p0015 :=
    @gSyl
      (synWa (synWbr (.cv u) (synChwniso A) (.cv v))
        (synWbr (.cv v) (synChwniso A) (.cv w)))
      (synWa (.classMem (.cv v) (synChwcn A)) (.classMem (.cv w) (synChwcn A)))
      (.classMem (.cv w) (synChwcn A)) p0013 p0014
  have p0016 :=
    @gJca
      (synWa (synWbr (.cv u) (synChwniso A) (.cv v))
        (synWbr (.cv v) (synChwniso A) (.cv w)))
      (.classMem (.cv u) (synChwcn A)) (.classMem (.cv w) (synChwcn A)) p0007 p0015
  have p0021 :=
    @gSimpr (synWa (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A)))
      (synWbr (.cv u) (synChwiso A) (.cv v))
  have p0022 :=
    @gSyl
      (synWa (synWbr (.cv u) (synChwniso A) (.cv v))
        (synWbr (.cv v) (synChwniso A) (.cv w)))
      (synWa (synWa (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A)))
        (synWbr (.cv u) (synChwiso A) (.cv v)))
      (synWbr (.cv u) (synChwiso A) (.cv v)) p0003 p0021
  have p0027 :=
    @gSimpr (synWa (.classMem (.cv v) (synChwcn A)) (.classMem (.cv w) (synChwcn A)))
      (synWbr (.cv v) (synChwiso A) (.cv w))
  have p0028 :=
    @gSyl
      (synWa (synWbr (.cv u) (synChwniso A) (.cv v))
        (synWbr (.cv v) (synChwniso A) (.cv w)))
      (synWa (synWa (.classMem (.cv v) (synChwcn A)) (.classMem (.cv w) (synChwcn A)))
        (synWbr (.cv v) (synChwiso A) (.cv w)))
      (synWbr (.cv v) (synChwiso A) (.cv w)) p0011 p0027
  have p0029 :=
    @gJca
      (synWa (synWbr (.cv u) (synChwniso A) (.cv v))
        (synWbr (.cv v) (synChwniso A) (.cv w)))
      (synWbr (.cv u) (synChwiso A) (.cv v)) (synWbr (.cv v) (synChwiso A) (.cv w))
      p0022 p0028
  have p0030 :=
    @gHwisotri w v u A dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0001
      dv_cache_0006 dv_cache_0002
  have p0031 :=
    @gSyl
      (synWa (synWbr (.cv u) (synChwniso A) (.cv v))
        (synWbr (.cv v) (synChwniso A) (.cv w)))
      (synWa (synWbr (.cv u) (synChwiso A) (.cv v)) (synWbr (.cv v) (synChwiso A) (.cv w)))
      (synWbr (.cv u) (synChwiso A) (.cv w)) p0029 p0030
  have p0032 :=
    @gJca
      (synWa (synWbr (.cv u) (synChwniso A) (.cv v))
        (synWbr (.cv v) (synChwniso A) (.cv w)))
      (synWa (.classMem (.cv u) (synChwcn A)) (.classMem (.cv w) (synChwcn A)))
      (synWbr (.cv u) (synChwiso A) (.cv w)) p0016 p0031
  have p0033 := @gHwnisohwisob w u A dv_cache_0006
  have p0034 :=
    @gBiimpri (synWbr (.cv u) (synChwniso A) (.cv w))
      (synWa (synWa (.classMem (.cv u) (synChwcn A)) (.classMem (.cv w) (synChwcn A)))
        (synWbr (.cv u) (synChwiso A) (.cv w)))
      p0033
  have p0035 :=
    @gSyl
      (synWa (synWbr (.cv u) (synChwniso A) (.cv v))
        (synWbr (.cv v) (synChwniso A) (.cv w)))
      (synWa (synWa (.classMem (.cv u) (synChwcn A)) (.classMem (.cv w) (synChwcn A)))
        (synWbr (.cv u) (synChwiso A) (.cv w)))
      (synWbr (.cv u) (synChwniso A) (.cv w)) p0032 p0034
  exact p0035

/-- Checked nominal proof certificate identified upstream as `g_hwnisoer`. -/
@[expose]
noncomputable def gHwnisoer (A : Class) :
    Nominal.NPrf
      (.imp (.classMem A (synCvv)) (synWbr (synChwniso A) (synCer) (synChwcn A))) :=
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
  have dv_cache_0008 : u ∉ ((synChwcn A)).fv :=
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
  have dv_cache_0009 : v ∉ ((synChwcn A)).fv :=
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
  have dv_cache_0010 : w ∉ ((synChwcn A)).fv :=
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
  have dv_cache_0011 : u ∉ ((synChwniso A)).fv :=
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
  have dv_cache_0012 : v ∉ ((synChwniso A)).fv :=
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
  have dv_cache_0013 : w ∉ ((synChwniso A)).fv :=
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
  have dv_cache_0014 : u ∉ ((Wff.classMem A (synCvv))).fv :=
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
  have dv_cache_0015 : v ∉ ((Wff.classMem A (synCvv))).fv :=
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
  have dv_cache_0016 : w ∉ ((Wff.classMem A (synCvv))).fv :=
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
  have p0000 := (Nominal.classEqRefl (synChwniso A))
  have p0001 := @gHwgenex
  have p0002 := @gHwbijex
  have p0003 := @gVvex
  have p0004 := @gXpex (synChwbij) (synCvv) p0002 p0003
  have p0005 := @gImaex (synChwgen) (synCxp (synChwbij) (synCvv)) p0001 p0004
  have p0006 :=
    @gA1i (.classMem (synCima (synChwgen) (synCxp (synChwbij) (synCvv))) (synCvv))
      (.classMem A (synCvv)) p0005
  have p0007 := (Nominal.classEqRefl (synChwcn A))
  have p0008 := @gHwcodesexg A (synCvv)
  have p0009 := @gHwrelsex
  have p0010 := @gA1i (.classMem (synChwrels) (synCvv)) (.classMem A (synCvv)) p0009
  have p0011 :=
    @gJca (.classMem A (synCvv)) (.classMem (synChwcodes A) (synCvv))
      (.classMem (synChwrels) (synCvv)) p0008 p0010
  have p0012 := @gInexg (synChwcodes A) (synChwrels) (synCvv) (synCvv)
  have p0013 :=
    @gSyl (.classMem A (synCvv))
      (synWa (.classMem (synChwcodes A) (synCvv)) (.classMem (synChwrels) (synCvv)))
      (.classMem (synCin (synChwcodes A) (synChwrels)) (synCvv)) p0011 p0012
  have p0014 :=
    @gSyl5eqel (.classMem A (synCvv)) (synChwcn A)
      (synCin (synChwcodes A) (synChwrels)) (synCvv) p0007 p0013
  have p0023 :=
    @gJca (.classMem A (synCvv)) (.classMem (synChwcn A) (synCvv))
      (.classMem (synChwcn A) (synCvv)) p0014 p0014
  have p0024 := @gXpexg (synChwcn A) (synChwcn A) (synCvv) (synCvv)
  have p0025 :=
    @gSyl (.classMem A (synCvv))
      (synWa (.classMem (synChwcn A) (synCvv)) (.classMem (synChwcn A) (synCvv)))
      (.classMem (synCxp (synChwcn A) (synChwcn A)) (synCvv)) p0023 p0024
  have p0026 :=
    @gJca (.classMem A (synCvv))
      (.classMem (synCima (synChwgen) (synCxp (synChwbij) (synCvv))) (synCvv))
      (.classMem (synCxp (synChwcn A) (synChwcn A)) (synCvv)) p0006 p0025
  have p0027 :=
    @gInexg (synCima (synChwgen) (synCxp (synChwbij) (synCvv)))
      (synCxp (synChwcn A) (synChwcn A)) (synCvv) (synCvv)
  have p0028 :=
    @gSyl (.classMem A (synCvv))
      (synWa (.classMem (synCima (synChwgen) (synCxp (synChwbij) (synCvv))) (synCvv))
        (.classMem (synCxp (synChwcn A) (synChwcn A)) (synCvv)))
      (.classMem (synCin (synCima (synChwgen) (synCxp (synChwbij) (synCvv)))
          (synCxp (synChwcn A) (synChwcn A))) (synCvv))
      p0026 p0027
  have p0029 :=
    @gSyl5eqel (.classMem A (synCvv)) (synChwniso A)
      (synCin (synCima (synChwgen) (synCxp (synChwbij) (synCvv)))
        (synCxp (synChwcn A) (synChwcn A)))
      (synCvv) p0000 p0028
  have p0038 := @gHwnisohwisob v u A dv_cache_0001
  have p0039 :=
    @gBiimpi (synWbr (.cv u) (synChwniso A) (.cv v))
      (synWa (synWa (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A)))
        (synWbr (.cv u) (synChwiso A) (.cv v)))
      p0038
  have p0040 :=
    @gSimpld (synWbr (.cv u) (synChwniso A) (.cv v))
      (synWa (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A)))
      (synWbr (.cv u) (synChwiso A) (.cv v)) p0039
  have p0041 :=
    @gAncom (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A))
  have p0042 :=
    @gBiimpi (synWa (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A)))
      (synWa (.classMem (.cv v) (synChwcn A)) (.classMem (.cv u) (synChwcn A))) p0041
  have p0043 :=
    @gSyl (synWbr (.cv u) (synChwniso A) (.cv v))
      (synWa (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A)))
      (synWa (.classMem (.cv v) (synChwcn A)) (.classMem (.cv u) (synChwcn A))) p0040
      p0042
  have p0046 :=
    @gSimprd (synWbr (.cv u) (synChwniso A) (.cv v))
      (synWa (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A)))
      (synWbr (.cv u) (synChwiso A) (.cv v)) p0039
  have p0047 := @gHwisosymi v u A dv_cache_0002 dv_cache_0003 dv_cache_0001
  have p0048 :=
    @gSyl (synWbr (.cv u) (synChwniso A) (.cv v))
      (synWbr (.cv u) (synChwiso A) (.cv v)) (synWbr (.cv v) (synChwiso A) (.cv u))
      p0046 p0047
  have p0049 :=
    @gJca (synWbr (.cv u) (synChwniso A) (.cv v))
      (synWa (.classMem (.cv v) (synChwcn A)) (.classMem (.cv u) (synChwcn A)))
      (synWbr (.cv v) (synChwiso A) (.cv u)) p0043 p0048
  have p0050 := @gHwnisohwisob u v A dv_cache_0004
  have p0051 :=
    @gBiimpri (synWbr (.cv v) (synChwniso A) (.cv u))
      (synWa (synWa (.classMem (.cv v) (synChwcn A)) (.classMem (.cv u) (synChwcn A)))
        (synWbr (.cv v) (synChwiso A) (.cv u)))
      p0050
  have p0052 :=
    @gSyl (synWbr (.cv u) (synChwniso A) (.cv v))
      (synWa (synWa (.classMem (.cv v) (synChwcn A)) (.classMem (.cv u) (synChwcn A)))
        (synWbr (.cv v) (synChwiso A) (.cv u)))
      (synWbr (.cv v) (synChwniso A) (.cv u)) p0049 p0051
  have p0053 :=
    @gN3ad2ant3 (synWbr (.cv u) (synChwniso A) (.cv v)) (.classMem A (synCvv))
      (synWbr (.cv v) (synChwniso A) (.cv u))
      (synWa (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A))) p0052
  have p0054 :=
    @gSimpl (synWbr (.cv u) (synChwniso A) (.cv v))
      (synWbr (.cv v) (synChwniso A) (.cv w))
  have p0057 :=
    @gSyl
      (synWa (synWbr (.cv u) (synChwniso A) (.cv v))
        (synWbr (.cv v) (synChwniso A) (.cv w)))
      (synWbr (.cv u) (synChwniso A) (.cv v))
      (synWa (synWa (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A)))
        (synWbr (.cv u) (synChwiso A) (.cv v)))
      p0054 p0039
  have p0058 :=
    @gSimpl (synWa (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A)))
      (synWbr (.cv u) (synChwiso A) (.cv v))
  have p0059 :=
    @gSyl
      (synWa (synWbr (.cv u) (synChwniso A) (.cv v))
        (synWbr (.cv v) (synChwniso A) (.cv w)))
      (synWa (synWa (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A)))
        (synWbr (.cv u) (synChwiso A) (.cv v)))
      (synWa (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A))) p0057
      p0058
  have p0060 :=
    @gSimpl (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A))
  have p0061 :=
    @gSyl
      (synWa (synWbr (.cv u) (synChwniso A) (.cv v))
        (synWbr (.cv v) (synChwniso A) (.cv w)))
      (synWa (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A)))
      (.classMem (.cv u) (synChwcn A)) p0059 p0060
  have p0062 :=
    @gSimpr (synWbr (.cv u) (synChwniso A) (.cv v))
      (synWbr (.cv v) (synChwniso A) (.cv w))
  have p0063 := @gHwnisohwisob w v A dv_cache_0005
  have p0064 :=
    @gBiimpi (synWbr (.cv v) (synChwniso A) (.cv w))
      (synWa (synWa (.classMem (.cv v) (synChwcn A)) (.classMem (.cv w) (synChwcn A)))
        (synWbr (.cv v) (synChwiso A) (.cv w)))
      p0063
  have p0065 :=
    @gSyl
      (synWa (synWbr (.cv u) (synChwniso A) (.cv v))
        (synWbr (.cv v) (synChwniso A) (.cv w)))
      (synWbr (.cv v) (synChwniso A) (.cv w))
      (synWa (synWa (.classMem (.cv v) (synChwcn A)) (.classMem (.cv w) (synChwcn A)))
        (synWbr (.cv v) (synChwiso A) (.cv w)))
      p0062 p0064
  have p0066 :=
    @gSimpl (synWa (.classMem (.cv v) (synChwcn A)) (.classMem (.cv w) (synChwcn A)))
      (synWbr (.cv v) (synChwiso A) (.cv w))
  have p0067 :=
    @gSyl
      (synWa (synWbr (.cv u) (synChwniso A) (.cv v))
        (synWbr (.cv v) (synChwniso A) (.cv w)))
      (synWa (synWa (.classMem (.cv v) (synChwcn A)) (.classMem (.cv w) (synChwcn A)))
        (synWbr (.cv v) (synChwiso A) (.cv w)))
      (synWa (.classMem (.cv v) (synChwcn A)) (.classMem (.cv w) (synChwcn A))) p0065
      p0066
  have p0068 :=
    @gSimpr (.classMem (.cv v) (synChwcn A)) (.classMem (.cv w) (synChwcn A))
  have p0069 :=
    @gSyl
      (synWa (synWbr (.cv u) (synChwniso A) (.cv v))
        (synWbr (.cv v) (synChwniso A) (.cv w)))
      (synWa (.classMem (.cv v) (synChwcn A)) (.classMem (.cv w) (synChwcn A)))
      (.classMem (.cv w) (synChwcn A)) p0067 p0068
  have p0070 :=
    @gJca
      (synWa (synWbr (.cv u) (synChwniso A) (.cv v))
        (synWbr (.cv v) (synChwniso A) (.cv w)))
      (.classMem (.cv u) (synChwcn A)) (.classMem (.cv w) (synChwcn A)) p0061 p0069
  have p0075 :=
    @gSimpr (synWa (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A)))
      (synWbr (.cv u) (synChwiso A) (.cv v))
  have p0076 :=
    @gSyl
      (synWa (synWbr (.cv u) (synChwniso A) (.cv v))
        (synWbr (.cv v) (synChwniso A) (.cv w)))
      (synWa (synWa (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A)))
        (synWbr (.cv u) (synChwiso A) (.cv v)))
      (synWbr (.cv u) (synChwiso A) (.cv v)) p0057 p0075
  have p0081 :=
    @gSimpr (synWa (.classMem (.cv v) (synChwcn A)) (.classMem (.cv w) (synChwcn A)))
      (synWbr (.cv v) (synChwiso A) (.cv w))
  have p0082 :=
    @gSyl
      (synWa (synWbr (.cv u) (synChwniso A) (.cv v))
        (synWbr (.cv v) (synChwniso A) (.cv w)))
      (synWa (synWa (.classMem (.cv v) (synChwcn A)) (.classMem (.cv w) (synChwcn A)))
        (synWbr (.cv v) (synChwiso A) (.cv w)))
      (synWbr (.cv v) (synChwiso A) (.cv w)) p0065 p0081
  have p0083 :=
    @gJca
      (synWa (synWbr (.cv u) (synChwniso A) (.cv v))
        (synWbr (.cv v) (synChwniso A) (.cv w)))
      (synWbr (.cv u) (synChwiso A) (.cv v)) (synWbr (.cv v) (synChwiso A) (.cv w))
      p0076 p0082
  have p0084 :=
    @gHwisotri w v u A dv_cache_0002 dv_cache_0003 dv_cache_0006 dv_cache_0001
      dv_cache_0007 dv_cache_0005
  have p0085 :=
    @gSyl
      (synWa (synWbr (.cv u) (synChwniso A) (.cv v))
        (synWbr (.cv v) (synChwniso A) (.cv w)))
      (synWa (synWbr (.cv u) (synChwiso A) (.cv v)) (synWbr (.cv v) (synChwiso A) (.cv w)))
      (synWbr (.cv u) (synChwiso A) (.cv w)) p0083 p0084
  have p0086 :=
    @gJca
      (synWa (synWbr (.cv u) (synChwniso A) (.cv v))
        (synWbr (.cv v) (synChwniso A) (.cv w)))
      (synWa (.classMem (.cv u) (synChwcn A)) (.classMem (.cv w) (synChwcn A)))
      (synWbr (.cv u) (synChwiso A) (.cv w)) p0070 p0085
  have p0087 := @gHwnisohwisob w u A dv_cache_0007
  have p0088 :=
    @gBiimpri (synWbr (.cv u) (synChwniso A) (.cv w))
      (synWa (synWa (.classMem (.cv u) (synChwcn A)) (.classMem (.cv w) (synChwcn A)))
        (synWbr (.cv u) (synChwiso A) (.cv w)))
      p0087
  have p0089 :=
    @gSyl
      (synWa (synWbr (.cv u) (synChwniso A) (.cv v))
        (synWbr (.cv v) (synChwniso A) (.cv w)))
      (synWa (synWa (.classMem (.cv u) (synChwcn A)) (.classMem (.cv w) (synChwcn A)))
        (synWbr (.cv u) (synChwiso A) (.cv w)))
      (synWbr (.cv u) (synChwniso A) (.cv w)) p0086 p0088
  have p0090 :=
    @gN3ad2ant3
      (synWa (synWbr (.cv u) (synChwniso A) (.cv v))
        (synWbr (.cv v) (synChwniso A) (.cv w)))
      (.classMem A (synCvv)) (synWbr (.cv u) (synChwniso A) (.cv w))
      (synW3a (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A))
        (.classMem (.cv w) (synChwcn A)))
      p0089
  have p0091 :=
    @gIserd (.classMem A (synCvv)) u v w (synChwcn A) (synChwniso A) (synCvv)
      (synCvv) dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012
      dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0001 dv_cache_0007
      dv_cache_0005 p0029 p0014 p0053 p0090
  exact p0091

/-- Checked nominal proof certificate identified upstream as `g_hwnisorefli`. -/
@[expose]
noncomputable def gHwnisorefli (u : Var) (A : Class) (dv_A_u : u ∉ A.fv) :
    Nominal.NPrf
      (.imp (.classMem (.cv u) (synChwcn A)) (synWbr (.cv u) (synChwniso A) (.cv u))) :=
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
      ((synWb (synWbr (.cv u) (synChwniso A) (.cv u)) (synWa
            (synWa (.classMem (.cv u) (synChwcn A)) (.classMem (.cv u) (synChwcn A)))
            (synWbr (.cv u) (synChwiso A) (.cv u))))).fv :=
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
  have p0000 := @gPm424 (.classMem (.cv u) (synChwcn A))
  have p0001 :=
    @gBiimpi (.classMem (.cv u) (synChwcn A))
      (synWa (.classMem (.cv u) (synChwcn A)) (.classMem (.cv u) (synChwcn A))) p0000
  have p0002 := @gHwcnraw u A
  have p0003 := @gHwisorefl u A dv_cache_0001
  have p0004 :=
    @gSyl (.classMem (.cv u) (synChwcn A)) (.classMem (.cv u) (synChwcodes A))
      (synWbr (.cv u) (synChwiso A) (.cv u)) p0002 p0003
  have p0005 :=
    @gJca (.classMem (.cv u) (synChwcn A))
      (synWa (.classMem (.cv u) (synChwcn A)) (.classMem (.cv u) (synChwcn A)))
      (synWbr (.cv u) (synChwiso A) (.cv u)) p0001 p0004
  have p0006 := @gElex (.cv u) (synChwcn A)
  have p0007 := @gBreq2 (.cv v) (.cv u) (.cv u) (synChwniso A)
  have p0008 := @gEleq1 (.cv v) (.cv u) (synChwcn A)
  have p0009 :=
    @gAnbi2d (.classEq (.cv v) (.cv u)) (.classMem (.cv v) (synChwcn A))
      (.classMem (.cv u) (synChwcn A)) (.classMem (.cv u) (synChwcn A)) p0008
  have p0010 := @gBreq2 (.cv v) (.cv u) (.cv u) (synChwiso A)
  have p0011 :=
    @gAnbi12d (.classEq (.cv v) (.cv u))
      (synWa (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A)))
      (synWa (.classMem (.cv u) (synChwcn A)) (.classMem (.cv u) (synChwcn A)))
      (synWbr (.cv u) (synChwiso A) (.cv v)) (synWbr (.cv u) (synChwiso A) (.cv u))
      p0009 p0010
  have p0012 :=
    @gBibi12d (.classEq (.cv v) (.cv u)) (synWbr (.cv u) (synChwniso A) (.cv v))
      (synWbr (.cv u) (synChwniso A) (.cv u))
      (synWa (synWa (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A)))
        (synWbr (.cv u) (synChwiso A) (.cv v)))
      (synWa (synWa (.classMem (.cv u) (synChwcn A)) (.classMem (.cv u) (synChwcn A)))
        (synWbr (.cv u) (synChwiso A) (.cv u)))
      p0007 p0011
  have p0013 := @gHwnisohwisob v u A dv_cache_0002
  have p0014 :=
    @gVtoclg
      (synWb (synWbr (.cv u) (synChwniso A) (.cv v)) (synWa
          (synWa (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A)))
          (synWbr (.cv u) (synChwiso A) (.cv v))))
      (synWb (synWbr (.cv u) (synChwniso A) (.cv u)) (synWa
          (synWa (.classMem (.cv u) (synChwcn A)) (.classMem (.cv u) (synChwcn A)))
          (synWbr (.cv u) (synChwiso A) (.cv u))))
      v (.cv u) (synCvv) dv_cache_0003 dv_cache_0004 p0012 p0013
  have p0015 :=
    @gSyl (.classMem (.cv u) (synChwcn A)) (.classMem (.cv u) (synCvv))
      (synWb (synWbr (.cv u) (synChwniso A) (.cv u)) (synWa
          (synWa (.classMem (.cv u) (synChwcn A)) (.classMem (.cv u) (synChwcn A)))
          (synWbr (.cv u) (synChwiso A) (.cv u))))
      p0006 p0014
  have p0016 :=
    @gMpbird (.classMem (.cv u) (synChwcn A)) (synWbr (.cv u) (synChwniso A) (.cv u))
      (synWa (synWa (.classMem (.cv u) (synChwcn A)) (.classMem (.cv u) (synChwcn A)))
        (synWbr (.cv u) (synChwiso A) (.cv u)))
      p0005 p0015
  exact p0016

/-- Checked nominal proof certificate identified upstream as `g_hwnisoerv`. -/
@[expose]
noncomputable def gHwnisoerv (A : Class) :
    Nominal.NPrf
      (.imp (.classMem A (synCvv)) (synWbr (synChwniso A) (synCer) (synCvv))) :=
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
  have dv_cache_0007 : u ∉ ((synCvv)).fv :=
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
  have dv_cache_0008 : v ∉ ((synCvv)).fv :=
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
  have dv_cache_0009 : w ∉ ((synCvv)).fv :=
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
  have dv_cache_0010 : u ∉ ((synChwniso A)).fv :=
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
  have dv_cache_0011 : v ∉ ((synChwniso A)).fv :=
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
  have dv_cache_0012 : w ∉ ((synChwniso A)).fv :=
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
  have dv_cache_0013 : u ∉ ((Wff.classMem A (synCvv))).fv :=
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
  have dv_cache_0014 : v ∉ ((Wff.classMem A (synCvv))).fv :=
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
  have dv_cache_0015 : w ∉ ((Wff.classMem A (synCvv))).fv :=
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
  have p0000 := @gHwnisoexg A
  have p0001 := @gVvex
  have p0002 := @gA1i (.classMem (synCvv) (synCvv)) (.classMem A (synCvv)) p0001
  have p0003 := @gHwnisosymi v u A dv_cache_0001 dv_cache_0002 dv_cache_0003
  have p0004 :=
    @gN3ad2ant3 (synWbr (.cv u) (synChwniso A) (.cv v)) (.classMem A (synCvv))
      (synWbr (.cv v) (synChwniso A) (.cv u))
      (synWa (.classMem (.cv u) (synCvv)) (.classMem (.cv v) (synCvv))) p0003
  have p0005 :=
    @gHwnisotri w v u A dv_cache_0001 dv_cache_0002 dv_cache_0004 dv_cache_0003
      dv_cache_0005 dv_cache_0006
  have p0006 :=
    @gN3ad2ant3
      (synWa (synWbr (.cv u) (synChwniso A) (.cv v))
        (synWbr (.cv v) (synChwniso A) (.cv w)))
      (.classMem A (synCvv)) (synWbr (.cv u) (synChwniso A) (.cv w))
      (synW3a (.classMem (.cv u) (synCvv)) (.classMem (.cv v) (synCvv))
        (.classMem (.cv w) (synCvv)))
      p0005
  have p0007 :=
    @gIserd (.classMem A (synCvv)) u v w (synCvv) (synChwniso A) (synCvv) (synCvv)
      dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012
      dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0003 dv_cache_0005 dv_cache_0006
      p0000 p0002 p0004 p0006
  exact p0007


end NFChoice.DirectNominalPrf.WPPReplay

end
