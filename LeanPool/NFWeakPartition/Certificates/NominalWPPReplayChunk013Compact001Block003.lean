/-
Copyright (c) 2026 Elliot Glazer and NFNotWPP contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elliot Glazer and NFNotWPP contributors
-/

module

public import LeanPool.NFWeakPartition.Certificates.NominalWPPReplayChunk013Compact001Block002

/-! Nominal proof certificates grouped in dependency order. -/


public section

/-! Certificates from `NominalWPPReplayChunk013Compact001Part011`. -/


section

namespace NFChoice.DirectNominalPrf.WPPReplay

open scoped Fol
open NFChoice.Foundation
open NFChoice.SemanticCore
open NFChoice.ReplaySupport
open NFChoice.Compiler.CompactSourceSyntax

/-- Checked nominal proof certificate identified upstream as `g_pw1fnex`. -/
@[expose]
noncomputable def gPw1fnex : Nominal.NPrf (.classMem (synCpw1fn) (synCvv)) :=
  by
  let proofSupport : Finset Var := (∅ : Finset Var)
  let x : Var := freshVar proofSupport 0
  let y : Var := freshVar proofSupport 1
  let t : Var := freshVar proofSupport 2
  have fresh_x_ne_y : x ≠ y :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have fresh_y_ne_x : y ≠ x := Ne.symm fresh_x_ne_y
  have fresh_x_ne_t : x ≠ t :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 2
    exact freshVar_injective proofSupport (i := 0) (j := 2) (by decide)
  have fresh_t_ne_x : t ≠ x := Ne.symm fresh_x_ne_t
  have fresh_y_ne_t : y ≠ t :=
    by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 2
    exact freshVar_injective proofSupport (i := 1) (j := 2) (by decide)
  have fresh_t_ne_y : t ≠ y := Ne.symm fresh_y_ne_t
  have dv_cache_0001 : y ∉ ((synCop (synCsn (synCsn (.cv t))) (.cv x))).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cop,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, fresh_y_ne_t, fresh_y_ne_x, or_false, not_false_eq_true])
  have dv_cache_0002 : y ∉ ((synCtxp (synCsi (synCcnv (synCsset))) (synCsset))).fv :=
    by
    clear dv_cache_0001
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ctxp,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csi,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csset, Finset.mem_union,
          compact_fv_not_mem_empty, or_false, not_false_eq_true])
  have dv_cache_0003 : y ∉ ((Class.cv t)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_y_ne_t, not_false_eq_true])
  have dv_cache_0004 : y ∉ ((Class.cv x)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_y_ne_x, not_false_eq_true])
  have dv_cache_0005 : t ∉ ((synCop (synCsn (.cv y)) (.cv x))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact
      (by
        have compact_fv_not_mem_empty : t ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cop,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, fresh_t_ne_y, fresh_t_ne_x, or_false, not_false_eq_true])
  have dv_cache_0006 :
    t ∉
      ((synCtxp (synCid) (synCima (synCtxp (synCsi (synCcnv (synCsset))) (synCsset))
            (synC1c)))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact
      (by
        have compact_fv_not_mem_empty : t ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ctxp,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cid,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cima,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csi,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csset,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c, Finset.mem_union,
          compact_fv_not_mem_empty, or_false, not_false_eq_true])
  have dv_cache_0007 : t ∉ ((Class.cv y)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006
    exact
      (by
        have compact_fv_not_mem_empty : t ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_t_ne_y, not_false_eq_true])
  have dv_cache_0008 : t ∉ ((synCuni (.cv x))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007
    exact
      (by
        have compact_fv_not_mem_empty : t ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cuni,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton, fresh_t_ne_x,
          not_false_eq_true])
  have dv_cache_0009 : x ∉ ((synC1c)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c,
          compact_fv_not_mem_empty, not_false_eq_true])
  have dv_cache_0010 :
    x ∉
      ((synCima (synCtxp (synCid)
            (synCima (synCtxp (synCsi (synCcnv (synCsset))) (synCsset)) (synC1c)))
          (synCpw1 (synC1c)))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cima,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ctxp,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cid,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csi,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csset,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1, Finset.mem_union,
          compact_fv_not_mem_empty, or_false, not_false_eq_true])
  have dv_cache_0011 :
    y ∉
      ((synCima (synCtxp (synCid)
            (synCima (synCtxp (synCsi (synCcnv (synCsset))) (synCsset)) (synC1c)))
          (synCpw1 (synC1c)))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cima,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ctxp,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cid,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csi,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csset,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1, Finset.mem_union,
          compact_fv_not_mem_empty, or_false, not_false_eq_true])
  have dv_cache_0012 : y ∉ ((synCpw1 (synCuni (.cv x)))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cuni,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton, fresh_y_ne_x,
          not_false_eq_true])
  have dv_cache_0013 : x ≠ y :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012
    exact (show x ≠ y from (by exact fresh_x_ne_y))
  have p0000 := NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominalDfPw1fn x
  have p0001 :=
    @gOteltxp (synCsn (synCsn (.cv t))) (synCsn (.cv y)) (.cv x) (synCid)
      (synCima (synCtxp (synCsi (synCcnv (synCsset))) (synCsset)) (synC1c))
  have p0002 := @gSnex (.cv y)
  have p0003 := @gIdeq (synCsn (synCsn (.cv t))) (synCsn (.cv y)) p0002
  have p0004 :=
    (Nominal.biimpRefl (synWbr (synCsn (synCsn (.cv t))) (synCid) (synCsn (.cv y))))
  have p0005 := @gEqcom (synCsn (synCsn (.cv t))) (synCsn (.cv y))
  have p0006 := @gVex y
  have p0007 := @gSneqb (.cv y) (synCsn (.cv t)) p0006
  have p0008 :=
    @gBitri (.classEq (synCsn (synCsn (.cv t))) (synCsn (.cv y)))
      (.classEq (synCsn (.cv y)) (synCsn (synCsn (.cv t))))
      (.classEq (.cv y) (synCsn (.cv t))) p0005 p0007
  have p0009 :=
    @gN3bitr3i (synWbr (synCsn (synCsn (.cv t))) (synCid) (synCsn (.cv y)))
      (.classEq (synCsn (synCsn (.cv t))) (synCsn (.cv y)))
      (.classMem (synCop (synCsn (synCsn (.cv t))) (synCsn (.cv y))) (synCid))
      (.classEq (.cv y) (synCsn (.cv t))) p0003 p0004 p0008
  have p0010 :=
    @gOteltxp (synCsn (.cv y)) (synCsn (synCsn (.cv t))) (.cv x)
      (synCsi (synCcnv (synCsset))) (synCsset)
  have p0011 := @gSnex (.cv t)
  have p0012 := @gBrsnsi (.cv y) (synCsn (.cv t)) (synCcnv (synCsset)) p0006 p0011
  have p0013 :=
    (Nominal.biimpRefl (synWbr (synCsn (.cv y)) (synCsi (synCcnv (synCsset)))
        (synCsn (synCsn (.cv t)))))
  have p0014 := @gBrcnv (.cv y) (synCsn (.cv t)) (synCsset)
  have p0015 := @gVex t
  have p0016 := @gBrssetsn (.cv t) (.cv y) p0015 p0006
  have p0017_e01_recanon :
    Nominal.NPrf (synWb (synWbr (synCsn (.cv t)) (synCsset) (.cv y)) (.objMem t y)) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold synWb synWbr synCop synCun synCnin synWnan synWa synCcompl synWrex
          synWex synCphi synCsn synCsset synCopab synWss synCin
        simp (config :=
          { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_class_cv]
        apply Nominal.RecanonTransportDev.TRecanonWff.neg
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · apply Nominal.RecanonTransportDev.TRecanonWff.imp
          · exact Nominal.RecanonTransportDev.TRecanonWff.same _
          · exact Nominal.RecanonTransportDev.TRecanonWff.classMem_objMem _ _
        · apply Nominal.RecanonTransportDev.TRecanonWff.neg
          apply Nominal.RecanonTransportDev.TRecanonWff.imp
          · exact Nominal.RecanonTransportDev.TRecanonWff.classMem_objMem _ _
          · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0016
  have p0017 :=
    @gBitri (synWbr (.cv y) (synCcnv (synCsset)) (synCsn (.cv t)))
      (synWbr (synCsn (.cv t)) (synCsset) (.cv y)) (.objMem t y) p0014
      p0017_e01_recanon
  have p0018 :=
    @gN3bitr3i
      (synWbr (synCsn (.cv y)) (synCsi (synCcnv (synCsset))) (synCsn (synCsn (.cv t))))
      (synWbr (.cv y) (synCcnv (synCsset)) (synCsn (.cv t)))
      (.classMem (synCop (synCsn (.cv y)) (synCsn (synCsn (.cv t))))
        (synCsi (synCcnv (synCsset))))
      (.objMem t y) p0012 p0013 p0017
  have p0019 := @gVex x
  have p0020 := @gOpelssetsn (.cv y) (.cv x) p0006 p0019
  have p0021_e01_recanon :
    Nominal.NPrf
      (synWb (.classMem (synCop (synCsn (.cv y)) (.cv x)) (synCsset)) (.objMem y x)) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold synWb synCop synCun synCnin synWnan synWa synCcompl synWrex synWex
          synCphi synCsn synCsset synCopab synWss synCin
        simp (config :=
          { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_class_cv]
        apply Nominal.RecanonTransportDev.TRecanonWff.neg
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · apply Nominal.RecanonTransportDev.TRecanonWff.imp
          · exact Nominal.RecanonTransportDev.TRecanonWff.same _
          · exact Nominal.RecanonTransportDev.TRecanonWff.classMem_objMem _ _
        · apply Nominal.RecanonTransportDev.TRecanonWff.neg
          apply Nominal.RecanonTransportDev.TRecanonWff.imp
          · exact Nominal.RecanonTransportDev.TRecanonWff.classMem_objMem _ _
          · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0020
  have p0021 :=
    @gAnbi12i
      (.classMem (synCop (synCsn (.cv y)) (synCsn (synCsn (.cv t))))
        (synCsi (synCcnv (synCsset))))
      (.objMem t y) (.classMem (synCop (synCsn (.cv y)) (.cv x)) (synCsset))
      (.objMem y x) p0018 p0021_e01_recanon
  have p0022 :=
    @gBitri
      (.classMem (synCop (synCsn (.cv y)) (synCop (synCsn (synCsn (.cv t))) (.cv x)))
        (synCtxp (synCsi (synCcnv (synCsset))) (synCsset)))
      (synWa (.classMem (synCop (synCsn (.cv y)) (synCsn (synCsn (.cv t))))
          (synCsi (synCcnv (synCsset))))
        (.classMem (synCop (synCsn (.cv y)) (.cv x)) (synCsset)))
      (synWa (.objMem t y) (.objMem y x)) p0010 p0021
  have p0023 :=
    @gExbii
      (.classMem (synCop (synCsn (.cv y)) (synCop (synCsn (synCsn (.cv t))) (.cv x)))
        (synCtxp (synCsi (synCcnv (synCsset))) (synCsset)))
      (synWa (.objMem t y) (.objMem y x)) y p0022
  have p0024 :=
    @gElima1c y (synCop (synCsn (synCsn (.cv t))) (.cv x))
      (synCtxp (synCsi (synCcnv (synCsset))) (synCsset)) dv_cache_0001 dv_cache_0002
  have p0025 := @gEluni y (.cv t) (.cv x) dv_cache_0003 dv_cache_0004
  have p0026_e02_recanon :
    Nominal.NPrf
      (synWb (.classMem (.cv t) (synCuni (.cv x)))
        (synWex y (synWa (.objMem t y) (.objMem y x)))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold synWb synCuni synWex synWa
        simp (config :=
          { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_class_cv]
        apply Nominal.RecanonTransportDev.TRecanonWff.neg
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · apply Nominal.RecanonTransportDev.TRecanonWff.imp
          · exact Nominal.RecanonTransportDev.TRecanonWff.same _
          · apply Nominal.RecanonTransportDev.TRecanonWff.neg
            apply Nominal.RecanonTransportDev.TRecanonWff.all
            apply Nominal.RecanonTransportDev.TRecanonWff.neg
            apply Nominal.RecanonTransportDev.TRecanonWff.neg
            apply Nominal.RecanonTransportDev.TRecanonWff.imp
            · exact Nominal.RecanonTransportDev.TRecanonWff.classMem_objMem _ _
            · apply Nominal.RecanonTransportDev.TRecanonWff.neg
              exact Nominal.RecanonTransportDev.TRecanonWff.classMem_objMem _ _
        · apply Nominal.RecanonTransportDev.TRecanonWff.neg
          apply Nominal.RecanonTransportDev.TRecanonWff.imp
          · apply Nominal.RecanonTransportDev.TRecanonWff.neg
            apply Nominal.RecanonTransportDev.TRecanonWff.all
            apply Nominal.RecanonTransportDev.TRecanonWff.neg
            apply Nominal.RecanonTransportDev.TRecanonWff.neg
            apply Nominal.RecanonTransportDev.TRecanonWff.imp
            · exact Nominal.RecanonTransportDev.TRecanonWff.classMem_objMem _ _
            · apply Nominal.RecanonTransportDev.TRecanonWff.neg
              exact Nominal.RecanonTransportDev.TRecanonWff.classMem_objMem _ _
          · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0025
  have p0026 :=
    @gN3bitr4i
      (synWex y (.classMem
          (synCop (synCsn (.cv y)) (synCop (synCsn (synCsn (.cv t))) (.cv x)))
          (synCtxp (synCsi (synCcnv (synCsset))) (synCsset))))
      (synWex y (synWa (.objMem t y) (.objMem y x)))
      (.classMem (synCop (synCsn (synCsn (.cv t))) (.cv x))
        (synCima (synCtxp (synCsi (synCcnv (synCsset))) (synCsset)) (synC1c)))
      (.classMem (.cv t) (synCuni (.cv x))) p0023 p0024 p0026_e02_recanon
  have p0027 :=
    @gAnbi12i
      (.classMem (synCop (synCsn (synCsn (.cv t))) (synCsn (.cv y))) (synCid))
      (.classEq (.cv y) (synCsn (.cv t)))
      (.classMem (synCop (synCsn (synCsn (.cv t))) (.cv x))
        (synCima (synCtxp (synCsi (synCcnv (synCsset))) (synCsset)) (synC1c)))
      (.classMem (.cv t) (synCuni (.cv x))) p0009 p0026
  have p0028 :=
    @gBitri
      (.classMem (synCop (synCsn (synCsn (.cv t))) (synCop (synCsn (.cv y)) (.cv x)))
        (synCtxp (synCid)
          (synCima (synCtxp (synCsi (synCcnv (synCsset))) (synCsset)) (synC1c))))
      (synWa (.classMem (synCop (synCsn (synCsn (.cv t))) (synCsn (.cv y))) (synCid))
        (.classMem (synCop (synCsn (synCsn (.cv t))) (.cv x))
          (synCima (synCtxp (synCsi (synCcnv (synCsset))) (synCsset)) (synC1c))))
      (synWa (.classEq (.cv y) (synCsn (.cv t))) (.classMem (.cv t) (synCuni (.cv x))))
      p0001 p0027
  have p0029 :=
    @gAncom (.classEq (.cv y) (synCsn (.cv t))) (.classMem (.cv t) (synCuni (.cv x)))
  have p0030 :=
    @gBitri
      (.classMem (synCop (synCsn (synCsn (.cv t))) (synCop (synCsn (.cv y)) (.cv x)))
        (synCtxp (synCid)
          (synCima (synCtxp (synCsi (synCcnv (synCsset))) (synCsset)) (synC1c))))
      (synWa (.classEq (.cv y) (synCsn (.cv t))) (.classMem (.cv t) (synCuni (.cv x))))
      (synWa (.classMem (.cv t) (synCuni (.cv x))) (.classEq (.cv y) (synCsn (.cv t))))
      p0028 p0029
  have p0031 :=
    @gExbii
      (.classMem (synCop (synCsn (synCsn (.cv t))) (synCop (synCsn (.cv y)) (.cv x)))
        (synCtxp (synCid)
          (synCima (synCtxp (synCsi (synCcnv (synCsset))) (synCsset)) (synC1c))))
      (synWa (.classMem (.cv t) (synCuni (.cv x))) (.classEq (.cv y) (synCsn (.cv t))))
      t p0030
  have p0032 :=
    @gElimapw11c t (synCop (synCsn (.cv y)) (.cv x))
      (synCtxp (synCid)
        (synCima (synCtxp (synCsi (synCcnv (synCsset))) (synCsset)) (synC1c)))
      dv_cache_0005 dv_cache_0006
  have p0033 := @gElpw1 t (.cv y) (synCuni (.cv x)) dv_cache_0007 dv_cache_0008
  have p0034 :=
    (Nominal.biimpRefl (synWrex t (synCuni (.cv x)) (.classEq (.cv y) (synCsn (.cv t)))))
  have p0035 :=
    @gBitri (.classMem (.cv y) (synCpw1 (synCuni (.cv x))))
      (synWrex t (synCuni (.cv x)) (.classEq (.cv y) (synCsn (.cv t))))
      (synWex t (synWa (.classMem (.cv t) (synCuni (.cv x)))
          (.classEq (.cv y) (synCsn (.cv t)))))
      p0033 p0034
  have p0036 :=
    @gN3bitr4i
      (synWex t (.classMem
          (synCop (synCsn (synCsn (.cv t))) (synCop (synCsn (.cv y)) (.cv x)))
          (synCtxp (synCid) (synCima (synCtxp (synCsi (synCcnv (synCsset))) (synCsset))
              (synC1c)))))
      (synWex t (synWa (.classMem (.cv t) (synCuni (.cv x)))
          (.classEq (.cv y) (synCsn (.cv t)))))
      (.classMem (synCop (synCsn (.cv y)) (.cv x)) (synCima (synCtxp (synCid)
            (synCima (synCtxp (synCsi (synCcnv (synCsset))) (synCsset)) (synC1c)))
          (synCpw1 (synC1c))))
      (.classMem (.cv y) (synCpw1 (synCuni (.cv x)))) p0031 p0032 p0035
  have p0037 :=
    @gReleqmpt x y (synC1c)
      (synCima (synCtxp (synCid)
          (synCima (synCtxp (synCsi (synCcnv (synCsset))) (synCsset)) (synC1c)))
        (synCpw1 (synC1c)))
      (synCpw1 (synCuni (.cv x))) dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 p0036
  have p0038 :=
    @gEqtr4i (synCpw1fn) (synCmpt x (synC1c) (synCpw1 (synCuni (.cv x))))
      (synCin (synCxp (synC1c) (synCvv)) (synCcnv (synCcompl (synCima
              (synCsymdif (synCins3 (synCsset)) (synCins2 (synCima (synCtxp (synCid)
                      (synCima (synCtxp (synCsi (synCcnv (synCsset))) (synCsset))
                        (synC1c))) (synCpw1 (synC1c))))) (synC1c)))))
      p0000 p0037
  have p0039 := @gN1cex
  have p0040 := @gIdex
  have p0041 := @gSsetex
  have p0042 := @gCnvex (synCsset) p0041
  have p0043 := @gSiex (synCcnv (synCsset)) p0042
  have p0045 := @gTxpex (synCsi (synCcnv (synCsset))) (synCsset) p0043 p0041
  have p0047 :=
    @gImaex (synCtxp (synCsi (synCcnv (synCsset))) (synCsset)) (synC1c) p0045 p0039
  have p0048 :=
    @gTxpex (synCid)
      (synCima (synCtxp (synCsi (synCcnv (synCsset))) (synCsset)) (synC1c)) p0040
      p0047
  have p0050 := @gPw1ex (synC1c) p0039
  have p0051 :=
    @gImaex
      (synCtxp (synCid)
        (synCima (synCtxp (synCsi (synCcnv (synCsset))) (synCsset)) (synC1c)))
      (synCpw1 (synC1c)) p0048 p0050
  have p0052 :=
    @gMptexlem (synC1c)
      (synCima (synCtxp (synCid)
          (synCima (synCtxp (synCsi (synCcnv (synCsset))) (synCsset)) (synC1c)))
        (synCpw1 (synC1c)))
      p0039 p0051
  have p0053 :=
    @gEqeltri (synCpw1fn)
      (synCin (synCxp (synC1c) (synCvv)) (synCcnv (synCcompl (synCima
              (synCsymdif (synCins3 (synCsset)) (synCins2 (synCima (synCtxp (synCid)
                      (synCima (synCtxp (synCsi (synCcnv (synCsset))) (synCsset))
                        (synC1c))) (synCpw1 (synC1c))))) (synC1c)))))
      (synCvv) p0038 p0052
  exact p0053

/-- Checked nominal proof certificate identified upstream as `g_fnpw1fn`. -/
@[expose]
noncomputable def gFnpw1fn : Nominal.NPrf (synWfn (synCpw1fn) (synC1c)) :=
  by
  let proofSupport : Finset Var := (∅ : Finset Var)
  let x : Var := freshVar proofSupport 0
  have dv_cache_0001 : x ∉ ((synC1c)).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c,
          compact_fv_not_mem_empty, not_false_eq_true])
  have p0000 := NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominalDfPw1fn x
  have p0001 :=
    @gFnmpt x (synC1c) (synCpw1 (synCuni (.cv x))) (synCpw1fn) (synCvv)
      dv_cache_0001 p0000
  have p0002 := @gVex x
  have p0003 := @gUniex (.cv x) p0002
  have p0004 := @gPw1ex (synCuni (.cv x)) p0003
  have p0005 :=
    @gA1i (.classMem (synCpw1 (synCuni (.cv x))) (synCvv))
      (.classMem (.cv x) (synC1c)) p0004
  have p0006 :=
    @gMprg (.classMem (synCpw1 (synCuni (.cv x))) (synCvv))
      (synWfn (synCpw1fn) (synC1c)) x (synC1c) p0001 p0005
  exact p0006

/-- Checked nominal proof certificate identified upstream as `g_brpw1fn`. -/
@[expose]
noncomputable def gBrpw1fn (A : Class) (B : Class)
    (hyp_brpw1fn_1 : Nominal.NPrf (.classMem A (synCvv))) :
    Nominal.NPrf
      (synWb (synWbr (synCsn A) (synCpw1fn) B) (.classEq B (synCpw1 A))) :=
  by
  have p0000 := @gPw1fnval A hyp_brpw1fn_1
  have p0001 := @gEqeq1i (synCfv (synCpw1fn) (synCsn A)) (synCpw1 A) B p0000
  have p0002 := @gFnpw1fn
  have p0003 := @gSnel1c A hyp_brpw1fn_1
  have p0004 := @gFnbrfvb (synC1c) (synCsn A) B (synCpw1fn)
  have p0005 :=
    @gMp2an (synWfn (synCpw1fn) (synC1c)) (.classMem (synCsn A) (synC1c))
      (synWb (.classEq (synCfv (synCpw1fn) (synCsn A)) B)
        (synWbr (synCsn A) (synCpw1fn) B))
      p0002 p0003 p0004
  have p0006 := @gEqcom (synCpw1 A) B
  have p0007 :=
    @gN3bitr3i (.classEq (synCfv (synCpw1fn) (synCsn A)) B) (.classEq (synCpw1 A) B)
      (synWbr (synCsn A) (synCpw1fn) B) (.classEq B (synCpw1 A)) p0001 p0005 p0006
  exact p0007

/-- Checked nominal proof certificate identified upstream as `g_pw1fnf1o`. -/
@[expose]
noncomputable def gPw1fnf1o :
    Nominal.NPrf (synWf1o (synCpw1fn) (synC1c) (synCpw (synC1c))) :=
  by
  let proofSupport : Finset Var := (∅ : Finset Var)
  let x : Var := freshVar proofSupport 0
  let y : Var := freshVar proofSupport 1
  let z : Var := freshVar proofSupport 2
  let a : Var := freshVar proofSupport 3
  let b : Var := freshVar proofSupport 4
  have fresh_x_ne_y : x ≠ y :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have fresh_y_ne_x : y ≠ x := Ne.symm fresh_x_ne_y
  have fresh_x_ne_z : x ≠ z :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 2
    exact freshVar_injective proofSupport (i := 0) (j := 2) (by decide)
  have fresh_z_ne_x : z ≠ x := Ne.symm fresh_x_ne_z
  have fresh_x_ne_a : x ≠ a :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 3
    exact freshVar_injective proofSupport (i := 0) (j := 3) (by decide)
  have fresh_a_ne_x : a ≠ x := Ne.symm fresh_x_ne_a
  have fresh_x_ne_b : x ≠ b :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 4
    exact freshVar_injective proofSupport (i := 0) (j := 4) (by decide)
  have fresh_b_ne_x : b ≠ x := Ne.symm fresh_x_ne_b
  have fresh_y_ne_z : y ≠ z :=
    by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 2
    exact freshVar_injective proofSupport (i := 1) (j := 2) (by decide)
  have fresh_z_ne_y : z ≠ y := Ne.symm fresh_y_ne_z
  have fresh_y_ne_a : y ≠ a :=
    by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 3
    exact freshVar_injective proofSupport (i := 1) (j := 3) (by decide)
  have fresh_a_ne_y : a ≠ y := Ne.symm fresh_y_ne_a
  have fresh_y_ne_b : y ≠ b :=
    by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 4
    exact freshVar_injective proofSupport (i := 1) (j := 4) (by decide)
  have fresh_b_ne_y : b ≠ y := Ne.symm fresh_y_ne_b
  have fresh_a_ne_b : a ≠ b :=
    by
    change freshVar proofSupport 3 ≠ freshVar proofSupport 4
    exact freshVar_injective proofSupport (i := 3) (j := 4) (by decide)
  have fresh_b_ne_a : b ≠ a := Ne.symm fresh_a_ne_b
  have dv_cache_0001 : y ∉ ((synC1c)).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c,
          compact_fv_not_mem_empty, not_false_eq_true])
  have dv_cache_0002 : y ∉ ((synCpw1 (synCuni (.cv x)))).fv :=
    by
    clear dv_cache_0001
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cuni,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton, fresh_y_ne_x,
          not_false_eq_true])
  have dv_cache_0003 : x ≠ y :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact (show x ≠ y from (by exact fresh_x_ne_y))
  have dv_cache_0004 : z ∉ ((Class.cv y)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact
      (by
        have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_z_ne_y, not_false_eq_true])
  have dv_cache_0005 : z ∉ ((synCvv)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact
      (by
        have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv,
          compact_fv_not_mem_empty, not_false_eq_true])
  have dv_cache_0006 : z ∉ ((Class.cv x)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact
      (by
        have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_z_ne_x, not_false_eq_true])
  have dv_cache_0007 : z ∉ ((Wff.classEq (.cv y) (synCpw1 (synCuni (.cv x))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006
    exact
      (by
        have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cuni, Finset.mem_union,
          Finset.mem_singleton, fresh_z_ne_y, fresh_z_ne_x, or_false, not_false_eq_true])
  have dv_cache_0008 : x ∉ ((synCsn (.cv z))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton, fresh_x_ne_z,
          not_false_eq_true])
  have dv_cache_0009 : x ∉ ((Wff.classEq (.cv y) (synCpw1 (.cv z)))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1, Finset.mem_union,
          Finset.mem_singleton, fresh_x_ne_y, fresh_x_ne_z, or_false, not_false_eq_true])
  have dv_cache_0010 : y ∉ ((synCpw (synC1c))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c, compact_fv_not_mem_empty,
          not_false_eq_true])
  have dv_cache_0011 : a ∉ ((Class.cv x)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010
    exact
      (by
        have compact_fv_not_mem_empty : a ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_a_ne_x, not_false_eq_true])
  have dv_cache_0012 : b ∉ ((Class.cv y)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
    exact
      (by
        have compact_fv_not_mem_empty : b ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_b_ne_y, not_false_eq_true])
  have dv_cache_0013 : b ∉ ((Wff.classEq (.cv x) (synCsn (.cv a)))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012
    exact
      (by
        have compact_fv_not_mem_empty : b ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, Finset.mem_union,
          Finset.mem_singleton, fresh_b_ne_x, fresh_b_ne_a, or_false, not_false_eq_true])
  have dv_cache_0014 : a ∉ ((Wff.classEq (.cv y) (synCsn (.cv b)))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013
    exact
      (by
        have compact_fv_not_mem_empty : a ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, Finset.mem_union,
          Finset.mem_singleton, fresh_a_ne_y, fresh_a_ne_b, or_false, not_false_eq_true])
  have dv_cache_0015 :
    a ∉
      ((Wff.imp (.classEq (synCfv (synCpw1fn) (.cv x)) (synCfv (synCpw1fn) (.cv y)))
          (.objEq x y))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014
    exact
      (by
        have compact_fv_not_mem_empty : a ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1fn,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CoreFVSimp.fv_wff_objEq, Finset.mem_union, Finset.mem_insert,
          Finset.mem_singleton, fresh_a_ne_x, fresh_a_ne_y, compact_fv_not_mem_empty,
          or_false, not_false_eq_true])
  have dv_cache_0016 :
    b ∉
      ((Wff.imp (.classEq (synCfv (synCpw1fn) (.cv x)) (synCfv (synCpw1fn) (.cv y)))
          (.objEq x y))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015
    exact
      (by
        have compact_fv_not_mem_empty : b ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1fn,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CoreFVSimp.fv_wff_objEq, Finset.mem_union, Finset.mem_insert,
          Finset.mem_singleton, fresh_b_ne_x, fresh_b_ne_y, compact_fv_not_mem_empty,
          or_false, not_false_eq_true])
  have dv_cache_0017 : x ∉ ((synC1c)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c,
          compact_fv_not_mem_empty, not_false_eq_true])
  have dv_cache_0018 : x ∉ ((synCpw1fn)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1fn,
          compact_fv_not_mem_empty, not_false_eq_true])
  have dv_cache_0019 : y ∉ ((synCpw1fn)).fv :=
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
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1fn,
          compact_fv_not_mem_empty, not_false_eq_true])
  have p0000 := @gFnpw1fn
  have p0001 := NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominalDfPw1fn x
  have p0002 :=
    @gRnmpt x y (synC1c) (synCpw1 (synCuni (.cv x))) (synCpw1fn) dv_cache_0001
      dv_cache_0002 dv_cache_0003 p0001
  have p0003 := @gVex y
  have p0004 := @gSspw1 z (.cv y) (synCvv) dv_cache_0004 dv_cache_0005 p0003
  have p0005 := @gDf1c2
  have p0006 := @gSseq2i (synC1c) (synCpw1 (synCvv)) (.cv y) p0005
  have p0007 := @gSsv (.cv z)
  have p0008 :=
    @gBiantrur (synWss (.cv z) (synCvv)) (.classEq (.cv y) (synCpw1 (.cv z))) p0007
  have p0009 :=
    @gExbii (.classEq (.cv y) (synCpw1 (.cv z)))
      (synWa (synWss (.cv z) (synCvv)) (.classEq (.cv y) (synCpw1 (.cv z)))) z p0008
  have p0010 :=
    @gN3bitr4i (synWss (.cv y) (synCpw1 (synCvv)))
      (synWex z (synWa (synWss (.cv z) (synCvv)) (.classEq (.cv y) (synCpw1 (.cv z)))))
      (synWss (.cv y) (synC1c)) (synWex z (.classEq (.cv y) (synCpw1 (.cv z)))) p0004
      p0006 p0009
  have p0011 := @gElpw (.cv y) (synC1c) p0003
  have p0012 :=
    (Nominal.biimpRefl (synWrex x (synC1c) (.classEq (.cv y) (synCpw1 (synCuni (.cv x))))))
  have p0013 := @gEl1c z (.cv x) dv_cache_0006
  have p0014 :=
    @gAnbi1i (.classMem (.cv x) (synC1c))
      (synWex z (.classEq (.cv x) (synCsn (.cv z))))
      (.classEq (.cv y) (synCpw1 (synCuni (.cv x)))) p0013
  have p0015 :=
    @gN1941v (.classEq (.cv x) (synCsn (.cv z)))
      (.classEq (.cv y) (synCpw1 (synCuni (.cv x)))) z dv_cache_0007
  have p0016 :=
    @gBitr4i
      (synWa (.classMem (.cv x) (synC1c)) (.classEq (.cv y) (synCpw1 (synCuni (.cv x)))))
      (synWa (synWex z (.classEq (.cv x) (synCsn (.cv z))))
        (.classEq (.cv y) (synCpw1 (synCuni (.cv x)))))
      (synWex z (synWa (.classEq (.cv x) (synCsn (.cv z)))
          (.classEq (.cv y) (synCpw1 (synCuni (.cv x))))))
      p0014 p0015
  have p0017 :=
    @gExbii
      (synWa (.classMem (.cv x) (synC1c)) (.classEq (.cv y) (synCpw1 (synCuni (.cv x)))))
      (synWex z (synWa (.classEq (.cv x) (synCsn (.cv z)))
          (.classEq (.cv y) (synCpw1 (synCuni (.cv x))))))
      x p0016
  have p0018 :=
    @gExcom
      (synWa (.classEq (.cv x) (synCsn (.cv z)))
        (.classEq (.cv y) (synCpw1 (synCuni (.cv x)))))
      x z
  have p0019 := @gSnex (.cv z)
  have p0020 := @gUnieq (.cv x) (synCsn (.cv z))
  have p0021 := @gVex z
  have p0022 := @gUnisn (.cv z) p0021
  have p0023 :=
    @gSyl6eq (.classEq (.cv x) (synCsn (.cv z))) (synCuni (.cv x))
      (synCuni (synCsn (.cv z))) (.cv z) p0020 p0022
  have p0024 := @gPw1eq (synCuni (.cv x)) (.cv z)
  have p0025 :=
    @gSyl (.classEq (.cv x) (synCsn (.cv z))) (.classEq (synCuni (.cv x)) (.cv z))
      (.classEq (synCpw1 (synCuni (.cv x))) (synCpw1 (.cv z))) p0023 p0024
  have p0026 :=
    @gEqeq2d (.classEq (.cv x) (synCsn (.cv z))) (synCpw1 (synCuni (.cv x)))
      (synCpw1 (.cv z)) (.cv y) p0025
  have p0027 :=
    @gCeqsexv (.classEq (.cv y) (synCpw1 (synCuni (.cv x))))
      (.classEq (.cv y) (synCpw1 (.cv z))) x (synCsn (.cv z)) dv_cache_0008
      dv_cache_0009 p0019 p0026
  have p0028 :=
    @gExbii
      (synWex x (synWa (.classEq (.cv x) (synCsn (.cv z)))
          (.classEq (.cv y) (synCpw1 (synCuni (.cv x))))))
      (.classEq (.cv y) (synCpw1 (.cv z))) z p0027
  have p0029 :=
    @gBitri
      (synWex x (synWex z (synWa (.classEq (.cv x) (synCsn (.cv z)))
            (.classEq (.cv y) (synCpw1 (synCuni (.cv x)))))))
      (synWex z (synWex x (synWa (.classEq (.cv x) (synCsn (.cv z)))
            (.classEq (.cv y) (synCpw1 (synCuni (.cv x)))))))
      (synWex z (.classEq (.cv y) (synCpw1 (.cv z)))) p0018 p0028
  have p0030 :=
    @gN3bitri (synWrex x (synC1c) (.classEq (.cv y) (synCpw1 (synCuni (.cv x)))))
      (synWex x (synWa (.classMem (.cv x) (synC1c))
          (.classEq (.cv y) (synCpw1 (synCuni (.cv x))))))
      (synWex x (synWex z (synWa (.classEq (.cv x) (synCsn (.cv z)))
            (.classEq (.cv y) (synCpw1 (synCuni (.cv x)))))))
      (synWex z (.classEq (.cv y) (synCpw1 (.cv z)))) p0012 p0017 p0029
  have p0031 :=
    @gN3bitr4i (synWss (.cv y) (synC1c))
      (synWex z (.classEq (.cv y) (synCpw1 (.cv z))))
      (.classMem (.cv y) (synCpw (synC1c)))
      (synWrex x (synC1c) (.classEq (.cv y) (synCpw1 (synCuni (.cv x))))) p0010 p0011
      p0030
  have p0032 :=
    @gEqabi (synWrex x (synC1c) (.classEq (.cv y) (synCpw1 (synCuni (.cv x))))) y
      (synCpw (synC1c)) dv_cache_0010 p0031
  have p0033 :=
    @gEqtr4i (synCrn (synCpw1fn))
      (.cab y (synWrex x (synC1c) (.classEq (.cv y) (synCpw1 (synCuni (.cv x))))))
      (synCpw (synC1c)) p0002 p0032
  have p0034 := @gEl1c a (.cv x) dv_cache_0011
  have p0035 := @gEl1c b (.cv y) dv_cache_0012
  have p0036 :=
    @gAnbi12i (.classMem (.cv x) (synC1c))
      (synWex a (.classEq (.cv x) (synCsn (.cv a)))) (.classMem (.cv y) (synC1c))
      (synWex b (.classEq (.cv y) (synCsn (.cv b)))) p0034 p0035
  have p0037 :=
    @gEeanv (.classEq (.cv x) (synCsn (.cv a))) (.classEq (.cv y) (synCsn (.cv b))) a b
      dv_cache_0013 dv_cache_0014
  have p0038 :=
    @gBitr4i (synWa (.classMem (.cv x) (synC1c)) (.classMem (.cv y) (synC1c)))
      (synWa (synWex a (.classEq (.cv x) (synCsn (.cv a))))
        (synWex b (.classEq (.cv y) (synCsn (.cv b)))))
      (synWex a (synWex b (synWa (.classEq (.cv x) (synCsn (.cv a)))
            (.classEq (.cv y) (synCsn (.cv b))))))
      p0036 p0037
  have p0039 := @gPw111 (.cv a) (.cv b)
  have p0040_e00_recanon :
    Nominal.NPrf (synWb (.classEq (synCpw1 (.cv a)) (synCpw1 (.cv b))) (.objEq a b)) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold synWb synCpw1 synCin synCcompl synCnin synWnan synWa synCpw synWss
          synC1c synWex synCsn
        simp (config :=
          { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_class_cv]
        apply Nominal.RecanonTransportDev.TRecanonWff.neg
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · apply Nominal.RecanonTransportDev.TRecanonWff.imp
          · exact Nominal.RecanonTransportDev.TRecanonWff.same _
          · exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
        · apply Nominal.RecanonTransportDev.TRecanonWff.neg
          apply Nominal.RecanonTransportDev.TRecanonWff.imp
          · exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
          · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0039
  have p0040 :=
    @gBiimpi (.classEq (synCpw1 (.cv a)) (synCpw1 (.cv b))) (.objEq a b)
      p0040_e00_recanon
  have p0041 :=
    @gA1i (.imp (.classEq (synCpw1 (.cv a)) (synCpw1 (.cv b))) (.objEq a b))
      (synWa (.classEq (.cv x) (synCsn (.cv a))) (.classEq (.cv y) (synCsn (.cv b))))
      p0040
  have p0042 := @gFveq2 (.cv x) (synCsn (.cv a)) (synCpw1fn)
  have p0043 := @gVex a
  have p0044 := @gPw1fnval (.cv a) p0043
  have p0045 :=
    @gSyl6eq (.classEq (.cv x) (synCsn (.cv a))) (synCfv (synCpw1fn) (.cv x))
      (synCfv (synCpw1fn) (synCsn (.cv a))) (synCpw1 (.cv a)) p0042 p0044
  have p0046 := @gFveq2 (.cv y) (synCsn (.cv b)) (synCpw1fn)
  have p0047 := @gVex b
  have p0048 := @gPw1fnval (.cv b) p0047
  have p0049 :=
    @gSyl6eq (.classEq (.cv y) (synCsn (.cv b))) (synCfv (synCpw1fn) (.cv y))
      (synCfv (synCpw1fn) (synCsn (.cv b))) (synCpw1 (.cv b)) p0046 p0048
  have p0050 :=
    @gEqeqan12d (.classEq (.cv x) (synCsn (.cv a))) (.classEq (.cv y) (synCsn (.cv b)))
      (synCfv (synCpw1fn) (.cv x)) (synCpw1 (.cv a)) (synCfv (synCpw1fn) (.cv y))
      (synCpw1 (.cv b)) p0045 p0049
  have p0051 := @gEqeq12 (.cv x) (synCsn (.cv a)) (.cv y) (synCsn (.cv b))
  have p0052 := @gSneqb (.cv a) (.cv b) p0043
  have p0053_e00_recanon :
    Nominal.NPrf
      (.imp (synWa (.classEq (.cv x) (synCsn (.cv a))) (.classEq (.cv y) (synCsn (.cv b))))
        (synWb (.objEq x y) (.classEq (synCsn (.cv a)) (synCsn (.cv b))))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold synWa synCsn synWb
        simp (config :=
          { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_class_cv]
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · exact Nominal.RecanonTransportDev.TRecanonWff.same _
        · apply Nominal.RecanonTransportDev.TRecanonWff.neg
          apply Nominal.RecanonTransportDev.TRecanonWff.imp
          · apply Nominal.RecanonTransportDev.TRecanonWff.imp
            · exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
            · exact Nominal.RecanonTransportDev.TRecanonWff.same _
          · apply Nominal.RecanonTransportDev.TRecanonWff.neg
            apply Nominal.RecanonTransportDev.TRecanonWff.imp
            · exact Nominal.RecanonTransportDev.TRecanonWff.same _
            · exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _)
      p0051
  have p0053_e01_recanon :
    Nominal.NPrf (synWb (.classEq (synCsn (.cv a)) (synCsn (.cv b))) (.objEq a b)) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold synWb synCsn
        simp (config :=
          { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_class_cv]
        apply Nominal.RecanonTransportDev.TRecanonWff.neg
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · apply Nominal.RecanonTransportDev.TRecanonWff.imp
          · exact Nominal.RecanonTransportDev.TRecanonWff.same _
          · exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
        · apply Nominal.RecanonTransportDev.TRecanonWff.neg
          apply Nominal.RecanonTransportDev.TRecanonWff.imp
          · exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
          · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0052
  have p0053 :=
    @gSyl6bb
      (synWa (.classEq (.cv x) (synCsn (.cv a))) (.classEq (.cv y) (synCsn (.cv b))))
      (.objEq x y) (.classEq (synCsn (.cv a)) (synCsn (.cv b))) (.objEq a b)
      p0053_e00_recanon p0053_e01_recanon
  have p0054 :=
    @gN3imtr4d
      (synWa (.classEq (.cv x) (synCsn (.cv a))) (.classEq (.cv y) (synCsn (.cv b))))
      (.classEq (synCpw1 (.cv a)) (synCpw1 (.cv b))) (.objEq a b)
      (.classEq (synCfv (synCpw1fn) (.cv x)) (synCfv (synCpw1fn) (.cv y)))
      (.objEq x y) p0041 p0050 p0053
  have p0055 :=
    @gExlimivv
      (synWa (.classEq (.cv x) (synCsn (.cv a))) (.classEq (.cv y) (synCsn (.cv b))))
      (.imp (.classEq (synCfv (synCpw1fn) (.cv x)) (synCfv (synCpw1fn) (.cv y)))
        (.objEq x y))
      a b dv_cache_0015 dv_cache_0016 p0054
  have p0056 :=
    @gSylbi (synWa (.classMem (.cv x) (synC1c)) (.classMem (.cv y) (synC1c)))
      (synWex a (synWex b (synWa (.classEq (.cv x) (synCsn (.cv a)))
            (.classEq (.cv y) (synCsn (.cv b))))))
      (.imp (.classEq (synCfv (synCpw1fn) (.cv x)) (synCfv (synCpw1fn) (.cv y)))
        (.objEq x y))
      p0038 p0055
  have p0057 :=
    @gRgen2a
      (.imp (.classEq (synCfv (synCpw1fn) (.cv x)) (synCfv (synCpw1fn) (.cv y)))
        (.objEq x y))
      x y (synC1c) dv_cache_0001 p0056
  have p0058 :=
    @gDff1o6 x y (synC1c) (synCpw (synC1c)) (synCpw1fn) dv_cache_0017 dv_cache_0001
      dv_cache_0018 dv_cache_0019 dv_cache_0003
  have p0059_e03_recanon :
    Nominal.NPrf
      (synWb (synWf1o (synCpw1fn) (synC1c) (synCpw (synC1c)))
        (synW3a (synWfn (synCpw1fn) (synC1c))
          (.classEq (synCrn (synCpw1fn)) (synCpw (synC1c))) (synWral x (synC1c)
            (synWral y (synC1c) (.imp
                (.classEq (synCfv (synCpw1fn) (.cv x)) (synCfv (synCpw1fn) (.cv y)))
                (.objEq x y)))))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold synWb synWf1o synWa synWf1 synWfo synCpw1fn synCmpt synCopab
          synWex synC1c synCpw1 synCin synCcompl synCnin synWnan synCpw synWss
          synCuni synW3a synWfn synCrn synCima synWrex synWbr synCop synCun
          synCvv synWral
        simp (config :=
          {
            failIfUnchanged :=
              false }) only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv]
        apply Nominal.RecanonTransportDev.TRecanonWff.neg
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · apply Nominal.RecanonTransportDev.TRecanonWff.imp
          · exact Nominal.RecanonTransportDev.TRecanonWff.same _
          · apply Nominal.RecanonTransportDev.TRecanonWff.neg
            apply Nominal.RecanonTransportDev.TRecanonWff.imp
            · exact Nominal.RecanonTransportDev.TRecanonWff.same _
            · apply Nominal.RecanonTransportDev.TRecanonWff.neg
              apply Nominal.RecanonTransportDev.TRecanonWff.all
              apply Nominal.RecanonTransportDev.TRecanonWff.imp
              · exact Nominal.RecanonTransportDev.TRecanonWff.same _
              · apply Nominal.RecanonTransportDev.TRecanonWff.all
                apply Nominal.RecanonTransportDev.TRecanonWff.imp
                · exact Nominal.RecanonTransportDev.TRecanonWff.same _
                · apply Nominal.RecanonTransportDev.TRecanonWff.imp
                  · exact Nominal.RecanonTransportDev.TRecanonWff.same _
                  · exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
        · apply Nominal.RecanonTransportDev.TRecanonWff.neg
          apply Nominal.RecanonTransportDev.TRecanonWff.imp
          · apply Nominal.RecanonTransportDev.TRecanonWff.neg
            apply Nominal.RecanonTransportDev.TRecanonWff.imp
            · exact Nominal.RecanonTransportDev.TRecanonWff.same _
            · apply Nominal.RecanonTransportDev.TRecanonWff.neg
              apply Nominal.RecanonTransportDev.TRecanonWff.all
              apply Nominal.RecanonTransportDev.TRecanonWff.imp
              · exact Nominal.RecanonTransportDev.TRecanonWff.same _
              · apply Nominal.RecanonTransportDev.TRecanonWff.all
                apply Nominal.RecanonTransportDev.TRecanonWff.imp
                · exact Nominal.RecanonTransportDev.TRecanonWff.same _
                · apply Nominal.RecanonTransportDev.TRecanonWff.imp
                  · exact Nominal.RecanonTransportDev.TRecanonWff.same _
                  · exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
          · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0058
  have p0059 :=
    @gMpbir3an (synWf1o (synCpw1fn) (synC1c) (synCpw (synC1c)))
      (synWfn (synCpw1fn) (synC1c))
      (.classEq (synCrn (synCpw1fn)) (synCpw (synC1c)))
      (synWral x (synC1c) (synWral y (synC1c)
          (.imp (.classEq (synCfv (synCpw1fn) (.cv x)) (synCfv (synCpw1fn) (.cv y)))
            (.objEq x y))))
      p0000 p0033 p0057 p0059_e03_recanon
  exact p0059


end NFChoice.DirectNominalPrf.WPPReplay

end

/-! Certificates from `NominalWPPReplayChunk013Compact001Part012`. -/


section

namespace NFChoice.DirectNominalPrf.WPPReplay

open scoped Fol
open NFChoice.Foundation
open NFChoice.SemanticCore
open NFChoice.ReplaySupport
open NFChoice.Compiler.CompactSourceSyntax

/-- Checked nominal proof certificate identified upstream as `g_fnfullfunlem1`. -/
@[expose]
noncomputable def gFnfullfunlem1 (x : Var) (A : Class) (B : Class) (F : Class)
    (dv_A_x : x ∉ A.fv) (dv_B_x : x ∉ B.fv) (dv_F_x : x ∉ F.fv) :
    Nominal.NPrf
      (synWb (synWbr A (synCdif (synCcom (synCid) F) (synCcom (synCcompl (synCid)) F))
          B) (synWa (synWbr A F B)
          (.all x (.imp (synWbr A F (.cv x)) (.classEq (.cv x) B))))) :=
  by
  let proofSupport : Finset Var := ({ x } : Finset Var) ∪ A.fv ∪ B.fv ∪ F.fv
  let y : Var := freshVar proofSupport 0
  have fresh_y : y ∉ proofSupport :=
    by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_y_ne_x : y ≠ x := by
    intro h
    exact
      fresh_y
        (Finset.mem_union_left _ (Finset.mem_union_left _
            (Finset.mem_union_left _ (Finset.mem_singleton.mpr h))))
  have fresh_x_ne_y : x ≠ y := Ne.symm fresh_y_ne_x
  have fresh_y_not_A : y ∉ A.fv := by
    intro h
    exact
      fresh_y
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))
  have fresh_y_not_B : y ∉ B.fv := by
    intro h
    exact fresh_y (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_y_not_F : y ∉ F.fv := by
    intro h
    exact fresh_y (Finset.mem_union_right _ (h))
  have dv_cache_0001 : x ∉ ((Wff.classEq (.cv y) B)).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, fresh_x_ne_y, dv_B_x, or_false, not_false_eq_true])
  have dv_cache_0002 : x ∉ (A).fv :=
    by
    clear dv_cache_0001
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_A_x, not_false_eq_true])
  have dv_cache_0003 : x ∉ ((Class.cv y)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_x_ne_y, not_false_eq_true])
  have dv_cache_0004 : x ∉ ((synCcompl (synCid))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccompl,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cid, compact_fv_not_mem_empty,
          not_false_eq_true])
  have dv_cache_0005 : x ∉ (F).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_F_x, not_false_eq_true])
  have dv_cache_0006 : y ∉ (B).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_y_not_B, not_false_eq_true])
  have dv_cache_0007 :
    y ∉
      ((synWb (synWbr A (synCdif (synCcom (synCid) F) (synCcom (synCcompl (synCid)) F))
            B) (synWa (synWbr A F B)
            (.all x (.imp (synWbr A F (.cv x)) (.classEq (.cv x) B)))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wb,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdif,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccom,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cid,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccompl,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
          NFChoice.Compiler.CoreFVSimp.fv_wff_all,
          NFChoice.Compiler.CoreFVSimp.fv_wff_imp,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, Finset.mem_union, Finset.mem_erase,
          Finset.mem_singleton, fresh_y_not_A, fresh_y_not_B, fresh_y_not_F, fresh_y_ne_x,
          compact_fv_not_mem_empty, or_false, and_false, not_false_eq_true])
  have p0000 :=
    @gBrex A B (synCdif (synCcom (synCid) F) (synCcom (synCcompl (synCid)) F))
  have p0001 :=
    @gSimprd
      (synWbr A (synCdif (synCcom (synCid) F) (synCcom (synCcompl (synCid)) F)) B)
      (.classMem A (synCvv)) (.classMem B (synCvv)) p0000
  have p0002 := @gBrex A B F
  have p0003 :=
    @gSimprd (synWbr A F B) (.classMem A (synCvv)) (.classMem B (synCvv)) p0002
  have p0004 :=
    @gAdantr (synWbr A F B) (.classMem B (synCvv))
      (.all x (.imp (synWbr A F (.cv x)) (.classEq (.cv x) B))) p0003
  have p0005 :=
    @gBreq2 (.cv y) B A
      (synCdif (synCcom (synCid) F) (synCcom (synCcompl (synCid)) F))
  have p0006 := @gBreq2 (.cv y) B A F
  have p0007 := @gEqeq2 (.cv y) B (.cv x)
  have p0008_e00_recanon :
    Nominal.NPrf (.imp (.classEq (.cv y) B) (synWb (.objEq x y) (.classEq (.cv x) B))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold synWb
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · exact Nominal.RecanonTransportDev.TRecanonWff.same _
        · apply Nominal.RecanonTransportDev.TRecanonWff.neg
          apply Nominal.RecanonTransportDev.TRecanonWff.imp
          · apply Nominal.RecanonTransportDev.TRecanonWff.imp
            · exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
            · exact Nominal.RecanonTransportDev.TRecanonWff.same _
          · apply Nominal.RecanonTransportDev.TRecanonWff.neg
            apply Nominal.RecanonTransportDev.TRecanonWff.imp
            · exact Nominal.RecanonTransportDev.TRecanonWff.same _
            · exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _)
      p0007
  have p0008 :=
    @gImbi2d (.classEq (.cv y) B) (.objEq x y) (.classEq (.cv x) B) (synWbr A F (.cv x))
      p0008_e00_recanon
  have p0009 :=
    @gAlbidv (.classEq (.cv y) B) (.imp (synWbr A F (.cv x)) (.objEq x y))
      (.imp (synWbr A F (.cv x)) (.classEq (.cv x) B)) x dv_cache_0001 p0008
  have p0010 :=
    @gAnbi12d (.classEq (.cv y) B) (synWbr A F (.cv y)) (synWbr A F B)
      (.all x (.imp (synWbr A F (.cv x)) (.objEq x y)))
      (.all x (.imp (synWbr A F (.cv x)) (.classEq (.cv x) B))) p0006 p0009
  have p0011 :=
    @gBibi12d (.classEq (.cv y) B)
      (synWbr A (synCdif (synCcom (synCid) F) (synCcom (synCcompl (synCid)) F)) (.cv y))
      (synWbr A (synCdif (synCcom (synCid) F) (synCcom (synCcompl (synCid)) F)) B)
      (synWa (synWbr A F (.cv y)) (.all x (.imp (synWbr A F (.cv x)) (.objEq x y))))
      (synWa (synWbr A F B) (.all x (.imp (synWbr A F (.cv x)) (.classEq (.cv x) B))))
      p0005 p0010
  have p0012 :=
    @gBrdif A (.cv y) (synCcom (synCid) F) (synCcom (synCcompl (synCid)) F)
  have p0013 := @gCoi2 F
  have p0014 := @gBreqi A (.cv y) (synCcom (synCid) F) F p0013
  have p0015 :=
    @gBrco x A (.cv y) (synCcompl (synCid)) F dv_cache_0002 dv_cache_0003 dv_cache_0004
      dv_cache_0005
  have p0016 := (Nominal.biimpRefl (synWbr (.cv x) (synCcompl (synCid)) (.cv y)))
  have p0017 := @gVex x
  have p0018 := @gVex y
  have p0019 := @gOpex (.cv x) (.cv y) p0017 p0018
  have p0020 := @gElcompl (synCop (.cv x) (.cv y)) (synCid) p0019
  have p0021 := (Nominal.biimpRefl (synWbr (.cv x) (synCid) (.cv y)))
  have p0022 := @gIdeq (.cv x) (.cv y) p0018
  have p0023_e01_recanon :
    Nominal.NPrf (synWb (synWbr (.cv x) (synCid) (.cv y)) (.objEq x y)) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold synWb synWbr synCop synCun synCnin synWnan synWa synCcompl synWrex
          synWex synCphi synCid synCopab
        simp (config :=
          { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CoreFVSimp.fv_wff_objEq]
        apply Nominal.RecanonTransportDev.TRecanonWff.neg
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · apply Nominal.RecanonTransportDev.TRecanonWff.imp
          · exact Nominal.RecanonTransportDev.TRecanonWff.same _
          · exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
        · apply Nominal.RecanonTransportDev.TRecanonWff.neg
          apply Nominal.RecanonTransportDev.TRecanonWff.imp
          · exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
          · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0022
  have p0023 :=
    @gBitr3i (.classMem (synCop (.cv x) (.cv y)) (synCid))
      (synWbr (.cv x) (synCid) (.cv y)) (.objEq x y) p0021 p0023_e01_recanon
  have p0024 :=
    @gXchbinx (.classMem (synCop (.cv x) (.cv y)) (synCcompl (synCid)))
      (.classMem (synCop (.cv x) (.cv y)) (synCid)) (.objEq x y) p0020 p0023
  have p0025 :=
    @gBitri (synWbr (.cv x) (synCcompl (synCid)) (.cv y))
      (.classMem (synCop (.cv x) (.cv y)) (synCcompl (synCid))) (.neg (.objEq x y))
      p0016 p0024
  have p0026 :=
    @gAnbi2i (synWbr (.cv x) (synCcompl (synCid)) (.cv y)) (.neg (.objEq x y))
      (synWbr A F (.cv x)) p0025
  have p0027 :=
    @gExbii
      (synWa (synWbr A F (.cv x)) (synWbr (.cv x) (synCcompl (synCid)) (.cv y)))
      (synWa (synWbr A F (.cv x)) (.neg (.objEq x y))) x p0026
  have p0028 := @gExanali (synWbr A F (.cv x)) (.objEq x y) x
  have p0029 :=
    @gN3bitrri (synWbr A (synCcom (synCcompl (synCid)) F) (.cv y))
      (synWex x
        (synWa (synWbr A F (.cv x)) (synWbr (.cv x) (synCcompl (synCid)) (.cv y))))
      (synWex x (synWa (synWbr A F (.cv x)) (.neg (.objEq x y))))
      (.neg (.all x (.imp (synWbr A F (.cv x)) (.objEq x y)))) p0015 p0027 p0028
  have p0030 :=
    @gCon1bii (.all x (.imp (synWbr A F (.cv x)) (.objEq x y)))
      (synWbr A (synCcom (synCcompl (synCid)) F) (.cv y)) p0029
  have p0031 :=
    @gAnbi12i (synWbr A (synCcom (synCid) F) (.cv y)) (synWbr A F (.cv y))
      (.neg (synWbr A (synCcom (synCcompl (synCid)) F) (.cv y)))
      (.all x (.imp (synWbr A F (.cv x)) (.objEq x y))) p0014 p0030
  have p0032 :=
    @gBitri
      (synWbr A (synCdif (synCcom (synCid) F) (synCcom (synCcompl (synCid)) F)) (.cv y))
      (synWa (synWbr A (synCcom (synCid) F) (.cv y))
        (.neg (synWbr A (synCcom (synCcompl (synCid)) F) (.cv y))))
      (synWa (synWbr A F (.cv y)) (.all x (.imp (synWbr A F (.cv x)) (.objEq x y))))
      p0012 p0031
  have p0033 :=
    @gVtoclg
      (synWb (synWbr A (synCdif (synCcom (synCid) F) (synCcom (synCcompl (synCid)) F))
          (.cv y))
        (synWa (synWbr A F (.cv y)) (.all x (.imp (synWbr A F (.cv x)) (.objEq x y)))))
      (synWb (synWbr A (synCdif (synCcom (synCid) F) (synCcom (synCcompl (synCid)) F))
          B) (synWa (synWbr A F B)
          (.all x (.imp (synWbr A F (.cv x)) (.classEq (.cv x) B)))))
      y B (synCvv) dv_cache_0006 dv_cache_0007 p0011 p0032
  have p0034 :=
    @gPm521nii
      (synWbr A (synCdif (synCcom (synCid) F) (synCcom (synCcompl (synCid)) F)) B)
      (.classMem B (synCvv))
      (synWa (synWbr A F B) (.all x (.imp (synWbr A F (.cv x)) (.classEq (.cv x) B))))
      p0001 p0004 p0033
  exact p0034

/-- Checked nominal proof certificate identified upstream as `g_fnfullfunlem2`. -/
@[expose]
noncomputable def gFnfullfunlem2 (F : Class) :
    Nominal.NPrf
      (synWfun (synCdif (synCcom (synCid) F) (synCcom (synCcompl (synCid)) F))) :=
  by
  let proofSupport : Finset Var := F.fv
  let x : Var := freshVar proofSupport 0
  let y : Var := freshVar proofSupport 1
  let z : Var := freshVar proofSupport 2
  have fresh_x : x ∉ proofSupport :=
    by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_x_not_F : x ∉ F.fv := by
    intro h
    exact fresh_x (h)
  have fresh_y : y ∉ proofSupport :=
    by
    change freshVar proofSupport 1 ∉ proofSupport
    exact freshVar_not_mem proofSupport 1
  have fresh_y_not_F : y ∉ F.fv := by
    intro h
    exact fresh_y (h)
  have fresh_z : z ∉ proofSupport :=
    by
    change freshVar proofSupport 2 ∉ proofSupport
    exact freshVar_not_mem proofSupport 2
  have fresh_z_not_F : z ∉ F.fv := by
    intro h
    exact fresh_z (h)
  have fresh_x_ne_y : x ≠ y :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have fresh_y_ne_x : y ≠ x := Ne.symm fresh_x_ne_y
  have fresh_x_ne_z : x ≠ z :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 2
    exact freshVar_injective proofSupport (i := 0) (j := 2) (by decide)
  have fresh_z_ne_x : z ≠ x := Ne.symm fresh_x_ne_z
  have fresh_y_ne_z : y ≠ z :=
    by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 2
    exact freshVar_injective proofSupport (i := 1) (j := 2) (by decide)
  have fresh_z_ne_y : z ≠ y := Ne.symm fresh_y_ne_z
  have dv_cache_0001 :
    x ∉ ((synCdif (synCcom (synCid) F) (synCcom (synCcompl (synCid)) F))).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdif,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccom,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cid,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccompl, Finset.mem_union,
          fresh_x_not_F, compact_fv_not_mem_empty, or_false, not_false_eq_true])
  have dv_cache_0002 :
    y ∉ ((synCdif (synCcom (synCid) F) (synCcom (synCcompl (synCid)) F))).fv :=
    by
    clear dv_cache_0001
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdif,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccom,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cid,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccompl, Finset.mem_union,
          fresh_y_not_F, compact_fv_not_mem_empty, or_false, not_false_eq_true])
  have dv_cache_0003 :
    z ∉ ((synCdif (synCcom (synCid) F) (synCcom (synCcompl (synCid)) F))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact
      (by
        have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdif,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccom,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cid,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccompl, Finset.mem_union,
          fresh_z_not_F, compact_fv_not_mem_empty, or_false, not_false_eq_true])
  have dv_cache_0004 : x ≠ y :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact (show x ≠ y from (by exact fresh_x_ne_y))
  have dv_cache_0005 : x ≠ z :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact (show x ≠ z from (by exact fresh_x_ne_z))
  have dv_cache_0006 : y ≠ z :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact (show y ≠ z from (by exact fresh_y_ne_z))
  have dv_cache_0007 : z ∉ ((Class.cv x)).fv :=
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
          fresh_z_ne_x, not_false_eq_true])
  have dv_cache_0008 : z ∉ ((Class.cv y)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007
    exact
      (by
        have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_z_ne_y, not_false_eq_true])
  have dv_cache_0009 : z ∉ (F).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008
    exact
      (by
        have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_z_not_F, not_false_eq_true])
  have dv_cache_0010 : y ∉ ((Class.cv x)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_y_ne_x, not_false_eq_true])
  have dv_cache_0011 : y ∉ ((Class.cv z)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_y_ne_z, not_false_eq_true])
  have dv_cache_0012 : y ∉ (F).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_y_not_F, not_false_eq_true])
  have p0000 :=
    @gDffun2 x y z (synCdif (synCcom (synCid) F) (synCcom (synCcompl (synCid)) F))
      dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006
  have p0001 :=
    @gFnfullfunlem1 z (.cv x) (.cv y) F dv_cache_0007 dv_cache_0008 dv_cache_0009
  have p0002 :=
    @gFnfullfunlem1 y (.cv x) (.cv z) F dv_cache_0010 dv_cache_0011 dv_cache_0012
  have p0003 := @gSp (.imp (synWbr (.cv x) F (.cv y)) (.objEq y z)) y
  have p0004 :=
    @gImpcom (.all y (.imp (synWbr (.cv x) F (.cv y)) (.objEq y z)))
      (synWbr (.cv x) F (.cv y)) (.objEq y z) p0003
  have p0005 :=
    @gAd2ant2rl (synWbr (.cv x) F (.cv y))
      (.all y (.imp (synWbr (.cv x) F (.cv y)) (.objEq y z))) (.objEq y z)
      (.all z (.imp (synWbr (.cv x) F (.cv z)) (.objEq z y))) (synWbr (.cv x) F (.cv z))
      p0004
  have p0006_e00_recanon :
    Nominal.NPrf
      (synWb (synWbr (.cv x)
          (synCdif (synCcom (synCid) F) (synCcom (synCcompl (synCid)) F)) (.cv y))
        (synWa (synWbr (.cv x) F (.cv y))
          (.all z (.imp (synWbr (.cv x) F (.cv z)) (.objEq z y))))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold synWb synWbr synCop synCun synCnin synWnan synWa synCcompl synWrex
          synWex synCphi synCdif synCin synCcom synCopab synCid
        simp (config :=
          { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_class_cv]
        apply Nominal.RecanonTransportDev.TRecanonWff.neg
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · apply Nominal.RecanonTransportDev.TRecanonWff.imp
          · exact Nominal.RecanonTransportDev.TRecanonWff.same _
          · apply Nominal.RecanonTransportDev.TRecanonWff.neg
            apply Nominal.RecanonTransportDev.TRecanonWff.imp
            · exact Nominal.RecanonTransportDev.TRecanonWff.same _
            · apply Nominal.RecanonTransportDev.TRecanonWff.neg
              apply Nominal.RecanonTransportDev.TRecanonWff.all
              apply Nominal.RecanonTransportDev.TRecanonWff.imp
              · exact Nominal.RecanonTransportDev.TRecanonWff.same _
              · exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
        · apply Nominal.RecanonTransportDev.TRecanonWff.neg
          apply Nominal.RecanonTransportDev.TRecanonWff.imp
          · apply Nominal.RecanonTransportDev.TRecanonWff.neg
            apply Nominal.RecanonTransportDev.TRecanonWff.imp
            · exact Nominal.RecanonTransportDev.TRecanonWff.same _
            · apply Nominal.RecanonTransportDev.TRecanonWff.neg
              apply Nominal.RecanonTransportDev.TRecanonWff.all
              apply Nominal.RecanonTransportDev.TRecanonWff.imp
              · exact Nominal.RecanonTransportDev.TRecanonWff.same _
              · exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
          · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0001
  have p0006_e01_recanon :
    Nominal.NPrf
      (synWb (synWbr (.cv x)
          (synCdif (synCcom (synCid) F) (synCcom (synCcompl (synCid)) F)) (.cv z))
        (synWa (synWbr (.cv x) F (.cv z))
          (.all y (.imp (synWbr (.cv x) F (.cv y)) (.objEq y z))))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold synWb synWbr synCop synCun synCnin synWnan synWa synCcompl synWrex
          synWex synCphi synCdif synCin synCcom synCopab synCid
        simp (config :=
          { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_class_cv]
        apply Nominal.RecanonTransportDev.TRecanonWff.neg
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · apply Nominal.RecanonTransportDev.TRecanonWff.imp
          · exact Nominal.RecanonTransportDev.TRecanonWff.same _
          · apply Nominal.RecanonTransportDev.TRecanonWff.neg
            apply Nominal.RecanonTransportDev.TRecanonWff.imp
            · exact Nominal.RecanonTransportDev.TRecanonWff.same _
            · apply Nominal.RecanonTransportDev.TRecanonWff.neg
              apply Nominal.RecanonTransportDev.TRecanonWff.all
              apply Nominal.RecanonTransportDev.TRecanonWff.imp
              · exact Nominal.RecanonTransportDev.TRecanonWff.same _
              · exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
        · apply Nominal.RecanonTransportDev.TRecanonWff.neg
          apply Nominal.RecanonTransportDev.TRecanonWff.imp
          · apply Nominal.RecanonTransportDev.TRecanonWff.neg
            apply Nominal.RecanonTransportDev.TRecanonWff.imp
            · exact Nominal.RecanonTransportDev.TRecanonWff.same _
            · apply Nominal.RecanonTransportDev.TRecanonWff.neg
              apply Nominal.RecanonTransportDev.TRecanonWff.all
              apply Nominal.RecanonTransportDev.TRecanonWff.imp
              · exact Nominal.RecanonTransportDev.TRecanonWff.same _
              · exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
          · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0002
  have p0006 :=
    @gSyl2anb
      (synWbr (.cv x)
        (synCdif (synCcom (synCid) F) (synCcom (synCcompl (synCid)) F)) (.cv y))
      (synWa (synWbr (.cv x) F (.cv y))
        (.all z (.imp (synWbr (.cv x) F (.cv z)) (.objEq z y))))
      (synWa (synWbr (.cv x) F (.cv z))
        (.all y (.imp (synWbr (.cv x) F (.cv y)) (.objEq y z))))
      (.objEq y z)
      (synWbr (.cv x)
        (synCdif (synCcom (synCid) F) (synCcom (synCcompl (synCid)) F)) (.cv z))
      p0006_e00_recanon p0006_e01_recanon p0005
  have p0007 :=
    @gGen2
      (.imp (synWa (synWbr (.cv x)
            (synCdif (synCcom (synCid) F) (synCcom (synCcompl (synCid)) F)) (.cv y))
          (synWbr (.cv x) (synCdif (synCcom (synCid) F) (synCcom (synCcompl (synCid)) F))
            (.cv z))) (.objEq y z))
      y z p0006
  have p0008 :=
    @gMpgbir
      (synWfun (synCdif (synCcom (synCid) F) (synCcom (synCcompl (synCid)) F)))
      (.all y (.all z (.imp (synWa (synWbr (.cv x)
                (synCdif (synCcom (synCid) F) (synCcom (synCcompl (synCid)) F)) (.cv y))
              (synWbr (.cv x)
                (synCdif (synCcom (synCid) F) (synCcom (synCcompl (synCid)) F)) (.cv z)))
            (.objEq y z))))
      x p0000 p0007
  exact p0008

/-- Checked nominal proof certificate identified upstream as `g_fnfullfun`. -/
@[expose]
noncomputable def gFnfullfun (F : Class) :
    Nominal.NPrf (synWfn (synCfullfun F) (synCvv)) :=
  by
  have p0000 := @gFnfullfunlem2 F
  have p0001 :=
    @gFunfn (synCdif (synCcom (synCid) F) (synCcom (synCcompl (synCid)) F))
  have p0002 :=
    @gMpbi
      (synWfun (synCdif (synCcom (synCid) F) (synCcom (synCcompl (synCid)) F)))
      (synWfn (synCdif (synCcom (synCid) F) (synCcom (synCcompl (synCid)) F))
        (synCdm (synCdif (synCcom (synCid) F) (synCcom (synCcompl (synCid)) F))))
      p0000 p0001
  have p0003 := @gN0ex
  have p0004 :=
    @gFnconstg
      (synCcompl
        (synCdm (synCdif (synCcom (synCid) F) (synCcom (synCcompl (synCid)) F))))
      (synC0) (synCvv)
  have p0005 := Nominal.mp p0003 p0004
  have p0006 :=
    @gPm32i
      (synWfn (synCdif (synCcom (synCid) F) (synCcom (synCcompl (synCid)) F))
        (synCdm (synCdif (synCcom (synCid) F) (synCcom (synCcompl (synCid)) F))))
      (synWfn (synCxp (synCcompl (synCdm
              (synCdif (synCcom (synCid) F) (synCcom (synCcompl (synCid)) F))))
          (synCsn (synC0))) (synCcompl (synCdm
            (synCdif (synCcom (synCid) F) (synCcom (synCcompl (synCid)) F)))))
      p0002 p0005
  have p0007 :=
    @gIncompl
      (synCdm (synCdif (synCcom (synCid) F) (synCcom (synCcompl (synCid)) F)))
  have p0008 :=
    @gFnun
      (synCdm (synCdif (synCcom (synCid) F) (synCcom (synCcompl (synCid)) F)))
      (synCcompl
        (synCdm (synCdif (synCcom (synCid) F) (synCcom (synCcompl (synCid)) F))))
      (synCdif (synCcom (synCid) F) (synCcom (synCcompl (synCid)) F))
      (synCxp (synCcompl
          (synCdm (synCdif (synCcom (synCid) F) (synCcom (synCcompl (synCid)) F))))
        (synCsn (synC0)))
  have p0009 :=
    @gMp2an
      (synWa (synWfn (synCdif (synCcom (synCid) F) (synCcom (synCcompl (synCid)) F))
          (synCdm (synCdif (synCcom (synCid) F) (synCcom (synCcompl (synCid)) F))))
        (synWfn (synCxp (synCcompl (synCdm
                (synCdif (synCcom (synCid) F) (synCcom (synCcompl (synCid)) F))))
            (synCsn (synC0))) (synCcompl (synCdm
              (synCdif (synCcom (synCid) F) (synCcom (synCcompl (synCid)) F))))))
      (.classEq (synCin
          (synCdm (synCdif (synCcom (synCid) F) (synCcom (synCcompl (synCid)) F)))
          (synCcompl (synCdm
              (synCdif (synCcom (synCid) F) (synCcom (synCcompl (synCid)) F))))) (synC0))
      (synWfn (synCun (synCdif (synCcom (synCid) F) (synCcom (synCcompl (synCid)) F))
          (synCxp (synCcompl (synCdm
                (synCdif (synCcom (synCid) F) (synCcom (synCcompl (synCid)) F))))
            (synCsn (synC0)))) (synCun
          (synCdm (synCdif (synCcom (synCid) F) (synCcom (synCcompl (synCid)) F)))
          (synCcompl (synCdm
              (synCdif (synCcom (synCid) F) (synCcom (synCcompl (synCid)) F))))))
      p0006 p0007 p0008
  have p0010 := (Nominal.classEqRefl (synCfullfun F))
  have p0011 :=
    @gUncompl
      (synCdm (synCdif (synCcom (synCid) F) (synCcom (synCcompl (synCid)) F)))
  have p0012 :=
    @gEqcomi
      (synCun (synCdm (synCdif (synCcom (synCid) F) (synCcom (synCcompl (synCid)) F)))
        (synCcompl (synCdm
            (synCdif (synCcom (synCid) F) (synCcom (synCcompl (synCid)) F)))))
      (synCvv) p0011
  have p0013 :=
    @gFneq1 (synCvv) (synCfullfun F)
      (synCun (synCdif (synCcom (synCid) F) (synCcom (synCcompl (synCid)) F)) (synCxp
          (synCcompl (synCdm
              (synCdif (synCcom (synCid) F) (synCcom (synCcompl (synCid)) F))))
          (synCsn (synC0))))
  have p0014 :=
    @gFneq2 (synCvv)
      (synCun (synCdm (synCdif (synCcom (synCid) F) (synCcom (synCcompl (synCid)) F)))
        (synCcompl (synCdm
            (synCdif (synCcom (synCid) F) (synCcom (synCcompl (synCid)) F)))))
      (synCun (synCdif (synCcom (synCid) F) (synCcom (synCcompl (synCid)) F)) (synCxp
          (synCcompl (synCdm
              (synCdif (synCcom (synCid) F) (synCcom (synCcompl (synCid)) F))))
          (synCsn (synC0))))
  have p0015 :=
    @gSylan9bb
      (.classEq (synCfullfun F)
        (synCun (synCdif (synCcom (synCid) F) (synCcom (synCcompl (synCid)) F)) (synCxp
            (synCcompl (synCdm
                (synCdif (synCcom (synCid) F) (synCcom (synCcompl (synCid)) F))))
            (synCsn (synC0)))))
      (synWfn (synCfullfun F) (synCvv))
      (synWfn (synCun (synCdif (synCcom (synCid) F) (synCcom (synCcompl (synCid)) F))
          (synCxp (synCcompl (synCdm
                (synCdif (synCcom (synCid) F) (synCcom (synCcompl (synCid)) F))))
            (synCsn (synC0)))) (synCvv))
      (.classEq (synCvv) (synCun
          (synCdm (synCdif (synCcom (synCid) F) (synCcom (synCcompl (synCid)) F)))
          (synCcompl (synCdm
              (synCdif (synCcom (synCid) F) (synCcom (synCcompl (synCid)) F))))))
      (synWfn (synCun (synCdif (synCcom (synCid) F) (synCcom (synCcompl (synCid)) F))
          (synCxp (synCcompl (synCdm
                (synCdif (synCcom (synCid) F) (synCcom (synCcompl (synCid)) F))))
            (synCsn (synC0)))) (synCun
          (synCdm (synCdif (synCcom (synCid) F) (synCcom (synCcompl (synCid)) F)))
          (synCcompl (synCdm
              (synCdif (synCcom (synCid) F) (synCcom (synCcompl (synCid)) F))))))
      p0013 p0014
  have p0016 :=
    @gMp2an
      (.classEq (synCfullfun F)
        (synCun (synCdif (synCcom (synCid) F) (synCcom (synCcompl (synCid)) F)) (synCxp
            (synCcompl (synCdm
                (synCdif (synCcom (synCid) F) (synCcom (synCcompl (synCid)) F))))
            (synCsn (synC0)))))
      (.classEq (synCvv) (synCun
          (synCdm (synCdif (synCcom (synCid) F) (synCcom (synCcompl (synCid)) F)))
          (synCcompl (synCdm
              (synCdif (synCcom (synCid) F) (synCcom (synCcompl (synCid)) F))))))
      (synWb (synWfn (synCfullfun F) (synCvv)) (synWfn
          (synCun (synCdif (synCcom (synCid) F) (synCcom (synCcompl (synCid)) F))
            (synCxp (synCcompl (synCdm
                  (synCdif (synCcom (synCid) F) (synCcom (synCcompl (synCid)) F))))
              (synCsn (synC0)))) (synCun (synCdm
              (synCdif (synCcom (synCid) F) (synCcom (synCcompl (synCid)) F))) (synCcompl
              (synCdm
                (synCdif (synCcom (synCid) F) (synCcom (synCcompl (synCid)) F)))))))
      p0010 p0012 p0015
  have p0017 :=
    @gMpbir (synWfn (synCfullfun F) (synCvv))
      (synWfn (synCun (synCdif (synCcom (synCid) F) (synCcom (synCcompl (synCid)) F))
          (synCxp (synCcompl (synCdm
                (synCdif (synCcom (synCid) F) (synCcom (synCcompl (synCid)) F))))
            (synCsn (synC0)))) (synCun
          (synCdm (synCdif (synCcom (synCid) F) (synCcom (synCcompl (synCid)) F)))
          (synCcompl (synCdm
              (synCdif (synCcom (synCid) F) (synCcom (synCcompl (synCid)) F))))))
      p0009 p0016
  exact p0017

/-- Checked nominal proof certificate identified upstream as `g_fullfunexg`. -/
@[expose]
noncomputable def gFullfunexg (F : Class) (V : Class) :
    Nominal.NPrf (.imp (.classMem F V) (.classMem (synCfullfun F) (synCvv))) :=
  by
  have p0000 := (Nominal.classEqRefl (synCfullfun F))
  have p0001 := @gIdex
  have p0002 := @gCoexg (synCid) F (synCvv) V
  have p0003 :=
    @gMpan (.classMem (synCid) (synCvv)) (.classMem F V)
      (.classMem (synCcom (synCid) F) (synCvv)) p0001 p0002
  have p0005 := @gComplex (synCid) p0001
  have p0006 := @gCoexg (synCcompl (synCid)) F (synCvv) V
  have p0007 :=
    @gMpan (.classMem (synCcompl (synCid)) (synCvv)) (.classMem F V)
      (.classMem (synCcom (synCcompl (synCid)) F) (synCvv)) p0005 p0006
  have p0008 :=
    @gDifexg (synCcom (synCid) F) (synCcom (synCcompl (synCid)) F) (synCvv)
      (synCvv)
  have p0009 :=
    @gSyl2anc (.classMem F V) (.classMem (synCcom (synCid) F) (synCvv))
      (.classMem (synCcom (synCcompl (synCid)) F) (synCvv))
      (.classMem (synCdif (synCcom (synCid) F) (synCcom (synCcompl (synCid)) F))
        (synCvv))
      p0003 p0007 p0008
  have p0010 :=
    @gDmexg (synCdif (synCcom (synCid) F) (synCcom (synCcompl (synCid)) F))
      (synCvv)
  have p0011 :=
    @gComplexg
      (synCdm (synCdif (synCcom (synCid) F) (synCcom (synCcompl (synCid)) F)))
      (synCvv)
  have p0012 :=
    @gN3syl (.classMem F V)
      (.classMem (synCdif (synCcom (synCid) F) (synCcom (synCcompl (synCid)) F))
        (synCvv))
      (.classMem (synCdm (synCdif (synCcom (synCid) F) (synCcom (synCcompl (synCid)) F)))
        (synCvv))
      (.classMem (synCcompl
          (synCdm (synCdif (synCcom (synCid) F) (synCcom (synCcompl (synCid)) F))))
        (synCvv))
      p0009 p0010 p0011
  have p0013 := @gSnex (synC0)
  have p0014 :=
    @gXpexg
      (synCcompl
        (synCdm (synCdif (synCcom (synCid) F) (synCcom (synCcompl (synCid)) F))))
      (synCsn (synC0)) (synCvv) (synCvv)
  have p0015 :=
    @gSylancl (.classMem F V)
      (.classMem (synCcompl
          (synCdm (synCdif (synCcom (synCid) F) (synCcom (synCcompl (synCid)) F))))
        (synCvv))
      (.classMem (synCsn (synC0)) (synCvv))
      (.classMem (synCxp (synCcompl (synCdm
              (synCdif (synCcom (synCid) F) (synCcom (synCcompl (synCid)) F))))
          (synCsn (synC0))) (synCvv))
      p0012 p0013 p0014
  have p0016 :=
    @gUnexg (synCdif (synCcom (synCid) F) (synCcom (synCcompl (synCid)) F))
      (synCxp (synCcompl
          (synCdm (synCdif (synCcom (synCid) F) (synCcom (synCcompl (synCid)) F))))
        (synCsn (synC0)))
      (synCvv) (synCvv)
  have p0017 :=
    @gSyl2anc (.classMem F V)
      (.classMem (synCdif (synCcom (synCid) F) (synCcom (synCcompl (synCid)) F))
        (synCvv))
      (.classMem (synCxp (synCcompl (synCdm
              (synCdif (synCcom (synCid) F) (synCcom (synCcompl (synCid)) F))))
          (synCsn (synC0))) (synCvv))
      (.classMem (synCun (synCdif (synCcom (synCid) F) (synCcom (synCcompl (synCid)) F))
          (synCxp (synCcompl (synCdm
                (synCdif (synCcom (synCid) F) (synCcom (synCcompl (synCid)) F))))
            (synCsn (synC0)))) (synCvv))
      p0009 p0015 p0016
  have p0018 :=
    @gSyl5eqel (.classMem F V) (synCfullfun F)
      (synCun (synCdif (synCcom (synCid) F) (synCcom (synCcompl (synCid)) F)) (synCxp
          (synCcompl (synCdm
              (synCdif (synCcom (synCid) F) (synCcom (synCcompl (synCid)) F))))
          (synCsn (synC0))))
      (synCvv) p0000 p0017
  exact p0018

/-- Checked nominal proof certificate identified upstream as `g_fullfunex`. -/
@[expose]
noncomputable def gFullfunex (F : Class)
    (hyp_fullfunex_1 : Nominal.NPrf (.classMem F (synCvv))) :
    Nominal.NPrf (.classMem (synCfullfun F) (synCvv)) :=
  by
  have p0000 := @gFullfunexg F (synCvv)
  have p0001 := Nominal.mp hyp_fullfunex_1 p0000
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_fvfullfunlem1`. -/
@[expose]
noncomputable def gFvfullfunlem1 (x : Var) (y : Var) (F : Class) (dv_F_x : x ∉ F.fv)
    (dv_F_y : y ∉ F.fv) (dv_x_y : x ≠ y) :
    Nominal.NPrf
      (.classEq (synCdm (synCdif (synCcom (synCid) F) (synCcom (synCcompl (synCid)) F)))
        (.cab x (synWeu y (synWbr (.cv x) F (.cv y))))) :=
  by
  let proofSupport : Finset Var := ({ x } : Finset Var) ∪ ({ y } : Finset Var) ∪ F.fv
  let z : Var := freshVar proofSupport 0
  have fresh_z : z ∉ proofSupport :=
    by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_z_ne_x : z ≠ x := by
    intro h
    exact
      fresh_z
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_singleton.mpr h)))
  have fresh_z_ne_y : z ≠ y := by
    intro h
    exact
      fresh_z
        (Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_singleton.mpr h)))
  have fresh_y_ne_z : y ≠ z := Ne.symm fresh_z_ne_y
  have fresh_z_not_F : z ∉ F.fv := by
    intro h
    exact fresh_z (Finset.mem_union_right _ (h))
  have dv_cache_0001 : y ∉ ((Class.cv x)).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          (Ne.symm dv_x_y), not_false_eq_true])
  have dv_cache_0002 :
    y ∉ ((synCdif (synCcom (synCid) F) (synCcom (synCcompl (synCid)) F))).fv :=
    by
    clear dv_cache_0001
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdif,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccom,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cid,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccompl, Finset.mem_union,
          dv_F_y, compact_fv_not_mem_empty, or_false, not_false_eq_true])
  have dv_cache_0003 : z ∉ ((Class.cv x)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact
      (by
        have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_z_ne_x, not_false_eq_true])
  have dv_cache_0004 : z ∉ ((Class.cv y)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact
      (by
        have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_z_ne_y, not_false_eq_true])
  have dv_cache_0005 : z ∉ (F).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact
      (by
        have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_z_not_F, not_false_eq_true])
  have dv_cache_0006 : z ∉ ((synWbr (.cv x) F (.cv y))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact
      (by
        have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, fresh_z_ne_x, fresh_z_ne_y, fresh_z_not_F, or_false,
          not_false_eq_true])
  have dv_cache_0007 : y ≠ z :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006
    exact (show y ≠ z from (by exact fresh_y_ne_z))
  have dv_cache_0008 : y ∉ ((synWbr (.cv x) F (.cv z))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, (Ne.symm dv_x_y), fresh_y_ne_z, dv_F_y, or_false,
          not_false_eq_true])
  have dv_cache_0009 :
    x ∉
      ((synCdm (synCdif (synCcom (synCid) F) (synCcom (synCcompl (synCid)) F)))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdm,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdif,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccom,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cid,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccompl, Finset.mem_union,
          dv_F_x, compact_fv_not_mem_empty, or_false, not_false_eq_true])
  have p0000 :=
    @gEldm y (.cv x)
      (synCdif (synCcom (synCid) F) (synCcom (synCcompl (synCid)) F)) dv_cache_0001
      dv_cache_0002
  have p0001 :=
    @gFnfullfunlem1 z (.cv x) (.cv y) F dv_cache_0003 dv_cache_0004 dv_cache_0005
  have p0002_e00_recanon :
    Nominal.NPrf
      (synWb (synWbr (.cv x)
          (synCdif (synCcom (synCid) F) (synCcom (synCcompl (synCid)) F)) (.cv y))
        (synWa (synWbr (.cv x) F (.cv y))
          (.all z (.imp (synWbr (.cv x) F (.cv z)) (.objEq z y))))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold synWb synWbr synCop synCun synCnin synWnan synWa synCcompl synWrex
          synWex synCphi synCdif synCin synCcom synCopab synCid
        simp (config :=
          { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_class_cv]
        apply Nominal.RecanonTransportDev.TRecanonWff.neg
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · apply Nominal.RecanonTransportDev.TRecanonWff.imp
          · exact Nominal.RecanonTransportDev.TRecanonWff.same _
          · apply Nominal.RecanonTransportDev.TRecanonWff.neg
            apply Nominal.RecanonTransportDev.TRecanonWff.imp
            · exact Nominal.RecanonTransportDev.TRecanonWff.same _
            · apply Nominal.RecanonTransportDev.TRecanonWff.neg
              apply Nominal.RecanonTransportDev.TRecanonWff.all
              apply Nominal.RecanonTransportDev.TRecanonWff.imp
              · exact Nominal.RecanonTransportDev.TRecanonWff.same _
              · exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
        · apply Nominal.RecanonTransportDev.TRecanonWff.neg
          apply Nominal.RecanonTransportDev.TRecanonWff.imp
          · apply Nominal.RecanonTransportDev.TRecanonWff.neg
            apply Nominal.RecanonTransportDev.TRecanonWff.imp
            · exact Nominal.RecanonTransportDev.TRecanonWff.same _
            · apply Nominal.RecanonTransportDev.TRecanonWff.neg
              apply Nominal.RecanonTransportDev.TRecanonWff.all
              apply Nominal.RecanonTransportDev.TRecanonWff.imp
              · exact Nominal.RecanonTransportDev.TRecanonWff.same _
              · exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
          · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0001
  have p0002 :=
    @gExbii
      (synWbr (.cv x)
        (synCdif (synCcom (synCid) F) (synCcom (synCcompl (synCid)) F)) (.cv y))
      (synWa (synWbr (.cv x) F (.cv y))
        (.all z (.imp (synWbr (.cv x) F (.cv z)) (.objEq z y))))
      y p0002_e00_recanon
  have p0003 := @gNfv (synWbr (.cv x) F (.cv y)) z dv_cache_0006
  have p0004 := @gEu1 (synWbr (.cv x) F (.cv y)) y z dv_cache_0007 p0003
  have p0005 := @gNfv (synWbr (.cv x) F (.cv z)) y dv_cache_0008
  have p0006 := @gBreq2 (.cv y) (.cv z) (.cv x) F
  have p0007_e01_recanon :
    Nominal.NPrf
      (.imp (.objEq y z) (synWb (synWbr (.cv x) F (.cv y)) (synWbr (.cv x) F (.cv z)))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold synWb synWbr synCop synCun synCnin synWnan synWa synCcompl synWrex
          synWex synCphi
        simp (config :=
          { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_class_cv]
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
        · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0006
  have p0007 :=
    @gSbie (synWbr (.cv x) F (.cv y)) (synWbr (.cv x) F (.cv z)) y z p0005
      p0007_e01_recanon
  have p0008 := @gEqucom y z
  have p0009 :=
    @gImbi12i (synWsb z y (synWbr (.cv x) F (.cv y))) (synWbr (.cv x) F (.cv z))
      (.objEq y z) (.objEq z y) p0007 p0008
  have p0010 :=
    @gAlbii (.imp (synWsb z y (synWbr (.cv x) F (.cv y))) (.objEq y z))
      (.imp (synWbr (.cv x) F (.cv z)) (.objEq z y)) z p0009
  have p0011 :=
    @gAnbi2i (.all z (.imp (synWsb z y (synWbr (.cv x) F (.cv y))) (.objEq y z)))
      (.all z (.imp (synWbr (.cv x) F (.cv z)) (.objEq z y))) (synWbr (.cv x) F (.cv y))
      p0010
  have p0012 :=
    @gExbii
      (synWa (synWbr (.cv x) F (.cv y))
        (.all z (.imp (synWsb z y (synWbr (.cv x) F (.cv y))) (.objEq y z))))
      (synWa (synWbr (.cv x) F (.cv y))
        (.all z (.imp (synWbr (.cv x) F (.cv z)) (.objEq z y))))
      y p0011
  have p0013_e00_recanon :
    Nominal.NPrf
      (synWb (synWeu y (synWbr (.cv x) F (.cv y))) (synWex y
          (synWa (synWbr (.cv x) F (.cv y))
            (.all z (.imp (synWsb z y (synWbr (.cv x) F (.cv y))) (.objEq y z)))))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold synWb synWeu synWex synWbr synCop synCun synCnin synWnan synWa
          synCcompl synWrex synCphi
        simp (config :=
          { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_class_cv]
        apply Nominal.RecanonTransportDev.TRecanonWff.neg
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · apply Nominal.RecanonTransportDev.TRecanonWff.imp
          · exact Nominal.RecanonTransportDev.TRecanonWff.same _
          · apply Nominal.RecanonTransportDev.TRecanonWff.neg
            apply Nominal.RecanonTransportDev.TRecanonWff.all
            apply Nominal.RecanonTransportDev.TRecanonWff.neg
            apply Nominal.RecanonTransportDev.TRecanonWff.neg
            apply Nominal.RecanonTransportDev.TRecanonWff.imp
            · exact Nominal.RecanonTransportDev.TRecanonWff.same _
            · apply Nominal.RecanonTransportDev.TRecanonWff.neg
              apply Nominal.RecanonTransportDev.TRecanonWff.all
              apply Nominal.RecanonTransportDev.TRecanonWff.imp
              · exact Nominal.RecanonTransportDev.TRecanonWff.same _
              · exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
        · apply Nominal.RecanonTransportDev.TRecanonWff.neg
          apply Nominal.RecanonTransportDev.TRecanonWff.imp
          · apply Nominal.RecanonTransportDev.TRecanonWff.neg
            apply Nominal.RecanonTransportDev.TRecanonWff.all
            apply Nominal.RecanonTransportDev.TRecanonWff.neg
            apply Nominal.RecanonTransportDev.TRecanonWff.neg
            apply Nominal.RecanonTransportDev.TRecanonWff.imp
            · exact Nominal.RecanonTransportDev.TRecanonWff.same _
            · apply Nominal.RecanonTransportDev.TRecanonWff.neg
              apply Nominal.RecanonTransportDev.TRecanonWff.all
              apply Nominal.RecanonTransportDev.TRecanonWff.imp
              · exact Nominal.RecanonTransportDev.TRecanonWff.same _
              · exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
          · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0004
  have p0013 :=
    @gBitr2i (synWeu y (synWbr (.cv x) F (.cv y)))
      (synWex y (synWa (synWbr (.cv x) F (.cv y))
          (.all z (.imp (synWsb z y (synWbr (.cv x) F (.cv y))) (.objEq y z)))))
      (synWex y (synWa (synWbr (.cv x) F (.cv y))
          (.all z (.imp (synWbr (.cv x) F (.cv z)) (.objEq z y)))))
      p0013_e00_recanon p0012
  have p0014 :=
    @gN3bitri
      (.classMem (.cv x)
        (synCdm (synCdif (synCcom (synCid) F) (synCcom (synCcompl (synCid)) F))))
      (synWex y (synWbr (.cv x)
          (synCdif (synCcom (synCid) F) (synCcom (synCcompl (synCid)) F)) (.cv y)))
      (synWex y (synWa (synWbr (.cv x) F (.cv y))
          (.all z (.imp (synWbr (.cv x) F (.cv z)) (.objEq z y)))))
      (synWeu y (synWbr (.cv x) F (.cv y))) p0000 p0002 p0013
  have p0015 :=
    @gEqabi (synWeu y (synWbr (.cv x) F (.cv y))) x
      (synCdm (synCdif (synCcom (synCid) F) (synCcom (synCcompl (synCid)) F)))
      dv_cache_0009 p0014
  exact p0015


end NFChoice.DirectNominalPrf.WPPReplay

end

/-! Certificates from `NominalWPPReplayChunk013Compact001Part013`. -/


section

namespace NFChoice.DirectNominalPrf.WPPReplay

open scoped Fol
open NFChoice.Foundation
open NFChoice.SemanticCore
open NFChoice.ReplaySupport
open NFChoice.Compiler.CompactSourceSyntax

/-- Checked nominal proof certificate identified upstream as `g_fvfullfunlem2`. -/
@[expose]
noncomputable def gFvfullfunlem2 (F : Class) :
    Nominal.NPrf
      (synWss (synCdif (synCcom (synCid) F) (synCcom (synCcompl (synCid)) F)) F) :=
  by
  let proofSupport : Finset Var := F.fv
  let x : Var := freshVar proofSupport 0
  let y : Var := freshVar proofSupport 1
  let z : Var := freshVar proofSupport 2
  have fresh_x : x ∉ proofSupport :=
    by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_x_not_F : x ∉ F.fv := by
    intro h
    exact fresh_x (h)
  have fresh_y : y ∉ proofSupport :=
    by
    change freshVar proofSupport 1 ∉ proofSupport
    exact freshVar_not_mem proofSupport 1
  have fresh_y_not_F : y ∉ F.fv := by
    intro h
    exact fresh_y (h)
  have fresh_z : z ∉ proofSupport :=
    by
    change freshVar proofSupport 2 ∉ proofSupport
    exact freshVar_not_mem proofSupport 2
  have fresh_z_not_F : z ∉ F.fv := by
    intro h
    exact fresh_z (h)
  have fresh_x_ne_y : x ≠ y :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have fresh_x_ne_z : x ≠ z :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 2
    exact freshVar_injective proofSupport (i := 0) (j := 2) (by decide)
  have fresh_z_ne_x : z ≠ x := Ne.symm fresh_x_ne_z
  have fresh_y_ne_z : y ≠ z :=
    by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 2
    exact freshVar_injective proofSupport (i := 1) (j := 2) (by decide)
  have fresh_z_ne_y : z ≠ y := Ne.symm fresh_y_ne_z
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
  have dv_cache_0003 : z ∉ (F).fv :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact
      (by
        have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_z_not_F, not_false_eq_true])
  have dv_cache_0004 :
    x ∉ ((synCdif (synCcom (synCid) F) (synCcom (synCcompl (synCid)) F))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdif,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccom,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cid,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccompl, Finset.mem_union,
          fresh_x_not_F, compact_fv_not_mem_empty, or_false, not_false_eq_true])
  have dv_cache_0005 :
    y ∉ ((synCdif (synCcom (synCid) F) (synCcom (synCcompl (synCid)) F))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdif,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccom,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cid,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccompl, Finset.mem_union,
          fresh_y_not_F, compact_fv_not_mem_empty, or_false, not_false_eq_true])
  have dv_cache_0006 : x ∉ (F).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_x_not_F, not_false_eq_true])
  have dv_cache_0007 : y ∉ (F).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_y_not_F, not_false_eq_true])
  have dv_cache_0008 : x ≠ y :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007
    exact (show x ≠ y from (by exact fresh_x_ne_y))
  have p0000 :=
    @gSimpl (synWbr (.cv x) F (.cv y))
      (.all z (.imp (synWbr (.cv x) F (.cv z)) (.objEq z y)))
  have p0001 :=
    @gFnfullfunlem1 z (.cv x) (.cv y) F dv_cache_0001 dv_cache_0002 dv_cache_0003
  have p0002 :=
    (Nominal.biimpRefl (synWbr (.cv x)
        (synCdif (synCcom (synCid) F) (synCcom (synCcompl (synCid)) F)) (.cv y)))
  have p0003_e00_recanon :
    Nominal.NPrf
      (synWb (synWbr (.cv x)
          (synCdif (synCcom (synCid) F) (synCcom (synCcompl (synCid)) F)) (.cv y))
        (synWa (synWbr (.cv x) F (.cv y))
          (.all z (.imp (synWbr (.cv x) F (.cv z)) (.objEq z y))))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold synWb synWbr synCop synCun synCnin synWnan synWa synCcompl synWrex
          synWex synCphi synCdif synCin synCcom synCopab synCid
        simp (config :=
          { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_class_cv]
        apply Nominal.RecanonTransportDev.TRecanonWff.neg
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · apply Nominal.RecanonTransportDev.TRecanonWff.imp
          · exact Nominal.RecanonTransportDev.TRecanonWff.same _
          · apply Nominal.RecanonTransportDev.TRecanonWff.neg
            apply Nominal.RecanonTransportDev.TRecanonWff.imp
            · exact Nominal.RecanonTransportDev.TRecanonWff.same _
            · apply Nominal.RecanonTransportDev.TRecanonWff.neg
              apply Nominal.RecanonTransportDev.TRecanonWff.all
              apply Nominal.RecanonTransportDev.TRecanonWff.imp
              · exact Nominal.RecanonTransportDev.TRecanonWff.same _
              · exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
        · apply Nominal.RecanonTransportDev.TRecanonWff.neg
          apply Nominal.RecanonTransportDev.TRecanonWff.imp
          · apply Nominal.RecanonTransportDev.TRecanonWff.neg
            apply Nominal.RecanonTransportDev.TRecanonWff.imp
            · exact Nominal.RecanonTransportDev.TRecanonWff.same _
            · apply Nominal.RecanonTransportDev.TRecanonWff.neg
              apply Nominal.RecanonTransportDev.TRecanonWff.all
              apply Nominal.RecanonTransportDev.TRecanonWff.imp
              · exact Nominal.RecanonTransportDev.TRecanonWff.same _
              · exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
          · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0001
  have p0003 :=
    @gBitr3i
      (synWa (synWbr (.cv x) F (.cv y))
        (.all z (.imp (synWbr (.cv x) F (.cv z)) (.objEq z y))))
      (synWbr (.cv x)
        (synCdif (synCcom (synCid) F) (synCcom (synCcompl (synCid)) F)) (.cv y))
      (.classMem (synCop (.cv x) (.cv y))
        (synCdif (synCcom (synCid) F) (synCcom (synCcompl (synCid)) F)))
      p0003_e00_recanon p0002
  have p0004 := (Nominal.biimpRefl (synWbr (.cv x) F (.cv y)))
  have p0005 :=
    @gN3imtr3i
      (synWa (synWbr (.cv x) F (.cv y))
        (.all z (.imp (synWbr (.cv x) F (.cv z)) (.objEq z y))))
      (synWbr (.cv x) F (.cv y))
      (.classMem (synCop (.cv x) (.cv y))
        (synCdif (synCcom (synCid) F) (synCcom (synCcompl (synCid)) F)))
      (.classMem (synCop (.cv x) (.cv y)) F) p0000 p0003 p0004
  have p0006 :=
    @gGen2
      (.imp (.classMem (synCop (.cv x) (.cv y))
          (synCdif (synCcom (synCid) F) (synCcom (synCcompl (synCid)) F)))
        (.classMem (synCop (.cv x) (.cv y)) F))
      x y p0005
  have p0007 :=
    @gSsrel x y (synCdif (synCcom (synCid) F) (synCcom (synCcompl (synCid)) F)) F
      dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008
  have p0008 :=
    @gMpbir
      (synWss (synCdif (synCcom (synCid) F) (synCcom (synCcompl (synCid)) F)) F)
      (.all x (.all y (.imp (.classMem (synCop (.cv x) (.cv y))
              (synCdif (synCcom (synCid) F) (synCcom (synCcompl (synCid)) F)))
            (.classMem (synCop (.cv x) (.cv y)) F))))
      p0006 p0007
  exact p0008

/-- Checked nominal proof certificate identified upstream as `g_fvfullfunlem3`. -/
@[expose]
noncomputable def gFvfullfunlem3 (A : Class) (F : Class) :
    Nominal.NPrf
      (.imp (.classMem A
          (synCdm (synCdif (synCcom (synCid) F) (synCcom (synCcompl (synCid)) F))))
        (.classEq (synCfv (synCdif (synCcom (synCid) F) (synCcom (synCcompl (synCid)) F))
            A) (synCfv F A))) :=
  by
  let proofSupport : Finset Var := A.fv ∪ F.fv
  let x : Var := freshVar proofSupport 0
  let y : Var := freshVar proofSupport 1
  let z : Var := freshVar proofSupport 2
  have fresh_x : x ∉ proofSupport :=
    by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_x_not_F : x ∉ F.fv := by
    intro h
    exact fresh_x (Finset.mem_union_right _ (h))
  have fresh_y : y ∉ proofSupport :=
    by
    change freshVar proofSupport 1 ∉ proofSupport
    exact freshVar_not_mem proofSupport 1
  have fresh_y_not_F : y ∉ F.fv := by
    intro h
    exact fresh_y (Finset.mem_union_right _ (h))
  have fresh_z : z ∉ proofSupport :=
    by
    change freshVar proofSupport 2 ∉ proofSupport
    exact freshVar_not_mem proofSupport 2
  have fresh_z_not_F : z ∉ F.fv := by
    intro h
    exact fresh_z (Finset.mem_union_right _ (h))
  have fresh_x_ne_y : x ≠ y :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have fresh_y_ne_x : y ≠ x := Ne.symm fresh_x_ne_y
  have fresh_x_ne_z : x ≠ z :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 2
    exact freshVar_injective proofSupport (i := 0) (j := 2) (by decide)
  have fresh_y_ne_z : y ≠ z :=
    by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 2
    exact freshVar_injective proofSupport (i := 1) (j := 2) (by decide)
  have dv_cache_0001 :
    x ∉
      ((synCres F (synCdm
            (synCdif (synCcom (synCid) F) (synCcom (synCcompl (synCid)) F))))).fv :=
    by
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cres,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdm,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdif,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccom,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cid,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccompl, Finset.mem_union,
          fresh_x_not_F, compact_fv_not_mem_empty, or_false, not_false_eq_true])
  have dv_cache_0002 :
    y ∉
      ((synCres F (synCdm
            (synCdif (synCcom (synCid) F) (synCcom (synCcompl (synCid)) F))))).fv :=
    by
    clear dv_cache_0001
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cres,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdm,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdif,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccom,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cid,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccompl, Finset.mem_union,
          fresh_y_not_F, compact_fv_not_mem_empty, or_false, not_false_eq_true])
  have dv_cache_0003 :
    z ∉
      ((synCres F (synCdm
            (synCdif (synCcom (synCid) F) (synCcom (synCcompl (synCid)) F))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact
      (by
        have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cres,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdm,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdif,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccom,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cid,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccompl, Finset.mem_union,
          fresh_z_not_F, compact_fv_not_mem_empty, or_false, not_false_eq_true])
  have dv_cache_0004 : x ≠ y :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact (show x ≠ y from (by exact fresh_x_ne_y))
  have dv_cache_0005 : x ≠ z :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact (show x ≠ z from (by exact fresh_x_ne_z))
  have dv_cache_0006 : y ≠ z :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact (show y ≠ z from (by exact fresh_y_ne_z))
  have dv_cache_0007 : x ∉ (F).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_x_not_F, not_false_eq_true])
  have dv_cache_0008 : z ∉ (F).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007
    exact
      (by
        have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_z_not_F, not_false_eq_true])
  have dv_cache_0009 : y ∉ (F).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_y_not_F, not_false_eq_true])
  have dv_cache_0010 : y ∉ ((Class.cv x)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_y_ne_x, not_false_eq_true])
  have p0000 :=
    @gDffun2 x y z
      (synCres F
        (synCdm (synCdif (synCcom (synCid) F) (synCcom (synCcompl (synCid)) F))))
      dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006
  have p0001 :=
    @gBrres (.cv x) (.cv y) F
      (synCdm (synCdif (synCcom (synCid) F) (synCcom (synCcompl (synCid)) F)))
  have p0002 := @gFvfullfunlem1 x z F dv_cache_0007 dv_cache_0008 dv_cache_0005
  have p0003 :=
    @gEqabri (synWeu z (synWbr (.cv x) F (.cv z))) x
      (synCdm (synCdif (synCcom (synCid) F) (synCcom (synCcompl (synCid)) F)))
      p0002
  have p0004 :=
    @gAnbi2i
      (.classMem (.cv x)
        (synCdm (synCdif (synCcom (synCid) F) (synCcom (synCcompl (synCid)) F))))
      (synWeu z (synWbr (.cv x) F (.cv z))) (synWbr (.cv x) F (.cv y)) p0003
  have p0005 :=
    @gBitri
      (synWbr (.cv x) (synCres F
          (synCdm (synCdif (synCcom (synCid) F) (synCcom (synCcompl (synCid)) F))))
        (.cv y))
      (synWa (synWbr (.cv x) F (.cv y)) (.classMem (.cv x) (synCdm
            (synCdif (synCcom (synCid) F) (synCcom (synCcompl (synCid)) F)))))
      (synWa (synWbr (.cv x) F (.cv y)) (synWeu z (synWbr (.cv x) F (.cv z)))) p0001
      p0004
  have p0006 :=
    @gBrres (.cv x) (.cv z) F
      (synCdm (synCdif (synCcom (synCid) F) (synCcom (synCcompl (synCid)) F)))
  have p0007 := @gFvfullfunlem1 x y F dv_cache_0007 dv_cache_0009 dv_cache_0004
  have p0008 :=
    @gEqabri (synWeu y (synWbr (.cv x) F (.cv y))) x
      (synCdm (synCdif (synCcom (synCid) F) (synCcom (synCcompl (synCid)) F)))
      p0007
  have p0009 :=
    @gAnbi2i
      (.classMem (.cv x)
        (synCdm (synCdif (synCcom (synCid) F) (synCcom (synCcompl (synCid)) F))))
      (synWeu y (synWbr (.cv x) F (.cv y))) (synWbr (.cv x) F (.cv z)) p0008
  have p0010 :=
    @gBitri
      (synWbr (.cv x) (synCres F
          (synCdm (synCdif (synCcom (synCid) F) (synCcom (synCcompl (synCid)) F))))
        (.cv z))
      (synWa (synWbr (.cv x) F (.cv z)) (.classMem (.cv x) (synCdm
            (synCdif (synCcom (synCid) F) (synCcom (synCcompl (synCid)) F)))))
      (synWa (synWbr (.cv x) F (.cv z)) (synWeu y (synWbr (.cv x) F (.cv y)))) p0006
      p0009
  have p0011 := @g_tz6_12_1 y (.cv x) (.cv y) F dv_cache_0010 dv_cache_0009
  have p0012 :=
    @gAdantrl (synWbr (.cv x) F (.cv y)) (synWeu y (synWbr (.cv x) F (.cv y)))
      (.classEq (synCfv F (.cv x)) (.cv y)) (synWbr (.cv x) F (.cv z)) p0011
  have p0013 := @g_tz6_12_1 y (.cv x) (.cv z) F dv_cache_0010 dv_cache_0009
  have p0014 :=
    @gAdantl (synWa (synWbr (.cv x) F (.cv z)) (synWeu y (synWbr (.cv x) F (.cv y))))
      (.classEq (synCfv F (.cv x)) (.cv z)) (synWbr (.cv x) F (.cv y)) p0013
  have p0015 :=
    @gEqtr3d
      (synWa (synWbr (.cv x) F (.cv y))
        (synWa (synWbr (.cv x) F (.cv z)) (synWeu y (synWbr (.cv x) F (.cv y)))))
      (synCfv F (.cv x)) (.cv y) (.cv z) p0012 p0014
  have p0016_e00_recanon :
    Nominal.NPrf
      (.imp (synWa (synWbr (.cv x) F (.cv y))
          (synWa (synWbr (.cv x) F (.cv z)) (synWeu y (synWbr (.cv x) F (.cv y)))))
        (.objEq y z)) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold synWa synWbr synCop synCun synCnin synWnan synCcompl synWrex
          synWex synCphi
        simp (config :=
          { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_class_cv]
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · exact Nominal.RecanonTransportDev.TRecanonWff.same _
        · exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _)
      p0015
  have p0016 :=
    @gAdantlr (synWbr (.cv x) F (.cv y))
      (synWa (synWbr (.cv x) F (.cv z)) (synWeu y (synWbr (.cv x) F (.cv y))))
      (.objEq y z) (synWeu z (synWbr (.cv x) F (.cv z))) p0016_e00_recanon
  have p0017 :=
    @gSyl2anb
      (synWbr (.cv x) (synCres F
          (synCdm (synCdif (synCcom (synCid) F) (synCcom (synCcompl (synCid)) F))))
        (.cv y))
      (synWa (synWbr (.cv x) F (.cv y)) (synWeu z (synWbr (.cv x) F (.cv z))))
      (synWa (synWbr (.cv x) F (.cv z)) (synWeu y (synWbr (.cv x) F (.cv y))))
      (.objEq y z)
      (synWbr (.cv x) (synCres F
          (synCdm (synCdif (synCcom (synCid) F) (synCcom (synCcompl (synCid)) F))))
        (.cv z))
      p0005 p0010 p0016
  have p0018 :=
    @gGen2
      (.imp (synWa (synWbr (.cv x) (synCres F (synCdm
                (synCdif (synCcom (synCid) F) (synCcom (synCcompl (synCid)) F)))) (.cv y))
          (synWbr (.cv x) (synCres F (synCdm
                (synCdif (synCcom (synCid) F) (synCcom (synCcompl (synCid)) F))))
            (.cv z))) (.objEq y z))
      y z p0017
  have p0019 :=
    @gMpgbir
      (synWfun (synCres F (synCdm
            (synCdif (synCcom (synCid) F) (synCcom (synCcompl (synCid)) F)))))
      (.all y (.all z (.imp (synWa (synWbr (.cv x) (synCres F (synCdm
                    (synCdif (synCcom (synCid) F) (synCcom (synCcompl (synCid)) F))))
                (.cv y)) (synWbr (.cv x) (synCres F (synCdm (synCdif (synCcom (synCid) F)
                      (synCcom (synCcompl (synCid)) F)))) (.cv z))) (.objEq y z))))
      x p0000 p0018
  have p0020 := @gFvfullfunlem2 F
  have p0021 :=
    @gSsdmrn (synCdif (synCcom (synCid) F) (synCcom (synCcompl (synCid)) F))
  have p0022 :=
    @gSsv (synCrn (synCdif (synCcom (synCid) F) (synCcom (synCcompl (synCid)) F)))
  have p0023 :=
    @gXpss2
      (synCrn (synCdif (synCcom (synCid) F) (synCcom (synCcompl (synCid)) F)))
      (synCvv)
      (synCdm (synCdif (synCcom (synCid) F) (synCcom (synCcompl (synCid)) F)))
  have p0024 := Nominal.mp p0022 p0023
  have p0025 :=
    @gSstri (synCdif (synCcom (synCid) F) (synCcom (synCcompl (synCid)) F))
      (synCxp (synCdm (synCdif (synCcom (synCid) F) (synCcom (synCcompl (synCid)) F)))
        (synCrn (synCdif (synCcom (synCid) F) (synCcom (synCcompl (synCid)) F))))
      (synCxp (synCdm (synCdif (synCcom (synCid) F) (synCcom (synCcompl (synCid)) F)))
        (synCvv))
      p0021 p0024
  have p0026 :=
    @gSsini (synCdif (synCcom (synCid) F) (synCcom (synCcompl (synCid)) F)) F
      (synCxp (synCdm (synCdif (synCcom (synCid) F) (synCcom (synCcompl (synCid)) F)))
        (synCvv))
      p0020 p0025
  have p0027 :=
    (Nominal.classEqRefl (synCres F
        (synCdm (synCdif (synCcom (synCid) F) (synCcom (synCcompl (synCid)) F)))))
  have p0028 :=
    @gSseqtr4i (synCdif (synCcom (synCid) F) (synCcom (synCcompl (synCid)) F))
      (synCin F (synCxp
          (synCdm (synCdif (synCcom (synCid) F) (synCcom (synCcompl (synCid)) F)))
          (synCvv)))
      (synCres F
        (synCdm (synCdif (synCcom (synCid) F) (synCcom (synCcompl (synCid)) F))))
      p0026 p0027
  have p0029 :=
    @gFunssfv A
      (synCres F
        (synCdm (synCdif (synCcom (synCid) F) (synCcom (synCcompl (synCid)) F))))
      (synCdif (synCcom (synCid) F) (synCcom (synCcompl (synCid)) F))
  have p0030 :=
    @gMp3an12
      (synWfun (synCres F (synCdm
            (synCdif (synCcom (synCid) F) (synCcom (synCcompl (synCid)) F)))))
      (synWss (synCdif (synCcom (synCid) F) (synCcom (synCcompl (synCid)) F)) (synCres F
          (synCdm (synCdif (synCcom (synCid) F) (synCcom (synCcompl (synCid)) F)))))
      (.classMem A
        (synCdm (synCdif (synCcom (synCid) F) (synCcom (synCcompl (synCid)) F))))
      (.classEq (synCfv (synCres F (synCdm
              (synCdif (synCcom (synCid) F) (synCcom (synCcompl (synCid)) F)))) A)
        (synCfv (synCdif (synCcom (synCid) F) (synCcom (synCcompl (synCid)) F)) A))
      p0019 p0028 p0029
  have p0031 :=
    @gFvres A
      (synCdm (synCdif (synCcom (synCid) F) (synCcom (synCcompl (synCid)) F))) F
  have p0032 :=
    @gEqtr3d
      (.classMem A
        (synCdm (synCdif (synCcom (synCid) F) (synCcom (synCcompl (synCid)) F))))
      (synCfv (synCres F
          (synCdm (synCdif (synCcom (synCid) F) (synCcom (synCcompl (synCid)) F)))) A)
      (synCfv (synCdif (synCcom (synCid) F) (synCcom (synCcompl (synCid)) F)) A)
      (synCfv F A) p0030 p0031
  exact p0032

/-- Checked nominal proof certificate identified upstream as `g_fvfullfun`. -/
@[expose]
noncomputable def gFvfullfun (A : Class) (F : Class) :
    Nominal.NPrf (.classEq (synCfv (synCfullfun F) A) (synCfv F A)) :=
  by
  let proofSupport : Finset Var := A.fv ∪ F.fv
  let x : Var := freshVar proofSupport 0
  let y : Var := freshVar proofSupport 1
  have fresh_x : x ∉ proofSupport :=
    by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_x_not_A : x ∉ A.fv := by
    intro h
    exact fresh_x (Finset.mem_union_left _ (h))
  have fresh_x_not_F : x ∉ F.fv := by
    intro h
    exact fresh_x (Finset.mem_union_right _ (h))
  have fresh_y : y ∉ proofSupport :=
    by
    change freshVar proofSupport 1 ∉ proofSupport
    exact freshVar_not_mem proofSupport 1
  have fresh_y_not_F : y ∉ F.fv := by
    intro h
    exact fresh_y (Finset.mem_union_right _ (h))
  have fresh_x_ne_y : x ≠ y :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have fresh_y_ne_x : y ≠ x := Ne.symm fresh_x_ne_y
  have dv_cache_0001 : x ∉ (F).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_x_not_F, not_false_eq_true])
  have dv_cache_0002 : y ∉ (F).fv :=
    by
    clear dv_cache_0001
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_y_not_F, not_false_eq_true])
  have dv_cache_0003 : x ≠ y :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact (show x ≠ y from (by exact fresh_x_ne_y))
  have dv_cache_0004 : y ∉ ((Class.cv x)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_y_ne_x, not_false_eq_true])
  have dv_cache_0005 : x ∉ (A).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_x_not_A, not_false_eq_true])
  have dv_cache_0006 :
    x ∉ ((Wff.classEq (synCfv (synCfullfun F) A) (synCfv F A))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfullfun, Finset.mem_union,
          fresh_x_not_A, fresh_x_not_F, or_false, not_false_eq_true])
  have p0000 := @gFveq2 (.cv x) A (synCfullfun F)
  have p0001 := @gFveq2 (.cv x) A F
  have p0002 :=
    @gEqeq12d (.classEq (.cv x) A) (synCfv (synCfullfun F) (.cv x))
      (synCfv (synCfullfun F) A) (synCfv F (.cv x)) (synCfv F A) p0000 p0001
  have p0003 := (Nominal.classEqRefl (synCfullfun F))
  have p0004 :=
    @gFveq1i (.cv x) (synCfullfun F)
      (synCun (synCdif (synCcom (synCid) F) (synCcom (synCcompl (synCid)) F)) (synCxp
          (synCcompl (synCdm
              (synCdif (synCcom (synCid) F) (synCcom (synCcompl (synCid)) F))))
          (synCsn (synC0))))
      p0003
  have p0005 :=
    @gIncompl
      (synCdm (synCdif (synCcom (synCid) F) (synCcom (synCcompl (synCid)) F)))
  have p0006 := @gFnfullfunlem2 F
  have p0007 :=
    @gFunfn (synCdif (synCcom (synCid) F) (synCcom (synCcompl (synCid)) F))
  have p0008 :=
    @gMpbi
      (synWfun (synCdif (synCcom (synCid) F) (synCcom (synCcompl (synCid)) F)))
      (synWfn (synCdif (synCcom (synCid) F) (synCcom (synCcompl (synCid)) F))
        (synCdm (synCdif (synCcom (synCid) F) (synCcom (synCcompl (synCid)) F))))
      p0006 p0007
  have p0009 := @gN0ex
  have p0010 :=
    @gFnconstg
      (synCcompl
        (synCdm (synCdif (synCcom (synCid) F) (synCcom (synCcompl (synCid)) F))))
      (synC0) (synCvv)
  have p0011 := Nominal.mp p0009 p0010
  have p0012 :=
    @gFvun1
      (synCdm (synCdif (synCcom (synCid) F) (synCcom (synCcompl (synCid)) F)))
      (synCcompl
        (synCdm (synCdif (synCcom (synCid) F) (synCcom (synCcompl (synCid)) F))))
      (synCdif (synCcom (synCid) F) (synCcom (synCcompl (synCid)) F))
      (synCxp (synCcompl
          (synCdm (synCdif (synCcom (synCid) F) (synCcom (synCcompl (synCid)) F))))
        (synCsn (synC0)))
      (.cv x)
  have p0013 :=
    @gMp3an12
      (synWfn (synCdif (synCcom (synCid) F) (synCcom (synCcompl (synCid)) F))
        (synCdm (synCdif (synCcom (synCid) F) (synCcom (synCcompl (synCid)) F))))
      (synWfn (synCxp (synCcompl (synCdm
              (synCdif (synCcom (synCid) F) (synCcom (synCcompl (synCid)) F))))
          (synCsn (synC0))) (synCcompl (synCdm
            (synCdif (synCcom (synCid) F) (synCcom (synCcompl (synCid)) F)))))
      (synWa (.classEq (synCin (synCdm
              (synCdif (synCcom (synCid) F) (synCcom (synCcompl (synCid)) F))) (synCcompl
              (synCdm (synCdif (synCcom (synCid) F) (synCcom (synCcompl (synCid)) F)))))
          (synC0)) (.classMem (.cv x) (synCdm
            (synCdif (synCcom (synCid) F) (synCcom (synCcompl (synCid)) F)))))
      (.classEq (synCfv
          (synCun (synCdif (synCcom (synCid) F) (synCcom (synCcompl (synCid)) F))
            (synCxp (synCcompl (synCdm
                  (synCdif (synCcom (synCid) F) (synCcom (synCcompl (synCid)) F))))
              (synCsn (synC0)))) (.cv x))
        (synCfv (synCdif (synCcom (synCid) F) (synCcom (synCcompl (synCid)) F)) (.cv x)))
      p0008 p0011 p0012
  have p0014 :=
    @gMpan
      (.classEq (synCin
          (synCdm (synCdif (synCcom (synCid) F) (synCcom (synCcompl (synCid)) F)))
          (synCcompl (synCdm
              (synCdif (synCcom (synCid) F) (synCcom (synCcompl (synCid)) F))))) (synC0))
      (.classMem (.cv x)
        (synCdm (synCdif (synCcom (synCid) F) (synCcom (synCcompl (synCid)) F))))
      (.classEq (synCfv
          (synCun (synCdif (synCcom (synCid) F) (synCcom (synCcompl (synCid)) F))
            (synCxp (synCcompl (synCdm
                  (synCdif (synCcom (synCid) F) (synCcom (synCcompl (synCid)) F))))
              (synCsn (synC0)))) (.cv x))
        (synCfv (synCdif (synCcom (synCid) F) (synCcom (synCcompl (synCid)) F)) (.cv x)))
      p0005 p0013
  have p0015 := @gFvfullfunlem3 (.cv x) F
  have p0016 :=
    @gEqtrd
      (.classMem (.cv x)
        (synCdm (synCdif (synCcom (synCid) F) (synCcom (synCcompl (synCid)) F))))
      (synCfv (synCun (synCdif (synCcom (synCid) F) (synCcom (synCcompl (synCid)) F))
          (synCxp (synCcompl (synCdm
                (synCdif (synCcom (synCid) F) (synCcom (synCcompl (synCid)) F))))
            (synCsn (synC0)))) (.cv x))
      (synCfv (synCdif (synCcom (synCid) F) (synCcom (synCcompl (synCid)) F)) (.cv x))
      (synCfv F (.cv x)) p0014 p0015
  have p0017 := @gVex x
  have p0018 :=
    @gElcompl (.cv x)
      (synCdm (synCdif (synCcom (synCid) F) (synCcom (synCcompl (synCid)) F)))
      p0017
  have p0019 :=
    @gFvun2
      (synCdm (synCdif (synCcom (synCid) F) (synCcom (synCcompl (synCid)) F)))
      (synCcompl
        (synCdm (synCdif (synCcom (synCid) F) (synCcom (synCcompl (synCid)) F))))
      (synCdif (synCcom (synCid) F) (synCcom (synCcompl (synCid)) F))
      (synCxp (synCcompl
          (synCdm (synCdif (synCcom (synCid) F) (synCcom (synCcompl (synCid)) F))))
        (synCsn (synC0)))
      (.cv x)
  have p0020 :=
    @gMp3an12
      (synWfn (synCdif (synCcom (synCid) F) (synCcom (synCcompl (synCid)) F))
        (synCdm (synCdif (synCcom (synCid) F) (synCcom (synCcompl (synCid)) F))))
      (synWfn (synCxp (synCcompl (synCdm
              (synCdif (synCcom (synCid) F) (synCcom (synCcompl (synCid)) F))))
          (synCsn (synC0))) (synCcompl (synCdm
            (synCdif (synCcom (synCid) F) (synCcom (synCcompl (synCid)) F)))))
      (synWa (.classEq (synCin (synCdm
              (synCdif (synCcom (synCid) F) (synCcom (synCcompl (synCid)) F))) (synCcompl
              (synCdm (synCdif (synCcom (synCid) F) (synCcom (synCcompl (synCid)) F)))))
          (synC0)) (.classMem (.cv x) (synCcompl (synCdm
              (synCdif (synCcom (synCid) F) (synCcom (synCcompl (synCid)) F))))))
      (.classEq (synCfv
          (synCun (synCdif (synCcom (synCid) F) (synCcom (synCcompl (synCid)) F))
            (synCxp (synCcompl (synCdm
                  (synCdif (synCcom (synCid) F) (synCcom (synCcompl (synCid)) F))))
              (synCsn (synC0)))) (.cv x)) (synCfv (synCxp (synCcompl (synCdm
                (synCdif (synCcom (synCid) F) (synCcom (synCcompl (synCid)) F))))
            (synCsn (synC0))) (.cv x)))
      p0008 p0011 p0019
  have p0021 :=
    @gMpan
      (.classEq (synCin
          (synCdm (synCdif (synCcom (synCid) F) (synCcom (synCcompl (synCid)) F)))
          (synCcompl (synCdm
              (synCdif (synCcom (synCid) F) (synCcom (synCcompl (synCid)) F))))) (synC0))
      (.classMem (.cv x) (synCcompl (synCdm
            (synCdif (synCcom (synCid) F) (synCcom (synCcompl (synCid)) F)))))
      (.classEq (synCfv
          (synCun (synCdif (synCcom (synCid) F) (synCcom (synCcompl (synCid)) F))
            (synCxp (synCcompl (synCdm
                  (synCdif (synCcom (synCid) F) (synCcom (synCcompl (synCid)) F))))
              (synCsn (synC0)))) (.cv x)) (synCfv (synCxp (synCcompl (synCdm
                (synCdif (synCcom (synCid) F) (synCcom (synCcompl (synCid)) F))))
            (synCsn (synC0))) (.cv x)))
      p0005 p0020
  have p0022 :=
    @gSylbir
      (.neg (.classMem (.cv x) (synCdm
            (synCdif (synCcom (synCid) F) (synCcom (synCcompl (synCid)) F)))))
      (.classMem (.cv x) (synCcompl (synCdm
            (synCdif (synCcom (synCid) F) (synCcom (synCcompl (synCid)) F)))))
      (.classEq (synCfv
          (synCun (synCdif (synCcom (synCid) F) (synCcom (synCcompl (synCid)) F))
            (synCxp (synCcompl (synCdm
                  (synCdif (synCcom (synCid) F) (synCcom (synCcompl (synCid)) F))))
              (synCsn (synC0)))) (.cv x)) (synCfv (synCxp (synCcompl (synCdm
                (synCdif (synCcom (synCid) F) (synCcom (synCcompl (synCid)) F))))
            (synCsn (synC0))) (.cv x)))
      p0018 p0021
  have p0023 := @gFvfullfunlem1 x y F dv_cache_0001 dv_cache_0002 dv_cache_0003
  have p0024 :=
    @gEqabri (synWeu y (synWbr (.cv x) F (.cv y))) x
      (synCdm (synCdif (synCcom (synCid) F) (synCcom (synCcompl (synCid)) F)))
      p0023
  have p0025 := @g_tz6_12_2 y (.cv x) F dv_cache_0004 dv_cache_0002
  have p0026 :=
    @gSylnbi
      (.classMem (.cv x)
        (synCdm (synCdif (synCcom (synCid) F) (synCcom (synCcompl (synCid)) F))))
      (synWeu y (synWbr (.cv x) F (.cv y))) (.classEq (synCfv F (.cv x)) (synC0))
      p0024 p0025
  have p0028 :=
    @gFvconst2
      (synCcompl
        (synCdm (synCdif (synCcom (synCid) F) (synCcom (synCcompl (synCid)) F))))
      (synC0) (.cv x) p0009
  have p0029 :=
    @gSylbir
      (.neg (.classMem (.cv x) (synCdm
            (synCdif (synCcom (synCid) F) (synCcom (synCcompl (synCid)) F)))))
      (.classMem (.cv x) (synCcompl (synCdm
            (synCdif (synCcom (synCid) F) (synCcom (synCcompl (synCid)) F)))))
      (.classEq (synCfv (synCxp (synCcompl (synCdm
                (synCdif (synCcom (synCid) F) (synCcom (synCcompl (synCid)) F))))
            (synCsn (synC0))) (.cv x)) (synC0))
      p0018 p0028
  have p0030 :=
    @gEqtr4d
      (.neg (.classMem (.cv x) (synCdm
            (synCdif (synCcom (synCid) F) (synCcom (synCcompl (synCid)) F)))))
      (synCfv F (.cv x)) (synC0)
      (synCfv (synCxp (synCcompl (synCdm
              (synCdif (synCcom (synCid) F) (synCcom (synCcompl (synCid)) F))))
          (synCsn (synC0))) (.cv x))
      p0026 p0029
  have p0031 :=
    @gEqtr4d
      (.neg (.classMem (.cv x) (synCdm
            (synCdif (synCcom (synCid) F) (synCcom (synCcompl (synCid)) F)))))
      (synCfv (synCun (synCdif (synCcom (synCid) F) (synCcom (synCcompl (synCid)) F))
          (synCxp (synCcompl (synCdm
                (synCdif (synCcom (synCid) F) (synCcom (synCcompl (synCid)) F))))
            (synCsn (synC0)))) (.cv x))
      (synCfv (synCxp (synCcompl (synCdm
              (synCdif (synCcom (synCid) F) (synCcom (synCcompl (synCid)) F))))
          (synCsn (synC0))) (.cv x))
      (synCfv F (.cv x)) p0022 p0030
  have p0032 :=
    @gPm261i
      (.classMem (.cv x)
        (synCdm (synCdif (synCcom (synCid) F) (synCcom (synCcompl (synCid)) F))))
      (.classEq (synCfv
          (synCun (synCdif (synCcom (synCid) F) (synCcom (synCcompl (synCid)) F))
            (synCxp (synCcompl (synCdm
                  (synCdif (synCcom (synCid) F) (synCcom (synCcompl (synCid)) F))))
              (synCsn (synC0)))) (.cv x)) (synCfv F (.cv x)))
      p0016 p0031
  have p0033 :=
    @gEqtri (synCfv (synCfullfun F) (.cv x))
      (synCfv (synCun (synCdif (synCcom (synCid) F) (synCcom (synCcompl (synCid)) F))
          (synCxp (synCcompl (synCdm
                (synCdif (synCcom (synCid) F) (synCcom (synCcompl (synCid)) F))))
            (synCsn (synC0)))) (.cv x))
      (synCfv F (.cv x)) p0004 p0032
  have p0034 :=
    @gVtoclg (.classEq (synCfv (synCfullfun F) (.cv x)) (synCfv F (.cv x)))
      (.classEq (synCfv (synCfullfun F) A) (synCfv F A)) x A (synCvv) dv_cache_0005
      dv_cache_0006 p0002 p0033
  have p0035 := @gFvprc A (synCfullfun F)
  have p0036 := @gFvprc A F
  have p0037 :=
    @gEqtr4d (.neg (.classMem A (synCvv))) (synCfv (synCfullfun F) A) (synC0)
      (synCfv F A) p0035 p0036
  have p0038 :=
    @gPm261i (.classMem A (synCvv))
      (.classEq (synCfv (synCfullfun F) A) (synCfv F A)) p0034 p0037
  exact p0038

/-- Checked nominal proof certificate identified upstream as `g_fvdomfn`. -/
@[expose]
noncomputable def gFvdomfn (A : Class) (V : Class) :
    Nominal.NPrf (.imp (.classMem A V) (.classEq (synCfv (synCdomfn) A) (synCdm A))) :=
  by
  let proofSupport : Finset Var := A.fv ∪ V.fv
  let x : Var := freshVar proofSupport 0
  have fresh_x : x ∉ proofSupport :=
    by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_x_not_A : x ∉ A.fv := by
    intro h
    exact fresh_x (Finset.mem_union_left _ (h))
  have dv_cache_0001 : x ∉ (A).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_x_not_A, not_false_eq_true])
  have dv_cache_0002 : x ∉ ((synCdm A)).fv :=
    by
    clear dv_cache_0001
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdm, fresh_x_not_A,
          not_false_eq_true])
  have dv_cache_0003 : x ∉ ((synCvv)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv,
          compact_fv_not_mem_empty, not_false_eq_true])
  have p0000 := @gElex A V
  have p0001 := @gDmexg A (synCvv)
  have p0002 := @gDmeq (.cv x) A
  have p0003 := NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominalDfDomfn x
  have p0004 :=
    @gFvmptg x A (synCdm (.cv x)) (synCdm A) (synCvv) (synCvv) (synCdomfn)
      dv_cache_0001 dv_cache_0002 dv_cache_0003 p0002 p0003
  have p0005 :=
    @gMpdan (.classMem A (synCvv)) (.classMem (synCdm A) (synCvv))
      (.classEq (synCfv (synCdomfn) A) (synCdm A)) p0001 p0004
  have p0006 :=
    @gSyl (.classMem A V) (.classMem A (synCvv))
      (.classEq (synCfv (synCdomfn) A) (synCdm A)) p0000 p0005
  exact p0006

/-- Checked nominal proof certificate identified upstream as `g_fvranfn`. -/
@[expose]
noncomputable def gFvranfn (A : Class) (V : Class) :
    Nominal.NPrf (.imp (.classMem A V) (.classEq (synCfv (synCranfn) A) (synCrn A))) :=
  by
  let proofSupport : Finset Var := A.fv ∪ V.fv
  let x : Var := freshVar proofSupport 0
  have fresh_x : x ∉ proofSupport :=
    by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_x_not_A : x ∉ A.fv := by
    intro h
    exact fresh_x (Finset.mem_union_left _ (h))
  have dv_cache_0001 : x ∉ (A).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_x_not_A, not_false_eq_true])
  have dv_cache_0002 : x ∉ ((synCrn A)).fv :=
    by
    clear dv_cache_0001
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_crn, fresh_x_not_A,
          not_false_eq_true])
  have dv_cache_0003 : x ∉ ((synCvv)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv,
          compact_fv_not_mem_empty, not_false_eq_true])
  have p0000 := @gElex A V
  have p0001 := @gRnexg A (synCvv)
  have p0002 := @gRneq (.cv x) A
  have p0003 := NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominalDfRanfn x
  have p0004 :=
    @gFvmptg x A (synCrn (.cv x)) (synCrn A) (synCvv) (synCvv) (synCranfn)
      dv_cache_0001 dv_cache_0002 dv_cache_0003 p0002 p0003
  have p0005 :=
    @gMpdan (.classMem A (synCvv)) (.classMem (synCrn A) (synCvv))
      (.classEq (synCfv (synCranfn) A) (synCrn A)) p0001 p0004
  have p0006 :=
    @gSyl (.classMem A V) (.classMem A (synCvv))
      (.classEq (synCfv (synCranfn) A) (synCrn A)) p0000 p0005
  exact p0006


end NFChoice.DirectNominalPrf.WPPReplay

end

/-! Certificates from `NominalWPPReplayChunk013Compact001Part014`. -/


section

namespace NFChoice.DirectNominalPrf.WPPReplay

open scoped Fol
open NFChoice.Foundation
open NFChoice.SemanticCore
open NFChoice.ReplaySupport
open NFChoice.Compiler.CompactSourceSyntax

/-- Checked nominal proof certificate identified upstream as `g_domfnex`. -/
@[expose]
noncomputable def gDomfnex : Nominal.NPrf (.classMem (synCdomfn) (synCvv)) :=
  by
  let proofSupport : Finset Var := (∅ : Finset Var)
  let x : Var := freshVar proofSupport 0
  let y : Var := freshVar proofSupport 1
  let z : Var := freshVar proofSupport 2
  let w : Var := freshVar proofSupport 3
  have fresh_x_ne_y : x ≠ y :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have fresh_y_ne_x : y ≠ x := Ne.symm fresh_x_ne_y
  have fresh_x_ne_z : x ≠ z :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 2
    exact freshVar_injective proofSupport (i := 0) (j := 2) (by decide)
  have fresh_z_ne_x : z ≠ x := Ne.symm fresh_x_ne_z
  have fresh_x_ne_w : x ≠ w :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 3
    exact freshVar_injective proofSupport (i := 0) (j := 3) (by decide)
  have fresh_w_ne_x : w ≠ x := Ne.symm fresh_x_ne_w
  have fresh_y_ne_z : y ≠ z :=
    by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 2
    exact freshVar_injective proofSupport (i := 1) (j := 2) (by decide)
  have fresh_z_ne_y : z ≠ y := Ne.symm fresh_y_ne_z
  have fresh_y_ne_w : y ≠ w :=
    by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 3
    exact freshVar_injective proofSupport (i := 1) (j := 3) (by decide)
  have fresh_w_ne_y : w ≠ y := Ne.symm fresh_y_ne_w
  have fresh_z_ne_w : z ≠ w :=
    by
    change freshVar proofSupport 2 ≠ freshVar proofSupport 3
    exact freshVar_injective proofSupport (i := 2) (j := 3) (by decide)
  have fresh_w_ne_z : w ≠ z := Ne.symm fresh_z_ne_w
  have dv_cache_0001 :
    w ∉ ((synCop (synCsn (.cv z)) (synCop (synCsn (.cv y)) (.cv x)))).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : w ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cop,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, fresh_w_ne_z, fresh_w_ne_y, fresh_w_ne_x, or_false,
          not_false_eq_true])
  have dv_cache_0002 :
    w ∉
      ((synCin (synCins4 (synCsi3 (synCswap))) (synCins2 (synCins2 (synCsset))))).fv :=
    by
    clear dv_cache_0001
    exact
      (by
        have compact_fv_not_mem_empty : w ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins4,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csi3,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cswap,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins2,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csset, Finset.mem_union,
          compact_fv_not_mem_empty, or_false, not_false_eq_true])
  have dv_cache_0003 : w ∉ ((synCop (.cv y) (.cv z))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact
      (by
        have compact_fv_not_mem_empty : w ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cop,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, fresh_w_ne_y, fresh_w_ne_z, or_false, not_false_eq_true])
  have dv_cache_0004 : w ∉ ((Class.cv x)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact
      (by
        have compact_fv_not_mem_empty : w ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_w_ne_x, not_false_eq_true])
  have dv_cache_0005 : z ∉ ((synCop (synCsn (.cv y)) (.cv x))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact
      (by
        have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cop,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, fresh_z_ne_y, fresh_z_ne_x, or_false, not_false_eq_true])
  have dv_cache_0006 :
    z ∉
      ((synCima
          (synCin (synCins4 (synCsi3 (synCswap))) (synCins2 (synCins2 (synCsset))))
          (synC1c))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact
      (by
        have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cima,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins4,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csi3,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cswap,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins2,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csset,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c, Finset.mem_union,
          compact_fv_not_mem_empty, or_false, not_false_eq_true])
  have dv_cache_0007 : z ∉ ((Class.cv y)).fv :=
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
          fresh_z_ne_y, not_false_eq_true])
  have dv_cache_0008 : z ∉ ((Class.cv x)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007
    exact
      (by
        have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_z_ne_x, not_false_eq_true])
  have dv_cache_0009 : x ∉ ((synCvv)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv,
          compact_fv_not_mem_empty, not_false_eq_true])
  have dv_cache_0010 :
    x ∉
      ((synCima (synCima (synCin (synCins4 (synCsi3 (synCswap)))
              (synCins2 (synCins2 (synCsset)))) (synC1c)) (synC1c))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cima,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins4,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csi3,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cswap,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins2,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csset,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c, Finset.mem_union,
          compact_fv_not_mem_empty, or_false, not_false_eq_true])
  have dv_cache_0011 :
    y ∉
      ((synCima (synCima (synCin (synCins4 (synCsi3 (synCswap)))
              (synCins2 (synCins2 (synCsset)))) (synC1c)) (synC1c))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cima,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins4,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csi3,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cswap,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins2,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csset,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c, Finset.mem_union,
          compact_fv_not_mem_empty, or_false, not_false_eq_true])
  have dv_cache_0012 : y ∉ ((synCdm (.cv x))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdm,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton, fresh_y_ne_x,
          not_false_eq_true])
  have dv_cache_0013 : x ≠ y :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012
    exact (show x ≠ y from (by exact fresh_x_ne_y))
  have p0000 := NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominalDfDomfn x
  have p0001 :=
    @gElin
      (synCop (synCsn (.cv w))
        (synCop (synCsn (.cv z)) (synCop (synCsn (.cv y)) (.cv x))))
      (synCins4 (synCsi3 (synCswap))) (synCins2 (synCins2 (synCsset)))
  have p0002 := @gVex x
  have p0003 :=
    @gOqelins4 (synCsn (.cv w)) (synCsn (.cv z)) (synCsn (.cv y)) (.cv x)
      (synCsi3 (synCswap)) p0002
  have p0004 := @gVex w
  have p0005 := @gVex z
  have p0006 := @gVex y
  have p0007 := @gOtsnelsi3 (.cv w) (.cv z) (.cv y) (synCswap) p0004 p0005 p0006
  have p0008 :=
    (Nominal.biimpRefl (synWbr (.cv w) (synCswap) (synCop (.cv z) (.cv y))))
  have p0009 := @gBrswap2 (.cv w) (.cv z) (.cv y) p0005 p0006
  have p0010 :=
    @gN3bitr2i
      (.classMem (synCop (synCsn (.cv w)) (synCop (synCsn (.cv z)) (synCsn (.cv y))))
        (synCsi3 (synCswap)))
      (.classMem (synCop (.cv w) (synCop (.cv z) (.cv y))) (synCswap))
      (synWbr (.cv w) (synCswap) (synCop (.cv z) (.cv y)))
      (.classEq (.cv w) (synCop (.cv y) (.cv z))) p0007 p0008 p0009
  have p0011 :=
    @gBitri
      (.classMem (synCop (synCsn (.cv w))
          (synCop (synCsn (.cv z)) (synCop (synCsn (.cv y)) (.cv x))))
        (synCins4 (synCsi3 (synCswap))))
      (.classMem (synCop (synCsn (.cv w)) (synCop (synCsn (.cv z)) (synCsn (.cv y))))
        (synCsi3 (synCswap)))
      (.classEq (.cv w) (synCop (.cv y) (.cv z))) p0003 p0010
  have p0012 := @gSnex (.cv z)
  have p0013 :=
    @gOtelins2 (synCsn (.cv w)) (synCsn (.cv z)) (synCop (synCsn (.cv y)) (.cv x))
      (synCins2 (synCsset)) p0012
  have p0014 := @gSnex (.cv y)
  have p0015 := @gOtelins2 (synCsn (.cv w)) (synCsn (.cv y)) (.cv x) (synCsset) p0014
  have p0016 := @gOpelssetsn (.cv w) (.cv x) p0004 p0002
  have p0017_e01_recanon :
    Nominal.NPrf
      (synWb (.classMem (synCop (synCsn (.cv w)) (.cv x)) (synCsset)) (.objMem w x)) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold synWb synCop synCun synCnin synWnan synWa synCcompl synWrex synWex
          synCphi synCsn synCsset synCopab synWss synCin
        simp (config :=
          { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_class_cv]
        apply Nominal.RecanonTransportDev.TRecanonWff.neg
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · apply Nominal.RecanonTransportDev.TRecanonWff.imp
          · exact Nominal.RecanonTransportDev.TRecanonWff.same _
          · exact Nominal.RecanonTransportDev.TRecanonWff.classMem_objMem _ _
        · apply Nominal.RecanonTransportDev.TRecanonWff.neg
          apply Nominal.RecanonTransportDev.TRecanonWff.imp
          · exact Nominal.RecanonTransportDev.TRecanonWff.classMem_objMem _ _
          · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0016
  have p0017 :=
    @gBitri
      (.classMem (synCop (synCsn (.cv w)) (synCop (synCsn (.cv y)) (.cv x)))
        (synCins2 (synCsset)))
      (.classMem (synCop (synCsn (.cv w)) (.cv x)) (synCsset)) (.objMem w x) p0015
      p0017_e01_recanon
  have p0018 :=
    @gBitri
      (.classMem (synCop (synCsn (.cv w))
          (synCop (synCsn (.cv z)) (synCop (synCsn (.cv y)) (.cv x))))
        (synCins2 (synCins2 (synCsset))))
      (.classMem (synCop (synCsn (.cv w)) (synCop (synCsn (.cv y)) (.cv x)))
        (synCins2 (synCsset)))
      (.objMem w x) p0013 p0017
  have p0019 :=
    @gAnbi12i
      (.classMem (synCop (synCsn (.cv w))
          (synCop (synCsn (.cv z)) (synCop (synCsn (.cv y)) (.cv x))))
        (synCins4 (synCsi3 (synCswap))))
      (.classEq (.cv w) (synCop (.cv y) (.cv z)))
      (.classMem (synCop (synCsn (.cv w))
          (synCop (synCsn (.cv z)) (synCop (synCsn (.cv y)) (.cv x))))
        (synCins2 (synCins2 (synCsset))))
      (.objMem w x) p0011 p0018
  have p0020 :=
    @gBitri
      (.classMem (synCop (synCsn (.cv w))
          (synCop (synCsn (.cv z)) (synCop (synCsn (.cv y)) (.cv x))))
        (synCin (synCins4 (synCsi3 (synCswap))) (synCins2 (synCins2 (synCsset)))))
      (synWa (.classMem (synCop (synCsn (.cv w))
            (synCop (synCsn (.cv z)) (synCop (synCsn (.cv y)) (.cv x))))
          (synCins4 (synCsi3 (synCswap)))) (.classMem (synCop (synCsn (.cv w))
            (synCop (synCsn (.cv z)) (synCop (synCsn (.cv y)) (.cv x))))
          (synCins2 (synCins2 (synCsset)))))
      (synWa (.classEq (.cv w) (synCop (.cv y) (.cv z))) (.objMem w x)) p0001 p0019
  have p0021 :=
    @gExbii
      (.classMem (synCop (synCsn (.cv w))
          (synCop (synCsn (.cv z)) (synCop (synCsn (.cv y)) (.cv x))))
        (synCin (synCins4 (synCsi3 (synCswap))) (synCins2 (synCins2 (synCsset)))))
      (synWa (.classEq (.cv w) (synCop (.cv y) (.cv z))) (.objMem w x)) w p0020
  have p0022 :=
    @gElima1c w (synCop (synCsn (.cv z)) (synCop (synCsn (.cv y)) (.cv x)))
      (synCin (synCins4 (synCsi3 (synCswap))) (synCins2 (synCins2 (synCsset))))
      dv_cache_0001 dv_cache_0002
  have p0023 :=
    (NFChoice.DirectNominalPrf.Nominal.DefinitionLeafHandlersCanonical001.dfClelOfDV w
      (synCop (.cv y) (.cv z)) (.cv x) dv_cache_0003 dv_cache_0004)
  have p0024_e02_recanon :
    Nominal.NPrf
      (synWb (.classMem (synCop (.cv y) (.cv z)) (.cv x)) (synWex w
          (synWa (.classEq (.cv w) (synCop (.cv y) (.cv z))) (.objMem w x)))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold synWb synCop synCun synCnin synWnan synWa synCcompl synWrex synWex
          synCphi
        simp (config :=
          { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_class_cv]
        apply Nominal.RecanonTransportDev.TRecanonWff.neg
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · apply Nominal.RecanonTransportDev.TRecanonWff.imp
          · exact Nominal.RecanonTransportDev.TRecanonWff.same _
          · apply Nominal.RecanonTransportDev.TRecanonWff.neg
            apply Nominal.RecanonTransportDev.TRecanonWff.all
            apply Nominal.RecanonTransportDev.TRecanonWff.neg
            apply Nominal.RecanonTransportDev.TRecanonWff.neg
            apply Nominal.RecanonTransportDev.TRecanonWff.imp
            · exact Nominal.RecanonTransportDev.TRecanonWff.same _
            · apply Nominal.RecanonTransportDev.TRecanonWff.neg
              exact Nominal.RecanonTransportDev.TRecanonWff.classMem_objMem _ _
        · apply Nominal.RecanonTransportDev.TRecanonWff.neg
          apply Nominal.RecanonTransportDev.TRecanonWff.imp
          · apply Nominal.RecanonTransportDev.TRecanonWff.neg
            apply Nominal.RecanonTransportDev.TRecanonWff.all
            apply Nominal.RecanonTransportDev.TRecanonWff.neg
            apply Nominal.RecanonTransportDev.TRecanonWff.neg
            apply Nominal.RecanonTransportDev.TRecanonWff.imp
            · exact Nominal.RecanonTransportDev.TRecanonWff.same _
            · apply Nominal.RecanonTransportDev.TRecanonWff.neg
              exact Nominal.RecanonTransportDev.TRecanonWff.classMem_objMem _ _
          · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0023
  have p0024 :=
    @gN3bitr4i
      (synWex w (.classMem (synCop (synCsn (.cv w))
            (synCop (synCsn (.cv z)) (synCop (synCsn (.cv y)) (.cv x))))
          (synCin (synCins4 (synCsi3 (synCswap))) (synCins2 (synCins2 (synCsset))))))
      (synWex w (synWa (.classEq (.cv w) (synCop (.cv y) (.cv z))) (.objMem w x)))
      (.classMem (synCop (synCsn (.cv z)) (synCop (synCsn (.cv y)) (.cv x))) (synCima
          (synCin (synCins4 (synCsi3 (synCswap))) (synCins2 (synCins2 (synCsset))))
          (synC1c)))
      (.classMem (synCop (.cv y) (.cv z)) (.cv x)) p0021 p0022 p0024_e02_recanon
  have p0025 :=
    @gExbii
      (.classMem (synCop (synCsn (.cv z)) (synCop (synCsn (.cv y)) (.cv x))) (synCima
          (synCin (synCins4 (synCsi3 (synCswap))) (synCins2 (synCins2 (synCsset))))
          (synC1c)))
      (.classMem (synCop (.cv y) (.cv z)) (.cv x)) z p0024
  have p0026 :=
    @gElima1c z (synCop (synCsn (.cv y)) (.cv x))
      (synCima (synCin (synCins4 (synCsi3 (synCswap))) (synCins2 (synCins2 (synCsset))))
        (synC1c))
      dv_cache_0005 dv_cache_0006
  have p0027 := @gEldm2 z (.cv y) (.cv x) dv_cache_0007 dv_cache_0008
  have p0028 :=
    @gN3bitr4i
      (synWex z (.classMem (synCop (synCsn (.cv z)) (synCop (synCsn (.cv y)) (.cv x)))
          (synCima (synCin (synCins4 (synCsi3 (synCswap)))
              (synCins2 (synCins2 (synCsset)))) (synC1c))))
      (synWex z (.classMem (synCop (.cv y) (.cv z)) (.cv x)))
      (.classMem (synCop (synCsn (.cv y)) (.cv x)) (synCima (synCima
            (synCin (synCins4 (synCsi3 (synCswap))) (synCins2 (synCins2 (synCsset))))
            (synC1c)) (synC1c)))
      (.classMem (.cv y) (synCdm (.cv x))) p0025 p0026 p0027
  have p0029 :=
    @gReleqmpt x y (synCvv)
      (synCima (synCima
          (synCin (synCins4 (synCsi3 (synCswap))) (synCins2 (synCins2 (synCsset))))
          (synC1c)) (synC1c))
      (synCdm (.cv x)) dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012
      dv_cache_0013 p0028
  have p0030 :=
    @gEqtr4i (synCdomfn) (synCmpt x (synCvv) (synCdm (.cv x)))
      (synCin (synCxp (synCvv) (synCvv)) (synCcnv (synCcompl (synCima
              (synCsymdif (synCins3 (synCsset)) (synCins2 (synCima (synCima
                      (synCin (synCins4 (synCsi3 (synCswap)))
                        (synCins2 (synCins2 (synCsset)))) (synC1c)) (synC1c))))
              (synC1c)))))
      p0000 p0029
  have p0031 := @gVvex
  have p0032 := @gSwapex
  have p0033 := @gSi3ex (synCswap) p0032
  have p0034 := @gIns4ex (synCsi3 (synCswap)) p0033
  have p0035 := @gSsetex
  have p0036 := @gIns2ex (synCsset) p0035
  have p0037 := @gIns2ex (synCins2 (synCsset)) p0036
  have p0038 :=
    @gInex (synCins4 (synCsi3 (synCswap))) (synCins2 (synCins2 (synCsset))) p0034
      p0037
  have p0039 := @gN1cex
  have p0040 :=
    @gImaex
      (synCin (synCins4 (synCsi3 (synCswap))) (synCins2 (synCins2 (synCsset))))
      (synC1c) p0038 p0039
  have p0042 :=
    @gImaex
      (synCima (synCin (synCins4 (synCsi3 (synCswap))) (synCins2 (synCins2 (synCsset))))
        (synC1c))
      (synC1c) p0040 p0039
  have p0043 :=
    @gMptexlem (synCvv)
      (synCima (synCima
          (synCin (synCins4 (synCsi3 (synCswap))) (synCins2 (synCins2 (synCsset))))
          (synC1c)) (synC1c))
      p0031 p0042
  have p0044 :=
    @gEqeltri (synCdomfn)
      (synCin (synCxp (synCvv) (synCvv)) (synCcnv (synCcompl (synCima
              (synCsymdif (synCins3 (synCsset)) (synCins2 (synCima (synCima
                      (synCin (synCins4 (synCsi3 (synCswap)))
                        (synCins2 (synCins2 (synCsset)))) (synC1c)) (synC1c))))
              (synC1c)))))
      (synCvv) p0030 p0043
  exact p0044

/-- Checked nominal proof certificate identified upstream as `g_ranfnex`. -/
@[expose]
noncomputable def gRanfnex : Nominal.NPrf (.classMem (synCranfn) (synCvv)) :=
  by
  let proofSupport : Finset Var := (∅ : Finset Var)
  let x : Var := freshVar proofSupport 0
  let y : Var := freshVar proofSupport 1
  let z : Var := freshVar proofSupport 2
  let w : Var := freshVar proofSupport 3
  have fresh_x_ne_y : x ≠ y :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have fresh_y_ne_x : y ≠ x := Ne.symm fresh_x_ne_y
  have fresh_x_ne_z : x ≠ z :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 2
    exact freshVar_injective proofSupport (i := 0) (j := 2) (by decide)
  have fresh_z_ne_x : z ≠ x := Ne.symm fresh_x_ne_z
  have fresh_x_ne_w : x ≠ w :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 3
    exact freshVar_injective proofSupport (i := 0) (j := 3) (by decide)
  have fresh_w_ne_x : w ≠ x := Ne.symm fresh_x_ne_w
  have fresh_y_ne_z : y ≠ z :=
    by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 2
    exact freshVar_injective proofSupport (i := 1) (j := 2) (by decide)
  have fresh_z_ne_y : z ≠ y := Ne.symm fresh_y_ne_z
  have fresh_y_ne_w : y ≠ w :=
    by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 3
    exact freshVar_injective proofSupport (i := 1) (j := 3) (by decide)
  have fresh_w_ne_y : w ≠ y := Ne.symm fresh_y_ne_w
  have fresh_z_ne_w : z ≠ w :=
    by
    change freshVar proofSupport 2 ≠ freshVar proofSupport 3
    exact freshVar_injective proofSupport (i := 2) (j := 3) (by decide)
  have fresh_w_ne_z : w ≠ z := Ne.symm fresh_z_ne_w
  have dv_cache_0001 :
    w ∉ ((synCop (synCsn (.cv z)) (synCop (synCsn (.cv y)) (.cv x)))).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : w ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cop,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, fresh_w_ne_z, fresh_w_ne_y, fresh_w_ne_x, or_false,
          not_false_eq_true])
  have dv_cache_0002 :
    w ∉
      ((synCin (synCins4 (synCsi3 (synCid))) (synCins2 (synCins2 (synCsset))))).fv :=
    by
    clear dv_cache_0001
    exact
      (by
        have compact_fv_not_mem_empty : w ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins4,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csi3,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cid,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins2,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csset, Finset.mem_union,
          compact_fv_not_mem_empty, or_false, not_false_eq_true])
  have dv_cache_0003 : w ∉ ((synCop (.cv z) (.cv y))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact
      (by
        have compact_fv_not_mem_empty : w ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cop,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, fresh_w_ne_z, fresh_w_ne_y, or_false, not_false_eq_true])
  have dv_cache_0004 : w ∉ ((Class.cv x)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact
      (by
        have compact_fv_not_mem_empty : w ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_w_ne_x, not_false_eq_true])
  have dv_cache_0005 : z ∉ ((synCop (synCsn (.cv y)) (.cv x))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact
      (by
        have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cop,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, fresh_z_ne_y, fresh_z_ne_x, or_false, not_false_eq_true])
  have dv_cache_0006 :
    z ∉
      ((synCima (synCin (synCins4 (synCsi3 (synCid))) (synCins2 (synCins2 (synCsset))))
          (synC1c))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact
      (by
        have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cima,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins4,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csi3,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cid,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins2,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csset,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c, Finset.mem_union,
          compact_fv_not_mem_empty, or_false, not_false_eq_true])
  have dv_cache_0007 : z ∉ ((Class.cv y)).fv :=
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
          fresh_z_ne_y, not_false_eq_true])
  have dv_cache_0008 : z ∉ ((Class.cv x)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007
    exact
      (by
        have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_z_ne_x, not_false_eq_true])
  have dv_cache_0009 : x ∉ ((synCvv)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv,
          compact_fv_not_mem_empty, not_false_eq_true])
  have dv_cache_0010 :
    x ∉
      ((synCima (synCima
            (synCin (synCins4 (synCsi3 (synCid))) (synCins2 (synCins2 (synCsset))))
            (synC1c)) (synC1c))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cima,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins4,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csi3,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cid,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins2,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csset,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c, Finset.mem_union,
          compact_fv_not_mem_empty, or_false, not_false_eq_true])
  have dv_cache_0011 :
    y ∉
      ((synCima (synCima
            (synCin (synCins4 (synCsi3 (synCid))) (synCins2 (synCins2 (synCsset))))
            (synC1c)) (synC1c))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cima,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins4,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csi3,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cid,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins2,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csset,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c, Finset.mem_union,
          compact_fv_not_mem_empty, or_false, not_false_eq_true])
  have dv_cache_0012 : y ∉ ((synCrn (.cv x))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_crn,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton, fresh_y_ne_x,
          not_false_eq_true])
  have dv_cache_0013 : x ≠ y :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012
    exact (show x ≠ y from (by exact fresh_x_ne_y))
  have p0000 := NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominalDfRanfn x
  have p0001 :=
    @gElin
      (synCop (synCsn (.cv w))
        (synCop (synCsn (.cv z)) (synCop (synCsn (.cv y)) (.cv x))))
      (synCins4 (synCsi3 (synCid))) (synCins2 (synCins2 (synCsset)))
  have p0002 := @gVex x
  have p0003 :=
    @gOqelins4 (synCsn (.cv w)) (synCsn (.cv z)) (synCsn (.cv y)) (.cv x)
      (synCsi3 (synCid)) p0002
  have p0004 := @gVex w
  have p0005 := @gVex z
  have p0006 := @gVex y
  have p0007 := @gOtsnelsi3 (.cv w) (.cv z) (.cv y) (synCid) p0004 p0005 p0006
  have p0008 := (Nominal.biimpRefl (synWbr (.cv w) (synCid) (synCop (.cv z) (.cv y))))
  have p0009 := @gOpex (.cv z) (.cv y) p0005 p0006
  have p0010 := @gIdeq (.cv w) (synCop (.cv z) (.cv y)) p0009
  have p0011 :=
    @gN3bitr2i
      (.classMem (synCop (synCsn (.cv w)) (synCop (synCsn (.cv z)) (synCsn (.cv y))))
        (synCsi3 (synCid)))
      (.classMem (synCop (.cv w) (synCop (.cv z) (.cv y))) (synCid))
      (synWbr (.cv w) (synCid) (synCop (.cv z) (.cv y)))
      (.classEq (.cv w) (synCop (.cv z) (.cv y))) p0007 p0008 p0010
  have p0012 :=
    @gBitri
      (.classMem (synCop (synCsn (.cv w))
          (synCop (synCsn (.cv z)) (synCop (synCsn (.cv y)) (.cv x))))
        (synCins4 (synCsi3 (synCid))))
      (.classMem (synCop (synCsn (.cv w)) (synCop (synCsn (.cv z)) (synCsn (.cv y))))
        (synCsi3 (synCid)))
      (.classEq (.cv w) (synCop (.cv z) (.cv y))) p0003 p0011
  have p0013 := @gSnex (.cv z)
  have p0014 :=
    @gOtelins2 (synCsn (.cv w)) (synCsn (.cv z)) (synCop (synCsn (.cv y)) (.cv x))
      (synCins2 (synCsset)) p0013
  have p0015 := @gSnex (.cv y)
  have p0016 := @gOtelins2 (synCsn (.cv w)) (synCsn (.cv y)) (.cv x) (synCsset) p0015
  have p0017 := @gOpelssetsn (.cv w) (.cv x) p0004 p0002
  have p0018_e01_recanon :
    Nominal.NPrf
      (synWb (.classMem (synCop (synCsn (.cv w)) (.cv x)) (synCsset)) (.objMem w x)) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold synWb synCop synCun synCnin synWnan synWa synCcompl synWrex synWex
          synCphi synCsn synCsset synCopab synWss synCin
        simp (config :=
          { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_class_cv]
        apply Nominal.RecanonTransportDev.TRecanonWff.neg
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · apply Nominal.RecanonTransportDev.TRecanonWff.imp
          · exact Nominal.RecanonTransportDev.TRecanonWff.same _
          · exact Nominal.RecanonTransportDev.TRecanonWff.classMem_objMem _ _
        · apply Nominal.RecanonTransportDev.TRecanonWff.neg
          apply Nominal.RecanonTransportDev.TRecanonWff.imp
          · exact Nominal.RecanonTransportDev.TRecanonWff.classMem_objMem _ _
          · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0017
  have p0018 :=
    @gBitri
      (.classMem (synCop (synCsn (.cv w)) (synCop (synCsn (.cv y)) (.cv x)))
        (synCins2 (synCsset)))
      (.classMem (synCop (synCsn (.cv w)) (.cv x)) (synCsset)) (.objMem w x) p0016
      p0018_e01_recanon
  have p0019 :=
    @gBitri
      (.classMem (synCop (synCsn (.cv w))
          (synCop (synCsn (.cv z)) (synCop (synCsn (.cv y)) (.cv x))))
        (synCins2 (synCins2 (synCsset))))
      (.classMem (synCop (synCsn (.cv w)) (synCop (synCsn (.cv y)) (.cv x)))
        (synCins2 (synCsset)))
      (.objMem w x) p0014 p0018
  have p0020 :=
    @gAnbi12i
      (.classMem (synCop (synCsn (.cv w))
          (synCop (synCsn (.cv z)) (synCop (synCsn (.cv y)) (.cv x))))
        (synCins4 (synCsi3 (synCid))))
      (.classEq (.cv w) (synCop (.cv z) (.cv y)))
      (.classMem (synCop (synCsn (.cv w))
          (synCop (synCsn (.cv z)) (synCop (synCsn (.cv y)) (.cv x))))
        (synCins2 (synCins2 (synCsset))))
      (.objMem w x) p0012 p0019
  have p0021 :=
    @gBitri
      (.classMem (synCop (synCsn (.cv w))
          (synCop (synCsn (.cv z)) (synCop (synCsn (.cv y)) (.cv x))))
        (synCin (synCins4 (synCsi3 (synCid))) (synCins2 (synCins2 (synCsset)))))
      (synWa (.classMem (synCop (synCsn (.cv w))
            (synCop (synCsn (.cv z)) (synCop (synCsn (.cv y)) (.cv x))))
          (synCins4 (synCsi3 (synCid)))) (.classMem (synCop (synCsn (.cv w))
            (synCop (synCsn (.cv z)) (synCop (synCsn (.cv y)) (.cv x))))
          (synCins2 (synCins2 (synCsset)))))
      (synWa (.classEq (.cv w) (synCop (.cv z) (.cv y))) (.objMem w x)) p0001 p0020
  have p0022 :=
    @gExbii
      (.classMem (synCop (synCsn (.cv w))
          (synCop (synCsn (.cv z)) (synCop (synCsn (.cv y)) (.cv x))))
        (synCin (synCins4 (synCsi3 (synCid))) (synCins2 (synCins2 (synCsset)))))
      (synWa (.classEq (.cv w) (synCop (.cv z) (.cv y))) (.objMem w x)) w p0021
  have p0023 :=
    @gElima1c w (synCop (synCsn (.cv z)) (synCop (synCsn (.cv y)) (.cv x)))
      (synCin (synCins4 (synCsi3 (synCid))) (synCins2 (synCins2 (synCsset))))
      dv_cache_0001 dv_cache_0002
  have p0024 :=
    (NFChoice.DirectNominalPrf.Nominal.DefinitionLeafHandlersCanonical001.dfClelOfDV w
      (synCop (.cv z) (.cv y)) (.cv x) dv_cache_0003 dv_cache_0004)
  have p0025_e02_recanon :
    Nominal.NPrf
      (synWb (.classMem (synCop (.cv z) (.cv y)) (.cv x)) (synWex w
          (synWa (.classEq (.cv w) (synCop (.cv z) (.cv y))) (.objMem w x)))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold synWb synCop synCun synCnin synWnan synWa synCcompl synWrex synWex
          synCphi
        simp (config :=
          { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_class_cv]
        apply Nominal.RecanonTransportDev.TRecanonWff.neg
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · apply Nominal.RecanonTransportDev.TRecanonWff.imp
          · exact Nominal.RecanonTransportDev.TRecanonWff.same _
          · apply Nominal.RecanonTransportDev.TRecanonWff.neg
            apply Nominal.RecanonTransportDev.TRecanonWff.all
            apply Nominal.RecanonTransportDev.TRecanonWff.neg
            apply Nominal.RecanonTransportDev.TRecanonWff.neg
            apply Nominal.RecanonTransportDev.TRecanonWff.imp
            · exact Nominal.RecanonTransportDev.TRecanonWff.same _
            · apply Nominal.RecanonTransportDev.TRecanonWff.neg
              exact Nominal.RecanonTransportDev.TRecanonWff.classMem_objMem _ _
        · apply Nominal.RecanonTransportDev.TRecanonWff.neg
          apply Nominal.RecanonTransportDev.TRecanonWff.imp
          · apply Nominal.RecanonTransportDev.TRecanonWff.neg
            apply Nominal.RecanonTransportDev.TRecanonWff.all
            apply Nominal.RecanonTransportDev.TRecanonWff.neg
            apply Nominal.RecanonTransportDev.TRecanonWff.neg
            apply Nominal.RecanonTransportDev.TRecanonWff.imp
            · exact Nominal.RecanonTransportDev.TRecanonWff.same _
            · apply Nominal.RecanonTransportDev.TRecanonWff.neg
              exact Nominal.RecanonTransportDev.TRecanonWff.classMem_objMem _ _
          · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0024
  have p0025 :=
    @gN3bitr4i
      (synWex w (.classMem (synCop (synCsn (.cv w))
            (synCop (synCsn (.cv z)) (synCop (synCsn (.cv y)) (.cv x))))
          (synCin (synCins4 (synCsi3 (synCid))) (synCins2 (synCins2 (synCsset))))))
      (synWex w (synWa (.classEq (.cv w) (synCop (.cv z) (.cv y))) (.objMem w x)))
      (.classMem (synCop (synCsn (.cv z)) (synCop (synCsn (.cv y)) (.cv x))) (synCima
          (synCin (synCins4 (synCsi3 (synCid))) (synCins2 (synCins2 (synCsset))))
          (synC1c)))
      (.classMem (synCop (.cv z) (.cv y)) (.cv x)) p0022 p0023 p0025_e02_recanon
  have p0026 :=
    @gExbii
      (.classMem (synCop (synCsn (.cv z)) (synCop (synCsn (.cv y)) (.cv x))) (synCima
          (synCin (synCins4 (synCsi3 (synCid))) (synCins2 (synCins2 (synCsset))))
          (synC1c)))
      (.classMem (synCop (.cv z) (.cv y)) (.cv x)) z p0025
  have p0027 :=
    @gElima1c z (synCop (synCsn (.cv y)) (.cv x))
      (synCima (synCin (synCins4 (synCsi3 (synCid))) (synCins2 (synCins2 (synCsset))))
        (synC1c))
      dv_cache_0005 dv_cache_0006
  have p0028 := @gElrn2 z (.cv y) (.cv x) dv_cache_0007 dv_cache_0008
  have p0029 :=
    @gN3bitr4i
      (synWex z (.classMem (synCop (synCsn (.cv z)) (synCop (synCsn (.cv y)) (.cv x)))
          (synCima
            (synCin (synCins4 (synCsi3 (synCid))) (synCins2 (synCins2 (synCsset))))
            (synC1c))))
      (synWex z (.classMem (synCop (.cv z) (.cv y)) (.cv x)))
      (.classMem (synCop (synCsn (.cv y)) (.cv x)) (synCima (synCima
            (synCin (synCins4 (synCsi3 (synCid))) (synCins2 (synCins2 (synCsset))))
            (synC1c)) (synC1c)))
      (.classMem (.cv y) (synCrn (.cv x))) p0026 p0027 p0028
  have p0030 :=
    @gReleqmpt x y (synCvv)
      (synCima (synCima
          (synCin (synCins4 (synCsi3 (synCid))) (synCins2 (synCins2 (synCsset))))
          (synC1c)) (synC1c))
      (synCrn (.cv x)) dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012
      dv_cache_0013 p0029
  have p0031 :=
    @gEqtr4i (synCranfn) (synCmpt x (synCvv) (synCrn (.cv x)))
      (synCin (synCxp (synCvv) (synCvv)) (synCcnv (synCcompl (synCima
              (synCsymdif (synCins3 (synCsset)) (synCins2 (synCima (synCima
                      (synCin (synCins4 (synCsi3 (synCid)))
                        (synCins2 (synCins2 (synCsset)))) (synC1c)) (synC1c))))
              (synC1c)))))
      p0000 p0030
  have p0032 := @gVvex
  have p0033 := @gIdex
  have p0034 := @gSi3ex (synCid) p0033
  have p0035 := @gIns4ex (synCsi3 (synCid)) p0034
  have p0036 := @gSsetex
  have p0037 := @gIns2ex (synCsset) p0036
  have p0038 := @gIns2ex (synCins2 (synCsset)) p0037
  have p0039 :=
    @gInex (synCins4 (synCsi3 (synCid))) (synCins2 (synCins2 (synCsset))) p0035
      p0038
  have p0040 := @gN1cex
  have p0041 :=
    @gImaex
      (synCin (synCins4 (synCsi3 (synCid))) (synCins2 (synCins2 (synCsset))))
      (synC1c) p0039 p0040
  have p0043 :=
    @gImaex
      (synCima (synCin (synCins4 (synCsi3 (synCid))) (synCins2 (synCins2 (synCsset))))
        (synC1c))
      (synC1c) p0041 p0040
  have p0044 :=
    @gMptexlem (synCvv)
      (synCima (synCima
          (synCin (synCins4 (synCsi3 (synCid))) (synCins2 (synCins2 (synCsset))))
          (synC1c)) (synC1c))
      p0032 p0043
  have p0045 :=
    @gEqeltri (synCranfn)
      (synCin (synCxp (synCvv) (synCvv)) (synCcnv (synCcompl (synCima
              (synCsymdif (synCins3 (synCsset)) (synCins2 (synCima (synCima
                      (synCin (synCins4 (synCsi3 (synCid)))
                        (synCins2 (synCins2 (synCsset)))) (synC1c)) (synC1c))))
              (synC1c)))))
      (synCvv) p0031 p0044
  exact p0045

/-- Checked nominal proof certificate identified upstream as `g_clos1eq1`. -/
@[expose]
noncomputable def gClos1eq1 (R : Class) (S : Class) (T : Class) :
    Nominal.NPrf (.imp (.classEq S T) (.classEq (synCclos1 S R) (synCclos1 T R))) :=
  by
  let proofSupport : Finset Var := R.fv ∪ S.fv ∪ T.fv
  let a : Var := freshVar proofSupport 0
  have fresh_a : a ∉ proofSupport :=
    by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_a_not_R : a ∉ R.fv := by
    intro h
    exact fresh_a (Finset.mem_union_left _ (Finset.mem_union_left _ (h)))
  have fresh_a_not_S : a ∉ S.fv := by
    intro h
    exact fresh_a (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_a_not_T : a ∉ T.fv := by
    intro h
    exact fresh_a (Finset.mem_union_right _ (h))
  have dv_cache_0001 : a ∉ ((Wff.classEq S T)).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : a ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, Finset.mem_union,
          fresh_a_not_S, fresh_a_not_T, or_false, not_false_eq_true])
  have dv_cache_0002 : a ∉ (R).fv :=
    by
    clear dv_cache_0001
    exact
      (by
        have compact_fv_not_mem_empty : a ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_a_not_R, not_false_eq_true])
  have dv_cache_0003 : a ∉ (S).fv :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact
      (by
        have compact_fv_not_mem_empty : a ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_a_not_S, not_false_eq_true])
  have dv_cache_0004 : a ∉ (T).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact
      (by
        have compact_fv_not_mem_empty : a ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_a_not_T, not_false_eq_true])
  have p0000 := @gSseq1 S T (.cv a)
  have p0001 :=
    @gAnbi1d (.classEq S T) (synWss S (.cv a)) (synWss T (.cv a))
      (synWss (synCima R (.cv a)) (.cv a)) p0000
  have p0002 :=
    @gAbbidv (.classEq S T)
      (synWa (synWss S (.cv a)) (synWss (synCima R (.cv a)) (.cv a)))
      (synWa (synWss T (.cv a)) (synWss (synCima R (.cv a)) (.cv a))) a dv_cache_0001
      p0001
  have p0003 :=
    @gInteq (.cab a (synWa (synWss S (.cv a)) (synWss (synCima R (.cv a)) (.cv a))))
      (.cab a (synWa (synWss T (.cv a)) (synWss (synCima R (.cv a)) (.cv a))))
  have p0004 :=
    @gSyl (.classEq S T)
      (.classEq (.cab a (synWa (synWss S (.cv a)) (synWss (synCima R (.cv a)) (.cv a))))
        (.cab a (synWa (synWss T (.cv a)) (synWss (synCima R (.cv a)) (.cv a)))))
      (.classEq (synCint
          (.cab a (synWa (synWss S (.cv a)) (synWss (synCima R (.cv a)) (.cv a)))))
        (synCint (.cab a (synWa (synWss T (.cv a)) (synWss (synCima R (.cv a)) (.cv a))))))
      p0002 p0003
  have p0005 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominalDfClos1 R S a
      dv_cache_0002 dv_cache_0003
  have p0006 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominalDfClos1 R T a
      dv_cache_0002 dv_cache_0004
  have p0007 :=
    @gN3eqtr4g (.classEq S T)
      (synCint (.cab a (synWa (synWss S (.cv a)) (synWss (synCima R (.cv a)) (.cv a)))))
      (synCint (.cab a (synWa (synWss T (.cv a)) (synWss (synCima R (.cv a)) (.cv a)))))
      (synCclos1 S R) (synCclos1 T R) p0004 p0005 p0006
  exact p0007

/-- Checked nominal proof certificate identified upstream as `g_clos1eq2`. -/
@[expose]
noncomputable def gClos1eq2 (R : Class) (S : Class) (T : Class) :
    Nominal.NPrf (.imp (.classEq R T) (.classEq (synCclos1 S R) (synCclos1 S T))) :=
  by
  let proofSupport : Finset Var := R.fv ∪ S.fv ∪ T.fv
  let a : Var := freshVar proofSupport 0
  have fresh_a : a ∉ proofSupport :=
    by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_a_not_R : a ∉ R.fv := by
    intro h
    exact fresh_a (Finset.mem_union_left _ (Finset.mem_union_left _ (h)))
  have fresh_a_not_S : a ∉ S.fv := by
    intro h
    exact fresh_a (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_a_not_T : a ∉ T.fv := by
    intro h
    exact fresh_a (Finset.mem_union_right _ (h))
  have dv_cache_0001 : a ∉ ((Wff.classEq R T)).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : a ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, Finset.mem_union,
          fresh_a_not_R, fresh_a_not_T, or_false, not_false_eq_true])
  have dv_cache_0002 : a ∉ (R).fv :=
    by
    clear dv_cache_0001
    exact
      (by
        have compact_fv_not_mem_empty : a ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_a_not_R, not_false_eq_true])
  have dv_cache_0003 : a ∉ (S).fv :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact
      (by
        have compact_fv_not_mem_empty : a ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_a_not_S, not_false_eq_true])
  have dv_cache_0004 : a ∉ (T).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact
      (by
        have compact_fv_not_mem_empty : a ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_a_not_T, not_false_eq_true])
  have p0000 := @gImaeq1 R T (.cv a)
  have p0001 :=
    @gSseq1d (.classEq R T) (synCima R (.cv a)) (synCima T (.cv a)) (.cv a) p0000
  have p0002 :=
    @gAnbi2d (.classEq R T) (synWss (synCima R (.cv a)) (.cv a))
      (synWss (synCima T (.cv a)) (.cv a)) (synWss S (.cv a)) p0001
  have p0003 :=
    @gAbbidv (.classEq R T)
      (synWa (synWss S (.cv a)) (synWss (synCima R (.cv a)) (.cv a)))
      (synWa (synWss S (.cv a)) (synWss (synCima T (.cv a)) (.cv a))) a dv_cache_0001
      p0002
  have p0004 :=
    @gInteq (.cab a (synWa (synWss S (.cv a)) (synWss (synCima R (.cv a)) (.cv a))))
      (.cab a (synWa (synWss S (.cv a)) (synWss (synCima T (.cv a)) (.cv a))))
  have p0005 :=
    @gSyl (.classEq R T)
      (.classEq (.cab a (synWa (synWss S (.cv a)) (synWss (synCima R (.cv a)) (.cv a))))
        (.cab a (synWa (synWss S (.cv a)) (synWss (synCima T (.cv a)) (.cv a)))))
      (.classEq (synCint
          (.cab a (synWa (synWss S (.cv a)) (synWss (synCima R (.cv a)) (.cv a)))))
        (synCint (.cab a (synWa (synWss S (.cv a)) (synWss (synCima T (.cv a)) (.cv a))))))
      p0003 p0004
  have p0006 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominalDfClos1 R S a
      dv_cache_0002 dv_cache_0003
  have p0007 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominalDfClos1 T S a
      dv_cache_0004 dv_cache_0003
  have p0008 :=
    @gN3eqtr4g (.classEq R T)
      (synCint (.cab a (synWa (synWss S (.cv a)) (synWss (synCima R (.cv a)) (.cv a)))))
      (synCint (.cab a (synWa (synWss S (.cv a)) (synWss (synCima T (.cv a)) (.cv a)))))
      (synCclos1 S R) (synCclos1 S T) p0005 p0006 p0007
  exact p0008


end NFChoice.DirectNominalPrf.WPPReplay

end

/-! Certificates from `NominalWPPReplayChunk013Compact001Part015`. -/


section

namespace NFChoice.DirectNominalPrf.WPPReplay

open scoped Fol
open NFChoice.Foundation
open NFChoice.SemanticCore
open NFChoice.ReplaySupport
open NFChoice.Compiler.CompactSourceSyntax

/-- Checked nominal proof certificate identified upstream as `g_clos1ex`. -/
@[expose]
noncomputable def gClos1ex (R : Class) (S : Class)
    (hyp_clos1ex_1 : Nominal.NPrf (.classMem S (synCvv)))
    (hyp_clos1ex_2 : Nominal.NPrf (.classMem R (synCvv))) :
    Nominal.NPrf (.classMem (synCclos1 S R) (synCvv)) :=
  by
  let proofSupport : Finset Var := R.fv ∪ S.fv
  let a : Var := freshVar proofSupport 0
  let b : Var := freshVar proofSupport 1
  have fresh_a : a ∉ proofSupport :=
    by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_a_not_R : a ∉ R.fv := by
    intro h
    exact fresh_a (Finset.mem_union_left _ (h))
  have fresh_a_not_S : a ∉ S.fv := by
    intro h
    exact fresh_a (Finset.mem_union_right _ (h))
  have fresh_b : b ∉ proofSupport :=
    by
    change freshVar proofSupport 1 ∉ proofSupport
    exact freshVar_not_mem proofSupport 1
  have fresh_b_not_R : b ∉ R.fv := by
    intro h
    exact fresh_b (Finset.mem_union_left _ (h))
  have fresh_a_ne_b : a ≠ b :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have fresh_b_ne_a : b ≠ a := Ne.symm fresh_a_ne_b
  have dv_cache_0001 : a ∉ (R).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : a ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_a_not_R, not_false_eq_true])
  have dv_cache_0002 : a ∉ (S).fv :=
    by
    clear dv_cache_0001
    exact
      (by
        have compact_fv_not_mem_empty : a ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_a_not_S, not_false_eq_true])
  have dv_cache_0003 : b ∉ ((Class.cv a)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact
      (by
        have compact_fv_not_mem_empty : b ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_b_ne_a, not_false_eq_true])
  have dv_cache_0004 : b ∉ ((synCsset)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact
      (by
        have compact_fv_not_mem_empty : b ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csset,
          compact_fv_not_mem_empty, not_false_eq_true])
  have dv_cache_0005 : b ∉ ((synCimage R)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact
      (by
        have compact_fv_not_mem_empty : b ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cimage, fresh_b_not_R,
          not_false_eq_true])
  have dv_cache_0006 : b ∉ ((synCima R (.cv a))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact
      (by
        have compact_fv_not_mem_empty : b ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cima,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, fresh_b_not_R, fresh_b_ne_a, or_false, not_false_eq_true])
  have dv_cache_0007 : b ∉ ((synWss (synCima R (.cv a)) (.cv a))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006
    exact
      (by
        have compact_fv_not_mem_empty : b ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wss,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cima,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, fresh_b_not_R, fresh_b_ne_a, or_false, not_false_eq_true])
  have dv_cache_0008 :
    a ∉
      ((synCin (synCima (synCsset) (synCsn S))
          (synCfix (synCcom (synCsset) (synCimage R))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007
    exact
      (by
        have compact_fv_not_mem_empty : a ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cima,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csset,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfix,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccom,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cimage, Finset.mem_union,
          fresh_a_not_S, fresh_a_not_R, compact_fv_not_mem_empty, or_false,
          not_false_eq_true])
  have p0000 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominalDfClos1 R S a
      dv_cache_0001 dv_cache_0002
  have p0001 :=
    @gElin (.cv a) (synCima (synCsset) (synCsn S))
      (synCfix (synCcom (synCsset) (synCimage R)))
  have p0002 := @gElimasn (synCsset) S (.cv a)
  have p0003 := (Nominal.biimpRefl (synWbr S (synCsset) (.cv a)))
  have p0004 := @gVex a
  have p0005 := @gBrsset S (.cv a) hyp_clos1ex_1 p0004
  have p0006 :=
    @gN3bitr2i (.classMem (.cv a) (synCima (synCsset) (synCsn S)))
      (.classMem (synCop S (.cv a)) (synCsset)) (synWbr S (synCsset) (.cv a))
      (synWss S (.cv a)) p0002 p0003 p0005
  have p0007 := @gElfix (.cv a) (synCcom (synCsset) (synCimage R))
  have p0008 :=
    @gBrco b (.cv a) (.cv a) (synCsset) (synCimage R) dv_cache_0003 dv_cache_0003
      dv_cache_0004 dv_cache_0005
  have p0009 := @gVex b
  have p0010 := @gBrimage (.cv a) (.cv b) R p0004 p0009
  have p0011 :=
    @gAnbi1i (synWbr (.cv a) (synCimage R) (.cv b))
      (.classEq (.cv b) (synCima R (.cv a))) (synWbr (.cv b) (synCsset) (.cv a)) p0010
  have p0012 :=
    @gExbii
      (synWa (synWbr (.cv a) (synCimage R) (.cv b)) (synWbr (.cv b) (synCsset) (.cv a)))
      (synWa (.classEq (.cv b) (synCima R (.cv a))) (synWbr (.cv b) (synCsset) (.cv a)))
      b p0011
  have p0013 := @gImaex R (.cv a) hyp_clos1ex_2 p0004
  have p0014 := @gBreq1 (.cv b) (synCima R (.cv a)) (.cv a) (synCsset)
  have p0015 := @gBrsset (synCima R (.cv a)) (.cv a) p0013 p0004
  have p0016 :=
    @gSyl6bb (.classEq (.cv b) (synCima R (.cv a)))
      (synWbr (.cv b) (synCsset) (.cv a))
      (synWbr (synCima R (.cv a)) (synCsset) (.cv a))
      (synWss (synCima R (.cv a)) (.cv a)) p0014 p0015
  have p0017 :=
    @gCeqsexv (synWbr (.cv b) (synCsset) (.cv a))
      (synWss (synCima R (.cv a)) (.cv a)) b (synCima R (.cv a)) dv_cache_0006
      dv_cache_0007 p0013 p0016
  have p0018 :=
    @gBitri
      (synWex b (synWa (synWbr (.cv a) (synCimage R) (.cv b))
          (synWbr (.cv b) (synCsset) (.cv a))))
      (synWex b (synWa (.classEq (.cv b) (synCima R (.cv a)))
          (synWbr (.cv b) (synCsset) (.cv a))))
      (synWss (synCima R (.cv a)) (.cv a)) p0012 p0017
  have p0019 :=
    @gBitri (synWbr (.cv a) (synCcom (synCsset) (synCimage R)) (.cv a))
      (synWex b (synWa (synWbr (.cv a) (synCimage R) (.cv b))
          (synWbr (.cv b) (synCsset) (.cv a))))
      (synWss (synCima R (.cv a)) (.cv a)) p0008 p0018
  have p0020 :=
    @gBitri (.classMem (.cv a) (synCfix (synCcom (synCsset) (synCimage R))))
      (synWbr (.cv a) (synCcom (synCsset) (synCimage R)) (.cv a))
      (synWss (synCima R (.cv a)) (.cv a)) p0007 p0019
  have p0021 :=
    @gAnbi12i (.classMem (.cv a) (synCima (synCsset) (synCsn S))) (synWss S (.cv a))
      (.classMem (.cv a) (synCfix (synCcom (synCsset) (synCimage R))))
      (synWss (synCima R (.cv a)) (.cv a)) p0006 p0020
  have p0022 :=
    @gBitri
      (.classMem (.cv a) (synCin (synCima (synCsset) (synCsn S))
          (synCfix (synCcom (synCsset) (synCimage R)))))
      (synWa (.classMem (.cv a) (synCima (synCsset) (synCsn S)))
        (.classMem (.cv a) (synCfix (synCcom (synCsset) (synCimage R)))))
      (synWa (synWss S (.cv a)) (synWss (synCima R (.cv a)) (.cv a))) p0001 p0021
  have p0023 :=
    @gEqabi (synWa (synWss S (.cv a)) (synWss (synCima R (.cv a)) (.cv a))) a
      (synCin (synCima (synCsset) (synCsn S))
        (synCfix (synCcom (synCsset) (synCimage R))))
      dv_cache_0008 p0022
  have p0024 := @gSsetex
  have p0025 := @gSnex S
  have p0026 := @gImaex (synCsset) (synCsn S) p0024 p0025
  have p0028 := @gImageex R hyp_clos1ex_2
  have p0029 := @gCoex (synCsset) (synCimage R) p0024 p0028
  have p0030 := @gFixex (synCcom (synCsset) (synCimage R)) p0029
  have p0031 :=
    @gInex (synCima (synCsset) (synCsn S))
      (synCfix (synCcom (synCsset) (synCimage R))) p0026 p0030
  have p0032 :=
    @gEqeltrri
      (synCin (synCima (synCsset) (synCsn S))
        (synCfix (synCcom (synCsset) (synCimage R))))
      (.cab a (synWa (synWss S (.cv a)) (synWss (synCima R (.cv a)) (.cv a))))
      (synCvv) p0023 p0031
  have p0033 :=
    @gIntex (.cab a (synWa (synWss S (.cv a)) (synWss (synCima R (.cv a)) (.cv a))))
      p0032
  have p0034 :=
    @gEqeltri (synCclos1 S R)
      (synCint (.cab a (synWa (synWss S (.cv a)) (synWss (synCima R (.cv a)) (.cv a)))))
      (synCvv) p0000 p0033
  exact p0034

/-- Checked nominal proof certificate identified upstream as `g_clos1exg`. -/
@[expose]
noncomputable def gClos1exg (R : Class) (S : Class) (V : Class) (W : Class) :
    Nominal.NPrf
      (.imp (synWa (.classMem S V) (.classMem R W)) (.classMem (synCclos1 S R) (synCvv))) :=
  by
  let proofSupport : Finset Var := R.fv ∪ S.fv ∪ V.fv ∪ W.fv
  let s : Var := freshVar proofSupport 0
  let r : Var := freshVar proofSupport 1
  have fresh_s : s ∉ proofSupport :=
    by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_s_not_S : s ∉ S.fv := by
    intro h
    exact
      fresh_s
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))
  have fresh_r : r ∉ proofSupport :=
    by
    change freshVar proofSupport 1 ∉ proofSupport
    exact freshVar_not_mem proofSupport 1
  have fresh_r_not_R : r ∉ R.fv := by
    intro h
    exact
      fresh_r
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (h))))
  have fresh_r_not_S : r ∉ S.fv := by
    intro h
    exact
      fresh_r
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))
  have fresh_s_ne_r : s ≠ r :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have dv_cache_0001 : s ∉ (S).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : s ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_s_not_S, not_false_eq_true])
  have dv_cache_0002 : r ∉ (S).fv :=
    by
    clear dv_cache_0001
    exact
      (by
        have compact_fv_not_mem_empty : r ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_r_not_S, not_false_eq_true])
  have dv_cache_0003 : r ∉ (R).fv :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact
      (by
        have compact_fv_not_mem_empty : r ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_r_not_R, not_false_eq_true])
  have dv_cache_0004 : r ∉ ((Wff.classMem (synCclos1 S R) (synCvv))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact
      (by
        have compact_fv_not_mem_empty : r ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cclos1,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv, Finset.mem_union,
          fresh_r_not_R, fresh_r_not_S, compact_fv_not_mem_empty, or_false,
          not_false_eq_true])
  have dv_cache_0005 : s ∉ ((Wff.classMem (synCclos1 S (.cv r)) (synCvv))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact
      (by
        have compact_fv_not_mem_empty : s ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cclos1,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv, Finset.mem_union,
          Finset.mem_singleton, fresh_s_ne_r, fresh_s_not_S, compact_fv_not_mem_empty,
          or_false, not_false_eq_true])
  have p0000 := @gClos1eq1 (.cv r) (.cv s) S
  have p0001 :=
    @gEleq1d (.classEq (.cv s) S) (synCclos1 (.cv s) (.cv r)) (synCclos1 S (.cv r))
      (synCvv) p0000
  have p0002 := @gClos1eq2 (.cv r) S R
  have p0003 :=
    @gEleq1d (.classEq (.cv r) R) (synCclos1 S (.cv r)) (synCclos1 S R) (synCvv) p0002
  have p0004 := @gVex s
  have p0005 := @gVex r
  have p0006 := @gClos1ex (.cv r) (.cv s) p0004 p0005
  have p0007 :=
    @gVtocl2g (.classMem (synCclos1 (.cv s) (.cv r)) (synCvv))
      (.classMem (synCclos1 S (.cv r)) (synCvv)) (.classMem (synCclos1 S R) (synCvv))
      s r S R V W dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      p0001 p0003 p0006
  exact p0007

/-- Checked nominal proof certificate identified upstream as `g_clos1base`. -/
@[expose]
noncomputable def gClos1base (C : Class) (R : Class) (S : Class)
    (hyp_clos1base_1 : Nominal.NPrf (.classEq C (synCclos1 S R))) :
    Nominal.NPrf (synWss S C) :=
  by
  let proofSupport : Finset Var := C.fv ∪ R.fv ∪ S.fv
  let a : Var := freshVar proofSupport 0
  have fresh_a : a ∉ proofSupport :=
    by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_a_not_R : a ∉ R.fv := by
    intro h
    exact fresh_a (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_a_not_S : a ∉ S.fv := by
    intro h
    exact fresh_a (Finset.mem_union_right _ (h))
  have dv_cache_0001 : a ∉ (S).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : a ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_a_not_S, not_false_eq_true])
  have dv_cache_0002 : a ∉ (R).fv :=
    by
    clear dv_cache_0001
    exact
      (by
        have compact_fv_not_mem_empty : a ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_a_not_R, not_false_eq_true])
  have p0000 := @gSsmin (synWss (synCima R (.cv a)) (.cv a)) a S dv_cache_0001
  have p0001 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominalDfClos1 R S a
      dv_cache_0002 dv_cache_0001
  have p0002 :=
    @gEqtr2i C (synCclos1 S R)
      (synCint (.cab a (synWa (synWss S (.cv a)) (synWss (synCima R (.cv a)) (.cv a)))))
      hyp_clos1base_1 p0001
  have p0003 :=
    @gSseqtri S
      (synCint (.cab a (synWa (synWss S (.cv a)) (synWss (synCima R (.cv a)) (.cv a)))))
      C p0000 p0002
  exact p0003

/-- Checked nominal proof certificate identified upstream as `g_clos1conn`. -/
@[expose]
noncomputable def gClos1conn (A : Class) (B : Class) (C : Class) (R : Class) (S : Class)
    (hyp_clos1base_1 : Nominal.NPrf (.classEq C (synCclos1 S R))) :
    Nominal.NPrf (.imp (synWa (.classMem A C) (synWbr A R B)) (.classMem B C)) :=
  by
  let proofSupport : Finset Var := A.fv ∪ B.fv ∪ C.fv ∪ R.fv ∪ S.fv
  let x : Var := freshVar proofSupport 0
  let y : Var := freshVar proofSupport 1
  let a : Var := freshVar proofSupport 2
  let z : Var := freshVar proofSupport 3
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
  have fresh_x_not_C : x ∉ C.fv := by
    intro h
    exact
      fresh_x
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))
  have fresh_x_not_R : x ∉ R.fv := by
    intro h
    exact fresh_x (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
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
  have fresh_y_not_C : y ∉ C.fv := by
    intro h
    exact
      fresh_y
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))
  have fresh_y_not_R : y ∉ R.fv := by
    intro h
    exact fresh_y (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_a : a ∉ proofSupport :=
    by
    change freshVar proofSupport 2 ∉ proofSupport
    exact freshVar_not_mem proofSupport 2
  have fresh_a_not_R : a ∉ R.fv := by
    intro h
    exact fresh_a (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_a_not_S : a ∉ S.fv := by
    intro h
    exact fresh_a (Finset.mem_union_right _ (h))
  have fresh_z : z ∉ proofSupport :=
    by
    change freshVar proofSupport 3 ∉ proofSupport
    exact freshVar_not_mem proofSupport 3
  have fresh_z_not_R : z ∉ R.fv := by
    intro h
    exact fresh_z (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_x_ne_y : x ≠ y :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have fresh_x_ne_a : x ≠ a :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 2
    exact freshVar_injective proofSupport (i := 0) (j := 2) (by decide)
  have fresh_a_ne_x : a ≠ x := Ne.symm fresh_x_ne_a
  have fresh_x_ne_z : x ≠ z :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 3
    exact freshVar_injective proofSupport (i := 0) (j := 3) (by decide)
  have fresh_z_ne_x : z ≠ x := Ne.symm fresh_x_ne_z
  have fresh_y_ne_a : y ≠ a :=
    by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 2
    exact freshVar_injective proofSupport (i := 1) (j := 2) (by decide)
  have fresh_a_ne_y : a ≠ y := Ne.symm fresh_y_ne_a
  have fresh_y_ne_z : y ≠ z :=
    by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 3
    exact freshVar_injective proofSupport (i := 1) (j := 3) (by decide)
  have fresh_z_ne_y : z ≠ y := Ne.symm fresh_y_ne_z
  have fresh_a_ne_z : a ≠ z :=
    by
    change freshVar proofSupport 2 ≠ freshVar proofSupport 3
    exact freshVar_injective proofSupport (i := 2) (j := 3) (by decide)
  have fresh_z_ne_a : z ≠ a := Ne.symm fresh_a_ne_z
  have dv_cache_0001 : z ∉ ((Class.cv x)).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_z_ne_x, not_false_eq_true])
  have dv_cache_0002 : z ∉ ((Class.cv a)).fv :=
    by
    clear dv_cache_0001
    exact
      (by
        have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_z_ne_a, not_false_eq_true])
  have dv_cache_0003 : z ∉ ((synWbr (.cv x) R (.cv y))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact
      (by
        have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, fresh_z_ne_x, fresh_z_ne_y, fresh_z_not_R, or_false,
          not_false_eq_true])
  have dv_cache_0004 : z ∉ ((Class.cv y)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact
      (by
        have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_z_ne_y, not_false_eq_true])
  have dv_cache_0005 : z ∉ (R).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact
      (by
        have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_z_not_R, not_false_eq_true])
  have dv_cache_0006 : a ∉ ((synWbr (.cv x) R (.cv y))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact
      (by
        have compact_fv_not_mem_empty : a ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, fresh_a_ne_x, fresh_a_ne_y, fresh_a_not_R, or_false,
          not_false_eq_true])
  have dv_cache_0007 : a ∉ (R).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006
    exact
      (by
        have compact_fv_not_mem_empty : a ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_a_not_R, not_false_eq_true])
  have dv_cache_0008 : a ∉ (S).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007
    exact
      (by
        have compact_fv_not_mem_empty : a ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_a_not_S, not_false_eq_true])
  have dv_cache_0009 : a ∉ ((Class.cv x)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008
    exact
      (by
        have compact_fv_not_mem_empty : a ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_a_ne_x, not_false_eq_true])
  have dv_cache_0010 : a ∉ ((Class.cv y)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009
    exact
      (by
        have compact_fv_not_mem_empty : a ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_a_ne_y, not_false_eq_true])
  have dv_cache_0011 : x ∉ (A).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_x_not_A, not_false_eq_true])
  have dv_cache_0012 : y ∉ (A).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_y_not_A, not_false_eq_true])
  have dv_cache_0013 : y ∉ (B).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_y_not_B, not_false_eq_true])
  have dv_cache_0014 :
    y ∉ ((Wff.imp (synWa (.classMem A C) (synWbr A R B)) (.classMem B C))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr, Finset.mem_union,
          fresh_y_not_A, fresh_y_not_C, fresh_y_not_B, fresh_y_not_R, or_false,
          not_false_eq_true])
  have dv_cache_0015 :
    x ∉
      ((Wff.imp (synWa (.classMem A C) (synWbr A R (.cv y))) (.classMem (.cv y) C))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, fresh_x_not_A, fresh_x_not_C, fresh_x_ne_y, fresh_x_not_R,
          or_false, not_false_eq_true])
  have p0000 := @gBrex A B R
  have p0001 :=
    @gAdantl (synWbr A R B) (synWa (.classMem A (synCvv)) (.classMem B (synCvv)))
      (.classMem A C) p0000
  have p0002 := @gEleq1 (.cv x) A C
  have p0003 := @gBreq1 (.cv x) A (.cv y) R
  have p0004 :=
    @gAnbi12d (.classEq (.cv x) A) (.classMem (.cv x) C) (.classMem A C)
      (synWbr (.cv x) R (.cv y)) (synWbr A R (.cv y)) p0002 p0003
  have p0005 :=
    @gImbi1d (.classEq (.cv x) A)
      (synWa (.classMem (.cv x) C) (synWbr (.cv x) R (.cv y)))
      (synWa (.classMem A C) (synWbr A R (.cv y))) (.classMem (.cv y) C) p0004
  have p0006 := @gBreq2 (.cv y) B A R
  have p0007 :=
    @gAnbi2d (.classEq (.cv y) B) (synWbr A R (.cv y)) (synWbr A R B) (.classMem A C)
      p0006
  have p0008 := @gEleq1 (.cv y) B C
  have p0009 :=
    @gImbi12d (.classEq (.cv y) B) (synWa (.classMem A C) (synWbr A R (.cv y)))
      (synWa (.classMem A C) (synWbr A R B)) (.classMem (.cv y) C) (.classMem B C) p0007
      p0008
  have p0010 := @gBreq1 (.cv z) (.cv x) (.cv y) R
  have p0011 :=
    @gRspcev (synWbr (.cv z) R (.cv y)) (synWbr (.cv x) R (.cv y)) z (.cv x) (.cv a)
      dv_cache_0001 dv_cache_0002 dv_cache_0003 p0010
  have p0012 := @gElima z (.cv y) R (.cv a) dv_cache_0004 dv_cache_0005 dv_cache_0002
  have p0013_e00_recanon :
    Nominal.NPrf
      (.imp (synWa (.objMem x a) (synWbr (.cv x) R (.cv y)))
        (synWrex z (.cv a) (synWbr (.cv z) R (.cv y)))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold synWa synWbr synCop synCun synCnin synWnan synCcompl synWrex
          synWex synCphi
        simp (config :=
          { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_class_cv]
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · apply Nominal.RecanonTransportDev.TRecanonWff.neg
          apply Nominal.RecanonTransportDev.TRecanonWff.imp
          · exact Nominal.RecanonTransportDev.TRecanonWff.classMem_objMem _ _
          · exact Nominal.RecanonTransportDev.TRecanonWff.same _
        · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0011
  have p0013 :=
    @gSylibr (synWa (.objMem x a) (synWbr (.cv x) R (.cv y)))
      (synWrex z (.cv a) (synWbr (.cv z) R (.cv y)))
      (.classMem (.cv y) (synCima R (.cv a))) p0013_e00_recanon p0012
  have p0014 :=
    @gAncoms (.objMem x a) (synWbr (.cv x) R (.cv y))
      (.classMem (.cv y) (synCima R (.cv a))) p0013
  have p0015 := @gSsel (synCima R (.cv a)) (.cv a) (.cv y)
  have p0016_e01_recanon :
    Nominal.NPrf
      (.imp (synWss (synCima R (.cv a)) (.cv a))
        (.imp (.classMem (.cv y) (synCima R (.cv a))) (.objMem y a))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold synWss synCin synCcompl synCnin synWnan synWa synCima synWrex
          synWex synWbr synCop synCun
        simp (config :=
          { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_class_cv]
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · exact Nominal.RecanonTransportDev.TRecanonWff.same _
        · apply Nominal.RecanonTransportDev.TRecanonWff.imp
          · exact Nominal.RecanonTransportDev.TRecanonWff.same _
          · exact Nominal.RecanonTransportDev.TRecanonWff.classMem_objMem _ _)
      p0015
  have p0016 :=
    @gSyl5 (synWa (synWbr (.cv x) R (.cv y)) (.objMem x a))
      (.classMem (.cv y) (synCima R (.cv a))) (synWss (synCima R (.cv a)) (.cv a))
      (.objMem y a) p0014 p0016_e01_recanon
  have p0017 :=
    @gExp3a (synWss (synCima R (.cv a)) (.cv a)) (synWbr (.cv x) R (.cv y))
      (.objMem x a) (.objMem y a) p0016
  have p0018 :=
    @gCom12 (synWss (synCima R (.cv a)) (.cv a)) (synWbr (.cv x) R (.cv y))
      (.imp (.objMem x a) (.objMem y a)) p0017
  have p0019 :=
    @gAdantld (synWbr (.cv x) R (.cv y)) (synWss (synCima R (.cv a)) (.cv a))
      (.imp (.objMem x a) (.objMem y a)) (synWss S (.cv a)) p0018
  have p0020 :=
    @gA2d (synWbr (.cv x) R (.cv y))
      (synWa (synWss S (.cv a)) (synWss (synCima R (.cv a)) (.cv a))) (.objMem x a)
      (.objMem y a) p0019
  have p0021 :=
    @gAlimdv (synWbr (.cv x) R (.cv y))
      (.imp (synWa (synWss S (.cv a)) (synWss (synCima R (.cv a)) (.cv a))) (.objMem x a))
      (.imp (synWa (synWss S (.cv a)) (synWss (synCima R (.cv a)) (.cv a))) (.objMem y a))
      a dv_cache_0006 p0020
  have p0022 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominalDfClos1 R S a
      dv_cache_0007 dv_cache_0008
  have p0023 :=
    @gEqtri C (synCclos1 S R)
      (synCint (.cab a (synWa (synWss S (.cv a)) (synWss (synCima R (.cv a)) (.cv a)))))
      hyp_clos1base_1 p0022
  have p0024 :=
    @gEleq2i C
      (synCint (.cab a (synWa (synWss S (.cv a)) (synWss (synCima R (.cv a)) (.cv a)))))
      (.cv x) p0023
  have p0025 := @gVex x
  have p0026 :=
    @gElintab (synWa (synWss S (.cv a)) (synWss (synCima R (.cv a)) (.cv a))) a
      (.cv x) dv_cache_0009 p0025
  have p0027_e01_recanon :
    Nominal.NPrf
      (synWb (.classMem (.cv x) (synCint
            (.cab a (synWa (synWss S (.cv a)) (synWss (synCima R (.cv a)) (.cv a))))))
        (.all a (.imp (synWa (synWss S (.cv a)) (synWss (synCima R (.cv a)) (.cv a)))
            (.objMem x a)))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold synWb synCint synWa synWss synCin synCcompl synCnin synWnan
        simp (config :=
          { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CoreFVSimp.fv_class_cab,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cima]
        apply Nominal.RecanonTransportDev.TRecanonWff.neg
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · apply Nominal.RecanonTransportDev.TRecanonWff.imp
          · exact Nominal.RecanonTransportDev.TRecanonWff.same _
          · apply Nominal.RecanonTransportDev.TRecanonWff.all
            apply Nominal.RecanonTransportDev.TRecanonWff.imp
            · exact Nominal.RecanonTransportDev.TRecanonWff.same _
            · exact Nominal.RecanonTransportDev.TRecanonWff.classMem_objMem _ _
        · apply Nominal.RecanonTransportDev.TRecanonWff.neg
          apply Nominal.RecanonTransportDev.TRecanonWff.imp
          · apply Nominal.RecanonTransportDev.TRecanonWff.all
            apply Nominal.RecanonTransportDev.TRecanonWff.imp
            · exact Nominal.RecanonTransportDev.TRecanonWff.same _
            · exact Nominal.RecanonTransportDev.TRecanonWff.classMem_objMem _ _
          · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0026
  have p0027 :=
    @gBitri (.classMem (.cv x) C)
      (.classMem (.cv x) (synCint
          (.cab a (synWa (synWss S (.cv a)) (synWss (synCima R (.cv a)) (.cv a))))))
      (.all a (.imp (synWa (synWss S (.cv a)) (synWss (synCima R (.cv a)) (.cv a)))
          (.objMem x a)))
      p0024 p0027_e01_recanon
  have p0028 :=
    @gEleq2i C
      (synCint (.cab a (synWa (synWss S (.cv a)) (synWss (synCima R (.cv a)) (.cv a)))))
      (.cv y) p0023
  have p0029 := @gVex y
  have p0030 :=
    @gElintab (synWa (synWss S (.cv a)) (synWss (synCima R (.cv a)) (.cv a))) a
      (.cv y) dv_cache_0010 p0029
  have p0031_e01_recanon :
    Nominal.NPrf
      (synWb (.classMem (.cv y) (synCint
            (.cab a (synWa (synWss S (.cv a)) (synWss (synCima R (.cv a)) (.cv a))))))
        (.all a (.imp (synWa (synWss S (.cv a)) (synWss (synCima R (.cv a)) (.cv a)))
            (.objMem y a)))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold synWb synCint synWa synWss synCin synCcompl synCnin synWnan
        simp (config :=
          { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CoreFVSimp.fv_class_cab,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cima]
        apply Nominal.RecanonTransportDev.TRecanonWff.neg
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · apply Nominal.RecanonTransportDev.TRecanonWff.imp
          · exact Nominal.RecanonTransportDev.TRecanonWff.same _
          · apply Nominal.RecanonTransportDev.TRecanonWff.all
            apply Nominal.RecanonTransportDev.TRecanonWff.imp
            · exact Nominal.RecanonTransportDev.TRecanonWff.same _
            · exact Nominal.RecanonTransportDev.TRecanonWff.classMem_objMem _ _
        · apply Nominal.RecanonTransportDev.TRecanonWff.neg
          apply Nominal.RecanonTransportDev.TRecanonWff.imp
          · apply Nominal.RecanonTransportDev.TRecanonWff.all
            apply Nominal.RecanonTransportDev.TRecanonWff.imp
            · exact Nominal.RecanonTransportDev.TRecanonWff.same _
            · exact Nominal.RecanonTransportDev.TRecanonWff.classMem_objMem _ _
          · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0030
  have p0031 :=
    @gBitri (.classMem (.cv y) C)
      (.classMem (.cv y) (synCint
          (.cab a (synWa (synWss S (.cv a)) (synWss (synCima R (.cv a)) (.cv a))))))
      (.all a (.imp (synWa (synWss S (.cv a)) (synWss (synCima R (.cv a)) (.cv a)))
          (.objMem y a)))
      p0028 p0031_e01_recanon
  have p0032 :=
    @gN3imtr4g (synWbr (.cv x) R (.cv y))
      (.all a (.imp (synWa (synWss S (.cv a)) (synWss (synCima R (.cv a)) (.cv a)))
          (.objMem x a)))
      (.all a (.imp (synWa (synWss S (.cv a)) (synWss (synCima R (.cv a)) (.cv a)))
          (.objMem y a)))
      (.classMem (.cv x) C) (.classMem (.cv y) C) p0021 p0027 p0031
  have p0033 :=
    @gImpcom (synWbr (.cv x) R (.cv y)) (.classMem (.cv x) C) (.classMem (.cv y) C)
      p0032
  have p0034 :=
    @gVtocl2g
      (.imp (synWa (.classMem (.cv x) C) (synWbr (.cv x) R (.cv y))) (.classMem (.cv y) C))
      (.imp (synWa (.classMem A C) (synWbr A R (.cv y))) (.classMem (.cv y) C))
      (.imp (synWa (.classMem A C) (synWbr A R B)) (.classMem B C)) x y A B (synCvv)
      (synCvv) dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015
      p0005 p0009 p0033
  have p0035 :=
    @gMpcom (synWa (.classMem A (synCvv)) (.classMem B (synCvv)))
      (synWa (.classMem A C) (synWbr A R B)) (.classMem B C) p0001 p0034
  exact p0035


end NFChoice.DirectNominalPrf.WPPReplay

end
