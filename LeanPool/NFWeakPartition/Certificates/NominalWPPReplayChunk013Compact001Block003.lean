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

@[expose]
noncomputable def g_pw1fnex : Nominal.NPrf (.classMem (syn_cpw1fn) (syn_cvv)) :=
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
  have dv_cache_0001 : y ∉ ((syn_cop (syn_csn (syn_csn (.cv t))) (.cv x))).fv := by
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
  have dv_cache_0002 : y ∉ ((syn_ctxp (syn_csi (syn_ccnv (syn_csset))) (syn_csset))).fv :=
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
  have dv_cache_0005 : t ∉ ((syn_cop (syn_csn (.cv y)) (.cv x))).fv :=
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
      ((syn_ctxp (syn_cid) (syn_cima (syn_ctxp (syn_csi (syn_ccnv (syn_csset))) (syn_csset))
            (syn_c1c)))).fv :=
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
  have dv_cache_0008 : t ∉ ((syn_cuni (.cv x))).fv :=
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
  have dv_cache_0009 : x ∉ ((syn_c1c)).fv :=
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
      ((syn_cima (syn_ctxp (syn_cid)
            (syn_cima (syn_ctxp (syn_csi (syn_ccnv (syn_csset))) (syn_csset)) (syn_c1c)))
          (syn_cpw1 (syn_c1c)))).fv :=
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
      ((syn_cima (syn_ctxp (syn_cid)
            (syn_cima (syn_ctxp (syn_csi (syn_ccnv (syn_csset))) (syn_csset)) (syn_c1c)))
          (syn_cpw1 (syn_c1c)))).fv :=
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
  have dv_cache_0012 : y ∉ ((syn_cpw1 (syn_cuni (.cv x)))).fv :=
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
  have p0000 := NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominal_df_pw1fn x
  have p0001 :=
    @g_oteltxp (syn_csn (syn_csn (.cv t))) (syn_csn (.cv y)) (.cv x) (syn_cid)
      (syn_cima (syn_ctxp (syn_csi (syn_ccnv (syn_csset))) (syn_csset)) (syn_c1c))
  have p0002 := @g_snex (.cv y)
  have p0003 := @g_ideq (syn_csn (syn_csn (.cv t))) (syn_csn (.cv y)) p0002
  have p0004 :=
    (Nominal.biimpRefl (syn_wbr (syn_csn (syn_csn (.cv t))) (syn_cid) (syn_csn (.cv y))))
  have p0005 := @g_eqcom (syn_csn (syn_csn (.cv t))) (syn_csn (.cv y))
  have p0006 := @g_vex y
  have p0007 := @g_sneqb (.cv y) (syn_csn (.cv t)) p0006
  have p0008 :=
    @g_bitri (.classEq (syn_csn (syn_csn (.cv t))) (syn_csn (.cv y)))
      (.classEq (syn_csn (.cv y)) (syn_csn (syn_csn (.cv t))))
      (.classEq (.cv y) (syn_csn (.cv t))) p0005 p0007
  have p0009 :=
    @g_n_3bitr3i (syn_wbr (syn_csn (syn_csn (.cv t))) (syn_cid) (syn_csn (.cv y)))
      (.classEq (syn_csn (syn_csn (.cv t))) (syn_csn (.cv y)))
      (.classMem (syn_cop (syn_csn (syn_csn (.cv t))) (syn_csn (.cv y))) (syn_cid))
      (.classEq (.cv y) (syn_csn (.cv t))) p0003 p0004 p0008
  have p0010 :=
    @g_oteltxp (syn_csn (.cv y)) (syn_csn (syn_csn (.cv t))) (.cv x)
      (syn_csi (syn_ccnv (syn_csset))) (syn_csset)
  have p0011 := @g_snex (.cv t)
  have p0012 := @g_brsnsi (.cv y) (syn_csn (.cv t)) (syn_ccnv (syn_csset)) p0006 p0011
  have p0013 :=
    (Nominal.biimpRefl (syn_wbr (syn_csn (.cv y)) (syn_csi (syn_ccnv (syn_csset)))
        (syn_csn (syn_csn (.cv t)))))
  have p0014 := @g_brcnv (.cv y) (syn_csn (.cv t)) (syn_csset)
  have p0015 := @g_vex t
  have p0016 := @g_brssetsn (.cv t) (.cv y) p0015 p0006
  have p0017_e01_recanon :
    Nominal.NPrf (syn_wb (syn_wbr (syn_csn (.cv t)) (syn_csset) (.cv y)) (.objMem t y)) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wb syn_wbr syn_cop syn_cun syn_cnin syn_wnan syn_wa syn_ccompl syn_wrex
          syn_wex syn_cphi syn_csn syn_csset syn_copab syn_wss syn_cin
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
    @g_bitri (syn_wbr (.cv y) (syn_ccnv (syn_csset)) (syn_csn (.cv t)))
      (syn_wbr (syn_csn (.cv t)) (syn_csset) (.cv y)) (.objMem t y) p0014
      p0017_e01_recanon
  have p0018 :=
    @g_n_3bitr3i
      (syn_wbr (syn_csn (.cv y)) (syn_csi (syn_ccnv (syn_csset))) (syn_csn (syn_csn (.cv t))))
      (syn_wbr (.cv y) (syn_ccnv (syn_csset)) (syn_csn (.cv t)))
      (.classMem (syn_cop (syn_csn (.cv y)) (syn_csn (syn_csn (.cv t))))
        (syn_csi (syn_ccnv (syn_csset))))
      (.objMem t y) p0012 p0013 p0017
  have p0019 := @g_vex x
  have p0020 := @g_opelssetsn (.cv y) (.cv x) p0006 p0019
  have p0021_e01_recanon :
    Nominal.NPrf
      (syn_wb (.classMem (syn_cop (syn_csn (.cv y)) (.cv x)) (syn_csset)) (.objMem y x)) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wb syn_cop syn_cun syn_cnin syn_wnan syn_wa syn_ccompl syn_wrex syn_wex
          syn_cphi syn_csn syn_csset syn_copab syn_wss syn_cin
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
    @g_anbi12i
      (.classMem (syn_cop (syn_csn (.cv y)) (syn_csn (syn_csn (.cv t))))
        (syn_csi (syn_ccnv (syn_csset))))
      (.objMem t y) (.classMem (syn_cop (syn_csn (.cv y)) (.cv x)) (syn_csset))
      (.objMem y x) p0018 p0021_e01_recanon
  have p0022 :=
    @g_bitri
      (.classMem (syn_cop (syn_csn (.cv y)) (syn_cop (syn_csn (syn_csn (.cv t))) (.cv x)))
        (syn_ctxp (syn_csi (syn_ccnv (syn_csset))) (syn_csset)))
      (syn_wa (.classMem (syn_cop (syn_csn (.cv y)) (syn_csn (syn_csn (.cv t))))
          (syn_csi (syn_ccnv (syn_csset))))
        (.classMem (syn_cop (syn_csn (.cv y)) (.cv x)) (syn_csset)))
      (syn_wa (.objMem t y) (.objMem y x)) p0010 p0021
  have p0023 :=
    @g_exbii
      (.classMem (syn_cop (syn_csn (.cv y)) (syn_cop (syn_csn (syn_csn (.cv t))) (.cv x)))
        (syn_ctxp (syn_csi (syn_ccnv (syn_csset))) (syn_csset)))
      (syn_wa (.objMem t y) (.objMem y x)) y p0022
  have p0024 :=
    @g_elima1c y (syn_cop (syn_csn (syn_csn (.cv t))) (.cv x))
      (syn_ctxp (syn_csi (syn_ccnv (syn_csset))) (syn_csset)) dv_cache_0001 dv_cache_0002
  have p0025 := @g_eluni y (.cv t) (.cv x) dv_cache_0003 dv_cache_0004
  have p0026_e02_recanon :
    Nominal.NPrf
      (syn_wb (.classMem (.cv t) (syn_cuni (.cv x)))
        (syn_wex y (syn_wa (.objMem t y) (.objMem y x)))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wb syn_cuni syn_wex syn_wa
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
    @g_n_3bitr4i
      (syn_wex y (.classMem
          (syn_cop (syn_csn (.cv y)) (syn_cop (syn_csn (syn_csn (.cv t))) (.cv x)))
          (syn_ctxp (syn_csi (syn_ccnv (syn_csset))) (syn_csset))))
      (syn_wex y (syn_wa (.objMem t y) (.objMem y x)))
      (.classMem (syn_cop (syn_csn (syn_csn (.cv t))) (.cv x))
        (syn_cima (syn_ctxp (syn_csi (syn_ccnv (syn_csset))) (syn_csset)) (syn_c1c)))
      (.classMem (.cv t) (syn_cuni (.cv x))) p0023 p0024 p0026_e02_recanon
  have p0027 :=
    @g_anbi12i
      (.classMem (syn_cop (syn_csn (syn_csn (.cv t))) (syn_csn (.cv y))) (syn_cid))
      (.classEq (.cv y) (syn_csn (.cv t)))
      (.classMem (syn_cop (syn_csn (syn_csn (.cv t))) (.cv x))
        (syn_cima (syn_ctxp (syn_csi (syn_ccnv (syn_csset))) (syn_csset)) (syn_c1c)))
      (.classMem (.cv t) (syn_cuni (.cv x))) p0009 p0026
  have p0028 :=
    @g_bitri
      (.classMem (syn_cop (syn_csn (syn_csn (.cv t))) (syn_cop (syn_csn (.cv y)) (.cv x)))
        (syn_ctxp (syn_cid)
          (syn_cima (syn_ctxp (syn_csi (syn_ccnv (syn_csset))) (syn_csset)) (syn_c1c))))
      (syn_wa (.classMem (syn_cop (syn_csn (syn_csn (.cv t))) (syn_csn (.cv y))) (syn_cid))
        (.classMem (syn_cop (syn_csn (syn_csn (.cv t))) (.cv x))
          (syn_cima (syn_ctxp (syn_csi (syn_ccnv (syn_csset))) (syn_csset)) (syn_c1c))))
      (syn_wa (.classEq (.cv y) (syn_csn (.cv t))) (.classMem (.cv t) (syn_cuni (.cv x))))
      p0001 p0027
  have p0029 :=
    @g_ancom (.classEq (.cv y) (syn_csn (.cv t))) (.classMem (.cv t) (syn_cuni (.cv x)))
  have p0030 :=
    @g_bitri
      (.classMem (syn_cop (syn_csn (syn_csn (.cv t))) (syn_cop (syn_csn (.cv y)) (.cv x)))
        (syn_ctxp (syn_cid)
          (syn_cima (syn_ctxp (syn_csi (syn_ccnv (syn_csset))) (syn_csset)) (syn_c1c))))
      (syn_wa (.classEq (.cv y) (syn_csn (.cv t))) (.classMem (.cv t) (syn_cuni (.cv x))))
      (syn_wa (.classMem (.cv t) (syn_cuni (.cv x))) (.classEq (.cv y) (syn_csn (.cv t))))
      p0028 p0029
  have p0031 :=
    @g_exbii
      (.classMem (syn_cop (syn_csn (syn_csn (.cv t))) (syn_cop (syn_csn (.cv y)) (.cv x)))
        (syn_ctxp (syn_cid)
          (syn_cima (syn_ctxp (syn_csi (syn_ccnv (syn_csset))) (syn_csset)) (syn_c1c))))
      (syn_wa (.classMem (.cv t) (syn_cuni (.cv x))) (.classEq (.cv y) (syn_csn (.cv t))))
      t p0030
  have p0032 :=
    @g_elimapw11c t (syn_cop (syn_csn (.cv y)) (.cv x))
      (syn_ctxp (syn_cid)
        (syn_cima (syn_ctxp (syn_csi (syn_ccnv (syn_csset))) (syn_csset)) (syn_c1c)))
      dv_cache_0005 dv_cache_0006
  have p0033 := @g_elpw1 t (.cv y) (syn_cuni (.cv x)) dv_cache_0007 dv_cache_0008
  have p0034 :=
    (Nominal.biimpRefl (syn_wrex t (syn_cuni (.cv x)) (.classEq (.cv y) (syn_csn (.cv t)))))
  have p0035 :=
    @g_bitri (.classMem (.cv y) (syn_cpw1 (syn_cuni (.cv x))))
      (syn_wrex t (syn_cuni (.cv x)) (.classEq (.cv y) (syn_csn (.cv t))))
      (syn_wex t (syn_wa (.classMem (.cv t) (syn_cuni (.cv x)))
          (.classEq (.cv y) (syn_csn (.cv t)))))
      p0033 p0034
  have p0036 :=
    @g_n_3bitr4i
      (syn_wex t (.classMem
          (syn_cop (syn_csn (syn_csn (.cv t))) (syn_cop (syn_csn (.cv y)) (.cv x)))
          (syn_ctxp (syn_cid) (syn_cima (syn_ctxp (syn_csi (syn_ccnv (syn_csset))) (syn_csset))
              (syn_c1c)))))
      (syn_wex t (syn_wa (.classMem (.cv t) (syn_cuni (.cv x)))
          (.classEq (.cv y) (syn_csn (.cv t)))))
      (.classMem (syn_cop (syn_csn (.cv y)) (.cv x)) (syn_cima (syn_ctxp (syn_cid)
            (syn_cima (syn_ctxp (syn_csi (syn_ccnv (syn_csset))) (syn_csset)) (syn_c1c)))
          (syn_cpw1 (syn_c1c))))
      (.classMem (.cv y) (syn_cpw1 (syn_cuni (.cv x)))) p0031 p0032 p0035
  have p0037 :=
    @g_releqmpt x y (syn_c1c)
      (syn_cima (syn_ctxp (syn_cid)
          (syn_cima (syn_ctxp (syn_csi (syn_ccnv (syn_csset))) (syn_csset)) (syn_c1c)))
        (syn_cpw1 (syn_c1c)))
      (syn_cpw1 (syn_cuni (.cv x))) dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 p0036
  have p0038 :=
    @g_eqtr4i (syn_cpw1fn) (syn_cmpt x (syn_c1c) (syn_cpw1 (syn_cuni (.cv x))))
      (syn_cin (syn_cxp (syn_c1c) (syn_cvv)) (syn_ccnv (syn_ccompl (syn_cima
              (syn_csymdif (syn_cins3 (syn_csset)) (syn_cins2 (syn_cima (syn_ctxp (syn_cid)
                      (syn_cima (syn_ctxp (syn_csi (syn_ccnv (syn_csset))) (syn_csset))
                        (syn_c1c))) (syn_cpw1 (syn_c1c))))) (syn_c1c)))))
      p0000 p0037
  have p0039 := @g_n_1cex
  have p0040 := @g_idex
  have p0041 := @g_ssetex
  have p0042 := @g_cnvex (syn_csset) p0041
  have p0043 := @g_siex (syn_ccnv (syn_csset)) p0042
  have p0045 := @g_txpex (syn_csi (syn_ccnv (syn_csset))) (syn_csset) p0043 p0041
  have p0047 :=
    @g_imaex (syn_ctxp (syn_csi (syn_ccnv (syn_csset))) (syn_csset)) (syn_c1c) p0045 p0039
  have p0048 :=
    @g_txpex (syn_cid)
      (syn_cima (syn_ctxp (syn_csi (syn_ccnv (syn_csset))) (syn_csset)) (syn_c1c)) p0040
      p0047
  have p0050 := @g_pw1ex (syn_c1c) p0039
  have p0051 :=
    @g_imaex
      (syn_ctxp (syn_cid)
        (syn_cima (syn_ctxp (syn_csi (syn_ccnv (syn_csset))) (syn_csset)) (syn_c1c)))
      (syn_cpw1 (syn_c1c)) p0048 p0050
  have p0052 :=
    @g_mptexlem (syn_c1c)
      (syn_cima (syn_ctxp (syn_cid)
          (syn_cima (syn_ctxp (syn_csi (syn_ccnv (syn_csset))) (syn_csset)) (syn_c1c)))
        (syn_cpw1 (syn_c1c)))
      p0039 p0051
  have p0053 :=
    @g_eqeltri (syn_cpw1fn)
      (syn_cin (syn_cxp (syn_c1c) (syn_cvv)) (syn_ccnv (syn_ccompl (syn_cima
              (syn_csymdif (syn_cins3 (syn_csset)) (syn_cins2 (syn_cima (syn_ctxp (syn_cid)
                      (syn_cima (syn_ctxp (syn_csi (syn_ccnv (syn_csset))) (syn_csset))
                        (syn_c1c))) (syn_cpw1 (syn_c1c))))) (syn_c1c)))))
      (syn_cvv) p0038 p0052
  exact p0053

@[expose]
noncomputable def g_fnpw1fn : Nominal.NPrf (syn_wfn (syn_cpw1fn) (syn_c1c)) :=
  by
  let proofSupport : Finset Var := (∅ : Finset Var)
  let x : Var := freshVar proofSupport 0
  have dv_cache_0001 : x ∉ ((syn_c1c)).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c,
          compact_fv_not_mem_empty, not_false_eq_true])
  have p0000 := NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominal_df_pw1fn x
  have p0001 :=
    @g_fnmpt x (syn_c1c) (syn_cpw1 (syn_cuni (.cv x))) (syn_cpw1fn) (syn_cvv)
      dv_cache_0001 p0000
  have p0002 := @g_vex x
  have p0003 := @g_uniex (.cv x) p0002
  have p0004 := @g_pw1ex (syn_cuni (.cv x)) p0003
  have p0005 :=
    @g_a1i (.classMem (syn_cpw1 (syn_cuni (.cv x))) (syn_cvv))
      (.classMem (.cv x) (syn_c1c)) p0004
  have p0006 :=
    @g_mprg (.classMem (syn_cpw1 (syn_cuni (.cv x))) (syn_cvv))
      (syn_wfn (syn_cpw1fn) (syn_c1c)) x (syn_c1c) p0001 p0005
  exact p0006

@[expose]
noncomputable def g_brpw1fn (A : Class) (B : Class)
    (hyp_brpw1fn_1 : Nominal.NPrf (.classMem A (syn_cvv))) :
    Nominal.NPrf
      (syn_wb (syn_wbr (syn_csn A) (syn_cpw1fn) B) (.classEq B (syn_cpw1 A))) :=
  by
  have p0000 := @g_pw1fnval A hyp_brpw1fn_1
  have p0001 := @g_eqeq1i (syn_cfv (syn_cpw1fn) (syn_csn A)) (syn_cpw1 A) B p0000
  have p0002 := @g_fnpw1fn
  have p0003 := @g_snel1c A hyp_brpw1fn_1
  have p0004 := @g_fnbrfvb (syn_c1c) (syn_csn A) B (syn_cpw1fn)
  have p0005 :=
    @g_mp2an (syn_wfn (syn_cpw1fn) (syn_c1c)) (.classMem (syn_csn A) (syn_c1c))
      (syn_wb (.classEq (syn_cfv (syn_cpw1fn) (syn_csn A)) B)
        (syn_wbr (syn_csn A) (syn_cpw1fn) B))
      p0002 p0003 p0004
  have p0006 := @g_eqcom (syn_cpw1 A) B
  have p0007 :=
    @g_n_3bitr3i (.classEq (syn_cfv (syn_cpw1fn) (syn_csn A)) B) (.classEq (syn_cpw1 A) B)
      (syn_wbr (syn_csn A) (syn_cpw1fn) B) (.classEq B (syn_cpw1 A)) p0001 p0005 p0006
  exact p0007

@[expose]
noncomputable def g_pw1fnf1o :
    Nominal.NPrf (syn_wf1o (syn_cpw1fn) (syn_c1c) (syn_cpw (syn_c1c))) :=
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
  have dv_cache_0001 : y ∉ ((syn_c1c)).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c,
          compact_fv_not_mem_empty, not_false_eq_true])
  have dv_cache_0002 : y ∉ ((syn_cpw1 (syn_cuni (.cv x)))).fv :=
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
  have dv_cache_0005 : z ∉ ((syn_cvv)).fv :=
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
  have dv_cache_0007 : z ∉ ((Wff.classEq (.cv y) (syn_cpw1 (syn_cuni (.cv x))))).fv :=
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
  have dv_cache_0008 : x ∉ ((syn_csn (.cv z))).fv :=
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
  have dv_cache_0009 : x ∉ ((Wff.classEq (.cv y) (syn_cpw1 (.cv z)))).fv :=
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
  have dv_cache_0010 : y ∉ ((syn_cpw (syn_c1c))).fv :=
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
  have dv_cache_0013 : b ∉ ((Wff.classEq (.cv x) (syn_csn (.cv a)))).fv :=
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
  have dv_cache_0014 : a ∉ ((Wff.classEq (.cv y) (syn_csn (.cv b)))).fv :=
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
      ((Wff.imp (.classEq (syn_cfv (syn_cpw1fn) (.cv x)) (syn_cfv (syn_cpw1fn) (.cv y)))
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
      ((Wff.imp (.classEq (syn_cfv (syn_cpw1fn) (.cv x)) (syn_cfv (syn_cpw1fn) (.cv y)))
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
  have dv_cache_0017 : x ∉ ((syn_c1c)).fv :=
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
  have dv_cache_0018 : x ∉ ((syn_cpw1fn)).fv :=
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
  have dv_cache_0019 : y ∉ ((syn_cpw1fn)).fv :=
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
  have p0000 := @g_fnpw1fn
  have p0001 := NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominal_df_pw1fn x
  have p0002 :=
    @g_rnmpt x y (syn_c1c) (syn_cpw1 (syn_cuni (.cv x))) (syn_cpw1fn) dv_cache_0001
      dv_cache_0002 dv_cache_0003 p0001
  have p0003 := @g_vex y
  have p0004 := @g_sspw1 z (.cv y) (syn_cvv) dv_cache_0004 dv_cache_0005 p0003
  have p0005 := @g_df1c2
  have p0006 := @g_sseq2i (syn_c1c) (syn_cpw1 (syn_cvv)) (.cv y) p0005
  have p0007 := @g_ssv (.cv z)
  have p0008 :=
    @g_biantrur (syn_wss (.cv z) (syn_cvv)) (.classEq (.cv y) (syn_cpw1 (.cv z))) p0007
  have p0009 :=
    @g_exbii (.classEq (.cv y) (syn_cpw1 (.cv z)))
      (syn_wa (syn_wss (.cv z) (syn_cvv)) (.classEq (.cv y) (syn_cpw1 (.cv z)))) z p0008
  have p0010 :=
    @g_n_3bitr4i (syn_wss (.cv y) (syn_cpw1 (syn_cvv)))
      (syn_wex z (syn_wa (syn_wss (.cv z) (syn_cvv)) (.classEq (.cv y) (syn_cpw1 (.cv z)))))
      (syn_wss (.cv y) (syn_c1c)) (syn_wex z (.classEq (.cv y) (syn_cpw1 (.cv z)))) p0004
      p0006 p0009
  have p0011 := @g_elpw (.cv y) (syn_c1c) p0003
  have p0012 :=
    (Nominal.biimpRefl (syn_wrex x (syn_c1c) (.classEq (.cv y) (syn_cpw1 (syn_cuni (.cv x))))))
  have p0013 := @g_el1c z (.cv x) dv_cache_0006
  have p0014 :=
    @g_anbi1i (.classMem (.cv x) (syn_c1c))
      (syn_wex z (.classEq (.cv x) (syn_csn (.cv z))))
      (.classEq (.cv y) (syn_cpw1 (syn_cuni (.cv x)))) p0013
  have p0015 :=
    @g_n_19_41v (.classEq (.cv x) (syn_csn (.cv z)))
      (.classEq (.cv y) (syn_cpw1 (syn_cuni (.cv x)))) z dv_cache_0007
  have p0016 :=
    @g_bitr4i
      (syn_wa (.classMem (.cv x) (syn_c1c)) (.classEq (.cv y) (syn_cpw1 (syn_cuni (.cv x)))))
      (syn_wa (syn_wex z (.classEq (.cv x) (syn_csn (.cv z))))
        (.classEq (.cv y) (syn_cpw1 (syn_cuni (.cv x)))))
      (syn_wex z (syn_wa (.classEq (.cv x) (syn_csn (.cv z)))
          (.classEq (.cv y) (syn_cpw1 (syn_cuni (.cv x))))))
      p0014 p0015
  have p0017 :=
    @g_exbii
      (syn_wa (.classMem (.cv x) (syn_c1c)) (.classEq (.cv y) (syn_cpw1 (syn_cuni (.cv x)))))
      (syn_wex z (syn_wa (.classEq (.cv x) (syn_csn (.cv z)))
          (.classEq (.cv y) (syn_cpw1 (syn_cuni (.cv x))))))
      x p0016
  have p0018 :=
    @g_excom
      (syn_wa (.classEq (.cv x) (syn_csn (.cv z)))
        (.classEq (.cv y) (syn_cpw1 (syn_cuni (.cv x)))))
      x z
  have p0019 := @g_snex (.cv z)
  have p0020 := @g_unieq (.cv x) (syn_csn (.cv z))
  have p0021 := @g_vex z
  have p0022 := @g_unisn (.cv z) p0021
  have p0023 :=
    @g_syl6eq (.classEq (.cv x) (syn_csn (.cv z))) (syn_cuni (.cv x))
      (syn_cuni (syn_csn (.cv z))) (.cv z) p0020 p0022
  have p0024 := @g_pw1eq (syn_cuni (.cv x)) (.cv z)
  have p0025 :=
    @g_syl (.classEq (.cv x) (syn_csn (.cv z))) (.classEq (syn_cuni (.cv x)) (.cv z))
      (.classEq (syn_cpw1 (syn_cuni (.cv x))) (syn_cpw1 (.cv z))) p0023 p0024
  have p0026 :=
    @g_eqeq2d (.classEq (.cv x) (syn_csn (.cv z))) (syn_cpw1 (syn_cuni (.cv x)))
      (syn_cpw1 (.cv z)) (.cv y) p0025
  have p0027 :=
    @g_ceqsexv (.classEq (.cv y) (syn_cpw1 (syn_cuni (.cv x))))
      (.classEq (.cv y) (syn_cpw1 (.cv z))) x (syn_csn (.cv z)) dv_cache_0008
      dv_cache_0009 p0019 p0026
  have p0028 :=
    @g_exbii
      (syn_wex x (syn_wa (.classEq (.cv x) (syn_csn (.cv z)))
          (.classEq (.cv y) (syn_cpw1 (syn_cuni (.cv x))))))
      (.classEq (.cv y) (syn_cpw1 (.cv z))) z p0027
  have p0029 :=
    @g_bitri
      (syn_wex x (syn_wex z (syn_wa (.classEq (.cv x) (syn_csn (.cv z)))
            (.classEq (.cv y) (syn_cpw1 (syn_cuni (.cv x)))))))
      (syn_wex z (syn_wex x (syn_wa (.classEq (.cv x) (syn_csn (.cv z)))
            (.classEq (.cv y) (syn_cpw1 (syn_cuni (.cv x)))))))
      (syn_wex z (.classEq (.cv y) (syn_cpw1 (.cv z)))) p0018 p0028
  have p0030 :=
    @g_n_3bitri (syn_wrex x (syn_c1c) (.classEq (.cv y) (syn_cpw1 (syn_cuni (.cv x)))))
      (syn_wex x (syn_wa (.classMem (.cv x) (syn_c1c))
          (.classEq (.cv y) (syn_cpw1 (syn_cuni (.cv x))))))
      (syn_wex x (syn_wex z (syn_wa (.classEq (.cv x) (syn_csn (.cv z)))
            (.classEq (.cv y) (syn_cpw1 (syn_cuni (.cv x)))))))
      (syn_wex z (.classEq (.cv y) (syn_cpw1 (.cv z)))) p0012 p0017 p0029
  have p0031 :=
    @g_n_3bitr4i (syn_wss (.cv y) (syn_c1c))
      (syn_wex z (.classEq (.cv y) (syn_cpw1 (.cv z))))
      (.classMem (.cv y) (syn_cpw (syn_c1c)))
      (syn_wrex x (syn_c1c) (.classEq (.cv y) (syn_cpw1 (syn_cuni (.cv x))))) p0010 p0011
      p0030
  have p0032 :=
    @g_eqabi (syn_wrex x (syn_c1c) (.classEq (.cv y) (syn_cpw1 (syn_cuni (.cv x))))) y
      (syn_cpw (syn_c1c)) dv_cache_0010 p0031
  have p0033 :=
    @g_eqtr4i (syn_crn (syn_cpw1fn))
      (.cab y (syn_wrex x (syn_c1c) (.classEq (.cv y) (syn_cpw1 (syn_cuni (.cv x))))))
      (syn_cpw (syn_c1c)) p0002 p0032
  have p0034 := @g_el1c a (.cv x) dv_cache_0011
  have p0035 := @g_el1c b (.cv y) dv_cache_0012
  have p0036 :=
    @g_anbi12i (.classMem (.cv x) (syn_c1c))
      (syn_wex a (.classEq (.cv x) (syn_csn (.cv a)))) (.classMem (.cv y) (syn_c1c))
      (syn_wex b (.classEq (.cv y) (syn_csn (.cv b)))) p0034 p0035
  have p0037 :=
    @g_eeanv (.classEq (.cv x) (syn_csn (.cv a))) (.classEq (.cv y) (syn_csn (.cv b))) a b
      dv_cache_0013 dv_cache_0014
  have p0038 :=
    @g_bitr4i (syn_wa (.classMem (.cv x) (syn_c1c)) (.classMem (.cv y) (syn_c1c)))
      (syn_wa (syn_wex a (.classEq (.cv x) (syn_csn (.cv a))))
        (syn_wex b (.classEq (.cv y) (syn_csn (.cv b)))))
      (syn_wex a (syn_wex b (syn_wa (.classEq (.cv x) (syn_csn (.cv a)))
            (.classEq (.cv y) (syn_csn (.cv b))))))
      p0036 p0037
  have p0039 := @g_pw111 (.cv a) (.cv b)
  have p0040_e00_recanon :
    Nominal.NPrf (syn_wb (.classEq (syn_cpw1 (.cv a)) (syn_cpw1 (.cv b))) (.objEq a b)) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wb syn_cpw1 syn_cin syn_ccompl syn_cnin syn_wnan syn_wa syn_cpw syn_wss
          syn_c1c syn_wex syn_csn
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
    @g_biimpi (.classEq (syn_cpw1 (.cv a)) (syn_cpw1 (.cv b))) (.objEq a b)
      p0040_e00_recanon
  have p0041 :=
    @g_a1i (.imp (.classEq (syn_cpw1 (.cv a)) (syn_cpw1 (.cv b))) (.objEq a b))
      (syn_wa (.classEq (.cv x) (syn_csn (.cv a))) (.classEq (.cv y) (syn_csn (.cv b))))
      p0040
  have p0042 := @g_fveq2 (.cv x) (syn_csn (.cv a)) (syn_cpw1fn)
  have p0043 := @g_vex a
  have p0044 := @g_pw1fnval (.cv a) p0043
  have p0045 :=
    @g_syl6eq (.classEq (.cv x) (syn_csn (.cv a))) (syn_cfv (syn_cpw1fn) (.cv x))
      (syn_cfv (syn_cpw1fn) (syn_csn (.cv a))) (syn_cpw1 (.cv a)) p0042 p0044
  have p0046 := @g_fveq2 (.cv y) (syn_csn (.cv b)) (syn_cpw1fn)
  have p0047 := @g_vex b
  have p0048 := @g_pw1fnval (.cv b) p0047
  have p0049 :=
    @g_syl6eq (.classEq (.cv y) (syn_csn (.cv b))) (syn_cfv (syn_cpw1fn) (.cv y))
      (syn_cfv (syn_cpw1fn) (syn_csn (.cv b))) (syn_cpw1 (.cv b)) p0046 p0048
  have p0050 :=
    @g_eqeqan12d (.classEq (.cv x) (syn_csn (.cv a))) (.classEq (.cv y) (syn_csn (.cv b)))
      (syn_cfv (syn_cpw1fn) (.cv x)) (syn_cpw1 (.cv a)) (syn_cfv (syn_cpw1fn) (.cv y))
      (syn_cpw1 (.cv b)) p0045 p0049
  have p0051 := @g_eqeq12 (.cv x) (syn_csn (.cv a)) (.cv y) (syn_csn (.cv b))
  have p0052 := @g_sneqb (.cv a) (.cv b) p0043
  have p0053_e00_recanon :
    Nominal.NPrf
      (.imp (syn_wa (.classEq (.cv x) (syn_csn (.cv a))) (.classEq (.cv y) (syn_csn (.cv b))))
        (syn_wb (.objEq x y) (.classEq (syn_csn (.cv a)) (syn_csn (.cv b))))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wa syn_csn syn_wb
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
    Nominal.NPrf (syn_wb (.classEq (syn_csn (.cv a)) (syn_csn (.cv b))) (.objEq a b)) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wb syn_csn
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
    @g_syl6bb
      (syn_wa (.classEq (.cv x) (syn_csn (.cv a))) (.classEq (.cv y) (syn_csn (.cv b))))
      (.objEq x y) (.classEq (syn_csn (.cv a)) (syn_csn (.cv b))) (.objEq a b)
      p0053_e00_recanon p0053_e01_recanon
  have p0054 :=
    @g_n_3imtr4d
      (syn_wa (.classEq (.cv x) (syn_csn (.cv a))) (.classEq (.cv y) (syn_csn (.cv b))))
      (.classEq (syn_cpw1 (.cv a)) (syn_cpw1 (.cv b))) (.objEq a b)
      (.classEq (syn_cfv (syn_cpw1fn) (.cv x)) (syn_cfv (syn_cpw1fn) (.cv y)))
      (.objEq x y) p0041 p0050 p0053
  have p0055 :=
    @g_exlimivv
      (syn_wa (.classEq (.cv x) (syn_csn (.cv a))) (.classEq (.cv y) (syn_csn (.cv b))))
      (.imp (.classEq (syn_cfv (syn_cpw1fn) (.cv x)) (syn_cfv (syn_cpw1fn) (.cv y)))
        (.objEq x y))
      a b dv_cache_0015 dv_cache_0016 p0054
  have p0056 :=
    @g_sylbi (syn_wa (.classMem (.cv x) (syn_c1c)) (.classMem (.cv y) (syn_c1c)))
      (syn_wex a (syn_wex b (syn_wa (.classEq (.cv x) (syn_csn (.cv a)))
            (.classEq (.cv y) (syn_csn (.cv b))))))
      (.imp (.classEq (syn_cfv (syn_cpw1fn) (.cv x)) (syn_cfv (syn_cpw1fn) (.cv y)))
        (.objEq x y))
      p0038 p0055
  have p0057 :=
    @g_rgen2a
      (.imp (.classEq (syn_cfv (syn_cpw1fn) (.cv x)) (syn_cfv (syn_cpw1fn) (.cv y)))
        (.objEq x y))
      x y (syn_c1c) dv_cache_0001 p0056
  have p0058 :=
    @g_dff1o6 x y (syn_c1c) (syn_cpw (syn_c1c)) (syn_cpw1fn) dv_cache_0017 dv_cache_0001
      dv_cache_0018 dv_cache_0019 dv_cache_0003
  have p0059_e03_recanon :
    Nominal.NPrf
      (syn_wb (syn_wf1o (syn_cpw1fn) (syn_c1c) (syn_cpw (syn_c1c)))
        (syn_w3a (syn_wfn (syn_cpw1fn) (syn_c1c))
          (.classEq (syn_crn (syn_cpw1fn)) (syn_cpw (syn_c1c))) (syn_wral x (syn_c1c)
            (syn_wral y (syn_c1c) (.imp
                (.classEq (syn_cfv (syn_cpw1fn) (.cv x)) (syn_cfv (syn_cpw1fn) (.cv y)))
                (.objEq x y)))))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wb syn_wf1o syn_wa syn_wf1 syn_wfo syn_cpw1fn syn_cmpt syn_copab
          syn_wex syn_c1c syn_cpw1 syn_cin syn_ccompl syn_cnin syn_wnan syn_cpw syn_wss
          syn_cuni syn_w3a syn_wfn syn_crn syn_cima syn_wrex syn_wbr syn_cop syn_cun
          syn_cvv syn_wral
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
    @g_mpbir3an (syn_wf1o (syn_cpw1fn) (syn_c1c) (syn_cpw (syn_c1c)))
      (syn_wfn (syn_cpw1fn) (syn_c1c))
      (.classEq (syn_crn (syn_cpw1fn)) (syn_cpw (syn_c1c)))
      (syn_wral x (syn_c1c) (syn_wral y (syn_c1c)
          (.imp (.classEq (syn_cfv (syn_cpw1fn) (.cv x)) (syn_cfv (syn_cpw1fn) (.cv y)))
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

@[expose]
noncomputable def g_fnfullfunlem1 (x : Var) (A : Class) (B : Class) (F : Class)
    (dv_A_x : x ∉ A.fv) (dv_B_x : x ∉ B.fv) (dv_F_x : x ∉ F.fv) :
    Nominal.NPrf
      (syn_wb (syn_wbr A (syn_cdif (syn_ccom (syn_cid) F) (syn_ccom (syn_ccompl (syn_cid)) F))
          B) (syn_wa (syn_wbr A F B)
          (.all x (.imp (syn_wbr A F (.cv x)) (.classEq (.cv x) B))))) :=
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
  have dv_cache_0004 : x ∉ ((syn_ccompl (syn_cid))).fv :=
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
      ((syn_wb (syn_wbr A (syn_cdif (syn_ccom (syn_cid) F) (syn_ccom (syn_ccompl (syn_cid)) F))
            B) (syn_wa (syn_wbr A F B)
            (.all x (.imp (syn_wbr A F (.cv x)) (.classEq (.cv x) B)))))).fv :=
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
    @g_brex A B (syn_cdif (syn_ccom (syn_cid) F) (syn_ccom (syn_ccompl (syn_cid)) F))
  have p0001 :=
    @g_simprd
      (syn_wbr A (syn_cdif (syn_ccom (syn_cid) F) (syn_ccom (syn_ccompl (syn_cid)) F)) B)
      (.classMem A (syn_cvv)) (.classMem B (syn_cvv)) p0000
  have p0002 := @g_brex A B F
  have p0003 :=
    @g_simprd (syn_wbr A F B) (.classMem A (syn_cvv)) (.classMem B (syn_cvv)) p0002
  have p0004 :=
    @g_adantr (syn_wbr A F B) (.classMem B (syn_cvv))
      (.all x (.imp (syn_wbr A F (.cv x)) (.classEq (.cv x) B))) p0003
  have p0005 :=
    @g_breq2 (.cv y) B A
      (syn_cdif (syn_ccom (syn_cid) F) (syn_ccom (syn_ccompl (syn_cid)) F))
  have p0006 := @g_breq2 (.cv y) B A F
  have p0007 := @g_eqeq2 (.cv y) B (.cv x)
  have p0008_e00_recanon :
    Nominal.NPrf (.imp (.classEq (.cv y) B) (syn_wb (.objEq x y) (.classEq (.cv x) B))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wb
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
    @g_imbi2d (.classEq (.cv y) B) (.objEq x y) (.classEq (.cv x) B) (syn_wbr A F (.cv x))
      p0008_e00_recanon
  have p0009 :=
    @g_albidv (.classEq (.cv y) B) (.imp (syn_wbr A F (.cv x)) (.objEq x y))
      (.imp (syn_wbr A F (.cv x)) (.classEq (.cv x) B)) x dv_cache_0001 p0008
  have p0010 :=
    @g_anbi12d (.classEq (.cv y) B) (syn_wbr A F (.cv y)) (syn_wbr A F B)
      (.all x (.imp (syn_wbr A F (.cv x)) (.objEq x y)))
      (.all x (.imp (syn_wbr A F (.cv x)) (.classEq (.cv x) B))) p0006 p0009
  have p0011 :=
    @g_bibi12d (.classEq (.cv y) B)
      (syn_wbr A (syn_cdif (syn_ccom (syn_cid) F) (syn_ccom (syn_ccompl (syn_cid)) F)) (.cv y))
      (syn_wbr A (syn_cdif (syn_ccom (syn_cid) F) (syn_ccom (syn_ccompl (syn_cid)) F)) B)
      (syn_wa (syn_wbr A F (.cv y)) (.all x (.imp (syn_wbr A F (.cv x)) (.objEq x y))))
      (syn_wa (syn_wbr A F B) (.all x (.imp (syn_wbr A F (.cv x)) (.classEq (.cv x) B))))
      p0005 p0010
  have p0012 :=
    @g_brdif A (.cv y) (syn_ccom (syn_cid) F) (syn_ccom (syn_ccompl (syn_cid)) F)
  have p0013 := @g_coi2 F
  have p0014 := @g_breqi A (.cv y) (syn_ccom (syn_cid) F) F p0013
  have p0015 :=
    @g_brco x A (.cv y) (syn_ccompl (syn_cid)) F dv_cache_0002 dv_cache_0003 dv_cache_0004
      dv_cache_0005
  have p0016 := (Nominal.biimpRefl (syn_wbr (.cv x) (syn_ccompl (syn_cid)) (.cv y)))
  have p0017 := @g_vex x
  have p0018 := @g_vex y
  have p0019 := @g_opex (.cv x) (.cv y) p0017 p0018
  have p0020 := @g_elcompl (syn_cop (.cv x) (.cv y)) (syn_cid) p0019
  have p0021 := (Nominal.biimpRefl (syn_wbr (.cv x) (syn_cid) (.cv y)))
  have p0022 := @g_ideq (.cv x) (.cv y) p0018
  have p0023_e01_recanon :
    Nominal.NPrf (syn_wb (syn_wbr (.cv x) (syn_cid) (.cv y)) (.objEq x y)) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wb syn_wbr syn_cop syn_cun syn_cnin syn_wnan syn_wa syn_ccompl syn_wrex
          syn_wex syn_cphi syn_cid syn_copab
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
    @g_bitr3i (.classMem (syn_cop (.cv x) (.cv y)) (syn_cid))
      (syn_wbr (.cv x) (syn_cid) (.cv y)) (.objEq x y) p0021 p0023_e01_recanon
  have p0024 :=
    @g_xchbinx (.classMem (syn_cop (.cv x) (.cv y)) (syn_ccompl (syn_cid)))
      (.classMem (syn_cop (.cv x) (.cv y)) (syn_cid)) (.objEq x y) p0020 p0023
  have p0025 :=
    @g_bitri (syn_wbr (.cv x) (syn_ccompl (syn_cid)) (.cv y))
      (.classMem (syn_cop (.cv x) (.cv y)) (syn_ccompl (syn_cid))) (.neg (.objEq x y))
      p0016 p0024
  have p0026 :=
    @g_anbi2i (syn_wbr (.cv x) (syn_ccompl (syn_cid)) (.cv y)) (.neg (.objEq x y))
      (syn_wbr A F (.cv x)) p0025
  have p0027 :=
    @g_exbii
      (syn_wa (syn_wbr A F (.cv x)) (syn_wbr (.cv x) (syn_ccompl (syn_cid)) (.cv y)))
      (syn_wa (syn_wbr A F (.cv x)) (.neg (.objEq x y))) x p0026
  have p0028 := @g_exanali (syn_wbr A F (.cv x)) (.objEq x y) x
  have p0029 :=
    @g_n_3bitrri (syn_wbr A (syn_ccom (syn_ccompl (syn_cid)) F) (.cv y))
      (syn_wex x
        (syn_wa (syn_wbr A F (.cv x)) (syn_wbr (.cv x) (syn_ccompl (syn_cid)) (.cv y))))
      (syn_wex x (syn_wa (syn_wbr A F (.cv x)) (.neg (.objEq x y))))
      (.neg (.all x (.imp (syn_wbr A F (.cv x)) (.objEq x y)))) p0015 p0027 p0028
  have p0030 :=
    @g_con1bii (.all x (.imp (syn_wbr A F (.cv x)) (.objEq x y)))
      (syn_wbr A (syn_ccom (syn_ccompl (syn_cid)) F) (.cv y)) p0029
  have p0031 :=
    @g_anbi12i (syn_wbr A (syn_ccom (syn_cid) F) (.cv y)) (syn_wbr A F (.cv y))
      (.neg (syn_wbr A (syn_ccom (syn_ccompl (syn_cid)) F) (.cv y)))
      (.all x (.imp (syn_wbr A F (.cv x)) (.objEq x y))) p0014 p0030
  have p0032 :=
    @g_bitri
      (syn_wbr A (syn_cdif (syn_ccom (syn_cid) F) (syn_ccom (syn_ccompl (syn_cid)) F)) (.cv y))
      (syn_wa (syn_wbr A (syn_ccom (syn_cid) F) (.cv y))
        (.neg (syn_wbr A (syn_ccom (syn_ccompl (syn_cid)) F) (.cv y))))
      (syn_wa (syn_wbr A F (.cv y)) (.all x (.imp (syn_wbr A F (.cv x)) (.objEq x y))))
      p0012 p0031
  have p0033 :=
    @g_vtoclg
      (syn_wb (syn_wbr A (syn_cdif (syn_ccom (syn_cid) F) (syn_ccom (syn_ccompl (syn_cid)) F))
          (.cv y))
        (syn_wa (syn_wbr A F (.cv y)) (.all x (.imp (syn_wbr A F (.cv x)) (.objEq x y)))))
      (syn_wb (syn_wbr A (syn_cdif (syn_ccom (syn_cid) F) (syn_ccom (syn_ccompl (syn_cid)) F))
          B) (syn_wa (syn_wbr A F B)
          (.all x (.imp (syn_wbr A F (.cv x)) (.classEq (.cv x) B)))))
      y B (syn_cvv) dv_cache_0006 dv_cache_0007 p0011 p0032
  have p0034 :=
    @g_pm5_21nii
      (syn_wbr A (syn_cdif (syn_ccom (syn_cid) F) (syn_ccom (syn_ccompl (syn_cid)) F)) B)
      (.classMem B (syn_cvv))
      (syn_wa (syn_wbr A F B) (.all x (.imp (syn_wbr A F (.cv x)) (.classEq (.cv x) B))))
      p0001 p0004 p0033
  exact p0034

@[expose]
noncomputable def g_fnfullfunlem2 (F : Class) :
    Nominal.NPrf
      (syn_wfun (syn_cdif (syn_ccom (syn_cid) F) (syn_ccom (syn_ccompl (syn_cid)) F))) :=
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
    x ∉ ((syn_cdif (syn_ccom (syn_cid) F) (syn_ccom (syn_ccompl (syn_cid)) F))).fv := by
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
    y ∉ ((syn_cdif (syn_ccom (syn_cid) F) (syn_ccom (syn_ccompl (syn_cid)) F))).fv :=
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
    z ∉ ((syn_cdif (syn_ccom (syn_cid) F) (syn_ccom (syn_ccompl (syn_cid)) F))).fv :=
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
    @g_dffun2 x y z (syn_cdif (syn_ccom (syn_cid) F) (syn_ccom (syn_ccompl (syn_cid)) F))
      dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006
  have p0001 :=
    @g_fnfullfunlem1 z (.cv x) (.cv y) F dv_cache_0007 dv_cache_0008 dv_cache_0009
  have p0002 :=
    @g_fnfullfunlem1 y (.cv x) (.cv z) F dv_cache_0010 dv_cache_0011 dv_cache_0012
  have p0003 := @g_sp (.imp (syn_wbr (.cv x) F (.cv y)) (.objEq y z)) y
  have p0004 :=
    @g_impcom (.all y (.imp (syn_wbr (.cv x) F (.cv y)) (.objEq y z)))
      (syn_wbr (.cv x) F (.cv y)) (.objEq y z) p0003
  have p0005 :=
    @g_ad2ant2rl (syn_wbr (.cv x) F (.cv y))
      (.all y (.imp (syn_wbr (.cv x) F (.cv y)) (.objEq y z))) (.objEq y z)
      (.all z (.imp (syn_wbr (.cv x) F (.cv z)) (.objEq z y))) (syn_wbr (.cv x) F (.cv z))
      p0004
  have p0006_e00_recanon :
    Nominal.NPrf
      (syn_wb (syn_wbr (.cv x)
          (syn_cdif (syn_ccom (syn_cid) F) (syn_ccom (syn_ccompl (syn_cid)) F)) (.cv y))
        (syn_wa (syn_wbr (.cv x) F (.cv y))
          (.all z (.imp (syn_wbr (.cv x) F (.cv z)) (.objEq z y))))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wb syn_wbr syn_cop syn_cun syn_cnin syn_wnan syn_wa syn_ccompl syn_wrex
          syn_wex syn_cphi syn_cdif syn_cin syn_ccom syn_copab syn_cid
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
      (syn_wb (syn_wbr (.cv x)
          (syn_cdif (syn_ccom (syn_cid) F) (syn_ccom (syn_ccompl (syn_cid)) F)) (.cv z))
        (syn_wa (syn_wbr (.cv x) F (.cv z))
          (.all y (.imp (syn_wbr (.cv x) F (.cv y)) (.objEq y z))))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wb syn_wbr syn_cop syn_cun syn_cnin syn_wnan syn_wa syn_ccompl syn_wrex
          syn_wex syn_cphi syn_cdif syn_cin syn_ccom syn_copab syn_cid
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
    @g_syl2anb
      (syn_wbr (.cv x)
        (syn_cdif (syn_ccom (syn_cid) F) (syn_ccom (syn_ccompl (syn_cid)) F)) (.cv y))
      (syn_wa (syn_wbr (.cv x) F (.cv y))
        (.all z (.imp (syn_wbr (.cv x) F (.cv z)) (.objEq z y))))
      (syn_wa (syn_wbr (.cv x) F (.cv z))
        (.all y (.imp (syn_wbr (.cv x) F (.cv y)) (.objEq y z))))
      (.objEq y z)
      (syn_wbr (.cv x)
        (syn_cdif (syn_ccom (syn_cid) F) (syn_ccom (syn_ccompl (syn_cid)) F)) (.cv z))
      p0006_e00_recanon p0006_e01_recanon p0005
  have p0007 :=
    @g_gen2
      (.imp (syn_wa (syn_wbr (.cv x)
            (syn_cdif (syn_ccom (syn_cid) F) (syn_ccom (syn_ccompl (syn_cid)) F)) (.cv y))
          (syn_wbr (.cv x) (syn_cdif (syn_ccom (syn_cid) F) (syn_ccom (syn_ccompl (syn_cid)) F))
            (.cv z))) (.objEq y z))
      y z p0006
  have p0008 :=
    @g_mpgbir
      (syn_wfun (syn_cdif (syn_ccom (syn_cid) F) (syn_ccom (syn_ccompl (syn_cid)) F)))
      (.all y (.all z (.imp (syn_wa (syn_wbr (.cv x)
                (syn_cdif (syn_ccom (syn_cid) F) (syn_ccom (syn_ccompl (syn_cid)) F)) (.cv y))
              (syn_wbr (.cv x)
                (syn_cdif (syn_ccom (syn_cid) F) (syn_ccom (syn_ccompl (syn_cid)) F)) (.cv z)))
            (.objEq y z))))
      x p0000 p0007
  exact p0008

@[expose]
noncomputable def g_fnfullfun (F : Class) :
    Nominal.NPrf (syn_wfn (syn_cfullfun F) (syn_cvv)) :=
  by
  have p0000 := @g_fnfullfunlem2 F
  have p0001 :=
    @g_funfn (syn_cdif (syn_ccom (syn_cid) F) (syn_ccom (syn_ccompl (syn_cid)) F))
  have p0002 :=
    @g_mpbi
      (syn_wfun (syn_cdif (syn_ccom (syn_cid) F) (syn_ccom (syn_ccompl (syn_cid)) F)))
      (syn_wfn (syn_cdif (syn_ccom (syn_cid) F) (syn_ccom (syn_ccompl (syn_cid)) F))
        (syn_cdm (syn_cdif (syn_ccom (syn_cid) F) (syn_ccom (syn_ccompl (syn_cid)) F))))
      p0000 p0001
  have p0003 := @g_n_0ex
  have p0004 :=
    @g_fnconstg
      (syn_ccompl
        (syn_cdm (syn_cdif (syn_ccom (syn_cid) F) (syn_ccom (syn_ccompl (syn_cid)) F))))
      (syn_c0) (syn_cvv)
  have p0005 := Nominal.mp p0003 p0004
  have p0006 :=
    @g_pm3_2i
      (syn_wfn (syn_cdif (syn_ccom (syn_cid) F) (syn_ccom (syn_ccompl (syn_cid)) F))
        (syn_cdm (syn_cdif (syn_ccom (syn_cid) F) (syn_ccom (syn_ccompl (syn_cid)) F))))
      (syn_wfn (syn_cxp (syn_ccompl (syn_cdm
              (syn_cdif (syn_ccom (syn_cid) F) (syn_ccom (syn_ccompl (syn_cid)) F))))
          (syn_csn (syn_c0))) (syn_ccompl (syn_cdm
            (syn_cdif (syn_ccom (syn_cid) F) (syn_ccom (syn_ccompl (syn_cid)) F)))))
      p0002 p0005
  have p0007 :=
    @g_incompl
      (syn_cdm (syn_cdif (syn_ccom (syn_cid) F) (syn_ccom (syn_ccompl (syn_cid)) F)))
  have p0008 :=
    @g_fnun
      (syn_cdm (syn_cdif (syn_ccom (syn_cid) F) (syn_ccom (syn_ccompl (syn_cid)) F)))
      (syn_ccompl
        (syn_cdm (syn_cdif (syn_ccom (syn_cid) F) (syn_ccom (syn_ccompl (syn_cid)) F))))
      (syn_cdif (syn_ccom (syn_cid) F) (syn_ccom (syn_ccompl (syn_cid)) F))
      (syn_cxp (syn_ccompl
          (syn_cdm (syn_cdif (syn_ccom (syn_cid) F) (syn_ccom (syn_ccompl (syn_cid)) F))))
        (syn_csn (syn_c0)))
  have p0009 :=
    @g_mp2an
      (syn_wa (syn_wfn (syn_cdif (syn_ccom (syn_cid) F) (syn_ccom (syn_ccompl (syn_cid)) F))
          (syn_cdm (syn_cdif (syn_ccom (syn_cid) F) (syn_ccom (syn_ccompl (syn_cid)) F))))
        (syn_wfn (syn_cxp (syn_ccompl (syn_cdm
                (syn_cdif (syn_ccom (syn_cid) F) (syn_ccom (syn_ccompl (syn_cid)) F))))
            (syn_csn (syn_c0))) (syn_ccompl (syn_cdm
              (syn_cdif (syn_ccom (syn_cid) F) (syn_ccom (syn_ccompl (syn_cid)) F))))))
      (.classEq (syn_cin
          (syn_cdm (syn_cdif (syn_ccom (syn_cid) F) (syn_ccom (syn_ccompl (syn_cid)) F)))
          (syn_ccompl (syn_cdm
              (syn_cdif (syn_ccom (syn_cid) F) (syn_ccom (syn_ccompl (syn_cid)) F))))) (syn_c0))
      (syn_wfn (syn_cun (syn_cdif (syn_ccom (syn_cid) F) (syn_ccom (syn_ccompl (syn_cid)) F))
          (syn_cxp (syn_ccompl (syn_cdm
                (syn_cdif (syn_ccom (syn_cid) F) (syn_ccom (syn_ccompl (syn_cid)) F))))
            (syn_csn (syn_c0)))) (syn_cun
          (syn_cdm (syn_cdif (syn_ccom (syn_cid) F) (syn_ccom (syn_ccompl (syn_cid)) F)))
          (syn_ccompl (syn_cdm
              (syn_cdif (syn_ccom (syn_cid) F) (syn_ccom (syn_ccompl (syn_cid)) F))))))
      p0006 p0007 p0008
  have p0010 := (Nominal.classEqRefl (syn_cfullfun F))
  have p0011 :=
    @g_uncompl
      (syn_cdm (syn_cdif (syn_ccom (syn_cid) F) (syn_ccom (syn_ccompl (syn_cid)) F)))
  have p0012 :=
    @g_eqcomi
      (syn_cun (syn_cdm (syn_cdif (syn_ccom (syn_cid) F) (syn_ccom (syn_ccompl (syn_cid)) F)))
        (syn_ccompl (syn_cdm
            (syn_cdif (syn_ccom (syn_cid) F) (syn_ccom (syn_ccompl (syn_cid)) F)))))
      (syn_cvv) p0011
  have p0013 :=
    @g_fneq1 (syn_cvv) (syn_cfullfun F)
      (syn_cun (syn_cdif (syn_ccom (syn_cid) F) (syn_ccom (syn_ccompl (syn_cid)) F)) (syn_cxp
          (syn_ccompl (syn_cdm
              (syn_cdif (syn_ccom (syn_cid) F) (syn_ccom (syn_ccompl (syn_cid)) F))))
          (syn_csn (syn_c0))))
  have p0014 :=
    @g_fneq2 (syn_cvv)
      (syn_cun (syn_cdm (syn_cdif (syn_ccom (syn_cid) F) (syn_ccom (syn_ccompl (syn_cid)) F)))
        (syn_ccompl (syn_cdm
            (syn_cdif (syn_ccom (syn_cid) F) (syn_ccom (syn_ccompl (syn_cid)) F)))))
      (syn_cun (syn_cdif (syn_ccom (syn_cid) F) (syn_ccom (syn_ccompl (syn_cid)) F)) (syn_cxp
          (syn_ccompl (syn_cdm
              (syn_cdif (syn_ccom (syn_cid) F) (syn_ccom (syn_ccompl (syn_cid)) F))))
          (syn_csn (syn_c0))))
  have p0015 :=
    @g_sylan9bb
      (.classEq (syn_cfullfun F)
        (syn_cun (syn_cdif (syn_ccom (syn_cid) F) (syn_ccom (syn_ccompl (syn_cid)) F)) (syn_cxp
            (syn_ccompl (syn_cdm
                (syn_cdif (syn_ccom (syn_cid) F) (syn_ccom (syn_ccompl (syn_cid)) F))))
            (syn_csn (syn_c0)))))
      (syn_wfn (syn_cfullfun F) (syn_cvv))
      (syn_wfn (syn_cun (syn_cdif (syn_ccom (syn_cid) F) (syn_ccom (syn_ccompl (syn_cid)) F))
          (syn_cxp (syn_ccompl (syn_cdm
                (syn_cdif (syn_ccom (syn_cid) F) (syn_ccom (syn_ccompl (syn_cid)) F))))
            (syn_csn (syn_c0)))) (syn_cvv))
      (.classEq (syn_cvv) (syn_cun
          (syn_cdm (syn_cdif (syn_ccom (syn_cid) F) (syn_ccom (syn_ccompl (syn_cid)) F)))
          (syn_ccompl (syn_cdm
              (syn_cdif (syn_ccom (syn_cid) F) (syn_ccom (syn_ccompl (syn_cid)) F))))))
      (syn_wfn (syn_cun (syn_cdif (syn_ccom (syn_cid) F) (syn_ccom (syn_ccompl (syn_cid)) F))
          (syn_cxp (syn_ccompl (syn_cdm
                (syn_cdif (syn_ccom (syn_cid) F) (syn_ccom (syn_ccompl (syn_cid)) F))))
            (syn_csn (syn_c0)))) (syn_cun
          (syn_cdm (syn_cdif (syn_ccom (syn_cid) F) (syn_ccom (syn_ccompl (syn_cid)) F)))
          (syn_ccompl (syn_cdm
              (syn_cdif (syn_ccom (syn_cid) F) (syn_ccom (syn_ccompl (syn_cid)) F))))))
      p0013 p0014
  have p0016 :=
    @g_mp2an
      (.classEq (syn_cfullfun F)
        (syn_cun (syn_cdif (syn_ccom (syn_cid) F) (syn_ccom (syn_ccompl (syn_cid)) F)) (syn_cxp
            (syn_ccompl (syn_cdm
                (syn_cdif (syn_ccom (syn_cid) F) (syn_ccom (syn_ccompl (syn_cid)) F))))
            (syn_csn (syn_c0)))))
      (.classEq (syn_cvv) (syn_cun
          (syn_cdm (syn_cdif (syn_ccom (syn_cid) F) (syn_ccom (syn_ccompl (syn_cid)) F)))
          (syn_ccompl (syn_cdm
              (syn_cdif (syn_ccom (syn_cid) F) (syn_ccom (syn_ccompl (syn_cid)) F))))))
      (syn_wb (syn_wfn (syn_cfullfun F) (syn_cvv)) (syn_wfn
          (syn_cun (syn_cdif (syn_ccom (syn_cid) F) (syn_ccom (syn_ccompl (syn_cid)) F))
            (syn_cxp (syn_ccompl (syn_cdm
                  (syn_cdif (syn_ccom (syn_cid) F) (syn_ccom (syn_ccompl (syn_cid)) F))))
              (syn_csn (syn_c0)))) (syn_cun (syn_cdm
              (syn_cdif (syn_ccom (syn_cid) F) (syn_ccom (syn_ccompl (syn_cid)) F))) (syn_ccompl
              (syn_cdm
                (syn_cdif (syn_ccom (syn_cid) F) (syn_ccom (syn_ccompl (syn_cid)) F)))))))
      p0010 p0012 p0015
  have p0017 :=
    @g_mpbir (syn_wfn (syn_cfullfun F) (syn_cvv))
      (syn_wfn (syn_cun (syn_cdif (syn_ccom (syn_cid) F) (syn_ccom (syn_ccompl (syn_cid)) F))
          (syn_cxp (syn_ccompl (syn_cdm
                (syn_cdif (syn_ccom (syn_cid) F) (syn_ccom (syn_ccompl (syn_cid)) F))))
            (syn_csn (syn_c0)))) (syn_cun
          (syn_cdm (syn_cdif (syn_ccom (syn_cid) F) (syn_ccom (syn_ccompl (syn_cid)) F)))
          (syn_ccompl (syn_cdm
              (syn_cdif (syn_ccom (syn_cid) F) (syn_ccom (syn_ccompl (syn_cid)) F))))))
      p0009 p0016
  exact p0017

@[expose]
noncomputable def g_fullfunexg (F : Class) (V : Class) :
    Nominal.NPrf (.imp (.classMem F V) (.classMem (syn_cfullfun F) (syn_cvv))) :=
  by
  have p0000 := (Nominal.classEqRefl (syn_cfullfun F))
  have p0001 := @g_idex
  have p0002 := @g_coexg (syn_cid) F (syn_cvv) V
  have p0003 :=
    @g_mpan (.classMem (syn_cid) (syn_cvv)) (.classMem F V)
      (.classMem (syn_ccom (syn_cid) F) (syn_cvv)) p0001 p0002
  have p0005 := @g_complex (syn_cid) p0001
  have p0006 := @g_coexg (syn_ccompl (syn_cid)) F (syn_cvv) V
  have p0007 :=
    @g_mpan (.classMem (syn_ccompl (syn_cid)) (syn_cvv)) (.classMem F V)
      (.classMem (syn_ccom (syn_ccompl (syn_cid)) F) (syn_cvv)) p0005 p0006
  have p0008 :=
    @g_difexg (syn_ccom (syn_cid) F) (syn_ccom (syn_ccompl (syn_cid)) F) (syn_cvv)
      (syn_cvv)
  have p0009 :=
    @g_syl2anc (.classMem F V) (.classMem (syn_ccom (syn_cid) F) (syn_cvv))
      (.classMem (syn_ccom (syn_ccompl (syn_cid)) F) (syn_cvv))
      (.classMem (syn_cdif (syn_ccom (syn_cid) F) (syn_ccom (syn_ccompl (syn_cid)) F))
        (syn_cvv))
      p0003 p0007 p0008
  have p0010 :=
    @g_dmexg (syn_cdif (syn_ccom (syn_cid) F) (syn_ccom (syn_ccompl (syn_cid)) F))
      (syn_cvv)
  have p0011 :=
    @g_complexg
      (syn_cdm (syn_cdif (syn_ccom (syn_cid) F) (syn_ccom (syn_ccompl (syn_cid)) F)))
      (syn_cvv)
  have p0012 :=
    @g_n_3syl (.classMem F V)
      (.classMem (syn_cdif (syn_ccom (syn_cid) F) (syn_ccom (syn_ccompl (syn_cid)) F))
        (syn_cvv))
      (.classMem (syn_cdm (syn_cdif (syn_ccom (syn_cid) F) (syn_ccom (syn_ccompl (syn_cid)) F)))
        (syn_cvv))
      (.classMem (syn_ccompl
          (syn_cdm (syn_cdif (syn_ccom (syn_cid) F) (syn_ccom (syn_ccompl (syn_cid)) F))))
        (syn_cvv))
      p0009 p0010 p0011
  have p0013 := @g_snex (syn_c0)
  have p0014 :=
    @g_xpexg
      (syn_ccompl
        (syn_cdm (syn_cdif (syn_ccom (syn_cid) F) (syn_ccom (syn_ccompl (syn_cid)) F))))
      (syn_csn (syn_c0)) (syn_cvv) (syn_cvv)
  have p0015 :=
    @g_sylancl (.classMem F V)
      (.classMem (syn_ccompl
          (syn_cdm (syn_cdif (syn_ccom (syn_cid) F) (syn_ccom (syn_ccompl (syn_cid)) F))))
        (syn_cvv))
      (.classMem (syn_csn (syn_c0)) (syn_cvv))
      (.classMem (syn_cxp (syn_ccompl (syn_cdm
              (syn_cdif (syn_ccom (syn_cid) F) (syn_ccom (syn_ccompl (syn_cid)) F))))
          (syn_csn (syn_c0))) (syn_cvv))
      p0012 p0013 p0014
  have p0016 :=
    @g_unexg (syn_cdif (syn_ccom (syn_cid) F) (syn_ccom (syn_ccompl (syn_cid)) F))
      (syn_cxp (syn_ccompl
          (syn_cdm (syn_cdif (syn_ccom (syn_cid) F) (syn_ccom (syn_ccompl (syn_cid)) F))))
        (syn_csn (syn_c0)))
      (syn_cvv) (syn_cvv)
  have p0017 :=
    @g_syl2anc (.classMem F V)
      (.classMem (syn_cdif (syn_ccom (syn_cid) F) (syn_ccom (syn_ccompl (syn_cid)) F))
        (syn_cvv))
      (.classMem (syn_cxp (syn_ccompl (syn_cdm
              (syn_cdif (syn_ccom (syn_cid) F) (syn_ccom (syn_ccompl (syn_cid)) F))))
          (syn_csn (syn_c0))) (syn_cvv))
      (.classMem (syn_cun (syn_cdif (syn_ccom (syn_cid) F) (syn_ccom (syn_ccompl (syn_cid)) F))
          (syn_cxp (syn_ccompl (syn_cdm
                (syn_cdif (syn_ccom (syn_cid) F) (syn_ccom (syn_ccompl (syn_cid)) F))))
            (syn_csn (syn_c0)))) (syn_cvv))
      p0009 p0015 p0016
  have p0018 :=
    @g_syl5eqel (.classMem F V) (syn_cfullfun F)
      (syn_cun (syn_cdif (syn_ccom (syn_cid) F) (syn_ccom (syn_ccompl (syn_cid)) F)) (syn_cxp
          (syn_ccompl (syn_cdm
              (syn_cdif (syn_ccom (syn_cid) F) (syn_ccom (syn_ccompl (syn_cid)) F))))
          (syn_csn (syn_c0))))
      (syn_cvv) p0000 p0017
  exact p0018

@[expose]
noncomputable def g_fullfunex (F : Class)
    (hyp_fullfunex_1 : Nominal.NPrf (.classMem F (syn_cvv))) :
    Nominal.NPrf (.classMem (syn_cfullfun F) (syn_cvv)) :=
  by
  have p0000 := @g_fullfunexg F (syn_cvv)
  have p0001 := Nominal.mp hyp_fullfunex_1 p0000
  exact p0001

@[expose]
noncomputable def g_fvfullfunlem1 (x : Var) (y : Var) (F : Class) (dv_F_x : x ∉ F.fv)
    (dv_F_y : y ∉ F.fv) (dv_x_y : x ≠ y) :
    Nominal.NPrf
      (.classEq (syn_cdm (syn_cdif (syn_ccom (syn_cid) F) (syn_ccom (syn_ccompl (syn_cid)) F)))
        (.cab x (syn_weu y (syn_wbr (.cv x) F (.cv y))))) :=
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
    y ∉ ((syn_cdif (syn_ccom (syn_cid) F) (syn_ccom (syn_ccompl (syn_cid)) F))).fv :=
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
  have dv_cache_0006 : z ∉ ((syn_wbr (.cv x) F (.cv y))).fv :=
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
  have dv_cache_0008 : y ∉ ((syn_wbr (.cv x) F (.cv z))).fv :=
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
      ((syn_cdm (syn_cdif (syn_ccom (syn_cid) F) (syn_ccom (syn_ccompl (syn_cid)) F)))).fv :=
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
    @g_eldm y (.cv x)
      (syn_cdif (syn_ccom (syn_cid) F) (syn_ccom (syn_ccompl (syn_cid)) F)) dv_cache_0001
      dv_cache_0002
  have p0001 :=
    @g_fnfullfunlem1 z (.cv x) (.cv y) F dv_cache_0003 dv_cache_0004 dv_cache_0005
  have p0002_e00_recanon :
    Nominal.NPrf
      (syn_wb (syn_wbr (.cv x)
          (syn_cdif (syn_ccom (syn_cid) F) (syn_ccom (syn_ccompl (syn_cid)) F)) (.cv y))
        (syn_wa (syn_wbr (.cv x) F (.cv y))
          (.all z (.imp (syn_wbr (.cv x) F (.cv z)) (.objEq z y))))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wb syn_wbr syn_cop syn_cun syn_cnin syn_wnan syn_wa syn_ccompl syn_wrex
          syn_wex syn_cphi syn_cdif syn_cin syn_ccom syn_copab syn_cid
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
    @g_exbii
      (syn_wbr (.cv x)
        (syn_cdif (syn_ccom (syn_cid) F) (syn_ccom (syn_ccompl (syn_cid)) F)) (.cv y))
      (syn_wa (syn_wbr (.cv x) F (.cv y))
        (.all z (.imp (syn_wbr (.cv x) F (.cv z)) (.objEq z y))))
      y p0002_e00_recanon
  have p0003 := @g_nfv (syn_wbr (.cv x) F (.cv y)) z dv_cache_0006
  have p0004 := @g_eu1 (syn_wbr (.cv x) F (.cv y)) y z dv_cache_0007 p0003
  have p0005 := @g_nfv (syn_wbr (.cv x) F (.cv z)) y dv_cache_0008
  have p0006 := @g_breq2 (.cv y) (.cv z) (.cv x) F
  have p0007_e01_recanon :
    Nominal.NPrf
      (.imp (.objEq y z) (syn_wb (syn_wbr (.cv x) F (.cv y)) (syn_wbr (.cv x) F (.cv z)))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wb syn_wbr syn_cop syn_cun syn_cnin syn_wnan syn_wa syn_ccompl syn_wrex
          syn_wex syn_cphi
        simp (config :=
          { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_class_cv]
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
        · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0006
  have p0007 :=
    @g_sbie (syn_wbr (.cv x) F (.cv y)) (syn_wbr (.cv x) F (.cv z)) y z p0005
      p0007_e01_recanon
  have p0008 := @g_equcom y z
  have p0009 :=
    @g_imbi12i (syn_wsb z y (syn_wbr (.cv x) F (.cv y))) (syn_wbr (.cv x) F (.cv z))
      (.objEq y z) (.objEq z y) p0007 p0008
  have p0010 :=
    @g_albii (.imp (syn_wsb z y (syn_wbr (.cv x) F (.cv y))) (.objEq y z))
      (.imp (syn_wbr (.cv x) F (.cv z)) (.objEq z y)) z p0009
  have p0011 :=
    @g_anbi2i (.all z (.imp (syn_wsb z y (syn_wbr (.cv x) F (.cv y))) (.objEq y z)))
      (.all z (.imp (syn_wbr (.cv x) F (.cv z)) (.objEq z y))) (syn_wbr (.cv x) F (.cv y))
      p0010
  have p0012 :=
    @g_exbii
      (syn_wa (syn_wbr (.cv x) F (.cv y))
        (.all z (.imp (syn_wsb z y (syn_wbr (.cv x) F (.cv y))) (.objEq y z))))
      (syn_wa (syn_wbr (.cv x) F (.cv y))
        (.all z (.imp (syn_wbr (.cv x) F (.cv z)) (.objEq z y))))
      y p0011
  have p0013_e00_recanon :
    Nominal.NPrf
      (syn_wb (syn_weu y (syn_wbr (.cv x) F (.cv y))) (syn_wex y
          (syn_wa (syn_wbr (.cv x) F (.cv y))
            (.all z (.imp (syn_wsb z y (syn_wbr (.cv x) F (.cv y))) (.objEq y z)))))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wb syn_weu syn_wex syn_wbr syn_cop syn_cun syn_cnin syn_wnan syn_wa
          syn_ccompl syn_wrex syn_cphi
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
    @g_bitr2i (syn_weu y (syn_wbr (.cv x) F (.cv y)))
      (syn_wex y (syn_wa (syn_wbr (.cv x) F (.cv y))
          (.all z (.imp (syn_wsb z y (syn_wbr (.cv x) F (.cv y))) (.objEq y z)))))
      (syn_wex y (syn_wa (syn_wbr (.cv x) F (.cv y))
          (.all z (.imp (syn_wbr (.cv x) F (.cv z)) (.objEq z y)))))
      p0013_e00_recanon p0012
  have p0014 :=
    @g_n_3bitri
      (.classMem (.cv x)
        (syn_cdm (syn_cdif (syn_ccom (syn_cid) F) (syn_ccom (syn_ccompl (syn_cid)) F))))
      (syn_wex y (syn_wbr (.cv x)
          (syn_cdif (syn_ccom (syn_cid) F) (syn_ccom (syn_ccompl (syn_cid)) F)) (.cv y)))
      (syn_wex y (syn_wa (syn_wbr (.cv x) F (.cv y))
          (.all z (.imp (syn_wbr (.cv x) F (.cv z)) (.objEq z y)))))
      (syn_weu y (syn_wbr (.cv x) F (.cv y))) p0000 p0002 p0013
  have p0015 :=
    @g_eqabi (syn_weu y (syn_wbr (.cv x) F (.cv y))) x
      (syn_cdm (syn_cdif (syn_ccom (syn_cid) F) (syn_ccom (syn_ccompl (syn_cid)) F)))
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

@[expose]
noncomputable def g_fvfullfunlem2 (F : Class) :
    Nominal.NPrf
      (syn_wss (syn_cdif (syn_ccom (syn_cid) F) (syn_ccom (syn_ccompl (syn_cid)) F)) F) :=
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
    x ∉ ((syn_cdif (syn_ccom (syn_cid) F) (syn_ccom (syn_ccompl (syn_cid)) F))).fv :=
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
    y ∉ ((syn_cdif (syn_ccom (syn_cid) F) (syn_ccom (syn_ccompl (syn_cid)) F))).fv :=
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
    @g_simpl (syn_wbr (.cv x) F (.cv y))
      (.all z (.imp (syn_wbr (.cv x) F (.cv z)) (.objEq z y)))
  have p0001 :=
    @g_fnfullfunlem1 z (.cv x) (.cv y) F dv_cache_0001 dv_cache_0002 dv_cache_0003
  have p0002 :=
    (Nominal.biimpRefl (syn_wbr (.cv x)
        (syn_cdif (syn_ccom (syn_cid) F) (syn_ccom (syn_ccompl (syn_cid)) F)) (.cv y)))
  have p0003_e00_recanon :
    Nominal.NPrf
      (syn_wb (syn_wbr (.cv x)
          (syn_cdif (syn_ccom (syn_cid) F) (syn_ccom (syn_ccompl (syn_cid)) F)) (.cv y))
        (syn_wa (syn_wbr (.cv x) F (.cv y))
          (.all z (.imp (syn_wbr (.cv x) F (.cv z)) (.objEq z y))))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wb syn_wbr syn_cop syn_cun syn_cnin syn_wnan syn_wa syn_ccompl syn_wrex
          syn_wex syn_cphi syn_cdif syn_cin syn_ccom syn_copab syn_cid
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
    @g_bitr3i
      (syn_wa (syn_wbr (.cv x) F (.cv y))
        (.all z (.imp (syn_wbr (.cv x) F (.cv z)) (.objEq z y))))
      (syn_wbr (.cv x)
        (syn_cdif (syn_ccom (syn_cid) F) (syn_ccom (syn_ccompl (syn_cid)) F)) (.cv y))
      (.classMem (syn_cop (.cv x) (.cv y))
        (syn_cdif (syn_ccom (syn_cid) F) (syn_ccom (syn_ccompl (syn_cid)) F)))
      p0003_e00_recanon p0002
  have p0004 := (Nominal.biimpRefl (syn_wbr (.cv x) F (.cv y)))
  have p0005 :=
    @g_n_3imtr3i
      (syn_wa (syn_wbr (.cv x) F (.cv y))
        (.all z (.imp (syn_wbr (.cv x) F (.cv z)) (.objEq z y))))
      (syn_wbr (.cv x) F (.cv y))
      (.classMem (syn_cop (.cv x) (.cv y))
        (syn_cdif (syn_ccom (syn_cid) F) (syn_ccom (syn_ccompl (syn_cid)) F)))
      (.classMem (syn_cop (.cv x) (.cv y)) F) p0000 p0003 p0004
  have p0006 :=
    @g_gen2
      (.imp (.classMem (syn_cop (.cv x) (.cv y))
          (syn_cdif (syn_ccom (syn_cid) F) (syn_ccom (syn_ccompl (syn_cid)) F)))
        (.classMem (syn_cop (.cv x) (.cv y)) F))
      x y p0005
  have p0007 :=
    @g_ssrel x y (syn_cdif (syn_ccom (syn_cid) F) (syn_ccom (syn_ccompl (syn_cid)) F)) F
      dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008
  have p0008 :=
    @g_mpbir
      (syn_wss (syn_cdif (syn_ccom (syn_cid) F) (syn_ccom (syn_ccompl (syn_cid)) F)) F)
      (.all x (.all y (.imp (.classMem (syn_cop (.cv x) (.cv y))
              (syn_cdif (syn_ccom (syn_cid) F) (syn_ccom (syn_ccompl (syn_cid)) F)))
            (.classMem (syn_cop (.cv x) (.cv y)) F))))
      p0006 p0007
  exact p0008

@[expose]
noncomputable def g_fvfullfunlem3 (A : Class) (F : Class) :
    Nominal.NPrf
      (.imp (.classMem A
          (syn_cdm (syn_cdif (syn_ccom (syn_cid) F) (syn_ccom (syn_ccompl (syn_cid)) F))))
        (.classEq (syn_cfv (syn_cdif (syn_ccom (syn_cid) F) (syn_ccom (syn_ccompl (syn_cid)) F))
            A) (syn_cfv F A))) :=
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
      ((syn_cres F (syn_cdm
            (syn_cdif (syn_ccom (syn_cid) F) (syn_ccom (syn_ccompl (syn_cid)) F))))).fv :=
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
      ((syn_cres F (syn_cdm
            (syn_cdif (syn_ccom (syn_cid) F) (syn_ccom (syn_ccompl (syn_cid)) F))))).fv :=
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
      ((syn_cres F (syn_cdm
            (syn_cdif (syn_ccom (syn_cid) F) (syn_ccom (syn_ccompl (syn_cid)) F))))).fv :=
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
    @g_dffun2 x y z
      (syn_cres F
        (syn_cdm (syn_cdif (syn_ccom (syn_cid) F) (syn_ccom (syn_ccompl (syn_cid)) F))))
      dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006
  have p0001 :=
    @g_brres (.cv x) (.cv y) F
      (syn_cdm (syn_cdif (syn_ccom (syn_cid) F) (syn_ccom (syn_ccompl (syn_cid)) F)))
  have p0002 := @g_fvfullfunlem1 x z F dv_cache_0007 dv_cache_0008 dv_cache_0005
  have p0003 :=
    @g_eqabri (syn_weu z (syn_wbr (.cv x) F (.cv z))) x
      (syn_cdm (syn_cdif (syn_ccom (syn_cid) F) (syn_ccom (syn_ccompl (syn_cid)) F)))
      p0002
  have p0004 :=
    @g_anbi2i
      (.classMem (.cv x)
        (syn_cdm (syn_cdif (syn_ccom (syn_cid) F) (syn_ccom (syn_ccompl (syn_cid)) F))))
      (syn_weu z (syn_wbr (.cv x) F (.cv z))) (syn_wbr (.cv x) F (.cv y)) p0003
  have p0005 :=
    @g_bitri
      (syn_wbr (.cv x) (syn_cres F
          (syn_cdm (syn_cdif (syn_ccom (syn_cid) F) (syn_ccom (syn_ccompl (syn_cid)) F))))
        (.cv y))
      (syn_wa (syn_wbr (.cv x) F (.cv y)) (.classMem (.cv x) (syn_cdm
            (syn_cdif (syn_ccom (syn_cid) F) (syn_ccom (syn_ccompl (syn_cid)) F)))))
      (syn_wa (syn_wbr (.cv x) F (.cv y)) (syn_weu z (syn_wbr (.cv x) F (.cv z)))) p0001
      p0004
  have p0006 :=
    @g_brres (.cv x) (.cv z) F
      (syn_cdm (syn_cdif (syn_ccom (syn_cid) F) (syn_ccom (syn_ccompl (syn_cid)) F)))
  have p0007 := @g_fvfullfunlem1 x y F dv_cache_0007 dv_cache_0009 dv_cache_0004
  have p0008 :=
    @g_eqabri (syn_weu y (syn_wbr (.cv x) F (.cv y))) x
      (syn_cdm (syn_cdif (syn_ccom (syn_cid) F) (syn_ccom (syn_ccompl (syn_cid)) F)))
      p0007
  have p0009 :=
    @g_anbi2i
      (.classMem (.cv x)
        (syn_cdm (syn_cdif (syn_ccom (syn_cid) F) (syn_ccom (syn_ccompl (syn_cid)) F))))
      (syn_weu y (syn_wbr (.cv x) F (.cv y))) (syn_wbr (.cv x) F (.cv z)) p0008
  have p0010 :=
    @g_bitri
      (syn_wbr (.cv x) (syn_cres F
          (syn_cdm (syn_cdif (syn_ccom (syn_cid) F) (syn_ccom (syn_ccompl (syn_cid)) F))))
        (.cv z))
      (syn_wa (syn_wbr (.cv x) F (.cv z)) (.classMem (.cv x) (syn_cdm
            (syn_cdif (syn_ccom (syn_cid) F) (syn_ccom (syn_ccompl (syn_cid)) F)))))
      (syn_wa (syn_wbr (.cv x) F (.cv z)) (syn_weu y (syn_wbr (.cv x) F (.cv y)))) p0006
      p0009
  have p0011 := @g_tz6_12_1 y (.cv x) (.cv y) F dv_cache_0010 dv_cache_0009
  have p0012 :=
    @g_adantrl (syn_wbr (.cv x) F (.cv y)) (syn_weu y (syn_wbr (.cv x) F (.cv y)))
      (.classEq (syn_cfv F (.cv x)) (.cv y)) (syn_wbr (.cv x) F (.cv z)) p0011
  have p0013 := @g_tz6_12_1 y (.cv x) (.cv z) F dv_cache_0010 dv_cache_0009
  have p0014 :=
    @g_adantl (syn_wa (syn_wbr (.cv x) F (.cv z)) (syn_weu y (syn_wbr (.cv x) F (.cv y))))
      (.classEq (syn_cfv F (.cv x)) (.cv z)) (syn_wbr (.cv x) F (.cv y)) p0013
  have p0015 :=
    @g_eqtr3d
      (syn_wa (syn_wbr (.cv x) F (.cv y))
        (syn_wa (syn_wbr (.cv x) F (.cv z)) (syn_weu y (syn_wbr (.cv x) F (.cv y)))))
      (syn_cfv F (.cv x)) (.cv y) (.cv z) p0012 p0014
  have p0016_e00_recanon :
    Nominal.NPrf
      (.imp (syn_wa (syn_wbr (.cv x) F (.cv y))
          (syn_wa (syn_wbr (.cv x) F (.cv z)) (syn_weu y (syn_wbr (.cv x) F (.cv y)))))
        (.objEq y z)) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wa syn_wbr syn_cop syn_cun syn_cnin syn_wnan syn_ccompl syn_wrex
          syn_wex syn_cphi
        simp (config :=
          { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_class_cv]
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · exact Nominal.RecanonTransportDev.TRecanonWff.same _
        · exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _)
      p0015
  have p0016 :=
    @g_adantlr (syn_wbr (.cv x) F (.cv y))
      (syn_wa (syn_wbr (.cv x) F (.cv z)) (syn_weu y (syn_wbr (.cv x) F (.cv y))))
      (.objEq y z) (syn_weu z (syn_wbr (.cv x) F (.cv z))) p0016_e00_recanon
  have p0017 :=
    @g_syl2anb
      (syn_wbr (.cv x) (syn_cres F
          (syn_cdm (syn_cdif (syn_ccom (syn_cid) F) (syn_ccom (syn_ccompl (syn_cid)) F))))
        (.cv y))
      (syn_wa (syn_wbr (.cv x) F (.cv y)) (syn_weu z (syn_wbr (.cv x) F (.cv z))))
      (syn_wa (syn_wbr (.cv x) F (.cv z)) (syn_weu y (syn_wbr (.cv x) F (.cv y))))
      (.objEq y z)
      (syn_wbr (.cv x) (syn_cres F
          (syn_cdm (syn_cdif (syn_ccom (syn_cid) F) (syn_ccom (syn_ccompl (syn_cid)) F))))
        (.cv z))
      p0005 p0010 p0016
  have p0018 :=
    @g_gen2
      (.imp (syn_wa (syn_wbr (.cv x) (syn_cres F (syn_cdm
                (syn_cdif (syn_ccom (syn_cid) F) (syn_ccom (syn_ccompl (syn_cid)) F)))) (.cv y))
          (syn_wbr (.cv x) (syn_cres F (syn_cdm
                (syn_cdif (syn_ccom (syn_cid) F) (syn_ccom (syn_ccompl (syn_cid)) F))))
            (.cv z))) (.objEq y z))
      y z p0017
  have p0019 :=
    @g_mpgbir
      (syn_wfun (syn_cres F (syn_cdm
            (syn_cdif (syn_ccom (syn_cid) F) (syn_ccom (syn_ccompl (syn_cid)) F)))))
      (.all y (.all z (.imp (syn_wa (syn_wbr (.cv x) (syn_cres F (syn_cdm
                    (syn_cdif (syn_ccom (syn_cid) F) (syn_ccom (syn_ccompl (syn_cid)) F))))
                (.cv y)) (syn_wbr (.cv x) (syn_cres F (syn_cdm (syn_cdif (syn_ccom (syn_cid) F)
                      (syn_ccom (syn_ccompl (syn_cid)) F)))) (.cv z))) (.objEq y z))))
      x p0000 p0018
  have p0020 := @g_fvfullfunlem2 F
  have p0021 :=
    @g_ssdmrn (syn_cdif (syn_ccom (syn_cid) F) (syn_ccom (syn_ccompl (syn_cid)) F))
  have p0022 :=
    @g_ssv (syn_crn (syn_cdif (syn_ccom (syn_cid) F) (syn_ccom (syn_ccompl (syn_cid)) F)))
  have p0023 :=
    @g_xpss2
      (syn_crn (syn_cdif (syn_ccom (syn_cid) F) (syn_ccom (syn_ccompl (syn_cid)) F)))
      (syn_cvv)
      (syn_cdm (syn_cdif (syn_ccom (syn_cid) F) (syn_ccom (syn_ccompl (syn_cid)) F)))
  have p0024 := Nominal.mp p0022 p0023
  have p0025 :=
    @g_sstri (syn_cdif (syn_ccom (syn_cid) F) (syn_ccom (syn_ccompl (syn_cid)) F))
      (syn_cxp (syn_cdm (syn_cdif (syn_ccom (syn_cid) F) (syn_ccom (syn_ccompl (syn_cid)) F)))
        (syn_crn (syn_cdif (syn_ccom (syn_cid) F) (syn_ccom (syn_ccompl (syn_cid)) F))))
      (syn_cxp (syn_cdm (syn_cdif (syn_ccom (syn_cid) F) (syn_ccom (syn_ccompl (syn_cid)) F)))
        (syn_cvv))
      p0021 p0024
  have p0026 :=
    @g_ssini (syn_cdif (syn_ccom (syn_cid) F) (syn_ccom (syn_ccompl (syn_cid)) F)) F
      (syn_cxp (syn_cdm (syn_cdif (syn_ccom (syn_cid) F) (syn_ccom (syn_ccompl (syn_cid)) F)))
        (syn_cvv))
      p0020 p0025
  have p0027 :=
    (Nominal.classEqRefl (syn_cres F
        (syn_cdm (syn_cdif (syn_ccom (syn_cid) F) (syn_ccom (syn_ccompl (syn_cid)) F)))))
  have p0028 :=
    @g_sseqtr4i (syn_cdif (syn_ccom (syn_cid) F) (syn_ccom (syn_ccompl (syn_cid)) F))
      (syn_cin F (syn_cxp
          (syn_cdm (syn_cdif (syn_ccom (syn_cid) F) (syn_ccom (syn_ccompl (syn_cid)) F)))
          (syn_cvv)))
      (syn_cres F
        (syn_cdm (syn_cdif (syn_ccom (syn_cid) F) (syn_ccom (syn_ccompl (syn_cid)) F))))
      p0026 p0027
  have p0029 :=
    @g_funssfv A
      (syn_cres F
        (syn_cdm (syn_cdif (syn_ccom (syn_cid) F) (syn_ccom (syn_ccompl (syn_cid)) F))))
      (syn_cdif (syn_ccom (syn_cid) F) (syn_ccom (syn_ccompl (syn_cid)) F))
  have p0030 :=
    @g_mp3an12
      (syn_wfun (syn_cres F (syn_cdm
            (syn_cdif (syn_ccom (syn_cid) F) (syn_ccom (syn_ccompl (syn_cid)) F)))))
      (syn_wss (syn_cdif (syn_ccom (syn_cid) F) (syn_ccom (syn_ccompl (syn_cid)) F)) (syn_cres F
          (syn_cdm (syn_cdif (syn_ccom (syn_cid) F) (syn_ccom (syn_ccompl (syn_cid)) F)))))
      (.classMem A
        (syn_cdm (syn_cdif (syn_ccom (syn_cid) F) (syn_ccom (syn_ccompl (syn_cid)) F))))
      (.classEq (syn_cfv (syn_cres F (syn_cdm
              (syn_cdif (syn_ccom (syn_cid) F) (syn_ccom (syn_ccompl (syn_cid)) F)))) A)
        (syn_cfv (syn_cdif (syn_ccom (syn_cid) F) (syn_ccom (syn_ccompl (syn_cid)) F)) A))
      p0019 p0028 p0029
  have p0031 :=
    @g_fvres A
      (syn_cdm (syn_cdif (syn_ccom (syn_cid) F) (syn_ccom (syn_ccompl (syn_cid)) F))) F
  have p0032 :=
    @g_eqtr3d
      (.classMem A
        (syn_cdm (syn_cdif (syn_ccom (syn_cid) F) (syn_ccom (syn_ccompl (syn_cid)) F))))
      (syn_cfv (syn_cres F
          (syn_cdm (syn_cdif (syn_ccom (syn_cid) F) (syn_ccom (syn_ccompl (syn_cid)) F)))) A)
      (syn_cfv (syn_cdif (syn_ccom (syn_cid) F) (syn_ccom (syn_ccompl (syn_cid)) F)) A)
      (syn_cfv F A) p0030 p0031
  exact p0032

@[expose]
noncomputable def g_fvfullfun (A : Class) (F : Class) :
    Nominal.NPrf (.classEq (syn_cfv (syn_cfullfun F) A) (syn_cfv F A)) :=
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
    x ∉ ((Wff.classEq (syn_cfv (syn_cfullfun F) A) (syn_cfv F A))).fv :=
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
  have p0000 := @g_fveq2 (.cv x) A (syn_cfullfun F)
  have p0001 := @g_fveq2 (.cv x) A F
  have p0002 :=
    @g_eqeq12d (.classEq (.cv x) A) (syn_cfv (syn_cfullfun F) (.cv x))
      (syn_cfv (syn_cfullfun F) A) (syn_cfv F (.cv x)) (syn_cfv F A) p0000 p0001
  have p0003 := (Nominal.classEqRefl (syn_cfullfun F))
  have p0004 :=
    @g_fveq1i (.cv x) (syn_cfullfun F)
      (syn_cun (syn_cdif (syn_ccom (syn_cid) F) (syn_ccom (syn_ccompl (syn_cid)) F)) (syn_cxp
          (syn_ccompl (syn_cdm
              (syn_cdif (syn_ccom (syn_cid) F) (syn_ccom (syn_ccompl (syn_cid)) F))))
          (syn_csn (syn_c0))))
      p0003
  have p0005 :=
    @g_incompl
      (syn_cdm (syn_cdif (syn_ccom (syn_cid) F) (syn_ccom (syn_ccompl (syn_cid)) F)))
  have p0006 := @g_fnfullfunlem2 F
  have p0007 :=
    @g_funfn (syn_cdif (syn_ccom (syn_cid) F) (syn_ccom (syn_ccompl (syn_cid)) F))
  have p0008 :=
    @g_mpbi
      (syn_wfun (syn_cdif (syn_ccom (syn_cid) F) (syn_ccom (syn_ccompl (syn_cid)) F)))
      (syn_wfn (syn_cdif (syn_ccom (syn_cid) F) (syn_ccom (syn_ccompl (syn_cid)) F))
        (syn_cdm (syn_cdif (syn_ccom (syn_cid) F) (syn_ccom (syn_ccompl (syn_cid)) F))))
      p0006 p0007
  have p0009 := @g_n_0ex
  have p0010 :=
    @g_fnconstg
      (syn_ccompl
        (syn_cdm (syn_cdif (syn_ccom (syn_cid) F) (syn_ccom (syn_ccompl (syn_cid)) F))))
      (syn_c0) (syn_cvv)
  have p0011 := Nominal.mp p0009 p0010
  have p0012 :=
    @g_fvun1
      (syn_cdm (syn_cdif (syn_ccom (syn_cid) F) (syn_ccom (syn_ccompl (syn_cid)) F)))
      (syn_ccompl
        (syn_cdm (syn_cdif (syn_ccom (syn_cid) F) (syn_ccom (syn_ccompl (syn_cid)) F))))
      (syn_cdif (syn_ccom (syn_cid) F) (syn_ccom (syn_ccompl (syn_cid)) F))
      (syn_cxp (syn_ccompl
          (syn_cdm (syn_cdif (syn_ccom (syn_cid) F) (syn_ccom (syn_ccompl (syn_cid)) F))))
        (syn_csn (syn_c0)))
      (.cv x)
  have p0013 :=
    @g_mp3an12
      (syn_wfn (syn_cdif (syn_ccom (syn_cid) F) (syn_ccom (syn_ccompl (syn_cid)) F))
        (syn_cdm (syn_cdif (syn_ccom (syn_cid) F) (syn_ccom (syn_ccompl (syn_cid)) F))))
      (syn_wfn (syn_cxp (syn_ccompl (syn_cdm
              (syn_cdif (syn_ccom (syn_cid) F) (syn_ccom (syn_ccompl (syn_cid)) F))))
          (syn_csn (syn_c0))) (syn_ccompl (syn_cdm
            (syn_cdif (syn_ccom (syn_cid) F) (syn_ccom (syn_ccompl (syn_cid)) F)))))
      (syn_wa (.classEq (syn_cin (syn_cdm
              (syn_cdif (syn_ccom (syn_cid) F) (syn_ccom (syn_ccompl (syn_cid)) F))) (syn_ccompl
              (syn_cdm (syn_cdif (syn_ccom (syn_cid) F) (syn_ccom (syn_ccompl (syn_cid)) F)))))
          (syn_c0)) (.classMem (.cv x) (syn_cdm
            (syn_cdif (syn_ccom (syn_cid) F) (syn_ccom (syn_ccompl (syn_cid)) F)))))
      (.classEq (syn_cfv
          (syn_cun (syn_cdif (syn_ccom (syn_cid) F) (syn_ccom (syn_ccompl (syn_cid)) F))
            (syn_cxp (syn_ccompl (syn_cdm
                  (syn_cdif (syn_ccom (syn_cid) F) (syn_ccom (syn_ccompl (syn_cid)) F))))
              (syn_csn (syn_c0)))) (.cv x))
        (syn_cfv (syn_cdif (syn_ccom (syn_cid) F) (syn_ccom (syn_ccompl (syn_cid)) F)) (.cv x)))
      p0008 p0011 p0012
  have p0014 :=
    @g_mpan
      (.classEq (syn_cin
          (syn_cdm (syn_cdif (syn_ccom (syn_cid) F) (syn_ccom (syn_ccompl (syn_cid)) F)))
          (syn_ccompl (syn_cdm
              (syn_cdif (syn_ccom (syn_cid) F) (syn_ccom (syn_ccompl (syn_cid)) F))))) (syn_c0))
      (.classMem (.cv x)
        (syn_cdm (syn_cdif (syn_ccom (syn_cid) F) (syn_ccom (syn_ccompl (syn_cid)) F))))
      (.classEq (syn_cfv
          (syn_cun (syn_cdif (syn_ccom (syn_cid) F) (syn_ccom (syn_ccompl (syn_cid)) F))
            (syn_cxp (syn_ccompl (syn_cdm
                  (syn_cdif (syn_ccom (syn_cid) F) (syn_ccom (syn_ccompl (syn_cid)) F))))
              (syn_csn (syn_c0)))) (.cv x))
        (syn_cfv (syn_cdif (syn_ccom (syn_cid) F) (syn_ccom (syn_ccompl (syn_cid)) F)) (.cv x)))
      p0005 p0013
  have p0015 := @g_fvfullfunlem3 (.cv x) F
  have p0016 :=
    @g_eqtrd
      (.classMem (.cv x)
        (syn_cdm (syn_cdif (syn_ccom (syn_cid) F) (syn_ccom (syn_ccompl (syn_cid)) F))))
      (syn_cfv (syn_cun (syn_cdif (syn_ccom (syn_cid) F) (syn_ccom (syn_ccompl (syn_cid)) F))
          (syn_cxp (syn_ccompl (syn_cdm
                (syn_cdif (syn_ccom (syn_cid) F) (syn_ccom (syn_ccompl (syn_cid)) F))))
            (syn_csn (syn_c0)))) (.cv x))
      (syn_cfv (syn_cdif (syn_ccom (syn_cid) F) (syn_ccom (syn_ccompl (syn_cid)) F)) (.cv x))
      (syn_cfv F (.cv x)) p0014 p0015
  have p0017 := @g_vex x
  have p0018 :=
    @g_elcompl (.cv x)
      (syn_cdm (syn_cdif (syn_ccom (syn_cid) F) (syn_ccom (syn_ccompl (syn_cid)) F)))
      p0017
  have p0019 :=
    @g_fvun2
      (syn_cdm (syn_cdif (syn_ccom (syn_cid) F) (syn_ccom (syn_ccompl (syn_cid)) F)))
      (syn_ccompl
        (syn_cdm (syn_cdif (syn_ccom (syn_cid) F) (syn_ccom (syn_ccompl (syn_cid)) F))))
      (syn_cdif (syn_ccom (syn_cid) F) (syn_ccom (syn_ccompl (syn_cid)) F))
      (syn_cxp (syn_ccompl
          (syn_cdm (syn_cdif (syn_ccom (syn_cid) F) (syn_ccom (syn_ccompl (syn_cid)) F))))
        (syn_csn (syn_c0)))
      (.cv x)
  have p0020 :=
    @g_mp3an12
      (syn_wfn (syn_cdif (syn_ccom (syn_cid) F) (syn_ccom (syn_ccompl (syn_cid)) F))
        (syn_cdm (syn_cdif (syn_ccom (syn_cid) F) (syn_ccom (syn_ccompl (syn_cid)) F))))
      (syn_wfn (syn_cxp (syn_ccompl (syn_cdm
              (syn_cdif (syn_ccom (syn_cid) F) (syn_ccom (syn_ccompl (syn_cid)) F))))
          (syn_csn (syn_c0))) (syn_ccompl (syn_cdm
            (syn_cdif (syn_ccom (syn_cid) F) (syn_ccom (syn_ccompl (syn_cid)) F)))))
      (syn_wa (.classEq (syn_cin (syn_cdm
              (syn_cdif (syn_ccom (syn_cid) F) (syn_ccom (syn_ccompl (syn_cid)) F))) (syn_ccompl
              (syn_cdm (syn_cdif (syn_ccom (syn_cid) F) (syn_ccom (syn_ccompl (syn_cid)) F)))))
          (syn_c0)) (.classMem (.cv x) (syn_ccompl (syn_cdm
              (syn_cdif (syn_ccom (syn_cid) F) (syn_ccom (syn_ccompl (syn_cid)) F))))))
      (.classEq (syn_cfv
          (syn_cun (syn_cdif (syn_ccom (syn_cid) F) (syn_ccom (syn_ccompl (syn_cid)) F))
            (syn_cxp (syn_ccompl (syn_cdm
                  (syn_cdif (syn_ccom (syn_cid) F) (syn_ccom (syn_ccompl (syn_cid)) F))))
              (syn_csn (syn_c0)))) (.cv x)) (syn_cfv (syn_cxp (syn_ccompl (syn_cdm
                (syn_cdif (syn_ccom (syn_cid) F) (syn_ccom (syn_ccompl (syn_cid)) F))))
            (syn_csn (syn_c0))) (.cv x)))
      p0008 p0011 p0019
  have p0021 :=
    @g_mpan
      (.classEq (syn_cin
          (syn_cdm (syn_cdif (syn_ccom (syn_cid) F) (syn_ccom (syn_ccompl (syn_cid)) F)))
          (syn_ccompl (syn_cdm
              (syn_cdif (syn_ccom (syn_cid) F) (syn_ccom (syn_ccompl (syn_cid)) F))))) (syn_c0))
      (.classMem (.cv x) (syn_ccompl (syn_cdm
            (syn_cdif (syn_ccom (syn_cid) F) (syn_ccom (syn_ccompl (syn_cid)) F)))))
      (.classEq (syn_cfv
          (syn_cun (syn_cdif (syn_ccom (syn_cid) F) (syn_ccom (syn_ccompl (syn_cid)) F))
            (syn_cxp (syn_ccompl (syn_cdm
                  (syn_cdif (syn_ccom (syn_cid) F) (syn_ccom (syn_ccompl (syn_cid)) F))))
              (syn_csn (syn_c0)))) (.cv x)) (syn_cfv (syn_cxp (syn_ccompl (syn_cdm
                (syn_cdif (syn_ccom (syn_cid) F) (syn_ccom (syn_ccompl (syn_cid)) F))))
            (syn_csn (syn_c0))) (.cv x)))
      p0005 p0020
  have p0022 :=
    @g_sylbir
      (.neg (.classMem (.cv x) (syn_cdm
            (syn_cdif (syn_ccom (syn_cid) F) (syn_ccom (syn_ccompl (syn_cid)) F)))))
      (.classMem (.cv x) (syn_ccompl (syn_cdm
            (syn_cdif (syn_ccom (syn_cid) F) (syn_ccom (syn_ccompl (syn_cid)) F)))))
      (.classEq (syn_cfv
          (syn_cun (syn_cdif (syn_ccom (syn_cid) F) (syn_ccom (syn_ccompl (syn_cid)) F))
            (syn_cxp (syn_ccompl (syn_cdm
                  (syn_cdif (syn_ccom (syn_cid) F) (syn_ccom (syn_ccompl (syn_cid)) F))))
              (syn_csn (syn_c0)))) (.cv x)) (syn_cfv (syn_cxp (syn_ccompl (syn_cdm
                (syn_cdif (syn_ccom (syn_cid) F) (syn_ccom (syn_ccompl (syn_cid)) F))))
            (syn_csn (syn_c0))) (.cv x)))
      p0018 p0021
  have p0023 := @g_fvfullfunlem1 x y F dv_cache_0001 dv_cache_0002 dv_cache_0003
  have p0024 :=
    @g_eqabri (syn_weu y (syn_wbr (.cv x) F (.cv y))) x
      (syn_cdm (syn_cdif (syn_ccom (syn_cid) F) (syn_ccom (syn_ccompl (syn_cid)) F)))
      p0023
  have p0025 := @g_tz6_12_2 y (.cv x) F dv_cache_0004 dv_cache_0002
  have p0026 :=
    @g_sylnbi
      (.classMem (.cv x)
        (syn_cdm (syn_cdif (syn_ccom (syn_cid) F) (syn_ccom (syn_ccompl (syn_cid)) F))))
      (syn_weu y (syn_wbr (.cv x) F (.cv y))) (.classEq (syn_cfv F (.cv x)) (syn_c0))
      p0024 p0025
  have p0028 :=
    @g_fvconst2
      (syn_ccompl
        (syn_cdm (syn_cdif (syn_ccom (syn_cid) F) (syn_ccom (syn_ccompl (syn_cid)) F))))
      (syn_c0) (.cv x) p0009
  have p0029 :=
    @g_sylbir
      (.neg (.classMem (.cv x) (syn_cdm
            (syn_cdif (syn_ccom (syn_cid) F) (syn_ccom (syn_ccompl (syn_cid)) F)))))
      (.classMem (.cv x) (syn_ccompl (syn_cdm
            (syn_cdif (syn_ccom (syn_cid) F) (syn_ccom (syn_ccompl (syn_cid)) F)))))
      (.classEq (syn_cfv (syn_cxp (syn_ccompl (syn_cdm
                (syn_cdif (syn_ccom (syn_cid) F) (syn_ccom (syn_ccompl (syn_cid)) F))))
            (syn_csn (syn_c0))) (.cv x)) (syn_c0))
      p0018 p0028
  have p0030 :=
    @g_eqtr4d
      (.neg (.classMem (.cv x) (syn_cdm
            (syn_cdif (syn_ccom (syn_cid) F) (syn_ccom (syn_ccompl (syn_cid)) F)))))
      (syn_cfv F (.cv x)) (syn_c0)
      (syn_cfv (syn_cxp (syn_ccompl (syn_cdm
              (syn_cdif (syn_ccom (syn_cid) F) (syn_ccom (syn_ccompl (syn_cid)) F))))
          (syn_csn (syn_c0))) (.cv x))
      p0026 p0029
  have p0031 :=
    @g_eqtr4d
      (.neg (.classMem (.cv x) (syn_cdm
            (syn_cdif (syn_ccom (syn_cid) F) (syn_ccom (syn_ccompl (syn_cid)) F)))))
      (syn_cfv (syn_cun (syn_cdif (syn_ccom (syn_cid) F) (syn_ccom (syn_ccompl (syn_cid)) F))
          (syn_cxp (syn_ccompl (syn_cdm
                (syn_cdif (syn_ccom (syn_cid) F) (syn_ccom (syn_ccompl (syn_cid)) F))))
            (syn_csn (syn_c0)))) (.cv x))
      (syn_cfv (syn_cxp (syn_ccompl (syn_cdm
              (syn_cdif (syn_ccom (syn_cid) F) (syn_ccom (syn_ccompl (syn_cid)) F))))
          (syn_csn (syn_c0))) (.cv x))
      (syn_cfv F (.cv x)) p0022 p0030
  have p0032 :=
    @g_pm2_61i
      (.classMem (.cv x)
        (syn_cdm (syn_cdif (syn_ccom (syn_cid) F) (syn_ccom (syn_ccompl (syn_cid)) F))))
      (.classEq (syn_cfv
          (syn_cun (syn_cdif (syn_ccom (syn_cid) F) (syn_ccom (syn_ccompl (syn_cid)) F))
            (syn_cxp (syn_ccompl (syn_cdm
                  (syn_cdif (syn_ccom (syn_cid) F) (syn_ccom (syn_ccompl (syn_cid)) F))))
              (syn_csn (syn_c0)))) (.cv x)) (syn_cfv F (.cv x)))
      p0016 p0031
  have p0033 :=
    @g_eqtri (syn_cfv (syn_cfullfun F) (.cv x))
      (syn_cfv (syn_cun (syn_cdif (syn_ccom (syn_cid) F) (syn_ccom (syn_ccompl (syn_cid)) F))
          (syn_cxp (syn_ccompl (syn_cdm
                (syn_cdif (syn_ccom (syn_cid) F) (syn_ccom (syn_ccompl (syn_cid)) F))))
            (syn_csn (syn_c0)))) (.cv x))
      (syn_cfv F (.cv x)) p0004 p0032
  have p0034 :=
    @g_vtoclg (.classEq (syn_cfv (syn_cfullfun F) (.cv x)) (syn_cfv F (.cv x)))
      (.classEq (syn_cfv (syn_cfullfun F) A) (syn_cfv F A)) x A (syn_cvv) dv_cache_0005
      dv_cache_0006 p0002 p0033
  have p0035 := @g_fvprc A (syn_cfullfun F)
  have p0036 := @g_fvprc A F
  have p0037 :=
    @g_eqtr4d (.neg (.classMem A (syn_cvv))) (syn_cfv (syn_cfullfun F) A) (syn_c0)
      (syn_cfv F A) p0035 p0036
  have p0038 :=
    @g_pm2_61i (.classMem A (syn_cvv))
      (.classEq (syn_cfv (syn_cfullfun F) A) (syn_cfv F A)) p0034 p0037
  exact p0038

@[expose]
noncomputable def g_fvdomfn (A : Class) (V : Class) :
    Nominal.NPrf (.imp (.classMem A V) (.classEq (syn_cfv (syn_cdomfn) A) (syn_cdm A))) :=
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
  have dv_cache_0002 : x ∉ ((syn_cdm A)).fv :=
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
  have dv_cache_0003 : x ∉ ((syn_cvv)).fv :=
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
  have p0000 := @g_elex A V
  have p0001 := @g_dmexg A (syn_cvv)
  have p0002 := @g_dmeq (.cv x) A
  have p0003 := NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominal_df_domfn x
  have p0004 :=
    @g_fvmptg x A (syn_cdm (.cv x)) (syn_cdm A) (syn_cvv) (syn_cvv) (syn_cdomfn)
      dv_cache_0001 dv_cache_0002 dv_cache_0003 p0002 p0003
  have p0005 :=
    @g_mpdan (.classMem A (syn_cvv)) (.classMem (syn_cdm A) (syn_cvv))
      (.classEq (syn_cfv (syn_cdomfn) A) (syn_cdm A)) p0001 p0004
  have p0006 :=
    @g_syl (.classMem A V) (.classMem A (syn_cvv))
      (.classEq (syn_cfv (syn_cdomfn) A) (syn_cdm A)) p0000 p0005
  exact p0006

@[expose]
noncomputable def g_fvranfn (A : Class) (V : Class) :
    Nominal.NPrf (.imp (.classMem A V) (.classEq (syn_cfv (syn_cranfn) A) (syn_crn A))) :=
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
  have dv_cache_0002 : x ∉ ((syn_crn A)).fv :=
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
  have dv_cache_0003 : x ∉ ((syn_cvv)).fv :=
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
  have p0000 := @g_elex A V
  have p0001 := @g_rnexg A (syn_cvv)
  have p0002 := @g_rneq (.cv x) A
  have p0003 := NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominal_df_ranfn x
  have p0004 :=
    @g_fvmptg x A (syn_crn (.cv x)) (syn_crn A) (syn_cvv) (syn_cvv) (syn_cranfn)
      dv_cache_0001 dv_cache_0002 dv_cache_0003 p0002 p0003
  have p0005 :=
    @g_mpdan (.classMem A (syn_cvv)) (.classMem (syn_crn A) (syn_cvv))
      (.classEq (syn_cfv (syn_cranfn) A) (syn_crn A)) p0001 p0004
  have p0006 :=
    @g_syl (.classMem A V) (.classMem A (syn_cvv))
      (.classEq (syn_cfv (syn_cranfn) A) (syn_crn A)) p0000 p0005
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

@[expose]
noncomputable def g_domfnex : Nominal.NPrf (.classMem (syn_cdomfn) (syn_cvv)) :=
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
    w ∉ ((syn_cop (syn_csn (.cv z)) (syn_cop (syn_csn (.cv y)) (.cv x)))).fv := by
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
      ((syn_cin (syn_cins4 (syn_csi3 (syn_cswap))) (syn_cins2 (syn_cins2 (syn_csset))))).fv :=
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
  have dv_cache_0003 : w ∉ ((syn_cop (.cv y) (.cv z))).fv :=
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
  have dv_cache_0005 : z ∉ ((syn_cop (syn_csn (.cv y)) (.cv x))).fv :=
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
      ((syn_cima
          (syn_cin (syn_cins4 (syn_csi3 (syn_cswap))) (syn_cins2 (syn_cins2 (syn_csset))))
          (syn_c1c))).fv :=
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
  have dv_cache_0009 : x ∉ ((syn_cvv)).fv :=
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
      ((syn_cima (syn_cima (syn_cin (syn_cins4 (syn_csi3 (syn_cswap)))
              (syn_cins2 (syn_cins2 (syn_csset)))) (syn_c1c)) (syn_c1c))).fv :=
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
      ((syn_cima (syn_cima (syn_cin (syn_cins4 (syn_csi3 (syn_cswap)))
              (syn_cins2 (syn_cins2 (syn_csset)))) (syn_c1c)) (syn_c1c))).fv :=
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
  have dv_cache_0012 : y ∉ ((syn_cdm (.cv x))).fv :=
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
  have p0000 := NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominal_df_domfn x
  have p0001 :=
    @g_elin
      (syn_cop (syn_csn (.cv w))
        (syn_cop (syn_csn (.cv z)) (syn_cop (syn_csn (.cv y)) (.cv x))))
      (syn_cins4 (syn_csi3 (syn_cswap))) (syn_cins2 (syn_cins2 (syn_csset)))
  have p0002 := @g_vex x
  have p0003 :=
    @g_oqelins4 (syn_csn (.cv w)) (syn_csn (.cv z)) (syn_csn (.cv y)) (.cv x)
      (syn_csi3 (syn_cswap)) p0002
  have p0004 := @g_vex w
  have p0005 := @g_vex z
  have p0006 := @g_vex y
  have p0007 := @g_otsnelsi3 (.cv w) (.cv z) (.cv y) (syn_cswap) p0004 p0005 p0006
  have p0008 :=
    (Nominal.biimpRefl (syn_wbr (.cv w) (syn_cswap) (syn_cop (.cv z) (.cv y))))
  have p0009 := @g_brswap2 (.cv w) (.cv z) (.cv y) p0005 p0006
  have p0010 :=
    @g_n_3bitr2i
      (.classMem (syn_cop (syn_csn (.cv w)) (syn_cop (syn_csn (.cv z)) (syn_csn (.cv y))))
        (syn_csi3 (syn_cswap)))
      (.classMem (syn_cop (.cv w) (syn_cop (.cv z) (.cv y))) (syn_cswap))
      (syn_wbr (.cv w) (syn_cswap) (syn_cop (.cv z) (.cv y)))
      (.classEq (.cv w) (syn_cop (.cv y) (.cv z))) p0007 p0008 p0009
  have p0011 :=
    @g_bitri
      (.classMem (syn_cop (syn_csn (.cv w))
          (syn_cop (syn_csn (.cv z)) (syn_cop (syn_csn (.cv y)) (.cv x))))
        (syn_cins4 (syn_csi3 (syn_cswap))))
      (.classMem (syn_cop (syn_csn (.cv w)) (syn_cop (syn_csn (.cv z)) (syn_csn (.cv y))))
        (syn_csi3 (syn_cswap)))
      (.classEq (.cv w) (syn_cop (.cv y) (.cv z))) p0003 p0010
  have p0012 := @g_snex (.cv z)
  have p0013 :=
    @g_otelins2 (syn_csn (.cv w)) (syn_csn (.cv z)) (syn_cop (syn_csn (.cv y)) (.cv x))
      (syn_cins2 (syn_csset)) p0012
  have p0014 := @g_snex (.cv y)
  have p0015 := @g_otelins2 (syn_csn (.cv w)) (syn_csn (.cv y)) (.cv x) (syn_csset) p0014
  have p0016 := @g_opelssetsn (.cv w) (.cv x) p0004 p0002
  have p0017_e01_recanon :
    Nominal.NPrf
      (syn_wb (.classMem (syn_cop (syn_csn (.cv w)) (.cv x)) (syn_csset)) (.objMem w x)) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wb syn_cop syn_cun syn_cnin syn_wnan syn_wa syn_ccompl syn_wrex syn_wex
          syn_cphi syn_csn syn_csset syn_copab syn_wss syn_cin
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
    @g_bitri
      (.classMem (syn_cop (syn_csn (.cv w)) (syn_cop (syn_csn (.cv y)) (.cv x)))
        (syn_cins2 (syn_csset)))
      (.classMem (syn_cop (syn_csn (.cv w)) (.cv x)) (syn_csset)) (.objMem w x) p0015
      p0017_e01_recanon
  have p0018 :=
    @g_bitri
      (.classMem (syn_cop (syn_csn (.cv w))
          (syn_cop (syn_csn (.cv z)) (syn_cop (syn_csn (.cv y)) (.cv x))))
        (syn_cins2 (syn_cins2 (syn_csset))))
      (.classMem (syn_cop (syn_csn (.cv w)) (syn_cop (syn_csn (.cv y)) (.cv x)))
        (syn_cins2 (syn_csset)))
      (.objMem w x) p0013 p0017
  have p0019 :=
    @g_anbi12i
      (.classMem (syn_cop (syn_csn (.cv w))
          (syn_cop (syn_csn (.cv z)) (syn_cop (syn_csn (.cv y)) (.cv x))))
        (syn_cins4 (syn_csi3 (syn_cswap))))
      (.classEq (.cv w) (syn_cop (.cv y) (.cv z)))
      (.classMem (syn_cop (syn_csn (.cv w))
          (syn_cop (syn_csn (.cv z)) (syn_cop (syn_csn (.cv y)) (.cv x))))
        (syn_cins2 (syn_cins2 (syn_csset))))
      (.objMem w x) p0011 p0018
  have p0020 :=
    @g_bitri
      (.classMem (syn_cop (syn_csn (.cv w))
          (syn_cop (syn_csn (.cv z)) (syn_cop (syn_csn (.cv y)) (.cv x))))
        (syn_cin (syn_cins4 (syn_csi3 (syn_cswap))) (syn_cins2 (syn_cins2 (syn_csset)))))
      (syn_wa (.classMem (syn_cop (syn_csn (.cv w))
            (syn_cop (syn_csn (.cv z)) (syn_cop (syn_csn (.cv y)) (.cv x))))
          (syn_cins4 (syn_csi3 (syn_cswap)))) (.classMem (syn_cop (syn_csn (.cv w))
            (syn_cop (syn_csn (.cv z)) (syn_cop (syn_csn (.cv y)) (.cv x))))
          (syn_cins2 (syn_cins2 (syn_csset)))))
      (syn_wa (.classEq (.cv w) (syn_cop (.cv y) (.cv z))) (.objMem w x)) p0001 p0019
  have p0021 :=
    @g_exbii
      (.classMem (syn_cop (syn_csn (.cv w))
          (syn_cop (syn_csn (.cv z)) (syn_cop (syn_csn (.cv y)) (.cv x))))
        (syn_cin (syn_cins4 (syn_csi3 (syn_cswap))) (syn_cins2 (syn_cins2 (syn_csset)))))
      (syn_wa (.classEq (.cv w) (syn_cop (.cv y) (.cv z))) (.objMem w x)) w p0020
  have p0022 :=
    @g_elima1c w (syn_cop (syn_csn (.cv z)) (syn_cop (syn_csn (.cv y)) (.cv x)))
      (syn_cin (syn_cins4 (syn_csi3 (syn_cswap))) (syn_cins2 (syn_cins2 (syn_csset))))
      dv_cache_0001 dv_cache_0002
  have p0023 :=
    (NFChoice.DirectNominalPrf.Nominal.DefinitionLeafHandlersCanonical001.dfClelOfDV w
      (syn_cop (.cv y) (.cv z)) (.cv x) dv_cache_0003 dv_cache_0004)
  have p0024_e02_recanon :
    Nominal.NPrf
      (syn_wb (.classMem (syn_cop (.cv y) (.cv z)) (.cv x)) (syn_wex w
          (syn_wa (.classEq (.cv w) (syn_cop (.cv y) (.cv z))) (.objMem w x)))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wb syn_cop syn_cun syn_cnin syn_wnan syn_wa syn_ccompl syn_wrex syn_wex
          syn_cphi
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
    @g_n_3bitr4i
      (syn_wex w (.classMem (syn_cop (syn_csn (.cv w))
            (syn_cop (syn_csn (.cv z)) (syn_cop (syn_csn (.cv y)) (.cv x))))
          (syn_cin (syn_cins4 (syn_csi3 (syn_cswap))) (syn_cins2 (syn_cins2 (syn_csset))))))
      (syn_wex w (syn_wa (.classEq (.cv w) (syn_cop (.cv y) (.cv z))) (.objMem w x)))
      (.classMem (syn_cop (syn_csn (.cv z)) (syn_cop (syn_csn (.cv y)) (.cv x))) (syn_cima
          (syn_cin (syn_cins4 (syn_csi3 (syn_cswap))) (syn_cins2 (syn_cins2 (syn_csset))))
          (syn_c1c)))
      (.classMem (syn_cop (.cv y) (.cv z)) (.cv x)) p0021 p0022 p0024_e02_recanon
  have p0025 :=
    @g_exbii
      (.classMem (syn_cop (syn_csn (.cv z)) (syn_cop (syn_csn (.cv y)) (.cv x))) (syn_cima
          (syn_cin (syn_cins4 (syn_csi3 (syn_cswap))) (syn_cins2 (syn_cins2 (syn_csset))))
          (syn_c1c)))
      (.classMem (syn_cop (.cv y) (.cv z)) (.cv x)) z p0024
  have p0026 :=
    @g_elima1c z (syn_cop (syn_csn (.cv y)) (.cv x))
      (syn_cima (syn_cin (syn_cins4 (syn_csi3 (syn_cswap))) (syn_cins2 (syn_cins2 (syn_csset))))
        (syn_c1c))
      dv_cache_0005 dv_cache_0006
  have p0027 := @g_eldm2 z (.cv y) (.cv x) dv_cache_0007 dv_cache_0008
  have p0028 :=
    @g_n_3bitr4i
      (syn_wex z (.classMem (syn_cop (syn_csn (.cv z)) (syn_cop (syn_csn (.cv y)) (.cv x)))
          (syn_cima (syn_cin (syn_cins4 (syn_csi3 (syn_cswap)))
              (syn_cins2 (syn_cins2 (syn_csset)))) (syn_c1c))))
      (syn_wex z (.classMem (syn_cop (.cv y) (.cv z)) (.cv x)))
      (.classMem (syn_cop (syn_csn (.cv y)) (.cv x)) (syn_cima (syn_cima
            (syn_cin (syn_cins4 (syn_csi3 (syn_cswap))) (syn_cins2 (syn_cins2 (syn_csset))))
            (syn_c1c)) (syn_c1c)))
      (.classMem (.cv y) (syn_cdm (.cv x))) p0025 p0026 p0027
  have p0029 :=
    @g_releqmpt x y (syn_cvv)
      (syn_cima (syn_cima
          (syn_cin (syn_cins4 (syn_csi3 (syn_cswap))) (syn_cins2 (syn_cins2 (syn_csset))))
          (syn_c1c)) (syn_c1c))
      (syn_cdm (.cv x)) dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012
      dv_cache_0013 p0028
  have p0030 :=
    @g_eqtr4i (syn_cdomfn) (syn_cmpt x (syn_cvv) (syn_cdm (.cv x)))
      (syn_cin (syn_cxp (syn_cvv) (syn_cvv)) (syn_ccnv (syn_ccompl (syn_cima
              (syn_csymdif (syn_cins3 (syn_csset)) (syn_cins2 (syn_cima (syn_cima
                      (syn_cin (syn_cins4 (syn_csi3 (syn_cswap)))
                        (syn_cins2 (syn_cins2 (syn_csset)))) (syn_c1c)) (syn_c1c))))
              (syn_c1c)))))
      p0000 p0029
  have p0031 := @g_vvex
  have p0032 := @g_swapex
  have p0033 := @g_si3ex (syn_cswap) p0032
  have p0034 := @g_ins4ex (syn_csi3 (syn_cswap)) p0033
  have p0035 := @g_ssetex
  have p0036 := @g_ins2ex (syn_csset) p0035
  have p0037 := @g_ins2ex (syn_cins2 (syn_csset)) p0036
  have p0038 :=
    @g_inex (syn_cins4 (syn_csi3 (syn_cswap))) (syn_cins2 (syn_cins2 (syn_csset))) p0034
      p0037
  have p0039 := @g_n_1cex
  have p0040 :=
    @g_imaex
      (syn_cin (syn_cins4 (syn_csi3 (syn_cswap))) (syn_cins2 (syn_cins2 (syn_csset))))
      (syn_c1c) p0038 p0039
  have p0042 :=
    @g_imaex
      (syn_cima (syn_cin (syn_cins4 (syn_csi3 (syn_cswap))) (syn_cins2 (syn_cins2 (syn_csset))))
        (syn_c1c))
      (syn_c1c) p0040 p0039
  have p0043 :=
    @g_mptexlem (syn_cvv)
      (syn_cima (syn_cima
          (syn_cin (syn_cins4 (syn_csi3 (syn_cswap))) (syn_cins2 (syn_cins2 (syn_csset))))
          (syn_c1c)) (syn_c1c))
      p0031 p0042
  have p0044 :=
    @g_eqeltri (syn_cdomfn)
      (syn_cin (syn_cxp (syn_cvv) (syn_cvv)) (syn_ccnv (syn_ccompl (syn_cima
              (syn_csymdif (syn_cins3 (syn_csset)) (syn_cins2 (syn_cima (syn_cima
                      (syn_cin (syn_cins4 (syn_csi3 (syn_cswap)))
                        (syn_cins2 (syn_cins2 (syn_csset)))) (syn_c1c)) (syn_c1c))))
              (syn_c1c)))))
      (syn_cvv) p0030 p0043
  exact p0044

@[expose]
noncomputable def g_ranfnex : Nominal.NPrf (.classMem (syn_cranfn) (syn_cvv)) :=
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
    w ∉ ((syn_cop (syn_csn (.cv z)) (syn_cop (syn_csn (.cv y)) (.cv x)))).fv := by
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
      ((syn_cin (syn_cins4 (syn_csi3 (syn_cid))) (syn_cins2 (syn_cins2 (syn_csset))))).fv :=
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
  have dv_cache_0003 : w ∉ ((syn_cop (.cv z) (.cv y))).fv :=
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
  have dv_cache_0005 : z ∉ ((syn_cop (syn_csn (.cv y)) (.cv x))).fv :=
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
      ((syn_cima (syn_cin (syn_cins4 (syn_csi3 (syn_cid))) (syn_cins2 (syn_cins2 (syn_csset))))
          (syn_c1c))).fv :=
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
  have dv_cache_0009 : x ∉ ((syn_cvv)).fv :=
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
      ((syn_cima (syn_cima
            (syn_cin (syn_cins4 (syn_csi3 (syn_cid))) (syn_cins2 (syn_cins2 (syn_csset))))
            (syn_c1c)) (syn_c1c))).fv :=
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
      ((syn_cima (syn_cima
            (syn_cin (syn_cins4 (syn_csi3 (syn_cid))) (syn_cins2 (syn_cins2 (syn_csset))))
            (syn_c1c)) (syn_c1c))).fv :=
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
  have dv_cache_0012 : y ∉ ((syn_crn (.cv x))).fv :=
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
  have p0000 := NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominal_df_ranfn x
  have p0001 :=
    @g_elin
      (syn_cop (syn_csn (.cv w))
        (syn_cop (syn_csn (.cv z)) (syn_cop (syn_csn (.cv y)) (.cv x))))
      (syn_cins4 (syn_csi3 (syn_cid))) (syn_cins2 (syn_cins2 (syn_csset)))
  have p0002 := @g_vex x
  have p0003 :=
    @g_oqelins4 (syn_csn (.cv w)) (syn_csn (.cv z)) (syn_csn (.cv y)) (.cv x)
      (syn_csi3 (syn_cid)) p0002
  have p0004 := @g_vex w
  have p0005 := @g_vex z
  have p0006 := @g_vex y
  have p0007 := @g_otsnelsi3 (.cv w) (.cv z) (.cv y) (syn_cid) p0004 p0005 p0006
  have p0008 := (Nominal.biimpRefl (syn_wbr (.cv w) (syn_cid) (syn_cop (.cv z) (.cv y))))
  have p0009 := @g_opex (.cv z) (.cv y) p0005 p0006
  have p0010 := @g_ideq (.cv w) (syn_cop (.cv z) (.cv y)) p0009
  have p0011 :=
    @g_n_3bitr2i
      (.classMem (syn_cop (syn_csn (.cv w)) (syn_cop (syn_csn (.cv z)) (syn_csn (.cv y))))
        (syn_csi3 (syn_cid)))
      (.classMem (syn_cop (.cv w) (syn_cop (.cv z) (.cv y))) (syn_cid))
      (syn_wbr (.cv w) (syn_cid) (syn_cop (.cv z) (.cv y)))
      (.classEq (.cv w) (syn_cop (.cv z) (.cv y))) p0007 p0008 p0010
  have p0012 :=
    @g_bitri
      (.classMem (syn_cop (syn_csn (.cv w))
          (syn_cop (syn_csn (.cv z)) (syn_cop (syn_csn (.cv y)) (.cv x))))
        (syn_cins4 (syn_csi3 (syn_cid))))
      (.classMem (syn_cop (syn_csn (.cv w)) (syn_cop (syn_csn (.cv z)) (syn_csn (.cv y))))
        (syn_csi3 (syn_cid)))
      (.classEq (.cv w) (syn_cop (.cv z) (.cv y))) p0003 p0011
  have p0013 := @g_snex (.cv z)
  have p0014 :=
    @g_otelins2 (syn_csn (.cv w)) (syn_csn (.cv z)) (syn_cop (syn_csn (.cv y)) (.cv x))
      (syn_cins2 (syn_csset)) p0013
  have p0015 := @g_snex (.cv y)
  have p0016 := @g_otelins2 (syn_csn (.cv w)) (syn_csn (.cv y)) (.cv x) (syn_csset) p0015
  have p0017 := @g_opelssetsn (.cv w) (.cv x) p0004 p0002
  have p0018_e01_recanon :
    Nominal.NPrf
      (syn_wb (.classMem (syn_cop (syn_csn (.cv w)) (.cv x)) (syn_csset)) (.objMem w x)) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wb syn_cop syn_cun syn_cnin syn_wnan syn_wa syn_ccompl syn_wrex syn_wex
          syn_cphi syn_csn syn_csset syn_copab syn_wss syn_cin
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
    @g_bitri
      (.classMem (syn_cop (syn_csn (.cv w)) (syn_cop (syn_csn (.cv y)) (.cv x)))
        (syn_cins2 (syn_csset)))
      (.classMem (syn_cop (syn_csn (.cv w)) (.cv x)) (syn_csset)) (.objMem w x) p0016
      p0018_e01_recanon
  have p0019 :=
    @g_bitri
      (.classMem (syn_cop (syn_csn (.cv w))
          (syn_cop (syn_csn (.cv z)) (syn_cop (syn_csn (.cv y)) (.cv x))))
        (syn_cins2 (syn_cins2 (syn_csset))))
      (.classMem (syn_cop (syn_csn (.cv w)) (syn_cop (syn_csn (.cv y)) (.cv x)))
        (syn_cins2 (syn_csset)))
      (.objMem w x) p0014 p0018
  have p0020 :=
    @g_anbi12i
      (.classMem (syn_cop (syn_csn (.cv w))
          (syn_cop (syn_csn (.cv z)) (syn_cop (syn_csn (.cv y)) (.cv x))))
        (syn_cins4 (syn_csi3 (syn_cid))))
      (.classEq (.cv w) (syn_cop (.cv z) (.cv y)))
      (.classMem (syn_cop (syn_csn (.cv w))
          (syn_cop (syn_csn (.cv z)) (syn_cop (syn_csn (.cv y)) (.cv x))))
        (syn_cins2 (syn_cins2 (syn_csset))))
      (.objMem w x) p0012 p0019
  have p0021 :=
    @g_bitri
      (.classMem (syn_cop (syn_csn (.cv w))
          (syn_cop (syn_csn (.cv z)) (syn_cop (syn_csn (.cv y)) (.cv x))))
        (syn_cin (syn_cins4 (syn_csi3 (syn_cid))) (syn_cins2 (syn_cins2 (syn_csset)))))
      (syn_wa (.classMem (syn_cop (syn_csn (.cv w))
            (syn_cop (syn_csn (.cv z)) (syn_cop (syn_csn (.cv y)) (.cv x))))
          (syn_cins4 (syn_csi3 (syn_cid)))) (.classMem (syn_cop (syn_csn (.cv w))
            (syn_cop (syn_csn (.cv z)) (syn_cop (syn_csn (.cv y)) (.cv x))))
          (syn_cins2 (syn_cins2 (syn_csset)))))
      (syn_wa (.classEq (.cv w) (syn_cop (.cv z) (.cv y))) (.objMem w x)) p0001 p0020
  have p0022 :=
    @g_exbii
      (.classMem (syn_cop (syn_csn (.cv w))
          (syn_cop (syn_csn (.cv z)) (syn_cop (syn_csn (.cv y)) (.cv x))))
        (syn_cin (syn_cins4 (syn_csi3 (syn_cid))) (syn_cins2 (syn_cins2 (syn_csset)))))
      (syn_wa (.classEq (.cv w) (syn_cop (.cv z) (.cv y))) (.objMem w x)) w p0021
  have p0023 :=
    @g_elima1c w (syn_cop (syn_csn (.cv z)) (syn_cop (syn_csn (.cv y)) (.cv x)))
      (syn_cin (syn_cins4 (syn_csi3 (syn_cid))) (syn_cins2 (syn_cins2 (syn_csset))))
      dv_cache_0001 dv_cache_0002
  have p0024 :=
    (NFChoice.DirectNominalPrf.Nominal.DefinitionLeafHandlersCanonical001.dfClelOfDV w
      (syn_cop (.cv z) (.cv y)) (.cv x) dv_cache_0003 dv_cache_0004)
  have p0025_e02_recanon :
    Nominal.NPrf
      (syn_wb (.classMem (syn_cop (.cv z) (.cv y)) (.cv x)) (syn_wex w
          (syn_wa (.classEq (.cv w) (syn_cop (.cv z) (.cv y))) (.objMem w x)))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wb syn_cop syn_cun syn_cnin syn_wnan syn_wa syn_ccompl syn_wrex syn_wex
          syn_cphi
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
    @g_n_3bitr4i
      (syn_wex w (.classMem (syn_cop (syn_csn (.cv w))
            (syn_cop (syn_csn (.cv z)) (syn_cop (syn_csn (.cv y)) (.cv x))))
          (syn_cin (syn_cins4 (syn_csi3 (syn_cid))) (syn_cins2 (syn_cins2 (syn_csset))))))
      (syn_wex w (syn_wa (.classEq (.cv w) (syn_cop (.cv z) (.cv y))) (.objMem w x)))
      (.classMem (syn_cop (syn_csn (.cv z)) (syn_cop (syn_csn (.cv y)) (.cv x))) (syn_cima
          (syn_cin (syn_cins4 (syn_csi3 (syn_cid))) (syn_cins2 (syn_cins2 (syn_csset))))
          (syn_c1c)))
      (.classMem (syn_cop (.cv z) (.cv y)) (.cv x)) p0022 p0023 p0025_e02_recanon
  have p0026 :=
    @g_exbii
      (.classMem (syn_cop (syn_csn (.cv z)) (syn_cop (syn_csn (.cv y)) (.cv x))) (syn_cima
          (syn_cin (syn_cins4 (syn_csi3 (syn_cid))) (syn_cins2 (syn_cins2 (syn_csset))))
          (syn_c1c)))
      (.classMem (syn_cop (.cv z) (.cv y)) (.cv x)) z p0025
  have p0027 :=
    @g_elima1c z (syn_cop (syn_csn (.cv y)) (.cv x))
      (syn_cima (syn_cin (syn_cins4 (syn_csi3 (syn_cid))) (syn_cins2 (syn_cins2 (syn_csset))))
        (syn_c1c))
      dv_cache_0005 dv_cache_0006
  have p0028 := @g_elrn2 z (.cv y) (.cv x) dv_cache_0007 dv_cache_0008
  have p0029 :=
    @g_n_3bitr4i
      (syn_wex z (.classMem (syn_cop (syn_csn (.cv z)) (syn_cop (syn_csn (.cv y)) (.cv x)))
          (syn_cima
            (syn_cin (syn_cins4 (syn_csi3 (syn_cid))) (syn_cins2 (syn_cins2 (syn_csset))))
            (syn_c1c))))
      (syn_wex z (.classMem (syn_cop (.cv z) (.cv y)) (.cv x)))
      (.classMem (syn_cop (syn_csn (.cv y)) (.cv x)) (syn_cima (syn_cima
            (syn_cin (syn_cins4 (syn_csi3 (syn_cid))) (syn_cins2 (syn_cins2 (syn_csset))))
            (syn_c1c)) (syn_c1c)))
      (.classMem (.cv y) (syn_crn (.cv x))) p0026 p0027 p0028
  have p0030 :=
    @g_releqmpt x y (syn_cvv)
      (syn_cima (syn_cima
          (syn_cin (syn_cins4 (syn_csi3 (syn_cid))) (syn_cins2 (syn_cins2 (syn_csset))))
          (syn_c1c)) (syn_c1c))
      (syn_crn (.cv x)) dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012
      dv_cache_0013 p0029
  have p0031 :=
    @g_eqtr4i (syn_cranfn) (syn_cmpt x (syn_cvv) (syn_crn (.cv x)))
      (syn_cin (syn_cxp (syn_cvv) (syn_cvv)) (syn_ccnv (syn_ccompl (syn_cima
              (syn_csymdif (syn_cins3 (syn_csset)) (syn_cins2 (syn_cima (syn_cima
                      (syn_cin (syn_cins4 (syn_csi3 (syn_cid)))
                        (syn_cins2 (syn_cins2 (syn_csset)))) (syn_c1c)) (syn_c1c))))
              (syn_c1c)))))
      p0000 p0030
  have p0032 := @g_vvex
  have p0033 := @g_idex
  have p0034 := @g_si3ex (syn_cid) p0033
  have p0035 := @g_ins4ex (syn_csi3 (syn_cid)) p0034
  have p0036 := @g_ssetex
  have p0037 := @g_ins2ex (syn_csset) p0036
  have p0038 := @g_ins2ex (syn_cins2 (syn_csset)) p0037
  have p0039 :=
    @g_inex (syn_cins4 (syn_csi3 (syn_cid))) (syn_cins2 (syn_cins2 (syn_csset))) p0035
      p0038
  have p0040 := @g_n_1cex
  have p0041 :=
    @g_imaex
      (syn_cin (syn_cins4 (syn_csi3 (syn_cid))) (syn_cins2 (syn_cins2 (syn_csset))))
      (syn_c1c) p0039 p0040
  have p0043 :=
    @g_imaex
      (syn_cima (syn_cin (syn_cins4 (syn_csi3 (syn_cid))) (syn_cins2 (syn_cins2 (syn_csset))))
        (syn_c1c))
      (syn_c1c) p0041 p0040
  have p0044 :=
    @g_mptexlem (syn_cvv)
      (syn_cima (syn_cima
          (syn_cin (syn_cins4 (syn_csi3 (syn_cid))) (syn_cins2 (syn_cins2 (syn_csset))))
          (syn_c1c)) (syn_c1c))
      p0032 p0043
  have p0045 :=
    @g_eqeltri (syn_cranfn)
      (syn_cin (syn_cxp (syn_cvv) (syn_cvv)) (syn_ccnv (syn_ccompl (syn_cima
              (syn_csymdif (syn_cins3 (syn_csset)) (syn_cins2 (syn_cima (syn_cima
                      (syn_cin (syn_cins4 (syn_csi3 (syn_cid)))
                        (syn_cins2 (syn_cins2 (syn_csset)))) (syn_c1c)) (syn_c1c))))
              (syn_c1c)))))
      (syn_cvv) p0031 p0044
  exact p0045

@[expose]
noncomputable def g_clos1eq1 (R : Class) (S : Class) (T : Class) :
    Nominal.NPrf (.imp (.classEq S T) (.classEq (syn_cclos1 S R) (syn_cclos1 T R))) :=
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
  have p0000 := @g_sseq1 S T (.cv a)
  have p0001 :=
    @g_anbi1d (.classEq S T) (syn_wss S (.cv a)) (syn_wss T (.cv a))
      (syn_wss (syn_cima R (.cv a)) (.cv a)) p0000
  have p0002 :=
    @g_abbidv (.classEq S T)
      (syn_wa (syn_wss S (.cv a)) (syn_wss (syn_cima R (.cv a)) (.cv a)))
      (syn_wa (syn_wss T (.cv a)) (syn_wss (syn_cima R (.cv a)) (.cv a))) a dv_cache_0001
      p0001
  have p0003 :=
    @g_inteq (.cab a (syn_wa (syn_wss S (.cv a)) (syn_wss (syn_cima R (.cv a)) (.cv a))))
      (.cab a (syn_wa (syn_wss T (.cv a)) (syn_wss (syn_cima R (.cv a)) (.cv a))))
  have p0004 :=
    @g_syl (.classEq S T)
      (.classEq (.cab a (syn_wa (syn_wss S (.cv a)) (syn_wss (syn_cima R (.cv a)) (.cv a))))
        (.cab a (syn_wa (syn_wss T (.cv a)) (syn_wss (syn_cima R (.cv a)) (.cv a)))))
      (.classEq (syn_cint
          (.cab a (syn_wa (syn_wss S (.cv a)) (syn_wss (syn_cima R (.cv a)) (.cv a)))))
        (syn_cint (.cab a (syn_wa (syn_wss T (.cv a)) (syn_wss (syn_cima R (.cv a)) (.cv a))))))
      p0002 p0003
  have p0005 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominal_df_clos1 R S a
      dv_cache_0002 dv_cache_0003
  have p0006 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominal_df_clos1 R T a
      dv_cache_0002 dv_cache_0004
  have p0007 :=
    @g_n_3eqtr4g (.classEq S T)
      (syn_cint (.cab a (syn_wa (syn_wss S (.cv a)) (syn_wss (syn_cima R (.cv a)) (.cv a)))))
      (syn_cint (.cab a (syn_wa (syn_wss T (.cv a)) (syn_wss (syn_cima R (.cv a)) (.cv a)))))
      (syn_cclos1 S R) (syn_cclos1 T R) p0004 p0005 p0006
  exact p0007

@[expose]
noncomputable def g_clos1eq2 (R : Class) (S : Class) (T : Class) :
    Nominal.NPrf (.imp (.classEq R T) (.classEq (syn_cclos1 S R) (syn_cclos1 S T))) :=
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
  have p0000 := @g_imaeq1 R T (.cv a)
  have p0001 :=
    @g_sseq1d (.classEq R T) (syn_cima R (.cv a)) (syn_cima T (.cv a)) (.cv a) p0000
  have p0002 :=
    @g_anbi2d (.classEq R T) (syn_wss (syn_cima R (.cv a)) (.cv a))
      (syn_wss (syn_cima T (.cv a)) (.cv a)) (syn_wss S (.cv a)) p0001
  have p0003 :=
    @g_abbidv (.classEq R T)
      (syn_wa (syn_wss S (.cv a)) (syn_wss (syn_cima R (.cv a)) (.cv a)))
      (syn_wa (syn_wss S (.cv a)) (syn_wss (syn_cima T (.cv a)) (.cv a))) a dv_cache_0001
      p0002
  have p0004 :=
    @g_inteq (.cab a (syn_wa (syn_wss S (.cv a)) (syn_wss (syn_cima R (.cv a)) (.cv a))))
      (.cab a (syn_wa (syn_wss S (.cv a)) (syn_wss (syn_cima T (.cv a)) (.cv a))))
  have p0005 :=
    @g_syl (.classEq R T)
      (.classEq (.cab a (syn_wa (syn_wss S (.cv a)) (syn_wss (syn_cima R (.cv a)) (.cv a))))
        (.cab a (syn_wa (syn_wss S (.cv a)) (syn_wss (syn_cima T (.cv a)) (.cv a)))))
      (.classEq (syn_cint
          (.cab a (syn_wa (syn_wss S (.cv a)) (syn_wss (syn_cima R (.cv a)) (.cv a)))))
        (syn_cint (.cab a (syn_wa (syn_wss S (.cv a)) (syn_wss (syn_cima T (.cv a)) (.cv a))))))
      p0003 p0004
  have p0006 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominal_df_clos1 R S a
      dv_cache_0002 dv_cache_0003
  have p0007 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominal_df_clos1 T S a
      dv_cache_0004 dv_cache_0003
  have p0008 :=
    @g_n_3eqtr4g (.classEq R T)
      (syn_cint (.cab a (syn_wa (syn_wss S (.cv a)) (syn_wss (syn_cima R (.cv a)) (.cv a)))))
      (syn_cint (.cab a (syn_wa (syn_wss S (.cv a)) (syn_wss (syn_cima T (.cv a)) (.cv a)))))
      (syn_cclos1 S R) (syn_cclos1 S T) p0005 p0006 p0007
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

@[expose]
noncomputable def g_clos1ex (R : Class) (S : Class)
    (hyp_clos1ex_1 : Nominal.NPrf (.classMem S (syn_cvv)))
    (hyp_clos1ex_2 : Nominal.NPrf (.classMem R (syn_cvv))) :
    Nominal.NPrf (.classMem (syn_cclos1 S R) (syn_cvv)) :=
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
  have dv_cache_0004 : b ∉ ((syn_csset)).fv :=
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
  have dv_cache_0005 : b ∉ ((syn_cimage R)).fv :=
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
  have dv_cache_0006 : b ∉ ((syn_cima R (.cv a))).fv :=
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
  have dv_cache_0007 : b ∉ ((syn_wss (syn_cima R (.cv a)) (.cv a))).fv :=
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
      ((syn_cin (syn_cima (syn_csset) (syn_csn S))
          (syn_cfix (syn_ccom (syn_csset) (syn_cimage R))))).fv :=
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
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominal_df_clos1 R S a
      dv_cache_0001 dv_cache_0002
  have p0001 :=
    @g_elin (.cv a) (syn_cima (syn_csset) (syn_csn S))
      (syn_cfix (syn_ccom (syn_csset) (syn_cimage R)))
  have p0002 := @g_elimasn (syn_csset) S (.cv a)
  have p0003 := (Nominal.biimpRefl (syn_wbr S (syn_csset) (.cv a)))
  have p0004 := @g_vex a
  have p0005 := @g_brsset S (.cv a) hyp_clos1ex_1 p0004
  have p0006 :=
    @g_n_3bitr2i (.classMem (.cv a) (syn_cima (syn_csset) (syn_csn S)))
      (.classMem (syn_cop S (.cv a)) (syn_csset)) (syn_wbr S (syn_csset) (.cv a))
      (syn_wss S (.cv a)) p0002 p0003 p0005
  have p0007 := @g_elfix (.cv a) (syn_ccom (syn_csset) (syn_cimage R))
  have p0008 :=
    @g_brco b (.cv a) (.cv a) (syn_csset) (syn_cimage R) dv_cache_0003 dv_cache_0003
      dv_cache_0004 dv_cache_0005
  have p0009 := @g_vex b
  have p0010 := @g_brimage (.cv a) (.cv b) R p0004 p0009
  have p0011 :=
    @g_anbi1i (syn_wbr (.cv a) (syn_cimage R) (.cv b))
      (.classEq (.cv b) (syn_cima R (.cv a))) (syn_wbr (.cv b) (syn_csset) (.cv a)) p0010
  have p0012 :=
    @g_exbii
      (syn_wa (syn_wbr (.cv a) (syn_cimage R) (.cv b)) (syn_wbr (.cv b) (syn_csset) (.cv a)))
      (syn_wa (.classEq (.cv b) (syn_cima R (.cv a))) (syn_wbr (.cv b) (syn_csset) (.cv a)))
      b p0011
  have p0013 := @g_imaex R (.cv a) hyp_clos1ex_2 p0004
  have p0014 := @g_breq1 (.cv b) (syn_cima R (.cv a)) (.cv a) (syn_csset)
  have p0015 := @g_brsset (syn_cima R (.cv a)) (.cv a) p0013 p0004
  have p0016 :=
    @g_syl6bb (.classEq (.cv b) (syn_cima R (.cv a)))
      (syn_wbr (.cv b) (syn_csset) (.cv a))
      (syn_wbr (syn_cima R (.cv a)) (syn_csset) (.cv a))
      (syn_wss (syn_cima R (.cv a)) (.cv a)) p0014 p0015
  have p0017 :=
    @g_ceqsexv (syn_wbr (.cv b) (syn_csset) (.cv a))
      (syn_wss (syn_cima R (.cv a)) (.cv a)) b (syn_cima R (.cv a)) dv_cache_0006
      dv_cache_0007 p0013 p0016
  have p0018 :=
    @g_bitri
      (syn_wex b (syn_wa (syn_wbr (.cv a) (syn_cimage R) (.cv b))
          (syn_wbr (.cv b) (syn_csset) (.cv a))))
      (syn_wex b (syn_wa (.classEq (.cv b) (syn_cima R (.cv a)))
          (syn_wbr (.cv b) (syn_csset) (.cv a))))
      (syn_wss (syn_cima R (.cv a)) (.cv a)) p0012 p0017
  have p0019 :=
    @g_bitri (syn_wbr (.cv a) (syn_ccom (syn_csset) (syn_cimage R)) (.cv a))
      (syn_wex b (syn_wa (syn_wbr (.cv a) (syn_cimage R) (.cv b))
          (syn_wbr (.cv b) (syn_csset) (.cv a))))
      (syn_wss (syn_cima R (.cv a)) (.cv a)) p0008 p0018
  have p0020 :=
    @g_bitri (.classMem (.cv a) (syn_cfix (syn_ccom (syn_csset) (syn_cimage R))))
      (syn_wbr (.cv a) (syn_ccom (syn_csset) (syn_cimage R)) (.cv a))
      (syn_wss (syn_cima R (.cv a)) (.cv a)) p0007 p0019
  have p0021 :=
    @g_anbi12i (.classMem (.cv a) (syn_cima (syn_csset) (syn_csn S))) (syn_wss S (.cv a))
      (.classMem (.cv a) (syn_cfix (syn_ccom (syn_csset) (syn_cimage R))))
      (syn_wss (syn_cima R (.cv a)) (.cv a)) p0006 p0020
  have p0022 :=
    @g_bitri
      (.classMem (.cv a) (syn_cin (syn_cima (syn_csset) (syn_csn S))
          (syn_cfix (syn_ccom (syn_csset) (syn_cimage R)))))
      (syn_wa (.classMem (.cv a) (syn_cima (syn_csset) (syn_csn S)))
        (.classMem (.cv a) (syn_cfix (syn_ccom (syn_csset) (syn_cimage R)))))
      (syn_wa (syn_wss S (.cv a)) (syn_wss (syn_cima R (.cv a)) (.cv a))) p0001 p0021
  have p0023 :=
    @g_eqabi (syn_wa (syn_wss S (.cv a)) (syn_wss (syn_cima R (.cv a)) (.cv a))) a
      (syn_cin (syn_cima (syn_csset) (syn_csn S))
        (syn_cfix (syn_ccom (syn_csset) (syn_cimage R))))
      dv_cache_0008 p0022
  have p0024 := @g_ssetex
  have p0025 := @g_snex S
  have p0026 := @g_imaex (syn_csset) (syn_csn S) p0024 p0025
  have p0028 := @g_imageex R hyp_clos1ex_2
  have p0029 := @g_coex (syn_csset) (syn_cimage R) p0024 p0028
  have p0030 := @g_fixex (syn_ccom (syn_csset) (syn_cimage R)) p0029
  have p0031 :=
    @g_inex (syn_cima (syn_csset) (syn_csn S))
      (syn_cfix (syn_ccom (syn_csset) (syn_cimage R))) p0026 p0030
  have p0032 :=
    @g_eqeltrri
      (syn_cin (syn_cima (syn_csset) (syn_csn S))
        (syn_cfix (syn_ccom (syn_csset) (syn_cimage R))))
      (.cab a (syn_wa (syn_wss S (.cv a)) (syn_wss (syn_cima R (.cv a)) (.cv a))))
      (syn_cvv) p0023 p0031
  have p0033 :=
    @g_intex (.cab a (syn_wa (syn_wss S (.cv a)) (syn_wss (syn_cima R (.cv a)) (.cv a))))
      p0032
  have p0034 :=
    @g_eqeltri (syn_cclos1 S R)
      (syn_cint (.cab a (syn_wa (syn_wss S (.cv a)) (syn_wss (syn_cima R (.cv a)) (.cv a)))))
      (syn_cvv) p0000 p0033
  exact p0034

@[expose]
noncomputable def g_clos1exg (R : Class) (S : Class) (V : Class) (W : Class) :
    Nominal.NPrf
      (.imp (syn_wa (.classMem S V) (.classMem R W)) (.classMem (syn_cclos1 S R) (syn_cvv))) :=
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
  have dv_cache_0004 : r ∉ ((Wff.classMem (syn_cclos1 S R) (syn_cvv))).fv :=
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
  have dv_cache_0005 : s ∉ ((Wff.classMem (syn_cclos1 S (.cv r)) (syn_cvv))).fv :=
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
  have p0000 := @g_clos1eq1 (.cv r) (.cv s) S
  have p0001 :=
    @g_eleq1d (.classEq (.cv s) S) (syn_cclos1 (.cv s) (.cv r)) (syn_cclos1 S (.cv r))
      (syn_cvv) p0000
  have p0002 := @g_clos1eq2 (.cv r) S R
  have p0003 :=
    @g_eleq1d (.classEq (.cv r) R) (syn_cclos1 S (.cv r)) (syn_cclos1 S R) (syn_cvv) p0002
  have p0004 := @g_vex s
  have p0005 := @g_vex r
  have p0006 := @g_clos1ex (.cv r) (.cv s) p0004 p0005
  have p0007 :=
    @g_vtocl2g (.classMem (syn_cclos1 (.cv s) (.cv r)) (syn_cvv))
      (.classMem (syn_cclos1 S (.cv r)) (syn_cvv)) (.classMem (syn_cclos1 S R) (syn_cvv))
      s r S R V W dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      p0001 p0003 p0006
  exact p0007

@[expose]
noncomputable def g_clos1base (C : Class) (R : Class) (S : Class)
    (hyp_clos1base_1 : Nominal.NPrf (.classEq C (syn_cclos1 S R))) :
    Nominal.NPrf (syn_wss S C) :=
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
  have p0000 := @g_ssmin (syn_wss (syn_cima R (.cv a)) (.cv a)) a S dv_cache_0001
  have p0001 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominal_df_clos1 R S a
      dv_cache_0002 dv_cache_0001
  have p0002 :=
    @g_eqtr2i C (syn_cclos1 S R)
      (syn_cint (.cab a (syn_wa (syn_wss S (.cv a)) (syn_wss (syn_cima R (.cv a)) (.cv a)))))
      hyp_clos1base_1 p0001
  have p0003 :=
    @g_sseqtri S
      (syn_cint (.cab a (syn_wa (syn_wss S (.cv a)) (syn_wss (syn_cima R (.cv a)) (.cv a)))))
      C p0000 p0002
  exact p0003

@[expose]
noncomputable def g_clos1conn (A : Class) (B : Class) (C : Class) (R : Class) (S : Class)
    (hyp_clos1base_1 : Nominal.NPrf (.classEq C (syn_cclos1 S R))) :
    Nominal.NPrf (.imp (syn_wa (.classMem A C) (syn_wbr A R B)) (.classMem B C)) :=
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
  have dv_cache_0003 : z ∉ ((syn_wbr (.cv x) R (.cv y))).fv :=
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
  have dv_cache_0006 : a ∉ ((syn_wbr (.cv x) R (.cv y))).fv :=
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
    y ∉ ((Wff.imp (syn_wa (.classMem A C) (syn_wbr A R B)) (.classMem B C))).fv :=
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
      ((Wff.imp (syn_wa (.classMem A C) (syn_wbr A R (.cv y))) (.classMem (.cv y) C))).fv :=
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
  have p0000 := @g_brex A B R
  have p0001 :=
    @g_adantl (syn_wbr A R B) (syn_wa (.classMem A (syn_cvv)) (.classMem B (syn_cvv)))
      (.classMem A C) p0000
  have p0002 := @g_eleq1 (.cv x) A C
  have p0003 := @g_breq1 (.cv x) A (.cv y) R
  have p0004 :=
    @g_anbi12d (.classEq (.cv x) A) (.classMem (.cv x) C) (.classMem A C)
      (syn_wbr (.cv x) R (.cv y)) (syn_wbr A R (.cv y)) p0002 p0003
  have p0005 :=
    @g_imbi1d (.classEq (.cv x) A)
      (syn_wa (.classMem (.cv x) C) (syn_wbr (.cv x) R (.cv y)))
      (syn_wa (.classMem A C) (syn_wbr A R (.cv y))) (.classMem (.cv y) C) p0004
  have p0006 := @g_breq2 (.cv y) B A R
  have p0007 :=
    @g_anbi2d (.classEq (.cv y) B) (syn_wbr A R (.cv y)) (syn_wbr A R B) (.classMem A C)
      p0006
  have p0008 := @g_eleq1 (.cv y) B C
  have p0009 :=
    @g_imbi12d (.classEq (.cv y) B) (syn_wa (.classMem A C) (syn_wbr A R (.cv y)))
      (syn_wa (.classMem A C) (syn_wbr A R B)) (.classMem (.cv y) C) (.classMem B C) p0007
      p0008
  have p0010 := @g_breq1 (.cv z) (.cv x) (.cv y) R
  have p0011 :=
    @g_rspcev (syn_wbr (.cv z) R (.cv y)) (syn_wbr (.cv x) R (.cv y)) z (.cv x) (.cv a)
      dv_cache_0001 dv_cache_0002 dv_cache_0003 p0010
  have p0012 := @g_elima z (.cv y) R (.cv a) dv_cache_0004 dv_cache_0005 dv_cache_0002
  have p0013_e00_recanon :
    Nominal.NPrf
      (.imp (syn_wa (.objMem x a) (syn_wbr (.cv x) R (.cv y)))
        (syn_wrex z (.cv a) (syn_wbr (.cv z) R (.cv y)))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wa syn_wbr syn_cop syn_cun syn_cnin syn_wnan syn_ccompl syn_wrex
          syn_wex syn_cphi
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
    @g_sylibr (syn_wa (.objMem x a) (syn_wbr (.cv x) R (.cv y)))
      (syn_wrex z (.cv a) (syn_wbr (.cv z) R (.cv y)))
      (.classMem (.cv y) (syn_cima R (.cv a))) p0013_e00_recanon p0012
  have p0014 :=
    @g_ancoms (.objMem x a) (syn_wbr (.cv x) R (.cv y))
      (.classMem (.cv y) (syn_cima R (.cv a))) p0013
  have p0015 := @g_ssel (syn_cima R (.cv a)) (.cv a) (.cv y)
  have p0016_e01_recanon :
    Nominal.NPrf
      (.imp (syn_wss (syn_cima R (.cv a)) (.cv a))
        (.imp (.classMem (.cv y) (syn_cima R (.cv a))) (.objMem y a))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wss syn_cin syn_ccompl syn_cnin syn_wnan syn_wa syn_cima syn_wrex
          syn_wex syn_wbr syn_cop syn_cun
        simp (config :=
          { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_class_cv]
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · exact Nominal.RecanonTransportDev.TRecanonWff.same _
        · apply Nominal.RecanonTransportDev.TRecanonWff.imp
          · exact Nominal.RecanonTransportDev.TRecanonWff.same _
          · exact Nominal.RecanonTransportDev.TRecanonWff.classMem_objMem _ _)
      p0015
  have p0016 :=
    @g_syl5 (syn_wa (syn_wbr (.cv x) R (.cv y)) (.objMem x a))
      (.classMem (.cv y) (syn_cima R (.cv a))) (syn_wss (syn_cima R (.cv a)) (.cv a))
      (.objMem y a) p0014 p0016_e01_recanon
  have p0017 :=
    @g_exp3a (syn_wss (syn_cima R (.cv a)) (.cv a)) (syn_wbr (.cv x) R (.cv y))
      (.objMem x a) (.objMem y a) p0016
  have p0018 :=
    @g_com12 (syn_wss (syn_cima R (.cv a)) (.cv a)) (syn_wbr (.cv x) R (.cv y))
      (.imp (.objMem x a) (.objMem y a)) p0017
  have p0019 :=
    @g_adantld (syn_wbr (.cv x) R (.cv y)) (syn_wss (syn_cima R (.cv a)) (.cv a))
      (.imp (.objMem x a) (.objMem y a)) (syn_wss S (.cv a)) p0018
  have p0020 :=
    @g_a2d (syn_wbr (.cv x) R (.cv y))
      (syn_wa (syn_wss S (.cv a)) (syn_wss (syn_cima R (.cv a)) (.cv a))) (.objMem x a)
      (.objMem y a) p0019
  have p0021 :=
    @g_alimdv (syn_wbr (.cv x) R (.cv y))
      (.imp (syn_wa (syn_wss S (.cv a)) (syn_wss (syn_cima R (.cv a)) (.cv a))) (.objMem x a))
      (.imp (syn_wa (syn_wss S (.cv a)) (syn_wss (syn_cima R (.cv a)) (.cv a))) (.objMem y a))
      a dv_cache_0006 p0020
  have p0022 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominal_df_clos1 R S a
      dv_cache_0007 dv_cache_0008
  have p0023 :=
    @g_eqtri C (syn_cclos1 S R)
      (syn_cint (.cab a (syn_wa (syn_wss S (.cv a)) (syn_wss (syn_cima R (.cv a)) (.cv a)))))
      hyp_clos1base_1 p0022
  have p0024 :=
    @g_eleq2i C
      (syn_cint (.cab a (syn_wa (syn_wss S (.cv a)) (syn_wss (syn_cima R (.cv a)) (.cv a)))))
      (.cv x) p0023
  have p0025 := @g_vex x
  have p0026 :=
    @g_elintab (syn_wa (syn_wss S (.cv a)) (syn_wss (syn_cima R (.cv a)) (.cv a))) a
      (.cv x) dv_cache_0009 p0025
  have p0027_e01_recanon :
    Nominal.NPrf
      (syn_wb (.classMem (.cv x) (syn_cint
            (.cab a (syn_wa (syn_wss S (.cv a)) (syn_wss (syn_cima R (.cv a)) (.cv a))))))
        (.all a (.imp (syn_wa (syn_wss S (.cv a)) (syn_wss (syn_cima R (.cv a)) (.cv a)))
            (.objMem x a)))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wb syn_cint syn_wa syn_wss syn_cin syn_ccompl syn_cnin syn_wnan
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
    @g_bitri (.classMem (.cv x) C)
      (.classMem (.cv x) (syn_cint
          (.cab a (syn_wa (syn_wss S (.cv a)) (syn_wss (syn_cima R (.cv a)) (.cv a))))))
      (.all a (.imp (syn_wa (syn_wss S (.cv a)) (syn_wss (syn_cima R (.cv a)) (.cv a)))
          (.objMem x a)))
      p0024 p0027_e01_recanon
  have p0028 :=
    @g_eleq2i C
      (syn_cint (.cab a (syn_wa (syn_wss S (.cv a)) (syn_wss (syn_cima R (.cv a)) (.cv a)))))
      (.cv y) p0023
  have p0029 := @g_vex y
  have p0030 :=
    @g_elintab (syn_wa (syn_wss S (.cv a)) (syn_wss (syn_cima R (.cv a)) (.cv a))) a
      (.cv y) dv_cache_0010 p0029
  have p0031_e01_recanon :
    Nominal.NPrf
      (syn_wb (.classMem (.cv y) (syn_cint
            (.cab a (syn_wa (syn_wss S (.cv a)) (syn_wss (syn_cima R (.cv a)) (.cv a))))))
        (.all a (.imp (syn_wa (syn_wss S (.cv a)) (syn_wss (syn_cima R (.cv a)) (.cv a)))
            (.objMem y a)))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wb syn_cint syn_wa syn_wss syn_cin syn_ccompl syn_cnin syn_wnan
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
    @g_bitri (.classMem (.cv y) C)
      (.classMem (.cv y) (syn_cint
          (.cab a (syn_wa (syn_wss S (.cv a)) (syn_wss (syn_cima R (.cv a)) (.cv a))))))
      (.all a (.imp (syn_wa (syn_wss S (.cv a)) (syn_wss (syn_cima R (.cv a)) (.cv a)))
          (.objMem y a)))
      p0028 p0031_e01_recanon
  have p0032 :=
    @g_n_3imtr4g (syn_wbr (.cv x) R (.cv y))
      (.all a (.imp (syn_wa (syn_wss S (.cv a)) (syn_wss (syn_cima R (.cv a)) (.cv a)))
          (.objMem x a)))
      (.all a (.imp (syn_wa (syn_wss S (.cv a)) (syn_wss (syn_cima R (.cv a)) (.cv a)))
          (.objMem y a)))
      (.classMem (.cv x) C) (.classMem (.cv y) C) p0021 p0027 p0031
  have p0033 :=
    @g_impcom (syn_wbr (.cv x) R (.cv y)) (.classMem (.cv x) C) (.classMem (.cv y) C)
      p0032
  have p0034 :=
    @g_vtocl2g
      (.imp (syn_wa (.classMem (.cv x) C) (syn_wbr (.cv x) R (.cv y))) (.classMem (.cv y) C))
      (.imp (syn_wa (.classMem A C) (syn_wbr A R (.cv y))) (.classMem (.cv y) C))
      (.imp (syn_wa (.classMem A C) (syn_wbr A R B)) (.classMem B C)) x y A B (syn_cvv)
      (syn_cvv) dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015
      p0005 p0009 p0033
  have p0035 :=
    @g_mpcom (syn_wa (.classMem A (syn_cvv)) (.classMem B (syn_cvv)))
      (syn_wa (.classMem A C) (syn_wbr A R B)) (.classMem B C) p0001 p0034
  exact p0035


end NFChoice.DirectNominalPrf.WPPReplay

end
