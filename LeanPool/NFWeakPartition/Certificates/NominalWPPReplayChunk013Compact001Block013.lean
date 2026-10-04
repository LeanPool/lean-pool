/-
Copyright (c) 2026 Elliot Glazer and NFNotWPP contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elliot Glazer and NFNotWPP contributors
-/

module

public import LeanPool.NFWeakPartition.Certificates.NominalWPPReplayChunk013Compact001Block012

/-! Nominal proof certificates grouped in dependency order. -/


public section

/-! Certificates from `NominalWPPReplayChunk013Compact001Part061`. -/


section

namespace NFChoice.DirectNominalPrf.WPPReplay

open scoped Fol
open NFChoice.Foundation
open NFChoice.SemanticCore
open NFChoice.ReplaySupport
open NFChoice.Compiler.CompactSourceSyntax

/-- Checked nominal proof certificate identified upstream as `g_csucex`. -/
@[expose]
noncomputable def gCsucex (x : Var) :
    Nominal.NPrf
      (.classMem (synCmpt x (synCvv) (synCplc (.cv x) (synC1c))) (synCvv)) :=
  by
  let proofSupport : Finset Var := ({ x } : Finset Var)
  let y : Var := freshVar proofSupport 0
  let z : Var := freshVar proofSupport 1
  let w : Var := freshVar proofSupport 2
  have fresh_y : y ∉ proofSupport :=
    by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_y_ne_x : y ≠ x := by
    intro h
    exact fresh_y (Finset.mem_singleton.mpr h)
  have fresh_x_ne_y : x ≠ y := Ne.symm fresh_y_ne_x
  have fresh_z : z ∉ proofSupport :=
    by
    change freshVar proofSupport 1 ∉ proofSupport
    exact freshVar_not_mem proofSupport 1
  have fresh_z_ne_x : z ≠ x := by
    intro h
    exact fresh_z (Finset.mem_singleton.mpr h)
  have fresh_x_ne_z : x ≠ z := Ne.symm fresh_z_ne_x
  have fresh_w : w ∉ proofSupport :=
    by
    change freshVar proofSupport 2 ∉ proofSupport
    exact freshVar_not_mem proofSupport 2
  have fresh_w_ne_x : w ≠ x := by
    intro h
    exact fresh_w (Finset.mem_singleton.mpr h)
  have fresh_x_ne_w : x ≠ w := Ne.symm fresh_w_ne_x
  have fresh_y_ne_z : y ≠ z :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have fresh_y_ne_w : y ≠ w :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 2
    exact freshVar_injective proofSupport (i := 0) (j := 2) (by decide)
  have fresh_w_ne_y : w ≠ y := Ne.symm fresh_y_ne_w
  have fresh_z_ne_w : z ≠ w :=
    by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 2
    exact freshVar_injective proofSupport (i := 1) (j := 2) (by decide)
  have fresh_w_ne_z : w ≠ z := Ne.symm fresh_z_ne_w
  have dv_cache_0001 : x ∉ ((Class.cv w)).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_x_ne_w, not_false_eq_true])
  have dv_cache_0002 : x ∉ ((Class.cv y)).fv :=
    by
    clear dv_cache_0001
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_x_ne_y, not_false_eq_true])
  have dv_cache_0003 :
    x ∉
      ((synWbr (.cv w) (synCres (synCaddcfn) (synCxp (synCvv) (synCsn (synC1c))))
          (.cv z))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cres,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_caddcfn,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxp,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c, Finset.mem_union,
          Finset.mem_singleton, fresh_x_ne_w, fresh_x_ne_z, compact_fv_not_mem_empty,
          or_false, not_false_eq_true])
  have dv_cache_0004 : x ∉ ((synC1c)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c,
          compact_fv_not_mem_empty, not_false_eq_true])
  have dv_cache_0005 : w ∉ ((synCop (.cv y) (.cv x))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact
      (by
        have compact_fv_not_mem_empty : w ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cop,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, fresh_w_ne_y, fresh_w_ne_x, or_false, not_false_eq_true])
  have dv_cache_0006 :
    w ∉
      ((synWa (.classEq (.cv x) (synC1c))
          (.classEq (synCplc (.cv y) (.cv x)) (.cv z)))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact
      (by
        have compact_fv_not_mem_empty : w ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cplc, Finset.mem_union,
          Finset.mem_singleton, fresh_w_ne_x, fresh_w_ne_y, fresh_w_ne_z,
          compact_fv_not_mem_empty, or_false, not_false_eq_true])
  have dv_cache_0007 : x ∉ ((Wff.classEq (synCplc (.cv y) (synC1c)) (.cv z))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cplc,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c, Finset.mem_union,
          Finset.mem_singleton, fresh_x_ne_y, fresh_x_ne_z, compact_fv_not_mem_empty,
          or_false, not_false_eq_true])
  have dv_cache_0008 : w ∉ ((Class.cv y)).fv :=
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
          fresh_w_ne_y, not_false_eq_true])
  have dv_cache_0009 : w ∉ ((Class.cv z)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008
    exact
      (by
        have compact_fv_not_mem_empty : w ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_w_ne_z, not_false_eq_true])
  have dv_cache_0010 :
    w ∉ ((synCres (synCaddcfn) (synCxp (synCvv) (synCsn (synC1c))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009
    exact
      (by
        have compact_fv_not_mem_empty : w ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cres,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_caddcfn,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxp,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c, Finset.mem_union,
          compact_fv_not_mem_empty, or_false, not_false_eq_true])
  have dv_cache_0011 : w ∉ ((synCcnv (synC1st))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010
    exact
      (by
        have compact_fv_not_mem_empty : w ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1st, compact_fv_not_mem_empty,
          not_false_eq_true])
  have dv_cache_0012 : w ∉ ((synCplc (.cv x) (synC1c))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
    exact
      (by
        have compact_fv_not_mem_empty : w ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cplc,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c, Finset.mem_union,
          Finset.mem_singleton, fresh_w_ne_x, compact_fv_not_mem_empty, or_false,
          not_false_eq_true])
  have dv_cache_0013 : x ≠ w :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012
    exact (show x ≠ w from (by exact fresh_x_ne_w))
  have dv_cache_0014 : x ∉ ((Class.cv z)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_x_ne_z, not_false_eq_true])
  have dv_cache_0015 : w ∉ ((Wff.classEq (synCplc (.cv y) (synC1c)) (.cv z))).fv :=
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
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cplc,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c, Finset.mem_union,
          Finset.mem_singleton, fresh_w_ne_y, fresh_w_ne_z, compact_fv_not_mem_empty,
          or_false, not_false_eq_true])
  have dv_cache_0016 : y ∉ ((synCmpt x (synCvv) (synCplc (.cv x) (synC1c)))).fv :=
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
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cmpt,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cplc,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c, Finset.mem_union,
          Finset.mem_erase, Finset.mem_singleton, fresh_y_ne_x, compact_fv_not_mem_empty,
          or_false, and_false, not_false_eq_true])
  have dv_cache_0017 : z ∉ ((synCmpt x (synCvv) (synCplc (.cv x) (synC1c)))).fv :=
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
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cmpt,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cplc,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c, Finset.mem_union,
          Finset.mem_erase, Finset.mem_singleton, fresh_z_ne_x, compact_fv_not_mem_empty,
          or_false, and_false, not_false_eq_true])
  have dv_cache_0018 :
    y ∉
      ((synCcom (synCres (synCaddcfn) (synCxp (synCvv) (synCsn (synC1c))))
          (synCcnv (synC1st)))).fv :=
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
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccom,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cres,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_caddcfn,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxp,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1st, Finset.mem_union,
          compact_fv_not_mem_empty, or_false, not_false_eq_true])
  have dv_cache_0019 :
    z ∉
      ((synCcom (synCres (synCaddcfn) (synCxp (synCvv) (synCsn (synC1c))))
          (synCcnv (synC1st)))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018
    exact
      (by
        have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccom,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cres,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_caddcfn,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxp,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1st, Finset.mem_union,
          compact_fv_not_mem_empty, or_false, not_false_eq_true])
  have dv_cache_0020 : y ≠ z :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019
    exact (show y ≠ z from (by exact fresh_y_ne_z))
  have p0000 := @gBrcnv (.cv y) (.cv w) (synC1st)
  have p0001 := @gVex y
  have p0002 := @gBr1st x (.cv w) (.cv y) dv_cache_0001 dv_cache_0002 p0001
  have p0003 :=
    @gBitri (synWbr (.cv y) (synCcnv (synC1st)) (.cv w))
      (synWbr (.cv w) (synC1st) (.cv y))
      (synWex x (.classEq (.cv w) (synCop (.cv y) (.cv x)))) p0000 p0002
  have p0004 :=
    @gAnbi1i (synWbr (.cv y) (synCcnv (synC1st)) (.cv w))
      (synWex x (.classEq (.cv w) (synCop (.cv y) (.cv x))))
      (synWbr (.cv w) (synCres (synCaddcfn) (synCxp (synCvv) (synCsn (synC1c)))) (.cv z))
      p0003
  have p0005 :=
    @gN1941v (.classEq (.cv w) (synCop (.cv y) (.cv x)))
      (synWbr (.cv w) (synCres (synCaddcfn) (synCxp (synCvv) (synCsn (synC1c)))) (.cv z))
      x dv_cache_0003
  have p0006 :=
    @gBitr4i
      (synWa (synWbr (.cv y) (synCcnv (synC1st)) (.cv w))
        (synWbr (.cv w) (synCres (synCaddcfn) (synCxp (synCvv) (synCsn (synC1c))))
          (.cv z)))
      (synWa (synWex x (.classEq (.cv w) (synCop (.cv y) (.cv x))))
        (synWbr (.cv w) (synCres (synCaddcfn) (synCxp (synCvv) (synCsn (synC1c))))
          (.cv z)))
      (synWex x (synWa (.classEq (.cv w) (synCop (.cv y) (.cv x))) (synWbr (.cv w)
            (synCres (synCaddcfn) (synCxp (synCvv) (synCsn (synC1c)))) (.cv z))))
      p0004 p0005
  have p0007 :=
    @gExbii
      (synWa (synWbr (.cv y) (synCcnv (synC1st)) (.cv w))
        (synWbr (.cv w) (synCres (synCaddcfn) (synCxp (synCvv) (synCsn (synC1c))))
          (.cv z)))
      (synWex x (synWa (.classEq (.cv w) (synCop (.cv y) (.cv x))) (synWbr (.cv w)
            (synCres (synCaddcfn) (synCxp (synCvv) (synCsn (synC1c)))) (.cv z))))
      w p0006
  have p0008 :=
    @gExcom
      (synWa (.classEq (.cv w) (synCop (.cv y) (.cv x)))
        (synWbr (.cv w) (synCres (synCaddcfn) (synCxp (synCvv) (synCsn (synC1c))))
          (.cv z)))
      w x
  have p0009 := @gVex x
  have p0010 := @gOpex (.cv y) (.cv x) p0001 p0009
  have p0011 :=
    @gBreq1 (.cv w) (synCop (.cv y) (.cv x)) (.cv z)
      (synCres (synCaddcfn) (synCxp (synCvv) (synCsn (synC1c))))
  have p0012 :=
    @gBrres (synCop (.cv y) (.cv x)) (.cv z) (synCaddcfn)
      (synCxp (synCvv) (synCsn (synC1c)))
  have p0013 := @gBraddcfn (.cv y) (.cv x) (.cv z) p0001 p0009
  have p0014 := @gOpelxp (.cv y) (.cv x) (synCvv) (synCsn (synC1c))
  have p0015 :=
    @gMpbiran
      (.classMem (synCop (.cv y) (.cv x)) (synCxp (synCvv) (synCsn (synC1c))))
      (.classMem (.cv y) (synCvv)) (.classMem (.cv x) (synCsn (synC1c))) p0001 p0014
  have p0016 := @gElsn x (synC1c) dv_cache_0004
  have p0017 :=
    @gBitri (.classMem (synCop (.cv y) (.cv x)) (synCxp (synCvv) (synCsn (synC1c))))
      (.classMem (.cv x) (synCsn (synC1c))) (.classEq (.cv x) (synC1c)) p0015 p0016
  have p0018 :=
    @gAnbi12ci (synWbr (synCop (.cv y) (.cv x)) (synCaddcfn) (.cv z))
      (.classEq (synCplc (.cv y) (.cv x)) (.cv z))
      (.classMem (synCop (.cv y) (.cv x)) (synCxp (synCvv) (synCsn (synC1c))))
      (.classEq (.cv x) (synC1c)) p0013 p0017
  have p0019 :=
    @gBitri
      (synWbr (synCop (.cv y) (.cv x))
        (synCres (synCaddcfn) (synCxp (synCvv) (synCsn (synC1c)))) (.cv z))
      (synWa (synWbr (synCop (.cv y) (.cv x)) (synCaddcfn) (.cv z))
        (.classMem (synCop (.cv y) (.cv x)) (synCxp (synCvv) (synCsn (synC1c)))))
      (synWa (.classEq (.cv x) (synC1c)) (.classEq (synCplc (.cv y) (.cv x)) (.cv z)))
      p0012 p0018
  have p0020 :=
    @gSyl6bb (.classEq (.cv w) (synCop (.cv y) (.cv x)))
      (synWbr (.cv w) (synCres (synCaddcfn) (synCxp (synCvv) (synCsn (synC1c)))) (.cv z))
      (synWbr (synCop (.cv y) (.cv x))
        (synCres (synCaddcfn) (synCxp (synCvv) (synCsn (synC1c)))) (.cv z))
      (synWa (.classEq (.cv x) (synC1c)) (.classEq (synCplc (.cv y) (.cv x)) (.cv z)))
      p0011 p0019
  have p0021 :=
    @gCeqsexv
      (synWbr (.cv w) (synCres (synCaddcfn) (synCxp (synCvv) (synCsn (synC1c)))) (.cv z))
      (synWa (.classEq (.cv x) (synC1c)) (.classEq (synCplc (.cv y) (.cv x)) (.cv z)))
      w (synCop (.cv y) (.cv x)) dv_cache_0005 dv_cache_0006 p0010 p0020
  have p0022 :=
    @gExbii
      (synWex w (synWa (.classEq (.cv w) (synCop (.cv y) (.cv x))) (synWbr (.cv w)
            (synCres (synCaddcfn) (synCxp (synCvv) (synCsn (synC1c)))) (.cv z))))
      (synWa (.classEq (.cv x) (synC1c)) (.classEq (synCplc (.cv y) (.cv x)) (.cv z)))
      x p0021
  have p0023 :=
    @gBitri
      (synWex w (synWex x (synWa (.classEq (.cv w) (synCop (.cv y) (.cv x)))
            (synWbr (.cv w)
              (synCres (synCaddcfn) (synCxp (synCvv) (synCsn (synC1c)))) (.cv z)))))
      (synWex x (synWex w (synWa (.classEq (.cv w) (synCop (.cv y) (.cv x)))
            (synWbr (.cv w)
              (synCres (synCaddcfn) (synCxp (synCvv) (synCsn (synC1c)))) (.cv z)))))
      (synWex x (synWa (.classEq (.cv x) (synC1c))
          (.classEq (synCplc (.cv y) (.cv x)) (.cv z))))
      p0008 p0022
  have p0024 :=
    @gBitri
      (synWex w (synWa (synWbr (.cv y) (synCcnv (synC1st)) (.cv w)) (synWbr (.cv w)
            (synCres (synCaddcfn) (synCxp (synCvv) (synCsn (synC1c)))) (.cv z))))
      (synWex w (synWex x (synWa (.classEq (.cv w) (synCop (.cv y) (.cv x)))
            (synWbr (.cv w)
              (synCres (synCaddcfn) (synCxp (synCvv) (synCsn (synC1c)))) (.cv z)))))
      (synWex x (synWa (.classEq (.cv x) (synC1c))
          (.classEq (synCplc (.cv y) (.cv x)) (.cv z))))
      p0007 p0023
  have p0025 := @gN1cex
  have p0026 := @gAddceq2 (.cv x) (synC1c) (.cv y)
  have p0027 :=
    @gEqeq1d (.classEq (.cv x) (synC1c)) (synCplc (.cv y) (.cv x))
      (synCplc (.cv y) (synC1c)) (.cv z) p0026
  have p0028 :=
    @gCeqsexv (.classEq (synCplc (.cv y) (.cv x)) (.cv z))
      (.classEq (synCplc (.cv y) (synC1c)) (.cv z)) x (synC1c) dv_cache_0004
      dv_cache_0007 p0025 p0027
  have p0029 :=
    @gBitri
      (synWex w (synWa (synWbr (.cv y) (synCcnv (synC1st)) (.cv w)) (synWbr (.cv w)
            (synCres (synCaddcfn) (synCxp (synCvv) (synCsn (synC1c)))) (.cv z))))
      (synWex x (synWa (.classEq (.cv x) (synC1c))
          (.classEq (synCplc (.cv y) (.cv x)) (.cv z))))
      (.classEq (synCplc (.cv y) (synC1c)) (.cv z)) p0024 p0028
  have p0030 :=
    @gOpelco w (.cv y) (.cv z)
      (synCres (synCaddcfn) (synCxp (synCvv) (synCsn (synC1c))))
      (synCcnv (synC1st)) dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
  have p0031 := @gMptv x w (synCplc (.cv x) (synC1c)) dv_cache_0012 dv_cache_0013
  have p0032 :=
    @gEleq2i (synCmpt x (synCvv) (synCplc (.cv x) (synC1c)))
      (synCopab x w (.classEq (.cv w) (synCplc (.cv x) (synC1c))))
      (synCop (.cv y) (.cv z)) p0031
  have p0033 := @gVex z
  have p0034 := @gAddceq1 (.cv x) (.cv y) (synC1c)
  have p0035_e00_recanon :
    Nominal.NPrf
      (.imp (.objEq x y)
        (.classEq (synCplc (.cv x) (synC1c)) (synCplc (.cv y) (synC1c)))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold synCplc synWrex synWex synWa synC1c
        simp (config :=
          { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_class_cv]
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
        · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0034
  have p0035 :=
    @gEqeq2d (.objEq x y) (synCplc (.cv x) (synC1c)) (synCplc (.cv y) (synC1c))
      (.cv w) p0035_e00_recanon
  have p0036 := @gEqeq1 (.cv w) (.cv z) (synCplc (.cv y) (synC1c))
  have p0037 := @gEqcom (.cv z) (synCplc (.cv y) (synC1c))
  have p0038_e00_recanon :
    Nominal.NPrf
      (.imp (.objEq w z) (synWb (.classEq (.cv w) (synCplc (.cv y) (synC1c)))
          (.classEq (.cv z) (synCplc (.cv y) (synC1c))))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold synWb synCplc synWrex synWex synWa synC1c
        simp (config :=
          { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_class_cv]
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
        · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0036
  have p0038 :=
    @gSyl6bb (.objEq w z) (.classEq (.cv w) (synCplc (.cv y) (synC1c)))
      (.classEq (.cv z) (synCplc (.cv y) (synC1c)))
      (.classEq (synCplc (.cv y) (synC1c)) (.cv z)) p0038_e00_recanon p0037
  have p0039_e02_recanon :
    Nominal.NPrf
      (.imp (.classEq (.cv x) (.cv y)) (synWb (.classEq (.cv w) (synCplc (.cv x) (synC1c)))
          (.classEq (.cv w) (synCplc (.cv y) (synC1c))))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold synWb synCplc synWrex synWex synWa synC1c
        simp (config :=
          { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_class_cv]
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · exact Nominal.RecanonTransportDev.TRecanonWff.objEq_classEq _ _
        · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0035
  have p0039_e03_recanon :
    Nominal.NPrf
      (.imp (.classEq (.cv w) (.cv z)) (synWb (.classEq (.cv w) (synCplc (.cv y) (synC1c)))
          (.classEq (synCplc (.cv y) (synC1c)) (.cv z)))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold synWb synCplc synWrex synWex synWa synC1c
        simp (config :=
          { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_class_cv]
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · exact Nominal.RecanonTransportDev.TRecanonWff.objEq_classEq _ _
        · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0038
  have p0039 :=
    @gOpelopab (.classEq (.cv w) (synCplc (.cv x) (synC1c)))
      (.classEq (.cv w) (synCplc (.cv y) (synC1c)))
      (.classEq (synCplc (.cv y) (synC1c)) (.cv z)) x w (.cv y) (.cv z) dv_cache_0002
      dv_cache_0008 dv_cache_0014 dv_cache_0009 dv_cache_0007 dv_cache_0015 dv_cache_0013
      p0001 p0033 p0039_e02_recanon p0039_e03_recanon
  have p0040 :=
    @gBitri
      (.classMem (synCop (.cv y) (.cv z)) (synCmpt x (synCvv) (synCplc (.cv x) (synC1c))))
      (.classMem (synCop (.cv y) (.cv z))
        (synCopab x w (.classEq (.cv w) (synCplc (.cv x) (synC1c)))))
      (.classEq (synCplc (.cv y) (synC1c)) (.cv z)) p0032 p0039
  have p0041 :=
    @gN3bitr4ri
      (synWex w (synWa (synWbr (.cv y) (synCcnv (synC1st)) (.cv w)) (synWbr (.cv w)
            (synCres (synCaddcfn) (synCxp (synCvv) (synCsn (synC1c)))) (.cv z))))
      (.classEq (synCplc (.cv y) (synC1c)) (.cv z))
      (.classMem (synCop (.cv y) (.cv z))
        (synCcom (synCres (synCaddcfn) (synCxp (synCvv) (synCsn (synC1c))))
          (synCcnv (synC1st))))
      (.classMem (synCop (.cv y) (.cv z)) (synCmpt x (synCvv) (synCplc (.cv x) (synC1c))))
      p0029 p0030 p0040
  have p0042 :=
    @gEqrelriv y z (synCmpt x (synCvv) (synCplc (.cv x) (synC1c)))
      (synCcom (synCres (synCaddcfn) (synCxp (synCvv) (synCsn (synC1c))))
        (synCcnv (synC1st)))
      dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 p0041
  have p0043 := @gAddcfnex
  have p0044 := @gVvex
  have p0045 := @gSnex (synC1c)
  have p0046 := @gXpex (synCvv) (synCsn (synC1c)) p0044 p0045
  have p0047 := @gResex (synCaddcfn) (synCxp (synCvv) (synCsn (synC1c))) p0043 p0046
  have p0048 := @gN1stex
  have p0049 := @gCnvex (synC1st) p0048
  have p0050 :=
    @gCoex (synCres (synCaddcfn) (synCxp (synCvv) (synCsn (synC1c))))
      (synCcnv (synC1st)) p0047 p0049
  have p0051 :=
    @gEqeltri (synCmpt x (synCvv) (synCplc (.cv x) (synC1c)))
      (synCcom (synCres (synCaddcfn) (synCxp (synCvv) (synCsn (synC1c))))
        (synCcnv (synC1st)))
      (synCvv) p0042 p0050
  exact p0051

/-- Checked nominal proof certificate identified upstream as `g_brcsuc`. -/
@[expose]
noncomputable def gBrcsuc (x : Var) (A : Class) (B : Class) (dv_A_x : x ∉ A.fv)
    (dv_B_x : x ∉ B.fv) (hyp_brcsuc_1 : Nominal.NPrf (.classMem A (synCvv)))
    (hyp_brcsuc_2 : Nominal.NPrf (.classMem B (synCvv))) :
    Nominal.NPrf
      (synWb (synWbr A (synCmpt x (synCvv) (synCplc (.cv x) (synC1c))) B)
        (.classEq B (synCplc A (synC1c)))) :=
  by
  let proofSupport : Finset Var := ({ x } : Finset Var) ∪ A.fv ∪ B.fv
  let y : Var := freshVar proofSupport 0
  have fresh_y : y ∉ proofSupport :=
    by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_y_ne_x : y ≠ x := by
    intro h
    exact
      fresh_y
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_singleton.mpr h)))
  have fresh_x_ne_y : x ≠ y := Ne.symm fresh_y_ne_x
  have fresh_y_not_A : y ∉ A.fv := by
    intro h
    exact fresh_y (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_y_not_B : y ∉ B.fv := by
    intro h
    exact fresh_y (Finset.mem_union_right _ (h))
  have dv_cache_0001 : y ∉ ((synCplc (.cv x) (synC1c))).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cplc,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c, Finset.mem_union,
          Finset.mem_singleton, fresh_y_ne_x, compact_fv_not_mem_empty, or_false,
          not_false_eq_true])
  have dv_cache_0002 : x ≠ y := by
    clear dv_cache_0001
    exact (show x ≠ y from (by exact fresh_x_ne_y))
  have dv_cache_0003 : x ∉ (A).fv :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_A_x, not_false_eq_true])
  have dv_cache_0004 : y ∉ (A).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_y_not_A, not_false_eq_true])
  have dv_cache_0005 : x ∉ (B).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_B_x, not_false_eq_true])
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
  have dv_cache_0007 : x ∉ ((Wff.classEq B (synCplc A (synC1c)))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cplc,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c, Finset.mem_union, dv_B_x,
          dv_A_x, compact_fv_not_mem_empty, or_false, not_false_eq_true])
  have dv_cache_0008 : y ∉ ((Wff.classEq B (synCplc A (synC1c)))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cplc,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c, Finset.mem_union,
          fresh_y_not_B, fresh_y_not_A, compact_fv_not_mem_empty, or_false,
          not_false_eq_true])
  have p0000 := @gAddceq1 (.cv x) A (synC1c)
  have p0001 :=
    @gEqeq2d (.classEq (.cv x) A) (synCplc (.cv x) (synC1c)) (synCplc A (synC1c))
      (.cv y) p0000
  have p0002 := @gEqeq1 (.cv y) B (synCplc A (synC1c))
  have p0003 := @gMptv x y (synCplc (.cv x) (synC1c)) dv_cache_0001 dv_cache_0002
  have p0004 :=
    @gBrab (.classEq (.cv y) (synCplc (.cv x) (synC1c)))
      (.classEq (.cv y) (synCplc A (synC1c))) (.classEq B (synCplc A (synC1c))) x y A
      B (synCmpt x (synCvv) (synCplc (.cv x) (synC1c))) dv_cache_0003 dv_cache_0004
      dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0002 hyp_brcsuc_1
      hyp_brcsuc_2 p0001 p0002 p0003
  exact p0004


end NFChoice.DirectNominalPrf.WPPReplay

end

/-! Certificates from `NominalWPPReplayChunk013Compact001Part062`. -/


section

namespace NFChoice.DirectNominalPrf.WPPReplay

open scoped Fol
open NFChoice.Foundation
open NFChoice.SemanticCore
open NFChoice.ReplaySupport
open NFChoice.Compiler.CompactSourceSyntax

/-- Checked nominal proof certificate identified upstream as `g_nncdiv3lem1`. -/
@[expose]
noncomputable def gNncdiv3lem1 (n : Var) (b : Var) :
    Nominal.NPrf
      (synWb (.classMem (synCop (.cv n) (.cv b)) (synCrn (synCin (synCins3 (synCcnv
                  (synCima (synCtxp (synCrn
                        (synCtxp (synCcnv (synC1st)) (synCin (synC1st) (synC2nd))))
                      (synC2nd)) (synCaddcfn)))) (synCima
                (synCtxp (synCcom (synC1st) (synC1st))
                  (synCtxp (synCcom (synC2nd) (synC1st)) (synC2nd))) (synCaddcfn)))))
        (.classEq (.cv b) (synCplc (synCplc (.cv n) (.cv n)) (.cv n)))) :=
  by
  let proofSupport : Finset Var := ({ n } : Finset Var) ∪ ({ b } : Finset Var)
  let m : Var := freshVar proofSupport 0
  let t : Var := freshVar proofSupport 1
  have fresh_m : m ∉ proofSupport :=
    by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_m_ne_n : m ≠ n := by
    intro h
    exact fresh_m (Finset.mem_union_left _ (Finset.mem_singleton.mpr h))
  have fresh_n_ne_m : n ≠ m := Ne.symm fresh_m_ne_n
  have fresh_m_ne_b : m ≠ b := by
    intro h
    exact fresh_m (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))
  have fresh_t : t ∉ proofSupport :=
    by
    change freshVar proofSupport 1 ∉ proofSupport
    exact freshVar_not_mem proofSupport 1
  have fresh_t_ne_n : t ≠ n := by
    intro h
    exact fresh_t (Finset.mem_union_left _ (Finset.mem_singleton.mpr h))
  have fresh_n_ne_t : n ≠ t := Ne.symm fresh_t_ne_n
  have fresh_t_ne_b : t ≠ b := by
    intro h
    exact fresh_t (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))
  have fresh_m_ne_t : m ≠ t :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have fresh_t_ne_m : t ≠ m := Ne.symm fresh_m_ne_t
  have dv_cache_0001 : m ∉ ((synCop (.cv n) (.cv b))).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : m ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cop,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, fresh_m_ne_n, fresh_m_ne_b, or_false, not_false_eq_true])
  have dv_cache_0002 :
    m ∉
      ((synCin (synCins3 (synCcnv (synCima (synCtxp (synCrn
                    (synCtxp (synCcnv (synC1st)) (synCin (synC1st) (synC2nd))))
                  (synC2nd)) (synCaddcfn)))) (synCima
            (synCtxp (synCcom (synC1st) (synC1st))
              (synCtxp (synCcom (synC2nd) (synC1st)) (synC2nd))) (synCaddcfn)))).fv :=
    by
    clear dv_cache_0001
    exact
      (by
        have compact_fv_not_mem_empty : m ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins3,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cima,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ctxp,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_crn,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1st,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c2nd,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_caddcfn,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccom, Finset.mem_union,
          compact_fv_not_mem_empty, or_false, not_false_eq_true])
  have dv_cache_0003 : m ∉ ((synCop (.cv t) (.cv n))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact
      (by
        have compact_fv_not_mem_empty : m ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cop,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, fresh_m_ne_t, fresh_m_ne_n, or_false, not_false_eq_true])
  have dv_cache_0004 :
    m ∉ ((synCtxp (synCcnv (synC1st)) (synCin (synC1st) (synC2nd)))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact
      (by
        have compact_fv_not_mem_empty : m ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ctxp,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1st,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c2nd, Finset.mem_union,
          compact_fv_not_mem_empty, or_false, not_false_eq_true])
  have dv_cache_0005 : m ∉ ((synCproj1 (.cv t))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact
      (by
        have compact_fv_not_mem_empty : m ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cproj1,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton, fresh_m_ne_t,
          not_false_eq_true])
  have dv_cache_0006 : m ∉ ((synCop (.cv n) (.cv n))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact
      (by
        have compact_fv_not_mem_empty : m ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cop,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, fresh_m_ne_n, or_false, not_false_eq_true])
  have dv_cache_0007 : t ∉ ((synCop (.cv n) (.cv m))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006
    exact
      (by
        have compact_fv_not_mem_empty : t ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cop,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, fresh_t_ne_n, fresh_t_ne_m, or_false, not_false_eq_true])
  have dv_cache_0008 :
    t ∉
      ((synCtxp (synCrn (synCtxp (synCcnv (synC1st)) (synCin (synC1st) (synC2nd))))
          (synC2nd))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007
    exact
      (by
        have compact_fv_not_mem_empty : t ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ctxp,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_crn,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1st,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c2nd, Finset.mem_union,
          compact_fv_not_mem_empty, or_false, not_false_eq_true])
  have dv_cache_0009 : t ∉ ((synCaddcfn)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008
    exact
      (by
        have compact_fv_not_mem_empty : t ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_caddcfn,
          compact_fv_not_mem_empty, not_false_eq_true])
  have dv_cache_0010 : t ∉ ((synCop (synCop (.cv n) (.cv n)) (.cv m))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009
    exact
      (by
        have compact_fv_not_mem_empty : t ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cop,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, fresh_t_ne_n, fresh_t_ne_m, or_false, not_false_eq_true])
  have dv_cache_0011 : t ∉ ((synCop (.cv m) (synCop (.cv n) (.cv b)))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010
    exact
      (by
        have compact_fv_not_mem_empty : t ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cop,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, fresh_t_ne_m, fresh_t_ne_n, fresh_t_ne_b, or_false,
          not_false_eq_true])
  have dv_cache_0012 :
    t ∉
      ((synCtxp (synCcom (synC1st) (synC1st))
          (synCtxp (synCcom (synC2nd) (synC1st)) (synC2nd)))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
    exact
      (by
        have compact_fv_not_mem_empty : t ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ctxp,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccom,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1st,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c2nd, Finset.mem_union,
          compact_fv_not_mem_empty, or_false, not_false_eq_true])
  have dv_cache_0013 : n ∉ ((Class.cv t)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012
    exact
      (by
        have compact_fv_not_mem_empty : n ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_n_ne_t, not_false_eq_true])
  have dv_cache_0014 : n ∉ ((Class.cv m)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013
    exact
      (by
        have compact_fv_not_mem_empty : n ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_n_ne_m, not_false_eq_true])
  have dv_cache_0015 : n ∉ ((synC1st)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014
    exact
      (by
        have compact_fv_not_mem_empty : n ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1st,
          compact_fv_not_mem_empty, not_false_eq_true])
  have dv_cache_0016 : n ∉ ((synCproj1 (.cv t))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015
    exact
      (by
        have compact_fv_not_mem_empty : n ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cproj1,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton, fresh_n_ne_t,
          not_false_eq_true])
  have dv_cache_0017 : n ∉ ((synWbr (synCproj1 (.cv t)) (synC1st) (.cv m))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016
    exact
      (by
        have compact_fv_not_mem_empty : n ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cproj1,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1st, Finset.mem_union,
          Finset.mem_singleton, fresh_n_ne_t, fresh_n_ne_m, compact_fv_not_mem_empty,
          or_false, not_false_eq_true])
  have dv_cache_0018 : m ∉ ((Class.cv t)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
    exact
      (by
        have compact_fv_not_mem_empty : m ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_m_ne_t, not_false_eq_true])
  have dv_cache_0019 : m ∉ ((Class.cv n)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018
    exact
      (by
        have compact_fv_not_mem_empty : m ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_m_ne_n, not_false_eq_true])
  have dv_cache_0020 : m ∉ ((synC2nd)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019
    exact
      (by
        have compact_fv_not_mem_empty : m ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c2nd,
          compact_fv_not_mem_empty, not_false_eq_true])
  have dv_cache_0021 : m ∉ ((synC1st)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020
    exact
      (by
        have compact_fv_not_mem_empty : m ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1st,
          compact_fv_not_mem_empty, not_false_eq_true])
  have dv_cache_0022 : m ∉ ((synWbr (synCproj1 (.cv t)) (synC2nd) (.cv n))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021
    exact
      (by
        have compact_fv_not_mem_empty : m ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cproj1,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c2nd, Finset.mem_union,
          Finset.mem_singleton, fresh_m_ne_t, fresh_m_ne_n, compact_fv_not_mem_empty,
          or_false, not_false_eq_true])
  have dv_cache_0023 : t ∉ ((synCop (synCop (.cv m) (.cv n)) (.cv b))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022
    exact
      (by
        have compact_fv_not_mem_empty : t ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cop,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, fresh_t_ne_m, fresh_t_ne_n, fresh_t_ne_b, or_false,
          not_false_eq_true])
  have dv_cache_0024 : m ∉ ((synCplc (.cv n) (.cv n))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
    exact
      (by
        have compact_fv_not_mem_empty : m ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cplc,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, fresh_m_ne_n, or_false, not_false_eq_true])
  have dv_cache_0025 :
    m ∉ ((Wff.classEq (.cv b) (synCplc (synCplc (.cv n) (.cv n)) (.cv n)))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024
    exact
      (by
        have compact_fv_not_mem_empty : m ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cplc, Finset.mem_union,
          Finset.mem_singleton, fresh_m_ne_b, fresh_m_ne_n, or_false, not_false_eq_true])
  have p0000 :=
    @gElrn2 m (synCop (.cv n) (.cv b))
      (synCin (synCins3 (synCcnv (synCima (synCtxp
                (synCrn (synCtxp (synCcnv (synC1st)) (synCin (synC1st) (synC2nd))))
                (synC2nd)) (synCaddcfn)))) (synCima
          (synCtxp (synCcom (synC1st) (synC1st))
            (synCtxp (synCcom (synC2nd) (synC1st)) (synC2nd))) (synCaddcfn)))
      dv_cache_0001 dv_cache_0002
  have p0001 :=
    @gElin (synCop (.cv m) (synCop (.cv n) (.cv b)))
      (synCins3 (synCcnv (synCima (synCtxp
              (synCrn (synCtxp (synCcnv (synC1st)) (synCin (synC1st) (synC2nd))))
              (synC2nd)) (synCaddcfn))))
      (synCima (synCtxp (synCcom (synC1st) (synC1st))
          (synCtxp (synCcom (synC2nd) (synC1st)) (synC2nd))) (synCaddcfn))
  have p0002 := @gVex b
  have p0003 :=
    @gOtelins3 (.cv m) (.cv n) (.cv b)
      (synCcnv (synCima (synCtxp
            (synCrn (synCtxp (synCcnv (synC1st)) (synCin (synC1st) (synC2nd))))
            (synC2nd)) (synCaddcfn)))
      p0002
  have p0004 :=
    @gOpelcnv (.cv m) (.cv n)
      (synCima (synCtxp
          (synCrn (synCtxp (synCcnv (synC1st)) (synCin (synC1st) (synC2nd)))) (synC2nd))
        (synCaddcfn))
  have p0005 :=
    @gTrtxp (.cv t) (.cv n) (.cv m)
      (synCrn (synCtxp (synCcnv (synC1st)) (synCin (synC1st) (synC2nd))))
      (synC2nd)
  have p0006 :=
    (Nominal.biimpRefl (synWbr (.cv t)
        (synCrn (synCtxp (synCcnv (synC1st)) (synCin (synC1st) (synC2nd)))) (.cv n)))
  have p0007 :=
    @gElrn2 m (synCop (.cv t) (.cv n))
      (synCtxp (synCcnv (synC1st)) (synCin (synC1st) (synC2nd))) dv_cache_0003
      dv_cache_0004
  have p0008 := @gVex t
  have p0009 := @gProj1ex (.cv t) p0008
  have p0010 :=
    @gEqvinc m (synCproj1 (.cv t)) (synCop (.cv n) (.cv n)) dv_cache_0005 dv_cache_0006
      p0009
  have p0011 := @gOpeq (.cv t)
  have p0012 :=
    @gBreq1i (.cv t) (synCop (synCproj1 (.cv t)) (synCproj2 (.cv t)))
      (synCop (.cv n) (.cv n)) (synC1st) p0011
  have p0013 := @gProj2ex (.cv t) p0008
  have p0014 :=
    @gOpbr1st (synCproj1 (.cv t)) (synCproj2 (.cv t)) (synCop (.cv n) (.cv n)) p0009
      p0013
  have p0015 :=
    @gBitri (synWbr (.cv t) (synC1st) (synCop (.cv n) (.cv n)))
      (synWbr (synCop (synCproj1 (.cv t)) (synCproj2 (.cv t))) (synC1st)
        (synCop (.cv n) (.cv n)))
      (.classEq (synCproj1 (.cv t)) (synCop (.cv n) (.cv n))) p0012 p0014
  have p0016 :=
    @gOteltxp (.cv m) (.cv t) (.cv n) (synCcnv (synC1st))
      (synCin (synC1st) (synC2nd))
  have p0017 := @gOpelcnv (.cv m) (.cv t) (synC1st)
  have p0018 := (Nominal.biimpRefl (synWbr (.cv t) (synC1st) (.cv m)))
  have p0019 :=
    @gBreq1i (.cv t) (synCop (synCproj1 (.cv t)) (synCproj2 (.cv t))) (.cv m)
      (synC1st) p0011
  have p0020 := @gOpbr1st (synCproj1 (.cv t)) (synCproj2 (.cv t)) (.cv m) p0009 p0013
  have p0021 := @gEqcom (synCproj1 (.cv t)) (.cv m)
  have p0022 :=
    @gN3bitri (synWbr (.cv t) (synC1st) (.cv m))
      (synWbr (synCop (synCproj1 (.cv t)) (synCproj2 (.cv t))) (synC1st) (.cv m))
      (.classEq (synCproj1 (.cv t)) (.cv m)) (.classEq (.cv m) (synCproj1 (.cv t)))
      p0019 p0020 p0021
  have p0023 :=
    @gN3bitr2i (.classMem (synCop (.cv m) (.cv t)) (synCcnv (synC1st)))
      (.classMem (synCop (.cv t) (.cv m)) (synC1st))
      (synWbr (.cv t) (synC1st) (.cv m)) (.classEq (.cv m) (synCproj1 (.cv t))) p0017
      p0018 p0022
  have p0024 := @gElin (synCop (.cv m) (.cv n)) (synC1st) (synC2nd)
  have p0025 := (Nominal.biimpRefl (synWbr (.cv m) (synC1st) (.cv n)))
  have p0026 := (Nominal.biimpRefl (synWbr (.cv m) (synC2nd) (.cv n)))
  have p0027 :=
    @gAnbi12i (synWbr (.cv m) (synC1st) (.cv n))
      (.classMem (synCop (.cv m) (.cv n)) (synC1st))
      (synWbr (.cv m) (synC2nd) (.cv n))
      (.classMem (synCop (.cv m) (.cv n)) (synC2nd)) p0025 p0026
  have p0028 := @gVex n
  have p0029 := @gOp1st2nd (.cv n) (.cv n) (.cv m) p0028 p0028
  have p0030 :=
    @gN3bitr2i (.classMem (synCop (.cv m) (.cv n)) (synCin (synC1st) (synC2nd)))
      (synWa (.classMem (synCop (.cv m) (.cv n)) (synC1st))
        (.classMem (synCop (.cv m) (.cv n)) (synC2nd)))
      (synWa (synWbr (.cv m) (synC1st) (.cv n)) (synWbr (.cv m) (synC2nd) (.cv n)))
      (.classEq (.cv m) (synCop (.cv n) (.cv n))) p0024 p0027 p0029
  have p0031 :=
    @gAnbi12i (.classMem (synCop (.cv m) (.cv t)) (synCcnv (synC1st)))
      (.classEq (.cv m) (synCproj1 (.cv t)))
      (.classMem (synCop (.cv m) (.cv n)) (synCin (synC1st) (synC2nd)))
      (.classEq (.cv m) (synCop (.cv n) (.cv n))) p0023 p0030
  have p0032 :=
    @gBitri
      (.classMem (synCop (.cv m) (synCop (.cv t) (.cv n)))
        (synCtxp (synCcnv (synC1st)) (synCin (synC1st) (synC2nd))))
      (synWa (.classMem (synCop (.cv m) (.cv t)) (synCcnv (synC1st)))
        (.classMem (synCop (.cv m) (.cv n)) (synCin (synC1st) (synC2nd))))
      (synWa (.classEq (.cv m) (synCproj1 (.cv t)))
        (.classEq (.cv m) (synCop (.cv n) (.cv n))))
      p0016 p0031
  have p0033 :=
    @gExbii
      (.classMem (synCop (.cv m) (synCop (.cv t) (.cv n)))
        (synCtxp (synCcnv (synC1st)) (synCin (synC1st) (synC2nd))))
      (synWa (.classEq (.cv m) (synCproj1 (.cv t)))
        (.classEq (.cv m) (synCop (.cv n) (.cv n))))
      m p0032
  have p0034 :=
    @gN3bitr4ri (.classEq (synCproj1 (.cv t)) (synCop (.cv n) (.cv n)))
      (synWex m (synWa (.classEq (.cv m) (synCproj1 (.cv t)))
          (.classEq (.cv m) (synCop (.cv n) (.cv n)))))
      (synWbr (.cv t) (synC1st) (synCop (.cv n) (.cv n)))
      (synWex m (.classMem (synCop (.cv m) (synCop (.cv t) (.cv n)))
          (synCtxp (synCcnv (synC1st)) (synCin (synC1st) (synC2nd)))))
      p0010 p0015 p0033
  have p0035 :=
    @gN3bitri
      (synWbr (.cv t)
        (synCrn (synCtxp (synCcnv (synC1st)) (synCin (synC1st) (synC2nd)))) (.cv n))
      (.classMem (synCop (.cv t) (.cv n))
        (synCrn (synCtxp (synCcnv (synC1st)) (synCin (synC1st) (synC2nd)))))
      (synWex m (.classMem (synCop (.cv m) (synCop (.cv t) (.cv n)))
          (synCtxp (synCcnv (synC1st)) (synCin (synC1st) (synC2nd)))))
      (synWbr (.cv t) (synC1st) (synCop (.cv n) (.cv n))) p0006 p0007 p0034
  have p0036 :=
    @gAnbi1i
      (synWbr (.cv t)
        (synCrn (synCtxp (synCcnv (synC1st)) (synCin (synC1st) (synC2nd)))) (.cv n))
      (synWbr (.cv t) (synC1st) (synCop (.cv n) (.cv n)))
      (synWbr (.cv t) (synC2nd) (.cv m)) p0035
  have p0037 := @gOpex (.cv n) (.cv n) p0028 p0028
  have p0038 := @gVex m
  have p0039 := @gOp1st2nd (synCop (.cv n) (.cv n)) (.cv m) (.cv t) p0037 p0038
  have p0040 :=
    @gN3bitri
      (synWbr (.cv t) (synCtxp
          (synCrn (synCtxp (synCcnv (synC1st)) (synCin (synC1st) (synC2nd)))) (synC2nd))
        (synCop (.cv n) (.cv m)))
      (synWa (synWbr (.cv t)
          (synCrn (synCtxp (synCcnv (synC1st)) (synCin (synC1st) (synC2nd)))) (.cv n))
        (synWbr (.cv t) (synC2nd) (.cv m)))
      (synWa (synWbr (.cv t) (synC1st) (synCop (.cv n) (.cv n)))
        (synWbr (.cv t) (synC2nd) (.cv m)))
      (.classEq (.cv t) (synCop (synCop (.cv n) (.cv n)) (.cv m))) p0005 p0036 p0039
  have p0041 :=
    @gRexbii
      (synWbr (.cv t) (synCtxp
          (synCrn (synCtxp (synCcnv (synC1st)) (synCin (synC1st) (synC2nd)))) (synC2nd))
        (synCop (.cv n) (.cv m)))
      (.classEq (.cv t) (synCop (synCop (.cv n) (.cv n)) (.cv m))) t (synCaddcfn) p0040
  have p0042 :=
    @gElima t (synCop (.cv n) (.cv m))
      (synCtxp (synCrn (synCtxp (synCcnv (synC1st)) (synCin (synC1st) (synC2nd))))
        (synC2nd))
      (synCaddcfn) dv_cache_0007 dv_cache_0008 dv_cache_0009
  have p0043 :=
    (Nominal.biimpRefl (synWbr (synCop (.cv n) (.cv n)) (synCaddcfn) (.cv m)))
  have p0044 :=
    @gRisset t (synCop (synCop (.cv n) (.cv n)) (.cv m)) (synCaddcfn) dv_cache_0010
      dv_cache_0009
  have p0045 :=
    @gBitri (synWbr (synCop (.cv n) (.cv n)) (synCaddcfn) (.cv m))
      (.classMem (synCop (synCop (.cv n) (.cv n)) (.cv m)) (synCaddcfn))
      (synWrex t (synCaddcfn) (.classEq (.cv t) (synCop (synCop (.cv n) (.cv n)) (.cv m))))
      p0043 p0044
  have p0046 :=
    @gN3bitr4i
      (synWrex t (synCaddcfn) (synWbr (.cv t) (synCtxp
            (synCrn (synCtxp (synCcnv (synC1st)) (synCin (synC1st) (synC2nd))))
            (synC2nd)) (synCop (.cv n) (.cv m))))
      (synWrex t (synCaddcfn) (.classEq (.cv t) (synCop (synCop (.cv n) (.cv n)) (.cv m))))
      (.classMem (synCop (.cv n) (.cv m)) (synCima (synCtxp
            (synCrn (synCtxp (synCcnv (synC1st)) (synCin (synC1st) (synC2nd))))
            (synC2nd)) (synCaddcfn)))
      (synWbr (synCop (.cv n) (.cv n)) (synCaddcfn) (.cv m)) p0041 p0042 p0045
  have p0047 := @gBraddcfn (.cv n) (.cv n) (.cv m) p0028 p0028
  have p0048 := @gEqcom (synCplc (.cv n) (.cv n)) (.cv m)
  have p0049 :=
    @gN3bitri
      (.classMem (synCop (.cv n) (.cv m)) (synCima (synCtxp
            (synCrn (synCtxp (synCcnv (synC1st)) (synCin (synC1st) (synC2nd))))
            (synC2nd)) (synCaddcfn)))
      (synWbr (synCop (.cv n) (.cv n)) (synCaddcfn) (.cv m))
      (.classEq (synCplc (.cv n) (.cv n)) (.cv m))
      (.classEq (.cv m) (synCplc (.cv n) (.cv n))) p0046 p0047 p0048
  have p0050 :=
    @gN3bitri
      (.classMem (synCop (.cv m) (synCop (.cv n) (.cv b))) (synCins3 (synCcnv (synCima
              (synCtxp
                (synCrn (synCtxp (synCcnv (synC1st)) (synCin (synC1st) (synC2nd))))
                (synC2nd)) (synCaddcfn)))))
      (.classMem (synCop (.cv m) (.cv n)) (synCcnv (synCima (synCtxp
              (synCrn (synCtxp (synCcnv (synC1st)) (synCin (synC1st) (synC2nd))))
              (synC2nd)) (synCaddcfn))))
      (.classMem (synCop (.cv n) (.cv m)) (synCima (synCtxp
            (synCrn (synCtxp (synCcnv (synC1st)) (synCin (synC1st) (synC2nd))))
            (synC2nd)) (synCaddcfn)))
      (.classEq (.cv m) (synCplc (.cv n) (.cv n))) p0003 p0004 p0049
  have p0051 :=
    @gElima t (synCop (.cv m) (synCop (.cv n) (.cv b)))
      (synCtxp (synCcom (synC1st) (synC1st))
        (synCtxp (synCcom (synC2nd) (synC1st)) (synC2nd)))
      (synCaddcfn) dv_cache_0011 dv_cache_0012 dv_cache_0009
  have p0052 :=
    @gTrtxp (.cv t) (.cv m) (synCop (.cv n) (.cv b)) (synCcom (synC1st) (synC1st))
      (synCtxp (synCcom (synC2nd) (synC1st)) (synC2nd))
  have p0053 :=
    @gTrtxp (.cv t) (.cv n) (.cv b) (synCcom (synC2nd) (synC1st)) (synC2nd)
  have p0054 :=
    @gAnbi2i
      (synWbr (.cv t) (synCtxp (synCcom (synC2nd) (synC1st)) (synC2nd))
        (synCop (.cv n) (.cv b)))
      (synWa (synWbr (.cv t) (synCcom (synC2nd) (synC1st)) (.cv n))
        (synWbr (.cv t) (synC2nd) (.cv b)))
      (synWbr (.cv t) (synCcom (synC1st) (synC1st)) (.cv m)) p0053
  have p0055 :=
    @gAnass (synWbr (.cv t) (synCcom (synC1st) (synC1st)) (.cv m))
      (synWbr (.cv t) (synCcom (synC2nd) (synC1st)) (.cv n))
      (synWbr (.cv t) (synC2nd) (.cv b))
  have p0056 := @gOp1st2nd (.cv m) (.cv n) (synCproj1 (.cv t)) p0038 p0028
  have p0057 :=
    @gBrco n (.cv t) (.cv m) (synC1st) (synC1st) dv_cache_0013 dv_cache_0014
      dv_cache_0015 dv_cache_0015
  have p0058 :=
    @gBreq1i (.cv t) (synCop (synCproj1 (.cv t)) (synCproj2 (.cv t))) (.cv n)
      (synC1st) p0011
  have p0059 := @gOpbr1st (synCproj1 (.cv t)) (synCproj2 (.cv t)) (.cv n) p0009 p0013
  have p0060 := @gEqcom (synCproj1 (.cv t)) (.cv n)
  have p0061 :=
    @gN3bitri (synWbr (.cv t) (synC1st) (.cv n))
      (synWbr (synCop (synCproj1 (.cv t)) (synCproj2 (.cv t))) (synC1st) (.cv n))
      (.classEq (synCproj1 (.cv t)) (.cv n)) (.classEq (.cv n) (synCproj1 (.cv t)))
      p0058 p0059 p0060
  have p0062 :=
    @gAnbi1i (synWbr (.cv t) (synC1st) (.cv n)) (.classEq (.cv n) (synCproj1 (.cv t)))
      (synWbr (.cv n) (synC1st) (.cv m)) p0061
  have p0063 :=
    @gExbii
      (synWa (synWbr (.cv t) (synC1st) (.cv n)) (synWbr (.cv n) (synC1st) (.cv m)))
      (synWa (.classEq (.cv n) (synCproj1 (.cv t))) (synWbr (.cv n) (synC1st) (.cv m)))
      n p0062
  have p0064 := @gBreq1 (.cv n) (synCproj1 (.cv t)) (.cv m) (synC1st)
  have p0065 :=
    @gCeqsexv (synWbr (.cv n) (synC1st) (.cv m))
      (synWbr (synCproj1 (.cv t)) (synC1st) (.cv m)) n (synCproj1 (.cv t))
      dv_cache_0016 dv_cache_0017 p0009 p0064
  have p0066 :=
    @gN3bitri (synWbr (.cv t) (synCcom (synC1st) (synC1st)) (.cv m))
      (synWex n (synWa (synWbr (.cv t) (synC1st) (.cv n))
          (synWbr (.cv n) (synC1st) (.cv m))))
      (synWex n (synWa (.classEq (.cv n) (synCproj1 (.cv t)))
          (synWbr (.cv n) (synC1st) (.cv m))))
      (synWbr (synCproj1 (.cv t)) (synC1st) (.cv m)) p0057 p0063 p0065
  have p0067 :=
    @gBrco m (.cv t) (.cv n) (synC2nd) (synC1st) dv_cache_0018 dv_cache_0019
      dv_cache_0020 dv_cache_0021
  have p0068 :=
    @gAnbi1i (synWbr (.cv t) (synC1st) (.cv m)) (.classEq (.cv m) (synCproj1 (.cv t)))
      (synWbr (.cv m) (synC2nd) (.cv n)) p0022
  have p0069 :=
    @gExbii
      (synWa (synWbr (.cv t) (synC1st) (.cv m)) (synWbr (.cv m) (synC2nd) (.cv n)))
      (synWa (.classEq (.cv m) (synCproj1 (.cv t))) (synWbr (.cv m) (synC2nd) (.cv n)))
      m p0068
  have p0070 := @gBreq1 (.cv m) (synCproj1 (.cv t)) (.cv n) (synC2nd)
  have p0071 :=
    @gCeqsexv (synWbr (.cv m) (synC2nd) (.cv n))
      (synWbr (synCproj1 (.cv t)) (synC2nd) (.cv n)) m (synCproj1 (.cv t))
      dv_cache_0005 dv_cache_0022 p0009 p0070
  have p0072 :=
    @gN3bitri (synWbr (.cv t) (synCcom (synC2nd) (synC1st)) (.cv n))
      (synWex m (synWa (synWbr (.cv t) (synC1st) (.cv m))
          (synWbr (.cv m) (synC2nd) (.cv n))))
      (synWex m (synWa (.classEq (.cv m) (synCproj1 (.cv t)))
          (synWbr (.cv m) (synC2nd) (.cv n))))
      (synWbr (synCproj1 (.cv t)) (synC2nd) (.cv n)) p0067 p0069 p0071
  have p0073 :=
    @gAnbi12i (synWbr (.cv t) (synCcom (synC1st) (synC1st)) (.cv m))
      (synWbr (synCproj1 (.cv t)) (synC1st) (.cv m))
      (synWbr (.cv t) (synCcom (synC2nd) (synC1st)) (.cv n))
      (synWbr (synCproj1 (.cv t)) (synC2nd) (.cv n)) p0066 p0072
  have p0074 :=
    @gBreq1i (.cv t) (synCop (synCproj1 (.cv t)) (synCproj2 (.cv t)))
      (synCop (.cv m) (.cv n)) (synC1st) p0011
  have p0075 :=
    @gOpbr1st (synCproj1 (.cv t)) (synCproj2 (.cv t)) (synCop (.cv m) (.cv n)) p0009
      p0013
  have p0076 :=
    @gBitri (synWbr (.cv t) (synC1st) (synCop (.cv m) (.cv n)))
      (synWbr (synCop (synCproj1 (.cv t)) (synCproj2 (.cv t))) (synC1st)
        (synCop (.cv m) (.cv n)))
      (.classEq (synCproj1 (.cv t)) (synCop (.cv m) (.cv n))) p0074 p0075
  have p0077 :=
    @gN3bitr4i
      (synWa (synWbr (synCproj1 (.cv t)) (synC1st) (.cv m))
        (synWbr (synCproj1 (.cv t)) (synC2nd) (.cv n)))
      (.classEq (synCproj1 (.cv t)) (synCop (.cv m) (.cv n)))
      (synWa (synWbr (.cv t) (synCcom (synC1st) (synC1st)) (.cv m))
        (synWbr (.cv t) (synCcom (synC2nd) (synC1st)) (.cv n)))
      (synWbr (.cv t) (synC1st) (synCop (.cv m) (.cv n))) p0056 p0073 p0076
  have p0078 :=
    @gAnbi1i
      (synWa (synWbr (.cv t) (synCcom (synC1st) (synC1st)) (.cv m))
        (synWbr (.cv t) (synCcom (synC2nd) (synC1st)) (.cv n)))
      (synWbr (.cv t) (synC1st) (synCop (.cv m) (.cv n)))
      (synWbr (.cv t) (synC2nd) (.cv b)) p0077
  have p0079 :=
    @gN3bitr2i
      (synWa (synWbr (.cv t) (synCcom (synC1st) (synC1st)) (.cv m))
        (synWbr (.cv t) (synCtxp (synCcom (synC2nd) (synC1st)) (synC2nd))
          (synCop (.cv n) (.cv b))))
      (synWa (synWbr (.cv t) (synCcom (synC1st) (synC1st)) (.cv m))
        (synWa (synWbr (.cv t) (synCcom (synC2nd) (synC1st)) (.cv n))
          (synWbr (.cv t) (synC2nd) (.cv b))))
      (synWa (synWa (synWbr (.cv t) (synCcom (synC1st) (synC1st)) (.cv m))
          (synWbr (.cv t) (synCcom (synC2nd) (synC1st)) (.cv n)))
        (synWbr (.cv t) (synC2nd) (.cv b)))
      (synWa (synWbr (.cv t) (synC1st) (synCop (.cv m) (.cv n)))
        (synWbr (.cv t) (synC2nd) (.cv b)))
      p0054 p0055 p0078
  have p0080 := @gOpex (.cv m) (.cv n) p0038 p0028
  have p0081 := @gOp1st2nd (synCop (.cv m) (.cv n)) (.cv b) (.cv t) p0080 p0002
  have p0082 :=
    @gN3bitri
      (synWbr (.cv t) (synCtxp (synCcom (synC1st) (synC1st))
          (synCtxp (synCcom (synC2nd) (synC1st)) (synC2nd)))
        (synCop (.cv m) (synCop (.cv n) (.cv b))))
      (synWa (synWbr (.cv t) (synCcom (synC1st) (synC1st)) (.cv m))
        (synWbr (.cv t) (synCtxp (synCcom (synC2nd) (synC1st)) (synC2nd))
          (synCop (.cv n) (.cv b))))
      (synWa (synWbr (.cv t) (synC1st) (synCop (.cv m) (.cv n)))
        (synWbr (.cv t) (synC2nd) (.cv b)))
      (.classEq (.cv t) (synCop (synCop (.cv m) (.cv n)) (.cv b))) p0052 p0079 p0081
  have p0083 :=
    @gRexbii
      (synWbr (.cv t) (synCtxp (synCcom (synC1st) (synC1st))
          (synCtxp (synCcom (synC2nd) (synC1st)) (synC2nd)))
        (synCop (.cv m) (synCop (.cv n) (.cv b))))
      (.classEq (.cv t) (synCop (synCop (.cv m) (.cv n)) (.cv b))) t (synCaddcfn) p0082
  have p0084 :=
    @gBitri
      (.classMem (synCop (.cv m) (synCop (.cv n) (.cv b))) (synCima
          (synCtxp (synCcom (synC1st) (synC1st))
            (synCtxp (synCcom (synC2nd) (synC1st)) (synC2nd))) (synCaddcfn)))
      (synWrex t (synCaddcfn) (synWbr (.cv t) (synCtxp (synCcom (synC1st) (synC1st))
            (synCtxp (synCcom (synC2nd) (synC1st)) (synC2nd)))
          (synCop (.cv m) (synCop (.cv n) (.cv b)))))
      (synWrex t (synCaddcfn) (.classEq (.cv t) (synCop (synCop (.cv m) (.cv n)) (.cv b))))
      p0051 p0083
  have p0085 :=
    (Nominal.biimpRefl (synWbr (synCop (.cv m) (.cv n)) (synCaddcfn) (.cv b)))
  have p0086 :=
    @gRisset t (synCop (synCop (.cv m) (.cv n)) (.cv b)) (synCaddcfn) dv_cache_0023
      dv_cache_0009
  have p0087 :=
    @gBitr2i (synWbr (synCop (.cv m) (.cv n)) (synCaddcfn) (.cv b))
      (.classMem (synCop (synCop (.cv m) (.cv n)) (.cv b)) (synCaddcfn))
      (synWrex t (synCaddcfn) (.classEq (.cv t) (synCop (synCop (.cv m) (.cv n)) (.cv b))))
      p0085 p0086
  have p0088 := @gBraddcfn (.cv m) (.cv n) (.cv b) p0038 p0028
  have p0089 := @gEqcom (synCplc (.cv m) (.cv n)) (.cv b)
  have p0090 :=
    @gBitri (synWbr (synCop (.cv m) (.cv n)) (synCaddcfn) (.cv b))
      (.classEq (synCplc (.cv m) (.cv n)) (.cv b))
      (.classEq (.cv b) (synCplc (.cv m) (.cv n))) p0088 p0089
  have p0091 :=
    @gN3bitri
      (.classMem (synCop (.cv m) (synCop (.cv n) (.cv b))) (synCima
          (synCtxp (synCcom (synC1st) (synC1st))
            (synCtxp (synCcom (synC2nd) (synC1st)) (synC2nd))) (synCaddcfn)))
      (synWrex t (synCaddcfn) (.classEq (.cv t) (synCop (synCop (.cv m) (.cv n)) (.cv b))))
      (synWbr (synCop (.cv m) (.cv n)) (synCaddcfn) (.cv b))
      (.classEq (.cv b) (synCplc (.cv m) (.cv n))) p0084 p0087 p0090
  have p0092 :=
    @gAnbi12i
      (.classMem (synCop (.cv m) (synCop (.cv n) (.cv b))) (synCins3 (synCcnv (synCima
              (synCtxp
                (synCrn (synCtxp (synCcnv (synC1st)) (synCin (synC1st) (synC2nd))))
                (synC2nd)) (synCaddcfn)))))
      (.classEq (.cv m) (synCplc (.cv n) (.cv n)))
      (.classMem (synCop (.cv m) (synCop (.cv n) (.cv b))) (synCima
          (synCtxp (synCcom (synC1st) (synC1st))
            (synCtxp (synCcom (synC2nd) (synC1st)) (synC2nd))) (synCaddcfn)))
      (.classEq (.cv b) (synCplc (.cv m) (.cv n))) p0050 p0091
  have p0093 :=
    @gBitri
      (.classMem (synCop (.cv m) (synCop (.cv n) (.cv b))) (synCin (synCins3 (synCcnv
              (synCima (synCtxp (synCrn
                    (synCtxp (synCcnv (synC1st)) (synCin (synC1st) (synC2nd))))
                  (synC2nd)) (synCaddcfn)))) (synCima
            (synCtxp (synCcom (synC1st) (synC1st))
              (synCtxp (synCcom (synC2nd) (synC1st)) (synC2nd))) (synCaddcfn))))
      (synWa (.classMem (synCop (.cv m) (synCop (.cv n) (.cv b))) (synCins3 (synCcnv
              (synCima (synCtxp (synCrn
                    (synCtxp (synCcnv (synC1st)) (synCin (synC1st) (synC2nd))))
                  (synC2nd)) (synCaddcfn)))))
        (.classMem (synCop (.cv m) (synCop (.cv n) (.cv b))) (synCima
            (synCtxp (synCcom (synC1st) (synC1st))
              (synCtxp (synCcom (synC2nd) (synC1st)) (synC2nd))) (synCaddcfn))))
      (synWa (.classEq (.cv m) (synCplc (.cv n) (.cv n)))
        (.classEq (.cv b) (synCplc (.cv m) (.cv n))))
      p0001 p0092
  have p0094 :=
    @gExbii
      (.classMem (synCop (.cv m) (synCop (.cv n) (.cv b))) (synCin (synCins3 (synCcnv
              (synCima (synCtxp (synCrn
                    (synCtxp (synCcnv (synC1st)) (synCin (synC1st) (synC2nd))))
                  (synC2nd)) (synCaddcfn)))) (synCima
            (synCtxp (synCcom (synC1st) (synC1st))
              (synCtxp (synCcom (synC2nd) (synC1st)) (synC2nd))) (synCaddcfn))))
      (synWa (.classEq (.cv m) (synCplc (.cv n) (.cv n)))
        (.classEq (.cv b) (synCplc (.cv m) (.cv n))))
      m p0093
  have p0095 := @gAddcex (.cv n) (.cv n) p0028 p0028
  have p0096 := @gAddceq1 (.cv m) (synCplc (.cv n) (.cv n)) (.cv n)
  have p0097 :=
    @gEqeq2d (.classEq (.cv m) (synCplc (.cv n) (.cv n))) (synCplc (.cv m) (.cv n))
      (synCplc (synCplc (.cv n) (.cv n)) (.cv n)) (.cv b) p0096
  have p0098 :=
    @gCeqsexv (.classEq (.cv b) (synCplc (.cv m) (.cv n)))
      (.classEq (.cv b) (synCplc (synCplc (.cv n) (.cv n)) (.cv n))) m
      (synCplc (.cv n) (.cv n)) dv_cache_0024 dv_cache_0025 p0095 p0097
  have p0099 :=
    @gN3bitri
      (.classMem (synCop (.cv n) (.cv b)) (synCrn (synCin (synCins3 (synCcnv (synCima
                  (synCtxp (synCrn
                      (synCtxp (synCcnv (synC1st)) (synCin (synC1st) (synC2nd))))
                    (synC2nd)) (synCaddcfn)))) (synCima
              (synCtxp (synCcom (synC1st) (synC1st))
                (synCtxp (synCcom (synC2nd) (synC1st)) (synC2nd))) (synCaddcfn)))))
      (synWex m (.classMem (synCop (.cv m) (synCop (.cv n) (.cv b))) (synCin (synCins3
              (synCcnv (synCima (synCtxp (synCrn
                      (synCtxp (synCcnv (synC1st)) (synCin (synC1st) (synC2nd))))
                    (synC2nd)) (synCaddcfn)))) (synCima
              (synCtxp (synCcom (synC1st) (synC1st))
                (synCtxp (synCcom (synC2nd) (synC1st)) (synC2nd))) (synCaddcfn)))))
      (synWex m (synWa (.classEq (.cv m) (synCplc (.cv n) (.cv n)))
          (.classEq (.cv b) (synCplc (.cv m) (.cv n)))))
      (.classEq (.cv b) (synCplc (synCplc (.cv n) (.cv n)) (.cv n))) p0000 p0094 p0098
  exact p0099


end NFChoice.DirectNominalPrf.WPPReplay

end

/-! Certificates from `NominalWPPReplayChunk013Compact001Part063`. -/


section

namespace NFChoice.DirectNominalPrf.WPPReplay

open scoped Fol
open NFChoice.Foundation
open NFChoice.SemanticCore
open NFChoice.ReplaySupport
open NFChoice.Compiler.CompactSourceSyntax

/-- Checked nominal proof certificate identified upstream as `g_nncdiv3lem2`. -/
@[expose]
noncomputable def gNncdiv3lem2 (n : Var) (a : Var) (dv_a_n : a ≠ n) :
    Nominal.NPrf
      (.classMem (.cab a (synWrex n (synCnnc)
            (synW3o (.classEq (.cv a) (synCplc (synCplc (.cv n) (.cv n)) (.cv n)))
              (.classEq (.cv a)
                (synCplc (synCplc (synCplc (.cv n) (.cv n)) (.cv n)) (synC1c)))
              (.classEq (.cv a)
                (synCplc (synCplc (synCplc (.cv n) (.cv n)) (.cv n)) (synC2c))))))
        (synCvv)) :=
  by
  let proofSupport : Finset Var := ({ n } : Finset Var) ∪ ({ a } : Finset Var)
  let b : Var := freshVar proofSupport 0
  have fresh_b : b ∉ proofSupport :=
    by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_b_ne_n : b ≠ n := by
    intro h
    exact fresh_b (Finset.mem_union_left _ (Finset.mem_singleton.mpr h))
  have fresh_n_ne_b : n ≠ b := Ne.symm fresh_b_ne_n
  have fresh_b_ne_a : b ≠ a := by
    intro h
    exact fresh_b (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))
  have dv_cache_0001 : n ∉ ((Class.cv a)).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : n ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          (Ne.symm dv_a_n), not_false_eq_true])
  have dv_cache_0002 :
    n ∉
      ((synCun (synCun (synCrn (synCin (synCins3 (synCcnv (synCima (synCtxp (synCrn
                          (synCtxp (synCcnv (synC1st)) (synCin (synC1st) (synC2nd))))
                        (synC2nd)) (synCaddcfn)))) (synCima
                  (synCtxp (synCcom (synC1st) (synC1st))
                    (synCtxp (synCcom (synC2nd) (synC1st)) (synC2nd))) (synCaddcfn))))
            (synCrn (synCtxp (synCcnv (synCrn (synCin (synCins3 (synCcnv (synCima
                            (synCtxp (synCrn (synCtxp (synCcnv (synC1st))
                                  (synCin (synC1st) (synC2nd)))) (synC2nd)) (synCaddcfn))))
                      (synCima (synCtxp (synCcom (synC1st) (synC1st))
                          (synCtxp (synCcom (synC2nd) (synC1st)) (synC2nd)))
                        (synCaddcfn))))) (synCrn (synCtxp (synCin (synC1st)
                      (synCxp (synCima (synCcnv (synC2nd)) (synCsn (synC1c))) (synCvv)))
                    (synCaddcfn)))))) (synCrn (synCtxp (synCcnv (synCrn (synCin (synCins3
                      (synCcnv (synCima (synCtxp (synCrn (synCtxp (synCcnv (synC1st))
                                (synCin (synC1st) (synC2nd)))) (synC2nd)) (synCaddcfn))))
                    (synCima (synCtxp (synCcom (synC1st) (synC1st))
                        (synCtxp (synCcom (synC2nd) (synC1st)) (synC2nd)))
                      (synCaddcfn))))) (synCrn (synCtxp (synCin (synC1st)
                    (synCxp (synCima (synCcnv (synC2nd)) (synCsn (synC2c))) (synCvv)))
                  (synCaddcfn))))))).fv :=
    by
    clear dv_cache_0001
    exact
      (by
        have compact_fv_not_mem_empty : n ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cun,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_crn,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins3,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cima,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ctxp,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1st,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c2nd,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_caddcfn,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccom,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxp,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c2c, Finset.mem_union,
          compact_fv_not_mem_empty, or_false, not_false_eq_true])
  have dv_cache_0003 : n ∉ ((synCnnc)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact
      (by
        have compact_fv_not_mem_empty : n ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc,
          compact_fv_not_mem_empty, not_false_eq_true])
  have dv_cache_0004 : b ∉ ((synCop (.cv n) (.cv a))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact
      (by
        have compact_fv_not_mem_empty : b ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cop,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, fresh_b_ne_n, fresh_b_ne_a, or_false, not_false_eq_true])
  have dv_cache_0005 :
    b ∉
      ((synCtxp (synCcnv (synCrn (synCin (synCins3 (synCcnv (synCima (synCtxp (synCrn
                          (synCtxp (synCcnv (synC1st)) (synCin (synC1st) (synC2nd))))
                        (synC2nd)) (synCaddcfn)))) (synCima
                  (synCtxp (synCcom (synC1st) (synC1st))
                    (synCtxp (synCcom (synC2nd) (synC1st)) (synC2nd))) (synCaddcfn)))))
          (synCrn (synCtxp (synCin (synC1st)
                (synCxp (synCima (synCcnv (synC2nd)) (synCsn (synC1c))) (synCvv)))
              (synCaddcfn))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact
      (by
        have compact_fv_not_mem_empty : b ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ctxp,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_crn,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins3,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cima,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1st,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c2nd,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_caddcfn,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccom,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxp,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv, Finset.mem_union,
          compact_fv_not_mem_empty, or_false, not_false_eq_true])
  have dv_cache_0006 : n ∉ ((synCop (.cv b) (.cv a))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact
      (by
        have compact_fv_not_mem_empty : n ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cop,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, fresh_n_ne_b, (Ne.symm dv_a_n), or_false,
          not_false_eq_true])
  have dv_cache_0007 :
    n ∉
      ((synCtxp (synCin (synC1st)
            (synCxp (synCima (synCcnv (synC2nd)) (synCsn (synC1c))) (synCvv)))
          (synCaddcfn))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006
    exact
      (by
        have compact_fv_not_mem_empty : n ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ctxp,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1st,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxp,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cima,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c2nd,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_caddcfn, Finset.mem_union,
          compact_fv_not_mem_empty, or_false, not_false_eq_true])
  have dv_cache_0008 : n ∉ ((synCop (.cv b) (synC1c))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007
    exact
      (by
        have compact_fv_not_mem_empty : n ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cop,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c, Finset.mem_union,
          Finset.mem_singleton, fresh_n_ne_b, compact_fv_not_mem_empty, or_false,
          not_false_eq_true])
  have dv_cache_0009 :
    n ∉ ((synWbr (synCop (.cv b) (synC1c)) (synCaddcfn) (.cv a))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008
    exact
      (by
        have compact_fv_not_mem_empty : n ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cop,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_caddcfn, Finset.mem_union,
          Finset.mem_singleton, fresh_n_ne_b, (Ne.symm dv_a_n), compact_fv_not_mem_empty,
          or_false, not_false_eq_true])
  have dv_cache_0010 : b ∉ ((synCplc (synCplc (.cv n) (.cv n)) (.cv n))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009
    exact
      (by
        have compact_fv_not_mem_empty : b ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cplc,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, fresh_b_ne_n, or_false, not_false_eq_true])
  have dv_cache_0011 :
    b ∉
      ((Wff.classEq (.cv a)
          (synCplc (synCplc (synCplc (.cv n) (.cv n)) (.cv n)) (synC1c)))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010
    exact
      (by
        have compact_fv_not_mem_empty : b ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cplc,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c, Finset.mem_union,
          Finset.mem_singleton, fresh_b_ne_a, fresh_b_ne_n, compact_fv_not_mem_empty,
          or_false, not_false_eq_true])
  have dv_cache_0012 :
    b ∉
      ((synCtxp (synCcnv (synCrn (synCin (synCins3 (synCcnv (synCima (synCtxp (synCrn
                          (synCtxp (synCcnv (synC1st)) (synCin (synC1st) (synC2nd))))
                        (synC2nd)) (synCaddcfn)))) (synCima
                  (synCtxp (synCcom (synC1st) (synC1st))
                    (synCtxp (synCcom (synC2nd) (synC1st)) (synC2nd))) (synCaddcfn)))))
          (synCrn (synCtxp (synCin (synC1st)
                (synCxp (synCima (synCcnv (synC2nd)) (synCsn (synC2c))) (synCvv)))
              (synCaddcfn))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
    exact
      (by
        have compact_fv_not_mem_empty : b ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ctxp,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_crn,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins3,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cima,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1st,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c2nd,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_caddcfn,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccom,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxp,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c2c,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv, Finset.mem_union,
          compact_fv_not_mem_empty, or_false, not_false_eq_true])
  have dv_cache_0013 :
    n ∉
      ((synCtxp (synCin (synC1st)
            (synCxp (synCima (synCcnv (synC2nd)) (synCsn (synC2c))) (synCvv)))
          (synCaddcfn))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012
    exact
      (by
        have compact_fv_not_mem_empty : n ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ctxp,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1st,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxp,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cima,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c2nd,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c2c,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_caddcfn, Finset.mem_union,
          compact_fv_not_mem_empty, or_false, not_false_eq_true])
  have dv_cache_0014 : n ∉ ((synCop (.cv b) (synC2c))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013
    exact
      (by
        have compact_fv_not_mem_empty : n ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cop,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c2c, Finset.mem_union,
          Finset.mem_singleton, fresh_n_ne_b, compact_fv_not_mem_empty, or_false,
          not_false_eq_true])
  have dv_cache_0015 :
    n ∉ ((synWbr (synCop (.cv b) (synC2c)) (synCaddcfn) (.cv a))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014
    exact
      (by
        have compact_fv_not_mem_empty : n ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cop,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c2c,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_caddcfn, Finset.mem_union,
          Finset.mem_singleton, fresh_n_ne_b, (Ne.symm dv_a_n), compact_fv_not_mem_empty,
          or_false, not_false_eq_true])
  have dv_cache_0016 :
    b ∉
      ((Wff.classEq (.cv a)
          (synCplc (synCplc (synCplc (.cv n) (.cv n)) (.cv n)) (synC2c)))).fv :=
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
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cplc,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c2c, Finset.mem_union,
          Finset.mem_singleton, fresh_b_ne_a, fresh_b_ne_n, compact_fv_not_mem_empty,
          or_false, not_false_eq_true])
  have dv_cache_0017 :
    a ∉
      ((synCima (synCun (synCun (synCrn (synCin (synCins3 (synCcnv (synCima (synCtxp
                          (synCrn (synCtxp (synCcnv (synC1st))
                              (synCin (synC1st) (synC2nd)))) (synC2nd)) (synCaddcfn))))
                  (synCima (synCtxp (synCcom (synC1st) (synC1st))
                      (synCtxp (synCcom (synC2nd) (synC1st)) (synC2nd))) (synCaddcfn))))
              (synCrn (synCtxp (synCcnv (synCrn (synCin (synCins3 (synCcnv (synCima
                              (synCtxp (synCrn (synCtxp (synCcnv (synC1st))
                                    (synCin (synC1st) (synC2nd)))) (synC2nd))
                              (synCaddcfn)))) (synCima
                          (synCtxp (synCcom (synC1st) (synC1st))
                            (synCtxp (synCcom (synC2nd) (synC1st)) (synC2nd)))
                          (synCaddcfn))))) (synCrn (synCtxp (synCin (synC1st)
                        (synCxp (synCima (synCcnv (synC2nd)) (synCsn (synC1c)))
                          (synCvv))) (synCaddcfn)))))) (synCrn (synCtxp (synCcnv (synCrn
                    (synCin (synCins3 (synCcnv (synCima (synCtxp (synCrn
                                (synCtxp (synCcnv (synC1st))
                                  (synCin (synC1st) (synC2nd)))) (synC2nd)) (synCaddcfn))))
                      (synCima (synCtxp (synCcom (synC1st) (synC1st))
                          (synCtxp (synCcom (synC2nd) (synC1st)) (synC2nd)))
                        (synCaddcfn))))) (synCrn (synCtxp (synCin (synC1st)
                      (synCxp (synCima (synCcnv (synC2nd)) (synCsn (synC2c))) (synCvv)))
                    (synCaddcfn)))))) (synCnnc))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016
    exact
      (by
        have compact_fv_not_mem_empty : a ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cima,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cun,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_crn,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins3,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ctxp,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1st,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c2nd,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_caddcfn,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccom,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxp,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c2c,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc, Finset.mem_union,
          compact_fv_not_mem_empty, or_false, not_false_eq_true])
  have p0000 :=
    @gElima n (.cv a)
      (synCun (synCun (synCrn (synCin (synCins3 (synCcnv (synCima (synCtxp (synCrn
                        (synCtxp (synCcnv (synC1st)) (synCin (synC1st) (synC2nd))))
                      (synC2nd)) (synCaddcfn)))) (synCima
                (synCtxp (synCcom (synC1st) (synC1st))
                  (synCtxp (synCcom (synC2nd) (synC1st)) (synC2nd))) (synCaddcfn))))
          (synCrn (synCtxp (synCcnv (synCrn (synCin (synCins3 (synCcnv (synCima
                          (synCtxp (synCrn (synCtxp (synCcnv (synC1st))
                                (synCin (synC1st) (synC2nd)))) (synC2nd)) (synCaddcfn))))
                    (synCima (synCtxp (synCcom (synC1st) (synC1st))
                        (synCtxp (synCcom (synC2nd) (synC1st)) (synC2nd)))
                      (synCaddcfn))))) (synCrn (synCtxp (synCin (synC1st)
                    (synCxp (synCima (synCcnv (synC2nd)) (synCsn (synC1c))) (synCvv)))
                  (synCaddcfn)))))) (synCrn (synCtxp (synCcnv (synCrn (synCin (synCins3
                    (synCcnv (synCima (synCtxp (synCrn (synCtxp (synCcnv (synC1st))
                              (synCin (synC1st) (synC2nd)))) (synC2nd)) (synCaddcfn))))
                  (synCima (synCtxp (synCcom (synC1st) (synC1st))
                      (synCtxp (synCcom (synC2nd) (synC1st)) (synC2nd))) (synCaddcfn)))))
            (synCrn (synCtxp (synCin (synC1st)
                  (synCxp (synCima (synCcnv (synC2nd)) (synCsn (synC2c))) (synCvv)))
                (synCaddcfn))))))
      (synCnnc) dv_cache_0001 dv_cache_0002 dv_cache_0003
  have p0001 :=
    (Nominal.biimpRefl (synWbr (.cv n) (synCun (synCun (synCrn (synCin (synCins3 (synCcnv
                    (synCima (synCtxp (synCrn (synCtxp (synCcnv (synC1st))
                            (synCin (synC1st) (synC2nd)))) (synC2nd)) (synCaddcfn))))
                (synCima (synCtxp (synCcom (synC1st) (synC1st))
                    (synCtxp (synCcom (synC2nd) (synC1st)) (synC2nd))) (synCaddcfn))))
            (synCrn (synCtxp (synCcnv (synCrn (synCin (synCins3 (synCcnv (synCima
                            (synCtxp (synCrn (synCtxp (synCcnv (synC1st))
                                  (synCin (synC1st) (synC2nd)))) (synC2nd)) (synCaddcfn))))
                      (synCima (synCtxp (synCcom (synC1st) (synC1st))
                          (synCtxp (synCcom (synC2nd) (synC1st)) (synC2nd)))
                        (synCaddcfn))))) (synCrn (synCtxp (synCin (synC1st)
                      (synCxp (synCima (synCcnv (synC2nd)) (synCsn (synC1c))) (synCvv)))
                    (synCaddcfn)))))) (synCrn (synCtxp (synCcnv (synCrn (synCin (synCins3
                      (synCcnv (synCima (synCtxp (synCrn (synCtxp (synCcnv (synC1st))
                                (synCin (synC1st) (synC2nd)))) (synC2nd)) (synCaddcfn))))
                    (synCima (synCtxp (synCcom (synC1st) (synC1st))
                        (synCtxp (synCcom (synC2nd) (synC1st)) (synC2nd)))
                      (synCaddcfn))))) (synCrn (synCtxp (synCin (synC1st)
                    (synCxp (synCima (synCcnv (synC2nd)) (synCsn (synC2c))) (synCvv)))
                  (synCaddcfn)))))) (.cv a)))
  have p0002 :=
    @gElun (synCop (.cv n) (.cv a))
      (synCrn (synCin (synCins3 (synCcnv (synCima (synCtxp (synCrn
                    (synCtxp (synCcnv (synC1st)) (synCin (synC1st) (synC2nd))))
                  (synC2nd)) (synCaddcfn)))) (synCima
            (synCtxp (synCcom (synC1st) (synC1st))
              (synCtxp (synCcom (synC2nd) (synC1st)) (synC2nd))) (synCaddcfn))))
      (synCrn (synCtxp (synCcnv (synCrn (synCin (synCins3 (synCcnv (synCima (synCtxp
                        (synCrn (synCtxp (synCcnv (synC1st))
                            (synCin (synC1st) (synC2nd)))) (synC2nd)) (synCaddcfn))))
                (synCima (synCtxp (synCcom (synC1st) (synC1st))
                    (synCtxp (synCcom (synC2nd) (synC1st)) (synC2nd))) (synCaddcfn)))))
          (synCrn (synCtxp (synCin (synC1st)
                (synCxp (synCima (synCcnv (synC2nd)) (synCsn (synC1c))) (synCvv)))
              (synCaddcfn)))))
  have p0003 := @gNncdiv3lem1 n a
  have p0004 :=
    @gElrn2 b (synCop (.cv n) (.cv a))
      (synCtxp (synCcnv (synCrn (synCin (synCins3 (synCcnv (synCima (synCtxp (synCrn
                        (synCtxp (synCcnv (synC1st)) (synCin (synC1st) (synC2nd))))
                      (synC2nd)) (synCaddcfn)))) (synCima
                (synCtxp (synCcom (synC1st) (synC1st))
                  (synCtxp (synCcom (synC2nd) (synC1st)) (synC2nd))) (synCaddcfn)))))
        (synCrn (synCtxp (synCin (synC1st)
              (synCxp (synCima (synCcnv (synC2nd)) (synCsn (synC1c))) (synCvv)))
            (synCaddcfn))))
      dv_cache_0004 dv_cache_0005
  have p0005 :=
    @gOteltxp (.cv b) (.cv n) (.cv a)
      (synCcnv (synCrn (synCin (synCins3 (synCcnv (synCima (synCtxp (synCrn
                      (synCtxp (synCcnv (synC1st)) (synCin (synC1st) (synC2nd))))
                    (synC2nd)) (synCaddcfn)))) (synCima
              (synCtxp (synCcom (synC1st) (synC1st))
                (synCtxp (synCcom (synC2nd) (synC1st)) (synC2nd))) (synCaddcfn)))))
      (synCrn (synCtxp (synCin (synC1st)
            (synCxp (synCima (synCcnv (synC2nd)) (synCsn (synC1c))) (synCvv)))
          (synCaddcfn)))
  have p0006 :=
    @gOpelcnv (.cv b) (.cv n)
      (synCrn (synCin (synCins3 (synCcnv (synCima (synCtxp (synCrn
                    (synCtxp (synCcnv (synC1st)) (synCin (synC1st) (synC2nd))))
                  (synC2nd)) (synCaddcfn)))) (synCima
            (synCtxp (synCcom (synC1st) (synC1st))
              (synCtxp (synCcom (synC2nd) (synC1st)) (synC2nd))) (synCaddcfn))))
  have p0007 := @gNncdiv3lem1 n b
  have p0008 :=
    @gBitri
      (.classMem (synCop (.cv b) (.cv n)) (synCcnv (synCrn (synCin (synCins3 (synCcnv
                  (synCima (synCtxp (synCrn
                        (synCtxp (synCcnv (synC1st)) (synCin (synC1st) (synC2nd))))
                      (synC2nd)) (synCaddcfn)))) (synCima
                (synCtxp (synCcom (synC1st) (synC1st))
                  (synCtxp (synCcom (synC2nd) (synC1st)) (synC2nd))) (synCaddcfn))))))
      (.classMem (synCop (.cv n) (.cv b)) (synCrn (synCin (synCins3 (synCcnv (synCima
                  (synCtxp (synCrn
                      (synCtxp (synCcnv (synC1st)) (synCin (synC1st) (synC2nd))))
                    (synC2nd)) (synCaddcfn)))) (synCima
              (synCtxp (synCcom (synC1st) (synC1st))
                (synCtxp (synCcom (synC2nd) (synC1st)) (synC2nd))) (synCaddcfn)))))
      (.classEq (.cv b) (synCplc (synCplc (.cv n) (.cv n)) (.cv n))) p0006 p0007
  have p0009 :=
    @gElrn2 n (synCop (.cv b) (.cv a))
      (synCtxp (synCin (synC1st)
          (synCxp (synCima (synCcnv (synC2nd)) (synCsn (synC1c))) (synCvv)))
        (synCaddcfn))
      dv_cache_0006 dv_cache_0007
  have p0010 :=
    @gOteltxp (.cv n) (.cv b) (.cv a)
      (synCin (synC1st)
        (synCxp (synCima (synCcnv (synC2nd)) (synCsn (synC1c))) (synCvv)))
      (synCaddcfn)
  have p0011 :=
    @gElin (synCop (.cv n) (.cv b)) (synC1st)
      (synCxp (synCima (synCcnv (synC2nd)) (synCsn (synC1c))) (synCvv))
  have p0012 := (Nominal.biimpRefl (synWbr (.cv n) (synC1st) (.cv b)))
  have p0013 :=
    @gBicomi (synWbr (.cv n) (synC1st) (.cv b))
      (.classMem (synCop (.cv n) (.cv b)) (synC1st)) p0012
  have p0014 := @gVex b
  have p0015 :=
    @gOpelxp (.cv n) (.cv b) (synCima (synCcnv (synC2nd)) (synCsn (synC1c)))
      (synCvv)
  have p0016 :=
    @gMpbiran2
      (.classMem (synCop (.cv n) (.cv b))
        (synCxp (synCima (synCcnv (synC2nd)) (synCsn (synC1c))) (synCvv)))
      (.classMem (.cv n) (synCima (synCcnv (synC2nd)) (synCsn (synC1c))))
      (.classMem (.cv b) (synCvv)) p0014 p0015
  have p0017 := @gEliniseg (synC2nd) (synC1c) (.cv n)
  have p0018 :=
    @gBitri
      (.classMem (synCop (.cv n) (.cv b))
        (synCxp (synCima (synCcnv (synC2nd)) (synCsn (synC1c))) (synCvv)))
      (.classMem (.cv n) (synCima (synCcnv (synC2nd)) (synCsn (synC1c))))
      (synWbr (.cv n) (synC2nd) (synC1c)) p0016 p0017
  have p0019 :=
    @gAnbi12i (.classMem (synCop (.cv n) (.cv b)) (synC1st))
      (synWbr (.cv n) (synC1st) (.cv b))
      (.classMem (synCop (.cv n) (.cv b))
        (synCxp (synCima (synCcnv (synC2nd)) (synCsn (synC1c))) (synCvv)))
      (synWbr (.cv n) (synC2nd) (synC1c)) p0013 p0018
  have p0020 := @gN1cex
  have p0021 := @gOp1st2nd (.cv b) (synC1c) (.cv n) p0014 p0020
  have p0022 :=
    @gN3bitri
      (.classMem (synCop (.cv n) (.cv b)) (synCin (synC1st)
          (synCxp (synCima (synCcnv (synC2nd)) (synCsn (synC1c))) (synCvv))))
      (synWa (.classMem (synCop (.cv n) (.cv b)) (synC1st))
        (.classMem (synCop (.cv n) (.cv b))
          (synCxp (synCima (synCcnv (synC2nd)) (synCsn (synC1c))) (synCvv))))
      (synWa (synWbr (.cv n) (synC1st) (.cv b)) (synWbr (.cv n) (synC2nd) (synC1c)))
      (.classEq (.cv n) (synCop (.cv b) (synC1c))) p0011 p0019 p0021
  have p0023 := (Nominal.biimpRefl (synWbr (.cv n) (synCaddcfn) (.cv a)))
  have p0024 :=
    @gBicomi (synWbr (.cv n) (synCaddcfn) (.cv a))
      (.classMem (synCop (.cv n) (.cv a)) (synCaddcfn)) p0023
  have p0025 :=
    @gAnbi12i
      (.classMem (synCop (.cv n) (.cv b)) (synCin (synC1st)
          (synCxp (synCima (synCcnv (synC2nd)) (synCsn (synC1c))) (synCvv))))
      (.classEq (.cv n) (synCop (.cv b) (synC1c)))
      (.classMem (synCop (.cv n) (.cv a)) (synCaddcfn))
      (synWbr (.cv n) (synCaddcfn) (.cv a)) p0022 p0024
  have p0026 :=
    @gBitri
      (.classMem (synCop (.cv n) (synCop (.cv b) (.cv a))) (synCtxp (synCin (synC1st)
            (synCxp (synCima (synCcnv (synC2nd)) (synCsn (synC1c))) (synCvv)))
          (synCaddcfn)))
      (synWa (.classMem (synCop (.cv n) (.cv b)) (synCin (synC1st)
            (synCxp (synCima (synCcnv (synC2nd)) (synCsn (synC1c))) (synCvv))))
        (.classMem (synCop (.cv n) (.cv a)) (synCaddcfn)))
      (synWa (.classEq (.cv n) (synCop (.cv b) (synC1c)))
        (synWbr (.cv n) (synCaddcfn) (.cv a)))
      p0010 p0025
  have p0027 :=
    @gExbii
      (.classMem (synCop (.cv n) (synCop (.cv b) (.cv a))) (synCtxp (synCin (synC1st)
            (synCxp (synCima (synCcnv (synC2nd)) (synCsn (synC1c))) (synCvv)))
          (synCaddcfn)))
      (synWa (.classEq (.cv n) (synCop (.cv b) (synC1c)))
        (synWbr (.cv n) (synCaddcfn) (.cv a)))
      n p0026
  have p0028 :=
    @gBitri
      (.classMem (synCop (.cv b) (.cv a)) (synCrn (synCtxp (synCin (synC1st)
              (synCxp (synCima (synCcnv (synC2nd)) (synCsn (synC1c))) (synCvv)))
            (synCaddcfn))))
      (synWex n (.classMem (synCop (.cv n) (synCop (.cv b) (.cv a))) (synCtxp
            (synCin (synC1st)
              (synCxp (synCima (synCcnv (synC2nd)) (synCsn (synC1c))) (synCvv)))
            (synCaddcfn))))
      (synWex n (synWa (.classEq (.cv n) (synCop (.cv b) (synC1c)))
          (synWbr (.cv n) (synCaddcfn) (.cv a))))
      p0009 p0027
  have p0030 := @gOpex (.cv b) (synC1c) p0014 p0020
  have p0031 := @gBreq1 (.cv n) (synCop (.cv b) (synC1c)) (.cv a) (synCaddcfn)
  have p0032 :=
    @gCeqsexv (synWbr (.cv n) (synCaddcfn) (.cv a))
      (synWbr (synCop (.cv b) (synC1c)) (synCaddcfn) (.cv a)) n
      (synCop (.cv b) (synC1c)) dv_cache_0008 dv_cache_0009 p0030 p0031
  have p0034 := @gBraddcfn (.cv b) (synC1c) (.cv a) p0014 p0020
  have p0035 := @gEqcom (synCplc (.cv b) (synC1c)) (.cv a)
  have p0036 :=
    @gBitri (synWbr (synCop (.cv b) (synC1c)) (synCaddcfn) (.cv a))
      (.classEq (synCplc (.cv b) (synC1c)) (.cv a))
      (.classEq (.cv a) (synCplc (.cv b) (synC1c))) p0034 p0035
  have p0037 :=
    @gN3bitri
      (.classMem (synCop (.cv b) (.cv a)) (synCrn (synCtxp (synCin (synC1st)
              (synCxp (synCima (synCcnv (synC2nd)) (synCsn (synC1c))) (synCvv)))
            (synCaddcfn))))
      (synWex n (synWa (.classEq (.cv n) (synCop (.cv b) (synC1c)))
          (synWbr (.cv n) (synCaddcfn) (.cv a))))
      (synWbr (synCop (.cv b) (synC1c)) (synCaddcfn) (.cv a))
      (.classEq (.cv a) (synCplc (.cv b) (synC1c))) p0028 p0032 p0036
  have p0038 :=
    @gAnbi12i
      (.classMem (synCop (.cv b) (.cv n)) (synCcnv (synCrn (synCin (synCins3 (synCcnv
                  (synCima (synCtxp (synCrn
                        (synCtxp (synCcnv (synC1st)) (synCin (synC1st) (synC2nd))))
                      (synC2nd)) (synCaddcfn)))) (synCima
                (synCtxp (synCcom (synC1st) (synC1st))
                  (synCtxp (synCcom (synC2nd) (synC1st)) (synC2nd))) (synCaddcfn))))))
      (.classEq (.cv b) (synCplc (synCplc (.cv n) (.cv n)) (.cv n)))
      (.classMem (synCop (.cv b) (.cv a)) (synCrn (synCtxp (synCin (synC1st)
              (synCxp (synCima (synCcnv (synC2nd)) (synCsn (synC1c))) (synCvv)))
            (synCaddcfn))))
      (.classEq (.cv a) (synCplc (.cv b) (synC1c))) p0008 p0037
  have p0039 :=
    @gBitri
      (.classMem (synCop (.cv b) (synCop (.cv n) (.cv a))) (synCtxp (synCcnv (synCrn
              (synCin (synCins3 (synCcnv (synCima (synCtxp (synCrn
                          (synCtxp (synCcnv (synC1st)) (synCin (synC1st) (synC2nd))))
                        (synC2nd)) (synCaddcfn)))) (synCima
                  (synCtxp (synCcom (synC1st) (synC1st))
                    (synCtxp (synCcom (synC2nd) (synC1st)) (synC2nd))) (synCaddcfn)))))
          (synCrn (synCtxp (synCin (synC1st)
                (synCxp (synCima (synCcnv (synC2nd)) (synCsn (synC1c))) (synCvv)))
              (synCaddcfn)))))
      (synWa (.classMem (synCop (.cv b) (.cv n)) (synCcnv (synCrn (synCin (synCins3
                  (synCcnv (synCima (synCtxp (synCrn (synCtxp (synCcnv (synC1st))
                            (synCin (synC1st) (synC2nd)))) (synC2nd)) (synCaddcfn))))
                (synCima (synCtxp (synCcom (synC1st) (synC1st))
                    (synCtxp (synCcom (synC2nd) (synC1st)) (synC2nd))) (synCaddcfn))))))
        (.classMem (synCop (.cv b) (.cv a)) (synCrn (synCtxp (synCin (synC1st)
                (synCxp (synCima (synCcnv (synC2nd)) (synCsn (synC1c))) (synCvv)))
              (synCaddcfn)))))
      (synWa (.classEq (.cv b) (synCplc (synCplc (.cv n) (.cv n)) (.cv n)))
        (.classEq (.cv a) (synCplc (.cv b) (synC1c))))
      p0005 p0038
  have p0040 :=
    @gExbii
      (.classMem (synCop (.cv b) (synCop (.cv n) (.cv a))) (synCtxp (synCcnv (synCrn
              (synCin (synCins3 (synCcnv (synCima (synCtxp (synCrn
                          (synCtxp (synCcnv (synC1st)) (synCin (synC1st) (synC2nd))))
                        (synC2nd)) (synCaddcfn)))) (synCima
                  (synCtxp (synCcom (synC1st) (synC1st))
                    (synCtxp (synCcom (synC2nd) (synC1st)) (synC2nd))) (synCaddcfn)))))
          (synCrn (synCtxp (synCin (synC1st)
                (synCxp (synCima (synCcnv (synC2nd)) (synCsn (synC1c))) (synCvv)))
              (synCaddcfn)))))
      (synWa (.classEq (.cv b) (synCplc (synCplc (.cv n) (.cv n)) (.cv n)))
        (.classEq (.cv a) (synCplc (.cv b) (synC1c))))
      b p0039
  have p0041 := @gVex n
  have p0042 := @gAddcex (.cv n) (.cv n) p0041 p0041
  have p0043 := @gAddcex (synCplc (.cv n) (.cv n)) (.cv n) p0042 p0041
  have p0044 := @gAddceq1 (.cv b) (synCplc (synCplc (.cv n) (.cv n)) (.cv n)) (synC1c)
  have p0045 :=
    @gEqeq2d (.classEq (.cv b) (synCplc (synCplc (.cv n) (.cv n)) (.cv n)))
      (synCplc (.cv b) (synC1c))
      (synCplc (synCplc (synCplc (.cv n) (.cv n)) (.cv n)) (synC1c)) (.cv a) p0044
  have p0046 :=
    @gCeqsexv (.classEq (.cv a) (synCplc (.cv b) (synC1c)))
      (.classEq (.cv a) (synCplc (synCplc (synCplc (.cv n) (.cv n)) (.cv n)) (synC1c)))
      b (synCplc (synCplc (.cv n) (.cv n)) (.cv n)) dv_cache_0010 dv_cache_0011 p0043
      p0045
  have p0047 :=
    @gN3bitri
      (.classMem (synCop (.cv n) (.cv a)) (synCrn (synCtxp (synCcnv (synCrn (synCin
                  (synCins3 (synCcnv (synCima (synCtxp (synCrn
                            (synCtxp (synCcnv (synC1st)) (synCin (synC1st) (synC2nd))))
                          (synC2nd)) (synCaddcfn)))) (synCima
                    (synCtxp (synCcom (synC1st) (synC1st))
                      (synCtxp (synCcom (synC2nd) (synC1st)) (synC2nd))) (synCaddcfn)))))
            (synCrn (synCtxp (synCin (synC1st)
                  (synCxp (synCima (synCcnv (synC2nd)) (synCsn (synC1c))) (synCvv)))
                (synCaddcfn))))))
      (synWex b (.classMem (synCop (.cv b) (synCop (.cv n) (.cv a))) (synCtxp (synCcnv
              (synCrn (synCin (synCins3 (synCcnv (synCima (synCtxp (synCrn
                            (synCtxp (synCcnv (synC1st)) (synCin (synC1st) (synC2nd))))
                          (synC2nd)) (synCaddcfn)))) (synCima
                    (synCtxp (synCcom (synC1st) (synC1st))
                      (synCtxp (synCcom (synC2nd) (synC1st)) (synC2nd))) (synCaddcfn)))))
            (synCrn (synCtxp (synCin (synC1st)
                  (synCxp (synCima (synCcnv (synC2nd)) (synCsn (synC1c))) (synCvv)))
                (synCaddcfn))))))
      (synWex b (synWa (.classEq (.cv b) (synCplc (synCplc (.cv n) (.cv n)) (.cv n)))
          (.classEq (.cv a) (synCplc (.cv b) (synC1c)))))
      (.classEq (.cv a) (synCplc (synCplc (synCplc (.cv n) (.cv n)) (.cv n)) (synC1c)))
      p0004 p0040 p0046
  have p0048 :=
    @gOrbi12i
      (.classMem (synCop (.cv n) (.cv a)) (synCrn (synCin (synCins3 (synCcnv (synCima
                  (synCtxp (synCrn
                      (synCtxp (synCcnv (synC1st)) (synCin (synC1st) (synC2nd))))
                    (synC2nd)) (synCaddcfn)))) (synCima
              (synCtxp (synCcom (synC1st) (synC1st))
                (synCtxp (synCcom (synC2nd) (synC1st)) (synC2nd))) (synCaddcfn)))))
      (.classEq (.cv a) (synCplc (synCplc (.cv n) (.cv n)) (.cv n)))
      (.classMem (synCop (.cv n) (.cv a)) (synCrn (synCtxp (synCcnv (synCrn (synCin
                  (synCins3 (synCcnv (synCima (synCtxp (synCrn
                            (synCtxp (synCcnv (synC1st)) (synCin (synC1st) (synC2nd))))
                          (synC2nd)) (synCaddcfn)))) (synCima
                    (synCtxp (synCcom (synC1st) (synC1st))
                      (synCtxp (synCcom (synC2nd) (synC1st)) (synC2nd))) (synCaddcfn)))))
            (synCrn (synCtxp (synCin (synC1st)
                  (synCxp (synCima (synCcnv (synC2nd)) (synCsn (synC1c))) (synCvv)))
                (synCaddcfn))))))
      (.classEq (.cv a) (synCplc (synCplc (synCplc (.cv n) (.cv n)) (.cv n)) (synC1c)))
      p0003 p0047
  have p0049 :=
    @gBitri
      (.classMem (synCop (.cv n) (.cv a)) (synCun (synCrn (synCin (synCins3 (synCcnv
                  (synCima (synCtxp (synCrn
                        (synCtxp (synCcnv (synC1st)) (synCin (synC1st) (synC2nd))))
                      (synC2nd)) (synCaddcfn)))) (synCima
                (synCtxp (synCcom (synC1st) (synC1st))
                  (synCtxp (synCcom (synC2nd) (synC1st)) (synC2nd))) (synCaddcfn))))
          (synCrn (synCtxp (synCcnv (synCrn (synCin (synCins3 (synCcnv (synCima
                          (synCtxp (synCrn (synCtxp (synCcnv (synC1st))
                                (synCin (synC1st) (synC2nd)))) (synC2nd)) (synCaddcfn))))
                    (synCima (synCtxp (synCcom (synC1st) (synC1st))
                        (synCtxp (synCcom (synC2nd) (synC1st)) (synC2nd)))
                      (synCaddcfn))))) (synCrn (synCtxp (synCin (synC1st)
                    (synCxp (synCima (synCcnv (synC2nd)) (synCsn (synC1c))) (synCvv)))
                  (synCaddcfn)))))))
      (synWo (.classMem (synCop (.cv n) (.cv a)) (synCrn (synCin (synCins3 (synCcnv
                  (synCima (synCtxp (synCrn
                        (synCtxp (synCcnv (synC1st)) (synCin (synC1st) (synC2nd))))
                      (synC2nd)) (synCaddcfn)))) (synCima
                (synCtxp (synCcom (synC1st) (synC1st))
                  (synCtxp (synCcom (synC2nd) (synC1st)) (synC2nd))) (synCaddcfn)))))
        (.classMem (synCop (.cv n) (.cv a)) (synCrn (synCtxp (synCcnv (synCrn (synCin
                    (synCins3 (synCcnv (synCima (synCtxp (synCrn
                              (synCtxp (synCcnv (synC1st)) (synCin (synC1st) (synC2nd))))
                            (synC2nd)) (synCaddcfn)))) (synCima
                      (synCtxp (synCcom (synC1st) (synC1st))
                        (synCtxp (synCcom (synC2nd) (synC1st)) (synC2nd)))
                      (synCaddcfn))))) (synCrn (synCtxp (synCin (synC1st)
                    (synCxp (synCima (synCcnv (synC2nd)) (synCsn (synC1c))) (synCvv)))
                  (synCaddcfn)))))))
      (synWo (.classEq (.cv a) (synCplc (synCplc (.cv n) (.cv n)) (.cv n))) (.classEq (.cv a)
          (synCplc (synCplc (synCplc (.cv n) (.cv n)) (.cv n)) (synC1c))))
      p0002 p0048
  have p0050 :=
    @gElrn2 b (synCop (.cv n) (.cv a))
      (synCtxp (synCcnv (synCrn (synCin (synCins3 (synCcnv (synCima (synCtxp (synCrn
                        (synCtxp (synCcnv (synC1st)) (synCin (synC1st) (synC2nd))))
                      (synC2nd)) (synCaddcfn)))) (synCima
                (synCtxp (synCcom (synC1st) (synC1st))
                  (synCtxp (synCcom (synC2nd) (synC1st)) (synC2nd))) (synCaddcfn)))))
        (synCrn (synCtxp (synCin (synC1st)
              (synCxp (synCima (synCcnv (synC2nd)) (synCsn (synC2c))) (synCvv)))
            (synCaddcfn))))
      dv_cache_0004 dv_cache_0012
  have p0051 :=
    @gOteltxp (.cv b) (.cv n) (.cv a)
      (synCcnv (synCrn (synCin (synCins3 (synCcnv (synCima (synCtxp (synCrn
                      (synCtxp (synCcnv (synC1st)) (synCin (synC1st) (synC2nd))))
                    (synC2nd)) (synCaddcfn)))) (synCima
              (synCtxp (synCcom (synC1st) (synC1st))
                (synCtxp (synCcom (synC2nd) (synC1st)) (synC2nd))) (synCaddcfn)))))
      (synCrn (synCtxp (synCin (synC1st)
            (synCxp (synCima (synCcnv (synC2nd)) (synCsn (synC2c))) (synCvv)))
          (synCaddcfn)))
  have p0052 :=
    @gElrn2 n (synCop (.cv b) (.cv a))
      (synCtxp (synCin (synC1st)
          (synCxp (synCima (synCcnv (synC2nd)) (synCsn (synC2c))) (synCvv)))
        (synCaddcfn))
      dv_cache_0006 dv_cache_0013
  have p0053 :=
    @gOteltxp (.cv n) (.cv b) (.cv a)
      (synCin (synC1st)
        (synCxp (synCima (synCcnv (synC2nd)) (synCsn (synC2c))) (synCvv)))
      (synCaddcfn)
  have p0054 :=
    @gElin (synCop (.cv n) (.cv b)) (synC1st)
      (synCxp (synCima (synCcnv (synC2nd)) (synCsn (synC2c))) (synCvv))
  have p0055 :=
    @gOpelxp (.cv n) (.cv b) (synCima (synCcnv (synC2nd)) (synCsn (synC2c)))
      (synCvv)
  have p0056 :=
    @gMpbiran2
      (.classMem (synCop (.cv n) (.cv b))
        (synCxp (synCima (synCcnv (synC2nd)) (synCsn (synC2c))) (synCvv)))
      (.classMem (.cv n) (synCima (synCcnv (synC2nd)) (synCsn (synC2c))))
      (.classMem (.cv b) (synCvv)) p0014 p0055
  have p0057 := @gEliniseg (synC2nd) (synC2c) (.cv n)
  have p0058 :=
    @gBitri
      (.classMem (synCop (.cv n) (.cv b))
        (synCxp (synCima (synCcnv (synC2nd)) (synCsn (synC2c))) (synCvv)))
      (.classMem (.cv n) (synCima (synCcnv (synC2nd)) (synCsn (synC2c))))
      (synWbr (.cv n) (synC2nd) (synC2c)) p0056 p0057
  have p0059 :=
    @gAnbi12i (.classMem (synCop (.cv n) (.cv b)) (synC1st))
      (synWbr (.cv n) (synC1st) (.cv b))
      (.classMem (synCop (.cv n) (.cv b))
        (synCxp (synCima (synCcnv (synC2nd)) (synCsn (synC2c))) (synCvv)))
      (synWbr (.cv n) (synC2nd) (synC2c)) p0013 p0058
  have p0060 := (Nominal.classEqRefl (synC2c))
  have p0061 := @gNcex (synCpr (synC0) (synCvv))
  have p0062 :=
    @gEqeltri (synC2c) (synCnc (synCpr (synC0) (synCvv))) (synCvv) p0060 p0061
  have p0063 := @gOp1st2nd (.cv b) (synC2c) (.cv n) p0014 p0062
  have p0064 :=
    @gN3bitri
      (.classMem (synCop (.cv n) (.cv b)) (synCin (synC1st)
          (synCxp (synCima (synCcnv (synC2nd)) (synCsn (synC2c))) (synCvv))))
      (synWa (.classMem (synCop (.cv n) (.cv b)) (synC1st))
        (.classMem (synCop (.cv n) (.cv b))
          (synCxp (synCima (synCcnv (synC2nd)) (synCsn (synC2c))) (synCvv))))
      (synWa (synWbr (.cv n) (synC1st) (.cv b)) (synWbr (.cv n) (synC2nd) (synC2c)))
      (.classEq (.cv n) (synCop (.cv b) (synC2c))) p0054 p0059 p0063
  have p0065 :=
    @gAnbi12i
      (.classMem (synCop (.cv n) (.cv b)) (synCin (synC1st)
          (synCxp (synCima (synCcnv (synC2nd)) (synCsn (synC2c))) (synCvv))))
      (.classEq (.cv n) (synCop (.cv b) (synC2c)))
      (.classMem (synCop (.cv n) (.cv a)) (synCaddcfn))
      (synWbr (.cv n) (synCaddcfn) (.cv a)) p0064 p0024
  have p0066 :=
    @gBitri
      (.classMem (synCop (.cv n) (synCop (.cv b) (.cv a))) (synCtxp (synCin (synC1st)
            (synCxp (synCima (synCcnv (synC2nd)) (synCsn (synC2c))) (synCvv)))
          (synCaddcfn)))
      (synWa (.classMem (synCop (.cv n) (.cv b)) (synCin (synC1st)
            (synCxp (synCima (synCcnv (synC2nd)) (synCsn (synC2c))) (synCvv))))
        (.classMem (synCop (.cv n) (.cv a)) (synCaddcfn)))
      (synWa (.classEq (.cv n) (synCop (.cv b) (synC2c)))
        (synWbr (.cv n) (synCaddcfn) (.cv a)))
      p0053 p0065
  have p0067 :=
    @gExbii
      (.classMem (synCop (.cv n) (synCop (.cv b) (.cv a))) (synCtxp (synCin (synC1st)
            (synCxp (synCima (synCcnv (synC2nd)) (synCsn (synC2c))) (synCvv)))
          (synCaddcfn)))
      (synWa (.classEq (.cv n) (synCop (.cv b) (synC2c)))
        (synWbr (.cv n) (synCaddcfn) (.cv a)))
      n p0066
  have p0068 := @gOpex (.cv b) (synC2c) p0014 p0062
  have p0069 := @gBreq1 (.cv n) (synCop (.cv b) (synC2c)) (.cv a) (synCaddcfn)
  have p0070 :=
    @gCeqsexv (synWbr (.cv n) (synCaddcfn) (.cv a))
      (synWbr (synCop (.cv b) (synC2c)) (synCaddcfn) (.cv a)) n
      (synCop (.cv b) (synC2c)) dv_cache_0014 dv_cache_0015 p0068 p0069
  have p0071 :=
    @gN3bitri
      (.classMem (synCop (.cv b) (.cv a)) (synCrn (synCtxp (synCin (synC1st)
              (synCxp (synCima (synCcnv (synC2nd)) (synCsn (synC2c))) (synCvv)))
            (synCaddcfn))))
      (synWex n (.classMem (synCop (.cv n) (synCop (.cv b) (.cv a))) (synCtxp
            (synCin (synC1st)
              (synCxp (synCima (synCcnv (synC2nd)) (synCsn (synC2c))) (synCvv)))
            (synCaddcfn))))
      (synWex n (synWa (.classEq (.cv n) (synCop (.cv b) (synC2c)))
          (synWbr (.cv n) (synCaddcfn) (.cv a))))
      (synWbr (synCop (.cv b) (synC2c)) (synCaddcfn) (.cv a)) p0052 p0067 p0070
  have p0072 := @gBraddcfn (.cv b) (synC2c) (.cv a) p0014 p0062
  have p0073 := @gEqcom (synCplc (.cv b) (synC2c)) (.cv a)
  have p0074 :=
    @gN3bitri
      (.classMem (synCop (.cv b) (.cv a)) (synCrn (synCtxp (synCin (synC1st)
              (synCxp (synCima (synCcnv (synC2nd)) (synCsn (synC2c))) (synCvv)))
            (synCaddcfn))))
      (synWbr (synCop (.cv b) (synC2c)) (synCaddcfn) (.cv a))
      (.classEq (synCplc (.cv b) (synC2c)) (.cv a))
      (.classEq (.cv a) (synCplc (.cv b) (synC2c))) p0071 p0072 p0073
  have p0075 :=
    @gAnbi12i
      (.classMem (synCop (.cv b) (.cv n)) (synCcnv (synCrn (synCin (synCins3 (synCcnv
                  (synCima (synCtxp (synCrn
                        (synCtxp (synCcnv (synC1st)) (synCin (synC1st) (synC2nd))))
                      (synC2nd)) (synCaddcfn)))) (synCima
                (synCtxp (synCcom (synC1st) (synC1st))
                  (synCtxp (synCcom (synC2nd) (synC1st)) (synC2nd))) (synCaddcfn))))))
      (.classEq (.cv b) (synCplc (synCplc (.cv n) (.cv n)) (.cv n)))
      (.classMem (synCop (.cv b) (.cv a)) (synCrn (synCtxp (synCin (synC1st)
              (synCxp (synCima (synCcnv (synC2nd)) (synCsn (synC2c))) (synCvv)))
            (synCaddcfn))))
      (.classEq (.cv a) (synCplc (.cv b) (synC2c))) p0008 p0074
  have p0076 :=
    @gBitri
      (.classMem (synCop (.cv b) (synCop (.cv n) (.cv a))) (synCtxp (synCcnv (synCrn
              (synCin (synCins3 (synCcnv (synCima (synCtxp (synCrn
                          (synCtxp (synCcnv (synC1st)) (synCin (synC1st) (synC2nd))))
                        (synC2nd)) (synCaddcfn)))) (synCima
                  (synCtxp (synCcom (synC1st) (synC1st))
                    (synCtxp (synCcom (synC2nd) (synC1st)) (synC2nd))) (synCaddcfn)))))
          (synCrn (synCtxp (synCin (synC1st)
                (synCxp (synCima (synCcnv (synC2nd)) (synCsn (synC2c))) (synCvv)))
              (synCaddcfn)))))
      (synWa (.classMem (synCop (.cv b) (.cv n)) (synCcnv (synCrn (synCin (synCins3
                  (synCcnv (synCima (synCtxp (synCrn (synCtxp (synCcnv (synC1st))
                            (synCin (synC1st) (synC2nd)))) (synC2nd)) (synCaddcfn))))
                (synCima (synCtxp (synCcom (synC1st) (synC1st))
                    (synCtxp (synCcom (synC2nd) (synC1st)) (synC2nd))) (synCaddcfn))))))
        (.classMem (synCop (.cv b) (.cv a)) (synCrn (synCtxp (synCin (synC1st)
                (synCxp (synCima (synCcnv (synC2nd)) (synCsn (synC2c))) (synCvv)))
              (synCaddcfn)))))
      (synWa (.classEq (.cv b) (synCplc (synCplc (.cv n) (.cv n)) (.cv n)))
        (.classEq (.cv a) (synCplc (.cv b) (synC2c))))
      p0051 p0075
  have p0077 :=
    @gExbii
      (.classMem (synCop (.cv b) (synCop (.cv n) (.cv a))) (synCtxp (synCcnv (synCrn
              (synCin (synCins3 (synCcnv (synCima (synCtxp (synCrn
                          (synCtxp (synCcnv (synC1st)) (synCin (synC1st) (synC2nd))))
                        (synC2nd)) (synCaddcfn)))) (synCima
                  (synCtxp (synCcom (synC1st) (synC1st))
                    (synCtxp (synCcom (synC2nd) (synC1st)) (synC2nd))) (synCaddcfn)))))
          (synCrn (synCtxp (synCin (synC1st)
                (synCxp (synCima (synCcnv (synC2nd)) (synCsn (synC2c))) (synCvv)))
              (synCaddcfn)))))
      (synWa (.classEq (.cv b) (synCplc (synCplc (.cv n) (.cv n)) (.cv n)))
        (.classEq (.cv a) (synCplc (.cv b) (synC2c))))
      b p0076
  have p0078 := @gAddceq1 (.cv b) (synCplc (synCplc (.cv n) (.cv n)) (.cv n)) (synC2c)
  have p0079 :=
    @gEqeq2d (.classEq (.cv b) (synCplc (synCplc (.cv n) (.cv n)) (.cv n)))
      (synCplc (.cv b) (synC2c))
      (synCplc (synCplc (synCplc (.cv n) (.cv n)) (.cv n)) (synC2c)) (.cv a) p0078
  have p0080 :=
    @gCeqsexv (.classEq (.cv a) (synCplc (.cv b) (synC2c)))
      (.classEq (.cv a) (synCplc (synCplc (synCplc (.cv n) (.cv n)) (.cv n)) (synC2c)))
      b (synCplc (synCplc (.cv n) (.cv n)) (.cv n)) dv_cache_0010 dv_cache_0016 p0043
      p0079
  have p0081 :=
    @gN3bitri
      (.classMem (synCop (.cv n) (.cv a)) (synCrn (synCtxp (synCcnv (synCrn (synCin
                  (synCins3 (synCcnv (synCima (synCtxp (synCrn
                            (synCtxp (synCcnv (synC1st)) (synCin (synC1st) (synC2nd))))
                          (synC2nd)) (synCaddcfn)))) (synCima
                    (synCtxp (synCcom (synC1st) (synC1st))
                      (synCtxp (synCcom (synC2nd) (synC1st)) (synC2nd))) (synCaddcfn)))))
            (synCrn (synCtxp (synCin (synC1st)
                  (synCxp (synCima (synCcnv (synC2nd)) (synCsn (synC2c))) (synCvv)))
                (synCaddcfn))))))
      (synWex b (.classMem (synCop (.cv b) (synCop (.cv n) (.cv a))) (synCtxp (synCcnv
              (synCrn (synCin (synCins3 (synCcnv (synCima (synCtxp (synCrn
                            (synCtxp (synCcnv (synC1st)) (synCin (synC1st) (synC2nd))))
                          (synC2nd)) (synCaddcfn)))) (synCima
                    (synCtxp (synCcom (synC1st) (synC1st))
                      (synCtxp (synCcom (synC2nd) (synC1st)) (synC2nd))) (synCaddcfn)))))
            (synCrn (synCtxp (synCin (synC1st)
                  (synCxp (synCima (synCcnv (synC2nd)) (synCsn (synC2c))) (synCvv)))
                (synCaddcfn))))))
      (synWex b (synWa (.classEq (.cv b) (synCplc (synCplc (.cv n) (.cv n)) (.cv n)))
          (.classEq (.cv a) (synCplc (.cv b) (synC2c)))))
      (.classEq (.cv a) (synCplc (synCplc (synCplc (.cv n) (.cv n)) (.cv n)) (synC2c)))
      p0050 p0077 p0080
  have p0082 :=
    @gOrbi12i
      (.classMem (synCop (.cv n) (.cv a)) (synCun (synCrn (synCin (synCins3 (synCcnv
                  (synCima (synCtxp (synCrn
                        (synCtxp (synCcnv (synC1st)) (synCin (synC1st) (synC2nd))))
                      (synC2nd)) (synCaddcfn)))) (synCima
                (synCtxp (synCcom (synC1st) (synC1st))
                  (synCtxp (synCcom (synC2nd) (synC1st)) (synC2nd))) (synCaddcfn))))
          (synCrn (synCtxp (synCcnv (synCrn (synCin (synCins3 (synCcnv (synCima
                          (synCtxp (synCrn (synCtxp (synCcnv (synC1st))
                                (synCin (synC1st) (synC2nd)))) (synC2nd)) (synCaddcfn))))
                    (synCima (synCtxp (synCcom (synC1st) (synC1st))
                        (synCtxp (synCcom (synC2nd) (synC1st)) (synC2nd)))
                      (synCaddcfn))))) (synCrn (synCtxp (synCin (synC1st)
                    (synCxp (synCima (synCcnv (synC2nd)) (synCsn (synC1c))) (synCvv)))
                  (synCaddcfn)))))))
      (synWo (.classEq (.cv a) (synCplc (synCplc (.cv n) (.cv n)) (.cv n))) (.classEq (.cv a)
          (synCplc (synCplc (synCplc (.cv n) (.cv n)) (.cv n)) (synC1c))))
      (.classMem (synCop (.cv n) (.cv a)) (synCrn (synCtxp (synCcnv (synCrn (synCin
                  (synCins3 (synCcnv (synCima (synCtxp (synCrn
                            (synCtxp (synCcnv (synC1st)) (synCin (synC1st) (synC2nd))))
                          (synC2nd)) (synCaddcfn)))) (synCima
                    (synCtxp (synCcom (synC1st) (synC1st))
                      (synCtxp (synCcom (synC2nd) (synC1st)) (synC2nd))) (synCaddcfn)))))
            (synCrn (synCtxp (synCin (synC1st)
                  (synCxp (synCima (synCcnv (synC2nd)) (synCsn (synC2c))) (synCvv)))
                (synCaddcfn))))))
      (.classEq (.cv a) (synCplc (synCplc (synCplc (.cv n) (.cv n)) (.cv n)) (synC2c)))
      p0049 p0081
  have p0083 :=
    @gElun (synCop (.cv n) (.cv a))
      (synCun (synCrn (synCin (synCins3 (synCcnv (synCima (synCtxp (synCrn
                      (synCtxp (synCcnv (synC1st)) (synCin (synC1st) (synC2nd))))
                    (synC2nd)) (synCaddcfn)))) (synCima
              (synCtxp (synCcom (synC1st) (synC1st))
                (synCtxp (synCcom (synC2nd) (synC1st)) (synC2nd))) (synCaddcfn))))
        (synCrn (synCtxp (synCcnv (synCrn (synCin (synCins3 (synCcnv (synCima (synCtxp
                          (synCrn (synCtxp (synCcnv (synC1st))
                              (synCin (synC1st) (synC2nd)))) (synC2nd)) (synCaddcfn))))
                  (synCima (synCtxp (synCcom (synC1st) (synC1st))
                      (synCtxp (synCcom (synC2nd) (synC1st)) (synC2nd))) (synCaddcfn)))))
            (synCrn (synCtxp (synCin (synC1st)
                  (synCxp (synCima (synCcnv (synC2nd)) (synCsn (synC1c))) (synCvv)))
                (synCaddcfn))))))
      (synCrn (synCtxp (synCcnv (synCrn (synCin (synCins3 (synCcnv (synCima (synCtxp
                        (synCrn (synCtxp (synCcnv (synC1st))
                            (synCin (synC1st) (synC2nd)))) (synC2nd)) (synCaddcfn))))
                (synCima (synCtxp (synCcom (synC1st) (synC1st))
                    (synCtxp (synCcom (synC2nd) (synC1st)) (synC2nd))) (synCaddcfn)))))
          (synCrn (synCtxp (synCin (synC1st)
                (synCxp (synCima (synCcnv (synC2nd)) (synCsn (synC2c))) (synCvv)))
              (synCaddcfn)))))
  have p0084 :=
    (Nominal.biimpRefl (synW3o (.classEq (.cv a) (synCplc (synCplc (.cv n) (.cv n)) (.cv n)))
        (.classEq (.cv a) (synCplc (synCplc (synCplc (.cv n) (.cv n)) (.cv n)) (synC1c)))
        (.classEq (.cv a) (synCplc (synCplc (synCplc (.cv n) (.cv n)) (.cv n)) (synC2c)))))
  have p0085 :=
    @gN3bitr4i
      (synWo (.classMem (synCop (.cv n) (.cv a)) (synCun (synCrn (synCin (synCins3
                  (synCcnv (synCima (synCtxp (synCrn (synCtxp (synCcnv (synC1st))
                            (synCin (synC1st) (synC2nd)))) (synC2nd)) (synCaddcfn))))
                (synCima (synCtxp (synCcom (synC1st) (synC1st))
                    (synCtxp (synCcom (synC2nd) (synC1st)) (synC2nd))) (synCaddcfn))))
            (synCrn (synCtxp (synCcnv (synCrn (synCin (synCins3 (synCcnv (synCima
                            (synCtxp (synCrn (synCtxp (synCcnv (synC1st))
                                  (synCin (synC1st) (synC2nd)))) (synC2nd)) (synCaddcfn))))
                      (synCima (synCtxp (synCcom (synC1st) (synC1st))
                          (synCtxp (synCcom (synC2nd) (synC1st)) (synC2nd)))
                        (synCaddcfn))))) (synCrn (synCtxp (synCin (synC1st)
                      (synCxp (synCima (synCcnv (synC2nd)) (synCsn (synC1c))) (synCvv)))
                    (synCaddcfn))))))) (.classMem (synCop (.cv n) (.cv a)) (synCrn (synCtxp
              (synCcnv (synCrn (synCin (synCins3 (synCcnv (synCima (synCtxp (synCrn
                              (synCtxp (synCcnv (synC1st)) (synCin (synC1st) (synC2nd))))
                            (synC2nd)) (synCaddcfn)))) (synCima
                      (synCtxp (synCcom (synC1st) (synC1st))
                        (synCtxp (synCcom (synC2nd) (synC1st)) (synC2nd)))
                      (synCaddcfn))))) (synCrn (synCtxp (synCin (synC1st)
                    (synCxp (synCima (synCcnv (synC2nd)) (synCsn (synC2c))) (synCvv)))
                  (synCaddcfn)))))))
      (synWo (synWo (.classEq (.cv a) (synCplc (synCplc (.cv n) (.cv n)) (.cv n)))
          (.classEq (.cv a) (synCplc (synCplc (synCplc (.cv n) (.cv n)) (.cv n)) (synC1c))))
        (.classEq (.cv a) (synCplc (synCplc (synCplc (.cv n) (.cv n)) (.cv n)) (synC2c))))
      (.classMem (synCop (.cv n) (.cv a)) (synCun (synCun (synCrn (synCin (synCins3
                  (synCcnv (synCima (synCtxp (synCrn (synCtxp (synCcnv (synC1st))
                            (synCin (synC1st) (synC2nd)))) (synC2nd)) (synCaddcfn))))
                (synCima (synCtxp (synCcom (synC1st) (synC1st))
                    (synCtxp (synCcom (synC2nd) (synC1st)) (synC2nd))) (synCaddcfn))))
            (synCrn (synCtxp (synCcnv (synCrn (synCin (synCins3 (synCcnv (synCima
                            (synCtxp (synCrn (synCtxp (synCcnv (synC1st))
                                  (synCin (synC1st) (synC2nd)))) (synC2nd)) (synCaddcfn))))
                      (synCima (synCtxp (synCcom (synC1st) (synC1st))
                          (synCtxp (synCcom (synC2nd) (synC1st)) (synC2nd)))
                        (synCaddcfn))))) (synCrn (synCtxp (synCin (synC1st)
                      (synCxp (synCima (synCcnv (synC2nd)) (synCsn (synC1c))) (synCvv)))
                    (synCaddcfn)))))) (synCrn (synCtxp (synCcnv (synCrn (synCin (synCins3
                      (synCcnv (synCima (synCtxp (synCrn (synCtxp (synCcnv (synC1st))
                                (synCin (synC1st) (synC2nd)))) (synC2nd)) (synCaddcfn))))
                    (synCima (synCtxp (synCcom (synC1st) (synC1st))
                        (synCtxp (synCcom (synC2nd) (synC1st)) (synC2nd)))
                      (synCaddcfn))))) (synCrn (synCtxp (synCin (synC1st)
                    (synCxp (synCima (synCcnv (synC2nd)) (synCsn (synC2c))) (synCvv)))
                  (synCaddcfn)))))))
      (synW3o (.classEq (.cv a) (synCplc (synCplc (.cv n) (.cv n)) (.cv n)))
        (.classEq (.cv a) (synCplc (synCplc (synCplc (.cv n) (.cv n)) (.cv n)) (synC1c)))
        (.classEq (.cv a) (synCplc (synCplc (synCplc (.cv n) (.cv n)) (.cv n)) (synC2c))))
      p0082 p0083 p0084
  have p0086 :=
    @gBitri
      (synWbr (.cv n) (synCun (synCun (synCrn (synCin (synCins3 (synCcnv (synCima
                      (synCtxp (synCrn (synCtxp (synCcnv (synC1st))
                            (synCin (synC1st) (synC2nd)))) (synC2nd)) (synCaddcfn))))
                (synCima (synCtxp (synCcom (synC1st) (synC1st))
                    (synCtxp (synCcom (synC2nd) (synC1st)) (synC2nd))) (synCaddcfn))))
            (synCrn (synCtxp (synCcnv (synCrn (synCin (synCins3 (synCcnv (synCima
                            (synCtxp (synCrn (synCtxp (synCcnv (synC1st))
                                  (synCin (synC1st) (synC2nd)))) (synC2nd)) (synCaddcfn))))
                      (synCima (synCtxp (synCcom (synC1st) (synC1st))
                          (synCtxp (synCcom (synC2nd) (synC1st)) (synC2nd)))
                        (synCaddcfn))))) (synCrn (synCtxp (synCin (synC1st)
                      (synCxp (synCima (synCcnv (synC2nd)) (synCsn (synC1c))) (synCvv)))
                    (synCaddcfn)))))) (synCrn (synCtxp (synCcnv (synCrn (synCin (synCins3
                      (synCcnv (synCima (synCtxp (synCrn (synCtxp (synCcnv (synC1st))
                                (synCin (synC1st) (synC2nd)))) (synC2nd)) (synCaddcfn))))
                    (synCima (synCtxp (synCcom (synC1st) (synC1st))
                        (synCtxp (synCcom (synC2nd) (synC1st)) (synC2nd)))
                      (synCaddcfn))))) (synCrn (synCtxp (synCin (synC1st)
                    (synCxp (synCima (synCcnv (synC2nd)) (synCsn (synC2c))) (synCvv)))
                  (synCaddcfn)))))) (.cv a))
      (.classMem (synCop (.cv n) (.cv a)) (synCun (synCun (synCrn (synCin (synCins3
                  (synCcnv (synCima (synCtxp (synCrn (synCtxp (synCcnv (synC1st))
                            (synCin (synC1st) (synC2nd)))) (synC2nd)) (synCaddcfn))))
                (synCima (synCtxp (synCcom (synC1st) (synC1st))
                    (synCtxp (synCcom (synC2nd) (synC1st)) (synC2nd))) (synCaddcfn))))
            (synCrn (synCtxp (synCcnv (synCrn (synCin (synCins3 (synCcnv (synCima
                            (synCtxp (synCrn (synCtxp (synCcnv (synC1st))
                                  (synCin (synC1st) (synC2nd)))) (synC2nd)) (synCaddcfn))))
                      (synCima (synCtxp (synCcom (synC1st) (synC1st))
                          (synCtxp (synCcom (synC2nd) (synC1st)) (synC2nd)))
                        (synCaddcfn))))) (synCrn (synCtxp (synCin (synC1st)
                      (synCxp (synCima (synCcnv (synC2nd)) (synCsn (synC1c))) (synCvv)))
                    (synCaddcfn)))))) (synCrn (synCtxp (synCcnv (synCrn (synCin (synCins3
                      (synCcnv (synCima (synCtxp (synCrn (synCtxp (synCcnv (synC1st))
                                (synCin (synC1st) (synC2nd)))) (synC2nd)) (synCaddcfn))))
                    (synCima (synCtxp (synCcom (synC1st) (synC1st))
                        (synCtxp (synCcom (synC2nd) (synC1st)) (synC2nd)))
                      (synCaddcfn))))) (synCrn (synCtxp (synCin (synC1st)
                    (synCxp (synCima (synCcnv (synC2nd)) (synCsn (synC2c))) (synCvv)))
                  (synCaddcfn)))))))
      (synW3o (.classEq (.cv a) (synCplc (synCplc (.cv n) (.cv n)) (.cv n)))
        (.classEq (.cv a) (synCplc (synCplc (synCplc (.cv n) (.cv n)) (.cv n)) (synC1c)))
        (.classEq (.cv a) (synCplc (synCplc (synCplc (.cv n) (.cv n)) (.cv n)) (synC2c))))
      p0001 p0085
  have p0087 :=
    @gRexbii
      (synWbr (.cv n) (synCun (synCun (synCrn (synCin (synCins3 (synCcnv (synCima
                      (synCtxp (synCrn (synCtxp (synCcnv (synC1st))
                            (synCin (synC1st) (synC2nd)))) (synC2nd)) (synCaddcfn))))
                (synCima (synCtxp (synCcom (synC1st) (synC1st))
                    (synCtxp (synCcom (synC2nd) (synC1st)) (synC2nd))) (synCaddcfn))))
            (synCrn (synCtxp (synCcnv (synCrn (synCin (synCins3 (synCcnv (synCima
                            (synCtxp (synCrn (synCtxp (synCcnv (synC1st))
                                  (synCin (synC1st) (synC2nd)))) (synC2nd)) (synCaddcfn))))
                      (synCima (synCtxp (synCcom (synC1st) (synC1st))
                          (synCtxp (synCcom (synC2nd) (synC1st)) (synC2nd)))
                        (synCaddcfn))))) (synCrn (synCtxp (synCin (synC1st)
                      (synCxp (synCima (synCcnv (synC2nd)) (synCsn (synC1c))) (synCvv)))
                    (synCaddcfn)))))) (synCrn (synCtxp (synCcnv (synCrn (synCin (synCins3
                      (synCcnv (synCima (synCtxp (synCrn (synCtxp (synCcnv (synC1st))
                                (synCin (synC1st) (synC2nd)))) (synC2nd)) (synCaddcfn))))
                    (synCima (synCtxp (synCcom (synC1st) (synC1st))
                        (synCtxp (synCcom (synC2nd) (synC1st)) (synC2nd)))
                      (synCaddcfn))))) (synCrn (synCtxp (synCin (synC1st)
                    (synCxp (synCima (synCcnv (synC2nd)) (synCsn (synC2c))) (synCvv)))
                  (synCaddcfn)))))) (.cv a))
      (synW3o (.classEq (.cv a) (synCplc (synCplc (.cv n) (.cv n)) (.cv n)))
        (.classEq (.cv a) (synCplc (synCplc (synCplc (.cv n) (.cv n)) (.cv n)) (synC1c)))
        (.classEq (.cv a) (synCplc (synCplc (synCplc (.cv n) (.cv n)) (.cv n)) (synC2c))))
      n (synCnnc) p0086
  have p0088 :=
    @gBitri
      (.classMem (.cv a) (synCima (synCun (synCun (synCrn (synCin (synCins3 (synCcnv
                      (synCima (synCtxp (synCrn (synCtxp (synCcnv (synC1st))
                              (synCin (synC1st) (synC2nd)))) (synC2nd)) (synCaddcfn))))
                  (synCima (synCtxp (synCcom (synC1st) (synC1st))
                      (synCtxp (synCcom (synC2nd) (synC1st)) (synC2nd))) (synCaddcfn))))
              (synCrn (synCtxp (synCcnv (synCrn (synCin (synCins3 (synCcnv (synCima
                              (synCtxp (synCrn (synCtxp (synCcnv (synC1st))
                                    (synCin (synC1st) (synC2nd)))) (synC2nd))
                              (synCaddcfn)))) (synCima
                          (synCtxp (synCcom (synC1st) (synC1st))
                            (synCtxp (synCcom (synC2nd) (synC1st)) (synC2nd)))
                          (synCaddcfn))))) (synCrn (synCtxp (synCin (synC1st)
                        (synCxp (synCima (synCcnv (synC2nd)) (synCsn (synC1c)))
                          (synCvv))) (synCaddcfn)))))) (synCrn (synCtxp (synCcnv (synCrn
                    (synCin (synCins3 (synCcnv (synCima (synCtxp (synCrn
                                (synCtxp (synCcnv (synC1st))
                                  (synCin (synC1st) (synC2nd)))) (synC2nd)) (synCaddcfn))))
                      (synCima (synCtxp (synCcom (synC1st) (synC1st))
                          (synCtxp (synCcom (synC2nd) (synC1st)) (synC2nd)))
                        (synCaddcfn))))) (synCrn (synCtxp (synCin (synC1st)
                      (synCxp (synCima (synCcnv (synC2nd)) (synCsn (synC2c))) (synCvv)))
                    (synCaddcfn)))))) (synCnnc)))
      (synWrex n (synCnnc) (synWbr (.cv n) (synCun (synCun (synCrn (synCin (synCins3
                    (synCcnv (synCima (synCtxp (synCrn (synCtxp (synCcnv (synC1st))
                              (synCin (synC1st) (synC2nd)))) (synC2nd)) (synCaddcfn))))
                  (synCima (synCtxp (synCcom (synC1st) (synC1st))
                      (synCtxp (synCcom (synC2nd) (synC1st)) (synC2nd))) (synCaddcfn))))
              (synCrn (synCtxp (synCcnv (synCrn (synCin (synCins3 (synCcnv (synCima
                              (synCtxp (synCrn (synCtxp (synCcnv (synC1st))
                                    (synCin (synC1st) (synC2nd)))) (synC2nd))
                              (synCaddcfn)))) (synCima
                          (synCtxp (synCcom (synC1st) (synC1st))
                            (synCtxp (synCcom (synC2nd) (synC1st)) (synC2nd)))
                          (synCaddcfn))))) (synCrn (synCtxp (synCin (synC1st)
                        (synCxp (synCima (synCcnv (synC2nd)) (synCsn (synC1c)))
                          (synCvv))) (synCaddcfn)))))) (synCrn (synCtxp (synCcnv (synCrn
                    (synCin (synCins3 (synCcnv (synCima (synCtxp (synCrn
                                (synCtxp (synCcnv (synC1st))
                                  (synCin (synC1st) (synC2nd)))) (synC2nd)) (synCaddcfn))))
                      (synCima (synCtxp (synCcom (synC1st) (synC1st))
                          (synCtxp (synCcom (synC2nd) (synC1st)) (synC2nd)))
                        (synCaddcfn))))) (synCrn (synCtxp (synCin (synC1st)
                      (synCxp (synCima (synCcnv (synC2nd)) (synCsn (synC2c))) (synCvv)))
                    (synCaddcfn)))))) (.cv a)))
      (synWrex n (synCnnc)
        (synW3o (.classEq (.cv a) (synCplc (synCplc (.cv n) (.cv n)) (.cv n)))
          (.classEq (.cv a) (synCplc (synCplc (synCplc (.cv n) (.cv n)) (.cv n)) (synC1c)))
          (.classEq (.cv a)
            (synCplc (synCplc (synCplc (.cv n) (.cv n)) (.cv n)) (synC2c)))))
      p0000 p0087
  have p0089 :=
    @gEqabi
      (synWrex n (synCnnc)
        (synW3o (.classEq (.cv a) (synCplc (synCplc (.cv n) (.cv n)) (.cv n)))
          (.classEq (.cv a) (synCplc (synCplc (synCplc (.cv n) (.cv n)) (.cv n)) (synC1c)))
          (.classEq (.cv a)
            (synCplc (synCplc (synCplc (.cv n) (.cv n)) (.cv n)) (synC2c)))))
      a
      (synCima (synCun (synCun (synCrn (synCin (synCins3 (synCcnv (synCima (synCtxp
                        (synCrn (synCtxp (synCcnv (synC1st))
                            (synCin (synC1st) (synC2nd)))) (synC2nd)) (synCaddcfn))))
                (synCima (synCtxp (synCcom (synC1st) (synC1st))
                    (synCtxp (synCcom (synC2nd) (synC1st)) (synC2nd))) (synCaddcfn))))
            (synCrn (synCtxp (synCcnv (synCrn (synCin (synCins3 (synCcnv (synCima
                            (synCtxp (synCrn (synCtxp (synCcnv (synC1st))
                                  (synCin (synC1st) (synC2nd)))) (synC2nd)) (synCaddcfn))))
                      (synCima (synCtxp (synCcom (synC1st) (synC1st))
                          (synCtxp (synCcom (synC2nd) (synC1st)) (synC2nd)))
                        (synCaddcfn))))) (synCrn (synCtxp (synCin (synC1st)
                      (synCxp (synCima (synCcnv (synC2nd)) (synCsn (synC1c))) (synCvv)))
                    (synCaddcfn)))))) (synCrn (synCtxp (synCcnv (synCrn (synCin (synCins3
                      (synCcnv (synCima (synCtxp (synCrn (synCtxp (synCcnv (synC1st))
                                (synCin (synC1st) (synC2nd)))) (synC2nd)) (synCaddcfn))))
                    (synCima (synCtxp (synCcom (synC1st) (synC1st))
                        (synCtxp (synCcom (synC2nd) (synC1st)) (synC2nd)))
                      (synCaddcfn))))) (synCrn (synCtxp (synCin (synC1st)
                    (synCxp (synCima (synCcnv (synC2nd)) (synCsn (synC2c))) (synCvv)))
                  (synCaddcfn)))))) (synCnnc))
      dv_cache_0017 p0088
  have p0090 := @gN1stex
  have p0091 := @gCnvex (synC1st) p0090
  have p0093 := @gN2ndex
  have p0094 := @gInex (synC1st) (synC2nd) p0090 p0093
  have p0095 := @gTxpex (synCcnv (synC1st)) (synCin (synC1st) (synC2nd)) p0091 p0094
  have p0096 :=
    @gRnex (synCtxp (synCcnv (synC1st)) (synCin (synC1st) (synC2nd))) p0095
  have p0098 :=
    @gTxpex (synCrn (synCtxp (synCcnv (synC1st)) (synCin (synC1st) (synC2nd))))
      (synC2nd) p0096 p0093
  have p0099 := @gAddcfnex
  have p0100 :=
    @gImaex
      (synCtxp (synCrn (synCtxp (synCcnv (synC1st)) (synCin (synC1st) (synC2nd))))
        (synC2nd))
      (synCaddcfn) p0098 p0099
  have p0101 :=
    @gCnvex
      (synCima (synCtxp
          (synCrn (synCtxp (synCcnv (synC1st)) (synCin (synC1st) (synC2nd)))) (synC2nd))
        (synCaddcfn))
      p0100
  have p0102 :=
    @gIns3ex
      (synCcnv (synCima (synCtxp
            (synCrn (synCtxp (synCcnv (synC1st)) (synCin (synC1st) (synC2nd))))
            (synC2nd)) (synCaddcfn)))
      p0101
  have p0105 := @gCoex (synC1st) (synC1st) p0090 p0090
  have p0108 := @gCoex (synC2nd) (synC1st) p0093 p0090
  have p0110 := @gTxpex (synCcom (synC2nd) (synC1st)) (synC2nd) p0108 p0093
  have p0111 :=
    @gTxpex (synCcom (synC1st) (synC1st))
      (synCtxp (synCcom (synC2nd) (synC1st)) (synC2nd)) p0105 p0110
  have p0113 :=
    @gImaex
      (synCtxp (synCcom (synC1st) (synC1st))
        (synCtxp (synCcom (synC2nd) (synC1st)) (synC2nd)))
      (synCaddcfn) p0111 p0099
  have p0114 :=
    @gInex
      (synCins3 (synCcnv (synCima (synCtxp
              (synCrn (synCtxp (synCcnv (synC1st)) (synCin (synC1st) (synC2nd))))
              (synC2nd)) (synCaddcfn))))
      (synCima (synCtxp (synCcom (synC1st) (synC1st))
          (synCtxp (synCcom (synC2nd) (synC1st)) (synC2nd))) (synCaddcfn))
      p0102 p0113
  have p0115 :=
    @gRnex
      (synCin (synCins3 (synCcnv (synCima (synCtxp
                (synCrn (synCtxp (synCcnv (synC1st)) (synCin (synC1st) (synC2nd))))
                (synC2nd)) (synCaddcfn)))) (synCima
          (synCtxp (synCcom (synC1st) (synC1st))
            (synCtxp (synCcom (synC2nd) (synC1st)) (synC2nd))) (synCaddcfn)))
      p0114
  have p0116 :=
    @gCnvex
      (synCrn (synCin (synCins3 (synCcnv (synCima (synCtxp (synCrn
                    (synCtxp (synCcnv (synC1st)) (synCin (synC1st) (synC2nd))))
                  (synC2nd)) (synCaddcfn)))) (synCima
            (synCtxp (synCcom (synC1st) (synC1st))
              (synCtxp (synCcom (synC2nd) (synC1st)) (synC2nd))) (synCaddcfn))))
      p0115
  have p0119 := @gCnvex (synC2nd) p0093
  have p0120 := @gSnex (synC1c)
  have p0121 := @gImaex (synCcnv (synC2nd)) (synCsn (synC1c)) p0119 p0120
  have p0122 := @gVvex
  have p0123 :=
    @gXpex (synCima (synCcnv (synC2nd)) (synCsn (synC1c))) (synCvv) p0121 p0122
  have p0124 :=
    @gInex (synC1st)
      (synCxp (synCima (synCcnv (synC2nd)) (synCsn (synC1c))) (synCvv)) p0090 p0123
  have p0126 :=
    @gTxpex
      (synCin (synC1st)
        (synCxp (synCima (synCcnv (synC2nd)) (synCsn (synC1c))) (synCvv)))
      (synCaddcfn) p0124 p0099
  have p0127 :=
    @gRnex
      (synCtxp (synCin (synC1st)
          (synCxp (synCima (synCcnv (synC2nd)) (synCsn (synC1c))) (synCvv)))
        (synCaddcfn))
      p0126
  have p0128 :=
    @gTxpex
      (synCcnv (synCrn (synCin (synCins3 (synCcnv (synCima (synCtxp (synCrn
                      (synCtxp (synCcnv (synC1st)) (synCin (synC1st) (synC2nd))))
                    (synC2nd)) (synCaddcfn)))) (synCima
              (synCtxp (synCcom (synC1st) (synC1st))
                (synCtxp (synCcom (synC2nd) (synC1st)) (synC2nd))) (synCaddcfn)))))
      (synCrn (synCtxp (synCin (synC1st)
            (synCxp (synCima (synCcnv (synC2nd)) (synCsn (synC1c))) (synCvv)))
          (synCaddcfn)))
      p0116 p0127
  have p0129 :=
    @gRnex
      (synCtxp (synCcnv (synCrn (synCin (synCins3 (synCcnv (synCima (synCtxp (synCrn
                        (synCtxp (synCcnv (synC1st)) (synCin (synC1st) (synC2nd))))
                      (synC2nd)) (synCaddcfn)))) (synCima
                (synCtxp (synCcom (synC1st) (synC1st))
                  (synCtxp (synCcom (synC2nd) (synC1st)) (synC2nd))) (synCaddcfn)))))
        (synCrn (synCtxp (synCin (synC1st)
              (synCxp (synCima (synCcnv (synC2nd)) (synCsn (synC1c))) (synCvv)))
            (synCaddcfn))))
      p0128
  have p0130 :=
    @gUnex
      (synCrn (synCin (synCins3 (synCcnv (synCima (synCtxp (synCrn
                    (synCtxp (synCcnv (synC1st)) (synCin (synC1st) (synC2nd))))
                  (synC2nd)) (synCaddcfn)))) (synCima
            (synCtxp (synCcom (synC1st) (synC1st))
              (synCtxp (synCcom (synC2nd) (synC1st)) (synC2nd))) (synCaddcfn))))
      (synCrn (synCtxp (synCcnv (synCrn (synCin (synCins3 (synCcnv (synCima (synCtxp
                        (synCrn (synCtxp (synCcnv (synC1st))
                            (synCin (synC1st) (synC2nd)))) (synC2nd)) (synCaddcfn))))
                (synCima (synCtxp (synCcom (synC1st) (synC1st))
                    (synCtxp (synCcom (synC2nd) (synC1st)) (synC2nd))) (synCaddcfn)))))
          (synCrn (synCtxp (synCin (synC1st)
                (synCxp (synCima (synCcnv (synC2nd)) (synCsn (synC1c))) (synCvv)))
              (synCaddcfn)))))
      p0115 p0129
  have p0132 := @gSnex (synC2c)
  have p0133 := @gImaex (synCcnv (synC2nd)) (synCsn (synC2c)) p0119 p0132
  have p0135 :=
    @gXpex (synCima (synCcnv (synC2nd)) (synCsn (synC2c))) (synCvv) p0133 p0122
  have p0136 :=
    @gInex (synC1st)
      (synCxp (synCima (synCcnv (synC2nd)) (synCsn (synC2c))) (synCvv)) p0090 p0135
  have p0138 :=
    @gTxpex
      (synCin (synC1st)
        (synCxp (synCima (synCcnv (synC2nd)) (synCsn (synC2c))) (synCvv)))
      (synCaddcfn) p0136 p0099
  have p0139 :=
    @gRnex
      (synCtxp (synCin (synC1st)
          (synCxp (synCima (synCcnv (synC2nd)) (synCsn (synC2c))) (synCvv)))
        (synCaddcfn))
      p0138
  have p0140 :=
    @gTxpex
      (synCcnv (synCrn (synCin (synCins3 (synCcnv (synCima (synCtxp (synCrn
                      (synCtxp (synCcnv (synC1st)) (synCin (synC1st) (synC2nd))))
                    (synC2nd)) (synCaddcfn)))) (synCima
              (synCtxp (synCcom (synC1st) (synC1st))
                (synCtxp (synCcom (synC2nd) (synC1st)) (synC2nd))) (synCaddcfn)))))
      (synCrn (synCtxp (synCin (synC1st)
            (synCxp (synCima (synCcnv (synC2nd)) (synCsn (synC2c))) (synCvv)))
          (synCaddcfn)))
      p0116 p0139
  have p0141 :=
    @gRnex
      (synCtxp (synCcnv (synCrn (synCin (synCins3 (synCcnv (synCima (synCtxp (synCrn
                        (synCtxp (synCcnv (synC1st)) (synCin (synC1st) (synC2nd))))
                      (synC2nd)) (synCaddcfn)))) (synCima
                (synCtxp (synCcom (synC1st) (synC1st))
                  (synCtxp (synCcom (synC2nd) (synC1st)) (synC2nd))) (synCaddcfn)))))
        (synCrn (synCtxp (synCin (synC1st)
              (synCxp (synCima (synCcnv (synC2nd)) (synCsn (synC2c))) (synCvv)))
            (synCaddcfn))))
      p0140
  have p0142 :=
    @gUnex
      (synCun (synCrn (synCin (synCins3 (synCcnv (synCima (synCtxp (synCrn
                      (synCtxp (synCcnv (synC1st)) (synCin (synC1st) (synC2nd))))
                    (synC2nd)) (synCaddcfn)))) (synCima
              (synCtxp (synCcom (synC1st) (synC1st))
                (synCtxp (synCcom (synC2nd) (synC1st)) (synC2nd))) (synCaddcfn))))
        (synCrn (synCtxp (synCcnv (synCrn (synCin (synCins3 (synCcnv (synCima (synCtxp
                          (synCrn (synCtxp (synCcnv (synC1st))
                              (synCin (synC1st) (synC2nd)))) (synC2nd)) (synCaddcfn))))
                  (synCima (synCtxp (synCcom (synC1st) (synC1st))
                      (synCtxp (synCcom (synC2nd) (synC1st)) (synC2nd))) (synCaddcfn)))))
            (synCrn (synCtxp (synCin (synC1st)
                  (synCxp (synCima (synCcnv (synC2nd)) (synCsn (synC1c))) (synCvv)))
                (synCaddcfn))))))
      (synCrn (synCtxp (synCcnv (synCrn (synCin (synCins3 (synCcnv (synCima (synCtxp
                        (synCrn (synCtxp (synCcnv (synC1st))
                            (synCin (synC1st) (synC2nd)))) (synC2nd)) (synCaddcfn))))
                (synCima (synCtxp (synCcom (synC1st) (synC1st))
                    (synCtxp (synCcom (synC2nd) (synC1st)) (synC2nd))) (synCaddcfn)))))
          (synCrn (synCtxp (synCin (synC1st)
                (synCxp (synCima (synCcnv (synC2nd)) (synCsn (synC2c))) (synCvv)))
              (synCaddcfn)))))
      p0130 p0141
  have p0143 := @gNncex
  have p0144 :=
    @gImaex
      (synCun (synCun (synCrn (synCin (synCins3 (synCcnv (synCima (synCtxp (synCrn
                        (synCtxp (synCcnv (synC1st)) (synCin (synC1st) (synC2nd))))
                      (synC2nd)) (synCaddcfn)))) (synCima
                (synCtxp (synCcom (synC1st) (synC1st))
                  (synCtxp (synCcom (synC2nd) (synC1st)) (synC2nd))) (synCaddcfn))))
          (synCrn (synCtxp (synCcnv (synCrn (synCin (synCins3 (synCcnv (synCima
                          (synCtxp (synCrn (synCtxp (synCcnv (synC1st))
                                (synCin (synC1st) (synC2nd)))) (synC2nd)) (synCaddcfn))))
                    (synCima (synCtxp (synCcom (synC1st) (synC1st))
                        (synCtxp (synCcom (synC2nd) (synC1st)) (synC2nd)))
                      (synCaddcfn))))) (synCrn (synCtxp (synCin (synC1st)
                    (synCxp (synCima (synCcnv (synC2nd)) (synCsn (synC1c))) (synCvv)))
                  (synCaddcfn)))))) (synCrn (synCtxp (synCcnv (synCrn (synCin (synCins3
                    (synCcnv (synCima (synCtxp (synCrn (synCtxp (synCcnv (synC1st))
                              (synCin (synC1st) (synC2nd)))) (synC2nd)) (synCaddcfn))))
                  (synCima (synCtxp (synCcom (synC1st) (synC1st))
                      (synCtxp (synCcom (synC2nd) (synC1st)) (synC2nd))) (synCaddcfn)))))
            (synCrn (synCtxp (synCin (synC1st)
                  (synCxp (synCima (synCcnv (synC2nd)) (synCsn (synC2c))) (synCvv)))
                (synCaddcfn))))))
      (synCnnc) p0142 p0143
  have p0145 :=
    @gEqeltrri
      (synCima (synCun (synCun (synCrn (synCin (synCins3 (synCcnv (synCima (synCtxp
                        (synCrn (synCtxp (synCcnv (synC1st))
                            (synCin (synC1st) (synC2nd)))) (synC2nd)) (synCaddcfn))))
                (synCima (synCtxp (synCcom (synC1st) (synC1st))
                    (synCtxp (synCcom (synC2nd) (synC1st)) (synC2nd))) (synCaddcfn))))
            (synCrn (synCtxp (synCcnv (synCrn (synCin (synCins3 (synCcnv (synCima
                            (synCtxp (synCrn (synCtxp (synCcnv (synC1st))
                                  (synCin (synC1st) (synC2nd)))) (synC2nd)) (synCaddcfn))))
                      (synCima (synCtxp (synCcom (synC1st) (synC1st))
                          (synCtxp (synCcom (synC2nd) (synC1st)) (synC2nd)))
                        (synCaddcfn))))) (synCrn (synCtxp (synCin (synC1st)
                      (synCxp (synCima (synCcnv (synC2nd)) (synCsn (synC1c))) (synCvv)))
                    (synCaddcfn)))))) (synCrn (synCtxp (synCcnv (synCrn (synCin (synCins3
                      (synCcnv (synCima (synCtxp (synCrn (synCtxp (synCcnv (synC1st))
                                (synCin (synC1st) (synC2nd)))) (synC2nd)) (synCaddcfn))))
                    (synCima (synCtxp (synCcom (synC1st) (synC1st))
                        (synCtxp (synCcom (synC2nd) (synC1st)) (synC2nd)))
                      (synCaddcfn))))) (synCrn (synCtxp (synCin (synC1st)
                    (synCxp (synCima (synCcnv (synC2nd)) (synCsn (synC2c))) (synCvv)))
                  (synCaddcfn)))))) (synCnnc))
      (.cab a (synWrex n (synCnnc)
          (synW3o (.classEq (.cv a) (synCplc (synCplc (.cv n) (.cv n)) (.cv n)))
            (.classEq (.cv a)
              (synCplc (synCplc (synCplc (.cv n) (.cv n)) (.cv n)) (synC1c)))
            (.classEq (.cv a)
              (synCplc (synCplc (synCplc (.cv n) (.cv n)) (.cv n)) (synC2c))))))
      (synCvv) p0089 p0144
  exact p0145


end NFChoice.DirectNominalPrf.WPPReplay

end

/-! Certificates from `NominalWPPReplayChunk013Compact001Part064`. -/


section

namespace NFChoice.DirectNominalPrf.WPPReplay

open scoped Fol
open NFChoice.Foundation
open NFChoice.SemanticCore
open NFChoice.ReplaySupport
open NFChoice.Compiler.CompactSourceSyntax

/-- Checked nominal proof certificate identified upstream as `g_nncdiv3`. -/
@[expose]
noncomputable def gNncdiv3 (A : Class) (n : Var) (dv_A_n : n ∉ A.fv) :
    Nominal.NPrf
      (.imp (.classMem A (synCnnc)) (synWrex n (synCnnc)
          (synW3o (.classEq A (synCplc (synCplc (.cv n) (.cv n)) (.cv n))) (.classEq A
              (synCplc (synCplc (synCplc (.cv n) (.cv n)) (.cv n)) (synC1c))) (.classEq A
              (synCplc (synCplc (synCplc (.cv n) (.cv n)) (.cv n)) (synC2c)))))) :=
  by
  let proofSupport : Finset Var := A.fv ∪ ({ n } : Finset Var)
  let a : Var := freshVar proofSupport 0
  let m : Var := freshVar proofSupport 1
  have fresh_a : a ∉ proofSupport :=
    by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_a_not_A : a ∉ A.fv := by
    intro h
    exact fresh_a (Finset.mem_union_left _ (h))
  have fresh_a_ne_n : a ≠ n := by
    intro h
    exact fresh_a (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))
  have fresh_n_ne_a : n ≠ a := Ne.symm fresh_a_ne_n
  have fresh_m : m ∉ proofSupport :=
    by
    change freshVar proofSupport 1 ∉ proofSupport
    exact freshVar_not_mem proofSupport 1
  have fresh_m_ne_n : m ≠ n := by
    intro h
    exact fresh_m (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))
  have fresh_n_ne_m : n ≠ m := Ne.symm fresh_m_ne_n
  have fresh_a_ne_m : a ≠ m :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have fresh_m_ne_a : m ≠ a := Ne.symm fresh_a_ne_m
  have dv_cache_0001 : a ≠ n := by exact (show a ≠ n from (by exact fresh_a_ne_n))
  have dv_cache_0002 : n ∉ ((Wff.classEq (.cv a) (synC0c))).fv :=
    by
    clear dv_cache_0001
    exact
      (by
        have compact_fv_not_mem_empty : n ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0c, Finset.mem_union,
          Finset.mem_singleton, fresh_n_ne_a, compact_fv_not_mem_empty, or_false,
          not_false_eq_true])
  have dv_cache_0003 : n ∉ ((Wff.objEq a m)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact
      (by
        have compact_fv_not_mem_empty : n ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_objEq, Finset.mem_insert,
          Finset.mem_singleton, fresh_n_ne_a, fresh_n_ne_m, or_false, not_false_eq_true])
  have dv_cache_0004 : n ∉ ((Wff.classEq (.cv a) (synCplc (.cv m) (synC1c)))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact
      (by
        have compact_fv_not_mem_empty : n ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cplc,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c, Finset.mem_union,
          Finset.mem_singleton, fresh_n_ne_a, fresh_n_ne_m, compact_fv_not_mem_empty,
          or_false, not_false_eq_true])
  have dv_cache_0005 : n ∉ ((Wff.classEq (.cv a) A)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact
      (by
        have compact_fv_not_mem_empty : n ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, fresh_n_ne_a, dv_A_n, or_false, not_false_eq_true])
  have dv_cache_0006 : n ∉ ((synC0c)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact
      (by
        have compact_fv_not_mem_empty : n ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0c,
          compact_fv_not_mem_empty, not_false_eq_true])
  have dv_cache_0007 : n ∉ ((synCnnc)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006
    exact
      (by
        have compact_fv_not_mem_empty : n ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc,
          compact_fv_not_mem_empty, not_false_eq_true])
  have dv_cache_0008 :
    n ∉
      ((synW3o (.classEq (synC0c) (synCplc (synCplc (synC0c) (synC0c)) (synC0c)))
          (.classEq (synC0c)
            (synCplc (synCplc (synCplc (synC0c) (synC0c)) (synC0c)) (synC1c)))
          (.classEq (synC0c) (synCplc (synCplc (synCplc (synC0c) (synC0c)) (synC0c))
              (synC2c))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007
    exact
      (by
        have compact_fv_not_mem_empty : n ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_w3o,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0c,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cplc,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c2c, Finset.mem_union,
          compact_fv_not_mem_empty, or_false, not_false_eq_true])
  have dv_cache_0009 : a ∉ ((synCplc (.cv n) (synC1c))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008
    exact
      (by
        have compact_fv_not_mem_empty : a ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cplc,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c, Finset.mem_union,
          Finset.mem_singleton, fresh_a_ne_n, compact_fv_not_mem_empty, or_false,
          not_false_eq_true])
  have dv_cache_0010 : a ∉ ((synCnnc)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009
    exact
      (by
        have compact_fv_not_mem_empty : a ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc,
          compact_fv_not_mem_empty, not_false_eq_true])
  have dv_cache_0011 :
    a ∉
      ((Wff.classEq (synCplc (synCplc (synCplc (synCplc (.cv n) (.cv n)) (.cv n)) (synC2c))
            (synC1c))
          (synCplc (synCplc (synCplc (.cv n) (synC1c)) (synCplc (.cv n) (synC1c)))
            (synCplc (.cv n) (synC1c))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010
    exact
      (by
        have compact_fv_not_mem_empty : a ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cplc,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c2c,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c, Finset.mem_union,
          Finset.mem_singleton, fresh_a_ne_n, compact_fv_not_mem_empty, or_false,
          not_false_eq_true])
  have dv_cache_0012 :
    a ∉
      ((Wff.classEq (.cv m)
          (synCplc (synCplc (synCplc (.cv n) (.cv n)) (.cv n)) (synC2c)))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
    exact
      (by
        have compact_fv_not_mem_empty : a ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cplc,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c2c, Finset.mem_union,
          Finset.mem_singleton, fresh_a_ne_m, fresh_a_ne_n, compact_fv_not_mem_empty,
          or_false, not_false_eq_true])
  have dv_cache_0013 :
    n ∉
      ((synWrex a (synCnnc) (.classEq (synCplc (.cv m) (synC1c))
            (synCplc (synCplc (.cv a) (.cv a)) (.cv a))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012
    exact
      (by
        have compact_fv_not_mem_empty : n ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wrex,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cplc,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c, Finset.mem_union,
          Finset.mem_erase, Finset.mem_singleton, fresh_n_ne_m, fresh_n_ne_a,
          compact_fv_not_mem_empty, or_false, and_false, not_false_eq_true])
  have dv_cache_0014 :
    n ∉
      ((Wff.classEq (synCplc (.cv m) (synC1c))
          (synCplc (synCplc (.cv a) (.cv a)) (.cv a)))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013
    exact
      (by
        have compact_fv_not_mem_empty : n ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cplc,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c, Finset.mem_union,
          Finset.mem_singleton, fresh_n_ne_m, fresh_n_ne_a, compact_fv_not_mem_empty,
          or_false, not_false_eq_true])
  have dv_cache_0015 :
    a ∉
      ((Wff.classEq (synCplc (.cv m) (synC1c))
          (synCplc (synCplc (.cv n) (.cv n)) (.cv n)))).fv :=
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
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cplc,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c, Finset.mem_union,
          Finset.mem_singleton, fresh_a_ne_m, fresh_a_ne_n, compact_fv_not_mem_empty,
          or_false, not_false_eq_true])
  have dv_cache_0016 : a ∉ (A).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015
    exact
      (by
        have compact_fv_not_mem_empty : a ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_a_not_A, not_false_eq_true])
  have dv_cache_0017 :
    a ∉
      ((synWrex n (synCnnc)
          (synW3o (.classEq (.cv m) (synCplc (synCplc (.cv n) (.cv n)) (.cv n)))
            (.classEq (.cv m)
              (synCplc (synCplc (synCplc (.cv n) (.cv n)) (.cv n)) (synC1c)))
            (.classEq (.cv m)
              (synCplc (synCplc (synCplc (.cv n) (.cv n)) (.cv n)) (synC2c)))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016
    exact
      (by
        have compact_fv_not_mem_empty : a ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wrex,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_w3o,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cplc,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c2c, Finset.mem_union,
          Finset.mem_erase, Finset.mem_singleton, fresh_a_ne_m, fresh_a_ne_n,
          compact_fv_not_mem_empty, or_false, and_false, not_false_eq_true])
  have dv_cache_0018 :
    m ∉
      ((synWrex n (synCnnc)
          (synW3o (.classEq (.cv a) (synCplc (synCplc (.cv n) (.cv n)) (.cv n)))
            (.classEq (.cv a)
              (synCplc (synCplc (synCplc (.cv n) (.cv n)) (.cv n)) (synC1c)))
            (.classEq (.cv a)
              (synCplc (synCplc (synCplc (.cv n) (.cv n)) (.cv n)) (synC2c)))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
    exact
      (by
        have compact_fv_not_mem_empty : m ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wrex,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_w3o,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cplc,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c2c, Finset.mem_union,
          Finset.mem_erase, Finset.mem_singleton, fresh_m_ne_a, fresh_m_ne_n,
          compact_fv_not_mem_empty, or_false, and_false, not_false_eq_true])
  have dv_cache_0019 :
    a ∉
      ((synWrex n (synCnnc)
          (synW3o (.classEq (synC0c) (synCplc (synCplc (.cv n) (.cv n)) (.cv n)))
            (.classEq (synC0c)
              (synCplc (synCplc (synCplc (.cv n) (.cv n)) (.cv n)) (synC1c)))
            (.classEq (synC0c)
              (synCplc (synCplc (synCplc (.cv n) (.cv n)) (.cv n)) (synC2c)))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018
    exact
      (by
        have compact_fv_not_mem_empty : a ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wrex,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_w3o,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0c,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cplc,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c2c, Finset.mem_union,
          Finset.mem_erase, Finset.mem_singleton, fresh_a_ne_n, compact_fv_not_mem_empty,
          or_false, and_false, not_false_eq_true])
  have dv_cache_0020 :
    a ∉
      ((synWrex n (synCnnc)
          (synW3o (.classEq A (synCplc (synCplc (.cv n) (.cv n)) (.cv n))) (.classEq A
              (synCplc (synCplc (synCplc (.cv n) (.cv n)) (.cv n)) (synC1c))) (.classEq A
              (synCplc (synCplc (synCplc (.cv n) (.cv n)) (.cv n)) (synC2c)))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019
    exact
      (by
        have compact_fv_not_mem_empty : a ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wrex,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_w3o,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cplc,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c2c, Finset.mem_union,
          Finset.mem_erase, Finset.mem_singleton, fresh_a_not_A, fresh_a_ne_n,
          compact_fv_not_mem_empty, or_false, and_false, not_false_eq_true])
  have dv_cache_0021 :
    a ∉
      ((synWrex n (synCnnc) (synW3o (.classEq (synCplc (.cv m) (synC1c))
              (synCplc (synCplc (.cv n) (.cv n)) (.cv n)))
            (.classEq (synCplc (.cv m) (synC1c))
              (synCplc (synCplc (synCplc (.cv n) (.cv n)) (.cv n)) (synC1c)))
            (.classEq (synCplc (.cv m) (synC1c))
              (synCplc (synCplc (synCplc (.cv n) (.cv n)) (.cv n)) (synC2c)))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020
    exact
      (by
        have compact_fv_not_mem_empty : a ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wrex,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_w3o,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cplc,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c2c, Finset.mem_union,
          Finset.mem_erase, Finset.mem_singleton, fresh_a_ne_m, fresh_a_ne_n,
          compact_fv_not_mem_empty, or_false, and_false, not_false_eq_true])
  have dv_cache_0022 : a ≠ m :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021
    exact (show a ≠ m from (by exact fresh_a_ne_m))
  have p0000 := @gNncdiv3lem2 n a dv_cache_0001
  have p0001 := @gEqeq1 (.cv a) (synC0c) (synCplc (synCplc (.cv n) (.cv n)) (.cv n))
  have p0002 :=
    @gEqeq1 (.cv a) (synC0c)
      (synCplc (synCplc (synCplc (.cv n) (.cv n)) (.cv n)) (synC1c))
  have p0003 :=
    @gEqeq1 (.cv a) (synC0c)
      (synCplc (synCplc (synCplc (.cv n) (.cv n)) (.cv n)) (synC2c))
  have p0004 :=
    @gN3orbi123d (.classEq (.cv a) (synC0c))
      (.classEq (.cv a) (synCplc (synCplc (.cv n) (.cv n)) (.cv n)))
      (.classEq (synC0c) (synCplc (synCplc (.cv n) (.cv n)) (.cv n)))
      (.classEq (.cv a) (synCplc (synCplc (synCplc (.cv n) (.cv n)) (.cv n)) (synC1c)))
      (.classEq (synC0c) (synCplc (synCplc (synCplc (.cv n) (.cv n)) (.cv n)) (synC1c)))
      (.classEq (.cv a) (synCplc (synCplc (synCplc (.cv n) (.cv n)) (.cv n)) (synC2c)))
      (.classEq (synC0c) (synCplc (synCplc (synCplc (.cv n) (.cv n)) (.cv n)) (synC2c)))
      p0001 p0002 p0003
  have p0005 :=
    @gRexbidv (.classEq (.cv a) (synC0c))
      (synW3o (.classEq (.cv a) (synCplc (synCplc (.cv n) (.cv n)) (.cv n)))
        (.classEq (.cv a) (synCplc (synCplc (synCplc (.cv n) (.cv n)) (.cv n)) (synC1c)))
        (.classEq (.cv a) (synCplc (synCplc (synCplc (.cv n) (.cv n)) (.cv n)) (synC2c))))
      (synW3o (.classEq (synC0c) (synCplc (synCplc (.cv n) (.cv n)) (.cv n)))
        (.classEq (synC0c) (synCplc (synCplc (synCplc (.cv n) (.cv n)) (.cv n)) (synC1c)))
        (.classEq (synC0c) (synCplc (synCplc (synCplc (.cv n) (.cv n)) (.cv n)) (synC2c))))
      n (synCnnc) dv_cache_0002 p0004
  have p0006 := @gEqeq1 (.cv a) (.cv m) (synCplc (synCplc (.cv n) (.cv n)) (.cv n))
  have p0007 :=
    @gEqeq1 (.cv a) (.cv m)
      (synCplc (synCplc (synCplc (.cv n) (.cv n)) (.cv n)) (synC1c))
  have p0008 :=
    @gEqeq1 (.cv a) (.cv m)
      (synCplc (synCplc (synCplc (.cv n) (.cv n)) (.cv n)) (synC2c))
  have p0009_e00_recanon :
    Nominal.NPrf
      (.imp (.objEq a m)
        (synWb (.classEq (.cv a) (synCplc (synCplc (.cv n) (.cv n)) (.cv n)))
          (.classEq (.cv m) (synCplc (synCplc (.cv n) (.cv n)) (.cv n))))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold synWb synCplc synWrex synWex synWa
        simp (config :=
          { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_class_cv]
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
        · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0006
  have p0009_e01_recanon :
    Nominal.NPrf
      (.imp (.objEq a m) (synWb (.classEq (.cv a)
            (synCplc (synCplc (synCplc (.cv n) (.cv n)) (.cv n)) (synC1c)))
          (.classEq (.cv m)
            (synCplc (synCplc (synCplc (.cv n) (.cv n)) (.cv n)) (synC1c))))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold synWb synCplc synWrex synWex synWa synC1c
        simp (config :=
          { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_class_cv]
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
        · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0007
  have p0009_e02_recanon :
    Nominal.NPrf
      (.imp (.objEq a m) (synWb (.classEq (.cv a)
            (synCplc (synCplc (synCplc (.cv n) (.cv n)) (.cv n)) (synC2c)))
          (.classEq (.cv m)
            (synCplc (synCplc (synCplc (.cv n) (.cv n)) (.cv n)) (synC2c))))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold synWb synCplc synWrex synWex synWa synC2c synCnc synCec synCima
          synCsn synCen synCopab synCpr synCun synCnin synWnan synCcompl synC0
          synCdif synCin synCvv
        simp (config :=
          { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_class_cv]
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
        · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0008
  have p0009 :=
    @gN3orbi123d (.objEq a m)
      (.classEq (.cv a) (synCplc (synCplc (.cv n) (.cv n)) (.cv n)))
      (.classEq (.cv m) (synCplc (synCplc (.cv n) (.cv n)) (.cv n)))
      (.classEq (.cv a) (synCplc (synCplc (synCplc (.cv n) (.cv n)) (.cv n)) (synC1c)))
      (.classEq (.cv m) (synCplc (synCplc (synCplc (.cv n) (.cv n)) (.cv n)) (synC1c)))
      (.classEq (.cv a) (synCplc (synCplc (synCplc (.cv n) (.cv n)) (.cv n)) (synC2c)))
      (.classEq (.cv m) (synCplc (synCplc (synCplc (.cv n) (.cv n)) (.cv n)) (synC2c)))
      p0009_e00_recanon p0009_e01_recanon p0009_e02_recanon
  have p0010 :=
    @gRexbidv (.objEq a m)
      (synW3o (.classEq (.cv a) (synCplc (synCplc (.cv n) (.cv n)) (.cv n)))
        (.classEq (.cv a) (synCplc (synCplc (synCplc (.cv n) (.cv n)) (.cv n)) (synC1c)))
        (.classEq (.cv a) (synCplc (synCplc (synCplc (.cv n) (.cv n)) (.cv n)) (synC2c))))
      (synW3o (.classEq (.cv m) (synCplc (synCplc (.cv n) (.cv n)) (.cv n)))
        (.classEq (.cv m) (synCplc (synCplc (synCplc (.cv n) (.cv n)) (.cv n)) (synC1c)))
        (.classEq (.cv m) (synCplc (synCplc (synCplc (.cv n) (.cv n)) (.cv n)) (synC2c))))
      n (synCnnc) dv_cache_0003 p0009
  have p0011 :=
    @gEqeq1 (.cv a) (synCplc (.cv m) (synC1c))
      (synCplc (synCplc (.cv n) (.cv n)) (.cv n))
  have p0012 :=
    @gEqeq1 (.cv a) (synCplc (.cv m) (synC1c))
      (synCplc (synCplc (synCplc (.cv n) (.cv n)) (.cv n)) (synC1c))
  have p0013 :=
    @gEqeq1 (.cv a) (synCplc (.cv m) (synC1c))
      (synCplc (synCplc (synCplc (.cv n) (.cv n)) (.cv n)) (synC2c))
  have p0014 :=
    @gN3orbi123d (.classEq (.cv a) (synCplc (.cv m) (synC1c)))
      (.classEq (.cv a) (synCplc (synCplc (.cv n) (.cv n)) (.cv n)))
      (.classEq (synCplc (.cv m) (synC1c)) (synCplc (synCplc (.cv n) (.cv n)) (.cv n)))
      (.classEq (.cv a) (synCplc (synCplc (synCplc (.cv n) (.cv n)) (.cv n)) (synC1c)))
      (.classEq (synCplc (.cv m) (synC1c))
        (synCplc (synCplc (synCplc (.cv n) (.cv n)) (.cv n)) (synC1c)))
      (.classEq (.cv a) (synCplc (synCplc (synCplc (.cv n) (.cv n)) (.cv n)) (synC2c)))
      (.classEq (synCplc (.cv m) (synC1c))
        (synCplc (synCplc (synCplc (.cv n) (.cv n)) (.cv n)) (synC2c)))
      p0011 p0012 p0013
  have p0015 :=
    @gRexbidv (.classEq (.cv a) (synCplc (.cv m) (synC1c)))
      (synW3o (.classEq (.cv a) (synCplc (synCplc (.cv n) (.cv n)) (.cv n)))
        (.classEq (.cv a) (synCplc (synCplc (synCplc (.cv n) (.cv n)) (.cv n)) (synC1c)))
        (.classEq (.cv a) (synCplc (synCplc (synCplc (.cv n) (.cv n)) (.cv n)) (synC2c))))
      (synW3o (.classEq (synCplc (.cv m) (synC1c))
          (synCplc (synCplc (.cv n) (.cv n)) (.cv n))) (.classEq (synCplc (.cv m) (synC1c))
          (synCplc (synCplc (synCplc (.cv n) (.cv n)) (.cv n)) (synC1c)))
        (.classEq (synCplc (.cv m) (synC1c))
          (synCplc (synCplc (synCplc (.cv n) (.cv n)) (.cv n)) (synC2c))))
      n (synCnnc) dv_cache_0004 p0014
  have p0016 := @gEqeq1 (.cv a) A (synCplc (synCplc (.cv n) (.cv n)) (.cv n))
  have p0017 :=
    @gEqeq1 (.cv a) A (synCplc (synCplc (synCplc (.cv n) (.cv n)) (.cv n)) (synC1c))
  have p0018 :=
    @gEqeq1 (.cv a) A (synCplc (synCplc (synCplc (.cv n) (.cv n)) (.cv n)) (synC2c))
  have p0019 :=
    @gN3orbi123d (.classEq (.cv a) A)
      (.classEq (.cv a) (synCplc (synCplc (.cv n) (.cv n)) (.cv n)))
      (.classEq A (synCplc (synCplc (.cv n) (.cv n)) (.cv n)))
      (.classEq (.cv a) (synCplc (synCplc (synCplc (.cv n) (.cv n)) (.cv n)) (synC1c)))
      (.classEq A (synCplc (synCplc (synCplc (.cv n) (.cv n)) (.cv n)) (synC1c)))
      (.classEq (.cv a) (synCplc (synCplc (synCplc (.cv n) (.cv n)) (.cv n)) (synC2c)))
      (.classEq A (synCplc (synCplc (synCplc (.cv n) (.cv n)) (.cv n)) (synC2c)))
      p0016 p0017 p0018
  have p0020 :=
    @gRexbidv (.classEq (.cv a) A)
      (synW3o (.classEq (.cv a) (synCplc (synCplc (.cv n) (.cv n)) (.cv n)))
        (.classEq (.cv a) (synCplc (synCplc (synCplc (.cv n) (.cv n)) (.cv n)) (synC1c)))
        (.classEq (.cv a) (synCplc (synCplc (synCplc (.cv n) (.cv n)) (.cv n)) (synC2c))))
      (synW3o (.classEq A (synCplc (synCplc (.cv n) (.cv n)) (.cv n)))
        (.classEq A (synCplc (synCplc (synCplc (.cv n) (.cv n)) (.cv n)) (synC1c)))
        (.classEq A (synCplc (synCplc (synCplc (.cv n) (.cv n)) (.cv n)) (synC2c))))
      n (synCnnc) dv_cache_0005 p0019
  have p0021 := @gPeano1
  have p0022 := @gAddcid1 (synCplc (synC0c) (synC0c))
  have p0023 := @gAddcid2 (synC0c)
  have p0024 :=
    @gEqtr2i (synCplc (synCplc (synC0c) (synC0c)) (synC0c))
      (synCplc (synC0c) (synC0c)) (synC0c) p0022 p0023
  have p0025 :=
    @gN3mix1 (.classEq (synC0c) (synCplc (synCplc (synC0c) (synC0c)) (synC0c)))
      (.classEq (synC0c)
        (synCplc (synCplc (synCplc (synC0c) (synC0c)) (synC0c)) (synC1c)))
      (.classEq (synC0c)
        (synCplc (synCplc (synCplc (synC0c) (synC0c)) (synC0c)) (synC2c)))
  have p0026 := Nominal.mp p0024 p0025
  have p0027 := @gAddceq12 (.cv n) (.cv n) (synC0c) (synC0c)
  have p0028 :=
    @gAnidms (.classEq (.cv n) (synC0c))
      (.classEq (synCplc (.cv n) (.cv n)) (synCplc (synC0c) (synC0c))) p0027
  have p0029 := @gId (.classEq (.cv n) (synC0c))
  have p0030 :=
    @gAddceq12d (.classEq (.cv n) (synC0c)) (synCplc (.cv n) (.cv n))
      (synCplc (synC0c) (synC0c)) (.cv n) (synC0c) p0028 p0029
  have p0031 :=
    @gEqeq2d (.classEq (.cv n) (synC0c)) (synCplc (synCplc (.cv n) (.cv n)) (.cv n))
      (synCplc (synCplc (synC0c) (synC0c)) (synC0c)) (synC0c) p0030
  have p0032 :=
    @gAddceq1d (.classEq (.cv n) (synC0c)) (synCplc (synCplc (.cv n) (.cv n)) (.cv n))
      (synCplc (synCplc (synC0c) (synC0c)) (synC0c)) (synC1c) p0030
  have p0033 :=
    @gEqeq2d (.classEq (.cv n) (synC0c))
      (synCplc (synCplc (synCplc (.cv n) (.cv n)) (.cv n)) (synC1c))
      (synCplc (synCplc (synCplc (synC0c) (synC0c)) (synC0c)) (synC1c)) (synC0c)
      p0032
  have p0034 :=
    @gAddceq1d (.classEq (.cv n) (synC0c)) (synCplc (synCplc (.cv n) (.cv n)) (.cv n))
      (synCplc (synCplc (synC0c) (synC0c)) (synC0c)) (synC2c) p0030
  have p0035 :=
    @gEqeq2d (.classEq (.cv n) (synC0c))
      (synCplc (synCplc (synCplc (.cv n) (.cv n)) (.cv n)) (synC2c))
      (synCplc (synCplc (synCplc (synC0c) (synC0c)) (synC0c)) (synC2c)) (synC0c)
      p0034
  have p0036 :=
    @gN3orbi123d (.classEq (.cv n) (synC0c))
      (.classEq (synC0c) (synCplc (synCplc (.cv n) (.cv n)) (.cv n)))
      (.classEq (synC0c) (synCplc (synCplc (synC0c) (synC0c)) (synC0c)))
      (.classEq (synC0c) (synCplc (synCplc (synCplc (.cv n) (.cv n)) (.cv n)) (synC1c)))
      (.classEq (synC0c)
        (synCplc (synCplc (synCplc (synC0c) (synC0c)) (synC0c)) (synC1c)))
      (.classEq (synC0c) (synCplc (synCplc (synCplc (.cv n) (.cv n)) (.cv n)) (synC2c)))
      (.classEq (synC0c)
        (synCplc (synCplc (synCplc (synC0c) (synC0c)) (synC0c)) (synC2c)))
      p0031 p0033 p0035
  have p0037 :=
    @gRspcev
      (synW3o (.classEq (synC0c) (synCplc (synCplc (.cv n) (.cv n)) (.cv n)))
        (.classEq (synC0c) (synCplc (synCplc (synCplc (.cv n) (.cv n)) (.cv n)) (synC1c)))
        (.classEq (synC0c) (synCplc (synCplc (synCplc (.cv n) (.cv n)) (.cv n)) (synC2c))))
      (synW3o (.classEq (synC0c) (synCplc (synCplc (synC0c) (synC0c)) (synC0c)))
        (.classEq (synC0c)
          (synCplc (synCplc (synCplc (synC0c) (synC0c)) (synC0c)) (synC1c)))
        (.classEq (synC0c)
          (synCplc (synCplc (synCplc (synC0c) (synC0c)) (synC0c)) (synC2c))))
      n (synC0c) (synCnnc) dv_cache_0006 dv_cache_0007 dv_cache_0008 p0036
  have p0038 :=
    @gMp2an (.classMem (synC0c) (synCnnc))
      (synW3o (.classEq (synC0c) (synCplc (synCplc (synC0c) (synC0c)) (synC0c)))
        (.classEq (synC0c)
          (synCplc (synCplc (synCplc (synC0c) (synC0c)) (synC0c)) (synC1c)))
        (.classEq (synC0c)
          (synCplc (synCplc (synCplc (synC0c) (synC0c)) (synC0c)) (synC2c))))
      (synWrex n (synCnnc)
        (synW3o (.classEq (synC0c) (synCplc (synCplc (.cv n) (.cv n)) (.cv n)))
          (.classEq (synC0c)
            (synCplc (synCplc (synCplc (.cv n) (.cv n)) (.cv n)) (synC1c)))
          (.classEq (synC0c)
            (synCplc (synCplc (synCplc (.cv n) (.cv n)) (.cv n)) (synC2c)))))
      p0021 p0026 p0037
  have p0039 := @gAddceq1 (.cv m) (synCplc (synCplc (.cv n) (.cv n)) (.cv n)) (synC1c)
  have p0040 :=
    @gReximi (.classEq (.cv m) (synCplc (synCplc (.cv n) (.cv n)) (.cv n)))
      (.classEq (synCplc (.cv m) (synC1c))
        (synCplc (synCplc (synCplc (.cv n) (.cv n)) (.cv n)) (synC1c)))
      n (synCnnc) p0039
  have p0041 :=
    @gA1i
      (.imp (synWrex n (synCnnc)
          (.classEq (.cv m) (synCplc (synCplc (.cv n) (.cv n)) (.cv n))))
        (synWrex n (synCnnc) (.classEq (synCplc (.cv m) (synC1c))
            (synCplc (synCplc (synCplc (.cv n) (.cv n)) (.cv n)) (synC1c)))))
      (.classMem (.cv m) (synCnnc)) p0040
  have p0042 :=
    @gAddceq1 (.cv m) (synCplc (synCplc (synCplc (.cv n) (.cv n)) (.cv n)) (synC1c))
      (synC1c)
  have p0043 :=
    @gAddcass (synCplc (synCplc (.cv n) (.cv n)) (.cv n)) (synC1c) (synC1c)
  have p0044 := @gN1p1e2c
  have p0045 :=
    @gAddceq2i (synCplc (synC1c) (synC1c)) (synC2c)
      (synCplc (synCplc (.cv n) (.cv n)) (.cv n)) p0044
  have p0046 :=
    @gEqtri
      (synCplc (synCplc (synCplc (synCplc (.cv n) (.cv n)) (.cv n)) (synC1c)) (synC1c))
      (synCplc (synCplc (synCplc (.cv n) (.cv n)) (.cv n)) (synCplc (synC1c) (synC1c)))
      (synCplc (synCplc (synCplc (.cv n) (.cv n)) (.cv n)) (synC2c)) p0043 p0045
  have p0047 :=
    @gSyl6eq
      (.classEq (.cv m) (synCplc (synCplc (synCplc (.cv n) (.cv n)) (.cv n)) (synC1c)))
      (synCplc (.cv m) (synC1c))
      (synCplc (synCplc (synCplc (synCplc (.cv n) (.cv n)) (.cv n)) (synC1c)) (synC1c))
      (synCplc (synCplc (synCplc (.cv n) (.cv n)) (.cv n)) (synC2c)) p0042 p0046
  have p0048 :=
    @gReximi
      (.classEq (.cv m) (synCplc (synCplc (synCplc (.cv n) (.cv n)) (.cv n)) (synC1c)))
      (.classEq (synCplc (.cv m) (synC1c))
        (synCplc (synCplc (synCplc (.cv n) (.cv n)) (.cv n)) (synC2c)))
      n (synCnnc) p0047
  have p0049 :=
    @gA1i
      (.imp (synWrex n (synCnnc) (.classEq (.cv m)
            (synCplc (synCplc (synCplc (.cv n) (.cv n)) (.cv n)) (synC1c))))
        (synWrex n (synCnnc) (.classEq (synCplc (.cv m) (synC1c))
            (synCplc (synCplc (synCplc (.cv n) (.cv n)) (.cv n)) (synC2c)))))
      (.classMem (.cv m) (synCnnc)) p0048
  have p0050 := @gPeano2 (.cv n)
  have p0051 := @gAddc32 (synCplc (.cv n) (.cv n)) (.cv n) (synC2c)
  have p0053 :=
    @gAddceq2i (synCplc (synC1c) (synC1c)) (synC2c) (synCplc (.cv n) (.cv n)) p0044
  have p0054 := @gAddc4 (.cv n) (.cv n) (synC1c) (synC1c)
  have p0055 :=
    @gEqtr3i (synCplc (synCplc (.cv n) (.cv n)) (synCplc (synC1c) (synC1c)))
      (synCplc (synCplc (.cv n) (.cv n)) (synC2c))
      (synCplc (synCplc (.cv n) (synC1c)) (synCplc (.cv n) (synC1c))) p0053 p0054
  have p0056 :=
    @gAddceq1i (synCplc (synCplc (.cv n) (.cv n)) (synC2c))
      (synCplc (synCplc (.cv n) (synC1c)) (synCplc (.cv n) (synC1c))) (.cv n) p0055
  have p0057 :=
    @gEqtri (synCplc (synCplc (synCplc (.cv n) (.cv n)) (.cv n)) (synC2c))
      (synCplc (synCplc (synCplc (.cv n) (.cv n)) (synC2c)) (.cv n))
      (synCplc (synCplc (synCplc (.cv n) (synC1c)) (synCplc (.cv n) (synC1c))) (.cv n))
      p0051 p0056
  have p0058 :=
    @gAddceq1i (synCplc (synCplc (synCplc (.cv n) (.cv n)) (.cv n)) (synC2c))
      (synCplc (synCplc (synCplc (.cv n) (synC1c)) (synCplc (.cv n) (synC1c))) (.cv n))
      (synC1c) p0057
  have p0059 :=
    @gAddcass (synCplc (synCplc (.cv n) (synC1c)) (synCplc (.cv n) (synC1c)))
      (.cv n) (synC1c)
  have p0060 :=
    @gEqtri
      (synCplc (synCplc (synCplc (synCplc (.cv n) (.cv n)) (.cv n)) (synC2c)) (synC1c))
      (synCplc (synCplc (synCplc (synCplc (.cv n) (synC1c)) (synCplc (.cv n) (synC1c)))
          (.cv n)) (synC1c))
      (synCplc (synCplc (synCplc (.cv n) (synC1c)) (synCplc (.cv n) (synC1c)))
        (synCplc (.cv n) (synC1c)))
      p0058 p0059
  have p0061 :=
    @gAddceq12 (.cv a) (.cv a) (synCplc (.cv n) (synC1c)) (synCplc (.cv n) (synC1c))
  have p0062 :=
    @gAnidms (.classEq (.cv a) (synCplc (.cv n) (synC1c)))
      (.classEq (synCplc (.cv a) (.cv a))
        (synCplc (synCplc (.cv n) (synC1c)) (synCplc (.cv n) (synC1c))))
      p0061
  have p0063 := @gId (.classEq (.cv a) (synCplc (.cv n) (synC1c)))
  have p0064 :=
    @gAddceq12d (.classEq (.cv a) (synCplc (.cv n) (synC1c)))
      (synCplc (.cv a) (.cv a))
      (synCplc (synCplc (.cv n) (synC1c)) (synCplc (.cv n) (synC1c))) (.cv a)
      (synCplc (.cv n) (synC1c)) p0062 p0063
  have p0065 :=
    @gEqeq2d (.classEq (.cv a) (synCplc (.cv n) (synC1c)))
      (synCplc (synCplc (.cv a) (.cv a)) (.cv a))
      (synCplc (synCplc (synCplc (.cv n) (synC1c)) (synCplc (.cv n) (synC1c)))
        (synCplc (.cv n) (synC1c)))
      (synCplc (synCplc (synCplc (synCplc (.cv n) (.cv n)) (.cv n)) (synC2c)) (synC1c))
      p0064
  have p0066 :=
    @gRspcev
      (.classEq (synCplc (synCplc (synCplc (synCplc (.cv n) (.cv n)) (.cv n)) (synC2c))
          (synC1c)) (synCplc (synCplc (.cv a) (.cv a)) (.cv a)))
      (.classEq (synCplc (synCplc (synCplc (synCplc (.cv n) (.cv n)) (.cv n)) (synC2c))
          (synC1c))
        (synCplc (synCplc (synCplc (.cv n) (synC1c)) (synCplc (.cv n) (synC1c)))
          (synCplc (.cv n) (synC1c))))
      a (synCplc (.cv n) (synC1c)) (synCnnc) dv_cache_0009 dv_cache_0010 dv_cache_0011
      p0065
  have p0067 :=
    @gSylancl (.classMem (.cv n) (synCnnc))
      (.classMem (synCplc (.cv n) (synC1c)) (synCnnc))
      (.classEq (synCplc (synCplc (synCplc (synCplc (.cv n) (.cv n)) (.cv n)) (synC2c))
          (synC1c))
        (synCplc (synCplc (synCplc (.cv n) (synC1c)) (synCplc (.cv n) (synC1c)))
          (synCplc (.cv n) (synC1c))))
      (synWrex a (synCnnc) (.classEq
          (synCplc (synCplc (synCplc (synCplc (.cv n) (.cv n)) (.cv n)) (synC2c))
            (synC1c)) (synCplc (synCplc (.cv a) (.cv a)) (.cv a))))
      p0050 p0060 p0066
  have p0068 :=
    @gAddceq1 (.cv m) (synCplc (synCplc (synCplc (.cv n) (.cv n)) (.cv n)) (synC2c))
      (synC1c)
  have p0069 :=
    @gEqeq1d
      (.classEq (.cv m) (synCplc (synCplc (synCplc (.cv n) (.cv n)) (.cv n)) (synC2c)))
      (synCplc (.cv m) (synC1c))
      (synCplc (synCplc (synCplc (synCplc (.cv n) (.cv n)) (.cv n)) (synC2c)) (synC1c))
      (synCplc (synCplc (.cv a) (.cv a)) (.cv a)) p0068
  have p0070 :=
    @gRexbidv
      (.classEq (.cv m) (synCplc (synCplc (synCplc (.cv n) (.cv n)) (.cv n)) (synC2c)))
      (.classEq (synCplc (.cv m) (synC1c)) (synCplc (synCplc (.cv a) (.cv a)) (.cv a)))
      (.classEq (synCplc (synCplc (synCplc (synCplc (.cv n) (.cv n)) (.cv n)) (synC2c))
          (synC1c)) (synCplc (synCplc (.cv a) (.cv a)) (.cv a)))
      a (synCnnc) dv_cache_0012 p0069
  have p0071 :=
    @gSyl5ibrcom (.classMem (.cv n) (synCnnc))
      (synWrex a (synCnnc) (.classEq (synCplc (.cv m) (synC1c))
          (synCplc (synCplc (.cv a) (.cv a)) (.cv a))))
      (.classEq (.cv m) (synCplc (synCplc (synCplc (.cv n) (.cv n)) (.cv n)) (synC2c)))
      (synWrex a (synCnnc) (.classEq
          (synCplc (synCplc (synCplc (synCplc (.cv n) (.cv n)) (.cv n)) (synC2c))
            (synC1c)) (synCplc (synCplc (.cv a) (.cv a)) (.cv a))))
      p0067 p0070
  have p0072 :=
    @gRexlimiv
      (.classEq (.cv m) (synCplc (synCplc (synCplc (.cv n) (.cv n)) (.cv n)) (synC2c)))
      (synWrex a (synCnnc) (.classEq (synCplc (.cv m) (synC1c))
          (synCplc (synCplc (.cv a) (.cv a)) (.cv a))))
      n (synCnnc) dv_cache_0013 p0071
  have p0073 := @gAddceq12 (.cv a) (.cv a) (.cv n) (.cv n)
  have p0074_e00_recanon :
    Nominal.NPrf
      (.imp (synWa (.objEq a n) (.objEq a n))
        (.classEq (synCplc (.cv a) (.cv a)) (synCplc (.cv n) (.cv n)))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold synWa synCplc synWrex synWex
        simp (config :=
          { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_class_cv]
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · apply Nominal.RecanonTransportDev.TRecanonWff.neg
          apply Nominal.RecanonTransportDev.TRecanonWff.imp
          · exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
          · apply Nominal.RecanonTransportDev.TRecanonWff.neg
            exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
        · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0073
  have p0074 :=
    @gAnidms (.objEq a n)
      (.classEq (synCplc (.cv a) (.cv a)) (synCplc (.cv n) (.cv n))) p0074_e00_recanon
  have p0075 := @gId (.objEq a n)
  have p0076_e01_recanon : Nominal.NPrf (.imp (.objEq a n) (.classEq (.cv a) (.cv n))) :=
    Nominal.RecanonTransportDev.transport
      (by
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · exact Nominal.RecanonTransportDev.TRecanonWff.same _
        · exact Nominal.RecanonTransportDev.TRecanonWff.objEq_classEq _ _)
      p0075
  have p0076 :=
    @gAddceq12d (.objEq a n) (synCplc (.cv a) (.cv a)) (synCplc (.cv n) (.cv n))
      (.cv a) (.cv n) p0074 p0076_e01_recanon
  have p0077 :=
    @gEqeq2d (.objEq a n) (synCplc (synCplc (.cv a) (.cv a)) (.cv a))
      (synCplc (synCplc (.cv n) (.cv n)) (.cv n)) (synCplc (.cv m) (synC1c)) p0076
  have p0078 :=
    @gCbvrexv
      (.classEq (synCplc (.cv m) (synC1c)) (synCplc (synCplc (.cv a) (.cv a)) (.cv a)))
      (.classEq (synCplc (.cv m) (synC1c)) (synCplc (synCplc (.cv n) (.cv n)) (.cv n)))
      a n (synCnnc) dv_cache_0010 dv_cache_0007 dv_cache_0014 dv_cache_0015 p0077
  have p0079 :=
    @gSylib
      (synWrex n (synCnnc) (.classEq (.cv m)
          (synCplc (synCplc (synCplc (.cv n) (.cv n)) (.cv n)) (synC2c))))
      (synWrex a (synCnnc) (.classEq (synCplc (.cv m) (synC1c))
          (synCplc (synCplc (.cv a) (.cv a)) (.cv a))))
      (synWrex n (synCnnc) (.classEq (synCplc (.cv m) (synC1c))
          (synCplc (synCplc (.cv n) (.cv n)) (.cv n))))
      p0072 p0078
  have p0080 :=
    @gA1i
      (.imp (synWrex n (synCnnc) (.classEq (.cv m)
            (synCplc (synCplc (synCplc (.cv n) (.cv n)) (.cv n)) (synC2c))))
        (synWrex n (synCnnc) (.classEq (synCplc (.cv m) (synC1c))
            (synCplc (synCplc (.cv n) (.cv n)) (.cv n)))))
      (.classMem (.cv m) (synCnnc)) p0079
  have p0081 :=
    @gN3orim123d (.classMem (.cv m) (synCnnc))
      (synWrex n (synCnnc) (.classEq (.cv m) (synCplc (synCplc (.cv n) (.cv n)) (.cv n))))
      (synWrex n (synCnnc) (.classEq (synCplc (.cv m) (synC1c))
          (synCplc (synCplc (synCplc (.cv n) (.cv n)) (.cv n)) (synC1c))))
      (synWrex n (synCnnc) (.classEq (.cv m)
          (synCplc (synCplc (synCplc (.cv n) (.cv n)) (.cv n)) (synC1c))))
      (synWrex n (synCnnc) (.classEq (synCplc (.cv m) (synC1c))
          (synCplc (synCplc (synCplc (.cv n) (.cv n)) (.cv n)) (synC2c))))
      (synWrex n (synCnnc) (.classEq (.cv m)
          (synCplc (synCplc (synCplc (.cv n) (.cv n)) (.cv n)) (synC2c))))
      (synWrex n (synCnnc) (.classEq (synCplc (.cv m) (synC1c))
          (synCplc (synCplc (.cv n) (.cv n)) (.cv n))))
      p0041 p0049 p0080
  have p0082 :=
    (Nominal.biimpRefl (synW3o (.classEq (.cv m) (synCplc (synCplc (.cv n) (.cv n)) (.cv n)))
        (.classEq (.cv m) (synCplc (synCplc (synCplc (.cv n) (.cv n)) (.cv n)) (synC1c)))
        (.classEq (.cv m) (synCplc (synCplc (synCplc (.cv n) (.cv n)) (.cv n)) (synC2c)))))
  have p0083 :=
    @gRexbii
      (synW3o (.classEq (.cv m) (synCplc (synCplc (.cv n) (.cv n)) (.cv n)))
        (.classEq (.cv m) (synCplc (synCplc (synCplc (.cv n) (.cv n)) (.cv n)) (synC1c)))
        (.classEq (.cv m) (synCplc (synCplc (synCplc (.cv n) (.cv n)) (.cv n)) (synC2c))))
      (synWo (synWo (.classEq (.cv m) (synCplc (synCplc (.cv n) (.cv n)) (.cv n)))
          (.classEq (.cv m) (synCplc (synCplc (synCplc (.cv n) (.cv n)) (.cv n)) (synC1c))))
        (.classEq (.cv m) (synCplc (synCplc (synCplc (.cv n) (.cv n)) (.cv n)) (synC2c))))
      n (synCnnc) p0082
  have p0084 :=
    @gR1943 (.classEq (.cv m) (synCplc (synCplc (.cv n) (.cv n)) (.cv n)))
      (.classEq (.cv m) (synCplc (synCplc (synCplc (.cv n) (.cv n)) (.cv n)) (synC1c)))
      n (synCnnc)
  have p0085 :=
    @gOrbi1i
      (synWrex n (synCnnc)
        (synWo (.classEq (.cv m) (synCplc (synCplc (.cv n) (.cv n)) (.cv n)))
          (.classEq (.cv m)
            (synCplc (synCplc (synCplc (.cv n) (.cv n)) (.cv n)) (synC1c)))))
      (synWo (synWrex n (synCnnc)
          (.classEq (.cv m) (synCplc (synCplc (.cv n) (.cv n)) (.cv n))))
        (synWrex n (synCnnc) (.classEq (.cv m)
            (synCplc (synCplc (synCplc (.cv n) (.cv n)) (.cv n)) (synC1c)))))
      (synWrex n (synCnnc) (.classEq (.cv m)
          (synCplc (synCplc (synCplc (.cv n) (.cv n)) (.cv n)) (synC2c))))
      p0084
  have p0086 :=
    @gR1943
      (synWo (.classEq (.cv m) (synCplc (synCplc (.cv n) (.cv n)) (.cv n))) (.classEq (.cv m)
          (synCplc (synCplc (synCplc (.cv n) (.cv n)) (.cv n)) (synC1c))))
      (.classEq (.cv m) (synCplc (synCplc (synCplc (.cv n) (.cv n)) (.cv n)) (synC2c)))
      n (synCnnc)
  have p0087 :=
    (Nominal.biimpRefl (synW3o (synWrex n (synCnnc)
          (.classEq (.cv m) (synCplc (synCplc (.cv n) (.cv n)) (.cv n))))
        (synWrex n (synCnnc) (.classEq (.cv m)
            (synCplc (synCplc (synCplc (.cv n) (.cv n)) (.cv n)) (synC1c))))
        (synWrex n (synCnnc) (.classEq (.cv m)
            (synCplc (synCplc (synCplc (.cv n) (.cv n)) (.cv n)) (synC2c))))))
  have p0088 :=
    @gN3bitr4i
      (synWo (synWrex n (synCnnc)
          (synWo (.classEq (.cv m) (synCplc (synCplc (.cv n) (.cv n)) (.cv n)))
            (.classEq (.cv m)
              (synCplc (synCplc (synCplc (.cv n) (.cv n)) (.cv n)) (synC1c)))))
        (synWrex n (synCnnc) (.classEq (.cv m)
            (synCplc (synCplc (synCplc (.cv n) (.cv n)) (.cv n)) (synC2c)))))
      (synWo (synWo (synWrex n (synCnnc)
            (.classEq (.cv m) (synCplc (synCplc (.cv n) (.cv n)) (.cv n))))
          (synWrex n (synCnnc) (.classEq (.cv m)
              (synCplc (synCplc (synCplc (.cv n) (.cv n)) (.cv n)) (synC1c)))))
        (synWrex n (synCnnc) (.classEq (.cv m)
            (synCplc (synCplc (synCplc (.cv n) (.cv n)) (.cv n)) (synC2c)))))
      (synWrex n (synCnnc) (synWo
          (synWo (.classEq (.cv m) (synCplc (synCplc (.cv n) (.cv n)) (.cv n)))
            (.classEq (.cv m)
              (synCplc (synCplc (synCplc (.cv n) (.cv n)) (.cv n)) (synC1c))))
          (.classEq (.cv m)
            (synCplc (synCplc (synCplc (.cv n) (.cv n)) (.cv n)) (synC2c)))))
      (synW3o (synWrex n (synCnnc)
          (.classEq (.cv m) (synCplc (synCplc (.cv n) (.cv n)) (.cv n))))
        (synWrex n (synCnnc) (.classEq (.cv m)
            (synCplc (synCplc (synCplc (.cv n) (.cv n)) (.cv n)) (synC1c))))
        (synWrex n (synCnnc) (.classEq (.cv m)
            (synCplc (synCplc (synCplc (.cv n) (.cv n)) (.cv n)) (synC2c)))))
      p0085 p0086 p0087
  have p0089 :=
    @gBitri
      (synWrex n (synCnnc)
        (synW3o (.classEq (.cv m) (synCplc (synCplc (.cv n) (.cv n)) (.cv n)))
          (.classEq (.cv m) (synCplc (synCplc (synCplc (.cv n) (.cv n)) (.cv n)) (synC1c)))
          (.classEq (.cv m)
            (synCplc (synCplc (synCplc (.cv n) (.cv n)) (.cv n)) (synC2c)))))
      (synWrex n (synCnnc) (synWo
          (synWo (.classEq (.cv m) (synCplc (synCplc (.cv n) (.cv n)) (.cv n)))
            (.classEq (.cv m)
              (synCplc (synCplc (synCplc (.cv n) (.cv n)) (.cv n)) (synC1c))))
          (.classEq (.cv m)
            (synCplc (synCplc (synCplc (.cv n) (.cv n)) (.cv n)) (synC2c)))))
      (synW3o (synWrex n (synCnnc)
          (.classEq (.cv m) (synCplc (synCplc (.cv n) (.cv n)) (.cv n))))
        (synWrex n (synCnnc) (.classEq (.cv m)
            (synCplc (synCplc (synCplc (.cv n) (.cv n)) (.cv n)) (synC1c))))
        (synWrex n (synCnnc) (.classEq (.cv m)
            (synCplc (synCplc (synCplc (.cv n) (.cv n)) (.cv n)) (synC2c)))))
      p0083 p0088
  have p0090 :=
    (Nominal.biimpRefl (synW3o (.classEq (synCplc (.cv m) (synC1c))
          (synCplc (synCplc (.cv n) (.cv n)) (.cv n))) (.classEq (synCplc (.cv m) (synC1c))
          (synCplc (synCplc (synCplc (.cv n) (.cv n)) (.cv n)) (synC1c)))
        (.classEq (synCplc (.cv m) (synC1c))
          (synCplc (synCplc (synCplc (.cv n) (.cv n)) (.cv n)) (synC2c)))))
  have p0091 :=
    @gRexbii
      (synW3o (.classEq (synCplc (.cv m) (synC1c))
          (synCplc (synCplc (.cv n) (.cv n)) (.cv n))) (.classEq (synCplc (.cv m) (synC1c))
          (synCplc (synCplc (synCplc (.cv n) (.cv n)) (.cv n)) (synC1c)))
        (.classEq (synCplc (.cv m) (synC1c))
          (synCplc (synCplc (synCplc (.cv n) (.cv n)) (.cv n)) (synC2c))))
      (synWo (synWo (.classEq (synCplc (.cv m) (synC1c))
            (synCplc (synCplc (.cv n) (.cv n)) (.cv n)))
          (.classEq (synCplc (.cv m) (synC1c))
            (synCplc (synCplc (synCplc (.cv n) (.cv n)) (.cv n)) (synC1c))))
        (.classEq (synCplc (.cv m) (synC1c))
          (synCplc (synCplc (synCplc (.cv n) (.cv n)) (.cv n)) (synC2c))))
      n (synCnnc) p0090
  have p0092 :=
    @gR1943
      (synWo (.classEq (synCplc (.cv m) (synC1c))
          (synCplc (synCplc (.cv n) (.cv n)) (.cv n))) (.classEq (synCplc (.cv m) (synC1c))
          (synCplc (synCplc (synCplc (.cv n) (.cv n)) (.cv n)) (synC1c))))
      (.classEq (synCplc (.cv m) (synC1c))
        (synCplc (synCplc (synCplc (.cv n) (.cv n)) (.cv n)) (synC2c)))
      n (synCnnc)
  have p0093 :=
    @gR1943
      (.classEq (synCplc (.cv m) (synC1c)) (synCplc (synCplc (.cv n) (.cv n)) (.cv n)))
      (.classEq (synCplc (.cv m) (synC1c))
        (synCplc (synCplc (synCplc (.cv n) (.cv n)) (.cv n)) (synC1c)))
      n (synCnnc)
  have p0094 :=
    @gOrbi1i
      (synWrex n (synCnnc) (synWo (.classEq (synCplc (.cv m) (synC1c))
            (synCplc (synCplc (.cv n) (.cv n)) (.cv n)))
          (.classEq (synCplc (.cv m) (synC1c))
            (synCplc (synCplc (synCplc (.cv n) (.cv n)) (.cv n)) (synC1c)))))
      (synWo (synWrex n (synCnnc) (.classEq (synCplc (.cv m) (synC1c))
            (synCplc (synCplc (.cv n) (.cv n)) (.cv n)))) (synWrex n (synCnnc)
          (.classEq (synCplc (.cv m) (synC1c))
            (synCplc (synCplc (synCplc (.cv n) (.cv n)) (.cv n)) (synC1c)))))
      (synWrex n (synCnnc) (.classEq (synCplc (.cv m) (synC1c))
          (synCplc (synCplc (synCplc (.cv n) (.cv n)) (.cv n)) (synC2c))))
      p0093
  have p0095 :=
    (Nominal.biimpRefl (synW3o (synWrex n (synCnnc) (.classEq (synCplc (.cv m) (synC1c))
            (synCplc (synCplc (.cv n) (.cv n)) (.cv n)))) (synWrex n (synCnnc)
          (.classEq (synCplc (.cv m) (synC1c))
            (synCplc (synCplc (synCplc (.cv n) (.cv n)) (.cv n)) (synC1c))))
        (synWrex n (synCnnc) (.classEq (synCplc (.cv m) (synC1c))
            (synCplc (synCplc (synCplc (.cv n) (.cv n)) (.cv n)) (synC2c))))))
  have p0096 :=
    @gN3orrot
      (synWrex n (synCnnc) (.classEq (synCplc (.cv m) (synC1c))
          (synCplc (synCplc (.cv n) (.cv n)) (.cv n))))
      (synWrex n (synCnnc) (.classEq (synCplc (.cv m) (synC1c))
          (synCplc (synCplc (synCplc (.cv n) (.cv n)) (.cv n)) (synC1c))))
      (synWrex n (synCnnc) (.classEq (synCplc (.cv m) (synC1c))
          (synCplc (synCplc (synCplc (.cv n) (.cv n)) (.cv n)) (synC2c))))
  have p0097 :=
    @gN3bitr2i
      (synWo (synWrex n (synCnnc) (synWo (.classEq (synCplc (.cv m) (synC1c))
              (synCplc (synCplc (.cv n) (.cv n)) (.cv n)))
            (.classEq (synCplc (.cv m) (synC1c))
              (synCplc (synCplc (synCplc (.cv n) (.cv n)) (.cv n)) (synC1c)))))
        (synWrex n (synCnnc) (.classEq (synCplc (.cv m) (synC1c))
            (synCplc (synCplc (synCplc (.cv n) (.cv n)) (.cv n)) (synC2c)))))
      (synWo (synWo (synWrex n (synCnnc) (.classEq (synCplc (.cv m) (synC1c))
              (synCplc (synCplc (.cv n) (.cv n)) (.cv n)))) (synWrex n (synCnnc)
            (.classEq (synCplc (.cv m) (synC1c))
              (synCplc (synCplc (synCplc (.cv n) (.cv n)) (.cv n)) (synC1c)))))
        (synWrex n (synCnnc) (.classEq (synCplc (.cv m) (synC1c))
            (synCplc (synCplc (synCplc (.cv n) (.cv n)) (.cv n)) (synC2c)))))
      (synW3o (synWrex n (synCnnc) (.classEq (synCplc (.cv m) (synC1c))
            (synCplc (synCplc (.cv n) (.cv n)) (.cv n)))) (synWrex n (synCnnc)
          (.classEq (synCplc (.cv m) (synC1c))
            (synCplc (synCplc (synCplc (.cv n) (.cv n)) (.cv n)) (synC1c))))
        (synWrex n (synCnnc) (.classEq (synCplc (.cv m) (synC1c))
            (synCplc (synCplc (synCplc (.cv n) (.cv n)) (.cv n)) (synC2c)))))
      (synW3o (synWrex n (synCnnc) (.classEq (synCplc (.cv m) (synC1c))
            (synCplc (synCplc (synCplc (.cv n) (.cv n)) (.cv n)) (synC1c))))
        (synWrex n (synCnnc) (.classEq (synCplc (.cv m) (synC1c))
            (synCplc (synCplc (synCplc (.cv n) (.cv n)) (.cv n)) (synC2c))))
        (synWrex n (synCnnc) (.classEq (synCplc (.cv m) (synC1c))
            (synCplc (synCplc (.cv n) (.cv n)) (.cv n)))))
      p0094 p0095 p0096
  have p0098 :=
    @gBitri
      (synWrex n (synCnnc) (synWo (synWo (.classEq (synCplc (.cv m) (synC1c))
              (synCplc (synCplc (.cv n) (.cv n)) (.cv n)))
            (.classEq (synCplc (.cv m) (synC1c))
              (synCplc (synCplc (synCplc (.cv n) (.cv n)) (.cv n)) (synC1c))))
          (.classEq (synCplc (.cv m) (synC1c))
            (synCplc (synCplc (synCplc (.cv n) (.cv n)) (.cv n)) (synC2c)))))
      (synWo (synWrex n (synCnnc) (synWo (.classEq (synCplc (.cv m) (synC1c))
              (synCplc (synCplc (.cv n) (.cv n)) (.cv n)))
            (.classEq (synCplc (.cv m) (synC1c))
              (synCplc (synCplc (synCplc (.cv n) (.cv n)) (.cv n)) (synC1c)))))
        (synWrex n (synCnnc) (.classEq (synCplc (.cv m) (synC1c))
            (synCplc (synCplc (synCplc (.cv n) (.cv n)) (.cv n)) (synC2c)))))
      (synW3o (synWrex n (synCnnc) (.classEq (synCplc (.cv m) (synC1c))
            (synCplc (synCplc (synCplc (.cv n) (.cv n)) (.cv n)) (synC1c))))
        (synWrex n (synCnnc) (.classEq (synCplc (.cv m) (synC1c))
            (synCplc (synCplc (synCplc (.cv n) (.cv n)) (.cv n)) (synC2c))))
        (synWrex n (synCnnc) (.classEq (synCplc (.cv m) (synC1c))
            (synCplc (synCplc (.cv n) (.cv n)) (.cv n)))))
      p0092 p0097
  have p0099 :=
    @gBitri
      (synWrex n (synCnnc) (synW3o (.classEq (synCplc (.cv m) (synC1c))
            (synCplc (synCplc (.cv n) (.cv n)) (.cv n)))
          (.classEq (synCplc (.cv m) (synC1c))
            (synCplc (synCplc (synCplc (.cv n) (.cv n)) (.cv n)) (synC1c)))
          (.classEq (synCplc (.cv m) (synC1c))
            (synCplc (synCplc (synCplc (.cv n) (.cv n)) (.cv n)) (synC2c)))))
      (synWrex n (synCnnc) (synWo (synWo (.classEq (synCplc (.cv m) (synC1c))
              (synCplc (synCplc (.cv n) (.cv n)) (.cv n)))
            (.classEq (synCplc (.cv m) (synC1c))
              (synCplc (synCplc (synCplc (.cv n) (.cv n)) (.cv n)) (synC1c))))
          (.classEq (synCplc (.cv m) (synC1c))
            (synCplc (synCplc (synCplc (.cv n) (.cv n)) (.cv n)) (synC2c)))))
      (synW3o (synWrex n (synCnnc) (.classEq (synCplc (.cv m) (synC1c))
            (synCplc (synCplc (synCplc (.cv n) (.cv n)) (.cv n)) (synC1c))))
        (synWrex n (synCnnc) (.classEq (synCplc (.cv m) (synC1c))
            (synCplc (synCplc (synCplc (.cv n) (.cv n)) (.cv n)) (synC2c))))
        (synWrex n (synCnnc) (.classEq (synCplc (.cv m) (synC1c))
            (synCplc (synCplc (.cv n) (.cv n)) (.cv n)))))
      p0091 p0098
  have p0100 :=
    @gN3imtr4g (.classMem (.cv m) (synCnnc))
      (synW3o (synWrex n (synCnnc)
          (.classEq (.cv m) (synCplc (synCplc (.cv n) (.cv n)) (.cv n))))
        (synWrex n (synCnnc) (.classEq (.cv m)
            (synCplc (synCplc (synCplc (.cv n) (.cv n)) (.cv n)) (synC1c))))
        (synWrex n (synCnnc) (.classEq (.cv m)
            (synCplc (synCplc (synCplc (.cv n) (.cv n)) (.cv n)) (synC2c)))))
      (synW3o (synWrex n (synCnnc) (.classEq (synCplc (.cv m) (synC1c))
            (synCplc (synCplc (synCplc (.cv n) (.cv n)) (.cv n)) (synC1c))))
        (synWrex n (synCnnc) (.classEq (synCplc (.cv m) (synC1c))
            (synCplc (synCplc (synCplc (.cv n) (.cv n)) (.cv n)) (synC2c))))
        (synWrex n (synCnnc) (.classEq (synCplc (.cv m) (synC1c))
            (synCplc (synCplc (.cv n) (.cv n)) (.cv n)))))
      (synWrex n (synCnnc)
        (synW3o (.classEq (.cv m) (synCplc (synCplc (.cv n) (.cv n)) (.cv n)))
          (.classEq (.cv m) (synCplc (synCplc (synCplc (.cv n) (.cv n)) (.cv n)) (synC1c)))
          (.classEq (.cv m)
            (synCplc (synCplc (synCplc (.cv n) (.cv n)) (.cv n)) (synC2c)))))
      (synWrex n (synCnnc) (synW3o (.classEq (synCplc (.cv m) (synC1c))
            (synCplc (synCplc (.cv n) (.cv n)) (.cv n)))
          (.classEq (synCplc (.cv m) (synC1c))
            (synCplc (synCplc (synCplc (.cv n) (.cv n)) (.cv n)) (synC1c)))
          (.classEq (synCplc (.cv m) (synC1c))
            (synCplc (synCplc (synCplc (.cv n) (.cv n)) (.cv n)) (synC2c)))))
      p0081 p0089 p0099
  have p0101 :=
    @gFinds
      (synWrex n (synCnnc)
        (synW3o (.classEq (.cv a) (synCplc (synCplc (.cv n) (.cv n)) (.cv n)))
          (.classEq (.cv a) (synCplc (synCplc (synCplc (.cv n) (.cv n)) (.cv n)) (synC1c)))
          (.classEq (.cv a)
            (synCplc (synCplc (synCplc (.cv n) (.cv n)) (.cv n)) (synC2c)))))
      (synWrex n (synCnnc)
        (synW3o (.classEq (synC0c) (synCplc (synCplc (.cv n) (.cv n)) (.cv n)))
          (.classEq (synC0c)
            (synCplc (synCplc (synCplc (.cv n) (.cv n)) (.cv n)) (synC1c)))
          (.classEq (synC0c)
            (synCplc (synCplc (synCplc (.cv n) (.cv n)) (.cv n)) (synC2c)))))
      (synWrex n (synCnnc)
        (synW3o (.classEq (.cv m) (synCplc (synCplc (.cv n) (.cv n)) (.cv n)))
          (.classEq (.cv m) (synCplc (synCplc (synCplc (.cv n) (.cv n)) (.cv n)) (synC1c)))
          (.classEq (.cv m)
            (synCplc (synCplc (synCplc (.cv n) (.cv n)) (.cv n)) (synC2c)))))
      (synWrex n (synCnnc) (synW3o (.classEq (synCplc (.cv m) (synC1c))
            (synCplc (synCplc (.cv n) (.cv n)) (.cv n)))
          (.classEq (synCplc (.cv m) (synC1c))
            (synCplc (synCplc (synCplc (.cv n) (.cv n)) (.cv n)) (synC1c)))
          (.classEq (synCplc (.cv m) (synC1c))
            (synCplc (synCplc (synCplc (.cv n) (.cv n)) (.cv n)) (synC2c)))))
      (synWrex n (synCnnc) (synW3o (.classEq A (synCplc (synCplc (.cv n) (.cv n)) (.cv n)))
          (.classEq A (synCplc (synCplc (synCplc (.cv n) (.cv n)) (.cv n)) (synC1c)))
          (.classEq A (synCplc (synCplc (synCplc (.cv n) (.cv n)) (.cv n)) (synC2c)))))
      a m A dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020
      dv_cache_0021 dv_cache_0022 p0000 p0005 p0010 p0015 p0020 p0038 p0100
  exact p0101


end NFChoice.DirectNominalPrf.WPPReplay

end
