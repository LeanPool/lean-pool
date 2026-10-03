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

@[expose]
noncomputable def g_csucex (x : Var) :
    Nominal.NPrf
      (.classMem (syn_cmpt x (syn_cvv) (syn_cplc (.cv x) (syn_c1c))) (syn_cvv)) :=
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
      ((syn_wbr (.cv w) (syn_cres (syn_caddcfn) (syn_cxp (syn_cvv) (syn_csn (syn_c1c))))
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
  have dv_cache_0004 : x ∉ ((syn_c1c)).fv :=
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
  have dv_cache_0005 : w ∉ ((syn_cop (.cv y) (.cv x))).fv :=
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
      ((syn_wa (.classEq (.cv x) (syn_c1c))
          (.classEq (syn_cplc (.cv y) (.cv x)) (.cv z)))).fv :=
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
  have dv_cache_0007 : x ∉ ((Wff.classEq (syn_cplc (.cv y) (syn_c1c)) (.cv z))).fv :=
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
    w ∉ ((syn_cres (syn_caddcfn) (syn_cxp (syn_cvv) (syn_csn (syn_c1c))))).fv :=
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
  have dv_cache_0011 : w ∉ ((syn_ccnv (syn_c1st))).fv :=
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
  have dv_cache_0012 : w ∉ ((syn_cplc (.cv x) (syn_c1c))).fv :=
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
  have dv_cache_0015 : w ∉ ((Wff.classEq (syn_cplc (.cv y) (syn_c1c)) (.cv z))).fv :=
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
  have dv_cache_0016 : y ∉ ((syn_cmpt x (syn_cvv) (syn_cplc (.cv x) (syn_c1c)))).fv :=
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
  have dv_cache_0017 : z ∉ ((syn_cmpt x (syn_cvv) (syn_cplc (.cv x) (syn_c1c)))).fv :=
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
      ((syn_ccom (syn_cres (syn_caddcfn) (syn_cxp (syn_cvv) (syn_csn (syn_c1c))))
          (syn_ccnv (syn_c1st)))).fv :=
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
      ((syn_ccom (syn_cres (syn_caddcfn) (syn_cxp (syn_cvv) (syn_csn (syn_c1c))))
          (syn_ccnv (syn_c1st)))).fv :=
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
  have p0000 := @g_brcnv (.cv y) (.cv w) (syn_c1st)
  have p0001 := @g_vex y
  have p0002 := @g_br1st x (.cv w) (.cv y) dv_cache_0001 dv_cache_0002 p0001
  have p0003 :=
    @g_bitri (syn_wbr (.cv y) (syn_ccnv (syn_c1st)) (.cv w))
      (syn_wbr (.cv w) (syn_c1st) (.cv y))
      (syn_wex x (.classEq (.cv w) (syn_cop (.cv y) (.cv x)))) p0000 p0002
  have p0004 :=
    @g_anbi1i (syn_wbr (.cv y) (syn_ccnv (syn_c1st)) (.cv w))
      (syn_wex x (.classEq (.cv w) (syn_cop (.cv y) (.cv x))))
      (syn_wbr (.cv w) (syn_cres (syn_caddcfn) (syn_cxp (syn_cvv) (syn_csn (syn_c1c)))) (.cv z))
      p0003
  have p0005 :=
    @g_n_19_41v (.classEq (.cv w) (syn_cop (.cv y) (.cv x)))
      (syn_wbr (.cv w) (syn_cres (syn_caddcfn) (syn_cxp (syn_cvv) (syn_csn (syn_c1c)))) (.cv z))
      x dv_cache_0003
  have p0006 :=
    @g_bitr4i
      (syn_wa (syn_wbr (.cv y) (syn_ccnv (syn_c1st)) (.cv w))
        (syn_wbr (.cv w) (syn_cres (syn_caddcfn) (syn_cxp (syn_cvv) (syn_csn (syn_c1c))))
          (.cv z)))
      (syn_wa (syn_wex x (.classEq (.cv w) (syn_cop (.cv y) (.cv x))))
        (syn_wbr (.cv w) (syn_cres (syn_caddcfn) (syn_cxp (syn_cvv) (syn_csn (syn_c1c))))
          (.cv z)))
      (syn_wex x (syn_wa (.classEq (.cv w) (syn_cop (.cv y) (.cv x))) (syn_wbr (.cv w)
            (syn_cres (syn_caddcfn) (syn_cxp (syn_cvv) (syn_csn (syn_c1c)))) (.cv z))))
      p0004 p0005
  have p0007 :=
    @g_exbii
      (syn_wa (syn_wbr (.cv y) (syn_ccnv (syn_c1st)) (.cv w))
        (syn_wbr (.cv w) (syn_cres (syn_caddcfn) (syn_cxp (syn_cvv) (syn_csn (syn_c1c))))
          (.cv z)))
      (syn_wex x (syn_wa (.classEq (.cv w) (syn_cop (.cv y) (.cv x))) (syn_wbr (.cv w)
            (syn_cres (syn_caddcfn) (syn_cxp (syn_cvv) (syn_csn (syn_c1c)))) (.cv z))))
      w p0006
  have p0008 :=
    @g_excom
      (syn_wa (.classEq (.cv w) (syn_cop (.cv y) (.cv x)))
        (syn_wbr (.cv w) (syn_cres (syn_caddcfn) (syn_cxp (syn_cvv) (syn_csn (syn_c1c))))
          (.cv z)))
      w x
  have p0009 := @g_vex x
  have p0010 := @g_opex (.cv y) (.cv x) p0001 p0009
  have p0011 :=
    @g_breq1 (.cv w) (syn_cop (.cv y) (.cv x)) (.cv z)
      (syn_cres (syn_caddcfn) (syn_cxp (syn_cvv) (syn_csn (syn_c1c))))
  have p0012 :=
    @g_brres (syn_cop (.cv y) (.cv x)) (.cv z) (syn_caddcfn)
      (syn_cxp (syn_cvv) (syn_csn (syn_c1c)))
  have p0013 := @g_braddcfn (.cv y) (.cv x) (.cv z) p0001 p0009
  have p0014 := @g_opelxp (.cv y) (.cv x) (syn_cvv) (syn_csn (syn_c1c))
  have p0015 :=
    @g_mpbiran
      (.classMem (syn_cop (.cv y) (.cv x)) (syn_cxp (syn_cvv) (syn_csn (syn_c1c))))
      (.classMem (.cv y) (syn_cvv)) (.classMem (.cv x) (syn_csn (syn_c1c))) p0001 p0014
  have p0016 := @g_elsn x (syn_c1c) dv_cache_0004
  have p0017 :=
    @g_bitri (.classMem (syn_cop (.cv y) (.cv x)) (syn_cxp (syn_cvv) (syn_csn (syn_c1c))))
      (.classMem (.cv x) (syn_csn (syn_c1c))) (.classEq (.cv x) (syn_c1c)) p0015 p0016
  have p0018 :=
    @g_anbi12ci (syn_wbr (syn_cop (.cv y) (.cv x)) (syn_caddcfn) (.cv z))
      (.classEq (syn_cplc (.cv y) (.cv x)) (.cv z))
      (.classMem (syn_cop (.cv y) (.cv x)) (syn_cxp (syn_cvv) (syn_csn (syn_c1c))))
      (.classEq (.cv x) (syn_c1c)) p0013 p0017
  have p0019 :=
    @g_bitri
      (syn_wbr (syn_cop (.cv y) (.cv x))
        (syn_cres (syn_caddcfn) (syn_cxp (syn_cvv) (syn_csn (syn_c1c)))) (.cv z))
      (syn_wa (syn_wbr (syn_cop (.cv y) (.cv x)) (syn_caddcfn) (.cv z))
        (.classMem (syn_cop (.cv y) (.cv x)) (syn_cxp (syn_cvv) (syn_csn (syn_c1c)))))
      (syn_wa (.classEq (.cv x) (syn_c1c)) (.classEq (syn_cplc (.cv y) (.cv x)) (.cv z)))
      p0012 p0018
  have p0020 :=
    @g_syl6bb (.classEq (.cv w) (syn_cop (.cv y) (.cv x)))
      (syn_wbr (.cv w) (syn_cres (syn_caddcfn) (syn_cxp (syn_cvv) (syn_csn (syn_c1c)))) (.cv z))
      (syn_wbr (syn_cop (.cv y) (.cv x))
        (syn_cres (syn_caddcfn) (syn_cxp (syn_cvv) (syn_csn (syn_c1c)))) (.cv z))
      (syn_wa (.classEq (.cv x) (syn_c1c)) (.classEq (syn_cplc (.cv y) (.cv x)) (.cv z)))
      p0011 p0019
  have p0021 :=
    @g_ceqsexv
      (syn_wbr (.cv w) (syn_cres (syn_caddcfn) (syn_cxp (syn_cvv) (syn_csn (syn_c1c)))) (.cv z))
      (syn_wa (.classEq (.cv x) (syn_c1c)) (.classEq (syn_cplc (.cv y) (.cv x)) (.cv z)))
      w (syn_cop (.cv y) (.cv x)) dv_cache_0005 dv_cache_0006 p0010 p0020
  have p0022 :=
    @g_exbii
      (syn_wex w (syn_wa (.classEq (.cv w) (syn_cop (.cv y) (.cv x))) (syn_wbr (.cv w)
            (syn_cres (syn_caddcfn) (syn_cxp (syn_cvv) (syn_csn (syn_c1c)))) (.cv z))))
      (syn_wa (.classEq (.cv x) (syn_c1c)) (.classEq (syn_cplc (.cv y) (.cv x)) (.cv z)))
      x p0021
  have p0023 :=
    @g_bitri
      (syn_wex w (syn_wex x (syn_wa (.classEq (.cv w) (syn_cop (.cv y) (.cv x)))
            (syn_wbr (.cv w)
              (syn_cres (syn_caddcfn) (syn_cxp (syn_cvv) (syn_csn (syn_c1c)))) (.cv z)))))
      (syn_wex x (syn_wex w (syn_wa (.classEq (.cv w) (syn_cop (.cv y) (.cv x)))
            (syn_wbr (.cv w)
              (syn_cres (syn_caddcfn) (syn_cxp (syn_cvv) (syn_csn (syn_c1c)))) (.cv z)))))
      (syn_wex x (syn_wa (.classEq (.cv x) (syn_c1c))
          (.classEq (syn_cplc (.cv y) (.cv x)) (.cv z))))
      p0008 p0022
  have p0024 :=
    @g_bitri
      (syn_wex w (syn_wa (syn_wbr (.cv y) (syn_ccnv (syn_c1st)) (.cv w)) (syn_wbr (.cv w)
            (syn_cres (syn_caddcfn) (syn_cxp (syn_cvv) (syn_csn (syn_c1c)))) (.cv z))))
      (syn_wex w (syn_wex x (syn_wa (.classEq (.cv w) (syn_cop (.cv y) (.cv x)))
            (syn_wbr (.cv w)
              (syn_cres (syn_caddcfn) (syn_cxp (syn_cvv) (syn_csn (syn_c1c)))) (.cv z)))))
      (syn_wex x (syn_wa (.classEq (.cv x) (syn_c1c))
          (.classEq (syn_cplc (.cv y) (.cv x)) (.cv z))))
      p0007 p0023
  have p0025 := @g_n_1cex
  have p0026 := @g_addceq2 (.cv x) (syn_c1c) (.cv y)
  have p0027 :=
    @g_eqeq1d (.classEq (.cv x) (syn_c1c)) (syn_cplc (.cv y) (.cv x))
      (syn_cplc (.cv y) (syn_c1c)) (.cv z) p0026
  have p0028 :=
    @g_ceqsexv (.classEq (syn_cplc (.cv y) (.cv x)) (.cv z))
      (.classEq (syn_cplc (.cv y) (syn_c1c)) (.cv z)) x (syn_c1c) dv_cache_0004
      dv_cache_0007 p0025 p0027
  have p0029 :=
    @g_bitri
      (syn_wex w (syn_wa (syn_wbr (.cv y) (syn_ccnv (syn_c1st)) (.cv w)) (syn_wbr (.cv w)
            (syn_cres (syn_caddcfn) (syn_cxp (syn_cvv) (syn_csn (syn_c1c)))) (.cv z))))
      (syn_wex x (syn_wa (.classEq (.cv x) (syn_c1c))
          (.classEq (syn_cplc (.cv y) (.cv x)) (.cv z))))
      (.classEq (syn_cplc (.cv y) (syn_c1c)) (.cv z)) p0024 p0028
  have p0030 :=
    @g_opelco w (.cv y) (.cv z)
      (syn_cres (syn_caddcfn) (syn_cxp (syn_cvv) (syn_csn (syn_c1c))))
      (syn_ccnv (syn_c1st)) dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
  have p0031 := @g_mptv x w (syn_cplc (.cv x) (syn_c1c)) dv_cache_0012 dv_cache_0013
  have p0032 :=
    @g_eleq2i (syn_cmpt x (syn_cvv) (syn_cplc (.cv x) (syn_c1c)))
      (syn_copab x w (.classEq (.cv w) (syn_cplc (.cv x) (syn_c1c))))
      (syn_cop (.cv y) (.cv z)) p0031
  have p0033 := @g_vex z
  have p0034 := @g_addceq1 (.cv x) (.cv y) (syn_c1c)
  have p0035_e00_recanon :
    Nominal.NPrf
      (.imp (.objEq x y)
        (.classEq (syn_cplc (.cv x) (syn_c1c)) (syn_cplc (.cv y) (syn_c1c)))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_cplc syn_wrex syn_wex syn_wa syn_c1c
        simp (config :=
          { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_class_cv]
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
        · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0034
  have p0035 :=
    @g_eqeq2d (.objEq x y) (syn_cplc (.cv x) (syn_c1c)) (syn_cplc (.cv y) (syn_c1c))
      (.cv w) p0035_e00_recanon
  have p0036 := @g_eqeq1 (.cv w) (.cv z) (syn_cplc (.cv y) (syn_c1c))
  have p0037 := @g_eqcom (.cv z) (syn_cplc (.cv y) (syn_c1c))
  have p0038_e00_recanon :
    Nominal.NPrf
      (.imp (.objEq w z) (syn_wb (.classEq (.cv w) (syn_cplc (.cv y) (syn_c1c)))
          (.classEq (.cv z) (syn_cplc (.cv y) (syn_c1c))))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wb syn_cplc syn_wrex syn_wex syn_wa syn_c1c
        simp (config :=
          { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_class_cv]
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
        · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0036
  have p0038 :=
    @g_syl6bb (.objEq w z) (.classEq (.cv w) (syn_cplc (.cv y) (syn_c1c)))
      (.classEq (.cv z) (syn_cplc (.cv y) (syn_c1c)))
      (.classEq (syn_cplc (.cv y) (syn_c1c)) (.cv z)) p0038_e00_recanon p0037
  have p0039_e02_recanon :
    Nominal.NPrf
      (.imp (.classEq (.cv x) (.cv y)) (syn_wb (.classEq (.cv w) (syn_cplc (.cv x) (syn_c1c)))
          (.classEq (.cv w) (syn_cplc (.cv y) (syn_c1c))))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wb syn_cplc syn_wrex syn_wex syn_wa syn_c1c
        simp (config :=
          { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_class_cv]
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · exact Nominal.RecanonTransportDev.TRecanonWff.objEq_classEq _ _
        · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0035
  have p0039_e03_recanon :
    Nominal.NPrf
      (.imp (.classEq (.cv w) (.cv z)) (syn_wb (.classEq (.cv w) (syn_cplc (.cv y) (syn_c1c)))
          (.classEq (syn_cplc (.cv y) (syn_c1c)) (.cv z)))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wb syn_cplc syn_wrex syn_wex syn_wa syn_c1c
        simp (config :=
          { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_class_cv]
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · exact Nominal.RecanonTransportDev.TRecanonWff.objEq_classEq _ _
        · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0038
  have p0039 :=
    @g_opelopab (.classEq (.cv w) (syn_cplc (.cv x) (syn_c1c)))
      (.classEq (.cv w) (syn_cplc (.cv y) (syn_c1c)))
      (.classEq (syn_cplc (.cv y) (syn_c1c)) (.cv z)) x w (.cv y) (.cv z) dv_cache_0002
      dv_cache_0008 dv_cache_0014 dv_cache_0009 dv_cache_0007 dv_cache_0015 dv_cache_0013
      p0001 p0033 p0039_e02_recanon p0039_e03_recanon
  have p0040 :=
    @g_bitri
      (.classMem (syn_cop (.cv y) (.cv z)) (syn_cmpt x (syn_cvv) (syn_cplc (.cv x) (syn_c1c))))
      (.classMem (syn_cop (.cv y) (.cv z))
        (syn_copab x w (.classEq (.cv w) (syn_cplc (.cv x) (syn_c1c)))))
      (.classEq (syn_cplc (.cv y) (syn_c1c)) (.cv z)) p0032 p0039
  have p0041 :=
    @g_n_3bitr4ri
      (syn_wex w (syn_wa (syn_wbr (.cv y) (syn_ccnv (syn_c1st)) (.cv w)) (syn_wbr (.cv w)
            (syn_cres (syn_caddcfn) (syn_cxp (syn_cvv) (syn_csn (syn_c1c)))) (.cv z))))
      (.classEq (syn_cplc (.cv y) (syn_c1c)) (.cv z))
      (.classMem (syn_cop (.cv y) (.cv z))
        (syn_ccom (syn_cres (syn_caddcfn) (syn_cxp (syn_cvv) (syn_csn (syn_c1c))))
          (syn_ccnv (syn_c1st))))
      (.classMem (syn_cop (.cv y) (.cv z)) (syn_cmpt x (syn_cvv) (syn_cplc (.cv x) (syn_c1c))))
      p0029 p0030 p0040
  have p0042 :=
    @g_eqrelriv y z (syn_cmpt x (syn_cvv) (syn_cplc (.cv x) (syn_c1c)))
      (syn_ccom (syn_cres (syn_caddcfn) (syn_cxp (syn_cvv) (syn_csn (syn_c1c))))
        (syn_ccnv (syn_c1st)))
      dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 p0041
  have p0043 := @g_addcfnex
  have p0044 := @g_vvex
  have p0045 := @g_snex (syn_c1c)
  have p0046 := @g_xpex (syn_cvv) (syn_csn (syn_c1c)) p0044 p0045
  have p0047 := @g_resex (syn_caddcfn) (syn_cxp (syn_cvv) (syn_csn (syn_c1c))) p0043 p0046
  have p0048 := @g_n_1stex
  have p0049 := @g_cnvex (syn_c1st) p0048
  have p0050 :=
    @g_coex (syn_cres (syn_caddcfn) (syn_cxp (syn_cvv) (syn_csn (syn_c1c))))
      (syn_ccnv (syn_c1st)) p0047 p0049
  have p0051 :=
    @g_eqeltri (syn_cmpt x (syn_cvv) (syn_cplc (.cv x) (syn_c1c)))
      (syn_ccom (syn_cres (syn_caddcfn) (syn_cxp (syn_cvv) (syn_csn (syn_c1c))))
        (syn_ccnv (syn_c1st)))
      (syn_cvv) p0042 p0050
  exact p0051

@[expose]
noncomputable def g_brcsuc (x : Var) (A : Class) (B : Class) (dv_A_x : x ∉ A.fv)
    (dv_B_x : x ∉ B.fv) (hyp_brcsuc_1 : Nominal.NPrf (.classMem A (syn_cvv)))
    (hyp_brcsuc_2 : Nominal.NPrf (.classMem B (syn_cvv))) :
    Nominal.NPrf
      (syn_wb (syn_wbr A (syn_cmpt x (syn_cvv) (syn_cplc (.cv x) (syn_c1c))) B)
        (.classEq B (syn_cplc A (syn_c1c)))) :=
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
  have dv_cache_0001 : y ∉ ((syn_cplc (.cv x) (syn_c1c))).fv := by
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
  have dv_cache_0007 : x ∉ ((Wff.classEq B (syn_cplc A (syn_c1c)))).fv :=
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
  have dv_cache_0008 : y ∉ ((Wff.classEq B (syn_cplc A (syn_c1c)))).fv :=
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
  have p0000 := @g_addceq1 (.cv x) A (syn_c1c)
  have p0001 :=
    @g_eqeq2d (.classEq (.cv x) A) (syn_cplc (.cv x) (syn_c1c)) (syn_cplc A (syn_c1c))
      (.cv y) p0000
  have p0002 := @g_eqeq1 (.cv y) B (syn_cplc A (syn_c1c))
  have p0003 := @g_mptv x y (syn_cplc (.cv x) (syn_c1c)) dv_cache_0001 dv_cache_0002
  have p0004 :=
    @g_brab (.classEq (.cv y) (syn_cplc (.cv x) (syn_c1c)))
      (.classEq (.cv y) (syn_cplc A (syn_c1c))) (.classEq B (syn_cplc A (syn_c1c))) x y A
      B (syn_cmpt x (syn_cvv) (syn_cplc (.cv x) (syn_c1c))) dv_cache_0003 dv_cache_0004
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

@[expose]
noncomputable def g_nncdiv3lem1 (n : Var) (b : Var) :
    Nominal.NPrf
      (syn_wb (.classMem (syn_cop (.cv n) (.cv b)) (syn_crn (syn_cin (syn_cins3 (syn_ccnv
                  (syn_cima (syn_ctxp (syn_crn
                        (syn_ctxp (syn_ccnv (syn_c1st)) (syn_cin (syn_c1st) (syn_c2nd))))
                      (syn_c2nd)) (syn_caddcfn)))) (syn_cima
                (syn_ctxp (syn_ccom (syn_c1st) (syn_c1st))
                  (syn_ctxp (syn_ccom (syn_c2nd) (syn_c1st)) (syn_c2nd))) (syn_caddcfn)))))
        (.classEq (.cv b) (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n)))) :=
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
  have dv_cache_0001 : m ∉ ((syn_cop (.cv n) (.cv b))).fv := by
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
      ((syn_cin (syn_cins3 (syn_ccnv (syn_cima (syn_ctxp (syn_crn
                    (syn_ctxp (syn_ccnv (syn_c1st)) (syn_cin (syn_c1st) (syn_c2nd))))
                  (syn_c2nd)) (syn_caddcfn)))) (syn_cima
            (syn_ctxp (syn_ccom (syn_c1st) (syn_c1st))
              (syn_ctxp (syn_ccom (syn_c2nd) (syn_c1st)) (syn_c2nd))) (syn_caddcfn)))).fv :=
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
  have dv_cache_0003 : m ∉ ((syn_cop (.cv t) (.cv n))).fv :=
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
    m ∉ ((syn_ctxp (syn_ccnv (syn_c1st)) (syn_cin (syn_c1st) (syn_c2nd)))).fv :=
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
  have dv_cache_0005 : m ∉ ((syn_cproj1 (.cv t))).fv :=
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
  have dv_cache_0006 : m ∉ ((syn_cop (.cv n) (.cv n))).fv :=
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
  have dv_cache_0007 : t ∉ ((syn_cop (.cv n) (.cv m))).fv :=
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
      ((syn_ctxp (syn_crn (syn_ctxp (syn_ccnv (syn_c1st)) (syn_cin (syn_c1st) (syn_c2nd))))
          (syn_c2nd))).fv :=
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
  have dv_cache_0009 : t ∉ ((syn_caddcfn)).fv :=
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
  have dv_cache_0010 : t ∉ ((syn_cop (syn_cop (.cv n) (.cv n)) (.cv m))).fv :=
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
  have dv_cache_0011 : t ∉ ((syn_cop (.cv m) (syn_cop (.cv n) (.cv b)))).fv :=
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
      ((syn_ctxp (syn_ccom (syn_c1st) (syn_c1st))
          (syn_ctxp (syn_ccom (syn_c2nd) (syn_c1st)) (syn_c2nd)))).fv :=
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
  have dv_cache_0015 : n ∉ ((syn_c1st)).fv :=
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
  have dv_cache_0016 : n ∉ ((syn_cproj1 (.cv t))).fv :=
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
  have dv_cache_0017 : n ∉ ((syn_wbr (syn_cproj1 (.cv t)) (syn_c1st) (.cv m))).fv :=
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
  have dv_cache_0020 : m ∉ ((syn_c2nd)).fv :=
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
  have dv_cache_0021 : m ∉ ((syn_c1st)).fv :=
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
  have dv_cache_0022 : m ∉ ((syn_wbr (syn_cproj1 (.cv t)) (syn_c2nd) (.cv n))).fv :=
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
  have dv_cache_0023 : t ∉ ((syn_cop (syn_cop (.cv m) (.cv n)) (.cv b))).fv :=
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
  have dv_cache_0024 : m ∉ ((syn_cplc (.cv n) (.cv n))).fv :=
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
    m ∉ ((Wff.classEq (.cv b) (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n)))).fv :=
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
    @g_elrn2 m (syn_cop (.cv n) (.cv b))
      (syn_cin (syn_cins3 (syn_ccnv (syn_cima (syn_ctxp
                (syn_crn (syn_ctxp (syn_ccnv (syn_c1st)) (syn_cin (syn_c1st) (syn_c2nd))))
                (syn_c2nd)) (syn_caddcfn)))) (syn_cima
          (syn_ctxp (syn_ccom (syn_c1st) (syn_c1st))
            (syn_ctxp (syn_ccom (syn_c2nd) (syn_c1st)) (syn_c2nd))) (syn_caddcfn)))
      dv_cache_0001 dv_cache_0002
  have p0001 :=
    @g_elin (syn_cop (.cv m) (syn_cop (.cv n) (.cv b)))
      (syn_cins3 (syn_ccnv (syn_cima (syn_ctxp
              (syn_crn (syn_ctxp (syn_ccnv (syn_c1st)) (syn_cin (syn_c1st) (syn_c2nd))))
              (syn_c2nd)) (syn_caddcfn))))
      (syn_cima (syn_ctxp (syn_ccom (syn_c1st) (syn_c1st))
          (syn_ctxp (syn_ccom (syn_c2nd) (syn_c1st)) (syn_c2nd))) (syn_caddcfn))
  have p0002 := @g_vex b
  have p0003 :=
    @g_otelins3 (.cv m) (.cv n) (.cv b)
      (syn_ccnv (syn_cima (syn_ctxp
            (syn_crn (syn_ctxp (syn_ccnv (syn_c1st)) (syn_cin (syn_c1st) (syn_c2nd))))
            (syn_c2nd)) (syn_caddcfn)))
      p0002
  have p0004 :=
    @g_opelcnv (.cv m) (.cv n)
      (syn_cima (syn_ctxp
          (syn_crn (syn_ctxp (syn_ccnv (syn_c1st)) (syn_cin (syn_c1st) (syn_c2nd)))) (syn_c2nd))
        (syn_caddcfn))
  have p0005 :=
    @g_trtxp (.cv t) (.cv n) (.cv m)
      (syn_crn (syn_ctxp (syn_ccnv (syn_c1st)) (syn_cin (syn_c1st) (syn_c2nd))))
      (syn_c2nd)
  have p0006 :=
    (Nominal.biimpRefl (syn_wbr (.cv t)
        (syn_crn (syn_ctxp (syn_ccnv (syn_c1st)) (syn_cin (syn_c1st) (syn_c2nd)))) (.cv n)))
  have p0007 :=
    @g_elrn2 m (syn_cop (.cv t) (.cv n))
      (syn_ctxp (syn_ccnv (syn_c1st)) (syn_cin (syn_c1st) (syn_c2nd))) dv_cache_0003
      dv_cache_0004
  have p0008 := @g_vex t
  have p0009 := @g_proj1ex (.cv t) p0008
  have p0010 :=
    @g_eqvinc m (syn_cproj1 (.cv t)) (syn_cop (.cv n) (.cv n)) dv_cache_0005 dv_cache_0006
      p0009
  have p0011 := @g_opeq (.cv t)
  have p0012 :=
    @g_breq1i (.cv t) (syn_cop (syn_cproj1 (.cv t)) (syn_cproj2 (.cv t)))
      (syn_cop (.cv n) (.cv n)) (syn_c1st) p0011
  have p0013 := @g_proj2ex (.cv t) p0008
  have p0014 :=
    @g_opbr1st (syn_cproj1 (.cv t)) (syn_cproj2 (.cv t)) (syn_cop (.cv n) (.cv n)) p0009
      p0013
  have p0015 :=
    @g_bitri (syn_wbr (.cv t) (syn_c1st) (syn_cop (.cv n) (.cv n)))
      (syn_wbr (syn_cop (syn_cproj1 (.cv t)) (syn_cproj2 (.cv t))) (syn_c1st)
        (syn_cop (.cv n) (.cv n)))
      (.classEq (syn_cproj1 (.cv t)) (syn_cop (.cv n) (.cv n))) p0012 p0014
  have p0016 :=
    @g_oteltxp (.cv m) (.cv t) (.cv n) (syn_ccnv (syn_c1st))
      (syn_cin (syn_c1st) (syn_c2nd))
  have p0017 := @g_opelcnv (.cv m) (.cv t) (syn_c1st)
  have p0018 := (Nominal.biimpRefl (syn_wbr (.cv t) (syn_c1st) (.cv m)))
  have p0019 :=
    @g_breq1i (.cv t) (syn_cop (syn_cproj1 (.cv t)) (syn_cproj2 (.cv t))) (.cv m)
      (syn_c1st) p0011
  have p0020 := @g_opbr1st (syn_cproj1 (.cv t)) (syn_cproj2 (.cv t)) (.cv m) p0009 p0013
  have p0021 := @g_eqcom (syn_cproj1 (.cv t)) (.cv m)
  have p0022 :=
    @g_n_3bitri (syn_wbr (.cv t) (syn_c1st) (.cv m))
      (syn_wbr (syn_cop (syn_cproj1 (.cv t)) (syn_cproj2 (.cv t))) (syn_c1st) (.cv m))
      (.classEq (syn_cproj1 (.cv t)) (.cv m)) (.classEq (.cv m) (syn_cproj1 (.cv t)))
      p0019 p0020 p0021
  have p0023 :=
    @g_n_3bitr2i (.classMem (syn_cop (.cv m) (.cv t)) (syn_ccnv (syn_c1st)))
      (.classMem (syn_cop (.cv t) (.cv m)) (syn_c1st))
      (syn_wbr (.cv t) (syn_c1st) (.cv m)) (.classEq (.cv m) (syn_cproj1 (.cv t))) p0017
      p0018 p0022
  have p0024 := @g_elin (syn_cop (.cv m) (.cv n)) (syn_c1st) (syn_c2nd)
  have p0025 := (Nominal.biimpRefl (syn_wbr (.cv m) (syn_c1st) (.cv n)))
  have p0026 := (Nominal.biimpRefl (syn_wbr (.cv m) (syn_c2nd) (.cv n)))
  have p0027 :=
    @g_anbi12i (syn_wbr (.cv m) (syn_c1st) (.cv n))
      (.classMem (syn_cop (.cv m) (.cv n)) (syn_c1st))
      (syn_wbr (.cv m) (syn_c2nd) (.cv n))
      (.classMem (syn_cop (.cv m) (.cv n)) (syn_c2nd)) p0025 p0026
  have p0028 := @g_vex n
  have p0029 := @g_op1st2nd (.cv n) (.cv n) (.cv m) p0028 p0028
  have p0030 :=
    @g_n_3bitr2i (.classMem (syn_cop (.cv m) (.cv n)) (syn_cin (syn_c1st) (syn_c2nd)))
      (syn_wa (.classMem (syn_cop (.cv m) (.cv n)) (syn_c1st))
        (.classMem (syn_cop (.cv m) (.cv n)) (syn_c2nd)))
      (syn_wa (syn_wbr (.cv m) (syn_c1st) (.cv n)) (syn_wbr (.cv m) (syn_c2nd) (.cv n)))
      (.classEq (.cv m) (syn_cop (.cv n) (.cv n))) p0024 p0027 p0029
  have p0031 :=
    @g_anbi12i (.classMem (syn_cop (.cv m) (.cv t)) (syn_ccnv (syn_c1st)))
      (.classEq (.cv m) (syn_cproj1 (.cv t)))
      (.classMem (syn_cop (.cv m) (.cv n)) (syn_cin (syn_c1st) (syn_c2nd)))
      (.classEq (.cv m) (syn_cop (.cv n) (.cv n))) p0023 p0030
  have p0032 :=
    @g_bitri
      (.classMem (syn_cop (.cv m) (syn_cop (.cv t) (.cv n)))
        (syn_ctxp (syn_ccnv (syn_c1st)) (syn_cin (syn_c1st) (syn_c2nd))))
      (syn_wa (.classMem (syn_cop (.cv m) (.cv t)) (syn_ccnv (syn_c1st)))
        (.classMem (syn_cop (.cv m) (.cv n)) (syn_cin (syn_c1st) (syn_c2nd))))
      (syn_wa (.classEq (.cv m) (syn_cproj1 (.cv t)))
        (.classEq (.cv m) (syn_cop (.cv n) (.cv n))))
      p0016 p0031
  have p0033 :=
    @g_exbii
      (.classMem (syn_cop (.cv m) (syn_cop (.cv t) (.cv n)))
        (syn_ctxp (syn_ccnv (syn_c1st)) (syn_cin (syn_c1st) (syn_c2nd))))
      (syn_wa (.classEq (.cv m) (syn_cproj1 (.cv t)))
        (.classEq (.cv m) (syn_cop (.cv n) (.cv n))))
      m p0032
  have p0034 :=
    @g_n_3bitr4ri (.classEq (syn_cproj1 (.cv t)) (syn_cop (.cv n) (.cv n)))
      (syn_wex m (syn_wa (.classEq (.cv m) (syn_cproj1 (.cv t)))
          (.classEq (.cv m) (syn_cop (.cv n) (.cv n)))))
      (syn_wbr (.cv t) (syn_c1st) (syn_cop (.cv n) (.cv n)))
      (syn_wex m (.classMem (syn_cop (.cv m) (syn_cop (.cv t) (.cv n)))
          (syn_ctxp (syn_ccnv (syn_c1st)) (syn_cin (syn_c1st) (syn_c2nd)))))
      p0010 p0015 p0033
  have p0035 :=
    @g_n_3bitri
      (syn_wbr (.cv t)
        (syn_crn (syn_ctxp (syn_ccnv (syn_c1st)) (syn_cin (syn_c1st) (syn_c2nd)))) (.cv n))
      (.classMem (syn_cop (.cv t) (.cv n))
        (syn_crn (syn_ctxp (syn_ccnv (syn_c1st)) (syn_cin (syn_c1st) (syn_c2nd)))))
      (syn_wex m (.classMem (syn_cop (.cv m) (syn_cop (.cv t) (.cv n)))
          (syn_ctxp (syn_ccnv (syn_c1st)) (syn_cin (syn_c1st) (syn_c2nd)))))
      (syn_wbr (.cv t) (syn_c1st) (syn_cop (.cv n) (.cv n))) p0006 p0007 p0034
  have p0036 :=
    @g_anbi1i
      (syn_wbr (.cv t)
        (syn_crn (syn_ctxp (syn_ccnv (syn_c1st)) (syn_cin (syn_c1st) (syn_c2nd)))) (.cv n))
      (syn_wbr (.cv t) (syn_c1st) (syn_cop (.cv n) (.cv n)))
      (syn_wbr (.cv t) (syn_c2nd) (.cv m)) p0035
  have p0037 := @g_opex (.cv n) (.cv n) p0028 p0028
  have p0038 := @g_vex m
  have p0039 := @g_op1st2nd (syn_cop (.cv n) (.cv n)) (.cv m) (.cv t) p0037 p0038
  have p0040 :=
    @g_n_3bitri
      (syn_wbr (.cv t) (syn_ctxp
          (syn_crn (syn_ctxp (syn_ccnv (syn_c1st)) (syn_cin (syn_c1st) (syn_c2nd)))) (syn_c2nd))
        (syn_cop (.cv n) (.cv m)))
      (syn_wa (syn_wbr (.cv t)
          (syn_crn (syn_ctxp (syn_ccnv (syn_c1st)) (syn_cin (syn_c1st) (syn_c2nd)))) (.cv n))
        (syn_wbr (.cv t) (syn_c2nd) (.cv m)))
      (syn_wa (syn_wbr (.cv t) (syn_c1st) (syn_cop (.cv n) (.cv n)))
        (syn_wbr (.cv t) (syn_c2nd) (.cv m)))
      (.classEq (.cv t) (syn_cop (syn_cop (.cv n) (.cv n)) (.cv m))) p0005 p0036 p0039
  have p0041 :=
    @g_rexbii
      (syn_wbr (.cv t) (syn_ctxp
          (syn_crn (syn_ctxp (syn_ccnv (syn_c1st)) (syn_cin (syn_c1st) (syn_c2nd)))) (syn_c2nd))
        (syn_cop (.cv n) (.cv m)))
      (.classEq (.cv t) (syn_cop (syn_cop (.cv n) (.cv n)) (.cv m))) t (syn_caddcfn) p0040
  have p0042 :=
    @g_elima t (syn_cop (.cv n) (.cv m))
      (syn_ctxp (syn_crn (syn_ctxp (syn_ccnv (syn_c1st)) (syn_cin (syn_c1st) (syn_c2nd))))
        (syn_c2nd))
      (syn_caddcfn) dv_cache_0007 dv_cache_0008 dv_cache_0009
  have p0043 :=
    (Nominal.biimpRefl (syn_wbr (syn_cop (.cv n) (.cv n)) (syn_caddcfn) (.cv m)))
  have p0044 :=
    @g_risset t (syn_cop (syn_cop (.cv n) (.cv n)) (.cv m)) (syn_caddcfn) dv_cache_0010
      dv_cache_0009
  have p0045 :=
    @g_bitri (syn_wbr (syn_cop (.cv n) (.cv n)) (syn_caddcfn) (.cv m))
      (.classMem (syn_cop (syn_cop (.cv n) (.cv n)) (.cv m)) (syn_caddcfn))
      (syn_wrex t (syn_caddcfn) (.classEq (.cv t) (syn_cop (syn_cop (.cv n) (.cv n)) (.cv m))))
      p0043 p0044
  have p0046 :=
    @g_n_3bitr4i
      (syn_wrex t (syn_caddcfn) (syn_wbr (.cv t) (syn_ctxp
            (syn_crn (syn_ctxp (syn_ccnv (syn_c1st)) (syn_cin (syn_c1st) (syn_c2nd))))
            (syn_c2nd)) (syn_cop (.cv n) (.cv m))))
      (syn_wrex t (syn_caddcfn) (.classEq (.cv t) (syn_cop (syn_cop (.cv n) (.cv n)) (.cv m))))
      (.classMem (syn_cop (.cv n) (.cv m)) (syn_cima (syn_ctxp
            (syn_crn (syn_ctxp (syn_ccnv (syn_c1st)) (syn_cin (syn_c1st) (syn_c2nd))))
            (syn_c2nd)) (syn_caddcfn)))
      (syn_wbr (syn_cop (.cv n) (.cv n)) (syn_caddcfn) (.cv m)) p0041 p0042 p0045
  have p0047 := @g_braddcfn (.cv n) (.cv n) (.cv m) p0028 p0028
  have p0048 := @g_eqcom (syn_cplc (.cv n) (.cv n)) (.cv m)
  have p0049 :=
    @g_n_3bitri
      (.classMem (syn_cop (.cv n) (.cv m)) (syn_cima (syn_ctxp
            (syn_crn (syn_ctxp (syn_ccnv (syn_c1st)) (syn_cin (syn_c1st) (syn_c2nd))))
            (syn_c2nd)) (syn_caddcfn)))
      (syn_wbr (syn_cop (.cv n) (.cv n)) (syn_caddcfn) (.cv m))
      (.classEq (syn_cplc (.cv n) (.cv n)) (.cv m))
      (.classEq (.cv m) (syn_cplc (.cv n) (.cv n))) p0046 p0047 p0048
  have p0050 :=
    @g_n_3bitri
      (.classMem (syn_cop (.cv m) (syn_cop (.cv n) (.cv b))) (syn_cins3 (syn_ccnv (syn_cima
              (syn_ctxp
                (syn_crn (syn_ctxp (syn_ccnv (syn_c1st)) (syn_cin (syn_c1st) (syn_c2nd))))
                (syn_c2nd)) (syn_caddcfn)))))
      (.classMem (syn_cop (.cv m) (.cv n)) (syn_ccnv (syn_cima (syn_ctxp
              (syn_crn (syn_ctxp (syn_ccnv (syn_c1st)) (syn_cin (syn_c1st) (syn_c2nd))))
              (syn_c2nd)) (syn_caddcfn))))
      (.classMem (syn_cop (.cv n) (.cv m)) (syn_cima (syn_ctxp
            (syn_crn (syn_ctxp (syn_ccnv (syn_c1st)) (syn_cin (syn_c1st) (syn_c2nd))))
            (syn_c2nd)) (syn_caddcfn)))
      (.classEq (.cv m) (syn_cplc (.cv n) (.cv n))) p0003 p0004 p0049
  have p0051 :=
    @g_elima t (syn_cop (.cv m) (syn_cop (.cv n) (.cv b)))
      (syn_ctxp (syn_ccom (syn_c1st) (syn_c1st))
        (syn_ctxp (syn_ccom (syn_c2nd) (syn_c1st)) (syn_c2nd)))
      (syn_caddcfn) dv_cache_0011 dv_cache_0012 dv_cache_0009
  have p0052 :=
    @g_trtxp (.cv t) (.cv m) (syn_cop (.cv n) (.cv b)) (syn_ccom (syn_c1st) (syn_c1st))
      (syn_ctxp (syn_ccom (syn_c2nd) (syn_c1st)) (syn_c2nd))
  have p0053 :=
    @g_trtxp (.cv t) (.cv n) (.cv b) (syn_ccom (syn_c2nd) (syn_c1st)) (syn_c2nd)
  have p0054 :=
    @g_anbi2i
      (syn_wbr (.cv t) (syn_ctxp (syn_ccom (syn_c2nd) (syn_c1st)) (syn_c2nd))
        (syn_cop (.cv n) (.cv b)))
      (syn_wa (syn_wbr (.cv t) (syn_ccom (syn_c2nd) (syn_c1st)) (.cv n))
        (syn_wbr (.cv t) (syn_c2nd) (.cv b)))
      (syn_wbr (.cv t) (syn_ccom (syn_c1st) (syn_c1st)) (.cv m)) p0053
  have p0055 :=
    @g_anass (syn_wbr (.cv t) (syn_ccom (syn_c1st) (syn_c1st)) (.cv m))
      (syn_wbr (.cv t) (syn_ccom (syn_c2nd) (syn_c1st)) (.cv n))
      (syn_wbr (.cv t) (syn_c2nd) (.cv b))
  have p0056 := @g_op1st2nd (.cv m) (.cv n) (syn_cproj1 (.cv t)) p0038 p0028
  have p0057 :=
    @g_brco n (.cv t) (.cv m) (syn_c1st) (syn_c1st) dv_cache_0013 dv_cache_0014
      dv_cache_0015 dv_cache_0015
  have p0058 :=
    @g_breq1i (.cv t) (syn_cop (syn_cproj1 (.cv t)) (syn_cproj2 (.cv t))) (.cv n)
      (syn_c1st) p0011
  have p0059 := @g_opbr1st (syn_cproj1 (.cv t)) (syn_cproj2 (.cv t)) (.cv n) p0009 p0013
  have p0060 := @g_eqcom (syn_cproj1 (.cv t)) (.cv n)
  have p0061 :=
    @g_n_3bitri (syn_wbr (.cv t) (syn_c1st) (.cv n))
      (syn_wbr (syn_cop (syn_cproj1 (.cv t)) (syn_cproj2 (.cv t))) (syn_c1st) (.cv n))
      (.classEq (syn_cproj1 (.cv t)) (.cv n)) (.classEq (.cv n) (syn_cproj1 (.cv t)))
      p0058 p0059 p0060
  have p0062 :=
    @g_anbi1i (syn_wbr (.cv t) (syn_c1st) (.cv n)) (.classEq (.cv n) (syn_cproj1 (.cv t)))
      (syn_wbr (.cv n) (syn_c1st) (.cv m)) p0061
  have p0063 :=
    @g_exbii
      (syn_wa (syn_wbr (.cv t) (syn_c1st) (.cv n)) (syn_wbr (.cv n) (syn_c1st) (.cv m)))
      (syn_wa (.classEq (.cv n) (syn_cproj1 (.cv t))) (syn_wbr (.cv n) (syn_c1st) (.cv m)))
      n p0062
  have p0064 := @g_breq1 (.cv n) (syn_cproj1 (.cv t)) (.cv m) (syn_c1st)
  have p0065 :=
    @g_ceqsexv (syn_wbr (.cv n) (syn_c1st) (.cv m))
      (syn_wbr (syn_cproj1 (.cv t)) (syn_c1st) (.cv m)) n (syn_cproj1 (.cv t))
      dv_cache_0016 dv_cache_0017 p0009 p0064
  have p0066 :=
    @g_n_3bitri (syn_wbr (.cv t) (syn_ccom (syn_c1st) (syn_c1st)) (.cv m))
      (syn_wex n (syn_wa (syn_wbr (.cv t) (syn_c1st) (.cv n))
          (syn_wbr (.cv n) (syn_c1st) (.cv m))))
      (syn_wex n (syn_wa (.classEq (.cv n) (syn_cproj1 (.cv t)))
          (syn_wbr (.cv n) (syn_c1st) (.cv m))))
      (syn_wbr (syn_cproj1 (.cv t)) (syn_c1st) (.cv m)) p0057 p0063 p0065
  have p0067 :=
    @g_brco m (.cv t) (.cv n) (syn_c2nd) (syn_c1st) dv_cache_0018 dv_cache_0019
      dv_cache_0020 dv_cache_0021
  have p0068 :=
    @g_anbi1i (syn_wbr (.cv t) (syn_c1st) (.cv m)) (.classEq (.cv m) (syn_cproj1 (.cv t)))
      (syn_wbr (.cv m) (syn_c2nd) (.cv n)) p0022
  have p0069 :=
    @g_exbii
      (syn_wa (syn_wbr (.cv t) (syn_c1st) (.cv m)) (syn_wbr (.cv m) (syn_c2nd) (.cv n)))
      (syn_wa (.classEq (.cv m) (syn_cproj1 (.cv t))) (syn_wbr (.cv m) (syn_c2nd) (.cv n)))
      m p0068
  have p0070 := @g_breq1 (.cv m) (syn_cproj1 (.cv t)) (.cv n) (syn_c2nd)
  have p0071 :=
    @g_ceqsexv (syn_wbr (.cv m) (syn_c2nd) (.cv n))
      (syn_wbr (syn_cproj1 (.cv t)) (syn_c2nd) (.cv n)) m (syn_cproj1 (.cv t))
      dv_cache_0005 dv_cache_0022 p0009 p0070
  have p0072 :=
    @g_n_3bitri (syn_wbr (.cv t) (syn_ccom (syn_c2nd) (syn_c1st)) (.cv n))
      (syn_wex m (syn_wa (syn_wbr (.cv t) (syn_c1st) (.cv m))
          (syn_wbr (.cv m) (syn_c2nd) (.cv n))))
      (syn_wex m (syn_wa (.classEq (.cv m) (syn_cproj1 (.cv t)))
          (syn_wbr (.cv m) (syn_c2nd) (.cv n))))
      (syn_wbr (syn_cproj1 (.cv t)) (syn_c2nd) (.cv n)) p0067 p0069 p0071
  have p0073 :=
    @g_anbi12i (syn_wbr (.cv t) (syn_ccom (syn_c1st) (syn_c1st)) (.cv m))
      (syn_wbr (syn_cproj1 (.cv t)) (syn_c1st) (.cv m))
      (syn_wbr (.cv t) (syn_ccom (syn_c2nd) (syn_c1st)) (.cv n))
      (syn_wbr (syn_cproj1 (.cv t)) (syn_c2nd) (.cv n)) p0066 p0072
  have p0074 :=
    @g_breq1i (.cv t) (syn_cop (syn_cproj1 (.cv t)) (syn_cproj2 (.cv t)))
      (syn_cop (.cv m) (.cv n)) (syn_c1st) p0011
  have p0075 :=
    @g_opbr1st (syn_cproj1 (.cv t)) (syn_cproj2 (.cv t)) (syn_cop (.cv m) (.cv n)) p0009
      p0013
  have p0076 :=
    @g_bitri (syn_wbr (.cv t) (syn_c1st) (syn_cop (.cv m) (.cv n)))
      (syn_wbr (syn_cop (syn_cproj1 (.cv t)) (syn_cproj2 (.cv t))) (syn_c1st)
        (syn_cop (.cv m) (.cv n)))
      (.classEq (syn_cproj1 (.cv t)) (syn_cop (.cv m) (.cv n))) p0074 p0075
  have p0077 :=
    @g_n_3bitr4i
      (syn_wa (syn_wbr (syn_cproj1 (.cv t)) (syn_c1st) (.cv m))
        (syn_wbr (syn_cproj1 (.cv t)) (syn_c2nd) (.cv n)))
      (.classEq (syn_cproj1 (.cv t)) (syn_cop (.cv m) (.cv n)))
      (syn_wa (syn_wbr (.cv t) (syn_ccom (syn_c1st) (syn_c1st)) (.cv m))
        (syn_wbr (.cv t) (syn_ccom (syn_c2nd) (syn_c1st)) (.cv n)))
      (syn_wbr (.cv t) (syn_c1st) (syn_cop (.cv m) (.cv n))) p0056 p0073 p0076
  have p0078 :=
    @g_anbi1i
      (syn_wa (syn_wbr (.cv t) (syn_ccom (syn_c1st) (syn_c1st)) (.cv m))
        (syn_wbr (.cv t) (syn_ccom (syn_c2nd) (syn_c1st)) (.cv n)))
      (syn_wbr (.cv t) (syn_c1st) (syn_cop (.cv m) (.cv n)))
      (syn_wbr (.cv t) (syn_c2nd) (.cv b)) p0077
  have p0079 :=
    @g_n_3bitr2i
      (syn_wa (syn_wbr (.cv t) (syn_ccom (syn_c1st) (syn_c1st)) (.cv m))
        (syn_wbr (.cv t) (syn_ctxp (syn_ccom (syn_c2nd) (syn_c1st)) (syn_c2nd))
          (syn_cop (.cv n) (.cv b))))
      (syn_wa (syn_wbr (.cv t) (syn_ccom (syn_c1st) (syn_c1st)) (.cv m))
        (syn_wa (syn_wbr (.cv t) (syn_ccom (syn_c2nd) (syn_c1st)) (.cv n))
          (syn_wbr (.cv t) (syn_c2nd) (.cv b))))
      (syn_wa (syn_wa (syn_wbr (.cv t) (syn_ccom (syn_c1st) (syn_c1st)) (.cv m))
          (syn_wbr (.cv t) (syn_ccom (syn_c2nd) (syn_c1st)) (.cv n)))
        (syn_wbr (.cv t) (syn_c2nd) (.cv b)))
      (syn_wa (syn_wbr (.cv t) (syn_c1st) (syn_cop (.cv m) (.cv n)))
        (syn_wbr (.cv t) (syn_c2nd) (.cv b)))
      p0054 p0055 p0078
  have p0080 := @g_opex (.cv m) (.cv n) p0038 p0028
  have p0081 := @g_op1st2nd (syn_cop (.cv m) (.cv n)) (.cv b) (.cv t) p0080 p0002
  have p0082 :=
    @g_n_3bitri
      (syn_wbr (.cv t) (syn_ctxp (syn_ccom (syn_c1st) (syn_c1st))
          (syn_ctxp (syn_ccom (syn_c2nd) (syn_c1st)) (syn_c2nd)))
        (syn_cop (.cv m) (syn_cop (.cv n) (.cv b))))
      (syn_wa (syn_wbr (.cv t) (syn_ccom (syn_c1st) (syn_c1st)) (.cv m))
        (syn_wbr (.cv t) (syn_ctxp (syn_ccom (syn_c2nd) (syn_c1st)) (syn_c2nd))
          (syn_cop (.cv n) (.cv b))))
      (syn_wa (syn_wbr (.cv t) (syn_c1st) (syn_cop (.cv m) (.cv n)))
        (syn_wbr (.cv t) (syn_c2nd) (.cv b)))
      (.classEq (.cv t) (syn_cop (syn_cop (.cv m) (.cv n)) (.cv b))) p0052 p0079 p0081
  have p0083 :=
    @g_rexbii
      (syn_wbr (.cv t) (syn_ctxp (syn_ccom (syn_c1st) (syn_c1st))
          (syn_ctxp (syn_ccom (syn_c2nd) (syn_c1st)) (syn_c2nd)))
        (syn_cop (.cv m) (syn_cop (.cv n) (.cv b))))
      (.classEq (.cv t) (syn_cop (syn_cop (.cv m) (.cv n)) (.cv b))) t (syn_caddcfn) p0082
  have p0084 :=
    @g_bitri
      (.classMem (syn_cop (.cv m) (syn_cop (.cv n) (.cv b))) (syn_cima
          (syn_ctxp (syn_ccom (syn_c1st) (syn_c1st))
            (syn_ctxp (syn_ccom (syn_c2nd) (syn_c1st)) (syn_c2nd))) (syn_caddcfn)))
      (syn_wrex t (syn_caddcfn) (syn_wbr (.cv t) (syn_ctxp (syn_ccom (syn_c1st) (syn_c1st))
            (syn_ctxp (syn_ccom (syn_c2nd) (syn_c1st)) (syn_c2nd)))
          (syn_cop (.cv m) (syn_cop (.cv n) (.cv b)))))
      (syn_wrex t (syn_caddcfn) (.classEq (.cv t) (syn_cop (syn_cop (.cv m) (.cv n)) (.cv b))))
      p0051 p0083
  have p0085 :=
    (Nominal.biimpRefl (syn_wbr (syn_cop (.cv m) (.cv n)) (syn_caddcfn) (.cv b)))
  have p0086 :=
    @g_risset t (syn_cop (syn_cop (.cv m) (.cv n)) (.cv b)) (syn_caddcfn) dv_cache_0023
      dv_cache_0009
  have p0087 :=
    @g_bitr2i (syn_wbr (syn_cop (.cv m) (.cv n)) (syn_caddcfn) (.cv b))
      (.classMem (syn_cop (syn_cop (.cv m) (.cv n)) (.cv b)) (syn_caddcfn))
      (syn_wrex t (syn_caddcfn) (.classEq (.cv t) (syn_cop (syn_cop (.cv m) (.cv n)) (.cv b))))
      p0085 p0086
  have p0088 := @g_braddcfn (.cv m) (.cv n) (.cv b) p0038 p0028
  have p0089 := @g_eqcom (syn_cplc (.cv m) (.cv n)) (.cv b)
  have p0090 :=
    @g_bitri (syn_wbr (syn_cop (.cv m) (.cv n)) (syn_caddcfn) (.cv b))
      (.classEq (syn_cplc (.cv m) (.cv n)) (.cv b))
      (.classEq (.cv b) (syn_cplc (.cv m) (.cv n))) p0088 p0089
  have p0091 :=
    @g_n_3bitri
      (.classMem (syn_cop (.cv m) (syn_cop (.cv n) (.cv b))) (syn_cima
          (syn_ctxp (syn_ccom (syn_c1st) (syn_c1st))
            (syn_ctxp (syn_ccom (syn_c2nd) (syn_c1st)) (syn_c2nd))) (syn_caddcfn)))
      (syn_wrex t (syn_caddcfn) (.classEq (.cv t) (syn_cop (syn_cop (.cv m) (.cv n)) (.cv b))))
      (syn_wbr (syn_cop (.cv m) (.cv n)) (syn_caddcfn) (.cv b))
      (.classEq (.cv b) (syn_cplc (.cv m) (.cv n))) p0084 p0087 p0090
  have p0092 :=
    @g_anbi12i
      (.classMem (syn_cop (.cv m) (syn_cop (.cv n) (.cv b))) (syn_cins3 (syn_ccnv (syn_cima
              (syn_ctxp
                (syn_crn (syn_ctxp (syn_ccnv (syn_c1st)) (syn_cin (syn_c1st) (syn_c2nd))))
                (syn_c2nd)) (syn_caddcfn)))))
      (.classEq (.cv m) (syn_cplc (.cv n) (.cv n)))
      (.classMem (syn_cop (.cv m) (syn_cop (.cv n) (.cv b))) (syn_cima
          (syn_ctxp (syn_ccom (syn_c1st) (syn_c1st))
            (syn_ctxp (syn_ccom (syn_c2nd) (syn_c1st)) (syn_c2nd))) (syn_caddcfn)))
      (.classEq (.cv b) (syn_cplc (.cv m) (.cv n))) p0050 p0091
  have p0093 :=
    @g_bitri
      (.classMem (syn_cop (.cv m) (syn_cop (.cv n) (.cv b))) (syn_cin (syn_cins3 (syn_ccnv
              (syn_cima (syn_ctxp (syn_crn
                    (syn_ctxp (syn_ccnv (syn_c1st)) (syn_cin (syn_c1st) (syn_c2nd))))
                  (syn_c2nd)) (syn_caddcfn)))) (syn_cima
            (syn_ctxp (syn_ccom (syn_c1st) (syn_c1st))
              (syn_ctxp (syn_ccom (syn_c2nd) (syn_c1st)) (syn_c2nd))) (syn_caddcfn))))
      (syn_wa (.classMem (syn_cop (.cv m) (syn_cop (.cv n) (.cv b))) (syn_cins3 (syn_ccnv
              (syn_cima (syn_ctxp (syn_crn
                    (syn_ctxp (syn_ccnv (syn_c1st)) (syn_cin (syn_c1st) (syn_c2nd))))
                  (syn_c2nd)) (syn_caddcfn)))))
        (.classMem (syn_cop (.cv m) (syn_cop (.cv n) (.cv b))) (syn_cima
            (syn_ctxp (syn_ccom (syn_c1st) (syn_c1st))
              (syn_ctxp (syn_ccom (syn_c2nd) (syn_c1st)) (syn_c2nd))) (syn_caddcfn))))
      (syn_wa (.classEq (.cv m) (syn_cplc (.cv n) (.cv n)))
        (.classEq (.cv b) (syn_cplc (.cv m) (.cv n))))
      p0001 p0092
  have p0094 :=
    @g_exbii
      (.classMem (syn_cop (.cv m) (syn_cop (.cv n) (.cv b))) (syn_cin (syn_cins3 (syn_ccnv
              (syn_cima (syn_ctxp (syn_crn
                    (syn_ctxp (syn_ccnv (syn_c1st)) (syn_cin (syn_c1st) (syn_c2nd))))
                  (syn_c2nd)) (syn_caddcfn)))) (syn_cima
            (syn_ctxp (syn_ccom (syn_c1st) (syn_c1st))
              (syn_ctxp (syn_ccom (syn_c2nd) (syn_c1st)) (syn_c2nd))) (syn_caddcfn))))
      (syn_wa (.classEq (.cv m) (syn_cplc (.cv n) (.cv n)))
        (.classEq (.cv b) (syn_cplc (.cv m) (.cv n))))
      m p0093
  have p0095 := @g_addcex (.cv n) (.cv n) p0028 p0028
  have p0096 := @g_addceq1 (.cv m) (syn_cplc (.cv n) (.cv n)) (.cv n)
  have p0097 :=
    @g_eqeq2d (.classEq (.cv m) (syn_cplc (.cv n) (.cv n))) (syn_cplc (.cv m) (.cv n))
      (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n)) (.cv b) p0096
  have p0098 :=
    @g_ceqsexv (.classEq (.cv b) (syn_cplc (.cv m) (.cv n)))
      (.classEq (.cv b) (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n))) m
      (syn_cplc (.cv n) (.cv n)) dv_cache_0024 dv_cache_0025 p0095 p0097
  have p0099 :=
    @g_n_3bitri
      (.classMem (syn_cop (.cv n) (.cv b)) (syn_crn (syn_cin (syn_cins3 (syn_ccnv (syn_cima
                  (syn_ctxp (syn_crn
                      (syn_ctxp (syn_ccnv (syn_c1st)) (syn_cin (syn_c1st) (syn_c2nd))))
                    (syn_c2nd)) (syn_caddcfn)))) (syn_cima
              (syn_ctxp (syn_ccom (syn_c1st) (syn_c1st))
                (syn_ctxp (syn_ccom (syn_c2nd) (syn_c1st)) (syn_c2nd))) (syn_caddcfn)))))
      (syn_wex m (.classMem (syn_cop (.cv m) (syn_cop (.cv n) (.cv b))) (syn_cin (syn_cins3
              (syn_ccnv (syn_cima (syn_ctxp (syn_crn
                      (syn_ctxp (syn_ccnv (syn_c1st)) (syn_cin (syn_c1st) (syn_c2nd))))
                    (syn_c2nd)) (syn_caddcfn)))) (syn_cima
              (syn_ctxp (syn_ccom (syn_c1st) (syn_c1st))
                (syn_ctxp (syn_ccom (syn_c2nd) (syn_c1st)) (syn_c2nd))) (syn_caddcfn)))))
      (syn_wex m (syn_wa (.classEq (.cv m) (syn_cplc (.cv n) (.cv n)))
          (.classEq (.cv b) (syn_cplc (.cv m) (.cv n)))))
      (.classEq (.cv b) (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n))) p0000 p0094 p0098
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

@[expose]
noncomputable def g_nncdiv3lem2 (n : Var) (a : Var) (dv_a_n : a ≠ n) :
    Nominal.NPrf
      (.classMem (.cab a (syn_wrex n (syn_cnnc)
            (syn_w3o (.classEq (.cv a) (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n)))
              (.classEq (.cv a)
                (syn_cplc (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n)) (syn_c1c)))
              (.classEq (.cv a)
                (syn_cplc (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n)) (syn_c2c))))))
        (syn_cvv)) :=
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
      ((syn_cun (syn_cun (syn_crn (syn_cin (syn_cins3 (syn_ccnv (syn_cima (syn_ctxp (syn_crn
                          (syn_ctxp (syn_ccnv (syn_c1st)) (syn_cin (syn_c1st) (syn_c2nd))))
                        (syn_c2nd)) (syn_caddcfn)))) (syn_cima
                  (syn_ctxp (syn_ccom (syn_c1st) (syn_c1st))
                    (syn_ctxp (syn_ccom (syn_c2nd) (syn_c1st)) (syn_c2nd))) (syn_caddcfn))))
            (syn_crn (syn_ctxp (syn_ccnv (syn_crn (syn_cin (syn_cins3 (syn_ccnv (syn_cima
                            (syn_ctxp (syn_crn (syn_ctxp (syn_ccnv (syn_c1st))
                                  (syn_cin (syn_c1st) (syn_c2nd)))) (syn_c2nd)) (syn_caddcfn))))
                      (syn_cima (syn_ctxp (syn_ccom (syn_c1st) (syn_c1st))
                          (syn_ctxp (syn_ccom (syn_c2nd) (syn_c1st)) (syn_c2nd)))
                        (syn_caddcfn))))) (syn_crn (syn_ctxp (syn_cin (syn_c1st)
                      (syn_cxp (syn_cima (syn_ccnv (syn_c2nd)) (syn_csn (syn_c1c))) (syn_cvv)))
                    (syn_caddcfn)))))) (syn_crn (syn_ctxp (syn_ccnv (syn_crn (syn_cin (syn_cins3
                      (syn_ccnv (syn_cima (syn_ctxp (syn_crn (syn_ctxp (syn_ccnv (syn_c1st))
                                (syn_cin (syn_c1st) (syn_c2nd)))) (syn_c2nd)) (syn_caddcfn))))
                    (syn_cima (syn_ctxp (syn_ccom (syn_c1st) (syn_c1st))
                        (syn_ctxp (syn_ccom (syn_c2nd) (syn_c1st)) (syn_c2nd)))
                      (syn_caddcfn))))) (syn_crn (syn_ctxp (syn_cin (syn_c1st)
                    (syn_cxp (syn_cima (syn_ccnv (syn_c2nd)) (syn_csn (syn_c2c))) (syn_cvv)))
                  (syn_caddcfn))))))).fv :=
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
  have dv_cache_0003 : n ∉ ((syn_cnnc)).fv :=
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
  have dv_cache_0004 : b ∉ ((syn_cop (.cv n) (.cv a))).fv :=
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
      ((syn_ctxp (syn_ccnv (syn_crn (syn_cin (syn_cins3 (syn_ccnv (syn_cima (syn_ctxp (syn_crn
                          (syn_ctxp (syn_ccnv (syn_c1st)) (syn_cin (syn_c1st) (syn_c2nd))))
                        (syn_c2nd)) (syn_caddcfn)))) (syn_cima
                  (syn_ctxp (syn_ccom (syn_c1st) (syn_c1st))
                    (syn_ctxp (syn_ccom (syn_c2nd) (syn_c1st)) (syn_c2nd))) (syn_caddcfn)))))
          (syn_crn (syn_ctxp (syn_cin (syn_c1st)
                (syn_cxp (syn_cima (syn_ccnv (syn_c2nd)) (syn_csn (syn_c1c))) (syn_cvv)))
              (syn_caddcfn))))).fv :=
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
  have dv_cache_0006 : n ∉ ((syn_cop (.cv b) (.cv a))).fv :=
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
      ((syn_ctxp (syn_cin (syn_c1st)
            (syn_cxp (syn_cima (syn_ccnv (syn_c2nd)) (syn_csn (syn_c1c))) (syn_cvv)))
          (syn_caddcfn))).fv :=
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
  have dv_cache_0008 : n ∉ ((syn_cop (.cv b) (syn_c1c))).fv :=
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
    n ∉ ((syn_wbr (syn_cop (.cv b) (syn_c1c)) (syn_caddcfn) (.cv a))).fv :=
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
  have dv_cache_0010 : b ∉ ((syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n))).fv :=
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
          (syn_cplc (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n)) (syn_c1c)))).fv :=
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
      ((syn_ctxp (syn_ccnv (syn_crn (syn_cin (syn_cins3 (syn_ccnv (syn_cima (syn_ctxp (syn_crn
                          (syn_ctxp (syn_ccnv (syn_c1st)) (syn_cin (syn_c1st) (syn_c2nd))))
                        (syn_c2nd)) (syn_caddcfn)))) (syn_cima
                  (syn_ctxp (syn_ccom (syn_c1st) (syn_c1st))
                    (syn_ctxp (syn_ccom (syn_c2nd) (syn_c1st)) (syn_c2nd))) (syn_caddcfn)))))
          (syn_crn (syn_ctxp (syn_cin (syn_c1st)
                (syn_cxp (syn_cima (syn_ccnv (syn_c2nd)) (syn_csn (syn_c2c))) (syn_cvv)))
              (syn_caddcfn))))).fv :=
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
      ((syn_ctxp (syn_cin (syn_c1st)
            (syn_cxp (syn_cima (syn_ccnv (syn_c2nd)) (syn_csn (syn_c2c))) (syn_cvv)))
          (syn_caddcfn))).fv :=
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
  have dv_cache_0014 : n ∉ ((syn_cop (.cv b) (syn_c2c))).fv :=
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
    n ∉ ((syn_wbr (syn_cop (.cv b) (syn_c2c)) (syn_caddcfn) (.cv a))).fv :=
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
          (syn_cplc (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n)) (syn_c2c)))).fv :=
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
      ((syn_cima (syn_cun (syn_cun (syn_crn (syn_cin (syn_cins3 (syn_ccnv (syn_cima (syn_ctxp
                          (syn_crn (syn_ctxp (syn_ccnv (syn_c1st))
                              (syn_cin (syn_c1st) (syn_c2nd)))) (syn_c2nd)) (syn_caddcfn))))
                  (syn_cima (syn_ctxp (syn_ccom (syn_c1st) (syn_c1st))
                      (syn_ctxp (syn_ccom (syn_c2nd) (syn_c1st)) (syn_c2nd))) (syn_caddcfn))))
              (syn_crn (syn_ctxp (syn_ccnv (syn_crn (syn_cin (syn_cins3 (syn_ccnv (syn_cima
                              (syn_ctxp (syn_crn (syn_ctxp (syn_ccnv (syn_c1st))
                                    (syn_cin (syn_c1st) (syn_c2nd)))) (syn_c2nd))
                              (syn_caddcfn)))) (syn_cima
                          (syn_ctxp (syn_ccom (syn_c1st) (syn_c1st))
                            (syn_ctxp (syn_ccom (syn_c2nd) (syn_c1st)) (syn_c2nd)))
                          (syn_caddcfn))))) (syn_crn (syn_ctxp (syn_cin (syn_c1st)
                        (syn_cxp (syn_cima (syn_ccnv (syn_c2nd)) (syn_csn (syn_c1c)))
                          (syn_cvv))) (syn_caddcfn)))))) (syn_crn (syn_ctxp (syn_ccnv (syn_crn
                    (syn_cin (syn_cins3 (syn_ccnv (syn_cima (syn_ctxp (syn_crn
                                (syn_ctxp (syn_ccnv (syn_c1st))
                                  (syn_cin (syn_c1st) (syn_c2nd)))) (syn_c2nd)) (syn_caddcfn))))
                      (syn_cima (syn_ctxp (syn_ccom (syn_c1st) (syn_c1st))
                          (syn_ctxp (syn_ccom (syn_c2nd) (syn_c1st)) (syn_c2nd)))
                        (syn_caddcfn))))) (syn_crn (syn_ctxp (syn_cin (syn_c1st)
                      (syn_cxp (syn_cima (syn_ccnv (syn_c2nd)) (syn_csn (syn_c2c))) (syn_cvv)))
                    (syn_caddcfn)))))) (syn_cnnc))).fv :=
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
    @g_elima n (.cv a)
      (syn_cun (syn_cun (syn_crn (syn_cin (syn_cins3 (syn_ccnv (syn_cima (syn_ctxp (syn_crn
                        (syn_ctxp (syn_ccnv (syn_c1st)) (syn_cin (syn_c1st) (syn_c2nd))))
                      (syn_c2nd)) (syn_caddcfn)))) (syn_cima
                (syn_ctxp (syn_ccom (syn_c1st) (syn_c1st))
                  (syn_ctxp (syn_ccom (syn_c2nd) (syn_c1st)) (syn_c2nd))) (syn_caddcfn))))
          (syn_crn (syn_ctxp (syn_ccnv (syn_crn (syn_cin (syn_cins3 (syn_ccnv (syn_cima
                          (syn_ctxp (syn_crn (syn_ctxp (syn_ccnv (syn_c1st))
                                (syn_cin (syn_c1st) (syn_c2nd)))) (syn_c2nd)) (syn_caddcfn))))
                    (syn_cima (syn_ctxp (syn_ccom (syn_c1st) (syn_c1st))
                        (syn_ctxp (syn_ccom (syn_c2nd) (syn_c1st)) (syn_c2nd)))
                      (syn_caddcfn))))) (syn_crn (syn_ctxp (syn_cin (syn_c1st)
                    (syn_cxp (syn_cima (syn_ccnv (syn_c2nd)) (syn_csn (syn_c1c))) (syn_cvv)))
                  (syn_caddcfn)))))) (syn_crn (syn_ctxp (syn_ccnv (syn_crn (syn_cin (syn_cins3
                    (syn_ccnv (syn_cima (syn_ctxp (syn_crn (syn_ctxp (syn_ccnv (syn_c1st))
                              (syn_cin (syn_c1st) (syn_c2nd)))) (syn_c2nd)) (syn_caddcfn))))
                  (syn_cima (syn_ctxp (syn_ccom (syn_c1st) (syn_c1st))
                      (syn_ctxp (syn_ccom (syn_c2nd) (syn_c1st)) (syn_c2nd))) (syn_caddcfn)))))
            (syn_crn (syn_ctxp (syn_cin (syn_c1st)
                  (syn_cxp (syn_cima (syn_ccnv (syn_c2nd)) (syn_csn (syn_c2c))) (syn_cvv)))
                (syn_caddcfn))))))
      (syn_cnnc) dv_cache_0001 dv_cache_0002 dv_cache_0003
  have p0001 :=
    (Nominal.biimpRefl (syn_wbr (.cv n) (syn_cun (syn_cun (syn_crn (syn_cin (syn_cins3 (syn_ccnv
                    (syn_cima (syn_ctxp (syn_crn (syn_ctxp (syn_ccnv (syn_c1st))
                            (syn_cin (syn_c1st) (syn_c2nd)))) (syn_c2nd)) (syn_caddcfn))))
                (syn_cima (syn_ctxp (syn_ccom (syn_c1st) (syn_c1st))
                    (syn_ctxp (syn_ccom (syn_c2nd) (syn_c1st)) (syn_c2nd))) (syn_caddcfn))))
            (syn_crn (syn_ctxp (syn_ccnv (syn_crn (syn_cin (syn_cins3 (syn_ccnv (syn_cima
                            (syn_ctxp (syn_crn (syn_ctxp (syn_ccnv (syn_c1st))
                                  (syn_cin (syn_c1st) (syn_c2nd)))) (syn_c2nd)) (syn_caddcfn))))
                      (syn_cima (syn_ctxp (syn_ccom (syn_c1st) (syn_c1st))
                          (syn_ctxp (syn_ccom (syn_c2nd) (syn_c1st)) (syn_c2nd)))
                        (syn_caddcfn))))) (syn_crn (syn_ctxp (syn_cin (syn_c1st)
                      (syn_cxp (syn_cima (syn_ccnv (syn_c2nd)) (syn_csn (syn_c1c))) (syn_cvv)))
                    (syn_caddcfn)))))) (syn_crn (syn_ctxp (syn_ccnv (syn_crn (syn_cin (syn_cins3
                      (syn_ccnv (syn_cima (syn_ctxp (syn_crn (syn_ctxp (syn_ccnv (syn_c1st))
                                (syn_cin (syn_c1st) (syn_c2nd)))) (syn_c2nd)) (syn_caddcfn))))
                    (syn_cima (syn_ctxp (syn_ccom (syn_c1st) (syn_c1st))
                        (syn_ctxp (syn_ccom (syn_c2nd) (syn_c1st)) (syn_c2nd)))
                      (syn_caddcfn))))) (syn_crn (syn_ctxp (syn_cin (syn_c1st)
                    (syn_cxp (syn_cima (syn_ccnv (syn_c2nd)) (syn_csn (syn_c2c))) (syn_cvv)))
                  (syn_caddcfn)))))) (.cv a)))
  have p0002 :=
    @g_elun (syn_cop (.cv n) (.cv a))
      (syn_crn (syn_cin (syn_cins3 (syn_ccnv (syn_cima (syn_ctxp (syn_crn
                    (syn_ctxp (syn_ccnv (syn_c1st)) (syn_cin (syn_c1st) (syn_c2nd))))
                  (syn_c2nd)) (syn_caddcfn)))) (syn_cima
            (syn_ctxp (syn_ccom (syn_c1st) (syn_c1st))
              (syn_ctxp (syn_ccom (syn_c2nd) (syn_c1st)) (syn_c2nd))) (syn_caddcfn))))
      (syn_crn (syn_ctxp (syn_ccnv (syn_crn (syn_cin (syn_cins3 (syn_ccnv (syn_cima (syn_ctxp
                        (syn_crn (syn_ctxp (syn_ccnv (syn_c1st))
                            (syn_cin (syn_c1st) (syn_c2nd)))) (syn_c2nd)) (syn_caddcfn))))
                (syn_cima (syn_ctxp (syn_ccom (syn_c1st) (syn_c1st))
                    (syn_ctxp (syn_ccom (syn_c2nd) (syn_c1st)) (syn_c2nd))) (syn_caddcfn)))))
          (syn_crn (syn_ctxp (syn_cin (syn_c1st)
                (syn_cxp (syn_cima (syn_ccnv (syn_c2nd)) (syn_csn (syn_c1c))) (syn_cvv)))
              (syn_caddcfn)))))
  have p0003 := @g_nncdiv3lem1 n a
  have p0004 :=
    @g_elrn2 b (syn_cop (.cv n) (.cv a))
      (syn_ctxp (syn_ccnv (syn_crn (syn_cin (syn_cins3 (syn_ccnv (syn_cima (syn_ctxp (syn_crn
                        (syn_ctxp (syn_ccnv (syn_c1st)) (syn_cin (syn_c1st) (syn_c2nd))))
                      (syn_c2nd)) (syn_caddcfn)))) (syn_cima
                (syn_ctxp (syn_ccom (syn_c1st) (syn_c1st))
                  (syn_ctxp (syn_ccom (syn_c2nd) (syn_c1st)) (syn_c2nd))) (syn_caddcfn)))))
        (syn_crn (syn_ctxp (syn_cin (syn_c1st)
              (syn_cxp (syn_cima (syn_ccnv (syn_c2nd)) (syn_csn (syn_c1c))) (syn_cvv)))
            (syn_caddcfn))))
      dv_cache_0004 dv_cache_0005
  have p0005 :=
    @g_oteltxp (.cv b) (.cv n) (.cv a)
      (syn_ccnv (syn_crn (syn_cin (syn_cins3 (syn_ccnv (syn_cima (syn_ctxp (syn_crn
                      (syn_ctxp (syn_ccnv (syn_c1st)) (syn_cin (syn_c1st) (syn_c2nd))))
                    (syn_c2nd)) (syn_caddcfn)))) (syn_cima
              (syn_ctxp (syn_ccom (syn_c1st) (syn_c1st))
                (syn_ctxp (syn_ccom (syn_c2nd) (syn_c1st)) (syn_c2nd))) (syn_caddcfn)))))
      (syn_crn (syn_ctxp (syn_cin (syn_c1st)
            (syn_cxp (syn_cima (syn_ccnv (syn_c2nd)) (syn_csn (syn_c1c))) (syn_cvv)))
          (syn_caddcfn)))
  have p0006 :=
    @g_opelcnv (.cv b) (.cv n)
      (syn_crn (syn_cin (syn_cins3 (syn_ccnv (syn_cima (syn_ctxp (syn_crn
                    (syn_ctxp (syn_ccnv (syn_c1st)) (syn_cin (syn_c1st) (syn_c2nd))))
                  (syn_c2nd)) (syn_caddcfn)))) (syn_cima
            (syn_ctxp (syn_ccom (syn_c1st) (syn_c1st))
              (syn_ctxp (syn_ccom (syn_c2nd) (syn_c1st)) (syn_c2nd))) (syn_caddcfn))))
  have p0007 := @g_nncdiv3lem1 n b
  have p0008 :=
    @g_bitri
      (.classMem (syn_cop (.cv b) (.cv n)) (syn_ccnv (syn_crn (syn_cin (syn_cins3 (syn_ccnv
                  (syn_cima (syn_ctxp (syn_crn
                        (syn_ctxp (syn_ccnv (syn_c1st)) (syn_cin (syn_c1st) (syn_c2nd))))
                      (syn_c2nd)) (syn_caddcfn)))) (syn_cima
                (syn_ctxp (syn_ccom (syn_c1st) (syn_c1st))
                  (syn_ctxp (syn_ccom (syn_c2nd) (syn_c1st)) (syn_c2nd))) (syn_caddcfn))))))
      (.classMem (syn_cop (.cv n) (.cv b)) (syn_crn (syn_cin (syn_cins3 (syn_ccnv (syn_cima
                  (syn_ctxp (syn_crn
                      (syn_ctxp (syn_ccnv (syn_c1st)) (syn_cin (syn_c1st) (syn_c2nd))))
                    (syn_c2nd)) (syn_caddcfn)))) (syn_cima
              (syn_ctxp (syn_ccom (syn_c1st) (syn_c1st))
                (syn_ctxp (syn_ccom (syn_c2nd) (syn_c1st)) (syn_c2nd))) (syn_caddcfn)))))
      (.classEq (.cv b) (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n))) p0006 p0007
  have p0009 :=
    @g_elrn2 n (syn_cop (.cv b) (.cv a))
      (syn_ctxp (syn_cin (syn_c1st)
          (syn_cxp (syn_cima (syn_ccnv (syn_c2nd)) (syn_csn (syn_c1c))) (syn_cvv)))
        (syn_caddcfn))
      dv_cache_0006 dv_cache_0007
  have p0010 :=
    @g_oteltxp (.cv n) (.cv b) (.cv a)
      (syn_cin (syn_c1st)
        (syn_cxp (syn_cima (syn_ccnv (syn_c2nd)) (syn_csn (syn_c1c))) (syn_cvv)))
      (syn_caddcfn)
  have p0011 :=
    @g_elin (syn_cop (.cv n) (.cv b)) (syn_c1st)
      (syn_cxp (syn_cima (syn_ccnv (syn_c2nd)) (syn_csn (syn_c1c))) (syn_cvv))
  have p0012 := (Nominal.biimpRefl (syn_wbr (.cv n) (syn_c1st) (.cv b)))
  have p0013 :=
    @g_bicomi (syn_wbr (.cv n) (syn_c1st) (.cv b))
      (.classMem (syn_cop (.cv n) (.cv b)) (syn_c1st)) p0012
  have p0014 := @g_vex b
  have p0015 :=
    @g_opelxp (.cv n) (.cv b) (syn_cima (syn_ccnv (syn_c2nd)) (syn_csn (syn_c1c)))
      (syn_cvv)
  have p0016 :=
    @g_mpbiran2
      (.classMem (syn_cop (.cv n) (.cv b))
        (syn_cxp (syn_cima (syn_ccnv (syn_c2nd)) (syn_csn (syn_c1c))) (syn_cvv)))
      (.classMem (.cv n) (syn_cima (syn_ccnv (syn_c2nd)) (syn_csn (syn_c1c))))
      (.classMem (.cv b) (syn_cvv)) p0014 p0015
  have p0017 := @g_eliniseg (syn_c2nd) (syn_c1c) (.cv n)
  have p0018 :=
    @g_bitri
      (.classMem (syn_cop (.cv n) (.cv b))
        (syn_cxp (syn_cima (syn_ccnv (syn_c2nd)) (syn_csn (syn_c1c))) (syn_cvv)))
      (.classMem (.cv n) (syn_cima (syn_ccnv (syn_c2nd)) (syn_csn (syn_c1c))))
      (syn_wbr (.cv n) (syn_c2nd) (syn_c1c)) p0016 p0017
  have p0019 :=
    @g_anbi12i (.classMem (syn_cop (.cv n) (.cv b)) (syn_c1st))
      (syn_wbr (.cv n) (syn_c1st) (.cv b))
      (.classMem (syn_cop (.cv n) (.cv b))
        (syn_cxp (syn_cima (syn_ccnv (syn_c2nd)) (syn_csn (syn_c1c))) (syn_cvv)))
      (syn_wbr (.cv n) (syn_c2nd) (syn_c1c)) p0013 p0018
  have p0020 := @g_n_1cex
  have p0021 := @g_op1st2nd (.cv b) (syn_c1c) (.cv n) p0014 p0020
  have p0022 :=
    @g_n_3bitri
      (.classMem (syn_cop (.cv n) (.cv b)) (syn_cin (syn_c1st)
          (syn_cxp (syn_cima (syn_ccnv (syn_c2nd)) (syn_csn (syn_c1c))) (syn_cvv))))
      (syn_wa (.classMem (syn_cop (.cv n) (.cv b)) (syn_c1st))
        (.classMem (syn_cop (.cv n) (.cv b))
          (syn_cxp (syn_cima (syn_ccnv (syn_c2nd)) (syn_csn (syn_c1c))) (syn_cvv))))
      (syn_wa (syn_wbr (.cv n) (syn_c1st) (.cv b)) (syn_wbr (.cv n) (syn_c2nd) (syn_c1c)))
      (.classEq (.cv n) (syn_cop (.cv b) (syn_c1c))) p0011 p0019 p0021
  have p0023 := (Nominal.biimpRefl (syn_wbr (.cv n) (syn_caddcfn) (.cv a)))
  have p0024 :=
    @g_bicomi (syn_wbr (.cv n) (syn_caddcfn) (.cv a))
      (.classMem (syn_cop (.cv n) (.cv a)) (syn_caddcfn)) p0023
  have p0025 :=
    @g_anbi12i
      (.classMem (syn_cop (.cv n) (.cv b)) (syn_cin (syn_c1st)
          (syn_cxp (syn_cima (syn_ccnv (syn_c2nd)) (syn_csn (syn_c1c))) (syn_cvv))))
      (.classEq (.cv n) (syn_cop (.cv b) (syn_c1c)))
      (.classMem (syn_cop (.cv n) (.cv a)) (syn_caddcfn))
      (syn_wbr (.cv n) (syn_caddcfn) (.cv a)) p0022 p0024
  have p0026 :=
    @g_bitri
      (.classMem (syn_cop (.cv n) (syn_cop (.cv b) (.cv a))) (syn_ctxp (syn_cin (syn_c1st)
            (syn_cxp (syn_cima (syn_ccnv (syn_c2nd)) (syn_csn (syn_c1c))) (syn_cvv)))
          (syn_caddcfn)))
      (syn_wa (.classMem (syn_cop (.cv n) (.cv b)) (syn_cin (syn_c1st)
            (syn_cxp (syn_cima (syn_ccnv (syn_c2nd)) (syn_csn (syn_c1c))) (syn_cvv))))
        (.classMem (syn_cop (.cv n) (.cv a)) (syn_caddcfn)))
      (syn_wa (.classEq (.cv n) (syn_cop (.cv b) (syn_c1c)))
        (syn_wbr (.cv n) (syn_caddcfn) (.cv a)))
      p0010 p0025
  have p0027 :=
    @g_exbii
      (.classMem (syn_cop (.cv n) (syn_cop (.cv b) (.cv a))) (syn_ctxp (syn_cin (syn_c1st)
            (syn_cxp (syn_cima (syn_ccnv (syn_c2nd)) (syn_csn (syn_c1c))) (syn_cvv)))
          (syn_caddcfn)))
      (syn_wa (.classEq (.cv n) (syn_cop (.cv b) (syn_c1c)))
        (syn_wbr (.cv n) (syn_caddcfn) (.cv a)))
      n p0026
  have p0028 :=
    @g_bitri
      (.classMem (syn_cop (.cv b) (.cv a)) (syn_crn (syn_ctxp (syn_cin (syn_c1st)
              (syn_cxp (syn_cima (syn_ccnv (syn_c2nd)) (syn_csn (syn_c1c))) (syn_cvv)))
            (syn_caddcfn))))
      (syn_wex n (.classMem (syn_cop (.cv n) (syn_cop (.cv b) (.cv a))) (syn_ctxp
            (syn_cin (syn_c1st)
              (syn_cxp (syn_cima (syn_ccnv (syn_c2nd)) (syn_csn (syn_c1c))) (syn_cvv)))
            (syn_caddcfn))))
      (syn_wex n (syn_wa (.classEq (.cv n) (syn_cop (.cv b) (syn_c1c)))
          (syn_wbr (.cv n) (syn_caddcfn) (.cv a))))
      p0009 p0027
  have p0030 := @g_opex (.cv b) (syn_c1c) p0014 p0020
  have p0031 := @g_breq1 (.cv n) (syn_cop (.cv b) (syn_c1c)) (.cv a) (syn_caddcfn)
  have p0032 :=
    @g_ceqsexv (syn_wbr (.cv n) (syn_caddcfn) (.cv a))
      (syn_wbr (syn_cop (.cv b) (syn_c1c)) (syn_caddcfn) (.cv a)) n
      (syn_cop (.cv b) (syn_c1c)) dv_cache_0008 dv_cache_0009 p0030 p0031
  have p0034 := @g_braddcfn (.cv b) (syn_c1c) (.cv a) p0014 p0020
  have p0035 := @g_eqcom (syn_cplc (.cv b) (syn_c1c)) (.cv a)
  have p0036 :=
    @g_bitri (syn_wbr (syn_cop (.cv b) (syn_c1c)) (syn_caddcfn) (.cv a))
      (.classEq (syn_cplc (.cv b) (syn_c1c)) (.cv a))
      (.classEq (.cv a) (syn_cplc (.cv b) (syn_c1c))) p0034 p0035
  have p0037 :=
    @g_n_3bitri
      (.classMem (syn_cop (.cv b) (.cv a)) (syn_crn (syn_ctxp (syn_cin (syn_c1st)
              (syn_cxp (syn_cima (syn_ccnv (syn_c2nd)) (syn_csn (syn_c1c))) (syn_cvv)))
            (syn_caddcfn))))
      (syn_wex n (syn_wa (.classEq (.cv n) (syn_cop (.cv b) (syn_c1c)))
          (syn_wbr (.cv n) (syn_caddcfn) (.cv a))))
      (syn_wbr (syn_cop (.cv b) (syn_c1c)) (syn_caddcfn) (.cv a))
      (.classEq (.cv a) (syn_cplc (.cv b) (syn_c1c))) p0028 p0032 p0036
  have p0038 :=
    @g_anbi12i
      (.classMem (syn_cop (.cv b) (.cv n)) (syn_ccnv (syn_crn (syn_cin (syn_cins3 (syn_ccnv
                  (syn_cima (syn_ctxp (syn_crn
                        (syn_ctxp (syn_ccnv (syn_c1st)) (syn_cin (syn_c1st) (syn_c2nd))))
                      (syn_c2nd)) (syn_caddcfn)))) (syn_cima
                (syn_ctxp (syn_ccom (syn_c1st) (syn_c1st))
                  (syn_ctxp (syn_ccom (syn_c2nd) (syn_c1st)) (syn_c2nd))) (syn_caddcfn))))))
      (.classEq (.cv b) (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n)))
      (.classMem (syn_cop (.cv b) (.cv a)) (syn_crn (syn_ctxp (syn_cin (syn_c1st)
              (syn_cxp (syn_cima (syn_ccnv (syn_c2nd)) (syn_csn (syn_c1c))) (syn_cvv)))
            (syn_caddcfn))))
      (.classEq (.cv a) (syn_cplc (.cv b) (syn_c1c))) p0008 p0037
  have p0039 :=
    @g_bitri
      (.classMem (syn_cop (.cv b) (syn_cop (.cv n) (.cv a))) (syn_ctxp (syn_ccnv (syn_crn
              (syn_cin (syn_cins3 (syn_ccnv (syn_cima (syn_ctxp (syn_crn
                          (syn_ctxp (syn_ccnv (syn_c1st)) (syn_cin (syn_c1st) (syn_c2nd))))
                        (syn_c2nd)) (syn_caddcfn)))) (syn_cima
                  (syn_ctxp (syn_ccom (syn_c1st) (syn_c1st))
                    (syn_ctxp (syn_ccom (syn_c2nd) (syn_c1st)) (syn_c2nd))) (syn_caddcfn)))))
          (syn_crn (syn_ctxp (syn_cin (syn_c1st)
                (syn_cxp (syn_cima (syn_ccnv (syn_c2nd)) (syn_csn (syn_c1c))) (syn_cvv)))
              (syn_caddcfn)))))
      (syn_wa (.classMem (syn_cop (.cv b) (.cv n)) (syn_ccnv (syn_crn (syn_cin (syn_cins3
                  (syn_ccnv (syn_cima (syn_ctxp (syn_crn (syn_ctxp (syn_ccnv (syn_c1st))
                            (syn_cin (syn_c1st) (syn_c2nd)))) (syn_c2nd)) (syn_caddcfn))))
                (syn_cima (syn_ctxp (syn_ccom (syn_c1st) (syn_c1st))
                    (syn_ctxp (syn_ccom (syn_c2nd) (syn_c1st)) (syn_c2nd))) (syn_caddcfn))))))
        (.classMem (syn_cop (.cv b) (.cv a)) (syn_crn (syn_ctxp (syn_cin (syn_c1st)
                (syn_cxp (syn_cima (syn_ccnv (syn_c2nd)) (syn_csn (syn_c1c))) (syn_cvv)))
              (syn_caddcfn)))))
      (syn_wa (.classEq (.cv b) (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n)))
        (.classEq (.cv a) (syn_cplc (.cv b) (syn_c1c))))
      p0005 p0038
  have p0040 :=
    @g_exbii
      (.classMem (syn_cop (.cv b) (syn_cop (.cv n) (.cv a))) (syn_ctxp (syn_ccnv (syn_crn
              (syn_cin (syn_cins3 (syn_ccnv (syn_cima (syn_ctxp (syn_crn
                          (syn_ctxp (syn_ccnv (syn_c1st)) (syn_cin (syn_c1st) (syn_c2nd))))
                        (syn_c2nd)) (syn_caddcfn)))) (syn_cima
                  (syn_ctxp (syn_ccom (syn_c1st) (syn_c1st))
                    (syn_ctxp (syn_ccom (syn_c2nd) (syn_c1st)) (syn_c2nd))) (syn_caddcfn)))))
          (syn_crn (syn_ctxp (syn_cin (syn_c1st)
                (syn_cxp (syn_cima (syn_ccnv (syn_c2nd)) (syn_csn (syn_c1c))) (syn_cvv)))
              (syn_caddcfn)))))
      (syn_wa (.classEq (.cv b) (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n)))
        (.classEq (.cv a) (syn_cplc (.cv b) (syn_c1c))))
      b p0039
  have p0041 := @g_vex n
  have p0042 := @g_addcex (.cv n) (.cv n) p0041 p0041
  have p0043 := @g_addcex (syn_cplc (.cv n) (.cv n)) (.cv n) p0042 p0041
  have p0044 := @g_addceq1 (.cv b) (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n)) (syn_c1c)
  have p0045 :=
    @g_eqeq2d (.classEq (.cv b) (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n)))
      (syn_cplc (.cv b) (syn_c1c))
      (syn_cplc (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n)) (syn_c1c)) (.cv a) p0044
  have p0046 :=
    @g_ceqsexv (.classEq (.cv a) (syn_cplc (.cv b) (syn_c1c)))
      (.classEq (.cv a) (syn_cplc (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n)) (syn_c1c)))
      b (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n)) dv_cache_0010 dv_cache_0011 p0043
      p0045
  have p0047 :=
    @g_n_3bitri
      (.classMem (syn_cop (.cv n) (.cv a)) (syn_crn (syn_ctxp (syn_ccnv (syn_crn (syn_cin
                  (syn_cins3 (syn_ccnv (syn_cima (syn_ctxp (syn_crn
                            (syn_ctxp (syn_ccnv (syn_c1st)) (syn_cin (syn_c1st) (syn_c2nd))))
                          (syn_c2nd)) (syn_caddcfn)))) (syn_cima
                    (syn_ctxp (syn_ccom (syn_c1st) (syn_c1st))
                      (syn_ctxp (syn_ccom (syn_c2nd) (syn_c1st)) (syn_c2nd))) (syn_caddcfn)))))
            (syn_crn (syn_ctxp (syn_cin (syn_c1st)
                  (syn_cxp (syn_cima (syn_ccnv (syn_c2nd)) (syn_csn (syn_c1c))) (syn_cvv)))
                (syn_caddcfn))))))
      (syn_wex b (.classMem (syn_cop (.cv b) (syn_cop (.cv n) (.cv a))) (syn_ctxp (syn_ccnv
              (syn_crn (syn_cin (syn_cins3 (syn_ccnv (syn_cima (syn_ctxp (syn_crn
                            (syn_ctxp (syn_ccnv (syn_c1st)) (syn_cin (syn_c1st) (syn_c2nd))))
                          (syn_c2nd)) (syn_caddcfn)))) (syn_cima
                    (syn_ctxp (syn_ccom (syn_c1st) (syn_c1st))
                      (syn_ctxp (syn_ccom (syn_c2nd) (syn_c1st)) (syn_c2nd))) (syn_caddcfn)))))
            (syn_crn (syn_ctxp (syn_cin (syn_c1st)
                  (syn_cxp (syn_cima (syn_ccnv (syn_c2nd)) (syn_csn (syn_c1c))) (syn_cvv)))
                (syn_caddcfn))))))
      (syn_wex b (syn_wa (.classEq (.cv b) (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n)))
          (.classEq (.cv a) (syn_cplc (.cv b) (syn_c1c)))))
      (.classEq (.cv a) (syn_cplc (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n)) (syn_c1c)))
      p0004 p0040 p0046
  have p0048 :=
    @g_orbi12i
      (.classMem (syn_cop (.cv n) (.cv a)) (syn_crn (syn_cin (syn_cins3 (syn_ccnv (syn_cima
                  (syn_ctxp (syn_crn
                      (syn_ctxp (syn_ccnv (syn_c1st)) (syn_cin (syn_c1st) (syn_c2nd))))
                    (syn_c2nd)) (syn_caddcfn)))) (syn_cima
              (syn_ctxp (syn_ccom (syn_c1st) (syn_c1st))
                (syn_ctxp (syn_ccom (syn_c2nd) (syn_c1st)) (syn_c2nd))) (syn_caddcfn)))))
      (.classEq (.cv a) (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n)))
      (.classMem (syn_cop (.cv n) (.cv a)) (syn_crn (syn_ctxp (syn_ccnv (syn_crn (syn_cin
                  (syn_cins3 (syn_ccnv (syn_cima (syn_ctxp (syn_crn
                            (syn_ctxp (syn_ccnv (syn_c1st)) (syn_cin (syn_c1st) (syn_c2nd))))
                          (syn_c2nd)) (syn_caddcfn)))) (syn_cima
                    (syn_ctxp (syn_ccom (syn_c1st) (syn_c1st))
                      (syn_ctxp (syn_ccom (syn_c2nd) (syn_c1st)) (syn_c2nd))) (syn_caddcfn)))))
            (syn_crn (syn_ctxp (syn_cin (syn_c1st)
                  (syn_cxp (syn_cima (syn_ccnv (syn_c2nd)) (syn_csn (syn_c1c))) (syn_cvv)))
                (syn_caddcfn))))))
      (.classEq (.cv a) (syn_cplc (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n)) (syn_c1c)))
      p0003 p0047
  have p0049 :=
    @g_bitri
      (.classMem (syn_cop (.cv n) (.cv a)) (syn_cun (syn_crn (syn_cin (syn_cins3 (syn_ccnv
                  (syn_cima (syn_ctxp (syn_crn
                        (syn_ctxp (syn_ccnv (syn_c1st)) (syn_cin (syn_c1st) (syn_c2nd))))
                      (syn_c2nd)) (syn_caddcfn)))) (syn_cima
                (syn_ctxp (syn_ccom (syn_c1st) (syn_c1st))
                  (syn_ctxp (syn_ccom (syn_c2nd) (syn_c1st)) (syn_c2nd))) (syn_caddcfn))))
          (syn_crn (syn_ctxp (syn_ccnv (syn_crn (syn_cin (syn_cins3 (syn_ccnv (syn_cima
                          (syn_ctxp (syn_crn (syn_ctxp (syn_ccnv (syn_c1st))
                                (syn_cin (syn_c1st) (syn_c2nd)))) (syn_c2nd)) (syn_caddcfn))))
                    (syn_cima (syn_ctxp (syn_ccom (syn_c1st) (syn_c1st))
                        (syn_ctxp (syn_ccom (syn_c2nd) (syn_c1st)) (syn_c2nd)))
                      (syn_caddcfn))))) (syn_crn (syn_ctxp (syn_cin (syn_c1st)
                    (syn_cxp (syn_cima (syn_ccnv (syn_c2nd)) (syn_csn (syn_c1c))) (syn_cvv)))
                  (syn_caddcfn)))))))
      (syn_wo (.classMem (syn_cop (.cv n) (.cv a)) (syn_crn (syn_cin (syn_cins3 (syn_ccnv
                  (syn_cima (syn_ctxp (syn_crn
                        (syn_ctxp (syn_ccnv (syn_c1st)) (syn_cin (syn_c1st) (syn_c2nd))))
                      (syn_c2nd)) (syn_caddcfn)))) (syn_cima
                (syn_ctxp (syn_ccom (syn_c1st) (syn_c1st))
                  (syn_ctxp (syn_ccom (syn_c2nd) (syn_c1st)) (syn_c2nd))) (syn_caddcfn)))))
        (.classMem (syn_cop (.cv n) (.cv a)) (syn_crn (syn_ctxp (syn_ccnv (syn_crn (syn_cin
                    (syn_cins3 (syn_ccnv (syn_cima (syn_ctxp (syn_crn
                              (syn_ctxp (syn_ccnv (syn_c1st)) (syn_cin (syn_c1st) (syn_c2nd))))
                            (syn_c2nd)) (syn_caddcfn)))) (syn_cima
                      (syn_ctxp (syn_ccom (syn_c1st) (syn_c1st))
                        (syn_ctxp (syn_ccom (syn_c2nd) (syn_c1st)) (syn_c2nd)))
                      (syn_caddcfn))))) (syn_crn (syn_ctxp (syn_cin (syn_c1st)
                    (syn_cxp (syn_cima (syn_ccnv (syn_c2nd)) (syn_csn (syn_c1c))) (syn_cvv)))
                  (syn_caddcfn)))))))
      (syn_wo (.classEq (.cv a) (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n))) (.classEq (.cv a)
          (syn_cplc (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n)) (syn_c1c))))
      p0002 p0048
  have p0050 :=
    @g_elrn2 b (syn_cop (.cv n) (.cv a))
      (syn_ctxp (syn_ccnv (syn_crn (syn_cin (syn_cins3 (syn_ccnv (syn_cima (syn_ctxp (syn_crn
                        (syn_ctxp (syn_ccnv (syn_c1st)) (syn_cin (syn_c1st) (syn_c2nd))))
                      (syn_c2nd)) (syn_caddcfn)))) (syn_cima
                (syn_ctxp (syn_ccom (syn_c1st) (syn_c1st))
                  (syn_ctxp (syn_ccom (syn_c2nd) (syn_c1st)) (syn_c2nd))) (syn_caddcfn)))))
        (syn_crn (syn_ctxp (syn_cin (syn_c1st)
              (syn_cxp (syn_cima (syn_ccnv (syn_c2nd)) (syn_csn (syn_c2c))) (syn_cvv)))
            (syn_caddcfn))))
      dv_cache_0004 dv_cache_0012
  have p0051 :=
    @g_oteltxp (.cv b) (.cv n) (.cv a)
      (syn_ccnv (syn_crn (syn_cin (syn_cins3 (syn_ccnv (syn_cima (syn_ctxp (syn_crn
                      (syn_ctxp (syn_ccnv (syn_c1st)) (syn_cin (syn_c1st) (syn_c2nd))))
                    (syn_c2nd)) (syn_caddcfn)))) (syn_cima
              (syn_ctxp (syn_ccom (syn_c1st) (syn_c1st))
                (syn_ctxp (syn_ccom (syn_c2nd) (syn_c1st)) (syn_c2nd))) (syn_caddcfn)))))
      (syn_crn (syn_ctxp (syn_cin (syn_c1st)
            (syn_cxp (syn_cima (syn_ccnv (syn_c2nd)) (syn_csn (syn_c2c))) (syn_cvv)))
          (syn_caddcfn)))
  have p0052 :=
    @g_elrn2 n (syn_cop (.cv b) (.cv a))
      (syn_ctxp (syn_cin (syn_c1st)
          (syn_cxp (syn_cima (syn_ccnv (syn_c2nd)) (syn_csn (syn_c2c))) (syn_cvv)))
        (syn_caddcfn))
      dv_cache_0006 dv_cache_0013
  have p0053 :=
    @g_oteltxp (.cv n) (.cv b) (.cv a)
      (syn_cin (syn_c1st)
        (syn_cxp (syn_cima (syn_ccnv (syn_c2nd)) (syn_csn (syn_c2c))) (syn_cvv)))
      (syn_caddcfn)
  have p0054 :=
    @g_elin (syn_cop (.cv n) (.cv b)) (syn_c1st)
      (syn_cxp (syn_cima (syn_ccnv (syn_c2nd)) (syn_csn (syn_c2c))) (syn_cvv))
  have p0055 :=
    @g_opelxp (.cv n) (.cv b) (syn_cima (syn_ccnv (syn_c2nd)) (syn_csn (syn_c2c)))
      (syn_cvv)
  have p0056 :=
    @g_mpbiran2
      (.classMem (syn_cop (.cv n) (.cv b))
        (syn_cxp (syn_cima (syn_ccnv (syn_c2nd)) (syn_csn (syn_c2c))) (syn_cvv)))
      (.classMem (.cv n) (syn_cima (syn_ccnv (syn_c2nd)) (syn_csn (syn_c2c))))
      (.classMem (.cv b) (syn_cvv)) p0014 p0055
  have p0057 := @g_eliniseg (syn_c2nd) (syn_c2c) (.cv n)
  have p0058 :=
    @g_bitri
      (.classMem (syn_cop (.cv n) (.cv b))
        (syn_cxp (syn_cima (syn_ccnv (syn_c2nd)) (syn_csn (syn_c2c))) (syn_cvv)))
      (.classMem (.cv n) (syn_cima (syn_ccnv (syn_c2nd)) (syn_csn (syn_c2c))))
      (syn_wbr (.cv n) (syn_c2nd) (syn_c2c)) p0056 p0057
  have p0059 :=
    @g_anbi12i (.classMem (syn_cop (.cv n) (.cv b)) (syn_c1st))
      (syn_wbr (.cv n) (syn_c1st) (.cv b))
      (.classMem (syn_cop (.cv n) (.cv b))
        (syn_cxp (syn_cima (syn_ccnv (syn_c2nd)) (syn_csn (syn_c2c))) (syn_cvv)))
      (syn_wbr (.cv n) (syn_c2nd) (syn_c2c)) p0013 p0058
  have p0060 := (Nominal.classEqRefl (syn_c2c))
  have p0061 := @g_ncex (syn_cpr (syn_c0) (syn_cvv))
  have p0062 :=
    @g_eqeltri (syn_c2c) (syn_cnc (syn_cpr (syn_c0) (syn_cvv))) (syn_cvv) p0060 p0061
  have p0063 := @g_op1st2nd (.cv b) (syn_c2c) (.cv n) p0014 p0062
  have p0064 :=
    @g_n_3bitri
      (.classMem (syn_cop (.cv n) (.cv b)) (syn_cin (syn_c1st)
          (syn_cxp (syn_cima (syn_ccnv (syn_c2nd)) (syn_csn (syn_c2c))) (syn_cvv))))
      (syn_wa (.classMem (syn_cop (.cv n) (.cv b)) (syn_c1st))
        (.classMem (syn_cop (.cv n) (.cv b))
          (syn_cxp (syn_cima (syn_ccnv (syn_c2nd)) (syn_csn (syn_c2c))) (syn_cvv))))
      (syn_wa (syn_wbr (.cv n) (syn_c1st) (.cv b)) (syn_wbr (.cv n) (syn_c2nd) (syn_c2c)))
      (.classEq (.cv n) (syn_cop (.cv b) (syn_c2c))) p0054 p0059 p0063
  have p0065 :=
    @g_anbi12i
      (.classMem (syn_cop (.cv n) (.cv b)) (syn_cin (syn_c1st)
          (syn_cxp (syn_cima (syn_ccnv (syn_c2nd)) (syn_csn (syn_c2c))) (syn_cvv))))
      (.classEq (.cv n) (syn_cop (.cv b) (syn_c2c)))
      (.classMem (syn_cop (.cv n) (.cv a)) (syn_caddcfn))
      (syn_wbr (.cv n) (syn_caddcfn) (.cv a)) p0064 p0024
  have p0066 :=
    @g_bitri
      (.classMem (syn_cop (.cv n) (syn_cop (.cv b) (.cv a))) (syn_ctxp (syn_cin (syn_c1st)
            (syn_cxp (syn_cima (syn_ccnv (syn_c2nd)) (syn_csn (syn_c2c))) (syn_cvv)))
          (syn_caddcfn)))
      (syn_wa (.classMem (syn_cop (.cv n) (.cv b)) (syn_cin (syn_c1st)
            (syn_cxp (syn_cima (syn_ccnv (syn_c2nd)) (syn_csn (syn_c2c))) (syn_cvv))))
        (.classMem (syn_cop (.cv n) (.cv a)) (syn_caddcfn)))
      (syn_wa (.classEq (.cv n) (syn_cop (.cv b) (syn_c2c)))
        (syn_wbr (.cv n) (syn_caddcfn) (.cv a)))
      p0053 p0065
  have p0067 :=
    @g_exbii
      (.classMem (syn_cop (.cv n) (syn_cop (.cv b) (.cv a))) (syn_ctxp (syn_cin (syn_c1st)
            (syn_cxp (syn_cima (syn_ccnv (syn_c2nd)) (syn_csn (syn_c2c))) (syn_cvv)))
          (syn_caddcfn)))
      (syn_wa (.classEq (.cv n) (syn_cop (.cv b) (syn_c2c)))
        (syn_wbr (.cv n) (syn_caddcfn) (.cv a)))
      n p0066
  have p0068 := @g_opex (.cv b) (syn_c2c) p0014 p0062
  have p0069 := @g_breq1 (.cv n) (syn_cop (.cv b) (syn_c2c)) (.cv a) (syn_caddcfn)
  have p0070 :=
    @g_ceqsexv (syn_wbr (.cv n) (syn_caddcfn) (.cv a))
      (syn_wbr (syn_cop (.cv b) (syn_c2c)) (syn_caddcfn) (.cv a)) n
      (syn_cop (.cv b) (syn_c2c)) dv_cache_0014 dv_cache_0015 p0068 p0069
  have p0071 :=
    @g_n_3bitri
      (.classMem (syn_cop (.cv b) (.cv a)) (syn_crn (syn_ctxp (syn_cin (syn_c1st)
              (syn_cxp (syn_cima (syn_ccnv (syn_c2nd)) (syn_csn (syn_c2c))) (syn_cvv)))
            (syn_caddcfn))))
      (syn_wex n (.classMem (syn_cop (.cv n) (syn_cop (.cv b) (.cv a))) (syn_ctxp
            (syn_cin (syn_c1st)
              (syn_cxp (syn_cima (syn_ccnv (syn_c2nd)) (syn_csn (syn_c2c))) (syn_cvv)))
            (syn_caddcfn))))
      (syn_wex n (syn_wa (.classEq (.cv n) (syn_cop (.cv b) (syn_c2c)))
          (syn_wbr (.cv n) (syn_caddcfn) (.cv a))))
      (syn_wbr (syn_cop (.cv b) (syn_c2c)) (syn_caddcfn) (.cv a)) p0052 p0067 p0070
  have p0072 := @g_braddcfn (.cv b) (syn_c2c) (.cv a) p0014 p0062
  have p0073 := @g_eqcom (syn_cplc (.cv b) (syn_c2c)) (.cv a)
  have p0074 :=
    @g_n_3bitri
      (.classMem (syn_cop (.cv b) (.cv a)) (syn_crn (syn_ctxp (syn_cin (syn_c1st)
              (syn_cxp (syn_cima (syn_ccnv (syn_c2nd)) (syn_csn (syn_c2c))) (syn_cvv)))
            (syn_caddcfn))))
      (syn_wbr (syn_cop (.cv b) (syn_c2c)) (syn_caddcfn) (.cv a))
      (.classEq (syn_cplc (.cv b) (syn_c2c)) (.cv a))
      (.classEq (.cv a) (syn_cplc (.cv b) (syn_c2c))) p0071 p0072 p0073
  have p0075 :=
    @g_anbi12i
      (.classMem (syn_cop (.cv b) (.cv n)) (syn_ccnv (syn_crn (syn_cin (syn_cins3 (syn_ccnv
                  (syn_cima (syn_ctxp (syn_crn
                        (syn_ctxp (syn_ccnv (syn_c1st)) (syn_cin (syn_c1st) (syn_c2nd))))
                      (syn_c2nd)) (syn_caddcfn)))) (syn_cima
                (syn_ctxp (syn_ccom (syn_c1st) (syn_c1st))
                  (syn_ctxp (syn_ccom (syn_c2nd) (syn_c1st)) (syn_c2nd))) (syn_caddcfn))))))
      (.classEq (.cv b) (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n)))
      (.classMem (syn_cop (.cv b) (.cv a)) (syn_crn (syn_ctxp (syn_cin (syn_c1st)
              (syn_cxp (syn_cima (syn_ccnv (syn_c2nd)) (syn_csn (syn_c2c))) (syn_cvv)))
            (syn_caddcfn))))
      (.classEq (.cv a) (syn_cplc (.cv b) (syn_c2c))) p0008 p0074
  have p0076 :=
    @g_bitri
      (.classMem (syn_cop (.cv b) (syn_cop (.cv n) (.cv a))) (syn_ctxp (syn_ccnv (syn_crn
              (syn_cin (syn_cins3 (syn_ccnv (syn_cima (syn_ctxp (syn_crn
                          (syn_ctxp (syn_ccnv (syn_c1st)) (syn_cin (syn_c1st) (syn_c2nd))))
                        (syn_c2nd)) (syn_caddcfn)))) (syn_cima
                  (syn_ctxp (syn_ccom (syn_c1st) (syn_c1st))
                    (syn_ctxp (syn_ccom (syn_c2nd) (syn_c1st)) (syn_c2nd))) (syn_caddcfn)))))
          (syn_crn (syn_ctxp (syn_cin (syn_c1st)
                (syn_cxp (syn_cima (syn_ccnv (syn_c2nd)) (syn_csn (syn_c2c))) (syn_cvv)))
              (syn_caddcfn)))))
      (syn_wa (.classMem (syn_cop (.cv b) (.cv n)) (syn_ccnv (syn_crn (syn_cin (syn_cins3
                  (syn_ccnv (syn_cima (syn_ctxp (syn_crn (syn_ctxp (syn_ccnv (syn_c1st))
                            (syn_cin (syn_c1st) (syn_c2nd)))) (syn_c2nd)) (syn_caddcfn))))
                (syn_cima (syn_ctxp (syn_ccom (syn_c1st) (syn_c1st))
                    (syn_ctxp (syn_ccom (syn_c2nd) (syn_c1st)) (syn_c2nd))) (syn_caddcfn))))))
        (.classMem (syn_cop (.cv b) (.cv a)) (syn_crn (syn_ctxp (syn_cin (syn_c1st)
                (syn_cxp (syn_cima (syn_ccnv (syn_c2nd)) (syn_csn (syn_c2c))) (syn_cvv)))
              (syn_caddcfn)))))
      (syn_wa (.classEq (.cv b) (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n)))
        (.classEq (.cv a) (syn_cplc (.cv b) (syn_c2c))))
      p0051 p0075
  have p0077 :=
    @g_exbii
      (.classMem (syn_cop (.cv b) (syn_cop (.cv n) (.cv a))) (syn_ctxp (syn_ccnv (syn_crn
              (syn_cin (syn_cins3 (syn_ccnv (syn_cima (syn_ctxp (syn_crn
                          (syn_ctxp (syn_ccnv (syn_c1st)) (syn_cin (syn_c1st) (syn_c2nd))))
                        (syn_c2nd)) (syn_caddcfn)))) (syn_cima
                  (syn_ctxp (syn_ccom (syn_c1st) (syn_c1st))
                    (syn_ctxp (syn_ccom (syn_c2nd) (syn_c1st)) (syn_c2nd))) (syn_caddcfn)))))
          (syn_crn (syn_ctxp (syn_cin (syn_c1st)
                (syn_cxp (syn_cima (syn_ccnv (syn_c2nd)) (syn_csn (syn_c2c))) (syn_cvv)))
              (syn_caddcfn)))))
      (syn_wa (.classEq (.cv b) (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n)))
        (.classEq (.cv a) (syn_cplc (.cv b) (syn_c2c))))
      b p0076
  have p0078 := @g_addceq1 (.cv b) (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n)) (syn_c2c)
  have p0079 :=
    @g_eqeq2d (.classEq (.cv b) (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n)))
      (syn_cplc (.cv b) (syn_c2c))
      (syn_cplc (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n)) (syn_c2c)) (.cv a) p0078
  have p0080 :=
    @g_ceqsexv (.classEq (.cv a) (syn_cplc (.cv b) (syn_c2c)))
      (.classEq (.cv a) (syn_cplc (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n)) (syn_c2c)))
      b (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n)) dv_cache_0010 dv_cache_0016 p0043
      p0079
  have p0081 :=
    @g_n_3bitri
      (.classMem (syn_cop (.cv n) (.cv a)) (syn_crn (syn_ctxp (syn_ccnv (syn_crn (syn_cin
                  (syn_cins3 (syn_ccnv (syn_cima (syn_ctxp (syn_crn
                            (syn_ctxp (syn_ccnv (syn_c1st)) (syn_cin (syn_c1st) (syn_c2nd))))
                          (syn_c2nd)) (syn_caddcfn)))) (syn_cima
                    (syn_ctxp (syn_ccom (syn_c1st) (syn_c1st))
                      (syn_ctxp (syn_ccom (syn_c2nd) (syn_c1st)) (syn_c2nd))) (syn_caddcfn)))))
            (syn_crn (syn_ctxp (syn_cin (syn_c1st)
                  (syn_cxp (syn_cima (syn_ccnv (syn_c2nd)) (syn_csn (syn_c2c))) (syn_cvv)))
                (syn_caddcfn))))))
      (syn_wex b (.classMem (syn_cop (.cv b) (syn_cop (.cv n) (.cv a))) (syn_ctxp (syn_ccnv
              (syn_crn (syn_cin (syn_cins3 (syn_ccnv (syn_cima (syn_ctxp (syn_crn
                            (syn_ctxp (syn_ccnv (syn_c1st)) (syn_cin (syn_c1st) (syn_c2nd))))
                          (syn_c2nd)) (syn_caddcfn)))) (syn_cima
                    (syn_ctxp (syn_ccom (syn_c1st) (syn_c1st))
                      (syn_ctxp (syn_ccom (syn_c2nd) (syn_c1st)) (syn_c2nd))) (syn_caddcfn)))))
            (syn_crn (syn_ctxp (syn_cin (syn_c1st)
                  (syn_cxp (syn_cima (syn_ccnv (syn_c2nd)) (syn_csn (syn_c2c))) (syn_cvv)))
                (syn_caddcfn))))))
      (syn_wex b (syn_wa (.classEq (.cv b) (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n)))
          (.classEq (.cv a) (syn_cplc (.cv b) (syn_c2c)))))
      (.classEq (.cv a) (syn_cplc (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n)) (syn_c2c)))
      p0050 p0077 p0080
  have p0082 :=
    @g_orbi12i
      (.classMem (syn_cop (.cv n) (.cv a)) (syn_cun (syn_crn (syn_cin (syn_cins3 (syn_ccnv
                  (syn_cima (syn_ctxp (syn_crn
                        (syn_ctxp (syn_ccnv (syn_c1st)) (syn_cin (syn_c1st) (syn_c2nd))))
                      (syn_c2nd)) (syn_caddcfn)))) (syn_cima
                (syn_ctxp (syn_ccom (syn_c1st) (syn_c1st))
                  (syn_ctxp (syn_ccom (syn_c2nd) (syn_c1st)) (syn_c2nd))) (syn_caddcfn))))
          (syn_crn (syn_ctxp (syn_ccnv (syn_crn (syn_cin (syn_cins3 (syn_ccnv (syn_cima
                          (syn_ctxp (syn_crn (syn_ctxp (syn_ccnv (syn_c1st))
                                (syn_cin (syn_c1st) (syn_c2nd)))) (syn_c2nd)) (syn_caddcfn))))
                    (syn_cima (syn_ctxp (syn_ccom (syn_c1st) (syn_c1st))
                        (syn_ctxp (syn_ccom (syn_c2nd) (syn_c1st)) (syn_c2nd)))
                      (syn_caddcfn))))) (syn_crn (syn_ctxp (syn_cin (syn_c1st)
                    (syn_cxp (syn_cima (syn_ccnv (syn_c2nd)) (syn_csn (syn_c1c))) (syn_cvv)))
                  (syn_caddcfn)))))))
      (syn_wo (.classEq (.cv a) (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n))) (.classEq (.cv a)
          (syn_cplc (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n)) (syn_c1c))))
      (.classMem (syn_cop (.cv n) (.cv a)) (syn_crn (syn_ctxp (syn_ccnv (syn_crn (syn_cin
                  (syn_cins3 (syn_ccnv (syn_cima (syn_ctxp (syn_crn
                            (syn_ctxp (syn_ccnv (syn_c1st)) (syn_cin (syn_c1st) (syn_c2nd))))
                          (syn_c2nd)) (syn_caddcfn)))) (syn_cima
                    (syn_ctxp (syn_ccom (syn_c1st) (syn_c1st))
                      (syn_ctxp (syn_ccom (syn_c2nd) (syn_c1st)) (syn_c2nd))) (syn_caddcfn)))))
            (syn_crn (syn_ctxp (syn_cin (syn_c1st)
                  (syn_cxp (syn_cima (syn_ccnv (syn_c2nd)) (syn_csn (syn_c2c))) (syn_cvv)))
                (syn_caddcfn))))))
      (.classEq (.cv a) (syn_cplc (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n)) (syn_c2c)))
      p0049 p0081
  have p0083 :=
    @g_elun (syn_cop (.cv n) (.cv a))
      (syn_cun (syn_crn (syn_cin (syn_cins3 (syn_ccnv (syn_cima (syn_ctxp (syn_crn
                      (syn_ctxp (syn_ccnv (syn_c1st)) (syn_cin (syn_c1st) (syn_c2nd))))
                    (syn_c2nd)) (syn_caddcfn)))) (syn_cima
              (syn_ctxp (syn_ccom (syn_c1st) (syn_c1st))
                (syn_ctxp (syn_ccom (syn_c2nd) (syn_c1st)) (syn_c2nd))) (syn_caddcfn))))
        (syn_crn (syn_ctxp (syn_ccnv (syn_crn (syn_cin (syn_cins3 (syn_ccnv (syn_cima (syn_ctxp
                          (syn_crn (syn_ctxp (syn_ccnv (syn_c1st))
                              (syn_cin (syn_c1st) (syn_c2nd)))) (syn_c2nd)) (syn_caddcfn))))
                  (syn_cima (syn_ctxp (syn_ccom (syn_c1st) (syn_c1st))
                      (syn_ctxp (syn_ccom (syn_c2nd) (syn_c1st)) (syn_c2nd))) (syn_caddcfn)))))
            (syn_crn (syn_ctxp (syn_cin (syn_c1st)
                  (syn_cxp (syn_cima (syn_ccnv (syn_c2nd)) (syn_csn (syn_c1c))) (syn_cvv)))
                (syn_caddcfn))))))
      (syn_crn (syn_ctxp (syn_ccnv (syn_crn (syn_cin (syn_cins3 (syn_ccnv (syn_cima (syn_ctxp
                        (syn_crn (syn_ctxp (syn_ccnv (syn_c1st))
                            (syn_cin (syn_c1st) (syn_c2nd)))) (syn_c2nd)) (syn_caddcfn))))
                (syn_cima (syn_ctxp (syn_ccom (syn_c1st) (syn_c1st))
                    (syn_ctxp (syn_ccom (syn_c2nd) (syn_c1st)) (syn_c2nd))) (syn_caddcfn)))))
          (syn_crn (syn_ctxp (syn_cin (syn_c1st)
                (syn_cxp (syn_cima (syn_ccnv (syn_c2nd)) (syn_csn (syn_c2c))) (syn_cvv)))
              (syn_caddcfn)))))
  have p0084 :=
    (Nominal.biimpRefl (syn_w3o (.classEq (.cv a) (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n)))
        (.classEq (.cv a) (syn_cplc (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n)) (syn_c1c)))
        (.classEq (.cv a) (syn_cplc (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n)) (syn_c2c)))))
  have p0085 :=
    @g_n_3bitr4i
      (syn_wo (.classMem (syn_cop (.cv n) (.cv a)) (syn_cun (syn_crn (syn_cin (syn_cins3
                  (syn_ccnv (syn_cima (syn_ctxp (syn_crn (syn_ctxp (syn_ccnv (syn_c1st))
                            (syn_cin (syn_c1st) (syn_c2nd)))) (syn_c2nd)) (syn_caddcfn))))
                (syn_cima (syn_ctxp (syn_ccom (syn_c1st) (syn_c1st))
                    (syn_ctxp (syn_ccom (syn_c2nd) (syn_c1st)) (syn_c2nd))) (syn_caddcfn))))
            (syn_crn (syn_ctxp (syn_ccnv (syn_crn (syn_cin (syn_cins3 (syn_ccnv (syn_cima
                            (syn_ctxp (syn_crn (syn_ctxp (syn_ccnv (syn_c1st))
                                  (syn_cin (syn_c1st) (syn_c2nd)))) (syn_c2nd)) (syn_caddcfn))))
                      (syn_cima (syn_ctxp (syn_ccom (syn_c1st) (syn_c1st))
                          (syn_ctxp (syn_ccom (syn_c2nd) (syn_c1st)) (syn_c2nd)))
                        (syn_caddcfn))))) (syn_crn (syn_ctxp (syn_cin (syn_c1st)
                      (syn_cxp (syn_cima (syn_ccnv (syn_c2nd)) (syn_csn (syn_c1c))) (syn_cvv)))
                    (syn_caddcfn))))))) (.classMem (syn_cop (.cv n) (.cv a)) (syn_crn (syn_ctxp
              (syn_ccnv (syn_crn (syn_cin (syn_cins3 (syn_ccnv (syn_cima (syn_ctxp (syn_crn
                              (syn_ctxp (syn_ccnv (syn_c1st)) (syn_cin (syn_c1st) (syn_c2nd))))
                            (syn_c2nd)) (syn_caddcfn)))) (syn_cima
                      (syn_ctxp (syn_ccom (syn_c1st) (syn_c1st))
                        (syn_ctxp (syn_ccom (syn_c2nd) (syn_c1st)) (syn_c2nd)))
                      (syn_caddcfn))))) (syn_crn (syn_ctxp (syn_cin (syn_c1st)
                    (syn_cxp (syn_cima (syn_ccnv (syn_c2nd)) (syn_csn (syn_c2c))) (syn_cvv)))
                  (syn_caddcfn)))))))
      (syn_wo (syn_wo (.classEq (.cv a) (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n)))
          (.classEq (.cv a) (syn_cplc (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n)) (syn_c1c))))
        (.classEq (.cv a) (syn_cplc (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n)) (syn_c2c))))
      (.classMem (syn_cop (.cv n) (.cv a)) (syn_cun (syn_cun (syn_crn (syn_cin (syn_cins3
                  (syn_ccnv (syn_cima (syn_ctxp (syn_crn (syn_ctxp (syn_ccnv (syn_c1st))
                            (syn_cin (syn_c1st) (syn_c2nd)))) (syn_c2nd)) (syn_caddcfn))))
                (syn_cima (syn_ctxp (syn_ccom (syn_c1st) (syn_c1st))
                    (syn_ctxp (syn_ccom (syn_c2nd) (syn_c1st)) (syn_c2nd))) (syn_caddcfn))))
            (syn_crn (syn_ctxp (syn_ccnv (syn_crn (syn_cin (syn_cins3 (syn_ccnv (syn_cima
                            (syn_ctxp (syn_crn (syn_ctxp (syn_ccnv (syn_c1st))
                                  (syn_cin (syn_c1st) (syn_c2nd)))) (syn_c2nd)) (syn_caddcfn))))
                      (syn_cima (syn_ctxp (syn_ccom (syn_c1st) (syn_c1st))
                          (syn_ctxp (syn_ccom (syn_c2nd) (syn_c1st)) (syn_c2nd)))
                        (syn_caddcfn))))) (syn_crn (syn_ctxp (syn_cin (syn_c1st)
                      (syn_cxp (syn_cima (syn_ccnv (syn_c2nd)) (syn_csn (syn_c1c))) (syn_cvv)))
                    (syn_caddcfn)))))) (syn_crn (syn_ctxp (syn_ccnv (syn_crn (syn_cin (syn_cins3
                      (syn_ccnv (syn_cima (syn_ctxp (syn_crn (syn_ctxp (syn_ccnv (syn_c1st))
                                (syn_cin (syn_c1st) (syn_c2nd)))) (syn_c2nd)) (syn_caddcfn))))
                    (syn_cima (syn_ctxp (syn_ccom (syn_c1st) (syn_c1st))
                        (syn_ctxp (syn_ccom (syn_c2nd) (syn_c1st)) (syn_c2nd)))
                      (syn_caddcfn))))) (syn_crn (syn_ctxp (syn_cin (syn_c1st)
                    (syn_cxp (syn_cima (syn_ccnv (syn_c2nd)) (syn_csn (syn_c2c))) (syn_cvv)))
                  (syn_caddcfn)))))))
      (syn_w3o (.classEq (.cv a) (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n)))
        (.classEq (.cv a) (syn_cplc (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n)) (syn_c1c)))
        (.classEq (.cv a) (syn_cplc (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n)) (syn_c2c))))
      p0082 p0083 p0084
  have p0086 :=
    @g_bitri
      (syn_wbr (.cv n) (syn_cun (syn_cun (syn_crn (syn_cin (syn_cins3 (syn_ccnv (syn_cima
                      (syn_ctxp (syn_crn (syn_ctxp (syn_ccnv (syn_c1st))
                            (syn_cin (syn_c1st) (syn_c2nd)))) (syn_c2nd)) (syn_caddcfn))))
                (syn_cima (syn_ctxp (syn_ccom (syn_c1st) (syn_c1st))
                    (syn_ctxp (syn_ccom (syn_c2nd) (syn_c1st)) (syn_c2nd))) (syn_caddcfn))))
            (syn_crn (syn_ctxp (syn_ccnv (syn_crn (syn_cin (syn_cins3 (syn_ccnv (syn_cima
                            (syn_ctxp (syn_crn (syn_ctxp (syn_ccnv (syn_c1st))
                                  (syn_cin (syn_c1st) (syn_c2nd)))) (syn_c2nd)) (syn_caddcfn))))
                      (syn_cima (syn_ctxp (syn_ccom (syn_c1st) (syn_c1st))
                          (syn_ctxp (syn_ccom (syn_c2nd) (syn_c1st)) (syn_c2nd)))
                        (syn_caddcfn))))) (syn_crn (syn_ctxp (syn_cin (syn_c1st)
                      (syn_cxp (syn_cima (syn_ccnv (syn_c2nd)) (syn_csn (syn_c1c))) (syn_cvv)))
                    (syn_caddcfn)))))) (syn_crn (syn_ctxp (syn_ccnv (syn_crn (syn_cin (syn_cins3
                      (syn_ccnv (syn_cima (syn_ctxp (syn_crn (syn_ctxp (syn_ccnv (syn_c1st))
                                (syn_cin (syn_c1st) (syn_c2nd)))) (syn_c2nd)) (syn_caddcfn))))
                    (syn_cima (syn_ctxp (syn_ccom (syn_c1st) (syn_c1st))
                        (syn_ctxp (syn_ccom (syn_c2nd) (syn_c1st)) (syn_c2nd)))
                      (syn_caddcfn))))) (syn_crn (syn_ctxp (syn_cin (syn_c1st)
                    (syn_cxp (syn_cima (syn_ccnv (syn_c2nd)) (syn_csn (syn_c2c))) (syn_cvv)))
                  (syn_caddcfn)))))) (.cv a))
      (.classMem (syn_cop (.cv n) (.cv a)) (syn_cun (syn_cun (syn_crn (syn_cin (syn_cins3
                  (syn_ccnv (syn_cima (syn_ctxp (syn_crn (syn_ctxp (syn_ccnv (syn_c1st))
                            (syn_cin (syn_c1st) (syn_c2nd)))) (syn_c2nd)) (syn_caddcfn))))
                (syn_cima (syn_ctxp (syn_ccom (syn_c1st) (syn_c1st))
                    (syn_ctxp (syn_ccom (syn_c2nd) (syn_c1st)) (syn_c2nd))) (syn_caddcfn))))
            (syn_crn (syn_ctxp (syn_ccnv (syn_crn (syn_cin (syn_cins3 (syn_ccnv (syn_cima
                            (syn_ctxp (syn_crn (syn_ctxp (syn_ccnv (syn_c1st))
                                  (syn_cin (syn_c1st) (syn_c2nd)))) (syn_c2nd)) (syn_caddcfn))))
                      (syn_cima (syn_ctxp (syn_ccom (syn_c1st) (syn_c1st))
                          (syn_ctxp (syn_ccom (syn_c2nd) (syn_c1st)) (syn_c2nd)))
                        (syn_caddcfn))))) (syn_crn (syn_ctxp (syn_cin (syn_c1st)
                      (syn_cxp (syn_cima (syn_ccnv (syn_c2nd)) (syn_csn (syn_c1c))) (syn_cvv)))
                    (syn_caddcfn)))))) (syn_crn (syn_ctxp (syn_ccnv (syn_crn (syn_cin (syn_cins3
                      (syn_ccnv (syn_cima (syn_ctxp (syn_crn (syn_ctxp (syn_ccnv (syn_c1st))
                                (syn_cin (syn_c1st) (syn_c2nd)))) (syn_c2nd)) (syn_caddcfn))))
                    (syn_cima (syn_ctxp (syn_ccom (syn_c1st) (syn_c1st))
                        (syn_ctxp (syn_ccom (syn_c2nd) (syn_c1st)) (syn_c2nd)))
                      (syn_caddcfn))))) (syn_crn (syn_ctxp (syn_cin (syn_c1st)
                    (syn_cxp (syn_cima (syn_ccnv (syn_c2nd)) (syn_csn (syn_c2c))) (syn_cvv)))
                  (syn_caddcfn)))))))
      (syn_w3o (.classEq (.cv a) (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n)))
        (.classEq (.cv a) (syn_cplc (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n)) (syn_c1c)))
        (.classEq (.cv a) (syn_cplc (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n)) (syn_c2c))))
      p0001 p0085
  have p0087 :=
    @g_rexbii
      (syn_wbr (.cv n) (syn_cun (syn_cun (syn_crn (syn_cin (syn_cins3 (syn_ccnv (syn_cima
                      (syn_ctxp (syn_crn (syn_ctxp (syn_ccnv (syn_c1st))
                            (syn_cin (syn_c1st) (syn_c2nd)))) (syn_c2nd)) (syn_caddcfn))))
                (syn_cima (syn_ctxp (syn_ccom (syn_c1st) (syn_c1st))
                    (syn_ctxp (syn_ccom (syn_c2nd) (syn_c1st)) (syn_c2nd))) (syn_caddcfn))))
            (syn_crn (syn_ctxp (syn_ccnv (syn_crn (syn_cin (syn_cins3 (syn_ccnv (syn_cima
                            (syn_ctxp (syn_crn (syn_ctxp (syn_ccnv (syn_c1st))
                                  (syn_cin (syn_c1st) (syn_c2nd)))) (syn_c2nd)) (syn_caddcfn))))
                      (syn_cima (syn_ctxp (syn_ccom (syn_c1st) (syn_c1st))
                          (syn_ctxp (syn_ccom (syn_c2nd) (syn_c1st)) (syn_c2nd)))
                        (syn_caddcfn))))) (syn_crn (syn_ctxp (syn_cin (syn_c1st)
                      (syn_cxp (syn_cima (syn_ccnv (syn_c2nd)) (syn_csn (syn_c1c))) (syn_cvv)))
                    (syn_caddcfn)))))) (syn_crn (syn_ctxp (syn_ccnv (syn_crn (syn_cin (syn_cins3
                      (syn_ccnv (syn_cima (syn_ctxp (syn_crn (syn_ctxp (syn_ccnv (syn_c1st))
                                (syn_cin (syn_c1st) (syn_c2nd)))) (syn_c2nd)) (syn_caddcfn))))
                    (syn_cima (syn_ctxp (syn_ccom (syn_c1st) (syn_c1st))
                        (syn_ctxp (syn_ccom (syn_c2nd) (syn_c1st)) (syn_c2nd)))
                      (syn_caddcfn))))) (syn_crn (syn_ctxp (syn_cin (syn_c1st)
                    (syn_cxp (syn_cima (syn_ccnv (syn_c2nd)) (syn_csn (syn_c2c))) (syn_cvv)))
                  (syn_caddcfn)))))) (.cv a))
      (syn_w3o (.classEq (.cv a) (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n)))
        (.classEq (.cv a) (syn_cplc (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n)) (syn_c1c)))
        (.classEq (.cv a) (syn_cplc (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n)) (syn_c2c))))
      n (syn_cnnc) p0086
  have p0088 :=
    @g_bitri
      (.classMem (.cv a) (syn_cima (syn_cun (syn_cun (syn_crn (syn_cin (syn_cins3 (syn_ccnv
                      (syn_cima (syn_ctxp (syn_crn (syn_ctxp (syn_ccnv (syn_c1st))
                              (syn_cin (syn_c1st) (syn_c2nd)))) (syn_c2nd)) (syn_caddcfn))))
                  (syn_cima (syn_ctxp (syn_ccom (syn_c1st) (syn_c1st))
                      (syn_ctxp (syn_ccom (syn_c2nd) (syn_c1st)) (syn_c2nd))) (syn_caddcfn))))
              (syn_crn (syn_ctxp (syn_ccnv (syn_crn (syn_cin (syn_cins3 (syn_ccnv (syn_cima
                              (syn_ctxp (syn_crn (syn_ctxp (syn_ccnv (syn_c1st))
                                    (syn_cin (syn_c1st) (syn_c2nd)))) (syn_c2nd))
                              (syn_caddcfn)))) (syn_cima
                          (syn_ctxp (syn_ccom (syn_c1st) (syn_c1st))
                            (syn_ctxp (syn_ccom (syn_c2nd) (syn_c1st)) (syn_c2nd)))
                          (syn_caddcfn))))) (syn_crn (syn_ctxp (syn_cin (syn_c1st)
                        (syn_cxp (syn_cima (syn_ccnv (syn_c2nd)) (syn_csn (syn_c1c)))
                          (syn_cvv))) (syn_caddcfn)))))) (syn_crn (syn_ctxp (syn_ccnv (syn_crn
                    (syn_cin (syn_cins3 (syn_ccnv (syn_cima (syn_ctxp (syn_crn
                                (syn_ctxp (syn_ccnv (syn_c1st))
                                  (syn_cin (syn_c1st) (syn_c2nd)))) (syn_c2nd)) (syn_caddcfn))))
                      (syn_cima (syn_ctxp (syn_ccom (syn_c1st) (syn_c1st))
                          (syn_ctxp (syn_ccom (syn_c2nd) (syn_c1st)) (syn_c2nd)))
                        (syn_caddcfn))))) (syn_crn (syn_ctxp (syn_cin (syn_c1st)
                      (syn_cxp (syn_cima (syn_ccnv (syn_c2nd)) (syn_csn (syn_c2c))) (syn_cvv)))
                    (syn_caddcfn)))))) (syn_cnnc)))
      (syn_wrex n (syn_cnnc) (syn_wbr (.cv n) (syn_cun (syn_cun (syn_crn (syn_cin (syn_cins3
                    (syn_ccnv (syn_cima (syn_ctxp (syn_crn (syn_ctxp (syn_ccnv (syn_c1st))
                              (syn_cin (syn_c1st) (syn_c2nd)))) (syn_c2nd)) (syn_caddcfn))))
                  (syn_cima (syn_ctxp (syn_ccom (syn_c1st) (syn_c1st))
                      (syn_ctxp (syn_ccom (syn_c2nd) (syn_c1st)) (syn_c2nd))) (syn_caddcfn))))
              (syn_crn (syn_ctxp (syn_ccnv (syn_crn (syn_cin (syn_cins3 (syn_ccnv (syn_cima
                              (syn_ctxp (syn_crn (syn_ctxp (syn_ccnv (syn_c1st))
                                    (syn_cin (syn_c1st) (syn_c2nd)))) (syn_c2nd))
                              (syn_caddcfn)))) (syn_cima
                          (syn_ctxp (syn_ccom (syn_c1st) (syn_c1st))
                            (syn_ctxp (syn_ccom (syn_c2nd) (syn_c1st)) (syn_c2nd)))
                          (syn_caddcfn))))) (syn_crn (syn_ctxp (syn_cin (syn_c1st)
                        (syn_cxp (syn_cima (syn_ccnv (syn_c2nd)) (syn_csn (syn_c1c)))
                          (syn_cvv))) (syn_caddcfn)))))) (syn_crn (syn_ctxp (syn_ccnv (syn_crn
                    (syn_cin (syn_cins3 (syn_ccnv (syn_cima (syn_ctxp (syn_crn
                                (syn_ctxp (syn_ccnv (syn_c1st))
                                  (syn_cin (syn_c1st) (syn_c2nd)))) (syn_c2nd)) (syn_caddcfn))))
                      (syn_cima (syn_ctxp (syn_ccom (syn_c1st) (syn_c1st))
                          (syn_ctxp (syn_ccom (syn_c2nd) (syn_c1st)) (syn_c2nd)))
                        (syn_caddcfn))))) (syn_crn (syn_ctxp (syn_cin (syn_c1st)
                      (syn_cxp (syn_cima (syn_ccnv (syn_c2nd)) (syn_csn (syn_c2c))) (syn_cvv)))
                    (syn_caddcfn)))))) (.cv a)))
      (syn_wrex n (syn_cnnc)
        (syn_w3o (.classEq (.cv a) (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n)))
          (.classEq (.cv a) (syn_cplc (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n)) (syn_c1c)))
          (.classEq (.cv a)
            (syn_cplc (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n)) (syn_c2c)))))
      p0000 p0087
  have p0089 :=
    @g_eqabi
      (syn_wrex n (syn_cnnc)
        (syn_w3o (.classEq (.cv a) (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n)))
          (.classEq (.cv a) (syn_cplc (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n)) (syn_c1c)))
          (.classEq (.cv a)
            (syn_cplc (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n)) (syn_c2c)))))
      a
      (syn_cima (syn_cun (syn_cun (syn_crn (syn_cin (syn_cins3 (syn_ccnv (syn_cima (syn_ctxp
                        (syn_crn (syn_ctxp (syn_ccnv (syn_c1st))
                            (syn_cin (syn_c1st) (syn_c2nd)))) (syn_c2nd)) (syn_caddcfn))))
                (syn_cima (syn_ctxp (syn_ccom (syn_c1st) (syn_c1st))
                    (syn_ctxp (syn_ccom (syn_c2nd) (syn_c1st)) (syn_c2nd))) (syn_caddcfn))))
            (syn_crn (syn_ctxp (syn_ccnv (syn_crn (syn_cin (syn_cins3 (syn_ccnv (syn_cima
                            (syn_ctxp (syn_crn (syn_ctxp (syn_ccnv (syn_c1st))
                                  (syn_cin (syn_c1st) (syn_c2nd)))) (syn_c2nd)) (syn_caddcfn))))
                      (syn_cima (syn_ctxp (syn_ccom (syn_c1st) (syn_c1st))
                          (syn_ctxp (syn_ccom (syn_c2nd) (syn_c1st)) (syn_c2nd)))
                        (syn_caddcfn))))) (syn_crn (syn_ctxp (syn_cin (syn_c1st)
                      (syn_cxp (syn_cima (syn_ccnv (syn_c2nd)) (syn_csn (syn_c1c))) (syn_cvv)))
                    (syn_caddcfn)))))) (syn_crn (syn_ctxp (syn_ccnv (syn_crn (syn_cin (syn_cins3
                      (syn_ccnv (syn_cima (syn_ctxp (syn_crn (syn_ctxp (syn_ccnv (syn_c1st))
                                (syn_cin (syn_c1st) (syn_c2nd)))) (syn_c2nd)) (syn_caddcfn))))
                    (syn_cima (syn_ctxp (syn_ccom (syn_c1st) (syn_c1st))
                        (syn_ctxp (syn_ccom (syn_c2nd) (syn_c1st)) (syn_c2nd)))
                      (syn_caddcfn))))) (syn_crn (syn_ctxp (syn_cin (syn_c1st)
                    (syn_cxp (syn_cima (syn_ccnv (syn_c2nd)) (syn_csn (syn_c2c))) (syn_cvv)))
                  (syn_caddcfn)))))) (syn_cnnc))
      dv_cache_0017 p0088
  have p0090 := @g_n_1stex
  have p0091 := @g_cnvex (syn_c1st) p0090
  have p0093 := @g_n_2ndex
  have p0094 := @g_inex (syn_c1st) (syn_c2nd) p0090 p0093
  have p0095 := @g_txpex (syn_ccnv (syn_c1st)) (syn_cin (syn_c1st) (syn_c2nd)) p0091 p0094
  have p0096 :=
    @g_rnex (syn_ctxp (syn_ccnv (syn_c1st)) (syn_cin (syn_c1st) (syn_c2nd))) p0095
  have p0098 :=
    @g_txpex (syn_crn (syn_ctxp (syn_ccnv (syn_c1st)) (syn_cin (syn_c1st) (syn_c2nd))))
      (syn_c2nd) p0096 p0093
  have p0099 := @g_addcfnex
  have p0100 :=
    @g_imaex
      (syn_ctxp (syn_crn (syn_ctxp (syn_ccnv (syn_c1st)) (syn_cin (syn_c1st) (syn_c2nd))))
        (syn_c2nd))
      (syn_caddcfn) p0098 p0099
  have p0101 :=
    @g_cnvex
      (syn_cima (syn_ctxp
          (syn_crn (syn_ctxp (syn_ccnv (syn_c1st)) (syn_cin (syn_c1st) (syn_c2nd)))) (syn_c2nd))
        (syn_caddcfn))
      p0100
  have p0102 :=
    @g_ins3ex
      (syn_ccnv (syn_cima (syn_ctxp
            (syn_crn (syn_ctxp (syn_ccnv (syn_c1st)) (syn_cin (syn_c1st) (syn_c2nd))))
            (syn_c2nd)) (syn_caddcfn)))
      p0101
  have p0105 := @g_coex (syn_c1st) (syn_c1st) p0090 p0090
  have p0108 := @g_coex (syn_c2nd) (syn_c1st) p0093 p0090
  have p0110 := @g_txpex (syn_ccom (syn_c2nd) (syn_c1st)) (syn_c2nd) p0108 p0093
  have p0111 :=
    @g_txpex (syn_ccom (syn_c1st) (syn_c1st))
      (syn_ctxp (syn_ccom (syn_c2nd) (syn_c1st)) (syn_c2nd)) p0105 p0110
  have p0113 :=
    @g_imaex
      (syn_ctxp (syn_ccom (syn_c1st) (syn_c1st))
        (syn_ctxp (syn_ccom (syn_c2nd) (syn_c1st)) (syn_c2nd)))
      (syn_caddcfn) p0111 p0099
  have p0114 :=
    @g_inex
      (syn_cins3 (syn_ccnv (syn_cima (syn_ctxp
              (syn_crn (syn_ctxp (syn_ccnv (syn_c1st)) (syn_cin (syn_c1st) (syn_c2nd))))
              (syn_c2nd)) (syn_caddcfn))))
      (syn_cima (syn_ctxp (syn_ccom (syn_c1st) (syn_c1st))
          (syn_ctxp (syn_ccom (syn_c2nd) (syn_c1st)) (syn_c2nd))) (syn_caddcfn))
      p0102 p0113
  have p0115 :=
    @g_rnex
      (syn_cin (syn_cins3 (syn_ccnv (syn_cima (syn_ctxp
                (syn_crn (syn_ctxp (syn_ccnv (syn_c1st)) (syn_cin (syn_c1st) (syn_c2nd))))
                (syn_c2nd)) (syn_caddcfn)))) (syn_cima
          (syn_ctxp (syn_ccom (syn_c1st) (syn_c1st))
            (syn_ctxp (syn_ccom (syn_c2nd) (syn_c1st)) (syn_c2nd))) (syn_caddcfn)))
      p0114
  have p0116 :=
    @g_cnvex
      (syn_crn (syn_cin (syn_cins3 (syn_ccnv (syn_cima (syn_ctxp (syn_crn
                    (syn_ctxp (syn_ccnv (syn_c1st)) (syn_cin (syn_c1st) (syn_c2nd))))
                  (syn_c2nd)) (syn_caddcfn)))) (syn_cima
            (syn_ctxp (syn_ccom (syn_c1st) (syn_c1st))
              (syn_ctxp (syn_ccom (syn_c2nd) (syn_c1st)) (syn_c2nd))) (syn_caddcfn))))
      p0115
  have p0119 := @g_cnvex (syn_c2nd) p0093
  have p0120 := @g_snex (syn_c1c)
  have p0121 := @g_imaex (syn_ccnv (syn_c2nd)) (syn_csn (syn_c1c)) p0119 p0120
  have p0122 := @g_vvex
  have p0123 :=
    @g_xpex (syn_cima (syn_ccnv (syn_c2nd)) (syn_csn (syn_c1c))) (syn_cvv) p0121 p0122
  have p0124 :=
    @g_inex (syn_c1st)
      (syn_cxp (syn_cima (syn_ccnv (syn_c2nd)) (syn_csn (syn_c1c))) (syn_cvv)) p0090 p0123
  have p0126 :=
    @g_txpex
      (syn_cin (syn_c1st)
        (syn_cxp (syn_cima (syn_ccnv (syn_c2nd)) (syn_csn (syn_c1c))) (syn_cvv)))
      (syn_caddcfn) p0124 p0099
  have p0127 :=
    @g_rnex
      (syn_ctxp (syn_cin (syn_c1st)
          (syn_cxp (syn_cima (syn_ccnv (syn_c2nd)) (syn_csn (syn_c1c))) (syn_cvv)))
        (syn_caddcfn))
      p0126
  have p0128 :=
    @g_txpex
      (syn_ccnv (syn_crn (syn_cin (syn_cins3 (syn_ccnv (syn_cima (syn_ctxp (syn_crn
                      (syn_ctxp (syn_ccnv (syn_c1st)) (syn_cin (syn_c1st) (syn_c2nd))))
                    (syn_c2nd)) (syn_caddcfn)))) (syn_cima
              (syn_ctxp (syn_ccom (syn_c1st) (syn_c1st))
                (syn_ctxp (syn_ccom (syn_c2nd) (syn_c1st)) (syn_c2nd))) (syn_caddcfn)))))
      (syn_crn (syn_ctxp (syn_cin (syn_c1st)
            (syn_cxp (syn_cima (syn_ccnv (syn_c2nd)) (syn_csn (syn_c1c))) (syn_cvv)))
          (syn_caddcfn)))
      p0116 p0127
  have p0129 :=
    @g_rnex
      (syn_ctxp (syn_ccnv (syn_crn (syn_cin (syn_cins3 (syn_ccnv (syn_cima (syn_ctxp (syn_crn
                        (syn_ctxp (syn_ccnv (syn_c1st)) (syn_cin (syn_c1st) (syn_c2nd))))
                      (syn_c2nd)) (syn_caddcfn)))) (syn_cima
                (syn_ctxp (syn_ccom (syn_c1st) (syn_c1st))
                  (syn_ctxp (syn_ccom (syn_c2nd) (syn_c1st)) (syn_c2nd))) (syn_caddcfn)))))
        (syn_crn (syn_ctxp (syn_cin (syn_c1st)
              (syn_cxp (syn_cima (syn_ccnv (syn_c2nd)) (syn_csn (syn_c1c))) (syn_cvv)))
            (syn_caddcfn))))
      p0128
  have p0130 :=
    @g_unex
      (syn_crn (syn_cin (syn_cins3 (syn_ccnv (syn_cima (syn_ctxp (syn_crn
                    (syn_ctxp (syn_ccnv (syn_c1st)) (syn_cin (syn_c1st) (syn_c2nd))))
                  (syn_c2nd)) (syn_caddcfn)))) (syn_cima
            (syn_ctxp (syn_ccom (syn_c1st) (syn_c1st))
              (syn_ctxp (syn_ccom (syn_c2nd) (syn_c1st)) (syn_c2nd))) (syn_caddcfn))))
      (syn_crn (syn_ctxp (syn_ccnv (syn_crn (syn_cin (syn_cins3 (syn_ccnv (syn_cima (syn_ctxp
                        (syn_crn (syn_ctxp (syn_ccnv (syn_c1st))
                            (syn_cin (syn_c1st) (syn_c2nd)))) (syn_c2nd)) (syn_caddcfn))))
                (syn_cima (syn_ctxp (syn_ccom (syn_c1st) (syn_c1st))
                    (syn_ctxp (syn_ccom (syn_c2nd) (syn_c1st)) (syn_c2nd))) (syn_caddcfn)))))
          (syn_crn (syn_ctxp (syn_cin (syn_c1st)
                (syn_cxp (syn_cima (syn_ccnv (syn_c2nd)) (syn_csn (syn_c1c))) (syn_cvv)))
              (syn_caddcfn)))))
      p0115 p0129
  have p0132 := @g_snex (syn_c2c)
  have p0133 := @g_imaex (syn_ccnv (syn_c2nd)) (syn_csn (syn_c2c)) p0119 p0132
  have p0135 :=
    @g_xpex (syn_cima (syn_ccnv (syn_c2nd)) (syn_csn (syn_c2c))) (syn_cvv) p0133 p0122
  have p0136 :=
    @g_inex (syn_c1st)
      (syn_cxp (syn_cima (syn_ccnv (syn_c2nd)) (syn_csn (syn_c2c))) (syn_cvv)) p0090 p0135
  have p0138 :=
    @g_txpex
      (syn_cin (syn_c1st)
        (syn_cxp (syn_cima (syn_ccnv (syn_c2nd)) (syn_csn (syn_c2c))) (syn_cvv)))
      (syn_caddcfn) p0136 p0099
  have p0139 :=
    @g_rnex
      (syn_ctxp (syn_cin (syn_c1st)
          (syn_cxp (syn_cima (syn_ccnv (syn_c2nd)) (syn_csn (syn_c2c))) (syn_cvv)))
        (syn_caddcfn))
      p0138
  have p0140 :=
    @g_txpex
      (syn_ccnv (syn_crn (syn_cin (syn_cins3 (syn_ccnv (syn_cima (syn_ctxp (syn_crn
                      (syn_ctxp (syn_ccnv (syn_c1st)) (syn_cin (syn_c1st) (syn_c2nd))))
                    (syn_c2nd)) (syn_caddcfn)))) (syn_cima
              (syn_ctxp (syn_ccom (syn_c1st) (syn_c1st))
                (syn_ctxp (syn_ccom (syn_c2nd) (syn_c1st)) (syn_c2nd))) (syn_caddcfn)))))
      (syn_crn (syn_ctxp (syn_cin (syn_c1st)
            (syn_cxp (syn_cima (syn_ccnv (syn_c2nd)) (syn_csn (syn_c2c))) (syn_cvv)))
          (syn_caddcfn)))
      p0116 p0139
  have p0141 :=
    @g_rnex
      (syn_ctxp (syn_ccnv (syn_crn (syn_cin (syn_cins3 (syn_ccnv (syn_cima (syn_ctxp (syn_crn
                        (syn_ctxp (syn_ccnv (syn_c1st)) (syn_cin (syn_c1st) (syn_c2nd))))
                      (syn_c2nd)) (syn_caddcfn)))) (syn_cima
                (syn_ctxp (syn_ccom (syn_c1st) (syn_c1st))
                  (syn_ctxp (syn_ccom (syn_c2nd) (syn_c1st)) (syn_c2nd))) (syn_caddcfn)))))
        (syn_crn (syn_ctxp (syn_cin (syn_c1st)
              (syn_cxp (syn_cima (syn_ccnv (syn_c2nd)) (syn_csn (syn_c2c))) (syn_cvv)))
            (syn_caddcfn))))
      p0140
  have p0142 :=
    @g_unex
      (syn_cun (syn_crn (syn_cin (syn_cins3 (syn_ccnv (syn_cima (syn_ctxp (syn_crn
                      (syn_ctxp (syn_ccnv (syn_c1st)) (syn_cin (syn_c1st) (syn_c2nd))))
                    (syn_c2nd)) (syn_caddcfn)))) (syn_cima
              (syn_ctxp (syn_ccom (syn_c1st) (syn_c1st))
                (syn_ctxp (syn_ccom (syn_c2nd) (syn_c1st)) (syn_c2nd))) (syn_caddcfn))))
        (syn_crn (syn_ctxp (syn_ccnv (syn_crn (syn_cin (syn_cins3 (syn_ccnv (syn_cima (syn_ctxp
                          (syn_crn (syn_ctxp (syn_ccnv (syn_c1st))
                              (syn_cin (syn_c1st) (syn_c2nd)))) (syn_c2nd)) (syn_caddcfn))))
                  (syn_cima (syn_ctxp (syn_ccom (syn_c1st) (syn_c1st))
                      (syn_ctxp (syn_ccom (syn_c2nd) (syn_c1st)) (syn_c2nd))) (syn_caddcfn)))))
            (syn_crn (syn_ctxp (syn_cin (syn_c1st)
                  (syn_cxp (syn_cima (syn_ccnv (syn_c2nd)) (syn_csn (syn_c1c))) (syn_cvv)))
                (syn_caddcfn))))))
      (syn_crn (syn_ctxp (syn_ccnv (syn_crn (syn_cin (syn_cins3 (syn_ccnv (syn_cima (syn_ctxp
                        (syn_crn (syn_ctxp (syn_ccnv (syn_c1st))
                            (syn_cin (syn_c1st) (syn_c2nd)))) (syn_c2nd)) (syn_caddcfn))))
                (syn_cima (syn_ctxp (syn_ccom (syn_c1st) (syn_c1st))
                    (syn_ctxp (syn_ccom (syn_c2nd) (syn_c1st)) (syn_c2nd))) (syn_caddcfn)))))
          (syn_crn (syn_ctxp (syn_cin (syn_c1st)
                (syn_cxp (syn_cima (syn_ccnv (syn_c2nd)) (syn_csn (syn_c2c))) (syn_cvv)))
              (syn_caddcfn)))))
      p0130 p0141
  have p0143 := @g_nncex
  have p0144 :=
    @g_imaex
      (syn_cun (syn_cun (syn_crn (syn_cin (syn_cins3 (syn_ccnv (syn_cima (syn_ctxp (syn_crn
                        (syn_ctxp (syn_ccnv (syn_c1st)) (syn_cin (syn_c1st) (syn_c2nd))))
                      (syn_c2nd)) (syn_caddcfn)))) (syn_cima
                (syn_ctxp (syn_ccom (syn_c1st) (syn_c1st))
                  (syn_ctxp (syn_ccom (syn_c2nd) (syn_c1st)) (syn_c2nd))) (syn_caddcfn))))
          (syn_crn (syn_ctxp (syn_ccnv (syn_crn (syn_cin (syn_cins3 (syn_ccnv (syn_cima
                          (syn_ctxp (syn_crn (syn_ctxp (syn_ccnv (syn_c1st))
                                (syn_cin (syn_c1st) (syn_c2nd)))) (syn_c2nd)) (syn_caddcfn))))
                    (syn_cima (syn_ctxp (syn_ccom (syn_c1st) (syn_c1st))
                        (syn_ctxp (syn_ccom (syn_c2nd) (syn_c1st)) (syn_c2nd)))
                      (syn_caddcfn))))) (syn_crn (syn_ctxp (syn_cin (syn_c1st)
                    (syn_cxp (syn_cima (syn_ccnv (syn_c2nd)) (syn_csn (syn_c1c))) (syn_cvv)))
                  (syn_caddcfn)))))) (syn_crn (syn_ctxp (syn_ccnv (syn_crn (syn_cin (syn_cins3
                    (syn_ccnv (syn_cima (syn_ctxp (syn_crn (syn_ctxp (syn_ccnv (syn_c1st))
                              (syn_cin (syn_c1st) (syn_c2nd)))) (syn_c2nd)) (syn_caddcfn))))
                  (syn_cima (syn_ctxp (syn_ccom (syn_c1st) (syn_c1st))
                      (syn_ctxp (syn_ccom (syn_c2nd) (syn_c1st)) (syn_c2nd))) (syn_caddcfn)))))
            (syn_crn (syn_ctxp (syn_cin (syn_c1st)
                  (syn_cxp (syn_cima (syn_ccnv (syn_c2nd)) (syn_csn (syn_c2c))) (syn_cvv)))
                (syn_caddcfn))))))
      (syn_cnnc) p0142 p0143
  have p0145 :=
    @g_eqeltrri
      (syn_cima (syn_cun (syn_cun (syn_crn (syn_cin (syn_cins3 (syn_ccnv (syn_cima (syn_ctxp
                        (syn_crn (syn_ctxp (syn_ccnv (syn_c1st))
                            (syn_cin (syn_c1st) (syn_c2nd)))) (syn_c2nd)) (syn_caddcfn))))
                (syn_cima (syn_ctxp (syn_ccom (syn_c1st) (syn_c1st))
                    (syn_ctxp (syn_ccom (syn_c2nd) (syn_c1st)) (syn_c2nd))) (syn_caddcfn))))
            (syn_crn (syn_ctxp (syn_ccnv (syn_crn (syn_cin (syn_cins3 (syn_ccnv (syn_cima
                            (syn_ctxp (syn_crn (syn_ctxp (syn_ccnv (syn_c1st))
                                  (syn_cin (syn_c1st) (syn_c2nd)))) (syn_c2nd)) (syn_caddcfn))))
                      (syn_cima (syn_ctxp (syn_ccom (syn_c1st) (syn_c1st))
                          (syn_ctxp (syn_ccom (syn_c2nd) (syn_c1st)) (syn_c2nd)))
                        (syn_caddcfn))))) (syn_crn (syn_ctxp (syn_cin (syn_c1st)
                      (syn_cxp (syn_cima (syn_ccnv (syn_c2nd)) (syn_csn (syn_c1c))) (syn_cvv)))
                    (syn_caddcfn)))))) (syn_crn (syn_ctxp (syn_ccnv (syn_crn (syn_cin (syn_cins3
                      (syn_ccnv (syn_cima (syn_ctxp (syn_crn (syn_ctxp (syn_ccnv (syn_c1st))
                                (syn_cin (syn_c1st) (syn_c2nd)))) (syn_c2nd)) (syn_caddcfn))))
                    (syn_cima (syn_ctxp (syn_ccom (syn_c1st) (syn_c1st))
                        (syn_ctxp (syn_ccom (syn_c2nd) (syn_c1st)) (syn_c2nd)))
                      (syn_caddcfn))))) (syn_crn (syn_ctxp (syn_cin (syn_c1st)
                    (syn_cxp (syn_cima (syn_ccnv (syn_c2nd)) (syn_csn (syn_c2c))) (syn_cvv)))
                  (syn_caddcfn)))))) (syn_cnnc))
      (.cab a (syn_wrex n (syn_cnnc)
          (syn_w3o (.classEq (.cv a) (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n)))
            (.classEq (.cv a)
              (syn_cplc (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n)) (syn_c1c)))
            (.classEq (.cv a)
              (syn_cplc (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n)) (syn_c2c))))))
      (syn_cvv) p0089 p0144
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

@[expose]
noncomputable def g_nncdiv3 (A : Class) (n : Var) (dv_A_n : n ∉ A.fv) :
    Nominal.NPrf
      (.imp (.classMem A (syn_cnnc)) (syn_wrex n (syn_cnnc)
          (syn_w3o (.classEq A (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n))) (.classEq A
              (syn_cplc (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n)) (syn_c1c))) (.classEq A
              (syn_cplc (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n)) (syn_c2c)))))) :=
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
  have dv_cache_0002 : n ∉ ((Wff.classEq (.cv a) (syn_c0c))).fv :=
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
  have dv_cache_0004 : n ∉ ((Wff.classEq (.cv a) (syn_cplc (.cv m) (syn_c1c)))).fv :=
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
  have dv_cache_0006 : n ∉ ((syn_c0c)).fv :=
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
  have dv_cache_0007 : n ∉ ((syn_cnnc)).fv :=
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
      ((syn_w3o (.classEq (syn_c0c) (syn_cplc (syn_cplc (syn_c0c) (syn_c0c)) (syn_c0c)))
          (.classEq (syn_c0c)
            (syn_cplc (syn_cplc (syn_cplc (syn_c0c) (syn_c0c)) (syn_c0c)) (syn_c1c)))
          (.classEq (syn_c0c) (syn_cplc (syn_cplc (syn_cplc (syn_c0c) (syn_c0c)) (syn_c0c))
              (syn_c2c))))).fv :=
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
  have dv_cache_0009 : a ∉ ((syn_cplc (.cv n) (syn_c1c))).fv :=
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
  have dv_cache_0010 : a ∉ ((syn_cnnc)).fv :=
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
      ((Wff.classEq (syn_cplc (syn_cplc (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n)) (syn_c2c))
            (syn_c1c))
          (syn_cplc (syn_cplc (syn_cplc (.cv n) (syn_c1c)) (syn_cplc (.cv n) (syn_c1c)))
            (syn_cplc (.cv n) (syn_c1c))))).fv :=
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
          (syn_cplc (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n)) (syn_c2c)))).fv :=
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
      ((syn_wrex a (syn_cnnc) (.classEq (syn_cplc (.cv m) (syn_c1c))
            (syn_cplc (syn_cplc (.cv a) (.cv a)) (.cv a))))).fv :=
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
      ((Wff.classEq (syn_cplc (.cv m) (syn_c1c))
          (syn_cplc (syn_cplc (.cv a) (.cv a)) (.cv a)))).fv :=
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
      ((Wff.classEq (syn_cplc (.cv m) (syn_c1c))
          (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n)))).fv :=
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
      ((syn_wrex n (syn_cnnc)
          (syn_w3o (.classEq (.cv m) (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n)))
            (.classEq (.cv m)
              (syn_cplc (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n)) (syn_c1c)))
            (.classEq (.cv m)
              (syn_cplc (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n)) (syn_c2c)))))).fv :=
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
      ((syn_wrex n (syn_cnnc)
          (syn_w3o (.classEq (.cv a) (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n)))
            (.classEq (.cv a)
              (syn_cplc (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n)) (syn_c1c)))
            (.classEq (.cv a)
              (syn_cplc (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n)) (syn_c2c)))))).fv :=
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
      ((syn_wrex n (syn_cnnc)
          (syn_w3o (.classEq (syn_c0c) (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n)))
            (.classEq (syn_c0c)
              (syn_cplc (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n)) (syn_c1c)))
            (.classEq (syn_c0c)
              (syn_cplc (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n)) (syn_c2c)))))).fv :=
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
      ((syn_wrex n (syn_cnnc)
          (syn_w3o (.classEq A (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n))) (.classEq A
              (syn_cplc (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n)) (syn_c1c))) (.classEq A
              (syn_cplc (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n)) (syn_c2c)))))).fv :=
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
      ((syn_wrex n (syn_cnnc) (syn_w3o (.classEq (syn_cplc (.cv m) (syn_c1c))
              (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n)))
            (.classEq (syn_cplc (.cv m) (syn_c1c))
              (syn_cplc (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n)) (syn_c1c)))
            (.classEq (syn_cplc (.cv m) (syn_c1c))
              (syn_cplc (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n)) (syn_c2c)))))).fv :=
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
  have p0000 := @g_nncdiv3lem2 n a dv_cache_0001
  have p0001 := @g_eqeq1 (.cv a) (syn_c0c) (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n))
  have p0002 :=
    @g_eqeq1 (.cv a) (syn_c0c)
      (syn_cplc (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n)) (syn_c1c))
  have p0003 :=
    @g_eqeq1 (.cv a) (syn_c0c)
      (syn_cplc (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n)) (syn_c2c))
  have p0004 :=
    @g_n_3orbi123d (.classEq (.cv a) (syn_c0c))
      (.classEq (.cv a) (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n)))
      (.classEq (syn_c0c) (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n)))
      (.classEq (.cv a) (syn_cplc (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n)) (syn_c1c)))
      (.classEq (syn_c0c) (syn_cplc (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n)) (syn_c1c)))
      (.classEq (.cv a) (syn_cplc (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n)) (syn_c2c)))
      (.classEq (syn_c0c) (syn_cplc (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n)) (syn_c2c)))
      p0001 p0002 p0003
  have p0005 :=
    @g_rexbidv (.classEq (.cv a) (syn_c0c))
      (syn_w3o (.classEq (.cv a) (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n)))
        (.classEq (.cv a) (syn_cplc (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n)) (syn_c1c)))
        (.classEq (.cv a) (syn_cplc (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n)) (syn_c2c))))
      (syn_w3o (.classEq (syn_c0c) (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n)))
        (.classEq (syn_c0c) (syn_cplc (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n)) (syn_c1c)))
        (.classEq (syn_c0c) (syn_cplc (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n)) (syn_c2c))))
      n (syn_cnnc) dv_cache_0002 p0004
  have p0006 := @g_eqeq1 (.cv a) (.cv m) (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n))
  have p0007 :=
    @g_eqeq1 (.cv a) (.cv m)
      (syn_cplc (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n)) (syn_c1c))
  have p0008 :=
    @g_eqeq1 (.cv a) (.cv m)
      (syn_cplc (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n)) (syn_c2c))
  have p0009_e00_recanon :
    Nominal.NPrf
      (.imp (.objEq a m)
        (syn_wb (.classEq (.cv a) (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n)))
          (.classEq (.cv m) (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n))))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wb syn_cplc syn_wrex syn_wex syn_wa
        simp (config :=
          { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_class_cv]
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
        · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0006
  have p0009_e01_recanon :
    Nominal.NPrf
      (.imp (.objEq a m) (syn_wb (.classEq (.cv a)
            (syn_cplc (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n)) (syn_c1c)))
          (.classEq (.cv m)
            (syn_cplc (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n)) (syn_c1c))))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wb syn_cplc syn_wrex syn_wex syn_wa syn_c1c
        simp (config :=
          { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_class_cv]
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
        · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0007
  have p0009_e02_recanon :
    Nominal.NPrf
      (.imp (.objEq a m) (syn_wb (.classEq (.cv a)
            (syn_cplc (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n)) (syn_c2c)))
          (.classEq (.cv m)
            (syn_cplc (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n)) (syn_c2c))))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wb syn_cplc syn_wrex syn_wex syn_wa syn_c2c syn_cnc syn_cec syn_cima
          syn_csn syn_cen syn_copab syn_cpr syn_cun syn_cnin syn_wnan syn_ccompl syn_c0
          syn_cdif syn_cin syn_cvv
        simp (config :=
          { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_class_cv]
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
        · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0008
  have p0009 :=
    @g_n_3orbi123d (.objEq a m)
      (.classEq (.cv a) (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n)))
      (.classEq (.cv m) (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n)))
      (.classEq (.cv a) (syn_cplc (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n)) (syn_c1c)))
      (.classEq (.cv m) (syn_cplc (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n)) (syn_c1c)))
      (.classEq (.cv a) (syn_cplc (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n)) (syn_c2c)))
      (.classEq (.cv m) (syn_cplc (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n)) (syn_c2c)))
      p0009_e00_recanon p0009_e01_recanon p0009_e02_recanon
  have p0010 :=
    @g_rexbidv (.objEq a m)
      (syn_w3o (.classEq (.cv a) (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n)))
        (.classEq (.cv a) (syn_cplc (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n)) (syn_c1c)))
        (.classEq (.cv a) (syn_cplc (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n)) (syn_c2c))))
      (syn_w3o (.classEq (.cv m) (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n)))
        (.classEq (.cv m) (syn_cplc (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n)) (syn_c1c)))
        (.classEq (.cv m) (syn_cplc (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n)) (syn_c2c))))
      n (syn_cnnc) dv_cache_0003 p0009
  have p0011 :=
    @g_eqeq1 (.cv a) (syn_cplc (.cv m) (syn_c1c))
      (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n))
  have p0012 :=
    @g_eqeq1 (.cv a) (syn_cplc (.cv m) (syn_c1c))
      (syn_cplc (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n)) (syn_c1c))
  have p0013 :=
    @g_eqeq1 (.cv a) (syn_cplc (.cv m) (syn_c1c))
      (syn_cplc (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n)) (syn_c2c))
  have p0014 :=
    @g_n_3orbi123d (.classEq (.cv a) (syn_cplc (.cv m) (syn_c1c)))
      (.classEq (.cv a) (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n)))
      (.classEq (syn_cplc (.cv m) (syn_c1c)) (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n)))
      (.classEq (.cv a) (syn_cplc (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n)) (syn_c1c)))
      (.classEq (syn_cplc (.cv m) (syn_c1c))
        (syn_cplc (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n)) (syn_c1c)))
      (.classEq (.cv a) (syn_cplc (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n)) (syn_c2c)))
      (.classEq (syn_cplc (.cv m) (syn_c1c))
        (syn_cplc (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n)) (syn_c2c)))
      p0011 p0012 p0013
  have p0015 :=
    @g_rexbidv (.classEq (.cv a) (syn_cplc (.cv m) (syn_c1c)))
      (syn_w3o (.classEq (.cv a) (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n)))
        (.classEq (.cv a) (syn_cplc (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n)) (syn_c1c)))
        (.classEq (.cv a) (syn_cplc (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n)) (syn_c2c))))
      (syn_w3o (.classEq (syn_cplc (.cv m) (syn_c1c))
          (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n))) (.classEq (syn_cplc (.cv m) (syn_c1c))
          (syn_cplc (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n)) (syn_c1c)))
        (.classEq (syn_cplc (.cv m) (syn_c1c))
          (syn_cplc (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n)) (syn_c2c))))
      n (syn_cnnc) dv_cache_0004 p0014
  have p0016 := @g_eqeq1 (.cv a) A (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n))
  have p0017 :=
    @g_eqeq1 (.cv a) A (syn_cplc (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n)) (syn_c1c))
  have p0018 :=
    @g_eqeq1 (.cv a) A (syn_cplc (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n)) (syn_c2c))
  have p0019 :=
    @g_n_3orbi123d (.classEq (.cv a) A)
      (.classEq (.cv a) (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n)))
      (.classEq A (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n)))
      (.classEq (.cv a) (syn_cplc (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n)) (syn_c1c)))
      (.classEq A (syn_cplc (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n)) (syn_c1c)))
      (.classEq (.cv a) (syn_cplc (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n)) (syn_c2c)))
      (.classEq A (syn_cplc (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n)) (syn_c2c)))
      p0016 p0017 p0018
  have p0020 :=
    @g_rexbidv (.classEq (.cv a) A)
      (syn_w3o (.classEq (.cv a) (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n)))
        (.classEq (.cv a) (syn_cplc (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n)) (syn_c1c)))
        (.classEq (.cv a) (syn_cplc (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n)) (syn_c2c))))
      (syn_w3o (.classEq A (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n)))
        (.classEq A (syn_cplc (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n)) (syn_c1c)))
        (.classEq A (syn_cplc (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n)) (syn_c2c))))
      n (syn_cnnc) dv_cache_0005 p0019
  have p0021 := @g_peano1
  have p0022 := @g_addcid1 (syn_cplc (syn_c0c) (syn_c0c))
  have p0023 := @g_addcid2 (syn_c0c)
  have p0024 :=
    @g_eqtr2i (syn_cplc (syn_cplc (syn_c0c) (syn_c0c)) (syn_c0c))
      (syn_cplc (syn_c0c) (syn_c0c)) (syn_c0c) p0022 p0023
  have p0025 :=
    @g_n_3mix1 (.classEq (syn_c0c) (syn_cplc (syn_cplc (syn_c0c) (syn_c0c)) (syn_c0c)))
      (.classEq (syn_c0c)
        (syn_cplc (syn_cplc (syn_cplc (syn_c0c) (syn_c0c)) (syn_c0c)) (syn_c1c)))
      (.classEq (syn_c0c)
        (syn_cplc (syn_cplc (syn_cplc (syn_c0c) (syn_c0c)) (syn_c0c)) (syn_c2c)))
  have p0026 := Nominal.mp p0024 p0025
  have p0027 := @g_addceq12 (.cv n) (.cv n) (syn_c0c) (syn_c0c)
  have p0028 :=
    @g_anidms (.classEq (.cv n) (syn_c0c))
      (.classEq (syn_cplc (.cv n) (.cv n)) (syn_cplc (syn_c0c) (syn_c0c))) p0027
  have p0029 := @g_id (.classEq (.cv n) (syn_c0c))
  have p0030 :=
    @g_addceq12d (.classEq (.cv n) (syn_c0c)) (syn_cplc (.cv n) (.cv n))
      (syn_cplc (syn_c0c) (syn_c0c)) (.cv n) (syn_c0c) p0028 p0029
  have p0031 :=
    @g_eqeq2d (.classEq (.cv n) (syn_c0c)) (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n))
      (syn_cplc (syn_cplc (syn_c0c) (syn_c0c)) (syn_c0c)) (syn_c0c) p0030
  have p0032 :=
    @g_addceq1d (.classEq (.cv n) (syn_c0c)) (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n))
      (syn_cplc (syn_cplc (syn_c0c) (syn_c0c)) (syn_c0c)) (syn_c1c) p0030
  have p0033 :=
    @g_eqeq2d (.classEq (.cv n) (syn_c0c))
      (syn_cplc (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n)) (syn_c1c))
      (syn_cplc (syn_cplc (syn_cplc (syn_c0c) (syn_c0c)) (syn_c0c)) (syn_c1c)) (syn_c0c)
      p0032
  have p0034 :=
    @g_addceq1d (.classEq (.cv n) (syn_c0c)) (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n))
      (syn_cplc (syn_cplc (syn_c0c) (syn_c0c)) (syn_c0c)) (syn_c2c) p0030
  have p0035 :=
    @g_eqeq2d (.classEq (.cv n) (syn_c0c))
      (syn_cplc (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n)) (syn_c2c))
      (syn_cplc (syn_cplc (syn_cplc (syn_c0c) (syn_c0c)) (syn_c0c)) (syn_c2c)) (syn_c0c)
      p0034
  have p0036 :=
    @g_n_3orbi123d (.classEq (.cv n) (syn_c0c))
      (.classEq (syn_c0c) (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n)))
      (.classEq (syn_c0c) (syn_cplc (syn_cplc (syn_c0c) (syn_c0c)) (syn_c0c)))
      (.classEq (syn_c0c) (syn_cplc (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n)) (syn_c1c)))
      (.classEq (syn_c0c)
        (syn_cplc (syn_cplc (syn_cplc (syn_c0c) (syn_c0c)) (syn_c0c)) (syn_c1c)))
      (.classEq (syn_c0c) (syn_cplc (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n)) (syn_c2c)))
      (.classEq (syn_c0c)
        (syn_cplc (syn_cplc (syn_cplc (syn_c0c) (syn_c0c)) (syn_c0c)) (syn_c2c)))
      p0031 p0033 p0035
  have p0037 :=
    @g_rspcev
      (syn_w3o (.classEq (syn_c0c) (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n)))
        (.classEq (syn_c0c) (syn_cplc (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n)) (syn_c1c)))
        (.classEq (syn_c0c) (syn_cplc (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n)) (syn_c2c))))
      (syn_w3o (.classEq (syn_c0c) (syn_cplc (syn_cplc (syn_c0c) (syn_c0c)) (syn_c0c)))
        (.classEq (syn_c0c)
          (syn_cplc (syn_cplc (syn_cplc (syn_c0c) (syn_c0c)) (syn_c0c)) (syn_c1c)))
        (.classEq (syn_c0c)
          (syn_cplc (syn_cplc (syn_cplc (syn_c0c) (syn_c0c)) (syn_c0c)) (syn_c2c))))
      n (syn_c0c) (syn_cnnc) dv_cache_0006 dv_cache_0007 dv_cache_0008 p0036
  have p0038 :=
    @g_mp2an (.classMem (syn_c0c) (syn_cnnc))
      (syn_w3o (.classEq (syn_c0c) (syn_cplc (syn_cplc (syn_c0c) (syn_c0c)) (syn_c0c)))
        (.classEq (syn_c0c)
          (syn_cplc (syn_cplc (syn_cplc (syn_c0c) (syn_c0c)) (syn_c0c)) (syn_c1c)))
        (.classEq (syn_c0c)
          (syn_cplc (syn_cplc (syn_cplc (syn_c0c) (syn_c0c)) (syn_c0c)) (syn_c2c))))
      (syn_wrex n (syn_cnnc)
        (syn_w3o (.classEq (syn_c0c) (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n)))
          (.classEq (syn_c0c)
            (syn_cplc (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n)) (syn_c1c)))
          (.classEq (syn_c0c)
            (syn_cplc (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n)) (syn_c2c)))))
      p0021 p0026 p0037
  have p0039 := @g_addceq1 (.cv m) (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n)) (syn_c1c)
  have p0040 :=
    @g_reximi (.classEq (.cv m) (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n)))
      (.classEq (syn_cplc (.cv m) (syn_c1c))
        (syn_cplc (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n)) (syn_c1c)))
      n (syn_cnnc) p0039
  have p0041 :=
    @g_a1i
      (.imp (syn_wrex n (syn_cnnc)
          (.classEq (.cv m) (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n))))
        (syn_wrex n (syn_cnnc) (.classEq (syn_cplc (.cv m) (syn_c1c))
            (syn_cplc (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n)) (syn_c1c)))))
      (.classMem (.cv m) (syn_cnnc)) p0040
  have p0042 :=
    @g_addceq1 (.cv m) (syn_cplc (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n)) (syn_c1c))
      (syn_c1c)
  have p0043 :=
    @g_addcass (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n)) (syn_c1c) (syn_c1c)
  have p0044 := @g_n_1p1e2c
  have p0045 :=
    @g_addceq2i (syn_cplc (syn_c1c) (syn_c1c)) (syn_c2c)
      (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n)) p0044
  have p0046 :=
    @g_eqtri
      (syn_cplc (syn_cplc (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n)) (syn_c1c)) (syn_c1c))
      (syn_cplc (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n)) (syn_cplc (syn_c1c) (syn_c1c)))
      (syn_cplc (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n)) (syn_c2c)) p0043 p0045
  have p0047 :=
    @g_syl6eq
      (.classEq (.cv m) (syn_cplc (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n)) (syn_c1c)))
      (syn_cplc (.cv m) (syn_c1c))
      (syn_cplc (syn_cplc (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n)) (syn_c1c)) (syn_c1c))
      (syn_cplc (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n)) (syn_c2c)) p0042 p0046
  have p0048 :=
    @g_reximi
      (.classEq (.cv m) (syn_cplc (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n)) (syn_c1c)))
      (.classEq (syn_cplc (.cv m) (syn_c1c))
        (syn_cplc (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n)) (syn_c2c)))
      n (syn_cnnc) p0047
  have p0049 :=
    @g_a1i
      (.imp (syn_wrex n (syn_cnnc) (.classEq (.cv m)
            (syn_cplc (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n)) (syn_c1c))))
        (syn_wrex n (syn_cnnc) (.classEq (syn_cplc (.cv m) (syn_c1c))
            (syn_cplc (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n)) (syn_c2c)))))
      (.classMem (.cv m) (syn_cnnc)) p0048
  have p0050 := @g_peano2 (.cv n)
  have p0051 := @g_addc32 (syn_cplc (.cv n) (.cv n)) (.cv n) (syn_c2c)
  have p0053 :=
    @g_addceq2i (syn_cplc (syn_c1c) (syn_c1c)) (syn_c2c) (syn_cplc (.cv n) (.cv n)) p0044
  have p0054 := @g_addc4 (.cv n) (.cv n) (syn_c1c) (syn_c1c)
  have p0055 :=
    @g_eqtr3i (syn_cplc (syn_cplc (.cv n) (.cv n)) (syn_cplc (syn_c1c) (syn_c1c)))
      (syn_cplc (syn_cplc (.cv n) (.cv n)) (syn_c2c))
      (syn_cplc (syn_cplc (.cv n) (syn_c1c)) (syn_cplc (.cv n) (syn_c1c))) p0053 p0054
  have p0056 :=
    @g_addceq1i (syn_cplc (syn_cplc (.cv n) (.cv n)) (syn_c2c))
      (syn_cplc (syn_cplc (.cv n) (syn_c1c)) (syn_cplc (.cv n) (syn_c1c))) (.cv n) p0055
  have p0057 :=
    @g_eqtri (syn_cplc (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n)) (syn_c2c))
      (syn_cplc (syn_cplc (syn_cplc (.cv n) (.cv n)) (syn_c2c)) (.cv n))
      (syn_cplc (syn_cplc (syn_cplc (.cv n) (syn_c1c)) (syn_cplc (.cv n) (syn_c1c))) (.cv n))
      p0051 p0056
  have p0058 :=
    @g_addceq1i (syn_cplc (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n)) (syn_c2c))
      (syn_cplc (syn_cplc (syn_cplc (.cv n) (syn_c1c)) (syn_cplc (.cv n) (syn_c1c))) (.cv n))
      (syn_c1c) p0057
  have p0059 :=
    @g_addcass (syn_cplc (syn_cplc (.cv n) (syn_c1c)) (syn_cplc (.cv n) (syn_c1c)))
      (.cv n) (syn_c1c)
  have p0060 :=
    @g_eqtri
      (syn_cplc (syn_cplc (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n)) (syn_c2c)) (syn_c1c))
      (syn_cplc (syn_cplc (syn_cplc (syn_cplc (.cv n) (syn_c1c)) (syn_cplc (.cv n) (syn_c1c)))
          (.cv n)) (syn_c1c))
      (syn_cplc (syn_cplc (syn_cplc (.cv n) (syn_c1c)) (syn_cplc (.cv n) (syn_c1c)))
        (syn_cplc (.cv n) (syn_c1c)))
      p0058 p0059
  have p0061 :=
    @g_addceq12 (.cv a) (.cv a) (syn_cplc (.cv n) (syn_c1c)) (syn_cplc (.cv n) (syn_c1c))
  have p0062 :=
    @g_anidms (.classEq (.cv a) (syn_cplc (.cv n) (syn_c1c)))
      (.classEq (syn_cplc (.cv a) (.cv a))
        (syn_cplc (syn_cplc (.cv n) (syn_c1c)) (syn_cplc (.cv n) (syn_c1c))))
      p0061
  have p0063 := @g_id (.classEq (.cv a) (syn_cplc (.cv n) (syn_c1c)))
  have p0064 :=
    @g_addceq12d (.classEq (.cv a) (syn_cplc (.cv n) (syn_c1c)))
      (syn_cplc (.cv a) (.cv a))
      (syn_cplc (syn_cplc (.cv n) (syn_c1c)) (syn_cplc (.cv n) (syn_c1c))) (.cv a)
      (syn_cplc (.cv n) (syn_c1c)) p0062 p0063
  have p0065 :=
    @g_eqeq2d (.classEq (.cv a) (syn_cplc (.cv n) (syn_c1c)))
      (syn_cplc (syn_cplc (.cv a) (.cv a)) (.cv a))
      (syn_cplc (syn_cplc (syn_cplc (.cv n) (syn_c1c)) (syn_cplc (.cv n) (syn_c1c)))
        (syn_cplc (.cv n) (syn_c1c)))
      (syn_cplc (syn_cplc (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n)) (syn_c2c)) (syn_c1c))
      p0064
  have p0066 :=
    @g_rspcev
      (.classEq (syn_cplc (syn_cplc (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n)) (syn_c2c))
          (syn_c1c)) (syn_cplc (syn_cplc (.cv a) (.cv a)) (.cv a)))
      (.classEq (syn_cplc (syn_cplc (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n)) (syn_c2c))
          (syn_c1c))
        (syn_cplc (syn_cplc (syn_cplc (.cv n) (syn_c1c)) (syn_cplc (.cv n) (syn_c1c)))
          (syn_cplc (.cv n) (syn_c1c))))
      a (syn_cplc (.cv n) (syn_c1c)) (syn_cnnc) dv_cache_0009 dv_cache_0010 dv_cache_0011
      p0065
  have p0067 :=
    @g_sylancl (.classMem (.cv n) (syn_cnnc))
      (.classMem (syn_cplc (.cv n) (syn_c1c)) (syn_cnnc))
      (.classEq (syn_cplc (syn_cplc (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n)) (syn_c2c))
          (syn_c1c))
        (syn_cplc (syn_cplc (syn_cplc (.cv n) (syn_c1c)) (syn_cplc (.cv n) (syn_c1c)))
          (syn_cplc (.cv n) (syn_c1c))))
      (syn_wrex a (syn_cnnc) (.classEq
          (syn_cplc (syn_cplc (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n)) (syn_c2c))
            (syn_c1c)) (syn_cplc (syn_cplc (.cv a) (.cv a)) (.cv a))))
      p0050 p0060 p0066
  have p0068 :=
    @g_addceq1 (.cv m) (syn_cplc (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n)) (syn_c2c))
      (syn_c1c)
  have p0069 :=
    @g_eqeq1d
      (.classEq (.cv m) (syn_cplc (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n)) (syn_c2c)))
      (syn_cplc (.cv m) (syn_c1c))
      (syn_cplc (syn_cplc (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n)) (syn_c2c)) (syn_c1c))
      (syn_cplc (syn_cplc (.cv a) (.cv a)) (.cv a)) p0068
  have p0070 :=
    @g_rexbidv
      (.classEq (.cv m) (syn_cplc (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n)) (syn_c2c)))
      (.classEq (syn_cplc (.cv m) (syn_c1c)) (syn_cplc (syn_cplc (.cv a) (.cv a)) (.cv a)))
      (.classEq (syn_cplc (syn_cplc (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n)) (syn_c2c))
          (syn_c1c)) (syn_cplc (syn_cplc (.cv a) (.cv a)) (.cv a)))
      a (syn_cnnc) dv_cache_0012 p0069
  have p0071 :=
    @g_syl5ibrcom (.classMem (.cv n) (syn_cnnc))
      (syn_wrex a (syn_cnnc) (.classEq (syn_cplc (.cv m) (syn_c1c))
          (syn_cplc (syn_cplc (.cv a) (.cv a)) (.cv a))))
      (.classEq (.cv m) (syn_cplc (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n)) (syn_c2c)))
      (syn_wrex a (syn_cnnc) (.classEq
          (syn_cplc (syn_cplc (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n)) (syn_c2c))
            (syn_c1c)) (syn_cplc (syn_cplc (.cv a) (.cv a)) (.cv a))))
      p0067 p0070
  have p0072 :=
    @g_rexlimiv
      (.classEq (.cv m) (syn_cplc (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n)) (syn_c2c)))
      (syn_wrex a (syn_cnnc) (.classEq (syn_cplc (.cv m) (syn_c1c))
          (syn_cplc (syn_cplc (.cv a) (.cv a)) (.cv a))))
      n (syn_cnnc) dv_cache_0013 p0071
  have p0073 := @g_addceq12 (.cv a) (.cv a) (.cv n) (.cv n)
  have p0074_e00_recanon :
    Nominal.NPrf
      (.imp (syn_wa (.objEq a n) (.objEq a n))
        (.classEq (syn_cplc (.cv a) (.cv a)) (syn_cplc (.cv n) (.cv n)))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wa syn_cplc syn_wrex syn_wex
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
    @g_anidms (.objEq a n)
      (.classEq (syn_cplc (.cv a) (.cv a)) (syn_cplc (.cv n) (.cv n))) p0074_e00_recanon
  have p0075 := @g_id (.objEq a n)
  have p0076_e01_recanon : Nominal.NPrf (.imp (.objEq a n) (.classEq (.cv a) (.cv n))) :=
    Nominal.RecanonTransportDev.transport
      (by
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · exact Nominal.RecanonTransportDev.TRecanonWff.same _
        · exact Nominal.RecanonTransportDev.TRecanonWff.objEq_classEq _ _)
      p0075
  have p0076 :=
    @g_addceq12d (.objEq a n) (syn_cplc (.cv a) (.cv a)) (syn_cplc (.cv n) (.cv n))
      (.cv a) (.cv n) p0074 p0076_e01_recanon
  have p0077 :=
    @g_eqeq2d (.objEq a n) (syn_cplc (syn_cplc (.cv a) (.cv a)) (.cv a))
      (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n)) (syn_cplc (.cv m) (syn_c1c)) p0076
  have p0078 :=
    @g_cbvrexv
      (.classEq (syn_cplc (.cv m) (syn_c1c)) (syn_cplc (syn_cplc (.cv a) (.cv a)) (.cv a)))
      (.classEq (syn_cplc (.cv m) (syn_c1c)) (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n)))
      a n (syn_cnnc) dv_cache_0010 dv_cache_0007 dv_cache_0014 dv_cache_0015 p0077
  have p0079 :=
    @g_sylib
      (syn_wrex n (syn_cnnc) (.classEq (.cv m)
          (syn_cplc (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n)) (syn_c2c))))
      (syn_wrex a (syn_cnnc) (.classEq (syn_cplc (.cv m) (syn_c1c))
          (syn_cplc (syn_cplc (.cv a) (.cv a)) (.cv a))))
      (syn_wrex n (syn_cnnc) (.classEq (syn_cplc (.cv m) (syn_c1c))
          (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n))))
      p0072 p0078
  have p0080 :=
    @g_a1i
      (.imp (syn_wrex n (syn_cnnc) (.classEq (.cv m)
            (syn_cplc (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n)) (syn_c2c))))
        (syn_wrex n (syn_cnnc) (.classEq (syn_cplc (.cv m) (syn_c1c))
            (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n)))))
      (.classMem (.cv m) (syn_cnnc)) p0079
  have p0081 :=
    @g_n_3orim123d (.classMem (.cv m) (syn_cnnc))
      (syn_wrex n (syn_cnnc) (.classEq (.cv m) (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n))))
      (syn_wrex n (syn_cnnc) (.classEq (syn_cplc (.cv m) (syn_c1c))
          (syn_cplc (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n)) (syn_c1c))))
      (syn_wrex n (syn_cnnc) (.classEq (.cv m)
          (syn_cplc (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n)) (syn_c1c))))
      (syn_wrex n (syn_cnnc) (.classEq (syn_cplc (.cv m) (syn_c1c))
          (syn_cplc (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n)) (syn_c2c))))
      (syn_wrex n (syn_cnnc) (.classEq (.cv m)
          (syn_cplc (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n)) (syn_c2c))))
      (syn_wrex n (syn_cnnc) (.classEq (syn_cplc (.cv m) (syn_c1c))
          (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n))))
      p0041 p0049 p0080
  have p0082 :=
    (Nominal.biimpRefl (syn_w3o (.classEq (.cv m) (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n)))
        (.classEq (.cv m) (syn_cplc (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n)) (syn_c1c)))
        (.classEq (.cv m) (syn_cplc (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n)) (syn_c2c)))))
  have p0083 :=
    @g_rexbii
      (syn_w3o (.classEq (.cv m) (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n)))
        (.classEq (.cv m) (syn_cplc (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n)) (syn_c1c)))
        (.classEq (.cv m) (syn_cplc (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n)) (syn_c2c))))
      (syn_wo (syn_wo (.classEq (.cv m) (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n)))
          (.classEq (.cv m) (syn_cplc (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n)) (syn_c1c))))
        (.classEq (.cv m) (syn_cplc (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n)) (syn_c2c))))
      n (syn_cnnc) p0082
  have p0084 :=
    @g_r19_43 (.classEq (.cv m) (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n)))
      (.classEq (.cv m) (syn_cplc (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n)) (syn_c1c)))
      n (syn_cnnc)
  have p0085 :=
    @g_orbi1i
      (syn_wrex n (syn_cnnc)
        (syn_wo (.classEq (.cv m) (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n)))
          (.classEq (.cv m)
            (syn_cplc (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n)) (syn_c1c)))))
      (syn_wo (syn_wrex n (syn_cnnc)
          (.classEq (.cv m) (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n))))
        (syn_wrex n (syn_cnnc) (.classEq (.cv m)
            (syn_cplc (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n)) (syn_c1c)))))
      (syn_wrex n (syn_cnnc) (.classEq (.cv m)
          (syn_cplc (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n)) (syn_c2c))))
      p0084
  have p0086 :=
    @g_r19_43
      (syn_wo (.classEq (.cv m) (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n))) (.classEq (.cv m)
          (syn_cplc (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n)) (syn_c1c))))
      (.classEq (.cv m) (syn_cplc (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n)) (syn_c2c)))
      n (syn_cnnc)
  have p0087 :=
    (Nominal.biimpRefl (syn_w3o (syn_wrex n (syn_cnnc)
          (.classEq (.cv m) (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n))))
        (syn_wrex n (syn_cnnc) (.classEq (.cv m)
            (syn_cplc (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n)) (syn_c1c))))
        (syn_wrex n (syn_cnnc) (.classEq (.cv m)
            (syn_cplc (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n)) (syn_c2c))))))
  have p0088 :=
    @g_n_3bitr4i
      (syn_wo (syn_wrex n (syn_cnnc)
          (syn_wo (.classEq (.cv m) (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n)))
            (.classEq (.cv m)
              (syn_cplc (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n)) (syn_c1c)))))
        (syn_wrex n (syn_cnnc) (.classEq (.cv m)
            (syn_cplc (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n)) (syn_c2c)))))
      (syn_wo (syn_wo (syn_wrex n (syn_cnnc)
            (.classEq (.cv m) (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n))))
          (syn_wrex n (syn_cnnc) (.classEq (.cv m)
              (syn_cplc (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n)) (syn_c1c)))))
        (syn_wrex n (syn_cnnc) (.classEq (.cv m)
            (syn_cplc (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n)) (syn_c2c)))))
      (syn_wrex n (syn_cnnc) (syn_wo
          (syn_wo (.classEq (.cv m) (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n)))
            (.classEq (.cv m)
              (syn_cplc (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n)) (syn_c1c))))
          (.classEq (.cv m)
            (syn_cplc (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n)) (syn_c2c)))))
      (syn_w3o (syn_wrex n (syn_cnnc)
          (.classEq (.cv m) (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n))))
        (syn_wrex n (syn_cnnc) (.classEq (.cv m)
            (syn_cplc (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n)) (syn_c1c))))
        (syn_wrex n (syn_cnnc) (.classEq (.cv m)
            (syn_cplc (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n)) (syn_c2c)))))
      p0085 p0086 p0087
  have p0089 :=
    @g_bitri
      (syn_wrex n (syn_cnnc)
        (syn_w3o (.classEq (.cv m) (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n)))
          (.classEq (.cv m) (syn_cplc (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n)) (syn_c1c)))
          (.classEq (.cv m)
            (syn_cplc (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n)) (syn_c2c)))))
      (syn_wrex n (syn_cnnc) (syn_wo
          (syn_wo (.classEq (.cv m) (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n)))
            (.classEq (.cv m)
              (syn_cplc (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n)) (syn_c1c))))
          (.classEq (.cv m)
            (syn_cplc (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n)) (syn_c2c)))))
      (syn_w3o (syn_wrex n (syn_cnnc)
          (.classEq (.cv m) (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n))))
        (syn_wrex n (syn_cnnc) (.classEq (.cv m)
            (syn_cplc (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n)) (syn_c1c))))
        (syn_wrex n (syn_cnnc) (.classEq (.cv m)
            (syn_cplc (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n)) (syn_c2c)))))
      p0083 p0088
  have p0090 :=
    (Nominal.biimpRefl (syn_w3o (.classEq (syn_cplc (.cv m) (syn_c1c))
          (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n))) (.classEq (syn_cplc (.cv m) (syn_c1c))
          (syn_cplc (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n)) (syn_c1c)))
        (.classEq (syn_cplc (.cv m) (syn_c1c))
          (syn_cplc (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n)) (syn_c2c)))))
  have p0091 :=
    @g_rexbii
      (syn_w3o (.classEq (syn_cplc (.cv m) (syn_c1c))
          (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n))) (.classEq (syn_cplc (.cv m) (syn_c1c))
          (syn_cplc (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n)) (syn_c1c)))
        (.classEq (syn_cplc (.cv m) (syn_c1c))
          (syn_cplc (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n)) (syn_c2c))))
      (syn_wo (syn_wo (.classEq (syn_cplc (.cv m) (syn_c1c))
            (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n)))
          (.classEq (syn_cplc (.cv m) (syn_c1c))
            (syn_cplc (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n)) (syn_c1c))))
        (.classEq (syn_cplc (.cv m) (syn_c1c))
          (syn_cplc (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n)) (syn_c2c))))
      n (syn_cnnc) p0090
  have p0092 :=
    @g_r19_43
      (syn_wo (.classEq (syn_cplc (.cv m) (syn_c1c))
          (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n))) (.classEq (syn_cplc (.cv m) (syn_c1c))
          (syn_cplc (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n)) (syn_c1c))))
      (.classEq (syn_cplc (.cv m) (syn_c1c))
        (syn_cplc (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n)) (syn_c2c)))
      n (syn_cnnc)
  have p0093 :=
    @g_r19_43
      (.classEq (syn_cplc (.cv m) (syn_c1c)) (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n)))
      (.classEq (syn_cplc (.cv m) (syn_c1c))
        (syn_cplc (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n)) (syn_c1c)))
      n (syn_cnnc)
  have p0094 :=
    @g_orbi1i
      (syn_wrex n (syn_cnnc) (syn_wo (.classEq (syn_cplc (.cv m) (syn_c1c))
            (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n)))
          (.classEq (syn_cplc (.cv m) (syn_c1c))
            (syn_cplc (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n)) (syn_c1c)))))
      (syn_wo (syn_wrex n (syn_cnnc) (.classEq (syn_cplc (.cv m) (syn_c1c))
            (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n)))) (syn_wrex n (syn_cnnc)
          (.classEq (syn_cplc (.cv m) (syn_c1c))
            (syn_cplc (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n)) (syn_c1c)))))
      (syn_wrex n (syn_cnnc) (.classEq (syn_cplc (.cv m) (syn_c1c))
          (syn_cplc (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n)) (syn_c2c))))
      p0093
  have p0095 :=
    (Nominal.biimpRefl (syn_w3o (syn_wrex n (syn_cnnc) (.classEq (syn_cplc (.cv m) (syn_c1c))
            (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n)))) (syn_wrex n (syn_cnnc)
          (.classEq (syn_cplc (.cv m) (syn_c1c))
            (syn_cplc (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n)) (syn_c1c))))
        (syn_wrex n (syn_cnnc) (.classEq (syn_cplc (.cv m) (syn_c1c))
            (syn_cplc (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n)) (syn_c2c))))))
  have p0096 :=
    @g_n_3orrot
      (syn_wrex n (syn_cnnc) (.classEq (syn_cplc (.cv m) (syn_c1c))
          (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n))))
      (syn_wrex n (syn_cnnc) (.classEq (syn_cplc (.cv m) (syn_c1c))
          (syn_cplc (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n)) (syn_c1c))))
      (syn_wrex n (syn_cnnc) (.classEq (syn_cplc (.cv m) (syn_c1c))
          (syn_cplc (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n)) (syn_c2c))))
  have p0097 :=
    @g_n_3bitr2i
      (syn_wo (syn_wrex n (syn_cnnc) (syn_wo (.classEq (syn_cplc (.cv m) (syn_c1c))
              (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n)))
            (.classEq (syn_cplc (.cv m) (syn_c1c))
              (syn_cplc (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n)) (syn_c1c)))))
        (syn_wrex n (syn_cnnc) (.classEq (syn_cplc (.cv m) (syn_c1c))
            (syn_cplc (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n)) (syn_c2c)))))
      (syn_wo (syn_wo (syn_wrex n (syn_cnnc) (.classEq (syn_cplc (.cv m) (syn_c1c))
              (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n)))) (syn_wrex n (syn_cnnc)
            (.classEq (syn_cplc (.cv m) (syn_c1c))
              (syn_cplc (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n)) (syn_c1c)))))
        (syn_wrex n (syn_cnnc) (.classEq (syn_cplc (.cv m) (syn_c1c))
            (syn_cplc (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n)) (syn_c2c)))))
      (syn_w3o (syn_wrex n (syn_cnnc) (.classEq (syn_cplc (.cv m) (syn_c1c))
            (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n)))) (syn_wrex n (syn_cnnc)
          (.classEq (syn_cplc (.cv m) (syn_c1c))
            (syn_cplc (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n)) (syn_c1c))))
        (syn_wrex n (syn_cnnc) (.classEq (syn_cplc (.cv m) (syn_c1c))
            (syn_cplc (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n)) (syn_c2c)))))
      (syn_w3o (syn_wrex n (syn_cnnc) (.classEq (syn_cplc (.cv m) (syn_c1c))
            (syn_cplc (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n)) (syn_c1c))))
        (syn_wrex n (syn_cnnc) (.classEq (syn_cplc (.cv m) (syn_c1c))
            (syn_cplc (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n)) (syn_c2c))))
        (syn_wrex n (syn_cnnc) (.classEq (syn_cplc (.cv m) (syn_c1c))
            (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n)))))
      p0094 p0095 p0096
  have p0098 :=
    @g_bitri
      (syn_wrex n (syn_cnnc) (syn_wo (syn_wo (.classEq (syn_cplc (.cv m) (syn_c1c))
              (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n)))
            (.classEq (syn_cplc (.cv m) (syn_c1c))
              (syn_cplc (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n)) (syn_c1c))))
          (.classEq (syn_cplc (.cv m) (syn_c1c))
            (syn_cplc (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n)) (syn_c2c)))))
      (syn_wo (syn_wrex n (syn_cnnc) (syn_wo (.classEq (syn_cplc (.cv m) (syn_c1c))
              (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n)))
            (.classEq (syn_cplc (.cv m) (syn_c1c))
              (syn_cplc (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n)) (syn_c1c)))))
        (syn_wrex n (syn_cnnc) (.classEq (syn_cplc (.cv m) (syn_c1c))
            (syn_cplc (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n)) (syn_c2c)))))
      (syn_w3o (syn_wrex n (syn_cnnc) (.classEq (syn_cplc (.cv m) (syn_c1c))
            (syn_cplc (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n)) (syn_c1c))))
        (syn_wrex n (syn_cnnc) (.classEq (syn_cplc (.cv m) (syn_c1c))
            (syn_cplc (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n)) (syn_c2c))))
        (syn_wrex n (syn_cnnc) (.classEq (syn_cplc (.cv m) (syn_c1c))
            (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n)))))
      p0092 p0097
  have p0099 :=
    @g_bitri
      (syn_wrex n (syn_cnnc) (syn_w3o (.classEq (syn_cplc (.cv m) (syn_c1c))
            (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n)))
          (.classEq (syn_cplc (.cv m) (syn_c1c))
            (syn_cplc (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n)) (syn_c1c)))
          (.classEq (syn_cplc (.cv m) (syn_c1c))
            (syn_cplc (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n)) (syn_c2c)))))
      (syn_wrex n (syn_cnnc) (syn_wo (syn_wo (.classEq (syn_cplc (.cv m) (syn_c1c))
              (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n)))
            (.classEq (syn_cplc (.cv m) (syn_c1c))
              (syn_cplc (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n)) (syn_c1c))))
          (.classEq (syn_cplc (.cv m) (syn_c1c))
            (syn_cplc (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n)) (syn_c2c)))))
      (syn_w3o (syn_wrex n (syn_cnnc) (.classEq (syn_cplc (.cv m) (syn_c1c))
            (syn_cplc (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n)) (syn_c1c))))
        (syn_wrex n (syn_cnnc) (.classEq (syn_cplc (.cv m) (syn_c1c))
            (syn_cplc (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n)) (syn_c2c))))
        (syn_wrex n (syn_cnnc) (.classEq (syn_cplc (.cv m) (syn_c1c))
            (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n)))))
      p0091 p0098
  have p0100 :=
    @g_n_3imtr4g (.classMem (.cv m) (syn_cnnc))
      (syn_w3o (syn_wrex n (syn_cnnc)
          (.classEq (.cv m) (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n))))
        (syn_wrex n (syn_cnnc) (.classEq (.cv m)
            (syn_cplc (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n)) (syn_c1c))))
        (syn_wrex n (syn_cnnc) (.classEq (.cv m)
            (syn_cplc (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n)) (syn_c2c)))))
      (syn_w3o (syn_wrex n (syn_cnnc) (.classEq (syn_cplc (.cv m) (syn_c1c))
            (syn_cplc (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n)) (syn_c1c))))
        (syn_wrex n (syn_cnnc) (.classEq (syn_cplc (.cv m) (syn_c1c))
            (syn_cplc (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n)) (syn_c2c))))
        (syn_wrex n (syn_cnnc) (.classEq (syn_cplc (.cv m) (syn_c1c))
            (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n)))))
      (syn_wrex n (syn_cnnc)
        (syn_w3o (.classEq (.cv m) (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n)))
          (.classEq (.cv m) (syn_cplc (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n)) (syn_c1c)))
          (.classEq (.cv m)
            (syn_cplc (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n)) (syn_c2c)))))
      (syn_wrex n (syn_cnnc) (syn_w3o (.classEq (syn_cplc (.cv m) (syn_c1c))
            (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n)))
          (.classEq (syn_cplc (.cv m) (syn_c1c))
            (syn_cplc (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n)) (syn_c1c)))
          (.classEq (syn_cplc (.cv m) (syn_c1c))
            (syn_cplc (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n)) (syn_c2c)))))
      p0081 p0089 p0099
  have p0101 :=
    @g_finds
      (syn_wrex n (syn_cnnc)
        (syn_w3o (.classEq (.cv a) (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n)))
          (.classEq (.cv a) (syn_cplc (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n)) (syn_c1c)))
          (.classEq (.cv a)
            (syn_cplc (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n)) (syn_c2c)))))
      (syn_wrex n (syn_cnnc)
        (syn_w3o (.classEq (syn_c0c) (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n)))
          (.classEq (syn_c0c)
            (syn_cplc (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n)) (syn_c1c)))
          (.classEq (syn_c0c)
            (syn_cplc (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n)) (syn_c2c)))))
      (syn_wrex n (syn_cnnc)
        (syn_w3o (.classEq (.cv m) (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n)))
          (.classEq (.cv m) (syn_cplc (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n)) (syn_c1c)))
          (.classEq (.cv m)
            (syn_cplc (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n)) (syn_c2c)))))
      (syn_wrex n (syn_cnnc) (syn_w3o (.classEq (syn_cplc (.cv m) (syn_c1c))
            (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n)))
          (.classEq (syn_cplc (.cv m) (syn_c1c))
            (syn_cplc (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n)) (syn_c1c)))
          (.classEq (syn_cplc (.cv m) (syn_c1c))
            (syn_cplc (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n)) (syn_c2c)))))
      (syn_wrex n (syn_cnnc) (syn_w3o (.classEq A (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n)))
          (.classEq A (syn_cplc (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n)) (syn_c1c)))
          (.classEq A (syn_cplc (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n)) (syn_c2c)))))
      a m A dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020
      dv_cache_0021 dv_cache_0022 p0000 p0005 p0010 p0015 p0020 p0038 p0100
  exact p0101


end NFChoice.DirectNominalPrf.WPPReplay

end
