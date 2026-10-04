/-
Copyright (c) 2026 Elliot Glazer and NFNotWPP contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elliot Glazer and NFNotWPP contributors
-/

module

public import LeanPool.NFWeakPartition.Certificates.NominalWPPReplayChunk013Compact001Block004

/-! Nominal proof certificates grouped in dependency order. -/


public section

/-! Certificates from `NominalWPPReplayChunk013Compact001Part020`. -/


section

namespace NFChoice.DirectNominalPrf.WPPReplay

open scoped Fol
open NFChoice.Foundation
open NFChoice.SemanticCore
open NFChoice.ReplaySupport
open NFChoice.Compiler.CompactSourceSyntax

/-- Checked nominal proof certificate identified upstream as `g_antisymex`. -/
@[expose]
noncomputable def gAntisymex : Nominal.NPrf (.classMem (synCantisym) (synCvv)) :=
  by
  let proofSupport : Finset Var := (∅ : Finset Var)
  let x : Var := freshVar proofSupport 0
  let y : Var := freshVar proofSupport 1
  let r : Var := freshVar proofSupport 2
  let a : Var := freshVar proofSupport 3
  let p : Var := freshVar proofSupport 4
  have fresh_x_ne_y : x ≠ y :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have fresh_y_ne_x : y ≠ x := Ne.symm fresh_x_ne_y
  have fresh_x_ne_r : x ≠ r :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 2
    exact freshVar_injective proofSupport (i := 0) (j := 2) (by decide)
  have fresh_r_ne_x : r ≠ x := Ne.symm fresh_x_ne_r
  have fresh_x_ne_a : x ≠ a :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 3
    exact freshVar_injective proofSupport (i := 0) (j := 3) (by decide)
  have fresh_a_ne_x : a ≠ x := Ne.symm fresh_x_ne_a
  have fresh_x_ne_p : x ≠ p :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 4
    exact freshVar_injective proofSupport (i := 0) (j := 4) (by decide)
  have fresh_p_ne_x : p ≠ x := Ne.symm fresh_x_ne_p
  have fresh_y_ne_r : y ≠ r :=
    by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 2
    exact freshVar_injective proofSupport (i := 1) (j := 2) (by decide)
  have fresh_r_ne_y : r ≠ y := Ne.symm fresh_y_ne_r
  have fresh_y_ne_a : y ≠ a :=
    by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 3
    exact freshVar_injective proofSupport (i := 1) (j := 3) (by decide)
  have fresh_a_ne_y : a ≠ y := Ne.symm fresh_y_ne_a
  have fresh_y_ne_p : y ≠ p :=
    by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 4
    exact freshVar_injective proofSupport (i := 1) (j := 4) (by decide)
  have fresh_p_ne_y : p ≠ y := Ne.symm fresh_y_ne_p
  have fresh_r_ne_a : r ≠ a :=
    by
    change freshVar proofSupport 2 ≠ freshVar proofSupport 3
    exact freshVar_injective proofSupport (i := 2) (j := 3) (by decide)
  have fresh_a_ne_r : a ≠ r := Ne.symm fresh_r_ne_a
  have fresh_r_ne_p : r ≠ p :=
    by
    change freshVar proofSupport 2 ≠ freshVar proofSupport 4
    exact freshVar_injective proofSupport (i := 2) (j := 4) (by decide)
  have fresh_p_ne_r : p ≠ r := Ne.symm fresh_r_ne_p
  have dv_cache_0001 : a ≠ r := by exact (show a ≠ r from (by exact fresh_a_ne_r))
  have dv_cache_0002 : a ≠ x := by
    clear dv_cache_0001
    exact (show a ≠ x from (by exact fresh_a_ne_x))
  have dv_cache_0003 : a ≠ y :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact (show a ≠ y from (by exact fresh_a_ne_y))
  have dv_cache_0004 : r ≠ x :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact (show r ≠ x from (by exact fresh_r_ne_x))
  have dv_cache_0005 : r ≠ y :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact (show r ≠ y from (by exact fresh_r_ne_y))
  have dv_cache_0006 : x ≠ y :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact (show x ≠ y from (by exact fresh_x_ne_y))
  have dv_cache_0007 :
    p ∉ ((synCop (synCsn (.cv y)) (synCop (synCsn (.cv x)) (.cv r)))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006
    exact
      (by
        have compact_fv_not_mem_empty : p ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cop,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, fresh_p_ne_y, fresh_p_ne_x, fresh_p_ne_r, or_false,
          not_false_eq_true])
  have dv_cache_0008 :
    p ∉
      ((synCin (synCins4 (synCsi3 (synCtxp (synC2nd) (synC1st))))
          (synCins2 (synCins2 (synCsset))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007
    exact
      (by
        have compact_fv_not_mem_empty : p ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins4,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csi3,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ctxp,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c2nd,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1st,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins2,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csset, Finset.mem_union,
          compact_fv_not_mem_empty, or_false, not_false_eq_true])
  have dv_cache_0009 : p ∉ ((synCop (.cv x) (.cv y))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008
    exact
      (by
        have compact_fv_not_mem_empty : p ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cop,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, fresh_p_ne_x, fresh_p_ne_y, or_false, not_false_eq_true])
  have dv_cache_0010 : p ∉ ((Class.cv r)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009
    exact
      (by
        have compact_fv_not_mem_empty : p ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_p_ne_r, not_false_eq_true])
  have dv_cache_0011 :
    p ∉
      ((synCin (synCins4 (synCsi3 (synCid))) (synCins2 (synCins2 (synCsset))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010
    exact
      (by
        have compact_fv_not_mem_empty : p ∉ (∅ : Finset Var) :=
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
  have dv_cache_0012 : p ∉ ((synCop (.cv y) (.cv x))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
    exact
      (by
        have compact_fv_not_mem_empty : p ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cop,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, fresh_p_ne_y, fresh_p_ne_x, or_false, not_false_eq_true])
  have dv_cache_0013 : y ∉ ((synCop (synCsn (.cv x)) (synCop (.cv r) (.cv a)))).fv :=
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
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cop,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, fresh_y_ne_x, fresh_y_ne_r, fresh_y_ne_a, or_false,
          not_false_eq_true])
  have dv_cache_0014 :
    y ∉
      ((synCin (synCins2 (synCins2 (synCsset))) (synCins4 (synCdif (synCin (synCima
                  (synCin (synCins4 (synCsi3 (synCtxp (synC2nd) (synC1st))))
                    (synCins2 (synCins2 (synCsset)))) (synC1c)) (synCima
                  (synCin (synCins4 (synCsi3 (synCid))) (synCins2 (synCins2 (synCsset))))
                  (synC1c))) (synCins3 (synCid)))))).fv :=
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
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins2,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csset,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins4,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdif,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cima,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csi3,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ctxp,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c2nd,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1st,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cid,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins3, Finset.mem_union,
          compact_fv_not_mem_empty, or_false, not_false_eq_true])
  have dv_cache_0015 : x ∉ ((synCop (.cv r) (.cv a))).fv :=
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
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cop,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, fresh_x_ne_r, fresh_x_ne_a, or_false, not_false_eq_true])
  have dv_cache_0016 :
    x ∉
      ((synCin (synCins2 (synCsset)) (synCima (synCin (synCins2 (synCins2 (synCsset)))
              (synCins4 (synCdif (synCin (synCima
                      (synCin (synCins4 (synCsi3 (synCtxp (synC2nd) (synC1st))))
                        (synCins2 (synCins2 (synCsset)))) (synC1c)) (synCima
                      (synCin (synCins4 (synCsi3 (synCid)))
                        (synCins2 (synCins2 (synCsset)))) (synC1c)))
                  (synCins3 (synCid))))) (synC1c)))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins2,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csset,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cima,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins4,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdif,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csi3,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ctxp,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c2nd,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1st,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cid,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins3, Finset.mem_union,
          compact_fv_not_mem_empty, or_false, not_false_eq_true])
  have dv_cache_0017 :
    r ∉
      ((synCcompl (synCima (synCin (synCins2 (synCsset)) (synCima
                (synCin (synCins2 (synCins2 (synCsset))) (synCins4 (synCdif (synCin
                        (synCima
                          (synCin (synCins4 (synCsi3 (synCtxp (synC2nd) (synC1st))))
                            (synCins2 (synCins2 (synCsset)))) (synC1c)) (synCima
                          (synCin (synCins4 (synCsi3 (synCid)))
                            (synCins2 (synCins2 (synCsset)))) (synC1c)))
                      (synCins3 (synCid))))) (synC1c))) (synC1c)))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016
    exact
      (by
        have compact_fv_not_mem_empty : r ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccompl,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cima,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins2,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csset,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins4,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdif,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csi3,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ctxp,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c2nd,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1st,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cid,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins3, Finset.mem_union,
          compact_fv_not_mem_empty, or_false, not_false_eq_true])
  have dv_cache_0018 :
    a ∉
      ((synCcompl (synCima (synCin (synCins2 (synCsset)) (synCima
                (synCin (synCins2 (synCins2 (synCsset))) (synCins4 (synCdif (synCin
                        (synCima
                          (synCin (synCins4 (synCsi3 (synCtxp (synC2nd) (synC1st))))
                            (synCins2 (synCins2 (synCsset)))) (synC1c)) (synCima
                          (synCin (synCins4 (synCsi3 (synCid)))
                            (synCins2 (synCins2 (synCsset)))) (synC1c)))
                      (synCins3 (synCid))))) (synC1c))) (synC1c)))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
    exact
      (by
        have compact_fv_not_mem_empty : a ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccompl,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cima,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins2,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csset,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins4,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdif,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csi3,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ctxp,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c2nd,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1st,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cid,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins3, Finset.mem_union,
          compact_fv_not_mem_empty, or_false, not_false_eq_true])
  have dv_cache_0019 : r ≠ a :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018
    exact (show r ≠ a from (by exact fresh_r_ne_a))
  have p0000 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominalDfAntisym x y r a
      dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006
  have p0001 := @gVex r
  have p0002 := @gVex a
  have p0003 := @gOpex (.cv r) (.cv a) p0001 p0002
  have p0004 :=
    @gElcompl (synCop (.cv r) (.cv a))
      (synCima (synCin (synCins2 (synCsset)) (synCima
            (synCin (synCins2 (synCins2 (synCsset))) (synCins4 (synCdif (synCin (synCima
                      (synCin (synCins4 (synCsi3 (synCtxp (synC2nd) (synC1st))))
                        (synCins2 (synCins2 (synCsset)))) (synC1c)) (synCima
                      (synCin (synCins4 (synCsi3 (synCid)))
                        (synCins2 (synCins2 (synCsset)))) (synC1c)))
                  (synCins3 (synCid))))) (synC1c))) (synC1c))
      p0003
  have p0005 :=
    @gElin (synCop (synCsn (.cv x)) (synCop (.cv r) (.cv a))) (synCins2 (synCsset))
      (synCima (synCin (synCins2 (synCins2 (synCsset))) (synCins4 (synCdif (synCin
                (synCima (synCin (synCins4 (synCsi3 (synCtxp (synC2nd) (synC1st))))
                    (synCins2 (synCins2 (synCsset)))) (synC1c)) (synCima
                  (synCin (synCins4 (synCsi3 (synCid))) (synCins2 (synCins2 (synCsset))))
                  (synC1c))) (synCins3 (synCid))))) (synC1c))
  have p0006 := @gOtelins2 (synCsn (.cv x)) (.cv r) (.cv a) (synCsset) p0001
  have p0007 := @gVex x
  have p0008 := @gOpelssetsn (.cv x) (.cv a) p0007 p0002
  have p0009_e01_recanon :
    Nominal.NPrf
      (synWb (.classMem (synCop (synCsn (.cv x)) (.cv a)) (synCsset)) (.objMem x a)) :=
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
      p0008
  have p0009 :=
    @gBitri
      (.classMem (synCop (synCsn (.cv x)) (synCop (.cv r) (.cv a))) (synCins2 (synCsset)))
      (.classMem (synCop (synCsn (.cv x)) (.cv a)) (synCsset)) (.objMem x a) p0006
      p0009_e01_recanon
  have p0010 :=
    @gElin
      (synCop (synCsn (.cv y)) (synCop (synCsn (.cv x)) (synCop (.cv r) (.cv a))))
      (synCins2 (synCins2 (synCsset)))
      (synCins4 (synCdif (synCin (synCima
              (synCin (synCins4 (synCsi3 (synCtxp (synC2nd) (synC1st))))
                (synCins2 (synCins2 (synCsset)))) (synC1c)) (synCima
              (synCin (synCins4 (synCsi3 (synCid))) (synCins2 (synCins2 (synCsset))))
              (synC1c))) (synCins3 (synCid))))
  have p0011 := @gSnex (.cv x)
  have p0012 :=
    @gOtelins2 (synCsn (.cv y)) (synCsn (.cv x)) (synCop (.cv r) (.cv a))
      (synCins2 (synCsset)) p0011
  have p0013 := @gOtelins2 (synCsn (.cv y)) (.cv r) (.cv a) (synCsset) p0001
  have p0014 := @gVex y
  have p0015 := @gOpelssetsn (.cv y) (.cv a) p0014 p0002
  have p0016_e02_recanon :
    Nominal.NPrf
      (synWb (.classMem (synCop (synCsn (.cv y)) (.cv a)) (synCsset)) (.objMem y a)) :=
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
      p0015
  have p0016 :=
    @gN3bitri
      (.classMem
        (synCop (synCsn (.cv y)) (synCop (synCsn (.cv x)) (synCop (.cv r) (.cv a))))
        (synCins2 (synCins2 (synCsset))))
      (.classMem (synCop (synCsn (.cv y)) (synCop (.cv r) (.cv a))) (synCins2 (synCsset)))
      (.classMem (synCop (synCsn (.cv y)) (.cv a)) (synCsset)) (.objMem y a) p0012
      p0013 p0016_e02_recanon
  have p0017 :=
    @gOqelins4 (synCsn (.cv y)) (synCsn (.cv x)) (.cv r) (.cv a)
      (synCdif (synCin (synCima
            (synCin (synCins4 (synCsi3 (synCtxp (synC2nd) (synC1st))))
              (synCins2 (synCins2 (synCsset)))) (synC1c)) (synCima
            (synCin (synCins4 (synCsi3 (synCid))) (synCins2 (synCins2 (synCsset))))
            (synC1c))) (synCins3 (synCid)))
      p0002
  have p0018 :=
    @gEldif (synCop (synCsn (.cv y)) (synCop (synCsn (.cv x)) (.cv r)))
      (synCin (synCima (synCin (synCins4 (synCsi3 (synCtxp (synC2nd) (synC1st))))
            (synCins2 (synCins2 (synCsset)))) (synC1c)) (synCima
          (synCin (synCins4 (synCsi3 (synCid))) (synCins2 (synCins2 (synCsset))))
          (synC1c)))
      (synCins3 (synCid))
  have p0019 :=
    @gElin (synCop (synCsn (.cv y)) (synCop (synCsn (.cv x)) (.cv r)))
      (synCima (synCin (synCins4 (synCsi3 (synCtxp (synC2nd) (synC1st))))
          (synCins2 (synCins2 (synCsset)))) (synC1c))
      (synCima (synCin (synCins4 (synCsi3 (synCid))) (synCins2 (synCins2 (synCsset))))
        (synC1c))
  have p0020 :=
    @gElin
      (synCop (synCsn (.cv p))
        (synCop (synCsn (.cv y)) (synCop (synCsn (.cv x)) (.cv r))))
      (synCins4 (synCsi3 (synCtxp (synC2nd) (synC1st))))
      (synCins2 (synCins2 (synCsset)))
  have p0021 :=
    @gOqelins4 (synCsn (.cv p)) (synCsn (.cv y)) (synCsn (.cv x)) (.cv r)
      (synCsi3 (synCtxp (synC2nd) (synC1st))) p0001
  have p0022 := @gVex p
  have p0023 :=
    @gOtsnelsi3 (.cv p) (.cv y) (.cv x) (synCtxp (synC2nd) (synC1st)) p0022 p0014
      p0007
  have p0024 := @gOteltxp (.cv p) (.cv y) (.cv x) (synC2nd) (synC1st)
  have p0025 :=
    @gAncom (.classMem (synCop (.cv p) (.cv y)) (synC2nd))
      (.classMem (synCop (.cv p) (.cv x)) (synC1st))
  have p0026 := (Nominal.biimpRefl (synWbr (.cv p) (synC1st) (.cv x)))
  have p0027 := (Nominal.biimpRefl (synWbr (.cv p) (synC2nd) (.cv y)))
  have p0028 :=
    @gAnbi12i (synWbr (.cv p) (synC1st) (.cv x))
      (.classMem (synCop (.cv p) (.cv x)) (synC1st))
      (synWbr (.cv p) (synC2nd) (.cv y))
      (.classMem (synCop (.cv p) (.cv y)) (synC2nd)) p0026 p0027
  have p0029 :=
    @gBitr4i
      (synWa (.classMem (synCop (.cv p) (.cv y)) (synC2nd))
        (.classMem (synCop (.cv p) (.cv x)) (synC1st)))
      (synWa (.classMem (synCop (.cv p) (.cv x)) (synC1st))
        (.classMem (synCop (.cv p) (.cv y)) (synC2nd)))
      (synWa (synWbr (.cv p) (synC1st) (.cv x)) (synWbr (.cv p) (synC2nd) (.cv y)))
      p0025 p0028
  have p0030 := @gOp1st2nd (.cv x) (.cv y) (.cv p) p0007 p0014
  have p0031 :=
    @gN3bitri
      (.classMem (synCop (.cv p) (synCop (.cv y) (.cv x))) (synCtxp (synC2nd) (synC1st)))
      (synWa (.classMem (synCop (.cv p) (.cv y)) (synC2nd))
        (.classMem (synCop (.cv p) (.cv x)) (synC1st)))
      (synWa (synWbr (.cv p) (synC1st) (.cv x)) (synWbr (.cv p) (synC2nd) (.cv y)))
      (.classEq (.cv p) (synCop (.cv x) (.cv y))) p0024 p0029 p0030
  have p0032 :=
    @gN3bitri
      (.classMem (synCop (synCsn (.cv p))
          (synCop (synCsn (.cv y)) (synCop (synCsn (.cv x)) (.cv r))))
        (synCins4 (synCsi3 (synCtxp (synC2nd) (synC1st)))))
      (.classMem (synCop (synCsn (.cv p)) (synCop (synCsn (.cv y)) (synCsn (.cv x))))
        (synCsi3 (synCtxp (synC2nd) (synC1st))))
      (.classMem (synCop (.cv p) (synCop (.cv y) (.cv x))) (synCtxp (synC2nd) (synC1st)))
      (.classEq (.cv p) (synCop (.cv x) (.cv y))) p0021 p0023 p0031
  have p0033 := @gSnex (.cv y)
  have p0034 :=
    @gOtelins2 (synCsn (.cv p)) (synCsn (.cv y)) (synCop (synCsn (.cv x)) (.cv r))
      (synCins2 (synCsset)) p0033
  have p0035 := @gOtelins2 (synCsn (.cv p)) (synCsn (.cv x)) (.cv r) (synCsset) p0011
  have p0036 := @gOpelssetsn (.cv p) (.cv r) p0022 p0001
  have p0037_e02_recanon :
    Nominal.NPrf
      (synWb (.classMem (synCop (synCsn (.cv p)) (.cv r)) (synCsset)) (.objMem p r)) :=
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
      p0036
  have p0037 :=
    @gN3bitri
      (.classMem (synCop (synCsn (.cv p))
          (synCop (synCsn (.cv y)) (synCop (synCsn (.cv x)) (.cv r))))
        (synCins2 (synCins2 (synCsset))))
      (.classMem (synCop (synCsn (.cv p)) (synCop (synCsn (.cv x)) (.cv r)))
        (synCins2 (synCsset)))
      (.classMem (synCop (synCsn (.cv p)) (.cv r)) (synCsset)) (.objMem p r) p0034
      p0035 p0037_e02_recanon
  have p0038 :=
    @gAnbi12i
      (.classMem (synCop (synCsn (.cv p))
          (synCop (synCsn (.cv y)) (synCop (synCsn (.cv x)) (.cv r))))
        (synCins4 (synCsi3 (synCtxp (synC2nd) (synC1st)))))
      (.classEq (.cv p) (synCop (.cv x) (.cv y)))
      (.classMem (synCop (synCsn (.cv p))
          (synCop (synCsn (.cv y)) (synCop (synCsn (.cv x)) (.cv r))))
        (synCins2 (synCins2 (synCsset))))
      (.objMem p r) p0032 p0037
  have p0039 :=
    @gBitri
      (.classMem (synCop (synCsn (.cv p))
          (synCop (synCsn (.cv y)) (synCop (synCsn (.cv x)) (.cv r))))
        (synCin (synCins4 (synCsi3 (synCtxp (synC2nd) (synC1st))))
          (synCins2 (synCins2 (synCsset)))))
      (synWa (.classMem (synCop (synCsn (.cv p))
            (synCop (synCsn (.cv y)) (synCop (synCsn (.cv x)) (.cv r))))
          (synCins4 (synCsi3 (synCtxp (synC2nd) (synC1st))))) (.classMem
          (synCop (synCsn (.cv p))
            (synCop (synCsn (.cv y)) (synCop (synCsn (.cv x)) (.cv r))))
          (synCins2 (synCins2 (synCsset)))))
      (synWa (.classEq (.cv p) (synCop (.cv x) (.cv y))) (.objMem p r)) p0020 p0038
  have p0040 :=
    @gExbii
      (.classMem (synCop (synCsn (.cv p))
          (synCop (synCsn (.cv y)) (synCop (synCsn (.cv x)) (.cv r))))
        (synCin (synCins4 (synCsi3 (synCtxp (synC2nd) (synC1st))))
          (synCins2 (synCins2 (synCsset)))))
      (synWa (.classEq (.cv p) (synCop (.cv x) (.cv y))) (.objMem p r)) p p0039
  have p0041 :=
    @gElima1c p (synCop (synCsn (.cv y)) (synCop (synCsn (.cv x)) (.cv r)))
      (synCin (synCins4 (synCsi3 (synCtxp (synC2nd) (synC1st))))
        (synCins2 (synCins2 (synCsset))))
      dv_cache_0007 dv_cache_0008
  have p0042 := (Nominal.biimpRefl (synWbr (.cv x) (.cv r) (.cv y)))
  have p0043 :=
    (NFChoice.DirectNominalPrf.Nominal.DefinitionLeafHandlersCanonical001.dfClelOfDV p
      (synCop (.cv x) (.cv y)) (.cv r) dv_cache_0009 dv_cache_0010)
  have p0044_e01_recanon :
    Nominal.NPrf
      (synWb (.classMem (synCop (.cv x) (.cv y)) (.cv r)) (synWex p
          (synWa (.classEq (.cv p) (synCop (.cv x) (.cv y))) (.objMem p r)))) :=
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
      p0043
  have p0044 :=
    @gBitri (synWbr (.cv x) (.cv r) (.cv y))
      (.classMem (synCop (.cv x) (.cv y)) (.cv r))
      (synWex p (synWa (.classEq (.cv p) (synCop (.cv x) (.cv y))) (.objMem p r)))
      p0042 p0044_e01_recanon
  have p0045 :=
    @gN3bitr4i
      (synWex p (.classMem (synCop (synCsn (.cv p))
            (synCop (synCsn (.cv y)) (synCop (synCsn (.cv x)) (.cv r))))
          (synCin (synCins4 (synCsi3 (synCtxp (synC2nd) (synC1st))))
            (synCins2 (synCins2 (synCsset))))))
      (synWex p (synWa (.classEq (.cv p) (synCop (.cv x) (.cv y))) (.objMem p r)))
      (.classMem (synCop (synCsn (.cv y)) (synCop (synCsn (.cv x)) (.cv r))) (synCima
          (synCin (synCins4 (synCsi3 (synCtxp (synC2nd) (synC1st))))
            (synCins2 (synCins2 (synCsset)))) (synC1c)))
      (synWbr (.cv x) (.cv r) (.cv y)) p0040 p0041 p0044
  have p0046 :=
    @gElin
      (synCop (synCsn (.cv p))
        (synCop (synCsn (.cv y)) (synCop (synCsn (.cv x)) (.cv r))))
      (synCins4 (synCsi3 (synCid))) (synCins2 (synCins2 (synCsset)))
  have p0047 :=
    @gOqelins4 (synCsn (.cv p)) (synCsn (.cv y)) (synCsn (.cv x)) (.cv r)
      (synCsi3 (synCid)) p0001
  have p0048 := @gOtsnelsi3 (.cv p) (.cv y) (.cv x) (synCid) p0022 p0014 p0007
  have p0049 := (Nominal.biimpRefl (synWbr (.cv p) (synCid) (synCop (.cv y) (.cv x))))
  have p0050 := @gOpex (.cv y) (.cv x) p0014 p0007
  have p0051 := @gIdeq (.cv p) (synCop (.cv y) (.cv x)) p0050
  have p0052 :=
    @gN3bitr2i
      (.classMem (synCop (synCsn (.cv p)) (synCop (synCsn (.cv y)) (synCsn (.cv x))))
        (synCsi3 (synCid)))
      (.classMem (synCop (.cv p) (synCop (.cv y) (.cv x))) (synCid))
      (synWbr (.cv p) (synCid) (synCop (.cv y) (.cv x)))
      (.classEq (.cv p) (synCop (.cv y) (.cv x))) p0048 p0049 p0051
  have p0053 :=
    @gBitri
      (.classMem (synCop (synCsn (.cv p))
          (synCop (synCsn (.cv y)) (synCop (synCsn (.cv x)) (.cv r))))
        (synCins4 (synCsi3 (synCid))))
      (.classMem (synCop (synCsn (.cv p)) (synCop (synCsn (.cv y)) (synCsn (.cv x))))
        (synCsi3 (synCid)))
      (.classEq (.cv p) (synCop (.cv y) (.cv x))) p0047 p0052
  have p0054 :=
    @gAnbi12i
      (.classMem (synCop (synCsn (.cv p))
          (synCop (synCsn (.cv y)) (synCop (synCsn (.cv x)) (.cv r))))
        (synCins4 (synCsi3 (synCid))))
      (.classEq (.cv p) (synCop (.cv y) (.cv x)))
      (.classMem (synCop (synCsn (.cv p))
          (synCop (synCsn (.cv y)) (synCop (synCsn (.cv x)) (.cv r))))
        (synCins2 (synCins2 (synCsset))))
      (.objMem p r) p0053 p0037
  have p0055 :=
    @gBitri
      (.classMem (synCop (synCsn (.cv p))
          (synCop (synCsn (.cv y)) (synCop (synCsn (.cv x)) (.cv r))))
        (synCin (synCins4 (synCsi3 (synCid))) (synCins2 (synCins2 (synCsset)))))
      (synWa (.classMem (synCop (synCsn (.cv p))
            (synCop (synCsn (.cv y)) (synCop (synCsn (.cv x)) (.cv r))))
          (synCins4 (synCsi3 (synCid)))) (.classMem (synCop (synCsn (.cv p))
            (synCop (synCsn (.cv y)) (synCop (synCsn (.cv x)) (.cv r))))
          (synCins2 (synCins2 (synCsset)))))
      (synWa (.classEq (.cv p) (synCop (.cv y) (.cv x))) (.objMem p r)) p0046 p0054
  have p0056 :=
    @gExbii
      (.classMem (synCop (synCsn (.cv p))
          (synCop (synCsn (.cv y)) (synCop (synCsn (.cv x)) (.cv r))))
        (synCin (synCins4 (synCsi3 (synCid))) (synCins2 (synCins2 (synCsset)))))
      (synWa (.classEq (.cv p) (synCop (.cv y) (.cv x))) (.objMem p r)) p p0055
  have p0057 :=
    @gElima1c p (synCop (synCsn (.cv y)) (synCop (synCsn (.cv x)) (.cv r)))
      (synCin (synCins4 (synCsi3 (synCid))) (synCins2 (synCins2 (synCsset))))
      dv_cache_0007 dv_cache_0011
  have p0058 := (Nominal.biimpRefl (synWbr (.cv y) (.cv r) (.cv x)))
  have p0059 :=
    (NFChoice.DirectNominalPrf.Nominal.DefinitionLeafHandlersCanonical001.dfClelOfDV p
      (synCop (.cv y) (.cv x)) (.cv r) dv_cache_0012 dv_cache_0010)
  have p0060_e01_recanon :
    Nominal.NPrf
      (synWb (.classMem (synCop (.cv y) (.cv x)) (.cv r)) (synWex p
          (synWa (.classEq (.cv p) (synCop (.cv y) (.cv x))) (.objMem p r)))) :=
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
      p0059
  have p0060 :=
    @gBitri (synWbr (.cv y) (.cv r) (.cv x))
      (.classMem (synCop (.cv y) (.cv x)) (.cv r))
      (synWex p (synWa (.classEq (.cv p) (synCop (.cv y) (.cv x))) (.objMem p r)))
      p0058 p0060_e01_recanon
  have p0061 :=
    @gN3bitr4i
      (synWex p (.classMem (synCop (synCsn (.cv p))
            (synCop (synCsn (.cv y)) (synCop (synCsn (.cv x)) (.cv r))))
          (synCin (synCins4 (synCsi3 (synCid))) (synCins2 (synCins2 (synCsset))))))
      (synWex p (synWa (.classEq (.cv p) (synCop (.cv y) (.cv x))) (.objMem p r)))
      (.classMem (synCop (synCsn (.cv y)) (synCop (synCsn (.cv x)) (.cv r))) (synCima
          (synCin (synCins4 (synCsi3 (synCid))) (synCins2 (synCins2 (synCsset))))
          (synC1c)))
      (synWbr (.cv y) (.cv r) (.cv x)) p0056 p0057 p0060
  have p0062 :=
    @gAnbi12i
      (.classMem (synCop (synCsn (.cv y)) (synCop (synCsn (.cv x)) (.cv r))) (synCima
          (synCin (synCins4 (synCsi3 (synCtxp (synC2nd) (synC1st))))
            (synCins2 (synCins2 (synCsset)))) (synC1c)))
      (synWbr (.cv x) (.cv r) (.cv y))
      (.classMem (synCop (synCsn (.cv y)) (synCop (synCsn (.cv x)) (.cv r))) (synCima
          (synCin (synCins4 (synCsi3 (synCid))) (synCins2 (synCins2 (synCsset))))
          (synC1c)))
      (synWbr (.cv y) (.cv r) (.cv x)) p0045 p0061
  have p0063 :=
    @gBitri
      (.classMem (synCop (synCsn (.cv y)) (synCop (synCsn (.cv x)) (.cv r))) (synCin
          (synCima (synCin (synCins4 (synCsi3 (synCtxp (synC2nd) (synC1st))))
              (synCins2 (synCins2 (synCsset)))) (synC1c)) (synCima
            (synCin (synCins4 (synCsi3 (synCid))) (synCins2 (synCins2 (synCsset))))
            (synC1c))))
      (synWa (.classMem (synCop (synCsn (.cv y)) (synCop (synCsn (.cv x)) (.cv r)))
          (synCima (synCin (synCins4 (synCsi3 (synCtxp (synC2nd) (synC1st))))
              (synCins2 (synCins2 (synCsset)))) (synC1c)))
        (.classMem (synCop (synCsn (.cv y)) (synCop (synCsn (.cv x)) (.cv r))) (synCima
            (synCin (synCins4 (synCsi3 (synCid))) (synCins2 (synCins2 (synCsset))))
            (synC1c))))
      (synWa (synWbr (.cv x) (.cv r) (.cv y)) (synWbr (.cv y) (.cv r) (.cv x))) p0019
      p0062
  have p0064 := @gOtelins3 (synCsn (.cv y)) (synCsn (.cv x)) (.cv r) (synCid) p0001
  have p0065 :=
    (Nominal.biimpRefl (synWbr (synCsn (.cv y)) (synCid) (synCsn (.cv x))))
  have p0066 := @gIdeq (synCsn (.cv y)) (synCsn (.cv x)) p0011
  have p0067 := @gEqcom (synCsn (.cv y)) (synCsn (.cv x))
  have p0068 := @gSneqb (.cv x) (.cv y) p0007
  have p0069_e02_recanon :
    Nominal.NPrf (synWb (.classEq (synCsn (.cv x)) (synCsn (.cv y))) (.objEq x y)) :=
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
      p0068
  have p0069 :=
    @gN3bitri (synWbr (synCsn (.cv y)) (synCid) (synCsn (.cv x)))
      (.classEq (synCsn (.cv y)) (synCsn (.cv x)))
      (.classEq (synCsn (.cv x)) (synCsn (.cv y))) (.objEq x y) p0066 p0067
      p0069_e02_recanon
  have p0070 :=
    @gN3bitr2i
      (.classMem (synCop (synCsn (.cv y)) (synCop (synCsn (.cv x)) (.cv r)))
        (synCins3 (synCid)))
      (.classMem (synCop (synCsn (.cv y)) (synCsn (.cv x))) (synCid))
      (synWbr (synCsn (.cv y)) (synCid) (synCsn (.cv x))) (.objEq x y) p0064 p0065
      p0069
  have p0071 :=
    @gNotbii
      (.classMem (synCop (synCsn (.cv y)) (synCop (synCsn (.cv x)) (.cv r)))
        (synCins3 (synCid)))
      (.objEq x y) p0070
  have p0072 :=
    @gAnbi12i
      (.classMem (synCop (synCsn (.cv y)) (synCop (synCsn (.cv x)) (.cv r))) (synCin
          (synCima (synCin (synCins4 (synCsi3 (synCtxp (synC2nd) (synC1st))))
              (synCins2 (synCins2 (synCsset)))) (synC1c)) (synCima
            (synCin (synCins4 (synCsi3 (synCid))) (synCins2 (synCins2 (synCsset))))
            (synC1c))))
      (synWa (synWbr (.cv x) (.cv r) (.cv y)) (synWbr (.cv y) (.cv r) (.cv x)))
      (.neg (.classMem (synCop (synCsn (.cv y)) (synCop (synCsn (.cv x)) (.cv r)))
          (synCins3 (synCid))))
      (.neg (.objEq x y)) p0063 p0071
  have p0073 :=
    @gN3bitri
      (.classMem
        (synCop (synCsn (.cv y)) (synCop (synCsn (.cv x)) (synCop (.cv r) (.cv a))))
        (synCins4 (synCdif (synCin (synCima
                (synCin (synCins4 (synCsi3 (synCtxp (synC2nd) (synC1st))))
                  (synCins2 (synCins2 (synCsset)))) (synC1c)) (synCima
                (synCin (synCins4 (synCsi3 (synCid))) (synCins2 (synCins2 (synCsset))))
                (synC1c))) (synCins3 (synCid)))))
      (.classMem (synCop (synCsn (.cv y)) (synCop (synCsn (.cv x)) (.cv r))) (synCdif
          (synCin (synCima (synCin (synCins4 (synCsi3 (synCtxp (synC2nd) (synC1st))))
                (synCins2 (synCins2 (synCsset)))) (synC1c)) (synCima
              (synCin (synCins4 (synCsi3 (synCid))) (synCins2 (synCins2 (synCsset))))
              (synC1c))) (synCins3 (synCid))))
      (synWa (.classMem (synCop (synCsn (.cv y)) (synCop (synCsn (.cv x)) (.cv r)))
          (synCin (synCima (synCin (synCins4 (synCsi3 (synCtxp (synC2nd) (synC1st))))
                (synCins2 (synCins2 (synCsset)))) (synC1c)) (synCima
              (synCin (synCins4 (synCsi3 (synCid))) (synCins2 (synCins2 (synCsset))))
              (synC1c)))) (.neg
          (.classMem (synCop (synCsn (.cv y)) (synCop (synCsn (.cv x)) (.cv r)))
            (synCins3 (synCid)))))
      (synWa (synWa (synWbr (.cv x) (.cv r) (.cv y)) (synWbr (.cv y) (.cv r) (.cv x)))
        (.neg (.objEq x y)))
      p0017 p0018 p0072
  have p0074 :=
    @gAnbi12i
      (.classMem
        (synCop (synCsn (.cv y)) (synCop (synCsn (.cv x)) (synCop (.cv r) (.cv a))))
        (synCins2 (synCins2 (synCsset))))
      (.objMem y a)
      (.classMem
        (synCop (synCsn (.cv y)) (synCop (synCsn (.cv x)) (synCop (.cv r) (.cv a))))
        (synCins4 (synCdif (synCin (synCima
                (synCin (synCins4 (synCsi3 (synCtxp (synC2nd) (synC1st))))
                  (synCins2 (synCins2 (synCsset)))) (synC1c)) (synCima
                (synCin (synCins4 (synCsi3 (synCid))) (synCins2 (synCins2 (synCsset))))
                (synC1c))) (synCins3 (synCid)))))
      (synWa (synWa (synWbr (.cv x) (.cv r) (.cv y)) (synWbr (.cv y) (.cv r) (.cv x)))
        (.neg (.objEq x y)))
      p0016 p0073
  have p0075 :=
    @gBitri
      (.classMem
        (synCop (synCsn (.cv y)) (synCop (synCsn (.cv x)) (synCop (.cv r) (.cv a))))
        (synCin (synCins2 (synCins2 (synCsset))) (synCins4 (synCdif (synCin (synCima
                  (synCin (synCins4 (synCsi3 (synCtxp (synC2nd) (synC1st))))
                    (synCins2 (synCins2 (synCsset)))) (synC1c)) (synCima
                  (synCin (synCins4 (synCsi3 (synCid))) (synCins2 (synCins2 (synCsset))))
                  (synC1c))) (synCins3 (synCid))))))
      (synWa (.classMem (synCop (synCsn (.cv y))
            (synCop (synCsn (.cv x)) (synCop (.cv r) (.cv a))))
          (synCins2 (synCins2 (synCsset)))) (.classMem (synCop (synCsn (.cv y))
            (synCop (synCsn (.cv x)) (synCop (.cv r) (.cv a)))) (synCins4 (synCdif (synCin
                (synCima (synCin (synCins4 (synCsi3 (synCtxp (synC2nd) (synC1st))))
                    (synCins2 (synCins2 (synCsset)))) (synC1c)) (synCima
                  (synCin (synCins4 (synCsi3 (synCid))) (synCins2 (synCins2 (synCsset))))
                  (synC1c))) (synCins3 (synCid))))))
      (synWa (.objMem y a) (synWa
          (synWa (synWbr (.cv x) (.cv r) (.cv y)) (synWbr (.cv y) (.cv r) (.cv x)))
          (.neg (.objEq x y))))
      p0010 p0074
  have p0076 :=
    @gExbii
      (.classMem
        (synCop (synCsn (.cv y)) (synCop (synCsn (.cv x)) (synCop (.cv r) (.cv a))))
        (synCin (synCins2 (synCins2 (synCsset))) (synCins4 (synCdif (synCin (synCima
                  (synCin (synCins4 (synCsi3 (synCtxp (synC2nd) (synC1st))))
                    (synCins2 (synCins2 (synCsset)))) (synC1c)) (synCima
                  (synCin (synCins4 (synCsi3 (synCid))) (synCins2 (synCins2 (synCsset))))
                  (synC1c))) (synCins3 (synCid))))))
      (synWa (.objMem y a) (synWa
          (synWa (synWbr (.cv x) (.cv r) (.cv y)) (synWbr (.cv y) (.cv r) (.cv x)))
          (.neg (.objEq x y))))
      y p0075
  have p0077 :=
    @gElima1c y (synCop (synCsn (.cv x)) (synCop (.cv r) (.cv a)))
      (synCin (synCins2 (synCins2 (synCsset))) (synCins4 (synCdif (synCin (synCima
                (synCin (synCins4 (synCsi3 (synCtxp (synC2nd) (synC1st))))
                  (synCins2 (synCins2 (synCsset)))) (synC1c)) (synCima
                (synCin (synCins4 (synCsi3 (synCid))) (synCins2 (synCins2 (synCsset))))
                (synC1c))) (synCins3 (synCid)))))
      dv_cache_0013 dv_cache_0014
  have p0078 :=
    (Nominal.biimpRefl (synWrex y (.cv a) (synWa
          (synWa (synWbr (.cv x) (.cv r) (.cv y)) (synWbr (.cv y) (.cv r) (.cv x)))
          (.neg (.objEq x y)))))
  have p0079_e02_recanon :
    Nominal.NPrf
      (synWb (synWrex y (.cv a) (synWa
            (synWa (synWbr (.cv x) (.cv r) (.cv y)) (synWbr (.cv y) (.cv r) (.cv x)))
            (.neg (.objEq x y)))) (synWex y (synWa (.objMem y a) (synWa
              (synWa (synWbr (.cv x) (.cv r) (.cv y)) (synWbr (.cv y) (.cv r) (.cv x)))
              (.neg (.objEq x y)))))) :=
    Nominal.RecanonTransportDev.transport
      (by
        simp only [synWb, synWrex, synWex, synWa]
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
            · exact Nominal.RecanonTransportDev.TRecanonWff.same _
        · apply Nominal.RecanonTransportDev.TRecanonWff.neg
          apply Nominal.RecanonTransportDev.TRecanonWff.imp
          · apply Nominal.RecanonTransportDev.TRecanonWff.neg
            apply Nominal.RecanonTransportDev.TRecanonWff.all
            apply Nominal.RecanonTransportDev.TRecanonWff.neg
            apply Nominal.RecanonTransportDev.TRecanonWff.neg
            apply Nominal.RecanonTransportDev.TRecanonWff.imp
            · exact Nominal.RecanonTransportDev.TRecanonWff.classMem_objMem _ _
            · exact Nominal.RecanonTransportDev.TRecanonWff.same _
          · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0078
  have p0079 :=
    @gN3bitr4i
      (synWex y (.classMem (synCop (synCsn (.cv y))
            (synCop (synCsn (.cv x)) (synCop (.cv r) (.cv a))))
          (synCin (synCins2 (synCins2 (synCsset))) (synCins4 (synCdif (synCin (synCima
                    (synCin (synCins4 (synCsi3 (synCtxp (synC2nd) (synC1st))))
                      (synCins2 (synCins2 (synCsset)))) (synC1c)) (synCima
                    (synCin (synCins4 (synCsi3 (synCid)))
                      (synCins2 (synCins2 (synCsset)))) (synC1c)))
                (synCins3 (synCid)))))))
      (synWex y (synWa (.objMem y a) (synWa
            (synWa (synWbr (.cv x) (.cv r) (.cv y)) (synWbr (.cv y) (.cv r) (.cv x)))
            (.neg (.objEq x y)))))
      (.classMem (synCop (synCsn (.cv x)) (synCop (.cv r) (.cv a))) (synCima
          (synCin (synCins2 (synCins2 (synCsset))) (synCins4 (synCdif (synCin (synCima
                    (synCin (synCins4 (synCsi3 (synCtxp (synC2nd) (synC1st))))
                      (synCins2 (synCins2 (synCsset)))) (synC1c)) (synCima
                    (synCin (synCins4 (synCsi3 (synCid)))
                      (synCins2 (synCins2 (synCsset)))) (synC1c))) (synCins3 (synCid)))))
          (synC1c)))
      (synWrex y (.cv a) (synWa
          (synWa (synWbr (.cv x) (.cv r) (.cv y)) (synWbr (.cv y) (.cv r) (.cv x)))
          (.neg (.objEq x y))))
      p0076 p0077 p0079_e02_recanon
  have p0080 :=
    @gRexanali
      (synWa (synWbr (.cv x) (.cv r) (.cv y)) (synWbr (.cv y) (.cv r) (.cv x)))
      (.objEq x y) y (.cv a)
  have p0081 :=
    @gBitri
      (.classMem (synCop (synCsn (.cv x)) (synCop (.cv r) (.cv a))) (synCima
          (synCin (synCins2 (synCins2 (synCsset))) (synCins4 (synCdif (synCin (synCima
                    (synCin (synCins4 (synCsi3 (synCtxp (synC2nd) (synC1st))))
                      (synCins2 (synCins2 (synCsset)))) (synC1c)) (synCima
                    (synCin (synCins4 (synCsi3 (synCid)))
                      (synCins2 (synCins2 (synCsset)))) (synC1c))) (synCins3 (synCid)))))
          (synC1c)))
      (synWrex y (.cv a) (synWa
          (synWa (synWbr (.cv x) (.cv r) (.cv y)) (synWbr (.cv y) (.cv r) (.cv x)))
          (.neg (.objEq x y))))
      (.neg (synWral y (.cv a) (.imp
            (synWa (synWbr (.cv x) (.cv r) (.cv y)) (synWbr (.cv y) (.cv r) (.cv x)))
            (.objEq x y))))
      p0079 p0080
  have p0082 :=
    @gAnbi12i
      (.classMem (synCop (synCsn (.cv x)) (synCop (.cv r) (.cv a))) (synCins2 (synCsset)))
      (.objMem x a)
      (.classMem (synCop (synCsn (.cv x)) (synCop (.cv r) (.cv a))) (synCima
          (synCin (synCins2 (synCins2 (synCsset))) (synCins4 (synCdif (synCin (synCima
                    (synCin (synCins4 (synCsi3 (synCtxp (synC2nd) (synC1st))))
                      (synCins2 (synCins2 (synCsset)))) (synC1c)) (synCima
                    (synCin (synCins4 (synCsi3 (synCid)))
                      (synCins2 (synCins2 (synCsset)))) (synC1c))) (synCins3 (synCid)))))
          (synC1c)))
      (.neg (synWral y (.cv a) (.imp
            (synWa (synWbr (.cv x) (.cv r) (.cv y)) (synWbr (.cv y) (.cv r) (.cv x)))
            (.objEq x y))))
      p0009 p0081
  have p0083 :=
    @gBitri
      (.classMem (synCop (synCsn (.cv x)) (synCop (.cv r) (.cv a)))
        (synCin (synCins2 (synCsset)) (synCima (synCin (synCins2 (synCins2 (synCsset)))
              (synCins4 (synCdif (synCin (synCima
                      (synCin (synCins4 (synCsi3 (synCtxp (synC2nd) (synC1st))))
                        (synCins2 (synCins2 (synCsset)))) (synC1c)) (synCima
                      (synCin (synCins4 (synCsi3 (synCid)))
                        (synCins2 (synCins2 (synCsset)))) (synC1c)))
                  (synCins3 (synCid))))) (synC1c))))
      (synWa (.classMem (synCop (synCsn (.cv x)) (synCop (.cv r) (.cv a)))
          (synCins2 (synCsset)))
        (.classMem (synCop (synCsn (.cv x)) (synCop (.cv r) (.cv a))) (synCima
            (synCin (synCins2 (synCins2 (synCsset))) (synCins4 (synCdif (synCin (synCima
                      (synCin (synCins4 (synCsi3 (synCtxp (synC2nd) (synC1st))))
                        (synCins2 (synCins2 (synCsset)))) (synC1c)) (synCima
                      (synCin (synCins4 (synCsi3 (synCid)))
                        (synCins2 (synCins2 (synCsset)))) (synC1c)))
                  (synCins3 (synCid))))) (synC1c))))
      (synWa (.objMem x a) (.neg (synWral y (.cv a) (.imp
              (synWa (synWbr (.cv x) (.cv r) (.cv y)) (synWbr (.cv y) (.cv r) (.cv x)))
              (.objEq x y)))))
      p0005 p0082
  have p0084 :=
    @gExbii
      (.classMem (synCop (synCsn (.cv x)) (synCop (.cv r) (.cv a)))
        (synCin (synCins2 (synCsset)) (synCima (synCin (synCins2 (synCins2 (synCsset)))
              (synCins4 (synCdif (synCin (synCima
                      (synCin (synCins4 (synCsi3 (synCtxp (synC2nd) (synC1st))))
                        (synCins2 (synCins2 (synCsset)))) (synC1c)) (synCima
                      (synCin (synCins4 (synCsi3 (synCid)))
                        (synCins2 (synCins2 (synCsset)))) (synC1c)))
                  (synCins3 (synCid))))) (synC1c))))
      (synWa (.objMem x a) (.neg (synWral y (.cv a) (.imp
              (synWa (synWbr (.cv x) (.cv r) (.cv y)) (synWbr (.cv y) (.cv r) (.cv x)))
              (.objEq x y)))))
      x p0083
  have p0085 :=
    @gElima1c x (synCop (.cv r) (.cv a))
      (synCin (synCins2 (synCsset)) (synCima (synCin (synCins2 (synCins2 (synCsset)))
            (synCins4 (synCdif (synCin (synCima
                    (synCin (synCins4 (synCsi3 (synCtxp (synC2nd) (synC1st))))
                      (synCins2 (synCins2 (synCsset)))) (synC1c)) (synCima
                    (synCin (synCins4 (synCsi3 (synCid)))
                      (synCins2 (synCins2 (synCsset)))) (synC1c))) (synCins3 (synCid)))))
          (synC1c)))
      dv_cache_0015 dv_cache_0016
  have p0086 :=
    (Nominal.biimpRefl (synWrex x (.cv a) (.neg (synWral y (.cv a) (.imp
              (synWa (synWbr (.cv x) (.cv r) (.cv y)) (synWbr (.cv y) (.cv r) (.cv x)))
              (.objEq x y))))))
  have p0087_e02_recanon :
    Nominal.NPrf
      (synWb (synWrex x (.cv a) (.neg (synWral y (.cv a) (.imp
                (synWa (synWbr (.cv x) (.cv r) (.cv y)) (synWbr (.cv y) (.cv r) (.cv x)))
                (.objEq x y))))) (synWex x (synWa (.objMem x a) (.neg (synWral y (.cv a)
                (.imp (synWa (synWbr (.cv x) (.cv r) (.cv y))
                    (synWbr (.cv y) (.cv r) (.cv x))) (.objEq x y))))))) :=
    Nominal.RecanonTransportDev.transport
      (by
        simp only [synWb, synWrex, synWex, synWa, synWral]
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
            · exact Nominal.RecanonTransportDev.TRecanonWff.same _
        · apply Nominal.RecanonTransportDev.TRecanonWff.neg
          apply Nominal.RecanonTransportDev.TRecanonWff.imp
          · apply Nominal.RecanonTransportDev.TRecanonWff.neg
            apply Nominal.RecanonTransportDev.TRecanonWff.all
            apply Nominal.RecanonTransportDev.TRecanonWff.neg
            apply Nominal.RecanonTransportDev.TRecanonWff.neg
            apply Nominal.RecanonTransportDev.TRecanonWff.imp
            · exact Nominal.RecanonTransportDev.TRecanonWff.classMem_objMem _ _
            · exact Nominal.RecanonTransportDev.TRecanonWff.same _
          · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0086
  have p0087 :=
    @gN3bitr4i
      (synWex x (.classMem (synCop (synCsn (.cv x)) (synCop (.cv r) (.cv a)))
          (synCin (synCins2 (synCsset)) (synCima
              (synCin (synCins2 (synCins2 (synCsset))) (synCins4 (synCdif (synCin
                      (synCima (synCin (synCins4 (synCsi3 (synCtxp (synC2nd) (synC1st))))
                          (synCins2 (synCins2 (synCsset)))) (synC1c)) (synCima
                        (synCin (synCins4 (synCsi3 (synCid)))
                          (synCins2 (synCins2 (synCsset)))) (synC1c)))
                    (synCins3 (synCid))))) (synC1c)))))
      (synWex x (synWa (.objMem x a) (.neg (synWral y (.cv a) (.imp
                (synWa (synWbr (.cv x) (.cv r) (.cv y)) (synWbr (.cv y) (.cv r) (.cv x)))
                (.objEq x y))))))
      (.classMem (synCop (.cv r) (.cv a)) (synCima (synCin (synCins2 (synCsset)) (synCima
              (synCin (synCins2 (synCins2 (synCsset))) (synCins4 (synCdif (synCin
                      (synCima (synCin (synCins4 (synCsi3 (synCtxp (synC2nd) (synC1st))))
                          (synCins2 (synCins2 (synCsset)))) (synC1c)) (synCima
                        (synCin (synCins4 (synCsi3 (synCid)))
                          (synCins2 (synCins2 (synCsset)))) (synC1c)))
                    (synCins3 (synCid))))) (synC1c))) (synC1c)))
      (synWrex x (.cv a) (.neg (synWral y (.cv a) (.imp
              (synWa (synWbr (.cv x) (.cv r) (.cv y)) (synWbr (.cv y) (.cv r) (.cv x)))
              (.objEq x y)))))
      p0084 p0085 p0087_e02_recanon
  have p0088 :=
    @gRexnal
      (synWral y (.cv a)
        (.imp (synWa (synWbr (.cv x) (.cv r) (.cv y)) (synWbr (.cv y) (.cv r) (.cv x)))
          (.objEq x y)))
      x (.cv a)
  have p0089 :=
    @gBitri
      (.classMem (synCop (.cv r) (.cv a)) (synCima (synCin (synCins2 (synCsset)) (synCima
              (synCin (synCins2 (synCins2 (synCsset))) (synCins4 (synCdif (synCin
                      (synCima (synCin (synCins4 (synCsi3 (synCtxp (synC2nd) (synC1st))))
                          (synCins2 (synCins2 (synCsset)))) (synC1c)) (synCima
                        (synCin (synCins4 (synCsi3 (synCid)))
                          (synCins2 (synCins2 (synCsset)))) (synC1c)))
                    (synCins3 (synCid))))) (synC1c))) (synC1c)))
      (synWrex x (.cv a) (.neg (synWral y (.cv a) (.imp
              (synWa (synWbr (.cv x) (.cv r) (.cv y)) (synWbr (.cv y) (.cv r) (.cv x)))
              (.objEq x y)))))
      (.neg (synWral x (.cv a) (synWral y (.cv a) (.imp
              (synWa (synWbr (.cv x) (.cv r) (.cv y)) (synWbr (.cv y) (.cv r) (.cv x)))
              (.objEq x y)))))
      p0087 p0088
  have p0090 :=
    @gCon2bii
      (.classMem (synCop (.cv r) (.cv a)) (synCima (synCin (synCins2 (synCsset)) (synCima
              (synCin (synCins2 (synCins2 (synCsset))) (synCins4 (synCdif (synCin
                      (synCima (synCin (synCins4 (synCsi3 (synCtxp (synC2nd) (synC1st))))
                          (synCins2 (synCins2 (synCsset)))) (synC1c)) (synCima
                        (synCin (synCins4 (synCsi3 (synCid)))
                          (synCins2 (synCins2 (synCsset)))) (synC1c)))
                    (synCins3 (synCid))))) (synC1c))) (synC1c)))
      (synWral x (.cv a) (synWral y (.cv a) (.imp
            (synWa (synWbr (.cv x) (.cv r) (.cv y)) (synWbr (.cv y) (.cv r) (.cv x)))
            (.objEq x y))))
      p0089
  have p0091 :=
    @gBitr4i
      (.classMem (synCop (.cv r) (.cv a)) (synCcompl (synCima
            (synCin (synCins2 (synCsset)) (synCima
                (synCin (synCins2 (synCins2 (synCsset))) (synCins4 (synCdif (synCin
                        (synCima
                          (synCin (synCins4 (synCsi3 (synCtxp (synC2nd) (synC1st))))
                            (synCins2 (synCins2 (synCsset)))) (synC1c)) (synCima
                          (synCin (synCins4 (synCsi3 (synCid)))
                            (synCins2 (synCins2 (synCsset)))) (synC1c)))
                      (synCins3 (synCid))))) (synC1c))) (synC1c))))
      (.neg (.classMem (synCop (.cv r) (.cv a)) (synCima (synCin (synCins2 (synCsset))
              (synCima (synCin (synCins2 (synCins2 (synCsset))) (synCins4 (synCdif
                      (synCin (synCima
                          (synCin (synCins4 (synCsi3 (synCtxp (synC2nd) (synC1st))))
                            (synCins2 (synCins2 (synCsset)))) (synC1c)) (synCima
                          (synCin (synCins4 (synCsi3 (synCid)))
                            (synCins2 (synCins2 (synCsset)))) (synC1c)))
                      (synCins3 (synCid))))) (synC1c))) (synC1c))))
      (synWral x (.cv a) (synWral y (.cv a) (.imp
            (synWa (synWbr (.cv x) (.cv r) (.cv y)) (synWbr (.cv y) (.cv r) (.cv x)))
            (.objEq x y))))
      p0004 p0090
  have p0092 :=
    @gOpabbi2i
      (synWral x (.cv a) (synWral y (.cv a) (.imp
            (synWa (synWbr (.cv x) (.cv r) (.cv y)) (synWbr (.cv y) (.cv r) (.cv x)))
            (.objEq x y))))
      r a
      (synCcompl (synCima (synCin (synCins2 (synCsset)) (synCima
              (synCin (synCins2 (synCins2 (synCsset))) (synCins4 (synCdif (synCin
                      (synCima (synCin (synCins4 (synCsi3 (synCtxp (synC2nd) (synC1st))))
                          (synCins2 (synCins2 (synCsset)))) (synC1c)) (synCima
                        (synCin (synCins4 (synCsi3 (synCid)))
                          (synCins2 (synCins2 (synCsset)))) (synC1c)))
                    (synCins3 (synCid))))) (synC1c))) (synC1c)))
      dv_cache_0017 dv_cache_0018 dv_cache_0019 p0091
  have p0093 :=
    @gEqtr4i (synCantisym)
      (synCopab r a (synWral x (.cv a) (synWral y (.cv a) (.imp
              (synWa (synWbr (.cv x) (.cv r) (.cv y)) (synWbr (.cv y) (.cv r) (.cv x)))
              (.objEq x y)))))
      (synCcompl (synCima (synCin (synCins2 (synCsset)) (synCima
              (synCin (synCins2 (synCins2 (synCsset))) (synCins4 (synCdif (synCin
                      (synCima (synCin (synCins4 (synCsi3 (synCtxp (synC2nd) (synC1st))))
                          (synCins2 (synCins2 (synCsset)))) (synC1c)) (synCima
                        (synCin (synCins4 (synCsi3 (synCid)))
                          (synCins2 (synCins2 (synCsset)))) (synC1c)))
                    (synCins3 (synCid))))) (synC1c))) (synC1c)))
      p0000 p0092
  have p0094 := @gSsetex
  have p0095 := @gIns2ex (synCsset) p0094
  have p0096 := @gIns2ex (synCins2 (synCsset)) p0095
  have p0097 := @gN2ndex
  have p0098 := @gN1stex
  have p0099 := @gTxpex (synC2nd) (synC1st) p0097 p0098
  have p0100 := @gSi3ex (synCtxp (synC2nd) (synC1st)) p0099
  have p0101 := @gIns4ex (synCsi3 (synCtxp (synC2nd) (synC1st))) p0100
  have p0102 :=
    @gInex (synCins4 (synCsi3 (synCtxp (synC2nd) (synC1st))))
      (synCins2 (synCins2 (synCsset))) p0101 p0096
  have p0103 := @gN1cex
  have p0104 :=
    @gImaex
      (synCin (synCins4 (synCsi3 (synCtxp (synC2nd) (synC1st))))
        (synCins2 (synCins2 (synCsset))))
      (synC1c) p0102 p0103
  have p0105 := @gIdex
  have p0106 := @gSi3ex (synCid) p0105
  have p0107 := @gIns4ex (synCsi3 (synCid)) p0106
  have p0108 :=
    @gInex (synCins4 (synCsi3 (synCid))) (synCins2 (synCins2 (synCsset))) p0107
      p0096
  have p0110 :=
    @gImaex
      (synCin (synCins4 (synCsi3 (synCid))) (synCins2 (synCins2 (synCsset))))
      (synC1c) p0108 p0103
  have p0111 :=
    @gInex
      (synCima (synCin (synCins4 (synCsi3 (synCtxp (synC2nd) (synC1st))))
          (synCins2 (synCins2 (synCsset)))) (synC1c))
      (synCima (synCin (synCins4 (synCsi3 (synCid))) (synCins2 (synCins2 (synCsset))))
        (synC1c))
      p0104 p0110
  have p0113 := @gIns3ex (synCid) p0105
  have p0114 :=
    @gDifex
      (synCin (synCima (synCin (synCins4 (synCsi3 (synCtxp (synC2nd) (synC1st))))
            (synCins2 (synCins2 (synCsset)))) (synC1c)) (synCima
          (synCin (synCins4 (synCsi3 (synCid))) (synCins2 (synCins2 (synCsset))))
          (synC1c)))
      (synCins3 (synCid)) p0111 p0113
  have p0115 :=
    @gIns4ex
      (synCdif (synCin (synCima
            (synCin (synCins4 (synCsi3 (synCtxp (synC2nd) (synC1st))))
              (synCins2 (synCins2 (synCsset)))) (synC1c)) (synCima
            (synCin (synCins4 (synCsi3 (synCid))) (synCins2 (synCins2 (synCsset))))
            (synC1c))) (synCins3 (synCid)))
      p0114
  have p0116 :=
    @gInex (synCins2 (synCins2 (synCsset)))
      (synCins4 (synCdif (synCin (synCima
              (synCin (synCins4 (synCsi3 (synCtxp (synC2nd) (synC1st))))
                (synCins2 (synCins2 (synCsset)))) (synC1c)) (synCima
              (synCin (synCins4 (synCsi3 (synCid))) (synCins2 (synCins2 (synCsset))))
              (synC1c))) (synCins3 (synCid))))
      p0096 p0115
  have p0118 :=
    @gImaex
      (synCin (synCins2 (synCins2 (synCsset))) (synCins4 (synCdif (synCin (synCima
                (synCin (synCins4 (synCsi3 (synCtxp (synC2nd) (synC1st))))
                  (synCins2 (synCins2 (synCsset)))) (synC1c)) (synCima
                (synCin (synCins4 (synCsi3 (synCid))) (synCins2 (synCins2 (synCsset))))
                (synC1c))) (synCins3 (synCid)))))
      (synC1c) p0116 p0103
  have p0119 :=
    @gInex (synCins2 (synCsset))
      (synCima (synCin (synCins2 (synCins2 (synCsset))) (synCins4 (synCdif (synCin
                (synCima (synCin (synCins4 (synCsi3 (synCtxp (synC2nd) (synC1st))))
                    (synCins2 (synCins2 (synCsset)))) (synC1c)) (synCima
                  (synCin (synCins4 (synCsi3 (synCid))) (synCins2 (synCins2 (synCsset))))
                  (synC1c))) (synCins3 (synCid))))) (synC1c))
      p0095 p0118
  have p0121 :=
    @gImaex
      (synCin (synCins2 (synCsset)) (synCima (synCin (synCins2 (synCins2 (synCsset)))
            (synCins4 (synCdif (synCin (synCima
                    (synCin (synCins4 (synCsi3 (synCtxp (synC2nd) (synC1st))))
                      (synCins2 (synCins2 (synCsset)))) (synC1c)) (synCima
                    (synCin (synCins4 (synCsi3 (synCid)))
                      (synCins2 (synCins2 (synCsset)))) (synC1c))) (synCins3 (synCid)))))
          (synC1c)))
      (synC1c) p0119 p0103
  have p0122 :=
    @gComplex
      (synCima (synCin (synCins2 (synCsset)) (synCima
            (synCin (synCins2 (synCins2 (synCsset))) (synCins4 (synCdif (synCin (synCima
                      (synCin (synCins4 (synCsi3 (synCtxp (synC2nd) (synC1st))))
                        (synCins2 (synCins2 (synCsset)))) (synC1c)) (synCima
                      (synCin (synCins4 (synCsi3 (synCid)))
                        (synCins2 (synCins2 (synCsset)))) (synC1c)))
                  (synCins3 (synCid))))) (synC1c))) (synC1c))
      p0121
  have p0123 :=
    @gEqeltri (synCantisym)
      (synCcompl (synCima (synCin (synCins2 (synCsset)) (synCima
              (synCin (synCins2 (synCins2 (synCsset))) (synCins4 (synCdif (synCin
                      (synCima (synCin (synCins4 (synCsi3 (synCtxp (synC2nd) (synC1st))))
                          (synCins2 (synCins2 (synCsset)))) (synC1c)) (synCima
                        (synCin (synCins4 (synCsi3 (synCid)))
                          (synCins2 (synCins2 (synCsset)))) (synC1c)))
                    (synCins3 (synCid))))) (synC1c))) (synC1c)))
      (synCvv) p0093 p0122
  exact p0123


end NFChoice.DirectNominalPrf.WPPReplay

end

/-! Certificates from `NominalWPPReplayChunk013Compact001Part021`. -/


section

namespace NFChoice.DirectNominalPrf.WPPReplay

open scoped Fol
open NFChoice.Foundation
open NFChoice.SemanticCore
open NFChoice.ReplaySupport
open NFChoice.Compiler.CompactSourceSyntax

/-- Checked nominal proof certificate identified upstream as `g_connexex`. -/
@[expose]
noncomputable def gConnexex : Nominal.NPrf (.classMem (synCconnex) (synCvv)) :=
  by
  let proofSupport : Finset Var := (∅ : Finset Var)
  let x : Var := freshVar proofSupport 0
  let y : Var := freshVar proofSupport 1
  let r : Var := freshVar proofSupport 2
  let a : Var := freshVar proofSupport 3
  let p : Var := freshVar proofSupport 4
  have fresh_x_ne_y : x ≠ y :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have fresh_y_ne_x : y ≠ x := Ne.symm fresh_x_ne_y
  have fresh_x_ne_r : x ≠ r :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 2
    exact freshVar_injective proofSupport (i := 0) (j := 2) (by decide)
  have fresh_r_ne_x : r ≠ x := Ne.symm fresh_x_ne_r
  have fresh_x_ne_a : x ≠ a :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 3
    exact freshVar_injective proofSupport (i := 0) (j := 3) (by decide)
  have fresh_a_ne_x : a ≠ x := Ne.symm fresh_x_ne_a
  have fresh_x_ne_p : x ≠ p :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 4
    exact freshVar_injective proofSupport (i := 0) (j := 4) (by decide)
  have fresh_p_ne_x : p ≠ x := Ne.symm fresh_x_ne_p
  have fresh_y_ne_r : y ≠ r :=
    by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 2
    exact freshVar_injective proofSupport (i := 1) (j := 2) (by decide)
  have fresh_r_ne_y : r ≠ y := Ne.symm fresh_y_ne_r
  have fresh_y_ne_a : y ≠ a :=
    by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 3
    exact freshVar_injective proofSupport (i := 1) (j := 3) (by decide)
  have fresh_a_ne_y : a ≠ y := Ne.symm fresh_y_ne_a
  have fresh_y_ne_p : y ≠ p :=
    by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 4
    exact freshVar_injective proofSupport (i := 1) (j := 4) (by decide)
  have fresh_p_ne_y : p ≠ y := Ne.symm fresh_y_ne_p
  have fresh_r_ne_a : r ≠ a :=
    by
    change freshVar proofSupport 2 ≠ freshVar proofSupport 3
    exact freshVar_injective proofSupport (i := 2) (j := 3) (by decide)
  have fresh_a_ne_r : a ≠ r := Ne.symm fresh_r_ne_a
  have fresh_r_ne_p : r ≠ p :=
    by
    change freshVar proofSupport 2 ≠ freshVar proofSupport 4
    exact freshVar_injective proofSupport (i := 2) (j := 4) (by decide)
  have fresh_p_ne_r : p ≠ r := Ne.symm fresh_r_ne_p
  have dv_cache_0001 : a ≠ r := by exact (show a ≠ r from (by exact fresh_a_ne_r))
  have dv_cache_0002 : a ≠ x := by
    clear dv_cache_0001
    exact (show a ≠ x from (by exact fresh_a_ne_x))
  have dv_cache_0003 : a ≠ y :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact (show a ≠ y from (by exact fresh_a_ne_y))
  have dv_cache_0004 : r ≠ x :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact (show r ≠ x from (by exact fresh_r_ne_x))
  have dv_cache_0005 : r ≠ y :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact (show r ≠ y from (by exact fresh_r_ne_y))
  have dv_cache_0006 : x ≠ y :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact (show x ≠ y from (by exact fresh_x_ne_y))
  have dv_cache_0007 : x ∉ ((synCop (.cv r) (.cv a))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cop,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, fresh_x_ne_r, fresh_x_ne_a, or_false, not_false_eq_true])
  have dv_cache_0008 :
    x ∉
      ((synCin (synCins2 (synCsset)) (synCima (synCdif (synCins2 (synCins2 (synCsset)))
              (synCins4 (synCun (synCima (synCin (synCins4 (synCsi3 (synCswap)))
                      (synCins2 (synCins2 (synCsset)))) (synC1c)) (synCima
                    (synCin (synCins4 (synCsi3 (synCid)))
                      (synCins2 (synCins2 (synCsset)))) (synC1c))))) (synC1c)))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins2,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csset,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cima,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdif,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins4,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cun,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csi3,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cswap,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cid, Finset.mem_union,
          compact_fv_not_mem_empty, or_false, not_false_eq_true])
  have dv_cache_0009 : y ∉ ((synCop (synCsn (.cv x)) (synCop (.cv r) (.cv a)))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cop,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, fresh_y_ne_x, fresh_y_ne_r, fresh_y_ne_a, or_false,
          not_false_eq_true])
  have dv_cache_0010 :
    y ∉
      ((synCdif (synCins2 (synCins2 (synCsset))) (synCins4 (synCun (synCima
                (synCin (synCins4 (synCsi3 (synCswap))) (synCins2 (synCins2 (synCsset))))
                (synC1c)) (synCima (synCin (synCins4 (synCsi3 (synCid)))
                  (synCins2 (synCins2 (synCsset)))) (synC1c)))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdif,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins2,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csset,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins4,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cun,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cima,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csi3,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cswap,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cid, Finset.mem_union,
          compact_fv_not_mem_empty, or_false, not_false_eq_true])
  have dv_cache_0011 :
    p ∉ ((synCop (synCsn (.cv y)) (synCop (synCsn (.cv x)) (.cv r)))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010
    exact
      (by
        have compact_fv_not_mem_empty : p ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cop,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, fresh_p_ne_y, fresh_p_ne_x, fresh_p_ne_r, or_false,
          not_false_eq_true])
  have dv_cache_0012 :
    p ∉
      ((synCin (synCins4 (synCsi3 (synCswap))) (synCins2 (synCins2 (synCsset))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
    exact
      (by
        have compact_fv_not_mem_empty : p ∉ (∅ : Finset Var) :=
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
  have dv_cache_0013 : p ∉ ((synCop (.cv x) (.cv y))).fv :=
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
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cop,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, fresh_p_ne_x, fresh_p_ne_y, or_false, not_false_eq_true])
  have dv_cache_0014 : p ∉ ((Class.cv r)).fv :=
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
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_p_ne_r, not_false_eq_true])
  have dv_cache_0015 :
    p ∉
      ((synCin (synCins4 (synCsi3 (synCid))) (synCins2 (synCins2 (synCsset))))).fv :=
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
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins4,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csi3,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cid,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins2,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csset, Finset.mem_union,
          compact_fv_not_mem_empty, or_false, not_false_eq_true])
  have dv_cache_0016 : p ∉ ((synCop (.cv y) (.cv x))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015
    exact
      (by
        have compact_fv_not_mem_empty : p ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cop,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, fresh_p_ne_y, fresh_p_ne_x, or_false, not_false_eq_true])
  have dv_cache_0017 :
    r ∉
      ((synCcompl (synCima (synCin (synCins2 (synCsset)) (synCima
                (synCdif (synCins2 (synCins2 (synCsset))) (synCins4 (synCun (synCima
                        (synCin (synCins4 (synCsi3 (synCswap)))
                          (synCins2 (synCins2 (synCsset)))) (synC1c)) (synCima
                        (synCin (synCins4 (synCsi3 (synCid)))
                          (synCins2 (synCins2 (synCsset)))) (synC1c))))) (synC1c)))
            (synC1c)))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016
    exact
      (by
        have compact_fv_not_mem_empty : r ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccompl,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cima,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins2,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csset,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdif,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins4,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cun,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csi3,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cswap,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cid, Finset.mem_union,
          compact_fv_not_mem_empty, or_false, not_false_eq_true])
  have dv_cache_0018 :
    a ∉
      ((synCcompl (synCima (synCin (synCins2 (synCsset)) (synCima
                (synCdif (synCins2 (synCins2 (synCsset))) (synCins4 (synCun (synCima
                        (synCin (synCins4 (synCsi3 (synCswap)))
                          (synCins2 (synCins2 (synCsset)))) (synC1c)) (synCima
                        (synCin (synCins4 (synCsi3 (synCid)))
                          (synCins2 (synCins2 (synCsset)))) (synC1c))))) (synC1c)))
            (synC1c)))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
    exact
      (by
        have compact_fv_not_mem_empty : a ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccompl,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cima,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins2,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csset,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdif,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins4,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cun,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csi3,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cswap,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cid, Finset.mem_union,
          compact_fv_not_mem_empty, or_false, not_false_eq_true])
  have dv_cache_0019 : r ≠ a :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018
    exact (show r ≠ a from (by exact fresh_r_ne_a))
  have p0000 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominalDfConnex x y r a
      dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006
  have p0001 := @gVex r
  have p0002 := @gVex a
  have p0003 := @gOpex (.cv r) (.cv a) p0001 p0002
  have p0004 :=
    @gElcompl (synCop (.cv r) (.cv a))
      (synCima (synCin (synCins2 (synCsset)) (synCima
            (synCdif (synCins2 (synCins2 (synCsset))) (synCins4 (synCun (synCima
                    (synCin (synCins4 (synCsi3 (synCswap)))
                      (synCins2 (synCins2 (synCsset)))) (synC1c)) (synCima
                    (synCin (synCins4 (synCsi3 (synCid)))
                      (synCins2 (synCins2 (synCsset)))) (synC1c))))) (synC1c))) (synC1c))
      p0003
  have p0005 :=
    @gElima1c x (synCop (.cv r) (.cv a))
      (synCin (synCins2 (synCsset)) (synCima (synCdif (synCins2 (synCins2 (synCsset)))
            (synCins4 (synCun (synCima (synCin (synCins4 (synCsi3 (synCswap)))
                    (synCins2 (synCins2 (synCsset)))) (synC1c)) (synCima
                  (synCin (synCins4 (synCsi3 (synCid))) (synCins2 (synCins2 (synCsset))))
                  (synC1c))))) (synC1c)))
      dv_cache_0007 dv_cache_0008
  have p0006 :=
    @gElin (synCop (synCsn (.cv x)) (synCop (.cv r) (.cv a))) (synCins2 (synCsset))
      (synCima (synCdif (synCins2 (synCins2 (synCsset))) (synCins4 (synCun (synCima
                (synCin (synCins4 (synCsi3 (synCswap))) (synCins2 (synCins2 (synCsset))))
                (synC1c)) (synCima (synCin (synCins4 (synCsi3 (synCid)))
                  (synCins2 (synCins2 (synCsset)))) (synC1c))))) (synC1c))
  have p0007 := @gOtelins2 (synCsn (.cv x)) (.cv r) (.cv a) (synCsset) p0001
  have p0008 := @gVex x
  have p0009 := @gOpelssetsn (.cv x) (.cv a) p0008 p0002
  have p0010_e01_recanon :
    Nominal.NPrf
      (synWb (.classMem (synCop (synCsn (.cv x)) (.cv a)) (synCsset)) (.objMem x a)) :=
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
      p0009
  have p0010 :=
    @gBitri
      (.classMem (synCop (synCsn (.cv x)) (synCop (.cv r) (.cv a))) (synCins2 (synCsset)))
      (.classMem (synCop (synCsn (.cv x)) (.cv a)) (synCsset)) (.objMem x a) p0007
      p0010_e01_recanon
  have p0011 :=
    @gElima1c y (synCop (synCsn (.cv x)) (synCop (.cv r) (.cv a)))
      (synCdif (synCins2 (synCins2 (synCsset))) (synCins4 (synCun (synCima
              (synCin (synCins4 (synCsi3 (synCswap))) (synCins2 (synCins2 (synCsset))))
              (synC1c)) (synCima (synCin (synCins4 (synCsi3 (synCid)))
                (synCins2 (synCins2 (synCsset)))) (synC1c)))))
      dv_cache_0009 dv_cache_0010
  have p0012 :=
    @gEldif
      (synCop (synCsn (.cv y)) (synCop (synCsn (.cv x)) (synCop (.cv r) (.cv a))))
      (synCins2 (synCins2 (synCsset)))
      (synCins4 (synCun (synCima (synCin (synCins4 (synCsi3 (synCswap)))
              (synCins2 (synCins2 (synCsset)))) (synC1c)) (synCima
            (synCin (synCins4 (synCsi3 (synCid))) (synCins2 (synCins2 (synCsset))))
            (synC1c))))
  have p0013 := @gSnex (.cv x)
  have p0014 :=
    @gOtelins2 (synCsn (.cv y)) (synCsn (.cv x)) (synCop (.cv r) (.cv a))
      (synCins2 (synCsset)) p0013
  have p0015 := @gOtelins2 (synCsn (.cv y)) (.cv r) (.cv a) (synCsset) p0001
  have p0016 := @gVex y
  have p0017 := @gOpelssetsn (.cv y) (.cv a) p0016 p0002
  have p0018_e02_recanon :
    Nominal.NPrf
      (synWb (.classMem (synCop (synCsn (.cv y)) (.cv a)) (synCsset)) (.objMem y a)) :=
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
    @gN3bitri
      (.classMem
        (synCop (synCsn (.cv y)) (synCop (synCsn (.cv x)) (synCop (.cv r) (.cv a))))
        (synCins2 (synCins2 (synCsset))))
      (.classMem (synCop (synCsn (.cv y)) (synCop (.cv r) (.cv a))) (synCins2 (synCsset)))
      (.classMem (synCop (synCsn (.cv y)) (.cv a)) (synCsset)) (.objMem y a) p0014
      p0015 p0018_e02_recanon
  have p0019 :=
    @gOqelins4 (synCsn (.cv y)) (synCsn (.cv x)) (.cv r) (.cv a)
      (synCun (synCima
          (synCin (synCins4 (synCsi3 (synCswap))) (synCins2 (synCins2 (synCsset))))
          (synC1c)) (synCima
          (synCin (synCins4 (synCsi3 (synCid))) (synCins2 (synCins2 (synCsset))))
          (synC1c)))
      p0002
  have p0020 :=
    @gElun (synCop (synCsn (.cv y)) (synCop (synCsn (.cv x)) (.cv r)))
      (synCima (synCin (synCins4 (synCsi3 (synCswap))) (synCins2 (synCins2 (synCsset))))
        (synC1c))
      (synCima (synCin (synCins4 (synCsi3 (synCid))) (synCins2 (synCins2 (synCsset))))
        (synC1c))
  have p0021 :=
    @gElin
      (synCop (synCsn (.cv p))
        (synCop (synCsn (.cv y)) (synCop (synCsn (.cv x)) (.cv r))))
      (synCins4 (synCsi3 (synCswap))) (synCins2 (synCins2 (synCsset)))
  have p0022 :=
    @gOqelins4 (synCsn (.cv p)) (synCsn (.cv y)) (synCsn (.cv x)) (.cv r)
      (synCsi3 (synCswap)) p0001
  have p0023 := @gVex p
  have p0024 := @gOtsnelsi3 (.cv p) (.cv y) (.cv x) (synCswap) p0023 p0016 p0008
  have p0025 :=
    (Nominal.biimpRefl (synWbr (.cv p) (synCswap) (synCop (.cv y) (.cv x))))
  have p0026 := @gBrswap2 (.cv p) (.cv y) (.cv x) p0016 p0008
  have p0027 :=
    @gBitr3i (.classMem (synCop (.cv p) (synCop (.cv y) (.cv x))) (synCswap))
      (synWbr (.cv p) (synCswap) (synCop (.cv y) (.cv x)))
      (.classEq (.cv p) (synCop (.cv x) (.cv y))) p0025 p0026
  have p0028 :=
    @gN3bitri
      (.classMem (synCop (synCsn (.cv p))
          (synCop (synCsn (.cv y)) (synCop (synCsn (.cv x)) (.cv r))))
        (synCins4 (synCsi3 (synCswap))))
      (.classMem (synCop (synCsn (.cv p)) (synCop (synCsn (.cv y)) (synCsn (.cv x))))
        (synCsi3 (synCswap)))
      (.classMem (synCop (.cv p) (synCop (.cv y) (.cv x))) (synCswap))
      (.classEq (.cv p) (synCop (.cv x) (.cv y))) p0022 p0024 p0027
  have p0029 := @gSnex (.cv y)
  have p0030 :=
    @gOtelins2 (synCsn (.cv p)) (synCsn (.cv y)) (synCop (synCsn (.cv x)) (.cv r))
      (synCins2 (synCsset)) p0029
  have p0031 := @gOtelins2 (synCsn (.cv p)) (synCsn (.cv x)) (.cv r) (synCsset) p0013
  have p0032 := @gOpelssetsn (.cv p) (.cv r) p0023 p0001
  have p0033_e02_recanon :
    Nominal.NPrf
      (synWb (.classMem (synCop (synCsn (.cv p)) (.cv r)) (synCsset)) (.objMem p r)) :=
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
      p0032
  have p0033 :=
    @gN3bitri
      (.classMem (synCop (synCsn (.cv p))
          (synCop (synCsn (.cv y)) (synCop (synCsn (.cv x)) (.cv r))))
        (synCins2 (synCins2 (synCsset))))
      (.classMem (synCop (synCsn (.cv p)) (synCop (synCsn (.cv x)) (.cv r)))
        (synCins2 (synCsset)))
      (.classMem (synCop (synCsn (.cv p)) (.cv r)) (synCsset)) (.objMem p r) p0030
      p0031 p0033_e02_recanon
  have p0034 :=
    @gAnbi12i
      (.classMem (synCop (synCsn (.cv p))
          (synCop (synCsn (.cv y)) (synCop (synCsn (.cv x)) (.cv r))))
        (synCins4 (synCsi3 (synCswap))))
      (.classEq (.cv p) (synCop (.cv x) (.cv y)))
      (.classMem (synCop (synCsn (.cv p))
          (synCop (synCsn (.cv y)) (synCop (synCsn (.cv x)) (.cv r))))
        (synCins2 (synCins2 (synCsset))))
      (.objMem p r) p0028 p0033
  have p0035 :=
    @gBitri
      (.classMem (synCop (synCsn (.cv p))
          (synCop (synCsn (.cv y)) (synCop (synCsn (.cv x)) (.cv r))))
        (synCin (synCins4 (synCsi3 (synCswap))) (synCins2 (synCins2 (synCsset)))))
      (synWa (.classMem (synCop (synCsn (.cv p))
            (synCop (synCsn (.cv y)) (synCop (synCsn (.cv x)) (.cv r))))
          (synCins4 (synCsi3 (synCswap)))) (.classMem (synCop (synCsn (.cv p))
            (synCop (synCsn (.cv y)) (synCop (synCsn (.cv x)) (.cv r))))
          (synCins2 (synCins2 (synCsset)))))
      (synWa (.classEq (.cv p) (synCop (.cv x) (.cv y))) (.objMem p r)) p0021 p0034
  have p0036 :=
    @gExbii
      (.classMem (synCop (synCsn (.cv p))
          (synCop (synCsn (.cv y)) (synCop (synCsn (.cv x)) (.cv r))))
        (synCin (synCins4 (synCsi3 (synCswap))) (synCins2 (synCins2 (synCsset)))))
      (synWa (.classEq (.cv p) (synCop (.cv x) (.cv y))) (.objMem p r)) p p0035
  have p0037 :=
    @gElima1c p (synCop (synCsn (.cv y)) (synCop (synCsn (.cv x)) (.cv r)))
      (synCin (synCins4 (synCsi3 (synCswap))) (synCins2 (synCins2 (synCsset))))
      dv_cache_0011 dv_cache_0012
  have p0038 := (Nominal.biimpRefl (synWbr (.cv x) (.cv r) (.cv y)))
  have p0039 :=
    (NFChoice.DirectNominalPrf.Nominal.DefinitionLeafHandlersCanonical001.dfClelOfDV p
      (synCop (.cv x) (.cv y)) (.cv r) dv_cache_0013 dv_cache_0014)
  have p0040_e01_recanon :
    Nominal.NPrf
      (synWb (.classMem (synCop (.cv x) (.cv y)) (.cv r)) (synWex p
          (synWa (.classEq (.cv p) (synCop (.cv x) (.cv y))) (.objMem p r)))) :=
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
      p0039
  have p0040 :=
    @gBitri (synWbr (.cv x) (.cv r) (.cv y))
      (.classMem (synCop (.cv x) (.cv y)) (.cv r))
      (synWex p (synWa (.classEq (.cv p) (synCop (.cv x) (.cv y))) (.objMem p r)))
      p0038 p0040_e01_recanon
  have p0041 :=
    @gN3bitr4i
      (synWex p (.classMem (synCop (synCsn (.cv p))
            (synCop (synCsn (.cv y)) (synCop (synCsn (.cv x)) (.cv r))))
          (synCin (synCins4 (synCsi3 (synCswap))) (synCins2 (synCins2 (synCsset))))))
      (synWex p (synWa (.classEq (.cv p) (synCop (.cv x) (.cv y))) (.objMem p r)))
      (.classMem (synCop (synCsn (.cv y)) (synCop (synCsn (.cv x)) (.cv r))) (synCima
          (synCin (synCins4 (synCsi3 (synCswap))) (synCins2 (synCins2 (synCsset))))
          (synC1c)))
      (synWbr (.cv x) (.cv r) (.cv y)) p0036 p0037 p0040
  have p0042 :=
    @gElin
      (synCop (synCsn (.cv p))
        (synCop (synCsn (.cv y)) (synCop (synCsn (.cv x)) (.cv r))))
      (synCins4 (synCsi3 (synCid))) (synCins2 (synCins2 (synCsset)))
  have p0043 :=
    @gOqelins4 (synCsn (.cv p)) (synCsn (.cv y)) (synCsn (.cv x)) (.cv r)
      (synCsi3 (synCid)) p0001
  have p0044 := @gOtsnelsi3 (.cv p) (.cv y) (.cv x) (synCid) p0023 p0016 p0008
  have p0045 := (Nominal.biimpRefl (synWbr (.cv p) (synCid) (synCop (.cv y) (.cv x))))
  have p0046 := @gOpex (.cv y) (.cv x) p0016 p0008
  have p0047 := @gIdeq (.cv p) (synCop (.cv y) (.cv x)) p0046
  have p0048 :=
    @gBitr3i (.classMem (synCop (.cv p) (synCop (.cv y) (.cv x))) (synCid))
      (synWbr (.cv p) (synCid) (synCop (.cv y) (.cv x)))
      (.classEq (.cv p) (synCop (.cv y) (.cv x))) p0045 p0047
  have p0049 :=
    @gN3bitri
      (.classMem (synCop (synCsn (.cv p))
          (synCop (synCsn (.cv y)) (synCop (synCsn (.cv x)) (.cv r))))
        (synCins4 (synCsi3 (synCid))))
      (.classMem (synCop (synCsn (.cv p)) (synCop (synCsn (.cv y)) (synCsn (.cv x))))
        (synCsi3 (synCid)))
      (.classMem (synCop (.cv p) (synCop (.cv y) (.cv x))) (synCid))
      (.classEq (.cv p) (synCop (.cv y) (.cv x))) p0043 p0044 p0048
  have p0050 :=
    @gAnbi12i
      (.classMem (synCop (synCsn (.cv p))
          (synCop (synCsn (.cv y)) (synCop (synCsn (.cv x)) (.cv r))))
        (synCins4 (synCsi3 (synCid))))
      (.classEq (.cv p) (synCop (.cv y) (.cv x)))
      (.classMem (synCop (synCsn (.cv p))
          (synCop (synCsn (.cv y)) (synCop (synCsn (.cv x)) (.cv r))))
        (synCins2 (synCins2 (synCsset))))
      (.objMem p r) p0049 p0033
  have p0051 :=
    @gBitri
      (.classMem (synCop (synCsn (.cv p))
          (synCop (synCsn (.cv y)) (synCop (synCsn (.cv x)) (.cv r))))
        (synCin (synCins4 (synCsi3 (synCid))) (synCins2 (synCins2 (synCsset)))))
      (synWa (.classMem (synCop (synCsn (.cv p))
            (synCop (synCsn (.cv y)) (synCop (synCsn (.cv x)) (.cv r))))
          (synCins4 (synCsi3 (synCid)))) (.classMem (synCop (synCsn (.cv p))
            (synCop (synCsn (.cv y)) (synCop (synCsn (.cv x)) (.cv r))))
          (synCins2 (synCins2 (synCsset)))))
      (synWa (.classEq (.cv p) (synCop (.cv y) (.cv x))) (.objMem p r)) p0042 p0050
  have p0052 :=
    @gExbii
      (.classMem (synCop (synCsn (.cv p))
          (synCop (synCsn (.cv y)) (synCop (synCsn (.cv x)) (.cv r))))
        (synCin (synCins4 (synCsi3 (synCid))) (synCins2 (synCins2 (synCsset)))))
      (synWa (.classEq (.cv p) (synCop (.cv y) (.cv x))) (.objMem p r)) p p0051
  have p0053 :=
    @gElima1c p (synCop (synCsn (.cv y)) (synCop (synCsn (.cv x)) (.cv r)))
      (synCin (synCins4 (synCsi3 (synCid))) (synCins2 (synCins2 (synCsset))))
      dv_cache_0011 dv_cache_0015
  have p0054 := (Nominal.biimpRefl (synWbr (.cv y) (.cv r) (.cv x)))
  have p0055 :=
    (NFChoice.DirectNominalPrf.Nominal.DefinitionLeafHandlersCanonical001.dfClelOfDV p
      (synCop (.cv y) (.cv x)) (.cv r) dv_cache_0016 dv_cache_0014)
  have p0056_e01_recanon :
    Nominal.NPrf
      (synWb (.classMem (synCop (.cv y) (.cv x)) (.cv r)) (synWex p
          (synWa (.classEq (.cv p) (synCop (.cv y) (.cv x))) (.objMem p r)))) :=
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
      p0055
  have p0056 :=
    @gBitri (synWbr (.cv y) (.cv r) (.cv x))
      (.classMem (synCop (.cv y) (.cv x)) (.cv r))
      (synWex p (synWa (.classEq (.cv p) (synCop (.cv y) (.cv x))) (.objMem p r)))
      p0054 p0056_e01_recanon
  have p0057 :=
    @gN3bitr4i
      (synWex p (.classMem (synCop (synCsn (.cv p))
            (synCop (synCsn (.cv y)) (synCop (synCsn (.cv x)) (.cv r))))
          (synCin (synCins4 (synCsi3 (synCid))) (synCins2 (synCins2 (synCsset))))))
      (synWex p (synWa (.classEq (.cv p) (synCop (.cv y) (.cv x))) (.objMem p r)))
      (.classMem (synCop (synCsn (.cv y)) (synCop (synCsn (.cv x)) (.cv r))) (synCima
          (synCin (synCins4 (synCsi3 (synCid))) (synCins2 (synCins2 (synCsset))))
          (synC1c)))
      (synWbr (.cv y) (.cv r) (.cv x)) p0052 p0053 p0056
  have p0058 :=
    @gOrbi12i
      (.classMem (synCop (synCsn (.cv y)) (synCop (synCsn (.cv x)) (.cv r))) (synCima
          (synCin (synCins4 (synCsi3 (synCswap))) (synCins2 (synCins2 (synCsset))))
          (synC1c)))
      (synWbr (.cv x) (.cv r) (.cv y))
      (.classMem (synCop (synCsn (.cv y)) (synCop (synCsn (.cv x)) (.cv r))) (synCima
          (synCin (synCins4 (synCsi3 (synCid))) (synCins2 (synCins2 (synCsset))))
          (synC1c)))
      (synWbr (.cv y) (.cv r) (.cv x)) p0041 p0057
  have p0059 :=
    @gN3bitri
      (.classMem
        (synCop (synCsn (.cv y)) (synCop (synCsn (.cv x)) (synCop (.cv r) (.cv a))))
        (synCins4 (synCun (synCima (synCin (synCins4 (synCsi3 (synCswap)))
                (synCins2 (synCins2 (synCsset)))) (synC1c)) (synCima
              (synCin (synCins4 (synCsi3 (synCid))) (synCins2 (synCins2 (synCsset))))
              (synC1c)))))
      (.classMem (synCop (synCsn (.cv y)) (synCop (synCsn (.cv x)) (.cv r))) (synCun
          (synCima (synCin (synCins4 (synCsi3 (synCswap)))
              (synCins2 (synCins2 (synCsset)))) (synC1c)) (synCima
            (synCin (synCins4 (synCsi3 (synCid))) (synCins2 (synCins2 (synCsset))))
            (synC1c))))
      (synWo (.classMem (synCop (synCsn (.cv y)) (synCop (synCsn (.cv x)) (.cv r)))
          (synCima (synCin (synCins4 (synCsi3 (synCswap)))
              (synCins2 (synCins2 (synCsset)))) (synC1c)))
        (.classMem (synCop (synCsn (.cv y)) (synCop (synCsn (.cv x)) (.cv r))) (synCima
            (synCin (synCins4 (synCsi3 (synCid))) (synCins2 (synCins2 (synCsset))))
            (synC1c))))
      (synWo (synWbr (.cv x) (.cv r) (.cv y)) (synWbr (.cv y) (.cv r) (.cv x))) p0019
      p0020 p0058
  have p0060 :=
    @gNotbii
      (.classMem
        (synCop (synCsn (.cv y)) (synCop (synCsn (.cv x)) (synCop (.cv r) (.cv a))))
        (synCins4 (synCun (synCima (synCin (synCins4 (synCsi3 (synCswap)))
                (synCins2 (synCins2 (synCsset)))) (synC1c)) (synCima
              (synCin (synCins4 (synCsi3 (synCid))) (synCins2 (synCins2 (synCsset))))
              (synC1c)))))
      (synWo (synWbr (.cv x) (.cv r) (.cv y)) (synWbr (.cv y) (.cv r) (.cv x))) p0059
  have p0061 :=
    @gAnbi12i
      (.classMem
        (synCop (synCsn (.cv y)) (synCop (synCsn (.cv x)) (synCop (.cv r) (.cv a))))
        (synCins2 (synCins2 (synCsset))))
      (.objMem y a)
      (.neg (.classMem (synCop (synCsn (.cv y))
            (synCop (synCsn (.cv x)) (synCop (.cv r) (.cv a)))) (synCins4 (synCun (synCima
                (synCin (synCins4 (synCsi3 (synCswap))) (synCins2 (synCins2 (synCsset))))
                (synC1c)) (synCima (synCin (synCins4 (synCsi3 (synCid)))
                  (synCins2 (synCins2 (synCsset)))) (synC1c))))))
      (.neg (synWo (synWbr (.cv x) (.cv r) (.cv y)) (synWbr (.cv y) (.cv r) (.cv x))))
      p0018 p0060
  have p0062 :=
    @gBitri
      (.classMem
        (synCop (synCsn (.cv y)) (synCop (synCsn (.cv x)) (synCop (.cv r) (.cv a))))
        (synCdif (synCins2 (synCins2 (synCsset))) (synCins4 (synCun (synCima
                (synCin (synCins4 (synCsi3 (synCswap))) (synCins2 (synCins2 (synCsset))))
                (synC1c)) (synCima (synCin (synCins4 (synCsi3 (synCid)))
                  (synCins2 (synCins2 (synCsset)))) (synC1c))))))
      (synWa (.classMem (synCop (synCsn (.cv y))
            (synCop (synCsn (.cv x)) (synCop (.cv r) (.cv a))))
          (synCins2 (synCins2 (synCsset)))) (.neg (.classMem (synCop (synCsn (.cv y))
              (synCop (synCsn (.cv x)) (synCop (.cv r) (.cv a)))) (synCins4 (synCun
                (synCima (synCin (synCins4 (synCsi3 (synCswap)))
                    (synCins2 (synCins2 (synCsset)))) (synC1c)) (synCima
                  (synCin (synCins4 (synCsi3 (synCid))) (synCins2 (synCins2 (synCsset))))
                  (synC1c)))))))
      (synWa (.objMem y a) (.neg
          (synWo (synWbr (.cv x) (.cv r) (.cv y)) (synWbr (.cv y) (.cv r) (.cv x)))))
      p0012 p0061
  have p0063 :=
    @gExbii
      (.classMem
        (synCop (synCsn (.cv y)) (synCop (synCsn (.cv x)) (synCop (.cv r) (.cv a))))
        (synCdif (synCins2 (synCins2 (synCsset))) (synCins4 (synCun (synCima
                (synCin (synCins4 (synCsi3 (synCswap))) (synCins2 (synCins2 (synCsset))))
                (synC1c)) (synCima (synCin (synCins4 (synCsi3 (synCid)))
                  (synCins2 (synCins2 (synCsset)))) (synC1c))))))
      (synWa (.objMem y a) (.neg
          (synWo (synWbr (.cv x) (.cv r) (.cv y)) (synWbr (.cv y) (.cv r) (.cv x)))))
      y p0062
  have p0064 :=
    @gBitri
      (.classMem (synCop (synCsn (.cv x)) (synCop (.cv r) (.cv a))) (synCima
          (synCdif (synCins2 (synCins2 (synCsset))) (synCins4 (synCun (synCima
                  (synCin (synCins4 (synCsi3 (synCswap)))
                    (synCins2 (synCins2 (synCsset)))) (synC1c)) (synCima
                  (synCin (synCins4 (synCsi3 (synCid))) (synCins2 (synCins2 (synCsset))))
                  (synC1c))))) (synC1c)))
      (synWex y (.classMem (synCop (synCsn (.cv y))
            (synCop (synCsn (.cv x)) (synCop (.cv r) (.cv a))))
          (synCdif (synCins2 (synCins2 (synCsset))) (synCins4 (synCun (synCima
                  (synCin (synCins4 (synCsi3 (synCswap)))
                    (synCins2 (synCins2 (synCsset)))) (synC1c)) (synCima
                  (synCin (synCins4 (synCsi3 (synCid))) (synCins2 (synCins2 (synCsset))))
                  (synC1c)))))))
      (synWex y (synWa (.objMem y a) (.neg (synWo (synWbr (.cv x) (.cv r) (.cv y))
              (synWbr (.cv y) (.cv r) (.cv x))))))
      p0011 p0063
  have p0065 :=
    (Nominal.biimpRefl (synWrex y (.cv a) (.neg
          (synWo (synWbr (.cv x) (.cv r) (.cv y)) (synWbr (.cv y) (.cv r) (.cv x))))))
  have p0066 :=
    @gRexnal (synWo (synWbr (.cv x) (.cv r) (.cv y)) (synWbr (.cv y) (.cv r) (.cv x)))
      y (.cv a)
  have p0067_e01_recanon :
    Nominal.NPrf
      (synWb (synWrex y (.cv a) (.neg
            (synWo (synWbr (.cv x) (.cv r) (.cv y)) (synWbr (.cv y) (.cv r) (.cv x)))))
        (synWex y (synWa (.objMem y a) (.neg (synWo (synWbr (.cv x) (.cv r) (.cv y))
                (synWbr (.cv y) (.cv r) (.cv x))))))) :=
    Nominal.RecanonTransportDev.transport
      (by
        simp only [synWb, synWrex, synWex, synWa, synWo, synWbr, synCop, synCun,
          synCnin, synWnan, synCcompl]
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
            · exact Nominal.RecanonTransportDev.TRecanonWff.same _
        · apply Nominal.RecanonTransportDev.TRecanonWff.neg
          apply Nominal.RecanonTransportDev.TRecanonWff.imp
          · apply Nominal.RecanonTransportDev.TRecanonWff.neg
            apply Nominal.RecanonTransportDev.TRecanonWff.all
            apply Nominal.RecanonTransportDev.TRecanonWff.neg
            apply Nominal.RecanonTransportDev.TRecanonWff.neg
            apply Nominal.RecanonTransportDev.TRecanonWff.imp
            · exact Nominal.RecanonTransportDev.TRecanonWff.classMem_objMem _ _
            · exact Nominal.RecanonTransportDev.TRecanonWff.same _
          · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0065
  have p0067 :=
    @gN3bitr2i
      (.classMem (synCop (synCsn (.cv x)) (synCop (.cv r) (.cv a))) (synCima
          (synCdif (synCins2 (synCins2 (synCsset))) (synCins4 (synCun (synCima
                  (synCin (synCins4 (synCsi3 (synCswap)))
                    (synCins2 (synCins2 (synCsset)))) (synC1c)) (synCima
                  (synCin (synCins4 (synCsi3 (synCid))) (synCins2 (synCins2 (synCsset))))
                  (synC1c))))) (synC1c)))
      (synWex y (synWa (.objMem y a) (.neg (synWo (synWbr (.cv x) (.cv r) (.cv y))
              (synWbr (.cv y) (.cv r) (.cv x))))))
      (synWrex y (.cv a) (.neg
          (synWo (synWbr (.cv x) (.cv r) (.cv y)) (synWbr (.cv y) (.cv r) (.cv x)))))
      (.neg (synWral y (.cv a)
          (synWo (synWbr (.cv x) (.cv r) (.cv y)) (synWbr (.cv y) (.cv r) (.cv x)))))
      p0064 p0067_e01_recanon p0066
  have p0068 :=
    @gAnbi12i
      (.classMem (synCop (synCsn (.cv x)) (synCop (.cv r) (.cv a))) (synCins2 (synCsset)))
      (.objMem x a)
      (.classMem (synCop (synCsn (.cv x)) (synCop (.cv r) (.cv a))) (synCima
          (synCdif (synCins2 (synCins2 (synCsset))) (synCins4 (synCun (synCima
                  (synCin (synCins4 (synCsi3 (synCswap)))
                    (synCins2 (synCins2 (synCsset)))) (synC1c)) (synCima
                  (synCin (synCins4 (synCsi3 (synCid))) (synCins2 (synCins2 (synCsset))))
                  (synC1c))))) (synC1c)))
      (.neg (synWral y (.cv a)
          (synWo (synWbr (.cv x) (.cv r) (.cv y)) (synWbr (.cv y) (.cv r) (.cv x)))))
      p0010 p0067
  have p0069 :=
    @gBitri
      (.classMem (synCop (synCsn (.cv x)) (synCop (.cv r) (.cv a)))
        (synCin (synCins2 (synCsset)) (synCima (synCdif (synCins2 (synCins2 (synCsset)))
              (synCins4 (synCun (synCima (synCin (synCins4 (synCsi3 (synCswap)))
                      (synCins2 (synCins2 (synCsset)))) (synC1c)) (synCima
                    (synCin (synCins4 (synCsi3 (synCid)))
                      (synCins2 (synCins2 (synCsset)))) (synC1c))))) (synC1c))))
      (synWa (.classMem (synCop (synCsn (.cv x)) (synCop (.cv r) (.cv a)))
          (synCins2 (synCsset)))
        (.classMem (synCop (synCsn (.cv x)) (synCop (.cv r) (.cv a))) (synCima
            (synCdif (synCins2 (synCins2 (synCsset))) (synCins4 (synCun (synCima
                    (synCin (synCins4 (synCsi3 (synCswap)))
                      (synCins2 (synCins2 (synCsset)))) (synC1c)) (synCima
                    (synCin (synCins4 (synCsi3 (synCid)))
                      (synCins2 (synCins2 (synCsset)))) (synC1c))))) (synC1c))))
      (synWa (.objMem x a) (.neg (synWral y (.cv a) (synWo (synWbr (.cv x) (.cv r) (.cv y))
              (synWbr (.cv y) (.cv r) (.cv x))))))
      p0006 p0068
  have p0070 :=
    @gExbii
      (.classMem (synCop (synCsn (.cv x)) (synCop (.cv r) (.cv a)))
        (synCin (synCins2 (synCsset)) (synCima (synCdif (synCins2 (synCins2 (synCsset)))
              (synCins4 (synCun (synCima (synCin (synCins4 (synCsi3 (synCswap)))
                      (synCins2 (synCins2 (synCsset)))) (synC1c)) (synCima
                    (synCin (synCins4 (synCsi3 (synCid)))
                      (synCins2 (synCins2 (synCsset)))) (synC1c))))) (synC1c))))
      (synWa (.objMem x a) (.neg (synWral y (.cv a) (synWo (synWbr (.cv x) (.cv r) (.cv y))
              (synWbr (.cv y) (.cv r) (.cv x))))))
      x p0069
  have p0071 :=
    @gBitri
      (.classMem (synCop (.cv r) (.cv a)) (synCima (synCin (synCins2 (synCsset)) (synCima
              (synCdif (synCins2 (synCins2 (synCsset))) (synCins4 (synCun (synCima
                      (synCin (synCins4 (synCsi3 (synCswap)))
                        (synCins2 (synCins2 (synCsset)))) (synC1c)) (synCima
                      (synCin (synCins4 (synCsi3 (synCid)))
                        (synCins2 (synCins2 (synCsset)))) (synC1c))))) (synC1c)))
          (synC1c)))
      (synWex x (.classMem (synCop (synCsn (.cv x)) (synCop (.cv r) (.cv a)))
          (synCin (synCins2 (synCsset)) (synCima
              (synCdif (synCins2 (synCins2 (synCsset))) (synCins4 (synCun (synCima
                      (synCin (synCins4 (synCsi3 (synCswap)))
                        (synCins2 (synCins2 (synCsset)))) (synC1c)) (synCima
                      (synCin (synCins4 (synCsi3 (synCid)))
                        (synCins2 (synCins2 (synCsset)))) (synC1c))))) (synC1c)))))
      (synWex x (synWa (.objMem x a) (.neg (synWral y (.cv a)
              (synWo (synWbr (.cv x) (.cv r) (.cv y)) (synWbr (.cv y) (.cv r) (.cv x)))))))
      p0005 p0070
  have p0072 :=
    (Nominal.biimpRefl (synWrex x (.cv a) (.neg (synWral y (.cv a)
            (synWo (synWbr (.cv x) (.cv r) (.cv y)) (synWbr (.cv y) (.cv r) (.cv x)))))))
  have p0073 :=
    @gRexnal
      (synWral y (.cv a)
        (synWo (synWbr (.cv x) (.cv r) (.cv y)) (synWbr (.cv y) (.cv r) (.cv x))))
      x (.cv a)
  have p0074_e01_recanon :
    Nominal.NPrf
      (synWb (synWrex x (.cv a) (.neg (synWral y (.cv a)
              (synWo (synWbr (.cv x) (.cv r) (.cv y)) (synWbr (.cv y) (.cv r) (.cv x))))))
        (synWex x (synWa (.objMem x a) (.neg (synWral y (.cv a)
                (synWo (synWbr (.cv x) (.cv r) (.cv y))
                  (synWbr (.cv y) (.cv r) (.cv x)))))))) :=
    Nominal.RecanonTransportDev.transport
      (by
        simp only [synWb, synWrex, synWex, synWa, synWral, synWo, synWbr, synCop,
          synCun, synCnin, synWnan, synCcompl]
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
            · exact Nominal.RecanonTransportDev.TRecanonWff.same _
        · apply Nominal.RecanonTransportDev.TRecanonWff.neg
          apply Nominal.RecanonTransportDev.TRecanonWff.imp
          · apply Nominal.RecanonTransportDev.TRecanonWff.neg
            apply Nominal.RecanonTransportDev.TRecanonWff.all
            apply Nominal.RecanonTransportDev.TRecanonWff.neg
            apply Nominal.RecanonTransportDev.TRecanonWff.neg
            apply Nominal.RecanonTransportDev.TRecanonWff.imp
            · exact Nominal.RecanonTransportDev.TRecanonWff.classMem_objMem _ _
            · exact Nominal.RecanonTransportDev.TRecanonWff.same _
          · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0072
  have p0074 :=
    @gN3bitr2i
      (.classMem (synCop (.cv r) (.cv a)) (synCima (synCin (synCins2 (synCsset)) (synCima
              (synCdif (synCins2 (synCins2 (synCsset))) (synCins4 (synCun (synCima
                      (synCin (synCins4 (synCsi3 (synCswap)))
                        (synCins2 (synCins2 (synCsset)))) (synC1c)) (synCima
                      (synCin (synCins4 (synCsi3 (synCid)))
                        (synCins2 (synCins2 (synCsset)))) (synC1c))))) (synC1c)))
          (synC1c)))
      (synWex x (synWa (.objMem x a) (.neg (synWral y (.cv a)
              (synWo (synWbr (.cv x) (.cv r) (.cv y)) (synWbr (.cv y) (.cv r) (.cv x)))))))
      (synWrex x (.cv a) (.neg (synWral y (.cv a) (synWo (synWbr (.cv x) (.cv r) (.cv y))
              (synWbr (.cv y) (.cv r) (.cv x))))))
      (.neg (synWral x (.cv a) (synWral y (.cv a) (synWo (synWbr (.cv x) (.cv r) (.cv y))
              (synWbr (.cv y) (.cv r) (.cv x))))))
      p0071 p0074_e01_recanon p0073
  have p0075 :=
    @gCon2bii
      (.classMem (synCop (.cv r) (.cv a)) (synCima (synCin (synCins2 (synCsset)) (synCima
              (synCdif (synCins2 (synCins2 (synCsset))) (synCins4 (synCun (synCima
                      (synCin (synCins4 (synCsi3 (synCswap)))
                        (synCins2 (synCins2 (synCsset)))) (synC1c)) (synCima
                      (synCin (synCins4 (synCsi3 (synCid)))
                        (synCins2 (synCins2 (synCsset)))) (synC1c))))) (synC1c)))
          (synC1c)))
      (synWral x (.cv a) (synWral y (.cv a)
          (synWo (synWbr (.cv x) (.cv r) (.cv y)) (synWbr (.cv y) (.cv r) (.cv x)))))
      p0074
  have p0076 :=
    @gBitr4i
      (.classMem (synCop (.cv r) (.cv a)) (synCcompl (synCima
            (synCin (synCins2 (synCsset)) (synCima
                (synCdif (synCins2 (synCins2 (synCsset))) (synCins4 (synCun (synCima
                        (synCin (synCins4 (synCsi3 (synCswap)))
                          (synCins2 (synCins2 (synCsset)))) (synC1c)) (synCima
                        (synCin (synCins4 (synCsi3 (synCid)))
                          (synCins2 (synCins2 (synCsset)))) (synC1c))))) (synC1c)))
            (synC1c))))
      (.neg (.classMem (synCop (.cv r) (.cv a)) (synCima (synCin (synCins2 (synCsset))
              (synCima (synCdif (synCins2 (synCins2 (synCsset))) (synCins4 (synCun
                      (synCima (synCin (synCins4 (synCsi3 (synCswap)))
                          (synCins2 (synCins2 (synCsset)))) (synC1c)) (synCima
                        (synCin (synCins4 (synCsi3 (synCid)))
                          (synCins2 (synCins2 (synCsset)))) (synC1c))))) (synC1c)))
            (synC1c))))
      (synWral x (.cv a) (synWral y (.cv a)
          (synWo (synWbr (.cv x) (.cv r) (.cv y)) (synWbr (.cv y) (.cv r) (.cv x)))))
      p0004 p0075
  have p0077 :=
    @gOpabbi2i
      (synWral x (.cv a) (synWral y (.cv a)
          (synWo (synWbr (.cv x) (.cv r) (.cv y)) (synWbr (.cv y) (.cv r) (.cv x)))))
      r a
      (synCcompl (synCima (synCin (synCins2 (synCsset)) (synCima
              (synCdif (synCins2 (synCins2 (synCsset))) (synCins4 (synCun (synCima
                      (synCin (synCins4 (synCsi3 (synCswap)))
                        (synCins2 (synCins2 (synCsset)))) (synC1c)) (synCima
                      (synCin (synCins4 (synCsi3 (synCid)))
                        (synCins2 (synCins2 (synCsset)))) (synC1c))))) (synC1c)))
          (synC1c)))
      dv_cache_0017 dv_cache_0018 dv_cache_0019 p0076
  have p0078 :=
    @gEqtr4i (synCconnex)
      (synCopab r a (synWral x (.cv a) (synWral y (.cv a)
            (synWo (synWbr (.cv x) (.cv r) (.cv y)) (synWbr (.cv y) (.cv r) (.cv x))))))
      (synCcompl (synCima (synCin (synCins2 (synCsset)) (synCima
              (synCdif (synCins2 (synCins2 (synCsset))) (synCins4 (synCun (synCima
                      (synCin (synCins4 (synCsi3 (synCswap)))
                        (synCins2 (synCins2 (synCsset)))) (synC1c)) (synCima
                      (synCin (synCins4 (synCsi3 (synCid)))
                        (synCins2 (synCins2 (synCsset)))) (synC1c))))) (synC1c)))
          (synC1c)))
      p0000 p0077
  have p0079 := @gSsetex
  have p0080 := @gIns2ex (synCsset) p0079
  have p0081 := @gIns2ex (synCins2 (synCsset)) p0080
  have p0082 := @gSwapex
  have p0083 := @gSi3ex (synCswap) p0082
  have p0084 := @gIns4ex (synCsi3 (synCswap)) p0083
  have p0085 :=
    @gInex (synCins4 (synCsi3 (synCswap))) (synCins2 (synCins2 (synCsset))) p0084
      p0081
  have p0086 := @gN1cex
  have p0087 :=
    @gImaex
      (synCin (synCins4 (synCsi3 (synCswap))) (synCins2 (synCins2 (synCsset))))
      (synC1c) p0085 p0086
  have p0088 := @gIdex
  have p0089 := @gSi3ex (synCid) p0088
  have p0090 := @gIns4ex (synCsi3 (synCid)) p0089
  have p0091 :=
    @gInex (synCins4 (synCsi3 (synCid))) (synCins2 (synCins2 (synCsset))) p0090
      p0081
  have p0093 :=
    @gImaex
      (synCin (synCins4 (synCsi3 (synCid))) (synCins2 (synCins2 (synCsset))))
      (synC1c) p0091 p0086
  have p0094 :=
    @gUnex
      (synCima (synCin (synCins4 (synCsi3 (synCswap))) (synCins2 (synCins2 (synCsset))))
        (synC1c))
      (synCima (synCin (synCins4 (synCsi3 (synCid))) (synCins2 (synCins2 (synCsset))))
        (synC1c))
      p0087 p0093
  have p0095 :=
    @gIns4ex
      (synCun (synCima
          (synCin (synCins4 (synCsi3 (synCswap))) (synCins2 (synCins2 (synCsset))))
          (synC1c)) (synCima
          (synCin (synCins4 (synCsi3 (synCid))) (synCins2 (synCins2 (synCsset))))
          (synC1c)))
      p0094
  have p0096 :=
    @gDifex (synCins2 (synCins2 (synCsset)))
      (synCins4 (synCun (synCima (synCin (synCins4 (synCsi3 (synCswap)))
              (synCins2 (synCins2 (synCsset)))) (synC1c)) (synCima
            (synCin (synCins4 (synCsi3 (synCid))) (synCins2 (synCins2 (synCsset))))
            (synC1c))))
      p0081 p0095
  have p0098 :=
    @gImaex
      (synCdif (synCins2 (synCins2 (synCsset))) (synCins4 (synCun (synCima
              (synCin (synCins4 (synCsi3 (synCswap))) (synCins2 (synCins2 (synCsset))))
              (synC1c)) (synCima (synCin (synCins4 (synCsi3 (synCid)))
                (synCins2 (synCins2 (synCsset)))) (synC1c)))))
      (synC1c) p0096 p0086
  have p0099 :=
    @gInex (synCins2 (synCsset))
      (synCima (synCdif (synCins2 (synCins2 (synCsset))) (synCins4 (synCun (synCima
                (synCin (synCins4 (synCsi3 (synCswap))) (synCins2 (synCins2 (synCsset))))
                (synC1c)) (synCima (synCin (synCins4 (synCsi3 (synCid)))
                  (synCins2 (synCins2 (synCsset)))) (synC1c))))) (synC1c))
      p0080 p0098
  have p0101 :=
    @gImaex
      (synCin (synCins2 (synCsset)) (synCima (synCdif (synCins2 (synCins2 (synCsset)))
            (synCins4 (synCun (synCima (synCin (synCins4 (synCsi3 (synCswap)))
                    (synCins2 (synCins2 (synCsset)))) (synC1c)) (synCima
                  (synCin (synCins4 (synCsi3 (synCid))) (synCins2 (synCins2 (synCsset))))
                  (synC1c))))) (synC1c)))
      (synC1c) p0099 p0086
  have p0102 :=
    @gComplex
      (synCima (synCin (synCins2 (synCsset)) (synCima
            (synCdif (synCins2 (synCins2 (synCsset))) (synCins4 (synCun (synCima
                    (synCin (synCins4 (synCsi3 (synCswap)))
                      (synCins2 (synCins2 (synCsset)))) (synC1c)) (synCima
                    (synCin (synCins4 (synCsi3 (synCid)))
                      (synCins2 (synCins2 (synCsset)))) (synC1c))))) (synC1c))) (synC1c))
      p0101
  have p0103 :=
    @gEqeltri (synCconnex)
      (synCcompl (synCima (synCin (synCins2 (synCsset)) (synCima
              (synCdif (synCins2 (synCins2 (synCsset))) (synCins4 (synCun (synCima
                      (synCin (synCins4 (synCsi3 (synCswap)))
                        (synCins2 (synCins2 (synCsset)))) (synC1c)) (synCima
                      (synCin (synCins4 (synCsi3 (synCid)))
                        (synCins2 (synCins2 (synCsset)))) (synC1c))))) (synC1c)))
          (synC1c)))
      (synCvv) p0078 p0102
  exact p0103


end NFChoice.DirectNominalPrf.WPPReplay

end

/-! Certificates from `NominalWPPReplayChunk013Compact001Part022`. -/


section

namespace NFChoice.DirectNominalPrf.WPPReplay

open scoped Fol
open NFChoice.Foundation
open NFChoice.SemanticCore
open NFChoice.ReplaySupport
open NFChoice.Compiler.CompactSourceSyntax

/-- Checked nominal proof certificate identified upstream as `g_foundex`. -/
@[expose]
noncomputable def gFoundex : Nominal.NPrf (.classMem (synCfound) (synCvv)) :=
  by
  let proofSupport : Finset Var := (∅ : Finset Var)
  let x : Var := freshVar proofSupport 0
  let a : Var := freshVar proofSupport 1
  let y : Var := freshVar proofSupport 2
  let z : Var := freshVar proofSupport 3
  let r : Var := freshVar proofSupport 4
  let t : Var := freshVar proofSupport 5
  have fresh_x_ne_a : x ≠ a :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have fresh_a_ne_x : a ≠ x := Ne.symm fresh_x_ne_a
  have fresh_x_ne_y : x ≠ y :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 2
    exact freshVar_injective proofSupport (i := 0) (j := 2) (by decide)
  have fresh_y_ne_x : y ≠ x := Ne.symm fresh_x_ne_y
  have fresh_x_ne_z : x ≠ z :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 3
    exact freshVar_injective proofSupport (i := 0) (j := 3) (by decide)
  have fresh_z_ne_x : z ≠ x := Ne.symm fresh_x_ne_z
  have fresh_x_ne_r : x ≠ r :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 4
    exact freshVar_injective proofSupport (i := 0) (j := 4) (by decide)
  have fresh_r_ne_x : r ≠ x := Ne.symm fresh_x_ne_r
  have fresh_x_ne_t : x ≠ t :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 5
    exact freshVar_injective proofSupport (i := 0) (j := 5) (by decide)
  have fresh_t_ne_x : t ≠ x := Ne.symm fresh_x_ne_t
  have fresh_a_ne_y : a ≠ y :=
    by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 2
    exact freshVar_injective proofSupport (i := 1) (j := 2) (by decide)
  have fresh_a_ne_z : a ≠ z :=
    by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 3
    exact freshVar_injective proofSupport (i := 1) (j := 3) (by decide)
  have fresh_a_ne_r : a ≠ r :=
    by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 4
    exact freshVar_injective proofSupport (i := 1) (j := 4) (by decide)
  have fresh_r_ne_a : r ≠ a := Ne.symm fresh_a_ne_r
  have fresh_y_ne_z : y ≠ z :=
    by
    change freshVar proofSupport 2 ≠ freshVar proofSupport 3
    exact freshVar_injective proofSupport (i := 2) (j := 3) (by decide)
  have fresh_y_ne_r : y ≠ r :=
    by
    change freshVar proofSupport 2 ≠ freshVar proofSupport 4
    exact freshVar_injective proofSupport (i := 2) (j := 4) (by decide)
  have fresh_r_ne_y : r ≠ y := Ne.symm fresh_y_ne_r
  have fresh_y_ne_t : y ≠ t :=
    by
    change freshVar proofSupport 2 ≠ freshVar proofSupport 5
    exact freshVar_injective proofSupport (i := 2) (j := 5) (by decide)
  have fresh_t_ne_y : t ≠ y := Ne.symm fresh_y_ne_t
  have fresh_z_ne_r : z ≠ r :=
    by
    change freshVar proofSupport 3 ≠ freshVar proofSupport 4
    exact freshVar_injective proofSupport (i := 3) (j := 4) (by decide)
  have fresh_r_ne_z : r ≠ z := Ne.symm fresh_z_ne_r
  have fresh_z_ne_t : z ≠ t :=
    by
    change freshVar proofSupport 3 ≠ freshVar proofSupport 5
    exact freshVar_injective proofSupport (i := 3) (j := 5) (by decide)
  have fresh_t_ne_z : t ≠ z := Ne.symm fresh_z_ne_t
  have fresh_r_ne_t : r ≠ t :=
    by
    change freshVar proofSupport 4 ≠ freshVar proofSupport 5
    exact freshVar_injective proofSupport (i := 4) (j := 5) (by decide)
  have fresh_t_ne_r : t ≠ r := Ne.symm fresh_r_ne_t
  have dv_cache_0001 : a ≠ r := by exact (show a ≠ r from (by exact fresh_a_ne_r))
  have dv_cache_0002 : a ≠ x := by
    clear dv_cache_0001
    exact (show a ≠ x from (by exact fresh_a_ne_x))
  have dv_cache_0003 : a ≠ y :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact (show a ≠ y from (by exact fresh_a_ne_y))
  have dv_cache_0004 : a ≠ z :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact (show a ≠ z from (by exact fresh_a_ne_z))
  have dv_cache_0005 : r ≠ x :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact (show r ≠ x from (by exact fresh_r_ne_x))
  have dv_cache_0006 : r ≠ y :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact (show r ≠ y from (by exact fresh_r_ne_y))
  have dv_cache_0007 : r ≠ z :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006
    exact (show r ≠ z from (by exact fresh_r_ne_z))
  have dv_cache_0008 : x ≠ y :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007
    exact (show x ≠ y from (by exact fresh_x_ne_y))
  have dv_cache_0009 : x ≠ z :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008
    exact (show x ≠ z from (by exact fresh_x_ne_z))
  have dv_cache_0010 : y ≠ z :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009
    exact (show y ≠ z from (by exact fresh_y_ne_z))
  have dv_cache_0011 : x ∉ ((synCop (.cv r) (.cv a))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cop,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, fresh_x_ne_r, fresh_x_ne_a, or_false, not_false_eq_true])
  have dv_cache_0012 :
    x ∉
      ((synCtxp (synCcompl (synCima (synCin (synCins3 (synCsset)) (synCcompl (synCima
                    (synCin (synCins2 (synCins3 (synCsset))) (synCdif (synCima
                          (synCin (synCins4 (synCsi3 (synCid)))
                            (synCins2 (synCins2 (synCins2 (synCsset))))) (synC1c))
                        (synCins3 (synCid)))) (synC1c)))) (synC1c))) (synCin (synCsset)
            (synCxp (synCcompl (synCsn (synC0))) (synCvv))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ctxp,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccompl,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cima,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins3,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csset,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins2,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdif,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins4,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csi3,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cid,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxp,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv, Finset.mem_union,
          compact_fv_not_mem_empty, or_false, not_false_eq_true])
  have dv_cache_0013 :
    t ∉
      ((synCop (synCsn (.cv y)) (synCop (synCsn (.cv z)) (synCop (.cv x) (.cv r))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012
    exact
      (by
        have compact_fv_not_mem_empty : t ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cop,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, fresh_t_ne_y, fresh_t_ne_z, fresh_t_ne_x, fresh_t_ne_r,
          or_false, not_false_eq_true])
  have dv_cache_0014 :
    t ∉
      ((synCin (synCins4 (synCsi3 (synCid)))
          (synCins2 (synCins2 (synCins2 (synCsset)))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013
    exact
      (by
        have compact_fv_not_mem_empty : t ∉ (∅ : Finset Var) :=
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
  have dv_cache_0015 : t ∉ ((synCop (.cv y) (.cv z))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014
    exact
      (by
        have compact_fv_not_mem_empty : t ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cop,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, fresh_t_ne_y, fresh_t_ne_z, or_false, not_false_eq_true])
  have dv_cache_0016 : t ∉ ((Class.cv r)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015
    exact
      (by
        have compact_fv_not_mem_empty : t ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_t_ne_r, not_false_eq_true])
  have dv_cache_0017 : y ∉ ((synCop (synCsn (.cv z)) (synCop (.cv x) (.cv r)))).fv :=
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
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cop,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, fresh_y_ne_z, fresh_y_ne_x, fresh_y_ne_r, or_false,
          not_false_eq_true])
  have dv_cache_0018 :
    y ∉
      ((synCin (synCins2 (synCins3 (synCsset))) (synCdif (synCima
              (synCin (synCins4 (synCsi3 (synCid)))
                (synCins2 (synCins2 (synCins2 (synCsset))))) (synC1c))
            (synCins3 (synCid))))).fv :=
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
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins2,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins3,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csset,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdif,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cima,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins4,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csi3,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cid,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c, Finset.mem_union,
          compact_fv_not_mem_empty, or_false, not_false_eq_true])
  have dv_cache_0019 : z ∉ ((synCop (.cv x) (.cv r))).fv :=
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
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cop,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, fresh_z_ne_x, fresh_z_ne_r, or_false, not_false_eq_true])
  have dv_cache_0020 :
    z ∉
      ((synCin (synCins3 (synCsset)) (synCcompl (synCima
              (synCin (synCins2 (synCins3 (synCsset))) (synCdif (synCima
                    (synCin (synCins4 (synCsi3 (synCid)))
                      (synCins2 (synCins2 (synCins2 (synCsset))))) (synC1c))
                  (synCins3 (synCid)))) (synC1c))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019
    exact
      (by
        have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins3,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csset,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccompl,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cima,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins2,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdif,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins4,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csi3,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cid,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c, Finset.mem_union,
          compact_fv_not_mem_empty, or_false, not_false_eq_true])
  have dv_cache_0021 : x ∉ ((synC0)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0,
          compact_fv_not_mem_empty, not_false_eq_true])
  have dv_cache_0022 :
    r ∉
      ((synCcompl (synCrn (synCtxp (synCcompl (synCima (synCin (synCins3 (synCsset))
                    (synCcompl (synCima (synCin (synCins2 (synCins3 (synCsset))) (synCdif
                            (synCima (synCin (synCins4 (synCsi3 (synCid)))
                                (synCins2 (synCins2 (synCins2 (synCsset))))) (synC1c))
                            (synCins3 (synCid)))) (synC1c)))) (synC1c)))
              (synCin (synCsset)
                (synCxp (synCcompl (synCsn (synC0))) (synCvv))))))).fv :=
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
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccompl,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_crn,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ctxp,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cima,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins3,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csset,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins2,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdif,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins4,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csi3,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cid,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxp,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv, Finset.mem_union,
          compact_fv_not_mem_empty, or_false, not_false_eq_true])
  have dv_cache_0023 :
    a ∉
      ((synCcompl (synCrn (synCtxp (synCcompl (synCima (synCin (synCins3 (synCsset))
                    (synCcompl (synCima (synCin (synCins2 (synCins3 (synCsset))) (synCdif
                            (synCima (synCin (synCins4 (synCsi3 (synCid)))
                                (synCins2 (synCins2 (synCins2 (synCsset))))) (synC1c))
                            (synCins3 (synCid)))) (synC1c)))) (synC1c)))
              (synCin (synCsset)
                (synCxp (synCcompl (synCsn (synC0))) (synCvv))))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022
    exact
      (by
        have compact_fv_not_mem_empty : a ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccompl,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_crn,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ctxp,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cima,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins3,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csset,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins2,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdif,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins4,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csi3,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cid,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxp,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv, Finset.mem_union,
          compact_fv_not_mem_empty, or_false, not_false_eq_true])
  have dv_cache_0024 : r ≠ a :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
    exact (show r ≠ a from (by exact fresh_r_ne_a))
  have p0000 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominalDfFound x y z r a
      dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006
      dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010
  have p0001 := @gVex r
  have p0002 := @gVex a
  have p0003 := @gOpex (.cv r) (.cv a) p0001 p0002
  have p0004 :=
    @gElcompl (synCop (.cv r) (.cv a))
      (synCrn (synCtxp (synCcompl (synCima (synCin (synCins3 (synCsset)) (synCcompl
                  (synCima (synCin (synCins2 (synCins3 (synCsset))) (synCdif (synCima
                          (synCin (synCins4 (synCsi3 (synCid)))
                            (synCins2 (synCins2 (synCins2 (synCsset))))) (synC1c))
                        (synCins3 (synCid)))) (synC1c)))) (synC1c)))
          (synCin (synCsset) (synCxp (synCcompl (synCsn (synC0))) (synCvv)))))
      p0003
  have p0005 :=
    @gElrn2 x (synCop (.cv r) (.cv a))
      (synCtxp (synCcompl (synCima (synCin (synCins3 (synCsset)) (synCcompl (synCima
                  (synCin (synCins2 (synCins3 (synCsset))) (synCdif (synCima
                        (synCin (synCins4 (synCsi3 (synCid)))
                          (synCins2 (synCins2 (synCins2 (synCsset))))) (synC1c))
                      (synCins3 (synCid)))) (synC1c)))) (synC1c)))
        (synCin (synCsset) (synCxp (synCcompl (synCsn (synC0))) (synCvv))))
      dv_cache_0011 dv_cache_0012
  have p0006 :=
    @gOteltxp (.cv x) (.cv r) (.cv a)
      (synCcompl (synCima (synCin (synCins3 (synCsset)) (synCcompl (synCima
                (synCin (synCins2 (synCins3 (synCsset))) (synCdif (synCima
                      (synCin (synCins4 (synCsi3 (synCid)))
                        (synCins2 (synCins2 (synCins2 (synCsset))))) (synC1c))
                    (synCins3 (synCid)))) (synC1c)))) (synC1c)))
      (synCin (synCsset) (synCxp (synCcompl (synCsn (synC0))) (synCvv)))
  have p0007 := @gVex x
  have p0008 := @gOpex (.cv x) (.cv r) p0007 p0001
  have p0009 :=
    @gElcompl (synCop (.cv x) (.cv r))
      (synCima (synCin (synCins3 (synCsset)) (synCcompl (synCima
              (synCin (synCins2 (synCins3 (synCsset))) (synCdif (synCima
                    (synCin (synCins4 (synCsi3 (synCid)))
                      (synCins2 (synCins2 (synCins2 (synCsset))))) (synC1c))
                  (synCins3 (synCid)))) (synC1c)))) (synC1c))
      p0008
  have p0010 :=
    @gElin (synCop (synCsn (.cv z)) (synCop (.cv x) (.cv r))) (synCins3 (synCsset))
      (synCcompl (synCima (synCin (synCins2 (synCins3 (synCsset))) (synCdif (synCima
                (synCin (synCins4 (synCsi3 (synCid)))
                  (synCins2 (synCins2 (synCins2 (synCsset))))) (synC1c))
              (synCins3 (synCid)))) (synC1c)))
  have p0011 := @gOtelins3 (synCsn (.cv z)) (.cv x) (.cv r) (synCsset) p0001
  have p0012 := @gVex z
  have p0013 := @gOpelssetsn (.cv z) (.cv x) p0012 p0007
  have p0014_e01_recanon :
    Nominal.NPrf
      (synWb (.classMem (synCop (synCsn (.cv z)) (.cv x)) (synCsset)) (.objMem z x)) :=
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
      p0013
  have p0014 :=
    @gBitri
      (.classMem (synCop (synCsn (.cv z)) (synCop (.cv x) (.cv r))) (synCins3 (synCsset)))
      (.classMem (synCop (synCsn (.cv z)) (.cv x)) (synCsset)) (.objMem z x) p0011
      p0014_e01_recanon
  have p0015 := @gSnex (.cv z)
  have p0016 := @gOpex (synCsn (.cv z)) (synCop (.cv x) (.cv r)) p0015 p0008
  have p0017 :=
    @gElcompl (synCop (synCsn (.cv z)) (synCop (.cv x) (.cv r)))
      (synCima (synCin (synCins2 (synCins3 (synCsset))) (synCdif (synCima
              (synCin (synCins4 (synCsi3 (synCid)))
                (synCins2 (synCins2 (synCins2 (synCsset))))) (synC1c))
            (synCins3 (synCid)))) (synC1c))
      p0016
  have p0018 :=
    @gElin
      (synCop (synCsn (.cv y)) (synCop (synCsn (.cv z)) (synCop (.cv x) (.cv r))))
      (synCins2 (synCins3 (synCsset)))
      (synCdif (synCima (synCin (synCins4 (synCsi3 (synCid)))
            (synCins2 (synCins2 (synCins2 (synCsset))))) (synC1c)) (synCins3 (synCid)))
  have p0019 :=
    @gOtelins2 (synCsn (.cv y)) (synCsn (.cv z)) (synCop (.cv x) (.cv r))
      (synCins3 (synCsset)) p0015
  have p0020 := @gOtelins3 (synCsn (.cv y)) (.cv x) (.cv r) (synCsset) p0001
  have p0021 := @gVex y
  have p0022 := @gOpelssetsn (.cv y) (.cv x) p0021 p0007
  have p0023_e02_recanon :
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
      p0022
  have p0023 :=
    @gN3bitri
      (.classMem
        (synCop (synCsn (.cv y)) (synCop (synCsn (.cv z)) (synCop (.cv x) (.cv r))))
        (synCins2 (synCins3 (synCsset))))
      (.classMem (synCop (synCsn (.cv y)) (synCop (.cv x) (.cv r))) (synCins3 (synCsset)))
      (.classMem (synCop (synCsn (.cv y)) (.cv x)) (synCsset)) (.objMem y x) p0019
      p0020 p0023_e02_recanon
  have p0024 :=
    @gEldif
      (synCop (synCsn (.cv y)) (synCop (synCsn (.cv z)) (synCop (.cv x) (.cv r))))
      (synCima (synCin (synCins4 (synCsi3 (synCid)))
          (synCins2 (synCins2 (synCins2 (synCsset))))) (synC1c))
      (synCins3 (synCid))
  have p0025 :=
    @gElin
      (synCop (synCsn (.cv t))
        (synCop (synCsn (.cv y)) (synCop (synCsn (.cv z)) (synCop (.cv x) (.cv r)))))
      (synCins4 (synCsi3 (synCid))) (synCins2 (synCins2 (synCins2 (synCsset))))
  have p0026 :=
    @gOqelins4 (synCsn (.cv t)) (synCsn (.cv y)) (synCsn (.cv z))
      (synCop (.cv x) (.cv r)) (synCsi3 (synCid)) p0008
  have p0027 := @gVex t
  have p0028 := @gOtsnelsi3 (.cv t) (.cv y) (.cv z) (synCid) p0027 p0021 p0012
  have p0029 := (Nominal.biimpRefl (synWbr (.cv t) (synCid) (synCop (.cv y) (.cv z))))
  have p0030 := @gOpex (.cv y) (.cv z) p0021 p0012
  have p0031 := @gIdeq (.cv t) (synCop (.cv y) (.cv z)) p0030
  have p0032 :=
    @gBitr3i (.classMem (synCop (.cv t) (synCop (.cv y) (.cv z))) (synCid))
      (synWbr (.cv t) (synCid) (synCop (.cv y) (.cv z)))
      (.classEq (.cv t) (synCop (.cv y) (.cv z))) p0029 p0031
  have p0033 :=
    @gN3bitri
      (.classMem (synCop (synCsn (.cv t)) (synCop (synCsn (.cv y))
            (synCop (synCsn (.cv z)) (synCop (.cv x) (.cv r)))))
        (synCins4 (synCsi3 (synCid))))
      (.classMem (synCop (synCsn (.cv t)) (synCop (synCsn (.cv y)) (synCsn (.cv z))))
        (synCsi3 (synCid)))
      (.classMem (synCop (.cv t) (synCop (.cv y) (.cv z))) (synCid))
      (.classEq (.cv t) (synCop (.cv y) (.cv z))) p0026 p0028 p0032
  have p0034 := @gSnex (.cv y)
  have p0035 :=
    @gOtelins2 (synCsn (.cv t)) (synCsn (.cv y))
      (synCop (synCsn (.cv z)) (synCop (.cv x) (.cv r)))
      (synCins2 (synCins2 (synCsset))) p0034
  have p0036 :=
    @gOtelins2 (synCsn (.cv t)) (synCsn (.cv z)) (synCop (.cv x) (.cv r))
      (synCins2 (synCsset)) p0015
  have p0037 := @gOtelins2 (synCsn (.cv t)) (.cv x) (.cv r) (synCsset) p0007
  have p0038 := @gOpelssetsn (.cv t) (.cv r) p0027 p0001
  have p0039_e01_recanon :
    Nominal.NPrf
      (synWb (.classMem (synCop (synCsn (.cv t)) (.cv r)) (synCsset)) (.objMem t r)) :=
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
      p0038
  have p0039 :=
    @gBitri
      (.classMem (synCop (synCsn (.cv t)) (synCop (.cv x) (.cv r))) (synCins2 (synCsset)))
      (.classMem (synCop (synCsn (.cv t)) (.cv r)) (synCsset)) (.objMem t r) p0037
      p0039_e01_recanon
  have p0040 :=
    @gN3bitri
      (.classMem (synCop (synCsn (.cv t)) (synCop (synCsn (.cv y))
            (synCop (synCsn (.cv z)) (synCop (.cv x) (.cv r)))))
        (synCins2 (synCins2 (synCins2 (synCsset)))))
      (.classMem
        (synCop (synCsn (.cv t)) (synCop (synCsn (.cv z)) (synCop (.cv x) (.cv r))))
        (synCins2 (synCins2 (synCsset))))
      (.classMem (synCop (synCsn (.cv t)) (synCop (.cv x) (.cv r))) (synCins2 (synCsset)))
      (.objMem t r) p0035 p0036 p0039
  have p0041 :=
    @gAnbi12i
      (.classMem (synCop (synCsn (.cv t)) (synCop (synCsn (.cv y))
            (synCop (synCsn (.cv z)) (synCop (.cv x) (.cv r)))))
        (synCins4 (synCsi3 (synCid))))
      (.classEq (.cv t) (synCop (.cv y) (.cv z)))
      (.classMem (synCop (synCsn (.cv t)) (synCop (synCsn (.cv y))
            (synCop (synCsn (.cv z)) (synCop (.cv x) (.cv r)))))
        (synCins2 (synCins2 (synCins2 (synCsset)))))
      (.objMem t r) p0033 p0040
  have p0042 :=
    @gBitri
      (.classMem (synCop (synCsn (.cv t)) (synCop (synCsn (.cv y))
            (synCop (synCsn (.cv z)) (synCop (.cv x) (.cv r)))))
        (synCin (synCins4 (synCsi3 (synCid)))
          (synCins2 (synCins2 (synCins2 (synCsset))))))
      (synWa (.classMem (synCop (synCsn (.cv t)) (synCop (synCsn (.cv y))
              (synCop (synCsn (.cv z)) (synCop (.cv x) (.cv r)))))
          (synCins4 (synCsi3 (synCid)))) (.classMem (synCop (synCsn (.cv t))
            (synCop (synCsn (.cv y)) (synCop (synCsn (.cv z)) (synCop (.cv x) (.cv r)))))
          (synCins2 (synCins2 (synCins2 (synCsset))))))
      (synWa (.classEq (.cv t) (synCop (.cv y) (.cv z))) (.objMem t r)) p0025 p0041
  have p0043 :=
    @gExbii
      (.classMem (synCop (synCsn (.cv t)) (synCop (synCsn (.cv y))
            (synCop (synCsn (.cv z)) (synCop (.cv x) (.cv r)))))
        (synCin (synCins4 (synCsi3 (synCid)))
          (synCins2 (synCins2 (synCins2 (synCsset))))))
      (synWa (.classEq (.cv t) (synCop (.cv y) (.cv z))) (.objMem t r)) t p0042
  have p0044 :=
    @gElima1c t
      (synCop (synCsn (.cv y)) (synCop (synCsn (.cv z)) (synCop (.cv x) (.cv r))))
      (synCin (synCins4 (synCsi3 (synCid))) (synCins2 (synCins2 (synCins2 (synCsset)))))
      dv_cache_0013 dv_cache_0014
  have p0045 := (Nominal.biimpRefl (synWbr (.cv y) (.cv r) (.cv z)))
  have p0046 :=
    (NFChoice.DirectNominalPrf.Nominal.DefinitionLeafHandlersCanonical001.dfClelOfDV t
      (synCop (.cv y) (.cv z)) (.cv r) dv_cache_0015 dv_cache_0016)
  have p0047_e01_recanon :
    Nominal.NPrf
      (synWb (.classMem (synCop (.cv y) (.cv z)) (.cv r)) (synWex t
          (synWa (.classEq (.cv t) (synCop (.cv y) (.cv z))) (.objMem t r)))) :=
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
      p0046
  have p0047 :=
    @gBitri (synWbr (.cv y) (.cv r) (.cv z))
      (.classMem (synCop (.cv y) (.cv z)) (.cv r))
      (synWex t (synWa (.classEq (.cv t) (synCop (.cv y) (.cv z))) (.objMem t r)))
      p0045 p0047_e01_recanon
  have p0048 :=
    @gN3bitr4i
      (synWex t (.classMem (synCop (synCsn (.cv t)) (synCop (synCsn (.cv y))
              (synCop (synCsn (.cv z)) (synCop (.cv x) (.cv r)))))
          (synCin (synCins4 (synCsi3 (synCid)))
            (synCins2 (synCins2 (synCins2 (synCsset)))))))
      (synWex t (synWa (.classEq (.cv t) (synCop (.cv y) (.cv z))) (.objMem t r)))
      (.classMem
        (synCop (synCsn (.cv y)) (synCop (synCsn (.cv z)) (synCop (.cv x) (.cv r))))
        (synCima (synCin (synCins4 (synCsi3 (synCid)))
            (synCins2 (synCins2 (synCins2 (synCsset))))) (synC1c)))
      (synWbr (.cv y) (.cv r) (.cv z)) p0043 p0044 p0047
  have p0049 :=
    @gOtelins3 (synCsn (.cv y)) (synCsn (.cv z)) (synCop (.cv x) (.cv r)) (synCid)
      p0008
  have p0050 :=
    (Nominal.biimpRefl (synWbr (synCsn (.cv y)) (synCid) (synCsn (.cv z))))
  have p0051 := @gIdeq (synCsn (.cv y)) (synCsn (.cv z)) p0015
  have p0052 := @gSneqb (.cv y) (.cv z) p0021
  have p0053_e01_recanon :
    Nominal.NPrf (synWb (.classEq (synCsn (.cv y)) (synCsn (.cv z))) (.objEq y z)) :=
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
    @gBitri (synWbr (synCsn (.cv y)) (synCid) (synCsn (.cv z)))
      (.classEq (synCsn (.cv y)) (synCsn (.cv z))) (.objEq y z) p0051 p0053_e01_recanon
  have p0054 :=
    @gBitr3i (.classMem (synCop (synCsn (.cv y)) (synCsn (.cv z))) (synCid))
      (synWbr (synCsn (.cv y)) (synCid) (synCsn (.cv z))) (.objEq y z) p0050 p0053
  have p0055 :=
    @gBitri
      (.classMem
        (synCop (synCsn (.cv y)) (synCop (synCsn (.cv z)) (synCop (.cv x) (.cv r))))
        (synCins3 (synCid)))
      (.classMem (synCop (synCsn (.cv y)) (synCsn (.cv z))) (synCid)) (.objEq y z)
      p0049 p0054
  have p0056 :=
    @gNotbii
      (.classMem
        (synCop (synCsn (.cv y)) (synCop (synCsn (.cv z)) (synCop (.cv x) (.cv r))))
        (synCins3 (synCid)))
      (.objEq y z) p0055
  have p0057 :=
    @gAnbi12i
      (.classMem
        (synCop (synCsn (.cv y)) (synCop (synCsn (.cv z)) (synCop (.cv x) (.cv r))))
        (synCima (synCin (synCins4 (synCsi3 (synCid)))
            (synCins2 (synCins2 (synCins2 (synCsset))))) (synC1c)))
      (synWbr (.cv y) (.cv r) (.cv z))
      (.neg (.classMem (synCop (synCsn (.cv y))
            (synCop (synCsn (.cv z)) (synCop (.cv x) (.cv r)))) (synCins3 (synCid))))
      (.neg (.objEq y z)) p0048 p0056
  have p0058 :=
    @gBitri
      (.classMem
        (synCop (synCsn (.cv y)) (synCop (synCsn (.cv z)) (synCop (.cv x) (.cv r))))
        (synCdif (synCima (synCin (synCins4 (synCsi3 (synCid)))
              (synCins2 (synCins2 (synCins2 (synCsset))))) (synC1c))
          (synCins3 (synCid))))
      (synWa (.classMem (synCop (synCsn (.cv y))
            (synCop (synCsn (.cv z)) (synCop (.cv x) (.cv r)))) (synCima
            (synCin (synCins4 (synCsi3 (synCid)))
              (synCins2 (synCins2 (synCins2 (synCsset))))) (synC1c))) (.neg (.classMem
            (synCop (synCsn (.cv y)) (synCop (synCsn (.cv z)) (synCop (.cv x) (.cv r))))
            (synCins3 (synCid)))))
      (synWa (synWbr (.cv y) (.cv r) (.cv z)) (.neg (.objEq y z))) p0024 p0057
  have p0059 :=
    @gAnbi12i
      (.classMem
        (synCop (synCsn (.cv y)) (synCop (synCsn (.cv z)) (synCop (.cv x) (.cv r))))
        (synCins2 (synCins3 (synCsset))))
      (.objMem y x)
      (.classMem
        (synCop (synCsn (.cv y)) (synCop (synCsn (.cv z)) (synCop (.cv x) (.cv r))))
        (synCdif (synCima (synCin (synCins4 (synCsi3 (synCid)))
              (synCins2 (synCins2 (synCins2 (synCsset))))) (synC1c))
          (synCins3 (synCid))))
      (synWa (synWbr (.cv y) (.cv r) (.cv z)) (.neg (.objEq y z))) p0023 p0058
  have p0060 :=
    @gBitri
      (.classMem
        (synCop (synCsn (.cv y)) (synCop (synCsn (.cv z)) (synCop (.cv x) (.cv r))))
        (synCin (synCins2 (synCins3 (synCsset))) (synCdif (synCima
              (synCin (synCins4 (synCsi3 (synCid)))
                (synCins2 (synCins2 (synCins2 (synCsset))))) (synC1c))
            (synCins3 (synCid)))))
      (synWa (.classMem (synCop (synCsn (.cv y))
            (synCop (synCsn (.cv z)) (synCop (.cv x) (.cv r))))
          (synCins2 (synCins3 (synCsset)))) (.classMem (synCop (synCsn (.cv y))
            (synCop (synCsn (.cv z)) (synCop (.cv x) (.cv r)))) (synCdif (synCima
              (synCin (synCins4 (synCsi3 (synCid)))
                (synCins2 (synCins2 (synCins2 (synCsset))))) (synC1c))
            (synCins3 (synCid)))))
      (synWa (.objMem y x) (synWa (synWbr (.cv y) (.cv r) (.cv z)) (.neg (.objEq y z))))
      p0018 p0059
  have p0061 :=
    @gExbii
      (.classMem
        (synCop (synCsn (.cv y)) (synCop (synCsn (.cv z)) (synCop (.cv x) (.cv r))))
        (synCin (synCins2 (synCins3 (synCsset))) (synCdif (synCima
              (synCin (synCins4 (synCsi3 (synCid)))
                (synCins2 (synCins2 (synCins2 (synCsset))))) (synC1c))
            (synCins3 (synCid)))))
      (synWa (.objMem y x) (synWa (synWbr (.cv y) (.cv r) (.cv z)) (.neg (.objEq y z))))
      y p0060
  have p0062 :=
    @gElima1c y (synCop (synCsn (.cv z)) (synCop (.cv x) (.cv r)))
      (synCin (synCins2 (synCins3 (synCsset))) (synCdif (synCima
            (synCin (synCins4 (synCsi3 (synCid)))
              (synCins2 (synCins2 (synCins2 (synCsset))))) (synC1c))
          (synCins3 (synCid))))
      dv_cache_0017 dv_cache_0018
  have p0063 :=
    (Nominal.biimpRefl
      (synWrex y (.cv x) (synWa (synWbr (.cv y) (.cv r) (.cv z)) (.neg (.objEq y z)))))
  have p0064_e02_recanon :
    Nominal.NPrf
      (synWb (synWrex y (.cv x)
          (synWa (synWbr (.cv y) (.cv r) (.cv z)) (.neg (.objEq y z)))) (synWex y
          (synWa (.objMem y x)
            (synWa (synWbr (.cv y) (.cv r) (.cv z)) (.neg (.objEq y z)))))) :=
    Nominal.RecanonTransportDev.transport
      (by
        simp only [synWb, synWrex, synWex, synWa]
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
            · exact Nominal.RecanonTransportDev.TRecanonWff.same _
        · apply Nominal.RecanonTransportDev.TRecanonWff.neg
          apply Nominal.RecanonTransportDev.TRecanonWff.imp
          · apply Nominal.RecanonTransportDev.TRecanonWff.neg
            apply Nominal.RecanonTransportDev.TRecanonWff.all
            apply Nominal.RecanonTransportDev.TRecanonWff.neg
            apply Nominal.RecanonTransportDev.TRecanonWff.neg
            apply Nominal.RecanonTransportDev.TRecanonWff.imp
            · exact Nominal.RecanonTransportDev.TRecanonWff.classMem_objMem _ _
            · exact Nominal.RecanonTransportDev.TRecanonWff.same _
          · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0063
  have p0064 :=
    @gN3bitr4i
      (synWex y (.classMem (synCop (synCsn (.cv y))
            (synCop (synCsn (.cv z)) (synCop (.cv x) (.cv r))))
          (synCin (synCins2 (synCins3 (synCsset))) (synCdif (synCima
                (synCin (synCins4 (synCsi3 (synCid)))
                  (synCins2 (synCins2 (synCins2 (synCsset))))) (synC1c))
              (synCins3 (synCid))))))
      (synWex y (synWa (.objMem y x)
          (synWa (synWbr (.cv y) (.cv r) (.cv z)) (.neg (.objEq y z)))))
      (.classMem (synCop (synCsn (.cv z)) (synCop (.cv x) (.cv r))) (synCima
          (synCin (synCins2 (synCins3 (synCsset))) (synCdif (synCima
                (synCin (synCins4 (synCsi3 (synCid)))
                  (synCins2 (synCins2 (synCins2 (synCsset))))) (synC1c))
              (synCins3 (synCid)))) (synC1c)))
      (synWrex y (.cv x) (synWa (synWbr (.cv y) (.cv r) (.cv z)) (.neg (.objEq y z))))
      p0061 p0062 p0064_e02_recanon
  have p0065 := @gRexanali (synWbr (.cv y) (.cv r) (.cv z)) (.objEq y z) y (.cv x)
  have p0066 :=
    @gBitri
      (.classMem (synCop (synCsn (.cv z)) (synCop (.cv x) (.cv r))) (synCima
          (synCin (synCins2 (synCins3 (synCsset))) (synCdif (synCima
                (synCin (synCins4 (synCsi3 (synCid)))
                  (synCins2 (synCins2 (synCins2 (synCsset))))) (synC1c))
              (synCins3 (synCid)))) (synC1c)))
      (synWrex y (.cv x) (synWa (synWbr (.cv y) (.cv r) (.cv z)) (.neg (.objEq y z))))
      (.neg (synWral y (.cv x) (.imp (synWbr (.cv y) (.cv r) (.cv z)) (.objEq y z))))
      p0064 p0065
  have p0067 :=
    @gCon2bii
      (.classMem (synCop (synCsn (.cv z)) (synCop (.cv x) (.cv r))) (synCima
          (synCin (synCins2 (synCins3 (synCsset))) (synCdif (synCima
                (synCin (synCins4 (synCsi3 (synCid)))
                  (synCins2 (synCins2 (synCins2 (synCsset))))) (synC1c))
              (synCins3 (synCid)))) (synC1c)))
      (synWral y (.cv x) (.imp (synWbr (.cv y) (.cv r) (.cv z)) (.objEq y z))) p0066
  have p0068 :=
    @gBitr4i
      (.classMem (synCop (synCsn (.cv z)) (synCop (.cv x) (.cv r))) (synCcompl (synCima
            (synCin (synCins2 (synCins3 (synCsset))) (synCdif (synCima
                  (synCin (synCins4 (synCsi3 (synCid)))
                    (synCins2 (synCins2 (synCins2 (synCsset))))) (synC1c))
                (synCins3 (synCid)))) (synC1c))))
      (.neg (.classMem (synCop (synCsn (.cv z)) (synCop (.cv x) (.cv r))) (synCima
            (synCin (synCins2 (synCins3 (synCsset))) (synCdif (synCima
                  (synCin (synCins4 (synCsi3 (synCid)))
                    (synCins2 (synCins2 (synCins2 (synCsset))))) (synC1c))
                (synCins3 (synCid)))) (synC1c))))
      (synWral y (.cv x) (.imp (synWbr (.cv y) (.cv r) (.cv z)) (.objEq y z))) p0017
      p0067
  have p0069 :=
    @gAnbi12i
      (.classMem (synCop (synCsn (.cv z)) (synCop (.cv x) (.cv r))) (synCins3 (synCsset)))
      (.objMem z x)
      (.classMem (synCop (synCsn (.cv z)) (synCop (.cv x) (.cv r))) (synCcompl (synCima
            (synCin (synCins2 (synCins3 (synCsset))) (synCdif (synCima
                  (synCin (synCins4 (synCsi3 (synCid)))
                    (synCins2 (synCins2 (synCins2 (synCsset))))) (synC1c))
                (synCins3 (synCid)))) (synC1c))))
      (synWral y (.cv x) (.imp (synWbr (.cv y) (.cv r) (.cv z)) (.objEq y z))) p0014
      p0068
  have p0070 :=
    @gBitri
      (.classMem (synCop (synCsn (.cv z)) (synCop (.cv x) (.cv r)))
        (synCin (synCins3 (synCsset)) (synCcompl (synCima
              (synCin (synCins2 (synCins3 (synCsset))) (synCdif (synCima
                    (synCin (synCins4 (synCsi3 (synCid)))
                      (synCins2 (synCins2 (synCins2 (synCsset))))) (synC1c))
                  (synCins3 (synCid)))) (synC1c)))))
      (synWa (.classMem (synCop (synCsn (.cv z)) (synCop (.cv x) (.cv r)))
          (synCins3 (synCsset)))
        (.classMem (synCop (synCsn (.cv z)) (synCop (.cv x) (.cv r))) (synCcompl (synCima
              (synCin (synCins2 (synCins3 (synCsset))) (synCdif (synCima
                    (synCin (synCins4 (synCsi3 (synCid)))
                      (synCins2 (synCins2 (synCins2 (synCsset))))) (synC1c))
                  (synCins3 (synCid)))) (synC1c)))))
      (synWa (.objMem z x)
        (synWral y (.cv x) (.imp (synWbr (.cv y) (.cv r) (.cv z)) (.objEq y z))))
      p0010 p0069
  have p0071 :=
    @gExbii
      (.classMem (synCop (synCsn (.cv z)) (synCop (.cv x) (.cv r)))
        (synCin (synCins3 (synCsset)) (synCcompl (synCima
              (synCin (synCins2 (synCins3 (synCsset))) (synCdif (synCima
                    (synCin (synCins4 (synCsi3 (synCid)))
                      (synCins2 (synCins2 (synCins2 (synCsset))))) (synC1c))
                  (synCins3 (synCid)))) (synC1c)))))
      (synWa (.objMem z x)
        (synWral y (.cv x) (.imp (synWbr (.cv y) (.cv r) (.cv z)) (.objEq y z))))
      z p0070
  have p0072 :=
    @gElima1c z (synCop (.cv x) (.cv r))
      (synCin (synCins3 (synCsset)) (synCcompl (synCima
            (synCin (synCins2 (synCins3 (synCsset))) (synCdif (synCima
                  (synCin (synCins4 (synCsi3 (synCid)))
                    (synCins2 (synCins2 (synCins2 (synCsset))))) (synC1c))
                (synCins3 (synCid)))) (synC1c))))
      dv_cache_0019 dv_cache_0020
  have p0073 :=
    (Nominal.biimpRefl (synWrex z (.cv x)
        (synWral y (.cv x) (.imp (synWbr (.cv y) (.cv r) (.cv z)) (.objEq y z)))))
  have p0074_e02_recanon :
    Nominal.NPrf
      (synWb (synWrex z (.cv x)
          (synWral y (.cv x) (.imp (synWbr (.cv y) (.cv r) (.cv z)) (.objEq y z)))) (synWex z
          (synWa (.objMem z x) (synWral y (.cv x)
              (.imp (synWbr (.cv y) (.cv r) (.cv z)) (.objEq y z)))))) :=
    Nominal.RecanonTransportDev.transport
      (by
        simp only [synWb, synWrex, synWex, synWa, synWral, synWbr, synCop, synCun,
          synCnin, synWnan, synCcompl]
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
            · exact Nominal.RecanonTransportDev.TRecanonWff.same _
        · apply Nominal.RecanonTransportDev.TRecanonWff.neg
          apply Nominal.RecanonTransportDev.TRecanonWff.imp
          · apply Nominal.RecanonTransportDev.TRecanonWff.neg
            apply Nominal.RecanonTransportDev.TRecanonWff.all
            apply Nominal.RecanonTransportDev.TRecanonWff.neg
            apply Nominal.RecanonTransportDev.TRecanonWff.neg
            apply Nominal.RecanonTransportDev.TRecanonWff.imp
            · exact Nominal.RecanonTransportDev.TRecanonWff.classMem_objMem _ _
            · exact Nominal.RecanonTransportDev.TRecanonWff.same _
          · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0073
  have p0074 :=
    @gN3bitr4i
      (synWex z (.classMem (synCop (synCsn (.cv z)) (synCop (.cv x) (.cv r)))
          (synCin (synCins3 (synCsset)) (synCcompl (synCima
                (synCin (synCins2 (synCins3 (synCsset))) (synCdif (synCima
                      (synCin (synCins4 (synCsi3 (synCid)))
                        (synCins2 (synCins2 (synCins2 (synCsset))))) (synC1c))
                    (synCins3 (synCid)))) (synC1c))))))
      (synWex z (synWa (.objMem z x)
          (synWral y (.cv x) (.imp (synWbr (.cv y) (.cv r) (.cv z)) (.objEq y z)))))
      (.classMem (synCop (.cv x) (.cv r)) (synCima (synCin (synCins3 (synCsset))
            (synCcompl (synCima (synCin (synCins2 (synCins3 (synCsset))) (synCdif
                    (synCima (synCin (synCins4 (synCsi3 (synCid)))
                        (synCins2 (synCins2 (synCins2 (synCsset))))) (synC1c))
                    (synCins3 (synCid)))) (synC1c)))) (synC1c)))
      (synWrex z (.cv x)
        (synWral y (.cv x) (.imp (synWbr (.cv y) (.cv r) (.cv z)) (.objEq y z))))
      p0071 p0072 p0074_e02_recanon
  have p0075 :=
    @gNotbii
      (.classMem (synCop (.cv x) (.cv r)) (synCima (synCin (synCins3 (synCsset))
            (synCcompl (synCima (synCin (synCins2 (synCins3 (synCsset))) (synCdif
                    (synCima (synCin (synCins4 (synCsi3 (synCid)))
                        (synCins2 (synCins2 (synCins2 (synCsset))))) (synC1c))
                    (synCins3 (synCid)))) (synC1c)))) (synC1c)))
      (synWrex z (.cv x)
        (synWral y (.cv x) (.imp (synWbr (.cv y) (.cv r) (.cv z)) (.objEq y z))))
      p0074
  have p0076 :=
    @gBitri
      (.classMem (synCop (.cv x) (.cv r)) (synCcompl (synCima
            (synCin (synCins3 (synCsset)) (synCcompl (synCima
                  (synCin (synCins2 (synCins3 (synCsset))) (synCdif (synCima
                        (synCin (synCins4 (synCsi3 (synCid)))
                          (synCins2 (synCins2 (synCins2 (synCsset))))) (synC1c))
                      (synCins3 (synCid)))) (synC1c)))) (synC1c))))
      (.neg (.classMem (synCop (.cv x) (.cv r)) (synCima (synCin (synCins3 (synCsset))
              (synCcompl (synCima (synCin (synCins2 (synCins3 (synCsset))) (synCdif
                      (synCima (synCin (synCins4 (synCsi3 (synCid)))
                          (synCins2 (synCins2 (synCins2 (synCsset))))) (synC1c))
                      (synCins3 (synCid)))) (synC1c)))) (synC1c))))
      (.neg (synWrex z (.cv x)
          (synWral y (.cv x) (.imp (synWbr (.cv y) (.cv r) (.cv z)) (.objEq y z)))))
      p0009 p0075
  have p0077 :=
    @gElin (synCop (.cv x) (.cv a)) (synCsset)
      (synCxp (synCcompl (synCsn (synC0))) (synCvv))
  have p0078 := (Nominal.biimpRefl (synWbr (.cv x) (synCsset) (.cv a)))
  have p0079 := @gBrsset (.cv x) (.cv a) p0007 p0002
  have p0080 :=
    @gBitr3i (.classMem (synCop (.cv x) (.cv a)) (synCsset))
      (synWbr (.cv x) (synCsset) (.cv a)) (synWss (.cv x) (.cv a)) p0078 p0079
  have p0081 := @gOpelxp (.cv x) (.cv a) (synCcompl (synCsn (synC0))) (synCvv)
  have p0082 :=
    @gMpbiran2
      (.classMem (synCop (.cv x) (.cv a)) (synCxp (synCcompl (synCsn (synC0))) (synCvv)))
      (.classMem (.cv x) (synCcompl (synCsn (synC0)))) (.classMem (.cv a) (synCvv))
      p0002 p0081
  have p0083 := @gElcompl (.cv x) (synCsn (synC0)) p0007
  have p0084 := @gElsn x (synC0) dv_cache_0021
  have p0085 :=
    @gNecon3bbii (.classMem (.cv x) (synCsn (synC0))) (.cv x) (synC0) p0084
  have p0086 :=
    @gN3bitri
      (.classMem (synCop (.cv x) (.cv a)) (synCxp (synCcompl (synCsn (synC0))) (synCvv)))
      (.classMem (.cv x) (synCcompl (synCsn (synC0))))
      (.neg (.classMem (.cv x) (synCsn (synC0)))) (synWne (.cv x) (synC0)) p0082 p0083
      p0085
  have p0087 :=
    @gAnbi12i (.classMem (synCop (.cv x) (.cv a)) (synCsset)) (synWss (.cv x) (.cv a))
      (.classMem (synCop (.cv x) (.cv a)) (synCxp (synCcompl (synCsn (synC0))) (synCvv)))
      (synWne (.cv x) (synC0)) p0080 p0086
  have p0088 :=
    @gBitri
      (.classMem (synCop (.cv x) (.cv a))
        (synCin (synCsset) (synCxp (synCcompl (synCsn (synC0))) (synCvv))))
      (synWa (.classMem (synCop (.cv x) (.cv a)) (synCsset))
        (.classMem (synCop (.cv x) (.cv a))
          (synCxp (synCcompl (synCsn (synC0))) (synCvv))))
      (synWa (synWss (.cv x) (.cv a)) (synWne (.cv x) (synC0))) p0077 p0087
  have p0089 :=
    @gAnbi12ci
      (.classMem (synCop (.cv x) (.cv r)) (synCcompl (synCima
            (synCin (synCins3 (synCsset)) (synCcompl (synCima
                  (synCin (synCins2 (synCins3 (synCsset))) (synCdif (synCima
                        (synCin (synCins4 (synCsi3 (synCid)))
                          (synCins2 (synCins2 (synCins2 (synCsset))))) (synC1c))
                      (synCins3 (synCid)))) (synC1c)))) (synC1c))))
      (.neg (synWrex z (.cv x)
          (synWral y (.cv x) (.imp (synWbr (.cv y) (.cv r) (.cv z)) (.objEq y z)))))
      (.classMem (synCop (.cv x) (.cv a))
        (synCin (synCsset) (synCxp (synCcompl (synCsn (synC0))) (synCvv))))
      (synWa (synWss (.cv x) (.cv a)) (synWne (.cv x) (synC0))) p0076 p0088
  have p0090 :=
    @gBitri
      (.classMem (synCop (.cv x) (synCop (.cv r) (.cv a))) (synCtxp (synCcompl (synCima
              (synCin (synCins3 (synCsset)) (synCcompl (synCima
                    (synCin (synCins2 (synCins3 (synCsset))) (synCdif (synCima
                          (synCin (synCins4 (synCsi3 (synCid)))
                            (synCins2 (synCins2 (synCins2 (synCsset))))) (synC1c))
                        (synCins3 (synCid)))) (synC1c)))) (synC1c)))
          (synCin (synCsset) (synCxp (synCcompl (synCsn (synC0))) (synCvv)))))
      (synWa (.classMem (synCop (.cv x) (.cv r)) (synCcompl (synCima
              (synCin (synCins3 (synCsset)) (synCcompl (synCima
                    (synCin (synCins2 (synCins3 (synCsset))) (synCdif (synCima
                          (synCin (synCins4 (synCsi3 (synCid)))
                            (synCins2 (synCins2 (synCins2 (synCsset))))) (synC1c))
                        (synCins3 (synCid)))) (synC1c)))) (synC1c))))
        (.classMem (synCop (.cv x) (.cv a))
          (synCin (synCsset) (synCxp (synCcompl (synCsn (synC0))) (synCvv)))))
      (synWa (synWa (synWss (.cv x) (.cv a)) (synWne (.cv x) (synC0))) (.neg
          (synWrex z (.cv x)
            (synWral y (.cv x) (.imp (synWbr (.cv y) (.cv r) (.cv z)) (.objEq y z))))))
      p0006 p0089
  have p0091 :=
    @gExbii
      (.classMem (synCop (.cv x) (synCop (.cv r) (.cv a))) (synCtxp (synCcompl (synCima
              (synCin (synCins3 (synCsset)) (synCcompl (synCima
                    (synCin (synCins2 (synCins3 (synCsset))) (synCdif (synCima
                          (synCin (synCins4 (synCsi3 (synCid)))
                            (synCins2 (synCins2 (synCins2 (synCsset))))) (synC1c))
                        (synCins3 (synCid)))) (synC1c)))) (synC1c)))
          (synCin (synCsset) (synCxp (synCcompl (synCsn (synC0))) (synCvv)))))
      (synWa (synWa (synWss (.cv x) (.cv a)) (synWne (.cv x) (synC0))) (.neg
          (synWrex z (.cv x)
            (synWral y (.cv x) (.imp (synWbr (.cv y) (.cv r) (.cv z)) (.objEq y z))))))
      x p0090
  have p0092 :=
    @gExanali (synWa (synWss (.cv x) (.cv a)) (synWne (.cv x) (synC0)))
      (synWrex z (.cv x)
        (synWral y (.cv x) (.imp (synWbr (.cv y) (.cv r) (.cv z)) (.objEq y z))))
      x
  have p0093 :=
    @gN3bitri
      (.classMem (synCop (.cv r) (.cv a)) (synCrn (synCtxp (synCcompl (synCima
                (synCin (synCins3 (synCsset)) (synCcompl (synCima
                      (synCin (synCins2 (synCins3 (synCsset))) (synCdif (synCima
                            (synCin (synCins4 (synCsi3 (synCid)))
                              (synCins2 (synCins2 (synCins2 (synCsset))))) (synC1c))
                          (synCins3 (synCid)))) (synC1c)))) (synC1c)))
            (synCin (synCsset) (synCxp (synCcompl (synCsn (synC0))) (synCvv))))))
      (synWex x (.classMem (synCop (.cv x) (synCop (.cv r) (.cv a))) (synCtxp (synCcompl
              (synCima (synCin (synCins3 (synCsset)) (synCcompl (synCima
                      (synCin (synCins2 (synCins3 (synCsset))) (synCdif (synCima
                            (synCin (synCins4 (synCsi3 (synCid)))
                              (synCins2 (synCins2 (synCins2 (synCsset))))) (synC1c))
                          (synCins3 (synCid)))) (synC1c)))) (synC1c)))
            (synCin (synCsset) (synCxp (synCcompl (synCsn (synC0))) (synCvv))))))
      (synWex x (synWa (synWa (synWss (.cv x) (.cv a)) (synWne (.cv x) (synC0))) (.neg
            (synWrex z (.cv x) (synWral y (.cv x)
                (.imp (synWbr (.cv y) (.cv r) (.cv z)) (.objEq y z)))))))
      (.neg (.all x (.imp (synWa (synWss (.cv x) (.cv a)) (synWne (.cv x) (synC0)))
            (synWrex z (.cv x) (synWral y (.cv x)
                (.imp (synWbr (.cv y) (.cv r) (.cv z)) (.objEq y z)))))))
      p0005 p0091 p0092
  have p0094 :=
    @gCon2bii
      (.classMem (synCop (.cv r) (.cv a)) (synCrn (synCtxp (synCcompl (synCima
                (synCin (synCins3 (synCsset)) (synCcompl (synCima
                      (synCin (synCins2 (synCins3 (synCsset))) (synCdif (synCima
                            (synCin (synCins4 (synCsi3 (synCid)))
                              (synCins2 (synCins2 (synCins2 (synCsset))))) (synC1c))
                          (synCins3 (synCid)))) (synC1c)))) (synC1c)))
            (synCin (synCsset) (synCxp (synCcompl (synCsn (synC0))) (synCvv))))))
      (.all x (.imp (synWa (synWss (.cv x) (.cv a)) (synWne (.cv x) (synC0)))
          (synWrex z (.cv x)
            (synWral y (.cv x) (.imp (synWbr (.cv y) (.cv r) (.cv z)) (.objEq y z))))))
      p0093
  have p0095 :=
    @gBitr4i
      (.classMem (synCop (.cv r) (.cv a)) (synCcompl (synCrn (synCtxp (synCcompl (synCima
                  (synCin (synCins3 (synCsset)) (synCcompl (synCima
                        (synCin (synCins2 (synCins3 (synCsset))) (synCdif (synCima
                              (synCin (synCins4 (synCsi3 (synCid)))
                                (synCins2 (synCins2 (synCins2 (synCsset))))) (synC1c))
                            (synCins3 (synCid)))) (synC1c)))) (synC1c)))
              (synCin (synCsset) (synCxp (synCcompl (synCsn (synC0))) (synCvv)))))))
      (.neg (.classMem (synCop (.cv r) (.cv a)) (synCrn (synCtxp (synCcompl (synCima
                  (synCin (synCins3 (synCsset)) (synCcompl (synCima
                        (synCin (synCins2 (synCins3 (synCsset))) (synCdif (synCima
                              (synCin (synCins4 (synCsi3 (synCid)))
                                (synCins2 (synCins2 (synCins2 (synCsset))))) (synC1c))
                            (synCins3 (synCid)))) (synC1c)))) (synC1c)))
              (synCin (synCsset) (synCxp (synCcompl (synCsn (synC0))) (synCvv)))))))
      (.all x (.imp (synWa (synWss (.cv x) (.cv a)) (synWne (.cv x) (synC0)))
          (synWrex z (.cv x)
            (synWral y (.cv x) (.imp (synWbr (.cv y) (.cv r) (.cv z)) (.objEq y z))))))
      p0004 p0094
  have p0096 :=
    @gOpabbi2i
      (.all x (.imp (synWa (synWss (.cv x) (.cv a)) (synWne (.cv x) (synC0)))
          (synWrex z (.cv x)
            (synWral y (.cv x) (.imp (synWbr (.cv y) (.cv r) (.cv z)) (.objEq y z))))))
      r a
      (synCcompl (synCrn (synCtxp (synCcompl (synCima (synCin (synCins3 (synCsset))
                  (synCcompl (synCima (synCin (synCins2 (synCins3 (synCsset))) (synCdif
                          (synCima (synCin (synCins4 (synCsi3 (synCid)))
                              (synCins2 (synCins2 (synCins2 (synCsset))))) (synC1c))
                          (synCins3 (synCid)))) (synC1c)))) (synC1c)))
            (synCin (synCsset) (synCxp (synCcompl (synCsn (synC0))) (synCvv))))))
      dv_cache_0022 dv_cache_0023 dv_cache_0024 p0095
  have p0097 :=
    @gEqtr4i (synCfound)
      (synCopab r a (.all x (.imp (synWa (synWss (.cv x) (.cv a)) (synWne (.cv x) (synC0)))
            (synWrex z (.cv x) (synWral y (.cv x)
                (.imp (synWbr (.cv y) (.cv r) (.cv z)) (.objEq y z)))))))
      (synCcompl (synCrn (synCtxp (synCcompl (synCima (synCin (synCins3 (synCsset))
                  (synCcompl (synCima (synCin (synCins2 (synCins3 (synCsset))) (synCdif
                          (synCima (synCin (synCins4 (synCsi3 (synCid)))
                              (synCins2 (synCins2 (synCins2 (synCsset))))) (synC1c))
                          (synCins3 (synCid)))) (synC1c)))) (synC1c)))
            (synCin (synCsset) (synCxp (synCcompl (synCsn (synC0))) (synCvv))))))
      p0000 p0096
  have p0098 := @gSsetex
  have p0099 := @gIns3ex (synCsset) p0098
  have p0100 := @gIns2ex (synCins3 (synCsset)) p0099
  have p0101 := @gIdex
  have p0102 := @gSi3ex (synCid) p0101
  have p0103 := @gIns4ex (synCsi3 (synCid)) p0102
  have p0105 := @gIns2ex (synCsset) p0098
  have p0106 := @gIns2ex (synCins2 (synCsset)) p0105
  have p0107 := @gIns2ex (synCins2 (synCins2 (synCsset))) p0106
  have p0108 :=
    @gInex (synCins4 (synCsi3 (synCid)))
      (synCins2 (synCins2 (synCins2 (synCsset)))) p0103 p0107
  have p0109 := @gN1cex
  have p0110 :=
    @gImaex
      (synCin (synCins4 (synCsi3 (synCid))) (synCins2 (synCins2 (synCins2 (synCsset)))))
      (synC1c) p0108 p0109
  have p0112 := @gIns3ex (synCid) p0101
  have p0113 :=
    @gDifex
      (synCima (synCin (synCins4 (synCsi3 (synCid)))
          (synCins2 (synCins2 (synCins2 (synCsset))))) (synC1c))
      (synCins3 (synCid)) p0110 p0112
  have p0114 :=
    @gInex (synCins2 (synCins3 (synCsset)))
      (synCdif (synCima (synCin (synCins4 (synCsi3 (synCid)))
            (synCins2 (synCins2 (synCins2 (synCsset))))) (synC1c)) (synCins3 (synCid)))
      p0100 p0113
  have p0116 :=
    @gImaex
      (synCin (synCins2 (synCins3 (synCsset))) (synCdif (synCima
            (synCin (synCins4 (synCsi3 (synCid)))
              (synCins2 (synCins2 (synCins2 (synCsset))))) (synC1c))
          (synCins3 (synCid))))
      (synC1c) p0114 p0109
  have p0117 :=
    @gComplex
      (synCima (synCin (synCins2 (synCins3 (synCsset))) (synCdif (synCima
              (synCin (synCins4 (synCsi3 (synCid)))
                (synCins2 (synCins2 (synCins2 (synCsset))))) (synC1c))
            (synCins3 (synCid)))) (synC1c))
      p0116
  have p0118 :=
    @gInex (synCins3 (synCsset))
      (synCcompl (synCima (synCin (synCins2 (synCins3 (synCsset))) (synCdif (synCima
                (synCin (synCins4 (synCsi3 (synCid)))
                  (synCins2 (synCins2 (synCins2 (synCsset))))) (synC1c))
              (synCins3 (synCid)))) (synC1c)))
      p0099 p0117
  have p0120 :=
    @gImaex
      (synCin (synCins3 (synCsset)) (synCcompl (synCima
            (synCin (synCins2 (synCins3 (synCsset))) (synCdif (synCima
                  (synCin (synCins4 (synCsi3 (synCid)))
                    (synCins2 (synCins2 (synCins2 (synCsset))))) (synC1c))
                (synCins3 (synCid)))) (synC1c))))
      (synC1c) p0118 p0109
  have p0121 :=
    @gComplex
      (synCima (synCin (synCins3 (synCsset)) (synCcompl (synCima
              (synCin (synCins2 (synCins3 (synCsset))) (synCdif (synCima
                    (synCin (synCins4 (synCsi3 (synCid)))
                      (synCins2 (synCins2 (synCins2 (synCsset))))) (synC1c))
                  (synCins3 (synCid)))) (synC1c)))) (synC1c))
      p0120
  have p0123 := @gSnex (synC0)
  have p0124 := @gComplex (synCsn (synC0)) p0123
  have p0125 := @gVvex
  have p0126 := @gXpex (synCcompl (synCsn (synC0))) (synCvv) p0124 p0125
  have p0127 :=
    @gInex (synCsset) (synCxp (synCcompl (synCsn (synC0))) (synCvv)) p0098 p0126
  have p0128 :=
    @gTxpex
      (synCcompl (synCima (synCin (synCins3 (synCsset)) (synCcompl (synCima
                (synCin (synCins2 (synCins3 (synCsset))) (synCdif (synCima
                      (synCin (synCins4 (synCsi3 (synCid)))
                        (synCins2 (synCins2 (synCins2 (synCsset))))) (synC1c))
                    (synCins3 (synCid)))) (synC1c)))) (synC1c)))
      (synCin (synCsset) (synCxp (synCcompl (synCsn (synC0))) (synCvv))) p0121
      p0127
  have p0129 :=
    @gRnex
      (synCtxp (synCcompl (synCima (synCin (synCins3 (synCsset)) (synCcompl (synCima
                  (synCin (synCins2 (synCins3 (synCsset))) (synCdif (synCima
                        (synCin (synCins4 (synCsi3 (synCid)))
                          (synCins2 (synCins2 (synCins2 (synCsset))))) (synC1c))
                      (synCins3 (synCid)))) (synC1c)))) (synC1c)))
        (synCin (synCsset) (synCxp (synCcompl (synCsn (synC0))) (synCvv))))
      p0128
  have p0130 :=
    @gComplex
      (synCrn (synCtxp (synCcompl (synCima (synCin (synCins3 (synCsset)) (synCcompl
                  (synCima (synCin (synCins2 (synCins3 (synCsset))) (synCdif (synCima
                          (synCin (synCins4 (synCsi3 (synCid)))
                            (synCins2 (synCins2 (synCins2 (synCsset))))) (synC1c))
                        (synCins3 (synCid)))) (synC1c)))) (synC1c)))
          (synCin (synCsset) (synCxp (synCcompl (synCsn (synC0))) (synCvv)))))
      p0129
  have p0131 :=
    @gEqeltri (synCfound)
      (synCcompl (synCrn (synCtxp (synCcompl (synCima (synCin (synCins3 (synCsset))
                  (synCcompl (synCima (synCin (synCins2 (synCins3 (synCsset))) (synCdif
                          (synCima (synCin (synCins4 (synCsi3 (synCid)))
                              (synCins2 (synCins2 (synCins2 (synCsset))))) (synC1c))
                          (synCins3 (synCid)))) (synC1c)))) (synC1c)))
            (synCin (synCsset) (synCxp (synCcompl (synCsn (synC0))) (synCvv))))))
      (synCvv) p0097 p0130
  exact p0131


end NFChoice.DirectNominalPrf.WPPReplay

end

/-! Certificates from `NominalWPPReplayChunk013Compact001Part023`. -/


section

namespace NFChoice.DirectNominalPrf.WPPReplay

open scoped Fol
open NFChoice.Foundation
open NFChoice.SemanticCore
open NFChoice.ReplaySupport
open NFChoice.Compiler.CompactSourceSyntax

/-- Checked nominal proof certificate identified upstream as `g_partialex`. -/
@[expose]
noncomputable def gPartialex : Nominal.NPrf (.classMem (synCpartial) (synCvv)) :=
  by
  have p0000 := (Nominal.classEqRefl (synCpartial))
  have p0001 := @gRefex
  have p0002 := @gTransex
  have p0003 := @gInex (synCref) (synCtrans) p0001 p0002
  have p0004 := @gAntisymex
  have p0005 := @gInex (synCin (synCref) (synCtrans)) (synCantisym) p0003 p0004
  have p0006 :=
    @gEqeltri (synCpartial) (synCin (synCin (synCref) (synCtrans)) (synCantisym))
      (synCvv) p0000 p0005
  exact p0006

/-- Checked nominal proof certificate identified upstream as `g_strictex`. -/
@[expose]
noncomputable def gStrictex : Nominal.NPrf (.classMem (synCstrict) (synCvv)) :=
  by
  have p0000 := (Nominal.classEqRefl (synCstrict))
  have p0001 := @gPartialex
  have p0002 := @gConnexex
  have p0003 := @gInex (synCpartial) (synCconnex) p0001 p0002
  have p0004 :=
    @gEqeltri (synCstrict) (synCin (synCpartial) (synCconnex)) (synCvv) p0000 p0003
  exact p0004

/-- Checked nominal proof certificate identified upstream as `g_weex`. -/
@[expose]
noncomputable def gWeex : Nominal.NPrf (.classMem (synCwe) (synCvv)) :=
  by
  have p0000 := (Nominal.classEqRefl (synCwe))
  have p0001 := @gStrictex
  have p0002 := @gFoundex
  have p0003 := @gInex (synCstrict) (synCfound) p0001 p0002
  have p0004 :=
    @gEqeltri (synCwe) (synCin (synCstrict) (synCfound)) (synCvv) p0000 p0003
  exact p0004

/-- Checked nominal proof certificate identified upstream as `g_trd`. -/
@[expose]
noncomputable def gTrd (ph : Wff) (A : Class) (R : Class) (X : Class) (Y : Class)
    (Z : Class) (hyp_trd_1 : Nominal.NPrf (.imp ph (synWbr R (synCtrans) A)))
    (hyp_trd_2 : Nominal.NPrf (.imp ph (.classMem X A)))
    (hyp_trd_3 : Nominal.NPrf (.imp ph (.classMem Y A)))
    (hyp_trd_4 : Nominal.NPrf (.imp ph (.classMem Z A)))
    (hyp_trd_5 : Nominal.NPrf (.imp ph (synWbr X R Y)))
    (hyp_trd_6 : Nominal.NPrf (.imp ph (synWbr Y R Z))) :
    Nominal.NPrf (.imp ph (synWbr X R Z)) :=
  by
  let proofSupport : Finset Var := ph.fv ∪ A.fv ∪ R.fv ∪ X.fv ∪ Y.fv ∪ Z.fv
  let x : Var := freshVar proofSupport 0
  let y : Var := freshVar proofSupport 1
  let z : Var := freshVar proofSupport 2
  let r : Var := freshVar proofSupport 3
  let a : Var := freshVar proofSupport 4
  have fresh_x : x ∉ proofSupport :=
    by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_x_not_A : x ∉ A.fv := by
    intro h
    exact
      fresh_x
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _
              (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))))
  have fresh_x_not_R : x ∉ R.fv := by
    intro h
    exact
      fresh_x
        (Finset.mem_union_left _ (Finset.mem_union_left _
            (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))))
  have fresh_x_not_X : x ∉ X.fv := by
    intro h
    exact
      fresh_x
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))
  have fresh_y : y ∉ proofSupport :=
    by
    change freshVar proofSupport 1 ∉ proofSupport
    exact freshVar_not_mem proofSupport 1
  have fresh_y_not_A : y ∉ A.fv := by
    intro h
    exact
      fresh_y
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _
              (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))))
  have fresh_y_not_R : y ∉ R.fv := by
    intro h
    exact
      fresh_y
        (Finset.mem_union_left _ (Finset.mem_union_left _
            (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))))
  have fresh_y_not_X : y ∉ X.fv := by
    intro h
    exact
      fresh_y
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))
  have fresh_y_not_Y : y ∉ Y.fv := by
    intro h
    exact fresh_y (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_z : z ∉ proofSupport :=
    by
    change freshVar proofSupport 2 ∉ proofSupport
    exact freshVar_not_mem proofSupport 2
  have fresh_z_not_A : z ∉ A.fv := by
    intro h
    exact
      fresh_z
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _
              (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))))
  have fresh_z_not_R : z ∉ R.fv := by
    intro h
    exact
      fresh_z
        (Finset.mem_union_left _ (Finset.mem_union_left _
            (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))))
  have fresh_z_not_X : z ∉ X.fv := by
    intro h
    exact
      fresh_z
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))
  have fresh_z_not_Y : z ∉ Y.fv := by
    intro h
    exact fresh_z (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_z_not_Z : z ∉ Z.fv := by
    intro h
    exact fresh_z (Finset.mem_union_right _ (h))
  have fresh_r : r ∉ proofSupport :=
    by
    change freshVar proofSupport 3 ∉ proofSupport
    exact freshVar_not_mem proofSupport 3
  have fresh_r_not_A : r ∉ A.fv := by
    intro h
    exact
      fresh_r
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _
              (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))))
  have fresh_r_not_R : r ∉ R.fv := by
    intro h
    exact
      fresh_r
        (Finset.mem_union_left _ (Finset.mem_union_left _
            (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))))
  have fresh_a : a ∉ proofSupport :=
    by
    change freshVar proofSupport 4 ∉ proofSupport
    exact freshVar_not_mem proofSupport 4
  have fresh_a_not_A : a ∉ A.fv := by
    intro h
    exact
      fresh_a
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _
              (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))))
  have fresh_a_not_R : a ∉ R.fv := by
    intro h
    exact
      fresh_a
        (Finset.mem_union_left _ (Finset.mem_union_left _
            (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))))
  have fresh_x_ne_y : x ≠ y :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have fresh_x_ne_z : x ≠ z :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 2
    exact freshVar_injective proofSupport (i := 0) (j := 2) (by decide)
  have fresh_x_ne_r : x ≠ r :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 3
    exact freshVar_injective proofSupport (i := 0) (j := 3) (by decide)
  have fresh_r_ne_x : r ≠ x := Ne.symm fresh_x_ne_r
  have fresh_x_ne_a : x ≠ a :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 4
    exact freshVar_injective proofSupport (i := 0) (j := 4) (by decide)
  have fresh_a_ne_x : a ≠ x := Ne.symm fresh_x_ne_a
  have fresh_y_ne_z : y ≠ z :=
    by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 2
    exact freshVar_injective proofSupport (i := 1) (j := 2) (by decide)
  have fresh_y_ne_r : y ≠ r :=
    by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 3
    exact freshVar_injective proofSupport (i := 1) (j := 3) (by decide)
  have fresh_r_ne_y : r ≠ y := Ne.symm fresh_y_ne_r
  have fresh_y_ne_a : y ≠ a :=
    by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 4
    exact freshVar_injective proofSupport (i := 1) (j := 4) (by decide)
  have fresh_a_ne_y : a ≠ y := Ne.symm fresh_y_ne_a
  have fresh_z_ne_r : z ≠ r :=
    by
    change freshVar proofSupport 2 ≠ freshVar proofSupport 3
    exact freshVar_injective proofSupport (i := 2) (j := 3) (by decide)
  have fresh_r_ne_z : r ≠ z := Ne.symm fresh_z_ne_r
  have fresh_z_ne_a : z ≠ a :=
    by
    change freshVar proofSupport 2 ≠ freshVar proofSupport 4
    exact freshVar_injective proofSupport (i := 2) (j := 4) (by decide)
  have fresh_a_ne_z : a ≠ z := Ne.symm fresh_z_ne_a
  have fresh_r_ne_a : r ≠ a :=
    by
    change freshVar proofSupport 3 ≠ freshVar proofSupport 4
    exact freshVar_injective proofSupport (i := 3) (j := 4) (by decide)
  have fresh_a_ne_r : a ≠ r := Ne.symm fresh_r_ne_a
  have dv_cache_0001 : z ∉ ((Wff.classEq (.cv r) R)).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, fresh_z_ne_r, fresh_z_not_R, or_false, not_false_eq_true])
  have dv_cache_0002 : x ∉ ((Wff.classEq (.cv r) R)).fv :=
    by
    clear dv_cache_0001
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, fresh_x_ne_r, fresh_x_not_R, or_false, not_false_eq_true])
  have dv_cache_0003 : y ∉ ((Wff.classEq (.cv r) R)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, fresh_y_ne_r, fresh_y_not_R, or_false, not_false_eq_true])
  have dv_cache_0004 : z ∉ ((Class.cv a)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact
      (by
        have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_z_ne_a, not_false_eq_true])
  have dv_cache_0005 : z ∉ (A).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact
      (by
        have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_z_not_A, not_false_eq_true])
  have dv_cache_0006 : y ∉ ((Class.cv a)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_y_ne_a, not_false_eq_true])
  have dv_cache_0007 : y ∉ (A).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_y_not_A, not_false_eq_true])
  have dv_cache_0008 : x ∉ ((Class.cv a)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_x_ne_a, not_false_eq_true])
  have dv_cache_0009 : x ∉ (A).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_x_not_A, not_false_eq_true])
  have dv_cache_0010 : a ≠ r :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009
    exact (show a ≠ r from (by exact fresh_a_ne_r))
  have dv_cache_0011 : a ≠ x :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010
    exact (show a ≠ x from (by exact fresh_a_ne_x))
  have dv_cache_0012 : a ≠ y :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
    exact (show a ≠ y from (by exact fresh_a_ne_y))
  have dv_cache_0013 : a ≠ z :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012
    exact (show a ≠ z from (by exact fresh_a_ne_z))
  have dv_cache_0014 : r ≠ x :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013
    exact (show r ≠ x from (by exact fresh_r_ne_x))
  have dv_cache_0015 : r ≠ y :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014
    exact (show r ≠ y from (by exact fresh_r_ne_y))
  have dv_cache_0016 : r ≠ z :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015
    exact (show r ≠ z from (by exact fresh_r_ne_z))
  have dv_cache_0017 : x ≠ y :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016
    exact (show x ≠ y from (by exact fresh_x_ne_y))
  have dv_cache_0018 : x ≠ z :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
    exact (show x ≠ z from (by exact fresh_x_ne_z))
  have dv_cache_0019 : y ≠ z :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018
    exact (show y ≠ z from (by exact fresh_y_ne_z))
  have dv_cache_0020 : r ∉ (R).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019
    exact
      (by
        have compact_fv_not_mem_empty : r ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_r_not_R, not_false_eq_true])
  have dv_cache_0021 : a ∉ (R).fv :=
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
        simp only [fresh_a_not_R, not_false_eq_true])
  have dv_cache_0022 : r ∉ (A).fv :=
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
        simp only [fresh_r_not_A, not_false_eq_true])
  have dv_cache_0023 : a ∉ (A).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022
    exact
      (by
        have compact_fv_not_mem_empty : a ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_a_not_A, not_false_eq_true])
  have dv_cache_0024 :
    r ∉
      ((synWral x A (synWral y A (synWral z A
              (.imp (synWa (synWbr (.cv x) R (.cv y)) (synWbr (.cv y) R (.cv z)))
                (synWbr (.cv x) R (.cv z))))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
    exact
      (by
        have compact_fv_not_mem_empty : r ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wral,
          NFChoice.Compiler.CoreFVSimp.fv_wff_imp,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase,
          Finset.mem_singleton, fresh_r_not_A, fresh_r_ne_x, fresh_r_ne_y, fresh_r_not_R,
          fresh_r_ne_z, or_false, and_false, not_false_eq_true])
  have dv_cache_0025 :
    a ∉
      ((synWral x A (synWral y A (synWral z A
              (.imp (synWa (synWbr (.cv x) R (.cv y)) (synWbr (.cv y) R (.cv z)))
                (synWbr (.cv x) R (.cv z))))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024
    exact
      (by
        have compact_fv_not_mem_empty : a ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wral,
          NFChoice.Compiler.CoreFVSimp.fv_wff_imp,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase,
          Finset.mem_singleton, fresh_a_not_A, fresh_a_ne_x, fresh_a_ne_y, fresh_a_not_R,
          fresh_a_ne_z, or_false, and_false, not_false_eq_true])
  have dv_cache_0026 : r ≠ a :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025
    exact (show r ≠ a from (by exact fresh_r_ne_a))
  have dv_cache_0027 : x ∉ (X).fv :=
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
        simp only [fresh_x_not_X, not_false_eq_true])
  have dv_cache_0028 : y ∉ (X).fv :=
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
        simp only [fresh_y_not_X, not_false_eq_true])
  have dv_cache_0029 : z ∉ (X).fv :=
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
        simp only [fresh_z_not_X, not_false_eq_true])
  have dv_cache_0030 : y ∉ (Y).fv :=
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
        simp only [fresh_y_not_Y, not_false_eq_true])
  have dv_cache_0031 : z ∉ (Y).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
      dv_cache_0030
    exact
      (by
        have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_z_not_Y, not_false_eq_true])
  have dv_cache_0032 : z ∉ (Z).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
      dv_cache_0030 dv_cache_0031
    exact
      (by
        have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_z_not_Z, not_false_eq_true])
  have dv_cache_0033 :
    x ∉
      ((Wff.imp (synWa (synWbr X R (.cv y)) (synWbr (.cv y) R (.cv z)))
          (synWbr X R (.cv z)))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
      dv_cache_0030 dv_cache_0031 dv_cache_0032
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, fresh_x_not_X, fresh_x_ne_y, fresh_x_not_R, fresh_x_ne_z,
          or_false, not_false_eq_true])
  have dv_cache_0034 :
    z ∉ ((Wff.imp (synWa (synWbr X R Y) (synWbr Y R Z)) (synWbr X R Z))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
      dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033
    exact
      (by
        have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr, Finset.mem_union,
          fresh_z_not_X, fresh_z_not_Y, fresh_z_not_R, fresh_z_not_Z, or_false,
          not_false_eq_true])
  have dv_cache_0035 :
    y ∉
      ((Wff.imp (synWa (synWbr X R Y) (synWbr Y R (.cv z))) (synWbr X R (.cv z)))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
      dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, fresh_y_not_X, fresh_y_not_Y, fresh_y_not_R, fresh_y_ne_z,
          or_false, not_false_eq_true])
  have p0000 := @gBrex R A (synCtrans)
  have p0001 := @gBreq (.cv x) (.cv y) (.cv r) R
  have p0002 := @gBreq (.cv y) (.cv z) (.cv r) R
  have p0003 :=
    @gAnbi12d (.classEq (.cv r) R) (synWbr (.cv x) (.cv r) (.cv y))
      (synWbr (.cv x) R (.cv y)) (synWbr (.cv y) (.cv r) (.cv z))
      (synWbr (.cv y) R (.cv z)) p0001 p0002
  have p0004 := @gBreq (.cv x) (.cv z) (.cv r) R
  have p0005 :=
    @gImbi12d (.classEq (.cv r) R)
      (synWa (synWbr (.cv x) (.cv r) (.cv y)) (synWbr (.cv y) (.cv r) (.cv z)))
      (synWa (synWbr (.cv x) R (.cv y)) (synWbr (.cv y) R (.cv z)))
      (synWbr (.cv x) (.cv r) (.cv z)) (synWbr (.cv x) R (.cv z)) p0003 p0004
  have p0006 :=
    @gRalbidv (.classEq (.cv r) R)
      (.imp (synWa (synWbr (.cv x) (.cv r) (.cv y)) (synWbr (.cv y) (.cv r) (.cv z)))
        (synWbr (.cv x) (.cv r) (.cv z)))
      (.imp (synWa (synWbr (.cv x) R (.cv y)) (synWbr (.cv y) R (.cv z)))
        (synWbr (.cv x) R (.cv z)))
      z (.cv a) dv_cache_0001 p0005
  have p0007 :=
    @gN2ralbidv (.classEq (.cv r) R)
      (synWral z (.cv a)
        (.imp (synWa (synWbr (.cv x) (.cv r) (.cv y)) (synWbr (.cv y) (.cv r) (.cv z)))
          (synWbr (.cv x) (.cv r) (.cv z))))
      (synWral z (.cv a) (.imp (synWa (synWbr (.cv x) R (.cv y)) (synWbr (.cv y) R (.cv z)))
          (synWbr (.cv x) R (.cv z))))
      x y (.cv a) (.cv a) dv_cache_0002 dv_cache_0003 p0006
  have p0008 :=
    @gRaleq
      (.imp (synWa (synWbr (.cv x) R (.cv y)) (synWbr (.cv y) R (.cv z)))
        (synWbr (.cv x) R (.cv z)))
      z (.cv a) A dv_cache_0004 dv_cache_0005
  have p0009 :=
    @gRaleqbi1dv
      (synWral z (.cv a) (.imp (synWa (synWbr (.cv x) R (.cv y)) (synWbr (.cv y) R (.cv z)))
          (synWbr (.cv x) R (.cv z))))
      (synWral z A (.imp (synWa (synWbr (.cv x) R (.cv y)) (synWbr (.cv y) R (.cv z)))
          (synWbr (.cv x) R (.cv z))))
      y (.cv a) A dv_cache_0006 dv_cache_0007 p0008
  have p0010 :=
    @gRaleqbi1dv
      (synWral y (.cv a) (synWral z (.cv a)
          (.imp (synWa (synWbr (.cv x) R (.cv y)) (synWbr (.cv y) R (.cv z)))
            (synWbr (.cv x) R (.cv z)))))
      (synWral y A (synWral z A
          (.imp (synWa (synWbr (.cv x) R (.cv y)) (synWbr (.cv y) R (.cv z)))
            (synWbr (.cv x) R (.cv z)))))
      x (.cv a) A dv_cache_0008 dv_cache_0009 p0009
  have p0011 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominalDfTrans x y z r a
      dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015
      dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019
  have p0012 :=
    @gBrabg
      (synWral x (.cv a) (synWral y (.cv a) (synWral z (.cv a) (.imp
              (synWa (synWbr (.cv x) (.cv r) (.cv y)) (synWbr (.cv y) (.cv r) (.cv z)))
              (synWbr (.cv x) (.cv r) (.cv z))))))
      (synWral x (.cv a) (synWral y (.cv a) (synWral z (.cv a)
            (.imp (synWa (synWbr (.cv x) R (.cv y)) (synWbr (.cv y) R (.cv z)))
              (synWbr (.cv x) R (.cv z))))))
      (synWral x A (synWral y A (synWral z A
            (.imp (synWa (synWbr (.cv x) R (.cv y)) (synWbr (.cv y) R (.cv z)))
              (synWbr (.cv x) R (.cv z))))))
      r a R A (synCvv) (synCvv) (synCtrans) dv_cache_0020 dv_cache_0021 dv_cache_0022
      dv_cache_0023 dv_cache_0024 dv_cache_0025 dv_cache_0026 p0007 p0010 p0011
  have p0013 :=
    @gSyl (synWbr R (synCtrans) A)
      (synWa (.classMem R (synCvv)) (.classMem A (synCvv)))
      (synWb (synWbr R (synCtrans) A) (synWral x A (synWral y A (synWral z A
              (.imp (synWa (synWbr (.cv x) R (.cv y)) (synWbr (.cv y) R (.cv z)))
                (synWbr (.cv x) R (.cv z)))))))
      p0000 p0012
  have p0014 :=
    @gIbi (synWbr R (synCtrans) A)
      (synWral x A (synWral y A (synWral z A
            (.imp (synWa (synWbr (.cv x) R (.cv y)) (synWbr (.cv y) R (.cv z)))
              (synWbr (.cv x) R (.cv z))))))
      p0013
  have p0015 :=
    @gSyl ph (synWbr R (synCtrans) A)
      (synWral x A (synWral y A (synWral z A
            (.imp (synWa (synWbr (.cv x) R (.cv y)) (synWbr (.cv y) R (.cv z)))
              (synWbr (.cv x) R (.cv z))))))
      hyp_trd_1 p0014
  have p0016 := @gBreq1 (.cv x) X (.cv y) R
  have p0017 :=
    @gAnbi1d (.classEq (.cv x) X) (synWbr (.cv x) R (.cv y)) (synWbr X R (.cv y))
      (synWbr (.cv y) R (.cv z)) p0016
  have p0018 := @gBreq1 (.cv x) X (.cv z) R
  have p0019 :=
    @gImbi12d (.classEq (.cv x) X)
      (synWa (synWbr (.cv x) R (.cv y)) (synWbr (.cv y) R (.cv z)))
      (synWa (synWbr X R (.cv y)) (synWbr (.cv y) R (.cv z)))
      (synWbr (.cv x) R (.cv z)) (synWbr X R (.cv z)) p0017 p0018
  have p0020 := @gBreq2 (.cv y) Y X R
  have p0021 := @gBreq1 (.cv y) Y (.cv z) R
  have p0022 :=
    @gAnbi12d (.classEq (.cv y) Y) (synWbr X R (.cv y)) (synWbr X R Y)
      (synWbr (.cv y) R (.cv z)) (synWbr Y R (.cv z)) p0020 p0021
  have p0023 :=
    @gImbi1d (.classEq (.cv y) Y)
      (synWa (synWbr X R (.cv y)) (synWbr (.cv y) R (.cv z)))
      (synWa (synWbr X R Y) (synWbr Y R (.cv z))) (synWbr X R (.cv z)) p0022
  have p0024 := @gBreq2 (.cv z) Z Y R
  have p0025 :=
    @gAnbi2d (.classEq (.cv z) Z) (synWbr Y R (.cv z)) (synWbr Y R Z) (synWbr X R Y)
      p0024
  have p0026 := @gBreq2 (.cv z) Z X R
  have p0027 :=
    @gImbi12d (.classEq (.cv z) Z) (synWa (synWbr X R Y) (synWbr Y R (.cv z)))
      (synWa (synWbr X R Y) (synWbr Y R Z)) (synWbr X R (.cv z)) (synWbr X R Z) p0025
      p0026
  have p0028 :=
    @gRspc3v
      (.imp (synWa (synWbr (.cv x) R (.cv y)) (synWbr (.cv y) R (.cv z)))
        (synWbr (.cv x) R (.cv z)))
      (.imp (synWa (synWbr X R Y) (synWbr Y R Z)) (synWbr X R Z))
      (.imp (synWa (synWbr X R (.cv y)) (synWbr (.cv y) R (.cv z))) (synWbr X R (.cv z)))
      (.imp (synWa (synWbr X R Y) (synWbr Y R (.cv z))) (synWbr X R (.cv z))) x y z X
      Y Z A A A dv_cache_0027 dv_cache_0028 dv_cache_0029 dv_cache_0030 dv_cache_0031
      dv_cache_0032 dv_cache_0009 dv_cache_0009 dv_cache_0007 dv_cache_0009 dv_cache_0007
      dv_cache_0005 dv_cache_0033 dv_cache_0034 dv_cache_0035 dv_cache_0017 dv_cache_0018
      dv_cache_0019 p0019 p0023 p0027
  have p0029 :=
    @gSyl3anc ph (.classMem X A) (.classMem Y A) (.classMem Z A)
      (.imp (synWral x A (synWral y A (synWral z A
              (.imp (synWa (synWbr (.cv x) R (.cv y)) (synWbr (.cv y) R (.cv z)))
                (synWbr (.cv x) R (.cv z))))))
        (.imp (synWa (synWbr X R Y) (synWbr Y R Z)) (synWbr X R Z)))
      hyp_trd_2 hyp_trd_3 hyp_trd_4 p0028
  have p0030 :=
    @gMpd ph
      (synWral x A (synWral y A (synWral z A
            (.imp (synWa (synWbr (.cv x) R (.cv y)) (synWbr (.cv y) R (.cv z)))
              (synWbr (.cv x) R (.cv z))))))
      (.imp (synWa (synWbr X R Y) (synWbr Y R Z)) (synWbr X R Z)) p0015 p0029
  have p0031 :=
    @gMp2and ph (synWbr X R Y) (synWbr Y R Z) (synWbr X R Z) hyp_trd_5 hyp_trd_6 p0030
  exact p0031


end NFChoice.DirectNominalPrf.WPPReplay

end
