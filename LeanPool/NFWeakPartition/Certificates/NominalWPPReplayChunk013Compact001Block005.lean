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

@[expose]
noncomputable def g_antisymex : Nominal.NPrf (.classMem (syn_cantisym) (syn_cvv)) :=
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
    p ∉ ((syn_cop (syn_csn (.cv y)) (syn_cop (syn_csn (.cv x)) (.cv r)))).fv :=
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
      ((syn_cin (syn_cins4 (syn_csi3 (syn_ctxp (syn_c2nd) (syn_c1st))))
          (syn_cins2 (syn_cins2 (syn_csset))))).fv :=
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
  have dv_cache_0009 : p ∉ ((syn_cop (.cv x) (.cv y))).fv :=
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
      ((syn_cin (syn_cins4 (syn_csi3 (syn_cid))) (syn_cins2 (syn_cins2 (syn_csset))))).fv :=
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
  have dv_cache_0012 : p ∉ ((syn_cop (.cv y) (.cv x))).fv :=
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
  have dv_cache_0013 : y ∉ ((syn_cop (syn_csn (.cv x)) (syn_cop (.cv r) (.cv a)))).fv :=
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
      ((syn_cin (syn_cins2 (syn_cins2 (syn_csset))) (syn_cins4 (syn_cdif (syn_cin (syn_cima
                  (syn_cin (syn_cins4 (syn_csi3 (syn_ctxp (syn_c2nd) (syn_c1st))))
                    (syn_cins2 (syn_cins2 (syn_csset)))) (syn_c1c)) (syn_cima
                  (syn_cin (syn_cins4 (syn_csi3 (syn_cid))) (syn_cins2 (syn_cins2 (syn_csset))))
                  (syn_c1c))) (syn_cins3 (syn_cid)))))).fv :=
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
  have dv_cache_0015 : x ∉ ((syn_cop (.cv r) (.cv a))).fv :=
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
      ((syn_cin (syn_cins2 (syn_csset)) (syn_cima (syn_cin (syn_cins2 (syn_cins2 (syn_csset)))
              (syn_cins4 (syn_cdif (syn_cin (syn_cima
                      (syn_cin (syn_cins4 (syn_csi3 (syn_ctxp (syn_c2nd) (syn_c1st))))
                        (syn_cins2 (syn_cins2 (syn_csset)))) (syn_c1c)) (syn_cima
                      (syn_cin (syn_cins4 (syn_csi3 (syn_cid)))
                        (syn_cins2 (syn_cins2 (syn_csset)))) (syn_c1c)))
                  (syn_cins3 (syn_cid))))) (syn_c1c)))).fv :=
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
      ((syn_ccompl (syn_cima (syn_cin (syn_cins2 (syn_csset)) (syn_cima
                (syn_cin (syn_cins2 (syn_cins2 (syn_csset))) (syn_cins4 (syn_cdif (syn_cin
                        (syn_cima
                          (syn_cin (syn_cins4 (syn_csi3 (syn_ctxp (syn_c2nd) (syn_c1st))))
                            (syn_cins2 (syn_cins2 (syn_csset)))) (syn_c1c)) (syn_cima
                          (syn_cin (syn_cins4 (syn_csi3 (syn_cid)))
                            (syn_cins2 (syn_cins2 (syn_csset)))) (syn_c1c)))
                      (syn_cins3 (syn_cid))))) (syn_c1c))) (syn_c1c)))).fv :=
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
      ((syn_ccompl (syn_cima (syn_cin (syn_cins2 (syn_csset)) (syn_cima
                (syn_cin (syn_cins2 (syn_cins2 (syn_csset))) (syn_cins4 (syn_cdif (syn_cin
                        (syn_cima
                          (syn_cin (syn_cins4 (syn_csi3 (syn_ctxp (syn_c2nd) (syn_c1st))))
                            (syn_cins2 (syn_cins2 (syn_csset)))) (syn_c1c)) (syn_cima
                          (syn_cin (syn_cins4 (syn_csi3 (syn_cid)))
                            (syn_cins2 (syn_cins2 (syn_csset)))) (syn_c1c)))
                      (syn_cins3 (syn_cid))))) (syn_c1c))) (syn_c1c)))).fv :=
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
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominal_df_antisym x y r a
      dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006
  have p0001 := @g_vex r
  have p0002 := @g_vex a
  have p0003 := @g_opex (.cv r) (.cv a) p0001 p0002
  have p0004 :=
    @g_elcompl (syn_cop (.cv r) (.cv a))
      (syn_cima (syn_cin (syn_cins2 (syn_csset)) (syn_cima
            (syn_cin (syn_cins2 (syn_cins2 (syn_csset))) (syn_cins4 (syn_cdif (syn_cin (syn_cima
                      (syn_cin (syn_cins4 (syn_csi3 (syn_ctxp (syn_c2nd) (syn_c1st))))
                        (syn_cins2 (syn_cins2 (syn_csset)))) (syn_c1c)) (syn_cima
                      (syn_cin (syn_cins4 (syn_csi3 (syn_cid)))
                        (syn_cins2 (syn_cins2 (syn_csset)))) (syn_c1c)))
                  (syn_cins3 (syn_cid))))) (syn_c1c))) (syn_c1c))
      p0003
  have p0005 :=
    @g_elin (syn_cop (syn_csn (.cv x)) (syn_cop (.cv r) (.cv a))) (syn_cins2 (syn_csset))
      (syn_cima (syn_cin (syn_cins2 (syn_cins2 (syn_csset))) (syn_cins4 (syn_cdif (syn_cin
                (syn_cima (syn_cin (syn_cins4 (syn_csi3 (syn_ctxp (syn_c2nd) (syn_c1st))))
                    (syn_cins2 (syn_cins2 (syn_csset)))) (syn_c1c)) (syn_cima
                  (syn_cin (syn_cins4 (syn_csi3 (syn_cid))) (syn_cins2 (syn_cins2 (syn_csset))))
                  (syn_c1c))) (syn_cins3 (syn_cid))))) (syn_c1c))
  have p0006 := @g_otelins2 (syn_csn (.cv x)) (.cv r) (.cv a) (syn_csset) p0001
  have p0007 := @g_vex x
  have p0008 := @g_opelssetsn (.cv x) (.cv a) p0007 p0002
  have p0009_e01_recanon :
    Nominal.NPrf
      (syn_wb (.classMem (syn_cop (syn_csn (.cv x)) (.cv a)) (syn_csset)) (.objMem x a)) :=
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
      p0008
  have p0009 :=
    @g_bitri
      (.classMem (syn_cop (syn_csn (.cv x)) (syn_cop (.cv r) (.cv a))) (syn_cins2 (syn_csset)))
      (.classMem (syn_cop (syn_csn (.cv x)) (.cv a)) (syn_csset)) (.objMem x a) p0006
      p0009_e01_recanon
  have p0010 :=
    @g_elin
      (syn_cop (syn_csn (.cv y)) (syn_cop (syn_csn (.cv x)) (syn_cop (.cv r) (.cv a))))
      (syn_cins2 (syn_cins2 (syn_csset)))
      (syn_cins4 (syn_cdif (syn_cin (syn_cima
              (syn_cin (syn_cins4 (syn_csi3 (syn_ctxp (syn_c2nd) (syn_c1st))))
                (syn_cins2 (syn_cins2 (syn_csset)))) (syn_c1c)) (syn_cima
              (syn_cin (syn_cins4 (syn_csi3 (syn_cid))) (syn_cins2 (syn_cins2 (syn_csset))))
              (syn_c1c))) (syn_cins3 (syn_cid))))
  have p0011 := @g_snex (.cv x)
  have p0012 :=
    @g_otelins2 (syn_csn (.cv y)) (syn_csn (.cv x)) (syn_cop (.cv r) (.cv a))
      (syn_cins2 (syn_csset)) p0011
  have p0013 := @g_otelins2 (syn_csn (.cv y)) (.cv r) (.cv a) (syn_csset) p0001
  have p0014 := @g_vex y
  have p0015 := @g_opelssetsn (.cv y) (.cv a) p0014 p0002
  have p0016_e02_recanon :
    Nominal.NPrf
      (syn_wb (.classMem (syn_cop (syn_csn (.cv y)) (.cv a)) (syn_csset)) (.objMem y a)) :=
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
      p0015
  have p0016 :=
    @g_n_3bitri
      (.classMem
        (syn_cop (syn_csn (.cv y)) (syn_cop (syn_csn (.cv x)) (syn_cop (.cv r) (.cv a))))
        (syn_cins2 (syn_cins2 (syn_csset))))
      (.classMem (syn_cop (syn_csn (.cv y)) (syn_cop (.cv r) (.cv a))) (syn_cins2 (syn_csset)))
      (.classMem (syn_cop (syn_csn (.cv y)) (.cv a)) (syn_csset)) (.objMem y a) p0012
      p0013 p0016_e02_recanon
  have p0017 :=
    @g_oqelins4 (syn_csn (.cv y)) (syn_csn (.cv x)) (.cv r) (.cv a)
      (syn_cdif (syn_cin (syn_cima
            (syn_cin (syn_cins4 (syn_csi3 (syn_ctxp (syn_c2nd) (syn_c1st))))
              (syn_cins2 (syn_cins2 (syn_csset)))) (syn_c1c)) (syn_cima
            (syn_cin (syn_cins4 (syn_csi3 (syn_cid))) (syn_cins2 (syn_cins2 (syn_csset))))
            (syn_c1c))) (syn_cins3 (syn_cid)))
      p0002
  have p0018 :=
    @g_eldif (syn_cop (syn_csn (.cv y)) (syn_cop (syn_csn (.cv x)) (.cv r)))
      (syn_cin (syn_cima (syn_cin (syn_cins4 (syn_csi3 (syn_ctxp (syn_c2nd) (syn_c1st))))
            (syn_cins2 (syn_cins2 (syn_csset)))) (syn_c1c)) (syn_cima
          (syn_cin (syn_cins4 (syn_csi3 (syn_cid))) (syn_cins2 (syn_cins2 (syn_csset))))
          (syn_c1c)))
      (syn_cins3 (syn_cid))
  have p0019 :=
    @g_elin (syn_cop (syn_csn (.cv y)) (syn_cop (syn_csn (.cv x)) (.cv r)))
      (syn_cima (syn_cin (syn_cins4 (syn_csi3 (syn_ctxp (syn_c2nd) (syn_c1st))))
          (syn_cins2 (syn_cins2 (syn_csset)))) (syn_c1c))
      (syn_cima (syn_cin (syn_cins4 (syn_csi3 (syn_cid))) (syn_cins2 (syn_cins2 (syn_csset))))
        (syn_c1c))
  have p0020 :=
    @g_elin
      (syn_cop (syn_csn (.cv p))
        (syn_cop (syn_csn (.cv y)) (syn_cop (syn_csn (.cv x)) (.cv r))))
      (syn_cins4 (syn_csi3 (syn_ctxp (syn_c2nd) (syn_c1st))))
      (syn_cins2 (syn_cins2 (syn_csset)))
  have p0021 :=
    @g_oqelins4 (syn_csn (.cv p)) (syn_csn (.cv y)) (syn_csn (.cv x)) (.cv r)
      (syn_csi3 (syn_ctxp (syn_c2nd) (syn_c1st))) p0001
  have p0022 := @g_vex p
  have p0023 :=
    @g_otsnelsi3 (.cv p) (.cv y) (.cv x) (syn_ctxp (syn_c2nd) (syn_c1st)) p0022 p0014
      p0007
  have p0024 := @g_oteltxp (.cv p) (.cv y) (.cv x) (syn_c2nd) (syn_c1st)
  have p0025 :=
    @g_ancom (.classMem (syn_cop (.cv p) (.cv y)) (syn_c2nd))
      (.classMem (syn_cop (.cv p) (.cv x)) (syn_c1st))
  have p0026 := (Nominal.biimpRefl (syn_wbr (.cv p) (syn_c1st) (.cv x)))
  have p0027 := (Nominal.biimpRefl (syn_wbr (.cv p) (syn_c2nd) (.cv y)))
  have p0028 :=
    @g_anbi12i (syn_wbr (.cv p) (syn_c1st) (.cv x))
      (.classMem (syn_cop (.cv p) (.cv x)) (syn_c1st))
      (syn_wbr (.cv p) (syn_c2nd) (.cv y))
      (.classMem (syn_cop (.cv p) (.cv y)) (syn_c2nd)) p0026 p0027
  have p0029 :=
    @g_bitr4i
      (syn_wa (.classMem (syn_cop (.cv p) (.cv y)) (syn_c2nd))
        (.classMem (syn_cop (.cv p) (.cv x)) (syn_c1st)))
      (syn_wa (.classMem (syn_cop (.cv p) (.cv x)) (syn_c1st))
        (.classMem (syn_cop (.cv p) (.cv y)) (syn_c2nd)))
      (syn_wa (syn_wbr (.cv p) (syn_c1st) (.cv x)) (syn_wbr (.cv p) (syn_c2nd) (.cv y)))
      p0025 p0028
  have p0030 := @g_op1st2nd (.cv x) (.cv y) (.cv p) p0007 p0014
  have p0031 :=
    @g_n_3bitri
      (.classMem (syn_cop (.cv p) (syn_cop (.cv y) (.cv x))) (syn_ctxp (syn_c2nd) (syn_c1st)))
      (syn_wa (.classMem (syn_cop (.cv p) (.cv y)) (syn_c2nd))
        (.classMem (syn_cop (.cv p) (.cv x)) (syn_c1st)))
      (syn_wa (syn_wbr (.cv p) (syn_c1st) (.cv x)) (syn_wbr (.cv p) (syn_c2nd) (.cv y)))
      (.classEq (.cv p) (syn_cop (.cv x) (.cv y))) p0024 p0029 p0030
  have p0032 :=
    @g_n_3bitri
      (.classMem (syn_cop (syn_csn (.cv p))
          (syn_cop (syn_csn (.cv y)) (syn_cop (syn_csn (.cv x)) (.cv r))))
        (syn_cins4 (syn_csi3 (syn_ctxp (syn_c2nd) (syn_c1st)))))
      (.classMem (syn_cop (syn_csn (.cv p)) (syn_cop (syn_csn (.cv y)) (syn_csn (.cv x))))
        (syn_csi3 (syn_ctxp (syn_c2nd) (syn_c1st))))
      (.classMem (syn_cop (.cv p) (syn_cop (.cv y) (.cv x))) (syn_ctxp (syn_c2nd) (syn_c1st)))
      (.classEq (.cv p) (syn_cop (.cv x) (.cv y))) p0021 p0023 p0031
  have p0033 := @g_snex (.cv y)
  have p0034 :=
    @g_otelins2 (syn_csn (.cv p)) (syn_csn (.cv y)) (syn_cop (syn_csn (.cv x)) (.cv r))
      (syn_cins2 (syn_csset)) p0033
  have p0035 := @g_otelins2 (syn_csn (.cv p)) (syn_csn (.cv x)) (.cv r) (syn_csset) p0011
  have p0036 := @g_opelssetsn (.cv p) (.cv r) p0022 p0001
  have p0037_e02_recanon :
    Nominal.NPrf
      (syn_wb (.classMem (syn_cop (syn_csn (.cv p)) (.cv r)) (syn_csset)) (.objMem p r)) :=
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
      p0036
  have p0037 :=
    @g_n_3bitri
      (.classMem (syn_cop (syn_csn (.cv p))
          (syn_cop (syn_csn (.cv y)) (syn_cop (syn_csn (.cv x)) (.cv r))))
        (syn_cins2 (syn_cins2 (syn_csset))))
      (.classMem (syn_cop (syn_csn (.cv p)) (syn_cop (syn_csn (.cv x)) (.cv r)))
        (syn_cins2 (syn_csset)))
      (.classMem (syn_cop (syn_csn (.cv p)) (.cv r)) (syn_csset)) (.objMem p r) p0034
      p0035 p0037_e02_recanon
  have p0038 :=
    @g_anbi12i
      (.classMem (syn_cop (syn_csn (.cv p))
          (syn_cop (syn_csn (.cv y)) (syn_cop (syn_csn (.cv x)) (.cv r))))
        (syn_cins4 (syn_csi3 (syn_ctxp (syn_c2nd) (syn_c1st)))))
      (.classEq (.cv p) (syn_cop (.cv x) (.cv y)))
      (.classMem (syn_cop (syn_csn (.cv p))
          (syn_cop (syn_csn (.cv y)) (syn_cop (syn_csn (.cv x)) (.cv r))))
        (syn_cins2 (syn_cins2 (syn_csset))))
      (.objMem p r) p0032 p0037
  have p0039 :=
    @g_bitri
      (.classMem (syn_cop (syn_csn (.cv p))
          (syn_cop (syn_csn (.cv y)) (syn_cop (syn_csn (.cv x)) (.cv r))))
        (syn_cin (syn_cins4 (syn_csi3 (syn_ctxp (syn_c2nd) (syn_c1st))))
          (syn_cins2 (syn_cins2 (syn_csset)))))
      (syn_wa (.classMem (syn_cop (syn_csn (.cv p))
            (syn_cop (syn_csn (.cv y)) (syn_cop (syn_csn (.cv x)) (.cv r))))
          (syn_cins4 (syn_csi3 (syn_ctxp (syn_c2nd) (syn_c1st))))) (.classMem
          (syn_cop (syn_csn (.cv p))
            (syn_cop (syn_csn (.cv y)) (syn_cop (syn_csn (.cv x)) (.cv r))))
          (syn_cins2 (syn_cins2 (syn_csset)))))
      (syn_wa (.classEq (.cv p) (syn_cop (.cv x) (.cv y))) (.objMem p r)) p0020 p0038
  have p0040 :=
    @g_exbii
      (.classMem (syn_cop (syn_csn (.cv p))
          (syn_cop (syn_csn (.cv y)) (syn_cop (syn_csn (.cv x)) (.cv r))))
        (syn_cin (syn_cins4 (syn_csi3 (syn_ctxp (syn_c2nd) (syn_c1st))))
          (syn_cins2 (syn_cins2 (syn_csset)))))
      (syn_wa (.classEq (.cv p) (syn_cop (.cv x) (.cv y))) (.objMem p r)) p p0039
  have p0041 :=
    @g_elima1c p (syn_cop (syn_csn (.cv y)) (syn_cop (syn_csn (.cv x)) (.cv r)))
      (syn_cin (syn_cins4 (syn_csi3 (syn_ctxp (syn_c2nd) (syn_c1st))))
        (syn_cins2 (syn_cins2 (syn_csset))))
      dv_cache_0007 dv_cache_0008
  have p0042 := (Nominal.biimpRefl (syn_wbr (.cv x) (.cv r) (.cv y)))
  have p0043 :=
    (NFChoice.DirectNominalPrf.Nominal.DefinitionLeafHandlersCanonical001.dfClelOfDV p
      (syn_cop (.cv x) (.cv y)) (.cv r) dv_cache_0009 dv_cache_0010)
  have p0044_e01_recanon :
    Nominal.NPrf
      (syn_wb (.classMem (syn_cop (.cv x) (.cv y)) (.cv r)) (syn_wex p
          (syn_wa (.classEq (.cv p) (syn_cop (.cv x) (.cv y))) (.objMem p r)))) :=
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
      p0043
  have p0044 :=
    @g_bitri (syn_wbr (.cv x) (.cv r) (.cv y))
      (.classMem (syn_cop (.cv x) (.cv y)) (.cv r))
      (syn_wex p (syn_wa (.classEq (.cv p) (syn_cop (.cv x) (.cv y))) (.objMem p r)))
      p0042 p0044_e01_recanon
  have p0045 :=
    @g_n_3bitr4i
      (syn_wex p (.classMem (syn_cop (syn_csn (.cv p))
            (syn_cop (syn_csn (.cv y)) (syn_cop (syn_csn (.cv x)) (.cv r))))
          (syn_cin (syn_cins4 (syn_csi3 (syn_ctxp (syn_c2nd) (syn_c1st))))
            (syn_cins2 (syn_cins2 (syn_csset))))))
      (syn_wex p (syn_wa (.classEq (.cv p) (syn_cop (.cv x) (.cv y))) (.objMem p r)))
      (.classMem (syn_cop (syn_csn (.cv y)) (syn_cop (syn_csn (.cv x)) (.cv r))) (syn_cima
          (syn_cin (syn_cins4 (syn_csi3 (syn_ctxp (syn_c2nd) (syn_c1st))))
            (syn_cins2 (syn_cins2 (syn_csset)))) (syn_c1c)))
      (syn_wbr (.cv x) (.cv r) (.cv y)) p0040 p0041 p0044
  have p0046 :=
    @g_elin
      (syn_cop (syn_csn (.cv p))
        (syn_cop (syn_csn (.cv y)) (syn_cop (syn_csn (.cv x)) (.cv r))))
      (syn_cins4 (syn_csi3 (syn_cid))) (syn_cins2 (syn_cins2 (syn_csset)))
  have p0047 :=
    @g_oqelins4 (syn_csn (.cv p)) (syn_csn (.cv y)) (syn_csn (.cv x)) (.cv r)
      (syn_csi3 (syn_cid)) p0001
  have p0048 := @g_otsnelsi3 (.cv p) (.cv y) (.cv x) (syn_cid) p0022 p0014 p0007
  have p0049 := (Nominal.biimpRefl (syn_wbr (.cv p) (syn_cid) (syn_cop (.cv y) (.cv x))))
  have p0050 := @g_opex (.cv y) (.cv x) p0014 p0007
  have p0051 := @g_ideq (.cv p) (syn_cop (.cv y) (.cv x)) p0050
  have p0052 :=
    @g_n_3bitr2i
      (.classMem (syn_cop (syn_csn (.cv p)) (syn_cop (syn_csn (.cv y)) (syn_csn (.cv x))))
        (syn_csi3 (syn_cid)))
      (.classMem (syn_cop (.cv p) (syn_cop (.cv y) (.cv x))) (syn_cid))
      (syn_wbr (.cv p) (syn_cid) (syn_cop (.cv y) (.cv x)))
      (.classEq (.cv p) (syn_cop (.cv y) (.cv x))) p0048 p0049 p0051
  have p0053 :=
    @g_bitri
      (.classMem (syn_cop (syn_csn (.cv p))
          (syn_cop (syn_csn (.cv y)) (syn_cop (syn_csn (.cv x)) (.cv r))))
        (syn_cins4 (syn_csi3 (syn_cid))))
      (.classMem (syn_cop (syn_csn (.cv p)) (syn_cop (syn_csn (.cv y)) (syn_csn (.cv x))))
        (syn_csi3 (syn_cid)))
      (.classEq (.cv p) (syn_cop (.cv y) (.cv x))) p0047 p0052
  have p0054 :=
    @g_anbi12i
      (.classMem (syn_cop (syn_csn (.cv p))
          (syn_cop (syn_csn (.cv y)) (syn_cop (syn_csn (.cv x)) (.cv r))))
        (syn_cins4 (syn_csi3 (syn_cid))))
      (.classEq (.cv p) (syn_cop (.cv y) (.cv x)))
      (.classMem (syn_cop (syn_csn (.cv p))
          (syn_cop (syn_csn (.cv y)) (syn_cop (syn_csn (.cv x)) (.cv r))))
        (syn_cins2 (syn_cins2 (syn_csset))))
      (.objMem p r) p0053 p0037
  have p0055 :=
    @g_bitri
      (.classMem (syn_cop (syn_csn (.cv p))
          (syn_cop (syn_csn (.cv y)) (syn_cop (syn_csn (.cv x)) (.cv r))))
        (syn_cin (syn_cins4 (syn_csi3 (syn_cid))) (syn_cins2 (syn_cins2 (syn_csset)))))
      (syn_wa (.classMem (syn_cop (syn_csn (.cv p))
            (syn_cop (syn_csn (.cv y)) (syn_cop (syn_csn (.cv x)) (.cv r))))
          (syn_cins4 (syn_csi3 (syn_cid)))) (.classMem (syn_cop (syn_csn (.cv p))
            (syn_cop (syn_csn (.cv y)) (syn_cop (syn_csn (.cv x)) (.cv r))))
          (syn_cins2 (syn_cins2 (syn_csset)))))
      (syn_wa (.classEq (.cv p) (syn_cop (.cv y) (.cv x))) (.objMem p r)) p0046 p0054
  have p0056 :=
    @g_exbii
      (.classMem (syn_cop (syn_csn (.cv p))
          (syn_cop (syn_csn (.cv y)) (syn_cop (syn_csn (.cv x)) (.cv r))))
        (syn_cin (syn_cins4 (syn_csi3 (syn_cid))) (syn_cins2 (syn_cins2 (syn_csset)))))
      (syn_wa (.classEq (.cv p) (syn_cop (.cv y) (.cv x))) (.objMem p r)) p p0055
  have p0057 :=
    @g_elima1c p (syn_cop (syn_csn (.cv y)) (syn_cop (syn_csn (.cv x)) (.cv r)))
      (syn_cin (syn_cins4 (syn_csi3 (syn_cid))) (syn_cins2 (syn_cins2 (syn_csset))))
      dv_cache_0007 dv_cache_0011
  have p0058 := (Nominal.biimpRefl (syn_wbr (.cv y) (.cv r) (.cv x)))
  have p0059 :=
    (NFChoice.DirectNominalPrf.Nominal.DefinitionLeafHandlersCanonical001.dfClelOfDV p
      (syn_cop (.cv y) (.cv x)) (.cv r) dv_cache_0012 dv_cache_0010)
  have p0060_e01_recanon :
    Nominal.NPrf
      (syn_wb (.classMem (syn_cop (.cv y) (.cv x)) (.cv r)) (syn_wex p
          (syn_wa (.classEq (.cv p) (syn_cop (.cv y) (.cv x))) (.objMem p r)))) :=
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
      p0059
  have p0060 :=
    @g_bitri (syn_wbr (.cv y) (.cv r) (.cv x))
      (.classMem (syn_cop (.cv y) (.cv x)) (.cv r))
      (syn_wex p (syn_wa (.classEq (.cv p) (syn_cop (.cv y) (.cv x))) (.objMem p r)))
      p0058 p0060_e01_recanon
  have p0061 :=
    @g_n_3bitr4i
      (syn_wex p (.classMem (syn_cop (syn_csn (.cv p))
            (syn_cop (syn_csn (.cv y)) (syn_cop (syn_csn (.cv x)) (.cv r))))
          (syn_cin (syn_cins4 (syn_csi3 (syn_cid))) (syn_cins2 (syn_cins2 (syn_csset))))))
      (syn_wex p (syn_wa (.classEq (.cv p) (syn_cop (.cv y) (.cv x))) (.objMem p r)))
      (.classMem (syn_cop (syn_csn (.cv y)) (syn_cop (syn_csn (.cv x)) (.cv r))) (syn_cima
          (syn_cin (syn_cins4 (syn_csi3 (syn_cid))) (syn_cins2 (syn_cins2 (syn_csset))))
          (syn_c1c)))
      (syn_wbr (.cv y) (.cv r) (.cv x)) p0056 p0057 p0060
  have p0062 :=
    @g_anbi12i
      (.classMem (syn_cop (syn_csn (.cv y)) (syn_cop (syn_csn (.cv x)) (.cv r))) (syn_cima
          (syn_cin (syn_cins4 (syn_csi3 (syn_ctxp (syn_c2nd) (syn_c1st))))
            (syn_cins2 (syn_cins2 (syn_csset)))) (syn_c1c)))
      (syn_wbr (.cv x) (.cv r) (.cv y))
      (.classMem (syn_cop (syn_csn (.cv y)) (syn_cop (syn_csn (.cv x)) (.cv r))) (syn_cima
          (syn_cin (syn_cins4 (syn_csi3 (syn_cid))) (syn_cins2 (syn_cins2 (syn_csset))))
          (syn_c1c)))
      (syn_wbr (.cv y) (.cv r) (.cv x)) p0045 p0061
  have p0063 :=
    @g_bitri
      (.classMem (syn_cop (syn_csn (.cv y)) (syn_cop (syn_csn (.cv x)) (.cv r))) (syn_cin
          (syn_cima (syn_cin (syn_cins4 (syn_csi3 (syn_ctxp (syn_c2nd) (syn_c1st))))
              (syn_cins2 (syn_cins2 (syn_csset)))) (syn_c1c)) (syn_cima
            (syn_cin (syn_cins4 (syn_csi3 (syn_cid))) (syn_cins2 (syn_cins2 (syn_csset))))
            (syn_c1c))))
      (syn_wa (.classMem (syn_cop (syn_csn (.cv y)) (syn_cop (syn_csn (.cv x)) (.cv r)))
          (syn_cima (syn_cin (syn_cins4 (syn_csi3 (syn_ctxp (syn_c2nd) (syn_c1st))))
              (syn_cins2 (syn_cins2 (syn_csset)))) (syn_c1c)))
        (.classMem (syn_cop (syn_csn (.cv y)) (syn_cop (syn_csn (.cv x)) (.cv r))) (syn_cima
            (syn_cin (syn_cins4 (syn_csi3 (syn_cid))) (syn_cins2 (syn_cins2 (syn_csset))))
            (syn_c1c))))
      (syn_wa (syn_wbr (.cv x) (.cv r) (.cv y)) (syn_wbr (.cv y) (.cv r) (.cv x))) p0019
      p0062
  have p0064 := @g_otelins3 (syn_csn (.cv y)) (syn_csn (.cv x)) (.cv r) (syn_cid) p0001
  have p0065 :=
    (Nominal.biimpRefl (syn_wbr (syn_csn (.cv y)) (syn_cid) (syn_csn (.cv x))))
  have p0066 := @g_ideq (syn_csn (.cv y)) (syn_csn (.cv x)) p0011
  have p0067 := @g_eqcom (syn_csn (.cv y)) (syn_csn (.cv x))
  have p0068 := @g_sneqb (.cv x) (.cv y) p0007
  have p0069_e02_recanon :
    Nominal.NPrf (syn_wb (.classEq (syn_csn (.cv x)) (syn_csn (.cv y))) (.objEq x y)) :=
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
      p0068
  have p0069 :=
    @g_n_3bitri (syn_wbr (syn_csn (.cv y)) (syn_cid) (syn_csn (.cv x)))
      (.classEq (syn_csn (.cv y)) (syn_csn (.cv x)))
      (.classEq (syn_csn (.cv x)) (syn_csn (.cv y))) (.objEq x y) p0066 p0067
      p0069_e02_recanon
  have p0070 :=
    @g_n_3bitr2i
      (.classMem (syn_cop (syn_csn (.cv y)) (syn_cop (syn_csn (.cv x)) (.cv r)))
        (syn_cins3 (syn_cid)))
      (.classMem (syn_cop (syn_csn (.cv y)) (syn_csn (.cv x))) (syn_cid))
      (syn_wbr (syn_csn (.cv y)) (syn_cid) (syn_csn (.cv x))) (.objEq x y) p0064 p0065
      p0069
  have p0071 :=
    @g_notbii
      (.classMem (syn_cop (syn_csn (.cv y)) (syn_cop (syn_csn (.cv x)) (.cv r)))
        (syn_cins3 (syn_cid)))
      (.objEq x y) p0070
  have p0072 :=
    @g_anbi12i
      (.classMem (syn_cop (syn_csn (.cv y)) (syn_cop (syn_csn (.cv x)) (.cv r))) (syn_cin
          (syn_cima (syn_cin (syn_cins4 (syn_csi3 (syn_ctxp (syn_c2nd) (syn_c1st))))
              (syn_cins2 (syn_cins2 (syn_csset)))) (syn_c1c)) (syn_cima
            (syn_cin (syn_cins4 (syn_csi3 (syn_cid))) (syn_cins2 (syn_cins2 (syn_csset))))
            (syn_c1c))))
      (syn_wa (syn_wbr (.cv x) (.cv r) (.cv y)) (syn_wbr (.cv y) (.cv r) (.cv x)))
      (.neg (.classMem (syn_cop (syn_csn (.cv y)) (syn_cop (syn_csn (.cv x)) (.cv r)))
          (syn_cins3 (syn_cid))))
      (.neg (.objEq x y)) p0063 p0071
  have p0073 :=
    @g_n_3bitri
      (.classMem
        (syn_cop (syn_csn (.cv y)) (syn_cop (syn_csn (.cv x)) (syn_cop (.cv r) (.cv a))))
        (syn_cins4 (syn_cdif (syn_cin (syn_cima
                (syn_cin (syn_cins4 (syn_csi3 (syn_ctxp (syn_c2nd) (syn_c1st))))
                  (syn_cins2 (syn_cins2 (syn_csset)))) (syn_c1c)) (syn_cima
                (syn_cin (syn_cins4 (syn_csi3 (syn_cid))) (syn_cins2 (syn_cins2 (syn_csset))))
                (syn_c1c))) (syn_cins3 (syn_cid)))))
      (.classMem (syn_cop (syn_csn (.cv y)) (syn_cop (syn_csn (.cv x)) (.cv r))) (syn_cdif
          (syn_cin (syn_cima (syn_cin (syn_cins4 (syn_csi3 (syn_ctxp (syn_c2nd) (syn_c1st))))
                (syn_cins2 (syn_cins2 (syn_csset)))) (syn_c1c)) (syn_cima
              (syn_cin (syn_cins4 (syn_csi3 (syn_cid))) (syn_cins2 (syn_cins2 (syn_csset))))
              (syn_c1c))) (syn_cins3 (syn_cid))))
      (syn_wa (.classMem (syn_cop (syn_csn (.cv y)) (syn_cop (syn_csn (.cv x)) (.cv r)))
          (syn_cin (syn_cima (syn_cin (syn_cins4 (syn_csi3 (syn_ctxp (syn_c2nd) (syn_c1st))))
                (syn_cins2 (syn_cins2 (syn_csset)))) (syn_c1c)) (syn_cima
              (syn_cin (syn_cins4 (syn_csi3 (syn_cid))) (syn_cins2 (syn_cins2 (syn_csset))))
              (syn_c1c)))) (.neg
          (.classMem (syn_cop (syn_csn (.cv y)) (syn_cop (syn_csn (.cv x)) (.cv r)))
            (syn_cins3 (syn_cid)))))
      (syn_wa (syn_wa (syn_wbr (.cv x) (.cv r) (.cv y)) (syn_wbr (.cv y) (.cv r) (.cv x)))
        (.neg (.objEq x y)))
      p0017 p0018 p0072
  have p0074 :=
    @g_anbi12i
      (.classMem
        (syn_cop (syn_csn (.cv y)) (syn_cop (syn_csn (.cv x)) (syn_cop (.cv r) (.cv a))))
        (syn_cins2 (syn_cins2 (syn_csset))))
      (.objMem y a)
      (.classMem
        (syn_cop (syn_csn (.cv y)) (syn_cop (syn_csn (.cv x)) (syn_cop (.cv r) (.cv a))))
        (syn_cins4 (syn_cdif (syn_cin (syn_cima
                (syn_cin (syn_cins4 (syn_csi3 (syn_ctxp (syn_c2nd) (syn_c1st))))
                  (syn_cins2 (syn_cins2 (syn_csset)))) (syn_c1c)) (syn_cima
                (syn_cin (syn_cins4 (syn_csi3 (syn_cid))) (syn_cins2 (syn_cins2 (syn_csset))))
                (syn_c1c))) (syn_cins3 (syn_cid)))))
      (syn_wa (syn_wa (syn_wbr (.cv x) (.cv r) (.cv y)) (syn_wbr (.cv y) (.cv r) (.cv x)))
        (.neg (.objEq x y)))
      p0016 p0073
  have p0075 :=
    @g_bitri
      (.classMem
        (syn_cop (syn_csn (.cv y)) (syn_cop (syn_csn (.cv x)) (syn_cop (.cv r) (.cv a))))
        (syn_cin (syn_cins2 (syn_cins2 (syn_csset))) (syn_cins4 (syn_cdif (syn_cin (syn_cima
                  (syn_cin (syn_cins4 (syn_csi3 (syn_ctxp (syn_c2nd) (syn_c1st))))
                    (syn_cins2 (syn_cins2 (syn_csset)))) (syn_c1c)) (syn_cima
                  (syn_cin (syn_cins4 (syn_csi3 (syn_cid))) (syn_cins2 (syn_cins2 (syn_csset))))
                  (syn_c1c))) (syn_cins3 (syn_cid))))))
      (syn_wa (.classMem (syn_cop (syn_csn (.cv y))
            (syn_cop (syn_csn (.cv x)) (syn_cop (.cv r) (.cv a))))
          (syn_cins2 (syn_cins2 (syn_csset)))) (.classMem (syn_cop (syn_csn (.cv y))
            (syn_cop (syn_csn (.cv x)) (syn_cop (.cv r) (.cv a)))) (syn_cins4 (syn_cdif (syn_cin
                (syn_cima (syn_cin (syn_cins4 (syn_csi3 (syn_ctxp (syn_c2nd) (syn_c1st))))
                    (syn_cins2 (syn_cins2 (syn_csset)))) (syn_c1c)) (syn_cima
                  (syn_cin (syn_cins4 (syn_csi3 (syn_cid))) (syn_cins2 (syn_cins2 (syn_csset))))
                  (syn_c1c))) (syn_cins3 (syn_cid))))))
      (syn_wa (.objMem y a) (syn_wa
          (syn_wa (syn_wbr (.cv x) (.cv r) (.cv y)) (syn_wbr (.cv y) (.cv r) (.cv x)))
          (.neg (.objEq x y))))
      p0010 p0074
  have p0076 :=
    @g_exbii
      (.classMem
        (syn_cop (syn_csn (.cv y)) (syn_cop (syn_csn (.cv x)) (syn_cop (.cv r) (.cv a))))
        (syn_cin (syn_cins2 (syn_cins2 (syn_csset))) (syn_cins4 (syn_cdif (syn_cin (syn_cima
                  (syn_cin (syn_cins4 (syn_csi3 (syn_ctxp (syn_c2nd) (syn_c1st))))
                    (syn_cins2 (syn_cins2 (syn_csset)))) (syn_c1c)) (syn_cima
                  (syn_cin (syn_cins4 (syn_csi3 (syn_cid))) (syn_cins2 (syn_cins2 (syn_csset))))
                  (syn_c1c))) (syn_cins3 (syn_cid))))))
      (syn_wa (.objMem y a) (syn_wa
          (syn_wa (syn_wbr (.cv x) (.cv r) (.cv y)) (syn_wbr (.cv y) (.cv r) (.cv x)))
          (.neg (.objEq x y))))
      y p0075
  have p0077 :=
    @g_elima1c y (syn_cop (syn_csn (.cv x)) (syn_cop (.cv r) (.cv a)))
      (syn_cin (syn_cins2 (syn_cins2 (syn_csset))) (syn_cins4 (syn_cdif (syn_cin (syn_cima
                (syn_cin (syn_cins4 (syn_csi3 (syn_ctxp (syn_c2nd) (syn_c1st))))
                  (syn_cins2 (syn_cins2 (syn_csset)))) (syn_c1c)) (syn_cima
                (syn_cin (syn_cins4 (syn_csi3 (syn_cid))) (syn_cins2 (syn_cins2 (syn_csset))))
                (syn_c1c))) (syn_cins3 (syn_cid)))))
      dv_cache_0013 dv_cache_0014
  have p0078 :=
    (Nominal.biimpRefl (syn_wrex y (.cv a) (syn_wa
          (syn_wa (syn_wbr (.cv x) (.cv r) (.cv y)) (syn_wbr (.cv y) (.cv r) (.cv x)))
          (.neg (.objEq x y)))))
  have p0079_e02_recanon :
    Nominal.NPrf
      (syn_wb (syn_wrex y (.cv a) (syn_wa
            (syn_wa (syn_wbr (.cv x) (.cv r) (.cv y)) (syn_wbr (.cv y) (.cv r) (.cv x)))
            (.neg (.objEq x y)))) (syn_wex y (syn_wa (.objMem y a) (syn_wa
              (syn_wa (syn_wbr (.cv x) (.cv r) (.cv y)) (syn_wbr (.cv y) (.cv r) (.cv x)))
              (.neg (.objEq x y)))))) :=
    Nominal.RecanonTransportDev.transport
      (by
        simp only [syn_wb, syn_wrex, syn_wex, syn_wa]
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
    @g_n_3bitr4i
      (syn_wex y (.classMem (syn_cop (syn_csn (.cv y))
            (syn_cop (syn_csn (.cv x)) (syn_cop (.cv r) (.cv a))))
          (syn_cin (syn_cins2 (syn_cins2 (syn_csset))) (syn_cins4 (syn_cdif (syn_cin (syn_cima
                    (syn_cin (syn_cins4 (syn_csi3 (syn_ctxp (syn_c2nd) (syn_c1st))))
                      (syn_cins2 (syn_cins2 (syn_csset)))) (syn_c1c)) (syn_cima
                    (syn_cin (syn_cins4 (syn_csi3 (syn_cid)))
                      (syn_cins2 (syn_cins2 (syn_csset)))) (syn_c1c)))
                (syn_cins3 (syn_cid)))))))
      (syn_wex y (syn_wa (.objMem y a) (syn_wa
            (syn_wa (syn_wbr (.cv x) (.cv r) (.cv y)) (syn_wbr (.cv y) (.cv r) (.cv x)))
            (.neg (.objEq x y)))))
      (.classMem (syn_cop (syn_csn (.cv x)) (syn_cop (.cv r) (.cv a))) (syn_cima
          (syn_cin (syn_cins2 (syn_cins2 (syn_csset))) (syn_cins4 (syn_cdif (syn_cin (syn_cima
                    (syn_cin (syn_cins4 (syn_csi3 (syn_ctxp (syn_c2nd) (syn_c1st))))
                      (syn_cins2 (syn_cins2 (syn_csset)))) (syn_c1c)) (syn_cima
                    (syn_cin (syn_cins4 (syn_csi3 (syn_cid)))
                      (syn_cins2 (syn_cins2 (syn_csset)))) (syn_c1c))) (syn_cins3 (syn_cid)))))
          (syn_c1c)))
      (syn_wrex y (.cv a) (syn_wa
          (syn_wa (syn_wbr (.cv x) (.cv r) (.cv y)) (syn_wbr (.cv y) (.cv r) (.cv x)))
          (.neg (.objEq x y))))
      p0076 p0077 p0079_e02_recanon
  have p0080 :=
    @g_rexanali
      (syn_wa (syn_wbr (.cv x) (.cv r) (.cv y)) (syn_wbr (.cv y) (.cv r) (.cv x)))
      (.objEq x y) y (.cv a)
  have p0081 :=
    @g_bitri
      (.classMem (syn_cop (syn_csn (.cv x)) (syn_cop (.cv r) (.cv a))) (syn_cima
          (syn_cin (syn_cins2 (syn_cins2 (syn_csset))) (syn_cins4 (syn_cdif (syn_cin (syn_cima
                    (syn_cin (syn_cins4 (syn_csi3 (syn_ctxp (syn_c2nd) (syn_c1st))))
                      (syn_cins2 (syn_cins2 (syn_csset)))) (syn_c1c)) (syn_cima
                    (syn_cin (syn_cins4 (syn_csi3 (syn_cid)))
                      (syn_cins2 (syn_cins2 (syn_csset)))) (syn_c1c))) (syn_cins3 (syn_cid)))))
          (syn_c1c)))
      (syn_wrex y (.cv a) (syn_wa
          (syn_wa (syn_wbr (.cv x) (.cv r) (.cv y)) (syn_wbr (.cv y) (.cv r) (.cv x)))
          (.neg (.objEq x y))))
      (.neg (syn_wral y (.cv a) (.imp
            (syn_wa (syn_wbr (.cv x) (.cv r) (.cv y)) (syn_wbr (.cv y) (.cv r) (.cv x)))
            (.objEq x y))))
      p0079 p0080
  have p0082 :=
    @g_anbi12i
      (.classMem (syn_cop (syn_csn (.cv x)) (syn_cop (.cv r) (.cv a))) (syn_cins2 (syn_csset)))
      (.objMem x a)
      (.classMem (syn_cop (syn_csn (.cv x)) (syn_cop (.cv r) (.cv a))) (syn_cima
          (syn_cin (syn_cins2 (syn_cins2 (syn_csset))) (syn_cins4 (syn_cdif (syn_cin (syn_cima
                    (syn_cin (syn_cins4 (syn_csi3 (syn_ctxp (syn_c2nd) (syn_c1st))))
                      (syn_cins2 (syn_cins2 (syn_csset)))) (syn_c1c)) (syn_cima
                    (syn_cin (syn_cins4 (syn_csi3 (syn_cid)))
                      (syn_cins2 (syn_cins2 (syn_csset)))) (syn_c1c))) (syn_cins3 (syn_cid)))))
          (syn_c1c)))
      (.neg (syn_wral y (.cv a) (.imp
            (syn_wa (syn_wbr (.cv x) (.cv r) (.cv y)) (syn_wbr (.cv y) (.cv r) (.cv x)))
            (.objEq x y))))
      p0009 p0081
  have p0083 :=
    @g_bitri
      (.classMem (syn_cop (syn_csn (.cv x)) (syn_cop (.cv r) (.cv a)))
        (syn_cin (syn_cins2 (syn_csset)) (syn_cima (syn_cin (syn_cins2 (syn_cins2 (syn_csset)))
              (syn_cins4 (syn_cdif (syn_cin (syn_cima
                      (syn_cin (syn_cins4 (syn_csi3 (syn_ctxp (syn_c2nd) (syn_c1st))))
                        (syn_cins2 (syn_cins2 (syn_csset)))) (syn_c1c)) (syn_cima
                      (syn_cin (syn_cins4 (syn_csi3 (syn_cid)))
                        (syn_cins2 (syn_cins2 (syn_csset)))) (syn_c1c)))
                  (syn_cins3 (syn_cid))))) (syn_c1c))))
      (syn_wa (.classMem (syn_cop (syn_csn (.cv x)) (syn_cop (.cv r) (.cv a)))
          (syn_cins2 (syn_csset)))
        (.classMem (syn_cop (syn_csn (.cv x)) (syn_cop (.cv r) (.cv a))) (syn_cima
            (syn_cin (syn_cins2 (syn_cins2 (syn_csset))) (syn_cins4 (syn_cdif (syn_cin (syn_cima
                      (syn_cin (syn_cins4 (syn_csi3 (syn_ctxp (syn_c2nd) (syn_c1st))))
                        (syn_cins2 (syn_cins2 (syn_csset)))) (syn_c1c)) (syn_cima
                      (syn_cin (syn_cins4 (syn_csi3 (syn_cid)))
                        (syn_cins2 (syn_cins2 (syn_csset)))) (syn_c1c)))
                  (syn_cins3 (syn_cid))))) (syn_c1c))))
      (syn_wa (.objMem x a) (.neg (syn_wral y (.cv a) (.imp
              (syn_wa (syn_wbr (.cv x) (.cv r) (.cv y)) (syn_wbr (.cv y) (.cv r) (.cv x)))
              (.objEq x y)))))
      p0005 p0082
  have p0084 :=
    @g_exbii
      (.classMem (syn_cop (syn_csn (.cv x)) (syn_cop (.cv r) (.cv a)))
        (syn_cin (syn_cins2 (syn_csset)) (syn_cima (syn_cin (syn_cins2 (syn_cins2 (syn_csset)))
              (syn_cins4 (syn_cdif (syn_cin (syn_cima
                      (syn_cin (syn_cins4 (syn_csi3 (syn_ctxp (syn_c2nd) (syn_c1st))))
                        (syn_cins2 (syn_cins2 (syn_csset)))) (syn_c1c)) (syn_cima
                      (syn_cin (syn_cins4 (syn_csi3 (syn_cid)))
                        (syn_cins2 (syn_cins2 (syn_csset)))) (syn_c1c)))
                  (syn_cins3 (syn_cid))))) (syn_c1c))))
      (syn_wa (.objMem x a) (.neg (syn_wral y (.cv a) (.imp
              (syn_wa (syn_wbr (.cv x) (.cv r) (.cv y)) (syn_wbr (.cv y) (.cv r) (.cv x)))
              (.objEq x y)))))
      x p0083
  have p0085 :=
    @g_elima1c x (syn_cop (.cv r) (.cv a))
      (syn_cin (syn_cins2 (syn_csset)) (syn_cima (syn_cin (syn_cins2 (syn_cins2 (syn_csset)))
            (syn_cins4 (syn_cdif (syn_cin (syn_cima
                    (syn_cin (syn_cins4 (syn_csi3 (syn_ctxp (syn_c2nd) (syn_c1st))))
                      (syn_cins2 (syn_cins2 (syn_csset)))) (syn_c1c)) (syn_cima
                    (syn_cin (syn_cins4 (syn_csi3 (syn_cid)))
                      (syn_cins2 (syn_cins2 (syn_csset)))) (syn_c1c))) (syn_cins3 (syn_cid)))))
          (syn_c1c)))
      dv_cache_0015 dv_cache_0016
  have p0086 :=
    (Nominal.biimpRefl (syn_wrex x (.cv a) (.neg (syn_wral y (.cv a) (.imp
              (syn_wa (syn_wbr (.cv x) (.cv r) (.cv y)) (syn_wbr (.cv y) (.cv r) (.cv x)))
              (.objEq x y))))))
  have p0087_e02_recanon :
    Nominal.NPrf
      (syn_wb (syn_wrex x (.cv a) (.neg (syn_wral y (.cv a) (.imp
                (syn_wa (syn_wbr (.cv x) (.cv r) (.cv y)) (syn_wbr (.cv y) (.cv r) (.cv x)))
                (.objEq x y))))) (syn_wex x (syn_wa (.objMem x a) (.neg (syn_wral y (.cv a)
                (.imp (syn_wa (syn_wbr (.cv x) (.cv r) (.cv y))
                    (syn_wbr (.cv y) (.cv r) (.cv x))) (.objEq x y))))))) :=
    Nominal.RecanonTransportDev.transport
      (by
        simp only [syn_wb, syn_wrex, syn_wex, syn_wa, syn_wral]
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
    @g_n_3bitr4i
      (syn_wex x (.classMem (syn_cop (syn_csn (.cv x)) (syn_cop (.cv r) (.cv a)))
          (syn_cin (syn_cins2 (syn_csset)) (syn_cima
              (syn_cin (syn_cins2 (syn_cins2 (syn_csset))) (syn_cins4 (syn_cdif (syn_cin
                      (syn_cima (syn_cin (syn_cins4 (syn_csi3 (syn_ctxp (syn_c2nd) (syn_c1st))))
                          (syn_cins2 (syn_cins2 (syn_csset)))) (syn_c1c)) (syn_cima
                        (syn_cin (syn_cins4 (syn_csi3 (syn_cid)))
                          (syn_cins2 (syn_cins2 (syn_csset)))) (syn_c1c)))
                    (syn_cins3 (syn_cid))))) (syn_c1c)))))
      (syn_wex x (syn_wa (.objMem x a) (.neg (syn_wral y (.cv a) (.imp
                (syn_wa (syn_wbr (.cv x) (.cv r) (.cv y)) (syn_wbr (.cv y) (.cv r) (.cv x)))
                (.objEq x y))))))
      (.classMem (syn_cop (.cv r) (.cv a)) (syn_cima (syn_cin (syn_cins2 (syn_csset)) (syn_cima
              (syn_cin (syn_cins2 (syn_cins2 (syn_csset))) (syn_cins4 (syn_cdif (syn_cin
                      (syn_cima (syn_cin (syn_cins4 (syn_csi3 (syn_ctxp (syn_c2nd) (syn_c1st))))
                          (syn_cins2 (syn_cins2 (syn_csset)))) (syn_c1c)) (syn_cima
                        (syn_cin (syn_cins4 (syn_csi3 (syn_cid)))
                          (syn_cins2 (syn_cins2 (syn_csset)))) (syn_c1c)))
                    (syn_cins3 (syn_cid))))) (syn_c1c))) (syn_c1c)))
      (syn_wrex x (.cv a) (.neg (syn_wral y (.cv a) (.imp
              (syn_wa (syn_wbr (.cv x) (.cv r) (.cv y)) (syn_wbr (.cv y) (.cv r) (.cv x)))
              (.objEq x y)))))
      p0084 p0085 p0087_e02_recanon
  have p0088 :=
    @g_rexnal
      (syn_wral y (.cv a)
        (.imp (syn_wa (syn_wbr (.cv x) (.cv r) (.cv y)) (syn_wbr (.cv y) (.cv r) (.cv x)))
          (.objEq x y)))
      x (.cv a)
  have p0089 :=
    @g_bitri
      (.classMem (syn_cop (.cv r) (.cv a)) (syn_cima (syn_cin (syn_cins2 (syn_csset)) (syn_cima
              (syn_cin (syn_cins2 (syn_cins2 (syn_csset))) (syn_cins4 (syn_cdif (syn_cin
                      (syn_cima (syn_cin (syn_cins4 (syn_csi3 (syn_ctxp (syn_c2nd) (syn_c1st))))
                          (syn_cins2 (syn_cins2 (syn_csset)))) (syn_c1c)) (syn_cima
                        (syn_cin (syn_cins4 (syn_csi3 (syn_cid)))
                          (syn_cins2 (syn_cins2 (syn_csset)))) (syn_c1c)))
                    (syn_cins3 (syn_cid))))) (syn_c1c))) (syn_c1c)))
      (syn_wrex x (.cv a) (.neg (syn_wral y (.cv a) (.imp
              (syn_wa (syn_wbr (.cv x) (.cv r) (.cv y)) (syn_wbr (.cv y) (.cv r) (.cv x)))
              (.objEq x y)))))
      (.neg (syn_wral x (.cv a) (syn_wral y (.cv a) (.imp
              (syn_wa (syn_wbr (.cv x) (.cv r) (.cv y)) (syn_wbr (.cv y) (.cv r) (.cv x)))
              (.objEq x y)))))
      p0087 p0088
  have p0090 :=
    @g_con2bii
      (.classMem (syn_cop (.cv r) (.cv a)) (syn_cima (syn_cin (syn_cins2 (syn_csset)) (syn_cima
              (syn_cin (syn_cins2 (syn_cins2 (syn_csset))) (syn_cins4 (syn_cdif (syn_cin
                      (syn_cima (syn_cin (syn_cins4 (syn_csi3 (syn_ctxp (syn_c2nd) (syn_c1st))))
                          (syn_cins2 (syn_cins2 (syn_csset)))) (syn_c1c)) (syn_cima
                        (syn_cin (syn_cins4 (syn_csi3 (syn_cid)))
                          (syn_cins2 (syn_cins2 (syn_csset)))) (syn_c1c)))
                    (syn_cins3 (syn_cid))))) (syn_c1c))) (syn_c1c)))
      (syn_wral x (.cv a) (syn_wral y (.cv a) (.imp
            (syn_wa (syn_wbr (.cv x) (.cv r) (.cv y)) (syn_wbr (.cv y) (.cv r) (.cv x)))
            (.objEq x y))))
      p0089
  have p0091 :=
    @g_bitr4i
      (.classMem (syn_cop (.cv r) (.cv a)) (syn_ccompl (syn_cima
            (syn_cin (syn_cins2 (syn_csset)) (syn_cima
                (syn_cin (syn_cins2 (syn_cins2 (syn_csset))) (syn_cins4 (syn_cdif (syn_cin
                        (syn_cima
                          (syn_cin (syn_cins4 (syn_csi3 (syn_ctxp (syn_c2nd) (syn_c1st))))
                            (syn_cins2 (syn_cins2 (syn_csset)))) (syn_c1c)) (syn_cima
                          (syn_cin (syn_cins4 (syn_csi3 (syn_cid)))
                            (syn_cins2 (syn_cins2 (syn_csset)))) (syn_c1c)))
                      (syn_cins3 (syn_cid))))) (syn_c1c))) (syn_c1c))))
      (.neg (.classMem (syn_cop (.cv r) (.cv a)) (syn_cima (syn_cin (syn_cins2 (syn_csset))
              (syn_cima (syn_cin (syn_cins2 (syn_cins2 (syn_csset))) (syn_cins4 (syn_cdif
                      (syn_cin (syn_cima
                          (syn_cin (syn_cins4 (syn_csi3 (syn_ctxp (syn_c2nd) (syn_c1st))))
                            (syn_cins2 (syn_cins2 (syn_csset)))) (syn_c1c)) (syn_cima
                          (syn_cin (syn_cins4 (syn_csi3 (syn_cid)))
                            (syn_cins2 (syn_cins2 (syn_csset)))) (syn_c1c)))
                      (syn_cins3 (syn_cid))))) (syn_c1c))) (syn_c1c))))
      (syn_wral x (.cv a) (syn_wral y (.cv a) (.imp
            (syn_wa (syn_wbr (.cv x) (.cv r) (.cv y)) (syn_wbr (.cv y) (.cv r) (.cv x)))
            (.objEq x y))))
      p0004 p0090
  have p0092 :=
    @g_opabbi2i
      (syn_wral x (.cv a) (syn_wral y (.cv a) (.imp
            (syn_wa (syn_wbr (.cv x) (.cv r) (.cv y)) (syn_wbr (.cv y) (.cv r) (.cv x)))
            (.objEq x y))))
      r a
      (syn_ccompl (syn_cima (syn_cin (syn_cins2 (syn_csset)) (syn_cima
              (syn_cin (syn_cins2 (syn_cins2 (syn_csset))) (syn_cins4 (syn_cdif (syn_cin
                      (syn_cima (syn_cin (syn_cins4 (syn_csi3 (syn_ctxp (syn_c2nd) (syn_c1st))))
                          (syn_cins2 (syn_cins2 (syn_csset)))) (syn_c1c)) (syn_cima
                        (syn_cin (syn_cins4 (syn_csi3 (syn_cid)))
                          (syn_cins2 (syn_cins2 (syn_csset)))) (syn_c1c)))
                    (syn_cins3 (syn_cid))))) (syn_c1c))) (syn_c1c)))
      dv_cache_0017 dv_cache_0018 dv_cache_0019 p0091
  have p0093 :=
    @g_eqtr4i (syn_cantisym)
      (syn_copab r a (syn_wral x (.cv a) (syn_wral y (.cv a) (.imp
              (syn_wa (syn_wbr (.cv x) (.cv r) (.cv y)) (syn_wbr (.cv y) (.cv r) (.cv x)))
              (.objEq x y)))))
      (syn_ccompl (syn_cima (syn_cin (syn_cins2 (syn_csset)) (syn_cima
              (syn_cin (syn_cins2 (syn_cins2 (syn_csset))) (syn_cins4 (syn_cdif (syn_cin
                      (syn_cima (syn_cin (syn_cins4 (syn_csi3 (syn_ctxp (syn_c2nd) (syn_c1st))))
                          (syn_cins2 (syn_cins2 (syn_csset)))) (syn_c1c)) (syn_cima
                        (syn_cin (syn_cins4 (syn_csi3 (syn_cid)))
                          (syn_cins2 (syn_cins2 (syn_csset)))) (syn_c1c)))
                    (syn_cins3 (syn_cid))))) (syn_c1c))) (syn_c1c)))
      p0000 p0092
  have p0094 := @g_ssetex
  have p0095 := @g_ins2ex (syn_csset) p0094
  have p0096 := @g_ins2ex (syn_cins2 (syn_csset)) p0095
  have p0097 := @g_n_2ndex
  have p0098 := @g_n_1stex
  have p0099 := @g_txpex (syn_c2nd) (syn_c1st) p0097 p0098
  have p0100 := @g_si3ex (syn_ctxp (syn_c2nd) (syn_c1st)) p0099
  have p0101 := @g_ins4ex (syn_csi3 (syn_ctxp (syn_c2nd) (syn_c1st))) p0100
  have p0102 :=
    @g_inex (syn_cins4 (syn_csi3 (syn_ctxp (syn_c2nd) (syn_c1st))))
      (syn_cins2 (syn_cins2 (syn_csset))) p0101 p0096
  have p0103 := @g_n_1cex
  have p0104 :=
    @g_imaex
      (syn_cin (syn_cins4 (syn_csi3 (syn_ctxp (syn_c2nd) (syn_c1st))))
        (syn_cins2 (syn_cins2 (syn_csset))))
      (syn_c1c) p0102 p0103
  have p0105 := @g_idex
  have p0106 := @g_si3ex (syn_cid) p0105
  have p0107 := @g_ins4ex (syn_csi3 (syn_cid)) p0106
  have p0108 :=
    @g_inex (syn_cins4 (syn_csi3 (syn_cid))) (syn_cins2 (syn_cins2 (syn_csset))) p0107
      p0096
  have p0110 :=
    @g_imaex
      (syn_cin (syn_cins4 (syn_csi3 (syn_cid))) (syn_cins2 (syn_cins2 (syn_csset))))
      (syn_c1c) p0108 p0103
  have p0111 :=
    @g_inex
      (syn_cima (syn_cin (syn_cins4 (syn_csi3 (syn_ctxp (syn_c2nd) (syn_c1st))))
          (syn_cins2 (syn_cins2 (syn_csset)))) (syn_c1c))
      (syn_cima (syn_cin (syn_cins4 (syn_csi3 (syn_cid))) (syn_cins2 (syn_cins2 (syn_csset))))
        (syn_c1c))
      p0104 p0110
  have p0113 := @g_ins3ex (syn_cid) p0105
  have p0114 :=
    @g_difex
      (syn_cin (syn_cima (syn_cin (syn_cins4 (syn_csi3 (syn_ctxp (syn_c2nd) (syn_c1st))))
            (syn_cins2 (syn_cins2 (syn_csset)))) (syn_c1c)) (syn_cima
          (syn_cin (syn_cins4 (syn_csi3 (syn_cid))) (syn_cins2 (syn_cins2 (syn_csset))))
          (syn_c1c)))
      (syn_cins3 (syn_cid)) p0111 p0113
  have p0115 :=
    @g_ins4ex
      (syn_cdif (syn_cin (syn_cima
            (syn_cin (syn_cins4 (syn_csi3 (syn_ctxp (syn_c2nd) (syn_c1st))))
              (syn_cins2 (syn_cins2 (syn_csset)))) (syn_c1c)) (syn_cima
            (syn_cin (syn_cins4 (syn_csi3 (syn_cid))) (syn_cins2 (syn_cins2 (syn_csset))))
            (syn_c1c))) (syn_cins3 (syn_cid)))
      p0114
  have p0116 :=
    @g_inex (syn_cins2 (syn_cins2 (syn_csset)))
      (syn_cins4 (syn_cdif (syn_cin (syn_cima
              (syn_cin (syn_cins4 (syn_csi3 (syn_ctxp (syn_c2nd) (syn_c1st))))
                (syn_cins2 (syn_cins2 (syn_csset)))) (syn_c1c)) (syn_cima
              (syn_cin (syn_cins4 (syn_csi3 (syn_cid))) (syn_cins2 (syn_cins2 (syn_csset))))
              (syn_c1c))) (syn_cins3 (syn_cid))))
      p0096 p0115
  have p0118 :=
    @g_imaex
      (syn_cin (syn_cins2 (syn_cins2 (syn_csset))) (syn_cins4 (syn_cdif (syn_cin (syn_cima
                (syn_cin (syn_cins4 (syn_csi3 (syn_ctxp (syn_c2nd) (syn_c1st))))
                  (syn_cins2 (syn_cins2 (syn_csset)))) (syn_c1c)) (syn_cima
                (syn_cin (syn_cins4 (syn_csi3 (syn_cid))) (syn_cins2 (syn_cins2 (syn_csset))))
                (syn_c1c))) (syn_cins3 (syn_cid)))))
      (syn_c1c) p0116 p0103
  have p0119 :=
    @g_inex (syn_cins2 (syn_csset))
      (syn_cima (syn_cin (syn_cins2 (syn_cins2 (syn_csset))) (syn_cins4 (syn_cdif (syn_cin
                (syn_cima (syn_cin (syn_cins4 (syn_csi3 (syn_ctxp (syn_c2nd) (syn_c1st))))
                    (syn_cins2 (syn_cins2 (syn_csset)))) (syn_c1c)) (syn_cima
                  (syn_cin (syn_cins4 (syn_csi3 (syn_cid))) (syn_cins2 (syn_cins2 (syn_csset))))
                  (syn_c1c))) (syn_cins3 (syn_cid))))) (syn_c1c))
      p0095 p0118
  have p0121 :=
    @g_imaex
      (syn_cin (syn_cins2 (syn_csset)) (syn_cima (syn_cin (syn_cins2 (syn_cins2 (syn_csset)))
            (syn_cins4 (syn_cdif (syn_cin (syn_cima
                    (syn_cin (syn_cins4 (syn_csi3 (syn_ctxp (syn_c2nd) (syn_c1st))))
                      (syn_cins2 (syn_cins2 (syn_csset)))) (syn_c1c)) (syn_cima
                    (syn_cin (syn_cins4 (syn_csi3 (syn_cid)))
                      (syn_cins2 (syn_cins2 (syn_csset)))) (syn_c1c))) (syn_cins3 (syn_cid)))))
          (syn_c1c)))
      (syn_c1c) p0119 p0103
  have p0122 :=
    @g_complex
      (syn_cima (syn_cin (syn_cins2 (syn_csset)) (syn_cima
            (syn_cin (syn_cins2 (syn_cins2 (syn_csset))) (syn_cins4 (syn_cdif (syn_cin (syn_cima
                      (syn_cin (syn_cins4 (syn_csi3 (syn_ctxp (syn_c2nd) (syn_c1st))))
                        (syn_cins2 (syn_cins2 (syn_csset)))) (syn_c1c)) (syn_cima
                      (syn_cin (syn_cins4 (syn_csi3 (syn_cid)))
                        (syn_cins2 (syn_cins2 (syn_csset)))) (syn_c1c)))
                  (syn_cins3 (syn_cid))))) (syn_c1c))) (syn_c1c))
      p0121
  have p0123 :=
    @g_eqeltri (syn_cantisym)
      (syn_ccompl (syn_cima (syn_cin (syn_cins2 (syn_csset)) (syn_cima
              (syn_cin (syn_cins2 (syn_cins2 (syn_csset))) (syn_cins4 (syn_cdif (syn_cin
                      (syn_cima (syn_cin (syn_cins4 (syn_csi3 (syn_ctxp (syn_c2nd) (syn_c1st))))
                          (syn_cins2 (syn_cins2 (syn_csset)))) (syn_c1c)) (syn_cima
                        (syn_cin (syn_cins4 (syn_csi3 (syn_cid)))
                          (syn_cins2 (syn_cins2 (syn_csset)))) (syn_c1c)))
                    (syn_cins3 (syn_cid))))) (syn_c1c))) (syn_c1c)))
      (syn_cvv) p0093 p0122
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

@[expose]
noncomputable def g_connexex : Nominal.NPrf (.classMem (syn_cconnex) (syn_cvv)) :=
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
  have dv_cache_0007 : x ∉ ((syn_cop (.cv r) (.cv a))).fv :=
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
      ((syn_cin (syn_cins2 (syn_csset)) (syn_cima (syn_cdif (syn_cins2 (syn_cins2 (syn_csset)))
              (syn_cins4 (syn_cun (syn_cima (syn_cin (syn_cins4 (syn_csi3 (syn_cswap)))
                      (syn_cins2 (syn_cins2 (syn_csset)))) (syn_c1c)) (syn_cima
                    (syn_cin (syn_cins4 (syn_csi3 (syn_cid)))
                      (syn_cins2 (syn_cins2 (syn_csset)))) (syn_c1c))))) (syn_c1c)))).fv :=
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
  have dv_cache_0009 : y ∉ ((syn_cop (syn_csn (.cv x)) (syn_cop (.cv r) (.cv a)))).fv :=
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
      ((syn_cdif (syn_cins2 (syn_cins2 (syn_csset))) (syn_cins4 (syn_cun (syn_cima
                (syn_cin (syn_cins4 (syn_csi3 (syn_cswap))) (syn_cins2 (syn_cins2 (syn_csset))))
                (syn_c1c)) (syn_cima (syn_cin (syn_cins4 (syn_csi3 (syn_cid)))
                  (syn_cins2 (syn_cins2 (syn_csset)))) (syn_c1c)))))).fv :=
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
    p ∉ ((syn_cop (syn_csn (.cv y)) (syn_cop (syn_csn (.cv x)) (.cv r)))).fv :=
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
      ((syn_cin (syn_cins4 (syn_csi3 (syn_cswap))) (syn_cins2 (syn_cins2 (syn_csset))))).fv :=
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
  have dv_cache_0013 : p ∉ ((syn_cop (.cv x) (.cv y))).fv :=
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
      ((syn_cin (syn_cins4 (syn_csi3 (syn_cid))) (syn_cins2 (syn_cins2 (syn_csset))))).fv :=
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
  have dv_cache_0016 : p ∉ ((syn_cop (.cv y) (.cv x))).fv :=
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
      ((syn_ccompl (syn_cima (syn_cin (syn_cins2 (syn_csset)) (syn_cima
                (syn_cdif (syn_cins2 (syn_cins2 (syn_csset))) (syn_cins4 (syn_cun (syn_cima
                        (syn_cin (syn_cins4 (syn_csi3 (syn_cswap)))
                          (syn_cins2 (syn_cins2 (syn_csset)))) (syn_c1c)) (syn_cima
                        (syn_cin (syn_cins4 (syn_csi3 (syn_cid)))
                          (syn_cins2 (syn_cins2 (syn_csset)))) (syn_c1c))))) (syn_c1c)))
            (syn_c1c)))).fv :=
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
      ((syn_ccompl (syn_cima (syn_cin (syn_cins2 (syn_csset)) (syn_cima
                (syn_cdif (syn_cins2 (syn_cins2 (syn_csset))) (syn_cins4 (syn_cun (syn_cima
                        (syn_cin (syn_cins4 (syn_csi3 (syn_cswap)))
                          (syn_cins2 (syn_cins2 (syn_csset)))) (syn_c1c)) (syn_cima
                        (syn_cin (syn_cins4 (syn_csi3 (syn_cid)))
                          (syn_cins2 (syn_cins2 (syn_csset)))) (syn_c1c))))) (syn_c1c)))
            (syn_c1c)))).fv :=
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
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominal_df_connex x y r a
      dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006
  have p0001 := @g_vex r
  have p0002 := @g_vex a
  have p0003 := @g_opex (.cv r) (.cv a) p0001 p0002
  have p0004 :=
    @g_elcompl (syn_cop (.cv r) (.cv a))
      (syn_cima (syn_cin (syn_cins2 (syn_csset)) (syn_cima
            (syn_cdif (syn_cins2 (syn_cins2 (syn_csset))) (syn_cins4 (syn_cun (syn_cima
                    (syn_cin (syn_cins4 (syn_csi3 (syn_cswap)))
                      (syn_cins2 (syn_cins2 (syn_csset)))) (syn_c1c)) (syn_cima
                    (syn_cin (syn_cins4 (syn_csi3 (syn_cid)))
                      (syn_cins2 (syn_cins2 (syn_csset)))) (syn_c1c))))) (syn_c1c))) (syn_c1c))
      p0003
  have p0005 :=
    @g_elima1c x (syn_cop (.cv r) (.cv a))
      (syn_cin (syn_cins2 (syn_csset)) (syn_cima (syn_cdif (syn_cins2 (syn_cins2 (syn_csset)))
            (syn_cins4 (syn_cun (syn_cima (syn_cin (syn_cins4 (syn_csi3 (syn_cswap)))
                    (syn_cins2 (syn_cins2 (syn_csset)))) (syn_c1c)) (syn_cima
                  (syn_cin (syn_cins4 (syn_csi3 (syn_cid))) (syn_cins2 (syn_cins2 (syn_csset))))
                  (syn_c1c))))) (syn_c1c)))
      dv_cache_0007 dv_cache_0008
  have p0006 :=
    @g_elin (syn_cop (syn_csn (.cv x)) (syn_cop (.cv r) (.cv a))) (syn_cins2 (syn_csset))
      (syn_cima (syn_cdif (syn_cins2 (syn_cins2 (syn_csset))) (syn_cins4 (syn_cun (syn_cima
                (syn_cin (syn_cins4 (syn_csi3 (syn_cswap))) (syn_cins2 (syn_cins2 (syn_csset))))
                (syn_c1c)) (syn_cima (syn_cin (syn_cins4 (syn_csi3 (syn_cid)))
                  (syn_cins2 (syn_cins2 (syn_csset)))) (syn_c1c))))) (syn_c1c))
  have p0007 := @g_otelins2 (syn_csn (.cv x)) (.cv r) (.cv a) (syn_csset) p0001
  have p0008 := @g_vex x
  have p0009 := @g_opelssetsn (.cv x) (.cv a) p0008 p0002
  have p0010_e01_recanon :
    Nominal.NPrf
      (syn_wb (.classMem (syn_cop (syn_csn (.cv x)) (.cv a)) (syn_csset)) (.objMem x a)) :=
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
      p0009
  have p0010 :=
    @g_bitri
      (.classMem (syn_cop (syn_csn (.cv x)) (syn_cop (.cv r) (.cv a))) (syn_cins2 (syn_csset)))
      (.classMem (syn_cop (syn_csn (.cv x)) (.cv a)) (syn_csset)) (.objMem x a) p0007
      p0010_e01_recanon
  have p0011 :=
    @g_elima1c y (syn_cop (syn_csn (.cv x)) (syn_cop (.cv r) (.cv a)))
      (syn_cdif (syn_cins2 (syn_cins2 (syn_csset))) (syn_cins4 (syn_cun (syn_cima
              (syn_cin (syn_cins4 (syn_csi3 (syn_cswap))) (syn_cins2 (syn_cins2 (syn_csset))))
              (syn_c1c)) (syn_cima (syn_cin (syn_cins4 (syn_csi3 (syn_cid)))
                (syn_cins2 (syn_cins2 (syn_csset)))) (syn_c1c)))))
      dv_cache_0009 dv_cache_0010
  have p0012 :=
    @g_eldif
      (syn_cop (syn_csn (.cv y)) (syn_cop (syn_csn (.cv x)) (syn_cop (.cv r) (.cv a))))
      (syn_cins2 (syn_cins2 (syn_csset)))
      (syn_cins4 (syn_cun (syn_cima (syn_cin (syn_cins4 (syn_csi3 (syn_cswap)))
              (syn_cins2 (syn_cins2 (syn_csset)))) (syn_c1c)) (syn_cima
            (syn_cin (syn_cins4 (syn_csi3 (syn_cid))) (syn_cins2 (syn_cins2 (syn_csset))))
            (syn_c1c))))
  have p0013 := @g_snex (.cv x)
  have p0014 :=
    @g_otelins2 (syn_csn (.cv y)) (syn_csn (.cv x)) (syn_cop (.cv r) (.cv a))
      (syn_cins2 (syn_csset)) p0013
  have p0015 := @g_otelins2 (syn_csn (.cv y)) (.cv r) (.cv a) (syn_csset) p0001
  have p0016 := @g_vex y
  have p0017 := @g_opelssetsn (.cv y) (.cv a) p0016 p0002
  have p0018_e02_recanon :
    Nominal.NPrf
      (syn_wb (.classMem (syn_cop (syn_csn (.cv y)) (.cv a)) (syn_csset)) (.objMem y a)) :=
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
    @g_n_3bitri
      (.classMem
        (syn_cop (syn_csn (.cv y)) (syn_cop (syn_csn (.cv x)) (syn_cop (.cv r) (.cv a))))
        (syn_cins2 (syn_cins2 (syn_csset))))
      (.classMem (syn_cop (syn_csn (.cv y)) (syn_cop (.cv r) (.cv a))) (syn_cins2 (syn_csset)))
      (.classMem (syn_cop (syn_csn (.cv y)) (.cv a)) (syn_csset)) (.objMem y a) p0014
      p0015 p0018_e02_recanon
  have p0019 :=
    @g_oqelins4 (syn_csn (.cv y)) (syn_csn (.cv x)) (.cv r) (.cv a)
      (syn_cun (syn_cima
          (syn_cin (syn_cins4 (syn_csi3 (syn_cswap))) (syn_cins2 (syn_cins2 (syn_csset))))
          (syn_c1c)) (syn_cima
          (syn_cin (syn_cins4 (syn_csi3 (syn_cid))) (syn_cins2 (syn_cins2 (syn_csset))))
          (syn_c1c)))
      p0002
  have p0020 :=
    @g_elun (syn_cop (syn_csn (.cv y)) (syn_cop (syn_csn (.cv x)) (.cv r)))
      (syn_cima (syn_cin (syn_cins4 (syn_csi3 (syn_cswap))) (syn_cins2 (syn_cins2 (syn_csset))))
        (syn_c1c))
      (syn_cima (syn_cin (syn_cins4 (syn_csi3 (syn_cid))) (syn_cins2 (syn_cins2 (syn_csset))))
        (syn_c1c))
  have p0021 :=
    @g_elin
      (syn_cop (syn_csn (.cv p))
        (syn_cop (syn_csn (.cv y)) (syn_cop (syn_csn (.cv x)) (.cv r))))
      (syn_cins4 (syn_csi3 (syn_cswap))) (syn_cins2 (syn_cins2 (syn_csset)))
  have p0022 :=
    @g_oqelins4 (syn_csn (.cv p)) (syn_csn (.cv y)) (syn_csn (.cv x)) (.cv r)
      (syn_csi3 (syn_cswap)) p0001
  have p0023 := @g_vex p
  have p0024 := @g_otsnelsi3 (.cv p) (.cv y) (.cv x) (syn_cswap) p0023 p0016 p0008
  have p0025 :=
    (Nominal.biimpRefl (syn_wbr (.cv p) (syn_cswap) (syn_cop (.cv y) (.cv x))))
  have p0026 := @g_brswap2 (.cv p) (.cv y) (.cv x) p0016 p0008
  have p0027 :=
    @g_bitr3i (.classMem (syn_cop (.cv p) (syn_cop (.cv y) (.cv x))) (syn_cswap))
      (syn_wbr (.cv p) (syn_cswap) (syn_cop (.cv y) (.cv x)))
      (.classEq (.cv p) (syn_cop (.cv x) (.cv y))) p0025 p0026
  have p0028 :=
    @g_n_3bitri
      (.classMem (syn_cop (syn_csn (.cv p))
          (syn_cop (syn_csn (.cv y)) (syn_cop (syn_csn (.cv x)) (.cv r))))
        (syn_cins4 (syn_csi3 (syn_cswap))))
      (.classMem (syn_cop (syn_csn (.cv p)) (syn_cop (syn_csn (.cv y)) (syn_csn (.cv x))))
        (syn_csi3 (syn_cswap)))
      (.classMem (syn_cop (.cv p) (syn_cop (.cv y) (.cv x))) (syn_cswap))
      (.classEq (.cv p) (syn_cop (.cv x) (.cv y))) p0022 p0024 p0027
  have p0029 := @g_snex (.cv y)
  have p0030 :=
    @g_otelins2 (syn_csn (.cv p)) (syn_csn (.cv y)) (syn_cop (syn_csn (.cv x)) (.cv r))
      (syn_cins2 (syn_csset)) p0029
  have p0031 := @g_otelins2 (syn_csn (.cv p)) (syn_csn (.cv x)) (.cv r) (syn_csset) p0013
  have p0032 := @g_opelssetsn (.cv p) (.cv r) p0023 p0001
  have p0033_e02_recanon :
    Nominal.NPrf
      (syn_wb (.classMem (syn_cop (syn_csn (.cv p)) (.cv r)) (syn_csset)) (.objMem p r)) :=
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
      p0032
  have p0033 :=
    @g_n_3bitri
      (.classMem (syn_cop (syn_csn (.cv p))
          (syn_cop (syn_csn (.cv y)) (syn_cop (syn_csn (.cv x)) (.cv r))))
        (syn_cins2 (syn_cins2 (syn_csset))))
      (.classMem (syn_cop (syn_csn (.cv p)) (syn_cop (syn_csn (.cv x)) (.cv r)))
        (syn_cins2 (syn_csset)))
      (.classMem (syn_cop (syn_csn (.cv p)) (.cv r)) (syn_csset)) (.objMem p r) p0030
      p0031 p0033_e02_recanon
  have p0034 :=
    @g_anbi12i
      (.classMem (syn_cop (syn_csn (.cv p))
          (syn_cop (syn_csn (.cv y)) (syn_cop (syn_csn (.cv x)) (.cv r))))
        (syn_cins4 (syn_csi3 (syn_cswap))))
      (.classEq (.cv p) (syn_cop (.cv x) (.cv y)))
      (.classMem (syn_cop (syn_csn (.cv p))
          (syn_cop (syn_csn (.cv y)) (syn_cop (syn_csn (.cv x)) (.cv r))))
        (syn_cins2 (syn_cins2 (syn_csset))))
      (.objMem p r) p0028 p0033
  have p0035 :=
    @g_bitri
      (.classMem (syn_cop (syn_csn (.cv p))
          (syn_cop (syn_csn (.cv y)) (syn_cop (syn_csn (.cv x)) (.cv r))))
        (syn_cin (syn_cins4 (syn_csi3 (syn_cswap))) (syn_cins2 (syn_cins2 (syn_csset)))))
      (syn_wa (.classMem (syn_cop (syn_csn (.cv p))
            (syn_cop (syn_csn (.cv y)) (syn_cop (syn_csn (.cv x)) (.cv r))))
          (syn_cins4 (syn_csi3 (syn_cswap)))) (.classMem (syn_cop (syn_csn (.cv p))
            (syn_cop (syn_csn (.cv y)) (syn_cop (syn_csn (.cv x)) (.cv r))))
          (syn_cins2 (syn_cins2 (syn_csset)))))
      (syn_wa (.classEq (.cv p) (syn_cop (.cv x) (.cv y))) (.objMem p r)) p0021 p0034
  have p0036 :=
    @g_exbii
      (.classMem (syn_cop (syn_csn (.cv p))
          (syn_cop (syn_csn (.cv y)) (syn_cop (syn_csn (.cv x)) (.cv r))))
        (syn_cin (syn_cins4 (syn_csi3 (syn_cswap))) (syn_cins2 (syn_cins2 (syn_csset)))))
      (syn_wa (.classEq (.cv p) (syn_cop (.cv x) (.cv y))) (.objMem p r)) p p0035
  have p0037 :=
    @g_elima1c p (syn_cop (syn_csn (.cv y)) (syn_cop (syn_csn (.cv x)) (.cv r)))
      (syn_cin (syn_cins4 (syn_csi3 (syn_cswap))) (syn_cins2 (syn_cins2 (syn_csset))))
      dv_cache_0011 dv_cache_0012
  have p0038 := (Nominal.biimpRefl (syn_wbr (.cv x) (.cv r) (.cv y)))
  have p0039 :=
    (NFChoice.DirectNominalPrf.Nominal.DefinitionLeafHandlersCanonical001.dfClelOfDV p
      (syn_cop (.cv x) (.cv y)) (.cv r) dv_cache_0013 dv_cache_0014)
  have p0040_e01_recanon :
    Nominal.NPrf
      (syn_wb (.classMem (syn_cop (.cv x) (.cv y)) (.cv r)) (syn_wex p
          (syn_wa (.classEq (.cv p) (syn_cop (.cv x) (.cv y))) (.objMem p r)))) :=
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
      p0039
  have p0040 :=
    @g_bitri (syn_wbr (.cv x) (.cv r) (.cv y))
      (.classMem (syn_cop (.cv x) (.cv y)) (.cv r))
      (syn_wex p (syn_wa (.classEq (.cv p) (syn_cop (.cv x) (.cv y))) (.objMem p r)))
      p0038 p0040_e01_recanon
  have p0041 :=
    @g_n_3bitr4i
      (syn_wex p (.classMem (syn_cop (syn_csn (.cv p))
            (syn_cop (syn_csn (.cv y)) (syn_cop (syn_csn (.cv x)) (.cv r))))
          (syn_cin (syn_cins4 (syn_csi3 (syn_cswap))) (syn_cins2 (syn_cins2 (syn_csset))))))
      (syn_wex p (syn_wa (.classEq (.cv p) (syn_cop (.cv x) (.cv y))) (.objMem p r)))
      (.classMem (syn_cop (syn_csn (.cv y)) (syn_cop (syn_csn (.cv x)) (.cv r))) (syn_cima
          (syn_cin (syn_cins4 (syn_csi3 (syn_cswap))) (syn_cins2 (syn_cins2 (syn_csset))))
          (syn_c1c)))
      (syn_wbr (.cv x) (.cv r) (.cv y)) p0036 p0037 p0040
  have p0042 :=
    @g_elin
      (syn_cop (syn_csn (.cv p))
        (syn_cop (syn_csn (.cv y)) (syn_cop (syn_csn (.cv x)) (.cv r))))
      (syn_cins4 (syn_csi3 (syn_cid))) (syn_cins2 (syn_cins2 (syn_csset)))
  have p0043 :=
    @g_oqelins4 (syn_csn (.cv p)) (syn_csn (.cv y)) (syn_csn (.cv x)) (.cv r)
      (syn_csi3 (syn_cid)) p0001
  have p0044 := @g_otsnelsi3 (.cv p) (.cv y) (.cv x) (syn_cid) p0023 p0016 p0008
  have p0045 := (Nominal.biimpRefl (syn_wbr (.cv p) (syn_cid) (syn_cop (.cv y) (.cv x))))
  have p0046 := @g_opex (.cv y) (.cv x) p0016 p0008
  have p0047 := @g_ideq (.cv p) (syn_cop (.cv y) (.cv x)) p0046
  have p0048 :=
    @g_bitr3i (.classMem (syn_cop (.cv p) (syn_cop (.cv y) (.cv x))) (syn_cid))
      (syn_wbr (.cv p) (syn_cid) (syn_cop (.cv y) (.cv x)))
      (.classEq (.cv p) (syn_cop (.cv y) (.cv x))) p0045 p0047
  have p0049 :=
    @g_n_3bitri
      (.classMem (syn_cop (syn_csn (.cv p))
          (syn_cop (syn_csn (.cv y)) (syn_cop (syn_csn (.cv x)) (.cv r))))
        (syn_cins4 (syn_csi3 (syn_cid))))
      (.classMem (syn_cop (syn_csn (.cv p)) (syn_cop (syn_csn (.cv y)) (syn_csn (.cv x))))
        (syn_csi3 (syn_cid)))
      (.classMem (syn_cop (.cv p) (syn_cop (.cv y) (.cv x))) (syn_cid))
      (.classEq (.cv p) (syn_cop (.cv y) (.cv x))) p0043 p0044 p0048
  have p0050 :=
    @g_anbi12i
      (.classMem (syn_cop (syn_csn (.cv p))
          (syn_cop (syn_csn (.cv y)) (syn_cop (syn_csn (.cv x)) (.cv r))))
        (syn_cins4 (syn_csi3 (syn_cid))))
      (.classEq (.cv p) (syn_cop (.cv y) (.cv x)))
      (.classMem (syn_cop (syn_csn (.cv p))
          (syn_cop (syn_csn (.cv y)) (syn_cop (syn_csn (.cv x)) (.cv r))))
        (syn_cins2 (syn_cins2 (syn_csset))))
      (.objMem p r) p0049 p0033
  have p0051 :=
    @g_bitri
      (.classMem (syn_cop (syn_csn (.cv p))
          (syn_cop (syn_csn (.cv y)) (syn_cop (syn_csn (.cv x)) (.cv r))))
        (syn_cin (syn_cins4 (syn_csi3 (syn_cid))) (syn_cins2 (syn_cins2 (syn_csset)))))
      (syn_wa (.classMem (syn_cop (syn_csn (.cv p))
            (syn_cop (syn_csn (.cv y)) (syn_cop (syn_csn (.cv x)) (.cv r))))
          (syn_cins4 (syn_csi3 (syn_cid)))) (.classMem (syn_cop (syn_csn (.cv p))
            (syn_cop (syn_csn (.cv y)) (syn_cop (syn_csn (.cv x)) (.cv r))))
          (syn_cins2 (syn_cins2 (syn_csset)))))
      (syn_wa (.classEq (.cv p) (syn_cop (.cv y) (.cv x))) (.objMem p r)) p0042 p0050
  have p0052 :=
    @g_exbii
      (.classMem (syn_cop (syn_csn (.cv p))
          (syn_cop (syn_csn (.cv y)) (syn_cop (syn_csn (.cv x)) (.cv r))))
        (syn_cin (syn_cins4 (syn_csi3 (syn_cid))) (syn_cins2 (syn_cins2 (syn_csset)))))
      (syn_wa (.classEq (.cv p) (syn_cop (.cv y) (.cv x))) (.objMem p r)) p p0051
  have p0053 :=
    @g_elima1c p (syn_cop (syn_csn (.cv y)) (syn_cop (syn_csn (.cv x)) (.cv r)))
      (syn_cin (syn_cins4 (syn_csi3 (syn_cid))) (syn_cins2 (syn_cins2 (syn_csset))))
      dv_cache_0011 dv_cache_0015
  have p0054 := (Nominal.biimpRefl (syn_wbr (.cv y) (.cv r) (.cv x)))
  have p0055 :=
    (NFChoice.DirectNominalPrf.Nominal.DefinitionLeafHandlersCanonical001.dfClelOfDV p
      (syn_cop (.cv y) (.cv x)) (.cv r) dv_cache_0016 dv_cache_0014)
  have p0056_e01_recanon :
    Nominal.NPrf
      (syn_wb (.classMem (syn_cop (.cv y) (.cv x)) (.cv r)) (syn_wex p
          (syn_wa (.classEq (.cv p) (syn_cop (.cv y) (.cv x))) (.objMem p r)))) :=
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
      p0055
  have p0056 :=
    @g_bitri (syn_wbr (.cv y) (.cv r) (.cv x))
      (.classMem (syn_cop (.cv y) (.cv x)) (.cv r))
      (syn_wex p (syn_wa (.classEq (.cv p) (syn_cop (.cv y) (.cv x))) (.objMem p r)))
      p0054 p0056_e01_recanon
  have p0057 :=
    @g_n_3bitr4i
      (syn_wex p (.classMem (syn_cop (syn_csn (.cv p))
            (syn_cop (syn_csn (.cv y)) (syn_cop (syn_csn (.cv x)) (.cv r))))
          (syn_cin (syn_cins4 (syn_csi3 (syn_cid))) (syn_cins2 (syn_cins2 (syn_csset))))))
      (syn_wex p (syn_wa (.classEq (.cv p) (syn_cop (.cv y) (.cv x))) (.objMem p r)))
      (.classMem (syn_cop (syn_csn (.cv y)) (syn_cop (syn_csn (.cv x)) (.cv r))) (syn_cima
          (syn_cin (syn_cins4 (syn_csi3 (syn_cid))) (syn_cins2 (syn_cins2 (syn_csset))))
          (syn_c1c)))
      (syn_wbr (.cv y) (.cv r) (.cv x)) p0052 p0053 p0056
  have p0058 :=
    @g_orbi12i
      (.classMem (syn_cop (syn_csn (.cv y)) (syn_cop (syn_csn (.cv x)) (.cv r))) (syn_cima
          (syn_cin (syn_cins4 (syn_csi3 (syn_cswap))) (syn_cins2 (syn_cins2 (syn_csset))))
          (syn_c1c)))
      (syn_wbr (.cv x) (.cv r) (.cv y))
      (.classMem (syn_cop (syn_csn (.cv y)) (syn_cop (syn_csn (.cv x)) (.cv r))) (syn_cima
          (syn_cin (syn_cins4 (syn_csi3 (syn_cid))) (syn_cins2 (syn_cins2 (syn_csset))))
          (syn_c1c)))
      (syn_wbr (.cv y) (.cv r) (.cv x)) p0041 p0057
  have p0059 :=
    @g_n_3bitri
      (.classMem
        (syn_cop (syn_csn (.cv y)) (syn_cop (syn_csn (.cv x)) (syn_cop (.cv r) (.cv a))))
        (syn_cins4 (syn_cun (syn_cima (syn_cin (syn_cins4 (syn_csi3 (syn_cswap)))
                (syn_cins2 (syn_cins2 (syn_csset)))) (syn_c1c)) (syn_cima
              (syn_cin (syn_cins4 (syn_csi3 (syn_cid))) (syn_cins2 (syn_cins2 (syn_csset))))
              (syn_c1c)))))
      (.classMem (syn_cop (syn_csn (.cv y)) (syn_cop (syn_csn (.cv x)) (.cv r))) (syn_cun
          (syn_cima (syn_cin (syn_cins4 (syn_csi3 (syn_cswap)))
              (syn_cins2 (syn_cins2 (syn_csset)))) (syn_c1c)) (syn_cima
            (syn_cin (syn_cins4 (syn_csi3 (syn_cid))) (syn_cins2 (syn_cins2 (syn_csset))))
            (syn_c1c))))
      (syn_wo (.classMem (syn_cop (syn_csn (.cv y)) (syn_cop (syn_csn (.cv x)) (.cv r)))
          (syn_cima (syn_cin (syn_cins4 (syn_csi3 (syn_cswap)))
              (syn_cins2 (syn_cins2 (syn_csset)))) (syn_c1c)))
        (.classMem (syn_cop (syn_csn (.cv y)) (syn_cop (syn_csn (.cv x)) (.cv r))) (syn_cima
            (syn_cin (syn_cins4 (syn_csi3 (syn_cid))) (syn_cins2 (syn_cins2 (syn_csset))))
            (syn_c1c))))
      (syn_wo (syn_wbr (.cv x) (.cv r) (.cv y)) (syn_wbr (.cv y) (.cv r) (.cv x))) p0019
      p0020 p0058
  have p0060 :=
    @g_notbii
      (.classMem
        (syn_cop (syn_csn (.cv y)) (syn_cop (syn_csn (.cv x)) (syn_cop (.cv r) (.cv a))))
        (syn_cins4 (syn_cun (syn_cima (syn_cin (syn_cins4 (syn_csi3 (syn_cswap)))
                (syn_cins2 (syn_cins2 (syn_csset)))) (syn_c1c)) (syn_cima
              (syn_cin (syn_cins4 (syn_csi3 (syn_cid))) (syn_cins2 (syn_cins2 (syn_csset))))
              (syn_c1c)))))
      (syn_wo (syn_wbr (.cv x) (.cv r) (.cv y)) (syn_wbr (.cv y) (.cv r) (.cv x))) p0059
  have p0061 :=
    @g_anbi12i
      (.classMem
        (syn_cop (syn_csn (.cv y)) (syn_cop (syn_csn (.cv x)) (syn_cop (.cv r) (.cv a))))
        (syn_cins2 (syn_cins2 (syn_csset))))
      (.objMem y a)
      (.neg (.classMem (syn_cop (syn_csn (.cv y))
            (syn_cop (syn_csn (.cv x)) (syn_cop (.cv r) (.cv a)))) (syn_cins4 (syn_cun (syn_cima
                (syn_cin (syn_cins4 (syn_csi3 (syn_cswap))) (syn_cins2 (syn_cins2 (syn_csset))))
                (syn_c1c)) (syn_cima (syn_cin (syn_cins4 (syn_csi3 (syn_cid)))
                  (syn_cins2 (syn_cins2 (syn_csset)))) (syn_c1c))))))
      (.neg (syn_wo (syn_wbr (.cv x) (.cv r) (.cv y)) (syn_wbr (.cv y) (.cv r) (.cv x))))
      p0018 p0060
  have p0062 :=
    @g_bitri
      (.classMem
        (syn_cop (syn_csn (.cv y)) (syn_cop (syn_csn (.cv x)) (syn_cop (.cv r) (.cv a))))
        (syn_cdif (syn_cins2 (syn_cins2 (syn_csset))) (syn_cins4 (syn_cun (syn_cima
                (syn_cin (syn_cins4 (syn_csi3 (syn_cswap))) (syn_cins2 (syn_cins2 (syn_csset))))
                (syn_c1c)) (syn_cima (syn_cin (syn_cins4 (syn_csi3 (syn_cid)))
                  (syn_cins2 (syn_cins2 (syn_csset)))) (syn_c1c))))))
      (syn_wa (.classMem (syn_cop (syn_csn (.cv y))
            (syn_cop (syn_csn (.cv x)) (syn_cop (.cv r) (.cv a))))
          (syn_cins2 (syn_cins2 (syn_csset)))) (.neg (.classMem (syn_cop (syn_csn (.cv y))
              (syn_cop (syn_csn (.cv x)) (syn_cop (.cv r) (.cv a)))) (syn_cins4 (syn_cun
                (syn_cima (syn_cin (syn_cins4 (syn_csi3 (syn_cswap)))
                    (syn_cins2 (syn_cins2 (syn_csset)))) (syn_c1c)) (syn_cima
                  (syn_cin (syn_cins4 (syn_csi3 (syn_cid))) (syn_cins2 (syn_cins2 (syn_csset))))
                  (syn_c1c)))))))
      (syn_wa (.objMem y a) (.neg
          (syn_wo (syn_wbr (.cv x) (.cv r) (.cv y)) (syn_wbr (.cv y) (.cv r) (.cv x)))))
      p0012 p0061
  have p0063 :=
    @g_exbii
      (.classMem
        (syn_cop (syn_csn (.cv y)) (syn_cop (syn_csn (.cv x)) (syn_cop (.cv r) (.cv a))))
        (syn_cdif (syn_cins2 (syn_cins2 (syn_csset))) (syn_cins4 (syn_cun (syn_cima
                (syn_cin (syn_cins4 (syn_csi3 (syn_cswap))) (syn_cins2 (syn_cins2 (syn_csset))))
                (syn_c1c)) (syn_cima (syn_cin (syn_cins4 (syn_csi3 (syn_cid)))
                  (syn_cins2 (syn_cins2 (syn_csset)))) (syn_c1c))))))
      (syn_wa (.objMem y a) (.neg
          (syn_wo (syn_wbr (.cv x) (.cv r) (.cv y)) (syn_wbr (.cv y) (.cv r) (.cv x)))))
      y p0062
  have p0064 :=
    @g_bitri
      (.classMem (syn_cop (syn_csn (.cv x)) (syn_cop (.cv r) (.cv a))) (syn_cima
          (syn_cdif (syn_cins2 (syn_cins2 (syn_csset))) (syn_cins4 (syn_cun (syn_cima
                  (syn_cin (syn_cins4 (syn_csi3 (syn_cswap)))
                    (syn_cins2 (syn_cins2 (syn_csset)))) (syn_c1c)) (syn_cima
                  (syn_cin (syn_cins4 (syn_csi3 (syn_cid))) (syn_cins2 (syn_cins2 (syn_csset))))
                  (syn_c1c))))) (syn_c1c)))
      (syn_wex y (.classMem (syn_cop (syn_csn (.cv y))
            (syn_cop (syn_csn (.cv x)) (syn_cop (.cv r) (.cv a))))
          (syn_cdif (syn_cins2 (syn_cins2 (syn_csset))) (syn_cins4 (syn_cun (syn_cima
                  (syn_cin (syn_cins4 (syn_csi3 (syn_cswap)))
                    (syn_cins2 (syn_cins2 (syn_csset)))) (syn_c1c)) (syn_cima
                  (syn_cin (syn_cins4 (syn_csi3 (syn_cid))) (syn_cins2 (syn_cins2 (syn_csset))))
                  (syn_c1c)))))))
      (syn_wex y (syn_wa (.objMem y a) (.neg (syn_wo (syn_wbr (.cv x) (.cv r) (.cv y))
              (syn_wbr (.cv y) (.cv r) (.cv x))))))
      p0011 p0063
  have p0065 :=
    (Nominal.biimpRefl (syn_wrex y (.cv a) (.neg
          (syn_wo (syn_wbr (.cv x) (.cv r) (.cv y)) (syn_wbr (.cv y) (.cv r) (.cv x))))))
  have p0066 :=
    @g_rexnal (syn_wo (syn_wbr (.cv x) (.cv r) (.cv y)) (syn_wbr (.cv y) (.cv r) (.cv x)))
      y (.cv a)
  have p0067_e01_recanon :
    Nominal.NPrf
      (syn_wb (syn_wrex y (.cv a) (.neg
            (syn_wo (syn_wbr (.cv x) (.cv r) (.cv y)) (syn_wbr (.cv y) (.cv r) (.cv x)))))
        (syn_wex y (syn_wa (.objMem y a) (.neg (syn_wo (syn_wbr (.cv x) (.cv r) (.cv y))
                (syn_wbr (.cv y) (.cv r) (.cv x))))))) :=
    Nominal.RecanonTransportDev.transport
      (by
        simp only [syn_wb, syn_wrex, syn_wex, syn_wa, syn_wo, syn_wbr, syn_cop, syn_cun,
          syn_cnin, syn_wnan, syn_ccompl]
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
    @g_n_3bitr2i
      (.classMem (syn_cop (syn_csn (.cv x)) (syn_cop (.cv r) (.cv a))) (syn_cima
          (syn_cdif (syn_cins2 (syn_cins2 (syn_csset))) (syn_cins4 (syn_cun (syn_cima
                  (syn_cin (syn_cins4 (syn_csi3 (syn_cswap)))
                    (syn_cins2 (syn_cins2 (syn_csset)))) (syn_c1c)) (syn_cima
                  (syn_cin (syn_cins4 (syn_csi3 (syn_cid))) (syn_cins2 (syn_cins2 (syn_csset))))
                  (syn_c1c))))) (syn_c1c)))
      (syn_wex y (syn_wa (.objMem y a) (.neg (syn_wo (syn_wbr (.cv x) (.cv r) (.cv y))
              (syn_wbr (.cv y) (.cv r) (.cv x))))))
      (syn_wrex y (.cv a) (.neg
          (syn_wo (syn_wbr (.cv x) (.cv r) (.cv y)) (syn_wbr (.cv y) (.cv r) (.cv x)))))
      (.neg (syn_wral y (.cv a)
          (syn_wo (syn_wbr (.cv x) (.cv r) (.cv y)) (syn_wbr (.cv y) (.cv r) (.cv x)))))
      p0064 p0067_e01_recanon p0066
  have p0068 :=
    @g_anbi12i
      (.classMem (syn_cop (syn_csn (.cv x)) (syn_cop (.cv r) (.cv a))) (syn_cins2 (syn_csset)))
      (.objMem x a)
      (.classMem (syn_cop (syn_csn (.cv x)) (syn_cop (.cv r) (.cv a))) (syn_cima
          (syn_cdif (syn_cins2 (syn_cins2 (syn_csset))) (syn_cins4 (syn_cun (syn_cima
                  (syn_cin (syn_cins4 (syn_csi3 (syn_cswap)))
                    (syn_cins2 (syn_cins2 (syn_csset)))) (syn_c1c)) (syn_cima
                  (syn_cin (syn_cins4 (syn_csi3 (syn_cid))) (syn_cins2 (syn_cins2 (syn_csset))))
                  (syn_c1c))))) (syn_c1c)))
      (.neg (syn_wral y (.cv a)
          (syn_wo (syn_wbr (.cv x) (.cv r) (.cv y)) (syn_wbr (.cv y) (.cv r) (.cv x)))))
      p0010 p0067
  have p0069 :=
    @g_bitri
      (.classMem (syn_cop (syn_csn (.cv x)) (syn_cop (.cv r) (.cv a)))
        (syn_cin (syn_cins2 (syn_csset)) (syn_cima (syn_cdif (syn_cins2 (syn_cins2 (syn_csset)))
              (syn_cins4 (syn_cun (syn_cima (syn_cin (syn_cins4 (syn_csi3 (syn_cswap)))
                      (syn_cins2 (syn_cins2 (syn_csset)))) (syn_c1c)) (syn_cima
                    (syn_cin (syn_cins4 (syn_csi3 (syn_cid)))
                      (syn_cins2 (syn_cins2 (syn_csset)))) (syn_c1c))))) (syn_c1c))))
      (syn_wa (.classMem (syn_cop (syn_csn (.cv x)) (syn_cop (.cv r) (.cv a)))
          (syn_cins2 (syn_csset)))
        (.classMem (syn_cop (syn_csn (.cv x)) (syn_cop (.cv r) (.cv a))) (syn_cima
            (syn_cdif (syn_cins2 (syn_cins2 (syn_csset))) (syn_cins4 (syn_cun (syn_cima
                    (syn_cin (syn_cins4 (syn_csi3 (syn_cswap)))
                      (syn_cins2 (syn_cins2 (syn_csset)))) (syn_c1c)) (syn_cima
                    (syn_cin (syn_cins4 (syn_csi3 (syn_cid)))
                      (syn_cins2 (syn_cins2 (syn_csset)))) (syn_c1c))))) (syn_c1c))))
      (syn_wa (.objMem x a) (.neg (syn_wral y (.cv a) (syn_wo (syn_wbr (.cv x) (.cv r) (.cv y))
              (syn_wbr (.cv y) (.cv r) (.cv x))))))
      p0006 p0068
  have p0070 :=
    @g_exbii
      (.classMem (syn_cop (syn_csn (.cv x)) (syn_cop (.cv r) (.cv a)))
        (syn_cin (syn_cins2 (syn_csset)) (syn_cima (syn_cdif (syn_cins2 (syn_cins2 (syn_csset)))
              (syn_cins4 (syn_cun (syn_cima (syn_cin (syn_cins4 (syn_csi3 (syn_cswap)))
                      (syn_cins2 (syn_cins2 (syn_csset)))) (syn_c1c)) (syn_cima
                    (syn_cin (syn_cins4 (syn_csi3 (syn_cid)))
                      (syn_cins2 (syn_cins2 (syn_csset)))) (syn_c1c))))) (syn_c1c))))
      (syn_wa (.objMem x a) (.neg (syn_wral y (.cv a) (syn_wo (syn_wbr (.cv x) (.cv r) (.cv y))
              (syn_wbr (.cv y) (.cv r) (.cv x))))))
      x p0069
  have p0071 :=
    @g_bitri
      (.classMem (syn_cop (.cv r) (.cv a)) (syn_cima (syn_cin (syn_cins2 (syn_csset)) (syn_cima
              (syn_cdif (syn_cins2 (syn_cins2 (syn_csset))) (syn_cins4 (syn_cun (syn_cima
                      (syn_cin (syn_cins4 (syn_csi3 (syn_cswap)))
                        (syn_cins2 (syn_cins2 (syn_csset)))) (syn_c1c)) (syn_cima
                      (syn_cin (syn_cins4 (syn_csi3 (syn_cid)))
                        (syn_cins2 (syn_cins2 (syn_csset)))) (syn_c1c))))) (syn_c1c)))
          (syn_c1c)))
      (syn_wex x (.classMem (syn_cop (syn_csn (.cv x)) (syn_cop (.cv r) (.cv a)))
          (syn_cin (syn_cins2 (syn_csset)) (syn_cima
              (syn_cdif (syn_cins2 (syn_cins2 (syn_csset))) (syn_cins4 (syn_cun (syn_cima
                      (syn_cin (syn_cins4 (syn_csi3 (syn_cswap)))
                        (syn_cins2 (syn_cins2 (syn_csset)))) (syn_c1c)) (syn_cima
                      (syn_cin (syn_cins4 (syn_csi3 (syn_cid)))
                        (syn_cins2 (syn_cins2 (syn_csset)))) (syn_c1c))))) (syn_c1c)))))
      (syn_wex x (syn_wa (.objMem x a) (.neg (syn_wral y (.cv a)
              (syn_wo (syn_wbr (.cv x) (.cv r) (.cv y)) (syn_wbr (.cv y) (.cv r) (.cv x)))))))
      p0005 p0070
  have p0072 :=
    (Nominal.biimpRefl (syn_wrex x (.cv a) (.neg (syn_wral y (.cv a)
            (syn_wo (syn_wbr (.cv x) (.cv r) (.cv y)) (syn_wbr (.cv y) (.cv r) (.cv x)))))))
  have p0073 :=
    @g_rexnal
      (syn_wral y (.cv a)
        (syn_wo (syn_wbr (.cv x) (.cv r) (.cv y)) (syn_wbr (.cv y) (.cv r) (.cv x))))
      x (.cv a)
  have p0074_e01_recanon :
    Nominal.NPrf
      (syn_wb (syn_wrex x (.cv a) (.neg (syn_wral y (.cv a)
              (syn_wo (syn_wbr (.cv x) (.cv r) (.cv y)) (syn_wbr (.cv y) (.cv r) (.cv x))))))
        (syn_wex x (syn_wa (.objMem x a) (.neg (syn_wral y (.cv a)
                (syn_wo (syn_wbr (.cv x) (.cv r) (.cv y))
                  (syn_wbr (.cv y) (.cv r) (.cv x)))))))) :=
    Nominal.RecanonTransportDev.transport
      (by
        simp only [syn_wb, syn_wrex, syn_wex, syn_wa, syn_wral, syn_wo, syn_wbr, syn_cop,
          syn_cun, syn_cnin, syn_wnan, syn_ccompl]
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
    @g_n_3bitr2i
      (.classMem (syn_cop (.cv r) (.cv a)) (syn_cima (syn_cin (syn_cins2 (syn_csset)) (syn_cima
              (syn_cdif (syn_cins2 (syn_cins2 (syn_csset))) (syn_cins4 (syn_cun (syn_cima
                      (syn_cin (syn_cins4 (syn_csi3 (syn_cswap)))
                        (syn_cins2 (syn_cins2 (syn_csset)))) (syn_c1c)) (syn_cima
                      (syn_cin (syn_cins4 (syn_csi3 (syn_cid)))
                        (syn_cins2 (syn_cins2 (syn_csset)))) (syn_c1c))))) (syn_c1c)))
          (syn_c1c)))
      (syn_wex x (syn_wa (.objMem x a) (.neg (syn_wral y (.cv a)
              (syn_wo (syn_wbr (.cv x) (.cv r) (.cv y)) (syn_wbr (.cv y) (.cv r) (.cv x)))))))
      (syn_wrex x (.cv a) (.neg (syn_wral y (.cv a) (syn_wo (syn_wbr (.cv x) (.cv r) (.cv y))
              (syn_wbr (.cv y) (.cv r) (.cv x))))))
      (.neg (syn_wral x (.cv a) (syn_wral y (.cv a) (syn_wo (syn_wbr (.cv x) (.cv r) (.cv y))
              (syn_wbr (.cv y) (.cv r) (.cv x))))))
      p0071 p0074_e01_recanon p0073
  have p0075 :=
    @g_con2bii
      (.classMem (syn_cop (.cv r) (.cv a)) (syn_cima (syn_cin (syn_cins2 (syn_csset)) (syn_cima
              (syn_cdif (syn_cins2 (syn_cins2 (syn_csset))) (syn_cins4 (syn_cun (syn_cima
                      (syn_cin (syn_cins4 (syn_csi3 (syn_cswap)))
                        (syn_cins2 (syn_cins2 (syn_csset)))) (syn_c1c)) (syn_cima
                      (syn_cin (syn_cins4 (syn_csi3 (syn_cid)))
                        (syn_cins2 (syn_cins2 (syn_csset)))) (syn_c1c))))) (syn_c1c)))
          (syn_c1c)))
      (syn_wral x (.cv a) (syn_wral y (.cv a)
          (syn_wo (syn_wbr (.cv x) (.cv r) (.cv y)) (syn_wbr (.cv y) (.cv r) (.cv x)))))
      p0074
  have p0076 :=
    @g_bitr4i
      (.classMem (syn_cop (.cv r) (.cv a)) (syn_ccompl (syn_cima
            (syn_cin (syn_cins2 (syn_csset)) (syn_cima
                (syn_cdif (syn_cins2 (syn_cins2 (syn_csset))) (syn_cins4 (syn_cun (syn_cima
                        (syn_cin (syn_cins4 (syn_csi3 (syn_cswap)))
                          (syn_cins2 (syn_cins2 (syn_csset)))) (syn_c1c)) (syn_cima
                        (syn_cin (syn_cins4 (syn_csi3 (syn_cid)))
                          (syn_cins2 (syn_cins2 (syn_csset)))) (syn_c1c))))) (syn_c1c)))
            (syn_c1c))))
      (.neg (.classMem (syn_cop (.cv r) (.cv a)) (syn_cima (syn_cin (syn_cins2 (syn_csset))
              (syn_cima (syn_cdif (syn_cins2 (syn_cins2 (syn_csset))) (syn_cins4 (syn_cun
                      (syn_cima (syn_cin (syn_cins4 (syn_csi3 (syn_cswap)))
                          (syn_cins2 (syn_cins2 (syn_csset)))) (syn_c1c)) (syn_cima
                        (syn_cin (syn_cins4 (syn_csi3 (syn_cid)))
                          (syn_cins2 (syn_cins2 (syn_csset)))) (syn_c1c))))) (syn_c1c)))
            (syn_c1c))))
      (syn_wral x (.cv a) (syn_wral y (.cv a)
          (syn_wo (syn_wbr (.cv x) (.cv r) (.cv y)) (syn_wbr (.cv y) (.cv r) (.cv x)))))
      p0004 p0075
  have p0077 :=
    @g_opabbi2i
      (syn_wral x (.cv a) (syn_wral y (.cv a)
          (syn_wo (syn_wbr (.cv x) (.cv r) (.cv y)) (syn_wbr (.cv y) (.cv r) (.cv x)))))
      r a
      (syn_ccompl (syn_cima (syn_cin (syn_cins2 (syn_csset)) (syn_cima
              (syn_cdif (syn_cins2 (syn_cins2 (syn_csset))) (syn_cins4 (syn_cun (syn_cima
                      (syn_cin (syn_cins4 (syn_csi3 (syn_cswap)))
                        (syn_cins2 (syn_cins2 (syn_csset)))) (syn_c1c)) (syn_cima
                      (syn_cin (syn_cins4 (syn_csi3 (syn_cid)))
                        (syn_cins2 (syn_cins2 (syn_csset)))) (syn_c1c))))) (syn_c1c)))
          (syn_c1c)))
      dv_cache_0017 dv_cache_0018 dv_cache_0019 p0076
  have p0078 :=
    @g_eqtr4i (syn_cconnex)
      (syn_copab r a (syn_wral x (.cv a) (syn_wral y (.cv a)
            (syn_wo (syn_wbr (.cv x) (.cv r) (.cv y)) (syn_wbr (.cv y) (.cv r) (.cv x))))))
      (syn_ccompl (syn_cima (syn_cin (syn_cins2 (syn_csset)) (syn_cima
              (syn_cdif (syn_cins2 (syn_cins2 (syn_csset))) (syn_cins4 (syn_cun (syn_cima
                      (syn_cin (syn_cins4 (syn_csi3 (syn_cswap)))
                        (syn_cins2 (syn_cins2 (syn_csset)))) (syn_c1c)) (syn_cima
                      (syn_cin (syn_cins4 (syn_csi3 (syn_cid)))
                        (syn_cins2 (syn_cins2 (syn_csset)))) (syn_c1c))))) (syn_c1c)))
          (syn_c1c)))
      p0000 p0077
  have p0079 := @g_ssetex
  have p0080 := @g_ins2ex (syn_csset) p0079
  have p0081 := @g_ins2ex (syn_cins2 (syn_csset)) p0080
  have p0082 := @g_swapex
  have p0083 := @g_si3ex (syn_cswap) p0082
  have p0084 := @g_ins4ex (syn_csi3 (syn_cswap)) p0083
  have p0085 :=
    @g_inex (syn_cins4 (syn_csi3 (syn_cswap))) (syn_cins2 (syn_cins2 (syn_csset))) p0084
      p0081
  have p0086 := @g_n_1cex
  have p0087 :=
    @g_imaex
      (syn_cin (syn_cins4 (syn_csi3 (syn_cswap))) (syn_cins2 (syn_cins2 (syn_csset))))
      (syn_c1c) p0085 p0086
  have p0088 := @g_idex
  have p0089 := @g_si3ex (syn_cid) p0088
  have p0090 := @g_ins4ex (syn_csi3 (syn_cid)) p0089
  have p0091 :=
    @g_inex (syn_cins4 (syn_csi3 (syn_cid))) (syn_cins2 (syn_cins2 (syn_csset))) p0090
      p0081
  have p0093 :=
    @g_imaex
      (syn_cin (syn_cins4 (syn_csi3 (syn_cid))) (syn_cins2 (syn_cins2 (syn_csset))))
      (syn_c1c) p0091 p0086
  have p0094 :=
    @g_unex
      (syn_cima (syn_cin (syn_cins4 (syn_csi3 (syn_cswap))) (syn_cins2 (syn_cins2 (syn_csset))))
        (syn_c1c))
      (syn_cima (syn_cin (syn_cins4 (syn_csi3 (syn_cid))) (syn_cins2 (syn_cins2 (syn_csset))))
        (syn_c1c))
      p0087 p0093
  have p0095 :=
    @g_ins4ex
      (syn_cun (syn_cima
          (syn_cin (syn_cins4 (syn_csi3 (syn_cswap))) (syn_cins2 (syn_cins2 (syn_csset))))
          (syn_c1c)) (syn_cima
          (syn_cin (syn_cins4 (syn_csi3 (syn_cid))) (syn_cins2 (syn_cins2 (syn_csset))))
          (syn_c1c)))
      p0094
  have p0096 :=
    @g_difex (syn_cins2 (syn_cins2 (syn_csset)))
      (syn_cins4 (syn_cun (syn_cima (syn_cin (syn_cins4 (syn_csi3 (syn_cswap)))
              (syn_cins2 (syn_cins2 (syn_csset)))) (syn_c1c)) (syn_cima
            (syn_cin (syn_cins4 (syn_csi3 (syn_cid))) (syn_cins2 (syn_cins2 (syn_csset))))
            (syn_c1c))))
      p0081 p0095
  have p0098 :=
    @g_imaex
      (syn_cdif (syn_cins2 (syn_cins2 (syn_csset))) (syn_cins4 (syn_cun (syn_cima
              (syn_cin (syn_cins4 (syn_csi3 (syn_cswap))) (syn_cins2 (syn_cins2 (syn_csset))))
              (syn_c1c)) (syn_cima (syn_cin (syn_cins4 (syn_csi3 (syn_cid)))
                (syn_cins2 (syn_cins2 (syn_csset)))) (syn_c1c)))))
      (syn_c1c) p0096 p0086
  have p0099 :=
    @g_inex (syn_cins2 (syn_csset))
      (syn_cima (syn_cdif (syn_cins2 (syn_cins2 (syn_csset))) (syn_cins4 (syn_cun (syn_cima
                (syn_cin (syn_cins4 (syn_csi3 (syn_cswap))) (syn_cins2 (syn_cins2 (syn_csset))))
                (syn_c1c)) (syn_cima (syn_cin (syn_cins4 (syn_csi3 (syn_cid)))
                  (syn_cins2 (syn_cins2 (syn_csset)))) (syn_c1c))))) (syn_c1c))
      p0080 p0098
  have p0101 :=
    @g_imaex
      (syn_cin (syn_cins2 (syn_csset)) (syn_cima (syn_cdif (syn_cins2 (syn_cins2 (syn_csset)))
            (syn_cins4 (syn_cun (syn_cima (syn_cin (syn_cins4 (syn_csi3 (syn_cswap)))
                    (syn_cins2 (syn_cins2 (syn_csset)))) (syn_c1c)) (syn_cima
                  (syn_cin (syn_cins4 (syn_csi3 (syn_cid))) (syn_cins2 (syn_cins2 (syn_csset))))
                  (syn_c1c))))) (syn_c1c)))
      (syn_c1c) p0099 p0086
  have p0102 :=
    @g_complex
      (syn_cima (syn_cin (syn_cins2 (syn_csset)) (syn_cima
            (syn_cdif (syn_cins2 (syn_cins2 (syn_csset))) (syn_cins4 (syn_cun (syn_cima
                    (syn_cin (syn_cins4 (syn_csi3 (syn_cswap)))
                      (syn_cins2 (syn_cins2 (syn_csset)))) (syn_c1c)) (syn_cima
                    (syn_cin (syn_cins4 (syn_csi3 (syn_cid)))
                      (syn_cins2 (syn_cins2 (syn_csset)))) (syn_c1c))))) (syn_c1c))) (syn_c1c))
      p0101
  have p0103 :=
    @g_eqeltri (syn_cconnex)
      (syn_ccompl (syn_cima (syn_cin (syn_cins2 (syn_csset)) (syn_cima
              (syn_cdif (syn_cins2 (syn_cins2 (syn_csset))) (syn_cins4 (syn_cun (syn_cima
                      (syn_cin (syn_cins4 (syn_csi3 (syn_cswap)))
                        (syn_cins2 (syn_cins2 (syn_csset)))) (syn_c1c)) (syn_cima
                      (syn_cin (syn_cins4 (syn_csi3 (syn_cid)))
                        (syn_cins2 (syn_cins2 (syn_csset)))) (syn_c1c))))) (syn_c1c)))
          (syn_c1c)))
      (syn_cvv) p0078 p0102
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

@[expose]
noncomputable def g_foundex : Nominal.NPrf (.classMem (syn_cfound) (syn_cvv)) :=
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
  have dv_cache_0011 : x ∉ ((syn_cop (.cv r) (.cv a))).fv :=
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
      ((syn_ctxp (syn_ccompl (syn_cima (syn_cin (syn_cins3 (syn_csset)) (syn_ccompl (syn_cima
                    (syn_cin (syn_cins2 (syn_cins3 (syn_csset))) (syn_cdif (syn_cima
                          (syn_cin (syn_cins4 (syn_csi3 (syn_cid)))
                            (syn_cins2 (syn_cins2 (syn_cins2 (syn_csset))))) (syn_c1c))
                        (syn_cins3 (syn_cid)))) (syn_c1c)))) (syn_c1c))) (syn_cin (syn_csset)
            (syn_cxp (syn_ccompl (syn_csn (syn_c0))) (syn_cvv))))).fv :=
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
      ((syn_cop (syn_csn (.cv y)) (syn_cop (syn_csn (.cv z)) (syn_cop (.cv x) (.cv r))))).fv :=
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
      ((syn_cin (syn_cins4 (syn_csi3 (syn_cid)))
          (syn_cins2 (syn_cins2 (syn_cins2 (syn_csset)))))).fv :=
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
  have dv_cache_0015 : t ∉ ((syn_cop (.cv y) (.cv z))).fv :=
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
  have dv_cache_0017 : y ∉ ((syn_cop (syn_csn (.cv z)) (syn_cop (.cv x) (.cv r)))).fv :=
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
      ((syn_cin (syn_cins2 (syn_cins3 (syn_csset))) (syn_cdif (syn_cima
              (syn_cin (syn_cins4 (syn_csi3 (syn_cid)))
                (syn_cins2 (syn_cins2 (syn_cins2 (syn_csset))))) (syn_c1c))
            (syn_cins3 (syn_cid))))).fv :=
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
  have dv_cache_0019 : z ∉ ((syn_cop (.cv x) (.cv r))).fv :=
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
      ((syn_cin (syn_cins3 (syn_csset)) (syn_ccompl (syn_cima
              (syn_cin (syn_cins2 (syn_cins3 (syn_csset))) (syn_cdif (syn_cima
                    (syn_cin (syn_cins4 (syn_csi3 (syn_cid)))
                      (syn_cins2 (syn_cins2 (syn_cins2 (syn_csset))))) (syn_c1c))
                  (syn_cins3 (syn_cid)))) (syn_c1c))))).fv :=
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
  have dv_cache_0021 : x ∉ ((syn_c0)).fv :=
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
      ((syn_ccompl (syn_crn (syn_ctxp (syn_ccompl (syn_cima (syn_cin (syn_cins3 (syn_csset))
                    (syn_ccompl (syn_cima (syn_cin (syn_cins2 (syn_cins3 (syn_csset))) (syn_cdif
                            (syn_cima (syn_cin (syn_cins4 (syn_csi3 (syn_cid)))
                                (syn_cins2 (syn_cins2 (syn_cins2 (syn_csset))))) (syn_c1c))
                            (syn_cins3 (syn_cid)))) (syn_c1c)))) (syn_c1c)))
              (syn_cin (syn_csset)
                (syn_cxp (syn_ccompl (syn_csn (syn_c0))) (syn_cvv))))))).fv :=
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
      ((syn_ccompl (syn_crn (syn_ctxp (syn_ccompl (syn_cima (syn_cin (syn_cins3 (syn_csset))
                    (syn_ccompl (syn_cima (syn_cin (syn_cins2 (syn_cins3 (syn_csset))) (syn_cdif
                            (syn_cima (syn_cin (syn_cins4 (syn_csi3 (syn_cid)))
                                (syn_cins2 (syn_cins2 (syn_cins2 (syn_csset))))) (syn_c1c))
                            (syn_cins3 (syn_cid)))) (syn_c1c)))) (syn_c1c)))
              (syn_cin (syn_csset)
                (syn_cxp (syn_ccompl (syn_csn (syn_c0))) (syn_cvv))))))).fv :=
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
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominal_df_found x y z r a
      dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006
      dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010
  have p0001 := @g_vex r
  have p0002 := @g_vex a
  have p0003 := @g_opex (.cv r) (.cv a) p0001 p0002
  have p0004 :=
    @g_elcompl (syn_cop (.cv r) (.cv a))
      (syn_crn (syn_ctxp (syn_ccompl (syn_cima (syn_cin (syn_cins3 (syn_csset)) (syn_ccompl
                  (syn_cima (syn_cin (syn_cins2 (syn_cins3 (syn_csset))) (syn_cdif (syn_cima
                          (syn_cin (syn_cins4 (syn_csi3 (syn_cid)))
                            (syn_cins2 (syn_cins2 (syn_cins2 (syn_csset))))) (syn_c1c))
                        (syn_cins3 (syn_cid)))) (syn_c1c)))) (syn_c1c)))
          (syn_cin (syn_csset) (syn_cxp (syn_ccompl (syn_csn (syn_c0))) (syn_cvv)))))
      p0003
  have p0005 :=
    @g_elrn2 x (syn_cop (.cv r) (.cv a))
      (syn_ctxp (syn_ccompl (syn_cima (syn_cin (syn_cins3 (syn_csset)) (syn_ccompl (syn_cima
                  (syn_cin (syn_cins2 (syn_cins3 (syn_csset))) (syn_cdif (syn_cima
                        (syn_cin (syn_cins4 (syn_csi3 (syn_cid)))
                          (syn_cins2 (syn_cins2 (syn_cins2 (syn_csset))))) (syn_c1c))
                      (syn_cins3 (syn_cid)))) (syn_c1c)))) (syn_c1c)))
        (syn_cin (syn_csset) (syn_cxp (syn_ccompl (syn_csn (syn_c0))) (syn_cvv))))
      dv_cache_0011 dv_cache_0012
  have p0006 :=
    @g_oteltxp (.cv x) (.cv r) (.cv a)
      (syn_ccompl (syn_cima (syn_cin (syn_cins3 (syn_csset)) (syn_ccompl (syn_cima
                (syn_cin (syn_cins2 (syn_cins3 (syn_csset))) (syn_cdif (syn_cima
                      (syn_cin (syn_cins4 (syn_csi3 (syn_cid)))
                        (syn_cins2 (syn_cins2 (syn_cins2 (syn_csset))))) (syn_c1c))
                    (syn_cins3 (syn_cid)))) (syn_c1c)))) (syn_c1c)))
      (syn_cin (syn_csset) (syn_cxp (syn_ccompl (syn_csn (syn_c0))) (syn_cvv)))
  have p0007 := @g_vex x
  have p0008 := @g_opex (.cv x) (.cv r) p0007 p0001
  have p0009 :=
    @g_elcompl (syn_cop (.cv x) (.cv r))
      (syn_cima (syn_cin (syn_cins3 (syn_csset)) (syn_ccompl (syn_cima
              (syn_cin (syn_cins2 (syn_cins3 (syn_csset))) (syn_cdif (syn_cima
                    (syn_cin (syn_cins4 (syn_csi3 (syn_cid)))
                      (syn_cins2 (syn_cins2 (syn_cins2 (syn_csset))))) (syn_c1c))
                  (syn_cins3 (syn_cid)))) (syn_c1c)))) (syn_c1c))
      p0008
  have p0010 :=
    @g_elin (syn_cop (syn_csn (.cv z)) (syn_cop (.cv x) (.cv r))) (syn_cins3 (syn_csset))
      (syn_ccompl (syn_cima (syn_cin (syn_cins2 (syn_cins3 (syn_csset))) (syn_cdif (syn_cima
                (syn_cin (syn_cins4 (syn_csi3 (syn_cid)))
                  (syn_cins2 (syn_cins2 (syn_cins2 (syn_csset))))) (syn_c1c))
              (syn_cins3 (syn_cid)))) (syn_c1c)))
  have p0011 := @g_otelins3 (syn_csn (.cv z)) (.cv x) (.cv r) (syn_csset) p0001
  have p0012 := @g_vex z
  have p0013 := @g_opelssetsn (.cv z) (.cv x) p0012 p0007
  have p0014_e01_recanon :
    Nominal.NPrf
      (syn_wb (.classMem (syn_cop (syn_csn (.cv z)) (.cv x)) (syn_csset)) (.objMem z x)) :=
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
      p0013
  have p0014 :=
    @g_bitri
      (.classMem (syn_cop (syn_csn (.cv z)) (syn_cop (.cv x) (.cv r))) (syn_cins3 (syn_csset)))
      (.classMem (syn_cop (syn_csn (.cv z)) (.cv x)) (syn_csset)) (.objMem z x) p0011
      p0014_e01_recanon
  have p0015 := @g_snex (.cv z)
  have p0016 := @g_opex (syn_csn (.cv z)) (syn_cop (.cv x) (.cv r)) p0015 p0008
  have p0017 :=
    @g_elcompl (syn_cop (syn_csn (.cv z)) (syn_cop (.cv x) (.cv r)))
      (syn_cima (syn_cin (syn_cins2 (syn_cins3 (syn_csset))) (syn_cdif (syn_cima
              (syn_cin (syn_cins4 (syn_csi3 (syn_cid)))
                (syn_cins2 (syn_cins2 (syn_cins2 (syn_csset))))) (syn_c1c))
            (syn_cins3 (syn_cid)))) (syn_c1c))
      p0016
  have p0018 :=
    @g_elin
      (syn_cop (syn_csn (.cv y)) (syn_cop (syn_csn (.cv z)) (syn_cop (.cv x) (.cv r))))
      (syn_cins2 (syn_cins3 (syn_csset)))
      (syn_cdif (syn_cima (syn_cin (syn_cins4 (syn_csi3 (syn_cid)))
            (syn_cins2 (syn_cins2 (syn_cins2 (syn_csset))))) (syn_c1c)) (syn_cins3 (syn_cid)))
  have p0019 :=
    @g_otelins2 (syn_csn (.cv y)) (syn_csn (.cv z)) (syn_cop (.cv x) (.cv r))
      (syn_cins3 (syn_csset)) p0015
  have p0020 := @g_otelins3 (syn_csn (.cv y)) (.cv x) (.cv r) (syn_csset) p0001
  have p0021 := @g_vex y
  have p0022 := @g_opelssetsn (.cv y) (.cv x) p0021 p0007
  have p0023_e02_recanon :
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
      p0022
  have p0023 :=
    @g_n_3bitri
      (.classMem
        (syn_cop (syn_csn (.cv y)) (syn_cop (syn_csn (.cv z)) (syn_cop (.cv x) (.cv r))))
        (syn_cins2 (syn_cins3 (syn_csset))))
      (.classMem (syn_cop (syn_csn (.cv y)) (syn_cop (.cv x) (.cv r))) (syn_cins3 (syn_csset)))
      (.classMem (syn_cop (syn_csn (.cv y)) (.cv x)) (syn_csset)) (.objMem y x) p0019
      p0020 p0023_e02_recanon
  have p0024 :=
    @g_eldif
      (syn_cop (syn_csn (.cv y)) (syn_cop (syn_csn (.cv z)) (syn_cop (.cv x) (.cv r))))
      (syn_cima (syn_cin (syn_cins4 (syn_csi3 (syn_cid)))
          (syn_cins2 (syn_cins2 (syn_cins2 (syn_csset))))) (syn_c1c))
      (syn_cins3 (syn_cid))
  have p0025 :=
    @g_elin
      (syn_cop (syn_csn (.cv t))
        (syn_cop (syn_csn (.cv y)) (syn_cop (syn_csn (.cv z)) (syn_cop (.cv x) (.cv r)))))
      (syn_cins4 (syn_csi3 (syn_cid))) (syn_cins2 (syn_cins2 (syn_cins2 (syn_csset))))
  have p0026 :=
    @g_oqelins4 (syn_csn (.cv t)) (syn_csn (.cv y)) (syn_csn (.cv z))
      (syn_cop (.cv x) (.cv r)) (syn_csi3 (syn_cid)) p0008
  have p0027 := @g_vex t
  have p0028 := @g_otsnelsi3 (.cv t) (.cv y) (.cv z) (syn_cid) p0027 p0021 p0012
  have p0029 := (Nominal.biimpRefl (syn_wbr (.cv t) (syn_cid) (syn_cop (.cv y) (.cv z))))
  have p0030 := @g_opex (.cv y) (.cv z) p0021 p0012
  have p0031 := @g_ideq (.cv t) (syn_cop (.cv y) (.cv z)) p0030
  have p0032 :=
    @g_bitr3i (.classMem (syn_cop (.cv t) (syn_cop (.cv y) (.cv z))) (syn_cid))
      (syn_wbr (.cv t) (syn_cid) (syn_cop (.cv y) (.cv z)))
      (.classEq (.cv t) (syn_cop (.cv y) (.cv z))) p0029 p0031
  have p0033 :=
    @g_n_3bitri
      (.classMem (syn_cop (syn_csn (.cv t)) (syn_cop (syn_csn (.cv y))
            (syn_cop (syn_csn (.cv z)) (syn_cop (.cv x) (.cv r)))))
        (syn_cins4 (syn_csi3 (syn_cid))))
      (.classMem (syn_cop (syn_csn (.cv t)) (syn_cop (syn_csn (.cv y)) (syn_csn (.cv z))))
        (syn_csi3 (syn_cid)))
      (.classMem (syn_cop (.cv t) (syn_cop (.cv y) (.cv z))) (syn_cid))
      (.classEq (.cv t) (syn_cop (.cv y) (.cv z))) p0026 p0028 p0032
  have p0034 := @g_snex (.cv y)
  have p0035 :=
    @g_otelins2 (syn_csn (.cv t)) (syn_csn (.cv y))
      (syn_cop (syn_csn (.cv z)) (syn_cop (.cv x) (.cv r)))
      (syn_cins2 (syn_cins2 (syn_csset))) p0034
  have p0036 :=
    @g_otelins2 (syn_csn (.cv t)) (syn_csn (.cv z)) (syn_cop (.cv x) (.cv r))
      (syn_cins2 (syn_csset)) p0015
  have p0037 := @g_otelins2 (syn_csn (.cv t)) (.cv x) (.cv r) (syn_csset) p0007
  have p0038 := @g_opelssetsn (.cv t) (.cv r) p0027 p0001
  have p0039_e01_recanon :
    Nominal.NPrf
      (syn_wb (.classMem (syn_cop (syn_csn (.cv t)) (.cv r)) (syn_csset)) (.objMem t r)) :=
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
      p0038
  have p0039 :=
    @g_bitri
      (.classMem (syn_cop (syn_csn (.cv t)) (syn_cop (.cv x) (.cv r))) (syn_cins2 (syn_csset)))
      (.classMem (syn_cop (syn_csn (.cv t)) (.cv r)) (syn_csset)) (.objMem t r) p0037
      p0039_e01_recanon
  have p0040 :=
    @g_n_3bitri
      (.classMem (syn_cop (syn_csn (.cv t)) (syn_cop (syn_csn (.cv y))
            (syn_cop (syn_csn (.cv z)) (syn_cop (.cv x) (.cv r)))))
        (syn_cins2 (syn_cins2 (syn_cins2 (syn_csset)))))
      (.classMem
        (syn_cop (syn_csn (.cv t)) (syn_cop (syn_csn (.cv z)) (syn_cop (.cv x) (.cv r))))
        (syn_cins2 (syn_cins2 (syn_csset))))
      (.classMem (syn_cop (syn_csn (.cv t)) (syn_cop (.cv x) (.cv r))) (syn_cins2 (syn_csset)))
      (.objMem t r) p0035 p0036 p0039
  have p0041 :=
    @g_anbi12i
      (.classMem (syn_cop (syn_csn (.cv t)) (syn_cop (syn_csn (.cv y))
            (syn_cop (syn_csn (.cv z)) (syn_cop (.cv x) (.cv r)))))
        (syn_cins4 (syn_csi3 (syn_cid))))
      (.classEq (.cv t) (syn_cop (.cv y) (.cv z)))
      (.classMem (syn_cop (syn_csn (.cv t)) (syn_cop (syn_csn (.cv y))
            (syn_cop (syn_csn (.cv z)) (syn_cop (.cv x) (.cv r)))))
        (syn_cins2 (syn_cins2 (syn_cins2 (syn_csset)))))
      (.objMem t r) p0033 p0040
  have p0042 :=
    @g_bitri
      (.classMem (syn_cop (syn_csn (.cv t)) (syn_cop (syn_csn (.cv y))
            (syn_cop (syn_csn (.cv z)) (syn_cop (.cv x) (.cv r)))))
        (syn_cin (syn_cins4 (syn_csi3 (syn_cid)))
          (syn_cins2 (syn_cins2 (syn_cins2 (syn_csset))))))
      (syn_wa (.classMem (syn_cop (syn_csn (.cv t)) (syn_cop (syn_csn (.cv y))
              (syn_cop (syn_csn (.cv z)) (syn_cop (.cv x) (.cv r)))))
          (syn_cins4 (syn_csi3 (syn_cid)))) (.classMem (syn_cop (syn_csn (.cv t))
            (syn_cop (syn_csn (.cv y)) (syn_cop (syn_csn (.cv z)) (syn_cop (.cv x) (.cv r)))))
          (syn_cins2 (syn_cins2 (syn_cins2 (syn_csset))))))
      (syn_wa (.classEq (.cv t) (syn_cop (.cv y) (.cv z))) (.objMem t r)) p0025 p0041
  have p0043 :=
    @g_exbii
      (.classMem (syn_cop (syn_csn (.cv t)) (syn_cop (syn_csn (.cv y))
            (syn_cop (syn_csn (.cv z)) (syn_cop (.cv x) (.cv r)))))
        (syn_cin (syn_cins4 (syn_csi3 (syn_cid)))
          (syn_cins2 (syn_cins2 (syn_cins2 (syn_csset))))))
      (syn_wa (.classEq (.cv t) (syn_cop (.cv y) (.cv z))) (.objMem t r)) t p0042
  have p0044 :=
    @g_elima1c t
      (syn_cop (syn_csn (.cv y)) (syn_cop (syn_csn (.cv z)) (syn_cop (.cv x) (.cv r))))
      (syn_cin (syn_cins4 (syn_csi3 (syn_cid))) (syn_cins2 (syn_cins2 (syn_cins2 (syn_csset)))))
      dv_cache_0013 dv_cache_0014
  have p0045 := (Nominal.biimpRefl (syn_wbr (.cv y) (.cv r) (.cv z)))
  have p0046 :=
    (NFChoice.DirectNominalPrf.Nominal.DefinitionLeafHandlersCanonical001.dfClelOfDV t
      (syn_cop (.cv y) (.cv z)) (.cv r) dv_cache_0015 dv_cache_0016)
  have p0047_e01_recanon :
    Nominal.NPrf
      (syn_wb (.classMem (syn_cop (.cv y) (.cv z)) (.cv r)) (syn_wex t
          (syn_wa (.classEq (.cv t) (syn_cop (.cv y) (.cv z))) (.objMem t r)))) :=
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
      p0046
  have p0047 :=
    @g_bitri (syn_wbr (.cv y) (.cv r) (.cv z))
      (.classMem (syn_cop (.cv y) (.cv z)) (.cv r))
      (syn_wex t (syn_wa (.classEq (.cv t) (syn_cop (.cv y) (.cv z))) (.objMem t r)))
      p0045 p0047_e01_recanon
  have p0048 :=
    @g_n_3bitr4i
      (syn_wex t (.classMem (syn_cop (syn_csn (.cv t)) (syn_cop (syn_csn (.cv y))
              (syn_cop (syn_csn (.cv z)) (syn_cop (.cv x) (.cv r)))))
          (syn_cin (syn_cins4 (syn_csi3 (syn_cid)))
            (syn_cins2 (syn_cins2 (syn_cins2 (syn_csset)))))))
      (syn_wex t (syn_wa (.classEq (.cv t) (syn_cop (.cv y) (.cv z))) (.objMem t r)))
      (.classMem
        (syn_cop (syn_csn (.cv y)) (syn_cop (syn_csn (.cv z)) (syn_cop (.cv x) (.cv r))))
        (syn_cima (syn_cin (syn_cins4 (syn_csi3 (syn_cid)))
            (syn_cins2 (syn_cins2 (syn_cins2 (syn_csset))))) (syn_c1c)))
      (syn_wbr (.cv y) (.cv r) (.cv z)) p0043 p0044 p0047
  have p0049 :=
    @g_otelins3 (syn_csn (.cv y)) (syn_csn (.cv z)) (syn_cop (.cv x) (.cv r)) (syn_cid)
      p0008
  have p0050 :=
    (Nominal.biimpRefl (syn_wbr (syn_csn (.cv y)) (syn_cid) (syn_csn (.cv z))))
  have p0051 := @g_ideq (syn_csn (.cv y)) (syn_csn (.cv z)) p0015
  have p0052 := @g_sneqb (.cv y) (.cv z) p0021
  have p0053_e01_recanon :
    Nominal.NPrf (syn_wb (.classEq (syn_csn (.cv y)) (syn_csn (.cv z))) (.objEq y z)) :=
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
    @g_bitri (syn_wbr (syn_csn (.cv y)) (syn_cid) (syn_csn (.cv z)))
      (.classEq (syn_csn (.cv y)) (syn_csn (.cv z))) (.objEq y z) p0051 p0053_e01_recanon
  have p0054 :=
    @g_bitr3i (.classMem (syn_cop (syn_csn (.cv y)) (syn_csn (.cv z))) (syn_cid))
      (syn_wbr (syn_csn (.cv y)) (syn_cid) (syn_csn (.cv z))) (.objEq y z) p0050 p0053
  have p0055 :=
    @g_bitri
      (.classMem
        (syn_cop (syn_csn (.cv y)) (syn_cop (syn_csn (.cv z)) (syn_cop (.cv x) (.cv r))))
        (syn_cins3 (syn_cid)))
      (.classMem (syn_cop (syn_csn (.cv y)) (syn_csn (.cv z))) (syn_cid)) (.objEq y z)
      p0049 p0054
  have p0056 :=
    @g_notbii
      (.classMem
        (syn_cop (syn_csn (.cv y)) (syn_cop (syn_csn (.cv z)) (syn_cop (.cv x) (.cv r))))
        (syn_cins3 (syn_cid)))
      (.objEq y z) p0055
  have p0057 :=
    @g_anbi12i
      (.classMem
        (syn_cop (syn_csn (.cv y)) (syn_cop (syn_csn (.cv z)) (syn_cop (.cv x) (.cv r))))
        (syn_cima (syn_cin (syn_cins4 (syn_csi3 (syn_cid)))
            (syn_cins2 (syn_cins2 (syn_cins2 (syn_csset))))) (syn_c1c)))
      (syn_wbr (.cv y) (.cv r) (.cv z))
      (.neg (.classMem (syn_cop (syn_csn (.cv y))
            (syn_cop (syn_csn (.cv z)) (syn_cop (.cv x) (.cv r)))) (syn_cins3 (syn_cid))))
      (.neg (.objEq y z)) p0048 p0056
  have p0058 :=
    @g_bitri
      (.classMem
        (syn_cop (syn_csn (.cv y)) (syn_cop (syn_csn (.cv z)) (syn_cop (.cv x) (.cv r))))
        (syn_cdif (syn_cima (syn_cin (syn_cins4 (syn_csi3 (syn_cid)))
              (syn_cins2 (syn_cins2 (syn_cins2 (syn_csset))))) (syn_c1c))
          (syn_cins3 (syn_cid))))
      (syn_wa (.classMem (syn_cop (syn_csn (.cv y))
            (syn_cop (syn_csn (.cv z)) (syn_cop (.cv x) (.cv r)))) (syn_cima
            (syn_cin (syn_cins4 (syn_csi3 (syn_cid)))
              (syn_cins2 (syn_cins2 (syn_cins2 (syn_csset))))) (syn_c1c))) (.neg (.classMem
            (syn_cop (syn_csn (.cv y)) (syn_cop (syn_csn (.cv z)) (syn_cop (.cv x) (.cv r))))
            (syn_cins3 (syn_cid)))))
      (syn_wa (syn_wbr (.cv y) (.cv r) (.cv z)) (.neg (.objEq y z))) p0024 p0057
  have p0059 :=
    @g_anbi12i
      (.classMem
        (syn_cop (syn_csn (.cv y)) (syn_cop (syn_csn (.cv z)) (syn_cop (.cv x) (.cv r))))
        (syn_cins2 (syn_cins3 (syn_csset))))
      (.objMem y x)
      (.classMem
        (syn_cop (syn_csn (.cv y)) (syn_cop (syn_csn (.cv z)) (syn_cop (.cv x) (.cv r))))
        (syn_cdif (syn_cima (syn_cin (syn_cins4 (syn_csi3 (syn_cid)))
              (syn_cins2 (syn_cins2 (syn_cins2 (syn_csset))))) (syn_c1c))
          (syn_cins3 (syn_cid))))
      (syn_wa (syn_wbr (.cv y) (.cv r) (.cv z)) (.neg (.objEq y z))) p0023 p0058
  have p0060 :=
    @g_bitri
      (.classMem
        (syn_cop (syn_csn (.cv y)) (syn_cop (syn_csn (.cv z)) (syn_cop (.cv x) (.cv r))))
        (syn_cin (syn_cins2 (syn_cins3 (syn_csset))) (syn_cdif (syn_cima
              (syn_cin (syn_cins4 (syn_csi3 (syn_cid)))
                (syn_cins2 (syn_cins2 (syn_cins2 (syn_csset))))) (syn_c1c))
            (syn_cins3 (syn_cid)))))
      (syn_wa (.classMem (syn_cop (syn_csn (.cv y))
            (syn_cop (syn_csn (.cv z)) (syn_cop (.cv x) (.cv r))))
          (syn_cins2 (syn_cins3 (syn_csset)))) (.classMem (syn_cop (syn_csn (.cv y))
            (syn_cop (syn_csn (.cv z)) (syn_cop (.cv x) (.cv r)))) (syn_cdif (syn_cima
              (syn_cin (syn_cins4 (syn_csi3 (syn_cid)))
                (syn_cins2 (syn_cins2 (syn_cins2 (syn_csset))))) (syn_c1c))
            (syn_cins3 (syn_cid)))))
      (syn_wa (.objMem y x) (syn_wa (syn_wbr (.cv y) (.cv r) (.cv z)) (.neg (.objEq y z))))
      p0018 p0059
  have p0061 :=
    @g_exbii
      (.classMem
        (syn_cop (syn_csn (.cv y)) (syn_cop (syn_csn (.cv z)) (syn_cop (.cv x) (.cv r))))
        (syn_cin (syn_cins2 (syn_cins3 (syn_csset))) (syn_cdif (syn_cima
              (syn_cin (syn_cins4 (syn_csi3 (syn_cid)))
                (syn_cins2 (syn_cins2 (syn_cins2 (syn_csset))))) (syn_c1c))
            (syn_cins3 (syn_cid)))))
      (syn_wa (.objMem y x) (syn_wa (syn_wbr (.cv y) (.cv r) (.cv z)) (.neg (.objEq y z))))
      y p0060
  have p0062 :=
    @g_elima1c y (syn_cop (syn_csn (.cv z)) (syn_cop (.cv x) (.cv r)))
      (syn_cin (syn_cins2 (syn_cins3 (syn_csset))) (syn_cdif (syn_cima
            (syn_cin (syn_cins4 (syn_csi3 (syn_cid)))
              (syn_cins2 (syn_cins2 (syn_cins2 (syn_csset))))) (syn_c1c))
          (syn_cins3 (syn_cid))))
      dv_cache_0017 dv_cache_0018
  have p0063 :=
    (Nominal.biimpRefl
      (syn_wrex y (.cv x) (syn_wa (syn_wbr (.cv y) (.cv r) (.cv z)) (.neg (.objEq y z)))))
  have p0064_e02_recanon :
    Nominal.NPrf
      (syn_wb (syn_wrex y (.cv x)
          (syn_wa (syn_wbr (.cv y) (.cv r) (.cv z)) (.neg (.objEq y z)))) (syn_wex y
          (syn_wa (.objMem y x)
            (syn_wa (syn_wbr (.cv y) (.cv r) (.cv z)) (.neg (.objEq y z)))))) :=
    Nominal.RecanonTransportDev.transport
      (by
        simp only [syn_wb, syn_wrex, syn_wex, syn_wa]
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
    @g_n_3bitr4i
      (syn_wex y (.classMem (syn_cop (syn_csn (.cv y))
            (syn_cop (syn_csn (.cv z)) (syn_cop (.cv x) (.cv r))))
          (syn_cin (syn_cins2 (syn_cins3 (syn_csset))) (syn_cdif (syn_cima
                (syn_cin (syn_cins4 (syn_csi3 (syn_cid)))
                  (syn_cins2 (syn_cins2 (syn_cins2 (syn_csset))))) (syn_c1c))
              (syn_cins3 (syn_cid))))))
      (syn_wex y (syn_wa (.objMem y x)
          (syn_wa (syn_wbr (.cv y) (.cv r) (.cv z)) (.neg (.objEq y z)))))
      (.classMem (syn_cop (syn_csn (.cv z)) (syn_cop (.cv x) (.cv r))) (syn_cima
          (syn_cin (syn_cins2 (syn_cins3 (syn_csset))) (syn_cdif (syn_cima
                (syn_cin (syn_cins4 (syn_csi3 (syn_cid)))
                  (syn_cins2 (syn_cins2 (syn_cins2 (syn_csset))))) (syn_c1c))
              (syn_cins3 (syn_cid)))) (syn_c1c)))
      (syn_wrex y (.cv x) (syn_wa (syn_wbr (.cv y) (.cv r) (.cv z)) (.neg (.objEq y z))))
      p0061 p0062 p0064_e02_recanon
  have p0065 := @g_rexanali (syn_wbr (.cv y) (.cv r) (.cv z)) (.objEq y z) y (.cv x)
  have p0066 :=
    @g_bitri
      (.classMem (syn_cop (syn_csn (.cv z)) (syn_cop (.cv x) (.cv r))) (syn_cima
          (syn_cin (syn_cins2 (syn_cins3 (syn_csset))) (syn_cdif (syn_cima
                (syn_cin (syn_cins4 (syn_csi3 (syn_cid)))
                  (syn_cins2 (syn_cins2 (syn_cins2 (syn_csset))))) (syn_c1c))
              (syn_cins3 (syn_cid)))) (syn_c1c)))
      (syn_wrex y (.cv x) (syn_wa (syn_wbr (.cv y) (.cv r) (.cv z)) (.neg (.objEq y z))))
      (.neg (syn_wral y (.cv x) (.imp (syn_wbr (.cv y) (.cv r) (.cv z)) (.objEq y z))))
      p0064 p0065
  have p0067 :=
    @g_con2bii
      (.classMem (syn_cop (syn_csn (.cv z)) (syn_cop (.cv x) (.cv r))) (syn_cima
          (syn_cin (syn_cins2 (syn_cins3 (syn_csset))) (syn_cdif (syn_cima
                (syn_cin (syn_cins4 (syn_csi3 (syn_cid)))
                  (syn_cins2 (syn_cins2 (syn_cins2 (syn_csset))))) (syn_c1c))
              (syn_cins3 (syn_cid)))) (syn_c1c)))
      (syn_wral y (.cv x) (.imp (syn_wbr (.cv y) (.cv r) (.cv z)) (.objEq y z))) p0066
  have p0068 :=
    @g_bitr4i
      (.classMem (syn_cop (syn_csn (.cv z)) (syn_cop (.cv x) (.cv r))) (syn_ccompl (syn_cima
            (syn_cin (syn_cins2 (syn_cins3 (syn_csset))) (syn_cdif (syn_cima
                  (syn_cin (syn_cins4 (syn_csi3 (syn_cid)))
                    (syn_cins2 (syn_cins2 (syn_cins2 (syn_csset))))) (syn_c1c))
                (syn_cins3 (syn_cid)))) (syn_c1c))))
      (.neg (.classMem (syn_cop (syn_csn (.cv z)) (syn_cop (.cv x) (.cv r))) (syn_cima
            (syn_cin (syn_cins2 (syn_cins3 (syn_csset))) (syn_cdif (syn_cima
                  (syn_cin (syn_cins4 (syn_csi3 (syn_cid)))
                    (syn_cins2 (syn_cins2 (syn_cins2 (syn_csset))))) (syn_c1c))
                (syn_cins3 (syn_cid)))) (syn_c1c))))
      (syn_wral y (.cv x) (.imp (syn_wbr (.cv y) (.cv r) (.cv z)) (.objEq y z))) p0017
      p0067
  have p0069 :=
    @g_anbi12i
      (.classMem (syn_cop (syn_csn (.cv z)) (syn_cop (.cv x) (.cv r))) (syn_cins3 (syn_csset)))
      (.objMem z x)
      (.classMem (syn_cop (syn_csn (.cv z)) (syn_cop (.cv x) (.cv r))) (syn_ccompl (syn_cima
            (syn_cin (syn_cins2 (syn_cins3 (syn_csset))) (syn_cdif (syn_cima
                  (syn_cin (syn_cins4 (syn_csi3 (syn_cid)))
                    (syn_cins2 (syn_cins2 (syn_cins2 (syn_csset))))) (syn_c1c))
                (syn_cins3 (syn_cid)))) (syn_c1c))))
      (syn_wral y (.cv x) (.imp (syn_wbr (.cv y) (.cv r) (.cv z)) (.objEq y z))) p0014
      p0068
  have p0070 :=
    @g_bitri
      (.classMem (syn_cop (syn_csn (.cv z)) (syn_cop (.cv x) (.cv r)))
        (syn_cin (syn_cins3 (syn_csset)) (syn_ccompl (syn_cima
              (syn_cin (syn_cins2 (syn_cins3 (syn_csset))) (syn_cdif (syn_cima
                    (syn_cin (syn_cins4 (syn_csi3 (syn_cid)))
                      (syn_cins2 (syn_cins2 (syn_cins2 (syn_csset))))) (syn_c1c))
                  (syn_cins3 (syn_cid)))) (syn_c1c)))))
      (syn_wa (.classMem (syn_cop (syn_csn (.cv z)) (syn_cop (.cv x) (.cv r)))
          (syn_cins3 (syn_csset)))
        (.classMem (syn_cop (syn_csn (.cv z)) (syn_cop (.cv x) (.cv r))) (syn_ccompl (syn_cima
              (syn_cin (syn_cins2 (syn_cins3 (syn_csset))) (syn_cdif (syn_cima
                    (syn_cin (syn_cins4 (syn_csi3 (syn_cid)))
                      (syn_cins2 (syn_cins2 (syn_cins2 (syn_csset))))) (syn_c1c))
                  (syn_cins3 (syn_cid)))) (syn_c1c)))))
      (syn_wa (.objMem z x)
        (syn_wral y (.cv x) (.imp (syn_wbr (.cv y) (.cv r) (.cv z)) (.objEq y z))))
      p0010 p0069
  have p0071 :=
    @g_exbii
      (.classMem (syn_cop (syn_csn (.cv z)) (syn_cop (.cv x) (.cv r)))
        (syn_cin (syn_cins3 (syn_csset)) (syn_ccompl (syn_cima
              (syn_cin (syn_cins2 (syn_cins3 (syn_csset))) (syn_cdif (syn_cima
                    (syn_cin (syn_cins4 (syn_csi3 (syn_cid)))
                      (syn_cins2 (syn_cins2 (syn_cins2 (syn_csset))))) (syn_c1c))
                  (syn_cins3 (syn_cid)))) (syn_c1c)))))
      (syn_wa (.objMem z x)
        (syn_wral y (.cv x) (.imp (syn_wbr (.cv y) (.cv r) (.cv z)) (.objEq y z))))
      z p0070
  have p0072 :=
    @g_elima1c z (syn_cop (.cv x) (.cv r))
      (syn_cin (syn_cins3 (syn_csset)) (syn_ccompl (syn_cima
            (syn_cin (syn_cins2 (syn_cins3 (syn_csset))) (syn_cdif (syn_cima
                  (syn_cin (syn_cins4 (syn_csi3 (syn_cid)))
                    (syn_cins2 (syn_cins2 (syn_cins2 (syn_csset))))) (syn_c1c))
                (syn_cins3 (syn_cid)))) (syn_c1c))))
      dv_cache_0019 dv_cache_0020
  have p0073 :=
    (Nominal.biimpRefl (syn_wrex z (.cv x)
        (syn_wral y (.cv x) (.imp (syn_wbr (.cv y) (.cv r) (.cv z)) (.objEq y z)))))
  have p0074_e02_recanon :
    Nominal.NPrf
      (syn_wb (syn_wrex z (.cv x)
          (syn_wral y (.cv x) (.imp (syn_wbr (.cv y) (.cv r) (.cv z)) (.objEq y z)))) (syn_wex z
          (syn_wa (.objMem z x) (syn_wral y (.cv x)
              (.imp (syn_wbr (.cv y) (.cv r) (.cv z)) (.objEq y z)))))) :=
    Nominal.RecanonTransportDev.transport
      (by
        simp only [syn_wb, syn_wrex, syn_wex, syn_wa, syn_wral, syn_wbr, syn_cop, syn_cun,
          syn_cnin, syn_wnan, syn_ccompl]
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
    @g_n_3bitr4i
      (syn_wex z (.classMem (syn_cop (syn_csn (.cv z)) (syn_cop (.cv x) (.cv r)))
          (syn_cin (syn_cins3 (syn_csset)) (syn_ccompl (syn_cima
                (syn_cin (syn_cins2 (syn_cins3 (syn_csset))) (syn_cdif (syn_cima
                      (syn_cin (syn_cins4 (syn_csi3 (syn_cid)))
                        (syn_cins2 (syn_cins2 (syn_cins2 (syn_csset))))) (syn_c1c))
                    (syn_cins3 (syn_cid)))) (syn_c1c))))))
      (syn_wex z (syn_wa (.objMem z x)
          (syn_wral y (.cv x) (.imp (syn_wbr (.cv y) (.cv r) (.cv z)) (.objEq y z)))))
      (.classMem (syn_cop (.cv x) (.cv r)) (syn_cima (syn_cin (syn_cins3 (syn_csset))
            (syn_ccompl (syn_cima (syn_cin (syn_cins2 (syn_cins3 (syn_csset))) (syn_cdif
                    (syn_cima (syn_cin (syn_cins4 (syn_csi3 (syn_cid)))
                        (syn_cins2 (syn_cins2 (syn_cins2 (syn_csset))))) (syn_c1c))
                    (syn_cins3 (syn_cid)))) (syn_c1c)))) (syn_c1c)))
      (syn_wrex z (.cv x)
        (syn_wral y (.cv x) (.imp (syn_wbr (.cv y) (.cv r) (.cv z)) (.objEq y z))))
      p0071 p0072 p0074_e02_recanon
  have p0075 :=
    @g_notbii
      (.classMem (syn_cop (.cv x) (.cv r)) (syn_cima (syn_cin (syn_cins3 (syn_csset))
            (syn_ccompl (syn_cima (syn_cin (syn_cins2 (syn_cins3 (syn_csset))) (syn_cdif
                    (syn_cima (syn_cin (syn_cins4 (syn_csi3 (syn_cid)))
                        (syn_cins2 (syn_cins2 (syn_cins2 (syn_csset))))) (syn_c1c))
                    (syn_cins3 (syn_cid)))) (syn_c1c)))) (syn_c1c)))
      (syn_wrex z (.cv x)
        (syn_wral y (.cv x) (.imp (syn_wbr (.cv y) (.cv r) (.cv z)) (.objEq y z))))
      p0074
  have p0076 :=
    @g_bitri
      (.classMem (syn_cop (.cv x) (.cv r)) (syn_ccompl (syn_cima
            (syn_cin (syn_cins3 (syn_csset)) (syn_ccompl (syn_cima
                  (syn_cin (syn_cins2 (syn_cins3 (syn_csset))) (syn_cdif (syn_cima
                        (syn_cin (syn_cins4 (syn_csi3 (syn_cid)))
                          (syn_cins2 (syn_cins2 (syn_cins2 (syn_csset))))) (syn_c1c))
                      (syn_cins3 (syn_cid)))) (syn_c1c)))) (syn_c1c))))
      (.neg (.classMem (syn_cop (.cv x) (.cv r)) (syn_cima (syn_cin (syn_cins3 (syn_csset))
              (syn_ccompl (syn_cima (syn_cin (syn_cins2 (syn_cins3 (syn_csset))) (syn_cdif
                      (syn_cima (syn_cin (syn_cins4 (syn_csi3 (syn_cid)))
                          (syn_cins2 (syn_cins2 (syn_cins2 (syn_csset))))) (syn_c1c))
                      (syn_cins3 (syn_cid)))) (syn_c1c)))) (syn_c1c))))
      (.neg (syn_wrex z (.cv x)
          (syn_wral y (.cv x) (.imp (syn_wbr (.cv y) (.cv r) (.cv z)) (.objEq y z)))))
      p0009 p0075
  have p0077 :=
    @g_elin (syn_cop (.cv x) (.cv a)) (syn_csset)
      (syn_cxp (syn_ccompl (syn_csn (syn_c0))) (syn_cvv))
  have p0078 := (Nominal.biimpRefl (syn_wbr (.cv x) (syn_csset) (.cv a)))
  have p0079 := @g_brsset (.cv x) (.cv a) p0007 p0002
  have p0080 :=
    @g_bitr3i (.classMem (syn_cop (.cv x) (.cv a)) (syn_csset))
      (syn_wbr (.cv x) (syn_csset) (.cv a)) (syn_wss (.cv x) (.cv a)) p0078 p0079
  have p0081 := @g_opelxp (.cv x) (.cv a) (syn_ccompl (syn_csn (syn_c0))) (syn_cvv)
  have p0082 :=
    @g_mpbiran2
      (.classMem (syn_cop (.cv x) (.cv a)) (syn_cxp (syn_ccompl (syn_csn (syn_c0))) (syn_cvv)))
      (.classMem (.cv x) (syn_ccompl (syn_csn (syn_c0)))) (.classMem (.cv a) (syn_cvv))
      p0002 p0081
  have p0083 := @g_elcompl (.cv x) (syn_csn (syn_c0)) p0007
  have p0084 := @g_elsn x (syn_c0) dv_cache_0021
  have p0085 :=
    @g_necon3bbii (.classMem (.cv x) (syn_csn (syn_c0))) (.cv x) (syn_c0) p0084
  have p0086 :=
    @g_n_3bitri
      (.classMem (syn_cop (.cv x) (.cv a)) (syn_cxp (syn_ccompl (syn_csn (syn_c0))) (syn_cvv)))
      (.classMem (.cv x) (syn_ccompl (syn_csn (syn_c0))))
      (.neg (.classMem (.cv x) (syn_csn (syn_c0)))) (syn_wne (.cv x) (syn_c0)) p0082 p0083
      p0085
  have p0087 :=
    @g_anbi12i (.classMem (syn_cop (.cv x) (.cv a)) (syn_csset)) (syn_wss (.cv x) (.cv a))
      (.classMem (syn_cop (.cv x) (.cv a)) (syn_cxp (syn_ccompl (syn_csn (syn_c0))) (syn_cvv)))
      (syn_wne (.cv x) (syn_c0)) p0080 p0086
  have p0088 :=
    @g_bitri
      (.classMem (syn_cop (.cv x) (.cv a))
        (syn_cin (syn_csset) (syn_cxp (syn_ccompl (syn_csn (syn_c0))) (syn_cvv))))
      (syn_wa (.classMem (syn_cop (.cv x) (.cv a)) (syn_csset))
        (.classMem (syn_cop (.cv x) (.cv a))
          (syn_cxp (syn_ccompl (syn_csn (syn_c0))) (syn_cvv))))
      (syn_wa (syn_wss (.cv x) (.cv a)) (syn_wne (.cv x) (syn_c0))) p0077 p0087
  have p0089 :=
    @g_anbi12ci
      (.classMem (syn_cop (.cv x) (.cv r)) (syn_ccompl (syn_cima
            (syn_cin (syn_cins3 (syn_csset)) (syn_ccompl (syn_cima
                  (syn_cin (syn_cins2 (syn_cins3 (syn_csset))) (syn_cdif (syn_cima
                        (syn_cin (syn_cins4 (syn_csi3 (syn_cid)))
                          (syn_cins2 (syn_cins2 (syn_cins2 (syn_csset))))) (syn_c1c))
                      (syn_cins3 (syn_cid)))) (syn_c1c)))) (syn_c1c))))
      (.neg (syn_wrex z (.cv x)
          (syn_wral y (.cv x) (.imp (syn_wbr (.cv y) (.cv r) (.cv z)) (.objEq y z)))))
      (.classMem (syn_cop (.cv x) (.cv a))
        (syn_cin (syn_csset) (syn_cxp (syn_ccompl (syn_csn (syn_c0))) (syn_cvv))))
      (syn_wa (syn_wss (.cv x) (.cv a)) (syn_wne (.cv x) (syn_c0))) p0076 p0088
  have p0090 :=
    @g_bitri
      (.classMem (syn_cop (.cv x) (syn_cop (.cv r) (.cv a))) (syn_ctxp (syn_ccompl (syn_cima
              (syn_cin (syn_cins3 (syn_csset)) (syn_ccompl (syn_cima
                    (syn_cin (syn_cins2 (syn_cins3 (syn_csset))) (syn_cdif (syn_cima
                          (syn_cin (syn_cins4 (syn_csi3 (syn_cid)))
                            (syn_cins2 (syn_cins2 (syn_cins2 (syn_csset))))) (syn_c1c))
                        (syn_cins3 (syn_cid)))) (syn_c1c)))) (syn_c1c)))
          (syn_cin (syn_csset) (syn_cxp (syn_ccompl (syn_csn (syn_c0))) (syn_cvv)))))
      (syn_wa (.classMem (syn_cop (.cv x) (.cv r)) (syn_ccompl (syn_cima
              (syn_cin (syn_cins3 (syn_csset)) (syn_ccompl (syn_cima
                    (syn_cin (syn_cins2 (syn_cins3 (syn_csset))) (syn_cdif (syn_cima
                          (syn_cin (syn_cins4 (syn_csi3 (syn_cid)))
                            (syn_cins2 (syn_cins2 (syn_cins2 (syn_csset))))) (syn_c1c))
                        (syn_cins3 (syn_cid)))) (syn_c1c)))) (syn_c1c))))
        (.classMem (syn_cop (.cv x) (.cv a))
          (syn_cin (syn_csset) (syn_cxp (syn_ccompl (syn_csn (syn_c0))) (syn_cvv)))))
      (syn_wa (syn_wa (syn_wss (.cv x) (.cv a)) (syn_wne (.cv x) (syn_c0))) (.neg
          (syn_wrex z (.cv x)
            (syn_wral y (.cv x) (.imp (syn_wbr (.cv y) (.cv r) (.cv z)) (.objEq y z))))))
      p0006 p0089
  have p0091 :=
    @g_exbii
      (.classMem (syn_cop (.cv x) (syn_cop (.cv r) (.cv a))) (syn_ctxp (syn_ccompl (syn_cima
              (syn_cin (syn_cins3 (syn_csset)) (syn_ccompl (syn_cima
                    (syn_cin (syn_cins2 (syn_cins3 (syn_csset))) (syn_cdif (syn_cima
                          (syn_cin (syn_cins4 (syn_csi3 (syn_cid)))
                            (syn_cins2 (syn_cins2 (syn_cins2 (syn_csset))))) (syn_c1c))
                        (syn_cins3 (syn_cid)))) (syn_c1c)))) (syn_c1c)))
          (syn_cin (syn_csset) (syn_cxp (syn_ccompl (syn_csn (syn_c0))) (syn_cvv)))))
      (syn_wa (syn_wa (syn_wss (.cv x) (.cv a)) (syn_wne (.cv x) (syn_c0))) (.neg
          (syn_wrex z (.cv x)
            (syn_wral y (.cv x) (.imp (syn_wbr (.cv y) (.cv r) (.cv z)) (.objEq y z))))))
      x p0090
  have p0092 :=
    @g_exanali (syn_wa (syn_wss (.cv x) (.cv a)) (syn_wne (.cv x) (syn_c0)))
      (syn_wrex z (.cv x)
        (syn_wral y (.cv x) (.imp (syn_wbr (.cv y) (.cv r) (.cv z)) (.objEq y z))))
      x
  have p0093 :=
    @g_n_3bitri
      (.classMem (syn_cop (.cv r) (.cv a)) (syn_crn (syn_ctxp (syn_ccompl (syn_cima
                (syn_cin (syn_cins3 (syn_csset)) (syn_ccompl (syn_cima
                      (syn_cin (syn_cins2 (syn_cins3 (syn_csset))) (syn_cdif (syn_cima
                            (syn_cin (syn_cins4 (syn_csi3 (syn_cid)))
                              (syn_cins2 (syn_cins2 (syn_cins2 (syn_csset))))) (syn_c1c))
                          (syn_cins3 (syn_cid)))) (syn_c1c)))) (syn_c1c)))
            (syn_cin (syn_csset) (syn_cxp (syn_ccompl (syn_csn (syn_c0))) (syn_cvv))))))
      (syn_wex x (.classMem (syn_cop (.cv x) (syn_cop (.cv r) (.cv a))) (syn_ctxp (syn_ccompl
              (syn_cima (syn_cin (syn_cins3 (syn_csset)) (syn_ccompl (syn_cima
                      (syn_cin (syn_cins2 (syn_cins3 (syn_csset))) (syn_cdif (syn_cima
                            (syn_cin (syn_cins4 (syn_csi3 (syn_cid)))
                              (syn_cins2 (syn_cins2 (syn_cins2 (syn_csset))))) (syn_c1c))
                          (syn_cins3 (syn_cid)))) (syn_c1c)))) (syn_c1c)))
            (syn_cin (syn_csset) (syn_cxp (syn_ccompl (syn_csn (syn_c0))) (syn_cvv))))))
      (syn_wex x (syn_wa (syn_wa (syn_wss (.cv x) (.cv a)) (syn_wne (.cv x) (syn_c0))) (.neg
            (syn_wrex z (.cv x) (syn_wral y (.cv x)
                (.imp (syn_wbr (.cv y) (.cv r) (.cv z)) (.objEq y z)))))))
      (.neg (.all x (.imp (syn_wa (syn_wss (.cv x) (.cv a)) (syn_wne (.cv x) (syn_c0)))
            (syn_wrex z (.cv x) (syn_wral y (.cv x)
                (.imp (syn_wbr (.cv y) (.cv r) (.cv z)) (.objEq y z)))))))
      p0005 p0091 p0092
  have p0094 :=
    @g_con2bii
      (.classMem (syn_cop (.cv r) (.cv a)) (syn_crn (syn_ctxp (syn_ccompl (syn_cima
                (syn_cin (syn_cins3 (syn_csset)) (syn_ccompl (syn_cima
                      (syn_cin (syn_cins2 (syn_cins3 (syn_csset))) (syn_cdif (syn_cima
                            (syn_cin (syn_cins4 (syn_csi3 (syn_cid)))
                              (syn_cins2 (syn_cins2 (syn_cins2 (syn_csset))))) (syn_c1c))
                          (syn_cins3 (syn_cid)))) (syn_c1c)))) (syn_c1c)))
            (syn_cin (syn_csset) (syn_cxp (syn_ccompl (syn_csn (syn_c0))) (syn_cvv))))))
      (.all x (.imp (syn_wa (syn_wss (.cv x) (.cv a)) (syn_wne (.cv x) (syn_c0)))
          (syn_wrex z (.cv x)
            (syn_wral y (.cv x) (.imp (syn_wbr (.cv y) (.cv r) (.cv z)) (.objEq y z))))))
      p0093
  have p0095 :=
    @g_bitr4i
      (.classMem (syn_cop (.cv r) (.cv a)) (syn_ccompl (syn_crn (syn_ctxp (syn_ccompl (syn_cima
                  (syn_cin (syn_cins3 (syn_csset)) (syn_ccompl (syn_cima
                        (syn_cin (syn_cins2 (syn_cins3 (syn_csset))) (syn_cdif (syn_cima
                              (syn_cin (syn_cins4 (syn_csi3 (syn_cid)))
                                (syn_cins2 (syn_cins2 (syn_cins2 (syn_csset))))) (syn_c1c))
                            (syn_cins3 (syn_cid)))) (syn_c1c)))) (syn_c1c)))
              (syn_cin (syn_csset) (syn_cxp (syn_ccompl (syn_csn (syn_c0))) (syn_cvv)))))))
      (.neg (.classMem (syn_cop (.cv r) (.cv a)) (syn_crn (syn_ctxp (syn_ccompl (syn_cima
                  (syn_cin (syn_cins3 (syn_csset)) (syn_ccompl (syn_cima
                        (syn_cin (syn_cins2 (syn_cins3 (syn_csset))) (syn_cdif (syn_cima
                              (syn_cin (syn_cins4 (syn_csi3 (syn_cid)))
                                (syn_cins2 (syn_cins2 (syn_cins2 (syn_csset))))) (syn_c1c))
                            (syn_cins3 (syn_cid)))) (syn_c1c)))) (syn_c1c)))
              (syn_cin (syn_csset) (syn_cxp (syn_ccompl (syn_csn (syn_c0))) (syn_cvv)))))))
      (.all x (.imp (syn_wa (syn_wss (.cv x) (.cv a)) (syn_wne (.cv x) (syn_c0)))
          (syn_wrex z (.cv x)
            (syn_wral y (.cv x) (.imp (syn_wbr (.cv y) (.cv r) (.cv z)) (.objEq y z))))))
      p0004 p0094
  have p0096 :=
    @g_opabbi2i
      (.all x (.imp (syn_wa (syn_wss (.cv x) (.cv a)) (syn_wne (.cv x) (syn_c0)))
          (syn_wrex z (.cv x)
            (syn_wral y (.cv x) (.imp (syn_wbr (.cv y) (.cv r) (.cv z)) (.objEq y z))))))
      r a
      (syn_ccompl (syn_crn (syn_ctxp (syn_ccompl (syn_cima (syn_cin (syn_cins3 (syn_csset))
                  (syn_ccompl (syn_cima (syn_cin (syn_cins2 (syn_cins3 (syn_csset))) (syn_cdif
                          (syn_cima (syn_cin (syn_cins4 (syn_csi3 (syn_cid)))
                              (syn_cins2 (syn_cins2 (syn_cins2 (syn_csset))))) (syn_c1c))
                          (syn_cins3 (syn_cid)))) (syn_c1c)))) (syn_c1c)))
            (syn_cin (syn_csset) (syn_cxp (syn_ccompl (syn_csn (syn_c0))) (syn_cvv))))))
      dv_cache_0022 dv_cache_0023 dv_cache_0024 p0095
  have p0097 :=
    @g_eqtr4i (syn_cfound)
      (syn_copab r a (.all x (.imp (syn_wa (syn_wss (.cv x) (.cv a)) (syn_wne (.cv x) (syn_c0)))
            (syn_wrex z (.cv x) (syn_wral y (.cv x)
                (.imp (syn_wbr (.cv y) (.cv r) (.cv z)) (.objEq y z)))))))
      (syn_ccompl (syn_crn (syn_ctxp (syn_ccompl (syn_cima (syn_cin (syn_cins3 (syn_csset))
                  (syn_ccompl (syn_cima (syn_cin (syn_cins2 (syn_cins3 (syn_csset))) (syn_cdif
                          (syn_cima (syn_cin (syn_cins4 (syn_csi3 (syn_cid)))
                              (syn_cins2 (syn_cins2 (syn_cins2 (syn_csset))))) (syn_c1c))
                          (syn_cins3 (syn_cid)))) (syn_c1c)))) (syn_c1c)))
            (syn_cin (syn_csset) (syn_cxp (syn_ccompl (syn_csn (syn_c0))) (syn_cvv))))))
      p0000 p0096
  have p0098 := @g_ssetex
  have p0099 := @g_ins3ex (syn_csset) p0098
  have p0100 := @g_ins2ex (syn_cins3 (syn_csset)) p0099
  have p0101 := @g_idex
  have p0102 := @g_si3ex (syn_cid) p0101
  have p0103 := @g_ins4ex (syn_csi3 (syn_cid)) p0102
  have p0105 := @g_ins2ex (syn_csset) p0098
  have p0106 := @g_ins2ex (syn_cins2 (syn_csset)) p0105
  have p0107 := @g_ins2ex (syn_cins2 (syn_cins2 (syn_csset))) p0106
  have p0108 :=
    @g_inex (syn_cins4 (syn_csi3 (syn_cid)))
      (syn_cins2 (syn_cins2 (syn_cins2 (syn_csset)))) p0103 p0107
  have p0109 := @g_n_1cex
  have p0110 :=
    @g_imaex
      (syn_cin (syn_cins4 (syn_csi3 (syn_cid))) (syn_cins2 (syn_cins2 (syn_cins2 (syn_csset)))))
      (syn_c1c) p0108 p0109
  have p0112 := @g_ins3ex (syn_cid) p0101
  have p0113 :=
    @g_difex
      (syn_cima (syn_cin (syn_cins4 (syn_csi3 (syn_cid)))
          (syn_cins2 (syn_cins2 (syn_cins2 (syn_csset))))) (syn_c1c))
      (syn_cins3 (syn_cid)) p0110 p0112
  have p0114 :=
    @g_inex (syn_cins2 (syn_cins3 (syn_csset)))
      (syn_cdif (syn_cima (syn_cin (syn_cins4 (syn_csi3 (syn_cid)))
            (syn_cins2 (syn_cins2 (syn_cins2 (syn_csset))))) (syn_c1c)) (syn_cins3 (syn_cid)))
      p0100 p0113
  have p0116 :=
    @g_imaex
      (syn_cin (syn_cins2 (syn_cins3 (syn_csset))) (syn_cdif (syn_cima
            (syn_cin (syn_cins4 (syn_csi3 (syn_cid)))
              (syn_cins2 (syn_cins2 (syn_cins2 (syn_csset))))) (syn_c1c))
          (syn_cins3 (syn_cid))))
      (syn_c1c) p0114 p0109
  have p0117 :=
    @g_complex
      (syn_cima (syn_cin (syn_cins2 (syn_cins3 (syn_csset))) (syn_cdif (syn_cima
              (syn_cin (syn_cins4 (syn_csi3 (syn_cid)))
                (syn_cins2 (syn_cins2 (syn_cins2 (syn_csset))))) (syn_c1c))
            (syn_cins3 (syn_cid)))) (syn_c1c))
      p0116
  have p0118 :=
    @g_inex (syn_cins3 (syn_csset))
      (syn_ccompl (syn_cima (syn_cin (syn_cins2 (syn_cins3 (syn_csset))) (syn_cdif (syn_cima
                (syn_cin (syn_cins4 (syn_csi3 (syn_cid)))
                  (syn_cins2 (syn_cins2 (syn_cins2 (syn_csset))))) (syn_c1c))
              (syn_cins3 (syn_cid)))) (syn_c1c)))
      p0099 p0117
  have p0120 :=
    @g_imaex
      (syn_cin (syn_cins3 (syn_csset)) (syn_ccompl (syn_cima
            (syn_cin (syn_cins2 (syn_cins3 (syn_csset))) (syn_cdif (syn_cima
                  (syn_cin (syn_cins4 (syn_csi3 (syn_cid)))
                    (syn_cins2 (syn_cins2 (syn_cins2 (syn_csset))))) (syn_c1c))
                (syn_cins3 (syn_cid)))) (syn_c1c))))
      (syn_c1c) p0118 p0109
  have p0121 :=
    @g_complex
      (syn_cima (syn_cin (syn_cins3 (syn_csset)) (syn_ccompl (syn_cima
              (syn_cin (syn_cins2 (syn_cins3 (syn_csset))) (syn_cdif (syn_cima
                    (syn_cin (syn_cins4 (syn_csi3 (syn_cid)))
                      (syn_cins2 (syn_cins2 (syn_cins2 (syn_csset))))) (syn_c1c))
                  (syn_cins3 (syn_cid)))) (syn_c1c)))) (syn_c1c))
      p0120
  have p0123 := @g_snex (syn_c0)
  have p0124 := @g_complex (syn_csn (syn_c0)) p0123
  have p0125 := @g_vvex
  have p0126 := @g_xpex (syn_ccompl (syn_csn (syn_c0))) (syn_cvv) p0124 p0125
  have p0127 :=
    @g_inex (syn_csset) (syn_cxp (syn_ccompl (syn_csn (syn_c0))) (syn_cvv)) p0098 p0126
  have p0128 :=
    @g_txpex
      (syn_ccompl (syn_cima (syn_cin (syn_cins3 (syn_csset)) (syn_ccompl (syn_cima
                (syn_cin (syn_cins2 (syn_cins3 (syn_csset))) (syn_cdif (syn_cima
                      (syn_cin (syn_cins4 (syn_csi3 (syn_cid)))
                        (syn_cins2 (syn_cins2 (syn_cins2 (syn_csset))))) (syn_c1c))
                    (syn_cins3 (syn_cid)))) (syn_c1c)))) (syn_c1c)))
      (syn_cin (syn_csset) (syn_cxp (syn_ccompl (syn_csn (syn_c0))) (syn_cvv))) p0121
      p0127
  have p0129 :=
    @g_rnex
      (syn_ctxp (syn_ccompl (syn_cima (syn_cin (syn_cins3 (syn_csset)) (syn_ccompl (syn_cima
                  (syn_cin (syn_cins2 (syn_cins3 (syn_csset))) (syn_cdif (syn_cima
                        (syn_cin (syn_cins4 (syn_csi3 (syn_cid)))
                          (syn_cins2 (syn_cins2 (syn_cins2 (syn_csset))))) (syn_c1c))
                      (syn_cins3 (syn_cid)))) (syn_c1c)))) (syn_c1c)))
        (syn_cin (syn_csset) (syn_cxp (syn_ccompl (syn_csn (syn_c0))) (syn_cvv))))
      p0128
  have p0130 :=
    @g_complex
      (syn_crn (syn_ctxp (syn_ccompl (syn_cima (syn_cin (syn_cins3 (syn_csset)) (syn_ccompl
                  (syn_cima (syn_cin (syn_cins2 (syn_cins3 (syn_csset))) (syn_cdif (syn_cima
                          (syn_cin (syn_cins4 (syn_csi3 (syn_cid)))
                            (syn_cins2 (syn_cins2 (syn_cins2 (syn_csset))))) (syn_c1c))
                        (syn_cins3 (syn_cid)))) (syn_c1c)))) (syn_c1c)))
          (syn_cin (syn_csset) (syn_cxp (syn_ccompl (syn_csn (syn_c0))) (syn_cvv)))))
      p0129
  have p0131 :=
    @g_eqeltri (syn_cfound)
      (syn_ccompl (syn_crn (syn_ctxp (syn_ccompl (syn_cima (syn_cin (syn_cins3 (syn_csset))
                  (syn_ccompl (syn_cima (syn_cin (syn_cins2 (syn_cins3 (syn_csset))) (syn_cdif
                          (syn_cima (syn_cin (syn_cins4 (syn_csi3 (syn_cid)))
                              (syn_cins2 (syn_cins2 (syn_cins2 (syn_csset))))) (syn_c1c))
                          (syn_cins3 (syn_cid)))) (syn_c1c)))) (syn_c1c)))
            (syn_cin (syn_csset) (syn_cxp (syn_ccompl (syn_csn (syn_c0))) (syn_cvv))))))
      (syn_cvv) p0097 p0130
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

@[expose]
noncomputable def g_partialex : Nominal.NPrf (.classMem (syn_cpartial) (syn_cvv)) :=
  by
  have p0000 := (Nominal.classEqRefl (syn_cpartial))
  have p0001 := @g_refex
  have p0002 := @g_transex
  have p0003 := @g_inex (syn_cref) (syn_ctrans) p0001 p0002
  have p0004 := @g_antisymex
  have p0005 := @g_inex (syn_cin (syn_cref) (syn_ctrans)) (syn_cantisym) p0003 p0004
  have p0006 :=
    @g_eqeltri (syn_cpartial) (syn_cin (syn_cin (syn_cref) (syn_ctrans)) (syn_cantisym))
      (syn_cvv) p0000 p0005
  exact p0006

@[expose]
noncomputable def g_strictex : Nominal.NPrf (.classMem (syn_cstrict) (syn_cvv)) :=
  by
  have p0000 := (Nominal.classEqRefl (syn_cstrict))
  have p0001 := @g_partialex
  have p0002 := @g_connexex
  have p0003 := @g_inex (syn_cpartial) (syn_cconnex) p0001 p0002
  have p0004 :=
    @g_eqeltri (syn_cstrict) (syn_cin (syn_cpartial) (syn_cconnex)) (syn_cvv) p0000 p0003
  exact p0004

@[expose]
noncomputable def g_weex : Nominal.NPrf (.classMem (syn_cwe) (syn_cvv)) :=
  by
  have p0000 := (Nominal.classEqRefl (syn_cwe))
  have p0001 := @g_strictex
  have p0002 := @g_foundex
  have p0003 := @g_inex (syn_cstrict) (syn_cfound) p0001 p0002
  have p0004 :=
    @g_eqeltri (syn_cwe) (syn_cin (syn_cstrict) (syn_cfound)) (syn_cvv) p0000 p0003
  exact p0004

@[expose]
noncomputable def g_trd (ph : Wff) (A : Class) (R : Class) (X : Class) (Y : Class)
    (Z : Class) (hyp_trd_1 : Nominal.NPrf (.imp ph (syn_wbr R (syn_ctrans) A)))
    (hyp_trd_2 : Nominal.NPrf (.imp ph (.classMem X A)))
    (hyp_trd_3 : Nominal.NPrf (.imp ph (.classMem Y A)))
    (hyp_trd_4 : Nominal.NPrf (.imp ph (.classMem Z A)))
    (hyp_trd_5 : Nominal.NPrf (.imp ph (syn_wbr X R Y)))
    (hyp_trd_6 : Nominal.NPrf (.imp ph (syn_wbr Y R Z))) :
    Nominal.NPrf (.imp ph (syn_wbr X R Z)) :=
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
      ((syn_wral x A (syn_wral y A (syn_wral z A
              (.imp (syn_wa (syn_wbr (.cv x) R (.cv y)) (syn_wbr (.cv y) R (.cv z)))
                (syn_wbr (.cv x) R (.cv z))))))).fv :=
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
      ((syn_wral x A (syn_wral y A (syn_wral z A
              (.imp (syn_wa (syn_wbr (.cv x) R (.cv y)) (syn_wbr (.cv y) R (.cv z)))
                (syn_wbr (.cv x) R (.cv z))))))).fv :=
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
      ((Wff.imp (syn_wa (syn_wbr X R (.cv y)) (syn_wbr (.cv y) R (.cv z)))
          (syn_wbr X R (.cv z)))).fv :=
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
    z ∉ ((Wff.imp (syn_wa (syn_wbr X R Y) (syn_wbr Y R Z)) (syn_wbr X R Z))).fv :=
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
      ((Wff.imp (syn_wa (syn_wbr X R Y) (syn_wbr Y R (.cv z))) (syn_wbr X R (.cv z)))).fv :=
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
  have p0000 := @g_brex R A (syn_ctrans)
  have p0001 := @g_breq (.cv x) (.cv y) (.cv r) R
  have p0002 := @g_breq (.cv y) (.cv z) (.cv r) R
  have p0003 :=
    @g_anbi12d (.classEq (.cv r) R) (syn_wbr (.cv x) (.cv r) (.cv y))
      (syn_wbr (.cv x) R (.cv y)) (syn_wbr (.cv y) (.cv r) (.cv z))
      (syn_wbr (.cv y) R (.cv z)) p0001 p0002
  have p0004 := @g_breq (.cv x) (.cv z) (.cv r) R
  have p0005 :=
    @g_imbi12d (.classEq (.cv r) R)
      (syn_wa (syn_wbr (.cv x) (.cv r) (.cv y)) (syn_wbr (.cv y) (.cv r) (.cv z)))
      (syn_wa (syn_wbr (.cv x) R (.cv y)) (syn_wbr (.cv y) R (.cv z)))
      (syn_wbr (.cv x) (.cv r) (.cv z)) (syn_wbr (.cv x) R (.cv z)) p0003 p0004
  have p0006 :=
    @g_ralbidv (.classEq (.cv r) R)
      (.imp (syn_wa (syn_wbr (.cv x) (.cv r) (.cv y)) (syn_wbr (.cv y) (.cv r) (.cv z)))
        (syn_wbr (.cv x) (.cv r) (.cv z)))
      (.imp (syn_wa (syn_wbr (.cv x) R (.cv y)) (syn_wbr (.cv y) R (.cv z)))
        (syn_wbr (.cv x) R (.cv z)))
      z (.cv a) dv_cache_0001 p0005
  have p0007 :=
    @g_n_2ralbidv (.classEq (.cv r) R)
      (syn_wral z (.cv a)
        (.imp (syn_wa (syn_wbr (.cv x) (.cv r) (.cv y)) (syn_wbr (.cv y) (.cv r) (.cv z)))
          (syn_wbr (.cv x) (.cv r) (.cv z))))
      (syn_wral z (.cv a) (.imp (syn_wa (syn_wbr (.cv x) R (.cv y)) (syn_wbr (.cv y) R (.cv z)))
          (syn_wbr (.cv x) R (.cv z))))
      x y (.cv a) (.cv a) dv_cache_0002 dv_cache_0003 p0006
  have p0008 :=
    @g_raleq
      (.imp (syn_wa (syn_wbr (.cv x) R (.cv y)) (syn_wbr (.cv y) R (.cv z)))
        (syn_wbr (.cv x) R (.cv z)))
      z (.cv a) A dv_cache_0004 dv_cache_0005
  have p0009 :=
    @g_raleqbi1dv
      (syn_wral z (.cv a) (.imp (syn_wa (syn_wbr (.cv x) R (.cv y)) (syn_wbr (.cv y) R (.cv z)))
          (syn_wbr (.cv x) R (.cv z))))
      (syn_wral z A (.imp (syn_wa (syn_wbr (.cv x) R (.cv y)) (syn_wbr (.cv y) R (.cv z)))
          (syn_wbr (.cv x) R (.cv z))))
      y (.cv a) A dv_cache_0006 dv_cache_0007 p0008
  have p0010 :=
    @g_raleqbi1dv
      (syn_wral y (.cv a) (syn_wral z (.cv a)
          (.imp (syn_wa (syn_wbr (.cv x) R (.cv y)) (syn_wbr (.cv y) R (.cv z)))
            (syn_wbr (.cv x) R (.cv z)))))
      (syn_wral y A (syn_wral z A
          (.imp (syn_wa (syn_wbr (.cv x) R (.cv y)) (syn_wbr (.cv y) R (.cv z)))
            (syn_wbr (.cv x) R (.cv z)))))
      x (.cv a) A dv_cache_0008 dv_cache_0009 p0009
  have p0011 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominal_df_trans x y z r a
      dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015
      dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019
  have p0012 :=
    @g_brabg
      (syn_wral x (.cv a) (syn_wral y (.cv a) (syn_wral z (.cv a) (.imp
              (syn_wa (syn_wbr (.cv x) (.cv r) (.cv y)) (syn_wbr (.cv y) (.cv r) (.cv z)))
              (syn_wbr (.cv x) (.cv r) (.cv z))))))
      (syn_wral x (.cv a) (syn_wral y (.cv a) (syn_wral z (.cv a)
            (.imp (syn_wa (syn_wbr (.cv x) R (.cv y)) (syn_wbr (.cv y) R (.cv z)))
              (syn_wbr (.cv x) R (.cv z))))))
      (syn_wral x A (syn_wral y A (syn_wral z A
            (.imp (syn_wa (syn_wbr (.cv x) R (.cv y)) (syn_wbr (.cv y) R (.cv z)))
              (syn_wbr (.cv x) R (.cv z))))))
      r a R A (syn_cvv) (syn_cvv) (syn_ctrans) dv_cache_0020 dv_cache_0021 dv_cache_0022
      dv_cache_0023 dv_cache_0024 dv_cache_0025 dv_cache_0026 p0007 p0010 p0011
  have p0013 :=
    @g_syl (syn_wbr R (syn_ctrans) A)
      (syn_wa (.classMem R (syn_cvv)) (.classMem A (syn_cvv)))
      (syn_wb (syn_wbr R (syn_ctrans) A) (syn_wral x A (syn_wral y A (syn_wral z A
              (.imp (syn_wa (syn_wbr (.cv x) R (.cv y)) (syn_wbr (.cv y) R (.cv z)))
                (syn_wbr (.cv x) R (.cv z)))))))
      p0000 p0012
  have p0014 :=
    @g_ibi (syn_wbr R (syn_ctrans) A)
      (syn_wral x A (syn_wral y A (syn_wral z A
            (.imp (syn_wa (syn_wbr (.cv x) R (.cv y)) (syn_wbr (.cv y) R (.cv z)))
              (syn_wbr (.cv x) R (.cv z))))))
      p0013
  have p0015 :=
    @g_syl ph (syn_wbr R (syn_ctrans) A)
      (syn_wral x A (syn_wral y A (syn_wral z A
            (.imp (syn_wa (syn_wbr (.cv x) R (.cv y)) (syn_wbr (.cv y) R (.cv z)))
              (syn_wbr (.cv x) R (.cv z))))))
      hyp_trd_1 p0014
  have p0016 := @g_breq1 (.cv x) X (.cv y) R
  have p0017 :=
    @g_anbi1d (.classEq (.cv x) X) (syn_wbr (.cv x) R (.cv y)) (syn_wbr X R (.cv y))
      (syn_wbr (.cv y) R (.cv z)) p0016
  have p0018 := @g_breq1 (.cv x) X (.cv z) R
  have p0019 :=
    @g_imbi12d (.classEq (.cv x) X)
      (syn_wa (syn_wbr (.cv x) R (.cv y)) (syn_wbr (.cv y) R (.cv z)))
      (syn_wa (syn_wbr X R (.cv y)) (syn_wbr (.cv y) R (.cv z)))
      (syn_wbr (.cv x) R (.cv z)) (syn_wbr X R (.cv z)) p0017 p0018
  have p0020 := @g_breq2 (.cv y) Y X R
  have p0021 := @g_breq1 (.cv y) Y (.cv z) R
  have p0022 :=
    @g_anbi12d (.classEq (.cv y) Y) (syn_wbr X R (.cv y)) (syn_wbr X R Y)
      (syn_wbr (.cv y) R (.cv z)) (syn_wbr Y R (.cv z)) p0020 p0021
  have p0023 :=
    @g_imbi1d (.classEq (.cv y) Y)
      (syn_wa (syn_wbr X R (.cv y)) (syn_wbr (.cv y) R (.cv z)))
      (syn_wa (syn_wbr X R Y) (syn_wbr Y R (.cv z))) (syn_wbr X R (.cv z)) p0022
  have p0024 := @g_breq2 (.cv z) Z Y R
  have p0025 :=
    @g_anbi2d (.classEq (.cv z) Z) (syn_wbr Y R (.cv z)) (syn_wbr Y R Z) (syn_wbr X R Y)
      p0024
  have p0026 := @g_breq2 (.cv z) Z X R
  have p0027 :=
    @g_imbi12d (.classEq (.cv z) Z) (syn_wa (syn_wbr X R Y) (syn_wbr Y R (.cv z)))
      (syn_wa (syn_wbr X R Y) (syn_wbr Y R Z)) (syn_wbr X R (.cv z)) (syn_wbr X R Z) p0025
      p0026
  have p0028 :=
    @g_rspc3v
      (.imp (syn_wa (syn_wbr (.cv x) R (.cv y)) (syn_wbr (.cv y) R (.cv z)))
        (syn_wbr (.cv x) R (.cv z)))
      (.imp (syn_wa (syn_wbr X R Y) (syn_wbr Y R Z)) (syn_wbr X R Z))
      (.imp (syn_wa (syn_wbr X R (.cv y)) (syn_wbr (.cv y) R (.cv z))) (syn_wbr X R (.cv z)))
      (.imp (syn_wa (syn_wbr X R Y) (syn_wbr Y R (.cv z))) (syn_wbr X R (.cv z))) x y z X
      Y Z A A A dv_cache_0027 dv_cache_0028 dv_cache_0029 dv_cache_0030 dv_cache_0031
      dv_cache_0032 dv_cache_0009 dv_cache_0009 dv_cache_0007 dv_cache_0009 dv_cache_0007
      dv_cache_0005 dv_cache_0033 dv_cache_0034 dv_cache_0035 dv_cache_0017 dv_cache_0018
      dv_cache_0019 p0019 p0023 p0027
  have p0029 :=
    @g_syl3anc ph (.classMem X A) (.classMem Y A) (.classMem Z A)
      (.imp (syn_wral x A (syn_wral y A (syn_wral z A
              (.imp (syn_wa (syn_wbr (.cv x) R (.cv y)) (syn_wbr (.cv y) R (.cv z)))
                (syn_wbr (.cv x) R (.cv z))))))
        (.imp (syn_wa (syn_wbr X R Y) (syn_wbr Y R Z)) (syn_wbr X R Z)))
      hyp_trd_2 hyp_trd_3 hyp_trd_4 p0028
  have p0030 :=
    @g_mpd ph
      (syn_wral x A (syn_wral y A (syn_wral z A
            (.imp (syn_wa (syn_wbr (.cv x) R (.cv y)) (syn_wbr (.cv y) R (.cv z)))
              (syn_wbr (.cv x) R (.cv z))))))
      (.imp (syn_wa (syn_wbr X R Y) (syn_wbr Y R Z)) (syn_wbr X R Z)) p0015 p0029
  have p0031 :=
    @g_mp2and ph (syn_wbr X R Y) (syn_wbr Y R Z) (syn_wbr X R Z) hyp_trd_5 hyp_trd_6 p0030
  exact p0031


end NFChoice.DirectNominalPrf.WPPReplay

end
