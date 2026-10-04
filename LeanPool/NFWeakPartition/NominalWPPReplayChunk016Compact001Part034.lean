/-
Copyright (c) 2026 Elliot Glazer and NFNotWPP contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elliot Glazer and NFNotWPP contributors
-/

module

public import LeanPool.NFWeakPartition.NominalWPPReplayChunk016Compact001Part033

/-! NF weak partition development: NominalWPPReplayChunk016Compact001Part034. -/


public section


namespace NFChoice.DirectNominalPrf.WPPReplay

open scoped Fol
open NFChoice.Foundation
open NFChoice.SemanticCore
open NFChoice.ReplaySupport
open NFChoice.Compiler.CompactSourceSyntax

/-- Checked nominal proof certificate identified upstream as `g_wecutisobranchccknfdv`. -/
@[expose]
noncomputable def gWecutisobranchccknfdv (x : Var) (y : Var) (z : Var) (v : Var)
    (u : Var) (D : Class) (R : Class) (S : Class) (h : Var) (E : Class)
    (_dv_D_h : h ∉ D.fv) (_dv_D_u : u ∉ D.fv) (_dv_D_v : v ∉ D.fv) (_dv_D_x : x ∉ D.fv)
    (_dv_D_y : y ∉ D.fv) (_dv_D_z : z ∉ D.fv) (_dv_E_h : h ∉ E.fv) (_dv_E_u : u ∉ E.fv)
    (_dv_E_v : v ∉ E.fv) (_dv_E_x : x ∉ E.fv) (_dv_E_y : y ∉ E.fv) (_dv_E_z : z ∉ E.fv)
    (_dv_R_h : h ∉ R.fv) (_dv_R_u : u ∉ R.fv) (_dv_R_v : v ∉ R.fv) (_dv_R_x : x ∉ R.fv)
    (_dv_R_y : y ∉ R.fv) (_dv_R_z : z ∉ R.fv) (_dv_S_h : h ∉ S.fv) (_dv_S_u : u ∉ S.fv)
    (_dv_S_v : v ∉ S.fv) (_dv_S_x : x ∉ S.fv) (_dv_S_y : y ∉ S.fv) (_dv_S_z : z ∉ S.fv)
    (_dv_h_u : h ≠ u) (_dv_h_v : h ≠ v) (_dv_h_x : h ≠ x) (_dv_h_y : h ≠ y)
    (_dv_h_z : h ≠ z) (_dv_u_v : u ≠ v) (_dv_u_x : u ≠ x) (_dv_u_y : u ≠ y)
    (_dv_u_z : u ≠ z) (_dv_v_x : v ≠ x) (_dv_v_y : v ≠ y) (_dv_v_z : v ≠ z)
    (_dv_x_y : x ≠ y) (_dv_x_z : x ≠ z) (_dv_y_z : y ≠ z)
    (_hyp_wecutisobranchknterminalfdv_1 : Nominal.NPrf (synWbr R (synCwe) D))
    (_hyp_wecutisobranchknterminalfdv_2 : Nominal.NPrf (synWbr S (synCwe) E))
    (hyp_wecutisobranchknterminalfdv_3 :
      Nominal.NPrf (.classMem (synCuni (synCwecutiso R D S E)) (synCvv))) :
    Nominal.NPrf
      (.imp (.neg (.classMem (.cv y) (synCdm (synCuni (synCwecutiso R D S E))))) (.imp
          (synWiso (synCun (synCuni (synCwecutiso R D S E))
              (synCsn (synCop (.cv y) (.cv u)))) R S (synCun
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
              (synCsn (.cv y))) (synCun
              (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
              (synCsn (.cv u)))) (.imp (synWa (synWa (synWa (.classMem (.cv z) D) (.classEq
                    (synCun (synCin D
                        (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
                      (synCsn (.cv y))) (synCin D
                      (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z))))))
                (.classMem (.cv v) E)) (.classEq (synCun (synCin E
                    (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
                  (synCsn (.cv u))) (synCin E
                  (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))))
            (synW3o (synWex h (synWiso (.cv h) R S D E)) (synWrex x E (synWex h
                  (synWiso (.cv h) R (synCin S (synCxp (synCin E
                          (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv x))))
                        (synCin E (synCima (synCcnv (synCdif S (synCid)))
                            (synCsn (.cv x)))))) D (synCin E
                      (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv x)))))))
              (synWrex x D (synWex h (synWiso (.cv h) S (synCin R (synCxp (synCin D
                          (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
                        (synCin D (synCima (synCcnv (synCdif R (synCid)))
                            (synCsn (.cv x)))))) E (synCin D
                      (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))))))) :=
  by
  let proofSupport : Finset Var :=
    ({ x } : Finset Var) ∪ ({ y } : Finset Var) ∪ ({ z } : Finset Var) ∪
                  ({ v } : Finset Var) ∪
                ({ u } : Finset Var) ∪
              D.fv ∪
            R.fv ∪
          S.fv ∪
        ({ h } : Finset Var) ∪
      E.fv
  let a : Var := freshVar proofSupport 0
  let b : Var := freshVar proofSupport 1
  have fresh_a : a ∉ proofSupport :=
    by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_a_ne_y : a ≠ y := by
    intro h
    exact
      fresh_a
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _
              (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _
                    (Finset.mem_union_left _ (Finset.mem_union_left _
                        (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))))))))))
  have fresh_a_ne_z : a ≠ z := by
    intro h
    exact
      fresh_a
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _
              (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _
                    (Finset.mem_union_left _
                      (Finset.mem_union_right _ (Finset.mem_singleton.mpr h)))))))))
  have fresh_a_ne_u : a ≠ u := by
    intro h
    exact
      fresh_a
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _
              (Finset.mem_union_left _ (Finset.mem_union_left _
                  (Finset.mem_union_right _ (Finset.mem_singleton.mpr h)))))))
  have fresh_a_not_D : a ∉ D.fv := by
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
  have fresh_a_not_S : a ∉ S.fv := by
    intro h
    exact
      fresh_a
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))
  have fresh_a_not_E : a ∉ E.fv := by
    intro h
    exact fresh_a (Finset.mem_union_right _ (h))
  have fresh_b : b ∉ proofSupport :=
    by
    change freshVar proofSupport 1 ∉ proofSupport
    exact freshVar_not_mem proofSupport 1
  have fresh_b_ne_y : b ≠ y := by
    intro h
    exact
      fresh_b
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _
              (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _
                    (Finset.mem_union_left _ (Finset.mem_union_left _
                        (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))))))))))
  have fresh_b_ne_z : b ≠ z := by
    intro h
    exact
      fresh_b
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _
              (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _
                    (Finset.mem_union_left _
                      (Finset.mem_union_right _ (Finset.mem_singleton.mpr h)))))))))
  have fresh_b_ne_v : b ≠ v := by
    intro h
    exact
      fresh_b
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _
              (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _
                    (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))))))))
  have fresh_b_ne_u : b ≠ u := by
    intro h
    exact
      fresh_b
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _
              (Finset.mem_union_left _ (Finset.mem_union_left _
                  (Finset.mem_union_right _ (Finset.mem_singleton.mpr h)))))))
  have fresh_b_not_D : b ∉ D.fv := by
    intro h
    exact
      fresh_b
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _
              (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))))
  have fresh_b_not_R : b ∉ R.fv := by
    intro h
    exact
      fresh_b
        (Finset.mem_union_left _ (Finset.mem_union_left _
            (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))))
  have fresh_b_not_S : b ∉ S.fv := by
    intro h
    exact
      fresh_b
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))
  have fresh_b_not_E : b ∉ E.fv := by
    intro h
    exact fresh_b (Finset.mem_union_right _ (h))
  have fresh_a_ne_b : a ≠ b :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have fresh_b_ne_a : b ≠ a := Ne.symm fresh_a_ne_b
  have dv_cache_0001 : a ∉ ((Class.cv z)).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : a ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_a_ne_z, not_false_eq_true])
  have dv_cache_0002 : b ∉ ((Class.cv z)).fv :=
    by
    clear dv_cache_0001
    exact
      (by
        have compact_fv_not_mem_empty : b ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_b_ne_z, not_false_eq_true])
  have dv_cache_0003 : b ∉ ((Class.cv v)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact
      (by
        have compact_fv_not_mem_empty : b ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_b_ne_v, not_false_eq_true])
  have dv_cache_0004 : a ∉ (D).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact
      (by
        have compact_fv_not_mem_empty : a ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_a_not_D, not_false_eq_true])
  have dv_cache_0005 : a ∉ (E).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact
      (by
        have compact_fv_not_mem_empty : a ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_a_not_E, not_false_eq_true])
  have dv_cache_0006 : b ∉ (E).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact
      (by
        have compact_fv_not_mem_empty : b ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_b_not_E, not_false_eq_true])
  have dv_cache_0007 :
    a ∉
      ((synWiso
          (synCun (synCuni (synCwecutiso R D S E)) (synCsn (synCop (.cv y) (.cv u))))
          (synCin R (synCxp
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z))))
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z))))))
          (synCin S (synCxp
              (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv b))))
              (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv b))))))
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z)))) (synCin E
            (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv b)))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006
    exact
      (by
        have compact_fv_not_mem_empty : a ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_wiso,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cun,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cuni,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwecutiso,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cop,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxp,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cima,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdif,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cid, Finset.mem_union,
          Finset.mem_singleton, fresh_a_not_D, fresh_a_not_R, fresh_a_ne_z, fresh_a_not_E,
          fresh_a_not_S, fresh_a_ne_b, fresh_a_ne_y, fresh_a_ne_u,
          compact_fv_not_mem_empty, or_false, not_false_eq_true])
  have dv_cache_0008 :
    b ∉
      ((synWiso
          (synCun (synCuni (synCwecutiso R D S E)) (synCsn (synCop (.cv y) (.cv u))))
          (synCin R (synCxp
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z))))
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z))))))
          (synCin S (synCxp
              (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))
              (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))))
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z)))) (synCin E
            (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v)))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007
    exact
      (by
        have compact_fv_not_mem_empty : b ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_wiso,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cun,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cuni,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwecutiso,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cop,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxp,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cima,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdif,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cid, Finset.mem_union,
          Finset.mem_singleton, fresh_b_not_D, fresh_b_not_R, fresh_b_ne_z, fresh_b_not_E,
          fresh_b_not_S, fresh_b_ne_v, fresh_b_ne_y, fresh_b_ne_u,
          compact_fv_not_mem_empty, or_false, not_false_eq_true])
  have dv_cache_0009 : a ≠ b :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008
    exact (show a ≠ b from (by exact fresh_a_ne_b))
  have dv_cache_0010 : b ∉ (D).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009
    exact
      (by
        have compact_fv_not_mem_empty : b ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_b_not_D, not_false_eq_true])
  have dv_cache_0011 :
    b ∉
      ((synCun (synCuni (synCwecutiso R D S E)) (synCsn (synCop (.cv y) (.cv u))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010
    exact
      (by
        have compact_fv_not_mem_empty : b ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cun,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cuni,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwecutiso,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cop,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, fresh_b_not_D, fresh_b_not_E, fresh_b_not_R,
          fresh_b_not_S, fresh_b_ne_y, fresh_b_ne_u, or_false, not_false_eq_true])
  have dv_cache_0012 :
    a ∉
      ((synCun (synCuni (synCwecutiso R D S E)) (synCsn (synCop (.cv y) (.cv u))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
    exact
      (by
        have compact_fv_not_mem_empty : a ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cun,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cuni,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwecutiso,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cop,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, fresh_a_not_D, fresh_a_not_E, fresh_a_not_R,
          fresh_a_not_S, fresh_a_ne_y, fresh_a_ne_u, or_false, not_false_eq_true])
  have dv_cache_0013 : b ∉ (R).fv :=
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
        simp only [fresh_b_not_R, not_false_eq_true])
  have dv_cache_0014 : a ∉ (R).fv :=
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
        simp only [fresh_a_not_R, not_false_eq_true])
  have dv_cache_0015 : b ∉ (S).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014
    exact
      (by
        have compact_fv_not_mem_empty : b ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_b_not_S, not_false_eq_true])
  have dv_cache_0016 : a ∉ (S).fv :=
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
        simp only [fresh_a_not_S, not_false_eq_true])
  have dv_cache_0017 : b ≠ a :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016
    exact (show b ≠ a from (by exact fresh_b_ne_a))
  have p0000 := @gVex y
  have p0001 := @gVex u
  have p0002 := @gOpex (.cv y) (.cv u) p0000 p0001
  have p0003 := @gSnid (synCop (.cv y) (.cv u)) p0002
  have p0004 :=
    @gElun2 (synCop (.cv y) (.cv u)) (synCsn (synCop (.cv y) (.cv u)))
      (synCuni (synCwecutiso R D S E))
  have p0005 := Nominal.mp p0003 p0004
  have p0006 :=
    @gA1i
      (.classMem (synCop (.cv y) (.cv u))
        (synCun (synCuni (synCwecutiso R D S E)) (synCsn (synCop (.cv y) (.cv u)))))
      (synWa (synWa (synWa (.classMem (.cv z) D) (.classEq (synCun
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
                (synCsn (.cv y)))
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z))))))
          (.classMem (.cv v) E)) (.classEq (synCun
            (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
            (synCsn (.cv u)))
          (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))))
      p0005
  have p0007 :=
    @gA1i
      (.imp (synWa (synWa (synWa (.classMem (.cv z) D) (.classEq (synCun (synCin D
                    (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
                  (synCsn (.cv y))) (synCin D
                  (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z))))))
            (.classMem (.cv v) E)) (.classEq (synCun
              (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
              (synCsn (.cv u)))
            (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))))
        (.classMem (synCop (.cv y) (.cv u)) (synCun (synCuni (synCwecutiso R D S E))
            (synCsn (synCop (.cv y) (.cv u))))))
      (synWiso
        (synCun (synCuni (synCwecutiso R D S E)) (synCsn (synCop (.cv y) (.cv u)))) R S
        (synCun (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
          (synCsn (.cv y))) (synCun
          (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
          (synCsn (.cv u))))
      p0006
  have p0008 :=
    @gId
      (synWa (synWa (synWa (.classMem (.cv z) D) (.classEq (synCun
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
                (synCsn (.cv y)))
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z))))))
          (.classMem (.cv v) E)) (.classEq (synCun
            (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
            (synCsn (.cv u)))
          (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))))
  have p0009 :=
    @gA1i
      (.imp (synWa (synWa (synWa (.classMem (.cv z) D) (.classEq (synCun (synCin D
                    (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
                  (synCsn (.cv y))) (synCin D
                  (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z))))))
            (.classMem (.cv v) E)) (.classEq (synCun
              (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
              (synCsn (.cv u)))
            (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v)))))) (synWa
          (synWa (synWa (.classMem (.cv z) D) (.classEq (synCun (synCin D
                    (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
                  (synCsn (.cv y))) (synCin D
                  (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z))))))
            (.classMem (.cv v) E)) (.classEq (synCun
              (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
              (synCsn (.cv u)))
            (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v)))))))
      (synWiso
        (synCun (synCuni (synCwecutiso R D S E)) (synCsn (synCop (.cv y) (.cv u)))) R S
        (synCun (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
          (synCsn (.cv y))) (synCun
          (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
          (synCsn (.cv u))))
      p0008
  have p0010 :=
    @gSimpl
      (synWa (synWa (.classMem (.cv z) D) (.classEq (synCun
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
              (synCsn (.cv y)))
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z))))))
        (.classMem (.cv v) E))
      (.classEq (synCun
          (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
          (synCsn (.cv u)))
        (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v)))))
  have p0011 :=
    @gSimpl
      (synWa (.classMem (.cv z) D) (.classEq (synCun
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
            (synCsn (.cv y)))
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z))))))
      (.classMem (.cv v) E)
  have p0012 :=
    @gSyl
      (synWa (synWa (synWa (.classMem (.cv z) D) (.classEq (synCun
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
                (synCsn (.cv y)))
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z))))))
          (.classMem (.cv v) E)) (.classEq (synCun
            (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
            (synCsn (.cv u)))
          (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))))
      (synWa (synWa (.classMem (.cv z) D) (.classEq (synCun
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
              (synCsn (.cv y)))
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z))))))
        (.classMem (.cv v) E))
      (synWa (.classMem (.cv z) D) (.classEq (synCun
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
            (synCsn (.cv y)))
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z))))))
      p0010 p0011
  have p0013 :=
    @gSimpl (.classMem (.cv z) D)
      (.classEq (synCun
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
          (synCsn (.cv y)))
        (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z)))))
  have p0014 :=
    @gSyl
      (synWa (synWa (synWa (.classMem (.cv z) D) (.classEq (synCun
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
                (synCsn (.cv y)))
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z))))))
          (.classMem (.cv v) E)) (.classEq (synCun
            (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
            (synCsn (.cv u)))
          (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))))
      (synWa (.classMem (.cv z) D) (.classEq (synCun
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
            (synCsn (.cv y)))
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z))))))
      (.classMem (.cv z) D) p0012 p0013
  have p0016 :=
    @gSimpr
      (synWa (.classMem (.cv z) D) (.classEq (synCun
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
            (synCsn (.cv y)))
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z))))))
      (.classMem (.cv v) E)
  have p0017 :=
    @gSyl
      (synWa (synWa (synWa (.classMem (.cv z) D) (.classEq (synCun
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
                (synCsn (.cv y)))
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z))))))
          (.classMem (.cv v) E)) (.classEq (synCun
            (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
            (synCsn (.cv u)))
          (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))))
      (synWa (synWa (.classMem (.cv z) D) (.classEq (synCun
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
              (synCsn (.cv y)))
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z))))))
        (.classMem (.cv v) E))
      (.classMem (.cv v) E) p0010 p0016
  have p0018 :=
    @gJca
      (synWa (synWa (synWa (.classMem (.cv z) D) (.classEq (synCun
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
                (synCsn (.cv y)))
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z))))))
          (.classMem (.cv v) E)) (.classEq (synCun
            (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
            (synCsn (.cv u)))
          (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))))
      (.classMem (.cv z) D) (.classMem (.cv v) E) p0014 p0017
  have p0019 :=
    @gA1i
      (.imp (synWa (synWa (synWa (.classMem (.cv z) D) (.classEq (synCun (synCin D
                    (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
                  (synCsn (.cv y))) (synCin D
                  (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z))))))
            (.classMem (.cv v) E)) (.classEq (synCun
              (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
              (synCsn (.cv u)))
            (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))))
        (synWa (.classMem (.cv z) D) (.classMem (.cv v) E)))
      (synWiso
        (synCun (synCuni (synCwecutiso R D S E)) (synCsn (synCop (.cv y) (.cv u)))) R S
        (synCun (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
          (synCsn (.cv y))) (synCun
          (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
          (synCsn (.cv u))))
      p0018
  have p0020 := @gId (synWa (.classMem (.cv z) D) (.classMem (.cv v) E))
  have p0021 :=
    @gA1d (synWa (.classMem (.cv z) D) (.classMem (.cv v) E))
      (synWa (.classMem (.cv z) D) (.classMem (.cv v) E))
      (synWa (synWa (synWa (.classMem (.cv z) D) (.classEq (synCun
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
                (synCsn (.cv y)))
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z))))))
          (.classMem (.cv v) E)) (.classEq (synCun
            (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
            (synCsn (.cv u)))
          (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))))
      p0020
  have p0022 :=
    @gA1i
      (.imp (synWa (.classMem (.cv z) D) (.classMem (.cv v) E)) (.imp (synWa (synWa
              (synWa (.classMem (.cv z) D) (.classEq (synCun (synCin D
                      (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
                    (synCsn (.cv y))) (synCin D
                    (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z))))))
              (.classMem (.cv v) E)) (.classEq (synCun
                (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
                (synCsn (.cv u)))
              (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))))
          (synWa (.classMem (.cv z) D) (.classMem (.cv v) E))))
      (synWiso
        (synCun (synCuni (synCwecutiso R D S E)) (synCsn (synCop (.cv y) (.cv u)))) R S
        (synCun (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
          (synCsn (.cv y))) (synCun
          (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
          (synCsn (.cv u))))
      p0021
  have p0023 :=
    @gId
      (synWiso
        (synCun (synCuni (synCwecutiso R D S E)) (synCsn (synCop (.cv y) (.cv u)))) R S
        (synCun (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
          (synCsn (.cv y))) (synCun
          (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
          (synCsn (.cv u))))
  have p0024 :=
    Nominal.ax1
      (synWiso
        (synCun (synCuni (synCwecutiso R D S E)) (synCsn (synCop (.cv y) (.cv u)))) R S
        (synCun (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
          (synCsn (.cv y))) (synCun
          (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
          (synCsn (.cv u))))
      (synWa (synWa (synWa (.classMem (.cv z) D) (.classEq (synCun
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
                (synCsn (.cv y)))
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z))))))
          (.classMem (.cv v) E)) (.classEq (synCun
            (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
            (synCsn (.cv u)))
          (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))))
  have p0025 :=
    @gA1i
      (.imp (synWiso
          (synCun (synCuni (synCwecutiso R D S E)) (synCsn (synCop (.cv y) (.cv u)))) R S
          (synCun (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
            (synCsn (.cv y))) (synCun
            (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
            (synCsn (.cv u)))) (.imp (synWa (synWa (synWa (.classMem (.cv z) D) (.classEq
                  (synCun (synCin D
                      (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
                    (synCsn (.cv y))) (synCin D
                    (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z))))))
              (.classMem (.cv v) E)) (.classEq (synCun
                (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
                (synCsn (.cv u)))
              (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))))
          (synWiso (synCun (synCuni (synCwecutiso R D S E))
              (synCsn (synCop (.cv y) (.cv u)))) R S (synCun
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
              (synCsn (.cv y))) (synCun
              (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
              (synCsn (.cv u))))))
      (synWiso
        (synCun (synCuni (synCwecutiso R D S E)) (synCsn (synCop (.cv y) (.cv u)))) R S
        (synCun (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
          (synCsn (.cv y))) (synCun
          (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
          (synCsn (.cv u))))
      p0024
  have p0026 :=
    @gMpd
      (synWiso
        (synCun (synCuni (synCwecutiso R D S E)) (synCsn (synCop (.cv y) (.cv u)))) R S
        (synCun (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
          (synCsn (.cv y))) (synCun
          (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
          (synCsn (.cv u))))
      (synWiso
        (synCun (synCuni (synCwecutiso R D S E)) (synCsn (synCop (.cv y) (.cv u)))) R S
        (synCun (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
          (synCsn (.cv y))) (synCun
          (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
          (synCsn (.cv u))))
      (.imp (synWa (synWa (synWa (.classMem (.cv z) D) (.classEq (synCun (synCin D
                    (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
                  (synCsn (.cv y))) (synCin D
                  (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z))))))
            (.classMem (.cv v) E)) (.classEq (synCun
              (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
              (synCsn (.cv u)))
            (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))))
        (synWiso
          (synCun (synCuni (synCwecutiso R D S E)) (synCsn (synCop (.cv y) (.cv u)))) R S
          (synCun (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
            (synCsn (.cv y))) (synCun
            (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
            (synCsn (.cv u)))))
      p0023 p0025
  have p0030 :=
    @gSimpr (.classMem (.cv z) D)
      (.classEq (synCun
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
          (synCsn (.cv y)))
        (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z)))))
  have p0031 :=
    @gSyl
      (synWa (synWa (synWa (.classMem (.cv z) D) (.classEq (synCun
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
                (synCsn (.cv y)))
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z))))))
          (.classMem (.cv v) E)) (.classEq (synCun
            (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
            (synCsn (.cv u)))
          (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))))
      (synWa (.classMem (.cv z) D) (.classEq (synCun
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
            (synCsn (.cv y)))
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z))))))
      (.classEq (synCun
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
          (synCsn (.cv y)))
        (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z)))))
      p0012 p0030
  have p0032 :=
    @gIsoeq4
      (synCun (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
        (synCsn (.cv y)))
      (synCun (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
        (synCsn (.cv u)))
      (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z)))) R S
      (synCun (synCuni (synCwecutiso R D S E)) (synCsn (synCop (.cv y) (.cv u))))
  have p0033 :=
    @gSyl
      (synWa (synWa (synWa (.classMem (.cv z) D) (.classEq (synCun
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
                (synCsn (.cv y)))
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z))))))
          (.classMem (.cv v) E)) (.classEq (synCun
            (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
            (synCsn (.cv u)))
          (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))))
      (.classEq (synCun
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
          (synCsn (.cv y)))
        (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z)))))
      (synWb (synWiso
          (synCun (synCuni (synCwecutiso R D S E)) (synCsn (synCop (.cv y) (.cv u)))) R S
          (synCun (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
            (synCsn (.cv y))) (synCun
            (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
            (synCsn (.cv u)))) (synWiso
          (synCun (synCuni (synCwecutiso R D S E)) (synCsn (synCop (.cv y) (.cv u))))
          R S (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z))))
          (synCun (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
            (synCsn (.cv u)))))
      p0031 p0032
  have p0034 :=
    @gBiimpd
      (synWa (synWa (synWa (.classMem (.cv z) D) (.classEq (synCun
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
                (synCsn (.cv y)))
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z))))))
          (.classMem (.cv v) E)) (.classEq (synCun
            (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
            (synCsn (.cv u)))
          (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))))
      (synWiso
        (synCun (synCuni (synCwecutiso R D S E)) (synCsn (synCop (.cv y) (.cv u)))) R S
        (synCun (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
          (synCsn (.cv y))) (synCun
          (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
          (synCsn (.cv u))))
      (synWiso
        (synCun (synCuni (synCwecutiso R D S E)) (synCsn (synCop (.cv y) (.cv u)))) R
        S (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z)))) (synCun
          (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
          (synCsn (.cv u))))
      p0033
  have p0035 :=
    @gA2i
      (synWa (synWa (synWa (.classMem (.cv z) D) (.classEq (synCun
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
                (synCsn (.cv y)))
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z))))))
          (.classMem (.cv v) E)) (.classEq (synCun
            (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
            (synCsn (.cv u)))
          (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))))
      (synWiso
        (synCun (synCuni (synCwecutiso R D S E)) (synCsn (synCop (.cv y) (.cv u)))) R S
        (synCun (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
          (synCsn (.cv y))) (synCun
          (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
          (synCsn (.cv u))))
      (synWiso
        (synCun (synCuni (synCwecutiso R D S E)) (synCsn (synCop (.cv y) (.cv u)))) R
        S (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z)))) (synCun
          (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
          (synCsn (.cv u))))
      p0034
  have p0036 :=
    @gA1i
      (.imp (.imp (synWa (synWa (synWa (.classMem (.cv z) D) (.classEq (synCun (synCin D
                      (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
                    (synCsn (.cv y))) (synCin D
                    (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z))))))
              (.classMem (.cv v) E)) (.classEq (synCun
                (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
                (synCsn (.cv u)))
              (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))))
          (synWiso (synCun (synCuni (synCwecutiso R D S E))
              (synCsn (synCop (.cv y) (.cv u)))) R S (synCun
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
              (synCsn (.cv y))) (synCun
              (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
              (synCsn (.cv u))))) (.imp (synWa (synWa (synWa (.classMem (.cv z) D) (.classEq
                  (synCun (synCin D
                      (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
                    (synCsn (.cv y))) (synCin D
                    (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z))))))
              (.classMem (.cv v) E)) (.classEq (synCun
                (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
                (synCsn (.cv u)))
              (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))))
          (synWiso (synCun (synCuni (synCwecutiso R D S E))
              (synCsn (synCop (.cv y) (.cv u))))
            R S (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z))))
            (synCun (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
              (synCsn (.cv u))))))
      (synWiso
        (synCun (synCuni (synCwecutiso R D S E)) (synCsn (synCop (.cv y) (.cv u)))) R S
        (synCun (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
          (synCsn (.cv y))) (synCun
          (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
          (synCsn (.cv u))))
      p0035
  have p0037 :=
    @gMpd
      (synWiso
        (synCun (synCuni (synCwecutiso R D S E)) (synCsn (synCop (.cv y) (.cv u)))) R S
        (synCun (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
          (synCsn (.cv y))) (synCun
          (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
          (synCsn (.cv u))))
      (.imp (synWa (synWa (synWa (.classMem (.cv z) D) (.classEq (synCun (synCin D
                    (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
                  (synCsn (.cv y))) (synCin D
                  (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z))))))
            (.classMem (.cv v) E)) (.classEq (synCun
              (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
              (synCsn (.cv u)))
            (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))))
        (synWiso
          (synCun (synCuni (synCwecutiso R D S E)) (synCsn (synCop (.cv y) (.cv u)))) R S
          (synCun (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
            (synCsn (.cv y))) (synCun
            (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
            (synCsn (.cv u)))))
      (.imp (synWa (synWa (synWa (.classMem (.cv z) D) (.classEq (synCun (synCin D
                    (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
                  (synCsn (.cv y))) (synCin D
                  (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z))))))
            (.classMem (.cv v) E)) (.classEq (synCun
              (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
              (synCsn (.cv u)))
            (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))))
        (synWiso
          (synCun (synCuni (synCwecutiso R D S E)) (synCsn (synCop (.cv y) (.cv u))))
          R S (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z))))
          (synCun (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
            (synCsn (.cv u)))))
      p0026 p0036
  have p0038 :=
    @gSimpr
      (synWa (synWa (.classMem (.cv z) D) (.classEq (synCun
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
              (synCsn (.cv y)))
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z))))))
        (.classMem (.cv v) E))
      (.classEq (synCun
          (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
          (synCsn (.cv u)))
        (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v)))))
  have p0039 :=
    @gIsoeq5 (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z))))
      (synCun (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
        (synCsn (.cv u)))
      (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v)))) R S
      (synCun (synCuni (synCwecutiso R D S E)) (synCsn (synCop (.cv y) (.cv u))))
  have p0040 :=
    @gSyl
      (synWa (synWa (synWa (.classMem (.cv z) D) (.classEq (synCun
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
                (synCsn (.cv y)))
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z))))))
          (.classMem (.cv v) E)) (.classEq (synCun
            (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
            (synCsn (.cv u)))
          (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))))
      (.classEq (synCun
          (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
          (synCsn (.cv u)))
        (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v)))))
      (synWb (synWiso
          (synCun (synCuni (synCwecutiso R D S E)) (synCsn (synCop (.cv y) (.cv u))))
          R S (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z))))
          (synCun (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
            (synCsn (.cv u)))) (synWiso
          (synCun (synCuni (synCwecutiso R D S E)) (synCsn (synCop (.cv y) (.cv u))))
          R S (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z))))
          (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))))
      p0038 p0039
  have p0041 :=
    @gBiimpd
      (synWa (synWa (synWa (.classMem (.cv z) D) (.classEq (synCun
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
                (synCsn (.cv y)))
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z))))))
          (.classMem (.cv v) E)) (.classEq (synCun
            (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
            (synCsn (.cv u)))
          (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))))
      (synWiso
        (synCun (synCuni (synCwecutiso R D S E)) (synCsn (synCop (.cv y) (.cv u)))) R
        S (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z)))) (synCun
          (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
          (synCsn (.cv u))))
      (synWiso
        (synCun (synCuni (synCwecutiso R D S E)) (synCsn (synCop (.cv y) (.cv u)))) R
        S (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z))))
        (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v)))))
      p0040
  have p0042 :=
    @gA2i
      (synWa (synWa (synWa (.classMem (.cv z) D) (.classEq (synCun
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
                (synCsn (.cv y)))
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z))))))
          (.classMem (.cv v) E)) (.classEq (synCun
            (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
            (synCsn (.cv u)))
          (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))))
      (synWiso
        (synCun (synCuni (synCwecutiso R D S E)) (synCsn (synCop (.cv y) (.cv u)))) R
        S (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z)))) (synCun
          (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
          (synCsn (.cv u))))
      (synWiso
        (synCun (synCuni (synCwecutiso R D S E)) (synCsn (synCop (.cv y) (.cv u)))) R
        S (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z))))
        (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v)))))
      p0041
  have p0043 :=
    @gA1i
      (.imp (.imp (synWa (synWa (synWa (.classMem (.cv z) D) (.classEq (synCun (synCin D
                      (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
                    (synCsn (.cv y))) (synCin D
                    (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z))))))
              (.classMem (.cv v) E)) (.classEq (synCun
                (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
                (synCsn (.cv u)))
              (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))))
          (synWiso (synCun (synCuni (synCwecutiso R D S E))
              (synCsn (synCop (.cv y) (.cv u))))
            R S (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z))))
            (synCun (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
              (synCsn (.cv u))))) (.imp (synWa (synWa (synWa (.classMem (.cv z) D) (.classEq
                  (synCun (synCin D
                      (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
                    (synCsn (.cv y))) (synCin D
                    (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z))))))
              (.classMem (.cv v) E)) (.classEq (synCun
                (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
                (synCsn (.cv u)))
              (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))))
          (synWiso (synCun (synCuni (synCwecutiso R D S E))
              (synCsn (synCop (.cv y) (.cv u))))
            R S (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z))))
            (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v)))))))
      (synWiso
        (synCun (synCuni (synCwecutiso R D S E)) (synCsn (synCop (.cv y) (.cv u)))) R S
        (synCun (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
          (synCsn (.cv y))) (synCun
          (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
          (synCsn (.cv u))))
      p0042
  have p0044 :=
    @gMpd
      (synWiso
        (synCun (synCuni (synCwecutiso R D S E)) (synCsn (synCop (.cv y) (.cv u)))) R S
        (synCun (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
          (synCsn (.cv y))) (synCun
          (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
          (synCsn (.cv u))))
      (.imp (synWa (synWa (synWa (.classMem (.cv z) D) (.classEq (synCun (synCin D
                    (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
                  (synCsn (.cv y))) (synCin D
                  (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z))))))
            (.classMem (.cv v) E)) (.classEq (synCun
              (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
              (synCsn (.cv u)))
            (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))))
        (synWiso
          (synCun (synCuni (synCwecutiso R D S E)) (synCsn (synCop (.cv y) (.cv u))))
          R S (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z))))
          (synCun (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
            (synCsn (.cv u)))))
      (.imp (synWa (synWa (synWa (.classMem (.cv z) D) (.classEq (synCun (synCin D
                    (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
                  (synCsn (.cv y))) (synCin D
                  (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z))))))
            (.classMem (.cv v) E)) (.classEq (synCun
              (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
              (synCsn (.cv u)))
            (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))))
        (synWiso
          (synCun (synCuni (synCwecutiso R D S E)) (synCsn (synCop (.cv y) (.cv u))))
          R S (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z))))
          (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))))
      p0037 p0043
  have p0045 :=
    @gIsores1 (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z))))
      (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v)))) R S
      (synCun (synCuni (synCwecutiso R D S E)) (synCsn (synCop (.cv y) (.cv u))))
  have p0046 :=
    @gBiimpi
      (synWiso
        (synCun (synCuni (synCwecutiso R D S E)) (synCsn (synCop (.cv y) (.cv u)))) R
        S (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z))))
        (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v)))))
      (synWiso (synCun (synCuni (synCwecutiso R D S E)) (synCsn (synCop (.cv y) (.cv u))))
        (synCin R (synCxp
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z))))
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z))))))
        S (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z))))
        (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v)))))
      p0045
  have p0047 :=
    @gA1i
      (.imp (synWiso
          (synCun (synCuni (synCwecutiso R D S E)) (synCsn (synCop (.cv y) (.cv u))))
          R S (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z))))
          (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))) (synWiso
          (synCun (synCuni (synCwecutiso R D S E)) (synCsn (synCop (.cv y) (.cv u))))
          (synCin R (synCxp
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z))))
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z))))))
          S (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z))))
          (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))))
      (synWa (synWa (synWa (.classMem (.cv z) D) (.classEq (synCun
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
                (synCsn (.cv y)))
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z))))))
          (.classMem (.cv v) E)) (.classEq (synCun
            (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
            (synCsn (.cv u)))
          (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))))
      p0046
  have p0048 :=
    @gA2i
      (synWa (synWa (synWa (.classMem (.cv z) D) (.classEq (synCun
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
                (synCsn (.cv y)))
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z))))))
          (.classMem (.cv v) E)) (.classEq (synCun
            (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
            (synCsn (.cv u)))
          (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))))
      (synWiso
        (synCun (synCuni (synCwecutiso R D S E)) (synCsn (synCop (.cv y) (.cv u)))) R
        S (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z))))
        (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v)))))
      (synWiso (synCun (synCuni (synCwecutiso R D S E)) (synCsn (synCop (.cv y) (.cv u))))
        (synCin R (synCxp
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z))))
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z))))))
        S (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z))))
        (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v)))))
      p0047
  have p0049 :=
    @gA1i
      (.imp (.imp (synWa (synWa (synWa (.classMem (.cv z) D) (.classEq (synCun (synCin D
                      (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
                    (synCsn (.cv y))) (synCin D
                    (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z))))))
              (.classMem (.cv v) E)) (.classEq (synCun
                (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
                (synCsn (.cv u)))
              (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))))
          (synWiso (synCun (synCuni (synCwecutiso R D S E))
              (synCsn (synCop (.cv y) (.cv u))))
            R S (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z))))
            (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v)))))) (.imp
          (synWa (synWa (synWa (.classMem (.cv z) D) (.classEq (synCun (synCin D
                      (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
                    (synCsn (.cv y))) (synCin D
                    (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z))))))
              (.classMem (.cv v) E)) (.classEq (synCun
                (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
                (synCsn (.cv u)))
              (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))))
          (synWiso (synCun (synCuni (synCwecutiso R D S E))
              (synCsn (synCop (.cv y) (.cv u)))) (synCin R (synCxp
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z))))
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z))))))
            S (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z))))
            (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v)))))))
      (synWiso
        (synCun (synCuni (synCwecutiso R D S E)) (synCsn (synCop (.cv y) (.cv u)))) R S
        (synCun (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
          (synCsn (.cv y))) (synCun
          (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
          (synCsn (.cv u))))
      p0048
  have p0050 :=
    @gMpd
      (synWiso
        (synCun (synCuni (synCwecutiso R D S E)) (synCsn (synCop (.cv y) (.cv u)))) R S
        (synCun (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
          (synCsn (.cv y))) (synCun
          (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
          (synCsn (.cv u))))
      (.imp (synWa (synWa (synWa (.classMem (.cv z) D) (.classEq (synCun (synCin D
                    (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
                  (synCsn (.cv y))) (synCin D
                  (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z))))))
            (.classMem (.cv v) E)) (.classEq (synCun
              (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
              (synCsn (.cv u)))
            (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))))
        (synWiso
          (synCun (synCuni (synCwecutiso R D S E)) (synCsn (synCop (.cv y) (.cv u))))
          R S (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z))))
          (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))))
      (.imp (synWa (synWa (synWa (.classMem (.cv z) D) (.classEq (synCun (synCin D
                    (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
                  (synCsn (.cv y))) (synCin D
                  (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z))))))
            (.classMem (.cv v) E)) (.classEq (synCun
              (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
              (synCsn (.cv u)))
            (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))))
        (synWiso
          (synCun (synCuni (synCwecutiso R D S E)) (synCsn (synCop (.cv y) (.cv u))))
          (synCin R (synCxp
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z))))
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z))))))
          S (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z))))
          (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))))
      p0044 p0049
  have p0051 :=
    @gIsores2 (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z))))
      (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))
      (synCin R (synCxp
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z))))
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z))))))
      S (synCun (synCuni (synCwecutiso R D S E)) (synCsn (synCop (.cv y) (.cv u))))
  have p0052 :=
    @gBiimpi
      (synWiso (synCun (synCuni (synCwecutiso R D S E)) (synCsn (synCop (.cv y) (.cv u))))
        (synCin R (synCxp
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z))))
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z))))))
        S (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z))))
        (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v)))))
      (synWiso (synCun (synCuni (synCwecutiso R D S E)) (synCsn (synCop (.cv y) (.cv u))))
        (synCin R (synCxp
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z))))
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z))))))
        (synCin S (synCxp
            (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))
            (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))))
        (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z))))
        (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v)))))
      p0051
  have p0053 :=
    @gA1i
      (.imp (synWiso
          (synCun (synCuni (synCwecutiso R D S E)) (synCsn (synCop (.cv y) (.cv u))))
          (synCin R (synCxp
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z))))
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z))))))
          S (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z))))
          (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))) (synWiso
          (synCun (synCuni (synCwecutiso R D S E)) (synCsn (synCop (.cv y) (.cv u))))
          (synCin R (synCxp
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z))))
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z))))))
          (synCin S (synCxp
              (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))
              (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))))
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z))))
          (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))))
      (synWa (synWa (synWa (.classMem (.cv z) D) (.classEq (synCun
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
                (synCsn (.cv y)))
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z))))))
          (.classMem (.cv v) E)) (.classEq (synCun
            (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
            (synCsn (.cv u)))
          (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))))
      p0052
  have p0054 :=
    @gA2i
      (synWa (synWa (synWa (.classMem (.cv z) D) (.classEq (synCun
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
                (synCsn (.cv y)))
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z))))))
          (.classMem (.cv v) E)) (.classEq (synCun
            (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
            (synCsn (.cv u)))
          (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))))
      (synWiso (synCun (synCuni (synCwecutiso R D S E)) (synCsn (synCop (.cv y) (.cv u))))
        (synCin R (synCxp
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z))))
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z))))))
        S (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z))))
        (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v)))))
      (synWiso (synCun (synCuni (synCwecutiso R D S E)) (synCsn (synCop (.cv y) (.cv u))))
        (synCin R (synCxp
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z))))
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z))))))
        (synCin S (synCxp
            (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))
            (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))))
        (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z))))
        (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v)))))
      p0053
  have p0055 :=
    @gA1i
      (.imp (.imp (synWa (synWa (synWa (.classMem (.cv z) D) (.classEq (synCun (synCin D
                      (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
                    (synCsn (.cv y))) (synCin D
                    (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z))))))
              (.classMem (.cv v) E)) (.classEq (synCun
                (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
                (synCsn (.cv u)))
              (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))))
          (synWiso (synCun (synCuni (synCwecutiso R D S E))
              (synCsn (synCop (.cv y) (.cv u)))) (synCin R (synCxp
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z))))
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z))))))
            S (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z))))
            (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v)))))) (.imp
          (synWa (synWa (synWa (.classMem (.cv z) D) (.classEq (synCun (synCin D
                      (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
                    (synCsn (.cv y))) (synCin D
                    (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z))))))
              (.classMem (.cv v) E)) (.classEq (synCun
                (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
                (synCsn (.cv u)))
              (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))))
          (synWiso (synCun (synCuni (synCwecutiso R D S E))
              (synCsn (synCop (.cv y) (.cv u)))) (synCin R (synCxp
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z))))
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z))))))
            (synCin S (synCxp
                (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))
                (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))))
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z))))
            (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v)))))))
      (synWiso
        (synCun (synCuni (synCwecutiso R D S E)) (synCsn (synCop (.cv y) (.cv u)))) R S
        (synCun (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
          (synCsn (.cv y))) (synCun
          (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
          (synCsn (.cv u))))
      p0054
  have p0056 :=
    @gMpd
      (synWiso
        (synCun (synCuni (synCwecutiso R D S E)) (synCsn (synCop (.cv y) (.cv u)))) R S
        (synCun (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
          (synCsn (.cv y))) (synCun
          (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
          (synCsn (.cv u))))
      (.imp (synWa (synWa (synWa (.classMem (.cv z) D) (.classEq (synCun (synCin D
                    (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
                  (synCsn (.cv y))) (synCin D
                  (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z))))))
            (.classMem (.cv v) E)) (.classEq (synCun
              (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
              (synCsn (.cv u)))
            (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))))
        (synWiso
          (synCun (synCuni (synCwecutiso R D S E)) (synCsn (synCop (.cv y) (.cv u))))
          (synCin R (synCxp
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z))))
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z))))))
          S (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z))))
          (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))))
      (.imp (synWa (synWa (synWa (.classMem (.cv z) D) (.classEq (synCun (synCin D
                    (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
                  (synCsn (.cv y))) (synCin D
                  (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z))))))
            (.classMem (.cv v) E)) (.classEq (synCun
              (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
              (synCsn (.cv u)))
            (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))))
        (synWiso
          (synCun (synCuni (synCwecutiso R D S E)) (synCsn (synCop (.cv y) (.cv u))))
          (synCin R (synCxp
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z))))
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z))))))
          (synCin S (synCxp
              (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))
              (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))))
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z))))
          (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))))
      p0050 p0055
  have p0057 :=
    Nominal.ax1
      (synWiso (synCun (synCuni (synCwecutiso R D S E)) (synCsn (synCop (.cv y) (.cv u))))
        (synCin R (synCxp
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z))))
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z))))))
        (synCin S (synCxp
            (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))
            (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))))
        (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z))))
        (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v)))))
      (synWa (.classMem (.cv z) D) (.classMem (.cv v) E))
  have p0058 :=
    @gA1i
      (.imp (synWiso
          (synCun (synCuni (synCwecutiso R D S E)) (synCsn (synCop (.cv y) (.cv u))))
          (synCin R (synCxp
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z))))
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z))))))
          (synCin S (synCxp
              (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))
              (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))))
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z))))
          (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v)))))
        (.imp (synWa (.classMem (.cv z) D) (.classMem (.cv v) E)) (synWiso
            (synCun (synCuni (synCwecutiso R D S E)) (synCsn (synCop (.cv y) (.cv u))))
            (synCin R (synCxp
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z))))
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z))))))
            (synCin S (synCxp
                (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))
                (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))))
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z))))
            (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v)))))))
      (synWa (synWa (synWa (.classMem (.cv z) D) (.classEq (synCun
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
                (synCsn (.cv y)))
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z))))))
          (.classMem (.cv v) E)) (.classEq (synCun
            (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
            (synCsn (.cv u)))
          (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))))
      p0057
  have p0059 :=
    @gA2i
      (synWa (synWa (synWa (.classMem (.cv z) D) (.classEq (synCun
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
                (synCsn (.cv y)))
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z))))))
          (.classMem (.cv v) E)) (.classEq (synCun
            (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
            (synCsn (.cv u)))
          (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))))
      (synWiso (synCun (synCuni (synCwecutiso R D S E)) (synCsn (synCop (.cv y) (.cv u))))
        (synCin R (synCxp
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z))))
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z))))))
        (synCin S (synCxp
            (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))
            (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))))
        (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z))))
        (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v)))))
      (.imp (synWa (.classMem (.cv z) D) (.classMem (.cv v) E)) (synWiso
          (synCun (synCuni (synCwecutiso R D S E)) (synCsn (synCop (.cv y) (.cv u))))
          (synCin R (synCxp
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z))))
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z))))))
          (synCin S (synCxp
              (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))
              (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))))
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z))))
          (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))))
      p0058
  have p0060 :=
    @gA1i
      (.imp (.imp (synWa (synWa (synWa (.classMem (.cv z) D) (.classEq (synCun (synCin D
                      (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
                    (synCsn (.cv y))) (synCin D
                    (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z))))))
              (.classMem (.cv v) E)) (.classEq (synCun
                (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
                (synCsn (.cv u)))
              (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))))
          (synWiso (synCun (synCuni (synCwecutiso R D S E))
              (synCsn (synCop (.cv y) (.cv u)))) (synCin R (synCxp
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z))))
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z))))))
            (synCin S (synCxp
                (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))
                (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))))
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z))))
            (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v)))))) (.imp
          (synWa (synWa (synWa (.classMem (.cv z) D) (.classEq (synCun (synCin D
                      (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
                    (synCsn (.cv y))) (synCin D
                    (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z))))))
              (.classMem (.cv v) E)) (.classEq (synCun
                (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
                (synCsn (.cv u)))
              (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))))
          (.imp (synWa (.classMem (.cv z) D) (.classMem (.cv v) E)) (synWiso
              (synCun (synCuni (synCwecutiso R D S E)) (synCsn (synCop (.cv y) (.cv u))))
              (synCin R (synCxp (synCin D
                    (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z)))) (synCin D
                    (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z)))))) (synCin S
                (synCxp (synCin E
                    (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v)))) (synCin E
                    (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))))
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z))))
              (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))))))
      (synWiso
        (synCun (synCuni (synCwecutiso R D S E)) (synCsn (synCop (.cv y) (.cv u)))) R S
        (synCun (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
          (synCsn (.cv y))) (synCun
          (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
          (synCsn (.cv u))))
      p0059
  have p0061 :=
    @gMpd
      (synWiso
        (synCun (synCuni (synCwecutiso R D S E)) (synCsn (synCop (.cv y) (.cv u)))) R S
        (synCun (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
          (synCsn (.cv y))) (synCun
          (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
          (synCsn (.cv u))))
      (.imp (synWa (synWa (synWa (.classMem (.cv z) D) (.classEq (synCun (synCin D
                    (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
                  (synCsn (.cv y))) (synCin D
                  (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z))))))
            (.classMem (.cv v) E)) (.classEq (synCun
              (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
              (synCsn (.cv u)))
            (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))))
        (synWiso
          (synCun (synCuni (synCwecutiso R D S E)) (synCsn (synCop (.cv y) (.cv u))))
          (synCin R (synCxp
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z))))
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z))))))
          (synCin S (synCxp
              (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))
              (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))))
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z))))
          (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))))
      (.imp (synWa (synWa (synWa (.classMem (.cv z) D) (.classEq (synCun (synCin D
                    (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
                  (synCsn (.cv y))) (synCin D
                  (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z))))))
            (.classMem (.cv v) E)) (.classEq (synCun
              (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
              (synCsn (.cv u)))
            (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))))
        (.imp (synWa (.classMem (.cv z) D) (.classMem (.cv v) E)) (synWiso
            (synCun (synCuni (synCwecutiso R D S E)) (synCsn (synCop (.cv y) (.cv u))))
            (synCin R (synCxp
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z))))
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z))))))
            (synCin S (synCxp
                (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))
                (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))))
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z))))
            (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v)))))))
      p0056 p0060
  have p0062 :=
    @g_pm3_2 (synWa (.classMem (.cv z) D) (.classMem (.cv v) E))
      (synWiso (synCun (synCuni (synCwecutiso R D S E)) (synCsn (synCop (.cv y) (.cv u))))
        (synCin R (synCxp
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z))))
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z))))))
        (synCin S (synCxp
            (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))
            (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))))
        (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z))))
        (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v)))))
  have p0063 :=
    @gA2i (synWa (.classMem (.cv z) D) (.classMem (.cv v) E))
      (synWiso (synCun (synCuni (synCwecutiso R D S E)) (synCsn (synCop (.cv y) (.cv u))))
        (synCin R (synCxp
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z))))
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z))))))
        (synCin S (synCxp
            (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))
            (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))))
        (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z))))
        (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v)))))
      (synWa (synWa (.classMem (.cv z) D) (.classMem (.cv v) E)) (synWiso
          (synCun (synCuni (synCwecutiso R D S E)) (synCsn (synCop (.cv y) (.cv u))))
          (synCin R (synCxp
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z))))
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z))))))
          (synCin S (synCxp
              (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))
              (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))))
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z))))
          (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))))
      p0062
  have p0064 :=
    @gA1i
      (.imp (.imp (synWa (.classMem (.cv z) D) (.classMem (.cv v) E)) (synWiso
            (synCun (synCuni (synCwecutiso R D S E)) (synCsn (synCop (.cv y) (.cv u))))
            (synCin R (synCxp
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z))))
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z))))))
            (synCin S (synCxp
                (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))
                (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))))
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z))))
            (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))))
        (.imp (synWa (.classMem (.cv z) D) (.classMem (.cv v) E))
          (synWa (synWa (.classMem (.cv z) D) (.classMem (.cv v) E)) (synWiso
              (synCun (synCuni (synCwecutiso R D S E)) (synCsn (synCop (.cv y) (.cv u))))
              (synCin R (synCxp (synCin D
                    (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z)))) (synCin D
                    (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z)))))) (synCin S
                (synCxp (synCin E
                    (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v)))) (synCin E
                    (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))))
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z))))
              (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))))))
      (synWa (synWa (synWa (.classMem (.cv z) D) (.classEq (synCun
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
                (synCsn (.cv y)))
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z))))))
          (.classMem (.cv v) E)) (.classEq (synCun
            (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
            (synCsn (.cv u)))
          (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))))
      p0063
  have p0065 :=
    @gA2i
      (synWa (synWa (synWa (.classMem (.cv z) D) (.classEq (synCun
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
                (synCsn (.cv y)))
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z))))))
          (.classMem (.cv v) E)) (.classEq (synCun
            (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
            (synCsn (.cv u)))
          (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))))
      (.imp (synWa (.classMem (.cv z) D) (.classMem (.cv v) E)) (synWiso
          (synCun (synCuni (synCwecutiso R D S E)) (synCsn (synCop (.cv y) (.cv u))))
          (synCin R (synCxp
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z))))
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z))))))
          (synCin S (synCxp
              (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))
              (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))))
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z))))
          (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))))
      (.imp (synWa (.classMem (.cv z) D) (.classMem (.cv v) E))
        (synWa (synWa (.classMem (.cv z) D) (.classMem (.cv v) E)) (synWiso
            (synCun (synCuni (synCwecutiso R D S E)) (synCsn (synCop (.cv y) (.cv u))))
            (synCin R (synCxp
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z))))
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z))))))
            (synCin S (synCxp
                (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))
                (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))))
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z))))
            (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v)))))))
      p0064
  have p0066 :=
    @gA1i
      (.imp (.imp (synWa (synWa (synWa (.classMem (.cv z) D) (.classEq (synCun (synCin D
                      (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
                    (synCsn (.cv y))) (synCin D
                    (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z))))))
              (.classMem (.cv v) E)) (.classEq (synCun
                (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
                (synCsn (.cv u)))
              (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))))
          (.imp (synWa (.classMem (.cv z) D) (.classMem (.cv v) E)) (synWiso
              (synCun (synCuni (synCwecutiso R D S E)) (synCsn (synCop (.cv y) (.cv u))))
              (synCin R (synCxp (synCin D
                    (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z)))) (synCin D
                    (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z)))))) (synCin S
                (synCxp (synCin E
                    (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v)))) (synCin E
                    (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))))
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z))))
              (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v)))))))
        (.imp (synWa (synWa (synWa (.classMem (.cv z) D) (.classEq (synCun (synCin D
                      (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
                    (synCsn (.cv y))) (synCin D
                    (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z))))))
              (.classMem (.cv v) E)) (.classEq (synCun
                (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
                (synCsn (.cv u)))
              (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))))
          (.imp (synWa (.classMem (.cv z) D) (.classMem (.cv v) E))
            (synWa (synWa (.classMem (.cv z) D) (.classMem (.cv v) E)) (synWiso
                (synCun (synCuni (synCwecutiso R D S E)) (synCsn (synCop (.cv y) (.cv u))))
                (synCin R (synCxp (synCin D
                      (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z)))) (synCin D
                      (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z))))))
                (synCin S (synCxp (synCin E
                      (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v)))) (synCin E
                      (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))))
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z))))
                (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v)))))))))
      (synWiso
        (synCun (synCuni (synCwecutiso R D S E)) (synCsn (synCop (.cv y) (.cv u)))) R S
        (synCun (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
          (synCsn (.cv y))) (synCun
          (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
          (synCsn (.cv u))))
      p0065
  have p0067 :=
    @gMpd
      (synWiso
        (synCun (synCuni (synCwecutiso R D S E)) (synCsn (synCop (.cv y) (.cv u)))) R S
        (synCun (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
          (synCsn (.cv y))) (synCun
          (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
          (synCsn (.cv u))))
      (.imp (synWa (synWa (synWa (.classMem (.cv z) D) (.classEq (synCun (synCin D
                    (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
                  (synCsn (.cv y))) (synCin D
                  (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z))))))
            (.classMem (.cv v) E)) (.classEq (synCun
              (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
              (synCsn (.cv u)))
            (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))))
        (.imp (synWa (.classMem (.cv z) D) (.classMem (.cv v) E)) (synWiso
            (synCun (synCuni (synCwecutiso R D S E)) (synCsn (synCop (.cv y) (.cv u))))
            (synCin R (synCxp
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z))))
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z))))))
            (synCin S (synCxp
                (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))
                (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))))
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z))))
            (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v)))))))
      (.imp (synWa (synWa (synWa (.classMem (.cv z) D) (.classEq (synCun (synCin D
                    (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
                  (synCsn (.cv y))) (synCin D
                  (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z))))))
            (.classMem (.cv v) E)) (.classEq (synCun
              (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
              (synCsn (.cv u)))
            (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))))
        (.imp (synWa (.classMem (.cv z) D) (.classMem (.cv v) E))
          (synWa (synWa (.classMem (.cv z) D) (.classMem (.cv v) E)) (synWiso
              (synCun (synCuni (synCwecutiso R D S E)) (synCsn (synCop (.cv y) (.cv u))))
              (synCin R (synCxp (synCin D
                    (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z)))) (synCin D
                    (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z)))))) (synCin S
                (synCxp (synCin E
                    (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v)))) (synCin E
                    (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))))
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z))))
              (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))))))
      p0061 p0066
  have p0068 :=
    Nominal.ax2
      (synWa (synWa (synWa (.classMem (.cv z) D) (.classEq (synCun
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
                (synCsn (.cv y)))
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z))))))
          (.classMem (.cv v) E)) (.classEq (synCun
            (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
            (synCsn (.cv u)))
          (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))))
      (synWa (.classMem (.cv z) D) (.classMem (.cv v) E))
      (synWa (synWa (.classMem (.cv z) D) (.classMem (.cv v) E)) (synWiso
          (synCun (synCuni (synCwecutiso R D S E)) (synCsn (synCop (.cv y) (.cv u))))
          (synCin R (synCxp
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z))))
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z))))))
          (synCin S (synCxp
              (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))
              (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))))
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z))))
          (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))))
  have p0069 :=
    @gA1i
      (.imp (.imp (synWa (synWa (synWa (.classMem (.cv z) D) (.classEq (synCun (synCin D
                      (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
                    (synCsn (.cv y))) (synCin D
                    (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z))))))
              (.classMem (.cv v) E)) (.classEq (synCun
                (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
                (synCsn (.cv u)))
              (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))))
          (.imp (synWa (.classMem (.cv z) D) (.classMem (.cv v) E))
            (synWa (synWa (.classMem (.cv z) D) (.classMem (.cv v) E)) (synWiso
                (synCun (synCuni (synCwecutiso R D S E)) (synCsn (synCop (.cv y) (.cv u))))
                (synCin R (synCxp (synCin D
                      (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z)))) (synCin D
                      (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z))))))
                (synCin S (synCxp (synCin E
                      (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v)))) (synCin E
                      (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))))
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z))))
                (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))))))
        (.imp (.imp (synWa (synWa (synWa (.classMem (.cv z) D) (.classEq (synCun (synCin D
                        (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
                      (synCsn (.cv y))) (synCin D
                      (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z))))))
                (.classMem (.cv v) E)) (.classEq (synCun (synCin E
                    (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
                  (synCsn (.cv u))) (synCin E
                  (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))))
            (synWa (.classMem (.cv z) D) (.classMem (.cv v) E))) (.imp (synWa (synWa
                (synWa (.classMem (.cv z) D) (.classEq (synCun (synCin D
                        (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
                      (synCsn (.cv y))) (synCin D
                      (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z))))))
                (.classMem (.cv v) E)) (.classEq (synCun (synCin E
                    (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
                  (synCsn (.cv u))) (synCin E
                  (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))))
            (synWa (synWa (.classMem (.cv z) D) (.classMem (.cv v) E)) (synWiso
                (synCun (synCuni (synCwecutiso R D S E)) (synCsn (synCop (.cv y) (.cv u))))
                (synCin R (synCxp (synCin D
                      (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z)))) (synCin D
                      (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z))))))
                (synCin S (synCxp (synCin E
                      (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v)))) (synCin E
                      (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))))
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z))))
                (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v)))))))))
      (synWiso
        (synCun (synCuni (synCwecutiso R D S E)) (synCsn (synCop (.cv y) (.cv u)))) R S
        (synCun (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
          (synCsn (.cv y))) (synCun
          (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
          (synCsn (.cv u))))
      p0068
  have p0070 :=
    @gMpd
      (synWiso
        (synCun (synCuni (synCwecutiso R D S E)) (synCsn (synCop (.cv y) (.cv u)))) R S
        (synCun (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
          (synCsn (.cv y))) (synCun
          (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
          (synCsn (.cv u))))
      (.imp (synWa (synWa (synWa (.classMem (.cv z) D) (.classEq (synCun (synCin D
                    (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
                  (synCsn (.cv y))) (synCin D
                  (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z))))))
            (.classMem (.cv v) E)) (.classEq (synCun
              (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
              (synCsn (.cv u)))
            (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))))
        (.imp (synWa (.classMem (.cv z) D) (.classMem (.cv v) E))
          (synWa (synWa (.classMem (.cv z) D) (.classMem (.cv v) E)) (synWiso
              (synCun (synCuni (synCwecutiso R D S E)) (synCsn (synCop (.cv y) (.cv u))))
              (synCin R (synCxp (synCin D
                    (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z)))) (synCin D
                    (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z)))))) (synCin S
                (synCxp (synCin E
                    (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v)))) (synCin E
                    (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))))
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z))))
              (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))))))
      (.imp (.imp (synWa (synWa (synWa (.classMem (.cv z) D) (.classEq (synCun (synCin D
                      (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
                    (synCsn (.cv y))) (synCin D
                    (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z))))))
              (.classMem (.cv v) E)) (.classEq (synCun
                (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
                (synCsn (.cv u)))
              (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))))
          (synWa (.classMem (.cv z) D) (.classMem (.cv v) E))) (.imp (synWa (synWa
              (synWa (.classMem (.cv z) D) (.classEq (synCun (synCin D
                      (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
                    (synCsn (.cv y))) (synCin D
                    (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z))))))
              (.classMem (.cv v) E)) (.classEq (synCun
                (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
                (synCsn (.cv u)))
              (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))))
          (synWa (synWa (.classMem (.cv z) D) (.classMem (.cv v) E)) (synWiso
              (synCun (synCuni (synCwecutiso R D S E)) (synCsn (synCop (.cv y) (.cv u))))
              (synCin R (synCxp (synCin D
                    (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z)))) (synCin D
                    (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z)))))) (synCin S
                (synCxp (synCin E
                    (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v)))) (synCin E
                    (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))))
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z))))
              (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))))))
      p0067 p0069
  have p0071 :=
    Nominal.ax1
      (.imp (.imp (synWa (synWa (synWa (.classMem (.cv z) D) (.classEq (synCun (synCin D
                      (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
                    (synCsn (.cv y))) (synCin D
                    (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z))))))
              (.classMem (.cv v) E)) (.classEq (synCun
                (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
                (synCsn (.cv u)))
              (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))))
          (synWa (.classMem (.cv z) D) (.classMem (.cv v) E))) (.imp (synWa (synWa
              (synWa (.classMem (.cv z) D) (.classEq (synCun (synCin D
                      (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
                    (synCsn (.cv y))) (synCin D
                    (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z))))))
              (.classMem (.cv v) E)) (.classEq (synCun
                (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
                (synCsn (.cv u)))
              (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))))
          (synWa (synWa (.classMem (.cv z) D) (.classMem (.cv v) E)) (synWiso
              (synCun (synCuni (synCwecutiso R D S E)) (synCsn (synCop (.cv y) (.cv u))))
              (synCin R (synCxp (synCin D
                    (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z)))) (synCin D
                    (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z)))))) (synCin S
                (synCxp (synCin E
                    (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v)))) (synCin E
                    (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))))
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z))))
              (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))))))
      (synWa (.classMem (.cv z) D) (.classMem (.cv v) E))
  have p0072 :=
    @gA1i
      (.imp (.imp (.imp (synWa (synWa (synWa (.classMem (.cv z) D) (.classEq (synCun
                      (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
                      (synCsn (.cv y))) (synCin D
                      (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z))))))
                (.classMem (.cv v) E)) (.classEq (synCun (synCin E
                    (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
                  (synCsn (.cv u))) (synCin E
                  (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))))
            (synWa (.classMem (.cv z) D) (.classMem (.cv v) E))) (.imp (synWa (synWa
                (synWa (.classMem (.cv z) D) (.classEq (synCun (synCin D
                        (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
                      (synCsn (.cv y))) (synCin D
                      (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z))))))
                (.classMem (.cv v) E)) (.classEq (synCun (synCin E
                    (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
                  (synCsn (.cv u))) (synCin E
                  (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))))
            (synWa (synWa (.classMem (.cv z) D) (.classMem (.cv v) E)) (synWiso
                (synCun (synCuni (synCwecutiso R D S E)) (synCsn (synCop (.cv y) (.cv u))))
                (synCin R (synCxp (synCin D
                      (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z)))) (synCin D
                      (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z))))))
                (synCin S (synCxp (synCin E
                      (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v)))) (synCin E
                      (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))))
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z))))
                (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))))))
        (.imp (synWa (.classMem (.cv z) D) (.classMem (.cv v) E)) (.imp (.imp (synWa (synWa
                  (synWa (.classMem (.cv z) D) (.classEq (synCun (synCin D
                          (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
                        (synCsn (.cv y))) (synCin D
                        (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z))))))
                  (.classMem (.cv v) E)) (.classEq (synCun (synCin E
                      (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
                    (synCsn (.cv u))) (synCin E
                    (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))))
              (synWa (.classMem (.cv z) D) (.classMem (.cv v) E))) (.imp (synWa (synWa
                  (synWa (.classMem (.cv z) D) (.classEq (synCun (synCin D
                          (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
                        (synCsn (.cv y))) (synCin D
                        (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z))))))
                  (.classMem (.cv v) E)) (.classEq (synCun (synCin E
                      (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
                    (synCsn (.cv u))) (synCin E
                    (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))))
              (synWa (synWa (.classMem (.cv z) D) (.classMem (.cv v) E)) (synWiso
                  (synCun (synCuni (synCwecutiso R D S E))
                    (synCsn (synCop (.cv y) (.cv u)))) (synCin R (synCxp (synCin D
                        (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z))))
                      (synCin D
                        (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z))))))
                  (synCin S (synCxp (synCin E
                        (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))
                      (synCin E
                        (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))))
                  (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z))))
                  (synCin E
                    (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))))))))
      (synWiso
        (synCun (synCuni (synCwecutiso R D S E)) (synCsn (synCop (.cv y) (.cv u)))) R S
        (synCun (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
          (synCsn (.cv y))) (synCun
          (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
          (synCsn (.cv u))))
      p0071
  have p0073 :=
    @gMpd
      (synWiso
        (synCun (synCuni (synCwecutiso R D S E)) (synCsn (synCop (.cv y) (.cv u)))) R S
        (synCun (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
          (synCsn (.cv y))) (synCun
          (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
          (synCsn (.cv u))))
      (.imp (.imp (synWa (synWa (synWa (.classMem (.cv z) D) (.classEq (synCun (synCin D
                      (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
                    (synCsn (.cv y))) (synCin D
                    (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z))))))
              (.classMem (.cv v) E)) (.classEq (synCun
                (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
                (synCsn (.cv u)))
              (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))))
          (synWa (.classMem (.cv z) D) (.classMem (.cv v) E))) (.imp (synWa (synWa
              (synWa (.classMem (.cv z) D) (.classEq (synCun (synCin D
                      (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
                    (synCsn (.cv y))) (synCin D
                    (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z))))))
              (.classMem (.cv v) E)) (.classEq (synCun
                (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
                (synCsn (.cv u)))
              (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))))
          (synWa (synWa (.classMem (.cv z) D) (.classMem (.cv v) E)) (synWiso
              (synCun (synCuni (synCwecutiso R D S E)) (synCsn (synCop (.cv y) (.cv u))))
              (synCin R (synCxp (synCin D
                    (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z)))) (synCin D
                    (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z)))))) (synCin S
                (synCxp (synCin E
                    (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v)))) (synCin E
                    (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))))
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z))))
              (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))))))
      (.imp (synWa (.classMem (.cv z) D) (.classMem (.cv v) E)) (.imp (.imp (synWa (synWa
                (synWa (.classMem (.cv z) D) (.classEq (synCun (synCin D
                        (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
                      (synCsn (.cv y))) (synCin D
                      (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z))))))
                (.classMem (.cv v) E)) (.classEq (synCun (synCin E
                    (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
                  (synCsn (.cv u))) (synCin E
                  (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))))
            (synWa (.classMem (.cv z) D) (.classMem (.cv v) E))) (.imp (synWa (synWa
                (synWa (.classMem (.cv z) D) (.classEq (synCun (synCin D
                        (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
                      (synCsn (.cv y))) (synCin D
                      (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z))))))
                (.classMem (.cv v) E)) (.classEq (synCun (synCin E
                    (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
                  (synCsn (.cv u))) (synCin E
                  (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))))
            (synWa (synWa (.classMem (.cv z) D) (.classMem (.cv v) E)) (synWiso
                (synCun (synCuni (synCwecutiso R D S E)) (synCsn (synCop (.cv y) (.cv u))))
                (synCin R (synCxp (synCin D
                      (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z)))) (synCin D
                      (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z))))))
                (synCin S (synCxp (synCin E
                      (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v)))) (synCin E
                      (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))))
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z))))
                (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v)))))))))
      p0070 p0072
  have p0074 :=
    Nominal.ax2 (synWa (.classMem (.cv z) D) (.classMem (.cv v) E))
      (.imp (synWa (synWa (synWa (.classMem (.cv z) D) (.classEq (synCun (synCin D
                    (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
                  (synCsn (.cv y))) (synCin D
                  (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z))))))
            (.classMem (.cv v) E)) (.classEq (synCun
              (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
              (synCsn (.cv u)))
            (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))))
        (synWa (.classMem (.cv z) D) (.classMem (.cv v) E)))
      (.imp (synWa (synWa (synWa (.classMem (.cv z) D) (.classEq (synCun (synCin D
                    (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
                  (synCsn (.cv y))) (synCin D
                  (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z))))))
            (.classMem (.cv v) E)) (.classEq (synCun
              (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
              (synCsn (.cv u)))
            (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))))
        (synWa (synWa (.classMem (.cv z) D) (.classMem (.cv v) E)) (synWiso
            (synCun (synCuni (synCwecutiso R D S E)) (synCsn (synCop (.cv y) (.cv u))))
            (synCin R (synCxp
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z))))
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z))))))
            (synCin S (synCxp
                (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))
                (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))))
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z))))
            (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v)))))))
  have p0075 :=
    @gA1i
      (.imp (.imp (synWa (.classMem (.cv z) D) (.classMem (.cv v) E)) (.imp (.imp (synWa
                (synWa (synWa (.classMem (.cv z) D) (.classEq (synCun (synCin D
                          (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
                        (synCsn (.cv y))) (synCin D
                        (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z))))))
                  (.classMem (.cv v) E)) (.classEq (synCun (synCin E
                      (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
                    (synCsn (.cv u))) (synCin E
                    (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))))
              (synWa (.classMem (.cv z) D) (.classMem (.cv v) E))) (.imp (synWa (synWa
                  (synWa (.classMem (.cv z) D) (.classEq (synCun (synCin D
                          (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
                        (synCsn (.cv y))) (synCin D
                        (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z))))))
                  (.classMem (.cv v) E)) (.classEq (synCun (synCin E
                      (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
                    (synCsn (.cv u))) (synCin E
                    (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))))
              (synWa (synWa (.classMem (.cv z) D) (.classMem (.cv v) E)) (synWiso
                  (synCun (synCuni (synCwecutiso R D S E))
                    (synCsn (synCop (.cv y) (.cv u)))) (synCin R (synCxp (synCin D
                        (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z))))
                      (synCin D
                        (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z))))))
                  (synCin S (synCxp (synCin E
                        (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))
                      (synCin E
                        (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))))
                  (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z))))
                  (synCin E
                    (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))))))) (.imp
          (.imp (synWa (.classMem (.cv z) D) (.classMem (.cv v) E)) (.imp (synWa (synWa
                  (synWa (.classMem (.cv z) D) (.classEq (synCun (synCin D
                          (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
                        (synCsn (.cv y))) (synCin D
                        (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z))))))
                  (.classMem (.cv v) E)) (.classEq (synCun (synCin E
                      (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
                    (synCsn (.cv u))) (synCin E
                    (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))))
              (synWa (.classMem (.cv z) D) (.classMem (.cv v) E))))
          (.imp (synWa (.classMem (.cv z) D) (.classMem (.cv v) E)) (.imp (synWa (synWa
                  (synWa (.classMem (.cv z) D) (.classEq (synCun (synCin D
                          (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
                        (synCsn (.cv y))) (synCin D
                        (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z))))))
                  (.classMem (.cv v) E)) (.classEq (synCun (synCin E
                      (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
                    (synCsn (.cv u))) (synCin E
                    (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))))
              (synWa (synWa (.classMem (.cv z) D) (.classMem (.cv v) E)) (synWiso
                  (synCun (synCuni (synCwecutiso R D S E))
                    (synCsn (synCop (.cv y) (.cv u)))) (synCin R (synCxp (synCin D
                        (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z))))
                      (synCin D
                        (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z))))))
                  (synCin S (synCxp (synCin E
                        (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))
                      (synCin E
                        (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))))
                  (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z))))
                  (synCin E
                    (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))))))))
      (synWiso
        (synCun (synCuni (synCwecutiso R D S E)) (synCsn (synCop (.cv y) (.cv u)))) R S
        (synCun (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
          (synCsn (.cv y))) (synCun
          (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
          (synCsn (.cv u))))
      p0074
  have p0076 :=
    @gMpd
      (synWiso
        (synCun (synCuni (synCwecutiso R D S E)) (synCsn (synCop (.cv y) (.cv u)))) R S
        (synCun (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
          (synCsn (.cv y))) (synCun
          (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
          (synCsn (.cv u))))
      (.imp (synWa (.classMem (.cv z) D) (.classMem (.cv v) E)) (.imp (.imp (synWa (synWa
                (synWa (.classMem (.cv z) D) (.classEq (synCun (synCin D
                        (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
                      (synCsn (.cv y))) (synCin D
                      (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z))))))
                (.classMem (.cv v) E)) (.classEq (synCun (synCin E
                    (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
                  (synCsn (.cv u))) (synCin E
                  (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))))
            (synWa (.classMem (.cv z) D) (.classMem (.cv v) E))) (.imp (synWa (synWa
                (synWa (.classMem (.cv z) D) (.classEq (synCun (synCin D
                        (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
                      (synCsn (.cv y))) (synCin D
                      (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z))))))
                (.classMem (.cv v) E)) (.classEq (synCun (synCin E
                    (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
                  (synCsn (.cv u))) (synCin E
                  (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))))
            (synWa (synWa (.classMem (.cv z) D) (.classMem (.cv v) E)) (synWiso
                (synCun (synCuni (synCwecutiso R D S E)) (synCsn (synCop (.cv y) (.cv u))))
                (synCin R (synCxp (synCin D
                      (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z)))) (synCin D
                      (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z))))))
                (synCin S (synCxp (synCin E
                      (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v)))) (synCin E
                      (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))))
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z))))
                (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v)))))))))
      (.imp (.imp (synWa (.classMem (.cv z) D) (.classMem (.cv v) E)) (.imp (synWa (synWa
                (synWa (.classMem (.cv z) D) (.classEq (synCun (synCin D
                        (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
                      (synCsn (.cv y))) (synCin D
                      (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z))))))
                (.classMem (.cv v) E)) (.classEq (synCun (synCin E
                    (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
                  (synCsn (.cv u))) (synCin E
                  (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))))
            (synWa (.classMem (.cv z) D) (.classMem (.cv v) E))))
        (.imp (synWa (.classMem (.cv z) D) (.classMem (.cv v) E)) (.imp (synWa (synWa
                (synWa (.classMem (.cv z) D) (.classEq (synCun (synCin D
                        (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
                      (synCsn (.cv y))) (synCin D
                      (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z))))))
                (.classMem (.cv v) E)) (.classEq (synCun (synCin E
                    (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
                  (synCsn (.cv u))) (synCin E
                  (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))))
            (synWa (synWa (.classMem (.cv z) D) (.classMem (.cv v) E)) (synWiso
                (synCun (synCuni (synCwecutiso R D S E)) (synCsn (synCop (.cv y) (.cv u))))
                (synCin R (synCxp (synCin D
                      (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z)))) (synCin D
                      (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z))))))
                (synCin S (synCxp (synCin E
                      (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v)))) (synCin E
                      (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))))
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z))))
                (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v)))))))))
      p0073 p0075
  have p0077 :=
    @gMpd
      (synWiso
        (synCun (synCuni (synCwecutiso R D S E)) (synCsn (synCop (.cv y) (.cv u)))) R S
        (synCun (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
          (synCsn (.cv y))) (synCun
          (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
          (synCsn (.cv u))))
      (.imp (synWa (.classMem (.cv z) D) (.classMem (.cv v) E)) (.imp (synWa (synWa
              (synWa (.classMem (.cv z) D) (.classEq (synCun (synCin D
                      (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
                    (synCsn (.cv y))) (synCin D
                    (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z))))))
              (.classMem (.cv v) E)) (.classEq (synCun
                (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
                (synCsn (.cv u)))
              (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))))
          (synWa (.classMem (.cv z) D) (.classMem (.cv v) E))))
      (.imp (synWa (.classMem (.cv z) D) (.classMem (.cv v) E)) (.imp (synWa (synWa
              (synWa (.classMem (.cv z) D) (.classEq (synCun (synCin D
                      (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
                    (synCsn (.cv y))) (synCin D
                    (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z))))))
              (.classMem (.cv v) E)) (.classEq (synCun
                (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
                (synCsn (.cv u)))
              (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))))
          (synWa (synWa (.classMem (.cv z) D) (.classMem (.cv v) E)) (synWiso
              (synCun (synCuni (synCwecutiso R D S E)) (synCsn (synCop (.cv y) (.cv u))))
              (synCin R (synCxp (synCin D
                    (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z)))) (synCin D
                    (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z)))))) (synCin S
                (synCxp (synCin E
                    (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v)))) (synCin E
                    (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))))
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z))))
              (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))))))
      p0022 p0076
  have p0078 :=
    Nominal.ax1
      (.imp (synWa (.classMem (.cv z) D) (.classMem (.cv v) E)) (.imp (synWa (synWa
              (synWa (.classMem (.cv z) D) (.classEq (synCun (synCin D
                      (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
                    (synCsn (.cv y))) (synCin D
                    (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z))))))
              (.classMem (.cv v) E)) (.classEq (synCun
                (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
                (synCsn (.cv u)))
              (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))))
          (synWa (synWa (.classMem (.cv z) D) (.classMem (.cv v) E)) (synWiso
              (synCun (synCuni (synCwecutiso R D S E)) (synCsn (synCop (.cv y) (.cv u))))
              (synCin R (synCxp (synCin D
                    (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z)))) (synCin D
                    (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z)))))) (synCin S
                (synCxp (synCin E
                    (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v)))) (synCin E
                    (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))))
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z))))
              (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))))))
      (synWa (synWa (synWa (.classMem (.cv z) D) (.classEq (synCun
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
                (synCsn (.cv y)))
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z))))))
          (.classMem (.cv v) E)) (.classEq (synCun
            (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
            (synCsn (.cv u)))
          (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))))
  have p0079 :=
    @gA1i
      (.imp (.imp (synWa (.classMem (.cv z) D) (.classMem (.cv v) E)) (.imp (synWa (synWa
                (synWa (.classMem (.cv z) D) (.classEq (synCun (synCin D
                        (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
                      (synCsn (.cv y))) (synCin D
                      (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z))))))
                (.classMem (.cv v) E)) (.classEq (synCun (synCin E
                    (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
                  (synCsn (.cv u))) (synCin E
                  (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))))
            (synWa (synWa (.classMem (.cv z) D) (.classMem (.cv v) E)) (synWiso
                (synCun (synCuni (synCwecutiso R D S E)) (synCsn (synCop (.cv y) (.cv u))))
                (synCin R (synCxp (synCin D
                      (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z)))) (synCin D
                      (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z))))))
                (synCin S (synCxp (synCin E
                      (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v)))) (synCin E
                      (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))))
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z))))
                (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))))))
        (.imp (synWa (synWa (synWa (.classMem (.cv z) D) (.classEq (synCun (synCin D
                      (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
                    (synCsn (.cv y))) (synCin D
                    (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z))))))
              (.classMem (.cv v) E)) (.classEq (synCun
                (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
                (synCsn (.cv u)))
              (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))))
          (.imp (synWa (.classMem (.cv z) D) (.classMem (.cv v) E)) (.imp (synWa (synWa
                  (synWa (.classMem (.cv z) D) (.classEq (synCun (synCin D
                          (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
                        (synCsn (.cv y))) (synCin D
                        (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z))))))
                  (.classMem (.cv v) E)) (.classEq (synCun (synCin E
                      (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
                    (synCsn (.cv u))) (synCin E
                    (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))))
              (synWa (synWa (.classMem (.cv z) D) (.classMem (.cv v) E)) (synWiso
                  (synCun (synCuni (synCwecutiso R D S E))
                    (synCsn (synCop (.cv y) (.cv u)))) (synCin R (synCxp (synCin D
                        (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z))))
                      (synCin D
                        (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z))))))
                  (synCin S (synCxp (synCin E
                        (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))
                      (synCin E
                        (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))))
                  (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z))))
                  (synCin E
                    (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))))))))
      (synWiso
        (synCun (synCuni (synCwecutiso R D S E)) (synCsn (synCop (.cv y) (.cv u)))) R S
        (synCun (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
          (synCsn (.cv y))) (synCun
          (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
          (synCsn (.cv u))))
      p0078
  have p0080 :=
    @gMpd
      (synWiso
        (synCun (synCuni (synCwecutiso R D S E)) (synCsn (synCop (.cv y) (.cv u)))) R S
        (synCun (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
          (synCsn (.cv y))) (synCun
          (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
          (synCsn (.cv u))))
      (.imp (synWa (.classMem (.cv z) D) (.classMem (.cv v) E)) (.imp (synWa (synWa
              (synWa (.classMem (.cv z) D) (.classEq (synCun (synCin D
                      (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
                    (synCsn (.cv y))) (synCin D
                    (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z))))))
              (.classMem (.cv v) E)) (.classEq (synCun
                (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
                (synCsn (.cv u)))
              (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))))
          (synWa (synWa (.classMem (.cv z) D) (.classMem (.cv v) E)) (synWiso
              (synCun (synCuni (synCwecutiso R D S E)) (synCsn (synCop (.cv y) (.cv u))))
              (synCin R (synCxp (synCin D
                    (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z)))) (synCin D
                    (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z)))))) (synCin S
                (synCxp (synCin E
                    (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v)))) (synCin E
                    (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))))
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z))))
              (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))))))
      (.imp (synWa (synWa (synWa (.classMem (.cv z) D) (.classEq (synCun (synCin D
                    (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
                  (synCsn (.cv y))) (synCin D
                  (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z))))))
            (.classMem (.cv v) E)) (.classEq (synCun
              (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
              (synCsn (.cv u)))
            (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))))
        (.imp (synWa (.classMem (.cv z) D) (.classMem (.cv v) E)) (.imp (synWa (synWa
                (synWa (.classMem (.cv z) D) (.classEq (synCun (synCin D
                        (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
                      (synCsn (.cv y))) (synCin D
                      (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z))))))
                (.classMem (.cv v) E)) (.classEq (synCun (synCin E
                    (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
                  (synCsn (.cv u))) (synCin E
                  (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))))
            (synWa (synWa (.classMem (.cv z) D) (.classMem (.cv v) E)) (synWiso
                (synCun (synCuni (synCwecutiso R D S E)) (synCsn (synCop (.cv y) (.cv u))))
                (synCin R (synCxp (synCin D
                      (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z)))) (synCin D
                      (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z))))))
                (synCin S (synCxp (synCin E
                      (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v)))) (synCin E
                      (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))))
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z))))
                (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v)))))))))
      p0077 p0079
  have p0081 :=
    Nominal.ax2
      (synWa (synWa (synWa (.classMem (.cv z) D) (.classEq (synCun
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
                (synCsn (.cv y)))
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z))))))
          (.classMem (.cv v) E)) (.classEq (synCun
            (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
            (synCsn (.cv u)))
          (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))))
      (synWa (.classMem (.cv z) D) (.classMem (.cv v) E))
      (.imp (synWa (synWa (synWa (.classMem (.cv z) D) (.classEq (synCun (synCin D
                    (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
                  (synCsn (.cv y))) (synCin D
                  (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z))))))
            (.classMem (.cv v) E)) (.classEq (synCun
              (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
              (synCsn (.cv u)))
            (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))))
        (synWa (synWa (.classMem (.cv z) D) (.classMem (.cv v) E)) (synWiso
            (synCun (synCuni (synCwecutiso R D S E)) (synCsn (synCop (.cv y) (.cv u))))
            (synCin R (synCxp
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z))))
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z))))))
            (synCin S (synCxp
                (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))
                (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))))
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z))))
            (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v)))))))
  have p0082 :=
    @gA1i
      (.imp (.imp (synWa (synWa (synWa (.classMem (.cv z) D) (.classEq (synCun (synCin D
                      (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
                    (synCsn (.cv y))) (synCin D
                    (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z))))))
              (.classMem (.cv v) E)) (.classEq (synCun
                (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
                (synCsn (.cv u)))
              (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))))
          (.imp (synWa (.classMem (.cv z) D) (.classMem (.cv v) E)) (.imp (synWa (synWa
                  (synWa (.classMem (.cv z) D) (.classEq (synCun (synCin D
                          (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
                        (synCsn (.cv y))) (synCin D
                        (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z))))))
                  (.classMem (.cv v) E)) (.classEq (synCun (synCin E
                      (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
                    (synCsn (.cv u))) (synCin E
                    (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))))
              (synWa (synWa (.classMem (.cv z) D) (.classMem (.cv v) E)) (synWiso
                  (synCun (synCuni (synCwecutiso R D S E))
                    (synCsn (synCop (.cv y) (.cv u)))) (synCin R (synCxp (synCin D
                        (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z))))
                      (synCin D
                        (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z))))))
                  (synCin S (synCxp (synCin E
                        (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))
                      (synCin E
                        (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))))
                  (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z))))
                  (synCin E
                    (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))))))) (.imp
          (.imp (synWa (synWa (synWa (.classMem (.cv z) D) (.classEq (synCun (synCin D
                        (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
                      (synCsn (.cv y))) (synCin D
                      (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z))))))
                (.classMem (.cv v) E)) (.classEq (synCun (synCin E
                    (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
                  (synCsn (.cv u))) (synCin E
                  (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))))
            (synWa (.classMem (.cv z) D) (.classMem (.cv v) E))) (.imp (synWa (synWa
                (synWa (.classMem (.cv z) D) (.classEq (synCun (synCin D
                        (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
                      (synCsn (.cv y))) (synCin D
                      (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z))))))
                (.classMem (.cv v) E)) (.classEq (synCun (synCin E
                    (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
                  (synCsn (.cv u))) (synCin E
                  (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v)))))) (.imp
              (synWa (synWa (synWa (.classMem (.cv z) D) (.classEq (synCun (synCin D
                          (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
                        (synCsn (.cv y))) (synCin D
                        (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z))))))
                  (.classMem (.cv v) E)) (.classEq (synCun (synCin E
                      (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
                    (synCsn (.cv u))) (synCin E
                    (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))))
              (synWa (synWa (.classMem (.cv z) D) (.classMem (.cv v) E)) (synWiso
                  (synCun (synCuni (synCwecutiso R D S E))
                    (synCsn (synCop (.cv y) (.cv u)))) (synCin R (synCxp (synCin D
                        (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z))))
                      (synCin D
                        (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z))))))
                  (synCin S (synCxp (synCin E
                        (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))
                      (synCin E
                        (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))))
                  (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z))))
                  (synCin E
                    (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))))))))
      (synWiso
        (synCun (synCuni (synCwecutiso R D S E)) (synCsn (synCop (.cv y) (.cv u)))) R S
        (synCun (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
          (synCsn (.cv y))) (synCun
          (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
          (synCsn (.cv u))))
      p0081
  have p0083 :=
    @gMpd
      (synWiso
        (synCun (synCuni (synCwecutiso R D S E)) (synCsn (synCop (.cv y) (.cv u)))) R S
        (synCun (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
          (synCsn (.cv y))) (synCun
          (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
          (synCsn (.cv u))))
      (.imp (synWa (synWa (synWa (.classMem (.cv z) D) (.classEq (synCun (synCin D
                    (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
                  (synCsn (.cv y))) (synCin D
                  (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z))))))
            (.classMem (.cv v) E)) (.classEq (synCun
              (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
              (synCsn (.cv u)))
            (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))))
        (.imp (synWa (.classMem (.cv z) D) (.classMem (.cv v) E)) (.imp (synWa (synWa
                (synWa (.classMem (.cv z) D) (.classEq (synCun (synCin D
                        (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
                      (synCsn (.cv y))) (synCin D
                      (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z))))))
                (.classMem (.cv v) E)) (.classEq (synCun (synCin E
                    (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
                  (synCsn (.cv u))) (synCin E
                  (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))))
            (synWa (synWa (.classMem (.cv z) D) (.classMem (.cv v) E)) (synWiso
                (synCun (synCuni (synCwecutiso R D S E)) (synCsn (synCop (.cv y) (.cv u))))
                (synCin R (synCxp (synCin D
                      (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z)))) (synCin D
                      (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z))))))
                (synCin S (synCxp (synCin E
                      (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v)))) (synCin E
                      (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))))
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z))))
                (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v)))))))))
      (.imp (.imp (synWa (synWa (synWa (.classMem (.cv z) D) (.classEq (synCun (synCin D
                      (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
                    (synCsn (.cv y))) (synCin D
                    (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z))))))
              (.classMem (.cv v) E)) (.classEq (synCun
                (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
                (synCsn (.cv u)))
              (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))))
          (synWa (.classMem (.cv z) D) (.classMem (.cv v) E))) (.imp (synWa (synWa
              (synWa (.classMem (.cv z) D) (.classEq (synCun (synCin D
                      (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
                    (synCsn (.cv y))) (synCin D
                    (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z))))))
              (.classMem (.cv v) E)) (.classEq (synCun
                (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
                (synCsn (.cv u)))
              (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v)))))) (.imp
            (synWa (synWa (synWa (.classMem (.cv z) D) (.classEq (synCun (synCin D
                        (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
                      (synCsn (.cv y))) (synCin D
                      (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z))))))
                (.classMem (.cv v) E)) (.classEq (synCun (synCin E
                    (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
                  (synCsn (.cv u))) (synCin E
                  (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))))
            (synWa (synWa (.classMem (.cv z) D) (.classMem (.cv v) E)) (synWiso
                (synCun (synCuni (synCwecutiso R D S E)) (synCsn (synCop (.cv y) (.cv u))))
                (synCin R (synCxp (synCin D
                      (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z)))) (synCin D
                      (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z))))))
                (synCin S (synCxp (synCin E
                      (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v)))) (synCin E
                      (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))))
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z))))
                (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v)))))))))
      p0080 p0082
  have p0084 :=
    @gMpd
      (synWiso
        (synCun (synCuni (synCwecutiso R D S E)) (synCsn (synCop (.cv y) (.cv u)))) R S
        (synCun (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
          (synCsn (.cv y))) (synCun
          (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
          (synCsn (.cv u))))
      (.imp (synWa (synWa (synWa (.classMem (.cv z) D) (.classEq (synCun (synCin D
                    (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
                  (synCsn (.cv y))) (synCin D
                  (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z))))))
            (.classMem (.cv v) E)) (.classEq (synCun
              (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
              (synCsn (.cv u)))
            (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))))
        (synWa (.classMem (.cv z) D) (.classMem (.cv v) E)))
      (.imp (synWa (synWa (synWa (.classMem (.cv z) D) (.classEq (synCun (synCin D
                    (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
                  (synCsn (.cv y))) (synCin D
                  (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z))))))
            (.classMem (.cv v) E)) (.classEq (synCun
              (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
              (synCsn (.cv u)))
            (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v)))))) (.imp
          (synWa (synWa (synWa (.classMem (.cv z) D) (.classEq (synCun (synCin D
                      (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
                    (synCsn (.cv y))) (synCin D
                    (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z))))))
              (.classMem (.cv v) E)) (.classEq (synCun
                (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
                (synCsn (.cv u)))
              (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))))
          (synWa (synWa (.classMem (.cv z) D) (.classMem (.cv v) E)) (synWiso
              (synCun (synCuni (synCwecutiso R D S E)) (synCsn (synCop (.cv y) (.cv u))))
              (synCin R (synCxp (synCin D
                    (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z)))) (synCin D
                    (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z)))))) (synCin S
                (synCxp (synCin E
                    (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v)))) (synCin E
                    (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))))
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z))))
              (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))))))
      p0019 p0083
  have p0085 :=
    Nominal.ax2
      (synWa (synWa (synWa (.classMem (.cv z) D) (.classEq (synCun
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
                (synCsn (.cv y)))
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z))))))
          (.classMem (.cv v) E)) (.classEq (synCun
            (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
            (synCsn (.cv u)))
          (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))))
      (synWa (synWa (synWa (.classMem (.cv z) D) (.classEq (synCun
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
                (synCsn (.cv y)))
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z))))))
          (.classMem (.cv v) E)) (.classEq (synCun
            (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
            (synCsn (.cv u)))
          (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))))
      (synWa (synWa (.classMem (.cv z) D) (.classMem (.cv v) E)) (synWiso
          (synCun (synCuni (synCwecutiso R D S E)) (synCsn (synCop (.cv y) (.cv u))))
          (synCin R (synCxp
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z))))
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z))))))
          (synCin S (synCxp
              (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))
              (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))))
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z))))
          (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))))
  have p0086 :=
    @gA1i
      (.imp (.imp (synWa (synWa (synWa (.classMem (.cv z) D) (.classEq (synCun (synCin D
                      (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
                    (synCsn (.cv y))) (synCin D
                    (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z))))))
              (.classMem (.cv v) E)) (.classEq (synCun
                (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
                (synCsn (.cv u)))
              (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v)))))) (.imp
            (synWa (synWa (synWa (.classMem (.cv z) D) (.classEq (synCun (synCin D
                        (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
                      (synCsn (.cv y))) (synCin D
                      (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z))))))
                (.classMem (.cv v) E)) (.classEq (synCun (synCin E
                    (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
                  (synCsn (.cv u))) (synCin E
                  (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))))
            (synWa (synWa (.classMem (.cv z) D) (.classMem (.cv v) E)) (synWiso
                (synCun (synCuni (synCwecutiso R D S E)) (synCsn (synCop (.cv y) (.cv u))))
                (synCin R (synCxp (synCin D
                      (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z)))) (synCin D
                      (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z))))))
                (synCin S (synCxp (synCin E
                      (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v)))) (synCin E
                      (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))))
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z))))
                (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))))))
        (.imp (.imp (synWa (synWa (synWa (.classMem (.cv z) D) (.classEq (synCun (synCin D
                        (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
                      (synCsn (.cv y))) (synCin D
                      (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z))))))
                (.classMem (.cv v) E)) (.classEq (synCun (synCin E
                    (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
                  (synCsn (.cv u))) (synCin E
                  (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v)))))) (synWa
              (synWa (synWa (.classMem (.cv z) D) (.classEq (synCun (synCin D
                        (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
                      (synCsn (.cv y))) (synCin D
                      (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z))))))
                (.classMem (.cv v) E)) (.classEq (synCun (synCin E
                    (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
                  (synCsn (.cv u))) (synCin E
                  (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))))) (.imp
            (synWa (synWa (synWa (.classMem (.cv z) D) (.classEq (synCun (synCin D
                        (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
                      (synCsn (.cv y))) (synCin D
                      (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z))))))
                (.classMem (.cv v) E)) (.classEq (synCun (synCin E
                    (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
                  (synCsn (.cv u))) (synCin E
                  (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))))
            (synWa (synWa (.classMem (.cv z) D) (.classMem (.cv v) E)) (synWiso
                (synCun (synCuni (synCwecutiso R D S E)) (synCsn (synCop (.cv y) (.cv u))))
                (synCin R (synCxp (synCin D
                      (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z)))) (synCin D
                      (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z))))))
                (synCin S (synCxp (synCin E
                      (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v)))) (synCin E
                      (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))))
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z))))
                (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v)))))))))
      (synWiso
        (synCun (synCuni (synCwecutiso R D S E)) (synCsn (synCop (.cv y) (.cv u)))) R S
        (synCun (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
          (synCsn (.cv y))) (synCun
          (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
          (synCsn (.cv u))))
      p0085
  have p0087 :=
    @gMpd
      (synWiso
        (synCun (synCuni (synCwecutiso R D S E)) (synCsn (synCop (.cv y) (.cv u)))) R S
        (synCun (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
          (synCsn (.cv y))) (synCun
          (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
          (synCsn (.cv u))))
      (.imp (synWa (synWa (synWa (.classMem (.cv z) D) (.classEq (synCun (synCin D
                    (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
                  (synCsn (.cv y))) (synCin D
                  (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z))))))
            (.classMem (.cv v) E)) (.classEq (synCun
              (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
              (synCsn (.cv u)))
            (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v)))))) (.imp
          (synWa (synWa (synWa (.classMem (.cv z) D) (.classEq (synCun (synCin D
                      (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
                    (synCsn (.cv y))) (synCin D
                    (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z))))))
              (.classMem (.cv v) E)) (.classEq (synCun
                (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
                (synCsn (.cv u)))
              (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))))
          (synWa (synWa (.classMem (.cv z) D) (.classMem (.cv v) E)) (synWiso
              (synCun (synCuni (synCwecutiso R D S E)) (synCsn (synCop (.cv y) (.cv u))))
              (synCin R (synCxp (synCin D
                    (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z)))) (synCin D
                    (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z)))))) (synCin S
                (synCxp (synCin E
                    (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v)))) (synCin E
                    (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))))
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z))))
              (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))))))
      (.imp (.imp (synWa (synWa (synWa (.classMem (.cv z) D) (.classEq (synCun (synCin D
                      (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
                    (synCsn (.cv y))) (synCin D
                    (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z))))))
              (.classMem (.cv v) E)) (.classEq (synCun
                (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
                (synCsn (.cv u)))
              (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))))
          (synWa (synWa (synWa (.classMem (.cv z) D) (.classEq (synCun (synCin D
                      (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
                    (synCsn (.cv y))) (synCin D
                    (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z))))))
              (.classMem (.cv v) E)) (.classEq (synCun
                (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
                (synCsn (.cv u))) (synCin E
                (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))))) (.imp (synWa
            (synWa (synWa (.classMem (.cv z) D) (.classEq (synCun (synCin D
                      (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
                    (synCsn (.cv y))) (synCin D
                    (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z))))))
              (.classMem (.cv v) E)) (.classEq (synCun
                (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
                (synCsn (.cv u)))
              (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))))
          (synWa (synWa (.classMem (.cv z) D) (.classMem (.cv v) E)) (synWiso
              (synCun (synCuni (synCwecutiso R D S E)) (synCsn (synCop (.cv y) (.cv u))))
              (synCin R (synCxp (synCin D
                    (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z)))) (synCin D
                    (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z)))))) (synCin S
                (synCxp (synCin E
                    (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v)))) (synCin E
                    (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))))
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z))))
              (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))))))
      p0084 p0086
  have p0088 :=
    @gMpd
      (synWiso
        (synCun (synCuni (synCwecutiso R D S E)) (synCsn (synCop (.cv y) (.cv u)))) R S
        (synCun (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
          (synCsn (.cv y))) (synCun
          (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
          (synCsn (.cv u))))
      (.imp (synWa (synWa (synWa (.classMem (.cv z) D) (.classEq (synCun (synCin D
                    (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
                  (synCsn (.cv y))) (synCin D
                  (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z))))))
            (.classMem (.cv v) E)) (.classEq (synCun
              (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
              (synCsn (.cv u)))
            (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v)))))) (synWa
          (synWa (synWa (.classMem (.cv z) D) (.classEq (synCun (synCin D
                    (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
                  (synCsn (.cv y))) (synCin D
                  (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z))))))
            (.classMem (.cv v) E)) (.classEq (synCun
              (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
              (synCsn (.cv u)))
            (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v)))))))
      (.imp (synWa (synWa (synWa (.classMem (.cv z) D) (.classEq (synCun (synCin D
                    (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
                  (synCsn (.cv y))) (synCin D
                  (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z))))))
            (.classMem (.cv v) E)) (.classEq (synCun
              (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
              (synCsn (.cv u)))
            (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))))
        (synWa (synWa (.classMem (.cv z) D) (.classMem (.cv v) E)) (synWiso
            (synCun (synCuni (synCwecutiso R D S E)) (synCsn (synCop (.cv y) (.cv u))))
            (synCin R (synCxp
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z))))
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z))))))
            (synCin S (synCxp
                (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))
                (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))))
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z))))
            (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v)))))))
      p0009 p0087
  have p0089 :=
    (Nominal.biimpRefl (synW3a (.classMem (.cv z) D) (.classMem (.cv v) E) (synWiso
          (synCun (synCuni (synCwecutiso R D S E)) (synCsn (synCop (.cv y) (.cv u))))
          (synCin R (synCxp
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z))))
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z))))))
          (synCin S (synCxp
              (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))
              (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))))
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z))))
          (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v)))))))
  have p0090 :=
    @gBiimpri
      (synW3a (.classMem (.cv z) D) (.classMem (.cv v) E) (synWiso
          (synCun (synCuni (synCwecutiso R D S E)) (synCsn (synCop (.cv y) (.cv u))))
          (synCin R (synCxp
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z))))
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z))))))
          (synCin S (synCxp
              (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))
              (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))))
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z))))
          (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))))
      (synWa (synWa (.classMem (.cv z) D) (.classMem (.cv v) E)) (synWiso
          (synCun (synCuni (synCwecutiso R D S E)) (synCsn (synCop (.cv y) (.cv u))))
          (synCin R (synCxp
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z))))
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z))))))
          (synCin S (synCxp
              (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))
              (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))))
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z))))
          (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))))
      p0089
  have p0091 :=
    @gA1i
      (.imp (synWa (synWa (.classMem (.cv z) D) (.classMem (.cv v) E)) (synWiso
            (synCun (synCuni (synCwecutiso R D S E)) (synCsn (synCop (.cv y) (.cv u))))
            (synCin R (synCxp
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z))))
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z))))))
            (synCin S (synCxp
                (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))
                (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))))
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z))))
            (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))))
        (synW3a (.classMem (.cv z) D) (.classMem (.cv v) E) (synWiso
            (synCun (synCuni (synCwecutiso R D S E)) (synCsn (synCop (.cv y) (.cv u))))
            (synCin R (synCxp
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z))))
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z))))))
            (synCin S (synCxp
                (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))
                (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))))
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z))))
            (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v)))))))
      (synWa (synWa (synWa (.classMem (.cv z) D) (.classEq (synCun
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
                (synCsn (.cv y)))
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z))))))
          (.classMem (.cv v) E)) (.classEq (synCun
            (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
            (synCsn (.cv u)))
          (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))))
      p0090
  have p0092 :=
    @gA2i
      (synWa (synWa (synWa (.classMem (.cv z) D) (.classEq (synCun
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
                (synCsn (.cv y)))
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z))))))
          (.classMem (.cv v) E)) (.classEq (synCun
            (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
            (synCsn (.cv u)))
          (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))))
      (synWa (synWa (.classMem (.cv z) D) (.classMem (.cv v) E)) (synWiso
          (synCun (synCuni (synCwecutiso R D S E)) (synCsn (synCop (.cv y) (.cv u))))
          (synCin R (synCxp
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z))))
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z))))))
          (synCin S (synCxp
              (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))
              (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))))
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z))))
          (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))))
      (synW3a (.classMem (.cv z) D) (.classMem (.cv v) E) (synWiso
          (synCun (synCuni (synCwecutiso R D S E)) (synCsn (synCop (.cv y) (.cv u))))
          (synCin R (synCxp
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z))))
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z))))))
          (synCin S (synCxp
              (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))
              (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))))
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z))))
          (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))))
      p0091
  have p0093 :=
    @gA1i
      (.imp (.imp (synWa (synWa (synWa (.classMem (.cv z) D) (.classEq (synCun (synCin D
                      (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
                    (synCsn (.cv y))) (synCin D
                    (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z))))))
              (.classMem (.cv v) E)) (.classEq (synCun
                (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
                (synCsn (.cv u)))
              (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))))
          (synWa (synWa (.classMem (.cv z) D) (.classMem (.cv v) E)) (synWiso
              (synCun (synCuni (synCwecutiso R D S E)) (synCsn (synCop (.cv y) (.cv u))))
              (synCin R (synCxp (synCin D
                    (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z)))) (synCin D
                    (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z)))))) (synCin S
                (synCxp (synCin E
                    (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v)))) (synCin E
                    (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))))
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z))))
              (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v)))))))
        (.imp (synWa (synWa (synWa (.classMem (.cv z) D) (.classEq (synCun (synCin D
                      (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
                    (synCsn (.cv y))) (synCin D
                    (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z))))))
              (.classMem (.cv v) E)) (.classEq (synCun
                (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
                (synCsn (.cv u)))
              (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))))
          (synW3a (.classMem (.cv z) D) (.classMem (.cv v) E) (synWiso
              (synCun (synCuni (synCwecutiso R D S E)) (synCsn (synCop (.cv y) (.cv u))))
              (synCin R (synCxp (synCin D
                    (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z)))) (synCin D
                    (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z)))))) (synCin S
                (synCxp (synCin E
                    (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v)))) (synCin E
                    (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))))
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z))))
              (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))))))
      (synWiso
        (synCun (synCuni (synCwecutiso R D S E)) (synCsn (synCop (.cv y) (.cv u)))) R S
        (synCun (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
          (synCsn (.cv y))) (synCun
          (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
          (synCsn (.cv u))))
      p0092
  have p0094 :=
    @gMpd
      (synWiso
        (synCun (synCuni (synCwecutiso R D S E)) (synCsn (synCop (.cv y) (.cv u)))) R S
        (synCun (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
          (synCsn (.cv y))) (synCun
          (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
          (synCsn (.cv u))))
      (.imp (synWa (synWa (synWa (.classMem (.cv z) D) (.classEq (synCun (synCin D
                    (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
                  (synCsn (.cv y))) (synCin D
                  (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z))))))
            (.classMem (.cv v) E)) (.classEq (synCun
              (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
              (synCsn (.cv u)))
            (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))))
        (synWa (synWa (.classMem (.cv z) D) (.classMem (.cv v) E)) (synWiso
            (synCun (synCuni (synCwecutiso R D S E)) (synCsn (synCop (.cv y) (.cv u))))
            (synCin R (synCxp
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z))))
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z))))))
            (synCin S (synCxp
                (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))
                (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))))
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z))))
            (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v)))))))
      (.imp (synWa (synWa (synWa (.classMem (.cv z) D) (.classEq (synCun (synCin D
                    (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
                  (synCsn (.cv y))) (synCin D
                  (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z))))))
            (.classMem (.cv v) E)) (.classEq (synCun
              (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
              (synCsn (.cv u)))
            (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))))
        (synW3a (.classMem (.cv z) D) (.classMem (.cv v) E) (synWiso
            (synCun (synCuni (synCwecutiso R D S E)) (synCsn (synCop (.cv y) (.cv u))))
            (synCin R (synCxp
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z))))
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z))))))
            (synCin S (synCxp
                (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))
                (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))))
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z))))
            (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v)))))))
      p0088 p0093
  have p0095 := @gSneq (.cv a) (.cv z)
  have p0096 :=
    @gImaeq2d (.classEq (.cv a) (.cv z)) (synCsn (.cv a)) (synCsn (.cv z))
      (synCcnv (synCdif R (synCid))) p0095
  have p0097 :=
    @gIneq2d (.classEq (.cv a) (.cv z))
      (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv a)))
      (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z))) D p0096
  have p0101 :=
    @gXpeq12d (.classEq (.cv a) (.cv z))
      (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv a))))
      (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z))))
      (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv a))))
      (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z)))) p0097
      p0097
  have p0102 :=
    @gIneq2d (.classEq (.cv a) (.cv z))
      (synCxp (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv a))))
        (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv a)))))
      (synCxp (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z))))
        (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z)))))
      R p0101
  have p0103 :=
    @gIsoeq2 (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv a))))
      (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv b))))
      (synCin R (synCxp
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv a))))
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv a))))))
      (synCin S (synCxp
          (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv b))))
          (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv b))))))
      (synCin R (synCxp
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z))))
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z))))))
      (synCun (synCuni (synCwecutiso R D S E)) (synCsn (synCop (.cv y) (.cv u))))
  have p0104 :=
    @gSyl (.classEq (.cv a) (.cv z))
      (.classEq (synCin R (synCxp
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv a))))
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv a))))))
        (synCin R (synCxp
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z))))
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z)))))))
      (synWb (synWiso
          (synCun (synCuni (synCwecutiso R D S E)) (synCsn (synCop (.cv y) (.cv u))))
          (synCin R (synCxp
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv a))))
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv a))))))
          (synCin S (synCxp
              (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv b))))
              (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv b))))))
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv a))))
          (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv b))))) (synWiso
          (synCun (synCuni (synCwecutiso R D S E)) (synCsn (synCop (.cv y) (.cv u))))
          (synCin R (synCxp
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z))))
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z))))))
          (synCin S (synCxp
              (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv b))))
              (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv b))))))
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv a))))
          (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv b))))))
      p0102 p0103
  have p0108 :=
    @gIsoeq4 (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv a))))
      (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv b))))
      (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z))))
      (synCin R (synCxp
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z))))
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z))))))
      (synCin S (synCxp
          (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv b))))
          (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv b))))))
      (synCun (synCuni (synCwecutiso R D S E)) (synCsn (synCop (.cv y) (.cv u))))
  have p0109 :=
    @gSyl (.classEq (.cv a) (.cv z))
      (.classEq (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv a))))
        (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z)))))
      (synWb (synWiso
          (synCun (synCuni (synCwecutiso R D S E)) (synCsn (synCop (.cv y) (.cv u))))
          (synCin R (synCxp
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z))))
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z))))))
          (synCin S (synCxp
              (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv b))))
              (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv b))))))
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv a))))
          (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv b))))) (synWiso
          (synCun (synCuni (synCwecutiso R D S E)) (synCsn (synCop (.cv y) (.cv u))))
          (synCin R (synCxp
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z))))
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z))))))
          (synCin S (synCxp
              (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv b))))
              (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv b))))))
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z))))
          (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv b))))))
      p0097 p0108
  have p0110 :=
    @gBitrd (.classEq (.cv a) (.cv z))
      (synWiso (synCun (synCuni (synCwecutiso R D S E)) (synCsn (synCop (.cv y) (.cv u))))
        (synCin R (synCxp
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv a))))
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv a))))))
        (synCin S (synCxp
            (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv b))))
            (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv b))))))
        (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv a))))
        (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv b)))))
      (synWiso (synCun (synCuni (synCwecutiso R D S E)) (synCsn (synCop (.cv y) (.cv u))))
        (synCin R (synCxp
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z))))
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z))))))
        (synCin S (synCxp
            (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv b))))
            (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv b))))))
        (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv a))))
        (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv b)))))
      (synWiso (synCun (synCuni (synCwecutiso R D S E)) (synCsn (synCop (.cv y) (.cv u))))
        (synCin R (synCxp
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z))))
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z))))))
        (synCin S (synCxp
            (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv b))))
            (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv b))))))
        (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z))))
        (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv b)))))
      p0104 p0109
  have p0111 := @gSneq (.cv b) (.cv v)
  have p0112 :=
    @gImaeq2d (.classEq (.cv b) (.cv v)) (synCsn (.cv b)) (synCsn (.cv v))
      (synCcnv (synCdif S (synCid))) p0111
  have p0113 :=
    @gIneq2d (.classEq (.cv b) (.cv v))
      (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv b)))
      (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))) E p0112
  have p0117 :=
    @gXpeq12d (.classEq (.cv b) (.cv v))
      (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv b))))
      (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))
      (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv b))))
      (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v)))) p0113
      p0113
  have p0118 :=
    @gIneq2d (.classEq (.cv b) (.cv v))
      (synCxp (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv b))))
        (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv b)))))
      (synCxp (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))
        (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v)))))
      S p0117
  have p0119 :=
    @gIsoeq3 (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z))))
      (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv b))))
      (synCin R (synCxp
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z))))
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z))))))
      (synCin S (synCxp
          (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv b))))
          (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv b))))))
      (synCin S (synCxp
          (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))
          (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))))
      (synCun (synCuni (synCwecutiso R D S E)) (synCsn (synCop (.cv y) (.cv u))))
  have p0120 :=
    @gSyl (.classEq (.cv b) (.cv v))
      (.classEq (synCin S (synCxp
            (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv b))))
            (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv b))))))
        (synCin S (synCxp
            (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))
            (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v)))))))
      (synWb (synWiso
          (synCun (synCuni (synCwecutiso R D S E)) (synCsn (synCop (.cv y) (.cv u))))
          (synCin R (synCxp
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z))))
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z))))))
          (synCin S (synCxp
              (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv b))))
              (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv b))))))
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z))))
          (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv b))))) (synWiso
          (synCun (synCuni (synCwecutiso R D S E)) (synCsn (synCop (.cv y) (.cv u))))
          (synCin R (synCxp
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z))))
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z))))))
          (synCin S (synCxp
              (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))
              (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))))
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z))))
          (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv b))))))
      p0118 p0119
  have p0124 :=
    @gIsoeq5 (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z))))
      (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv b))))
      (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))
      (synCin R (synCxp
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z))))
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z))))))
      (synCin S (synCxp
          (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))
          (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))))
      (synCun (synCuni (synCwecutiso R D S E)) (synCsn (synCop (.cv y) (.cv u))))
  have p0125 :=
    @gSyl (.classEq (.cv b) (.cv v))
      (.classEq (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv b))))
        (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v)))))
      (synWb (synWiso
          (synCun (synCuni (synCwecutiso R D S E)) (synCsn (synCop (.cv y) (.cv u))))
          (synCin R (synCxp
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z))))
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z))))))
          (synCin S (synCxp
              (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))
              (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))))
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z))))
          (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv b))))) (synWiso
          (synCun (synCuni (synCwecutiso R D S E)) (synCsn (synCop (.cv y) (.cv u))))
          (synCin R (synCxp
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z))))
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z))))))
          (synCin S (synCxp
              (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))
              (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))))
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z))))
          (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))))
      p0113 p0124
  have p0126 :=
    @gBitrd (.classEq (.cv b) (.cv v))
      (synWiso (synCun (synCuni (synCwecutiso R D S E)) (synCsn (synCop (.cv y) (.cv u))))
        (synCin R (synCxp
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z))))
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z))))))
        (synCin S (synCxp
            (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv b))))
            (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv b))))))
        (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z))))
        (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv b)))))
      (synWiso (synCun (synCuni (synCwecutiso R D S E)) (synCsn (synCop (.cv y) (.cv u))))
        (synCin R (synCxp
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z))))
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z))))))
        (synCin S (synCxp
            (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))
            (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))))
        (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z))))
        (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv b)))))
      (synWiso (synCun (synCuni (synCwecutiso R D S E)) (synCsn (synCop (.cv y) (.cv u))))
        (synCin R (synCxp
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z))))
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z))))))
        (synCin S (synCxp
            (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))
            (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))))
        (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z))))
        (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v)))))
      p0120 p0125
  have p0127 :=
    @gRspc2ev
      (synWiso (synCun (synCuni (synCwecutiso R D S E)) (synCsn (synCop (.cv y) (.cv u))))
        (synCin R (synCxp
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv a))))
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv a))))))
        (synCin S (synCxp
            (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv b))))
            (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv b))))))
        (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv a))))
        (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv b)))))
      (synWiso (synCun (synCuni (synCwecutiso R D S E)) (synCsn (synCop (.cv y) (.cv u))))
        (synCin R (synCxp
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z))))
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z))))))
        (synCin S (synCxp
            (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))
            (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))))
        (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z))))
        (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v)))))
      (synWiso (synCun (synCuni (synCwecutiso R D S E)) (synCsn (synCop (.cv y) (.cv u))))
        (synCin R (synCxp
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z))))
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z))))))
        (synCin S (synCxp
            (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv b))))
            (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv b))))))
        (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z))))
        (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv b)))))
      a b (.cv z) (.cv v) D E dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
      dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 p0110 p0126
  have p0128 :=
    @gA1i
      (.imp (synW3a (.classMem (.cv z) D) (.classMem (.cv v) E) (synWiso
            (synCun (synCuni (synCwecutiso R D S E)) (synCsn (synCop (.cv y) (.cv u))))
            (synCin R (synCxp
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z))))
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z))))))
            (synCin S (synCxp
                (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))
                (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))))
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z))))
            (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))))
        (synWrex a D (synWrex b E (synWiso (synCun (synCuni (synCwecutiso R D S E))
                (synCsn (synCop (.cv y) (.cv u)))) (synCin R (synCxp (synCin D
                    (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv a)))) (synCin D
                    (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv a)))))) (synCin S
                (synCxp (synCin E
                    (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv b)))) (synCin E
                    (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv b))))))
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv a))))
              (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv b))))))))
      (synWa (synWa (synWa (.classMem (.cv z) D) (.classEq (synCun
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
                (synCsn (.cv y)))
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z))))))
          (.classMem (.cv v) E)) (.classEq (synCun
            (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
            (synCsn (.cv u)))
          (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))))
      p0127
  have p0129 :=
    @gA2i
      (synWa (synWa (synWa (.classMem (.cv z) D) (.classEq (synCun
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
                (synCsn (.cv y)))
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z))))))
          (.classMem (.cv v) E)) (.classEq (synCun
            (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
            (synCsn (.cv u)))
          (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))))
      (synW3a (.classMem (.cv z) D) (.classMem (.cv v) E) (synWiso
          (synCun (synCuni (synCwecutiso R D S E)) (synCsn (synCop (.cv y) (.cv u))))
          (synCin R (synCxp
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z))))
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z))))))
          (synCin S (synCxp
              (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))
              (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))))
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z))))
          (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))))
      (synWrex a D (synWrex b E (synWiso (synCun (synCuni (synCwecutiso R D S E))
              (synCsn (synCop (.cv y) (.cv u)))) (synCin R (synCxp
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv a))))
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv a))))))
            (synCin S (synCxp
                (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv b))))
                (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv b))))))
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv a))))
            (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv b)))))))
      p0128
  have p0130 :=
    @gA1i
      (.imp (.imp (synWa (synWa (synWa (.classMem (.cv z) D) (.classEq (synCun (synCin D
                      (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
                    (synCsn (.cv y))) (synCin D
                    (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z))))))
              (.classMem (.cv v) E)) (.classEq (synCun
                (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
                (synCsn (.cv u)))
              (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))))
          (synW3a (.classMem (.cv z) D) (.classMem (.cv v) E) (synWiso
              (synCun (synCuni (synCwecutiso R D S E)) (synCsn (synCop (.cv y) (.cv u))))
              (synCin R (synCxp (synCin D
                    (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z)))) (synCin D
                    (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z)))))) (synCin S
                (synCxp (synCin E
                    (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v)))) (synCin E
                    (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))))
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z))))
              (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v)))))))
        (.imp (synWa (synWa (synWa (.classMem (.cv z) D) (.classEq (synCun (synCin D
                      (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
                    (synCsn (.cv y))) (synCin D
                    (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z))))))
              (.classMem (.cv v) E)) (.classEq (synCun
                (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
                (synCsn (.cv u)))
              (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))))
          (synWrex a D (synWrex b E (synWiso (synCun (synCuni (synCwecutiso R D S E))
                  (synCsn (synCop (.cv y) (.cv u)))) (synCin R (synCxp (synCin D
                      (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv a)))) (synCin D
                      (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv a))))))
                (synCin S (synCxp (synCin E
                      (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv b)))) (synCin E
                      (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv b))))))
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv a))))
                (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv b)))))))))
      (synWiso
        (synCun (synCuni (synCwecutiso R D S E)) (synCsn (synCop (.cv y) (.cv u)))) R S
        (synCun (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
          (synCsn (.cv y))) (synCun
          (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
          (synCsn (.cv u))))
      p0129
  have p0131 :=
    @gMpd
      (synWiso
        (synCun (synCuni (synCwecutiso R D S E)) (synCsn (synCop (.cv y) (.cv u)))) R S
        (synCun (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
          (synCsn (.cv y))) (synCun
          (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
          (synCsn (.cv u))))
      (.imp (synWa (synWa (synWa (.classMem (.cv z) D) (.classEq (synCun (synCin D
                    (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
                  (synCsn (.cv y))) (synCin D
                  (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z))))))
            (.classMem (.cv v) E)) (.classEq (synCun
              (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
              (synCsn (.cv u)))
            (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))))
        (synW3a (.classMem (.cv z) D) (.classMem (.cv v) E) (synWiso
            (synCun (synCuni (synCwecutiso R D S E)) (synCsn (synCop (.cv y) (.cv u))))
            (synCin R (synCxp
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z))))
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z))))))
            (synCin S (synCxp
                (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))
                (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))))
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z))))
            (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v)))))))
      (.imp (synWa (synWa (synWa (.classMem (.cv z) D) (.classEq (synCun (synCin D
                    (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
                  (synCsn (.cv y))) (synCin D
                  (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z))))))
            (.classMem (.cv v) E)) (.classEq (synCun
              (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
              (synCsn (.cv u)))
            (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))))
        (synWrex a D (synWrex b E (synWiso (synCun (synCuni (synCwecutiso R D S E))
                (synCsn (synCop (.cv y) (.cv u)))) (synCin R (synCxp (synCin D
                    (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv a)))) (synCin D
                    (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv a)))))) (synCin S
                (synCxp (synCin E
                    (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv b)))) (synCin E
                    (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv b))))))
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv a))))
              (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv b))))))))
      p0094 p0130
  have p0132 := @gSnex (synCop (.cv y) (.cv u))
  have p0133 :=
    @gUnex (synCuni (synCwecutiso R D S E)) (synCsn (synCop (.cv y) (.cv u)))
      hyp_wecutisobranchknterminalfdv_3 p0132
  have p0134 :=
    @gElwecutisoclterminalndv a b D R S E
      (synCun (synCuni (synCwecutiso R D S E)) (synCsn (synCop (.cv y) (.cv u))))
      dv_cache_0010 dv_cache_0004 dv_cache_0006 dv_cache_0005 dv_cache_0011 dv_cache_0012
      dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
  have p0135 := Nominal.mp p0133 p0134
  have p0136 :=
    @gBiimpri
      (.classMem
        (synCun (synCuni (synCwecutiso R D S E)) (synCsn (synCop (.cv y) (.cv u))))
        (synCwecutiso R D S E))
      (synWrex a D (synWrex b E (synWiso (synCun (synCuni (synCwecutiso R D S E))
              (synCsn (synCop (.cv y) (.cv u)))) (synCin R (synCxp
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv a))))
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv a))))))
            (synCin S (synCxp
                (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv b))))
                (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv b))))))
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv a))))
            (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv b)))))))
      p0135
  have p0137 :=
    @gA1i
      (.imp (synWrex a D (synWrex b E (synWiso (synCun (synCuni (synCwecutiso R D S E))
                (synCsn (synCop (.cv y) (.cv u)))) (synCin R (synCxp (synCin D
                    (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv a)))) (synCin D
                    (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv a)))))) (synCin S
                (synCxp (synCin E
                    (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv b)))) (synCin E
                    (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv b))))))
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv a))))
              (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv b)))))))
        (.classMem
          (synCun (synCuni (synCwecutiso R D S E)) (synCsn (synCop (.cv y) (.cv u))))
          (synCwecutiso R D S E)))
      (synWa (synWa (synWa (.classMem (.cv z) D) (.classEq (synCun
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
                (synCsn (.cv y)))
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z))))))
          (.classMem (.cv v) E)) (.classEq (synCun
            (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
            (synCsn (.cv u)))
          (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))))
      p0136
  have p0138 :=
    @gA2i
      (synWa (synWa (synWa (.classMem (.cv z) D) (.classEq (synCun
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
                (synCsn (.cv y)))
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z))))))
          (.classMem (.cv v) E)) (.classEq (synCun
            (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
            (synCsn (.cv u)))
          (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))))
      (synWrex a D (synWrex b E (synWiso (synCun (synCuni (synCwecutiso R D S E))
              (synCsn (synCop (.cv y) (.cv u)))) (synCin R (synCxp
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv a))))
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv a))))))
            (synCin S (synCxp
                (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv b))))
                (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv b))))))
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv a))))
            (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv b)))))))
      (.classMem
        (synCun (synCuni (synCwecutiso R D S E)) (synCsn (synCop (.cv y) (.cv u))))
        (synCwecutiso R D S E))
      p0137
  have p0139 :=
    @gA1i
      (.imp (.imp (synWa (synWa (synWa (.classMem (.cv z) D) (.classEq (synCun (synCin D
                      (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
                    (synCsn (.cv y))) (synCin D
                    (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z))))))
              (.classMem (.cv v) E)) (.classEq (synCun
                (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
                (synCsn (.cv u)))
              (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))))
          (synWrex a D (synWrex b E (synWiso (synCun (synCuni (synCwecutiso R D S E))
                  (synCsn (synCop (.cv y) (.cv u)))) (synCin R (synCxp (synCin D
                      (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv a)))) (synCin D
                      (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv a))))))
                (synCin S (synCxp (synCin E
                      (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv b)))) (synCin E
                      (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv b))))))
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv a))))
                (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv b))))))))
        (.imp (synWa (synWa (synWa (.classMem (.cv z) D) (.classEq (synCun (synCin D
                      (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
                    (synCsn (.cv y))) (synCin D
                    (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z))))))
              (.classMem (.cv v) E)) (.classEq (synCun
                (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
                (synCsn (.cv u)))
              (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))))
          (.classMem (synCun (synCuni (synCwecutiso R D S E))
              (synCsn (synCop (.cv y) (.cv u)))) (synCwecutiso R D S E))))
      (synWiso
        (synCun (synCuni (synCwecutiso R D S E)) (synCsn (synCop (.cv y) (.cv u)))) R S
        (synCun (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
          (synCsn (.cv y))) (synCun
          (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
          (synCsn (.cv u))))
      p0138
  have p0140 :=
    @gMpd
      (synWiso
        (synCun (synCuni (synCwecutiso R D S E)) (synCsn (synCop (.cv y) (.cv u)))) R S
        (synCun (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
          (synCsn (.cv y))) (synCun
          (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
          (synCsn (.cv u))))
      (.imp (synWa (synWa (synWa (.classMem (.cv z) D) (.classEq (synCun (synCin D
                    (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
                  (synCsn (.cv y))) (synCin D
                  (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z))))))
            (.classMem (.cv v) E)) (.classEq (synCun
              (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
              (synCsn (.cv u)))
            (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))))
        (synWrex a D (synWrex b E (synWiso (synCun (synCuni (synCwecutiso R D S E))
                (synCsn (synCop (.cv y) (.cv u)))) (synCin R (synCxp (synCin D
                    (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv a)))) (synCin D
                    (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv a)))))) (synCin S
                (synCxp (synCin E
                    (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv b)))) (synCin E
                    (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv b))))))
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv a))))
              (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv b))))))))
      (.imp (synWa (synWa (synWa (.classMem (.cv z) D) (.classEq (synCun (synCin D
                    (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
                  (synCsn (.cv y))) (synCin D
                  (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z))))))
            (.classMem (.cv v) E)) (.classEq (synCun
              (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
              (synCsn (.cv u)))
            (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))))
        (.classMem
          (synCun (synCuni (synCwecutiso R D S E)) (synCsn (synCop (.cv y) (.cv u))))
          (synCwecutiso R D S E)))
      p0131 p0139
  have p0141 :=
    @gElssuni
      (synCun (synCuni (synCwecutiso R D S E)) (synCsn (synCop (.cv y) (.cv u))))
      (synCwecutiso R D S E)
  have p0142 :=
    @gA1i
      (.imp (.classMem
          (synCun (synCuni (synCwecutiso R D S E)) (synCsn (synCop (.cv y) (.cv u))))
          (synCwecutiso R D S E)) (synWss
          (synCun (synCuni (synCwecutiso R D S E)) (synCsn (synCop (.cv y) (.cv u))))
          (synCuni (synCwecutiso R D S E))))
      (synWa (synWa (synWa (.classMem (.cv z) D) (.classEq (synCun
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
                (synCsn (.cv y)))
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z))))))
          (.classMem (.cv v) E)) (.classEq (synCun
            (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
            (synCsn (.cv u)))
          (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))))
      p0141
  have p0143 :=
    @gA2i
      (synWa (synWa (synWa (.classMem (.cv z) D) (.classEq (synCun
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
                (synCsn (.cv y)))
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z))))))
          (.classMem (.cv v) E)) (.classEq (synCun
            (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
            (synCsn (.cv u)))
          (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))))
      (.classMem
        (synCun (synCuni (synCwecutiso R D S E)) (synCsn (synCop (.cv y) (.cv u))))
        (synCwecutiso R D S E))
      (synWss (synCun (synCuni (synCwecutiso R D S E)) (synCsn (synCop (.cv y) (.cv u))))
        (synCuni (synCwecutiso R D S E)))
      p0142
  have p0144 :=
    @gA1i
      (.imp (.imp (synWa (synWa (synWa (.classMem (.cv z) D) (.classEq (synCun (synCin D
                      (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
                    (synCsn (.cv y))) (synCin D
                    (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z))))))
              (.classMem (.cv v) E)) (.classEq (synCun
                (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
                (synCsn (.cv u)))
              (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))))
          (.classMem (synCun (synCuni (synCwecutiso R D S E))
              (synCsn (synCop (.cv y) (.cv u)))) (synCwecutiso R D S E))) (.imp (synWa
            (synWa (synWa (.classMem (.cv z) D) (.classEq (synCun (synCin D
                      (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
                    (synCsn (.cv y))) (synCin D
                    (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z))))))
              (.classMem (.cv v) E)) (.classEq (synCun
                (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
                (synCsn (.cv u)))
              (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))))
          (synWss (synCun (synCuni (synCwecutiso R D S E))
              (synCsn (synCop (.cv y) (.cv u)))) (synCuni (synCwecutiso R D S E)))))
      (synWiso
        (synCun (synCuni (synCwecutiso R D S E)) (synCsn (synCop (.cv y) (.cv u)))) R S
        (synCun (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
          (synCsn (.cv y))) (synCun
          (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
          (synCsn (.cv u))))
      p0143
  have p0145 :=
    @gMpd
      (synWiso
        (synCun (synCuni (synCwecutiso R D S E)) (synCsn (synCop (.cv y) (.cv u)))) R S
        (synCun (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
          (synCsn (.cv y))) (synCun
          (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
          (synCsn (.cv u))))
      (.imp (synWa (synWa (synWa (.classMem (.cv z) D) (.classEq (synCun (synCin D
                    (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
                  (synCsn (.cv y))) (synCin D
                  (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z))))))
            (.classMem (.cv v) E)) (.classEq (synCun
              (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
              (synCsn (.cv u)))
            (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))))
        (.classMem
          (synCun (synCuni (synCwecutiso R D S E)) (synCsn (synCop (.cv y) (.cv u))))
          (synCwecutiso R D S E)))
      (.imp (synWa (synWa (synWa (.classMem (.cv z) D) (.classEq (synCun (synCin D
                    (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
                  (synCsn (.cv y))) (synCin D
                  (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z))))))
            (.classMem (.cv v) E)) (.classEq (synCun
              (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
              (synCsn (.cv u)))
            (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))))
        (synWss
          (synCun (synCuni (synCwecutiso R D S E)) (synCsn (synCop (.cv y) (.cv u))))
          (synCuni (synCwecutiso R D S E))))
      p0140 p0144
  have p0146 :=
    @gSsel
      (synCun (synCuni (synCwecutiso R D S E)) (synCsn (synCop (.cv y) (.cv u))))
      (synCuni (synCwecutiso R D S E)) (synCop (.cv y) (.cv u))
  have p0147 :=
    @gA1i
      (.imp (synWss
          (synCun (synCuni (synCwecutiso R D S E)) (synCsn (synCop (.cv y) (.cv u))))
          (synCuni (synCwecutiso R D S E))) (.imp (.classMem (synCop (.cv y) (.cv u))
            (synCun (synCuni (synCwecutiso R D S E)) (synCsn (synCop (.cv y) (.cv u)))))
          (.classMem (synCop (.cv y) (.cv u)) (synCuni (synCwecutiso R D S E)))))
      (synWa (synWa (synWa (.classMem (.cv z) D) (.classEq (synCun
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
                (synCsn (.cv y)))
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z))))))
          (.classMem (.cv v) E)) (.classEq (synCun
            (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
            (synCsn (.cv u)))
          (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))))
      p0146
  have p0148 :=
    @gA2i
      (synWa (synWa (synWa (.classMem (.cv z) D) (.classEq (synCun
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
                (synCsn (.cv y)))
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z))))))
          (.classMem (.cv v) E)) (.classEq (synCun
            (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
            (synCsn (.cv u)))
          (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))))
      (synWss (synCun (synCuni (synCwecutiso R D S E)) (synCsn (synCop (.cv y) (.cv u))))
        (synCuni (synCwecutiso R D S E)))
      (.imp (.classMem (synCop (.cv y) (.cv u)) (synCun (synCuni (synCwecutiso R D S E))
            (synCsn (synCop (.cv y) (.cv u)))))
        (.classMem (synCop (.cv y) (.cv u)) (synCuni (synCwecutiso R D S E))))
      p0147
  have p0149 :=
    @gA1i
      (.imp (.imp (synWa (synWa (synWa (.classMem (.cv z) D) (.classEq (synCun (synCin D
                      (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
                    (synCsn (.cv y))) (synCin D
                    (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z))))))
              (.classMem (.cv v) E)) (.classEq (synCun
                (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
                (synCsn (.cv u)))
              (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))))
          (synWss (synCun (synCuni (synCwecutiso R D S E))
              (synCsn (synCop (.cv y) (.cv u)))) (synCuni (synCwecutiso R D S E)))) (.imp
          (synWa (synWa (synWa (.classMem (.cv z) D) (.classEq (synCun (synCin D
                      (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
                    (synCsn (.cv y))) (synCin D
                    (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z))))))
              (.classMem (.cv v) E)) (.classEq (synCun
                (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
                (synCsn (.cv u)))
              (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v)))))) (.imp
            (.classMem (synCop (.cv y) (.cv u)) (synCun (synCuni (synCwecutiso R D S E))
                (synCsn (synCop (.cv y) (.cv u)))))
            (.classMem (synCop (.cv y) (.cv u)) (synCuni (synCwecutiso R D S E))))))
      (synWiso
        (synCun (synCuni (synCwecutiso R D S E)) (synCsn (synCop (.cv y) (.cv u)))) R S
        (synCun (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
          (synCsn (.cv y))) (synCun
          (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
          (synCsn (.cv u))))
      p0148
  have p0150 :=
    @gMpd
      (synWiso
        (synCun (synCuni (synCwecutiso R D S E)) (synCsn (synCop (.cv y) (.cv u)))) R S
        (synCun (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
          (synCsn (.cv y))) (synCun
          (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
          (synCsn (.cv u))))
      (.imp (synWa (synWa (synWa (.classMem (.cv z) D) (.classEq (synCun (synCin D
                    (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
                  (synCsn (.cv y))) (synCin D
                  (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z))))))
            (.classMem (.cv v) E)) (.classEq (synCun
              (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
              (synCsn (.cv u)))
            (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))))
        (synWss
          (synCun (synCuni (synCwecutiso R D S E)) (synCsn (synCop (.cv y) (.cv u))))
          (synCuni (synCwecutiso R D S E))))
      (.imp (synWa (synWa (synWa (.classMem (.cv z) D) (.classEq (synCun (synCin D
                    (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
                  (synCsn (.cv y))) (synCin D
                  (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z))))))
            (.classMem (.cv v) E)) (.classEq (synCun
              (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
              (synCsn (.cv u)))
            (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v)))))) (.imp
          (.classMem (synCop (.cv y) (.cv u)) (synCun (synCuni (synCwecutiso R D S E))
              (synCsn (synCop (.cv y) (.cv u)))))
          (.classMem (synCop (.cv y) (.cv u)) (synCuni (synCwecutiso R D S E)))))
      p0145 p0149
  have p0151 :=
    Nominal.ax2
      (synWa (synWa (synWa (.classMem (.cv z) D) (.classEq (synCun
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
                (synCsn (.cv y)))
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z))))))
          (.classMem (.cv v) E)) (.classEq (synCun
            (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
            (synCsn (.cv u)))
          (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))))
      (.classMem (synCop (.cv y) (.cv u))
        (synCun (synCuni (synCwecutiso R D S E)) (synCsn (synCop (.cv y) (.cv u)))))
      (.classMem (synCop (.cv y) (.cv u)) (synCuni (synCwecutiso R D S E)))
  have p0152 :=
    @gA1i
      (.imp (.imp (synWa (synWa (synWa (.classMem (.cv z) D) (.classEq (synCun (synCin D
                      (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
                    (synCsn (.cv y))) (synCin D
                    (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z))))))
              (.classMem (.cv v) E)) (.classEq (synCun
                (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
                (synCsn (.cv u)))
              (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v)))))) (.imp
            (.classMem (synCop (.cv y) (.cv u)) (synCun (synCuni (synCwecutiso R D S E))
                (synCsn (synCop (.cv y) (.cv u)))))
            (.classMem (synCop (.cv y) (.cv u)) (synCuni (synCwecutiso R D S E))))) (.imp
          (.imp (synWa (synWa (synWa (.classMem (.cv z) D) (.classEq (synCun (synCin D
                        (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
                      (synCsn (.cv y))) (synCin D
                      (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z))))))
                (.classMem (.cv v) E)) (.classEq (synCun (synCin E
                    (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
                  (synCsn (.cv u))) (synCin E
                  (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))))
            (.classMem (synCop (.cv y) (.cv u)) (synCun (synCuni (synCwecutiso R D S E))
                (synCsn (synCop (.cv y) (.cv u)))))) (.imp (synWa (synWa
                (synWa (.classMem (.cv z) D) (.classEq (synCun (synCin D
                        (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
                      (synCsn (.cv y))) (synCin D
                      (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z))))))
                (.classMem (.cv v) E)) (.classEq (synCun (synCin E
                    (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
                  (synCsn (.cv u))) (synCin E
                  (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))))
            (.classMem (synCop (.cv y) (.cv u)) (synCuni (synCwecutiso R D S E))))))
      (synWiso
        (synCun (synCuni (synCwecutiso R D S E)) (synCsn (synCop (.cv y) (.cv u)))) R S
        (synCun (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
          (synCsn (.cv y))) (synCun
          (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
          (synCsn (.cv u))))
      p0151
  have p0153 :=
    @gMpd
      (synWiso
        (synCun (synCuni (synCwecutiso R D S E)) (synCsn (synCop (.cv y) (.cv u)))) R S
        (synCun (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
          (synCsn (.cv y))) (synCun
          (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
          (synCsn (.cv u))))
      (.imp (synWa (synWa (synWa (.classMem (.cv z) D) (.classEq (synCun (synCin D
                    (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
                  (synCsn (.cv y))) (synCin D
                  (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z))))))
            (.classMem (.cv v) E)) (.classEq (synCun
              (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
              (synCsn (.cv u)))
            (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v)))))) (.imp
          (.classMem (synCop (.cv y) (.cv u)) (synCun (synCuni (synCwecutiso R D S E))
              (synCsn (synCop (.cv y) (.cv u)))))
          (.classMem (synCop (.cv y) (.cv u)) (synCuni (synCwecutiso R D S E)))))
      (.imp (.imp (synWa (synWa (synWa (.classMem (.cv z) D) (.classEq (synCun (synCin D
                      (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
                    (synCsn (.cv y))) (synCin D
                    (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z))))))
              (.classMem (.cv v) E)) (.classEq (synCun
                (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
                (synCsn (.cv u)))
              (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))))
          (.classMem (synCop (.cv y) (.cv u)) (synCun (synCuni (synCwecutiso R D S E))
              (synCsn (synCop (.cv y) (.cv u)))))) (.imp (synWa (synWa
              (synWa (.classMem (.cv z) D) (.classEq (synCun (synCin D
                      (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
                    (synCsn (.cv y))) (synCin D
                    (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z))))))
              (.classMem (.cv v) E)) (.classEq (synCun
                (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
                (synCsn (.cv u)))
              (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))))
          (.classMem (synCop (.cv y) (.cv u)) (synCuni (synCwecutiso R D S E)))))
      p0150 p0152
  have p0154 :=
    @gMpd
      (synWiso
        (synCun (synCuni (synCwecutiso R D S E)) (synCsn (synCop (.cv y) (.cv u)))) R S
        (synCun (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
          (synCsn (.cv y))) (synCun
          (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
          (synCsn (.cv u))))
      (.imp (synWa (synWa (synWa (.classMem (.cv z) D) (.classEq (synCun (synCin D
                    (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
                  (synCsn (.cv y))) (synCin D
                  (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z))))))
            (.classMem (.cv v) E)) (.classEq (synCun
              (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
              (synCsn (.cv u)))
            (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))))
        (.classMem (synCop (.cv y) (.cv u)) (synCun (synCuni (synCwecutiso R D S E))
            (synCsn (synCop (.cv y) (.cv u))))))
      (.imp (synWa (synWa (synWa (.classMem (.cv z) D) (.classEq (synCun (synCin D
                    (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
                  (synCsn (.cv y))) (synCin D
                  (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z))))))
            (.classMem (.cv v) E)) (.classEq (synCun
              (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
              (synCsn (.cv u)))
            (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))))
        (.classMem (synCop (.cv y) (.cv u)) (synCuni (synCwecutiso R D S E))))
      p0007 p0153
  have p0155 := @gOpeldm (.cv y) (.cv u) (synCuni (synCwecutiso R D S E))
  have p0156 :=
    @gA1i
      (.imp (.classMem (synCop (.cv y) (.cv u)) (synCuni (synCwecutiso R D S E)))
        (.classMem (.cv y) (synCdm (synCuni (synCwecutiso R D S E)))))
      (synWa (synWa (synWa (.classMem (.cv z) D) (.classEq (synCun
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
                (synCsn (.cv y)))
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z))))))
          (.classMem (.cv v) E)) (.classEq (synCun
            (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
            (synCsn (.cv u)))
          (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))))
      p0155
  have p0157 :=
    @gA2i
      (synWa (synWa (synWa (.classMem (.cv z) D) (.classEq (synCun
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
                (synCsn (.cv y)))
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z))))))
          (.classMem (.cv v) E)) (.classEq (synCun
            (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
            (synCsn (.cv u)))
          (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))))
      (.classMem (synCop (.cv y) (.cv u)) (synCuni (synCwecutiso R D S E)))
      (.classMem (.cv y) (synCdm (synCuni (synCwecutiso R D S E)))) p0156
  have p0158 :=
    @gA1i
      (.imp (.imp (synWa (synWa (synWa (.classMem (.cv z) D) (.classEq (synCun (synCin D
                      (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
                    (synCsn (.cv y))) (synCin D
                    (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z))))))
              (.classMem (.cv v) E)) (.classEq (synCun
                (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
                (synCsn (.cv u)))
              (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))))
          (.classMem (synCop (.cv y) (.cv u)) (synCuni (synCwecutiso R D S E)))) (.imp
          (synWa (synWa (synWa (.classMem (.cv z) D) (.classEq (synCun (synCin D
                      (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
                    (synCsn (.cv y))) (synCin D
                    (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z))))))
              (.classMem (.cv v) E)) (.classEq (synCun
                (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
                (synCsn (.cv u)))
              (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))))
          (.classMem (.cv y) (synCdm (synCuni (synCwecutiso R D S E))))))
      (synWiso
        (synCun (synCuni (synCwecutiso R D S E)) (synCsn (synCop (.cv y) (.cv u)))) R S
        (synCun (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
          (synCsn (.cv y))) (synCun
          (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
          (synCsn (.cv u))))
      p0157
  have p0159 :=
    @gMpd
      (synWiso
        (synCun (synCuni (synCwecutiso R D S E)) (synCsn (synCop (.cv y) (.cv u)))) R S
        (synCun (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
          (synCsn (.cv y))) (synCun
          (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
          (synCsn (.cv u))))
      (.imp (synWa (synWa (synWa (.classMem (.cv z) D) (.classEq (synCun (synCin D
                    (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
                  (synCsn (.cv y))) (synCin D
                  (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z))))))
            (.classMem (.cv v) E)) (.classEq (synCun
              (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
              (synCsn (.cv u)))
            (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))))
        (.classMem (synCop (.cv y) (.cv u)) (synCuni (synCwecutiso R D S E))))
      (.imp (synWa (synWa (synWa (.classMem (.cv z) D) (.classEq (synCun (synCin D
                    (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
                  (synCsn (.cv y))) (synCin D
                  (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z))))))
            (.classMem (.cv v) E)) (.classEq (synCun
              (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
              (synCsn (.cv u)))
            (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))))
        (.classMem (.cv y) (synCdm (synCuni (synCwecutiso R D S E)))))
      p0154 p0158
  have p0160 :=
    @gA1i
      (.imp (synWiso
          (synCun (synCuni (synCwecutiso R D S E)) (synCsn (synCop (.cv y) (.cv u)))) R S
          (synCun (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
            (synCsn (.cv y))) (synCun
            (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
            (synCsn (.cv u)))) (.imp (synWa (synWa (synWa (.classMem (.cv z) D) (.classEq
                  (synCun (synCin D
                      (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
                    (synCsn (.cv y))) (synCin D
                    (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z))))))
              (.classMem (.cv v) E)) (.classEq (synCun
                (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
                (synCsn (.cv u)))
              (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))))
          (.classMem (.cv y) (synCdm (synCuni (synCwecutiso R D S E))))))
      (.neg (.classMem (.cv y) (synCdm (synCuni (synCwecutiso R D S E))))) p0159
  have p0161 :=
    @gId (.neg (.classMem (.cv y) (synCdm (synCuni (synCwecutiso R D S E)))))
  have p0162 :=
    Nominal.ax1 (.neg (.classMem (.cv y) (synCdm (synCuni (synCwecutiso R D S E)))))
      (synWa (synWa (synWa (.classMem (.cv z) D) (.classEq (synCun
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
                (synCsn (.cv y)))
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z))))))
          (.classMem (.cv v) E)) (.classEq (synCun
            (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
            (synCsn (.cv u)))
          (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))))
  have p0163 :=
    @gA1i
      (.imp (.neg (.classMem (.cv y) (synCdm (synCuni (synCwecutiso R D S E))))) (.imp
          (synWa (synWa (synWa (.classMem (.cv z) D) (.classEq (synCun (synCin D
                      (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
                    (synCsn (.cv y))) (synCin D
                    (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z))))))
              (.classMem (.cv v) E)) (.classEq (synCun
                (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
                (synCsn (.cv u)))
              (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))))
          (.neg (.classMem (.cv y) (synCdm (synCuni (synCwecutiso R D S E)))))))
      (.neg (.classMem (.cv y) (synCdm (synCuni (synCwecutiso R D S E))))) p0162
  have p0164 :=
    @gMpd (.neg (.classMem (.cv y) (synCdm (synCuni (synCwecutiso R D S E)))))
      (.neg (.classMem (.cv y) (synCdm (synCuni (synCwecutiso R D S E)))))
      (.imp (synWa (synWa (synWa (.classMem (.cv z) D) (.classEq (synCun (synCin D
                    (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
                  (synCsn (.cv y))) (synCin D
                  (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z))))))
            (.classMem (.cv v) E)) (.classEq (synCun
              (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
              (synCsn (.cv u)))
            (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))))
        (.neg (.classMem (.cv y) (synCdm (synCuni (synCwecutiso R D S E))))))
      p0161 p0163
  have p0165 :=
    Nominal.ax1 (.neg (.classMem (.cv y) (synCdm (synCuni (synCwecutiso R D S E)))))
      (.neg (synW3o (synWex h (synWiso (.cv h) R S D E)) (synWrex x E (synWex h
              (synWiso (.cv h) R (synCin S (synCxp (synCin E
                      (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv x)))) (synCin E
                      (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv x)))))) D
                (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv x)))))))
          (synWrex x D (synWex h (synWiso (.cv h) S (synCin R (synCxp (synCin D
                      (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))) (synCin D
                      (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))))) E
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))))))))
  have p0166 :=
    @gA1i
      (.imp (.neg (.classMem (.cv y) (synCdm (synCuni (synCwecutiso R D S E))))) (.imp (.neg
            (synW3o (synWex h (synWiso (.cv h) R S D E)) (synWrex x E (synWex h
                  (synWiso (.cv h) R (synCin S (synCxp (synCin E
                          (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv x))))
                        (synCin E (synCima (synCcnv (synCdif S (synCid)))
                            (synCsn (.cv x)))))) D (synCin E
                      (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv x)))))))
              (synWrex x D (synWex h (synWiso (.cv h) S (synCin R (synCxp (synCin D
                          (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
                        (synCin D (synCima (synCcnv (synCdif R (synCid)))
                            (synCsn (.cv x)))))) E (synCin D
                      (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))))))))
          (.neg (.classMem (.cv y) (synCdm (synCuni (synCwecutiso R D S E)))))))
      (synWa (synWa (synWa (.classMem (.cv z) D) (.classEq (synCun
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
                (synCsn (.cv y)))
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z))))))
          (.classMem (.cv v) E)) (.classEq (synCun
            (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
            (synCsn (.cv u)))
          (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))))
      p0165
  have p0167 :=
    @gA2i
      (synWa (synWa (synWa (.classMem (.cv z) D) (.classEq (synCun
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
                (synCsn (.cv y)))
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z))))))
          (.classMem (.cv v) E)) (.classEq (synCun
            (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
            (synCsn (.cv u)))
          (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))))
      (.neg (.classMem (.cv y) (synCdm (synCuni (synCwecutiso R D S E)))))
      (.imp (.neg (synW3o (synWex h (synWiso (.cv h) R S D E)) (synWrex x E (synWex h
                (synWiso (.cv h) R (synCin S (synCxp (synCin E
                        (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv x))))
                      (synCin E
                        (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv x)))))) D
                  (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv x)))))))
            (synWrex x D (synWex h (synWiso (.cv h) S (synCin R (synCxp (synCin D
                        (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
                      (synCin D
                        (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))))) E
                  (synCin D
                    (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))))))))
        (.neg (.classMem (.cv y) (synCdm (synCuni (synCwecutiso R D S E))))))
      p0166
  have p0168 :=
    @gA1i
      (.imp (.imp (synWa (synWa (synWa (.classMem (.cv z) D) (.classEq (synCun (synCin D
                      (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
                    (synCsn (.cv y))) (synCin D
                    (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z))))))
              (.classMem (.cv v) E)) (.classEq (synCun
                (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
                (synCsn (.cv u)))
              (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))))
          (.neg (.classMem (.cv y) (synCdm (synCuni (synCwecutiso R D S E)))))) (.imp (synWa
            (synWa (synWa (.classMem (.cv z) D) (.classEq (synCun (synCin D
                      (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
                    (synCsn (.cv y))) (synCin D
                    (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z))))))
              (.classMem (.cv v) E)) (.classEq (synCun
                (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
                (synCsn (.cv u)))
              (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v)))))) (.imp
            (.neg (synW3o (synWex h (synWiso (.cv h) R S D E)) (synWrex x E (synWex h
                    (synWiso (.cv h) R (synCin S (synCxp (synCin E
                            (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv x))))
                          (synCin E (synCima (synCcnv (synCdif S (synCid)))
                              (synCsn (.cv x)))))) D (synCin E
                        (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv x)))))))
                (synWrex x D (synWex h (synWiso (.cv h) S (synCin R (synCxp (synCin D
                            (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
                          (synCin D (synCima (synCcnv (synCdif R (synCid)))
                              (synCsn (.cv x)))))) E (synCin D
                        (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))))))))
            (.neg (.classMem (.cv y) (synCdm (synCuni (synCwecutiso R D S E))))))))
      (.neg (.classMem (.cv y) (synCdm (synCuni (synCwecutiso R D S E))))) p0167
  have p0169 :=
    @gMpd (.neg (.classMem (.cv y) (synCdm (synCuni (synCwecutiso R D S E)))))
      (.imp (synWa (synWa (synWa (.classMem (.cv z) D) (.classEq (synCun (synCin D
                    (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
                  (synCsn (.cv y))) (synCin D
                  (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z))))))
            (.classMem (.cv v) E)) (.classEq (synCun
              (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
              (synCsn (.cv u)))
            (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))))
        (.neg (.classMem (.cv y) (synCdm (synCuni (synCwecutiso R D S E))))))
      (.imp (synWa (synWa (synWa (.classMem (.cv z) D) (.classEq (synCun (synCin D
                    (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
                  (synCsn (.cv y))) (synCin D
                  (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z))))))
            (.classMem (.cv v) E)) (.classEq (synCun
              (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
              (synCsn (.cv u)))
            (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v)))))) (.imp
          (.neg (synW3o (synWex h (synWiso (.cv h) R S D E)) (synWrex x E (synWex h
                  (synWiso (.cv h) R (synCin S (synCxp (synCin E
                          (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv x))))
                        (synCin E (synCima (synCcnv (synCdif S (synCid)))
                            (synCsn (.cv x)))))) D (synCin E
                      (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv x)))))))
              (synWrex x D (synWex h (synWiso (.cv h) S (synCin R (synCxp (synCin D
                          (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
                        (synCin D (synCima (synCcnv (synCdif R (synCid)))
                            (synCsn (.cv x)))))) E (synCin D
                      (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))))))))
          (.neg (.classMem (.cv y) (synCdm (synCuni (synCwecutiso R D S E)))))))
      p0164 p0168
  have p0170 :=
    Nominal.ax3
      (synW3o (synWex h (synWiso (.cv h) R S D E)) (synWrex x E (synWex h
            (synWiso (.cv h) R (synCin S (synCxp (synCin E
                    (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv x)))) (synCin E
                    (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv x)))))) D
              (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv x)))))))
        (synWrex x D (synWex h (synWiso (.cv h) S (synCin R (synCxp (synCin D
                    (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))) (synCin D
                    (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))))) E
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))))
      (.classMem (.cv y) (synCdm (synCuni (synCwecutiso R D S E))))
  have p0171 :=
    @gA1i
      (.imp (.imp (.neg (synW3o (synWex h (synWiso (.cv h) R S D E)) (synWrex x E (synWex h
                  (synWiso (.cv h) R (synCin S (synCxp (synCin E
                          (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv x))))
                        (synCin E (synCima (synCcnv (synCdif S (synCid)))
                            (synCsn (.cv x)))))) D (synCin E
                      (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv x)))))))
              (synWrex x D (synWex h (synWiso (.cv h) S (synCin R (synCxp (synCin D
                          (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
                        (synCin D (synCima (synCcnv (synCdif R (synCid)))
                            (synCsn (.cv x)))))) E (synCin D
                      (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))))))))
          (.neg (.classMem (.cv y) (synCdm (synCuni (synCwecutiso R D S E))))))
        (.imp (.classMem (.cv y) (synCdm (synCuni (synCwecutiso R D S E))))
          (synW3o (synWex h (synWiso (.cv h) R S D E)) (synWrex x E (synWex h
                (synWiso (.cv h) R (synCin S (synCxp (synCin E
                        (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv x))))
                      (synCin E
                        (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv x)))))) D
                  (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv x)))))))
            (synWrex x D (synWex h (synWiso (.cv h) S (synCin R (synCxp (synCin D
                        (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
                      (synCin D
                        (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))))) E
                  (synCin D
                    (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))))))
      (synWa (synWa (synWa (.classMem (.cv z) D) (.classEq (synCun
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
                (synCsn (.cv y)))
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z))))))
          (.classMem (.cv v) E)) (.classEq (synCun
            (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
            (synCsn (.cv u)))
          (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))))
      p0170
  have p0172 :=
    @gA2i
      (synWa (synWa (synWa (.classMem (.cv z) D) (.classEq (synCun
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
                (synCsn (.cv y)))
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z))))))
          (.classMem (.cv v) E)) (.classEq (synCun
            (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
            (synCsn (.cv u)))
          (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))))
      (.imp (.neg (synW3o (synWex h (synWiso (.cv h) R S D E)) (synWrex x E (synWex h
                (synWiso (.cv h) R (synCin S (synCxp (synCin E
                        (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv x))))
                      (synCin E
                        (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv x)))))) D
                  (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv x)))))))
            (synWrex x D (synWex h (synWiso (.cv h) S (synCin R (synCxp (synCin D
                        (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
                      (synCin D
                        (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))))) E
                  (synCin D
                    (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))))))))
        (.neg (.classMem (.cv y) (synCdm (synCuni (synCwecutiso R D S E))))))
      (.imp (.classMem (.cv y) (synCdm (synCuni (synCwecutiso R D S E))))
        (synW3o (synWex h (synWiso (.cv h) R S D E)) (synWrex x E (synWex h
              (synWiso (.cv h) R (synCin S (synCxp (synCin E
                      (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv x)))) (synCin E
                      (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv x)))))) D
                (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv x)))))))
          (synWrex x D (synWex h (synWiso (.cv h) S (synCin R (synCxp (synCin D
                      (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))) (synCin D
                      (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))))) E
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))))))))
      p0171
  have p0173 :=
    @gA1i
      (.imp (.imp (synWa (synWa (synWa (.classMem (.cv z) D) (.classEq (synCun (synCin D
                      (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
                    (synCsn (.cv y))) (synCin D
                    (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z))))))
              (.classMem (.cv v) E)) (.classEq (synCun
                (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
                (synCsn (.cv u)))
              (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v)))))) (.imp
            (.neg (synW3o (synWex h (synWiso (.cv h) R S D E)) (synWrex x E (synWex h
                    (synWiso (.cv h) R (synCin S (synCxp (synCin E
                            (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv x))))
                          (synCin E (synCima (synCcnv (synCdif S (synCid)))
                              (synCsn (.cv x)))))) D (synCin E
                        (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv x)))))))
                (synWrex x D (synWex h (synWiso (.cv h) S (synCin R (synCxp (synCin D
                            (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
                          (synCin D (synCima (synCcnv (synCdif R (synCid)))
                              (synCsn (.cv x)))))) E (synCin D
                        (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))))))))
            (.neg (.classMem (.cv y) (synCdm (synCuni (synCwecutiso R D S E))))))) (.imp
          (synWa (synWa (synWa (.classMem (.cv z) D) (.classEq (synCun (synCin D
                      (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
                    (synCsn (.cv y))) (synCin D
                    (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z))))))
              (.classMem (.cv v) E)) (.classEq (synCun
                (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
                (synCsn (.cv u)))
              (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))))
          (.imp (.classMem (.cv y) (synCdm (synCuni (synCwecutiso R D S E))))
            (synW3o (synWex h (synWiso (.cv h) R S D E)) (synWrex x E (synWex h
                  (synWiso (.cv h) R (synCin S (synCxp (synCin E
                          (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv x))))
                        (synCin E (synCima (synCcnv (synCdif S (synCid)))
                            (synCsn (.cv x)))))) D (synCin E
                      (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv x)))))))
              (synWrex x D (synWex h (synWiso (.cv h) S (synCin R (synCxp (synCin D
                          (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
                        (synCin D (synCima (synCcnv (synCdif R (synCid)))
                            (synCsn (.cv x)))))) E (synCin D
                      (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))))))))))
      (.neg (.classMem (.cv y) (synCdm (synCuni (synCwecutiso R D S E))))) p0172
  have p0174 :=
    @gMpd (.neg (.classMem (.cv y) (synCdm (synCuni (synCwecutiso R D S E)))))
      (.imp (synWa (synWa (synWa (.classMem (.cv z) D) (.classEq (synCun (synCin D
                    (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
                  (synCsn (.cv y))) (synCin D
                  (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z))))))
            (.classMem (.cv v) E)) (.classEq (synCun
              (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
              (synCsn (.cv u)))
            (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v)))))) (.imp
          (.neg (synW3o (synWex h (synWiso (.cv h) R S D E)) (synWrex x E (synWex h
                  (synWiso (.cv h) R (synCin S (synCxp (synCin E
                          (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv x))))
                        (synCin E (synCima (synCcnv (synCdif S (synCid)))
                            (synCsn (.cv x)))))) D (synCin E
                      (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv x)))))))
              (synWrex x D (synWex h (synWiso (.cv h) S (synCin R (synCxp (synCin D
                          (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
                        (synCin D (synCima (synCcnv (synCdif R (synCid)))
                            (synCsn (.cv x)))))) E (synCin D
                      (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))))))))
          (.neg (.classMem (.cv y) (synCdm (synCuni (synCwecutiso R D S E)))))))
      (.imp (synWa (synWa (synWa (.classMem (.cv z) D) (.classEq (synCun (synCin D
                    (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
                  (synCsn (.cv y))) (synCin D
                  (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z))))))
            (.classMem (.cv v) E)) (.classEq (synCun
              (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
              (synCsn (.cv u)))
            (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))))
        (.imp (.classMem (.cv y) (synCdm (synCuni (synCwecutiso R D S E))))
          (synW3o (synWex h (synWiso (.cv h) R S D E)) (synWrex x E (synWex h
                (synWiso (.cv h) R (synCin S (synCxp (synCin E
                        (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv x))))
                      (synCin E
                        (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv x)))))) D
                  (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv x)))))))
            (synWrex x D (synWex h (synWiso (.cv h) S (synCin R (synCxp (synCin D
                        (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
                      (synCin D
                        (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))))) E
                  (synCin D
                    (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))))))
      p0169 p0173
  have p0175 :=
    Nominal.ax2
      (synWa (synWa (synWa (.classMem (.cv z) D) (.classEq (synCun
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
                (synCsn (.cv y)))
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z))))))
          (.classMem (.cv v) E)) (.classEq (synCun
            (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
            (synCsn (.cv u)))
          (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))))
      (.classMem (.cv y) (synCdm (synCuni (synCwecutiso R D S E))))
      (synW3o (synWex h (synWiso (.cv h) R S D E)) (synWrex x E (synWex h
            (synWiso (.cv h) R (synCin S (synCxp (synCin E
                    (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv x)))) (synCin E
                    (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv x)))))) D
              (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv x)))))))
        (synWrex x D (synWex h (synWiso (.cv h) S (synCin R (synCxp (synCin D
                    (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))) (synCin D
                    (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))))) E
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))))
  have p0176 :=
    @gA1i
      (.imp (.imp (synWa (synWa (synWa (.classMem (.cv z) D) (.classEq (synCun (synCin D
                      (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
                    (synCsn (.cv y))) (synCin D
                    (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z))))))
              (.classMem (.cv v) E)) (.classEq (synCun
                (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
                (synCsn (.cv u)))
              (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))))
          (.imp (.classMem (.cv y) (synCdm (synCuni (synCwecutiso R D S E))))
            (synW3o (synWex h (synWiso (.cv h) R S D E)) (synWrex x E (synWex h
                  (synWiso (.cv h) R (synCin S (synCxp (synCin E
                          (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv x))))
                        (synCin E (synCima (synCcnv (synCdif S (synCid)))
                            (synCsn (.cv x)))))) D (synCin E
                      (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv x)))))))
              (synWrex x D (synWex h (synWiso (.cv h) S (synCin R (synCxp (synCin D
                          (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
                        (synCin D (synCima (synCcnv (synCdif R (synCid)))
                            (synCsn (.cv x)))))) E (synCin D
                      (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))))))
        (.imp (.imp (synWa (synWa (synWa (.classMem (.cv z) D) (.classEq (synCun (synCin D
                        (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
                      (synCsn (.cv y))) (synCin D
                      (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z))))))
                (.classMem (.cv v) E)) (.classEq (synCun (synCin E
                    (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
                  (synCsn (.cv u))) (synCin E
                  (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))))
            (.classMem (.cv y) (synCdm (synCuni (synCwecutiso R D S E))))) (.imp (synWa
              (synWa (synWa (.classMem (.cv z) D) (.classEq (synCun (synCin D
                        (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
                      (synCsn (.cv y))) (synCin D
                      (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z))))))
                (.classMem (.cv v) E)) (.classEq (synCun (synCin E
                    (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
                  (synCsn (.cv u))) (synCin E
                  (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))))
            (synW3o (synWex h (synWiso (.cv h) R S D E)) (synWrex x E (synWex h
                  (synWiso (.cv h) R (synCin S (synCxp (synCin E
                          (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv x))))
                        (synCin E (synCima (synCcnv (synCdif S (synCid)))
                            (synCsn (.cv x)))))) D (synCin E
                      (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv x)))))))
              (synWrex x D (synWex h (synWiso (.cv h) S (synCin R (synCxp (synCin D
                          (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
                        (synCin D (synCima (synCcnv (synCdif R (synCid)))
                            (synCsn (.cv x)))))) E (synCin D
                      (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))))))))))
      (.neg (.classMem (.cv y) (synCdm (synCuni (synCwecutiso R D S E))))) p0175
  have p0177 :=
    @gMpd (.neg (.classMem (.cv y) (synCdm (synCuni (synCwecutiso R D S E)))))
      (.imp (synWa (synWa (synWa (.classMem (.cv z) D) (.classEq (synCun (synCin D
                    (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
                  (synCsn (.cv y))) (synCin D
                  (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z))))))
            (.classMem (.cv v) E)) (.classEq (synCun
              (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
              (synCsn (.cv u)))
            (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))))
        (.imp (.classMem (.cv y) (synCdm (synCuni (synCwecutiso R D S E))))
          (synW3o (synWex h (synWiso (.cv h) R S D E)) (synWrex x E (synWex h
                (synWiso (.cv h) R (synCin S (synCxp (synCin E
                        (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv x))))
                      (synCin E
                        (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv x)))))) D
                  (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv x)))))))
            (synWrex x D (synWex h (synWiso (.cv h) S (synCin R (synCxp (synCin D
                        (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
                      (synCin D
                        (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))))) E
                  (synCin D
                    (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))))))
      (.imp (.imp (synWa (synWa (synWa (.classMem (.cv z) D) (.classEq (synCun (synCin D
                      (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
                    (synCsn (.cv y))) (synCin D
                    (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z))))))
              (.classMem (.cv v) E)) (.classEq (synCun
                (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
                (synCsn (.cv u)))
              (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))))
          (.classMem (.cv y) (synCdm (synCuni (synCwecutiso R D S E))))) (.imp (synWa
            (synWa (synWa (.classMem (.cv z) D) (.classEq (synCun (synCin D
                      (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
                    (synCsn (.cv y))) (synCin D
                    (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z))))))
              (.classMem (.cv v) E)) (.classEq (synCun
                (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
                (synCsn (.cv u)))
              (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))))
          (synW3o (synWex h (synWiso (.cv h) R S D E)) (synWrex x E (synWex h
                (synWiso (.cv h) R (synCin S (synCxp (synCin E
                        (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv x))))
                      (synCin E
                        (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv x)))))) D
                  (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv x)))))))
            (synWrex x D (synWex h (synWiso (.cv h) S (synCin R (synCxp (synCin D
                        (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
                      (synCin D
                        (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))))) E
                  (synCin D
                    (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))))))
      p0174 p0176
  have p0178 :=
    Nominal.ax1
      (.imp (.imp (synWa (synWa (synWa (.classMem (.cv z) D) (.classEq (synCun (synCin D
                      (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
                    (synCsn (.cv y))) (synCin D
                    (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z))))))
              (.classMem (.cv v) E)) (.classEq (synCun
                (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
                (synCsn (.cv u)))
              (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))))
          (.classMem (.cv y) (synCdm (synCuni (synCwecutiso R D S E))))) (.imp (synWa
            (synWa (synWa (.classMem (.cv z) D) (.classEq (synCun (synCin D
                      (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
                    (synCsn (.cv y))) (synCin D
                    (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z))))))
              (.classMem (.cv v) E)) (.classEq (synCun
                (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
                (synCsn (.cv u)))
              (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))))
          (synW3o (synWex h (synWiso (.cv h) R S D E)) (synWrex x E (synWex h
                (synWiso (.cv h) R (synCin S (synCxp (synCin E
                        (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv x))))
                      (synCin E
                        (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv x)))))) D
                  (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv x)))))))
            (synWrex x D (synWex h (synWiso (.cv h) S (synCin R (synCxp (synCin D
                        (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
                      (synCin D
                        (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))))) E
                  (synCin D
                    (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))))))
      (synWiso
        (synCun (synCuni (synCwecutiso R D S E)) (synCsn (synCop (.cv y) (.cv u)))) R S
        (synCun (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
          (synCsn (.cv y))) (synCun
          (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
          (synCsn (.cv u))))
  have p0179 :=
    @gA1i
      (.imp (.imp (.imp (synWa (synWa (synWa (.classMem (.cv z) D) (.classEq (synCun
                      (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
                      (synCsn (.cv y))) (synCin D
                      (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z))))))
                (.classMem (.cv v) E)) (.classEq (synCun (synCin E
                    (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
                  (synCsn (.cv u))) (synCin E
                  (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))))
            (.classMem (.cv y) (synCdm (synCuni (synCwecutiso R D S E))))) (.imp (synWa
              (synWa (synWa (.classMem (.cv z) D) (.classEq (synCun (synCin D
                        (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
                      (synCsn (.cv y))) (synCin D
                      (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z))))))
                (.classMem (.cv v) E)) (.classEq (synCun (synCin E
                    (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
                  (synCsn (.cv u))) (synCin E
                  (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))))
            (synW3o (synWex h (synWiso (.cv h) R S D E)) (synWrex x E (synWex h
                  (synWiso (.cv h) R (synCin S (synCxp (synCin E
                          (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv x))))
                        (synCin E (synCima (synCcnv (synCdif S (synCid)))
                            (synCsn (.cv x)))))) D (synCin E
                      (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv x)))))))
              (synWrex x D (synWex h (synWiso (.cv h) S (synCin R (synCxp (synCin D
                          (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
                        (synCin D (synCima (synCcnv (synCdif R (synCid)))
                            (synCsn (.cv x)))))) E (synCin D
                      (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))))))
        (.imp (synWiso (synCun (synCuni (synCwecutiso R D S E))
              (synCsn (synCop (.cv y) (.cv u)))) R S (synCun
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
              (synCsn (.cv y))) (synCun
              (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
              (synCsn (.cv u)))) (.imp (.imp (synWa (synWa (synWa (.classMem (.cv z) D)
                    (.classEq (synCun (synCin D
                          (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
                        (synCsn (.cv y))) (synCin D
                        (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z))))))
                  (.classMem (.cv v) E)) (.classEq (synCun (synCin E
                      (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
                    (synCsn (.cv u))) (synCin E
                    (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))))
              (.classMem (.cv y) (synCdm (synCuni (synCwecutiso R D S E))))) (.imp (synWa
                (synWa (synWa (.classMem (.cv z) D) (.classEq (synCun (synCin D
                          (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
                        (synCsn (.cv y))) (synCin D
                        (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z))))))
                  (.classMem (.cv v) E)) (.classEq (synCun (synCin E
                      (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
                    (synCsn (.cv u))) (synCin E
                    (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))))
              (synW3o (synWex h (synWiso (.cv h) R S D E)) (synWrex x E (synWex h
                    (synWiso (.cv h) R (synCin S (synCxp (synCin E
                            (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv x))))
                          (synCin E (synCima (synCcnv (synCdif S (synCid)))
                              (synCsn (.cv x)))))) D (synCin E
                        (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv x)))))))
                (synWrex x D (synWex h (synWiso (.cv h) S (synCin R (synCxp (synCin D
                            (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
                          (synCin D (synCima (synCcnv (synCdif R (synCid)))
                              (synCsn (.cv x)))))) E (synCin D
                        (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))))))))
      (.neg (.classMem (.cv y) (synCdm (synCuni (synCwecutiso R D S E))))) p0178
  have p0180 :=
    @gMpd (.neg (.classMem (.cv y) (synCdm (synCuni (synCwecutiso R D S E)))))
      (.imp (.imp (synWa (synWa (synWa (.classMem (.cv z) D) (.classEq (synCun (synCin D
                      (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
                    (synCsn (.cv y))) (synCin D
                    (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z))))))
              (.classMem (.cv v) E)) (.classEq (synCun
                (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
                (synCsn (.cv u)))
              (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))))
          (.classMem (.cv y) (synCdm (synCuni (synCwecutiso R D S E))))) (.imp (synWa
            (synWa (synWa (.classMem (.cv z) D) (.classEq (synCun (synCin D
                      (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
                    (synCsn (.cv y))) (synCin D
                    (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z))))))
              (.classMem (.cv v) E)) (.classEq (synCun
                (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
                (synCsn (.cv u)))
              (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))))
          (synW3o (synWex h (synWiso (.cv h) R S D E)) (synWrex x E (synWex h
                (synWiso (.cv h) R (synCin S (synCxp (synCin E
                        (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv x))))
                      (synCin E
                        (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv x)))))) D
                  (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv x)))))))
            (synWrex x D (synWex h (synWiso (.cv h) S (synCin R (synCxp (synCin D
                        (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
                      (synCin D
                        (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))))) E
                  (synCin D
                    (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))))))
      (.imp (synWiso
          (synCun (synCuni (synCwecutiso R D S E)) (synCsn (synCop (.cv y) (.cv u)))) R S
          (synCun (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
            (synCsn (.cv y))) (synCun
            (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
            (synCsn (.cv u)))) (.imp (.imp (synWa (synWa (synWa (.classMem (.cv z) D)
                  (.classEq (synCun (synCin D
                        (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
                      (synCsn (.cv y))) (synCin D
                      (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z))))))
                (.classMem (.cv v) E)) (.classEq (synCun (synCin E
                    (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
                  (synCsn (.cv u))) (synCin E
                  (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))))
            (.classMem (.cv y) (synCdm (synCuni (synCwecutiso R D S E))))) (.imp (synWa
              (synWa (synWa (.classMem (.cv z) D) (.classEq (synCun (synCin D
                        (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
                      (synCsn (.cv y))) (synCin D
                      (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z))))))
                (.classMem (.cv v) E)) (.classEq (synCun (synCin E
                    (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
                  (synCsn (.cv u))) (synCin E
                  (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))))
            (synW3o (synWex h (synWiso (.cv h) R S D E)) (synWrex x E (synWex h
                  (synWiso (.cv h) R (synCin S (synCxp (synCin E
                          (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv x))))
                        (synCin E (synCima (synCcnv (synCdif S (synCid)))
                            (synCsn (.cv x)))))) D (synCin E
                      (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv x)))))))
              (synWrex x D (synWex h (synWiso (.cv h) S (synCin R (synCxp (synCin D
                          (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
                        (synCin D (synCima (synCcnv (synCdif R (synCid)))
                            (synCsn (.cv x)))))) E (synCin D
                      (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))))))))))
      p0177 p0179
  have p0181 :=
    Nominal.ax2
      (synWiso
        (synCun (synCuni (synCwecutiso R D S E)) (synCsn (synCop (.cv y) (.cv u)))) R S
        (synCun (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
          (synCsn (.cv y))) (synCun
          (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
          (synCsn (.cv u))))
      (.imp (synWa (synWa (synWa (.classMem (.cv z) D) (.classEq (synCun (synCin D
                    (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
                  (synCsn (.cv y))) (synCin D
                  (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z))))))
            (.classMem (.cv v) E)) (.classEq (synCun
              (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
              (synCsn (.cv u)))
            (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))))
        (.classMem (.cv y) (synCdm (synCuni (synCwecutiso R D S E)))))
      (.imp (synWa (synWa (synWa (.classMem (.cv z) D) (.classEq (synCun (synCin D
                    (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
                  (synCsn (.cv y))) (synCin D
                  (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z))))))
            (.classMem (.cv v) E)) (.classEq (synCun
              (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
              (synCsn (.cv u)))
            (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))))
        (synW3o (synWex h (synWiso (.cv h) R S D E)) (synWrex x E (synWex h
              (synWiso (.cv h) R (synCin S (synCxp (synCin E
                      (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv x)))) (synCin E
                      (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv x)))))) D
                (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv x)))))))
          (synWrex x D (synWex h (synWiso (.cv h) S (synCin R (synCxp (synCin D
                      (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))) (synCin D
                      (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))))) E
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))))))))
  have p0182 :=
    @gA1i
      (.imp (.imp (synWiso (synCun (synCuni (synCwecutiso R D S E))
              (synCsn (synCop (.cv y) (.cv u)))) R S (synCun
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
              (synCsn (.cv y))) (synCun
              (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
              (synCsn (.cv u)))) (.imp (.imp (synWa (synWa (synWa (.classMem (.cv z) D)
                    (.classEq (synCun (synCin D
                          (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
                        (synCsn (.cv y))) (synCin D
                        (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z))))))
                  (.classMem (.cv v) E)) (.classEq (synCun (synCin E
                      (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
                    (synCsn (.cv u))) (synCin E
                    (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))))
              (.classMem (.cv y) (synCdm (synCuni (synCwecutiso R D S E))))) (.imp (synWa
                (synWa (synWa (.classMem (.cv z) D) (.classEq (synCun (synCin D
                          (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
                        (synCsn (.cv y))) (synCin D
                        (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z))))))
                  (.classMem (.cv v) E)) (.classEq (synCun (synCin E
                      (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
                    (synCsn (.cv u))) (synCin E
                    (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))))
              (synW3o (synWex h (synWiso (.cv h) R S D E)) (synWrex x E (synWex h
                    (synWiso (.cv h) R (synCin S (synCxp (synCin E
                            (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv x))))
                          (synCin E (synCima (synCcnv (synCdif S (synCid)))
                              (synCsn (.cv x)))))) D (synCin E
                        (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv x)))))))
                (synWrex x D (synWex h (synWiso (.cv h) S (synCin R (synCxp (synCin D
                            (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
                          (synCin D (synCima (synCcnv (synCdif R (synCid)))
                              (synCsn (.cv x)))))) E (synCin D
                        (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))))))))))
        (.imp (.imp (synWiso (synCun (synCuni (synCwecutiso R D S E))
                (synCsn (synCop (.cv y) (.cv u)))) R S (synCun
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
                (synCsn (.cv y))) (synCun
                (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
                (synCsn (.cv u)))) (.imp (synWa (synWa (synWa (.classMem (.cv z) D)
                    (.classEq (synCun (synCin D
                          (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
                        (synCsn (.cv y))) (synCin D
                        (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z))))))
                  (.classMem (.cv v) E)) (.classEq (synCun (synCin E
                      (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
                    (synCsn (.cv u))) (synCin E
                    (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))))
              (.classMem (.cv y) (synCdm (synCuni (synCwecutiso R D S E)))))) (.imp (synWiso
              (synCun (synCuni (synCwecutiso R D S E)) (synCsn (synCop (.cv y) (.cv u))))
              R S (synCun
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
                (synCsn (.cv y))) (synCun
                (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
                (synCsn (.cv u)))) (.imp (synWa (synWa (synWa (.classMem (.cv z) D)
                    (.classEq (synCun (synCin D
                          (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
                        (synCsn (.cv y))) (synCin D
                        (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z))))))
                  (.classMem (.cv v) E)) (.classEq (synCun (synCin E
                      (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
                    (synCsn (.cv u))) (synCin E
                    (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))))
              (synW3o (synWex h (synWiso (.cv h) R S D E)) (synWrex x E (synWex h
                    (synWiso (.cv h) R (synCin S (synCxp (synCin E
                            (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv x))))
                          (synCin E (synCima (synCcnv (synCdif S (synCid)))
                              (synCsn (.cv x)))))) D (synCin E
                        (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv x)))))))
                (synWrex x D (synWex h (synWiso (.cv h) S (synCin R (synCxp (synCin D
                            (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
                          (synCin D (synCima (synCcnv (synCdif R (synCid)))
                              (synCsn (.cv x)))))) E (synCin D
                        (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))))))))
      (.neg (.classMem (.cv y) (synCdm (synCuni (synCwecutiso R D S E))))) p0181
  have p0183 :=
    @gMpd (.neg (.classMem (.cv y) (synCdm (synCuni (synCwecutiso R D S E)))))
      (.imp (synWiso
          (synCun (synCuni (synCwecutiso R D S E)) (synCsn (synCop (.cv y) (.cv u)))) R S
          (synCun (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
            (synCsn (.cv y))) (synCun
            (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
            (synCsn (.cv u)))) (.imp (.imp (synWa (synWa (synWa (.classMem (.cv z) D)
                  (.classEq (synCun (synCin D
                        (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
                      (synCsn (.cv y))) (synCin D
                      (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z))))))
                (.classMem (.cv v) E)) (.classEq (synCun (synCin E
                    (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
                  (synCsn (.cv u))) (synCin E
                  (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))))
            (.classMem (.cv y) (synCdm (synCuni (synCwecutiso R D S E))))) (.imp (synWa
              (synWa (synWa (.classMem (.cv z) D) (.classEq (synCun (synCin D
                        (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
                      (synCsn (.cv y))) (synCin D
                      (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z))))))
                (.classMem (.cv v) E)) (.classEq (synCun (synCin E
                    (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
                  (synCsn (.cv u))) (synCin E
                  (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))))
            (synW3o (synWex h (synWiso (.cv h) R S D E)) (synWrex x E (synWex h
                  (synWiso (.cv h) R (synCin S (synCxp (synCin E
                          (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv x))))
                        (synCin E (synCima (synCcnv (synCdif S (synCid)))
                            (synCsn (.cv x)))))) D (synCin E
                      (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv x)))))))
              (synWrex x D (synWex h (synWiso (.cv h) S (synCin R (synCxp (synCin D
                          (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
                        (synCin D (synCima (synCcnv (synCdif R (synCid)))
                            (synCsn (.cv x)))))) E (synCin D
                      (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))))))))))
      (.imp (.imp (synWiso (synCun (synCuni (synCwecutiso R D S E))
              (synCsn (synCop (.cv y) (.cv u)))) R S (synCun
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
              (synCsn (.cv y))) (synCun
              (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
              (synCsn (.cv u)))) (.imp (synWa (synWa (synWa (.classMem (.cv z) D) (.classEq
                    (synCun (synCin D
                        (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
                      (synCsn (.cv y))) (synCin D
                      (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z))))))
                (.classMem (.cv v) E)) (.classEq (synCun (synCin E
                    (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
                  (synCsn (.cv u))) (synCin E
                  (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))))
            (.classMem (.cv y) (synCdm (synCuni (synCwecutiso R D S E)))))) (.imp (synWiso
            (synCun (synCuni (synCwecutiso R D S E)) (synCsn (synCop (.cv y) (.cv u)))) R S
            (synCun (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
              (synCsn (.cv y))) (synCun
              (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
              (synCsn (.cv u)))) (.imp (synWa (synWa (synWa (.classMem (.cv z) D) (.classEq
                    (synCun (synCin D
                        (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
                      (synCsn (.cv y))) (synCin D
                      (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z))))))
                (.classMem (.cv v) E)) (.classEq (synCun (synCin E
                    (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
                  (synCsn (.cv u))) (synCin E
                  (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))))
            (synW3o (synWex h (synWiso (.cv h) R S D E)) (synWrex x E (synWex h
                  (synWiso (.cv h) R (synCin S (synCxp (synCin E
                          (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv x))))
                        (synCin E (synCima (synCcnv (synCdif S (synCid)))
                            (synCsn (.cv x)))))) D (synCin E
                      (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv x)))))))
              (synWrex x D (synWex h (synWiso (.cv h) S (synCin R (synCxp (synCin D
                          (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
                        (synCin D (synCima (synCcnv (synCdif R (synCid)))
                            (synCsn (.cv x)))))) E (synCin D
                      (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))))))))))
      p0180 p0182
  have p0184 :=
    @gMpd (.neg (.classMem (.cv y) (synCdm (synCuni (synCwecutiso R D S E)))))
      (.imp (synWiso
          (synCun (synCuni (synCwecutiso R D S E)) (synCsn (synCop (.cv y) (.cv u)))) R S
          (synCun (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
            (synCsn (.cv y))) (synCun
            (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
            (synCsn (.cv u)))) (.imp (synWa (synWa (synWa (.classMem (.cv z) D) (.classEq
                  (synCun (synCin D
                      (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
                    (synCsn (.cv y))) (synCin D
                    (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z))))))
              (.classMem (.cv v) E)) (.classEq (synCun
                (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
                (synCsn (.cv u)))
              (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))))
          (.classMem (.cv y) (synCdm (synCuni (synCwecutiso R D S E))))))
      (.imp (synWiso
          (synCun (synCuni (synCwecutiso R D S E)) (synCsn (synCop (.cv y) (.cv u)))) R S
          (synCun (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
            (synCsn (.cv y))) (synCun
            (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
            (synCsn (.cv u)))) (.imp (synWa (synWa (synWa (.classMem (.cv z) D) (.classEq
                  (synCun (synCin D
                      (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
                    (synCsn (.cv y))) (synCin D
                    (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z))))))
              (.classMem (.cv v) E)) (.classEq (synCun
                (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
                (synCsn (.cv u)))
              (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))))
          (synW3o (synWex h (synWiso (.cv h) R S D E)) (synWrex x E (synWex h
                (synWiso (.cv h) R (synCin S (synCxp (synCin E
                        (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv x))))
                      (synCin E
                        (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv x)))))) D
                  (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv x)))))))
            (synWrex x D (synWex h (synWiso (.cv h) S (synCin R (synCxp (synCin D
                        (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
                      (synCin D
                        (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))))) E
                  (synCin D
                    (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))))))
      p0160 p0183
  exact p0184


end NFChoice.DirectNominalPrf.WPPReplay
