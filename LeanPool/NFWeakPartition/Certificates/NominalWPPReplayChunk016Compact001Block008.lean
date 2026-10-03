/-
Copyright (c) 2026 Elliot Glazer and NFNotWPP contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elliot Glazer and NFNotWPP contributors
-/

module

public import LeanPool.NFWeakPartition.NominalWPPReplayChunk016Compact001Part034

/-! Nominal proof certificates grouped in dependency order. -/


public section

/-! Certificates from `NominalWPPReplayChunk016Compact001Part035`. -/


section

namespace NFChoice.DirectNominalPrf.WPPReplay

open scoped Fol
open NFChoice.Foundation
open NFChoice.SemanticCore
open NFChoice.ReplaySupport
open NFChoice.Compiler.CompactSourceSyntax

@[expose]
noncomputable def g_wecutisoextendedterminaldfdv (x : Var) (y : Var) (u : Var) (D : Class)
    (R : Class) (S : Class) (h : Var) (E : Class) (dv_D_h : h ∉ D.fv) (dv_D_u : u ∉ D.fv)
    (dv_D_x : x ∉ D.fv) (dv_D_y : y ∉ D.fv) (dv_E_h : h ∉ E.fv) (dv_E_u : u ∉ E.fv)
    (dv_E_x : x ∉ E.fv) (dv_E_y : y ∉ E.fv) (dv_R_h : h ∉ R.fv) (dv_R_u : u ∉ R.fv)
    (dv_R_x : x ∉ R.fv) (dv_R_y : y ∉ R.fv) (dv_S_h : h ∉ S.fv) (dv_S_u : u ∉ S.fv)
    (dv_S_x : x ∉ S.fv) (dv_S_y : y ∉ S.fv) (dv_h_u : h ≠ u) (dv_h_x : h ≠ x)
    (dv_h_y : h ≠ y) (dv_u_x : u ≠ x) (dv_u_y : u ≠ y) (dv_x_y : x ≠ y)
    (hyp_wecutisoextendedterminaldfdv_1 : Nominal.NPrf (syn_wbr R (syn_cwe) D))
    (hyp_wecutisoextendedterminaldfdv_2 : Nominal.NPrf (syn_wbr S (syn_cwe) E))
    (hyp_wecutisoextendedterminaldfdv_3 :
      Nominal.NPrf (.classMem (syn_cuni (syn_cwecutiso R D S E)) (syn_cvv))) :
    Nominal.NPrf
      (.imp (syn_wa (syn_wa (.classMem (.cv y) D) (.classMem (.cv u) E))
          (syn_wa (.neg (.classMem (.cv y) (syn_cdm (syn_cuni (syn_cwecutiso R D S E)))))
            (syn_wiso (syn_cun (syn_cuni (syn_cwecutiso R D S E))
                (syn_csn (syn_cop (.cv y) (.cv u)))) R S (syn_cun
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
                (syn_csn (.cv y))) (syn_cun
                (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))
                (syn_csn (.cv u)))))) (syn_w3o (syn_wex h (syn_wiso (.cv h) R S D E))
          (syn_wrex x E (syn_wex h (syn_wiso (.cv h) R (syn_cin S (syn_cxp (syn_cin E
                      (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv x)))) (syn_cin E
                      (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv x)))))) D
                (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv x)))))))
          (syn_wrex x D (syn_wex h (syn_wiso (.cv h) S (syn_cin R (syn_cxp (syn_cin D
                      (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D
                      (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) E
                (syn_cin D
                  (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))))) :=
  by
  let proofSupport : Finset Var :=
    ({ x } : Finset Var) ∪ ({ y } : Finset Var) ∪ ({ u } : Finset Var) ∪ D.fv ∪ R.fv ∪
          S.fv ∪
        ({ h } : Finset Var) ∪
      E.fv
  let z : Var := freshVar proofSupport 0
  let v : Var := freshVar proofSupport 1
  have fresh_z : z ∉ proofSupport :=
    by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_z_ne_x : z ≠ x := by
    intro h
    exact
      fresh_z
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _
              (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _
                    (Finset.mem_union_left _ (Finset.mem_singleton.mpr h))))))))
  have fresh_x_ne_z : x ≠ z := Ne.symm fresh_z_ne_x
  have fresh_z_ne_y : z ≠ y := by
    intro h
    exact
      fresh_z
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _
              (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _
                    (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))))))))
  have fresh_y_ne_z : y ≠ z := Ne.symm fresh_z_ne_y
  have fresh_z_ne_u : z ≠ u := by
    intro h
    exact
      fresh_z
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _
              (Finset.mem_union_left _ (Finset.mem_union_left _
                  (Finset.mem_union_right _ (Finset.mem_singleton.mpr h)))))))
  have fresh_u_ne_z : u ≠ z := Ne.symm fresh_z_ne_u
  have fresh_z_not_D : z ∉ D.fv := by
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
  have fresh_z_not_S : z ∉ S.fv := by
    intro h
    exact
      fresh_z
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))
  have fresh_z_ne_h : z ≠ h := by
    intro h
    exact
      fresh_z
        (Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_singleton.mpr h)))
  have fresh_h_ne_z : h ≠ z := Ne.symm fresh_z_ne_h
  have fresh_z_not_E : z ∉ E.fv := by
    intro h
    exact fresh_z (Finset.mem_union_right _ (h))
  have fresh_v : v ∉ proofSupport :=
    by
    change freshVar proofSupport 1 ∉ proofSupport
    exact freshVar_not_mem proofSupport 1
  have fresh_v_ne_x : v ≠ x := by
    intro h
    exact
      fresh_v
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _
              (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _
                    (Finset.mem_union_left _ (Finset.mem_singleton.mpr h))))))))
  have fresh_v_ne_y : v ≠ y := by
    intro h
    exact
      fresh_v
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _
              (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _
                    (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))))))))
  have fresh_v_ne_u : v ≠ u := by
    intro h
    exact
      fresh_v
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _
              (Finset.mem_union_left _ (Finset.mem_union_left _
                  (Finset.mem_union_right _ (Finset.mem_singleton.mpr h)))))))
  have fresh_u_ne_v : u ≠ v := Ne.symm fresh_v_ne_u
  have fresh_v_not_D : v ∉ D.fv := by
    intro h
    exact
      fresh_v
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _
              (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))))
  have fresh_v_not_R : v ∉ R.fv := by
    intro h
    exact
      fresh_v
        (Finset.mem_union_left _ (Finset.mem_union_left _
            (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))))
  have fresh_v_not_S : v ∉ S.fv := by
    intro h
    exact
      fresh_v
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))
  have fresh_v_ne_h : v ≠ h := by
    intro h
    exact
      fresh_v
        (Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_singleton.mpr h)))
  have fresh_h_ne_v : h ≠ v := Ne.symm fresh_v_ne_h
  have fresh_v_not_E : v ∉ E.fv := by
    intro h
    exact fresh_v (Finset.mem_union_right _ (h))
  have fresh_z_ne_v : z ≠ v :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have fresh_v_ne_z : v ≠ z := Ne.symm fresh_z_ne_v
  have dv_cache_0001 : z ∉ (D).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_z_not_D, not_false_eq_true])
  have dv_cache_0002 : z ∉ (R).fv :=
    by
    clear dv_cache_0001
    exact
      (by
        have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_z_not_R, not_false_eq_true])
  have dv_cache_0003 : y ≠ z :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact (show y ≠ z from (by exact fresh_y_ne_z))
  have dv_cache_0004 : v ∉ (E).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact
      (by
        have compact_fv_not_mem_empty : v ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_v_not_E, not_false_eq_true])
  have dv_cache_0005 : v ∉ (S).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact
      (by
        have compact_fv_not_mem_empty : v ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_v_not_S, not_false_eq_true])
  have dv_cache_0006 : u ≠ v :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact (show u ≠ v from (by exact fresh_u_ne_v))
  have dv_cache_0007 : h ∉ (D).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006
    exact
      (by
        have compact_fv_not_mem_empty : h ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_D_h, not_false_eq_true])
  have dv_cache_0008 : u ∉ (D).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007
    exact
      (by
        have compact_fv_not_mem_empty : u ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_D_u, not_false_eq_true])
  have dv_cache_0009 : x ∉ (D).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_D_x, not_false_eq_true])
  have dv_cache_0010 : y ∉ (D).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_D_y, not_false_eq_true])
  have dv_cache_0011 : h ∉ (E).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010
    exact
      (by
        have compact_fv_not_mem_empty : h ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_E_h, not_false_eq_true])
  have dv_cache_0012 : u ∉ (E).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
    exact
      (by
        have compact_fv_not_mem_empty : u ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_E_u, not_false_eq_true])
  have dv_cache_0013 : x ∉ (E).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_E_x, not_false_eq_true])
  have dv_cache_0014 : y ∉ (E).fv :=
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
        simp only [dv_E_y, not_false_eq_true])
  have dv_cache_0015 : h ∉ (R).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014
    exact
      (by
        have compact_fv_not_mem_empty : h ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_R_h, not_false_eq_true])
  have dv_cache_0016 : u ∉ (R).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015
    exact
      (by
        have compact_fv_not_mem_empty : u ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_R_u, not_false_eq_true])
  have dv_cache_0017 : x ∉ (R).fv :=
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
        simp only [dv_R_x, not_false_eq_true])
  have dv_cache_0018 : y ∉ (R).fv :=
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
        simp only [dv_R_y, not_false_eq_true])
  have dv_cache_0019 : h ∉ (S).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018
    exact
      (by
        have compact_fv_not_mem_empty : h ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_S_h, not_false_eq_true])
  have dv_cache_0020 : u ∉ (S).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019
    exact
      (by
        have compact_fv_not_mem_empty : u ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_S_u, not_false_eq_true])
  have dv_cache_0021 : x ∉ (S).fv :=
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
        simp only [dv_S_x, not_false_eq_true])
  have dv_cache_0022 : y ∉ (S).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_S_y, not_false_eq_true])
  have dv_cache_0023 : h ≠ u :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022
    exact (show h ≠ u from (by exact dv_h_u))
  have dv_cache_0024 : h ≠ x :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
    exact (show h ≠ x from (by exact dv_h_x))
  have dv_cache_0025 : h ≠ y :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024
    exact (show h ≠ y from (by exact dv_h_y))
  have dv_cache_0026 : u ≠ x :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025
    exact (show u ≠ x from (by exact dv_u_x))
  have dv_cache_0027 : u ≠ y :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026
    exact (show u ≠ y from (by exact dv_u_y))
  have dv_cache_0028 : x ≠ y :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027
    exact (show x ≠ y from (by exact dv_x_y))
  have dv_cache_0029 : v ∉ (D).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028
    exact
      (by
        have compact_fv_not_mem_empty : v ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_v_not_D, not_false_eq_true])
  have dv_cache_0030 : v ∉ (R).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
    exact
      (by
        have compact_fv_not_mem_empty : v ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_v_not_R, not_false_eq_true])
  have dv_cache_0031 : h ≠ v :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
      dv_cache_0030
    exact (show h ≠ v from (by exact fresh_h_ne_v))
  have dv_cache_0032 : v ≠ x :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
      dv_cache_0030 dv_cache_0031
    exact (show v ≠ x from (by exact fresh_v_ne_x))
  have dv_cache_0033 : v ≠ y :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
      dv_cache_0030 dv_cache_0031 dv_cache_0032
    exact (show v ≠ y from (by exact fresh_v_ne_y))
  have dv_cache_0034 :
    v ∉
      ((syn_w3o (syn_wex h (syn_wiso (.cv h) R S D E)) (syn_wrex x E (syn_wex h
              (syn_wiso (.cv h) R (syn_cin S (syn_cxp (syn_cin E
                      (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv x)))) (syn_cin E
                      (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv x)))))) D
                (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv x)))))))
          (syn_wrex x D (syn_wex h (syn_wiso (.cv h) S (syn_cin R (syn_cxp (syn_cin D
                      (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D
                      (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) E
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
                    (syn_csn (.cv x))))))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
      dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033
    exact
      (by
        have compact_fv_not_mem_empty : v ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_w3o,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wex,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_wiso,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wrex,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxp,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cima,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdif,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cid,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, Finset.mem_union,
          Finset.mem_erase, Finset.mem_singleton, fresh_v_not_D, fresh_v_not_E,
          fresh_v_not_R, fresh_v_ne_x, fresh_v_ne_h, fresh_v_not_S,
          compact_fv_not_mem_empty, or_false, and_false, not_false_eq_true])
  have dv_cache_0035 :
    v ∉
      ((syn_wa (syn_wa (syn_wa (.classMem (.cv y) D) (.classMem (.cv u) E)) (syn_wa
              (.neg (.classMem (.cv y) (syn_cdm (syn_cuni (syn_cwecutiso R D S E))))) (syn_wiso
                (syn_cun (syn_cuni (syn_cwecutiso R D S E)) (syn_csn (syn_cop (.cv y) (.cv u))))
                R S (syn_cun (syn_cin D
                    (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
                  (syn_csn (.cv y))) (syn_cun (syn_cin E
                    (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))
                  (syn_csn (.cv u)))))) (.classEq (syn_cun
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
              (syn_csn (.cv y))) D))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
      dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034
    exact
      (by
        have compact_fv_not_mem_empty : v ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CoreFVSimp.fv_wff_neg,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdm,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cuni,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwecutiso,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_wiso,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cun,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cop,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cima,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdif,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cid,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, Finset.mem_union,
          Finset.mem_singleton, fresh_v_ne_y, fresh_v_not_D, fresh_v_ne_u, fresh_v_not_E,
          fresh_v_not_R, fresh_v_not_S, compact_fv_not_mem_empty, or_false,
          not_false_eq_true])
  have dv_cache_0036 : z ∉ (E).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
      dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035
    exact
      (by
        have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_z_not_E, not_false_eq_true])
  have dv_cache_0037 : z ∉ (S).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
      dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035
      dv_cache_0036
    exact
      (by
        have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_z_not_S, not_false_eq_true])
  have dv_cache_0038 : h ≠ z :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
      dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035
      dv_cache_0036 dv_cache_0037
    exact (show h ≠ z from (by exact fresh_h_ne_z))
  have dv_cache_0039 : u ≠ z :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
      dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035
      dv_cache_0036 dv_cache_0037 dv_cache_0038
    exact (show u ≠ z from (by exact fresh_u_ne_z))
  have dv_cache_0040 : x ≠ z :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
      dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035
      dv_cache_0036 dv_cache_0037 dv_cache_0038 dv_cache_0039
    exact (show x ≠ z from (by exact fresh_x_ne_z))
  have dv_cache_0041 : v ≠ z :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
      dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035
      dv_cache_0036 dv_cache_0037 dv_cache_0038 dv_cache_0039 dv_cache_0040
    exact (show v ≠ z from (by exact fresh_v_ne_z))
  have dv_cache_0042 :
    v ∉
      ((syn_wa (syn_wa (syn_wa (.classMem (.cv y) D) (.classMem (.cv u) E)) (syn_wa
              (.neg (.classMem (.cv y) (syn_cdm (syn_cuni (syn_cwecutiso R D S E))))) (syn_wiso
                (syn_cun (syn_cuni (syn_cwecutiso R D S E)) (syn_csn (syn_cop (.cv y) (.cv u))))
                R S (syn_cun (syn_cin D
                    (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
                  (syn_csn (.cv y))) (syn_cun (syn_cin E
                    (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))
                  (syn_csn (.cv u)))))) (syn_wa (.classMem (.cv z) D) (.classEq (syn_cun
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
                (syn_csn (.cv y))) (syn_cin D
                (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv z)))))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
      dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035
      dv_cache_0036 dv_cache_0037 dv_cache_0038 dv_cache_0039 dv_cache_0040 dv_cache_0041
    exact
      (by
        have compact_fv_not_mem_empty : v ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CoreFVSimp.fv_wff_neg,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdm,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cuni,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwecutiso,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_wiso,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cun,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cop,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cima,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdif,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cid,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, Finset.mem_union,
          Finset.mem_singleton, fresh_v_ne_y, fresh_v_not_D, fresh_v_ne_u, fresh_v_not_E,
          fresh_v_not_R, fresh_v_not_S, fresh_v_ne_z, compact_fv_not_mem_empty, or_false,
          not_false_eq_true])
  have dv_cache_0043 :
    z ∉
      ((syn_w3o (syn_wex h (syn_wiso (.cv h) R S D E)) (syn_wrex x E (syn_wex h
              (syn_wiso (.cv h) R (syn_cin S (syn_cxp (syn_cin E
                      (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv x)))) (syn_cin E
                      (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv x)))))) D
                (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv x)))))))
          (syn_wrex x D (syn_wex h (syn_wiso (.cv h) S (syn_cin R (syn_cxp (syn_cin D
                      (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D
                      (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) E
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
                    (syn_csn (.cv x))))))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
      dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035
      dv_cache_0036 dv_cache_0037 dv_cache_0038 dv_cache_0039 dv_cache_0040 dv_cache_0041
      dv_cache_0042
    exact
      (by
        have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_w3o,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wex,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_wiso,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wrex,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxp,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cima,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdif,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cid,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, Finset.mem_union,
          Finset.mem_erase, Finset.mem_singleton, fresh_z_not_D, fresh_z_not_E,
          fresh_z_not_R, fresh_z_ne_x, fresh_z_ne_h, fresh_z_not_S,
          compact_fv_not_mem_empty, or_false, and_false, not_false_eq_true])
  have dv_cache_0044 :
    z ∉
      ((syn_wa (syn_wa (.classMem (.cv y) D) (.classMem (.cv u) E))
          (syn_wa (.neg (.classMem (.cv y) (syn_cdm (syn_cuni (syn_cwecutiso R D S E)))))
            (syn_wiso (syn_cun (syn_cuni (syn_cwecutiso R D S E))
                (syn_csn (syn_cop (.cv y) (.cv u)))) R S (syn_cun
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
                (syn_csn (.cv y))) (syn_cun
                (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))
                (syn_csn (.cv u))))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
      dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035
      dv_cache_0036 dv_cache_0037 dv_cache_0038 dv_cache_0039 dv_cache_0040 dv_cache_0041
      dv_cache_0042 dv_cache_0043
    exact
      (by
        have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CoreFVSimp.fv_wff_neg,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdm,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cuni,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwecutiso,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_wiso,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cun,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cop,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cima,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdif,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cid, Finset.mem_union,
          Finset.mem_singleton, fresh_z_ne_y, fresh_z_not_D, fresh_z_ne_u, fresh_z_not_E,
          fresh_z_not_R, fresh_z_not_S, compact_fv_not_mem_empty, or_false,
          not_false_eq_true])
  have p0000 :=
    @g_simpll (.classMem (.cv y) D) (.classMem (.cv u) E)
      (syn_wa (.neg (.classMem (.cv y) (syn_cdm (syn_cuni (syn_cwecutiso R D S E))))) (syn_wiso
          (syn_cun (syn_cuni (syn_cwecutiso R D S E)) (syn_csn (syn_cop (.cv y) (.cv u)))) R S
          (syn_cun (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
            (syn_csn (.cv y))) (syn_cun
            (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))
            (syn_csn (.cv u)))))
  have p0001 :=
    @g_weincsegcutorwholendv y z D R dv_cache_0001 dv_cache_0002 dv_cache_0003
      hyp_wecutisoextendedterminaldfdv_1
  have p0002 :=
    @g_syl
      (syn_wa (syn_wa (.classMem (.cv y) D) (.classMem (.cv u) E))
        (syn_wa (.neg (.classMem (.cv y) (syn_cdm (syn_cuni (syn_cwecutiso R D S E)))))
          (syn_wiso (syn_cun (syn_cuni (syn_cwecutiso R D S E))
              (syn_csn (syn_cop (.cv y) (.cv u)))) R S (syn_cun
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
              (syn_csn (.cv y))) (syn_cun
              (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))
              (syn_csn (.cv u))))))
      (.classMem (.cv y) D)
      (syn_wo (.classEq (syn_cun
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
            (syn_csn (.cv y))) D) (syn_wrex z D (.classEq (syn_cun
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
              (syn_csn (.cv y)))
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv z)))))))
      p0000 p0001
  have p0003 :=
    @g_simplr (.classMem (.cv y) D) (.classMem (.cv u) E)
      (syn_wa (.neg (.classMem (.cv y) (syn_cdm (syn_cuni (syn_cwecutiso R D S E))))) (syn_wiso
          (syn_cun (syn_cuni (syn_cwecutiso R D S E)) (syn_csn (syn_cop (.cv y) (.cv u)))) R S
          (syn_cun (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
            (syn_csn (.cv y))) (syn_cun
            (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))
            (syn_csn (.cv u)))))
  have p0004 :=
    @g_weincsegcutorwholendv u v E S dv_cache_0004 dv_cache_0005 dv_cache_0006
      hyp_wecutisoextendedterminaldfdv_2
  have p0005 :=
    @g_syl
      (syn_wa (syn_wa (.classMem (.cv y) D) (.classMem (.cv u) E))
        (syn_wa (.neg (.classMem (.cv y) (syn_cdm (syn_cuni (syn_cwecutiso R D S E)))))
          (syn_wiso (syn_cun (syn_cuni (syn_cwecutiso R D S E))
              (syn_csn (syn_cop (.cv y) (.cv u)))) R S (syn_cun
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
              (syn_csn (.cv y))) (syn_cun
              (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))
              (syn_csn (.cv u))))))
      (.classMem (.cv u) E)
      (syn_wo (.classEq (syn_cun
            (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))
            (syn_csn (.cv u))) E) (syn_wrex v E (.classEq (syn_cun
              (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))
              (syn_csn (.cv u)))
            (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v)))))))
      p0003 p0004
  have p0006 :=
    @g_a1d
      (syn_wa (syn_wa (.classMem (.cv y) D) (.classMem (.cv u) E))
        (syn_wa (.neg (.classMem (.cv y) (syn_cdm (syn_cuni (syn_cwecutiso R D S E)))))
          (syn_wiso (syn_cun (syn_cuni (syn_cwecutiso R D S E))
              (syn_csn (syn_cop (.cv y) (.cv u)))) R S (syn_cun
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
              (syn_csn (.cv y))) (syn_cun
              (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))
              (syn_csn (.cv u))))))
      (syn_wo (.classEq (syn_cun
            (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))
            (syn_csn (.cv u))) E) (syn_wrex v E (.classEq (syn_cun
              (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))
              (syn_csn (.cv u)))
            (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v)))))))
      (.classEq (syn_cun
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
          (syn_csn (.cv y))) D)
      p0005
  have p0007 :=
    @g_simprr (syn_wa (.classMem (.cv y) D) (.classMem (.cv u) E))
      (.neg (.classMem (.cv y) (syn_cdm (syn_cuni (syn_cwecutiso R D S E)))))
      (syn_wiso
        (syn_cun (syn_cuni (syn_cwecutiso R D S E)) (syn_csn (syn_cop (.cv y) (.cv u)))) R S
        (syn_cun (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
          (syn_csn (.cv y))) (syn_cun
          (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))
          (syn_csn (.cv u))))
  have p0008 :=
    @g_simprl (syn_wa (.classMem (.cv y) D) (.classMem (.cv u) E))
      (.neg (.classMem (.cv y) (syn_cdm (syn_cuni (syn_cwecutiso R D S E)))))
      (syn_wiso
        (syn_cun (syn_cuni (syn_cwecutiso R D S E)) (syn_csn (syn_cop (.cv y) (.cv u)))) R S
        (syn_cun (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
          (syn_csn (.cv y))) (syn_cun
          (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))
          (syn_csn (.cv u))))
  have p0009 :=
    @g_wecutisobranchwwknfdv x y u D R S h E dv_cache_0007 dv_cache_0008 dv_cache_0009
      dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015
      dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021
      dv_cache_0022 dv_cache_0023 dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027
      dv_cache_0028 hyp_wecutisoextendedterminaldfdv_1 hyp_wecutisoextendedterminaldfdv_2
      hyp_wecutisoextendedterminaldfdv_3
  have p0010 :=
    @g_syl
      (syn_wa (syn_wa (.classMem (.cv y) D) (.classMem (.cv u) E))
        (syn_wa (.neg (.classMem (.cv y) (syn_cdm (syn_cuni (syn_cwecutiso R D S E)))))
          (syn_wiso (syn_cun (syn_cuni (syn_cwecutiso R D S E))
              (syn_csn (syn_cop (.cv y) (.cv u)))) R S (syn_cun
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
              (syn_csn (.cv y))) (syn_cun
              (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))
              (syn_csn (.cv u))))))
      (.neg (.classMem (.cv y) (syn_cdm (syn_cuni (syn_cwecutiso R D S E)))))
      (.imp (syn_wiso
          (syn_cun (syn_cuni (syn_cwecutiso R D S E)) (syn_csn (syn_cop (.cv y) (.cv u)))) R S
          (syn_cun (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
            (syn_csn (.cv y))) (syn_cun
            (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))
            (syn_csn (.cv u)))) (.imp (syn_wa (.classEq (syn_cun
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
                (syn_csn (.cv y))) D) (.classEq (syn_cun
                (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))
                (syn_csn (.cv u))) E)) (syn_w3o (syn_wex h (syn_wiso (.cv h) R S D E))
            (syn_wrex x E (syn_wex h (syn_wiso (.cv h) R (syn_cin S (syn_cxp (syn_cin E
                        (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv x))))
                      (syn_cin E
                        (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv x)))))) D
                  (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv x)))))))
            (syn_wrex x D (syn_wex h (syn_wiso (.cv h) S (syn_cin R (syn_cxp (syn_cin D
                        (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
                      (syn_cin D
                        (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) E
                  (syn_cin D
                    (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))))))
      p0008 p0009
  have p0011 :=
    @g_mpd
      (syn_wa (syn_wa (.classMem (.cv y) D) (.classMem (.cv u) E))
        (syn_wa (.neg (.classMem (.cv y) (syn_cdm (syn_cuni (syn_cwecutiso R D S E)))))
          (syn_wiso (syn_cun (syn_cuni (syn_cwecutiso R D S E))
              (syn_csn (syn_cop (.cv y) (.cv u)))) R S (syn_cun
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
              (syn_csn (.cv y))) (syn_cun
              (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))
              (syn_csn (.cv u))))))
      (syn_wiso
        (syn_cun (syn_cuni (syn_cwecutiso R D S E)) (syn_csn (syn_cop (.cv y) (.cv u)))) R S
        (syn_cun (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
          (syn_csn (.cv y))) (syn_cun
          (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))
          (syn_csn (.cv u))))
      (.imp (syn_wa (.classEq (syn_cun
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
              (syn_csn (.cv y))) D) (.classEq (syn_cun
              (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))
              (syn_csn (.cv u))) E)) (syn_w3o (syn_wex h (syn_wiso (.cv h) R S D E))
          (syn_wrex x E (syn_wex h (syn_wiso (.cv h) R (syn_cin S (syn_cxp (syn_cin E
                      (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv x)))) (syn_cin E
                      (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv x)))))) D
                (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv x)))))))
          (syn_wrex x D (syn_wex h (syn_wiso (.cv h) S (syn_cin R (syn_cxp (syn_cin D
                      (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D
                      (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) E
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))))))
      p0007 p0010
  have p0012 :=
    @g_exp3a
      (syn_wa (syn_wa (.classMem (.cv y) D) (.classMem (.cv u) E))
        (syn_wa (.neg (.classMem (.cv y) (syn_cdm (syn_cuni (syn_cwecutiso R D S E)))))
          (syn_wiso (syn_cun (syn_cuni (syn_cwecutiso R D S E))
              (syn_csn (syn_cop (.cv y) (.cv u)))) R S (syn_cun
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
              (syn_csn (.cv y))) (syn_cun
              (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))
              (syn_csn (.cv u))))))
      (.classEq (syn_cun
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
          (syn_csn (.cv y))) D)
      (.classEq (syn_cun
          (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))
          (syn_csn (.cv u))) E)
      (syn_w3o (syn_wex h (syn_wiso (.cv h) R S D E)) (syn_wrex x E (syn_wex h
            (syn_wiso (.cv h) R (syn_cin S (syn_cxp (syn_cin E
                    (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv x)))) (syn_cin E
                    (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv x)))))) D
              (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv x)))))))
        (syn_wrex x D (syn_wex h (syn_wiso (.cv h) S (syn_cin R (syn_cxp (syn_cin D
                    (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D
                    (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) E
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))))
      p0011
  have p0013 :=
    @g_imp
      (syn_wa (syn_wa (.classMem (.cv y) D) (.classMem (.cv u) E))
        (syn_wa (.neg (.classMem (.cv y) (syn_cdm (syn_cuni (syn_cwecutiso R D S E)))))
          (syn_wiso (syn_cun (syn_cuni (syn_cwecutiso R D S E))
              (syn_csn (syn_cop (.cv y) (.cv u)))) R S (syn_cun
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
              (syn_csn (.cv y))) (syn_cun
              (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))
              (syn_csn (.cv u))))))
      (.classEq (syn_cun
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
          (syn_csn (.cv y))) D)
      (.imp (.classEq (syn_cun
            (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))
            (syn_csn (.cv u))) E) (syn_w3o (syn_wex h (syn_wiso (.cv h) R S D E)) (syn_wrex x E
            (syn_wex h (syn_wiso (.cv h) R (syn_cin S (syn_cxp (syn_cin E
                      (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv x)))) (syn_cin E
                      (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv x)))))) D
                (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv x)))))))
          (syn_wrex x D (syn_wex h (syn_wiso (.cv h) S (syn_cin R (syn_cxp (syn_cin D
                      (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D
                      (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) E
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))))))
      p0012
  have p0016 :=
    @g_wecutisobranchwcknfdv x y v u D R S h E dv_cache_0007 dv_cache_0008 dv_cache_0029
      dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0004 dv_cache_0013
      dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0030 dv_cache_0017 dv_cache_0018
      dv_cache_0019 dv_cache_0020 dv_cache_0005 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0031 dv_cache_0024 dv_cache_0025 dv_cache_0006 dv_cache_0026 dv_cache_0027
      dv_cache_0032 dv_cache_0033 dv_cache_0028 hyp_wecutisoextendedterminaldfdv_1
      hyp_wecutisoextendedterminaldfdv_2 hyp_wecutisoextendedterminaldfdv_3
  have p0017 :=
    @g_syl
      (syn_wa (syn_wa (.classMem (.cv y) D) (.classMem (.cv u) E))
        (syn_wa (.neg (.classMem (.cv y) (syn_cdm (syn_cuni (syn_cwecutiso R D S E)))))
          (syn_wiso (syn_cun (syn_cuni (syn_cwecutiso R D S E))
              (syn_csn (syn_cop (.cv y) (.cv u)))) R S (syn_cun
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
              (syn_csn (.cv y))) (syn_cun
              (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))
              (syn_csn (.cv u))))))
      (.neg (.classMem (.cv y) (syn_cdm (syn_cuni (syn_cwecutiso R D S E)))))
      (.imp (syn_wiso
          (syn_cun (syn_cuni (syn_cwecutiso R D S E)) (syn_csn (syn_cop (.cv y) (.cv u)))) R S
          (syn_cun (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
            (syn_csn (.cv y))) (syn_cun
            (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))
            (syn_csn (.cv u)))) (.imp (syn_wa (syn_wa (.classEq (syn_cun (syn_cin D
                    (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
                  (syn_csn (.cv y))) D) (.classMem (.cv v) E)) (.classEq (syn_cun
                (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))
                (syn_csn (.cv u)))
              (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v))))))
          (syn_w3o (syn_wex h (syn_wiso (.cv h) R S D E)) (syn_wrex x E (syn_wex h
                (syn_wiso (.cv h) R (syn_cin S (syn_cxp (syn_cin E
                        (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv x))))
                      (syn_cin E
                        (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv x)))))) D
                  (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv x)))))))
            (syn_wrex x D (syn_wex h (syn_wiso (.cv h) S (syn_cin R (syn_cxp (syn_cin D
                        (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
                      (syn_cin D
                        (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) E
                  (syn_cin D
                    (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))))))
      p0008 p0016
  have p0018 :=
    @g_mpd
      (syn_wa (syn_wa (.classMem (.cv y) D) (.classMem (.cv u) E))
        (syn_wa (.neg (.classMem (.cv y) (syn_cdm (syn_cuni (syn_cwecutiso R D S E)))))
          (syn_wiso (syn_cun (syn_cuni (syn_cwecutiso R D S E))
              (syn_csn (syn_cop (.cv y) (.cv u)))) R S (syn_cun
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
              (syn_csn (.cv y))) (syn_cun
              (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))
              (syn_csn (.cv u))))))
      (syn_wiso
        (syn_cun (syn_cuni (syn_cwecutiso R D S E)) (syn_csn (syn_cop (.cv y) (.cv u)))) R S
        (syn_cun (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
          (syn_csn (.cv y))) (syn_cun
          (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))
          (syn_csn (.cv u))))
      (.imp (syn_wa (syn_wa (.classEq (syn_cun
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
                (syn_csn (.cv y))) D) (.classMem (.cv v) E)) (.classEq (syn_cun
              (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))
              (syn_csn (.cv u)))
            (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v))))))
        (syn_w3o (syn_wex h (syn_wiso (.cv h) R S D E)) (syn_wrex x E (syn_wex h
              (syn_wiso (.cv h) R (syn_cin S (syn_cxp (syn_cin E
                      (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv x)))) (syn_cin E
                      (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv x)))))) D
                (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv x)))))))
          (syn_wrex x D (syn_wex h (syn_wiso (.cv h) S (syn_cin R (syn_cxp (syn_cin D
                      (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D
                      (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) E
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))))))
      p0007 p0017
  have p0019 :=
    @g_exp3a
      (syn_wa (syn_wa (.classMem (.cv y) D) (.classMem (.cv u) E))
        (syn_wa (.neg (.classMem (.cv y) (syn_cdm (syn_cuni (syn_cwecutiso R D S E)))))
          (syn_wiso (syn_cun (syn_cuni (syn_cwecutiso R D S E))
              (syn_csn (syn_cop (.cv y) (.cv u)))) R S (syn_cun
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
              (syn_csn (.cv y))) (syn_cun
              (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))
              (syn_csn (.cv u))))))
      (syn_wa (.classEq (syn_cun
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
            (syn_csn (.cv y))) D) (.classMem (.cv v) E))
      (.classEq (syn_cun
          (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))
          (syn_csn (.cv u)))
        (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v)))))
      (syn_w3o (syn_wex h (syn_wiso (.cv h) R S D E)) (syn_wrex x E (syn_wex h
            (syn_wiso (.cv h) R (syn_cin S (syn_cxp (syn_cin E
                    (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv x)))) (syn_cin E
                    (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv x)))))) D
              (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv x)))))))
        (syn_wrex x D (syn_wex h (syn_wiso (.cv h) S (syn_cin R (syn_cxp (syn_cin D
                    (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D
                    (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) E
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))))
      p0018
  have p0020 :=
    @g_exp3a
      (syn_wa (syn_wa (.classMem (.cv y) D) (.classMem (.cv u) E))
        (syn_wa (.neg (.classMem (.cv y) (syn_cdm (syn_cuni (syn_cwecutiso R D S E)))))
          (syn_wiso (syn_cun (syn_cuni (syn_cwecutiso R D S E))
              (syn_csn (syn_cop (.cv y) (.cv u)))) R S (syn_cun
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
              (syn_csn (.cv y))) (syn_cun
              (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))
              (syn_csn (.cv u))))))
      (.classEq (syn_cun
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
          (syn_csn (.cv y))) D)
      (.classMem (.cv v) E)
      (.imp (.classEq (syn_cun
            (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))
            (syn_csn (.cv u)))
          (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v)))))
        (syn_w3o (syn_wex h (syn_wiso (.cv h) R S D E)) (syn_wrex x E (syn_wex h
              (syn_wiso (.cv h) R (syn_cin S (syn_cxp (syn_cin E
                      (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv x)))) (syn_cin E
                      (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv x)))))) D
                (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv x)))))))
          (syn_wrex x D (syn_wex h (syn_wiso (.cv h) S (syn_cin R (syn_cxp (syn_cin D
                      (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D
                      (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) E
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))))))
      p0019
  have p0021 :=
    @g_imp
      (syn_wa (syn_wa (.classMem (.cv y) D) (.classMem (.cv u) E))
        (syn_wa (.neg (.classMem (.cv y) (syn_cdm (syn_cuni (syn_cwecutiso R D S E)))))
          (syn_wiso (syn_cun (syn_cuni (syn_cwecutiso R D S E))
              (syn_csn (syn_cop (.cv y) (.cv u)))) R S (syn_cun
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
              (syn_csn (.cv y))) (syn_cun
              (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))
              (syn_csn (.cv u))))))
      (.classEq (syn_cun
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
          (syn_csn (.cv y))) D)
      (.imp (.classMem (.cv v) E) (.imp (.classEq (syn_cun
              (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))
              (syn_csn (.cv u)))
            (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v)))))
          (syn_w3o (syn_wex h (syn_wiso (.cv h) R S D E)) (syn_wrex x E (syn_wex h
                (syn_wiso (.cv h) R (syn_cin S (syn_cxp (syn_cin E
                        (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv x))))
                      (syn_cin E
                        (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv x)))))) D
                  (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv x)))))))
            (syn_wrex x D (syn_wex h (syn_wiso (.cv h) S (syn_cin R (syn_cxp (syn_cin D
                        (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
                      (syn_cin D
                        (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) E
                  (syn_cin D
                    (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))))))
      p0020
  have p0022 :=
    @g_imp
      (syn_wa (syn_wa (syn_wa (.classMem (.cv y) D) (.classMem (.cv u) E))
          (syn_wa (.neg (.classMem (.cv y) (syn_cdm (syn_cuni (syn_cwecutiso R D S E)))))
            (syn_wiso (syn_cun (syn_cuni (syn_cwecutiso R D S E))
                (syn_csn (syn_cop (.cv y) (.cv u)))) R S (syn_cun
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
                (syn_csn (.cv y))) (syn_cun
                (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))
                (syn_csn (.cv u)))))) (.classEq (syn_cun
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
            (syn_csn (.cv y))) D))
      (.classMem (.cv v) E)
      (.imp (.classEq (syn_cun
            (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))
            (syn_csn (.cv u)))
          (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v)))))
        (syn_w3o (syn_wex h (syn_wiso (.cv h) R S D E)) (syn_wrex x E (syn_wex h
              (syn_wiso (.cv h) R (syn_cin S (syn_cxp (syn_cin E
                      (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv x)))) (syn_cin E
                      (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv x)))))) D
                (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv x)))))))
          (syn_wrex x D (syn_wex h (syn_wiso (.cv h) S (syn_cin R (syn_cxp (syn_cin D
                      (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D
                      (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) E
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))))))
      p0021
  have p0023 :=
    @g_rexlimdva
      (syn_wa (syn_wa (syn_wa (.classMem (.cv y) D) (.classMem (.cv u) E))
          (syn_wa (.neg (.classMem (.cv y) (syn_cdm (syn_cuni (syn_cwecutiso R D S E)))))
            (syn_wiso (syn_cun (syn_cuni (syn_cwecutiso R D S E))
                (syn_csn (syn_cop (.cv y) (.cv u)))) R S (syn_cun
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
                (syn_csn (.cv y))) (syn_cun
                (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))
                (syn_csn (.cv u)))))) (.classEq (syn_cun
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
            (syn_csn (.cv y))) D))
      (.classEq (syn_cun
          (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))
          (syn_csn (.cv u)))
        (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v)))))
      (syn_w3o (syn_wex h (syn_wiso (.cv h) R S D E)) (syn_wrex x E (syn_wex h
            (syn_wiso (.cv h) R (syn_cin S (syn_cxp (syn_cin E
                    (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv x)))) (syn_cin E
                    (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv x)))))) D
              (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv x)))))))
        (syn_wrex x D (syn_wex h (syn_wiso (.cv h) S (syn_cin R (syn_cxp (syn_cin D
                    (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D
                    (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) E
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))))
      v E dv_cache_0034 dv_cache_0035 p0022
  have p0024 :=
    @g_jaod
      (syn_wa (syn_wa (syn_wa (.classMem (.cv y) D) (.classMem (.cv u) E))
          (syn_wa (.neg (.classMem (.cv y) (syn_cdm (syn_cuni (syn_cwecutiso R D S E)))))
            (syn_wiso (syn_cun (syn_cuni (syn_cwecutiso R D S E))
                (syn_csn (syn_cop (.cv y) (.cv u)))) R S (syn_cun
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
                (syn_csn (.cv y))) (syn_cun
                (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))
                (syn_csn (.cv u)))))) (.classEq (syn_cun
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
            (syn_csn (.cv y))) D))
      (.classEq (syn_cun
          (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))
          (syn_csn (.cv u))) E)
      (syn_w3o (syn_wex h (syn_wiso (.cv h) R S D E)) (syn_wrex x E (syn_wex h
            (syn_wiso (.cv h) R (syn_cin S (syn_cxp (syn_cin E
                    (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv x)))) (syn_cin E
                    (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv x)))))) D
              (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv x)))))))
        (syn_wrex x D (syn_wex h (syn_wiso (.cv h) S (syn_cin R (syn_cxp (syn_cin D
                    (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D
                    (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) E
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))))
      (syn_wrex v E (.classEq (syn_cun
            (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))
            (syn_csn (.cv u)))
          (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v))))))
      p0013 p0023
  have p0025 :=
    @g_ex
      (syn_wa (syn_wa (.classMem (.cv y) D) (.classMem (.cv u) E))
        (syn_wa (.neg (.classMem (.cv y) (syn_cdm (syn_cuni (syn_cwecutiso R D S E)))))
          (syn_wiso (syn_cun (syn_cuni (syn_cwecutiso R D S E))
              (syn_csn (syn_cop (.cv y) (.cv u)))) R S (syn_cun
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
              (syn_csn (.cv y))) (syn_cun
              (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))
              (syn_csn (.cv u))))))
      (.classEq (syn_cun
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
          (syn_csn (.cv y))) D)
      (.imp (syn_wo (.classEq (syn_cun
              (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))
              (syn_csn (.cv u))) E) (syn_wrex v E (.classEq (syn_cun
                (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))
                (syn_csn (.cv u))) (syn_cin E
                (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v)))))))
        (syn_w3o (syn_wex h (syn_wiso (.cv h) R S D E)) (syn_wrex x E (syn_wex h
              (syn_wiso (.cv h) R (syn_cin S (syn_cxp (syn_cin E
                      (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv x)))) (syn_cin E
                      (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv x)))))) D
                (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv x)))))))
          (syn_wrex x D (syn_wex h (syn_wiso (.cv h) S (syn_cin R (syn_cxp (syn_cin D
                      (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D
                      (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) E
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))))))
      p0024
  have p0026 :=
    @g_mpdd
      (syn_wa (syn_wa (.classMem (.cv y) D) (.classMem (.cv u) E))
        (syn_wa (.neg (.classMem (.cv y) (syn_cdm (syn_cuni (syn_cwecutiso R D S E)))))
          (syn_wiso (syn_cun (syn_cuni (syn_cwecutiso R D S E))
              (syn_csn (syn_cop (.cv y) (.cv u)))) R S (syn_cun
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
              (syn_csn (.cv y))) (syn_cun
              (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))
              (syn_csn (.cv u))))))
      (.classEq (syn_cun
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
          (syn_csn (.cv y))) D)
      (syn_wo (.classEq (syn_cun
            (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))
            (syn_csn (.cv u))) E) (syn_wrex v E (.classEq (syn_cun
              (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))
              (syn_csn (.cv u)))
            (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v)))))))
      (syn_w3o (syn_wex h (syn_wiso (.cv h) R S D E)) (syn_wrex x E (syn_wex h
            (syn_wiso (.cv h) R (syn_cin S (syn_cxp (syn_cin E
                    (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv x)))) (syn_cin E
                    (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv x)))))) D
              (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv x)))))))
        (syn_wrex x D (syn_wex h (syn_wiso (.cv h) S (syn_cin R (syn_cxp (syn_cin D
                    (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D
                    (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) E
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))))
      p0006 p0025
  have p0030 :=
    @g_a1d
      (syn_wa (syn_wa (.classMem (.cv y) D) (.classMem (.cv u) E))
        (syn_wa (.neg (.classMem (.cv y) (syn_cdm (syn_cuni (syn_cwecutiso R D S E)))))
          (syn_wiso (syn_cun (syn_cuni (syn_cwecutiso R D S E))
              (syn_csn (syn_cop (.cv y) (.cv u)))) R S (syn_cun
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
              (syn_csn (.cv y))) (syn_cun
              (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))
              (syn_csn (.cv u))))))
      (syn_wo (.classEq (syn_cun
            (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))
            (syn_csn (.cv u))) E) (syn_wrex v E (.classEq (syn_cun
              (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))
              (syn_csn (.cv u)))
            (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v)))))))
      (syn_wa (.classMem (.cv z) D) (.classEq (syn_cun
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
            (syn_csn (.cv y)))
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv z))))))
      p0005
  have p0033 :=
    @g_wecutisobranchcwknfdv x y z u D R S h E dv_cache_0007 dv_cache_0008 dv_cache_0009
      dv_cache_0010 dv_cache_0001 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014
      dv_cache_0036 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0002
      dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0037 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0038 dv_cache_0026 dv_cache_0027 dv_cache_0039
      dv_cache_0028 dv_cache_0040 dv_cache_0003 hyp_wecutisoextendedterminaldfdv_1
      hyp_wecutisoextendedterminaldfdv_2 hyp_wecutisoextendedterminaldfdv_3
  have p0034 :=
    @g_syl
      (syn_wa (syn_wa (.classMem (.cv y) D) (.classMem (.cv u) E))
        (syn_wa (.neg (.classMem (.cv y) (syn_cdm (syn_cuni (syn_cwecutiso R D S E)))))
          (syn_wiso (syn_cun (syn_cuni (syn_cwecutiso R D S E))
              (syn_csn (syn_cop (.cv y) (.cv u)))) R S (syn_cun
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
              (syn_csn (.cv y))) (syn_cun
              (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))
              (syn_csn (.cv u))))))
      (.neg (.classMem (.cv y) (syn_cdm (syn_cuni (syn_cwecutiso R D S E)))))
      (.imp (syn_wiso
          (syn_cun (syn_cuni (syn_cwecutiso R D S E)) (syn_csn (syn_cop (.cv y) (.cv u)))) R S
          (syn_cun (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
            (syn_csn (.cv y))) (syn_cun
            (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))
            (syn_csn (.cv u)))) (.imp (syn_wa (syn_wa (.classMem (.cv z) D) (.classEq (syn_cun
                  (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
                  (syn_csn (.cv y))) (syn_cin D
                  (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv z)))))) (.classEq
              (syn_cun
                (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))
                (syn_csn (.cv u))) E)) (syn_w3o (syn_wex h (syn_wiso (.cv h) R S D E))
            (syn_wrex x E (syn_wex h (syn_wiso (.cv h) R (syn_cin S (syn_cxp (syn_cin E
                        (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv x))))
                      (syn_cin E
                        (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv x)))))) D
                  (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv x)))))))
            (syn_wrex x D (syn_wex h (syn_wiso (.cv h) S (syn_cin R (syn_cxp (syn_cin D
                        (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
                      (syn_cin D
                        (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) E
                  (syn_cin D
                    (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))))))
      p0008 p0033
  have p0035 :=
    @g_mpd
      (syn_wa (syn_wa (.classMem (.cv y) D) (.classMem (.cv u) E))
        (syn_wa (.neg (.classMem (.cv y) (syn_cdm (syn_cuni (syn_cwecutiso R D S E)))))
          (syn_wiso (syn_cun (syn_cuni (syn_cwecutiso R D S E))
              (syn_csn (syn_cop (.cv y) (.cv u)))) R S (syn_cun
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
              (syn_csn (.cv y))) (syn_cun
              (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))
              (syn_csn (.cv u))))))
      (syn_wiso
        (syn_cun (syn_cuni (syn_cwecutiso R D S E)) (syn_csn (syn_cop (.cv y) (.cv u)))) R S
        (syn_cun (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
          (syn_csn (.cv y))) (syn_cun
          (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))
          (syn_csn (.cv u))))
      (.imp (syn_wa (syn_wa (.classMem (.cv z) D) (.classEq (syn_cun
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
                (syn_csn (.cv y)))
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv z))))))
          (.classEq (syn_cun
              (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))
              (syn_csn (.cv u))) E)) (syn_w3o (syn_wex h (syn_wiso (.cv h) R S D E))
          (syn_wrex x E (syn_wex h (syn_wiso (.cv h) R (syn_cin S (syn_cxp (syn_cin E
                      (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv x)))) (syn_cin E
                      (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv x)))))) D
                (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv x)))))))
          (syn_wrex x D (syn_wex h (syn_wiso (.cv h) S (syn_cin R (syn_cxp (syn_cin D
                      (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D
                      (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) E
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))))))
      p0007 p0034
  have p0036 :=
    @g_exp3a
      (syn_wa (syn_wa (.classMem (.cv y) D) (.classMem (.cv u) E))
        (syn_wa (.neg (.classMem (.cv y) (syn_cdm (syn_cuni (syn_cwecutiso R D S E)))))
          (syn_wiso (syn_cun (syn_cuni (syn_cwecutiso R D S E))
              (syn_csn (syn_cop (.cv y) (.cv u)))) R S (syn_cun
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
              (syn_csn (.cv y))) (syn_cun
              (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))
              (syn_csn (.cv u))))))
      (syn_wa (.classMem (.cv z) D) (.classEq (syn_cun
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
            (syn_csn (.cv y)))
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv z))))))
      (.classEq (syn_cun
          (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))
          (syn_csn (.cv u))) E)
      (syn_w3o (syn_wex h (syn_wiso (.cv h) R S D E)) (syn_wrex x E (syn_wex h
            (syn_wiso (.cv h) R (syn_cin S (syn_cxp (syn_cin E
                    (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv x)))) (syn_cin E
                    (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv x)))))) D
              (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv x)))))))
        (syn_wrex x D (syn_wex h (syn_wiso (.cv h) S (syn_cin R (syn_cxp (syn_cin D
                    (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D
                    (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) E
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))))
      p0035
  have p0037 :=
    @g_imp
      (syn_wa (syn_wa (.classMem (.cv y) D) (.classMem (.cv u) E))
        (syn_wa (.neg (.classMem (.cv y) (syn_cdm (syn_cuni (syn_cwecutiso R D S E)))))
          (syn_wiso (syn_cun (syn_cuni (syn_cwecutiso R D S E))
              (syn_csn (syn_cop (.cv y) (.cv u)))) R S (syn_cun
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
              (syn_csn (.cv y))) (syn_cun
              (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))
              (syn_csn (.cv u))))))
      (syn_wa (.classMem (.cv z) D) (.classEq (syn_cun
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
            (syn_csn (.cv y)))
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv z))))))
      (.imp (.classEq (syn_cun
            (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))
            (syn_csn (.cv u))) E) (syn_w3o (syn_wex h (syn_wiso (.cv h) R S D E)) (syn_wrex x E
            (syn_wex h (syn_wiso (.cv h) R (syn_cin S (syn_cxp (syn_cin E
                      (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv x)))) (syn_cin E
                      (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv x)))))) D
                (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv x)))))))
          (syn_wrex x D (syn_wex h (syn_wiso (.cv h) S (syn_cin R (syn_cxp (syn_cin D
                      (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D
                      (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) E
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))))))
      p0036
  have p0040 :=
    @g_wecutisobranchccknfdv x y z v u D R S h E dv_cache_0007 dv_cache_0008 dv_cache_0029
      dv_cache_0009 dv_cache_0010 dv_cache_0001 dv_cache_0011 dv_cache_0012 dv_cache_0004
      dv_cache_0013 dv_cache_0014 dv_cache_0036 dv_cache_0015 dv_cache_0016 dv_cache_0030
      dv_cache_0017 dv_cache_0018 dv_cache_0002 dv_cache_0019 dv_cache_0020 dv_cache_0005
      dv_cache_0021 dv_cache_0022 dv_cache_0037 dv_cache_0023 dv_cache_0031 dv_cache_0024
      dv_cache_0025 dv_cache_0038 dv_cache_0006 dv_cache_0026 dv_cache_0027 dv_cache_0039
      dv_cache_0032 dv_cache_0033 dv_cache_0041 dv_cache_0028 dv_cache_0040 dv_cache_0003
      hyp_wecutisoextendedterminaldfdv_1 hyp_wecutisoextendedterminaldfdv_2
      hyp_wecutisoextendedterminaldfdv_3
  have p0041 :=
    @g_syl
      (syn_wa (syn_wa (.classMem (.cv y) D) (.classMem (.cv u) E))
        (syn_wa (.neg (.classMem (.cv y) (syn_cdm (syn_cuni (syn_cwecutiso R D S E)))))
          (syn_wiso (syn_cun (syn_cuni (syn_cwecutiso R D S E))
              (syn_csn (syn_cop (.cv y) (.cv u)))) R S (syn_cun
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
              (syn_csn (.cv y))) (syn_cun
              (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))
              (syn_csn (.cv u))))))
      (.neg (.classMem (.cv y) (syn_cdm (syn_cuni (syn_cwecutiso R D S E)))))
      (.imp (syn_wiso
          (syn_cun (syn_cuni (syn_cwecutiso R D S E)) (syn_csn (syn_cop (.cv y) (.cv u)))) R S
          (syn_cun (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
            (syn_csn (.cv y))) (syn_cun
            (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))
            (syn_csn (.cv u)))) (.imp (syn_wa (syn_wa (syn_wa (.classMem (.cv z) D) (.classEq
                  (syn_cun (syn_cin D
                      (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
                    (syn_csn (.cv y))) (syn_cin D
                    (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv z))))))
              (.classMem (.cv v) E)) (.classEq (syn_cun
                (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))
                (syn_csn (.cv u)))
              (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v))))))
          (syn_w3o (syn_wex h (syn_wiso (.cv h) R S D E)) (syn_wrex x E (syn_wex h
                (syn_wiso (.cv h) R (syn_cin S (syn_cxp (syn_cin E
                        (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv x))))
                      (syn_cin E
                        (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv x)))))) D
                  (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv x)))))))
            (syn_wrex x D (syn_wex h (syn_wiso (.cv h) S (syn_cin R (syn_cxp (syn_cin D
                        (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
                      (syn_cin D
                        (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) E
                  (syn_cin D
                    (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))))))
      p0008 p0040
  have p0042 :=
    @g_mpd
      (syn_wa (syn_wa (.classMem (.cv y) D) (.classMem (.cv u) E))
        (syn_wa (.neg (.classMem (.cv y) (syn_cdm (syn_cuni (syn_cwecutiso R D S E)))))
          (syn_wiso (syn_cun (syn_cuni (syn_cwecutiso R D S E))
              (syn_csn (syn_cop (.cv y) (.cv u)))) R S (syn_cun
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
              (syn_csn (.cv y))) (syn_cun
              (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))
              (syn_csn (.cv u))))))
      (syn_wiso
        (syn_cun (syn_cuni (syn_cwecutiso R D S E)) (syn_csn (syn_cop (.cv y) (.cv u)))) R S
        (syn_cun (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
          (syn_csn (.cv y))) (syn_cun
          (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))
          (syn_csn (.cv u))))
      (.imp (syn_wa (syn_wa (syn_wa (.classMem (.cv z) D) (.classEq (syn_cun (syn_cin D
                    (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
                  (syn_csn (.cv y))) (syn_cin D
                  (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv z))))))
            (.classMem (.cv v) E)) (.classEq (syn_cun
              (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))
              (syn_csn (.cv u)))
            (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v))))))
        (syn_w3o (syn_wex h (syn_wiso (.cv h) R S D E)) (syn_wrex x E (syn_wex h
              (syn_wiso (.cv h) R (syn_cin S (syn_cxp (syn_cin E
                      (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv x)))) (syn_cin E
                      (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv x)))))) D
                (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv x)))))))
          (syn_wrex x D (syn_wex h (syn_wiso (.cv h) S (syn_cin R (syn_cxp (syn_cin D
                      (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D
                      (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) E
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))))))
      p0007 p0041
  have p0043 :=
    @g_exp3a
      (syn_wa (syn_wa (.classMem (.cv y) D) (.classMem (.cv u) E))
        (syn_wa (.neg (.classMem (.cv y) (syn_cdm (syn_cuni (syn_cwecutiso R D S E)))))
          (syn_wiso (syn_cun (syn_cuni (syn_cwecutiso R D S E))
              (syn_csn (syn_cop (.cv y) (.cv u)))) R S (syn_cun
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
              (syn_csn (.cv y))) (syn_cun
              (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))
              (syn_csn (.cv u))))))
      (syn_wa (syn_wa (.classMem (.cv z) D) (.classEq (syn_cun
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
              (syn_csn (.cv y)))
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv z))))))
        (.classMem (.cv v) E))
      (.classEq (syn_cun
          (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))
          (syn_csn (.cv u)))
        (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v)))))
      (syn_w3o (syn_wex h (syn_wiso (.cv h) R S D E)) (syn_wrex x E (syn_wex h
            (syn_wiso (.cv h) R (syn_cin S (syn_cxp (syn_cin E
                    (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv x)))) (syn_cin E
                    (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv x)))))) D
              (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv x)))))))
        (syn_wrex x D (syn_wex h (syn_wiso (.cv h) S (syn_cin R (syn_cxp (syn_cin D
                    (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D
                    (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) E
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))))
      p0042
  have p0044 :=
    @g_exp3a
      (syn_wa (syn_wa (.classMem (.cv y) D) (.classMem (.cv u) E))
        (syn_wa (.neg (.classMem (.cv y) (syn_cdm (syn_cuni (syn_cwecutiso R D S E)))))
          (syn_wiso (syn_cun (syn_cuni (syn_cwecutiso R D S E))
              (syn_csn (syn_cop (.cv y) (.cv u)))) R S (syn_cun
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
              (syn_csn (.cv y))) (syn_cun
              (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))
              (syn_csn (.cv u))))))
      (syn_wa (.classMem (.cv z) D) (.classEq (syn_cun
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
            (syn_csn (.cv y)))
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv z))))))
      (.classMem (.cv v) E)
      (.imp (.classEq (syn_cun
            (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))
            (syn_csn (.cv u)))
          (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v)))))
        (syn_w3o (syn_wex h (syn_wiso (.cv h) R S D E)) (syn_wrex x E (syn_wex h
              (syn_wiso (.cv h) R (syn_cin S (syn_cxp (syn_cin E
                      (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv x)))) (syn_cin E
                      (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv x)))))) D
                (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv x)))))))
          (syn_wrex x D (syn_wex h (syn_wiso (.cv h) S (syn_cin R (syn_cxp (syn_cin D
                      (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D
                      (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) E
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))))))
      p0043
  have p0045 :=
    @g_imp
      (syn_wa (syn_wa (.classMem (.cv y) D) (.classMem (.cv u) E))
        (syn_wa (.neg (.classMem (.cv y) (syn_cdm (syn_cuni (syn_cwecutiso R D S E)))))
          (syn_wiso (syn_cun (syn_cuni (syn_cwecutiso R D S E))
              (syn_csn (syn_cop (.cv y) (.cv u)))) R S (syn_cun
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
              (syn_csn (.cv y))) (syn_cun
              (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))
              (syn_csn (.cv u))))))
      (syn_wa (.classMem (.cv z) D) (.classEq (syn_cun
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
            (syn_csn (.cv y)))
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv z))))))
      (.imp (.classMem (.cv v) E) (.imp (.classEq (syn_cun
              (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))
              (syn_csn (.cv u)))
            (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v)))))
          (syn_w3o (syn_wex h (syn_wiso (.cv h) R S D E)) (syn_wrex x E (syn_wex h
                (syn_wiso (.cv h) R (syn_cin S (syn_cxp (syn_cin E
                        (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv x))))
                      (syn_cin E
                        (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv x)))))) D
                  (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv x)))))))
            (syn_wrex x D (syn_wex h (syn_wiso (.cv h) S (syn_cin R (syn_cxp (syn_cin D
                        (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
                      (syn_cin D
                        (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) E
                  (syn_cin D
                    (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))))))
      p0044
  have p0046 :=
    @g_imp
      (syn_wa (syn_wa (syn_wa (.classMem (.cv y) D) (.classMem (.cv u) E))
          (syn_wa (.neg (.classMem (.cv y) (syn_cdm (syn_cuni (syn_cwecutiso R D S E)))))
            (syn_wiso (syn_cun (syn_cuni (syn_cwecutiso R D S E))
                (syn_csn (syn_cop (.cv y) (.cv u)))) R S (syn_cun
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
                (syn_csn (.cv y))) (syn_cun
                (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))
                (syn_csn (.cv u)))))) (syn_wa (.classMem (.cv z) D) (.classEq (syn_cun
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
              (syn_csn (.cv y)))
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv z)))))))
      (.classMem (.cv v) E)
      (.imp (.classEq (syn_cun
            (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))
            (syn_csn (.cv u)))
          (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v)))))
        (syn_w3o (syn_wex h (syn_wiso (.cv h) R S D E)) (syn_wrex x E (syn_wex h
              (syn_wiso (.cv h) R (syn_cin S (syn_cxp (syn_cin E
                      (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv x)))) (syn_cin E
                      (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv x)))))) D
                (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv x)))))))
          (syn_wrex x D (syn_wex h (syn_wiso (.cv h) S (syn_cin R (syn_cxp (syn_cin D
                      (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D
                      (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) E
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))))))
      p0045
  have p0047 :=
    @g_rexlimdva
      (syn_wa (syn_wa (syn_wa (.classMem (.cv y) D) (.classMem (.cv u) E))
          (syn_wa (.neg (.classMem (.cv y) (syn_cdm (syn_cuni (syn_cwecutiso R D S E)))))
            (syn_wiso (syn_cun (syn_cuni (syn_cwecutiso R D S E))
                (syn_csn (syn_cop (.cv y) (.cv u)))) R S (syn_cun
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
                (syn_csn (.cv y))) (syn_cun
                (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))
                (syn_csn (.cv u)))))) (syn_wa (.classMem (.cv z) D) (.classEq (syn_cun
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
              (syn_csn (.cv y)))
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv z)))))))
      (.classEq (syn_cun
          (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))
          (syn_csn (.cv u)))
        (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v)))))
      (syn_w3o (syn_wex h (syn_wiso (.cv h) R S D E)) (syn_wrex x E (syn_wex h
            (syn_wiso (.cv h) R (syn_cin S (syn_cxp (syn_cin E
                    (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv x)))) (syn_cin E
                    (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv x)))))) D
              (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv x)))))))
        (syn_wrex x D (syn_wex h (syn_wiso (.cv h) S (syn_cin R (syn_cxp (syn_cin D
                    (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D
                    (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) E
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))))
      v E dv_cache_0034 dv_cache_0042 p0046
  have p0048 :=
    @g_jaod
      (syn_wa (syn_wa (syn_wa (.classMem (.cv y) D) (.classMem (.cv u) E))
          (syn_wa (.neg (.classMem (.cv y) (syn_cdm (syn_cuni (syn_cwecutiso R D S E)))))
            (syn_wiso (syn_cun (syn_cuni (syn_cwecutiso R D S E))
                (syn_csn (syn_cop (.cv y) (.cv u)))) R S (syn_cun
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
                (syn_csn (.cv y))) (syn_cun
                (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))
                (syn_csn (.cv u)))))) (syn_wa (.classMem (.cv z) D) (.classEq (syn_cun
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
              (syn_csn (.cv y)))
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv z)))))))
      (.classEq (syn_cun
          (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))
          (syn_csn (.cv u))) E)
      (syn_w3o (syn_wex h (syn_wiso (.cv h) R S D E)) (syn_wrex x E (syn_wex h
            (syn_wiso (.cv h) R (syn_cin S (syn_cxp (syn_cin E
                    (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv x)))) (syn_cin E
                    (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv x)))))) D
              (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv x)))))))
        (syn_wrex x D (syn_wex h (syn_wiso (.cv h) S (syn_cin R (syn_cxp (syn_cin D
                    (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D
                    (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) E
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))))
      (syn_wrex v E (.classEq (syn_cun
            (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))
            (syn_csn (.cv u)))
          (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v))))))
      p0037 p0047
  have p0049 :=
    @g_ex
      (syn_wa (syn_wa (.classMem (.cv y) D) (.classMem (.cv u) E))
        (syn_wa (.neg (.classMem (.cv y) (syn_cdm (syn_cuni (syn_cwecutiso R D S E)))))
          (syn_wiso (syn_cun (syn_cuni (syn_cwecutiso R D S E))
              (syn_csn (syn_cop (.cv y) (.cv u)))) R S (syn_cun
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
              (syn_csn (.cv y))) (syn_cun
              (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))
              (syn_csn (.cv u))))))
      (syn_wa (.classMem (.cv z) D) (.classEq (syn_cun
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
            (syn_csn (.cv y)))
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv z))))))
      (.imp (syn_wo (.classEq (syn_cun
              (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))
              (syn_csn (.cv u))) E) (syn_wrex v E (.classEq (syn_cun
                (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))
                (syn_csn (.cv u))) (syn_cin E
                (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v)))))))
        (syn_w3o (syn_wex h (syn_wiso (.cv h) R S D E)) (syn_wrex x E (syn_wex h
              (syn_wiso (.cv h) R (syn_cin S (syn_cxp (syn_cin E
                      (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv x)))) (syn_cin E
                      (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv x)))))) D
                (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv x)))))))
          (syn_wrex x D (syn_wex h (syn_wiso (.cv h) S (syn_cin R (syn_cxp (syn_cin D
                      (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D
                      (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) E
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))))))
      p0048
  have p0050 :=
    @g_mpdd
      (syn_wa (syn_wa (.classMem (.cv y) D) (.classMem (.cv u) E))
        (syn_wa (.neg (.classMem (.cv y) (syn_cdm (syn_cuni (syn_cwecutiso R D S E)))))
          (syn_wiso (syn_cun (syn_cuni (syn_cwecutiso R D S E))
              (syn_csn (syn_cop (.cv y) (.cv u)))) R S (syn_cun
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
              (syn_csn (.cv y))) (syn_cun
              (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))
              (syn_csn (.cv u))))))
      (syn_wa (.classMem (.cv z) D) (.classEq (syn_cun
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
            (syn_csn (.cv y)))
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv z))))))
      (syn_wo (.classEq (syn_cun
            (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))
            (syn_csn (.cv u))) E) (syn_wrex v E (.classEq (syn_cun
              (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))
              (syn_csn (.cv u)))
            (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv v)))))))
      (syn_w3o (syn_wex h (syn_wiso (.cv h) R S D E)) (syn_wrex x E (syn_wex h
            (syn_wiso (.cv h) R (syn_cin S (syn_cxp (syn_cin E
                    (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv x)))) (syn_cin E
                    (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv x)))))) D
              (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv x)))))))
        (syn_wrex x D (syn_wex h (syn_wiso (.cv h) S (syn_cin R (syn_cxp (syn_cin D
                    (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D
                    (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) E
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))))
      p0030 p0049
  have p0051 :=
    @g_exp3a
      (syn_wa (syn_wa (.classMem (.cv y) D) (.classMem (.cv u) E))
        (syn_wa (.neg (.classMem (.cv y) (syn_cdm (syn_cuni (syn_cwecutiso R D S E)))))
          (syn_wiso (syn_cun (syn_cuni (syn_cwecutiso R D S E))
              (syn_csn (syn_cop (.cv y) (.cv u)))) R S (syn_cun
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
              (syn_csn (.cv y))) (syn_cun
              (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))
              (syn_csn (.cv u))))))
      (.classMem (.cv z) D)
      (.classEq (syn_cun
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
          (syn_csn (.cv y)))
        (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv z)))))
      (syn_w3o (syn_wex h (syn_wiso (.cv h) R S D E)) (syn_wrex x E (syn_wex h
            (syn_wiso (.cv h) R (syn_cin S (syn_cxp (syn_cin E
                    (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv x)))) (syn_cin E
                    (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv x)))))) D
              (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv x)))))))
        (syn_wrex x D (syn_wex h (syn_wiso (.cv h) S (syn_cin R (syn_cxp (syn_cin D
                    (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D
                    (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) E
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))))
      p0050
  have p0052 :=
    @g_imp
      (syn_wa (syn_wa (.classMem (.cv y) D) (.classMem (.cv u) E))
        (syn_wa (.neg (.classMem (.cv y) (syn_cdm (syn_cuni (syn_cwecutiso R D S E)))))
          (syn_wiso (syn_cun (syn_cuni (syn_cwecutiso R D S E))
              (syn_csn (syn_cop (.cv y) (.cv u)))) R S (syn_cun
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
              (syn_csn (.cv y))) (syn_cun
              (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))
              (syn_csn (.cv u))))))
      (.classMem (.cv z) D)
      (.imp (.classEq (syn_cun
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
            (syn_csn (.cv y)))
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv z)))))
        (syn_w3o (syn_wex h (syn_wiso (.cv h) R S D E)) (syn_wrex x E (syn_wex h
              (syn_wiso (.cv h) R (syn_cin S (syn_cxp (syn_cin E
                      (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv x)))) (syn_cin E
                      (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv x)))))) D
                (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv x)))))))
          (syn_wrex x D (syn_wex h (syn_wiso (.cv h) S (syn_cin R (syn_cxp (syn_cin D
                      (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D
                      (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) E
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))))))
      p0051
  have p0053 :=
    @g_rexlimdva
      (syn_wa (syn_wa (.classMem (.cv y) D) (.classMem (.cv u) E))
        (syn_wa (.neg (.classMem (.cv y) (syn_cdm (syn_cuni (syn_cwecutiso R D S E)))))
          (syn_wiso (syn_cun (syn_cuni (syn_cwecutiso R D S E))
              (syn_csn (syn_cop (.cv y) (.cv u)))) R S (syn_cun
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
              (syn_csn (.cv y))) (syn_cun
              (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))
              (syn_csn (.cv u))))))
      (.classEq (syn_cun
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
          (syn_csn (.cv y)))
        (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv z)))))
      (syn_w3o (syn_wex h (syn_wiso (.cv h) R S D E)) (syn_wrex x E (syn_wex h
            (syn_wiso (.cv h) R (syn_cin S (syn_cxp (syn_cin E
                    (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv x)))) (syn_cin E
                    (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv x)))))) D
              (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv x)))))))
        (syn_wrex x D (syn_wex h (syn_wiso (.cv h) S (syn_cin R (syn_cxp (syn_cin D
                    (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D
                    (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) E
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))))
      z D dv_cache_0043 dv_cache_0044 p0052
  have p0054 :=
    @g_jaod
      (syn_wa (syn_wa (.classMem (.cv y) D) (.classMem (.cv u) E))
        (syn_wa (.neg (.classMem (.cv y) (syn_cdm (syn_cuni (syn_cwecutiso R D S E)))))
          (syn_wiso (syn_cun (syn_cuni (syn_cwecutiso R D S E))
              (syn_csn (syn_cop (.cv y) (.cv u)))) R S (syn_cun
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
              (syn_csn (.cv y))) (syn_cun
              (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))
              (syn_csn (.cv u))))))
      (.classEq (syn_cun
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
          (syn_csn (.cv y))) D)
      (syn_w3o (syn_wex h (syn_wiso (.cv h) R S D E)) (syn_wrex x E (syn_wex h
            (syn_wiso (.cv h) R (syn_cin S (syn_cxp (syn_cin E
                    (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv x)))) (syn_cin E
                    (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv x)))))) D
              (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv x)))))))
        (syn_wrex x D (syn_wex h (syn_wiso (.cv h) S (syn_cin R (syn_cxp (syn_cin D
                    (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D
                    (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) E
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))))
      (syn_wrex z D (.classEq (syn_cun
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
            (syn_csn (.cv y)))
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv z))))))
      p0026 p0053
  have p0055 :=
    @g_mpd
      (syn_wa (syn_wa (.classMem (.cv y) D) (.classMem (.cv u) E))
        (syn_wa (.neg (.classMem (.cv y) (syn_cdm (syn_cuni (syn_cwecutiso R D S E)))))
          (syn_wiso (syn_cun (syn_cuni (syn_cwecutiso R D S E))
              (syn_csn (syn_cop (.cv y) (.cv u)))) R S (syn_cun
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
              (syn_csn (.cv y))) (syn_cun
              (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))
              (syn_csn (.cv u))))))
      (syn_wo (.classEq (syn_cun
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
            (syn_csn (.cv y))) D) (syn_wrex z D (.classEq (syn_cun
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
              (syn_csn (.cv y)))
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv z)))))))
      (syn_w3o (syn_wex h (syn_wiso (.cv h) R S D E)) (syn_wrex x E (syn_wex h
            (syn_wiso (.cv h) R (syn_cin S (syn_cxp (syn_cin E
                    (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv x)))) (syn_cin E
                    (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv x)))))) D
              (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv x)))))))
        (syn_wrex x D (syn_wex h (syn_wiso (.cv h) S (syn_cin R (syn_cxp (syn_cin D
                    (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D
                    (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) E
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))))
      p0002 p0054
  exact p0055


end NFChoice.DirectNominalPrf.WPPReplay

end

/-! Certificates from `NominalWPPReplayChunk016Compact001Part036`. -/


section

namespace NFChoice.DirectNominalPrf.WPPReplay

open scoped Fol
open NFChoice.Foundation
open NFChoice.SemanticCore
open NFChoice.ReplaySupport
open NFChoice.Compiler.CompactSourceSyntax

@[expose]
noncomputable def g_wecomparisonterminalsetfdv (x : Var) (D : Class) (R : Class)
    (S : Class) (h : Var) (E : Class) (dv_D_h : h ∉ D.fv) (dv_D_x : x ∉ D.fv)
    (dv_E_h : h ∉ E.fv) (dv_E_x : x ∉ E.fv) (dv_R_h : h ∉ R.fv) (dv_R_x : x ∉ R.fv)
    (dv_S_h : h ∉ S.fv) (dv_S_x : x ∉ S.fv) (dv_h_x : h ≠ x)
    (hyp_wecomparisonterminalsetfdv_1 : Nominal.NPrf (syn_wbr R (syn_cwe) D))
    (hyp_wecomparisonterminalsetfdv_2 : Nominal.NPrf (syn_wbr S (syn_cwe) E))
    (hyp_wecomparisonterminalsetfdv_3 :
      Nominal.NPrf (.classMem (syn_cuni (syn_cwecutiso R D S E)) (syn_cvv))) :
    Nominal.NPrf
      (syn_w3o (syn_wex h (syn_wiso (.cv h) R S D E)) (syn_wrex x E (syn_wex h
            (syn_wiso (.cv h) R (syn_cin S (syn_cxp (syn_cin E
                    (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv x)))) (syn_cin E
                    (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv x)))))) D
              (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv x)))))))
        (syn_wrex x D (syn_wex h (syn_wiso (.cv h) S (syn_cin R (syn_cxp (syn_cin D
                    (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D
                    (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) E
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))))) :=
  by
  let proofSupport : Finset Var :=
    ({ x } : Finset Var) ∪ D.fv ∪ R.fv ∪ S.fv ∪ ({ h } : Finset Var) ∪ E.fv
  let y : Var := freshVar proofSupport 0
  let u : Var := freshVar proofSupport 1
  have fresh_y : y ∉ proofSupport :=
    by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_y_ne_x : y ≠ x := by
    intro h
    exact
      fresh_y
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _
              (Finset.mem_union_left _
                (Finset.mem_union_left _ (Finset.mem_singleton.mpr h))))))
  have fresh_x_ne_y : x ≠ y := Ne.symm fresh_y_ne_x
  have fresh_y_not_D : y ∉ D.fv := by
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
  have fresh_y_not_S : y ∉ S.fv := by
    intro h
    exact
      fresh_y
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))
  have fresh_y_ne_h : y ≠ h := by
    intro h
    exact
      fresh_y
        (Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_singleton.mpr h)))
  have fresh_h_ne_y : h ≠ y := Ne.symm fresh_y_ne_h
  have fresh_y_not_E : y ∉ E.fv := by
    intro h
    exact fresh_y (Finset.mem_union_right _ (h))
  have fresh_u : u ∉ proofSupport :=
    by
    change freshVar proofSupport 1 ∉ proofSupport
    exact freshVar_not_mem proofSupport 1
  have fresh_u_ne_x : u ≠ x := by
    intro h
    exact
      fresh_u
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _
              (Finset.mem_union_left _
                (Finset.mem_union_left _ (Finset.mem_singleton.mpr h))))))
  have fresh_x_ne_u : x ≠ u := Ne.symm fresh_u_ne_x
  have fresh_u_not_D : u ∉ D.fv := by
    intro h
    exact
      fresh_u
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _
              (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))))
  have fresh_u_not_R : u ∉ R.fv := by
    intro h
    exact
      fresh_u
        (Finset.mem_union_left _ (Finset.mem_union_left _
            (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))))
  have fresh_u_not_S : u ∉ S.fv := by
    intro h
    exact
      fresh_u
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))
  have fresh_u_ne_h : u ≠ h := by
    intro h
    exact
      fresh_u
        (Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_singleton.mpr h)))
  have fresh_h_ne_u : h ≠ u := Ne.symm fresh_u_ne_h
  have fresh_u_not_E : u ∉ E.fv := by
    intro h
    exact fresh_u (Finset.mem_union_right _ (h))
  have fresh_y_ne_u : y ≠ u :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have fresh_u_ne_y : u ≠ y := Ne.symm fresh_y_ne_u
  have dv_cache_0001 : y ∉ (D).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_y_not_D, not_false_eq_true])
  have dv_cache_0002 : y ∉ (E).fv :=
    by
    clear dv_cache_0001
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_y_not_E, not_false_eq_true])
  have dv_cache_0003 : y ∉ (R).fv :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_y_not_R, not_false_eq_true])
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
  have dv_cache_0005 : u ∉ (D).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact
      (by
        have compact_fv_not_mem_empty : u ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_u_not_D, not_false_eq_true])
  have dv_cache_0006 : u ∉ (E).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact
      (by
        have compact_fv_not_mem_empty : u ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_u_not_E, not_false_eq_true])
  have dv_cache_0007 : u ∉ (R).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006
    exact
      (by
        have compact_fv_not_mem_empty : u ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_u_not_R, not_false_eq_true])
  have dv_cache_0008 : u ∉ (S).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007
    exact
      (by
        have compact_fv_not_mem_empty : u ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_u_not_S, not_false_eq_true])
  have dv_cache_0009 : h ∉ ((syn_cuni (syn_cwecutiso R D S E))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008
    exact
      (by
        have compact_fv_not_mem_empty : h ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cuni,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwecutiso, Finset.mem_union,
          dv_D_h, dv_E_h, dv_R_h, dv_S_h, or_false, not_false_eq_true])
  have dv_cache_0010 : h ∉ ((syn_wiso (syn_cuni (syn_cwecutiso R D S E)) R S D E)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009
    exact
      (by
        have compact_fv_not_mem_empty : h ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_wiso,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cuni,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwecutiso, Finset.mem_union,
          dv_D_h, dv_E_h, dv_R_h, dv_S_h, or_false, not_false_eq_true])
  have dv_cache_0011 :
    h ∉
      ((syn_wiso (syn_cuni (syn_cwecutiso R D S E)) R (syn_cin S (syn_cxp
              (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))
              (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u)))))) D
          (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u)))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010
    exact
      (by
        have compact_fv_not_mem_empty : h ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_wiso,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cuni,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwecutiso,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxp,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cima,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdif,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cid,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, dv_D_h, dv_E_h, dv_S_h, fresh_h_ne_u, dv_R_h,
          compact_fv_not_mem_empty, or_false, not_false_eq_true])
  have dv_cache_0012 : h ∉ ((Wff.classEq (.cv x) (.cv u))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
    exact
      (by
        have compact_fv_not_mem_empty : h ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, dv_h_x, fresh_h_ne_u, or_false, not_false_eq_true])
  have dv_cache_0013 : x ∉ ((Class.cv u)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_x_ne_u, not_false_eq_true])
  have dv_cache_0014 : x ∉ (E).fv :=
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
        simp only [dv_E_x, not_false_eq_true])
  have dv_cache_0015 :
    x ∉
      ((syn_wex h (syn_wiso (.cv h) R (syn_cin S (syn_cxp
                (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))
                (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u)))))) D
            (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))))).fv :=
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
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wex,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_wiso,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxp,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cima,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdif,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cid,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, Finset.mem_union,
          Finset.mem_erase, Finset.mem_singleton, dv_D_x, dv_E_x, dv_S_x, fresh_x_ne_u,
          (Ne.symm dv_h_x), dv_R_x, compact_fv_not_mem_empty, or_false, and_false,
          not_false_eq_true])
  have dv_cache_0016 :
    u ∉
      ((syn_w3o (syn_wex h (syn_wiso (.cv h) R S D E)) (syn_wrex x E (syn_wex h
              (syn_wiso (.cv h) R (syn_cin S (syn_cxp (syn_cin E
                      (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv x)))) (syn_cin E
                      (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv x)))))) D
                (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv x)))))))
          (syn_wrex x D (syn_wex h (syn_wiso (.cv h) S (syn_cin R (syn_cxp (syn_cin D
                      (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D
                      (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) E
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
                    (syn_csn (.cv x))))))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015
    exact
      (by
        have compact_fv_not_mem_empty : u ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_w3o,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wex,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_wiso,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wrex,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxp,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cima,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdif,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cid,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, Finset.mem_union,
          Finset.mem_erase, Finset.mem_singleton, fresh_u_not_D, fresh_u_not_E,
          fresh_u_not_R, fresh_u_ne_x, fresh_u_ne_h, fresh_u_not_S,
          compact_fv_not_mem_empty, or_false, and_false, not_false_eq_true])
  have dv_cache_0017 :
    u ∉ ((Wff.classEq (syn_cdm (syn_cuni (syn_cwecutiso R D S E))) D)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016
    exact
      (by
        have compact_fv_not_mem_empty : u ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdm,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cuni,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwecutiso, Finset.mem_union,
          fresh_u_not_D, fresh_u_not_E, fresh_u_not_R, fresh_u_not_S, or_false,
          not_false_eq_true])
  have dv_cache_0018 : h ∉ ((syn_ccnv (syn_cuni (syn_cwecutiso R D S E)))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
    exact
      (by
        have compact_fv_not_mem_empty : h ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cuni,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwecutiso, Finset.mem_union,
          dv_D_h, dv_E_h, dv_R_h, dv_S_h, or_false, not_false_eq_true])
  have dv_cache_0019 :
    h ∉
      ((syn_wiso (syn_ccnv (syn_cuni (syn_cwecutiso R D S E))) S (syn_cin R (syn_cxp
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))) E
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018
    exact
      (by
        have compact_fv_not_mem_empty : h ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_wiso,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cuni,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwecutiso,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxp,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cima,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdif,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cid,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, dv_E_h, dv_D_h, dv_R_h, fresh_h_ne_y, dv_S_h,
          compact_fv_not_mem_empty, or_false, not_false_eq_true])
  have dv_cache_0020 : h ∉ ((Wff.classEq (.cv x) (.cv y))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019
    exact
      (by
        have compact_fv_not_mem_empty : h ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, dv_h_x, fresh_h_ne_y, or_false, not_false_eq_true])
  have dv_cache_0021 : x ∉ ((Class.cv y)).fv :=
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
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_x_ne_y, not_false_eq_true])
  have dv_cache_0022 : x ∉ (D).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_D_x, not_false_eq_true])
  have dv_cache_0023 :
    x ∉
      ((syn_wex h (syn_wiso (.cv h) S (syn_cin R (syn_cxp
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))) E
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wex,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_wiso,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxp,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cima,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdif,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cid,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, Finset.mem_union,
          Finset.mem_erase, Finset.mem_singleton, dv_E_x, dv_D_x, dv_R_x, fresh_x_ne_y,
          (Ne.symm dv_h_x), dv_S_x, compact_fv_not_mem_empty, or_false, and_false,
          not_false_eq_true])
  have dv_cache_0024 : h ∉ (D).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
    exact
      (by
        have compact_fv_not_mem_empty : h ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_D_h, not_false_eq_true])
  have dv_cache_0025 : h ∉ (E).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024
    exact
      (by
        have compact_fv_not_mem_empty : h ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_E_h, not_false_eq_true])
  have dv_cache_0026 : h ∉ (R).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025
    exact
      (by
        have compact_fv_not_mem_empty : h ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_R_h, not_false_eq_true])
  have dv_cache_0027 : x ∉ (R).fv :=
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
        simp only [dv_R_x, not_false_eq_true])
  have dv_cache_0028 : h ∉ (S).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027
    exact
      (by
        have compact_fv_not_mem_empty : h ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_S_h, not_false_eq_true])
  have dv_cache_0029 : x ∉ (S).fv :=
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
        simp only [dv_S_x, not_false_eq_true])
  have dv_cache_0030 : h ≠ u :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
    exact (show h ≠ u from (by exact fresh_h_ne_u))
  have dv_cache_0031 : h ≠ x :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
      dv_cache_0030
    exact (show h ≠ x from (by exact dv_h_x))
  have dv_cache_0032 : h ≠ y :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
      dv_cache_0030 dv_cache_0031
    exact (show h ≠ y from (by exact fresh_h_ne_y))
  have dv_cache_0033 : u ≠ x :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
      dv_cache_0030 dv_cache_0031 dv_cache_0032
    exact (show u ≠ x from (by exact fresh_u_ne_x))
  have dv_cache_0034 : u ≠ y :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
      dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033
    exact (show u ≠ y from (by exact fresh_u_ne_y))
  have dv_cache_0035 : x ≠ y :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
      dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034
    exact (show x ≠ y from (by exact fresh_x_ne_y))
  have dv_cache_0036 :
    u ∉
      ((syn_wa (.classMem (.cv y) D) (.classEq (syn_cdm (syn_cuni (syn_cwecutiso R D S E)))
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
      dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035
    exact
      (by
        have compact_fv_not_mem_empty : u ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdm,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cuni,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwecutiso,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cima,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdif,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cid,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, Finset.mem_union,
          Finset.mem_singleton, fresh_u_ne_y, fresh_u_not_D, fresh_u_not_E, fresh_u_not_R,
          fresh_u_not_S, compact_fv_not_mem_empty, or_false, not_false_eq_true])
  have dv_cache_0037 :
    y ∉
      ((syn_w3o (syn_wex h (syn_wiso (.cv h) R S D E)) (syn_wrex x E (syn_wex h
              (syn_wiso (.cv h) R (syn_cin S (syn_cxp (syn_cin E
                      (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv x)))) (syn_cin E
                      (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv x)))))) D
                (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv x)))))))
          (syn_wrex x D (syn_wex h (syn_wiso (.cv h) S (syn_cin R (syn_cxp (syn_cin D
                      (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D
                      (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) E
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
                    (syn_csn (.cv x))))))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
      dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035
      dv_cache_0036
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_w3o,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wex,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_wiso,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wrex,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxp,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cima,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdif,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cid,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, Finset.mem_union,
          Finset.mem_erase, Finset.mem_singleton, fresh_y_not_D, fresh_y_not_E,
          fresh_y_not_R, fresh_y_ne_x, fresh_y_ne_h, fresh_y_not_S,
          compact_fv_not_mem_empty, or_false, and_false, not_false_eq_true])
  have p0000 :=
    @g_wecutisouniondmcutorwholendv y D R S E dv_cache_0001 dv_cache_0002 dv_cache_0003
      dv_cache_0004 hyp_wecomparisonterminalsetfdv_1 hyp_wecomparisonterminalsetfdv_3
  have p0001 :=
    @g_wecutisounionrncutorwholendv u D R S E dv_cache_0005 dv_cache_0006 dv_cache_0007
      dv_cache_0008 hyp_wecomparisonterminalsetfdv_2 hyp_wecomparisonterminalsetfdv_3
  have p0002 :=
    @g_a1i
      (syn_wo (.classEq (syn_crn (syn_cuni (syn_cwecutiso R D S E))) E) (syn_wrex u E
          (.classEq (syn_crn (syn_cuni (syn_cwecutiso R D S E)))
            (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u)))))))
      (.classEq (syn_cdm (syn_cuni (syn_cwecutiso R D S E))) D) p0001
  have p0003 :=
    @g_wecutisounionisondv D R S E hyp_wecomparisonterminalsetfdv_1
      hyp_wecomparisonterminalsetfdv_2
  have p0004 :=
    @g_a1i
      (syn_wiso (syn_cuni (syn_cwecutiso R D S E)) R S
        (syn_cdm (syn_cuni (syn_cwecutiso R D S E)))
        (syn_crn (syn_cuni (syn_cwecutiso R D S E))))
      (syn_wa (.classEq (syn_cdm (syn_cuni (syn_cwecutiso R D S E))) D)
        (.classEq (syn_crn (syn_cuni (syn_cwecutiso R D S E))) E))
      p0003
  have p0005 :=
    @g_simpl (.classEq (syn_cdm (syn_cuni (syn_cwecutiso R D S E))) D)
      (.classEq (syn_crn (syn_cuni (syn_cwecutiso R D S E))) E)
  have p0006 :=
    @g_isoeq4 (syn_cdm (syn_cuni (syn_cwecutiso R D S E)))
      (syn_crn (syn_cuni (syn_cwecutiso R D S E))) D R S
      (syn_cuni (syn_cwecutiso R D S E))
  have p0007 :=
    @g_syl
      (syn_wa (.classEq (syn_cdm (syn_cuni (syn_cwecutiso R D S E))) D)
        (.classEq (syn_crn (syn_cuni (syn_cwecutiso R D S E))) E))
      (.classEq (syn_cdm (syn_cuni (syn_cwecutiso R D S E))) D)
      (syn_wb (syn_wiso (syn_cuni (syn_cwecutiso R D S E)) R S
          (syn_cdm (syn_cuni (syn_cwecutiso R D S E)))
          (syn_crn (syn_cuni (syn_cwecutiso R D S E))))
        (syn_wiso (syn_cuni (syn_cwecutiso R D S E)) R S D
          (syn_crn (syn_cuni (syn_cwecutiso R D S E)))))
      p0005 p0006
  have p0008 :=
    @g_mpbid
      (syn_wa (.classEq (syn_cdm (syn_cuni (syn_cwecutiso R D S E))) D)
        (.classEq (syn_crn (syn_cuni (syn_cwecutiso R D S E))) E))
      (syn_wiso (syn_cuni (syn_cwecutiso R D S E)) R S
        (syn_cdm (syn_cuni (syn_cwecutiso R D S E)))
        (syn_crn (syn_cuni (syn_cwecutiso R D S E))))
      (syn_wiso (syn_cuni (syn_cwecutiso R D S E)) R S D
        (syn_crn (syn_cuni (syn_cwecutiso R D S E))))
      p0004 p0007
  have p0009 :=
    @g_simpr (.classEq (syn_cdm (syn_cuni (syn_cwecutiso R D S E))) D)
      (.classEq (syn_crn (syn_cuni (syn_cwecutiso R D S E))) E)
  have p0010 :=
    @g_isoeq5 D (syn_crn (syn_cuni (syn_cwecutiso R D S E))) E R S
      (syn_cuni (syn_cwecutiso R D S E))
  have p0011 :=
    @g_syl
      (syn_wa (.classEq (syn_cdm (syn_cuni (syn_cwecutiso R D S E))) D)
        (.classEq (syn_crn (syn_cuni (syn_cwecutiso R D S E))) E))
      (.classEq (syn_crn (syn_cuni (syn_cwecutiso R D S E))) E)
      (syn_wb (syn_wiso (syn_cuni (syn_cwecutiso R D S E)) R S D
          (syn_crn (syn_cuni (syn_cwecutiso R D S E))))
        (syn_wiso (syn_cuni (syn_cwecutiso R D S E)) R S D E))
      p0009 p0010
  have p0012 :=
    @g_mpbid
      (syn_wa (.classEq (syn_cdm (syn_cuni (syn_cwecutiso R D S E))) D)
        (.classEq (syn_crn (syn_cuni (syn_cwecutiso R D S E))) E))
      (syn_wiso (syn_cuni (syn_cwecutiso R D S E)) R S D
        (syn_crn (syn_cuni (syn_cwecutiso R D S E))))
      (syn_wiso (syn_cuni (syn_cwecutiso R D S E)) R S D E) p0008 p0011
  have p0013 := @g_isoeq1 D E R S (syn_cuni (syn_cwecutiso R D S E)) (.cv h)
  have p0014 :=
    @g_spcev (syn_wiso (.cv h) R S D E)
      (syn_wiso (syn_cuni (syn_cwecutiso R D S E)) R S D E) h
      (syn_cuni (syn_cwecutiso R D S E)) dv_cache_0009 dv_cache_0010
      hyp_wecomparisonterminalsetfdv_3 p0013
  have p0015 :=
    @g_syl
      (syn_wa (.classEq (syn_cdm (syn_cuni (syn_cwecutiso R D S E))) D)
        (.classEq (syn_crn (syn_cuni (syn_cwecutiso R D S E))) E))
      (syn_wiso (syn_cuni (syn_cwecutiso R D S E)) R S D E)
      (syn_wex h (syn_wiso (.cv h) R S D E)) p0012 p0014
  have p0016 :=
    @g_n_3mix1 (syn_wex h (syn_wiso (.cv h) R S D E))
      (syn_wrex x E (syn_wex h (syn_wiso (.cv h) R (syn_cin S (syn_cxp
                (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv x))))
                (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv x)))))) D
            (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv x)))))))
      (syn_wrex x D (syn_wex h (syn_wiso (.cv h) S (syn_cin R (syn_cxp
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) E
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))))
  have p0017 :=
    @g_syl
      (syn_wa (.classEq (syn_cdm (syn_cuni (syn_cwecutiso R D S E))) D)
        (.classEq (syn_crn (syn_cuni (syn_cwecutiso R D S E))) E))
      (syn_wex h (syn_wiso (.cv h) R S D E))
      (syn_w3o (syn_wex h (syn_wiso (.cv h) R S D E)) (syn_wrex x E (syn_wex h
            (syn_wiso (.cv h) R (syn_cin S (syn_cxp (syn_cin E
                    (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv x)))) (syn_cin E
                    (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv x)))))) D
              (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv x)))))))
        (syn_wrex x D (syn_wex h (syn_wiso (.cv h) S (syn_cin R (syn_cxp (syn_cin D
                    (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D
                    (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) E
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))))
      p0015 p0016
  have p0018 :=
    @g_ex (.classEq (syn_cdm (syn_cuni (syn_cwecutiso R D S E))) D)
      (.classEq (syn_crn (syn_cuni (syn_cwecutiso R D S E))) E)
      (syn_w3o (syn_wex h (syn_wiso (.cv h) R S D E)) (syn_wrex x E (syn_wex h
            (syn_wiso (.cv h) R (syn_cin S (syn_cxp (syn_cin E
                    (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv x)))) (syn_cin E
                    (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv x)))))) D
              (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv x)))))))
        (syn_wrex x D (syn_wex h (syn_wiso (.cv h) S (syn_cin R (syn_cxp (syn_cin D
                    (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D
                    (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) E
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))))
      p0017
  have p0019 :=
    @g_simpl
      (syn_wa (.classEq (syn_cdm (syn_cuni (syn_cwecutiso R D S E))) D) (.classMem (.cv u) E))
      (.classEq (syn_crn (syn_cuni (syn_cwecutiso R D S E)))
        (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u)))))
  have p0020 :=
    @g_simpr (.classEq (syn_cdm (syn_cuni (syn_cwecutiso R D S E))) D)
      (.classMem (.cv u) E)
  have p0021 :=
    @g_syl
      (syn_wa (syn_wa (.classEq (syn_cdm (syn_cuni (syn_cwecutiso R D S E))) D)
          (.classMem (.cv u) E)) (.classEq (syn_crn (syn_cuni (syn_cwecutiso R D S E)))
          (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))))
      (syn_wa (.classEq (syn_cdm (syn_cuni (syn_cwecutiso R D S E))) D) (.classMem (.cv u) E))
      (.classMem (.cv u) E) p0019 p0020
  have p0023 :=
    @g_a1i
      (syn_wiso (syn_cuni (syn_cwecutiso R D S E)) R S
        (syn_cdm (syn_cuni (syn_cwecutiso R D S E)))
        (syn_crn (syn_cuni (syn_cwecutiso R D S E))))
      (syn_wa (syn_wa (.classEq (syn_cdm (syn_cuni (syn_cwecutiso R D S E))) D)
          (.classMem (.cv u) E)) (.classEq (syn_crn (syn_cuni (syn_cwecutiso R D S E)))
          (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))))
      p0003
  have p0025 :=
    @g_simpl (.classEq (syn_cdm (syn_cuni (syn_cwecutiso R D S E))) D)
      (.classMem (.cv u) E)
  have p0026 :=
    @g_syl
      (syn_wa (syn_wa (.classEq (syn_cdm (syn_cuni (syn_cwecutiso R D S E))) D)
          (.classMem (.cv u) E)) (.classEq (syn_crn (syn_cuni (syn_cwecutiso R D S E)))
          (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))))
      (syn_wa (.classEq (syn_cdm (syn_cuni (syn_cwecutiso R D S E))) D) (.classMem (.cv u) E))
      (.classEq (syn_cdm (syn_cuni (syn_cwecutiso R D S E))) D) p0019 p0025
  have p0028 :=
    @g_syl
      (syn_wa (syn_wa (.classEq (syn_cdm (syn_cuni (syn_cwecutiso R D S E))) D)
          (.classMem (.cv u) E)) (.classEq (syn_crn (syn_cuni (syn_cwecutiso R D S E)))
          (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))))
      (.classEq (syn_cdm (syn_cuni (syn_cwecutiso R D S E))) D)
      (syn_wb (syn_wiso (syn_cuni (syn_cwecutiso R D S E)) R S
          (syn_cdm (syn_cuni (syn_cwecutiso R D S E)))
          (syn_crn (syn_cuni (syn_cwecutiso R D S E))))
        (syn_wiso (syn_cuni (syn_cwecutiso R D S E)) R S D
          (syn_crn (syn_cuni (syn_cwecutiso R D S E)))))
      p0026 p0006
  have p0029 :=
    @g_mpbid
      (syn_wa (syn_wa (.classEq (syn_cdm (syn_cuni (syn_cwecutiso R D S E))) D)
          (.classMem (.cv u) E)) (.classEq (syn_crn (syn_cuni (syn_cwecutiso R D S E)))
          (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))))
      (syn_wiso (syn_cuni (syn_cwecutiso R D S E)) R S
        (syn_cdm (syn_cuni (syn_cwecutiso R D S E)))
        (syn_crn (syn_cuni (syn_cwecutiso R D S E))))
      (syn_wiso (syn_cuni (syn_cwecutiso R D S E)) R S D
        (syn_crn (syn_cuni (syn_cwecutiso R D S E))))
      p0023 p0028
  have p0030 :=
    @g_simpr
      (syn_wa (.classEq (syn_cdm (syn_cuni (syn_cwecutiso R D S E))) D) (.classMem (.cv u) E))
      (.classEq (syn_crn (syn_cuni (syn_cwecutiso R D S E)))
        (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u)))))
  have p0031 :=
    @g_isoeq5 D (syn_crn (syn_cuni (syn_cwecutiso R D S E)))
      (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u)))) R S
      (syn_cuni (syn_cwecutiso R D S E))
  have p0032 :=
    @g_syl
      (syn_wa (syn_wa (.classEq (syn_cdm (syn_cuni (syn_cwecutiso R D S E))) D)
          (.classMem (.cv u) E)) (.classEq (syn_crn (syn_cuni (syn_cwecutiso R D S E)))
          (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))))
      (.classEq (syn_crn (syn_cuni (syn_cwecutiso R D S E)))
        (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u)))))
      (syn_wb (syn_wiso (syn_cuni (syn_cwecutiso R D S E)) R S D
          (syn_crn (syn_cuni (syn_cwecutiso R D S E))))
        (syn_wiso (syn_cuni (syn_cwecutiso R D S E)) R S D
          (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))))
      p0030 p0031
  have p0033 :=
    @g_mpbid
      (syn_wa (syn_wa (.classEq (syn_cdm (syn_cuni (syn_cwecutiso R D S E))) D)
          (.classMem (.cv u) E)) (.classEq (syn_crn (syn_cuni (syn_cwecutiso R D S E)))
          (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))))
      (syn_wiso (syn_cuni (syn_cwecutiso R D S E)) R S D
        (syn_crn (syn_cuni (syn_cwecutiso R D S E))))
      (syn_wiso (syn_cuni (syn_cwecutiso R D S E)) R S D
        (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u)))))
      p0029 p0032
  have p0034 :=
    @g_isores2 D
      (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u)))) R S
      (syn_cuni (syn_cwecutiso R D S E))
  have p0035 :=
    @g_biimpi
      (syn_wiso (syn_cuni (syn_cwecutiso R D S E)) R S D
        (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u)))))
      (syn_wiso (syn_cuni (syn_cwecutiso R D S E)) R (syn_cin S (syn_cxp
            (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))
            (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))))
        D (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u)))))
      p0034
  have p0036 :=
    @g_syl
      (syn_wa (syn_wa (.classEq (syn_cdm (syn_cuni (syn_cwecutiso R D S E))) D)
          (.classMem (.cv u) E)) (.classEq (syn_crn (syn_cuni (syn_cwecutiso R D S E)))
          (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))))
      (syn_wiso (syn_cuni (syn_cwecutiso R D S E)) R S D
        (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u)))))
      (syn_wiso (syn_cuni (syn_cwecutiso R D S E)) R (syn_cin S (syn_cxp
            (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))
            (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))))
        D (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u)))))
      p0033 p0035
  have p0037 :=
    @g_isoeq1 D (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))
      R
      (syn_cin S (syn_cxp
          (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))
          (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))))
      (syn_cuni (syn_cwecutiso R D S E)) (.cv h)
  have p0038 :=
    @g_spcev
      (syn_wiso (.cv h) R (syn_cin S (syn_cxp
            (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))
            (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))))
        D (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u)))))
      (syn_wiso (syn_cuni (syn_cwecutiso R D S E)) R (syn_cin S (syn_cxp
            (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))
            (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))))
        D (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u)))))
      h (syn_cuni (syn_cwecutiso R D S E)) dv_cache_0009 dv_cache_0011
      hyp_wecomparisonterminalsetfdv_3 p0037
  have p0039 :=
    @g_syl
      (syn_wa (syn_wa (.classEq (syn_cdm (syn_cuni (syn_cwecutiso R D S E))) D)
          (.classMem (.cv u) E)) (.classEq (syn_crn (syn_cuni (syn_cwecutiso R D S E)))
          (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))))
      (syn_wiso (syn_cuni (syn_cwecutiso R D S E)) R (syn_cin S (syn_cxp
            (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))
            (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))))
        D (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u)))))
      (syn_wex h (syn_wiso (.cv h) R (syn_cin S (syn_cxp
              (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))
              (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))))
          D (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))))
      p0036 p0038
  have p0040 :=
    @g_jca
      (syn_wa (syn_wa (.classEq (syn_cdm (syn_cuni (syn_cwecutiso R D S E))) D)
          (.classMem (.cv u) E)) (.classEq (syn_crn (syn_cuni (syn_cwecutiso R D S E)))
          (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))))
      (.classMem (.cv u) E)
      (syn_wex h (syn_wiso (.cv h) R (syn_cin S (syn_cxp
              (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))
              (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))))
          D (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))))
      p0021 p0039
  have p0041 := @g_sneq (.cv x) (.cv u)
  have p0042 :=
    @g_imaeq2d (.classEq (.cv x) (.cv u)) (syn_csn (.cv x)) (syn_csn (.cv u))
      (syn_ccnv (syn_cdif S (syn_cid))) p0041
  have p0043 :=
    @g_ineq2d (.classEq (.cv x) (.cv u))
      (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv x)))
      (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))) E p0042
  have p0047 :=
    @g_xpeq12d (.classEq (.cv x) (.cv u))
      (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv x))))
      (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))
      (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv x))))
      (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u)))) p0043
      p0043
  have p0048 :=
    @g_ineq2d (.classEq (.cv x) (.cv u))
      (syn_cxp (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv x))))
        (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv x)))))
      (syn_cxp (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))
        (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u)))))
      S p0047
  have p0049 :=
    @g_isoeq3 D (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv x))))
      R
      (syn_cin S (syn_cxp
          (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv x))))
          (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv x))))))
      (syn_cin S (syn_cxp
          (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))
          (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))))
      (.cv h)
  have p0050 :=
    @g_syl (.classEq (.cv x) (.cv u))
      (.classEq (syn_cin S (syn_cxp
            (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv x))))
            (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv x))))))
        (syn_cin S (syn_cxp
            (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))
            (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u)))))))
      (syn_wb (syn_wiso (.cv h) R (syn_cin S (syn_cxp
              (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv x))))
              (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv x))))))
          D (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv x)))))
        (syn_wiso (.cv h) R (syn_cin S (syn_cxp
              (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))
              (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))))
          D (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv x))))))
      p0048 p0049
  have p0054 :=
    @g_isoeq5 D (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv x))))
      (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u)))) R
      (syn_cin S (syn_cxp
          (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))
          (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))))
      (.cv h)
  have p0055 :=
    @g_syl (.classEq (.cv x) (.cv u))
      (.classEq (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv x))))
        (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u)))))
      (syn_wb (syn_wiso (.cv h) R (syn_cin S (syn_cxp
              (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))
              (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))))
          D (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv x)))))
        (syn_wiso (.cv h) R (syn_cin S (syn_cxp
              (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))
              (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))))
          D (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))))
      p0043 p0054
  have p0056 :=
    @g_bitrd (.classEq (.cv x) (.cv u))
      (syn_wiso (.cv h) R (syn_cin S (syn_cxp
            (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv x))))
            (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv x))))))
        D (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv x)))))
      (syn_wiso (.cv h) R (syn_cin S (syn_cxp
            (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))
            (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))))
        D (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv x)))))
      (syn_wiso (.cv h) R (syn_cin S (syn_cxp
            (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))
            (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))))
        D (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u)))))
      p0050 p0055
  have p0057 :=
    @g_exbidv (.classEq (.cv x) (.cv u))
      (syn_wiso (.cv h) R (syn_cin S (syn_cxp
            (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv x))))
            (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv x))))))
        D (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv x)))))
      (syn_wiso (.cv h) R (syn_cin S (syn_cxp
            (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))
            (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))))
        D (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u)))))
      h dv_cache_0012 p0056
  have p0058 :=
    @g_rspcev
      (syn_wex h (syn_wiso (.cv h) R (syn_cin S (syn_cxp
              (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv x))))
              (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv x))))))
          D (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv x))))))
      (syn_wex h (syn_wiso (.cv h) R (syn_cin S (syn_cxp
              (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))
              (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))))
          D (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))))
      x (.cv u) E dv_cache_0013 dv_cache_0014 dv_cache_0015 p0057
  have p0059 :=
    @g_syl
      (syn_wa (syn_wa (.classEq (syn_cdm (syn_cuni (syn_cwecutiso R D S E))) D)
          (.classMem (.cv u) E)) (.classEq (syn_crn (syn_cuni (syn_cwecutiso R D S E)))
          (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))))
      (syn_wa (.classMem (.cv u) E) (syn_wex h (syn_wiso (.cv h) R (syn_cin S (syn_cxp
                (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))
                (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u)))))) D
            (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u)))))))
      (syn_wrex x E (syn_wex h (syn_wiso (.cv h) R (syn_cin S (syn_cxp
                (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv x))))
                (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv x)))))) D
            (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv x)))))))
      p0040 p0058
  have p0060 :=
    @g_n_3mix2
      (syn_wrex x E (syn_wex h (syn_wiso (.cv h) R (syn_cin S (syn_cxp
                (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv x))))
                (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv x)))))) D
            (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv x)))))))
      (syn_wex h (syn_wiso (.cv h) R S D E))
      (syn_wrex x D (syn_wex h (syn_wiso (.cv h) S (syn_cin R (syn_cxp
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) E
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))))
  have p0061 :=
    @g_syl
      (syn_wa (syn_wa (.classEq (syn_cdm (syn_cuni (syn_cwecutiso R D S E))) D)
          (.classMem (.cv u) E)) (.classEq (syn_crn (syn_cuni (syn_cwecutiso R D S E)))
          (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))))
      (syn_wrex x E (syn_wex h (syn_wiso (.cv h) R (syn_cin S (syn_cxp
                (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv x))))
                (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv x)))))) D
            (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv x)))))))
      (syn_w3o (syn_wex h (syn_wiso (.cv h) R S D E)) (syn_wrex x E (syn_wex h
            (syn_wiso (.cv h) R (syn_cin S (syn_cxp (syn_cin E
                    (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv x)))) (syn_cin E
                    (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv x)))))) D
              (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv x)))))))
        (syn_wrex x D (syn_wex h (syn_wiso (.cv h) S (syn_cin R (syn_cxp (syn_cin D
                    (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D
                    (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) E
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))))
      p0059 p0060
  have p0062 :=
    @g_ex
      (syn_wa (.classEq (syn_cdm (syn_cuni (syn_cwecutiso R D S E))) D) (.classMem (.cv u) E))
      (.classEq (syn_crn (syn_cuni (syn_cwecutiso R D S E)))
        (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u)))))
      (syn_w3o (syn_wex h (syn_wiso (.cv h) R S D E)) (syn_wrex x E (syn_wex h
            (syn_wiso (.cv h) R (syn_cin S (syn_cxp (syn_cin E
                    (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv x)))) (syn_cin E
                    (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv x)))))) D
              (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv x)))))))
        (syn_wrex x D (syn_wex h (syn_wiso (.cv h) S (syn_cin R (syn_cxp (syn_cin D
                    (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D
                    (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) E
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))))
      p0061
  have p0063 :=
    @g_rexlimdva (.classEq (syn_cdm (syn_cuni (syn_cwecutiso R D S E))) D)
      (.classEq (syn_crn (syn_cuni (syn_cwecutiso R D S E)))
        (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u)))))
      (syn_w3o (syn_wex h (syn_wiso (.cv h) R S D E)) (syn_wrex x E (syn_wex h
            (syn_wiso (.cv h) R (syn_cin S (syn_cxp (syn_cin E
                    (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv x)))) (syn_cin E
                    (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv x)))))) D
              (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv x)))))))
        (syn_wrex x D (syn_wex h (syn_wiso (.cv h) S (syn_cin R (syn_cxp (syn_cin D
                    (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D
                    (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) E
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))))
      u E dv_cache_0016 dv_cache_0017 p0062
  have p0064 :=
    @g_jaod (.classEq (syn_cdm (syn_cuni (syn_cwecutiso R D S E))) D)
      (.classEq (syn_crn (syn_cuni (syn_cwecutiso R D S E))) E)
      (syn_w3o (syn_wex h (syn_wiso (.cv h) R S D E)) (syn_wrex x E (syn_wex h
            (syn_wiso (.cv h) R (syn_cin S (syn_cxp (syn_cin E
                    (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv x)))) (syn_cin E
                    (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv x)))))) D
              (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv x)))))))
        (syn_wrex x D (syn_wex h (syn_wiso (.cv h) S (syn_cin R (syn_cxp (syn_cin D
                    (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D
                    (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) E
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))))
      (syn_wrex u E (.classEq (syn_crn (syn_cuni (syn_cwecutiso R D S E)))
          (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))))
      p0018 p0063
  have p0065 :=
    @g_mpd (.classEq (syn_cdm (syn_cuni (syn_cwecutiso R D S E))) D)
      (syn_wo (.classEq (syn_crn (syn_cuni (syn_cwecutiso R D S E))) E) (syn_wrex u E
          (.classEq (syn_crn (syn_cuni (syn_cwecutiso R D S E)))
            (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u)))))))
      (syn_w3o (syn_wex h (syn_wiso (.cv h) R S D E)) (syn_wrex x E (syn_wex h
            (syn_wiso (.cv h) R (syn_cin S (syn_cxp (syn_cin E
                    (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv x)))) (syn_cin E
                    (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv x)))))) D
              (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv x)))))))
        (syn_wrex x D (syn_wex h (syn_wiso (.cv h) S (syn_cin R (syn_cxp (syn_cin D
                    (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D
                    (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) E
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))))
      p0002 p0064
  have p0067 :=
    @g_a1i
      (syn_wo (.classEq (syn_crn (syn_cuni (syn_cwecutiso R D S E))) E) (syn_wrex u E
          (.classEq (syn_crn (syn_cuni (syn_cwecutiso R D S E)))
            (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u)))))))
      (syn_wa (.classMem (.cv y) D) (.classEq (syn_cdm (syn_cuni (syn_cwecutiso R D S E)))
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
      p0001
  have p0068 :=
    @g_simpl
      (syn_wa (.classMem (.cv y) D) (.classEq (syn_cdm (syn_cuni (syn_cwecutiso R D S E)))
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
      (.classEq (syn_crn (syn_cuni (syn_cwecutiso R D S E))) E)
  have p0069 :=
    @g_simpl (.classMem (.cv y) D)
      (.classEq (syn_cdm (syn_cuni (syn_cwecutiso R D S E)))
        (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))
  have p0070 :=
    @g_syl
      (syn_wa (syn_wa (.classMem (.cv y) D)
          (.classEq (syn_cdm (syn_cuni (syn_cwecutiso R D S E)))
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
        (.classEq (syn_crn (syn_cuni (syn_cwecutiso R D S E))) E))
      (syn_wa (.classMem (.cv y) D) (.classEq (syn_cdm (syn_cuni (syn_cwecutiso R D S E)))
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
      (.classMem (.cv y) D) p0068 p0069
  have p0072 :=
    @g_a1i
      (syn_wiso (syn_cuni (syn_cwecutiso R D S E)) R S
        (syn_cdm (syn_cuni (syn_cwecutiso R D S E)))
        (syn_crn (syn_cuni (syn_cwecutiso R D S E))))
      (syn_wa (syn_wa (.classMem (.cv y) D)
          (.classEq (syn_cdm (syn_cuni (syn_cwecutiso R D S E)))
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
        (.classEq (syn_crn (syn_cuni (syn_cwecutiso R D S E))) E))
      p0003
  have p0074 :=
    @g_simpr (.classMem (.cv y) D)
      (.classEq (syn_cdm (syn_cuni (syn_cwecutiso R D S E)))
        (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))
  have p0075 :=
    @g_syl
      (syn_wa (syn_wa (.classMem (.cv y) D)
          (.classEq (syn_cdm (syn_cuni (syn_cwecutiso R D S E)))
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
        (.classEq (syn_crn (syn_cuni (syn_cwecutiso R D S E))) E))
      (syn_wa (.classMem (.cv y) D) (.classEq (syn_cdm (syn_cuni (syn_cwecutiso R D S E)))
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
      (.classEq (syn_cdm (syn_cuni (syn_cwecutiso R D S E)))
        (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))
      p0068 p0074
  have p0076 :=
    @g_isoeq4 (syn_cdm (syn_cuni (syn_cwecutiso R D S E)))
      (syn_crn (syn_cuni (syn_cwecutiso R D S E)))
      (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))) R S
      (syn_cuni (syn_cwecutiso R D S E))
  have p0077 :=
    @g_syl
      (syn_wa (syn_wa (.classMem (.cv y) D)
          (.classEq (syn_cdm (syn_cuni (syn_cwecutiso R D S E)))
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
        (.classEq (syn_crn (syn_cuni (syn_cwecutiso R D S E))) E))
      (.classEq (syn_cdm (syn_cuni (syn_cwecutiso R D S E)))
        (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))
      (syn_wb (syn_wiso (syn_cuni (syn_cwecutiso R D S E)) R S
          (syn_cdm (syn_cuni (syn_cwecutiso R D S E)))
          (syn_crn (syn_cuni (syn_cwecutiso R D S E))))
        (syn_wiso (syn_cuni (syn_cwecutiso R D S E)) R S
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
          (syn_crn (syn_cuni (syn_cwecutiso R D S E)))))
      p0075 p0076
  have p0078 :=
    @g_mpbid
      (syn_wa (syn_wa (.classMem (.cv y) D)
          (.classEq (syn_cdm (syn_cuni (syn_cwecutiso R D S E)))
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
        (.classEq (syn_crn (syn_cuni (syn_cwecutiso R D S E))) E))
      (syn_wiso (syn_cuni (syn_cwecutiso R D S E)) R S
        (syn_cdm (syn_cuni (syn_cwecutiso R D S E)))
        (syn_crn (syn_cuni (syn_cwecutiso R D S E))))
      (syn_wiso (syn_cuni (syn_cwecutiso R D S E)) R S
        (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
        (syn_crn (syn_cuni (syn_cwecutiso R D S E))))
      p0072 p0077
  have p0079 :=
    @g_simpr
      (syn_wa (.classMem (.cv y) D) (.classEq (syn_cdm (syn_cuni (syn_cwecutiso R D S E)))
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
      (.classEq (syn_crn (syn_cuni (syn_cwecutiso R D S E))) E)
  have p0080 :=
    @g_isoeq5 (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
      (syn_crn (syn_cuni (syn_cwecutiso R D S E))) E R S
      (syn_cuni (syn_cwecutiso R D S E))
  have p0081 :=
    @g_syl
      (syn_wa (syn_wa (.classMem (.cv y) D)
          (.classEq (syn_cdm (syn_cuni (syn_cwecutiso R D S E)))
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
        (.classEq (syn_crn (syn_cuni (syn_cwecutiso R D S E))) E))
      (.classEq (syn_crn (syn_cuni (syn_cwecutiso R D S E))) E)
      (syn_wb (syn_wiso (syn_cuni (syn_cwecutiso R D S E)) R S
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
          (syn_crn (syn_cuni (syn_cwecutiso R D S E))))
        (syn_wiso (syn_cuni (syn_cwecutiso R D S E)) R S
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))) E))
      p0079 p0080
  have p0082 :=
    @g_mpbid
      (syn_wa (syn_wa (.classMem (.cv y) D)
          (.classEq (syn_cdm (syn_cuni (syn_cwecutiso R D S E)))
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
        (.classEq (syn_crn (syn_cuni (syn_cwecutiso R D S E))) E))
      (syn_wiso (syn_cuni (syn_cwecutiso R D S E)) R S
        (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
        (syn_crn (syn_cuni (syn_cwecutiso R D S E))))
      (syn_wiso (syn_cuni (syn_cwecutiso R D S E)) R S
        (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))) E)
      p0078 p0081
  have p0083 :=
    @g_isocnv (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))) E
      R S (syn_cuni (syn_cwecutiso R D S E))
  have p0084 :=
    @g_syl
      (syn_wa (syn_wa (.classMem (.cv y) D)
          (.classEq (syn_cdm (syn_cuni (syn_cwecutiso R D S E)))
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
        (.classEq (syn_crn (syn_cuni (syn_cwecutiso R D S E))) E))
      (syn_wiso (syn_cuni (syn_cwecutiso R D S E)) R S
        (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))) E)
      (syn_wiso (syn_ccnv (syn_cuni (syn_cwecutiso R D S E))) S R E
        (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))
      p0082 p0083
  have p0085 :=
    @g_isores2 E
      (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))) S R
      (syn_ccnv (syn_cuni (syn_cwecutiso R D S E)))
  have p0086 :=
    @g_biimpi
      (syn_wiso (syn_ccnv (syn_cuni (syn_cwecutiso R D S E))) S R E
        (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))
      (syn_wiso (syn_ccnv (syn_cuni (syn_cwecutiso R D S E))) S (syn_cin R (syn_cxp
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
        E (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))
      p0085
  have p0087 :=
    @g_syl
      (syn_wa (syn_wa (.classMem (.cv y) D)
          (.classEq (syn_cdm (syn_cuni (syn_cwecutiso R D S E)))
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
        (.classEq (syn_crn (syn_cuni (syn_cwecutiso R D S E))) E))
      (syn_wiso (syn_ccnv (syn_cuni (syn_cwecutiso R D S E))) S R E
        (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))
      (syn_wiso (syn_ccnv (syn_cuni (syn_cwecutiso R D S E))) S (syn_cin R (syn_cxp
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
        E (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))
      p0084 p0086
  have p0088 :=
    @g_cnvex (syn_cuni (syn_cwecutiso R D S E)) hyp_wecomparisonterminalsetfdv_3
  have p0089 :=
    @g_isoeq1 E (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
      S
      (syn_cin R (syn_cxp
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
      (syn_ccnv (syn_cuni (syn_cwecutiso R D S E))) (.cv h)
  have p0090 :=
    @g_spcev
      (syn_wiso (.cv h) S (syn_cin R (syn_cxp
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
        E (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))
      (syn_wiso (syn_ccnv (syn_cuni (syn_cwecutiso R D S E))) S (syn_cin R (syn_cxp
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
        E (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))
      h (syn_ccnv (syn_cuni (syn_cwecutiso R D S E))) dv_cache_0018 dv_cache_0019 p0088
      p0089
  have p0091 :=
    @g_syl
      (syn_wa (syn_wa (.classMem (.cv y) D)
          (.classEq (syn_cdm (syn_cuni (syn_cwecutiso R D S E)))
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
        (.classEq (syn_crn (syn_cuni (syn_cwecutiso R D S E))) E))
      (syn_wiso (syn_ccnv (syn_cuni (syn_cwecutiso R D S E))) S (syn_cin R (syn_cxp
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
        E (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))
      (syn_wex h (syn_wiso (.cv h) S (syn_cin R (syn_cxp
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
          E (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
      p0087 p0090
  have p0092 :=
    @g_jca
      (syn_wa (syn_wa (.classMem (.cv y) D)
          (.classEq (syn_cdm (syn_cuni (syn_cwecutiso R D S E)))
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
        (.classEq (syn_crn (syn_cuni (syn_cwecutiso R D S E))) E))
      (.classMem (.cv y) D)
      (syn_wex h (syn_wiso (.cv h) S (syn_cin R (syn_cxp
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
          E (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
      p0070 p0091
  have p0093 := @g_sneq (.cv x) (.cv y)
  have p0094 :=
    @g_imaeq2d (.classEq (.cv x) (.cv y)) (syn_csn (.cv x)) (syn_csn (.cv y))
      (syn_ccnv (syn_cdif R (syn_cid))) p0093
  have p0095 :=
    @g_ineq2d (.classEq (.cv x) (.cv y))
      (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))
      (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))) D p0094
  have p0099 :=
    @g_xpeq12d (.classEq (.cv x) (.cv y))
      (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
      (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
      (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
      (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))) p0095
      p0095
  have p0100 :=
    @g_ineq2d (.classEq (.cv x) (.cv y))
      (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
        (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))
      (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
        (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))
      R p0099
  have p0101 :=
    @g_isoeq3 E (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
      S
      (syn_cin R (syn_cxp
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))
      (syn_cin R (syn_cxp
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
      (.cv h)
  have p0102 :=
    @g_syl (.classEq (.cv x) (.cv y))
      (.classEq (syn_cin R (syn_cxp
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))
        (syn_cin R (syn_cxp
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))))
      (syn_wb (syn_wiso (.cv h) S (syn_cin R (syn_cxp
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))
          E (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))
        (syn_wiso (.cv h) S (syn_cin R (syn_cxp
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
          E (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))
      p0100 p0101
  have p0106 :=
    @g_isoeq5 E (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
      (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))) S
      (syn_cin R (syn_cxp
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
      (.cv h)
  have p0107 :=
    @g_syl (.classEq (.cv x) (.cv y))
      (.classEq (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
        (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))
      (syn_wb (syn_wiso (.cv h) S (syn_cin R (syn_cxp
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
          E (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))
        (syn_wiso (.cv h) S (syn_cin R (syn_cxp
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
          E (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
      p0095 p0106
  have p0108 :=
    @g_bitrd (.classEq (.cv x) (.cv y))
      (syn_wiso (.cv h) S (syn_cin R (syn_cxp
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))
        E (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))
      (syn_wiso (.cv h) S (syn_cin R (syn_cxp
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
        E (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))
      (syn_wiso (.cv h) S (syn_cin R (syn_cxp
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
        E (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))
      p0102 p0107
  have p0109 :=
    @g_exbidv (.classEq (.cv x) (.cv y))
      (syn_wiso (.cv h) S (syn_cin R (syn_cxp
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))
        E (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))
      (syn_wiso (.cv h) S (syn_cin R (syn_cxp
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
        E (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))
      h dv_cache_0020 p0108
  have p0110 :=
    @g_rspcev
      (syn_wex h (syn_wiso (.cv h) S (syn_cin R (syn_cxp
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))
          E (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))
      (syn_wex h (syn_wiso (.cv h) S (syn_cin R (syn_cxp
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
          E (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
      x (.cv y) D dv_cache_0021 dv_cache_0022 dv_cache_0023 p0109
  have p0111 :=
    @g_syl
      (syn_wa (syn_wa (.classMem (.cv y) D)
          (.classEq (syn_cdm (syn_cuni (syn_cwecutiso R D S E)))
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
        (.classEq (syn_crn (syn_cuni (syn_cwecutiso R D S E))) E))
      (syn_wa (.classMem (.cv y) D) (syn_wex h (syn_wiso (.cv h) S (syn_cin R (syn_cxp
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))) E
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))))
      (syn_wrex x D (syn_wex h (syn_wiso (.cv h) S (syn_cin R (syn_cxp
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) E
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))))
      p0092 p0110
  have p0112 :=
    @g_n_3mix3
      (syn_wrex x D (syn_wex h (syn_wiso (.cv h) S (syn_cin R (syn_cxp
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) E
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))))
      (syn_wex h (syn_wiso (.cv h) R S D E))
      (syn_wrex x E (syn_wex h (syn_wiso (.cv h) R (syn_cin S (syn_cxp
                (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv x))))
                (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv x)))))) D
            (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv x)))))))
  have p0113 :=
    @g_syl
      (syn_wa (syn_wa (.classMem (.cv y) D)
          (.classEq (syn_cdm (syn_cuni (syn_cwecutiso R D S E)))
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
        (.classEq (syn_crn (syn_cuni (syn_cwecutiso R D S E))) E))
      (syn_wrex x D (syn_wex h (syn_wiso (.cv h) S (syn_cin R (syn_cxp
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) E
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))))
      (syn_w3o (syn_wex h (syn_wiso (.cv h) R S D E)) (syn_wrex x E (syn_wex h
            (syn_wiso (.cv h) R (syn_cin S (syn_cxp (syn_cin E
                    (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv x)))) (syn_cin E
                    (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv x)))))) D
              (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv x)))))))
        (syn_wrex x D (syn_wex h (syn_wiso (.cv h) S (syn_cin R (syn_cxp (syn_cin D
                    (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D
                    (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) E
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))))
      p0111 p0112
  have p0114 :=
    @g_ex
      (syn_wa (.classMem (.cv y) D) (.classEq (syn_cdm (syn_cuni (syn_cwecutiso R D S E)))
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
      (.classEq (syn_crn (syn_cuni (syn_cwecutiso R D S E))) E)
      (syn_w3o (syn_wex h (syn_wiso (.cv h) R S D E)) (syn_wrex x E (syn_wex h
            (syn_wiso (.cv h) R (syn_cin S (syn_cxp (syn_cin E
                    (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv x)))) (syn_cin E
                    (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv x)))))) D
              (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv x)))))))
        (syn_wrex x D (syn_wex h (syn_wiso (.cv h) S (syn_cin R (syn_cxp (syn_cin D
                    (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D
                    (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) E
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))))
      p0113
  have p0115 :=
    @g_simpl
      (syn_wa (syn_wa (.classMem (.cv y) D)
          (.classEq (syn_cdm (syn_cuni (syn_cwecutiso R D S E)))
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
        (.classMem (.cv u) E))
      (.classEq (syn_crn (syn_cuni (syn_cwecutiso R D S E)))
        (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u)))))
  have p0116 :=
    @g_simpl
      (syn_wa (.classMem (.cv y) D) (.classEq (syn_cdm (syn_cuni (syn_cwecutiso R D S E)))
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
      (.classMem (.cv u) E)
  have p0117 :=
    @g_syl
      (syn_wa (syn_wa (syn_wa (.classMem (.cv y) D)
            (.classEq (syn_cdm (syn_cuni (syn_cwecutiso R D S E)))
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
          (.classMem (.cv u) E)) (.classEq (syn_crn (syn_cuni (syn_cwecutiso R D S E)))
          (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))))
      (syn_wa (syn_wa (.classMem (.cv y) D)
          (.classEq (syn_cdm (syn_cuni (syn_cwecutiso R D S E)))
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
        (.classMem (.cv u) E))
      (syn_wa (.classMem (.cv y) D) (.classEq (syn_cdm (syn_cuni (syn_cwecutiso R D S E)))
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
      p0115 p0116
  have p0119 :=
    @g_syl
      (syn_wa (syn_wa (syn_wa (.classMem (.cv y) D)
            (.classEq (syn_cdm (syn_cuni (syn_cwecutiso R D S E)))
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
          (.classMem (.cv u) E)) (.classEq (syn_crn (syn_cuni (syn_cwecutiso R D S E)))
          (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))))
      (syn_wa (.classMem (.cv y) D) (.classEq (syn_cdm (syn_cuni (syn_cwecutiso R D S E)))
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
      (.classMem (.cv y) D) p0117 p0069
  have p0121 :=
    @g_simpr
      (syn_wa (.classMem (.cv y) D) (.classEq (syn_cdm (syn_cuni (syn_cwecutiso R D S E)))
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
      (.classMem (.cv u) E)
  have p0122 :=
    @g_syl
      (syn_wa (syn_wa (syn_wa (.classMem (.cv y) D)
            (.classEq (syn_cdm (syn_cuni (syn_cwecutiso R D S E)))
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
          (.classMem (.cv u) E)) (.classEq (syn_crn (syn_cuni (syn_cwecutiso R D S E)))
          (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))))
      (syn_wa (syn_wa (.classMem (.cv y) D)
          (.classEq (syn_cdm (syn_cuni (syn_cwecutiso R D S E)))
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
        (.classMem (.cv u) E))
      (.classMem (.cv u) E) p0115 p0121
  have p0123 :=
    @g_jca
      (syn_wa (syn_wa (syn_wa (.classMem (.cv y) D)
            (.classEq (syn_cdm (syn_cuni (syn_cwecutiso R D S E)))
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
          (.classMem (.cv u) E)) (.classEq (syn_crn (syn_cuni (syn_cwecutiso R D S E)))
          (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))))
      (.classMem (.cv y) D) (.classMem (.cv u) E) p0119 p0122
  have p0124 := @g_strictsegnel y D R
  have p0125 :=
    @g_a1i
      (.neg (.classMem (.cv y)
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
      (syn_wa (syn_wa (syn_wa (.classMem (.cv y) D)
            (.classEq (syn_cdm (syn_cuni (syn_cwecutiso R D S E)))
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
          (.classMem (.cv u) E)) (.classEq (syn_crn (syn_cuni (syn_cwecutiso R D S E)))
          (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))))
      p0124
  have p0130 :=
    @g_syl
      (syn_wa (syn_wa (syn_wa (.classMem (.cv y) D)
            (.classEq (syn_cdm (syn_cuni (syn_cwecutiso R D S E)))
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
          (.classMem (.cv u) E)) (.classEq (syn_crn (syn_cuni (syn_cwecutiso R D S E)))
          (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))))
      (syn_wa (.classMem (.cv y) D) (.classEq (syn_cdm (syn_cuni (syn_cwecutiso R D S E)))
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
      (.classEq (syn_cdm (syn_cuni (syn_cwecutiso R D S E)))
        (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))
      p0117 p0074
  have p0131 :=
    @g_eleq2d
      (syn_wa (syn_wa (syn_wa (.classMem (.cv y) D)
            (.classEq (syn_cdm (syn_cuni (syn_cwecutiso R D S E)))
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
          (.classMem (.cv u) E)) (.classEq (syn_crn (syn_cuni (syn_cwecutiso R D S E)))
          (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))))
      (syn_cdm (syn_cuni (syn_cwecutiso R D S E)))
      (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))) (.cv y)
      p0130
  have p0132 :=
    @g_notbid
      (syn_wa (syn_wa (syn_wa (.classMem (.cv y) D)
            (.classEq (syn_cdm (syn_cuni (syn_cwecutiso R D S E)))
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
          (.classMem (.cv u) E)) (.classEq (syn_crn (syn_cuni (syn_cwecutiso R D S E)))
          (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))))
      (.classMem (.cv y) (syn_cdm (syn_cuni (syn_cwecutiso R D S E))))
      (.classMem (.cv y)
        (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))
      p0131
  have p0133 :=
    @g_mpbird
      (syn_wa (syn_wa (syn_wa (.classMem (.cv y) D)
            (.classEq (syn_cdm (syn_cuni (syn_cwecutiso R D S E)))
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
          (.classMem (.cv u) E)) (.classEq (syn_crn (syn_cuni (syn_cwecutiso R D S E)))
          (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))))
      (.neg (.classMem (.cv y) (syn_cdm (syn_cuni (syn_cwecutiso R D S E)))))
      (.neg (.classMem (.cv y)
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
      p0125 p0132
  have p0134 :=
    @g_a1i (syn_wbr R (syn_cwe) D)
      (syn_wa (syn_wa (syn_wa (.classMem (.cv y) D)
            (.classEq (syn_cdm (syn_cuni (syn_cwecutiso R D S E)))
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
          (.classMem (.cv u) E)) (.classEq (syn_crn (syn_cuni (syn_cwecutiso R D S E)))
          (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))))
      hyp_wecomparisonterminalsetfdv_1
  have p0135 :=
    @g_a1i (syn_wbr S (syn_cwe) E)
      (syn_wa (syn_wa (syn_wa (.classMem (.cv y) D)
            (.classEq (syn_cdm (syn_cuni (syn_cwecutiso R D S E)))
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
          (.classMem (.cv u) E)) (.classEq (syn_crn (syn_cuni (syn_cwecutiso R D S E)))
          (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))))
      hyp_wecomparisonterminalsetfdv_2
  have p0136 :=
    @g_jca
      (syn_wa (syn_wa (syn_wa (.classMem (.cv y) D)
            (.classEq (syn_cdm (syn_cuni (syn_cwecutiso R D S E)))
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
          (.classMem (.cv u) E)) (.classEq (syn_crn (syn_cuni (syn_cwecutiso R D S E)))
          (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))))
      (syn_wbr R (syn_cwe) D) (syn_wbr S (syn_cwe) E) p0134 p0135
  have p0146 :=
    @g_jca
      (syn_wa (syn_wa (syn_wa (.classMem (.cv y) D)
            (.classEq (syn_cdm (syn_cuni (syn_cwecutiso R D S E)))
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
          (.classMem (.cv u) E)) (.classEq (syn_crn (syn_cuni (syn_cwecutiso R D S E)))
          (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))))
      (syn_wa (syn_wbr R (syn_cwe) D) (syn_wbr S (syn_cwe) E))
      (syn_wa (.classMem (.cv y) D) (.classMem (.cv u) E)) p0136 p0123
  have p0148 :=
    @g_a1i
      (syn_wiso (syn_cuni (syn_cwecutiso R D S E)) R S
        (syn_cdm (syn_cuni (syn_cwecutiso R D S E)))
        (syn_crn (syn_cuni (syn_cwecutiso R D S E))))
      (syn_wa (syn_wa (syn_wa (.classMem (.cv y) D)
            (.classEq (syn_cdm (syn_cuni (syn_cwecutiso R D S E)))
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
          (.classMem (.cv u) E)) (.classEq (syn_crn (syn_cuni (syn_cwecutiso R D S E)))
          (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))))
      p0003
  have p0155 :=
    @g_syl
      (syn_wa (syn_wa (syn_wa (.classMem (.cv y) D)
            (.classEq (syn_cdm (syn_cuni (syn_cwecutiso R D S E)))
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
          (.classMem (.cv u) E)) (.classEq (syn_crn (syn_cuni (syn_cwecutiso R D S E)))
          (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))))
      (.classEq (syn_cdm (syn_cuni (syn_cwecutiso R D S E)))
        (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))
      (syn_wb (syn_wiso (syn_cuni (syn_cwecutiso R D S E)) R S
          (syn_cdm (syn_cuni (syn_cwecutiso R D S E)))
          (syn_crn (syn_cuni (syn_cwecutiso R D S E))))
        (syn_wiso (syn_cuni (syn_cwecutiso R D S E)) R S
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
          (syn_crn (syn_cuni (syn_cwecutiso R D S E)))))
      p0130 p0076
  have p0156 :=
    @g_mpbid
      (syn_wa (syn_wa (syn_wa (.classMem (.cv y) D)
            (.classEq (syn_cdm (syn_cuni (syn_cwecutiso R D S E)))
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
          (.classMem (.cv u) E)) (.classEq (syn_crn (syn_cuni (syn_cwecutiso R D S E)))
          (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))))
      (syn_wiso (syn_cuni (syn_cwecutiso R D S E)) R S
        (syn_cdm (syn_cuni (syn_cwecutiso R D S E)))
        (syn_crn (syn_cuni (syn_cwecutiso R D S E))))
      (syn_wiso (syn_cuni (syn_cwecutiso R D S E)) R S
        (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
        (syn_crn (syn_cuni (syn_cwecutiso R D S E))))
      p0148 p0155
  have p0157 :=
    @g_simpr
      (syn_wa (syn_wa (.classMem (.cv y) D)
          (.classEq (syn_cdm (syn_cuni (syn_cwecutiso R D S E)))
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
        (.classMem (.cv u) E))
      (.classEq (syn_crn (syn_cuni (syn_cwecutiso R D S E)))
        (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u)))))
  have p0158 :=
    @g_isoeq5 (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
      (syn_crn (syn_cuni (syn_cwecutiso R D S E)))
      (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u)))) R S
      (syn_cuni (syn_cwecutiso R D S E))
  have p0159 :=
    @g_syl
      (syn_wa (syn_wa (syn_wa (.classMem (.cv y) D)
            (.classEq (syn_cdm (syn_cuni (syn_cwecutiso R D S E)))
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
          (.classMem (.cv u) E)) (.classEq (syn_crn (syn_cuni (syn_cwecutiso R D S E)))
          (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))))
      (.classEq (syn_crn (syn_cuni (syn_cwecutiso R D S E)))
        (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u)))))
      (syn_wb (syn_wiso (syn_cuni (syn_cwecutiso R D S E)) R S
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
          (syn_crn (syn_cuni (syn_cwecutiso R D S E))))
        (syn_wiso (syn_cuni (syn_cwecutiso R D S E)) R S
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
          (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))))
      p0157 p0158
  have p0160 :=
    @g_mpbid
      (syn_wa (syn_wa (syn_wa (.classMem (.cv y) D)
            (.classEq (syn_cdm (syn_cuni (syn_cwecutiso R D S E)))
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
          (.classMem (.cv u) E)) (.classEq (syn_crn (syn_cuni (syn_cwecutiso R D S E)))
          (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))))
      (syn_wiso (syn_cuni (syn_cwecutiso R D S E)) R S
        (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
        (syn_crn (syn_cuni (syn_cwecutiso R D S E))))
      (syn_wiso (syn_cuni (syn_cwecutiso R D S E)) R S
        (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
        (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u)))))
      p0156 p0159
  have p0161 :=
    @g_jca
      (syn_wa (syn_wa (syn_wa (.classMem (.cv y) D)
            (.classEq (syn_cdm (syn_cuni (syn_cwecutiso R D S E)))
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
          (.classMem (.cv u) E)) (.classEq (syn_crn (syn_cuni (syn_cwecutiso R D S E)))
          (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))))
      (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (syn_wbr S (syn_cwe) E))
        (syn_wa (.classMem (.cv y) D) (.classMem (.cv u) E)))
      (syn_wiso (syn_cuni (syn_cwecutiso R D S E)) R S
        (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
        (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u)))))
      p0146 p0160
  have p0162 := @g_wecutisoaddpairisondv y u D R S E (syn_cuni (syn_cwecutiso R D S E))
  have p0163 :=
    @g_syl
      (syn_wa (syn_wa (syn_wa (.classMem (.cv y) D)
            (.classEq (syn_cdm (syn_cuni (syn_cwecutiso R D S E)))
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
          (.classMem (.cv u) E)) (.classEq (syn_crn (syn_cuni (syn_cwecutiso R D S E)))
          (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))))
      (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (syn_wbr S (syn_cwe) E))
          (syn_wa (.classMem (.cv y) D) (.classMem (.cv u) E)))
        (syn_wiso (syn_cuni (syn_cwecutiso R D S E)) R S
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
          (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))))
      (syn_wiso
        (syn_cun (syn_cuni (syn_cwecutiso R D S E)) (syn_csn (syn_cop (.cv y) (.cv u)))) R S
        (syn_cun (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
          (syn_csn (.cv y))) (syn_cun
          (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))
          (syn_csn (.cv u))))
      p0161 p0162
  have p0164 :=
    @g_jca
      (syn_wa (syn_wa (syn_wa (.classMem (.cv y) D)
            (.classEq (syn_cdm (syn_cuni (syn_cwecutiso R D S E)))
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
          (.classMem (.cv u) E)) (.classEq (syn_crn (syn_cuni (syn_cwecutiso R D S E)))
          (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))))
      (.neg (.classMem (.cv y) (syn_cdm (syn_cuni (syn_cwecutiso R D S E)))))
      (syn_wiso
        (syn_cun (syn_cuni (syn_cwecutiso R D S E)) (syn_csn (syn_cop (.cv y) (.cv u)))) R S
        (syn_cun (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
          (syn_csn (.cv y))) (syn_cun
          (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))
          (syn_csn (.cv u))))
      p0133 p0163
  have p0165 :=
    @g_jca
      (syn_wa (syn_wa (syn_wa (.classMem (.cv y) D)
            (.classEq (syn_cdm (syn_cuni (syn_cwecutiso R D S E)))
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
          (.classMem (.cv u) E)) (.classEq (syn_crn (syn_cuni (syn_cwecutiso R D S E)))
          (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))))
      (syn_wa (.classMem (.cv y) D) (.classMem (.cv u) E))
      (syn_wa (.neg (.classMem (.cv y) (syn_cdm (syn_cuni (syn_cwecutiso R D S E))))) (syn_wiso
          (syn_cun (syn_cuni (syn_cwecutiso R D S E)) (syn_csn (syn_cop (.cv y) (.cv u)))) R S
          (syn_cun (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
            (syn_csn (.cv y))) (syn_cun
            (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))
            (syn_csn (.cv u)))))
      p0123 p0164
  have p0166 :=
    @g_wecutisoextendedterminaldfdv x y u D R S h E dv_cache_0024 dv_cache_0005
      dv_cache_0022 dv_cache_0001 dv_cache_0025 dv_cache_0006 dv_cache_0014 dv_cache_0002
      dv_cache_0026 dv_cache_0007 dv_cache_0027 dv_cache_0003 dv_cache_0028 dv_cache_0008
      dv_cache_0029 dv_cache_0004 dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033
      dv_cache_0034 dv_cache_0035 hyp_wecomparisonterminalsetfdv_1
      hyp_wecomparisonterminalsetfdv_2 hyp_wecomparisonterminalsetfdv_3
  have p0167 :=
    @g_syl
      (syn_wa (syn_wa (syn_wa (.classMem (.cv y) D)
            (.classEq (syn_cdm (syn_cuni (syn_cwecutiso R D S E)))
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
          (.classMem (.cv u) E)) (.classEq (syn_crn (syn_cuni (syn_cwecutiso R D S E)))
          (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))))
      (syn_wa (syn_wa (.classMem (.cv y) D) (.classMem (.cv u) E))
        (syn_wa (.neg (.classMem (.cv y) (syn_cdm (syn_cuni (syn_cwecutiso R D S E)))))
          (syn_wiso (syn_cun (syn_cuni (syn_cwecutiso R D S E))
              (syn_csn (syn_cop (.cv y) (.cv u)))) R S (syn_cun
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
              (syn_csn (.cv y))) (syn_cun
              (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))
              (syn_csn (.cv u))))))
      (syn_w3o (syn_wex h (syn_wiso (.cv h) R S D E)) (syn_wrex x E (syn_wex h
            (syn_wiso (.cv h) R (syn_cin S (syn_cxp (syn_cin E
                    (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv x)))) (syn_cin E
                    (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv x)))))) D
              (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv x)))))))
        (syn_wrex x D (syn_wex h (syn_wiso (.cv h) S (syn_cin R (syn_cxp (syn_cin D
                    (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D
                    (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) E
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))))
      p0165 p0166
  have p0168 :=
    @g_ex
      (syn_wa (syn_wa (.classMem (.cv y) D)
          (.classEq (syn_cdm (syn_cuni (syn_cwecutiso R D S E)))
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
        (.classMem (.cv u) E))
      (.classEq (syn_crn (syn_cuni (syn_cwecutiso R D S E)))
        (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u)))))
      (syn_w3o (syn_wex h (syn_wiso (.cv h) R S D E)) (syn_wrex x E (syn_wex h
            (syn_wiso (.cv h) R (syn_cin S (syn_cxp (syn_cin E
                    (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv x)))) (syn_cin E
                    (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv x)))))) D
              (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv x)))))))
        (syn_wrex x D (syn_wex h (syn_wiso (.cv h) S (syn_cin R (syn_cxp (syn_cin D
                    (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D
                    (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) E
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))))
      p0167
  have p0169 :=
    @g_rexlimdva
      (syn_wa (.classMem (.cv y) D) (.classEq (syn_cdm (syn_cuni (syn_cwecutiso R D S E)))
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
      (.classEq (syn_crn (syn_cuni (syn_cwecutiso R D S E)))
        (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u)))))
      (syn_w3o (syn_wex h (syn_wiso (.cv h) R S D E)) (syn_wrex x E (syn_wex h
            (syn_wiso (.cv h) R (syn_cin S (syn_cxp (syn_cin E
                    (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv x)))) (syn_cin E
                    (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv x)))))) D
              (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv x)))))))
        (syn_wrex x D (syn_wex h (syn_wiso (.cv h) S (syn_cin R (syn_cxp (syn_cin D
                    (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D
                    (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) E
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))))
      u E dv_cache_0016 dv_cache_0036 p0168
  have p0170 :=
    @g_jaod
      (syn_wa (.classMem (.cv y) D) (.classEq (syn_cdm (syn_cuni (syn_cwecutiso R D S E)))
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
      (.classEq (syn_crn (syn_cuni (syn_cwecutiso R D S E))) E)
      (syn_w3o (syn_wex h (syn_wiso (.cv h) R S D E)) (syn_wrex x E (syn_wex h
            (syn_wiso (.cv h) R (syn_cin S (syn_cxp (syn_cin E
                    (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv x)))) (syn_cin E
                    (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv x)))))) D
              (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv x)))))))
        (syn_wrex x D (syn_wex h (syn_wiso (.cv h) S (syn_cin R (syn_cxp (syn_cin D
                    (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D
                    (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) E
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))))
      (syn_wrex u E (.classEq (syn_crn (syn_cuni (syn_cwecutiso R D S E)))
          (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u))))))
      p0114 p0169
  have p0171 :=
    @g_mpd
      (syn_wa (.classMem (.cv y) D) (.classEq (syn_cdm (syn_cuni (syn_cwecutiso R D S E)))
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
      (syn_wo (.classEq (syn_crn (syn_cuni (syn_cwecutiso R D S E))) E) (syn_wrex u E
          (.classEq (syn_crn (syn_cuni (syn_cwecutiso R D S E)))
            (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv u)))))))
      (syn_w3o (syn_wex h (syn_wiso (.cv h) R S D E)) (syn_wrex x E (syn_wex h
            (syn_wiso (.cv h) R (syn_cin S (syn_cxp (syn_cin E
                    (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv x)))) (syn_cin E
                    (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv x)))))) D
              (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv x)))))))
        (syn_wrex x D (syn_wex h (syn_wiso (.cv h) S (syn_cin R (syn_cxp (syn_cin D
                    (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D
                    (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) E
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))))
      p0067 p0170
  have p0172 :=
    @g_ex (.classMem (.cv y) D)
      (.classEq (syn_cdm (syn_cuni (syn_cwecutiso R D S E)))
        (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))
      (syn_w3o (syn_wex h (syn_wiso (.cv h) R S D E)) (syn_wrex x E (syn_wex h
            (syn_wiso (.cv h) R (syn_cin S (syn_cxp (syn_cin E
                    (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv x)))) (syn_cin E
                    (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv x)))))) D
              (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv x)))))))
        (syn_wrex x D (syn_wex h (syn_wiso (.cv h) S (syn_cin R (syn_cxp (syn_cin D
                    (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D
                    (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) E
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))))
      p0171
  have p0173 :=
    @g_rexlimiv
      (.classEq (syn_cdm (syn_cuni (syn_cwecutiso R D S E)))
        (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))
      (syn_w3o (syn_wex h (syn_wiso (.cv h) R S D E)) (syn_wrex x E (syn_wex h
            (syn_wiso (.cv h) R (syn_cin S (syn_cxp (syn_cin E
                    (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv x)))) (syn_cin E
                    (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv x)))))) D
              (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv x)))))))
        (syn_wrex x D (syn_wex h (syn_wiso (.cv h) S (syn_cin R (syn_cxp (syn_cin D
                    (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D
                    (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) E
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))))
      y D dv_cache_0037 p0172
  have p0174 :=
    @g_jaoi (.classEq (syn_cdm (syn_cuni (syn_cwecutiso R D S E))) D)
      (syn_w3o (syn_wex h (syn_wiso (.cv h) R S D E)) (syn_wrex x E (syn_wex h
            (syn_wiso (.cv h) R (syn_cin S (syn_cxp (syn_cin E
                    (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv x)))) (syn_cin E
                    (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv x)))))) D
              (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv x)))))))
        (syn_wrex x D (syn_wex h (syn_wiso (.cv h) S (syn_cin R (syn_cxp (syn_cin D
                    (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D
                    (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) E
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))))
      (syn_wrex y D (.classEq (syn_cdm (syn_cuni (syn_cwecutiso R D S E)))
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
      p0065 p0173
  have p0175 := Nominal.mp p0000 p0174
  exact p0175


end NFChoice.DirectNominalPrf.WPPReplay

end

/-! Certificates from `NominalWPPReplayChunk016Compact001Part037`. -/


section

namespace NFChoice.DirectNominalPrf.WPPReplay

open scoped Fol
open NFChoice.Foundation
open NFChoice.SemanticCore
open NFChoice.ReplaySupport
open NFChoice.Compiler.CompactSourceSyntax

@[expose]
noncomputable def g_wecomparisonterminalfdv (x : Var) (D : Class) (R : Class) (S : Class)
    (h : Var) (E : Class) (dv_D_h : h ∉ D.fv) (dv_D_x : x ∉ D.fv) (dv_E_h : h ∉ E.fv)
    (dv_E_x : x ∉ E.fv) (dv_R_h : h ∉ R.fv) (dv_R_x : x ∉ R.fv) (dv_S_h : h ∉ S.fv)
    (dv_S_x : x ∉ S.fv) (dv_h_x : h ≠ x)
    (hyp_wecomparisonterminalfdv_1 : Nominal.NPrf (syn_wbr R (syn_cwe) D))
    (hyp_wecomparisonterminalfdv_2 : Nominal.NPrf (syn_wbr S (syn_cwe) E)) :
    Nominal.NPrf
      (syn_w3o (syn_wex h (syn_wiso (.cv h) R S D E)) (syn_wrex x E (syn_wex h
            (syn_wiso (.cv h) R (syn_cin S (syn_cxp (syn_cin E
                    (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv x)))) (syn_cin E
                    (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv x)))))) D
              (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv x)))))))
        (syn_wrex x D (syn_wex h (syn_wiso (.cv h) S (syn_cin R (syn_cxp (syn_cin D
                    (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D
                    (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) E
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))))) :=
  by
  have dv_cache_0001 : h ∉ (D).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : h ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_D_h, not_false_eq_true])
  have dv_cache_0002 : x ∉ (D).fv :=
    by
    clear dv_cache_0001
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_D_x, not_false_eq_true])
  have dv_cache_0003 : h ∉ (E).fv :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact
      (by
        have compact_fv_not_mem_empty : h ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_E_h, not_false_eq_true])
  have dv_cache_0004 : x ∉ (E).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_E_x, not_false_eq_true])
  have dv_cache_0005 : h ∉ (R).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact
      (by
        have compact_fv_not_mem_empty : h ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_R_h, not_false_eq_true])
  have dv_cache_0006 : x ∉ (R).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_R_x, not_false_eq_true])
  have dv_cache_0007 : h ∉ (S).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006
    exact
      (by
        have compact_fv_not_mem_empty : h ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_S_h, not_false_eq_true])
  have dv_cache_0008 : x ∉ (S).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_S_x, not_false_eq_true])
  have dv_cache_0009 : h ≠ x :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008
    exact (show h ≠ x from (by exact dv_h_x))
  have p0000 :=
    @g_wecutisouniex D R S E hyp_wecomparisonterminalfdv_1 hyp_wecomparisonterminalfdv_2
  have p0001 :=
    @g_wecomparisonterminalsetfdv x D R S h E dv_cache_0001 dv_cache_0002 dv_cache_0003
      dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009
      hyp_wecomparisonterminalfdv_1 hyp_wecomparisonterminalfdv_2 p0000
  exact p0001

@[expose]
noncomputable def g_weisoexnceqclfdv (A : Class) (B : Class) (T : Class) (U : Class)
    (h : Var) (dv_A_h : h ∉ A.fv) (dv_B_h : h ∉ B.fv) :
    Nominal.NPrf
      (.imp (syn_wex h (syn_wiso (.cv h) T U A B)) (.classEq (syn_cnc A) (syn_cnc B))) :=
  by
  have dv_cache_0001 : h ∉ ((Wff.classEq (syn_cnc A) (syn_cnc B))).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : h ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnc, Finset.mem_union, dv_A_h,
          dv_B_h, or_false, not_false_eq_true])
  have p0000 := @g_isof1o A B T U (.cv h)
  have p0001 := @g_vex h
  have p0002 := @g_f1oen A B (.cv h) p0001
  have p0003 :=
    @g_syl (syn_wiso (.cv h) T U A B) (syn_wf1o (.cv h) A B) (syn_wbr A (syn_cen) B) p0000
      p0002
  have p0008 := @g_breldm A B (syn_cen)
  have p0009 :=
    @g_syl (syn_wiso (.cv h) T U A B) (syn_wbr A (syn_cen) B)
      (.classMem A (syn_cdm (syn_cen))) p0003 p0008
  have p0010 := @g_dmen
  have p0011 := @g_eleq2i (syn_cdm (syn_cen)) (syn_cvv) A p0010
  have p0012 := @g_biimpi (.classMem A (syn_cdm (syn_cen))) (.classMem A (syn_cvv)) p0011
  have p0013 :=
    @g_syl (syn_wiso (.cv h) T U A B) (.classMem A (syn_cdm (syn_cen)))
      (.classMem A (syn_cvv)) p0009 p0012
  have p0014 := @g_eqncg A B (syn_cvv)
  have p0015 :=
    @g_syl (syn_wiso (.cv h) T U A B) (.classMem A (syn_cvv))
      (syn_wb (.classEq (syn_cnc A) (syn_cnc B)) (syn_wbr A (syn_cen) B)) p0013 p0014
  have p0016 :=
    @g_mpbird (syn_wiso (.cv h) T U A B) (.classEq (syn_cnc A) (syn_cnc B))
      (syn_wbr A (syn_cen) B) p0003 p0015
  have p0017 :=
    @g_exlimiv (syn_wiso (.cv h) T U A B) (.classEq (syn_cnc A) (syn_cnc B)) h
      dv_cache_0001 p0016
  exact p0017

@[expose]
noncomputable def g_wecomparisonforwardnclecclfdv (x : Var) (D : Class) (R : Class)
    (S : Class) (h : Var) (E : Class) (dv_D_h : h ∉ D.fv) (dv_D_x : x ∉ D.fv)
    (dv_E_h : h ∉ E.fv) (dv_E_x : x ∉ E.fv) (_dv_R_h : h ∉ R.fv) (_dv_R_x : x ∉ R.fv)
    (dv_S_h : h ∉ S.fv) (_dv_S_x : x ∉ S.fv) (dv_h_x : h ≠ x)
    (hyp_wecomparisonforwardnclecclfdv_1 : Nominal.NPrf (syn_wbr S (syn_cwe) E)) :
    Nominal.NPrf
      (.imp (syn_wo (syn_wex h (syn_wiso (.cv h) R S D E)) (syn_wrex x E (syn_wex h
              (syn_wiso (.cv h) R (syn_cin S (syn_cxp (syn_cin E
                      (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv x)))) (syn_cin E
                      (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv x)))))) D
                (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv x))))))))
        (syn_wbr (syn_cnc D) (syn_clec) (syn_cnc E))) :=
  by
  have dv_cache_0001 : h ∉ (D).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : h ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_D_h, not_false_eq_true])
  have dv_cache_0002 : h ∉ (E).fv :=
    by
    clear dv_cache_0001
    exact
      (by
        have compact_fv_not_mem_empty : h ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_E_h, not_false_eq_true])
  have dv_cache_0003 :
    h ∉ ((syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv x))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact
      (by
        have compact_fv_not_mem_empty : h ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cima,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdif,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cid,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, dv_E_h, dv_S_h, dv_h_x, compact_fv_not_mem_empty,
          or_false, not_false_eq_true])
  have dv_cache_0004 : x ∉ ((syn_wbr (syn_cnc D) (syn_clec) (syn_cnc E))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnc,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_clec, Finset.mem_union, dv_D_x,
          dv_E_x, compact_fv_not_mem_empty, or_false, not_false_eq_true])
  have p0000 := @g_brex S E (syn_cwe)
  have p0001 := Nominal.mp hyp_wecomparisonforwardnclecclfdv_1 p0000
  have p0002 := @g_simpri (.classMem S (syn_cvv)) (.classMem E (syn_cvv)) p0001
  have p0003 := @g_ncelncsi E p0002
  have p0004 := @g_nclecid (syn_cnc E)
  have p0005 := Nominal.mp p0003 p0004
  have p0006 := @g_weisoexnceqclfdv D E R S h dv_cache_0001 dv_cache_0002
  have p0007 :=
    @g_breq1d (syn_wex h (syn_wiso (.cv h) R S D E)) (syn_cnc D) (syn_cnc E) (syn_cnc E)
      (syn_clec) p0006
  have p0008 :=
    @g_mpbiri (syn_wex h (syn_wiso (.cv h) R S D E))
      (syn_wbr (syn_cnc D) (syn_clec) (syn_cnc E))
      (syn_wbr (syn_cnc E) (syn_clec) (syn_cnc E)) p0005 p0007
  have p0009 := @g_inss1 E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv x)))
  have p0015 := @g_simpli (.classMem S (syn_cvv)) (.classMem E (syn_cvv)) p0001
  have p0016 := @g_idex
  have p0017 := @g_difex S (syn_cid) p0015 p0016
  have p0018 := @g_cnvex (syn_cdif S (syn_cid)) p0017
  have p0019 := @g_snex (.cv x)
  have p0020 := @g_imaex (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv x)) p0018 p0019
  have p0021 :=
    @g_inex E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv x))) p0002 p0020
  have p0025 :=
    @g_nclec (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv x)))) E
      p0021 p0002
  have p0026 := Nominal.mp p0009 p0025
  have p0027 :=
    @g_weisoexnceqclfdv D
      (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv x)))) R
      (syn_cin S (syn_cxp
          (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv x))))
          (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv x))))))
      h dv_cache_0001 dv_cache_0003
  have p0028 :=
    @g_breq1d
      (syn_wex h (syn_wiso (.cv h) R (syn_cin S (syn_cxp
              (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv x))))
              (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv x))))))
          D (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv x))))))
      (syn_cnc D)
      (syn_cnc (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv x)))))
      (syn_cnc E) (syn_clec) p0027
  have p0029 :=
    @g_mpbiri
      (syn_wex h (syn_wiso (.cv h) R (syn_cin S (syn_cxp
              (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv x))))
              (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv x))))))
          D (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv x))))))
      (syn_wbr (syn_cnc D) (syn_clec) (syn_cnc E))
      (syn_wbr (syn_cnc
          (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv x)))))
        (syn_clec) (syn_cnc E))
      p0026 p0028
  have p0030 :=
    @g_rexlimivw
      (syn_wex h (syn_wiso (.cv h) R (syn_cin S (syn_cxp
              (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv x))))
              (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv x))))))
          D (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv x))))))
      (syn_wbr (syn_cnc D) (syn_clec) (syn_cnc E)) x E dv_cache_0004 p0029
  have p0031 :=
    @g_jaoi (syn_wex h (syn_wiso (.cv h) R S D E))
      (syn_wbr (syn_cnc D) (syn_clec) (syn_cnc E))
      (syn_wrex x E (syn_wex h (syn_wiso (.cv h) R (syn_cin S (syn_cxp
                (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv x))))
                (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv x)))))) D
            (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv x)))))))
      p0008 p0030
  exact p0031

@[expose]
noncomputable def g_wecomparisonreversecutrepfdv (x : Var) (D : Class) (R : Class)
    (S : Class) (h : Var) (E : Class) (dv_D_h : h ∉ D.fv) (_dv_D_x : x ∉ D.fv)
    (dv_E_h : h ∉ E.fv) (_dv_E_x : x ∉ E.fv) (dv_R_h : h ∉ R.fv) (_dv_R_x : x ∉ R.fv)
    (dv_h_x : h ≠ x) :
    Nominal.NPrf
      (.imp (syn_wrex x D (syn_wex h (syn_wiso (.cv h) S (syn_cin R (syn_cxp (syn_cin D
                    (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) (syn_cin D
                    (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) E
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))))
        (syn_wrex x D (.classEq (syn_cnc E) (syn_cnc (syn_cin D
                (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))))) :=
  by
  have dv_cache_0001 : h ∉ (E).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : h ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_E_h, not_false_eq_true])
  have dv_cache_0002 :
    h ∉ ((syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))).fv :=
    by
    clear dv_cache_0001
    exact
      (by
        have compact_fv_not_mem_empty : h ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cima,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdif,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cid,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, dv_D_h, dv_R_h, dv_h_x, compact_fv_not_mem_empty,
          or_false, not_false_eq_true])
  have p0000 :=
    @g_weisoexnceqclfdv E
      (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) S
      (syn_cin R (syn_cxp
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))
      h dv_cache_0001 dv_cache_0002
  have p0001 :=
    @g_reximi
      (syn_wex h (syn_wiso (.cv h) S (syn_cin R (syn_cxp
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))
          E (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))
      (.classEq (syn_cnc E) (syn_cnc
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))
      x D p0000
  exact p0001

@[expose]
noncomputable def g_wecomparisoncutrepltfdv (x : Var) (D : Class) (R : Class) (S : Class)
    (E : Class) (dv_D_x : x ∉ D.fv) (dv_E_x : x ∉ E.fv) (dv_R_x : x ∉ R.fv)
    (dv_S_x : x ∉ S.fv)
    (hyp_wecomparisoncutrepltfdv_1 : Nominal.NPrf (syn_wbr R (syn_cwe) D))
    (hyp_wecomparisoncutrepltfdv_2 : Nominal.NPrf (syn_wbr S (syn_cwe) E))
    (hyp_wecomparisoncutrepltfdv_3 :
      Nominal.NPrf (syn_wbr (syn_cnc E) (syn_cltc) (syn_cnc D))) :
    Nominal.NPrf
      (syn_wrex x D (.classEq (syn_cnc E) (syn_cnc (syn_cin D
              (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))) :=
  by
  let proofSupport : Finset Var := ({ x } : Finset Var) ∪ D.fv ∪ R.fv ∪ S.fv ∪ E.fv
  let h : Var := freshVar proofSupport 0
  have fresh_h : h ∉ proofSupport :=
    by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_h_ne_x : h ≠ x := by
    intro h
    exact
      fresh_h
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _
              (Finset.mem_union_left _ (Finset.mem_singleton.mpr h)))))
  have fresh_h_not_D : h ∉ D.fv := by
    intro h
    exact
      fresh_h
        (Finset.mem_union_left _ (Finset.mem_union_left _
            (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))))
  have fresh_h_not_R : h ∉ R.fv := by
    intro h
    exact
      fresh_h
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))
  have fresh_h_not_S : h ∉ S.fv := by
    intro h
    exact fresh_h (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_h_not_E : h ∉ E.fv := by
    intro h
    exact fresh_h (Finset.mem_union_right _ (h))
  have dv_cache_0001 : h ∉ (D).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : h ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_h_not_D, not_false_eq_true])
  have dv_cache_0002 : x ∉ (D).fv :=
    by
    clear dv_cache_0001
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_D_x, not_false_eq_true])
  have dv_cache_0003 : h ∉ (E).fv :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact
      (by
        have compact_fv_not_mem_empty : h ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_h_not_E, not_false_eq_true])
  have dv_cache_0004 : x ∉ (E).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_E_x, not_false_eq_true])
  have dv_cache_0005 : h ∉ (R).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact
      (by
        have compact_fv_not_mem_empty : h ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_h_not_R, not_false_eq_true])
  have dv_cache_0006 : x ∉ (R).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_R_x, not_false_eq_true])
  have dv_cache_0007 : h ∉ (S).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006
    exact
      (by
        have compact_fv_not_mem_empty : h ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_h_not_S, not_false_eq_true])
  have dv_cache_0008 : x ∉ (S).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_S_x, not_false_eq_true])
  have dv_cache_0009 : h ≠ x :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008
    exact (show h ≠ x from (by exact fresh_h_ne_x))
  have p0000 :=
    @g_wecomparisonterminalfdv x D R S h E dv_cache_0001 dv_cache_0002 dv_cache_0003
      dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009
      hyp_wecomparisoncutrepltfdv_1 hyp_wecomparisoncutrepltfdv_2
  have p0001 :=
    @g_orc (syn_wex h (syn_wiso (.cv h) R S D E))
      (syn_wrex x E (syn_wex h (syn_wiso (.cv h) R (syn_cin S (syn_cxp
                (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv x))))
                (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv x)))))) D
            (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv x)))))))
  have p0002 :=
    @g_wecomparisonforwardnclecclfdv x D R S h E dv_cache_0001 dv_cache_0002 dv_cache_0003
      dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009
      hyp_wecomparisoncutrepltfdv_2
  have p0003 := @g_brex S E (syn_cwe)
  have p0004 := Nominal.mp hyp_wecomparisoncutrepltfdv_2 p0003
  have p0005 := @g_simpri (.classMem S (syn_cvv)) (.classMem E (syn_cvv)) p0004
  have p0006 := @g_ncelncsi E p0005
  have p0007 := @g_brex R D (syn_cwe)
  have p0008 := Nominal.mp hyp_wecomparisoncutrepltfdv_1 p0007
  have p0009 := @g_simpri (.classMem R (syn_cvv)) (.classMem D (syn_cvv)) p0008
  have p0010 := @g_ncelncsi D p0009
  have p0011 :=
    @g_pm3_2i (.classMem (syn_cnc E) (syn_cncs)) (.classMem (syn_cnc D) (syn_cncs)) p0006
      p0010
  have p0012 := @g_ltlenlec (syn_cnc E) (syn_cnc D)
  have p0013 := Nominal.mp p0011 p0012
  have p0014 :=
    @g_biimpi (syn_wbr (syn_cnc E) (syn_cltc) (syn_cnc D))
      (syn_wa (syn_wbr (syn_cnc E) (syn_clec) (syn_cnc D))
        (.neg (syn_wbr (syn_cnc D) (syn_clec) (syn_cnc E))))
      p0013
  have p0015 := Nominal.mp hyp_wecomparisoncutrepltfdv_3 p0014
  have p0016 :=
    @g_simpri (syn_wbr (syn_cnc E) (syn_clec) (syn_cnc D))
      (.neg (syn_wbr (syn_cnc D) (syn_clec) (syn_cnc E))) p0015
  have p0017 :=
    @g_pm2_21 (syn_wbr (syn_cnc D) (syn_clec) (syn_cnc E))
      (syn_wrex x D (.classEq (syn_cnc E) (syn_cnc
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))))
  have p0018 := Nominal.mp p0016 p0017
  have p0019 :=
    @g_syl
      (syn_wo (syn_wex h (syn_wiso (.cv h) R S D E)) (syn_wrex x E (syn_wex h
            (syn_wiso (.cv h) R (syn_cin S (syn_cxp (syn_cin E
                    (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv x)))) (syn_cin E
                    (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv x)))))) D
              (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv x))))))))
      (syn_wbr (syn_cnc D) (syn_clec) (syn_cnc E))
      (syn_wrex x D (.classEq (syn_cnc E) (syn_cnc
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))))
      p0002 p0018
  have p0020 :=
    @g_syl (syn_wex h (syn_wiso (.cv h) R S D E))
      (syn_wo (syn_wex h (syn_wiso (.cv h) R S D E)) (syn_wrex x E (syn_wex h
            (syn_wiso (.cv h) R (syn_cin S (syn_cxp (syn_cin E
                    (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv x)))) (syn_cin E
                    (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv x)))))) D
              (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv x))))))))
      (syn_wrex x D (.classEq (syn_cnc E) (syn_cnc
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))))
      p0001 p0019
  have p0021 :=
    @g_olc
      (syn_wrex x E (syn_wex h (syn_wiso (.cv h) R (syn_cin S (syn_cxp
                (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv x))))
                (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv x)))))) D
            (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv x)))))))
      (syn_wex h (syn_wiso (.cv h) R S D E))
  have p0040 :=
    @g_syl
      (syn_wrex x E (syn_wex h (syn_wiso (.cv h) R (syn_cin S (syn_cxp
                (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv x))))
                (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv x)))))) D
            (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv x)))))))
      (syn_wo (syn_wex h (syn_wiso (.cv h) R S D E)) (syn_wrex x E (syn_wex h
            (syn_wiso (.cv h) R (syn_cin S (syn_cxp (syn_cin E
                    (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv x)))) (syn_cin E
                    (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv x)))))) D
              (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv x))))))))
      (syn_wrex x D (.classEq (syn_cnc E) (syn_cnc
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))))
      p0021 p0019
  have p0041 :=
    @g_wecomparisonreversecutrepfdv x D R S h E dv_cache_0001 dv_cache_0002 dv_cache_0003
      dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0009
  have p0042 :=
    @g_n_3jaoi (syn_wex h (syn_wiso (.cv h) R S D E))
      (syn_wrex x D (.classEq (syn_cnc E) (syn_cnc
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))))
      (syn_wrex x E (syn_wex h (syn_wiso (.cv h) R (syn_cin S (syn_cxp
                (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv x))))
                (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv x)))))) D
            (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv x)))))))
      (syn_wrex x D (syn_wex h (syn_wiso (.cv h) S (syn_cin R (syn_cxp
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))) E
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))))
      p0020 p0040 p0041
  have p0043 := Nominal.mp p0000 p0042
  exact p0043


end NFChoice.DirectNominalPrf.WPPReplay

end
