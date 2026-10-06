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

/-- Checked nominal proof certificate identified upstream as `g_wecutisoextendedterminaldfdv`. -/
@[expose]
noncomputable def gWecutisoextendedterminaldfdv (x : Var) (y : Var) (u : Var) (D : Class)
    (R : Class) (S : Class) (h : Var) (E : Class) (dv_D_h : h ∉ D.fv) (dv_D_u : u ∉ D.fv)
    (dv_D_x : x ∉ D.fv) (dv_D_y : y ∉ D.fv) (dv_E_h : h ∉ E.fv) (dv_E_u : u ∉ E.fv)
    (dv_E_x : x ∉ E.fv) (dv_E_y : y ∉ E.fv) (dv_R_h : h ∉ R.fv) (dv_R_u : u ∉ R.fv)
    (dv_R_x : x ∉ R.fv) (dv_R_y : y ∉ R.fv) (dv_S_h : h ∉ S.fv) (dv_S_u : u ∉ S.fv)
    (dv_S_x : x ∉ S.fv) (dv_S_y : y ∉ S.fv) (dv_h_u : h ≠ u) (dv_h_x : h ≠ x)
    (dv_h_y : h ≠ y) (dv_u_x : u ≠ x) (dv_u_y : u ≠ y) (dv_x_y : x ≠ y)
    (hyp_wecutisoextendedterminaldfdv_1 : Nominal.NPrf (synWbr R (synCwe) D))
    (hyp_wecutisoextendedterminaldfdv_2 : Nominal.NPrf (synWbr S (synCwe) E))
    (hyp_wecutisoextendedterminaldfdv_3 :
      Nominal.NPrf (.classMem (synCuni (synCwecutiso R D S E)) (synCvv))) :
    Nominal.NPrf
      (.imp (synWa (synWa (.classMem (.cv y) D) (.classMem (.cv u) E))
          (synWa (.neg (.classMem (.cv y) (synCdm (synCuni (synCwecutiso R D S E)))))
            (synWiso (synCun (synCuni (synCwecutiso R D S E))
                (synCsn (synCop (.cv y) (.cv u)))) R S (synCun
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
                (synCsn (.cv y))) (synCun
                (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
                (synCsn (.cv u)))))) (synW3o (synWex h (synWiso (.cv h) R S D E))
          (synWrex x E (synWex h (synWiso (.cv h) R (synCin S (synCxp (synCin E
                      (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv x)))) (synCin E
                      (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv x)))))) D
                (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv x)))))))
          (synWrex x D (synWex h (synWiso (.cv h) S (synCin R (synCxp (synCin D
                      (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))) (synCin D
                      (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))))) E
                (synCin D
                  (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))))) :=
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
      ((synW3o (synWex h (synWiso (.cv h) R S D E)) (synWrex x E (synWex h
              (synWiso (.cv h) R (synCin S (synCxp (synCin E
                      (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv x)))) (synCin E
                      (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv x)))))) D
                (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv x)))))))
          (synWrex x D (synWex h (synWiso (.cv h) S (synCin R (synCxp (synCin D
                      (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))) (synCin D
                      (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))))) E
                (synCin D (synCima (synCcnv (synCdif R (synCid)))
                    (synCsn (.cv x))))))))).fv :=
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
      ((synWa (synWa (synWa (.classMem (.cv y) D) (.classMem (.cv u) E)) (synWa
              (.neg (.classMem (.cv y) (synCdm (synCuni (synCwecutiso R D S E))))) (synWiso
                (synCun (synCuni (synCwecutiso R D S E)) (synCsn (synCop (.cv y) (.cv u))))
                R S (synCun (synCin D
                    (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
                  (synCsn (.cv y))) (synCun (synCin E
                    (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
                  (synCsn (.cv u)))))) (.classEq (synCun
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
              (synCsn (.cv y))) D))).fv :=
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
      ((synWa (synWa (synWa (.classMem (.cv y) D) (.classMem (.cv u) E)) (synWa
              (.neg (.classMem (.cv y) (synCdm (synCuni (synCwecutiso R D S E))))) (synWiso
                (synCun (synCuni (synCwecutiso R D S E)) (synCsn (synCop (.cv y) (.cv u))))
                R S (synCun (synCin D
                    (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
                  (synCsn (.cv y))) (synCun (synCin E
                    (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
                  (synCsn (.cv u)))))) (synWa (.classMem (.cv z) D) (.classEq (synCun
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
                (synCsn (.cv y))) (synCin D
                (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z)))))))).fv :=
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
      ((synW3o (synWex h (synWiso (.cv h) R S D E)) (synWrex x E (synWex h
              (synWiso (.cv h) R (synCin S (synCxp (synCin E
                      (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv x)))) (synCin E
                      (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv x)))))) D
                (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv x)))))))
          (synWrex x D (synWex h (synWiso (.cv h) S (synCin R (synCxp (synCin D
                      (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))) (synCin D
                      (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))))) E
                (synCin D (synCima (synCcnv (synCdif R (synCid)))
                    (synCsn (.cv x))))))))).fv :=
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
      ((synWa (synWa (.classMem (.cv y) D) (.classMem (.cv u) E))
          (synWa (.neg (.classMem (.cv y) (synCdm (synCuni (synCwecutiso R D S E)))))
            (synWiso (synCun (synCuni (synCwecutiso R D S E))
                (synCsn (synCop (.cv y) (.cv u)))) R S (synCun
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
                (synCsn (.cv y))) (synCun
                (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
                (synCsn (.cv u))))))).fv :=
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
    @gSimpll (.classMem (.cv y) D) (.classMem (.cv u) E)
      (synWa (.neg (.classMem (.cv y) (synCdm (synCuni (synCwecutiso R D S E))))) (synWiso
          (synCun (synCuni (synCwecutiso R D S E)) (synCsn (synCop (.cv y) (.cv u)))) R S
          (synCun (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
            (synCsn (.cv y))) (synCun
            (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
            (synCsn (.cv u)))))
  have p0001 :=
    @gWeincsegcutorwholendv y z D R dv_cache_0001 dv_cache_0002 dv_cache_0003
      hyp_wecutisoextendedterminaldfdv_1
  have p0002 :=
    @gSyl
      (synWa (synWa (.classMem (.cv y) D) (.classMem (.cv u) E))
        (synWa (.neg (.classMem (.cv y) (synCdm (synCuni (synCwecutiso R D S E)))))
          (synWiso (synCun (synCuni (synCwecutiso R D S E))
              (synCsn (synCop (.cv y) (.cv u)))) R S (synCun
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
              (synCsn (.cv y))) (synCun
              (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
              (synCsn (.cv u))))))
      (.classMem (.cv y) D)
      (synWo (.classEq (synCun
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
            (synCsn (.cv y))) D) (synWrex z D (.classEq (synCun
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
              (synCsn (.cv y)))
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z)))))))
      p0000 p0001
  have p0003 :=
    @gSimplr (.classMem (.cv y) D) (.classMem (.cv u) E)
      (synWa (.neg (.classMem (.cv y) (synCdm (synCuni (synCwecutiso R D S E))))) (synWiso
          (synCun (synCuni (synCwecutiso R D S E)) (synCsn (synCop (.cv y) (.cv u)))) R S
          (synCun (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
            (synCsn (.cv y))) (synCun
            (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
            (synCsn (.cv u)))))
  have p0004 :=
    @gWeincsegcutorwholendv u v E S dv_cache_0004 dv_cache_0005 dv_cache_0006
      hyp_wecutisoextendedterminaldfdv_2
  have p0005 :=
    @gSyl
      (synWa (synWa (.classMem (.cv y) D) (.classMem (.cv u) E))
        (synWa (.neg (.classMem (.cv y) (synCdm (synCuni (synCwecutiso R D S E)))))
          (synWiso (synCun (synCuni (synCwecutiso R D S E))
              (synCsn (synCop (.cv y) (.cv u)))) R S (synCun
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
              (synCsn (.cv y))) (synCun
              (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
              (synCsn (.cv u))))))
      (.classMem (.cv u) E)
      (synWo (.classEq (synCun
            (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
            (synCsn (.cv u))) E) (synWrex v E (.classEq (synCun
              (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
              (synCsn (.cv u)))
            (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v)))))))
      p0003 p0004
  have p0006 :=
    @gA1d
      (synWa (synWa (.classMem (.cv y) D) (.classMem (.cv u) E))
        (synWa (.neg (.classMem (.cv y) (synCdm (synCuni (synCwecutiso R D S E)))))
          (synWiso (synCun (synCuni (synCwecutiso R D S E))
              (synCsn (synCop (.cv y) (.cv u)))) R S (synCun
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
              (synCsn (.cv y))) (synCun
              (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
              (synCsn (.cv u))))))
      (synWo (.classEq (synCun
            (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
            (synCsn (.cv u))) E) (synWrex v E (.classEq (synCun
              (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
              (synCsn (.cv u)))
            (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v)))))))
      (.classEq (synCun
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
          (synCsn (.cv y))) D)
      p0005
  have p0007 :=
    @gSimprr (synWa (.classMem (.cv y) D) (.classMem (.cv u) E))
      (.neg (.classMem (.cv y) (synCdm (synCuni (synCwecutiso R D S E)))))
      (synWiso
        (synCun (synCuni (synCwecutiso R D S E)) (synCsn (synCop (.cv y) (.cv u)))) R S
        (synCun (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
          (synCsn (.cv y))) (synCun
          (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
          (synCsn (.cv u))))
  have p0008 :=
    @gSimprl (synWa (.classMem (.cv y) D) (.classMem (.cv u) E))
      (.neg (.classMem (.cv y) (synCdm (synCuni (synCwecutiso R D S E)))))
      (synWiso
        (synCun (synCuni (synCwecutiso R D S E)) (synCsn (synCop (.cv y) (.cv u)))) R S
        (synCun (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
          (synCsn (.cv y))) (synCun
          (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
          (synCsn (.cv u))))
  have p0009 :=
    @gWecutisobranchwwknfdv x y u D R S h E dv_cache_0007 dv_cache_0008 dv_cache_0009
      dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015
      dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021
      dv_cache_0022 dv_cache_0023 dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027
      dv_cache_0028 hyp_wecutisoextendedterminaldfdv_1 hyp_wecutisoextendedterminaldfdv_2
      hyp_wecutisoextendedterminaldfdv_3
  have p0010 :=
    @gSyl
      (synWa (synWa (.classMem (.cv y) D) (.classMem (.cv u) E))
        (synWa (.neg (.classMem (.cv y) (synCdm (synCuni (synCwecutiso R D S E)))))
          (synWiso (synCun (synCuni (synCwecutiso R D S E))
              (synCsn (synCop (.cv y) (.cv u)))) R S (synCun
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
              (synCsn (.cv y))) (synCun
              (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
              (synCsn (.cv u))))))
      (.neg (.classMem (.cv y) (synCdm (synCuni (synCwecutiso R D S E)))))
      (.imp (synWiso
          (synCun (synCuni (synCwecutiso R D S E)) (synCsn (synCop (.cv y) (.cv u)))) R S
          (synCun (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
            (synCsn (.cv y))) (synCun
            (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
            (synCsn (.cv u)))) (.imp (synWa (.classEq (synCun
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
                (synCsn (.cv y))) D) (.classEq (synCun
                (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
                (synCsn (.cv u))) E)) (synW3o (synWex h (synWiso (.cv h) R S D E))
            (synWrex x E (synWex h (synWiso (.cv h) R (synCin S (synCxp (synCin E
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
      p0008 p0009
  have p0011 :=
    @gMpd
      (synWa (synWa (.classMem (.cv y) D) (.classMem (.cv u) E))
        (synWa (.neg (.classMem (.cv y) (synCdm (synCuni (synCwecutiso R D S E)))))
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
      (.imp (synWa (.classEq (synCun
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
              (synCsn (.cv y))) D) (.classEq (synCun
              (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
              (synCsn (.cv u))) E)) (synW3o (synWex h (synWiso (.cv h) R S D E))
          (synWrex x E (synWex h (synWiso (.cv h) R (synCin S (synCxp (synCin E
                      (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv x)))) (synCin E
                      (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv x)))))) D
                (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv x)))))))
          (synWrex x D (synWex h (synWiso (.cv h) S (synCin R (synCxp (synCin D
                      (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))) (synCin D
                      (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))))) E
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))))))))
      p0007 p0010
  have p0012 :=
    @gExp3a
      (synWa (synWa (.classMem (.cv y) D) (.classMem (.cv u) E))
        (synWa (.neg (.classMem (.cv y) (synCdm (synCuni (synCwecutiso R D S E)))))
          (synWiso (synCun (synCuni (synCwecutiso R D S E))
              (synCsn (synCop (.cv y) (.cv u)))) R S (synCun
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
              (synCsn (.cv y))) (synCun
              (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
              (synCsn (.cv u))))))
      (.classEq (synCun
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
          (synCsn (.cv y))) D)
      (.classEq (synCun
          (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
          (synCsn (.cv u))) E)
      (synW3o (synWex h (synWiso (.cv h) R S D E)) (synWrex x E (synWex h
            (synWiso (.cv h) R (synCin S (synCxp (synCin E
                    (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv x)))) (synCin E
                    (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv x)))))) D
              (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv x)))))))
        (synWrex x D (synWex h (synWiso (.cv h) S (synCin R (synCxp (synCin D
                    (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))) (synCin D
                    (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))))) E
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))))
      p0011
  have p0013 :=
    @gImp
      (synWa (synWa (.classMem (.cv y) D) (.classMem (.cv u) E))
        (synWa (.neg (.classMem (.cv y) (synCdm (synCuni (synCwecutiso R D S E)))))
          (synWiso (synCun (synCuni (synCwecutiso R D S E))
              (synCsn (synCop (.cv y) (.cv u)))) R S (synCun
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
              (synCsn (.cv y))) (synCun
              (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
              (synCsn (.cv u))))))
      (.classEq (synCun
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
          (synCsn (.cv y))) D)
      (.imp (.classEq (synCun
            (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
            (synCsn (.cv u))) E) (synW3o (synWex h (synWiso (.cv h) R S D E)) (synWrex x E
            (synWex h (synWiso (.cv h) R (synCin S (synCxp (synCin E
                      (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv x)))) (synCin E
                      (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv x)))))) D
                (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv x)))))))
          (synWrex x D (synWex h (synWiso (.cv h) S (synCin R (synCxp (synCin D
                      (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))) (synCin D
                      (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))))) E
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))))))))
      p0012
  have p0016 :=
    @gWecutisobranchwcknfdv x y v u D R S h E dv_cache_0007 dv_cache_0008 dv_cache_0029
      dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0004 dv_cache_0013
      dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0030 dv_cache_0017 dv_cache_0018
      dv_cache_0019 dv_cache_0020 dv_cache_0005 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0031 dv_cache_0024 dv_cache_0025 dv_cache_0006 dv_cache_0026 dv_cache_0027
      dv_cache_0032 dv_cache_0033 dv_cache_0028 hyp_wecutisoextendedterminaldfdv_1
      hyp_wecutisoextendedterminaldfdv_2 hyp_wecutisoextendedterminaldfdv_3
  have p0017 :=
    @gSyl
      (synWa (synWa (.classMem (.cv y) D) (.classMem (.cv u) E))
        (synWa (.neg (.classMem (.cv y) (synCdm (synCuni (synCwecutiso R D S E)))))
          (synWiso (synCun (synCuni (synCwecutiso R D S E))
              (synCsn (synCop (.cv y) (.cv u)))) R S (synCun
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
              (synCsn (.cv y))) (synCun
              (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
              (synCsn (.cv u))))))
      (.neg (.classMem (.cv y) (synCdm (synCuni (synCwecutiso R D S E)))))
      (.imp (synWiso
          (synCun (synCuni (synCwecutiso R D S E)) (synCsn (synCop (.cv y) (.cv u)))) R S
          (synCun (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
            (synCsn (.cv y))) (synCun
            (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
            (synCsn (.cv u)))) (.imp (synWa (synWa (.classEq (synCun (synCin D
                    (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
                  (synCsn (.cv y))) D) (.classMem (.cv v) E)) (.classEq (synCun
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
      p0008 p0016
  have p0018 :=
    @gMpd
      (synWa (synWa (.classMem (.cv y) D) (.classMem (.cv u) E))
        (synWa (.neg (.classMem (.cv y) (synCdm (synCuni (synCwecutiso R D S E)))))
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
      (.imp (synWa (synWa (.classEq (synCun
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
                (synCsn (.cv y))) D) (.classMem (.cv v) E)) (.classEq (synCun
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
      p0007 p0017
  have p0019 :=
    @gExp3a
      (synWa (synWa (.classMem (.cv y) D) (.classMem (.cv u) E))
        (synWa (.neg (.classMem (.cv y) (synCdm (synCuni (synCwecutiso R D S E)))))
          (synWiso (synCun (synCuni (synCwecutiso R D S E))
              (synCsn (synCop (.cv y) (.cv u)))) R S (synCun
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
              (synCsn (.cv y))) (synCun
              (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
              (synCsn (.cv u))))))
      (synWa (.classEq (synCun
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
            (synCsn (.cv y))) D) (.classMem (.cv v) E))
      (.classEq (synCun
          (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
          (synCsn (.cv u)))
        (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v)))))
      (synW3o (synWex h (synWiso (.cv h) R S D E)) (synWrex x E (synWex h
            (synWiso (.cv h) R (synCin S (synCxp (synCin E
                    (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv x)))) (synCin E
                    (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv x)))))) D
              (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv x)))))))
        (synWrex x D (synWex h (synWiso (.cv h) S (synCin R (synCxp (synCin D
                    (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))) (synCin D
                    (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))))) E
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))))
      p0018
  have p0020 :=
    @gExp3a
      (synWa (synWa (.classMem (.cv y) D) (.classMem (.cv u) E))
        (synWa (.neg (.classMem (.cv y) (synCdm (synCuni (synCwecutiso R D S E)))))
          (synWiso (synCun (synCuni (synCwecutiso R D S E))
              (synCsn (synCop (.cv y) (.cv u)))) R S (synCun
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
              (synCsn (.cv y))) (synCun
              (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
              (synCsn (.cv u))))))
      (.classEq (synCun
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
          (synCsn (.cv y))) D)
      (.classMem (.cv v) E)
      (.imp (.classEq (synCun
            (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
            (synCsn (.cv u)))
          (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v)))))
        (synW3o (synWex h (synWiso (.cv h) R S D E)) (synWrex x E (synWex h
              (synWiso (.cv h) R (synCin S (synCxp (synCin E
                      (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv x)))) (synCin E
                      (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv x)))))) D
                (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv x)))))))
          (synWrex x D (synWex h (synWiso (.cv h) S (synCin R (synCxp (synCin D
                      (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))) (synCin D
                      (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))))) E
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))))))))
      p0019
  have p0021 :=
    @gImp
      (synWa (synWa (.classMem (.cv y) D) (.classMem (.cv u) E))
        (synWa (.neg (.classMem (.cv y) (synCdm (synCuni (synCwecutiso R D S E)))))
          (synWiso (synCun (synCuni (synCwecutiso R D S E))
              (synCsn (synCop (.cv y) (.cv u)))) R S (synCun
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
              (synCsn (.cv y))) (synCun
              (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
              (synCsn (.cv u))))))
      (.classEq (synCun
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
          (synCsn (.cv y))) D)
      (.imp (.classMem (.cv v) E) (.imp (.classEq (synCun
              (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
              (synCsn (.cv u)))
            (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v)))))
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
      p0020
  have p0022 :=
    @gImp
      (synWa (synWa (synWa (.classMem (.cv y) D) (.classMem (.cv u) E))
          (synWa (.neg (.classMem (.cv y) (synCdm (synCuni (synCwecutiso R D S E)))))
            (synWiso (synCun (synCuni (synCwecutiso R D S E))
                (synCsn (synCop (.cv y) (.cv u)))) R S (synCun
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
                (synCsn (.cv y))) (synCun
                (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
                (synCsn (.cv u)))))) (.classEq (synCun
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
            (synCsn (.cv y))) D))
      (.classMem (.cv v) E)
      (.imp (.classEq (synCun
            (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
            (synCsn (.cv u)))
          (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v)))))
        (synW3o (synWex h (synWiso (.cv h) R S D E)) (synWrex x E (synWex h
              (synWiso (.cv h) R (synCin S (synCxp (synCin E
                      (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv x)))) (synCin E
                      (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv x)))))) D
                (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv x)))))))
          (synWrex x D (synWex h (synWiso (.cv h) S (synCin R (synCxp (synCin D
                      (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))) (synCin D
                      (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))))) E
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))))))))
      p0021
  have p0023 :=
    @gRexlimdva
      (synWa (synWa (synWa (.classMem (.cv y) D) (.classMem (.cv u) E))
          (synWa (.neg (.classMem (.cv y) (synCdm (synCuni (synCwecutiso R D S E)))))
            (synWiso (synCun (synCuni (synCwecutiso R D S E))
                (synCsn (synCop (.cv y) (.cv u)))) R S (synCun
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
                (synCsn (.cv y))) (synCun
                (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
                (synCsn (.cv u)))))) (.classEq (synCun
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
            (synCsn (.cv y))) D))
      (.classEq (synCun
          (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
          (synCsn (.cv u)))
        (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v)))))
      (synW3o (synWex h (synWiso (.cv h) R S D E)) (synWrex x E (synWex h
            (synWiso (.cv h) R (synCin S (synCxp (synCin E
                    (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv x)))) (synCin E
                    (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv x)))))) D
              (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv x)))))))
        (synWrex x D (synWex h (synWiso (.cv h) S (synCin R (synCxp (synCin D
                    (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))) (synCin D
                    (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))))) E
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))))
      v E dv_cache_0034 dv_cache_0035 p0022
  have p0024 :=
    @gJaod
      (synWa (synWa (synWa (.classMem (.cv y) D) (.classMem (.cv u) E))
          (synWa (.neg (.classMem (.cv y) (synCdm (synCuni (synCwecutiso R D S E)))))
            (synWiso (synCun (synCuni (synCwecutiso R D S E))
                (synCsn (synCop (.cv y) (.cv u)))) R S (synCun
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
                (synCsn (.cv y))) (synCun
                (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
                (synCsn (.cv u)))))) (.classEq (synCun
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
            (synCsn (.cv y))) D))
      (.classEq (synCun
          (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
          (synCsn (.cv u))) E)
      (synW3o (synWex h (synWiso (.cv h) R S D E)) (synWrex x E (synWex h
            (synWiso (.cv h) R (synCin S (synCxp (synCin E
                    (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv x)))) (synCin E
                    (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv x)))))) D
              (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv x)))))))
        (synWrex x D (synWex h (synWiso (.cv h) S (synCin R (synCxp (synCin D
                    (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))) (synCin D
                    (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))))) E
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))))
      (synWrex v E (.classEq (synCun
            (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
            (synCsn (.cv u)))
          (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))))
      p0013 p0023
  have p0025 :=
    @gEx
      (synWa (synWa (.classMem (.cv y) D) (.classMem (.cv u) E))
        (synWa (.neg (.classMem (.cv y) (synCdm (synCuni (synCwecutiso R D S E)))))
          (synWiso (synCun (synCuni (synCwecutiso R D S E))
              (synCsn (synCop (.cv y) (.cv u)))) R S (synCun
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
              (synCsn (.cv y))) (synCun
              (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
              (synCsn (.cv u))))))
      (.classEq (synCun
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
          (synCsn (.cv y))) D)
      (.imp (synWo (.classEq (synCun
              (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
              (synCsn (.cv u))) E) (synWrex v E (.classEq (synCun
                (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
                (synCsn (.cv u))) (synCin E
                (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v)))))))
        (synW3o (synWex h (synWiso (.cv h) R S D E)) (synWrex x E (synWex h
              (synWiso (.cv h) R (synCin S (synCxp (synCin E
                      (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv x)))) (synCin E
                      (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv x)))))) D
                (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv x)))))))
          (synWrex x D (synWex h (synWiso (.cv h) S (synCin R (synCxp (synCin D
                      (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))) (synCin D
                      (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))))) E
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))))))))
      p0024
  have p0026 :=
    @gMpdd
      (synWa (synWa (.classMem (.cv y) D) (.classMem (.cv u) E))
        (synWa (.neg (.classMem (.cv y) (synCdm (synCuni (synCwecutiso R D S E)))))
          (synWiso (synCun (synCuni (synCwecutiso R D S E))
              (synCsn (synCop (.cv y) (.cv u)))) R S (synCun
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
              (synCsn (.cv y))) (synCun
              (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
              (synCsn (.cv u))))))
      (.classEq (synCun
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
          (synCsn (.cv y))) D)
      (synWo (.classEq (synCun
            (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
            (synCsn (.cv u))) E) (synWrex v E (.classEq (synCun
              (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
              (synCsn (.cv u)))
            (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v)))))))
      (synW3o (synWex h (synWiso (.cv h) R S D E)) (synWrex x E (synWex h
            (synWiso (.cv h) R (synCin S (synCxp (synCin E
                    (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv x)))) (synCin E
                    (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv x)))))) D
              (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv x)))))))
        (synWrex x D (synWex h (synWiso (.cv h) S (synCin R (synCxp (synCin D
                    (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))) (synCin D
                    (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))))) E
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))))
      p0006 p0025
  have p0030 :=
    @gA1d
      (synWa (synWa (.classMem (.cv y) D) (.classMem (.cv u) E))
        (synWa (.neg (.classMem (.cv y) (synCdm (synCuni (synCwecutiso R D S E)))))
          (synWiso (synCun (synCuni (synCwecutiso R D S E))
              (synCsn (synCop (.cv y) (.cv u)))) R S (synCun
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
              (synCsn (.cv y))) (synCun
              (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
              (synCsn (.cv u))))))
      (synWo (.classEq (synCun
            (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
            (synCsn (.cv u))) E) (synWrex v E (.classEq (synCun
              (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
              (synCsn (.cv u)))
            (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v)))))))
      (synWa (.classMem (.cv z) D) (.classEq (synCun
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
            (synCsn (.cv y)))
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z))))))
      p0005
  have p0033 :=
    @gWecutisobranchcwknfdv x y z u D R S h E dv_cache_0007 dv_cache_0008 dv_cache_0009
      dv_cache_0010 dv_cache_0001 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014
      dv_cache_0036 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0002
      dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0037 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0038 dv_cache_0026 dv_cache_0027 dv_cache_0039
      dv_cache_0028 dv_cache_0040 dv_cache_0003 hyp_wecutisoextendedterminaldfdv_1
      hyp_wecutisoextendedterminaldfdv_2 hyp_wecutisoextendedterminaldfdv_3
  have p0034 :=
    @gSyl
      (synWa (synWa (.classMem (.cv y) D) (.classMem (.cv u) E))
        (synWa (.neg (.classMem (.cv y) (synCdm (synCuni (synCwecutiso R D S E)))))
          (synWiso (synCun (synCuni (synCwecutiso R D S E))
              (synCsn (synCop (.cv y) (.cv u)))) R S (synCun
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
              (synCsn (.cv y))) (synCun
              (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
              (synCsn (.cv u))))))
      (.neg (.classMem (.cv y) (synCdm (synCuni (synCwecutiso R D S E)))))
      (.imp (synWiso
          (synCun (synCuni (synCwecutiso R D S E)) (synCsn (synCop (.cv y) (.cv u)))) R S
          (synCun (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
            (synCsn (.cv y))) (synCun
            (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
            (synCsn (.cv u)))) (.imp (synWa (synWa (.classMem (.cv z) D) (.classEq (synCun
                  (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
                  (synCsn (.cv y))) (synCin D
                  (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z)))))) (.classEq
              (synCun
                (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
                (synCsn (.cv u))) E)) (synW3o (synWex h (synWiso (.cv h) R S D E))
            (synWrex x E (synWex h (synWiso (.cv h) R (synCin S (synCxp (synCin E
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
      p0008 p0033
  have p0035 :=
    @gMpd
      (synWa (synWa (.classMem (.cv y) D) (.classMem (.cv u) E))
        (synWa (.neg (.classMem (.cv y) (synCdm (synCuni (synCwecutiso R D S E)))))
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
      (.imp (synWa (synWa (.classMem (.cv z) D) (.classEq (synCun
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
                (synCsn (.cv y)))
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z))))))
          (.classEq (synCun
              (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
              (synCsn (.cv u))) E)) (synW3o (synWex h (synWiso (.cv h) R S D E))
          (synWrex x E (synWex h (synWiso (.cv h) R (synCin S (synCxp (synCin E
                      (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv x)))) (synCin E
                      (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv x)))))) D
                (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv x)))))))
          (synWrex x D (synWex h (synWiso (.cv h) S (synCin R (synCxp (synCin D
                      (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))) (synCin D
                      (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))))) E
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))))))))
      p0007 p0034
  have p0036 :=
    @gExp3a
      (synWa (synWa (.classMem (.cv y) D) (.classMem (.cv u) E))
        (synWa (.neg (.classMem (.cv y) (synCdm (synCuni (synCwecutiso R D S E)))))
          (synWiso (synCun (synCuni (synCwecutiso R D S E))
              (synCsn (synCop (.cv y) (.cv u)))) R S (synCun
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
              (synCsn (.cv y))) (synCun
              (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
              (synCsn (.cv u))))))
      (synWa (.classMem (.cv z) D) (.classEq (synCun
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
            (synCsn (.cv y)))
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z))))))
      (.classEq (synCun
          (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
          (synCsn (.cv u))) E)
      (synW3o (synWex h (synWiso (.cv h) R S D E)) (synWrex x E (synWex h
            (synWiso (.cv h) R (synCin S (synCxp (synCin E
                    (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv x)))) (synCin E
                    (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv x)))))) D
              (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv x)))))))
        (synWrex x D (synWex h (synWiso (.cv h) S (synCin R (synCxp (synCin D
                    (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))) (synCin D
                    (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))))) E
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))))
      p0035
  have p0037 :=
    @gImp
      (synWa (synWa (.classMem (.cv y) D) (.classMem (.cv u) E))
        (synWa (.neg (.classMem (.cv y) (synCdm (synCuni (synCwecutiso R D S E)))))
          (synWiso (synCun (synCuni (synCwecutiso R D S E))
              (synCsn (synCop (.cv y) (.cv u)))) R S (synCun
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
              (synCsn (.cv y))) (synCun
              (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
              (synCsn (.cv u))))))
      (synWa (.classMem (.cv z) D) (.classEq (synCun
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
            (synCsn (.cv y)))
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z))))))
      (.imp (.classEq (synCun
            (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
            (synCsn (.cv u))) E) (synW3o (synWex h (synWiso (.cv h) R S D E)) (synWrex x E
            (synWex h (synWiso (.cv h) R (synCin S (synCxp (synCin E
                      (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv x)))) (synCin E
                      (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv x)))))) D
                (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv x)))))))
          (synWrex x D (synWex h (synWiso (.cv h) S (synCin R (synCxp (synCin D
                      (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))) (synCin D
                      (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))))) E
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))))))))
      p0036
  have p0040 :=
    @gWecutisobranchccknfdv x y z v u D R S h E dv_cache_0007 dv_cache_0008 dv_cache_0029
      dv_cache_0009 dv_cache_0010 dv_cache_0001 dv_cache_0011 dv_cache_0012 dv_cache_0004
      dv_cache_0013 dv_cache_0014 dv_cache_0036 dv_cache_0015 dv_cache_0016 dv_cache_0030
      dv_cache_0017 dv_cache_0018 dv_cache_0002 dv_cache_0019 dv_cache_0020 dv_cache_0005
      dv_cache_0021 dv_cache_0022 dv_cache_0037 dv_cache_0023 dv_cache_0031 dv_cache_0024
      dv_cache_0025 dv_cache_0038 dv_cache_0006 dv_cache_0026 dv_cache_0027 dv_cache_0039
      dv_cache_0032 dv_cache_0033 dv_cache_0041 dv_cache_0028 dv_cache_0040 dv_cache_0003
      hyp_wecutisoextendedterminaldfdv_1 hyp_wecutisoextendedterminaldfdv_2
      hyp_wecutisoextendedterminaldfdv_3
  have p0041 :=
    @gSyl
      (synWa (synWa (.classMem (.cv y) D) (.classMem (.cv u) E))
        (synWa (.neg (.classMem (.cv y) (synCdm (synCuni (synCwecutiso R D S E)))))
          (synWiso (synCun (synCuni (synCwecutiso R D S E))
              (synCsn (synCop (.cv y) (.cv u)))) R S (synCun
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
              (synCsn (.cv y))) (synCun
              (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
              (synCsn (.cv u))))))
      (.neg (.classMem (.cv y) (synCdm (synCuni (synCwecutiso R D S E)))))
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
      p0008 p0040
  have p0042 :=
    @gMpd
      (synWa (synWa (.classMem (.cv y) D) (.classMem (.cv u) E))
        (synWa (.neg (.classMem (.cv y) (synCdm (synCuni (synCwecutiso R D S E)))))
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
      p0007 p0041
  have p0043 :=
    @gExp3a
      (synWa (synWa (.classMem (.cv y) D) (.classMem (.cv u) E))
        (synWa (.neg (.classMem (.cv y) (synCdm (synCuni (synCwecutiso R D S E)))))
          (synWiso (synCun (synCuni (synCwecutiso R D S E))
              (synCsn (synCop (.cv y) (.cv u)))) R S (synCun
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
              (synCsn (.cv y))) (synCun
              (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
              (synCsn (.cv u))))))
      (synWa (synWa (.classMem (.cv z) D) (.classEq (synCun
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
              (synCsn (.cv y)))
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z))))))
        (.classMem (.cv v) E))
      (.classEq (synCun
          (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
          (synCsn (.cv u)))
        (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v)))))
      (synW3o (synWex h (synWiso (.cv h) R S D E)) (synWrex x E (synWex h
            (synWiso (.cv h) R (synCin S (synCxp (synCin E
                    (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv x)))) (synCin E
                    (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv x)))))) D
              (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv x)))))))
        (synWrex x D (synWex h (synWiso (.cv h) S (synCin R (synCxp (synCin D
                    (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))) (synCin D
                    (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))))) E
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))))
      p0042
  have p0044 :=
    @gExp3a
      (synWa (synWa (.classMem (.cv y) D) (.classMem (.cv u) E))
        (synWa (.neg (.classMem (.cv y) (synCdm (synCuni (synCwecutiso R D S E)))))
          (synWiso (synCun (synCuni (synCwecutiso R D S E))
              (synCsn (synCop (.cv y) (.cv u)))) R S (synCun
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
              (synCsn (.cv y))) (synCun
              (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
              (synCsn (.cv u))))))
      (synWa (.classMem (.cv z) D) (.classEq (synCun
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
            (synCsn (.cv y)))
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z))))))
      (.classMem (.cv v) E)
      (.imp (.classEq (synCun
            (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
            (synCsn (.cv u)))
          (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v)))))
        (synW3o (synWex h (synWiso (.cv h) R S D E)) (synWrex x E (synWex h
              (synWiso (.cv h) R (synCin S (synCxp (synCin E
                      (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv x)))) (synCin E
                      (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv x)))))) D
                (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv x)))))))
          (synWrex x D (synWex h (synWiso (.cv h) S (synCin R (synCxp (synCin D
                      (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))) (synCin D
                      (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))))) E
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))))))))
      p0043
  have p0045 :=
    @gImp
      (synWa (synWa (.classMem (.cv y) D) (.classMem (.cv u) E))
        (synWa (.neg (.classMem (.cv y) (synCdm (synCuni (synCwecutiso R D S E)))))
          (synWiso (synCun (synCuni (synCwecutiso R D S E))
              (synCsn (synCop (.cv y) (.cv u)))) R S (synCun
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
              (synCsn (.cv y))) (synCun
              (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
              (synCsn (.cv u))))))
      (synWa (.classMem (.cv z) D) (.classEq (synCun
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
            (synCsn (.cv y)))
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z))))))
      (.imp (.classMem (.cv v) E) (.imp (.classEq (synCun
              (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
              (synCsn (.cv u)))
            (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v)))))
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
      p0044
  have p0046 :=
    @gImp
      (synWa (synWa (synWa (.classMem (.cv y) D) (.classMem (.cv u) E))
          (synWa (.neg (.classMem (.cv y) (synCdm (synCuni (synCwecutiso R D S E)))))
            (synWiso (synCun (synCuni (synCwecutiso R D S E))
                (synCsn (synCop (.cv y) (.cv u)))) R S (synCun
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
                (synCsn (.cv y))) (synCun
                (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
                (synCsn (.cv u)))))) (synWa (.classMem (.cv z) D) (.classEq (synCun
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
              (synCsn (.cv y)))
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z)))))))
      (.classMem (.cv v) E)
      (.imp (.classEq (synCun
            (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
            (synCsn (.cv u)))
          (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v)))))
        (synW3o (synWex h (synWiso (.cv h) R S D E)) (synWrex x E (synWex h
              (synWiso (.cv h) R (synCin S (synCxp (synCin E
                      (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv x)))) (synCin E
                      (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv x)))))) D
                (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv x)))))))
          (synWrex x D (synWex h (synWiso (.cv h) S (synCin R (synCxp (synCin D
                      (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))) (synCin D
                      (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))))) E
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))))))))
      p0045
  have p0047 :=
    @gRexlimdva
      (synWa (synWa (synWa (.classMem (.cv y) D) (.classMem (.cv u) E))
          (synWa (.neg (.classMem (.cv y) (synCdm (synCuni (synCwecutiso R D S E)))))
            (synWiso (synCun (synCuni (synCwecutiso R D S E))
                (synCsn (synCop (.cv y) (.cv u)))) R S (synCun
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
                (synCsn (.cv y))) (synCun
                (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
                (synCsn (.cv u)))))) (synWa (.classMem (.cv z) D) (.classEq (synCun
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
              (synCsn (.cv y)))
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z)))))))
      (.classEq (synCun
          (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
          (synCsn (.cv u)))
        (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v)))))
      (synW3o (synWex h (synWiso (.cv h) R S D E)) (synWrex x E (synWex h
            (synWiso (.cv h) R (synCin S (synCxp (synCin E
                    (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv x)))) (synCin E
                    (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv x)))))) D
              (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv x)))))))
        (synWrex x D (synWex h (synWiso (.cv h) S (synCin R (synCxp (synCin D
                    (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))) (synCin D
                    (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))))) E
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))))
      v E dv_cache_0034 dv_cache_0042 p0046
  have p0048 :=
    @gJaod
      (synWa (synWa (synWa (.classMem (.cv y) D) (.classMem (.cv u) E))
          (synWa (.neg (.classMem (.cv y) (synCdm (synCuni (synCwecutiso R D S E)))))
            (synWiso (synCun (synCuni (synCwecutiso R D S E))
                (synCsn (synCop (.cv y) (.cv u)))) R S (synCun
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
                (synCsn (.cv y))) (synCun
                (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
                (synCsn (.cv u)))))) (synWa (.classMem (.cv z) D) (.classEq (synCun
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
              (synCsn (.cv y)))
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z)))))))
      (.classEq (synCun
          (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
          (synCsn (.cv u))) E)
      (synW3o (synWex h (synWiso (.cv h) R S D E)) (synWrex x E (synWex h
            (synWiso (.cv h) R (synCin S (synCxp (synCin E
                    (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv x)))) (synCin E
                    (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv x)))))) D
              (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv x)))))))
        (synWrex x D (synWex h (synWiso (.cv h) S (synCin R (synCxp (synCin D
                    (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))) (synCin D
                    (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))))) E
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))))
      (synWrex v E (.classEq (synCun
            (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
            (synCsn (.cv u)))
          (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))))
      p0037 p0047
  have p0049 :=
    @gEx
      (synWa (synWa (.classMem (.cv y) D) (.classMem (.cv u) E))
        (synWa (.neg (.classMem (.cv y) (synCdm (synCuni (synCwecutiso R D S E)))))
          (synWiso (synCun (synCuni (synCwecutiso R D S E))
              (synCsn (synCop (.cv y) (.cv u)))) R S (synCun
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
              (synCsn (.cv y))) (synCun
              (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
              (synCsn (.cv u))))))
      (synWa (.classMem (.cv z) D) (.classEq (synCun
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
            (synCsn (.cv y)))
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z))))))
      (.imp (synWo (.classEq (synCun
              (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
              (synCsn (.cv u))) E) (synWrex v E (.classEq (synCun
                (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
                (synCsn (.cv u))) (synCin E
                (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v)))))))
        (synW3o (synWex h (synWiso (.cv h) R S D E)) (synWrex x E (synWex h
              (synWiso (.cv h) R (synCin S (synCxp (synCin E
                      (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv x)))) (synCin E
                      (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv x)))))) D
                (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv x)))))))
          (synWrex x D (synWex h (synWiso (.cv h) S (synCin R (synCxp (synCin D
                      (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))) (synCin D
                      (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))))) E
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))))))))
      p0048
  have p0050 :=
    @gMpdd
      (synWa (synWa (.classMem (.cv y) D) (.classMem (.cv u) E))
        (synWa (.neg (.classMem (.cv y) (synCdm (synCuni (synCwecutiso R D S E)))))
          (synWiso (synCun (synCuni (synCwecutiso R D S E))
              (synCsn (synCop (.cv y) (.cv u)))) R S (synCun
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
              (synCsn (.cv y))) (synCun
              (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
              (synCsn (.cv u))))))
      (synWa (.classMem (.cv z) D) (.classEq (synCun
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
            (synCsn (.cv y)))
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z))))))
      (synWo (.classEq (synCun
            (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
            (synCsn (.cv u))) E) (synWrex v E (.classEq (synCun
              (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
              (synCsn (.cv u)))
            (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v)))))))
      (synW3o (synWex h (synWiso (.cv h) R S D E)) (synWrex x E (synWex h
            (synWiso (.cv h) R (synCin S (synCxp (synCin E
                    (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv x)))) (synCin E
                    (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv x)))))) D
              (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv x)))))))
        (synWrex x D (synWex h (synWiso (.cv h) S (synCin R (synCxp (synCin D
                    (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))) (synCin D
                    (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))))) E
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))))
      p0030 p0049
  have p0051 :=
    @gExp3a
      (synWa (synWa (.classMem (.cv y) D) (.classMem (.cv u) E))
        (synWa (.neg (.classMem (.cv y) (synCdm (synCuni (synCwecutiso R D S E)))))
          (synWiso (synCun (synCuni (synCwecutiso R D S E))
              (synCsn (synCop (.cv y) (.cv u)))) R S (synCun
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
              (synCsn (.cv y))) (synCun
              (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
              (synCsn (.cv u))))))
      (.classMem (.cv z) D)
      (.classEq (synCun
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
          (synCsn (.cv y)))
        (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z)))))
      (synW3o (synWex h (synWiso (.cv h) R S D E)) (synWrex x E (synWex h
            (synWiso (.cv h) R (synCin S (synCxp (synCin E
                    (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv x)))) (synCin E
                    (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv x)))))) D
              (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv x)))))))
        (synWrex x D (synWex h (synWiso (.cv h) S (synCin R (synCxp (synCin D
                    (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))) (synCin D
                    (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))))) E
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))))
      p0050
  have p0052 :=
    @gImp
      (synWa (synWa (.classMem (.cv y) D) (.classMem (.cv u) E))
        (synWa (.neg (.classMem (.cv y) (synCdm (synCuni (synCwecutiso R D S E)))))
          (synWiso (synCun (synCuni (synCwecutiso R D S E))
              (synCsn (synCop (.cv y) (.cv u)))) R S (synCun
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
              (synCsn (.cv y))) (synCun
              (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
              (synCsn (.cv u))))))
      (.classMem (.cv z) D)
      (.imp (.classEq (synCun
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
            (synCsn (.cv y)))
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z)))))
        (synW3o (synWex h (synWiso (.cv h) R S D E)) (synWrex x E (synWex h
              (synWiso (.cv h) R (synCin S (synCxp (synCin E
                      (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv x)))) (synCin E
                      (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv x)))))) D
                (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv x)))))))
          (synWrex x D (synWex h (synWiso (.cv h) S (synCin R (synCxp (synCin D
                      (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))) (synCin D
                      (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))))) E
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))))))))
      p0051
  have p0053 :=
    @gRexlimdva
      (synWa (synWa (.classMem (.cv y) D) (.classMem (.cv u) E))
        (synWa (.neg (.classMem (.cv y) (synCdm (synCuni (synCwecutiso R D S E)))))
          (synWiso (synCun (synCuni (synCwecutiso R D S E))
              (synCsn (synCop (.cv y) (.cv u)))) R S (synCun
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
              (synCsn (.cv y))) (synCun
              (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
              (synCsn (.cv u))))))
      (.classEq (synCun
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
          (synCsn (.cv y)))
        (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z)))))
      (synW3o (synWex h (synWiso (.cv h) R S D E)) (synWrex x E (synWex h
            (synWiso (.cv h) R (synCin S (synCxp (synCin E
                    (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv x)))) (synCin E
                    (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv x)))))) D
              (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv x)))))))
        (synWrex x D (synWex h (synWiso (.cv h) S (synCin R (synCxp (synCin D
                    (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))) (synCin D
                    (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))))) E
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))))
      z D dv_cache_0043 dv_cache_0044 p0052
  have p0054 :=
    @gJaod
      (synWa (synWa (.classMem (.cv y) D) (.classMem (.cv u) E))
        (synWa (.neg (.classMem (.cv y) (synCdm (synCuni (synCwecutiso R D S E)))))
          (synWiso (synCun (synCuni (synCwecutiso R D S E))
              (synCsn (synCop (.cv y) (.cv u)))) R S (synCun
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
              (synCsn (.cv y))) (synCun
              (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
              (synCsn (.cv u))))))
      (.classEq (synCun
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
          (synCsn (.cv y))) D)
      (synW3o (synWex h (synWiso (.cv h) R S D E)) (synWrex x E (synWex h
            (synWiso (.cv h) R (synCin S (synCxp (synCin E
                    (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv x)))) (synCin E
                    (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv x)))))) D
              (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv x)))))))
        (synWrex x D (synWex h (synWiso (.cv h) S (synCin R (synCxp (synCin D
                    (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))) (synCin D
                    (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))))) E
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))))
      (synWrex z D (.classEq (synCun
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
            (synCsn (.cv y)))
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z))))))
      p0026 p0053
  have p0055 :=
    @gMpd
      (synWa (synWa (.classMem (.cv y) D) (.classMem (.cv u) E))
        (synWa (.neg (.classMem (.cv y) (synCdm (synCuni (synCwecutiso R D S E)))))
          (synWiso (synCun (synCuni (synCwecutiso R D S E))
              (synCsn (synCop (.cv y) (.cv u)))) R S (synCun
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
              (synCsn (.cv y))) (synCun
              (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
              (synCsn (.cv u))))))
      (synWo (.classEq (synCun
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
            (synCsn (.cv y))) D) (synWrex z D (.classEq (synCun
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
              (synCsn (.cv y)))
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv z)))))))
      (synW3o (synWex h (synWiso (.cv h) R S D E)) (synWrex x E (synWex h
            (synWiso (.cv h) R (synCin S (synCxp (synCin E
                    (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv x)))) (synCin E
                    (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv x)))))) D
              (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv x)))))))
        (synWrex x D (synWex h (synWiso (.cv h) S (synCin R (synCxp (synCin D
                    (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))) (synCin D
                    (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))))) E
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))))
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

/-- Checked nominal proof certificate identified upstream as `g_wecomparisonterminalsetfdv`. -/
@[expose]
noncomputable def gWecomparisonterminalsetfdv (x : Var) (D : Class) (R : Class)
    (S : Class) (h : Var) (E : Class) (dv_D_h : h ∉ D.fv) (dv_D_x : x ∉ D.fv)
    (dv_E_h : h ∉ E.fv) (dv_E_x : x ∉ E.fv) (dv_R_h : h ∉ R.fv) (dv_R_x : x ∉ R.fv)
    (dv_S_h : h ∉ S.fv) (dv_S_x : x ∉ S.fv) (dv_h_x : h ≠ x)
    (hyp_wecomparisonterminalsetfdv_1 : Nominal.NPrf (synWbr R (synCwe) D))
    (hyp_wecomparisonterminalsetfdv_2 : Nominal.NPrf (synWbr S (synCwe) E))
    (hyp_wecomparisonterminalsetfdv_3 :
      Nominal.NPrf (.classMem (synCuni (synCwecutiso R D S E)) (synCvv))) :
    Nominal.NPrf
      (synW3o (synWex h (synWiso (.cv h) R S D E)) (synWrex x E (synWex h
            (synWiso (.cv h) R (synCin S (synCxp (synCin E
                    (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv x)))) (synCin E
                    (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv x)))))) D
              (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv x)))))))
        (synWrex x D (synWex h (synWiso (.cv h) S (synCin R (synCxp (synCin D
                    (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))) (synCin D
                    (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))))) E
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))))))) :=
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
  have dv_cache_0009 : h ∉ ((synCuni (synCwecutiso R D S E))).fv :=
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
  have dv_cache_0010 : h ∉ ((synWiso (synCuni (synCwecutiso R D S E)) R S D E)).fv :=
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
      ((synWiso (synCuni (synCwecutiso R D S E)) R (synCin S (synCxp
              (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
              (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u)))))) D
          (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u)))))).fv :=
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
      ((synWex h (synWiso (.cv h) R (synCin S (synCxp
                (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
                (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u)))))) D
            (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))))).fv :=
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
      ((synW3o (synWex h (synWiso (.cv h) R S D E)) (synWrex x E (synWex h
              (synWiso (.cv h) R (synCin S (synCxp (synCin E
                      (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv x)))) (synCin E
                      (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv x)))))) D
                (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv x)))))))
          (synWrex x D (synWex h (synWiso (.cv h) S (synCin R (synCxp (synCin D
                      (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))) (synCin D
                      (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))))) E
                (synCin D (synCima (synCcnv (synCdif R (synCid)))
                    (synCsn (.cv x))))))))).fv :=
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
    u ∉ ((Wff.classEq (synCdm (synCuni (synCwecutiso R D S E))) D)).fv :=
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
  have dv_cache_0018 : h ∉ ((synCcnv (synCuni (synCwecutiso R D S E)))).fv :=
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
      ((synWiso (synCcnv (synCuni (synCwecutiso R D S E))) S (synCin R (synCxp
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y)))))) E
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y)))))).fv :=
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
      ((synWex h (synWiso (.cv h) S (synCin R (synCxp
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y)))))) E
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))).fv :=
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
      ((synWa (.classMem (.cv y) D) (.classEq (synCdm (synCuni (synCwecutiso R D S E)))
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))).fv :=
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
      ((synW3o (synWex h (synWiso (.cv h) R S D E)) (synWrex x E (synWex h
              (synWiso (.cv h) R (synCin S (synCxp (synCin E
                      (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv x)))) (synCin E
                      (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv x)))))) D
                (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv x)))))))
          (synWrex x D (synWex h (synWiso (.cv h) S (synCin R (synCxp (synCin D
                      (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))) (synCin D
                      (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))))) E
                (synCin D (synCima (synCcnv (synCdif R (synCid)))
                    (synCsn (.cv x))))))))).fv :=
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
    @gWecutisouniondmcutorwholendv y D R S E dv_cache_0001 dv_cache_0002 dv_cache_0003
      dv_cache_0004 hyp_wecomparisonterminalsetfdv_1 hyp_wecomparisonterminalsetfdv_3
  have p0001 :=
    @gWecutisounionrncutorwholendv u D R S E dv_cache_0005 dv_cache_0006 dv_cache_0007
      dv_cache_0008 hyp_wecomparisonterminalsetfdv_2 hyp_wecomparisonterminalsetfdv_3
  have p0002 :=
    @gA1i
      (synWo (.classEq (synCrn (synCuni (synCwecutiso R D S E))) E) (synWrex u E
          (.classEq (synCrn (synCuni (synCwecutiso R D S E)))
            (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u)))))))
      (.classEq (synCdm (synCuni (synCwecutiso R D S E))) D) p0001
  have p0003 :=
    @gWecutisounionisondv D R S E hyp_wecomparisonterminalsetfdv_1
      hyp_wecomparisonterminalsetfdv_2
  have p0004 :=
    @gA1i
      (synWiso (synCuni (synCwecutiso R D S E)) R S
        (synCdm (synCuni (synCwecutiso R D S E)))
        (synCrn (synCuni (synCwecutiso R D S E))))
      (synWa (.classEq (synCdm (synCuni (synCwecutiso R D S E))) D)
        (.classEq (synCrn (synCuni (synCwecutiso R D S E))) E))
      p0003
  have p0005 :=
    @gSimpl (.classEq (synCdm (synCuni (synCwecutiso R D S E))) D)
      (.classEq (synCrn (synCuni (synCwecutiso R D S E))) E)
  have p0006 :=
    @gIsoeq4 (synCdm (synCuni (synCwecutiso R D S E)))
      (synCrn (synCuni (synCwecutiso R D S E))) D R S
      (synCuni (synCwecutiso R D S E))
  have p0007 :=
    @gSyl
      (synWa (.classEq (synCdm (synCuni (synCwecutiso R D S E))) D)
        (.classEq (synCrn (synCuni (synCwecutiso R D S E))) E))
      (.classEq (synCdm (synCuni (synCwecutiso R D S E))) D)
      (synWb (synWiso (synCuni (synCwecutiso R D S E)) R S
          (synCdm (synCuni (synCwecutiso R D S E)))
          (synCrn (synCuni (synCwecutiso R D S E))))
        (synWiso (synCuni (synCwecutiso R D S E)) R S D
          (synCrn (synCuni (synCwecutiso R D S E)))))
      p0005 p0006
  have p0008 :=
    @gMpbid
      (synWa (.classEq (synCdm (synCuni (synCwecutiso R D S E))) D)
        (.classEq (synCrn (synCuni (synCwecutiso R D S E))) E))
      (synWiso (synCuni (synCwecutiso R D S E)) R S
        (synCdm (synCuni (synCwecutiso R D S E)))
        (synCrn (synCuni (synCwecutiso R D S E))))
      (synWiso (synCuni (synCwecutiso R D S E)) R S D
        (synCrn (synCuni (synCwecutiso R D S E))))
      p0004 p0007
  have p0009 :=
    @gSimpr (.classEq (synCdm (synCuni (synCwecutiso R D S E))) D)
      (.classEq (synCrn (synCuni (synCwecutiso R D S E))) E)
  have p0010 :=
    @gIsoeq5 D (synCrn (synCuni (synCwecutiso R D S E))) E R S
      (synCuni (synCwecutiso R D S E))
  have p0011 :=
    @gSyl
      (synWa (.classEq (synCdm (synCuni (synCwecutiso R D S E))) D)
        (.classEq (synCrn (synCuni (synCwecutiso R D S E))) E))
      (.classEq (synCrn (synCuni (synCwecutiso R D S E))) E)
      (synWb (synWiso (synCuni (synCwecutiso R D S E)) R S D
          (synCrn (synCuni (synCwecutiso R D S E))))
        (synWiso (synCuni (synCwecutiso R D S E)) R S D E))
      p0009 p0010
  have p0012 :=
    @gMpbid
      (synWa (.classEq (synCdm (synCuni (synCwecutiso R D S E))) D)
        (.classEq (synCrn (synCuni (synCwecutiso R D S E))) E))
      (synWiso (synCuni (synCwecutiso R D S E)) R S D
        (synCrn (synCuni (synCwecutiso R D S E))))
      (synWiso (synCuni (synCwecutiso R D S E)) R S D E) p0008 p0011
  have p0013 := @gIsoeq1 D E R S (synCuni (synCwecutiso R D S E)) (.cv h)
  have p0014 :=
    @gSpcev (synWiso (.cv h) R S D E)
      (synWiso (synCuni (synCwecutiso R D S E)) R S D E) h
      (synCuni (synCwecutiso R D S E)) dv_cache_0009 dv_cache_0010
      hyp_wecomparisonterminalsetfdv_3 p0013
  have p0015 :=
    @gSyl
      (synWa (.classEq (synCdm (synCuni (synCwecutiso R D S E))) D)
        (.classEq (synCrn (synCuni (synCwecutiso R D S E))) E))
      (synWiso (synCuni (synCwecutiso R D S E)) R S D E)
      (synWex h (synWiso (.cv h) R S D E)) p0012 p0014
  have p0016 :=
    @gN3mix1 (synWex h (synWiso (.cv h) R S D E))
      (synWrex x E (synWex h (synWiso (.cv h) R (synCin S (synCxp
                (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv x))))
                (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv x)))))) D
            (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv x)))))))
      (synWrex x D (synWex h (synWiso (.cv h) S (synCin R (synCxp
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))))) E
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))))))
  have p0017 :=
    @gSyl
      (synWa (.classEq (synCdm (synCuni (synCwecutiso R D S E))) D)
        (.classEq (synCrn (synCuni (synCwecutiso R D S E))) E))
      (synWex h (synWiso (.cv h) R S D E))
      (synW3o (synWex h (synWiso (.cv h) R S D E)) (synWrex x E (synWex h
            (synWiso (.cv h) R (synCin S (synCxp (synCin E
                    (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv x)))) (synCin E
                    (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv x)))))) D
              (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv x)))))))
        (synWrex x D (synWex h (synWiso (.cv h) S (synCin R (synCxp (synCin D
                    (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))) (synCin D
                    (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))))) E
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))))
      p0015 p0016
  have p0018 :=
    @gEx (.classEq (synCdm (synCuni (synCwecutiso R D S E))) D)
      (.classEq (synCrn (synCuni (synCwecutiso R D S E))) E)
      (synW3o (synWex h (synWiso (.cv h) R S D E)) (synWrex x E (synWex h
            (synWiso (.cv h) R (synCin S (synCxp (synCin E
                    (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv x)))) (synCin E
                    (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv x)))))) D
              (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv x)))))))
        (synWrex x D (synWex h (synWiso (.cv h) S (synCin R (synCxp (synCin D
                    (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))) (synCin D
                    (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))))) E
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))))
      p0017
  have p0019 :=
    @gSimpl
      (synWa (.classEq (synCdm (synCuni (synCwecutiso R D S E))) D) (.classMem (.cv u) E))
      (.classEq (synCrn (synCuni (synCwecutiso R D S E)))
        (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u)))))
  have p0020 :=
    @gSimpr (.classEq (synCdm (synCuni (synCwecutiso R D S E))) D)
      (.classMem (.cv u) E)
  have p0021 :=
    @gSyl
      (synWa (synWa (.classEq (synCdm (synCuni (synCwecutiso R D S E))) D)
          (.classMem (.cv u) E)) (.classEq (synCrn (synCuni (synCwecutiso R D S E)))
          (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))))
      (synWa (.classEq (synCdm (synCuni (synCwecutiso R D S E))) D) (.classMem (.cv u) E))
      (.classMem (.cv u) E) p0019 p0020
  have p0023 :=
    @gA1i
      (synWiso (synCuni (synCwecutiso R D S E)) R S
        (synCdm (synCuni (synCwecutiso R D S E)))
        (synCrn (synCuni (synCwecutiso R D S E))))
      (synWa (synWa (.classEq (synCdm (synCuni (synCwecutiso R D S E))) D)
          (.classMem (.cv u) E)) (.classEq (synCrn (synCuni (synCwecutiso R D S E)))
          (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))))
      p0003
  have p0025 :=
    @gSimpl (.classEq (synCdm (synCuni (synCwecutiso R D S E))) D)
      (.classMem (.cv u) E)
  have p0026 :=
    @gSyl
      (synWa (synWa (.classEq (synCdm (synCuni (synCwecutiso R D S E))) D)
          (.classMem (.cv u) E)) (.classEq (synCrn (synCuni (synCwecutiso R D S E)))
          (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))))
      (synWa (.classEq (synCdm (synCuni (synCwecutiso R D S E))) D) (.classMem (.cv u) E))
      (.classEq (synCdm (synCuni (synCwecutiso R D S E))) D) p0019 p0025
  have p0028 :=
    @gSyl
      (synWa (synWa (.classEq (synCdm (synCuni (synCwecutiso R D S E))) D)
          (.classMem (.cv u) E)) (.classEq (synCrn (synCuni (synCwecutiso R D S E)))
          (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))))
      (.classEq (synCdm (synCuni (synCwecutiso R D S E))) D)
      (synWb (synWiso (synCuni (synCwecutiso R D S E)) R S
          (synCdm (synCuni (synCwecutiso R D S E)))
          (synCrn (synCuni (synCwecutiso R D S E))))
        (synWiso (synCuni (synCwecutiso R D S E)) R S D
          (synCrn (synCuni (synCwecutiso R D S E)))))
      p0026 p0006
  have p0029 :=
    @gMpbid
      (synWa (synWa (.classEq (synCdm (synCuni (synCwecutiso R D S E))) D)
          (.classMem (.cv u) E)) (.classEq (synCrn (synCuni (synCwecutiso R D S E)))
          (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))))
      (synWiso (synCuni (synCwecutiso R D S E)) R S
        (synCdm (synCuni (synCwecutiso R D S E)))
        (synCrn (synCuni (synCwecutiso R D S E))))
      (synWiso (synCuni (synCwecutiso R D S E)) R S D
        (synCrn (synCuni (synCwecutiso R D S E))))
      p0023 p0028
  have p0030 :=
    @gSimpr
      (synWa (.classEq (synCdm (synCuni (synCwecutiso R D S E))) D) (.classMem (.cv u) E))
      (.classEq (synCrn (synCuni (synCwecutiso R D S E)))
        (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u)))))
  have p0031 :=
    @gIsoeq5 D (synCrn (synCuni (synCwecutiso R D S E)))
      (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u)))) R S
      (synCuni (synCwecutiso R D S E))
  have p0032 :=
    @gSyl
      (synWa (synWa (.classEq (synCdm (synCuni (synCwecutiso R D S E))) D)
          (.classMem (.cv u) E)) (.classEq (synCrn (synCuni (synCwecutiso R D S E)))
          (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))))
      (.classEq (synCrn (synCuni (synCwecutiso R D S E)))
        (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u)))))
      (synWb (synWiso (synCuni (synCwecutiso R D S E)) R S D
          (synCrn (synCuni (synCwecutiso R D S E))))
        (synWiso (synCuni (synCwecutiso R D S E)) R S D
          (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))))
      p0030 p0031
  have p0033 :=
    @gMpbid
      (synWa (synWa (.classEq (synCdm (synCuni (synCwecutiso R D S E))) D)
          (.classMem (.cv u) E)) (.classEq (synCrn (synCuni (synCwecutiso R D S E)))
          (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))))
      (synWiso (synCuni (synCwecutiso R D S E)) R S D
        (synCrn (synCuni (synCwecutiso R D S E))))
      (synWiso (synCuni (synCwecutiso R D S E)) R S D
        (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u)))))
      p0029 p0032
  have p0034 :=
    @gIsores2 D
      (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u)))) R S
      (synCuni (synCwecutiso R D S E))
  have p0035 :=
    @gBiimpi
      (synWiso (synCuni (synCwecutiso R D S E)) R S D
        (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u)))))
      (synWiso (synCuni (synCwecutiso R D S E)) R (synCin S (synCxp
            (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
            (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))))
        D (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u)))))
      p0034
  have p0036 :=
    @gSyl
      (synWa (synWa (.classEq (synCdm (synCuni (synCwecutiso R D S E))) D)
          (.classMem (.cv u) E)) (.classEq (synCrn (synCuni (synCwecutiso R D S E)))
          (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))))
      (synWiso (synCuni (synCwecutiso R D S E)) R S D
        (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u)))))
      (synWiso (synCuni (synCwecutiso R D S E)) R (synCin S (synCxp
            (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
            (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))))
        D (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u)))))
      p0033 p0035
  have p0037 :=
    @gIsoeq1 D (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
      R
      (synCin S (synCxp
          (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
          (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))))
      (synCuni (synCwecutiso R D S E)) (.cv h)
  have p0038 :=
    @gSpcev
      (synWiso (.cv h) R (synCin S (synCxp
            (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
            (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))))
        D (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u)))))
      (synWiso (synCuni (synCwecutiso R D S E)) R (synCin S (synCxp
            (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
            (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))))
        D (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u)))))
      h (synCuni (synCwecutiso R D S E)) dv_cache_0009 dv_cache_0011
      hyp_wecomparisonterminalsetfdv_3 p0037
  have p0039 :=
    @gSyl
      (synWa (synWa (.classEq (synCdm (synCuni (synCwecutiso R D S E))) D)
          (.classMem (.cv u) E)) (.classEq (synCrn (synCuni (synCwecutiso R D S E)))
          (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))))
      (synWiso (synCuni (synCwecutiso R D S E)) R (synCin S (synCxp
            (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
            (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))))
        D (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u)))))
      (synWex h (synWiso (.cv h) R (synCin S (synCxp
              (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
              (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))))
          D (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))))
      p0036 p0038
  have p0040 :=
    @gJca
      (synWa (synWa (.classEq (synCdm (synCuni (synCwecutiso R D S E))) D)
          (.classMem (.cv u) E)) (.classEq (synCrn (synCuni (synCwecutiso R D S E)))
          (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))))
      (.classMem (.cv u) E)
      (synWex h (synWiso (.cv h) R (synCin S (synCxp
              (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
              (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))))
          D (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))))
      p0021 p0039
  have p0041 := @gSneq (.cv x) (.cv u)
  have p0042 :=
    @gImaeq2d (.classEq (.cv x) (.cv u)) (synCsn (.cv x)) (synCsn (.cv u))
      (synCcnv (synCdif S (synCid))) p0041
  have p0043 :=
    @gIneq2d (.classEq (.cv x) (.cv u))
      (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv x)))
      (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))) E p0042
  have p0047 :=
    @gXpeq12d (.classEq (.cv x) (.cv u))
      (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv x))))
      (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
      (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv x))))
      (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u)))) p0043
      p0043
  have p0048 :=
    @gIneq2d (.classEq (.cv x) (.cv u))
      (synCxp (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv x))))
        (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv x)))))
      (synCxp (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
        (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u)))))
      S p0047
  have p0049 :=
    @gIsoeq3 D (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv x))))
      R
      (synCin S (synCxp
          (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv x))))
          (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv x))))))
      (synCin S (synCxp
          (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
          (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))))
      (.cv h)
  have p0050 :=
    @gSyl (.classEq (.cv x) (.cv u))
      (.classEq (synCin S (synCxp
            (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv x))))
            (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv x))))))
        (synCin S (synCxp
            (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
            (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u)))))))
      (synWb (synWiso (.cv h) R (synCin S (synCxp
              (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv x))))
              (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv x))))))
          D (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv x)))))
        (synWiso (.cv h) R (synCin S (synCxp
              (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
              (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))))
          D (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv x))))))
      p0048 p0049
  have p0054 :=
    @gIsoeq5 D (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv x))))
      (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u)))) R
      (synCin S (synCxp
          (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
          (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))))
      (.cv h)
  have p0055 :=
    @gSyl (.classEq (.cv x) (.cv u))
      (.classEq (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv x))))
        (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u)))))
      (synWb (synWiso (.cv h) R (synCin S (synCxp
              (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
              (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))))
          D (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv x)))))
        (synWiso (.cv h) R (synCin S (synCxp
              (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
              (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))))
          D (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))))
      p0043 p0054
  have p0056 :=
    @gBitrd (.classEq (.cv x) (.cv u))
      (synWiso (.cv h) R (synCin S (synCxp
            (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv x))))
            (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv x))))))
        D (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv x)))))
      (synWiso (.cv h) R (synCin S (synCxp
            (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
            (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))))
        D (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv x)))))
      (synWiso (.cv h) R (synCin S (synCxp
            (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
            (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))))
        D (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u)))))
      p0050 p0055
  have p0057 :=
    @gExbidv (.classEq (.cv x) (.cv u))
      (synWiso (.cv h) R (synCin S (synCxp
            (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv x))))
            (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv x))))))
        D (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv x)))))
      (synWiso (.cv h) R (synCin S (synCxp
            (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
            (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))))
        D (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u)))))
      h dv_cache_0012 p0056
  have p0058 :=
    @gRspcev
      (synWex h (synWiso (.cv h) R (synCin S (synCxp
              (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv x))))
              (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv x))))))
          D (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv x))))))
      (synWex h (synWiso (.cv h) R (synCin S (synCxp
              (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
              (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))))
          D (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))))
      x (.cv u) E dv_cache_0013 dv_cache_0014 dv_cache_0015 p0057
  have p0059 :=
    @gSyl
      (synWa (synWa (.classEq (synCdm (synCuni (synCwecutiso R D S E))) D)
          (.classMem (.cv u) E)) (.classEq (synCrn (synCuni (synCwecutiso R D S E)))
          (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))))
      (synWa (.classMem (.cv u) E) (synWex h (synWiso (.cv h) R (synCin S (synCxp
                (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
                (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u)))))) D
            (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u)))))))
      (synWrex x E (synWex h (synWiso (.cv h) R (synCin S (synCxp
                (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv x))))
                (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv x)))))) D
            (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv x)))))))
      p0040 p0058
  have p0060 :=
    @gN3mix2
      (synWrex x E (synWex h (synWiso (.cv h) R (synCin S (synCxp
                (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv x))))
                (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv x)))))) D
            (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv x)))))))
      (synWex h (synWiso (.cv h) R S D E))
      (synWrex x D (synWex h (synWiso (.cv h) S (synCin R (synCxp
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))))) E
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))))))
  have p0061 :=
    @gSyl
      (synWa (synWa (.classEq (synCdm (synCuni (synCwecutiso R D S E))) D)
          (.classMem (.cv u) E)) (.classEq (synCrn (synCuni (synCwecutiso R D S E)))
          (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))))
      (synWrex x E (synWex h (synWiso (.cv h) R (synCin S (synCxp
                (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv x))))
                (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv x)))))) D
            (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv x)))))))
      (synW3o (synWex h (synWiso (.cv h) R S D E)) (synWrex x E (synWex h
            (synWiso (.cv h) R (synCin S (synCxp (synCin E
                    (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv x)))) (synCin E
                    (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv x)))))) D
              (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv x)))))))
        (synWrex x D (synWex h (synWiso (.cv h) S (synCin R (synCxp (synCin D
                    (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))) (synCin D
                    (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))))) E
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))))
      p0059 p0060
  have p0062 :=
    @gEx
      (synWa (.classEq (synCdm (synCuni (synCwecutiso R D S E))) D) (.classMem (.cv u) E))
      (.classEq (synCrn (synCuni (synCwecutiso R D S E)))
        (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u)))))
      (synW3o (synWex h (synWiso (.cv h) R S D E)) (synWrex x E (synWex h
            (synWiso (.cv h) R (synCin S (synCxp (synCin E
                    (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv x)))) (synCin E
                    (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv x)))))) D
              (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv x)))))))
        (synWrex x D (synWex h (synWiso (.cv h) S (synCin R (synCxp (synCin D
                    (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))) (synCin D
                    (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))))) E
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))))
      p0061
  have p0063 :=
    @gRexlimdva (.classEq (synCdm (synCuni (synCwecutiso R D S E))) D)
      (.classEq (synCrn (synCuni (synCwecutiso R D S E)))
        (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u)))))
      (synW3o (synWex h (synWiso (.cv h) R S D E)) (synWrex x E (synWex h
            (synWiso (.cv h) R (synCin S (synCxp (synCin E
                    (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv x)))) (synCin E
                    (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv x)))))) D
              (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv x)))))))
        (synWrex x D (synWex h (synWiso (.cv h) S (synCin R (synCxp (synCin D
                    (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))) (synCin D
                    (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))))) E
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))))
      u E dv_cache_0016 dv_cache_0017 p0062
  have p0064 :=
    @gJaod (.classEq (synCdm (synCuni (synCwecutiso R D S E))) D)
      (.classEq (synCrn (synCuni (synCwecutiso R D S E))) E)
      (synW3o (synWex h (synWiso (.cv h) R S D E)) (synWrex x E (synWex h
            (synWiso (.cv h) R (synCin S (synCxp (synCin E
                    (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv x)))) (synCin E
                    (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv x)))))) D
              (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv x)))))))
        (synWrex x D (synWex h (synWiso (.cv h) S (synCin R (synCxp (synCin D
                    (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))) (synCin D
                    (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))))) E
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))))
      (synWrex u E (.classEq (synCrn (synCuni (synCwecutiso R D S E)))
          (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))))
      p0018 p0063
  have p0065 :=
    @gMpd (.classEq (synCdm (synCuni (synCwecutiso R D S E))) D)
      (synWo (.classEq (synCrn (synCuni (synCwecutiso R D S E))) E) (synWrex u E
          (.classEq (synCrn (synCuni (synCwecutiso R D S E)))
            (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u)))))))
      (synW3o (synWex h (synWiso (.cv h) R S D E)) (synWrex x E (synWex h
            (synWiso (.cv h) R (synCin S (synCxp (synCin E
                    (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv x)))) (synCin E
                    (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv x)))))) D
              (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv x)))))))
        (synWrex x D (synWex h (synWiso (.cv h) S (synCin R (synCxp (synCin D
                    (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))) (synCin D
                    (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))))) E
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))))
      p0002 p0064
  have p0067 :=
    @gA1i
      (synWo (.classEq (synCrn (synCuni (synCwecutiso R D S E))) E) (synWrex u E
          (.classEq (synCrn (synCuni (synCwecutiso R D S E)))
            (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u)))))))
      (synWa (.classMem (.cv y) D) (.classEq (synCdm (synCuni (synCwecutiso R D S E)))
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
      p0001
  have p0068 :=
    @gSimpl
      (synWa (.classMem (.cv y) D) (.classEq (synCdm (synCuni (synCwecutiso R D S E)))
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
      (.classEq (synCrn (synCuni (synCwecutiso R D S E))) E)
  have p0069 :=
    @gSimpl (.classMem (.cv y) D)
      (.classEq (synCdm (synCuni (synCwecutiso R D S E)))
        (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y)))))
  have p0070 :=
    @gSyl
      (synWa (synWa (.classMem (.cv y) D)
          (.classEq (synCdm (synCuni (synCwecutiso R D S E)))
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
        (.classEq (synCrn (synCuni (synCwecutiso R D S E))) E))
      (synWa (.classMem (.cv y) D) (.classEq (synCdm (synCuni (synCwecutiso R D S E)))
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
      (.classMem (.cv y) D) p0068 p0069
  have p0072 :=
    @gA1i
      (synWiso (synCuni (synCwecutiso R D S E)) R S
        (synCdm (synCuni (synCwecutiso R D S E)))
        (synCrn (synCuni (synCwecutiso R D S E))))
      (synWa (synWa (.classMem (.cv y) D)
          (.classEq (synCdm (synCuni (synCwecutiso R D S E)))
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
        (.classEq (synCrn (synCuni (synCwecutiso R D S E))) E))
      p0003
  have p0074 :=
    @gSimpr (.classMem (.cv y) D)
      (.classEq (synCdm (synCuni (synCwecutiso R D S E)))
        (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y)))))
  have p0075 :=
    @gSyl
      (synWa (synWa (.classMem (.cv y) D)
          (.classEq (synCdm (synCuni (synCwecutiso R D S E)))
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
        (.classEq (synCrn (synCuni (synCwecutiso R D S E))) E))
      (synWa (.classMem (.cv y) D) (.classEq (synCdm (synCuni (synCwecutiso R D S E)))
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
      (.classEq (synCdm (synCuni (synCwecutiso R D S E)))
        (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y)))))
      p0068 p0074
  have p0076 :=
    @gIsoeq4 (synCdm (synCuni (synCwecutiso R D S E)))
      (synCrn (synCuni (synCwecutiso R D S E)))
      (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y)))) R S
      (synCuni (synCwecutiso R D S E))
  have p0077 :=
    @gSyl
      (synWa (synWa (.classMem (.cv y) D)
          (.classEq (synCdm (synCuni (synCwecutiso R D S E)))
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
        (.classEq (synCrn (synCuni (synCwecutiso R D S E))) E))
      (.classEq (synCdm (synCuni (synCwecutiso R D S E)))
        (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y)))))
      (synWb (synWiso (synCuni (synCwecutiso R D S E)) R S
          (synCdm (synCuni (synCwecutiso R D S E)))
          (synCrn (synCuni (synCwecutiso R D S E))))
        (synWiso (synCuni (synCwecutiso R D S E)) R S
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
          (synCrn (synCuni (synCwecutiso R D S E)))))
      p0075 p0076
  have p0078 :=
    @gMpbid
      (synWa (synWa (.classMem (.cv y) D)
          (.classEq (synCdm (synCuni (synCwecutiso R D S E)))
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
        (.classEq (synCrn (synCuni (synCwecutiso R D S E))) E))
      (synWiso (synCuni (synCwecutiso R D S E)) R S
        (synCdm (synCuni (synCwecutiso R D S E)))
        (synCrn (synCuni (synCwecutiso R D S E))))
      (synWiso (synCuni (synCwecutiso R D S E)) R S
        (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
        (synCrn (synCuni (synCwecutiso R D S E))))
      p0072 p0077
  have p0079 :=
    @gSimpr
      (synWa (.classMem (.cv y) D) (.classEq (synCdm (synCuni (synCwecutiso R D S E)))
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
      (.classEq (synCrn (synCuni (synCwecutiso R D S E))) E)
  have p0080 :=
    @gIsoeq5 (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
      (synCrn (synCuni (synCwecutiso R D S E))) E R S
      (synCuni (synCwecutiso R D S E))
  have p0081 :=
    @gSyl
      (synWa (synWa (.classMem (.cv y) D)
          (.classEq (synCdm (synCuni (synCwecutiso R D S E)))
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
        (.classEq (synCrn (synCuni (synCwecutiso R D S E))) E))
      (.classEq (synCrn (synCuni (synCwecutiso R D S E))) E)
      (synWb (synWiso (synCuni (synCwecutiso R D S E)) R S
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
          (synCrn (synCuni (synCwecutiso R D S E))))
        (synWiso (synCuni (synCwecutiso R D S E)) R S
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y)))) E))
      p0079 p0080
  have p0082 :=
    @gMpbid
      (synWa (synWa (.classMem (.cv y) D)
          (.classEq (synCdm (synCuni (synCwecutiso R D S E)))
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
        (.classEq (synCrn (synCuni (synCwecutiso R D S E))) E))
      (synWiso (synCuni (synCwecutiso R D S E)) R S
        (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
        (synCrn (synCuni (synCwecutiso R D S E))))
      (synWiso (synCuni (synCwecutiso R D S E)) R S
        (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y)))) E)
      p0078 p0081
  have p0083 :=
    @gIsocnv (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y)))) E
      R S (synCuni (synCwecutiso R D S E))
  have p0084 :=
    @gSyl
      (synWa (synWa (.classMem (.cv y) D)
          (.classEq (synCdm (synCuni (synCwecutiso R D S E)))
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
        (.classEq (synCrn (synCuni (synCwecutiso R D S E))) E))
      (synWiso (synCuni (synCwecutiso R D S E)) R S
        (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y)))) E)
      (synWiso (synCcnv (synCuni (synCwecutiso R D S E))) S R E
        (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y)))))
      p0082 p0083
  have p0085 :=
    @gIsores2 E
      (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y)))) S R
      (synCcnv (synCuni (synCwecutiso R D S E)))
  have p0086 :=
    @gBiimpi
      (synWiso (synCcnv (synCuni (synCwecutiso R D S E))) S R E
        (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y)))))
      (synWiso (synCcnv (synCuni (synCwecutiso R D S E))) S (synCin R (synCxp
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
        E (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y)))))
      p0085
  have p0087 :=
    @gSyl
      (synWa (synWa (.classMem (.cv y) D)
          (.classEq (synCdm (synCuni (synCwecutiso R D S E)))
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
        (.classEq (synCrn (synCuni (synCwecutiso R D S E))) E))
      (synWiso (synCcnv (synCuni (synCwecutiso R D S E))) S R E
        (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y)))))
      (synWiso (synCcnv (synCuni (synCwecutiso R D S E))) S (synCin R (synCxp
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
        E (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y)))))
      p0084 p0086
  have p0088 :=
    @gCnvex (synCuni (synCwecutiso R D S E)) hyp_wecomparisonterminalsetfdv_3
  have p0089 :=
    @gIsoeq1 E (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
      S
      (synCin R (synCxp
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
      (synCcnv (synCuni (synCwecutiso R D S E))) (.cv h)
  have p0090 :=
    @gSpcev
      (synWiso (.cv h) S (synCin R (synCxp
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
        E (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y)))))
      (synWiso (synCcnv (synCuni (synCwecutiso R D S E))) S (synCin R (synCxp
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
        E (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y)))))
      h (synCcnv (synCuni (synCwecutiso R D S E))) dv_cache_0018 dv_cache_0019 p0088
      p0089
  have p0091 :=
    @gSyl
      (synWa (synWa (.classMem (.cv y) D)
          (.classEq (synCdm (synCuni (synCwecutiso R D S E)))
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
        (.classEq (synCrn (synCuni (synCwecutiso R D S E))) E))
      (synWiso (synCcnv (synCuni (synCwecutiso R D S E))) S (synCin R (synCxp
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
        E (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y)))))
      (synWex h (synWiso (.cv h) S (synCin R (synCxp
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
          E (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
      p0087 p0090
  have p0092 :=
    @gJca
      (synWa (synWa (.classMem (.cv y) D)
          (.classEq (synCdm (synCuni (synCwecutiso R D S E)))
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
        (.classEq (synCrn (synCuni (synCwecutiso R D S E))) E))
      (.classMem (.cv y) D)
      (synWex h (synWiso (.cv h) S (synCin R (synCxp
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
          E (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
      p0070 p0091
  have p0093 := @gSneq (.cv x) (.cv y)
  have p0094 :=
    @gImaeq2d (.classEq (.cv x) (.cv y)) (synCsn (.cv x)) (synCsn (.cv y))
      (synCcnv (synCdif R (synCid))) p0093
  have p0095 :=
    @gIneq2d (.classEq (.cv x) (.cv y))
      (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))
      (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))) D p0094
  have p0099 :=
    @gXpeq12d (.classEq (.cv x) (.cv y))
      (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
      (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
      (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
      (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y)))) p0095
      p0095
  have p0100 :=
    @gIneq2d (.classEq (.cv x) (.cv y))
      (synCxp (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
        (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))))
      (synCxp (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
        (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y)))))
      R p0099
  have p0101 :=
    @gIsoeq3 E (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
      S
      (synCin R (synCxp
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))
      (synCin R (synCxp
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
      (.cv h)
  have p0102 :=
    @gSyl (.classEq (.cv x) (.cv y))
      (.classEq (synCin R (synCxp
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))
        (synCin R (synCxp
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y)))))))
      (synWb (synWiso (.cv h) S (synCin R (synCxp
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))
          E (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))))
        (synWiso (.cv h) S (synCin R (synCxp
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
          E (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))
      p0100 p0101
  have p0106 :=
    @gIsoeq5 E (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
      (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y)))) S
      (synCin R (synCxp
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
      (.cv h)
  have p0107 :=
    @gSyl (.classEq (.cv x) (.cv y))
      (.classEq (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
        (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y)))))
      (synWb (synWiso (.cv h) S (synCin R (synCxp
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
          E (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))))
        (synWiso (.cv h) S (synCin R (synCxp
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
          E (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
      p0095 p0106
  have p0108 :=
    @gBitrd (.classEq (.cv x) (.cv y))
      (synWiso (.cv h) S (synCin R (synCxp
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))
        E (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))))
      (synWiso (.cv h) S (synCin R (synCxp
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
        E (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))))
      (synWiso (.cv h) S (synCin R (synCxp
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
        E (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y)))))
      p0102 p0107
  have p0109 :=
    @gExbidv (.classEq (.cv x) (.cv y))
      (synWiso (.cv h) S (synCin R (synCxp
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))
        E (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))))
      (synWiso (.cv h) S (synCin R (synCxp
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
        E (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y)))))
      h dv_cache_0020 p0108
  have p0110 :=
    @gRspcev
      (synWex h (synWiso (.cv h) S (synCin R (synCxp
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))
          E (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))
      (synWex h (synWiso (.cv h) S (synCin R (synCxp
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
          E (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
      x (.cv y) D dv_cache_0021 dv_cache_0022 dv_cache_0023 p0109
  have p0111 :=
    @gSyl
      (synWa (synWa (.classMem (.cv y) D)
          (.classEq (synCdm (synCuni (synCwecutiso R D S E)))
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
        (.classEq (synCrn (synCuni (synCwecutiso R D S E))) E))
      (synWa (.classMem (.cv y) D) (synWex h (synWiso (.cv h) S (synCin R (synCxp
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y)))))) E
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y)))))))
      (synWrex x D (synWex h (synWiso (.cv h) S (synCin R (synCxp
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))))) E
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))))))
      p0092 p0110
  have p0112 :=
    @gN3mix3
      (synWrex x D (synWex h (synWiso (.cv h) S (synCin R (synCxp
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))))) E
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))))))
      (synWex h (synWiso (.cv h) R S D E))
      (synWrex x E (synWex h (synWiso (.cv h) R (synCin S (synCxp
                (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv x))))
                (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv x)))))) D
            (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv x)))))))
  have p0113 :=
    @gSyl
      (synWa (synWa (.classMem (.cv y) D)
          (.classEq (synCdm (synCuni (synCwecutiso R D S E)))
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
        (.classEq (synCrn (synCuni (synCwecutiso R D S E))) E))
      (synWrex x D (synWex h (synWiso (.cv h) S (synCin R (synCxp
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))))) E
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))))))
      (synW3o (synWex h (synWiso (.cv h) R S D E)) (synWrex x E (synWex h
            (synWiso (.cv h) R (synCin S (synCxp (synCin E
                    (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv x)))) (synCin E
                    (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv x)))))) D
              (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv x)))))))
        (synWrex x D (synWex h (synWiso (.cv h) S (synCin R (synCxp (synCin D
                    (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))) (synCin D
                    (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))))) E
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))))
      p0111 p0112
  have p0114 :=
    @gEx
      (synWa (.classMem (.cv y) D) (.classEq (synCdm (synCuni (synCwecutiso R D S E)))
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
      (.classEq (synCrn (synCuni (synCwecutiso R D S E))) E)
      (synW3o (synWex h (synWiso (.cv h) R S D E)) (synWrex x E (synWex h
            (synWiso (.cv h) R (synCin S (synCxp (synCin E
                    (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv x)))) (synCin E
                    (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv x)))))) D
              (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv x)))))))
        (synWrex x D (synWex h (synWiso (.cv h) S (synCin R (synCxp (synCin D
                    (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))) (synCin D
                    (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))))) E
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))))
      p0113
  have p0115 :=
    @gSimpl
      (synWa (synWa (.classMem (.cv y) D)
          (.classEq (synCdm (synCuni (synCwecutiso R D S E)))
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
        (.classMem (.cv u) E))
      (.classEq (synCrn (synCuni (synCwecutiso R D S E)))
        (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u)))))
  have p0116 :=
    @gSimpl
      (synWa (.classMem (.cv y) D) (.classEq (synCdm (synCuni (synCwecutiso R D S E)))
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
      (.classMem (.cv u) E)
  have p0117 :=
    @gSyl
      (synWa (synWa (synWa (.classMem (.cv y) D)
            (.classEq (synCdm (synCuni (synCwecutiso R D S E)))
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
          (.classMem (.cv u) E)) (.classEq (synCrn (synCuni (synCwecutiso R D S E)))
          (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))))
      (synWa (synWa (.classMem (.cv y) D)
          (.classEq (synCdm (synCuni (synCwecutiso R D S E)))
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
        (.classMem (.cv u) E))
      (synWa (.classMem (.cv y) D) (.classEq (synCdm (synCuni (synCwecutiso R D S E)))
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
      p0115 p0116
  have p0119 :=
    @gSyl
      (synWa (synWa (synWa (.classMem (.cv y) D)
            (.classEq (synCdm (synCuni (synCwecutiso R D S E)))
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
          (.classMem (.cv u) E)) (.classEq (synCrn (synCuni (synCwecutiso R D S E)))
          (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))))
      (synWa (.classMem (.cv y) D) (.classEq (synCdm (synCuni (synCwecutiso R D S E)))
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
      (.classMem (.cv y) D) p0117 p0069
  have p0121 :=
    @gSimpr
      (synWa (.classMem (.cv y) D) (.classEq (synCdm (synCuni (synCwecutiso R D S E)))
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
      (.classMem (.cv u) E)
  have p0122 :=
    @gSyl
      (synWa (synWa (synWa (.classMem (.cv y) D)
            (.classEq (synCdm (synCuni (synCwecutiso R D S E)))
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
          (.classMem (.cv u) E)) (.classEq (synCrn (synCuni (synCwecutiso R D S E)))
          (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))))
      (synWa (synWa (.classMem (.cv y) D)
          (.classEq (synCdm (synCuni (synCwecutiso R D S E)))
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
        (.classMem (.cv u) E))
      (.classMem (.cv u) E) p0115 p0121
  have p0123 :=
    @gJca
      (synWa (synWa (synWa (.classMem (.cv y) D)
            (.classEq (synCdm (synCuni (synCwecutiso R D S E)))
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
          (.classMem (.cv u) E)) (.classEq (synCrn (synCuni (synCwecutiso R D S E)))
          (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))))
      (.classMem (.cv y) D) (.classMem (.cv u) E) p0119 p0122
  have p0124 := @gStrictsegnel y D R
  have p0125 :=
    @gA1i
      (.neg (.classMem (.cv y)
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
      (synWa (synWa (synWa (.classMem (.cv y) D)
            (.classEq (synCdm (synCuni (synCwecutiso R D S E)))
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
          (.classMem (.cv u) E)) (.classEq (synCrn (synCuni (synCwecutiso R D S E)))
          (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))))
      p0124
  have p0130 :=
    @gSyl
      (synWa (synWa (synWa (.classMem (.cv y) D)
            (.classEq (synCdm (synCuni (synCwecutiso R D S E)))
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
          (.classMem (.cv u) E)) (.classEq (synCrn (synCuni (synCwecutiso R D S E)))
          (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))))
      (synWa (.classMem (.cv y) D) (.classEq (synCdm (synCuni (synCwecutiso R D S E)))
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
      (.classEq (synCdm (synCuni (synCwecutiso R D S E)))
        (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y)))))
      p0117 p0074
  have p0131 :=
    @gEleq2d
      (synWa (synWa (synWa (.classMem (.cv y) D)
            (.classEq (synCdm (synCuni (synCwecutiso R D S E)))
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
          (.classMem (.cv u) E)) (.classEq (synCrn (synCuni (synCwecutiso R D S E)))
          (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))))
      (synCdm (synCuni (synCwecutiso R D S E)))
      (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y)))) (.cv y)
      p0130
  have p0132 :=
    @gNotbid
      (synWa (synWa (synWa (.classMem (.cv y) D)
            (.classEq (synCdm (synCuni (synCwecutiso R D S E)))
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
          (.classMem (.cv u) E)) (.classEq (synCrn (synCuni (synCwecutiso R D S E)))
          (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))))
      (.classMem (.cv y) (synCdm (synCuni (synCwecutiso R D S E))))
      (.classMem (.cv y)
        (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y)))))
      p0131
  have p0133 :=
    @gMpbird
      (synWa (synWa (synWa (.classMem (.cv y) D)
            (.classEq (synCdm (synCuni (synCwecutiso R D S E)))
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
          (.classMem (.cv u) E)) (.classEq (synCrn (synCuni (synCwecutiso R D S E)))
          (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))))
      (.neg (.classMem (.cv y) (synCdm (synCuni (synCwecutiso R D S E)))))
      (.neg (.classMem (.cv y)
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
      p0125 p0132
  have p0134 :=
    @gA1i (synWbr R (synCwe) D)
      (synWa (synWa (synWa (.classMem (.cv y) D)
            (.classEq (synCdm (synCuni (synCwecutiso R D S E)))
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
          (.classMem (.cv u) E)) (.classEq (synCrn (synCuni (synCwecutiso R D S E)))
          (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))))
      hyp_wecomparisonterminalsetfdv_1
  have p0135 :=
    @gA1i (synWbr S (synCwe) E)
      (synWa (synWa (synWa (.classMem (.cv y) D)
            (.classEq (synCdm (synCuni (synCwecutiso R D S E)))
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
          (.classMem (.cv u) E)) (.classEq (synCrn (synCuni (synCwecutiso R D S E)))
          (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))))
      hyp_wecomparisonterminalsetfdv_2
  have p0136 :=
    @gJca
      (synWa (synWa (synWa (.classMem (.cv y) D)
            (.classEq (synCdm (synCuni (synCwecutiso R D S E)))
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
          (.classMem (.cv u) E)) (.classEq (synCrn (synCuni (synCwecutiso R D S E)))
          (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))))
      (synWbr R (synCwe) D) (synWbr S (synCwe) E) p0134 p0135
  have p0146 :=
    @gJca
      (synWa (synWa (synWa (.classMem (.cv y) D)
            (.classEq (synCdm (synCuni (synCwecutiso R D S E)))
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
          (.classMem (.cv u) E)) (.classEq (synCrn (synCuni (synCwecutiso R D S E)))
          (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))))
      (synWa (synWbr R (synCwe) D) (synWbr S (synCwe) E))
      (synWa (.classMem (.cv y) D) (.classMem (.cv u) E)) p0136 p0123
  have p0148 :=
    @gA1i
      (synWiso (synCuni (synCwecutiso R D S E)) R S
        (synCdm (synCuni (synCwecutiso R D S E)))
        (synCrn (synCuni (synCwecutiso R D S E))))
      (synWa (synWa (synWa (.classMem (.cv y) D)
            (.classEq (synCdm (synCuni (synCwecutiso R D S E)))
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
          (.classMem (.cv u) E)) (.classEq (synCrn (synCuni (synCwecutiso R D S E)))
          (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))))
      p0003
  have p0155 :=
    @gSyl
      (synWa (synWa (synWa (.classMem (.cv y) D)
            (.classEq (synCdm (synCuni (synCwecutiso R D S E)))
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
          (.classMem (.cv u) E)) (.classEq (synCrn (synCuni (synCwecutiso R D S E)))
          (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))))
      (.classEq (synCdm (synCuni (synCwecutiso R D S E)))
        (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y)))))
      (synWb (synWiso (synCuni (synCwecutiso R D S E)) R S
          (synCdm (synCuni (synCwecutiso R D S E)))
          (synCrn (synCuni (synCwecutiso R D S E))))
        (synWiso (synCuni (synCwecutiso R D S E)) R S
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
          (synCrn (synCuni (synCwecutiso R D S E)))))
      p0130 p0076
  have p0156 :=
    @gMpbid
      (synWa (synWa (synWa (.classMem (.cv y) D)
            (.classEq (synCdm (synCuni (synCwecutiso R D S E)))
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
          (.classMem (.cv u) E)) (.classEq (synCrn (synCuni (synCwecutiso R D S E)))
          (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))))
      (synWiso (synCuni (synCwecutiso R D S E)) R S
        (synCdm (synCuni (synCwecutiso R D S E)))
        (synCrn (synCuni (synCwecutiso R D S E))))
      (synWiso (synCuni (synCwecutiso R D S E)) R S
        (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
        (synCrn (synCuni (synCwecutiso R D S E))))
      p0148 p0155
  have p0157 :=
    @gSimpr
      (synWa (synWa (.classMem (.cv y) D)
          (.classEq (synCdm (synCuni (synCwecutiso R D S E)))
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
        (.classMem (.cv u) E))
      (.classEq (synCrn (synCuni (synCwecutiso R D S E)))
        (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u)))))
  have p0158 :=
    @gIsoeq5 (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
      (synCrn (synCuni (synCwecutiso R D S E)))
      (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u)))) R S
      (synCuni (synCwecutiso R D S E))
  have p0159 :=
    @gSyl
      (synWa (synWa (synWa (.classMem (.cv y) D)
            (.classEq (synCdm (synCuni (synCwecutiso R D S E)))
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
          (.classMem (.cv u) E)) (.classEq (synCrn (synCuni (synCwecutiso R D S E)))
          (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))))
      (.classEq (synCrn (synCuni (synCwecutiso R D S E)))
        (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u)))))
      (synWb (synWiso (synCuni (synCwecutiso R D S E)) R S
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
          (synCrn (synCuni (synCwecutiso R D S E))))
        (synWiso (synCuni (synCwecutiso R D S E)) R S
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
          (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))))
      p0157 p0158
  have p0160 :=
    @gMpbid
      (synWa (synWa (synWa (.classMem (.cv y) D)
            (.classEq (synCdm (synCuni (synCwecutiso R D S E)))
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
          (.classMem (.cv u) E)) (.classEq (synCrn (synCuni (synCwecutiso R D S E)))
          (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))))
      (synWiso (synCuni (synCwecutiso R D S E)) R S
        (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
        (synCrn (synCuni (synCwecutiso R D S E))))
      (synWiso (synCuni (synCwecutiso R D S E)) R S
        (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
        (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u)))))
      p0156 p0159
  have p0161 :=
    @gJca
      (synWa (synWa (synWa (.classMem (.cv y) D)
            (.classEq (synCdm (synCuni (synCwecutiso R D S E)))
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
          (.classMem (.cv u) E)) (.classEq (synCrn (synCuni (synCwecutiso R D S E)))
          (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))))
      (synWa (synWa (synWbr R (synCwe) D) (synWbr S (synCwe) E))
        (synWa (.classMem (.cv y) D) (.classMem (.cv u) E)))
      (synWiso (synCuni (synCwecutiso R D S E)) R S
        (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
        (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u)))))
      p0146 p0160
  have p0162 := @gWecutisoaddpairisondv y u D R S E (synCuni (synCwecutiso R D S E))
  have p0163 :=
    @gSyl
      (synWa (synWa (synWa (.classMem (.cv y) D)
            (.classEq (synCdm (synCuni (synCwecutiso R D S E)))
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
          (.classMem (.cv u) E)) (.classEq (synCrn (synCuni (synCwecutiso R D S E)))
          (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))))
      (synWa (synWa (synWa (synWbr R (synCwe) D) (synWbr S (synCwe) E))
          (synWa (.classMem (.cv y) D) (.classMem (.cv u) E)))
        (synWiso (synCuni (synCwecutiso R D S E)) R S
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
          (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))))
      (synWiso
        (synCun (synCuni (synCwecutiso R D S E)) (synCsn (synCop (.cv y) (.cv u)))) R S
        (synCun (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
          (synCsn (.cv y))) (synCun
          (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
          (synCsn (.cv u))))
      p0161 p0162
  have p0164 :=
    @gJca
      (synWa (synWa (synWa (.classMem (.cv y) D)
            (.classEq (synCdm (synCuni (synCwecutiso R D S E)))
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
          (.classMem (.cv u) E)) (.classEq (synCrn (synCuni (synCwecutiso R D S E)))
          (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))))
      (.neg (.classMem (.cv y) (synCdm (synCuni (synCwecutiso R D S E)))))
      (synWiso
        (synCun (synCuni (synCwecutiso R D S E)) (synCsn (synCop (.cv y) (.cv u)))) R S
        (synCun (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
          (synCsn (.cv y))) (synCun
          (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
          (synCsn (.cv u))))
      p0133 p0163
  have p0165 :=
    @gJca
      (synWa (synWa (synWa (.classMem (.cv y) D)
            (.classEq (synCdm (synCuni (synCwecutiso R D S E)))
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
          (.classMem (.cv u) E)) (.classEq (synCrn (synCuni (synCwecutiso R D S E)))
          (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))))
      (synWa (.classMem (.cv y) D) (.classMem (.cv u) E))
      (synWa (.neg (.classMem (.cv y) (synCdm (synCuni (synCwecutiso R D S E))))) (synWiso
          (synCun (synCuni (synCwecutiso R D S E)) (synCsn (synCop (.cv y) (.cv u)))) R S
          (synCun (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
            (synCsn (.cv y))) (synCun
            (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
            (synCsn (.cv u)))))
      p0123 p0164
  have p0166 :=
    @gWecutisoextendedterminaldfdv x y u D R S h E dv_cache_0024 dv_cache_0005
      dv_cache_0022 dv_cache_0001 dv_cache_0025 dv_cache_0006 dv_cache_0014 dv_cache_0002
      dv_cache_0026 dv_cache_0007 dv_cache_0027 dv_cache_0003 dv_cache_0028 dv_cache_0008
      dv_cache_0029 dv_cache_0004 dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033
      dv_cache_0034 dv_cache_0035 hyp_wecomparisonterminalsetfdv_1
      hyp_wecomparisonterminalsetfdv_2 hyp_wecomparisonterminalsetfdv_3
  have p0167 :=
    @gSyl
      (synWa (synWa (synWa (.classMem (.cv y) D)
            (.classEq (synCdm (synCuni (synCwecutiso R D S E)))
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
          (.classMem (.cv u) E)) (.classEq (synCrn (synCuni (synCwecutiso R D S E)))
          (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))))
      (synWa (synWa (.classMem (.cv y) D) (.classMem (.cv u) E))
        (synWa (.neg (.classMem (.cv y) (synCdm (synCuni (synCwecutiso R D S E)))))
          (synWiso (synCun (synCuni (synCwecutiso R D S E))
              (synCsn (synCop (.cv y) (.cv u)))) R S (synCun
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
              (synCsn (.cv y))) (synCun
              (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
              (synCsn (.cv u))))))
      (synW3o (synWex h (synWiso (.cv h) R S D E)) (synWrex x E (synWex h
            (synWiso (.cv h) R (synCin S (synCxp (synCin E
                    (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv x)))) (synCin E
                    (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv x)))))) D
              (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv x)))))))
        (synWrex x D (synWex h (synWiso (.cv h) S (synCin R (synCxp (synCin D
                    (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))) (synCin D
                    (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))))) E
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))))
      p0165 p0166
  have p0168 :=
    @gEx
      (synWa (synWa (.classMem (.cv y) D)
          (.classEq (synCdm (synCuni (synCwecutiso R D S E)))
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
        (.classMem (.cv u) E))
      (.classEq (synCrn (synCuni (synCwecutiso R D S E)))
        (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u)))))
      (synW3o (synWex h (synWiso (.cv h) R S D E)) (synWrex x E (synWex h
            (synWiso (.cv h) R (synCin S (synCxp (synCin E
                    (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv x)))) (synCin E
                    (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv x)))))) D
              (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv x)))))))
        (synWrex x D (synWex h (synWiso (.cv h) S (synCin R (synCxp (synCin D
                    (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))) (synCin D
                    (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))))) E
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))))
      p0167
  have p0169 :=
    @gRexlimdva
      (synWa (.classMem (.cv y) D) (.classEq (synCdm (synCuni (synCwecutiso R D S E)))
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
      (.classEq (synCrn (synCuni (synCwecutiso R D S E)))
        (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u)))))
      (synW3o (synWex h (synWiso (.cv h) R S D E)) (synWrex x E (synWex h
            (synWiso (.cv h) R (synCin S (synCxp (synCin E
                    (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv x)))) (synCin E
                    (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv x)))))) D
              (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv x)))))))
        (synWrex x D (synWex h (synWiso (.cv h) S (synCin R (synCxp (synCin D
                    (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))) (synCin D
                    (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))))) E
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))))
      u E dv_cache_0016 dv_cache_0036 p0168
  have p0170 :=
    @gJaod
      (synWa (.classMem (.cv y) D) (.classEq (synCdm (synCuni (synCwecutiso R D S E)))
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
      (.classEq (synCrn (synCuni (synCwecutiso R D S E))) E)
      (synW3o (synWex h (synWiso (.cv h) R S D E)) (synWrex x E (synWex h
            (synWiso (.cv h) R (synCin S (synCxp (synCin E
                    (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv x)))) (synCin E
                    (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv x)))))) D
              (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv x)))))))
        (synWrex x D (synWex h (synWiso (.cv h) S (synCin R (synCxp (synCin D
                    (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))) (synCin D
                    (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))))) E
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))))
      (synWrex u E (.classEq (synCrn (synCuni (synCwecutiso R D S E)))
          (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))))
      p0114 p0169
  have p0171 :=
    @gMpd
      (synWa (.classMem (.cv y) D) (.classEq (synCdm (synCuni (synCwecutiso R D S E)))
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
      (synWo (.classEq (synCrn (synCuni (synCwecutiso R D S E))) E) (synWrex u E
          (.classEq (synCrn (synCuni (synCwecutiso R D S E)))
            (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u)))))))
      (synW3o (synWex h (synWiso (.cv h) R S D E)) (synWrex x E (synWex h
            (synWiso (.cv h) R (synCin S (synCxp (synCin E
                    (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv x)))) (synCin E
                    (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv x)))))) D
              (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv x)))))))
        (synWrex x D (synWex h (synWiso (.cv h) S (synCin R (synCxp (synCin D
                    (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))) (synCin D
                    (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))))) E
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))))
      p0067 p0170
  have p0172 :=
    @gEx (.classMem (.cv y) D)
      (.classEq (synCdm (synCuni (synCwecutiso R D S E)))
        (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y)))))
      (synW3o (synWex h (synWiso (.cv h) R S D E)) (synWrex x E (synWex h
            (synWiso (.cv h) R (synCin S (synCxp (synCin E
                    (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv x)))) (synCin E
                    (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv x)))))) D
              (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv x)))))))
        (synWrex x D (synWex h (synWiso (.cv h) S (synCin R (synCxp (synCin D
                    (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))) (synCin D
                    (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))))) E
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))))
      p0171
  have p0173 :=
    @gRexlimiv
      (.classEq (synCdm (synCuni (synCwecutiso R D S E)))
        (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y)))))
      (synW3o (synWex h (synWiso (.cv h) R S D E)) (synWrex x E (synWex h
            (synWiso (.cv h) R (synCin S (synCxp (synCin E
                    (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv x)))) (synCin E
                    (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv x)))))) D
              (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv x)))))))
        (synWrex x D (synWex h (synWiso (.cv h) S (synCin R (synCxp (synCin D
                    (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))) (synCin D
                    (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))))) E
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))))
      y D dv_cache_0037 p0172
  have p0174 :=
    @gJaoi (.classEq (synCdm (synCuni (synCwecutiso R D S E))) D)
      (synW3o (synWex h (synWiso (.cv h) R S D E)) (synWrex x E (synWex h
            (synWiso (.cv h) R (synCin S (synCxp (synCin E
                    (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv x)))) (synCin E
                    (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv x)))))) D
              (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv x)))))))
        (synWrex x D (synWex h (synWiso (.cv h) S (synCin R (synCxp (synCin D
                    (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))) (synCin D
                    (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))))) E
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))))
      (synWrex y D (.classEq (synCdm (synCuni (synCwecutiso R D S E)))
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
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

/-- Checked nominal proof certificate identified upstream as `g_wecomparisonterminalfdv`. -/
@[expose]
noncomputable def gWecomparisonterminalfdv (x : Var) (D : Class) (R : Class) (S : Class)
    (h : Var) (E : Class) (dv_D_h : h ∉ D.fv) (dv_D_x : x ∉ D.fv) (dv_E_h : h ∉ E.fv)
    (dv_E_x : x ∉ E.fv) (dv_R_h : h ∉ R.fv) (dv_R_x : x ∉ R.fv) (dv_S_h : h ∉ S.fv)
    (dv_S_x : x ∉ S.fv) (dv_h_x : h ≠ x)
    (hyp_wecomparisonterminalfdv_1 : Nominal.NPrf (synWbr R (synCwe) D))
    (hyp_wecomparisonterminalfdv_2 : Nominal.NPrf (synWbr S (synCwe) E)) :
    Nominal.NPrf
      (synW3o (synWex h (synWiso (.cv h) R S D E)) (synWrex x E (synWex h
            (synWiso (.cv h) R (synCin S (synCxp (synCin E
                    (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv x)))) (synCin E
                    (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv x)))))) D
              (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv x)))))))
        (synWrex x D (synWex h (synWiso (.cv h) S (synCin R (synCxp (synCin D
                    (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))) (synCin D
                    (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))))) E
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))))))) :=
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
    @gWecutisouniex D R S E hyp_wecomparisonterminalfdv_1 hyp_wecomparisonterminalfdv_2
  have p0001 :=
    @gWecomparisonterminalsetfdv x D R S h E dv_cache_0001 dv_cache_0002 dv_cache_0003
      dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009
      hyp_wecomparisonterminalfdv_1 hyp_wecomparisonterminalfdv_2 p0000
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_weisoexnceqclfdv`. -/
@[expose]
noncomputable def gWeisoexnceqclfdv (A : Class) (B : Class) (T : Class) (U : Class)
    (h : Var) (dv_A_h : h ∉ A.fv) (dv_B_h : h ∉ B.fv) :
    Nominal.NPrf
      (.imp (synWex h (synWiso (.cv h) T U A B)) (.classEq (synCnc A) (synCnc B))) :=
  by
  have dv_cache_0001 : h ∉ ((Wff.classEq (synCnc A) (synCnc B))).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : h ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnc, Finset.mem_union, dv_A_h,
          dv_B_h, or_false, not_false_eq_true])
  have p0000 := @gIsof1o A B T U (.cv h)
  have p0001 := @gVex h
  have p0002 := @gF1oen A B (.cv h) p0001
  have p0003 :=
    @gSyl (synWiso (.cv h) T U A B) (synWf1o (.cv h) A B) (synWbr A (synCen) B) p0000
      p0002
  have p0008 := @gBreldm A B (synCen)
  have p0009 :=
    @gSyl (synWiso (.cv h) T U A B) (synWbr A (synCen) B)
      (.classMem A (synCdm (synCen))) p0003 p0008
  have p0010 := @gDmen
  have p0011 := @gEleq2i (synCdm (synCen)) (synCvv) A p0010
  have p0012 := @gBiimpi (.classMem A (synCdm (synCen))) (.classMem A (synCvv)) p0011
  have p0013 :=
    @gSyl (synWiso (.cv h) T U A B) (.classMem A (synCdm (synCen)))
      (.classMem A (synCvv)) p0009 p0012
  have p0014 := @gEqncg A B (synCvv)
  have p0015 :=
    @gSyl (synWiso (.cv h) T U A B) (.classMem A (synCvv))
      (synWb (.classEq (synCnc A) (synCnc B)) (synWbr A (synCen) B)) p0013 p0014
  have p0016 :=
    @gMpbird (synWiso (.cv h) T U A B) (.classEq (synCnc A) (synCnc B))
      (synWbr A (synCen) B) p0003 p0015
  have p0017 :=
    @gExlimiv (synWiso (.cv h) T U A B) (.classEq (synCnc A) (synCnc B)) h
      dv_cache_0001 p0016
  exact p0017

/-- Checked nominal proof certificate identified upstream as `g_wecomparisonforwardnclecclfdv`. -/
@[expose]
noncomputable def gWecomparisonforwardnclecclfdv (x : Var) (D : Class) (R : Class)
    (S : Class) (h : Var) (E : Class) (dv_D_h : h ∉ D.fv) (dv_D_x : x ∉ D.fv)
    (dv_E_h : h ∉ E.fv) (dv_E_x : x ∉ E.fv) (_dv_R_h : h ∉ R.fv) (_dv_R_x : x ∉ R.fv)
    (dv_S_h : h ∉ S.fv) (_dv_S_x : x ∉ S.fv) (dv_h_x : h ≠ x)
    (hyp_wecomparisonforwardnclecclfdv_1 : Nominal.NPrf (synWbr S (synCwe) E)) :
    Nominal.NPrf
      (.imp (synWo (synWex h (synWiso (.cv h) R S D E)) (synWrex x E (synWex h
              (synWiso (.cv h) R (synCin S (synCxp (synCin E
                      (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv x)))) (synCin E
                      (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv x)))))) D
                (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv x))))))))
        (synWbr (synCnc D) (synClec) (synCnc E))) :=
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
    h ∉ ((synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv x))))).fv :=
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
  have dv_cache_0004 : x ∉ ((synWbr (synCnc D) (synClec) (synCnc E))).fv :=
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
  have p0000 := @gBrex S E (synCwe)
  have p0001 := Nominal.mp hyp_wecomparisonforwardnclecclfdv_1 p0000
  have p0002 := @gSimpri (.classMem S (synCvv)) (.classMem E (synCvv)) p0001
  have p0003 := @gNcelncsi E p0002
  have p0004 := @gNclecid (synCnc E)
  have p0005 := Nominal.mp p0003 p0004
  have p0006 := @gWeisoexnceqclfdv D E R S h dv_cache_0001 dv_cache_0002
  have p0007 :=
    @gBreq1d (synWex h (synWiso (.cv h) R S D E)) (synCnc D) (synCnc E) (synCnc E)
      (synClec) p0006
  have p0008 :=
    @gMpbiri (synWex h (synWiso (.cv h) R S D E))
      (synWbr (synCnc D) (synClec) (synCnc E))
      (synWbr (synCnc E) (synClec) (synCnc E)) p0005 p0007
  have p0009 := @gInss1 E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv x)))
  have p0015 := @gSimpli (.classMem S (synCvv)) (.classMem E (synCvv)) p0001
  have p0016 := @gIdex
  have p0017 := @gDifex S (synCid) p0015 p0016
  have p0018 := @gCnvex (synCdif S (synCid)) p0017
  have p0019 := @gSnex (.cv x)
  have p0020 := @gImaex (synCcnv (synCdif S (synCid))) (synCsn (.cv x)) p0018 p0019
  have p0021 :=
    @gInex E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv x))) p0002 p0020
  have p0025 :=
    @gNclec (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv x)))) E
      p0021 p0002
  have p0026 := Nominal.mp p0009 p0025
  have p0027 :=
    @gWeisoexnceqclfdv D
      (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv x)))) R
      (synCin S (synCxp
          (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv x))))
          (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv x))))))
      h dv_cache_0001 dv_cache_0003
  have p0028 :=
    @gBreq1d
      (synWex h (synWiso (.cv h) R (synCin S (synCxp
              (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv x))))
              (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv x))))))
          D (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv x))))))
      (synCnc D)
      (synCnc (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv x)))))
      (synCnc E) (synClec) p0027
  have p0029 :=
    @gMpbiri
      (synWex h (synWiso (.cv h) R (synCin S (synCxp
              (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv x))))
              (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv x))))))
          D (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv x))))))
      (synWbr (synCnc D) (synClec) (synCnc E))
      (synWbr (synCnc
          (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv x)))))
        (synClec) (synCnc E))
      p0026 p0028
  have p0030 :=
    @gRexlimivw
      (synWex h (synWiso (.cv h) R (synCin S (synCxp
              (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv x))))
              (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv x))))))
          D (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv x))))))
      (synWbr (synCnc D) (synClec) (synCnc E)) x E dv_cache_0004 p0029
  have p0031 :=
    @gJaoi (synWex h (synWiso (.cv h) R S D E))
      (synWbr (synCnc D) (synClec) (synCnc E))
      (synWrex x E (synWex h (synWiso (.cv h) R (synCin S (synCxp
                (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv x))))
                (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv x)))))) D
            (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv x)))))))
      p0008 p0030
  exact p0031

/-- Checked nominal proof certificate identified upstream as `g_wecomparisonreversecutrepfdv`. -/
@[expose]
noncomputable def gWecomparisonreversecutrepfdv (x : Var) (D : Class) (R : Class)
    (S : Class) (h : Var) (E : Class) (dv_D_h : h ∉ D.fv) (_dv_D_x : x ∉ D.fv)
    (dv_E_h : h ∉ E.fv) (_dv_E_x : x ∉ E.fv) (dv_R_h : h ∉ R.fv) (_dv_R_x : x ∉ R.fv)
    (dv_h_x : h ≠ x) :
    Nominal.NPrf
      (.imp (synWrex x D (synWex h (synWiso (.cv h) S (synCin R (synCxp (synCin D
                    (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))) (synCin D
                    (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))))) E
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))))))
        (synWrex x D (.classEq (synCnc E) (synCnc (synCin D
                (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))))))) :=
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
    h ∉ ((synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))).fv :=
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
    @gWeisoexnceqclfdv E
      (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))) S
      (synCin R (synCxp
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))
      h dv_cache_0001 dv_cache_0002
  have p0001 :=
    @gReximi
      (synWex h (synWiso (.cv h) S (synCin R (synCxp
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))
          E (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))
      (.classEq (synCnc E) (synCnc
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))
      x D p0000
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_wecomparisoncutrepltfdv`. -/
@[expose]
noncomputable def gWecomparisoncutrepltfdv (x : Var) (D : Class) (R : Class) (S : Class)
    (E : Class) (dv_D_x : x ∉ D.fv) (dv_E_x : x ∉ E.fv) (dv_R_x : x ∉ R.fv)
    (dv_S_x : x ∉ S.fv)
    (hyp_wecomparisoncutrepltfdv_1 : Nominal.NPrf (synWbr R (synCwe) D))
    (hyp_wecomparisoncutrepltfdv_2 : Nominal.NPrf (synWbr S (synCwe) E))
    (hyp_wecomparisoncutrepltfdv_3 :
      Nominal.NPrf (synWbr (synCnc E) (synCltc) (synCnc D))) :
    Nominal.NPrf
      (synWrex x D (.classEq (synCnc E) (synCnc (synCin D
              (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))) :=
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
    @gWecomparisonterminalfdv x D R S h E dv_cache_0001 dv_cache_0002 dv_cache_0003
      dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009
      hyp_wecomparisoncutrepltfdv_1 hyp_wecomparisoncutrepltfdv_2
  have p0001 :=
    @gOrc (synWex h (synWiso (.cv h) R S D E))
      (synWrex x E (synWex h (synWiso (.cv h) R (synCin S (synCxp
                (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv x))))
                (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv x)))))) D
            (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv x)))))))
  have p0002 :=
    @gWecomparisonforwardnclecclfdv x D R S h E dv_cache_0001 dv_cache_0002 dv_cache_0003
      dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009
      hyp_wecomparisoncutrepltfdv_2
  have p0003 := @gBrex S E (synCwe)
  have p0004 := Nominal.mp hyp_wecomparisoncutrepltfdv_2 p0003
  have p0005 := @gSimpri (.classMem S (synCvv)) (.classMem E (synCvv)) p0004
  have p0006 := @gNcelncsi E p0005
  have p0007 := @gBrex R D (synCwe)
  have p0008 := Nominal.mp hyp_wecomparisoncutrepltfdv_1 p0007
  have p0009 := @gSimpri (.classMem R (synCvv)) (.classMem D (synCvv)) p0008
  have p0010 := @gNcelncsi D p0009
  have p0011 :=
    @gPm32i (.classMem (synCnc E) (synCncs)) (.classMem (synCnc D) (synCncs)) p0006
      p0010
  have p0012 := @gLtlenlec (synCnc E) (synCnc D)
  have p0013 := Nominal.mp p0011 p0012
  have p0014 :=
    @gBiimpi (synWbr (synCnc E) (synCltc) (synCnc D))
      (synWa (synWbr (synCnc E) (synClec) (synCnc D))
        (.neg (synWbr (synCnc D) (synClec) (synCnc E))))
      p0013
  have p0015 := Nominal.mp hyp_wecomparisoncutrepltfdv_3 p0014
  have p0016 :=
    @gSimpri (synWbr (synCnc E) (synClec) (synCnc D))
      (.neg (synWbr (synCnc D) (synClec) (synCnc E))) p0015
  have p0017 :=
    @gPm221 (synWbr (synCnc D) (synClec) (synCnc E))
      (synWrex x D (.classEq (synCnc E) (synCnc
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))))))
  have p0018 := Nominal.mp p0016 p0017
  have p0019 :=
    @gSyl
      (synWo (synWex h (synWiso (.cv h) R S D E)) (synWrex x E (synWex h
            (synWiso (.cv h) R (synCin S (synCxp (synCin E
                    (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv x)))) (synCin E
                    (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv x)))))) D
              (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv x))))))))
      (synWbr (synCnc D) (synClec) (synCnc E))
      (synWrex x D (.classEq (synCnc E) (synCnc
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))))))
      p0002 p0018
  have p0020 :=
    @gSyl (synWex h (synWiso (.cv h) R S D E))
      (synWo (synWex h (synWiso (.cv h) R S D E)) (synWrex x E (synWex h
            (synWiso (.cv h) R (synCin S (synCxp (synCin E
                    (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv x)))) (synCin E
                    (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv x)))))) D
              (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv x))))))))
      (synWrex x D (.classEq (synCnc E) (synCnc
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))))))
      p0001 p0019
  have p0021 :=
    @gOlc
      (synWrex x E (synWex h (synWiso (.cv h) R (synCin S (synCxp
                (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv x))))
                (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv x)))))) D
            (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv x)))))))
      (synWex h (synWiso (.cv h) R S D E))
  have p0040 :=
    @gSyl
      (synWrex x E (synWex h (synWiso (.cv h) R (synCin S (synCxp
                (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv x))))
                (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv x)))))) D
            (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv x)))))))
      (synWo (synWex h (synWiso (.cv h) R S D E)) (synWrex x E (synWex h
            (synWiso (.cv h) R (synCin S (synCxp (synCin E
                    (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv x)))) (synCin E
                    (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv x)))))) D
              (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv x))))))))
      (synWrex x D (.classEq (synCnc E) (synCnc
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))))))
      p0021 p0019
  have p0041 :=
    @gWecomparisonreversecutrepfdv x D R S h E dv_cache_0001 dv_cache_0002 dv_cache_0003
      dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0009
  have p0042 :=
    @gN3jaoi (synWex h (synWiso (.cv h) R S D E))
      (synWrex x D (.classEq (synCnc E) (synCnc
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))))))
      (synWrex x E (synWex h (synWiso (.cv h) R (synCin S (synCxp
                (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv x))))
                (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv x)))))) D
            (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv x)))))))
      (synWrex x D (synWex h (synWiso (.cv h) S (synCin R (synCxp
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))))) E
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))))))
      p0020 p0040 p0041
  have p0043 := Nominal.mp p0000 p0042
  exact p0043


end NFChoice.DirectNominalPrf.WPPReplay

end
