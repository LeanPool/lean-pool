/-
Copyright (c) 2026 Elliot Glazer and NFNotWPP contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elliot Glazer and NFNotWPP contributors
-/

module

public import LeanPool.NFWeakPartition.Certificates.NominalWPPReplayChunk016Compact001Block001

/-! Nominal proof certificates grouped in dependency order. -/


public section

/-! Certificates from `NominalWPPReplayChunk016Compact001Part004`. -/


section

namespace NFChoice.DirectNominalPrf.WPPReplay

open scoped Fol
open NFChoice.Foundation
open NFChoice.SemanticCore
open NFChoice.ReplaySupport
open NFChoice.Compiler.CompactSourceSyntax

/-- Checked nominal proof certificate identified upstream as `g_wecutisofamilychainndv`. -/
@[expose]
noncomputable def gWecutisofamilychainndv (D : Class) (R : Class) (S : Class) (f : Var)
    (g : Var) (E : Class)
    (hyp_wecutisofamilychainndv_1 : Nominal.NPrf (synWbr R (synCwe) D))
    (hyp_wecutisofamilychainndv_2 : Nominal.NPrf (synWbr S (synCwe) E)) :
    Nominal.NPrf
      (.imp (synWa (.classMem (.cv f) (synCwecutiso R D S E))
          (.classMem (.cv g) (synCwecutiso R D S E)))
        (synWo (synWss (.cv f) (.cv g)) (synWss (.cv g) (.cv f)))) :=
  by
  let proofSupport : Finset Var :=
    D.fv ∪ R.fv ∪ S.fv ∪ ({ f } : Finset Var) ∪ ({ g } : Finset Var) ∪ E.fv
  let x : Var := freshVar proofSupport 0
  let u : Var := freshVar proofSupport 1
  let y : Var := freshVar proofSupport 2
  let v : Var := freshVar proofSupport 3
  have fresh_x : x ∉ proofSupport :=
    by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_x_not_D : x ∉ D.fv := by
    intro h
    exact
      fresh_x
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _
              (Finset.mem_union_left _ (Finset.mem_union_left _ (h))))))
  have fresh_x_not_R : x ∉ R.fv := by
    intro h
    exact
      fresh_x
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _
              (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))))
  have fresh_x_not_S : x ∉ S.fv := by
    intro h
    exact
      fresh_x
        (Finset.mem_union_left _ (Finset.mem_union_left _
            (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))))
  have fresh_x_ne_f : x ≠ f := by
    intro h
    exact
      fresh_x
        (Finset.mem_union_left _ (Finset.mem_union_left _
            (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))))
  have fresh_f_ne_x : f ≠ x := Ne.symm fresh_x_ne_f
  have fresh_x_ne_g : x ≠ g := by
    intro h
    exact
      fresh_x
        (Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_singleton.mpr h)))
  have fresh_x_not_E : x ∉ E.fv := by
    intro h
    exact fresh_x (Finset.mem_union_right _ (h))
  have fresh_u : u ∉ proofSupport :=
    by
    change freshVar proofSupport 1 ∉ proofSupport
    exact freshVar_not_mem proofSupport 1
  have fresh_u_not_D : u ∉ D.fv := by
    intro h
    exact
      fresh_u
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _
              (Finset.mem_union_left _ (Finset.mem_union_left _ (h))))))
  have fresh_u_not_R : u ∉ R.fv := by
    intro h
    exact
      fresh_u
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _
              (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))))
  have fresh_u_not_S : u ∉ S.fv := by
    intro h
    exact
      fresh_u
        (Finset.mem_union_left _ (Finset.mem_union_left _
            (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))))
  have fresh_u_ne_f : u ≠ f := by
    intro h
    exact
      fresh_u
        (Finset.mem_union_left _ (Finset.mem_union_left _
            (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))))
  have fresh_f_ne_u : f ≠ u := Ne.symm fresh_u_ne_f
  have fresh_u_ne_g : u ≠ g := by
    intro h
    exact
      fresh_u
        (Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_singleton.mpr h)))
  have fresh_u_not_E : u ∉ E.fv := by
    intro h
    exact fresh_u (Finset.mem_union_right _ (h))
  have fresh_y : y ∉ proofSupport :=
    by
    change freshVar proofSupport 2 ∉ proofSupport
    exact freshVar_not_mem proofSupport 2
  have fresh_y_not_D : y ∉ D.fv := by
    intro h
    exact
      fresh_y
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _
              (Finset.mem_union_left _ (Finset.mem_union_left _ (h))))))
  have fresh_y_not_R : y ∉ R.fv := by
    intro h
    exact
      fresh_y
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _
              (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))))
  have fresh_y_not_S : y ∉ S.fv := by
    intro h
    exact
      fresh_y
        (Finset.mem_union_left _ (Finset.mem_union_left _
            (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))))
  have fresh_y_ne_f : y ≠ f := by
    intro h
    exact
      fresh_y
        (Finset.mem_union_left _ (Finset.mem_union_left _
            (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))))
  have fresh_y_ne_g : y ≠ g := by
    intro h
    exact
      fresh_y
        (Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_singleton.mpr h)))
  have fresh_g_ne_y : g ≠ y := Ne.symm fresh_y_ne_g
  have fresh_y_not_E : y ∉ E.fv := by
    intro h
    exact fresh_y (Finset.mem_union_right _ (h))
  have fresh_v : v ∉ proofSupport :=
    by
    change freshVar proofSupport 3 ∉ proofSupport
    exact freshVar_not_mem proofSupport 3
  have fresh_v_not_D : v ∉ D.fv := by
    intro h
    exact
      fresh_v
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _
              (Finset.mem_union_left _ (Finset.mem_union_left _ (h))))))
  have fresh_v_not_R : v ∉ R.fv := by
    intro h
    exact
      fresh_v
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _
              (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))))
  have fresh_v_not_S : v ∉ S.fv := by
    intro h
    exact
      fresh_v
        (Finset.mem_union_left _ (Finset.mem_union_left _
            (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))))
  have fresh_v_ne_f : v ≠ f := by
    intro h
    exact
      fresh_v
        (Finset.mem_union_left _ (Finset.mem_union_left _
            (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))))
  have fresh_v_ne_g : v ≠ g := by
    intro h
    exact
      fresh_v
        (Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_singleton.mpr h)))
  have fresh_g_ne_v : g ≠ v := Ne.symm fresh_v_ne_g
  have fresh_v_not_E : v ∉ E.fv := by
    intro h
    exact fresh_v (Finset.mem_union_right _ (h))
  have fresh_x_ne_u : x ≠ u :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have fresh_u_ne_x : u ≠ x := Ne.symm fresh_x_ne_u
  have fresh_x_ne_y : x ≠ y :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 2
    exact freshVar_injective proofSupport (i := 0) (j := 2) (by decide)
  have fresh_y_ne_x : y ≠ x := Ne.symm fresh_x_ne_y
  have fresh_x_ne_v : x ≠ v :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 3
    exact freshVar_injective proofSupport (i := 0) (j := 3) (by decide)
  have fresh_v_ne_x : v ≠ x := Ne.symm fresh_x_ne_v
  have fresh_u_ne_y : u ≠ y :=
    by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 2
    exact freshVar_injective proofSupport (i := 1) (j := 2) (by decide)
  have fresh_y_ne_u : y ≠ u := Ne.symm fresh_u_ne_y
  have fresh_u_ne_v : u ≠ v :=
    by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 3
    exact freshVar_injective proofSupport (i := 1) (j := 3) (by decide)
  have fresh_v_ne_u : v ≠ u := Ne.symm fresh_u_ne_v
  have fresh_y_ne_v : y ≠ v :=
    by
    change freshVar proofSupport 2 ≠ freshVar proofSupport 3
    exact freshVar_injective proofSupport (i := 2) (j := 3) (by decide)
  have fresh_v_ne_y : v ≠ y := Ne.symm fresh_y_ne_v
  have dv_cache_0001 : u ∉ (D).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : u ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_u_not_D, not_false_eq_true])
  have dv_cache_0002 : x ∉ (D).fv :=
    by
    clear dv_cache_0001
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_x_not_D, not_false_eq_true])
  have dv_cache_0003 : u ∉ (E).fv :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact
      (by
        have compact_fv_not_mem_empty : u ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_u_not_E, not_false_eq_true])
  have dv_cache_0004 : x ∉ (E).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_x_not_E, not_false_eq_true])
  have dv_cache_0005 : u ∉ (R).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact
      (by
        have compact_fv_not_mem_empty : u ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_u_not_R, not_false_eq_true])
  have dv_cache_0006 : x ∉ (R).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_x_not_R, not_false_eq_true])
  have dv_cache_0007 : u ∉ (S).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006
    exact
      (by
        have compact_fv_not_mem_empty : u ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_u_not_S, not_false_eq_true])
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
        simp only [fresh_x_not_S, not_false_eq_true])
  have dv_cache_0009 : f ≠ u :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008
    exact (show f ≠ u from (by exact fresh_f_ne_u))
  have dv_cache_0010 : f ≠ x :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009
    exact (show f ≠ x from (by exact fresh_f_ne_x))
  have dv_cache_0011 : u ≠ x :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010
    exact (show u ≠ x from (by exact fresh_u_ne_x))
  have dv_cache_0012 : v ∉ (D).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
    exact
      (by
        have compact_fv_not_mem_empty : v ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_v_not_D, not_false_eq_true])
  have dv_cache_0013 : y ∉ (D).fv :=
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
        simp only [fresh_y_not_D, not_false_eq_true])
  have dv_cache_0014 : v ∉ (E).fv :=
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
        simp only [fresh_v_not_E, not_false_eq_true])
  have dv_cache_0015 : y ∉ (E).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_y_not_E, not_false_eq_true])
  have dv_cache_0016 : v ∉ (R).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015
    exact
      (by
        have compact_fv_not_mem_empty : v ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_v_not_R, not_false_eq_true])
  have dv_cache_0017 : y ∉ (R).fv :=
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
        simp only [fresh_y_not_R, not_false_eq_true])
  have dv_cache_0018 : v ∉ (S).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
    exact
      (by
        have compact_fv_not_mem_empty : v ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_v_not_S, not_false_eq_true])
  have dv_cache_0019 : y ∉ (S).fv :=
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
        simp only [fresh_y_not_S, not_false_eq_true])
  have dv_cache_0020 : g ≠ v :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019
    exact (show g ≠ v from (by exact fresh_g_ne_v))
  have dv_cache_0021 : g ≠ y :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020
    exact (show g ≠ y from (by exact fresh_g_ne_y))
  have dv_cache_0022 : v ≠ y :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021
    exact (show v ≠ y from (by exact fresh_v_ne_y))
  have dv_cache_0023 :
    y ∉ ((synWo (synWss (.cv f) (.cv g)) (synWss (.cv g) (.cv f)))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wo,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wss,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, fresh_y_ne_f, fresh_y_ne_g, or_false, not_false_eq_true])
  have dv_cache_0024 :
    v ∉ ((synWo (synWss (.cv f) (.cv g)) (synWss (.cv g) (.cv f)))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
    exact
      (by
        have compact_fv_not_mem_empty : v ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wo,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wss,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, fresh_v_ne_f, fresh_v_ne_g, or_false, not_false_eq_true])
  have dv_cache_0025 :
    y ∉
      ((synWa (synWa (.classMem (.cv x) D) (.classMem (.cv u) E)) (synWiso (.cv f) (synCin R
              (synCxp
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))
            (synCin S (synCxp
                (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
                (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))))
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
            (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_wiso,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxp,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cima,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdif,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cid,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, Finset.mem_union,
          Finset.mem_singleton, fresh_y_ne_x, fresh_y_not_D, fresh_y_ne_u, fresh_y_not_E,
          fresh_y_not_R, fresh_y_not_S, fresh_y_ne_f, compact_fv_not_mem_empty, or_false,
          not_false_eq_true])
  have dv_cache_0026 :
    v ∉
      ((synWa (synWa (.classMem (.cv x) D) (.classMem (.cv u) E)) (synWiso (.cv f) (synCin R
              (synCxp
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))
            (synCin S (synCxp
                (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
                (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))))
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
            (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025
    exact
      (by
        have compact_fv_not_mem_empty : v ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_wiso,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxp,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cima,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdif,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cid,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, Finset.mem_union,
          Finset.mem_singleton, fresh_v_ne_x, fresh_v_not_D, fresh_v_ne_u, fresh_v_not_E,
          fresh_v_not_R, fresh_v_not_S, fresh_v_ne_f, compact_fv_not_mem_empty, or_false,
          not_false_eq_true])
  have dv_cache_0027 : y ≠ v :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026
    exact (show y ≠ v from (by exact fresh_y_ne_v))
  have dv_cache_0028 :
    x ∉
      ((Wff.imp (.classMem (.cv g) (synCwecutiso R D S E))
          (synWo (synWss (.cv f) (.cv g)) (synWss (.cv g) (.cv f))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwecutiso,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wo,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wss, Finset.mem_union,
          Finset.mem_singleton, fresh_x_ne_g, fresh_x_not_D, fresh_x_not_E, fresh_x_not_R,
          fresh_x_not_S, fresh_x_ne_f, or_false, not_false_eq_true])
  have dv_cache_0029 :
    u ∉
      ((Wff.imp (.classMem (.cv g) (synCwecutiso R D S E))
          (synWo (synWss (.cv f) (.cv g)) (synWss (.cv g) (.cv f))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028
    exact
      (by
        have compact_fv_not_mem_empty : u ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwecutiso,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wo,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wss, Finset.mem_union,
          Finset.mem_singleton, fresh_u_ne_g, fresh_u_not_D, fresh_u_not_E, fresh_u_not_R,
          fresh_u_not_S, fresh_u_ne_f, or_false, not_false_eq_true])
  have dv_cache_0030 : x ≠ u :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
    exact (show x ≠ u from (by exact fresh_x_ne_u))
  have p0000 :=
    @gElwecutiso x u D R S f E dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
      dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010
      dv_cache_0011
  have p0001 :=
    @gBiimpi (.classMem (.cv f) (synCwecutiso R D S E))
      (synWrex x D (synWrex u E (synWiso (.cv f) (synCin R (synCxp
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))
            (synCin S (synCxp
                (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
                (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))))
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
            (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u)))))))
      p0000
  have p0002 :=
    @gElwecutiso y v D R S g E dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015
      dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021
      dv_cache_0022
  have p0003 :=
    @gBiimpi (.classMem (.cv g) (synCwecutiso R D S E))
      (synWrex y D (synWrex v E (synWiso (.cv g) (synCin R (synCxp
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
            (synCin S (synCxp
                (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))
                (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))))
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
            (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v)))))))
      p0002
  have p0004 :=
    @gSimpl (synWa (.classMem (.cv x) D) (.classMem (.cv u) E))
      (synWa (synWiso (.cv f) (synCin R (synCxp
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))
          (synCin S (synCxp
              (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
              (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))))
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
          (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u)))))
        (synWa (synWa (.classMem (.cv y) D) (.classMem (.cv v) E)) (synWiso (.cv g)
            (synCin R (synCxp
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
            (synCin S (synCxp
                (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))
                (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))))
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
            (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v)))))))
  have p0005 := @gSimpl (.classMem (.cv x) D) (.classMem (.cv u) E)
  have p0006 :=
    @gSyl
      (synWa (synWa (.classMem (.cv x) D) (.classMem (.cv u) E)) (synWa (synWiso (.cv f)
            (synCin R (synCxp
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))
            (synCin S (synCxp
                (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
                (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))))
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
            (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u)))))
          (synWa (synWa (.classMem (.cv y) D) (.classMem (.cv v) E)) (synWiso (.cv g)
              (synCin R (synCxp (synCin D
                    (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y)))) (synCin D
                    (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y)))))) (synCin S
                (synCxp (synCin E
                    (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v)))) (synCin E
                    (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))))
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
              (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))))))
      (synWa (.classMem (.cv x) D) (.classMem (.cv u) E)) (.classMem (.cv x) D) p0004
      p0005
  have p0007 :=
    @gSimpr (synWa (.classMem (.cv x) D) (.classMem (.cv u) E))
      (synWa (synWiso (.cv f) (synCin R (synCxp
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))
          (synCin S (synCxp
              (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
              (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))))
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
          (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u)))))
        (synWa (synWa (.classMem (.cv y) D) (.classMem (.cv v) E)) (synWiso (.cv g)
            (synCin R (synCxp
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
            (synCin S (synCxp
                (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))
                (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))))
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
            (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v)))))))
  have p0008 :=
    @gSimpr
      (synWiso (.cv f) (synCin R (synCxp
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))
        (synCin S (synCxp
            (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
            (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))))
        (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
        (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u)))))
      (synWa (synWa (.classMem (.cv y) D) (.classMem (.cv v) E)) (synWiso (.cv g) (synCin R
            (synCxp (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
          (synCin S (synCxp
              (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))
              (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))))
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
          (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))))
  have p0009 :=
    @gSyl
      (synWa (synWa (.classMem (.cv x) D) (.classMem (.cv u) E)) (synWa (synWiso (.cv f)
            (synCin R (synCxp
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))
            (synCin S (synCxp
                (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
                (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))))
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
            (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u)))))
          (synWa (synWa (.classMem (.cv y) D) (.classMem (.cv v) E)) (synWiso (.cv g)
              (synCin R (synCxp (synCin D
                    (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y)))) (synCin D
                    (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y)))))) (synCin S
                (synCxp (synCin E
                    (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v)))) (synCin E
                    (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))))
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
              (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))))))
      (synWa (synWiso (.cv f) (synCin R (synCxp
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))
          (synCin S (synCxp
              (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
              (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))))
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
          (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u)))))
        (synWa (synWa (.classMem (.cv y) D) (.classMem (.cv v) E)) (synWiso (.cv g)
            (synCin R (synCxp
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
            (synCin S (synCxp
                (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))
                (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))))
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
            (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v)))))))
      (synWa (synWa (.classMem (.cv y) D) (.classMem (.cv v) E)) (synWiso (.cv g) (synCin R
            (synCxp (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
          (synCin S (synCxp
              (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))
              (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))))
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
          (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))))
      p0007 p0008
  have p0010 :=
    @gSimpl (synWa (.classMem (.cv y) D) (.classMem (.cv v) E))
      (synWiso (.cv g) (synCin R (synCxp
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
        (synCin S (synCxp
            (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))
            (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))))
        (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
        (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v)))))
  have p0011 :=
    @gSyl
      (synWa (synWa (.classMem (.cv x) D) (.classMem (.cv u) E)) (synWa (synWiso (.cv f)
            (synCin R (synCxp
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))
            (synCin S (synCxp
                (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
                (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))))
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
            (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u)))))
          (synWa (synWa (.classMem (.cv y) D) (.classMem (.cv v) E)) (synWiso (.cv g)
              (synCin R (synCxp (synCin D
                    (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y)))) (synCin D
                    (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y)))))) (synCin S
                (synCxp (synCin E
                    (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v)))) (synCin E
                    (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))))
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
              (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))))))
      (synWa (synWa (.classMem (.cv y) D) (.classMem (.cv v) E)) (synWiso (.cv g) (synCin R
            (synCxp (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
          (synCin S (synCxp
              (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))
              (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))))
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
          (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))))
      (synWa (.classMem (.cv y) D) (.classMem (.cv v) E)) p0009 p0010
  have p0012 := @gSimpl (.classMem (.cv y) D) (.classMem (.cv v) E)
  have p0013 :=
    @gSyl
      (synWa (synWa (.classMem (.cv x) D) (.classMem (.cv u) E)) (synWa (synWiso (.cv f)
            (synCin R (synCxp
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))
            (synCin S (synCxp
                (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
                (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))))
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
            (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u)))))
          (synWa (synWa (.classMem (.cv y) D) (.classMem (.cv v) E)) (synWiso (.cv g)
              (synCin R (synCxp (synCin D
                    (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y)))) (synCin D
                    (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y)))))) (synCin S
                (synCxp (synCin E
                    (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v)))) (synCin E
                    (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))))
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
              (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))))))
      (synWa (.classMem (.cv y) D) (.classMem (.cv v) E)) (.classMem (.cv y) D) p0011
      p0012
  have p0014 :=
    @gJca
      (synWa (synWa (.classMem (.cv x) D) (.classMem (.cv u) E)) (synWa (synWiso (.cv f)
            (synCin R (synCxp
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))
            (synCin S (synCxp
                (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
                (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))))
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
            (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u)))))
          (synWa (synWa (.classMem (.cv y) D) (.classMem (.cv v) E)) (synWiso (.cv g)
              (synCin R (synCxp (synCin D
                    (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y)))) (synCin D
                    (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y)))))) (synCin S
                (synCxp (synCin E
                    (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v)))) (synCin E
                    (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))))
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
              (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))))))
      (.classMem (.cv x) D) (.classMem (.cv y) D) p0006 p0013
  have p0016 := @gSimpr (.classMem (.cv x) D) (.classMem (.cv u) E)
  have p0017 :=
    @gSyl
      (synWa (synWa (.classMem (.cv x) D) (.classMem (.cv u) E)) (synWa (synWiso (.cv f)
            (synCin R (synCxp
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))
            (synCin S (synCxp
                (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
                (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))))
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
            (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u)))))
          (synWa (synWa (.classMem (.cv y) D) (.classMem (.cv v) E)) (synWiso (.cv g)
              (synCin R (synCxp (synCin D
                    (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y)))) (synCin D
                    (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y)))))) (synCin S
                (synCxp (synCin E
                    (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v)))) (synCin E
                    (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))))
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
              (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))))))
      (synWa (.classMem (.cv x) D) (.classMem (.cv u) E)) (.classMem (.cv u) E) p0004
      p0016
  have p0023 := @gSimpr (.classMem (.cv y) D) (.classMem (.cv v) E)
  have p0024 :=
    @gSyl
      (synWa (synWa (.classMem (.cv x) D) (.classMem (.cv u) E)) (synWa (synWiso (.cv f)
            (synCin R (synCxp
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))
            (synCin S (synCxp
                (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
                (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))))
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
            (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u)))))
          (synWa (synWa (.classMem (.cv y) D) (.classMem (.cv v) E)) (synWiso (.cv g)
              (synCin R (synCxp (synCin D
                    (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y)))) (synCin D
                    (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y)))))) (synCin S
                (synCxp (synCin E
                    (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v)))) (synCin E
                    (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))))
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
              (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))))))
      (synWa (.classMem (.cv y) D) (.classMem (.cv v) E)) (.classMem (.cv v) E) p0011
      p0023
  have p0025 :=
    @gJca
      (synWa (synWa (.classMem (.cv x) D) (.classMem (.cv u) E)) (synWa (synWiso (.cv f)
            (synCin R (synCxp
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))
            (synCin S (synCxp
                (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
                (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))))
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
            (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u)))))
          (synWa (synWa (.classMem (.cv y) D) (.classMem (.cv v) E)) (synWiso (.cv g)
              (synCin R (synCxp (synCin D
                    (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y)))) (synCin D
                    (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y)))))) (synCin S
                (synCxp (synCin E
                    (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v)))) (synCin E
                    (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))))
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
              (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))))))
      (.classMem (.cv u) E) (.classMem (.cv v) E) p0017 p0024
  have p0026 :=
    @gJca
      (synWa (synWa (.classMem (.cv x) D) (.classMem (.cv u) E)) (synWa (synWiso (.cv f)
            (synCin R (synCxp
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))
            (synCin S (synCxp
                (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
                (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))))
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
            (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u)))))
          (synWa (synWa (.classMem (.cv y) D) (.classMem (.cv v) E)) (synWiso (.cv g)
              (synCin R (synCxp (synCin D
                    (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y)))) (synCin D
                    (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y)))))) (synCin S
                (synCxp (synCin E
                    (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v)))) (synCin E
                    (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))))
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
              (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))))))
      (synWa (.classMem (.cv x) D) (.classMem (.cv y) D))
      (synWa (.classMem (.cv u) E) (.classMem (.cv v) E)) p0014 p0025
  have p0028 :=
    @gSimpl
      (synWiso (.cv f) (synCin R (synCxp
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))
        (synCin S (synCxp
            (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
            (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))))
        (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
        (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u)))))
      (synWa (synWa (.classMem (.cv y) D) (.classMem (.cv v) E)) (synWiso (.cv g) (synCin R
            (synCxp (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
          (synCin S (synCxp
              (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))
              (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))))
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
          (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))))
  have p0029 :=
    @gSyl
      (synWa (synWa (.classMem (.cv x) D) (.classMem (.cv u) E)) (synWa (synWiso (.cv f)
            (synCin R (synCxp
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))
            (synCin S (synCxp
                (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
                (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))))
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
            (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u)))))
          (synWa (synWa (.classMem (.cv y) D) (.classMem (.cv v) E)) (synWiso (.cv g)
              (synCin R (synCxp (synCin D
                    (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y)))) (synCin D
                    (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y)))))) (synCin S
                (synCxp (synCin E
                    (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v)))) (synCin E
                    (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))))
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
              (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))))))
      (synWa (synWiso (.cv f) (synCin R (synCxp
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))
          (synCin S (synCxp
              (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
              (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))))
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
          (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u)))))
        (synWa (synWa (.classMem (.cv y) D) (.classMem (.cv v) E)) (synWiso (.cv g)
            (synCin R (synCxp
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
            (synCin S (synCxp
                (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))
                (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))))
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
            (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v)))))))
      (synWiso (.cv f) (synCin R (synCxp
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))
        (synCin S (synCxp
            (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
            (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))))
        (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
        (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u)))))
      p0007 p0028
  have p0033 :=
    @gSimpr (synWa (.classMem (.cv y) D) (.classMem (.cv v) E))
      (synWiso (.cv g) (synCin R (synCxp
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
        (synCin S (synCxp
            (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))
            (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))))
        (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
        (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v)))))
  have p0034 :=
    @gSyl
      (synWa (synWa (.classMem (.cv x) D) (.classMem (.cv u) E)) (synWa (synWiso (.cv f)
            (synCin R (synCxp
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))
            (synCin S (synCxp
                (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
                (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))))
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
            (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u)))))
          (synWa (synWa (.classMem (.cv y) D) (.classMem (.cv v) E)) (synWiso (.cv g)
              (synCin R (synCxp (synCin D
                    (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y)))) (synCin D
                    (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y)))))) (synCin S
                (synCxp (synCin E
                    (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v)))) (synCin E
                    (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))))
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
              (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))))))
      (synWa (synWa (.classMem (.cv y) D) (.classMem (.cv v) E)) (synWiso (.cv g) (synCin R
            (synCxp (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
          (synCin S (synCxp
              (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))
              (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))))
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
          (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))))
      (synWiso (.cv g) (synCin R (synCxp
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
        (synCin S (synCxp
            (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))
            (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))))
        (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
        (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v)))))
      p0009 p0033
  have p0035 :=
    @gJca
      (synWa (synWa (.classMem (.cv x) D) (.classMem (.cv u) E)) (synWa (synWiso (.cv f)
            (synCin R (synCxp
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))
            (synCin S (synCxp
                (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
                (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))))
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
            (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u)))))
          (synWa (synWa (.classMem (.cv y) D) (.classMem (.cv v) E)) (synWiso (.cv g)
              (synCin R (synCxp (synCin D
                    (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y)))) (synCin D
                    (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y)))))) (synCin S
                (synCxp (synCin E
                    (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v)))) (synCin E
                    (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))))
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
              (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))))))
      (synWiso (.cv f) (synCin R (synCxp
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))
        (synCin S (synCxp
            (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
            (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))))
        (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
        (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u)))))
      (synWiso (.cv g) (synCin R (synCxp
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
        (synCin S (synCxp
            (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))
            (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))))
        (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
        (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v)))))
      p0029 p0034
  have p0036 :=
    @gJca
      (synWa (synWa (.classMem (.cv x) D) (.classMem (.cv u) E)) (synWa (synWiso (.cv f)
            (synCin R (synCxp
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))
            (synCin S (synCxp
                (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
                (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))))
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
            (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u)))))
          (synWa (synWa (.classMem (.cv y) D) (.classMem (.cv v) E)) (synWiso (.cv g)
              (synCin R (synCxp (synCin D
                    (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y)))) (synCin D
                    (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y)))))) (synCin S
                (synCxp (synCin E
                    (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v)))) (synCin E
                    (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))))
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
              (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))))))
      (synWa (synWa (.classMem (.cv x) D) (.classMem (.cv y) D))
        (synWa (.classMem (.cv u) E) (.classMem (.cv v) E)))
      (synWa (synWiso (.cv f) (synCin R (synCxp
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))
          (synCin S (synCxp
              (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
              (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))))
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
          (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u)))))
        (synWiso (.cv g) (synCin R (synCxp
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
          (synCin S (synCxp
              (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))
              (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))))
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
          (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))))
      p0026 p0035
  have p0037 :=
    @gWecutisochainndv x y v u D R S f g E hyp_wecutisofamilychainndv_1
      hyp_wecutisofamilychainndv_2
  have p0038 :=
    @gSyl
      (synWa (synWa (.classMem (.cv x) D) (.classMem (.cv u) E)) (synWa (synWiso (.cv f)
            (synCin R (synCxp
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))
            (synCin S (synCxp
                (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
                (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))))
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
            (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u)))))
          (synWa (synWa (.classMem (.cv y) D) (.classMem (.cv v) E)) (synWiso (.cv g)
              (synCin R (synCxp (synCin D
                    (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y)))) (synCin D
                    (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y)))))) (synCin S
                (synCxp (synCin E
                    (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v)))) (synCin E
                    (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))))
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
              (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))))))
      (synWa (synWa (synWa (.classMem (.cv x) D) (.classMem (.cv y) D))
          (synWa (.classMem (.cv u) E) (.classMem (.cv v) E))) (synWa (synWiso (.cv f)
            (synCin R (synCxp
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))
            (synCin S (synCxp
                (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
                (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))))
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
            (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u)))))
          (synWiso (.cv g) (synCin R (synCxp
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
            (synCin S (synCxp
                (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))
                (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))))
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
            (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v)))))))
      (synWo (synWss (.cv f) (.cv g)) (synWss (.cv g) (.cv f))) p0036 p0037
  have p0039 :=
    @gExp45 (synWa (.classMem (.cv x) D) (.classMem (.cv u) E))
      (synWiso (.cv f) (synCin R (synCxp
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))
        (synCin S (synCxp
            (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
            (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))))
        (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
        (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u)))))
      (synWa (.classMem (.cv y) D) (.classMem (.cv v) E))
      (synWiso (.cv g) (synCin R (synCxp
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
        (synCin S (synCxp
            (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))
            (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))))
        (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
        (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v)))))
      (synWo (synWss (.cv f) (.cv g)) (synWss (.cv g) (.cv f))) p0038
  have p0040 :=
    @gImp (synWa (.classMem (.cv x) D) (.classMem (.cv u) E))
      (synWiso (.cv f) (synCin R (synCxp
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))
        (synCin S (synCxp
            (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
            (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))))
        (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
        (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u)))))
      (.imp (synWa (.classMem (.cv y) D) (.classMem (.cv v) E)) (.imp (synWiso (.cv g)
            (synCin R (synCxp
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
            (synCin S (synCxp
                (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))
                (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))))
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
            (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v)))))
          (synWo (synWss (.cv f) (.cv g)) (synWss (.cv g) (.cv f)))))
      p0039
  have p0041 :=
    @gRexlimdvv
      (synWa (synWa (.classMem (.cv x) D) (.classMem (.cv u) E)) (synWiso (.cv f) (synCin R
            (synCxp (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))
          (synCin S (synCxp
              (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
              (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))))
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
          (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))))
      (synWiso (.cv g) (synCin R (synCxp
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
        (synCin S (synCxp
            (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))
            (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))))
        (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
        (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v)))))
      (synWo (synWss (.cv f) (.cv g)) (synWss (.cv g) (.cv f))) y v D E dv_cache_0012
      dv_cache_0023 dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 p0040
  have p0042 :=
    @gSyl5 (.classMem (.cv g) (synCwecutiso R D S E))
      (synWrex y D (synWrex v E (synWiso (.cv g) (synCin R (synCxp
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
            (synCin S (synCxp
                (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))
                (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v))))))
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
            (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv v)))))))
      (synWa (synWa (.classMem (.cv x) D) (.classMem (.cv u) E)) (synWiso (.cv f) (synCin R
            (synCxp (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))
          (synCin S (synCxp
              (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
              (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))))
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
          (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))))
      (synWo (synWss (.cv f) (.cv g)) (synWss (.cv g) (.cv f))) p0003 p0041
  have p0043 :=
    @gEx (synWa (.classMem (.cv x) D) (.classMem (.cv u) E))
      (synWiso (.cv f) (synCin R (synCxp
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))
        (synCin S (synCxp
            (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
            (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))))
        (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
        (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u)))))
      (.imp (.classMem (.cv g) (synCwecutiso R D S E))
        (synWo (synWss (.cv f) (.cv g)) (synWss (.cv g) (.cv f))))
      p0042
  have p0044 :=
    @gRexlimivv
      (synWiso (.cv f) (synCin R (synCxp
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))
        (synCin S (synCxp
            (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
            (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))))
        (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
        (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u)))))
      (.imp (.classMem (.cv g) (synCwecutiso R D S E))
        (synWo (synWss (.cv f) (.cv g)) (synWss (.cv g) (.cv f))))
      x u D E dv_cache_0001 dv_cache_0028 dv_cache_0029 dv_cache_0030 p0043
  have p0045 :=
    @gSyl (.classMem (.cv f) (synCwecutiso R D S E))
      (synWrex x D (synWrex u E (synWiso (.cv f) (synCin R (synCxp
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))
            (synCin S (synCxp
                (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
                (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))))
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
            (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u)))))))
      (.imp (.classMem (.cv g) (synCwecutiso R D S E))
        (synWo (synWss (.cv f) (.cv g)) (synWss (.cv g) (.cv f))))
      p0001 p0044
  have p0046 :=
    @gImp (.classMem (.cv f) (synCwecutiso R D S E))
      (.classMem (.cv g) (synCwecutiso R D S E))
      (synWo (synWss (.cv f) (.cv g)) (synWss (.cv g) (.cv f))) p0045
  exact p0046


end NFChoice.DirectNominalPrf.WPPReplay

end

/-! Certificates from `NominalWPPReplayChunk016Compact001Part005`. -/


section

namespace NFChoice.DirectNominalPrf.WPPReplay

open scoped Fol
open NFChoice.Foundation
open NFChoice.SemanticCore
open NFChoice.ReplaySupport
open NFChoice.Compiler.CompactSourceSyntax

/-- Checked nominal proof certificate identified upstream as `g_wecutisounionfun11ndv`. -/
@[expose]
noncomputable def gWecutisounionfun11ndv (D : Class) (R : Class) (S : Class) (E : Class)
    (hyp_wecutisounionfun11ndv_1 : Nominal.NPrf (synWbr R (synCwe) D))
    (hyp_wecutisounionfun11ndv_2 : Nominal.NPrf (synWbr S (synCwe) E)) :
    Nominal.NPrf
      (synWa (synWfun (synCuni (synCwecutiso R D S E)))
        (synWfun (synCcnv (synCuni (synCwecutiso R D S E))))) :=
  by
  let proofSupport : Finset Var := D.fv ∪ R.fv ∪ S.fv ∪ E.fv
  let f : Var := freshVar proofSupport 0
  let g : Var := freshVar proofSupport 1
  have fresh_f : f ∉ proofSupport :=
    by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_f_not_D : f ∉ D.fv := by
    intro h
    exact
      fresh_f
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (h))))
  have fresh_f_not_R : f ∉ R.fv := by
    intro h
    exact
      fresh_f
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))
  have fresh_f_not_S : f ∉ S.fv := by
    intro h
    exact fresh_f (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_f_not_E : f ∉ E.fv := by
    intro h
    exact fresh_f (Finset.mem_union_right _ (h))
  have fresh_g : g ∉ proofSupport :=
    by
    change freshVar proofSupport 1 ∉ proofSupport
    exact freshVar_not_mem proofSupport 1
  have fresh_g_not_D : g ∉ D.fv := by
    intro h
    exact
      fresh_g
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (h))))
  have fresh_g_not_R : g ∉ R.fv := by
    intro h
    exact
      fresh_g
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))
  have fresh_g_not_S : g ∉ S.fv := by
    intro h
    exact fresh_g (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_g_not_E : g ∉ E.fv := by
    intro h
    exact fresh_g (Finset.mem_union_right _ (h))
  have fresh_f_ne_g : f ≠ g :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have fresh_g_ne_f : g ≠ f := Ne.symm fresh_f_ne_g
  have dv_cache_0001 : g ∉ ((Wff.classMem (.cv f) (synCwecutiso R D S E))).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : g ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwecutiso, Finset.mem_union,
          Finset.mem_singleton, fresh_g_ne_f, fresh_g_not_D, fresh_g_not_E, fresh_g_not_R,
          fresh_g_not_S, or_false, not_false_eq_true])
  have dv_cache_0002 : f ∉ ((synCwecutiso R D S E)).fv :=
    by
    clear dv_cache_0001
    exact
      (by
        have compact_fv_not_mem_empty : f ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwecutiso,
          Finset.mem_union, fresh_f_not_D, fresh_f_not_E, fresh_f_not_R, fresh_f_not_S,
          or_false, not_false_eq_true])
  have dv_cache_0003 : g ∉ ((synCwecutiso R D S E)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact
      (by
        have compact_fv_not_mem_empty : g ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwecutiso,
          Finset.mem_union, fresh_g_not_D, fresh_g_not_E, fresh_g_not_R, fresh_g_not_S,
          or_false, not_false_eq_true])
  have dv_cache_0004 : f ≠ g :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact (show f ≠ g from (by exact fresh_f_ne_g))
  have p0000 := @gElwecutisofun11 D R S f E
  have p0001 :=
    @gWecutisofamilychainndv D R S f g E hyp_wecutisounionfun11ndv_1
      hyp_wecutisounionfun11ndv_2
  have p0002 :=
    @gRalrimiva (.classMem (.cv f) (synCwecutiso R D S E))
      (synWo (synWss (.cv f) (.cv g)) (synWss (.cv g) (.cv f))) g
      (synCwecutiso R D S E) dv_cache_0001 p0001
  have p0003 :=
    @gJca (.classMem (.cv f) (synCwecutiso R D S E))
      (synWa (synWfun (.cv f)) (synWfun (synCcnv (.cv f))))
      (synWral g (synCwecutiso R D S E)
        (synWo (synWss (.cv f) (.cv g)) (synWss (.cv g) (.cv f))))
      p0000 p0002
  have p0004 :=
    @gRgen
      (synWa (synWa (synWfun (.cv f)) (synWfun (synCcnv (.cv f))))
        (synWral g (synCwecutiso R D S E)
          (synWo (synWss (.cv f) (.cv g)) (synWss (.cv g) (.cv f)))))
      f (synCwecutiso R D S E) p0003
  have p0005 :=
    @gFun11uni (synCwecutiso R D S E) f g dv_cache_0002 dv_cache_0003 dv_cache_0004
  have p0006 := Nominal.mp p0004 p0005
  exact p0006

/-- Checked nominal proof certificate identified upstream as `g_elwecutisodmrn`. -/
@[expose]
noncomputable def gElwecutisodmrn (x : Var) (u : Var) (D : Class) (R : Class) (S : Class)
    (f : Var) (E : Class) (dv_D_u : u ∉ D.fv) (dv_D_x : x ∉ D.fv) (dv_E_u : u ∉ E.fv)
    (dv_E_x : x ∉ E.fv) (dv_R_u : u ∉ R.fv) (dv_R_x : x ∉ R.fv) (dv_S_u : u ∉ S.fv)
    (dv_S_x : x ∉ S.fv) (dv_f_u : f ≠ u) (dv_f_x : f ≠ x) (dv_u_x : u ≠ x) :
    Nominal.NPrf
      (.imp (.classMem (.cv f) (synCwecutiso R D S E)) (synWrex x D (synWrex u E (synWa
              (.classEq (synCdm (.cv f)) (synCin D
                  (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))))
              (.classEq (synCrn (.cv f)) (synCin E
                  (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))))))) :=
  by
  have dv_cache_0001 : u ∉ (D).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : u ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_D_u, not_false_eq_true])
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
  have dv_cache_0003 : u ∉ (E).fv :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact
      (by
        have compact_fv_not_mem_empty : u ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_E_u, not_false_eq_true])
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
  have dv_cache_0005 : u ∉ (R).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact
      (by
        have compact_fv_not_mem_empty : u ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_R_u, not_false_eq_true])
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
  have dv_cache_0007 : u ∉ (S).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006
    exact
      (by
        have compact_fv_not_mem_empty : u ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_S_u, not_false_eq_true])
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
  have dv_cache_0009 : f ≠ u :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008
    exact (show f ≠ u from (by exact dv_f_u))
  have dv_cache_0010 : f ≠ x :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009
    exact (show f ≠ x from (by exact dv_f_x))
  have dv_cache_0011 : u ≠ x :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010
    exact (show u ≠ x from (by exact dv_u_x))
  have p0000 :=
    @gElwecutiso x u D R S f E dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
      dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010
      dv_cache_0011
  have p0001 :=
    @gBiimpi (.classMem (.cv f) (synCwecutiso R D S E))
      (synWrex x D (synWrex u E (synWiso (.cv f) (synCin R (synCxp
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))
            (synCin S (synCxp
                (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
                (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))))
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
            (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u)))))))
      p0000
  have p0002 :=
    @gIsof1o (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
      (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
      (synCin R (synCxp
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))
      (synCin S (synCxp
          (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
          (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))))
      (.cv f)
  have p0003 :=
    @gF1odm (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
      (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u)))) (.cv f)
  have p0004 :=
    @gSyl
      (synWiso (.cv f) (synCin R (synCxp
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))
        (synCin S (synCxp
            (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
            (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))))
        (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
        (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u)))))
      (synWf1o (.cv f)
        (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
        (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u)))))
      (.classEq (synCdm (.cv f))
        (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))))
      p0002 p0003
  have p0006 :=
    @gF1ofo (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
      (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u)))) (.cv f)
  have p0007 :=
    @gSyl
      (synWiso (.cv f) (synCin R (synCxp
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))
        (synCin S (synCxp
            (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
            (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))))
        (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
        (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u)))))
      (synWf1o (.cv f)
        (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
        (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u)))))
      (synWfo (.cv f)
        (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
        (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u)))))
      p0002 p0006
  have p0008 :=
    @gForn (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
      (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u)))) (.cv f)
  have p0009 :=
    @gSyl
      (synWiso (.cv f) (synCin R (synCxp
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))
        (synCin S (synCxp
            (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
            (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))))
        (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
        (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u)))))
      (synWfo (.cv f)
        (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
        (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u)))))
      (.classEq (synCrn (.cv f))
        (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u)))))
      p0007 p0008
  have p0010 :=
    @gJca
      (synWiso (.cv f) (synCin R (synCxp
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))
        (synCin S (synCxp
            (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
            (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))))
        (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
        (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u)))))
      (.classEq (synCdm (.cv f))
        (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))))
      (.classEq (synCrn (.cv f))
        (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u)))))
      p0004 p0009
  have p0011 :=
    @gReximi
      (synWiso (.cv f) (synCin R (synCxp
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))
        (synCin S (synCxp
            (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
            (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))))
        (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
        (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u)))))
      (synWa (.classEq (synCdm (.cv f))
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))))
        (.classEq (synCrn (.cv f))
          (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))))
      u E p0010
  have p0012 :=
    @gReximi
      (synWrex u E (synWiso (.cv f) (synCin R (synCxp
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))
          (synCin S (synCxp
              (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
              (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))))
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
          (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))))
      (synWrex u E (synWa (.classEq (synCdm (.cv f))
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))))
          (.classEq (synCrn (.cv f))
            (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u)))))))
      x D p0011
  have p0013 :=
    @gSyl (.classMem (.cv f) (synCwecutiso R D S E))
      (synWrex x D (synWrex u E (synWiso (.cv f) (synCin R (synCxp
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))
            (synCin S (synCxp
                (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
                (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))))
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
            (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u)))))))
      (synWrex x D (synWrex u E (synWa (.classEq (synCdm (.cv f))
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))))
            (.classEq (synCrn (.cv f)) (synCin E
                (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))))))
      p0001 p0012
  exact p0013

/-- Checked nominal proof certificate identified upstream as `g_elwecutisodmrnss`. -/
@[expose]
noncomputable def gElwecutisodmrnss (D : Class) (R : Class) (S : Class) (f : Var)
    (E : Class) :
    Nominal.NPrf
      (.imp (.classMem (.cv f) (synCwecutiso R D S E))
        (synWa (synWss (synCdm (.cv f)) D) (synWss (synCrn (.cv f)) E))) :=
  by
  let proofSupport : Finset Var := D.fv ∪ R.fv ∪ S.fv ∪ ({ f } : Finset Var) ∪ E.fv
  let x : Var := freshVar proofSupport 0
  let u : Var := freshVar proofSupport 1
  have fresh_x : x ∉ proofSupport :=
    by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_x_not_D : x ∉ D.fv := by
    intro h
    exact
      fresh_x
        (Finset.mem_union_left _ (Finset.mem_union_left _
            (Finset.mem_union_left _ (Finset.mem_union_left _ (h)))))
  have fresh_x_not_R : x ∉ R.fv := by
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
  have fresh_x_not_E : x ∉ E.fv := by
    intro h
    exact fresh_x (Finset.mem_union_right _ (h))
  have fresh_u : u ∉ proofSupport :=
    by
    change freshVar proofSupport 1 ∉ proofSupport
    exact freshVar_not_mem proofSupport 1
  have fresh_u_not_D : u ∉ D.fv := by
    intro h
    exact
      fresh_u
        (Finset.mem_union_left _ (Finset.mem_union_left _
            (Finset.mem_union_left _ (Finset.mem_union_left _ (h)))))
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
  have fresh_u_ne_f : u ≠ f := by
    intro h
    exact
      fresh_u
        (Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_singleton.mpr h)))
  have fresh_f_ne_u : f ≠ u := Ne.symm fresh_u_ne_f
  have fresh_u_not_E : u ∉ E.fv := by
    intro h
    exact fresh_u (Finset.mem_union_right _ (h))
  have fresh_x_ne_u : x ≠ u :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have fresh_u_ne_x : u ≠ x := Ne.symm fresh_x_ne_u
  have dv_cache_0001 : u ∉ (D).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : u ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_u_not_D, not_false_eq_true])
  have dv_cache_0002 : x ∉ (D).fv :=
    by
    clear dv_cache_0001
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_x_not_D, not_false_eq_true])
  have dv_cache_0003 : u ∉ (E).fv :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact
      (by
        have compact_fv_not_mem_empty : u ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_u_not_E, not_false_eq_true])
  have dv_cache_0004 : x ∉ (E).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_x_not_E, not_false_eq_true])
  have dv_cache_0005 : u ∉ (R).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact
      (by
        have compact_fv_not_mem_empty : u ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_u_not_R, not_false_eq_true])
  have dv_cache_0006 : x ∉ (R).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_x_not_R, not_false_eq_true])
  have dv_cache_0007 : u ∉ (S).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006
    exact
      (by
        have compact_fv_not_mem_empty : u ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_u_not_S, not_false_eq_true])
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
        simp only [fresh_x_not_S, not_false_eq_true])
  have dv_cache_0009 : f ≠ u :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008
    exact (show f ≠ u from (by exact fresh_f_ne_u))
  have dv_cache_0010 : f ≠ x :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009
    exact (show f ≠ x from (by exact fresh_f_ne_x))
  have dv_cache_0011 : u ≠ x :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010
    exact (show u ≠ x from (by exact fresh_u_ne_x))
  have dv_cache_0012 :
    x ∉ ((synWa (synWss (synCdm (.cv f)) D) (synWss (synCrn (.cv f)) E))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wss,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdm,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_crn, Finset.mem_union,
          Finset.mem_singleton, fresh_x_ne_f, fresh_x_not_D, fresh_x_not_E, or_false,
          not_false_eq_true])
  have dv_cache_0013 :
    u ∉ ((synWa (synWss (synCdm (.cv f)) D) (synWss (synCrn (.cv f)) E))).fv :=
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
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wss,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdm,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_crn, Finset.mem_union,
          Finset.mem_singleton, fresh_u_ne_f, fresh_u_not_D, fresh_u_not_E, or_false,
          not_false_eq_true])
  have dv_cache_0014 : x ≠ u :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013
    exact (show x ≠ u from (by exact fresh_x_ne_u))
  have p0000 :=
    @gElwecutiso x u D R S f E dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
      dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010
      dv_cache_0011
  have p0001 :=
    @gBiimpi (.classMem (.cv f) (synCwecutiso R D S E))
      (synWrex x D (synWrex u E (synWiso (.cv f) (synCin R (synCxp
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))
            (synCin S (synCxp
                (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
                (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))))
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
            (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u)))))))
      p0000
  have p0002 :=
    @gIsof1o (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
      (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
      (synCin R (synCxp
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))
      (synCin S (synCxp
          (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
          (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))))
      (.cv f)
  have p0003 :=
    @gF1odm (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
      (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u)))) (.cv f)
  have p0004 :=
    @gSyl
      (synWiso (.cv f) (synCin R (synCxp
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))
        (synCin S (synCxp
            (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
            (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))))
        (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
        (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u)))))
      (synWf1o (.cv f)
        (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
        (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u)))))
      (.classEq (synCdm (.cv f))
        (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))))
      p0002 p0003
  have p0006 :=
    @gF1ofo (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
      (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u)))) (.cv f)
  have p0007 :=
    @gSyl
      (synWiso (.cv f) (synCin R (synCxp
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))
        (synCin S (synCxp
            (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
            (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))))
        (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
        (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u)))))
      (synWf1o (.cv f)
        (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
        (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u)))))
      (synWfo (.cv f)
        (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
        (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u)))))
      p0002 p0006
  have p0008 :=
    @gForn (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
      (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u)))) (.cv f)
  have p0009 :=
    @gSyl
      (synWiso (.cv f) (synCin R (synCxp
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))
        (synCin S (synCxp
            (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
            (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))))
        (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
        (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u)))))
      (synWfo (.cv f)
        (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
        (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u)))))
      (.classEq (synCrn (.cv f))
        (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u)))))
      p0007 p0008
  have p0010 :=
    @gJca
      (synWiso (.cv f) (synCin R (synCxp
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))
        (synCin S (synCxp
            (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
            (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))))
        (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
        (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u)))))
      (.classEq (synCdm (.cv f))
        (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))))
      (.classEq (synCrn (.cv f))
        (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u)))))
      p0004 p0009
  have p0011 :=
    @gReximi
      (synWiso (.cv f) (synCin R (synCxp
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))
        (synCin S (synCxp
            (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
            (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))))
        (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
        (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u)))))
      (synWa (.classEq (synCdm (.cv f))
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))))
        (.classEq (synCrn (.cv f))
          (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))))
      u E p0010
  have p0012 :=
    @gReximi
      (synWrex u E (synWiso (.cv f) (synCin R (synCxp
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))
          (synCin S (synCxp
              (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
              (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))))
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
          (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))))
      (synWrex u E (synWa (.classEq (synCdm (.cv f))
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))))
          (.classEq (synCrn (.cv f))
            (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u)))))))
      x D p0011
  have p0013 :=
    @gSyl (.classMem (.cv f) (synCwecutiso R D S E))
      (synWrex x D (synWrex u E (synWiso (.cv f) (synCin R (synCxp
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))
            (synCin S (synCxp
                (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
                (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))))
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
            (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u)))))))
      (synWrex x D (synWrex u E (synWa (.classEq (synCdm (.cv f))
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))))
            (.classEq (synCrn (.cv f)) (synCin E
                (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))))))
      p0001 p0012
  have p0014 :=
    @gSimpl
      (.classEq (synCdm (.cv f))
        (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))))
      (.classEq (synCrn (.cv f))
        (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u)))))
  have p0015 := @gInss1 D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))
  have p0016 :=
    @gA1i
      (synWss (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))) D)
      (synWa (.classEq (synCdm (.cv f))
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))))
        (.classEq (synCrn (.cv f))
          (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))))
      p0015
  have p0017 :=
    @gEqsstrd
      (synWa (.classEq (synCdm (.cv f))
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))))
        (.classEq (synCrn (.cv f))
          (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))))
      (synCdm (.cv f))
      (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))) D p0014
      p0016
  have p0018 :=
    @gSimpr
      (.classEq (synCdm (.cv f))
        (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))))
      (.classEq (synCrn (.cv f))
        (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u)))))
  have p0019 := @gInss1 E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u)))
  have p0020 :=
    @gA1i
      (synWss (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u)))) E)
      (synWa (.classEq (synCdm (.cv f))
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))))
        (.classEq (synCrn (.cv f))
          (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))))
      p0019
  have p0021 :=
    @gEqsstrd
      (synWa (.classEq (synCdm (.cv f))
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))))
        (.classEq (synCrn (.cv f))
          (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))))
      (synCrn (.cv f))
      (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u)))) E p0018
      p0020
  have p0022 :=
    @gJca
      (synWa (.classEq (synCdm (.cv f))
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))))
        (.classEq (synCrn (.cv f))
          (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))))
      (synWss (synCdm (.cv f)) D) (synWss (synCrn (.cv f)) E) p0017 p0021
  have p0023 :=
    @gA1i
      (.imp (synWa (.classEq (synCdm (.cv f))
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))))
          (.classEq (synCrn (.cv f))
            (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))))
        (synWa (synWss (synCdm (.cv f)) D) (synWss (synCrn (.cv f)) E)))
      (synWa (.classMem (.cv x) D) (.classMem (.cv u) E)) p0022
  have p0024 :=
    @gRexlimivv
      (synWa (.classEq (synCdm (.cv f))
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))))
        (.classEq (synCrn (.cv f))
          (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))))
      (synWa (synWss (synCdm (.cv f)) D) (synWss (synCrn (.cv f)) E)) x u D E
      dv_cache_0001 dv_cache_0012 dv_cache_0013 dv_cache_0014 p0023
  have p0025 :=
    @gSyl (.classMem (.cv f) (synCwecutiso R D S E))
      (synWrex x D (synWrex u E (synWa (.classEq (synCdm (.cv f))
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))))
            (.classEq (synCrn (.cv f)) (synCin E
                (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))))))
      (synWa (synWss (synCdm (.cv f)) D) (synWss (synCrn (.cv f)) E)) p0013 p0024
  exact p0025

/-- Checked nominal proof certificate identified upstream as `g_wecutisouniondmrnss`. -/
@[expose]
noncomputable def gWecutisouniondmrnss (D : Class) (R : Class) (S : Class) (E : Class) :
    Nominal.NPrf
      (synWa (synWss (synCdm (synCuni (synCwecutiso R D S E))) D)
        (synWss (synCrn (synCuni (synCwecutiso R D S E))) E)) :=
  by
  let proofSupport : Finset Var := D.fv ∪ R.fv ∪ S.fv ∪ E.fv
  let f : Var := freshVar proofSupport 0
  have fresh_f : f ∉ proofSupport :=
    by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_f_not_D : f ∉ D.fv := by
    intro h
    exact
      fresh_f
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (h))))
  have fresh_f_not_R : f ∉ R.fv := by
    intro h
    exact
      fresh_f
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))
  have fresh_f_not_S : f ∉ S.fv := by
    intro h
    exact fresh_f (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_f_not_E : f ∉ E.fv := by
    intro h
    exact fresh_f (Finset.mem_union_right _ (h))
  have dv_cache_0001 : f ∉ ((synCwecutiso R D S E)).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : f ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwecutiso,
          Finset.mem_union, fresh_f_not_D, fresh_f_not_E, fresh_f_not_R, fresh_f_not_S,
          or_false, not_false_eq_true])
  have dv_cache_0002 : f ∉ (D).fv :=
    by
    clear dv_cache_0001
    exact
      (by
        have compact_fv_not_mem_empty : f ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_f_not_D, not_false_eq_true])
  have dv_cache_0003 : f ∉ (E).fv :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact
      (by
        have compact_fv_not_mem_empty : f ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_f_not_E, not_false_eq_true])
  have p0000 := @gDmuni f (synCwecutiso R D S E) dv_cache_0001
  have p0001 := @gElwecutisodmrnss D R S f E
  have p0002 := @gSimpl (synWss (synCdm (.cv f)) D) (synWss (synCrn (.cv f)) E)
  have p0003 :=
    @gSyl (.classMem (.cv f) (synCwecutiso R D S E))
      (synWa (synWss (synCdm (.cv f)) D) (synWss (synCrn (.cv f)) E))
      (synWss (synCdm (.cv f)) D) p0001 p0002
  have p0004 := @gRgen (synWss (synCdm (.cv f)) D) f (synCwecutiso R D S E) p0003
  have p0005 := @gIunss f (synCwecutiso R D S E) (synCdm (.cv f)) D dv_cache_0002
  have p0006 :=
    @gMpbir (synWss (synCiun f (synCwecutiso R D S E) (synCdm (.cv f))) D)
      (synWral f (synCwecutiso R D S E) (synWss (synCdm (.cv f)) D)) p0004 p0005
  have p0007 :=
    @gEqsstri (synCdm (synCuni (synCwecutiso R D S E)))
      (synCiun f (synCwecutiso R D S E) (synCdm (.cv f))) D p0000 p0006
  have p0008 := @gRnuni f (synCwecutiso R D S E) dv_cache_0001
  have p0010 := @gSimpr (synWss (synCdm (.cv f)) D) (synWss (synCrn (.cv f)) E)
  have p0011 :=
    @gSyl (.classMem (.cv f) (synCwecutiso R D S E))
      (synWa (synWss (synCdm (.cv f)) D) (synWss (synCrn (.cv f)) E))
      (synWss (synCrn (.cv f)) E) p0001 p0010
  have p0012 := @gRgen (synWss (synCrn (.cv f)) E) f (synCwecutiso R D S E) p0011
  have p0013 := @gIunss f (synCwecutiso R D S E) (synCrn (.cv f)) E dv_cache_0003
  have p0014 :=
    @gMpbir (synWss (synCiun f (synCwecutiso R D S E) (synCrn (.cv f))) E)
      (synWral f (synCwecutiso R D S E) (synWss (synCrn (.cv f)) E)) p0012 p0013
  have p0015 :=
    @gEqsstri (synCrn (synCuni (synCwecutiso R D S E)))
      (synCiun f (synCwecutiso R D S E) (synCrn (.cv f))) E p0008 p0014
  have p0016 :=
    @gPm32i (synWss (synCdm (synCuni (synCwecutiso R D S E))) D)
      (synWss (synCrn (synCuni (synCwecutiso R D S E))) E) p0007 p0015
  exact p0016


end NFChoice.DirectNominalPrf.WPPReplay

end

/-! Certificates from `NominalWPPReplayChunk016Compact001Part006`. -/


section

namespace NFChoice.DirectNominalPrf.WPPReplay

open scoped Fol
open NFChoice.Foundation
open NFChoice.SemanticCore
open NFChoice.ReplaySupport
open NFChoice.Compiler.CompactSourceSyntax

/-- Checked nominal proof certificate identified upstream as `g_wecutisouniondirectedndv`. -/
@[expose]
noncomputable def gWecutisouniondirectedndv (B : Class) (C : Class) (D : Class)
    (R : Class) (S : Class) (h : Var) (E : Class) (dv_B_h : h ∉ B.fv) (dv_C_h : h ∉ C.fv)
    (dv_D_h : h ∉ D.fv) (dv_E_h : h ∉ E.fv) (dv_R_h : h ∉ R.fv) (dv_S_h : h ∉ S.fv)
    (hyp_wecutisouniondirectedndv_1 : Nominal.NPrf (synWbr R (synCwe) D))
    (hyp_wecutisouniondirectedndv_2 : Nominal.NPrf (synWbr S (synCwe) E)) :
    Nominal.NPrf
      (.imp (synWa (.classMem C (synCuni (synCwecutiso R D S E)))
          (.classMem B (synCuni (synCwecutiso R D S E)))) (synWrex h (synCwecutiso R D S E)
          (synWa (.classMem C (.cv h)) (.classMem B (.cv h))))) :=
  by
  let proofSupport : Finset Var :=
    B.fv ∪ C.fv ∪ D.fv ∪ R.fv ∪ S.fv ∪ ({ h } : Finset Var) ∪ E.fv
  let f : Var := freshVar proofSupport 0
  let g : Var := freshVar proofSupport 1
  have fresh_f : f ∉ proofSupport :=
    by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_f_not_B : f ∉ B.fv := by
    intro h
    exact
      fresh_f
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _
              (Finset.mem_union_left _
                (Finset.mem_union_left _ (Finset.mem_union_left _ (h)))))))
  have fresh_f_not_C : f ∉ C.fv := by
    intro h
    exact
      fresh_f
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _
              (Finset.mem_union_left _
                (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))))))
  have fresh_f_not_D : f ∉ D.fv := by
    intro h
    exact
      fresh_f
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _
              (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))))
  have fresh_f_not_R : f ∉ R.fv := by
    intro h
    exact
      fresh_f
        (Finset.mem_union_left _ (Finset.mem_union_left _
            (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))))
  have fresh_f_not_S : f ∉ S.fv := by
    intro h
    exact
      fresh_f
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))
  have fresh_f_ne_h : f ≠ h := by
    intro h
    exact
      fresh_f
        (Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_singleton.mpr h)))
  have fresh_h_ne_f : h ≠ f := Ne.symm fresh_f_ne_h
  have fresh_f_not_E : f ∉ E.fv := by
    intro h
    exact fresh_f (Finset.mem_union_right _ (h))
  have fresh_g : g ∉ proofSupport :=
    by
    change freshVar proofSupport 1 ∉ proofSupport
    exact freshVar_not_mem proofSupport 1
  have fresh_g_not_B : g ∉ B.fv := by
    intro h
    exact
      fresh_g
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _
              (Finset.mem_union_left _
                (Finset.mem_union_left _ (Finset.mem_union_left _ (h)))))))
  have fresh_g_not_C : g ∉ C.fv := by
    intro h
    exact
      fresh_g
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _
              (Finset.mem_union_left _
                (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))))))
  have fresh_g_not_D : g ∉ D.fv := by
    intro h
    exact
      fresh_g
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _
              (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))))
  have fresh_g_not_R : g ∉ R.fv := by
    intro h
    exact
      fresh_g
        (Finset.mem_union_left _ (Finset.mem_union_left _
            (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))))
  have fresh_g_not_S : g ∉ S.fv := by
    intro h
    exact
      fresh_g
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))
  have fresh_g_ne_h : g ≠ h := by
    intro h
    exact
      fresh_g
        (Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_singleton.mpr h)))
  have fresh_h_ne_g : h ≠ g := Ne.symm fresh_g_ne_h
  have fresh_g_not_E : g ∉ E.fv := by
    intro h
    exact fresh_g (Finset.mem_union_right _ (h))
  have fresh_f_ne_g : f ≠ g :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have fresh_g_ne_f : g ≠ f := Ne.symm fresh_f_ne_g
  have dv_cache_0001 : f ∉ (C).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : f ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_f_not_C, not_false_eq_true])
  have dv_cache_0002 : f ∉ ((synCwecutiso R D S E)).fv :=
    by
    clear dv_cache_0001
    exact
      (by
        have compact_fv_not_mem_empty : f ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwecutiso,
          Finset.mem_union, fresh_f_not_D, fresh_f_not_E, fresh_f_not_R, fresh_f_not_S,
          or_false, not_false_eq_true])
  have dv_cache_0003 : g ∉ (B).fv :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact
      (by
        have compact_fv_not_mem_empty : g ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_g_not_B, not_false_eq_true])
  have dv_cache_0004 : g ∉ ((synCwecutiso R D S E)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact
      (by
        have compact_fv_not_mem_empty : g ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwecutiso,
          Finset.mem_union, fresh_g_not_D, fresh_g_not_E, fresh_g_not_R, fresh_g_not_S,
          or_false, not_false_eq_true])
  have dv_cache_0005 : h ∉ ((Class.cv g)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact
      (by
        have compact_fv_not_mem_empty : h ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_h_ne_g, not_false_eq_true])
  have dv_cache_0006 : h ∉ ((synCwecutiso R D S E)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact
      (by
        have compact_fv_not_mem_empty : h ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwecutiso,
          Finset.mem_union, dv_D_h, dv_E_h, dv_R_h, dv_S_h, or_false, not_false_eq_true])
  have dv_cache_0007 : h ∉ ((synWa (.classMem C (.cv g)) (.classMem B (.cv g)))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006
    exact
      (by
        have compact_fv_not_mem_empty : h ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, dv_C_h, fresh_h_ne_g, dv_B_h, or_false,
          not_false_eq_true])
  have dv_cache_0008 : h ∉ ((Class.cv f)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007
    exact
      (by
        have compact_fv_not_mem_empty : h ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_h_ne_f, not_false_eq_true])
  have dv_cache_0009 : h ∉ ((synWa (.classMem C (.cv f)) (.classMem B (.cv f)))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008
    exact
      (by
        have compact_fv_not_mem_empty : h ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, dv_C_h, fresh_h_ne_f, dv_B_h, or_false,
          not_false_eq_true])
  have dv_cache_0010 :
    g ∉
      ((synWrex h (synCwecutiso R D S E)
          (synWa (.classMem C (.cv h)) (.classMem B (.cv h))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009
    exact
      (by
        have compact_fv_not_mem_empty : g ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wrex,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwecutiso,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase,
          Finset.mem_singleton, fresh_g_not_D, fresh_g_not_E, fresh_g_not_R,
          fresh_g_not_S, fresh_g_not_C, fresh_g_ne_h, fresh_g_not_B, or_false, and_false,
          not_false_eq_true])
  have dv_cache_0011 :
    g ∉ ((synWa (.classMem (.cv f) (synCwecutiso R D S E)) (.classMem C (.cv f)))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010
    exact
      (by
        have compact_fv_not_mem_empty : g ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwecutiso, Finset.mem_union,
          Finset.mem_singleton, fresh_g_ne_f, fresh_g_not_D, fresh_g_not_E, fresh_g_not_R,
          fresh_g_not_S, fresh_g_not_C, or_false, not_false_eq_true])
  have dv_cache_0012 :
    f ∉
      ((synWrex h (synCwecutiso R D S E)
          (synWa (.classMem C (.cv h)) (.classMem B (.cv h))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
    exact
      (by
        have compact_fv_not_mem_empty : f ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wrex,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwecutiso,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase,
          Finset.mem_singleton, fresh_f_not_D, fresh_f_not_E, fresh_f_not_R,
          fresh_f_not_S, fresh_f_not_C, fresh_f_ne_h, fresh_f_not_B, or_false, and_false,
          not_false_eq_true])
  have dv_cache_0013 :
    f ∉ ((synWrex g (synCwecutiso R D S E) (.classMem B (.cv g)))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012
    exact
      (by
        have compact_fv_not_mem_empty : f ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wrex,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwecutiso,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase,
          Finset.mem_singleton, fresh_f_not_D, fresh_f_not_E, fresh_f_not_R,
          fresh_f_not_S, fresh_f_not_B, fresh_f_ne_g, or_false, and_false,
          not_false_eq_true])
  have p0000 :=
    @gSimpl (.classMem C (synCuni (synCwecutiso R D S E)))
      (.classMem B (synCuni (synCwecutiso R D S E)))
  have p0001 := @gEluni2 f C (synCwecutiso R D S E) dv_cache_0001 dv_cache_0002
  have p0002 :=
    @gBiimpi (.classMem C (synCuni (synCwecutiso R D S E)))
      (synWrex f (synCwecutiso R D S E) (.classMem C (.cv f))) p0001
  have p0003 :=
    @gSyl
      (synWa (.classMem C (synCuni (synCwecutiso R D S E)))
        (.classMem B (synCuni (synCwecutiso R D S E))))
      (.classMem C (synCuni (synCwecutiso R D S E)))
      (synWrex f (synCwecutiso R D S E) (.classMem C (.cv f))) p0000 p0002
  have p0004 :=
    @gSimpr (.classMem C (synCuni (synCwecutiso R D S E)))
      (.classMem B (synCuni (synCwecutiso R D S E)))
  have p0005 := @gEluni2 g B (synCwecutiso R D S E) dv_cache_0003 dv_cache_0004
  have p0006 :=
    @gBiimpi (.classMem B (synCuni (synCwecutiso R D S E)))
      (synWrex g (synCwecutiso R D S E) (.classMem B (.cv g))) p0005
  have p0007 :=
    @gSyl
      (synWa (.classMem C (synCuni (synCwecutiso R D S E)))
        (.classMem B (synCuni (synCwecutiso R D S E))))
      (.classMem B (synCuni (synCwecutiso R D S E)))
      (synWrex g (synCwecutiso R D S E) (.classMem B (.cv g))) p0004 p0006
  have p0008 :=
    @gJca
      (synWa (.classMem C (synCuni (synCwecutiso R D S E)))
        (.classMem B (synCuni (synCwecutiso R D S E))))
      (synWrex f (synCwecutiso R D S E) (.classMem C (.cv f)))
      (synWrex g (synCwecutiso R D S E) (.classMem B (.cv g))) p0003 p0007
  have p0009 :=
    @gSimpl
      (synWa (.classMem (.cv f) (synCwecutiso R D S E))
        (.classMem (.cv g) (synCwecutiso R D S E)))
      (synWa (.classMem C (.cv f)) (.classMem B (.cv g)))
  have p0010 :=
    @gSimpr (.classMem (.cv f) (synCwecutiso R D S E))
      (.classMem (.cv g) (synCwecutiso R D S E))
  have p0011 :=
    @gSyl
      (synWa (synWa (.classMem (.cv f) (synCwecutiso R D S E))
          (.classMem (.cv g) (synCwecutiso R D S E)))
        (synWa (.classMem C (.cv f)) (.classMem B (.cv g))))
      (synWa (.classMem (.cv f) (synCwecutiso R D S E))
        (.classMem (.cv g) (synCwecutiso R D S E)))
      (.classMem (.cv g) (synCwecutiso R D S E)) p0009 p0010
  have p0012 :=
    @gA1d
      (synWa (synWa (.classMem (.cv f) (synCwecutiso R D S E))
          (.classMem (.cv g) (synCwecutiso R D S E)))
        (synWa (.classMem C (.cv f)) (.classMem B (.cv g))))
      (.classMem (.cv g) (synCwecutiso R D S E)) (synWss (.cv f) (.cv g)) p0011
  have p0013 :=
    @gSimpr
      (synWa (.classMem (.cv f) (synCwecutiso R D S E))
        (.classMem (.cv g) (synCwecutiso R D S E)))
      (synWa (.classMem C (.cv f)) (.classMem B (.cv g)))
  have p0014 := @gSimpl (.classMem C (.cv f)) (.classMem B (.cv g))
  have p0015 :=
    @gSyl
      (synWa (synWa (.classMem (.cv f) (synCwecutiso R D S E))
          (.classMem (.cv g) (synCwecutiso R D S E)))
        (synWa (.classMem C (.cv f)) (.classMem B (.cv g))))
      (synWa (.classMem C (.cv f)) (.classMem B (.cv g))) (.classMem C (.cv f)) p0013
      p0014
  have p0016 := @gSsel (.cv f) (.cv g) C
  have p0017 :=
    @gSyl5com
      (synWa (synWa (.classMem (.cv f) (synCwecutiso R D S E))
          (.classMem (.cv g) (synCwecutiso R D S E)))
        (synWa (.classMem C (.cv f)) (.classMem B (.cv g))))
      (.classMem C (.cv f)) (synWss (.cv f) (.cv g)) (.classMem C (.cv g)) p0015 p0016
  have p0019 := @gSimpr (.classMem C (.cv f)) (.classMem B (.cv g))
  have p0020 :=
    @gSyl
      (synWa (synWa (.classMem (.cv f) (synCwecutiso R D S E))
          (.classMem (.cv g) (synCwecutiso R D S E)))
        (synWa (.classMem C (.cv f)) (.classMem B (.cv g))))
      (synWa (.classMem C (.cv f)) (.classMem B (.cv g))) (.classMem B (.cv g)) p0013
      p0019
  have p0021 :=
    @gA1d
      (synWa (synWa (.classMem (.cv f) (synCwecutiso R D S E))
          (.classMem (.cv g) (synCwecutiso R D S E)))
        (synWa (.classMem C (.cv f)) (.classMem B (.cv g))))
      (.classMem B (.cv g)) (synWss (.cv f) (.cv g)) p0020
  have p0022 :=
    @gJcad
      (synWa (synWa (.classMem (.cv f) (synCwecutiso R D S E))
          (.classMem (.cv g) (synCwecutiso R D S E)))
        (synWa (.classMem C (.cv f)) (.classMem B (.cv g))))
      (synWss (.cv f) (.cv g)) (.classMem C (.cv g)) (.classMem B (.cv g)) p0017 p0021
  have p0023 :=
    @gJcad
      (synWa (synWa (.classMem (.cv f) (synCwecutiso R D S E))
          (.classMem (.cv g) (synCwecutiso R D S E)))
        (synWa (.classMem C (.cv f)) (.classMem B (.cv g))))
      (synWss (.cv f) (.cv g)) (.classMem (.cv g) (synCwecutiso R D S E))
      (synWa (.classMem C (.cv g)) (.classMem B (.cv g))) p0012 p0022
  have p0024 := @gEleq2 (.cv h) (.cv g) C
  have p0025 := @gEleq2 (.cv h) (.cv g) B
  have p0026 :=
    @gAnbi12d (.classEq (.cv h) (.cv g)) (.classMem C (.cv h)) (.classMem C (.cv g))
      (.classMem B (.cv h)) (.classMem B (.cv g)) p0024 p0025
  have p0027 :=
    @gRspcev (synWa (.classMem C (.cv h)) (.classMem B (.cv h)))
      (synWa (.classMem C (.cv g)) (.classMem B (.cv g))) h (.cv g)
      (synCwecutiso R D S E) dv_cache_0005 dv_cache_0006 dv_cache_0007 p0026
  have p0028 :=
    @gSyl6
      (synWa (synWa (.classMem (.cv f) (synCwecutiso R D S E))
          (.classMem (.cv g) (synCwecutiso R D S E)))
        (synWa (.classMem C (.cv f)) (.classMem B (.cv g))))
      (synWss (.cv f) (.cv g))
      (synWa (.classMem (.cv g) (synCwecutiso R D S E))
        (synWa (.classMem C (.cv g)) (.classMem B (.cv g))))
      (synWrex h (synCwecutiso R D S E) (synWa (.classMem C (.cv h)) (.classMem B (.cv h))))
      p0023 p0027
  have p0030 :=
    @gSimpl (.classMem (.cv f) (synCwecutiso R D S E))
      (.classMem (.cv g) (synCwecutiso R D S E))
  have p0031 :=
    @gSyl
      (synWa (synWa (.classMem (.cv f) (synCwecutiso R D S E))
          (.classMem (.cv g) (synCwecutiso R D S E)))
        (synWa (.classMem C (.cv f)) (.classMem B (.cv g))))
      (synWa (.classMem (.cv f) (synCwecutiso R D S E))
        (.classMem (.cv g) (synCwecutiso R D S E)))
      (.classMem (.cv f) (synCwecutiso R D S E)) p0009 p0030
  have p0032 :=
    @gA1d
      (synWa (synWa (.classMem (.cv f) (synCwecutiso R D S E))
          (.classMem (.cv g) (synCwecutiso R D S E)))
        (synWa (.classMem C (.cv f)) (.classMem B (.cv g))))
      (.classMem (.cv f) (synCwecutiso R D S E)) (synWss (.cv g) (.cv f)) p0031
  have p0036 :=
    @gA1d
      (synWa (synWa (.classMem (.cv f) (synCwecutiso R D S E))
          (.classMem (.cv g) (synCwecutiso R D S E)))
        (synWa (.classMem C (.cv f)) (.classMem B (.cv g))))
      (.classMem C (.cv f)) (synWss (.cv g) (.cv f)) p0015
  have p0040 := @gSsel (.cv g) (.cv f) B
  have p0041 :=
    @gSyl5com
      (synWa (synWa (.classMem (.cv f) (synCwecutiso R D S E))
          (.classMem (.cv g) (synCwecutiso R D S E)))
        (synWa (.classMem C (.cv f)) (.classMem B (.cv g))))
      (.classMem B (.cv g)) (synWss (.cv g) (.cv f)) (.classMem B (.cv f)) p0020 p0040
  have p0042 :=
    @gJcad
      (synWa (synWa (.classMem (.cv f) (synCwecutiso R D S E))
          (.classMem (.cv g) (synCwecutiso R D S E)))
        (synWa (.classMem C (.cv f)) (.classMem B (.cv g))))
      (synWss (.cv g) (.cv f)) (.classMem C (.cv f)) (.classMem B (.cv f)) p0036 p0041
  have p0043 :=
    @gJcad
      (synWa (synWa (.classMem (.cv f) (synCwecutiso R D S E))
          (.classMem (.cv g) (synCwecutiso R D S E)))
        (synWa (.classMem C (.cv f)) (.classMem B (.cv g))))
      (synWss (.cv g) (.cv f)) (.classMem (.cv f) (synCwecutiso R D S E))
      (synWa (.classMem C (.cv f)) (.classMem B (.cv f))) p0032 p0042
  have p0044 := @gEleq2 (.cv h) (.cv f) C
  have p0045 := @gEleq2 (.cv h) (.cv f) B
  have p0046 :=
    @gAnbi12d (.classEq (.cv h) (.cv f)) (.classMem C (.cv h)) (.classMem C (.cv f))
      (.classMem B (.cv h)) (.classMem B (.cv f)) p0044 p0045
  have p0047 :=
    @gRspcev (synWa (.classMem C (.cv h)) (.classMem B (.cv h)))
      (synWa (.classMem C (.cv f)) (.classMem B (.cv f))) h (.cv f)
      (synCwecutiso R D S E) dv_cache_0008 dv_cache_0006 dv_cache_0009 p0046
  have p0048 :=
    @gSyl6
      (synWa (synWa (.classMem (.cv f) (synCwecutiso R D S E))
          (.classMem (.cv g) (synCwecutiso R D S E)))
        (synWa (.classMem C (.cv f)) (.classMem B (.cv g))))
      (synWss (.cv g) (.cv f))
      (synWa (.classMem (.cv f) (synCwecutiso R D S E))
        (synWa (.classMem C (.cv f)) (.classMem B (.cv f))))
      (synWrex h (synCwecutiso R D S E) (synWa (.classMem C (.cv h)) (.classMem B (.cv h))))
      p0043 p0047
  have p0050 :=
    @gWecutisofamilychainndv D R S f g E hyp_wecutisouniondirectedndv_1
      hyp_wecutisouniondirectedndv_2
  have p0051 :=
    @gSyl
      (synWa (synWa (.classMem (.cv f) (synCwecutiso R D S E))
          (.classMem (.cv g) (synCwecutiso R D S E)))
        (synWa (.classMem C (.cv f)) (.classMem B (.cv g))))
      (synWa (.classMem (.cv f) (synCwecutiso R D S E))
        (.classMem (.cv g) (synCwecutiso R D S E)))
      (synWo (synWss (.cv f) (.cv g)) (synWss (.cv g) (.cv f))) p0009 p0050
  have p0052 :=
    @gMpjaod
      (synWa (synWa (.classMem (.cv f) (synCwecutiso R D S E))
          (.classMem (.cv g) (synCwecutiso R D S E)))
        (synWa (.classMem C (.cv f)) (.classMem B (.cv g))))
      (synWss (.cv f) (.cv g))
      (synWrex h (synCwecutiso R D S E) (synWa (.classMem C (.cv h)) (.classMem B (.cv h))))
      (synWss (.cv g) (.cv f)) p0028 p0048 p0051
  have p0053 :=
    @gAn4s (.classMem (.cv f) (synCwecutiso R D S E))
      (.classMem (.cv g) (synCwecutiso R D S E)) (.classMem C (.cv f))
      (.classMem B (.cv g))
      (synWrex h (synCwecutiso R D S E) (synWa (.classMem C (.cv h)) (.classMem B (.cv h))))
      p0052
  have p0054 :=
    @gExp32 (synWa (.classMem (.cv f) (synCwecutiso R D S E)) (.classMem C (.cv f)))
      (.classMem (.cv g) (synCwecutiso R D S E)) (.classMem B (.cv g))
      (synWrex h (synCwecutiso R D S E) (synWa (.classMem C (.cv h)) (.classMem B (.cv h))))
      p0053
  have p0055 :=
    @gRexlimdv (synWa (.classMem (.cv f) (synCwecutiso R D S E)) (.classMem C (.cv f)))
      (.classMem B (.cv g))
      (synWrex h (synCwecutiso R D S E) (synWa (.classMem C (.cv h)) (.classMem B (.cv h))))
      g (synCwecutiso R D S E) dv_cache_0010 dv_cache_0011 p0054
  have p0056 :=
    @gEx (.classMem (.cv f) (synCwecutiso R D S E)) (.classMem C (.cv f))
      (.imp (synWrex g (synCwecutiso R D S E) (.classMem B (.cv g)))
        (synWrex h (synCwecutiso R D S E)
          (synWa (.classMem C (.cv h)) (.classMem B (.cv h)))))
      p0055
  have p0057 :=
    @gCom3r (.classMem (.cv f) (synCwecutiso R D S E)) (.classMem C (.cv f))
      (synWrex g (synCwecutiso R D S E) (.classMem B (.cv g)))
      (synWrex h (synCwecutiso R D S E) (synWa (.classMem C (.cv h)) (.classMem B (.cv h))))
      p0056
  have p0058 :=
    @gRexlimdv (synWrex g (synCwecutiso R D S E) (.classMem B (.cv g)))
      (.classMem C (.cv f))
      (synWrex h (synCwecutiso R D S E) (synWa (.classMem C (.cv h)) (.classMem B (.cv h))))
      f (synCwecutiso R D S E) dv_cache_0012 dv_cache_0013 p0057
  have p0059 :=
    @gCom12 (synWrex g (synCwecutiso R D S E) (.classMem B (.cv g)))
      (synWrex f (synCwecutiso R D S E) (.classMem C (.cv f)))
      (synWrex h (synCwecutiso R D S E) (synWa (.classMem C (.cv h)) (.classMem B (.cv h))))
      p0058
  have p0060 :=
    @gImp (synWrex f (synCwecutiso R D S E) (.classMem C (.cv f)))
      (synWrex g (synCwecutiso R D S E) (.classMem B (.cv g)))
      (synWrex h (synCwecutiso R D S E) (synWa (.classMem C (.cv h)) (.classMem B (.cv h))))
      p0059
  have p0061 :=
    @gSyl
      (synWa (.classMem C (synCuni (synCwecutiso R D S E)))
        (.classMem B (synCuni (synCwecutiso R D S E))))
      (synWa (synWrex f (synCwecutiso R D S E) (.classMem C (.cv f)))
        (synWrex g (synCwecutiso R D S E) (.classMem B (.cv g))))
      (synWrex h (synCwecutiso R D S E) (synWa (.classMem C (.cv h)) (.classMem B (.cv h))))
      p0008 p0060
  exact p0061


end NFChoice.DirectNominalPrf.WPPReplay

end

/-! Certificates from `NominalWPPReplayChunk016Compact001Part007`. -/


section

namespace NFChoice.DirectNominalPrf.WPPReplay

open scoped Fol
open NFChoice.Foundation
open NFChoice.SemanticCore
open NFChoice.ReplaySupport
open NFChoice.Compiler.CompactSourceSyntax

/-- Checked nominal proof certificate identified upstream as `g_wecutisomemberrelndv`. -/
@[expose]
noncomputable def gWecutisomemberrelndv (C : Class) (D : Class) (R : Class) (S : Class)
    (f : Var) (E : Class) (K : Class) (L : Class) (M : Class) :
    Nominal.NPrf
      (.imp (synWa (.classMem (.cv f) (synCwecutiso R D S E))
          (synWa (.classMem (synCop C L) (.cv f)) (.classMem (synCop K M) (.cv f))))
        (synWb (synWbr C R K) (synWbr L S M))) :=
  by
  let proofSupport : Finset Var :=
    C.fv ∪ D.fv ∪ R.fv ∪ S.fv ∪ ({ f } : Finset Var) ∪ E.fv ∪ K.fv ∪ L.fv ∪ M.fv
  let x : Var := freshVar proofSupport 0
  let u : Var := freshVar proofSupport 1
  have fresh_x : x ∉ proofSupport :=
    by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_x_not_C : x ∉ C.fv := by
    intro h
    exact
      fresh_x
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _
              (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _
                    (Finset.mem_union_left _ (Finset.mem_union_left _ (h)))))))))
  have fresh_x_not_D : x ∉ D.fv := by
    intro h
    exact
      fresh_x
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _
              (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _
                    (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))))))))
  have fresh_x_not_R : x ∉ R.fv := by
    intro h
    exact
      fresh_x
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _
              (Finset.mem_union_left _ (Finset.mem_union_left _
                  (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))))))
  have fresh_x_not_S : x ∉ S.fv := by
    intro h
    exact
      fresh_x
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _
              (Finset.mem_union_left _
                (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))))))
  have fresh_x_ne_f : x ≠ f := by
    intro h
    exact
      fresh_x
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _
              (Finset.mem_union_left _
                (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))))))
  have fresh_f_ne_x : f ≠ x := Ne.symm fresh_x_ne_f
  have fresh_x_not_E : x ∉ E.fv := by
    intro h
    exact
      fresh_x
        (Finset.mem_union_left _ (Finset.mem_union_left _
            (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))))
  have fresh_x_not_K : x ∉ K.fv := by
    intro h
    exact
      fresh_x
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))
  have fresh_x_not_L : x ∉ L.fv := by
    intro h
    exact fresh_x (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_x_not_M : x ∉ M.fv := by
    intro h
    exact fresh_x (Finset.mem_union_right _ (h))
  have fresh_u : u ∉ proofSupport :=
    by
    change freshVar proofSupport 1 ∉ proofSupport
    exact freshVar_not_mem proofSupport 1
  have fresh_u_not_C : u ∉ C.fv := by
    intro h
    exact
      fresh_u
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _
              (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _
                    (Finset.mem_union_left _ (Finset.mem_union_left _ (h)))))))))
  have fresh_u_not_D : u ∉ D.fv := by
    intro h
    exact
      fresh_u
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _
              (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _
                    (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))))))))
  have fresh_u_not_R : u ∉ R.fv := by
    intro h
    exact
      fresh_u
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _
              (Finset.mem_union_left _ (Finset.mem_union_left _
                  (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))))))
  have fresh_u_not_S : u ∉ S.fv := by
    intro h
    exact
      fresh_u
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _
              (Finset.mem_union_left _
                (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))))))
  have fresh_u_ne_f : u ≠ f := by
    intro h
    exact
      fresh_u
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _
              (Finset.mem_union_left _
                (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))))))
  have fresh_f_ne_u : f ≠ u := Ne.symm fresh_u_ne_f
  have fresh_u_not_E : u ∉ E.fv := by
    intro h
    exact
      fresh_u
        (Finset.mem_union_left _ (Finset.mem_union_left _
            (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))))
  have fresh_u_not_K : u ∉ K.fv := by
    intro h
    exact
      fresh_u
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))
  have fresh_u_not_L : u ∉ L.fv := by
    intro h
    exact fresh_u (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_u_not_M : u ∉ M.fv := by
    intro h
    exact fresh_u (Finset.mem_union_right _ (h))
  have fresh_x_ne_u : x ≠ u :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have fresh_u_ne_x : u ≠ x := Ne.symm fresh_x_ne_u
  have dv_cache_0001 : u ∉ (D).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : u ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_u_not_D, not_false_eq_true])
  have dv_cache_0002 : x ∉ (D).fv :=
    by
    clear dv_cache_0001
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_x_not_D, not_false_eq_true])
  have dv_cache_0003 : u ∉ (E).fv :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact
      (by
        have compact_fv_not_mem_empty : u ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_u_not_E, not_false_eq_true])
  have dv_cache_0004 : x ∉ (E).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_x_not_E, not_false_eq_true])
  have dv_cache_0005 : u ∉ (R).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact
      (by
        have compact_fv_not_mem_empty : u ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_u_not_R, not_false_eq_true])
  have dv_cache_0006 : x ∉ (R).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_x_not_R, not_false_eq_true])
  have dv_cache_0007 : u ∉ (S).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006
    exact
      (by
        have compact_fv_not_mem_empty : u ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_u_not_S, not_false_eq_true])
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
        simp only [fresh_x_not_S, not_false_eq_true])
  have dv_cache_0009 : f ≠ u :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008
    exact (show f ≠ u from (by exact fresh_f_ne_u))
  have dv_cache_0010 : f ≠ x :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009
    exact (show f ≠ x from (by exact fresh_f_ne_x))
  have dv_cache_0011 : u ≠ x :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010
    exact (show u ≠ x from (by exact fresh_u_ne_x))
  have dv_cache_0012 :
    x ∉
      ((Wff.imp (synWa (.classMem (synCop C L) (.cv f)) (.classMem (synCop K M) (.cv f)))
          (synWb (synWbr C R K) (synWbr L S M)))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cop,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wb,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr, Finset.mem_union,
          Finset.mem_singleton, fresh_x_not_C, fresh_x_not_L, fresh_x_ne_f, fresh_x_not_K,
          fresh_x_not_M, fresh_x_not_R, fresh_x_not_S, or_false, not_false_eq_true])
  have dv_cache_0013 :
    u ∉
      ((Wff.imp (synWa (.classMem (synCop C L) (.cv f)) (.classMem (synCop K M) (.cv f)))
          (synWb (synWbr C R K) (synWbr L S M)))).fv :=
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
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cop,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wb,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr, Finset.mem_union,
          Finset.mem_singleton, fresh_u_not_C, fresh_u_not_L, fresh_u_ne_f, fresh_u_not_K,
          fresh_u_not_M, fresh_u_not_R, fresh_u_not_S, or_false, not_false_eq_true])
  have dv_cache_0014 : x ≠ u :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013
    exact (show x ≠ u from (by exact fresh_x_ne_u))
  have p0000 :=
    @gElwecutiso x u D R S f E dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
      dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010
      dv_cache_0011
  have p0001 :=
    @gBiimpi (.classMem (.cv f) (synCwecutiso R D S E))
      (synWrex x D (synWrex u E (synWiso (.cv f) (synCin R (synCxp
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))
            (synCin S (synCxp
                (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
                (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))))
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
            (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u)))))))
      p0000
  have p0002 :=
    @gSimpl
      (synWiso (.cv f) (synCin R (synCxp
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))
        (synCin S (synCxp
            (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
            (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))))
        (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
        (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u)))))
      (synWa (.classMem (synCop C L) (.cv f)) (.classMem (synCop K M) (.cv f)))
  have p0003 :=
    @gIsores1 (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
      (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u)))) R
      (synCin S (synCxp
          (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
          (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))))
      (.cv f)
  have p0004 :=
    @gBiimpri
      (synWiso (.cv f) R (synCin S (synCxp
            (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
            (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))))
        (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
        (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u)))))
      (synWiso (.cv f) (synCin R (synCxp
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))
        (synCin S (synCxp
            (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
            (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))))
        (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
        (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u)))))
      p0003
  have p0005 :=
    @gIsores2 (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
      (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u)))) R S
      (.cv f)
  have p0006 :=
    @gBiimpri
      (synWiso (.cv f) R S
        (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
        (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u)))))
      (synWiso (.cv f) R (synCin S (synCxp
            (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
            (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))))
        (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
        (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u)))))
      p0005
  have p0007 :=
    @gSyl
      (synWiso (.cv f) (synCin R (synCxp
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))
        (synCin S (synCxp
            (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
            (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))))
        (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
        (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u)))))
      (synWiso (.cv f) R (synCin S (synCxp
            (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
            (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))))
        (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
        (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u)))))
      (synWiso (.cv f) R S
        (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
        (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u)))))
      p0004 p0006
  have p0008 :=
    @gSyl
      (synWa (synWiso (.cv f) (synCin R (synCxp
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))
          (synCin S (synCxp
              (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
              (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))))
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
          (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u)))))
        (synWa (.classMem (synCop C L) (.cv f)) (.classMem (synCop K M) (.cv f))))
      (synWiso (.cv f) (synCin R (synCxp
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))
        (synCin S (synCxp
            (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
            (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))))
        (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
        (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u)))))
      (synWiso (.cv f) R S
        (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
        (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u)))))
      p0002 p0007
  have p0009 :=
    @gSimpr
      (synWiso (.cv f) (synCin R (synCxp
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))
        (synCin S (synCxp
            (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
            (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))))
        (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
        (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u)))))
      (synWa (.classMem (synCop C L) (.cv f)) (.classMem (synCop K M) (.cv f)))
  have p0010 :=
    @gSimpl (.classMem (synCop C L) (.cv f)) (.classMem (synCop K M) (.cv f))
  have p0011 :=
    @gSyl
      (synWa (synWiso (.cv f) (synCin R (synCxp
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))
          (synCin S (synCxp
              (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
              (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))))
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
          (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u)))))
        (synWa (.classMem (synCop C L) (.cv f)) (.classMem (synCop K M) (.cv f))))
      (synWa (.classMem (synCop C L) (.cv f)) (.classMem (synCop K M) (.cv f)))
      (.classMem (synCop C L) (.cv f)) p0009 p0010
  have p0012 := @gOpeldm C L (.cv f)
  have p0013 :=
    @gSyl
      (synWa (synWiso (.cv f) (synCin R (synCxp
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))
          (synCin S (synCxp
              (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
              (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))))
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
          (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u)))))
        (synWa (.classMem (synCop C L) (.cv f)) (.classMem (synCop K M) (.cv f))))
      (.classMem (synCop C L) (.cv f)) (.classMem C (synCdm (.cv f))) p0011 p0012
  have p0021 :=
    @gIsof1o (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
      (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u)))) R S
      (.cv f)
  have p0022 :=
    @gSyl
      (synWa (synWiso (.cv f) (synCin R (synCxp
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))
          (synCin S (synCxp
              (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
              (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))))
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
          (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u)))))
        (synWa (.classMem (synCop C L) (.cv f)) (.classMem (synCop K M) (.cv f))))
      (synWiso (.cv f) R S
        (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
        (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u)))))
      (synWf1o (.cv f)
        (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
        (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u)))))
      p0008 p0021
  have p0023 :=
    @gF1odm (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
      (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u)))) (.cv f)
  have p0024 :=
    @gSyl
      (synWa (synWiso (.cv f) (synCin R (synCxp
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))
          (synCin S (synCxp
              (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
              (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))))
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
          (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u)))))
        (synWa (.classMem (synCop C L) (.cv f)) (.classMem (synCop K M) (.cv f))))
      (synWf1o (.cv f)
        (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
        (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u)))))
      (.classEq (synCdm (.cv f))
        (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))))
      p0022 p0023
  have p0025 :=
    @gEleqtrd
      (synWa (synWiso (.cv f) (synCin R (synCxp
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))
          (synCin S (synCxp
              (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
              (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))))
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
          (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u)))))
        (synWa (.classMem (synCop C L) (.cv f)) (.classMem (synCop K M) (.cv f))))
      C (synCdm (.cv f))
      (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))) p0013
      p0024
  have p0027 :=
    @gSimpr (.classMem (synCop C L) (.cv f)) (.classMem (synCop K M) (.cv f))
  have p0028 :=
    @gSyl
      (synWa (synWiso (.cv f) (synCin R (synCxp
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))
          (synCin S (synCxp
              (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
              (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))))
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
          (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u)))))
        (synWa (.classMem (synCop C L) (.cv f)) (.classMem (synCop K M) (.cv f))))
      (synWa (.classMem (synCop C L) (.cv f)) (.classMem (synCop K M) (.cv f)))
      (.classMem (synCop K M) (.cv f)) p0009 p0027
  have p0029 := @gOpeldm K M (.cv f)
  have p0030 :=
    @gSyl
      (synWa (synWiso (.cv f) (synCin R (synCxp
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))
          (synCin S (synCxp
              (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
              (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))))
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
          (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u)))))
        (synWa (.classMem (synCop C L) (.cv f)) (.classMem (synCop K M) (.cv f))))
      (.classMem (synCop K M) (.cv f)) (.classMem K (synCdm (.cv f))) p0028 p0029
  have p0042 :=
    @gEleqtrd
      (synWa (synWiso (.cv f) (synCin R (synCxp
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))
          (synCin S (synCxp
              (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
              (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))))
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
          (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u)))))
        (synWa (.classMem (synCop C L) (.cv f)) (.classMem (synCop K M) (.cv f))))
      K (synCdm (.cv f))
      (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))) p0030
      p0024
  have p0043 :=
    @gJca
      (synWa (synWiso (.cv f) (synCin R (synCxp
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))
          (synCin S (synCxp
              (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
              (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))))
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
          (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u)))))
        (synWa (.classMem (synCop C L) (.cv f)) (.classMem (synCop K M) (.cv f))))
      (.classMem C (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))))
      (.classMem K (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))))
      p0025 p0042
  have p0044 :=
    @gJca
      (synWa (synWiso (.cv f) (synCin R (synCxp
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))
          (synCin S (synCxp
              (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
              (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))))
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
          (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u)))))
        (synWa (.classMem (synCop C L) (.cv f)) (.classMem (synCop K M) (.cv f))))
      (synWiso (.cv f) R S
        (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
        (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u)))))
      (synWa (.classMem C
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))))
        (.classMem K
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))
      p0008 p0043
  have p0045 :=
    @gIsorel (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
      (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u)))) C K R S
      (.cv f)
  have p0046 :=
    @gSyl
      (synWa (synWiso (.cv f) (synCin R (synCxp
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))
          (synCin S (synCxp
              (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
              (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))))
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
          (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u)))))
        (synWa (.classMem (synCop C L) (.cv f)) (.classMem (synCop K M) (.cv f))))
      (synWa (synWiso (.cv f) R S
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
          (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))) (synWa
          (.classMem C
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))))
          (.classMem K
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))))))
      (synWb (synWbr C R K) (synWbr (synCfv (.cv f) C) S (synCfv (.cv f) K))) p0044
      p0045
  have p0059 :=
    @gF1ofun (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
      (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u)))) (.cv f)
  have p0060 :=
    @gSyl
      (synWa (synWiso (.cv f) (synCin R (synCxp
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))
          (synCin S (synCxp
              (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
              (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))))
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
          (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u)))))
        (synWa (.classMem (synCop C L) (.cv f)) (.classMem (synCop K M) (.cv f))))
      (synWf1o (.cv f)
        (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
        (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u)))))
      (synWfun (.cv f)) p0022 p0059
  have p0061 := @gFunopfv C L (.cv f)
  have p0062 :=
    @gSyl
      (synWa (synWiso (.cv f) (synCin R (synCxp
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))
          (synCin S (synCxp
              (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
              (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))))
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
          (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u)))))
        (synWa (.classMem (synCop C L) (.cv f)) (.classMem (synCop K M) (.cv f))))
      (synWfun (.cv f))
      (.imp (.classMem (synCop C L) (.cv f)) (.classEq (synCfv (.cv f) C) L)) p0060
      p0061
  have p0063 :=
    @gMpd
      (synWa (synWiso (.cv f) (synCin R (synCxp
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))
          (synCin S (synCxp
              (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
              (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))))
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
          (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u)))))
        (synWa (.classMem (synCop C L) (.cv f)) (.classMem (synCop K M) (.cv f))))
      (.classMem (synCop C L) (.cv f)) (.classEq (synCfv (.cv f) C) L) p0011 p0062
  have p0078 := @gFunopfv K M (.cv f)
  have p0079 :=
    @gSyl
      (synWa (synWiso (.cv f) (synCin R (synCxp
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))
          (synCin S (synCxp
              (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
              (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))))
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
          (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u)))))
        (synWa (.classMem (synCop C L) (.cv f)) (.classMem (synCop K M) (.cv f))))
      (synWfun (.cv f))
      (.imp (.classMem (synCop K M) (.cv f)) (.classEq (synCfv (.cv f) K) M)) p0060
      p0078
  have p0080 :=
    @gMpd
      (synWa (synWiso (.cv f) (synCin R (synCxp
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))
          (synCin S (synCxp
              (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
              (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))))
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
          (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u)))))
        (synWa (.classMem (synCop C L) (.cv f)) (.classMem (synCop K M) (.cv f))))
      (.classMem (synCop K M) (.cv f)) (.classEq (synCfv (.cv f) K) M) p0028 p0079
  have p0081 :=
    @gBreq12d
      (synWa (synWiso (.cv f) (synCin R (synCxp
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))
          (synCin S (synCxp
              (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
              (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))))
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
          (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u)))))
        (synWa (.classMem (synCop C L) (.cv f)) (.classMem (synCop K M) (.cv f))))
      (synCfv (.cv f) C) L (synCfv (.cv f) K) M S p0063 p0080
  have p0082 :=
    @gBitrd
      (synWa (synWiso (.cv f) (synCin R (synCxp
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))
          (synCin S (synCxp
              (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
              (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))))
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
          (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u)))))
        (synWa (.classMem (synCop C L) (.cv f)) (.classMem (synCop K M) (.cv f))))
      (synWbr C R K) (synWbr (synCfv (.cv f) C) S (synCfv (.cv f) K)) (synWbr L S M)
      p0046 p0081
  have p0083 :=
    @gEx
      (synWiso (.cv f) (synCin R (synCxp
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))
        (synCin S (synCxp
            (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
            (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))))
        (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
        (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u)))))
      (synWa (.classMem (synCop C L) (.cv f)) (.classMem (synCop K M) (.cv f)))
      (synWb (synWbr C R K) (synWbr L S M)) p0082
  have p0084 :=
    @gA1i
      (.imp (synWiso (.cv f) (synCin R (synCxp
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))
          (synCin S (synCxp
              (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
              (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))))
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
          (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u)))))
        (.imp (synWa (.classMem (synCop C L) (.cv f)) (.classMem (synCop K M) (.cv f)))
          (synWb (synWbr C R K) (synWbr L S M))))
      (synWa (.classMem (.cv x) D) (.classMem (.cv u) E)) p0083
  have p0085 :=
    @gRexlimivv
      (synWiso (.cv f) (synCin R (synCxp
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))
        (synCin S (synCxp
            (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
            (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))))
        (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
        (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u)))))
      (.imp (synWa (.classMem (synCop C L) (.cv f)) (.classMem (synCop K M) (.cv f)))
        (synWb (synWbr C R K) (synWbr L S M)))
      x u D E dv_cache_0001 dv_cache_0012 dv_cache_0013 dv_cache_0014 p0084
  have p0086 :=
    @gSyl (.classMem (.cv f) (synCwecutiso R D S E))
      (synWrex x D (synWrex u E (synWiso (.cv f) (synCin R (synCxp
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))
            (synCin S (synCxp
                (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))
                (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))))
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
            (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u)))))))
      (.imp (synWa (.classMem (synCop C L) (.cv f)) (.classMem (synCop K M) (.cv f)))
        (synWb (synWbr C R K) (synWbr L S M)))
      p0001 p0085
  have p0087 :=
    @gImp (.classMem (.cv f) (synCwecutiso R D S E))
      (synWa (.classMem (synCop C L) (.cv f)) (.classMem (synCop K M) (.cv f)))
      (synWb (synWbr C R K) (synWbr L S M)) p0086
  exact p0087


end NFChoice.DirectNominalPrf.WPPReplay

end

/-! Certificates from `NominalWPPReplayChunk016Compact001Part008`. -/


section

namespace NFChoice.DirectNominalPrf.WPPReplay

open scoped Fol
open NFChoice.Foundation
open NFChoice.SemanticCore
open NFChoice.ReplaySupport
open NFChoice.Compiler.CompactSourceSyntax

/-- Checked nominal proof certificate identified upstream as `g_wecutisounionrelndv`. -/
@[expose]
noncomputable def gWecutisounionrelndv (C : Class) (D : Class) (R : Class) (S : Class)
    (E : Class) (K : Class) (L : Class) (M : Class)
    (hyp_wecutisounionrelndv_1 : Nominal.NPrf (synWbr R (synCwe) D))
    (hyp_wecutisounionrelndv_2 : Nominal.NPrf (synWbr S (synCwe) E)) :
    Nominal.NPrf
      (.imp (synWa (.classMem (synCop C L) (synCuni (synCwecutiso R D S E)))
          (.classMem (synCop K M) (synCuni (synCwecutiso R D S E))))
        (synWb (synWbr C R K) (synWbr L S M))) :=
  by
  let proofSupport : Finset Var := C.fv ∪ D.fv ∪ R.fv ∪ S.fv ∪ E.fv ∪ K.fv ∪ L.fv ∪ M.fv
  let h : Var := freshVar proofSupport 0
  have fresh_h : h ∉ proofSupport :=
    by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_h_not_C : h ∉ C.fv := by
    intro h
    exact
      fresh_h
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _
              (Finset.mem_union_left _ (Finset.mem_union_left _
                  (Finset.mem_union_left _ (Finset.mem_union_left _ (h))))))))
  have fresh_h_not_D : h ∉ D.fv := by
    intro h
    exact
      fresh_h
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _
              (Finset.mem_union_left _ (Finset.mem_union_left _
                  (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))))))
  have fresh_h_not_R : h ∉ R.fv := by
    intro h
    exact
      fresh_h
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _
              (Finset.mem_union_left _
                (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))))))
  have fresh_h_not_S : h ∉ S.fv := by
    intro h
    exact
      fresh_h
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _
              (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))))
  have fresh_h_not_E : h ∉ E.fv := by
    intro h
    exact
      fresh_h
        (Finset.mem_union_left _ (Finset.mem_union_left _
            (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))))
  have fresh_h_not_K : h ∉ K.fv := by
    intro h
    exact
      fresh_h
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))
  have fresh_h_not_L : h ∉ L.fv := by
    intro h
    exact fresh_h (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_h_not_M : h ∉ M.fv := by
    intro h
    exact fresh_h (Finset.mem_union_right _ (h))
  have dv_cache_0001 : h ∉ ((synCop K M)).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : h ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cop, Finset.mem_union,
          fresh_h_not_K, fresh_h_not_M, or_false, not_false_eq_true])
  have dv_cache_0002 : h ∉ ((synCop C L)).fv :=
    by
    clear dv_cache_0001
    exact
      (by
        have compact_fv_not_mem_empty : h ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cop, Finset.mem_union,
          fresh_h_not_C, fresh_h_not_L, or_false, not_false_eq_true])
  have dv_cache_0003 : h ∉ (D).fv :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact
      (by
        have compact_fv_not_mem_empty : h ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_h_not_D, not_false_eq_true])
  have dv_cache_0004 : h ∉ (E).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact
      (by
        have compact_fv_not_mem_empty : h ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_h_not_E, not_false_eq_true])
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
  have dv_cache_0006 : h ∉ (S).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact
      (by
        have compact_fv_not_mem_empty : h ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_h_not_S, not_false_eq_true])
  have dv_cache_0007 : h ∉ ((synWb (synWbr C R K) (synWbr L S M))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006
    exact
      (by
        have compact_fv_not_mem_empty : h ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wb,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr, Finset.mem_union,
          fresh_h_not_C, fresh_h_not_K, fresh_h_not_R, fresh_h_not_L, fresh_h_not_M,
          fresh_h_not_S, or_false, not_false_eq_true])
  have p0000 :=
    @gWecutisouniondirectedndv (synCop K M) (synCop C L) D R S h E dv_cache_0001
      dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006
      hyp_wecutisounionrelndv_1 hyp_wecutisounionrelndv_2
  have p0001 := @gWecutisomemberrelndv C D R S h E K L M
  have p0002 :=
    @gEx (.classMem (.cv h) (synCwecutiso R D S E))
      (synWa (.classMem (synCop C L) (.cv h)) (.classMem (synCop K M) (.cv h)))
      (synWb (synWbr C R K) (synWbr L S M)) p0001
  have p0003 :=
    @gRexlimiv
      (synWa (.classMem (synCop C L) (.cv h)) (.classMem (synCop K M) (.cv h)))
      (synWb (synWbr C R K) (synWbr L S M)) h (synCwecutiso R D S E) dv_cache_0007
      p0002
  have p0004 :=
    @gSyl
      (synWa (.classMem (synCop C L) (synCuni (synCwecutiso R D S E)))
        (.classMem (synCop K M) (synCuni (synCwecutiso R D S E))))
      (synWrex h (synCwecutiso R D S E)
        (synWa (.classMem (synCop C L) (.cv h)) (.classMem (synCop K M) (.cv h))))
      (synWb (synWbr C R K) (synWbr L S M)) p0000 p0003
  exact p0004

/-- Checked nominal proof certificate identified upstream as `g_wecutisounionisondv`. -/
@[expose]
noncomputable def gWecutisounionisondv (D : Class) (R : Class) (S : Class) (E : Class)
    (hyp_wecutisounionisondv_1 : Nominal.NPrf (synWbr R (synCwe) D))
    (hyp_wecutisounionisondv_2 : Nominal.NPrf (synWbr S (synCwe) E)) :
    Nominal.NPrf
      (synWiso (synCuni (synCwecutiso R D S E)) R S
        (synCdm (synCuni (synCwecutiso R D S E)))
        (synCrn (synCuni (synCwecutiso R D S E)))) :=
  by
  let proofSupport : Finset Var := D.fv ∪ R.fv ∪ S.fv ∪ E.fv
  let x : Var := freshVar proofSupport 0
  let y : Var := freshVar proofSupport 1
  have fresh_x : x ∉ proofSupport :=
    by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_x_not_D : x ∉ D.fv := by
    intro h
    exact
      fresh_x
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (h))))
  have fresh_x_not_R : x ∉ R.fv := by
    intro h
    exact
      fresh_x
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))
  have fresh_x_not_S : x ∉ S.fv := by
    intro h
    exact fresh_x (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_x_not_E : x ∉ E.fv := by
    intro h
    exact fresh_x (Finset.mem_union_right _ (h))
  have fresh_y : y ∉ proofSupport :=
    by
    change freshVar proofSupport 1 ∉ proofSupport
    exact freshVar_not_mem proofSupport 1
  have fresh_y_not_D : y ∉ D.fv := by
    intro h
    exact
      fresh_y
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (h))))
  have fresh_y_not_R : y ∉ R.fv := by
    intro h
    exact
      fresh_y
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))
  have fresh_y_not_S : y ∉ S.fv := by
    intro h
    exact fresh_y (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_y_not_E : y ∉ E.fv := by
    intro h
    exact fresh_y (Finset.mem_union_right _ (h))
  have fresh_x_ne_y : x ≠ y :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have dv_cache_0001 : y ∉ ((synCdm (synCuni (synCwecutiso R D S E)))).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdm,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cuni,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwecutiso, Finset.mem_union,
          fresh_y_not_D, fresh_y_not_E, fresh_y_not_R, fresh_y_not_S, or_false,
          not_false_eq_true])
  have dv_cache_0002 : x ≠ y := by
    clear dv_cache_0001
    exact (show x ≠ y from (by exact fresh_x_ne_y))
  have dv_cache_0003 : x ∉ ((synCdm (synCuni (synCwecutiso R D S E)))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdm,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cuni,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwecutiso, Finset.mem_union,
          fresh_x_not_D, fresh_x_not_E, fresh_x_not_R, fresh_x_not_S, or_false,
          not_false_eq_true])
  have dv_cache_0004 : x ∉ ((synCrn (synCuni (synCwecutiso R D S E)))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_crn,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cuni,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwecutiso, Finset.mem_union,
          fresh_x_not_D, fresh_x_not_E, fresh_x_not_R, fresh_x_not_S, or_false,
          not_false_eq_true])
  have dv_cache_0005 : y ∉ ((synCrn (synCuni (synCwecutiso R D S E)))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_crn,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cuni,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwecutiso, Finset.mem_union,
          fresh_y_not_D, fresh_y_not_E, fresh_y_not_R, fresh_y_not_S, or_false,
          not_false_eq_true])
  have dv_cache_0006 : x ∉ ((synCuni (synCwecutiso R D S E))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cuni,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwecutiso, Finset.mem_union,
          fresh_x_not_D, fresh_x_not_E, fresh_x_not_R, fresh_x_not_S, or_false,
          not_false_eq_true])
  have dv_cache_0007 : y ∉ ((synCuni (synCwecutiso R D S E))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cuni,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwecutiso, Finset.mem_union,
          fresh_y_not_D, fresh_y_not_E, fresh_y_not_R, fresh_y_not_S, or_false,
          not_false_eq_true])
  have dv_cache_0008 : x ∉ (R).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_x_not_R, not_false_eq_true])
  have dv_cache_0009 : y ∉ (R).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_y_not_R, not_false_eq_true])
  have dv_cache_0010 : x ∉ (S).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_x_not_S, not_false_eq_true])
  have dv_cache_0011 : y ∉ (S).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_y_not_S, not_false_eq_true])
  have p0000 :=
    @gWecutisounionfun11ndv D R S E hyp_wecutisounionisondv_1 hyp_wecutisounionisondv_2
  have p0001 :=
    @gSimpli (synWfun (synCuni (synCwecutiso R D S E)))
      (synWfun (synCcnv (synCuni (synCwecutiso R D S E)))) p0000
  have p0002 := @gFunfn (synCuni (synCwecutiso R D S E))
  have p0003 :=
    @gMpbi (synWfun (synCuni (synCwecutiso R D S E)))
      (synWfn (synCuni (synCwecutiso R D S E)) (synCdm (synCuni (synCwecutiso R D S E))))
      p0001 p0002
  have p0005 :=
    @gSimpri (synWfun (synCuni (synCwecutiso R D S E)))
      (synWfun (synCcnv (synCuni (synCwecutiso R D S E)))) p0000
  have p0006 :=
    @gPm32i
      (synWfn (synCuni (synCwecutiso R D S E)) (synCdm (synCuni (synCwecutiso R D S E))))
      (synWfun (synCcnv (synCuni (synCwecutiso R D S E)))) p0003 p0005
  have p0007 :=
    @gF1orn (synCdm (synCuni (synCwecutiso R D S E)))
      (synCuni (synCwecutiso R D S E))
  have p0008 :=
    @gMpbir
      (synWf1o (synCuni (synCwecutiso R D S E)) (synCdm (synCuni (synCwecutiso R D S E)))
        (synCrn (synCuni (synCwecutiso R D S E))))
      (synWa (synWfn (synCuni (synCwecutiso R D S E))
          (synCdm (synCuni (synCwecutiso R D S E))))
        (synWfun (synCcnv (synCuni (synCwecutiso R D S E)))))
      p0006 p0007
  have p0011 :=
    @gA1i (synWfun (synCuni (synCwecutiso R D S E)))
      (synWa (.classMem (.cv x) (synCdm (synCuni (synCwecutiso R D S E))))
        (.classMem (.cv y) (synCdm (synCuni (synCwecutiso R D S E)))))
      p0001
  have p0012 :=
    @gSimpl (.classMem (.cv x) (synCdm (synCuni (synCwecutiso R D S E))))
      (.classMem (.cv y) (synCdm (synCuni (synCwecutiso R D S E))))
  have p0013 :=
    @gJca
      (synWa (.classMem (.cv x) (synCdm (synCuni (synCwecutiso R D S E))))
        (.classMem (.cv y) (synCdm (synCuni (synCwecutiso R D S E)))))
      (synWfun (synCuni (synCwecutiso R D S E)))
      (.classMem (.cv x) (synCdm (synCuni (synCwecutiso R D S E)))) p0011 p0012
  have p0014 := @gFunfvop (.cv x) (synCuni (synCwecutiso R D S E))
  have p0015 :=
    @gSyl
      (synWa (.classMem (.cv x) (synCdm (synCuni (synCwecutiso R D S E))))
        (.classMem (.cv y) (synCdm (synCuni (synCwecutiso R D S E)))))
      (synWa (synWfun (synCuni (synCwecutiso R D S E)))
        (.classMem (.cv x) (synCdm (synCuni (synCwecutiso R D S E)))))
      (.classMem (synCop (.cv x) (synCfv (synCuni (synCwecutiso R D S E)) (.cv x)))
        (synCuni (synCwecutiso R D S E)))
      p0013 p0014
  have p0019 :=
    @gSimpr (.classMem (.cv x) (synCdm (synCuni (synCwecutiso R D S E))))
      (.classMem (.cv y) (synCdm (synCuni (synCwecutiso R D S E))))
  have p0020 :=
    @gJca
      (synWa (.classMem (.cv x) (synCdm (synCuni (synCwecutiso R D S E))))
        (.classMem (.cv y) (synCdm (synCuni (synCwecutiso R D S E)))))
      (synWfun (synCuni (synCwecutiso R D S E)))
      (.classMem (.cv y) (synCdm (synCuni (synCwecutiso R D S E)))) p0011 p0019
  have p0021 := @gFunfvop (.cv y) (synCuni (synCwecutiso R D S E))
  have p0022 :=
    @gSyl
      (synWa (.classMem (.cv x) (synCdm (synCuni (synCwecutiso R D S E))))
        (.classMem (.cv y) (synCdm (synCuni (synCwecutiso R D S E)))))
      (synWa (synWfun (synCuni (synCwecutiso R D S E)))
        (.classMem (.cv y) (synCdm (synCuni (synCwecutiso R D S E)))))
      (.classMem (synCop (.cv y) (synCfv (synCuni (synCwecutiso R D S E)) (.cv y)))
        (synCuni (synCwecutiso R D S E)))
      p0020 p0021
  have p0023 :=
    @gJca
      (synWa (.classMem (.cv x) (synCdm (synCuni (synCwecutiso R D S E))))
        (.classMem (.cv y) (synCdm (synCuni (synCwecutiso R D S E)))))
      (.classMem (synCop (.cv x) (synCfv (synCuni (synCwecutiso R D S E)) (.cv x)))
        (synCuni (synCwecutiso R D S E)))
      (.classMem (synCop (.cv y) (synCfv (synCuni (synCwecutiso R D S E)) (.cv y)))
        (synCuni (synCwecutiso R D S E)))
      p0015 p0022
  have p0024 :=
    @gWecutisounionrelndv (.cv x) D R S E (.cv y)
      (synCfv (synCuni (synCwecutiso R D S E)) (.cv x))
      (synCfv (synCuni (synCwecutiso R D S E)) (.cv y)) hyp_wecutisounionisondv_1
      hyp_wecutisounionisondv_2
  have p0025 :=
    @gSyl
      (synWa (.classMem (.cv x) (synCdm (synCuni (synCwecutiso R D S E))))
        (.classMem (.cv y) (synCdm (synCuni (synCwecutiso R D S E)))))
      (synWa (.classMem (synCop (.cv x) (synCfv (synCuni (synCwecutiso R D S E)) (.cv x)))
          (synCuni (synCwecutiso R D S E)))
        (.classMem (synCop (.cv y) (synCfv (synCuni (synCwecutiso R D S E)) (.cv y)))
          (synCuni (synCwecutiso R D S E))))
      (synWb (synWbr (.cv x) R (.cv y))
        (synWbr (synCfv (synCuni (synCwecutiso R D S E)) (.cv x)) S
          (synCfv (synCuni (synCwecutiso R D S E)) (.cv y))))
      p0023 p0024
  have p0026 :=
    @gRgen2
      (synWb (synWbr (.cv x) R (.cv y))
        (synWbr (synCfv (synCuni (synCwecutiso R D S E)) (.cv x)) S
          (synCfv (synCuni (synCwecutiso R D S E)) (.cv y))))
      x y (synCdm (synCuni (synCwecutiso R D S E)))
      (synCdm (synCuni (synCwecutiso R D S E))) dv_cache_0001 dv_cache_0002 p0025
  have p0027 :=
    @gPm32i
      (synWf1o (synCuni (synCwecutiso R D S E)) (synCdm (synCuni (synCwecutiso R D S E)))
        (synCrn (synCuni (synCwecutiso R D S E))))
      (synWral x (synCdm (synCuni (synCwecutiso R D S E)))
        (synWral y (synCdm (synCuni (synCwecutiso R D S E)))
          (synWb (synWbr (.cv x) R (.cv y))
            (synWbr (synCfv (synCuni (synCwecutiso R D S E)) (.cv x)) S
              (synCfv (synCuni (synCwecutiso R D S E)) (.cv y))))))
      p0008 p0026
  have p0028 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominalDfIso x y
      (synCdm (synCuni (synCwecutiso R D S E)))
      (synCrn (synCuni (synCwecutiso R D S E))) R S (synCuni (synCwecutiso R D S E))
      dv_cache_0003 dv_cache_0001 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007
      dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0002
  have p0029 :=
    @gMpbir
      (synWiso (synCuni (synCwecutiso R D S E)) R S
        (synCdm (synCuni (synCwecutiso R D S E)))
        (synCrn (synCuni (synCwecutiso R D S E))))
      (synWa (synWf1o (synCuni (synCwecutiso R D S E))
          (synCdm (synCuni (synCwecutiso R D S E)))
          (synCrn (synCuni (synCwecutiso R D S E))))
        (synWral x (synCdm (synCuni (synCwecutiso R D S E)))
          (synWral y (synCdm (synCuni (synCwecutiso R D S E)))
            (synWb (synWbr (.cv x) R (.cv y))
              (synWbr (synCfv (synCuni (synCwecutiso R D S E)) (.cv x)) S
                (synCfv (synCuni (synCwecutiso R D S E)) (.cv y)))))))
      p0027 p0028
  exact p0029

/-- Checked nominal proof certificate identified upstream as `g_wecutisomemberdmdownndv`. -/
@[expose]
noncomputable def gWecutisomemberdmdownndv (y : Var) (z : Var) (D : Class) (R : Class)
    (S : Class) (f : Var) (E : Class)
    (hyp_wecutisomemberdmdownndv_1 : Nominal.NPrf (synWbr R (synCwe) D)) :
    Nominal.NPrf
      (.imp (synWa (.classMem (.cv f) (synCwecutiso R D S E))
          (synWa (.classMem (.cv y) (synCdm (.cv f)))
            (synWa (.classMem (.cv z) D) (synWbr (.cv z) R (.cv y)))))
        (.classMem (.cv z) (synCdm (.cv f)))) :=
  by
  let proofSupport : Finset Var :=
    ({ y } : Finset Var) ∪ ({ z } : Finset Var) ∪ D.fv ∪ R.fv ∪ S.fv ∪
        ({ f } : Finset Var) ∪
      E.fv
  let x : Var := freshVar proofSupport 0
  let u : Var := freshVar proofSupport 1
  have fresh_x : x ∉ proofSupport :=
    by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_x_ne_y : x ≠ y := by
    intro h
    exact
      fresh_x
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _
              (Finset.mem_union_left _ (Finset.mem_union_left _
                  (Finset.mem_union_left _ (Finset.mem_singleton.mpr h)))))))
  have fresh_x_ne_z : x ≠ z := by
    intro h
    exact
      fresh_x
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _
              (Finset.mem_union_left _ (Finset.mem_union_left _
                  (Finset.mem_union_right _ (Finset.mem_singleton.mpr h)))))))
  have fresh_x_not_D : x ∉ D.fv := by
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
  have fresh_x_not_E : x ∉ E.fv := by
    intro h
    exact fresh_x (Finset.mem_union_right _ (h))
  have fresh_u : u ∉ proofSupport :=
    by
    change freshVar proofSupport 1 ∉ proofSupport
    exact freshVar_not_mem proofSupport 1
  have fresh_u_ne_y : u ≠ y := by
    intro h
    exact
      fresh_u
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _
              (Finset.mem_union_left _ (Finset.mem_union_left _
                  (Finset.mem_union_left _ (Finset.mem_singleton.mpr h)))))))
  have fresh_u_ne_z : u ≠ z := by
    intro h
    exact
      fresh_u
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _
              (Finset.mem_union_left _ (Finset.mem_union_left _
                  (Finset.mem_union_right _ (Finset.mem_singleton.mpr h)))))))
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
  have fresh_u_ne_f : u ≠ f := by
    intro h
    exact
      fresh_u
        (Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_singleton.mpr h)))
  have fresh_f_ne_u : f ≠ u := Ne.symm fresh_u_ne_f
  have fresh_u_not_E : u ∉ E.fv := by
    intro h
    exact fresh_u (Finset.mem_union_right _ (h))
  have fresh_x_ne_u : x ≠ u :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have fresh_u_ne_x : u ≠ x := Ne.symm fresh_x_ne_u
  have dv_cache_0001 : u ∉ (D).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : u ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_u_not_D, not_false_eq_true])
  have dv_cache_0002 : x ∉ (D).fv :=
    by
    clear dv_cache_0001
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_x_not_D, not_false_eq_true])
  have dv_cache_0003 : u ∉ (E).fv :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact
      (by
        have compact_fv_not_mem_empty : u ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_u_not_E, not_false_eq_true])
  have dv_cache_0004 : x ∉ (E).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_x_not_E, not_false_eq_true])
  have dv_cache_0005 : u ∉ (R).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact
      (by
        have compact_fv_not_mem_empty : u ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_u_not_R, not_false_eq_true])
  have dv_cache_0006 : x ∉ (R).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_x_not_R, not_false_eq_true])
  have dv_cache_0007 : u ∉ (S).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006
    exact
      (by
        have compact_fv_not_mem_empty : u ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_u_not_S, not_false_eq_true])
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
        simp only [fresh_x_not_S, not_false_eq_true])
  have dv_cache_0009 : f ≠ u :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008
    exact (show f ≠ u from (by exact fresh_f_ne_u))
  have dv_cache_0010 : f ≠ x :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009
    exact (show f ≠ x from (by exact fresh_f_ne_x))
  have dv_cache_0011 : u ≠ x :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010
    exact (show u ≠ x from (by exact fresh_u_ne_x))
  have dv_cache_0012 :
    x ∉
      ((Wff.imp (synWa (.classMem (.cv y) (synCdm (.cv f)))
            (synWa (.classMem (.cv z) D) (synWbr (.cv z) R (.cv y))))
          (.classMem (.cv z) (synCdm (.cv f))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdm,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr, Finset.mem_union,
          Finset.mem_singleton, fresh_x_ne_y, fresh_x_ne_f, fresh_x_ne_z, fresh_x_not_D,
          fresh_x_not_R, or_false, not_false_eq_true])
  have dv_cache_0013 :
    u ∉
      ((Wff.imp (synWa (.classMem (.cv y) (synCdm (.cv f)))
            (synWa (.classMem (.cv z) D) (synWbr (.cv z) R (.cv y))))
          (.classMem (.cv z) (synCdm (.cv f))))).fv :=
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
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdm,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr, Finset.mem_union,
          Finset.mem_singleton, fresh_u_ne_y, fresh_u_ne_f, fresh_u_ne_z, fresh_u_not_D,
          fresh_u_not_R, or_false, not_false_eq_true])
  have dv_cache_0014 : x ≠ u :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013
    exact (show x ≠ u from (by exact fresh_x_ne_u))
  have p0000 :=
    @gElwecutisodmrn x u D R S f E dv_cache_0001 dv_cache_0002 dv_cache_0003
      dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009
      dv_cache_0010 dv_cache_0011
  have p0001 :=
    @gA1i (synWbr R (synCwe) D)
      (synWa (synWa (.classMem (.cv x) D) (.classMem (.cv u) E)) (synWa (synWa
            (.classEq (synCdm (.cv f))
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))))
            (.classEq (synCrn (.cv f))
              (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))))
          (synWa (.classMem (.cv y) (synCdm (.cv f)))
            (synWa (.classMem (.cv z) D) (synWbr (.cv z) R (.cv y))))))
      hyp_wecutisomemberdmdownndv_1
  have p0002 :=
    @gSimpl (synWa (.classMem (.cv x) D) (.classMem (.cv u) E))
      (synWa (synWa (.classEq (synCdm (.cv f))
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))))
          (.classEq (synCrn (.cv f))
            (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))))
        (synWa (.classMem (.cv y) (synCdm (.cv f)))
          (synWa (.classMem (.cv z) D) (synWbr (.cv z) R (.cv y)))))
  have p0003 := @gSimpl (.classMem (.cv x) D) (.classMem (.cv u) E)
  have p0004 :=
    @gSyl
      (synWa (synWa (.classMem (.cv x) D) (.classMem (.cv u) E)) (synWa (synWa
            (.classEq (synCdm (.cv f))
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))))
            (.classEq (synCrn (.cv f))
              (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))))
          (synWa (.classMem (.cv y) (synCdm (.cv f)))
            (synWa (.classMem (.cv z) D) (synWbr (.cv z) R (.cv y))))))
      (synWa (.classMem (.cv x) D) (.classMem (.cv u) E)) (.classMem (.cv x) D) p0002
      p0003
  have p0005 :=
    @gJca
      (synWa (synWa (.classMem (.cv x) D) (.classMem (.cv u) E)) (synWa (synWa
            (.classEq (synCdm (.cv f))
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))))
            (.classEq (synCrn (.cv f))
              (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))))
          (synWa (.classMem (.cv y) (synCdm (.cv f)))
            (synWa (.classMem (.cv z) D) (synWbr (.cv z) R (.cv y))))))
      (synWbr R (synCwe) D) (.classMem (.cv x) D) p0001 p0004
  have p0006 :=
    @gSimpr (synWa (.classMem (.cv x) D) (.classMem (.cv u) E))
      (synWa (synWa (.classEq (synCdm (.cv f))
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))))
          (.classEq (synCrn (.cv f))
            (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))))
        (synWa (.classMem (.cv y) (synCdm (.cv f)))
          (synWa (.classMem (.cv z) D) (synWbr (.cv z) R (.cv y)))))
  have p0007 :=
    @gSimpr
      (synWa (.classEq (synCdm (.cv f))
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))))
        (.classEq (synCrn (.cv f))
          (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))))
      (synWa (.classMem (.cv y) (synCdm (.cv f)))
        (synWa (.classMem (.cv z) D) (synWbr (.cv z) R (.cv y))))
  have p0008 :=
    @gSyl
      (synWa (synWa (.classMem (.cv x) D) (.classMem (.cv u) E)) (synWa (synWa
            (.classEq (synCdm (.cv f))
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))))
            (.classEq (synCrn (.cv f))
              (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))))
          (synWa (.classMem (.cv y) (synCdm (.cv f)))
            (synWa (.classMem (.cv z) D) (synWbr (.cv z) R (.cv y))))))
      (synWa (synWa (.classEq (synCdm (.cv f))
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))))
          (.classEq (synCrn (.cv f))
            (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))))
        (synWa (.classMem (.cv y) (synCdm (.cv f)))
          (synWa (.classMem (.cv z) D) (synWbr (.cv z) R (.cv y)))))
      (synWa (.classMem (.cv y) (synCdm (.cv f)))
        (synWa (.classMem (.cv z) D) (synWbr (.cv z) R (.cv y))))
      p0006 p0007
  have p0009 :=
    @gSimpl (.classMem (.cv y) (synCdm (.cv f)))
      (synWa (.classMem (.cv z) D) (synWbr (.cv z) R (.cv y)))
  have p0010 :=
    @gSyl
      (synWa (synWa (.classMem (.cv x) D) (.classMem (.cv u) E)) (synWa (synWa
            (.classEq (synCdm (.cv f))
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))))
            (.classEq (synCrn (.cv f))
              (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))))
          (synWa (.classMem (.cv y) (synCdm (.cv f)))
            (synWa (.classMem (.cv z) D) (synWbr (.cv z) R (.cv y))))))
      (synWa (.classMem (.cv y) (synCdm (.cv f)))
        (synWa (.classMem (.cv z) D) (synWbr (.cv z) R (.cv y))))
      (.classMem (.cv y) (synCdm (.cv f))) p0008 p0009
  have p0012 :=
    @gSimpl
      (synWa (.classEq (synCdm (.cv f))
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))))
        (.classEq (synCrn (.cv f))
          (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))))
      (synWa (.classMem (.cv y) (synCdm (.cv f)))
        (synWa (.classMem (.cv z) D) (synWbr (.cv z) R (.cv y))))
  have p0013 :=
    @gSyl
      (synWa (synWa (.classMem (.cv x) D) (.classMem (.cv u) E)) (synWa (synWa
            (.classEq (synCdm (.cv f))
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))))
            (.classEq (synCrn (.cv f))
              (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))))
          (synWa (.classMem (.cv y) (synCdm (.cv f)))
            (synWa (.classMem (.cv z) D) (synWbr (.cv z) R (.cv y))))))
      (synWa (synWa (.classEq (synCdm (.cv f))
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))))
          (.classEq (synCrn (.cv f))
            (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))))
        (synWa (.classMem (.cv y) (synCdm (.cv f)))
          (synWa (.classMem (.cv z) D) (synWbr (.cv z) R (.cv y)))))
      (synWa (.classEq (synCdm (.cv f))
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))))
        (.classEq (synCrn (.cv f))
          (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))))
      p0006 p0012
  have p0014 :=
    @gSimpl
      (.classEq (synCdm (.cv f))
        (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))))
      (.classEq (synCrn (.cv f))
        (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u)))))
  have p0015 :=
    @gSyl
      (synWa (synWa (.classMem (.cv x) D) (.classMem (.cv u) E)) (synWa (synWa
            (.classEq (synCdm (.cv f))
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))))
            (.classEq (synCrn (.cv f))
              (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))))
          (synWa (.classMem (.cv y) (synCdm (.cv f)))
            (synWa (.classMem (.cv z) D) (synWbr (.cv z) R (.cv y))))))
      (synWa (.classEq (synCdm (.cv f))
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))))
        (.classEq (synCrn (.cv f))
          (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))))
      (.classEq (synCdm (.cv f))
        (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))))
      p0013 p0014
  have p0016 :=
    @gEleqtrd
      (synWa (synWa (.classMem (.cv x) D) (.classMem (.cv u) E)) (synWa (synWa
            (.classEq (synCdm (.cv f))
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))))
            (.classEq (synCrn (.cv f))
              (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))))
          (synWa (.classMem (.cv y) (synCdm (.cv f)))
            (synWa (.classMem (.cv z) D) (synWbr (.cv z) R (.cv y))))))
      (.cv y) (synCdm (.cv f))
      (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))) p0010
      p0015
  have p0020 :=
    @gSimpr (.classMem (.cv y) (synCdm (.cv f)))
      (synWa (.classMem (.cv z) D) (synWbr (.cv z) R (.cv y)))
  have p0021 :=
    @gSyl
      (synWa (synWa (.classMem (.cv x) D) (.classMem (.cv u) E)) (synWa (synWa
            (.classEq (synCdm (.cv f))
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))))
            (.classEq (synCrn (.cv f))
              (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))))
          (synWa (.classMem (.cv y) (synCdm (.cv f)))
            (synWa (.classMem (.cv z) D) (synWbr (.cv z) R (.cv y))))))
      (synWa (.classMem (.cv y) (synCdm (.cv f)))
        (synWa (.classMem (.cv z) D) (synWbr (.cv z) R (.cv y))))
      (synWa (.classMem (.cv z) D) (synWbr (.cv z) R (.cv y))) p0008 p0020
  have p0022 := @gSimpl (.classMem (.cv z) D) (synWbr (.cv z) R (.cv y))
  have p0023 :=
    @gSyl
      (synWa (synWa (.classMem (.cv x) D) (.classMem (.cv u) E)) (synWa (synWa
            (.classEq (synCdm (.cv f))
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))))
            (.classEq (synCrn (.cv f))
              (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))))
          (synWa (.classMem (.cv y) (synCdm (.cv f)))
            (synWa (.classMem (.cv z) D) (synWbr (.cv z) R (.cv y))))))
      (synWa (.classMem (.cv z) D) (synWbr (.cv z) R (.cv y))) (.classMem (.cv z) D)
      p0021 p0022
  have p0024 :=
    @gJca
      (synWa (synWa (.classMem (.cv x) D) (.classMem (.cv u) E)) (synWa (synWa
            (.classEq (synCdm (.cv f))
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))))
            (.classEq (synCrn (.cv f))
              (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))))
          (synWa (.classMem (.cv y) (synCdm (.cv f)))
            (synWa (.classMem (.cv z) D) (synWbr (.cv z) R (.cv y))))))
      (.classMem (.cv y)
        (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))))
      (.classMem (.cv z) D) p0016 p0023
  have p0030 := @gSimpr (.classMem (.cv z) D) (synWbr (.cv z) R (.cv y))
  have p0031 :=
    @gSyl
      (synWa (synWa (.classMem (.cv x) D) (.classMem (.cv u) E)) (synWa (synWa
            (.classEq (synCdm (.cv f))
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))))
            (.classEq (synCrn (.cv f))
              (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))))
          (synWa (.classMem (.cv y) (synCdm (.cv f)))
            (synWa (.classMem (.cv z) D) (synWbr (.cv z) R (.cv y))))))
      (synWa (.classMem (.cv z) D) (synWbr (.cv z) R (.cv y)))
      (synWbr (.cv z) R (.cv y)) p0021 p0030
  have p0032 :=
    @gN3jca
      (synWa (synWa (.classMem (.cv x) D) (.classMem (.cv u) E)) (synWa (synWa
            (.classEq (synCdm (.cv f))
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))))
            (.classEq (synCrn (.cv f))
              (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))))
          (synWa (.classMem (.cv y) (synCdm (.cv f)))
            (synWa (.classMem (.cv z) D) (synWbr (.cv z) R (.cv y))))))
      (synWa (synWbr R (synCwe) D) (.classMem (.cv x) D))
      (synWa (.classMem (.cv y)
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))))
        (.classMem (.cv z) D))
      (synWbr (.cv z) R (.cv y)) p0005 p0024 p0031
  have p0033 := @gStrictsegdown x y z D R
  have p0034 :=
    @gSyl
      (synWa (synWa (.classMem (.cv x) D) (.classMem (.cv u) E)) (synWa (synWa
            (.classEq (synCdm (.cv f))
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))))
            (.classEq (synCrn (.cv f))
              (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))))
          (synWa (.classMem (.cv y) (synCdm (.cv f)))
            (synWa (.classMem (.cv z) D) (synWbr (.cv z) R (.cv y))))))
      (synW3a (synWa (synWbr R (synCwe) D) (.classMem (.cv x) D)) (synWa (.classMem (.cv y)
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))))
          (.classMem (.cv z) D)) (synWbr (.cv z) R (.cv y)))
      (.classMem (.cv z)
        (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))))
      p0032 p0033
  have p0040 :=
    @gEleqtrrd
      (synWa (synWa (.classMem (.cv x) D) (.classMem (.cv u) E)) (synWa (synWa
            (.classEq (synCdm (.cv f))
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))))
            (.classEq (synCrn (.cv f))
              (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))))
          (synWa (.classMem (.cv y) (synCdm (.cv f)))
            (synWa (.classMem (.cv z) D) (synWbr (.cv z) R (.cv y))))))
      (.cv z) (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
      (synCdm (.cv f)) p0034 p0015
  have p0041 :=
    @gExp32 (synWa (.classMem (.cv x) D) (.classMem (.cv u) E))
      (synWa (.classEq (synCdm (.cv f))
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))))
        (.classEq (synCrn (.cv f))
          (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))))
      (synWa (.classMem (.cv y) (synCdm (.cv f)))
        (synWa (.classMem (.cv z) D) (synWbr (.cv z) R (.cv y))))
      (.classMem (.cv z) (synCdm (.cv f))) p0040
  have p0042 :=
    @gRexlimivv
      (synWa (.classEq (synCdm (.cv f))
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))))
        (.classEq (synCrn (.cv f))
          (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))))
      (.imp (synWa (.classMem (.cv y) (synCdm (.cv f)))
          (synWa (.classMem (.cv z) D) (synWbr (.cv z) R (.cv y))))
        (.classMem (.cv z) (synCdm (.cv f))))
      x u D E dv_cache_0001 dv_cache_0012 dv_cache_0013 dv_cache_0014 p0041
  have p0043 :=
    @gSyl (.classMem (.cv f) (synCwecutiso R D S E))
      (synWrex x D (synWrex u E (synWa (.classEq (synCdm (.cv f))
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))))
            (.classEq (synCrn (.cv f)) (synCin E
                (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv u))))))))
      (.imp (synWa (.classMem (.cv y) (synCdm (.cv f)))
          (synWa (.classMem (.cv z) D) (synWbr (.cv z) R (.cv y))))
        (.classMem (.cv z) (synCdm (.cv f))))
      p0000 p0042
  have p0044 :=
    @gImp (.classMem (.cv f) (synCwecutiso R D S E))
      (synWa (.classMem (.cv y) (synCdm (.cv f)))
        (synWa (.classMem (.cv z) D) (synWbr (.cv z) R (.cv y))))
      (.classMem (.cv z) (synCdm (.cv f))) p0043
  exact p0044


end NFChoice.DirectNominalPrf.WPPReplay

end
