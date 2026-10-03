/-
Copyright (c) 2026 Elliot Glazer and NFNotWPP contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elliot Glazer and NFNotWPP contributors
-/

module

public import LeanPool.NFWeakPartition.NominalAlphaTransport
public import LeanPool.NFWeakPartition.WPPCompactSyntaxFVExplicitPart010
public import LeanPool.NFWeakPartition.FocusedFVPaths

/-! NF weak partition development: NominalAlphaRepairedBase001037OpabFVReflOnHelpers004. -/


public section


namespace NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired

open scoped Fol
open NFChoice.Foundation
open NFChoice.Foundation.ExactLiteralTrial
open NFChoice.SemanticCore
open NFChoice.ReplaySupport
open NFChoice.Compiler.CompactSourceSyntax
open NFChoice.Compiler.CompactSyntaxFVExplicit
open NFChoice.Compiler.WPPCompactSyntaxFVExplicit
open NFChoice.Compiler.CoreFVSimp
open NFChoice.DefinitionLeaves.AlphaFocusedSupport
open NFChoice.DefinitionLeaves.AlphaFocusedFV
open NFChoice.DirectNominalPrf
open NFChoice.DirectNominalPrf.Nominal

theorem nb037_opab_notmem_syn_cop_cv_cv {a x y : Var} (ha_x : a ≠ x) (ha_y : a ≠ y) :
    a ∉ (syn_cop (Class.cv x) (Class.cv y)).fv :=
  by
  intro h_mem
  have h_union : a ∈ (Class.cv x).fv ∪ (Class.cv y).fv :=
    (fv_syn_cop (Class.cv x) (Class.cv y)) ▸ h_mem
  rcases Finset.mem_union.mp h_union with h_x | h_y
  · exact ha_x (Finset.mem_singleton.mp ((fv_class_cv x) ▸ h_x))
  · exact ha_y (Finset.mem_singleton.mp ((fv_class_cv y) ▸ h_y))

theorem nb037_opab_support_mem_x (ph : Wff) (x y : Var) :
    x ∈ (({ x } : Finset Var) ∪ ({ y } : Finset Var) ∪ ph.fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  with_reducible rw [Finset.mem_union]
  left
  exact Finset.mem_singleton_self _

theorem nb037_opab_support_mem_y (ph : Wff) (x y : Var) :
    y ∈ (({ x } : Finset Var) ∪ ({ y } : Finset Var) ∪ ph.fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  with_reducible rw [Finset.mem_union]
  right
  exact Finset.mem_singleton_self _

theorem nb037_opab_fresh_ne_x (ph : Wff) (x y : Var) :
    freshVar (({ x } : Finset Var) ∪ ({ y } : Finset Var) ∪ ph.fv) 0 ≠ x := by
  exact Ne.symm (Nat.ne_of_lt (mem_lt_freshVar (nb037_opab_support_mem_x ph x y) 0))

theorem nb037_opab_fresh_ne_y (ph : Wff) (x y : Var) :
    freshVar (({ x } : Finset Var) ∪ ({ y } : Finset Var) ∪ ph.fv) 0 ≠ y := by
  exact Ne.symm (Nat.ne_of_lt (mem_lt_freshVar (nb037_opab_support_mem_y ph x y) 0))

theorem nb037_opab_fresh_notmem_syn_cop_cv_cv (ph : Wff) (x y : Var) :
    freshVar (({ x } : Finset Var) ∪ ({ y } : Finset Var) ∪ ph.fv) 0 ∉
      (syn_cop (Class.cv x) (Class.cv y)).fv :=
  by
  exact
    nb037_opab_notmem_syn_cop_cv_cv (nb037_opab_fresh_ne_x ph x y)
      (nb037_opab_fresh_ne_y ph x y)

theorem nb037_opab_z_notmem_syn_cop_cv_cv (x y z : Var) (dv_x_z : x ≠ z)
    (dv_y_z : y ≠ z) : z ∉ (syn_cop (Class.cv x) (Class.cv y)).fv := by
  exact nb037_opab_notmem_syn_cop_cv_cv (Ne.symm dv_x_z) (Ne.symm dv_y_z)

theorem nb037_opab_notmem_neg_of_notmem {a : Var} {ph : Wff} (h : a ∉ ph.fv) :
    a ∉ (Wff.neg ph).fv := by
  intro h_mem
  exact h ((fv_wff_neg ph) ▸ h_mem)

theorem nb037_opab_fresh_notmem_ph (ph : Wff) (x y : Var) :
    freshVar (({ x } : Finset Var) ∪ ({ y } : Finset Var) ∪ ph.fv) 0 ∉ ph.fv := by
  exact
    NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 0
      (fun _ h_mem => Finset.mem_union_right _ h_mem)

theorem nb037_opab_fresh_notmem_neg (ph : Wff) (x y : Var) :
    freshVar (({ x } : Finset Var) ∪ ({ y } : Finset Var) ∪ ph.fv) 0 ∉ (Wff.neg ph).fv :=
  by exact nb037_opab_notmem_neg_of_notmem (nb037_opab_fresh_notmem_ph ph x y)

theorem nb037_opab_z_notmem_neg (ph : Wff) (z : Var) (dv_ph_z : z ∉ ph.fv) :
    z ∉ (Wff.neg ph).fv := by exact nb037_opab_notmem_neg_of_notmem dv_ph_z

@[expose]
noncomputable def nb037_opab_reflOn_three_pair (support : Finset Var) (x y d z : Var)
    (d_notmem : d ∉ support) (z_notmem : z ∉ support) :
    TReflOn [(y, y), (x, x), (d, z)] support :=
  by
  intro u hu
  by_cases h_y : u = y
  · subst u
    exact TAlphaVar.here _ _ _
  · exact
      TAlphaVar.there h_y h_y
        (by
          by_cases h_x : u = x
          · subst u
            exact TAlphaVar.here _ _ _
          · exact
              TAlphaVar.there h_x h_x
                (TAlphaVar.there (fun h => d_notmem (h ▸ hu)) (fun h => z_notmem (h ▸ hu))
                  (TAlphaVar.free (by simp) (by simp))))

end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired
