/-
Copyright (c) 2026 Elliot Glazer and NFNotWPP contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elliot Glazer and NFNotWPP contributors
-/

module

public import LeanPool.NFWeakPartition.NominalAlphaOprabCompactSupport001
public import LeanPool.NFWeakPartition.WPPCompactSyntaxFVExplicitPart010
public import LeanPool.NFWeakPartition.FocusedFVPaths

/-! NF weak partition development: NominalAlphaOprabCompactCertificate001. -/


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

/-! The equality branches in the nominal batch source are unnecessary here:
the three inner binders are paired with themselves, while only the outer
fresh binder is renamed.  This certificate therefore works uniformly even
when any of `x`, `y`, and `z` coincide. -/


/-- Checked nominal proof certificate identified upstream as `nb049_oprab_alpha_certificate`. -/
@[expose]
noncomputable def nb049OprabAlphaCertificate (ph : Wff) (x : Var) (y : Var) (z : Var)
    (w : Var) (dv_ph_w : w ∉ ph.fv) (dv_w_x : w ≠ x) (dv_w_y : w ≠ y) (dv_w_z : w ≠ z) :
    TAlphaClass [] (synCoprab x y z ph)
      (.cab w (synWex x (synWex y (synWex z
              (synWa (.classEq (.cv w) (synCop (synCop (.cv x) (.cv y)) (.cv z))) ph))))) :=
  by
  let alphaDummy000 : Var :=
    freshVar (({ x } : Finset Var) ∪ ({ y } : Finset Var) ∪ ({ z } : Finset Var) ∪ ph.fv)
      0
  have fresh_000 :
    alphaDummy000 ∉
      (({ x } : Finset Var) ∪ ({ y } : Finset Var) ∪ ({ z } : Finset Var) ∪ ph.fv) :=
    by
    change
      freshVar
          (({ x } : Finset Var) ∪ ({ y } : Finset Var) ∪ ({ z } : Finset Var) ∪ ph.fv) 0 ∉
        (({ x } : Finset Var) ∪ ({ y } : Finset Var) ∪ ({ z } : Finset Var) ∪ ph.fv)
    exact freshVar_not_mem _ 0
  have support_mem_x :
    x ∈ (({ x } : Finset Var) ∪ ({ y } : Finset Var) ∪ ({ z } : Finset Var) ∪ ph.fv) :=
    by
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_union]
    left
    exact Finset.mem_singleton_self _
  have support_mem_y :
    y ∈ (({ x } : Finset Var) ∪ ({ y } : Finset Var) ∪ ({ z } : Finset Var) ∪ ph.fv) :=
    by
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_union]
    right
    exact Finset.mem_singleton_self _
  have support_mem_z :
    z ∈ (({ x } : Finset Var) ∪ ({ y } : Finset Var) ∪ ({ z } : Finset Var) ∪ ph.fv) :=
    by
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_union]
    right
    exact Finset.mem_singleton_self _
  have alpha_ne_x : alphaDummy000 ≠ x :=
    Ne.symm (Nat.ne_of_lt (mem_lt_freshVar support_mem_x 0))
  have alpha_ne_y : alphaDummy000 ≠ y :=
    Ne.symm (Nat.ne_of_lt (mem_lt_freshVar support_mem_y 0))
  have alpha_ne_z : alphaDummy000 ≠ z :=
    Ne.symm (Nat.ne_of_lt (mem_lt_freshVar support_mem_z 0))
  have triple_dummy_notmem :
    alphaDummy000 ∉ (synCop (synCop (Class.cv x) (Class.cv y)) (Class.cv z)).fv := by
    simp only [fv_syn_cop, fv_class_cv, Finset.mem_union, Finset.mem_singleton,
      alpha_ne_x, alpha_ne_y, alpha_ne_z, or_false, not_false_eq_true]
  have triple_w_notmem :
    w ∉ (synCop (synCop (Class.cv x) (Class.cv y)) (Class.cv z)).fv := by
    simp only [fv_syn_cop, fv_class_cv, Finset.mem_union, Finset.mem_singleton, dv_w_x,
      dv_w_y, dv_w_z, or_false, not_false_eq_true]
  have triple_refl :
    TReflOn [(z, z), (y, y), (x, x), (alphaDummy000, w)]
      (synCop (synCop (Class.cv x) (Class.cv y)) (Class.cv z)).fv :=
    nb049ReflOnSelf3Fresh x y z alphaDummy000 w _ triple_dummy_notmem triple_w_notmem
  have focused_dummy_notmem : alphaDummy000 ∉ ph.fv :=
    by
    change
      freshVar
          (({ x } : Finset Var) ∪ ({ y } : Finset Var) ∪ ({ z } : Finset Var) ∪ ph.fv) 0 ∉
        ph.fv
    exact
      NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 0
        (fun _ hu => Finset.mem_union_right _ hu)
  have neg_dummy_notmem : alphaDummy000 ∉ (Wff.neg ph).fv := by
    exact fun hmem => focused_dummy_notmem ((fv_wff_neg ph) ▸ hmem)
  have neg_w_notmem : w ∉ (Wff.neg ph).fv := by
    exact fun hmem => dv_ph_w ((fv_wff_neg ph) ▸ hmem)
  have neg_refl :
    TReflOn [(z, z), (y, y), (x, x), (alphaDummy000, w)] (Wff.neg ph).fv :=
    nb049ReflOnSelf3Fresh x y z alphaDummy000 w _ neg_dummy_notmem neg_w_notmem
  exact
    TAlphaClass.cab
      (TAlphaWff.ex (TAlphaWff.ex (TAlphaWff.ex (TAlphaWff.neg (TAlphaWff.imp (TAlphaWff.classEq
                  (TAlphaClass.cv (TAlphaVar.there alpha_ne_z dv_w_z
                      (TAlphaVar.there alpha_ne_y dv_w_y
                        (TAlphaVar.there alpha_ne_x dv_w_x (TAlphaVar.here _ _ _)))))
                  (TAlphaClass.reflOfReflOn [(z, z), (y, y), (x, x), (alphaDummy000, w)]
                    (synCop (synCop (Class.cv x) (Class.cv y)) (Class.cv z)) triple_refl))
                (TAlphaWff.reflOfReflOn [(z, z), (y, y), (x, x), (alphaDummy000, w)]
                  (Wff.neg ph) neg_refl))))))

end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired
