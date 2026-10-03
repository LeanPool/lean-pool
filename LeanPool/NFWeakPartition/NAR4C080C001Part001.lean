/-
Copyright (c) 2026 Elliot Glazer and NFNotWPP contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elliot Glazer and NFNotWPP contributors
-/

module

public import LeanPool.NFWeakPartition.NominalAlphaCompactEnvFreshSupport002
public import LeanPool.NFWeakPartition.WPPCompactSyntaxFVExplicitPart010
public import LeanPool.NFWeakPartition.FocusedFVPaths

/-! NF weak partition development: NAR4C080C001Part001. -/


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

@[expose]
noncomputable def nb080_alpha_dummy_000 (A : Class) (B : Class) : Var :=
  (freshVar ((A).fv ∪ (B).fv) 0)

theorem nb080_fresh_000 (A : Class) (B : Class) :
    (nb080_alpha_dummy_000 A B) ∉ ((A).fv ∪ (B).fv) := by
  simpa only [nb080_alpha_dummy_000] using freshVar_not_mem ((A).fv ∪ (B).fv) 0

theorem nb080_focused_notmem_0000 (A : Class) (B : Class) :
    (nb080_alpha_dummy_000 A B) ∉ A.fv :=
  by
  change freshVar ((A).fv ∪ (B).fv) 0 ∉ A.fv
  exact
    NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 0
      (fun u hu => Finset.mem_union_left _ (hu))

theorem nb080_compact_envfresh_0000 (z : Var) (A : Class) (B : Class)
    (dv_A_z : z ∉ A.fv) : TEnvFresh [((nb080_alpha_dummy_000 A B), z)] A.fv := by
  exact
    (TEnvFresh.consFresh (nb080_alpha_dummy_000 A B) z (nb080_focused_notmem_0000 A B)
      dv_A_z (TEnvFresh.nil A.fv))

@[expose]
noncomputable def nb080_focused_refl_0000 (z : Var) (A : Class) (B : Class)
    (dv_A_z : z ∉ A.fv) : TReflOn [((nb080_alpha_dummy_000 A B), z)] A.fv :=
  TEnvFresh.reflOn (nb080_compact_envfresh_0000 z A B dv_A_z)

theorem nb080_focused_notmem_0001 (A : Class) (B : Class) :
    (nb080_alpha_dummy_000 A B) ∉ B.fv :=
  by
  change freshVar ((A).fv ∪ (B).fv) 0 ∉ B.fv
  exact
    NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 0
      (fun u hu => Finset.mem_union_right _ (hu))

theorem nb080_compact_envfresh_0001 (z : Var) (A : Class) (B : Class)
    (dv_B_z : z ∉ B.fv) : TEnvFresh [((nb080_alpha_dummy_000 A B), z)] B.fv := by
  exact
    (TEnvFresh.consFresh (nb080_alpha_dummy_000 A B) z (nb080_focused_notmem_0001 A B)
      dv_B_z (TEnvFresh.nil B.fv))

@[expose]
noncomputable def nb080_focused_refl_0001 (z : Var) (A : Class) (B : Class)
    (dv_B_z : z ∉ B.fv) : TReflOn [((nb080_alpha_dummy_000 A B), z)] B.fv :=
  TEnvFresh.reflOn (nb080_compact_envfresh_0001 z A B dv_B_z)

@[expose]
noncomputable def nominal_df_sep2 (z : Var) (A : Class) (B : Class)
    (__dv_A_B : Disjoint A.fv B.fv) (dv_A_z : z ∉ A.fv) (dv_B_z : z ∉ B.fv) :
    Nominal.NPrf
      (.classEq (syn_csep2 A B) (.cab z
          (syn_wo (syn_wa (.classMem A (.cv z)) (.neg (.classMem B (.cv z))))
            (syn_wa (.classMem B (.cv z)) (.neg (.classMem A (.cv z))))))) :=
  by
  exact
    Nominal.alphaClassEq
      (TAlphaClass.cab (TAlphaWff.imp (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
                (TAlphaClass.refl_of_reflOn [((nb080_alpha_dummy_000 A B), z)] A
                  (nb080_focused_refl_0000 z A B dv_A_z))
                (TAlphaClass.cv (TAlphaVar.here _ _ _))) (TAlphaWff.neg (TAlphaWff.classMem
                  (TAlphaClass.refl_of_reflOn [((nb080_alpha_dummy_000 A B), z)] B
                    (nb080_focused_refl_0001 z A B dv_B_z))
                  (TAlphaClass.cv (TAlphaVar.here _ _ _)))))) (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.refl_of_reflOn [((nb080_alpha_dummy_000 A B), z)] B
                (nb080_focused_refl_0001 z A B dv_B_z)) (TAlphaClass.cv (TAlphaVar.here _ _ _)))
            (TAlphaWff.neg (TAlphaWff.classMem
                (TAlphaClass.refl_of_reflOn [((nb080_alpha_dummy_000 A B), z)] A
                  (nb080_focused_refl_0000 z A B dv_A_z))
                (TAlphaClass.cv (TAlphaVar.here _ _ _)))))))

end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired
