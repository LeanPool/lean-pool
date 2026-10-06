/-
Copyright (c) 2026 Elliot Glazer and NFNotWPP contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elliot Glazer and NFNotWPP contributors
-/

module

public import LeanPool.NFWeakPartition.NominalAlphaCompactEnvFreshSupport002
public import LeanPool.NFWeakPartition.WPPCompactSyntaxFVExplicitPart010
public import LeanPool.NFWeakPartition.FocusedFVPaths

/-! NF weak partition development: NAR4C085C001Part001. -/


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

/-- Checked nominal proof certificate identified upstream as `nb085_alpha_dummy_000`. -/
@[expose]
noncomputable def nb085AlphaDummy000 (A : Class) (B : Class) (C : Class) (R : Class) :
    Var :=
  (freshVar ((R).fv ∪ (A).fv ∪ (B).fv ∪ (C).fv) 0)

theorem nb085_fresh_000 (A : Class) (B : Class) (C : Class) (R : Class) :
    (nb085AlphaDummy000 A B C R) ∉ ((R).fv ∪ (A).fv ∪ (B).fv ∪ (C).fv) := by
  simpa only [nb085AlphaDummy000] using
    freshVar_not_mem ((R).fv ∪ (A).fv ∪ (B).fv ∪ (C).fv) 0

theorem nb085_focused_notmem_0000 (A : Class) (B : Class) (C : Class) (R : Class) :
    (nb085AlphaDummy000 A B C R) ∉ A.fv :=
  by
  change freshVar ((R).fv ∪ (A).fv ∪ (B).fv ∪ (C).fv) 0 ∉ A.fv
  exact
    NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 0
      (fun u hu =>
        Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (hu))))

theorem nb085_focused_notmem_0001 (A : Class) (B : Class) (C : Class) (R : Class) :
    (nb085AlphaDummy000 A B C R) ∉ B.fv :=
  by
  change freshVar ((R).fv ∪ (A).fv ∪ (B).fv ∪ (C).fv) 0 ∉ B.fv
  exact
    NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 0
      (fun u hu => Finset.mem_union_left _ (Finset.mem_union_right _ (hu)))

theorem nb085_focused_notmem_0002 (A : Class) (B : Class) (C : Class) (R : Class) :
    (nb085AlphaDummy000 A B C R) ∉ R.fv :=
  by
  change freshVar ((R).fv ∪ (A).fv ∪ (B).fv ∪ (C).fv) 0 ∉ R.fv
  exact
    NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 0
      (fun u hu =>
        Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (hu))))

theorem nb085_wpp_notmem_0000 (A : Class) (B : Class) (C : Class) (R : Class) :
    (nb085AlphaDummy000 A B C R) ∉ ((synCfdif R A B)).fv := by
  simpa only [nb085AlphaDummy000, fv_syn_cfdif, Finset.mem_union, not_or] using
    (And.intro
      (And.intro (nb085_focused_notmem_0000 A B C R) (nb085_focused_notmem_0001 A B C R))
      (nb085_focused_notmem_0002 A B C R))

theorem nb085_wpp_notmem_0001 (A : Class) (B : Class) (R : Class) (d : Var)
    (dv_A_d : d ∉ A.fv) (dv_B_d : d ∉ B.fv) (dv_R_d : d ∉ R.fv) :
    d ∉ ((synCfdif R A B)).fv := by
  simpa only [fv_syn_cfdif, Finset.mem_union, not_or] using
    (And.intro (And.intro dv_A_d dv_B_d) dv_R_d)

theorem nb085_compact_envfresh_0000 (A : Class) (B : Class) (C : Class) (R : Class)
    (d : Var) (dv_A_d : d ∉ A.fv) (dv_B_d : d ∉ B.fv) (dv_R_d : d ∉ R.fv) :
    TEnvFresh [((nb085AlphaDummy000 A B C R), d)] ((synCfdif R A B)).fv := by
  exact
    (TEnvFresh.consFresh (nb085AlphaDummy000 A B C R) d (nb085_wpp_notmem_0000 A B C R)
      (nb085_wpp_notmem_0001 A B R d dv_A_d dv_B_d dv_R_d)
      (TEnvFresh.nil ((synCfdif R A B)).fv))

/-- Checked nominal proof certificate identified upstream as `nb085_wpp_refl_0000`. -/
@[expose]
noncomputable def nb085WppRefl0000 (A : Class) (B : Class) (C : Class) (R : Class)
    (d : Var) (dv_A_d : d ∉ A.fv) (dv_B_d : d ∉ B.fv) (dv_R_d : d ∉ R.fv) :
    TReflOn [((nb085AlphaDummy000 A B C R), d)] ((synCfdif R A B)).fv :=
  TEnvFresh.reflOn (nb085_compact_envfresh_0000 A B C R d dv_A_d dv_B_d dv_R_d)

theorem nb085_focused_notmem_0003 (A : Class) (B : Class) (C : Class) (R : Class) :
    (nb085AlphaDummy000 A B C R) ∉ C.fv :=
  by
  change freshVar ((R).fv ∪ (A).fv ∪ (B).fv ∪ (C).fv) 0 ∉ C.fv
  exact
    NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 0
      (fun u hu => Finset.mem_union_right _ (hu))

theorem nb085_compact_envfresh_0001 (A : Class) (B : Class) (C : Class) (R : Class)
    (d : Var) (dv_C_d : d ∉ C.fv) :
    TEnvFresh [((nb085AlphaDummy000 A B C R), d)] C.fv := by
  exact
    (TEnvFresh.consFresh (nb085AlphaDummy000 A B C R) d
      (nb085_focused_notmem_0003 A B C R) dv_C_d (TEnvFresh.nil C.fv))

/-- Checked nominal proof certificate identified upstream as `nb085_focused_refl_0000`. -/
@[expose]
noncomputable def nb085FocusedRefl0000 (A : Class) (B : Class) (C : Class) (R : Class)
    (d : Var) (dv_C_d : d ∉ C.fv) : TReflOn [((nb085AlphaDummy000 A B C R), d)] C.fv :=
  TEnvFresh.reflOn (nb085_compact_envfresh_0001 A B C R d dv_C_d)

/-- Checked nominal proof certificate identified upstream as `nominal_df_fdrow`. -/
@[expose]
noncomputable def nominalDfFdrow (A : Class) (B : Class) (C : Class) (R : Class)
    (d : Var) (__dv_A_B : Disjoint A.fv B.fv) (__dv_A_C : Disjoint A.fv C.fv)
    (__dv_A_R : Disjoint A.fv R.fv) (dv_A_d : d ∉ A.fv) (__dv_B_C : Disjoint B.fv C.fv)
    (__dv_B_R : Disjoint B.fv R.fv) (dv_B_d : d ∉ B.fv) (__dv_C_R : Disjoint C.fv R.fv)
    (dv_C_d : d ∉ C.fv) (dv_R_d : d ∉ R.fv) :
    Nominal.NPrf
      (.classEq (synCfdrow R A B C) (synCrab d (synCfdif R A B) (.classMem C (.cv d)))) :=
  by
  exact
    Nominal.alphaClassEq
      (TAlphaClass.cab (TAlphaWff.conj
          (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
            (TAlphaClass.reflOfReflOn [((nb085AlphaDummy000 A B C R), d)]
              (synCfdif R A B) (nb085WppRefl0000 A B C R d dv_A_d dv_B_d dv_R_d)))
          (TAlphaWff.classMem
            (TAlphaClass.reflOfReflOn [((nb085AlphaDummy000 A B C R), d)] C
              (nb085FocusedRefl0000 A B C R d dv_C_d))
            (TAlphaClass.cv (TAlphaVar.here _ _ _)))))

end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired
