/-
Copyright (c) 2026 Elliot Glazer and NFNotWPP contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elliot Glazer and NFNotWPP contributors
-/

module

public import LeanPool.NFWeakPartition.NAR4C082C001Part005

/-! NF weak partition development: NAR4C082C001Part006. -/


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

theorem nb082_focused_notmem_0039 (A : Class) (B : Class) (R : Class) (p : Var) :
    (nb082_alpha_dummy_043 A B R p) ∉ B.fv :=
  by
  change
    freshVar
        (((syn_cin (syn_cimak (syn_ccnvk (syn_cfdminsep R A B)) (syn_csn (Class.cv p)))
            (syn_c1c))).fv)
        0 ∉
      B.fv
  refine NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 0 ?_
  intro u hu
  rw [fv_syn_cin (syn_cimak (syn_ccnvk (syn_cfdminsep R A B)) (syn_csn (Class.cv p)))
      (syn_c1c)]
  rw [Finset.mem_union]
  left
  rw [fv_syn_cimak (syn_ccnvk (syn_cfdminsep R A B)) (syn_csn (Class.cv p))]
  rw [Finset.mem_union]
  left
  rw [fv_syn_ccnvk (syn_cfdminsep R A B)]
  rw [fv_syn_cfdminsep R A B]
  rw [Finset.mem_union]
  left
  rw [Finset.mem_union]
  right
  exact hu

theorem nb082_focused_notmem_0040 (A : Class) (B : Class) (R : Class) (p : Var) :
    (nb082_alpha_dummy_043 A B R p) ∉ R.fv :=
  by
  change
    freshVar
        (((syn_cin (syn_cimak (syn_ccnvk (syn_cfdminsep R A B)) (syn_csn (Class.cv p)))
            (syn_c1c))).fv)
        0 ∉
      R.fv
  refine NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 0 ?_
  intro u hu
  rw [fv_syn_cin (syn_cimak (syn_ccnvk (syn_cfdminsep R A B)) (syn_csn (Class.cv p)))
      (syn_c1c)]
  rw [Finset.mem_union]
  left
  rw [fv_syn_cimak (syn_ccnvk (syn_cfdminsep R A B)) (syn_csn (Class.cv p))]
  rw [Finset.mem_union]
  left
  rw [fv_syn_ccnvk (syn_cfdminsep R A B)]
  rw [fv_syn_cfdminsep R A B]
  rw [Finset.mem_union]
  right
  exact hu

theorem nb082_wpp_notmem_0123 (A : Class) (B : Class) (R : Class) (p : Var) :
    (nb082_alpha_dummy_043 A B R p) ∉ ((syn_ccnvk (syn_cfdminsep R A B))).fv := by
  simpa only [nb082_alpha_dummy_043, fv_syn_ccnvk, fv_syn_cfdminsep, Finset.mem_union,
    not_or] using
    (And.intro
      (And.intro (nb082_focused_notmem_0038 A B R p) (nb082_focused_notmem_0039 A B R p))
      (nb082_focused_notmem_0040 A B R p))

theorem nb082_focused_notmem_0041 (A : Class) (B : Class) (R : Class) :
    (nb082_alpha_dummy_001 A B R) ∉ A.fv :=
  by
  change
    freshVar
        (({(nb082_alpha_dummy_000 A B R)} : Finset Var) ∪ ((syn_cxpk B B)).fv ∪
          ((syn_cfdminvalp R A B (Class.cv (nb082_alpha_dummy_000 A B R)))).fv)
        0 ∉
      A.fv
  refine NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 0 ?_
  intro u hu
  rw [Finset.mem_union]
  right
  rw [fv_syn_cfdminvalp R A B (Class.cv (nb082_alpha_dummy_000 A B R))]
  rw [Finset.mem_union]
  left
  rw [Finset.mem_union]
  left
  rw [Finset.mem_union]
  left
  exact hu

theorem nb082_focused_notmem_0042 (A : Class) (B : Class) (R : Class) :
    (nb082_alpha_dummy_001 A B R) ∉ R.fv :=
  by
  change
    freshVar
        (({(nb082_alpha_dummy_000 A B R)} : Finset Var) ∪ ((syn_cxpk B B)).fv ∪
          ((syn_cfdminvalp R A B (Class.cv (nb082_alpha_dummy_000 A B R)))).fv)
        0 ∉
      R.fv
  refine NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 0 ?_
  intro u hu
  rw [Finset.mem_union]
  right
  rw [fv_syn_cfdminvalp R A B (Class.cv (nb082_alpha_dummy_000 A B R))]
  rw [Finset.mem_union]
  right
  exact hu

theorem nb082_wpp_notmem_0124 (A : Class) (B : Class) (R : Class) :
    (nb082_alpha_dummy_001 A B R) ∉ ((syn_ccnvk (syn_cfdminsep R A B))).fv := by
  simpa only [nb082_alpha_dummy_001, fv_syn_ccnvk, fv_syn_cfdminsep, Finset.mem_union,
    not_or] using
    (And.intro (And.intro (nb082_focused_notmem_0041 A B R) (nb082_focused_notmem_0000 A B R))
      (nb082_focused_notmem_0042 A B R))

theorem nb082_focused_notmem_0043 (A : Class) (B : Class) (R : Class) (p : Var) :
    (nb082_alpha_dummy_002 A B R p) ∉ A.fv :=
  by
  change
    freshVar
        (({ p } : Finset Var) ∪ ((syn_cxpk B B)).fv ∪ ((syn_cfdminvalp R A B (Class.cv p))).fv)
        0 ∉
      A.fv
  refine NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 0 ?_
  intro u hu
  rw [Finset.mem_union]
  right
  rw [fv_syn_cfdminvalp R A B (Class.cv p)]
  rw [Finset.mem_union]
  left
  rw [Finset.mem_union]
  left
  rw [Finset.mem_union]
  left
  exact hu

theorem nb082_focused_notmem_0044 (A : Class) (B : Class) (R : Class) (p : Var) :
    (nb082_alpha_dummy_002 A B R p) ∉ R.fv :=
  by
  change
    freshVar
        (({ p } : Finset Var) ∪ ((syn_cxpk B B)).fv ∪ ((syn_cfdminvalp R A B (Class.cv p))).fv)
        0 ∉
      R.fv
  refine NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 0 ?_
  intro u hu
  rw [Finset.mem_union]
  right
  rw [fv_syn_cfdminvalp R A B (Class.cv p)]
  rw [Finset.mem_union]
  right
  exact hu

theorem nb082_wpp_notmem_0125 (A : Class) (B : Class) (R : Class) (p : Var) :
    (nb082_alpha_dummy_002 A B R p) ∉ ((syn_ccnvk (syn_cfdminsep R A B))).fv := by
  simpa only [nb082_alpha_dummy_002, fv_syn_ccnvk, fv_syn_cfdminsep, Finset.mem_union,
    not_or] using
    (And.intro
      (And.intro (nb082_focused_notmem_0043 A B R p) (nb082_focused_notmem_0001 A B R p))
      (nb082_focused_notmem_0044 A B R p))

theorem nb082_focused_notmem_0045 (A : Class) (B : Class) (R : Class) :
    (nb082_alpha_dummy_000 A B R) ∉ A.fv :=
  by
  change freshVar ((R).fv ∪ (A).fv ∪ (B).fv) 0 ∉ A.fv
  exact
    NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 0
      (fun u hu => Finset.mem_union_left _ (Finset.mem_union_right _ (hu)))

theorem nb082_focused_notmem_0046 (A : Class) (B : Class) (R : Class) :
    (nb082_alpha_dummy_000 A B R) ∉ R.fv :=
  by
  change freshVar ((R).fv ∪ (A).fv ∪ (B).fv) 0 ∉ R.fv
  exact
    NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 0
      (fun u hu => Finset.mem_union_left _ (Finset.mem_union_left _ (hu)))

theorem nb082_wpp_notmem_0126 (A : Class) (B : Class) (R : Class) :
    (nb082_alpha_dummy_000 A B R) ∉ ((syn_ccnvk (syn_cfdminsep R A B))).fv := by
  simpa only [nb082_alpha_dummy_000, fv_syn_ccnvk, fv_syn_cfdminsep, Finset.mem_union,
    not_or] using
    (And.intro (And.intro (nb082_focused_notmem_0045 A B R) (nb082_focused_notmem_0002 A B R))
      (nb082_focused_notmem_0046 A B R))

theorem nb082_wpp_notmem_0127 (A : Class) (B : Class) (R : Class) (p : Var)
    (dv_A_p : p ∉ A.fv) (dv_B_p : p ∉ B.fv) (dv_R_p : p ∉ R.fv) :
    p ∉ ((syn_ccnvk (syn_cfdminsep R A B))).fv := by
  simpa only [fv_syn_ccnvk, fv_syn_cfdminsep, Finset.mem_union, not_or] using
    (And.intro (And.intro dv_A_p dv_B_p) dv_R_p)

theorem nb082_focused_notmem_0047 (A : Class) (B : Class) (R : Class) :
    (nb082_alpha_dummy_003 A B R) ∉ A.fv :=
  by
  change
    freshVar
        (({(nb082_alpha_dummy_000 A B R)} : Finset Var) ∪
            ({(nb082_alpha_dummy_001 A B R)} : Finset Var) ∪
          ((syn_wa (Wff.classMem (Class.cv (nb082_alpha_dummy_000 A B R)) (syn_cxpk B B))
              (Wff.classEq (Class.cv (nb082_alpha_dummy_001 A B R))
                (syn_cfdminvalp R A B (Class.cv (nb082_alpha_dummy_000 A B R)))))).fv)
        0 ∉
      A.fv
  refine NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 0 ?_
  intro u hu
  rw [Finset.mem_union]
  right
  rw [fv_syn_wa (Wff.classMem (Class.cv (nb082_alpha_dummy_000 A B R)) (syn_cxpk B B))
      (Wff.classEq (Class.cv (nb082_alpha_dummy_001 A B R))
        (syn_cfdminvalp R A B (Class.cv (nb082_alpha_dummy_000 A B R))))]
  rw [Finset.mem_union]
  right
  rw [fv_wff_classEq (Class.cv (nb082_alpha_dummy_001 A B R))
      (syn_cfdminvalp R A B (Class.cv (nb082_alpha_dummy_000 A B R)))]
  rw [Finset.mem_union]
  right
  rw [fv_syn_cfdminvalp R A B (Class.cv (nb082_alpha_dummy_000 A B R))]
  rw [Finset.mem_union]
  left
  rw [Finset.mem_union]
  left
  rw [Finset.mem_union]
  left
  exact hu

theorem nb082_focused_notmem_0048 (A : Class) (B : Class) (R : Class) :
    (nb082_alpha_dummy_003 A B R) ∉ R.fv :=
  by
  change
    freshVar
        (({(nb082_alpha_dummy_000 A B R)} : Finset Var) ∪
            ({(nb082_alpha_dummy_001 A B R)} : Finset Var) ∪
          ((syn_wa (Wff.classMem (Class.cv (nb082_alpha_dummy_000 A B R)) (syn_cxpk B B))
              (Wff.classEq (Class.cv (nb082_alpha_dummy_001 A B R))
                (syn_cfdminvalp R A B (Class.cv (nb082_alpha_dummy_000 A B R)))))).fv)
        0 ∉
      R.fv
  refine NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 0 ?_
  intro u hu
  rw [Finset.mem_union]
  right
  rw [fv_syn_wa (Wff.classMem (Class.cv (nb082_alpha_dummy_000 A B R)) (syn_cxpk B B))
      (Wff.classEq (Class.cv (nb082_alpha_dummy_001 A B R))
        (syn_cfdminvalp R A B (Class.cv (nb082_alpha_dummy_000 A B R))))]
  rw [Finset.mem_union]
  right
  rw [fv_wff_classEq (Class.cv (nb082_alpha_dummy_001 A B R))
      (syn_cfdminvalp R A B (Class.cv (nb082_alpha_dummy_000 A B R)))]
  rw [Finset.mem_union]
  right
  rw [fv_syn_cfdminvalp R A B (Class.cv (nb082_alpha_dummy_000 A B R))]
  rw [Finset.mem_union]
  right
  exact hu

theorem nb082_wpp_notmem_0128 (A : Class) (B : Class) (R : Class) :
    (nb082_alpha_dummy_003 A B R) ∉ ((syn_ccnvk (syn_cfdminsep R A B))).fv := by
  simpa only [nb082_alpha_dummy_003, fv_syn_ccnvk, fv_syn_cfdminsep, Finset.mem_union,
    not_or] using
    (And.intro (And.intro (nb082_focused_notmem_0047 A B R) (nb082_focused_notmem_0003 A B R))
      (nb082_focused_notmem_0048 A B R))

theorem nb082_focused_notmem_0049 (A : Class) (B : Class) (R : Class) (p : Var) :
    (nb082_alpha_dummy_004 A B R p) ∉ A.fv :=
  by
  change
    freshVar
        (({ p } : Finset Var) ∪ ({(nb082_alpha_dummy_002 A B R p)} : Finset Var) ∪
          ((syn_wa (Wff.classMem (Class.cv p) (syn_cxpk B B))
              (Wff.classEq (Class.cv (nb082_alpha_dummy_002 A B R p))
                (syn_cfdminvalp R A B (Class.cv p))))).fv)
        0 ∉
      A.fv
  refine NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 0 ?_
  intro u hu
  rw [Finset.mem_union]
  right
  rw [fv_syn_wa (Wff.classMem (Class.cv p) (syn_cxpk B B))
      (Wff.classEq (Class.cv (nb082_alpha_dummy_002 A B R p))
        (syn_cfdminvalp R A B (Class.cv p)))]
  rw [Finset.mem_union]
  right
  rw [fv_wff_classEq (Class.cv (nb082_alpha_dummy_002 A B R p))
      (syn_cfdminvalp R A B (Class.cv p))]
  rw [Finset.mem_union]
  right
  rw [fv_syn_cfdminvalp R A B (Class.cv p)]
  rw [Finset.mem_union]
  left
  rw [Finset.mem_union]
  left
  rw [Finset.mem_union]
  left
  exact hu

theorem nb082_focused_notmem_0050 (A : Class) (B : Class) (R : Class) (p : Var) :
    (nb082_alpha_dummy_004 A B R p) ∉ R.fv :=
  by
  change
    freshVar
        (({ p } : Finset Var) ∪ ({(nb082_alpha_dummy_002 A B R p)} : Finset Var) ∪
          ((syn_wa (Wff.classMem (Class.cv p) (syn_cxpk B B))
              (Wff.classEq (Class.cv (nb082_alpha_dummy_002 A B R p))
                (syn_cfdminvalp R A B (Class.cv p))))).fv)
        0 ∉
      R.fv
  refine NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 0 ?_
  intro u hu
  rw [Finset.mem_union]
  right
  rw [fv_syn_wa (Wff.classMem (Class.cv p) (syn_cxpk B B))
      (Wff.classEq (Class.cv (nb082_alpha_dummy_002 A B R p))
        (syn_cfdminvalp R A B (Class.cv p)))]
  rw [Finset.mem_union]
  right
  rw [fv_wff_classEq (Class.cv (nb082_alpha_dummy_002 A B R p))
      (syn_cfdminvalp R A B (Class.cv p))]
  rw [Finset.mem_union]
  right
  rw [fv_syn_cfdminvalp R A B (Class.cv p)]
  rw [Finset.mem_union]
  right
  exact hu

theorem nb082_wpp_notmem_0129 (A : Class) (B : Class) (R : Class) (p : Var) :
    (nb082_alpha_dummy_004 A B R p) ∉ ((syn_ccnvk (syn_cfdminsep R A B))).fv := by
  simpa only [nb082_alpha_dummy_004, fv_syn_ccnvk, fv_syn_cfdminsep, Finset.mem_union,
    not_or] using
    (And.intro
      (And.intro (nb082_focused_notmem_0049 A B R p) (nb082_focused_notmem_0004 A B R p))
      (nb082_focused_notmem_0050 A B R p))

theorem nb082_compact_envfresh_0008 (A : Class) (B : Class) (R : Class) (p : Var)
    (dv_A_p : p ∉ A.fv) (dv_B_p : p ∉ B.fv) (dv_R_p : p ∉ R.fv) :
    TEnvFresh
      [((nb082_alpha_dummy_050 A B R), (nb082_alpha_dummy_052 A B R p)),
        ((nb082_alpha_dummy_049 A B R), (nb082_alpha_dummy_051 A B R p)),
        ((nb082_alpha_dummy_047 A B R), (nb082_alpha_dummy_048 A B R p)),
        ((nb082_alpha_dummy_045 A B R), (nb082_alpha_dummy_046 A B R p)),
        ((nb082_alpha_dummy_042 A B R), (nb082_alpha_dummy_044 A B R p)),
        ((nb082_alpha_dummy_041 A B R), (nb082_alpha_dummy_043 A B R p)),
        ((nb082_alpha_dummy_001 A B R), (nb082_alpha_dummy_002 A B R p)),
        ((nb082_alpha_dummy_000 A B R), p),
        ((nb082_alpha_dummy_003 A B R), (nb082_alpha_dummy_004 A B R p))]
      ((syn_ccnvk (syn_cfdminsep R A B))).fv :=
  by
  exact
    (TEnvFresh.consFresh (nb082_alpha_dummy_050 A B R) (nb082_alpha_dummy_052 A B R p)
      (nb082_wpp_notmem_0112 A B R) (nb082_wpp_notmem_0113 A B R p)
      (TEnvFresh.consFresh (nb082_alpha_dummy_049 A B R) (nb082_alpha_dummy_051 A B R p)
        (nb082_wpp_notmem_0114 A B R) (nb082_wpp_notmem_0115 A B R p)
        (TEnvFresh.consFresh (nb082_alpha_dummy_047 A B R) (nb082_alpha_dummy_048 A B R p)
          (nb082_wpp_notmem_0116 A B R) (nb082_wpp_notmem_0117 A B R p)
          (TEnvFresh.consFresh (nb082_alpha_dummy_045 A B R)
            (nb082_alpha_dummy_046 A B R p) (nb082_wpp_notmem_0118 A B R)
            (nb082_wpp_notmem_0119 A B R p) (TEnvFresh.consFresh (nb082_alpha_dummy_042 A B R)
              (nb082_alpha_dummy_044 A B R p) (nb082_wpp_notmem_0120 A B R)
              (nb082_wpp_notmem_0121 A B R p) (TEnvFresh.consFresh (nb082_alpha_dummy_041 A B R)
                (nb082_alpha_dummy_043 A B R p) (nb082_wpp_notmem_0122 A B R)
                (nb082_wpp_notmem_0123 A B R p)
                (TEnvFresh.consFresh (nb082_alpha_dummy_001 A B R)
                  (nb082_alpha_dummy_002 A B R p) (nb082_wpp_notmem_0124 A B R)
                  (nb082_wpp_notmem_0125 A B R p)
                  (TEnvFresh.consFresh (nb082_alpha_dummy_000 A B R) p
                    (nb082_wpp_notmem_0126 A B R)
                    (nb082_wpp_notmem_0127 A B R p dv_A_p dv_B_p dv_R_p)
                    (TEnvFresh.consFresh (nb082_alpha_dummy_003 A B R)
                      (nb082_alpha_dummy_004 A B R p) (nb082_wpp_notmem_0128 A B R)
                      (nb082_wpp_notmem_0129 A B R p)
                      (TEnvFresh.nil ((syn_ccnvk (syn_cfdminsep R A B))).fv))))))))))


end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired
