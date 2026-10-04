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
    (nb082AlphaDummy043 A B R p) ∉ B.fv :=
  by
  change
    freshVar
        (((synCin (synCimak (synCcnvk (synCfdminsep R A B)) (synCsn (Class.cv p)))
            (synC1c))).fv)
        0 ∉
      B.fv
  refine NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 0 ?_
  intro u hu
  rw [fv_syn_cin (synCimak (synCcnvk (synCfdminsep R A B)) (synCsn (Class.cv p)))
      (synC1c)]
  rw [Finset.mem_union]
  left
  rw [fv_syn_cimak (synCcnvk (synCfdminsep R A B)) (synCsn (Class.cv p))]
  rw [Finset.mem_union]
  left
  rw [fv_syn_ccnvk (synCfdminsep R A B)]
  rw [fv_syn_cfdminsep R A B]
  rw [Finset.mem_union]
  left
  rw [Finset.mem_union]
  right
  exact hu

theorem nb082_focused_notmem_0040 (A : Class) (B : Class) (R : Class) (p : Var) :
    (nb082AlphaDummy043 A B R p) ∉ R.fv :=
  by
  change
    freshVar
        (((synCin (synCimak (synCcnvk (synCfdminsep R A B)) (synCsn (Class.cv p)))
            (synC1c))).fv)
        0 ∉
      R.fv
  refine NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 0 ?_
  intro u hu
  rw [fv_syn_cin (synCimak (synCcnvk (synCfdminsep R A B)) (synCsn (Class.cv p)))
      (synC1c)]
  rw [Finset.mem_union]
  left
  rw [fv_syn_cimak (synCcnvk (synCfdminsep R A B)) (synCsn (Class.cv p))]
  rw [Finset.mem_union]
  left
  rw [fv_syn_ccnvk (synCfdminsep R A B)]
  rw [fv_syn_cfdminsep R A B]
  rw [Finset.mem_union]
  right
  exact hu

theorem nb082_wpp_notmem_0123 (A : Class) (B : Class) (R : Class) (p : Var) :
    (nb082AlphaDummy043 A B R p) ∉ ((synCcnvk (synCfdminsep R A B))).fv := by
  simpa only [nb082AlphaDummy043, fv_syn_ccnvk, fv_syn_cfdminsep, Finset.mem_union,
    not_or] using
    (And.intro
      (And.intro (nb082_focused_notmem_0038 A B R p) (nb082_focused_notmem_0039 A B R p))
      (nb082_focused_notmem_0040 A B R p))

theorem nb082_focused_notmem_0041 (A : Class) (B : Class) (R : Class) :
    (nb082AlphaDummy001 A B R) ∉ A.fv :=
  by
  change
    freshVar
        (({(nb082AlphaDummy000 A B R)} : Finset Var) ∪ ((synCxpk B B)).fv ∪
          ((synCfdminvalp R A B (Class.cv (nb082AlphaDummy000 A B R)))).fv)
        0 ∉
      A.fv
  refine NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 0 ?_
  intro u hu
  rw [Finset.mem_union]
  right
  rw [fv_syn_cfdminvalp R A B (Class.cv (nb082AlphaDummy000 A B R))]
  rw [Finset.mem_union]
  left
  rw [Finset.mem_union]
  left
  rw [Finset.mem_union]
  left
  exact hu

theorem nb082_focused_notmem_0042 (A : Class) (B : Class) (R : Class) :
    (nb082AlphaDummy001 A B R) ∉ R.fv :=
  by
  change
    freshVar
        (({(nb082AlphaDummy000 A B R)} : Finset Var) ∪ ((synCxpk B B)).fv ∪
          ((synCfdminvalp R A B (Class.cv (nb082AlphaDummy000 A B R)))).fv)
        0 ∉
      R.fv
  refine NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 0 ?_
  intro u hu
  rw [Finset.mem_union]
  right
  rw [fv_syn_cfdminvalp R A B (Class.cv (nb082AlphaDummy000 A B R))]
  rw [Finset.mem_union]
  right
  exact hu

theorem nb082_wpp_notmem_0124 (A : Class) (B : Class) (R : Class) :
    (nb082AlphaDummy001 A B R) ∉ ((synCcnvk (synCfdminsep R A B))).fv := by
  simpa only [nb082AlphaDummy001, fv_syn_ccnvk, fv_syn_cfdminsep, Finset.mem_union,
    not_or] using
    (And.intro (And.intro (nb082_focused_notmem_0041 A B R) (nb082_focused_notmem_0000 A B R))
      (nb082_focused_notmem_0042 A B R))

theorem nb082_focused_notmem_0043 (A : Class) (B : Class) (R : Class) (p : Var) :
    (nb082AlphaDummy002 A B R p) ∉ A.fv :=
  by
  change
    freshVar
        (({ p } : Finset Var) ∪ ((synCxpk B B)).fv ∪ ((synCfdminvalp R A B (Class.cv p))).fv)
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
    (nb082AlphaDummy002 A B R p) ∉ R.fv :=
  by
  change
    freshVar
        (({ p } : Finset Var) ∪ ((synCxpk B B)).fv ∪ ((synCfdminvalp R A B (Class.cv p))).fv)
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
    (nb082AlphaDummy002 A B R p) ∉ ((synCcnvk (synCfdminsep R A B))).fv := by
  simpa only [nb082AlphaDummy002, fv_syn_ccnvk, fv_syn_cfdminsep, Finset.mem_union,
    not_or] using
    (And.intro
      (And.intro (nb082_focused_notmem_0043 A B R p) (nb082_focused_notmem_0001 A B R p))
      (nb082_focused_notmem_0044 A B R p))

theorem nb082_focused_notmem_0045 (A : Class) (B : Class) (R : Class) :
    (nb082AlphaDummy000 A B R) ∉ A.fv :=
  by
  change freshVar ((R).fv ∪ (A).fv ∪ (B).fv) 0 ∉ A.fv
  exact
    NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 0
      (fun u hu => Finset.mem_union_left _ (Finset.mem_union_right _ (hu)))

theorem nb082_focused_notmem_0046 (A : Class) (B : Class) (R : Class) :
    (nb082AlphaDummy000 A B R) ∉ R.fv :=
  by
  change freshVar ((R).fv ∪ (A).fv ∪ (B).fv) 0 ∉ R.fv
  exact
    NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 0
      (fun u hu => Finset.mem_union_left _ (Finset.mem_union_left _ (hu)))

theorem nb082_wpp_notmem_0126 (A : Class) (B : Class) (R : Class) :
    (nb082AlphaDummy000 A B R) ∉ ((synCcnvk (synCfdminsep R A B))).fv := by
  simpa only [nb082AlphaDummy000, fv_syn_ccnvk, fv_syn_cfdminsep, Finset.mem_union,
    not_or] using
    (And.intro (And.intro (nb082_focused_notmem_0045 A B R) (nb082_focused_notmem_0002 A B R))
      (nb082_focused_notmem_0046 A B R))

theorem nb082_wpp_notmem_0127 (A : Class) (B : Class) (R : Class) (p : Var)
    (dv_A_p : p ∉ A.fv) (dv_B_p : p ∉ B.fv) (dv_R_p : p ∉ R.fv) :
    p ∉ ((synCcnvk (synCfdminsep R A B))).fv := by
  simpa only [fv_syn_ccnvk, fv_syn_cfdminsep, Finset.mem_union, not_or] using
    (And.intro (And.intro dv_A_p dv_B_p) dv_R_p)

theorem nb082_focused_notmem_0047 (A : Class) (B : Class) (R : Class) :
    (nb082AlphaDummy003 A B R) ∉ A.fv :=
  by
  change
    freshVar
        (({(nb082AlphaDummy000 A B R)} : Finset Var) ∪
            ({(nb082AlphaDummy001 A B R)} : Finset Var) ∪
          ((synWa (Wff.classMem (Class.cv (nb082AlphaDummy000 A B R)) (synCxpk B B))
              (Wff.classEq (Class.cv (nb082AlphaDummy001 A B R))
                (synCfdminvalp R A B (Class.cv (nb082AlphaDummy000 A B R)))))).fv)
        0 ∉
      A.fv
  refine NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 0 ?_
  intro u hu
  rw [Finset.mem_union]
  right
  rw [fv_syn_wa (Wff.classMem (Class.cv (nb082AlphaDummy000 A B R)) (synCxpk B B))
      (Wff.classEq (Class.cv (nb082AlphaDummy001 A B R))
        (synCfdminvalp R A B (Class.cv (nb082AlphaDummy000 A B R))))]
  rw [Finset.mem_union]
  right
  rw [fv_wff_classEq (Class.cv (nb082AlphaDummy001 A B R))
      (synCfdminvalp R A B (Class.cv (nb082AlphaDummy000 A B R)))]
  rw [Finset.mem_union]
  right
  rw [fv_syn_cfdminvalp R A B (Class.cv (nb082AlphaDummy000 A B R))]
  rw [Finset.mem_union]
  left
  rw [Finset.mem_union]
  left
  rw [Finset.mem_union]
  left
  exact hu

theorem nb082_focused_notmem_0048 (A : Class) (B : Class) (R : Class) :
    (nb082AlphaDummy003 A B R) ∉ R.fv :=
  by
  change
    freshVar
        (({(nb082AlphaDummy000 A B R)} : Finset Var) ∪
            ({(nb082AlphaDummy001 A B R)} : Finset Var) ∪
          ((synWa (Wff.classMem (Class.cv (nb082AlphaDummy000 A B R)) (synCxpk B B))
              (Wff.classEq (Class.cv (nb082AlphaDummy001 A B R))
                (synCfdminvalp R A B (Class.cv (nb082AlphaDummy000 A B R)))))).fv)
        0 ∉
      R.fv
  refine NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 0 ?_
  intro u hu
  rw [Finset.mem_union]
  right
  rw [fv_syn_wa (Wff.classMem (Class.cv (nb082AlphaDummy000 A B R)) (synCxpk B B))
      (Wff.classEq (Class.cv (nb082AlphaDummy001 A B R))
        (synCfdminvalp R A B (Class.cv (nb082AlphaDummy000 A B R))))]
  rw [Finset.mem_union]
  right
  rw [fv_wff_classEq (Class.cv (nb082AlphaDummy001 A B R))
      (synCfdminvalp R A B (Class.cv (nb082AlphaDummy000 A B R)))]
  rw [Finset.mem_union]
  right
  rw [fv_syn_cfdminvalp R A B (Class.cv (nb082AlphaDummy000 A B R))]
  rw [Finset.mem_union]
  right
  exact hu

theorem nb082_wpp_notmem_0128 (A : Class) (B : Class) (R : Class) :
    (nb082AlphaDummy003 A B R) ∉ ((synCcnvk (synCfdminsep R A B))).fv := by
  simpa only [nb082AlphaDummy003, fv_syn_ccnvk, fv_syn_cfdminsep, Finset.mem_union,
    not_or] using
    (And.intro (And.intro (nb082_focused_notmem_0047 A B R) (nb082_focused_notmem_0003 A B R))
      (nb082_focused_notmem_0048 A B R))

theorem nb082_focused_notmem_0049 (A : Class) (B : Class) (R : Class) (p : Var) :
    (nb082AlphaDummy004 A B R p) ∉ A.fv :=
  by
  change
    freshVar
        (({ p } : Finset Var) ∪ ({(nb082AlphaDummy002 A B R p)} : Finset Var) ∪
          ((synWa (Wff.classMem (Class.cv p) (synCxpk B B))
              (Wff.classEq (Class.cv (nb082AlphaDummy002 A B R p))
                (synCfdminvalp R A B (Class.cv p))))).fv)
        0 ∉
      A.fv
  refine NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 0 ?_
  intro u hu
  rw [Finset.mem_union]
  right
  rw [fv_syn_wa (Wff.classMem (Class.cv p) (synCxpk B B))
      (Wff.classEq (Class.cv (nb082AlphaDummy002 A B R p))
        (synCfdminvalp R A B (Class.cv p)))]
  rw [Finset.mem_union]
  right
  rw [fv_wff_classEq (Class.cv (nb082AlphaDummy002 A B R p))
      (synCfdminvalp R A B (Class.cv p))]
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
    (nb082AlphaDummy004 A B R p) ∉ R.fv :=
  by
  change
    freshVar
        (({ p } : Finset Var) ∪ ({(nb082AlphaDummy002 A B R p)} : Finset Var) ∪
          ((synWa (Wff.classMem (Class.cv p) (synCxpk B B))
              (Wff.classEq (Class.cv (nb082AlphaDummy002 A B R p))
                (synCfdminvalp R A B (Class.cv p))))).fv)
        0 ∉
      R.fv
  refine NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 0 ?_
  intro u hu
  rw [Finset.mem_union]
  right
  rw [fv_syn_wa (Wff.classMem (Class.cv p) (synCxpk B B))
      (Wff.classEq (Class.cv (nb082AlphaDummy002 A B R p))
        (synCfdminvalp R A B (Class.cv p)))]
  rw [Finset.mem_union]
  right
  rw [fv_wff_classEq (Class.cv (nb082AlphaDummy002 A B R p))
      (synCfdminvalp R A B (Class.cv p))]
  rw [Finset.mem_union]
  right
  rw [fv_syn_cfdminvalp R A B (Class.cv p)]
  rw [Finset.mem_union]
  right
  exact hu

theorem nb082_wpp_notmem_0129 (A : Class) (B : Class) (R : Class) (p : Var) :
    (nb082AlphaDummy004 A B R p) ∉ ((synCcnvk (synCfdminsep R A B))).fv := by
  simpa only [nb082AlphaDummy004, fv_syn_ccnvk, fv_syn_cfdminsep, Finset.mem_union,
    not_or] using
    (And.intro
      (And.intro (nb082_focused_notmem_0049 A B R p) (nb082_focused_notmem_0004 A B R p))
      (nb082_focused_notmem_0050 A B R p))

theorem nb082_compact_envfresh_0008 (A : Class) (B : Class) (R : Class) (p : Var)
    (dv_A_p : p ∉ A.fv) (dv_B_p : p ∉ B.fv) (dv_R_p : p ∉ R.fv) :
    TEnvFresh
      [((nb082AlphaDummy050 A B R), (nb082AlphaDummy052 A B R p)),
        ((nb082AlphaDummy049 A B R), (nb082AlphaDummy051 A B R p)),
        ((nb082AlphaDummy047 A B R), (nb082AlphaDummy048 A B R p)),
        ((nb082AlphaDummy045 A B R), (nb082AlphaDummy046 A B R p)),
        ((nb082AlphaDummy042 A B R), (nb082AlphaDummy044 A B R p)),
        ((nb082AlphaDummy041 A B R), (nb082AlphaDummy043 A B R p)),
        ((nb082AlphaDummy001 A B R), (nb082AlphaDummy002 A B R p)),
        ((nb082AlphaDummy000 A B R), p),
        ((nb082AlphaDummy003 A B R), (nb082AlphaDummy004 A B R p))]
      ((synCcnvk (synCfdminsep R A B))).fv :=
  by
  exact
    (TEnvFresh.consFresh (nb082AlphaDummy050 A B R) (nb082AlphaDummy052 A B R p)
      (nb082_wpp_notmem_0112 A B R) (nb082_wpp_notmem_0113 A B R p)
      (TEnvFresh.consFresh (nb082AlphaDummy049 A B R) (nb082AlphaDummy051 A B R p)
        (nb082_wpp_notmem_0114 A B R) (nb082_wpp_notmem_0115 A B R p)
        (TEnvFresh.consFresh (nb082AlphaDummy047 A B R) (nb082AlphaDummy048 A B R p)
          (nb082_wpp_notmem_0116 A B R) (nb082_wpp_notmem_0117 A B R p)
          (TEnvFresh.consFresh (nb082AlphaDummy045 A B R)
            (nb082AlphaDummy046 A B R p) (nb082_wpp_notmem_0118 A B R)
            (nb082_wpp_notmem_0119 A B R p) (TEnvFresh.consFresh (nb082AlphaDummy042 A B R)
              (nb082AlphaDummy044 A B R p) (nb082_wpp_notmem_0120 A B R)
              (nb082_wpp_notmem_0121 A B R p) (TEnvFresh.consFresh (nb082AlphaDummy041 A B R)
                (nb082AlphaDummy043 A B R p) (nb082_wpp_notmem_0122 A B R)
                (nb082_wpp_notmem_0123 A B R p)
                (TEnvFresh.consFresh (nb082AlphaDummy001 A B R)
                  (nb082AlphaDummy002 A B R p) (nb082_wpp_notmem_0124 A B R)
                  (nb082_wpp_notmem_0125 A B R p)
                  (TEnvFresh.consFresh (nb082AlphaDummy000 A B R) p
                    (nb082_wpp_notmem_0126 A B R)
                    (nb082_wpp_notmem_0127 A B R p dv_A_p dv_B_p dv_R_p)
                    (TEnvFresh.consFresh (nb082AlphaDummy003 A B R)
                      (nb082AlphaDummy004 A B R p) (nb082_wpp_notmem_0128 A B R)
                      (nb082_wpp_notmem_0129 A B R p)
                      (TEnvFresh.nil ((synCcnvk (synCfdminsep R A B))).fv))))))))))


end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired
