/-
Copyright (c) 2026 Elliot Glazer and NFNotWPP contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elliot Glazer and NFNotWPP contributors
-/

module

public import LeanPool.NFWeakPartition.AlphaSupport.NAR4H5C096M3Part002Stage2


/-! NF weak partition development: NAR4H5C096M3Part002. -/


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
noncomputable def nb096_wpp_refl_0007 (D : Class) (R : Class) (q : Var)
    (dv_D_q : q ∉ D.fv) :
    TReflOn
      [((nb096_alpha_dummy_001 D R), (nb096_alpha_dummy_002 D R q)),
        ((nb096_alpha_dummy_000 D R), q),
        ((nb096_alpha_dummy_003 D R), (nb096_alpha_dummy_004 D R q))]
      ((syn_cpw1 (syn_cpw1 D))).fv :=
  TEnvFresh.reflOn (nb096_compact_envfresh_0007 D R q dv_D_q)

theorem nb096_focused_notmem_0005 (D : Class) (R : Class) :
    (nb096_alpha_dummy_049 D R) ∉ D.fv :=
  by
  change
    freshVar
        ((D).fv ∪ ((syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
              (syn_csn (syn_cuni (syn_cuni (Class.cv (nb096_alpha_dummy_000 D R))))))).fv)
        0 ∉
      D.fv
  exact
    NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 0
      (fun _ hu => Finset.mem_union_left _ (hu))

theorem nb096_focused_notmem_0006 (D : Class) (R : Class) (q : Var) :
    (nb096_alpha_dummy_050 D R q) ∉ D.fv :=
  by
  change
    freshVar
        ((D).fv ∪ ((syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
              (syn_csn (syn_cuni (syn_cuni (Class.cv q)))))).fv)
        0 ∉
      D.fv
  exact
    NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 0
      (fun _ hu => Finset.mem_union_left _ (hu))

theorem nb096_focused_notmem_0007 (D : Class) (R : Class) :
    (nb096_alpha_dummy_047 D R) ∉ D.fv :=
  by
  change
    freshVar
        (((syn_cnin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn
                  (syn_cuni (syn_cuni (Class.cv (nb096_alpha_dummy_000 D R)))))))).fv ∪
          ((syn_cnin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn
                  (syn_cuni (syn_cuni (Class.cv (nb096_alpha_dummy_000 D R)))))))).fv)
        0 ∉
      D.fv
  refine NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 0 ?_
  intro supportVariable hu
  rw [Finset.mem_union]
  left
  rw [fv_syn_cnin D
      (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
        (syn_csn (syn_cuni (syn_cuni (Class.cv (nb096_alpha_dummy_000 D R))))))]
  rw [Finset.mem_union]
  left
  exact hu

theorem nb096_focused_notmem_0008 (D : Class) (R : Class) (q : Var) :
    (nb096_alpha_dummy_048 D R q) ∉ D.fv :=
  by
  change
    freshVar
        (((syn_cnin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
                (syn_csn (syn_cuni (syn_cuni (Class.cv q))))))).fv ∪ ((syn_cnin D
              (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
                (syn_csn (syn_cuni (syn_cuni (Class.cv q))))))).fv)
        0 ∉
      D.fv
  refine NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 0 ?_
  intro supportVariable hu
  rw [Finset.mem_union]
  left
  rw [fv_syn_cnin D
      (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (syn_cuni (syn_cuni (Class.cv q)))))]
  rw [Finset.mem_union]
  left
  exact hu

theorem nb096_focused_notmem_0009 (D : Class) (R : Class) :
    (nb096_alpha_dummy_045 D R) ∉ D.fv :=
  by
  change
    freshVar
        (((syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn
                (syn_cuni (syn_cuni (Class.cv (nb096_alpha_dummy_000 D R)))))))).fv)
        0 ∉
      D.fv
  refine NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 0 ?_
  intro supportVariable hu
  rw [fv_syn_cin D
      (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
        (syn_csn (syn_cuni (syn_cuni (Class.cv (nb096_alpha_dummy_000 D R))))))]
  rw [Finset.mem_union]
  left
  exact hu

theorem nb096_focused_notmem_0010 (D : Class) (R : Class) (q : Var) :
    (nb096_alpha_dummy_046 D R q) ∉ D.fv :=
  by
  change
    freshVar
        (((syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
              (syn_csn (syn_cuni (syn_cuni (Class.cv q))))))).fv)
        0 ∉
      D.fv
  refine NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 0 ?_
  intro supportVariable hu
  rw [fv_syn_cin D
      (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (syn_cuni (syn_cuni (Class.cv q)))))]
  rw [Finset.mem_union]
  left
  exact hu

theorem nb096_focused_notmem_0011 (D : Class) (R : Class) :
    (nb096_alpha_dummy_042 D R) ∉ D.fv :=
  by
  change
    freshVar
        (((syn_cen)).fv ∪ ((syn_csn (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
                  (syn_csn (syn_cuni (syn_cuni (Class.cv (nb096_alpha_dummy_000 D R))))))))).fv)
        1 ∉
      D.fv
  refine NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 1 ?_
  intro supportVariable hu
  rw [Finset.mem_union]
  right
  rw [fv_syn_csn
      (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
          (syn_csn (syn_cuni (syn_cuni (Class.cv (nb096_alpha_dummy_000 D R)))))))]
  rw [fv_syn_cin D
      (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
        (syn_csn (syn_cuni (syn_cuni (Class.cv (nb096_alpha_dummy_000 D R))))))]
  rw [Finset.mem_union]
  left
  exact hu

theorem nb096_focused_notmem_0012 (D : Class) (R : Class) (q : Var) :
    (nb096_alpha_dummy_044 D R q) ∉ D.fv :=
  by
  change
    freshVar
        (((syn_cen)).fv ∪ ((syn_csn (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
                  (syn_csn (syn_cuni (syn_cuni (Class.cv q)))))))).fv)
        1 ∉
      D.fv
  refine NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 1 ?_
  intro supportVariable hu
  rw [Finset.mem_union]
  right
  rw [fv_syn_csn
      (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
          (syn_csn (syn_cuni (syn_cuni (Class.cv q))))))]
  rw [fv_syn_cin D
      (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (syn_cuni (syn_cuni (Class.cv q)))))]
  rw [Finset.mem_union]
  left
  exact hu

theorem nb096_focused_notmem_0013 (D : Class) (R : Class) :
    (nb096_alpha_dummy_041 D R) ∉ D.fv :=
  by
  change
    freshVar
        (((syn_cen)).fv ∪ ((syn_csn (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
                  (syn_csn (syn_cuni (syn_cuni (Class.cv (nb096_alpha_dummy_000 D R))))))))).fv)
        0 ∉
      D.fv
  refine NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 0 ?_
  intro supportVariable hu
  rw [Finset.mem_union]
  right
  rw [fv_syn_csn
      (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
          (syn_csn (syn_cuni (syn_cuni (Class.cv (nb096_alpha_dummy_000 D R)))))))]
  rw [fv_syn_cin D
      (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
        (syn_csn (syn_cuni (syn_cuni (Class.cv (nb096_alpha_dummy_000 D R))))))]
  rw [Finset.mem_union]
  left
  exact hu

theorem nb096_focused_notmem_0014 (D : Class) (R : Class) (q : Var) :
    (nb096_alpha_dummy_043 D R q) ∉ D.fv :=
  by
  change
    freshVar
        (((syn_cen)).fv ∪ ((syn_csn (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
                  (syn_csn (syn_cuni (syn_cuni (Class.cv q)))))))).fv)
        0 ∉
      D.fv
  refine NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 0 ?_
  intro supportVariable hu
  rw [Finset.mem_union]
  right
  rw [fv_syn_csn
      (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
          (syn_csn (syn_cuni (syn_cuni (Class.cv q))))))]
  rw [fv_syn_cin D
      (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (syn_cuni (syn_cuni (Class.cv q)))))]
  rw [Finset.mem_union]
  left
  exact hu

theorem nb096_compact_envfresh_0008 (D : Class) (R : Class) (q : Var)
    (dv_D_q : q ∉ D.fv) :
    TEnvFresh
      [((nb096_alpha_dummy_049 D R), (nb096_alpha_dummy_050 D R q)),
        ((nb096_alpha_dummy_047 D R), (nb096_alpha_dummy_048 D R q)),
        ((nb096_alpha_dummy_045 D R), (nb096_alpha_dummy_046 D R q)),
        ((nb096_alpha_dummy_042 D R), (nb096_alpha_dummy_044 D R q)),
        ((nb096_alpha_dummy_041 D R), (nb096_alpha_dummy_043 D R q)),
        ((nb096_alpha_dummy_001 D R), (nb096_alpha_dummy_002 D R q)),
        ((nb096_alpha_dummy_000 D R), q),
        ((nb096_alpha_dummy_003 D R), (nb096_alpha_dummy_004 D R q))]
      D.fv :=
  by
  exact
    (TEnvFresh.consFresh (nb096_alpha_dummy_049 D R) (nb096_alpha_dummy_050 D R q)
      (nb096_focused_notmem_0005 D R) (nb096_focused_notmem_0006 D R q)
      (TEnvFresh.consFresh (nb096_alpha_dummy_047 D R) (nb096_alpha_dummy_048 D R q)
        (nb096_focused_notmem_0007 D R) (nb096_focused_notmem_0008 D R q)
        (TEnvFresh.consFresh (nb096_alpha_dummy_045 D R) (nb096_alpha_dummy_046 D R q)
          (nb096_focused_notmem_0009 D R) (nb096_focused_notmem_0010 D R q)
          (TEnvFresh.consFresh (nb096_alpha_dummy_042 D R) (nb096_alpha_dummy_044 D R q)
            (nb096_focused_notmem_0011 D R) (nb096_focused_notmem_0012 D R q)
            (TEnvFresh.consFresh (nb096_alpha_dummy_041 D R) (nb096_alpha_dummy_043 D R q)
              (nb096_focused_notmem_0013 D R) (nb096_focused_notmem_0014 D R q)
              (TEnvFresh.consFresh (nb096_alpha_dummy_001 D R)
                (nb096_alpha_dummy_002 D R q) (nb096_focused_notmem_0000 D R)
                (nb096_focused_notmem_0001 D R q)
                (TEnvFresh.consFresh (nb096_alpha_dummy_000 D R) q
                  (nb096_focused_notmem_0002 D R) dv_D_q
                  (TEnvFresh.consFresh (nb096_alpha_dummy_003 D R)
                    (nb096_alpha_dummy_004 D R q) (nb096_focused_notmem_0003 D R)
                    (nb096_focused_notmem_0004 D R q) (TEnvFresh.nil D.fv)))))))))


end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired
