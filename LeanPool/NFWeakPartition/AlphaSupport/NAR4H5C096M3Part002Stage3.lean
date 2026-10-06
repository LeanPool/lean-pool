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

/-- Checked nominal proof certificate identified upstream as `nb096_wpp_refl_0007`. -/
@[expose]
noncomputable def nb096WppRefl0007 (D : Class) (R : Class) (q : Var)
    (dv_D_q : q ∉ D.fv) :
    TReflOn
      [((nb096AlphaDummy001 D R), (nb096AlphaDummy002 D R q)),
        ((nb096AlphaDummy000 D R), q),
        ((nb096AlphaDummy003 D R), (nb096AlphaDummy004 D R q))]
      ((synCpw1 (synCpw1 D))).fv :=
  TEnvFresh.reflOn (nb096_compact_envfresh_0007 D R q dv_D_q)

theorem nb096_focused_notmem_0005 (D : Class) (R : Class) :
    (nb096AlphaDummy049 D R) ∉ D.fv :=
  by
  change
    freshVar
        ((D).fv ∪ ((synCima (synCcnv (synCdif R (synCid)))
              (synCsn (synCuni (synCuni (Class.cv (nb096AlphaDummy000 D R))))))).fv)
        0 ∉
      D.fv
  exact
    NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 0
      (fun _ hu => Finset.mem_union_left _ (hu))

theorem nb096_focused_notmem_0006 (D : Class) (R : Class) (q : Var) :
    (nb096AlphaDummy050 D R q) ∉ D.fv :=
  by
  change
    freshVar
        ((D).fv ∪ ((synCima (synCcnv (synCdif R (synCid)))
              (synCsn (synCuni (synCuni (Class.cv q)))))).fv)
        0 ∉
      D.fv
  exact
    NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 0
      (fun _ hu => Finset.mem_union_left _ (hu))

theorem nb096_focused_notmem_0007 (D : Class) (R : Class) :
    (nb096AlphaDummy047 D R) ∉ D.fv :=
  by
  change
    freshVar
        (((synCnin D (synCima (synCcnv (synCdif R (synCid))) (synCsn
                  (synCuni (synCuni (Class.cv (nb096AlphaDummy000 D R)))))))).fv ∪
          ((synCnin D (synCima (synCcnv (synCdif R (synCid))) (synCsn
                  (synCuni (synCuni (Class.cv (nb096AlphaDummy000 D R)))))))).fv)
        0 ∉
      D.fv
  refine NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 0 ?_
  intro supportVariable hu
  rw [Finset.mem_union]
  left
  rw [fv_syn_cnin D
      (synCima (synCcnv (synCdif R (synCid)))
        (synCsn (synCuni (synCuni (Class.cv (nb096AlphaDummy000 D R))))))]
  rw [Finset.mem_union]
  left
  exact hu

theorem nb096_focused_notmem_0008 (D : Class) (R : Class) (q : Var) :
    (nb096AlphaDummy048 D R q) ∉ D.fv :=
  by
  change
    freshVar
        (((synCnin D (synCima (synCcnv (synCdif R (synCid)))
                (synCsn (synCuni (synCuni (Class.cv q))))))).fv ∪ ((synCnin D
              (synCima (synCcnv (synCdif R (synCid)))
                (synCsn (synCuni (synCuni (Class.cv q))))))).fv)
        0 ∉
      D.fv
  refine NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 0 ?_
  intro supportVariable hu
  rw [Finset.mem_union]
  left
  rw [fv_syn_cnin D
      (synCima (synCcnv (synCdif R (synCid))) (synCsn (synCuni (synCuni (Class.cv q)))))]
  rw [Finset.mem_union]
  left
  exact hu

theorem nb096_focused_notmem_0009 (D : Class) (R : Class) :
    (nb096AlphaDummy045 D R) ∉ D.fv :=
  by
  change
    freshVar
        (((synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn
                (synCuni (synCuni (Class.cv (nb096AlphaDummy000 D R)))))))).fv)
        0 ∉
      D.fv
  refine NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 0 ?_
  intro supportVariable hu
  rw [fv_syn_cin D
      (synCima (synCcnv (synCdif R (synCid)))
        (synCsn (synCuni (synCuni (Class.cv (nb096AlphaDummy000 D R))))))]
  rw [Finset.mem_union]
  left
  exact hu

theorem nb096_focused_notmem_0010 (D : Class) (R : Class) (q : Var) :
    (nb096AlphaDummy046 D R q) ∉ D.fv :=
  by
  change
    freshVar
        (((synCin D (synCima (synCcnv (synCdif R (synCid)))
              (synCsn (synCuni (synCuni (Class.cv q))))))).fv)
        0 ∉
      D.fv
  refine NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 0 ?_
  intro supportVariable hu
  rw [fv_syn_cin D
      (synCima (synCcnv (synCdif R (synCid))) (synCsn (synCuni (synCuni (Class.cv q)))))]
  rw [Finset.mem_union]
  left
  exact hu

theorem nb096_focused_notmem_0011 (D : Class) (R : Class) :
    (nb096AlphaDummy042 D R) ∉ D.fv :=
  by
  change
    freshVar
        (((synCen)).fv ∪ ((synCsn (synCin D (synCima (synCcnv (synCdif R (synCid)))
                  (synCsn (synCuni (synCuni (Class.cv (nb096AlphaDummy000 D R))))))))).fv)
        1 ∉
      D.fv
  refine NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 1 ?_
  intro supportVariable hu
  rw [Finset.mem_union]
  right
  rw [fv_syn_csn
      (synCin D (synCima (synCcnv (synCdif R (synCid)))
          (synCsn (synCuni (synCuni (Class.cv (nb096AlphaDummy000 D R)))))))]
  rw [fv_syn_cin D
      (synCima (synCcnv (synCdif R (synCid)))
        (synCsn (synCuni (synCuni (Class.cv (nb096AlphaDummy000 D R))))))]
  rw [Finset.mem_union]
  left
  exact hu

theorem nb096_focused_notmem_0012 (D : Class) (R : Class) (q : Var) :
    (nb096AlphaDummy044 D R q) ∉ D.fv :=
  by
  change
    freshVar
        (((synCen)).fv ∪ ((synCsn (synCin D (synCima (synCcnv (synCdif R (synCid)))
                  (synCsn (synCuni (synCuni (Class.cv q)))))))).fv)
        1 ∉
      D.fv
  refine NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 1 ?_
  intro supportVariable hu
  rw [Finset.mem_union]
  right
  rw [fv_syn_csn
      (synCin D (synCima (synCcnv (synCdif R (synCid)))
          (synCsn (synCuni (synCuni (Class.cv q))))))]
  rw [fv_syn_cin D
      (synCima (synCcnv (synCdif R (synCid))) (synCsn (synCuni (synCuni (Class.cv q)))))]
  rw [Finset.mem_union]
  left
  exact hu

theorem nb096_focused_notmem_0013 (D : Class) (R : Class) :
    (nb096AlphaDummy041 D R) ∉ D.fv :=
  by
  change
    freshVar
        (((synCen)).fv ∪ ((synCsn (synCin D (synCima (synCcnv (synCdif R (synCid)))
                  (synCsn (synCuni (synCuni (Class.cv (nb096AlphaDummy000 D R))))))))).fv)
        0 ∉
      D.fv
  refine NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 0 ?_
  intro supportVariable hu
  rw [Finset.mem_union]
  right
  rw [fv_syn_csn
      (synCin D (synCima (synCcnv (synCdif R (synCid)))
          (synCsn (synCuni (synCuni (Class.cv (nb096AlphaDummy000 D R)))))))]
  rw [fv_syn_cin D
      (synCima (synCcnv (synCdif R (synCid)))
        (synCsn (synCuni (synCuni (Class.cv (nb096AlphaDummy000 D R))))))]
  rw [Finset.mem_union]
  left
  exact hu

theorem nb096_focused_notmem_0014 (D : Class) (R : Class) (q : Var) :
    (nb096AlphaDummy043 D R q) ∉ D.fv :=
  by
  change
    freshVar
        (((synCen)).fv ∪ ((synCsn (synCin D (synCima (synCcnv (synCdif R (synCid)))
                  (synCsn (synCuni (synCuni (Class.cv q)))))))).fv)
        0 ∉
      D.fv
  refine NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 0 ?_
  intro supportVariable hu
  rw [Finset.mem_union]
  right
  rw [fv_syn_csn
      (synCin D (synCima (synCcnv (synCdif R (synCid)))
          (synCsn (synCuni (synCuni (Class.cv q))))))]
  rw [fv_syn_cin D
      (synCima (synCcnv (synCdif R (synCid))) (synCsn (synCuni (synCuni (Class.cv q)))))]
  rw [Finset.mem_union]
  left
  exact hu

theorem nb096_compact_envfresh_0008 (D : Class) (R : Class) (q : Var)
    (dv_D_q : q ∉ D.fv) :
    TEnvFresh
      [((nb096AlphaDummy049 D R), (nb096AlphaDummy050 D R q)),
        ((nb096AlphaDummy047 D R), (nb096AlphaDummy048 D R q)),
        ((nb096AlphaDummy045 D R), (nb096AlphaDummy046 D R q)),
        ((nb096AlphaDummy042 D R), (nb096AlphaDummy044 D R q)),
        ((nb096AlphaDummy041 D R), (nb096AlphaDummy043 D R q)),
        ((nb096AlphaDummy001 D R), (nb096AlphaDummy002 D R q)),
        ((nb096AlphaDummy000 D R), q),
        ((nb096AlphaDummy003 D R), (nb096AlphaDummy004 D R q))]
      D.fv :=
  by
  exact
    (TEnvFresh.consFresh (nb096AlphaDummy049 D R) (nb096AlphaDummy050 D R q)
      (nb096_focused_notmem_0005 D R) (nb096_focused_notmem_0006 D R q)
      (TEnvFresh.consFresh (nb096AlphaDummy047 D R) (nb096AlphaDummy048 D R q)
        (nb096_focused_notmem_0007 D R) (nb096_focused_notmem_0008 D R q)
        (TEnvFresh.consFresh (nb096AlphaDummy045 D R) (nb096AlphaDummy046 D R q)
          (nb096_focused_notmem_0009 D R) (nb096_focused_notmem_0010 D R q)
          (TEnvFresh.consFresh (nb096AlphaDummy042 D R) (nb096AlphaDummy044 D R q)
            (nb096_focused_notmem_0011 D R) (nb096_focused_notmem_0012 D R q)
            (TEnvFresh.consFresh (nb096AlphaDummy041 D R) (nb096AlphaDummy043 D R q)
              (nb096_focused_notmem_0013 D R) (nb096_focused_notmem_0014 D R q)
              (TEnvFresh.consFresh (nb096AlphaDummy001 D R)
                (nb096AlphaDummy002 D R q) (nb096_focused_notmem_0000 D R)
                (nb096_focused_notmem_0001 D R q)
                (TEnvFresh.consFresh (nb096AlphaDummy000 D R) q
                  (nb096_focused_notmem_0002 D R) dv_D_q
                  (TEnvFresh.consFresh (nb096AlphaDummy003 D R)
                    (nb096AlphaDummy004 D R q) (nb096_focused_notmem_0003 D R)
                    (nb096_focused_notmem_0004 D R q) (TEnvFresh.nil D.fv)))))))))


end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired
