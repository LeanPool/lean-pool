/-
Copyright (c) 2026 Elliot Glazer and NFNotWPP contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elliot Glazer and NFNotWPP contributors
-/

module

public import LeanPool.NFWeakPartition.NAR4H5C091M3BPart005

/-! NF weak partition development: NAR4H5C091M3BPart006. -/


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

theorem nb091_focused_notmem_0064 (D : Class) (R : Class) :
    (nb091AlphaDummy060 D R) ∉ R.fv :=
  by
  change
    freshVar
        (((synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn
                  (synCuni (synCuni (Class.cv (nb091AlphaDummy000 D R)))))))).fv ∪
          ((synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn
                  (synCuni (synCuni (Class.cv (nb091AlphaDummy000 D R)))))))).fv)
        1 ∉
      R.fv
  refine NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 1 ?_
  intro supportVariable hu
  rw [Finset.mem_union]
  left
  rw [fv_syn_cin D
      (synCima (synCcnv (synCdif R (synCid)))
        (synCsn (synCuni (synCuni (Class.cv (nb091AlphaDummy000 D R))))))]
  rw [Finset.mem_union]
  right
  rw [fv_syn_cima (synCcnv (synCdif R (synCid)))
      (synCsn (synCuni (synCuni (Class.cv (nb091AlphaDummy000 D R)))))]
  rw [Finset.mem_union]
  left
  rw [fv_syn_ccnv (synCdif R (synCid))]
  rw [fv_syn_cdif R (synCid)]
  rw [Finset.mem_union]
  left
  exact hu

theorem nb091_wpp_notmem_0412 (D : Class) (R : Class) :
    (nb091AlphaDummy060 D R) ∉ ((synCcnv (synCdif R (synCid)))).fv := by
  simpa only [nb091AlphaDummy060, fv_syn_ccnv, fv_syn_cdif, Finset.mem_union,
    fv_syn_cid, not_or] using
    (And.intro (nb091_focused_notmem_0064 D R) (nb091_compact_fv_empty_0052 D R))

theorem nb091_focused_notmem_0065 (D : Class) (R : Class) (p : Var) :
    (nb091AlphaDummy062 D R p) ∉ R.fv :=
  by
  change
    freshVar
        (((synCin D (synCima (synCcnv (synCdif R (synCid)))
                (synCsn (synCuni (synCuni (Class.cv p))))))).fv ∪ ((synCin D
              (synCima (synCcnv (synCdif R (synCid)))
                (synCsn (synCuni (synCuni (Class.cv p))))))).fv)
        1 ∉
      R.fv
  refine NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 1 ?_
  intro supportVariable hu
  rw [Finset.mem_union]
  left
  rw [fv_syn_cin D
      (synCima (synCcnv (synCdif R (synCid))) (synCsn (synCuni (synCuni (Class.cv p)))))]
  rw [Finset.mem_union]
  right
  rw [fv_syn_cima (synCcnv (synCdif R (synCid)))
      (synCsn (synCuni (synCuni (Class.cv p))))]
  rw [Finset.mem_union]
  left
  rw [fv_syn_ccnv (synCdif R (synCid))]
  rw [fv_syn_cdif R (synCid)]
  rw [Finset.mem_union]
  left
  exact hu

theorem nb091_wpp_notmem_0413 (D : Class) (R : Class) (p : Var) :
    (nb091AlphaDummy062 D R p) ∉ ((synCcnv (synCdif R (synCid)))).fv := by
  simpa only [nb091AlphaDummy062, fv_syn_ccnv, fv_syn_cdif, Finset.mem_union,
    fv_syn_cid, not_or] using
    (And.intro (nb091_focused_notmem_0065 D R p) (nb091_compact_fv_empty_0053 D R p))

theorem nb091_focused_notmem_0066 (D : Class) (R : Class) :
    (nb091AlphaDummy059 D R) ∉ R.fv :=
  by
  change
    freshVar
        (((synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn
                  (synCuni (synCuni (Class.cv (nb091AlphaDummy000 D R)))))))).fv ∪
          ((synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn
                  (synCuni (synCuni (Class.cv (nb091AlphaDummy000 D R)))))))).fv)
        0 ∉
      R.fv
  refine NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 0 ?_
  intro supportVariable hu
  rw [Finset.mem_union]
  left
  rw [fv_syn_cin D
      (synCima (synCcnv (synCdif R (synCid)))
        (synCsn (synCuni (synCuni (Class.cv (nb091AlphaDummy000 D R))))))]
  rw [Finset.mem_union]
  right
  rw [fv_syn_cima (synCcnv (synCdif R (synCid)))
      (synCsn (synCuni (synCuni (Class.cv (nb091AlphaDummy000 D R)))))]
  rw [Finset.mem_union]
  left
  rw [fv_syn_ccnv (synCdif R (synCid))]
  rw [fv_syn_cdif R (synCid)]
  rw [Finset.mem_union]
  left
  exact hu

theorem nb091_wpp_notmem_0414 (D : Class) (R : Class) :
    (nb091AlphaDummy059 D R) ∉ ((synCcnv (synCdif R (synCid)))).fv := by
  simpa only [nb091AlphaDummy059, fv_syn_ccnv, fv_syn_cdif, Finset.mem_union,
    fv_syn_cid, not_or] using
    (And.intro (nb091_focused_notmem_0066 D R) (nb091_compact_fv_empty_0054 D R))

theorem nb091_focused_notmem_0067 (D : Class) (R : Class) (p : Var) :
    (nb091AlphaDummy061 D R p) ∉ R.fv :=
  by
  change
    freshVar
        (((synCin D (synCima (synCcnv (synCdif R (synCid)))
                (synCsn (synCuni (synCuni (Class.cv p))))))).fv ∪ ((synCin D
              (synCima (synCcnv (synCdif R (synCid)))
                (synCsn (synCuni (synCuni (Class.cv p))))))).fv)
        0 ∉
      R.fv
  refine NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 0 ?_
  intro supportVariable hu
  rw [Finset.mem_union]
  left
  rw [fv_syn_cin D
      (synCima (synCcnv (synCdif R (synCid))) (synCsn (synCuni (synCuni (Class.cv p)))))]
  rw [Finset.mem_union]
  right
  rw [fv_syn_cima (synCcnv (synCdif R (synCid)))
      (synCsn (synCuni (synCuni (Class.cv p))))]
  rw [Finset.mem_union]
  left
  rw [fv_syn_ccnv (synCdif R (synCid))]
  rw [fv_syn_cdif R (synCid)]
  rw [Finset.mem_union]
  left
  exact hu

theorem nb091_wpp_notmem_0415 (D : Class) (R : Class) (p : Var) :
    (nb091AlphaDummy061 D R p) ∉ ((synCcnv (synCdif R (synCid)))).fv := by
  simpa only [nb091AlphaDummy061, fv_syn_ccnv, fv_syn_cdif, Finset.mem_union,
    fv_syn_cid, not_or] using
    (And.intro (nb091_focused_notmem_0067 D R p) (nb091_compact_fv_empty_0055 D R p))

theorem nb091_focused_notmem_0068 (D : Class) (R : Class) :
    (nb091AlphaDummy063 D R) ∉ R.fv :=
  by
  change
    freshVar
        (({(nb091AlphaDummy059 D R)} : Finset Var) ∪
            ({(nb091AlphaDummy060 D R)} : Finset Var) ∪ ((synWa
              (Wff.classMem (Class.cv (nb091AlphaDummy059 D R)) (synCin D
                  (synCima (synCcnv (synCdif R (synCid))) (synCsn
                      (synCuni (synCuni (Class.cv (nb091AlphaDummy000 D R))))))))
              (Wff.classMem (Class.cv (nb091AlphaDummy060 D R)) (synCin D
                  (synCima (synCcnv (synCdif R (synCid))) (synCsn (synCuni
                        (synCuni (Class.cv (nb091AlphaDummy000 D R)))))))))).fv)
        0 ∉
      R.fv
  refine NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 0 ?_
  intro supportVariable hu
  rw [Finset.mem_union]
  right
  rw [fv_syn_wa
      (Wff.classMem (Class.cv (nb091AlphaDummy059 D R)) (synCin D
          (synCima (synCcnv (synCdif R (synCid)))
            (synCsn (synCuni (synCuni (Class.cv (nb091AlphaDummy000 D R))))))))
      (Wff.classMem (Class.cv (nb091AlphaDummy060 D R)) (synCin D
          (synCima (synCcnv (synCdif R (synCid)))
            (synCsn (synCuni (synCuni (Class.cv (nb091AlphaDummy000 D R))))))))]
  rw [Finset.mem_union]
  left
  rw [fv_wff_classMem (Class.cv (nb091AlphaDummy059 D R))
      (synCin D (synCima (synCcnv (synCdif R (synCid)))
          (synCsn (synCuni (synCuni (Class.cv (nb091AlphaDummy000 D R)))))))]
  rw [Finset.mem_union]
  right
  rw [fv_syn_cin D
      (synCima (synCcnv (synCdif R (synCid)))
        (synCsn (synCuni (synCuni (Class.cv (nb091AlphaDummy000 D R))))))]
  rw [Finset.mem_union]
  right
  rw [fv_syn_cima (synCcnv (synCdif R (synCid)))
      (synCsn (synCuni (synCuni (Class.cv (nb091AlphaDummy000 D R)))))]
  rw [Finset.mem_union]
  left
  rw [fv_syn_ccnv (synCdif R (synCid))]
  rw [fv_syn_cdif R (synCid)]
  rw [Finset.mem_union]
  left
  exact hu

theorem nb091_wpp_notmem_0416 (D : Class) (R : Class) :
    (nb091AlphaDummy063 D R) ∉ ((synCcnv (synCdif R (synCid)))).fv := by
  simpa only [nb091AlphaDummy063, fv_syn_ccnv, fv_syn_cdif, Finset.mem_union,
    fv_syn_cid, not_or] using
    (And.intro (nb091_focused_notmem_0068 D R) (nb091_compact_fv_empty_0056 D R))

theorem nb091_focused_notmem_0069 (D : Class) (R : Class) (p : Var) :
    (nb091AlphaDummy064 D R p) ∉ R.fv :=
  by
  change
    freshVar
        (({(nb091AlphaDummy061 D R p)} : Finset Var) ∪
            ({(nb091AlphaDummy062 D R p)} : Finset Var) ∪ ((synWa
              (Wff.classMem (Class.cv (nb091AlphaDummy061 D R p)) (synCin D
                  (synCima (synCcnv (synCdif R (synCid)))
                    (synCsn (synCuni (synCuni (Class.cv p)))))))
              (Wff.classMem (Class.cv (nb091AlphaDummy062 D R p)) (synCin D
                  (synCima (synCcnv (synCdif R (synCid)))
                    (synCsn (synCuni (synCuni (Class.cv p))))))))).fv)
        0 ∉
      R.fv
  refine NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 0 ?_
  intro supportVariable hu
  rw [Finset.mem_union]
  right
  rw [fv_syn_wa
      (Wff.classMem (Class.cv (nb091AlphaDummy061 D R p)) (synCin D
          (synCima (synCcnv (synCdif R (synCid)))
            (synCsn (synCuni (synCuni (Class.cv p)))))))
      (Wff.classMem (Class.cv (nb091AlphaDummy062 D R p)) (synCin D
          (synCima (synCcnv (synCdif R (synCid)))
            (synCsn (synCuni (synCuni (Class.cv p)))))))]
  rw [Finset.mem_union]
  left
  rw [fv_wff_classMem (Class.cv (nb091AlphaDummy061 D R p))
      (synCin D (synCima (synCcnv (synCdif R (synCid)))
          (synCsn (synCuni (synCuni (Class.cv p))))))]
  rw [Finset.mem_union]
  right
  rw [fv_syn_cin D
      (synCima (synCcnv (synCdif R (synCid))) (synCsn (synCuni (synCuni (Class.cv p)))))]
  rw [Finset.mem_union]
  right
  rw [fv_syn_cima (synCcnv (synCdif R (synCid)))
      (synCsn (synCuni (synCuni (Class.cv p))))]
  rw [Finset.mem_union]
  left
  rw [fv_syn_ccnv (synCdif R (synCid))]
  rw [fv_syn_cdif R (synCid)]
  rw [Finset.mem_union]
  left
  exact hu

theorem nb091_wpp_notmem_0417 (D : Class) (R : Class) (p : Var) :
    (nb091AlphaDummy064 D R p) ∉ ((synCcnv (synCdif R (synCid)))).fv := by
  simpa only [nb091AlphaDummy064, fv_syn_ccnv, fv_syn_cdif, Finset.mem_union,
    fv_syn_cid, not_or] using
    (And.intro (nb091_focused_notmem_0069 D R p) (nb091_compact_fv_empty_0057 D R p))

theorem nb091_wpp_notmem_0418 (D : Class) (R : Class) :
    (nb091AlphaDummy057 D R) ∉ ((synCcnv (synCdif R (synCid)))).fv := by
  simpa only [nb091AlphaDummy057, fv_syn_ccnv, fv_syn_cdif, Finset.mem_union,
    fv_syn_cid, not_or] using
    (And.intro (nb091_focused_notmem_0005 D R) (nb091_compact_fv_empty_0058 D R))

theorem nb091_wpp_notmem_0419 (D : Class) (R : Class) (p : Var) :
    (nb091AlphaDummy058 D R p) ∉ ((synCcnv (synCdif R (synCid)))).fv := by
  simpa only [nb091AlphaDummy058, fv_syn_ccnv, fv_syn_cdif, Finset.mem_union,
    fv_syn_cid, not_or] using
    (And.intro (nb091_focused_notmem_0006 D R p) (nb091_compact_fv_empty_0059 D R p))

theorem nb091_wpp_notmem_0420 (D : Class) (R : Class) :
    (nb091AlphaDummy055 D R) ∉ ((synCcnv (synCdif R (synCid)))).fv := by
  simpa only [nb091AlphaDummy055, fv_syn_ccnv, fv_syn_cdif, Finset.mem_union,
    fv_syn_cid, not_or] using
    (And.intro (nb091_focused_notmem_0007 D R) (nb091_compact_fv_empty_0060 D R))

theorem nb091_wpp_notmem_0421 (D : Class) (R : Class) (p : Var) :
    (nb091AlphaDummy056 D R p) ∉ ((synCcnv (synCdif R (synCid)))).fv := by
  simpa only [nb091AlphaDummy056, fv_syn_ccnv, fv_syn_cdif, Finset.mem_union,
    fv_syn_cid, not_or] using
    (And.intro (nb091_focused_notmem_0008 D R p) (nb091_compact_fv_empty_0061 D R p))

theorem nb091_wpp_notmem_0422 (D : Class) (R : Class) :
    (nb091AlphaDummy048 D R) ∉ ((synCcnv (synCdif R (synCid)))).fv := by
  simpa only [nb091AlphaDummy048, fv_syn_ccnv, fv_syn_cdif, Finset.mem_union,
    fv_syn_cid, not_or] using
    (And.intro (nb091_focused_notmem_0009 D R) (nb091_compact_fv_empty_0062 D R))

theorem nb091_wpp_notmem_0423 (D : Class) (R : Class) (p : Var) :
    (nb091AlphaDummy050 D R p) ∉ ((synCcnv (synCdif R (synCid)))).fv := by
  simpa only [nb091AlphaDummy050, fv_syn_ccnv, fv_syn_cdif, Finset.mem_union,
    fv_syn_cid, not_or] using
    (And.intro (nb091_focused_notmem_0010 D R p) (nb091_compact_fv_empty_0063 D R p))

theorem nb091_wpp_notmem_0424 (D : Class) (R : Class) :
    (nb091AlphaDummy047 D R) ∉ ((synCcnv (synCdif R (synCid)))).fv := by
  simpa only [nb091AlphaDummy047, fv_syn_ccnv, fv_syn_cdif, Finset.mem_union,
    fv_syn_cid, not_or] using
    (And.intro (nb091_focused_notmem_0011 D R) (nb091_compact_fv_empty_0064 D R))

theorem nb091_wpp_notmem_0425 (D : Class) (R : Class) (p : Var) :
    (nb091AlphaDummy049 D R p) ∉ ((synCcnv (synCdif R (synCid)))).fv := by
  simpa only [nb091AlphaDummy049, fv_syn_ccnv, fv_syn_cdif, Finset.mem_union,
    fv_syn_cid, not_or] using
    (And.intro (nb091_focused_notmem_0012 D R p) (nb091_compact_fv_empty_0065 D R p))

theorem nb091_wpp_notmem_0426 (D : Class) (R : Class) :
    (nb091AlphaDummy053 D R) ∉ ((synCcnv (synCdif R (synCid)))).fv := by
  simpa only [nb091AlphaDummy053, fv_syn_ccnv, fv_syn_cdif, Finset.mem_union,
    fv_syn_cid, not_or] using
    (And.intro (nb091_focused_notmem_0013 D R) (nb091_compact_fv_empty_0066 D R))

theorem nb091_wpp_notmem_0427 (D : Class) (R : Class) (p : Var) :
    (nb091AlphaDummy054 D R p) ∉ ((synCcnv (synCdif R (synCid)))).fv := by
  simpa only [nb091AlphaDummy054, fv_syn_ccnv, fv_syn_cdif, Finset.mem_union,
    fv_syn_cid, not_or] using
    (And.intro (nb091_focused_notmem_0014 D R p) (nb091_compact_fv_empty_0067 D R p))

theorem nb091_wpp_notmem_0428 (D : Class) (R : Class) :
    (nb091AlphaDummy051 D R) ∉ ((synCcnv (synCdif R (synCid)))).fv := by
  simpa only [nb091AlphaDummy051, fv_syn_ccnv, fv_syn_cdif, Finset.mem_union,
    fv_syn_cid, not_or] using
    (And.intro (nb091_focused_notmem_0015 D R) (nb091_compact_fv_empty_0068 D R))

theorem nb091_wpp_notmem_0429 (D : Class) (R : Class) (p : Var) :
    (nb091AlphaDummy052 D R p) ∉ ((synCcnv (synCdif R (synCid)))).fv := by
  simpa only [nb091AlphaDummy052, fv_syn_ccnv, fv_syn_cdif, Finset.mem_union,
    fv_syn_cid, not_or] using
    (And.intro (nb091_focused_notmem_0016 D R p) (nb091_compact_fv_empty_0069 D R p))

theorem nb091_wpp_notmem_0430 (D : Class) (R : Class) :
    (nb091AlphaDummy045 D R) ∉ ((synCcnv (synCdif R (synCid)))).fv := by
  simpa only [nb091AlphaDummy045, fv_syn_ccnv, fv_syn_cdif, Finset.mem_union,
    fv_syn_cid, not_or] using
    (And.intro (nb091_focused_notmem_0017 D R) (nb091_compact_fv_empty_0070 D R))

theorem nb091_wpp_notmem_0431 (D : Class) (R : Class) (p : Var) :
    (nb091AlphaDummy046 D R p) ∉ ((synCcnv (synCdif R (synCid)))).fv := by
  simpa only [nb091AlphaDummy046, fv_syn_ccnv, fv_syn_cdif, Finset.mem_union,
    fv_syn_cid, not_or] using
    (And.intro (nb091_focused_notmem_0018 D R p) (nb091_compact_fv_empty_0071 D R p))

theorem nb091_wpp_notmem_0432 (D : Class) (R : Class) :
    (nb091AlphaDummy042 D R) ∉ ((synCcnv (synCdif R (synCid)))).fv := by
  simpa only [nb091AlphaDummy042, fv_syn_ccnv, fv_syn_cdif, Finset.mem_union,
    fv_syn_cid, not_or] using
    (And.intro (nb091_focused_notmem_0019 D R) (nb091_compact_fv_empty_0072 D R))

theorem nb091_wpp_notmem_0433 (D : Class) (R : Class) (p : Var) :
    (nb091AlphaDummy044 D R p) ∉ ((synCcnv (synCdif R (synCid)))).fv := by
  simpa only [nb091AlphaDummy044, fv_syn_ccnv, fv_syn_cdif, Finset.mem_union,
    fv_syn_cid, not_or] using
    (And.intro (nb091_focused_notmem_0020 D R p) (nb091_compact_fv_empty_0073 D R p))

theorem nb091_wpp_notmem_0434 (D : Class) (R : Class) :
    (nb091AlphaDummy041 D R) ∉ ((synCcnv (synCdif R (synCid)))).fv := by
  simpa only [nb091AlphaDummy041, fv_syn_ccnv, fv_syn_cdif, Finset.mem_union,
    fv_syn_cid, not_or] using
    (And.intro (nb091_focused_notmem_0021 D R) (nb091_compact_fv_empty_0074 D R))

theorem nb091_wpp_notmem_0435 (D : Class) (R : Class) (p : Var) :
    (nb091AlphaDummy043 D R p) ∉ ((synCcnv (synCdif R (synCid)))).fv := by
  simpa only [nb091AlphaDummy043, fv_syn_ccnv, fv_syn_cdif, Finset.mem_union,
    fv_syn_cid, not_or] using
    (And.intro (nb091_focused_notmem_0022 D R p) (nb091_compact_fv_empty_0075 D R p))

theorem nb091_wpp_notmem_0436 (D : Class) (R : Class) :
    (nb091AlphaDummy001 D R) ∉ ((synCcnv (synCdif R (synCid)))).fv := by
  simpa only [nb091AlphaDummy001, fv_syn_ccnv, fv_syn_cdif, Finset.mem_union,
    fv_syn_cid, not_or] using
    (And.intro (nb091_focused_notmem_0023 D R) (nb091_compact_fv_empty_0020 D R))

theorem nb091_wpp_notmem_0437 (D : Class) (R : Class) (p : Var) :
    (nb091AlphaDummy002 D R p) ∉ ((synCcnv (synCdif R (synCid)))).fv := by
  simpa only [nb091AlphaDummy002, fv_syn_ccnv, fv_syn_cdif, Finset.mem_union,
    fv_syn_cid, not_or] using
    (And.intro (nb091_focused_notmem_0024 D R p) (nb091_compact_fv_empty_0021 D R p))

theorem nb091_wpp_notmem_0438 (D : Class) (R : Class) :
    (nb091AlphaDummy000 D R) ∉ ((synCcnv (synCdif R (synCid)))).fv := by
  simpa only [nb091AlphaDummy000, fv_syn_ccnv, fv_syn_cdif, Finset.mem_union,
    fv_syn_cid, not_or] using
    (And.intro (nb091_focused_notmem_0025 D R) (nb091_compact_fv_empty_0022 D R))

theorem nb091_wpp_notmem_0439 (R : Class) (p : Var) (dv_R_p : p ∉ R.fv) :
    p ∉ ((synCcnv (synCdif R (synCid)))).fv := by
  simpa only [fv_syn_ccnv, fv_syn_cdif, Finset.mem_union, fv_syn_cid, not_or] using
    (And.intro dv_R_p (nb091_compact_fv_empty_0023 p))

theorem nb091_wpp_notmem_0440 (D : Class) (R : Class) :
    (nb091AlphaDummy003 D R) ∉ ((synCcnv (synCdif R (synCid)))).fv := by
  simpa only [nb091AlphaDummy003, fv_syn_ccnv, fv_syn_cdif, Finset.mem_union,
    fv_syn_cid, not_or] using
    (And.intro (nb091_focused_notmem_0026 D R) (nb091_compact_fv_empty_0024 D R))

theorem nb091_wpp_notmem_0441 (D : Class) (R : Class) (p : Var) :
    (nb091AlphaDummy004 D R p) ∉ ((synCcnv (synCdif R (synCid)))).fv := by
  simpa only [nb091AlphaDummy004, fv_syn_ccnv, fv_syn_cdif, Finset.mem_union,
    fv_syn_cid, not_or] using
    (And.intro (nb091_focused_notmem_0027 D R p) (nb091_compact_fv_empty_0025 D R p))

theorem nb091_compact_envfresh_0024 (D : Class) (R : Class) (p : Var)
    (dv_R_p : p ∉ R.fv) :
    TEnvFresh
      [((nb091AlphaDummy106 D R), (nb091AlphaDummy108 R p)),
        ((nb091AlphaDummy105 D R), (nb091AlphaDummy107 R p)),
        ((nb091AlphaDummy103 D R), (nb091AlphaDummy104 D R p)),
        ((nb091AlphaDummy101 D R), (nb091AlphaDummy102 D R p)),
        ((nb091AlphaDummy060 D R), (nb091AlphaDummy062 D R p)),
        ((nb091AlphaDummy059 D R), (nb091AlphaDummy061 D R p)),
        ((nb091AlphaDummy063 D R), (nb091AlphaDummy064 D R p)),
        ((nb091AlphaDummy057 D R), (nb091AlphaDummy058 D R p)),
        ((nb091AlphaDummy055 D R), (nb091AlphaDummy056 D R p)),
        ((nb091AlphaDummy048 D R), (nb091AlphaDummy050 D R p)),
        ((nb091AlphaDummy047 D R), (nb091AlphaDummy049 D R p)),
        ((nb091AlphaDummy053 D R), (nb091AlphaDummy054 D R p)),
        ((nb091AlphaDummy051 D R), (nb091AlphaDummy052 D R p)),
        ((nb091AlphaDummy045 D R), (nb091AlphaDummy046 D R p)),
        ((nb091AlphaDummy042 D R), (nb091AlphaDummy044 D R p)),
        ((nb091AlphaDummy041 D R), (nb091AlphaDummy043 D R p)),
        ((nb091AlphaDummy001 D R), (nb091AlphaDummy002 D R p)),
        ((nb091AlphaDummy000 D R), p),
        ((nb091AlphaDummy003 D R), (nb091AlphaDummy004 D R p))]
      ((synCcnv (synCdif R (synCid)))).fv :=
  by
  exact
    (TEnvFresh.consFresh (nb091AlphaDummy106 D R) (nb091AlphaDummy108 R p)
      (nb091_wpp_notmem_0404 D R) (nb091_wpp_notmem_0405 R p)
      (TEnvFresh.consFresh (nb091AlphaDummy105 D R) (nb091AlphaDummy107 R p)
        (nb091_wpp_notmem_0406 D R) (nb091_wpp_notmem_0407 R p)
        (TEnvFresh.consFresh (nb091AlphaDummy103 D R) (nb091AlphaDummy104 D R p)
          (nb091_wpp_notmem_0408 D R) (nb091_wpp_notmem_0409 D R p)
          (TEnvFresh.consFresh (nb091AlphaDummy101 D R) (nb091AlphaDummy102 D R p)
            (nb091_wpp_notmem_0410 D R) (nb091_wpp_notmem_0411 D R p)
            (TEnvFresh.consFresh (nb091AlphaDummy060 D R) (nb091AlphaDummy062 D R p)
              (nb091_wpp_notmem_0412 D R) (nb091_wpp_notmem_0413 D R p)
              (TEnvFresh.consFresh (nb091AlphaDummy059 D R)
                (nb091AlphaDummy061 D R p) (nb091_wpp_notmem_0414 D R)
                (nb091_wpp_notmem_0415 D R p) (TEnvFresh.consFresh (nb091AlphaDummy063 D R)
                  (nb091AlphaDummy064 D R p) (nb091_wpp_notmem_0416 D R)
                  (nb091_wpp_notmem_0417 D R p) (TEnvFresh.consFresh (nb091AlphaDummy057 D R)
                    (nb091AlphaDummy058 D R p) (nb091_wpp_notmem_0418 D R)
                    (nb091_wpp_notmem_0419 D R p)
                    (TEnvFresh.consFresh (nb091AlphaDummy055 D R)
                      (nb091AlphaDummy056 D R p) (nb091_wpp_notmem_0420 D R)
                      (nb091_wpp_notmem_0421 D R p)
                      (TEnvFresh.consFresh (nb091AlphaDummy048 D R)
                        (nb091AlphaDummy050 D R p) (nb091_wpp_notmem_0422 D R)
                        (nb091_wpp_notmem_0423 D R p)
                        (TEnvFresh.consFresh (nb091AlphaDummy047 D R)
                          (nb091AlphaDummy049 D R p) (nb091_wpp_notmem_0424 D R)
                          (nb091_wpp_notmem_0425 D R p)
                          (TEnvFresh.consFresh (nb091AlphaDummy053 D R)
                            (nb091AlphaDummy054 D R p) (nb091_wpp_notmem_0426 D R)
                            (nb091_wpp_notmem_0427 D R p)
                            (TEnvFresh.consFresh (nb091AlphaDummy051 D R)
                              (nb091AlphaDummy052 D R p) (nb091_wpp_notmem_0428 D R)
                              (nb091_wpp_notmem_0429 D R p)
                              (TEnvFresh.consFresh (nb091AlphaDummy045 D R)
                                (nb091AlphaDummy046 D R p) (nb091_wpp_notmem_0430 D R)
                                (nb091_wpp_notmem_0431 D R p)
                                (TEnvFresh.consFresh (nb091AlphaDummy042 D R)
                                  (nb091AlphaDummy044 D R p) (nb091_wpp_notmem_0432 D R)
                                  (nb091_wpp_notmem_0433 D R p)
                                  (TEnvFresh.consFresh (nb091AlphaDummy041 D R)
                                    (nb091AlphaDummy043 D R p) (nb091_wpp_notmem_0434 D R)
                                    (nb091_wpp_notmem_0435 D R p)
                                    (TEnvFresh.consFresh (nb091AlphaDummy001 D R)
                                      (nb091AlphaDummy002 D R p) (nb091_wpp_notmem_0436 D R)
                                      (nb091_wpp_notmem_0437 D R p)
                                      (TEnvFresh.consFresh (nb091AlphaDummy000 D R) p
                                        (nb091_wpp_notmem_0438 D R)
                                        (nb091_wpp_notmem_0439 R p dv_R_p)
                                        (TEnvFresh.consFresh (nb091AlphaDummy003 D R)
        (nb091AlphaDummy004 D R p) (nb091_wpp_notmem_0440 D R) (nb091_wpp_notmem_0441 D R p)
        (TEnvFresh.nil ((synCcnv (synCdif R (synCid)))).fv))))))))))))))))))))


end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired
