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
    (nb091_alpha_dummy_060 D R) ∉ R.fv :=
  by
  change
    freshVar
        (((syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn
                  (syn_cuni (syn_cuni (Class.cv (nb091_alpha_dummy_000 D R)))))))).fv ∪
          ((syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn
                  (syn_cuni (syn_cuni (Class.cv (nb091_alpha_dummy_000 D R)))))))).fv)
        1 ∉
      R.fv
  refine NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 1 ?_
  intro supportVariable hu
  rw [Finset.mem_union]
  left
  rw [fv_syn_cin D
      (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
        (syn_csn (syn_cuni (syn_cuni (Class.cv (nb091_alpha_dummy_000 D R))))))]
  rw [Finset.mem_union]
  right
  rw [fv_syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
      (syn_csn (syn_cuni (syn_cuni (Class.cv (nb091_alpha_dummy_000 D R)))))]
  rw [Finset.mem_union]
  left
  rw [fv_syn_ccnv (syn_cdif R (syn_cid))]
  rw [fv_syn_cdif R (syn_cid)]
  rw [Finset.mem_union]
  left
  exact hu

theorem nb091_wpp_notmem_0412 (D : Class) (R : Class) :
    (nb091_alpha_dummy_060 D R) ∉ ((syn_ccnv (syn_cdif R (syn_cid)))).fv := by
  simpa only [nb091_alpha_dummy_060, fv_syn_ccnv, fv_syn_cdif, Finset.mem_union,
    fv_syn_cid, not_or] using
    (And.intro (nb091_focused_notmem_0064 D R) (nb091_compact_fv_empty_0052 D R))

theorem nb091_focused_notmem_0065 (D : Class) (R : Class) (p : Var) :
    (nb091_alpha_dummy_062 D R p) ∉ R.fv :=
  by
  change
    freshVar
        (((syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
                (syn_csn (syn_cuni (syn_cuni (Class.cv p))))))).fv ∪ ((syn_cin D
              (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
                (syn_csn (syn_cuni (syn_cuni (Class.cv p))))))).fv)
        1 ∉
      R.fv
  refine NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 1 ?_
  intro supportVariable hu
  rw [Finset.mem_union]
  left
  rw [fv_syn_cin D
      (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (syn_cuni (syn_cuni (Class.cv p)))))]
  rw [Finset.mem_union]
  right
  rw [fv_syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
      (syn_csn (syn_cuni (syn_cuni (Class.cv p))))]
  rw [Finset.mem_union]
  left
  rw [fv_syn_ccnv (syn_cdif R (syn_cid))]
  rw [fv_syn_cdif R (syn_cid)]
  rw [Finset.mem_union]
  left
  exact hu

theorem nb091_wpp_notmem_0413 (D : Class) (R : Class) (p : Var) :
    (nb091_alpha_dummy_062 D R p) ∉ ((syn_ccnv (syn_cdif R (syn_cid)))).fv := by
  simpa only [nb091_alpha_dummy_062, fv_syn_ccnv, fv_syn_cdif, Finset.mem_union,
    fv_syn_cid, not_or] using
    (And.intro (nb091_focused_notmem_0065 D R p) (nb091_compact_fv_empty_0053 D R p))

theorem nb091_focused_notmem_0066 (D : Class) (R : Class) :
    (nb091_alpha_dummy_059 D R) ∉ R.fv :=
  by
  change
    freshVar
        (((syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn
                  (syn_cuni (syn_cuni (Class.cv (nb091_alpha_dummy_000 D R)))))))).fv ∪
          ((syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn
                  (syn_cuni (syn_cuni (Class.cv (nb091_alpha_dummy_000 D R)))))))).fv)
        0 ∉
      R.fv
  refine NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 0 ?_
  intro supportVariable hu
  rw [Finset.mem_union]
  left
  rw [fv_syn_cin D
      (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
        (syn_csn (syn_cuni (syn_cuni (Class.cv (nb091_alpha_dummy_000 D R))))))]
  rw [Finset.mem_union]
  right
  rw [fv_syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
      (syn_csn (syn_cuni (syn_cuni (Class.cv (nb091_alpha_dummy_000 D R)))))]
  rw [Finset.mem_union]
  left
  rw [fv_syn_ccnv (syn_cdif R (syn_cid))]
  rw [fv_syn_cdif R (syn_cid)]
  rw [Finset.mem_union]
  left
  exact hu

theorem nb091_wpp_notmem_0414 (D : Class) (R : Class) :
    (nb091_alpha_dummy_059 D R) ∉ ((syn_ccnv (syn_cdif R (syn_cid)))).fv := by
  simpa only [nb091_alpha_dummy_059, fv_syn_ccnv, fv_syn_cdif, Finset.mem_union,
    fv_syn_cid, not_or] using
    (And.intro (nb091_focused_notmem_0066 D R) (nb091_compact_fv_empty_0054 D R))

theorem nb091_focused_notmem_0067 (D : Class) (R : Class) (p : Var) :
    (nb091_alpha_dummy_061 D R p) ∉ R.fv :=
  by
  change
    freshVar
        (((syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
                (syn_csn (syn_cuni (syn_cuni (Class.cv p))))))).fv ∪ ((syn_cin D
              (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
                (syn_csn (syn_cuni (syn_cuni (Class.cv p))))))).fv)
        0 ∉
      R.fv
  refine NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 0 ?_
  intro supportVariable hu
  rw [Finset.mem_union]
  left
  rw [fv_syn_cin D
      (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (syn_cuni (syn_cuni (Class.cv p)))))]
  rw [Finset.mem_union]
  right
  rw [fv_syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
      (syn_csn (syn_cuni (syn_cuni (Class.cv p))))]
  rw [Finset.mem_union]
  left
  rw [fv_syn_ccnv (syn_cdif R (syn_cid))]
  rw [fv_syn_cdif R (syn_cid)]
  rw [Finset.mem_union]
  left
  exact hu

theorem nb091_wpp_notmem_0415 (D : Class) (R : Class) (p : Var) :
    (nb091_alpha_dummy_061 D R p) ∉ ((syn_ccnv (syn_cdif R (syn_cid)))).fv := by
  simpa only [nb091_alpha_dummy_061, fv_syn_ccnv, fv_syn_cdif, Finset.mem_union,
    fv_syn_cid, not_or] using
    (And.intro (nb091_focused_notmem_0067 D R p) (nb091_compact_fv_empty_0055 D R p))

theorem nb091_focused_notmem_0068 (D : Class) (R : Class) :
    (nb091_alpha_dummy_063 D R) ∉ R.fv :=
  by
  change
    freshVar
        (({(nb091_alpha_dummy_059 D R)} : Finset Var) ∪
            ({(nb091_alpha_dummy_060 D R)} : Finset Var) ∪ ((syn_wa
              (Wff.classMem (Class.cv (nb091_alpha_dummy_059 D R)) (syn_cin D
                  (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn
                      (syn_cuni (syn_cuni (Class.cv (nb091_alpha_dummy_000 D R))))))))
              (Wff.classMem (Class.cv (nb091_alpha_dummy_060 D R)) (syn_cin D
                  (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (syn_cuni
                        (syn_cuni (Class.cv (nb091_alpha_dummy_000 D R)))))))))).fv)
        0 ∉
      R.fv
  refine NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 0 ?_
  intro supportVariable hu
  rw [Finset.mem_union]
  right
  rw [fv_syn_wa
      (Wff.classMem (Class.cv (nb091_alpha_dummy_059 D R)) (syn_cin D
          (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
            (syn_csn (syn_cuni (syn_cuni (Class.cv (nb091_alpha_dummy_000 D R))))))))
      (Wff.classMem (Class.cv (nb091_alpha_dummy_060 D R)) (syn_cin D
          (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
            (syn_csn (syn_cuni (syn_cuni (Class.cv (nb091_alpha_dummy_000 D R))))))))]
  rw [Finset.mem_union]
  left
  rw [fv_wff_classMem (Class.cv (nb091_alpha_dummy_059 D R))
      (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
          (syn_csn (syn_cuni (syn_cuni (Class.cv (nb091_alpha_dummy_000 D R)))))))]
  rw [Finset.mem_union]
  right
  rw [fv_syn_cin D
      (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
        (syn_csn (syn_cuni (syn_cuni (Class.cv (nb091_alpha_dummy_000 D R))))))]
  rw [Finset.mem_union]
  right
  rw [fv_syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
      (syn_csn (syn_cuni (syn_cuni (Class.cv (nb091_alpha_dummy_000 D R)))))]
  rw [Finset.mem_union]
  left
  rw [fv_syn_ccnv (syn_cdif R (syn_cid))]
  rw [fv_syn_cdif R (syn_cid)]
  rw [Finset.mem_union]
  left
  exact hu

theorem nb091_wpp_notmem_0416 (D : Class) (R : Class) :
    (nb091_alpha_dummy_063 D R) ∉ ((syn_ccnv (syn_cdif R (syn_cid)))).fv := by
  simpa only [nb091_alpha_dummy_063, fv_syn_ccnv, fv_syn_cdif, Finset.mem_union,
    fv_syn_cid, not_or] using
    (And.intro (nb091_focused_notmem_0068 D R) (nb091_compact_fv_empty_0056 D R))

theorem nb091_focused_notmem_0069 (D : Class) (R : Class) (p : Var) :
    (nb091_alpha_dummy_064 D R p) ∉ R.fv :=
  by
  change
    freshVar
        (({(nb091_alpha_dummy_061 D R p)} : Finset Var) ∪
            ({(nb091_alpha_dummy_062 D R p)} : Finset Var) ∪ ((syn_wa
              (Wff.classMem (Class.cv (nb091_alpha_dummy_061 D R p)) (syn_cin D
                  (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
                    (syn_csn (syn_cuni (syn_cuni (Class.cv p)))))))
              (Wff.classMem (Class.cv (nb091_alpha_dummy_062 D R p)) (syn_cin D
                  (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
                    (syn_csn (syn_cuni (syn_cuni (Class.cv p))))))))).fv)
        0 ∉
      R.fv
  refine NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 0 ?_
  intro supportVariable hu
  rw [Finset.mem_union]
  right
  rw [fv_syn_wa
      (Wff.classMem (Class.cv (nb091_alpha_dummy_061 D R p)) (syn_cin D
          (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
            (syn_csn (syn_cuni (syn_cuni (Class.cv p)))))))
      (Wff.classMem (Class.cv (nb091_alpha_dummy_062 D R p)) (syn_cin D
          (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
            (syn_csn (syn_cuni (syn_cuni (Class.cv p)))))))]
  rw [Finset.mem_union]
  left
  rw [fv_wff_classMem (Class.cv (nb091_alpha_dummy_061 D R p))
      (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
          (syn_csn (syn_cuni (syn_cuni (Class.cv p))))))]
  rw [Finset.mem_union]
  right
  rw [fv_syn_cin D
      (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (syn_cuni (syn_cuni (Class.cv p)))))]
  rw [Finset.mem_union]
  right
  rw [fv_syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
      (syn_csn (syn_cuni (syn_cuni (Class.cv p))))]
  rw [Finset.mem_union]
  left
  rw [fv_syn_ccnv (syn_cdif R (syn_cid))]
  rw [fv_syn_cdif R (syn_cid)]
  rw [Finset.mem_union]
  left
  exact hu

theorem nb091_wpp_notmem_0417 (D : Class) (R : Class) (p : Var) :
    (nb091_alpha_dummy_064 D R p) ∉ ((syn_ccnv (syn_cdif R (syn_cid)))).fv := by
  simpa only [nb091_alpha_dummy_064, fv_syn_ccnv, fv_syn_cdif, Finset.mem_union,
    fv_syn_cid, not_or] using
    (And.intro (nb091_focused_notmem_0069 D R p) (nb091_compact_fv_empty_0057 D R p))

theorem nb091_wpp_notmem_0418 (D : Class) (R : Class) :
    (nb091_alpha_dummy_057 D R) ∉ ((syn_ccnv (syn_cdif R (syn_cid)))).fv := by
  simpa only [nb091_alpha_dummy_057, fv_syn_ccnv, fv_syn_cdif, Finset.mem_union,
    fv_syn_cid, not_or] using
    (And.intro (nb091_focused_notmem_0005 D R) (nb091_compact_fv_empty_0058 D R))

theorem nb091_wpp_notmem_0419 (D : Class) (R : Class) (p : Var) :
    (nb091_alpha_dummy_058 D R p) ∉ ((syn_ccnv (syn_cdif R (syn_cid)))).fv := by
  simpa only [nb091_alpha_dummy_058, fv_syn_ccnv, fv_syn_cdif, Finset.mem_union,
    fv_syn_cid, not_or] using
    (And.intro (nb091_focused_notmem_0006 D R p) (nb091_compact_fv_empty_0059 D R p))

theorem nb091_wpp_notmem_0420 (D : Class) (R : Class) :
    (nb091_alpha_dummy_055 D R) ∉ ((syn_ccnv (syn_cdif R (syn_cid)))).fv := by
  simpa only [nb091_alpha_dummy_055, fv_syn_ccnv, fv_syn_cdif, Finset.mem_union,
    fv_syn_cid, not_or] using
    (And.intro (nb091_focused_notmem_0007 D R) (nb091_compact_fv_empty_0060 D R))

theorem nb091_wpp_notmem_0421 (D : Class) (R : Class) (p : Var) :
    (nb091_alpha_dummy_056 D R p) ∉ ((syn_ccnv (syn_cdif R (syn_cid)))).fv := by
  simpa only [nb091_alpha_dummy_056, fv_syn_ccnv, fv_syn_cdif, Finset.mem_union,
    fv_syn_cid, not_or] using
    (And.intro (nb091_focused_notmem_0008 D R p) (nb091_compact_fv_empty_0061 D R p))

theorem nb091_wpp_notmem_0422 (D : Class) (R : Class) :
    (nb091_alpha_dummy_048 D R) ∉ ((syn_ccnv (syn_cdif R (syn_cid)))).fv := by
  simpa only [nb091_alpha_dummy_048, fv_syn_ccnv, fv_syn_cdif, Finset.mem_union,
    fv_syn_cid, not_or] using
    (And.intro (nb091_focused_notmem_0009 D R) (nb091_compact_fv_empty_0062 D R))

theorem nb091_wpp_notmem_0423 (D : Class) (R : Class) (p : Var) :
    (nb091_alpha_dummy_050 D R p) ∉ ((syn_ccnv (syn_cdif R (syn_cid)))).fv := by
  simpa only [nb091_alpha_dummy_050, fv_syn_ccnv, fv_syn_cdif, Finset.mem_union,
    fv_syn_cid, not_or] using
    (And.intro (nb091_focused_notmem_0010 D R p) (nb091_compact_fv_empty_0063 D R p))

theorem nb091_wpp_notmem_0424 (D : Class) (R : Class) :
    (nb091_alpha_dummy_047 D R) ∉ ((syn_ccnv (syn_cdif R (syn_cid)))).fv := by
  simpa only [nb091_alpha_dummy_047, fv_syn_ccnv, fv_syn_cdif, Finset.mem_union,
    fv_syn_cid, not_or] using
    (And.intro (nb091_focused_notmem_0011 D R) (nb091_compact_fv_empty_0064 D R))

theorem nb091_wpp_notmem_0425 (D : Class) (R : Class) (p : Var) :
    (nb091_alpha_dummy_049 D R p) ∉ ((syn_ccnv (syn_cdif R (syn_cid)))).fv := by
  simpa only [nb091_alpha_dummy_049, fv_syn_ccnv, fv_syn_cdif, Finset.mem_union,
    fv_syn_cid, not_or] using
    (And.intro (nb091_focused_notmem_0012 D R p) (nb091_compact_fv_empty_0065 D R p))

theorem nb091_wpp_notmem_0426 (D : Class) (R : Class) :
    (nb091_alpha_dummy_053 D R) ∉ ((syn_ccnv (syn_cdif R (syn_cid)))).fv := by
  simpa only [nb091_alpha_dummy_053, fv_syn_ccnv, fv_syn_cdif, Finset.mem_union,
    fv_syn_cid, not_or] using
    (And.intro (nb091_focused_notmem_0013 D R) (nb091_compact_fv_empty_0066 D R))

theorem nb091_wpp_notmem_0427 (D : Class) (R : Class) (p : Var) :
    (nb091_alpha_dummy_054 D R p) ∉ ((syn_ccnv (syn_cdif R (syn_cid)))).fv := by
  simpa only [nb091_alpha_dummy_054, fv_syn_ccnv, fv_syn_cdif, Finset.mem_union,
    fv_syn_cid, not_or] using
    (And.intro (nb091_focused_notmem_0014 D R p) (nb091_compact_fv_empty_0067 D R p))

theorem nb091_wpp_notmem_0428 (D : Class) (R : Class) :
    (nb091_alpha_dummy_051 D R) ∉ ((syn_ccnv (syn_cdif R (syn_cid)))).fv := by
  simpa only [nb091_alpha_dummy_051, fv_syn_ccnv, fv_syn_cdif, Finset.mem_union,
    fv_syn_cid, not_or] using
    (And.intro (nb091_focused_notmem_0015 D R) (nb091_compact_fv_empty_0068 D R))

theorem nb091_wpp_notmem_0429 (D : Class) (R : Class) (p : Var) :
    (nb091_alpha_dummy_052 D R p) ∉ ((syn_ccnv (syn_cdif R (syn_cid)))).fv := by
  simpa only [nb091_alpha_dummy_052, fv_syn_ccnv, fv_syn_cdif, Finset.mem_union,
    fv_syn_cid, not_or] using
    (And.intro (nb091_focused_notmem_0016 D R p) (nb091_compact_fv_empty_0069 D R p))

theorem nb091_wpp_notmem_0430 (D : Class) (R : Class) :
    (nb091_alpha_dummy_045 D R) ∉ ((syn_ccnv (syn_cdif R (syn_cid)))).fv := by
  simpa only [nb091_alpha_dummy_045, fv_syn_ccnv, fv_syn_cdif, Finset.mem_union,
    fv_syn_cid, not_or] using
    (And.intro (nb091_focused_notmem_0017 D R) (nb091_compact_fv_empty_0070 D R))

theorem nb091_wpp_notmem_0431 (D : Class) (R : Class) (p : Var) :
    (nb091_alpha_dummy_046 D R p) ∉ ((syn_ccnv (syn_cdif R (syn_cid)))).fv := by
  simpa only [nb091_alpha_dummy_046, fv_syn_ccnv, fv_syn_cdif, Finset.mem_union,
    fv_syn_cid, not_or] using
    (And.intro (nb091_focused_notmem_0018 D R p) (nb091_compact_fv_empty_0071 D R p))

theorem nb091_wpp_notmem_0432 (D : Class) (R : Class) :
    (nb091_alpha_dummy_042 D R) ∉ ((syn_ccnv (syn_cdif R (syn_cid)))).fv := by
  simpa only [nb091_alpha_dummy_042, fv_syn_ccnv, fv_syn_cdif, Finset.mem_union,
    fv_syn_cid, not_or] using
    (And.intro (nb091_focused_notmem_0019 D R) (nb091_compact_fv_empty_0072 D R))

theorem nb091_wpp_notmem_0433 (D : Class) (R : Class) (p : Var) :
    (nb091_alpha_dummy_044 D R p) ∉ ((syn_ccnv (syn_cdif R (syn_cid)))).fv := by
  simpa only [nb091_alpha_dummy_044, fv_syn_ccnv, fv_syn_cdif, Finset.mem_union,
    fv_syn_cid, not_or] using
    (And.intro (nb091_focused_notmem_0020 D R p) (nb091_compact_fv_empty_0073 D R p))

theorem nb091_wpp_notmem_0434 (D : Class) (R : Class) :
    (nb091_alpha_dummy_041 D R) ∉ ((syn_ccnv (syn_cdif R (syn_cid)))).fv := by
  simpa only [nb091_alpha_dummy_041, fv_syn_ccnv, fv_syn_cdif, Finset.mem_union,
    fv_syn_cid, not_or] using
    (And.intro (nb091_focused_notmem_0021 D R) (nb091_compact_fv_empty_0074 D R))

theorem nb091_wpp_notmem_0435 (D : Class) (R : Class) (p : Var) :
    (nb091_alpha_dummy_043 D R p) ∉ ((syn_ccnv (syn_cdif R (syn_cid)))).fv := by
  simpa only [nb091_alpha_dummy_043, fv_syn_ccnv, fv_syn_cdif, Finset.mem_union,
    fv_syn_cid, not_or] using
    (And.intro (nb091_focused_notmem_0022 D R p) (nb091_compact_fv_empty_0075 D R p))

theorem nb091_wpp_notmem_0436 (D : Class) (R : Class) :
    (nb091_alpha_dummy_001 D R) ∉ ((syn_ccnv (syn_cdif R (syn_cid)))).fv := by
  simpa only [nb091_alpha_dummy_001, fv_syn_ccnv, fv_syn_cdif, Finset.mem_union,
    fv_syn_cid, not_or] using
    (And.intro (nb091_focused_notmem_0023 D R) (nb091_compact_fv_empty_0020 D R))

theorem nb091_wpp_notmem_0437 (D : Class) (R : Class) (p : Var) :
    (nb091_alpha_dummy_002 D R p) ∉ ((syn_ccnv (syn_cdif R (syn_cid)))).fv := by
  simpa only [nb091_alpha_dummy_002, fv_syn_ccnv, fv_syn_cdif, Finset.mem_union,
    fv_syn_cid, not_or] using
    (And.intro (nb091_focused_notmem_0024 D R p) (nb091_compact_fv_empty_0021 D R p))

theorem nb091_wpp_notmem_0438 (D : Class) (R : Class) :
    (nb091_alpha_dummy_000 D R) ∉ ((syn_ccnv (syn_cdif R (syn_cid)))).fv := by
  simpa only [nb091_alpha_dummy_000, fv_syn_ccnv, fv_syn_cdif, Finset.mem_union,
    fv_syn_cid, not_or] using
    (And.intro (nb091_focused_notmem_0025 D R) (nb091_compact_fv_empty_0022 D R))

theorem nb091_wpp_notmem_0439 (R : Class) (p : Var) (dv_R_p : p ∉ R.fv) :
    p ∉ ((syn_ccnv (syn_cdif R (syn_cid)))).fv := by
  simpa only [fv_syn_ccnv, fv_syn_cdif, Finset.mem_union, fv_syn_cid, not_or] using
    (And.intro dv_R_p (nb091_compact_fv_empty_0023 p))

theorem nb091_wpp_notmem_0440 (D : Class) (R : Class) :
    (nb091_alpha_dummy_003 D R) ∉ ((syn_ccnv (syn_cdif R (syn_cid)))).fv := by
  simpa only [nb091_alpha_dummy_003, fv_syn_ccnv, fv_syn_cdif, Finset.mem_union,
    fv_syn_cid, not_or] using
    (And.intro (nb091_focused_notmem_0026 D R) (nb091_compact_fv_empty_0024 D R))

theorem nb091_wpp_notmem_0441 (D : Class) (R : Class) (p : Var) :
    (nb091_alpha_dummy_004 D R p) ∉ ((syn_ccnv (syn_cdif R (syn_cid)))).fv := by
  simpa only [nb091_alpha_dummy_004, fv_syn_ccnv, fv_syn_cdif, Finset.mem_union,
    fv_syn_cid, not_or] using
    (And.intro (nb091_focused_notmem_0027 D R p) (nb091_compact_fv_empty_0025 D R p))

theorem nb091_compact_envfresh_0024 (D : Class) (R : Class) (p : Var)
    (dv_R_p : p ∉ R.fv) :
    TEnvFresh
      [((nb091_alpha_dummy_106 D R), (nb091_alpha_dummy_108 R p)),
        ((nb091_alpha_dummy_105 D R), (nb091_alpha_dummy_107 R p)),
        ((nb091_alpha_dummy_103 D R), (nb091_alpha_dummy_104 D R p)),
        ((nb091_alpha_dummy_101 D R), (nb091_alpha_dummy_102 D R p)),
        ((nb091_alpha_dummy_060 D R), (nb091_alpha_dummy_062 D R p)),
        ((nb091_alpha_dummy_059 D R), (nb091_alpha_dummy_061 D R p)),
        ((nb091_alpha_dummy_063 D R), (nb091_alpha_dummy_064 D R p)),
        ((nb091_alpha_dummy_057 D R), (nb091_alpha_dummy_058 D R p)),
        ((nb091_alpha_dummy_055 D R), (nb091_alpha_dummy_056 D R p)),
        ((nb091_alpha_dummy_048 D R), (nb091_alpha_dummy_050 D R p)),
        ((nb091_alpha_dummy_047 D R), (nb091_alpha_dummy_049 D R p)),
        ((nb091_alpha_dummy_053 D R), (nb091_alpha_dummy_054 D R p)),
        ((nb091_alpha_dummy_051 D R), (nb091_alpha_dummy_052 D R p)),
        ((nb091_alpha_dummy_045 D R), (nb091_alpha_dummy_046 D R p)),
        ((nb091_alpha_dummy_042 D R), (nb091_alpha_dummy_044 D R p)),
        ((nb091_alpha_dummy_041 D R), (nb091_alpha_dummy_043 D R p)),
        ((nb091_alpha_dummy_001 D R), (nb091_alpha_dummy_002 D R p)),
        ((nb091_alpha_dummy_000 D R), p),
        ((nb091_alpha_dummy_003 D R), (nb091_alpha_dummy_004 D R p))]
      ((syn_ccnv (syn_cdif R (syn_cid)))).fv :=
  by
  exact
    (TEnvFresh.consFresh (nb091_alpha_dummy_106 D R) (nb091_alpha_dummy_108 R p)
      (nb091_wpp_notmem_0404 D R) (nb091_wpp_notmem_0405 R p)
      (TEnvFresh.consFresh (nb091_alpha_dummy_105 D R) (nb091_alpha_dummy_107 R p)
        (nb091_wpp_notmem_0406 D R) (nb091_wpp_notmem_0407 R p)
        (TEnvFresh.consFresh (nb091_alpha_dummy_103 D R) (nb091_alpha_dummy_104 D R p)
          (nb091_wpp_notmem_0408 D R) (nb091_wpp_notmem_0409 D R p)
          (TEnvFresh.consFresh (nb091_alpha_dummy_101 D R) (nb091_alpha_dummy_102 D R p)
            (nb091_wpp_notmem_0410 D R) (nb091_wpp_notmem_0411 D R p)
            (TEnvFresh.consFresh (nb091_alpha_dummy_060 D R) (nb091_alpha_dummy_062 D R p)
              (nb091_wpp_notmem_0412 D R) (nb091_wpp_notmem_0413 D R p)
              (TEnvFresh.consFresh (nb091_alpha_dummy_059 D R)
                (nb091_alpha_dummy_061 D R p) (nb091_wpp_notmem_0414 D R)
                (nb091_wpp_notmem_0415 D R p) (TEnvFresh.consFresh (nb091_alpha_dummy_063 D R)
                  (nb091_alpha_dummy_064 D R p) (nb091_wpp_notmem_0416 D R)
                  (nb091_wpp_notmem_0417 D R p) (TEnvFresh.consFresh (nb091_alpha_dummy_057 D R)
                    (nb091_alpha_dummy_058 D R p) (nb091_wpp_notmem_0418 D R)
                    (nb091_wpp_notmem_0419 D R p)
                    (TEnvFresh.consFresh (nb091_alpha_dummy_055 D R)
                      (nb091_alpha_dummy_056 D R p) (nb091_wpp_notmem_0420 D R)
                      (nb091_wpp_notmem_0421 D R p)
                      (TEnvFresh.consFresh (nb091_alpha_dummy_048 D R)
                        (nb091_alpha_dummy_050 D R p) (nb091_wpp_notmem_0422 D R)
                        (nb091_wpp_notmem_0423 D R p)
                        (TEnvFresh.consFresh (nb091_alpha_dummy_047 D R)
                          (nb091_alpha_dummy_049 D R p) (nb091_wpp_notmem_0424 D R)
                          (nb091_wpp_notmem_0425 D R p)
                          (TEnvFresh.consFresh (nb091_alpha_dummy_053 D R)
                            (nb091_alpha_dummy_054 D R p) (nb091_wpp_notmem_0426 D R)
                            (nb091_wpp_notmem_0427 D R p)
                            (TEnvFresh.consFresh (nb091_alpha_dummy_051 D R)
                              (nb091_alpha_dummy_052 D R p) (nb091_wpp_notmem_0428 D R)
                              (nb091_wpp_notmem_0429 D R p)
                              (TEnvFresh.consFresh (nb091_alpha_dummy_045 D R)
                                (nb091_alpha_dummy_046 D R p) (nb091_wpp_notmem_0430 D R)
                                (nb091_wpp_notmem_0431 D R p)
                                (TEnvFresh.consFresh (nb091_alpha_dummy_042 D R)
                                  (nb091_alpha_dummy_044 D R p) (nb091_wpp_notmem_0432 D R)
                                  (nb091_wpp_notmem_0433 D R p)
                                  (TEnvFresh.consFresh (nb091_alpha_dummy_041 D R)
                                    (nb091_alpha_dummy_043 D R p) (nb091_wpp_notmem_0434 D R)
                                    (nb091_wpp_notmem_0435 D R p)
                                    (TEnvFresh.consFresh (nb091_alpha_dummy_001 D R)
                                      (nb091_alpha_dummy_002 D R p) (nb091_wpp_notmem_0436 D R)
                                      (nb091_wpp_notmem_0437 D R p)
                                      (TEnvFresh.consFresh (nb091_alpha_dummy_000 D R) p
                                        (nb091_wpp_notmem_0438 D R)
                                        (nb091_wpp_notmem_0439 R p dv_R_p)
                                        (TEnvFresh.consFresh (nb091_alpha_dummy_003 D R)
        (nb091_alpha_dummy_004 D R p) (nb091_wpp_notmem_0440 D R) (nb091_wpp_notmem_0441 D R p)
        (TEnvFresh.nil ((syn_ccnv (syn_cdif R (syn_cid)))).fv))))))))))))))))))))


end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired
