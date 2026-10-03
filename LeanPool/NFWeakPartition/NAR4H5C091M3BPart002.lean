/-
Copyright (c) 2026 Elliot Glazer and NFNotWPP contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elliot Glazer and NFNotWPP contributors
-/

module

public import LeanPool.NFWeakPartition.NAR4H5C091M3BPart001

/-! NF weak partition development: NAR4H5C091M3BPart002. -/


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

theorem nb091_fresh_225 (D : Class) (R : Class) :
    (nb091_alpha_dummy_060 D R) ∉
      (((syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn
                (syn_cuni (syn_cuni (Class.cv (nb091_alpha_dummy_000 D R)))))))).fv ∪
        ((syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn
                (syn_cuni (syn_cuni (Class.cv (nb091_alpha_dummy_000 D R)))))))).fv) :=
  by
  simpa only [nb091_alpha_dummy_060] using
    freshVar_not_mem
      (((syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn
                (syn_cuni (syn_cuni (Class.cv (nb091_alpha_dummy_000 D R)))))))).fv ∪
        ((syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn
                (syn_cuni (syn_cuni (Class.cv (nb091_alpha_dummy_000 D R)))))))).fv)
      1

theorem nb091_distinct_226 (D : Class) (R : Class) :
    (nb091_alpha_dummy_059 D R) ≠ (nb091_alpha_dummy_060 D R) := by
  simpa only [nb091_alpha_dummy_059, nb091_alpha_dummy_060] using
    (freshVar_injective (((syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn
                (syn_cuni (syn_cuni (Class.cv (nb091_alpha_dummy_000 D R)))))))).fv ∪
        ((syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn
                (syn_cuni (syn_cuni (Class.cv (nb091_alpha_dummy_000 D R)))))))).fv)
      (i := 0) (j := 1) (by decide))

theorem nb091_fresh_227 (D : Class) (R : Class) (p : Var) :
    (nb091_alpha_dummy_061 D R p) ∉
      (((syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
              (syn_csn (syn_cuni (syn_cuni (Class.cv p))))))).fv ∪ ((syn_cin D
            (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
              (syn_csn (syn_cuni (syn_cuni (Class.cv p))))))).fv) :=
  by
  simpa only [nb091_alpha_dummy_061] using
    freshVar_not_mem
      (((syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
              (syn_csn (syn_cuni (syn_cuni (Class.cv p))))))).fv ∪ ((syn_cin D
            (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
              (syn_csn (syn_cuni (syn_cuni (Class.cv p))))))).fv)
      0

theorem nb091_fresh_228 (D : Class) (R : Class) (p : Var) :
    (nb091_alpha_dummy_062 D R p) ∉
      (((syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
              (syn_csn (syn_cuni (syn_cuni (Class.cv p))))))).fv ∪ ((syn_cin D
            (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
              (syn_csn (syn_cuni (syn_cuni (Class.cv p))))))).fv) :=
  by
  simpa only [nb091_alpha_dummy_062] using
    freshVar_not_mem
      (((syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
              (syn_csn (syn_cuni (syn_cuni (Class.cv p))))))).fv ∪ ((syn_cin D
            (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
              (syn_csn (syn_cuni (syn_cuni (Class.cv p))))))).fv)
      1

theorem nb091_distinct_229 (D : Class) (R : Class) (p : Var) :
    (nb091_alpha_dummy_061 D R p) ≠ (nb091_alpha_dummy_062 D R p) := by
  simpa only [nb091_alpha_dummy_061, nb091_alpha_dummy_062] using
    (freshVar_injective (((syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
              (syn_csn (syn_cuni (syn_cuni (Class.cv p))))))).fv ∪ ((syn_cin D
            (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
              (syn_csn (syn_cuni (syn_cuni (Class.cv p))))))).fv) (i := 0) (j := 1) (by decide))

theorem nb091_fresh_230 (D : Class) (R : Class) :
    (nb091_alpha_dummy_047 D R) ∉
      (((syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
                  (syn_csn (syn_cuni (syn_cuni (Class.cv (nb091_alpha_dummy_000 D R)))))))
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (syn_cuni
                      (syn_cuni (Class.cv (nb091_alpha_dummy_000 D R)))))))))).fv ∪ ((syn_cin D
            (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn
                (syn_cuni (syn_cuni (Class.cv (nb091_alpha_dummy_000 D R)))))))).fv) :=
  by
  simpa only [nb091_alpha_dummy_047] using
    freshVar_not_mem
      (((syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
                  (syn_csn (syn_cuni (syn_cuni (Class.cv (nb091_alpha_dummy_000 D R)))))))
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (syn_cuni
                      (syn_cuni (Class.cv (nb091_alpha_dummy_000 D R)))))))))).fv ∪ ((syn_cin D
            (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn
                (syn_cuni (syn_cuni (Class.cv (nb091_alpha_dummy_000 D R)))))))).fv)
      0

theorem nb091_fresh_231 (D : Class) (R : Class) :
    (nb091_alpha_dummy_048 D R) ∉
      (((syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
                  (syn_csn (syn_cuni (syn_cuni (Class.cv (nb091_alpha_dummy_000 D R)))))))
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (syn_cuni
                      (syn_cuni (Class.cv (nb091_alpha_dummy_000 D R)))))))))).fv ∪ ((syn_cin D
            (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn
                (syn_cuni (syn_cuni (Class.cv (nb091_alpha_dummy_000 D R)))))))).fv) :=
  by
  simpa only [nb091_alpha_dummy_048] using
    freshVar_not_mem
      (((syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
                  (syn_csn (syn_cuni (syn_cuni (Class.cv (nb091_alpha_dummy_000 D R)))))))
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (syn_cuni
                      (syn_cuni (Class.cv (nb091_alpha_dummy_000 D R)))))))))).fv ∪ ((syn_cin D
            (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn
                (syn_cuni (syn_cuni (Class.cv (nb091_alpha_dummy_000 D R)))))))).fv)
      1

theorem nb091_distinct_232 (D : Class) (R : Class) :
    (nb091_alpha_dummy_047 D R) ≠ (nb091_alpha_dummy_048 D R) := by
  simpa only [nb091_alpha_dummy_047, nb091_alpha_dummy_048] using
    (freshVar_injective (((syn_cin R (syn_cxp (syn_cin D
                (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
                  (syn_csn (syn_cuni (syn_cuni (Class.cv (nb091_alpha_dummy_000 D R)))))))
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (syn_cuni
                      (syn_cuni (Class.cv (nb091_alpha_dummy_000 D R)))))))))).fv ∪ ((syn_cin D
            (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn
                (syn_cuni (syn_cuni (Class.cv (nb091_alpha_dummy_000 D R)))))))).fv)
      (i := 0) (j := 1) (by decide))

theorem nb091_fresh_233 (D : Class) (R : Class) (p : Var) :
    (nb091_alpha_dummy_049 D R p) ∉
      (((syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
                  (syn_csn (syn_cuni (syn_cuni (Class.cv p)))))) (syn_cin D
                (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
                  (syn_csn (syn_cuni (syn_cuni (Class.cv p))))))))).fv ∪ ((syn_cin D
            (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
              (syn_csn (syn_cuni (syn_cuni (Class.cv p))))))).fv) :=
  by
  simpa only [nb091_alpha_dummy_049] using
    freshVar_not_mem
      (((syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
                  (syn_csn (syn_cuni (syn_cuni (Class.cv p)))))) (syn_cin D
                (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
                  (syn_csn (syn_cuni (syn_cuni (Class.cv p))))))))).fv ∪ ((syn_cin D
            (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
              (syn_csn (syn_cuni (syn_cuni (Class.cv p))))))).fv)
      0

theorem nb091_fresh_234 (D : Class) (R : Class) (p : Var) :
    (nb091_alpha_dummy_050 D R p) ∉
      (((syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
                  (syn_csn (syn_cuni (syn_cuni (Class.cv p)))))) (syn_cin D
                (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
                  (syn_csn (syn_cuni (syn_cuni (Class.cv p))))))))).fv ∪ ((syn_cin D
            (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
              (syn_csn (syn_cuni (syn_cuni (Class.cv p))))))).fv) :=
  by
  simpa only [nb091_alpha_dummy_050] using
    freshVar_not_mem
      (((syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
                  (syn_csn (syn_cuni (syn_cuni (Class.cv p)))))) (syn_cin D
                (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
                  (syn_csn (syn_cuni (syn_cuni (Class.cv p))))))))).fv ∪ ((syn_cin D
            (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
              (syn_csn (syn_cuni (syn_cuni (Class.cv p))))))).fv)
      1

theorem nb091_distinct_235 (D : Class) (R : Class) (p : Var) :
    (nb091_alpha_dummy_049 D R p) ≠ (nb091_alpha_dummy_050 D R p) := by
  simpa only [nb091_alpha_dummy_049, nb091_alpha_dummy_050] using
    (freshVar_injective (((syn_cin R (syn_cxp (syn_cin D
                (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
                  (syn_csn (syn_cuni (syn_cuni (Class.cv p)))))) (syn_cin D
                (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
                  (syn_csn (syn_cuni (syn_cuni (Class.cv p))))))))).fv ∪ ((syn_cin D
            (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
              (syn_csn (syn_cuni (syn_cuni (Class.cv p))))))).fv) (i := 0) (j := 1) (by decide))

theorem nb091_fresh_236 (D : Class) (R : Class) :
    (nb091_alpha_dummy_025 D R) ∉
      (((syn_cnin (Class.cv (nb091_alpha_dummy_020 D R))
            (Class.cv (nb091_alpha_dummy_021 D R)))).fv ∪
        ((syn_cnin (Class.cv (nb091_alpha_dummy_020 D R))
            (Class.cv (nb091_alpha_dummy_021 D R)))).fv) :=
  by
  simpa only [nb091_alpha_dummy_025] using
    freshVar_not_mem
      (((syn_cnin (Class.cv (nb091_alpha_dummy_020 D R))
            (Class.cv (nb091_alpha_dummy_021 D R)))).fv ∪
        ((syn_cnin (Class.cv (nb091_alpha_dummy_020 D R))
            (Class.cv (nb091_alpha_dummy_021 D R)))).fv)
      0

theorem nb091_fresh_237 (D : Class) (R : Class) (p : Var) :
    (nb091_alpha_dummy_026 D R p) ∉
      (((syn_cnin (Class.cv (nb091_alpha_dummy_023 D R p))
            (Class.cv (nb091_alpha_dummy_024 D R p)))).fv ∪
        ((syn_cnin (Class.cv (nb091_alpha_dummy_023 D R p))
            (Class.cv (nb091_alpha_dummy_024 D R p)))).fv) :=
  by
  simpa only [nb091_alpha_dummy_026] using
    freshVar_not_mem
      (((syn_cnin (Class.cv (nb091_alpha_dummy_023 D R p))
            (Class.cv (nb091_alpha_dummy_024 D R p)))).fv ∪
        ((syn_cnin (Class.cv (nb091_alpha_dummy_023 D R p))
            (Class.cv (nb091_alpha_dummy_024 D R p)))).fv)
      0

theorem nb091_fresh_238 (D : Class) (R : Class) :
    (nb091_alpha_dummy_085 D R) ∉
      (((syn_cnin (Class.cv (nb091_alpha_dummy_080 D R))
            (Class.cv (nb091_alpha_dummy_081 D R)))).fv ∪
        ((syn_cnin (Class.cv (nb091_alpha_dummy_080 D R))
            (Class.cv (nb091_alpha_dummy_081 D R)))).fv) :=
  by
  simpa only [nb091_alpha_dummy_085] using
    freshVar_not_mem
      (((syn_cnin (Class.cv (nb091_alpha_dummy_080 D R))
            (Class.cv (nb091_alpha_dummy_081 D R)))).fv ∪
        ((syn_cnin (Class.cv (nb091_alpha_dummy_080 D R))
            (Class.cv (nb091_alpha_dummy_081 D R)))).fv)
      0

theorem nb091_fresh_239 (D : Class) (R : Class) (p : Var) :
    (nb091_alpha_dummy_086 D R p) ∉
      (((syn_cnin (Class.cv (nb091_alpha_dummy_083 D R p))
            (Class.cv (nb091_alpha_dummy_084 D R p)))).fv ∪
        ((syn_cnin (Class.cv (nb091_alpha_dummy_083 D R p))
            (Class.cv (nb091_alpha_dummy_084 D R p)))).fv) :=
  by
  simpa only [nb091_alpha_dummy_086] using
    freshVar_not_mem
      (((syn_cnin (Class.cv (nb091_alpha_dummy_083 D R p))
            (Class.cv (nb091_alpha_dummy_084 D R p)))).fv ∪
        ((syn_cnin (Class.cv (nb091_alpha_dummy_083 D R p))
            (Class.cv (nb091_alpha_dummy_084 D R p)))).fv)
      0

theorem nb091_fresh_240 (D : Class) (R : Class) :
    (nb091_alpha_dummy_139 D R) ∉
      (((syn_cnin (Class.cv (nb091_alpha_dummy_134 D R))
            (Class.cv (nb091_alpha_dummy_135 D R)))).fv ∪
        ((syn_cnin (Class.cv (nb091_alpha_dummy_134 D R))
            (Class.cv (nb091_alpha_dummy_135 D R)))).fv) :=
  by
  simpa only [nb091_alpha_dummy_139] using
    freshVar_not_mem
      (((syn_cnin (Class.cv (nb091_alpha_dummy_134 D R))
            (Class.cv (nb091_alpha_dummy_135 D R)))).fv ∪
        ((syn_cnin (Class.cv (nb091_alpha_dummy_134 D R))
            (Class.cv (nb091_alpha_dummy_135 D R)))).fv)
      0

theorem nb091_fresh_241 (R : Class) (p : Var) :
    (nb091_alpha_dummy_140 R p) ∉
      (((syn_cnin (Class.cv (nb091_alpha_dummy_137 R p))
            (Class.cv (nb091_alpha_dummy_138 R p)))).fv ∪
        ((syn_cnin (Class.cv (nb091_alpha_dummy_137 R p))
            (Class.cv (nb091_alpha_dummy_138 R p)))).fv) :=
  by
  simpa only [nb091_alpha_dummy_140] using
    freshVar_not_mem
      (((syn_cnin (Class.cv (nb091_alpha_dummy_137 R p))
            (Class.cv (nb091_alpha_dummy_138 R p)))).fv ∪
        ((syn_cnin (Class.cv (nb091_alpha_dummy_137 R p))
            (Class.cv (nb091_alpha_dummy_138 R p)))).fv)
      0

theorem nb091_fresh_242 (D : Class) (R : Class) :
    (nb091_alpha_dummy_167 D R) ∉
      (((syn_cnin (Class.cv (nb091_alpha_dummy_162 D R))
            (Class.cv (nb091_alpha_dummy_163 D R)))).fv ∪
        ((syn_cnin (Class.cv (nb091_alpha_dummy_162 D R))
            (Class.cv (nb091_alpha_dummy_163 D R)))).fv) :=
  by
  simpa only [nb091_alpha_dummy_167] using
    freshVar_not_mem
      (((syn_cnin (Class.cv (nb091_alpha_dummy_162 D R))
            (Class.cv (nb091_alpha_dummy_163 D R)))).fv ∪
        ((syn_cnin (Class.cv (nb091_alpha_dummy_162 D R))
            (Class.cv (nb091_alpha_dummy_163 D R)))).fv)
      0

theorem nb091_fresh_243 (D : Class) (R : Class) (p : Var) :
    (nb091_alpha_dummy_168 D R p) ∉
      (((syn_cnin (Class.cv (nb091_alpha_dummy_165 D R p))
            (Class.cv (nb091_alpha_dummy_166 D R p)))).fv ∪
        ((syn_cnin (Class.cv (nb091_alpha_dummy_165 D R p))
            (Class.cv (nb091_alpha_dummy_166 D R p)))).fv) :=
  by
  simpa only [nb091_alpha_dummy_168] using
    freshVar_not_mem
      (((syn_cnin (Class.cv (nb091_alpha_dummy_165 D R p))
            (Class.cv (nb091_alpha_dummy_166 D R p)))).fv ∪
        ((syn_cnin (Class.cv (nb091_alpha_dummy_165 D R p))
            (Class.cv (nb091_alpha_dummy_166 D R p)))).fv)
      0

theorem nb091_fresh_244 (D : Class) (R : Class) :
    (nb091_alpha_dummy_203 D R) ∉
      (((syn_cnin (Class.cv (nb091_alpha_dummy_198 D R))
            (Class.cv (nb091_alpha_dummy_199 D R)))).fv ∪
        ((syn_cnin (Class.cv (nb091_alpha_dummy_198 D R))
            (Class.cv (nb091_alpha_dummy_199 D R)))).fv) :=
  by
  simpa only [nb091_alpha_dummy_203] using
    freshVar_not_mem
      (((syn_cnin (Class.cv (nb091_alpha_dummy_198 D R))
            (Class.cv (nb091_alpha_dummy_199 D R)))).fv ∪
        ((syn_cnin (Class.cv (nb091_alpha_dummy_198 D R))
            (Class.cv (nb091_alpha_dummy_199 D R)))).fv)
      0

theorem nb091_fresh_245 (D : Class) (R : Class) (p : Var) :
    (nb091_alpha_dummy_204 D R p) ∉
      (((syn_cnin (Class.cv (nb091_alpha_dummy_201 D R p))
            (Class.cv (nb091_alpha_dummy_202 D R p)))).fv ∪
        ((syn_cnin (Class.cv (nb091_alpha_dummy_201 D R p))
            (Class.cv (nb091_alpha_dummy_202 D R p)))).fv) :=
  by
  simpa only [nb091_alpha_dummy_204] using
    freshVar_not_mem
      (((syn_cnin (Class.cv (nb091_alpha_dummy_201 D R p))
            (Class.cv (nb091_alpha_dummy_202 D R p)))).fv ∪
        ((syn_cnin (Class.cv (nb091_alpha_dummy_201 D R p))
            (Class.cv (nb091_alpha_dummy_202 D R p)))).fv)
      0

theorem nb091_fresh_246 (D : Class) (R : Class) :
    (nb091_alpha_dummy_101 D R) ∉
      (((syn_cnin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn
                (syn_cuni (syn_cuni (Class.cv (nb091_alpha_dummy_000 D R)))))))).fv ∪
        ((syn_cnin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn
                (syn_cuni (syn_cuni (Class.cv (nb091_alpha_dummy_000 D R)))))))).fv) :=
  by
  simpa only [nb091_alpha_dummy_101] using
    freshVar_not_mem
      (((syn_cnin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn
                (syn_cuni (syn_cuni (Class.cv (nb091_alpha_dummy_000 D R)))))))).fv ∪
        ((syn_cnin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn
                (syn_cuni (syn_cuni (Class.cv (nb091_alpha_dummy_000 D R)))))))).fv)
      0

theorem nb091_fresh_247 (D : Class) (R : Class) (p : Var) :
    (nb091_alpha_dummy_102 D R p) ∉
      (((syn_cnin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
              (syn_csn (syn_cuni (syn_cuni (Class.cv p))))))).fv ∪ ((syn_cnin D
            (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
              (syn_csn (syn_cuni (syn_cuni (Class.cv p))))))).fv) :=
  by
  simpa only [nb091_alpha_dummy_102] using
    freshVar_not_mem
      (((syn_cnin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
              (syn_csn (syn_cuni (syn_cuni (Class.cv p))))))).fv ∪ ((syn_cnin D
            (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
              (syn_csn (syn_cuni (syn_cuni (Class.cv p))))))).fv)
      0

theorem nb091_fresh_248 (D : Class) (R : Class) :
    (nb091_alpha_dummy_055 D R) ∉
      (((syn_cnin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
                  (syn_csn (syn_cuni (syn_cuni (Class.cv (nb091_alpha_dummy_000 D R)))))))
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (syn_cuni
                      (syn_cuni (Class.cv (nb091_alpha_dummy_000 D R)))))))))).fv ∪ ((syn_cnin R
            (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
                  (syn_csn (syn_cuni (syn_cuni (Class.cv (nb091_alpha_dummy_000 D R)))))))
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (syn_cuni
                      (syn_cuni (Class.cv (nb091_alpha_dummy_000 D R)))))))))).fv) :=
  by
  simpa only [nb091_alpha_dummy_055] using
    freshVar_not_mem
      (((syn_cnin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
                  (syn_csn (syn_cuni (syn_cuni (Class.cv (nb091_alpha_dummy_000 D R)))))))
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (syn_cuni
                      (syn_cuni (Class.cv (nb091_alpha_dummy_000 D R)))))))))).fv ∪ ((syn_cnin R
            (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
                  (syn_csn (syn_cuni (syn_cuni (Class.cv (nb091_alpha_dummy_000 D R)))))))
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn
                    (syn_cuni (syn_cuni (Class.cv (nb091_alpha_dummy_000 D R)))))))))).fv)
      0

theorem nb091_fresh_249 (D : Class) (R : Class) (p : Var) :
    (nb091_alpha_dummy_056 D R p) ∉
      (((syn_cnin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
                  (syn_csn (syn_cuni (syn_cuni (Class.cv p)))))) (syn_cin D
                (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
                  (syn_csn (syn_cuni (syn_cuni (Class.cv p))))))))).fv ∪ ((syn_cnin R (syn_cxp
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
                  (syn_csn (syn_cuni (syn_cuni (Class.cv p)))))) (syn_cin D
                (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
                  (syn_csn (syn_cuni (syn_cuni (Class.cv p))))))))).fv) :=
  by
  simpa only [nb091_alpha_dummy_056] using
    freshVar_not_mem
      (((syn_cnin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
                  (syn_csn (syn_cuni (syn_cuni (Class.cv p)))))) (syn_cin D
                (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
                  (syn_csn (syn_cuni (syn_cuni (Class.cv p))))))))).fv ∪ ((syn_cnin R (syn_cxp
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
                  (syn_csn (syn_cuni (syn_cuni (Class.cv p)))))) (syn_cin D
                (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
                  (syn_csn (syn_cuni (syn_cuni (Class.cv p))))))))).fv)
      0

theorem nb091_fresh_250 (D : Class) (R : Class) :
    (nb091_alpha_dummy_039 D R) ∉
      (((syn_cphi (Class.cv (nb091_alpha_dummy_006 D R)))).fv ∪
        ((syn_cphi (Class.cv (nb091_alpha_dummy_006 D R)))).fv) :=
  by
  simpa only [nb091_alpha_dummy_039] using
    freshVar_not_mem
      (((syn_cphi (Class.cv (nb091_alpha_dummy_006 D R)))).fv ∪
        ((syn_cphi (Class.cv (nb091_alpha_dummy_006 D R)))).fv)
      0

theorem nb091_fresh_251 (D : Class) (R : Class) (p : Var) :
    (nb091_alpha_dummy_040 D R p) ∉
      (((syn_cphi (Class.cv (nb091_alpha_dummy_008 D R p)))).fv ∪
        ((syn_cphi (Class.cv (nb091_alpha_dummy_008 D R p)))).fv) :=
  by
  simpa only [nb091_alpha_dummy_040] using
    freshVar_not_mem
      (((syn_cphi (Class.cv (nb091_alpha_dummy_008 D R p)))).fv ∪
        ((syn_cphi (Class.cv (nb091_alpha_dummy_008 D R p)))).fv)
      0

theorem nb091_fresh_252 (D : Class) (R : Class) :
    (nb091_alpha_dummy_181 D R) ∉
      (((syn_cphi (Class.cv (nb091_alpha_dummy_048 D R)))).fv ∪
        ((syn_cphi (Class.cv (nb091_alpha_dummy_048 D R)))).fv) :=
  by
  simpa only [nb091_alpha_dummy_181] using
    freshVar_not_mem
      (((syn_cphi (Class.cv (nb091_alpha_dummy_048 D R)))).fv ∪
        ((syn_cphi (Class.cv (nb091_alpha_dummy_048 D R)))).fv)
      0

theorem nb091_fresh_253 (D : Class) (R : Class) (p : Var) :
    (nb091_alpha_dummy_182 D R p) ∉
      (((syn_cphi (Class.cv (nb091_alpha_dummy_050 D R p)))).fv ∪
        ((syn_cphi (Class.cv (nb091_alpha_dummy_050 D R p)))).fv) :=
  by
  simpa only [nb091_alpha_dummy_182] using
    freshVar_not_mem
      (((syn_cphi (Class.cv (nb091_alpha_dummy_050 D R p)))).fv ∪
        ((syn_cphi (Class.cv (nb091_alpha_dummy_050 D R p)))).fv)
      0

theorem nb091_fresh_254 (D : Class) (R : Class) :
    (nb091_alpha_dummy_099 D R) ∉
      (((syn_cphi (Class.cv (nb091_alpha_dummy_066 D R)))).fv ∪
        ((syn_cphi (Class.cv (nb091_alpha_dummy_066 D R)))).fv) :=
  by
  simpa only [nb091_alpha_dummy_099] using
    freshVar_not_mem
      (((syn_cphi (Class.cv (nb091_alpha_dummy_066 D R)))).fv ∪
        ((syn_cphi (Class.cv (nb091_alpha_dummy_066 D R)))).fv)
      0

theorem nb091_fresh_255 (D : Class) (R : Class) (p : Var) :
    (nb091_alpha_dummy_100 D R p) ∉
      (((syn_cphi (Class.cv (nb091_alpha_dummy_068 D R p)))).fv ∪
        ((syn_cphi (Class.cv (nb091_alpha_dummy_068 D R p)))).fv) :=
  by
  simpa only [nb091_alpha_dummy_100] using
    freshVar_not_mem
      (((syn_cphi (Class.cv (nb091_alpha_dummy_068 D R p)))).fv ∪
        ((syn_cphi (Class.cv (nb091_alpha_dummy_068 D R p)))).fv)
      0

theorem nb091_fresh_256 (D : Class) (R : Class) :
    (nb091_alpha_dummy_153 D R) ∉
      (((syn_cphi (Class.cv (nb091_alpha_dummy_120 D R)))).fv ∪
        ((syn_cphi (Class.cv (nb091_alpha_dummy_120 D R)))).fv) :=
  by
  simpa only [nb091_alpha_dummy_153] using
    freshVar_not_mem
      (((syn_cphi (Class.cv (nb091_alpha_dummy_120 D R)))).fv ∪
        ((syn_cphi (Class.cv (nb091_alpha_dummy_120 D R)))).fv)
      0

theorem nb091_fresh_257 (R : Class) (p : Var) :
    (nb091_alpha_dummy_154 R p) ∉
      (((syn_cphi (Class.cv (nb091_alpha_dummy_122 R p)))).fv ∪
        ((syn_cphi (Class.cv (nb091_alpha_dummy_122 R p)))).fv) :=
  by
  simpa only [nb091_alpha_dummy_154] using
    freshVar_not_mem
      (((syn_cphi (Class.cv (nb091_alpha_dummy_122 R p)))).fv ∪
        ((syn_cphi (Class.cv (nb091_alpha_dummy_122 R p)))).fv)
      0

theorem nb091_fresh_258 (D : Class) (R : Class) :
    (nb091_alpha_dummy_217 D R) ∉
      (((syn_cphi (Class.cv (nb091_alpha_dummy_184 D R)))).fv ∪
        ((syn_cphi (Class.cv (nb091_alpha_dummy_184 D R)))).fv) :=
  by
  simpa only [nb091_alpha_dummy_217] using
    freshVar_not_mem
      (((syn_cphi (Class.cv (nb091_alpha_dummy_184 D R)))).fv ∪
        ((syn_cphi (Class.cv (nb091_alpha_dummy_184 D R)))).fv)
      0

theorem nb091_fresh_259 (D : Class) (R : Class) (p : Var) :
    (nb091_alpha_dummy_218 D R p) ∉
      (((syn_cphi (Class.cv (nb091_alpha_dummy_186 D R p)))).fv ∪
        ((syn_cphi (Class.cv (nb091_alpha_dummy_186 D R p)))).fv) :=
  by
  simpa only [nb091_alpha_dummy_218] using
    freshVar_not_mem
      (((syn_cphi (Class.cv (nb091_alpha_dummy_186 D R p)))).fv ∪
        ((syn_cphi (Class.cv (nb091_alpha_dummy_186 D R p)))).fv)
      0

theorem nb091_fresh_260 (D : Class) (R : Class) :
    (nb091_alpha_dummy_111 D R) ∉
      (((syn_cuni (Class.cv (nb091_alpha_dummy_000 D R)))).fv) :=
  by
  simpa only [nb091_alpha_dummy_111] using
    freshVar_not_mem (((syn_cuni (Class.cv (nb091_alpha_dummy_000 D R)))).fv) 0

theorem nb091_fresh_261 (D : Class) (R : Class) :
    (nb091_alpha_dummy_112 D R) ∉
      (((syn_cuni (Class.cv (nb091_alpha_dummy_000 D R)))).fv) :=
  by
  simpa only [nb091_alpha_dummy_112] using
    freshVar_not_mem (((syn_cuni (Class.cv (nb091_alpha_dummy_000 D R)))).fv) 1

theorem nb091_distinct_262 (D : Class) (R : Class) :
    (nb091_alpha_dummy_111 D R) ≠ (nb091_alpha_dummy_112 D R) := by
  simpa only [nb091_alpha_dummy_111, nb091_alpha_dummy_112] using
    (freshVar_injective (((syn_cuni (Class.cv (nb091_alpha_dummy_000 D R)))).fv) (i := 0)
      (j := 1) (by decide))

theorem nb091_fresh_263 (p : Var) :
    (nb091_alpha_dummy_113 p) ∉ (((syn_cuni (Class.cv p))).fv) := by
  simpa only [nb091_alpha_dummy_113] using
    freshVar_not_mem (((syn_cuni (Class.cv p))).fv) 0

theorem nb091_fresh_264 (p : Var) :
    (nb091_alpha_dummy_114 p) ∉ (((syn_cuni (Class.cv p))).fv) := by
  simpa only [nb091_alpha_dummy_114] using
    freshVar_not_mem (((syn_cuni (Class.cv p))).fv) 1

theorem nb091_distinct_265 (p : Var) :
    (nb091_alpha_dummy_113 p) ≠ (nb091_alpha_dummy_114 p) := by
  simpa only [nb091_alpha_dummy_113, nb091_alpha_dummy_114] using
    (freshVar_injective (((syn_cuni (Class.cv p))).fv) (i := 0) (j := 1) (by decide))

theorem nb091_fresh_266 (D : Class) (R : Class) :
    (nb091_alpha_dummy_109 D R) ∉
      (((syn_cuni (syn_cuni (Class.cv (nb091_alpha_dummy_000 D R))))).fv) :=
  by
  simpa only [nb091_alpha_dummy_109] using
    freshVar_not_mem (((syn_cuni (syn_cuni (Class.cv (nb091_alpha_dummy_000 D R))))).fv) 0

theorem nb091_fresh_267 (p : Var) :
    (nb091_alpha_dummy_110 p) ∉ (((syn_cuni (syn_cuni (Class.cv p)))).fv) := by
  simpa only [nb091_alpha_dummy_110] using
    freshVar_not_mem (((syn_cuni (syn_cuni (Class.cv p)))).fv) 0

theorem nb091_fresh_268 (D : Class) (R : Class) :
    (nb091_alpha_dummy_103 D R) ∉
      ((D).fv ∪ ((syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn
              (syn_cuni (syn_cuni (Class.cv (nb091_alpha_dummy_000 D R))))))).fv) :=
  by
  simpa only [nb091_alpha_dummy_103] using
    freshVar_not_mem
      ((D).fv ∪ ((syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
            (syn_csn (syn_cuni (syn_cuni (Class.cv (nb091_alpha_dummy_000 D R))))))).fv)
      0

theorem nb091_fresh_269 (D : Class) (R : Class) (p : Var) :
    (nb091_alpha_dummy_104 D R p) ∉
      ((D).fv ∪ ((syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
            (syn_csn (syn_cuni (syn_cuni (Class.cv p)))))).fv) :=
  by
  simpa only [nb091_alpha_dummy_104] using
    freshVar_not_mem
      ((D).fv ∪ ((syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
            (syn_csn (syn_cuni (syn_cuni (Class.cv p)))))).fv)
      0

theorem nb091_fresh_270 (D : Class) (R : Class) :
    (nb091_alpha_dummy_057 D R) ∉
      ((R).fv ∪ ((syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
                (syn_csn (syn_cuni (syn_cuni (Class.cv (nb091_alpha_dummy_000 D R)))))))
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn
                  (syn_cuni (syn_cuni (Class.cv (nb091_alpha_dummy_000 D R))))))))).fv) :=
  by
  simpa only [nb091_alpha_dummy_057] using
    freshVar_not_mem
      ((R).fv ∪ ((syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
                (syn_csn (syn_cuni (syn_cuni (Class.cv (nb091_alpha_dummy_000 D R)))))))
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn
                  (syn_cuni (syn_cuni (Class.cv (nb091_alpha_dummy_000 D R))))))))).fv)
      0

theorem nb091_fresh_271 (D : Class) (R : Class) (p : Var) :
    (nb091_alpha_dummy_058 D R p) ∉
      ((R).fv ∪ ((syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
                (syn_csn (syn_cuni (syn_cuni (Class.cv p)))))) (syn_cin D
              (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
                (syn_csn (syn_cuni (syn_cuni (Class.cv p)))))))).fv) :=
  by
  simpa only [nb091_alpha_dummy_058] using
    freshVar_not_mem
      ((R).fv ∪ ((syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
                (syn_csn (syn_cuni (syn_cuni (Class.cv p)))))) (syn_cin D
              (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
                (syn_csn (syn_cuni (syn_cuni (Class.cv p)))))))).fv)
      0

theorem nb091_fresh_272 (D : Class) (R : Class) :
    (nb091_alpha_dummy_000 D R) ∉ ((R).fv ∪ (D).fv) := by
  simpa only [nb091_alpha_dummy_000] using freshVar_not_mem ((R).fv ∪ (D).fv) 0

theorem nb091_fresh_273 (D : Class) (R : Class) :
    (nb091_alpha_dummy_001 D R) ∉
      (({(nb091_alpha_dummy_000 D R)} : Finset Var) ∪ ((syn_cpw1 (syn_cpw1 D))).fv ∪ ((syn_cec
            (syn_chnwcutcode R D (syn_cuni (syn_cuni (Class.cv (nb091_alpha_dummy_000 D R)))))
            (syn_chwniso D))).fv) :=
  by
  simpa only [nb091_alpha_dummy_001] using
    freshVar_not_mem
      (({(nb091_alpha_dummy_000 D R)} : Finset Var) ∪ ((syn_cpw1 (syn_cpw1 D))).fv ∪ ((syn_cec
            (syn_chnwcutcode R D (syn_cuni (syn_cuni (Class.cv (nb091_alpha_dummy_000 D R)))))
            (syn_chwniso D))).fv)
      0

theorem nb091_fresh_274 (D : Class) (R : Class) :
    (nb091_alpha_dummy_003 D R) ∉
      (({(nb091_alpha_dummy_000 D R)} : Finset Var) ∪
          ({(nb091_alpha_dummy_001 D R)} : Finset Var) ∪ ((syn_wa
            (Wff.classMem (Class.cv (nb091_alpha_dummy_000 D R)) (syn_cpw1 (syn_cpw1 D)))
            (Wff.classEq (Class.cv (nb091_alpha_dummy_001 D R)) (syn_cec (syn_chnwcutcode R D
                  (syn_cuni (syn_cuni (Class.cv (nb091_alpha_dummy_000 D R)))))
                (syn_chwniso D))))).fv) :=
  by
  simpa only [nb091_alpha_dummy_003] using
    freshVar_not_mem
      (({(nb091_alpha_dummy_000 D R)} : Finset Var) ∪
          ({(nb091_alpha_dummy_001 D R)} : Finset Var) ∪ ((syn_wa
            (Wff.classMem (Class.cv (nb091_alpha_dummy_000 D R)) (syn_cpw1 (syn_cpw1 D)))
            (Wff.classEq (Class.cv (nb091_alpha_dummy_001 D R)) (syn_cec (syn_chnwcutcode R D
                  (syn_cuni (syn_cuni (Class.cv (nb091_alpha_dummy_000 D R)))))
                (syn_chwniso D))))).fv)
      0

theorem nb091_fresh_275 (D : Class) (R : Class) :
    (nb091_alpha_dummy_063 D R) ∉
      (({(nb091_alpha_dummy_059 D R)} : Finset Var) ∪
          ({(nb091_alpha_dummy_060 D R)} : Finset Var) ∪ ((syn_wa
            (Wff.classMem (Class.cv (nb091_alpha_dummy_059 D R)) (syn_cin D
                (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn
                    (syn_cuni (syn_cuni (Class.cv (nb091_alpha_dummy_000 D R))))))))
            (Wff.classMem (Class.cv (nb091_alpha_dummy_060 D R)) (syn_cin D
                (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (syn_cuni
                      (syn_cuni (Class.cv (nb091_alpha_dummy_000 D R)))))))))).fv) :=
  by
  simpa only [nb091_alpha_dummy_063] using
    freshVar_not_mem
      (({(nb091_alpha_dummy_059 D R)} : Finset Var) ∪
          ({(nb091_alpha_dummy_060 D R)} : Finset Var) ∪ ((syn_wa
            (Wff.classMem (Class.cv (nb091_alpha_dummy_059 D R)) (syn_cin D
                (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn
                    (syn_cuni (syn_cuni (Class.cv (nb091_alpha_dummy_000 D R))))))))
            (Wff.classMem (Class.cv (nb091_alpha_dummy_060 D R)) (syn_cin D
                (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn
                    (syn_cuni (syn_cuni (Class.cv (nb091_alpha_dummy_000 D R)))))))))).fv)
      0

theorem nb091_fresh_276 (D : Class) (R : Class) (p : Var) :
    (nb091_alpha_dummy_064 D R p) ∉
      (({(nb091_alpha_dummy_061 D R p)} : Finset Var) ∪
          ({(nb091_alpha_dummy_062 D R p)} : Finset Var) ∪ ((syn_wa
            (Wff.classMem (Class.cv (nb091_alpha_dummy_061 D R p)) (syn_cin D
                (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
                  (syn_csn (syn_cuni (syn_cuni (Class.cv p)))))))
            (Wff.classMem (Class.cv (nb091_alpha_dummy_062 D R p)) (syn_cin D
                (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
                  (syn_csn (syn_cuni (syn_cuni (Class.cv p))))))))).fv) :=
  by
  simpa only [nb091_alpha_dummy_064] using
    freshVar_not_mem
      (({(nb091_alpha_dummy_061 D R p)} : Finset Var) ∪
          ({(nb091_alpha_dummy_062 D R p)} : Finset Var) ∪ ((syn_wa
            (Wff.classMem (Class.cv (nb091_alpha_dummy_061 D R p)) (syn_cin D
                (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
                  (syn_csn (syn_cuni (syn_cuni (Class.cv p)))))))
            (Wff.classMem (Class.cv (nb091_alpha_dummy_062 D R p)) (syn_cin D
                (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
                  (syn_csn (syn_cuni (syn_cuni (Class.cv p))))))))).fv)
      0

theorem nb091_fresh_277 (D : Class) (R : Class) (p : Var) :
    (nb091_alpha_dummy_002 D R p) ∉
      (({ p } : Finset Var) ∪ ((syn_cpw1 (syn_cpw1 D))).fv ∪
        ((syn_cec (syn_chnwcutcode R D (syn_cuni (syn_cuni (Class.cv p))))
            (syn_chwniso D))).fv) :=
  by
  simpa only [nb091_alpha_dummy_002] using
    freshVar_not_mem
      (({ p } : Finset Var) ∪ ((syn_cpw1 (syn_cpw1 D))).fv ∪
        ((syn_cec (syn_chnwcutcode R D (syn_cuni (syn_cuni (Class.cv p)))) (syn_chwniso D))).fv)
      0

theorem nb091_fresh_278 (D : Class) (R : Class) (p : Var) :
    (nb091_alpha_dummy_004 D R p) ∉
      (({ p } : Finset Var) ∪ ({(nb091_alpha_dummy_002 D R p)} : Finset Var) ∪
        ((syn_wa (Wff.classMem (Class.cv p) (syn_cpw1 (syn_cpw1 D)))
            (Wff.classEq (Class.cv (nb091_alpha_dummy_002 D R p))
              (syn_cec (syn_chnwcutcode R D (syn_cuni (syn_cuni (Class.cv p))))
                (syn_chwniso D))))).fv) :=
  by
  simpa only [nb091_alpha_dummy_004] using
    freshVar_not_mem
      (({ p } : Finset Var) ∪ ({(nb091_alpha_dummy_002 D R p)} : Finset Var) ∪
        ((syn_wa (Wff.classMem (Class.cv p) (syn_cpw1 (syn_cpw1 D)))
            (Wff.classEq (Class.cv (nb091_alpha_dummy_002 D R p))
              (syn_cec (syn_chnwcutcode R D (syn_cuni (syn_cuni (Class.cv p))))
                (syn_chwniso D))))).fv)
      0

theorem nb091_support_mem_0000 (D : Class) (R : Class) :
    (nb091_alpha_dummy_000 D R) ∈
      (({(nb091_alpha_dummy_000 D R)} : Finset Var) ∪
          ({(nb091_alpha_dummy_001 D R)} : Finset Var) ∪ ((syn_wa
            (Wff.classMem (Class.cv (nb091_alpha_dummy_000 D R)) (syn_cpw1 (syn_cpw1 D)))
            (Wff.classEq (Class.cv (nb091_alpha_dummy_001 D R)) (syn_cec (syn_chnwcutcode R D
                  (syn_cuni (syn_cuni (Class.cv (nb091_alpha_dummy_000 D R)))))
                (syn_chwniso D))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  with_reducible rw [Finset.mem_union]
  left
  exact Finset.mem_singleton_self _

theorem nb091_support_mem_0001 (D : Class) (R : Class) (p : Var) :
    p ∈
      (({ p } : Finset Var) ∪ ({(nb091_alpha_dummy_002 D R p)} : Finset Var) ∪
        ((syn_wa (Wff.classMem (Class.cv p) (syn_cpw1 (syn_cpw1 D)))
            (Wff.classEq (Class.cv (nb091_alpha_dummy_002 D R p))
              (syn_cec (syn_chnwcutcode R D (syn_cuni (syn_cuni (Class.cv p))))
                (syn_chwniso D))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  with_reducible rw [Finset.mem_union]
  left
  exact Finset.mem_singleton_self _

theorem nb091_support_mem_0002 (D : Class) (R : Class) :
    (nb091_alpha_dummy_001 D R) ∈
      (({(nb091_alpha_dummy_000 D R)} : Finset Var) ∪
          ({(nb091_alpha_dummy_001 D R)} : Finset Var) ∪ ((syn_wa
            (Wff.classMem (Class.cv (nb091_alpha_dummy_000 D R)) (syn_cpw1 (syn_cpw1 D)))
            (Wff.classEq (Class.cv (nb091_alpha_dummy_001 D R)) (syn_cec (syn_chnwcutcode R D
                  (syn_cuni (syn_cuni (Class.cv (nb091_alpha_dummy_000 D R)))))
                (syn_chwniso D))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  with_reducible rw [Finset.mem_union]
  right
  exact Finset.mem_singleton_self _

theorem nb091_support_mem_0003 (D : Class) (R : Class) (p : Var) :
    (nb091_alpha_dummy_002 D R p) ∈
      (({ p } : Finset Var) ∪ ({(nb091_alpha_dummy_002 D R p)} : Finset Var) ∪
        ((syn_wa (Wff.classMem (Class.cv p) (syn_cpw1 (syn_cpw1 D)))
            (Wff.classEq (Class.cv (nb091_alpha_dummy_002 D R p))
              (syn_cec (syn_chnwcutcode R D (syn_cuni (syn_cuni (Class.cv p))))
                (syn_chwniso D))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  with_reducible rw [Finset.mem_union]
  right
  exact Finset.mem_singleton_self _

theorem nb091_support_mem_0004 (D : Class) (R : Class) :
    (nb091_alpha_dummy_000 D R) ∈
      (({(nb091_alpha_dummy_000 D R)} : Finset Var) ∪ ((syn_cpw1 (syn_cpw1 D))).fv ∪ ((syn_cec
            (syn_chnwcutcode R D (syn_cuni (syn_cuni (Class.cv (nb091_alpha_dummy_000 D R)))))
            (syn_chwniso D))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  with_reducible rw [Finset.mem_union]
  left
  exact Finset.mem_singleton_self _

theorem nb091_support_mem_0005 (D : Class) (R : Class) (p : Var) :
    p ∈
      (({ p } : Finset Var) ∪ ((syn_cpw1 (syn_cpw1 D))).fv ∪
        ((syn_cec (syn_chnwcutcode R D (syn_cuni (syn_cuni (Class.cv p))))
            (syn_chwniso D))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  with_reducible rw [Finset.mem_union]
  left
  exact Finset.mem_singleton_self _

theorem nb091_support_mem_0006 (D : Class) (R : Class) :
    (nb091_alpha_dummy_000 D R) ∈
      (((Class.cv (nb091_alpha_dummy_000 D R))).fv ∪
        ((Class.cv (nb091_alpha_dummy_001 D R))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb091_support_mem_0007 (D : Class) (R : Class) :
    (nb091_alpha_dummy_000 D R) ∈
      (((syn_ccompl (Class.cab (nb091_alpha_dummy_005 D R)
              (syn_wrex (nb091_alpha_dummy_006 D R) (Class.cv (nb091_alpha_dummy_000 D R))
                (Wff.classEq (Class.cv (nb091_alpha_dummy_005 D R))
                  (syn_cphi (Class.cv (nb091_alpha_dummy_006 D R)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb091_alpha_dummy_005 D R)
              (syn_wrex (nb091_alpha_dummy_006 D R) (Class.cv (nb091_alpha_dummy_001 D R))
                (Wff.classEq (Class.cv (nb091_alpha_dummy_005 D R))
                  (syn_cun (syn_cphi (Class.cv (nb091_alpha_dummy_006 D R)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb091_alpha_dummy_000 D R) ≠ (nb091_alpha_dummy_005 D R) from (by
          unfold nb091_alpha_dummy_005;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb091_support_mem_0006 D R) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb091_alpha_dummy_000 D R) ≠ (nb091_alpha_dummy_006 D R) from (by
            unfold nb091_alpha_dummy_006;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb091_support_mem_0006 D R) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb091_support_mem_0008 (D : Class) (R : Class) (p : Var) :
    p ∈ (((Class.cv p)).fv ∪ ((Class.cv (nb091_alpha_dummy_002 D R p))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb091_support_mem_0009 (D : Class) (R : Class) (p : Var) :
    p ∈
      (((syn_ccompl (Class.cab (nb091_alpha_dummy_007 D R p)
              (syn_wrex (nb091_alpha_dummy_008 D R p) (Class.cv p)
                (Wff.classEq (Class.cv (nb091_alpha_dummy_007 D R p))
                  (syn_cphi (Class.cv (nb091_alpha_dummy_008 D R p)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb091_alpha_dummy_007 D R p) (syn_wrex (nb091_alpha_dummy_008 D R p)
                (Class.cv (nb091_alpha_dummy_002 D R p))
                (Wff.classEq (Class.cv (nb091_alpha_dummy_007 D R p))
                  (syn_cun (syn_cphi (Class.cv (nb091_alpha_dummy_008 D R p)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show p ≠ (nb091_alpha_dummy_007 D R p) from (by
          unfold nb091_alpha_dummy_007;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb091_support_mem_0008 D R p) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show p ≠ (nb091_alpha_dummy_008 D R p) from (by
            unfold nb091_alpha_dummy_008;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb091_support_mem_0008 D R p) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb091_support_mem_0010 (D : Class) (R : Class) :
    (nb091_alpha_dummy_000 D R) ∈
      (((Class.cab (nb091_alpha_dummy_005 D R)
            (syn_wrex (nb091_alpha_dummy_006 D R) (Class.cv (nb091_alpha_dummy_000 D R))
              (Wff.classEq (Class.cv (nb091_alpha_dummy_005 D R))
                (syn_cphi (Class.cv (nb091_alpha_dummy_006 D R))))))).fv ∪
        ((Class.cab (nb091_alpha_dummy_005 D R)
            (syn_wrex (nb091_alpha_dummy_006 D R) (Class.cv (nb091_alpha_dummy_000 D R))
              (Wff.classEq (Class.cv (nb091_alpha_dummy_005 D R))
                (syn_cphi (Class.cv (nb091_alpha_dummy_006 D R))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb091_alpha_dummy_000 D R) ≠ (nb091_alpha_dummy_005 D R) from (by
          unfold nb091_alpha_dummy_005;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb091_support_mem_0006 D R) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb091_alpha_dummy_000 D R) ≠ (nb091_alpha_dummy_006 D R) from (by
            unfold nb091_alpha_dummy_006;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb091_support_mem_0006 D R) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb091_support_mem_0011 (D : Class) (R : Class) (p : Var) :
    p ∈
      (((Class.cab (nb091_alpha_dummy_007 D R p)
            (syn_wrex (nb091_alpha_dummy_008 D R p) (Class.cv p)
              (Wff.classEq (Class.cv (nb091_alpha_dummy_007 D R p))
                (syn_cphi (Class.cv (nb091_alpha_dummy_008 D R p))))))).fv ∪
        ((Class.cab (nb091_alpha_dummy_007 D R p)
            (syn_wrex (nb091_alpha_dummy_008 D R p) (Class.cv p)
              (Wff.classEq (Class.cv (nb091_alpha_dummy_007 D R p))
                (syn_cphi (Class.cv (nb091_alpha_dummy_008 D R p))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show p ≠ (nb091_alpha_dummy_007 D R p) from (by
          unfold nb091_alpha_dummy_007;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb091_support_mem_0008 D R p) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show p ≠ (nb091_alpha_dummy_008 D R p) from (by
            unfold nb091_alpha_dummy_008;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb091_support_mem_0008 D R p) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb091_support_mem_0012 (D : Class) (R : Class) :
    (nb091_alpha_dummy_006 D R) ∈ (((Class.cv (nb091_alpha_dummy_006 D R))).fv) :=
  by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb091_support_mem_0013 (D : Class) (R : Class) (p : Var) :
    (nb091_alpha_dummy_008 D R p) ∈ (((Class.cv (nb091_alpha_dummy_008 D R p))).fv) :=
  by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb091_support_mem_0014 (D : Class) (R : Class) :
    (nb091_alpha_dummy_013 D R) ∈
      (((Wff.classMem (Class.cv (nb091_alpha_dummy_013 D R)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb091_alpha_dummy_013 D R)) (syn_c1c))).fv ∪
        ((Class.cv (nb091_alpha_dummy_013 D R))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_wff_classMem]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb091_support_mem_0015 (D : Class) (R : Class) (p : Var) :
    (nb091_alpha_dummy_015 D R p) ∈
      (((Wff.classMem (Class.cv (nb091_alpha_dummy_015 D R p)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb091_alpha_dummy_015 D R p)) (syn_c1c))).fv ∪
        ((Class.cv (nb091_alpha_dummy_015 D R p))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_wff_classMem]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb091_support_mem_0016 (D : Class) (R : Class) :
    (nb091_alpha_dummy_013 D R) ∈
      (((Class.cv (nb091_alpha_dummy_013 D R))).fv ∪ ((syn_c1c)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb091_support_mem_0017 (D : Class) (R : Class) (p : Var) :
    (nb091_alpha_dummy_015 D R p) ∈
      (((Class.cv (nb091_alpha_dummy_015 D R p))).fv ∪ ((syn_c1c)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb091_support_mem_0018 (D : Class) (R : Class) :
    (nb091_alpha_dummy_020 D R) ∈
      (((syn_cnin (Class.cv (nb091_alpha_dummy_020 D R))
            (Class.cv (nb091_alpha_dummy_021 D R)))).fv ∪
        ((syn_cnin (Class.cv (nb091_alpha_dummy_020 D R))
            (Class.cv (nb091_alpha_dummy_021 D R)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb091_support_mem_0019 (D : Class) (R : Class) (p : Var) :
    (nb091_alpha_dummy_023 D R p) ∈
      (((syn_cnin (Class.cv (nb091_alpha_dummy_023 D R p))
            (Class.cv (nb091_alpha_dummy_024 D R p)))).fv ∪
        ((syn_cnin (Class.cv (nb091_alpha_dummy_023 D R p))
            (Class.cv (nb091_alpha_dummy_024 D R p)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb091_support_mem_0020 (D : Class) (R : Class) :
    (nb091_alpha_dummy_020 D R) ∈
      (((Class.cv (nb091_alpha_dummy_020 D R))).fv ∪
        ((Class.cv (nb091_alpha_dummy_021 D R))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb091_support_mem_0021 (D : Class) (R : Class) (p : Var) :
    (nb091_alpha_dummy_023 D R p) ∈
      (((Class.cv (nb091_alpha_dummy_023 D R p))).fv ∪
        ((Class.cv (nb091_alpha_dummy_024 D R p))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb091_support_mem_0022 (D : Class) (R : Class) :
    (nb091_alpha_dummy_021 D R) ∈
      (((syn_cnin (Class.cv (nb091_alpha_dummy_020 D R))
            (Class.cv (nb091_alpha_dummy_021 D R)))).fv ∪
        ((syn_cnin (Class.cv (nb091_alpha_dummy_020 D R))
            (Class.cv (nb091_alpha_dummy_021 D R)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb091_support_mem_0023 (D : Class) (R : Class) (p : Var) :
    (nb091_alpha_dummy_024 D R p) ∈
      (((syn_cnin (Class.cv (nb091_alpha_dummy_023 D R p))
            (Class.cv (nb091_alpha_dummy_024 D R p)))).fv ∪
        ((syn_cnin (Class.cv (nb091_alpha_dummy_023 D R p))
            (Class.cv (nb091_alpha_dummy_024 D R p)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb091_support_mem_0024 (D : Class) (R : Class) :
    (nb091_alpha_dummy_021 D R) ∈
      (((Class.cv (nb091_alpha_dummy_020 D R))).fv ∪
        ((Class.cv (nb091_alpha_dummy_021 D R))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb091_support_mem_0025 (D : Class) (R : Class) (p : Var) :
    (nb091_alpha_dummy_024 D R p) ∈
      (((Class.cv (nb091_alpha_dummy_023 D R p))).fv ∪
        ((Class.cv (nb091_alpha_dummy_024 D R p))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb091_support_mem_0026 (D : Class) (R : Class) :
    (nb091_alpha_dummy_020 D R) ∈
      (((syn_ccompl (Class.cv (nb091_alpha_dummy_020 D R)))).fv ∪
        ((syn_ccompl (Class.cv (nb091_alpha_dummy_021 D R)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb091_support_mem_0027 (D : Class) (R : Class) (p : Var) :
    (nb091_alpha_dummy_023 D R p) ∈
      (((syn_ccompl (Class.cv (nb091_alpha_dummy_023 D R p)))).fv ∪
        ((syn_ccompl (Class.cv (nb091_alpha_dummy_024 D R p)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb091_support_mem_0028 (D : Class) (R : Class) :
    (nb091_alpha_dummy_020 D R) ∈
      (((Class.cv (nb091_alpha_dummy_020 D R))).fv ∪
        ((Class.cv (nb091_alpha_dummy_020 D R))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb091_support_mem_0029 (D : Class) (R : Class) (p : Var) :
    (nb091_alpha_dummy_023 D R p) ∈
      (((Class.cv (nb091_alpha_dummy_023 D R p))).fv ∪
        ((Class.cv (nb091_alpha_dummy_023 D R p))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb091_support_mem_0030 (D : Class) (R : Class) :
    (nb091_alpha_dummy_021 D R) ∈
      (((syn_ccompl (Class.cv (nb091_alpha_dummy_020 D R)))).fv ∪
        ((syn_ccompl (Class.cv (nb091_alpha_dummy_021 D R)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb091_support_mem_0031 (D : Class) (R : Class) (p : Var) :
    (nb091_alpha_dummy_024 D R p) ∈
      (((syn_ccompl (Class.cv (nb091_alpha_dummy_023 D R p)))).fv ∪
        ((syn_ccompl (Class.cv (nb091_alpha_dummy_024 D R p)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb091_support_mem_0032 (D : Class) (R : Class) :
    (nb091_alpha_dummy_021 D R) ∈
      (((Class.cv (nb091_alpha_dummy_021 D R))).fv ∪
        ((Class.cv (nb091_alpha_dummy_021 D R))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb091_support_mem_0033 (D : Class) (R : Class) (p : Var) :
    (nb091_alpha_dummy_024 D R p) ∈
      (((Class.cv (nb091_alpha_dummy_024 D R p))).fv ∪
        ((Class.cv (nb091_alpha_dummy_024 D R p))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb091_support_mem_0034 (D : Class) (R : Class) :
    (nb091_alpha_dummy_001 D R) ∈
      (((Class.cv (nb091_alpha_dummy_000 D R))).fv ∪
        ((Class.cv (nb091_alpha_dummy_001 D R))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb091_support_mem_0035 (D : Class) (R : Class) :
    (nb091_alpha_dummy_001 D R) ∈
      (((syn_ccompl (Class.cab (nb091_alpha_dummy_005 D R)
              (syn_wrex (nb091_alpha_dummy_006 D R) (Class.cv (nb091_alpha_dummy_000 D R))
                (Wff.classEq (Class.cv (nb091_alpha_dummy_005 D R))
                  (syn_cphi (Class.cv (nb091_alpha_dummy_006 D R)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb091_alpha_dummy_005 D R)
              (syn_wrex (nb091_alpha_dummy_006 D R) (Class.cv (nb091_alpha_dummy_001 D R))
                (Wff.classEq (Class.cv (nb091_alpha_dummy_005 D R))
                  (syn_cun (syn_cphi (Class.cv (nb091_alpha_dummy_006 D R)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb091_alpha_dummy_001 D R) ≠ (nb091_alpha_dummy_005 D R) from (by
          unfold nb091_alpha_dummy_005;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb091_support_mem_0034 D R) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb091_alpha_dummy_001 D R) ≠ (nb091_alpha_dummy_006 D R) from (by
            unfold nb091_alpha_dummy_006;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb091_support_mem_0034 D R) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb091_support_mem_0036 (D : Class) (R : Class) (p : Var) :
    (nb091_alpha_dummy_002 D R p) ∈
      (((Class.cv p)).fv ∪ ((Class.cv (nb091_alpha_dummy_002 D R p))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb091_support_mem_0037 (D : Class) (R : Class) (p : Var) :
    (nb091_alpha_dummy_002 D R p) ∈
      (((syn_ccompl (Class.cab (nb091_alpha_dummy_007 D R p)
              (syn_wrex (nb091_alpha_dummy_008 D R p) (Class.cv p)
                (Wff.classEq (Class.cv (nb091_alpha_dummy_007 D R p))
                  (syn_cphi (Class.cv (nb091_alpha_dummy_008 D R p)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb091_alpha_dummy_007 D R p) (syn_wrex (nb091_alpha_dummy_008 D R p)
                (Class.cv (nb091_alpha_dummy_002 D R p))
                (Wff.classEq (Class.cv (nb091_alpha_dummy_007 D R p))
                  (syn_cun (syn_cphi (Class.cv (nb091_alpha_dummy_008 D R p)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb091_alpha_dummy_002 D R p) ≠ (nb091_alpha_dummy_007 D R p) from (by
          unfold nb091_alpha_dummy_007;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb091_support_mem_0036 D R p) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb091_alpha_dummy_002 D R p) ≠ (nb091_alpha_dummy_008 D R p) from (by
            unfold nb091_alpha_dummy_008;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb091_support_mem_0036 D R p) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb091_support_mem_0038 (D : Class) (R : Class) :
    (nb091_alpha_dummy_001 D R) ∈
      (((Class.cab (nb091_alpha_dummy_005 D R)
            (syn_wrex (nb091_alpha_dummy_006 D R) (Class.cv (nb091_alpha_dummy_001 D R))
              (Wff.classEq (Class.cv (nb091_alpha_dummy_005 D R))
                (syn_cun (syn_cphi (Class.cv (nb091_alpha_dummy_006 D R)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb091_alpha_dummy_005 D R)
            (syn_wrex (nb091_alpha_dummy_006 D R) (Class.cv (nb091_alpha_dummy_001 D R))
              (Wff.classEq (Class.cv (nb091_alpha_dummy_005 D R))
                (syn_cun (syn_cphi (Class.cv (nb091_alpha_dummy_006 D R)))
                  (syn_csn (syn_c0c))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb091_alpha_dummy_001 D R) ≠ (nb091_alpha_dummy_005 D R) from (by
          unfold nb091_alpha_dummy_005;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb091_support_mem_0034 D R) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb091_alpha_dummy_001 D R) ≠ (nb091_alpha_dummy_006 D R) from (by
            unfold nb091_alpha_dummy_006;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb091_support_mem_0034 D R) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb091_support_mem_0039 (D : Class) (R : Class) (p : Var) :
    (nb091_alpha_dummy_002 D R p) ∈
      (((Class.cab (nb091_alpha_dummy_007 D R p) (syn_wrex (nb091_alpha_dummy_008 D R p)
              (Class.cv (nb091_alpha_dummy_002 D R p))
              (Wff.classEq (Class.cv (nb091_alpha_dummy_007 D R p))
                (syn_cun (syn_cphi (Class.cv (nb091_alpha_dummy_008 D R p)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb091_alpha_dummy_007 D R p)
            (syn_wrex (nb091_alpha_dummy_008 D R p) (Class.cv (nb091_alpha_dummy_002 D R p))
              (Wff.classEq (Class.cv (nb091_alpha_dummy_007 D R p))
                (syn_cun (syn_cphi (Class.cv (nb091_alpha_dummy_008 D R p)))
                  (syn_csn (syn_c0c))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb091_alpha_dummy_002 D R p) ≠ (nb091_alpha_dummy_007 D R p) from (by
          unfold nb091_alpha_dummy_007;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb091_support_mem_0036 D R p) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb091_alpha_dummy_002 D R p) ≠ (nb091_alpha_dummy_008 D R p) from (by
            unfold nb091_alpha_dummy_008;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb091_support_mem_0036 D R p) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb091_support_mem_0040 (D : Class) (R : Class) :
    (nb091_alpha_dummy_006 D R) ∈
      (((syn_ccompl (syn_cphi (Class.cv (nb091_alpha_dummy_006 D R))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb091_support_mem_0041 (D : Class) (R : Class) (p : Var) :
    (nb091_alpha_dummy_008 D R p) ∈
      (((syn_ccompl (syn_cphi (Class.cv (nb091_alpha_dummy_008 D R p))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb091_support_mem_0042 (D : Class) (R : Class) :
    (nb091_alpha_dummy_006 D R) ∈
      (((syn_cphi (Class.cv (nb091_alpha_dummy_006 D R)))).fv ∪
        ((syn_cphi (Class.cv (nb091_alpha_dummy_006 D R)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb091_support_mem_0043 (D : Class) (R : Class) (p : Var) :
    (nb091_alpha_dummy_008 D R p) ∈
      (((syn_cphi (Class.cv (nb091_alpha_dummy_008 D R p)))).fv ∪
        ((syn_cphi (Class.cv (nb091_alpha_dummy_008 D R p)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb091_support_mem_0044 (D : Class) (R : Class) :
    (nb091_alpha_dummy_059 D R) ∈
      (({(nb091_alpha_dummy_059 D R)} : Finset Var) ∪
          ({(nb091_alpha_dummy_060 D R)} : Finset Var) ∪ ((syn_wa
            (Wff.classMem (Class.cv (nb091_alpha_dummy_059 D R)) (syn_cin D
                (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn
                    (syn_cuni (syn_cuni (Class.cv (nb091_alpha_dummy_000 D R))))))))
            (Wff.classMem (Class.cv (nb091_alpha_dummy_060 D R)) (syn_cin D
                (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (syn_cuni
                      (syn_cuni (Class.cv (nb091_alpha_dummy_000 D R)))))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  with_reducible rw [Finset.mem_union]
  left
  exact Finset.mem_singleton_self _

theorem nb091_support_mem_0045 (D : Class) (R : Class) (p : Var) :
    (nb091_alpha_dummy_061 D R p) ∈
      (({(nb091_alpha_dummy_061 D R p)} : Finset Var) ∪
          ({(nb091_alpha_dummy_062 D R p)} : Finset Var) ∪ ((syn_wa
            (Wff.classMem (Class.cv (nb091_alpha_dummy_061 D R p)) (syn_cin D
                (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
                  (syn_csn (syn_cuni (syn_cuni (Class.cv p)))))))
            (Wff.classMem (Class.cv (nb091_alpha_dummy_062 D R p)) (syn_cin D
                (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
                  (syn_csn (syn_cuni (syn_cuni (Class.cv p))))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  with_reducible rw [Finset.mem_union]
  left
  exact Finset.mem_singleton_self _

theorem nb091_support_mem_0046 (D : Class) (R : Class) :
    (nb091_alpha_dummy_060 D R) ∈
      (({(nb091_alpha_dummy_059 D R)} : Finset Var) ∪
          ({(nb091_alpha_dummy_060 D R)} : Finset Var) ∪ ((syn_wa
            (Wff.classMem (Class.cv (nb091_alpha_dummy_059 D R)) (syn_cin D
                (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn
                    (syn_cuni (syn_cuni (Class.cv (nb091_alpha_dummy_000 D R))))))))
            (Wff.classMem (Class.cv (nb091_alpha_dummy_060 D R)) (syn_cin D
                (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (syn_cuni
                      (syn_cuni (Class.cv (nb091_alpha_dummy_000 D R)))))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  with_reducible rw [Finset.mem_union]
  right
  exact Finset.mem_singleton_self _

theorem nb091_support_mem_0047 (D : Class) (R : Class) (p : Var) :
    (nb091_alpha_dummy_062 D R p) ∈
      (({(nb091_alpha_dummy_061 D R p)} : Finset Var) ∪
          ({(nb091_alpha_dummy_062 D R p)} : Finset Var) ∪ ((syn_wa
            (Wff.classMem (Class.cv (nb091_alpha_dummy_061 D R p)) (syn_cin D
                (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
                  (syn_csn (syn_cuni (syn_cuni (Class.cv p)))))))
            (Wff.classMem (Class.cv (nb091_alpha_dummy_062 D R p)) (syn_cin D
                (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
                  (syn_csn (syn_cuni (syn_cuni (Class.cv p))))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  with_reducible rw [Finset.mem_union]
  right
  exact Finset.mem_singleton_self _

theorem nb091_support_mem_0048 (D : Class) (R : Class) :
    (nb091_alpha_dummy_059 D R) ∈
      (((Class.cv (nb091_alpha_dummy_059 D R))).fv ∪
        ((Class.cv (nb091_alpha_dummy_060 D R))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb091_support_mem_0049 (D : Class) (R : Class) :
    (nb091_alpha_dummy_059 D R) ∈
      (((syn_ccompl (Class.cab (nb091_alpha_dummy_065 D R)
              (syn_wrex (nb091_alpha_dummy_066 D R) (Class.cv (nb091_alpha_dummy_059 D R))
                (Wff.classEq (Class.cv (nb091_alpha_dummy_065 D R))
                  (syn_cphi (Class.cv (nb091_alpha_dummy_066 D R)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb091_alpha_dummy_065 D R)
              (syn_wrex (nb091_alpha_dummy_066 D R) (Class.cv (nb091_alpha_dummy_060 D R))
                (Wff.classEq (Class.cv (nb091_alpha_dummy_065 D R))
                  (syn_cun (syn_cphi (Class.cv (nb091_alpha_dummy_066 D R)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb091_alpha_dummy_059 D R) ≠ (nb091_alpha_dummy_065 D R) from (by
          unfold nb091_alpha_dummy_065;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb091_support_mem_0048 D R) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb091_alpha_dummy_059 D R) ≠ (nb091_alpha_dummy_066 D R) from (by
            unfold nb091_alpha_dummy_066;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb091_support_mem_0048 D R) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb091_support_mem_0050 (D : Class) (R : Class) (p : Var) :
    (nb091_alpha_dummy_061 D R p) ∈
      (((Class.cv (nb091_alpha_dummy_061 D R p))).fv ∪
        ((Class.cv (nb091_alpha_dummy_062 D R p))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb091_support_mem_0051 (D : Class) (R : Class) (p : Var) :
    (nb091_alpha_dummy_061 D R p) ∈
      (((syn_ccompl (Class.cab (nb091_alpha_dummy_067 D R p)
              (syn_wrex (nb091_alpha_dummy_068 D R p) (Class.cv (nb091_alpha_dummy_061 D R p))
                (Wff.classEq (Class.cv (nb091_alpha_dummy_067 D R p))
                  (syn_cphi (Class.cv (nb091_alpha_dummy_068 D R p)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb091_alpha_dummy_067 D R p) (syn_wrex (nb091_alpha_dummy_068 D R p)
                (Class.cv (nb091_alpha_dummy_062 D R p))
                (Wff.classEq (Class.cv (nb091_alpha_dummy_067 D R p))
                  (syn_cun (syn_cphi (Class.cv (nb091_alpha_dummy_068 D R p)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb091_alpha_dummy_061 D R p) ≠ (nb091_alpha_dummy_067 D R p) from (by
          unfold nb091_alpha_dummy_067;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb091_support_mem_0050 D R p) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb091_alpha_dummy_061 D R p) ≠ (nb091_alpha_dummy_068 D R p) from (by
            unfold nb091_alpha_dummy_068;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb091_support_mem_0050 D R p) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb091_support_mem_0052 (D : Class) (R : Class) :
    (nb091_alpha_dummy_059 D R) ∈
      (((Class.cab (nb091_alpha_dummy_065 D R)
            (syn_wrex (nb091_alpha_dummy_066 D R) (Class.cv (nb091_alpha_dummy_059 D R))
              (Wff.classEq (Class.cv (nb091_alpha_dummy_065 D R))
                (syn_cphi (Class.cv (nb091_alpha_dummy_066 D R))))))).fv ∪
        ((Class.cab (nb091_alpha_dummy_065 D R)
            (syn_wrex (nb091_alpha_dummy_066 D R) (Class.cv (nb091_alpha_dummy_059 D R))
              (Wff.classEq (Class.cv (nb091_alpha_dummy_065 D R))
                (syn_cphi (Class.cv (nb091_alpha_dummy_066 D R))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb091_alpha_dummy_059 D R) ≠ (nb091_alpha_dummy_065 D R) from (by
          unfold nb091_alpha_dummy_065;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb091_support_mem_0048 D R) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb091_alpha_dummy_059 D R) ≠ (nb091_alpha_dummy_066 D R) from (by
            unfold nb091_alpha_dummy_066;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb091_support_mem_0048 D R) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb091_support_mem_0053 (D : Class) (R : Class) (p : Var) :
    (nb091_alpha_dummy_061 D R p) ∈
      (((Class.cab (nb091_alpha_dummy_067 D R p) (syn_wrex (nb091_alpha_dummy_068 D R p)
              (Class.cv (nb091_alpha_dummy_061 D R p))
              (Wff.classEq (Class.cv (nb091_alpha_dummy_067 D R p))
                (syn_cphi (Class.cv (nb091_alpha_dummy_068 D R p))))))).fv ∪
        ((Class.cab (nb091_alpha_dummy_067 D R p) (syn_wrex (nb091_alpha_dummy_068 D R p)
              (Class.cv (nb091_alpha_dummy_061 D R p))
              (Wff.classEq (Class.cv (nb091_alpha_dummy_067 D R p))
                (syn_cphi (Class.cv (nb091_alpha_dummy_068 D R p))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb091_alpha_dummy_061 D R p) ≠ (nb091_alpha_dummy_067 D R p) from (by
          unfold nb091_alpha_dummy_067;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb091_support_mem_0050 D R p) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb091_alpha_dummy_061 D R p) ≠ (nb091_alpha_dummy_068 D R p) from (by
            unfold nb091_alpha_dummy_068;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb091_support_mem_0050 D R p) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb091_support_mem_0054 (D : Class) (R : Class) :
    (nb091_alpha_dummy_066 D R) ∈ (((Class.cv (nb091_alpha_dummy_066 D R))).fv) :=
  by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb091_support_mem_0055 (D : Class) (R : Class) (p : Var) :
    (nb091_alpha_dummy_068 D R p) ∈ (((Class.cv (nb091_alpha_dummy_068 D R p))).fv) :=
  by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb091_support_mem_0056 (D : Class) (R : Class) :
    (nb091_alpha_dummy_073 D R) ∈
      (((Wff.classMem (Class.cv (nb091_alpha_dummy_073 D R)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb091_alpha_dummy_073 D R)) (syn_c1c))).fv ∪
        ((Class.cv (nb091_alpha_dummy_073 D R))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_wff_classMem]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb091_support_mem_0057 (D : Class) (R : Class) (p : Var) :
    (nb091_alpha_dummy_075 D R p) ∈
      (((Wff.classMem (Class.cv (nb091_alpha_dummy_075 D R p)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb091_alpha_dummy_075 D R p)) (syn_c1c))).fv ∪
        ((Class.cv (nb091_alpha_dummy_075 D R p))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_wff_classMem]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb091_support_mem_0058 (D : Class) (R : Class) :
    (nb091_alpha_dummy_073 D R) ∈
      (((Class.cv (nb091_alpha_dummy_073 D R))).fv ∪ ((syn_c1c)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb091_support_mem_0059 (D : Class) (R : Class) (p : Var) :
    (nb091_alpha_dummy_075 D R p) ∈
      (((Class.cv (nb091_alpha_dummy_075 D R p))).fv ∪ ((syn_c1c)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb091_support_mem_0060 (D : Class) (R : Class) :
    (nb091_alpha_dummy_080 D R) ∈
      (((syn_cnin (Class.cv (nb091_alpha_dummy_080 D R))
            (Class.cv (nb091_alpha_dummy_081 D R)))).fv ∪
        ((syn_cnin (Class.cv (nb091_alpha_dummy_080 D R))
            (Class.cv (nb091_alpha_dummy_081 D R)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired


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

theorem nb091_support_mem_0061 (D : Class) (R : Class) (p : Var) :
    (nb091_alpha_dummy_083 D R p) ∈
      (((syn_cnin (Class.cv (nb091_alpha_dummy_083 D R p))
            (Class.cv (nb091_alpha_dummy_084 D R p)))).fv ∪
        ((syn_cnin (Class.cv (nb091_alpha_dummy_083 D R p))
            (Class.cv (nb091_alpha_dummy_084 D R p)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb091_support_mem_0062 (D : Class) (R : Class) :
    (nb091_alpha_dummy_080 D R) ∈
      (((Class.cv (nb091_alpha_dummy_080 D R))).fv ∪
        ((Class.cv (nb091_alpha_dummy_081 D R))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb091_support_mem_0063 (D : Class) (R : Class) (p : Var) :
    (nb091_alpha_dummy_083 D R p) ∈
      (((Class.cv (nb091_alpha_dummy_083 D R p))).fv ∪
        ((Class.cv (nb091_alpha_dummy_084 D R p))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb091_support_mem_0064 (D : Class) (R : Class) :
    (nb091_alpha_dummy_081 D R) ∈
      (((syn_cnin (Class.cv (nb091_alpha_dummy_080 D R))
            (Class.cv (nb091_alpha_dummy_081 D R)))).fv ∪
        ((syn_cnin (Class.cv (nb091_alpha_dummy_080 D R))
            (Class.cv (nb091_alpha_dummy_081 D R)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb091_support_mem_0065 (D : Class) (R : Class) (p : Var) :
    (nb091_alpha_dummy_084 D R p) ∈
      (((syn_cnin (Class.cv (nb091_alpha_dummy_083 D R p))
            (Class.cv (nb091_alpha_dummy_084 D R p)))).fv ∪
        ((syn_cnin (Class.cv (nb091_alpha_dummy_083 D R p))
            (Class.cv (nb091_alpha_dummy_084 D R p)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb091_support_mem_0066 (D : Class) (R : Class) :
    (nb091_alpha_dummy_081 D R) ∈
      (((Class.cv (nb091_alpha_dummy_080 D R))).fv ∪
        ((Class.cv (nb091_alpha_dummy_081 D R))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb091_support_mem_0067 (D : Class) (R : Class) (p : Var) :
    (nb091_alpha_dummy_084 D R p) ∈
      (((Class.cv (nb091_alpha_dummy_083 D R p))).fv ∪
        ((Class.cv (nb091_alpha_dummy_084 D R p))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb091_support_mem_0068 (D : Class) (R : Class) :
    (nb091_alpha_dummy_080 D R) ∈
      (((syn_ccompl (Class.cv (nb091_alpha_dummy_080 D R)))).fv ∪
        ((syn_ccompl (Class.cv (nb091_alpha_dummy_081 D R)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb091_support_mem_0069 (D : Class) (R : Class) (p : Var) :
    (nb091_alpha_dummy_083 D R p) ∈
      (((syn_ccompl (Class.cv (nb091_alpha_dummy_083 D R p)))).fv ∪
        ((syn_ccompl (Class.cv (nb091_alpha_dummy_084 D R p)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb091_support_mem_0070 (D : Class) (R : Class) :
    (nb091_alpha_dummy_080 D R) ∈
      (((Class.cv (nb091_alpha_dummy_080 D R))).fv ∪
        ((Class.cv (nb091_alpha_dummy_080 D R))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb091_support_mem_0071 (D : Class) (R : Class) (p : Var) :
    (nb091_alpha_dummy_083 D R p) ∈
      (((Class.cv (nb091_alpha_dummy_083 D R p))).fv ∪
        ((Class.cv (nb091_alpha_dummy_083 D R p))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb091_support_mem_0072 (D : Class) (R : Class) :
    (nb091_alpha_dummy_081 D R) ∈
      (((syn_ccompl (Class.cv (nb091_alpha_dummy_080 D R)))).fv ∪
        ((syn_ccompl (Class.cv (nb091_alpha_dummy_081 D R)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb091_support_mem_0073 (D : Class) (R : Class) (p : Var) :
    (nb091_alpha_dummy_084 D R p) ∈
      (((syn_ccompl (Class.cv (nb091_alpha_dummy_083 D R p)))).fv ∪
        ((syn_ccompl (Class.cv (nb091_alpha_dummy_084 D R p)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb091_support_mem_0074 (D : Class) (R : Class) :
    (nb091_alpha_dummy_081 D R) ∈
      (((Class.cv (nb091_alpha_dummy_081 D R))).fv ∪
        ((Class.cv (nb091_alpha_dummy_081 D R))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb091_support_mem_0075 (D : Class) (R : Class) (p : Var) :
    (nb091_alpha_dummy_084 D R p) ∈
      (((Class.cv (nb091_alpha_dummy_084 D R p))).fv ∪
        ((Class.cv (nb091_alpha_dummy_084 D R p))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb091_support_mem_0076 (D : Class) (R : Class) :
    (nb091_alpha_dummy_060 D R) ∈
      (((Class.cv (nb091_alpha_dummy_059 D R))).fv ∪
        ((Class.cv (nb091_alpha_dummy_060 D R))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb091_support_mem_0077 (D : Class) (R : Class) :
    (nb091_alpha_dummy_060 D R) ∈
      (((syn_ccompl (Class.cab (nb091_alpha_dummy_065 D R)
              (syn_wrex (nb091_alpha_dummy_066 D R) (Class.cv (nb091_alpha_dummy_059 D R))
                (Wff.classEq (Class.cv (nb091_alpha_dummy_065 D R))
                  (syn_cphi (Class.cv (nb091_alpha_dummy_066 D R)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb091_alpha_dummy_065 D R)
              (syn_wrex (nb091_alpha_dummy_066 D R) (Class.cv (nb091_alpha_dummy_060 D R))
                (Wff.classEq (Class.cv (nb091_alpha_dummy_065 D R))
                  (syn_cun (syn_cphi (Class.cv (nb091_alpha_dummy_066 D R)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb091_alpha_dummy_060 D R) ≠ (nb091_alpha_dummy_065 D R) from (by
          unfold nb091_alpha_dummy_065;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb091_support_mem_0076 D R) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb091_alpha_dummy_060 D R) ≠ (nb091_alpha_dummy_066 D R) from (by
            unfold nb091_alpha_dummy_066;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb091_support_mem_0076 D R) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb091_support_mem_0078 (D : Class) (R : Class) (p : Var) :
    (nb091_alpha_dummy_062 D R p) ∈
      (((Class.cv (nb091_alpha_dummy_061 D R p))).fv ∪
        ((Class.cv (nb091_alpha_dummy_062 D R p))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb091_support_mem_0079 (D : Class) (R : Class) (p : Var) :
    (nb091_alpha_dummy_062 D R p) ∈
      (((syn_ccompl (Class.cab (nb091_alpha_dummy_067 D R p)
              (syn_wrex (nb091_alpha_dummy_068 D R p) (Class.cv (nb091_alpha_dummy_061 D R p))
                (Wff.classEq (Class.cv (nb091_alpha_dummy_067 D R p))
                  (syn_cphi (Class.cv (nb091_alpha_dummy_068 D R p)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb091_alpha_dummy_067 D R p) (syn_wrex (nb091_alpha_dummy_068 D R p)
                (Class.cv (nb091_alpha_dummy_062 D R p))
                (Wff.classEq (Class.cv (nb091_alpha_dummy_067 D R p))
                  (syn_cun (syn_cphi (Class.cv (nb091_alpha_dummy_068 D R p)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb091_alpha_dummy_062 D R p) ≠ (nb091_alpha_dummy_067 D R p) from (by
          unfold nb091_alpha_dummy_067;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb091_support_mem_0078 D R p) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb091_alpha_dummy_062 D R p) ≠ (nb091_alpha_dummy_068 D R p) from (by
            unfold nb091_alpha_dummy_068;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb091_support_mem_0078 D R p) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb091_support_mem_0080 (D : Class) (R : Class) :
    (nb091_alpha_dummy_060 D R) ∈
      (((Class.cab (nb091_alpha_dummy_065 D R)
            (syn_wrex (nb091_alpha_dummy_066 D R) (Class.cv (nb091_alpha_dummy_060 D R))
              (Wff.classEq (Class.cv (nb091_alpha_dummy_065 D R))
                (syn_cun (syn_cphi (Class.cv (nb091_alpha_dummy_066 D R)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb091_alpha_dummy_065 D R)
            (syn_wrex (nb091_alpha_dummy_066 D R) (Class.cv (nb091_alpha_dummy_060 D R))
              (Wff.classEq (Class.cv (nb091_alpha_dummy_065 D R))
                (syn_cun (syn_cphi (Class.cv (nb091_alpha_dummy_066 D R)))
                  (syn_csn (syn_c0c))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb091_alpha_dummy_060 D R) ≠ (nb091_alpha_dummy_065 D R) from (by
          unfold nb091_alpha_dummy_065;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb091_support_mem_0076 D R) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb091_alpha_dummy_060 D R) ≠ (nb091_alpha_dummy_066 D R) from (by
            unfold nb091_alpha_dummy_066;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb091_support_mem_0076 D R) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb091_support_mem_0081 (D : Class) (R : Class) (p : Var) :
    (nb091_alpha_dummy_062 D R p) ∈
      (((Class.cab (nb091_alpha_dummy_067 D R p) (syn_wrex (nb091_alpha_dummy_068 D R p)
              (Class.cv (nb091_alpha_dummy_062 D R p))
              (Wff.classEq (Class.cv (nb091_alpha_dummy_067 D R p))
                (syn_cun (syn_cphi (Class.cv (nb091_alpha_dummy_068 D R p)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb091_alpha_dummy_067 D R p)
            (syn_wrex (nb091_alpha_dummy_068 D R p) (Class.cv (nb091_alpha_dummy_062 D R p))
              (Wff.classEq (Class.cv (nb091_alpha_dummy_067 D R p))
                (syn_cun (syn_cphi (Class.cv (nb091_alpha_dummy_068 D R p)))
                  (syn_csn (syn_c0c))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb091_alpha_dummy_062 D R p) ≠ (nb091_alpha_dummy_067 D R p) from (by
          unfold nb091_alpha_dummy_067;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb091_support_mem_0078 D R p) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb091_alpha_dummy_062 D R p) ≠ (nb091_alpha_dummy_068 D R p) from (by
            unfold nb091_alpha_dummy_068;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb091_support_mem_0078 D R p) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb091_support_mem_0082 (D : Class) (R : Class) :
    (nb091_alpha_dummy_066 D R) ∈
      (((syn_ccompl (syn_cphi (Class.cv (nb091_alpha_dummy_066 D R))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb091_support_mem_0083 (D : Class) (R : Class) (p : Var) :
    (nb091_alpha_dummy_068 D R p) ∈
      (((syn_ccompl (syn_cphi (Class.cv (nb091_alpha_dummy_068 D R p))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb091_support_mem_0084 (D : Class) (R : Class) :
    (nb091_alpha_dummy_066 D R) ∈
      (((syn_cphi (Class.cv (nb091_alpha_dummy_066 D R)))).fv ∪
        ((syn_cphi (Class.cv (nb091_alpha_dummy_066 D R)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb091_support_mem_0085 (D : Class) (R : Class) (p : Var) :
    (nb091_alpha_dummy_068 D R p) ∈
      (((syn_cphi (Class.cv (nb091_alpha_dummy_068 D R p)))).fv ∪
        ((syn_cphi (Class.cv (nb091_alpha_dummy_068 D R p)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb091_support_mem_0086 (D : Class) (R : Class) :
    (nb091_alpha_dummy_000 D R) ∈
      (((syn_chwniso D)).fv ∪ ((syn_csn (syn_chnwcutcode R D
              (syn_cuni (syn_cuni (Class.cv (nb091_alpha_dummy_000 D R))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_csn]
  rw [fv_syn_chnwcutcode]
  with_reducible rw [Finset.mem_union]
  left
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cuni]
  rw [fv_syn_cuni]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb091_support_mem_0087 (D : Class) (R : Class) (p : Var) :
    p ∈
      (((syn_chwniso D)).fv ∪
        ((syn_csn (syn_chnwcutcode R D (syn_cuni (syn_cuni (Class.cv p)))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_csn]
  rw [fv_syn_chnwcutcode]
  with_reducible rw [Finset.mem_union]
  left
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cuni]
  rw [fv_syn_cuni]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb091_support_mem_0088 (D : Class) (R : Class) :
    (nb091_alpha_dummy_000 D R) ∈
      (((syn_chnwcutcode R D
          (syn_cuni (syn_cuni (Class.cv (nb091_alpha_dummy_000 D R)))))).fv) :=
  by
  rw [fv_syn_chnwcutcode]
  with_reducible rw [Finset.mem_union]
  left
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cuni]
  rw [fv_syn_cuni]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb091_support_mem_0089 (D : Class) (R : Class) (p : Var) :
    p ∈ (((syn_chnwcutcode R D (syn_cuni (syn_cuni (Class.cv p))))).fv) :=
  by
  rw [fv_syn_chnwcutcode]
  with_reducible rw [Finset.mem_union]
  left
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cuni]
  rw [fv_syn_cuni]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb091_support_mem_0090 (D : Class) (R : Class) :
    (nb091_alpha_dummy_000 D R) ∈
      (((syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
                  (syn_csn (syn_cuni (syn_cuni (Class.cv (nb091_alpha_dummy_000 D R)))))))
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (syn_cuni
                      (syn_cuni (Class.cv (nb091_alpha_dummy_000 D R)))))))))).fv ∪ ((syn_cin D
            (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn
                (syn_cuni (syn_cuni (Class.cv (nb091_alpha_dummy_000 D R)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cin]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_cxp]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cin]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_cima]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_csn]
  rw [fv_syn_cuni]
  rw [fv_syn_cuni]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb091_support_mem_0091 (D : Class) (R : Class) :
    (nb091_alpha_dummy_000 D R) ∈
      (((syn_ccompl (Class.cab (nb091_alpha_dummy_047 D R) (syn_wrex (nb091_alpha_dummy_048 D R)
                (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
                        (syn_csn (syn_cuni (syn_cuni (Class.cv (nb091_alpha_dummy_000 D R)))))))
                    (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (syn_cuni
                            (syn_cuni (Class.cv (nb091_alpha_dummy_000 D R)))))))))
                (Wff.classEq (Class.cv (nb091_alpha_dummy_047 D R))
                  (syn_cphi (Class.cv (nb091_alpha_dummy_048 D R)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb091_alpha_dummy_047 D R) (syn_wrex (nb091_alpha_dummy_048 D R)
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn
                      (syn_cuni (syn_cuni (Class.cv (nb091_alpha_dummy_000 D R)))))))
                (Wff.classEq (Class.cv (nb091_alpha_dummy_047 D R))
                  (syn_cun (syn_cphi (Class.cv (nb091_alpha_dummy_048 D R)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb091_alpha_dummy_000 D R) ≠ (nb091_alpha_dummy_047 D R) from (by
          unfold nb091_alpha_dummy_047;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb091_support_mem_0090 D R) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb091_alpha_dummy_000 D R) ≠ (nb091_alpha_dummy_048 D R) from (by
            unfold nb091_alpha_dummy_048;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb091_support_mem_0090 D R) 1))))
    · rw [fv_syn_cin]
      with_reducible rw [Finset.mem_union]
      right
      rw [fv_syn_cxp]
      with_reducible rw [Finset.mem_union]
      left
      rw [fv_syn_cin]
      with_reducible rw [Finset.mem_union]
      right
      rw [fv_syn_cima]
      with_reducible rw [Finset.mem_union]
      right
      rw [fv_syn_csn]
      rw [fv_syn_cuni]
      rw [fv_syn_cuni]
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb091_support_mem_0092 (D : Class) (R : Class) (p : Var) :
    p ∈
      (((syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
                  (syn_csn (syn_cuni (syn_cuni (Class.cv p)))))) (syn_cin D
                (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
                  (syn_csn (syn_cuni (syn_cuni (Class.cv p))))))))).fv ∪ ((syn_cin D
            (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
              (syn_csn (syn_cuni (syn_cuni (Class.cv p))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cin]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_cxp]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cin]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_cima]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_csn]
  rw [fv_syn_cuni]
  rw [fv_syn_cuni]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb091_support_mem_0093 (D : Class) (R : Class) (p : Var) :
    p ∈
      (((syn_ccompl (Class.cab (nb091_alpha_dummy_049 D R p)
              (syn_wrex (nb091_alpha_dummy_050 D R p) (syn_cin R (syn_cxp (syn_cin D
                      (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
                        (syn_csn (syn_cuni (syn_cuni (Class.cv p)))))) (syn_cin D
                      (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
                        (syn_csn (syn_cuni (syn_cuni (Class.cv p))))))))
                (Wff.classEq (Class.cv (nb091_alpha_dummy_049 D R p))
                  (syn_cphi (Class.cv (nb091_alpha_dummy_050 D R p)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb091_alpha_dummy_049 D R p) (syn_wrex (nb091_alpha_dummy_050 D R p)
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
                    (syn_csn (syn_cuni (syn_cuni (Class.cv p))))))
                (Wff.classEq (Class.cv (nb091_alpha_dummy_049 D R p))
                  (syn_cun (syn_cphi (Class.cv (nb091_alpha_dummy_050 D R p)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show p ≠ (nb091_alpha_dummy_049 D R p) from (by
          unfold nb091_alpha_dummy_049;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb091_support_mem_0092 D R p) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show p ≠ (nb091_alpha_dummy_050 D R p) from (by
            unfold nb091_alpha_dummy_050;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb091_support_mem_0092 D R p) 1))))
    · rw [fv_syn_cin]
      with_reducible rw [Finset.mem_union]
      right
      rw [fv_syn_cxp]
      with_reducible rw [Finset.mem_union]
      left
      rw [fv_syn_cin]
      with_reducible rw [Finset.mem_union]
      right
      rw [fv_syn_cima]
      with_reducible rw [Finset.mem_union]
      right
      rw [fv_syn_csn]
      rw [fv_syn_cuni]
      rw [fv_syn_cuni]
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb091_support_mem_0094 (D : Class) (R : Class) :
    (nb091_alpha_dummy_000 D R) ∈
      (((Class.cab (nb091_alpha_dummy_047 D R) (syn_wrex (nb091_alpha_dummy_048 D R) (syn_cin R
                (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn
                        (syn_cuni (syn_cuni (Class.cv (nb091_alpha_dummy_000 D R)))))))
                  (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn
                        (syn_cuni (syn_cuni (Class.cv (nb091_alpha_dummy_000 D R)))))))))
              (Wff.classEq (Class.cv (nb091_alpha_dummy_047 D R))
                (syn_cphi (Class.cv (nb091_alpha_dummy_048 D R))))))).fv ∪
        ((Class.cab (nb091_alpha_dummy_047 D R) (syn_wrex (nb091_alpha_dummy_048 D R) (syn_cin R
                (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn
                        (syn_cuni (syn_cuni (Class.cv (nb091_alpha_dummy_000 D R)))))))
                  (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn
                        (syn_cuni (syn_cuni (Class.cv (nb091_alpha_dummy_000 D R)))))))))
              (Wff.classEq (Class.cv (nb091_alpha_dummy_047 D R))
                (syn_cphi (Class.cv (nb091_alpha_dummy_048 D R))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb091_alpha_dummy_000 D R) ≠ (nb091_alpha_dummy_047 D R) from (by
          unfold nb091_alpha_dummy_047;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb091_support_mem_0090 D R) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb091_alpha_dummy_000 D R) ≠ (nb091_alpha_dummy_048 D R) from (by
            unfold nb091_alpha_dummy_048;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb091_support_mem_0090 D R) 1))))
    · rw [fv_syn_cin]
      with_reducible rw [Finset.mem_union]
      right
      rw [fv_syn_cxp]
      with_reducible rw [Finset.mem_union]
      left
      rw [fv_syn_cin]
      with_reducible rw [Finset.mem_union]
      right
      rw [fv_syn_cima]
      with_reducible rw [Finset.mem_union]
      right
      rw [fv_syn_csn]
      rw [fv_syn_cuni]
      rw [fv_syn_cuni]
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb091_support_mem_0095 (D : Class) (R : Class) (p : Var) :
    p ∈
      (((Class.cab (nb091_alpha_dummy_049 D R p) (syn_wrex (nb091_alpha_dummy_050 D R p)
              (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
                      (syn_csn (syn_cuni (syn_cuni (Class.cv p)))))) (syn_cin D
                    (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
                      (syn_csn (syn_cuni (syn_cuni (Class.cv p))))))))
              (Wff.classEq (Class.cv (nb091_alpha_dummy_049 D R p))
                (syn_cphi (Class.cv (nb091_alpha_dummy_050 D R p))))))).fv ∪
        ((Class.cab (nb091_alpha_dummy_049 D R p) (syn_wrex (nb091_alpha_dummy_050 D R p)
              (syn_cin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
                      (syn_csn (syn_cuni (syn_cuni (Class.cv p)))))) (syn_cin D
                    (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
                      (syn_csn (syn_cuni (syn_cuni (Class.cv p))))))))
              (Wff.classEq (Class.cv (nb091_alpha_dummy_049 D R p))
                (syn_cphi (Class.cv (nb091_alpha_dummy_050 D R p))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show p ≠ (nb091_alpha_dummy_049 D R p) from (by
          unfold nb091_alpha_dummy_049;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb091_support_mem_0092 D R p) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show p ≠ (nb091_alpha_dummy_050 D R p) from (by
            unfold nb091_alpha_dummy_050;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb091_support_mem_0092 D R p) 1))))
    · rw [fv_syn_cin]
      with_reducible rw [Finset.mem_union]
      right
      rw [fv_syn_cxp]
      with_reducible rw [Finset.mem_union]
      left
      rw [fv_syn_cin]
      with_reducible rw [Finset.mem_union]
      right
      rw [fv_syn_cima]
      with_reducible rw [Finset.mem_union]
      right
      rw [fv_syn_csn]
      rw [fv_syn_cuni]
      rw [fv_syn_cuni]
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb091_support_mem_0096 (D : Class) (R : Class) :
    (nb091_alpha_dummy_000 D R) ∈
      (((syn_cnin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
                  (syn_csn (syn_cuni (syn_cuni (Class.cv (nb091_alpha_dummy_000 D R)))))))
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (syn_cuni
                      (syn_cuni (Class.cv (nb091_alpha_dummy_000 D R)))))))))).fv ∪ ((syn_cnin R
            (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
                  (syn_csn (syn_cuni (syn_cuni (Class.cv (nb091_alpha_dummy_000 D R)))))))
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (syn_cuni
                      (syn_cuni (Class.cv (nb091_alpha_dummy_000 D R)))))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_cxp]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cin]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_cima]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_csn]
  rw [fv_syn_cuni]
  rw [fv_syn_cuni]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb091_support_mem_0097 (D : Class) (R : Class) (p : Var) :
    p ∈
      (((syn_cnin R (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
                  (syn_csn (syn_cuni (syn_cuni (Class.cv p)))))) (syn_cin D
                (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
                  (syn_csn (syn_cuni (syn_cuni (Class.cv p))))))))).fv ∪ ((syn_cnin R (syn_cxp
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
                  (syn_csn (syn_cuni (syn_cuni (Class.cv p)))))) (syn_cin D
                (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
                  (syn_csn (syn_cuni (syn_cuni (Class.cv p))))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_cxp]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cin]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_cima]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_csn]
  rw [fv_syn_cuni]
  rw [fv_syn_cuni]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb091_support_mem_0098 (D : Class) (R : Class) :
    (nb091_alpha_dummy_000 D R) ∈
      ((R).fv ∪ ((syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
                (syn_csn (syn_cuni (syn_cuni (Class.cv (nb091_alpha_dummy_000 D R)))))))
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn
                  (syn_cuni (syn_cuni (Class.cv (nb091_alpha_dummy_000 D R))))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_cxp]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cin]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_cima]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_csn]
  rw [fv_syn_cuni]
  rw [fv_syn_cuni]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb091_support_mem_0099 (D : Class) (R : Class) (p : Var) :
    p ∈
      ((R).fv ∪ ((syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
                (syn_csn (syn_cuni (syn_cuni (Class.cv p)))))) (syn_cin D
              (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
                (syn_csn (syn_cuni (syn_cuni (Class.cv p)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_cxp]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cin]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_cima]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_csn]
  rw [fv_syn_cuni]
  rw [fv_syn_cuni]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb091_support_mem_0100 (D : Class) (R : Class) :
    (nb091_alpha_dummy_000 D R) ∈
      (({(nb091_alpha_dummy_059 D R)} : Finset Var) ∪
          ({(nb091_alpha_dummy_060 D R)} : Finset Var) ∪ ((syn_wa
            (Wff.classMem (Class.cv (nb091_alpha_dummy_059 D R)) (syn_cin D
                (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn
                    (syn_cuni (syn_cuni (Class.cv (nb091_alpha_dummy_000 D R))))))))
            (Wff.classMem (Class.cv (nb091_alpha_dummy_060 D R)) (syn_cin D
                (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (syn_cuni
                      (syn_cuni (Class.cv (nb091_alpha_dummy_000 D R)))))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_wa]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_wff_classMem]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_cin]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_cima]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_csn]
  rw [fv_syn_cuni]
  rw [fv_syn_cuni]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb091_support_mem_0101 (D : Class) (R : Class) (p : Var) :
    p ∈
      (({(nb091_alpha_dummy_061 D R p)} : Finset Var) ∪
          ({(nb091_alpha_dummy_062 D R p)} : Finset Var) ∪ ((syn_wa
            (Wff.classMem (Class.cv (nb091_alpha_dummy_061 D R p)) (syn_cin D
                (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
                  (syn_csn (syn_cuni (syn_cuni (Class.cv p)))))))
            (Wff.classMem (Class.cv (nb091_alpha_dummy_062 D R p)) (syn_cin D
                (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
                  (syn_csn (syn_cuni (syn_cuni (Class.cv p))))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_wa]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_wff_classMem]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_cin]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_cima]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_csn]
  rw [fv_syn_cuni]
  rw [fv_syn_cuni]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb091_support_mem_0102 (D : Class) (R : Class) :
    (nb091_alpha_dummy_000 D R) ∈
      (((syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn
                (syn_cuni (syn_cuni (Class.cv (nb091_alpha_dummy_000 D R)))))))).fv ∪
        ((syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn
                (syn_cuni (syn_cuni (Class.cv (nb091_alpha_dummy_000 D R)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cin]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_cima]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_csn]
  rw [fv_syn_cuni]
  rw [fv_syn_cuni]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb091_support_mem_0103 (D : Class) (R : Class) (p : Var) :
    p ∈
      (((syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
              (syn_csn (syn_cuni (syn_cuni (Class.cv p))))))).fv ∪ ((syn_cin D
            (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
              (syn_csn (syn_cuni (syn_cuni (Class.cv p))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cin]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_cima]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_csn]
  rw [fv_syn_cuni]
  rw [fv_syn_cuni]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb091_support_mem_0104 (D : Class) (R : Class) :
    (nb091_alpha_dummy_000 D R) ∈
      (((syn_cnin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn
                (syn_cuni (syn_cuni (Class.cv (nb091_alpha_dummy_000 D R)))))))).fv ∪
        ((syn_cnin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn
                (syn_cuni (syn_cuni (Class.cv (nb091_alpha_dummy_000 D R)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_cima]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_csn]
  rw [fv_syn_cuni]
  rw [fv_syn_cuni]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb091_support_mem_0105 (D : Class) (R : Class) (p : Var) :
    p ∈
      (((syn_cnin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
              (syn_csn (syn_cuni (syn_cuni (Class.cv p))))))).fv ∪ ((syn_cnin D
            (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
              (syn_csn (syn_cuni (syn_cuni (Class.cv p))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_cima]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_csn]
  rw [fv_syn_cuni]
  rw [fv_syn_cuni]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb091_support_mem_0106 (D : Class) (R : Class) :
    (nb091_alpha_dummy_000 D R) ∈
      ((D).fv ∪ ((syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn
              (syn_cuni (syn_cuni (Class.cv (nb091_alpha_dummy_000 D R))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_cima]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_csn]
  rw [fv_syn_cuni]
  rw [fv_syn_cuni]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb091_support_mem_0107 (D : Class) (R : Class) (p : Var) :
    p ∈
      ((D).fv ∪ ((syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
            (syn_csn (syn_cuni (syn_cuni (Class.cv p)))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_cima]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_csn]
  rw [fv_syn_cuni]
  rw [fv_syn_cuni]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb091_support_mem_0108 (D : Class) (R : Class) :
    (nb091_alpha_dummy_000 D R) ∈
      (((syn_ccnv (syn_cdif R (syn_cid)))).fv ∪
        ((syn_csn (syn_cuni (syn_cuni (Class.cv (nb091_alpha_dummy_000 D R)))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_csn]
  rw [fv_syn_cuni]
  rw [fv_syn_cuni]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb091_support_mem_0109 (R : Class) (p : Var) :
    p ∈
      (((syn_ccnv (syn_cdif R (syn_cid)))).fv ∪
        ((syn_csn (syn_cuni (syn_cuni (Class.cv p))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_csn]
  rw [fv_syn_cuni]
  rw [fv_syn_cuni]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb091_support_mem_0110 (D : Class) (R : Class) :
    (nb091_alpha_dummy_000 D R) ∈
      (((syn_cuni (syn_cuni (Class.cv (nb091_alpha_dummy_000 D R))))).fv) :=
  by
  rw [fv_syn_cuni]
  rw [fv_syn_cuni]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb091_support_mem_0111 (p : Var) :
    p ∈ (((syn_cuni (syn_cuni (Class.cv p)))).fv) :=
  by
  rw [fv_syn_cuni]
  rw [fv_syn_cuni]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb091_support_mem_0112 (D : Class) (R : Class) :
    (nb091_alpha_dummy_000 D R) ∈
      (((syn_cuni (Class.cv (nb091_alpha_dummy_000 D R)))).fv) :=
  by
  rw [fv_syn_cuni]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb091_support_mem_0113 (p : Var) : p ∈ (((syn_cuni (Class.cv p))).fv) :=
  by
  rw [fv_syn_cuni]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb091_support_mem_0114 (D : Class) (R : Class) :
    (nb091_alpha_dummy_000 D R) ∈ (((Class.cv (nb091_alpha_dummy_000 D R))).fv) :=
  by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb091_support_mem_0115 (p : Var) : p ∈ (((Class.cv p)).fv) :=
  by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb091_support_mem_0116 (D : Class) (R : Class) :
    (nb091_alpha_dummy_106 D R) ∈
      (((Class.cv (nb091_alpha_dummy_106 D R))).fv ∪
        ((Class.cv (nb091_alpha_dummy_105 D R))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb091_support_mem_0117 (D : Class) (R : Class) :
    (nb091_alpha_dummy_106 D R) ∈
      (((syn_ccompl (Class.cab (nb091_alpha_dummy_119 D R)
              (syn_wrex (nb091_alpha_dummy_120 D R) (Class.cv (nb091_alpha_dummy_106 D R))
                (Wff.classEq (Class.cv (nb091_alpha_dummy_119 D R))
                  (syn_cphi (Class.cv (nb091_alpha_dummy_120 D R)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb091_alpha_dummy_119 D R)
              (syn_wrex (nb091_alpha_dummy_120 D R) (Class.cv (nb091_alpha_dummy_105 D R))
                (Wff.classEq (Class.cv (nb091_alpha_dummy_119 D R))
                  (syn_cun (syn_cphi (Class.cv (nb091_alpha_dummy_120 D R)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb091_alpha_dummy_106 D R) ≠ (nb091_alpha_dummy_119 D R) from (by
          unfold nb091_alpha_dummy_119;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb091_support_mem_0116 D R) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb091_alpha_dummy_106 D R) ≠ (nb091_alpha_dummy_120 D R) from (by
            unfold nb091_alpha_dummy_120;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb091_support_mem_0116 D R) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb091_support_mem_0118 (R : Class) (p : Var) :
    (nb091_alpha_dummy_108 R p) ∈
      (((Class.cv (nb091_alpha_dummy_108 R p))).fv ∪
        ((Class.cv (nb091_alpha_dummy_107 R p))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb091_support_mem_0119 (R : Class) (p : Var) :
    (nb091_alpha_dummy_108 R p) ∈
      (((syn_ccompl (Class.cab (nb091_alpha_dummy_121 R p)
              (syn_wrex (nb091_alpha_dummy_122 R p) (Class.cv (nb091_alpha_dummy_108 R p))
                (Wff.classEq (Class.cv (nb091_alpha_dummy_121 R p))
                  (syn_cphi (Class.cv (nb091_alpha_dummy_122 R p)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb091_alpha_dummy_121 R p)
              (syn_wrex (nb091_alpha_dummy_122 R p) (Class.cv (nb091_alpha_dummy_107 R p))
                (Wff.classEq (Class.cv (nb091_alpha_dummy_121 R p))
                  (syn_cun (syn_cphi (Class.cv (nb091_alpha_dummy_122 R p)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb091_alpha_dummy_108 R p) ≠ (nb091_alpha_dummy_121 R p) from (by
          unfold nb091_alpha_dummy_121;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb091_support_mem_0118 R p) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb091_alpha_dummy_108 R p) ≠ (nb091_alpha_dummy_122 R p) from (by
            unfold nb091_alpha_dummy_122;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb091_support_mem_0118 R p) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb091_support_mem_0120 (D : Class) (R : Class) :
    (nb091_alpha_dummy_106 D R) ∈
      (((Class.cab (nb091_alpha_dummy_119 D R)
            (syn_wrex (nb091_alpha_dummy_120 D R) (Class.cv (nb091_alpha_dummy_106 D R))
              (Wff.classEq (Class.cv (nb091_alpha_dummy_119 D R))
                (syn_cphi (Class.cv (nb091_alpha_dummy_120 D R))))))).fv ∪
        ((Class.cab (nb091_alpha_dummy_119 D R)
            (syn_wrex (nb091_alpha_dummy_120 D R) (Class.cv (nb091_alpha_dummy_106 D R))
              (Wff.classEq (Class.cv (nb091_alpha_dummy_119 D R))
                (syn_cphi (Class.cv (nb091_alpha_dummy_120 D R))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb091_alpha_dummy_106 D R) ≠ (nb091_alpha_dummy_119 D R) from (by
          unfold nb091_alpha_dummy_119;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb091_support_mem_0116 D R) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb091_alpha_dummy_106 D R) ≠ (nb091_alpha_dummy_120 D R) from (by
            unfold nb091_alpha_dummy_120;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb091_support_mem_0116 D R) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb091_support_mem_0121 (R : Class) (p : Var) :
    (nb091_alpha_dummy_108 R p) ∈
      (((Class.cab (nb091_alpha_dummy_121 R p)
            (syn_wrex (nb091_alpha_dummy_122 R p) (Class.cv (nb091_alpha_dummy_108 R p))
              (Wff.classEq (Class.cv (nb091_alpha_dummy_121 R p))
                (syn_cphi (Class.cv (nb091_alpha_dummy_122 R p))))))).fv ∪
        ((Class.cab (nb091_alpha_dummy_121 R p)
            (syn_wrex (nb091_alpha_dummy_122 R p) (Class.cv (nb091_alpha_dummy_108 R p))
              (Wff.classEq (Class.cv (nb091_alpha_dummy_121 R p))
                (syn_cphi (Class.cv (nb091_alpha_dummy_122 R p))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb091_alpha_dummy_108 R p) ≠ (nb091_alpha_dummy_121 R p) from (by
          unfold nb091_alpha_dummy_121;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb091_support_mem_0118 R p) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb091_alpha_dummy_108 R p) ≠ (nb091_alpha_dummy_122 R p) from (by
            unfold nb091_alpha_dummy_122;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb091_support_mem_0118 R p) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb091_support_mem_0122 (D : Class) (R : Class) :
    (nb091_alpha_dummy_120 D R) ∈ (((Class.cv (nb091_alpha_dummy_120 D R))).fv) :=
  by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb091_support_mem_0123 (R : Class) (p : Var) :
    (nb091_alpha_dummy_122 R p) ∈ (((Class.cv (nb091_alpha_dummy_122 R p))).fv) :=
  by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb091_support_mem_0124 (D : Class) (R : Class) :
    (nb091_alpha_dummy_127 D R) ∈
      (((Wff.classMem (Class.cv (nb091_alpha_dummy_127 D R)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb091_alpha_dummy_127 D R)) (syn_c1c))).fv ∪
        ((Class.cv (nb091_alpha_dummy_127 D R))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_wff_classMem]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb091_support_mem_0125 (R : Class) (p : Var) :
    (nb091_alpha_dummy_129 R p) ∈
      (((Wff.classMem (Class.cv (nb091_alpha_dummy_129 R p)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb091_alpha_dummy_129 R p)) (syn_c1c))).fv ∪
        ((Class.cv (nb091_alpha_dummy_129 R p))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_wff_classMem]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb091_support_mem_0126 (D : Class) (R : Class) :
    (nb091_alpha_dummy_127 D R) ∈
      (((Class.cv (nb091_alpha_dummy_127 D R))).fv ∪ ((syn_c1c)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb091_support_mem_0127 (R : Class) (p : Var) :
    (nb091_alpha_dummy_129 R p) ∈
      (((Class.cv (nb091_alpha_dummy_129 R p))).fv ∪ ((syn_c1c)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb091_support_mem_0128 (D : Class) (R : Class) :
    (nb091_alpha_dummy_134 D R) ∈
      (((syn_cnin (Class.cv (nb091_alpha_dummy_134 D R))
            (Class.cv (nb091_alpha_dummy_135 D R)))).fv ∪
        ((syn_cnin (Class.cv (nb091_alpha_dummy_134 D R))
            (Class.cv (nb091_alpha_dummy_135 D R)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb091_support_mem_0129 (R : Class) (p : Var) :
    (nb091_alpha_dummy_137 R p) ∈
      (((syn_cnin (Class.cv (nb091_alpha_dummy_137 R p))
            (Class.cv (nb091_alpha_dummy_138 R p)))).fv ∪
        ((syn_cnin (Class.cv (nb091_alpha_dummy_137 R p))
            (Class.cv (nb091_alpha_dummy_138 R p)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb091_support_mem_0130 (D : Class) (R : Class) :
    (nb091_alpha_dummy_134 D R) ∈
      (((Class.cv (nb091_alpha_dummy_134 D R))).fv ∪
        ((Class.cv (nb091_alpha_dummy_135 D R))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb091_support_mem_0131 (R : Class) (p : Var) :
    (nb091_alpha_dummy_137 R p) ∈
      (((Class.cv (nb091_alpha_dummy_137 R p))).fv ∪
        ((Class.cv (nb091_alpha_dummy_138 R p))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb091_support_mem_0132 (D : Class) (R : Class) :
    (nb091_alpha_dummy_135 D R) ∈
      (((syn_cnin (Class.cv (nb091_alpha_dummy_134 D R))
            (Class.cv (nb091_alpha_dummy_135 D R)))).fv ∪
        ((syn_cnin (Class.cv (nb091_alpha_dummy_134 D R))
            (Class.cv (nb091_alpha_dummy_135 D R)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb091_support_mem_0133 (R : Class) (p : Var) :
    (nb091_alpha_dummy_138 R p) ∈
      (((syn_cnin (Class.cv (nb091_alpha_dummy_137 R p))
            (Class.cv (nb091_alpha_dummy_138 R p)))).fv ∪
        ((syn_cnin (Class.cv (nb091_alpha_dummy_137 R p))
            (Class.cv (nb091_alpha_dummy_138 R p)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb091_support_mem_0134 (D : Class) (R : Class) :
    (nb091_alpha_dummy_135 D R) ∈
      (((Class.cv (nb091_alpha_dummy_134 D R))).fv ∪
        ((Class.cv (nb091_alpha_dummy_135 D R))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb091_support_mem_0135 (R : Class) (p : Var) :
    (nb091_alpha_dummy_138 R p) ∈
      (((Class.cv (nb091_alpha_dummy_137 R p))).fv ∪
        ((Class.cv (nb091_alpha_dummy_138 R p))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb091_support_mem_0136 (D : Class) (R : Class) :
    (nb091_alpha_dummy_134 D R) ∈
      (((syn_ccompl (Class.cv (nb091_alpha_dummy_134 D R)))).fv ∪
        ((syn_ccompl (Class.cv (nb091_alpha_dummy_135 D R)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb091_support_mem_0137 (R : Class) (p : Var) :
    (nb091_alpha_dummy_137 R p) ∈
      (((syn_ccompl (Class.cv (nb091_alpha_dummy_137 R p)))).fv ∪
        ((syn_ccompl (Class.cv (nb091_alpha_dummy_138 R p)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb091_support_mem_0138 (D : Class) (R : Class) :
    (nb091_alpha_dummy_134 D R) ∈
      (((Class.cv (nb091_alpha_dummy_134 D R))).fv ∪
        ((Class.cv (nb091_alpha_dummy_134 D R))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb091_support_mem_0139 (R : Class) (p : Var) :
    (nb091_alpha_dummy_137 R p) ∈
      (((Class.cv (nb091_alpha_dummy_137 R p))).fv ∪
        ((Class.cv (nb091_alpha_dummy_137 R p))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb091_support_mem_0140 (D : Class) (R : Class) :
    (nb091_alpha_dummy_135 D R) ∈
      (((syn_ccompl (Class.cv (nb091_alpha_dummy_134 D R)))).fv ∪
        ((syn_ccompl (Class.cv (nb091_alpha_dummy_135 D R)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb091_support_mem_0141 (R : Class) (p : Var) :
    (nb091_alpha_dummy_138 R p) ∈
      (((syn_ccompl (Class.cv (nb091_alpha_dummy_137 R p)))).fv ∪
        ((syn_ccompl (Class.cv (nb091_alpha_dummy_138 R p)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb091_support_mem_0142 (D : Class) (R : Class) :
    (nb091_alpha_dummy_135 D R) ∈
      (((Class.cv (nb091_alpha_dummy_135 D R))).fv ∪
        ((Class.cv (nb091_alpha_dummy_135 D R))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb091_support_mem_0143 (R : Class) (p : Var) :
    (nb091_alpha_dummy_138 R p) ∈
      (((Class.cv (nb091_alpha_dummy_138 R p))).fv ∪
        ((Class.cv (nb091_alpha_dummy_138 R p))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb091_support_mem_0144 (D : Class) (R : Class) :
    (nb091_alpha_dummy_105 D R) ∈
      (((Class.cv (nb091_alpha_dummy_106 D R))).fv ∪
        ((Class.cv (nb091_alpha_dummy_105 D R))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb091_support_mem_0145 (D : Class) (R : Class) :
    (nb091_alpha_dummy_105 D R) ∈
      (((syn_ccompl (Class.cab (nb091_alpha_dummy_119 D R)
              (syn_wrex (nb091_alpha_dummy_120 D R) (Class.cv (nb091_alpha_dummy_106 D R))
                (Wff.classEq (Class.cv (nb091_alpha_dummy_119 D R))
                  (syn_cphi (Class.cv (nb091_alpha_dummy_120 D R)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb091_alpha_dummy_119 D R)
              (syn_wrex (nb091_alpha_dummy_120 D R) (Class.cv (nb091_alpha_dummy_105 D R))
                (Wff.classEq (Class.cv (nb091_alpha_dummy_119 D R))
                  (syn_cun (syn_cphi (Class.cv (nb091_alpha_dummy_120 D R)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb091_alpha_dummy_105 D R) ≠ (nb091_alpha_dummy_119 D R) from (by
          unfold nb091_alpha_dummy_119;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb091_support_mem_0144 D R) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb091_alpha_dummy_105 D R) ≠ (nb091_alpha_dummy_120 D R) from (by
            unfold nb091_alpha_dummy_120;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb091_support_mem_0144 D R) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb091_support_mem_0146 (R : Class) (p : Var) :
    (nb091_alpha_dummy_107 R p) ∈
      (((Class.cv (nb091_alpha_dummy_108 R p))).fv ∪
        ((Class.cv (nb091_alpha_dummy_107 R p))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb091_support_mem_0147 (R : Class) (p : Var) :
    (nb091_alpha_dummy_107 R p) ∈
      (((syn_ccompl (Class.cab (nb091_alpha_dummy_121 R p)
              (syn_wrex (nb091_alpha_dummy_122 R p) (Class.cv (nb091_alpha_dummy_108 R p))
                (Wff.classEq (Class.cv (nb091_alpha_dummy_121 R p))
                  (syn_cphi (Class.cv (nb091_alpha_dummy_122 R p)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb091_alpha_dummy_121 R p)
              (syn_wrex (nb091_alpha_dummy_122 R p) (Class.cv (nb091_alpha_dummy_107 R p))
                (Wff.classEq (Class.cv (nb091_alpha_dummy_121 R p))
                  (syn_cun (syn_cphi (Class.cv (nb091_alpha_dummy_122 R p)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb091_alpha_dummy_107 R p) ≠ (nb091_alpha_dummy_121 R p) from (by
          unfold nb091_alpha_dummy_121;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb091_support_mem_0146 R p) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb091_alpha_dummy_107 R p) ≠ (nb091_alpha_dummy_122 R p) from (by
            unfold nb091_alpha_dummy_122;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb091_support_mem_0146 R p) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb091_support_mem_0148 (D : Class) (R : Class) :
    (nb091_alpha_dummy_105 D R) ∈
      (((Class.cab (nb091_alpha_dummy_119 D R)
            (syn_wrex (nb091_alpha_dummy_120 D R) (Class.cv (nb091_alpha_dummy_105 D R))
              (Wff.classEq (Class.cv (nb091_alpha_dummy_119 D R))
                (syn_cun (syn_cphi (Class.cv (nb091_alpha_dummy_120 D R)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb091_alpha_dummy_119 D R)
            (syn_wrex (nb091_alpha_dummy_120 D R) (Class.cv (nb091_alpha_dummy_105 D R))
              (Wff.classEq (Class.cv (nb091_alpha_dummy_119 D R))
                (syn_cun (syn_cphi (Class.cv (nb091_alpha_dummy_120 D R)))
                  (syn_csn (syn_c0c))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb091_alpha_dummy_105 D R) ≠ (nb091_alpha_dummy_119 D R) from (by
          unfold nb091_alpha_dummy_119;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb091_support_mem_0144 D R) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb091_alpha_dummy_105 D R) ≠ (nb091_alpha_dummy_120 D R) from (by
            unfold nb091_alpha_dummy_120;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb091_support_mem_0144 D R) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb091_support_mem_0149 (R : Class) (p : Var) :
    (nb091_alpha_dummy_107 R p) ∈
      (((Class.cab (nb091_alpha_dummy_121 R p)
            (syn_wrex (nb091_alpha_dummy_122 R p) (Class.cv (nb091_alpha_dummy_107 R p))
              (Wff.classEq (Class.cv (nb091_alpha_dummy_121 R p))
                (syn_cun (syn_cphi (Class.cv (nb091_alpha_dummy_122 R p)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb091_alpha_dummy_121 R p)
            (syn_wrex (nb091_alpha_dummy_122 R p) (Class.cv (nb091_alpha_dummy_107 R p))
              (Wff.classEq (Class.cv (nb091_alpha_dummy_121 R p))
                (syn_cun (syn_cphi (Class.cv (nb091_alpha_dummy_122 R p)))
                  (syn_csn (syn_c0c))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb091_alpha_dummy_107 R p) ≠ (nb091_alpha_dummy_121 R p) from (by
          unfold nb091_alpha_dummy_121;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb091_support_mem_0146 R p) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb091_alpha_dummy_107 R p) ≠ (nb091_alpha_dummy_122 R p) from (by
            unfold nb091_alpha_dummy_122;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb091_support_mem_0146 R p) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb091_support_mem_0150 (D : Class) (R : Class) :
    (nb091_alpha_dummy_120 D R) ∈
      (((syn_ccompl (syn_cphi (Class.cv (nb091_alpha_dummy_120 D R))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb091_support_mem_0151 (R : Class) (p : Var) :
    (nb091_alpha_dummy_122 R p) ∈
      (((syn_ccompl (syn_cphi (Class.cv (nb091_alpha_dummy_122 R p))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb091_support_mem_0152 (D : Class) (R : Class) :
    (nb091_alpha_dummy_120 D R) ∈
      (((syn_cphi (Class.cv (nb091_alpha_dummy_120 D R)))).fv ∪
        ((syn_cphi (Class.cv (nb091_alpha_dummy_120 D R)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb091_support_mem_0153 (R : Class) (p : Var) :
    (nb091_alpha_dummy_122 R p) ∈
      (((syn_cphi (Class.cv (nb091_alpha_dummy_122 R p)))).fv ∪
        ((syn_cphi (Class.cv (nb091_alpha_dummy_122 R p)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb091_support_mem_0154 (D : Class) (R : Class) :
    (nb091_alpha_dummy_048 D R) ∈ (((Class.cv (nb091_alpha_dummy_048 D R))).fv) :=
  by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb091_support_mem_0155 (D : Class) (R : Class) (p : Var) :
    (nb091_alpha_dummy_050 D R p) ∈ (((Class.cv (nb091_alpha_dummy_050 D R p))).fv) :=
  by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb091_support_mem_0156 (D : Class) (R : Class) :
    (nb091_alpha_dummy_155 D R) ∈
      (((Wff.classMem (Class.cv (nb091_alpha_dummy_155 D R)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb091_alpha_dummy_155 D R)) (syn_c1c))).fv ∪
        ((Class.cv (nb091_alpha_dummy_155 D R))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_wff_classMem]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb091_support_mem_0157 (D : Class) (R : Class) (p : Var) :
    (nb091_alpha_dummy_157 D R p) ∈
      (((Wff.classMem (Class.cv (nb091_alpha_dummy_157 D R p)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb091_alpha_dummy_157 D R p)) (syn_c1c))).fv ∪
        ((Class.cv (nb091_alpha_dummy_157 D R p))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_wff_classMem]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb091_support_mem_0158 (D : Class) (R : Class) :
    (nb091_alpha_dummy_155 D R) ∈
      (((Class.cv (nb091_alpha_dummy_155 D R))).fv ∪ ((syn_c1c)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb091_support_mem_0159 (D : Class) (R : Class) (p : Var) :
    (nb091_alpha_dummy_157 D R p) ∈
      (((Class.cv (nb091_alpha_dummy_157 D R p))).fv ∪ ((syn_c1c)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb091_support_mem_0160 (D : Class) (R : Class) :
    (nb091_alpha_dummy_162 D R) ∈
      (((syn_cnin (Class.cv (nb091_alpha_dummy_162 D R))
            (Class.cv (nb091_alpha_dummy_163 D R)))).fv ∪
        ((syn_cnin (Class.cv (nb091_alpha_dummy_162 D R))
            (Class.cv (nb091_alpha_dummy_163 D R)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb091_support_mem_0161 (D : Class) (R : Class) (p : Var) :
    (nb091_alpha_dummy_165 D R p) ∈
      (((syn_cnin (Class.cv (nb091_alpha_dummy_165 D R p))
            (Class.cv (nb091_alpha_dummy_166 D R p)))).fv ∪
        ((syn_cnin (Class.cv (nb091_alpha_dummy_165 D R p))
            (Class.cv (nb091_alpha_dummy_166 D R p)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb091_support_mem_0162 (D : Class) (R : Class) :
    (nb091_alpha_dummy_162 D R) ∈
      (((Class.cv (nb091_alpha_dummy_162 D R))).fv ∪
        ((Class.cv (nb091_alpha_dummy_163 D R))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb091_support_mem_0163 (D : Class) (R : Class) (p : Var) :
    (nb091_alpha_dummy_165 D R p) ∈
      (((Class.cv (nb091_alpha_dummy_165 D R p))).fv ∪
        ((Class.cv (nb091_alpha_dummy_166 D R p))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb091_support_mem_0164 (D : Class) (R : Class) :
    (nb091_alpha_dummy_163 D R) ∈
      (((syn_cnin (Class.cv (nb091_alpha_dummy_162 D R))
            (Class.cv (nb091_alpha_dummy_163 D R)))).fv ∪
        ((syn_cnin (Class.cv (nb091_alpha_dummy_162 D R))
            (Class.cv (nb091_alpha_dummy_163 D R)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb091_support_mem_0165 (D : Class) (R : Class) (p : Var) :
    (nb091_alpha_dummy_166 D R p) ∈
      (((syn_cnin (Class.cv (nb091_alpha_dummy_165 D R p))
            (Class.cv (nb091_alpha_dummy_166 D R p)))).fv ∪
        ((syn_cnin (Class.cv (nb091_alpha_dummy_165 D R p))
            (Class.cv (nb091_alpha_dummy_166 D R p)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb091_support_mem_0166 (D : Class) (R : Class) :
    (nb091_alpha_dummy_163 D R) ∈
      (((Class.cv (nb091_alpha_dummy_162 D R))).fv ∪
        ((Class.cv (nb091_alpha_dummy_163 D R))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb091_support_mem_0167 (D : Class) (R : Class) (p : Var) :
    (nb091_alpha_dummy_166 D R p) ∈
      (((Class.cv (nb091_alpha_dummy_165 D R p))).fv ∪
        ((Class.cv (nb091_alpha_dummy_166 D R p))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb091_support_mem_0168 (D : Class) (R : Class) :
    (nb091_alpha_dummy_162 D R) ∈
      (((syn_ccompl (Class.cv (nb091_alpha_dummy_162 D R)))).fv ∪
        ((syn_ccompl (Class.cv (nb091_alpha_dummy_163 D R)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb091_support_mem_0169 (D : Class) (R : Class) (p : Var) :
    (nb091_alpha_dummy_165 D R p) ∈
      (((syn_ccompl (Class.cv (nb091_alpha_dummy_165 D R p)))).fv ∪
        ((syn_ccompl (Class.cv (nb091_alpha_dummy_166 D R p)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb091_support_mem_0170 (D : Class) (R : Class) :
    (nb091_alpha_dummy_162 D R) ∈
      (((Class.cv (nb091_alpha_dummy_162 D R))).fv ∪
        ((Class.cv (nb091_alpha_dummy_162 D R))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb091_support_mem_0171 (D : Class) (R : Class) (p : Var) :
    (nb091_alpha_dummy_165 D R p) ∈
      (((Class.cv (nb091_alpha_dummy_165 D R p))).fv ∪
        ((Class.cv (nb091_alpha_dummy_165 D R p))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb091_support_mem_0172 (D : Class) (R : Class) :
    (nb091_alpha_dummy_163 D R) ∈
      (((syn_ccompl (Class.cv (nb091_alpha_dummy_162 D R)))).fv ∪
        ((syn_ccompl (Class.cv (nb091_alpha_dummy_163 D R)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb091_support_mem_0173 (D : Class) (R : Class) (p : Var) :
    (nb091_alpha_dummy_166 D R p) ∈
      (((syn_ccompl (Class.cv (nb091_alpha_dummy_165 D R p)))).fv ∪
        ((syn_ccompl (Class.cv (nb091_alpha_dummy_166 D R p)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb091_support_mem_0174 (D : Class) (R : Class) :
    (nb091_alpha_dummy_163 D R) ∈
      (((Class.cv (nb091_alpha_dummy_163 D R))).fv ∪
        ((Class.cv (nb091_alpha_dummy_163 D R))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb091_support_mem_0175 (D : Class) (R : Class) (p : Var) :
    (nb091_alpha_dummy_166 D R p) ∈
      (((Class.cv (nb091_alpha_dummy_166 D R p))).fv ∪
        ((Class.cv (nb091_alpha_dummy_166 D R p))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb091_support_mem_0176 (D : Class) (R : Class) :
    (nb091_alpha_dummy_000 D R) ∈
      (((Class.cab (nb091_alpha_dummy_047 D R) (syn_wrex (nb091_alpha_dummy_048 D R) (syn_cin D
                (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
                  (syn_csn (syn_cuni (syn_cuni (Class.cv (nb091_alpha_dummy_000 D R)))))))
              (Wff.classEq (Class.cv (nb091_alpha_dummy_047 D R))
                (syn_cun (syn_cphi (Class.cv (nb091_alpha_dummy_048 D R)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb091_alpha_dummy_047 D R)
            (syn_wrex (nb091_alpha_dummy_048 D R) (syn_cin D
                (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
                  (syn_csn (syn_cuni (syn_cuni (Class.cv (nb091_alpha_dummy_000 D R)))))))
              (Wff.classEq (Class.cv (nb091_alpha_dummy_047 D R))
                (syn_cun (syn_cphi (Class.cv (nb091_alpha_dummy_048 D R)))
                  (syn_csn (syn_c0c))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb091_alpha_dummy_000 D R) ≠ (nb091_alpha_dummy_047 D R) from (by
          unfold nb091_alpha_dummy_047;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb091_support_mem_0090 D R) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb091_alpha_dummy_000 D R) ≠ (nb091_alpha_dummy_048 D R) from (by
            unfold nb091_alpha_dummy_048;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb091_support_mem_0090 D R) 1))))
    · rw [fv_syn_cin]
      with_reducible rw [Finset.mem_union]
      right
      rw [fv_syn_cima]
      with_reducible rw [Finset.mem_union]
      right
      rw [fv_syn_csn]
      rw [fv_syn_cuni]
      rw [fv_syn_cuni]
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb091_support_mem_0177 (D : Class) (R : Class) (p : Var) :
    p ∈
      (((Class.cab (nb091_alpha_dummy_049 D R p) (syn_wrex (nb091_alpha_dummy_050 D R p)
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
                  (syn_csn (syn_cuni (syn_cuni (Class.cv p))))))
              (Wff.classEq (Class.cv (nb091_alpha_dummy_049 D R p))
                (syn_cun (syn_cphi (Class.cv (nb091_alpha_dummy_050 D R p)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb091_alpha_dummy_049 D R p)
            (syn_wrex (nb091_alpha_dummy_050 D R p) (syn_cin D
                (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
                  (syn_csn (syn_cuni (syn_cuni (Class.cv p))))))
              (Wff.classEq (Class.cv (nb091_alpha_dummy_049 D R p))
                (syn_cun (syn_cphi (Class.cv (nb091_alpha_dummy_050 D R p)))
                  (syn_csn (syn_c0c))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show p ≠ (nb091_alpha_dummy_049 D R p) from (by
          unfold nb091_alpha_dummy_049;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb091_support_mem_0092 D R p) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show p ≠ (nb091_alpha_dummy_050 D R p) from (by
            unfold nb091_alpha_dummy_050;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb091_support_mem_0092 D R p) 1))))
    · rw [fv_syn_cin]
      with_reducible rw [Finset.mem_union]
      right
      rw [fv_syn_cima]
      with_reducible rw [Finset.mem_union]
      right
      rw [fv_syn_csn]
      rw [fv_syn_cuni]
      rw [fv_syn_cuni]
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb091_support_mem_0178 (D : Class) (R : Class) :
    (nb091_alpha_dummy_048 D R) ∈
      (((syn_ccompl (syn_cphi (Class.cv (nb091_alpha_dummy_048 D R))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb091_support_mem_0179 (D : Class) (R : Class) (p : Var) :
    (nb091_alpha_dummy_050 D R p) ∈
      (((syn_ccompl (syn_cphi (Class.cv (nb091_alpha_dummy_050 D R p))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb091_support_mem_0180 (D : Class) (R : Class) :
    (nb091_alpha_dummy_048 D R) ∈
      (((syn_cphi (Class.cv (nb091_alpha_dummy_048 D R)))).fv ∪
        ((syn_cphi (Class.cv (nb091_alpha_dummy_048 D R)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb091_support_mem_0181 (D : Class) (R : Class) (p : Var) :
    (nb091_alpha_dummy_050 D R p) ∈
      (((syn_cphi (Class.cv (nb091_alpha_dummy_050 D R p)))).fv ∪
        ((syn_cphi (Class.cv (nb091_alpha_dummy_050 D R p)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb091_support_mem_0182 (D : Class) (R : Class) :
    (nb091_alpha_dummy_042 D R) ∈
      (((Class.cv (nb091_alpha_dummy_042 D R))).fv ∪
        ((Class.cv (nb091_alpha_dummy_041 D R))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired


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

theorem nb091_support_mem_0183 (D : Class) (R : Class) :
    (nb091_alpha_dummy_042 D R) ∈
      (((syn_ccompl (Class.cab (nb091_alpha_dummy_183 D R)
              (syn_wrex (nb091_alpha_dummy_184 D R) (Class.cv (nb091_alpha_dummy_042 D R))
                (Wff.classEq (Class.cv (nb091_alpha_dummy_183 D R))
                  (syn_cphi (Class.cv (nb091_alpha_dummy_184 D R)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb091_alpha_dummy_183 D R)
              (syn_wrex (nb091_alpha_dummy_184 D R) (Class.cv (nb091_alpha_dummy_041 D R))
                (Wff.classEq (Class.cv (nb091_alpha_dummy_183 D R))
                  (syn_cun (syn_cphi (Class.cv (nb091_alpha_dummy_184 D R)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb091_alpha_dummy_042 D R) ≠ (nb091_alpha_dummy_183 D R) from (by
          unfold nb091_alpha_dummy_183;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb091_support_mem_0182 D R) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb091_alpha_dummy_042 D R) ≠ (nb091_alpha_dummy_184 D R) from (by
            unfold nb091_alpha_dummy_184;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb091_support_mem_0182 D R) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb091_support_mem_0184 (D : Class) (R : Class) (p : Var) :
    (nb091_alpha_dummy_044 D R p) ∈
      (((Class.cv (nb091_alpha_dummy_044 D R p))).fv ∪
        ((Class.cv (nb091_alpha_dummy_043 D R p))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb091_support_mem_0185 (D : Class) (R : Class) (p : Var) :
    (nb091_alpha_dummy_044 D R p) ∈
      (((syn_ccompl (Class.cab (nb091_alpha_dummy_185 D R p)
              (syn_wrex (nb091_alpha_dummy_186 D R p) (Class.cv (nb091_alpha_dummy_044 D R p))
                (Wff.classEq (Class.cv (nb091_alpha_dummy_185 D R p))
                  (syn_cphi (Class.cv (nb091_alpha_dummy_186 D R p)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb091_alpha_dummy_185 D R p) (syn_wrex (nb091_alpha_dummy_186 D R p)
                (Class.cv (nb091_alpha_dummy_043 D R p))
                (Wff.classEq (Class.cv (nb091_alpha_dummy_185 D R p))
                  (syn_cun (syn_cphi (Class.cv (nb091_alpha_dummy_186 D R p)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb091_alpha_dummy_044 D R p) ≠ (nb091_alpha_dummy_185 D R p) from (by
          unfold nb091_alpha_dummy_185;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb091_support_mem_0184 D R p) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb091_alpha_dummy_044 D R p) ≠ (nb091_alpha_dummy_186 D R p) from (by
            unfold nb091_alpha_dummy_186;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb091_support_mem_0184 D R p) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb091_support_mem_0186 (D : Class) (R : Class) :
    (nb091_alpha_dummy_042 D R) ∈
      (((Class.cab (nb091_alpha_dummy_183 D R)
            (syn_wrex (nb091_alpha_dummy_184 D R) (Class.cv (nb091_alpha_dummy_042 D R))
              (Wff.classEq (Class.cv (nb091_alpha_dummy_183 D R))
                (syn_cphi (Class.cv (nb091_alpha_dummy_184 D R))))))).fv ∪
        ((Class.cab (nb091_alpha_dummy_183 D R)
            (syn_wrex (nb091_alpha_dummy_184 D R) (Class.cv (nb091_alpha_dummy_042 D R))
              (Wff.classEq (Class.cv (nb091_alpha_dummy_183 D R))
                (syn_cphi (Class.cv (nb091_alpha_dummy_184 D R))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb091_alpha_dummy_042 D R) ≠ (nb091_alpha_dummy_183 D R) from (by
          unfold nb091_alpha_dummy_183;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb091_support_mem_0182 D R) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb091_alpha_dummy_042 D R) ≠ (nb091_alpha_dummy_184 D R) from (by
            unfold nb091_alpha_dummy_184;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb091_support_mem_0182 D R) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb091_support_mem_0187 (D : Class) (R : Class) (p : Var) :
    (nb091_alpha_dummy_044 D R p) ∈
      (((Class.cab (nb091_alpha_dummy_185 D R p) (syn_wrex (nb091_alpha_dummy_186 D R p)
              (Class.cv (nb091_alpha_dummy_044 D R p))
              (Wff.classEq (Class.cv (nb091_alpha_dummy_185 D R p))
                (syn_cphi (Class.cv (nb091_alpha_dummy_186 D R p))))))).fv ∪
        ((Class.cab (nb091_alpha_dummy_185 D R p) (syn_wrex (nb091_alpha_dummy_186 D R p)
              (Class.cv (nb091_alpha_dummy_044 D R p))
              (Wff.classEq (Class.cv (nb091_alpha_dummy_185 D R p))
                (syn_cphi (Class.cv (nb091_alpha_dummy_186 D R p))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb091_alpha_dummy_044 D R p) ≠ (nb091_alpha_dummy_185 D R p) from (by
          unfold nb091_alpha_dummy_185;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb091_support_mem_0184 D R p) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb091_alpha_dummy_044 D R p) ≠ (nb091_alpha_dummy_186 D R p) from (by
            unfold nb091_alpha_dummy_186;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb091_support_mem_0184 D R p) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb091_support_mem_0188 (D : Class) (R : Class) :
    (nb091_alpha_dummy_184 D R) ∈ (((Class.cv (nb091_alpha_dummy_184 D R))).fv) :=
  by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb091_support_mem_0189 (D : Class) (R : Class) (p : Var) :
    (nb091_alpha_dummy_186 D R p) ∈ (((Class.cv (nb091_alpha_dummy_186 D R p))).fv) :=
  by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb091_support_mem_0190 (D : Class) (R : Class) :
    (nb091_alpha_dummy_191 D R) ∈
      (((Wff.classMem (Class.cv (nb091_alpha_dummy_191 D R)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb091_alpha_dummy_191 D R)) (syn_c1c))).fv ∪
        ((Class.cv (nb091_alpha_dummy_191 D R))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_wff_classMem]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb091_support_mem_0191 (D : Class) (R : Class) (p : Var) :
    (nb091_alpha_dummy_193 D R p) ∈
      (((Wff.classMem (Class.cv (nb091_alpha_dummy_193 D R p)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb091_alpha_dummy_193 D R p)) (syn_c1c))).fv ∪
        ((Class.cv (nb091_alpha_dummy_193 D R p))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_wff_classMem]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb091_support_mem_0192 (D : Class) (R : Class) :
    (nb091_alpha_dummy_191 D R) ∈
      (((Class.cv (nb091_alpha_dummy_191 D R))).fv ∪ ((syn_c1c)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb091_support_mem_0193 (D : Class) (R : Class) (p : Var) :
    (nb091_alpha_dummy_193 D R p) ∈
      (((Class.cv (nb091_alpha_dummy_193 D R p))).fv ∪ ((syn_c1c)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb091_support_mem_0194 (D : Class) (R : Class) :
    (nb091_alpha_dummy_198 D R) ∈
      (((syn_cnin (Class.cv (nb091_alpha_dummy_198 D R))
            (Class.cv (nb091_alpha_dummy_199 D R)))).fv ∪
        ((syn_cnin (Class.cv (nb091_alpha_dummy_198 D R))
            (Class.cv (nb091_alpha_dummy_199 D R)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb091_support_mem_0195 (D : Class) (R : Class) (p : Var) :
    (nb091_alpha_dummy_201 D R p) ∈
      (((syn_cnin (Class.cv (nb091_alpha_dummy_201 D R p))
            (Class.cv (nb091_alpha_dummy_202 D R p)))).fv ∪
        ((syn_cnin (Class.cv (nb091_alpha_dummy_201 D R p))
            (Class.cv (nb091_alpha_dummy_202 D R p)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb091_support_mem_0196 (D : Class) (R : Class) :
    (nb091_alpha_dummy_198 D R) ∈
      (((Class.cv (nb091_alpha_dummy_198 D R))).fv ∪
        ((Class.cv (nb091_alpha_dummy_199 D R))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb091_support_mem_0197 (D : Class) (R : Class) (p : Var) :
    (nb091_alpha_dummy_201 D R p) ∈
      (((Class.cv (nb091_alpha_dummy_201 D R p))).fv ∪
        ((Class.cv (nb091_alpha_dummy_202 D R p))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb091_support_mem_0198 (D : Class) (R : Class) :
    (nb091_alpha_dummy_199 D R) ∈
      (((syn_cnin (Class.cv (nb091_alpha_dummy_198 D R))
            (Class.cv (nb091_alpha_dummy_199 D R)))).fv ∪
        ((syn_cnin (Class.cv (nb091_alpha_dummy_198 D R))
            (Class.cv (nb091_alpha_dummy_199 D R)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb091_support_mem_0199 (D : Class) (R : Class) (p : Var) :
    (nb091_alpha_dummy_202 D R p) ∈
      (((syn_cnin (Class.cv (nb091_alpha_dummy_201 D R p))
            (Class.cv (nb091_alpha_dummy_202 D R p)))).fv ∪
        ((syn_cnin (Class.cv (nb091_alpha_dummy_201 D R p))
            (Class.cv (nb091_alpha_dummy_202 D R p)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb091_support_mem_0200 (D : Class) (R : Class) :
    (nb091_alpha_dummy_199 D R) ∈
      (((Class.cv (nb091_alpha_dummy_198 D R))).fv ∪
        ((Class.cv (nb091_alpha_dummy_199 D R))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb091_support_mem_0201 (D : Class) (R : Class) (p : Var) :
    (nb091_alpha_dummy_202 D R p) ∈
      (((Class.cv (nb091_alpha_dummy_201 D R p))).fv ∪
        ((Class.cv (nb091_alpha_dummy_202 D R p))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb091_support_mem_0202 (D : Class) (R : Class) :
    (nb091_alpha_dummy_198 D R) ∈
      (((syn_ccompl (Class.cv (nb091_alpha_dummy_198 D R)))).fv ∪
        ((syn_ccompl (Class.cv (nb091_alpha_dummy_199 D R)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb091_support_mem_0203 (D : Class) (R : Class) (p : Var) :
    (nb091_alpha_dummy_201 D R p) ∈
      (((syn_ccompl (Class.cv (nb091_alpha_dummy_201 D R p)))).fv ∪
        ((syn_ccompl (Class.cv (nb091_alpha_dummy_202 D R p)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb091_support_mem_0204 (D : Class) (R : Class) :
    (nb091_alpha_dummy_198 D R) ∈
      (((Class.cv (nb091_alpha_dummy_198 D R))).fv ∪
        ((Class.cv (nb091_alpha_dummy_198 D R))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb091_support_mem_0205 (D : Class) (R : Class) (p : Var) :
    (nb091_alpha_dummy_201 D R p) ∈
      (((Class.cv (nb091_alpha_dummy_201 D R p))).fv ∪
        ((Class.cv (nb091_alpha_dummy_201 D R p))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb091_support_mem_0206 (D : Class) (R : Class) :
    (nb091_alpha_dummy_199 D R) ∈
      (((syn_ccompl (Class.cv (nb091_alpha_dummy_198 D R)))).fv ∪
        ((syn_ccompl (Class.cv (nb091_alpha_dummy_199 D R)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb091_support_mem_0207 (D : Class) (R : Class) (p : Var) :
    (nb091_alpha_dummy_202 D R p) ∈
      (((syn_ccompl (Class.cv (nb091_alpha_dummy_201 D R p)))).fv ∪
        ((syn_ccompl (Class.cv (nb091_alpha_dummy_202 D R p)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb091_support_mem_0208 (D : Class) (R : Class) :
    (nb091_alpha_dummy_199 D R) ∈
      (((Class.cv (nb091_alpha_dummy_199 D R))).fv ∪
        ((Class.cv (nb091_alpha_dummy_199 D R))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb091_support_mem_0209 (D : Class) (R : Class) (p : Var) :
    (nb091_alpha_dummy_202 D R p) ∈
      (((Class.cv (nb091_alpha_dummy_202 D R p))).fv ∪
        ((Class.cv (nb091_alpha_dummy_202 D R p))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb091_support_mem_0210 (D : Class) (R : Class) :
    (nb091_alpha_dummy_041 D R) ∈
      (((Class.cv (nb091_alpha_dummy_042 D R))).fv ∪
        ((Class.cv (nb091_alpha_dummy_041 D R))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb091_support_mem_0211 (D : Class) (R : Class) :
    (nb091_alpha_dummy_041 D R) ∈
      (((syn_ccompl (Class.cab (nb091_alpha_dummy_183 D R)
              (syn_wrex (nb091_alpha_dummy_184 D R) (Class.cv (nb091_alpha_dummy_042 D R))
                (Wff.classEq (Class.cv (nb091_alpha_dummy_183 D R))
                  (syn_cphi (Class.cv (nb091_alpha_dummy_184 D R)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb091_alpha_dummy_183 D R)
              (syn_wrex (nb091_alpha_dummy_184 D R) (Class.cv (nb091_alpha_dummy_041 D R))
                (Wff.classEq (Class.cv (nb091_alpha_dummy_183 D R))
                  (syn_cun (syn_cphi (Class.cv (nb091_alpha_dummy_184 D R)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb091_alpha_dummy_041 D R) ≠ (nb091_alpha_dummy_183 D R) from (by
          unfold nb091_alpha_dummy_183;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb091_support_mem_0210 D R) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb091_alpha_dummy_041 D R) ≠ (nb091_alpha_dummy_184 D R) from (by
            unfold nb091_alpha_dummy_184;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb091_support_mem_0210 D R) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb091_support_mem_0212 (D : Class) (R : Class) (p : Var) :
    (nb091_alpha_dummy_043 D R p) ∈
      (((Class.cv (nb091_alpha_dummy_044 D R p))).fv ∪
        ((Class.cv (nb091_alpha_dummy_043 D R p))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb091_support_mem_0213 (D : Class) (R : Class) (p : Var) :
    (nb091_alpha_dummy_043 D R p) ∈
      (((syn_ccompl (Class.cab (nb091_alpha_dummy_185 D R p)
              (syn_wrex (nb091_alpha_dummy_186 D R p) (Class.cv (nb091_alpha_dummy_044 D R p))
                (Wff.classEq (Class.cv (nb091_alpha_dummy_185 D R p))
                  (syn_cphi (Class.cv (nb091_alpha_dummy_186 D R p)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb091_alpha_dummy_185 D R p) (syn_wrex (nb091_alpha_dummy_186 D R p)
                (Class.cv (nb091_alpha_dummy_043 D R p))
                (Wff.classEq (Class.cv (nb091_alpha_dummy_185 D R p))
                  (syn_cun (syn_cphi (Class.cv (nb091_alpha_dummy_186 D R p)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb091_alpha_dummy_043 D R p) ≠ (nb091_alpha_dummy_185 D R p) from (by
          unfold nb091_alpha_dummy_185;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb091_support_mem_0212 D R p) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb091_alpha_dummy_043 D R p) ≠ (nb091_alpha_dummy_186 D R p) from (by
            unfold nb091_alpha_dummy_186;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb091_support_mem_0212 D R p) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb091_support_mem_0214 (D : Class) (R : Class) :
    (nb091_alpha_dummy_041 D R) ∈
      (((Class.cab (nb091_alpha_dummy_183 D R)
            (syn_wrex (nb091_alpha_dummy_184 D R) (Class.cv (nb091_alpha_dummy_041 D R))
              (Wff.classEq (Class.cv (nb091_alpha_dummy_183 D R))
                (syn_cun (syn_cphi (Class.cv (nb091_alpha_dummy_184 D R)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb091_alpha_dummy_183 D R)
            (syn_wrex (nb091_alpha_dummy_184 D R) (Class.cv (nb091_alpha_dummy_041 D R))
              (Wff.classEq (Class.cv (nb091_alpha_dummy_183 D R))
                (syn_cun (syn_cphi (Class.cv (nb091_alpha_dummy_184 D R)))
                  (syn_csn (syn_c0c))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb091_alpha_dummy_041 D R) ≠ (nb091_alpha_dummy_183 D R) from (by
          unfold nb091_alpha_dummy_183;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb091_support_mem_0210 D R) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb091_alpha_dummy_041 D R) ≠ (nb091_alpha_dummy_184 D R) from (by
            unfold nb091_alpha_dummy_184;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb091_support_mem_0210 D R) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb091_support_mem_0215 (D : Class) (R : Class) (p : Var) :
    (nb091_alpha_dummy_043 D R p) ∈
      (((Class.cab (nb091_alpha_dummy_185 D R p) (syn_wrex (nb091_alpha_dummy_186 D R p)
              (Class.cv (nb091_alpha_dummy_043 D R p))
              (Wff.classEq (Class.cv (nb091_alpha_dummy_185 D R p))
                (syn_cun (syn_cphi (Class.cv (nb091_alpha_dummy_186 D R p)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb091_alpha_dummy_185 D R p)
            (syn_wrex (nb091_alpha_dummy_186 D R p) (Class.cv (nb091_alpha_dummy_043 D R p))
              (Wff.classEq (Class.cv (nb091_alpha_dummy_185 D R p))
                (syn_cun (syn_cphi (Class.cv (nb091_alpha_dummy_186 D R p)))
                  (syn_csn (syn_c0c))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb091_alpha_dummy_043 D R p) ≠ (nb091_alpha_dummy_185 D R p) from (by
          unfold nb091_alpha_dummy_185;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb091_support_mem_0212 D R p) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb091_alpha_dummy_043 D R p) ≠ (nb091_alpha_dummy_186 D R p) from (by
            unfold nb091_alpha_dummy_186;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb091_support_mem_0212 D R p) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb091_support_mem_0216 (D : Class) (R : Class) :
    (nb091_alpha_dummy_184 D R) ∈
      (((syn_ccompl (syn_cphi (Class.cv (nb091_alpha_dummy_184 D R))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb091_support_mem_0217 (D : Class) (R : Class) (p : Var) :
    (nb091_alpha_dummy_186 D R p) ∈
      (((syn_ccompl (syn_cphi (Class.cv (nb091_alpha_dummy_186 D R p))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb091_support_mem_0218 (D : Class) (R : Class) :
    (nb091_alpha_dummy_184 D R) ∈
      (((syn_cphi (Class.cv (nb091_alpha_dummy_184 D R)))).fv ∪
        ((syn_cphi (Class.cv (nb091_alpha_dummy_184 D R)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb091_support_mem_0219 (D : Class) (R : Class) (p : Var) :
    (nb091_alpha_dummy_186 D R p) ∈
      (((syn_cphi (Class.cv (nb091_alpha_dummy_186 D R p)))).fv ∪
        ((syn_cphi (Class.cv (nb091_alpha_dummy_186 D R p)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb091_compact_fv_empty_0020 (D : Class) (R : Class) :
    (nb091_alpha_dummy_001 D R) ∉ (∅ : Finset Var) :=
  by
  intro hmem
  cases hmem

theorem nb091_compact_fv_empty_0021 (D : Class) (R : Class) (p : Var) :
    (nb091_alpha_dummy_002 D R p) ∉ (∅ : Finset Var) :=
  by
  intro hmem
  cases hmem

theorem nb091_compact_fv_empty_0022 (D : Class) (R : Class) :
    (nb091_alpha_dummy_000 D R) ∉ (∅ : Finset Var) :=
  by
  intro hmem
  cases hmem

theorem nb091_compact_fv_empty_0023 (p : Var) : p ∉ (∅ : Finset Var) :=
  by
  intro hmem
  cases hmem

theorem nb091_compact_fv_empty_0024 (D : Class) (R : Class) :
    (nb091_alpha_dummy_003 D R) ∉ (∅ : Finset Var) :=
  by
  intro hmem
  cases hmem

theorem nb091_compact_fv_empty_0025 (D : Class) (R : Class) (p : Var) :
    (nb091_alpha_dummy_004 D R p) ∉ (∅ : Finset Var) :=
  by
  intro hmem
  cases hmem


end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired
