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
    (nb091AlphaDummy060 D R) ∉
      (((synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn
                (synCuni (synCuni (Class.cv (nb091AlphaDummy000 D R)))))))).fv ∪
        ((synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn
                (synCuni (synCuni (Class.cv (nb091AlphaDummy000 D R)))))))).fv) :=
  by
  simpa only [nb091AlphaDummy060] using
    freshVar_not_mem
      (((synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn
                (synCuni (synCuni (Class.cv (nb091AlphaDummy000 D R)))))))).fv ∪
        ((synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn
                (synCuni (synCuni (Class.cv (nb091AlphaDummy000 D R)))))))).fv)
      1

theorem nb091_distinct_226 (D : Class) (R : Class) :
    (nb091AlphaDummy059 D R) ≠ (nb091AlphaDummy060 D R) := by
  simpa only [nb091AlphaDummy059, nb091AlphaDummy060] using
    (freshVar_injective (((synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn
                (synCuni (synCuni (Class.cv (nb091AlphaDummy000 D R)))))))).fv ∪
        ((synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn
                (synCuni (synCuni (Class.cv (nb091AlphaDummy000 D R)))))))).fv)
      (i := 0) (j := 1) (by decide))

theorem nb091_fresh_227 (D : Class) (R : Class) (p : Var) :
    (nb091AlphaDummy061 D R p) ∉
      (((synCin D (synCima (synCcnv (synCdif R (synCid)))
              (synCsn (synCuni (synCuni (Class.cv p))))))).fv ∪ ((synCin D
            (synCima (synCcnv (synCdif R (synCid)))
              (synCsn (synCuni (synCuni (Class.cv p))))))).fv) :=
  by
  simpa only [nb091AlphaDummy061] using
    freshVar_not_mem
      (((synCin D (synCima (synCcnv (synCdif R (synCid)))
              (synCsn (synCuni (synCuni (Class.cv p))))))).fv ∪ ((synCin D
            (synCima (synCcnv (synCdif R (synCid)))
              (synCsn (synCuni (synCuni (Class.cv p))))))).fv)
      0

theorem nb091_fresh_228 (D : Class) (R : Class) (p : Var) :
    (nb091AlphaDummy062 D R p) ∉
      (((synCin D (synCima (synCcnv (synCdif R (synCid)))
              (synCsn (synCuni (synCuni (Class.cv p))))))).fv ∪ ((synCin D
            (synCima (synCcnv (synCdif R (synCid)))
              (synCsn (synCuni (synCuni (Class.cv p))))))).fv) :=
  by
  simpa only [nb091AlphaDummy062] using
    freshVar_not_mem
      (((synCin D (synCima (synCcnv (synCdif R (synCid)))
              (synCsn (synCuni (synCuni (Class.cv p))))))).fv ∪ ((synCin D
            (synCima (synCcnv (synCdif R (synCid)))
              (synCsn (synCuni (synCuni (Class.cv p))))))).fv)
      1

theorem nb091_distinct_229 (D : Class) (R : Class) (p : Var) :
    (nb091AlphaDummy061 D R p) ≠ (nb091AlphaDummy062 D R p) := by
  simpa only [nb091AlphaDummy061, nb091AlphaDummy062] using
    (freshVar_injective (((synCin D (synCima (synCcnv (synCdif R (synCid)))
              (synCsn (synCuni (synCuni (Class.cv p))))))).fv ∪ ((synCin D
            (synCima (synCcnv (synCdif R (synCid)))
              (synCsn (synCuni (synCuni (Class.cv p))))))).fv) (i := 0) (j := 1) (by decide))

theorem nb091_fresh_230 (D : Class) (R : Class) :
    (nb091AlphaDummy047 D R) ∉
      (((synCin R (synCxp (synCin D (synCima (synCcnv (synCdif R (synCid)))
                  (synCsn (synCuni (synCuni (Class.cv (nb091AlphaDummy000 D R)))))))
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (synCuni
                      (synCuni (Class.cv (nb091AlphaDummy000 D R)))))))))).fv ∪ ((synCin D
            (synCima (synCcnv (synCdif R (synCid))) (synCsn
                (synCuni (synCuni (Class.cv (nb091AlphaDummy000 D R)))))))).fv) :=
  by
  simpa only [nb091AlphaDummy047] using
    freshVar_not_mem
      (((synCin R (synCxp (synCin D (synCima (synCcnv (synCdif R (synCid)))
                  (synCsn (synCuni (synCuni (Class.cv (nb091AlphaDummy000 D R)))))))
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (synCuni
                      (synCuni (Class.cv (nb091AlphaDummy000 D R)))))))))).fv ∪ ((synCin D
            (synCima (synCcnv (synCdif R (synCid))) (synCsn
                (synCuni (synCuni (Class.cv (nb091AlphaDummy000 D R)))))))).fv)
      0

theorem nb091_fresh_231 (D : Class) (R : Class) :
    (nb091AlphaDummy048 D R) ∉
      (((synCin R (synCxp (synCin D (synCima (synCcnv (synCdif R (synCid)))
                  (synCsn (synCuni (synCuni (Class.cv (nb091AlphaDummy000 D R)))))))
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (synCuni
                      (synCuni (Class.cv (nb091AlphaDummy000 D R)))))))))).fv ∪ ((synCin D
            (synCima (synCcnv (synCdif R (synCid))) (synCsn
                (synCuni (synCuni (Class.cv (nb091AlphaDummy000 D R)))))))).fv) :=
  by
  simpa only [nb091AlphaDummy048] using
    freshVar_not_mem
      (((synCin R (synCxp (synCin D (synCima (synCcnv (synCdif R (synCid)))
                  (synCsn (synCuni (synCuni (Class.cv (nb091AlphaDummy000 D R)))))))
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (synCuni
                      (synCuni (Class.cv (nb091AlphaDummy000 D R)))))))))).fv ∪ ((synCin D
            (synCima (synCcnv (synCdif R (synCid))) (synCsn
                (synCuni (synCuni (Class.cv (nb091AlphaDummy000 D R)))))))).fv)
      1

theorem nb091_distinct_232 (D : Class) (R : Class) :
    (nb091AlphaDummy047 D R) ≠ (nb091AlphaDummy048 D R) := by
  simpa only [nb091AlphaDummy047, nb091AlphaDummy048] using
    (freshVar_injective (((synCin R (synCxp (synCin D
                (synCima (synCcnv (synCdif R (synCid)))
                  (synCsn (synCuni (synCuni (Class.cv (nb091AlphaDummy000 D R)))))))
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (synCuni
                      (synCuni (Class.cv (nb091AlphaDummy000 D R)))))))))).fv ∪ ((synCin D
            (synCima (synCcnv (synCdif R (synCid))) (synCsn
                (synCuni (synCuni (Class.cv (nb091AlphaDummy000 D R)))))))).fv)
      (i := 0) (j := 1) (by decide))

theorem nb091_fresh_233 (D : Class) (R : Class) (p : Var) :
    (nb091AlphaDummy049 D R p) ∉
      (((synCin R (synCxp (synCin D (synCima (synCcnv (synCdif R (synCid)))
                  (synCsn (synCuni (synCuni (Class.cv p)))))) (synCin D
                (synCima (synCcnv (synCdif R (synCid)))
                  (synCsn (synCuni (synCuni (Class.cv p))))))))).fv ∪ ((synCin D
            (synCima (synCcnv (synCdif R (synCid)))
              (synCsn (synCuni (synCuni (Class.cv p))))))).fv) :=
  by
  simpa only [nb091AlphaDummy049] using
    freshVar_not_mem
      (((synCin R (synCxp (synCin D (synCima (synCcnv (synCdif R (synCid)))
                  (synCsn (synCuni (synCuni (Class.cv p)))))) (synCin D
                (synCima (synCcnv (synCdif R (synCid)))
                  (synCsn (synCuni (synCuni (Class.cv p))))))))).fv ∪ ((synCin D
            (synCima (synCcnv (synCdif R (synCid)))
              (synCsn (synCuni (synCuni (Class.cv p))))))).fv)
      0

theorem nb091_fresh_234 (D : Class) (R : Class) (p : Var) :
    (nb091AlphaDummy050 D R p) ∉
      (((synCin R (synCxp (synCin D (synCima (synCcnv (synCdif R (synCid)))
                  (synCsn (synCuni (synCuni (Class.cv p)))))) (synCin D
                (synCima (synCcnv (synCdif R (synCid)))
                  (synCsn (synCuni (synCuni (Class.cv p))))))))).fv ∪ ((synCin D
            (synCima (synCcnv (synCdif R (synCid)))
              (synCsn (synCuni (synCuni (Class.cv p))))))).fv) :=
  by
  simpa only [nb091AlphaDummy050] using
    freshVar_not_mem
      (((synCin R (synCxp (synCin D (synCima (synCcnv (synCdif R (synCid)))
                  (synCsn (synCuni (synCuni (Class.cv p)))))) (synCin D
                (synCima (synCcnv (synCdif R (synCid)))
                  (synCsn (synCuni (synCuni (Class.cv p))))))))).fv ∪ ((synCin D
            (synCima (synCcnv (synCdif R (synCid)))
              (synCsn (synCuni (synCuni (Class.cv p))))))).fv)
      1

theorem nb091_distinct_235 (D : Class) (R : Class) (p : Var) :
    (nb091AlphaDummy049 D R p) ≠ (nb091AlphaDummy050 D R p) := by
  simpa only [nb091AlphaDummy049, nb091AlphaDummy050] using
    (freshVar_injective (((synCin R (synCxp (synCin D
                (synCima (synCcnv (synCdif R (synCid)))
                  (synCsn (synCuni (synCuni (Class.cv p)))))) (synCin D
                (synCima (synCcnv (synCdif R (synCid)))
                  (synCsn (synCuni (synCuni (Class.cv p))))))))).fv ∪ ((synCin D
            (synCima (synCcnv (synCdif R (synCid)))
              (synCsn (synCuni (synCuni (Class.cv p))))))).fv) (i := 0) (j := 1) (by decide))

theorem nb091_fresh_236 (D : Class) (R : Class) :
    (nb091AlphaDummy025 D R) ∉
      (((synCnin (Class.cv (nb091AlphaDummy020 D R))
            (Class.cv (nb091AlphaDummy021 D R)))).fv ∪
        ((synCnin (Class.cv (nb091AlphaDummy020 D R))
            (Class.cv (nb091AlphaDummy021 D R)))).fv) :=
  by
  simpa only [nb091AlphaDummy025] using
    freshVar_not_mem
      (((synCnin (Class.cv (nb091AlphaDummy020 D R))
            (Class.cv (nb091AlphaDummy021 D R)))).fv ∪
        ((synCnin (Class.cv (nb091AlphaDummy020 D R))
            (Class.cv (nb091AlphaDummy021 D R)))).fv)
      0

theorem nb091_fresh_237 (D : Class) (R : Class) (p : Var) :
    (nb091AlphaDummy026 D R p) ∉
      (((synCnin (Class.cv (nb091AlphaDummy023 D R p))
            (Class.cv (nb091AlphaDummy024 D R p)))).fv ∪
        ((synCnin (Class.cv (nb091AlphaDummy023 D R p))
            (Class.cv (nb091AlphaDummy024 D R p)))).fv) :=
  by
  simpa only [nb091AlphaDummy026] using
    freshVar_not_mem
      (((synCnin (Class.cv (nb091AlphaDummy023 D R p))
            (Class.cv (nb091AlphaDummy024 D R p)))).fv ∪
        ((synCnin (Class.cv (nb091AlphaDummy023 D R p))
            (Class.cv (nb091AlphaDummy024 D R p)))).fv)
      0

theorem nb091_fresh_238 (D : Class) (R : Class) :
    (nb091AlphaDummy085 D R) ∉
      (((synCnin (Class.cv (nb091AlphaDummy080 D R))
            (Class.cv (nb091AlphaDummy081 D R)))).fv ∪
        ((synCnin (Class.cv (nb091AlphaDummy080 D R))
            (Class.cv (nb091AlphaDummy081 D R)))).fv) :=
  by
  simpa only [nb091AlphaDummy085] using
    freshVar_not_mem
      (((synCnin (Class.cv (nb091AlphaDummy080 D R))
            (Class.cv (nb091AlphaDummy081 D R)))).fv ∪
        ((synCnin (Class.cv (nb091AlphaDummy080 D R))
            (Class.cv (nb091AlphaDummy081 D R)))).fv)
      0

theorem nb091_fresh_239 (D : Class) (R : Class) (p : Var) :
    (nb091AlphaDummy086 D R p) ∉
      (((synCnin (Class.cv (nb091AlphaDummy083 D R p))
            (Class.cv (nb091AlphaDummy084 D R p)))).fv ∪
        ((synCnin (Class.cv (nb091AlphaDummy083 D R p))
            (Class.cv (nb091AlphaDummy084 D R p)))).fv) :=
  by
  simpa only [nb091AlphaDummy086] using
    freshVar_not_mem
      (((synCnin (Class.cv (nb091AlphaDummy083 D R p))
            (Class.cv (nb091AlphaDummy084 D R p)))).fv ∪
        ((synCnin (Class.cv (nb091AlphaDummy083 D R p))
            (Class.cv (nb091AlphaDummy084 D R p)))).fv)
      0

theorem nb091_fresh_240 (D : Class) (R : Class) :
    (nb091AlphaDummy139 D R) ∉
      (((synCnin (Class.cv (nb091AlphaDummy134 D R))
            (Class.cv (nb091AlphaDummy135 D R)))).fv ∪
        ((synCnin (Class.cv (nb091AlphaDummy134 D R))
            (Class.cv (nb091AlphaDummy135 D R)))).fv) :=
  by
  simpa only [nb091AlphaDummy139] using
    freshVar_not_mem
      (((synCnin (Class.cv (nb091AlphaDummy134 D R))
            (Class.cv (nb091AlphaDummy135 D R)))).fv ∪
        ((synCnin (Class.cv (nb091AlphaDummy134 D R))
            (Class.cv (nb091AlphaDummy135 D R)))).fv)
      0

theorem nb091_fresh_241 (R : Class) (p : Var) :
    (nb091AlphaDummy140 R p) ∉
      (((synCnin (Class.cv (nb091AlphaDummy137 R p))
            (Class.cv (nb091AlphaDummy138 R p)))).fv ∪
        ((synCnin (Class.cv (nb091AlphaDummy137 R p))
            (Class.cv (nb091AlphaDummy138 R p)))).fv) :=
  by
  simpa only [nb091AlphaDummy140] using
    freshVar_not_mem
      (((synCnin (Class.cv (nb091AlphaDummy137 R p))
            (Class.cv (nb091AlphaDummy138 R p)))).fv ∪
        ((synCnin (Class.cv (nb091AlphaDummy137 R p))
            (Class.cv (nb091AlphaDummy138 R p)))).fv)
      0

theorem nb091_fresh_242 (D : Class) (R : Class) :
    (nb091AlphaDummy167 D R) ∉
      (((synCnin (Class.cv (nb091AlphaDummy162 D R))
            (Class.cv (nb091AlphaDummy163 D R)))).fv ∪
        ((synCnin (Class.cv (nb091AlphaDummy162 D R))
            (Class.cv (nb091AlphaDummy163 D R)))).fv) :=
  by
  simpa only [nb091AlphaDummy167] using
    freshVar_not_mem
      (((synCnin (Class.cv (nb091AlphaDummy162 D R))
            (Class.cv (nb091AlphaDummy163 D R)))).fv ∪
        ((synCnin (Class.cv (nb091AlphaDummy162 D R))
            (Class.cv (nb091AlphaDummy163 D R)))).fv)
      0

theorem nb091_fresh_243 (D : Class) (R : Class) (p : Var) :
    (nb091AlphaDummy168 D R p) ∉
      (((synCnin (Class.cv (nb091AlphaDummy165 D R p))
            (Class.cv (nb091AlphaDummy166 D R p)))).fv ∪
        ((synCnin (Class.cv (nb091AlphaDummy165 D R p))
            (Class.cv (nb091AlphaDummy166 D R p)))).fv) :=
  by
  simpa only [nb091AlphaDummy168] using
    freshVar_not_mem
      (((synCnin (Class.cv (nb091AlphaDummy165 D R p))
            (Class.cv (nb091AlphaDummy166 D R p)))).fv ∪
        ((synCnin (Class.cv (nb091AlphaDummy165 D R p))
            (Class.cv (nb091AlphaDummy166 D R p)))).fv)
      0

theorem nb091_fresh_244 (D : Class) (R : Class) :
    (nb091AlphaDummy203 D R) ∉
      (((synCnin (Class.cv (nb091AlphaDummy198 D R))
            (Class.cv (nb091AlphaDummy199 D R)))).fv ∪
        ((synCnin (Class.cv (nb091AlphaDummy198 D R))
            (Class.cv (nb091AlphaDummy199 D R)))).fv) :=
  by
  simpa only [nb091AlphaDummy203] using
    freshVar_not_mem
      (((synCnin (Class.cv (nb091AlphaDummy198 D R))
            (Class.cv (nb091AlphaDummy199 D R)))).fv ∪
        ((synCnin (Class.cv (nb091AlphaDummy198 D R))
            (Class.cv (nb091AlphaDummy199 D R)))).fv)
      0

theorem nb091_fresh_245 (D : Class) (R : Class) (p : Var) :
    (nb091AlphaDummy204 D R p) ∉
      (((synCnin (Class.cv (nb091AlphaDummy201 D R p))
            (Class.cv (nb091AlphaDummy202 D R p)))).fv ∪
        ((synCnin (Class.cv (nb091AlphaDummy201 D R p))
            (Class.cv (nb091AlphaDummy202 D R p)))).fv) :=
  by
  simpa only [nb091AlphaDummy204] using
    freshVar_not_mem
      (((synCnin (Class.cv (nb091AlphaDummy201 D R p))
            (Class.cv (nb091AlphaDummy202 D R p)))).fv ∪
        ((synCnin (Class.cv (nb091AlphaDummy201 D R p))
            (Class.cv (nb091AlphaDummy202 D R p)))).fv)
      0

theorem nb091_fresh_246 (D : Class) (R : Class) :
    (nb091AlphaDummy101 D R) ∉
      (((synCnin D (synCima (synCcnv (synCdif R (synCid))) (synCsn
                (synCuni (synCuni (Class.cv (nb091AlphaDummy000 D R)))))))).fv ∪
        ((synCnin D (synCima (synCcnv (synCdif R (synCid))) (synCsn
                (synCuni (synCuni (Class.cv (nb091AlphaDummy000 D R)))))))).fv) :=
  by
  simpa only [nb091AlphaDummy101] using
    freshVar_not_mem
      (((synCnin D (synCima (synCcnv (synCdif R (synCid))) (synCsn
                (synCuni (synCuni (Class.cv (nb091AlphaDummy000 D R)))))))).fv ∪
        ((synCnin D (synCima (synCcnv (synCdif R (synCid))) (synCsn
                (synCuni (synCuni (Class.cv (nb091AlphaDummy000 D R)))))))).fv)
      0

theorem nb091_fresh_247 (D : Class) (R : Class) (p : Var) :
    (nb091AlphaDummy102 D R p) ∉
      (((synCnin D (synCima (synCcnv (synCdif R (synCid)))
              (synCsn (synCuni (synCuni (Class.cv p))))))).fv ∪ ((synCnin D
            (synCima (synCcnv (synCdif R (synCid)))
              (synCsn (synCuni (synCuni (Class.cv p))))))).fv) :=
  by
  simpa only [nb091AlphaDummy102] using
    freshVar_not_mem
      (((synCnin D (synCima (synCcnv (synCdif R (synCid)))
              (synCsn (synCuni (synCuni (Class.cv p))))))).fv ∪ ((synCnin D
            (synCima (synCcnv (synCdif R (synCid)))
              (synCsn (synCuni (synCuni (Class.cv p))))))).fv)
      0

theorem nb091_fresh_248 (D : Class) (R : Class) :
    (nb091AlphaDummy055 D R) ∉
      (((synCnin R (synCxp (synCin D (synCima (synCcnv (synCdif R (synCid)))
                  (synCsn (synCuni (synCuni (Class.cv (nb091AlphaDummy000 D R)))))))
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (synCuni
                      (synCuni (Class.cv (nb091AlphaDummy000 D R)))))))))).fv ∪ ((synCnin R
            (synCxp (synCin D (synCima (synCcnv (synCdif R (synCid)))
                  (synCsn (synCuni (synCuni (Class.cv (nb091AlphaDummy000 D R)))))))
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (synCuni
                      (synCuni (Class.cv (nb091AlphaDummy000 D R)))))))))).fv) :=
  by
  simpa only [nb091AlphaDummy055] using
    freshVar_not_mem
      (((synCnin R (synCxp (synCin D (synCima (synCcnv (synCdif R (synCid)))
                  (synCsn (synCuni (synCuni (Class.cv (nb091AlphaDummy000 D R)))))))
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (synCuni
                      (synCuni (Class.cv (nb091AlphaDummy000 D R)))))))))).fv ∪ ((synCnin R
            (synCxp (synCin D (synCima (synCcnv (synCdif R (synCid)))
                  (synCsn (synCuni (synCuni (Class.cv (nb091AlphaDummy000 D R)))))))
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn
                    (synCuni (synCuni (Class.cv (nb091AlphaDummy000 D R)))))))))).fv)
      0

theorem nb091_fresh_249 (D : Class) (R : Class) (p : Var) :
    (nb091AlphaDummy056 D R p) ∉
      (((synCnin R (synCxp (synCin D (synCima (synCcnv (synCdif R (synCid)))
                  (synCsn (synCuni (synCuni (Class.cv p)))))) (synCin D
                (synCima (synCcnv (synCdif R (synCid)))
                  (synCsn (synCuni (synCuni (Class.cv p))))))))).fv ∪ ((synCnin R (synCxp
              (synCin D (synCima (synCcnv (synCdif R (synCid)))
                  (synCsn (synCuni (synCuni (Class.cv p)))))) (synCin D
                (synCima (synCcnv (synCdif R (synCid)))
                  (synCsn (synCuni (synCuni (Class.cv p))))))))).fv) :=
  by
  simpa only [nb091AlphaDummy056] using
    freshVar_not_mem
      (((synCnin R (synCxp (synCin D (synCima (synCcnv (synCdif R (synCid)))
                  (synCsn (synCuni (synCuni (Class.cv p)))))) (synCin D
                (synCima (synCcnv (synCdif R (synCid)))
                  (synCsn (synCuni (synCuni (Class.cv p))))))))).fv ∪ ((synCnin R (synCxp
              (synCin D (synCima (synCcnv (synCdif R (synCid)))
                  (synCsn (synCuni (synCuni (Class.cv p)))))) (synCin D
                (synCima (synCcnv (synCdif R (synCid)))
                  (synCsn (synCuni (synCuni (Class.cv p))))))))).fv)
      0

theorem nb091_fresh_250 (D : Class) (R : Class) :
    (nb091AlphaDummy039 D R) ∉
      (((synCphi (Class.cv (nb091AlphaDummy006 D R)))).fv ∪
        ((synCphi (Class.cv (nb091AlphaDummy006 D R)))).fv) :=
  by
  simpa only [nb091AlphaDummy039] using
    freshVar_not_mem
      (((synCphi (Class.cv (nb091AlphaDummy006 D R)))).fv ∪
        ((synCphi (Class.cv (nb091AlphaDummy006 D R)))).fv)
      0

theorem nb091_fresh_251 (D : Class) (R : Class) (p : Var) :
    (nb091AlphaDummy040 D R p) ∉
      (((synCphi (Class.cv (nb091AlphaDummy008 D R p)))).fv ∪
        ((synCphi (Class.cv (nb091AlphaDummy008 D R p)))).fv) :=
  by
  simpa only [nb091AlphaDummy040] using
    freshVar_not_mem
      (((synCphi (Class.cv (nb091AlphaDummy008 D R p)))).fv ∪
        ((synCphi (Class.cv (nb091AlphaDummy008 D R p)))).fv)
      0

theorem nb091_fresh_252 (D : Class) (R : Class) :
    (nb091AlphaDummy181 D R) ∉
      (((synCphi (Class.cv (nb091AlphaDummy048 D R)))).fv ∪
        ((synCphi (Class.cv (nb091AlphaDummy048 D R)))).fv) :=
  by
  simpa only [nb091AlphaDummy181] using
    freshVar_not_mem
      (((synCphi (Class.cv (nb091AlphaDummy048 D R)))).fv ∪
        ((synCphi (Class.cv (nb091AlphaDummy048 D R)))).fv)
      0

theorem nb091_fresh_253 (D : Class) (R : Class) (p : Var) :
    (nb091AlphaDummy182 D R p) ∉
      (((synCphi (Class.cv (nb091AlphaDummy050 D R p)))).fv ∪
        ((synCphi (Class.cv (nb091AlphaDummy050 D R p)))).fv) :=
  by
  simpa only [nb091AlphaDummy182] using
    freshVar_not_mem
      (((synCphi (Class.cv (nb091AlphaDummy050 D R p)))).fv ∪
        ((synCphi (Class.cv (nb091AlphaDummy050 D R p)))).fv)
      0

theorem nb091_fresh_254 (D : Class) (R : Class) :
    (nb091AlphaDummy099 D R) ∉
      (((synCphi (Class.cv (nb091AlphaDummy066 D R)))).fv ∪
        ((synCphi (Class.cv (nb091AlphaDummy066 D R)))).fv) :=
  by
  simpa only [nb091AlphaDummy099] using
    freshVar_not_mem
      (((synCphi (Class.cv (nb091AlphaDummy066 D R)))).fv ∪
        ((synCphi (Class.cv (nb091AlphaDummy066 D R)))).fv)
      0

theorem nb091_fresh_255 (D : Class) (R : Class) (p : Var) :
    (nb091AlphaDummy100 D R p) ∉
      (((synCphi (Class.cv (nb091AlphaDummy068 D R p)))).fv ∪
        ((synCphi (Class.cv (nb091AlphaDummy068 D R p)))).fv) :=
  by
  simpa only [nb091AlphaDummy100] using
    freshVar_not_mem
      (((synCphi (Class.cv (nb091AlphaDummy068 D R p)))).fv ∪
        ((synCphi (Class.cv (nb091AlphaDummy068 D R p)))).fv)
      0

theorem nb091_fresh_256 (D : Class) (R : Class) :
    (nb091AlphaDummy153 D R) ∉
      (((synCphi (Class.cv (nb091AlphaDummy120 D R)))).fv ∪
        ((synCphi (Class.cv (nb091AlphaDummy120 D R)))).fv) :=
  by
  simpa only [nb091AlphaDummy153] using
    freshVar_not_mem
      (((synCphi (Class.cv (nb091AlphaDummy120 D R)))).fv ∪
        ((synCphi (Class.cv (nb091AlphaDummy120 D R)))).fv)
      0

theorem nb091_fresh_257 (R : Class) (p : Var) :
    (nb091AlphaDummy154 R p) ∉
      (((synCphi (Class.cv (nb091AlphaDummy122 R p)))).fv ∪
        ((synCphi (Class.cv (nb091AlphaDummy122 R p)))).fv) :=
  by
  simpa only [nb091AlphaDummy154] using
    freshVar_not_mem
      (((synCphi (Class.cv (nb091AlphaDummy122 R p)))).fv ∪
        ((synCphi (Class.cv (nb091AlphaDummy122 R p)))).fv)
      0

theorem nb091_fresh_258 (D : Class) (R : Class) :
    (nb091AlphaDummy217 D R) ∉
      (((synCphi (Class.cv (nb091AlphaDummy184 D R)))).fv ∪
        ((synCphi (Class.cv (nb091AlphaDummy184 D R)))).fv) :=
  by
  simpa only [nb091AlphaDummy217] using
    freshVar_not_mem
      (((synCphi (Class.cv (nb091AlphaDummy184 D R)))).fv ∪
        ((synCphi (Class.cv (nb091AlphaDummy184 D R)))).fv)
      0

theorem nb091_fresh_259 (D : Class) (R : Class) (p : Var) :
    (nb091AlphaDummy218 D R p) ∉
      (((synCphi (Class.cv (nb091AlphaDummy186 D R p)))).fv ∪
        ((synCphi (Class.cv (nb091AlphaDummy186 D R p)))).fv) :=
  by
  simpa only [nb091AlphaDummy218] using
    freshVar_not_mem
      (((synCphi (Class.cv (nb091AlphaDummy186 D R p)))).fv ∪
        ((synCphi (Class.cv (nb091AlphaDummy186 D R p)))).fv)
      0

theorem nb091_fresh_260 (D : Class) (R : Class) :
    (nb091AlphaDummy111 D R) ∉
      (((synCuni (Class.cv (nb091AlphaDummy000 D R)))).fv) :=
  by
  simpa only [nb091AlphaDummy111] using
    freshVar_not_mem (((synCuni (Class.cv (nb091AlphaDummy000 D R)))).fv) 0

theorem nb091_fresh_261 (D : Class) (R : Class) :
    (nb091AlphaDummy112 D R) ∉
      (((synCuni (Class.cv (nb091AlphaDummy000 D R)))).fv) :=
  by
  simpa only [nb091AlphaDummy112] using
    freshVar_not_mem (((synCuni (Class.cv (nb091AlphaDummy000 D R)))).fv) 1

theorem nb091_distinct_262 (D : Class) (R : Class) :
    (nb091AlphaDummy111 D R) ≠ (nb091AlphaDummy112 D R) := by
  simpa only [nb091AlphaDummy111, nb091AlphaDummy112] using
    (freshVar_injective (((synCuni (Class.cv (nb091AlphaDummy000 D R)))).fv) (i := 0)
      (j := 1) (by decide))

theorem nb091_fresh_263 (p : Var) :
    (nb091AlphaDummy113 p) ∉ (((synCuni (Class.cv p))).fv) := by
  simpa only [nb091AlphaDummy113] using
    freshVar_not_mem (((synCuni (Class.cv p))).fv) 0

theorem nb091_fresh_264 (p : Var) :
    (nb091AlphaDummy114 p) ∉ (((synCuni (Class.cv p))).fv) := by
  simpa only [nb091AlphaDummy114] using
    freshVar_not_mem (((synCuni (Class.cv p))).fv) 1

theorem nb091_distinct_265 (p : Var) :
    (nb091AlphaDummy113 p) ≠ (nb091AlphaDummy114 p) := by
  simpa only [nb091AlphaDummy113, nb091AlphaDummy114] using
    (freshVar_injective (((synCuni (Class.cv p))).fv) (i := 0) (j := 1) (by decide))

theorem nb091_fresh_266 (D : Class) (R : Class) :
    (nb091AlphaDummy109 D R) ∉
      (((synCuni (synCuni (Class.cv (nb091AlphaDummy000 D R))))).fv) :=
  by
  simpa only [nb091AlphaDummy109] using
    freshVar_not_mem (((synCuni (synCuni (Class.cv (nb091AlphaDummy000 D R))))).fv) 0

theorem nb091_fresh_267 (p : Var) :
    (nb091AlphaDummy110 p) ∉ (((synCuni (synCuni (Class.cv p)))).fv) := by
  simpa only [nb091AlphaDummy110] using
    freshVar_not_mem (((synCuni (synCuni (Class.cv p)))).fv) 0

theorem nb091_fresh_268 (D : Class) (R : Class) :
    (nb091AlphaDummy103 D R) ∉
      ((D).fv ∪ ((synCima (synCcnv (synCdif R (synCid))) (synCsn
              (synCuni (synCuni (Class.cv (nb091AlphaDummy000 D R))))))).fv) :=
  by
  simpa only [nb091AlphaDummy103] using
    freshVar_not_mem
      ((D).fv ∪ ((synCima (synCcnv (synCdif R (synCid)))
            (synCsn (synCuni (synCuni (Class.cv (nb091AlphaDummy000 D R))))))).fv)
      0

theorem nb091_fresh_269 (D : Class) (R : Class) (p : Var) :
    (nb091AlphaDummy104 D R p) ∉
      ((D).fv ∪ ((synCima (synCcnv (synCdif R (synCid)))
            (synCsn (synCuni (synCuni (Class.cv p)))))).fv) :=
  by
  simpa only [nb091AlphaDummy104] using
    freshVar_not_mem
      ((D).fv ∪ ((synCima (synCcnv (synCdif R (synCid)))
            (synCsn (synCuni (synCuni (Class.cv p)))))).fv)
      0

theorem nb091_fresh_270 (D : Class) (R : Class) :
    (nb091AlphaDummy057 D R) ∉
      ((R).fv ∪ ((synCxp (synCin D (synCima (synCcnv (synCdif R (synCid)))
                (synCsn (synCuni (synCuni (Class.cv (nb091AlphaDummy000 D R)))))))
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn
                  (synCuni (synCuni (Class.cv (nb091AlphaDummy000 D R))))))))).fv) :=
  by
  simpa only [nb091AlphaDummy057] using
    freshVar_not_mem
      ((R).fv ∪ ((synCxp (synCin D (synCima (synCcnv (synCdif R (synCid)))
                (synCsn (synCuni (synCuni (Class.cv (nb091AlphaDummy000 D R)))))))
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn
                  (synCuni (synCuni (Class.cv (nb091AlphaDummy000 D R))))))))).fv)
      0

theorem nb091_fresh_271 (D : Class) (R : Class) (p : Var) :
    (nb091AlphaDummy058 D R p) ∉
      ((R).fv ∪ ((synCxp (synCin D (synCima (synCcnv (synCdif R (synCid)))
                (synCsn (synCuni (synCuni (Class.cv p)))))) (synCin D
              (synCima (synCcnv (synCdif R (synCid)))
                (synCsn (synCuni (synCuni (Class.cv p)))))))).fv) :=
  by
  simpa only [nb091AlphaDummy058] using
    freshVar_not_mem
      ((R).fv ∪ ((synCxp (synCin D (synCima (synCcnv (synCdif R (synCid)))
                (synCsn (synCuni (synCuni (Class.cv p)))))) (synCin D
              (synCima (synCcnv (synCdif R (synCid)))
                (synCsn (synCuni (synCuni (Class.cv p)))))))).fv)
      0

theorem nb091_fresh_272 (D : Class) (R : Class) :
    (nb091AlphaDummy000 D R) ∉ ((R).fv ∪ (D).fv) := by
  simpa only [nb091AlphaDummy000] using freshVar_not_mem ((R).fv ∪ (D).fv) 0

theorem nb091_fresh_273 (D : Class) (R : Class) :
    (nb091AlphaDummy001 D R) ∉
      (({(nb091AlphaDummy000 D R)} : Finset Var) ∪ ((synCpw1 (synCpw1 D))).fv ∪ ((synCec
            (synChnwcutcode R D (synCuni (synCuni (Class.cv (nb091AlphaDummy000 D R)))))
            (synChwniso D))).fv) :=
  by
  simpa only [nb091AlphaDummy001] using
    freshVar_not_mem
      (({(nb091AlphaDummy000 D R)} : Finset Var) ∪ ((synCpw1 (synCpw1 D))).fv ∪ ((synCec
            (synChnwcutcode R D (synCuni (synCuni (Class.cv (nb091AlphaDummy000 D R)))))
            (synChwniso D))).fv)
      0

theorem nb091_fresh_274 (D : Class) (R : Class) :
    (nb091AlphaDummy003 D R) ∉
      (({(nb091AlphaDummy000 D R)} : Finset Var) ∪
          ({(nb091AlphaDummy001 D R)} : Finset Var) ∪ ((synWa
            (Wff.classMem (Class.cv (nb091AlphaDummy000 D R)) (synCpw1 (synCpw1 D)))
            (Wff.classEq (Class.cv (nb091AlphaDummy001 D R)) (synCec (synChnwcutcode R D
                  (synCuni (synCuni (Class.cv (nb091AlphaDummy000 D R)))))
                (synChwniso D))))).fv) :=
  by
  simpa only [nb091AlphaDummy003] using
    freshVar_not_mem
      (({(nb091AlphaDummy000 D R)} : Finset Var) ∪
          ({(nb091AlphaDummy001 D R)} : Finset Var) ∪ ((synWa
            (Wff.classMem (Class.cv (nb091AlphaDummy000 D R)) (synCpw1 (synCpw1 D)))
            (Wff.classEq (Class.cv (nb091AlphaDummy001 D R)) (synCec (synChnwcutcode R D
                  (synCuni (synCuni (Class.cv (nb091AlphaDummy000 D R)))))
                (synChwniso D))))).fv)
      0

theorem nb091_fresh_275 (D : Class) (R : Class) :
    (nb091AlphaDummy063 D R) ∉
      (({(nb091AlphaDummy059 D R)} : Finset Var) ∪
          ({(nb091AlphaDummy060 D R)} : Finset Var) ∪ ((synWa
            (Wff.classMem (Class.cv (nb091AlphaDummy059 D R)) (synCin D
                (synCima (synCcnv (synCdif R (synCid))) (synCsn
                    (synCuni (synCuni (Class.cv (nb091AlphaDummy000 D R))))))))
            (Wff.classMem (Class.cv (nb091AlphaDummy060 D R)) (synCin D
                (synCima (synCcnv (synCdif R (synCid))) (synCsn (synCuni
                      (synCuni (Class.cv (nb091AlphaDummy000 D R)))))))))).fv) :=
  by
  simpa only [nb091AlphaDummy063] using
    freshVar_not_mem
      (({(nb091AlphaDummy059 D R)} : Finset Var) ∪
          ({(nb091AlphaDummy060 D R)} : Finset Var) ∪ ((synWa
            (Wff.classMem (Class.cv (nb091AlphaDummy059 D R)) (synCin D
                (synCima (synCcnv (synCdif R (synCid))) (synCsn
                    (synCuni (synCuni (Class.cv (nb091AlphaDummy000 D R))))))))
            (Wff.classMem (Class.cv (nb091AlphaDummy060 D R)) (synCin D
                (synCima (synCcnv (synCdif R (synCid))) (synCsn
                    (synCuni (synCuni (Class.cv (nb091AlphaDummy000 D R)))))))))).fv)
      0

theorem nb091_fresh_276 (D : Class) (R : Class) (p : Var) :
    (nb091AlphaDummy064 D R p) ∉
      (({(nb091AlphaDummy061 D R p)} : Finset Var) ∪
          ({(nb091AlphaDummy062 D R p)} : Finset Var) ∪ ((synWa
            (Wff.classMem (Class.cv (nb091AlphaDummy061 D R p)) (synCin D
                (synCima (synCcnv (synCdif R (synCid)))
                  (synCsn (synCuni (synCuni (Class.cv p)))))))
            (Wff.classMem (Class.cv (nb091AlphaDummy062 D R p)) (synCin D
                (synCima (synCcnv (synCdif R (synCid)))
                  (synCsn (synCuni (synCuni (Class.cv p))))))))).fv) :=
  by
  simpa only [nb091AlphaDummy064] using
    freshVar_not_mem
      (({(nb091AlphaDummy061 D R p)} : Finset Var) ∪
          ({(nb091AlphaDummy062 D R p)} : Finset Var) ∪ ((synWa
            (Wff.classMem (Class.cv (nb091AlphaDummy061 D R p)) (synCin D
                (synCima (synCcnv (synCdif R (synCid)))
                  (synCsn (synCuni (synCuni (Class.cv p)))))))
            (Wff.classMem (Class.cv (nb091AlphaDummy062 D R p)) (synCin D
                (synCima (synCcnv (synCdif R (synCid)))
                  (synCsn (synCuni (synCuni (Class.cv p))))))))).fv)
      0

theorem nb091_fresh_277 (D : Class) (R : Class) (p : Var) :
    (nb091AlphaDummy002 D R p) ∉
      (({ p } : Finset Var) ∪ ((synCpw1 (synCpw1 D))).fv ∪
        ((synCec (synChnwcutcode R D (synCuni (synCuni (Class.cv p))))
            (synChwniso D))).fv) :=
  by
  simpa only [nb091AlphaDummy002] using
    freshVar_not_mem
      (({ p } : Finset Var) ∪ ((synCpw1 (synCpw1 D))).fv ∪
        ((synCec (synChnwcutcode R D (synCuni (synCuni (Class.cv p)))) (synChwniso D))).fv)
      0

theorem nb091_fresh_278 (D : Class) (R : Class) (p : Var) :
    (nb091AlphaDummy004 D R p) ∉
      (({ p } : Finset Var) ∪ ({(nb091AlphaDummy002 D R p)} : Finset Var) ∪
        ((synWa (Wff.classMem (Class.cv p) (synCpw1 (synCpw1 D)))
            (Wff.classEq (Class.cv (nb091AlphaDummy002 D R p))
              (synCec (synChnwcutcode R D (synCuni (synCuni (Class.cv p))))
                (synChwniso D))))).fv) :=
  by
  simpa only [nb091AlphaDummy004] using
    freshVar_not_mem
      (({ p } : Finset Var) ∪ ({(nb091AlphaDummy002 D R p)} : Finset Var) ∪
        ((synWa (Wff.classMem (Class.cv p) (synCpw1 (synCpw1 D)))
            (Wff.classEq (Class.cv (nb091AlphaDummy002 D R p))
              (synCec (synChnwcutcode R D (synCuni (synCuni (Class.cv p))))
                (synChwniso D))))).fv)
      0

theorem nb091_support_mem_0000 (D : Class) (R : Class) :
    (nb091AlphaDummy000 D R) ∈
      (({(nb091AlphaDummy000 D R)} : Finset Var) ∪
          ({(nb091AlphaDummy001 D R)} : Finset Var) ∪ ((synWa
            (Wff.classMem (Class.cv (nb091AlphaDummy000 D R)) (synCpw1 (synCpw1 D)))
            (Wff.classEq (Class.cv (nb091AlphaDummy001 D R)) (synCec (synChnwcutcode R D
                  (synCuni (synCuni (Class.cv (nb091AlphaDummy000 D R)))))
                (synChwniso D))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  with_reducible rw [Finset.mem_union]
  left
  exact Finset.mem_singleton_self _

theorem nb091_support_mem_0001 (D : Class) (R : Class) (p : Var) :
    p ∈
      (({ p } : Finset Var) ∪ ({(nb091AlphaDummy002 D R p)} : Finset Var) ∪
        ((synWa (Wff.classMem (Class.cv p) (synCpw1 (synCpw1 D)))
            (Wff.classEq (Class.cv (nb091AlphaDummy002 D R p))
              (synCec (synChnwcutcode R D (synCuni (synCuni (Class.cv p))))
                (synChwniso D))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  with_reducible rw [Finset.mem_union]
  left
  exact Finset.mem_singleton_self _

theorem nb091_support_mem_0002 (D : Class) (R : Class) :
    (nb091AlphaDummy001 D R) ∈
      (({(nb091AlphaDummy000 D R)} : Finset Var) ∪
          ({(nb091AlphaDummy001 D R)} : Finset Var) ∪ ((synWa
            (Wff.classMem (Class.cv (nb091AlphaDummy000 D R)) (synCpw1 (synCpw1 D)))
            (Wff.classEq (Class.cv (nb091AlphaDummy001 D R)) (synCec (synChnwcutcode R D
                  (synCuni (synCuni (Class.cv (nb091AlphaDummy000 D R)))))
                (synChwniso D))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  with_reducible rw [Finset.mem_union]
  right
  exact Finset.mem_singleton_self _

theorem nb091_support_mem_0003 (D : Class) (R : Class) (p : Var) :
    (nb091AlphaDummy002 D R p) ∈
      (({ p } : Finset Var) ∪ ({(nb091AlphaDummy002 D R p)} : Finset Var) ∪
        ((synWa (Wff.classMem (Class.cv p) (synCpw1 (synCpw1 D)))
            (Wff.classEq (Class.cv (nb091AlphaDummy002 D R p))
              (synCec (synChnwcutcode R D (synCuni (synCuni (Class.cv p))))
                (synChwniso D))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  with_reducible rw [Finset.mem_union]
  right
  exact Finset.mem_singleton_self _

theorem nb091_support_mem_0004 (D : Class) (R : Class) :
    (nb091AlphaDummy000 D R) ∈
      (({(nb091AlphaDummy000 D R)} : Finset Var) ∪ ((synCpw1 (synCpw1 D))).fv ∪ ((synCec
            (synChnwcutcode R D (synCuni (synCuni (Class.cv (nb091AlphaDummy000 D R)))))
            (synChwniso D))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  with_reducible rw [Finset.mem_union]
  left
  exact Finset.mem_singleton_self _

theorem nb091_support_mem_0005 (D : Class) (R : Class) (p : Var) :
    p ∈
      (({ p } : Finset Var) ∪ ((synCpw1 (synCpw1 D))).fv ∪
        ((synCec (synChnwcutcode R D (synCuni (synCuni (Class.cv p))))
            (synChwniso D))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  with_reducible rw [Finset.mem_union]
  left
  exact Finset.mem_singleton_self _

theorem nb091_support_mem_0006 (D : Class) (R : Class) :
    (nb091AlphaDummy000 D R) ∈
      (((Class.cv (nb091AlphaDummy000 D R))).fv ∪
        ((Class.cv (nb091AlphaDummy001 D R))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb091_support_mem_0007 (D : Class) (R : Class) :
    (nb091AlphaDummy000 D R) ∈
      (((synCcompl (Class.cab (nb091AlphaDummy005 D R)
              (synWrex (nb091AlphaDummy006 D R) (Class.cv (nb091AlphaDummy000 D R))
                (Wff.classEq (Class.cv (nb091AlphaDummy005 D R))
                  (synCphi (Class.cv (nb091AlphaDummy006 D R)))))))).fv ∪ ((synCcompl
            (Class.cab (nb091AlphaDummy005 D R)
              (synWrex (nb091AlphaDummy006 D R) (Class.cv (nb091AlphaDummy001 D R))
                (Wff.classEq (Class.cv (nb091AlphaDummy005 D R))
                  (synCun (synCphi (Class.cv (nb091AlphaDummy006 D R)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb091AlphaDummy000 D R) ≠ (nb091AlphaDummy005 D R) from (by
          unfold nb091AlphaDummy005;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb091_support_mem_0006 D R) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb091AlphaDummy000 D R) ≠ (nb091AlphaDummy006 D R) from (by
            unfold nb091AlphaDummy006;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb091_support_mem_0006 D R) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb091_support_mem_0008 (D : Class) (R : Class) (p : Var) :
    p ∈ (((Class.cv p)).fv ∪ ((Class.cv (nb091AlphaDummy002 D R p))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb091_support_mem_0009 (D : Class) (R : Class) (p : Var) :
    p ∈
      (((synCcompl (Class.cab (nb091AlphaDummy007 D R p)
              (synWrex (nb091AlphaDummy008 D R p) (Class.cv p)
                (Wff.classEq (Class.cv (nb091AlphaDummy007 D R p))
                  (synCphi (Class.cv (nb091AlphaDummy008 D R p)))))))).fv ∪ ((synCcompl
            (Class.cab (nb091AlphaDummy007 D R p) (synWrex (nb091AlphaDummy008 D R p)
                (Class.cv (nb091AlphaDummy002 D R p))
                (Wff.classEq (Class.cv (nb091AlphaDummy007 D R p))
                  (synCun (synCphi (Class.cv (nb091AlphaDummy008 D R p)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show p ≠ (nb091AlphaDummy007 D R p) from (by
          unfold nb091AlphaDummy007;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb091_support_mem_0008 D R p) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show p ≠ (nb091AlphaDummy008 D R p) from (by
            unfold nb091AlphaDummy008;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb091_support_mem_0008 D R p) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb091_support_mem_0010 (D : Class) (R : Class) :
    (nb091AlphaDummy000 D R) ∈
      (((Class.cab (nb091AlphaDummy005 D R)
            (synWrex (nb091AlphaDummy006 D R) (Class.cv (nb091AlphaDummy000 D R))
              (Wff.classEq (Class.cv (nb091AlphaDummy005 D R))
                (synCphi (Class.cv (nb091AlphaDummy006 D R))))))).fv ∪
        ((Class.cab (nb091AlphaDummy005 D R)
            (synWrex (nb091AlphaDummy006 D R) (Class.cv (nb091AlphaDummy000 D R))
              (Wff.classEq (Class.cv (nb091AlphaDummy005 D R))
                (synCphi (Class.cv (nb091AlphaDummy006 D R))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb091AlphaDummy000 D R) ≠ (nb091AlphaDummy005 D R) from (by
          unfold nb091AlphaDummy005;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb091_support_mem_0006 D R) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb091AlphaDummy000 D R) ≠ (nb091AlphaDummy006 D R) from (by
            unfold nb091AlphaDummy006;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb091_support_mem_0006 D R) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb091_support_mem_0011 (D : Class) (R : Class) (p : Var) :
    p ∈
      (((Class.cab (nb091AlphaDummy007 D R p)
            (synWrex (nb091AlphaDummy008 D R p) (Class.cv p)
              (Wff.classEq (Class.cv (nb091AlphaDummy007 D R p))
                (synCphi (Class.cv (nb091AlphaDummy008 D R p))))))).fv ∪
        ((Class.cab (nb091AlphaDummy007 D R p)
            (synWrex (nb091AlphaDummy008 D R p) (Class.cv p)
              (Wff.classEq (Class.cv (nb091AlphaDummy007 D R p))
                (synCphi (Class.cv (nb091AlphaDummy008 D R p))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show p ≠ (nb091AlphaDummy007 D R p) from (by
          unfold nb091AlphaDummy007;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb091_support_mem_0008 D R p) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show p ≠ (nb091AlphaDummy008 D R p) from (by
            unfold nb091AlphaDummy008;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb091_support_mem_0008 D R p) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb091_support_mem_0012 (D : Class) (R : Class) :
    (nb091AlphaDummy006 D R) ∈ (((Class.cv (nb091AlphaDummy006 D R))).fv) :=
  by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb091_support_mem_0013 (D : Class) (R : Class) (p : Var) :
    (nb091AlphaDummy008 D R p) ∈ (((Class.cv (nb091AlphaDummy008 D R p))).fv) :=
  by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb091_support_mem_0014 (D : Class) (R : Class) :
    (nb091AlphaDummy013 D R) ∈
      (((Wff.classMem (Class.cv (nb091AlphaDummy013 D R)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb091AlphaDummy013 D R)) (synC1c))).fv ∪
        ((Class.cv (nb091AlphaDummy013 D R))).fv) :=
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
    (nb091AlphaDummy015 D R p) ∈
      (((Wff.classMem (Class.cv (nb091AlphaDummy015 D R p)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb091AlphaDummy015 D R p)) (synC1c))).fv ∪
        ((Class.cv (nb091AlphaDummy015 D R p))).fv) :=
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
    (nb091AlphaDummy013 D R) ∈
      (((Class.cv (nb091AlphaDummy013 D R))).fv ∪ ((synC1c)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb091_support_mem_0017 (D : Class) (R : Class) (p : Var) :
    (nb091AlphaDummy015 D R p) ∈
      (((Class.cv (nb091AlphaDummy015 D R p))).fv ∪ ((synC1c)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb091_support_mem_0018 (D : Class) (R : Class) :
    (nb091AlphaDummy020 D R) ∈
      (((synCnin (Class.cv (nb091AlphaDummy020 D R))
            (Class.cv (nb091AlphaDummy021 D R)))).fv ∪
        ((synCnin (Class.cv (nb091AlphaDummy020 D R))
            (Class.cv (nb091AlphaDummy021 D R)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb091_support_mem_0019 (D : Class) (R : Class) (p : Var) :
    (nb091AlphaDummy023 D R p) ∈
      (((synCnin (Class.cv (nb091AlphaDummy023 D R p))
            (Class.cv (nb091AlphaDummy024 D R p)))).fv ∪
        ((synCnin (Class.cv (nb091AlphaDummy023 D R p))
            (Class.cv (nb091AlphaDummy024 D R p)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb091_support_mem_0020 (D : Class) (R : Class) :
    (nb091AlphaDummy020 D R) ∈
      (((Class.cv (nb091AlphaDummy020 D R))).fv ∪
        ((Class.cv (nb091AlphaDummy021 D R))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb091_support_mem_0021 (D : Class) (R : Class) (p : Var) :
    (nb091AlphaDummy023 D R p) ∈
      (((Class.cv (nb091AlphaDummy023 D R p))).fv ∪
        ((Class.cv (nb091AlphaDummy024 D R p))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb091_support_mem_0022 (D : Class) (R : Class) :
    (nb091AlphaDummy021 D R) ∈
      (((synCnin (Class.cv (nb091AlphaDummy020 D R))
            (Class.cv (nb091AlphaDummy021 D R)))).fv ∪
        ((synCnin (Class.cv (nb091AlphaDummy020 D R))
            (Class.cv (nb091AlphaDummy021 D R)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb091_support_mem_0023 (D : Class) (R : Class) (p : Var) :
    (nb091AlphaDummy024 D R p) ∈
      (((synCnin (Class.cv (nb091AlphaDummy023 D R p))
            (Class.cv (nb091AlphaDummy024 D R p)))).fv ∪
        ((synCnin (Class.cv (nb091AlphaDummy023 D R p))
            (Class.cv (nb091AlphaDummy024 D R p)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb091_support_mem_0024 (D : Class) (R : Class) :
    (nb091AlphaDummy021 D R) ∈
      (((Class.cv (nb091AlphaDummy020 D R))).fv ∪
        ((Class.cv (nb091AlphaDummy021 D R))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb091_support_mem_0025 (D : Class) (R : Class) (p : Var) :
    (nb091AlphaDummy024 D R p) ∈
      (((Class.cv (nb091AlphaDummy023 D R p))).fv ∪
        ((Class.cv (nb091AlphaDummy024 D R p))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb091_support_mem_0026 (D : Class) (R : Class) :
    (nb091AlphaDummy020 D R) ∈
      (((synCcompl (Class.cv (nb091AlphaDummy020 D R)))).fv ∪
        ((synCcompl (Class.cv (nb091AlphaDummy021 D R)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb091_support_mem_0027 (D : Class) (R : Class) (p : Var) :
    (nb091AlphaDummy023 D R p) ∈
      (((synCcompl (Class.cv (nb091AlphaDummy023 D R p)))).fv ∪
        ((synCcompl (Class.cv (nb091AlphaDummy024 D R p)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb091_support_mem_0028 (D : Class) (R : Class) :
    (nb091AlphaDummy020 D R) ∈
      (((Class.cv (nb091AlphaDummy020 D R))).fv ∪
        ((Class.cv (nb091AlphaDummy020 D R))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb091_support_mem_0029 (D : Class) (R : Class) (p : Var) :
    (nb091AlphaDummy023 D R p) ∈
      (((Class.cv (nb091AlphaDummy023 D R p))).fv ∪
        ((Class.cv (nb091AlphaDummy023 D R p))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb091_support_mem_0030 (D : Class) (R : Class) :
    (nb091AlphaDummy021 D R) ∈
      (((synCcompl (Class.cv (nb091AlphaDummy020 D R)))).fv ∪
        ((synCcompl (Class.cv (nb091AlphaDummy021 D R)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb091_support_mem_0031 (D : Class) (R : Class) (p : Var) :
    (nb091AlphaDummy024 D R p) ∈
      (((synCcompl (Class.cv (nb091AlphaDummy023 D R p)))).fv ∪
        ((synCcompl (Class.cv (nb091AlphaDummy024 D R p)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb091_support_mem_0032 (D : Class) (R : Class) :
    (nb091AlphaDummy021 D R) ∈
      (((Class.cv (nb091AlphaDummy021 D R))).fv ∪
        ((Class.cv (nb091AlphaDummy021 D R))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb091_support_mem_0033 (D : Class) (R : Class) (p : Var) :
    (nb091AlphaDummy024 D R p) ∈
      (((Class.cv (nb091AlphaDummy024 D R p))).fv ∪
        ((Class.cv (nb091AlphaDummy024 D R p))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb091_support_mem_0034 (D : Class) (R : Class) :
    (nb091AlphaDummy001 D R) ∈
      (((Class.cv (nb091AlphaDummy000 D R))).fv ∪
        ((Class.cv (nb091AlphaDummy001 D R))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb091_support_mem_0035 (D : Class) (R : Class) :
    (nb091AlphaDummy001 D R) ∈
      (((synCcompl (Class.cab (nb091AlphaDummy005 D R)
              (synWrex (nb091AlphaDummy006 D R) (Class.cv (nb091AlphaDummy000 D R))
                (Wff.classEq (Class.cv (nb091AlphaDummy005 D R))
                  (synCphi (Class.cv (nb091AlphaDummy006 D R)))))))).fv ∪ ((synCcompl
            (Class.cab (nb091AlphaDummy005 D R)
              (synWrex (nb091AlphaDummy006 D R) (Class.cv (nb091AlphaDummy001 D R))
                (Wff.classEq (Class.cv (nb091AlphaDummy005 D R))
                  (synCun (synCphi (Class.cv (nb091AlphaDummy006 D R)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb091AlphaDummy001 D R) ≠ (nb091AlphaDummy005 D R) from (by
          unfold nb091AlphaDummy005;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb091_support_mem_0034 D R) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb091AlphaDummy001 D R) ≠ (nb091AlphaDummy006 D R) from (by
            unfold nb091AlphaDummy006;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb091_support_mem_0034 D R) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb091_support_mem_0036 (D : Class) (R : Class) (p : Var) :
    (nb091AlphaDummy002 D R p) ∈
      (((Class.cv p)).fv ∪ ((Class.cv (nb091AlphaDummy002 D R p))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb091_support_mem_0037 (D : Class) (R : Class) (p : Var) :
    (nb091AlphaDummy002 D R p) ∈
      (((synCcompl (Class.cab (nb091AlphaDummy007 D R p)
              (synWrex (nb091AlphaDummy008 D R p) (Class.cv p)
                (Wff.classEq (Class.cv (nb091AlphaDummy007 D R p))
                  (synCphi (Class.cv (nb091AlphaDummy008 D R p)))))))).fv ∪ ((synCcompl
            (Class.cab (nb091AlphaDummy007 D R p) (synWrex (nb091AlphaDummy008 D R p)
                (Class.cv (nb091AlphaDummy002 D R p))
                (Wff.classEq (Class.cv (nb091AlphaDummy007 D R p))
                  (synCun (synCphi (Class.cv (nb091AlphaDummy008 D R p)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb091AlphaDummy002 D R p) ≠ (nb091AlphaDummy007 D R p) from (by
          unfold nb091AlphaDummy007;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb091_support_mem_0036 D R p) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb091AlphaDummy002 D R p) ≠ (nb091AlphaDummy008 D R p) from (by
            unfold nb091AlphaDummy008;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb091_support_mem_0036 D R p) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb091_support_mem_0038 (D : Class) (R : Class) :
    (nb091AlphaDummy001 D R) ∈
      (((Class.cab (nb091AlphaDummy005 D R)
            (synWrex (nb091AlphaDummy006 D R) (Class.cv (nb091AlphaDummy001 D R))
              (Wff.classEq (Class.cv (nb091AlphaDummy005 D R))
                (synCun (synCphi (Class.cv (nb091AlphaDummy006 D R)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb091AlphaDummy005 D R)
            (synWrex (nb091AlphaDummy006 D R) (Class.cv (nb091AlphaDummy001 D R))
              (Wff.classEq (Class.cv (nb091AlphaDummy005 D R))
                (synCun (synCphi (Class.cv (nb091AlphaDummy006 D R)))
                  (synCsn (synC0c))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb091AlphaDummy001 D R) ≠ (nb091AlphaDummy005 D R) from (by
          unfold nb091AlphaDummy005;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb091_support_mem_0034 D R) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb091AlphaDummy001 D R) ≠ (nb091AlphaDummy006 D R) from (by
            unfold nb091AlphaDummy006;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb091_support_mem_0034 D R) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb091_support_mem_0039 (D : Class) (R : Class) (p : Var) :
    (nb091AlphaDummy002 D R p) ∈
      (((Class.cab (nb091AlphaDummy007 D R p) (synWrex (nb091AlphaDummy008 D R p)
              (Class.cv (nb091AlphaDummy002 D R p))
              (Wff.classEq (Class.cv (nb091AlphaDummy007 D R p))
                (synCun (synCphi (Class.cv (nb091AlphaDummy008 D R p)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb091AlphaDummy007 D R p)
            (synWrex (nb091AlphaDummy008 D R p) (Class.cv (nb091AlphaDummy002 D R p))
              (Wff.classEq (Class.cv (nb091AlphaDummy007 D R p))
                (synCun (synCphi (Class.cv (nb091AlphaDummy008 D R p)))
                  (synCsn (synC0c))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb091AlphaDummy002 D R p) ≠ (nb091AlphaDummy007 D R p) from (by
          unfold nb091AlphaDummy007;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb091_support_mem_0036 D R p) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb091AlphaDummy002 D R p) ≠ (nb091AlphaDummy008 D R p) from (by
            unfold nb091AlphaDummy008;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb091_support_mem_0036 D R p) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb091_support_mem_0040 (D : Class) (R : Class) :
    (nb091AlphaDummy006 D R) ∈
      (((synCcompl (synCphi (Class.cv (nb091AlphaDummy006 D R))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb091_support_mem_0041 (D : Class) (R : Class) (p : Var) :
    (nb091AlphaDummy008 D R p) ∈
      (((synCcompl (synCphi (Class.cv (nb091AlphaDummy008 D R p))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb091_support_mem_0042 (D : Class) (R : Class) :
    (nb091AlphaDummy006 D R) ∈
      (((synCphi (Class.cv (nb091AlphaDummy006 D R)))).fv ∪
        ((synCphi (Class.cv (nb091AlphaDummy006 D R)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb091_support_mem_0043 (D : Class) (R : Class) (p : Var) :
    (nb091AlphaDummy008 D R p) ∈
      (((synCphi (Class.cv (nb091AlphaDummy008 D R p)))).fv ∪
        ((synCphi (Class.cv (nb091AlphaDummy008 D R p)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb091_support_mem_0044 (D : Class) (R : Class) :
    (nb091AlphaDummy059 D R) ∈
      (({(nb091AlphaDummy059 D R)} : Finset Var) ∪
          ({(nb091AlphaDummy060 D R)} : Finset Var) ∪ ((synWa
            (Wff.classMem (Class.cv (nb091AlphaDummy059 D R)) (synCin D
                (synCima (synCcnv (synCdif R (synCid))) (synCsn
                    (synCuni (synCuni (Class.cv (nb091AlphaDummy000 D R))))))))
            (Wff.classMem (Class.cv (nb091AlphaDummy060 D R)) (synCin D
                (synCima (synCcnv (synCdif R (synCid))) (synCsn (synCuni
                      (synCuni (Class.cv (nb091AlphaDummy000 D R)))))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  with_reducible rw [Finset.mem_union]
  left
  exact Finset.mem_singleton_self _

theorem nb091_support_mem_0045 (D : Class) (R : Class) (p : Var) :
    (nb091AlphaDummy061 D R p) ∈
      (({(nb091AlphaDummy061 D R p)} : Finset Var) ∪
          ({(nb091AlphaDummy062 D R p)} : Finset Var) ∪ ((synWa
            (Wff.classMem (Class.cv (nb091AlphaDummy061 D R p)) (synCin D
                (synCima (synCcnv (synCdif R (synCid)))
                  (synCsn (synCuni (synCuni (Class.cv p)))))))
            (Wff.classMem (Class.cv (nb091AlphaDummy062 D R p)) (synCin D
                (synCima (synCcnv (synCdif R (synCid)))
                  (synCsn (synCuni (synCuni (Class.cv p))))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  with_reducible rw [Finset.mem_union]
  left
  exact Finset.mem_singleton_self _

theorem nb091_support_mem_0046 (D : Class) (R : Class) :
    (nb091AlphaDummy060 D R) ∈
      (({(nb091AlphaDummy059 D R)} : Finset Var) ∪
          ({(nb091AlphaDummy060 D R)} : Finset Var) ∪ ((synWa
            (Wff.classMem (Class.cv (nb091AlphaDummy059 D R)) (synCin D
                (synCima (synCcnv (synCdif R (synCid))) (synCsn
                    (synCuni (synCuni (Class.cv (nb091AlphaDummy000 D R))))))))
            (Wff.classMem (Class.cv (nb091AlphaDummy060 D R)) (synCin D
                (synCima (synCcnv (synCdif R (synCid))) (synCsn (synCuni
                      (synCuni (Class.cv (nb091AlphaDummy000 D R)))))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  with_reducible rw [Finset.mem_union]
  right
  exact Finset.mem_singleton_self _

theorem nb091_support_mem_0047 (D : Class) (R : Class) (p : Var) :
    (nb091AlphaDummy062 D R p) ∈
      (({(nb091AlphaDummy061 D R p)} : Finset Var) ∪
          ({(nb091AlphaDummy062 D R p)} : Finset Var) ∪ ((synWa
            (Wff.classMem (Class.cv (nb091AlphaDummy061 D R p)) (synCin D
                (synCima (synCcnv (synCdif R (synCid)))
                  (synCsn (synCuni (synCuni (Class.cv p)))))))
            (Wff.classMem (Class.cv (nb091AlphaDummy062 D R p)) (synCin D
                (synCima (synCcnv (synCdif R (synCid)))
                  (synCsn (synCuni (synCuni (Class.cv p))))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  with_reducible rw [Finset.mem_union]
  right
  exact Finset.mem_singleton_self _

theorem nb091_support_mem_0048 (D : Class) (R : Class) :
    (nb091AlphaDummy059 D R) ∈
      (((Class.cv (nb091AlphaDummy059 D R))).fv ∪
        ((Class.cv (nb091AlphaDummy060 D R))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb091_support_mem_0049 (D : Class) (R : Class) :
    (nb091AlphaDummy059 D R) ∈
      (((synCcompl (Class.cab (nb091AlphaDummy065 D R)
              (synWrex (nb091AlphaDummy066 D R) (Class.cv (nb091AlphaDummy059 D R))
                (Wff.classEq (Class.cv (nb091AlphaDummy065 D R))
                  (synCphi (Class.cv (nb091AlphaDummy066 D R)))))))).fv ∪ ((synCcompl
            (Class.cab (nb091AlphaDummy065 D R)
              (synWrex (nb091AlphaDummy066 D R) (Class.cv (nb091AlphaDummy060 D R))
                (Wff.classEq (Class.cv (nb091AlphaDummy065 D R))
                  (synCun (synCphi (Class.cv (nb091AlphaDummy066 D R)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb091AlphaDummy059 D R) ≠ (nb091AlphaDummy065 D R) from (by
          unfold nb091AlphaDummy065;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb091_support_mem_0048 D R) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb091AlphaDummy059 D R) ≠ (nb091AlphaDummy066 D R) from (by
            unfold nb091AlphaDummy066;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb091_support_mem_0048 D R) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb091_support_mem_0050 (D : Class) (R : Class) (p : Var) :
    (nb091AlphaDummy061 D R p) ∈
      (((Class.cv (nb091AlphaDummy061 D R p))).fv ∪
        ((Class.cv (nb091AlphaDummy062 D R p))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb091_support_mem_0051 (D : Class) (R : Class) (p : Var) :
    (nb091AlphaDummy061 D R p) ∈
      (((synCcompl (Class.cab (nb091AlphaDummy067 D R p)
              (synWrex (nb091AlphaDummy068 D R p) (Class.cv (nb091AlphaDummy061 D R p))
                (Wff.classEq (Class.cv (nb091AlphaDummy067 D R p))
                  (synCphi (Class.cv (nb091AlphaDummy068 D R p)))))))).fv ∪ ((synCcompl
            (Class.cab (nb091AlphaDummy067 D R p) (synWrex (nb091AlphaDummy068 D R p)
                (Class.cv (nb091AlphaDummy062 D R p))
                (Wff.classEq (Class.cv (nb091AlphaDummy067 D R p))
                  (synCun (synCphi (Class.cv (nb091AlphaDummy068 D R p)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb091AlphaDummy061 D R p) ≠ (nb091AlphaDummy067 D R p) from (by
          unfold nb091AlphaDummy067;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb091_support_mem_0050 D R p) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb091AlphaDummy061 D R p) ≠ (nb091AlphaDummy068 D R p) from (by
            unfold nb091AlphaDummy068;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb091_support_mem_0050 D R p) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb091_support_mem_0052 (D : Class) (R : Class) :
    (nb091AlphaDummy059 D R) ∈
      (((Class.cab (nb091AlphaDummy065 D R)
            (synWrex (nb091AlphaDummy066 D R) (Class.cv (nb091AlphaDummy059 D R))
              (Wff.classEq (Class.cv (nb091AlphaDummy065 D R))
                (synCphi (Class.cv (nb091AlphaDummy066 D R))))))).fv ∪
        ((Class.cab (nb091AlphaDummy065 D R)
            (synWrex (nb091AlphaDummy066 D R) (Class.cv (nb091AlphaDummy059 D R))
              (Wff.classEq (Class.cv (nb091AlphaDummy065 D R))
                (synCphi (Class.cv (nb091AlphaDummy066 D R))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb091AlphaDummy059 D R) ≠ (nb091AlphaDummy065 D R) from (by
          unfold nb091AlphaDummy065;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb091_support_mem_0048 D R) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb091AlphaDummy059 D R) ≠ (nb091AlphaDummy066 D R) from (by
            unfold nb091AlphaDummy066;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb091_support_mem_0048 D R) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb091_support_mem_0053 (D : Class) (R : Class) (p : Var) :
    (nb091AlphaDummy061 D R p) ∈
      (((Class.cab (nb091AlphaDummy067 D R p) (synWrex (nb091AlphaDummy068 D R p)
              (Class.cv (nb091AlphaDummy061 D R p))
              (Wff.classEq (Class.cv (nb091AlphaDummy067 D R p))
                (synCphi (Class.cv (nb091AlphaDummy068 D R p))))))).fv ∪
        ((Class.cab (nb091AlphaDummy067 D R p) (synWrex (nb091AlphaDummy068 D R p)
              (Class.cv (nb091AlphaDummy061 D R p))
              (Wff.classEq (Class.cv (nb091AlphaDummy067 D R p))
                (synCphi (Class.cv (nb091AlphaDummy068 D R p))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb091AlphaDummy061 D R p) ≠ (nb091AlphaDummy067 D R p) from (by
          unfold nb091AlphaDummy067;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb091_support_mem_0050 D R p) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb091AlphaDummy061 D R p) ≠ (nb091AlphaDummy068 D R p) from (by
            unfold nb091AlphaDummy068;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb091_support_mem_0050 D R p) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb091_support_mem_0054 (D : Class) (R : Class) :
    (nb091AlphaDummy066 D R) ∈ (((Class.cv (nb091AlphaDummy066 D R))).fv) :=
  by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb091_support_mem_0055 (D : Class) (R : Class) (p : Var) :
    (nb091AlphaDummy068 D R p) ∈ (((Class.cv (nb091AlphaDummy068 D R p))).fv) :=
  by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb091_support_mem_0056 (D : Class) (R : Class) :
    (nb091AlphaDummy073 D R) ∈
      (((Wff.classMem (Class.cv (nb091AlphaDummy073 D R)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb091AlphaDummy073 D R)) (synC1c))).fv ∪
        ((Class.cv (nb091AlphaDummy073 D R))).fv) :=
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
    (nb091AlphaDummy075 D R p) ∈
      (((Wff.classMem (Class.cv (nb091AlphaDummy075 D R p)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb091AlphaDummy075 D R p)) (synC1c))).fv ∪
        ((Class.cv (nb091AlphaDummy075 D R p))).fv) :=
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
    (nb091AlphaDummy073 D R) ∈
      (((Class.cv (nb091AlphaDummy073 D R))).fv ∪ ((synC1c)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb091_support_mem_0059 (D : Class) (R : Class) (p : Var) :
    (nb091AlphaDummy075 D R p) ∈
      (((Class.cv (nb091AlphaDummy075 D R p))).fv ∪ ((synC1c)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb091_support_mem_0060 (D : Class) (R : Class) :
    (nb091AlphaDummy080 D R) ∈
      (((synCnin (Class.cv (nb091AlphaDummy080 D R))
            (Class.cv (nb091AlphaDummy081 D R)))).fv ∪
        ((synCnin (Class.cv (nb091AlphaDummy080 D R))
            (Class.cv (nb091AlphaDummy081 D R)))).fv) :=
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
    (nb091AlphaDummy083 D R p) ∈
      (((synCnin (Class.cv (nb091AlphaDummy083 D R p))
            (Class.cv (nb091AlphaDummy084 D R p)))).fv ∪
        ((synCnin (Class.cv (nb091AlphaDummy083 D R p))
            (Class.cv (nb091AlphaDummy084 D R p)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb091_support_mem_0062 (D : Class) (R : Class) :
    (nb091AlphaDummy080 D R) ∈
      (((Class.cv (nb091AlphaDummy080 D R))).fv ∪
        ((Class.cv (nb091AlphaDummy081 D R))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb091_support_mem_0063 (D : Class) (R : Class) (p : Var) :
    (nb091AlphaDummy083 D R p) ∈
      (((Class.cv (nb091AlphaDummy083 D R p))).fv ∪
        ((Class.cv (nb091AlphaDummy084 D R p))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb091_support_mem_0064 (D : Class) (R : Class) :
    (nb091AlphaDummy081 D R) ∈
      (((synCnin (Class.cv (nb091AlphaDummy080 D R))
            (Class.cv (nb091AlphaDummy081 D R)))).fv ∪
        ((synCnin (Class.cv (nb091AlphaDummy080 D R))
            (Class.cv (nb091AlphaDummy081 D R)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb091_support_mem_0065 (D : Class) (R : Class) (p : Var) :
    (nb091AlphaDummy084 D R p) ∈
      (((synCnin (Class.cv (nb091AlphaDummy083 D R p))
            (Class.cv (nb091AlphaDummy084 D R p)))).fv ∪
        ((synCnin (Class.cv (nb091AlphaDummy083 D R p))
            (Class.cv (nb091AlphaDummy084 D R p)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb091_support_mem_0066 (D : Class) (R : Class) :
    (nb091AlphaDummy081 D R) ∈
      (((Class.cv (nb091AlphaDummy080 D R))).fv ∪
        ((Class.cv (nb091AlphaDummy081 D R))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb091_support_mem_0067 (D : Class) (R : Class) (p : Var) :
    (nb091AlphaDummy084 D R p) ∈
      (((Class.cv (nb091AlphaDummy083 D R p))).fv ∪
        ((Class.cv (nb091AlphaDummy084 D R p))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb091_support_mem_0068 (D : Class) (R : Class) :
    (nb091AlphaDummy080 D R) ∈
      (((synCcompl (Class.cv (nb091AlphaDummy080 D R)))).fv ∪
        ((synCcompl (Class.cv (nb091AlphaDummy081 D R)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb091_support_mem_0069 (D : Class) (R : Class) (p : Var) :
    (nb091AlphaDummy083 D R p) ∈
      (((synCcompl (Class.cv (nb091AlphaDummy083 D R p)))).fv ∪
        ((synCcompl (Class.cv (nb091AlphaDummy084 D R p)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb091_support_mem_0070 (D : Class) (R : Class) :
    (nb091AlphaDummy080 D R) ∈
      (((Class.cv (nb091AlphaDummy080 D R))).fv ∪
        ((Class.cv (nb091AlphaDummy080 D R))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb091_support_mem_0071 (D : Class) (R : Class) (p : Var) :
    (nb091AlphaDummy083 D R p) ∈
      (((Class.cv (nb091AlphaDummy083 D R p))).fv ∪
        ((Class.cv (nb091AlphaDummy083 D R p))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb091_support_mem_0072 (D : Class) (R : Class) :
    (nb091AlphaDummy081 D R) ∈
      (((synCcompl (Class.cv (nb091AlphaDummy080 D R)))).fv ∪
        ((synCcompl (Class.cv (nb091AlphaDummy081 D R)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb091_support_mem_0073 (D : Class) (R : Class) (p : Var) :
    (nb091AlphaDummy084 D R p) ∈
      (((synCcompl (Class.cv (nb091AlphaDummy083 D R p)))).fv ∪
        ((synCcompl (Class.cv (nb091AlphaDummy084 D R p)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb091_support_mem_0074 (D : Class) (R : Class) :
    (nb091AlphaDummy081 D R) ∈
      (((Class.cv (nb091AlphaDummy081 D R))).fv ∪
        ((Class.cv (nb091AlphaDummy081 D R))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb091_support_mem_0075 (D : Class) (R : Class) (p : Var) :
    (nb091AlphaDummy084 D R p) ∈
      (((Class.cv (nb091AlphaDummy084 D R p))).fv ∪
        ((Class.cv (nb091AlphaDummy084 D R p))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb091_support_mem_0076 (D : Class) (R : Class) :
    (nb091AlphaDummy060 D R) ∈
      (((Class.cv (nb091AlphaDummy059 D R))).fv ∪
        ((Class.cv (nb091AlphaDummy060 D R))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb091_support_mem_0077 (D : Class) (R : Class) :
    (nb091AlphaDummy060 D R) ∈
      (((synCcompl (Class.cab (nb091AlphaDummy065 D R)
              (synWrex (nb091AlphaDummy066 D R) (Class.cv (nb091AlphaDummy059 D R))
                (Wff.classEq (Class.cv (nb091AlphaDummy065 D R))
                  (synCphi (Class.cv (nb091AlphaDummy066 D R)))))))).fv ∪ ((synCcompl
            (Class.cab (nb091AlphaDummy065 D R)
              (synWrex (nb091AlphaDummy066 D R) (Class.cv (nb091AlphaDummy060 D R))
                (Wff.classEq (Class.cv (nb091AlphaDummy065 D R))
                  (synCun (synCphi (Class.cv (nb091AlphaDummy066 D R)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb091AlphaDummy060 D R) ≠ (nb091AlphaDummy065 D R) from (by
          unfold nb091AlphaDummy065;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb091_support_mem_0076 D R) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb091AlphaDummy060 D R) ≠ (nb091AlphaDummy066 D R) from (by
            unfold nb091AlphaDummy066;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb091_support_mem_0076 D R) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb091_support_mem_0078 (D : Class) (R : Class) (p : Var) :
    (nb091AlphaDummy062 D R p) ∈
      (((Class.cv (nb091AlphaDummy061 D R p))).fv ∪
        ((Class.cv (nb091AlphaDummy062 D R p))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb091_support_mem_0079 (D : Class) (R : Class) (p : Var) :
    (nb091AlphaDummy062 D R p) ∈
      (((synCcompl (Class.cab (nb091AlphaDummy067 D R p)
              (synWrex (nb091AlphaDummy068 D R p) (Class.cv (nb091AlphaDummy061 D R p))
                (Wff.classEq (Class.cv (nb091AlphaDummy067 D R p))
                  (synCphi (Class.cv (nb091AlphaDummy068 D R p)))))))).fv ∪ ((synCcompl
            (Class.cab (nb091AlphaDummy067 D R p) (synWrex (nb091AlphaDummy068 D R p)
                (Class.cv (nb091AlphaDummy062 D R p))
                (Wff.classEq (Class.cv (nb091AlphaDummy067 D R p))
                  (synCun (synCphi (Class.cv (nb091AlphaDummy068 D R p)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb091AlphaDummy062 D R p) ≠ (nb091AlphaDummy067 D R p) from (by
          unfold nb091AlphaDummy067;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb091_support_mem_0078 D R p) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb091AlphaDummy062 D R p) ≠ (nb091AlphaDummy068 D R p) from (by
            unfold nb091AlphaDummy068;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb091_support_mem_0078 D R p) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb091_support_mem_0080 (D : Class) (R : Class) :
    (nb091AlphaDummy060 D R) ∈
      (((Class.cab (nb091AlphaDummy065 D R)
            (synWrex (nb091AlphaDummy066 D R) (Class.cv (nb091AlphaDummy060 D R))
              (Wff.classEq (Class.cv (nb091AlphaDummy065 D R))
                (synCun (synCphi (Class.cv (nb091AlphaDummy066 D R)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb091AlphaDummy065 D R)
            (synWrex (nb091AlphaDummy066 D R) (Class.cv (nb091AlphaDummy060 D R))
              (Wff.classEq (Class.cv (nb091AlphaDummy065 D R))
                (synCun (synCphi (Class.cv (nb091AlphaDummy066 D R)))
                  (synCsn (synC0c))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb091AlphaDummy060 D R) ≠ (nb091AlphaDummy065 D R) from (by
          unfold nb091AlphaDummy065;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb091_support_mem_0076 D R) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb091AlphaDummy060 D R) ≠ (nb091AlphaDummy066 D R) from (by
            unfold nb091AlphaDummy066;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb091_support_mem_0076 D R) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb091_support_mem_0081 (D : Class) (R : Class) (p : Var) :
    (nb091AlphaDummy062 D R p) ∈
      (((Class.cab (nb091AlphaDummy067 D R p) (synWrex (nb091AlphaDummy068 D R p)
              (Class.cv (nb091AlphaDummy062 D R p))
              (Wff.classEq (Class.cv (nb091AlphaDummy067 D R p))
                (synCun (synCphi (Class.cv (nb091AlphaDummy068 D R p)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb091AlphaDummy067 D R p)
            (synWrex (nb091AlphaDummy068 D R p) (Class.cv (nb091AlphaDummy062 D R p))
              (Wff.classEq (Class.cv (nb091AlphaDummy067 D R p))
                (synCun (synCphi (Class.cv (nb091AlphaDummy068 D R p)))
                  (synCsn (synC0c))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb091AlphaDummy062 D R p) ≠ (nb091AlphaDummy067 D R p) from (by
          unfold nb091AlphaDummy067;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb091_support_mem_0078 D R p) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb091AlphaDummy062 D R p) ≠ (nb091AlphaDummy068 D R p) from (by
            unfold nb091AlphaDummy068;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb091_support_mem_0078 D R p) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb091_support_mem_0082 (D : Class) (R : Class) :
    (nb091AlphaDummy066 D R) ∈
      (((synCcompl (synCphi (Class.cv (nb091AlphaDummy066 D R))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb091_support_mem_0083 (D : Class) (R : Class) (p : Var) :
    (nb091AlphaDummy068 D R p) ∈
      (((synCcompl (synCphi (Class.cv (nb091AlphaDummy068 D R p))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb091_support_mem_0084 (D : Class) (R : Class) :
    (nb091AlphaDummy066 D R) ∈
      (((synCphi (Class.cv (nb091AlphaDummy066 D R)))).fv ∪
        ((synCphi (Class.cv (nb091AlphaDummy066 D R)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb091_support_mem_0085 (D : Class) (R : Class) (p : Var) :
    (nb091AlphaDummy068 D R p) ∈
      (((synCphi (Class.cv (nb091AlphaDummy068 D R p)))).fv ∪
        ((synCphi (Class.cv (nb091AlphaDummy068 D R p)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb091_support_mem_0086 (D : Class) (R : Class) :
    (nb091AlphaDummy000 D R) ∈
      (((synChwniso D)).fv ∪ ((synCsn (synChnwcutcode R D
              (synCuni (synCuni (Class.cv (nb091AlphaDummy000 D R))))))).fv) :=
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
      (((synChwniso D)).fv ∪
        ((synCsn (synChnwcutcode R D (synCuni (synCuni (Class.cv p)))))).fv) :=
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
    (nb091AlphaDummy000 D R) ∈
      (((synChnwcutcode R D
          (synCuni (synCuni (Class.cv (nb091AlphaDummy000 D R)))))).fv) :=
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
    p ∈ (((synChnwcutcode R D (synCuni (synCuni (Class.cv p))))).fv) :=
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
    (nb091AlphaDummy000 D R) ∈
      (((synCin R (synCxp (synCin D (synCima (synCcnv (synCdif R (synCid)))
                  (synCsn (synCuni (synCuni (Class.cv (nb091AlphaDummy000 D R)))))))
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (synCuni
                      (synCuni (Class.cv (nb091AlphaDummy000 D R)))))))))).fv ∪ ((synCin D
            (synCima (synCcnv (synCdif R (synCid))) (synCsn
                (synCuni (synCuni (Class.cv (nb091AlphaDummy000 D R)))))))).fv) :=
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
    (nb091AlphaDummy000 D R) ∈
      (((synCcompl (Class.cab (nb091AlphaDummy047 D R) (synWrex (nb091AlphaDummy048 D R)
                (synCin R (synCxp (synCin D (synCima (synCcnv (synCdif R (synCid)))
                        (synCsn (synCuni (synCuni (Class.cv (nb091AlphaDummy000 D R)))))))
                    (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (synCuni
                            (synCuni (Class.cv (nb091AlphaDummy000 D R)))))))))
                (Wff.classEq (Class.cv (nb091AlphaDummy047 D R))
                  (synCphi (Class.cv (nb091AlphaDummy048 D R)))))))).fv ∪ ((synCcompl
            (Class.cab (nb091AlphaDummy047 D R) (synWrex (nb091AlphaDummy048 D R)
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn
                      (synCuni (synCuni (Class.cv (nb091AlphaDummy000 D R)))))))
                (Wff.classEq (Class.cv (nb091AlphaDummy047 D R))
                  (synCun (synCphi (Class.cv (nb091AlphaDummy048 D R)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb091AlphaDummy000 D R) ≠ (nb091AlphaDummy047 D R) from (by
          unfold nb091AlphaDummy047;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb091_support_mem_0090 D R) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb091AlphaDummy000 D R) ≠ (nb091AlphaDummy048 D R) from (by
            unfold nb091AlphaDummy048;
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
      (((synCin R (synCxp (synCin D (synCima (synCcnv (synCdif R (synCid)))
                  (synCsn (synCuni (synCuni (Class.cv p)))))) (synCin D
                (synCima (synCcnv (synCdif R (synCid)))
                  (synCsn (synCuni (synCuni (Class.cv p))))))))).fv ∪ ((synCin D
            (synCima (synCcnv (synCdif R (synCid)))
              (synCsn (synCuni (synCuni (Class.cv p))))))).fv) :=
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
      (((synCcompl (Class.cab (nb091AlphaDummy049 D R p)
              (synWrex (nb091AlphaDummy050 D R p) (synCin R (synCxp (synCin D
                      (synCima (synCcnv (synCdif R (synCid)))
                        (synCsn (synCuni (synCuni (Class.cv p)))))) (synCin D
                      (synCima (synCcnv (synCdif R (synCid)))
                        (synCsn (synCuni (synCuni (Class.cv p))))))))
                (Wff.classEq (Class.cv (nb091AlphaDummy049 D R p))
                  (synCphi (Class.cv (nb091AlphaDummy050 D R p)))))))).fv ∪ ((synCcompl
            (Class.cab (nb091AlphaDummy049 D R p) (synWrex (nb091AlphaDummy050 D R p)
                (synCin D (synCima (synCcnv (synCdif R (synCid)))
                    (synCsn (synCuni (synCuni (Class.cv p))))))
                (Wff.classEq (Class.cv (nb091AlphaDummy049 D R p))
                  (synCun (synCphi (Class.cv (nb091AlphaDummy050 D R p)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show p ≠ (nb091AlphaDummy049 D R p) from (by
          unfold nb091AlphaDummy049;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb091_support_mem_0092 D R p) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show p ≠ (nb091AlphaDummy050 D R p) from (by
            unfold nb091AlphaDummy050;
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
    (nb091AlphaDummy000 D R) ∈
      (((Class.cab (nb091AlphaDummy047 D R) (synWrex (nb091AlphaDummy048 D R) (synCin R
                (synCxp (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn
                        (synCuni (synCuni (Class.cv (nb091AlphaDummy000 D R)))))))
                  (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn
                        (synCuni (synCuni (Class.cv (nb091AlphaDummy000 D R)))))))))
              (Wff.classEq (Class.cv (nb091AlphaDummy047 D R))
                (synCphi (Class.cv (nb091AlphaDummy048 D R))))))).fv ∪
        ((Class.cab (nb091AlphaDummy047 D R) (synWrex (nb091AlphaDummy048 D R) (synCin R
                (synCxp (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn
                        (synCuni (synCuni (Class.cv (nb091AlphaDummy000 D R)))))))
                  (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn
                        (synCuni (synCuni (Class.cv (nb091AlphaDummy000 D R)))))))))
              (Wff.classEq (Class.cv (nb091AlphaDummy047 D R))
                (synCphi (Class.cv (nb091AlphaDummy048 D R))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb091AlphaDummy000 D R) ≠ (nb091AlphaDummy047 D R) from (by
          unfold nb091AlphaDummy047;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb091_support_mem_0090 D R) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb091AlphaDummy000 D R) ≠ (nb091AlphaDummy048 D R) from (by
            unfold nb091AlphaDummy048;
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
      (((Class.cab (nb091AlphaDummy049 D R p) (synWrex (nb091AlphaDummy050 D R p)
              (synCin R (synCxp (synCin D (synCima (synCcnv (synCdif R (synCid)))
                      (synCsn (synCuni (synCuni (Class.cv p)))))) (synCin D
                    (synCima (synCcnv (synCdif R (synCid)))
                      (synCsn (synCuni (synCuni (Class.cv p))))))))
              (Wff.classEq (Class.cv (nb091AlphaDummy049 D R p))
                (synCphi (Class.cv (nb091AlphaDummy050 D R p))))))).fv ∪
        ((Class.cab (nb091AlphaDummy049 D R p) (synWrex (nb091AlphaDummy050 D R p)
              (synCin R (synCxp (synCin D (synCima (synCcnv (synCdif R (synCid)))
                      (synCsn (synCuni (synCuni (Class.cv p)))))) (synCin D
                    (synCima (synCcnv (synCdif R (synCid)))
                      (synCsn (synCuni (synCuni (Class.cv p))))))))
              (Wff.classEq (Class.cv (nb091AlphaDummy049 D R p))
                (synCphi (Class.cv (nb091AlphaDummy050 D R p))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show p ≠ (nb091AlphaDummy049 D R p) from (by
          unfold nb091AlphaDummy049;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb091_support_mem_0092 D R p) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show p ≠ (nb091AlphaDummy050 D R p) from (by
            unfold nb091AlphaDummy050;
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
    (nb091AlphaDummy000 D R) ∈
      (((synCnin R (synCxp (synCin D (synCima (synCcnv (synCdif R (synCid)))
                  (synCsn (synCuni (synCuni (Class.cv (nb091AlphaDummy000 D R)))))))
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (synCuni
                      (synCuni (Class.cv (nb091AlphaDummy000 D R)))))))))).fv ∪ ((synCnin R
            (synCxp (synCin D (synCima (synCcnv (synCdif R (synCid)))
                  (synCsn (synCuni (synCuni (Class.cv (nb091AlphaDummy000 D R)))))))
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (synCuni
                      (synCuni (Class.cv (nb091AlphaDummy000 D R)))))))))).fv) :=
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
      (((synCnin R (synCxp (synCin D (synCima (synCcnv (synCdif R (synCid)))
                  (synCsn (synCuni (synCuni (Class.cv p)))))) (synCin D
                (synCima (synCcnv (synCdif R (synCid)))
                  (synCsn (synCuni (synCuni (Class.cv p))))))))).fv ∪ ((synCnin R (synCxp
              (synCin D (synCima (synCcnv (synCdif R (synCid)))
                  (synCsn (synCuni (synCuni (Class.cv p)))))) (synCin D
                (synCima (synCcnv (synCdif R (synCid)))
                  (synCsn (synCuni (synCuni (Class.cv p))))))))).fv) :=
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
    (nb091AlphaDummy000 D R) ∈
      ((R).fv ∪ ((synCxp (synCin D (synCima (synCcnv (synCdif R (synCid)))
                (synCsn (synCuni (synCuni (Class.cv (nb091AlphaDummy000 D R)))))))
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn
                  (synCuni (synCuni (Class.cv (nb091AlphaDummy000 D R))))))))).fv) :=
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
      ((R).fv ∪ ((synCxp (synCin D (synCima (synCcnv (synCdif R (synCid)))
                (synCsn (synCuni (synCuni (Class.cv p)))))) (synCin D
              (synCima (synCcnv (synCdif R (synCid)))
                (synCsn (synCuni (synCuni (Class.cv p)))))))).fv) :=
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
    (nb091AlphaDummy000 D R) ∈
      (({(nb091AlphaDummy059 D R)} : Finset Var) ∪
          ({(nb091AlphaDummy060 D R)} : Finset Var) ∪ ((synWa
            (Wff.classMem (Class.cv (nb091AlphaDummy059 D R)) (synCin D
                (synCima (synCcnv (synCdif R (synCid))) (synCsn
                    (synCuni (synCuni (Class.cv (nb091AlphaDummy000 D R))))))))
            (Wff.classMem (Class.cv (nb091AlphaDummy060 D R)) (synCin D
                (synCima (synCcnv (synCdif R (synCid))) (synCsn (synCuni
                      (synCuni (Class.cv (nb091AlphaDummy000 D R)))))))))).fv) :=
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
      (({(nb091AlphaDummy061 D R p)} : Finset Var) ∪
          ({(nb091AlphaDummy062 D R p)} : Finset Var) ∪ ((synWa
            (Wff.classMem (Class.cv (nb091AlphaDummy061 D R p)) (synCin D
                (synCima (synCcnv (synCdif R (synCid)))
                  (synCsn (synCuni (synCuni (Class.cv p)))))))
            (Wff.classMem (Class.cv (nb091AlphaDummy062 D R p)) (synCin D
                (synCima (synCcnv (synCdif R (synCid)))
                  (synCsn (synCuni (synCuni (Class.cv p))))))))).fv) :=
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
    (nb091AlphaDummy000 D R) ∈
      (((synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn
                (synCuni (synCuni (Class.cv (nb091AlphaDummy000 D R)))))))).fv ∪
        ((synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn
                (synCuni (synCuni (Class.cv (nb091AlphaDummy000 D R)))))))).fv) :=
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
      (((synCin D (synCima (synCcnv (synCdif R (synCid)))
              (synCsn (synCuni (synCuni (Class.cv p))))))).fv ∪ ((synCin D
            (synCima (synCcnv (synCdif R (synCid)))
              (synCsn (synCuni (synCuni (Class.cv p))))))).fv) :=
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
    (nb091AlphaDummy000 D R) ∈
      (((synCnin D (synCima (synCcnv (synCdif R (synCid))) (synCsn
                (synCuni (synCuni (Class.cv (nb091AlphaDummy000 D R)))))))).fv ∪
        ((synCnin D (synCima (synCcnv (synCdif R (synCid))) (synCsn
                (synCuni (synCuni (Class.cv (nb091AlphaDummy000 D R)))))))).fv) :=
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
      (((synCnin D (synCima (synCcnv (synCdif R (synCid)))
              (synCsn (synCuni (synCuni (Class.cv p))))))).fv ∪ ((synCnin D
            (synCima (synCcnv (synCdif R (synCid)))
              (synCsn (synCuni (synCuni (Class.cv p))))))).fv) :=
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
    (nb091AlphaDummy000 D R) ∈
      ((D).fv ∪ ((synCima (synCcnv (synCdif R (synCid))) (synCsn
              (synCuni (synCuni (Class.cv (nb091AlphaDummy000 D R))))))).fv) :=
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
      ((D).fv ∪ ((synCima (synCcnv (synCdif R (synCid)))
            (synCsn (synCuni (synCuni (Class.cv p)))))).fv) :=
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
    (nb091AlphaDummy000 D R) ∈
      (((synCcnv (synCdif R (synCid)))).fv ∪
        ((synCsn (synCuni (synCuni (Class.cv (nb091AlphaDummy000 D R)))))).fv) :=
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
      (((synCcnv (synCdif R (synCid)))).fv ∪
        ((synCsn (synCuni (synCuni (Class.cv p))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_csn]
  rw [fv_syn_cuni]
  rw [fv_syn_cuni]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb091_support_mem_0110 (D : Class) (R : Class) :
    (nb091AlphaDummy000 D R) ∈
      (((synCuni (synCuni (Class.cv (nb091AlphaDummy000 D R))))).fv) :=
  by
  rw [fv_syn_cuni]
  rw [fv_syn_cuni]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb091_support_mem_0111 (p : Var) :
    p ∈ (((synCuni (synCuni (Class.cv p)))).fv) :=
  by
  rw [fv_syn_cuni]
  rw [fv_syn_cuni]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb091_support_mem_0112 (D : Class) (R : Class) :
    (nb091AlphaDummy000 D R) ∈
      (((synCuni (Class.cv (nb091AlphaDummy000 D R)))).fv) :=
  by
  rw [fv_syn_cuni]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb091_support_mem_0113 (p : Var) : p ∈ (((synCuni (Class.cv p))).fv) :=
  by
  rw [fv_syn_cuni]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb091_support_mem_0114 (D : Class) (R : Class) :
    (nb091AlphaDummy000 D R) ∈ (((Class.cv (nb091AlphaDummy000 D R))).fv) :=
  by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb091_support_mem_0115 (p : Var) : p ∈ (((Class.cv p)).fv) :=
  by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb091_support_mem_0116 (D : Class) (R : Class) :
    (nb091AlphaDummy106 D R) ∈
      (((Class.cv (nb091AlphaDummy106 D R))).fv ∪
        ((Class.cv (nb091AlphaDummy105 D R))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb091_support_mem_0117 (D : Class) (R : Class) :
    (nb091AlphaDummy106 D R) ∈
      (((synCcompl (Class.cab (nb091AlphaDummy119 D R)
              (synWrex (nb091AlphaDummy120 D R) (Class.cv (nb091AlphaDummy106 D R))
                (Wff.classEq (Class.cv (nb091AlphaDummy119 D R))
                  (synCphi (Class.cv (nb091AlphaDummy120 D R)))))))).fv ∪ ((synCcompl
            (Class.cab (nb091AlphaDummy119 D R)
              (synWrex (nb091AlphaDummy120 D R) (Class.cv (nb091AlphaDummy105 D R))
                (Wff.classEq (Class.cv (nb091AlphaDummy119 D R))
                  (synCun (synCphi (Class.cv (nb091AlphaDummy120 D R)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb091AlphaDummy106 D R) ≠ (nb091AlphaDummy119 D R) from (by
          unfold nb091AlphaDummy119;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb091_support_mem_0116 D R) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb091AlphaDummy106 D R) ≠ (nb091AlphaDummy120 D R) from (by
            unfold nb091AlphaDummy120;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb091_support_mem_0116 D R) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb091_support_mem_0118 (R : Class) (p : Var) :
    (nb091AlphaDummy108 R p) ∈
      (((Class.cv (nb091AlphaDummy108 R p))).fv ∪
        ((Class.cv (nb091AlphaDummy107 R p))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb091_support_mem_0119 (R : Class) (p : Var) :
    (nb091AlphaDummy108 R p) ∈
      (((synCcompl (Class.cab (nb091AlphaDummy121 R p)
              (synWrex (nb091AlphaDummy122 R p) (Class.cv (nb091AlphaDummy108 R p))
                (Wff.classEq (Class.cv (nb091AlphaDummy121 R p))
                  (synCphi (Class.cv (nb091AlphaDummy122 R p)))))))).fv ∪ ((synCcompl
            (Class.cab (nb091AlphaDummy121 R p)
              (synWrex (nb091AlphaDummy122 R p) (Class.cv (nb091AlphaDummy107 R p))
                (Wff.classEq (Class.cv (nb091AlphaDummy121 R p))
                  (synCun (synCphi (Class.cv (nb091AlphaDummy122 R p)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb091AlphaDummy108 R p) ≠ (nb091AlphaDummy121 R p) from (by
          unfold nb091AlphaDummy121;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb091_support_mem_0118 R p) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb091AlphaDummy108 R p) ≠ (nb091AlphaDummy122 R p) from (by
            unfold nb091AlphaDummy122;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb091_support_mem_0118 R p) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb091_support_mem_0120 (D : Class) (R : Class) :
    (nb091AlphaDummy106 D R) ∈
      (((Class.cab (nb091AlphaDummy119 D R)
            (synWrex (nb091AlphaDummy120 D R) (Class.cv (nb091AlphaDummy106 D R))
              (Wff.classEq (Class.cv (nb091AlphaDummy119 D R))
                (synCphi (Class.cv (nb091AlphaDummy120 D R))))))).fv ∪
        ((Class.cab (nb091AlphaDummy119 D R)
            (synWrex (nb091AlphaDummy120 D R) (Class.cv (nb091AlphaDummy106 D R))
              (Wff.classEq (Class.cv (nb091AlphaDummy119 D R))
                (synCphi (Class.cv (nb091AlphaDummy120 D R))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb091AlphaDummy106 D R) ≠ (nb091AlphaDummy119 D R) from (by
          unfold nb091AlphaDummy119;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb091_support_mem_0116 D R) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb091AlphaDummy106 D R) ≠ (nb091AlphaDummy120 D R) from (by
            unfold nb091AlphaDummy120;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb091_support_mem_0116 D R) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb091_support_mem_0121 (R : Class) (p : Var) :
    (nb091AlphaDummy108 R p) ∈
      (((Class.cab (nb091AlphaDummy121 R p)
            (synWrex (nb091AlphaDummy122 R p) (Class.cv (nb091AlphaDummy108 R p))
              (Wff.classEq (Class.cv (nb091AlphaDummy121 R p))
                (synCphi (Class.cv (nb091AlphaDummy122 R p))))))).fv ∪
        ((Class.cab (nb091AlphaDummy121 R p)
            (synWrex (nb091AlphaDummy122 R p) (Class.cv (nb091AlphaDummy108 R p))
              (Wff.classEq (Class.cv (nb091AlphaDummy121 R p))
                (synCphi (Class.cv (nb091AlphaDummy122 R p))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb091AlphaDummy108 R p) ≠ (nb091AlphaDummy121 R p) from (by
          unfold nb091AlphaDummy121;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb091_support_mem_0118 R p) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb091AlphaDummy108 R p) ≠ (nb091AlphaDummy122 R p) from (by
            unfold nb091AlphaDummy122;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb091_support_mem_0118 R p) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb091_support_mem_0122 (D : Class) (R : Class) :
    (nb091AlphaDummy120 D R) ∈ (((Class.cv (nb091AlphaDummy120 D R))).fv) :=
  by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb091_support_mem_0123 (R : Class) (p : Var) :
    (nb091AlphaDummy122 R p) ∈ (((Class.cv (nb091AlphaDummy122 R p))).fv) :=
  by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb091_support_mem_0124 (D : Class) (R : Class) :
    (nb091AlphaDummy127 D R) ∈
      (((Wff.classMem (Class.cv (nb091AlphaDummy127 D R)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb091AlphaDummy127 D R)) (synC1c))).fv ∪
        ((Class.cv (nb091AlphaDummy127 D R))).fv) :=
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
    (nb091AlphaDummy129 R p) ∈
      (((Wff.classMem (Class.cv (nb091AlphaDummy129 R p)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb091AlphaDummy129 R p)) (synC1c))).fv ∪
        ((Class.cv (nb091AlphaDummy129 R p))).fv) :=
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
    (nb091AlphaDummy127 D R) ∈
      (((Class.cv (nb091AlphaDummy127 D R))).fv ∪ ((synC1c)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb091_support_mem_0127 (R : Class) (p : Var) :
    (nb091AlphaDummy129 R p) ∈
      (((Class.cv (nb091AlphaDummy129 R p))).fv ∪ ((synC1c)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb091_support_mem_0128 (D : Class) (R : Class) :
    (nb091AlphaDummy134 D R) ∈
      (((synCnin (Class.cv (nb091AlphaDummy134 D R))
            (Class.cv (nb091AlphaDummy135 D R)))).fv ∪
        ((synCnin (Class.cv (nb091AlphaDummy134 D R))
            (Class.cv (nb091AlphaDummy135 D R)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb091_support_mem_0129 (R : Class) (p : Var) :
    (nb091AlphaDummy137 R p) ∈
      (((synCnin (Class.cv (nb091AlphaDummy137 R p))
            (Class.cv (nb091AlphaDummy138 R p)))).fv ∪
        ((synCnin (Class.cv (nb091AlphaDummy137 R p))
            (Class.cv (nb091AlphaDummy138 R p)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb091_support_mem_0130 (D : Class) (R : Class) :
    (nb091AlphaDummy134 D R) ∈
      (((Class.cv (nb091AlphaDummy134 D R))).fv ∪
        ((Class.cv (nb091AlphaDummy135 D R))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb091_support_mem_0131 (R : Class) (p : Var) :
    (nb091AlphaDummy137 R p) ∈
      (((Class.cv (nb091AlphaDummy137 R p))).fv ∪
        ((Class.cv (nb091AlphaDummy138 R p))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb091_support_mem_0132 (D : Class) (R : Class) :
    (nb091AlphaDummy135 D R) ∈
      (((synCnin (Class.cv (nb091AlphaDummy134 D R))
            (Class.cv (nb091AlphaDummy135 D R)))).fv ∪
        ((synCnin (Class.cv (nb091AlphaDummy134 D R))
            (Class.cv (nb091AlphaDummy135 D R)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb091_support_mem_0133 (R : Class) (p : Var) :
    (nb091AlphaDummy138 R p) ∈
      (((synCnin (Class.cv (nb091AlphaDummy137 R p))
            (Class.cv (nb091AlphaDummy138 R p)))).fv ∪
        ((synCnin (Class.cv (nb091AlphaDummy137 R p))
            (Class.cv (nb091AlphaDummy138 R p)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb091_support_mem_0134 (D : Class) (R : Class) :
    (nb091AlphaDummy135 D R) ∈
      (((Class.cv (nb091AlphaDummy134 D R))).fv ∪
        ((Class.cv (nb091AlphaDummy135 D R))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb091_support_mem_0135 (R : Class) (p : Var) :
    (nb091AlphaDummy138 R p) ∈
      (((Class.cv (nb091AlphaDummy137 R p))).fv ∪
        ((Class.cv (nb091AlphaDummy138 R p))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb091_support_mem_0136 (D : Class) (R : Class) :
    (nb091AlphaDummy134 D R) ∈
      (((synCcompl (Class.cv (nb091AlphaDummy134 D R)))).fv ∪
        ((synCcompl (Class.cv (nb091AlphaDummy135 D R)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb091_support_mem_0137 (R : Class) (p : Var) :
    (nb091AlphaDummy137 R p) ∈
      (((synCcompl (Class.cv (nb091AlphaDummy137 R p)))).fv ∪
        ((synCcompl (Class.cv (nb091AlphaDummy138 R p)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb091_support_mem_0138 (D : Class) (R : Class) :
    (nb091AlphaDummy134 D R) ∈
      (((Class.cv (nb091AlphaDummy134 D R))).fv ∪
        ((Class.cv (nb091AlphaDummy134 D R))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb091_support_mem_0139 (R : Class) (p : Var) :
    (nb091AlphaDummy137 R p) ∈
      (((Class.cv (nb091AlphaDummy137 R p))).fv ∪
        ((Class.cv (nb091AlphaDummy137 R p))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb091_support_mem_0140 (D : Class) (R : Class) :
    (nb091AlphaDummy135 D R) ∈
      (((synCcompl (Class.cv (nb091AlphaDummy134 D R)))).fv ∪
        ((synCcompl (Class.cv (nb091AlphaDummy135 D R)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb091_support_mem_0141 (R : Class) (p : Var) :
    (nb091AlphaDummy138 R p) ∈
      (((synCcompl (Class.cv (nb091AlphaDummy137 R p)))).fv ∪
        ((synCcompl (Class.cv (nb091AlphaDummy138 R p)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb091_support_mem_0142 (D : Class) (R : Class) :
    (nb091AlphaDummy135 D R) ∈
      (((Class.cv (nb091AlphaDummy135 D R))).fv ∪
        ((Class.cv (nb091AlphaDummy135 D R))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb091_support_mem_0143 (R : Class) (p : Var) :
    (nb091AlphaDummy138 R p) ∈
      (((Class.cv (nb091AlphaDummy138 R p))).fv ∪
        ((Class.cv (nb091AlphaDummy138 R p))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb091_support_mem_0144 (D : Class) (R : Class) :
    (nb091AlphaDummy105 D R) ∈
      (((Class.cv (nb091AlphaDummy106 D R))).fv ∪
        ((Class.cv (nb091AlphaDummy105 D R))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb091_support_mem_0145 (D : Class) (R : Class) :
    (nb091AlphaDummy105 D R) ∈
      (((synCcompl (Class.cab (nb091AlphaDummy119 D R)
              (synWrex (nb091AlphaDummy120 D R) (Class.cv (nb091AlphaDummy106 D R))
                (Wff.classEq (Class.cv (nb091AlphaDummy119 D R))
                  (synCphi (Class.cv (nb091AlphaDummy120 D R)))))))).fv ∪ ((synCcompl
            (Class.cab (nb091AlphaDummy119 D R)
              (synWrex (nb091AlphaDummy120 D R) (Class.cv (nb091AlphaDummy105 D R))
                (Wff.classEq (Class.cv (nb091AlphaDummy119 D R))
                  (synCun (synCphi (Class.cv (nb091AlphaDummy120 D R)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb091AlphaDummy105 D R) ≠ (nb091AlphaDummy119 D R) from (by
          unfold nb091AlphaDummy119;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb091_support_mem_0144 D R) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb091AlphaDummy105 D R) ≠ (nb091AlphaDummy120 D R) from (by
            unfold nb091AlphaDummy120;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb091_support_mem_0144 D R) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb091_support_mem_0146 (R : Class) (p : Var) :
    (nb091AlphaDummy107 R p) ∈
      (((Class.cv (nb091AlphaDummy108 R p))).fv ∪
        ((Class.cv (nb091AlphaDummy107 R p))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb091_support_mem_0147 (R : Class) (p : Var) :
    (nb091AlphaDummy107 R p) ∈
      (((synCcompl (Class.cab (nb091AlphaDummy121 R p)
              (synWrex (nb091AlphaDummy122 R p) (Class.cv (nb091AlphaDummy108 R p))
                (Wff.classEq (Class.cv (nb091AlphaDummy121 R p))
                  (synCphi (Class.cv (nb091AlphaDummy122 R p)))))))).fv ∪ ((synCcompl
            (Class.cab (nb091AlphaDummy121 R p)
              (synWrex (nb091AlphaDummy122 R p) (Class.cv (nb091AlphaDummy107 R p))
                (Wff.classEq (Class.cv (nb091AlphaDummy121 R p))
                  (synCun (synCphi (Class.cv (nb091AlphaDummy122 R p)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb091AlphaDummy107 R p) ≠ (nb091AlphaDummy121 R p) from (by
          unfold nb091AlphaDummy121;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb091_support_mem_0146 R p) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb091AlphaDummy107 R p) ≠ (nb091AlphaDummy122 R p) from (by
            unfold nb091AlphaDummy122;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb091_support_mem_0146 R p) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb091_support_mem_0148 (D : Class) (R : Class) :
    (nb091AlphaDummy105 D R) ∈
      (((Class.cab (nb091AlphaDummy119 D R)
            (synWrex (nb091AlphaDummy120 D R) (Class.cv (nb091AlphaDummy105 D R))
              (Wff.classEq (Class.cv (nb091AlphaDummy119 D R))
                (synCun (synCphi (Class.cv (nb091AlphaDummy120 D R)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb091AlphaDummy119 D R)
            (synWrex (nb091AlphaDummy120 D R) (Class.cv (nb091AlphaDummy105 D R))
              (Wff.classEq (Class.cv (nb091AlphaDummy119 D R))
                (synCun (synCphi (Class.cv (nb091AlphaDummy120 D R)))
                  (synCsn (synC0c))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb091AlphaDummy105 D R) ≠ (nb091AlphaDummy119 D R) from (by
          unfold nb091AlphaDummy119;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb091_support_mem_0144 D R) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb091AlphaDummy105 D R) ≠ (nb091AlphaDummy120 D R) from (by
            unfold nb091AlphaDummy120;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb091_support_mem_0144 D R) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb091_support_mem_0149 (R : Class) (p : Var) :
    (nb091AlphaDummy107 R p) ∈
      (((Class.cab (nb091AlphaDummy121 R p)
            (synWrex (nb091AlphaDummy122 R p) (Class.cv (nb091AlphaDummy107 R p))
              (Wff.classEq (Class.cv (nb091AlphaDummy121 R p))
                (synCun (synCphi (Class.cv (nb091AlphaDummy122 R p)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb091AlphaDummy121 R p)
            (synWrex (nb091AlphaDummy122 R p) (Class.cv (nb091AlphaDummy107 R p))
              (Wff.classEq (Class.cv (nb091AlphaDummy121 R p))
                (synCun (synCphi (Class.cv (nb091AlphaDummy122 R p)))
                  (synCsn (synC0c))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb091AlphaDummy107 R p) ≠ (nb091AlphaDummy121 R p) from (by
          unfold nb091AlphaDummy121;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb091_support_mem_0146 R p) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb091AlphaDummy107 R p) ≠ (nb091AlphaDummy122 R p) from (by
            unfold nb091AlphaDummy122;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb091_support_mem_0146 R p) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb091_support_mem_0150 (D : Class) (R : Class) :
    (nb091AlphaDummy120 D R) ∈
      (((synCcompl (synCphi (Class.cv (nb091AlphaDummy120 D R))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb091_support_mem_0151 (R : Class) (p : Var) :
    (nb091AlphaDummy122 R p) ∈
      (((synCcompl (synCphi (Class.cv (nb091AlphaDummy122 R p))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb091_support_mem_0152 (D : Class) (R : Class) :
    (nb091AlphaDummy120 D R) ∈
      (((synCphi (Class.cv (nb091AlphaDummy120 D R)))).fv ∪
        ((synCphi (Class.cv (nb091AlphaDummy120 D R)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb091_support_mem_0153 (R : Class) (p : Var) :
    (nb091AlphaDummy122 R p) ∈
      (((synCphi (Class.cv (nb091AlphaDummy122 R p)))).fv ∪
        ((synCphi (Class.cv (nb091AlphaDummy122 R p)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb091_support_mem_0154 (D : Class) (R : Class) :
    (nb091AlphaDummy048 D R) ∈ (((Class.cv (nb091AlphaDummy048 D R))).fv) :=
  by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb091_support_mem_0155 (D : Class) (R : Class) (p : Var) :
    (nb091AlphaDummy050 D R p) ∈ (((Class.cv (nb091AlphaDummy050 D R p))).fv) :=
  by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb091_support_mem_0156 (D : Class) (R : Class) :
    (nb091AlphaDummy155 D R) ∈
      (((Wff.classMem (Class.cv (nb091AlphaDummy155 D R)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb091AlphaDummy155 D R)) (synC1c))).fv ∪
        ((Class.cv (nb091AlphaDummy155 D R))).fv) :=
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
    (nb091AlphaDummy157 D R p) ∈
      (((Wff.classMem (Class.cv (nb091AlphaDummy157 D R p)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb091AlphaDummy157 D R p)) (synC1c))).fv ∪
        ((Class.cv (nb091AlphaDummy157 D R p))).fv) :=
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
    (nb091AlphaDummy155 D R) ∈
      (((Class.cv (nb091AlphaDummy155 D R))).fv ∪ ((synC1c)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb091_support_mem_0159 (D : Class) (R : Class) (p : Var) :
    (nb091AlphaDummy157 D R p) ∈
      (((Class.cv (nb091AlphaDummy157 D R p))).fv ∪ ((synC1c)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb091_support_mem_0160 (D : Class) (R : Class) :
    (nb091AlphaDummy162 D R) ∈
      (((synCnin (Class.cv (nb091AlphaDummy162 D R))
            (Class.cv (nb091AlphaDummy163 D R)))).fv ∪
        ((synCnin (Class.cv (nb091AlphaDummy162 D R))
            (Class.cv (nb091AlphaDummy163 D R)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb091_support_mem_0161 (D : Class) (R : Class) (p : Var) :
    (nb091AlphaDummy165 D R p) ∈
      (((synCnin (Class.cv (nb091AlphaDummy165 D R p))
            (Class.cv (nb091AlphaDummy166 D R p)))).fv ∪
        ((synCnin (Class.cv (nb091AlphaDummy165 D R p))
            (Class.cv (nb091AlphaDummy166 D R p)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb091_support_mem_0162 (D : Class) (R : Class) :
    (nb091AlphaDummy162 D R) ∈
      (((Class.cv (nb091AlphaDummy162 D R))).fv ∪
        ((Class.cv (nb091AlphaDummy163 D R))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb091_support_mem_0163 (D : Class) (R : Class) (p : Var) :
    (nb091AlphaDummy165 D R p) ∈
      (((Class.cv (nb091AlphaDummy165 D R p))).fv ∪
        ((Class.cv (nb091AlphaDummy166 D R p))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb091_support_mem_0164 (D : Class) (R : Class) :
    (nb091AlphaDummy163 D R) ∈
      (((synCnin (Class.cv (nb091AlphaDummy162 D R))
            (Class.cv (nb091AlphaDummy163 D R)))).fv ∪
        ((synCnin (Class.cv (nb091AlphaDummy162 D R))
            (Class.cv (nb091AlphaDummy163 D R)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb091_support_mem_0165 (D : Class) (R : Class) (p : Var) :
    (nb091AlphaDummy166 D R p) ∈
      (((synCnin (Class.cv (nb091AlphaDummy165 D R p))
            (Class.cv (nb091AlphaDummy166 D R p)))).fv ∪
        ((synCnin (Class.cv (nb091AlphaDummy165 D R p))
            (Class.cv (nb091AlphaDummy166 D R p)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb091_support_mem_0166 (D : Class) (R : Class) :
    (nb091AlphaDummy163 D R) ∈
      (((Class.cv (nb091AlphaDummy162 D R))).fv ∪
        ((Class.cv (nb091AlphaDummy163 D R))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb091_support_mem_0167 (D : Class) (R : Class) (p : Var) :
    (nb091AlphaDummy166 D R p) ∈
      (((Class.cv (nb091AlphaDummy165 D R p))).fv ∪
        ((Class.cv (nb091AlphaDummy166 D R p))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb091_support_mem_0168 (D : Class) (R : Class) :
    (nb091AlphaDummy162 D R) ∈
      (((synCcompl (Class.cv (nb091AlphaDummy162 D R)))).fv ∪
        ((synCcompl (Class.cv (nb091AlphaDummy163 D R)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb091_support_mem_0169 (D : Class) (R : Class) (p : Var) :
    (nb091AlphaDummy165 D R p) ∈
      (((synCcompl (Class.cv (nb091AlphaDummy165 D R p)))).fv ∪
        ((synCcompl (Class.cv (nb091AlphaDummy166 D R p)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb091_support_mem_0170 (D : Class) (R : Class) :
    (nb091AlphaDummy162 D R) ∈
      (((Class.cv (nb091AlphaDummy162 D R))).fv ∪
        ((Class.cv (nb091AlphaDummy162 D R))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb091_support_mem_0171 (D : Class) (R : Class) (p : Var) :
    (nb091AlphaDummy165 D R p) ∈
      (((Class.cv (nb091AlphaDummy165 D R p))).fv ∪
        ((Class.cv (nb091AlphaDummy165 D R p))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb091_support_mem_0172 (D : Class) (R : Class) :
    (nb091AlphaDummy163 D R) ∈
      (((synCcompl (Class.cv (nb091AlphaDummy162 D R)))).fv ∪
        ((synCcompl (Class.cv (nb091AlphaDummy163 D R)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb091_support_mem_0173 (D : Class) (R : Class) (p : Var) :
    (nb091AlphaDummy166 D R p) ∈
      (((synCcompl (Class.cv (nb091AlphaDummy165 D R p)))).fv ∪
        ((synCcompl (Class.cv (nb091AlphaDummy166 D R p)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb091_support_mem_0174 (D : Class) (R : Class) :
    (nb091AlphaDummy163 D R) ∈
      (((Class.cv (nb091AlphaDummy163 D R))).fv ∪
        ((Class.cv (nb091AlphaDummy163 D R))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb091_support_mem_0175 (D : Class) (R : Class) (p : Var) :
    (nb091AlphaDummy166 D R p) ∈
      (((Class.cv (nb091AlphaDummy166 D R p))).fv ∪
        ((Class.cv (nb091AlphaDummy166 D R p))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb091_support_mem_0176 (D : Class) (R : Class) :
    (nb091AlphaDummy000 D R) ∈
      (((Class.cab (nb091AlphaDummy047 D R) (synWrex (nb091AlphaDummy048 D R) (synCin D
                (synCima (synCcnv (synCdif R (synCid)))
                  (synCsn (synCuni (synCuni (Class.cv (nb091AlphaDummy000 D R)))))))
              (Wff.classEq (Class.cv (nb091AlphaDummy047 D R))
                (synCun (synCphi (Class.cv (nb091AlphaDummy048 D R)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb091AlphaDummy047 D R)
            (synWrex (nb091AlphaDummy048 D R) (synCin D
                (synCima (synCcnv (synCdif R (synCid)))
                  (synCsn (synCuni (synCuni (Class.cv (nb091AlphaDummy000 D R)))))))
              (Wff.classEq (Class.cv (nb091AlphaDummy047 D R))
                (synCun (synCphi (Class.cv (nb091AlphaDummy048 D R)))
                  (synCsn (synC0c))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb091AlphaDummy000 D R) ≠ (nb091AlphaDummy047 D R) from (by
          unfold nb091AlphaDummy047;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb091_support_mem_0090 D R) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb091AlphaDummy000 D R) ≠ (nb091AlphaDummy048 D R) from (by
            unfold nb091AlphaDummy048;
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
      (((Class.cab (nb091AlphaDummy049 D R p) (synWrex (nb091AlphaDummy050 D R p)
              (synCin D (synCima (synCcnv (synCdif R (synCid)))
                  (synCsn (synCuni (synCuni (Class.cv p))))))
              (Wff.classEq (Class.cv (nb091AlphaDummy049 D R p))
                (synCun (synCphi (Class.cv (nb091AlphaDummy050 D R p)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb091AlphaDummy049 D R p)
            (synWrex (nb091AlphaDummy050 D R p) (synCin D
                (synCima (synCcnv (synCdif R (synCid)))
                  (synCsn (synCuni (synCuni (Class.cv p))))))
              (Wff.classEq (Class.cv (nb091AlphaDummy049 D R p))
                (synCun (synCphi (Class.cv (nb091AlphaDummy050 D R p)))
                  (synCsn (synC0c))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show p ≠ (nb091AlphaDummy049 D R p) from (by
          unfold nb091AlphaDummy049;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb091_support_mem_0092 D R p) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show p ≠ (nb091AlphaDummy050 D R p) from (by
            unfold nb091AlphaDummy050;
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
    (nb091AlphaDummy048 D R) ∈
      (((synCcompl (synCphi (Class.cv (nb091AlphaDummy048 D R))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb091_support_mem_0179 (D : Class) (R : Class) (p : Var) :
    (nb091AlphaDummy050 D R p) ∈
      (((synCcompl (synCphi (Class.cv (nb091AlphaDummy050 D R p))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb091_support_mem_0180 (D : Class) (R : Class) :
    (nb091AlphaDummy048 D R) ∈
      (((synCphi (Class.cv (nb091AlphaDummy048 D R)))).fv ∪
        ((synCphi (Class.cv (nb091AlphaDummy048 D R)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb091_support_mem_0181 (D : Class) (R : Class) (p : Var) :
    (nb091AlphaDummy050 D R p) ∈
      (((synCphi (Class.cv (nb091AlphaDummy050 D R p)))).fv ∪
        ((synCphi (Class.cv (nb091AlphaDummy050 D R p)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb091_support_mem_0182 (D : Class) (R : Class) :
    (nb091AlphaDummy042 D R) ∈
      (((Class.cv (nb091AlphaDummy042 D R))).fv ∪
        ((Class.cv (nb091AlphaDummy041 D R))).fv) :=
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
    (nb091AlphaDummy042 D R) ∈
      (((synCcompl (Class.cab (nb091AlphaDummy183 D R)
              (synWrex (nb091AlphaDummy184 D R) (Class.cv (nb091AlphaDummy042 D R))
                (Wff.classEq (Class.cv (nb091AlphaDummy183 D R))
                  (synCphi (Class.cv (nb091AlphaDummy184 D R)))))))).fv ∪ ((synCcompl
            (Class.cab (nb091AlphaDummy183 D R)
              (synWrex (nb091AlphaDummy184 D R) (Class.cv (nb091AlphaDummy041 D R))
                (Wff.classEq (Class.cv (nb091AlphaDummy183 D R))
                  (synCun (synCphi (Class.cv (nb091AlphaDummy184 D R)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb091AlphaDummy042 D R) ≠ (nb091AlphaDummy183 D R) from (by
          unfold nb091AlphaDummy183;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb091_support_mem_0182 D R) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb091AlphaDummy042 D R) ≠ (nb091AlphaDummy184 D R) from (by
            unfold nb091AlphaDummy184;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb091_support_mem_0182 D R) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb091_support_mem_0184 (D : Class) (R : Class) (p : Var) :
    (nb091AlphaDummy044 D R p) ∈
      (((Class.cv (nb091AlphaDummy044 D R p))).fv ∪
        ((Class.cv (nb091AlphaDummy043 D R p))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb091_support_mem_0185 (D : Class) (R : Class) (p : Var) :
    (nb091AlphaDummy044 D R p) ∈
      (((synCcompl (Class.cab (nb091AlphaDummy185 D R p)
              (synWrex (nb091AlphaDummy186 D R p) (Class.cv (nb091AlphaDummy044 D R p))
                (Wff.classEq (Class.cv (nb091AlphaDummy185 D R p))
                  (synCphi (Class.cv (nb091AlphaDummy186 D R p)))))))).fv ∪ ((synCcompl
            (Class.cab (nb091AlphaDummy185 D R p) (synWrex (nb091AlphaDummy186 D R p)
                (Class.cv (nb091AlphaDummy043 D R p))
                (Wff.classEq (Class.cv (nb091AlphaDummy185 D R p))
                  (synCun (synCphi (Class.cv (nb091AlphaDummy186 D R p)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb091AlphaDummy044 D R p) ≠ (nb091AlphaDummy185 D R p) from (by
          unfold nb091AlphaDummy185;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb091_support_mem_0184 D R p) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb091AlphaDummy044 D R p) ≠ (nb091AlphaDummy186 D R p) from (by
            unfold nb091AlphaDummy186;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb091_support_mem_0184 D R p) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb091_support_mem_0186 (D : Class) (R : Class) :
    (nb091AlphaDummy042 D R) ∈
      (((Class.cab (nb091AlphaDummy183 D R)
            (synWrex (nb091AlphaDummy184 D R) (Class.cv (nb091AlphaDummy042 D R))
              (Wff.classEq (Class.cv (nb091AlphaDummy183 D R))
                (synCphi (Class.cv (nb091AlphaDummy184 D R))))))).fv ∪
        ((Class.cab (nb091AlphaDummy183 D R)
            (synWrex (nb091AlphaDummy184 D R) (Class.cv (nb091AlphaDummy042 D R))
              (Wff.classEq (Class.cv (nb091AlphaDummy183 D R))
                (synCphi (Class.cv (nb091AlphaDummy184 D R))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb091AlphaDummy042 D R) ≠ (nb091AlphaDummy183 D R) from (by
          unfold nb091AlphaDummy183;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb091_support_mem_0182 D R) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb091AlphaDummy042 D R) ≠ (nb091AlphaDummy184 D R) from (by
            unfold nb091AlphaDummy184;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb091_support_mem_0182 D R) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb091_support_mem_0187 (D : Class) (R : Class) (p : Var) :
    (nb091AlphaDummy044 D R p) ∈
      (((Class.cab (nb091AlphaDummy185 D R p) (synWrex (nb091AlphaDummy186 D R p)
              (Class.cv (nb091AlphaDummy044 D R p))
              (Wff.classEq (Class.cv (nb091AlphaDummy185 D R p))
                (synCphi (Class.cv (nb091AlphaDummy186 D R p))))))).fv ∪
        ((Class.cab (nb091AlphaDummy185 D R p) (synWrex (nb091AlphaDummy186 D R p)
              (Class.cv (nb091AlphaDummy044 D R p))
              (Wff.classEq (Class.cv (nb091AlphaDummy185 D R p))
                (synCphi (Class.cv (nb091AlphaDummy186 D R p))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb091AlphaDummy044 D R p) ≠ (nb091AlphaDummy185 D R p) from (by
          unfold nb091AlphaDummy185;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb091_support_mem_0184 D R p) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb091AlphaDummy044 D R p) ≠ (nb091AlphaDummy186 D R p) from (by
            unfold nb091AlphaDummy186;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb091_support_mem_0184 D R p) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb091_support_mem_0188 (D : Class) (R : Class) :
    (nb091AlphaDummy184 D R) ∈ (((Class.cv (nb091AlphaDummy184 D R))).fv) :=
  by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb091_support_mem_0189 (D : Class) (R : Class) (p : Var) :
    (nb091AlphaDummy186 D R p) ∈ (((Class.cv (nb091AlphaDummy186 D R p))).fv) :=
  by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb091_support_mem_0190 (D : Class) (R : Class) :
    (nb091AlphaDummy191 D R) ∈
      (((Wff.classMem (Class.cv (nb091AlphaDummy191 D R)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb091AlphaDummy191 D R)) (synC1c))).fv ∪
        ((Class.cv (nb091AlphaDummy191 D R))).fv) :=
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
    (nb091AlphaDummy193 D R p) ∈
      (((Wff.classMem (Class.cv (nb091AlphaDummy193 D R p)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb091AlphaDummy193 D R p)) (synC1c))).fv ∪
        ((Class.cv (nb091AlphaDummy193 D R p))).fv) :=
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
    (nb091AlphaDummy191 D R) ∈
      (((Class.cv (nb091AlphaDummy191 D R))).fv ∪ ((synC1c)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb091_support_mem_0193 (D : Class) (R : Class) (p : Var) :
    (nb091AlphaDummy193 D R p) ∈
      (((Class.cv (nb091AlphaDummy193 D R p))).fv ∪ ((synC1c)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb091_support_mem_0194 (D : Class) (R : Class) :
    (nb091AlphaDummy198 D R) ∈
      (((synCnin (Class.cv (nb091AlphaDummy198 D R))
            (Class.cv (nb091AlphaDummy199 D R)))).fv ∪
        ((synCnin (Class.cv (nb091AlphaDummy198 D R))
            (Class.cv (nb091AlphaDummy199 D R)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb091_support_mem_0195 (D : Class) (R : Class) (p : Var) :
    (nb091AlphaDummy201 D R p) ∈
      (((synCnin (Class.cv (nb091AlphaDummy201 D R p))
            (Class.cv (nb091AlphaDummy202 D R p)))).fv ∪
        ((synCnin (Class.cv (nb091AlphaDummy201 D R p))
            (Class.cv (nb091AlphaDummy202 D R p)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb091_support_mem_0196 (D : Class) (R : Class) :
    (nb091AlphaDummy198 D R) ∈
      (((Class.cv (nb091AlphaDummy198 D R))).fv ∪
        ((Class.cv (nb091AlphaDummy199 D R))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb091_support_mem_0197 (D : Class) (R : Class) (p : Var) :
    (nb091AlphaDummy201 D R p) ∈
      (((Class.cv (nb091AlphaDummy201 D R p))).fv ∪
        ((Class.cv (nb091AlphaDummy202 D R p))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb091_support_mem_0198 (D : Class) (R : Class) :
    (nb091AlphaDummy199 D R) ∈
      (((synCnin (Class.cv (nb091AlphaDummy198 D R))
            (Class.cv (nb091AlphaDummy199 D R)))).fv ∪
        ((synCnin (Class.cv (nb091AlphaDummy198 D R))
            (Class.cv (nb091AlphaDummy199 D R)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb091_support_mem_0199 (D : Class) (R : Class) (p : Var) :
    (nb091AlphaDummy202 D R p) ∈
      (((synCnin (Class.cv (nb091AlphaDummy201 D R p))
            (Class.cv (nb091AlphaDummy202 D R p)))).fv ∪
        ((synCnin (Class.cv (nb091AlphaDummy201 D R p))
            (Class.cv (nb091AlphaDummy202 D R p)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb091_support_mem_0200 (D : Class) (R : Class) :
    (nb091AlphaDummy199 D R) ∈
      (((Class.cv (nb091AlphaDummy198 D R))).fv ∪
        ((Class.cv (nb091AlphaDummy199 D R))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb091_support_mem_0201 (D : Class) (R : Class) (p : Var) :
    (nb091AlphaDummy202 D R p) ∈
      (((Class.cv (nb091AlphaDummy201 D R p))).fv ∪
        ((Class.cv (nb091AlphaDummy202 D R p))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb091_support_mem_0202 (D : Class) (R : Class) :
    (nb091AlphaDummy198 D R) ∈
      (((synCcompl (Class.cv (nb091AlphaDummy198 D R)))).fv ∪
        ((synCcompl (Class.cv (nb091AlphaDummy199 D R)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb091_support_mem_0203 (D : Class) (R : Class) (p : Var) :
    (nb091AlphaDummy201 D R p) ∈
      (((synCcompl (Class.cv (nb091AlphaDummy201 D R p)))).fv ∪
        ((synCcompl (Class.cv (nb091AlphaDummy202 D R p)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb091_support_mem_0204 (D : Class) (R : Class) :
    (nb091AlphaDummy198 D R) ∈
      (((Class.cv (nb091AlphaDummy198 D R))).fv ∪
        ((Class.cv (nb091AlphaDummy198 D R))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb091_support_mem_0205 (D : Class) (R : Class) (p : Var) :
    (nb091AlphaDummy201 D R p) ∈
      (((Class.cv (nb091AlphaDummy201 D R p))).fv ∪
        ((Class.cv (nb091AlphaDummy201 D R p))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb091_support_mem_0206 (D : Class) (R : Class) :
    (nb091AlphaDummy199 D R) ∈
      (((synCcompl (Class.cv (nb091AlphaDummy198 D R)))).fv ∪
        ((synCcompl (Class.cv (nb091AlphaDummy199 D R)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb091_support_mem_0207 (D : Class) (R : Class) (p : Var) :
    (nb091AlphaDummy202 D R p) ∈
      (((synCcompl (Class.cv (nb091AlphaDummy201 D R p)))).fv ∪
        ((synCcompl (Class.cv (nb091AlphaDummy202 D R p)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb091_support_mem_0208 (D : Class) (R : Class) :
    (nb091AlphaDummy199 D R) ∈
      (((Class.cv (nb091AlphaDummy199 D R))).fv ∪
        ((Class.cv (nb091AlphaDummy199 D R))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb091_support_mem_0209 (D : Class) (R : Class) (p : Var) :
    (nb091AlphaDummy202 D R p) ∈
      (((Class.cv (nb091AlphaDummy202 D R p))).fv ∪
        ((Class.cv (nb091AlphaDummy202 D R p))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb091_support_mem_0210 (D : Class) (R : Class) :
    (nb091AlphaDummy041 D R) ∈
      (((Class.cv (nb091AlphaDummy042 D R))).fv ∪
        ((Class.cv (nb091AlphaDummy041 D R))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb091_support_mem_0211 (D : Class) (R : Class) :
    (nb091AlphaDummy041 D R) ∈
      (((synCcompl (Class.cab (nb091AlphaDummy183 D R)
              (synWrex (nb091AlphaDummy184 D R) (Class.cv (nb091AlphaDummy042 D R))
                (Wff.classEq (Class.cv (nb091AlphaDummy183 D R))
                  (synCphi (Class.cv (nb091AlphaDummy184 D R)))))))).fv ∪ ((synCcompl
            (Class.cab (nb091AlphaDummy183 D R)
              (synWrex (nb091AlphaDummy184 D R) (Class.cv (nb091AlphaDummy041 D R))
                (Wff.classEq (Class.cv (nb091AlphaDummy183 D R))
                  (synCun (synCphi (Class.cv (nb091AlphaDummy184 D R)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb091AlphaDummy041 D R) ≠ (nb091AlphaDummy183 D R) from (by
          unfold nb091AlphaDummy183;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb091_support_mem_0210 D R) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb091AlphaDummy041 D R) ≠ (nb091AlphaDummy184 D R) from (by
            unfold nb091AlphaDummy184;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb091_support_mem_0210 D R) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb091_support_mem_0212 (D : Class) (R : Class) (p : Var) :
    (nb091AlphaDummy043 D R p) ∈
      (((Class.cv (nb091AlphaDummy044 D R p))).fv ∪
        ((Class.cv (nb091AlphaDummy043 D R p))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb091_support_mem_0213 (D : Class) (R : Class) (p : Var) :
    (nb091AlphaDummy043 D R p) ∈
      (((synCcompl (Class.cab (nb091AlphaDummy185 D R p)
              (synWrex (nb091AlphaDummy186 D R p) (Class.cv (nb091AlphaDummy044 D R p))
                (Wff.classEq (Class.cv (nb091AlphaDummy185 D R p))
                  (synCphi (Class.cv (nb091AlphaDummy186 D R p)))))))).fv ∪ ((synCcompl
            (Class.cab (nb091AlphaDummy185 D R p) (synWrex (nb091AlphaDummy186 D R p)
                (Class.cv (nb091AlphaDummy043 D R p))
                (Wff.classEq (Class.cv (nb091AlphaDummy185 D R p))
                  (synCun (synCphi (Class.cv (nb091AlphaDummy186 D R p)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb091AlphaDummy043 D R p) ≠ (nb091AlphaDummy185 D R p) from (by
          unfold nb091AlphaDummy185;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb091_support_mem_0212 D R p) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb091AlphaDummy043 D R p) ≠ (nb091AlphaDummy186 D R p) from (by
            unfold nb091AlphaDummy186;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb091_support_mem_0212 D R p) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb091_support_mem_0214 (D : Class) (R : Class) :
    (nb091AlphaDummy041 D R) ∈
      (((Class.cab (nb091AlphaDummy183 D R)
            (synWrex (nb091AlphaDummy184 D R) (Class.cv (nb091AlphaDummy041 D R))
              (Wff.classEq (Class.cv (nb091AlphaDummy183 D R))
                (synCun (synCphi (Class.cv (nb091AlphaDummy184 D R)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb091AlphaDummy183 D R)
            (synWrex (nb091AlphaDummy184 D R) (Class.cv (nb091AlphaDummy041 D R))
              (Wff.classEq (Class.cv (nb091AlphaDummy183 D R))
                (synCun (synCphi (Class.cv (nb091AlphaDummy184 D R)))
                  (synCsn (synC0c))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb091AlphaDummy041 D R) ≠ (nb091AlphaDummy183 D R) from (by
          unfold nb091AlphaDummy183;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb091_support_mem_0210 D R) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb091AlphaDummy041 D R) ≠ (nb091AlphaDummy184 D R) from (by
            unfold nb091AlphaDummy184;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb091_support_mem_0210 D R) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb091_support_mem_0215 (D : Class) (R : Class) (p : Var) :
    (nb091AlphaDummy043 D R p) ∈
      (((Class.cab (nb091AlphaDummy185 D R p) (synWrex (nb091AlphaDummy186 D R p)
              (Class.cv (nb091AlphaDummy043 D R p))
              (Wff.classEq (Class.cv (nb091AlphaDummy185 D R p))
                (synCun (synCphi (Class.cv (nb091AlphaDummy186 D R p)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb091AlphaDummy185 D R p)
            (synWrex (nb091AlphaDummy186 D R p) (Class.cv (nb091AlphaDummy043 D R p))
              (Wff.classEq (Class.cv (nb091AlphaDummy185 D R p))
                (synCun (synCphi (Class.cv (nb091AlphaDummy186 D R p)))
                  (synCsn (synC0c))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb091AlphaDummy043 D R p) ≠ (nb091AlphaDummy185 D R p) from (by
          unfold nb091AlphaDummy185;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb091_support_mem_0212 D R p) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb091AlphaDummy043 D R p) ≠ (nb091AlphaDummy186 D R p) from (by
            unfold nb091AlphaDummy186;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb091_support_mem_0212 D R p) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb091_support_mem_0216 (D : Class) (R : Class) :
    (nb091AlphaDummy184 D R) ∈
      (((synCcompl (synCphi (Class.cv (nb091AlphaDummy184 D R))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb091_support_mem_0217 (D : Class) (R : Class) (p : Var) :
    (nb091AlphaDummy186 D R p) ∈
      (((synCcompl (synCphi (Class.cv (nb091AlphaDummy186 D R p))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb091_support_mem_0218 (D : Class) (R : Class) :
    (nb091AlphaDummy184 D R) ∈
      (((synCphi (Class.cv (nb091AlphaDummy184 D R)))).fv ∪
        ((synCphi (Class.cv (nb091AlphaDummy184 D R)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb091_support_mem_0219 (D : Class) (R : Class) (p : Var) :
    (nb091AlphaDummy186 D R p) ∈
      (((synCphi (Class.cv (nb091AlphaDummy186 D R p)))).fv ∪
        ((synCphi (Class.cv (nb091AlphaDummy186 D R p)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb091_compact_fv_empty_0020 (D : Class) (R : Class) :
    (nb091AlphaDummy001 D R) ∉ (∅ : Finset Var) :=
  by
  intro hmem
  cases hmem

theorem nb091_compact_fv_empty_0021 (D : Class) (R : Class) (p : Var) :
    (nb091AlphaDummy002 D R p) ∉ (∅ : Finset Var) :=
  by
  intro hmem
  cases hmem

theorem nb091_compact_fv_empty_0022 (D : Class) (R : Class) :
    (nb091AlphaDummy000 D R) ∉ (∅ : Finset Var) :=
  by
  intro hmem
  cases hmem

theorem nb091_compact_fv_empty_0023 (p : Var) : p ∉ (∅ : Finset Var) :=
  by
  intro hmem
  cases hmem

theorem nb091_compact_fv_empty_0024 (D : Class) (R : Class) :
    (nb091AlphaDummy003 D R) ∉ (∅ : Finset Var) :=
  by
  intro hmem
  cases hmem

theorem nb091_compact_fv_empty_0025 (D : Class) (R : Class) (p : Var) :
    (nb091AlphaDummy004 D R p) ∉ (∅ : Finset Var) :=
  by
  intro hmem
  cases hmem


end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired
