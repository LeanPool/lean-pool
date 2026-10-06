/-
Copyright (c) 2026 Elliot Glazer and NFNotWPP contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elliot Glazer and NFNotWPP contributors
-/

module

public import LeanPool.NFWeakPartition.Certificates.NAR4C057C001Block001

/-! Nominal proof certificates grouped in dependency order. -/


public section

/-! Certificates from `NAR4C057C001Part005`. -/


section

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

theorem nb057_fresh_322 :
    (nb057AlphaDummy072) ∉
      (((synCnin (Class.cv (nb057AlphaDummy067)) (Class.cv (nb057AlphaDummy068)))).fv ∪
        ((synCnin (Class.cv (nb057AlphaDummy067))
            (Class.cv (nb057AlphaDummy068)))).fv) :=
  by
  simpa only [nb057AlphaDummy072] using
    freshVar_not_mem
      (((synCnin (Class.cv (nb057AlphaDummy067)) (Class.cv (nb057AlphaDummy068)))).fv ∪
        ((synCnin (Class.cv (nb057AlphaDummy067)) (Class.cv (nb057AlphaDummy068)))).fv)
      0

theorem nb057_fresh_323 (f : Var) :
    (nb057AlphaDummy073 f) ∉
      (((synCnin (Class.cv (nb057AlphaDummy070 f))
            (Class.cv (nb057AlphaDummy071 f)))).fv ∪
        ((synCnin (Class.cv (nb057AlphaDummy070 f))
            (Class.cv (nb057AlphaDummy071 f)))).fv) :=
  by
  simpa only [nb057AlphaDummy073] using
    freshVar_not_mem
      (((synCnin (Class.cv (nb057AlphaDummy070 f))
            (Class.cv (nb057AlphaDummy071 f)))).fv ∪
        ((synCnin (Class.cv (nb057AlphaDummy070 f))
            (Class.cv (nb057AlphaDummy071 f)))).fv)
      0

theorem nb057_fresh_324 :
    (nb057AlphaDummy108) ∉
      (((synCnin (Class.cv (nb057AlphaDummy103)) (Class.cv (nb057AlphaDummy104)))).fv ∪
        ((synCnin (Class.cv (nb057AlphaDummy103))
            (Class.cv (nb057AlphaDummy104)))).fv) :=
  by
  simpa only [nb057AlphaDummy108] using
    freshVar_not_mem
      (((synCnin (Class.cv (nb057AlphaDummy103)) (Class.cv (nb057AlphaDummy104)))).fv ∪
        ((synCnin (Class.cv (nb057AlphaDummy103)) (Class.cv (nb057AlphaDummy104)))).fv)
      0

theorem nb057_fresh_325 (f : Var) :
    (nb057AlphaDummy109 f) ∉
      (((synCnin (Class.cv (nb057AlphaDummy106 f))
            (Class.cv (nb057AlphaDummy107 f)))).fv ∪
        ((synCnin (Class.cv (nb057AlphaDummy106 f))
            (Class.cv (nb057AlphaDummy107 f)))).fv) :=
  by
  simpa only [nb057AlphaDummy109] using
    freshVar_not_mem
      (((synCnin (Class.cv (nb057AlphaDummy106 f))
            (Class.cv (nb057AlphaDummy107 f)))).fv ∪
        ((synCnin (Class.cv (nb057AlphaDummy106 f))
            (Class.cv (nb057AlphaDummy107 f)))).fv)
      0

theorem nb057_fresh_326 :
    (nb057AlphaDummy150) ∉
      (((synCnin (Class.cv (nb057AlphaDummy145)) (Class.cv (nb057AlphaDummy146)))).fv ∪
        ((synCnin (Class.cv (nb057AlphaDummy145))
            (Class.cv (nb057AlphaDummy146)))).fv) :=
  by
  simpa only [nb057AlphaDummy150] using
    freshVar_not_mem
      (((synCnin (Class.cv (nb057AlphaDummy145)) (Class.cv (nb057AlphaDummy146)))).fv ∪
        ((synCnin (Class.cv (nb057AlphaDummy145)) (Class.cv (nb057AlphaDummy146)))).fv)
      0

theorem nb057_fresh_327 (f : Var) :
    (nb057AlphaDummy151 f) ∉
      (((synCnin (Class.cv (nb057AlphaDummy148 f))
            (Class.cv (nb057AlphaDummy149 f)))).fv ∪
        ((synCnin (Class.cv (nb057AlphaDummy148 f))
            (Class.cv (nb057AlphaDummy149 f)))).fv) :=
  by
  simpa only [nb057AlphaDummy151] using
    freshVar_not_mem
      (((synCnin (Class.cv (nb057AlphaDummy148 f))
            (Class.cv (nb057AlphaDummy149 f)))).fv ∪
        ((synCnin (Class.cv (nb057AlphaDummy148 f))
            (Class.cv (nb057AlphaDummy149 f)))).fv)
      0

theorem nb057_fresh_328 :
    (nb057AlphaDummy186) ∉
      (((synCnin (Class.cv (nb057AlphaDummy181)) (Class.cv (nb057AlphaDummy182)))).fv ∪
        ((synCnin (Class.cv (nb057AlphaDummy181))
            (Class.cv (nb057AlphaDummy182)))).fv) :=
  by
  simpa only [nb057AlphaDummy186] using
    freshVar_not_mem
      (((synCnin (Class.cv (nb057AlphaDummy181)) (Class.cv (nb057AlphaDummy182)))).fv ∪
        ((synCnin (Class.cv (nb057AlphaDummy181)) (Class.cv (nb057AlphaDummy182)))).fv)
      0

theorem nb057_fresh_329 (f : Var) :
    (nb057AlphaDummy187 f) ∉
      (((synCnin (Class.cv (nb057AlphaDummy184 f))
            (Class.cv (nb057AlphaDummy185 f)))).fv ∪
        ((synCnin (Class.cv (nb057AlphaDummy184 f))
            (Class.cv (nb057AlphaDummy185 f)))).fv) :=
  by
  simpa only [nb057AlphaDummy187] using
    freshVar_not_mem
      (((synCnin (Class.cv (nb057AlphaDummy184 f))
            (Class.cv (nb057AlphaDummy185 f)))).fv ∪
        ((synCnin (Class.cv (nb057AlphaDummy184 f))
            (Class.cv (nb057AlphaDummy185 f)))).fv)
      0

theorem nb057_fresh_330 :
    (nb057AlphaDummy222) ∉
      (((synCnin (Class.cv (nb057AlphaDummy217)) (Class.cv (nb057AlphaDummy218)))).fv ∪
        ((synCnin (Class.cv (nb057AlphaDummy217))
            (Class.cv (nb057AlphaDummy218)))).fv) :=
  by
  simpa only [nb057AlphaDummy222] using
    freshVar_not_mem
      (((synCnin (Class.cv (nb057AlphaDummy217)) (Class.cv (nb057AlphaDummy218)))).fv ∪
        ((synCnin (Class.cv (nb057AlphaDummy217)) (Class.cv (nb057AlphaDummy218)))).fv)
      0

theorem nb057_fresh_331 (f : Var) :
    (nb057AlphaDummy223 f) ∉
      (((synCnin (Class.cv (nb057AlphaDummy220 f))
            (Class.cv (nb057AlphaDummy221 f)))).fv ∪
        ((synCnin (Class.cv (nb057AlphaDummy220 f))
            (Class.cv (nb057AlphaDummy221 f)))).fv) :=
  by
  simpa only [nb057AlphaDummy223] using
    freshVar_not_mem
      (((synCnin (Class.cv (nb057AlphaDummy220 f))
            (Class.cv (nb057AlphaDummy221 f)))).fv ∪
        ((synCnin (Class.cv (nb057AlphaDummy220 f))
            (Class.cv (nb057AlphaDummy221 f)))).fv)
      0

theorem nb057_fresh_332 :
    (nb057AlphaDummy262) ∉
      (((synCnin (Class.cv (nb057AlphaDummy257)) (Class.cv (nb057AlphaDummy258)))).fv ∪
        ((synCnin (Class.cv (nb057AlphaDummy257))
            (Class.cv (nb057AlphaDummy258)))).fv) :=
  by
  simpa only [nb057AlphaDummy262] using
    freshVar_not_mem
      (((synCnin (Class.cv (nb057AlphaDummy257)) (Class.cv (nb057AlphaDummy258)))).fv ∪
        ((synCnin (Class.cv (nb057AlphaDummy257)) (Class.cv (nb057AlphaDummy258)))).fv)
      0

theorem nb057_fresh_333 (f : Var) :
    (nb057AlphaDummy263 f) ∉
      (((synCnin (Class.cv (nb057AlphaDummy260 f))
            (Class.cv (nb057AlphaDummy261 f)))).fv ∪
        ((synCnin (Class.cv (nb057AlphaDummy260 f))
            (Class.cv (nb057AlphaDummy261 f)))).fv) :=
  by
  simpa only [nb057AlphaDummy263] using
    freshVar_not_mem
      (((synCnin (Class.cv (nb057AlphaDummy260 f))
            (Class.cv (nb057AlphaDummy261 f)))).fv ∪
        ((synCnin (Class.cv (nb057AlphaDummy260 f))
            (Class.cv (nb057AlphaDummy261 f)))).fv)
      0

theorem nb057_fresh_334 :
    (nb057AlphaDummy040) ∉
      (((synCnin (synCcom (Class.cv (nb057AlphaDummy001))
              (synCcnv (Class.cv (nb057AlphaDummy001)))) (synCid))).fv ∪ ((synCnin
            (synCcom (Class.cv (nb057AlphaDummy001))
              (synCcnv (Class.cv (nb057AlphaDummy001)))) (synCid))).fv) :=
  by
  simpa only [nb057AlphaDummy040] using
    freshVar_not_mem
      (((synCnin (synCcom (Class.cv (nb057AlphaDummy001))
              (synCcnv (Class.cv (nb057AlphaDummy001)))) (synCid))).fv ∪ ((synCnin
            (synCcom (Class.cv (nb057AlphaDummy001))
              (synCcnv (Class.cv (nb057AlphaDummy001)))) (synCid))).fv)
      0

theorem nb057_fresh_335 (f : Var) :
    (nb057AlphaDummy041 f) ∉
      (((synCnin (synCcom (Class.cv f) (synCcnv (Class.cv f))) (synCid))).fv ∪
        ((synCnin (synCcom (Class.cv f) (synCcnv (Class.cv f))) (synCid))).fv) :=
  by
  simpa only [nb057AlphaDummy041] using
    freshVar_not_mem
      (((synCnin (synCcom (Class.cv f) (synCcnv (Class.cv f))) (synCid))).fv ∪
        ((synCnin (synCcom (Class.cv f) (synCcnv (Class.cv f))) (synCid))).fv)
      0

theorem nb057_fresh_336 :
    (nb057AlphaDummy038) ∉
      (((synCphi (Class.cv (nb057AlphaDummy005)))).fv ∪
        ((synCphi (Class.cv (nb057AlphaDummy005)))).fv) :=
  by
  simpa only [nb057AlphaDummy038] using
    freshVar_not_mem
      (((synCphi (Class.cv (nb057AlphaDummy005)))).fv ∪
        ((synCphi (Class.cv (nb057AlphaDummy005)))).fv)
      0

theorem nb057_fresh_337 (f : Var) (a : Var) :
    (nb057AlphaDummy039 f a) ∉
      (((synCphi (Class.cv (nb057AlphaDummy007 f a)))).fv ∪
        ((synCphi (Class.cv (nb057AlphaDummy007 f a)))).fv) :=
  by
  simpa only [nb057AlphaDummy039] using
    freshVar_not_mem
      (((synCphi (Class.cv (nb057AlphaDummy007 f a)))).fv ∪
        ((synCphi (Class.cv (nb057AlphaDummy007 f a)))).fv)
      0

theorem nb057_fresh_338 :
    (nb057AlphaDummy086) ∉
      (((synCphi (Class.cv (nb057AlphaDummy053)))).fv ∪
        ((synCphi (Class.cv (nb057AlphaDummy053)))).fv) :=
  by
  simpa only [nb057AlphaDummy086] using
    freshVar_not_mem
      (((synCphi (Class.cv (nb057AlphaDummy053)))).fv ∪
        ((synCphi (Class.cv (nb057AlphaDummy053)))).fv)
      0

theorem nb057_fresh_339 (f : Var) :
    (nb057AlphaDummy087 f) ∉
      (((synCphi (Class.cv (nb057AlphaDummy055 f)))).fv ∪
        ((synCphi (Class.cv (nb057AlphaDummy055 f)))).fv) :=
  by
  simpa only [nb057AlphaDummy087] using
    freshVar_not_mem
      (((synCphi (Class.cv (nb057AlphaDummy055 f)))).fv ∪
        ((synCphi (Class.cv (nb057AlphaDummy055 f)))).fv)
      0

theorem nb057_fresh_340 :
    (nb057AlphaDummy122) ∉
      (((synCphi (Class.cv (nb057AlphaDummy089)))).fv ∪
        ((synCphi (Class.cv (nb057AlphaDummy089)))).fv) :=
  by
  simpa only [nb057AlphaDummy122] using
    freshVar_not_mem
      (((synCphi (Class.cv (nb057AlphaDummy089)))).fv ∪
        ((synCphi (Class.cv (nb057AlphaDummy089)))).fv)
      0

theorem nb057_fresh_341 (f : Var) :
    (nb057AlphaDummy123 f) ∉
      (((synCphi (Class.cv (nb057AlphaDummy091 f)))).fv ∪
        ((synCphi (Class.cv (nb057AlphaDummy091 f)))).fv) :=
  by
  simpa only [nb057AlphaDummy123] using
    freshVar_not_mem
      (((synCphi (Class.cv (nb057AlphaDummy091 f)))).fv ∪
        ((synCphi (Class.cv (nb057AlphaDummy091 f)))).fv)
      0

theorem nb057_fresh_342 :
    (nb057AlphaDummy164) ∉
      (((synCphi (Class.cv (nb057AlphaDummy131)))).fv ∪
        ((synCphi (Class.cv (nb057AlphaDummy131)))).fv) :=
  by
  simpa only [nb057AlphaDummy164] using
    freshVar_not_mem
      (((synCphi (Class.cv (nb057AlphaDummy131)))).fv ∪
        ((synCphi (Class.cv (nb057AlphaDummy131)))).fv)
      0

theorem nb057_fresh_343 (f : Var) :
    (nb057AlphaDummy165 f) ∉
      (((synCphi (Class.cv (nb057AlphaDummy133 f)))).fv ∪
        ((synCphi (Class.cv (nb057AlphaDummy133 f)))).fv) :=
  by
  simpa only [nb057AlphaDummy165] using
    freshVar_not_mem
      (((synCphi (Class.cv (nb057AlphaDummy133 f)))).fv ∪
        ((synCphi (Class.cv (nb057AlphaDummy133 f)))).fv)
      0

theorem nb057_fresh_344 :
    (nb057AlphaDummy200) ∉
      (((synCphi (Class.cv (nb057AlphaDummy167)))).fv ∪
        ((synCphi (Class.cv (nb057AlphaDummy167)))).fv) :=
  by
  simpa only [nb057AlphaDummy200] using
    freshVar_not_mem
      (((synCphi (Class.cv (nb057AlphaDummy167)))).fv ∪
        ((synCphi (Class.cv (nb057AlphaDummy167)))).fv)
      0

theorem nb057_fresh_345 (f : Var) :
    (nb057AlphaDummy201 f) ∉
      (((synCphi (Class.cv (nb057AlphaDummy169 f)))).fv ∪
        ((synCphi (Class.cv (nb057AlphaDummy169 f)))).fv) :=
  by
  simpa only [nb057AlphaDummy201] using
    freshVar_not_mem
      (((synCphi (Class.cv (nb057AlphaDummy169 f)))).fv ∪
        ((synCphi (Class.cv (nb057AlphaDummy169 f)))).fv)
      0

theorem nb057_fresh_346 :
    (nb057AlphaDummy236) ∉
      (((synCphi (Class.cv (nb057AlphaDummy203)))).fv ∪
        ((synCphi (Class.cv (nb057AlphaDummy203)))).fv) :=
  by
  simpa only [nb057AlphaDummy236] using
    freshVar_not_mem
      (((synCphi (Class.cv (nb057AlphaDummy203)))).fv ∪
        ((synCphi (Class.cv (nb057AlphaDummy203)))).fv)
      0

theorem nb057_fresh_347 (f : Var) :
    (nb057AlphaDummy237 f) ∉
      (((synCphi (Class.cv (nb057AlphaDummy205 f)))).fv ∪
        ((synCphi (Class.cv (nb057AlphaDummy205 f)))).fv) :=
  by
  simpa only [nb057AlphaDummy237] using
    freshVar_not_mem
      (((synCphi (Class.cv (nb057AlphaDummy205 f)))).fv ∪
        ((synCphi (Class.cv (nb057AlphaDummy205 f)))).fv)
      0

theorem nb057_fresh_348 :
    (nb057AlphaDummy276) ∉
      (((synCphi (Class.cv (nb057AlphaDummy243)))).fv ∪
        ((synCphi (Class.cv (nb057AlphaDummy243)))).fv) :=
  by
  simpa only [nb057AlphaDummy276] using
    freshVar_not_mem
      (((synCphi (Class.cv (nb057AlphaDummy243)))).fv ∪
        ((synCphi (Class.cv (nb057AlphaDummy243)))).fv)
      0

theorem nb057_fresh_349 (f : Var) :
    (nb057AlphaDummy277 f) ∉
      (((synCphi (Class.cv (nb057AlphaDummy245 f)))).fv ∪
        ((synCphi (Class.cv (nb057AlphaDummy245 f)))).fv) :=
  by
  simpa only [nb057AlphaDummy277] using
    freshVar_not_mem
      (((synCphi (Class.cv (nb057AlphaDummy245 f)))).fv ∪
        ((synCphi (Class.cv (nb057AlphaDummy245 f)))).fv)
      0

theorem nb057_fresh_350 :
    (nb057AlphaDummy002) ∉
      (({(nb057AlphaDummy001)} : Finset Var) ∪ ({(nb057AlphaDummy000)} : Finset Var) ∪
        ((synWfn (Class.cv (nb057AlphaDummy001)) (Class.cv (nb057AlphaDummy000)))).fv) :=
  by
  simpa only [nb057AlphaDummy002] using
    freshVar_not_mem
      (({(nb057AlphaDummy001)} : Finset Var) ∪ ({(nb057AlphaDummy000)} : Finset Var) ∪
        ((synWfn (Class.cv (nb057AlphaDummy001)) (Class.cv (nb057AlphaDummy000)))).fv)
      0

theorem nb057_fresh_351 :
    (nb057AlphaDummy050) ∉
      (({(nb057AlphaDummy044)} : Finset Var) ∪ ({(nb057AlphaDummy045)} : Finset Var) ∪
        ((synWex (nb057AlphaDummy046) (synWa (synWbr (Class.cv (nb057AlphaDummy044))
                (synCcnv (Class.cv (nb057AlphaDummy001)))
                (Class.cv (nb057AlphaDummy046))) (synWbr (Class.cv (nb057AlphaDummy046))
                (Class.cv (nb057AlphaDummy001)) (Class.cv (nb057AlphaDummy045)))))).fv) :=
  by
  simpa only [nb057AlphaDummy050] using
    freshVar_not_mem
      (({(nb057AlphaDummy044)} : Finset Var) ∪ ({(nb057AlphaDummy045)} : Finset Var) ∪
        ((synWex (nb057AlphaDummy046) (synWa (synWbr (Class.cv (nb057AlphaDummy044))
                (synCcnv (Class.cv (nb057AlphaDummy001)))
                (Class.cv (nb057AlphaDummy046))) (synWbr (Class.cv (nb057AlphaDummy046))
                (Class.cv (nb057AlphaDummy001)) (Class.cv (nb057AlphaDummy045)))))).fv)
      0

theorem nb057_fresh_352 (f : Var) :
    (nb057AlphaDummy051 f) ∉
      (({(nb057AlphaDummy047 f)} : Finset Var) ∪ ({(nb057AlphaDummy048 f)} : Finset Var) ∪
        ((synWex (nb057AlphaDummy049 f) (synWa
              (synWbr (Class.cv (nb057AlphaDummy047 f)) (synCcnv (Class.cv f))
                (Class.cv (nb057AlphaDummy049 f)))
              (synWbr (Class.cv (nb057AlphaDummy049 f)) (Class.cv f)
                (Class.cv (nb057AlphaDummy048 f)))))).fv) :=
  by
  simpa only [nb057AlphaDummy051] using
    freshVar_not_mem
      (({(nb057AlphaDummy047 f)} : Finset Var) ∪ ({(nb057AlphaDummy048 f)} : Finset Var) ∪
        ((synWex (nb057AlphaDummy049 f) (synWa
              (synWbr (Class.cv (nb057AlphaDummy047 f)) (synCcnv (Class.cv f))
                (Class.cv (nb057AlphaDummy049 f)))
              (synWbr (Class.cv (nb057AlphaDummy049 f)) (Class.cv f)
                (Class.cv (nb057AlphaDummy048 f)))))).fv)
      0

theorem nb057_fresh_353 :
    (nb057AlphaDummy128) ∉
      (({(nb057AlphaDummy124)} : Finset Var) ∪ ({(nb057AlphaDummy125)} : Finset Var) ∪
        ((synWbr (Class.cv (nb057AlphaDummy125)) (Class.cv (nb057AlphaDummy001))
            (Class.cv (nb057AlphaDummy124)))).fv) :=
  by
  simpa only [nb057AlphaDummy128] using
    freshVar_not_mem
      (({(nb057AlphaDummy124)} : Finset Var) ∪ ({(nb057AlphaDummy125)} : Finset Var) ∪
        ((synWbr (Class.cv (nb057AlphaDummy125)) (Class.cv (nb057AlphaDummy001))
            (Class.cv (nb057AlphaDummy124)))).fv)
      0

theorem nb057_fresh_354 (f : Var) :
    (nb057AlphaDummy129 f) ∉
      (({(nb057AlphaDummy126 f)} : Finset Var) ∪ ({(nb057AlphaDummy127 f)} : Finset Var) ∪
        ((synWbr (Class.cv (nb057AlphaDummy127 f)) (Class.cv f)
            (Class.cv (nb057AlphaDummy126 f)))).fv) :=
  by
  simpa only [nb057AlphaDummy129] using
    freshVar_not_mem
      (({(nb057AlphaDummy126 f)} : Finset Var) ∪ ({(nb057AlphaDummy127 f)} : Finset Var) ∪
        ((synWbr (Class.cv (nb057AlphaDummy127 f)) (Class.cv f)
            (Class.cv (nb057AlphaDummy126 f)))).fv)
      0

theorem nb057_fresh_355 (f : Var) (a : Var) :
    (nb057AlphaDummy003 f a) ∉
      (({ f } : Finset Var) ∪ ({ a } : Finset Var) ∪
        ((synWfn (Class.cv f) (Class.cv a))).fv) :=
  by
  simpa only [nb057AlphaDummy003] using
    freshVar_not_mem
      (({ f } : Finset Var) ∪ ({ a } : Finset Var) ∪ ((synWfn (Class.cv f) (Class.cv a))).fv)
      0

theorem nb057_fresh_356 : (nb057AlphaDummy000) ∉ ((∅ : Finset Var)) := by
  simpa only [nb057AlphaDummy000] using freshVar_not_mem ((∅ : Finset Var)) 0

theorem nb057_fresh_357 : (nb057AlphaDummy001) ∉ ((∅ : Finset Var)) := by
  simpa only [nb057AlphaDummy001] using freshVar_not_mem ((∅ : Finset Var)) 1

theorem nb057_distinct_358 : (nb057AlphaDummy000) ≠ (nb057AlphaDummy001) := by
  simpa only [nb057AlphaDummy000, nb057AlphaDummy001] using
    (freshVar_injective ((∅ : Finset Var)) (i := 0) (j := 1) (by decide))

theorem nb057_support_mem_0000 :
    (nb057AlphaDummy001) ∈
      (({(nb057AlphaDummy001)} : Finset Var) ∪ ({(nb057AlphaDummy000)} : Finset Var) ∪
        ((synWfn (Class.cv (nb057AlphaDummy001)) (Class.cv (nb057AlphaDummy000)))).fv) :=
  by
  with_reducible
    refine
      Finset.mem_union_left (a := (nb057AlphaDummy001)) (s :=
        ({(nb057AlphaDummy001)} : Finset Var) ∪ ({(nb057AlphaDummy000)} : Finset Var))
        (((synWfn (Class.cv (nb057AlphaDummy001)) (Class.cv (nb057AlphaDummy000)))).fv)
        ?_
  with_reducible rw [Finset.mem_union]
  left
  exact Finset.mem_singleton_self _

theorem nb057_support_mem_0001 (f : Var) (a : Var) :
    f ∈
      (({ f } : Finset Var) ∪ ({ a } : Finset Var) ∪
        ((synWfn (Class.cv f) (Class.cv a))).fv) :=
  by
  with_reducible
    refine
      Finset.mem_union_left (a := f) (s := ({ f } : Finset Var) ∪ ({ a } : Finset Var))
        (((synWfn (Class.cv f) (Class.cv a))).fv) ?_
  with_reducible rw [Finset.mem_union]
  left
  exact Finset.mem_singleton_self _

theorem nb057_support_mem_0002 :
    (nb057AlphaDummy000) ∈
      (({(nb057AlphaDummy001)} : Finset Var) ∪ ({(nb057AlphaDummy000)} : Finset Var) ∪
        ((synWfn (Class.cv (nb057AlphaDummy001)) (Class.cv (nb057AlphaDummy000)))).fv) :=
  by
  with_reducible
    refine
      Finset.mem_union_left (a := (nb057AlphaDummy000)) (s :=
        ({(nb057AlphaDummy001)} : Finset Var) ∪ ({(nb057AlphaDummy000)} : Finset Var))
        (((synWfn (Class.cv (nb057AlphaDummy001)) (Class.cv (nb057AlphaDummy000)))).fv)
        ?_
  with_reducible rw [Finset.mem_union]
  right
  exact Finset.mem_singleton_self _

theorem nb057_support_mem_0003 (f : Var) (a : Var) :
    a ∈
      (({ f } : Finset Var) ∪ ({ a } : Finset Var) ∪
        ((synWfn (Class.cv f) (Class.cv a))).fv) :=
  by
  with_reducible
    refine
      Finset.mem_union_left (a := a) (s := ({ f } : Finset Var) ∪ ({ a } : Finset Var))
        (((synWfn (Class.cv f) (Class.cv a))).fv) ?_
  with_reducible rw [Finset.mem_union]
  right
  exact Finset.mem_singleton_self _

theorem nb057_support_mem_0004 :
    (nb057AlphaDummy001) ∈
      (((Class.cv (nb057AlphaDummy001))).fv ∪ ((Class.cv (nb057AlphaDummy000))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb057_support_mem_0005 :
    (nb057AlphaDummy001) ∈
      (((synCcompl (Class.cab (nb057AlphaDummy004)
              (synWrex (nb057AlphaDummy005) (Class.cv (nb057AlphaDummy001))
                (Wff.classEq (Class.cv (nb057AlphaDummy004))
                  (synCphi (Class.cv (nb057AlphaDummy005)))))))).fv ∪ ((synCcompl
            (Class.cab (nb057AlphaDummy004)
              (synWrex (nb057AlphaDummy005) (Class.cv (nb057AlphaDummy000))
                (Wff.classEq (Class.cv (nb057AlphaDummy004))
                  (synCun (synCphi (Class.cv (nb057AlphaDummy005)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0004) 0))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0004) 1))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb057_support_mem_0006 (f : Var) (a : Var) :
    f ∈ (((Class.cv f)).fv ∪ ((Class.cv a)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb057_support_mem_0007 (f : Var) (a : Var) :
    f ∈
      (((synCcompl (Class.cab (nb057AlphaDummy006 f a)
              (synWrex (nb057AlphaDummy007 f a) (Class.cv f)
                (Wff.classEq (Class.cv (nb057AlphaDummy006 f a))
                  (synCphi (Class.cv (nb057AlphaDummy007 f a)))))))).fv ∪ ((synCcompl
            (Class.cab (nb057AlphaDummy006 f a)
              (synWrex (nb057AlphaDummy007 f a) (Class.cv a)
                (Wff.classEq (Class.cv (nb057AlphaDummy006 f a))
                  (synCun (synCphi (Class.cv (nb057AlphaDummy007 f a)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0006 f a) 0))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0006 f a) 1))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb057_support_mem_0008 :
    (nb057AlphaDummy001) ∈
      (((Class.cab (nb057AlphaDummy004)
            (synWrex (nb057AlphaDummy005) (Class.cv (nb057AlphaDummy001))
              (Wff.classEq (Class.cv (nb057AlphaDummy004))
                (synCphi (Class.cv (nb057AlphaDummy005))))))).fv ∪
        ((Class.cab (nb057AlphaDummy004)
            (synWrex (nb057AlphaDummy005) (Class.cv (nb057AlphaDummy001))
              (Wff.classEq (Class.cv (nb057AlphaDummy004))
                (synCphi (Class.cv (nb057AlphaDummy005))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0004) 0))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0004) 1))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb057_support_mem_0009 (f : Var) (a : Var) :
    f ∈
      (((Class.cab (nb057AlphaDummy006 f a)
            (synWrex (nb057AlphaDummy007 f a) (Class.cv f)
              (Wff.classEq (Class.cv (nb057AlphaDummy006 f a))
                (synCphi (Class.cv (nb057AlphaDummy007 f a))))))).fv ∪
        ((Class.cab (nb057AlphaDummy006 f a)
            (synWrex (nb057AlphaDummy007 f a) (Class.cv f)
              (Wff.classEq (Class.cv (nb057AlphaDummy006 f a))
                (synCphi (Class.cv (nb057AlphaDummy007 f a))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0006 f a) 0))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0006 f a) 1))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb057_support_mem_0010 :
    (nb057AlphaDummy005) ∈ (((Class.cv (nb057AlphaDummy005))).fv) :=
  by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb057_support_mem_0011 (f : Var) (a : Var) :
    (nb057AlphaDummy007 f a) ∈ (((Class.cv (nb057AlphaDummy007 f a))).fv) :=
  by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb057_support_mem_0012 :
    (nb057AlphaDummy012) ∈
      (((Wff.classMem (Class.cv (nb057AlphaDummy012)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb057AlphaDummy012)) (synC1c))).fv ∪
        ((Class.cv (nb057AlphaDummy012))).fv) :=
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

theorem nb057_support_mem_0013 (f : Var) (a : Var) :
    (nb057AlphaDummy014 f a) ∈
      (((Wff.classMem (Class.cv (nb057AlphaDummy014 f a)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb057AlphaDummy014 f a)) (synC1c))).fv ∪
        ((Class.cv (nb057AlphaDummy014 f a))).fv) :=
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

theorem nb057_support_mem_0014 :
    (nb057AlphaDummy012) ∈
      (((Class.cv (nb057AlphaDummy012))).fv ∪ ((synC1c)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb057_support_mem_0015 (f : Var) (a : Var) :
    (nb057AlphaDummy014 f a) ∈
      (((Class.cv (nb057AlphaDummy014 f a))).fv ∪ ((synC1c)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb057_support_mem_0016 :
    (nb057AlphaDummy019) ∈
      (((synCnin (Class.cv (nb057AlphaDummy019)) (Class.cv (nb057AlphaDummy020)))).fv ∪
        ((synCnin (Class.cv (nb057AlphaDummy019))
            (Class.cv (nb057AlphaDummy020)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb057_support_mem_0017 (f : Var) (a : Var) :
    (nb057AlphaDummy022 f a) ∈
      (((synCnin (Class.cv (nb057AlphaDummy022 f a))
            (Class.cv (nb057AlphaDummy023 f a)))).fv ∪
        ((synCnin (Class.cv (nb057AlphaDummy022 f a))
            (Class.cv (nb057AlphaDummy023 f a)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb057_support_mem_0018 :
    (nb057AlphaDummy019) ∈
      (((Class.cv (nb057AlphaDummy019))).fv ∪ ((Class.cv (nb057AlphaDummy020))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb057_support_mem_0019 (f : Var) (a : Var) :
    (nb057AlphaDummy022 f a) ∈
      (((Class.cv (nb057AlphaDummy022 f a))).fv ∪
        ((Class.cv (nb057AlphaDummy023 f a))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb057_support_mem_0020 :
    (nb057AlphaDummy020) ∈
      (((synCnin (Class.cv (nb057AlphaDummy019)) (Class.cv (nb057AlphaDummy020)))).fv ∪
        ((synCnin (Class.cv (nb057AlphaDummy019))
            (Class.cv (nb057AlphaDummy020)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb057_support_mem_0021 (f : Var) (a : Var) :
    (nb057AlphaDummy023 f a) ∈
      (((synCnin (Class.cv (nb057AlphaDummy022 f a))
            (Class.cv (nb057AlphaDummy023 f a)))).fv ∪
        ((synCnin (Class.cv (nb057AlphaDummy022 f a))
            (Class.cv (nb057AlphaDummy023 f a)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb057_support_mem_0022 :
    (nb057AlphaDummy020) ∈
      (((Class.cv (nb057AlphaDummy019))).fv ∪ ((Class.cv (nb057AlphaDummy020))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb057_support_mem_0023 (f : Var) (a : Var) :
    (nb057AlphaDummy023 f a) ∈
      (((Class.cv (nb057AlphaDummy022 f a))).fv ∪
        ((Class.cv (nb057AlphaDummy023 f a))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb057_support_mem_0024 :
    (nb057AlphaDummy019) ∈
      (((synCcompl (Class.cv (nb057AlphaDummy019)))).fv ∪
        ((synCcompl (Class.cv (nb057AlphaDummy020)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb057_support_mem_0025 (f : Var) (a : Var) :
    (nb057AlphaDummy022 f a) ∈
      (((synCcompl (Class.cv (nb057AlphaDummy022 f a)))).fv ∪
        ((synCcompl (Class.cv (nb057AlphaDummy023 f a)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb057_support_mem_0026 :
    (nb057AlphaDummy019) ∈
      (((Class.cv (nb057AlphaDummy019))).fv ∪ ((Class.cv (nb057AlphaDummy019))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb057_support_mem_0027 (f : Var) (a : Var) :
    (nb057AlphaDummy022 f a) ∈
      (((Class.cv (nb057AlphaDummy022 f a))).fv ∪
        ((Class.cv (nb057AlphaDummy022 f a))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb057_support_mem_0028 :
    (nb057AlphaDummy020) ∈
      (((synCcompl (Class.cv (nb057AlphaDummy019)))).fv ∪
        ((synCcompl (Class.cv (nb057AlphaDummy020)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb057_support_mem_0029 (f : Var) (a : Var) :
    (nb057AlphaDummy023 f a) ∈
      (((synCcompl (Class.cv (nb057AlphaDummy022 f a)))).fv ∪
        ((synCcompl (Class.cv (nb057AlphaDummy023 f a)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb057_support_mem_0030 :
    (nb057AlphaDummy020) ∈
      (((Class.cv (nb057AlphaDummy020))).fv ∪ ((Class.cv (nb057AlphaDummy020))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb057_support_mem_0031 (f : Var) (a : Var) :
    (nb057AlphaDummy023 f a) ∈
      (((Class.cv (nb057AlphaDummy023 f a))).fv ∪
        ((Class.cv (nb057AlphaDummy023 f a))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb057_support_mem_0032 :
    (nb057AlphaDummy000) ∈
      (((Class.cv (nb057AlphaDummy001))).fv ∪ ((Class.cv (nb057AlphaDummy000))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb057_support_mem_0033 :
    (nb057AlphaDummy000) ∈
      (((synCcompl (Class.cab (nb057AlphaDummy004)
              (synWrex (nb057AlphaDummy005) (Class.cv (nb057AlphaDummy001))
                (Wff.classEq (Class.cv (nb057AlphaDummy004))
                  (synCphi (Class.cv (nb057AlphaDummy005)))))))).fv ∪ ((synCcompl
            (Class.cab (nb057AlphaDummy004)
              (synWrex (nb057AlphaDummy005) (Class.cv (nb057AlphaDummy000))
                (Wff.classEq (Class.cv (nb057AlphaDummy004))
                  (synCun (synCphi (Class.cv (nb057AlphaDummy005)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0032) 0))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0032) 1))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb057_support_mem_0034 (f : Var) (a : Var) :
    a ∈ (((Class.cv f)).fv ∪ ((Class.cv a)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb057_support_mem_0035 (f : Var) (a : Var) :
    a ∈
      (((synCcompl (Class.cab (nb057AlphaDummy006 f a)
              (synWrex (nb057AlphaDummy007 f a) (Class.cv f)
                (Wff.classEq (Class.cv (nb057AlphaDummy006 f a))
                  (synCphi (Class.cv (nb057AlphaDummy007 f a)))))))).fv ∪ ((synCcompl
            (Class.cab (nb057AlphaDummy006 f a)
              (synWrex (nb057AlphaDummy007 f a) (Class.cv a)
                (Wff.classEq (Class.cv (nb057AlphaDummy006 f a))
                  (synCun (synCphi (Class.cv (nb057AlphaDummy007 f a)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0034 f a) 0))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0034 f a) 1))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb057_support_mem_0036 :
    (nb057AlphaDummy000) ∈
      (((Class.cab (nb057AlphaDummy004)
            (synWrex (nb057AlphaDummy005) (Class.cv (nb057AlphaDummy000))
              (Wff.classEq (Class.cv (nb057AlphaDummy004))
                (synCun (synCphi (Class.cv (nb057AlphaDummy005)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb057AlphaDummy004)
            (synWrex (nb057AlphaDummy005) (Class.cv (nb057AlphaDummy000))
              (Wff.classEq (Class.cv (nb057AlphaDummy004))
                (synCun (synCphi (Class.cv (nb057AlphaDummy005)))
                  (synCsn (synC0c))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0032) 0))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0032) 1))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb057_support_mem_0037 (f : Var) (a : Var) :
    a ∈
      (((Class.cab (nb057AlphaDummy006 f a)
            (synWrex (nb057AlphaDummy007 f a) (Class.cv a)
              (Wff.classEq (Class.cv (nb057AlphaDummy006 f a))
                (synCun (synCphi (Class.cv (nb057AlphaDummy007 f a)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb057AlphaDummy006 f a)
            (synWrex (nb057AlphaDummy007 f a) (Class.cv a)
              (Wff.classEq (Class.cv (nb057AlphaDummy006 f a))
                (synCun (synCphi (Class.cv (nb057AlphaDummy007 f a)))
                  (synCsn (synC0c))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0034 f a) 0))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0034 f a) 1))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb057_support_mem_0038 :
    (nb057AlphaDummy005) ∈
      (((synCcompl (synCphi (Class.cv (nb057AlphaDummy005))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb057_support_mem_0039 (f : Var) (a : Var) :
    (nb057AlphaDummy007 f a) ∈
      (((synCcompl (synCphi (Class.cv (nb057AlphaDummy007 f a))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb057_support_mem_0040 :
    (nb057AlphaDummy005) ∈
      (((synCphi (Class.cv (nb057AlphaDummy005)))).fv ∪
        ((synCphi (Class.cv (nb057AlphaDummy005)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb057_support_mem_0041 (f : Var) (a : Var) :
    (nb057AlphaDummy007 f a) ∈
      (((synCphi (Class.cv (nb057AlphaDummy007 f a)))).fv ∪
        ((synCphi (Class.cv (nb057AlphaDummy007 f a)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb057_support_mem_0042 :
    (nb057AlphaDummy044) ∈
      (({(nb057AlphaDummy044)} : Finset Var) ∪ ({(nb057AlphaDummy045)} : Finset Var) ∪
        ((synWex (nb057AlphaDummy046) (synWa (synWbr (Class.cv (nb057AlphaDummy044))
                (synCcnv (Class.cv (nb057AlphaDummy001)))
                (Class.cv (nb057AlphaDummy046))) (synWbr (Class.cv (nb057AlphaDummy046))
                (Class.cv (nb057AlphaDummy001)) (Class.cv (nb057AlphaDummy045)))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  with_reducible rw [Finset.mem_union]
  left
  exact Finset.mem_singleton_self _

theorem nb057_support_mem_0043 (f : Var) :
    (nb057AlphaDummy047 f) ∈
      (({(nb057AlphaDummy047 f)} : Finset Var) ∪ ({(nb057AlphaDummy048 f)} : Finset Var) ∪
        ((synWex (nb057AlphaDummy049 f) (synWa
              (synWbr (Class.cv (nb057AlphaDummy047 f)) (synCcnv (Class.cv f))
                (Class.cv (nb057AlphaDummy049 f)))
              (synWbr (Class.cv (nb057AlphaDummy049 f)) (Class.cv f)
                (Class.cv (nb057AlphaDummy048 f)))))).fv) :=
  by
  with_reducible
    refine
      Finset.mem_union_left (a := (nb057AlphaDummy047 f)) (s :=
        ({(nb057AlphaDummy047 f)} : Finset Var) ∪ ({(nb057AlphaDummy048 f)} : Finset Var))
        (((synWex (nb057AlphaDummy049 f) (synWa
              (synWbr (Class.cv (nb057AlphaDummy047 f)) (synCcnv (Class.cv f))
                (Class.cv (nb057AlphaDummy049 f)))
              (synWbr (Class.cv (nb057AlphaDummy049 f)) (Class.cv f)
                (Class.cv (nb057AlphaDummy048 f)))))).fv)
        ?_
  with_reducible rw [Finset.mem_union]
  left
  exact Finset.mem_singleton_self _

theorem nb057_support_mem_0044 :
    (nb057AlphaDummy045) ∈
      (({(nb057AlphaDummy044)} : Finset Var) ∪ ({(nb057AlphaDummy045)} : Finset Var) ∪
        ((synWex (nb057AlphaDummy046) (synWa (synWbr (Class.cv (nb057AlphaDummy044))
                (synCcnv (Class.cv (nb057AlphaDummy001)))
                (Class.cv (nb057AlphaDummy046))) (synWbr (Class.cv (nb057AlphaDummy046))
                (Class.cv (nb057AlphaDummy001)) (Class.cv (nb057AlphaDummy045)))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  with_reducible rw [Finset.mem_union]
  right
  exact Finset.mem_singleton_self _

theorem nb057_support_mem_0045 (f : Var) :
    (nb057AlphaDummy048 f) ∈
      (({(nb057AlphaDummy047 f)} : Finset Var) ∪ ({(nb057AlphaDummy048 f)} : Finset Var) ∪
        ((synWex (nb057AlphaDummy049 f) (synWa
              (synWbr (Class.cv (nb057AlphaDummy047 f)) (synCcnv (Class.cv f))
                (Class.cv (nb057AlphaDummy049 f)))
              (synWbr (Class.cv (nb057AlphaDummy049 f)) (Class.cv f)
                (Class.cv (nb057AlphaDummy048 f)))))).fv) :=
  by
  with_reducible
    refine
      Finset.mem_union_left (a := (nb057AlphaDummy048 f)) (s :=
        ({(nb057AlphaDummy047 f)} : Finset Var) ∪ ({(nb057AlphaDummy048 f)} : Finset Var))
        (((synWex (nb057AlphaDummy049 f) (synWa
              (synWbr (Class.cv (nb057AlphaDummy047 f)) (synCcnv (Class.cv f))
                (Class.cv (nb057AlphaDummy049 f)))
              (synWbr (Class.cv (nb057AlphaDummy049 f)) (Class.cv f)
                (Class.cv (nb057AlphaDummy048 f)))))).fv)
        ?_
  with_reducible rw [Finset.mem_union]
  right
  exact Finset.mem_singleton_self _

theorem nb057_support_mem_0046 :
    (nb057AlphaDummy044) ∈
      (((Class.cv (nb057AlphaDummy044))).fv ∪ ((Class.cv (nb057AlphaDummy045))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb057_support_mem_0047 :
    (nb057AlphaDummy044) ∈
      (((synCcompl (Class.cab (nb057AlphaDummy052)
              (synWrex (nb057AlphaDummy053) (Class.cv (nb057AlphaDummy044))
                (Wff.classEq (Class.cv (nb057AlphaDummy052))
                  (synCphi (Class.cv (nb057AlphaDummy053)))))))).fv ∪ ((synCcompl
            (Class.cab (nb057AlphaDummy052)
              (synWrex (nb057AlphaDummy053) (Class.cv (nb057AlphaDummy045))
                (Wff.classEq (Class.cv (nb057AlphaDummy052))
                  (synCun (synCphi (Class.cv (nb057AlphaDummy053)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0046) 0))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0046) 1))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb057_support_mem_0048 (f : Var) :
    (nb057AlphaDummy047 f) ∈
      (((Class.cv (nb057AlphaDummy047 f))).fv ∪ ((Class.cv (nb057AlphaDummy048 f))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb057_support_mem_0049 (f : Var) :
    (nb057AlphaDummy047 f) ∈
      (((synCcompl (Class.cab (nb057AlphaDummy054 f)
              (synWrex (nb057AlphaDummy055 f) (Class.cv (nb057AlphaDummy047 f))
                (Wff.classEq (Class.cv (nb057AlphaDummy054 f))
                  (synCphi (Class.cv (nb057AlphaDummy055 f)))))))).fv ∪ ((synCcompl
            (Class.cab (nb057AlphaDummy054 f)
              (synWrex (nb057AlphaDummy055 f) (Class.cv (nb057AlphaDummy048 f))
                (Wff.classEq (Class.cv (nb057AlphaDummy054 f))
                  (synCun (synCphi (Class.cv (nb057AlphaDummy055 f)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0048 f) 0))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0048 f) 1))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb057_support_mem_0050 :
    (nb057AlphaDummy044) ∈
      (((Class.cab (nb057AlphaDummy052)
            (synWrex (nb057AlphaDummy053) (Class.cv (nb057AlphaDummy044))
              (Wff.classEq (Class.cv (nb057AlphaDummy052))
                (synCphi (Class.cv (nb057AlphaDummy053))))))).fv ∪
        ((Class.cab (nb057AlphaDummy052)
            (synWrex (nb057AlphaDummy053) (Class.cv (nb057AlphaDummy044))
              (Wff.classEq (Class.cv (nb057AlphaDummy052))
                (synCphi (Class.cv (nb057AlphaDummy053))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0046) 0))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0046) 1))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb057_support_mem_0051 (f : Var) :
    (nb057AlphaDummy047 f) ∈
      (((Class.cab (nb057AlphaDummy054 f)
            (synWrex (nb057AlphaDummy055 f) (Class.cv (nb057AlphaDummy047 f))
              (Wff.classEq (Class.cv (nb057AlphaDummy054 f))
                (synCphi (Class.cv (nb057AlphaDummy055 f))))))).fv ∪
        ((Class.cab (nb057AlphaDummy054 f)
            (synWrex (nb057AlphaDummy055 f) (Class.cv (nb057AlphaDummy047 f))
              (Wff.classEq (Class.cv (nb057AlphaDummy054 f))
                (synCphi (Class.cv (nb057AlphaDummy055 f))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0048 f) 0))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0048 f) 1))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb057_support_mem_0052 :
    (nb057AlphaDummy053) ∈ (((Class.cv (nb057AlphaDummy053))).fv) :=
  by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb057_support_mem_0053 (f : Var) :
    (nb057AlphaDummy055 f) ∈ (((Class.cv (nb057AlphaDummy055 f))).fv) :=
  by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb057_support_mem_0054 :
    (nb057AlphaDummy060) ∈
      (((Wff.classMem (Class.cv (nb057AlphaDummy060)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb057AlphaDummy060)) (synC1c))).fv ∪
        ((Class.cv (nb057AlphaDummy060))).fv) :=
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

theorem nb057_support_mem_0055 (f : Var) :
    (nb057AlphaDummy062 f) ∈
      (((Wff.classMem (Class.cv (nb057AlphaDummy062 f)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb057AlphaDummy062 f)) (synC1c))).fv ∪
        ((Class.cv (nb057AlphaDummy062 f))).fv) :=
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

theorem nb057_support_mem_0056 :
    (nb057AlphaDummy060) ∈
      (((Class.cv (nb057AlphaDummy060))).fv ∪ ((synC1c)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb057_support_mem_0057 (f : Var) :
    (nb057AlphaDummy062 f) ∈
      (((Class.cv (nb057AlphaDummy062 f))).fv ∪ ((synC1c)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb057_support_mem_0058 :
    (nb057AlphaDummy067) ∈
      (((synCnin (Class.cv (nb057AlphaDummy067)) (Class.cv (nb057AlphaDummy068)))).fv ∪
        ((synCnin (Class.cv (nb057AlphaDummy067))
            (Class.cv (nb057AlphaDummy068)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb057_support_mem_0059 (f : Var) :
    (nb057AlphaDummy070 f) ∈
      (((synCnin (Class.cv (nb057AlphaDummy070 f))
            (Class.cv (nb057AlphaDummy071 f)))).fv ∪
        ((synCnin (Class.cv (nb057AlphaDummy070 f))
            (Class.cv (nb057AlphaDummy071 f)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb057_support_mem_0060 :
    (nb057AlphaDummy067) ∈
      (((Class.cv (nb057AlphaDummy067))).fv ∪ ((Class.cv (nb057AlphaDummy068))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb057_support_mem_0061 (f : Var) :
    (nb057AlphaDummy070 f) ∈
      (((Class.cv (nb057AlphaDummy070 f))).fv ∪ ((Class.cv (nb057AlphaDummy071 f))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb057_support_mem_0062 :
    (nb057AlphaDummy068) ∈
      (((synCnin (Class.cv (nb057AlphaDummy067)) (Class.cv (nb057AlphaDummy068)))).fv ∪
        ((synCnin (Class.cv (nb057AlphaDummy067))
            (Class.cv (nb057AlphaDummy068)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb057_support_mem_0063 (f : Var) :
    (nb057AlphaDummy071 f) ∈
      (((synCnin (Class.cv (nb057AlphaDummy070 f))
            (Class.cv (nb057AlphaDummy071 f)))).fv ∪
        ((synCnin (Class.cv (nb057AlphaDummy070 f))
            (Class.cv (nb057AlphaDummy071 f)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb057_support_mem_0064 :
    (nb057AlphaDummy068) ∈
      (((Class.cv (nb057AlphaDummy067))).fv ∪ ((Class.cv (nb057AlphaDummy068))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb057_support_mem_0065 (f : Var) :
    (nb057AlphaDummy071 f) ∈
      (((Class.cv (nb057AlphaDummy070 f))).fv ∪ ((Class.cv (nb057AlphaDummy071 f))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb057_support_mem_0066 :
    (nb057AlphaDummy067) ∈
      (((synCcompl (Class.cv (nb057AlphaDummy067)))).fv ∪
        ((synCcompl (Class.cv (nb057AlphaDummy068)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb057_support_mem_0067 (f : Var) :
    (nb057AlphaDummy070 f) ∈
      (((synCcompl (Class.cv (nb057AlphaDummy070 f)))).fv ∪
        ((synCcompl (Class.cv (nb057AlphaDummy071 f)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb057_support_mem_0068 :
    (nb057AlphaDummy067) ∈
      (((Class.cv (nb057AlphaDummy067))).fv ∪ ((Class.cv (nb057AlphaDummy067))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb057_support_mem_0069 (f : Var) :
    (nb057AlphaDummy070 f) ∈
      (((Class.cv (nb057AlphaDummy070 f))).fv ∪ ((Class.cv (nb057AlphaDummy070 f))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb057_support_mem_0070 :
    (nb057AlphaDummy068) ∈
      (((synCcompl (Class.cv (nb057AlphaDummy067)))).fv ∪
        ((synCcompl (Class.cv (nb057AlphaDummy068)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb057_support_mem_0071 (f : Var) :
    (nb057AlphaDummy071 f) ∈
      (((synCcompl (Class.cv (nb057AlphaDummy070 f)))).fv ∪
        ((synCcompl (Class.cv (nb057AlphaDummy071 f)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb057_support_mem_0072 :
    (nb057AlphaDummy068) ∈
      (((Class.cv (nb057AlphaDummy068))).fv ∪ ((Class.cv (nb057AlphaDummy068))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb057_support_mem_0073 (f : Var) :
    (nb057AlphaDummy071 f) ∈
      (((Class.cv (nb057AlphaDummy071 f))).fv ∪ ((Class.cv (nb057AlphaDummy071 f))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb057_support_mem_0074 :
    (nb057AlphaDummy045) ∈
      (((Class.cv (nb057AlphaDummy044))).fv ∪ ((Class.cv (nb057AlphaDummy045))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb057_support_mem_0075 :
    (nb057AlphaDummy045) ∈
      (((synCcompl (Class.cab (nb057AlphaDummy052)
              (synWrex (nb057AlphaDummy053) (Class.cv (nb057AlphaDummy044))
                (Wff.classEq (Class.cv (nb057AlphaDummy052))
                  (synCphi (Class.cv (nb057AlphaDummy053)))))))).fv ∪ ((synCcompl
            (Class.cab (nb057AlphaDummy052)
              (synWrex (nb057AlphaDummy053) (Class.cv (nb057AlphaDummy045))
                (Wff.classEq (Class.cv (nb057AlphaDummy052))
                  (synCun (synCphi (Class.cv (nb057AlphaDummy053)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0074) 0))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0074) 1))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb057_support_mem_0076 (f : Var) :
    (nb057AlphaDummy048 f) ∈
      (((Class.cv (nb057AlphaDummy047 f))).fv ∪ ((Class.cv (nb057AlphaDummy048 f))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb057_support_mem_0077 (f : Var) :
    (nb057AlphaDummy048 f) ∈
      (((synCcompl (Class.cab (nb057AlphaDummy054 f)
              (synWrex (nb057AlphaDummy055 f) (Class.cv (nb057AlphaDummy047 f))
                (Wff.classEq (Class.cv (nb057AlphaDummy054 f))
                  (synCphi (Class.cv (nb057AlphaDummy055 f)))))))).fv ∪ ((synCcompl
            (Class.cab (nb057AlphaDummy054 f)
              (synWrex (nb057AlphaDummy055 f) (Class.cv (nb057AlphaDummy048 f))
                (Wff.classEq (Class.cv (nb057AlphaDummy054 f))
                  (synCun (synCphi (Class.cv (nb057AlphaDummy055 f)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0076 f) 0))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0076 f) 1))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb057_support_mem_0078 :
    (nb057AlphaDummy045) ∈
      (((Class.cab (nb057AlphaDummy052)
            (synWrex (nb057AlphaDummy053) (Class.cv (nb057AlphaDummy045))
              (Wff.classEq (Class.cv (nb057AlphaDummy052))
                (synCun (synCphi (Class.cv (nb057AlphaDummy053)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb057AlphaDummy052)
            (synWrex (nb057AlphaDummy053) (Class.cv (nb057AlphaDummy045))
              (Wff.classEq (Class.cv (nb057AlphaDummy052))
                (synCun (synCphi (Class.cv (nb057AlphaDummy053)))
                  (synCsn (synC0c))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0074) 0))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0074) 1))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb057_support_mem_0079 (f : Var) :
    (nb057AlphaDummy048 f) ∈
      (((Class.cab (nb057AlphaDummy054 f)
            (synWrex (nb057AlphaDummy055 f) (Class.cv (nb057AlphaDummy048 f))
              (Wff.classEq (Class.cv (nb057AlphaDummy054 f))
                (synCun (synCphi (Class.cv (nb057AlphaDummy055 f)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb057AlphaDummy054 f)
            (synWrex (nb057AlphaDummy055 f) (Class.cv (nb057AlphaDummy048 f))
              (Wff.classEq (Class.cv (nb057AlphaDummy054 f))
                (synCun (synCphi (Class.cv (nb057AlphaDummy055 f)))
                  (synCsn (synC0c))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0076 f) 0))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0076 f) 1))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb057_support_mem_0080 :
    (nb057AlphaDummy053) ∈
      (((synCcompl (synCphi (Class.cv (nb057AlphaDummy053))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb057_support_mem_0081 (f : Var) :
    (nb057AlphaDummy055 f) ∈
      (((synCcompl (synCphi (Class.cv (nb057AlphaDummy055 f))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb057_support_mem_0082 :
    (nb057AlphaDummy053) ∈
      (((synCphi (Class.cv (nb057AlphaDummy053)))).fv ∪
        ((synCphi (Class.cv (nb057AlphaDummy053)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb057_support_mem_0083 (f : Var) :
    (nb057AlphaDummy055 f) ∈
      (((synCphi (Class.cv (nb057AlphaDummy055 f)))).fv ∪
        ((synCphi (Class.cv (nb057AlphaDummy055 f)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb057_support_mem_0084 :
    (nb057AlphaDummy044) ∈
      (((Class.cv (nb057AlphaDummy044))).fv ∪ ((Class.cv (nb057AlphaDummy046))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb057_support_mem_0085 :
    (nb057AlphaDummy044) ∈
      (((synCcompl (Class.cab (nb057AlphaDummy088)
              (synWrex (nb057AlphaDummy089) (Class.cv (nb057AlphaDummy044))
                (Wff.classEq (Class.cv (nb057AlphaDummy088))
                  (synCphi (Class.cv (nb057AlphaDummy089)))))))).fv ∪ ((synCcompl
            (Class.cab (nb057AlphaDummy088)
              (synWrex (nb057AlphaDummy089) (Class.cv (nb057AlphaDummy046))
                (Wff.classEq (Class.cv (nb057AlphaDummy088))
                  (synCun (synCphi (Class.cv (nb057AlphaDummy089)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0084) 0))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0084) 1))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb057_support_mem_0086 (f : Var) :
    (nb057AlphaDummy047 f) ∈
      (((Class.cv (nb057AlphaDummy047 f))).fv ∪ ((Class.cv (nb057AlphaDummy049 f))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb057_support_mem_0087 (f : Var) :
    (nb057AlphaDummy047 f) ∈
      (((synCcompl (Class.cab (nb057AlphaDummy090 f)
              (synWrex (nb057AlphaDummy091 f) (Class.cv (nb057AlphaDummy047 f))
                (Wff.classEq (Class.cv (nb057AlphaDummy090 f))
                  (synCphi (Class.cv (nb057AlphaDummy091 f)))))))).fv ∪ ((synCcompl
            (Class.cab (nb057AlphaDummy090 f)
              (synWrex (nb057AlphaDummy091 f) (Class.cv (nb057AlphaDummy049 f))
                (Wff.classEq (Class.cv (nb057AlphaDummy090 f))
                  (synCun (synCphi (Class.cv (nb057AlphaDummy091 f)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0086 f) 0))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0086 f) 1))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb057_support_mem_0088 :
    (nb057AlphaDummy044) ∈
      (((Class.cab (nb057AlphaDummy088)
            (synWrex (nb057AlphaDummy089) (Class.cv (nb057AlphaDummy044))
              (Wff.classEq (Class.cv (nb057AlphaDummy088))
                (synCphi (Class.cv (nb057AlphaDummy089))))))).fv ∪
        ((Class.cab (nb057AlphaDummy088)
            (synWrex (nb057AlphaDummy089) (Class.cv (nb057AlphaDummy044))
              (Wff.classEq (Class.cv (nb057AlphaDummy088))
                (synCphi (Class.cv (nb057AlphaDummy089))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0084) 0))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0084) 1))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb057_support_mem_0089 (f : Var) :
    (nb057AlphaDummy047 f) ∈
      (((Class.cab (nb057AlphaDummy090 f)
            (synWrex (nb057AlphaDummy091 f) (Class.cv (nb057AlphaDummy047 f))
              (Wff.classEq (Class.cv (nb057AlphaDummy090 f))
                (synCphi (Class.cv (nb057AlphaDummy091 f))))))).fv ∪
        ((Class.cab (nb057AlphaDummy090 f)
            (synWrex (nb057AlphaDummy091 f) (Class.cv (nb057AlphaDummy047 f))
              (Wff.classEq (Class.cv (nb057AlphaDummy090 f))
                (synCphi (Class.cv (nb057AlphaDummy091 f))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0086 f) 0))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0086 f) 1))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb057_support_mem_0090 :
    (nb057AlphaDummy089) ∈ (((Class.cv (nb057AlphaDummy089))).fv) :=
  by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb057_support_mem_0091 (f : Var) :
    (nb057AlphaDummy091 f) ∈ (((Class.cv (nb057AlphaDummy091 f))).fv) :=
  by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb057_support_mem_0092 :
    (nb057AlphaDummy096) ∈
      (((Wff.classMem (Class.cv (nb057AlphaDummy096)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb057AlphaDummy096)) (synC1c))).fv ∪
        ((Class.cv (nb057AlphaDummy096))).fv) :=
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

theorem nb057_support_mem_0093 (f : Var) :
    (nb057AlphaDummy098 f) ∈
      (((Wff.classMem (Class.cv (nb057AlphaDummy098 f)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb057AlphaDummy098 f)) (synC1c))).fv ∪
        ((Class.cv (nb057AlphaDummy098 f))).fv) :=
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

theorem nb057_support_mem_0094 :
    (nb057AlphaDummy096) ∈
      (((Class.cv (nb057AlphaDummy096))).fv ∪ ((synC1c)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb057_support_mem_0095 (f : Var) :
    (nb057AlphaDummy098 f) ∈
      (((Class.cv (nb057AlphaDummy098 f))).fv ∪ ((synC1c)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb057_support_mem_0096 :
    (nb057AlphaDummy103) ∈
      (((synCnin (Class.cv (nb057AlphaDummy103)) (Class.cv (nb057AlphaDummy104)))).fv ∪
        ((synCnin (Class.cv (nb057AlphaDummy103))
            (Class.cv (nb057AlphaDummy104)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb057_support_mem_0097 (f : Var) :
    (nb057AlphaDummy106 f) ∈
      (((synCnin (Class.cv (nb057AlphaDummy106 f))
            (Class.cv (nb057AlphaDummy107 f)))).fv ∪
        ((synCnin (Class.cv (nb057AlphaDummy106 f))
            (Class.cv (nb057AlphaDummy107 f)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb057_support_mem_0098 :
    (nb057AlphaDummy103) ∈
      (((Class.cv (nb057AlphaDummy103))).fv ∪ ((Class.cv (nb057AlphaDummy104))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb057_support_mem_0099 (f : Var) :
    (nb057AlphaDummy106 f) ∈
      (((Class.cv (nb057AlphaDummy106 f))).fv ∪ ((Class.cv (nb057AlphaDummy107 f))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb057_support_mem_0100 :
    (nb057AlphaDummy104) ∈
      (((synCnin (Class.cv (nb057AlphaDummy103)) (Class.cv (nb057AlphaDummy104)))).fv ∪
        ((synCnin (Class.cv (nb057AlphaDummy103))
            (Class.cv (nb057AlphaDummy104)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb057_support_mem_0101 (f : Var) :
    (nb057AlphaDummy107 f) ∈
      (((synCnin (Class.cv (nb057AlphaDummy106 f))
            (Class.cv (nb057AlphaDummy107 f)))).fv ∪
        ((synCnin (Class.cv (nb057AlphaDummy106 f))
            (Class.cv (nb057AlphaDummy107 f)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb057_support_mem_0102 :
    (nb057AlphaDummy104) ∈
      (((Class.cv (nb057AlphaDummy103))).fv ∪ ((Class.cv (nb057AlphaDummy104))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired

end

/-! Certificates from `NAR4C057C001Part006`. -/


section

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

theorem nb057_support_mem_0103 (f : Var) :
    (nb057AlphaDummy107 f) ∈
      (((Class.cv (nb057AlphaDummy106 f))).fv ∪ ((Class.cv (nb057AlphaDummy107 f))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb057_support_mem_0104 :
    (nb057AlphaDummy103) ∈
      (((synCcompl (Class.cv (nb057AlphaDummy103)))).fv ∪
        ((synCcompl (Class.cv (nb057AlphaDummy104)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb057_support_mem_0105 (f : Var) :
    (nb057AlphaDummy106 f) ∈
      (((synCcompl (Class.cv (nb057AlphaDummy106 f)))).fv ∪
        ((synCcompl (Class.cv (nb057AlphaDummy107 f)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb057_support_mem_0106 :
    (nb057AlphaDummy103) ∈
      (((Class.cv (nb057AlphaDummy103))).fv ∪ ((Class.cv (nb057AlphaDummy103))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb057_support_mem_0107 (f : Var) :
    (nb057AlphaDummy106 f) ∈
      (((Class.cv (nb057AlphaDummy106 f))).fv ∪ ((Class.cv (nb057AlphaDummy106 f))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb057_support_mem_0108 :
    (nb057AlphaDummy104) ∈
      (((synCcompl (Class.cv (nb057AlphaDummy103)))).fv ∪
        ((synCcompl (Class.cv (nb057AlphaDummy104)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb057_support_mem_0109 (f : Var) :
    (nb057AlphaDummy107 f) ∈
      (((synCcompl (Class.cv (nb057AlphaDummy106 f)))).fv ∪
        ((synCcompl (Class.cv (nb057AlphaDummy107 f)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb057_support_mem_0110 :
    (nb057AlphaDummy104) ∈
      (((Class.cv (nb057AlphaDummy104))).fv ∪ ((Class.cv (nb057AlphaDummy104))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb057_support_mem_0111 (f : Var) :
    (nb057AlphaDummy107 f) ∈
      (((Class.cv (nb057AlphaDummy107 f))).fv ∪ ((Class.cv (nb057AlphaDummy107 f))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb057_support_mem_0112 :
    (nb057AlphaDummy046) ∈
      (((Class.cv (nb057AlphaDummy044))).fv ∪ ((Class.cv (nb057AlphaDummy046))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb057_support_mem_0113 :
    (nb057AlphaDummy046) ∈
      (((synCcompl (Class.cab (nb057AlphaDummy088)
              (synWrex (nb057AlphaDummy089) (Class.cv (nb057AlphaDummy044))
                (Wff.classEq (Class.cv (nb057AlphaDummy088))
                  (synCphi (Class.cv (nb057AlphaDummy089)))))))).fv ∪ ((synCcompl
            (Class.cab (nb057AlphaDummy088)
              (synWrex (nb057AlphaDummy089) (Class.cv (nb057AlphaDummy046))
                (Wff.classEq (Class.cv (nb057AlphaDummy088))
                  (synCun (synCphi (Class.cv (nb057AlphaDummy089)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0112) 0))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0112) 1))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb057_support_mem_0114 (f : Var) :
    (nb057AlphaDummy049 f) ∈
      (((Class.cv (nb057AlphaDummy047 f))).fv ∪ ((Class.cv (nb057AlphaDummy049 f))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb057_support_mem_0115 (f : Var) :
    (nb057AlphaDummy049 f) ∈
      (((synCcompl (Class.cab (nb057AlphaDummy090 f)
              (synWrex (nb057AlphaDummy091 f) (Class.cv (nb057AlphaDummy047 f))
                (Wff.classEq (Class.cv (nb057AlphaDummy090 f))
                  (synCphi (Class.cv (nb057AlphaDummy091 f)))))))).fv ∪ ((synCcompl
            (Class.cab (nb057AlphaDummy090 f)
              (synWrex (nb057AlphaDummy091 f) (Class.cv (nb057AlphaDummy049 f))
                (Wff.classEq (Class.cv (nb057AlphaDummy090 f))
                  (synCun (synCphi (Class.cv (nb057AlphaDummy091 f)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0114 f) 0))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0114 f) 1))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb057_support_mem_0116 :
    (nb057AlphaDummy046) ∈
      (((Class.cab (nb057AlphaDummy088)
            (synWrex (nb057AlphaDummy089) (Class.cv (nb057AlphaDummy046))
              (Wff.classEq (Class.cv (nb057AlphaDummy088))
                (synCun (synCphi (Class.cv (nb057AlphaDummy089)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb057AlphaDummy088)
            (synWrex (nb057AlphaDummy089) (Class.cv (nb057AlphaDummy046))
              (Wff.classEq (Class.cv (nb057AlphaDummy088))
                (synCun (synCphi (Class.cv (nb057AlphaDummy089)))
                  (synCsn (synC0c))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0112) 0))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0112) 1))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb057_support_mem_0117 (f : Var) :
    (nb057AlphaDummy049 f) ∈
      (((Class.cab (nb057AlphaDummy090 f)
            (synWrex (nb057AlphaDummy091 f) (Class.cv (nb057AlphaDummy049 f))
              (Wff.classEq (Class.cv (nb057AlphaDummy090 f))
                (synCun (synCphi (Class.cv (nb057AlphaDummy091 f)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb057AlphaDummy090 f)
            (synWrex (nb057AlphaDummy091 f) (Class.cv (nb057AlphaDummy049 f))
              (Wff.classEq (Class.cv (nb057AlphaDummy090 f))
                (synCun (synCphi (Class.cv (nb057AlphaDummy091 f)))
                  (synCsn (synC0c))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0114 f) 0))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0114 f) 1))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb057_support_mem_0118 :
    (nb057AlphaDummy089) ∈
      (((synCcompl (synCphi (Class.cv (nb057AlphaDummy089))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb057_support_mem_0119 (f : Var) :
    (nb057AlphaDummy091 f) ∈
      (((synCcompl (synCphi (Class.cv (nb057AlphaDummy091 f))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb057_support_mem_0120 :
    (nb057AlphaDummy089) ∈
      (((synCphi (Class.cv (nb057AlphaDummy089)))).fv ∪
        ((synCphi (Class.cv (nb057AlphaDummy089)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb057_support_mem_0121 (f : Var) :
    (nb057AlphaDummy091 f) ∈
      (((synCphi (Class.cv (nb057AlphaDummy091 f)))).fv ∪
        ((synCphi (Class.cv (nb057AlphaDummy091 f)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb057_support_mem_0122 :
    (nb057AlphaDummy124) ∈
      (({(nb057AlphaDummy124)} : Finset Var) ∪ ({(nb057AlphaDummy125)} : Finset Var) ∪
        ((synWbr (Class.cv (nb057AlphaDummy125)) (Class.cv (nb057AlphaDummy001))
            (Class.cv (nb057AlphaDummy124)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  with_reducible rw [Finset.mem_union]
  left
  exact Finset.mem_singleton_self _

theorem nb057_support_mem_0123 (f : Var) :
    (nb057AlphaDummy126 f) ∈
      (({(nb057AlphaDummy126 f)} : Finset Var) ∪ ({(nb057AlphaDummy127 f)} : Finset Var) ∪
        ((synWbr (Class.cv (nb057AlphaDummy127 f)) (Class.cv f)
            (Class.cv (nb057AlphaDummy126 f)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  with_reducible rw [Finset.mem_union]
  left
  exact Finset.mem_singleton_self _

theorem nb057_support_mem_0124 :
    (nb057AlphaDummy125) ∈
      (({(nb057AlphaDummy124)} : Finset Var) ∪ ({(nb057AlphaDummy125)} : Finset Var) ∪
        ((synWbr (Class.cv (nb057AlphaDummy125)) (Class.cv (nb057AlphaDummy001))
            (Class.cv (nb057AlphaDummy124)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  with_reducible rw [Finset.mem_union]
  right
  exact Finset.mem_singleton_self _

theorem nb057_support_mem_0125 (f : Var) :
    (nb057AlphaDummy127 f) ∈
      (({(nb057AlphaDummy126 f)} : Finset Var) ∪ ({(nb057AlphaDummy127 f)} : Finset Var) ∪
        ((synWbr (Class.cv (nb057AlphaDummy127 f)) (Class.cv f)
            (Class.cv (nb057AlphaDummy126 f)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  with_reducible rw [Finset.mem_union]
  right
  exact Finset.mem_singleton_self _

theorem nb057_support_mem_0126 :
    (nb057AlphaDummy124) ∈
      (((Class.cv (nb057AlphaDummy124))).fv ∪ ((Class.cv (nb057AlphaDummy125))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb057_support_mem_0127 :
    (nb057AlphaDummy124) ∈
      (((synCcompl (Class.cab (nb057AlphaDummy130)
              (synWrex (nb057AlphaDummy131) (Class.cv (nb057AlphaDummy124))
                (Wff.classEq (Class.cv (nb057AlphaDummy130))
                  (synCphi (Class.cv (nb057AlphaDummy131)))))))).fv ∪ ((synCcompl
            (Class.cab (nb057AlphaDummy130)
              (synWrex (nb057AlphaDummy131) (Class.cv (nb057AlphaDummy125))
                (Wff.classEq (Class.cv (nb057AlphaDummy130))
                  (synCun (synCphi (Class.cv (nb057AlphaDummy131)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0126) 0))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0126) 1))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb057_support_mem_0128 (f : Var) :
    (nb057AlphaDummy126 f) ∈
      (((Class.cv (nb057AlphaDummy126 f))).fv ∪ ((Class.cv (nb057AlphaDummy127 f))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb057_support_mem_0129 (f : Var) :
    (nb057AlphaDummy126 f) ∈
      (((synCcompl (Class.cab (nb057AlphaDummy132 f)
              (synWrex (nb057AlphaDummy133 f) (Class.cv (nb057AlphaDummy126 f))
                (Wff.classEq (Class.cv (nb057AlphaDummy132 f))
                  (synCphi (Class.cv (nb057AlphaDummy133 f)))))))).fv ∪ ((synCcompl
            (Class.cab (nb057AlphaDummy132 f)
              (synWrex (nb057AlphaDummy133 f) (Class.cv (nb057AlphaDummy127 f))
                (Wff.classEq (Class.cv (nb057AlphaDummy132 f))
                  (synCun (synCphi (Class.cv (nb057AlphaDummy133 f)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0128 f) 0))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0128 f) 1))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb057_support_mem_0130 :
    (nb057AlphaDummy124) ∈
      (((Class.cab (nb057AlphaDummy130)
            (synWrex (nb057AlphaDummy131) (Class.cv (nb057AlphaDummy124))
              (Wff.classEq (Class.cv (nb057AlphaDummy130))
                (synCphi (Class.cv (nb057AlphaDummy131))))))).fv ∪
        ((Class.cab (nb057AlphaDummy130)
            (synWrex (nb057AlphaDummy131) (Class.cv (nb057AlphaDummy124))
              (Wff.classEq (Class.cv (nb057AlphaDummy130))
                (synCphi (Class.cv (nb057AlphaDummy131))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0126) 0))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0126) 1))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb057_support_mem_0131 (f : Var) :
    (nb057AlphaDummy126 f) ∈
      (((Class.cab (nb057AlphaDummy132 f)
            (synWrex (nb057AlphaDummy133 f) (Class.cv (nb057AlphaDummy126 f))
              (Wff.classEq (Class.cv (nb057AlphaDummy132 f))
                (synCphi (Class.cv (nb057AlphaDummy133 f))))))).fv ∪
        ((Class.cab (nb057AlphaDummy132 f)
            (synWrex (nb057AlphaDummy133 f) (Class.cv (nb057AlphaDummy126 f))
              (Wff.classEq (Class.cv (nb057AlphaDummy132 f))
                (synCphi (Class.cv (nb057AlphaDummy133 f))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0128 f) 0))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0128 f) 1))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb057_support_mem_0132 :
    (nb057AlphaDummy131) ∈ (((Class.cv (nb057AlphaDummy131))).fv) :=
  by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb057_support_mem_0133 (f : Var) :
    (nb057AlphaDummy133 f) ∈ (((Class.cv (nb057AlphaDummy133 f))).fv) :=
  by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb057_support_mem_0134 :
    (nb057AlphaDummy138) ∈
      (((Wff.classMem (Class.cv (nb057AlphaDummy138)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb057AlphaDummy138)) (synC1c))).fv ∪
        ((Class.cv (nb057AlphaDummy138))).fv) :=
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

theorem nb057_support_mem_0135 (f : Var) :
    (nb057AlphaDummy140 f) ∈
      (((Wff.classMem (Class.cv (nb057AlphaDummy140 f)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb057AlphaDummy140 f)) (synC1c))).fv ∪
        ((Class.cv (nb057AlphaDummy140 f))).fv) :=
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

theorem nb057_support_mem_0136 :
    (nb057AlphaDummy138) ∈
      (((Class.cv (nb057AlphaDummy138))).fv ∪ ((synC1c)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb057_support_mem_0137 (f : Var) :
    (nb057AlphaDummy140 f) ∈
      (((Class.cv (nb057AlphaDummy140 f))).fv ∪ ((synC1c)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb057_support_mem_0138 :
    (nb057AlphaDummy145) ∈
      (((synCnin (Class.cv (nb057AlphaDummy145)) (Class.cv (nb057AlphaDummy146)))).fv ∪
        ((synCnin (Class.cv (nb057AlphaDummy145))
            (Class.cv (nb057AlphaDummy146)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb057_support_mem_0139 (f : Var) :
    (nb057AlphaDummy148 f) ∈
      (((synCnin (Class.cv (nb057AlphaDummy148 f))
            (Class.cv (nb057AlphaDummy149 f)))).fv ∪
        ((synCnin (Class.cv (nb057AlphaDummy148 f))
            (Class.cv (nb057AlphaDummy149 f)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb057_support_mem_0140 :
    (nb057AlphaDummy145) ∈
      (((Class.cv (nb057AlphaDummy145))).fv ∪ ((Class.cv (nb057AlphaDummy146))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb057_support_mem_0141 (f : Var) :
    (nb057AlphaDummy148 f) ∈
      (((Class.cv (nb057AlphaDummy148 f))).fv ∪ ((Class.cv (nb057AlphaDummy149 f))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb057_support_mem_0142 :
    (nb057AlphaDummy146) ∈
      (((synCnin (Class.cv (nb057AlphaDummy145)) (Class.cv (nb057AlphaDummy146)))).fv ∪
        ((synCnin (Class.cv (nb057AlphaDummy145))
            (Class.cv (nb057AlphaDummy146)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb057_support_mem_0143 (f : Var) :
    (nb057AlphaDummy149 f) ∈
      (((synCnin (Class.cv (nb057AlphaDummy148 f))
            (Class.cv (nb057AlphaDummy149 f)))).fv ∪
        ((synCnin (Class.cv (nb057AlphaDummy148 f))
            (Class.cv (nb057AlphaDummy149 f)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb057_support_mem_0144 :
    (nb057AlphaDummy146) ∈
      (((Class.cv (nb057AlphaDummy145))).fv ∪ ((Class.cv (nb057AlphaDummy146))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb057_support_mem_0145 (f : Var) :
    (nb057AlphaDummy149 f) ∈
      (((Class.cv (nb057AlphaDummy148 f))).fv ∪ ((Class.cv (nb057AlphaDummy149 f))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb057_support_mem_0146 :
    (nb057AlphaDummy145) ∈
      (((synCcompl (Class.cv (nb057AlphaDummy145)))).fv ∪
        ((synCcompl (Class.cv (nb057AlphaDummy146)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb057_support_mem_0147 (f : Var) :
    (nb057AlphaDummy148 f) ∈
      (((synCcompl (Class.cv (nb057AlphaDummy148 f)))).fv ∪
        ((synCcompl (Class.cv (nb057AlphaDummy149 f)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb057_support_mem_0148 :
    (nb057AlphaDummy145) ∈
      (((Class.cv (nb057AlphaDummy145))).fv ∪ ((Class.cv (nb057AlphaDummy145))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb057_support_mem_0149 (f : Var) :
    (nb057AlphaDummy148 f) ∈
      (((Class.cv (nb057AlphaDummy148 f))).fv ∪ ((Class.cv (nb057AlphaDummy148 f))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb057_support_mem_0150 :
    (nb057AlphaDummy146) ∈
      (((synCcompl (Class.cv (nb057AlphaDummy145)))).fv ∪
        ((synCcompl (Class.cv (nb057AlphaDummy146)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb057_support_mem_0151 (f : Var) :
    (nb057AlphaDummy149 f) ∈
      (((synCcompl (Class.cv (nb057AlphaDummy148 f)))).fv ∪
        ((synCcompl (Class.cv (nb057AlphaDummy149 f)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb057_support_mem_0152 :
    (nb057AlphaDummy146) ∈
      (((Class.cv (nb057AlphaDummy146))).fv ∪ ((Class.cv (nb057AlphaDummy146))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb057_support_mem_0153 (f : Var) :
    (nb057AlphaDummy149 f) ∈
      (((Class.cv (nb057AlphaDummy149 f))).fv ∪ ((Class.cv (nb057AlphaDummy149 f))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb057_support_mem_0154 :
    (nb057AlphaDummy125) ∈
      (((Class.cv (nb057AlphaDummy124))).fv ∪ ((Class.cv (nb057AlphaDummy125))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb057_support_mem_0155 :
    (nb057AlphaDummy125) ∈
      (((synCcompl (Class.cab (nb057AlphaDummy130)
              (synWrex (nb057AlphaDummy131) (Class.cv (nb057AlphaDummy124))
                (Wff.classEq (Class.cv (nb057AlphaDummy130))
                  (synCphi (Class.cv (nb057AlphaDummy131)))))))).fv ∪ ((synCcompl
            (Class.cab (nb057AlphaDummy130)
              (synWrex (nb057AlphaDummy131) (Class.cv (nb057AlphaDummy125))
                (Wff.classEq (Class.cv (nb057AlphaDummy130))
                  (synCun (synCphi (Class.cv (nb057AlphaDummy131)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0154) 0))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0154) 1))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb057_support_mem_0156 (f : Var) :
    (nb057AlphaDummy127 f) ∈
      (((Class.cv (nb057AlphaDummy126 f))).fv ∪ ((Class.cv (nb057AlphaDummy127 f))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb057_support_mem_0157 (f : Var) :
    (nb057AlphaDummy127 f) ∈
      (((synCcompl (Class.cab (nb057AlphaDummy132 f)
              (synWrex (nb057AlphaDummy133 f) (Class.cv (nb057AlphaDummy126 f))
                (Wff.classEq (Class.cv (nb057AlphaDummy132 f))
                  (synCphi (Class.cv (nb057AlphaDummy133 f)))))))).fv ∪ ((synCcompl
            (Class.cab (nb057AlphaDummy132 f)
              (synWrex (nb057AlphaDummy133 f) (Class.cv (nb057AlphaDummy127 f))
                (Wff.classEq (Class.cv (nb057AlphaDummy132 f))
                  (synCun (synCphi (Class.cv (nb057AlphaDummy133 f)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0156 f) 0))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0156 f) 1))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb057_support_mem_0158 :
    (nb057AlphaDummy125) ∈
      (((Class.cab (nb057AlphaDummy130)
            (synWrex (nb057AlphaDummy131) (Class.cv (nb057AlphaDummy125))
              (Wff.classEq (Class.cv (nb057AlphaDummy130))
                (synCun (synCphi (Class.cv (nb057AlphaDummy131)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb057AlphaDummy130)
            (synWrex (nb057AlphaDummy131) (Class.cv (nb057AlphaDummy125))
              (Wff.classEq (Class.cv (nb057AlphaDummy130))
                (synCun (synCphi (Class.cv (nb057AlphaDummy131)))
                  (synCsn (synC0c))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0154) 0))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0154) 1))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb057_support_mem_0159 (f : Var) :
    (nb057AlphaDummy127 f) ∈
      (((Class.cab (nb057AlphaDummy132 f)
            (synWrex (nb057AlphaDummy133 f) (Class.cv (nb057AlphaDummy127 f))
              (Wff.classEq (Class.cv (nb057AlphaDummy132 f))
                (synCun (synCphi (Class.cv (nb057AlphaDummy133 f)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb057AlphaDummy132 f)
            (synWrex (nb057AlphaDummy133 f) (Class.cv (nb057AlphaDummy127 f))
              (Wff.classEq (Class.cv (nb057AlphaDummy132 f))
                (synCun (synCphi (Class.cv (nb057AlphaDummy133 f)))
                  (synCsn (synC0c))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0156 f) 0))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0156 f) 1))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb057_support_mem_0160 :
    (nb057AlphaDummy131) ∈
      (((synCcompl (synCphi (Class.cv (nb057AlphaDummy131))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb057_support_mem_0161 (f : Var) :
    (nb057AlphaDummy133 f) ∈
      (((synCcompl (synCphi (Class.cv (nb057AlphaDummy133 f))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb057_support_mem_0162 :
    (nb057AlphaDummy131) ∈
      (((synCphi (Class.cv (nb057AlphaDummy131)))).fv ∪
        ((synCphi (Class.cv (nb057AlphaDummy131)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb057_support_mem_0163 (f : Var) :
    (nb057AlphaDummy133 f) ∈
      (((synCphi (Class.cv (nb057AlphaDummy133 f)))).fv ∪
        ((synCphi (Class.cv (nb057AlphaDummy133 f)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb057_support_mem_0164 :
    (nb057AlphaDummy125) ∈
      (((Class.cv (nb057AlphaDummy125))).fv ∪ ((Class.cv (nb057AlphaDummy124))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb057_support_mem_0165 :
    (nb057AlphaDummy125) ∈
      (((synCcompl (Class.cab (nb057AlphaDummy166)
              (synWrex (nb057AlphaDummy167) (Class.cv (nb057AlphaDummy125))
                (Wff.classEq (Class.cv (nb057AlphaDummy166))
                  (synCphi (Class.cv (nb057AlphaDummy167)))))))).fv ∪ ((synCcompl
            (Class.cab (nb057AlphaDummy166)
              (synWrex (nb057AlphaDummy167) (Class.cv (nb057AlphaDummy124))
                (Wff.classEq (Class.cv (nb057AlphaDummy166))
                  (synCun (synCphi (Class.cv (nb057AlphaDummy167)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0164) 0))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0164) 1))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb057_support_mem_0166 (f : Var) :
    (nb057AlphaDummy127 f) ∈
      (((Class.cv (nb057AlphaDummy127 f))).fv ∪ ((Class.cv (nb057AlphaDummy126 f))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb057_support_mem_0167 (f : Var) :
    (nb057AlphaDummy127 f) ∈
      (((synCcompl (Class.cab (nb057AlphaDummy168 f)
              (synWrex (nb057AlphaDummy169 f) (Class.cv (nb057AlphaDummy127 f))
                (Wff.classEq (Class.cv (nb057AlphaDummy168 f))
                  (synCphi (Class.cv (nb057AlphaDummy169 f)))))))).fv ∪ ((synCcompl
            (Class.cab (nb057AlphaDummy168 f)
              (synWrex (nb057AlphaDummy169 f) (Class.cv (nb057AlphaDummy126 f))
                (Wff.classEq (Class.cv (nb057AlphaDummy168 f))
                  (synCun (synCphi (Class.cv (nb057AlphaDummy169 f)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0166 f) 0))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0166 f) 1))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb057_support_mem_0168 :
    (nb057AlphaDummy125) ∈
      (((Class.cab (nb057AlphaDummy166)
            (synWrex (nb057AlphaDummy167) (Class.cv (nb057AlphaDummy125))
              (Wff.classEq (Class.cv (nb057AlphaDummy166))
                (synCphi (Class.cv (nb057AlphaDummy167))))))).fv ∪
        ((Class.cab (nb057AlphaDummy166)
            (synWrex (nb057AlphaDummy167) (Class.cv (nb057AlphaDummy125))
              (Wff.classEq (Class.cv (nb057AlphaDummy166))
                (synCphi (Class.cv (nb057AlphaDummy167))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0164) 0))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0164) 1))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb057_support_mem_0169 (f : Var) :
    (nb057AlphaDummy127 f) ∈
      (((Class.cab (nb057AlphaDummy168 f)
            (synWrex (nb057AlphaDummy169 f) (Class.cv (nb057AlphaDummy127 f))
              (Wff.classEq (Class.cv (nb057AlphaDummy168 f))
                (synCphi (Class.cv (nb057AlphaDummy169 f))))))).fv ∪
        ((Class.cab (nb057AlphaDummy168 f)
            (synWrex (nb057AlphaDummy169 f) (Class.cv (nb057AlphaDummy127 f))
              (Wff.classEq (Class.cv (nb057AlphaDummy168 f))
                (synCphi (Class.cv (nb057AlphaDummy169 f))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0166 f) 0))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0166 f) 1))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb057_support_mem_0170 :
    (nb057AlphaDummy167) ∈ (((Class.cv (nb057AlphaDummy167))).fv) :=
  by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb057_support_mem_0171 (f : Var) :
    (nb057AlphaDummy169 f) ∈ (((Class.cv (nb057AlphaDummy169 f))).fv) :=
  by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb057_support_mem_0172 :
    (nb057AlphaDummy174) ∈
      (((Wff.classMem (Class.cv (nb057AlphaDummy174)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb057AlphaDummy174)) (synC1c))).fv ∪
        ((Class.cv (nb057AlphaDummy174))).fv) :=
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

theorem nb057_support_mem_0173 (f : Var) :
    (nb057AlphaDummy176 f) ∈
      (((Wff.classMem (Class.cv (nb057AlphaDummy176 f)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb057AlphaDummy176 f)) (synC1c))).fv ∪
        ((Class.cv (nb057AlphaDummy176 f))).fv) :=
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

theorem nb057_support_mem_0174 :
    (nb057AlphaDummy174) ∈
      (((Class.cv (nb057AlphaDummy174))).fv ∪ ((synC1c)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb057_support_mem_0175 (f : Var) :
    (nb057AlphaDummy176 f) ∈
      (((Class.cv (nb057AlphaDummy176 f))).fv ∪ ((synC1c)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb057_support_mem_0176 :
    (nb057AlphaDummy181) ∈
      (((synCnin (Class.cv (nb057AlphaDummy181)) (Class.cv (nb057AlphaDummy182)))).fv ∪
        ((synCnin (Class.cv (nb057AlphaDummy181))
            (Class.cv (nb057AlphaDummy182)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb057_support_mem_0177 (f : Var) :
    (nb057AlphaDummy184 f) ∈
      (((synCnin (Class.cv (nb057AlphaDummy184 f))
            (Class.cv (nb057AlphaDummy185 f)))).fv ∪
        ((synCnin (Class.cv (nb057AlphaDummy184 f))
            (Class.cv (nb057AlphaDummy185 f)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb057_support_mem_0178 :
    (nb057AlphaDummy181) ∈
      (((Class.cv (nb057AlphaDummy181))).fv ∪ ((Class.cv (nb057AlphaDummy182))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb057_support_mem_0179 (f : Var) :
    (nb057AlphaDummy184 f) ∈
      (((Class.cv (nb057AlphaDummy184 f))).fv ∪ ((Class.cv (nb057AlphaDummy185 f))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb057_support_mem_0180 :
    (nb057AlphaDummy182) ∈
      (((synCnin (Class.cv (nb057AlphaDummy181)) (Class.cv (nb057AlphaDummy182)))).fv ∪
        ((synCnin (Class.cv (nb057AlphaDummy181))
            (Class.cv (nb057AlphaDummy182)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb057_support_mem_0181 (f : Var) :
    (nb057AlphaDummy185 f) ∈
      (((synCnin (Class.cv (nb057AlphaDummy184 f))
            (Class.cv (nb057AlphaDummy185 f)))).fv ∪
        ((synCnin (Class.cv (nb057AlphaDummy184 f))
            (Class.cv (nb057AlphaDummy185 f)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb057_support_mem_0182 :
    (nb057AlphaDummy182) ∈
      (((Class.cv (nb057AlphaDummy181))).fv ∪ ((Class.cv (nb057AlphaDummy182))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb057_support_mem_0183 (f : Var) :
    (nb057AlphaDummy185 f) ∈
      (((Class.cv (nb057AlphaDummy184 f))).fv ∪ ((Class.cv (nb057AlphaDummy185 f))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb057_support_mem_0184 :
    (nb057AlphaDummy181) ∈
      (((synCcompl (Class.cv (nb057AlphaDummy181)))).fv ∪
        ((synCcompl (Class.cv (nb057AlphaDummy182)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb057_support_mem_0185 (f : Var) :
    (nb057AlphaDummy184 f) ∈
      (((synCcompl (Class.cv (nb057AlphaDummy184 f)))).fv ∪
        ((synCcompl (Class.cv (nb057AlphaDummy185 f)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb057_support_mem_0186 :
    (nb057AlphaDummy181) ∈
      (((Class.cv (nb057AlphaDummy181))).fv ∪ ((Class.cv (nb057AlphaDummy181))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb057_support_mem_0187 (f : Var) :
    (nb057AlphaDummy184 f) ∈
      (((Class.cv (nb057AlphaDummy184 f))).fv ∪ ((Class.cv (nb057AlphaDummy184 f))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb057_support_mem_0188 :
    (nb057AlphaDummy182) ∈
      (((synCcompl (Class.cv (nb057AlphaDummy181)))).fv ∪
        ((synCcompl (Class.cv (nb057AlphaDummy182)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb057_support_mem_0189 (f : Var) :
    (nb057AlphaDummy185 f) ∈
      (((synCcompl (Class.cv (nb057AlphaDummy184 f)))).fv ∪
        ((synCcompl (Class.cv (nb057AlphaDummy185 f)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb057_support_mem_0190 :
    (nb057AlphaDummy182) ∈
      (((Class.cv (nb057AlphaDummy182))).fv ∪ ((Class.cv (nb057AlphaDummy182))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb057_support_mem_0191 (f : Var) :
    (nb057AlphaDummy185 f) ∈
      (((Class.cv (nb057AlphaDummy185 f))).fv ∪ ((Class.cv (nb057AlphaDummy185 f))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb057_support_mem_0192 :
    (nb057AlphaDummy124) ∈
      (((Class.cv (nb057AlphaDummy125))).fv ∪ ((Class.cv (nb057AlphaDummy124))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb057_support_mem_0193 :
    (nb057AlphaDummy124) ∈
      (((synCcompl (Class.cab (nb057AlphaDummy166)
              (synWrex (nb057AlphaDummy167) (Class.cv (nb057AlphaDummy125))
                (Wff.classEq (Class.cv (nb057AlphaDummy166))
                  (synCphi (Class.cv (nb057AlphaDummy167)))))))).fv ∪ ((synCcompl
            (Class.cab (nb057AlphaDummy166)
              (synWrex (nb057AlphaDummy167) (Class.cv (nb057AlphaDummy124))
                (Wff.classEq (Class.cv (nb057AlphaDummy166))
                  (synCun (synCphi (Class.cv (nb057AlphaDummy167)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0192) 0))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0192) 1))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb057_support_mem_0194 (f : Var) :
    (nb057AlphaDummy126 f) ∈
      (((Class.cv (nb057AlphaDummy127 f))).fv ∪ ((Class.cv (nb057AlphaDummy126 f))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb057_support_mem_0195 (f : Var) :
    (nb057AlphaDummy126 f) ∈
      (((synCcompl (Class.cab (nb057AlphaDummy168 f)
              (synWrex (nb057AlphaDummy169 f) (Class.cv (nb057AlphaDummy127 f))
                (Wff.classEq (Class.cv (nb057AlphaDummy168 f))
                  (synCphi (Class.cv (nb057AlphaDummy169 f)))))))).fv ∪ ((synCcompl
            (Class.cab (nb057AlphaDummy168 f)
              (synWrex (nb057AlphaDummy169 f) (Class.cv (nb057AlphaDummy126 f))
                (Wff.classEq (Class.cv (nb057AlphaDummy168 f))
                  (synCun (synCphi (Class.cv (nb057AlphaDummy169 f)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0194 f) 0))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0194 f) 1))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb057_support_mem_0196 :
    (nb057AlphaDummy124) ∈
      (((Class.cab (nb057AlphaDummy166)
            (synWrex (nb057AlphaDummy167) (Class.cv (nb057AlphaDummy124))
              (Wff.classEq (Class.cv (nb057AlphaDummy166))
                (synCun (synCphi (Class.cv (nb057AlphaDummy167)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb057AlphaDummy166)
            (synWrex (nb057AlphaDummy167) (Class.cv (nb057AlphaDummy124))
              (Wff.classEq (Class.cv (nb057AlphaDummy166))
                (synCun (synCphi (Class.cv (nb057AlphaDummy167)))
                  (synCsn (synC0c))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0192) 0))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0192) 1))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb057_support_mem_0197 (f : Var) :
    (nb057AlphaDummy126 f) ∈
      (((Class.cab (nb057AlphaDummy168 f)
            (synWrex (nb057AlphaDummy169 f) (Class.cv (nb057AlphaDummy126 f))
              (Wff.classEq (Class.cv (nb057AlphaDummy168 f))
                (synCun (synCphi (Class.cv (nb057AlphaDummy169 f)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb057AlphaDummy168 f)
            (synWrex (nb057AlphaDummy169 f) (Class.cv (nb057AlphaDummy126 f))
              (Wff.classEq (Class.cv (nb057AlphaDummy168 f))
                (synCun (synCphi (Class.cv (nb057AlphaDummy169 f)))
                  (synCsn (synC0c))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0194 f) 0))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0194 f) 1))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb057_support_mem_0198 :
    (nb057AlphaDummy167) ∈
      (((synCcompl (synCphi (Class.cv (nb057AlphaDummy167))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb057_support_mem_0199 (f : Var) :
    (nb057AlphaDummy169 f) ∈
      (((synCcompl (synCphi (Class.cv (nb057AlphaDummy169 f))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb057_support_mem_0200 :
    (nb057AlphaDummy167) ∈
      (((synCphi (Class.cv (nb057AlphaDummy167)))).fv ∪
        ((synCphi (Class.cv (nb057AlphaDummy167)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb057_support_mem_0201 (f : Var) :
    (nb057AlphaDummy169 f) ∈
      (((synCphi (Class.cv (nb057AlphaDummy169 f)))).fv ∪
        ((synCphi (Class.cv (nb057AlphaDummy169 f)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb057_support_mem_0202 :
    (nb057AlphaDummy001) ∈
      (((synCnin (synCcom (Class.cv (nb057AlphaDummy001))
              (synCcnv (Class.cv (nb057AlphaDummy001)))) (synCid))).fv ∪ ((synCnin
            (synCcom (Class.cv (nb057AlphaDummy001))
              (synCcnv (Class.cv (nb057AlphaDummy001)))) (synCid))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccom]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb057_support_mem_0203 (f : Var) :
    f ∈
      (((synCnin (synCcom (Class.cv f) (synCcnv (Class.cv f))) (synCid))).fv ∪
        ((synCnin (synCcom (Class.cv f) (synCcnv (Class.cv f))) (synCid))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccom]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb057_support_mem_0204 :
    (nb057AlphaDummy001) ∈
      (((synCcom (Class.cv (nb057AlphaDummy001))
            (synCcnv (Class.cv (nb057AlphaDummy001))))).fv ∪ ((synCid)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccom]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb057_support_mem_0205 (f : Var) :
    f ∈ (((synCcom (Class.cv f) (synCcnv (Class.cv f)))).fv ∪ ((synCid)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccom]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb057_support_mem_0206 :
    (nb057AlphaDummy001) ∈
      (((Class.cv (nb057AlphaDummy001))).fv ∪
        ((synCcnv (Class.cv (nb057AlphaDummy001)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb057_support_mem_0207 :
    (nb057AlphaDummy001) ∈
      (({(nb057AlphaDummy044)} : Finset Var) ∪ ({(nb057AlphaDummy045)} : Finset Var) ∪
        ((synWex (nb057AlphaDummy046) (synWa (synWbr (Class.cv (nb057AlphaDummy044))
                (synCcnv (Class.cv (nb057AlphaDummy001)))
                (Class.cv (nb057AlphaDummy046))) (synWbr (Class.cv (nb057AlphaDummy046))
                (Class.cv (nb057AlphaDummy001)) (Class.cv (nb057AlphaDummy045)))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_wex]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0206) 2))
  · rw [fv_syn_wa]
    with_reducible rw [Finset.mem_union]
    left
    rw [fv_syn_wbr]
    with_reducible rw [Finset.mem_union]
    right
    rw [fv_syn_ccnv]
    rw [fv_class_cv]
    exact Finset.mem_singleton_self _

theorem nb057_support_mem_0208 (f : Var) :
    f ∈ (((Class.cv f)).fv ∪ ((synCcnv (Class.cv f))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb057_support_mem_0209 (f : Var) :
    f ∈
      (({(nb057AlphaDummy047 f)} : Finset Var) ∪ ({(nb057AlphaDummy048 f)} : Finset Var) ∪
        ((synWex (nb057AlphaDummy049 f) (synWa
              (synWbr (Class.cv (nb057AlphaDummy047 f)) (synCcnv (Class.cv f))
                (Class.cv (nb057AlphaDummy049 f)))
              (synWbr (Class.cv (nb057AlphaDummy049 f)) (Class.cv f)
                (Class.cv (nb057AlphaDummy048 f)))))).fv) :=
  by
  have fresh : f ≠ nb057AlphaDummy049 f :=
    by
    unfold nb057AlphaDummy049
    with_reducible exact (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0208 f) 2))
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_wex]
  with_reducible rw [Finset.mem_erase]
  constructor
  · with_reducible exact fresh
  · rw [fv_syn_wa]
    with_reducible rw [Finset.mem_union]
    left
    rw [fv_syn_wbr]
    with_reducible rw [Finset.mem_union]
    right
    rw [fv_syn_ccnv]
    rw [fv_class_cv]
    exact Finset.mem_singleton_self _

theorem nb057_support_mem_0210 :
    (nb057AlphaDummy001) ∈
      (({(nb057AlphaDummy124)} : Finset Var) ∪ ({(nb057AlphaDummy125)} : Finset Var) ∪
        ((synWbr (Class.cv (nb057AlphaDummy125)) (Class.cv (nb057AlphaDummy001))
            (Class.cv (nb057AlphaDummy124)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_wbr]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb057_support_mem_0211 (f : Var) :
    f ∈
      (({(nb057AlphaDummy126 f)} : Finset Var) ∪ ({(nb057AlphaDummy127 f)} : Finset Var) ∪
        ((synWbr (Class.cv (nb057AlphaDummy127 f)) (Class.cv f)
            (Class.cv (nb057AlphaDummy126 f)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_wbr]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb057_support_mem_0212 :
    (nb057AlphaDummy001) ∈ (((Class.cv (nb057AlphaDummy001))).fv) :=
  by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb057_support_mem_0213 (f : Var) : f ∈ (((Class.cv f)).fv) :=
  by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb057_support_mem_0214 :
    (nb057AlphaDummy046) ∈
      (((Class.cv (nb057AlphaDummy046))).fv ∪ ((Class.cv (nb057AlphaDummy045))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb057_support_mem_0215 :
    (nb057AlphaDummy046) ∈
      (((synCcompl (Class.cab (nb057AlphaDummy202)
              (synWrex (nb057AlphaDummy203) (Class.cv (nb057AlphaDummy046))
                (Wff.classEq (Class.cv (nb057AlphaDummy202))
                  (synCphi (Class.cv (nb057AlphaDummy203)))))))).fv ∪ ((synCcompl
            (Class.cab (nb057AlphaDummy202)
              (synWrex (nb057AlphaDummy203) (Class.cv (nb057AlphaDummy045))
                (Wff.classEq (Class.cv (nb057AlphaDummy202))
                  (synCun (synCphi (Class.cv (nb057AlphaDummy203)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0214) 0))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0214) 1))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb057_support_mem_0216 (f : Var) :
    (nb057AlphaDummy049 f) ∈
      (((Class.cv (nb057AlphaDummy049 f))).fv ∪ ((Class.cv (nb057AlphaDummy048 f))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb057_support_mem_0217 (f : Var) :
    (nb057AlphaDummy049 f) ∈
      (((synCcompl (Class.cab (nb057AlphaDummy204 f)
              (synWrex (nb057AlphaDummy205 f) (Class.cv (nb057AlphaDummy049 f))
                (Wff.classEq (Class.cv (nb057AlphaDummy204 f))
                  (synCphi (Class.cv (nb057AlphaDummy205 f)))))))).fv ∪ ((synCcompl
            (Class.cab (nb057AlphaDummy204 f)
              (synWrex (nb057AlphaDummy205 f) (Class.cv (nb057AlphaDummy048 f))
                (Wff.classEq (Class.cv (nb057AlphaDummy204 f))
                  (synCun (synCphi (Class.cv (nb057AlphaDummy205 f)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0216 f) 0))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0216 f) 1))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb057_support_mem_0218 :
    (nb057AlphaDummy046) ∈
      (((Class.cab (nb057AlphaDummy202)
            (synWrex (nb057AlphaDummy203) (Class.cv (nb057AlphaDummy046))
              (Wff.classEq (Class.cv (nb057AlphaDummy202))
                (synCphi (Class.cv (nb057AlphaDummy203))))))).fv ∪
        ((Class.cab (nb057AlphaDummy202)
            (synWrex (nb057AlphaDummy203) (Class.cv (nb057AlphaDummy046))
              (Wff.classEq (Class.cv (nb057AlphaDummy202))
                (synCphi (Class.cv (nb057AlphaDummy203))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0214) 0))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0214) 1))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb057_support_mem_0219 (f : Var) :
    (nb057AlphaDummy049 f) ∈
      (((Class.cab (nb057AlphaDummy204 f)
            (synWrex (nb057AlphaDummy205 f) (Class.cv (nb057AlphaDummy049 f))
              (Wff.classEq (Class.cv (nb057AlphaDummy204 f))
                (synCphi (Class.cv (nb057AlphaDummy205 f))))))).fv ∪
        ((Class.cab (nb057AlphaDummy204 f)
            (synWrex (nb057AlphaDummy205 f) (Class.cv (nb057AlphaDummy049 f))
              (Wff.classEq (Class.cv (nb057AlphaDummy204 f))
                (synCphi (Class.cv (nb057AlphaDummy205 f))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0216 f) 0))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0216 f) 1))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb057_support_mem_0220 :
    (nb057AlphaDummy203) ∈ (((Class.cv (nb057AlphaDummy203))).fv) :=
  by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb057_support_mem_0221 (f : Var) :
    (nb057AlphaDummy205 f) ∈ (((Class.cv (nb057AlphaDummy205 f))).fv) :=
  by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb057_support_mem_0222 :
    (nb057AlphaDummy210) ∈
      (((Wff.classMem (Class.cv (nb057AlphaDummy210)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb057AlphaDummy210)) (synC1c))).fv ∪
        ((Class.cv (nb057AlphaDummy210))).fv) :=
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

theorem nb057_support_mem_0223 (f : Var) :
    (nb057AlphaDummy212 f) ∈
      (((Wff.classMem (Class.cv (nb057AlphaDummy212 f)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb057AlphaDummy212 f)) (synC1c))).fv ∪
        ((Class.cv (nb057AlphaDummy212 f))).fv) :=
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

theorem nb057_support_mem_0224 :
    (nb057AlphaDummy210) ∈
      (((Class.cv (nb057AlphaDummy210))).fv ∪ ((synC1c)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb057_support_mem_0225 (f : Var) :
    (nb057AlphaDummy212 f) ∈
      (((Class.cv (nb057AlphaDummy212 f))).fv ∪ ((synC1c)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb057_support_mem_0226 :
    (nb057AlphaDummy217) ∈
      (((synCnin (Class.cv (nb057AlphaDummy217)) (Class.cv (nb057AlphaDummy218)))).fv ∪
        ((synCnin (Class.cv (nb057AlphaDummy217))
            (Class.cv (nb057AlphaDummy218)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb057_support_mem_0227 (f : Var) :
    (nb057AlphaDummy220 f) ∈
      (((synCnin (Class.cv (nb057AlphaDummy220 f))
            (Class.cv (nb057AlphaDummy221 f)))).fv ∪
        ((synCnin (Class.cv (nb057AlphaDummy220 f))
            (Class.cv (nb057AlphaDummy221 f)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb057_support_mem_0228 :
    (nb057AlphaDummy217) ∈
      (((Class.cv (nb057AlphaDummy217))).fv ∪ ((Class.cv (nb057AlphaDummy218))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb057_support_mem_0229 (f : Var) :
    (nb057AlphaDummy220 f) ∈
      (((Class.cv (nb057AlphaDummy220 f))).fv ∪ ((Class.cv (nb057AlphaDummy221 f))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb057_support_mem_0230 :
    (nb057AlphaDummy218) ∈
      (((synCnin (Class.cv (nb057AlphaDummy217)) (Class.cv (nb057AlphaDummy218)))).fv ∪
        ((synCnin (Class.cv (nb057AlphaDummy217))
            (Class.cv (nb057AlphaDummy218)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb057_support_mem_0231 (f : Var) :
    (nb057AlphaDummy221 f) ∈
      (((synCnin (Class.cv (nb057AlphaDummy220 f))
            (Class.cv (nb057AlphaDummy221 f)))).fv ∪
        ((synCnin (Class.cv (nb057AlphaDummy220 f))
            (Class.cv (nb057AlphaDummy221 f)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb057_support_mem_0232 :
    (nb057AlphaDummy218) ∈
      (((Class.cv (nb057AlphaDummy217))).fv ∪ ((Class.cv (nb057AlphaDummy218))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb057_support_mem_0233 (f : Var) :
    (nb057AlphaDummy221 f) ∈
      (((Class.cv (nb057AlphaDummy220 f))).fv ∪ ((Class.cv (nb057AlphaDummy221 f))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb057_support_mem_0234 :
    (nb057AlphaDummy217) ∈
      (((synCcompl (Class.cv (nb057AlphaDummy217)))).fv ∪
        ((synCcompl (Class.cv (nb057AlphaDummy218)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb057_support_mem_0235 (f : Var) :
    (nb057AlphaDummy220 f) ∈
      (((synCcompl (Class.cv (nb057AlphaDummy220 f)))).fv ∪
        ((synCcompl (Class.cv (nb057AlphaDummy221 f)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb057_support_mem_0236 :
    (nb057AlphaDummy217) ∈
      (((Class.cv (nb057AlphaDummy217))).fv ∪ ((Class.cv (nb057AlphaDummy217))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb057_support_mem_0237 (f : Var) :
    (nb057AlphaDummy220 f) ∈
      (((Class.cv (nb057AlphaDummy220 f))).fv ∪ ((Class.cv (nb057AlphaDummy220 f))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb057_support_mem_0238 :
    (nb057AlphaDummy218) ∈
      (((synCcompl (Class.cv (nb057AlphaDummy217)))).fv ∪
        ((synCcompl (Class.cv (nb057AlphaDummy218)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb057_support_mem_0239 (f : Var) :
    (nb057AlphaDummy221 f) ∈
      (((synCcompl (Class.cv (nb057AlphaDummy220 f)))).fv ∪
        ((synCcompl (Class.cv (nb057AlphaDummy221 f)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb057_support_mem_0240 :
    (nb057AlphaDummy218) ∈
      (((Class.cv (nb057AlphaDummy218))).fv ∪ ((Class.cv (nb057AlphaDummy218))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb057_support_mem_0241 (f : Var) :
    (nb057AlphaDummy221 f) ∈
      (((Class.cv (nb057AlphaDummy221 f))).fv ∪ ((Class.cv (nb057AlphaDummy221 f))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb057_support_mem_0242 :
    (nb057AlphaDummy045) ∈
      (((Class.cv (nb057AlphaDummy046))).fv ∪ ((Class.cv (nb057AlphaDummy045))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb057_support_mem_0243 :
    (nb057AlphaDummy045) ∈
      (((synCcompl (Class.cab (nb057AlphaDummy202)
              (synWrex (nb057AlphaDummy203) (Class.cv (nb057AlphaDummy046))
                (Wff.classEq (Class.cv (nb057AlphaDummy202))
                  (synCphi (Class.cv (nb057AlphaDummy203)))))))).fv ∪ ((synCcompl
            (Class.cab (nb057AlphaDummy202)
              (synWrex (nb057AlphaDummy203) (Class.cv (nb057AlphaDummy045))
                (Wff.classEq (Class.cv (nb057AlphaDummy202))
                  (synCun (synCphi (Class.cv (nb057AlphaDummy203)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0242) 0))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0242) 1))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb057_support_mem_0244 (f : Var) :
    (nb057AlphaDummy048 f) ∈
      (((Class.cv (nb057AlphaDummy049 f))).fv ∪ ((Class.cv (nb057AlphaDummy048 f))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb057_support_mem_0245 (f : Var) :
    (nb057AlphaDummy048 f) ∈
      (((synCcompl (Class.cab (nb057AlphaDummy204 f)
              (synWrex (nb057AlphaDummy205 f) (Class.cv (nb057AlphaDummy049 f))
                (Wff.classEq (Class.cv (nb057AlphaDummy204 f))
                  (synCphi (Class.cv (nb057AlphaDummy205 f)))))))).fv ∪ ((synCcompl
            (Class.cab (nb057AlphaDummy204 f)
              (synWrex (nb057AlphaDummy205 f) (Class.cv (nb057AlphaDummy048 f))
                (Wff.classEq (Class.cv (nb057AlphaDummy204 f))
                  (synCun (synCphi (Class.cv (nb057AlphaDummy205 f)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0244 f) 0))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb057_support_mem_0244 f) 1))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired

end
