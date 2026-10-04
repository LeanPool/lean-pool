/-
Copyright (c) 2026 Elliot Glazer and NFNotWPP contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elliot Glazer and NFNotWPP contributors
-/

module

public import LeanPool.NFWeakPartition.Certificates.NAR4C067C001Block001

/-! Nominal proof certificates grouped in dependency order. -/


public section

/-! Certificates from `NAR4C067C001Part006`. -/


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

theorem nb067_fresh_371 (x : Var) (y : Var) (f : Var) :
    (nb067AlphaDummy068 x y f) ∉
      (((synCcompl (Class.cv (nb067AlphaDummy061 x y f)))).fv ∪
        ((synCcompl (Class.cv (nb067AlphaDummy062 x y f)))).fv) :=
  by
  simpa only [nb067AlphaDummy068] using
    freshVar_not_mem
      (((synCcompl (Class.cv (nb067AlphaDummy061 x y f)))).fv ∪
        ((synCcompl (Class.cv (nb067AlphaDummy062 x y f)))).fv)
      0

theorem nb067_fresh_372 :
    (nb067AlphaDummy115) ∉
      (((synCcompl (Class.cv (nb067AlphaDummy106)))).fv ∪
        ((synCcompl (Class.cv (nb067AlphaDummy107)))).fv) :=
  by
  simpa only [nb067AlphaDummy115] using
    freshVar_not_mem
      (((synCcompl (Class.cv (nb067AlphaDummy106)))).fv ∪
        ((synCcompl (Class.cv (nb067AlphaDummy107)))).fv)
      0

theorem nb067_fresh_373 (f : Var) :
    (nb067AlphaDummy116 f) ∉
      (((synCcompl (Class.cv (nb067AlphaDummy109 f)))).fv ∪
        ((synCcompl (Class.cv (nb067AlphaDummy110 f)))).fv) :=
  by
  simpa only [nb067AlphaDummy116] using
    freshVar_not_mem
      (((synCcompl (Class.cv (nb067AlphaDummy109 f)))).fv ∪
        ((synCcompl (Class.cv (nb067AlphaDummy110 f)))).fv)
      0

theorem nb067_fresh_374 :
    (nb067AlphaDummy151) ∉
      (((synCcompl (Class.cv (nb067AlphaDummy142)))).fv ∪
        ((synCcompl (Class.cv (nb067AlphaDummy143)))).fv) :=
  by
  simpa only [nb067AlphaDummy151] using
    freshVar_not_mem
      (((synCcompl (Class.cv (nb067AlphaDummy142)))).fv ∪
        ((synCcompl (Class.cv (nb067AlphaDummy143)))).fv)
      0

theorem nb067_fresh_375 (f : Var) :
    (nb067AlphaDummy152 f) ∉
      (((synCcompl (Class.cv (nb067AlphaDummy145 f)))).fv ∪
        ((synCcompl (Class.cv (nb067AlphaDummy146 f)))).fv) :=
  by
  simpa only [nb067AlphaDummy152] using
    freshVar_not_mem
      (((synCcompl (Class.cv (nb067AlphaDummy145 f)))).fv ∪
        ((synCcompl (Class.cv (nb067AlphaDummy146 f)))).fv)
      0

theorem nb067_fresh_376 :
    (nb067AlphaDummy193) ∉
      (((synCcompl (Class.cv (nb067AlphaDummy184)))).fv ∪
        ((synCcompl (Class.cv (nb067AlphaDummy185)))).fv) :=
  by
  simpa only [nb067AlphaDummy193] using
    freshVar_not_mem
      (((synCcompl (Class.cv (nb067AlphaDummy184)))).fv ∪
        ((synCcompl (Class.cv (nb067AlphaDummy185)))).fv)
      0

theorem nb067_fresh_377 (f : Var) :
    (nb067AlphaDummy194 f) ∉
      (((synCcompl (Class.cv (nb067AlphaDummy187 f)))).fv ∪
        ((synCcompl (Class.cv (nb067AlphaDummy188 f)))).fv) :=
  by
  simpa only [nb067AlphaDummy194] using
    freshVar_not_mem
      (((synCcompl (Class.cv (nb067AlphaDummy187 f)))).fv ∪
        ((synCcompl (Class.cv (nb067AlphaDummy188 f)))).fv)
      0

theorem nb067_fresh_378 :
    (nb067AlphaDummy229) ∉
      (((synCcompl (Class.cv (nb067AlphaDummy220)))).fv ∪
        ((synCcompl (Class.cv (nb067AlphaDummy221)))).fv) :=
  by
  simpa only [nb067AlphaDummy229] using
    freshVar_not_mem
      (((synCcompl (Class.cv (nb067AlphaDummy220)))).fv ∪
        ((synCcompl (Class.cv (nb067AlphaDummy221)))).fv)
      0

theorem nb067_fresh_379 (f : Var) :
    (nb067AlphaDummy230 f) ∉
      (((synCcompl (Class.cv (nb067AlphaDummy223 f)))).fv ∪
        ((synCcompl (Class.cv (nb067AlphaDummy224 f)))).fv) :=
  by
  simpa only [nb067AlphaDummy230] using
    freshVar_not_mem
      (((synCcompl (Class.cv (nb067AlphaDummy223 f)))).fv ∪
        ((synCcompl (Class.cv (nb067AlphaDummy224 f)))).fv)
      0

theorem nb067_fresh_380 :
    (nb067AlphaDummy265) ∉
      (((synCcompl (Class.cv (nb067AlphaDummy256)))).fv ∪
        ((synCcompl (Class.cv (nb067AlphaDummy257)))).fv) :=
  by
  simpa only [nb067AlphaDummy265] using
    freshVar_not_mem
      (((synCcompl (Class.cv (nb067AlphaDummy256)))).fv ∪
        ((synCcompl (Class.cv (nb067AlphaDummy257)))).fv)
      0

theorem nb067_fresh_381 (f : Var) :
    (nb067AlphaDummy266 f) ∉
      (((synCcompl (Class.cv (nb067AlphaDummy259 f)))).fv ∪
        ((synCcompl (Class.cv (nb067AlphaDummy260 f)))).fv) :=
  by
  simpa only [nb067AlphaDummy266] using
    freshVar_not_mem
      (((synCcompl (Class.cv (nb067AlphaDummy259 f)))).fv ∪
        ((synCcompl (Class.cv (nb067AlphaDummy260 f)))).fv)
      0

theorem nb067_fresh_382 :
    (nb067AlphaDummy305) ∉
      (((synCcompl (Class.cv (nb067AlphaDummy296)))).fv ∪
        ((synCcompl (Class.cv (nb067AlphaDummy297)))).fv) :=
  by
  simpa only [nb067AlphaDummy305] using
    freshVar_not_mem
      (((synCcompl (Class.cv (nb067AlphaDummy296)))).fv ∪
        ((synCcompl (Class.cv (nb067AlphaDummy297)))).fv)
      0

theorem nb067_fresh_383 (f : Var) :
    (nb067AlphaDummy306 f) ∉
      (((synCcompl (Class.cv (nb067AlphaDummy299 f)))).fv ∪
        ((synCcompl (Class.cv (nb067AlphaDummy300 f)))).fv) :=
  by
  simpa only [nb067AlphaDummy306] using
    freshVar_not_mem
      (((synCcompl (Class.cv (nb067AlphaDummy299 f)))).fv ∪
        ((synCcompl (Class.cv (nb067AlphaDummy300 f)))).fv)
      0

theorem nb067_fresh_384 :
    (nb067AlphaDummy349) ∉
      (((synCcompl (Class.cv (nb067AlphaDummy340)))).fv ∪
        ((synCcompl (Class.cv (nb067AlphaDummy341)))).fv) :=
  by
  simpa only [nb067AlphaDummy349] using
    freshVar_not_mem
      (((synCcompl (Class.cv (nb067AlphaDummy340)))).fv ∪
        ((synCcompl (Class.cv (nb067AlphaDummy341)))).fv)
      0

theorem nb067_fresh_385 (f : Var) :
    (nb067AlphaDummy350 f) ∉
      (((synCcompl (Class.cv (nb067AlphaDummy343 f)))).fv ∪
        ((synCcompl (Class.cv (nb067AlphaDummy344 f)))).fv) :=
  by
  simpa only [nb067AlphaDummy350] using
    freshVar_not_mem
      (((synCcompl (Class.cv (nb067AlphaDummy343 f)))).fv ∪
        ((synCcompl (Class.cv (nb067AlphaDummy344 f)))).fv)
      0

theorem nb067_fresh_386 :
    (nb067AlphaDummy075) ∉
      (((synCcompl (synCphi (Class.cv (nb067AlphaDummy008))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv) :=
  by
  simpa only [nb067AlphaDummy075] using
    freshVar_not_mem
      (((synCcompl (synCphi (Class.cv (nb067AlphaDummy008))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv)
      0

theorem nb067_fresh_387 (x : Var) (y : Var) (f : Var) :
    (nb067AlphaDummy076 x y f) ∉
      (((synCcompl (synCphi (Class.cv (nb067AlphaDummy010 x y f))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv) :=
  by
  simpa only [nb067AlphaDummy076] using
    freshVar_not_mem
      (((synCcompl (synCphi (Class.cv (nb067AlphaDummy010 x y f))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv)
      0

theorem nb067_fresh_388 :
    (nb067AlphaDummy047) ∉
      (((synCcompl (synCphi (Class.cv (nb067AlphaDummy016))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv) :=
  by
  simpa only [nb067AlphaDummy047] using
    freshVar_not_mem
      (((synCcompl (synCphi (Class.cv (nb067AlphaDummy016))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv)
      0

theorem nb067_fresh_389 (x : Var) (y : Var) :
    (nb067AlphaDummy048 x y) ∉
      (((synCcompl (synCphi (Class.cv (nb067AlphaDummy018 x y))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv) :=
  by
  simpa only [nb067AlphaDummy048] using
    freshVar_not_mem
      (((synCcompl (synCphi (Class.cv (nb067AlphaDummy018 x y))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv)
      0

theorem nb067_fresh_390 :
    (nb067AlphaDummy123) ∉
      (((synCcompl (synCphi (Class.cv (nb067AlphaDummy092))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv) :=
  by
  simpa only [nb067AlphaDummy123] using
    freshVar_not_mem
      (((synCcompl (synCphi (Class.cv (nb067AlphaDummy092))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv)
      0

theorem nb067_fresh_391 (f : Var) :
    (nb067AlphaDummy124 f) ∉
      (((synCcompl (synCphi (Class.cv (nb067AlphaDummy094 f))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv) :=
  by
  simpa only [nb067AlphaDummy124] using
    freshVar_not_mem
      (((synCcompl (synCphi (Class.cv (nb067AlphaDummy094 f))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv)
      0

theorem nb067_fresh_392 :
    (nb067AlphaDummy159) ∉
      (((synCcompl (synCphi (Class.cv (nb067AlphaDummy128))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv) :=
  by
  simpa only [nb067AlphaDummy159] using
    freshVar_not_mem
      (((synCcompl (synCphi (Class.cv (nb067AlphaDummy128))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv)
      0

theorem nb067_fresh_393 (f : Var) :
    (nb067AlphaDummy160 f) ∉
      (((synCcompl (synCphi (Class.cv (nb067AlphaDummy130 f))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv) :=
  by
  simpa only [nb067AlphaDummy160] using
    freshVar_not_mem
      (((synCcompl (synCphi (Class.cv (nb067AlphaDummy130 f))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv)
      0

theorem nb067_fresh_394 :
    (nb067AlphaDummy201) ∉
      (((synCcompl (synCphi (Class.cv (nb067AlphaDummy170))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv) :=
  by
  simpa only [nb067AlphaDummy201] using
    freshVar_not_mem
      (((synCcompl (synCphi (Class.cv (nb067AlphaDummy170))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv)
      0

theorem nb067_fresh_395 (f : Var) :
    (nb067AlphaDummy202 f) ∉
      (((synCcompl (synCphi (Class.cv (nb067AlphaDummy172 f))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv) :=
  by
  simpa only [nb067AlphaDummy202] using
    freshVar_not_mem
      (((synCcompl (synCphi (Class.cv (nb067AlphaDummy172 f))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv)
      0

theorem nb067_fresh_396 :
    (nb067AlphaDummy237) ∉
      (((synCcompl (synCphi (Class.cv (nb067AlphaDummy206))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv) :=
  by
  simpa only [nb067AlphaDummy237] using
    freshVar_not_mem
      (((synCcompl (synCphi (Class.cv (nb067AlphaDummy206))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv)
      0

theorem nb067_fresh_397 (f : Var) :
    (nb067AlphaDummy238 f) ∉
      (((synCcompl (synCphi (Class.cv (nb067AlphaDummy208 f))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv) :=
  by
  simpa only [nb067AlphaDummy238] using
    freshVar_not_mem
      (((synCcompl (synCphi (Class.cv (nb067AlphaDummy208 f))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv)
      0

theorem nb067_fresh_398 :
    (nb067AlphaDummy273) ∉
      (((synCcompl (synCphi (Class.cv (nb067AlphaDummy242))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv) :=
  by
  simpa only [nb067AlphaDummy273] using
    freshVar_not_mem
      (((synCcompl (synCphi (Class.cv (nb067AlphaDummy242))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv)
      0

theorem nb067_fresh_399 (f : Var) :
    (nb067AlphaDummy274 f) ∉
      (((synCcompl (synCphi (Class.cv (nb067AlphaDummy244 f))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv) :=
  by
  simpa only [nb067AlphaDummy274] using
    freshVar_not_mem
      (((synCcompl (synCphi (Class.cv (nb067AlphaDummy244 f))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv)
      0

theorem nb067_fresh_400 :
    (nb067AlphaDummy313) ∉
      (((synCcompl (synCphi (Class.cv (nb067AlphaDummy282))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv) :=
  by
  simpa only [nb067AlphaDummy313] using
    freshVar_not_mem
      (((synCcompl (synCphi (Class.cv (nb067AlphaDummy282))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv)
      0

theorem nb067_fresh_401 (f : Var) :
    (nb067AlphaDummy314 f) ∉
      (((synCcompl (synCphi (Class.cv (nb067AlphaDummy284 f))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv) :=
  by
  simpa only [nb067AlphaDummy314] using
    freshVar_not_mem
      (((synCcompl (synCphi (Class.cv (nb067AlphaDummy284 f))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv)
      0

theorem nb067_fresh_402 :
    (nb067AlphaDummy357) ∉
      (((synCcompl (synCphi (Class.cv (nb067AlphaDummy326))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv) :=
  by
  simpa only [nb067AlphaDummy357] using
    freshVar_not_mem
      (((synCcompl (synCphi (Class.cv (nb067AlphaDummy326))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv)
      0

theorem nb067_fresh_403 (f : Var) :
    (nb067AlphaDummy358 f) ∉
      (((synCcompl (synCphi (Class.cv (nb067AlphaDummy328 f))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv) :=
  by
  simpa only [nb067AlphaDummy358] using
    freshVar_not_mem
      (((synCcompl (synCphi (Class.cv (nb067AlphaDummy328 f))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv)
      0

theorem nb067_fresh_404 :
    (nb067AlphaDummy035) ∉
      (((synCnin (Class.cv (nb067AlphaDummy030)) (Class.cv (nb067AlphaDummy031)))).fv ∪
        ((synCnin (Class.cv (nb067AlphaDummy030))
            (Class.cv (nb067AlphaDummy031)))).fv) :=
  by
  simpa only [nb067AlphaDummy035] using
    freshVar_not_mem
      (((synCnin (Class.cv (nb067AlphaDummy030)) (Class.cv (nb067AlphaDummy031)))).fv ∪
        ((synCnin (Class.cv (nb067AlphaDummy030)) (Class.cv (nb067AlphaDummy031)))).fv)
      0

theorem nb067_fresh_405 (x : Var) (y : Var) :
    (nb067AlphaDummy036 x y) ∉
      (((synCnin (Class.cv (nb067AlphaDummy033 x y))
            (Class.cv (nb067AlphaDummy034 x y)))).fv ∪
        ((synCnin (Class.cv (nb067AlphaDummy033 x y))
            (Class.cv (nb067AlphaDummy034 x y)))).fv) :=
  by
  simpa only [nb067AlphaDummy036] using
    freshVar_not_mem
      (((synCnin (Class.cv (nb067AlphaDummy033 x y))
            (Class.cv (nb067AlphaDummy034 x y)))).fv ∪
        ((synCnin (Class.cv (nb067AlphaDummy033 x y))
            (Class.cv (nb067AlphaDummy034 x y)))).fv)
      0

theorem nb067_fresh_406 :
    (nb067AlphaDummy063) ∉
      (((synCnin (Class.cv (nb067AlphaDummy058)) (Class.cv (nb067AlphaDummy059)))).fv ∪
        ((synCnin (Class.cv (nb067AlphaDummy058))
            (Class.cv (nb067AlphaDummy059)))).fv) :=
  by
  simpa only [nb067AlphaDummy063] using
    freshVar_not_mem
      (((synCnin (Class.cv (nb067AlphaDummy058)) (Class.cv (nb067AlphaDummy059)))).fv ∪
        ((synCnin (Class.cv (nb067AlphaDummy058)) (Class.cv (nb067AlphaDummy059)))).fv)
      0

theorem nb067_fresh_407 (x : Var) (y : Var) (f : Var) :
    (nb067AlphaDummy064 x y f) ∉
      (((synCnin (Class.cv (nb067AlphaDummy061 x y f))
            (Class.cv (nb067AlphaDummy062 x y f)))).fv ∪
        ((synCnin (Class.cv (nb067AlphaDummy061 x y f))
            (Class.cv (nb067AlphaDummy062 x y f)))).fv) :=
  by
  simpa only [nb067AlphaDummy064] using
    freshVar_not_mem
      (((synCnin (Class.cv (nb067AlphaDummy061 x y f))
            (Class.cv (nb067AlphaDummy062 x y f)))).fv ∪
        ((synCnin (Class.cv (nb067AlphaDummy061 x y f))
            (Class.cv (nb067AlphaDummy062 x y f)))).fv)
      0

theorem nb067_fresh_408 :
    (nb067AlphaDummy111) ∉
      (((synCnin (Class.cv (nb067AlphaDummy106)) (Class.cv (nb067AlphaDummy107)))).fv ∪
        ((synCnin (Class.cv (nb067AlphaDummy106))
            (Class.cv (nb067AlphaDummy107)))).fv) :=
  by
  simpa only [nb067AlphaDummy111] using
    freshVar_not_mem
      (((synCnin (Class.cv (nb067AlphaDummy106)) (Class.cv (nb067AlphaDummy107)))).fv ∪
        ((synCnin (Class.cv (nb067AlphaDummy106)) (Class.cv (nb067AlphaDummy107)))).fv)
      0

theorem nb067_fresh_409 (f : Var) :
    (nb067AlphaDummy112 f) ∉
      (((synCnin (Class.cv (nb067AlphaDummy109 f))
            (Class.cv (nb067AlphaDummy110 f)))).fv ∪
        ((synCnin (Class.cv (nb067AlphaDummy109 f))
            (Class.cv (nb067AlphaDummy110 f)))).fv) :=
  by
  simpa only [nb067AlphaDummy112] using
    freshVar_not_mem
      (((synCnin (Class.cv (nb067AlphaDummy109 f))
            (Class.cv (nb067AlphaDummy110 f)))).fv ∪
        ((synCnin (Class.cv (nb067AlphaDummy109 f))
            (Class.cv (nb067AlphaDummy110 f)))).fv)
      0

theorem nb067_fresh_410 :
    (nb067AlphaDummy147) ∉
      (((synCnin (Class.cv (nb067AlphaDummy142)) (Class.cv (nb067AlphaDummy143)))).fv ∪
        ((synCnin (Class.cv (nb067AlphaDummy142))
            (Class.cv (nb067AlphaDummy143)))).fv) :=
  by
  simpa only [nb067AlphaDummy147] using
    freshVar_not_mem
      (((synCnin (Class.cv (nb067AlphaDummy142)) (Class.cv (nb067AlphaDummy143)))).fv ∪
        ((synCnin (Class.cv (nb067AlphaDummy142)) (Class.cv (nb067AlphaDummy143)))).fv)
      0

theorem nb067_fresh_411 (f : Var) :
    (nb067AlphaDummy148 f) ∉
      (((synCnin (Class.cv (nb067AlphaDummy145 f))
            (Class.cv (nb067AlphaDummy146 f)))).fv ∪
        ((synCnin (Class.cv (nb067AlphaDummy145 f))
            (Class.cv (nb067AlphaDummy146 f)))).fv) :=
  by
  simpa only [nb067AlphaDummy148] using
    freshVar_not_mem
      (((synCnin (Class.cv (nb067AlphaDummy145 f))
            (Class.cv (nb067AlphaDummy146 f)))).fv ∪
        ((synCnin (Class.cv (nb067AlphaDummy145 f))
            (Class.cv (nb067AlphaDummy146 f)))).fv)
      0

theorem nb067_fresh_412 :
    (nb067AlphaDummy189) ∉
      (((synCnin (Class.cv (nb067AlphaDummy184)) (Class.cv (nb067AlphaDummy185)))).fv ∪
        ((synCnin (Class.cv (nb067AlphaDummy184))
            (Class.cv (nb067AlphaDummy185)))).fv) :=
  by
  simpa only [nb067AlphaDummy189] using
    freshVar_not_mem
      (((synCnin (Class.cv (nb067AlphaDummy184)) (Class.cv (nb067AlphaDummy185)))).fv ∪
        ((synCnin (Class.cv (nb067AlphaDummy184)) (Class.cv (nb067AlphaDummy185)))).fv)
      0

theorem nb067_fresh_413 (f : Var) :
    (nb067AlphaDummy190 f) ∉
      (((synCnin (Class.cv (nb067AlphaDummy187 f))
            (Class.cv (nb067AlphaDummy188 f)))).fv ∪
        ((synCnin (Class.cv (nb067AlphaDummy187 f))
            (Class.cv (nb067AlphaDummy188 f)))).fv) :=
  by
  simpa only [nb067AlphaDummy190] using
    freshVar_not_mem
      (((synCnin (Class.cv (nb067AlphaDummy187 f))
            (Class.cv (nb067AlphaDummy188 f)))).fv ∪
        ((synCnin (Class.cv (nb067AlphaDummy187 f))
            (Class.cv (nb067AlphaDummy188 f)))).fv)
      0

theorem nb067_fresh_414 :
    (nb067AlphaDummy225) ∉
      (((synCnin (Class.cv (nb067AlphaDummy220)) (Class.cv (nb067AlphaDummy221)))).fv ∪
        ((synCnin (Class.cv (nb067AlphaDummy220))
            (Class.cv (nb067AlphaDummy221)))).fv) :=
  by
  simpa only [nb067AlphaDummy225] using
    freshVar_not_mem
      (((synCnin (Class.cv (nb067AlphaDummy220)) (Class.cv (nb067AlphaDummy221)))).fv ∪
        ((synCnin (Class.cv (nb067AlphaDummy220)) (Class.cv (nb067AlphaDummy221)))).fv)
      0

theorem nb067_fresh_415 (f : Var) :
    (nb067AlphaDummy226 f) ∉
      (((synCnin (Class.cv (nb067AlphaDummy223 f))
            (Class.cv (nb067AlphaDummy224 f)))).fv ∪
        ((synCnin (Class.cv (nb067AlphaDummy223 f))
            (Class.cv (nb067AlphaDummy224 f)))).fv) :=
  by
  simpa only [nb067AlphaDummy226] using
    freshVar_not_mem
      (((synCnin (Class.cv (nb067AlphaDummy223 f))
            (Class.cv (nb067AlphaDummy224 f)))).fv ∪
        ((synCnin (Class.cv (nb067AlphaDummy223 f))
            (Class.cv (nb067AlphaDummy224 f)))).fv)
      0

theorem nb067_fresh_416 :
    (nb067AlphaDummy261) ∉
      (((synCnin (Class.cv (nb067AlphaDummy256)) (Class.cv (nb067AlphaDummy257)))).fv ∪
        ((synCnin (Class.cv (nb067AlphaDummy256))
            (Class.cv (nb067AlphaDummy257)))).fv) :=
  by
  simpa only [nb067AlphaDummy261] using
    freshVar_not_mem
      (((synCnin (Class.cv (nb067AlphaDummy256)) (Class.cv (nb067AlphaDummy257)))).fv ∪
        ((synCnin (Class.cv (nb067AlphaDummy256)) (Class.cv (nb067AlphaDummy257)))).fv)
      0

theorem nb067_fresh_417 (f : Var) :
    (nb067AlphaDummy262 f) ∉
      (((synCnin (Class.cv (nb067AlphaDummy259 f))
            (Class.cv (nb067AlphaDummy260 f)))).fv ∪
        ((synCnin (Class.cv (nb067AlphaDummy259 f))
            (Class.cv (nb067AlphaDummy260 f)))).fv) :=
  by
  simpa only [nb067AlphaDummy262] using
    freshVar_not_mem
      (((synCnin (Class.cv (nb067AlphaDummy259 f))
            (Class.cv (nb067AlphaDummy260 f)))).fv ∪
        ((synCnin (Class.cv (nb067AlphaDummy259 f))
            (Class.cv (nb067AlphaDummy260 f)))).fv)
      0

theorem nb067_fresh_418 :
    (nb067AlphaDummy301) ∉
      (((synCnin (Class.cv (nb067AlphaDummy296)) (Class.cv (nb067AlphaDummy297)))).fv ∪
        ((synCnin (Class.cv (nb067AlphaDummy296))
            (Class.cv (nb067AlphaDummy297)))).fv) :=
  by
  simpa only [nb067AlphaDummy301] using
    freshVar_not_mem
      (((synCnin (Class.cv (nb067AlphaDummy296)) (Class.cv (nb067AlphaDummy297)))).fv ∪
        ((synCnin (Class.cv (nb067AlphaDummy296)) (Class.cv (nb067AlphaDummy297)))).fv)
      0

theorem nb067_fresh_419 (f : Var) :
    (nb067AlphaDummy302 f) ∉
      (((synCnin (Class.cv (nb067AlphaDummy299 f))
            (Class.cv (nb067AlphaDummy300 f)))).fv ∪
        ((synCnin (Class.cv (nb067AlphaDummy299 f))
            (Class.cv (nb067AlphaDummy300 f)))).fv) :=
  by
  simpa only [nb067AlphaDummy302] using
    freshVar_not_mem
      (((synCnin (Class.cv (nb067AlphaDummy299 f))
            (Class.cv (nb067AlphaDummy300 f)))).fv ∪
        ((synCnin (Class.cv (nb067AlphaDummy299 f))
            (Class.cv (nb067AlphaDummy300 f)))).fv)
      0

theorem nb067_fresh_420 :
    (nb067AlphaDummy345) ∉
      (((synCnin (Class.cv (nb067AlphaDummy340)) (Class.cv (nb067AlphaDummy341)))).fv ∪
        ((synCnin (Class.cv (nb067AlphaDummy340))
            (Class.cv (nb067AlphaDummy341)))).fv) :=
  by
  simpa only [nb067AlphaDummy345] using
    freshVar_not_mem
      (((synCnin (Class.cv (nb067AlphaDummy340)) (Class.cv (nb067AlphaDummy341)))).fv ∪
        ((synCnin (Class.cv (nb067AlphaDummy340)) (Class.cv (nb067AlphaDummy341)))).fv)
      0

theorem nb067_fresh_421 (f : Var) :
    (nb067AlphaDummy346 f) ∉
      (((synCnin (Class.cv (nb067AlphaDummy343 f))
            (Class.cv (nb067AlphaDummy344 f)))).fv ∪
        ((synCnin (Class.cv (nb067AlphaDummy343 f))
            (Class.cv (nb067AlphaDummy344 f)))).fv) :=
  by
  simpa only [nb067AlphaDummy346] using
    freshVar_not_mem
      (((synCnin (Class.cv (nb067AlphaDummy343 f))
            (Class.cv (nb067AlphaDummy344 f)))).fv ∪
        ((synCnin (Class.cv (nb067AlphaDummy343 f))
            (Class.cv (nb067AlphaDummy344 f)))).fv)
      0

theorem nb067_fresh_422 :
    (nb067AlphaDummy079) ∉
      (((synCnin (synCcom (Class.cv (nb067AlphaDummy000))
              (synCcnv (Class.cv (nb067AlphaDummy000)))) (synCid))).fv ∪ ((synCnin
            (synCcom (Class.cv (nb067AlphaDummy000))
              (synCcnv (Class.cv (nb067AlphaDummy000)))) (synCid))).fv) :=
  by
  simpa only [nb067AlphaDummy079] using
    freshVar_not_mem
      (((synCnin (synCcom (Class.cv (nb067AlphaDummy000))
              (synCcnv (Class.cv (nb067AlphaDummy000)))) (synCid))).fv ∪ ((synCnin
            (synCcom (Class.cv (nb067AlphaDummy000))
              (synCcnv (Class.cv (nb067AlphaDummy000)))) (synCid))).fv)
      0

theorem nb067_fresh_423 (f : Var) :
    (nb067AlphaDummy080 f) ∉
      (((synCnin (synCcom (Class.cv f) (synCcnv (Class.cv f))) (synCid))).fv ∪
        ((synCnin (synCcom (Class.cv f) (synCcnv (Class.cv f))) (synCid))).fv) :=
  by
  simpa only [nb067AlphaDummy080] using
    freshVar_not_mem
      (((synCnin (synCcom (Class.cv f) (synCcnv (Class.cv f))) (synCid))).fv ∪
        ((synCnin (synCcom (Class.cv f) (synCcnv (Class.cv f))) (synCid))).fv)
      0

theorem nb067_fresh_424 :
    (nb067AlphaDummy317) ∉
      (((synCnin (synCrn (Class.cv (nb067AlphaDummy000)))
            (Class.cv (nb067AlphaDummy001)))).fv ∪
        ((synCnin (synCrn (Class.cv (nb067AlphaDummy000)))
            (Class.cv (nb067AlphaDummy001)))).fv) :=
  by
  simpa only [nb067AlphaDummy317] using
    freshVar_not_mem
      (((synCnin (synCrn (Class.cv (nb067AlphaDummy000)))
            (Class.cv (nb067AlphaDummy001)))).fv ∪
        ((synCnin (synCrn (Class.cv (nb067AlphaDummy000)))
            (Class.cv (nb067AlphaDummy001)))).fv)
      0

theorem nb067_fresh_425 (x : Var) (f : Var) :
    (nb067AlphaDummy318 x f) ∉
      (((synCnin (synCrn (Class.cv f)) (Class.cv x))).fv ∪
        ((synCnin (synCrn (Class.cv f)) (Class.cv x))).fv) :=
  by
  simpa only [nb067AlphaDummy318] using
    freshVar_not_mem
      (((synCnin (synCrn (Class.cv f)) (Class.cv x))).fv ∪
        ((synCnin (synCrn (Class.cv f)) (Class.cv x))).fv)
      0

theorem nb067_fresh_426 :
    (nb067AlphaDummy007) ∉
      (((synCop (Class.cv (nb067AlphaDummy001)) (Class.cv (nb067AlphaDummy002)))).fv ∪
        ((Class.cv (nb067AlphaDummy003))).fv) :=
  by
  simpa only [nb067AlphaDummy007] using
    freshVar_not_mem
      (((synCop (Class.cv (nb067AlphaDummy001)) (Class.cv (nb067AlphaDummy002)))).fv ∪
        ((Class.cv (nb067AlphaDummy003))).fv)
      0

theorem nb067_fresh_427 :
    (nb067AlphaDummy008) ∉
      (((synCop (Class.cv (nb067AlphaDummy001)) (Class.cv (nb067AlphaDummy002)))).fv ∪
        ((Class.cv (nb067AlphaDummy003))).fv) :=
  by
  simpa only [nb067AlphaDummy008] using
    freshVar_not_mem
      (((synCop (Class.cv (nb067AlphaDummy001)) (Class.cv (nb067AlphaDummy002)))).fv ∪
        ((Class.cv (nb067AlphaDummy003))).fv)
      1

theorem nb067_distinct_428 : (nb067AlphaDummy007) ≠ (nb067AlphaDummy008) := by
  simpa only [nb067AlphaDummy007, nb067AlphaDummy008] using
    (freshVar_injective (((synCop (Class.cv (nb067AlphaDummy001))
            (Class.cv (nb067AlphaDummy002)))).fv ∪ ((Class.cv (nb067AlphaDummy003))).fv)
      (i := 0) (j := 1) (by decide))

theorem nb067_fresh_429 (x : Var) (y : Var) (f : Var) :
    (nb067AlphaDummy009 x y f) ∉
      (((synCop (Class.cv x) (Class.cv y))).fv ∪
        ((Class.cv (nb067AlphaDummy004 x y f))).fv) :=
  by
  simpa only [nb067AlphaDummy009] using
    freshVar_not_mem
      (((synCop (Class.cv x) (Class.cv y))).fv ∪ ((Class.cv (nb067AlphaDummy004 x y f))).fv)
      0

theorem nb067_fresh_430 (x : Var) (y : Var) (f : Var) :
    (nb067AlphaDummy010 x y f) ∉
      (((synCop (Class.cv x) (Class.cv y))).fv ∪
        ((Class.cv (nb067AlphaDummy004 x y f))).fv) :=
  by
  simpa only [nb067AlphaDummy010] using
    freshVar_not_mem
      (((synCop (Class.cv x) (Class.cv y))).fv ∪ ((Class.cv (nb067AlphaDummy004 x y f))).fv)
      1

theorem nb067_distinct_431 (x : Var) (y : Var) (f : Var) :
    (nb067AlphaDummy009 x y f) ≠ (nb067AlphaDummy010 x y f) := by
  simpa only [nb067AlphaDummy009, nb067AlphaDummy010] using
    (freshVar_injective (((synCop (Class.cv x) (Class.cv y))).fv ∪
        ((Class.cv (nb067AlphaDummy004 x y f))).fv) (i := 0) (j := 1) (by decide))

theorem nb067_fresh_432 :
    (nb067AlphaDummy077) ∉
      (((synCphi (Class.cv (nb067AlphaDummy008)))).fv ∪
        ((synCphi (Class.cv (nb067AlphaDummy008)))).fv) :=
  by
  simpa only [nb067AlphaDummy077] using
    freshVar_not_mem
      (((synCphi (Class.cv (nb067AlphaDummy008)))).fv ∪
        ((synCphi (Class.cv (nb067AlphaDummy008)))).fv)
      0

theorem nb067_fresh_433 (x : Var) (y : Var) (f : Var) :
    (nb067AlphaDummy078 x y f) ∉
      (((synCphi (Class.cv (nb067AlphaDummy010 x y f)))).fv ∪
        ((synCphi (Class.cv (nb067AlphaDummy010 x y f)))).fv) :=
  by
  simpa only [nb067AlphaDummy078] using
    freshVar_not_mem
      (((synCphi (Class.cv (nb067AlphaDummy010 x y f)))).fv ∪
        ((synCphi (Class.cv (nb067AlphaDummy010 x y f)))).fv)
      0

theorem nb067_fresh_434 :
    (nb067AlphaDummy049) ∉
      (((synCphi (Class.cv (nb067AlphaDummy016)))).fv ∪
        ((synCphi (Class.cv (nb067AlphaDummy016)))).fv) :=
  by
  simpa only [nb067AlphaDummy049] using
    freshVar_not_mem
      (((synCphi (Class.cv (nb067AlphaDummy016)))).fv ∪
        ((synCphi (Class.cv (nb067AlphaDummy016)))).fv)
      0

theorem nb067_fresh_435 (x : Var) (y : Var) :
    (nb067AlphaDummy050 x y) ∉
      (((synCphi (Class.cv (nb067AlphaDummy018 x y)))).fv ∪
        ((synCphi (Class.cv (nb067AlphaDummy018 x y)))).fv) :=
  by
  simpa only [nb067AlphaDummy050] using
    freshVar_not_mem
      (((synCphi (Class.cv (nb067AlphaDummy018 x y)))).fv ∪
        ((synCphi (Class.cv (nb067AlphaDummy018 x y)))).fv)
      0

theorem nb067_fresh_436 :
    (nb067AlphaDummy125) ∉
      (((synCphi (Class.cv (nb067AlphaDummy092)))).fv ∪
        ((synCphi (Class.cv (nb067AlphaDummy092)))).fv) :=
  by
  simpa only [nb067AlphaDummy125] using
    freshVar_not_mem
      (((synCphi (Class.cv (nb067AlphaDummy092)))).fv ∪
        ((synCphi (Class.cv (nb067AlphaDummy092)))).fv)
      0

theorem nb067_fresh_437 (f : Var) :
    (nb067AlphaDummy126 f) ∉
      (((synCphi (Class.cv (nb067AlphaDummy094 f)))).fv ∪
        ((synCphi (Class.cv (nb067AlphaDummy094 f)))).fv) :=
  by
  simpa only [nb067AlphaDummy126] using
    freshVar_not_mem
      (((synCphi (Class.cv (nb067AlphaDummy094 f)))).fv ∪
        ((synCphi (Class.cv (nb067AlphaDummy094 f)))).fv)
      0

theorem nb067_fresh_438 :
    (nb067AlphaDummy161) ∉
      (((synCphi (Class.cv (nb067AlphaDummy128)))).fv ∪
        ((synCphi (Class.cv (nb067AlphaDummy128)))).fv) :=
  by
  simpa only [nb067AlphaDummy161] using
    freshVar_not_mem
      (((synCphi (Class.cv (nb067AlphaDummy128)))).fv ∪
        ((synCphi (Class.cv (nb067AlphaDummy128)))).fv)
      0

theorem nb067_fresh_439 (f : Var) :
    (nb067AlphaDummy162 f) ∉
      (((synCphi (Class.cv (nb067AlphaDummy130 f)))).fv ∪
        ((synCphi (Class.cv (nb067AlphaDummy130 f)))).fv) :=
  by
  simpa only [nb067AlphaDummy162] using
    freshVar_not_mem
      (((synCphi (Class.cv (nb067AlphaDummy130 f)))).fv ∪
        ((synCphi (Class.cv (nb067AlphaDummy130 f)))).fv)
      0

theorem nb067_fresh_440 :
    (nb067AlphaDummy203) ∉
      (((synCphi (Class.cv (nb067AlphaDummy170)))).fv ∪
        ((synCphi (Class.cv (nb067AlphaDummy170)))).fv) :=
  by
  simpa only [nb067AlphaDummy203] using
    freshVar_not_mem
      (((synCphi (Class.cv (nb067AlphaDummy170)))).fv ∪
        ((synCphi (Class.cv (nb067AlphaDummy170)))).fv)
      0

theorem nb067_fresh_441 (f : Var) :
    (nb067AlphaDummy204 f) ∉
      (((synCphi (Class.cv (nb067AlphaDummy172 f)))).fv ∪
        ((synCphi (Class.cv (nb067AlphaDummy172 f)))).fv) :=
  by
  simpa only [nb067AlphaDummy204] using
    freshVar_not_mem
      (((synCphi (Class.cv (nb067AlphaDummy172 f)))).fv ∪
        ((synCphi (Class.cv (nb067AlphaDummy172 f)))).fv)
      0

theorem nb067_fresh_442 :
    (nb067AlphaDummy239) ∉
      (((synCphi (Class.cv (nb067AlphaDummy206)))).fv ∪
        ((synCphi (Class.cv (nb067AlphaDummy206)))).fv) :=
  by
  simpa only [nb067AlphaDummy239] using
    freshVar_not_mem
      (((synCphi (Class.cv (nb067AlphaDummy206)))).fv ∪
        ((synCphi (Class.cv (nb067AlphaDummy206)))).fv)
      0

theorem nb067_fresh_443 (f : Var) :
    (nb067AlphaDummy240 f) ∉
      (((synCphi (Class.cv (nb067AlphaDummy208 f)))).fv ∪
        ((synCphi (Class.cv (nb067AlphaDummy208 f)))).fv) :=
  by
  simpa only [nb067AlphaDummy240] using
    freshVar_not_mem
      (((synCphi (Class.cv (nb067AlphaDummy208 f)))).fv ∪
        ((synCphi (Class.cv (nb067AlphaDummy208 f)))).fv)
      0

theorem nb067_fresh_444 :
    (nb067AlphaDummy275) ∉
      (((synCphi (Class.cv (nb067AlphaDummy242)))).fv ∪
        ((synCphi (Class.cv (nb067AlphaDummy242)))).fv) :=
  by
  simpa only [nb067AlphaDummy275] using
    freshVar_not_mem
      (((synCphi (Class.cv (nb067AlphaDummy242)))).fv ∪
        ((synCphi (Class.cv (nb067AlphaDummy242)))).fv)
      0

theorem nb067_fresh_445 (f : Var) :
    (nb067AlphaDummy276 f) ∉
      (((synCphi (Class.cv (nb067AlphaDummy244 f)))).fv ∪
        ((synCphi (Class.cv (nb067AlphaDummy244 f)))).fv) :=
  by
  simpa only [nb067AlphaDummy276] using
    freshVar_not_mem
      (((synCphi (Class.cv (nb067AlphaDummy244 f)))).fv ∪
        ((synCphi (Class.cv (nb067AlphaDummy244 f)))).fv)
      0

theorem nb067_fresh_446 :
    (nb067AlphaDummy315) ∉
      (((synCphi (Class.cv (nb067AlphaDummy282)))).fv ∪
        ((synCphi (Class.cv (nb067AlphaDummy282)))).fv) :=
  by
  simpa only [nb067AlphaDummy315] using
    freshVar_not_mem
      (((synCphi (Class.cv (nb067AlphaDummy282)))).fv ∪
        ((synCphi (Class.cv (nb067AlphaDummy282)))).fv)
      0

theorem nb067_fresh_447 (f : Var) :
    (nb067AlphaDummy316 f) ∉
      (((synCphi (Class.cv (nb067AlphaDummy284 f)))).fv ∪
        ((synCphi (Class.cv (nb067AlphaDummy284 f)))).fv) :=
  by
  simpa only [nb067AlphaDummy316] using
    freshVar_not_mem
      (((synCphi (Class.cv (nb067AlphaDummy284 f)))).fv ∪
        ((synCphi (Class.cv (nb067AlphaDummy284 f)))).fv)
      0

theorem nb067_fresh_448 :
    (nb067AlphaDummy359) ∉
      (((synCphi (Class.cv (nb067AlphaDummy326)))).fv ∪
        ((synCphi (Class.cv (nb067AlphaDummy326)))).fv) :=
  by
  simpa only [nb067AlphaDummy359] using
    freshVar_not_mem
      (((synCphi (Class.cv (nb067AlphaDummy326)))).fv ∪
        ((synCphi (Class.cv (nb067AlphaDummy326)))).fv)
      0

theorem nb067_fresh_449 (f : Var) :
    (nb067AlphaDummy360 f) ∉
      (((synCphi (Class.cv (nb067AlphaDummy328 f)))).fv ∪
        ((synCphi (Class.cv (nb067AlphaDummy328 f)))).fv) :=
  by
  simpa only [nb067AlphaDummy360] using
    freshVar_not_mem
      (((synCphi (Class.cv (nb067AlphaDummy328 f)))).fv ∪
        ((synCphi (Class.cv (nb067AlphaDummy328 f)))).fv)
      0

theorem nb067_fresh_450 :
    (nb067AlphaDummy319) ∉
      (((synCrn (Class.cv (nb067AlphaDummy000)))).fv ∪
        ((Class.cv (nb067AlphaDummy001))).fv) :=
  by
  simpa only [nb067AlphaDummy319] using
    freshVar_not_mem
      (((synCrn (Class.cv (nb067AlphaDummy000)))).fv ∪
        ((Class.cv (nb067AlphaDummy001))).fv)
      0

theorem nb067_fresh_451 (x : Var) (f : Var) :
    (nb067AlphaDummy320 x f) ∉ (((synCrn (Class.cv f))).fv ∪ ((Class.cv x)).fv) := by
  simpa only [nb067AlphaDummy320] using
    freshVar_not_mem (((synCrn (Class.cv f))).fv ∪ ((Class.cv x)).fv) 0

theorem nb067_fresh_452 :
    (nb067AlphaDummy003) ∉
      (({(nb067AlphaDummy001)} : Finset Var) ∪ ((synCvv)).fv ∪
            ({(nb067AlphaDummy002)} : Finset Var) ∪ ((synCvv)).fv ∪
        ((Class.cab (nb067AlphaDummy000)
            (synWf (Class.cv (nb067AlphaDummy000)) (Class.cv (nb067AlphaDummy002))
              (Class.cv (nb067AlphaDummy001))))).fv) :=
  by
  simpa only [nb067AlphaDummy003] using
    freshVar_not_mem
      (({(nb067AlphaDummy001)} : Finset Var) ∪ ((synCvv)).fv ∪
            ({(nb067AlphaDummy002)} : Finset Var) ∪ ((synCvv)).fv ∪
        ((Class.cab (nb067AlphaDummy000)
            (synWf (Class.cv (nb067AlphaDummy000)) (Class.cv (nb067AlphaDummy002))
              (Class.cv (nb067AlphaDummy001))))).fv)
      0

theorem nb067_fresh_453 :
    (nb067AlphaDummy005) ∉
      (({(nb067AlphaDummy001)} : Finset Var) ∪ ({(nb067AlphaDummy002)} : Finset Var) ∪
          ({(nb067AlphaDummy003)} : Finset Var) ∪ ((synWa
            (synWa (Wff.classMem (Class.cv (nb067AlphaDummy001)) (synCvv))
              (Wff.classMem (Class.cv (nb067AlphaDummy002)) (synCvv)))
            (Wff.classEq (Class.cv (nb067AlphaDummy003)) (Class.cab (nb067AlphaDummy000)
                (synWf (Class.cv (nb067AlphaDummy000)) (Class.cv (nb067AlphaDummy002))
                  (Class.cv (nb067AlphaDummy001))))))).fv) :=
  by
  simpa only [nb067AlphaDummy005] using
    freshVar_not_mem
      (({(nb067AlphaDummy001)} : Finset Var) ∪ ({(nb067AlphaDummy002)} : Finset Var) ∪
          ({(nb067AlphaDummy003)} : Finset Var) ∪ ((synWa
            (synWa (Wff.classMem (Class.cv (nb067AlphaDummy001)) (synCvv))
              (Wff.classMem (Class.cv (nb067AlphaDummy002)) (synCvv)))
            (Wff.classEq (Class.cv (nb067AlphaDummy003)) (Class.cab (nb067AlphaDummy000)
                (synWf (Class.cv (nb067AlphaDummy000)) (Class.cv (nb067AlphaDummy002))
                  (Class.cv (nb067AlphaDummy001))))))).fv)
      0

theorem nb067_fresh_454 :
    (nb067AlphaDummy089) ∉
      (({(nb067AlphaDummy083)} : Finset Var) ∪ ({(nb067AlphaDummy084)} : Finset Var) ∪
        ((synWex (nb067AlphaDummy085) (synWa (synWbr (Class.cv (nb067AlphaDummy083))
                (synCcnv (Class.cv (nb067AlphaDummy000)))
                (Class.cv (nb067AlphaDummy085))) (synWbr (Class.cv (nb067AlphaDummy085))
                (Class.cv (nb067AlphaDummy000)) (Class.cv (nb067AlphaDummy084)))))).fv) :=
  by
  simpa only [nb067AlphaDummy089] using
    freshVar_not_mem
      (({(nb067AlphaDummy083)} : Finset Var) ∪ ({(nb067AlphaDummy084)} : Finset Var) ∪
        ((synWex (nb067AlphaDummy085) (synWa (synWbr (Class.cv (nb067AlphaDummy083))
                (synCcnv (Class.cv (nb067AlphaDummy000)))
                (Class.cv (nb067AlphaDummy085))) (synWbr (Class.cv (nb067AlphaDummy085))
                (Class.cv (nb067AlphaDummy000)) (Class.cv (nb067AlphaDummy084)))))).fv)
      0

theorem nb067_fresh_455 (f : Var) :
    (nb067AlphaDummy090 f) ∉
      (({(nb067AlphaDummy086 f)} : Finset Var) ∪ ({(nb067AlphaDummy087 f)} : Finset Var) ∪
        ((synWex (nb067AlphaDummy088 f) (synWa
              (synWbr (Class.cv (nb067AlphaDummy086 f)) (synCcnv (Class.cv f))
                (Class.cv (nb067AlphaDummy088 f)))
              (synWbr (Class.cv (nb067AlphaDummy088 f)) (Class.cv f)
                (Class.cv (nb067AlphaDummy087 f)))))).fv) :=
  by
  simpa only [nb067AlphaDummy090] using
    freshVar_not_mem
      (({(nb067AlphaDummy086 f)} : Finset Var) ∪ ({(nb067AlphaDummy087 f)} : Finset Var) ∪
        ((synWex (nb067AlphaDummy088 f) (synWa
              (synWbr (Class.cv (nb067AlphaDummy086 f)) (synCcnv (Class.cv f))
                (Class.cv (nb067AlphaDummy088 f)))
              (synWbr (Class.cv (nb067AlphaDummy088 f)) (Class.cv f)
                (Class.cv (nb067AlphaDummy087 f)))))).fv)
      0

theorem nb067_fresh_456 :
    (nb067AlphaDummy167) ∉
      (({(nb067AlphaDummy163)} : Finset Var) ∪ ({(nb067AlphaDummy164)} : Finset Var) ∪
        ((synWbr (Class.cv (nb067AlphaDummy164)) (Class.cv (nb067AlphaDummy000))
            (Class.cv (nb067AlphaDummy163)))).fv) :=
  by
  simpa only [nb067AlphaDummy167] using
    freshVar_not_mem
      (({(nb067AlphaDummy163)} : Finset Var) ∪ ({(nb067AlphaDummy164)} : Finset Var) ∪
        ((synWbr (Class.cv (nb067AlphaDummy164)) (Class.cv (nb067AlphaDummy000))
            (Class.cv (nb067AlphaDummy163)))).fv)
      0

theorem nb067_fresh_457 (f : Var) :
    (nb067AlphaDummy168 f) ∉
      (({(nb067AlphaDummy165 f)} : Finset Var) ∪ ({(nb067AlphaDummy166 f)} : Finset Var) ∪
        ((synWbr (Class.cv (nb067AlphaDummy166 f)) (Class.cv f)
            (Class.cv (nb067AlphaDummy165 f)))).fv) :=
  by
  simpa only [nb067AlphaDummy168] using
    freshVar_not_mem
      (({(nb067AlphaDummy165 f)} : Finset Var) ∪ ({(nb067AlphaDummy166 f)} : Finset Var) ∪
        ((synWbr (Class.cv (nb067AlphaDummy166 f)) (Class.cv f)
            (Class.cv (nb067AlphaDummy165 f)))).fv)
      0

theorem nb067_fresh_458 (x : Var) (y : Var) (f : Var) :
    (nb067AlphaDummy004 x y f) ∉
      (({ x } : Finset Var) ∪ ((synCvv)).fv ∪ ({ y } : Finset Var) ∪ ((synCvv)).fv ∪
        ((Class.cab f (synWf (Class.cv f) (Class.cv y) (Class.cv x)))).fv) :=
  by
  simpa only [nb067AlphaDummy004] using
    freshVar_not_mem
      (({ x } : Finset Var) ∪ ((synCvv)).fv ∪ ({ y } : Finset Var) ∪ ((synCvv)).fv ∪
        ((Class.cab f (synWf (Class.cv f) (Class.cv y) (Class.cv x)))).fv)
      0

theorem nb067_fresh_459 (x : Var) (y : Var) (f : Var) :
    (nb067AlphaDummy006 x y f) ∉
      (({ x } : Finset Var) ∪ ({ y } : Finset Var) ∪
          ({(nb067AlphaDummy004 x y f)} : Finset Var) ∪ ((synWa
            (synWa (Wff.classMem (Class.cv x) (synCvv)) (Wff.classMem (Class.cv y) (synCvv)))
            (Wff.classEq (Class.cv (nb067AlphaDummy004 x y f))
              (Class.cab f (synWf (Class.cv f) (Class.cv y) (Class.cv x)))))).fv) :=
  by
  simpa only [nb067AlphaDummy006] using
    freshVar_not_mem
      (({ x } : Finset Var) ∪ ({ y } : Finset Var) ∪
          ({(nb067AlphaDummy004 x y f)} : Finset Var) ∪ ((synWa
            (synWa (Wff.classMem (Class.cv x) (synCvv)) (Wff.classMem (Class.cv y) (synCvv)))
            (Wff.classEq (Class.cv (nb067AlphaDummy004 x y f))
              (Class.cab f (synWf (Class.cv f) (Class.cv y) (Class.cv x)))))).fv)
      0

theorem nb067_fresh_460 : (nb067AlphaDummy000) ∉ ((∅ : Finset Var)) := by
  simpa only [nb067AlphaDummy000] using freshVar_not_mem ((∅ : Finset Var)) 0

theorem nb067_fresh_461 : (nb067AlphaDummy001) ∉ ((∅ : Finset Var)) := by
  simpa only [nb067AlphaDummy001] using freshVar_not_mem ((∅ : Finset Var)) 1

theorem nb067_fresh_462 : (nb067AlphaDummy002) ∉ ((∅ : Finset Var)) := by
  simpa only [nb067AlphaDummy002] using freshVar_not_mem ((∅ : Finset Var)) 2

theorem nb067_distinct_463 : (nb067AlphaDummy000) ≠ (nb067AlphaDummy001) := by
  simpa only [nb067AlphaDummy000, nb067AlphaDummy001] using
    (freshVar_injective ((∅ : Finset Var)) (i := 0) (j := 1) (by decide))

theorem nb067_distinct_464 : (nb067AlphaDummy000) ≠ (nb067AlphaDummy002) := by
  simpa only [nb067AlphaDummy000, nb067AlphaDummy002] using
    (freshVar_injective ((∅ : Finset Var)) (i := 0) (j := 2) (by decide))

theorem nb067_distinct_465 : (nb067AlphaDummy001) ≠ (nb067AlphaDummy002) := by
  simpa only [nb067AlphaDummy001, nb067AlphaDummy002] using
    (freshVar_injective ((∅ : Finset Var)) (i := 1) (j := 2) (by decide))

theorem nb067_support_mem_0000 :
    (nb067AlphaDummy001) ∈
      (({(nb067AlphaDummy001)} : Finset Var) ∪ ({(nb067AlphaDummy002)} : Finset Var) ∪
          ({(nb067AlphaDummy003)} : Finset Var) ∪ ((synWa
            (synWa (Wff.classMem (Class.cv (nb067AlphaDummy001)) (synCvv))
              (Wff.classMem (Class.cv (nb067AlphaDummy002)) (synCvv)))
            (Wff.classEq (Class.cv (nb067AlphaDummy003)) (Class.cab (nb067AlphaDummy000)
                (synWf (Class.cv (nb067AlphaDummy000)) (Class.cv (nb067AlphaDummy002))
                  (Class.cv (nb067AlphaDummy001))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  with_reducible rw [Finset.mem_union]
  left
  with_reducible rw [Finset.mem_union]
  left
  exact Finset.mem_singleton_self _

theorem nb067_support_mem_0001 (x : Var) (y : Var) (f : Var) :
    x ∈
      (({ x } : Finset Var) ∪ ({ y } : Finset Var) ∪
          ({(nb067AlphaDummy004 x y f)} : Finset Var) ∪ ((synWa
            (synWa (Wff.classMem (Class.cv x) (synCvv)) (Wff.classMem (Class.cv y) (synCvv)))
            (Wff.classEq (Class.cv (nb067AlphaDummy004 x y f))
              (Class.cab f (synWf (Class.cv f) (Class.cv y) (Class.cv x)))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  with_reducible rw [Finset.mem_union]
  left
  with_reducible rw [Finset.mem_union]
  left
  exact Finset.mem_singleton_self _

theorem nb067_support_mem_0002 :
    (nb067AlphaDummy002) ∈
      (({(nb067AlphaDummy001)} : Finset Var) ∪ ({(nb067AlphaDummy002)} : Finset Var) ∪
          ({(nb067AlphaDummy003)} : Finset Var) ∪ ((synWa
            (synWa (Wff.classMem (Class.cv (nb067AlphaDummy001)) (synCvv))
              (Wff.classMem (Class.cv (nb067AlphaDummy002)) (synCvv)))
            (Wff.classEq (Class.cv (nb067AlphaDummy003)) (Class.cab (nb067AlphaDummy000)
                (synWf (Class.cv (nb067AlphaDummy000)) (Class.cv (nb067AlphaDummy002))
                  (Class.cv (nb067AlphaDummy001))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  with_reducible rw [Finset.mem_union]
  left
  with_reducible rw [Finset.mem_union]
  right
  exact Finset.mem_singleton_self _

theorem nb067_support_mem_0003 (x : Var) (y : Var) (f : Var) :
    y ∈
      (({ x } : Finset Var) ∪ ({ y } : Finset Var) ∪
          ({(nb067AlphaDummy004 x y f)} : Finset Var) ∪ ((synWa
            (synWa (Wff.classMem (Class.cv x) (synCvv)) (Wff.classMem (Class.cv y) (synCvv)))
            (Wff.classEq (Class.cv (nb067AlphaDummy004 x y f))
              (Class.cab f (synWf (Class.cv f) (Class.cv y) (Class.cv x)))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  with_reducible rw [Finset.mem_union]
  left
  with_reducible rw [Finset.mem_union]
  right
  exact Finset.mem_singleton_self _

theorem nb067_support_mem_0004 :
    (nb067AlphaDummy003) ∈
      (({(nb067AlphaDummy001)} : Finset Var) ∪ ({(nb067AlphaDummy002)} : Finset Var) ∪
          ({(nb067AlphaDummy003)} : Finset Var) ∪ ((synWa
            (synWa (Wff.classMem (Class.cv (nb067AlphaDummy001)) (synCvv))
              (Wff.classMem (Class.cv (nb067AlphaDummy002)) (synCvv)))
            (Wff.classEq (Class.cv (nb067AlphaDummy003)) (Class.cab (nb067AlphaDummy000)
                (synWf (Class.cv (nb067AlphaDummy000)) (Class.cv (nb067AlphaDummy002))
                  (Class.cv (nb067AlphaDummy001))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  with_reducible rw [Finset.mem_union]
  right
  exact Finset.mem_singleton_self _

theorem nb067_support_mem_0005 (x : Var) (y : Var) (f : Var) :
    (nb067AlphaDummy004 x y f) ∈
      (({ x } : Finset Var) ∪ ({ y } : Finset Var) ∪
          ({(nb067AlphaDummy004 x y f)} : Finset Var) ∪ ((synWa
            (synWa (Wff.classMem (Class.cv x) (synCvv)) (Wff.classMem (Class.cv y) (synCvv)))
            (Wff.classEq (Class.cv (nb067AlphaDummy004 x y f))
              (Class.cab f (synWf (Class.cv f) (Class.cv y) (Class.cv x)))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  with_reducible rw [Finset.mem_union]
  right
  exact Finset.mem_singleton_self _

theorem nb067_support_mem_0006 :
    (nb067AlphaDummy001) ∈
      (({(nb067AlphaDummy001)} : Finset Var) ∪ ((synCvv)).fv ∪
            ({(nb067AlphaDummy002)} : Finset Var) ∪ ((synCvv)).fv ∪
        ((Class.cab (nb067AlphaDummy000)
            (synWf (Class.cv (nb067AlphaDummy000)) (Class.cv (nb067AlphaDummy002))
              (Class.cv (nb067AlphaDummy001))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  with_reducible rw [Finset.mem_union]
  left
  with_reducible rw [Finset.mem_union]
  left
  with_reducible rw [Finset.mem_union]
  left
  exact Finset.mem_singleton_self _

theorem nb067_support_mem_0007 (x : Var) (y : Var) (f : Var) :
    x ∈
      (({ x } : Finset Var) ∪ ((synCvv)).fv ∪ ({ y } : Finset Var) ∪ ((synCvv)).fv ∪
        ((Class.cab f (synWf (Class.cv f) (Class.cv y) (Class.cv x)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  with_reducible rw [Finset.mem_union]
  left
  with_reducible rw [Finset.mem_union]
  left
  with_reducible rw [Finset.mem_union]
  left
  exact Finset.mem_singleton_self _

theorem nb067_support_mem_0008 :
    (nb067AlphaDummy001) ∈
      (((synCop (Class.cv (nb067AlphaDummy001)) (Class.cv (nb067AlphaDummy002)))).fv ∪
        ((Class.cv (nb067AlphaDummy003))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cop]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb067_support_mem_0009 :
    (nb067AlphaDummy001) ∈
      (((synCcompl (Class.cab (nb067AlphaDummy007) (synWrex (nb067AlphaDummy008)
                (synCop (Class.cv (nb067AlphaDummy001)) (Class.cv (nb067AlphaDummy002)))
                (Wff.classEq (Class.cv (nb067AlphaDummy007))
                  (synCphi (Class.cv (nb067AlphaDummy008)))))))).fv ∪ ((synCcompl
            (Class.cab (nb067AlphaDummy007)
              (synWrex (nb067AlphaDummy008) (Class.cv (nb067AlphaDummy003))
                (Wff.classEq (Class.cv (nb067AlphaDummy007))
                  (synCun (synCphi (Class.cv (nb067AlphaDummy008)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0008) 0))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0008) 1))
    · rw [fv_syn_cop]
      with_reducible rw [Finset.mem_union]
      left
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb067_support_mem_0010 (x : Var) (y : Var) (f : Var) :
    x ∈
      (((synCop (Class.cv x) (Class.cv y))).fv ∪
        ((Class.cv (nb067AlphaDummy004 x y f))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cop]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb067_support_mem_0011 (x : Var) (y : Var) (f : Var) :
    x ∈
      (((synCcompl (Class.cab (nb067AlphaDummy009 x y f)
              (synWrex (nb067AlphaDummy010 x y f) (synCop (Class.cv x) (Class.cv y))
                (Wff.classEq (Class.cv (nb067AlphaDummy009 x y f))
                  (synCphi (Class.cv (nb067AlphaDummy010 x y f)))))))).fv ∪ ((synCcompl
            (Class.cab (nb067AlphaDummy009 x y f) (synWrex (nb067AlphaDummy010 x y f)
                (Class.cv (nb067AlphaDummy004 x y f))
                (Wff.classEq (Class.cv (nb067AlphaDummy009 x y f))
                  (synCun (synCphi (Class.cv (nb067AlphaDummy010 x y f)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0010 x y f) 0))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0010 x y f) 1))
    · rw [fv_syn_cop]
      with_reducible rw [Finset.mem_union]
      left
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb067_support_mem_0012 :
    (nb067AlphaDummy001) ∈
      (((Class.cab (nb067AlphaDummy007) (synWrex (nb067AlphaDummy008)
              (synCop (Class.cv (nb067AlphaDummy001)) (Class.cv (nb067AlphaDummy002)))
              (Wff.classEq (Class.cv (nb067AlphaDummy007))
                (synCphi (Class.cv (nb067AlphaDummy008))))))).fv ∪
        ((Class.cab (nb067AlphaDummy007) (synWrex (nb067AlphaDummy008)
              (synCop (Class.cv (nb067AlphaDummy001)) (Class.cv (nb067AlphaDummy002)))
              (Wff.classEq (Class.cv (nb067AlphaDummy007))
                (synCphi (Class.cv (nb067AlphaDummy008))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0008) 0))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0008) 1))
    · rw [fv_syn_cop]
      with_reducible rw [Finset.mem_union]
      left
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb067_support_mem_0013 (x : Var) (y : Var) (f : Var) :
    x ∈
      (((Class.cab (nb067AlphaDummy009 x y f)
            (synWrex (nb067AlphaDummy010 x y f) (synCop (Class.cv x) (Class.cv y))
              (Wff.classEq (Class.cv (nb067AlphaDummy009 x y f))
                (synCphi (Class.cv (nb067AlphaDummy010 x y f))))))).fv ∪
        ((Class.cab (nb067AlphaDummy009 x y f)
            (synWrex (nb067AlphaDummy010 x y f) (synCop (Class.cv x) (Class.cv y))
              (Wff.classEq (Class.cv (nb067AlphaDummy009 x y f))
                (synCphi (Class.cv (nb067AlphaDummy010 x y f))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0010 x y f) 0))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0010 x y f) 1))
    · rw [fv_syn_cop]
      with_reducible rw [Finset.mem_union]
      left
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb067_support_mem_0014 :
    (nb067AlphaDummy001) ∈
      (((Class.cv (nb067AlphaDummy001))).fv ∪ ((Class.cv (nb067AlphaDummy002))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb067_support_mem_0015 :
    (nb067AlphaDummy001) ∈
      (((synCcompl (Class.cab (nb067AlphaDummy015)
              (synWrex (nb067AlphaDummy016) (Class.cv (nb067AlphaDummy001))
                (Wff.classEq (Class.cv (nb067AlphaDummy015))
                  (synCphi (Class.cv (nb067AlphaDummy016)))))))).fv ∪ ((synCcompl
            (Class.cab (nb067AlphaDummy015)
              (synWrex (nb067AlphaDummy016) (Class.cv (nb067AlphaDummy002))
                (Wff.classEq (Class.cv (nb067AlphaDummy015))
                  (synCun (synCphi (Class.cv (nb067AlphaDummy016)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0014) 0))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0014) 1))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb067_support_mem_0016 (x : Var) (y : Var) :
    x ∈ (((Class.cv x)).fv ∪ ((Class.cv y)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb067_support_mem_0017 (x : Var) (y : Var) :
    x ∈
      (((synCcompl (Class.cab (nb067AlphaDummy017 x y)
              (synWrex (nb067AlphaDummy018 x y) (Class.cv x)
                (Wff.classEq (Class.cv (nb067AlphaDummy017 x y))
                  (synCphi (Class.cv (nb067AlphaDummy018 x y)))))))).fv ∪ ((synCcompl
            (Class.cab (nb067AlphaDummy017 x y)
              (synWrex (nb067AlphaDummy018 x y) (Class.cv y)
                (Wff.classEq (Class.cv (nb067AlphaDummy017 x y))
                  (synCun (synCphi (Class.cv (nb067AlphaDummy018 x y)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0016 x y) 0))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0016 x y) 1))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb067_support_mem_0018 :
    (nb067AlphaDummy001) ∈
      (((Class.cab (nb067AlphaDummy015)
            (synWrex (nb067AlphaDummy016) (Class.cv (nb067AlphaDummy001))
              (Wff.classEq (Class.cv (nb067AlphaDummy015))
                (synCphi (Class.cv (nb067AlphaDummy016))))))).fv ∪
        ((Class.cab (nb067AlphaDummy015)
            (synWrex (nb067AlphaDummy016) (Class.cv (nb067AlphaDummy001))
              (Wff.classEq (Class.cv (nb067AlphaDummy015))
                (synCphi (Class.cv (nb067AlphaDummy016))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0014) 0))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0014) 1))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb067_support_mem_0019 (x : Var) (y : Var) :
    x ∈
      (((Class.cab (nb067AlphaDummy017 x y)
            (synWrex (nb067AlphaDummy018 x y) (Class.cv x)
              (Wff.classEq (Class.cv (nb067AlphaDummy017 x y))
                (synCphi (Class.cv (nb067AlphaDummy018 x y))))))).fv ∪
        ((Class.cab (nb067AlphaDummy017 x y)
            (synWrex (nb067AlphaDummy018 x y) (Class.cv x)
              (Wff.classEq (Class.cv (nb067AlphaDummy017 x y))
                (synCphi (Class.cv (nb067AlphaDummy018 x y))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0016 x y) 0))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0016 x y) 1))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb067_support_mem_0020 :
    (nb067AlphaDummy016) ∈ (((Class.cv (nb067AlphaDummy016))).fv) :=
  by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb067_support_mem_0021 (x : Var) (y : Var) :
    (nb067AlphaDummy018 x y) ∈ (((Class.cv (nb067AlphaDummy018 x y))).fv) :=
  by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb067_support_mem_0022 :
    (nb067AlphaDummy023) ∈
      (((Wff.classMem (Class.cv (nb067AlphaDummy023)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb067AlphaDummy023)) (synC1c))).fv ∪
        ((Class.cv (nb067AlphaDummy023))).fv) :=
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

theorem nb067_support_mem_0023 (x : Var) (y : Var) :
    (nb067AlphaDummy025 x y) ∈
      (((Wff.classMem (Class.cv (nb067AlphaDummy025 x y)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb067AlphaDummy025 x y)) (synC1c))).fv ∪
        ((Class.cv (nb067AlphaDummy025 x y))).fv) :=
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

theorem nb067_support_mem_0024 :
    (nb067AlphaDummy023) ∈
      (((Class.cv (nb067AlphaDummy023))).fv ∪ ((synC1c)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb067_support_mem_0025 (x : Var) (y : Var) :
    (nb067AlphaDummy025 x y) ∈
      (((Class.cv (nb067AlphaDummy025 x y))).fv ∪ ((synC1c)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb067_support_mem_0026 :
    (nb067AlphaDummy030) ∈
      (((synCnin (Class.cv (nb067AlphaDummy030)) (Class.cv (nb067AlphaDummy031)))).fv ∪
        ((synCnin (Class.cv (nb067AlphaDummy030))
            (Class.cv (nb067AlphaDummy031)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb067_support_mem_0027 (x : Var) (y : Var) :
    (nb067AlphaDummy033 x y) ∈
      (((synCnin (Class.cv (nb067AlphaDummy033 x y))
            (Class.cv (nb067AlphaDummy034 x y)))).fv ∪
        ((synCnin (Class.cv (nb067AlphaDummy033 x y))
            (Class.cv (nb067AlphaDummy034 x y)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb067_support_mem_0028 :
    (nb067AlphaDummy030) ∈
      (((Class.cv (nb067AlphaDummy030))).fv ∪ ((Class.cv (nb067AlphaDummy031))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb067_support_mem_0029 (x : Var) (y : Var) :
    (nb067AlphaDummy033 x y) ∈
      (((Class.cv (nb067AlphaDummy033 x y))).fv ∪
        ((Class.cv (nb067AlphaDummy034 x y))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb067_support_mem_0030 :
    (nb067AlphaDummy031) ∈
      (((synCnin (Class.cv (nb067AlphaDummy030)) (Class.cv (nb067AlphaDummy031)))).fv ∪
        ((synCnin (Class.cv (nb067AlphaDummy030))
            (Class.cv (nb067AlphaDummy031)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb067_support_mem_0031 (x : Var) (y : Var) :
    (nb067AlphaDummy034 x y) ∈
      (((synCnin (Class.cv (nb067AlphaDummy033 x y))
            (Class.cv (nb067AlphaDummy034 x y)))).fv ∪
        ((synCnin (Class.cv (nb067AlphaDummy033 x y))
            (Class.cv (nb067AlphaDummy034 x y)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb067_support_mem_0032 :
    (nb067AlphaDummy031) ∈
      (((Class.cv (nb067AlphaDummy030))).fv ∪ ((Class.cv (nb067AlphaDummy031))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb067_support_mem_0033 (x : Var) (y : Var) :
    (nb067AlphaDummy034 x y) ∈
      (((Class.cv (nb067AlphaDummy033 x y))).fv ∪
        ((Class.cv (nb067AlphaDummy034 x y))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb067_support_mem_0034 :
    (nb067AlphaDummy030) ∈
      (((synCcompl (Class.cv (nb067AlphaDummy030)))).fv ∪
        ((synCcompl (Class.cv (nb067AlphaDummy031)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb067_support_mem_0035 (x : Var) (y : Var) :
    (nb067AlphaDummy033 x y) ∈
      (((synCcompl (Class.cv (nb067AlphaDummy033 x y)))).fv ∪
        ((synCcompl (Class.cv (nb067AlphaDummy034 x y)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb067_support_mem_0036 :
    (nb067AlphaDummy030) ∈
      (((Class.cv (nb067AlphaDummy030))).fv ∪ ((Class.cv (nb067AlphaDummy030))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb067_support_mem_0037 (x : Var) (y : Var) :
    (nb067AlphaDummy033 x y) ∈
      (((Class.cv (nb067AlphaDummy033 x y))).fv ∪
        ((Class.cv (nb067AlphaDummy033 x y))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb067_support_mem_0038 :
    (nb067AlphaDummy031) ∈
      (((synCcompl (Class.cv (nb067AlphaDummy030)))).fv ∪
        ((synCcompl (Class.cv (nb067AlphaDummy031)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb067_support_mem_0039 (x : Var) (y : Var) :
    (nb067AlphaDummy034 x y) ∈
      (((synCcompl (Class.cv (nb067AlphaDummy033 x y)))).fv ∪
        ((synCcompl (Class.cv (nb067AlphaDummy034 x y)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb067_support_mem_0040 :
    (nb067AlphaDummy031) ∈
      (((Class.cv (nb067AlphaDummy031))).fv ∪ ((Class.cv (nb067AlphaDummy031))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb067_support_mem_0041 (x : Var) (y : Var) :
    (nb067AlphaDummy034 x y) ∈
      (((Class.cv (nb067AlphaDummy034 x y))).fv ∪
        ((Class.cv (nb067AlphaDummy034 x y))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb067_support_mem_0042 :
    (nb067AlphaDummy002) ∈
      (({(nb067AlphaDummy001)} : Finset Var) ∪ ((synCvv)).fv ∪
            ({(nb067AlphaDummy002)} : Finset Var) ∪ ((synCvv)).fv ∪
        ((Class.cab (nb067AlphaDummy000)
            (synWf (Class.cv (nb067AlphaDummy000)) (Class.cv (nb067AlphaDummy002))
              (Class.cv (nb067AlphaDummy001))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  with_reducible rw [Finset.mem_union]
  left
  with_reducible rw [Finset.mem_union]
  right
  exact Finset.mem_singleton_self _

theorem nb067_support_mem_0043 (x : Var) (y : Var) (f : Var) :
    y ∈
      (({ x } : Finset Var) ∪ ((synCvv)).fv ∪ ({ y } : Finset Var) ∪ ((synCvv)).fv ∪
        ((Class.cab f (synWf (Class.cv f) (Class.cv y) (Class.cv x)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  with_reducible rw [Finset.mem_union]
  left
  with_reducible rw [Finset.mem_union]
  right
  exact Finset.mem_singleton_self _

theorem nb067_support_mem_0044 :
    (nb067AlphaDummy002) ∈
      (((synCop (Class.cv (nb067AlphaDummy001)) (Class.cv (nb067AlphaDummy002)))).fv ∪
        ((Class.cv (nb067AlphaDummy003))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cop]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired

end

/-! Certificates from `NAR4C067C001Part007`. -/


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

theorem nb067_support_mem_0045 :
    (nb067AlphaDummy002) ∈
      (((synCcompl (Class.cab (nb067AlphaDummy007) (synWrex (nb067AlphaDummy008)
                (synCop (Class.cv (nb067AlphaDummy001)) (Class.cv (nb067AlphaDummy002)))
                (Wff.classEq (Class.cv (nb067AlphaDummy007))
                  (synCphi (Class.cv (nb067AlphaDummy008)))))))).fv ∪ ((synCcompl
            (Class.cab (nb067AlphaDummy007)
              (synWrex (nb067AlphaDummy008) (Class.cv (nb067AlphaDummy003))
                (Wff.classEq (Class.cv (nb067AlphaDummy007))
                  (synCun (synCphi (Class.cv (nb067AlphaDummy008)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0044) 0))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0044) 1))
    · rw [fv_syn_cop]
      with_reducible rw [Finset.mem_union]
      right
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb067_support_mem_0046 (x : Var) (y : Var) (f : Var) :
    y ∈
      (((synCop (Class.cv x) (Class.cv y))).fv ∪
        ((Class.cv (nb067AlphaDummy004 x y f))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cop]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb067_support_mem_0047 (x : Var) (y : Var) (f : Var) :
    y ∈
      (((synCcompl (Class.cab (nb067AlphaDummy009 x y f)
              (synWrex (nb067AlphaDummy010 x y f) (synCop (Class.cv x) (Class.cv y))
                (Wff.classEq (Class.cv (nb067AlphaDummy009 x y f))
                  (synCphi (Class.cv (nb067AlphaDummy010 x y f)))))))).fv ∪ ((synCcompl
            (Class.cab (nb067AlphaDummy009 x y f) (synWrex (nb067AlphaDummy010 x y f)
                (Class.cv (nb067AlphaDummy004 x y f))
                (Wff.classEq (Class.cv (nb067AlphaDummy009 x y f))
                  (synCun (synCphi (Class.cv (nb067AlphaDummy010 x y f)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0046 x y f) 0))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0046 x y f) 1))
    · rw [fv_syn_cop]
      with_reducible rw [Finset.mem_union]
      right
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb067_support_mem_0048 :
    (nb067AlphaDummy002) ∈
      (((Class.cab (nb067AlphaDummy007) (synWrex (nb067AlphaDummy008)
              (synCop (Class.cv (nb067AlphaDummy001)) (Class.cv (nb067AlphaDummy002)))
              (Wff.classEq (Class.cv (nb067AlphaDummy007))
                (synCphi (Class.cv (nb067AlphaDummy008))))))).fv ∪
        ((Class.cab (nb067AlphaDummy007) (synWrex (nb067AlphaDummy008)
              (synCop (Class.cv (nb067AlphaDummy001)) (Class.cv (nb067AlphaDummy002)))
              (Wff.classEq (Class.cv (nb067AlphaDummy007))
                (synCphi (Class.cv (nb067AlphaDummy008))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0044) 0))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0044) 1))
    · rw [fv_syn_cop]
      with_reducible rw [Finset.mem_union]
      right
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb067_support_mem_0049 (x : Var) (y : Var) (f : Var) :
    y ∈
      (((Class.cab (nb067AlphaDummy009 x y f)
            (synWrex (nb067AlphaDummy010 x y f) (synCop (Class.cv x) (Class.cv y))
              (Wff.classEq (Class.cv (nb067AlphaDummy009 x y f))
                (synCphi (Class.cv (nb067AlphaDummy010 x y f))))))).fv ∪
        ((Class.cab (nb067AlphaDummy009 x y f)
            (synWrex (nb067AlphaDummy010 x y f) (synCop (Class.cv x) (Class.cv y))
              (Wff.classEq (Class.cv (nb067AlphaDummy009 x y f))
                (synCphi (Class.cv (nb067AlphaDummy010 x y f))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0046 x y f) 0))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0046 x y f) 1))
    · rw [fv_syn_cop]
      with_reducible rw [Finset.mem_union]
      right
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb067_support_mem_0050 :
    (nb067AlphaDummy002) ∈
      (((Class.cv (nb067AlphaDummy001))).fv ∪ ((Class.cv (nb067AlphaDummy002))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb067_support_mem_0051 :
    (nb067AlphaDummy002) ∈
      (((synCcompl (Class.cab (nb067AlphaDummy015)
              (synWrex (nb067AlphaDummy016) (Class.cv (nb067AlphaDummy001))
                (Wff.classEq (Class.cv (nb067AlphaDummy015))
                  (synCphi (Class.cv (nb067AlphaDummy016)))))))).fv ∪ ((synCcompl
            (Class.cab (nb067AlphaDummy015)
              (synWrex (nb067AlphaDummy016) (Class.cv (nb067AlphaDummy002))
                (Wff.classEq (Class.cv (nb067AlphaDummy015))
                  (synCun (synCphi (Class.cv (nb067AlphaDummy016)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0050) 0))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0050) 1))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb067_support_mem_0052 (x : Var) (y : Var) :
    y ∈ (((Class.cv x)).fv ∪ ((Class.cv y)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb067_support_mem_0053 (x : Var) (y : Var) :
    y ∈
      (((synCcompl (Class.cab (nb067AlphaDummy017 x y)
              (synWrex (nb067AlphaDummy018 x y) (Class.cv x)
                (Wff.classEq (Class.cv (nb067AlphaDummy017 x y))
                  (synCphi (Class.cv (nb067AlphaDummy018 x y)))))))).fv ∪ ((synCcompl
            (Class.cab (nb067AlphaDummy017 x y)
              (synWrex (nb067AlphaDummy018 x y) (Class.cv y)
                (Wff.classEq (Class.cv (nb067AlphaDummy017 x y))
                  (synCun (synCphi (Class.cv (nb067AlphaDummy018 x y)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0052 x y) 0))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0052 x y) 1))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb067_support_mem_0054 :
    (nb067AlphaDummy002) ∈
      (((Class.cab (nb067AlphaDummy015)
            (synWrex (nb067AlphaDummy016) (Class.cv (nb067AlphaDummy002))
              (Wff.classEq (Class.cv (nb067AlphaDummy015))
                (synCun (synCphi (Class.cv (nb067AlphaDummy016)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb067AlphaDummy015)
            (synWrex (nb067AlphaDummy016) (Class.cv (nb067AlphaDummy002))
              (Wff.classEq (Class.cv (nb067AlphaDummy015))
                (synCun (synCphi (Class.cv (nb067AlphaDummy016)))
                  (synCsn (synC0c))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0050) 0))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0050) 1))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb067_support_mem_0055 (x : Var) (y : Var) :
    y ∈
      (((Class.cab (nb067AlphaDummy017 x y)
            (synWrex (nb067AlphaDummy018 x y) (Class.cv y)
              (Wff.classEq (Class.cv (nb067AlphaDummy017 x y))
                (synCun (synCphi (Class.cv (nb067AlphaDummy018 x y)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb067AlphaDummy017 x y)
            (synWrex (nb067AlphaDummy018 x y) (Class.cv y)
              (Wff.classEq (Class.cv (nb067AlphaDummy017 x y))
                (synCun (synCphi (Class.cv (nb067AlphaDummy018 x y)))
                  (synCsn (synC0c))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0052 x y) 0))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0052 x y) 1))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb067_support_mem_0056 :
    (nb067AlphaDummy016) ∈
      (((synCcompl (synCphi (Class.cv (nb067AlphaDummy016))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb067_support_mem_0057 (x : Var) (y : Var) :
    (nb067AlphaDummy018 x y) ∈
      (((synCcompl (synCphi (Class.cv (nb067AlphaDummy018 x y))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb067_support_mem_0058 :
    (nb067AlphaDummy016) ∈
      (((synCphi (Class.cv (nb067AlphaDummy016)))).fv ∪
        ((synCphi (Class.cv (nb067AlphaDummy016)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb067_support_mem_0059 (x : Var) (y : Var) :
    (nb067AlphaDummy018 x y) ∈
      (((synCphi (Class.cv (nb067AlphaDummy018 x y)))).fv ∪
        ((synCphi (Class.cv (nb067AlphaDummy018 x y)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb067_support_mem_0060 :
    (nb067AlphaDummy008) ∈ (((Class.cv (nb067AlphaDummy008))).fv) :=
  by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb067_support_mem_0061 (x : Var) (y : Var) (f : Var) :
    (nb067AlphaDummy010 x y f) ∈ (((Class.cv (nb067AlphaDummy010 x y f))).fv) :=
  by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb067_support_mem_0062 :
    (nb067AlphaDummy051) ∈
      (((Wff.classMem (Class.cv (nb067AlphaDummy051)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb067AlphaDummy051)) (synC1c))).fv ∪
        ((Class.cv (nb067AlphaDummy051))).fv) :=
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

theorem nb067_support_mem_0063 (x : Var) (y : Var) (f : Var) :
    (nb067AlphaDummy053 x y f) ∈
      (((Wff.classMem (Class.cv (nb067AlphaDummy053 x y f)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb067AlphaDummy053 x y f)) (synC1c))).fv ∪
        ((Class.cv (nb067AlphaDummy053 x y f))).fv) :=
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

theorem nb067_support_mem_0064 :
    (nb067AlphaDummy051) ∈
      (((Class.cv (nb067AlphaDummy051))).fv ∪ ((synC1c)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb067_support_mem_0065 (x : Var) (y : Var) (f : Var) :
    (nb067AlphaDummy053 x y f) ∈
      (((Class.cv (nb067AlphaDummy053 x y f))).fv ∪ ((synC1c)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb067_support_mem_0066 :
    (nb067AlphaDummy058) ∈
      (((synCnin (Class.cv (nb067AlphaDummy058)) (Class.cv (nb067AlphaDummy059)))).fv ∪
        ((synCnin (Class.cv (nb067AlphaDummy058))
            (Class.cv (nb067AlphaDummy059)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb067_support_mem_0067 (x : Var) (y : Var) (f : Var) :
    (nb067AlphaDummy061 x y f) ∈
      (((synCnin (Class.cv (nb067AlphaDummy061 x y f))
            (Class.cv (nb067AlphaDummy062 x y f)))).fv ∪
        ((synCnin (Class.cv (nb067AlphaDummy061 x y f))
            (Class.cv (nb067AlphaDummy062 x y f)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb067_support_mem_0068 :
    (nb067AlphaDummy058) ∈
      (((Class.cv (nb067AlphaDummy058))).fv ∪ ((Class.cv (nb067AlphaDummy059))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb067_support_mem_0069 (x : Var) (y : Var) (f : Var) :
    (nb067AlphaDummy061 x y f) ∈
      (((Class.cv (nb067AlphaDummy061 x y f))).fv ∪
        ((Class.cv (nb067AlphaDummy062 x y f))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb067_support_mem_0070 :
    (nb067AlphaDummy059) ∈
      (((synCnin (Class.cv (nb067AlphaDummy058)) (Class.cv (nb067AlphaDummy059)))).fv ∪
        ((synCnin (Class.cv (nb067AlphaDummy058))
            (Class.cv (nb067AlphaDummy059)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb067_support_mem_0071 (x : Var) (y : Var) (f : Var) :
    (nb067AlphaDummy062 x y f) ∈
      (((synCnin (Class.cv (nb067AlphaDummy061 x y f))
            (Class.cv (nb067AlphaDummy062 x y f)))).fv ∪
        ((synCnin (Class.cv (nb067AlphaDummy061 x y f))
            (Class.cv (nb067AlphaDummy062 x y f)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb067_support_mem_0072 :
    (nb067AlphaDummy059) ∈
      (((Class.cv (nb067AlphaDummy058))).fv ∪ ((Class.cv (nb067AlphaDummy059))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb067_support_mem_0073 (x : Var) (y : Var) (f : Var) :
    (nb067AlphaDummy062 x y f) ∈
      (((Class.cv (nb067AlphaDummy061 x y f))).fv ∪
        ((Class.cv (nb067AlphaDummy062 x y f))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb067_support_mem_0074 :
    (nb067AlphaDummy058) ∈
      (((synCcompl (Class.cv (nb067AlphaDummy058)))).fv ∪
        ((synCcompl (Class.cv (nb067AlphaDummy059)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb067_support_mem_0075 (x : Var) (y : Var) (f : Var) :
    (nb067AlphaDummy061 x y f) ∈
      (((synCcompl (Class.cv (nb067AlphaDummy061 x y f)))).fv ∪
        ((synCcompl (Class.cv (nb067AlphaDummy062 x y f)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb067_support_mem_0076 :
    (nb067AlphaDummy058) ∈
      (((Class.cv (nb067AlphaDummy058))).fv ∪ ((Class.cv (nb067AlphaDummy058))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb067_support_mem_0077 (x : Var) (y : Var) (f : Var) :
    (nb067AlphaDummy061 x y f) ∈
      (((Class.cv (nb067AlphaDummy061 x y f))).fv ∪
        ((Class.cv (nb067AlphaDummy061 x y f))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb067_support_mem_0078 :
    (nb067AlphaDummy059) ∈
      (((synCcompl (Class.cv (nb067AlphaDummy058)))).fv ∪
        ((synCcompl (Class.cv (nb067AlphaDummy059)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb067_support_mem_0079 (x : Var) (y : Var) (f : Var) :
    (nb067AlphaDummy062 x y f) ∈
      (((synCcompl (Class.cv (nb067AlphaDummy061 x y f)))).fv ∪
        ((synCcompl (Class.cv (nb067AlphaDummy062 x y f)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb067_support_mem_0080 :
    (nb067AlphaDummy059) ∈
      (((Class.cv (nb067AlphaDummy059))).fv ∪ ((Class.cv (nb067AlphaDummy059))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb067_support_mem_0081 (x : Var) (y : Var) (f : Var) :
    (nb067AlphaDummy062 x y f) ∈
      (((Class.cv (nb067AlphaDummy062 x y f))).fv ∪
        ((Class.cv (nb067AlphaDummy062 x y f))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb067_support_mem_0082 :
    (nb067AlphaDummy003) ∈
      (((synCop (Class.cv (nb067AlphaDummy001)) (Class.cv (nb067AlphaDummy002)))).fv ∪
        ((Class.cv (nb067AlphaDummy003))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb067_support_mem_0083 :
    (nb067AlphaDummy003) ∈
      (((synCcompl (Class.cab (nb067AlphaDummy007) (synWrex (nb067AlphaDummy008)
                (synCop (Class.cv (nb067AlphaDummy001)) (Class.cv (nb067AlphaDummy002)))
                (Wff.classEq (Class.cv (nb067AlphaDummy007))
                  (synCphi (Class.cv (nb067AlphaDummy008)))))))).fv ∪ ((synCcompl
            (Class.cab (nb067AlphaDummy007)
              (synWrex (nb067AlphaDummy008) (Class.cv (nb067AlphaDummy003))
                (Wff.classEq (Class.cv (nb067AlphaDummy007))
                  (synCun (synCphi (Class.cv (nb067AlphaDummy008)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0082) 0))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0082) 1))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb067_support_mem_0084 (x : Var) (y : Var) (f : Var) :
    (nb067AlphaDummy004 x y f) ∈
      (((synCop (Class.cv x) (Class.cv y))).fv ∪
        ((Class.cv (nb067AlphaDummy004 x y f))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb067_support_mem_0085 (x : Var) (y : Var) (f : Var) :
    (nb067AlphaDummy004 x y f) ∈
      (((synCcompl (Class.cab (nb067AlphaDummy009 x y f)
              (synWrex (nb067AlphaDummy010 x y f) (synCop (Class.cv x) (Class.cv y))
                (Wff.classEq (Class.cv (nb067AlphaDummy009 x y f))
                  (synCphi (Class.cv (nb067AlphaDummy010 x y f)))))))).fv ∪ ((synCcompl
            (Class.cab (nb067AlphaDummy009 x y f) (synWrex (nb067AlphaDummy010 x y f)
                (Class.cv (nb067AlphaDummy004 x y f))
                (Wff.classEq (Class.cv (nb067AlphaDummy009 x y f))
                  (synCun (synCphi (Class.cv (nb067AlphaDummy010 x y f)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0084 x y f) 0))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0084 x y f) 1))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb067_support_mem_0086 :
    (nb067AlphaDummy003) ∈
      (((Class.cab (nb067AlphaDummy007)
            (synWrex (nb067AlphaDummy008) (Class.cv (nb067AlphaDummy003))
              (Wff.classEq (Class.cv (nb067AlphaDummy007))
                (synCun (synCphi (Class.cv (nb067AlphaDummy008)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb067AlphaDummy007)
            (synWrex (nb067AlphaDummy008) (Class.cv (nb067AlphaDummy003))
              (Wff.classEq (Class.cv (nb067AlphaDummy007))
                (synCun (synCphi (Class.cv (nb067AlphaDummy008)))
                  (synCsn (synC0c))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0082) 0))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0082) 1))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb067_support_mem_0087 (x : Var) (y : Var) (f : Var) :
    (nb067AlphaDummy004 x y f) ∈
      (((Class.cab (nb067AlphaDummy009 x y f) (synWrex (nb067AlphaDummy010 x y f)
              (Class.cv (nb067AlphaDummy004 x y f))
              (Wff.classEq (Class.cv (nb067AlphaDummy009 x y f))
                (synCun (synCphi (Class.cv (nb067AlphaDummy010 x y f)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb067AlphaDummy009 x y f)
            (synWrex (nb067AlphaDummy010 x y f) (Class.cv (nb067AlphaDummy004 x y f))
              (Wff.classEq (Class.cv (nb067AlphaDummy009 x y f))
                (synCun (synCphi (Class.cv (nb067AlphaDummy010 x y f)))
                  (synCsn (synC0c))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0084 x y f) 0))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0084 x y f) 1))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb067_support_mem_0088 :
    (nb067AlphaDummy008) ∈
      (((synCcompl (synCphi (Class.cv (nb067AlphaDummy008))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb067_support_mem_0089 (x : Var) (y : Var) (f : Var) :
    (nb067AlphaDummy010 x y f) ∈
      (((synCcompl (synCphi (Class.cv (nb067AlphaDummy010 x y f))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb067_support_mem_0090 :
    (nb067AlphaDummy008) ∈
      (((synCphi (Class.cv (nb067AlphaDummy008)))).fv ∪
        ((synCphi (Class.cv (nb067AlphaDummy008)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb067_support_mem_0091 (x : Var) (y : Var) (f : Var) :
    (nb067AlphaDummy010 x y f) ∈
      (((synCphi (Class.cv (nb067AlphaDummy010 x y f)))).fv ∪
        ((synCphi (Class.cv (nb067AlphaDummy010 x y f)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb067_support_mem_0092 :
    (nb067AlphaDummy083) ∈
      (({(nb067AlphaDummy083)} : Finset Var) ∪ ({(nb067AlphaDummy084)} : Finset Var) ∪
        ((synWex (nb067AlphaDummy085) (synWa (synWbr (Class.cv (nb067AlphaDummy083))
                (synCcnv (Class.cv (nb067AlphaDummy000)))
                (Class.cv (nb067AlphaDummy085))) (synWbr (Class.cv (nb067AlphaDummy085))
                (Class.cv (nb067AlphaDummy000)) (Class.cv (nb067AlphaDummy084)))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  with_reducible rw [Finset.mem_union]
  left
  exact Finset.mem_singleton_self _

theorem nb067_support_mem_0093 (f : Var) :
    (nb067AlphaDummy086 f) ∈
      (({(nb067AlphaDummy086 f)} : Finset Var) ∪ ({(nb067AlphaDummy087 f)} : Finset Var) ∪
        ((synWex (nb067AlphaDummy088 f) (synWa
              (synWbr (Class.cv (nb067AlphaDummy086 f)) (synCcnv (Class.cv f))
                (Class.cv (nb067AlphaDummy088 f)))
              (synWbr (Class.cv (nb067AlphaDummy088 f)) (Class.cv f)
                (Class.cv (nb067AlphaDummy087 f)))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  with_reducible rw [Finset.mem_union]
  left
  exact Finset.mem_singleton_self _

theorem nb067_support_mem_0094 :
    (nb067AlphaDummy084) ∈
      (({(nb067AlphaDummy083)} : Finset Var) ∪ ({(nb067AlphaDummy084)} : Finset Var) ∪
        ((synWex (nb067AlphaDummy085) (synWa (synWbr (Class.cv (nb067AlphaDummy083))
                (synCcnv (Class.cv (nb067AlphaDummy000)))
                (Class.cv (nb067AlphaDummy085))) (synWbr (Class.cv (nb067AlphaDummy085))
                (Class.cv (nb067AlphaDummy000)) (Class.cv (nb067AlphaDummy084)))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  with_reducible rw [Finset.mem_union]
  right
  exact Finset.mem_singleton_self _

theorem nb067_support_mem_0095 (f : Var) :
    (nb067AlphaDummy087 f) ∈
      (({(nb067AlphaDummy086 f)} : Finset Var) ∪ ({(nb067AlphaDummy087 f)} : Finset Var) ∪
        ((synWex (nb067AlphaDummy088 f) (synWa
              (synWbr (Class.cv (nb067AlphaDummy086 f)) (synCcnv (Class.cv f))
                (Class.cv (nb067AlphaDummy088 f)))
              (synWbr (Class.cv (nb067AlphaDummy088 f)) (Class.cv f)
                (Class.cv (nb067AlphaDummy087 f)))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  with_reducible rw [Finset.mem_union]
  right
  exact Finset.mem_singleton_self _

theorem nb067_support_mem_0096 :
    (nb067AlphaDummy083) ∈
      (((Class.cv (nb067AlphaDummy083))).fv ∪ ((Class.cv (nb067AlphaDummy084))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb067_support_mem_0097 :
    (nb067AlphaDummy083) ∈
      (((synCcompl (Class.cab (nb067AlphaDummy091)
              (synWrex (nb067AlphaDummy092) (Class.cv (nb067AlphaDummy083))
                (Wff.classEq (Class.cv (nb067AlphaDummy091))
                  (synCphi (Class.cv (nb067AlphaDummy092)))))))).fv ∪ ((synCcompl
            (Class.cab (nb067AlphaDummy091)
              (synWrex (nb067AlphaDummy092) (Class.cv (nb067AlphaDummy084))
                (Wff.classEq (Class.cv (nb067AlphaDummy091))
                  (synCun (synCphi (Class.cv (nb067AlphaDummy092)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0096) 0))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0096) 1))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb067_support_mem_0098 (f : Var) :
    (nb067AlphaDummy086 f) ∈
      (((Class.cv (nb067AlphaDummy086 f))).fv ∪ ((Class.cv (nb067AlphaDummy087 f))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb067_support_mem_0099 (f : Var) :
    (nb067AlphaDummy086 f) ∈
      (((synCcompl (Class.cab (nb067AlphaDummy093 f)
              (synWrex (nb067AlphaDummy094 f) (Class.cv (nb067AlphaDummy086 f))
                (Wff.classEq (Class.cv (nb067AlphaDummy093 f))
                  (synCphi (Class.cv (nb067AlphaDummy094 f)))))))).fv ∪ ((synCcompl
            (Class.cab (nb067AlphaDummy093 f)
              (synWrex (nb067AlphaDummy094 f) (Class.cv (nb067AlphaDummy087 f))
                (Wff.classEq (Class.cv (nb067AlphaDummy093 f))
                  (synCun (synCphi (Class.cv (nb067AlphaDummy094 f)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0098 f) 0))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0098 f) 1))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb067_support_mem_0100 :
    (nb067AlphaDummy083) ∈
      (((Class.cab (nb067AlphaDummy091)
            (synWrex (nb067AlphaDummy092) (Class.cv (nb067AlphaDummy083))
              (Wff.classEq (Class.cv (nb067AlphaDummy091))
                (synCphi (Class.cv (nb067AlphaDummy092))))))).fv ∪
        ((Class.cab (nb067AlphaDummy091)
            (synWrex (nb067AlphaDummy092) (Class.cv (nb067AlphaDummy083))
              (Wff.classEq (Class.cv (nb067AlphaDummy091))
                (synCphi (Class.cv (nb067AlphaDummy092))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0096) 0))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0096) 1))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb067_support_mem_0101 (f : Var) :
    (nb067AlphaDummy086 f) ∈
      (((Class.cab (nb067AlphaDummy093 f)
            (synWrex (nb067AlphaDummy094 f) (Class.cv (nb067AlphaDummy086 f))
              (Wff.classEq (Class.cv (nb067AlphaDummy093 f))
                (synCphi (Class.cv (nb067AlphaDummy094 f))))))).fv ∪
        ((Class.cab (nb067AlphaDummy093 f)
            (synWrex (nb067AlphaDummy094 f) (Class.cv (nb067AlphaDummy086 f))
              (Wff.classEq (Class.cv (nb067AlphaDummy093 f))
                (synCphi (Class.cv (nb067AlphaDummy094 f))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0098 f) 0))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0098 f) 1))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb067_support_mem_0102 :
    (nb067AlphaDummy092) ∈ (((Class.cv (nb067AlphaDummy092))).fv) :=
  by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb067_support_mem_0103 (f : Var) :
    (nb067AlphaDummy094 f) ∈ (((Class.cv (nb067AlphaDummy094 f))).fv) :=
  by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb067_support_mem_0104 :
    (nb067AlphaDummy099) ∈
      (((Wff.classMem (Class.cv (nb067AlphaDummy099)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb067AlphaDummy099)) (synC1c))).fv ∪
        ((Class.cv (nb067AlphaDummy099))).fv) :=
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

theorem nb067_support_mem_0105 (f : Var) :
    (nb067AlphaDummy101 f) ∈
      (((Wff.classMem (Class.cv (nb067AlphaDummy101 f)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb067AlphaDummy101 f)) (synC1c))).fv ∪
        ((Class.cv (nb067AlphaDummy101 f))).fv) :=
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

theorem nb067_support_mem_0106 :
    (nb067AlphaDummy099) ∈
      (((Class.cv (nb067AlphaDummy099))).fv ∪ ((synC1c)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb067_support_mem_0107 (f : Var) :
    (nb067AlphaDummy101 f) ∈
      (((Class.cv (nb067AlphaDummy101 f))).fv ∪ ((synC1c)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb067_support_mem_0108 :
    (nb067AlphaDummy106) ∈
      (((synCnin (Class.cv (nb067AlphaDummy106)) (Class.cv (nb067AlphaDummy107)))).fv ∪
        ((synCnin (Class.cv (nb067AlphaDummy106))
            (Class.cv (nb067AlphaDummy107)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb067_support_mem_0109 (f : Var) :
    (nb067AlphaDummy109 f) ∈
      (((synCnin (Class.cv (nb067AlphaDummy109 f))
            (Class.cv (nb067AlphaDummy110 f)))).fv ∪
        ((synCnin (Class.cv (nb067AlphaDummy109 f))
            (Class.cv (nb067AlphaDummy110 f)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb067_support_mem_0110 :
    (nb067AlphaDummy106) ∈
      (((Class.cv (nb067AlphaDummy106))).fv ∪ ((Class.cv (nb067AlphaDummy107))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb067_support_mem_0111 (f : Var) :
    (nb067AlphaDummy109 f) ∈
      (((Class.cv (nb067AlphaDummy109 f))).fv ∪ ((Class.cv (nb067AlphaDummy110 f))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb067_support_mem_0112 :
    (nb067AlphaDummy107) ∈
      (((synCnin (Class.cv (nb067AlphaDummy106)) (Class.cv (nb067AlphaDummy107)))).fv ∪
        ((synCnin (Class.cv (nb067AlphaDummy106))
            (Class.cv (nb067AlphaDummy107)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb067_support_mem_0113 (f : Var) :
    (nb067AlphaDummy110 f) ∈
      (((synCnin (Class.cv (nb067AlphaDummy109 f))
            (Class.cv (nb067AlphaDummy110 f)))).fv ∪
        ((synCnin (Class.cv (nb067AlphaDummy109 f))
            (Class.cv (nb067AlphaDummy110 f)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb067_support_mem_0114 :
    (nb067AlphaDummy107) ∈
      (((Class.cv (nb067AlphaDummy106))).fv ∪ ((Class.cv (nb067AlphaDummy107))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb067_support_mem_0115 (f : Var) :
    (nb067AlphaDummy110 f) ∈
      (((Class.cv (nb067AlphaDummy109 f))).fv ∪ ((Class.cv (nb067AlphaDummy110 f))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb067_support_mem_0116 :
    (nb067AlphaDummy106) ∈
      (((synCcompl (Class.cv (nb067AlphaDummy106)))).fv ∪
        ((synCcompl (Class.cv (nb067AlphaDummy107)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb067_support_mem_0117 (f : Var) :
    (nb067AlphaDummy109 f) ∈
      (((synCcompl (Class.cv (nb067AlphaDummy109 f)))).fv ∪
        ((synCcompl (Class.cv (nb067AlphaDummy110 f)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb067_support_mem_0118 :
    (nb067AlphaDummy106) ∈
      (((Class.cv (nb067AlphaDummy106))).fv ∪ ((Class.cv (nb067AlphaDummy106))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb067_support_mem_0119 (f : Var) :
    (nb067AlphaDummy109 f) ∈
      (((Class.cv (nb067AlphaDummy109 f))).fv ∪ ((Class.cv (nb067AlphaDummy109 f))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb067_support_mem_0120 :
    (nb067AlphaDummy107) ∈
      (((synCcompl (Class.cv (nb067AlphaDummy106)))).fv ∪
        ((synCcompl (Class.cv (nb067AlphaDummy107)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb067_support_mem_0121 (f : Var) :
    (nb067AlphaDummy110 f) ∈
      (((synCcompl (Class.cv (nb067AlphaDummy109 f)))).fv ∪
        ((synCcompl (Class.cv (nb067AlphaDummy110 f)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb067_support_mem_0122 :
    (nb067AlphaDummy107) ∈
      (((Class.cv (nb067AlphaDummy107))).fv ∪ ((Class.cv (nb067AlphaDummy107))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb067_support_mem_0123 (f : Var) :
    (nb067AlphaDummy110 f) ∈
      (((Class.cv (nb067AlphaDummy110 f))).fv ∪ ((Class.cv (nb067AlphaDummy110 f))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb067_support_mem_0124 :
    (nb067AlphaDummy084) ∈
      (((Class.cv (nb067AlphaDummy083))).fv ∪ ((Class.cv (nb067AlphaDummy084))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb067_support_mem_0125 :
    (nb067AlphaDummy084) ∈
      (((synCcompl (Class.cab (nb067AlphaDummy091)
              (synWrex (nb067AlphaDummy092) (Class.cv (nb067AlphaDummy083))
                (Wff.classEq (Class.cv (nb067AlphaDummy091))
                  (synCphi (Class.cv (nb067AlphaDummy092)))))))).fv ∪ ((synCcompl
            (Class.cab (nb067AlphaDummy091)
              (synWrex (nb067AlphaDummy092) (Class.cv (nb067AlphaDummy084))
                (Wff.classEq (Class.cv (nb067AlphaDummy091))
                  (synCun (synCphi (Class.cv (nb067AlphaDummy092)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0124) 0))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0124) 1))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb067_support_mem_0126 (f : Var) :
    (nb067AlphaDummy087 f) ∈
      (((Class.cv (nb067AlphaDummy086 f))).fv ∪ ((Class.cv (nb067AlphaDummy087 f))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb067_support_mem_0127 (f : Var) :
    (nb067AlphaDummy087 f) ∈
      (((synCcompl (Class.cab (nb067AlphaDummy093 f)
              (synWrex (nb067AlphaDummy094 f) (Class.cv (nb067AlphaDummy086 f))
                (Wff.classEq (Class.cv (nb067AlphaDummy093 f))
                  (synCphi (Class.cv (nb067AlphaDummy094 f)))))))).fv ∪ ((synCcompl
            (Class.cab (nb067AlphaDummy093 f)
              (synWrex (nb067AlphaDummy094 f) (Class.cv (nb067AlphaDummy087 f))
                (Wff.classEq (Class.cv (nb067AlphaDummy093 f))
                  (synCun (synCphi (Class.cv (nb067AlphaDummy094 f)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0126 f) 0))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0126 f) 1))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb067_support_mem_0128 :
    (nb067AlphaDummy084) ∈
      (((Class.cab (nb067AlphaDummy091)
            (synWrex (nb067AlphaDummy092) (Class.cv (nb067AlphaDummy084))
              (Wff.classEq (Class.cv (nb067AlphaDummy091))
                (synCun (synCphi (Class.cv (nb067AlphaDummy092)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb067AlphaDummy091)
            (synWrex (nb067AlphaDummy092) (Class.cv (nb067AlphaDummy084))
              (Wff.classEq (Class.cv (nb067AlphaDummy091))
                (synCun (synCphi (Class.cv (nb067AlphaDummy092)))
                  (synCsn (synC0c))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0124) 0))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0124) 1))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb067_support_mem_0129 (f : Var) :
    (nb067AlphaDummy087 f) ∈
      (((Class.cab (nb067AlphaDummy093 f)
            (synWrex (nb067AlphaDummy094 f) (Class.cv (nb067AlphaDummy087 f))
              (Wff.classEq (Class.cv (nb067AlphaDummy093 f))
                (synCun (synCphi (Class.cv (nb067AlphaDummy094 f)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb067AlphaDummy093 f)
            (synWrex (nb067AlphaDummy094 f) (Class.cv (nb067AlphaDummy087 f))
              (Wff.classEq (Class.cv (nb067AlphaDummy093 f))
                (synCun (synCphi (Class.cv (nb067AlphaDummy094 f)))
                  (synCsn (synC0c))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0126 f) 0))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0126 f) 1))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb067_support_mem_0130 :
    (nb067AlphaDummy092) ∈
      (((synCcompl (synCphi (Class.cv (nb067AlphaDummy092))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb067_support_mem_0131 (f : Var) :
    (nb067AlphaDummy094 f) ∈
      (((synCcompl (synCphi (Class.cv (nb067AlphaDummy094 f))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb067_support_mem_0132 :
    (nb067AlphaDummy092) ∈
      (((synCphi (Class.cv (nb067AlphaDummy092)))).fv ∪
        ((synCphi (Class.cv (nb067AlphaDummy092)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb067_support_mem_0133 (f : Var) :
    (nb067AlphaDummy094 f) ∈
      (((synCphi (Class.cv (nb067AlphaDummy094 f)))).fv ∪
        ((synCphi (Class.cv (nb067AlphaDummy094 f)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb067_support_mem_0134 :
    (nb067AlphaDummy083) ∈
      (((Class.cv (nb067AlphaDummy083))).fv ∪ ((Class.cv (nb067AlphaDummy085))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb067_support_mem_0135 :
    (nb067AlphaDummy083) ∈
      (((synCcompl (Class.cab (nb067AlphaDummy127)
              (synWrex (nb067AlphaDummy128) (Class.cv (nb067AlphaDummy083))
                (Wff.classEq (Class.cv (nb067AlphaDummy127))
                  (synCphi (Class.cv (nb067AlphaDummy128)))))))).fv ∪ ((synCcompl
            (Class.cab (nb067AlphaDummy127)
              (synWrex (nb067AlphaDummy128) (Class.cv (nb067AlphaDummy085))
                (Wff.classEq (Class.cv (nb067AlphaDummy127))
                  (synCun (synCphi (Class.cv (nb067AlphaDummy128)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0134) 0))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0134) 1))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb067_support_mem_0136 (f : Var) :
    (nb067AlphaDummy086 f) ∈
      (((Class.cv (nb067AlphaDummy086 f))).fv ∪ ((Class.cv (nb067AlphaDummy088 f))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb067_support_mem_0137 (f : Var) :
    (nb067AlphaDummy086 f) ∈
      (((synCcompl (Class.cab (nb067AlphaDummy129 f)
              (synWrex (nb067AlphaDummy130 f) (Class.cv (nb067AlphaDummy086 f))
                (Wff.classEq (Class.cv (nb067AlphaDummy129 f))
                  (synCphi (Class.cv (nb067AlphaDummy130 f)))))))).fv ∪ ((synCcompl
            (Class.cab (nb067AlphaDummy129 f)
              (synWrex (nb067AlphaDummy130 f) (Class.cv (nb067AlphaDummy088 f))
                (Wff.classEq (Class.cv (nb067AlphaDummy129 f))
                  (synCun (synCphi (Class.cv (nb067AlphaDummy130 f)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0136 f) 0))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0136 f) 1))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb067_support_mem_0138 :
    (nb067AlphaDummy083) ∈
      (((Class.cab (nb067AlphaDummy127)
            (synWrex (nb067AlphaDummy128) (Class.cv (nb067AlphaDummy083))
              (Wff.classEq (Class.cv (nb067AlphaDummy127))
                (synCphi (Class.cv (nb067AlphaDummy128))))))).fv ∪
        ((Class.cab (nb067AlphaDummy127)
            (synWrex (nb067AlphaDummy128) (Class.cv (nb067AlphaDummy083))
              (Wff.classEq (Class.cv (nb067AlphaDummy127))
                (synCphi (Class.cv (nb067AlphaDummy128))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0134) 0))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0134) 1))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb067_support_mem_0139 (f : Var) :
    (nb067AlphaDummy086 f) ∈
      (((Class.cab (nb067AlphaDummy129 f)
            (synWrex (nb067AlphaDummy130 f) (Class.cv (nb067AlphaDummy086 f))
              (Wff.classEq (Class.cv (nb067AlphaDummy129 f))
                (synCphi (Class.cv (nb067AlphaDummy130 f))))))).fv ∪
        ((Class.cab (nb067AlphaDummy129 f)
            (synWrex (nb067AlphaDummy130 f) (Class.cv (nb067AlphaDummy086 f))
              (Wff.classEq (Class.cv (nb067AlphaDummy129 f))
                (synCphi (Class.cv (nb067AlphaDummy130 f))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0136 f) 0))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0136 f) 1))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb067_support_mem_0140 :
    (nb067AlphaDummy128) ∈ (((Class.cv (nb067AlphaDummy128))).fv) :=
  by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb067_support_mem_0141 (f : Var) :
    (nb067AlphaDummy130 f) ∈ (((Class.cv (nb067AlphaDummy130 f))).fv) :=
  by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb067_support_mem_0142 :
    (nb067AlphaDummy135) ∈
      (((Wff.classMem (Class.cv (nb067AlphaDummy135)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb067AlphaDummy135)) (synC1c))).fv ∪
        ((Class.cv (nb067AlphaDummy135))).fv) :=
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

theorem nb067_support_mem_0143 (f : Var) :
    (nb067AlphaDummy137 f) ∈
      (((Wff.classMem (Class.cv (nb067AlphaDummy137 f)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb067AlphaDummy137 f)) (synC1c))).fv ∪
        ((Class.cv (nb067AlphaDummy137 f))).fv) :=
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

theorem nb067_support_mem_0144 :
    (nb067AlphaDummy135) ∈
      (((Class.cv (nb067AlphaDummy135))).fv ∪ ((synC1c)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb067_support_mem_0145 (f : Var) :
    (nb067AlphaDummy137 f) ∈
      (((Class.cv (nb067AlphaDummy137 f))).fv ∪ ((synC1c)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb067_support_mem_0146 :
    (nb067AlphaDummy142) ∈
      (((synCnin (Class.cv (nb067AlphaDummy142)) (Class.cv (nb067AlphaDummy143)))).fv ∪
        ((synCnin (Class.cv (nb067AlphaDummy142))
            (Class.cv (nb067AlphaDummy143)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb067_support_mem_0147 (f : Var) :
    (nb067AlphaDummy145 f) ∈
      (((synCnin (Class.cv (nb067AlphaDummy145 f))
            (Class.cv (nb067AlphaDummy146 f)))).fv ∪
        ((synCnin (Class.cv (nb067AlphaDummy145 f))
            (Class.cv (nb067AlphaDummy146 f)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb067_support_mem_0148 :
    (nb067AlphaDummy142) ∈
      (((Class.cv (nb067AlphaDummy142))).fv ∪ ((Class.cv (nb067AlphaDummy143))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb067_support_mem_0149 (f : Var) :
    (nb067AlphaDummy145 f) ∈
      (((Class.cv (nb067AlphaDummy145 f))).fv ∪ ((Class.cv (nb067AlphaDummy146 f))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb067_support_mem_0150 :
    (nb067AlphaDummy143) ∈
      (((synCnin (Class.cv (nb067AlphaDummy142)) (Class.cv (nb067AlphaDummy143)))).fv ∪
        ((synCnin (Class.cv (nb067AlphaDummy142))
            (Class.cv (nb067AlphaDummy143)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb067_support_mem_0151 (f : Var) :
    (nb067AlphaDummy146 f) ∈
      (((synCnin (Class.cv (nb067AlphaDummy145 f))
            (Class.cv (nb067AlphaDummy146 f)))).fv ∪
        ((synCnin (Class.cv (nb067AlphaDummy145 f))
            (Class.cv (nb067AlphaDummy146 f)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb067_support_mem_0152 :
    (nb067AlphaDummy143) ∈
      (((Class.cv (nb067AlphaDummy142))).fv ∪ ((Class.cv (nb067AlphaDummy143))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb067_support_mem_0153 (f : Var) :
    (nb067AlphaDummy146 f) ∈
      (((Class.cv (nb067AlphaDummy145 f))).fv ∪ ((Class.cv (nb067AlphaDummy146 f))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb067_support_mem_0154 :
    (nb067AlphaDummy142) ∈
      (((synCcompl (Class.cv (nb067AlphaDummy142)))).fv ∪
        ((synCcompl (Class.cv (nb067AlphaDummy143)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb067_support_mem_0155 (f : Var) :
    (nb067AlphaDummy145 f) ∈
      (((synCcompl (Class.cv (nb067AlphaDummy145 f)))).fv ∪
        ((synCcompl (Class.cv (nb067AlphaDummy146 f)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb067_support_mem_0156 :
    (nb067AlphaDummy142) ∈
      (((Class.cv (nb067AlphaDummy142))).fv ∪ ((Class.cv (nb067AlphaDummy142))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb067_support_mem_0157 (f : Var) :
    (nb067AlphaDummy145 f) ∈
      (((Class.cv (nb067AlphaDummy145 f))).fv ∪ ((Class.cv (nb067AlphaDummy145 f))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb067_support_mem_0158 :
    (nb067AlphaDummy143) ∈
      (((synCcompl (Class.cv (nb067AlphaDummy142)))).fv ∪
        ((synCcompl (Class.cv (nb067AlphaDummy143)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb067_support_mem_0159 (f : Var) :
    (nb067AlphaDummy146 f) ∈
      (((synCcompl (Class.cv (nb067AlphaDummy145 f)))).fv ∪
        ((synCcompl (Class.cv (nb067AlphaDummy146 f)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb067_support_mem_0160 :
    (nb067AlphaDummy143) ∈
      (((Class.cv (nb067AlphaDummy143))).fv ∪ ((Class.cv (nb067AlphaDummy143))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb067_support_mem_0161 (f : Var) :
    (nb067AlphaDummy146 f) ∈
      (((Class.cv (nb067AlphaDummy146 f))).fv ∪ ((Class.cv (nb067AlphaDummy146 f))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb067_support_mem_0162 :
    (nb067AlphaDummy085) ∈
      (((Class.cv (nb067AlphaDummy083))).fv ∪ ((Class.cv (nb067AlphaDummy085))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb067_support_mem_0163 :
    (nb067AlphaDummy085) ∈
      (((synCcompl (Class.cab (nb067AlphaDummy127)
              (synWrex (nb067AlphaDummy128) (Class.cv (nb067AlphaDummy083))
                (Wff.classEq (Class.cv (nb067AlphaDummy127))
                  (synCphi (Class.cv (nb067AlphaDummy128)))))))).fv ∪ ((synCcompl
            (Class.cab (nb067AlphaDummy127)
              (synWrex (nb067AlphaDummy128) (Class.cv (nb067AlphaDummy085))
                (Wff.classEq (Class.cv (nb067AlphaDummy127))
                  (synCun (synCphi (Class.cv (nb067AlphaDummy128)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0162) 0))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0162) 1))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb067_support_mem_0164 (f : Var) :
    (nb067AlphaDummy088 f) ∈
      (((Class.cv (nb067AlphaDummy086 f))).fv ∪ ((Class.cv (nb067AlphaDummy088 f))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb067_support_mem_0165 (f : Var) :
    (nb067AlphaDummy088 f) ∈
      (((synCcompl (Class.cab (nb067AlphaDummy129 f)
              (synWrex (nb067AlphaDummy130 f) (Class.cv (nb067AlphaDummy086 f))
                (Wff.classEq (Class.cv (nb067AlphaDummy129 f))
                  (synCphi (Class.cv (nb067AlphaDummy130 f)))))))).fv ∪ ((synCcompl
            (Class.cab (nb067AlphaDummy129 f)
              (synWrex (nb067AlphaDummy130 f) (Class.cv (nb067AlphaDummy088 f))
                (Wff.classEq (Class.cv (nb067AlphaDummy129 f))
                  (synCun (synCphi (Class.cv (nb067AlphaDummy130 f)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0164 f) 0))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0164 f) 1))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb067_support_mem_0166 :
    (nb067AlphaDummy085) ∈
      (((Class.cab (nb067AlphaDummy127)
            (synWrex (nb067AlphaDummy128) (Class.cv (nb067AlphaDummy085))
              (Wff.classEq (Class.cv (nb067AlphaDummy127))
                (synCun (synCphi (Class.cv (nb067AlphaDummy128)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb067AlphaDummy127)
            (synWrex (nb067AlphaDummy128) (Class.cv (nb067AlphaDummy085))
              (Wff.classEq (Class.cv (nb067AlphaDummy127))
                (synCun (synCphi (Class.cv (nb067AlphaDummy128)))
                  (synCsn (synC0c))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0162) 0))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0162) 1))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb067_support_mem_0167 (f : Var) :
    (nb067AlphaDummy088 f) ∈
      (((Class.cab (nb067AlphaDummy129 f)
            (synWrex (nb067AlphaDummy130 f) (Class.cv (nb067AlphaDummy088 f))
              (Wff.classEq (Class.cv (nb067AlphaDummy129 f))
                (synCun (synCphi (Class.cv (nb067AlphaDummy130 f)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb067AlphaDummy129 f)
            (synWrex (nb067AlphaDummy130 f) (Class.cv (nb067AlphaDummy088 f))
              (Wff.classEq (Class.cv (nb067AlphaDummy129 f))
                (synCun (synCphi (Class.cv (nb067AlphaDummy130 f)))
                  (synCsn (synC0c))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0164 f) 0))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0164 f) 1))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb067_support_mem_0168 :
    (nb067AlphaDummy128) ∈
      (((synCcompl (synCphi (Class.cv (nb067AlphaDummy128))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb067_support_mem_0169 (f : Var) :
    (nb067AlphaDummy130 f) ∈
      (((synCcompl (synCphi (Class.cv (nb067AlphaDummy130 f))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb067_support_mem_0170 :
    (nb067AlphaDummy128) ∈
      (((synCphi (Class.cv (nb067AlphaDummy128)))).fv ∪
        ((synCphi (Class.cv (nb067AlphaDummy128)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb067_support_mem_0171 (f : Var) :
    (nb067AlphaDummy130 f) ∈
      (((synCphi (Class.cv (nb067AlphaDummy130 f)))).fv ∪
        ((synCphi (Class.cv (nb067AlphaDummy130 f)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb067_support_mem_0172 :
    (nb067AlphaDummy163) ∈
      (({(nb067AlphaDummy163)} : Finset Var) ∪ ({(nb067AlphaDummy164)} : Finset Var) ∪
        ((synWbr (Class.cv (nb067AlphaDummy164)) (Class.cv (nb067AlphaDummy000))
            (Class.cv (nb067AlphaDummy163)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  with_reducible rw [Finset.mem_union]
  left
  exact Finset.mem_singleton_self _

theorem nb067_support_mem_0173 (f : Var) :
    (nb067AlphaDummy165 f) ∈
      (({(nb067AlphaDummy165 f)} : Finset Var) ∪ ({(nb067AlphaDummy166 f)} : Finset Var) ∪
        ((synWbr (Class.cv (nb067AlphaDummy166 f)) (Class.cv f)
            (Class.cv (nb067AlphaDummy165 f)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  with_reducible rw [Finset.mem_union]
  left
  exact Finset.mem_singleton_self _

theorem nb067_support_mem_0174 :
    (nb067AlphaDummy164) ∈
      (({(nb067AlphaDummy163)} : Finset Var) ∪ ({(nb067AlphaDummy164)} : Finset Var) ∪
        ((synWbr (Class.cv (nb067AlphaDummy164)) (Class.cv (nb067AlphaDummy000))
            (Class.cv (nb067AlphaDummy163)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  with_reducible rw [Finset.mem_union]
  right
  exact Finset.mem_singleton_self _

theorem nb067_support_mem_0175 (f : Var) :
    (nb067AlphaDummy166 f) ∈
      (({(nb067AlphaDummy165 f)} : Finset Var) ∪ ({(nb067AlphaDummy166 f)} : Finset Var) ∪
        ((synWbr (Class.cv (nb067AlphaDummy166 f)) (Class.cv f)
            (Class.cv (nb067AlphaDummy165 f)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  with_reducible rw [Finset.mem_union]
  right
  exact Finset.mem_singleton_self _

theorem nb067_support_mem_0176 :
    (nb067AlphaDummy163) ∈
      (((Class.cv (nb067AlphaDummy163))).fv ∪ ((Class.cv (nb067AlphaDummy164))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb067_support_mem_0177 :
    (nb067AlphaDummy163) ∈
      (((synCcompl (Class.cab (nb067AlphaDummy169)
              (synWrex (nb067AlphaDummy170) (Class.cv (nb067AlphaDummy163))
                (Wff.classEq (Class.cv (nb067AlphaDummy169))
                  (synCphi (Class.cv (nb067AlphaDummy170)))))))).fv ∪ ((synCcompl
            (Class.cab (nb067AlphaDummy169)
              (synWrex (nb067AlphaDummy170) (Class.cv (nb067AlphaDummy164))
                (Wff.classEq (Class.cv (nb067AlphaDummy169))
                  (synCun (synCphi (Class.cv (nb067AlphaDummy170)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0176) 0))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0176) 1))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired

end

/-! Certificates from `NAR4C067C001Part008`. -/


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

theorem nb067_support_mem_0178 (f : Var) :
    (nb067AlphaDummy165 f) ∈
      (((Class.cv (nb067AlphaDummy165 f))).fv ∪ ((Class.cv (nb067AlphaDummy166 f))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb067_support_mem_0179 (f : Var) :
    (nb067AlphaDummy165 f) ∈
      (((synCcompl (Class.cab (nb067AlphaDummy171 f)
              (synWrex (nb067AlphaDummy172 f) (Class.cv (nb067AlphaDummy165 f))
                (Wff.classEq (Class.cv (nb067AlphaDummy171 f))
                  (synCphi (Class.cv (nb067AlphaDummy172 f)))))))).fv ∪ ((synCcompl
            (Class.cab (nb067AlphaDummy171 f)
              (synWrex (nb067AlphaDummy172 f) (Class.cv (nb067AlphaDummy166 f))
                (Wff.classEq (Class.cv (nb067AlphaDummy171 f))
                  (synCun (synCphi (Class.cv (nb067AlphaDummy172 f)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0178 f) 0))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0178 f) 1))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb067_support_mem_0180 :
    (nb067AlphaDummy163) ∈
      (((Class.cab (nb067AlphaDummy169)
            (synWrex (nb067AlphaDummy170) (Class.cv (nb067AlphaDummy163))
              (Wff.classEq (Class.cv (nb067AlphaDummy169))
                (synCphi (Class.cv (nb067AlphaDummy170))))))).fv ∪
        ((Class.cab (nb067AlphaDummy169)
            (synWrex (nb067AlphaDummy170) (Class.cv (nb067AlphaDummy163))
              (Wff.classEq (Class.cv (nb067AlphaDummy169))
                (synCphi (Class.cv (nb067AlphaDummy170))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0176) 0))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0176) 1))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb067_support_mem_0181 (f : Var) :
    (nb067AlphaDummy165 f) ∈
      (((Class.cab (nb067AlphaDummy171 f)
            (synWrex (nb067AlphaDummy172 f) (Class.cv (nb067AlphaDummy165 f))
              (Wff.classEq (Class.cv (nb067AlphaDummy171 f))
                (synCphi (Class.cv (nb067AlphaDummy172 f))))))).fv ∪
        ((Class.cab (nb067AlphaDummy171 f)
            (synWrex (nb067AlphaDummy172 f) (Class.cv (nb067AlphaDummy165 f))
              (Wff.classEq (Class.cv (nb067AlphaDummy171 f))
                (synCphi (Class.cv (nb067AlphaDummy172 f))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0178 f) 0))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0178 f) 1))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb067_support_mem_0182 :
    (nb067AlphaDummy170) ∈ (((Class.cv (nb067AlphaDummy170))).fv) :=
  by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb067_support_mem_0183 (f : Var) :
    (nb067AlphaDummy172 f) ∈ (((Class.cv (nb067AlphaDummy172 f))).fv) :=
  by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb067_support_mem_0184 :
    (nb067AlphaDummy177) ∈
      (((Wff.classMem (Class.cv (nb067AlphaDummy177)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb067AlphaDummy177)) (synC1c))).fv ∪
        ((Class.cv (nb067AlphaDummy177))).fv) :=
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

theorem nb067_support_mem_0185 (f : Var) :
    (nb067AlphaDummy179 f) ∈
      (((Wff.classMem (Class.cv (nb067AlphaDummy179 f)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb067AlphaDummy179 f)) (synC1c))).fv ∪
        ((Class.cv (nb067AlphaDummy179 f))).fv) :=
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

theorem nb067_support_mem_0186 :
    (nb067AlphaDummy177) ∈
      (((Class.cv (nb067AlphaDummy177))).fv ∪ ((synC1c)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb067_support_mem_0187 (f : Var) :
    (nb067AlphaDummy179 f) ∈
      (((Class.cv (nb067AlphaDummy179 f))).fv ∪ ((synC1c)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb067_support_mem_0188 :
    (nb067AlphaDummy184) ∈
      (((synCnin (Class.cv (nb067AlphaDummy184)) (Class.cv (nb067AlphaDummy185)))).fv ∪
        ((synCnin (Class.cv (nb067AlphaDummy184))
            (Class.cv (nb067AlphaDummy185)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb067_support_mem_0189 (f : Var) :
    (nb067AlphaDummy187 f) ∈
      (((synCnin (Class.cv (nb067AlphaDummy187 f))
            (Class.cv (nb067AlphaDummy188 f)))).fv ∪
        ((synCnin (Class.cv (nb067AlphaDummy187 f))
            (Class.cv (nb067AlphaDummy188 f)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb067_support_mem_0190 :
    (nb067AlphaDummy184) ∈
      (((Class.cv (nb067AlphaDummy184))).fv ∪ ((Class.cv (nb067AlphaDummy185))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb067_support_mem_0191 (f : Var) :
    (nb067AlphaDummy187 f) ∈
      (((Class.cv (nb067AlphaDummy187 f))).fv ∪ ((Class.cv (nb067AlphaDummy188 f))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb067_support_mem_0192 :
    (nb067AlphaDummy185) ∈
      (((synCnin (Class.cv (nb067AlphaDummy184)) (Class.cv (nb067AlphaDummy185)))).fv ∪
        ((synCnin (Class.cv (nb067AlphaDummy184))
            (Class.cv (nb067AlphaDummy185)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb067_support_mem_0193 (f : Var) :
    (nb067AlphaDummy188 f) ∈
      (((synCnin (Class.cv (nb067AlphaDummy187 f))
            (Class.cv (nb067AlphaDummy188 f)))).fv ∪
        ((synCnin (Class.cv (nb067AlphaDummy187 f))
            (Class.cv (nb067AlphaDummy188 f)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb067_support_mem_0194 :
    (nb067AlphaDummy185) ∈
      (((Class.cv (nb067AlphaDummy184))).fv ∪ ((Class.cv (nb067AlphaDummy185))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb067_support_mem_0195 (f : Var) :
    (nb067AlphaDummy188 f) ∈
      (((Class.cv (nb067AlphaDummy187 f))).fv ∪ ((Class.cv (nb067AlphaDummy188 f))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb067_support_mem_0196 :
    (nb067AlphaDummy184) ∈
      (((synCcompl (Class.cv (nb067AlphaDummy184)))).fv ∪
        ((synCcompl (Class.cv (nb067AlphaDummy185)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb067_support_mem_0197 (f : Var) :
    (nb067AlphaDummy187 f) ∈
      (((synCcompl (Class.cv (nb067AlphaDummy187 f)))).fv ∪
        ((synCcompl (Class.cv (nb067AlphaDummy188 f)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb067_support_mem_0198 :
    (nb067AlphaDummy184) ∈
      (((Class.cv (nb067AlphaDummy184))).fv ∪ ((Class.cv (nb067AlphaDummy184))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb067_support_mem_0199 (f : Var) :
    (nb067AlphaDummy187 f) ∈
      (((Class.cv (nb067AlphaDummy187 f))).fv ∪ ((Class.cv (nb067AlphaDummy187 f))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb067_support_mem_0200 :
    (nb067AlphaDummy185) ∈
      (((synCcompl (Class.cv (nb067AlphaDummy184)))).fv ∪
        ((synCcompl (Class.cv (nb067AlphaDummy185)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb067_support_mem_0201 (f : Var) :
    (nb067AlphaDummy188 f) ∈
      (((synCcompl (Class.cv (nb067AlphaDummy187 f)))).fv ∪
        ((synCcompl (Class.cv (nb067AlphaDummy188 f)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb067_support_mem_0202 :
    (nb067AlphaDummy185) ∈
      (((Class.cv (nb067AlphaDummy185))).fv ∪ ((Class.cv (nb067AlphaDummy185))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb067_support_mem_0203 (f : Var) :
    (nb067AlphaDummy188 f) ∈
      (((Class.cv (nb067AlphaDummy188 f))).fv ∪ ((Class.cv (nb067AlphaDummy188 f))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb067_support_mem_0204 :
    (nb067AlphaDummy164) ∈
      (((Class.cv (nb067AlphaDummy163))).fv ∪ ((Class.cv (nb067AlphaDummy164))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb067_support_mem_0205 :
    (nb067AlphaDummy164) ∈
      (((synCcompl (Class.cab (nb067AlphaDummy169)
              (synWrex (nb067AlphaDummy170) (Class.cv (nb067AlphaDummy163))
                (Wff.classEq (Class.cv (nb067AlphaDummy169))
                  (synCphi (Class.cv (nb067AlphaDummy170)))))))).fv ∪ ((synCcompl
            (Class.cab (nb067AlphaDummy169)
              (synWrex (nb067AlphaDummy170) (Class.cv (nb067AlphaDummy164))
                (Wff.classEq (Class.cv (nb067AlphaDummy169))
                  (synCun (synCphi (Class.cv (nb067AlphaDummy170)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0204) 0))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0204) 1))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb067_support_mem_0206 (f : Var) :
    (nb067AlphaDummy166 f) ∈
      (((Class.cv (nb067AlphaDummy165 f))).fv ∪ ((Class.cv (nb067AlphaDummy166 f))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb067_support_mem_0207 (f : Var) :
    (nb067AlphaDummy166 f) ∈
      (((synCcompl (Class.cab (nb067AlphaDummy171 f)
              (synWrex (nb067AlphaDummy172 f) (Class.cv (nb067AlphaDummy165 f))
                (Wff.classEq (Class.cv (nb067AlphaDummy171 f))
                  (synCphi (Class.cv (nb067AlphaDummy172 f)))))))).fv ∪ ((synCcompl
            (Class.cab (nb067AlphaDummy171 f)
              (synWrex (nb067AlphaDummy172 f) (Class.cv (nb067AlphaDummy166 f))
                (Wff.classEq (Class.cv (nb067AlphaDummy171 f))
                  (synCun (synCphi (Class.cv (nb067AlphaDummy172 f)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0206 f) 0))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0206 f) 1))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb067_support_mem_0208 :
    (nb067AlphaDummy164) ∈
      (((Class.cab (nb067AlphaDummy169)
            (synWrex (nb067AlphaDummy170) (Class.cv (nb067AlphaDummy164))
              (Wff.classEq (Class.cv (nb067AlphaDummy169))
                (synCun (synCphi (Class.cv (nb067AlphaDummy170)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb067AlphaDummy169)
            (synWrex (nb067AlphaDummy170) (Class.cv (nb067AlphaDummy164))
              (Wff.classEq (Class.cv (nb067AlphaDummy169))
                (synCun (synCphi (Class.cv (nb067AlphaDummy170)))
                  (synCsn (synC0c))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0204) 0))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0204) 1))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb067_support_mem_0209 (f : Var) :
    (nb067AlphaDummy166 f) ∈
      (((Class.cab (nb067AlphaDummy171 f)
            (synWrex (nb067AlphaDummy172 f) (Class.cv (nb067AlphaDummy166 f))
              (Wff.classEq (Class.cv (nb067AlphaDummy171 f))
                (synCun (synCphi (Class.cv (nb067AlphaDummy172 f)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb067AlphaDummy171 f)
            (synWrex (nb067AlphaDummy172 f) (Class.cv (nb067AlphaDummy166 f))
              (Wff.classEq (Class.cv (nb067AlphaDummy171 f))
                (synCun (synCphi (Class.cv (nb067AlphaDummy172 f)))
                  (synCsn (synC0c))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0206 f) 0))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0206 f) 1))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb067_support_mem_0210 :
    (nb067AlphaDummy170) ∈
      (((synCcompl (synCphi (Class.cv (nb067AlphaDummy170))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb067_support_mem_0211 (f : Var) :
    (nb067AlphaDummy172 f) ∈
      (((synCcompl (synCphi (Class.cv (nb067AlphaDummy172 f))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb067_support_mem_0212 :
    (nb067AlphaDummy170) ∈
      (((synCphi (Class.cv (nb067AlphaDummy170)))).fv ∪
        ((synCphi (Class.cv (nb067AlphaDummy170)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb067_support_mem_0213 (f : Var) :
    (nb067AlphaDummy172 f) ∈
      (((synCphi (Class.cv (nb067AlphaDummy172 f)))).fv ∪
        ((synCphi (Class.cv (nb067AlphaDummy172 f)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb067_support_mem_0214 :
    (nb067AlphaDummy164) ∈
      (((Class.cv (nb067AlphaDummy164))).fv ∪ ((Class.cv (nb067AlphaDummy163))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb067_support_mem_0215 :
    (nb067AlphaDummy164) ∈
      (((synCcompl (Class.cab (nb067AlphaDummy205)
              (synWrex (nb067AlphaDummy206) (Class.cv (nb067AlphaDummy164))
                (Wff.classEq (Class.cv (nb067AlphaDummy205))
                  (synCphi (Class.cv (nb067AlphaDummy206)))))))).fv ∪ ((synCcompl
            (Class.cab (nb067AlphaDummy205)
              (synWrex (nb067AlphaDummy206) (Class.cv (nb067AlphaDummy163))
                (Wff.classEq (Class.cv (nb067AlphaDummy205))
                  (synCun (synCphi (Class.cv (nb067AlphaDummy206)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0214) 0))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0214) 1))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb067_support_mem_0216 (f : Var) :
    (nb067AlphaDummy166 f) ∈
      (((Class.cv (nb067AlphaDummy166 f))).fv ∪ ((Class.cv (nb067AlphaDummy165 f))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb067_support_mem_0217 (f : Var) :
    (nb067AlphaDummy166 f) ∈
      (((synCcompl (Class.cab (nb067AlphaDummy207 f)
              (synWrex (nb067AlphaDummy208 f) (Class.cv (nb067AlphaDummy166 f))
                (Wff.classEq (Class.cv (nb067AlphaDummy207 f))
                  (synCphi (Class.cv (nb067AlphaDummy208 f)))))))).fv ∪ ((synCcompl
            (Class.cab (nb067AlphaDummy207 f)
              (synWrex (nb067AlphaDummy208 f) (Class.cv (nb067AlphaDummy165 f))
                (Wff.classEq (Class.cv (nb067AlphaDummy207 f))
                  (synCun (synCphi (Class.cv (nb067AlphaDummy208 f)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0216 f) 0))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0216 f) 1))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb067_support_mem_0218 :
    (nb067AlphaDummy164) ∈
      (((Class.cab (nb067AlphaDummy205)
            (synWrex (nb067AlphaDummy206) (Class.cv (nb067AlphaDummy164))
              (Wff.classEq (Class.cv (nb067AlphaDummy205))
                (synCphi (Class.cv (nb067AlphaDummy206))))))).fv ∪
        ((Class.cab (nb067AlphaDummy205)
            (synWrex (nb067AlphaDummy206) (Class.cv (nb067AlphaDummy164))
              (Wff.classEq (Class.cv (nb067AlphaDummy205))
                (synCphi (Class.cv (nb067AlphaDummy206))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0214) 0))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0214) 1))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb067_support_mem_0219 (f : Var) :
    (nb067AlphaDummy166 f) ∈
      (((Class.cab (nb067AlphaDummy207 f)
            (synWrex (nb067AlphaDummy208 f) (Class.cv (nb067AlphaDummy166 f))
              (Wff.classEq (Class.cv (nb067AlphaDummy207 f))
                (synCphi (Class.cv (nb067AlphaDummy208 f))))))).fv ∪
        ((Class.cab (nb067AlphaDummy207 f)
            (synWrex (nb067AlphaDummy208 f) (Class.cv (nb067AlphaDummy166 f))
              (Wff.classEq (Class.cv (nb067AlphaDummy207 f))
                (synCphi (Class.cv (nb067AlphaDummy208 f))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0216 f) 0))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0216 f) 1))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb067_support_mem_0220 :
    (nb067AlphaDummy206) ∈ (((Class.cv (nb067AlphaDummy206))).fv) :=
  by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb067_support_mem_0221 (f : Var) :
    (nb067AlphaDummy208 f) ∈ (((Class.cv (nb067AlphaDummy208 f))).fv) :=
  by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb067_support_mem_0222 :
    (nb067AlphaDummy213) ∈
      (((Wff.classMem (Class.cv (nb067AlphaDummy213)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb067AlphaDummy213)) (synC1c))).fv ∪
        ((Class.cv (nb067AlphaDummy213))).fv) :=
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

theorem nb067_support_mem_0223 (f : Var) :
    (nb067AlphaDummy215 f) ∈
      (((Wff.classMem (Class.cv (nb067AlphaDummy215 f)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb067AlphaDummy215 f)) (synC1c))).fv ∪
        ((Class.cv (nb067AlphaDummy215 f))).fv) :=
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

theorem nb067_support_mem_0224 :
    (nb067AlphaDummy213) ∈
      (((Class.cv (nb067AlphaDummy213))).fv ∪ ((synC1c)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb067_support_mem_0225 (f : Var) :
    (nb067AlphaDummy215 f) ∈
      (((Class.cv (nb067AlphaDummy215 f))).fv ∪ ((synC1c)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb067_support_mem_0226 :
    (nb067AlphaDummy220) ∈
      (((synCnin (Class.cv (nb067AlphaDummy220)) (Class.cv (nb067AlphaDummy221)))).fv ∪
        ((synCnin (Class.cv (nb067AlphaDummy220))
            (Class.cv (nb067AlphaDummy221)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb067_support_mem_0227 (f : Var) :
    (nb067AlphaDummy223 f) ∈
      (((synCnin (Class.cv (nb067AlphaDummy223 f))
            (Class.cv (nb067AlphaDummy224 f)))).fv ∪
        ((synCnin (Class.cv (nb067AlphaDummy223 f))
            (Class.cv (nb067AlphaDummy224 f)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb067_support_mem_0228 :
    (nb067AlphaDummy220) ∈
      (((Class.cv (nb067AlphaDummy220))).fv ∪ ((Class.cv (nb067AlphaDummy221))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb067_support_mem_0229 (f : Var) :
    (nb067AlphaDummy223 f) ∈
      (((Class.cv (nb067AlphaDummy223 f))).fv ∪ ((Class.cv (nb067AlphaDummy224 f))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb067_support_mem_0230 :
    (nb067AlphaDummy221) ∈
      (((synCnin (Class.cv (nb067AlphaDummy220)) (Class.cv (nb067AlphaDummy221)))).fv ∪
        ((synCnin (Class.cv (nb067AlphaDummy220))
            (Class.cv (nb067AlphaDummy221)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb067_support_mem_0231 (f : Var) :
    (nb067AlphaDummy224 f) ∈
      (((synCnin (Class.cv (nb067AlphaDummy223 f))
            (Class.cv (nb067AlphaDummy224 f)))).fv ∪
        ((synCnin (Class.cv (nb067AlphaDummy223 f))
            (Class.cv (nb067AlphaDummy224 f)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb067_support_mem_0232 :
    (nb067AlphaDummy221) ∈
      (((Class.cv (nb067AlphaDummy220))).fv ∪ ((Class.cv (nb067AlphaDummy221))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb067_support_mem_0233 (f : Var) :
    (nb067AlphaDummy224 f) ∈
      (((Class.cv (nb067AlphaDummy223 f))).fv ∪ ((Class.cv (nb067AlphaDummy224 f))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb067_support_mem_0234 :
    (nb067AlphaDummy220) ∈
      (((synCcompl (Class.cv (nb067AlphaDummy220)))).fv ∪
        ((synCcompl (Class.cv (nb067AlphaDummy221)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb067_support_mem_0235 (f : Var) :
    (nb067AlphaDummy223 f) ∈
      (((synCcompl (Class.cv (nb067AlphaDummy223 f)))).fv ∪
        ((synCcompl (Class.cv (nb067AlphaDummy224 f)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb067_support_mem_0236 :
    (nb067AlphaDummy220) ∈
      (((Class.cv (nb067AlphaDummy220))).fv ∪ ((Class.cv (nb067AlphaDummy220))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb067_support_mem_0237 (f : Var) :
    (nb067AlphaDummy223 f) ∈
      (((Class.cv (nb067AlphaDummy223 f))).fv ∪ ((Class.cv (nb067AlphaDummy223 f))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb067_support_mem_0238 :
    (nb067AlphaDummy221) ∈
      (((synCcompl (Class.cv (nb067AlphaDummy220)))).fv ∪
        ((synCcompl (Class.cv (nb067AlphaDummy221)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb067_support_mem_0239 (f : Var) :
    (nb067AlphaDummy224 f) ∈
      (((synCcompl (Class.cv (nb067AlphaDummy223 f)))).fv ∪
        ((synCcompl (Class.cv (nb067AlphaDummy224 f)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb067_support_mem_0240 :
    (nb067AlphaDummy221) ∈
      (((Class.cv (nb067AlphaDummy221))).fv ∪ ((Class.cv (nb067AlphaDummy221))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb067_support_mem_0241 (f : Var) :
    (nb067AlphaDummy224 f) ∈
      (((Class.cv (nb067AlphaDummy224 f))).fv ∪ ((Class.cv (nb067AlphaDummy224 f))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb067_support_mem_0242 :
    (nb067AlphaDummy163) ∈
      (((Class.cv (nb067AlphaDummy164))).fv ∪ ((Class.cv (nb067AlphaDummy163))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb067_support_mem_0243 :
    (nb067AlphaDummy163) ∈
      (((synCcompl (Class.cab (nb067AlphaDummy205)
              (synWrex (nb067AlphaDummy206) (Class.cv (nb067AlphaDummy164))
                (Wff.classEq (Class.cv (nb067AlphaDummy205))
                  (synCphi (Class.cv (nb067AlphaDummy206)))))))).fv ∪ ((synCcompl
            (Class.cab (nb067AlphaDummy205)
              (synWrex (nb067AlphaDummy206) (Class.cv (nb067AlphaDummy163))
                (Wff.classEq (Class.cv (nb067AlphaDummy205))
                  (synCun (synCphi (Class.cv (nb067AlphaDummy206)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0242) 0))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0242) 1))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb067_support_mem_0244 (f : Var) :
    (nb067AlphaDummy165 f) ∈
      (((Class.cv (nb067AlphaDummy166 f))).fv ∪ ((Class.cv (nb067AlphaDummy165 f))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb067_support_mem_0245 (f : Var) :
    (nb067AlphaDummy165 f) ∈
      (((synCcompl (Class.cab (nb067AlphaDummy207 f)
              (synWrex (nb067AlphaDummy208 f) (Class.cv (nb067AlphaDummy166 f))
                (Wff.classEq (Class.cv (nb067AlphaDummy207 f))
                  (synCphi (Class.cv (nb067AlphaDummy208 f)))))))).fv ∪ ((synCcompl
            (Class.cab (nb067AlphaDummy207 f)
              (synWrex (nb067AlphaDummy208 f) (Class.cv (nb067AlphaDummy165 f))
                (Wff.classEq (Class.cv (nb067AlphaDummy207 f))
                  (synCun (synCphi (Class.cv (nb067AlphaDummy208 f)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0244 f) 0))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0244 f) 1))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb067_support_mem_0246 :
    (nb067AlphaDummy163) ∈
      (((Class.cab (nb067AlphaDummy205)
            (synWrex (nb067AlphaDummy206) (Class.cv (nb067AlphaDummy163))
              (Wff.classEq (Class.cv (nb067AlphaDummy205))
                (synCun (synCphi (Class.cv (nb067AlphaDummy206)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb067AlphaDummy205)
            (synWrex (nb067AlphaDummy206) (Class.cv (nb067AlphaDummy163))
              (Wff.classEq (Class.cv (nb067AlphaDummy205))
                (synCun (synCphi (Class.cv (nb067AlphaDummy206)))
                  (synCsn (synC0c))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0242) 0))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0242) 1))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb067_support_mem_0247 (f : Var) :
    (nb067AlphaDummy165 f) ∈
      (((Class.cab (nb067AlphaDummy207 f)
            (synWrex (nb067AlphaDummy208 f) (Class.cv (nb067AlphaDummy165 f))
              (Wff.classEq (Class.cv (nb067AlphaDummy207 f))
                (synCun (synCphi (Class.cv (nb067AlphaDummy208 f)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb067AlphaDummy207 f)
            (synWrex (nb067AlphaDummy208 f) (Class.cv (nb067AlphaDummy165 f))
              (Wff.classEq (Class.cv (nb067AlphaDummy207 f))
                (synCun (synCphi (Class.cv (nb067AlphaDummy208 f)))
                  (synCsn (synC0c))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0244 f) 0))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0244 f) 1))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb067_support_mem_0248 :
    (nb067AlphaDummy206) ∈
      (((synCcompl (synCphi (Class.cv (nb067AlphaDummy206))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb067_support_mem_0249 (f : Var) :
    (nb067AlphaDummy208 f) ∈
      (((synCcompl (synCphi (Class.cv (nb067AlphaDummy208 f))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb067_support_mem_0250 :
    (nb067AlphaDummy206) ∈
      (((synCphi (Class.cv (nb067AlphaDummy206)))).fv ∪
        ((synCphi (Class.cv (nb067AlphaDummy206)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb067_support_mem_0251 (f : Var) :
    (nb067AlphaDummy208 f) ∈
      (((synCphi (Class.cv (nb067AlphaDummy208 f)))).fv ∪
        ((synCphi (Class.cv (nb067AlphaDummy208 f)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb067_support_mem_0252 :
    (nb067AlphaDummy000) ∈
      (((synCnin (synCcom (Class.cv (nb067AlphaDummy000))
              (synCcnv (Class.cv (nb067AlphaDummy000)))) (synCid))).fv ∪ ((synCnin
            (synCcom (Class.cv (nb067AlphaDummy000))
              (synCcnv (Class.cv (nb067AlphaDummy000)))) (synCid))).fv) :=
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

theorem nb067_support_mem_0253 (f : Var) :
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

theorem nb067_support_mem_0254 :
    (nb067AlphaDummy000) ∈
      (((synCcom (Class.cv (nb067AlphaDummy000))
            (synCcnv (Class.cv (nb067AlphaDummy000))))).fv ∪ ((synCid)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccom]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb067_support_mem_0255 (f : Var) :
    f ∈ (((synCcom (Class.cv f) (synCcnv (Class.cv f)))).fv ∪ ((synCid)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccom]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb067_support_mem_0256 :
    (nb067AlphaDummy000) ∈
      (((Class.cv (nb067AlphaDummy000))).fv ∪
        ((synCcnv (Class.cv (nb067AlphaDummy000)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb067_support_mem_0257 :
    (nb067AlphaDummy000) ∈
      (({(nb067AlphaDummy083)} : Finset Var) ∪ ({(nb067AlphaDummy084)} : Finset Var) ∪
        ((synWex (nb067AlphaDummy085) (synWa (synWbr (Class.cv (nb067AlphaDummy083))
                (synCcnv (Class.cv (nb067AlphaDummy000)))
                (Class.cv (nb067AlphaDummy085))) (synWbr (Class.cv (nb067AlphaDummy085))
                (Class.cv (nb067AlphaDummy000)) (Class.cv (nb067AlphaDummy084)))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_wex]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0256) 2))
  · rw [fv_syn_wa]
    with_reducible rw [Finset.mem_union]
    left
    rw [fv_syn_wbr]
    with_reducible rw [Finset.mem_union]
    right
    rw [fv_syn_ccnv]
    rw [fv_class_cv]
    exact Finset.mem_singleton_self _

theorem nb067_support_mem_0258 (f : Var) :
    f ∈ (((Class.cv f)).fv ∪ ((synCcnv (Class.cv f))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb067_support_mem_0259 (f : Var) :
    f ∈
      (({(nb067AlphaDummy086 f)} : Finset Var) ∪ ({(nb067AlphaDummy087 f)} : Finset Var) ∪
        ((synWex (nb067AlphaDummy088 f) (synWa
              (synWbr (Class.cv (nb067AlphaDummy086 f)) (synCcnv (Class.cv f))
                (Class.cv (nb067AlphaDummy088 f)))
              (synWbr (Class.cv (nb067AlphaDummy088 f)) (Class.cv f)
                (Class.cv (nb067AlphaDummy087 f)))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_wex]
  with_reducible rw [Finset.mem_erase]
  constructor
  · unfold nb067AlphaDummy088
    with_reducible exact (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0258 f) 2))
  · rw [fv_syn_wa]
    with_reducible rw [Finset.mem_union]
    left
    rw [fv_syn_wbr]
    with_reducible rw [Finset.mem_union]
    right
    rw [fv_syn_ccnv]
    rw [fv_class_cv]
    exact Finset.mem_singleton_self _

theorem nb067_support_mem_0260 :
    (nb067AlphaDummy000) ∈
      (({(nb067AlphaDummy163)} : Finset Var) ∪ ({(nb067AlphaDummy164)} : Finset Var) ∪
        ((synWbr (Class.cv (nb067AlphaDummy164)) (Class.cv (nb067AlphaDummy000))
            (Class.cv (nb067AlphaDummy163)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_wbr]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb067_support_mem_0261 (f : Var) :
    f ∈
      (({(nb067AlphaDummy165 f)} : Finset Var) ∪ ({(nb067AlphaDummy166 f)} : Finset Var) ∪
        ((synWbr (Class.cv (nb067AlphaDummy166 f)) (Class.cv f)
            (Class.cv (nb067AlphaDummy165 f)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_wbr]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb067_support_mem_0262 :
    (nb067AlphaDummy000) ∈ (((Class.cv (nb067AlphaDummy000))).fv) :=
  by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb067_support_mem_0263 (f : Var) : f ∈ (((Class.cv f)).fv) :=
  by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb067_support_mem_0264 :
    (nb067AlphaDummy085) ∈
      (((Class.cv (nb067AlphaDummy085))).fv ∪ ((Class.cv (nb067AlphaDummy084))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb067_support_mem_0265 :
    (nb067AlphaDummy085) ∈
      (((synCcompl (Class.cab (nb067AlphaDummy241)
              (synWrex (nb067AlphaDummy242) (Class.cv (nb067AlphaDummy085))
                (Wff.classEq (Class.cv (nb067AlphaDummy241))
                  (synCphi (Class.cv (nb067AlphaDummy242)))))))).fv ∪ ((synCcompl
            (Class.cab (nb067AlphaDummy241)
              (synWrex (nb067AlphaDummy242) (Class.cv (nb067AlphaDummy084))
                (Wff.classEq (Class.cv (nb067AlphaDummy241))
                  (synCun (synCphi (Class.cv (nb067AlphaDummy242)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0264) 0))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0264) 1))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb067_support_mem_0266 (f : Var) :
    (nb067AlphaDummy088 f) ∈
      (((Class.cv (nb067AlphaDummy088 f))).fv ∪ ((Class.cv (nb067AlphaDummy087 f))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb067_support_mem_0267 (f : Var) :
    (nb067AlphaDummy088 f) ∈
      (((synCcompl (Class.cab (nb067AlphaDummy243 f)
              (synWrex (nb067AlphaDummy244 f) (Class.cv (nb067AlphaDummy088 f))
                (Wff.classEq (Class.cv (nb067AlphaDummy243 f))
                  (synCphi (Class.cv (nb067AlphaDummy244 f)))))))).fv ∪ ((synCcompl
            (Class.cab (nb067AlphaDummy243 f)
              (synWrex (nb067AlphaDummy244 f) (Class.cv (nb067AlphaDummy087 f))
                (Wff.classEq (Class.cv (nb067AlphaDummy243 f))
                  (synCun (synCphi (Class.cv (nb067AlphaDummy244 f)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0266 f) 0))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0266 f) 1))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb067_support_mem_0268 :
    (nb067AlphaDummy085) ∈
      (((Class.cab (nb067AlphaDummy241)
            (synWrex (nb067AlphaDummy242) (Class.cv (nb067AlphaDummy085))
              (Wff.classEq (Class.cv (nb067AlphaDummy241))
                (synCphi (Class.cv (nb067AlphaDummy242))))))).fv ∪
        ((Class.cab (nb067AlphaDummy241)
            (synWrex (nb067AlphaDummy242) (Class.cv (nb067AlphaDummy085))
              (Wff.classEq (Class.cv (nb067AlphaDummy241))
                (synCphi (Class.cv (nb067AlphaDummy242))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0264) 0))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0264) 1))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb067_support_mem_0269 (f : Var) :
    (nb067AlphaDummy088 f) ∈
      (((Class.cab (nb067AlphaDummy243 f)
            (synWrex (nb067AlphaDummy244 f) (Class.cv (nb067AlphaDummy088 f))
              (Wff.classEq (Class.cv (nb067AlphaDummy243 f))
                (synCphi (Class.cv (nb067AlphaDummy244 f))))))).fv ∪
        ((Class.cab (nb067AlphaDummy243 f)
            (synWrex (nb067AlphaDummy244 f) (Class.cv (nb067AlphaDummy088 f))
              (Wff.classEq (Class.cv (nb067AlphaDummy243 f))
                (synCphi (Class.cv (nb067AlphaDummy244 f))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0266 f) 0))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0266 f) 1))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb067_support_mem_0270 :
    (nb067AlphaDummy242) ∈ (((Class.cv (nb067AlphaDummy242))).fv) :=
  by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb067_support_mem_0271 (f : Var) :
    (nb067AlphaDummy244 f) ∈ (((Class.cv (nb067AlphaDummy244 f))).fv) :=
  by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb067_support_mem_0272 :
    (nb067AlphaDummy249) ∈
      (((Wff.classMem (Class.cv (nb067AlphaDummy249)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb067AlphaDummy249)) (synC1c))).fv ∪
        ((Class.cv (nb067AlphaDummy249))).fv) :=
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

theorem nb067_support_mem_0273 (f : Var) :
    (nb067AlphaDummy251 f) ∈
      (((Wff.classMem (Class.cv (nb067AlphaDummy251 f)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb067AlphaDummy251 f)) (synC1c))).fv ∪
        ((Class.cv (nb067AlphaDummy251 f))).fv) :=
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

theorem nb067_support_mem_0274 :
    (nb067AlphaDummy249) ∈
      (((Class.cv (nb067AlphaDummy249))).fv ∪ ((synC1c)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb067_support_mem_0275 (f : Var) :
    (nb067AlphaDummy251 f) ∈
      (((Class.cv (nb067AlphaDummy251 f))).fv ∪ ((synC1c)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb067_support_mem_0276 :
    (nb067AlphaDummy256) ∈
      (((synCnin (Class.cv (nb067AlphaDummy256)) (Class.cv (nb067AlphaDummy257)))).fv ∪
        ((synCnin (Class.cv (nb067AlphaDummy256))
            (Class.cv (nb067AlphaDummy257)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb067_support_mem_0277 (f : Var) :
    (nb067AlphaDummy259 f) ∈
      (((synCnin (Class.cv (nb067AlphaDummy259 f))
            (Class.cv (nb067AlphaDummy260 f)))).fv ∪
        ((synCnin (Class.cv (nb067AlphaDummy259 f))
            (Class.cv (nb067AlphaDummy260 f)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb067_support_mem_0278 :
    (nb067AlphaDummy256) ∈
      (((Class.cv (nb067AlphaDummy256))).fv ∪ ((Class.cv (nb067AlphaDummy257))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb067_support_mem_0279 (f : Var) :
    (nb067AlphaDummy259 f) ∈
      (((Class.cv (nb067AlphaDummy259 f))).fv ∪ ((Class.cv (nb067AlphaDummy260 f))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb067_support_mem_0280 :
    (nb067AlphaDummy257) ∈
      (((synCnin (Class.cv (nb067AlphaDummy256)) (Class.cv (nb067AlphaDummy257)))).fv ∪
        ((synCnin (Class.cv (nb067AlphaDummy256))
            (Class.cv (nb067AlphaDummy257)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb067_support_mem_0281 (f : Var) :
    (nb067AlphaDummy260 f) ∈
      (((synCnin (Class.cv (nb067AlphaDummy259 f))
            (Class.cv (nb067AlphaDummy260 f)))).fv ∪
        ((synCnin (Class.cv (nb067AlphaDummy259 f))
            (Class.cv (nb067AlphaDummy260 f)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb067_support_mem_0282 :
    (nb067AlphaDummy257) ∈
      (((Class.cv (nb067AlphaDummy256))).fv ∪ ((Class.cv (nb067AlphaDummy257))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb067_support_mem_0283 (f : Var) :
    (nb067AlphaDummy260 f) ∈
      (((Class.cv (nb067AlphaDummy259 f))).fv ∪ ((Class.cv (nb067AlphaDummy260 f))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb067_support_mem_0284 :
    (nb067AlphaDummy256) ∈
      (((synCcompl (Class.cv (nb067AlphaDummy256)))).fv ∪
        ((synCcompl (Class.cv (nb067AlphaDummy257)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb067_support_mem_0285 (f : Var) :
    (nb067AlphaDummy259 f) ∈
      (((synCcompl (Class.cv (nb067AlphaDummy259 f)))).fv ∪
        ((synCcompl (Class.cv (nb067AlphaDummy260 f)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb067_support_mem_0286 :
    (nb067AlphaDummy256) ∈
      (((Class.cv (nb067AlphaDummy256))).fv ∪ ((Class.cv (nb067AlphaDummy256))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb067_support_mem_0287 (f : Var) :
    (nb067AlphaDummy259 f) ∈
      (((Class.cv (nb067AlphaDummy259 f))).fv ∪ ((Class.cv (nb067AlphaDummy259 f))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb067_support_mem_0288 :
    (nb067AlphaDummy257) ∈
      (((synCcompl (Class.cv (nb067AlphaDummy256)))).fv ∪
        ((synCcompl (Class.cv (nb067AlphaDummy257)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb067_support_mem_0289 (f : Var) :
    (nb067AlphaDummy260 f) ∈
      (((synCcompl (Class.cv (nb067AlphaDummy259 f)))).fv ∪
        ((synCcompl (Class.cv (nb067AlphaDummy260 f)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb067_support_mem_0290 :
    (nb067AlphaDummy257) ∈
      (((Class.cv (nb067AlphaDummy257))).fv ∪ ((Class.cv (nb067AlphaDummy257))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb067_support_mem_0291 (f : Var) :
    (nb067AlphaDummy260 f) ∈
      (((Class.cv (nb067AlphaDummy260 f))).fv ∪ ((Class.cv (nb067AlphaDummy260 f))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb067_support_mem_0292 :
    (nb067AlphaDummy084) ∈
      (((Class.cv (nb067AlphaDummy085))).fv ∪ ((Class.cv (nb067AlphaDummy084))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb067_support_mem_0293 :
    (nb067AlphaDummy084) ∈
      (((synCcompl (Class.cab (nb067AlphaDummy241)
              (synWrex (nb067AlphaDummy242) (Class.cv (nb067AlphaDummy085))
                (Wff.classEq (Class.cv (nb067AlphaDummy241))
                  (synCphi (Class.cv (nb067AlphaDummy242)))))))).fv ∪ ((synCcompl
            (Class.cab (nb067AlphaDummy241)
              (synWrex (nb067AlphaDummy242) (Class.cv (nb067AlphaDummy084))
                (Wff.classEq (Class.cv (nb067AlphaDummy241))
                  (synCun (synCphi (Class.cv (nb067AlphaDummy242)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0292) 0))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0292) 1))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb067_support_mem_0294 (f : Var) :
    (nb067AlphaDummy087 f) ∈
      (((Class.cv (nb067AlphaDummy088 f))).fv ∪ ((Class.cv (nb067AlphaDummy087 f))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb067_support_mem_0295 (f : Var) :
    (nb067AlphaDummy087 f) ∈
      (((synCcompl (Class.cab (nb067AlphaDummy243 f)
              (synWrex (nb067AlphaDummy244 f) (Class.cv (nb067AlphaDummy088 f))
                (Wff.classEq (Class.cv (nb067AlphaDummy243 f))
                  (synCphi (Class.cv (nb067AlphaDummy244 f)))))))).fv ∪ ((synCcompl
            (Class.cab (nb067AlphaDummy243 f)
              (synWrex (nb067AlphaDummy244 f) (Class.cv (nb067AlphaDummy087 f))
                (Wff.classEq (Class.cv (nb067AlphaDummy243 f))
                  (synCun (synCphi (Class.cv (nb067AlphaDummy244 f)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0294 f) 0))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0294 f) 1))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb067_support_mem_0296 :
    (nb067AlphaDummy084) ∈
      (((Class.cab (nb067AlphaDummy241)
            (synWrex (nb067AlphaDummy242) (Class.cv (nb067AlphaDummy084))
              (Wff.classEq (Class.cv (nb067AlphaDummy241))
                (synCun (synCphi (Class.cv (nb067AlphaDummy242)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb067AlphaDummy241)
            (synWrex (nb067AlphaDummy242) (Class.cv (nb067AlphaDummy084))
              (Wff.classEq (Class.cv (nb067AlphaDummy241))
                (synCun (synCphi (Class.cv (nb067AlphaDummy242)))
                  (synCsn (synC0c))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0292) 0))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0292) 1))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb067_support_mem_0297 (f : Var) :
    (nb067AlphaDummy087 f) ∈
      (((Class.cab (nb067AlphaDummy243 f)
            (synWrex (nb067AlphaDummy244 f) (Class.cv (nb067AlphaDummy087 f))
              (Wff.classEq (Class.cv (nb067AlphaDummy243 f))
                (synCun (synCphi (Class.cv (nb067AlphaDummy244 f)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb067AlphaDummy243 f)
            (synWrex (nb067AlphaDummy244 f) (Class.cv (nb067AlphaDummy087 f))
              (Wff.classEq (Class.cv (nb067AlphaDummy243 f))
                (synCun (synCphi (Class.cv (nb067AlphaDummy244 f)))
                  (synCsn (synC0c))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0294 f) 0))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0294 f) 1))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb067_support_mem_0298 :
    (nb067AlphaDummy242) ∈
      (((synCcompl (synCphi (Class.cv (nb067AlphaDummy242))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb067_support_mem_0299 (f : Var) :
    (nb067AlphaDummy244 f) ∈
      (((synCcompl (synCphi (Class.cv (nb067AlphaDummy244 f))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb067_support_mem_0300 :
    (nb067AlphaDummy242) ∈
      (((synCphi (Class.cv (nb067AlphaDummy242)))).fv ∪
        ((synCphi (Class.cv (nb067AlphaDummy242)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb067_support_mem_0301 (f : Var) :
    (nb067AlphaDummy244 f) ∈
      (((synCphi (Class.cv (nb067AlphaDummy244 f)))).fv ∪
        ((synCphi (Class.cv (nb067AlphaDummy244 f)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb067_support_mem_0302 :
    (nb067AlphaDummy278) ∈
      (((Class.cv (nb067AlphaDummy278))).fv ∪ ((Class.cv (nb067AlphaDummy277))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb067_support_mem_0303 :
    (nb067AlphaDummy278) ∈
      (((synCcompl (Class.cab (nb067AlphaDummy281)
              (synWrex (nb067AlphaDummy282) (Class.cv (nb067AlphaDummy278))
                (Wff.classEq (Class.cv (nb067AlphaDummy281))
                  (synCphi (Class.cv (nb067AlphaDummy282)))))))).fv ∪ ((synCcompl
            (Class.cab (nb067AlphaDummy281)
              (synWrex (nb067AlphaDummy282) (Class.cv (nb067AlphaDummy277))
                (Wff.classEq (Class.cv (nb067AlphaDummy281))
                  (synCun (synCphi (Class.cv (nb067AlphaDummy282)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0302) 0))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0302) 1))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb067_support_mem_0304 (f : Var) :
    (nb067AlphaDummy280 f) ∈
      (((Class.cv (nb067AlphaDummy280 f))).fv ∪ ((Class.cv (nb067AlphaDummy279 f))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb067_support_mem_0305 (f : Var) :
    (nb067AlphaDummy280 f) ∈
      (((synCcompl (Class.cab (nb067AlphaDummy283 f)
              (synWrex (nb067AlphaDummy284 f) (Class.cv (nb067AlphaDummy280 f))
                (Wff.classEq (Class.cv (nb067AlphaDummy283 f))
                  (synCphi (Class.cv (nb067AlphaDummy284 f)))))))).fv ∪ ((synCcompl
            (Class.cab (nb067AlphaDummy283 f)
              (synWrex (nb067AlphaDummy284 f) (Class.cv (nb067AlphaDummy279 f))
                (Wff.classEq (Class.cv (nb067AlphaDummy283 f))
                  (synCun (synCphi (Class.cv (nb067AlphaDummy284 f)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0304 f) 0))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0304 f) 1))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb067_support_mem_0306 :
    (nb067AlphaDummy278) ∈
      (((Class.cab (nb067AlphaDummy281)
            (synWrex (nb067AlphaDummy282) (Class.cv (nb067AlphaDummy278))
              (Wff.classEq (Class.cv (nb067AlphaDummy281))
                (synCphi (Class.cv (nb067AlphaDummy282))))))).fv ∪
        ((Class.cab (nb067AlphaDummy281)
            (synWrex (nb067AlphaDummy282) (Class.cv (nb067AlphaDummy278))
              (Wff.classEq (Class.cv (nb067AlphaDummy281))
                (synCphi (Class.cv (nb067AlphaDummy282))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0302) 0))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0302) 1))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb067_support_mem_0307 (f : Var) :
    (nb067AlphaDummy280 f) ∈
      (((Class.cab (nb067AlphaDummy283 f)
            (synWrex (nb067AlphaDummy284 f) (Class.cv (nb067AlphaDummy280 f))
              (Wff.classEq (Class.cv (nb067AlphaDummy283 f))
                (synCphi (Class.cv (nb067AlphaDummy284 f))))))).fv ∪
        ((Class.cab (nb067AlphaDummy283 f)
            (synWrex (nb067AlphaDummy284 f) (Class.cv (nb067AlphaDummy280 f))
              (Wff.classEq (Class.cv (nb067AlphaDummy283 f))
                (synCphi (Class.cv (nb067AlphaDummy284 f))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0304 f) 0))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb067_support_mem_0304 f) 1))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb067_support_mem_0308 :
    (nb067AlphaDummy282) ∈ (((Class.cv (nb067AlphaDummy282))).fv) :=
  by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb067_support_mem_0309 (f : Var) :
    (nb067AlphaDummy284 f) ∈ (((Class.cv (nb067AlphaDummy284 f))).fv) :=
  by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb067_support_mem_0310 :
    (nb067AlphaDummy289) ∈
      (((Wff.classMem (Class.cv (nb067AlphaDummy289)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb067AlphaDummy289)) (synC1c))).fv ∪
        ((Class.cv (nb067AlphaDummy289))).fv) :=
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

theorem nb067_support_mem_0311 (f : Var) :
    (nb067AlphaDummy291 f) ∈
      (((Wff.classMem (Class.cv (nb067AlphaDummy291 f)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb067AlphaDummy291 f)) (synC1c))).fv ∪
        ((Class.cv (nb067AlphaDummy291 f))).fv) :=
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

theorem nb067_support_mem_0312 :
    (nb067AlphaDummy289) ∈
      (((Class.cv (nb067AlphaDummy289))).fv ∪ ((synC1c)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb067_support_mem_0313 (f : Var) :
    (nb067AlphaDummy291 f) ∈
      (((Class.cv (nb067AlphaDummy291 f))).fv ∪ ((synC1c)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb067_support_mem_0314 :
    (nb067AlphaDummy296) ∈
      (((synCnin (Class.cv (nb067AlphaDummy296)) (Class.cv (nb067AlphaDummy297)))).fv ∪
        ((synCnin (Class.cv (nb067AlphaDummy296))
            (Class.cv (nb067AlphaDummy297)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb067_support_mem_0315 (f : Var) :
    (nb067AlphaDummy299 f) ∈
      (((synCnin (Class.cv (nb067AlphaDummy299 f))
            (Class.cv (nb067AlphaDummy300 f)))).fv ∪
        ((synCnin (Class.cv (nb067AlphaDummy299 f))
            (Class.cv (nb067AlphaDummy300 f)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb067_support_mem_0316 :
    (nb067AlphaDummy296) ∈
      (((Class.cv (nb067AlphaDummy296))).fv ∪ ((Class.cv (nb067AlphaDummy297))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb067_support_mem_0317 (f : Var) :
    (nb067AlphaDummy299 f) ∈
      (((Class.cv (nb067AlphaDummy299 f))).fv ∪ ((Class.cv (nb067AlphaDummy300 f))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb067_support_mem_0318 :
    (nb067AlphaDummy297) ∈
      (((synCnin (Class.cv (nb067AlphaDummy296)) (Class.cv (nb067AlphaDummy297)))).fv ∪
        ((synCnin (Class.cv (nb067AlphaDummy296))
            (Class.cv (nb067AlphaDummy297)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb067_support_mem_0319 (f : Var) :
    (nb067AlphaDummy300 f) ∈
      (((synCnin (Class.cv (nb067AlphaDummy299 f))
            (Class.cv (nb067AlphaDummy300 f)))).fv ∪
        ((synCnin (Class.cv (nb067AlphaDummy299 f))
            (Class.cv (nb067AlphaDummy300 f)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired

end
