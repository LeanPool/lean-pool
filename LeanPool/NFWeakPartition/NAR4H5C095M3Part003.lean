/-
Copyright (c) 2026 Elliot Glazer and NFNotWPP contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elliot Glazer and NFNotWPP contributors
-/

module

public import LeanPool.NFWeakPartition.NAR4H5C095M3Part002

/-! NF weak partition development: NAR4H5C095M3Part003. -/


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

theorem nb095_fresh_027 (x : Var) (R : Class) :
    (nb095AlphaDummy262 x R) ∉
      (((Class.cab (nb095AlphaDummy257 x R)
            (synWrex (nb095AlphaDummy258 x R) (Class.cv (nb095AlphaDummy252 x R))
              (Wff.classEq (Class.cv (nb095AlphaDummy257 x R))
                (synCphi (Class.cv (nb095AlphaDummy258 x R))))))).fv ∪
        ((Class.cab (nb095AlphaDummy257 x R)
            (synWrex (nb095AlphaDummy258 x R) (Class.cv (nb095AlphaDummy252 x R))
              (Wff.classEq (Class.cv (nb095AlphaDummy257 x R))
                (synCphi (Class.cv (nb095AlphaDummy258 x R))))))).fv) :=
  by
  simpa only [nb095AlphaDummy262] using
    freshVar_not_mem
      (((Class.cab (nb095AlphaDummy257 x R)
            (synWrex (nb095AlphaDummy258 x R) (Class.cv (nb095AlphaDummy252 x R))
              (Wff.classEq (Class.cv (nb095AlphaDummy257 x R))
                (synCphi (Class.cv (nb095AlphaDummy258 x R))))))).fv ∪
        ((Class.cab (nb095AlphaDummy257 x R)
            (synWrex (nb095AlphaDummy258 x R) (Class.cv (nb095AlphaDummy252 x R))
              (Wff.classEq (Class.cv (nb095AlphaDummy257 x R))
                (synCphi (Class.cv (nb095AlphaDummy258 x R))))))).fv)
      0

theorem nb095_fresh_028 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095AlphaDummy329 D R S_cls E) ∉
      (((Class.cab (nb095AlphaDummy299 D R S_cls E)
            (synWrex (nb095AlphaDummy300 D R S_cls E)
              (Class.cv (nb095AlphaDummy295 D R S_cls E))
              (Wff.classEq (Class.cv (nb095AlphaDummy299 D R S_cls E))
                (synCun (synCphi (Class.cv (nb095AlphaDummy300 D R S_cls E)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb095AlphaDummy299 D R S_cls E)
            (synWrex (nb095AlphaDummy300 D R S_cls E)
              (Class.cv (nb095AlphaDummy295 D R S_cls E))
              (Wff.classEq (Class.cv (nb095AlphaDummy299 D R S_cls E))
                (synCun (synCphi (Class.cv (nb095AlphaDummy300 D R S_cls E)))
                  (synCsn (synC0c))))))).fv) :=
  by
  simpa only [nb095AlphaDummy329] using
    freshVar_not_mem
      (((Class.cab (nb095AlphaDummy299 D R S_cls E)
            (synWrex (nb095AlphaDummy300 D R S_cls E)
              (Class.cv (nb095AlphaDummy295 D R S_cls E))
              (Wff.classEq (Class.cv (nb095AlphaDummy299 D R S_cls E))
                (synCun (synCphi (Class.cv (nb095AlphaDummy300 D R S_cls E)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb095AlphaDummy299 D R S_cls E)
            (synWrex (nb095AlphaDummy300 D R S_cls E)
              (Class.cv (nb095AlphaDummy295 D R S_cls E))
              (Wff.classEq (Class.cv (nb095AlphaDummy299 D R S_cls E))
                (synCun (synCphi (Class.cv (nb095AlphaDummy300 D R S_cls E)))
                  (synCsn (synC0c))))))).fv)
      0

theorem nb095_fresh_029 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095AlphaDummy305 D R S_cls E) ∉
      (((Class.cab (nb095AlphaDummy299 D R S_cls E)
            (synWrex (nb095AlphaDummy300 D R S_cls E)
              (Class.cv (nb095AlphaDummy296 D R S_cls E))
              (Wff.classEq (Class.cv (nb095AlphaDummy299 D R S_cls E))
                (synCphi (Class.cv (nb095AlphaDummy300 D R S_cls E))))))).fv ∪
        ((Class.cab (nb095AlphaDummy299 D R S_cls E)
            (synWrex (nb095AlphaDummy300 D R S_cls E)
              (Class.cv (nb095AlphaDummy296 D R S_cls E))
              (Wff.classEq (Class.cv (nb095AlphaDummy299 D R S_cls E))
                (synCphi (Class.cv (nb095AlphaDummy300 D R S_cls E))))))).fv) :=
  by
  simpa only [nb095AlphaDummy305] using
    freshVar_not_mem
      (((Class.cab (nb095AlphaDummy299 D R S_cls E)
            (synWrex (nb095AlphaDummy300 D R S_cls E)
              (Class.cv (nb095AlphaDummy296 D R S_cls E))
              (Wff.classEq (Class.cv (nb095AlphaDummy299 D R S_cls E))
                (synCphi (Class.cv (nb095AlphaDummy300 D R S_cls E))))))).fv ∪
        ((Class.cab (nb095AlphaDummy299 D R S_cls E)
            (synWrex (nb095AlphaDummy300 D R S_cls E)
              (Class.cv (nb095AlphaDummy296 D R S_cls E))
              (Wff.classEq (Class.cv (nb095AlphaDummy299 D R S_cls E))
                (synCphi (Class.cv (nb095AlphaDummy300 D R S_cls E))))))).fv)
      0

theorem nb095_fresh_030 (f : Var) :
    (nb095AlphaDummy330 f) ∉
      (((Class.cab (nb095AlphaDummy301 f)
            (synWrex (nb095AlphaDummy302 f) (Class.cv (nb095AlphaDummy297 f))
              (Wff.classEq (Class.cv (nb095AlphaDummy301 f))
                (synCun (synCphi (Class.cv (nb095AlphaDummy302 f)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb095AlphaDummy301 f)
            (synWrex (nb095AlphaDummy302 f) (Class.cv (nb095AlphaDummy297 f))
              (Wff.classEq (Class.cv (nb095AlphaDummy301 f))
                (synCun (synCphi (Class.cv (nb095AlphaDummy302 f)))
                  (synCsn (synC0c))))))).fv) :=
  by
  simpa only [nb095AlphaDummy330] using
    freshVar_not_mem
      (((Class.cab (nb095AlphaDummy301 f)
            (synWrex (nb095AlphaDummy302 f) (Class.cv (nb095AlphaDummy297 f))
              (Wff.classEq (Class.cv (nb095AlphaDummy301 f))
                (synCun (synCphi (Class.cv (nb095AlphaDummy302 f)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb095AlphaDummy301 f)
            (synWrex (nb095AlphaDummy302 f) (Class.cv (nb095AlphaDummy297 f))
              (Wff.classEq (Class.cv (nb095AlphaDummy301 f))
                (synCun (synCphi (Class.cv (nb095AlphaDummy302 f)))
                  (synCsn (synC0c))))))).fv)
      0

theorem nb095_fresh_031 (f : Var) :
    (nb095AlphaDummy306 f) ∉
      (((Class.cab (nb095AlphaDummy301 f)
            (synWrex (nb095AlphaDummy302 f) (Class.cv (nb095AlphaDummy298 f))
              (Wff.classEq (Class.cv (nb095AlphaDummy301 f))
                (synCphi (Class.cv (nb095AlphaDummy302 f))))))).fv ∪
        ((Class.cab (nb095AlphaDummy301 f)
            (synWrex (nb095AlphaDummy302 f) (Class.cv (nb095AlphaDummy298 f))
              (Wff.classEq (Class.cv (nb095AlphaDummy301 f))
                (synCphi (Class.cv (nb095AlphaDummy302 f))))))).fv) :=
  by
  simpa only [nb095AlphaDummy306] using
    freshVar_not_mem
      (((Class.cab (nb095AlphaDummy301 f)
            (synWrex (nb095AlphaDummy302 f) (Class.cv (nb095AlphaDummy298 f))
              (Wff.classEq (Class.cv (nb095AlphaDummy301 f))
                (synCphi (Class.cv (nb095AlphaDummy302 f))))))).fv ∪
        ((Class.cab (nb095AlphaDummy301 f)
            (synWrex (nb095AlphaDummy302 f) (Class.cv (nb095AlphaDummy298 f))
              (Wff.classEq (Class.cv (nb095AlphaDummy301 f))
                (synCphi (Class.cv (nb095AlphaDummy302 f))))))).fv)
      0

theorem nb095_fresh_032 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095AlphaDummy375 D R S_cls E) ∉
      (((Class.cab (nb095AlphaDummy345 D R S_cls E)
            (synWrex (nb095AlphaDummy346 D R S_cls E)
              (Class.cv (nb095AlphaDummy339 D R S_cls E))
              (Wff.classEq (Class.cv (nb095AlphaDummy345 D R S_cls E))
                (synCun (synCphi (Class.cv (nb095AlphaDummy346 D R S_cls E)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb095AlphaDummy345 D R S_cls E)
            (synWrex (nb095AlphaDummy346 D R S_cls E)
              (Class.cv (nb095AlphaDummy339 D R S_cls E))
              (Wff.classEq (Class.cv (nb095AlphaDummy345 D R S_cls E))
                (synCun (synCphi (Class.cv (nb095AlphaDummy346 D R S_cls E)))
                  (synCsn (synC0c))))))).fv) :=
  by
  simpa only [nb095AlphaDummy375] using
    freshVar_not_mem
      (((Class.cab (nb095AlphaDummy345 D R S_cls E)
            (synWrex (nb095AlphaDummy346 D R S_cls E)
              (Class.cv (nb095AlphaDummy339 D R S_cls E))
              (Wff.classEq (Class.cv (nb095AlphaDummy345 D R S_cls E))
                (synCun (synCphi (Class.cv (nb095AlphaDummy346 D R S_cls E)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb095AlphaDummy345 D R S_cls E)
            (synWrex (nb095AlphaDummy346 D R S_cls E)
              (Class.cv (nb095AlphaDummy339 D R S_cls E))
              (Wff.classEq (Class.cv (nb095AlphaDummy345 D R S_cls E))
                (synCun (synCphi (Class.cv (nb095AlphaDummy346 D R S_cls E)))
                  (synCsn (synC0c))))))).fv)
      0

theorem nb095_fresh_033 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095AlphaDummy351 D R S_cls E) ∉
      (((Class.cab (nb095AlphaDummy345 D R S_cls E)
            (synWrex (nb095AlphaDummy346 D R S_cls E)
              (Class.cv (nb095AlphaDummy340 D R S_cls E))
              (Wff.classEq (Class.cv (nb095AlphaDummy345 D R S_cls E))
                (synCphi (Class.cv (nb095AlphaDummy346 D R S_cls E))))))).fv ∪
        ((Class.cab (nb095AlphaDummy345 D R S_cls E)
            (synWrex (nb095AlphaDummy346 D R S_cls E)
              (Class.cv (nb095AlphaDummy340 D R S_cls E))
              (Wff.classEq (Class.cv (nb095AlphaDummy345 D R S_cls E))
                (synCphi (Class.cv (nb095AlphaDummy346 D R S_cls E))))))).fv) :=
  by
  simpa only [nb095AlphaDummy351] using
    freshVar_not_mem
      (((Class.cab (nb095AlphaDummy345 D R S_cls E)
            (synWrex (nb095AlphaDummy346 D R S_cls E)
              (Class.cv (nb095AlphaDummy340 D R S_cls E))
              (Wff.classEq (Class.cv (nb095AlphaDummy345 D R S_cls E))
                (synCphi (Class.cv (nb095AlphaDummy346 D R S_cls E))))))).fv ∪
        ((Class.cab (nb095AlphaDummy345 D R S_cls E)
            (synWrex (nb095AlphaDummy346 D R S_cls E)
              (Class.cv (nb095AlphaDummy340 D R S_cls E))
              (Wff.classEq (Class.cv (nb095AlphaDummy345 D R S_cls E))
                (synCphi (Class.cv (nb095AlphaDummy346 D R S_cls E))))))).fv)
      0

theorem nb095_fresh_034 (u : Var) (S_cls : Class) :
    (nb095AlphaDummy376 u S_cls) ∉
      (((Class.cab (nb095AlphaDummy347 u S_cls) (synWrex (nb095AlphaDummy348 u S_cls)
              (Class.cv (nb095AlphaDummy341 u S_cls))
              (Wff.classEq (Class.cv (nb095AlphaDummy347 u S_cls))
                (synCun (synCphi (Class.cv (nb095AlphaDummy348 u S_cls)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb095AlphaDummy347 u S_cls)
            (synWrex (nb095AlphaDummy348 u S_cls) (Class.cv (nb095AlphaDummy341 u S_cls))
              (Wff.classEq (Class.cv (nb095AlphaDummy347 u S_cls))
                (synCun (synCphi (Class.cv (nb095AlphaDummy348 u S_cls)))
                  (synCsn (synC0c))))))).fv) :=
  by
  simpa only [nb095AlphaDummy376] using
    freshVar_not_mem
      (((Class.cab (nb095AlphaDummy347 u S_cls) (synWrex (nb095AlphaDummy348 u S_cls)
              (Class.cv (nb095AlphaDummy341 u S_cls))
              (Wff.classEq (Class.cv (nb095AlphaDummy347 u S_cls))
                (synCun (synCphi (Class.cv (nb095AlphaDummy348 u S_cls)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb095AlphaDummy347 u S_cls)
            (synWrex (nb095AlphaDummy348 u S_cls) (Class.cv (nb095AlphaDummy341 u S_cls))
              (Wff.classEq (Class.cv (nb095AlphaDummy347 u S_cls))
                (synCun (synCphi (Class.cv (nb095AlphaDummy348 u S_cls)))
                  (synCsn (synC0c))))))).fv)
      0

theorem nb095_fresh_035 (u : Var) (S_cls : Class) :
    (nb095AlphaDummy352 u S_cls) ∉
      (((Class.cab (nb095AlphaDummy347 u S_cls) (synWrex (nb095AlphaDummy348 u S_cls)
              (Class.cv (nb095AlphaDummy342 u S_cls))
              (Wff.classEq (Class.cv (nb095AlphaDummy347 u S_cls))
                (synCphi (Class.cv (nb095AlphaDummy348 u S_cls))))))).fv ∪
        ((Class.cab (nb095AlphaDummy347 u S_cls) (synWrex (nb095AlphaDummy348 u S_cls)
              (Class.cv (nb095AlphaDummy342 u S_cls))
              (Wff.classEq (Class.cv (nb095AlphaDummy347 u S_cls))
                (synCphi (Class.cv (nb095AlphaDummy348 u S_cls))))))).fv) :=
  by
  simpa only [nb095AlphaDummy352] using
    freshVar_not_mem
      (((Class.cab (nb095AlphaDummy347 u S_cls) (synWrex (nb095AlphaDummy348 u S_cls)
              (Class.cv (nb095AlphaDummy342 u S_cls))
              (Wff.classEq (Class.cv (nb095AlphaDummy347 u S_cls))
                (synCphi (Class.cv (nb095AlphaDummy348 u S_cls))))))).fv ∪
        ((Class.cab (nb095AlphaDummy347 u S_cls) (synWrex (nb095AlphaDummy348 u S_cls)
              (Class.cv (nb095AlphaDummy342 u S_cls))
              (Wff.classEq (Class.cv (nb095AlphaDummy347 u S_cls))
                (synCphi (Class.cv (nb095AlphaDummy348 u S_cls))))))).fv)
      0

theorem nb095_fresh_036 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095AlphaDummy399 D R S_cls E) ∉
      (((Class.cab (nb095AlphaDummy393 D R S_cls E)
            (synWrex (nb095AlphaDummy394 D R S_cls E)
              (Class.cv (nb095AlphaDummy385 D R S_cls E))
              (Wff.classEq (Class.cv (nb095AlphaDummy393 D R S_cls E))
                (synCphi (Class.cv (nb095AlphaDummy394 D R S_cls E))))))).fv ∪
        ((Class.cab (nb095AlphaDummy393 D R S_cls E)
            (synWrex (nb095AlphaDummy394 D R S_cls E)
              (Class.cv (nb095AlphaDummy385 D R S_cls E))
              (Wff.classEq (Class.cv (nb095AlphaDummy393 D R S_cls E))
                (synCphi (Class.cv (nb095AlphaDummy394 D R S_cls E))))))).fv) :=
  by
  simpa only [nb095AlphaDummy399] using
    freshVar_not_mem
      (((Class.cab (nb095AlphaDummy393 D R S_cls E)
            (synWrex (nb095AlphaDummy394 D R S_cls E)
              (Class.cv (nb095AlphaDummy385 D R S_cls E))
              (Wff.classEq (Class.cv (nb095AlphaDummy393 D R S_cls E))
                (synCphi (Class.cv (nb095AlphaDummy394 D R S_cls E))))))).fv ∪
        ((Class.cab (nb095AlphaDummy393 D R S_cls E)
            (synWrex (nb095AlphaDummy394 D R S_cls E)
              (Class.cv (nb095AlphaDummy385 D R S_cls E))
              (Wff.classEq (Class.cv (nb095AlphaDummy393 D R S_cls E))
                (synCphi (Class.cv (nb095AlphaDummy394 D R S_cls E))))))).fv)
      0

theorem nb095_fresh_037 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095AlphaDummy423 D R S_cls E) ∉
      (((Class.cab (nb095AlphaDummy393 D R S_cls E)
            (synWrex (nb095AlphaDummy394 D R S_cls E)
              (Class.cv (nb095AlphaDummy386 D R S_cls E))
              (Wff.classEq (Class.cv (nb095AlphaDummy393 D R S_cls E))
                (synCun (synCphi (Class.cv (nb095AlphaDummy394 D R S_cls E)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb095AlphaDummy393 D R S_cls E)
            (synWrex (nb095AlphaDummy394 D R S_cls E)
              (Class.cv (nb095AlphaDummy386 D R S_cls E))
              (Wff.classEq (Class.cv (nb095AlphaDummy393 D R S_cls E))
                (synCun (synCphi (Class.cv (nb095AlphaDummy394 D R S_cls E)))
                  (synCsn (synC0c))))))).fv) :=
  by
  simpa only [nb095AlphaDummy423] using
    freshVar_not_mem
      (((Class.cab (nb095AlphaDummy393 D R S_cls E)
            (synWrex (nb095AlphaDummy394 D R S_cls E)
              (Class.cv (nb095AlphaDummy386 D R S_cls E))
              (Wff.classEq (Class.cv (nb095AlphaDummy393 D R S_cls E))
                (synCun (synCphi (Class.cv (nb095AlphaDummy394 D R S_cls E)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb095AlphaDummy393 D R S_cls E)
            (synWrex (nb095AlphaDummy394 D R S_cls E)
              (Class.cv (nb095AlphaDummy386 D R S_cls E))
              (Wff.classEq (Class.cv (nb095AlphaDummy393 D R S_cls E))
                (synCun (synCphi (Class.cv (nb095AlphaDummy394 D R S_cls E)))
                  (synCsn (synC0c))))))).fv)
      0

theorem nb095_fresh_038 (f : Var) :
    (nb095AlphaDummy400 f) ∉
      (((Class.cab (nb095AlphaDummy395 f)
            (synWrex (nb095AlphaDummy396 f) (Class.cv (nb095AlphaDummy388 f))
              (Wff.classEq (Class.cv (nb095AlphaDummy395 f))
                (synCphi (Class.cv (nb095AlphaDummy396 f))))))).fv ∪
        ((Class.cab (nb095AlphaDummy395 f)
            (synWrex (nb095AlphaDummy396 f) (Class.cv (nb095AlphaDummy388 f))
              (Wff.classEq (Class.cv (nb095AlphaDummy395 f))
                (synCphi (Class.cv (nb095AlphaDummy396 f))))))).fv) :=
  by
  simpa only [nb095AlphaDummy400] using
    freshVar_not_mem
      (((Class.cab (nb095AlphaDummy395 f)
            (synWrex (nb095AlphaDummy396 f) (Class.cv (nb095AlphaDummy388 f))
              (Wff.classEq (Class.cv (nb095AlphaDummy395 f))
                (synCphi (Class.cv (nb095AlphaDummy396 f))))))).fv ∪
        ((Class.cab (nb095AlphaDummy395 f)
            (synWrex (nb095AlphaDummy396 f) (Class.cv (nb095AlphaDummy388 f))
              (Wff.classEq (Class.cv (nb095AlphaDummy395 f))
                (synCphi (Class.cv (nb095AlphaDummy396 f))))))).fv)
      0

theorem nb095_fresh_039 (f : Var) :
    (nb095AlphaDummy424 f) ∉
      (((Class.cab (nb095AlphaDummy395 f)
            (synWrex (nb095AlphaDummy396 f) (Class.cv (nb095AlphaDummy389 f))
              (Wff.classEq (Class.cv (nb095AlphaDummy395 f))
                (synCun (synCphi (Class.cv (nb095AlphaDummy396 f)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb095AlphaDummy395 f)
            (synWrex (nb095AlphaDummy396 f) (Class.cv (nb095AlphaDummy389 f))
              (Wff.classEq (Class.cv (nb095AlphaDummy395 f))
                (synCun (synCphi (Class.cv (nb095AlphaDummy396 f)))
                  (synCsn (synC0c))))))).fv) :=
  by
  simpa only [nb095AlphaDummy424] using
    freshVar_not_mem
      (((Class.cab (nb095AlphaDummy395 f)
            (synWrex (nb095AlphaDummy396 f) (Class.cv (nb095AlphaDummy389 f))
              (Wff.classEq (Class.cv (nb095AlphaDummy395 f))
                (synCun (synCphi (Class.cv (nb095AlphaDummy396 f)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb095AlphaDummy395 f)
            (synWrex (nb095AlphaDummy396 f) (Class.cv (nb095AlphaDummy389 f))
              (Wff.classEq (Class.cv (nb095AlphaDummy395 f))
                (synCun (synCphi (Class.cv (nb095AlphaDummy396 f)))
                  (synCsn (synC0c))))))).fv)
      0

theorem nb095_fresh_040 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095AlphaDummy435 D R S_cls E) ∉
      (((Class.cab (nb095AlphaDummy429 D R S_cls E)
            (synWrex (nb095AlphaDummy430 D R S_cls E)
              (Class.cv (nb095AlphaDummy385 D R S_cls E))
              (Wff.classEq (Class.cv (nb095AlphaDummy429 D R S_cls E))
                (synCphi (Class.cv (nb095AlphaDummy430 D R S_cls E))))))).fv ∪
        ((Class.cab (nb095AlphaDummy429 D R S_cls E)
            (synWrex (nb095AlphaDummy430 D R S_cls E)
              (Class.cv (nb095AlphaDummy385 D R S_cls E))
              (Wff.classEq (Class.cv (nb095AlphaDummy429 D R S_cls E))
                (synCphi (Class.cv (nb095AlphaDummy430 D R S_cls E))))))).fv) :=
  by
  simpa only [nb095AlphaDummy435] using
    freshVar_not_mem
      (((Class.cab (nb095AlphaDummy429 D R S_cls E)
            (synWrex (nb095AlphaDummy430 D R S_cls E)
              (Class.cv (nb095AlphaDummy385 D R S_cls E))
              (Wff.classEq (Class.cv (nb095AlphaDummy429 D R S_cls E))
                (synCphi (Class.cv (nb095AlphaDummy430 D R S_cls E))))))).fv ∪
        ((Class.cab (nb095AlphaDummy429 D R S_cls E)
            (synWrex (nb095AlphaDummy430 D R S_cls E)
              (Class.cv (nb095AlphaDummy385 D R S_cls E))
              (Wff.classEq (Class.cv (nb095AlphaDummy429 D R S_cls E))
                (synCphi (Class.cv (nb095AlphaDummy430 D R S_cls E))))))).fv)
      0

theorem nb095_fresh_041 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095AlphaDummy459 D R S_cls E) ∉
      (((Class.cab (nb095AlphaDummy429 D R S_cls E)
            (synWrex (nb095AlphaDummy430 D R S_cls E)
              (Class.cv (nb095AlphaDummy387 D R S_cls E))
              (Wff.classEq (Class.cv (nb095AlphaDummy429 D R S_cls E))
                (synCun (synCphi (Class.cv (nb095AlphaDummy430 D R S_cls E)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb095AlphaDummy429 D R S_cls E)
            (synWrex (nb095AlphaDummy430 D R S_cls E)
              (Class.cv (nb095AlphaDummy387 D R S_cls E))
              (Wff.classEq (Class.cv (nb095AlphaDummy429 D R S_cls E))
                (synCun (synCphi (Class.cv (nb095AlphaDummy430 D R S_cls E)))
                  (synCsn (synC0c))))))).fv) :=
  by
  simpa only [nb095AlphaDummy459] using
    freshVar_not_mem
      (((Class.cab (nb095AlphaDummy429 D R S_cls E)
            (synWrex (nb095AlphaDummy430 D R S_cls E)
              (Class.cv (nb095AlphaDummy387 D R S_cls E))
              (Wff.classEq (Class.cv (nb095AlphaDummy429 D R S_cls E))
                (synCun (synCphi (Class.cv (nb095AlphaDummy430 D R S_cls E)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb095AlphaDummy429 D R S_cls E)
            (synWrex (nb095AlphaDummy430 D R S_cls E)
              (Class.cv (nb095AlphaDummy387 D R S_cls E))
              (Wff.classEq (Class.cv (nb095AlphaDummy429 D R S_cls E))
                (synCun (synCphi (Class.cv (nb095AlphaDummy430 D R S_cls E)))
                  (synCsn (synC0c))))))).fv)
      0

theorem nb095_fresh_042 (f : Var) :
    (nb095AlphaDummy436 f) ∉
      (((Class.cab (nb095AlphaDummy431 f)
            (synWrex (nb095AlphaDummy432 f) (Class.cv (nb095AlphaDummy388 f))
              (Wff.classEq (Class.cv (nb095AlphaDummy431 f))
                (synCphi (Class.cv (nb095AlphaDummy432 f))))))).fv ∪
        ((Class.cab (nb095AlphaDummy431 f)
            (synWrex (nb095AlphaDummy432 f) (Class.cv (nb095AlphaDummy388 f))
              (Wff.classEq (Class.cv (nb095AlphaDummy431 f))
                (synCphi (Class.cv (nb095AlphaDummy432 f))))))).fv) :=
  by
  simpa only [nb095AlphaDummy436] using
    freshVar_not_mem
      (((Class.cab (nb095AlphaDummy431 f)
            (synWrex (nb095AlphaDummy432 f) (Class.cv (nb095AlphaDummy388 f))
              (Wff.classEq (Class.cv (nb095AlphaDummy431 f))
                (synCphi (Class.cv (nb095AlphaDummy432 f))))))).fv ∪
        ((Class.cab (nb095AlphaDummy431 f)
            (synWrex (nb095AlphaDummy432 f) (Class.cv (nb095AlphaDummy388 f))
              (Wff.classEq (Class.cv (nb095AlphaDummy431 f))
                (synCphi (Class.cv (nb095AlphaDummy432 f))))))).fv)
      0

theorem nb095_fresh_043 (f : Var) :
    (nb095AlphaDummy460 f) ∉
      (((Class.cab (nb095AlphaDummy431 f)
            (synWrex (nb095AlphaDummy432 f) (Class.cv (nb095AlphaDummy390 f))
              (Wff.classEq (Class.cv (nb095AlphaDummy431 f))
                (synCun (synCphi (Class.cv (nb095AlphaDummy432 f)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb095AlphaDummy431 f)
            (synWrex (nb095AlphaDummy432 f) (Class.cv (nb095AlphaDummy390 f))
              (Wff.classEq (Class.cv (nb095AlphaDummy431 f))
                (synCun (synCphi (Class.cv (nb095AlphaDummy432 f)))
                  (synCsn (synC0c))))))).fv) :=
  by
  simpa only [nb095AlphaDummy460] using
    freshVar_not_mem
      (((Class.cab (nb095AlphaDummy431 f)
            (synWrex (nb095AlphaDummy432 f) (Class.cv (nb095AlphaDummy390 f))
              (Wff.classEq (Class.cv (nb095AlphaDummy431 f))
                (synCun (synCphi (Class.cv (nb095AlphaDummy432 f)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb095AlphaDummy431 f)
            (synWrex (nb095AlphaDummy432 f) (Class.cv (nb095AlphaDummy390 f))
              (Wff.classEq (Class.cv (nb095AlphaDummy431 f))
                (synCun (synCphi (Class.cv (nb095AlphaDummy432 f)))
                  (synCsn (synC0c))))))).fv)
      0

theorem nb095_fresh_044 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095AlphaDummy477 D R S_cls E) ∉
      (((Class.cab (nb095AlphaDummy471 D R S_cls E)
            (synWrex (nb095AlphaDummy472 D R S_cls E)
              (Class.cv (nb095AlphaDummy465 D R S_cls E))
              (Wff.classEq (Class.cv (nb095AlphaDummy471 D R S_cls E))
                (synCphi (Class.cv (nb095AlphaDummy472 D R S_cls E))))))).fv ∪
        ((Class.cab (nb095AlphaDummy471 D R S_cls E)
            (synWrex (nb095AlphaDummy472 D R S_cls E)
              (Class.cv (nb095AlphaDummy465 D R S_cls E))
              (Wff.classEq (Class.cv (nb095AlphaDummy471 D R S_cls E))
                (synCphi (Class.cv (nb095AlphaDummy472 D R S_cls E))))))).fv) :=
  by
  simpa only [nb095AlphaDummy477] using
    freshVar_not_mem
      (((Class.cab (nb095AlphaDummy471 D R S_cls E)
            (synWrex (nb095AlphaDummy472 D R S_cls E)
              (Class.cv (nb095AlphaDummy465 D R S_cls E))
              (Wff.classEq (Class.cv (nb095AlphaDummy471 D R S_cls E))
                (synCphi (Class.cv (nb095AlphaDummy472 D R S_cls E))))))).fv ∪
        ((Class.cab (nb095AlphaDummy471 D R S_cls E)
            (synWrex (nb095AlphaDummy472 D R S_cls E)
              (Class.cv (nb095AlphaDummy465 D R S_cls E))
              (Wff.classEq (Class.cv (nb095AlphaDummy471 D R S_cls E))
                (synCphi (Class.cv (nb095AlphaDummy472 D R S_cls E))))))).fv)
      0

theorem nb095_fresh_045 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095AlphaDummy501 D R S_cls E) ∉
      (((Class.cab (nb095AlphaDummy471 D R S_cls E)
            (synWrex (nb095AlphaDummy472 D R S_cls E)
              (Class.cv (nb095AlphaDummy466 D R S_cls E))
              (Wff.classEq (Class.cv (nb095AlphaDummy471 D R S_cls E))
                (synCun (synCphi (Class.cv (nb095AlphaDummy472 D R S_cls E)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb095AlphaDummy471 D R S_cls E)
            (synWrex (nb095AlphaDummy472 D R S_cls E)
              (Class.cv (nb095AlphaDummy466 D R S_cls E))
              (Wff.classEq (Class.cv (nb095AlphaDummy471 D R S_cls E))
                (synCun (synCphi (Class.cv (nb095AlphaDummy472 D R S_cls E)))
                  (synCsn (synC0c))))))).fv) :=
  by
  simpa only [nb095AlphaDummy501] using
    freshVar_not_mem
      (((Class.cab (nb095AlphaDummy471 D R S_cls E)
            (synWrex (nb095AlphaDummy472 D R S_cls E)
              (Class.cv (nb095AlphaDummy466 D R S_cls E))
              (Wff.classEq (Class.cv (nb095AlphaDummy471 D R S_cls E))
                (synCun (synCphi (Class.cv (nb095AlphaDummy472 D R S_cls E)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb095AlphaDummy471 D R S_cls E)
            (synWrex (nb095AlphaDummy472 D R S_cls E)
              (Class.cv (nb095AlphaDummy466 D R S_cls E))
              (Wff.classEq (Class.cv (nb095AlphaDummy471 D R S_cls E))
                (synCun (synCphi (Class.cv (nb095AlphaDummy472 D R S_cls E)))
                  (synCsn (synC0c))))))).fv)
      0

theorem nb095_fresh_046 (f : Var) :
    (nb095AlphaDummy478 f) ∉
      (((Class.cab (nb095AlphaDummy473 f)
            (synWrex (nb095AlphaDummy474 f) (Class.cv (nb095AlphaDummy467 f))
              (Wff.classEq (Class.cv (nb095AlphaDummy473 f))
                (synCphi (Class.cv (nb095AlphaDummy474 f))))))).fv ∪
        ((Class.cab (nb095AlphaDummy473 f)
            (synWrex (nb095AlphaDummy474 f) (Class.cv (nb095AlphaDummy467 f))
              (Wff.classEq (Class.cv (nb095AlphaDummy473 f))
                (synCphi (Class.cv (nb095AlphaDummy474 f))))))).fv) :=
  by
  simpa only [nb095AlphaDummy478] using
    freshVar_not_mem
      (((Class.cab (nb095AlphaDummy473 f)
            (synWrex (nb095AlphaDummy474 f) (Class.cv (nb095AlphaDummy467 f))
              (Wff.classEq (Class.cv (nb095AlphaDummy473 f))
                (synCphi (Class.cv (nb095AlphaDummy474 f))))))).fv ∪
        ((Class.cab (nb095AlphaDummy473 f)
            (synWrex (nb095AlphaDummy474 f) (Class.cv (nb095AlphaDummy467 f))
              (Wff.classEq (Class.cv (nb095AlphaDummy473 f))
                (synCphi (Class.cv (nb095AlphaDummy474 f))))))).fv)
      0

theorem nb095_fresh_047 (f : Var) :
    (nb095AlphaDummy502 f) ∉
      (((Class.cab (nb095AlphaDummy473 f)
            (synWrex (nb095AlphaDummy474 f) (Class.cv (nb095AlphaDummy468 f))
              (Wff.classEq (Class.cv (nb095AlphaDummy473 f))
                (synCun (synCphi (Class.cv (nb095AlphaDummy474 f)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb095AlphaDummy473 f)
            (synWrex (nb095AlphaDummy474 f) (Class.cv (nb095AlphaDummy468 f))
              (Wff.classEq (Class.cv (nb095AlphaDummy473 f))
                (synCun (synCphi (Class.cv (nb095AlphaDummy474 f)))
                  (synCsn (synC0c))))))).fv) :=
  by
  simpa only [nb095AlphaDummy502] using
    freshVar_not_mem
      (((Class.cab (nb095AlphaDummy473 f)
            (synWrex (nb095AlphaDummy474 f) (Class.cv (nb095AlphaDummy468 f))
              (Wff.classEq (Class.cv (nb095AlphaDummy473 f))
                (synCun (synCphi (Class.cv (nb095AlphaDummy474 f)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb095AlphaDummy473 f)
            (synWrex (nb095AlphaDummy474 f) (Class.cv (nb095AlphaDummy468 f))
              (Wff.classEq (Class.cv (nb095AlphaDummy473 f))
                (synCun (synCphi (Class.cv (nb095AlphaDummy474 f)))
                  (synCsn (synC0c))))))).fv)
      0

theorem nb095_fresh_048 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095AlphaDummy537 D R S_cls E) ∉
      (((Class.cab (nb095AlphaDummy507 D R S_cls E)
            (synWrex (nb095AlphaDummy508 D R S_cls E)
              (Class.cv (nb095AlphaDummy465 D R S_cls E))
              (Wff.classEq (Class.cv (nb095AlphaDummy507 D R S_cls E))
                (synCun (synCphi (Class.cv (nb095AlphaDummy508 D R S_cls E)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb095AlphaDummy507 D R S_cls E)
            (synWrex (nb095AlphaDummy508 D R S_cls E)
              (Class.cv (nb095AlphaDummy465 D R S_cls E))
              (Wff.classEq (Class.cv (nb095AlphaDummy507 D R S_cls E))
                (synCun (synCphi (Class.cv (nb095AlphaDummy508 D R S_cls E)))
                  (synCsn (synC0c))))))).fv) :=
  by
  simpa only [nb095AlphaDummy537] using
    freshVar_not_mem
      (((Class.cab (nb095AlphaDummy507 D R S_cls E)
            (synWrex (nb095AlphaDummy508 D R S_cls E)
              (Class.cv (nb095AlphaDummy465 D R S_cls E))
              (Wff.classEq (Class.cv (nb095AlphaDummy507 D R S_cls E))
                (synCun (synCphi (Class.cv (nb095AlphaDummy508 D R S_cls E)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb095AlphaDummy507 D R S_cls E)
            (synWrex (nb095AlphaDummy508 D R S_cls E)
              (Class.cv (nb095AlphaDummy465 D R S_cls E))
              (Wff.classEq (Class.cv (nb095AlphaDummy507 D R S_cls E))
                (synCun (synCphi (Class.cv (nb095AlphaDummy508 D R S_cls E)))
                  (synCsn (synC0c))))))).fv)
      0

theorem nb095_fresh_049 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095AlphaDummy513 D R S_cls E) ∉
      (((Class.cab (nb095AlphaDummy507 D R S_cls E)
            (synWrex (nb095AlphaDummy508 D R S_cls E)
              (Class.cv (nb095AlphaDummy466 D R S_cls E))
              (Wff.classEq (Class.cv (nb095AlphaDummy507 D R S_cls E))
                (synCphi (Class.cv (nb095AlphaDummy508 D R S_cls E))))))).fv ∪
        ((Class.cab (nb095AlphaDummy507 D R S_cls E)
            (synWrex (nb095AlphaDummy508 D R S_cls E)
              (Class.cv (nb095AlphaDummy466 D R S_cls E))
              (Wff.classEq (Class.cv (nb095AlphaDummy507 D R S_cls E))
                (synCphi (Class.cv (nb095AlphaDummy508 D R S_cls E))))))).fv) :=
  by
  simpa only [nb095AlphaDummy513] using
    freshVar_not_mem
      (((Class.cab (nb095AlphaDummy507 D R S_cls E)
            (synWrex (nb095AlphaDummy508 D R S_cls E)
              (Class.cv (nb095AlphaDummy466 D R S_cls E))
              (Wff.classEq (Class.cv (nb095AlphaDummy507 D R S_cls E))
                (synCphi (Class.cv (nb095AlphaDummy508 D R S_cls E))))))).fv ∪
        ((Class.cab (nb095AlphaDummy507 D R S_cls E)
            (synWrex (nb095AlphaDummy508 D R S_cls E)
              (Class.cv (nb095AlphaDummy466 D R S_cls E))
              (Wff.classEq (Class.cv (nb095AlphaDummy507 D R S_cls E))
                (synCphi (Class.cv (nb095AlphaDummy508 D R S_cls E))))))).fv)
      0

theorem nb095_fresh_050 (f : Var) :
    (nb095AlphaDummy538 f) ∉
      (((Class.cab (nb095AlphaDummy509 f)
            (synWrex (nb095AlphaDummy510 f) (Class.cv (nb095AlphaDummy467 f))
              (Wff.classEq (Class.cv (nb095AlphaDummy509 f))
                (synCun (synCphi (Class.cv (nb095AlphaDummy510 f)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb095AlphaDummy509 f)
            (synWrex (nb095AlphaDummy510 f) (Class.cv (nb095AlphaDummy467 f))
              (Wff.classEq (Class.cv (nb095AlphaDummy509 f))
                (synCun (synCphi (Class.cv (nb095AlphaDummy510 f)))
                  (synCsn (synC0c))))))).fv) :=
  by
  simpa only [nb095AlphaDummy538] using
    freshVar_not_mem
      (((Class.cab (nb095AlphaDummy509 f)
            (synWrex (nb095AlphaDummy510 f) (Class.cv (nb095AlphaDummy467 f))
              (Wff.classEq (Class.cv (nb095AlphaDummy509 f))
                (synCun (synCphi (Class.cv (nb095AlphaDummy510 f)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb095AlphaDummy509 f)
            (synWrex (nb095AlphaDummy510 f) (Class.cv (nb095AlphaDummy467 f))
              (Wff.classEq (Class.cv (nb095AlphaDummy509 f))
                (synCun (synCphi (Class.cv (nb095AlphaDummy510 f)))
                  (synCsn (synC0c))))))).fv)
      0

theorem nb095_fresh_051 (f : Var) :
    (nb095AlphaDummy514 f) ∉
      (((Class.cab (nb095AlphaDummy509 f)
            (synWrex (nb095AlphaDummy510 f) (Class.cv (nb095AlphaDummy468 f))
              (Wff.classEq (Class.cv (nb095AlphaDummy509 f))
                (synCphi (Class.cv (nb095AlphaDummy510 f))))))).fv ∪
        ((Class.cab (nb095AlphaDummy509 f)
            (synWrex (nb095AlphaDummy510 f) (Class.cv (nb095AlphaDummy468 f))
              (Wff.classEq (Class.cv (nb095AlphaDummy509 f))
                (synCphi (Class.cv (nb095AlphaDummy510 f))))))).fv) :=
  by
  simpa only [nb095AlphaDummy514] using
    freshVar_not_mem
      (((Class.cab (nb095AlphaDummy509 f)
            (synWrex (nb095AlphaDummy510 f) (Class.cv (nb095AlphaDummy468 f))
              (Wff.classEq (Class.cv (nb095AlphaDummy509 f))
                (synCphi (Class.cv (nb095AlphaDummy510 f))))))).fv ∪
        ((Class.cab (nb095AlphaDummy509 f)
            (synWrex (nb095AlphaDummy510 f) (Class.cv (nb095AlphaDummy468 f))
              (Wff.classEq (Class.cv (nb095AlphaDummy509 f))
                (synCphi (Class.cv (nb095AlphaDummy510 f))))))).fv)
      0

theorem nb095_fresh_052 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095AlphaDummy573 D R S_cls E) ∉
      (((Class.cab (nb095AlphaDummy543 D R S_cls E)
            (synWrex (nb095AlphaDummy544 D R S_cls E)
              (Class.cv (nb095AlphaDummy386 D R S_cls E))
              (Wff.classEq (Class.cv (nb095AlphaDummy543 D R S_cls E))
                (synCun (synCphi (Class.cv (nb095AlphaDummy544 D R S_cls E)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb095AlphaDummy543 D R S_cls E)
            (synWrex (nb095AlphaDummy544 D R S_cls E)
              (Class.cv (nb095AlphaDummy386 D R S_cls E))
              (Wff.classEq (Class.cv (nb095AlphaDummy543 D R S_cls E))
                (synCun (synCphi (Class.cv (nb095AlphaDummy544 D R S_cls E)))
                  (synCsn (synC0c))))))).fv) :=
  by
  simpa only [nb095AlphaDummy573] using
    freshVar_not_mem
      (((Class.cab (nb095AlphaDummy543 D R S_cls E)
            (synWrex (nb095AlphaDummy544 D R S_cls E)
              (Class.cv (nb095AlphaDummy386 D R S_cls E))
              (Wff.classEq (Class.cv (nb095AlphaDummy543 D R S_cls E))
                (synCun (synCphi (Class.cv (nb095AlphaDummy544 D R S_cls E)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb095AlphaDummy543 D R S_cls E)
            (synWrex (nb095AlphaDummy544 D R S_cls E)
              (Class.cv (nb095AlphaDummy386 D R S_cls E))
              (Wff.classEq (Class.cv (nb095AlphaDummy543 D R S_cls E))
                (synCun (synCphi (Class.cv (nb095AlphaDummy544 D R S_cls E)))
                  (synCsn (synC0c))))))).fv)
      0

theorem nb095_fresh_053 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095AlphaDummy549 D R S_cls E) ∉
      (((Class.cab (nb095AlphaDummy543 D R S_cls E)
            (synWrex (nb095AlphaDummy544 D R S_cls E)
              (Class.cv (nb095AlphaDummy387 D R S_cls E))
              (Wff.classEq (Class.cv (nb095AlphaDummy543 D R S_cls E))
                (synCphi (Class.cv (nb095AlphaDummy544 D R S_cls E))))))).fv ∪
        ((Class.cab (nb095AlphaDummy543 D R S_cls E)
            (synWrex (nb095AlphaDummy544 D R S_cls E)
              (Class.cv (nb095AlphaDummy387 D R S_cls E))
              (Wff.classEq (Class.cv (nb095AlphaDummy543 D R S_cls E))
                (synCphi (Class.cv (nb095AlphaDummy544 D R S_cls E))))))).fv) :=
  by
  simpa only [nb095AlphaDummy549] using
    freshVar_not_mem
      (((Class.cab (nb095AlphaDummy543 D R S_cls E)
            (synWrex (nb095AlphaDummy544 D R S_cls E)
              (Class.cv (nb095AlphaDummy387 D R S_cls E))
              (Wff.classEq (Class.cv (nb095AlphaDummy543 D R S_cls E))
                (synCphi (Class.cv (nb095AlphaDummy544 D R S_cls E))))))).fv ∪
        ((Class.cab (nb095AlphaDummy543 D R S_cls E)
            (synWrex (nb095AlphaDummy544 D R S_cls E)
              (Class.cv (nb095AlphaDummy387 D R S_cls E))
              (Wff.classEq (Class.cv (nb095AlphaDummy543 D R S_cls E))
                (synCphi (Class.cv (nb095AlphaDummy544 D R S_cls E))))))).fv)
      0

theorem nb095_fresh_054 (f : Var) :
    (nb095AlphaDummy574 f) ∉
      (((Class.cab (nb095AlphaDummy545 f)
            (synWrex (nb095AlphaDummy546 f) (Class.cv (nb095AlphaDummy389 f))
              (Wff.classEq (Class.cv (nb095AlphaDummy545 f))
                (synCun (synCphi (Class.cv (nb095AlphaDummy546 f)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb095AlphaDummy545 f)
            (synWrex (nb095AlphaDummy546 f) (Class.cv (nb095AlphaDummy389 f))
              (Wff.classEq (Class.cv (nb095AlphaDummy545 f))
                (synCun (synCphi (Class.cv (nb095AlphaDummy546 f)))
                  (synCsn (synC0c))))))).fv) :=
  by
  simpa only [nb095AlphaDummy574] using
    freshVar_not_mem
      (((Class.cab (nb095AlphaDummy545 f)
            (synWrex (nb095AlphaDummy546 f) (Class.cv (nb095AlphaDummy389 f))
              (Wff.classEq (Class.cv (nb095AlphaDummy545 f))
                (synCun (synCphi (Class.cv (nb095AlphaDummy546 f)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb095AlphaDummy545 f)
            (synWrex (nb095AlphaDummy546 f) (Class.cv (nb095AlphaDummy389 f))
              (Wff.classEq (Class.cv (nb095AlphaDummy545 f))
                (synCun (synCphi (Class.cv (nb095AlphaDummy546 f)))
                  (synCsn (synC0c))))))).fv)
      0

theorem nb095_fresh_055 (f : Var) :
    (nb095AlphaDummy550 f) ∉
      (((Class.cab (nb095AlphaDummy545 f)
            (synWrex (nb095AlphaDummy546 f) (Class.cv (nb095AlphaDummy390 f))
              (Wff.classEq (Class.cv (nb095AlphaDummy545 f))
                (synCphi (Class.cv (nb095AlphaDummy546 f))))))).fv ∪
        ((Class.cab (nb095AlphaDummy545 f)
            (synWrex (nb095AlphaDummy546 f) (Class.cv (nb095AlphaDummy390 f))
              (Wff.classEq (Class.cv (nb095AlphaDummy545 f))
                (synCphi (Class.cv (nb095AlphaDummy546 f))))))).fv) :=
  by
  simpa only [nb095AlphaDummy550] using
    freshVar_not_mem
      (((Class.cab (nb095AlphaDummy545 f)
            (synWrex (nb095AlphaDummy546 f) (Class.cv (nb095AlphaDummy390 f))
              (Wff.classEq (Class.cv (nb095AlphaDummy545 f))
                (synCphi (Class.cv (nb095AlphaDummy546 f))))))).fv ∪
        ((Class.cab (nb095AlphaDummy545 f)
            (synWrex (nb095AlphaDummy546 f) (Class.cv (nb095AlphaDummy390 f))
              (Wff.classEq (Class.cv (nb095AlphaDummy545 f))
                (synCphi (Class.cv (nb095AlphaDummy546 f))))))).fv)
      0

theorem nb095_fresh_056 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095AlphaDummy585 D R S_cls E) ∉
      (((Class.cab (nb095AlphaDummy579 D R S_cls E)
            (synWrex (nb095AlphaDummy580 D R S_cls E)
              (Class.cv (nb095AlphaDummy003 D R S_cls E))
              (Wff.classEq (Class.cv (nb095AlphaDummy579 D R S_cls E))
                (synCphi (Class.cv (nb095AlphaDummy580 D R S_cls E))))))).fv ∪
        ((Class.cab (nb095AlphaDummy579 D R S_cls E)
            (synWrex (nb095AlphaDummy580 D R S_cls E)
              (Class.cv (nb095AlphaDummy003 D R S_cls E))
              (Wff.classEq (Class.cv (nb095AlphaDummy579 D R S_cls E))
                (synCphi (Class.cv (nb095AlphaDummy580 D R S_cls E))))))).fv) :=
  by
  simpa only [nb095AlphaDummy585] using
    freshVar_not_mem
      (((Class.cab (nb095AlphaDummy579 D R S_cls E)
            (synWrex (nb095AlphaDummy580 D R S_cls E)
              (Class.cv (nb095AlphaDummy003 D R S_cls E))
              (Wff.classEq (Class.cv (nb095AlphaDummy579 D R S_cls E))
                (synCphi (Class.cv (nb095AlphaDummy580 D R S_cls E))))))).fv ∪
        ((Class.cab (nb095AlphaDummy579 D R S_cls E)
            (synWrex (nb095AlphaDummy580 D R S_cls E)
              (Class.cv (nb095AlphaDummy003 D R S_cls E))
              (Wff.classEq (Class.cv (nb095AlphaDummy579 D R S_cls E))
                (synCphi (Class.cv (nb095AlphaDummy580 D R S_cls E))))))).fv)
      0

theorem nb095_fresh_057 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095AlphaDummy609 D R S_cls E) ∉
      (((Class.cab (nb095AlphaDummy579 D R S_cls E)
            (synWrex (nb095AlphaDummy580 D R S_cls E)
              (Class.cv (nb095AlphaDummy004 D R S_cls E))
              (Wff.classEq (Class.cv (nb095AlphaDummy579 D R S_cls E))
                (synCun (synCphi (Class.cv (nb095AlphaDummy580 D R S_cls E)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb095AlphaDummy579 D R S_cls E)
            (synWrex (nb095AlphaDummy580 D R S_cls E)
              (Class.cv (nb095AlphaDummy004 D R S_cls E))
              (Wff.classEq (Class.cv (nb095AlphaDummy579 D R S_cls E))
                (synCun (synCphi (Class.cv (nb095AlphaDummy580 D R S_cls E)))
                  (synCsn (synC0c))))))).fv) :=
  by
  simpa only [nb095AlphaDummy609] using
    freshVar_not_mem
      (((Class.cab (nb095AlphaDummy579 D R S_cls E)
            (synWrex (nb095AlphaDummy580 D R S_cls E)
              (Class.cv (nb095AlphaDummy004 D R S_cls E))
              (Wff.classEq (Class.cv (nb095AlphaDummy579 D R S_cls E))
                (synCun (synCphi (Class.cv (nb095AlphaDummy580 D R S_cls E)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb095AlphaDummy579 D R S_cls E)
            (synWrex (nb095AlphaDummy580 D R S_cls E)
              (Class.cv (nb095AlphaDummy004 D R S_cls E))
              (Wff.classEq (Class.cv (nb095AlphaDummy579 D R S_cls E))
                (synCun (synCphi (Class.cv (nb095AlphaDummy580 D R S_cls E)))
                  (synCsn (synC0c))))))).fv)
      0

theorem nb095_fresh_058 (x : Var) (u : Var) (D : Class) (R : Class) (S_cls : Class)
    (f : Var) (E : Class) :
    (nb095AlphaDummy586 x u D R S_cls f E) ∉
      (((Class.cab (nb095AlphaDummy581 x u D R S_cls f E)
            (synWrex (nb095AlphaDummy582 x u D R S_cls f E)
              (Class.cv (nb095AlphaDummy005 x u D R S_cls f E))
              (Wff.classEq (Class.cv (nb095AlphaDummy581 x u D R S_cls f E))
                (synCphi (Class.cv (nb095AlphaDummy582 x u D R S_cls f E))))))).fv ∪
        ((Class.cab (nb095AlphaDummy581 x u D R S_cls f E)
            (synWrex (nb095AlphaDummy582 x u D R S_cls f E)
              (Class.cv (nb095AlphaDummy005 x u D R S_cls f E))
              (Wff.classEq (Class.cv (nb095AlphaDummy581 x u D R S_cls f E))
                (synCphi (Class.cv (nb095AlphaDummy582 x u D R S_cls f E))))))).fv) :=
  by
  simpa only [nb095AlphaDummy586] using
    freshVar_not_mem
      (((Class.cab (nb095AlphaDummy581 x u D R S_cls f E)
            (synWrex (nb095AlphaDummy582 x u D R S_cls f E)
              (Class.cv (nb095AlphaDummy005 x u D R S_cls f E))
              (Wff.classEq (Class.cv (nb095AlphaDummy581 x u D R S_cls f E))
                (synCphi (Class.cv (nb095AlphaDummy582 x u D R S_cls f E))))))).fv ∪
        ((Class.cab (nb095AlphaDummy581 x u D R S_cls f E)
            (synWrex (nb095AlphaDummy582 x u D R S_cls f E)
              (Class.cv (nb095AlphaDummy005 x u D R S_cls f E))
              (Wff.classEq (Class.cv (nb095AlphaDummy581 x u D R S_cls f E))
                (synCphi (Class.cv (nb095AlphaDummy582 x u D R S_cls f E))))))).fv)
      0

theorem nb095_fresh_059 (x : Var) (u : Var) (D : Class) (R : Class) (S_cls : Class)
    (f : Var) (E : Class) :
    (nb095AlphaDummy610 x u D R S_cls f E) ∉
      (((Class.cab (nb095AlphaDummy581 x u D R S_cls f E)
            (synWrex (nb095AlphaDummy582 x u D R S_cls f E)
              (Class.cv (nb095AlphaDummy006 x u D R S_cls f E))
              (Wff.classEq (Class.cv (nb095AlphaDummy581 x u D R S_cls f E))
                (synCun (synCphi (Class.cv (nb095AlphaDummy582 x u D R S_cls f E)))
                  (synCsn (synC0c))))))).fv ∪
        ((Class.cab (nb095AlphaDummy581 x u D R S_cls f E)
            (synWrex (nb095AlphaDummy582 x u D R S_cls f E)
              (Class.cv (nb095AlphaDummy006 x u D R S_cls f E))
              (Wff.classEq (Class.cv (nb095AlphaDummy581 x u D R S_cls f E))
                (synCun (synCphi (Class.cv (nb095AlphaDummy582 x u D R S_cls f E)))
                  (synCsn (synC0c))))))).fv) :=
  by
  simpa only [nb095AlphaDummy610] using
    freshVar_not_mem
      (((Class.cab (nb095AlphaDummy581 x u D R S_cls f E)
            (synWrex (nb095AlphaDummy582 x u D R S_cls f E)
              (Class.cv (nb095AlphaDummy006 x u D R S_cls f E))
              (Wff.classEq (Class.cv (nb095AlphaDummy581 x u D R S_cls f E))
                (synCun (synCphi (Class.cv (nb095AlphaDummy582 x u D R S_cls f E)))
                  (synCsn (synC0c))))))).fv ∪
        ((Class.cab (nb095AlphaDummy581 x u D R S_cls f E)
            (synWrex (nb095AlphaDummy582 x u D R S_cls f E)
              (Class.cv (nb095AlphaDummy006 x u D R S_cls f E))
              (Wff.classEq (Class.cv (nb095AlphaDummy581 x u D R S_cls f E))
                (synCun (synCphi (Class.cv (nb095AlphaDummy582 x u D R S_cls f E)))
                  (synCsn (synC0c))))))).fv)
      0

theorem nb095_fresh_060 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095AlphaDummy631 D R S_cls E) ∉
      (((Class.cab (nb095AlphaDummy625 D R S_cls E)
            (synWrex (nb095AlphaDummy626 D R S_cls E)
              (Class.cv (nb095AlphaDummy619 D R S_cls E))
              (Wff.classEq (Class.cv (nb095AlphaDummy625 D R S_cls E))
                (synCphi (Class.cv (nb095AlphaDummy626 D R S_cls E))))))).fv ∪
        ((Class.cab (nb095AlphaDummy625 D R S_cls E)
            (synWrex (nb095AlphaDummy626 D R S_cls E)
              (Class.cv (nb095AlphaDummy619 D R S_cls E))
              (Wff.classEq (Class.cv (nb095AlphaDummy625 D R S_cls E))
                (synCphi (Class.cv (nb095AlphaDummy626 D R S_cls E))))))).fv) :=
  by
  simpa only [nb095AlphaDummy631] using
    freshVar_not_mem
      (((Class.cab (nb095AlphaDummy625 D R S_cls E)
            (synWrex (nb095AlphaDummy626 D R S_cls E)
              (Class.cv (nb095AlphaDummy619 D R S_cls E))
              (Wff.classEq (Class.cv (nb095AlphaDummy625 D R S_cls E))
                (synCphi (Class.cv (nb095AlphaDummy626 D R S_cls E))))))).fv ∪
        ((Class.cab (nb095AlphaDummy625 D R S_cls E)
            (synWrex (nb095AlphaDummy626 D R S_cls E)
              (Class.cv (nb095AlphaDummy619 D R S_cls E))
              (Wff.classEq (Class.cv (nb095AlphaDummy625 D R S_cls E))
                (synCphi (Class.cv (nb095AlphaDummy626 D R S_cls E))))))).fv)
      0

theorem nb095_fresh_061 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095AlphaDummy655 D R S_cls E) ∉
      (((Class.cab (nb095AlphaDummy625 D R S_cls E)
            (synWrex (nb095AlphaDummy626 D R S_cls E)
              (Class.cv (nb095AlphaDummy620 D R S_cls E))
              (Wff.classEq (Class.cv (nb095AlphaDummy625 D R S_cls E))
                (synCun (synCphi (Class.cv (nb095AlphaDummy626 D R S_cls E)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb095AlphaDummy625 D R S_cls E)
            (synWrex (nb095AlphaDummy626 D R S_cls E)
              (Class.cv (nb095AlphaDummy620 D R S_cls E))
              (Wff.classEq (Class.cv (nb095AlphaDummy625 D R S_cls E))
                (synCun (synCphi (Class.cv (nb095AlphaDummy626 D R S_cls E)))
                  (synCsn (synC0c))))))).fv) :=
  by
  simpa only [nb095AlphaDummy655] using
    freshVar_not_mem
      (((Class.cab (nb095AlphaDummy625 D R S_cls E)
            (synWrex (nb095AlphaDummy626 D R S_cls E)
              (Class.cv (nb095AlphaDummy620 D R S_cls E))
              (Wff.classEq (Class.cv (nb095AlphaDummy625 D R S_cls E))
                (synCun (synCphi (Class.cv (nb095AlphaDummy626 D R S_cls E)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb095AlphaDummy625 D R S_cls E)
            (synWrex (nb095AlphaDummy626 D R S_cls E)
              (Class.cv (nb095AlphaDummy620 D R S_cls E))
              (Wff.classEq (Class.cv (nb095AlphaDummy625 D R S_cls E))
                (synCun (synCphi (Class.cv (nb095AlphaDummy626 D R S_cls E)))
                  (synCsn (synC0c))))))).fv)
      0

theorem nb095_fresh_062 (x : Var) (D : Class) (R : Class) :
    (nb095AlphaDummy632 x D R) ∉
      (((Class.cab (nb095AlphaDummy627 x D R) (synWrex (nb095AlphaDummy628 x D R)
              (Class.cv (nb095AlphaDummy621 x D R))
              (Wff.classEq (Class.cv (nb095AlphaDummy627 x D R))
                (synCphi (Class.cv (nb095AlphaDummy628 x D R))))))).fv ∪
        ((Class.cab (nb095AlphaDummy627 x D R) (synWrex (nb095AlphaDummy628 x D R)
              (Class.cv (nb095AlphaDummy621 x D R))
              (Wff.classEq (Class.cv (nb095AlphaDummy627 x D R))
                (synCphi (Class.cv (nb095AlphaDummy628 x D R))))))).fv) :=
  by
  simpa only [nb095AlphaDummy632] using
    freshVar_not_mem
      (((Class.cab (nb095AlphaDummy627 x D R) (synWrex (nb095AlphaDummy628 x D R)
              (Class.cv (nb095AlphaDummy621 x D R))
              (Wff.classEq (Class.cv (nb095AlphaDummy627 x D R))
                (synCphi (Class.cv (nb095AlphaDummy628 x D R))))))).fv ∪
        ((Class.cab (nb095AlphaDummy627 x D R) (synWrex (nb095AlphaDummy628 x D R)
              (Class.cv (nb095AlphaDummy621 x D R))
              (Wff.classEq (Class.cv (nb095AlphaDummy627 x D R))
                (synCphi (Class.cv (nb095AlphaDummy628 x D R))))))).fv)
      0

theorem nb095_fresh_063 (x : Var) (D : Class) (R : Class) :
    (nb095AlphaDummy656 x D R) ∉
      (((Class.cab (nb095AlphaDummy627 x D R) (synWrex (nb095AlphaDummy628 x D R)
              (Class.cv (nb095AlphaDummy622 x D R))
              (Wff.classEq (Class.cv (nb095AlphaDummy627 x D R))
                (synCun (synCphi (Class.cv (nb095AlphaDummy628 x D R)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb095AlphaDummy627 x D R)
            (synWrex (nb095AlphaDummy628 x D R) (Class.cv (nb095AlphaDummy622 x D R))
              (Wff.classEq (Class.cv (nb095AlphaDummy627 x D R))
                (synCun (synCphi (Class.cv (nb095AlphaDummy628 x D R)))
                  (synCsn (synC0c))))))).fv) :=
  by
  simpa only [nb095AlphaDummy656] using
    freshVar_not_mem
      (((Class.cab (nb095AlphaDummy627 x D R) (synWrex (nb095AlphaDummy628 x D R)
              (Class.cv (nb095AlphaDummy622 x D R))
              (Wff.classEq (Class.cv (nb095AlphaDummy627 x D R))
                (synCun (synCphi (Class.cv (nb095AlphaDummy628 x D R)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb095AlphaDummy627 x D R)
            (synWrex (nb095AlphaDummy628 x D R) (Class.cv (nb095AlphaDummy622 x D R))
              (Wff.classEq (Class.cv (nb095AlphaDummy627 x D R))
                (synCun (synCphi (Class.cv (nb095AlphaDummy628 x D R)))
                  (synCsn (synC0c))))))).fv)
      0

theorem nb095_fresh_064 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095AlphaDummy667 D R S_cls E) ∉
      (((Class.cab (nb095AlphaDummy661 D R S_cls E)
            (synWrex (nb095AlphaDummy662 D R S_cls E)
              (synCfv (Class.cv (nb095AlphaDummy000 D R S_cls E))
                (Class.cv (nb095AlphaDummy003 D R S_cls E)))
              (Wff.classEq (Class.cv (nb095AlphaDummy661 D R S_cls E))
                (synCphi (Class.cv (nb095AlphaDummy662 D R S_cls E))))))).fv ∪
        ((Class.cab (nb095AlphaDummy661 D R S_cls E)
            (synWrex (nb095AlphaDummy662 D R S_cls E)
              (synCfv (Class.cv (nb095AlphaDummy000 D R S_cls E))
                (Class.cv (nb095AlphaDummy003 D R S_cls E)))
              (Wff.classEq (Class.cv (nb095AlphaDummy661 D R S_cls E))
                (synCphi (Class.cv (nb095AlphaDummy662 D R S_cls E))))))).fv) :=
  by
  simpa only [nb095AlphaDummy667] using
    freshVar_not_mem
      (((Class.cab (nb095AlphaDummy661 D R S_cls E)
            (synWrex (nb095AlphaDummy662 D R S_cls E)
              (synCfv (Class.cv (nb095AlphaDummy000 D R S_cls E))
                (Class.cv (nb095AlphaDummy003 D R S_cls E)))
              (Wff.classEq (Class.cv (nb095AlphaDummy661 D R S_cls E))
                (synCphi (Class.cv (nb095AlphaDummy662 D R S_cls E))))))).fv ∪
        ((Class.cab (nb095AlphaDummy661 D R S_cls E)
            (synWrex (nb095AlphaDummy662 D R S_cls E)
              (synCfv (Class.cv (nb095AlphaDummy000 D R S_cls E))
                (Class.cv (nb095AlphaDummy003 D R S_cls E)))
              (Wff.classEq (Class.cv (nb095AlphaDummy661 D R S_cls E))
                (synCphi (Class.cv (nb095AlphaDummy662 D R S_cls E))))))).fv)
      0

theorem nb095_fresh_065 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095AlphaDummy737 D R S_cls E) ∉
      (((Class.cab (nb095AlphaDummy661 D R S_cls E)
            (synWrex (nb095AlphaDummy662 D R S_cls E)
              (synCfv (Class.cv (nb095AlphaDummy000 D R S_cls E))
                (Class.cv (nb095AlphaDummy004 D R S_cls E)))
              (Wff.classEq (Class.cv (nb095AlphaDummy661 D R S_cls E))
                (synCun (synCphi (Class.cv (nb095AlphaDummy662 D R S_cls E)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb095AlphaDummy661 D R S_cls E)
            (synWrex (nb095AlphaDummy662 D R S_cls E)
              (synCfv (Class.cv (nb095AlphaDummy000 D R S_cls E))
                (Class.cv (nb095AlphaDummy004 D R S_cls E)))
              (Wff.classEq (Class.cv (nb095AlphaDummy661 D R S_cls E))
                (synCun (synCphi (Class.cv (nb095AlphaDummy662 D R S_cls E)))
                  (synCsn (synC0c))))))).fv) :=
  by
  simpa only [nb095AlphaDummy737] using
    freshVar_not_mem
      (((Class.cab (nb095AlphaDummy661 D R S_cls E)
            (synWrex (nb095AlphaDummy662 D R S_cls E)
              (synCfv (Class.cv (nb095AlphaDummy000 D R S_cls E))
                (Class.cv (nb095AlphaDummy004 D R S_cls E)))
              (Wff.classEq (Class.cv (nb095AlphaDummy661 D R S_cls E))
                (synCun (synCphi (Class.cv (nb095AlphaDummy662 D R S_cls E)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb095AlphaDummy661 D R S_cls E)
            (synWrex (nb095AlphaDummy662 D R S_cls E)
              (synCfv (Class.cv (nb095AlphaDummy000 D R S_cls E))
                (Class.cv (nb095AlphaDummy004 D R S_cls E)))
              (Wff.classEq (Class.cv (nb095AlphaDummy661 D R S_cls E))
                (synCun (synCphi (Class.cv (nb095AlphaDummy662 D R S_cls E)))
                  (synCsn (synC0c))))))).fv)
      0

theorem nb095_fresh_066 (x : Var) (u : Var) (D : Class) (R : Class) (S_cls : Class)
    (f : Var) (E : Class) :
    (nb095AlphaDummy668 x u D R S_cls f E) ∉
      (((Class.cab (nb095AlphaDummy663 x u D R S_cls f E)
            (synWrex (nb095AlphaDummy664 x u D R S_cls f E)
              (synCfv (Class.cv f) (Class.cv (nb095AlphaDummy005 x u D R S_cls f E)))
              (Wff.classEq (Class.cv (nb095AlphaDummy663 x u D R S_cls f E))
                (synCphi (Class.cv (nb095AlphaDummy664 x u D R S_cls f E))))))).fv ∪
        ((Class.cab (nb095AlphaDummy663 x u D R S_cls f E)
            (synWrex (nb095AlphaDummy664 x u D R S_cls f E)
              (synCfv (Class.cv f) (Class.cv (nb095AlphaDummy005 x u D R S_cls f E)))
              (Wff.classEq (Class.cv (nb095AlphaDummy663 x u D R S_cls f E))
                (synCphi (Class.cv (nb095AlphaDummy664 x u D R S_cls f E))))))).fv) :=
  by
  simpa only [nb095AlphaDummy668] using
    freshVar_not_mem
      (((Class.cab (nb095AlphaDummy663 x u D R S_cls f E)
            (synWrex (nb095AlphaDummy664 x u D R S_cls f E)
              (synCfv (Class.cv f) (Class.cv (nb095AlphaDummy005 x u D R S_cls f E)))
              (Wff.classEq (Class.cv (nb095AlphaDummy663 x u D R S_cls f E))
                (synCphi (Class.cv (nb095AlphaDummy664 x u D R S_cls f E))))))).fv ∪
        ((Class.cab (nb095AlphaDummy663 x u D R S_cls f E)
            (synWrex (nb095AlphaDummy664 x u D R S_cls f E)
              (synCfv (Class.cv f) (Class.cv (nb095AlphaDummy005 x u D R S_cls f E)))
              (Wff.classEq (Class.cv (nb095AlphaDummy663 x u D R S_cls f E))
                (synCphi (Class.cv (nb095AlphaDummy664 x u D R S_cls f E))))))).fv)
      0

theorem nb095_fresh_067 (x : Var) (u : Var) (D : Class) (R : Class) (S_cls : Class)
    (f : Var) (E : Class) :
    (nb095AlphaDummy738 x u D R S_cls f E) ∉
      (((Class.cab (nb095AlphaDummy663 x u D R S_cls f E)
            (synWrex (nb095AlphaDummy664 x u D R S_cls f E)
              (synCfv (Class.cv f) (Class.cv (nb095AlphaDummy006 x u D R S_cls f E)))
              (Wff.classEq (Class.cv (nb095AlphaDummy663 x u D R S_cls f E))
                (synCun (synCphi (Class.cv (nb095AlphaDummy664 x u D R S_cls f E)))
                  (synCsn (synC0c))))))).fv ∪
        ((Class.cab (nb095AlphaDummy663 x u D R S_cls f E)
            (synWrex (nb095AlphaDummy664 x u D R S_cls f E)
              (synCfv (Class.cv f) (Class.cv (nb095AlphaDummy006 x u D R S_cls f E)))
              (Wff.classEq (Class.cv (nb095AlphaDummy663 x u D R S_cls f E))
                (synCun (synCphi (Class.cv (nb095AlphaDummy664 x u D R S_cls f E)))
                  (synCsn (synC0c))))))).fv) :=
  by
  simpa only [nb095AlphaDummy738] using
    freshVar_not_mem
      (((Class.cab (nb095AlphaDummy663 x u D R S_cls f E)
            (synWrex (nb095AlphaDummy664 x u D R S_cls f E)
              (synCfv (Class.cv f) (Class.cv (nb095AlphaDummy006 x u D R S_cls f E)))
              (Wff.classEq (Class.cv (nb095AlphaDummy663 x u D R S_cls f E))
                (synCun (synCphi (Class.cv (nb095AlphaDummy664 x u D R S_cls f E)))
                  (synCsn (synC0c))))))).fv ∪
        ((Class.cab (nb095AlphaDummy663 x u D R S_cls f E)
            (synWrex (nb095AlphaDummy664 x u D R S_cls f E)
              (synCfv (Class.cv f) (Class.cv (nb095AlphaDummy006 x u D R S_cls f E)))
              (Wff.classEq (Class.cv (nb095AlphaDummy663 x u D R S_cls f E))
                (synCun (synCphi (Class.cv (nb095AlphaDummy664 x u D R S_cls f E)))
                  (synCsn (synC0c))))))).fv)
      0

theorem nb095_fresh_068 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095AlphaDummy673 D R S_cls E) ∉
      (((Class.cab (nb095AlphaDummy671 D R S_cls E) (Wff.classEq
            (Class.cab (nb095AlphaDummy669 D R S_cls E)
              (synWbr (Class.cv (nb095AlphaDummy003 D R S_cls E))
                (Class.cv (nb095AlphaDummy000 D R S_cls E))
                (Class.cv (nb095AlphaDummy669 D R S_cls E))))
            (synCsn (Class.cv (nb095AlphaDummy671 D R S_cls E)))))).fv) :=
  by
  simpa only [nb095AlphaDummy673] using
    freshVar_not_mem
      (((Class.cab (nb095AlphaDummy671 D R S_cls E) (Wff.classEq
            (Class.cab (nb095AlphaDummy669 D R S_cls E)
              (synWbr (Class.cv (nb095AlphaDummy003 D R S_cls E))
                (Class.cv (nb095AlphaDummy000 D R S_cls E))
                (Class.cv (nb095AlphaDummy669 D R S_cls E))))
            (synCsn (Class.cv (nb095AlphaDummy671 D R S_cls E)))))).fv)
      0

theorem nb095_fresh_069 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095AlphaDummy674 D R S_cls E) ∉
      (((Class.cab (nb095AlphaDummy671 D R S_cls E) (Wff.classEq
            (Class.cab (nb095AlphaDummy669 D R S_cls E)
              (synWbr (Class.cv (nb095AlphaDummy003 D R S_cls E))
                (Class.cv (nb095AlphaDummy000 D R S_cls E))
                (Class.cv (nb095AlphaDummy669 D R S_cls E))))
            (synCsn (Class.cv (nb095AlphaDummy671 D R S_cls E)))))).fv) :=
  by
  simpa only [nb095AlphaDummy674] using
    freshVar_not_mem
      (((Class.cab (nb095AlphaDummy671 D R S_cls E) (Wff.classEq
            (Class.cab (nb095AlphaDummy669 D R S_cls E)
              (synWbr (Class.cv (nb095AlphaDummy003 D R S_cls E))
                (Class.cv (nb095AlphaDummy000 D R S_cls E))
                (Class.cv (nb095AlphaDummy669 D R S_cls E))))
            (synCsn (Class.cv (nb095AlphaDummy671 D R S_cls E)))))).fv)
      1

theorem nb095_distinct_070 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095AlphaDummy673 D R S_cls E) ≠ (nb095AlphaDummy674 D R S_cls E) := by
  simpa only [nb095AlphaDummy673, nb095AlphaDummy674] using
    (freshVar_injective (((Class.cab (nb095AlphaDummy671 D R S_cls E) (Wff.classEq
            (Class.cab (nb095AlphaDummy669 D R S_cls E)
              (synWbr (Class.cv (nb095AlphaDummy003 D R S_cls E))
                (Class.cv (nb095AlphaDummy000 D R S_cls E))
                (Class.cv (nb095AlphaDummy669 D R S_cls E))))
            (synCsn (Class.cv (nb095AlphaDummy671 D R S_cls E)))))).fv)
      (i := 0) (j := 1) (by decide))

theorem nb095_fresh_071 (x : Var) (u : Var) (D : Class) (R : Class) (S_cls : Class)
    (f : Var) (E : Class) :
    (nb095AlphaDummy675 x u D R S_cls f E) ∉
      (((Class.cab (nb095AlphaDummy672 x u D R S_cls f E) (Wff.classEq
            (Class.cab (nb095AlphaDummy670 x u D R S_cls f E)
              (synWbr (Class.cv (nb095AlphaDummy005 x u D R S_cls f E)) (Class.cv f)
                (Class.cv (nb095AlphaDummy670 x u D R S_cls f E))))
            (synCsn (Class.cv (nb095AlphaDummy672 x u D R S_cls f E)))))).fv) :=
  by
  simpa only [nb095AlphaDummy675] using
    freshVar_not_mem
      (((Class.cab (nb095AlphaDummy672 x u D R S_cls f E) (Wff.classEq
            (Class.cab (nb095AlphaDummy670 x u D R S_cls f E)
              (synWbr (Class.cv (nb095AlphaDummy005 x u D R S_cls f E)) (Class.cv f)
                (Class.cv (nb095AlphaDummy670 x u D R S_cls f E))))
            (synCsn (Class.cv (nb095AlphaDummy672 x u D R S_cls f E)))))).fv)
      0

theorem nb095_fresh_072 (x : Var) (u : Var) (D : Class) (R : Class) (S_cls : Class)
    (f : Var) (E : Class) :
    (nb095AlphaDummy676 x u D R S_cls f E) ∉
      (((Class.cab (nb095AlphaDummy672 x u D R S_cls f E) (Wff.classEq
            (Class.cab (nb095AlphaDummy670 x u D R S_cls f E)
              (synWbr (Class.cv (nb095AlphaDummy005 x u D R S_cls f E)) (Class.cv f)
                (Class.cv (nb095AlphaDummy670 x u D R S_cls f E))))
            (synCsn (Class.cv (nb095AlphaDummy672 x u D R S_cls f E)))))).fv) :=
  by
  simpa only [nb095AlphaDummy676] using
    freshVar_not_mem
      (((Class.cab (nb095AlphaDummy672 x u D R S_cls f E) (Wff.classEq
            (Class.cab (nb095AlphaDummy670 x u D R S_cls f E)
              (synWbr (Class.cv (nb095AlphaDummy005 x u D R S_cls f E)) (Class.cv f)
                (Class.cv (nb095AlphaDummy670 x u D R S_cls f E))))
            (synCsn (Class.cv (nb095AlphaDummy672 x u D R S_cls f E)))))).fv)
      1

theorem nb095_distinct_073 (x : Var) (u : Var) (D : Class) (R : Class) (S_cls : Class)
    (f : Var) (E : Class) :
    (nb095AlphaDummy675 x u D R S_cls f E) ≠
      (nb095AlphaDummy676 x u D R S_cls f E) :=
  by
  simpa only [nb095AlphaDummy675, nb095AlphaDummy676] using
    (freshVar_injective (((Class.cab (nb095AlphaDummy672 x u D R S_cls f E) (Wff.classEq
            (Class.cab (nb095AlphaDummy670 x u D R S_cls f E)
              (synWbr (Class.cv (nb095AlphaDummy005 x u D R S_cls f E)) (Class.cv f)
                (Class.cv (nb095AlphaDummy670 x u D R S_cls f E))))
            (synCsn (Class.cv (nb095AlphaDummy672 x u D R S_cls f E)))))).fv)
      (i := 0) (j := 1) (by decide))

theorem nb095_fresh_074 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095AlphaDummy683 D R S_cls E) ∉
      (((Class.cab (nb095AlphaDummy677 D R S_cls E)
            (synWrex (nb095AlphaDummy678 D R S_cls E)
              (Class.cv (nb095AlphaDummy003 D R S_cls E))
              (Wff.classEq (Class.cv (nb095AlphaDummy677 D R S_cls E))
                (synCphi (Class.cv (nb095AlphaDummy678 D R S_cls E))))))).fv ∪
        ((Class.cab (nb095AlphaDummy677 D R S_cls E)
            (synWrex (nb095AlphaDummy678 D R S_cls E)
              (Class.cv (nb095AlphaDummy003 D R S_cls E))
              (Wff.classEq (Class.cv (nb095AlphaDummy677 D R S_cls E))
                (synCphi (Class.cv (nb095AlphaDummy678 D R S_cls E))))))).fv) :=
  by
  simpa only [nb095AlphaDummy683] using
    freshVar_not_mem
      (((Class.cab (nb095AlphaDummy677 D R S_cls E)
            (synWrex (nb095AlphaDummy678 D R S_cls E)
              (Class.cv (nb095AlphaDummy003 D R S_cls E))
              (Wff.classEq (Class.cv (nb095AlphaDummy677 D R S_cls E))
                (synCphi (Class.cv (nb095AlphaDummy678 D R S_cls E))))))).fv ∪
        ((Class.cab (nb095AlphaDummy677 D R S_cls E)
            (synWrex (nb095AlphaDummy678 D R S_cls E)
              (Class.cv (nb095AlphaDummy003 D R S_cls E))
              (Wff.classEq (Class.cv (nb095AlphaDummy677 D R S_cls E))
                (synCphi (Class.cv (nb095AlphaDummy678 D R S_cls E))))))).fv)
      0

theorem nb095_fresh_075 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095AlphaDummy707 D R S_cls E) ∉
      (((Class.cab (nb095AlphaDummy677 D R S_cls E)
            (synWrex (nb095AlphaDummy678 D R S_cls E)
              (Class.cv (nb095AlphaDummy669 D R S_cls E))
              (Wff.classEq (Class.cv (nb095AlphaDummy677 D R S_cls E))
                (synCun (synCphi (Class.cv (nb095AlphaDummy678 D R S_cls E)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb095AlphaDummy677 D R S_cls E)
            (synWrex (nb095AlphaDummy678 D R S_cls E)
              (Class.cv (nb095AlphaDummy669 D R S_cls E))
              (Wff.classEq (Class.cv (nb095AlphaDummy677 D R S_cls E))
                (synCun (synCphi (Class.cv (nb095AlphaDummy678 D R S_cls E)))
                  (synCsn (synC0c))))))).fv) :=
  by
  simpa only [nb095AlphaDummy707] using
    freshVar_not_mem
      (((Class.cab (nb095AlphaDummy677 D R S_cls E)
            (synWrex (nb095AlphaDummy678 D R S_cls E)
              (Class.cv (nb095AlphaDummy669 D R S_cls E))
              (Wff.classEq (Class.cv (nb095AlphaDummy677 D R S_cls E))
                (synCun (synCphi (Class.cv (nb095AlphaDummy678 D R S_cls E)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb095AlphaDummy677 D R S_cls E)
            (synWrex (nb095AlphaDummy678 D R S_cls E)
              (Class.cv (nb095AlphaDummy669 D R S_cls E))
              (Wff.classEq (Class.cv (nb095AlphaDummy677 D R S_cls E))
                (synCun (synCphi (Class.cv (nb095AlphaDummy678 D R S_cls E)))
                  (synCsn (synC0c))))))).fv)
      0

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

theorem nb095_fresh_076 (x : Var) (u : Var) (D : Class) (R : Class) (S_cls : Class)
    (f : Var) (E : Class) :
    (nb095AlphaDummy684 x u D R S_cls f E) ∉
      (((Class.cab (nb095AlphaDummy679 x u D R S_cls f E)
            (synWrex (nb095AlphaDummy680 x u D R S_cls f E)
              (Class.cv (nb095AlphaDummy005 x u D R S_cls f E))
              (Wff.classEq (Class.cv (nb095AlphaDummy679 x u D R S_cls f E))
                (synCphi (Class.cv (nb095AlphaDummy680 x u D R S_cls f E))))))).fv ∪
        ((Class.cab (nb095AlphaDummy679 x u D R S_cls f E)
            (synWrex (nb095AlphaDummy680 x u D R S_cls f E)
              (Class.cv (nb095AlphaDummy005 x u D R S_cls f E))
              (Wff.classEq (Class.cv (nb095AlphaDummy679 x u D R S_cls f E))
                (synCphi (Class.cv (nb095AlphaDummy680 x u D R S_cls f E))))))).fv) :=
  by
  simpa only [nb095AlphaDummy684] using
    freshVar_not_mem
      (((Class.cab (nb095AlphaDummy679 x u D R S_cls f E)
            (synWrex (nb095AlphaDummy680 x u D R S_cls f E)
              (Class.cv (nb095AlphaDummy005 x u D R S_cls f E))
              (Wff.classEq (Class.cv (nb095AlphaDummy679 x u D R S_cls f E))
                (synCphi (Class.cv (nb095AlphaDummy680 x u D R S_cls f E))))))).fv ∪
        ((Class.cab (nb095AlphaDummy679 x u D R S_cls f E)
            (synWrex (nb095AlphaDummy680 x u D R S_cls f E)
              (Class.cv (nb095AlphaDummy005 x u D R S_cls f E))
              (Wff.classEq (Class.cv (nb095AlphaDummy679 x u D R S_cls f E))
                (synCphi (Class.cv (nb095AlphaDummy680 x u D R S_cls f E))))))).fv)
      0

theorem nb095_fresh_077 (x : Var) (u : Var) (D : Class) (R : Class) (S_cls : Class)
    (f : Var) (E : Class) :
    (nb095AlphaDummy708 x u D R S_cls f E) ∉
      (((Class.cab (nb095AlphaDummy679 x u D R S_cls f E)
            (synWrex (nb095AlphaDummy680 x u D R S_cls f E)
              (Class.cv (nb095AlphaDummy670 x u D R S_cls f E))
              (Wff.classEq (Class.cv (nb095AlphaDummy679 x u D R S_cls f E))
                (synCun (synCphi (Class.cv (nb095AlphaDummy680 x u D R S_cls f E)))
                  (synCsn (synC0c))))))).fv ∪
        ((Class.cab (nb095AlphaDummy679 x u D R S_cls f E)
            (synWrex (nb095AlphaDummy680 x u D R S_cls f E)
              (Class.cv (nb095AlphaDummy670 x u D R S_cls f E))
              (Wff.classEq (Class.cv (nb095AlphaDummy679 x u D R S_cls f E))
                (synCun (synCphi (Class.cv (nb095AlphaDummy680 x u D R S_cls f E)))
                  (synCsn (synC0c))))))).fv) :=
  by
  simpa only [nb095AlphaDummy708] using
    freshVar_not_mem
      (((Class.cab (nb095AlphaDummy679 x u D R S_cls f E)
            (synWrex (nb095AlphaDummy680 x u D R S_cls f E)
              (Class.cv (nb095AlphaDummy670 x u D R S_cls f E))
              (Wff.classEq (Class.cv (nb095AlphaDummy679 x u D R S_cls f E))
                (synCun (synCphi (Class.cv (nb095AlphaDummy680 x u D R S_cls f E)))
                  (synCsn (synC0c))))))).fv ∪
        ((Class.cab (nb095AlphaDummy679 x u D R S_cls f E)
            (synWrex (nb095AlphaDummy680 x u D R S_cls f E)
              (Class.cv (nb095AlphaDummy670 x u D R S_cls f E))
              (Wff.classEq (Class.cv (nb095AlphaDummy679 x u D R S_cls f E))
                (synCun (synCphi (Class.cv (nb095AlphaDummy680 x u D R S_cls f E)))
                  (synCsn (synC0c))))))).fv)
      0

theorem nb095_fresh_078 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095AlphaDummy743 D R S_cls E) ∉
      (((Class.cab (nb095AlphaDummy741 D R S_cls E) (Wff.classEq
            (Class.cab (nb095AlphaDummy739 D R S_cls E)
              (synWbr (Class.cv (nb095AlphaDummy004 D R S_cls E))
                (Class.cv (nb095AlphaDummy000 D R S_cls E))
                (Class.cv (nb095AlphaDummy739 D R S_cls E))))
            (synCsn (Class.cv (nb095AlphaDummy741 D R S_cls E)))))).fv) :=
  by
  simpa only [nb095AlphaDummy743] using
    freshVar_not_mem
      (((Class.cab (nb095AlphaDummy741 D R S_cls E) (Wff.classEq
            (Class.cab (nb095AlphaDummy739 D R S_cls E)
              (synWbr (Class.cv (nb095AlphaDummy004 D R S_cls E))
                (Class.cv (nb095AlphaDummy000 D R S_cls E))
                (Class.cv (nb095AlphaDummy739 D R S_cls E))))
            (synCsn (Class.cv (nb095AlphaDummy741 D R S_cls E)))))).fv)
      0

theorem nb095_fresh_079 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095AlphaDummy744 D R S_cls E) ∉
      (((Class.cab (nb095AlphaDummy741 D R S_cls E) (Wff.classEq
            (Class.cab (nb095AlphaDummy739 D R S_cls E)
              (synWbr (Class.cv (nb095AlphaDummy004 D R S_cls E))
                (Class.cv (nb095AlphaDummy000 D R S_cls E))
                (Class.cv (nb095AlphaDummy739 D R S_cls E))))
            (synCsn (Class.cv (nb095AlphaDummy741 D R S_cls E)))))).fv) :=
  by
  simpa only [nb095AlphaDummy744] using
    freshVar_not_mem
      (((Class.cab (nb095AlphaDummy741 D R S_cls E) (Wff.classEq
            (Class.cab (nb095AlphaDummy739 D R S_cls E)
              (synWbr (Class.cv (nb095AlphaDummy004 D R S_cls E))
                (Class.cv (nb095AlphaDummy000 D R S_cls E))
                (Class.cv (nb095AlphaDummy739 D R S_cls E))))
            (synCsn (Class.cv (nb095AlphaDummy741 D R S_cls E)))))).fv)
      1

theorem nb095_distinct_080 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095AlphaDummy743 D R S_cls E) ≠ (nb095AlphaDummy744 D R S_cls E) := by
  simpa only [nb095AlphaDummy743, nb095AlphaDummy744] using
    (freshVar_injective (((Class.cab (nb095AlphaDummy741 D R S_cls E) (Wff.classEq
            (Class.cab (nb095AlphaDummy739 D R S_cls E)
              (synWbr (Class.cv (nb095AlphaDummy004 D R S_cls E))
                (Class.cv (nb095AlphaDummy000 D R S_cls E))
                (Class.cv (nb095AlphaDummy739 D R S_cls E))))
            (synCsn (Class.cv (nb095AlphaDummy741 D R S_cls E)))))).fv)
      (i := 0) (j := 1) (by decide))

theorem nb095_fresh_081 (x : Var) (u : Var) (D : Class) (R : Class) (S_cls : Class)
    (f : Var) (E : Class) :
    (nb095AlphaDummy745 x u D R S_cls f E) ∉
      (((Class.cab (nb095AlphaDummy742 x u D R S_cls f E) (Wff.classEq
            (Class.cab (nb095AlphaDummy740 x u D R S_cls f E)
              (synWbr (Class.cv (nb095AlphaDummy006 x u D R S_cls f E)) (Class.cv f)
                (Class.cv (nb095AlphaDummy740 x u D R S_cls f E))))
            (synCsn (Class.cv (nb095AlphaDummy742 x u D R S_cls f E)))))).fv) :=
  by
  simpa only [nb095AlphaDummy745] using
    freshVar_not_mem
      (((Class.cab (nb095AlphaDummy742 x u D R S_cls f E) (Wff.classEq
            (Class.cab (nb095AlphaDummy740 x u D R S_cls f E)
              (synWbr (Class.cv (nb095AlphaDummy006 x u D R S_cls f E)) (Class.cv f)
                (Class.cv (nb095AlphaDummy740 x u D R S_cls f E))))
            (synCsn (Class.cv (nb095AlphaDummy742 x u D R S_cls f E)))))).fv)
      0

theorem nb095_fresh_082 (x : Var) (u : Var) (D : Class) (R : Class) (S_cls : Class)
    (f : Var) (E : Class) :
    (nb095AlphaDummy746 x u D R S_cls f E) ∉
      (((Class.cab (nb095AlphaDummy742 x u D R S_cls f E) (Wff.classEq
            (Class.cab (nb095AlphaDummy740 x u D R S_cls f E)
              (synWbr (Class.cv (nb095AlphaDummy006 x u D R S_cls f E)) (Class.cv f)
                (Class.cv (nb095AlphaDummy740 x u D R S_cls f E))))
            (synCsn (Class.cv (nb095AlphaDummy742 x u D R S_cls f E)))))).fv) :=
  by
  simpa only [nb095AlphaDummy746] using
    freshVar_not_mem
      (((Class.cab (nb095AlphaDummy742 x u D R S_cls f E) (Wff.classEq
            (Class.cab (nb095AlphaDummy740 x u D R S_cls f E)
              (synWbr (Class.cv (nb095AlphaDummy006 x u D R S_cls f E)) (Class.cv f)
                (Class.cv (nb095AlphaDummy740 x u D R S_cls f E))))
            (synCsn (Class.cv (nb095AlphaDummy742 x u D R S_cls f E)))))).fv)
      1

theorem nb095_distinct_083 (x : Var) (u : Var) (D : Class) (R : Class) (S_cls : Class)
    (f : Var) (E : Class) :
    (nb095AlphaDummy745 x u D R S_cls f E) ≠
      (nb095AlphaDummy746 x u D R S_cls f E) :=
  by
  simpa only [nb095AlphaDummy745, nb095AlphaDummy746] using
    (freshVar_injective (((Class.cab (nb095AlphaDummy742 x u D R S_cls f E) (Wff.classEq
            (Class.cab (nb095AlphaDummy740 x u D R S_cls f E)
              (synWbr (Class.cv (nb095AlphaDummy006 x u D R S_cls f E)) (Class.cv f)
                (Class.cv (nb095AlphaDummy740 x u D R S_cls f E))))
            (synCsn (Class.cv (nb095AlphaDummy742 x u D R S_cls f E)))))).fv)
      (i := 0) (j := 1) (by decide))

theorem nb095_fresh_084 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095AlphaDummy753 D R S_cls E) ∉
      (((Class.cab (nb095AlphaDummy747 D R S_cls E)
            (synWrex (nb095AlphaDummy748 D R S_cls E)
              (Class.cv (nb095AlphaDummy004 D R S_cls E))
              (Wff.classEq (Class.cv (nb095AlphaDummy747 D R S_cls E))
                (synCphi (Class.cv (nb095AlphaDummy748 D R S_cls E))))))).fv ∪
        ((Class.cab (nb095AlphaDummy747 D R S_cls E)
            (synWrex (nb095AlphaDummy748 D R S_cls E)
              (Class.cv (nb095AlphaDummy004 D R S_cls E))
              (Wff.classEq (Class.cv (nb095AlphaDummy747 D R S_cls E))
                (synCphi (Class.cv (nb095AlphaDummy748 D R S_cls E))))))).fv) :=
  by
  simpa only [nb095AlphaDummy753] using
    freshVar_not_mem
      (((Class.cab (nb095AlphaDummy747 D R S_cls E)
            (synWrex (nb095AlphaDummy748 D R S_cls E)
              (Class.cv (nb095AlphaDummy004 D R S_cls E))
              (Wff.classEq (Class.cv (nb095AlphaDummy747 D R S_cls E))
                (synCphi (Class.cv (nb095AlphaDummy748 D R S_cls E))))))).fv ∪
        ((Class.cab (nb095AlphaDummy747 D R S_cls E)
            (synWrex (nb095AlphaDummy748 D R S_cls E)
              (Class.cv (nb095AlphaDummy004 D R S_cls E))
              (Wff.classEq (Class.cv (nb095AlphaDummy747 D R S_cls E))
                (synCphi (Class.cv (nb095AlphaDummy748 D R S_cls E))))))).fv)
      0

theorem nb095_fresh_085 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095AlphaDummy777 D R S_cls E) ∉
      (((Class.cab (nb095AlphaDummy747 D R S_cls E)
            (synWrex (nb095AlphaDummy748 D R S_cls E)
              (Class.cv (nb095AlphaDummy739 D R S_cls E))
              (Wff.classEq (Class.cv (nb095AlphaDummy747 D R S_cls E))
                (synCun (synCphi (Class.cv (nb095AlphaDummy748 D R S_cls E)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb095AlphaDummy747 D R S_cls E)
            (synWrex (nb095AlphaDummy748 D R S_cls E)
              (Class.cv (nb095AlphaDummy739 D R S_cls E))
              (Wff.classEq (Class.cv (nb095AlphaDummy747 D R S_cls E))
                (synCun (synCphi (Class.cv (nb095AlphaDummy748 D R S_cls E)))
                  (synCsn (synC0c))))))).fv) :=
  by
  simpa only [nb095AlphaDummy777] using
    freshVar_not_mem
      (((Class.cab (nb095AlphaDummy747 D R S_cls E)
            (synWrex (nb095AlphaDummy748 D R S_cls E)
              (Class.cv (nb095AlphaDummy739 D R S_cls E))
              (Wff.classEq (Class.cv (nb095AlphaDummy747 D R S_cls E))
                (synCun (synCphi (Class.cv (nb095AlphaDummy748 D R S_cls E)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb095AlphaDummy747 D R S_cls E)
            (synWrex (nb095AlphaDummy748 D R S_cls E)
              (Class.cv (nb095AlphaDummy739 D R S_cls E))
              (Wff.classEq (Class.cv (nb095AlphaDummy747 D R S_cls E))
                (synCun (synCphi (Class.cv (nb095AlphaDummy748 D R S_cls E)))
                  (synCsn (synC0c))))))).fv)
      0

theorem nb095_fresh_086 (x : Var) (u : Var) (D : Class) (R : Class) (S_cls : Class)
    (f : Var) (E : Class) :
    (nb095AlphaDummy754 x u D R S_cls f E) ∉
      (((Class.cab (nb095AlphaDummy749 x u D R S_cls f E)
            (synWrex (nb095AlphaDummy750 x u D R S_cls f E)
              (Class.cv (nb095AlphaDummy006 x u D R S_cls f E))
              (Wff.classEq (Class.cv (nb095AlphaDummy749 x u D R S_cls f E))
                (synCphi (Class.cv (nb095AlphaDummy750 x u D R S_cls f E))))))).fv ∪
        ((Class.cab (nb095AlphaDummy749 x u D R S_cls f E)
            (synWrex (nb095AlphaDummy750 x u D R S_cls f E)
              (Class.cv (nb095AlphaDummy006 x u D R S_cls f E))
              (Wff.classEq (Class.cv (nb095AlphaDummy749 x u D R S_cls f E))
                (synCphi (Class.cv (nb095AlphaDummy750 x u D R S_cls f E))))))).fv) :=
  by
  simpa only [nb095AlphaDummy754] using
    freshVar_not_mem
      (((Class.cab (nb095AlphaDummy749 x u D R S_cls f E)
            (synWrex (nb095AlphaDummy750 x u D R S_cls f E)
              (Class.cv (nb095AlphaDummy006 x u D R S_cls f E))
              (Wff.classEq (Class.cv (nb095AlphaDummy749 x u D R S_cls f E))
                (synCphi (Class.cv (nb095AlphaDummy750 x u D R S_cls f E))))))).fv ∪
        ((Class.cab (nb095AlphaDummy749 x u D R S_cls f E)
            (synWrex (nb095AlphaDummy750 x u D R S_cls f E)
              (Class.cv (nb095AlphaDummy006 x u D R S_cls f E))
              (Wff.classEq (Class.cv (nb095AlphaDummy749 x u D R S_cls f E))
                (synCphi (Class.cv (nb095AlphaDummy750 x u D R S_cls f E))))))).fv)
      0

theorem nb095_fresh_087 (x : Var) (u : Var) (D : Class) (R : Class) (S_cls : Class)
    (f : Var) (E : Class) :
    (nb095AlphaDummy778 x u D R S_cls f E) ∉
      (((Class.cab (nb095AlphaDummy749 x u D R S_cls f E)
            (synWrex (nb095AlphaDummy750 x u D R S_cls f E)
              (Class.cv (nb095AlphaDummy740 x u D R S_cls f E))
              (Wff.classEq (Class.cv (nb095AlphaDummy749 x u D R S_cls f E))
                (synCun (synCphi (Class.cv (nb095AlphaDummy750 x u D R S_cls f E)))
                  (synCsn (synC0c))))))).fv ∪
        ((Class.cab (nb095AlphaDummy749 x u D R S_cls f E)
            (synWrex (nb095AlphaDummy750 x u D R S_cls f E)
              (Class.cv (nb095AlphaDummy740 x u D R S_cls f E))
              (Wff.classEq (Class.cv (nb095AlphaDummy749 x u D R S_cls f E))
                (synCun (synCphi (Class.cv (nb095AlphaDummy750 x u D R S_cls f E)))
                  (synCsn (synC0c))))))).fv) :=
  by
  simpa only [nb095AlphaDummy778] using
    freshVar_not_mem
      (((Class.cab (nb095AlphaDummy749 x u D R S_cls f E)
            (synWrex (nb095AlphaDummy750 x u D R S_cls f E)
              (Class.cv (nb095AlphaDummy740 x u D R S_cls f E))
              (Wff.classEq (Class.cv (nb095AlphaDummy749 x u D R S_cls f E))
                (synCun (synCphi (Class.cv (nb095AlphaDummy750 x u D R S_cls f E)))
                  (synCsn (synC0c))))))).fv ∪
        ((Class.cab (nb095AlphaDummy749 x u D R S_cls f E)
            (synWrex (nb095AlphaDummy750 x u D R S_cls f E)
              (Class.cv (nb095AlphaDummy740 x u D R S_cls f E))
              (Wff.classEq (Class.cv (nb095AlphaDummy749 x u D R S_cls f E))
                (synCun (synCphi (Class.cv (nb095AlphaDummy750 x u D R S_cls f E)))
                  (synCsn (synC0c))))))).fv)
      0

theorem nb095_fresh_088 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095AlphaDummy805 D R S_cls E) ∉
      (((Class.cab (nb095AlphaDummy799 D R S_cls E)
            (synWrex (nb095AlphaDummy800 D R S_cls E)
              (Class.cv (nb095AlphaDummy793 D R S_cls E))
              (Wff.classEq (Class.cv (nb095AlphaDummy799 D R S_cls E))
                (synCphi (Class.cv (nb095AlphaDummy800 D R S_cls E))))))).fv ∪
        ((Class.cab (nb095AlphaDummy799 D R S_cls E)
            (synWrex (nb095AlphaDummy800 D R S_cls E)
              (Class.cv (nb095AlphaDummy793 D R S_cls E))
              (Wff.classEq (Class.cv (nb095AlphaDummy799 D R S_cls E))
                (synCphi (Class.cv (nb095AlphaDummy800 D R S_cls E))))))).fv) :=
  by
  simpa only [nb095AlphaDummy805] using
    freshVar_not_mem
      (((Class.cab (nb095AlphaDummy799 D R S_cls E)
            (synWrex (nb095AlphaDummy800 D R S_cls E)
              (Class.cv (nb095AlphaDummy793 D R S_cls E))
              (Wff.classEq (Class.cv (nb095AlphaDummy799 D R S_cls E))
                (synCphi (Class.cv (nb095AlphaDummy800 D R S_cls E))))))).fv ∪
        ((Class.cab (nb095AlphaDummy799 D R S_cls E)
            (synWrex (nb095AlphaDummy800 D R S_cls E)
              (Class.cv (nb095AlphaDummy793 D R S_cls E))
              (Wff.classEq (Class.cv (nb095AlphaDummy799 D R S_cls E))
                (synCphi (Class.cv (nb095AlphaDummy800 D R S_cls E))))))).fv)
      0

theorem nb095_fresh_089 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095AlphaDummy829 D R S_cls E) ∉
      (((Class.cab (nb095AlphaDummy799 D R S_cls E)
            (synWrex (nb095AlphaDummy800 D R S_cls E)
              (Class.cv (nb095AlphaDummy794 D R S_cls E))
              (Wff.classEq (Class.cv (nb095AlphaDummy799 D R S_cls E))
                (synCun (synCphi (Class.cv (nb095AlphaDummy800 D R S_cls E)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb095AlphaDummy799 D R S_cls E)
            (synWrex (nb095AlphaDummy800 D R S_cls E)
              (Class.cv (nb095AlphaDummy794 D R S_cls E))
              (Wff.classEq (Class.cv (nb095AlphaDummy799 D R S_cls E))
                (synCun (synCphi (Class.cv (nb095AlphaDummy800 D R S_cls E)))
                  (synCsn (synC0c))))))).fv) :=
  by
  simpa only [nb095AlphaDummy829] using
    freshVar_not_mem
      (((Class.cab (nb095AlphaDummy799 D R S_cls E)
            (synWrex (nb095AlphaDummy800 D R S_cls E)
              (Class.cv (nb095AlphaDummy794 D R S_cls E))
              (Wff.classEq (Class.cv (nb095AlphaDummy799 D R S_cls E))
                (synCun (synCphi (Class.cv (nb095AlphaDummy800 D R S_cls E)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb095AlphaDummy799 D R S_cls E)
            (synWrex (nb095AlphaDummy800 D R S_cls E)
              (Class.cv (nb095AlphaDummy794 D R S_cls E))
              (Wff.classEq (Class.cv (nb095AlphaDummy799 D R S_cls E))
                (synCun (synCphi (Class.cv (nb095AlphaDummy800 D R S_cls E)))
                  (synCsn (synC0c))))))).fv)
      0

theorem nb095_fresh_090 (u : Var) (S_cls : Class) (E : Class) :
    (nb095AlphaDummy806 u S_cls E) ∉
      (((Class.cab (nb095AlphaDummy801 u S_cls E) (synWrex (nb095AlphaDummy802 u S_cls E)
              (Class.cv (nb095AlphaDummy795 u S_cls E))
              (Wff.classEq (Class.cv (nb095AlphaDummy801 u S_cls E))
                (synCphi (Class.cv (nb095AlphaDummy802 u S_cls E))))))).fv ∪
        ((Class.cab (nb095AlphaDummy801 u S_cls E)
            (synWrex (nb095AlphaDummy802 u S_cls E)
              (Class.cv (nb095AlphaDummy795 u S_cls E))
              (Wff.classEq (Class.cv (nb095AlphaDummy801 u S_cls E))
                (synCphi (Class.cv (nb095AlphaDummy802 u S_cls E))))))).fv) :=
  by
  simpa only [nb095AlphaDummy806] using
    freshVar_not_mem
      (((Class.cab (nb095AlphaDummy801 u S_cls E) (synWrex (nb095AlphaDummy802 u S_cls E)
              (Class.cv (nb095AlphaDummy795 u S_cls E))
              (Wff.classEq (Class.cv (nb095AlphaDummy801 u S_cls E))
                (synCphi (Class.cv (nb095AlphaDummy802 u S_cls E))))))).fv ∪
        ((Class.cab (nb095AlphaDummy801 u S_cls E)
            (synWrex (nb095AlphaDummy802 u S_cls E)
              (Class.cv (nb095AlphaDummy795 u S_cls E))
              (Wff.classEq (Class.cv (nb095AlphaDummy801 u S_cls E))
                (synCphi (Class.cv (nb095AlphaDummy802 u S_cls E))))))).fv)
      0

theorem nb095_fresh_091 (u : Var) (S_cls : Class) (E : Class) :
    (nb095AlphaDummy830 u S_cls E) ∉
      (((Class.cab (nb095AlphaDummy801 u S_cls E) (synWrex (nb095AlphaDummy802 u S_cls E)
              (Class.cv (nb095AlphaDummy796 u S_cls E))
              (Wff.classEq (Class.cv (nb095AlphaDummy801 u S_cls E))
                (synCun (synCphi (Class.cv (nb095AlphaDummy802 u S_cls E)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb095AlphaDummy801 u S_cls E)
            (synWrex (nb095AlphaDummy802 u S_cls E)
              (Class.cv (nb095AlphaDummy796 u S_cls E))
              (Wff.classEq (Class.cv (nb095AlphaDummy801 u S_cls E))
                (synCun (synCphi (Class.cv (nb095AlphaDummy802 u S_cls E)))
                  (synCsn (synC0c))))))).fv) :=
  by
  simpa only [nb095AlphaDummy830] using
    freshVar_not_mem
      (((Class.cab (nb095AlphaDummy801 u S_cls E) (synWrex (nb095AlphaDummy802 u S_cls E)
              (Class.cv (nb095AlphaDummy796 u S_cls E))
              (Wff.classEq (Class.cv (nb095AlphaDummy801 u S_cls E))
                (synCun (synCphi (Class.cv (nb095AlphaDummy802 u S_cls E)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb095AlphaDummy801 u S_cls E)
            (synWrex (nb095AlphaDummy802 u S_cls E)
              (Class.cv (nb095AlphaDummy796 u S_cls E))
              (Wff.classEq (Class.cv (nb095AlphaDummy801 u S_cls E))
                (synCun (synCphi (Class.cv (nb095AlphaDummy802 u S_cls E)))
                  (synCsn (synC0c))))))).fv)
      0

theorem nb095_fresh_092 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095AlphaDummy091 D R S_cls E) ∉
      (((Class.cv (nb095AlphaDummy000 D R S_cls E))).fv) :=
  by
  simpa only [nb095AlphaDummy091] using
    freshVar_not_mem (((Class.cv (nb095AlphaDummy000 D R S_cls E))).fv) 0

theorem nb095_fresh_093 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095AlphaDummy092 D R S_cls E) ∉
      (((Class.cv (nb095AlphaDummy000 D R S_cls E))).fv) :=
  by
  simpa only [nb095AlphaDummy092] using
    freshVar_not_mem (((Class.cv (nb095AlphaDummy000 D R S_cls E))).fv) 1

theorem nb095_distinct_094 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095AlphaDummy091 D R S_cls E) ≠ (nb095AlphaDummy092 D R S_cls E) := by
  simpa only [nb095AlphaDummy091, nb095AlphaDummy092] using
    (freshVar_injective (((Class.cv (nb095AlphaDummy000 D R S_cls E))).fv) (i := 0)
      (j := 1) (by decide))

theorem nb095_fresh_095 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095AlphaDummy669 D R S_cls E) ∉
      (((Class.cv (nb095AlphaDummy000 D R S_cls E))).fv ∪
        ((Class.cv (nb095AlphaDummy003 D R S_cls E))).fv) :=
  by
  simpa only [nb095AlphaDummy669] using
    freshVar_not_mem
      (((Class.cv (nb095AlphaDummy000 D R S_cls E))).fv ∪
        ((Class.cv (nb095AlphaDummy003 D R S_cls E))).fv)
      0

theorem nb095_fresh_096 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095AlphaDummy739 D R S_cls E) ∉
      (((Class.cv (nb095AlphaDummy000 D R S_cls E))).fv ∪
        ((Class.cv (nb095AlphaDummy004 D R S_cls E))).fv) :=
  by
  simpa only [nb095AlphaDummy739] using
    freshVar_not_mem
      (((Class.cv (nb095AlphaDummy000 D R S_cls E))).fv ∪
        ((Class.cv (nb095AlphaDummy004 D R S_cls E))).fv)
      0

theorem nb095_fresh_097 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095AlphaDummy011 D R S_cls E) ∉
      (((Class.cv (nb095AlphaDummy000 D R S_cls E))).fv ∪
        ((synCcnv (Class.cv (nb095AlphaDummy000 D R S_cls E)))).fv) :=
  by
  simpa only [nb095AlphaDummy011] using
    freshVar_not_mem
      (((Class.cv (nb095AlphaDummy000 D R S_cls E))).fv ∪
        ((synCcnv (Class.cv (nb095AlphaDummy000 D R S_cls E)))).fv)
      0

theorem nb095_fresh_098 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095AlphaDummy012 D R S_cls E) ∉
      (((Class.cv (nb095AlphaDummy000 D R S_cls E))).fv ∪
        ((synCcnv (Class.cv (nb095AlphaDummy000 D R S_cls E)))).fv) :=
  by
  simpa only [nb095AlphaDummy012] using
    freshVar_not_mem
      (((Class.cv (nb095AlphaDummy000 D R S_cls E))).fv ∪
        ((synCcnv (Class.cv (nb095AlphaDummy000 D R S_cls E)))).fv)
      1

theorem nb095_fresh_099 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095AlphaDummy013 D R S_cls E) ∉
      (((Class.cv (nb095AlphaDummy000 D R S_cls E))).fv ∪
        ((synCcnv (Class.cv (nb095AlphaDummy000 D R S_cls E)))).fv) :=
  by
  simpa only [nb095AlphaDummy013] using
    freshVar_not_mem
      (((Class.cv (nb095AlphaDummy000 D R S_cls E))).fv ∪
        ((synCcnv (Class.cv (nb095AlphaDummy000 D R S_cls E)))).fv)
      2

theorem nb095_distinct_100 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095AlphaDummy011 D R S_cls E) ≠ (nb095AlphaDummy012 D R S_cls E) := by
  simpa only [nb095AlphaDummy011, nb095AlphaDummy012] using
    (freshVar_injective (((Class.cv (nb095AlphaDummy000 D R S_cls E))).fv ∪
        ((synCcnv (Class.cv (nb095AlphaDummy000 D R S_cls E)))).fv)
      (i := 0) (j := 1) (by decide))

theorem nb095_distinct_101 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095AlphaDummy011 D R S_cls E) ≠ (nb095AlphaDummy013 D R S_cls E) := by
  simpa only [nb095AlphaDummy011, nb095AlphaDummy013] using
    (freshVar_injective (((Class.cv (nb095AlphaDummy000 D R S_cls E))).fv ∪
        ((synCcnv (Class.cv (nb095AlphaDummy000 D R S_cls E)))).fv)
      (i := 0) (j := 2) (by decide))

theorem nb095_distinct_102 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095AlphaDummy012 D R S_cls E) ≠ (nb095AlphaDummy013 D R S_cls E) := by
  simpa only [nb095AlphaDummy012, nb095AlphaDummy013] using
    (freshVar_injective (((Class.cv (nb095AlphaDummy000 D R S_cls E))).fv ∪
        ((synCcnv (Class.cv (nb095AlphaDummy000 D R S_cls E)))).fv)
      (i := 1) (j := 2) (by decide))

theorem nb095_fresh_103 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095AlphaDummy003 D R S_cls E) ∉
      (((Class.cv (nb095AlphaDummy000 D R S_cls E))).fv ∪ ((synCin R (synCxp (synCin D
                      (synCima (synCcnv (synCdif R (synCid)))
                        (synCsn (Class.cv (nb095AlphaDummy002 D R S_cls E))))) (synCin D
                      (synCima (synCcnv (synCdif R (synCid)))
                        (synCsn (Class.cv (nb095AlphaDummy002 D R S_cls E)))))))).fv ∪
            ((synCin S_cls (synCxp (synCin E (synCima (synCcnv (synCdif S_cls (synCid)))
                      (synCsn (Class.cv (nb095AlphaDummy001 D R S_cls E))))) (synCin E
                    (synCima (synCcnv (synCdif S_cls (synCid)))
                      (synCsn (Class.cv (nb095AlphaDummy001 D R S_cls E)))))))).fv ∪
          ((synCin D (synCima (synCcnv (synCdif R (synCid)))
                (synCsn (Class.cv (nb095AlphaDummy002 D R S_cls E)))))).fv ∪ ((synCin E
            (synCima (synCcnv (synCdif S_cls (synCid)))
              (synCsn (Class.cv (nb095AlphaDummy001 D R S_cls E)))))).fv) :=
  by
  simpa only [nb095AlphaDummy003] using
    freshVar_not_mem
      (((Class.cv (nb095AlphaDummy000 D R S_cls E))).fv ∪ ((synCin R (synCxp (synCin D
                      (synCima (synCcnv (synCdif R (synCid)))
                        (synCsn (Class.cv (nb095AlphaDummy002 D R S_cls E))))) (synCin D
                      (synCima (synCcnv (synCdif R (synCid)))
                        (synCsn (Class.cv (nb095AlphaDummy002 D R S_cls E)))))))).fv ∪
            ((synCin S_cls (synCxp (synCin E (synCima (synCcnv (synCdif S_cls (synCid)))
                      (synCsn (Class.cv (nb095AlphaDummy001 D R S_cls E))))) (synCin E
                    (synCima (synCcnv (synCdif S_cls (synCid)))
                      (synCsn (Class.cv (nb095AlphaDummy001 D R S_cls E)))))))).fv ∪
          ((synCin D (synCima (synCcnv (synCdif R (synCid)))
                (synCsn (Class.cv (nb095AlphaDummy002 D R S_cls E)))))).fv ∪ ((synCin E
            (synCima (synCcnv (synCdif S_cls (synCid)))
              (synCsn (Class.cv (nb095AlphaDummy001 D R S_cls E)))))).fv)
      0

theorem nb095_fresh_104 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095AlphaDummy004 D R S_cls E) ∉
      (((Class.cv (nb095AlphaDummy000 D R S_cls E))).fv ∪ ((synCin R (synCxp (synCin D
                      (synCima (synCcnv (synCdif R (synCid)))
                        (synCsn (Class.cv (nb095AlphaDummy002 D R S_cls E))))) (synCin D
                      (synCima (synCcnv (synCdif R (synCid)))
                        (synCsn (Class.cv (nb095AlphaDummy002 D R S_cls E)))))))).fv ∪
            ((synCin S_cls (synCxp (synCin E (synCima (synCcnv (synCdif S_cls (synCid)))
                      (synCsn (Class.cv (nb095AlphaDummy001 D R S_cls E))))) (synCin E
                    (synCima (synCcnv (synCdif S_cls (synCid)))
                      (synCsn (Class.cv (nb095AlphaDummy001 D R S_cls E)))))))).fv ∪
          ((synCin D (synCima (synCcnv (synCdif R (synCid)))
                (synCsn (Class.cv (nb095AlphaDummy002 D R S_cls E)))))).fv ∪ ((synCin E
            (synCima (synCcnv (synCdif S_cls (synCid)))
              (synCsn (Class.cv (nb095AlphaDummy001 D R S_cls E)))))).fv) :=
  by
  simpa only [nb095AlphaDummy004] using
    freshVar_not_mem
      (((Class.cv (nb095AlphaDummy000 D R S_cls E))).fv ∪ ((synCin R (synCxp (synCin D
                      (synCima (synCcnv (synCdif R (synCid)))
                        (synCsn (Class.cv (nb095AlphaDummy002 D R S_cls E))))) (synCin D
                      (synCima (synCcnv (synCdif R (synCid)))
                        (synCsn (Class.cv (nb095AlphaDummy002 D R S_cls E)))))))).fv ∪
            ((synCin S_cls (synCxp (synCin E (synCima (synCcnv (synCdif S_cls (synCid)))
                      (synCsn (Class.cv (nb095AlphaDummy001 D R S_cls E))))) (synCin E
                    (synCima (synCcnv (synCdif S_cls (synCid)))
                      (synCsn (Class.cv (nb095AlphaDummy001 D R S_cls E)))))))).fv ∪
          ((synCin D (synCima (synCcnv (synCdif R (synCid)))
                (synCsn (Class.cv (nb095AlphaDummy002 D R S_cls E)))))).fv ∪ ((synCin E
            (synCima (synCcnv (synCdif S_cls (synCid)))
              (synCsn (Class.cv (nb095AlphaDummy001 D R S_cls E)))))).fv)
      1

theorem nb095_distinct_105 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095AlphaDummy003 D R S_cls E) ≠ (nb095AlphaDummy004 D R S_cls E) := by
  simpa only [nb095AlphaDummy003, nb095AlphaDummy004] using
    (freshVar_injective (((Class.cv (nb095AlphaDummy000 D R S_cls E))).fv ∪ ((synCin R
                  (synCxp (synCin D (synCima (synCcnv (synCdif R (synCid)))
                        (synCsn (Class.cv (nb095AlphaDummy002 D R S_cls E))))) (synCin D
                      (synCima (synCcnv (synCdif R (synCid)))
                        (synCsn (Class.cv (nb095AlphaDummy002 D R S_cls E)))))))).fv ∪
            ((synCin S_cls (synCxp (synCin E (synCima (synCcnv (synCdif S_cls (synCid)))
                      (synCsn (Class.cv (nb095AlphaDummy001 D R S_cls E))))) (synCin E
                    (synCima (synCcnv (synCdif S_cls (synCid)))
                      (synCsn (Class.cv (nb095AlphaDummy001 D R S_cls E)))))))).fv ∪
          ((synCin D (synCima (synCcnv (synCdif R (synCid)))
                (synCsn (Class.cv (nb095AlphaDummy002 D R S_cls E)))))).fv ∪ ((synCin E
            (synCima (synCcnv (synCdif S_cls (synCid)))
              (synCsn (Class.cv (nb095AlphaDummy001 D R S_cls E)))))).fv)
      (i := 0) (j := 1) (by decide))

theorem nb095_fresh_106 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095AlphaDummy295 D R S_cls E) ∉
      (((Class.cv (nb095AlphaDummy000 D R S_cls E))).fv ∪ ((synCvv)).fv) :=
  by
  simpa only [nb095AlphaDummy295] using
    freshVar_not_mem
      (((Class.cv (nb095AlphaDummy000 D R S_cls E))).fv ∪ ((synCvv)).fv) 0

theorem nb095_fresh_107 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095AlphaDummy296 D R S_cls E) ∉
      (((Class.cv (nb095AlphaDummy000 D R S_cls E))).fv ∪ ((synCvv)).fv) :=
  by
  simpa only [nb095AlphaDummy296] using
    freshVar_not_mem
      (((Class.cv (nb095AlphaDummy000 D R S_cls E))).fv ∪ ((synCvv)).fv) 1

theorem nb095_distinct_108 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095AlphaDummy295 D R S_cls E) ≠ (nb095AlphaDummy296 D R S_cls E) := by
  simpa only [nb095AlphaDummy295, nb095AlphaDummy296] using
    (freshVar_injective
      (((Class.cv (nb095AlphaDummy000 D R S_cls E))).fv ∪ ((synCvv)).fv) (i := 0)
      (j := 1) (by decide))

theorem nb095_fresh_109 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095AlphaDummy343 D R S_cls E) ∉
      (((Class.cv (nb095AlphaDummy001 D R S_cls E))).fv) :=
  by
  simpa only [nb095AlphaDummy343] using
    freshVar_not_mem (((Class.cv (nb095AlphaDummy001 D R S_cls E))).fv) 0

theorem nb095_fresh_110 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095AlphaDummy253 D R S_cls E) ∉
      (((Class.cv (nb095AlphaDummy002 D R S_cls E))).fv) :=
  by
  simpa only [nb095AlphaDummy253] using
    freshVar_not_mem (((Class.cv (nb095AlphaDummy002 D R S_cls E))).fv) 0

theorem nb095_fresh_111 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095AlphaDummy579 D R S_cls E) ∉
      (((Class.cv (nb095AlphaDummy003 D R S_cls E))).fv ∪
        ((Class.cv (nb095AlphaDummy004 D R S_cls E))).fv) :=
  by
  simpa only [nb095AlphaDummy579] using
    freshVar_not_mem
      (((Class.cv (nb095AlphaDummy003 D R S_cls E))).fv ∪
        ((Class.cv (nb095AlphaDummy004 D R S_cls E))).fv)
      0

theorem nb095_fresh_112 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095AlphaDummy580 D R S_cls E) ∉
      (((Class.cv (nb095AlphaDummy003 D R S_cls E))).fv ∪
        ((Class.cv (nb095AlphaDummy004 D R S_cls E))).fv) :=
  by
  simpa only [nb095AlphaDummy580] using
    freshVar_not_mem
      (((Class.cv (nb095AlphaDummy003 D R S_cls E))).fv ∪
        ((Class.cv (nb095AlphaDummy004 D R S_cls E))).fv)
      1

theorem nb095_distinct_113 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095AlphaDummy579 D R S_cls E) ≠ (nb095AlphaDummy580 D R S_cls E) := by
  simpa only [nb095AlphaDummy579, nb095AlphaDummy580] using
    (freshVar_injective (((Class.cv (nb095AlphaDummy003 D R S_cls E))).fv ∪
        ((Class.cv (nb095AlphaDummy004 D R S_cls E))).fv) (i := 0) (j := 1) (by decide))

theorem nb095_fresh_114 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095AlphaDummy677 D R S_cls E) ∉
      (((Class.cv (nb095AlphaDummy003 D R S_cls E))).fv ∪
        ((Class.cv (nb095AlphaDummy669 D R S_cls E))).fv) :=
  by
  simpa only [nb095AlphaDummy677] using
    freshVar_not_mem
      (((Class.cv (nb095AlphaDummy003 D R S_cls E))).fv ∪
        ((Class.cv (nb095AlphaDummy669 D R S_cls E))).fv)
      0

theorem nb095_fresh_115 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095AlphaDummy678 D R S_cls E) ∉
      (((Class.cv (nb095AlphaDummy003 D R S_cls E))).fv ∪
        ((Class.cv (nb095AlphaDummy669 D R S_cls E))).fv) :=
  by
  simpa only [nb095AlphaDummy678] using
    freshVar_not_mem
      (((Class.cv (nb095AlphaDummy003 D R S_cls E))).fv ∪
        ((Class.cv (nb095AlphaDummy669 D R S_cls E))).fv)
      1

theorem nb095_distinct_116 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095AlphaDummy677 D R S_cls E) ≠ (nb095AlphaDummy678 D R S_cls E) := by
  simpa only [nb095AlphaDummy677, nb095AlphaDummy678] using
    (freshVar_injective (((Class.cv (nb095AlphaDummy003 D R S_cls E))).fv ∪
        ((Class.cv (nb095AlphaDummy669 D R S_cls E))).fv) (i := 0) (j := 1) (by decide))

theorem nb095_fresh_117 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095AlphaDummy747 D R S_cls E) ∉
      (((Class.cv (nb095AlphaDummy004 D R S_cls E))).fv ∪
        ((Class.cv (nb095AlphaDummy739 D R S_cls E))).fv) :=
  by
  simpa only [nb095AlphaDummy747] using
    freshVar_not_mem
      (((Class.cv (nb095AlphaDummy004 D R S_cls E))).fv ∪
        ((Class.cv (nb095AlphaDummy739 D R S_cls E))).fv)
      0

theorem nb095_fresh_118 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095AlphaDummy748 D R S_cls E) ∉
      (((Class.cv (nb095AlphaDummy004 D R S_cls E))).fv ∪
        ((Class.cv (nb095AlphaDummy739 D R S_cls E))).fv) :=
  by
  simpa only [nb095AlphaDummy748] using
    freshVar_not_mem
      (((Class.cv (nb095AlphaDummy004 D R S_cls E))).fv ∪
        ((Class.cv (nb095AlphaDummy739 D R S_cls E))).fv)
      1

theorem nb095_distinct_119 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095AlphaDummy747 D R S_cls E) ≠ (nb095AlphaDummy748 D R S_cls E) := by
  simpa only [nb095AlphaDummy747, nb095AlphaDummy748] using
    (freshVar_injective (((Class.cv (nb095AlphaDummy004 D R S_cls E))).fv ∪
        ((Class.cv (nb095AlphaDummy739 D R S_cls E))).fv) (i := 0) (j := 1) (by decide))

theorem nb095_fresh_120 (x : Var) (u : Var) (D : Class) (R : Class) (S_cls : Class)
    (f : Var) (E : Class) :
    (nb095AlphaDummy581 x u D R S_cls f E) ∉
      (((Class.cv (nb095AlphaDummy005 x u D R S_cls f E))).fv ∪
        ((Class.cv (nb095AlphaDummy006 x u D R S_cls f E))).fv) :=
  by
  simpa only [nb095AlphaDummy581] using
    freshVar_not_mem
      (((Class.cv (nb095AlphaDummy005 x u D R S_cls f E))).fv ∪
        ((Class.cv (nb095AlphaDummy006 x u D R S_cls f E))).fv)
      0

theorem nb095_fresh_121 (x : Var) (u : Var) (D : Class) (R : Class) (S_cls : Class)
    (f : Var) (E : Class) :
    (nb095AlphaDummy582 x u D R S_cls f E) ∉
      (((Class.cv (nb095AlphaDummy005 x u D R S_cls f E))).fv ∪
        ((Class.cv (nb095AlphaDummy006 x u D R S_cls f E))).fv) :=
  by
  simpa only [nb095AlphaDummy582] using
    freshVar_not_mem
      (((Class.cv (nb095AlphaDummy005 x u D R S_cls f E))).fv ∪
        ((Class.cv (nb095AlphaDummy006 x u D R S_cls f E))).fv)
      1

theorem nb095_distinct_122 (x : Var) (u : Var) (D : Class) (R : Class) (S_cls : Class)
    (f : Var) (E : Class) :
    (nb095AlphaDummy581 x u D R S_cls f E) ≠
      (nb095AlphaDummy582 x u D R S_cls f E) :=
  by
  simpa only [nb095AlphaDummy581, nb095AlphaDummy582] using
    (freshVar_injective (((Class.cv (nb095AlphaDummy005 x u D R S_cls f E))).fv ∪
        ((Class.cv (nb095AlphaDummy006 x u D R S_cls f E))).fv)
      (i := 0) (j := 1) (by decide))

theorem nb095_fresh_123 (x : Var) (u : Var) (D : Class) (R : Class) (S_cls : Class)
    (f : Var) (E : Class) :
    (nb095AlphaDummy679 x u D R S_cls f E) ∉
      (((Class.cv (nb095AlphaDummy005 x u D R S_cls f E))).fv ∪
        ((Class.cv (nb095AlphaDummy670 x u D R S_cls f E))).fv) :=
  by
  simpa only [nb095AlphaDummy679] using
    freshVar_not_mem
      (((Class.cv (nb095AlphaDummy005 x u D R S_cls f E))).fv ∪
        ((Class.cv (nb095AlphaDummy670 x u D R S_cls f E))).fv)
      0

theorem nb095_fresh_124 (x : Var) (u : Var) (D : Class) (R : Class) (S_cls : Class)
    (f : Var) (E : Class) :
    (nb095AlphaDummy680 x u D R S_cls f E) ∉
      (((Class.cv (nb095AlphaDummy005 x u D R S_cls f E))).fv ∪
        ((Class.cv (nb095AlphaDummy670 x u D R S_cls f E))).fv) :=
  by
  simpa only [nb095AlphaDummy680] using
    freshVar_not_mem
      (((Class.cv (nb095AlphaDummy005 x u D R S_cls f E))).fv ∪
        ((Class.cv (nb095AlphaDummy670 x u D R S_cls f E))).fv)
      1

theorem nb095_distinct_125 (x : Var) (u : Var) (D : Class) (R : Class) (S_cls : Class)
    (f : Var) (E : Class) :
    (nb095AlphaDummy679 x u D R S_cls f E) ≠
      (nb095AlphaDummy680 x u D R S_cls f E) :=
  by
  simpa only [nb095AlphaDummy679, nb095AlphaDummy680] using
    (freshVar_injective (((Class.cv (nb095AlphaDummy005 x u D R S_cls f E))).fv ∪
        ((Class.cv (nb095AlphaDummy670 x u D R S_cls f E))).fv)
      (i := 0) (j := 1) (by decide))

theorem nb095_fresh_126 (x : Var) (u : Var) (D : Class) (R : Class) (S_cls : Class)
    (f : Var) (E : Class) :
    (nb095AlphaDummy749 x u D R S_cls f E) ∉
      (((Class.cv (nb095AlphaDummy006 x u D R S_cls f E))).fv ∪
        ((Class.cv (nb095AlphaDummy740 x u D R S_cls f E))).fv) :=
  by
  simpa only [nb095AlphaDummy749] using
    freshVar_not_mem
      (((Class.cv (nb095AlphaDummy006 x u D R S_cls f E))).fv ∪
        ((Class.cv (nb095AlphaDummy740 x u D R S_cls f E))).fv)
      0

theorem nb095_fresh_127 (x : Var) (u : Var) (D : Class) (R : Class) (S_cls : Class)
    (f : Var) (E : Class) :
    (nb095AlphaDummy750 x u D R S_cls f E) ∉
      (((Class.cv (nb095AlphaDummy006 x u D R S_cls f E))).fv ∪
        ((Class.cv (nb095AlphaDummy740 x u D R S_cls f E))).fv) :=
  by
  simpa only [nb095AlphaDummy750] using
    freshVar_not_mem
      (((Class.cv (nb095AlphaDummy006 x u D R S_cls f E))).fv ∪
        ((Class.cv (nb095AlphaDummy740 x u D R S_cls f E))).fv)
      1

theorem nb095_distinct_128 (x : Var) (u : Var) (D : Class) (R : Class) (S_cls : Class)
    (f : Var) (E : Class) :
    (nb095AlphaDummy749 x u D R S_cls f E) ≠
      (nb095AlphaDummy750 x u D R S_cls f E) :=
  by
  simpa only [nb095AlphaDummy749, nb095AlphaDummy750] using
    (freshVar_injective (((Class.cv (nb095AlphaDummy006 x u D R S_cls f E))).fv ∪
        ((Class.cv (nb095AlphaDummy740 x u D R S_cls f E))).fv)
      (i := 0) (j := 1) (by decide))

theorem nb095_fresh_129 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095AlphaDummy019 D R S_cls E) ∉
      (((Class.cv (nb095AlphaDummy011 D R S_cls E))).fv ∪
        ((Class.cv (nb095AlphaDummy012 D R S_cls E))).fv) :=
  by
  simpa only [nb095AlphaDummy019] using
    freshVar_not_mem
      (((Class.cv (nb095AlphaDummy011 D R S_cls E))).fv ∪
        ((Class.cv (nb095AlphaDummy012 D R S_cls E))).fv)
      0

theorem nb095_fresh_130 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095AlphaDummy020 D R S_cls E) ∉
      (((Class.cv (nb095AlphaDummy011 D R S_cls E))).fv ∪
        ((Class.cv (nb095AlphaDummy012 D R S_cls E))).fv) :=
  by
  simpa only [nb095AlphaDummy020] using
    freshVar_not_mem
      (((Class.cv (nb095AlphaDummy011 D R S_cls E))).fv ∪
        ((Class.cv (nb095AlphaDummy012 D R S_cls E))).fv)
      1

theorem nb095_distinct_131 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095AlphaDummy019 D R S_cls E) ≠ (nb095AlphaDummy020 D R S_cls E) := by
  simpa only [nb095AlphaDummy019, nb095AlphaDummy020] using
    (freshVar_injective (((Class.cv (nb095AlphaDummy011 D R S_cls E))).fv ∪
        ((Class.cv (nb095AlphaDummy012 D R S_cls E))).fv) (i := 0) (j := 1) (by decide))

theorem nb095_fresh_132 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095AlphaDummy055 D R S_cls E) ∉
      (((Class.cv (nb095AlphaDummy011 D R S_cls E))).fv ∪
        ((Class.cv (nb095AlphaDummy013 D R S_cls E))).fv) :=
  by
  simpa only [nb095AlphaDummy055] using
    freshVar_not_mem
      (((Class.cv (nb095AlphaDummy011 D R S_cls E))).fv ∪
        ((Class.cv (nb095AlphaDummy013 D R S_cls E))).fv)
      0

theorem nb095_fresh_133 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095AlphaDummy056 D R S_cls E) ∉
      (((Class.cv (nb095AlphaDummy011 D R S_cls E))).fv ∪
        ((Class.cv (nb095AlphaDummy013 D R S_cls E))).fv) :=
  by
  simpa only [nb095AlphaDummy056] using
    freshVar_not_mem
      (((Class.cv (nb095AlphaDummy011 D R S_cls E))).fv ∪
        ((Class.cv (nb095AlphaDummy013 D R S_cls E))).fv)
      1

theorem nb095_distinct_134 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095AlphaDummy055 D R S_cls E) ≠ (nb095AlphaDummy056 D R S_cls E) := by
  simpa only [nb095AlphaDummy055, nb095AlphaDummy056] using
    (freshVar_injective (((Class.cv (nb095AlphaDummy011 D R S_cls E))).fv ∪
        ((Class.cv (nb095AlphaDummy013 D R S_cls E))).fv) (i := 0) (j := 1) (by decide))

theorem nb095_fresh_135 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095AlphaDummy169 D R S_cls E) ∉
      (((Class.cv (nb095AlphaDummy013 D R S_cls E))).fv ∪
        ((Class.cv (nb095AlphaDummy012 D R S_cls E))).fv) :=
  by
  simpa only [nb095AlphaDummy169] using
    freshVar_not_mem
      (((Class.cv (nb095AlphaDummy013 D R S_cls E))).fv ∪
        ((Class.cv (nb095AlphaDummy012 D R S_cls E))).fv)
      0

theorem nb095_fresh_136 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095AlphaDummy170 D R S_cls E) ∉
      (((Class.cv (nb095AlphaDummy013 D R S_cls E))).fv ∪
        ((Class.cv (nb095AlphaDummy012 D R S_cls E))).fv) :=
  by
  simpa only [nb095AlphaDummy170] using
    freshVar_not_mem
      (((Class.cv (nb095AlphaDummy013 D R S_cls E))).fv ∪
        ((Class.cv (nb095AlphaDummy012 D R S_cls E))).fv)
      1

theorem nb095_distinct_137 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095AlphaDummy169 D R S_cls E) ≠ (nb095AlphaDummy170 D R S_cls E) := by
  simpa only [nb095AlphaDummy169, nb095AlphaDummy170] using
    (freshVar_injective (((Class.cv (nb095AlphaDummy013 D R S_cls E))).fv ∪
        ((Class.cv (nb095AlphaDummy012 D R S_cls E))).fv) (i := 0) (j := 1) (by decide))

theorem nb095_fresh_138 (f : Var) :
    (nb095AlphaDummy021 f) ∉
      (((Class.cv (nb095AlphaDummy014 f))).fv ∪ ((Class.cv (nb095AlphaDummy015 f))).fv) :=
  by
  simpa only [nb095AlphaDummy021] using
    freshVar_not_mem
      (((Class.cv (nb095AlphaDummy014 f))).fv ∪ ((Class.cv (nb095AlphaDummy015 f))).fv)
      0

theorem nb095_fresh_139 (f : Var) :
    (nb095AlphaDummy022 f) ∉
      (((Class.cv (nb095AlphaDummy014 f))).fv ∪ ((Class.cv (nb095AlphaDummy015 f))).fv) :=
  by
  simpa only [nb095AlphaDummy022] using
    freshVar_not_mem
      (((Class.cv (nb095AlphaDummy014 f))).fv ∪ ((Class.cv (nb095AlphaDummy015 f))).fv)
      1

theorem nb095_distinct_140 (f : Var) :
    (nb095AlphaDummy021 f) ≠ (nb095AlphaDummy022 f) := by
  simpa only [nb095AlphaDummy021, nb095AlphaDummy022] using
    (freshVar_injective (((Class.cv (nb095AlphaDummy014 f))).fv ∪
        ((Class.cv (nb095AlphaDummy015 f))).fv) (i := 0) (j := 1) (by decide))

theorem nb095_fresh_141 (f : Var) :
    (nb095AlphaDummy057 f) ∉
      (((Class.cv (nb095AlphaDummy014 f))).fv ∪ ((Class.cv (nb095AlphaDummy016 f))).fv) :=
  by
  simpa only [nb095AlphaDummy057] using
    freshVar_not_mem
      (((Class.cv (nb095AlphaDummy014 f))).fv ∪ ((Class.cv (nb095AlphaDummy016 f))).fv)
      0

theorem nb095_fresh_142 (f : Var) :
    (nb095AlphaDummy058 f) ∉
      (((Class.cv (nb095AlphaDummy014 f))).fv ∪ ((Class.cv (nb095AlphaDummy016 f))).fv) :=
  by
  simpa only [nb095AlphaDummy058] using
    freshVar_not_mem
      (((Class.cv (nb095AlphaDummy014 f))).fv ∪ ((Class.cv (nb095AlphaDummy016 f))).fv)
      1

theorem nb095_distinct_143 (f : Var) :
    (nb095AlphaDummy057 f) ≠ (nb095AlphaDummy058 f) := by
  simpa only [nb095AlphaDummy057, nb095AlphaDummy058] using
    (freshVar_injective (((Class.cv (nb095AlphaDummy014 f))).fv ∪
        ((Class.cv (nb095AlphaDummy016 f))).fv) (i := 0) (j := 1) (by decide))

theorem nb095_fresh_144 (f : Var) :
    (nb095AlphaDummy171 f) ∉
      (((Class.cv (nb095AlphaDummy016 f))).fv ∪ ((Class.cv (nb095AlphaDummy015 f))).fv) :=
  by
  simpa only [nb095AlphaDummy171] using
    freshVar_not_mem
      (((Class.cv (nb095AlphaDummy016 f))).fv ∪ ((Class.cv (nb095AlphaDummy015 f))).fv)
      0

theorem nb095_fresh_145 (f : Var) :
    (nb095AlphaDummy172 f) ∉
      (((Class.cv (nb095AlphaDummy016 f))).fv ∪ ((Class.cv (nb095AlphaDummy015 f))).fv) :=
  by
  simpa only [nb095AlphaDummy172] using
    freshVar_not_mem
      (((Class.cv (nb095AlphaDummy016 f))).fv ∪ ((Class.cv (nb095AlphaDummy015 f))).fv)
      1

theorem nb095_distinct_146 (f : Var) :
    (nb095AlphaDummy171 f) ≠ (nb095AlphaDummy172 f) := by
  simpa only [nb095AlphaDummy171, nb095AlphaDummy172] using
    (freshVar_injective (((Class.cv (nb095AlphaDummy016 f))).fv ∪
        ((Class.cv (nb095AlphaDummy015 f))).fv) (i := 0) (j := 1) (by decide))

theorem nb095_fresh_147 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095AlphaDummy027 D R S_cls E) ∉
      (((Class.cv (nb095AlphaDummy020 D R S_cls E))).fv) :=
  by
  simpa only [nb095AlphaDummy027] using
    freshVar_not_mem (((Class.cv (nb095AlphaDummy020 D R S_cls E))).fv) 0

theorem nb095_fresh_148 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095AlphaDummy028 D R S_cls E) ∉
      (((Class.cv (nb095AlphaDummy020 D R S_cls E))).fv) :=
  by
  simpa only [nb095AlphaDummy028] using
    freshVar_not_mem (((Class.cv (nb095AlphaDummy020 D R S_cls E))).fv) 1

theorem nb095_distinct_149 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095AlphaDummy027 D R S_cls E) ≠ (nb095AlphaDummy028 D R S_cls E) := by
  simpa only [nb095AlphaDummy027, nb095AlphaDummy028] using
    (freshVar_injective (((Class.cv (nb095AlphaDummy020 D R S_cls E))).fv) (i := 0)
      (j := 1) (by decide))

theorem nb095_fresh_150 (f : Var) :
    (nb095AlphaDummy029 f) ∉ (((Class.cv (nb095AlphaDummy022 f))).fv) := by
  simpa only [nb095AlphaDummy029] using
    freshVar_not_mem (((Class.cv (nb095AlphaDummy022 f))).fv) 0

theorem nb095_fresh_151 (f : Var) :
    (nb095AlphaDummy030 f) ∉ (((Class.cv (nb095AlphaDummy022 f))).fv) := by
  simpa only [nb095AlphaDummy030] using
    freshVar_not_mem (((Class.cv (nb095AlphaDummy022 f))).fv) 1

theorem nb095_distinct_152 (f : Var) :
    (nb095AlphaDummy029 f) ≠ (nb095AlphaDummy030 f) := by
  simpa only [nb095AlphaDummy029, nb095AlphaDummy030] using
    (freshVar_injective (((Class.cv (nb095AlphaDummy022 f))).fv) (i := 0) (j := 1)
      (by decide))

theorem nb095_fresh_153 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095AlphaDummy033 D R S_cls E) ∉
      (((Class.cv (nb095AlphaDummy027 D R S_cls E))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb095AlphaDummy033] using
    freshVar_not_mem
      (((Class.cv (nb095AlphaDummy027 D R S_cls E))).fv ∪ ((synC1c)).fv) 0

theorem nb095_fresh_154 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095AlphaDummy034 D R S_cls E) ∉
      (((Class.cv (nb095AlphaDummy027 D R S_cls E))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb095AlphaDummy034] using
    freshVar_not_mem
      (((Class.cv (nb095AlphaDummy027 D R S_cls E))).fv ∪ ((synC1c)).fv) 1

theorem nb095_fresh_155 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095AlphaDummy035 D R S_cls E) ∉
      (((Class.cv (nb095AlphaDummy027 D R S_cls E))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb095AlphaDummy035] using
    freshVar_not_mem
      (((Class.cv (nb095AlphaDummy027 D R S_cls E))).fv ∪ ((synC1c)).fv) 2

theorem nb095_distinct_156 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095AlphaDummy033 D R S_cls E) ≠ (nb095AlphaDummy034 D R S_cls E) := by
  simpa only [nb095AlphaDummy033, nb095AlphaDummy034] using
    (freshVar_injective
      (((Class.cv (nb095AlphaDummy027 D R S_cls E))).fv ∪ ((synC1c)).fv) (i := 0)
      (j := 1) (by decide))

theorem nb095_distinct_157 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095AlphaDummy033 D R S_cls E) ≠ (nb095AlphaDummy035 D R S_cls E) := by
  simpa only [nb095AlphaDummy033, nb095AlphaDummy035] using
    (freshVar_injective
      (((Class.cv (nb095AlphaDummy027 D R S_cls E))).fv ∪ ((synC1c)).fv) (i := 0)
      (j := 2) (by decide))

theorem nb095_distinct_158 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095AlphaDummy034 D R S_cls E) ≠ (nb095AlphaDummy035 D R S_cls E) := by
  simpa only [nb095AlphaDummy034, nb095AlphaDummy035] using
    (freshVar_injective
      (((Class.cv (nb095AlphaDummy027 D R S_cls E))).fv ∪ ((synC1c)).fv) (i := 1)
      (j := 2) (by decide))

theorem nb095_fresh_159 (f : Var) :
    (nb095AlphaDummy036 f) ∉
      (((Class.cv (nb095AlphaDummy029 f))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb095AlphaDummy036] using
    freshVar_not_mem (((Class.cv (nb095AlphaDummy029 f))).fv ∪ ((synC1c)).fv) 0

theorem nb095_fresh_160 (f : Var) :
    (nb095AlphaDummy037 f) ∉
      (((Class.cv (nb095AlphaDummy029 f))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb095AlphaDummy037] using
    freshVar_not_mem (((Class.cv (nb095AlphaDummy029 f))).fv ∪ ((synC1c)).fv) 1

theorem nb095_fresh_161 (f : Var) :
    (nb095AlphaDummy038 f) ∉
      (((Class.cv (nb095AlphaDummy029 f))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb095AlphaDummy038] using
    freshVar_not_mem (((Class.cv (nb095AlphaDummy029 f))).fv ∪ ((synC1c)).fv) 2

theorem nb095_distinct_162 (f : Var) :
    (nb095AlphaDummy036 f) ≠ (nb095AlphaDummy037 f) := by
  simpa only [nb095AlphaDummy036, nb095AlphaDummy037] using
    (freshVar_injective (((Class.cv (nb095AlphaDummy029 f))).fv ∪ ((synC1c)).fv) (i :=
      0) (j := 1) (by decide))

theorem nb095_distinct_163 (f : Var) :
    (nb095AlphaDummy036 f) ≠ (nb095AlphaDummy038 f) := by
  simpa only [nb095AlphaDummy036, nb095AlphaDummy038] using
    (freshVar_injective (((Class.cv (nb095AlphaDummy029 f))).fv ∪ ((synC1c)).fv) (i :=
      0) (j := 2) (by decide))

theorem nb095_distinct_164 (f : Var) :
    (nb095AlphaDummy037 f) ≠ (nb095AlphaDummy038 f) := by
  simpa only [nb095AlphaDummy037, nb095AlphaDummy038] using
    (freshVar_injective (((Class.cv (nb095AlphaDummy029 f))).fv ∪ ((synC1c)).fv) (i :=
      1) (j := 2) (by decide))

theorem nb095_fresh_165 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095AlphaDummy045 D R S_cls E) ∉
      (((Class.cv (nb095AlphaDummy034 D R S_cls E))).fv ∪
        ((Class.cv (nb095AlphaDummy034 D R S_cls E))).fv) :=
  by
  simpa only [nb095AlphaDummy045] using
    freshVar_not_mem
      (((Class.cv (nb095AlphaDummy034 D R S_cls E))).fv ∪
        ((Class.cv (nb095AlphaDummy034 D R S_cls E))).fv)
      0

theorem nb095_fresh_166 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095AlphaDummy041 D R S_cls E) ∉
      (((Class.cv (nb095AlphaDummy034 D R S_cls E))).fv ∪
        ((Class.cv (nb095AlphaDummy035 D R S_cls E))).fv) :=
  by
  simpa only [nb095AlphaDummy041] using
    freshVar_not_mem
      (((Class.cv (nb095AlphaDummy034 D R S_cls E))).fv ∪
        ((Class.cv (nb095AlphaDummy035 D R S_cls E))).fv)
      0

theorem nb095_fresh_167 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095AlphaDummy047 D R S_cls E) ∉
      (((Class.cv (nb095AlphaDummy035 D R S_cls E))).fv ∪
        ((Class.cv (nb095AlphaDummy035 D R S_cls E))).fv) :=
  by
  simpa only [nb095AlphaDummy047] using
    freshVar_not_mem
      (((Class.cv (nb095AlphaDummy035 D R S_cls E))).fv ∪
        ((Class.cv (nb095AlphaDummy035 D R S_cls E))).fv)
      0

theorem nb095_fresh_168 (f : Var) :
    (nb095AlphaDummy046 f) ∉
      (((Class.cv (nb095AlphaDummy037 f))).fv ∪ ((Class.cv (nb095AlphaDummy037 f))).fv) :=
  by
  simpa only [nb095AlphaDummy046] using
    freshVar_not_mem
      (((Class.cv (nb095AlphaDummy037 f))).fv ∪ ((Class.cv (nb095AlphaDummy037 f))).fv)
      0

theorem nb095_fresh_169 (f : Var) :
    (nb095AlphaDummy042 f) ∉
      (((Class.cv (nb095AlphaDummy037 f))).fv ∪ ((Class.cv (nb095AlphaDummy038 f))).fv) :=
  by
  simpa only [nb095AlphaDummy042] using
    freshVar_not_mem
      (((Class.cv (nb095AlphaDummy037 f))).fv ∪ ((Class.cv (nb095AlphaDummy038 f))).fv)
      0

theorem nb095_fresh_170 (f : Var) :
    (nb095AlphaDummy048 f) ∉
      (((Class.cv (nb095AlphaDummy038 f))).fv ∪ ((Class.cv (nb095AlphaDummy038 f))).fv) :=
  by
  simpa only [nb095AlphaDummy048] using
    freshVar_not_mem
      (((Class.cv (nb095AlphaDummy038 f))).fv ∪ ((Class.cv (nb095AlphaDummy038 f))).fv)
      0

theorem nb095_fresh_171 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095AlphaDummy063 D R S_cls E) ∉
      (((Class.cv (nb095AlphaDummy056 D R S_cls E))).fv) :=
  by
  simpa only [nb095AlphaDummy063] using
    freshVar_not_mem (((Class.cv (nb095AlphaDummy056 D R S_cls E))).fv) 0

theorem nb095_fresh_172 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095AlphaDummy064 D R S_cls E) ∉
      (((Class.cv (nb095AlphaDummy056 D R S_cls E))).fv) :=
  by
  simpa only [nb095AlphaDummy064] using
    freshVar_not_mem (((Class.cv (nb095AlphaDummy056 D R S_cls E))).fv) 1

theorem nb095_distinct_173 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095AlphaDummy063 D R S_cls E) ≠ (nb095AlphaDummy064 D R S_cls E) := by
  simpa only [nb095AlphaDummy063, nb095AlphaDummy064] using
    (freshVar_injective (((Class.cv (nb095AlphaDummy056 D R S_cls E))).fv) (i := 0)
      (j := 1) (by decide))

theorem nb095_fresh_174 (f : Var) :
    (nb095AlphaDummy065 f) ∉ (((Class.cv (nb095AlphaDummy058 f))).fv) := by
  simpa only [nb095AlphaDummy065] using
    freshVar_not_mem (((Class.cv (nb095AlphaDummy058 f))).fv) 0

theorem nb095_fresh_175 (f : Var) :
    (nb095AlphaDummy066 f) ∉ (((Class.cv (nb095AlphaDummy058 f))).fv) := by
  simpa only [nb095AlphaDummy066] using
    freshVar_not_mem (((Class.cv (nb095AlphaDummy058 f))).fv) 1

theorem nb095_distinct_176 (f : Var) :
    (nb095AlphaDummy065 f) ≠ (nb095AlphaDummy066 f) := by
  simpa only [nb095AlphaDummy065, nb095AlphaDummy066] using
    (freshVar_injective (((Class.cv (nb095AlphaDummy058 f))).fv) (i := 0) (j := 1)
      (by decide))

theorem nb095_fresh_177 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095AlphaDummy069 D R S_cls E) ∉
      (((Class.cv (nb095AlphaDummy063 D R S_cls E))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb095AlphaDummy069] using
    freshVar_not_mem
      (((Class.cv (nb095AlphaDummy063 D R S_cls E))).fv ∪ ((synC1c)).fv) 0

theorem nb095_fresh_178 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095AlphaDummy070 D R S_cls E) ∉
      (((Class.cv (nb095AlphaDummy063 D R S_cls E))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb095AlphaDummy070] using
    freshVar_not_mem
      (((Class.cv (nb095AlphaDummy063 D R S_cls E))).fv ∪ ((synC1c)).fv) 1

theorem nb095_fresh_179 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095AlphaDummy071 D R S_cls E) ∉
      (((Class.cv (nb095AlphaDummy063 D R S_cls E))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb095AlphaDummy071] using
    freshVar_not_mem
      (((Class.cv (nb095AlphaDummy063 D R S_cls E))).fv ∪ ((synC1c)).fv) 2

theorem nb095_distinct_180 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095AlphaDummy069 D R S_cls E) ≠ (nb095AlphaDummy070 D R S_cls E) := by
  simpa only [nb095AlphaDummy069, nb095AlphaDummy070] using
    (freshVar_injective
      (((Class.cv (nb095AlphaDummy063 D R S_cls E))).fv ∪ ((synC1c)).fv) (i := 0)
      (j := 1) (by decide))

theorem nb095_distinct_181 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095AlphaDummy069 D R S_cls E) ≠ (nb095AlphaDummy071 D R S_cls E) := by
  simpa only [nb095AlphaDummy069, nb095AlphaDummy071] using
    (freshVar_injective
      (((Class.cv (nb095AlphaDummy063 D R S_cls E))).fv ∪ ((synC1c)).fv) (i := 0)
      (j := 2) (by decide))

theorem nb095_distinct_182 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095AlphaDummy070 D R S_cls E) ≠ (nb095AlphaDummy071 D R S_cls E) := by
  simpa only [nb095AlphaDummy070, nb095AlphaDummy071] using
    (freshVar_injective
      (((Class.cv (nb095AlphaDummy063 D R S_cls E))).fv ∪ ((synC1c)).fv) (i := 1)
      (j := 2) (by decide))

theorem nb095_fresh_183 (f : Var) :
    (nb095AlphaDummy072 f) ∉
      (((Class.cv (nb095AlphaDummy065 f))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb095AlphaDummy072] using
    freshVar_not_mem (((Class.cv (nb095AlphaDummy065 f))).fv ∪ ((synC1c)).fv) 0

theorem nb095_fresh_184 (f : Var) :
    (nb095AlphaDummy073 f) ∉
      (((Class.cv (nb095AlphaDummy065 f))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb095AlphaDummy073] using
    freshVar_not_mem (((Class.cv (nb095AlphaDummy065 f))).fv ∪ ((synC1c)).fv) 1

theorem nb095_fresh_185 (f : Var) :
    (nb095AlphaDummy074 f) ∉
      (((Class.cv (nb095AlphaDummy065 f))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb095AlphaDummy074] using
    freshVar_not_mem (((Class.cv (nb095AlphaDummy065 f))).fv ∪ ((synC1c)).fv) 2

theorem nb095_distinct_186 (f : Var) :
    (nb095AlphaDummy072 f) ≠ (nb095AlphaDummy073 f) := by
  simpa only [nb095AlphaDummy072, nb095AlphaDummy073] using
    (freshVar_injective (((Class.cv (nb095AlphaDummy065 f))).fv ∪ ((synC1c)).fv) (i :=
      0) (j := 1) (by decide))

theorem nb095_distinct_187 (f : Var) :
    (nb095AlphaDummy072 f) ≠ (nb095AlphaDummy074 f) := by
  simpa only [nb095AlphaDummy072, nb095AlphaDummy074] using
    (freshVar_injective (((Class.cv (nb095AlphaDummy065 f))).fv ∪ ((synC1c)).fv) (i :=
      0) (j := 2) (by decide))

theorem nb095_distinct_188 (f : Var) :
    (nb095AlphaDummy073 f) ≠ (nb095AlphaDummy074 f) := by
  simpa only [nb095AlphaDummy073, nb095AlphaDummy074] using
    (freshVar_injective (((Class.cv (nb095AlphaDummy065 f))).fv ∪ ((synC1c)).fv) (i :=
      1) (j := 2) (by decide))

theorem nb095_fresh_189 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095AlphaDummy081 D R S_cls E) ∉
      (((Class.cv (nb095AlphaDummy070 D R S_cls E))).fv ∪
        ((Class.cv (nb095AlphaDummy070 D R S_cls E))).fv) :=
  by
  simpa only [nb095AlphaDummy081] using
    freshVar_not_mem
      (((Class.cv (nb095AlphaDummy070 D R S_cls E))).fv ∪
        ((Class.cv (nb095AlphaDummy070 D R S_cls E))).fv)
      0

theorem nb095_fresh_190 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095AlphaDummy077 D R S_cls E) ∉
      (((Class.cv (nb095AlphaDummy070 D R S_cls E))).fv ∪
        ((Class.cv (nb095AlphaDummy071 D R S_cls E))).fv) :=
  by
  simpa only [nb095AlphaDummy077] using
    freshVar_not_mem
      (((Class.cv (nb095AlphaDummy070 D R S_cls E))).fv ∪
        ((Class.cv (nb095AlphaDummy071 D R S_cls E))).fv)
      0

theorem nb095_fresh_191 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095AlphaDummy083 D R S_cls E) ∉
      (((Class.cv (nb095AlphaDummy071 D R S_cls E))).fv ∪
        ((Class.cv (nb095AlphaDummy071 D R S_cls E))).fv) :=
  by
  simpa only [nb095AlphaDummy083] using
    freshVar_not_mem
      (((Class.cv (nb095AlphaDummy071 D R S_cls E))).fv ∪
        ((Class.cv (nb095AlphaDummy071 D R S_cls E))).fv)
      0

theorem nb095_fresh_192 (f : Var) :
    (nb095AlphaDummy082 f) ∉
      (((Class.cv (nb095AlphaDummy073 f))).fv ∪ ((Class.cv (nb095AlphaDummy073 f))).fv) :=
  by
  simpa only [nb095AlphaDummy082] using
    freshVar_not_mem
      (((Class.cv (nb095AlphaDummy073 f))).fv ∪ ((Class.cv (nb095AlphaDummy073 f))).fv)
      0

theorem nb095_fresh_193 (f : Var) :
    (nb095AlphaDummy078 f) ∉
      (((Class.cv (nb095AlphaDummy073 f))).fv ∪ ((Class.cv (nb095AlphaDummy074 f))).fv) :=
  by
  simpa only [nb095AlphaDummy078] using
    freshVar_not_mem
      (((Class.cv (nb095AlphaDummy073 f))).fv ∪ ((Class.cv (nb095AlphaDummy074 f))).fv)
      0

theorem nb095_fresh_194 (f : Var) :
    (nb095AlphaDummy084 f) ∉
      (((Class.cv (nb095AlphaDummy074 f))).fv ∪ ((Class.cv (nb095AlphaDummy074 f))).fv) :=
  by
  simpa only [nb095AlphaDummy084] using
    freshVar_not_mem
      (((Class.cv (nb095AlphaDummy074 f))).fv ∪ ((Class.cv (nb095AlphaDummy074 f))).fv)
      0

theorem nb095_fresh_195 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095AlphaDummy097 D R S_cls E) ∉
      (((Class.cv (nb095AlphaDummy091 D R S_cls E))).fv ∪
        ((Class.cv (nb095AlphaDummy092 D R S_cls E))).fv) :=
  by
  simpa only [nb095AlphaDummy097] using
    freshVar_not_mem
      (((Class.cv (nb095AlphaDummy091 D R S_cls E))).fv ∪
        ((Class.cv (nb095AlphaDummy092 D R S_cls E))).fv)
      0

theorem nb095_fresh_196 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095AlphaDummy098 D R S_cls E) ∉
      (((Class.cv (nb095AlphaDummy091 D R S_cls E))).fv ∪
        ((Class.cv (nb095AlphaDummy092 D R S_cls E))).fv) :=
  by
  simpa only [nb095AlphaDummy098] using
    freshVar_not_mem
      (((Class.cv (nb095AlphaDummy091 D R S_cls E))).fv ∪
        ((Class.cv (nb095AlphaDummy092 D R S_cls E))).fv)
      1

theorem nb095_distinct_197 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095AlphaDummy097 D R S_cls E) ≠ (nb095AlphaDummy098 D R S_cls E) := by
  simpa only [nb095AlphaDummy097, nb095AlphaDummy098] using
    (freshVar_injective (((Class.cv (nb095AlphaDummy091 D R S_cls E))).fv ∪
        ((Class.cv (nb095AlphaDummy092 D R S_cls E))).fv) (i := 0) (j := 1) (by decide))

theorem nb095_fresh_198 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095AlphaDummy133 D R S_cls E) ∉
      (((Class.cv (nb095AlphaDummy092 D R S_cls E))).fv ∪
        ((Class.cv (nb095AlphaDummy091 D R S_cls E))).fv) :=
  by
  simpa only [nb095AlphaDummy133] using
    freshVar_not_mem
      (((Class.cv (nb095AlphaDummy092 D R S_cls E))).fv ∪
        ((Class.cv (nb095AlphaDummy091 D R S_cls E))).fv)
      0

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

theorem nb095_fresh_199 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095AlphaDummy134 D R S_cls E) ∉
      (((Class.cv (nb095AlphaDummy092 D R S_cls E))).fv ∪
        ((Class.cv (nb095AlphaDummy091 D R S_cls E))).fv) :=
  by
  simpa only [nb095AlphaDummy134] using
    freshVar_not_mem
      (((Class.cv (nb095AlphaDummy092 D R S_cls E))).fv ∪
        ((Class.cv (nb095AlphaDummy091 D R S_cls E))).fv)
      1

theorem nb095_distinct_200 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095AlphaDummy133 D R S_cls E) ≠ (nb095AlphaDummy134 D R S_cls E) := by
  simpa only [nb095AlphaDummy133, nb095AlphaDummy134] using
    (freshVar_injective (((Class.cv (nb095AlphaDummy092 D R S_cls E))).fv ∪
        ((Class.cv (nb095AlphaDummy091 D R S_cls E))).fv) (i := 0) (j := 1) (by decide))

theorem nb095_fresh_201 (f : Var) :
    (nb095AlphaDummy099 f) ∉
      (((Class.cv (nb095AlphaDummy093 f))).fv ∪ ((Class.cv (nb095AlphaDummy094 f))).fv) :=
  by
  simpa only [nb095AlphaDummy099] using
    freshVar_not_mem
      (((Class.cv (nb095AlphaDummy093 f))).fv ∪ ((Class.cv (nb095AlphaDummy094 f))).fv)
      0

theorem nb095_fresh_202 (f : Var) :
    (nb095AlphaDummy100 f) ∉
      (((Class.cv (nb095AlphaDummy093 f))).fv ∪ ((Class.cv (nb095AlphaDummy094 f))).fv) :=
  by
  simpa only [nb095AlphaDummy100] using
    freshVar_not_mem
      (((Class.cv (nb095AlphaDummy093 f))).fv ∪ ((Class.cv (nb095AlphaDummy094 f))).fv)
      1

theorem nb095_distinct_203 (f : Var) :
    (nb095AlphaDummy099 f) ≠ (nb095AlphaDummy100 f) := by
  simpa only [nb095AlphaDummy099, nb095AlphaDummy100] using
    (freshVar_injective (((Class.cv (nb095AlphaDummy093 f))).fv ∪
        ((Class.cv (nb095AlphaDummy094 f))).fv) (i := 0) (j := 1) (by decide))

theorem nb095_fresh_204 (f : Var) :
    (nb095AlphaDummy135 f) ∉
      (((Class.cv (nb095AlphaDummy094 f))).fv ∪ ((Class.cv (nb095AlphaDummy093 f))).fv) :=
  by
  simpa only [nb095AlphaDummy135] using
    freshVar_not_mem
      (((Class.cv (nb095AlphaDummy094 f))).fv ∪ ((Class.cv (nb095AlphaDummy093 f))).fv)
      0

theorem nb095_fresh_205 (f : Var) :
    (nb095AlphaDummy136 f) ∉
      (((Class.cv (nb095AlphaDummy094 f))).fv ∪ ((Class.cv (nb095AlphaDummy093 f))).fv) :=
  by
  simpa only [nb095AlphaDummy136] using
    freshVar_not_mem
      (((Class.cv (nb095AlphaDummy094 f))).fv ∪ ((Class.cv (nb095AlphaDummy093 f))).fv)
      1

theorem nb095_distinct_206 (f : Var) :
    (nb095AlphaDummy135 f) ≠ (nb095AlphaDummy136 f) := by
  simpa only [nb095AlphaDummy135, nb095AlphaDummy136] using
    (freshVar_injective (((Class.cv (nb095AlphaDummy094 f))).fv ∪
        ((Class.cv (nb095AlphaDummy093 f))).fv) (i := 0) (j := 1) (by decide))

theorem nb095_fresh_207 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095AlphaDummy105 D R S_cls E) ∉
      (((Class.cv (nb095AlphaDummy098 D R S_cls E))).fv) :=
  by
  simpa only [nb095AlphaDummy105] using
    freshVar_not_mem (((Class.cv (nb095AlphaDummy098 D R S_cls E))).fv) 0

theorem nb095_fresh_208 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095AlphaDummy106 D R S_cls E) ∉
      (((Class.cv (nb095AlphaDummy098 D R S_cls E))).fv) :=
  by
  simpa only [nb095AlphaDummy106] using
    freshVar_not_mem (((Class.cv (nb095AlphaDummy098 D R S_cls E))).fv) 1

theorem nb095_distinct_209 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095AlphaDummy105 D R S_cls E) ≠ (nb095AlphaDummy106 D R S_cls E) := by
  simpa only [nb095AlphaDummy105, nb095AlphaDummy106] using
    (freshVar_injective (((Class.cv (nb095AlphaDummy098 D R S_cls E))).fv) (i := 0)
      (j := 1) (by decide))

theorem nb095_fresh_210 (f : Var) :
    (nb095AlphaDummy107 f) ∉ (((Class.cv (nb095AlphaDummy100 f))).fv) := by
  simpa only [nb095AlphaDummy107] using
    freshVar_not_mem (((Class.cv (nb095AlphaDummy100 f))).fv) 0

theorem nb095_fresh_211 (f : Var) :
    (nb095AlphaDummy108 f) ∉ (((Class.cv (nb095AlphaDummy100 f))).fv) := by
  simpa only [nb095AlphaDummy108] using
    freshVar_not_mem (((Class.cv (nb095AlphaDummy100 f))).fv) 1

theorem nb095_distinct_212 (f : Var) :
    (nb095AlphaDummy107 f) ≠ (nb095AlphaDummy108 f) := by
  simpa only [nb095AlphaDummy107, nb095AlphaDummy108] using
    (freshVar_injective (((Class.cv (nb095AlphaDummy100 f))).fv) (i := 0) (j := 1)
      (by decide))

theorem nb095_fresh_213 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095AlphaDummy111 D R S_cls E) ∉
      (((Class.cv (nb095AlphaDummy105 D R S_cls E))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb095AlphaDummy111] using
    freshVar_not_mem
      (((Class.cv (nb095AlphaDummy105 D R S_cls E))).fv ∪ ((synC1c)).fv) 0

theorem nb095_fresh_214 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095AlphaDummy112 D R S_cls E) ∉
      (((Class.cv (nb095AlphaDummy105 D R S_cls E))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb095AlphaDummy112] using
    freshVar_not_mem
      (((Class.cv (nb095AlphaDummy105 D R S_cls E))).fv ∪ ((synC1c)).fv) 1

theorem nb095_fresh_215 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095AlphaDummy113 D R S_cls E) ∉
      (((Class.cv (nb095AlphaDummy105 D R S_cls E))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb095AlphaDummy113] using
    freshVar_not_mem
      (((Class.cv (nb095AlphaDummy105 D R S_cls E))).fv ∪ ((synC1c)).fv) 2

theorem nb095_distinct_216 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095AlphaDummy111 D R S_cls E) ≠ (nb095AlphaDummy112 D R S_cls E) := by
  simpa only [nb095AlphaDummy111, nb095AlphaDummy112] using
    (freshVar_injective
      (((Class.cv (nb095AlphaDummy105 D R S_cls E))).fv ∪ ((synC1c)).fv) (i := 0)
      (j := 1) (by decide))

theorem nb095_distinct_217 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095AlphaDummy111 D R S_cls E) ≠ (nb095AlphaDummy113 D R S_cls E) := by
  simpa only [nb095AlphaDummy111, nb095AlphaDummy113] using
    (freshVar_injective
      (((Class.cv (nb095AlphaDummy105 D R S_cls E))).fv ∪ ((synC1c)).fv) (i := 0)
      (j := 2) (by decide))

theorem nb095_distinct_218 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095AlphaDummy112 D R S_cls E) ≠ (nb095AlphaDummy113 D R S_cls E) := by
  simpa only [nb095AlphaDummy112, nb095AlphaDummy113] using
    (freshVar_injective
      (((Class.cv (nb095AlphaDummy105 D R S_cls E))).fv ∪ ((synC1c)).fv) (i := 1)
      (j := 2) (by decide))

theorem nb095_fresh_219 (f : Var) :
    (nb095AlphaDummy114 f) ∉
      (((Class.cv (nb095AlphaDummy107 f))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb095AlphaDummy114] using
    freshVar_not_mem (((Class.cv (nb095AlphaDummy107 f))).fv ∪ ((synC1c)).fv) 0

theorem nb095_fresh_220 (f : Var) :
    (nb095AlphaDummy115 f) ∉
      (((Class.cv (nb095AlphaDummy107 f))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb095AlphaDummy115] using
    freshVar_not_mem (((Class.cv (nb095AlphaDummy107 f))).fv ∪ ((synC1c)).fv) 1

theorem nb095_fresh_221 (f : Var) :
    (nb095AlphaDummy116 f) ∉
      (((Class.cv (nb095AlphaDummy107 f))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb095AlphaDummy116] using
    freshVar_not_mem (((Class.cv (nb095AlphaDummy107 f))).fv ∪ ((synC1c)).fv) 2

theorem nb095_distinct_222 (f : Var) :
    (nb095AlphaDummy114 f) ≠ (nb095AlphaDummy115 f) := by
  simpa only [nb095AlphaDummy114, nb095AlphaDummy115] using
    (freshVar_injective (((Class.cv (nb095AlphaDummy107 f))).fv ∪ ((synC1c)).fv) (i :=
      0) (j := 1) (by decide))

theorem nb095_distinct_223 (f : Var) :
    (nb095AlphaDummy114 f) ≠ (nb095AlphaDummy116 f) := by
  simpa only [nb095AlphaDummy114, nb095AlphaDummy116] using
    (freshVar_injective (((Class.cv (nb095AlphaDummy107 f))).fv ∪ ((synC1c)).fv) (i :=
      0) (j := 2) (by decide))

theorem nb095_distinct_224 (f : Var) :
    (nb095AlphaDummy115 f) ≠ (nb095AlphaDummy116 f) := by
  simpa only [nb095AlphaDummy115, nb095AlphaDummy116] using
    (freshVar_injective (((Class.cv (nb095AlphaDummy107 f))).fv ∪ ((synC1c)).fv) (i :=
      1) (j := 2) (by decide))

theorem nb095_fresh_225 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095AlphaDummy123 D R S_cls E) ∉
      (((Class.cv (nb095AlphaDummy112 D R S_cls E))).fv ∪
        ((Class.cv (nb095AlphaDummy112 D R S_cls E))).fv) :=
  by
  simpa only [nb095AlphaDummy123] using
    freshVar_not_mem
      (((Class.cv (nb095AlphaDummy112 D R S_cls E))).fv ∪
        ((Class.cv (nb095AlphaDummy112 D R S_cls E))).fv)
      0

theorem nb095_fresh_226 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095AlphaDummy119 D R S_cls E) ∉
      (((Class.cv (nb095AlphaDummy112 D R S_cls E))).fv ∪
        ((Class.cv (nb095AlphaDummy113 D R S_cls E))).fv) :=
  by
  simpa only [nb095AlphaDummy119] using
    freshVar_not_mem
      (((Class.cv (nb095AlphaDummy112 D R S_cls E))).fv ∪
        ((Class.cv (nb095AlphaDummy113 D R S_cls E))).fv)
      0

theorem nb095_fresh_227 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095AlphaDummy125 D R S_cls E) ∉
      (((Class.cv (nb095AlphaDummy113 D R S_cls E))).fv ∪
        ((Class.cv (nb095AlphaDummy113 D R S_cls E))).fv) :=
  by
  simpa only [nb095AlphaDummy125] using
    freshVar_not_mem
      (((Class.cv (nb095AlphaDummy113 D R S_cls E))).fv ∪
        ((Class.cv (nb095AlphaDummy113 D R S_cls E))).fv)
      0

theorem nb095_fresh_228 (f : Var) :
    (nb095AlphaDummy124 f) ∉
      (((Class.cv (nb095AlphaDummy115 f))).fv ∪ ((Class.cv (nb095AlphaDummy115 f))).fv) :=
  by
  simpa only [nb095AlphaDummy124] using
    freshVar_not_mem
      (((Class.cv (nb095AlphaDummy115 f))).fv ∪ ((Class.cv (nb095AlphaDummy115 f))).fv)
      0

theorem nb095_fresh_229 (f : Var) :
    (nb095AlphaDummy120 f) ∉
      (((Class.cv (nb095AlphaDummy115 f))).fv ∪ ((Class.cv (nb095AlphaDummy116 f))).fv) :=
  by
  simpa only [nb095AlphaDummy120] using
    freshVar_not_mem
      (((Class.cv (nb095AlphaDummy115 f))).fv ∪ ((Class.cv (nb095AlphaDummy116 f))).fv)
      0

theorem nb095_fresh_230 (f : Var) :
    (nb095AlphaDummy126 f) ∉
      (((Class.cv (nb095AlphaDummy116 f))).fv ∪ ((Class.cv (nb095AlphaDummy116 f))).fv) :=
  by
  simpa only [nb095AlphaDummy126] using
    freshVar_not_mem
      (((Class.cv (nb095AlphaDummy116 f))).fv ∪ ((Class.cv (nb095AlphaDummy116 f))).fv)
      0

theorem nb095_fresh_231 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095AlphaDummy141 D R S_cls E) ∉
      (((Class.cv (nb095AlphaDummy134 D R S_cls E))).fv) :=
  by
  simpa only [nb095AlphaDummy141] using
    freshVar_not_mem (((Class.cv (nb095AlphaDummy134 D R S_cls E))).fv) 0

theorem nb095_fresh_232 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095AlphaDummy142 D R S_cls E) ∉
      (((Class.cv (nb095AlphaDummy134 D R S_cls E))).fv) :=
  by
  simpa only [nb095AlphaDummy142] using
    freshVar_not_mem (((Class.cv (nb095AlphaDummy134 D R S_cls E))).fv) 1

theorem nb095_distinct_233 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095AlphaDummy141 D R S_cls E) ≠ (nb095AlphaDummy142 D R S_cls E) := by
  simpa only [nb095AlphaDummy141, nb095AlphaDummy142] using
    (freshVar_injective (((Class.cv (nb095AlphaDummy134 D R S_cls E))).fv) (i := 0)
      (j := 1) (by decide))

theorem nb095_fresh_234 (f : Var) :
    (nb095AlphaDummy143 f) ∉ (((Class.cv (nb095AlphaDummy136 f))).fv) := by
  simpa only [nb095AlphaDummy143] using
    freshVar_not_mem (((Class.cv (nb095AlphaDummy136 f))).fv) 0

theorem nb095_fresh_235 (f : Var) :
    (nb095AlphaDummy144 f) ∉ (((Class.cv (nb095AlphaDummy136 f))).fv) := by
  simpa only [nb095AlphaDummy144] using
    freshVar_not_mem (((Class.cv (nb095AlphaDummy136 f))).fv) 1

theorem nb095_distinct_236 (f : Var) :
    (nb095AlphaDummy143 f) ≠ (nb095AlphaDummy144 f) := by
  simpa only [nb095AlphaDummy143, nb095AlphaDummy144] using
    (freshVar_injective (((Class.cv (nb095AlphaDummy136 f))).fv) (i := 0) (j := 1)
      (by decide))

theorem nb095_fresh_237 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095AlphaDummy147 D R S_cls E) ∉
      (((Class.cv (nb095AlphaDummy141 D R S_cls E))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb095AlphaDummy147] using
    freshVar_not_mem
      (((Class.cv (nb095AlphaDummy141 D R S_cls E))).fv ∪ ((synC1c)).fv) 0

theorem nb095_fresh_238 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095AlphaDummy148 D R S_cls E) ∉
      (((Class.cv (nb095AlphaDummy141 D R S_cls E))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb095AlphaDummy148] using
    freshVar_not_mem
      (((Class.cv (nb095AlphaDummy141 D R S_cls E))).fv ∪ ((synC1c)).fv) 1

theorem nb095_fresh_239 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095AlphaDummy149 D R S_cls E) ∉
      (((Class.cv (nb095AlphaDummy141 D R S_cls E))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb095AlphaDummy149] using
    freshVar_not_mem
      (((Class.cv (nb095AlphaDummy141 D R S_cls E))).fv ∪ ((synC1c)).fv) 2

theorem nb095_distinct_240 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095AlphaDummy147 D R S_cls E) ≠ (nb095AlphaDummy148 D R S_cls E) := by
  simpa only [nb095AlphaDummy147, nb095AlphaDummy148] using
    (freshVar_injective
      (((Class.cv (nb095AlphaDummy141 D R S_cls E))).fv ∪ ((synC1c)).fv) (i := 0)
      (j := 1) (by decide))

theorem nb095_distinct_241 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095AlphaDummy147 D R S_cls E) ≠ (nb095AlphaDummy149 D R S_cls E) := by
  simpa only [nb095AlphaDummy147, nb095AlphaDummy149] using
    (freshVar_injective
      (((Class.cv (nb095AlphaDummy141 D R S_cls E))).fv ∪ ((synC1c)).fv) (i := 0)
      (j := 2) (by decide))

theorem nb095_distinct_242 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095AlphaDummy148 D R S_cls E) ≠ (nb095AlphaDummy149 D R S_cls E) := by
  simpa only [nb095AlphaDummy148, nb095AlphaDummy149] using
    (freshVar_injective
      (((Class.cv (nb095AlphaDummy141 D R S_cls E))).fv ∪ ((synC1c)).fv) (i := 1)
      (j := 2) (by decide))

theorem nb095_fresh_243 (f : Var) :
    (nb095AlphaDummy150 f) ∉
      (((Class.cv (nb095AlphaDummy143 f))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb095AlphaDummy150] using
    freshVar_not_mem (((Class.cv (nb095AlphaDummy143 f))).fv ∪ ((synC1c)).fv) 0

theorem nb095_fresh_244 (f : Var) :
    (nb095AlphaDummy151 f) ∉
      (((Class.cv (nb095AlphaDummy143 f))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb095AlphaDummy151] using
    freshVar_not_mem (((Class.cv (nb095AlphaDummy143 f))).fv ∪ ((synC1c)).fv) 1

theorem nb095_fresh_245 (f : Var) :
    (nb095AlphaDummy152 f) ∉
      (((Class.cv (nb095AlphaDummy143 f))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb095AlphaDummy152] using
    freshVar_not_mem (((Class.cv (nb095AlphaDummy143 f))).fv ∪ ((synC1c)).fv) 2

theorem nb095_distinct_246 (f : Var) :
    (nb095AlphaDummy150 f) ≠ (nb095AlphaDummy151 f) := by
  simpa only [nb095AlphaDummy150, nb095AlphaDummy151] using
    (freshVar_injective (((Class.cv (nb095AlphaDummy143 f))).fv ∪ ((synC1c)).fv) (i :=
      0) (j := 1) (by decide))

theorem nb095_distinct_247 (f : Var) :
    (nb095AlphaDummy150 f) ≠ (nb095AlphaDummy152 f) := by
  simpa only [nb095AlphaDummy150, nb095AlphaDummy152] using
    (freshVar_injective (((Class.cv (nb095AlphaDummy143 f))).fv ∪ ((synC1c)).fv) (i :=
      0) (j := 2) (by decide))

theorem nb095_distinct_248 (f : Var) :
    (nb095AlphaDummy151 f) ≠ (nb095AlphaDummy152 f) := by
  simpa only [nb095AlphaDummy151, nb095AlphaDummy152] using
    (freshVar_injective (((Class.cv (nb095AlphaDummy143 f))).fv ∪ ((synC1c)).fv) (i :=
      1) (j := 2) (by decide))

theorem nb095_fresh_249 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095AlphaDummy159 D R S_cls E) ∉
      (((Class.cv (nb095AlphaDummy148 D R S_cls E))).fv ∪
        ((Class.cv (nb095AlphaDummy148 D R S_cls E))).fv) :=
  by
  simpa only [nb095AlphaDummy159] using
    freshVar_not_mem
      (((Class.cv (nb095AlphaDummy148 D R S_cls E))).fv ∪
        ((Class.cv (nb095AlphaDummy148 D R S_cls E))).fv)
      0

theorem nb095_fresh_250 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095AlphaDummy155 D R S_cls E) ∉
      (((Class.cv (nb095AlphaDummy148 D R S_cls E))).fv ∪
        ((Class.cv (nb095AlphaDummy149 D R S_cls E))).fv) :=
  by
  simpa only [nb095AlphaDummy155] using
    freshVar_not_mem
      (((Class.cv (nb095AlphaDummy148 D R S_cls E))).fv ∪
        ((Class.cv (nb095AlphaDummy149 D R S_cls E))).fv)
      0

theorem nb095_fresh_251 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095AlphaDummy161 D R S_cls E) ∉
      (((Class.cv (nb095AlphaDummy149 D R S_cls E))).fv ∪
        ((Class.cv (nb095AlphaDummy149 D R S_cls E))).fv) :=
  by
  simpa only [nb095AlphaDummy161] using
    freshVar_not_mem
      (((Class.cv (nb095AlphaDummy149 D R S_cls E))).fv ∪
        ((Class.cv (nb095AlphaDummy149 D R S_cls E))).fv)
      0

theorem nb095_fresh_252 (f : Var) :
    (nb095AlphaDummy160 f) ∉
      (((Class.cv (nb095AlphaDummy151 f))).fv ∪ ((Class.cv (nb095AlphaDummy151 f))).fv) :=
  by
  simpa only [nb095AlphaDummy160] using
    freshVar_not_mem
      (((Class.cv (nb095AlphaDummy151 f))).fv ∪ ((Class.cv (nb095AlphaDummy151 f))).fv)
      0

theorem nb095_fresh_253 (f : Var) :
    (nb095AlphaDummy156 f) ∉
      (((Class.cv (nb095AlphaDummy151 f))).fv ∪ ((Class.cv (nb095AlphaDummy152 f))).fv) :=
  by
  simpa only [nb095AlphaDummy156] using
    freshVar_not_mem
      (((Class.cv (nb095AlphaDummy151 f))).fv ∪ ((Class.cv (nb095AlphaDummy152 f))).fv)
      0

theorem nb095_fresh_254 (f : Var) :
    (nb095AlphaDummy162 f) ∉
      (((Class.cv (nb095AlphaDummy152 f))).fv ∪ ((Class.cv (nb095AlphaDummy152 f))).fv) :=
  by
  simpa only [nb095AlphaDummy162] using
    freshVar_not_mem
      (((Class.cv (nb095AlphaDummy152 f))).fv ∪ ((Class.cv (nb095AlphaDummy152 f))).fv)
      0

theorem nb095_fresh_255 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095AlphaDummy177 D R S_cls E) ∉
      (((Class.cv (nb095AlphaDummy170 D R S_cls E))).fv) :=
  by
  simpa only [nb095AlphaDummy177] using
    freshVar_not_mem (((Class.cv (nb095AlphaDummy170 D R S_cls E))).fv) 0

theorem nb095_fresh_256 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095AlphaDummy178 D R S_cls E) ∉
      (((Class.cv (nb095AlphaDummy170 D R S_cls E))).fv) :=
  by
  simpa only [nb095AlphaDummy178] using
    freshVar_not_mem (((Class.cv (nb095AlphaDummy170 D R S_cls E))).fv) 1

theorem nb095_distinct_257 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095AlphaDummy177 D R S_cls E) ≠ (nb095AlphaDummy178 D R S_cls E) := by
  simpa only [nb095AlphaDummy177, nb095AlphaDummy178] using
    (freshVar_injective (((Class.cv (nb095AlphaDummy170 D R S_cls E))).fv) (i := 0)
      (j := 1) (by decide))

theorem nb095_fresh_258 (f : Var) :
    (nb095AlphaDummy179 f) ∉ (((Class.cv (nb095AlphaDummy172 f))).fv) := by
  simpa only [nb095AlphaDummy179] using
    freshVar_not_mem (((Class.cv (nb095AlphaDummy172 f))).fv) 0

theorem nb095_fresh_259 (f : Var) :
    (nb095AlphaDummy180 f) ∉ (((Class.cv (nb095AlphaDummy172 f))).fv) := by
  simpa only [nb095AlphaDummy180] using
    freshVar_not_mem (((Class.cv (nb095AlphaDummy172 f))).fv) 1

theorem nb095_distinct_260 (f : Var) :
    (nb095AlphaDummy179 f) ≠ (nb095AlphaDummy180 f) := by
  simpa only [nb095AlphaDummy179, nb095AlphaDummy180] using
    (freshVar_injective (((Class.cv (nb095AlphaDummy172 f))).fv) (i := 0) (j := 1)
      (by decide))

theorem nb095_fresh_261 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095AlphaDummy183 D R S_cls E) ∉
      (((Class.cv (nb095AlphaDummy177 D R S_cls E))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb095AlphaDummy183] using
    freshVar_not_mem
      (((Class.cv (nb095AlphaDummy177 D R S_cls E))).fv ∪ ((synC1c)).fv) 0

theorem nb095_fresh_262 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095AlphaDummy184 D R S_cls E) ∉
      (((Class.cv (nb095AlphaDummy177 D R S_cls E))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb095AlphaDummy184] using
    freshVar_not_mem
      (((Class.cv (nb095AlphaDummy177 D R S_cls E))).fv ∪ ((synC1c)).fv) 1

theorem nb095_fresh_263 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095AlphaDummy185 D R S_cls E) ∉
      (((Class.cv (nb095AlphaDummy177 D R S_cls E))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb095AlphaDummy185] using
    freshVar_not_mem
      (((Class.cv (nb095AlphaDummy177 D R S_cls E))).fv ∪ ((synC1c)).fv) 2

theorem nb095_distinct_264 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095AlphaDummy183 D R S_cls E) ≠ (nb095AlphaDummy184 D R S_cls E) := by
  simpa only [nb095AlphaDummy183, nb095AlphaDummy184] using
    (freshVar_injective
      (((Class.cv (nb095AlphaDummy177 D R S_cls E))).fv ∪ ((synC1c)).fv) (i := 0)
      (j := 1) (by decide))

theorem nb095_distinct_265 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095AlphaDummy183 D R S_cls E) ≠ (nb095AlphaDummy185 D R S_cls E) := by
  simpa only [nb095AlphaDummy183, nb095AlphaDummy185] using
    (freshVar_injective
      (((Class.cv (nb095AlphaDummy177 D R S_cls E))).fv ∪ ((synC1c)).fv) (i := 0)
      (j := 2) (by decide))

theorem nb095_distinct_266 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095AlphaDummy184 D R S_cls E) ≠ (nb095AlphaDummy185 D R S_cls E) := by
  simpa only [nb095AlphaDummy184, nb095AlphaDummy185] using
    (freshVar_injective
      (((Class.cv (nb095AlphaDummy177 D R S_cls E))).fv ∪ ((synC1c)).fv) (i := 1)
      (j := 2) (by decide))

theorem nb095_fresh_267 (f : Var) :
    (nb095AlphaDummy186 f) ∉
      (((Class.cv (nb095AlphaDummy179 f))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb095AlphaDummy186] using
    freshVar_not_mem (((Class.cv (nb095AlphaDummy179 f))).fv ∪ ((synC1c)).fv) 0

theorem nb095_fresh_268 (f : Var) :
    (nb095AlphaDummy187 f) ∉
      (((Class.cv (nb095AlphaDummy179 f))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb095AlphaDummy187] using
    freshVar_not_mem (((Class.cv (nb095AlphaDummy179 f))).fv ∪ ((synC1c)).fv) 1

theorem nb095_fresh_269 (f : Var) :
    (nb095AlphaDummy188 f) ∉
      (((Class.cv (nb095AlphaDummy179 f))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb095AlphaDummy188] using
    freshVar_not_mem (((Class.cv (nb095AlphaDummy179 f))).fv ∪ ((synC1c)).fv) 2

theorem nb095_distinct_270 (f : Var) :
    (nb095AlphaDummy186 f) ≠ (nb095AlphaDummy187 f) := by
  simpa only [nb095AlphaDummy186, nb095AlphaDummy187] using
    (freshVar_injective (((Class.cv (nb095AlphaDummy179 f))).fv ∪ ((synC1c)).fv) (i :=
      0) (j := 1) (by decide))

theorem nb095_distinct_271 (f : Var) :
    (nb095AlphaDummy186 f) ≠ (nb095AlphaDummy188 f) := by
  simpa only [nb095AlphaDummy186, nb095AlphaDummy188] using
    (freshVar_injective (((Class.cv (nb095AlphaDummy179 f))).fv ∪ ((synC1c)).fv) (i :=
      0) (j := 2) (by decide))

theorem nb095_distinct_272 (f : Var) :
    (nb095AlphaDummy187 f) ≠ (nb095AlphaDummy188 f) := by
  simpa only [nb095AlphaDummy187, nb095AlphaDummy188] using
    (freshVar_injective (((Class.cv (nb095AlphaDummy179 f))).fv ∪ ((synC1c)).fv) (i :=
      1) (j := 2) (by decide))

theorem nb095_fresh_273 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095AlphaDummy195 D R S_cls E) ∉
      (((Class.cv (nb095AlphaDummy184 D R S_cls E))).fv ∪
        ((Class.cv (nb095AlphaDummy184 D R S_cls E))).fv) :=
  by
  simpa only [nb095AlphaDummy195] using
    freshVar_not_mem
      (((Class.cv (nb095AlphaDummy184 D R S_cls E))).fv ∪
        ((Class.cv (nb095AlphaDummy184 D R S_cls E))).fv)
      0

theorem nb095_fresh_274 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095AlphaDummy191 D R S_cls E) ∉
      (((Class.cv (nb095AlphaDummy184 D R S_cls E))).fv ∪
        ((Class.cv (nb095AlphaDummy185 D R S_cls E))).fv) :=
  by
  simpa only [nb095AlphaDummy191] using
    freshVar_not_mem
      (((Class.cv (nb095AlphaDummy184 D R S_cls E))).fv ∪
        ((Class.cv (nb095AlphaDummy185 D R S_cls E))).fv)
      0

theorem nb095_fresh_275 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095AlphaDummy197 D R S_cls E) ∉
      (((Class.cv (nb095AlphaDummy185 D R S_cls E))).fv ∪
        ((Class.cv (nb095AlphaDummy185 D R S_cls E))).fv) :=
  by
  simpa only [nb095AlphaDummy197] using
    freshVar_not_mem
      (((Class.cv (nb095AlphaDummy185 D R S_cls E))).fv ∪
        ((Class.cv (nb095AlphaDummy185 D R S_cls E))).fv)
      0

theorem nb095_fresh_276 (f : Var) :
    (nb095AlphaDummy196 f) ∉
      (((Class.cv (nb095AlphaDummy187 f))).fv ∪ ((Class.cv (nb095AlphaDummy187 f))).fv) :=
  by
  simpa only [nb095AlphaDummy196] using
    freshVar_not_mem
      (((Class.cv (nb095AlphaDummy187 f))).fv ∪ ((Class.cv (nb095AlphaDummy187 f))).fv)
      0

theorem nb095_fresh_277 (f : Var) :
    (nb095AlphaDummy192 f) ∉
      (((Class.cv (nb095AlphaDummy187 f))).fv ∪ ((Class.cv (nb095AlphaDummy188 f))).fv) :=
  by
  simpa only [nb095AlphaDummy192] using
    freshVar_not_mem
      (((Class.cv (nb095AlphaDummy187 f))).fv ∪ ((Class.cv (nb095AlphaDummy188 f))).fv)
      0

theorem nb095_fresh_278 (f : Var) :
    (nb095AlphaDummy198 f) ∉
      (((Class.cv (nb095AlphaDummy188 f))).fv ∪ ((Class.cv (nb095AlphaDummy188 f))).fv) :=
  by
  simpa only [nb095AlphaDummy198] using
    freshVar_not_mem
      (((Class.cv (nb095AlphaDummy188 f))).fv ∪ ((Class.cv (nb095AlphaDummy188 f))).fv)
      0

theorem nb095_fresh_279 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095AlphaDummy209 D R S_cls E) ∉
      (((Class.cv (nb095AlphaDummy206 D R S_cls E))).fv ∪
        ((Class.cv (nb095AlphaDummy205 D R S_cls E))).fv) :=
  by
  simpa only [nb095AlphaDummy209] using
    freshVar_not_mem
      (((Class.cv (nb095AlphaDummy206 D R S_cls E))).fv ∪
        ((Class.cv (nb095AlphaDummy205 D R S_cls E))).fv)
      0

theorem nb095_fresh_280 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095AlphaDummy210 D R S_cls E) ∉
      (((Class.cv (nb095AlphaDummy206 D R S_cls E))).fv ∪
        ((Class.cv (nb095AlphaDummy205 D R S_cls E))).fv) :=
  by
  simpa only [nb095AlphaDummy210] using
    freshVar_not_mem
      (((Class.cv (nb095AlphaDummy206 D R S_cls E))).fv ∪
        ((Class.cv (nb095AlphaDummy205 D R S_cls E))).fv)
      1

theorem nb095_distinct_281 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095AlphaDummy209 D R S_cls E) ≠ (nb095AlphaDummy210 D R S_cls E) := by
  simpa only [nb095AlphaDummy209, nb095AlphaDummy210] using
    (freshVar_injective (((Class.cv (nb095AlphaDummy206 D R S_cls E))).fv ∪
        ((Class.cv (nb095AlphaDummy205 D R S_cls E))).fv) (i := 0) (j := 1) (by decide))

theorem nb095_fresh_282 (f : Var) :
    (nb095AlphaDummy211 f) ∉
      (((Class.cv (nb095AlphaDummy208 f))).fv ∪ ((Class.cv (nb095AlphaDummy207 f))).fv) :=
  by
  simpa only [nb095AlphaDummy211] using
    freshVar_not_mem
      (((Class.cv (nb095AlphaDummy208 f))).fv ∪ ((Class.cv (nb095AlphaDummy207 f))).fv)
      0

theorem nb095_fresh_283 (f : Var) :
    (nb095AlphaDummy212 f) ∉
      (((Class.cv (nb095AlphaDummy208 f))).fv ∪ ((Class.cv (nb095AlphaDummy207 f))).fv) :=
  by
  simpa only [nb095AlphaDummy212] using
    freshVar_not_mem
      (((Class.cv (nb095AlphaDummy208 f))).fv ∪ ((Class.cv (nb095AlphaDummy207 f))).fv)
      1

theorem nb095_distinct_284 (f : Var) :
    (nb095AlphaDummy211 f) ≠ (nb095AlphaDummy212 f) := by
  simpa only [nb095AlphaDummy211, nb095AlphaDummy212] using
    (freshVar_injective (((Class.cv (nb095AlphaDummy208 f))).fv ∪
        ((Class.cv (nb095AlphaDummy207 f))).fv) (i := 0) (j := 1) (by decide))

theorem nb095_fresh_285 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095AlphaDummy217 D R S_cls E) ∉
      (((Class.cv (nb095AlphaDummy210 D R S_cls E))).fv) :=
  by
  simpa only [nb095AlphaDummy217] using
    freshVar_not_mem (((Class.cv (nb095AlphaDummy210 D R S_cls E))).fv) 0

theorem nb095_fresh_286 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095AlphaDummy218 D R S_cls E) ∉
      (((Class.cv (nb095AlphaDummy210 D R S_cls E))).fv) :=
  by
  simpa only [nb095AlphaDummy218] using
    freshVar_not_mem (((Class.cv (nb095AlphaDummy210 D R S_cls E))).fv) 1

theorem nb095_distinct_287 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095AlphaDummy217 D R S_cls E) ≠ (nb095AlphaDummy218 D R S_cls E) := by
  simpa only [nb095AlphaDummy217, nb095AlphaDummy218] using
    (freshVar_injective (((Class.cv (nb095AlphaDummy210 D R S_cls E))).fv) (i := 0)
      (j := 1) (by decide))

theorem nb095_fresh_288 (f : Var) :
    (nb095AlphaDummy219 f) ∉ (((Class.cv (nb095AlphaDummy212 f))).fv) := by
  simpa only [nb095AlphaDummy219] using
    freshVar_not_mem (((Class.cv (nb095AlphaDummy212 f))).fv) 0

theorem nb095_fresh_289 (f : Var) :
    (nb095AlphaDummy220 f) ∉ (((Class.cv (nb095AlphaDummy212 f))).fv) := by
  simpa only [nb095AlphaDummy220] using
    freshVar_not_mem (((Class.cv (nb095AlphaDummy212 f))).fv) 1

theorem nb095_distinct_290 (f : Var) :
    (nb095AlphaDummy219 f) ≠ (nb095AlphaDummy220 f) := by
  simpa only [nb095AlphaDummy219, nb095AlphaDummy220] using
    (freshVar_injective (((Class.cv (nb095AlphaDummy212 f))).fv) (i := 0) (j := 1)
      (by decide))

theorem nb095_fresh_291 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095AlphaDummy223 D R S_cls E) ∉
      (((Class.cv (nb095AlphaDummy217 D R S_cls E))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb095AlphaDummy223] using
    freshVar_not_mem
      (((Class.cv (nb095AlphaDummy217 D R S_cls E))).fv ∪ ((synC1c)).fv) 0

theorem nb095_fresh_292 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095AlphaDummy224 D R S_cls E) ∉
      (((Class.cv (nb095AlphaDummy217 D R S_cls E))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb095AlphaDummy224] using
    freshVar_not_mem
      (((Class.cv (nb095AlphaDummy217 D R S_cls E))).fv ∪ ((synC1c)).fv) 1

theorem nb095_fresh_293 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095AlphaDummy225 D R S_cls E) ∉
      (((Class.cv (nb095AlphaDummy217 D R S_cls E))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb095AlphaDummy225] using
    freshVar_not_mem
      (((Class.cv (nb095AlphaDummy217 D R S_cls E))).fv ∪ ((synC1c)).fv) 2

theorem nb095_distinct_294 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095AlphaDummy223 D R S_cls E) ≠ (nb095AlphaDummy224 D R S_cls E) := by
  simpa only [nb095AlphaDummy223, nb095AlphaDummy224] using
    (freshVar_injective
      (((Class.cv (nb095AlphaDummy217 D R S_cls E))).fv ∪ ((synC1c)).fv) (i := 0)
      (j := 1) (by decide))

theorem nb095_distinct_295 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095AlphaDummy223 D R S_cls E) ≠ (nb095AlphaDummy225 D R S_cls E) := by
  simpa only [nb095AlphaDummy223, nb095AlphaDummy225] using
    (freshVar_injective
      (((Class.cv (nb095AlphaDummy217 D R S_cls E))).fv ∪ ((synC1c)).fv) (i := 0)
      (j := 2) (by decide))

theorem nb095_distinct_296 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095AlphaDummy224 D R S_cls E) ≠ (nb095AlphaDummy225 D R S_cls E) := by
  simpa only [nb095AlphaDummy224, nb095AlphaDummy225] using
    (freshVar_injective
      (((Class.cv (nb095AlphaDummy217 D R S_cls E))).fv ∪ ((synC1c)).fv) (i := 1)
      (j := 2) (by decide))

theorem nb095_fresh_297 (f : Var) :
    (nb095AlphaDummy226 f) ∉
      (((Class.cv (nb095AlphaDummy219 f))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb095AlphaDummy226] using
    freshVar_not_mem (((Class.cv (nb095AlphaDummy219 f))).fv ∪ ((synC1c)).fv) 0

theorem nb095_fresh_298 (f : Var) :
    (nb095AlphaDummy227 f) ∉
      (((Class.cv (nb095AlphaDummy219 f))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb095AlphaDummy227] using
    freshVar_not_mem (((Class.cv (nb095AlphaDummy219 f))).fv ∪ ((synC1c)).fv) 1

theorem nb095_fresh_299 (f : Var) :
    (nb095AlphaDummy228 f) ∉
      (((Class.cv (nb095AlphaDummy219 f))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb095AlphaDummy228] using
    freshVar_not_mem (((Class.cv (nb095AlphaDummy219 f))).fv ∪ ((synC1c)).fv) 2

theorem nb095_distinct_300 (f : Var) :
    (nb095AlphaDummy226 f) ≠ (nb095AlphaDummy227 f) := by
  simpa only [nb095AlphaDummy226, nb095AlphaDummy227] using
    (freshVar_injective (((Class.cv (nb095AlphaDummy219 f))).fv ∪ ((synC1c)).fv) (i :=
      0) (j := 1) (by decide))

theorem nb095_distinct_301 (f : Var) :
    (nb095AlphaDummy226 f) ≠ (nb095AlphaDummy228 f) := by
  simpa only [nb095AlphaDummy226, nb095AlphaDummy228] using
    (freshVar_injective (((Class.cv (nb095AlphaDummy219 f))).fv ∪ ((synC1c)).fv) (i :=
      0) (j := 2) (by decide))

theorem nb095_distinct_302 (f : Var) :
    (nb095AlphaDummy227 f) ≠ (nb095AlphaDummy228 f) := by
  simpa only [nb095AlphaDummy227, nb095AlphaDummy228] using
    (freshVar_injective (((Class.cv (nb095AlphaDummy219 f))).fv ∪ ((synC1c)).fv) (i :=
      1) (j := 2) (by decide))

theorem nb095_fresh_303 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095AlphaDummy235 D R S_cls E) ∉
      (((Class.cv (nb095AlphaDummy224 D R S_cls E))).fv ∪
        ((Class.cv (nb095AlphaDummy224 D R S_cls E))).fv) :=
  by
  simpa only [nb095AlphaDummy235] using
    freshVar_not_mem
      (((Class.cv (nb095AlphaDummy224 D R S_cls E))).fv ∪
        ((Class.cv (nb095AlphaDummy224 D R S_cls E))).fv)
      0

theorem nb095_fresh_304 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095AlphaDummy231 D R S_cls E) ∉
      (((Class.cv (nb095AlphaDummy224 D R S_cls E))).fv ∪
        ((Class.cv (nb095AlphaDummy225 D R S_cls E))).fv) :=
  by
  simpa only [nb095AlphaDummy231] using
    freshVar_not_mem
      (((Class.cv (nb095AlphaDummy224 D R S_cls E))).fv ∪
        ((Class.cv (nb095AlphaDummy225 D R S_cls E))).fv)
      0

theorem nb095_fresh_305 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095AlphaDummy237 D R S_cls E) ∉
      (((Class.cv (nb095AlphaDummy225 D R S_cls E))).fv ∪
        ((Class.cv (nb095AlphaDummy225 D R S_cls E))).fv) :=
  by
  simpa only [nb095AlphaDummy237] using
    freshVar_not_mem
      (((Class.cv (nb095AlphaDummy225 D R S_cls E))).fv ∪
        ((Class.cv (nb095AlphaDummy225 D R S_cls E))).fv)
      0

theorem nb095_fresh_306 (f : Var) :
    (nb095AlphaDummy236 f) ∉
      (((Class.cv (nb095AlphaDummy227 f))).fv ∪ ((Class.cv (nb095AlphaDummy227 f))).fv) :=
  by
  simpa only [nb095AlphaDummy236] using
    freshVar_not_mem
      (((Class.cv (nb095AlphaDummy227 f))).fv ∪ ((Class.cv (nb095AlphaDummy227 f))).fv)
      0

theorem nb095_fresh_307 (f : Var) :
    (nb095AlphaDummy232 f) ∉
      (((Class.cv (nb095AlphaDummy227 f))).fv ∪ ((Class.cv (nb095AlphaDummy228 f))).fv) :=
  by
  simpa only [nb095AlphaDummy232] using
    freshVar_not_mem
      (((Class.cv (nb095AlphaDummy227 f))).fv ∪ ((Class.cv (nb095AlphaDummy228 f))).fv)
      0

theorem nb095_fresh_308 (f : Var) :
    (nb095AlphaDummy238 f) ∉
      (((Class.cv (nb095AlphaDummy228 f))).fv ∪ ((Class.cv (nb095AlphaDummy228 f))).fv) :=
  by
  simpa only [nb095AlphaDummy238] using
    freshVar_not_mem
      (((Class.cv (nb095AlphaDummy228 f))).fv ∪ ((Class.cv (nb095AlphaDummy228 f))).fv)
      0

theorem nb095_fresh_309 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095AlphaDummy255 D R S_cls E) ∉
      (((Class.cv (nb095AlphaDummy250 D R S_cls E))).fv ∪
        ((Class.cv (nb095AlphaDummy249 D R S_cls E))).fv) :=
  by
  simpa only [nb095AlphaDummy255] using
    freshVar_not_mem
      (((Class.cv (nb095AlphaDummy250 D R S_cls E))).fv ∪
        ((Class.cv (nb095AlphaDummy249 D R S_cls E))).fv)
      0

theorem nb095_fresh_310 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095AlphaDummy256 D R S_cls E) ∉
      (((Class.cv (nb095AlphaDummy250 D R S_cls E))).fv ∪
        ((Class.cv (nb095AlphaDummy249 D R S_cls E))).fv) :=
  by
  simpa only [nb095AlphaDummy256] using
    freshVar_not_mem
      (((Class.cv (nb095AlphaDummy250 D R S_cls E))).fv ∪
        ((Class.cv (nb095AlphaDummy249 D R S_cls E))).fv)
      1

theorem nb095_distinct_311 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095AlphaDummy255 D R S_cls E) ≠ (nb095AlphaDummy256 D R S_cls E) := by
  simpa only [nb095AlphaDummy255, nb095AlphaDummy256] using
    (freshVar_injective (((Class.cv (nb095AlphaDummy250 D R S_cls E))).fv ∪
        ((Class.cv (nb095AlphaDummy249 D R S_cls E))).fv) (i := 0) (j := 1) (by decide))

theorem nb095_fresh_312 (x : Var) (R : Class) :
    (nb095AlphaDummy257 x R) ∉
      (((Class.cv (nb095AlphaDummy252 x R))).fv ∪
        ((Class.cv (nb095AlphaDummy251 x R))).fv) :=
  by
  simpa only [nb095AlphaDummy257] using
    freshVar_not_mem
      (((Class.cv (nb095AlphaDummy252 x R))).fv ∪
        ((Class.cv (nb095AlphaDummy251 x R))).fv)
      0

theorem nb095_fresh_313 (x : Var) (R : Class) :
    (nb095AlphaDummy258 x R) ∉
      (((Class.cv (nb095AlphaDummy252 x R))).fv ∪
        ((Class.cv (nb095AlphaDummy251 x R))).fv) :=
  by
  simpa only [nb095AlphaDummy258] using
    freshVar_not_mem
      (((Class.cv (nb095AlphaDummy252 x R))).fv ∪
        ((Class.cv (nb095AlphaDummy251 x R))).fv)
      1

theorem nb095_distinct_314 (x : Var) (R : Class) :
    (nb095AlphaDummy257 x R) ≠ (nb095AlphaDummy258 x R) := by
  simpa only [nb095AlphaDummy257, nb095AlphaDummy258] using
    (freshVar_injective (((Class.cv (nb095AlphaDummy252 x R))).fv ∪
        ((Class.cv (nb095AlphaDummy251 x R))).fv) (i := 0) (j := 1) (by decide))

theorem nb095_fresh_315 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095AlphaDummy263 D R S_cls E) ∉
      (((Class.cv (nb095AlphaDummy256 D R S_cls E))).fv) :=
  by
  simpa only [nb095AlphaDummy263] using
    freshVar_not_mem (((Class.cv (nb095AlphaDummy256 D R S_cls E))).fv) 0

theorem nb095_fresh_316 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095AlphaDummy264 D R S_cls E) ∉
      (((Class.cv (nb095AlphaDummy256 D R S_cls E))).fv) :=
  by
  simpa only [nb095AlphaDummy264] using
    freshVar_not_mem (((Class.cv (nb095AlphaDummy256 D R S_cls E))).fv) 1

theorem nb095_distinct_317 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095AlphaDummy263 D R S_cls E) ≠ (nb095AlphaDummy264 D R S_cls E) := by
  simpa only [nb095AlphaDummy263, nb095AlphaDummy264] using
    (freshVar_injective (((Class.cv (nb095AlphaDummy256 D R S_cls E))).fv) (i := 0)
      (j := 1) (by decide))

theorem nb095_fresh_318 (x : Var) (R : Class) :
    (nb095AlphaDummy265 x R) ∉ (((Class.cv (nb095AlphaDummy258 x R))).fv) := by
  simpa only [nb095AlphaDummy265] using
    freshVar_not_mem (((Class.cv (nb095AlphaDummy258 x R))).fv) 0

theorem nb095_fresh_319 (x : Var) (R : Class) :
    (nb095AlphaDummy266 x R) ∉ (((Class.cv (nb095AlphaDummy258 x R))).fv) := by
  simpa only [nb095AlphaDummy266] using
    freshVar_not_mem (((Class.cv (nb095AlphaDummy258 x R))).fv) 1

theorem nb095_distinct_320 (x : Var) (R : Class) :
    (nb095AlphaDummy265 x R) ≠ (nb095AlphaDummy266 x R) := by
  simpa only [nb095AlphaDummy265, nb095AlphaDummy266] using
    (freshVar_injective (((Class.cv (nb095AlphaDummy258 x R))).fv) (i := 0) (j := 1)
      (by decide))

theorem nb095_fresh_321 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095AlphaDummy269 D R S_cls E) ∉
      (((Class.cv (nb095AlphaDummy263 D R S_cls E))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb095AlphaDummy269] using
    freshVar_not_mem
      (((Class.cv (nb095AlphaDummy263 D R S_cls E))).fv ∪ ((synC1c)).fv) 0

theorem nb095_fresh_322 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095AlphaDummy270 D R S_cls E) ∉
      (((Class.cv (nb095AlphaDummy263 D R S_cls E))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb095AlphaDummy270] using
    freshVar_not_mem
      (((Class.cv (nb095AlphaDummy263 D R S_cls E))).fv ∪ ((synC1c)).fv) 1

theorem nb095_fresh_323 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095AlphaDummy271 D R S_cls E) ∉
      (((Class.cv (nb095AlphaDummy263 D R S_cls E))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb095AlphaDummy271] using
    freshVar_not_mem
      (((Class.cv (nb095AlphaDummy263 D R S_cls E))).fv ∪ ((synC1c)).fv) 2

theorem nb095_distinct_324 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095AlphaDummy269 D R S_cls E) ≠ (nb095AlphaDummy270 D R S_cls E) := by
  simpa only [nb095AlphaDummy269, nb095AlphaDummy270] using
    (freshVar_injective
      (((Class.cv (nb095AlphaDummy263 D R S_cls E))).fv ∪ ((synC1c)).fv) (i := 0)
      (j := 1) (by decide))

theorem nb095_distinct_325 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095AlphaDummy269 D R S_cls E) ≠ (nb095AlphaDummy271 D R S_cls E) := by
  simpa only [nb095AlphaDummy269, nb095AlphaDummy271] using
    (freshVar_injective
      (((Class.cv (nb095AlphaDummy263 D R S_cls E))).fv ∪ ((synC1c)).fv) (i := 0)
      (j := 2) (by decide))

theorem nb095_distinct_326 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095AlphaDummy270 D R S_cls E) ≠ (nb095AlphaDummy271 D R S_cls E) := by
  simpa only [nb095AlphaDummy270, nb095AlphaDummy271] using
    (freshVar_injective
      (((Class.cv (nb095AlphaDummy263 D R S_cls E))).fv ∪ ((synC1c)).fv) (i := 1)
      (j := 2) (by decide))

theorem nb095_fresh_327 (x : Var) (R : Class) :
    (nb095AlphaDummy272 x R) ∉
      (((Class.cv (nb095AlphaDummy265 x R))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb095AlphaDummy272] using
    freshVar_not_mem (((Class.cv (nb095AlphaDummy265 x R))).fv ∪ ((synC1c)).fv) 0

theorem nb095_fresh_328 (x : Var) (R : Class) :
    (nb095AlphaDummy273 x R) ∉
      (((Class.cv (nb095AlphaDummy265 x R))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb095AlphaDummy273] using
    freshVar_not_mem (((Class.cv (nb095AlphaDummy265 x R))).fv ∪ ((synC1c)).fv) 1

theorem nb095_fresh_329 (x : Var) (R : Class) :
    (nb095AlphaDummy274 x R) ∉
      (((Class.cv (nb095AlphaDummy265 x R))).fv ∪ ((synC1c)).fv) :=
  by
  simpa only [nb095AlphaDummy274] using
    freshVar_not_mem (((Class.cv (nb095AlphaDummy265 x R))).fv ∪ ((synC1c)).fv) 2

theorem nb095_distinct_330 (x : Var) (R : Class) :
    (nb095AlphaDummy272 x R) ≠ (nb095AlphaDummy273 x R) := by
  simpa only [nb095AlphaDummy272, nb095AlphaDummy273] using
    (freshVar_injective (((Class.cv (nb095AlphaDummy265 x R))).fv ∪ ((synC1c)).fv)
      (i := 0) (j := 1) (by decide))

theorem nb095_distinct_331 (x : Var) (R : Class) :
    (nb095AlphaDummy272 x R) ≠ (nb095AlphaDummy274 x R) := by
  simpa only [nb095AlphaDummy272, nb095AlphaDummy274] using
    (freshVar_injective (((Class.cv (nb095AlphaDummy265 x R))).fv ∪ ((synC1c)).fv)
      (i := 0) (j := 2) (by decide))

theorem nb095_distinct_332 (x : Var) (R : Class) :
    (nb095AlphaDummy273 x R) ≠ (nb095AlphaDummy274 x R) := by
  simpa only [nb095AlphaDummy273, nb095AlphaDummy274] using
    (freshVar_injective (((Class.cv (nb095AlphaDummy265 x R))).fv ∪ ((synC1c)).fv)
      (i := 1) (j := 2) (by decide))

theorem nb095_fresh_333 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095AlphaDummy281 D R S_cls E) ∉
      (((Class.cv (nb095AlphaDummy270 D R S_cls E))).fv ∪
        ((Class.cv (nb095AlphaDummy270 D R S_cls E))).fv) :=
  by
  simpa only [nb095AlphaDummy281] using
    freshVar_not_mem
      (((Class.cv (nb095AlphaDummy270 D R S_cls E))).fv ∪
        ((Class.cv (nb095AlphaDummy270 D R S_cls E))).fv)
      0

theorem nb095_fresh_334 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095AlphaDummy277 D R S_cls E) ∉
      (((Class.cv (nb095AlphaDummy270 D R S_cls E))).fv ∪
        ((Class.cv (nb095AlphaDummy271 D R S_cls E))).fv) :=
  by
  simpa only [nb095AlphaDummy277] using
    freshVar_not_mem
      (((Class.cv (nb095AlphaDummy270 D R S_cls E))).fv ∪
        ((Class.cv (nb095AlphaDummy271 D R S_cls E))).fv)
      0

theorem nb095_fresh_335 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095AlphaDummy283 D R S_cls E) ∉
      (((Class.cv (nb095AlphaDummy271 D R S_cls E))).fv ∪
        ((Class.cv (nb095AlphaDummy271 D R S_cls E))).fv) :=
  by
  simpa only [nb095AlphaDummy283] using
    freshVar_not_mem
      (((Class.cv (nb095AlphaDummy271 D R S_cls E))).fv ∪
        ((Class.cv (nb095AlphaDummy271 D R S_cls E))).fv)
      0

theorem nb095_fresh_336 (x : Var) (R : Class) :
    (nb095AlphaDummy282 x R) ∉
      (((Class.cv (nb095AlphaDummy273 x R))).fv ∪
        ((Class.cv (nb095AlphaDummy273 x R))).fv) :=
  by
  simpa only [nb095AlphaDummy282] using
    freshVar_not_mem
      (((Class.cv (nb095AlphaDummy273 x R))).fv ∪
        ((Class.cv (nb095AlphaDummy273 x R))).fv)
      0

theorem nb095_fresh_337 (x : Var) (R : Class) :
    (nb095AlphaDummy278 x R) ∉
      (((Class.cv (nb095AlphaDummy273 x R))).fv ∪
        ((Class.cv (nb095AlphaDummy274 x R))).fv) :=
  by
  simpa only [nb095AlphaDummy278] using
    freshVar_not_mem
      (((Class.cv (nb095AlphaDummy273 x R))).fv ∪
        ((Class.cv (nb095AlphaDummy274 x R))).fv)
      0

theorem nb095_fresh_338 (x : Var) (R : Class) :
    (nb095AlphaDummy284 x R) ∉
      (((Class.cv (nb095AlphaDummy274 x R))).fv ∪
        ((Class.cv (nb095AlphaDummy274 x R))).fv) :=
  by
  simpa only [nb095AlphaDummy284] using
    freshVar_not_mem
      (((Class.cv (nb095AlphaDummy274 x R))).fv ∪
        ((Class.cv (nb095AlphaDummy274 x R))).fv)
      0

theorem nb095_fresh_339 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095AlphaDummy299 D R S_cls E) ∉
      (((Class.cv (nb095AlphaDummy296 D R S_cls E))).fv ∪
        ((Class.cv (nb095AlphaDummy295 D R S_cls E))).fv) :=
  by
  simpa only [nb095AlphaDummy299] using
    freshVar_not_mem
      (((Class.cv (nb095AlphaDummy296 D R S_cls E))).fv ∪
        ((Class.cv (nb095AlphaDummy295 D R S_cls E))).fv)
      0

theorem nb095_fresh_340 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095AlphaDummy300 D R S_cls E) ∉
      (((Class.cv (nb095AlphaDummy296 D R S_cls E))).fv ∪
        ((Class.cv (nb095AlphaDummy295 D R S_cls E))).fv) :=
  by
  simpa only [nb095AlphaDummy300] using
    freshVar_not_mem
      (((Class.cv (nb095AlphaDummy296 D R S_cls E))).fv ∪
        ((Class.cv (nb095AlphaDummy295 D R S_cls E))).fv)
      1

theorem nb095_distinct_341 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095AlphaDummy299 D R S_cls E) ≠ (nb095AlphaDummy300 D R S_cls E) := by
  simpa only [nb095AlphaDummy299, nb095AlphaDummy300] using
    (freshVar_injective (((Class.cv (nb095AlphaDummy296 D R S_cls E))).fv ∪
        ((Class.cv (nb095AlphaDummy295 D R S_cls E))).fv) (i := 0) (j := 1) (by decide))

theorem nb095_fresh_342 (f : Var) :
    (nb095AlphaDummy301 f) ∉
      (((Class.cv (nb095AlphaDummy298 f))).fv ∪ ((Class.cv (nb095AlphaDummy297 f))).fv) :=
  by
  simpa only [nb095AlphaDummy301] using
    freshVar_not_mem
      (((Class.cv (nb095AlphaDummy298 f))).fv ∪ ((Class.cv (nb095AlphaDummy297 f))).fv)
      0

theorem nb095_fresh_343 (f : Var) :
    (nb095AlphaDummy302 f) ∉
      (((Class.cv (nb095AlphaDummy298 f))).fv ∪ ((Class.cv (nb095AlphaDummy297 f))).fv) :=
  by
  simpa only [nb095AlphaDummy302] using
    freshVar_not_mem
      (((Class.cv (nb095AlphaDummy298 f))).fv ∪ ((Class.cv (nb095AlphaDummy297 f))).fv)
      1

theorem nb095_distinct_344 (f : Var) :
    (nb095AlphaDummy301 f) ≠ (nb095AlphaDummy302 f) := by
  simpa only [nb095AlphaDummy301, nb095AlphaDummy302] using
    (freshVar_injective (((Class.cv (nb095AlphaDummy298 f))).fv ∪
        ((Class.cv (nb095AlphaDummy297 f))).fv) (i := 0) (j := 1) (by decide))

theorem nb095_fresh_345 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095AlphaDummy307 D R S_cls E) ∉
      (((Class.cv (nb095AlphaDummy300 D R S_cls E))).fv) :=
  by
  simpa only [nb095AlphaDummy307] using
    freshVar_not_mem (((Class.cv (nb095AlphaDummy300 D R S_cls E))).fv) 0

theorem nb095_fresh_346 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095AlphaDummy308 D R S_cls E) ∉
      (((Class.cv (nb095AlphaDummy300 D R S_cls E))).fv) :=
  by
  simpa only [nb095AlphaDummy308] using
    freshVar_not_mem (((Class.cv (nb095AlphaDummy300 D R S_cls E))).fv) 1

theorem nb095_distinct_347 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095AlphaDummy307 D R S_cls E) ≠ (nb095AlphaDummy308 D R S_cls E) := by
  simpa only [nb095AlphaDummy307, nb095AlphaDummy308] using
    (freshVar_injective (((Class.cv (nb095AlphaDummy300 D R S_cls E))).fv) (i := 0)
      (j := 1) (by decide))

theorem nb095_fresh_348 (f : Var) :
    (nb095AlphaDummy309 f) ∉ (((Class.cv (nb095AlphaDummy302 f))).fv) := by
  simpa only [nb095AlphaDummy309] using
    freshVar_not_mem (((Class.cv (nb095AlphaDummy302 f))).fv) 0

end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired
