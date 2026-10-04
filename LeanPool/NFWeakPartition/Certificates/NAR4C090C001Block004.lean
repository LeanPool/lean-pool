/-
Copyright (c) 2026 Elliot Glazer and NFNotWPP contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elliot Glazer and NFNotWPP contributors
-/

module

public import LeanPool.NFWeakPartition.Certificates.NAR4C090C001Block003

/-! Nominal proof certificates grouped in dependency order. -/


public section

/-! Certificates from `NAR4C090C001Part014`. -/


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

theorem nb090_fresh_922 (A : Class) :
    (nb090AlphaDummy271 A) ∉
      (((synCcompl (Class.cv (nb090AlphaDummy262 A)))).fv ∪
        ((synCcompl (Class.cv (nb090AlphaDummy263 A)))).fv) :=
  by
  simpa only [nb090AlphaDummy271] using
    freshVar_not_mem
      (((synCcompl (Class.cv (nb090AlphaDummy262 A)))).fv ∪
        ((synCcompl (Class.cv (nb090AlphaDummy263 A)))).fv)
      0

theorem nb090_fresh_923 (h : Var) :
    (nb090AlphaDummy272 h) ∉
      (((synCcompl (Class.cv (nb090AlphaDummy265 h)))).fv ∪
        ((synCcompl (Class.cv (nb090AlphaDummy266 h)))).fv) :=
  by
  simpa only [nb090AlphaDummy272] using
    freshVar_not_mem
      (((synCcompl (Class.cv (nb090AlphaDummy265 h)))).fv ∪
        ((synCcompl (Class.cv (nb090AlphaDummy266 h)))).fv)
      0

theorem nb090_fresh_924 (A : Class) :
    (nb090AlphaDummy315 A) ∉
      (((synCcompl (Class.cv (nb090AlphaDummy306 A)))).fv ∪
        ((synCcompl (Class.cv (nb090AlphaDummy307 A)))).fv) :=
  by
  simpa only [nb090AlphaDummy315] using
    freshVar_not_mem
      (((synCcompl (Class.cv (nb090AlphaDummy306 A)))).fv ∪
        ((synCcompl (Class.cv (nb090AlphaDummy307 A)))).fv)
      0

theorem nb090_fresh_925 (u : Var) :
    (nb090AlphaDummy316 u) ∉
      (((synCcompl (Class.cv (nb090AlphaDummy309 u)))).fv ∪
        ((synCcompl (Class.cv (nb090AlphaDummy310 u)))).fv) :=
  by
  simpa only [nb090AlphaDummy316] using
    freshVar_not_mem
      (((synCcompl (Class.cv (nb090AlphaDummy309 u)))).fv ∪
        ((synCcompl (Class.cv (nb090AlphaDummy310 u)))).fv)
      0

theorem nb090_fresh_926 (A : Class) :
    (nb090AlphaDummy361 A) ∉
      (((synCcompl (Class.cv (nb090AlphaDummy352 A)))).fv ∪
        ((synCcompl (Class.cv (nb090AlphaDummy353 A)))).fv) :=
  by
  simpa only [nb090AlphaDummy361] using
    freshVar_not_mem
      (((synCcompl (Class.cv (nb090AlphaDummy352 A)))).fv ∪
        ((synCcompl (Class.cv (nb090AlphaDummy353 A)))).fv)
      0

theorem nb090_fresh_927 (h : Var) :
    (nb090AlphaDummy362 h) ∉
      (((synCcompl (Class.cv (nb090AlphaDummy355 h)))).fv ∪
        ((synCcompl (Class.cv (nb090AlphaDummy356 h)))).fv) :=
  by
  simpa only [nb090AlphaDummy362] using
    freshVar_not_mem
      (((synCcompl (Class.cv (nb090AlphaDummy355 h)))).fv ∪
        ((synCcompl (Class.cv (nb090AlphaDummy356 h)))).fv)
      0

theorem nb090_fresh_928 (A : Class) :
    (nb090AlphaDummy405 A) ∉
      (((synCcompl (Class.cv (nb090AlphaDummy396 A)))).fv ∪
        ((synCcompl (Class.cv (nb090AlphaDummy397 A)))).fv) :=
  by
  simpa only [nb090AlphaDummy405] using
    freshVar_not_mem
      (((synCcompl (Class.cv (nb090AlphaDummy396 A)))).fv ∪
        ((synCcompl (Class.cv (nb090AlphaDummy397 A)))).fv)
      0

theorem nb090_fresh_929 (v : Var) :
    (nb090AlphaDummy406 v) ∉
      (((synCcompl (Class.cv (nb090AlphaDummy399 v)))).fv ∪
        ((synCcompl (Class.cv (nb090AlphaDummy400 v)))).fv) :=
  by
  simpa only [nb090AlphaDummy406] using
    freshVar_not_mem
      (((synCcompl (Class.cv (nb090AlphaDummy399 v)))).fv ∪
        ((synCcompl (Class.cv (nb090AlphaDummy400 v)))).fv)
      0

theorem nb090_fresh_930 (A : Class) :
    (nb090AlphaDummy455 A) ∉
      (((synCcompl (Class.cv (nb090AlphaDummy446 A)))).fv ∪
        ((synCcompl (Class.cv (nb090AlphaDummy447 A)))).fv) :=
  by
  simpa only [nb090AlphaDummy455] using
    freshVar_not_mem
      (((synCcompl (Class.cv (nb090AlphaDummy446 A)))).fv ∪
        ((synCcompl (Class.cv (nb090AlphaDummy447 A)))).fv)
      0

theorem nb090_fresh_931 (h : Var) :
    (nb090AlphaDummy456 h) ∉
      (((synCcompl (Class.cv (nb090AlphaDummy449 h)))).fv ∪
        ((synCcompl (Class.cv (nb090AlphaDummy450 h)))).fv) :=
  by
  simpa only [nb090AlphaDummy456] using
    freshVar_not_mem
      (((synCcompl (Class.cv (nb090AlphaDummy449 h)))).fv ∪
        ((synCcompl (Class.cv (nb090AlphaDummy450 h)))).fv)
      0

theorem nb090_fresh_932 (A : Class) :
    (nb090AlphaDummy491 A) ∉
      (((synCcompl (Class.cv (nb090AlphaDummy482 A)))).fv ∪
        ((synCcompl (Class.cv (nb090AlphaDummy483 A)))).fv) :=
  by
  simpa only [nb090AlphaDummy491] using
    freshVar_not_mem
      (((synCcompl (Class.cv (nb090AlphaDummy482 A)))).fv ∪
        ((synCcompl (Class.cv (nb090AlphaDummy483 A)))).fv)
      0

theorem nb090_fresh_933 (h : Var) :
    (nb090AlphaDummy492 h) ∉
      (((synCcompl (Class.cv (nb090AlphaDummy485 h)))).fv ∪
        ((synCcompl (Class.cv (nb090AlphaDummy486 h)))).fv) :=
  by
  simpa only [nb090AlphaDummy492] using
    freshVar_not_mem
      (((synCcompl (Class.cv (nb090AlphaDummy485 h)))).fv ∪
        ((synCcompl (Class.cv (nb090AlphaDummy486 h)))).fv)
      0

theorem nb090_fresh_934 (A : Class) :
    (nb090AlphaDummy533 A) ∉
      (((synCcompl (Class.cv (nb090AlphaDummy524 A)))).fv ∪
        ((synCcompl (Class.cv (nb090AlphaDummy525 A)))).fv) :=
  by
  simpa only [nb090AlphaDummy533] using
    freshVar_not_mem
      (((synCcompl (Class.cv (nb090AlphaDummy524 A)))).fv ∪
        ((synCcompl (Class.cv (nb090AlphaDummy525 A)))).fv)
      0

theorem nb090_fresh_935 (h : Var) :
    (nb090AlphaDummy534 h) ∉
      (((synCcompl (Class.cv (nb090AlphaDummy527 h)))).fv ∪
        ((synCcompl (Class.cv (nb090AlphaDummy528 h)))).fv) :=
  by
  simpa only [nb090AlphaDummy534] using
    freshVar_not_mem
      (((synCcompl (Class.cv (nb090AlphaDummy527 h)))).fv ∪
        ((synCcompl (Class.cv (nb090AlphaDummy528 h)))).fv)
      0

theorem nb090_fresh_936 (A : Class) :
    (nb090AlphaDummy569 A) ∉
      (((synCcompl (Class.cv (nb090AlphaDummy560 A)))).fv ∪
        ((synCcompl (Class.cv (nb090AlphaDummy561 A)))).fv) :=
  by
  simpa only [nb090AlphaDummy569] using
    freshVar_not_mem
      (((synCcompl (Class.cv (nb090AlphaDummy560 A)))).fv ∪
        ((synCcompl (Class.cv (nb090AlphaDummy561 A)))).fv)
      0

theorem nb090_fresh_937 (h : Var) :
    (nb090AlphaDummy570 h) ∉
      (((synCcompl (Class.cv (nb090AlphaDummy563 h)))).fv ∪
        ((synCcompl (Class.cv (nb090AlphaDummy564 h)))).fv) :=
  by
  simpa only [nb090AlphaDummy570] using
    freshVar_not_mem
      (((synCcompl (Class.cv (nb090AlphaDummy563 h)))).fv ∪
        ((synCcompl (Class.cv (nb090AlphaDummy564 h)))).fv)
      0

theorem nb090_fresh_938 (A : Class) :
    (nb090AlphaDummy605 A) ∉
      (((synCcompl (Class.cv (nb090AlphaDummy596 A)))).fv ∪
        ((synCcompl (Class.cv (nb090AlphaDummy597 A)))).fv) :=
  by
  simpa only [nb090AlphaDummy605] using
    freshVar_not_mem
      (((synCcompl (Class.cv (nb090AlphaDummy596 A)))).fv ∪
        ((synCcompl (Class.cv (nb090AlphaDummy597 A)))).fv)
      0

theorem nb090_fresh_939 (h : Var) :
    (nb090AlphaDummy606 h) ∉
      (((synCcompl (Class.cv (nb090AlphaDummy599 h)))).fv ∪
        ((synCcompl (Class.cv (nb090AlphaDummy600 h)))).fv) :=
  by
  simpa only [nb090AlphaDummy606] using
    freshVar_not_mem
      (((synCcompl (Class.cv (nb090AlphaDummy599 h)))).fv ∪
        ((synCcompl (Class.cv (nb090AlphaDummy600 h)))).fv)
      0

theorem nb090_fresh_940 (A : Class) :
    (nb090AlphaDummy641 A) ∉
      (((synCcompl (Class.cv (nb090AlphaDummy632 A)))).fv ∪
        ((synCcompl (Class.cv (nb090AlphaDummy633 A)))).fv) :=
  by
  simpa only [nb090AlphaDummy641] using
    freshVar_not_mem
      (((synCcompl (Class.cv (nb090AlphaDummy632 A)))).fv ∪
        ((synCcompl (Class.cv (nb090AlphaDummy633 A)))).fv)
      0

theorem nb090_fresh_941 (v : Var) (u : Var) (h : Var) :
    (nb090AlphaDummy642 v u h) ∉
      (((synCcompl (Class.cv (nb090AlphaDummy635 v u h)))).fv ∪
        ((synCcompl (Class.cv (nb090AlphaDummy636 v u h)))).fv) :=
  by
  simpa only [nb090AlphaDummy642] using
    freshVar_not_mem
      (((synCcompl (Class.cv (nb090AlphaDummy635 v u h)))).fv ∪
        ((synCcompl (Class.cv (nb090AlphaDummy636 v u h)))).fv)
      0

theorem nb090_fresh_942 (A : Class) :
    (nb090AlphaDummy685 A) ∉
      (((synCcompl (Class.cv (nb090AlphaDummy676 A)))).fv ∪
        ((synCcompl (Class.cv (nb090AlphaDummy677 A)))).fv) :=
  by
  simpa only [nb090AlphaDummy685] using
    freshVar_not_mem
      (((synCcompl (Class.cv (nb090AlphaDummy676 A)))).fv ∪
        ((synCcompl (Class.cv (nb090AlphaDummy677 A)))).fv)
      0

theorem nb090_fresh_943 (u : Var) :
    (nb090AlphaDummy686 u) ∉
      (((synCcompl (Class.cv (nb090AlphaDummy679 u)))).fv ∪
        ((synCcompl (Class.cv (nb090AlphaDummy680 u)))).fv) :=
  by
  simpa only [nb090AlphaDummy686] using
    freshVar_not_mem
      (((synCcompl (Class.cv (nb090AlphaDummy679 u)))).fv ∪
        ((synCcompl (Class.cv (nb090AlphaDummy680 u)))).fv)
      0

theorem nb090_fresh_944 (A : Class) :
    (nb090AlphaDummy739 A) ∉
      (((synCcompl (Class.cv (nb090AlphaDummy730 A)))).fv ∪
        ((synCcompl (Class.cv (nb090AlphaDummy731 A)))).fv) :=
  by
  simpa only [nb090AlphaDummy739] using
    freshVar_not_mem
      (((synCcompl (Class.cv (nb090AlphaDummy730 A)))).fv ∪
        ((synCcompl (Class.cv (nb090AlphaDummy731 A)))).fv)
      0

theorem nb090_fresh_945 (v : Var) (u : Var) (h : Var) :
    (nb090AlphaDummy740 v u h) ∉
      (((synCcompl (Class.cv (nb090AlphaDummy733 v u h)))).fv ∪
        ((synCcompl (Class.cv (nb090AlphaDummy734 v u h)))).fv) :=
  by
  simpa only [nb090AlphaDummy740] using
    freshVar_not_mem
      (((synCcompl (Class.cv (nb090AlphaDummy733 v u h)))).fv ∪
        ((synCcompl (Class.cv (nb090AlphaDummy734 v u h)))).fv)
      0

theorem nb090_fresh_946 (A : Class) :
    (nb090AlphaDummy769 A) ∉
      (((synCcompl (Class.cv (nb090AlphaDummy760 A)))).fv ∪
        ((synCcompl (Class.cv (nb090AlphaDummy761 A)))).fv) :=
  by
  simpa only [nb090AlphaDummy769] using
    freshVar_not_mem
      (((synCcompl (Class.cv (nb090AlphaDummy760 A)))).fv ∪
        ((synCcompl (Class.cv (nb090AlphaDummy761 A)))).fv)
      0

theorem nb090_fresh_947 (v : Var) (u : Var) (h : Var) :
    (nb090AlphaDummy770 v u h) ∉
      (((synCcompl (Class.cv (nb090AlphaDummy763 v u h)))).fv ∪
        ((synCcompl (Class.cv (nb090AlphaDummy764 v u h)))).fv) :=
  by
  simpa only [nb090AlphaDummy770] using
    freshVar_not_mem
      (((synCcompl (Class.cv (nb090AlphaDummy763 v u h)))).fv ∪
        ((synCcompl (Class.cv (nb090AlphaDummy764 v u h)))).fv)
      0

theorem nb090_fresh_948 (A : Class) :
    (nb090AlphaDummy809 A) ∉
      (((synCcompl (Class.cv (nb090AlphaDummy800 A)))).fv ∪
        ((synCcompl (Class.cv (nb090AlphaDummy801 A)))).fv) :=
  by
  simpa only [nb090AlphaDummy809] using
    freshVar_not_mem
      (((synCcompl (Class.cv (nb090AlphaDummy800 A)))).fv ∪
        ((synCcompl (Class.cv (nb090AlphaDummy801 A)))).fv)
      0

theorem nb090_fresh_949 (v : Var) (u : Var) (h : Var) :
    (nb090AlphaDummy810 v u h) ∉
      (((synCcompl (Class.cv (nb090AlphaDummy803 v u h)))).fv ∪
        ((synCcompl (Class.cv (nb090AlphaDummy804 v u h)))).fv) :=
  by
  simpa only [nb090AlphaDummy810] using
    freshVar_not_mem
      (((synCcompl (Class.cv (nb090AlphaDummy803 v u h)))).fv ∪
        ((synCcompl (Class.cv (nb090AlphaDummy804 v u h)))).fv)
      0

theorem nb090_fresh_950 (A : Class) :
    (nb090AlphaDummy859 A) ∉
      (((synCcompl (Class.cv (nb090AlphaDummy850 A)))).fv ∪
        ((synCcompl (Class.cv (nb090AlphaDummy851 A)))).fv) :=
  by
  simpa only [nb090AlphaDummy859] using
    freshVar_not_mem
      (((synCcompl (Class.cv (nb090AlphaDummy850 A)))).fv ∪
        ((synCcompl (Class.cv (nb090AlphaDummy851 A)))).fv)
      0

theorem nb090_fresh_951 (v : Var) :
    (nb090AlphaDummy860 v) ∉
      (((synCcompl (Class.cv (nb090AlphaDummy853 v)))).fv ∪
        ((synCcompl (Class.cv (nb090AlphaDummy854 v)))).fv) :=
  by
  simpa only [nb090AlphaDummy860] using
    freshVar_not_mem
      (((synCcompl (Class.cv (nb090AlphaDummy853 v)))).fv ∪
        ((synCcompl (Class.cv (nb090AlphaDummy854 v)))).fv)
      0

theorem nb090_fresh_952 (A : Class) :
    (nb090AlphaDummy037 A) ∉
      (((synCcompl (synCphi (Class.cv (nb090AlphaDummy006 A))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv) :=
  by
  simpa only [nb090AlphaDummy037] using
    freshVar_not_mem
      (((synCcompl (synCphi (Class.cv (nb090AlphaDummy006 A))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv)
      0

theorem nb090_fresh_953 (v : Var) (u : Var) :
    (nb090AlphaDummy038 v u) ∉
      (((synCcompl (synCphi (Class.cv (nb090AlphaDummy008 v u))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv) :=
  by
  simpa only [nb090AlphaDummy038] using
    freshVar_not_mem
      (((synCcompl (synCphi (Class.cv (nb090AlphaDummy008 v u))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv)
      0

theorem nb090_fresh_954 (A : Class) :
    (nb090AlphaDummy089 A) ∉
      (((synCcompl (synCphi (Class.cv (nb090AlphaDummy058 A))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv) :=
  by
  simpa only [nb090AlphaDummy089] using
    freshVar_not_mem
      (((synCcompl (synCphi (Class.cv (nb090AlphaDummy058 A))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv)
      0

theorem nb090_fresh_955 (h : Var) :
    (nb090AlphaDummy090 h) ∉
      (((synCcompl (synCphi (Class.cv (nb090AlphaDummy060 h))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv) :=
  by
  simpa only [nb090AlphaDummy090] using
    freshVar_not_mem
      (((synCcompl (synCphi (Class.cv (nb090AlphaDummy060 h))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv)
      0

theorem nb090_fresh_956 (A : Class) :
    (nb090AlphaDummy125 A) ∉
      (((synCcompl (synCphi (Class.cv (nb090AlphaDummy094 A))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv) :=
  by
  simpa only [nb090AlphaDummy125] using
    freshVar_not_mem
      (((synCcompl (synCphi (Class.cv (nb090AlphaDummy094 A))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv)
      0

theorem nb090_fresh_957 (h : Var) :
    (nb090AlphaDummy126 h) ∉
      (((synCcompl (synCphi (Class.cv (nb090AlphaDummy096 h))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv) :=
  by
  simpa only [nb090AlphaDummy126] using
    freshVar_not_mem
      (((synCcompl (synCphi (Class.cv (nb090AlphaDummy096 h))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv)
      0

theorem nb090_fresh_958 (A : Class) :
    (nb090AlphaDummy167 A) ∉
      (((synCcompl (synCphi (Class.cv (nb090AlphaDummy136 A))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv) :=
  by
  simpa only [nb090AlphaDummy167] using
    freshVar_not_mem
      (((synCcompl (synCphi (Class.cv (nb090AlphaDummy136 A))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv)
      0

theorem nb090_fresh_959 (h : Var) :
    (nb090AlphaDummy168 h) ∉
      (((synCcompl (synCphi (Class.cv (nb090AlphaDummy138 h))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv) :=
  by
  simpa only [nb090AlphaDummy168] using
    freshVar_not_mem
      (((synCcompl (synCphi (Class.cv (nb090AlphaDummy138 h))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv)
      0

theorem nb090_fresh_960 (A : Class) :
    (nb090AlphaDummy203 A) ∉
      (((synCcompl (synCphi (Class.cv (nb090AlphaDummy172 A))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv) :=
  by
  simpa only [nb090AlphaDummy203] using
    freshVar_not_mem
      (((synCcompl (synCphi (Class.cv (nb090AlphaDummy172 A))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv)
      0

theorem nb090_fresh_961 (h : Var) :
    (nb090AlphaDummy204 h) ∉
      (((synCcompl (synCphi (Class.cv (nb090AlphaDummy174 h))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv) :=
  by
  simpa only [nb090AlphaDummy204] using
    freshVar_not_mem
      (((synCcompl (synCphi (Class.cv (nb090AlphaDummy174 h))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv)
      0

theorem nb090_fresh_962 (A : Class) :
    (nb090AlphaDummy239 A) ∉
      (((synCcompl (synCphi (Class.cv (nb090AlphaDummy208 A))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv) :=
  by
  simpa only [nb090AlphaDummy239] using
    freshVar_not_mem
      (((synCcompl (synCphi (Class.cv (nb090AlphaDummy208 A))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv)
      0

theorem nb090_fresh_963 (h : Var) :
    (nb090AlphaDummy240 h) ∉
      (((synCcompl (synCphi (Class.cv (nb090AlphaDummy210 h))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv) :=
  by
  simpa only [nb090AlphaDummy240] using
    freshVar_not_mem
      (((synCcompl (synCphi (Class.cv (nb090AlphaDummy210 h))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv)
      0

theorem nb090_fresh_964 (A : Class) :
    (nb090AlphaDummy279 A) ∉
      (((synCcompl (synCphi (Class.cv (nb090AlphaDummy248 A))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv) :=
  by
  simpa only [nb090AlphaDummy279] using
    freshVar_not_mem
      (((synCcompl (synCphi (Class.cv (nb090AlphaDummy248 A))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv)
      0

theorem nb090_fresh_965 (h : Var) :
    (nb090AlphaDummy280 h) ∉
      (((synCcompl (synCphi (Class.cv (nb090AlphaDummy250 h))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv) :=
  by
  simpa only [nb090AlphaDummy280] using
    freshVar_not_mem
      (((synCcompl (synCphi (Class.cv (nb090AlphaDummy250 h))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv)
      0

theorem nb090_fresh_966 (A : Class) :
    (nb090AlphaDummy323 A) ∉
      (((synCcompl (synCphi (Class.cv (nb090AlphaDummy292 A))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv) :=
  by
  simpa only [nb090AlphaDummy323] using
    freshVar_not_mem
      (((synCcompl (synCphi (Class.cv (nb090AlphaDummy292 A))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv)
      0

theorem nb090_fresh_967 (u : Var) :
    (nb090AlphaDummy324 u) ∉
      (((synCcompl (synCphi (Class.cv (nb090AlphaDummy294 u))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv) :=
  by
  simpa only [nb090AlphaDummy324] using
    freshVar_not_mem
      (((synCcompl (synCphi (Class.cv (nb090AlphaDummy294 u))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv)
      0

theorem nb090_fresh_968 (A : Class) :
    (nb090AlphaDummy369 A) ∉
      (((synCcompl (synCphi (Class.cv (nb090AlphaDummy338 A))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv) :=
  by
  simpa only [nb090AlphaDummy369] using
    freshVar_not_mem
      (((synCcompl (synCphi (Class.cv (nb090AlphaDummy338 A))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv)
      0

theorem nb090_fresh_969 (h : Var) :
    (nb090AlphaDummy370 h) ∉
      (((synCcompl (synCphi (Class.cv (nb090AlphaDummy340 h))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv) :=
  by
  simpa only [nb090AlphaDummy370] using
    freshVar_not_mem
      (((synCcompl (synCphi (Class.cv (nb090AlphaDummy340 h))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv)
      0

theorem nb090_fresh_970 (A : Class) :
    (nb090AlphaDummy413 A) ∉
      (((synCcompl (synCphi (Class.cv (nb090AlphaDummy382 A))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv) :=
  by
  simpa only [nb090AlphaDummy413] using
    freshVar_not_mem
      (((synCcompl (synCphi (Class.cv (nb090AlphaDummy382 A))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv)
      0

theorem nb090_fresh_971 (v : Var) :
    (nb090AlphaDummy414 v) ∉
      (((synCcompl (synCphi (Class.cv (nb090AlphaDummy384 v))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv) :=
  by
  simpa only [nb090AlphaDummy414] using
    freshVar_not_mem
      (((synCcompl (synCphi (Class.cv (nb090AlphaDummy384 v))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv)
      0

theorem nb090_fresh_972 (A : Class) :
    (nb090AlphaDummy463 A) ∉
      (((synCcompl (synCphi (Class.cv (nb090AlphaDummy432 A))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv) :=
  by
  simpa only [nb090AlphaDummy463] using
    freshVar_not_mem
      (((synCcompl (synCphi (Class.cv (nb090AlphaDummy432 A))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv)
      0

theorem nb090_fresh_973 (h : Var) :
    (nb090AlphaDummy464 h) ∉
      (((synCcompl (synCphi (Class.cv (nb090AlphaDummy434 h))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv) :=
  by
  simpa only [nb090AlphaDummy464] using
    freshVar_not_mem
      (((synCcompl (synCphi (Class.cv (nb090AlphaDummy434 h))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv)
      0

theorem nb090_fresh_974 (A : Class) :
    (nb090AlphaDummy499 A) ∉
      (((synCcompl (synCphi (Class.cv (nb090AlphaDummy468 A))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv) :=
  by
  simpa only [nb090AlphaDummy499] using
    freshVar_not_mem
      (((synCcompl (synCphi (Class.cv (nb090AlphaDummy468 A))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv)
      0

theorem nb090_fresh_975 (h : Var) :
    (nb090AlphaDummy500 h) ∉
      (((synCcompl (synCphi (Class.cv (nb090AlphaDummy470 h))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv) :=
  by
  simpa only [nb090AlphaDummy500] using
    freshVar_not_mem
      (((synCcompl (synCphi (Class.cv (nb090AlphaDummy470 h))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv)
      0

theorem nb090_fresh_976 (A : Class) :
    (nb090AlphaDummy541 A) ∉
      (((synCcompl (synCphi (Class.cv (nb090AlphaDummy510 A))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv) :=
  by
  simpa only [nb090AlphaDummy541] using
    freshVar_not_mem
      (((synCcompl (synCphi (Class.cv (nb090AlphaDummy510 A))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv)
      0

theorem nb090_fresh_977 (h : Var) :
    (nb090AlphaDummy542 h) ∉
      (((synCcompl (synCphi (Class.cv (nb090AlphaDummy512 h))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv) :=
  by
  simpa only [nb090AlphaDummy542] using
    freshVar_not_mem
      (((synCcompl (synCphi (Class.cv (nb090AlphaDummy512 h))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv)
      0

theorem nb090_fresh_978 (A : Class) :
    (nb090AlphaDummy577 A) ∉
      (((synCcompl (synCphi (Class.cv (nb090AlphaDummy546 A))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv) :=
  by
  simpa only [nb090AlphaDummy577] using
    freshVar_not_mem
      (((synCcompl (synCphi (Class.cv (nb090AlphaDummy546 A))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv)
      0

theorem nb090_fresh_979 (h : Var) :
    (nb090AlphaDummy578 h) ∉
      (((synCcompl (synCphi (Class.cv (nb090AlphaDummy548 h))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv) :=
  by
  simpa only [nb090AlphaDummy578] using
    freshVar_not_mem
      (((synCcompl (synCphi (Class.cv (nb090AlphaDummy548 h))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv)
      0

theorem nb090_fresh_980 (A : Class) :
    (nb090AlphaDummy613 A) ∉
      (((synCcompl (synCphi (Class.cv (nb090AlphaDummy582 A))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv) :=
  by
  simpa only [nb090AlphaDummy613] using
    freshVar_not_mem
      (((synCcompl (synCphi (Class.cv (nb090AlphaDummy582 A))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv)
      0

theorem nb090_fresh_981 (h : Var) :
    (nb090AlphaDummy614 h) ∉
      (((synCcompl (synCphi (Class.cv (nb090AlphaDummy584 h))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv) :=
  by
  simpa only [nb090AlphaDummy614] using
    freshVar_not_mem
      (((synCcompl (synCphi (Class.cv (nb090AlphaDummy584 h))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv)
      0

theorem nb090_fresh_982 (A : Class) :
    (nb090AlphaDummy649 A) ∉
      (((synCcompl (synCphi (Class.cv (nb090AlphaDummy618 A))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv) :=
  by
  simpa only [nb090AlphaDummy649] using
    freshVar_not_mem
      (((synCcompl (synCphi (Class.cv (nb090AlphaDummy618 A))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv)
      0

theorem nb090_fresh_983 (v : Var) (u : Var) (h : Var) :
    (nb090AlphaDummy650 v u h) ∉
      (((synCcompl (synCphi (Class.cv (nb090AlphaDummy620 v u h))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv) :=
  by
  simpa only [nb090AlphaDummy650] using
    freshVar_not_mem
      (((synCcompl (synCphi (Class.cv (nb090AlphaDummy620 v u h))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv)
      0

theorem nb090_fresh_984 (A : Class) :
    (nb090AlphaDummy693 A) ∉
      (((synCcompl (synCphi (Class.cv (nb090AlphaDummy662 A))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv) :=
  by
  simpa only [nb090AlphaDummy693] using
    freshVar_not_mem
      (((synCcompl (synCphi (Class.cv (nb090AlphaDummy662 A))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv)
      0

theorem nb090_fresh_985 (u : Var) :
    (nb090AlphaDummy694 u) ∉
      (((synCcompl (synCphi (Class.cv (nb090AlphaDummy664 u))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv) :=
  by
  simpa only [nb090AlphaDummy694] using
    freshVar_not_mem
      (((synCcompl (synCphi (Class.cv (nb090AlphaDummy664 u))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv)
      0

theorem nb090_fresh_986 (A : Class) :
    (nb090AlphaDummy823 A) ∉
      (((synCcompl (synCphi (Class.cv (nb090AlphaDummy700 A))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv) :=
  by
  simpa only [nb090AlphaDummy823] using
    freshVar_not_mem
      (((synCcompl (synCphi (Class.cv (nb090AlphaDummy700 A))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv)
      0

theorem nb090_fresh_987 (v : Var) (u : Var) (h : Var) :
    (nb090AlphaDummy824 v u h) ∉
      (((synCcompl (synCphi (Class.cv (nb090AlphaDummy702 v u h))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv) :=
  by
  simpa only [nb090AlphaDummy824] using
    freshVar_not_mem
      (((synCcompl (synCphi (Class.cv (nb090AlphaDummy702 v u h))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv)
      0

theorem nb090_fresh_988 (A : Class) :
    (nb090AlphaDummy747 A) ∉
      (((synCcompl (synCphi (Class.cv (nb090AlphaDummy716 A))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv) :=
  by
  simpa only [nb090AlphaDummy747] using
    freshVar_not_mem
      (((synCcompl (synCphi (Class.cv (nb090AlphaDummy716 A))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv)
      0

theorem nb090_fresh_989 (v : Var) (u : Var) (h : Var) :
    (nb090AlphaDummy748 v u h) ∉
      (((synCcompl (synCphi (Class.cv (nb090AlphaDummy718 v u h))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv) :=
  by
  simpa only [nb090AlphaDummy748] using
    freshVar_not_mem
      (((synCcompl (synCphi (Class.cv (nb090AlphaDummy718 v u h))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv)
      0

theorem nb090_fresh_990 (A : Class) :
    (nb090AlphaDummy817 A) ∉
      (((synCcompl (synCphi (Class.cv (nb090AlphaDummy786 A))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv) :=
  by
  simpa only [nb090AlphaDummy817] using
    freshVar_not_mem
      (((synCcompl (synCphi (Class.cv (nb090AlphaDummy786 A))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv)
      0

theorem nb090_fresh_991 (v : Var) (u : Var) (h : Var) :
    (nb090AlphaDummy818 v u h) ∉
      (((synCcompl (synCphi (Class.cv (nb090AlphaDummy788 v u h))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv) :=
  by
  simpa only [nb090AlphaDummy818] using
    freshVar_not_mem
      (((synCcompl (synCphi (Class.cv (nb090AlphaDummy788 v u h))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv)
      0

theorem nb090_fresh_992 (A : Class) :
    (nb090AlphaDummy867 A) ∉
      (((synCcompl (synCphi (Class.cv (nb090AlphaDummy836 A))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv) :=
  by
  simpa only [nb090AlphaDummy867] using
    freshVar_not_mem
      (((synCcompl (synCphi (Class.cv (nb090AlphaDummy836 A))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv)
      0

theorem nb090_fresh_993 (v : Var) :
    (nb090AlphaDummy868 v) ∉
      (((synCcompl (synCphi (Class.cv (nb090AlphaDummy838 v))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv) :=
  by
  simpa only [nb090AlphaDummy868] using
    freshVar_not_mem
      (((synCcompl (synCphi (Class.cv (nb090AlphaDummy838 v))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv)
      0

theorem nb090_fresh_994 (A : Class) :
    (nb090AlphaDummy699 A) ∉
      (((synCfv (Class.cv (nb090AlphaDummy000 A))
            (Class.cv (nb090AlphaDummy041 A)))).fv ∪
        ((synCfv (Class.cv (nb090AlphaDummy000 A))
            (Class.cv (nb090AlphaDummy042 A)))).fv) :=
  by
  simpa only [nb090AlphaDummy699] using
    freshVar_not_mem
      (((synCfv (Class.cv (nb090AlphaDummy000 A))
            (Class.cv (nb090AlphaDummy041 A)))).fv ∪
        ((synCfv (Class.cv (nb090AlphaDummy000 A))
            (Class.cv (nb090AlphaDummy042 A)))).fv)
      0

theorem nb090_fresh_995 (A : Class) :
    (nb090AlphaDummy700 A) ∉
      (((synCfv (Class.cv (nb090AlphaDummy000 A))
            (Class.cv (nb090AlphaDummy041 A)))).fv ∪
        ((synCfv (Class.cv (nb090AlphaDummy000 A))
            (Class.cv (nb090AlphaDummy042 A)))).fv) :=
  by
  simpa only [nb090AlphaDummy700] using
    freshVar_not_mem
      (((synCfv (Class.cv (nb090AlphaDummy000 A))
            (Class.cv (nb090AlphaDummy041 A)))).fv ∪
        ((synCfv (Class.cv (nb090AlphaDummy000 A))
            (Class.cv (nb090AlphaDummy042 A)))).fv)
      1

theorem nb090_distinct_996 (A : Class) :
    (nb090AlphaDummy699 A) ≠ (nb090AlphaDummy700 A) := by
  simpa only [nb090AlphaDummy699, nb090AlphaDummy700] using
    (freshVar_injective (((synCfv (Class.cv (nb090AlphaDummy000 A))
            (Class.cv (nb090AlphaDummy041 A)))).fv ∪
        ((synCfv (Class.cv (nb090AlphaDummy000 A))
            (Class.cv (nb090AlphaDummy042 A)))).fv) (i := 0) (j := 1) (by decide))

theorem nb090_fresh_997 (v : Var) (u : Var) (h : Var) :
    (nb090AlphaDummy701 v u h) ∉
      (((synCfv (Class.cv h) (Class.cv (nb090AlphaDummy043 v u h)))).fv ∪
        ((synCfv (Class.cv h) (Class.cv (nb090AlphaDummy044 v u h)))).fv) :=
  by
  simpa only [nb090AlphaDummy701] using
    freshVar_not_mem
      (((synCfv (Class.cv h) (Class.cv (nb090AlphaDummy043 v u h)))).fv ∪
        ((synCfv (Class.cv h) (Class.cv (nb090AlphaDummy044 v u h)))).fv)
      0

theorem nb090_fresh_998 (v : Var) (u : Var) (h : Var) :
    (nb090AlphaDummy702 v u h) ∉
      (((synCfv (Class.cv h) (Class.cv (nb090AlphaDummy043 v u h)))).fv ∪
        ((synCfv (Class.cv h) (Class.cv (nb090AlphaDummy044 v u h)))).fv) :=
  by
  simpa only [nb090AlphaDummy702] using
    freshVar_not_mem
      (((synCfv (Class.cv h) (Class.cv (nb090AlphaDummy043 v u h)))).fv ∪
        ((synCfv (Class.cv h) (Class.cv (nb090AlphaDummy044 v u h)))).fv)
      1

theorem nb090_distinct_999 (v : Var) (u : Var) (h : Var) :
    (nb090AlphaDummy701 v u h) ≠ (nb090AlphaDummy702 v u h) := by
  simpa only [nb090AlphaDummy701, nb090AlphaDummy702] using
    (freshVar_injective (((synCfv (Class.cv h) (Class.cv (nb090AlphaDummy043 v u h)))).fv ∪
        ((synCfv (Class.cv h) (Class.cv (nb090AlphaDummy044 v u h)))).fv)
      (i := 0) (j := 1) (by decide))

theorem nb090_fresh_1000 (A : Class) :
    (nb090AlphaDummy025 A) ∉
      (((synCnin (Class.cv (nb090AlphaDummy020 A))
            (Class.cv (nb090AlphaDummy021 A)))).fv ∪
        ((synCnin (Class.cv (nb090AlphaDummy020 A))
            (Class.cv (nb090AlphaDummy021 A)))).fv) :=
  by
  simpa only [nb090AlphaDummy025] using
    freshVar_not_mem
      (((synCnin (Class.cv (nb090AlphaDummy020 A))
            (Class.cv (nb090AlphaDummy021 A)))).fv ∪
        ((synCnin (Class.cv (nb090AlphaDummy020 A))
            (Class.cv (nb090AlphaDummy021 A)))).fv)
      0

theorem nb090_fresh_1001 (v : Var) (u : Var) :
    (nb090AlphaDummy026 v u) ∉
      (((synCnin (Class.cv (nb090AlphaDummy023 v u))
            (Class.cv (nb090AlphaDummy024 v u)))).fv ∪
        ((synCnin (Class.cv (nb090AlphaDummy023 v u))
            (Class.cv (nb090AlphaDummy024 v u)))).fv) :=
  by
  simpa only [nb090AlphaDummy026] using
    freshVar_not_mem
      (((synCnin (Class.cv (nb090AlphaDummy023 v u))
            (Class.cv (nb090AlphaDummy024 v u)))).fv ∪
        ((synCnin (Class.cv (nb090AlphaDummy023 v u))
            (Class.cv (nb090AlphaDummy024 v u)))).fv)
      0

theorem nb090_fresh_1002 (A : Class) :
    (nb090AlphaDummy077 A) ∉
      (((synCnin (Class.cv (nb090AlphaDummy072 A))
            (Class.cv (nb090AlphaDummy073 A)))).fv ∪
        ((synCnin (Class.cv (nb090AlphaDummy072 A))
            (Class.cv (nb090AlphaDummy073 A)))).fv) :=
  by
  simpa only [nb090AlphaDummy077] using
    freshVar_not_mem
      (((synCnin (Class.cv (nb090AlphaDummy072 A))
            (Class.cv (nb090AlphaDummy073 A)))).fv ∪
        ((synCnin (Class.cv (nb090AlphaDummy072 A))
            (Class.cv (nb090AlphaDummy073 A)))).fv)
      0

theorem nb090_fresh_1003 (h : Var) :
    (nb090AlphaDummy078 h) ∉
      (((synCnin (Class.cv (nb090AlphaDummy075 h))
            (Class.cv (nb090AlphaDummy076 h)))).fv ∪
        ((synCnin (Class.cv (nb090AlphaDummy075 h))
            (Class.cv (nb090AlphaDummy076 h)))).fv) :=
  by
  simpa only [nb090AlphaDummy078] using
    freshVar_not_mem
      (((synCnin (Class.cv (nb090AlphaDummy075 h))
            (Class.cv (nb090AlphaDummy076 h)))).fv ∪
        ((synCnin (Class.cv (nb090AlphaDummy075 h))
            (Class.cv (nb090AlphaDummy076 h)))).fv)
      0

theorem nb090_fresh_1004 (A : Class) :
    (nb090AlphaDummy113 A) ∉
      (((synCnin (Class.cv (nb090AlphaDummy108 A))
            (Class.cv (nb090AlphaDummy109 A)))).fv ∪
        ((synCnin (Class.cv (nb090AlphaDummy108 A))
            (Class.cv (nb090AlphaDummy109 A)))).fv) :=
  by
  simpa only [nb090AlphaDummy113] using
    freshVar_not_mem
      (((synCnin (Class.cv (nb090AlphaDummy108 A))
            (Class.cv (nb090AlphaDummy109 A)))).fv ∪
        ((synCnin (Class.cv (nb090AlphaDummy108 A))
            (Class.cv (nb090AlphaDummy109 A)))).fv)
      0

theorem nb090_fresh_1005 (h : Var) :
    (nb090AlphaDummy114 h) ∉
      (((synCnin (Class.cv (nb090AlphaDummy111 h))
            (Class.cv (nb090AlphaDummy112 h)))).fv ∪
        ((synCnin (Class.cv (nb090AlphaDummy111 h))
            (Class.cv (nb090AlphaDummy112 h)))).fv) :=
  by
  simpa only [nb090AlphaDummy114] using
    freshVar_not_mem
      (((synCnin (Class.cv (nb090AlphaDummy111 h))
            (Class.cv (nb090AlphaDummy112 h)))).fv ∪
        ((synCnin (Class.cv (nb090AlphaDummy111 h))
            (Class.cv (nb090AlphaDummy112 h)))).fv)
      0

theorem nb090_fresh_1006 (A : Class) :
    (nb090AlphaDummy155 A) ∉
      (((synCnin (Class.cv (nb090AlphaDummy150 A))
            (Class.cv (nb090AlphaDummy151 A)))).fv ∪
        ((synCnin (Class.cv (nb090AlphaDummy150 A))
            (Class.cv (nb090AlphaDummy151 A)))).fv) :=
  by
  simpa only [nb090AlphaDummy155] using
    freshVar_not_mem
      (((synCnin (Class.cv (nb090AlphaDummy150 A))
            (Class.cv (nb090AlphaDummy151 A)))).fv ∪
        ((synCnin (Class.cv (nb090AlphaDummy150 A))
            (Class.cv (nb090AlphaDummy151 A)))).fv)
      0

theorem nb090_fresh_1007 (h : Var) :
    (nb090AlphaDummy156 h) ∉
      (((synCnin (Class.cv (nb090AlphaDummy153 h))
            (Class.cv (nb090AlphaDummy154 h)))).fv ∪
        ((synCnin (Class.cv (nb090AlphaDummy153 h))
            (Class.cv (nb090AlphaDummy154 h)))).fv) :=
  by
  simpa only [nb090AlphaDummy156] using
    freshVar_not_mem
      (((synCnin (Class.cv (nb090AlphaDummy153 h))
            (Class.cv (nb090AlphaDummy154 h)))).fv ∪
        ((synCnin (Class.cv (nb090AlphaDummy153 h))
            (Class.cv (nb090AlphaDummy154 h)))).fv)
      0

theorem nb090_fresh_1008 (A : Class) :
    (nb090AlphaDummy191 A) ∉
      (((synCnin (Class.cv (nb090AlphaDummy186 A))
            (Class.cv (nb090AlphaDummy187 A)))).fv ∪
        ((synCnin (Class.cv (nb090AlphaDummy186 A))
            (Class.cv (nb090AlphaDummy187 A)))).fv) :=
  by
  simpa only [nb090AlphaDummy191] using
    freshVar_not_mem
      (((synCnin (Class.cv (nb090AlphaDummy186 A))
            (Class.cv (nb090AlphaDummy187 A)))).fv ∪
        ((synCnin (Class.cv (nb090AlphaDummy186 A))
            (Class.cv (nb090AlphaDummy187 A)))).fv)
      0

theorem nb090_fresh_1009 (h : Var) :
    (nb090AlphaDummy192 h) ∉
      (((synCnin (Class.cv (nb090AlphaDummy189 h))
            (Class.cv (nb090AlphaDummy190 h)))).fv ∪
        ((synCnin (Class.cv (nb090AlphaDummy189 h))
            (Class.cv (nb090AlphaDummy190 h)))).fv) :=
  by
  simpa only [nb090AlphaDummy192] using
    freshVar_not_mem
      (((synCnin (Class.cv (nb090AlphaDummy189 h))
            (Class.cv (nb090AlphaDummy190 h)))).fv ∪
        ((synCnin (Class.cv (nb090AlphaDummy189 h))
            (Class.cv (nb090AlphaDummy190 h)))).fv)
      0

theorem nb090_fresh_1010 (A : Class) :
    (nb090AlphaDummy227 A) ∉
      (((synCnin (Class.cv (nb090AlphaDummy222 A))
            (Class.cv (nb090AlphaDummy223 A)))).fv ∪
        ((synCnin (Class.cv (nb090AlphaDummy222 A))
            (Class.cv (nb090AlphaDummy223 A)))).fv) :=
  by
  simpa only [nb090AlphaDummy227] using
    freshVar_not_mem
      (((synCnin (Class.cv (nb090AlphaDummy222 A))
            (Class.cv (nb090AlphaDummy223 A)))).fv ∪
        ((synCnin (Class.cv (nb090AlphaDummy222 A))
            (Class.cv (nb090AlphaDummy223 A)))).fv)
      0

theorem nb090_fresh_1011 (h : Var) :
    (nb090AlphaDummy228 h) ∉
      (((synCnin (Class.cv (nb090AlphaDummy225 h))
            (Class.cv (nb090AlphaDummy226 h)))).fv ∪
        ((synCnin (Class.cv (nb090AlphaDummy225 h))
            (Class.cv (nb090AlphaDummy226 h)))).fv) :=
  by
  simpa only [nb090AlphaDummy228] using
    freshVar_not_mem
      (((synCnin (Class.cv (nb090AlphaDummy225 h))
            (Class.cv (nb090AlphaDummy226 h)))).fv ∪
        ((synCnin (Class.cv (nb090AlphaDummy225 h))
            (Class.cv (nb090AlphaDummy226 h)))).fv)
      0

theorem nb090_fresh_1012 (A : Class) :
    (nb090AlphaDummy267 A) ∉
      (((synCnin (Class.cv (nb090AlphaDummy262 A))
            (Class.cv (nb090AlphaDummy263 A)))).fv ∪
        ((synCnin (Class.cv (nb090AlphaDummy262 A))
            (Class.cv (nb090AlphaDummy263 A)))).fv) :=
  by
  simpa only [nb090AlphaDummy267] using
    freshVar_not_mem
      (((synCnin (Class.cv (nb090AlphaDummy262 A))
            (Class.cv (nb090AlphaDummy263 A)))).fv ∪
        ((synCnin (Class.cv (nb090AlphaDummy262 A))
            (Class.cv (nb090AlphaDummy263 A)))).fv)
      0

theorem nb090_fresh_1013 (h : Var) :
    (nb090AlphaDummy268 h) ∉
      (((synCnin (Class.cv (nb090AlphaDummy265 h))
            (Class.cv (nb090AlphaDummy266 h)))).fv ∪
        ((synCnin (Class.cv (nb090AlphaDummy265 h))
            (Class.cv (nb090AlphaDummy266 h)))).fv) :=
  by
  simpa only [nb090AlphaDummy268] using
    freshVar_not_mem
      (((synCnin (Class.cv (nb090AlphaDummy265 h))
            (Class.cv (nb090AlphaDummy266 h)))).fv ∪
        ((synCnin (Class.cv (nb090AlphaDummy265 h))
            (Class.cv (nb090AlphaDummy266 h)))).fv)
      0

theorem nb090_fresh_1014 (A : Class) :
    (nb090AlphaDummy311 A) ∉
      (((synCnin (Class.cv (nb090AlphaDummy306 A))
            (Class.cv (nb090AlphaDummy307 A)))).fv ∪
        ((synCnin (Class.cv (nb090AlphaDummy306 A))
            (Class.cv (nb090AlphaDummy307 A)))).fv) :=
  by
  simpa only [nb090AlphaDummy311] using
    freshVar_not_mem
      (((synCnin (Class.cv (nb090AlphaDummy306 A))
            (Class.cv (nb090AlphaDummy307 A)))).fv ∪
        ((synCnin (Class.cv (nb090AlphaDummy306 A))
            (Class.cv (nb090AlphaDummy307 A)))).fv)
      0

theorem nb090_fresh_1015 (u : Var) :
    (nb090AlphaDummy312 u) ∉
      (((synCnin (Class.cv (nb090AlphaDummy309 u))
            (Class.cv (nb090AlphaDummy310 u)))).fv ∪
        ((synCnin (Class.cv (nb090AlphaDummy309 u))
            (Class.cv (nb090AlphaDummy310 u)))).fv) :=
  by
  simpa only [nb090AlphaDummy312] using
    freshVar_not_mem
      (((synCnin (Class.cv (nb090AlphaDummy309 u))
            (Class.cv (nb090AlphaDummy310 u)))).fv ∪
        ((synCnin (Class.cv (nb090AlphaDummy309 u))
            (Class.cv (nb090AlphaDummy310 u)))).fv)
      0

theorem nb090_fresh_1016 (A : Class) :
    (nb090AlphaDummy357 A) ∉
      (((synCnin (Class.cv (nb090AlphaDummy352 A))
            (Class.cv (nb090AlphaDummy353 A)))).fv ∪
        ((synCnin (Class.cv (nb090AlphaDummy352 A))
            (Class.cv (nb090AlphaDummy353 A)))).fv) :=
  by
  simpa only [nb090AlphaDummy357] using
    freshVar_not_mem
      (((synCnin (Class.cv (nb090AlphaDummy352 A))
            (Class.cv (nb090AlphaDummy353 A)))).fv ∪
        ((synCnin (Class.cv (nb090AlphaDummy352 A))
            (Class.cv (nb090AlphaDummy353 A)))).fv)
      0

theorem nb090_fresh_1017 (h : Var) :
    (nb090AlphaDummy358 h) ∉
      (((synCnin (Class.cv (nb090AlphaDummy355 h))
            (Class.cv (nb090AlphaDummy356 h)))).fv ∪
        ((synCnin (Class.cv (nb090AlphaDummy355 h))
            (Class.cv (nb090AlphaDummy356 h)))).fv) :=
  by
  simpa only [nb090AlphaDummy358] using
    freshVar_not_mem
      (((synCnin (Class.cv (nb090AlphaDummy355 h))
            (Class.cv (nb090AlphaDummy356 h)))).fv ∪
        ((synCnin (Class.cv (nb090AlphaDummy355 h))
            (Class.cv (nb090AlphaDummy356 h)))).fv)
      0

theorem nb090_fresh_1018 (A : Class) :
    (nb090AlphaDummy401 A) ∉
      (((synCnin (Class.cv (nb090AlphaDummy396 A))
            (Class.cv (nb090AlphaDummy397 A)))).fv ∪
        ((synCnin (Class.cv (nb090AlphaDummy396 A))
            (Class.cv (nb090AlphaDummy397 A)))).fv) :=
  by
  simpa only [nb090AlphaDummy401] using
    freshVar_not_mem
      (((synCnin (Class.cv (nb090AlphaDummy396 A))
            (Class.cv (nb090AlphaDummy397 A)))).fv ∪
        ((synCnin (Class.cv (nb090AlphaDummy396 A))
            (Class.cv (nb090AlphaDummy397 A)))).fv)
      0

theorem nb090_fresh_1019 (v : Var) :
    (nb090AlphaDummy402 v) ∉
      (((synCnin (Class.cv (nb090AlphaDummy399 v))
            (Class.cv (nb090AlphaDummy400 v)))).fv ∪
        ((synCnin (Class.cv (nb090AlphaDummy399 v))
            (Class.cv (nb090AlphaDummy400 v)))).fv) :=
  by
  simpa only [nb090AlphaDummy402] using
    freshVar_not_mem
      (((synCnin (Class.cv (nb090AlphaDummy399 v))
            (Class.cv (nb090AlphaDummy400 v)))).fv ∪
        ((synCnin (Class.cv (nb090AlphaDummy399 v))
            (Class.cv (nb090AlphaDummy400 v)))).fv)
      0

theorem nb090_fresh_1020 (A : Class) :
    (nb090AlphaDummy451 A) ∉
      (((synCnin (Class.cv (nb090AlphaDummy446 A))
            (Class.cv (nb090AlphaDummy447 A)))).fv ∪
        ((synCnin (Class.cv (nb090AlphaDummy446 A))
            (Class.cv (nb090AlphaDummy447 A)))).fv) :=
  by
  simpa only [nb090AlphaDummy451] using
    freshVar_not_mem
      (((synCnin (Class.cv (nb090AlphaDummy446 A))
            (Class.cv (nb090AlphaDummy447 A)))).fv ∪
        ((synCnin (Class.cv (nb090AlphaDummy446 A))
            (Class.cv (nb090AlphaDummy447 A)))).fv)
      0

theorem nb090_fresh_1021 (h : Var) :
    (nb090AlphaDummy452 h) ∉
      (((synCnin (Class.cv (nb090AlphaDummy449 h))
            (Class.cv (nb090AlphaDummy450 h)))).fv ∪
        ((synCnin (Class.cv (nb090AlphaDummy449 h))
            (Class.cv (nb090AlphaDummy450 h)))).fv) :=
  by
  simpa only [nb090AlphaDummy452] using
    freshVar_not_mem
      (((synCnin (Class.cv (nb090AlphaDummy449 h))
            (Class.cv (nb090AlphaDummy450 h)))).fv ∪
        ((synCnin (Class.cv (nb090AlphaDummy449 h))
            (Class.cv (nb090AlphaDummy450 h)))).fv)
      0

theorem nb090_fresh_1022 (A : Class) :
    (nb090AlphaDummy487 A) ∉
      (((synCnin (Class.cv (nb090AlphaDummy482 A))
            (Class.cv (nb090AlphaDummy483 A)))).fv ∪
        ((synCnin (Class.cv (nb090AlphaDummy482 A))
            (Class.cv (nb090AlphaDummy483 A)))).fv) :=
  by
  simpa only [nb090AlphaDummy487] using
    freshVar_not_mem
      (((synCnin (Class.cv (nb090AlphaDummy482 A))
            (Class.cv (nb090AlphaDummy483 A)))).fv ∪
        ((synCnin (Class.cv (nb090AlphaDummy482 A))
            (Class.cv (nb090AlphaDummy483 A)))).fv)
      0

theorem nb090_fresh_1023 (h : Var) :
    (nb090AlphaDummy488 h) ∉
      (((synCnin (Class.cv (nb090AlphaDummy485 h))
            (Class.cv (nb090AlphaDummy486 h)))).fv ∪
        ((synCnin (Class.cv (nb090AlphaDummy485 h))
            (Class.cv (nb090AlphaDummy486 h)))).fv) :=
  by
  simpa only [nb090AlphaDummy488] using
    freshVar_not_mem
      (((synCnin (Class.cv (nb090AlphaDummy485 h))
            (Class.cv (nb090AlphaDummy486 h)))).fv ∪
        ((synCnin (Class.cv (nb090AlphaDummy485 h))
            (Class.cv (nb090AlphaDummy486 h)))).fv)
      0

theorem nb090_fresh_1024 (A : Class) :
    (nb090AlphaDummy529 A) ∉
      (((synCnin (Class.cv (nb090AlphaDummy524 A))
            (Class.cv (nb090AlphaDummy525 A)))).fv ∪
        ((synCnin (Class.cv (nb090AlphaDummy524 A))
            (Class.cv (nb090AlphaDummy525 A)))).fv) :=
  by
  simpa only [nb090AlphaDummy529] using
    freshVar_not_mem
      (((synCnin (Class.cv (nb090AlphaDummy524 A))
            (Class.cv (nb090AlphaDummy525 A)))).fv ∪
        ((synCnin (Class.cv (nb090AlphaDummy524 A))
            (Class.cv (nb090AlphaDummy525 A)))).fv)
      0

theorem nb090_fresh_1025 (h : Var) :
    (nb090AlphaDummy530 h) ∉
      (((synCnin (Class.cv (nb090AlphaDummy527 h))
            (Class.cv (nb090AlphaDummy528 h)))).fv ∪
        ((synCnin (Class.cv (nb090AlphaDummy527 h))
            (Class.cv (nb090AlphaDummy528 h)))).fv) :=
  by
  simpa only [nb090AlphaDummy530] using
    freshVar_not_mem
      (((synCnin (Class.cv (nb090AlphaDummy527 h))
            (Class.cv (nb090AlphaDummy528 h)))).fv ∪
        ((synCnin (Class.cv (nb090AlphaDummy527 h))
            (Class.cv (nb090AlphaDummy528 h)))).fv)
      0

theorem nb090_fresh_1026 (A : Class) :
    (nb090AlphaDummy565 A) ∉
      (((synCnin (Class.cv (nb090AlphaDummy560 A))
            (Class.cv (nb090AlphaDummy561 A)))).fv ∪
        ((synCnin (Class.cv (nb090AlphaDummy560 A))
            (Class.cv (nb090AlphaDummy561 A)))).fv) :=
  by
  simpa only [nb090AlphaDummy565] using
    freshVar_not_mem
      (((synCnin (Class.cv (nb090AlphaDummy560 A))
            (Class.cv (nb090AlphaDummy561 A)))).fv ∪
        ((synCnin (Class.cv (nb090AlphaDummy560 A))
            (Class.cv (nb090AlphaDummy561 A)))).fv)
      0

theorem nb090_fresh_1027 (h : Var) :
    (nb090AlphaDummy566 h) ∉
      (((synCnin (Class.cv (nb090AlphaDummy563 h))
            (Class.cv (nb090AlphaDummy564 h)))).fv ∪
        ((synCnin (Class.cv (nb090AlphaDummy563 h))
            (Class.cv (nb090AlphaDummy564 h)))).fv) :=
  by
  simpa only [nb090AlphaDummy566] using
    freshVar_not_mem
      (((synCnin (Class.cv (nb090AlphaDummy563 h))
            (Class.cv (nb090AlphaDummy564 h)))).fv ∪
        ((synCnin (Class.cv (nb090AlphaDummy563 h))
            (Class.cv (nb090AlphaDummy564 h)))).fv)
      0

theorem nb090_fresh_1028 (A : Class) :
    (nb090AlphaDummy601 A) ∉
      (((synCnin (Class.cv (nb090AlphaDummy596 A))
            (Class.cv (nb090AlphaDummy597 A)))).fv ∪
        ((synCnin (Class.cv (nb090AlphaDummy596 A))
            (Class.cv (nb090AlphaDummy597 A)))).fv) :=
  by
  simpa only [nb090AlphaDummy601] using
    freshVar_not_mem
      (((synCnin (Class.cv (nb090AlphaDummy596 A))
            (Class.cv (nb090AlphaDummy597 A)))).fv ∪
        ((synCnin (Class.cv (nb090AlphaDummy596 A))
            (Class.cv (nb090AlphaDummy597 A)))).fv)
      0

theorem nb090_fresh_1029 (h : Var) :
    (nb090AlphaDummy602 h) ∉
      (((synCnin (Class.cv (nb090AlphaDummy599 h))
            (Class.cv (nb090AlphaDummy600 h)))).fv ∪
        ((synCnin (Class.cv (nb090AlphaDummy599 h))
            (Class.cv (nb090AlphaDummy600 h)))).fv) :=
  by
  simpa only [nb090AlphaDummy602] using
    freshVar_not_mem
      (((synCnin (Class.cv (nb090AlphaDummy599 h))
            (Class.cv (nb090AlphaDummy600 h)))).fv ∪
        ((synCnin (Class.cv (nb090AlphaDummy599 h))
            (Class.cv (nb090AlphaDummy600 h)))).fv)
      0

theorem nb090_fresh_1030 (A : Class) :
    (nb090AlphaDummy637 A) ∉
      (((synCnin (Class.cv (nb090AlphaDummy632 A))
            (Class.cv (nb090AlphaDummy633 A)))).fv ∪
        ((synCnin (Class.cv (nb090AlphaDummy632 A))
            (Class.cv (nb090AlphaDummy633 A)))).fv) :=
  by
  simpa only [nb090AlphaDummy637] using
    freshVar_not_mem
      (((synCnin (Class.cv (nb090AlphaDummy632 A))
            (Class.cv (nb090AlphaDummy633 A)))).fv ∪
        ((synCnin (Class.cv (nb090AlphaDummy632 A))
            (Class.cv (nb090AlphaDummy633 A)))).fv)
      0

theorem nb090_fresh_1031 (v : Var) (u : Var) (h : Var) :
    (nb090AlphaDummy638 v u h) ∉
      (((synCnin (Class.cv (nb090AlphaDummy635 v u h))
            (Class.cv (nb090AlphaDummy636 v u h)))).fv ∪
        ((synCnin (Class.cv (nb090AlphaDummy635 v u h))
            (Class.cv (nb090AlphaDummy636 v u h)))).fv) :=
  by
  simpa only [nb090AlphaDummy638] using
    freshVar_not_mem
      (((synCnin (Class.cv (nb090AlphaDummy635 v u h))
            (Class.cv (nb090AlphaDummy636 v u h)))).fv ∪
        ((synCnin (Class.cv (nb090AlphaDummy635 v u h))
            (Class.cv (nb090AlphaDummy636 v u h)))).fv)
      0

theorem nb090_fresh_1032 (A : Class) :
    (nb090AlphaDummy681 A) ∉
      (((synCnin (Class.cv (nb090AlphaDummy676 A))
            (Class.cv (nb090AlphaDummy677 A)))).fv ∪
        ((synCnin (Class.cv (nb090AlphaDummy676 A))
            (Class.cv (nb090AlphaDummy677 A)))).fv) :=
  by
  simpa only [nb090AlphaDummy681] using
    freshVar_not_mem
      (((synCnin (Class.cv (nb090AlphaDummy676 A))
            (Class.cv (nb090AlphaDummy677 A)))).fv ∪
        ((synCnin (Class.cv (nb090AlphaDummy676 A))
            (Class.cv (nb090AlphaDummy677 A)))).fv)
      0

theorem nb090_fresh_1033 (u : Var) :
    (nb090AlphaDummy682 u) ∉
      (((synCnin (Class.cv (nb090AlphaDummy679 u))
            (Class.cv (nb090AlphaDummy680 u)))).fv ∪
        ((synCnin (Class.cv (nb090AlphaDummy679 u))
            (Class.cv (nb090AlphaDummy680 u)))).fv) :=
  by
  simpa only [nb090AlphaDummy682] using
    freshVar_not_mem
      (((synCnin (Class.cv (nb090AlphaDummy679 u))
            (Class.cv (nb090AlphaDummy680 u)))).fv ∪
        ((synCnin (Class.cv (nb090AlphaDummy679 u))
            (Class.cv (nb090AlphaDummy680 u)))).fv)
      0

theorem nb090_fresh_1034 (A : Class) :
    (nb090AlphaDummy735 A) ∉
      (((synCnin (Class.cv (nb090AlphaDummy730 A))
            (Class.cv (nb090AlphaDummy731 A)))).fv ∪
        ((synCnin (Class.cv (nb090AlphaDummy730 A))
            (Class.cv (nb090AlphaDummy731 A)))).fv) :=
  by
  simpa only [nb090AlphaDummy735] using
    freshVar_not_mem
      (((synCnin (Class.cv (nb090AlphaDummy730 A))
            (Class.cv (nb090AlphaDummy731 A)))).fv ∪
        ((synCnin (Class.cv (nb090AlphaDummy730 A))
            (Class.cv (nb090AlphaDummy731 A)))).fv)
      0

theorem nb090_fresh_1035 (v : Var) (u : Var) (h : Var) :
    (nb090AlphaDummy736 v u h) ∉
      (((synCnin (Class.cv (nb090AlphaDummy733 v u h))
            (Class.cv (nb090AlphaDummy734 v u h)))).fv ∪
        ((synCnin (Class.cv (nb090AlphaDummy733 v u h))
            (Class.cv (nb090AlphaDummy734 v u h)))).fv) :=
  by
  simpa only [nb090AlphaDummy736] using
    freshVar_not_mem
      (((synCnin (Class.cv (nb090AlphaDummy733 v u h))
            (Class.cv (nb090AlphaDummy734 v u h)))).fv ∪
        ((synCnin (Class.cv (nb090AlphaDummy733 v u h))
            (Class.cv (nb090AlphaDummy734 v u h)))).fv)
      0

theorem nb090_fresh_1036 (A : Class) :
    (nb090AlphaDummy765 A) ∉
      (((synCnin (Class.cv (nb090AlphaDummy760 A))
            (Class.cv (nb090AlphaDummy761 A)))).fv ∪
        ((synCnin (Class.cv (nb090AlphaDummy760 A))
            (Class.cv (nb090AlphaDummy761 A)))).fv) :=
  by
  simpa only [nb090AlphaDummy765] using
    freshVar_not_mem
      (((synCnin (Class.cv (nb090AlphaDummy760 A))
            (Class.cv (nb090AlphaDummy761 A)))).fv ∪
        ((synCnin (Class.cv (nb090AlphaDummy760 A))
            (Class.cv (nb090AlphaDummy761 A)))).fv)
      0

theorem nb090_fresh_1037 (v : Var) (u : Var) (h : Var) :
    (nb090AlphaDummy766 v u h) ∉
      (((synCnin (Class.cv (nb090AlphaDummy763 v u h))
            (Class.cv (nb090AlphaDummy764 v u h)))).fv ∪
        ((synCnin (Class.cv (nb090AlphaDummy763 v u h))
            (Class.cv (nb090AlphaDummy764 v u h)))).fv) :=
  by
  simpa only [nb090AlphaDummy766] using
    freshVar_not_mem
      (((synCnin (Class.cv (nb090AlphaDummy763 v u h))
            (Class.cv (nb090AlphaDummy764 v u h)))).fv ∪
        ((synCnin (Class.cv (nb090AlphaDummy763 v u h))
            (Class.cv (nb090AlphaDummy764 v u h)))).fv)
      0

theorem nb090_fresh_1038 (A : Class) :
    (nb090AlphaDummy805 A) ∉
      (((synCnin (Class.cv (nb090AlphaDummy800 A))
            (Class.cv (nb090AlphaDummy801 A)))).fv ∪
        ((synCnin (Class.cv (nb090AlphaDummy800 A))
            (Class.cv (nb090AlphaDummy801 A)))).fv) :=
  by
  simpa only [nb090AlphaDummy805] using
    freshVar_not_mem
      (((synCnin (Class.cv (nb090AlphaDummy800 A))
            (Class.cv (nb090AlphaDummy801 A)))).fv ∪
        ((synCnin (Class.cv (nb090AlphaDummy800 A))
            (Class.cv (nb090AlphaDummy801 A)))).fv)
      0

theorem nb090_fresh_1039 (v : Var) (u : Var) (h : Var) :
    (nb090AlphaDummy806 v u h) ∉
      (((synCnin (Class.cv (nb090AlphaDummy803 v u h))
            (Class.cv (nb090AlphaDummy804 v u h)))).fv ∪
        ((synCnin (Class.cv (nb090AlphaDummy803 v u h))
            (Class.cv (nb090AlphaDummy804 v u h)))).fv) :=
  by
  simpa only [nb090AlphaDummy806] using
    freshVar_not_mem
      (((synCnin (Class.cv (nb090AlphaDummy803 v u h))
            (Class.cv (nb090AlphaDummy804 v u h)))).fv ∪
        ((synCnin (Class.cv (nb090AlphaDummy803 v u h))
            (Class.cv (nb090AlphaDummy804 v u h)))).fv)
      0

theorem nb090_fresh_1040 (A : Class) :
    (nb090AlphaDummy855 A) ∉
      (((synCnin (Class.cv (nb090AlphaDummy850 A))
            (Class.cv (nb090AlphaDummy851 A)))).fv ∪
        ((synCnin (Class.cv (nb090AlphaDummy850 A))
            (Class.cv (nb090AlphaDummy851 A)))).fv) :=
  by
  simpa only [nb090AlphaDummy855] using
    freshVar_not_mem
      (((synCnin (Class.cv (nb090AlphaDummy850 A))
            (Class.cv (nb090AlphaDummy851 A)))).fv ∪
        ((synCnin (Class.cv (nb090AlphaDummy850 A))
            (Class.cv (nb090AlphaDummy851 A)))).fv)
      0

theorem nb090_fresh_1041 (v : Var) :
    (nb090AlphaDummy856 v) ∉
      (((synCnin (Class.cv (nb090AlphaDummy853 v))
            (Class.cv (nb090AlphaDummy854 v)))).fv ∪
        ((synCnin (Class.cv (nb090AlphaDummy853 v))
            (Class.cv (nb090AlphaDummy854 v)))).fv) :=
  by
  simpa only [nb090AlphaDummy856] using
    freshVar_not_mem
      (((synCnin (Class.cv (nb090AlphaDummy853 v))
            (Class.cv (nb090AlphaDummy854 v)))).fv ∪
        ((synCnin (Class.cv (nb090AlphaDummy853 v))
            (Class.cv (nb090AlphaDummy854 v)))).fv)
      0

theorem nb090_fresh_1042 (A : Class) :
    (nb090AlphaDummy045 A) ∉
      (((synCnin (synCcom (Class.cv (nb090AlphaDummy000 A))
              (synCcnv (Class.cv (nb090AlphaDummy000 A)))) (synCid))).fv ∪ ((synCnin
            (synCcom (Class.cv (nb090AlphaDummy000 A))
              (synCcnv (Class.cv (nb090AlphaDummy000 A)))) (synCid))).fv) :=
  by
  simpa only [nb090AlphaDummy045] using
    freshVar_not_mem
      (((synCnin (synCcom (Class.cv (nb090AlphaDummy000 A))
              (synCcnv (Class.cv (nb090AlphaDummy000 A)))) (synCid))).fv ∪ ((synCnin
            (synCcom (Class.cv (nb090AlphaDummy000 A))
              (synCcnv (Class.cv (nb090AlphaDummy000 A)))) (synCid))).fv)
      0

theorem nb090_fresh_1043 (h : Var) :
    (nb090AlphaDummy046 h) ∉
      (((synCnin (synCcom (Class.cv h) (synCcnv (Class.cv h))) (synCid))).fv ∪
        ((synCnin (synCcom (Class.cv h) (synCcnv (Class.cv h))) (synCid))).fv) :=
  by
  simpa only [nb090AlphaDummy046] using
    freshVar_not_mem
      (((synCnin (synCcom (Class.cv h) (synCcnv (Class.cv h))) (synCid))).fv ∪
        ((synCnin (synCcom (Class.cv h) (synCcnv (Class.cv h))) (synCid))).fv)
      0

theorem nb090_fresh_1044 (A : Class) :
    (nb090AlphaDummy419 A) ∉
      (((synCnin (synCcom (synCcnv (Class.cv (nb090AlphaDummy000 A)))
              (synCcnv (synCcnv (Class.cv (nb090AlphaDummy000 A))))) (synCid))).fv ∪
        ((synCnin (synCcom (synCcnv (Class.cv (nb090AlphaDummy000 A)))
              (synCcnv (synCcnv (Class.cv (nb090AlphaDummy000 A))))) (synCid))).fv) :=
  by
  simpa only [nb090AlphaDummy419] using
    freshVar_not_mem
      (((synCnin (synCcom (synCcnv (Class.cv (nb090AlphaDummy000 A)))
              (synCcnv (synCcnv (Class.cv (nb090AlphaDummy000 A))))) (synCid))).fv ∪
        ((synCnin (synCcom (synCcnv (Class.cv (nb090AlphaDummy000 A)))
              (synCcnv (synCcnv (Class.cv (nb090AlphaDummy000 A))))) (synCid))).fv)
      0

theorem nb090_fresh_1045 (h : Var) :
    (nb090AlphaDummy420 h) ∉
      (((synCnin (synCcom (synCcnv (Class.cv h)) (synCcnv (synCcnv (Class.cv h))))
            (synCid))).fv ∪
        ((synCnin (synCcom (synCcnv (Class.cv h)) (synCcnv (synCcnv (Class.cv h))))
            (synCid))).fv) :=
  by
  simpa only [nb090AlphaDummy420] using
    freshVar_not_mem
      (((synCnin (synCcom (synCcnv (Class.cv h)) (synCcnv (synCcnv (Class.cv h))))
            (synCid))).fv ∪
        ((synCnin (synCcom (synCcnv (Class.cv h)) (synCcnv (synCcnv (Class.cv h))))
            (synCid))).fv)
      0

theorem nb090_fresh_1046 (A : Class) :
    (nb090AlphaDummy329 A) ∉
      (((synCnin (synCrn (Class.cv (nb090AlphaDummy000 A)))
            (synCfv (synC2nd) (Class.cv (nb090AlphaDummy002 A))))).fv ∪
        ((synCnin (synCrn (Class.cv (nb090AlphaDummy000 A)))
            (synCfv (synC2nd) (Class.cv (nb090AlphaDummy002 A))))).fv) :=
  by
  simpa only [nb090AlphaDummy329] using
    freshVar_not_mem
      (((synCnin (synCrn (Class.cv (nb090AlphaDummy000 A)))
            (synCfv (synC2nd) (Class.cv (nb090AlphaDummy002 A))))).fv ∪
        ((synCnin (synCrn (Class.cv (nb090AlphaDummy000 A)))
            (synCfv (synC2nd) (Class.cv (nb090AlphaDummy002 A))))).fv)
      0

theorem nb090_fresh_1047 (v : Var) (h : Var) :
    (nb090AlphaDummy330 v h) ∉
      (((synCnin (synCrn (Class.cv h)) (synCfv (synC2nd) (Class.cv v)))).fv ∪
        ((synCnin (synCrn (Class.cv h)) (synCfv (synC2nd) (Class.cv v)))).fv) :=
  by
  simpa only [nb090AlphaDummy330] using
    freshVar_not_mem
      (((synCnin (synCrn (Class.cv h)) (synCfv (synC2nd) (Class.cv v)))).fv ∪
        ((synCnin (synCrn (Class.cv h)) (synCfv (synC2nd) (Class.cv v)))).fv)
      0

theorem nb090_fresh_1048 (A : Class) :
    (nb090AlphaDummy039 A) ∉
      (((synCphi (Class.cv (nb090AlphaDummy006 A)))).fv ∪
        ((synCphi (Class.cv (nb090AlphaDummy006 A)))).fv) :=
  by
  simpa only [nb090AlphaDummy039] using
    freshVar_not_mem
      (((synCphi (Class.cv (nb090AlphaDummy006 A)))).fv ∪
        ((synCphi (Class.cv (nb090AlphaDummy006 A)))).fv)
      0

theorem nb090_fresh_1049 (v : Var) (u : Var) :
    (nb090AlphaDummy040 v u) ∉
      (((synCphi (Class.cv (nb090AlphaDummy008 v u)))).fv ∪
        ((synCphi (Class.cv (nb090AlphaDummy008 v u)))).fv) :=
  by
  simpa only [nb090AlphaDummy040] using
    freshVar_not_mem
      (((synCphi (Class.cv (nb090AlphaDummy008 v u)))).fv ∪
        ((synCphi (Class.cv (nb090AlphaDummy008 v u)))).fv)
      0

theorem nb090_fresh_1050 (A : Class) :
    (nb090AlphaDummy091 A) ∉
      (((synCphi (Class.cv (nb090AlphaDummy058 A)))).fv ∪
        ((synCphi (Class.cv (nb090AlphaDummy058 A)))).fv) :=
  by
  simpa only [nb090AlphaDummy091] using
    freshVar_not_mem
      (((synCphi (Class.cv (nb090AlphaDummy058 A)))).fv ∪
        ((synCphi (Class.cv (nb090AlphaDummy058 A)))).fv)
      0

theorem nb090_fresh_1051 (h : Var) :
    (nb090AlphaDummy092 h) ∉
      (((synCphi (Class.cv (nb090AlphaDummy060 h)))).fv ∪
        ((synCphi (Class.cv (nb090AlphaDummy060 h)))).fv) :=
  by
  simpa only [nb090AlphaDummy092] using
    freshVar_not_mem
      (((synCphi (Class.cv (nb090AlphaDummy060 h)))).fv ∪
        ((synCphi (Class.cv (nb090AlphaDummy060 h)))).fv)
      0

theorem nb090_fresh_1052 (A : Class) :
    (nb090AlphaDummy127 A) ∉
      (((synCphi (Class.cv (nb090AlphaDummy094 A)))).fv ∪
        ((synCphi (Class.cv (nb090AlphaDummy094 A)))).fv) :=
  by
  simpa only [nb090AlphaDummy127] using
    freshVar_not_mem
      (((synCphi (Class.cv (nb090AlphaDummy094 A)))).fv ∪
        ((synCphi (Class.cv (nb090AlphaDummy094 A)))).fv)
      0

theorem nb090_fresh_1053 (h : Var) :
    (nb090AlphaDummy128 h) ∉
      (((synCphi (Class.cv (nb090AlphaDummy096 h)))).fv ∪
        ((synCphi (Class.cv (nb090AlphaDummy096 h)))).fv) :=
  by
  simpa only [nb090AlphaDummy128] using
    freshVar_not_mem
      (((synCphi (Class.cv (nb090AlphaDummy096 h)))).fv ∪
        ((synCphi (Class.cv (nb090AlphaDummy096 h)))).fv)
      0

theorem nb090_fresh_1054 (A : Class) :
    (nb090AlphaDummy169 A) ∉
      (((synCphi (Class.cv (nb090AlphaDummy136 A)))).fv ∪
        ((synCphi (Class.cv (nb090AlphaDummy136 A)))).fv) :=
  by
  simpa only [nb090AlphaDummy169] using
    freshVar_not_mem
      (((synCphi (Class.cv (nb090AlphaDummy136 A)))).fv ∪
        ((synCphi (Class.cv (nb090AlphaDummy136 A)))).fv)
      0

theorem nb090_fresh_1055 (h : Var) :
    (nb090AlphaDummy170 h) ∉
      (((synCphi (Class.cv (nb090AlphaDummy138 h)))).fv ∪
        ((synCphi (Class.cv (nb090AlphaDummy138 h)))).fv) :=
  by
  simpa only [nb090AlphaDummy170] using
    freshVar_not_mem
      (((synCphi (Class.cv (nb090AlphaDummy138 h)))).fv ∪
        ((synCphi (Class.cv (nb090AlphaDummy138 h)))).fv)
      0

theorem nb090_fresh_1056 (A : Class) :
    (nb090AlphaDummy205 A) ∉
      (((synCphi (Class.cv (nb090AlphaDummy172 A)))).fv ∪
        ((synCphi (Class.cv (nb090AlphaDummy172 A)))).fv) :=
  by
  simpa only [nb090AlphaDummy205] using
    freshVar_not_mem
      (((synCphi (Class.cv (nb090AlphaDummy172 A)))).fv ∪
        ((synCphi (Class.cv (nb090AlphaDummy172 A)))).fv)
      0

theorem nb090_fresh_1057 (h : Var) :
    (nb090AlphaDummy206 h) ∉
      (((synCphi (Class.cv (nb090AlphaDummy174 h)))).fv ∪
        ((synCphi (Class.cv (nb090AlphaDummy174 h)))).fv) :=
  by
  simpa only [nb090AlphaDummy206] using
    freshVar_not_mem
      (((synCphi (Class.cv (nb090AlphaDummy174 h)))).fv ∪
        ((synCphi (Class.cv (nb090AlphaDummy174 h)))).fv)
      0

theorem nb090_fresh_1058 (A : Class) :
    (nb090AlphaDummy241 A) ∉
      (((synCphi (Class.cv (nb090AlphaDummy208 A)))).fv ∪
        ((synCphi (Class.cv (nb090AlphaDummy208 A)))).fv) :=
  by
  simpa only [nb090AlphaDummy241] using
    freshVar_not_mem
      (((synCphi (Class.cv (nb090AlphaDummy208 A)))).fv ∪
        ((synCphi (Class.cv (nb090AlphaDummy208 A)))).fv)
      0

theorem nb090_fresh_1059 (h : Var) :
    (nb090AlphaDummy242 h) ∉
      (((synCphi (Class.cv (nb090AlphaDummy210 h)))).fv ∪
        ((synCphi (Class.cv (nb090AlphaDummy210 h)))).fv) :=
  by
  simpa only [nb090AlphaDummy242] using
    freshVar_not_mem
      (((synCphi (Class.cv (nb090AlphaDummy210 h)))).fv ∪
        ((synCphi (Class.cv (nb090AlphaDummy210 h)))).fv)
      0

theorem nb090_fresh_1060 (A : Class) :
    (nb090AlphaDummy281 A) ∉
      (((synCphi (Class.cv (nb090AlphaDummy248 A)))).fv ∪
        ((synCphi (Class.cv (nb090AlphaDummy248 A)))).fv) :=
  by
  simpa only [nb090AlphaDummy281] using
    freshVar_not_mem
      (((synCphi (Class.cv (nb090AlphaDummy248 A)))).fv ∪
        ((synCphi (Class.cv (nb090AlphaDummy248 A)))).fv)
      0

theorem nb090_fresh_1061 (h : Var) :
    (nb090AlphaDummy282 h) ∉
      (((synCphi (Class.cv (nb090AlphaDummy250 h)))).fv ∪
        ((synCphi (Class.cv (nb090AlphaDummy250 h)))).fv) :=
  by
  simpa only [nb090AlphaDummy282] using
    freshVar_not_mem
      (((synCphi (Class.cv (nb090AlphaDummy250 h)))).fv ∪
        ((synCphi (Class.cv (nb090AlphaDummy250 h)))).fv)
      0

theorem nb090_fresh_1062 (A : Class) :
    (nb090AlphaDummy325 A) ∉
      (((synCphi (Class.cv (nb090AlphaDummy292 A)))).fv ∪
        ((synCphi (Class.cv (nb090AlphaDummy292 A)))).fv) :=
  by
  simpa only [nb090AlphaDummy325] using
    freshVar_not_mem
      (((synCphi (Class.cv (nb090AlphaDummy292 A)))).fv ∪
        ((synCphi (Class.cv (nb090AlphaDummy292 A)))).fv)
      0

theorem nb090_fresh_1063 (u : Var) :
    (nb090AlphaDummy326 u) ∉
      (((synCphi (Class.cv (nb090AlphaDummy294 u)))).fv ∪
        ((synCphi (Class.cv (nb090AlphaDummy294 u)))).fv) :=
  by
  simpa only [nb090AlphaDummy326] using
    freshVar_not_mem
      (((synCphi (Class.cv (nb090AlphaDummy294 u)))).fv ∪
        ((synCphi (Class.cv (nb090AlphaDummy294 u)))).fv)
      0

theorem nb090_fresh_1064 (A : Class) :
    (nb090AlphaDummy371 A) ∉
      (((synCphi (Class.cv (nb090AlphaDummy338 A)))).fv ∪
        ((synCphi (Class.cv (nb090AlphaDummy338 A)))).fv) :=
  by
  simpa only [nb090AlphaDummy371] using
    freshVar_not_mem
      (((synCphi (Class.cv (nb090AlphaDummy338 A)))).fv ∪
        ((synCphi (Class.cv (nb090AlphaDummy338 A)))).fv)
      0

end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired

end

/-! Certificates from `NAR4C090C001Part015`. -/


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

theorem nb090_fresh_1065 (h : Var) :
    (nb090AlphaDummy372 h) ∉
      (((synCphi (Class.cv (nb090AlphaDummy340 h)))).fv ∪
        ((synCphi (Class.cv (nb090AlphaDummy340 h)))).fv) :=
  by
  simpa only [nb090AlphaDummy372] using
    freshVar_not_mem
      (((synCphi (Class.cv (nb090AlphaDummy340 h)))).fv ∪
        ((synCphi (Class.cv (nb090AlphaDummy340 h)))).fv)
      0

theorem nb090_fresh_1066 (A : Class) :
    (nb090AlphaDummy415 A) ∉
      (((synCphi (Class.cv (nb090AlphaDummy382 A)))).fv ∪
        ((synCphi (Class.cv (nb090AlphaDummy382 A)))).fv) :=
  by
  simpa only [nb090AlphaDummy415] using
    freshVar_not_mem
      (((synCphi (Class.cv (nb090AlphaDummy382 A)))).fv ∪
        ((synCphi (Class.cv (nb090AlphaDummy382 A)))).fv)
      0

theorem nb090_fresh_1067 (v : Var) :
    (nb090AlphaDummy416 v) ∉
      (((synCphi (Class.cv (nb090AlphaDummy384 v)))).fv ∪
        ((synCphi (Class.cv (nb090AlphaDummy384 v)))).fv) :=
  by
  simpa only [nb090AlphaDummy416] using
    freshVar_not_mem
      (((synCphi (Class.cv (nb090AlphaDummy384 v)))).fv ∪
        ((synCphi (Class.cv (nb090AlphaDummy384 v)))).fv)
      0

theorem nb090_fresh_1068 (A : Class) :
    (nb090AlphaDummy465 A) ∉
      (((synCphi (Class.cv (nb090AlphaDummy432 A)))).fv ∪
        ((synCphi (Class.cv (nb090AlphaDummy432 A)))).fv) :=
  by
  simpa only [nb090AlphaDummy465] using
    freshVar_not_mem
      (((synCphi (Class.cv (nb090AlphaDummy432 A)))).fv ∪
        ((synCphi (Class.cv (nb090AlphaDummy432 A)))).fv)
      0

theorem nb090_fresh_1069 (h : Var) :
    (nb090AlphaDummy466 h) ∉
      (((synCphi (Class.cv (nb090AlphaDummy434 h)))).fv ∪
        ((synCphi (Class.cv (nb090AlphaDummy434 h)))).fv) :=
  by
  simpa only [nb090AlphaDummy466] using
    freshVar_not_mem
      (((synCphi (Class.cv (nb090AlphaDummy434 h)))).fv ∪
        ((synCphi (Class.cv (nb090AlphaDummy434 h)))).fv)
      0

theorem nb090_fresh_1070 (A : Class) :
    (nb090AlphaDummy501 A) ∉
      (((synCphi (Class.cv (nb090AlphaDummy468 A)))).fv ∪
        ((synCphi (Class.cv (nb090AlphaDummy468 A)))).fv) :=
  by
  simpa only [nb090AlphaDummy501] using
    freshVar_not_mem
      (((synCphi (Class.cv (nb090AlphaDummy468 A)))).fv ∪
        ((synCphi (Class.cv (nb090AlphaDummy468 A)))).fv)
      0

theorem nb090_fresh_1071 (h : Var) :
    (nb090AlphaDummy502 h) ∉
      (((synCphi (Class.cv (nb090AlphaDummy470 h)))).fv ∪
        ((synCphi (Class.cv (nb090AlphaDummy470 h)))).fv) :=
  by
  simpa only [nb090AlphaDummy502] using
    freshVar_not_mem
      (((synCphi (Class.cv (nb090AlphaDummy470 h)))).fv ∪
        ((synCphi (Class.cv (nb090AlphaDummy470 h)))).fv)
      0

theorem nb090_fresh_1072 (A : Class) :
    (nb090AlphaDummy543 A) ∉
      (((synCphi (Class.cv (nb090AlphaDummy510 A)))).fv ∪
        ((synCphi (Class.cv (nb090AlphaDummy510 A)))).fv) :=
  by
  simpa only [nb090AlphaDummy543] using
    freshVar_not_mem
      (((synCphi (Class.cv (nb090AlphaDummy510 A)))).fv ∪
        ((synCphi (Class.cv (nb090AlphaDummy510 A)))).fv)
      0

theorem nb090_fresh_1073 (h : Var) :
    (nb090AlphaDummy544 h) ∉
      (((synCphi (Class.cv (nb090AlphaDummy512 h)))).fv ∪
        ((synCphi (Class.cv (nb090AlphaDummy512 h)))).fv) :=
  by
  simpa only [nb090AlphaDummy544] using
    freshVar_not_mem
      (((synCphi (Class.cv (nb090AlphaDummy512 h)))).fv ∪
        ((synCphi (Class.cv (nb090AlphaDummy512 h)))).fv)
      0

theorem nb090_fresh_1074 (A : Class) :
    (nb090AlphaDummy579 A) ∉
      (((synCphi (Class.cv (nb090AlphaDummy546 A)))).fv ∪
        ((synCphi (Class.cv (nb090AlphaDummy546 A)))).fv) :=
  by
  simpa only [nb090AlphaDummy579] using
    freshVar_not_mem
      (((synCphi (Class.cv (nb090AlphaDummy546 A)))).fv ∪
        ((synCphi (Class.cv (nb090AlphaDummy546 A)))).fv)
      0

theorem nb090_fresh_1075 (h : Var) :
    (nb090AlphaDummy580 h) ∉
      (((synCphi (Class.cv (nb090AlphaDummy548 h)))).fv ∪
        ((synCphi (Class.cv (nb090AlphaDummy548 h)))).fv) :=
  by
  simpa only [nb090AlphaDummy580] using
    freshVar_not_mem
      (((synCphi (Class.cv (nb090AlphaDummy548 h)))).fv ∪
        ((synCphi (Class.cv (nb090AlphaDummy548 h)))).fv)
      0

theorem nb090_fresh_1076 (A : Class) :
    (nb090AlphaDummy615 A) ∉
      (((synCphi (Class.cv (nb090AlphaDummy582 A)))).fv ∪
        ((synCphi (Class.cv (nb090AlphaDummy582 A)))).fv) :=
  by
  simpa only [nb090AlphaDummy615] using
    freshVar_not_mem
      (((synCphi (Class.cv (nb090AlphaDummy582 A)))).fv ∪
        ((synCphi (Class.cv (nb090AlphaDummy582 A)))).fv)
      0

theorem nb090_fresh_1077 (h : Var) :
    (nb090AlphaDummy616 h) ∉
      (((synCphi (Class.cv (nb090AlphaDummy584 h)))).fv ∪
        ((synCphi (Class.cv (nb090AlphaDummy584 h)))).fv) :=
  by
  simpa only [nb090AlphaDummy616] using
    freshVar_not_mem
      (((synCphi (Class.cv (nb090AlphaDummy584 h)))).fv ∪
        ((synCphi (Class.cv (nb090AlphaDummy584 h)))).fv)
      0

theorem nb090_fresh_1078 (A : Class) :
    (nb090AlphaDummy651 A) ∉
      (((synCphi (Class.cv (nb090AlphaDummy618 A)))).fv ∪
        ((synCphi (Class.cv (nb090AlphaDummy618 A)))).fv) :=
  by
  simpa only [nb090AlphaDummy651] using
    freshVar_not_mem
      (((synCphi (Class.cv (nb090AlphaDummy618 A)))).fv ∪
        ((synCphi (Class.cv (nb090AlphaDummy618 A)))).fv)
      0

theorem nb090_fresh_1079 (v : Var) (u : Var) (h : Var) :
    (nb090AlphaDummy652 v u h) ∉
      (((synCphi (Class.cv (nb090AlphaDummy620 v u h)))).fv ∪
        ((synCphi (Class.cv (nb090AlphaDummy620 v u h)))).fv) :=
  by
  simpa only [nb090AlphaDummy652] using
    freshVar_not_mem
      (((synCphi (Class.cv (nb090AlphaDummy620 v u h)))).fv ∪
        ((synCphi (Class.cv (nb090AlphaDummy620 v u h)))).fv)
      0

theorem nb090_fresh_1080 (A : Class) :
    (nb090AlphaDummy695 A) ∉
      (((synCphi (Class.cv (nb090AlphaDummy662 A)))).fv ∪
        ((synCphi (Class.cv (nb090AlphaDummy662 A)))).fv) :=
  by
  simpa only [nb090AlphaDummy695] using
    freshVar_not_mem
      (((synCphi (Class.cv (nb090AlphaDummy662 A)))).fv ∪
        ((synCphi (Class.cv (nb090AlphaDummy662 A)))).fv)
      0

theorem nb090_fresh_1081 (u : Var) :
    (nb090AlphaDummy696 u) ∉
      (((synCphi (Class.cv (nb090AlphaDummy664 u)))).fv ∪
        ((synCphi (Class.cv (nb090AlphaDummy664 u)))).fv) :=
  by
  simpa only [nb090AlphaDummy696] using
    freshVar_not_mem
      (((synCphi (Class.cv (nb090AlphaDummy664 u)))).fv ∪
        ((synCphi (Class.cv (nb090AlphaDummy664 u)))).fv)
      0

theorem nb090_fresh_1082 (A : Class) :
    (nb090AlphaDummy825 A) ∉
      (((synCphi (Class.cv (nb090AlphaDummy700 A)))).fv ∪
        ((synCphi (Class.cv (nb090AlphaDummy700 A)))).fv) :=
  by
  simpa only [nb090AlphaDummy825] using
    freshVar_not_mem
      (((synCphi (Class.cv (nb090AlphaDummy700 A)))).fv ∪
        ((synCphi (Class.cv (nb090AlphaDummy700 A)))).fv)
      0

theorem nb090_fresh_1083 (v : Var) (u : Var) (h : Var) :
    (nb090AlphaDummy826 v u h) ∉
      (((synCphi (Class.cv (nb090AlphaDummy702 v u h)))).fv ∪
        ((synCphi (Class.cv (nb090AlphaDummy702 v u h)))).fv) :=
  by
  simpa only [nb090AlphaDummy826] using
    freshVar_not_mem
      (((synCphi (Class.cv (nb090AlphaDummy702 v u h)))).fv ∪
        ((synCphi (Class.cv (nb090AlphaDummy702 v u h)))).fv)
      0

theorem nb090_fresh_1084 (A : Class) :
    (nb090AlphaDummy749 A) ∉
      (((synCphi (Class.cv (nb090AlphaDummy716 A)))).fv ∪
        ((synCphi (Class.cv (nb090AlphaDummy716 A)))).fv) :=
  by
  simpa only [nb090AlphaDummy749] using
    freshVar_not_mem
      (((synCphi (Class.cv (nb090AlphaDummy716 A)))).fv ∪
        ((synCphi (Class.cv (nb090AlphaDummy716 A)))).fv)
      0

theorem nb090_fresh_1085 (v : Var) (u : Var) (h : Var) :
    (nb090AlphaDummy750 v u h) ∉
      (((synCphi (Class.cv (nb090AlphaDummy718 v u h)))).fv ∪
        ((synCphi (Class.cv (nb090AlphaDummy718 v u h)))).fv) :=
  by
  simpa only [nb090AlphaDummy750] using
    freshVar_not_mem
      (((synCphi (Class.cv (nb090AlphaDummy718 v u h)))).fv ∪
        ((synCphi (Class.cv (nb090AlphaDummy718 v u h)))).fv)
      0

theorem nb090_fresh_1086 (A : Class) :
    (nb090AlphaDummy819 A) ∉
      (((synCphi (Class.cv (nb090AlphaDummy786 A)))).fv ∪
        ((synCphi (Class.cv (nb090AlphaDummy786 A)))).fv) :=
  by
  simpa only [nb090AlphaDummy819] using
    freshVar_not_mem
      (((synCphi (Class.cv (nb090AlphaDummy786 A)))).fv ∪
        ((synCphi (Class.cv (nb090AlphaDummy786 A)))).fv)
      0

theorem nb090_fresh_1087 (v : Var) (u : Var) (h : Var) :
    (nb090AlphaDummy820 v u h) ∉
      (((synCphi (Class.cv (nb090AlphaDummy788 v u h)))).fv ∪
        ((synCphi (Class.cv (nb090AlphaDummy788 v u h)))).fv) :=
  by
  simpa only [nb090AlphaDummy820] using
    freshVar_not_mem
      (((synCphi (Class.cv (nb090AlphaDummy788 v u h)))).fv ∪
        ((synCphi (Class.cv (nb090AlphaDummy788 v u h)))).fv)
      0

theorem nb090_fresh_1088 (A : Class) :
    (nb090AlphaDummy869 A) ∉
      (((synCphi (Class.cv (nb090AlphaDummy836 A)))).fv ∪
        ((synCphi (Class.cv (nb090AlphaDummy836 A)))).fv) :=
  by
  simpa only [nb090AlphaDummy869] using
    freshVar_not_mem
      (((synCphi (Class.cv (nb090AlphaDummy836 A)))).fv ∪
        ((synCphi (Class.cv (nb090AlphaDummy836 A)))).fv)
      0

theorem nb090_fresh_1089 (v : Var) :
    (nb090AlphaDummy870 v) ∉
      (((synCphi (Class.cv (nb090AlphaDummy838 v)))).fv ∪
        ((synCphi (Class.cv (nb090AlphaDummy838 v)))).fv) :=
  by
  simpa only [nb090AlphaDummy870] using
    freshVar_not_mem
      (((synCphi (Class.cv (nb090AlphaDummy838 v)))).fv ∪
        ((synCphi (Class.cv (nb090AlphaDummy838 v)))).fv)
      0

theorem nb090_fresh_1090 (A : Class) :
    (nb090AlphaDummy331 A) ∉
      (((synCrn (Class.cv (nb090AlphaDummy000 A)))).fv ∪
        ((synCfv (synC2nd) (Class.cv (nb090AlphaDummy002 A)))).fv) :=
  by
  simpa only [nb090AlphaDummy331] using
    freshVar_not_mem
      (((synCrn (Class.cv (nb090AlphaDummy000 A)))).fv ∪
        ((synCfv (synC2nd) (Class.cv (nb090AlphaDummy002 A)))).fv)
      0

theorem nb090_fresh_1091 (v : Var) (h : Var) :
    (nb090AlphaDummy332 v h) ∉
      (((synCrn (Class.cv h))).fv ∪ ((synCfv (synC2nd) (Class.cv v))).fv) :=
  by
  simpa only [nb090AlphaDummy332] using
    freshVar_not_mem
      (((synCrn (Class.cv h))).fv ∪ ((synCfv (synC2nd) (Class.cv v))).fv) 0

theorem nb090_fresh_1092 (A : Class) : (nb090AlphaDummy000 A) ∉ ((A).fv) := by
  simpa only [nb090AlphaDummy000] using freshVar_not_mem ((A).fv) 0

theorem nb090_fresh_1093 (A : Class) : (nb090AlphaDummy001 A) ∉ ((A).fv) := by
  simpa only [nb090AlphaDummy001] using freshVar_not_mem ((A).fv) 1

theorem nb090_fresh_1094 (A : Class) : (nb090AlphaDummy002 A) ∉ ((A).fv) := by
  simpa only [nb090AlphaDummy002] using freshVar_not_mem ((A).fv) 2

theorem nb090_distinct_1095 (A : Class) :
    (nb090AlphaDummy000 A) ≠ (nb090AlphaDummy001 A) := by
  simpa only [nb090AlphaDummy000, nb090AlphaDummy001] using
    (freshVar_injective ((A).fv) (i := 0) (j := 1) (by decide))

theorem nb090_distinct_1096 (A : Class) :
    (nb090AlphaDummy000 A) ≠ (nb090AlphaDummy002 A) := by
  simpa only [nb090AlphaDummy000, nb090AlphaDummy002] using
    (freshVar_injective ((A).fv) (i := 0) (j := 2) (by decide))

theorem nb090_distinct_1097 (A : Class) :
    (nb090AlphaDummy001 A) ≠ (nb090AlphaDummy002 A) := by
  simpa only [nb090AlphaDummy001, nb090AlphaDummy002] using
    (freshVar_injective ((A).fv) (i := 1) (j := 2) (by decide))

theorem nb090_fresh_1098 (A : Class) :
    (nb090AlphaDummy003 A) ∉
      (({(nb090AlphaDummy001 A)} : Finset Var) ∪ ({(nb090AlphaDummy002 A)} : Finset Var) ∪
        ((synWa (synWa (Wff.classMem (Class.cv (nb090AlphaDummy001 A)) (synChwcodes A))
              (Wff.classMem (Class.cv (nb090AlphaDummy002 A)) (synChwcodes A)))
            (synWex (nb090AlphaDummy000 A) (synWiso (Class.cv (nb090AlphaDummy000 A))
                (synCfv (synC1st) (Class.cv (nb090AlphaDummy001 A)))
                (synCfv (synC1st) (Class.cv (nb090AlphaDummy002 A)))
                (synCfv (synC2nd) (Class.cv (nb090AlphaDummy001 A)))
                (synCfv (synC2nd) (Class.cv (nb090AlphaDummy002 A))))))).fv) :=
  by
  simpa only [nb090AlphaDummy003] using
    freshVar_not_mem
      (({(nb090AlphaDummy001 A)} : Finset Var) ∪ ({(nb090AlphaDummy002 A)} : Finset Var) ∪
        ((synWa (synWa (Wff.classMem (Class.cv (nb090AlphaDummy001 A)) (synChwcodes A))
              (Wff.classMem (Class.cv (nb090AlphaDummy002 A)) (synChwcodes A)))
            (synWex (nb090AlphaDummy000 A) (synWiso (Class.cv (nb090AlphaDummy000 A))
                (synCfv (synC1st) (Class.cv (nb090AlphaDummy001 A)))
                (synCfv (synC1st) (Class.cv (nb090AlphaDummy002 A)))
                (synCfv (synC2nd) (Class.cv (nb090AlphaDummy001 A)))
                (synCfv (synC2nd) (Class.cv (nb090AlphaDummy002 A))))))).fv)
      0

theorem nb090_fresh_1099 (A : Class) :
    (nb090AlphaDummy055 A) ∉
      (({(nb090AlphaDummy049 A)} : Finset Var) ∪ ({(nb090AlphaDummy050 A)} : Finset Var) ∪
        ((synWex (nb090AlphaDummy051 A) (synWa
              (synWbr (Class.cv (nb090AlphaDummy049 A))
                (synCcnv (Class.cv (nb090AlphaDummy000 A)))
                (Class.cv (nb090AlphaDummy051 A)))
              (synWbr (Class.cv (nb090AlphaDummy051 A)) (Class.cv (nb090AlphaDummy000 A))
                (Class.cv (nb090AlphaDummy050 A)))))).fv) :=
  by
  simpa only [nb090AlphaDummy055] using
    freshVar_not_mem
      (({(nb090AlphaDummy049 A)} : Finset Var) ∪ ({(nb090AlphaDummy050 A)} : Finset Var) ∪
        ((synWex (nb090AlphaDummy051 A) (synWa
              (synWbr (Class.cv (nb090AlphaDummy049 A))
                (synCcnv (Class.cv (nb090AlphaDummy000 A)))
                (Class.cv (nb090AlphaDummy051 A)))
              (synWbr (Class.cv (nb090AlphaDummy051 A)) (Class.cv (nb090AlphaDummy000 A))
                (Class.cv (nb090AlphaDummy050 A)))))).fv)
      0

theorem nb090_fresh_1100 (h : Var) :
    (nb090AlphaDummy056 h) ∉
      (({(nb090AlphaDummy052 h)} : Finset Var) ∪ ({(nb090AlphaDummy053 h)} : Finset Var) ∪
        ((synWex (nb090AlphaDummy054 h) (synWa
              (synWbr (Class.cv (nb090AlphaDummy052 h)) (synCcnv (Class.cv h))
                (Class.cv (nb090AlphaDummy054 h)))
              (synWbr (Class.cv (nb090AlphaDummy054 h)) (Class.cv h)
                (Class.cv (nb090AlphaDummy053 h)))))).fv) :=
  by
  simpa only [nb090AlphaDummy056] using
    freshVar_not_mem
      (({(nb090AlphaDummy052 h)} : Finset Var) ∪ ({(nb090AlphaDummy053 h)} : Finset Var) ∪
        ((synWex (nb090AlphaDummy054 h) (synWa
              (synWbr (Class.cv (nb090AlphaDummy052 h)) (synCcnv (Class.cv h))
                (Class.cv (nb090AlphaDummy054 h)))
              (synWbr (Class.cv (nb090AlphaDummy054 h)) (Class.cv h)
                (Class.cv (nb090AlphaDummy053 h)))))).fv)
      0

theorem nb090_fresh_1101 (A : Class) :
    (nb090AlphaDummy133 A) ∉
      (({(nb090AlphaDummy129 A)} : Finset Var) ∪ ({(nb090AlphaDummy130 A)} : Finset Var) ∪
        ((synWbr (Class.cv (nb090AlphaDummy130 A)) (Class.cv (nb090AlphaDummy000 A))
            (Class.cv (nb090AlphaDummy129 A)))).fv) :=
  by
  simpa only [nb090AlphaDummy133] using
    freshVar_not_mem
      (({(nb090AlphaDummy129 A)} : Finset Var) ∪ ({(nb090AlphaDummy130 A)} : Finset Var) ∪
        ((synWbr (Class.cv (nb090AlphaDummy130 A)) (Class.cv (nb090AlphaDummy000 A))
            (Class.cv (nb090AlphaDummy129 A)))).fv)
      0

theorem nb090_fresh_1102 (h : Var) :
    (nb090AlphaDummy134 h) ∉
      (({(nb090AlphaDummy131 h)} : Finset Var) ∪ ({(nb090AlphaDummy132 h)} : Finset Var) ∪
        ((synWbr (Class.cv (nb090AlphaDummy132 h)) (Class.cv h)
            (Class.cv (nb090AlphaDummy131 h)))).fv) :=
  by
  simpa only [nb090AlphaDummy134] using
    freshVar_not_mem
      (({(nb090AlphaDummy131 h)} : Finset Var) ∪ ({(nb090AlphaDummy132 h)} : Finset Var) ∪
        ((synWbr (Class.cv (nb090AlphaDummy132 h)) (Class.cv h)
            (Class.cv (nb090AlphaDummy131 h)))).fv)
      0

theorem nb090_fresh_1103 (A : Class) :
    (nb090AlphaDummy285 A) ∉
      (({(nb090AlphaDummy283 A)} : Finset Var) ∪
        ((synWbr (Class.cv (nb090AlphaDummy001 A)) (synC2nd)
            (Class.cv (nb090AlphaDummy283 A)))).fv) :=
  by
  simpa only [nb090AlphaDummy285] using
    freshVar_not_mem
      (({(nb090AlphaDummy283 A)} : Finset Var) ∪
        ((synWbr (Class.cv (nb090AlphaDummy001 A)) (synC2nd)
            (Class.cv (nb090AlphaDummy283 A)))).fv)
      0

theorem nb090_fresh_1104 (u : Var) :
    (nb090AlphaDummy286 u) ∉
      (({(nb090AlphaDummy284 u)} : Finset Var) ∪
        ((synWbr (Class.cv u) (synC2nd) (Class.cv (nb090AlphaDummy284 u)))).fv) :=
  by
  simpa only [nb090AlphaDummy286] using
    freshVar_not_mem
      (({(nb090AlphaDummy284 u)} : Finset Var) ∪
        ((synWbr (Class.cv u) (synC2nd) (Class.cv (nb090AlphaDummy284 u)))).fv)
      0

theorem nb090_fresh_1105 (A : Class) :
    (nb090AlphaDummy375 A) ∉
      (({(nb090AlphaDummy373 A)} : Finset Var) ∪
        ((synWbr (Class.cv (nb090AlphaDummy002 A)) (synC2nd)
            (Class.cv (nb090AlphaDummy373 A)))).fv) :=
  by
  simpa only [nb090AlphaDummy375] using
    freshVar_not_mem
      (({(nb090AlphaDummy373 A)} : Finset Var) ∪
        ((synWbr (Class.cv (nb090AlphaDummy002 A)) (synC2nd)
            (Class.cv (nb090AlphaDummy373 A)))).fv)
      0

theorem nb090_fresh_1106 (v : Var) :
    (nb090AlphaDummy376 v) ∉
      (({(nb090AlphaDummy374 v)} : Finset Var) ∪
        ((synWbr (Class.cv v) (synC2nd) (Class.cv (nb090AlphaDummy374 v)))).fv) :=
  by
  simpa only [nb090AlphaDummy376] using
    freshVar_not_mem
      (({(nb090AlphaDummy374 v)} : Finset Var) ∪
        ((synWbr (Class.cv v) (synC2nd) (Class.cv (nb090AlphaDummy374 v)))).fv)
      0

theorem nb090_fresh_1107 (A : Class) :
    (nb090AlphaDummy429 A) ∉
      (({(nb090AlphaDummy423 A)} : Finset Var) ∪ ({(nb090AlphaDummy424 A)} : Finset Var) ∪
        ((synWex (nb090AlphaDummy425 A) (synWa
              (synWbr (Class.cv (nb090AlphaDummy423 A))
                (synCcnv (synCcnv (Class.cv (nb090AlphaDummy000 A))))
                (Class.cv (nb090AlphaDummy425 A)))
              (synWbr (Class.cv (nb090AlphaDummy425 A))
                (synCcnv (Class.cv (nb090AlphaDummy000 A)))
                (Class.cv (nb090AlphaDummy424 A)))))).fv) :=
  by
  simpa only [nb090AlphaDummy429] using
    freshVar_not_mem
      (({(nb090AlphaDummy423 A)} : Finset Var) ∪ ({(nb090AlphaDummy424 A)} : Finset Var) ∪
        ((synWex (nb090AlphaDummy425 A) (synWa
              (synWbr (Class.cv (nb090AlphaDummy423 A))
                (synCcnv (synCcnv (Class.cv (nb090AlphaDummy000 A))))
                (Class.cv (nb090AlphaDummy425 A)))
              (synWbr (Class.cv (nb090AlphaDummy425 A))
                (synCcnv (Class.cv (nb090AlphaDummy000 A)))
                (Class.cv (nb090AlphaDummy424 A)))))).fv)
      0

theorem nb090_fresh_1108 (h : Var) :
    (nb090AlphaDummy430 h) ∉
      (({(nb090AlphaDummy426 h)} : Finset Var) ∪ ({(nb090AlphaDummy427 h)} : Finset Var) ∪
        ((synWex (nb090AlphaDummy428 h) (synWa
              (synWbr (Class.cv (nb090AlphaDummy426 h))
                (synCcnv (synCcnv (Class.cv h))) (Class.cv (nb090AlphaDummy428 h)))
              (synWbr (Class.cv (nb090AlphaDummy428 h)) (synCcnv (Class.cv h))
                (Class.cv (nb090AlphaDummy427 h)))))).fv) :=
  by
  simpa only [nb090AlphaDummy430] using
    freshVar_not_mem
      (({(nb090AlphaDummy426 h)} : Finset Var) ∪ ({(nb090AlphaDummy427 h)} : Finset Var) ∪
        ((synWex (nb090AlphaDummy428 h) (synWa
              (synWbr (Class.cv (nb090AlphaDummy426 h))
                (synCcnv (synCcnv (Class.cv h))) (Class.cv (nb090AlphaDummy428 h)))
              (synWbr (Class.cv (nb090AlphaDummy428 h)) (synCcnv (Class.cv h))
                (Class.cv (nb090AlphaDummy427 h)))))).fv)
      0

theorem nb090_fresh_1109 (A : Class) :
    (nb090AlphaDummy507 A) ∉
      (({(nb090AlphaDummy503 A)} : Finset Var) ∪ ({(nb090AlphaDummy504 A)} : Finset Var) ∪
        ((synWbr (Class.cv (nb090AlphaDummy504 A))
            (synCcnv (Class.cv (nb090AlphaDummy000 A)))
            (Class.cv (nb090AlphaDummy503 A)))).fv) :=
  by
  simpa only [nb090AlphaDummy507] using
    freshVar_not_mem
      (({(nb090AlphaDummy503 A)} : Finset Var) ∪ ({(nb090AlphaDummy504 A)} : Finset Var) ∪
        ((synWbr (Class.cv (nb090AlphaDummy504 A))
            (synCcnv (Class.cv (nb090AlphaDummy000 A)))
            (Class.cv (nb090AlphaDummy503 A)))).fv)
      0

theorem nb090_fresh_1110 (h : Var) :
    (nb090AlphaDummy508 h) ∉
      (({(nb090AlphaDummy505 h)} : Finset Var) ∪ ({(nb090AlphaDummy506 h)} : Finset Var) ∪
        ((synWbr (Class.cv (nb090AlphaDummy506 h)) (synCcnv (Class.cv h))
            (Class.cv (nb090AlphaDummy505 h)))).fv) :=
  by
  simpa only [nb090AlphaDummy508] using
    freshVar_not_mem
      (({(nb090AlphaDummy505 h)} : Finset Var) ∪ ({(nb090AlphaDummy506 h)} : Finset Var) ∪
        ((synWbr (Class.cv (nb090AlphaDummy506 h)) (synCcnv (Class.cv h))
            (Class.cv (nb090AlphaDummy505 h)))).fv)
      0

theorem nb090_fresh_1111 (A : Class) :
    (nb090AlphaDummy655 A) ∉
      (({(nb090AlphaDummy653 A)} : Finset Var) ∪
        ((synWbr (Class.cv (nb090AlphaDummy001 A)) (synC1st)
            (Class.cv (nb090AlphaDummy653 A)))).fv) :=
  by
  simpa only [nb090AlphaDummy655] using
    freshVar_not_mem
      (({(nb090AlphaDummy653 A)} : Finset Var) ∪
        ((synWbr (Class.cv (nb090AlphaDummy001 A)) (synC1st)
            (Class.cv (nb090AlphaDummy653 A)))).fv)
      0

theorem nb090_fresh_1112 (u : Var) :
    (nb090AlphaDummy656 u) ∉
      (({(nb090AlphaDummy654 u)} : Finset Var) ∪
        ((synWbr (Class.cv u) (synC1st) (Class.cv (nb090AlphaDummy654 u)))).fv) :=
  by
  simpa only [nb090AlphaDummy656] using
    freshVar_not_mem
      (({(nb090AlphaDummy654 u)} : Finset Var) ∪
        ((synWbr (Class.cv u) (synC1st) (Class.cv (nb090AlphaDummy654 u)))).fv)
      0

theorem nb090_fresh_1113 (A : Class) :
    (nb090AlphaDummy709 A) ∉
      (({(nb090AlphaDummy707 A)} : Finset Var) ∪
        ((synWbr (Class.cv (nb090AlphaDummy041 A)) (Class.cv (nb090AlphaDummy000 A))
            (Class.cv (nb090AlphaDummy707 A)))).fv) :=
  by
  simpa only [nb090AlphaDummy709] using
    freshVar_not_mem
      (({(nb090AlphaDummy707 A)} : Finset Var) ∪
        ((synWbr (Class.cv (nb090AlphaDummy041 A)) (Class.cv (nb090AlphaDummy000 A))
            (Class.cv (nb090AlphaDummy707 A)))).fv)
      0

theorem nb090_fresh_1114 (v : Var) (u : Var) (h : Var) :
    (nb090AlphaDummy710 v u h) ∉
      (({(nb090AlphaDummy708 v u h)} : Finset Var) ∪
        ((synWbr (Class.cv (nb090AlphaDummy043 v u h)) (Class.cv h)
            (Class.cv (nb090AlphaDummy708 v u h)))).fv) :=
  by
  simpa only [nb090AlphaDummy710] using
    freshVar_not_mem
      (({(nb090AlphaDummy708 v u h)} : Finset Var) ∪
        ((synWbr (Class.cv (nb090AlphaDummy043 v u h)) (Class.cv h)
            (Class.cv (nb090AlphaDummy708 v u h)))).fv)
      0

theorem nb090_fresh_1115 (A : Class) :
    (nb090AlphaDummy779 A) ∉
      (({(nb090AlphaDummy777 A)} : Finset Var) ∪
        ((synWbr (Class.cv (nb090AlphaDummy042 A)) (Class.cv (nb090AlphaDummy000 A))
            (Class.cv (nb090AlphaDummy777 A)))).fv) :=
  by
  simpa only [nb090AlphaDummy779] using
    freshVar_not_mem
      (({(nb090AlphaDummy777 A)} : Finset Var) ∪
        ((synWbr (Class.cv (nb090AlphaDummy042 A)) (Class.cv (nb090AlphaDummy000 A))
            (Class.cv (nb090AlphaDummy777 A)))).fv)
      0

theorem nb090_fresh_1116 (v : Var) (u : Var) (h : Var) :
    (nb090AlphaDummy780 v u h) ∉
      (({(nb090AlphaDummy778 v u h)} : Finset Var) ∪
        ((synWbr (Class.cv (nb090AlphaDummy044 v u h)) (Class.cv h)
            (Class.cv (nb090AlphaDummy778 v u h)))).fv) :=
  by
  simpa only [nb090AlphaDummy780] using
    freshVar_not_mem
      (({(nb090AlphaDummy778 v u h)} : Finset Var) ∪
        ((synWbr (Class.cv (nb090AlphaDummy044 v u h)) (Class.cv h)
            (Class.cv (nb090AlphaDummy778 v u h)))).fv)
      0

theorem nb090_fresh_1117 (A : Class) :
    (nb090AlphaDummy829 A) ∉
      (({(nb090AlphaDummy827 A)} : Finset Var) ∪
        ((synWbr (Class.cv (nb090AlphaDummy002 A)) (synC1st)
            (Class.cv (nb090AlphaDummy827 A)))).fv) :=
  by
  simpa only [nb090AlphaDummy829] using
    freshVar_not_mem
      (({(nb090AlphaDummy827 A)} : Finset Var) ∪
        ((synWbr (Class.cv (nb090AlphaDummy002 A)) (synC1st)
            (Class.cv (nb090AlphaDummy827 A)))).fv)
      0

theorem nb090_fresh_1118 (v : Var) :
    (nb090AlphaDummy830 v) ∉
      (({(nb090AlphaDummy828 v)} : Finset Var) ∪
        ((synWbr (Class.cv v) (synC1st) (Class.cv (nb090AlphaDummy828 v)))).fv) :=
  by
  simpa only [nb090AlphaDummy830] using
    freshVar_not_mem
      (({(nb090AlphaDummy828 v)} : Finset Var) ∪
        ((synWbr (Class.cv v) (synC1st) (Class.cv (nb090AlphaDummy828 v)))).fv)
      0

theorem nb090_fresh_1119 (v : Var) (u : Var) (A : Class) (h : Var) :
    (nb090AlphaDummy004 v u A h) ∉
      (({ u } : Finset Var) ∪ ({ v } : Finset Var) ∪ ((synWa
            (synWa (Wff.classMem (Class.cv u) (synChwcodes A))
              (Wff.classMem (Class.cv v) (synChwcodes A))) (synWex h
              (synWiso (Class.cv h) (synCfv (synC1st) (Class.cv u))
                (synCfv (synC1st) (Class.cv v)) (synCfv (synC2nd) (Class.cv u))
                (synCfv (synC2nd) (Class.cv v)))))).fv) :=
  by
  simpa only [nb090AlphaDummy004] using
    freshVar_not_mem
      (({ u } : Finset Var) ∪ ({ v } : Finset Var) ∪ ((synWa
            (synWa (Wff.classMem (Class.cv u) (synChwcodes A))
              (Wff.classMem (Class.cv v) (synChwcodes A))) (synWex h
              (synWiso (Class.cv h) (synCfv (synC1st) (Class.cv u))
                (synCfv (synC1st) (Class.cv v)) (synCfv (synC2nd) (Class.cv u))
                (synCfv (synC2nd) (Class.cv v)))))).fv)
      0

theorem nb090_support_mem_0000 (A : Class) :
    (nb090AlphaDummy001 A) ∈
      (({(nb090AlphaDummy001 A)} : Finset Var) ∪ ({(nb090AlphaDummy002 A)} : Finset Var) ∪
        ((synWa (synWa (Wff.classMem (Class.cv (nb090AlphaDummy001 A)) (synChwcodes A))
              (Wff.classMem (Class.cv (nb090AlphaDummy002 A)) (synChwcodes A)))
            (synWex (nb090AlphaDummy000 A) (synWiso (Class.cv (nb090AlphaDummy000 A))
                (synCfv (synC1st) (Class.cv (nb090AlphaDummy001 A)))
                (synCfv (synC1st) (Class.cv (nb090AlphaDummy002 A)))
                (synCfv (synC2nd) (Class.cv (nb090AlphaDummy001 A)))
                (synCfv (synC2nd) (Class.cv (nb090AlphaDummy002 A))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  with_reducible rw [Finset.mem_union]
  left
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0001 (v : Var) (u : Var) (A : Class) (h : Var) :
    u ∈
      (({ u } : Finset Var) ∪ ({ v } : Finset Var) ∪ ((synWa
            (synWa (Wff.classMem (Class.cv u) (synChwcodes A))
              (Wff.classMem (Class.cv v) (synChwcodes A))) (synWex h
              (synWiso (Class.cv h) (synCfv (synC1st) (Class.cv u))
                (synCfv (synC1st) (Class.cv v)) (synCfv (synC2nd) (Class.cv u))
                (synCfv (synC2nd) (Class.cv v)))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  with_reducible rw [Finset.mem_union]
  left
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0002 (A : Class) :
    (nb090AlphaDummy002 A) ∈
      (({(nb090AlphaDummy001 A)} : Finset Var) ∪ ({(nb090AlphaDummy002 A)} : Finset Var) ∪
        ((synWa (synWa (Wff.classMem (Class.cv (nb090AlphaDummy001 A)) (synChwcodes A))
              (Wff.classMem (Class.cv (nb090AlphaDummy002 A)) (synChwcodes A)))
            (synWex (nb090AlphaDummy000 A) (synWiso (Class.cv (nb090AlphaDummy000 A))
                (synCfv (synC1st) (Class.cv (nb090AlphaDummy001 A)))
                (synCfv (synC1st) (Class.cv (nb090AlphaDummy002 A)))
                (synCfv (synC2nd) (Class.cv (nb090AlphaDummy001 A)))
                (synCfv (synC2nd) (Class.cv (nb090AlphaDummy002 A))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  with_reducible rw [Finset.mem_union]
  right
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0003 (v : Var) (u : Var) (A : Class) (h : Var) :
    v ∈
      (({ u } : Finset Var) ∪ ({ v } : Finset Var) ∪ ((synWa
            (synWa (Wff.classMem (Class.cv u) (synChwcodes A))
              (Wff.classMem (Class.cv v) (synChwcodes A))) (synWex h
              (synWiso (Class.cv h) (synCfv (synC1st) (Class.cv u))
                (synCfv (synC1st) (Class.cv v)) (synCfv (synC2nd) (Class.cv u))
                (synCfv (synC2nd) (Class.cv v)))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  with_reducible rw [Finset.mem_union]
  right
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0004 (A : Class) :
    (nb090AlphaDummy001 A) ∈
      (((Class.cv (nb090AlphaDummy001 A))).fv ∪ ((Class.cv (nb090AlphaDummy002 A))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0005 (A : Class) :
    (nb090AlphaDummy001 A) ∈
      (((synCcompl (Class.cab (nb090AlphaDummy005 A)
              (synWrex (nb090AlphaDummy006 A) (Class.cv (nb090AlphaDummy001 A))
                (Wff.classEq (Class.cv (nb090AlphaDummy005 A))
                  (synCphi (Class.cv (nb090AlphaDummy006 A)))))))).fv ∪ ((synCcompl
            (Class.cab (nb090AlphaDummy005 A)
              (synWrex (nb090AlphaDummy006 A) (Class.cv (nb090AlphaDummy002 A))
                (Wff.classEq (Class.cv (nb090AlphaDummy005 A))
                  (synCun (synCphi (Class.cv (nb090AlphaDummy006 A)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb090AlphaDummy001 A) ≠ (nb090AlphaDummy005 A) from (by
          unfold nb090AlphaDummy005;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0004 A) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb090AlphaDummy001 A) ≠ (nb090AlphaDummy006 A) from (by
            unfold nb090AlphaDummy006;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0004 A) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb090_support_mem_0006 (v : Var) (u : Var) :
    u ∈ (((Class.cv u)).fv ∪ ((Class.cv v)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0007 (v : Var) (u : Var) :
    u ∈
      (((synCcompl (Class.cab (nb090AlphaDummy007 v u)
              (synWrex (nb090AlphaDummy008 v u) (Class.cv u)
                (Wff.classEq (Class.cv (nb090AlphaDummy007 v u))
                  (synCphi (Class.cv (nb090AlphaDummy008 v u)))))))).fv ∪ ((synCcompl
            (Class.cab (nb090AlphaDummy007 v u)
              (synWrex (nb090AlphaDummy008 v u) (Class.cv v)
                (Wff.classEq (Class.cv (nb090AlphaDummy007 v u))
                  (synCun (synCphi (Class.cv (nb090AlphaDummy008 v u)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show u ≠ (nb090AlphaDummy007 v u) from (by
          unfold nb090AlphaDummy007;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0006 v u) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show u ≠ (nb090AlphaDummy008 v u) from (by
            unfold nb090AlphaDummy008;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0006 v u) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb090_support_mem_0008 (A : Class) :
    (nb090AlphaDummy001 A) ∈
      (((Class.cab (nb090AlphaDummy005 A)
            (synWrex (nb090AlphaDummy006 A) (Class.cv (nb090AlphaDummy001 A))
              (Wff.classEq (Class.cv (nb090AlphaDummy005 A))
                (synCphi (Class.cv (nb090AlphaDummy006 A))))))).fv ∪
        ((Class.cab (nb090AlphaDummy005 A)
            (synWrex (nb090AlphaDummy006 A) (Class.cv (nb090AlphaDummy001 A))
              (Wff.classEq (Class.cv (nb090AlphaDummy005 A))
                (synCphi (Class.cv (nb090AlphaDummy006 A))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb090AlphaDummy001 A) ≠ (nb090AlphaDummy005 A) from (by
          unfold nb090AlphaDummy005;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0004 A) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb090AlphaDummy001 A) ≠ (nb090AlphaDummy006 A) from (by
            unfold nb090AlphaDummy006;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0004 A) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb090_support_mem_0009 (v : Var) (u : Var) :
    u ∈
      (((Class.cab (nb090AlphaDummy007 v u)
            (synWrex (nb090AlphaDummy008 v u) (Class.cv u)
              (Wff.classEq (Class.cv (nb090AlphaDummy007 v u))
                (synCphi (Class.cv (nb090AlphaDummy008 v u))))))).fv ∪
        ((Class.cab (nb090AlphaDummy007 v u)
            (synWrex (nb090AlphaDummy008 v u) (Class.cv u)
              (Wff.classEq (Class.cv (nb090AlphaDummy007 v u))
                (synCphi (Class.cv (nb090AlphaDummy008 v u))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show u ≠ (nb090AlphaDummy007 v u) from (by
          unfold nb090AlphaDummy007;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0006 v u) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show u ≠ (nb090AlphaDummy008 v u) from (by
            unfold nb090AlphaDummy008;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0006 v u) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb090_support_mem_0010 (A : Class) :
    (nb090AlphaDummy006 A) ∈ (((Class.cv (nb090AlphaDummy006 A))).fv) :=
  by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0011 (v : Var) (u : Var) :
    (nb090AlphaDummy008 v u) ∈ (((Class.cv (nb090AlphaDummy008 v u))).fv) :=
  by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0012 (A : Class) :
    (nb090AlphaDummy013 A) ∈
      (((Wff.classMem (Class.cv (nb090AlphaDummy013 A)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb090AlphaDummy013 A)) (synC1c))).fv ∪
        ((Class.cv (nb090AlphaDummy013 A))).fv) :=
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

theorem nb090_support_mem_0013 (v : Var) (u : Var) :
    (nb090AlphaDummy015 v u) ∈
      (((Wff.classMem (Class.cv (nb090AlphaDummy015 v u)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb090AlphaDummy015 v u)) (synC1c))).fv ∪
        ((Class.cv (nb090AlphaDummy015 v u))).fv) :=
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

theorem nb090_support_mem_0014 (A : Class) :
    (nb090AlphaDummy013 A) ∈
      (((Class.cv (nb090AlphaDummy013 A))).fv ∪ ((synC1c)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0015 (v : Var) (u : Var) :
    (nb090AlphaDummy015 v u) ∈
      (((Class.cv (nb090AlphaDummy015 v u))).fv ∪ ((synC1c)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0016 (A : Class) :
    (nb090AlphaDummy020 A) ∈
      (((synCnin (Class.cv (nb090AlphaDummy020 A))
            (Class.cv (nb090AlphaDummy021 A)))).fv ∪
        ((synCnin (Class.cv (nb090AlphaDummy020 A))
            (Class.cv (nb090AlphaDummy021 A)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0017 (v : Var) (u : Var) :
    (nb090AlphaDummy023 v u) ∈
      (((synCnin (Class.cv (nb090AlphaDummy023 v u))
            (Class.cv (nb090AlphaDummy024 v u)))).fv ∪
        ((synCnin (Class.cv (nb090AlphaDummy023 v u))
            (Class.cv (nb090AlphaDummy024 v u)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0018 (A : Class) :
    (nb090AlphaDummy020 A) ∈
      (((Class.cv (nb090AlphaDummy020 A))).fv ∪ ((Class.cv (nb090AlphaDummy021 A))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0019 (v : Var) (u : Var) :
    (nb090AlphaDummy023 v u) ∈
      (((Class.cv (nb090AlphaDummy023 v u))).fv ∪
        ((Class.cv (nb090AlphaDummy024 v u))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0020 (A : Class) :
    (nb090AlphaDummy021 A) ∈
      (((synCnin (Class.cv (nb090AlphaDummy020 A))
            (Class.cv (nb090AlphaDummy021 A)))).fv ∪
        ((synCnin (Class.cv (nb090AlphaDummy020 A))
            (Class.cv (nb090AlphaDummy021 A)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0021 (v : Var) (u : Var) :
    (nb090AlphaDummy024 v u) ∈
      (((synCnin (Class.cv (nb090AlphaDummy023 v u))
            (Class.cv (nb090AlphaDummy024 v u)))).fv ∪
        ((synCnin (Class.cv (nb090AlphaDummy023 v u))
            (Class.cv (nb090AlphaDummy024 v u)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0022 (A : Class) :
    (nb090AlphaDummy021 A) ∈
      (((Class.cv (nb090AlphaDummy020 A))).fv ∪ ((Class.cv (nb090AlphaDummy021 A))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0023 (v : Var) (u : Var) :
    (nb090AlphaDummy024 v u) ∈
      (((Class.cv (nb090AlphaDummy023 v u))).fv ∪
        ((Class.cv (nb090AlphaDummy024 v u))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0024 (A : Class) :
    (nb090AlphaDummy020 A) ∈
      (((synCcompl (Class.cv (nb090AlphaDummy020 A)))).fv ∪
        ((synCcompl (Class.cv (nb090AlphaDummy021 A)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0025 (v : Var) (u : Var) :
    (nb090AlphaDummy023 v u) ∈
      (((synCcompl (Class.cv (nb090AlphaDummy023 v u)))).fv ∪
        ((synCcompl (Class.cv (nb090AlphaDummy024 v u)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0026 (A : Class) :
    (nb090AlphaDummy020 A) ∈
      (((Class.cv (nb090AlphaDummy020 A))).fv ∪ ((Class.cv (nb090AlphaDummy020 A))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0027 (v : Var) (u : Var) :
    (nb090AlphaDummy023 v u) ∈
      (((Class.cv (nb090AlphaDummy023 v u))).fv ∪
        ((Class.cv (nb090AlphaDummy023 v u))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0028 (A : Class) :
    (nb090AlphaDummy021 A) ∈
      (((synCcompl (Class.cv (nb090AlphaDummy020 A)))).fv ∪
        ((synCcompl (Class.cv (nb090AlphaDummy021 A)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0029 (v : Var) (u : Var) :
    (nb090AlphaDummy024 v u) ∈
      (((synCcompl (Class.cv (nb090AlphaDummy023 v u)))).fv ∪
        ((synCcompl (Class.cv (nb090AlphaDummy024 v u)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0030 (A : Class) :
    (nb090AlphaDummy021 A) ∈
      (((Class.cv (nb090AlphaDummy021 A))).fv ∪ ((Class.cv (nb090AlphaDummy021 A))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0031 (v : Var) (u : Var) :
    (nb090AlphaDummy024 v u) ∈
      (((Class.cv (nb090AlphaDummy024 v u))).fv ∪
        ((Class.cv (nb090AlphaDummy024 v u))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0032 (A : Class) :
    (nb090AlphaDummy002 A) ∈
      (((Class.cv (nb090AlphaDummy001 A))).fv ∪ ((Class.cv (nb090AlphaDummy002 A))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0033 (A : Class) :
    (nb090AlphaDummy002 A) ∈
      (((synCcompl (Class.cab (nb090AlphaDummy005 A)
              (synWrex (nb090AlphaDummy006 A) (Class.cv (nb090AlphaDummy001 A))
                (Wff.classEq (Class.cv (nb090AlphaDummy005 A))
                  (synCphi (Class.cv (nb090AlphaDummy006 A)))))))).fv ∪ ((synCcompl
            (Class.cab (nb090AlphaDummy005 A)
              (synWrex (nb090AlphaDummy006 A) (Class.cv (nb090AlphaDummy002 A))
                (Wff.classEq (Class.cv (nb090AlphaDummy005 A))
                  (synCun (synCphi (Class.cv (nb090AlphaDummy006 A)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb090AlphaDummy002 A) ≠ (nb090AlphaDummy005 A) from (by
          unfold nb090AlphaDummy005;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0032 A) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb090AlphaDummy002 A) ≠ (nb090AlphaDummy006 A) from (by
            unfold nb090AlphaDummy006;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0032 A) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb090_support_mem_0034 (v : Var) (u : Var) :
    v ∈ (((Class.cv u)).fv ∪ ((Class.cv v)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0035 (v : Var) (u : Var) :
    v ∈
      (((synCcompl (Class.cab (nb090AlphaDummy007 v u)
              (synWrex (nb090AlphaDummy008 v u) (Class.cv u)
                (Wff.classEq (Class.cv (nb090AlphaDummy007 v u))
                  (synCphi (Class.cv (nb090AlphaDummy008 v u)))))))).fv ∪ ((synCcompl
            (Class.cab (nb090AlphaDummy007 v u)
              (synWrex (nb090AlphaDummy008 v u) (Class.cv v)
                (Wff.classEq (Class.cv (nb090AlphaDummy007 v u))
                  (synCun (synCphi (Class.cv (nb090AlphaDummy008 v u)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show v ≠ (nb090AlphaDummy007 v u) from (by
          unfold nb090AlphaDummy007;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0034 v u) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show v ≠ (nb090AlphaDummy008 v u) from (by
            unfold nb090AlphaDummy008;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0034 v u) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb090_support_mem_0036 (A : Class) :
    (nb090AlphaDummy002 A) ∈
      (((Class.cab (nb090AlphaDummy005 A)
            (synWrex (nb090AlphaDummy006 A) (Class.cv (nb090AlphaDummy002 A))
              (Wff.classEq (Class.cv (nb090AlphaDummy005 A))
                (synCun (synCphi (Class.cv (nb090AlphaDummy006 A)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb090AlphaDummy005 A)
            (synWrex (nb090AlphaDummy006 A) (Class.cv (nb090AlphaDummy002 A))
              (Wff.classEq (Class.cv (nb090AlphaDummy005 A))
                (synCun (synCphi (Class.cv (nb090AlphaDummy006 A)))
                  (synCsn (synC0c))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb090AlphaDummy002 A) ≠ (nb090AlphaDummy005 A) from (by
          unfold nb090AlphaDummy005;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0032 A) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb090AlphaDummy002 A) ≠ (nb090AlphaDummy006 A) from (by
            unfold nb090AlphaDummy006;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0032 A) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb090_support_mem_0037 (v : Var) (u : Var) :
    v ∈
      (((Class.cab (nb090AlphaDummy007 v u)
            (synWrex (nb090AlphaDummy008 v u) (Class.cv v)
              (Wff.classEq (Class.cv (nb090AlphaDummy007 v u))
                (synCun (synCphi (Class.cv (nb090AlphaDummy008 v u)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb090AlphaDummy007 v u)
            (synWrex (nb090AlphaDummy008 v u) (Class.cv v)
              (Wff.classEq (Class.cv (nb090AlphaDummy007 v u))
                (synCun (synCphi (Class.cv (nb090AlphaDummy008 v u)))
                  (synCsn (synC0c))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show v ≠ (nb090AlphaDummy007 v u) from (by
          unfold nb090AlphaDummy007;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0034 v u) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show v ≠ (nb090AlphaDummy008 v u) from (by
            unfold nb090AlphaDummy008;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0034 v u) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb090_support_mem_0038 (A : Class) :
    (nb090AlphaDummy006 A) ∈
      (((synCcompl (synCphi (Class.cv (nb090AlphaDummy006 A))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0039 (v : Var) (u : Var) :
    (nb090AlphaDummy008 v u) ∈
      (((synCcompl (synCphi (Class.cv (nb090AlphaDummy008 v u))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0040 (A : Class) :
    (nb090AlphaDummy006 A) ∈
      (((synCphi (Class.cv (nb090AlphaDummy006 A)))).fv ∪
        ((synCphi (Class.cv (nb090AlphaDummy006 A)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0041 (v : Var) (u : Var) :
    (nb090AlphaDummy008 v u) ∈
      (((synCphi (Class.cv (nb090AlphaDummy008 v u)))).fv ∪
        ((synCphi (Class.cv (nb090AlphaDummy008 v u)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0042 (A : Class) :
    (nb090AlphaDummy049 A) ∈
      (({(nb090AlphaDummy049 A)} : Finset Var) ∪ ({(nb090AlphaDummy050 A)} : Finset Var) ∪
        ((synWex (nb090AlphaDummy051 A) (synWa
              (synWbr (Class.cv (nb090AlphaDummy049 A))
                (synCcnv (Class.cv (nb090AlphaDummy000 A)))
                (Class.cv (nb090AlphaDummy051 A)))
              (synWbr (Class.cv (nb090AlphaDummy051 A)) (Class.cv (nb090AlphaDummy000 A))
                (Class.cv (nb090AlphaDummy050 A)))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  with_reducible rw [Finset.mem_union]
  left
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0043 (h : Var) :
    (nb090AlphaDummy052 h) ∈
      (({(nb090AlphaDummy052 h)} : Finset Var) ∪ ({(nb090AlphaDummy053 h)} : Finset Var) ∪
        ((synWex (nb090AlphaDummy054 h) (synWa
              (synWbr (Class.cv (nb090AlphaDummy052 h)) (synCcnv (Class.cv h))
                (Class.cv (nb090AlphaDummy054 h)))
              (synWbr (Class.cv (nb090AlphaDummy054 h)) (Class.cv h)
                (Class.cv (nb090AlphaDummy053 h)))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  with_reducible rw [Finset.mem_union]
  left
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0044 (A : Class) :
    (nb090AlphaDummy050 A) ∈
      (({(nb090AlphaDummy049 A)} : Finset Var) ∪ ({(nb090AlphaDummy050 A)} : Finset Var) ∪
        ((synWex (nb090AlphaDummy051 A) (synWa
              (synWbr (Class.cv (nb090AlphaDummy049 A))
                (synCcnv (Class.cv (nb090AlphaDummy000 A)))
                (Class.cv (nb090AlphaDummy051 A)))
              (synWbr (Class.cv (nb090AlphaDummy051 A)) (Class.cv (nb090AlphaDummy000 A))
                (Class.cv (nb090AlphaDummy050 A)))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  with_reducible rw [Finset.mem_union]
  right
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0045 (h : Var) :
    (nb090AlphaDummy053 h) ∈
      (({(nb090AlphaDummy052 h)} : Finset Var) ∪ ({(nb090AlphaDummy053 h)} : Finset Var) ∪
        ((synWex (nb090AlphaDummy054 h) (synWa
              (synWbr (Class.cv (nb090AlphaDummy052 h)) (synCcnv (Class.cv h))
                (Class.cv (nb090AlphaDummy054 h)))
              (synWbr (Class.cv (nb090AlphaDummy054 h)) (Class.cv h)
                (Class.cv (nb090AlphaDummy053 h)))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  with_reducible rw [Finset.mem_union]
  right
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0046 (A : Class) :
    (nb090AlphaDummy049 A) ∈
      (((Class.cv (nb090AlphaDummy049 A))).fv ∪ ((Class.cv (nb090AlphaDummy050 A))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0047 (A : Class) :
    (nb090AlphaDummy049 A) ∈
      (((synCcompl (Class.cab (nb090AlphaDummy057 A)
              (synWrex (nb090AlphaDummy058 A) (Class.cv (nb090AlphaDummy049 A))
                (Wff.classEq (Class.cv (nb090AlphaDummy057 A))
                  (synCphi (Class.cv (nb090AlphaDummy058 A)))))))).fv ∪ ((synCcompl
            (Class.cab (nb090AlphaDummy057 A)
              (synWrex (nb090AlphaDummy058 A) (Class.cv (nb090AlphaDummy050 A))
                (Wff.classEq (Class.cv (nb090AlphaDummy057 A))
                  (synCun (synCphi (Class.cv (nb090AlphaDummy058 A)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb090AlphaDummy049 A) ≠ (nb090AlphaDummy057 A) from (by
          unfold nb090AlphaDummy057;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0046 A) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb090AlphaDummy049 A) ≠ (nb090AlphaDummy058 A) from (by
            unfold nb090AlphaDummy058;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0046 A) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb090_support_mem_0048 (h : Var) :
    (nb090AlphaDummy052 h) ∈
      (((Class.cv (nb090AlphaDummy052 h))).fv ∪ ((Class.cv (nb090AlphaDummy053 h))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0049 (h : Var) :
    (nb090AlphaDummy052 h) ∈
      (((synCcompl (Class.cab (nb090AlphaDummy059 h)
              (synWrex (nb090AlphaDummy060 h) (Class.cv (nb090AlphaDummy052 h))
                (Wff.classEq (Class.cv (nb090AlphaDummy059 h))
                  (synCphi (Class.cv (nb090AlphaDummy060 h)))))))).fv ∪ ((synCcompl
            (Class.cab (nb090AlphaDummy059 h)
              (synWrex (nb090AlphaDummy060 h) (Class.cv (nb090AlphaDummy053 h))
                (Wff.classEq (Class.cv (nb090AlphaDummy059 h))
                  (synCun (synCphi (Class.cv (nb090AlphaDummy060 h)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb090AlphaDummy052 h) ≠ (nb090AlphaDummy059 h) from (by
          unfold nb090AlphaDummy059;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0048 h) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb090AlphaDummy052 h) ≠ (nb090AlphaDummy060 h) from (by
            unfold nb090AlphaDummy060;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0048 h) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb090_support_mem_0050 (A : Class) :
    (nb090AlphaDummy049 A) ∈
      (((Class.cab (nb090AlphaDummy057 A)
            (synWrex (nb090AlphaDummy058 A) (Class.cv (nb090AlphaDummy049 A))
              (Wff.classEq (Class.cv (nb090AlphaDummy057 A))
                (synCphi (Class.cv (nb090AlphaDummy058 A))))))).fv ∪
        ((Class.cab (nb090AlphaDummy057 A)
            (synWrex (nb090AlphaDummy058 A) (Class.cv (nb090AlphaDummy049 A))
              (Wff.classEq (Class.cv (nb090AlphaDummy057 A))
                (synCphi (Class.cv (nb090AlphaDummy058 A))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb090AlphaDummy049 A) ≠ (nb090AlphaDummy057 A) from (by
          unfold nb090AlphaDummy057;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0046 A) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb090AlphaDummy049 A) ≠ (nb090AlphaDummy058 A) from (by
            unfold nb090AlphaDummy058;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0046 A) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb090_support_mem_0051 (h : Var) :
    (nb090AlphaDummy052 h) ∈
      (((Class.cab (nb090AlphaDummy059 h)
            (synWrex (nb090AlphaDummy060 h) (Class.cv (nb090AlphaDummy052 h))
              (Wff.classEq (Class.cv (nb090AlphaDummy059 h))
                (synCphi (Class.cv (nb090AlphaDummy060 h))))))).fv ∪
        ((Class.cab (nb090AlphaDummy059 h)
            (synWrex (nb090AlphaDummy060 h) (Class.cv (nb090AlphaDummy052 h))
              (Wff.classEq (Class.cv (nb090AlphaDummy059 h))
                (synCphi (Class.cv (nb090AlphaDummy060 h))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb090AlphaDummy052 h) ≠ (nb090AlphaDummy059 h) from (by
          unfold nb090AlphaDummy059;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0048 h) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb090AlphaDummy052 h) ≠ (nb090AlphaDummy060 h) from (by
            unfold nb090AlphaDummy060;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0048 h) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb090_support_mem_0052 (A : Class) :
    (nb090AlphaDummy058 A) ∈ (((Class.cv (nb090AlphaDummy058 A))).fv) :=
  by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0053 (h : Var) :
    (nb090AlphaDummy060 h) ∈ (((Class.cv (nb090AlphaDummy060 h))).fv) :=
  by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0054 (A : Class) :
    (nb090AlphaDummy065 A) ∈
      (((Wff.classMem (Class.cv (nb090AlphaDummy065 A)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb090AlphaDummy065 A)) (synC1c))).fv ∪
        ((Class.cv (nb090AlphaDummy065 A))).fv) :=
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

theorem nb090_support_mem_0055 (h : Var) :
    (nb090AlphaDummy067 h) ∈
      (((Wff.classMem (Class.cv (nb090AlphaDummy067 h)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb090AlphaDummy067 h)) (synC1c))).fv ∪
        ((Class.cv (nb090AlphaDummy067 h))).fv) :=
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

theorem nb090_support_mem_0056 (A : Class) :
    (nb090AlphaDummy065 A) ∈
      (((Class.cv (nb090AlphaDummy065 A))).fv ∪ ((synC1c)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0057 (h : Var) :
    (nb090AlphaDummy067 h) ∈
      (((Class.cv (nb090AlphaDummy067 h))).fv ∪ ((synC1c)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0058 (A : Class) :
    (nb090AlphaDummy072 A) ∈
      (((synCnin (Class.cv (nb090AlphaDummy072 A))
            (Class.cv (nb090AlphaDummy073 A)))).fv ∪
        ((synCnin (Class.cv (nb090AlphaDummy072 A))
            (Class.cv (nb090AlphaDummy073 A)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0059 (h : Var) :
    (nb090AlphaDummy075 h) ∈
      (((synCnin (Class.cv (nb090AlphaDummy075 h))
            (Class.cv (nb090AlphaDummy076 h)))).fv ∪
        ((synCnin (Class.cv (nb090AlphaDummy075 h))
            (Class.cv (nb090AlphaDummy076 h)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0060 (A : Class) :
    (nb090AlphaDummy072 A) ∈
      (((Class.cv (nb090AlphaDummy072 A))).fv ∪ ((Class.cv (nb090AlphaDummy073 A))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0061 (h : Var) :
    (nb090AlphaDummy075 h) ∈
      (((Class.cv (nb090AlphaDummy075 h))).fv ∪ ((Class.cv (nb090AlphaDummy076 h))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0062 (A : Class) :
    (nb090AlphaDummy073 A) ∈
      (((synCnin (Class.cv (nb090AlphaDummy072 A))
            (Class.cv (nb090AlphaDummy073 A)))).fv ∪
        ((synCnin (Class.cv (nb090AlphaDummy072 A))
            (Class.cv (nb090AlphaDummy073 A)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0063 (h : Var) :
    (nb090AlphaDummy076 h) ∈
      (((synCnin (Class.cv (nb090AlphaDummy075 h))
            (Class.cv (nb090AlphaDummy076 h)))).fv ∪
        ((synCnin (Class.cv (nb090AlphaDummy075 h))
            (Class.cv (nb090AlphaDummy076 h)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0064 (A : Class) :
    (nb090AlphaDummy073 A) ∈
      (((Class.cv (nb090AlphaDummy072 A))).fv ∪ ((Class.cv (nb090AlphaDummy073 A))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0065 (h : Var) :
    (nb090AlphaDummy076 h) ∈
      (((Class.cv (nb090AlphaDummy075 h))).fv ∪ ((Class.cv (nb090AlphaDummy076 h))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0066 (A : Class) :
    (nb090AlphaDummy072 A) ∈
      (((synCcompl (Class.cv (nb090AlphaDummy072 A)))).fv ∪
        ((synCcompl (Class.cv (nb090AlphaDummy073 A)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0067 (h : Var) :
    (nb090AlphaDummy075 h) ∈
      (((synCcompl (Class.cv (nb090AlphaDummy075 h)))).fv ∪
        ((synCcompl (Class.cv (nb090AlphaDummy076 h)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0068 (A : Class) :
    (nb090AlphaDummy072 A) ∈
      (((Class.cv (nb090AlphaDummy072 A))).fv ∪ ((Class.cv (nb090AlphaDummy072 A))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0069 (h : Var) :
    (nb090AlphaDummy075 h) ∈
      (((Class.cv (nb090AlphaDummy075 h))).fv ∪ ((Class.cv (nb090AlphaDummy075 h))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0070 (A : Class) :
    (nb090AlphaDummy073 A) ∈
      (((synCcompl (Class.cv (nb090AlphaDummy072 A)))).fv ∪
        ((synCcompl (Class.cv (nb090AlphaDummy073 A)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0071 (h : Var) :
    (nb090AlphaDummy076 h) ∈
      (((synCcompl (Class.cv (nb090AlphaDummy075 h)))).fv ∪
        ((synCcompl (Class.cv (nb090AlphaDummy076 h)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0072 (A : Class) :
    (nb090AlphaDummy073 A) ∈
      (((Class.cv (nb090AlphaDummy073 A))).fv ∪ ((Class.cv (nb090AlphaDummy073 A))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0073 (h : Var) :
    (nb090AlphaDummy076 h) ∈
      (((Class.cv (nb090AlphaDummy076 h))).fv ∪ ((Class.cv (nb090AlphaDummy076 h))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0074 (A : Class) :
    (nb090AlphaDummy050 A) ∈
      (((Class.cv (nb090AlphaDummy049 A))).fv ∪ ((Class.cv (nb090AlphaDummy050 A))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0075 (A : Class) :
    (nb090AlphaDummy050 A) ∈
      (((synCcompl (Class.cab (nb090AlphaDummy057 A)
              (synWrex (nb090AlphaDummy058 A) (Class.cv (nb090AlphaDummy049 A))
                (Wff.classEq (Class.cv (nb090AlphaDummy057 A))
                  (synCphi (Class.cv (nb090AlphaDummy058 A)))))))).fv ∪ ((synCcompl
            (Class.cab (nb090AlphaDummy057 A)
              (synWrex (nb090AlphaDummy058 A) (Class.cv (nb090AlphaDummy050 A))
                (Wff.classEq (Class.cv (nb090AlphaDummy057 A))
                  (synCun (synCphi (Class.cv (nb090AlphaDummy058 A)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb090AlphaDummy050 A) ≠ (nb090AlphaDummy057 A) from (by
          unfold nb090AlphaDummy057;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0074 A) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb090AlphaDummy050 A) ≠ (nb090AlphaDummy058 A) from (by
            unfold nb090AlphaDummy058;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0074 A) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb090_support_mem_0076 (h : Var) :
    (nb090AlphaDummy053 h) ∈
      (((Class.cv (nb090AlphaDummy052 h))).fv ∪ ((Class.cv (nb090AlphaDummy053 h))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0077 (h : Var) :
    (nb090AlphaDummy053 h) ∈
      (((synCcompl (Class.cab (nb090AlphaDummy059 h)
              (synWrex (nb090AlphaDummy060 h) (Class.cv (nb090AlphaDummy052 h))
                (Wff.classEq (Class.cv (nb090AlphaDummy059 h))
                  (synCphi (Class.cv (nb090AlphaDummy060 h)))))))).fv ∪ ((synCcompl
            (Class.cab (nb090AlphaDummy059 h)
              (synWrex (nb090AlphaDummy060 h) (Class.cv (nb090AlphaDummy053 h))
                (Wff.classEq (Class.cv (nb090AlphaDummy059 h))
                  (synCun (synCphi (Class.cv (nb090AlphaDummy060 h)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb090AlphaDummy053 h) ≠ (nb090AlphaDummy059 h) from (by
          unfold nb090AlphaDummy059;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0076 h) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb090AlphaDummy053 h) ≠ (nb090AlphaDummy060 h) from (by
            unfold nb090AlphaDummy060;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0076 h) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb090_support_mem_0078 (A : Class) :
    (nb090AlphaDummy050 A) ∈
      (((Class.cab (nb090AlphaDummy057 A)
            (synWrex (nb090AlphaDummy058 A) (Class.cv (nb090AlphaDummy050 A))
              (Wff.classEq (Class.cv (nb090AlphaDummy057 A))
                (synCun (synCphi (Class.cv (nb090AlphaDummy058 A)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb090AlphaDummy057 A)
            (synWrex (nb090AlphaDummy058 A) (Class.cv (nb090AlphaDummy050 A))
              (Wff.classEq (Class.cv (nb090AlphaDummy057 A))
                (synCun (synCphi (Class.cv (nb090AlphaDummy058 A)))
                  (synCsn (synC0c))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb090AlphaDummy050 A) ≠ (nb090AlphaDummy057 A) from (by
          unfold nb090AlphaDummy057;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0074 A) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb090AlphaDummy050 A) ≠ (nb090AlphaDummy058 A) from (by
            unfold nb090AlphaDummy058;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0074 A) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired

end

/-! Certificates from `NAR4C090C001Part016`. -/


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

theorem nb090_support_mem_0079 (h : Var) :
    (nb090AlphaDummy053 h) ∈
      (((Class.cab (nb090AlphaDummy059 h)
            (synWrex (nb090AlphaDummy060 h) (Class.cv (nb090AlphaDummy053 h))
              (Wff.classEq (Class.cv (nb090AlphaDummy059 h))
                (synCun (synCphi (Class.cv (nb090AlphaDummy060 h)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb090AlphaDummy059 h)
            (synWrex (nb090AlphaDummy060 h) (Class.cv (nb090AlphaDummy053 h))
              (Wff.classEq (Class.cv (nb090AlphaDummy059 h))
                (synCun (synCphi (Class.cv (nb090AlphaDummy060 h)))
                  (synCsn (synC0c))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb090AlphaDummy053 h) ≠ (nb090AlphaDummy059 h) from (by
          unfold nb090AlphaDummy059;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0076 h) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb090AlphaDummy053 h) ≠ (nb090AlphaDummy060 h) from (by
            unfold nb090AlphaDummy060;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0076 h) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb090_support_mem_0080 (A : Class) :
    (nb090AlphaDummy058 A) ∈
      (((synCcompl (synCphi (Class.cv (nb090AlphaDummy058 A))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0081 (h : Var) :
    (nb090AlphaDummy060 h) ∈
      (((synCcompl (synCphi (Class.cv (nb090AlphaDummy060 h))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0082 (A : Class) :
    (nb090AlphaDummy058 A) ∈
      (((synCphi (Class.cv (nb090AlphaDummy058 A)))).fv ∪
        ((synCphi (Class.cv (nb090AlphaDummy058 A)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0083 (h : Var) :
    (nb090AlphaDummy060 h) ∈
      (((synCphi (Class.cv (nb090AlphaDummy060 h)))).fv ∪
        ((synCphi (Class.cv (nb090AlphaDummy060 h)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0084 (A : Class) :
    (nb090AlphaDummy049 A) ∈
      (((Class.cv (nb090AlphaDummy049 A))).fv ∪ ((Class.cv (nb090AlphaDummy051 A))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0085 (A : Class) :
    (nb090AlphaDummy049 A) ∈
      (((synCcompl (Class.cab (nb090AlphaDummy093 A)
              (synWrex (nb090AlphaDummy094 A) (Class.cv (nb090AlphaDummy049 A))
                (Wff.classEq (Class.cv (nb090AlphaDummy093 A))
                  (synCphi (Class.cv (nb090AlphaDummy094 A)))))))).fv ∪ ((synCcompl
            (Class.cab (nb090AlphaDummy093 A)
              (synWrex (nb090AlphaDummy094 A) (Class.cv (nb090AlphaDummy051 A))
                (Wff.classEq (Class.cv (nb090AlphaDummy093 A))
                  (synCun (synCphi (Class.cv (nb090AlphaDummy094 A)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb090AlphaDummy049 A) ≠ (nb090AlphaDummy093 A) from (by
          unfold nb090AlphaDummy093;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0084 A) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb090AlphaDummy049 A) ≠ (nb090AlphaDummy094 A) from (by
            unfold nb090AlphaDummy094;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0084 A) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb090_support_mem_0086 (h : Var) :
    (nb090AlphaDummy052 h) ∈
      (((Class.cv (nb090AlphaDummy052 h))).fv ∪ ((Class.cv (nb090AlphaDummy054 h))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0087 (h : Var) :
    (nb090AlphaDummy052 h) ∈
      (((synCcompl (Class.cab (nb090AlphaDummy095 h)
              (synWrex (nb090AlphaDummy096 h) (Class.cv (nb090AlphaDummy052 h))
                (Wff.classEq (Class.cv (nb090AlphaDummy095 h))
                  (synCphi (Class.cv (nb090AlphaDummy096 h)))))))).fv ∪ ((synCcompl
            (Class.cab (nb090AlphaDummy095 h)
              (synWrex (nb090AlphaDummy096 h) (Class.cv (nb090AlphaDummy054 h))
                (Wff.classEq (Class.cv (nb090AlphaDummy095 h))
                  (synCun (synCphi (Class.cv (nb090AlphaDummy096 h)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb090AlphaDummy052 h) ≠ (nb090AlphaDummy095 h) from (by
          unfold nb090AlphaDummy095;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0086 h) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb090AlphaDummy052 h) ≠ (nb090AlphaDummy096 h) from (by
            unfold nb090AlphaDummy096;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0086 h) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb090_support_mem_0088 (A : Class) :
    (nb090AlphaDummy049 A) ∈
      (((Class.cab (nb090AlphaDummy093 A)
            (synWrex (nb090AlphaDummy094 A) (Class.cv (nb090AlphaDummy049 A))
              (Wff.classEq (Class.cv (nb090AlphaDummy093 A))
                (synCphi (Class.cv (nb090AlphaDummy094 A))))))).fv ∪
        ((Class.cab (nb090AlphaDummy093 A)
            (synWrex (nb090AlphaDummy094 A) (Class.cv (nb090AlphaDummy049 A))
              (Wff.classEq (Class.cv (nb090AlphaDummy093 A))
                (synCphi (Class.cv (nb090AlphaDummy094 A))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb090AlphaDummy049 A) ≠ (nb090AlphaDummy093 A) from (by
          unfold nb090AlphaDummy093;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0084 A) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb090AlphaDummy049 A) ≠ (nb090AlphaDummy094 A) from (by
            unfold nb090AlphaDummy094;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0084 A) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb090_support_mem_0089 (h : Var) :
    (nb090AlphaDummy052 h) ∈
      (((Class.cab (nb090AlphaDummy095 h)
            (synWrex (nb090AlphaDummy096 h) (Class.cv (nb090AlphaDummy052 h))
              (Wff.classEq (Class.cv (nb090AlphaDummy095 h))
                (synCphi (Class.cv (nb090AlphaDummy096 h))))))).fv ∪
        ((Class.cab (nb090AlphaDummy095 h)
            (synWrex (nb090AlphaDummy096 h) (Class.cv (nb090AlphaDummy052 h))
              (Wff.classEq (Class.cv (nb090AlphaDummy095 h))
                (synCphi (Class.cv (nb090AlphaDummy096 h))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb090AlphaDummy052 h) ≠ (nb090AlphaDummy095 h) from (by
          unfold nb090AlphaDummy095;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0086 h) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb090AlphaDummy052 h) ≠ (nb090AlphaDummy096 h) from (by
            unfold nb090AlphaDummy096;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0086 h) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb090_support_mem_0090 (A : Class) :
    (nb090AlphaDummy094 A) ∈ (((Class.cv (nb090AlphaDummy094 A))).fv) :=
  by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0091 (h : Var) :
    (nb090AlphaDummy096 h) ∈ (((Class.cv (nb090AlphaDummy096 h))).fv) :=
  by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0092 (A : Class) :
    (nb090AlphaDummy101 A) ∈
      (((Wff.classMem (Class.cv (nb090AlphaDummy101 A)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb090AlphaDummy101 A)) (synC1c))).fv ∪
        ((Class.cv (nb090AlphaDummy101 A))).fv) :=
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

theorem nb090_support_mem_0093 (h : Var) :
    (nb090AlphaDummy103 h) ∈
      (((Wff.classMem (Class.cv (nb090AlphaDummy103 h)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb090AlphaDummy103 h)) (synC1c))).fv ∪
        ((Class.cv (nb090AlphaDummy103 h))).fv) :=
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

theorem nb090_support_mem_0094 (A : Class) :
    (nb090AlphaDummy101 A) ∈
      (((Class.cv (nb090AlphaDummy101 A))).fv ∪ ((synC1c)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0095 (h : Var) :
    (nb090AlphaDummy103 h) ∈
      (((Class.cv (nb090AlphaDummy103 h))).fv ∪ ((synC1c)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0096 (A : Class) :
    (nb090AlphaDummy108 A) ∈
      (((synCnin (Class.cv (nb090AlphaDummy108 A))
            (Class.cv (nb090AlphaDummy109 A)))).fv ∪
        ((synCnin (Class.cv (nb090AlphaDummy108 A))
            (Class.cv (nb090AlphaDummy109 A)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0097 (h : Var) :
    (nb090AlphaDummy111 h) ∈
      (((synCnin (Class.cv (nb090AlphaDummy111 h))
            (Class.cv (nb090AlphaDummy112 h)))).fv ∪
        ((synCnin (Class.cv (nb090AlphaDummy111 h))
            (Class.cv (nb090AlphaDummy112 h)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0098 (A : Class) :
    (nb090AlphaDummy108 A) ∈
      (((Class.cv (nb090AlphaDummy108 A))).fv ∪ ((Class.cv (nb090AlphaDummy109 A))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0099 (h : Var) :
    (nb090AlphaDummy111 h) ∈
      (((Class.cv (nb090AlphaDummy111 h))).fv ∪ ((Class.cv (nb090AlphaDummy112 h))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0100 (A : Class) :
    (nb090AlphaDummy109 A) ∈
      (((synCnin (Class.cv (nb090AlphaDummy108 A))
            (Class.cv (nb090AlphaDummy109 A)))).fv ∪
        ((synCnin (Class.cv (nb090AlphaDummy108 A))
            (Class.cv (nb090AlphaDummy109 A)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0101 (h : Var) :
    (nb090AlphaDummy112 h) ∈
      (((synCnin (Class.cv (nb090AlphaDummy111 h))
            (Class.cv (nb090AlphaDummy112 h)))).fv ∪
        ((synCnin (Class.cv (nb090AlphaDummy111 h))
            (Class.cv (nb090AlphaDummy112 h)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0102 (A : Class) :
    (nb090AlphaDummy109 A) ∈
      (((Class.cv (nb090AlphaDummy108 A))).fv ∪ ((Class.cv (nb090AlphaDummy109 A))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0103 (h : Var) :
    (nb090AlphaDummy112 h) ∈
      (((Class.cv (nb090AlphaDummy111 h))).fv ∪ ((Class.cv (nb090AlphaDummy112 h))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0104 (A : Class) :
    (nb090AlphaDummy108 A) ∈
      (((synCcompl (Class.cv (nb090AlphaDummy108 A)))).fv ∪
        ((synCcompl (Class.cv (nb090AlphaDummy109 A)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0105 (h : Var) :
    (nb090AlphaDummy111 h) ∈
      (((synCcompl (Class.cv (nb090AlphaDummy111 h)))).fv ∪
        ((synCcompl (Class.cv (nb090AlphaDummy112 h)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0106 (A : Class) :
    (nb090AlphaDummy108 A) ∈
      (((Class.cv (nb090AlphaDummy108 A))).fv ∪ ((Class.cv (nb090AlphaDummy108 A))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0107 (h : Var) :
    (nb090AlphaDummy111 h) ∈
      (((Class.cv (nb090AlphaDummy111 h))).fv ∪ ((Class.cv (nb090AlphaDummy111 h))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0108 (A : Class) :
    (nb090AlphaDummy109 A) ∈
      (((synCcompl (Class.cv (nb090AlphaDummy108 A)))).fv ∪
        ((synCcompl (Class.cv (nb090AlphaDummy109 A)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0109 (h : Var) :
    (nb090AlphaDummy112 h) ∈
      (((synCcompl (Class.cv (nb090AlphaDummy111 h)))).fv ∪
        ((synCcompl (Class.cv (nb090AlphaDummy112 h)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0110 (A : Class) :
    (nb090AlphaDummy109 A) ∈
      (((Class.cv (nb090AlphaDummy109 A))).fv ∪ ((Class.cv (nb090AlphaDummy109 A))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0111 (h : Var) :
    (nb090AlphaDummy112 h) ∈
      (((Class.cv (nb090AlphaDummy112 h))).fv ∪ ((Class.cv (nb090AlphaDummy112 h))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0112 (A : Class) :
    (nb090AlphaDummy051 A) ∈
      (((Class.cv (nb090AlphaDummy049 A))).fv ∪ ((Class.cv (nb090AlphaDummy051 A))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0113 (A : Class) :
    (nb090AlphaDummy051 A) ∈
      (((synCcompl (Class.cab (nb090AlphaDummy093 A)
              (synWrex (nb090AlphaDummy094 A) (Class.cv (nb090AlphaDummy049 A))
                (Wff.classEq (Class.cv (nb090AlphaDummy093 A))
                  (synCphi (Class.cv (nb090AlphaDummy094 A)))))))).fv ∪ ((synCcompl
            (Class.cab (nb090AlphaDummy093 A)
              (synWrex (nb090AlphaDummy094 A) (Class.cv (nb090AlphaDummy051 A))
                (Wff.classEq (Class.cv (nb090AlphaDummy093 A))
                  (synCun (synCphi (Class.cv (nb090AlphaDummy094 A)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb090AlphaDummy051 A) ≠ (nb090AlphaDummy093 A) from (by
          unfold nb090AlphaDummy093;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0112 A) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb090AlphaDummy051 A) ≠ (nb090AlphaDummy094 A) from (by
            unfold nb090AlphaDummy094;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0112 A) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb090_support_mem_0114 (h : Var) :
    (nb090AlphaDummy054 h) ∈
      (((Class.cv (nb090AlphaDummy052 h))).fv ∪ ((Class.cv (nb090AlphaDummy054 h))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0115 (h : Var) :
    (nb090AlphaDummy054 h) ∈
      (((synCcompl (Class.cab (nb090AlphaDummy095 h)
              (synWrex (nb090AlphaDummy096 h) (Class.cv (nb090AlphaDummy052 h))
                (Wff.classEq (Class.cv (nb090AlphaDummy095 h))
                  (synCphi (Class.cv (nb090AlphaDummy096 h)))))))).fv ∪ ((synCcompl
            (Class.cab (nb090AlphaDummy095 h)
              (synWrex (nb090AlphaDummy096 h) (Class.cv (nb090AlphaDummy054 h))
                (Wff.classEq (Class.cv (nb090AlphaDummy095 h))
                  (synCun (synCphi (Class.cv (nb090AlphaDummy096 h)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb090AlphaDummy054 h) ≠ (nb090AlphaDummy095 h) from (by
          unfold nb090AlphaDummy095;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0114 h) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb090AlphaDummy054 h) ≠ (nb090AlphaDummy096 h) from (by
            unfold nb090AlphaDummy096;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0114 h) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb090_support_mem_0116 (A : Class) :
    (nb090AlphaDummy051 A) ∈
      (((Class.cab (nb090AlphaDummy093 A)
            (synWrex (nb090AlphaDummy094 A) (Class.cv (nb090AlphaDummy051 A))
              (Wff.classEq (Class.cv (nb090AlphaDummy093 A))
                (synCun (synCphi (Class.cv (nb090AlphaDummy094 A)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb090AlphaDummy093 A)
            (synWrex (nb090AlphaDummy094 A) (Class.cv (nb090AlphaDummy051 A))
              (Wff.classEq (Class.cv (nb090AlphaDummy093 A))
                (synCun (synCphi (Class.cv (nb090AlphaDummy094 A)))
                  (synCsn (synC0c))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb090AlphaDummy051 A) ≠ (nb090AlphaDummy093 A) from (by
          unfold nb090AlphaDummy093;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0112 A) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb090AlphaDummy051 A) ≠ (nb090AlphaDummy094 A) from (by
            unfold nb090AlphaDummy094;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0112 A) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb090_support_mem_0117 (h : Var) :
    (nb090AlphaDummy054 h) ∈
      (((Class.cab (nb090AlphaDummy095 h)
            (synWrex (nb090AlphaDummy096 h) (Class.cv (nb090AlphaDummy054 h))
              (Wff.classEq (Class.cv (nb090AlphaDummy095 h))
                (synCun (synCphi (Class.cv (nb090AlphaDummy096 h)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb090AlphaDummy095 h)
            (synWrex (nb090AlphaDummy096 h) (Class.cv (nb090AlphaDummy054 h))
              (Wff.classEq (Class.cv (nb090AlphaDummy095 h))
                (synCun (synCphi (Class.cv (nb090AlphaDummy096 h)))
                  (synCsn (synC0c))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb090AlphaDummy054 h) ≠ (nb090AlphaDummy095 h) from (by
          unfold nb090AlphaDummy095;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0114 h) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb090AlphaDummy054 h) ≠ (nb090AlphaDummy096 h) from (by
            unfold nb090AlphaDummy096;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0114 h) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb090_support_mem_0118 (A : Class) :
    (nb090AlphaDummy094 A) ∈
      (((synCcompl (synCphi (Class.cv (nb090AlphaDummy094 A))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0119 (h : Var) :
    (nb090AlphaDummy096 h) ∈
      (((synCcompl (synCphi (Class.cv (nb090AlphaDummy096 h))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0120 (A : Class) :
    (nb090AlphaDummy094 A) ∈
      (((synCphi (Class.cv (nb090AlphaDummy094 A)))).fv ∪
        ((synCphi (Class.cv (nb090AlphaDummy094 A)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0121 (h : Var) :
    (nb090AlphaDummy096 h) ∈
      (((synCphi (Class.cv (nb090AlphaDummy096 h)))).fv ∪
        ((synCphi (Class.cv (nb090AlphaDummy096 h)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0122 (A : Class) :
    (nb090AlphaDummy129 A) ∈
      (({(nb090AlphaDummy129 A)} : Finset Var) ∪ ({(nb090AlphaDummy130 A)} : Finset Var) ∪
        ((synWbr (Class.cv (nb090AlphaDummy130 A)) (Class.cv (nb090AlphaDummy000 A))
            (Class.cv (nb090AlphaDummy129 A)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  with_reducible rw [Finset.mem_union]
  left
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0123 (h : Var) :
    (nb090AlphaDummy131 h) ∈
      (({(nb090AlphaDummy131 h)} : Finset Var) ∪ ({(nb090AlphaDummy132 h)} : Finset Var) ∪
        ((synWbr (Class.cv (nb090AlphaDummy132 h)) (Class.cv h)
            (Class.cv (nb090AlphaDummy131 h)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  with_reducible rw [Finset.mem_union]
  left
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0124 (A : Class) :
    (nb090AlphaDummy130 A) ∈
      (({(nb090AlphaDummy129 A)} : Finset Var) ∪ ({(nb090AlphaDummy130 A)} : Finset Var) ∪
        ((synWbr (Class.cv (nb090AlphaDummy130 A)) (Class.cv (nb090AlphaDummy000 A))
            (Class.cv (nb090AlphaDummy129 A)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  with_reducible rw [Finset.mem_union]
  right
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0125 (h : Var) :
    (nb090AlphaDummy132 h) ∈
      (({(nb090AlphaDummy131 h)} : Finset Var) ∪ ({(nb090AlphaDummy132 h)} : Finset Var) ∪
        ((synWbr (Class.cv (nb090AlphaDummy132 h)) (Class.cv h)
            (Class.cv (nb090AlphaDummy131 h)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  with_reducible rw [Finset.mem_union]
  right
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0126 (A : Class) :
    (nb090AlphaDummy129 A) ∈
      (((Class.cv (nb090AlphaDummy129 A))).fv ∪ ((Class.cv (nb090AlphaDummy130 A))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0127 (A : Class) :
    (nb090AlphaDummy129 A) ∈
      (((synCcompl (Class.cab (nb090AlphaDummy135 A)
              (synWrex (nb090AlphaDummy136 A) (Class.cv (nb090AlphaDummy129 A))
                (Wff.classEq (Class.cv (nb090AlphaDummy135 A))
                  (synCphi (Class.cv (nb090AlphaDummy136 A)))))))).fv ∪ ((synCcompl
            (Class.cab (nb090AlphaDummy135 A)
              (synWrex (nb090AlphaDummy136 A) (Class.cv (nb090AlphaDummy130 A))
                (Wff.classEq (Class.cv (nb090AlphaDummy135 A))
                  (synCun (synCphi (Class.cv (nb090AlphaDummy136 A)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb090AlphaDummy129 A) ≠ (nb090AlphaDummy135 A) from (by
          unfold nb090AlphaDummy135;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0126 A) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb090AlphaDummy129 A) ≠ (nb090AlphaDummy136 A) from (by
            unfold nb090AlphaDummy136;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0126 A) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb090_support_mem_0128 (h : Var) :
    (nb090AlphaDummy131 h) ∈
      (((Class.cv (nb090AlphaDummy131 h))).fv ∪ ((Class.cv (nb090AlphaDummy132 h))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0129 (h : Var) :
    (nb090AlphaDummy131 h) ∈
      (((synCcompl (Class.cab (nb090AlphaDummy137 h)
              (synWrex (nb090AlphaDummy138 h) (Class.cv (nb090AlphaDummy131 h))
                (Wff.classEq (Class.cv (nb090AlphaDummy137 h))
                  (synCphi (Class.cv (nb090AlphaDummy138 h)))))))).fv ∪ ((synCcompl
            (Class.cab (nb090AlphaDummy137 h)
              (synWrex (nb090AlphaDummy138 h) (Class.cv (nb090AlphaDummy132 h))
                (Wff.classEq (Class.cv (nb090AlphaDummy137 h))
                  (synCun (synCphi (Class.cv (nb090AlphaDummy138 h)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb090AlphaDummy131 h) ≠ (nb090AlphaDummy137 h) from (by
          unfold nb090AlphaDummy137;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0128 h) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb090AlphaDummy131 h) ≠ (nb090AlphaDummy138 h) from (by
            unfold nb090AlphaDummy138;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0128 h) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb090_support_mem_0130 (A : Class) :
    (nb090AlphaDummy129 A) ∈
      (((Class.cab (nb090AlphaDummy135 A)
            (synWrex (nb090AlphaDummy136 A) (Class.cv (nb090AlphaDummy129 A))
              (Wff.classEq (Class.cv (nb090AlphaDummy135 A))
                (synCphi (Class.cv (nb090AlphaDummy136 A))))))).fv ∪
        ((Class.cab (nb090AlphaDummy135 A)
            (synWrex (nb090AlphaDummy136 A) (Class.cv (nb090AlphaDummy129 A))
              (Wff.classEq (Class.cv (nb090AlphaDummy135 A))
                (synCphi (Class.cv (nb090AlphaDummy136 A))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb090AlphaDummy129 A) ≠ (nb090AlphaDummy135 A) from (by
          unfold nb090AlphaDummy135;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0126 A) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb090AlphaDummy129 A) ≠ (nb090AlphaDummy136 A) from (by
            unfold nb090AlphaDummy136;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0126 A) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb090_support_mem_0131 (h : Var) :
    (nb090AlphaDummy131 h) ∈
      (((Class.cab (nb090AlphaDummy137 h)
            (synWrex (nb090AlphaDummy138 h) (Class.cv (nb090AlphaDummy131 h))
              (Wff.classEq (Class.cv (nb090AlphaDummy137 h))
                (synCphi (Class.cv (nb090AlphaDummy138 h))))))).fv ∪
        ((Class.cab (nb090AlphaDummy137 h)
            (synWrex (nb090AlphaDummy138 h) (Class.cv (nb090AlphaDummy131 h))
              (Wff.classEq (Class.cv (nb090AlphaDummy137 h))
                (synCphi (Class.cv (nb090AlphaDummy138 h))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb090AlphaDummy131 h) ≠ (nb090AlphaDummy137 h) from (by
          unfold nb090AlphaDummy137;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0128 h) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb090AlphaDummy131 h) ≠ (nb090AlphaDummy138 h) from (by
            unfold nb090AlphaDummy138;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0128 h) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb090_support_mem_0132 (A : Class) :
    (nb090AlphaDummy136 A) ∈ (((Class.cv (nb090AlphaDummy136 A))).fv) :=
  by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0133 (h : Var) :
    (nb090AlphaDummy138 h) ∈ (((Class.cv (nb090AlphaDummy138 h))).fv) :=
  by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0134 (A : Class) :
    (nb090AlphaDummy143 A) ∈
      (((Wff.classMem (Class.cv (nb090AlphaDummy143 A)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb090AlphaDummy143 A)) (synC1c))).fv ∪
        ((Class.cv (nb090AlphaDummy143 A))).fv) :=
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

theorem nb090_support_mem_0135 (h : Var) :
    (nb090AlphaDummy145 h) ∈
      (((Wff.classMem (Class.cv (nb090AlphaDummy145 h)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb090AlphaDummy145 h)) (synC1c))).fv ∪
        ((Class.cv (nb090AlphaDummy145 h))).fv) :=
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

theorem nb090_support_mem_0136 (A : Class) :
    (nb090AlphaDummy143 A) ∈
      (((Class.cv (nb090AlphaDummy143 A))).fv ∪ ((synC1c)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0137 (h : Var) :
    (nb090AlphaDummy145 h) ∈
      (((Class.cv (nb090AlphaDummy145 h))).fv ∪ ((synC1c)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0138 (A : Class) :
    (nb090AlphaDummy150 A) ∈
      (((synCnin (Class.cv (nb090AlphaDummy150 A))
            (Class.cv (nb090AlphaDummy151 A)))).fv ∪
        ((synCnin (Class.cv (nb090AlphaDummy150 A))
            (Class.cv (nb090AlphaDummy151 A)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0139 (h : Var) :
    (nb090AlphaDummy153 h) ∈
      (((synCnin (Class.cv (nb090AlphaDummy153 h))
            (Class.cv (nb090AlphaDummy154 h)))).fv ∪
        ((synCnin (Class.cv (nb090AlphaDummy153 h))
            (Class.cv (nb090AlphaDummy154 h)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0140 (A : Class) :
    (nb090AlphaDummy150 A) ∈
      (((Class.cv (nb090AlphaDummy150 A))).fv ∪ ((Class.cv (nb090AlphaDummy151 A))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0141 (h : Var) :
    (nb090AlphaDummy153 h) ∈
      (((Class.cv (nb090AlphaDummy153 h))).fv ∪ ((Class.cv (nb090AlphaDummy154 h))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0142 (A : Class) :
    (nb090AlphaDummy151 A) ∈
      (((synCnin (Class.cv (nb090AlphaDummy150 A))
            (Class.cv (nb090AlphaDummy151 A)))).fv ∪
        ((synCnin (Class.cv (nb090AlphaDummy150 A))
            (Class.cv (nb090AlphaDummy151 A)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0143 (h : Var) :
    (nb090AlphaDummy154 h) ∈
      (((synCnin (Class.cv (nb090AlphaDummy153 h))
            (Class.cv (nb090AlphaDummy154 h)))).fv ∪
        ((synCnin (Class.cv (nb090AlphaDummy153 h))
            (Class.cv (nb090AlphaDummy154 h)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0144 (A : Class) :
    (nb090AlphaDummy151 A) ∈
      (((Class.cv (nb090AlphaDummy150 A))).fv ∪ ((Class.cv (nb090AlphaDummy151 A))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0145 (h : Var) :
    (nb090AlphaDummy154 h) ∈
      (((Class.cv (nb090AlphaDummy153 h))).fv ∪ ((Class.cv (nb090AlphaDummy154 h))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0146 (A : Class) :
    (nb090AlphaDummy150 A) ∈
      (((synCcompl (Class.cv (nb090AlphaDummy150 A)))).fv ∪
        ((synCcompl (Class.cv (nb090AlphaDummy151 A)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0147 (h : Var) :
    (nb090AlphaDummy153 h) ∈
      (((synCcompl (Class.cv (nb090AlphaDummy153 h)))).fv ∪
        ((synCcompl (Class.cv (nb090AlphaDummy154 h)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0148 (A : Class) :
    (nb090AlphaDummy150 A) ∈
      (((Class.cv (nb090AlphaDummy150 A))).fv ∪ ((Class.cv (nb090AlphaDummy150 A))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0149 (h : Var) :
    (nb090AlphaDummy153 h) ∈
      (((Class.cv (nb090AlphaDummy153 h))).fv ∪ ((Class.cv (nb090AlphaDummy153 h))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0150 (A : Class) :
    (nb090AlphaDummy151 A) ∈
      (((synCcompl (Class.cv (nb090AlphaDummy150 A)))).fv ∪
        ((synCcompl (Class.cv (nb090AlphaDummy151 A)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0151 (h : Var) :
    (nb090AlphaDummy154 h) ∈
      (((synCcompl (Class.cv (nb090AlphaDummy153 h)))).fv ∪
        ((synCcompl (Class.cv (nb090AlphaDummy154 h)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0152 (A : Class) :
    (nb090AlphaDummy151 A) ∈
      (((Class.cv (nb090AlphaDummy151 A))).fv ∪ ((Class.cv (nb090AlphaDummy151 A))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0153 (h : Var) :
    (nb090AlphaDummy154 h) ∈
      (((Class.cv (nb090AlphaDummy154 h))).fv ∪ ((Class.cv (nb090AlphaDummy154 h))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0154 (A : Class) :
    (nb090AlphaDummy130 A) ∈
      (((Class.cv (nb090AlphaDummy129 A))).fv ∪ ((Class.cv (nb090AlphaDummy130 A))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0155 (A : Class) :
    (nb090AlphaDummy130 A) ∈
      (((synCcompl (Class.cab (nb090AlphaDummy135 A)
              (synWrex (nb090AlphaDummy136 A) (Class.cv (nb090AlphaDummy129 A))
                (Wff.classEq (Class.cv (nb090AlphaDummy135 A))
                  (synCphi (Class.cv (nb090AlphaDummy136 A)))))))).fv ∪ ((synCcompl
            (Class.cab (nb090AlphaDummy135 A)
              (synWrex (nb090AlphaDummy136 A) (Class.cv (nb090AlphaDummy130 A))
                (Wff.classEq (Class.cv (nb090AlphaDummy135 A))
                  (synCun (synCphi (Class.cv (nb090AlphaDummy136 A)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb090AlphaDummy130 A) ≠ (nb090AlphaDummy135 A) from (by
          unfold nb090AlphaDummy135;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0154 A) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb090AlphaDummy130 A) ≠ (nb090AlphaDummy136 A) from (by
            unfold nb090AlphaDummy136;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0154 A) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb090_support_mem_0156 (h : Var) :
    (nb090AlphaDummy132 h) ∈
      (((Class.cv (nb090AlphaDummy131 h))).fv ∪ ((Class.cv (nb090AlphaDummy132 h))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0157 (h : Var) :
    (nb090AlphaDummy132 h) ∈
      (((synCcompl (Class.cab (nb090AlphaDummy137 h)
              (synWrex (nb090AlphaDummy138 h) (Class.cv (nb090AlphaDummy131 h))
                (Wff.classEq (Class.cv (nb090AlphaDummy137 h))
                  (synCphi (Class.cv (nb090AlphaDummy138 h)))))))).fv ∪ ((synCcompl
            (Class.cab (nb090AlphaDummy137 h)
              (synWrex (nb090AlphaDummy138 h) (Class.cv (nb090AlphaDummy132 h))
                (Wff.classEq (Class.cv (nb090AlphaDummy137 h))
                  (synCun (synCphi (Class.cv (nb090AlphaDummy138 h)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb090AlphaDummy132 h) ≠ (nb090AlphaDummy137 h) from (by
          unfold nb090AlphaDummy137;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0156 h) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb090AlphaDummy132 h) ≠ (nb090AlphaDummy138 h) from (by
            unfold nb090AlphaDummy138;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0156 h) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb090_support_mem_0158 (A : Class) :
    (nb090AlphaDummy130 A) ∈
      (((Class.cab (nb090AlphaDummy135 A)
            (synWrex (nb090AlphaDummy136 A) (Class.cv (nb090AlphaDummy130 A))
              (Wff.classEq (Class.cv (nb090AlphaDummy135 A))
                (synCun (synCphi (Class.cv (nb090AlphaDummy136 A)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb090AlphaDummy135 A)
            (synWrex (nb090AlphaDummy136 A) (Class.cv (nb090AlphaDummy130 A))
              (Wff.classEq (Class.cv (nb090AlphaDummy135 A))
                (synCun (synCphi (Class.cv (nb090AlphaDummy136 A)))
                  (synCsn (synC0c))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb090AlphaDummy130 A) ≠ (nb090AlphaDummy135 A) from (by
          unfold nb090AlphaDummy135;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0154 A) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb090AlphaDummy130 A) ≠ (nb090AlphaDummy136 A) from (by
            unfold nb090AlphaDummy136;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0154 A) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb090_support_mem_0159 (h : Var) :
    (nb090AlphaDummy132 h) ∈
      (((Class.cab (nb090AlphaDummy137 h)
            (synWrex (nb090AlphaDummy138 h) (Class.cv (nb090AlphaDummy132 h))
              (Wff.classEq (Class.cv (nb090AlphaDummy137 h))
                (synCun (synCphi (Class.cv (nb090AlphaDummy138 h)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb090AlphaDummy137 h)
            (synWrex (nb090AlphaDummy138 h) (Class.cv (nb090AlphaDummy132 h))
              (Wff.classEq (Class.cv (nb090AlphaDummy137 h))
                (synCun (synCphi (Class.cv (nb090AlphaDummy138 h)))
                  (synCsn (synC0c))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb090AlphaDummy132 h) ≠ (nb090AlphaDummy137 h) from (by
          unfold nb090AlphaDummy137;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0156 h) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb090AlphaDummy132 h) ≠ (nb090AlphaDummy138 h) from (by
            unfold nb090AlphaDummy138;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0156 h) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb090_support_mem_0160 (A : Class) :
    (nb090AlphaDummy136 A) ∈
      (((synCcompl (synCphi (Class.cv (nb090AlphaDummy136 A))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0161 (h : Var) :
    (nb090AlphaDummy138 h) ∈
      (((synCcompl (synCphi (Class.cv (nb090AlphaDummy138 h))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0162 (A : Class) :
    (nb090AlphaDummy136 A) ∈
      (((synCphi (Class.cv (nb090AlphaDummy136 A)))).fv ∪
        ((synCphi (Class.cv (nb090AlphaDummy136 A)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0163 (h : Var) :
    (nb090AlphaDummy138 h) ∈
      (((synCphi (Class.cv (nb090AlphaDummy138 h)))).fv ∪
        ((synCphi (Class.cv (nb090AlphaDummy138 h)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0164 (A : Class) :
    (nb090AlphaDummy130 A) ∈
      (((Class.cv (nb090AlphaDummy130 A))).fv ∪ ((Class.cv (nb090AlphaDummy129 A))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0165 (A : Class) :
    (nb090AlphaDummy130 A) ∈
      (((synCcompl (Class.cab (nb090AlphaDummy171 A)
              (synWrex (nb090AlphaDummy172 A) (Class.cv (nb090AlphaDummy130 A))
                (Wff.classEq (Class.cv (nb090AlphaDummy171 A))
                  (synCphi (Class.cv (nb090AlphaDummy172 A)))))))).fv ∪ ((synCcompl
            (Class.cab (nb090AlphaDummy171 A)
              (synWrex (nb090AlphaDummy172 A) (Class.cv (nb090AlphaDummy129 A))
                (Wff.classEq (Class.cv (nb090AlphaDummy171 A))
                  (synCun (synCphi (Class.cv (nb090AlphaDummy172 A)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb090AlphaDummy130 A) ≠ (nb090AlphaDummy171 A) from (by
          unfold nb090AlphaDummy171;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0164 A) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb090AlphaDummy130 A) ≠ (nb090AlphaDummy172 A) from (by
            unfold nb090AlphaDummy172;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0164 A) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb090_support_mem_0166 (h : Var) :
    (nb090AlphaDummy132 h) ∈
      (((Class.cv (nb090AlphaDummy132 h))).fv ∪ ((Class.cv (nb090AlphaDummy131 h))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0167 (h : Var) :
    (nb090AlphaDummy132 h) ∈
      (((synCcompl (Class.cab (nb090AlphaDummy173 h)
              (synWrex (nb090AlphaDummy174 h) (Class.cv (nb090AlphaDummy132 h))
                (Wff.classEq (Class.cv (nb090AlphaDummy173 h))
                  (synCphi (Class.cv (nb090AlphaDummy174 h)))))))).fv ∪ ((synCcompl
            (Class.cab (nb090AlphaDummy173 h)
              (synWrex (nb090AlphaDummy174 h) (Class.cv (nb090AlphaDummy131 h))
                (Wff.classEq (Class.cv (nb090AlphaDummy173 h))
                  (synCun (synCphi (Class.cv (nb090AlphaDummy174 h)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb090AlphaDummy132 h) ≠ (nb090AlphaDummy173 h) from (by
          unfold nb090AlphaDummy173;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0166 h) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb090AlphaDummy132 h) ≠ (nb090AlphaDummy174 h) from (by
            unfold nb090AlphaDummy174;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0166 h) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb090_support_mem_0168 (A : Class) :
    (nb090AlphaDummy130 A) ∈
      (((Class.cab (nb090AlphaDummy171 A)
            (synWrex (nb090AlphaDummy172 A) (Class.cv (nb090AlphaDummy130 A))
              (Wff.classEq (Class.cv (nb090AlphaDummy171 A))
                (synCphi (Class.cv (nb090AlphaDummy172 A))))))).fv ∪
        ((Class.cab (nb090AlphaDummy171 A)
            (synWrex (nb090AlphaDummy172 A) (Class.cv (nb090AlphaDummy130 A))
              (Wff.classEq (Class.cv (nb090AlphaDummy171 A))
                (synCphi (Class.cv (nb090AlphaDummy172 A))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb090AlphaDummy130 A) ≠ (nb090AlphaDummy171 A) from (by
          unfold nb090AlphaDummy171;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0164 A) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb090AlphaDummy130 A) ≠ (nb090AlphaDummy172 A) from (by
            unfold nb090AlphaDummy172;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0164 A) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb090_support_mem_0169 (h : Var) :
    (nb090AlphaDummy132 h) ∈
      (((Class.cab (nb090AlphaDummy173 h)
            (synWrex (nb090AlphaDummy174 h) (Class.cv (nb090AlphaDummy132 h))
              (Wff.classEq (Class.cv (nb090AlphaDummy173 h))
                (synCphi (Class.cv (nb090AlphaDummy174 h))))))).fv ∪
        ((Class.cab (nb090AlphaDummy173 h)
            (synWrex (nb090AlphaDummy174 h) (Class.cv (nb090AlphaDummy132 h))
              (Wff.classEq (Class.cv (nb090AlphaDummy173 h))
                (synCphi (Class.cv (nb090AlphaDummy174 h))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb090AlphaDummy132 h) ≠ (nb090AlphaDummy173 h) from (by
          unfold nb090AlphaDummy173;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0166 h) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb090AlphaDummy132 h) ≠ (nb090AlphaDummy174 h) from (by
            unfold nb090AlphaDummy174;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0166 h) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb090_support_mem_0170 (A : Class) :
    (nb090AlphaDummy172 A) ∈ (((Class.cv (nb090AlphaDummy172 A))).fv) :=
  by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0171 (h : Var) :
    (nb090AlphaDummy174 h) ∈ (((Class.cv (nb090AlphaDummy174 h))).fv) :=
  by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0172 (A : Class) :
    (nb090AlphaDummy179 A) ∈
      (((Wff.classMem (Class.cv (nb090AlphaDummy179 A)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb090AlphaDummy179 A)) (synC1c))).fv ∪
        ((Class.cv (nb090AlphaDummy179 A))).fv) :=
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

theorem nb090_support_mem_0173 (h : Var) :
    (nb090AlphaDummy181 h) ∈
      (((Wff.classMem (Class.cv (nb090AlphaDummy181 h)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb090AlphaDummy181 h)) (synC1c))).fv ∪
        ((Class.cv (nb090AlphaDummy181 h))).fv) :=
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

theorem nb090_support_mem_0174 (A : Class) :
    (nb090AlphaDummy179 A) ∈
      (((Class.cv (nb090AlphaDummy179 A))).fv ∪ ((synC1c)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0175 (h : Var) :
    (nb090AlphaDummy181 h) ∈
      (((Class.cv (nb090AlphaDummy181 h))).fv ∪ ((synC1c)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0176 (A : Class) :
    (nb090AlphaDummy186 A) ∈
      (((synCnin (Class.cv (nb090AlphaDummy186 A))
            (Class.cv (nb090AlphaDummy187 A)))).fv ∪
        ((synCnin (Class.cv (nb090AlphaDummy186 A))
            (Class.cv (nb090AlphaDummy187 A)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0177 (h : Var) :
    (nb090AlphaDummy189 h) ∈
      (((synCnin (Class.cv (nb090AlphaDummy189 h))
            (Class.cv (nb090AlphaDummy190 h)))).fv ∪
        ((synCnin (Class.cv (nb090AlphaDummy189 h))
            (Class.cv (nb090AlphaDummy190 h)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0178 (A : Class) :
    (nb090AlphaDummy186 A) ∈
      (((Class.cv (nb090AlphaDummy186 A))).fv ∪ ((Class.cv (nb090AlphaDummy187 A))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0179 (h : Var) :
    (nb090AlphaDummy189 h) ∈
      (((Class.cv (nb090AlphaDummy189 h))).fv ∪ ((Class.cv (nb090AlphaDummy190 h))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0180 (A : Class) :
    (nb090AlphaDummy187 A) ∈
      (((synCnin (Class.cv (nb090AlphaDummy186 A))
            (Class.cv (nb090AlphaDummy187 A)))).fv ∪
        ((synCnin (Class.cv (nb090AlphaDummy186 A))
            (Class.cv (nb090AlphaDummy187 A)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0181 (h : Var) :
    (nb090AlphaDummy190 h) ∈
      (((synCnin (Class.cv (nb090AlphaDummy189 h))
            (Class.cv (nb090AlphaDummy190 h)))).fv ∪
        ((synCnin (Class.cv (nb090AlphaDummy189 h))
            (Class.cv (nb090AlphaDummy190 h)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0182 (A : Class) :
    (nb090AlphaDummy187 A) ∈
      (((Class.cv (nb090AlphaDummy186 A))).fv ∪ ((Class.cv (nb090AlphaDummy187 A))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0183 (h : Var) :
    (nb090AlphaDummy190 h) ∈
      (((Class.cv (nb090AlphaDummy189 h))).fv ∪ ((Class.cv (nb090AlphaDummy190 h))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0184 (A : Class) :
    (nb090AlphaDummy186 A) ∈
      (((synCcompl (Class.cv (nb090AlphaDummy186 A)))).fv ∪
        ((synCcompl (Class.cv (nb090AlphaDummy187 A)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0185 (h : Var) :
    (nb090AlphaDummy189 h) ∈
      (((synCcompl (Class.cv (nb090AlphaDummy189 h)))).fv ∪
        ((synCcompl (Class.cv (nb090AlphaDummy190 h)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0186 (A : Class) :
    (nb090AlphaDummy186 A) ∈
      (((Class.cv (nb090AlphaDummy186 A))).fv ∪ ((Class.cv (nb090AlphaDummy186 A))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0187 (h : Var) :
    (nb090AlphaDummy189 h) ∈
      (((Class.cv (nb090AlphaDummy189 h))).fv ∪ ((Class.cv (nb090AlphaDummy189 h))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0188 (A : Class) :
    (nb090AlphaDummy187 A) ∈
      (((synCcompl (Class.cv (nb090AlphaDummy186 A)))).fv ∪
        ((synCcompl (Class.cv (nb090AlphaDummy187 A)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0189 (h : Var) :
    (nb090AlphaDummy190 h) ∈
      (((synCcompl (Class.cv (nb090AlphaDummy189 h)))).fv ∪
        ((synCcompl (Class.cv (nb090AlphaDummy190 h)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0190 (A : Class) :
    (nb090AlphaDummy187 A) ∈
      (((Class.cv (nb090AlphaDummy187 A))).fv ∪ ((Class.cv (nb090AlphaDummy187 A))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0191 (h : Var) :
    (nb090AlphaDummy190 h) ∈
      (((Class.cv (nb090AlphaDummy190 h))).fv ∪ ((Class.cv (nb090AlphaDummy190 h))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0192 (A : Class) :
    (nb090AlphaDummy129 A) ∈
      (((Class.cv (nb090AlphaDummy130 A))).fv ∪ ((Class.cv (nb090AlphaDummy129 A))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0193 (A : Class) :
    (nb090AlphaDummy129 A) ∈
      (((synCcompl (Class.cab (nb090AlphaDummy171 A)
              (synWrex (nb090AlphaDummy172 A) (Class.cv (nb090AlphaDummy130 A))
                (Wff.classEq (Class.cv (nb090AlphaDummy171 A))
                  (synCphi (Class.cv (nb090AlphaDummy172 A)))))))).fv ∪ ((synCcompl
            (Class.cab (nb090AlphaDummy171 A)
              (synWrex (nb090AlphaDummy172 A) (Class.cv (nb090AlphaDummy129 A))
                (Wff.classEq (Class.cv (nb090AlphaDummy171 A))
                  (synCun (synCphi (Class.cv (nb090AlphaDummy172 A)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb090AlphaDummy129 A) ≠ (nb090AlphaDummy171 A) from (by
          unfold nb090AlphaDummy171;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0192 A) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb090AlphaDummy129 A) ≠ (nb090AlphaDummy172 A) from (by
            unfold nb090AlphaDummy172;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0192 A) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb090_support_mem_0194 (h : Var) :
    (nb090AlphaDummy131 h) ∈
      (((Class.cv (nb090AlphaDummy132 h))).fv ∪ ((Class.cv (nb090AlphaDummy131 h))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0195 (h : Var) :
    (nb090AlphaDummy131 h) ∈
      (((synCcompl (Class.cab (nb090AlphaDummy173 h)
              (synWrex (nb090AlphaDummy174 h) (Class.cv (nb090AlphaDummy132 h))
                (Wff.classEq (Class.cv (nb090AlphaDummy173 h))
                  (synCphi (Class.cv (nb090AlphaDummy174 h)))))))).fv ∪ ((synCcompl
            (Class.cab (nb090AlphaDummy173 h)
              (synWrex (nb090AlphaDummy174 h) (Class.cv (nb090AlphaDummy131 h))
                (Wff.classEq (Class.cv (nb090AlphaDummy173 h))
                  (synCun (synCphi (Class.cv (nb090AlphaDummy174 h)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb090AlphaDummy131 h) ≠ (nb090AlphaDummy173 h) from (by
          unfold nb090AlphaDummy173;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0194 h) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb090AlphaDummy131 h) ≠ (nb090AlphaDummy174 h) from (by
            unfold nb090AlphaDummy174;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0194 h) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb090_support_mem_0196 (A : Class) :
    (nb090AlphaDummy129 A) ∈
      (((Class.cab (nb090AlphaDummy171 A)
            (synWrex (nb090AlphaDummy172 A) (Class.cv (nb090AlphaDummy129 A))
              (Wff.classEq (Class.cv (nb090AlphaDummy171 A))
                (synCun (synCphi (Class.cv (nb090AlphaDummy172 A)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb090AlphaDummy171 A)
            (synWrex (nb090AlphaDummy172 A) (Class.cv (nb090AlphaDummy129 A))
              (Wff.classEq (Class.cv (nb090AlphaDummy171 A))
                (synCun (synCphi (Class.cv (nb090AlphaDummy172 A)))
                  (synCsn (synC0c))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb090AlphaDummy129 A) ≠ (nb090AlphaDummy171 A) from (by
          unfold nb090AlphaDummy171;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0192 A) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb090AlphaDummy129 A) ≠ (nb090AlphaDummy172 A) from (by
            unfold nb090AlphaDummy172;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0192 A) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb090_support_mem_0197 (h : Var) :
    (nb090AlphaDummy131 h) ∈
      (((Class.cab (nb090AlphaDummy173 h)
            (synWrex (nb090AlphaDummy174 h) (Class.cv (nb090AlphaDummy131 h))
              (Wff.classEq (Class.cv (nb090AlphaDummy173 h))
                (synCun (synCphi (Class.cv (nb090AlphaDummy174 h)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb090AlphaDummy173 h)
            (synWrex (nb090AlphaDummy174 h) (Class.cv (nb090AlphaDummy131 h))
              (Wff.classEq (Class.cv (nb090AlphaDummy173 h))
                (synCun (synCphi (Class.cv (nb090AlphaDummy174 h)))
                  (synCsn (synC0c))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb090AlphaDummy131 h) ≠ (nb090AlphaDummy173 h) from (by
          unfold nb090AlphaDummy173;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0194 h) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb090AlphaDummy131 h) ≠ (nb090AlphaDummy174 h) from (by
            unfold nb090AlphaDummy174;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0194 h) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb090_support_mem_0198 (A : Class) :
    (nb090AlphaDummy172 A) ∈
      (((synCcompl (synCphi (Class.cv (nb090AlphaDummy172 A))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0199 (h : Var) :
    (nb090AlphaDummy174 h) ∈
      (((synCcompl (synCphi (Class.cv (nb090AlphaDummy174 h))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0200 (A : Class) :
    (nb090AlphaDummy172 A) ∈
      (((synCphi (Class.cv (nb090AlphaDummy172 A)))).fv ∪
        ((synCphi (Class.cv (nb090AlphaDummy172 A)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0201 (h : Var) :
    (nb090AlphaDummy174 h) ∈
      (((synCphi (Class.cv (nb090AlphaDummy174 h)))).fv ∪
        ((synCphi (Class.cv (nb090AlphaDummy174 h)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0202 (A : Class) :
    (nb090AlphaDummy000 A) ∈
      (((synCnin (synCcom (Class.cv (nb090AlphaDummy000 A))
              (synCcnv (Class.cv (nb090AlphaDummy000 A)))) (synCid))).fv ∪ ((synCnin
            (synCcom (Class.cv (nb090AlphaDummy000 A))
              (synCcnv (Class.cv (nb090AlphaDummy000 A)))) (synCid))).fv) :=
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

theorem nb090_support_mem_0203 (h : Var) :
    h ∈
      (((synCnin (synCcom (Class.cv h) (synCcnv (Class.cv h))) (synCid))).fv ∪
        ((synCnin (synCcom (Class.cv h) (synCcnv (Class.cv h))) (synCid))).fv) :=
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

theorem nb090_support_mem_0204 (A : Class) :
    (nb090AlphaDummy000 A) ∈
      (((synCcom (Class.cv (nb090AlphaDummy000 A))
            (synCcnv (Class.cv (nb090AlphaDummy000 A))))).fv ∪ ((synCid)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccom]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0205 (h : Var) :
    h ∈ (((synCcom (Class.cv h) (synCcnv (Class.cv h)))).fv ∪ ((synCid)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccom]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0206 (A : Class) :
    (nb090AlphaDummy000 A) ∈
      (((Class.cv (nb090AlphaDummy000 A))).fv ∪
        ((synCcnv (Class.cv (nb090AlphaDummy000 A)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0207 (A : Class) :
    (nb090AlphaDummy000 A) ∈
      (({(nb090AlphaDummy049 A)} : Finset Var) ∪ ({(nb090AlphaDummy050 A)} : Finset Var) ∪
        ((synWex (nb090AlphaDummy051 A) (synWa
              (synWbr (Class.cv (nb090AlphaDummy049 A))
                (synCcnv (Class.cv (nb090AlphaDummy000 A)))
                (Class.cv (nb090AlphaDummy051 A)))
              (synWbr (Class.cv (nb090AlphaDummy051 A)) (Class.cv (nb090AlphaDummy000 A))
                (Class.cv (nb090AlphaDummy050 A)))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_wex]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb090AlphaDummy000 A) ≠ (nb090AlphaDummy051 A) from (by
          unfold nb090AlphaDummy051;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0206 A) 2))))
  · rw [fv_syn_wa]
    with_reducible rw [Finset.mem_union]
    left
    rw [fv_syn_wbr]
    with_reducible rw [Finset.mem_union]
    right
    rw [fv_syn_ccnv]
    rw [fv_class_cv]
    exact Finset.mem_singleton_self _

theorem nb090_support_mem_0208 (h : Var) :
    h ∈ (((Class.cv h)).fv ∪ ((synCcnv (Class.cv h))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0209 (h : Var) :
    h ∈
      (({(nb090AlphaDummy052 h)} : Finset Var) ∪ ({(nb090AlphaDummy053 h)} : Finset Var) ∪
        ((synWex (nb090AlphaDummy054 h) (synWa
              (synWbr (Class.cv (nb090AlphaDummy052 h)) (synCcnv (Class.cv h))
                (Class.cv (nb090AlphaDummy054 h)))
              (synWbr (Class.cv (nb090AlphaDummy054 h)) (Class.cv h)
                (Class.cv (nb090AlphaDummy053 h)))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_wex]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show h ≠ (nb090AlphaDummy054 h) from (by
          unfold nb090AlphaDummy054;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0208 h) 2))))
  · rw [fv_syn_wa]
    with_reducible rw [Finset.mem_union]
    left
    rw [fv_syn_wbr]
    with_reducible rw [Finset.mem_union]
    right
    rw [fv_syn_ccnv]
    rw [fv_class_cv]
    exact Finset.mem_singleton_self _

theorem nb090_support_mem_0210 (A : Class) :
    (nb090AlphaDummy000 A) ∈
      (({(nb090AlphaDummy129 A)} : Finset Var) ∪ ({(nb090AlphaDummy130 A)} : Finset Var) ∪
        ((synWbr (Class.cv (nb090AlphaDummy130 A)) (Class.cv (nb090AlphaDummy000 A))
            (Class.cv (nb090AlphaDummy129 A)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_wbr]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0211 (h : Var) :
    h ∈
      (({(nb090AlphaDummy131 h)} : Finset Var) ∪ ({(nb090AlphaDummy132 h)} : Finset Var) ∪
        ((synWbr (Class.cv (nb090AlphaDummy132 h)) (Class.cv h)
            (Class.cv (nb090AlphaDummy131 h)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_wbr]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0212 (A : Class) :
    (nb090AlphaDummy000 A) ∈ (((Class.cv (nb090AlphaDummy000 A))).fv) :=
  by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0213 (h : Var) : h ∈ (((Class.cv h)).fv) :=
  by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0214 (A : Class) :
    (nb090AlphaDummy051 A) ∈
      (((Class.cv (nb090AlphaDummy051 A))).fv ∪ ((Class.cv (nb090AlphaDummy050 A))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0215 (A : Class) :
    (nb090AlphaDummy051 A) ∈
      (((synCcompl (Class.cab (nb090AlphaDummy207 A)
              (synWrex (nb090AlphaDummy208 A) (Class.cv (nb090AlphaDummy051 A))
                (Wff.classEq (Class.cv (nb090AlphaDummy207 A))
                  (synCphi (Class.cv (nb090AlphaDummy208 A)))))))).fv ∪ ((synCcompl
            (Class.cab (nb090AlphaDummy207 A)
              (synWrex (nb090AlphaDummy208 A) (Class.cv (nb090AlphaDummy050 A))
                (Wff.classEq (Class.cv (nb090AlphaDummy207 A))
                  (synCun (synCphi (Class.cv (nb090AlphaDummy208 A)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb090AlphaDummy051 A) ≠ (nb090AlphaDummy207 A) from (by
          unfold nb090AlphaDummy207;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0214 A) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb090AlphaDummy051 A) ≠ (nb090AlphaDummy208 A) from (by
            unfold nb090AlphaDummy208;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0214 A) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb090_support_mem_0216 (h : Var) :
    (nb090AlphaDummy054 h) ∈
      (((Class.cv (nb090AlphaDummy054 h))).fv ∪ ((Class.cv (nb090AlphaDummy053 h))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired

end
