/-
Copyright (c) 2026 Elliot Glazer and NFNotWPP contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elliot Glazer and NFNotWPP contributors
-/

module

public import LeanPool.NFWeakPartition.NominalWPPReplayChunk015Compact001Part010

/-! Nominal proof certificates grouped in dependency order. -/


public section

/-! Certificates from `NominalWPPReplayChunk015Compact001Part011`. -/


section

namespace NFChoice.DirectNominalPrf.WPPReplay

open scoped Fol
open NFChoice.Foundation
open NFChoice.SemanticCore
open NFChoice.ReplaySupport
open NFChoice.Compiler.CompactSourceSyntax

@[expose]
noncomputable def g_lnqordor (C : Class) (R : Class) (dv_C_R : Disjoint C.fv R.fv) :
    Nominal.NPrf
      (.imp (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa
            (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
              (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))
        (syn_wbr (syn_clnqord R C) (syn_cstrict) (syn_clnquo R C))) :=
  by
  have dv_cache_0001 : Disjoint (C).fv (R).fv := by
    exact
      (show Disjoint (C).fv (R).fv from (show Disjoint (C).fv (R).fv from (by exact dv_C_R)))
  have p0000 := @g_lnqordref C R dv_cache_0001
  have p0001 := @g_lnqordtrans C R dv_cache_0001
  have p0002 := @g_lnqordantisym C R dv_cache_0001
  have p0003 :=
    @g_n_3jca
      (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa
          (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
            (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))
      (syn_wbr (syn_clnqord R C) (syn_cref) (syn_clnquo R C))
      (syn_wbr (syn_clnqord R C) (syn_ctrans) (syn_clnquo R C))
      (syn_wbr (syn_clnqord R C) (syn_cantisym) (syn_clnquo R C)) p0000 p0001 p0002
  have p0004 := @g_porta (syn_clnquo R C) (syn_clnqord R C)
  have p0005 :=
    @g_a1i
      (syn_wb (syn_wbr (syn_clnqord R C) (syn_cpartial) (syn_clnquo R C))
        (syn_w3a (syn_wbr (syn_clnqord R C) (syn_cref) (syn_clnquo R C))
          (syn_wbr (syn_clnqord R C) (syn_ctrans) (syn_clnquo R C))
          (syn_wbr (syn_clnqord R C) (syn_cantisym) (syn_clnquo R C))))
      (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa
          (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
            (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))
      p0004
  have p0006 :=
    @g_mpbird
      (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa
          (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
            (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))
      (syn_wbr (syn_clnqord R C) (syn_cpartial) (syn_clnquo R C))
      (syn_w3a (syn_wbr (syn_clnqord R C) (syn_cref) (syn_clnquo R C))
        (syn_wbr (syn_clnqord R C) (syn_ctrans) (syn_clnquo R C))
        (syn_wbr (syn_clnqord R C) (syn_cantisym) (syn_clnquo R C)))
      p0003 p0005
  have p0007 := @g_lnqordconnex C R dv_cache_0001
  have p0008 :=
    @g_jca
      (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa
          (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
            (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))
      (syn_wbr (syn_clnqord R C) (syn_cpartial) (syn_clnquo R C))
      (syn_wbr (syn_clnqord R C) (syn_cconnex) (syn_clnquo R C)) p0006 p0007
  have p0009 := @g_sopc (syn_clnquo R C) (syn_clnqord R C)
  have p0010 :=
    @g_a1i
      (syn_wb (syn_wbr (syn_clnqord R C) (syn_cstrict) (syn_clnquo R C))
        (syn_wa (syn_wbr (syn_clnqord R C) (syn_cpartial) (syn_clnquo R C))
          (syn_wbr (syn_clnqord R C) (syn_cconnex) (syn_clnquo R C))))
      (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa
          (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
            (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))
      p0009
  have p0011 :=
    @g_mpbird
      (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa
          (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
            (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))
      (syn_wbr (syn_clnqord R C) (syn_cstrict) (syn_clnquo R C))
      (syn_wa (syn_wbr (syn_clnqord R C) (syn_cpartial) (syn_clnquo R C))
        (syn_wbr (syn_clnqord R C) (syn_cconnex) (syn_clnquo R C)))
      p0008 p0010
  exact p0011

@[expose]
noncomputable def g_lnkereceqb (C : Class) (R : Class) (X : Class) (Y : Class)
    (dv_C_R : Disjoint C.fv R.fv) :
    Nominal.NPrf
      (.imp (syn_wa (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa
              (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
                (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))
          (syn_wa (.classMem X C) (.classMem Y C)))
        (syn_wb (.classEq (syn_cec X (syn_clnker R)) (syn_cec Y (syn_clnker R)))
          (syn_wa (syn_wbr X R Y) (syn_wbr Y R X)))) :=
  by
  have dv_cache_0001 : Disjoint (C).fv (R).fv := by
    exact
      (show Disjoint (C).fv (R).fv from (show Disjoint (C).fv (R).fv from (by exact dv_C_R)))
  have p0000 :=
    @g_simpl
      (syn_wa (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa
            (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
              (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))
        (syn_wa (.classMem X C) (.classMem Y C)))
      (.classEq (syn_cec X (syn_clnker R)) (syn_cec Y (syn_clnker R)))
  have p0001 :=
    @g_simpl
      (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa
          (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
            (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))
      (syn_wa (.classMem X C) (.classMem Y C))
  have p0002 :=
    @g_simpr (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv)))
      (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
          (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C)))
  have p0003 :=
    @g_simpl
      (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
        (syn_wbr R (syn_cconnex) C))
      (syn_wss R (syn_cxp C C))
  have p0004 :=
    @g_syl
      (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa
          (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
            (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))
      (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
          (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C)))
      (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
        (syn_wbr R (syn_cconnex) C))
      p0002 p0003
  have p0005 :=
    @g_syl
      (syn_wa (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa
            (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
              (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))
        (syn_wa (.classMem X C) (.classMem Y C)))
      (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa
          (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
            (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))
      (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
        (syn_wbr R (syn_cconnex) C))
      p0001 p0004
  have p0006 :=
    @g_simpl (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
      (syn_wbr R (syn_cconnex) C)
  have p0007 :=
    @g_syl
      (syn_wa (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa
            (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
              (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))
        (syn_wa (.classMem X C) (.classMem Y C)))
      (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
        (syn_wbr R (syn_cconnex) C))
      (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) p0005 p0006
  have p0008 := @g_simpl (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)
  have p0009 :=
    @g_syl
      (syn_wa (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa
            (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
              (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))
        (syn_wa (.classMem X C) (.classMem Y C)))
      (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
      (syn_wbr R (syn_cref) C) p0007 p0008
  have p0010 :=
    @g_syl
      (syn_wa (syn_wa (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa
              (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
                (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))
          (syn_wa (.classMem X C) (.classMem Y C)))
        (.classEq (syn_cec X (syn_clnker R)) (syn_cec Y (syn_clnker R))))
      (syn_wa (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa
            (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
              (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))
        (syn_wa (.classMem X C) (.classMem Y C)))
      (syn_wbr R (syn_cref) C) p0000 p0009
  have p0012 :=
    @g_simpr
      (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa
          (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
            (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))
      (syn_wa (.classMem X C) (.classMem Y C))
  have p0013 := @g_simpr (.classMem X C) (.classMem Y C)
  have p0014 :=
    @g_syl
      (syn_wa (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa
            (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
              (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))
        (syn_wa (.classMem X C) (.classMem Y C)))
      (syn_wa (.classMem X C) (.classMem Y C)) (.classMem Y C) p0012 p0013
  have p0015 :=
    @g_syl
      (syn_wa (syn_wa (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa
              (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
                (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))
          (syn_wa (.classMem X C) (.classMem Y C)))
        (.classEq (syn_cec X (syn_clnker R)) (syn_cec Y (syn_clnker R))))
      (syn_wa (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa
            (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
              (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))
        (syn_wa (.classMem X C) (.classMem Y C)))
      (.classMem Y C) p0000 p0014
  have p0016 :=
    @g_refd
      (syn_wa (syn_wa (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa
              (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
                (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))
          (syn_wa (.classMem X C) (.classMem Y C)))
        (.classEq (syn_cec X (syn_clnker R)) (syn_cec Y (syn_clnker R))))
      C R Y p0010 p0015
  have p0034 :=
    @g_jca
      (syn_wa (syn_wa (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa
              (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
                (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))
          (syn_wa (.classMem X C) (.classMem Y C)))
        (.classEq (syn_cec X (syn_clnker R)) (syn_cec Y (syn_clnker R))))
      (syn_wbr Y R Y) (syn_wbr Y R Y) p0016 p0016
  have p0035 := @g_ellnkerecg Y Y R
  have p0036 :=
    @g_a1i
      (syn_wb (.classMem Y (syn_cec Y (syn_clnker R))) (syn_wa (syn_wbr Y R Y) (syn_wbr Y R Y)))
      (syn_wa (syn_wa (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa
              (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
                (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))
          (syn_wa (.classMem X C) (.classMem Y C)))
        (.classEq (syn_cec X (syn_clnker R)) (syn_cec Y (syn_clnker R))))
      p0035
  have p0037 :=
    @g_mpbird
      (syn_wa (syn_wa (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa
              (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
                (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))
          (syn_wa (.classMem X C) (.classMem Y C)))
        (.classEq (syn_cec X (syn_clnker R)) (syn_cec Y (syn_clnker R))))
      (.classMem Y (syn_cec Y (syn_clnker R))) (syn_wa (syn_wbr Y R Y) (syn_wbr Y R Y))
      p0034 p0036
  have p0038 :=
    @g_simpr
      (syn_wa (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa
            (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
              (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))
        (syn_wa (.classMem X C) (.classMem Y C)))
      (.classEq (syn_cec X (syn_clnker R)) (syn_cec Y (syn_clnker R)))
  have p0039 :=
    @g_eleq2d
      (syn_wa (syn_wa (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa
              (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
                (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))
          (syn_wa (.classMem X C) (.classMem Y C)))
        (.classEq (syn_cec X (syn_clnker R)) (syn_cec Y (syn_clnker R))))
      (syn_cec X (syn_clnker R)) (syn_cec Y (syn_clnker R)) Y p0038
  have p0040 :=
    @g_mpbird
      (syn_wa (syn_wa (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa
              (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
                (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))
          (syn_wa (.classMem X C) (.classMem Y C)))
        (.classEq (syn_cec X (syn_clnker R)) (syn_cec Y (syn_clnker R))))
      (.classMem Y (syn_cec X (syn_clnker R))) (.classMem Y (syn_cec Y (syn_clnker R)))
      p0037 p0039
  have p0041 := @g_ellnkerecg Y X R
  have p0042 :=
    @g_a1i
      (syn_wb (.classMem Y (syn_cec X (syn_clnker R))) (syn_wa (syn_wbr X R Y) (syn_wbr Y R X)))
      (syn_wa (syn_wa (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa
              (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
                (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))
          (syn_wa (.classMem X C) (.classMem Y C)))
        (.classEq (syn_cec X (syn_clnker R)) (syn_cec Y (syn_clnker R))))
      p0041
  have p0043 :=
    @g_mpbid
      (syn_wa (syn_wa (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa
              (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
                (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))
          (syn_wa (.classMem X C) (.classMem Y C)))
        (.classEq (syn_cec X (syn_clnker R)) (syn_cec Y (syn_clnker R))))
      (.classMem Y (syn_cec X (syn_clnker R))) (syn_wa (syn_wbr X R Y) (syn_wbr Y R X))
      p0040 p0042
  have p0044 :=
    @g_ex
      (syn_wa (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa
            (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
              (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))
        (syn_wa (.classMem X C) (.classMem Y C)))
      (.classEq (syn_cec X (syn_clnker R)) (syn_cec Y (syn_clnker R)))
      (syn_wa (syn_wbr X R Y) (syn_wbr Y R X)) p0043
  have p0045 :=
    @g_simpl
      (syn_wa (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa
            (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
              (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))
        (syn_wa (.classMem X C) (.classMem Y C)))
      (syn_wa (syn_wbr X R Y) (syn_wbr Y R X))
  have p0047 :=
    @g_syl
      (syn_wa (syn_wa (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa
              (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
                (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))
          (syn_wa (.classMem X C) (.classMem Y C))) (syn_wa (syn_wbr X R Y) (syn_wbr Y R X)))
      (syn_wa (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa
            (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
              (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))
        (syn_wa (.classMem X C) (.classMem Y C)))
      (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa
          (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
            (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))
      p0045 p0001
  have p0048 := @g_lnqordantisym C R dv_cache_0001
  have p0049 :=
    @g_syl
      (syn_wa (syn_wa (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa
              (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
                (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))
          (syn_wa (.classMem X C) (.classMem Y C))) (syn_wa (syn_wbr X R Y) (syn_wbr Y R X)))
      (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa
          (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
            (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))
      (syn_wbr (syn_clnqord R C) (syn_cantisym) (syn_clnquo R C)) p0047 p0048
  have p0052 :=
    @g_simpl (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv)))
      (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
          (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C)))
  have p0053 :=
    @g_syl
      (syn_wa (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa
            (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
              (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))
        (syn_wa (.classMem X C) (.classMem Y C)))
      (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa
          (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
            (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))
      (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) p0001 p0052
  have p0054 := @g_simpl (.classMem R (syn_cvv)) (.classMem C (syn_cvv))
  have p0055 :=
    @g_syl
      (syn_wa (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa
            (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
              (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))
        (syn_wa (.classMem X C) (.classMem Y C)))
      (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (.classMem R (syn_cvv))
      p0053 p0054
  have p0056 := @g_lnkerexg R
  have p0057 :=
    @g_syl
      (syn_wa (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa
            (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
              (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))
        (syn_wa (.classMem X C) (.classMem Y C)))
      (.classMem R (syn_cvv)) (.classMem (syn_clnker R) (syn_cvv)) p0055 p0056
  have p0059 := @g_simpl (.classMem X C) (.classMem Y C)
  have p0060 :=
    @g_syl
      (syn_wa (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa
            (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
              (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))
        (syn_wa (.classMem X C) (.classMem Y C)))
      (syn_wa (.classMem X C) (.classMem Y C)) (.classMem X C) p0012 p0059
  have p0061 :=
    @g_jca
      (syn_wa (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa
            (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
              (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))
        (syn_wa (.classMem X C) (.classMem Y C)))
      (.classMem (syn_clnker R) (syn_cvv)) (.classMem X C) p0057 p0060
  have p0062 := @g_ecelqsg C X (syn_clnker R) (syn_cvv)
  have p0063 :=
    @g_syl
      (syn_wa (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa
            (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
              (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))
        (syn_wa (.classMem X C) (.classMem Y C)))
      (syn_wa (.classMem (syn_clnker R) (syn_cvv)) (.classMem X C))
      (.classMem (syn_cec X (syn_clnker R)) (syn_cqs C (syn_clnker R))) p0061 p0062
  have p0064 := (Nominal.classEqRefl (syn_clnquo R C))
  have p0065 :=
    @g_syl6eleqr
      (syn_wa (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa
            (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
              (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))
        (syn_wa (.classMem X C) (.classMem Y C)))
      (syn_cec X (syn_clnker R)) (syn_cqs C (syn_clnker R)) (syn_clnquo R C) p0063 p0064
  have p0066 :=
    @g_syl
      (syn_wa (syn_wa (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa
              (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
                (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))
          (syn_wa (.classMem X C) (.classMem Y C))) (syn_wa (syn_wbr X R Y) (syn_wbr Y R X)))
      (syn_wa (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa
            (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
              (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))
        (syn_wa (.classMem X C) (.classMem Y C)))
      (.classMem (syn_cec X (syn_clnker R)) (syn_clnquo R C)) p0045 p0065
  have p0078 :=
    @g_jca
      (syn_wa (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa
            (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
              (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))
        (syn_wa (.classMem X C) (.classMem Y C)))
      (.classMem (syn_clnker R) (syn_cvv)) (.classMem Y C) p0057 p0014
  have p0079 := @g_ecelqsg C Y (syn_clnker R) (syn_cvv)
  have p0080 :=
    @g_syl
      (syn_wa (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa
            (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
              (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))
        (syn_wa (.classMem X C) (.classMem Y C)))
      (syn_wa (.classMem (syn_clnker R) (syn_cvv)) (.classMem Y C))
      (.classMem (syn_cec Y (syn_clnker R)) (syn_cqs C (syn_clnker R))) p0078 p0079
  have p0082 :=
    @g_syl6eleqr
      (syn_wa (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa
            (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
              (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))
        (syn_wa (.classMem X C) (.classMem Y C)))
      (syn_cec Y (syn_clnker R)) (syn_cqs C (syn_clnker R)) (syn_clnquo R C) p0080 p0064
  have p0083 :=
    @g_syl
      (syn_wa (syn_wa (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa
              (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
                (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))
          (syn_wa (.classMem X C) (.classMem Y C))) (syn_wa (syn_wbr X R Y) (syn_wbr Y R X)))
      (syn_wa (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa
            (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
              (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))
        (syn_wa (.classMem X C) (.classMem Y C)))
      (.classMem (syn_cec Y (syn_clnker R)) (syn_clnquo R C)) p0045 p0082
  have p0084 :=
    @g_simpr
      (syn_wa (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa
            (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
              (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))
        (syn_wa (.classMem X C) (.classMem Y C)))
      (syn_wa (syn_wbr X R Y) (syn_wbr Y R X))
  have p0085 := @g_simpl (syn_wbr X R Y) (syn_wbr Y R X)
  have p0086 :=
    @g_syl
      (syn_wa (syn_wa (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa
              (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
                (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))
          (syn_wa (.classMem X C) (.classMem Y C))) (syn_wa (syn_wbr X R Y) (syn_wbr Y R X)))
      (syn_wa (syn_wbr X R Y) (syn_wbr Y R X)) (syn_wbr X R Y) p0084 p0085
  have p0102 :=
    @g_simpr
      (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
        (syn_wbr R (syn_cconnex) C))
      (syn_wss R (syn_cxp C C))
  have p0103 :=
    @g_syl
      (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa
          (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
            (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))
      (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
          (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C)))
      (syn_wss R (syn_cxp C C)) p0002 p0102
  have p0104 :=
    @g_syl
      (syn_wa (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa
            (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
              (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))
        (syn_wa (.classMem X C) (.classMem Y C)))
      (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa
          (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
            (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))
      (syn_wss R (syn_cxp C C)) p0001 p0103
  have p0105 :=
    @g_jca
      (syn_wa (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa
            (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
              (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))
        (syn_wa (.classMem X C) (.classMem Y C)))
      (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
      (syn_wss R (syn_cxp C C)) p0007 p0104
  have p0107 :=
    @g_jca
      (syn_wa (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa
            (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
              (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))
        (syn_wa (.classMem X C) (.classMem Y C)))
      (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
        (syn_wss R (syn_cxp C C)))
      (syn_wa (.classMem X C) (.classMem Y C)) p0105 p0012
  have p0108 :=
    @g_jca
      (syn_wa (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa
            (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
              (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))
        (syn_wa (.classMem X C) (.classMem Y C)))
      (.classMem R (syn_cvv))
      (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
          (syn_wss R (syn_cxp C C))) (syn_wa (.classMem X C) (.classMem Y C)))
      p0055 p0107
  have p0109 := @g_brlnqordkern C R X Y dv_cache_0001
  have p0110 :=
    @g_syl
      (syn_wa (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa
            (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
              (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))
        (syn_wa (.classMem X C) (.classMem Y C)))
      (syn_wa (.classMem R (syn_cvv)) (syn_wa
          (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
            (syn_wss R (syn_cxp C C))) (syn_wa (.classMem X C) (.classMem Y C))))
      (syn_wb (syn_wbr (syn_cec X (syn_clnker R)) (syn_clnqord R C) (syn_cec Y (syn_clnker R)))
        (syn_wbr X R Y))
      p0108 p0109
  have p0111 :=
    @g_syl
      (syn_wa (syn_wa (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa
              (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
                (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))
          (syn_wa (.classMem X C) (.classMem Y C))) (syn_wa (syn_wbr X R Y) (syn_wbr Y R X)))
      (syn_wa (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa
            (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
              (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))
        (syn_wa (.classMem X C) (.classMem Y C)))
      (syn_wb (syn_wbr (syn_cec X (syn_clnker R)) (syn_clnqord R C) (syn_cec Y (syn_clnker R)))
        (syn_wbr X R Y))
      p0045 p0110
  have p0112 :=
    @g_mpbird
      (syn_wa (syn_wa (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa
              (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
                (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))
          (syn_wa (.classMem X C) (.classMem Y C))) (syn_wa (syn_wbr X R Y) (syn_wbr Y R X)))
      (syn_wbr (syn_cec X (syn_clnker R)) (syn_clnqord R C) (syn_cec Y (syn_clnker R)))
      (syn_wbr X R Y) p0086 p0111
  have p0114 := @g_simpr (syn_wbr X R Y) (syn_wbr Y R X)
  have p0115 :=
    @g_syl
      (syn_wa (syn_wa (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa
              (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
                (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))
          (syn_wa (.classMem X C) (.classMem Y C))) (syn_wa (syn_wbr X R Y) (syn_wbr Y R X)))
      (syn_wa (syn_wbr X R Y) (syn_wbr Y R X)) (syn_wbr Y R X) p0084 p0114
  have p0141 :=
    @g_jca
      (syn_wa (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa
            (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
              (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))
        (syn_wa (.classMem X C) (.classMem Y C)))
      (.classMem Y C) (.classMem X C) p0014 p0060
  have p0142 :=
    @g_jca
      (syn_wa (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa
            (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
              (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))
        (syn_wa (.classMem X C) (.classMem Y C)))
      (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
        (syn_wss R (syn_cxp C C)))
      (syn_wa (.classMem Y C) (.classMem X C)) p0105 p0141
  have p0143 :=
    @g_jca
      (syn_wa (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa
            (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
              (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))
        (syn_wa (.classMem X C) (.classMem Y C)))
      (.classMem R (syn_cvv))
      (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
          (syn_wss R (syn_cxp C C))) (syn_wa (.classMem Y C) (.classMem X C)))
      p0055 p0142
  have p0144 := @g_brlnqordkern C R Y X dv_cache_0001
  have p0145 :=
    @g_syl
      (syn_wa (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa
            (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
              (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))
        (syn_wa (.classMem X C) (.classMem Y C)))
      (syn_wa (.classMem R (syn_cvv)) (syn_wa
          (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
            (syn_wss R (syn_cxp C C))) (syn_wa (.classMem Y C) (.classMem X C))))
      (syn_wb (syn_wbr (syn_cec Y (syn_clnker R)) (syn_clnqord R C) (syn_cec X (syn_clnker R)))
        (syn_wbr Y R X))
      p0143 p0144
  have p0146 :=
    @g_syl
      (syn_wa (syn_wa (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa
              (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
                (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))
          (syn_wa (.classMem X C) (.classMem Y C))) (syn_wa (syn_wbr X R Y) (syn_wbr Y R X)))
      (syn_wa (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa
            (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
              (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))
        (syn_wa (.classMem X C) (.classMem Y C)))
      (syn_wb (syn_wbr (syn_cec Y (syn_clnker R)) (syn_clnqord R C) (syn_cec X (syn_clnker R)))
        (syn_wbr Y R X))
      p0045 p0145
  have p0147 :=
    @g_mpbird
      (syn_wa (syn_wa (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa
              (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
                (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))
          (syn_wa (.classMem X C) (.classMem Y C))) (syn_wa (syn_wbr X R Y) (syn_wbr Y R X)))
      (syn_wbr (syn_cec Y (syn_clnker R)) (syn_clnqord R C) (syn_cec X (syn_clnker R)))
      (syn_wbr Y R X) p0115 p0146
  have p0148 :=
    @g_antid
      (syn_wa (syn_wa (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa
              (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
                (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))
          (syn_wa (.classMem X C) (.classMem Y C))) (syn_wa (syn_wbr X R Y) (syn_wbr Y R X)))
      (syn_clnquo R C) (syn_clnqord R C) (syn_cec X (syn_clnker R))
      (syn_cec Y (syn_clnker R)) p0049 p0066 p0083 p0112 p0147
  have p0149 :=
    @g_ex
      (syn_wa (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa
            (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
              (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))
        (syn_wa (.classMem X C) (.classMem Y C)))
      (syn_wa (syn_wbr X R Y) (syn_wbr Y R X))
      (.classEq (syn_cec X (syn_clnker R)) (syn_cec Y (syn_clnker R))) p0148
  have p0150 :=
    @g_impbid
      (syn_wa (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa
            (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
              (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))
        (syn_wa (.classMem X C) (.classMem Y C)))
      (.classEq (syn_cec X (syn_clnker R)) (syn_cec Y (syn_clnker R)))
      (syn_wa (syn_wbr X R Y) (syn_wbr Y R X)) p0044 p0149
  exact p0150


end NFChoice.DirectNominalPrf.WPPReplay

end

/-! Certificates from `NominalWPPReplayChunk015Compact001Part012`. -/


section

namespace NFChoice.DirectNominalPrf.WPPReplay

open scoped Fol
open NFChoice.Foundation
open NFChoice.SemanticCore
open NFChoice.ReplaySupport
open NFChoice.Compiler.CompactSourceSyntax

@[expose]
noncomputable def g_brlnqordstrict (C : Class) (R : Class) (X : Class) (Y : Class)
    (dv_C_R : Disjoint C.fv R.fv) :
    Nominal.NPrf
      (.imp (syn_wa (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa
              (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
                (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))
          (syn_wa (.classMem X C) (.classMem Y C))) (syn_wb
          (syn_wbr (syn_cec X (syn_clnker R)) (syn_cdif (syn_clnqord R C) (syn_cid))
            (syn_cec Y (syn_clnker R))) (syn_wbr X (syn_cdif R (syn_ccnv R)) Y))) :=
  by
  have dv_cache_0001 : Disjoint (C).fv (R).fv := by
    exact
      (show Disjoint (C).fv (R).fv from (show Disjoint (C).fv (R).fv from (by exact dv_C_R)))
  have p0000 :=
    @g_brdif (syn_cec X (syn_clnker R)) (syn_cec Y (syn_clnker R)) (syn_clnqord R C)
      (syn_cid)
  have p0001 :=
    @g_a1i
      (syn_wb (syn_wbr (syn_cec X (syn_clnker R)) (syn_cdif (syn_clnqord R C) (syn_cid))
          (syn_cec Y (syn_clnker R))) (syn_wa
          (syn_wbr (syn_cec X (syn_clnker R)) (syn_clnqord R C) (syn_cec Y (syn_clnker R)))
          (.neg (syn_wbr (syn_cec X (syn_clnker R)) (syn_cid) (syn_cec Y (syn_clnker R))))))
      (syn_wa (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa
            (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
              (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))
        (syn_wa (.classMem X C) (.classMem Y C)))
      p0000
  have p0002 :=
    @g_simpl
      (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa
          (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
            (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))
      (syn_wa (.classMem X C) (.classMem Y C))
  have p0003 :=
    @g_simpl (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv)))
      (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
          (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C)))
  have p0004 :=
    @g_syl
      (syn_wa (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa
            (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
              (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))
        (syn_wa (.classMem X C) (.classMem Y C)))
      (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa
          (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
            (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))
      (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) p0002 p0003
  have p0005 := @g_simpl (.classMem R (syn_cvv)) (.classMem C (syn_cvv))
  have p0006 :=
    @g_syl
      (syn_wa (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa
            (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
              (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))
        (syn_wa (.classMem X C) (.classMem Y C)))
      (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (.classMem R (syn_cvv))
      p0004 p0005
  have p0008 :=
    @g_simpr (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv)))
      (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
          (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C)))
  have p0009 :=
    @g_simpl
      (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
        (syn_wbr R (syn_cconnex) C))
      (syn_wss R (syn_cxp C C))
  have p0010 :=
    @g_syl
      (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa
          (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
            (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))
      (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
          (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C)))
      (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
        (syn_wbr R (syn_cconnex) C))
      p0008 p0009
  have p0011 :=
    @g_syl
      (syn_wa (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa
            (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
              (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))
        (syn_wa (.classMem X C) (.classMem Y C)))
      (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa
          (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
            (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))
      (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
        (syn_wbr R (syn_cconnex) C))
      p0002 p0010
  have p0012 :=
    @g_simpl (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
      (syn_wbr R (syn_cconnex) C)
  have p0013 :=
    @g_syl
      (syn_wa (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa
            (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
              (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))
        (syn_wa (.classMem X C) (.classMem Y C)))
      (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
        (syn_wbr R (syn_cconnex) C))
      (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) p0011 p0012
  have p0016 :=
    @g_simpr
      (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
        (syn_wbr R (syn_cconnex) C))
      (syn_wss R (syn_cxp C C))
  have p0017 :=
    @g_syl
      (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa
          (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
            (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))
      (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
          (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C)))
      (syn_wss R (syn_cxp C C)) p0008 p0016
  have p0018 :=
    @g_syl
      (syn_wa (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa
            (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
              (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))
        (syn_wa (.classMem X C) (.classMem Y C)))
      (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa
          (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
            (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))
      (syn_wss R (syn_cxp C C)) p0002 p0017
  have p0019 :=
    @g_jca
      (syn_wa (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa
            (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
              (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))
        (syn_wa (.classMem X C) (.classMem Y C)))
      (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
      (syn_wss R (syn_cxp C C)) p0013 p0018
  have p0020 :=
    @g_simpr
      (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa
          (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
            (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))
      (syn_wa (.classMem X C) (.classMem Y C))
  have p0021 :=
    @g_jca
      (syn_wa (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa
            (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
              (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))
        (syn_wa (.classMem X C) (.classMem Y C)))
      (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
        (syn_wss R (syn_cxp C C)))
      (syn_wa (.classMem X C) (.classMem Y C)) p0019 p0020
  have p0022 :=
    @g_jca
      (syn_wa (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa
            (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
              (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))
        (syn_wa (.classMem X C) (.classMem Y C)))
      (.classMem R (syn_cvv))
      (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
          (syn_wss R (syn_cxp C C))) (syn_wa (.classMem X C) (.classMem Y C)))
      p0006 p0021
  have p0023 := @g_brlnqordkern C R X Y dv_cache_0001
  have p0024 :=
    @g_syl
      (syn_wa (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa
            (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
              (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))
        (syn_wa (.classMem X C) (.classMem Y C)))
      (syn_wa (.classMem R (syn_cvv)) (syn_wa
          (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
            (syn_wss R (syn_cxp C C))) (syn_wa (.classMem X C) (.classMem Y C))))
      (syn_wb (syn_wbr (syn_cec X (syn_clnker R)) (syn_clnqord R C) (syn_cec Y (syn_clnker R)))
        (syn_wbr X R Y))
      p0022 p0023
  have p0030 := @g_lnkerexg R
  have p0031 :=
    @g_syl
      (syn_wa (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa
            (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
              (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))
        (syn_wa (.classMem X C) (.classMem Y C)))
      (.classMem R (syn_cvv)) (.classMem (syn_clnker R) (syn_cvv)) p0006 p0030
  have p0032 := @g_ecexg Y (syn_cvv) (syn_clnker R)
  have p0033 :=
    @g_syl
      (syn_wa (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa
            (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
              (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))
        (syn_wa (.classMem X C) (.classMem Y C)))
      (.classMem (syn_clnker R) (syn_cvv))
      (.classMem (syn_cec Y (syn_clnker R)) (syn_cvv)) p0031 p0032
  have p0034 := @g_ideqg (syn_cec X (syn_clnker R)) (syn_cec Y (syn_clnker R)) (syn_cvv)
  have p0035 :=
    @g_syl
      (syn_wa (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa
            (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
              (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))
        (syn_wa (.classMem X C) (.classMem Y C)))
      (.classMem (syn_cec Y (syn_clnker R)) (syn_cvv))
      (syn_wb (syn_wbr (syn_cec X (syn_clnker R)) (syn_cid) (syn_cec Y (syn_clnker R)))
        (.classEq (syn_cec X (syn_clnker R)) (syn_cec Y (syn_clnker R))))
      p0033 p0034
  have p0036 :=
    @g_notbid
      (syn_wa (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa
            (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
              (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))
        (syn_wa (.classMem X C) (.classMem Y C)))
      (syn_wbr (syn_cec X (syn_clnker R)) (syn_cid) (syn_cec Y (syn_clnker R)))
      (.classEq (syn_cec X (syn_clnker R)) (syn_cec Y (syn_clnker R))) p0035
  have p0037 :=
    @g_anbi12d
      (syn_wa (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa
            (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
              (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))
        (syn_wa (.classMem X C) (.classMem Y C)))
      (syn_wbr (syn_cec X (syn_clnker R)) (syn_clnqord R C) (syn_cec Y (syn_clnker R)))
      (syn_wbr X R Y)
      (.neg (syn_wbr (syn_cec X (syn_clnker R)) (syn_cid) (syn_cec Y (syn_clnker R))))
      (.neg (.classEq (syn_cec X (syn_clnker R)) (syn_cec Y (syn_clnker R)))) p0024 p0036
  have p0038 :=
    @g_bitrd
      (syn_wa (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa
            (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
              (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))
        (syn_wa (.classMem X C) (.classMem Y C)))
      (syn_wbr (syn_cec X (syn_clnker R)) (syn_cdif (syn_clnqord R C) (syn_cid))
        (syn_cec Y (syn_clnker R)))
      (syn_wa (syn_wbr (syn_cec X (syn_clnker R)) (syn_clnqord R C) (syn_cec Y (syn_clnker R)))
        (.neg (syn_wbr (syn_cec X (syn_clnker R)) (syn_cid) (syn_cec Y (syn_clnker R)))))
      (syn_wa (syn_wbr X R Y)
        (.neg (.classEq (syn_cec X (syn_clnker R)) (syn_cec Y (syn_clnker R)))))
      p0001 p0037
  have p0039 := @g_lnkereceqb C R X Y dv_cache_0001
  have p0040 :=
    @g_notbid
      (syn_wa (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa
            (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
              (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))
        (syn_wa (.classMem X C) (.classMem Y C)))
      (.classEq (syn_cec X (syn_clnker R)) (syn_cec Y (syn_clnker R)))
      (syn_wa (syn_wbr X R Y) (syn_wbr Y R X)) p0039
  have p0041 :=
    @g_anbi2d
      (syn_wa (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa
            (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
              (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))
        (syn_wa (.classMem X C) (.classMem Y C)))
      (.neg (.classEq (syn_cec X (syn_clnker R)) (syn_cec Y (syn_clnker R))))
      (.neg (syn_wa (syn_wbr X R Y) (syn_wbr Y R X))) (syn_wbr X R Y) p0040
  have p0042 :=
    @g_bitrd
      (syn_wa (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa
            (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
              (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))
        (syn_wa (.classMem X C) (.classMem Y C)))
      (syn_wbr (syn_cec X (syn_clnker R)) (syn_cdif (syn_clnqord R C) (syn_cid))
        (syn_cec Y (syn_clnker R)))
      (syn_wa (syn_wbr X R Y)
        (.neg (.classEq (syn_cec X (syn_clnker R)) (syn_cec Y (syn_clnker R)))))
      (syn_wa (syn_wbr X R Y) (.neg (syn_wa (syn_wbr X R Y) (syn_wbr Y R X)))) p0038 p0041
  have p0043 := @g_id (syn_wbr X R Y)
  have p0044 := @g_biantrurd (syn_wbr X R Y) (syn_wbr X R Y) (syn_wbr Y R X) p0043
  have p0045 :=
    @g_notbid (syn_wbr X R Y) (syn_wbr Y R X) (syn_wa (syn_wbr X R Y) (syn_wbr Y R X))
      p0044
  have p0046 :=
    @g_pm5_32i (syn_wbr X R Y) (.neg (syn_wbr Y R X))
      (.neg (syn_wa (syn_wbr X R Y) (syn_wbr Y R X))) p0045
  have p0047 :=
    @g_bicomi (syn_wa (syn_wbr X R Y) (.neg (syn_wbr Y R X)))
      (syn_wa (syn_wbr X R Y) (.neg (syn_wa (syn_wbr X R Y) (syn_wbr Y R X)))) p0046
  have p0048 :=
    @g_a1i
      (syn_wb (syn_wa (syn_wbr X R Y) (.neg (syn_wa (syn_wbr X R Y) (syn_wbr Y R X))))
        (syn_wa (syn_wbr X R Y) (.neg (syn_wbr Y R X))))
      (syn_wa (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa
            (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
              (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))
        (syn_wa (.classMem X C) (.classMem Y C)))
      p0047
  have p0049 :=
    @g_bitrd
      (syn_wa (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa
            (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
              (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))
        (syn_wa (.classMem X C) (.classMem Y C)))
      (syn_wbr (syn_cec X (syn_clnker R)) (syn_cdif (syn_clnqord R C) (syn_cid))
        (syn_cec Y (syn_clnker R)))
      (syn_wa (syn_wbr X R Y) (.neg (syn_wa (syn_wbr X R Y) (syn_wbr Y R X))))
      (syn_wa (syn_wbr X R Y) (.neg (syn_wbr Y R X))) p0042 p0048
  have p0050 := @g_brdif X Y R (syn_ccnv R)
  have p0051 := @g_brcnv X Y R
  have p0052 := @g_notbii (syn_wbr X (syn_ccnv R) Y) (syn_wbr Y R X) p0051
  have p0053 :=
    @g_anbi2i (.neg (syn_wbr X (syn_ccnv R) Y)) (.neg (syn_wbr Y R X)) (syn_wbr X R Y)
      p0052
  have p0054 :=
    @g_bitri (syn_wbr X (syn_cdif R (syn_ccnv R)) Y)
      (syn_wa (syn_wbr X R Y) (.neg (syn_wbr X (syn_ccnv R) Y)))
      (syn_wa (syn_wbr X R Y) (.neg (syn_wbr Y R X))) p0050 p0053
  have p0055 :=
    @g_a1i
      (syn_wb (syn_wbr X (syn_cdif R (syn_ccnv R)) Y)
        (syn_wa (syn_wbr X R Y) (.neg (syn_wbr Y R X))))
      (syn_wa (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa
            (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
              (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))
        (syn_wa (.classMem X C) (.classMem Y C)))
      p0054
  have p0056 :=
    @g_bitr4d
      (syn_wa (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa
            (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
              (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))
        (syn_wa (.classMem X C) (.classMem Y C)))
      (syn_wbr (syn_cec X (syn_clnker R)) (syn_cdif (syn_clnqord R C) (syn_cid))
        (syn_cec Y (syn_clnker R)))
      (syn_wa (syn_wbr X R Y) (.neg (syn_wbr Y R X)))
      (syn_wbr X (syn_cdif R (syn_ccnv R)) Y) p0049 p0055
  exact p0056


end NFChoice.DirectNominalPrf.WPPReplay

end

/-! Certificates from `NominalWPPReplayChunk015Compact001Part013`. -/


section

namespace NFChoice.DirectNominalPrf.WPPReplay

open scoped Fol
open NFChoice.Foundation
open NFChoice.SemanticCore
open NFChoice.ReplaySupport
open NFChoice.Compiler.CompactSourceSyntax

@[expose]
noncomputable def g_lnquounionb (u : Var) (C : Class) (R : Class) (S : Class)
    (dv_C_R : Disjoint C.fv R.fv) :
    Nominal.NPrf
      (.imp (syn_wa (syn_wa (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv)))
              (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
                  (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))
            (syn_wss S (syn_clnquo R C))) (.classMem (.cv u) C))
        (syn_wb (.classMem (.cv u) (syn_cuni S))
          (.classMem (syn_cec (.cv u) (syn_clnker R)) S))) :=
  by
  let proofSupport : Finset Var := ({ u } : Finset Var) ∪ C.fv ∪ R.fv ∪ S.fv
  let b : Var := freshVar proofSupport 0
  let w : Var := freshVar proofSupport 1
  have fresh_b : b ∉ proofSupport :=
    by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_b_ne_u : b ≠ u := by
    intro h
    exact
      fresh_b
        (Finset.mem_union_left _ (Finset.mem_union_left _
            (Finset.mem_union_left _ (Finset.mem_singleton.mpr h))))
  have fresh_b_not_C : b ∉ C.fv := by
    intro h
    exact
      fresh_b
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))
  have fresh_b_not_R : b ∉ R.fv := by
    intro h
    exact fresh_b (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_b_not_S : b ∉ S.fv := by
    intro h
    exact fresh_b (Finset.mem_union_right _ (h))
  have fresh_w : w ∉ proofSupport :=
    by
    change freshVar proofSupport 1 ∉ proofSupport
    exact freshVar_not_mem proofSupport 1
  have fresh_w_ne_u : w ≠ u := by
    intro h
    exact
      fresh_w
        (Finset.mem_union_left _ (Finset.mem_union_left _
            (Finset.mem_union_left _ (Finset.mem_singleton.mpr h))))
  have fresh_w_not_C : w ∉ C.fv := by
    intro h
    exact
      fresh_w
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))
  have fresh_w_not_R : w ∉ R.fv := by
    intro h
    exact fresh_w (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_w_not_S : w ∉ S.fv := by
    intro h
    exact fresh_w (Finset.mem_union_right _ (h))
  have fresh_b_ne_w : b ≠ w :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have fresh_w_ne_b : w ≠ b := Ne.symm fresh_b_ne_w
  have dv_cache_0001 : b ∉ ((Class.cv u)).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : b ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_b_ne_u, not_false_eq_true])
  have dv_cache_0002 : b ∉ (S).fv :=
    by
    clear dv_cache_0001
    exact
      (by
        have compact_fv_not_mem_empty : b ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_b_not_S, not_false_eq_true])
  have dv_cache_0003 : Disjoint (C).fv ((Class.cv b)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact
      (show Disjoint (C).fv ((Class.cv b)).fv from (by
          rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv];
          exact
            (show Disjoint ((C).fv) (({ b } : Finset Var)) from
              (Finset.disjoint_singleton_right.mpr
                (show b ∉ (C).fv from (by exact fresh_b_not_C))))))
  have dv_cache_0004 : Disjoint (C).fv (R).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact
      (show Disjoint (C).fv (R).fv from (show Disjoint (C).fv (R).fv from (by exact dv_C_R)))
  have dv_cache_0005 : w ∉ (C).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact
      (by
        have compact_fv_not_mem_empty : w ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_w_not_C, not_false_eq_true])
  have dv_cache_0006 : Disjoint ((Class.cv b)).fv (R).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact
      (show Disjoint ((Class.cv b)).fv (R).fv from (by
          rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv];
          exact
            (show Disjoint (({ b } : Finset Var)) ((R).fv) from
              (Finset.disjoint_singleton_left.mpr
                (show b ∉ (R).fv from (by exact fresh_b_not_R))))))
  have dv_cache_0007 : w ∉ ((Class.cv b)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006
    exact
      (by
        have compact_fv_not_mem_empty : w ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_w_ne_b, not_false_eq_true])
  have dv_cache_0008 : w ∉ (R).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007
    exact
      (by
        have compact_fv_not_mem_empty : w ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_w_not_R, not_false_eq_true])
  have dv_cache_0009 : w ∉ ((Wff.classMem (syn_cec (.cv u) (syn_clnker R)) S)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008
    exact
      (by
        have compact_fv_not_mem_empty : w ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cec,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_clnker, Finset.mem_union,
          Finset.mem_singleton, fresh_w_ne_u, fresh_w_not_R, fresh_w_not_S, or_false,
          not_false_eq_true])
  have dv_cache_0010 :
    w ∉
      ((syn_wa (syn_wa (syn_wa (syn_wa
                (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa
                    (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
                      (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))
                (syn_wss S (syn_clnquo R C))) (.classMem (.cv u) C))
            (.classMem (.cv u) (syn_cuni S)))
          (syn_wa (.classMem (.cv b) S) (.classMem (.cv u) (.cv b))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009
    exact
      (by
        have compact_fv_not_mem_empty : w ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cref,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ctrans,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cconnex,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wss,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxp,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_clnquo,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cuni, Finset.mem_union,
          Finset.mem_singleton, fresh_w_not_R, fresh_w_not_C, fresh_w_not_S, fresh_w_ne_u,
          fresh_w_ne_b, compact_fv_not_mem_empty, or_false, not_false_eq_true])
  have dv_cache_0011 : b ∉ ((Wff.classMem (syn_cec (.cv u) (syn_clnker R)) S)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010
    exact
      (by
        have compact_fv_not_mem_empty : b ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cec,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_clnker, Finset.mem_union,
          Finset.mem_singleton, fresh_b_ne_u, fresh_b_not_R, fresh_b_not_S, or_false,
          not_false_eq_true])
  have dv_cache_0012 :
    b ∉
      ((syn_wa (syn_wa (syn_wa (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv)))
                (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
                    (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))
              (syn_wss S (syn_clnquo R C))) (.classMem (.cv u) C))
          (.classMem (.cv u) (syn_cuni S)))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
    exact
      (by
        have compact_fv_not_mem_empty : b ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cref,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ctrans,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cconnex,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wss,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxp,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_clnquo,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cuni, Finset.mem_union,
          Finset.mem_singleton, fresh_b_not_R, fresh_b_not_C, fresh_b_not_S, fresh_b_ne_u,
          compact_fv_not_mem_empty, or_false, not_false_eq_true])
  have p0000 :=
    @g_simpr
      (syn_wa (syn_wa (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa
              (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
                (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))
          (syn_wss S (syn_clnquo R C))) (.classMem (.cv u) C))
      (.classMem (.cv u) (syn_cuni S))
  have p0001 := @g_eluni2 b (.cv u) S dv_cache_0001 dv_cache_0002
  have p0002 :=
    @g_biimpi (.classMem (.cv u) (syn_cuni S)) (syn_wrex b S (.classMem (.cv u) (.cv b)))
      p0001
  have p0003 :=
    @g_syl
      (syn_wa (syn_wa (syn_wa (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv)))
              (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
                  (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))
            (syn_wss S (syn_clnquo R C))) (.classMem (.cv u) C))
        (.classMem (.cv u) (syn_cuni S)))
      (.classMem (.cv u) (syn_cuni S)) (syn_wrex b S (.classMem (.cv u) (.cv b))) p0000
      p0002
  have p0004 :=
    @g_simpl
      (syn_wa (syn_wa (syn_wa (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv)))
              (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
                  (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))
            (syn_wss S (syn_clnquo R C))) (.classMem (.cv u) C))
        (.classMem (.cv u) (syn_cuni S)))
      (syn_wa (.classMem (.cv b) S) (.classMem (.cv u) (.cv b)))
  have p0005 :=
    @g_simpl
      (syn_wa (syn_wa (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa
              (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
                (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))
          (syn_wss S (syn_clnquo R C))) (.classMem (.cv u) C))
      (.classMem (.cv u) (syn_cuni S))
  have p0006 :=
    @g_syl
      (syn_wa (syn_wa (syn_wa (syn_wa
              (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa
                  (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
                    (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))
              (syn_wss S (syn_clnquo R C))) (.classMem (.cv u) C))
          (.classMem (.cv u) (syn_cuni S)))
        (syn_wa (.classMem (.cv b) S) (.classMem (.cv u) (.cv b))))
      (syn_wa (syn_wa (syn_wa (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv)))
              (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
                  (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))
            (syn_wss S (syn_clnquo R C))) (.classMem (.cv u) C))
        (.classMem (.cv u) (syn_cuni S)))
      (syn_wa (syn_wa (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa
              (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
                (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))
          (syn_wss S (syn_clnquo R C))) (.classMem (.cv u) C))
      p0004 p0005
  have p0007 :=
    @g_simpl
      (syn_wa (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa
            (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
              (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))
        (syn_wss S (syn_clnquo R C)))
      (.classMem (.cv u) C)
  have p0008 :=
    @g_simpr
      (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa
          (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
            (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))
      (syn_wss S (syn_clnquo R C))
  have p0009 :=
    @g_syl
      (syn_wa (syn_wa (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa
              (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
                (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))
          (syn_wss S (syn_clnquo R C))) (.classMem (.cv u) C))
      (syn_wa (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa
            (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
              (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))
        (syn_wss S (syn_clnquo R C)))
      (syn_wss S (syn_clnquo R C)) p0007 p0008
  have p0010 :=
    @g_syl
      (syn_wa (syn_wa (syn_wa (syn_wa
              (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa
                  (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
                    (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))
              (syn_wss S (syn_clnquo R C))) (.classMem (.cv u) C))
          (.classMem (.cv u) (syn_cuni S)))
        (syn_wa (.classMem (.cv b) S) (.classMem (.cv u) (.cv b))))
      (syn_wa (syn_wa (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa
              (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
                (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))
          (syn_wss S (syn_clnquo R C))) (.classMem (.cv u) C))
      (syn_wss S (syn_clnquo R C)) p0006 p0009
  have p0011 :=
    @g_simpr
      (syn_wa (syn_wa (syn_wa (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv)))
              (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
                  (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))
            (syn_wss S (syn_clnquo R C))) (.classMem (.cv u) C))
        (.classMem (.cv u) (syn_cuni S)))
      (syn_wa (.classMem (.cv b) S) (.classMem (.cv u) (.cv b)))
  have p0012 := @g_simpl (.classMem (.cv b) S) (.classMem (.cv u) (.cv b))
  have p0013 :=
    @g_syl
      (syn_wa (syn_wa (syn_wa (syn_wa
              (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa
                  (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
                    (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))
              (syn_wss S (syn_clnquo R C))) (.classMem (.cv u) C))
          (.classMem (.cv u) (syn_cuni S)))
        (syn_wa (.classMem (.cv b) S) (.classMem (.cv u) (.cv b))))
      (syn_wa (.classMem (.cv b) S) (.classMem (.cv u) (.cv b))) (.classMem (.cv b) S)
      p0011 p0012
  have p0014 :=
    @g_sseldd
      (syn_wa (syn_wa (syn_wa (syn_wa
              (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa
                  (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
                    (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))
              (syn_wss S (syn_clnquo R C))) (.classMem (.cv u) C))
          (.classMem (.cv u) (syn_cuni S)))
        (syn_wa (.classMem (.cv b) S) (.classMem (.cv u) (.cv b))))
      S (syn_clnquo R C) (.cv b) p0010 p0013
  have p0015 := @g_vex b
  have p0016 :=
    @g_ellnquo w C (.cv b) R dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006
      dv_cache_0007 dv_cache_0008 p0015
  have p0017 :=
    @g_a1i
      (syn_wb (.classMem (.cv b) (syn_clnquo R C))
        (syn_wrex w C (.classEq (.cv b) (syn_cec (.cv w) (syn_clnker R)))))
      (syn_wa (syn_wa (syn_wa (syn_wa
              (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa
                  (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
                    (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))
              (syn_wss S (syn_clnquo R C))) (.classMem (.cv u) C))
          (.classMem (.cv u) (syn_cuni S)))
        (syn_wa (.classMem (.cv b) S) (.classMem (.cv u) (.cv b))))
      p0016
  have p0018 :=
    @g_mpbid
      (syn_wa (syn_wa (syn_wa (syn_wa
              (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa
                  (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
                    (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))
              (syn_wss S (syn_clnquo R C))) (.classMem (.cv u) C))
          (.classMem (.cv u) (syn_cuni S)))
        (syn_wa (.classMem (.cv b) S) (.classMem (.cv u) (.cv b))))
      (.classMem (.cv b) (syn_clnquo R C))
      (syn_wrex w C (.classEq (.cv b) (syn_cec (.cv w) (syn_clnker R)))) p0014 p0017
  have p0019 :=
    @g_simpr
      (syn_wa (syn_wa (syn_wa (syn_wa
              (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa
                  (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
                    (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))
              (syn_wss S (syn_clnquo R C))) (.classMem (.cv u) C))
          (.classMem (.cv u) (syn_cuni S)))
        (syn_wa (.classMem (.cv b) S) (.classMem (.cv u) (.cv b))))
      (syn_wa (.classMem (.cv w) C) (.classEq (.cv b) (syn_cec (.cv w) (syn_clnker R))))
  have p0020 :=
    @g_simpr (.classMem (.cv w) C) (.classEq (.cv b) (syn_cec (.cv w) (syn_clnker R)))
  have p0021 :=
    @g_syl
      (syn_wa (syn_wa (syn_wa (syn_wa (syn_wa
                (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa
                    (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
                      (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))
                (syn_wss S (syn_clnquo R C))) (.classMem (.cv u) C))
            (.classMem (.cv u) (syn_cuni S)))
          (syn_wa (.classMem (.cv b) S) (.classMem (.cv u) (.cv b))))
        (syn_wa (.classMem (.cv w) C) (.classEq (.cv b) (syn_cec (.cv w) (syn_clnker R)))))
      (syn_wa (.classMem (.cv w) C) (.classEq (.cv b) (syn_cec (.cv w) (syn_clnker R))))
      (.classEq (.cv b) (syn_cec (.cv w) (syn_clnker R))) p0019 p0020
  have p0022 :=
    @g_simpl
      (syn_wa (syn_wa (syn_wa (syn_wa
              (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa
                  (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
                    (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))
              (syn_wss S (syn_clnquo R C))) (.classMem (.cv u) C))
          (.classMem (.cv u) (syn_cuni S)))
        (syn_wa (.classMem (.cv b) S) (.classMem (.cv u) (.cv b))))
      (syn_wa (.classMem (.cv w) C) (.classEq (.cv b) (syn_cec (.cv w) (syn_clnker R))))
  have p0024 := @g_simpr (.classMem (.cv b) S) (.classMem (.cv u) (.cv b))
  have p0025 :=
    @g_syl
      (syn_wa (syn_wa (syn_wa (syn_wa
              (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa
                  (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
                    (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))
              (syn_wss S (syn_clnquo R C))) (.classMem (.cv u) C))
          (.classMem (.cv u) (syn_cuni S)))
        (syn_wa (.classMem (.cv b) S) (.classMem (.cv u) (.cv b))))
      (syn_wa (.classMem (.cv b) S) (.classMem (.cv u) (.cv b)))
      (.classMem (.cv u) (.cv b)) p0011 p0024
  have p0026 :=
    @g_syl
      (syn_wa (syn_wa (syn_wa (syn_wa (syn_wa
                (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa
                    (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
                      (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))
                (syn_wss S (syn_clnquo R C))) (.classMem (.cv u) C))
            (.classMem (.cv u) (syn_cuni S)))
          (syn_wa (.classMem (.cv b) S) (.classMem (.cv u) (.cv b))))
        (syn_wa (.classMem (.cv w) C) (.classEq (.cv b) (syn_cec (.cv w) (syn_clnker R)))))
      (syn_wa (syn_wa (syn_wa (syn_wa
              (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa
                  (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
                    (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))
              (syn_wss S (syn_clnquo R C))) (.classMem (.cv u) C))
          (.classMem (.cv u) (syn_cuni S)))
        (syn_wa (.classMem (.cv b) S) (.classMem (.cv u) (.cv b))))
      (.classMem (.cv u) (.cv b)) p0022 p0025
  have p0030 :=
    @g_eleq2d
      (syn_wa (syn_wa (syn_wa (syn_wa (syn_wa
                (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa
                    (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
                      (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))
                (syn_wss S (syn_clnquo R C))) (.classMem (.cv u) C))
            (.classMem (.cv u) (syn_cuni S)))
          (syn_wa (.classMem (.cv b) S) (.classMem (.cv u) (.cv b))))
        (syn_wa (.classMem (.cv w) C) (.classEq (.cv b) (syn_cec (.cv w) (syn_clnker R)))))
      (.cv b) (syn_cec (.cv w) (syn_clnker R)) (.cv u) p0021
  have p0031 :=
    @g_mpbid
      (syn_wa (syn_wa (syn_wa (syn_wa (syn_wa
                (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa
                    (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
                      (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))
                (syn_wss S (syn_clnquo R C))) (.classMem (.cv u) C))
            (.classMem (.cv u) (syn_cuni S)))
          (syn_wa (.classMem (.cv b) S) (.classMem (.cv u) (.cv b))))
        (syn_wa (.classMem (.cv w) C) (.classEq (.cv b) (syn_cec (.cv w) (syn_clnker R)))))
      (.classMem (.cv u) (.cv b)) (.classMem (.cv u) (syn_cec (.cv w) (syn_clnker R)))
      p0026 p0030
  have p0032 := @g_ellnkerecg (.cv u) (.cv w) R
  have p0033 :=
    @g_a1i
      (syn_wb (.classMem (.cv u) (syn_cec (.cv w) (syn_clnker R)))
        (syn_wa (syn_wbr (.cv w) R (.cv u)) (syn_wbr (.cv u) R (.cv w))))
      (syn_wa (syn_wa (syn_wa (syn_wa (syn_wa
                (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa
                    (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
                      (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))
                (syn_wss S (syn_clnquo R C))) (.classMem (.cv u) C))
            (.classMem (.cv u) (syn_cuni S)))
          (syn_wa (.classMem (.cv b) S) (.classMem (.cv u) (.cv b))))
        (syn_wa (.classMem (.cv w) C) (.classEq (.cv b) (syn_cec (.cv w) (syn_clnker R)))))
      p0032
  have p0034 :=
    @g_mpbid
      (syn_wa (syn_wa (syn_wa (syn_wa (syn_wa
                (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa
                    (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
                      (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))
                (syn_wss S (syn_clnquo R C))) (.classMem (.cv u) C))
            (.classMem (.cv u) (syn_cuni S)))
          (syn_wa (.classMem (.cv b) S) (.classMem (.cv u) (.cv b))))
        (syn_wa (.classMem (.cv w) C) (.classEq (.cv b) (syn_cec (.cv w) (syn_clnker R)))))
      (.classMem (.cv u) (syn_cec (.cv w) (syn_clnker R)))
      (syn_wa (syn_wbr (.cv w) R (.cv u)) (syn_wbr (.cv u) R (.cv w))) p0031 p0033
  have p0039 :=
    @g_syl
      (syn_wa (syn_wa (syn_wa (syn_wa (syn_wa
                (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa
                    (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
                      (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))
                (syn_wss S (syn_clnquo R C))) (.classMem (.cv u) C))
            (.classMem (.cv u) (syn_cuni S)))
          (syn_wa (.classMem (.cv b) S) (.classMem (.cv u) (.cv b))))
        (syn_wa (.classMem (.cv w) C) (.classEq (.cv b) (syn_cec (.cv w) (syn_clnker R)))))
      (syn_wa (syn_wa (syn_wa (syn_wa
              (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa
                  (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
                    (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))
              (syn_wss S (syn_clnquo R C))) (.classMem (.cv u) C))
          (.classMem (.cv u) (syn_cuni S)))
        (syn_wa (.classMem (.cv b) S) (.classMem (.cv u) (.cv b))))
      (syn_wa (syn_wa (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa
              (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
                (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))
          (syn_wss S (syn_clnquo R C))) (.classMem (.cv u) C))
      p0022 p0006
  have p0041 :=
    @g_simpl
      (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa
          (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
            (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))
      (syn_wss S (syn_clnquo R C))
  have p0042 :=
    @g_syl
      (syn_wa (syn_wa (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa
              (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
                (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))
          (syn_wss S (syn_clnquo R C))) (.classMem (.cv u) C))
      (syn_wa (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa
            (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
              (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))
        (syn_wss S (syn_clnquo R C)))
      (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa
          (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
            (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))
      p0007 p0041
  have p0043 :=
    @g_syl
      (syn_wa (syn_wa (syn_wa (syn_wa (syn_wa
                (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa
                    (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
                      (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))
                (syn_wss S (syn_clnquo R C))) (.classMem (.cv u) C))
            (.classMem (.cv u) (syn_cuni S)))
          (syn_wa (.classMem (.cv b) S) (.classMem (.cv u) (.cv b))))
        (syn_wa (.classMem (.cv w) C) (.classEq (.cv b) (syn_cec (.cv w) (syn_clnker R)))))
      (syn_wa (syn_wa (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa
              (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
                (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))
          (syn_wss S (syn_clnquo R C))) (.classMem (.cv u) C))
      (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa
          (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
            (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))
      p0039 p0042
  have p0045 :=
    @g_simpl (.classMem (.cv w) C) (.classEq (.cv b) (syn_cec (.cv w) (syn_clnker R)))
  have p0046 :=
    @g_syl
      (syn_wa (syn_wa (syn_wa (syn_wa (syn_wa
                (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa
                    (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
                      (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))
                (syn_wss S (syn_clnquo R C))) (.classMem (.cv u) C))
            (.classMem (.cv u) (syn_cuni S)))
          (syn_wa (.classMem (.cv b) S) (.classMem (.cv u) (.cv b))))
        (syn_wa (.classMem (.cv w) C) (.classEq (.cv b) (syn_cec (.cv w) (syn_clnker R)))))
      (syn_wa (.classMem (.cv w) C) (.classEq (.cv b) (syn_cec (.cv w) (syn_clnker R))))
      (.classMem (.cv w) C) p0019 p0045
  have p0052 :=
    @g_simpr
      (syn_wa (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa
            (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
              (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))
        (syn_wss S (syn_clnquo R C)))
      (.classMem (.cv u) C)
  have p0053 :=
    @g_syl
      (syn_wa (syn_wa (syn_wa (syn_wa (syn_wa
                (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa
                    (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
                      (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))
                (syn_wss S (syn_clnquo R C))) (.classMem (.cv u) C))
            (.classMem (.cv u) (syn_cuni S)))
          (syn_wa (.classMem (.cv b) S) (.classMem (.cv u) (.cv b))))
        (syn_wa (.classMem (.cv w) C) (.classEq (.cv b) (syn_cec (.cv w) (syn_clnker R)))))
      (syn_wa (syn_wa (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa
              (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
                (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))
          (syn_wss S (syn_clnquo R C))) (.classMem (.cv u) C))
      (.classMem (.cv u) C) p0039 p0052
  have p0054 :=
    @g_jca
      (syn_wa (syn_wa (syn_wa (syn_wa (syn_wa
                (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa
                    (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
                      (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))
                (syn_wss S (syn_clnquo R C))) (.classMem (.cv u) C))
            (.classMem (.cv u) (syn_cuni S)))
          (syn_wa (.classMem (.cv b) S) (.classMem (.cv u) (.cv b))))
        (syn_wa (.classMem (.cv w) C) (.classEq (.cv b) (syn_cec (.cv w) (syn_clnker R)))))
      (.classMem (.cv w) C) (.classMem (.cv u) C) p0046 p0053
  have p0055 :=
    @g_jca
      (syn_wa (syn_wa (syn_wa (syn_wa (syn_wa
                (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa
                    (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
                      (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))
                (syn_wss S (syn_clnquo R C))) (.classMem (.cv u) C))
            (.classMem (.cv u) (syn_cuni S)))
          (syn_wa (.classMem (.cv b) S) (.classMem (.cv u) (.cv b))))
        (syn_wa (.classMem (.cv w) C) (.classEq (.cv b) (syn_cec (.cv w) (syn_clnker R)))))
      (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa
          (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
            (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))
      (syn_wa (.classMem (.cv w) C) (.classMem (.cv u) C)) p0043 p0054
  have p0056 := @g_lnkereceqb C R (.cv w) (.cv u) dv_cache_0004
  have p0057 :=
    @g_syl
      (syn_wa (syn_wa (syn_wa (syn_wa (syn_wa
                (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa
                    (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
                      (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))
                (syn_wss S (syn_clnquo R C))) (.classMem (.cv u) C))
            (.classMem (.cv u) (syn_cuni S)))
          (syn_wa (.classMem (.cv b) S) (.classMem (.cv u) (.cv b))))
        (syn_wa (.classMem (.cv w) C) (.classEq (.cv b) (syn_cec (.cv w) (syn_clnker R)))))
      (syn_wa (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa
            (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
              (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))
        (syn_wa (.classMem (.cv w) C) (.classMem (.cv u) C)))
      (syn_wb (.classEq (syn_cec (.cv w) (syn_clnker R)) (syn_cec (.cv u) (syn_clnker R)))
        (syn_wa (syn_wbr (.cv w) R (.cv u)) (syn_wbr (.cv u) R (.cv w))))
      p0055 p0056
  have p0058 :=
    @g_mpbird
      (syn_wa (syn_wa (syn_wa (syn_wa (syn_wa
                (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa
                    (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
                      (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))
                (syn_wss S (syn_clnquo R C))) (.classMem (.cv u) C))
            (.classMem (.cv u) (syn_cuni S)))
          (syn_wa (.classMem (.cv b) S) (.classMem (.cv u) (.cv b))))
        (syn_wa (.classMem (.cv w) C) (.classEq (.cv b) (syn_cec (.cv w) (syn_clnker R)))))
      (.classEq (syn_cec (.cv w) (syn_clnker R)) (syn_cec (.cv u) (syn_clnker R)))
      (syn_wa (syn_wbr (.cv w) R (.cv u)) (syn_wbr (.cv u) R (.cv w))) p0034 p0057
  have p0059 :=
    @g_eqtrd
      (syn_wa (syn_wa (syn_wa (syn_wa (syn_wa
                (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa
                    (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
                      (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))
                (syn_wss S (syn_clnquo R C))) (.classMem (.cv u) C))
            (.classMem (.cv u) (syn_cuni S)))
          (syn_wa (.classMem (.cv b) S) (.classMem (.cv u) (.cv b))))
        (syn_wa (.classMem (.cv w) C) (.classEq (.cv b) (syn_cec (.cv w) (syn_clnker R)))))
      (.cv b) (syn_cec (.cv w) (syn_clnker R)) (syn_cec (.cv u) (syn_clnker R)) p0021
      p0058
  have p0064 :=
    @g_syl
      (syn_wa (syn_wa (syn_wa (syn_wa (syn_wa
                (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa
                    (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
                      (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))
                (syn_wss S (syn_clnquo R C))) (.classMem (.cv u) C))
            (.classMem (.cv u) (syn_cuni S)))
          (syn_wa (.classMem (.cv b) S) (.classMem (.cv u) (.cv b))))
        (syn_wa (.classMem (.cv w) C) (.classEq (.cv b) (syn_cec (.cv w) (syn_clnker R)))))
      (syn_wa (syn_wa (syn_wa (syn_wa
              (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa
                  (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
                    (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))
              (syn_wss S (syn_clnquo R C))) (.classMem (.cv u) C))
          (.classMem (.cv u) (syn_cuni S)))
        (syn_wa (.classMem (.cv b) S) (.classMem (.cv u) (.cv b))))
      (.classMem (.cv b) S) p0022 p0013
  have p0065 :=
    @g_eqeltrrd
      (syn_wa (syn_wa (syn_wa (syn_wa (syn_wa
                (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa
                    (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
                      (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))
                (syn_wss S (syn_clnquo R C))) (.classMem (.cv u) C))
            (.classMem (.cv u) (syn_cuni S)))
          (syn_wa (.classMem (.cv b) S) (.classMem (.cv u) (.cv b))))
        (syn_wa (.classMem (.cv w) C) (.classEq (.cv b) (syn_cec (.cv w) (syn_clnker R)))))
      (.cv b) (syn_cec (.cv u) (syn_clnker R)) S p0059 p0064
  have p0066 :=
    @g_rexlimddv
      (syn_wa (syn_wa (syn_wa (syn_wa
              (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa
                  (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
                    (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))
              (syn_wss S (syn_clnquo R C))) (.classMem (.cv u) C))
          (.classMem (.cv u) (syn_cuni S)))
        (syn_wa (.classMem (.cv b) S) (.classMem (.cv u) (.cv b))))
      (.classEq (.cv b) (syn_cec (.cv w) (syn_clnker R)))
      (.classMem (syn_cec (.cv u) (syn_clnker R)) S) w C dv_cache_0009 dv_cache_0010 p0018
      p0065
  have p0067 :=
    @g_rexlimddv
      (syn_wa (syn_wa (syn_wa (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv)))
              (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
                  (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))
            (syn_wss S (syn_clnquo R C))) (.classMem (.cv u) C))
        (.classMem (.cv u) (syn_cuni S)))
      (.classMem (.cv u) (.cv b)) (.classMem (syn_cec (.cv u) (syn_clnker R)) S) b S
      dv_cache_0011 dv_cache_0012 p0003 p0066
  have p0068 :=
    @g_ex
      (syn_wa (syn_wa (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa
              (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
                (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))
          (syn_wss S (syn_clnquo R C))) (.classMem (.cv u) C))
      (.classMem (.cv u) (syn_cuni S)) (.classMem (syn_cec (.cv u) (syn_clnker R)) S)
      p0067
  have p0069 :=
    @g_simpl
      (syn_wa (syn_wa (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa
              (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
                (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))
          (syn_wss S (syn_clnquo R C))) (.classMem (.cv u) C))
      (.classMem (syn_cec (.cv u) (syn_clnker R)) S)
  have p0073 :=
    @g_simpr (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv)))
      (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
          (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C)))
  have p0074 :=
    @g_syl
      (syn_wa (syn_wa (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa
              (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
                (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))
          (syn_wss S (syn_clnquo R C))) (.classMem (.cv u) C))
      (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa
          (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
            (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))
      (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
          (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C)))
      p0042 p0073
  have p0075 :=
    @g_simpl
      (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
        (syn_wbr R (syn_cconnex) C))
      (syn_wss R (syn_cxp C C))
  have p0076 :=
    @g_syl
      (syn_wa (syn_wa (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa
              (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
                (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))
          (syn_wss S (syn_clnquo R C))) (.classMem (.cv u) C))
      (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
          (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C)))
      (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
        (syn_wbr R (syn_cconnex) C))
      p0074 p0075
  have p0077 :=
    @g_simpl (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
      (syn_wbr R (syn_cconnex) C)
  have p0078 :=
    @g_syl
      (syn_wa (syn_wa (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa
              (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
                (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))
          (syn_wss S (syn_clnquo R C))) (.classMem (.cv u) C))
      (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
        (syn_wbr R (syn_cconnex) C))
      (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) p0076 p0077
  have p0079 := @g_simpl (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)
  have p0080 :=
    @g_syl
      (syn_wa (syn_wa (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa
              (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
                (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))
          (syn_wss S (syn_clnquo R C))) (.classMem (.cv u) C))
      (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
      (syn_wbr R (syn_cref) C) p0078 p0079
  have p0081 :=
    @g_syl
      (syn_wa (syn_wa (syn_wa (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv)))
              (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
                  (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))
            (syn_wss S (syn_clnquo R C))) (.classMem (.cv u) C))
        (.classMem (syn_cec (.cv u) (syn_clnker R)) S))
      (syn_wa (syn_wa (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa
              (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
                (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))
          (syn_wss S (syn_clnquo R C))) (.classMem (.cv u) C))
      (syn_wbr R (syn_cref) C) p0069 p0080
  have p0084 :=
    @g_syl
      (syn_wa (syn_wa (syn_wa (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv)))
              (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
                  (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))
            (syn_wss S (syn_clnquo R C))) (.classMem (.cv u) C))
        (.classMem (syn_cec (.cv u) (syn_clnker R)) S))
      (syn_wa (syn_wa (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa
              (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
                (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))
          (syn_wss S (syn_clnquo R C))) (.classMem (.cv u) C))
      (.classMem (.cv u) C) p0069 p0052
  have p0085 :=
    @g_refd
      (syn_wa (syn_wa (syn_wa (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv)))
              (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
                  (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))
            (syn_wss S (syn_clnquo R C))) (.classMem (.cv u) C))
        (.classMem (syn_cec (.cv u) (syn_clnker R)) S))
      C R (.cv u) p0081 p0084
  have p0103 :=
    @g_jca
      (syn_wa (syn_wa (syn_wa (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv)))
              (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
                  (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))
            (syn_wss S (syn_clnquo R C))) (.classMem (.cv u) C))
        (.classMem (syn_cec (.cv u) (syn_clnker R)) S))
      (syn_wbr (.cv u) R (.cv u)) (syn_wbr (.cv u) R (.cv u)) p0085 p0085
  have p0104 := @g_ellnkerecg (.cv u) (.cv u) R
  have p0105 :=
    @g_a1i
      (syn_wb (.classMem (.cv u) (syn_cec (.cv u) (syn_clnker R)))
        (syn_wa (syn_wbr (.cv u) R (.cv u)) (syn_wbr (.cv u) R (.cv u))))
      (syn_wa (syn_wa (syn_wa (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv)))
              (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
                  (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))
            (syn_wss S (syn_clnquo R C))) (.classMem (.cv u) C))
        (.classMem (syn_cec (.cv u) (syn_clnker R)) S))
      p0104
  have p0106 :=
    @g_mpbird
      (syn_wa (syn_wa (syn_wa (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv)))
              (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
                  (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))
            (syn_wss S (syn_clnquo R C))) (.classMem (.cv u) C))
        (.classMem (syn_cec (.cv u) (syn_clnker R)) S))
      (.classMem (.cv u) (syn_cec (.cv u) (syn_clnker R)))
      (syn_wa (syn_wbr (.cv u) R (.cv u)) (syn_wbr (.cv u) R (.cv u))) p0103 p0105
  have p0107 :=
    @g_simpr
      (syn_wa (syn_wa (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa
              (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
                (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))
          (syn_wss S (syn_clnquo R C))) (.classMem (.cv u) C))
      (.classMem (syn_cec (.cv u) (syn_clnker R)) S)
  have p0108 :=
    @g_jca
      (syn_wa (syn_wa (syn_wa (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv)))
              (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
                  (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))
            (syn_wss S (syn_clnquo R C))) (.classMem (.cv u) C))
        (.classMem (syn_cec (.cv u) (syn_clnker R)) S))
      (.classMem (.cv u) (syn_cec (.cv u) (syn_clnker R)))
      (.classMem (syn_cec (.cv u) (syn_clnker R)) S) p0106 p0107
  have p0109 := @g_elunii (.cv u) (syn_cec (.cv u) (syn_clnker R)) S
  have p0110 :=
    @g_syl
      (syn_wa (syn_wa (syn_wa (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv)))
              (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
                  (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))
            (syn_wss S (syn_clnquo R C))) (.classMem (.cv u) C))
        (.classMem (syn_cec (.cv u) (syn_clnker R)) S))
      (syn_wa (.classMem (.cv u) (syn_cec (.cv u) (syn_clnker R)))
        (.classMem (syn_cec (.cv u) (syn_clnker R)) S))
      (.classMem (.cv u) (syn_cuni S)) p0108 p0109
  have p0111 :=
    @g_ex
      (syn_wa (syn_wa (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa
              (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
                (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))
          (syn_wss S (syn_clnquo R C))) (.classMem (.cv u) C))
      (.classMem (syn_cec (.cv u) (syn_clnker R)) S) (.classMem (.cv u) (syn_cuni S))
      p0110
  have p0112 :=
    @g_impbid
      (syn_wa (syn_wa (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa
              (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
                (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))
          (syn_wss S (syn_clnquo R C))) (.classMem (.cv u) C))
      (.classMem (.cv u) (syn_cuni S)) (.classMem (syn_cec (.cv u) (syn_clnker R)) S)
      p0068 p0111
  exact p0112


end NFChoice.DirectNominalPrf.WPPReplay

end

/-! Certificates from `NominalWPPReplayChunk015Compact001Part014`. -/


section

namespace NFChoice.DirectNominalPrf.WPPReplay

open scoped Fol
open NFChoice.Foundation
open NFChoice.SemanticCore
open NFChoice.ReplaySupport
open NFChoice.Compiler.CompactSourceSyntax

@[expose]
noncomputable def g_lnqordwe (C : Class) (R : Class) (dv_C_R : Disjoint C.fv R.fv) :
    Nominal.NPrf
      (.imp (syn_wa (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa
              (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
                (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))
          (syn_wbr (syn_cdif R (syn_ccnv R)) (syn_cfound) C))
        (syn_wbr (syn_clnqord R C) (syn_cwe) (syn_clnquo R C))) :=
  by
  let proofSupport : Finset Var := C.fv ∪ R.fv
  let x : Var := freshVar proofSupport 0
  let y : Var := freshVar proofSupport 1
  let z : Var := freshVar proofSupport 2
  let u : Var := freshVar proofSupport 3
  let t : Var := freshVar proofSupport 4
  let w : Var := freshVar proofSupport 5
  let b : Var := freshVar proofSupport 6
  let v : Var := freshVar proofSupport 7
  have fresh_x : x ∉ proofSupport :=
    by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_x_not_C : x ∉ C.fv := by
    intro h
    exact fresh_x (Finset.mem_union_left _ (h))
  have fresh_x_not_R : x ∉ R.fv := by
    intro h
    exact fresh_x (Finset.mem_union_right _ (h))
  have fresh_y : y ∉ proofSupport :=
    by
    change freshVar proofSupport 1 ∉ proofSupport
    exact freshVar_not_mem proofSupport 1
  have fresh_y_not_C : y ∉ C.fv := by
    intro h
    exact fresh_y (Finset.mem_union_left _ (h))
  have fresh_y_not_R : y ∉ R.fv := by
    intro h
    exact fresh_y (Finset.mem_union_right _ (h))
  have fresh_z : z ∉ proofSupport :=
    by
    change freshVar proofSupport 2 ∉ proofSupport
    exact freshVar_not_mem proofSupport 2
  have fresh_z_not_C : z ∉ C.fv := by
    intro h
    exact fresh_z (Finset.mem_union_left _ (h))
  have fresh_z_not_R : z ∉ R.fv := by
    intro h
    exact fresh_z (Finset.mem_union_right _ (h))
  have fresh_u : u ∉ proofSupport :=
    by
    change freshVar proofSupport 3 ∉ proofSupport
    exact freshVar_not_mem proofSupport 3
  have fresh_u_not_C : u ∉ C.fv := by
    intro h
    exact fresh_u (Finset.mem_union_left _ (h))
  have fresh_u_not_R : u ∉ R.fv := by
    intro h
    exact fresh_u (Finset.mem_union_right _ (h))
  have fresh_t : t ∉ proofSupport :=
    by
    change freshVar proofSupport 4 ∉ proofSupport
    exact freshVar_not_mem proofSupport 4
  have fresh_t_not_C : t ∉ C.fv := by
    intro h
    exact fresh_t (Finset.mem_union_left _ (h))
  have fresh_t_not_R : t ∉ R.fv := by
    intro h
    exact fresh_t (Finset.mem_union_right _ (h))
  have fresh_w : w ∉ proofSupport :=
    by
    change freshVar proofSupport 5 ∉ proofSupport
    exact freshVar_not_mem proofSupport 5
  have fresh_w_not_C : w ∉ C.fv := by
    intro h
    exact fresh_w (Finset.mem_union_left _ (h))
  have fresh_w_not_R : w ∉ R.fv := by
    intro h
    exact fresh_w (Finset.mem_union_right _ (h))
  have fresh_b : b ∉ proofSupport :=
    by
    change freshVar proofSupport 6 ∉ proofSupport
    exact freshVar_not_mem proofSupport 6
  have fresh_b_not_C : b ∉ C.fv := by
    intro h
    exact fresh_b (Finset.mem_union_left _ (h))
  have fresh_b_not_R : b ∉ R.fv := by
    intro h
    exact fresh_b (Finset.mem_union_right _ (h))
  have fresh_v : v ∉ proofSupport :=
    by
    change freshVar proofSupport 7 ∉ proofSupport
    exact freshVar_not_mem proofSupport 7
  have fresh_v_not_C : v ∉ C.fv := by
    intro h
    exact fresh_v (Finset.mem_union_left _ (h))
  have fresh_v_not_R : v ∉ R.fv := by
    intro h
    exact fresh_v (Finset.mem_union_right _ (h))
  have fresh_x_ne_y : x ≠ y :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have fresh_y_ne_x : y ≠ x := Ne.symm fresh_x_ne_y
  have fresh_x_ne_z : x ≠ z :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 2
    exact freshVar_injective proofSupport (i := 0) (j := 2) (by decide)
  have fresh_z_ne_x : z ≠ x := Ne.symm fresh_x_ne_z
  have fresh_x_ne_u : x ≠ u :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 3
    exact freshVar_injective proofSupport (i := 0) (j := 3) (by decide)
  have fresh_u_ne_x : u ≠ x := Ne.symm fresh_x_ne_u
  have fresh_x_ne_t : x ≠ t :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 4
    exact freshVar_injective proofSupport (i := 0) (j := 4) (by decide)
  have fresh_t_ne_x : t ≠ x := Ne.symm fresh_x_ne_t
  have fresh_x_ne_w : x ≠ w :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 5
    exact freshVar_injective proofSupport (i := 0) (j := 5) (by decide)
  have fresh_w_ne_x : w ≠ x := Ne.symm fresh_x_ne_w
  have fresh_x_ne_b : x ≠ b :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 6
    exact freshVar_injective proofSupport (i := 0) (j := 6) (by decide)
  have fresh_b_ne_x : b ≠ x := Ne.symm fresh_x_ne_b
  have fresh_x_ne_v : x ≠ v :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 7
    exact freshVar_injective proofSupport (i := 0) (j := 7) (by decide)
  have fresh_v_ne_x : v ≠ x := Ne.symm fresh_x_ne_v
  have fresh_y_ne_z : y ≠ z :=
    by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 2
    exact freshVar_injective proofSupport (i := 1) (j := 2) (by decide)
  have fresh_z_ne_y : z ≠ y := Ne.symm fresh_y_ne_z
  have fresh_y_ne_u : y ≠ u :=
    by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 3
    exact freshVar_injective proofSupport (i := 1) (j := 3) (by decide)
  have fresh_u_ne_y : u ≠ y := Ne.symm fresh_y_ne_u
  have fresh_y_ne_t : y ≠ t :=
    by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 4
    exact freshVar_injective proofSupport (i := 1) (j := 4) (by decide)
  have fresh_y_ne_v : y ≠ v :=
    by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 7
    exact freshVar_injective proofSupport (i := 1) (j := 7) (by decide)
  have fresh_v_ne_y : v ≠ y := Ne.symm fresh_y_ne_v
  have fresh_z_ne_u : z ≠ u :=
    by
    change freshVar proofSupport 2 ≠ freshVar proofSupport 3
    exact freshVar_injective proofSupport (i := 2) (j := 3) (by decide)
  have fresh_u_ne_z : u ≠ z := Ne.symm fresh_z_ne_u
  have fresh_u_ne_t : u ≠ t :=
    by
    change freshVar proofSupport 3 ≠ freshVar proofSupport 4
    exact freshVar_injective proofSupport (i := 3) (j := 4) (by decide)
  have fresh_t_ne_u : t ≠ u := Ne.symm fresh_u_ne_t
  have fresh_u_ne_w : u ≠ w :=
    by
    change freshVar proofSupport 3 ≠ freshVar proofSupport 5
    exact freshVar_injective proofSupport (i := 3) (j := 5) (by decide)
  have fresh_w_ne_u : w ≠ u := Ne.symm fresh_u_ne_w
  have fresh_u_ne_v : u ≠ v :=
    by
    change freshVar proofSupport 3 ≠ freshVar proofSupport 7
    exact freshVar_injective proofSupport (i := 3) (j := 7) (by decide)
  have fresh_v_ne_u : v ≠ u := Ne.symm fresh_u_ne_v
  have fresh_t_ne_w : t ≠ w :=
    by
    change freshVar proofSupport 4 ≠ freshVar proofSupport 5
    exact freshVar_injective proofSupport (i := 4) (j := 5) (by decide)
  have fresh_w_ne_t : w ≠ t := Ne.symm fresh_t_ne_w
  have fresh_t_ne_v : t ≠ v :=
    by
    change freshVar proofSupport 4 ≠ freshVar proofSupport 7
    exact freshVar_injective proofSupport (i := 4) (j := 7) (by decide)
  have fresh_v_ne_t : v ≠ t := Ne.symm fresh_t_ne_v
  have fresh_w_ne_b : w ≠ b :=
    by
    change freshVar proofSupport 5 ≠ freshVar proofSupport 6
    exact freshVar_injective proofSupport (i := 5) (j := 6) (by decide)
  have fresh_b_ne_w : b ≠ w := Ne.symm fresh_w_ne_b
  have dv_cache_0001 : Disjoint (C).fv (R).fv := by
    exact
      (show Disjoint (C).fv (R).fv from (show Disjoint (C).fv (R).fv from (by exact dv_C_R)))
  have dv_cache_0002 : w ∉ ((syn_cuni (.cv x))).fv :=
    by
    clear dv_cache_0001
    exact
      (by
        have compact_fv_not_mem_empty : w ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cuni,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton, fresh_w_ne_x,
          not_false_eq_true])
  have dv_cache_0003 : b ∉ ((Class.cv x)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact
      (by
        have compact_fv_not_mem_empty : b ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_b_ne_x, not_false_eq_true])
  have dv_cache_0004 : Disjoint (C).fv ((Class.cv b)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact
      (show Disjoint (C).fv ((Class.cv b)).fv from (by
          rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv];
          exact
            (show Disjoint ((C).fv) (({ b } : Finset Var)) from
              (Finset.disjoint_singleton_right.mpr
                (show b ∉ (C).fv from (by exact fresh_b_not_C))))))
  have dv_cache_0005 : w ∉ (C).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact
      (by
        have compact_fv_not_mem_empty : w ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_w_not_C, not_false_eq_true])
  have dv_cache_0006 : Disjoint ((Class.cv b)).fv (R).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact
      (show Disjoint ((Class.cv b)).fv (R).fv from (by
          rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv];
          exact
            (show Disjoint (({ b } : Finset Var)) ((R).fv) from
              (Finset.disjoint_singleton_left.mpr
                (show b ∉ (R).fv from (by exact fresh_b_not_R))))))
  have dv_cache_0007 : w ∉ ((Class.cv b)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006
    exact
      (by
        have compact_fv_not_mem_empty : w ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_w_ne_b, not_false_eq_true])
  have dv_cache_0008 : w ∉ (R).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007
    exact
      (by
        have compact_fv_not_mem_empty : w ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_w_not_R, not_false_eq_true])
  have dv_cache_0009 :
    w ∉
      ((syn_wa (syn_wa (syn_wa (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv)))
                (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
                    (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))
              (syn_wbr (syn_cdif R (syn_ccnv R)) (syn_cfound) C))
            (syn_wa (syn_wss (.cv x) (syn_clnquo R C)) (syn_wne (.cv x) (syn_c0))))
          (.classMem (.cv b) (.cv x)))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008
    exact
      (by
        have compact_fv_not_mem_empty : w ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cref,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ctrans,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cconnex,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wss,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxp,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdif,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfound,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_clnquo,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wne,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0, Finset.mem_union,
          Finset.mem_singleton, fresh_w_not_R, fresh_w_not_C, fresh_w_ne_x, fresh_w_ne_b,
          compact_fv_not_mem_empty, or_false, not_false_eq_true])
  have dv_cache_0010 : b ∉ ((syn_wrex w C (.classMem (.cv w) (syn_cuni (.cv x))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009
    exact
      (by
        have compact_fv_not_mem_empty : b ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wrex,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cuni, Finset.mem_union,
          Finset.mem_erase, Finset.mem_singleton, fresh_b_not_C, fresh_b_ne_w,
          fresh_b_ne_x, or_false, and_false, not_false_eq_true])
  have dv_cache_0011 :
    b ∉
      ((syn_wa (syn_wa (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa
                (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
                  (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))
            (syn_wbr (syn_cdif R (syn_ccnv R)) (syn_cfound) C))
          (syn_wa (syn_wss (.cv x) (syn_clnquo R C)) (syn_wne (.cv x) (syn_c0))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010
    exact
      (by
        have compact_fv_not_mem_empty : b ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cref,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ctrans,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cconnex,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wss,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxp,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdif,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfound,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_clnquo,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wne,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0, Finset.mem_union,
          Finset.mem_singleton, fresh_b_not_R, fresh_b_not_C, fresh_b_ne_x,
          compact_fv_not_mem_empty, or_false, not_false_eq_true])
  have dv_cache_0012 : u ∉ (C).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
    exact
      (by
        have compact_fv_not_mem_empty : u ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_u_not_C, not_false_eq_true])
  have dv_cache_0013 : t ∉ (C).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012
    exact
      (by
        have compact_fv_not_mem_empty : t ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_t_not_C, not_false_eq_true])
  have dv_cache_0014 : u ∉ ((syn_cdif R (syn_ccnv R))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013
    exact
      (by
        have compact_fv_not_mem_empty : u ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdif,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv, Finset.mem_union,
          fresh_u_not_R, or_false, not_false_eq_true])
  have dv_cache_0015 : t ∉ ((syn_cdif R (syn_ccnv R))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014
    exact
      (by
        have compact_fv_not_mem_empty : t ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdif,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv, Finset.mem_union,
          fresh_t_not_R, or_false, not_false_eq_true])
  have dv_cache_0016 : w ∉ ((Wff.classMem (.cv u) (syn_cuni (.cv x)))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015
    exact
      (by
        have compact_fv_not_mem_empty : w ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cuni, Finset.mem_union,
          Finset.mem_singleton, fresh_w_ne_u, fresh_w_ne_x, or_false, not_false_eq_true])
  have dv_cache_0017 : u ∉ ((Wff.classMem (.cv w) (syn_cuni (.cv x)))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016
    exact
      (by
        have compact_fv_not_mem_empty : u ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cuni, Finset.mem_union,
          Finset.mem_singleton, fresh_u_ne_w, fresh_u_ne_x, or_false, not_false_eq_true])
  have dv_cache_0018 : t ∉ ((Wff.classMem (.cv w) (syn_cuni (.cv x)))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
    exact
      (by
        have compact_fv_not_mem_empty : t ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cuni, Finset.mem_union,
          Finset.mem_singleton, fresh_t_ne_w, fresh_t_ne_x, or_false, not_false_eq_true])
  have dv_cache_0019 : w ∉ ((Wff.classMem (.cv t) (syn_cuni (.cv x)))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018
    exact
      (by
        have compact_fv_not_mem_empty : w ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cuni, Finset.mem_union,
          Finset.mem_singleton, fresh_w_ne_t, fresh_w_ne_x, or_false, not_false_eq_true])
  have dv_cache_0020 : w ≠ u :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019
    exact (show w ≠ u from (by exact fresh_w_ne_u))
  have dv_cache_0021 : w ≠ t :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020
    exact (show w ≠ t from (by exact fresh_w_ne_t))
  have dv_cache_0022 : u ≠ t :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021
    exact (show u ≠ t from (by exact fresh_u_ne_t))
  have dv_cache_0023 : Disjoint (C).fv ((Class.cv y)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022
    exact
      (show Disjoint (C).fv ((Class.cv y)).fv from (by
          rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv];
          exact
            (show Disjoint ((C).fv) (({ y } : Finset Var)) from
              (Finset.disjoint_singleton_right.mpr
                (show y ∉ (C).fv from (by exact fresh_y_not_C))))))
  have dv_cache_0024 : v ∉ (C).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
    exact
      (by
        have compact_fv_not_mem_empty : v ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_v_not_C, not_false_eq_true])
  have dv_cache_0025 : Disjoint ((Class.cv y)).fv (R).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024
    exact
      (show Disjoint ((Class.cv y)).fv (R).fv from (by
          rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv];
          exact
            (show Disjoint (({ y } : Finset Var)) ((R).fv) from
              (Finset.disjoint_singleton_left.mpr
                (show y ∉ (R).fv from (by exact fresh_y_not_R))))))
  have dv_cache_0026 : v ∉ ((Class.cv y)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025
    exact
      (by
        have compact_fv_not_mem_empty : v ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_v_ne_y, not_false_eq_true])
  have dv_cache_0027 : v ∉ (R).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026
    exact
      (by
        have compact_fv_not_mem_empty : v ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_v_not_R, not_false_eq_true])
  have dv_cache_0028 : t ∉ ((Class.cv v)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027
    exact
      (by
        have compact_fv_not_mem_empty : t ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_t_ne_v, not_false_eq_true])
  have dv_cache_0029 :
    t ∉
      ((Wff.imp (syn_wa (.classMem (.cv v) (syn_cuni (.cv x)))
            (syn_wbr (.cv v) (syn_cdif R (syn_ccnv R)) (.cv u)))
          (.classEq (.cv v) (.cv u)))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028
    exact
      (by
        have compact_fv_not_mem_empty : t ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cuni,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdif,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, Finset.mem_union,
          Finset.mem_singleton, fresh_t_ne_v, fresh_t_ne_x, fresh_t_ne_u, fresh_t_not_R,
          or_false, not_false_eq_true])
  have dv_cache_0030 : v ∉ ((Wff.classEq (.cv y) (syn_cec (.cv u) (syn_clnker R)))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
    exact
      (by
        have compact_fv_not_mem_empty : v ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cec,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_clnker, Finset.mem_union,
          Finset.mem_singleton, fresh_v_ne_y, fresh_v_ne_u, fresh_v_not_R, or_false,
          not_false_eq_true])
  have dv_cache_0031 :
    v ∉
      ((syn_wa (syn_wa (syn_wa (syn_wa
                (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa
                    (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
                      (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))
                (syn_wbr (syn_cdif R (syn_ccnv R)) (syn_cfound) C))
              (syn_wa (syn_wss (.cv x) (syn_clnquo R C)) (syn_wne (.cv x) (syn_c0))))
            (syn_wa (.classMem (.cv u) C) (syn_wa (.classMem (.cv u) (syn_cuni (.cv x)))
                (syn_wral t C (.imp (syn_wa (.classMem (.cv t) (syn_cuni (.cv x)))
                      (syn_wbr (.cv t) (syn_cdif R (syn_ccnv R)) (.cv u)))
                    (.classEq (.cv t) (.cv u))))))) (syn_wa (.classMem (.cv y) (.cv x))
            (syn_wbr (.cv y) (syn_clnqord R C) (syn_cec (.cv u) (syn_clnker R)))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
      dv_cache_0030
    exact
      (by
        have compact_fv_not_mem_empty : v ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cref,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ctrans,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cconnex,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wss,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxp,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdif,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfound,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_clnquo,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wne,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cuni,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wral,
          NFChoice.Compiler.CoreFVSimp.fv_wff_imp,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_clnqord,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cec,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_clnker, Finset.mem_union,
          Finset.mem_erase, Finset.mem_singleton, fresh_v_not_R, fresh_v_not_C,
          fresh_v_ne_x, fresh_v_ne_u, fresh_v_ne_t, fresh_v_ne_y,
          compact_fv_not_mem_empty, or_false, and_false, not_false_eq_true])
  have dv_cache_0032 :
    y ∉
      ((syn_wa (syn_wa (syn_wa (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv)))
                (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
                    (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))
              (syn_wbr (syn_cdif R (syn_ccnv R)) (syn_cfound) C))
            (syn_wa (syn_wss (.cv x) (syn_clnquo R C)) (syn_wne (.cv x) (syn_c0))))
          (syn_wa (.classMem (.cv u) C) (syn_wa (.classMem (.cv u) (syn_cuni (.cv x)))
              (syn_wral t C (.imp (syn_wa (.classMem (.cv t) (syn_cuni (.cv x)))
                    (syn_wbr (.cv t) (syn_cdif R (syn_ccnv R)) (.cv u)))
                  (.classEq (.cv t) (.cv u)))))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
      dv_cache_0030 dv_cache_0031
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cref,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ctrans,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cconnex,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wss,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxp,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdif,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfound,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_clnquo,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wne,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cuni,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wral,
          NFChoice.Compiler.CoreFVSimp.fv_wff_imp,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, Finset.mem_union, Finset.mem_erase,
          Finset.mem_singleton, fresh_y_not_R, fresh_y_not_C, fresh_y_ne_x, fresh_y_ne_u,
          fresh_y_ne_t, compact_fv_not_mem_empty, or_false, and_false, not_false_eq_true])
  have dv_cache_0033 : y ∉ ((Wff.classEq (.cv z) (syn_cec (.cv u) (syn_clnker R)))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
      dv_cache_0030 dv_cache_0031 dv_cache_0032
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cec,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_clnker, Finset.mem_union,
          Finset.mem_singleton, fresh_y_ne_z, fresh_y_ne_u, fresh_y_not_R, or_false,
          not_false_eq_true])
  have dv_cache_0034 : z ∉ ((syn_cec (.cv u) (syn_clnker R))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
      dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033
    exact
      (by
        have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cec,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_clnker, Finset.mem_union,
          Finset.mem_singleton, fresh_z_ne_u, fresh_z_not_R, or_false, not_false_eq_true])
  have dv_cache_0035 : z ∉ ((Class.cv x)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
      dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034
    exact
      (by
        have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_z_ne_x, not_false_eq_true])
  have dv_cache_0036 :
    z ∉
      ((syn_wral y (.cv x)
          (.imp (syn_wbr (.cv y) (syn_clnqord R C) (syn_cec (.cv u) (syn_clnker R)))
            (.classEq (.cv y) (syn_cec (.cv u) (syn_clnker R)))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
      dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035
    exact
      (by
        have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wral,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CoreFVSimp.fv_wff_imp,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_clnqord,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cec,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_clnker,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, Finset.mem_union, Finset.mem_erase,
          Finset.mem_singleton, fresh_z_ne_x, fresh_z_ne_y, fresh_z_ne_u, fresh_z_not_R,
          fresh_z_not_C, or_false, and_false, not_false_eq_true])
  have dv_cache_0037 :
    u ∉
      ((syn_wrex z (.cv x) (syn_wral y (.cv x) (.imp (syn_wbr (.cv y) (syn_clnqord R C) (.cv z))
              (.classEq (.cv y) (.cv z)))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
      dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035
      dv_cache_0036
    exact
      (by
        have compact_fv_not_mem_empty : u ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wrex,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wral,
          NFChoice.Compiler.CoreFVSimp.fv_wff_imp,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_clnqord,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, Finset.mem_union, Finset.mem_erase,
          Finset.mem_singleton, fresh_u_ne_x, fresh_u_ne_y, fresh_u_ne_z, fresh_u_not_C,
          fresh_u_not_R, or_false, and_false, not_false_eq_true])
  have dv_cache_0038 :
    u ∉
      ((syn_wa (syn_wa (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa
                (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
                  (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))
            (syn_wbr (syn_cdif R (syn_ccnv R)) (syn_cfound) C))
          (syn_wa (syn_wss (.cv x) (syn_clnquo R C)) (syn_wne (.cv x) (syn_c0))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
      dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035
      dv_cache_0036 dv_cache_0037
    exact
      (by
        have compact_fv_not_mem_empty : u ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cref,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ctrans,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cconnex,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wss,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxp,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdif,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfound,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_clnquo,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wne,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0, Finset.mem_union,
          Finset.mem_singleton, fresh_u_not_R, fresh_u_not_C, fresh_u_ne_x,
          compact_fv_not_mem_empty, or_false, not_false_eq_true])
  have dv_cache_0039 : x ∉ ((syn_clnquo R C)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
      dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035
      dv_cache_0036 dv_cache_0037 dv_cache_0038
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_clnquo,
          Finset.mem_union, fresh_x_not_C, fresh_x_not_R, or_false, not_false_eq_true])
  have dv_cache_0040 : y ∉ ((syn_clnquo R C)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
      dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035
      dv_cache_0036 dv_cache_0037 dv_cache_0038 dv_cache_0039
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_clnquo,
          Finset.mem_union, fresh_y_not_C, fresh_y_not_R, or_false, not_false_eq_true])
  have dv_cache_0041 : z ∉ ((syn_clnquo R C)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
      dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035
      dv_cache_0036 dv_cache_0037 dv_cache_0038 dv_cache_0039 dv_cache_0040
    exact
      (by
        have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_clnquo,
          Finset.mem_union, fresh_z_not_C, fresh_z_not_R, or_false, not_false_eq_true])
  have dv_cache_0042 : x ∉ ((syn_clnqord R C)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
      dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035
      dv_cache_0036 dv_cache_0037 dv_cache_0038 dv_cache_0039 dv_cache_0040 dv_cache_0041
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_clnqord,
          Finset.mem_union, fresh_x_not_C, fresh_x_not_R, or_false, not_false_eq_true])
  have dv_cache_0043 : y ∉ ((syn_clnqord R C)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
      dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035
      dv_cache_0036 dv_cache_0037 dv_cache_0038 dv_cache_0039 dv_cache_0040 dv_cache_0041
      dv_cache_0042
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_clnqord,
          Finset.mem_union, fresh_y_not_C, fresh_y_not_R, or_false, not_false_eq_true])
  have dv_cache_0044 : z ∉ ((syn_clnqord R C)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
      dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035
      dv_cache_0036 dv_cache_0037 dv_cache_0038 dv_cache_0039 dv_cache_0040 dv_cache_0041
      dv_cache_0042 dv_cache_0043
    exact
      (by
        have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_clnqord,
          Finset.mem_union, fresh_z_not_C, fresh_z_not_R, or_false, not_false_eq_true])
  have dv_cache_0045 :
    x ∉
      ((syn_wa (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) (syn_wa
              (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
                (syn_wbr R (syn_cconnex) C)) (syn_wss R (syn_cxp C C))))
          (syn_wbr (syn_cdif R (syn_ccnv R)) (syn_cfound) C))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
      dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035
      dv_cache_0036 dv_cache_0037 dv_cache_0038 dv_cache_0039 dv_cache_0040 dv_cache_0041
      dv_cache_0042 dv_cache_0043 dv_cache_0044
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cref,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ctrans,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cconnex,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wss,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxp,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdif,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfound, Finset.mem_union,
          fresh_x_not_R, fresh_x_not_C, compact_fv_not_mem_empty, or_false,
          not_false_eq_true])
  have dv_cache_0046 : x ≠ y :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
      dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035
      dv_cache_0036 dv_cache_0037 dv_cache_0038 dv_cache_0039 dv_cache_0040 dv_cache_0041
      dv_cache_0042 dv_cache_0043 dv_cache_0044 dv_cache_0045
    exact (show x ≠ y from (by exact fresh_x_ne_y))
  have dv_cache_0047 : x ≠ z :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
      dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035
      dv_cache_0036 dv_cache_0037 dv_cache_0038 dv_cache_0039 dv_cache_0040 dv_cache_0041
      dv_cache_0042 dv_cache_0043 dv_cache_0044 dv_cache_0045 dv_cache_0046
    exact (show x ≠ z from (by exact fresh_x_ne_z))
  have dv_cache_0048 : y ≠ z :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
      dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035
      dv_cache_0036 dv_cache_0037 dv_cache_0038 dv_cache_0039 dv_cache_0040 dv_cache_0041
      dv_cache_0042 dv_cache_0043 dv_cache_0044 dv_cache_0045 dv_cache_0046 dv_cache_0047
    exact (show y ≠ z from (by exact fresh_y_ne_z))
  let syntaxFormula0000 : Wff :=
    (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
      (syn_wbr R (syn_cconnex) C))
  let syntaxFormula0001 : Wff := (syn_wa syntaxFormula0000 (syn_wss R (syn_cxp C C)))
  let syntaxFormula0002 : Wff :=
    (syn_wa (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) syntaxFormula0001)
  let syntaxFormula0003 : Wff :=
    (syn_wa syntaxFormula0002 (syn_wbr (syn_cdif R (syn_ccnv R)) (syn_cfound) C))
  let syntaxFormula0004 : Wff :=
    (syn_wa syntaxFormula0003
      (syn_wa (syn_wss (.cv x) (syn_clnquo R C)) (syn_wne (.cv x) (syn_c0))))
  let syntaxFormula0005 : Wff := (syn_wa syntaxFormula0004 (.classMem (.cv b) (.cv x)))
  let syntaxFormula0006 : Wff := (syn_wa syntaxFormula0005 (.classMem (.cv w) C))
  let syntaxFormula0007 : Wff :=
    (syn_wa syntaxFormula0006 (.classEq (.cv b) (syn_cec (.cv w) (syn_clnker R))))
  let syntaxFormula0008 : Wff :=
    (syn_wa syntaxFormula0002 (syn_wss (.cv x) (syn_clnquo R C)))
  let syntaxFormula0009 : Wff :=
    (syn_wa (.classMem (.cv t) (syn_cuni (.cv x)))
      (syn_wbr (.cv t) (syn_cdif R (syn_ccnv R)) (.cv u)))
  let syntaxFormula0010 : Wff := (.imp syntaxFormula0009 (.classEq (.cv t) (.cv u)))
  let syntaxFormula0011 : Wff := (syn_wral t C syntaxFormula0010)
  let syntaxFormula0012 : Wff :=
    (syn_wa (.classMem (.cv u) (syn_cuni (.cv x))) syntaxFormula0011)
  let syntaxFormula0013 : Wff := (syn_wa (.classMem (.cv u) C) syntaxFormula0012)
  let syntaxFormula0014 : Wff := (syn_wa syntaxFormula0004 syntaxFormula0013)
  let syntaxFormula0015 : Wff :=
    (syn_wa (.classMem (.cv y) (.cv x))
      (syn_wbr (.cv y) (syn_clnqord R C) (syn_cec (.cv u) (syn_clnker R))))
  let syntaxFormula0016 : Wff := (syn_wa syntaxFormula0014 syntaxFormula0015)
  let syntaxFormula0017 : Wff :=
    (syn_wa (.classMem (.cv v) C) (.classEq (.cv y) (syn_cec (.cv v) (syn_clnker R))))
  let syntaxFormula0018 : Wff := (syn_wa syntaxFormula0016 syntaxFormula0017)
  let syntaxFormula0019 : Wff := (syn_wa syntaxFormula0018 (syn_wbr (.cv u) R (.cv v)))
  let syntaxFormula0020 : Wff :=
    (syn_wa (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
      (syn_wss R (syn_cxp C C)))
  let syntaxFormula0021 : Wff :=
    (syn_wa syntaxFormula0020 (syn_wa (.classMem (.cv v) C) (.classMem (.cv u) C)))
  let syntaxFormula0022 : Wff := (syn_wa (.classMem R (syn_cvv)) syntaxFormula0021)
  let syntaxFormula0023 : Wff :=
    (syn_wbr (syn_cec (.cv v) (syn_clnker R)) (syn_clnqord R C)
      (syn_cec (.cv u) (syn_clnker R)))
  let syntaxFormula0024 : Wff :=
    (syn_wa syntaxFormula0018 (.neg (syn_wbr (.cv u) R (.cv v))))
  let syntaxFormula0025 : Wff :=
    (syn_wa (.classMem (.cv v) (syn_cuni (.cv x)))
      (syn_wbr (.cv v) (syn_cdif R (syn_ccnv R)) (.cv u)))
  let syntaxFormula0026 : Wff := (.imp syntaxFormula0025 (.classEq (.cv v) (.cv u)))
  let syntaxFormula0027 : Wff :=
    (.imp (syn_wbr (.cv y) (syn_clnqord R C) (syn_cec (.cv u) (syn_clnker R)))
      (.classEq (.cv y) (syn_cec (.cv u) (syn_clnker R))))
  let syntaxFormula0028 : Wff := (syn_wral y (.cv x) syntaxFormula0027)
  let syntaxFormula0029 : Wff :=
    (syn_wral y (.cv x)
      (.imp (syn_wbr (.cv y) (syn_clnqord R C) (.cv z)) (.classEq (.cv y) (.cv z))))
  let syntaxFormula0030 : Wff :=
    (syn_wa (syn_wbr (syn_clnqord R C) (syn_cstrict) (syn_clnquo R C))
      (syn_wbr (syn_clnqord R C) (syn_cfound) (syn_clnquo R C)))
  have p0000 :=
    @g_simpl syntaxFormula0002 (syn_wbr (syn_cdif R (syn_ccnv R)) (syn_cfound) C)
  have p0001 := @g_lnqordor C R dv_cache_0001
  have p0002 :=
    @g_syl syntaxFormula0003 syntaxFormula0002
      (syn_wbr (syn_clnqord R C) (syn_cstrict) (syn_clnquo R C)) p0000 p0001
  have p0004 :=
    @g_simpl (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) syntaxFormula0001
  have p0005 :=
    @g_syl syntaxFormula0003 syntaxFormula0002
      (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) p0000 p0004
  have p0006 := @g_lnqordexg C R dv_cache_0001
  have p0007 :=
    @g_syl syntaxFormula0003 (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv)))
      (.classMem (syn_clnqord R C) (syn_cvv)) p0005 p0006
  have p0011 := @g_lnquoexg C R dv_cache_0001
  have p0012 :=
    @g_syl syntaxFormula0003 (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv)))
      (.classMem (syn_clnquo R C) (syn_cvv)) p0005 p0011
  have p0013 := @g_abid2 w (syn_cuni (.cv x)) dv_cache_0002
  have p0014 := @g_vex x
  have p0015 := @g_uniexg (.cv x) (syn_cvv)
  have p0016 := Nominal.mp p0014 p0015
  have p0017 :=
    @g_eqeltri (.cab w (.classMem (.cv w) (syn_cuni (.cv x)))) (syn_cuni (.cv x))
      (syn_cvv) p0013 p0016
  have p0018 := @g_eleq1 (.cv w) (.cv u) (syn_cuni (.cv x))
  have p0019 := @g_eleq1 (.cv w) (.cv t) (syn_cuni (.cv x))
  have p0020 :=
    @g_simpl syntaxFormula0003
      (syn_wa (syn_wss (.cv x) (syn_clnquo R C)) (syn_wne (.cv x) (syn_c0)))
  have p0021 :=
    @g_simpr syntaxFormula0002 (syn_wbr (syn_cdif R (syn_ccnv R)) (syn_cfound) C)
  have p0022 :=
    @g_syl syntaxFormula0004 syntaxFormula0003
      (syn_wbr (syn_cdif R (syn_ccnv R)) (syn_cfound) C) p0020 p0021
  have p0023 :=
    @g_simpr syntaxFormula0003
      (syn_wa (syn_wss (.cv x) (syn_clnquo R C)) (syn_wne (.cv x) (syn_c0)))
  have p0024 := @g_simpr (syn_wss (.cv x) (syn_clnquo R C)) (syn_wne (.cv x) (syn_c0))
  have p0025 :=
    @g_syl syntaxFormula0004
      (syn_wa (syn_wss (.cv x) (syn_clnquo R C)) (syn_wne (.cv x) (syn_c0)))
      (syn_wne (.cv x) (syn_c0)) p0023 p0024
  have p0026 := @g_n0 b (.cv x) dv_cache_0003
  have p0027 :=
    @g_a1i (syn_wb (syn_wne (.cv x) (syn_c0)) (syn_wex b (.classMem (.cv b) (.cv x))))
      syntaxFormula0004 p0026
  have p0028 :=
    @g_mpbid syntaxFormula0004 (syn_wne (.cv x) (syn_c0))
      (syn_wex b (.classMem (.cv b) (.cv x))) p0025 p0027
  have p0029 := @g_simpl syntaxFormula0004 (.classMem (.cv b) (.cv x))
  have p0030 :=
    @g_simpr syntaxFormula0003
      (syn_wa (syn_wss (.cv x) (syn_clnquo R C)) (syn_wne (.cv x) (syn_c0)))
  have p0031 := @g_simpl (syn_wss (.cv x) (syn_clnquo R C)) (syn_wne (.cv x) (syn_c0))
  have p0032 :=
    @g_syl syntaxFormula0004
      (syn_wa (syn_wss (.cv x) (syn_clnquo R C)) (syn_wne (.cv x) (syn_c0)))
      (syn_wss (.cv x) (syn_clnquo R C)) p0030 p0031
  have p0033 :=
    @g_syl syntaxFormula0005 syntaxFormula0004 (syn_wss (.cv x) (syn_clnquo R C)) p0029
      p0032
  have p0034 := @g_simpr syntaxFormula0004 (.classMem (.cv b) (.cv x))
  have p0035 := @g_sseldd syntaxFormula0005 (.cv x) (syn_clnquo R C) (.cv b) p0033 p0034
  have p0036 := @g_vex b
  have p0037 :=
    @g_ellnquo w C (.cv b) R dv_cache_0004 dv_cache_0001 dv_cache_0005 dv_cache_0006
      dv_cache_0007 dv_cache_0008 p0036
  have p0038 :=
    @g_a1i
      (syn_wb (.classMem (.cv b) (syn_clnquo R C))
        (syn_wrex w C (.classEq (.cv b) (syn_cec (.cv w) (syn_clnker R)))))
      syntaxFormula0005 p0037
  have p0039 :=
    @g_mpbid syntaxFormula0005 (.classMem (.cv b) (syn_clnquo R C))
      (syn_wrex w C (.classEq (.cv b) (syn_cec (.cv w) (syn_clnker R)))) p0035 p0038
  have p0040 :=
    @g_simpr syntaxFormula0006 (.classEq (.cv b) (syn_cec (.cv w) (syn_clnker R)))
  have p0041 :=
    @g_simpl syntaxFormula0006 (.classEq (.cv b) (syn_cec (.cv w) (syn_clnker R)))
  have p0042 := @g_simpl syntaxFormula0005 (.classMem (.cv w) C)
  have p0043 := @g_syl syntaxFormula0007 syntaxFormula0006 syntaxFormula0005 p0041 p0042
  have p0044 := @g_simpr syntaxFormula0004 (.classMem (.cv b) (.cv x))
  have p0045 :=
    @g_syl syntaxFormula0007 syntaxFormula0005 (.classMem (.cv b) (.cv x)) p0043 p0044
  have p0046 :=
    @g_eqeltrrd syntaxFormula0007 (.cv b) (syn_cec (.cv w) (syn_clnker R)) (.cv x) p0040
      p0045
  have p0047 :=
    @g_simpl syntaxFormula0006 (.classEq (.cv b) (syn_cec (.cv w) (syn_clnker R)))
  have p0048 := @g_simpl syntaxFormula0005 (.classMem (.cv w) C)
  have p0049 := @g_syl syntaxFormula0007 syntaxFormula0006 syntaxFormula0005 p0047 p0048
  have p0050 := @g_simpl syntaxFormula0004 (.classMem (.cv b) (.cv x))
  have p0051 := @g_syl syntaxFormula0007 syntaxFormula0005 syntaxFormula0004 p0049 p0050
  have p0052 :=
    @g_simpl syntaxFormula0003
      (syn_wa (syn_wss (.cv x) (syn_clnquo R C)) (syn_wne (.cv x) (syn_c0)))
  have p0053 :=
    @g_simpl syntaxFormula0002 (syn_wbr (syn_cdif R (syn_ccnv R)) (syn_cfound) C)
  have p0054 := @g_syl syntaxFormula0004 syntaxFormula0003 syntaxFormula0002 p0052 p0053
  have p0055 := @g_syl syntaxFormula0007 syntaxFormula0004 syntaxFormula0002 p0051 p0054
  have p0056 :=
    @g_simpl syntaxFormula0006 (.classEq (.cv b) (syn_cec (.cv w) (syn_clnker R)))
  have p0057 := @g_simpl syntaxFormula0005 (.classMem (.cv w) C)
  have p0058 := @g_syl syntaxFormula0007 syntaxFormula0006 syntaxFormula0005 p0056 p0057
  have p0059 := @g_simpl syntaxFormula0004 (.classMem (.cv b) (.cv x))
  have p0060 := @g_syl syntaxFormula0007 syntaxFormula0005 syntaxFormula0004 p0058 p0059
  have p0061 :=
    @g_simpr syntaxFormula0003
      (syn_wa (syn_wss (.cv x) (syn_clnquo R C)) (syn_wne (.cv x) (syn_c0)))
  have p0062 := @g_simpl (syn_wss (.cv x) (syn_clnquo R C)) (syn_wne (.cv x) (syn_c0))
  have p0063 :=
    @g_syl syntaxFormula0004
      (syn_wa (syn_wss (.cv x) (syn_clnquo R C)) (syn_wne (.cv x) (syn_c0)))
      (syn_wss (.cv x) (syn_clnquo R C)) p0061 p0062
  have p0064 :=
    @g_syl syntaxFormula0007 syntaxFormula0004 (syn_wss (.cv x) (syn_clnquo R C)) p0060
      p0063
  have p0065 :=
    @g_jca syntaxFormula0007 syntaxFormula0002 (syn_wss (.cv x) (syn_clnquo R C)) p0055
      p0064
  have p0066 :=
    @g_simpl syntaxFormula0006 (.classEq (.cv b) (syn_cec (.cv w) (syn_clnker R)))
  have p0067 := @g_simpr syntaxFormula0005 (.classMem (.cv w) C)
  have p0068 :=
    @g_syl syntaxFormula0007 syntaxFormula0006 (.classMem (.cv w) C) p0066 p0067
  have p0069 :=
    @g_jca syntaxFormula0007 syntaxFormula0008 (.classMem (.cv w) C) p0065 p0068
  have p0070 := @g_lnquounionb w C R (.cv x) dv_cache_0001
  have p0071 :=
    @g_syl syntaxFormula0007 (syn_wa syntaxFormula0008 (.classMem (.cv w) C))
      (syn_wb (.classMem (.cv w) (syn_cuni (.cv x)))
        (.classMem (syn_cec (.cv w) (syn_clnker R)) (.cv x)))
      p0069 p0070
  have p0072 :=
    @g_mpbird syntaxFormula0007 (.classMem (.cv w) (syn_cuni (.cv x)))
      (.classMem (syn_cec (.cv w) (syn_clnker R)) (.cv x)) p0046 p0071
  have p0073 :=
    @g_ex syntaxFormula0006 (.classEq (.cv b) (syn_cec (.cv w) (syn_clnker R)))
      (.classMem (.cv w) (syn_cuni (.cv x))) p0072
  have p0074 :=
    @g_reximdva syntaxFormula0005 (.classEq (.cv b) (syn_cec (.cv w) (syn_clnker R)))
      (.classMem (.cv w) (syn_cuni (.cv x))) w C dv_cache_0009 p0073
  have p0075 :=
    @g_mpd syntaxFormula0005
      (syn_wrex w C (.classEq (.cv b) (syn_cec (.cv w) (syn_clnker R))))
      (syn_wrex w C (.classMem (.cv w) (syn_cuni (.cv x)))) p0039 p0074
  have p0076 :=
    @g_exlimddv syntaxFormula0004 (.classMem (.cv b) (.cv x))
      (syn_wrex w C (.classMem (.cv w) (syn_cuni (.cv x)))) b dv_cache_0010 dv_cache_0011
      p0028 p0075
  have p0077_e01_recanon :
    Nominal.NPrf
      (.imp (.objEq w u) (syn_wb (.classMem (.cv w) (syn_cuni (.cv x)))
          (.classMem (.cv u) (syn_cuni (.cv x))))) :=
    Nominal.RecanonTransportDev.transport
      (by
        simp only [syn_wb, syn_cuni, syn_wex, syn_wa]
        simp (config :=
          { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_class_cv]
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
        · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0018
  have p0077_e02_recanon :
    Nominal.NPrf
      (.imp (.objEq w t) (syn_wb (.classMem (.cv w) (syn_cuni (.cv x)))
          (.classMem (.cv t) (syn_cuni (.cv x))))) :=
    Nominal.RecanonTransportDev.transport
      (by
        simp only [syn_wb, syn_cuni, syn_wex, syn_wa]
        simp (config :=
          { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_class_cv]
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
        · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0019
  have p0077 :=
    @g_frds syntaxFormula0004 (.classMem (.cv w) (syn_cuni (.cv x)))
      (.classMem (.cv u) (syn_cuni (.cv x))) (.classMem (.cv t) (syn_cuni (.cv x))) w u t
      C (syn_cdif R (syn_ccnv R)) dv_cache_0005 dv_cache_0012 dv_cache_0013 dv_cache_0014
      dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020
      dv_cache_0021 dv_cache_0022 p0017 p0077_e01_recanon p0077_e02_recanon p0022 p0076
  have p0078 := @g_simpr syntaxFormula0004 syntaxFormula0013
  have p0079 := @g_simpr (.classMem (.cv u) C) syntaxFormula0012
  have p0080 := @g_syl syntaxFormula0014 syntaxFormula0013 syntaxFormula0012 p0078 p0079
  have p0081 := @g_simpl (.classMem (.cv u) (syn_cuni (.cv x))) syntaxFormula0011
  have p0082 :=
    @g_syl syntaxFormula0014 syntaxFormula0012 (.classMem (.cv u) (syn_cuni (.cv x)))
      p0080 p0081
  have p0083 := @g_simpl syntaxFormula0004 syntaxFormula0013
  have p0084 :=
    @g_simpl syntaxFormula0003
      (syn_wa (syn_wss (.cv x) (syn_clnquo R C)) (syn_wne (.cv x) (syn_c0)))
  have p0085 :=
    @g_simpl syntaxFormula0002 (syn_wbr (syn_cdif R (syn_ccnv R)) (syn_cfound) C)
  have p0086 := @g_syl syntaxFormula0004 syntaxFormula0003 syntaxFormula0002 p0084 p0085
  have p0087 := @g_syl syntaxFormula0014 syntaxFormula0004 syntaxFormula0002 p0083 p0086
  have p0088 := @g_simpl syntaxFormula0004 syntaxFormula0013
  have p0089 :=
    @g_simpr syntaxFormula0003
      (syn_wa (syn_wss (.cv x) (syn_clnquo R C)) (syn_wne (.cv x) (syn_c0)))
  have p0090 := @g_simpl (syn_wss (.cv x) (syn_clnquo R C)) (syn_wne (.cv x) (syn_c0))
  have p0091 :=
    @g_syl syntaxFormula0004
      (syn_wa (syn_wss (.cv x) (syn_clnquo R C)) (syn_wne (.cv x) (syn_c0)))
      (syn_wss (.cv x) (syn_clnquo R C)) p0089 p0090
  have p0092 :=
    @g_syl syntaxFormula0014 syntaxFormula0004 (syn_wss (.cv x) (syn_clnquo R C)) p0088
      p0091
  have p0093 :=
    @g_jca syntaxFormula0014 syntaxFormula0002 (syn_wss (.cv x) (syn_clnquo R C)) p0087
      p0092
  have p0094 := @g_simpr syntaxFormula0004 syntaxFormula0013
  have p0095 := @g_simpl (.classMem (.cv u) C) syntaxFormula0012
  have p0096 :=
    @g_syl syntaxFormula0014 syntaxFormula0013 (.classMem (.cv u) C) p0094 p0095
  have p0097 :=
    @g_jca syntaxFormula0014 syntaxFormula0008 (.classMem (.cv u) C) p0093 p0096
  have p0098 := @g_lnquounionb u C R (.cv x) dv_cache_0001
  have p0099 :=
    @g_syl syntaxFormula0014 (syn_wa syntaxFormula0008 (.classMem (.cv u) C))
      (syn_wb (.classMem (.cv u) (syn_cuni (.cv x)))
        (.classMem (syn_cec (.cv u) (syn_clnker R)) (.cv x)))
      p0097 p0098
  have p0100 :=
    @g_mpbid syntaxFormula0014 (.classMem (.cv u) (syn_cuni (.cv x)))
      (.classMem (syn_cec (.cv u) (syn_clnker R)) (.cv x)) p0082 p0099
  have p0101 := @g_simpl syntaxFormula0014 syntaxFormula0015
  have p0102 := @g_simpl syntaxFormula0004 syntaxFormula0013
  have p0103 := @g_syl syntaxFormula0016 syntaxFormula0014 syntaxFormula0004 p0101 p0102
  have p0104 :=
    @g_simpr syntaxFormula0003
      (syn_wa (syn_wss (.cv x) (syn_clnquo R C)) (syn_wne (.cv x) (syn_c0)))
  have p0105 := @g_simpl (syn_wss (.cv x) (syn_clnquo R C)) (syn_wne (.cv x) (syn_c0))
  have p0106 :=
    @g_syl syntaxFormula0004
      (syn_wa (syn_wss (.cv x) (syn_clnquo R C)) (syn_wne (.cv x) (syn_c0)))
      (syn_wss (.cv x) (syn_clnquo R C)) p0104 p0105
  have p0107 :=
    @g_syl syntaxFormula0016 syntaxFormula0004 (syn_wss (.cv x) (syn_clnquo R C)) p0103
      p0106
  have p0108 := @g_simpr syntaxFormula0014 syntaxFormula0015
  have p0109 :=
    @g_simpl (.classMem (.cv y) (.cv x))
      (syn_wbr (.cv y) (syn_clnqord R C) (syn_cec (.cv u) (syn_clnker R)))
  have p0110 :=
    @g_syl syntaxFormula0016 syntaxFormula0015 (.classMem (.cv y) (.cv x)) p0108 p0109
  have p0111 := @g_sseldd syntaxFormula0016 (.cv x) (syn_clnquo R C) (.cv y) p0107 p0110
  have p0112 := @g_vex y
  have p0113 :=
    @g_ellnquo v C (.cv y) R dv_cache_0023 dv_cache_0001 dv_cache_0024 dv_cache_0025
      dv_cache_0026 dv_cache_0027 p0112
  have p0114 :=
    @g_a1i
      (syn_wb (.classMem (.cv y) (syn_clnquo R C))
        (syn_wrex v C (.classEq (.cv y) (syn_cec (.cv v) (syn_clnker R)))))
      syntaxFormula0016 p0113
  have p0115 :=
    @g_mpbid syntaxFormula0016 (.classMem (.cv y) (syn_clnquo R C))
      (syn_wrex v C (.classEq (.cv y) (syn_cec (.cv v) (syn_clnker R)))) p0111 p0114
  have p0116 := @g_simpl syntaxFormula0018 (syn_wbr (.cv u) R (.cv v))
  have p0117 := @g_simpr syntaxFormula0016 syntaxFormula0017
  have p0118 :=
    @g_simpr (.classMem (.cv v) C) (.classEq (.cv y) (syn_cec (.cv v) (syn_clnker R)))
  have p0119 :=
    @g_syl syntaxFormula0018 syntaxFormula0017
      (.classEq (.cv y) (syn_cec (.cv v) (syn_clnker R))) p0117 p0118
  have p0120 :=
    @g_syl syntaxFormula0019 syntaxFormula0018
      (.classEq (.cv y) (syn_cec (.cv v) (syn_clnker R))) p0116 p0119
  have p0121 := @g_simpl syntaxFormula0018 (syn_wbr (.cv u) R (.cv v))
  have p0122 := @g_simpr syntaxFormula0016 syntaxFormula0017
  have p0123 :=
    @g_simpr (.classMem (.cv v) C) (.classEq (.cv y) (syn_cec (.cv v) (syn_clnker R)))
  have p0124 :=
    @g_syl syntaxFormula0018 syntaxFormula0017
      (.classEq (.cv y) (syn_cec (.cv v) (syn_clnker R))) p0122 p0123
  have p0125 := @g_simpl syntaxFormula0016 syntaxFormula0017
  have p0126 := @g_simpr syntaxFormula0014 syntaxFormula0015
  have p0127 :=
    @g_simpr (.classMem (.cv y) (.cv x))
      (syn_wbr (.cv y) (syn_clnqord R C) (syn_cec (.cv u) (syn_clnker R)))
  have p0128 :=
    @g_syl syntaxFormula0016 syntaxFormula0015
      (syn_wbr (.cv y) (syn_clnqord R C) (syn_cec (.cv u) (syn_clnker R))) p0126 p0127
  have p0129 :=
    @g_syl syntaxFormula0018 syntaxFormula0016
      (syn_wbr (.cv y) (syn_clnqord R C) (syn_cec (.cv u) (syn_clnker R))) p0125 p0128
  have p0130 :=
    @g_eqbrtrrd syntaxFormula0018 (.cv y) (syn_cec (.cv v) (syn_clnker R))
      (syn_cec (.cv u) (syn_clnker R)) (syn_clnqord R C) p0124 p0129
  have p0131 := @g_simpl syntaxFormula0016 syntaxFormula0017
  have p0132 := @g_simpl syntaxFormula0014 syntaxFormula0015
  have p0133 := @g_simpl syntaxFormula0004 syntaxFormula0013
  have p0134 := @g_syl syntaxFormula0016 syntaxFormula0014 syntaxFormula0004 p0132 p0133
  have p0135 := @g_syl syntaxFormula0018 syntaxFormula0016 syntaxFormula0004 p0131 p0134
  have p0136 :=
    @g_simpl syntaxFormula0003
      (syn_wa (syn_wss (.cv x) (syn_clnquo R C)) (syn_wne (.cv x) (syn_c0)))
  have p0137 :=
    @g_simpl syntaxFormula0002 (syn_wbr (syn_cdif R (syn_ccnv R)) (syn_cfound) C)
  have p0138 := @g_syl syntaxFormula0004 syntaxFormula0003 syntaxFormula0002 p0136 p0137
  have p0139 :=
    @g_simpl (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) syntaxFormula0001
  have p0140 :=
    @g_syl syntaxFormula0004 syntaxFormula0002
      (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) p0138 p0139
  have p0141 := @g_simpl (.classMem R (syn_cvv)) (.classMem C (syn_cvv))
  have p0142 :=
    @g_syl syntaxFormula0004 (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv)))
      (.classMem R (syn_cvv)) p0140 p0141
  have p0143 :=
    @g_syl syntaxFormula0018 syntaxFormula0004 (.classMem R (syn_cvv)) p0135 p0142
  have p0144 := @g_simpl syntaxFormula0016 syntaxFormula0017
  have p0145 := @g_simpl syntaxFormula0014 syntaxFormula0015
  have p0146 := @g_simpl syntaxFormula0004 syntaxFormula0013
  have p0147 := @g_syl syntaxFormula0016 syntaxFormula0014 syntaxFormula0004 p0145 p0146
  have p0148 := @g_syl syntaxFormula0018 syntaxFormula0016 syntaxFormula0004 p0144 p0147
  have p0149 :=
    @g_simpl syntaxFormula0003
      (syn_wa (syn_wss (.cv x) (syn_clnquo R C)) (syn_wne (.cv x) (syn_c0)))
  have p0150 :=
    @g_simpl syntaxFormula0002 (syn_wbr (syn_cdif R (syn_ccnv R)) (syn_cfound) C)
  have p0151 := @g_syl syntaxFormula0004 syntaxFormula0003 syntaxFormula0002 p0149 p0150
  have p0152 :=
    @g_simpr (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) syntaxFormula0001
  have p0153 := @g_syl syntaxFormula0004 syntaxFormula0002 syntaxFormula0001 p0151 p0152
  have p0154 := @g_simpl syntaxFormula0000 (syn_wss R (syn_cxp C C))
  have p0155 := @g_syl syntaxFormula0004 syntaxFormula0001 syntaxFormula0000 p0153 p0154
  have p0156 :=
    @g_simpl (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
      (syn_wbr R (syn_cconnex) C)
  have p0157 :=
    @g_syl syntaxFormula0004 syntaxFormula0000
      (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) p0155 p0156
  have p0158 :=
    @g_syl syntaxFormula0018 syntaxFormula0004
      (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) p0148 p0157
  have p0159 := @g_simpl syntaxFormula0016 syntaxFormula0017
  have p0160 := @g_simpl syntaxFormula0014 syntaxFormula0015
  have p0161 := @g_simpl syntaxFormula0004 syntaxFormula0013
  have p0162 := @g_syl syntaxFormula0016 syntaxFormula0014 syntaxFormula0004 p0160 p0161
  have p0163 := @g_syl syntaxFormula0018 syntaxFormula0016 syntaxFormula0004 p0159 p0162
  have p0164 :=
    @g_simpl syntaxFormula0003
      (syn_wa (syn_wss (.cv x) (syn_clnquo R C)) (syn_wne (.cv x) (syn_c0)))
  have p0165 :=
    @g_simpl syntaxFormula0002 (syn_wbr (syn_cdif R (syn_ccnv R)) (syn_cfound) C)
  have p0166 := @g_syl syntaxFormula0004 syntaxFormula0003 syntaxFormula0002 p0164 p0165
  have p0167 :=
    @g_simpr (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) syntaxFormula0001
  have p0168 := @g_syl syntaxFormula0004 syntaxFormula0002 syntaxFormula0001 p0166 p0167
  have p0169 := @g_simpr syntaxFormula0000 (syn_wss R (syn_cxp C C))
  have p0170 :=
    @g_syl syntaxFormula0004 syntaxFormula0001 (syn_wss R (syn_cxp C C)) p0168 p0169
  have p0171 :=
    @g_syl syntaxFormula0018 syntaxFormula0004 (syn_wss R (syn_cxp C C)) p0163 p0170
  have p0172 :=
    @g_jca syntaxFormula0018 (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
      (syn_wss R (syn_cxp C C)) p0158 p0171
  have p0173 := @g_simpr syntaxFormula0016 syntaxFormula0017
  have p0174 :=
    @g_simpl (.classMem (.cv v) C) (.classEq (.cv y) (syn_cec (.cv v) (syn_clnker R)))
  have p0175 :=
    @g_syl syntaxFormula0018 syntaxFormula0017 (.classMem (.cv v) C) p0173 p0174
  have p0176 := @g_simpl syntaxFormula0016 syntaxFormula0017
  have p0177 := @g_simpl syntaxFormula0014 syntaxFormula0015
  have p0178 := @g_syl syntaxFormula0018 syntaxFormula0016 syntaxFormula0014 p0176 p0177
  have p0179 := @g_simpr syntaxFormula0004 syntaxFormula0013
  have p0180 := @g_simpl (.classMem (.cv u) C) syntaxFormula0012
  have p0181 :=
    @g_syl syntaxFormula0014 syntaxFormula0013 (.classMem (.cv u) C) p0179 p0180
  have p0182 :=
    @g_syl syntaxFormula0018 syntaxFormula0014 (.classMem (.cv u) C) p0178 p0181
  have p0183 :=
    @g_jca syntaxFormula0018 (.classMem (.cv v) C) (.classMem (.cv u) C) p0175 p0182
  have p0184 :=
    @g_jca syntaxFormula0018 syntaxFormula0020
      (syn_wa (.classMem (.cv v) C) (.classMem (.cv u) C)) p0172 p0183
  have p0185 :=
    @g_jca syntaxFormula0018 (.classMem R (syn_cvv)) syntaxFormula0021 p0143 p0184
  have p0186 := @g_brlnqordkern C R (.cv v) (.cv u) dv_cache_0001
  have p0187 :=
    @g_syl syntaxFormula0018 syntaxFormula0022
      (syn_wb syntaxFormula0023 (syn_wbr (.cv v) R (.cv u))) p0185 p0186
  have p0188 :=
    @g_mpbid syntaxFormula0018 syntaxFormula0023 (syn_wbr (.cv v) R (.cv u)) p0130 p0187
  have p0189 :=
    @g_syl syntaxFormula0019 syntaxFormula0018 (syn_wbr (.cv v) R (.cv u)) p0121 p0188
  have p0190 := @g_simpr syntaxFormula0018 (syn_wbr (.cv u) R (.cv v))
  have p0191 :=
    @g_jca syntaxFormula0019 (syn_wbr (.cv v) R (.cv u)) (syn_wbr (.cv u) R (.cv v)) p0189
      p0190
  have p0192 := @g_simpl syntaxFormula0018 (syn_wbr (.cv u) R (.cv v))
  have p0193 := @g_simpl syntaxFormula0016 syntaxFormula0017
  have p0194 := @g_simpl syntaxFormula0014 syntaxFormula0015
  have p0195 := @g_simpl syntaxFormula0004 syntaxFormula0013
  have p0196 := @g_syl syntaxFormula0016 syntaxFormula0014 syntaxFormula0004 p0194 p0195
  have p0197 := @g_syl syntaxFormula0018 syntaxFormula0016 syntaxFormula0004 p0193 p0196
  have p0198 := @g_syl syntaxFormula0019 syntaxFormula0018 syntaxFormula0004 p0192 p0197
  have p0199 :=
    @g_simpl syntaxFormula0003
      (syn_wa (syn_wss (.cv x) (syn_clnquo R C)) (syn_wne (.cv x) (syn_c0)))
  have p0200 :=
    @g_simpl syntaxFormula0002 (syn_wbr (syn_cdif R (syn_ccnv R)) (syn_cfound) C)
  have p0201 := @g_syl syntaxFormula0004 syntaxFormula0003 syntaxFormula0002 p0199 p0200
  have p0202 := @g_syl syntaxFormula0019 syntaxFormula0004 syntaxFormula0002 p0198 p0201
  have p0203 := @g_simpl syntaxFormula0018 (syn_wbr (.cv u) R (.cv v))
  have p0204 := @g_simpr syntaxFormula0016 syntaxFormula0017
  have p0205 :=
    @g_simpl (.classMem (.cv v) C) (.classEq (.cv y) (syn_cec (.cv v) (syn_clnker R)))
  have p0206 :=
    @g_syl syntaxFormula0018 syntaxFormula0017 (.classMem (.cv v) C) p0204 p0205
  have p0207 :=
    @g_syl syntaxFormula0019 syntaxFormula0018 (.classMem (.cv v) C) p0203 p0206
  have p0208 := @g_simpl syntaxFormula0018 (syn_wbr (.cv u) R (.cv v))
  have p0209 := @g_simpl syntaxFormula0016 syntaxFormula0017
  have p0210 := @g_simpl syntaxFormula0014 syntaxFormula0015
  have p0211 := @g_syl syntaxFormula0018 syntaxFormula0016 syntaxFormula0014 p0209 p0210
  have p0212 := @g_simpr syntaxFormula0004 syntaxFormula0013
  have p0213 := @g_simpl (.classMem (.cv u) C) syntaxFormula0012
  have p0214 :=
    @g_syl syntaxFormula0014 syntaxFormula0013 (.classMem (.cv u) C) p0212 p0213
  have p0215 :=
    @g_syl syntaxFormula0018 syntaxFormula0014 (.classMem (.cv u) C) p0211 p0214
  have p0216 :=
    @g_syl syntaxFormula0019 syntaxFormula0018 (.classMem (.cv u) C) p0208 p0215
  have p0217 :=
    @g_jca syntaxFormula0019 (.classMem (.cv v) C) (.classMem (.cv u) C) p0207 p0216
  have p0218 :=
    @g_jca syntaxFormula0019 syntaxFormula0002
      (syn_wa (.classMem (.cv v) C) (.classMem (.cv u) C)) p0202 p0217
  have p0219 := @g_lnkereceqb C R (.cv v) (.cv u) dv_cache_0001
  have p0220 :=
    @g_syl syntaxFormula0019
      (syn_wa syntaxFormula0002 (syn_wa (.classMem (.cv v) C) (.classMem (.cv u) C)))
      (syn_wb (.classEq (syn_cec (.cv v) (syn_clnker R)) (syn_cec (.cv u) (syn_clnker R)))
        (syn_wa (syn_wbr (.cv v) R (.cv u)) (syn_wbr (.cv u) R (.cv v))))
      p0218 p0219
  have p0221 :=
    @g_mpbird syntaxFormula0019
      (.classEq (syn_cec (.cv v) (syn_clnker R)) (syn_cec (.cv u) (syn_clnker R)))
      (syn_wa (syn_wbr (.cv v) R (.cv u)) (syn_wbr (.cv u) R (.cv v))) p0191 p0220
  have p0222 :=
    @g_eqtrd syntaxFormula0019 (.cv y) (syn_cec (.cv v) (syn_clnker R))
      (syn_cec (.cv u) (syn_clnker R)) p0120 p0221
  have p0223 :=
    @g_ex syntaxFormula0018 (syn_wbr (.cv u) R (.cv v))
      (.classEq (.cv y) (syn_cec (.cv u) (syn_clnker R))) p0222
  have p0224 := @g_simpl syntaxFormula0018 (.neg (syn_wbr (.cv u) R (.cv v)))
  have p0225 := @g_simpr syntaxFormula0016 syntaxFormula0017
  have p0226 :=
    @g_simpr (.classMem (.cv v) C) (.classEq (.cv y) (syn_cec (.cv v) (syn_clnker R)))
  have p0227 :=
    @g_syl syntaxFormula0018 syntaxFormula0017
      (.classEq (.cv y) (syn_cec (.cv v) (syn_clnker R))) p0225 p0226
  have p0228 :=
    @g_syl syntaxFormula0024 syntaxFormula0018
      (.classEq (.cv y) (syn_cec (.cv v) (syn_clnker R))) p0224 p0227
  have p0229 := @g_simpl syntaxFormula0018 (.neg (syn_wbr (.cv u) R (.cv v)))
  have p0230 := @g_simpr syntaxFormula0016 syntaxFormula0017
  have p0231 :=
    @g_simpr (.classMem (.cv v) C) (.classEq (.cv y) (syn_cec (.cv v) (syn_clnker R)))
  have p0232 :=
    @g_syl syntaxFormula0018 syntaxFormula0017
      (.classEq (.cv y) (syn_cec (.cv v) (syn_clnker R))) p0230 p0231
  have p0233 :=
    @g_syl syntaxFormula0024 syntaxFormula0018
      (.classEq (.cv y) (syn_cec (.cv v) (syn_clnker R))) p0229 p0232
  have p0234 := @g_simpl syntaxFormula0018 (.neg (syn_wbr (.cv u) R (.cv v)))
  have p0235 := @g_simpl syntaxFormula0016 syntaxFormula0017
  have p0236 := @g_simpr syntaxFormula0014 syntaxFormula0015
  have p0237 :=
    @g_simpl (.classMem (.cv y) (.cv x))
      (syn_wbr (.cv y) (syn_clnqord R C) (syn_cec (.cv u) (syn_clnker R)))
  have p0238 :=
    @g_syl syntaxFormula0016 syntaxFormula0015 (.classMem (.cv y) (.cv x)) p0236 p0237
  have p0239 :=
    @g_syl syntaxFormula0018 syntaxFormula0016 (.classMem (.cv y) (.cv x)) p0235 p0238
  have p0240 :=
    @g_syl syntaxFormula0024 syntaxFormula0018 (.classMem (.cv y) (.cv x)) p0234 p0239
  have p0241 :=
    @g_eqeltrrd syntaxFormula0024 (.cv y) (syn_cec (.cv v) (syn_clnker R)) (.cv x) p0233
      p0240
  have p0242 := @g_simpl syntaxFormula0018 (.neg (syn_wbr (.cv u) R (.cv v)))
  have p0243 := @g_simpl syntaxFormula0016 syntaxFormula0017
  have p0244 := @g_simpl syntaxFormula0014 syntaxFormula0015
  have p0245 := @g_simpl syntaxFormula0004 syntaxFormula0013
  have p0246 := @g_syl syntaxFormula0016 syntaxFormula0014 syntaxFormula0004 p0244 p0245
  have p0247 := @g_syl syntaxFormula0018 syntaxFormula0016 syntaxFormula0004 p0243 p0246
  have p0248 := @g_syl syntaxFormula0024 syntaxFormula0018 syntaxFormula0004 p0242 p0247
  have p0249 :=
    @g_simpl syntaxFormula0003
      (syn_wa (syn_wss (.cv x) (syn_clnquo R C)) (syn_wne (.cv x) (syn_c0)))
  have p0250 :=
    @g_simpl syntaxFormula0002 (syn_wbr (syn_cdif R (syn_ccnv R)) (syn_cfound) C)
  have p0251 := @g_syl syntaxFormula0004 syntaxFormula0003 syntaxFormula0002 p0249 p0250
  have p0252 := @g_syl syntaxFormula0024 syntaxFormula0004 syntaxFormula0002 p0248 p0251
  have p0253 := @g_simpl syntaxFormula0018 (.neg (syn_wbr (.cv u) R (.cv v)))
  have p0254 := @g_simpl syntaxFormula0016 syntaxFormula0017
  have p0255 := @g_simpl syntaxFormula0014 syntaxFormula0015
  have p0256 := @g_simpl syntaxFormula0004 syntaxFormula0013
  have p0257 := @g_syl syntaxFormula0016 syntaxFormula0014 syntaxFormula0004 p0255 p0256
  have p0258 := @g_syl syntaxFormula0018 syntaxFormula0016 syntaxFormula0004 p0254 p0257
  have p0259 := @g_syl syntaxFormula0024 syntaxFormula0018 syntaxFormula0004 p0253 p0258
  have p0260 :=
    @g_simpr syntaxFormula0003
      (syn_wa (syn_wss (.cv x) (syn_clnquo R C)) (syn_wne (.cv x) (syn_c0)))
  have p0261 := @g_simpl (syn_wss (.cv x) (syn_clnquo R C)) (syn_wne (.cv x) (syn_c0))
  have p0262 :=
    @g_syl syntaxFormula0004
      (syn_wa (syn_wss (.cv x) (syn_clnquo R C)) (syn_wne (.cv x) (syn_c0)))
      (syn_wss (.cv x) (syn_clnquo R C)) p0260 p0261
  have p0263 :=
    @g_syl syntaxFormula0024 syntaxFormula0004 (syn_wss (.cv x) (syn_clnquo R C)) p0259
      p0262
  have p0264 :=
    @g_jca syntaxFormula0024 syntaxFormula0002 (syn_wss (.cv x) (syn_clnquo R C)) p0252
      p0263
  have p0265 := @g_simpl syntaxFormula0018 (.neg (syn_wbr (.cv u) R (.cv v)))
  have p0266 := @g_simpr syntaxFormula0016 syntaxFormula0017
  have p0267 :=
    @g_simpl (.classMem (.cv v) C) (.classEq (.cv y) (syn_cec (.cv v) (syn_clnker R)))
  have p0268 :=
    @g_syl syntaxFormula0018 syntaxFormula0017 (.classMem (.cv v) C) p0266 p0267
  have p0269 :=
    @g_syl syntaxFormula0024 syntaxFormula0018 (.classMem (.cv v) C) p0265 p0268
  have p0270 :=
    @g_jca syntaxFormula0024 syntaxFormula0008 (.classMem (.cv v) C) p0264 p0269
  have p0271 := @g_lnquounionb v C R (.cv x) dv_cache_0001
  have p0272 :=
    @g_syl syntaxFormula0024 (syn_wa syntaxFormula0008 (.classMem (.cv v) C))
      (syn_wb (.classMem (.cv v) (syn_cuni (.cv x)))
        (.classMem (syn_cec (.cv v) (syn_clnker R)) (.cv x)))
      p0270 p0271
  have p0273 :=
    @g_mpbird syntaxFormula0024 (.classMem (.cv v) (syn_cuni (.cv x)))
      (.classMem (syn_cec (.cv v) (syn_clnker R)) (.cv x)) p0241 p0272
  have p0274 := @g_simpl syntaxFormula0018 (.neg (syn_wbr (.cv u) R (.cv v)))
  have p0275 := @g_simpr syntaxFormula0016 syntaxFormula0017
  have p0276 :=
    @g_simpr (.classMem (.cv v) C) (.classEq (.cv y) (syn_cec (.cv v) (syn_clnker R)))
  have p0277 :=
    @g_syl syntaxFormula0018 syntaxFormula0017
      (.classEq (.cv y) (syn_cec (.cv v) (syn_clnker R))) p0275 p0276
  have p0278 := @g_simpl syntaxFormula0016 syntaxFormula0017
  have p0279 := @g_simpr syntaxFormula0014 syntaxFormula0015
  have p0280 :=
    @g_simpr (.classMem (.cv y) (.cv x))
      (syn_wbr (.cv y) (syn_clnqord R C) (syn_cec (.cv u) (syn_clnker R)))
  have p0281 :=
    @g_syl syntaxFormula0016 syntaxFormula0015
      (syn_wbr (.cv y) (syn_clnqord R C) (syn_cec (.cv u) (syn_clnker R))) p0279 p0280
  have p0282 :=
    @g_syl syntaxFormula0018 syntaxFormula0016
      (syn_wbr (.cv y) (syn_clnqord R C) (syn_cec (.cv u) (syn_clnker R))) p0278 p0281
  have p0283 :=
    @g_eqbrtrrd syntaxFormula0018 (.cv y) (syn_cec (.cv v) (syn_clnker R))
      (syn_cec (.cv u) (syn_clnker R)) (syn_clnqord R C) p0277 p0282
  have p0284 := @g_simpl syntaxFormula0016 syntaxFormula0017
  have p0285 := @g_simpl syntaxFormula0014 syntaxFormula0015
  have p0286 := @g_simpl syntaxFormula0004 syntaxFormula0013
  have p0287 := @g_syl syntaxFormula0016 syntaxFormula0014 syntaxFormula0004 p0285 p0286
  have p0288 := @g_syl syntaxFormula0018 syntaxFormula0016 syntaxFormula0004 p0284 p0287
  have p0289 :=
    @g_simpl syntaxFormula0003
      (syn_wa (syn_wss (.cv x) (syn_clnquo R C)) (syn_wne (.cv x) (syn_c0)))
  have p0290 :=
    @g_simpl syntaxFormula0002 (syn_wbr (syn_cdif R (syn_ccnv R)) (syn_cfound) C)
  have p0291 := @g_syl syntaxFormula0004 syntaxFormula0003 syntaxFormula0002 p0289 p0290
  have p0292 :=
    @g_simpl (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) syntaxFormula0001
  have p0293 :=
    @g_syl syntaxFormula0004 syntaxFormula0002
      (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) p0291 p0292
  have p0294 := @g_simpl (.classMem R (syn_cvv)) (.classMem C (syn_cvv))
  have p0295 :=
    @g_syl syntaxFormula0004 (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv)))
      (.classMem R (syn_cvv)) p0293 p0294
  have p0296 :=
    @g_syl syntaxFormula0018 syntaxFormula0004 (.classMem R (syn_cvv)) p0288 p0295
  have p0297 := @g_simpl syntaxFormula0016 syntaxFormula0017
  have p0298 := @g_simpl syntaxFormula0014 syntaxFormula0015
  have p0299 := @g_simpl syntaxFormula0004 syntaxFormula0013
  have p0300 := @g_syl syntaxFormula0016 syntaxFormula0014 syntaxFormula0004 p0298 p0299
  have p0301 := @g_syl syntaxFormula0018 syntaxFormula0016 syntaxFormula0004 p0297 p0300
  have p0302 :=
    @g_simpl syntaxFormula0003
      (syn_wa (syn_wss (.cv x) (syn_clnquo R C)) (syn_wne (.cv x) (syn_c0)))
  have p0303 :=
    @g_simpl syntaxFormula0002 (syn_wbr (syn_cdif R (syn_ccnv R)) (syn_cfound) C)
  have p0304 := @g_syl syntaxFormula0004 syntaxFormula0003 syntaxFormula0002 p0302 p0303
  have p0305 :=
    @g_simpr (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) syntaxFormula0001
  have p0306 := @g_syl syntaxFormula0004 syntaxFormula0002 syntaxFormula0001 p0304 p0305
  have p0307 := @g_simpl syntaxFormula0000 (syn_wss R (syn_cxp C C))
  have p0308 := @g_syl syntaxFormula0004 syntaxFormula0001 syntaxFormula0000 p0306 p0307
  have p0309 :=
    @g_simpl (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
      (syn_wbr R (syn_cconnex) C)
  have p0310 :=
    @g_syl syntaxFormula0004 syntaxFormula0000
      (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) p0308 p0309
  have p0311 :=
    @g_syl syntaxFormula0018 syntaxFormula0004
      (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C)) p0301 p0310
  have p0312 := @g_simpl syntaxFormula0016 syntaxFormula0017
  have p0313 := @g_simpl syntaxFormula0014 syntaxFormula0015
  have p0314 := @g_simpl syntaxFormula0004 syntaxFormula0013
  have p0315 := @g_syl syntaxFormula0016 syntaxFormula0014 syntaxFormula0004 p0313 p0314
  have p0316 := @g_syl syntaxFormula0018 syntaxFormula0016 syntaxFormula0004 p0312 p0315
  have p0317 :=
    @g_simpl syntaxFormula0003
      (syn_wa (syn_wss (.cv x) (syn_clnquo R C)) (syn_wne (.cv x) (syn_c0)))
  have p0318 :=
    @g_simpl syntaxFormula0002 (syn_wbr (syn_cdif R (syn_ccnv R)) (syn_cfound) C)
  have p0319 := @g_syl syntaxFormula0004 syntaxFormula0003 syntaxFormula0002 p0317 p0318
  have p0320 :=
    @g_simpr (syn_wa (.classMem R (syn_cvv)) (.classMem C (syn_cvv))) syntaxFormula0001
  have p0321 := @g_syl syntaxFormula0004 syntaxFormula0002 syntaxFormula0001 p0319 p0320
  have p0322 := @g_simpr syntaxFormula0000 (syn_wss R (syn_cxp C C))
  have p0323 :=
    @g_syl syntaxFormula0004 syntaxFormula0001 (syn_wss R (syn_cxp C C)) p0321 p0322
  have p0324 :=
    @g_syl syntaxFormula0018 syntaxFormula0004 (syn_wss R (syn_cxp C C)) p0316 p0323
  have p0325 :=
    @g_jca syntaxFormula0018 (syn_wa (syn_wbr R (syn_cref) C) (syn_wbr R (syn_ctrans) C))
      (syn_wss R (syn_cxp C C)) p0311 p0324
  have p0326 := @g_simpr syntaxFormula0016 syntaxFormula0017
  have p0327 :=
    @g_simpl (.classMem (.cv v) C) (.classEq (.cv y) (syn_cec (.cv v) (syn_clnker R)))
  have p0328 :=
    @g_syl syntaxFormula0018 syntaxFormula0017 (.classMem (.cv v) C) p0326 p0327
  have p0329 := @g_simpl syntaxFormula0016 syntaxFormula0017
  have p0330 := @g_simpl syntaxFormula0014 syntaxFormula0015
  have p0331 := @g_syl syntaxFormula0018 syntaxFormula0016 syntaxFormula0014 p0329 p0330
  have p0332 := @g_simpr syntaxFormula0004 syntaxFormula0013
  have p0333 := @g_simpl (.classMem (.cv u) C) syntaxFormula0012
  have p0334 :=
    @g_syl syntaxFormula0014 syntaxFormula0013 (.classMem (.cv u) C) p0332 p0333
  have p0335 :=
    @g_syl syntaxFormula0018 syntaxFormula0014 (.classMem (.cv u) C) p0331 p0334
  have p0336 :=
    @g_jca syntaxFormula0018 (.classMem (.cv v) C) (.classMem (.cv u) C) p0328 p0335
  have p0337 :=
    @g_jca syntaxFormula0018 syntaxFormula0020
      (syn_wa (.classMem (.cv v) C) (.classMem (.cv u) C)) p0325 p0336
  have p0338 :=
    @g_jca syntaxFormula0018 (.classMem R (syn_cvv)) syntaxFormula0021 p0296 p0337
  have p0339 := @g_brlnqordkern C R (.cv v) (.cv u) dv_cache_0001
  have p0340 :=
    @g_syl syntaxFormula0018 syntaxFormula0022
      (syn_wb syntaxFormula0023 (syn_wbr (.cv v) R (.cv u))) p0338 p0339
  have p0341 :=
    @g_mpbid syntaxFormula0018 syntaxFormula0023 (syn_wbr (.cv v) R (.cv u)) p0283 p0340
  have p0342 :=
    @g_syl syntaxFormula0024 syntaxFormula0018 (syn_wbr (.cv v) R (.cv u)) p0274 p0341
  have p0343 := @g_simpr syntaxFormula0018 (.neg (syn_wbr (.cv u) R (.cv v)))
  have p0344 := @g_brcnv (.cv v) (.cv u) R
  have p0345 :=
    @g_a1i (syn_wb (syn_wbr (.cv v) (syn_ccnv R) (.cv u)) (syn_wbr (.cv u) R (.cv v)))
      syntaxFormula0024 p0344
  have p0346 :=
    @g_notbid syntaxFormula0024 (syn_wbr (.cv v) (syn_ccnv R) (.cv u))
      (syn_wbr (.cv u) R (.cv v)) p0345
  have p0347 :=
    @g_mpbird syntaxFormula0024 (.neg (syn_wbr (.cv v) (syn_ccnv R) (.cv u)))
      (.neg (syn_wbr (.cv u) R (.cv v))) p0343 p0346
  have p0348 :=
    @g_jca syntaxFormula0024 (syn_wbr (.cv v) R (.cv u))
      (.neg (syn_wbr (.cv v) (syn_ccnv R) (.cv u))) p0342 p0347
  have p0349 := @g_brdif (.cv v) (.cv u) R (syn_ccnv R)
  have p0350 :=
    @g_a1i
      (syn_wb (syn_wbr (.cv v) (syn_cdif R (syn_ccnv R)) (.cv u))
        (syn_wa (syn_wbr (.cv v) R (.cv u)) (.neg (syn_wbr (.cv v) (syn_ccnv R) (.cv u)))))
      syntaxFormula0024 p0349
  have p0351 :=
    @g_mpbird syntaxFormula0024 (syn_wbr (.cv v) (syn_cdif R (syn_ccnv R)) (.cv u))
      (syn_wa (syn_wbr (.cv v) R (.cv u)) (.neg (syn_wbr (.cv v) (syn_ccnv R) (.cv u))))
      p0348 p0350
  have p0352 :=
    @g_jca syntaxFormula0024 (.classMem (.cv v) (syn_cuni (.cv x)))
      (syn_wbr (.cv v) (syn_cdif R (syn_ccnv R)) (.cv u)) p0273 p0351
  have p0353 := @g_simpl syntaxFormula0018 (.neg (syn_wbr (.cv u) R (.cv v)))
  have p0354 := @g_simpl syntaxFormula0016 syntaxFormula0017
  have p0355 := @g_simpl syntaxFormula0014 syntaxFormula0015
  have p0356 := @g_syl syntaxFormula0018 syntaxFormula0016 syntaxFormula0014 p0354 p0355
  have p0357 := @g_simpr syntaxFormula0004 syntaxFormula0013
  have p0358 := @g_simpr (.classMem (.cv u) C) syntaxFormula0012
  have p0359 := @g_syl syntaxFormula0014 syntaxFormula0013 syntaxFormula0012 p0357 p0358
  have p0360 := @g_simpr (.classMem (.cv u) (syn_cuni (.cv x))) syntaxFormula0011
  have p0361 := @g_syl syntaxFormula0014 syntaxFormula0012 syntaxFormula0011 p0359 p0360
  have p0362 := @g_syl syntaxFormula0018 syntaxFormula0014 syntaxFormula0011 p0356 p0361
  have p0363 := @g_syl syntaxFormula0024 syntaxFormula0018 syntaxFormula0011 p0353 p0362
  have p0364 := @g_simpl syntaxFormula0018 (.neg (syn_wbr (.cv u) R (.cv v)))
  have p0365 := @g_simpr syntaxFormula0016 syntaxFormula0017
  have p0366 :=
    @g_simpl (.classMem (.cv v) C) (.classEq (.cv y) (syn_cec (.cv v) (syn_clnker R)))
  have p0367 :=
    @g_syl syntaxFormula0018 syntaxFormula0017 (.classMem (.cv v) C) p0365 p0366
  have p0368 :=
    @g_syl syntaxFormula0024 syntaxFormula0018 (.classMem (.cv v) C) p0364 p0367
  have p0369 := @g_id (.classEq (.cv t) (.cv v))
  have p0370 :=
    @g_eleq1d (.classEq (.cv t) (.cv v)) (.cv t) (.cv v) (syn_cuni (.cv x)) p0369
  have p0371 := @g_id (.classEq (.cv t) (.cv v))
  have p0372 :=
    @g_breq1d (.classEq (.cv t) (.cv v)) (.cv t) (.cv v) (.cv u) (syn_cdif R (syn_ccnv R))
      p0371
  have p0373 :=
    @g_anbi12d (.classEq (.cv t) (.cv v)) (.classMem (.cv t) (syn_cuni (.cv x)))
      (.classMem (.cv v) (syn_cuni (.cv x)))
      (syn_wbr (.cv t) (syn_cdif R (syn_ccnv R)) (.cv u))
      (syn_wbr (.cv v) (syn_cdif R (syn_ccnv R)) (.cv u)) p0370 p0372
  have p0374 := @g_id (.classEq (.cv t) (.cv v))
  have p0375 := @g_eqeq1d (.classEq (.cv t) (.cv v)) (.cv t) (.cv v) (.cv u) p0374
  have p0376 :=
    @g_imbi12d (.classEq (.cv t) (.cv v)) syntaxFormula0009 syntaxFormula0025
      (.classEq (.cv t) (.cv u)) (.classEq (.cv v) (.cv u)) p0373 p0375
  have p0377 :=
    @g_rspcv syntaxFormula0010 syntaxFormula0026 t (.cv v) C dv_cache_0028 dv_cache_0013
      dv_cache_0029 p0376
  have p0378 :=
    @g_syl syntaxFormula0024 (.classMem (.cv v) C)
      (.imp syntaxFormula0011 syntaxFormula0026) p0368 p0377
  have p0379 := @g_mpd syntaxFormula0024 syntaxFormula0011 syntaxFormula0026 p0363 p0378
  have p0380 :=
    @g_mpd syntaxFormula0024 syntaxFormula0025 (.classEq (.cv v) (.cv u)) p0352 p0379
  have p0381 := @g_eceq1 (.cv v) (.cv u) (syn_clnker R)
  have p0382 :=
    @g_syl syntaxFormula0024 (.classEq (.cv v) (.cv u))
      (.classEq (syn_cec (.cv v) (syn_clnker R)) (syn_cec (.cv u) (syn_clnker R))) p0380
      p0381
  have p0383 :=
    @g_eqtrd syntaxFormula0024 (.cv y) (syn_cec (.cv v) (syn_clnker R))
      (syn_cec (.cv u) (syn_clnker R)) p0228 p0382
  have p0384 :=
    @g_ex syntaxFormula0018 (.neg (syn_wbr (.cv u) R (.cv v)))
      (.classEq (.cv y) (syn_cec (.cv u) (syn_clnker R))) p0383
  have p0385 :=
    @g_pm2_61d syntaxFormula0018 (syn_wbr (.cv u) R (.cv v))
      (.classEq (.cv y) (syn_cec (.cv u) (syn_clnker R))) p0223 p0384
  have p0386 :=
    @g_rexlimddv syntaxFormula0016 (.classEq (.cv y) (syn_cec (.cv v) (syn_clnker R)))
      (.classEq (.cv y) (syn_cec (.cv u) (syn_clnker R))) v C dv_cache_0030 dv_cache_0031
      p0115 p0385
  have p0387 :=
    @g_exp32 syntaxFormula0014 (.classMem (.cv y) (.cv x))
      (syn_wbr (.cv y) (syn_clnqord R C) (syn_cec (.cv u) (syn_clnker R)))
      (.classEq (.cv y) (syn_cec (.cv u) (syn_clnker R))) p0386
  have p0388 :=
    @g_ralrimiv syntaxFormula0014 syntaxFormula0027 y (.cv x) dv_cache_0032 p0387
  have p0389 :=
    @g_jca syntaxFormula0014 (.classMem (syn_cec (.cv u) (syn_clnker R)) (.cv x))
      syntaxFormula0028 p0100 p0388
  have p0390 := @g_id (.classEq (.cv z) (syn_cec (.cv u) (syn_clnker R)))
  have p0391 :=
    @g_breq2d (.classEq (.cv z) (syn_cec (.cv u) (syn_clnker R))) (.cv z)
      (syn_cec (.cv u) (syn_clnker R)) (.cv y) (syn_clnqord R C) p0390
  have p0392 := @g_id (.classEq (.cv z) (syn_cec (.cv u) (syn_clnker R)))
  have p0393 :=
    @g_eqeq2d (.classEq (.cv z) (syn_cec (.cv u) (syn_clnker R))) (.cv z)
      (syn_cec (.cv u) (syn_clnker R)) (.cv y) p0392
  have p0394 :=
    @g_imbi12d (.classEq (.cv z) (syn_cec (.cv u) (syn_clnker R)))
      (syn_wbr (.cv y) (syn_clnqord R C) (.cv z))
      (syn_wbr (.cv y) (syn_clnqord R C) (syn_cec (.cv u) (syn_clnker R)))
      (.classEq (.cv y) (.cv z)) (.classEq (.cv y) (syn_cec (.cv u) (syn_clnker R))) p0391
      p0393
  have p0395 :=
    @g_ralbidv (.classEq (.cv z) (syn_cec (.cv u) (syn_clnker R)))
      (.imp (syn_wbr (.cv y) (syn_clnqord R C) (.cv z)) (.classEq (.cv y) (.cv z)))
      syntaxFormula0027 y (.cv x) dv_cache_0033 p0394
  have p0396 :=
    @g_rspcev syntaxFormula0029 syntaxFormula0028 z (syn_cec (.cv u) (syn_clnker R))
      (.cv x) dv_cache_0034 dv_cache_0035 dv_cache_0036 p0395
  have p0397 :=
    @g_syl syntaxFormula0014
      (syn_wa (.classMem (syn_cec (.cv u) (syn_clnker R)) (.cv x)) syntaxFormula0028)
      (syn_wrex z (.cv x) syntaxFormula0029) p0389 p0396
  have p0398_e00_recanon :
    Nominal.NPrf (.imp syntaxFormula0004 (syn_wrex u C syntaxFormula0012)) :=
    Nominal.RecanonTransportDev.transport
      (by
        simp only [syn_wa, syn_wrex, syn_wex]
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · exact Nominal.RecanonTransportDev.TRecanonWff.same _
        · apply Nominal.RecanonTransportDev.TRecanonWff.neg
          apply Nominal.RecanonTransportDev.TRecanonWff.all
          apply Nominal.RecanonTransportDev.TRecanonWff.neg
          apply Nominal.RecanonTransportDev.TRecanonWff.neg
          apply Nominal.RecanonTransportDev.TRecanonWff.imp
          · exact Nominal.RecanonTransportDev.TRecanonWff.same _
          · apply Nominal.RecanonTransportDev.TRecanonWff.neg
            apply Nominal.RecanonTransportDev.TRecanonWff.neg
            apply Nominal.RecanonTransportDev.TRecanonWff.imp
            · exact Nominal.RecanonTransportDev.TRecanonWff.same _
            · apply Nominal.RecanonTransportDev.TRecanonWff.neg
              apply Nominal.RecanonTransportDev.TRecanonWff.all
              apply Nominal.RecanonTransportDev.TRecanonWff.imp
              · exact Nominal.RecanonTransportDev.TRecanonWff.same _
              · apply Nominal.RecanonTransportDev.TRecanonWff.imp
                · exact Nominal.RecanonTransportDev.TRecanonWff.same _
                · exact Nominal.RecanonTransportDev.TRecanonWff.objEq_classEq _ _)
      p0077
  have p0398 :=
    @g_rexlimddv syntaxFormula0004 syntaxFormula0012
      (syn_wrex z (.cv x) syntaxFormula0029) u C dv_cache_0037 dv_cache_0038
      p0398_e00_recanon p0397
  have p0399_e02_recanon :
    Nominal.NPrf
      (.imp syntaxFormula0004 (syn_wrex z (.cv x) (syn_wral y (.cv x)
            (.imp (syn_wbr (.cv y) (syn_clnqord R C) (.cv z)) (.objEq y z))))) :=
    Nominal.RecanonTransportDev.transport
      (by
        simp only [syn_wrex, syn_wex, syn_wral, syn_wa]
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · exact Nominal.RecanonTransportDev.TRecanonWff.same _
        · apply Nominal.RecanonTransportDev.TRecanonWff.neg
          apply Nominal.RecanonTransportDev.TRecanonWff.all
          apply Nominal.RecanonTransportDev.TRecanonWff.neg
          apply Nominal.RecanonTransportDev.TRecanonWff.neg
          apply Nominal.RecanonTransportDev.TRecanonWff.imp
          · exact Nominal.RecanonTransportDev.TRecanonWff.same _
          · apply Nominal.RecanonTransportDev.TRecanonWff.neg
            apply Nominal.RecanonTransportDev.TRecanonWff.all
            apply Nominal.RecanonTransportDev.TRecanonWff.imp
            · exact Nominal.RecanonTransportDev.TRecanonWff.same _
            · apply Nominal.RecanonTransportDev.TRecanonWff.imp
              · exact Nominal.RecanonTransportDev.TRecanonWff.same _
              · exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _)
      p0398
  have p0399 :=
    @g_frrd syntaxFormula0003 x y z (syn_clnquo R C) (syn_clnqord R C) dv_cache_0039
      dv_cache_0040 dv_cache_0041 dv_cache_0042 dv_cache_0043 dv_cache_0044 dv_cache_0045
      dv_cache_0046 dv_cache_0047 dv_cache_0048 p0007 p0012 p0399_e02_recanon
  have p0400 :=
    @g_jca syntaxFormula0003 (syn_wbr (syn_clnqord R C) (syn_cstrict) (syn_clnquo R C))
      (syn_wbr (syn_clnqord R C) (syn_cfound) (syn_clnquo R C)) p0002 p0399
  have p0401 := (Nominal.classEqRefl (syn_cwe))
  have p0402 :=
    @g_breqi (syn_clnqord R C) (syn_clnquo R C) (syn_cwe)
      (syn_cin (syn_cstrict) (syn_cfound)) p0401
  have p0403 := @g_brin (syn_clnqord R C) (syn_clnquo R C) (syn_cstrict) (syn_cfound)
  have p0404 :=
    @g_bitri (syn_wbr (syn_clnqord R C) (syn_cwe) (syn_clnquo R C))
      (syn_wbr (syn_clnqord R C) (syn_cin (syn_cstrict) (syn_cfound)) (syn_clnquo R C))
      syntaxFormula0030 p0402 p0403
  have p0405 :=
    @g_a1i
      (syn_wb (syn_wbr (syn_clnqord R C) (syn_cwe) (syn_clnquo R C)) syntaxFormula0030)
      syntaxFormula0003 p0404
  have p0406 :=
    @g_mpbird syntaxFormula0003 (syn_wbr (syn_clnqord R C) (syn_cwe) (syn_clnquo R C))
      syntaxFormula0030 p0400 p0405
  exact p0406


end NFChoice.DirectNominalPrf.WPPReplay

end

/-! Certificates from `NominalWPPReplayChunk015Compact001Part015`. -/


section

namespace NFChoice.DirectNominalPrf.WPPReplay

open scoped Fol
open NFChoice.Foundation
open NFChoice.SemanticCore
open NFChoice.ReplaySupport
open NFChoice.Compiler.CompactSourceSyntax

@[expose]
noncomputable def g_finleastadjndv (k : Var) (m : Var) (n : Var) (X : Class) (Y : Class)
    (_dv_X_k : k ∉ X.fv) (_dv_X_m : m ∉ X.fv) (dv_X_n : n ∉ X.fv) (_dv_Y_k : k ∉ Y.fv)
    (_dv_Y_m : m ∉ Y.fv) (dv_Y_n : n ∉ Y.fv) (_dv_k_m : k ≠ m) (dv_k_n : k ≠ n)
    (dv_m_n : m ≠ n) :
    Nominal.NPrf
      (.imp (syn_w3a (syn_wa (.classMem (.cv m) (syn_cnnc)) (.classMem (.cv k) (syn_cnnc)))
          (syn_wa (.classMem (.cv m) X) (.classMem (.cv k) Y)) (syn_wa (syn_wa
              (syn_wral n (syn_cnnc) (.imp (.classMem (.cv n) X)
                  (syn_wbr (.cv m) (syn_ckqrel (syn_clefin)) (.cv n)))) (syn_wral n (syn_cnnc)
                (.imp (.classMem (.cv n) Y)
                  (syn_wbr (.cv k) (syn_ckqrel (syn_clefin)) (.cv n))))) (syn_wa
              (syn_wral n (syn_cnnc) (.imp (.classMem (.cv n) X) (.classMem (.cv n) Y)))
              (syn_wral n (syn_cnnc) (.imp (.classMem (.cv n) Y)
                  (.classMem (syn_cplc (.cv n) (syn_c1c)) X))))))
        (syn_wo (.classEq (.cv m) (.cv k)) (.classEq (.cv m) (syn_cplc (.cv k) (syn_c1c))))) :=
  by
  have dv_cache_0001 : n ∉ ((Class.cv k)).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : n ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          (Ne.symm dv_k_n), not_false_eq_true])
  have dv_cache_0002 : n ∉ ((syn_cnnc)).fv :=
    by
    clear dv_cache_0001
    exact
      (by
        have compact_fv_not_mem_empty : n ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc,
          compact_fv_not_mem_empty, not_false_eq_true])
  have dv_cache_0003 :
    n ∉ ((Wff.imp (.classMem (.cv k) Y) (.classMem (syn_cplc (.cv k) (syn_c1c)) X))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact
      (by
        have compact_fv_not_mem_empty : n ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cplc,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c, Finset.mem_union,
          Finset.mem_singleton, (Ne.symm dv_k_n), dv_Y_n, dv_X_n,
          compact_fv_not_mem_empty, or_false, not_false_eq_true])
  have dv_cache_0004 : n ∉ ((syn_cplc (.cv k) (syn_c1c))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact
      (by
        have compact_fv_not_mem_empty : n ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cplc,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c, Finset.mem_union,
          Finset.mem_singleton, (Ne.symm dv_k_n), compact_fv_not_mem_empty, or_false,
          not_false_eq_true])
  have dv_cache_0005 :
    n ∉
      ((Wff.imp (.classMem (syn_cplc (.cv k) (syn_c1c)) X)
          (syn_wbr (.cv m) (syn_ckqrel (syn_clefin)) (syn_cplc (.cv k) (syn_c1c))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact
      (by
        have compact_fv_not_mem_empty : n ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cplc,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_ckqrel,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_clefin, Finset.mem_union,
          Finset.mem_singleton, (Ne.symm dv_k_n), dv_X_n, (Ne.symm dv_m_n),
          compact_fv_not_mem_empty, or_false, not_false_eq_true])
  have dv_cache_0006 : n ∉ ((Class.cv m)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact
      (by
        have compact_fv_not_mem_empty : n ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          (Ne.symm dv_m_n), not_false_eq_true])
  have dv_cache_0007 : n ∉ ((Wff.imp (.classMem (.cv m) X) (.classMem (.cv m) Y))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006
    exact
      (by
        have compact_fv_not_mem_empty : n ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, (Ne.symm dv_m_n), dv_X_n, dv_Y_n, or_false,
          not_false_eq_true])
  have dv_cache_0008 :
    n ∉
      ((Wff.imp (.classMem (.cv m) Y)
          (syn_wbr (.cv k) (syn_ckqrel (syn_clefin)) (.cv m)))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007
    exact
      (by
        have compact_fv_not_mem_empty : n ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_ckqrel,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_clefin, Finset.mem_union,
          Finset.mem_singleton, (Ne.symm dv_m_n), dv_Y_n, (Ne.symm dv_k_n),
          compact_fv_not_mem_empty, or_false, not_false_eq_true])
  have p0000 :=
    @g_simp2 (syn_wa (.classMem (.cv m) (syn_cnnc)) (.classMem (.cv k) (syn_cnnc)))
      (syn_wa (.classMem (.cv m) X) (.classMem (.cv k) Y))
      (syn_wa (syn_wa (syn_wral n (syn_cnnc) (.imp (.classMem (.cv n) X)
              (syn_wbr (.cv m) (syn_ckqrel (syn_clefin)) (.cv n)))) (syn_wral n (syn_cnnc)
            (.imp (.classMem (.cv n) Y) (syn_wbr (.cv k) (syn_ckqrel (syn_clefin)) (.cv n)))))
        (syn_wa (syn_wral n (syn_cnnc) (.imp (.classMem (.cv n) X) (.classMem (.cv n) Y)))
          (syn_wral n (syn_cnnc)
            (.imp (.classMem (.cv n) Y) (.classMem (syn_cplc (.cv n) (syn_c1c)) X)))))
  have p0001 := @g_simpr (.classMem (.cv m) X) (.classMem (.cv k) Y)
  have p0002 :=
    @g_syl
      (syn_w3a (syn_wa (.classMem (.cv m) (syn_cnnc)) (.classMem (.cv k) (syn_cnnc)))
        (syn_wa (.classMem (.cv m) X) (.classMem (.cv k) Y)) (syn_wa (syn_wa
            (syn_wral n (syn_cnnc) (.imp (.classMem (.cv n) X)
                (syn_wbr (.cv m) (syn_ckqrel (syn_clefin)) (.cv n)))) (syn_wral n (syn_cnnc)
              (.imp (.classMem (.cv n) Y) (syn_wbr (.cv k) (syn_ckqrel (syn_clefin)) (.cv n)))))
          (syn_wa (syn_wral n (syn_cnnc) (.imp (.classMem (.cv n) X) (.classMem (.cv n) Y)))
            (syn_wral n (syn_cnnc)
              (.imp (.classMem (.cv n) Y) (.classMem (syn_cplc (.cv n) (syn_c1c)) X))))))
      (syn_wa (.classMem (.cv m) X) (.classMem (.cv k) Y)) (.classMem (.cv k) Y) p0000
      p0001
  have p0003 :=
    @g_simp3 (syn_wa (.classMem (.cv m) (syn_cnnc)) (.classMem (.cv k) (syn_cnnc)))
      (syn_wa (.classMem (.cv m) X) (.classMem (.cv k) Y))
      (syn_wa (syn_wa (syn_wral n (syn_cnnc) (.imp (.classMem (.cv n) X)
              (syn_wbr (.cv m) (syn_ckqrel (syn_clefin)) (.cv n)))) (syn_wral n (syn_cnnc)
            (.imp (.classMem (.cv n) Y) (syn_wbr (.cv k) (syn_ckqrel (syn_clefin)) (.cv n)))))
        (syn_wa (syn_wral n (syn_cnnc) (.imp (.classMem (.cv n) X) (.classMem (.cv n) Y)))
          (syn_wral n (syn_cnnc)
            (.imp (.classMem (.cv n) Y) (.classMem (syn_cplc (.cv n) (syn_c1c)) X)))))
  have p0004 :=
    @g_simpr
      (syn_wa (syn_wral n (syn_cnnc) (.imp (.classMem (.cv n) X)
            (syn_wbr (.cv m) (syn_ckqrel (syn_clefin)) (.cv n)))) (syn_wral n (syn_cnnc)
          (.imp (.classMem (.cv n) Y) (syn_wbr (.cv k) (syn_ckqrel (syn_clefin)) (.cv n)))))
      (syn_wa (syn_wral n (syn_cnnc) (.imp (.classMem (.cv n) X) (.classMem (.cv n) Y)))
        (syn_wral n (syn_cnnc)
          (.imp (.classMem (.cv n) Y) (.classMem (syn_cplc (.cv n) (syn_c1c)) X))))
  have p0005 :=
    @g_syl
      (syn_w3a (syn_wa (.classMem (.cv m) (syn_cnnc)) (.classMem (.cv k) (syn_cnnc)))
        (syn_wa (.classMem (.cv m) X) (.classMem (.cv k) Y)) (syn_wa (syn_wa
            (syn_wral n (syn_cnnc) (.imp (.classMem (.cv n) X)
                (syn_wbr (.cv m) (syn_ckqrel (syn_clefin)) (.cv n)))) (syn_wral n (syn_cnnc)
              (.imp (.classMem (.cv n) Y) (syn_wbr (.cv k) (syn_ckqrel (syn_clefin)) (.cv n)))))
          (syn_wa (syn_wral n (syn_cnnc) (.imp (.classMem (.cv n) X) (.classMem (.cv n) Y)))
            (syn_wral n (syn_cnnc)
              (.imp (.classMem (.cv n) Y) (.classMem (syn_cplc (.cv n) (syn_c1c)) X))))))
      (syn_wa (syn_wa (syn_wral n (syn_cnnc) (.imp (.classMem (.cv n) X)
              (syn_wbr (.cv m) (syn_ckqrel (syn_clefin)) (.cv n)))) (syn_wral n (syn_cnnc)
            (.imp (.classMem (.cv n) Y) (syn_wbr (.cv k) (syn_ckqrel (syn_clefin)) (.cv n)))))
        (syn_wa (syn_wral n (syn_cnnc) (.imp (.classMem (.cv n) X) (.classMem (.cv n) Y)))
          (syn_wral n (syn_cnnc)
            (.imp (.classMem (.cv n) Y) (.classMem (syn_cplc (.cv n) (syn_c1c)) X)))))
      (syn_wa (syn_wral n (syn_cnnc) (.imp (.classMem (.cv n) X) (.classMem (.cv n) Y)))
        (syn_wral n (syn_cnnc)
          (.imp (.classMem (.cv n) Y) (.classMem (syn_cplc (.cv n) (syn_c1c)) X))))
      p0003 p0004
  have p0006 :=
    @g_simpr (syn_wral n (syn_cnnc) (.imp (.classMem (.cv n) X) (.classMem (.cv n) Y)))
      (syn_wral n (syn_cnnc)
        (.imp (.classMem (.cv n) Y) (.classMem (syn_cplc (.cv n) (syn_c1c)) X)))
  have p0007 :=
    @g_syl
      (syn_w3a (syn_wa (.classMem (.cv m) (syn_cnnc)) (.classMem (.cv k) (syn_cnnc)))
        (syn_wa (.classMem (.cv m) X) (.classMem (.cv k) Y)) (syn_wa (syn_wa
            (syn_wral n (syn_cnnc) (.imp (.classMem (.cv n) X)
                (syn_wbr (.cv m) (syn_ckqrel (syn_clefin)) (.cv n)))) (syn_wral n (syn_cnnc)
              (.imp (.classMem (.cv n) Y) (syn_wbr (.cv k) (syn_ckqrel (syn_clefin)) (.cv n)))))
          (syn_wa (syn_wral n (syn_cnnc) (.imp (.classMem (.cv n) X) (.classMem (.cv n) Y)))
            (syn_wral n (syn_cnnc)
              (.imp (.classMem (.cv n) Y) (.classMem (syn_cplc (.cv n) (syn_c1c)) X))))))
      (syn_wa (syn_wral n (syn_cnnc) (.imp (.classMem (.cv n) X) (.classMem (.cv n) Y)))
        (syn_wral n (syn_cnnc)
          (.imp (.classMem (.cv n) Y) (.classMem (syn_cplc (.cv n) (syn_c1c)) X))))
      (syn_wral n (syn_cnnc)
        (.imp (.classMem (.cv n) Y) (.classMem (syn_cplc (.cv n) (syn_c1c)) X)))
      p0005 p0006
  have p0008 :=
    @g_simp1 (syn_wa (.classMem (.cv m) (syn_cnnc)) (.classMem (.cv k) (syn_cnnc)))
      (syn_wa (.classMem (.cv m) X) (.classMem (.cv k) Y))
      (syn_wa (syn_wa (syn_wral n (syn_cnnc) (.imp (.classMem (.cv n) X)
              (syn_wbr (.cv m) (syn_ckqrel (syn_clefin)) (.cv n)))) (syn_wral n (syn_cnnc)
            (.imp (.classMem (.cv n) Y) (syn_wbr (.cv k) (syn_ckqrel (syn_clefin)) (.cv n)))))
        (syn_wa (syn_wral n (syn_cnnc) (.imp (.classMem (.cv n) X) (.classMem (.cv n) Y)))
          (syn_wral n (syn_cnnc)
            (.imp (.classMem (.cv n) Y) (.classMem (syn_cplc (.cv n) (syn_c1c)) X)))))
  have p0009 := @g_simpr (.classMem (.cv m) (syn_cnnc)) (.classMem (.cv k) (syn_cnnc))
  have p0010 :=
    @g_syl
      (syn_w3a (syn_wa (.classMem (.cv m) (syn_cnnc)) (.classMem (.cv k) (syn_cnnc)))
        (syn_wa (.classMem (.cv m) X) (.classMem (.cv k) Y)) (syn_wa (syn_wa
            (syn_wral n (syn_cnnc) (.imp (.classMem (.cv n) X)
                (syn_wbr (.cv m) (syn_ckqrel (syn_clefin)) (.cv n)))) (syn_wral n (syn_cnnc)
              (.imp (.classMem (.cv n) Y) (syn_wbr (.cv k) (syn_ckqrel (syn_clefin)) (.cv n)))))
          (syn_wa (syn_wral n (syn_cnnc) (.imp (.classMem (.cv n) X) (.classMem (.cv n) Y)))
            (syn_wral n (syn_cnnc)
              (.imp (.classMem (.cv n) Y) (.classMem (syn_cplc (.cv n) (syn_c1c)) X))))))
      (syn_wa (.classMem (.cv m) (syn_cnnc)) (.classMem (.cv k) (syn_cnnc)))
      (.classMem (.cv k) (syn_cnnc)) p0008 p0009
  have p0011 :=
    @g_jca
      (syn_w3a (syn_wa (.classMem (.cv m) (syn_cnnc)) (.classMem (.cv k) (syn_cnnc)))
        (syn_wa (.classMem (.cv m) X) (.classMem (.cv k) Y)) (syn_wa (syn_wa
            (syn_wral n (syn_cnnc) (.imp (.classMem (.cv n) X)
                (syn_wbr (.cv m) (syn_ckqrel (syn_clefin)) (.cv n)))) (syn_wral n (syn_cnnc)
              (.imp (.classMem (.cv n) Y) (syn_wbr (.cv k) (syn_ckqrel (syn_clefin)) (.cv n)))))
          (syn_wa (syn_wral n (syn_cnnc) (.imp (.classMem (.cv n) X) (.classMem (.cv n) Y)))
            (syn_wral n (syn_cnnc)
              (.imp (.classMem (.cv n) Y) (.classMem (syn_cplc (.cv n) (syn_c1c)) X))))))
      (syn_wral n (syn_cnnc)
        (.imp (.classMem (.cv n) Y) (.classMem (syn_cplc (.cv n) (syn_c1c)) X)))
      (.classMem (.cv k) (syn_cnnc)) p0007 p0010
  have p0012 := @g_eleq1 (.cv n) (.cv k) Y
  have p0013 := @g_addceq1 (.cv n) (.cv k) (syn_c1c)
  have p0014 :=
    @g_eleq1d (.classEq (.cv n) (.cv k)) (syn_cplc (.cv n) (syn_c1c))
      (syn_cplc (.cv k) (syn_c1c)) X p0013
  have p0015 :=
    @g_imbi12d (.classEq (.cv n) (.cv k)) (.classMem (.cv n) Y) (.classMem (.cv k) Y)
      (.classMem (syn_cplc (.cv n) (syn_c1c)) X)
      (.classMem (syn_cplc (.cv k) (syn_c1c)) X) p0012 p0014
  have p0016 :=
    @g_rspccva (.imp (.classMem (.cv n) Y) (.classMem (syn_cplc (.cv n) (syn_c1c)) X))
      (.imp (.classMem (.cv k) Y) (.classMem (syn_cplc (.cv k) (syn_c1c)) X)) n (.cv k)
      (syn_cnnc) dv_cache_0001 dv_cache_0002 dv_cache_0003 p0015
  have p0017 :=
    @g_syl
      (syn_w3a (syn_wa (.classMem (.cv m) (syn_cnnc)) (.classMem (.cv k) (syn_cnnc)))
        (syn_wa (.classMem (.cv m) X) (.classMem (.cv k) Y)) (syn_wa (syn_wa
            (syn_wral n (syn_cnnc) (.imp (.classMem (.cv n) X)
                (syn_wbr (.cv m) (syn_ckqrel (syn_clefin)) (.cv n)))) (syn_wral n (syn_cnnc)
              (.imp (.classMem (.cv n) Y) (syn_wbr (.cv k) (syn_ckqrel (syn_clefin)) (.cv n)))))
          (syn_wa (syn_wral n (syn_cnnc) (.imp (.classMem (.cv n) X) (.classMem (.cv n) Y)))
            (syn_wral n (syn_cnnc)
              (.imp (.classMem (.cv n) Y) (.classMem (syn_cplc (.cv n) (syn_c1c)) X))))))
      (syn_wa (syn_wral n (syn_cnnc)
          (.imp (.classMem (.cv n) Y) (.classMem (syn_cplc (.cv n) (syn_c1c)) X)))
        (.classMem (.cv k) (syn_cnnc)))
      (.imp (.classMem (.cv k) Y) (.classMem (syn_cplc (.cv k) (syn_c1c)) X)) p0011 p0016
  have p0018 :=
    @g_mpd
      (syn_w3a (syn_wa (.classMem (.cv m) (syn_cnnc)) (.classMem (.cv k) (syn_cnnc)))
        (syn_wa (.classMem (.cv m) X) (.classMem (.cv k) Y)) (syn_wa (syn_wa
            (syn_wral n (syn_cnnc) (.imp (.classMem (.cv n) X)
                (syn_wbr (.cv m) (syn_ckqrel (syn_clefin)) (.cv n)))) (syn_wral n (syn_cnnc)
              (.imp (.classMem (.cv n) Y) (syn_wbr (.cv k) (syn_ckqrel (syn_clefin)) (.cv n)))))
          (syn_wa (syn_wral n (syn_cnnc) (.imp (.classMem (.cv n) X) (.classMem (.cv n) Y)))
            (syn_wral n (syn_cnnc)
              (.imp (.classMem (.cv n) Y) (.classMem (syn_cplc (.cv n) (syn_c1c)) X))))))
      (.classMem (.cv k) Y) (.classMem (syn_cplc (.cv k) (syn_c1c)) X) p0002 p0017
  have p0020 :=
    @g_simpl
      (syn_wa (syn_wral n (syn_cnnc) (.imp (.classMem (.cv n) X)
            (syn_wbr (.cv m) (syn_ckqrel (syn_clefin)) (.cv n)))) (syn_wral n (syn_cnnc)
          (.imp (.classMem (.cv n) Y) (syn_wbr (.cv k) (syn_ckqrel (syn_clefin)) (.cv n)))))
      (syn_wa (syn_wral n (syn_cnnc) (.imp (.classMem (.cv n) X) (.classMem (.cv n) Y)))
        (syn_wral n (syn_cnnc)
          (.imp (.classMem (.cv n) Y) (.classMem (syn_cplc (.cv n) (syn_c1c)) X))))
  have p0021 :=
    @g_syl
      (syn_w3a (syn_wa (.classMem (.cv m) (syn_cnnc)) (.classMem (.cv k) (syn_cnnc)))
        (syn_wa (.classMem (.cv m) X) (.classMem (.cv k) Y)) (syn_wa (syn_wa
            (syn_wral n (syn_cnnc) (.imp (.classMem (.cv n) X)
                (syn_wbr (.cv m) (syn_ckqrel (syn_clefin)) (.cv n)))) (syn_wral n (syn_cnnc)
              (.imp (.classMem (.cv n) Y) (syn_wbr (.cv k) (syn_ckqrel (syn_clefin)) (.cv n)))))
          (syn_wa (syn_wral n (syn_cnnc) (.imp (.classMem (.cv n) X) (.classMem (.cv n) Y)))
            (syn_wral n (syn_cnnc)
              (.imp (.classMem (.cv n) Y) (.classMem (syn_cplc (.cv n) (syn_c1c)) X))))))
      (syn_wa (syn_wa (syn_wral n (syn_cnnc) (.imp (.classMem (.cv n) X)
              (syn_wbr (.cv m) (syn_ckqrel (syn_clefin)) (.cv n)))) (syn_wral n (syn_cnnc)
            (.imp (.classMem (.cv n) Y) (syn_wbr (.cv k) (syn_ckqrel (syn_clefin)) (.cv n)))))
        (syn_wa (syn_wral n (syn_cnnc) (.imp (.classMem (.cv n) X) (.classMem (.cv n) Y)))
          (syn_wral n (syn_cnnc)
            (.imp (.classMem (.cv n) Y) (.classMem (syn_cplc (.cv n) (syn_c1c)) X)))))
      (syn_wa (syn_wral n (syn_cnnc) (.imp (.classMem (.cv n) X)
            (syn_wbr (.cv m) (syn_ckqrel (syn_clefin)) (.cv n)))) (syn_wral n (syn_cnnc)
          (.imp (.classMem (.cv n) Y) (syn_wbr (.cv k) (syn_ckqrel (syn_clefin)) (.cv n)))))
      p0003 p0020
  have p0022 :=
    @g_simpl
      (syn_wral n (syn_cnnc)
        (.imp (.classMem (.cv n) X) (syn_wbr (.cv m) (syn_ckqrel (syn_clefin)) (.cv n))))
      (syn_wral n (syn_cnnc)
        (.imp (.classMem (.cv n) Y) (syn_wbr (.cv k) (syn_ckqrel (syn_clefin)) (.cv n))))
  have p0023 :=
    @g_syl
      (syn_w3a (syn_wa (.classMem (.cv m) (syn_cnnc)) (.classMem (.cv k) (syn_cnnc)))
        (syn_wa (.classMem (.cv m) X) (.classMem (.cv k) Y)) (syn_wa (syn_wa
            (syn_wral n (syn_cnnc) (.imp (.classMem (.cv n) X)
                (syn_wbr (.cv m) (syn_ckqrel (syn_clefin)) (.cv n)))) (syn_wral n (syn_cnnc)
              (.imp (.classMem (.cv n) Y) (syn_wbr (.cv k) (syn_ckqrel (syn_clefin)) (.cv n)))))
          (syn_wa (syn_wral n (syn_cnnc) (.imp (.classMem (.cv n) X) (.classMem (.cv n) Y)))
            (syn_wral n (syn_cnnc)
              (.imp (.classMem (.cv n) Y) (.classMem (syn_cplc (.cv n) (syn_c1c)) X))))))
      (syn_wa (syn_wral n (syn_cnnc) (.imp (.classMem (.cv n) X)
            (syn_wbr (.cv m) (syn_ckqrel (syn_clefin)) (.cv n)))) (syn_wral n (syn_cnnc)
          (.imp (.classMem (.cv n) Y) (syn_wbr (.cv k) (syn_ckqrel (syn_clefin)) (.cv n)))))
      (syn_wral n (syn_cnnc)
        (.imp (.classMem (.cv n) X) (syn_wbr (.cv m) (syn_ckqrel (syn_clefin)) (.cv n))))
      p0021 p0022
  have p0027 := @g_peano2 (.cv k)
  have p0028 :=
    @g_syl
      (syn_w3a (syn_wa (.classMem (.cv m) (syn_cnnc)) (.classMem (.cv k) (syn_cnnc)))
        (syn_wa (.classMem (.cv m) X) (.classMem (.cv k) Y)) (syn_wa (syn_wa
            (syn_wral n (syn_cnnc) (.imp (.classMem (.cv n) X)
                (syn_wbr (.cv m) (syn_ckqrel (syn_clefin)) (.cv n)))) (syn_wral n (syn_cnnc)
              (.imp (.classMem (.cv n) Y) (syn_wbr (.cv k) (syn_ckqrel (syn_clefin)) (.cv n)))))
          (syn_wa (syn_wral n (syn_cnnc) (.imp (.classMem (.cv n) X) (.classMem (.cv n) Y)))
            (syn_wral n (syn_cnnc)
              (.imp (.classMem (.cv n) Y) (.classMem (syn_cplc (.cv n) (syn_c1c)) X))))))
      (.classMem (.cv k) (syn_cnnc)) (.classMem (syn_cplc (.cv k) (syn_c1c)) (syn_cnnc))
      p0010 p0027
  have p0029 :=
    @g_jca
      (syn_w3a (syn_wa (.classMem (.cv m) (syn_cnnc)) (.classMem (.cv k) (syn_cnnc)))
        (syn_wa (.classMem (.cv m) X) (.classMem (.cv k) Y)) (syn_wa (syn_wa
            (syn_wral n (syn_cnnc) (.imp (.classMem (.cv n) X)
                (syn_wbr (.cv m) (syn_ckqrel (syn_clefin)) (.cv n)))) (syn_wral n (syn_cnnc)
              (.imp (.classMem (.cv n) Y) (syn_wbr (.cv k) (syn_ckqrel (syn_clefin)) (.cv n)))))
          (syn_wa (syn_wral n (syn_cnnc) (.imp (.classMem (.cv n) X) (.classMem (.cv n) Y)))
            (syn_wral n (syn_cnnc)
              (.imp (.classMem (.cv n) Y) (.classMem (syn_cplc (.cv n) (syn_c1c)) X))))))
      (syn_wral n (syn_cnnc)
        (.imp (.classMem (.cv n) X) (syn_wbr (.cv m) (syn_ckqrel (syn_clefin)) (.cv n))))
      (.classMem (syn_cplc (.cv k) (syn_c1c)) (syn_cnnc)) p0023 p0028
  have p0030 := @g_eleq1 (.cv n) (syn_cplc (.cv k) (syn_c1c)) X
  have p0031 :=
    @g_breq2 (.cv n) (syn_cplc (.cv k) (syn_c1c)) (.cv m) (syn_ckqrel (syn_clefin))
  have p0032 :=
    @g_imbi12d (.classEq (.cv n) (syn_cplc (.cv k) (syn_c1c))) (.classMem (.cv n) X)
      (.classMem (syn_cplc (.cv k) (syn_c1c)) X)
      (syn_wbr (.cv m) (syn_ckqrel (syn_clefin)) (.cv n))
      (syn_wbr (.cv m) (syn_ckqrel (syn_clefin)) (syn_cplc (.cv k) (syn_c1c))) p0030 p0031
  have p0033 :=
    @g_rspccva
      (.imp (.classMem (.cv n) X) (syn_wbr (.cv m) (syn_ckqrel (syn_clefin)) (.cv n)))
      (.imp (.classMem (syn_cplc (.cv k) (syn_c1c)) X)
        (syn_wbr (.cv m) (syn_ckqrel (syn_clefin)) (syn_cplc (.cv k) (syn_c1c))))
      n (syn_cplc (.cv k) (syn_c1c)) (syn_cnnc) dv_cache_0004 dv_cache_0002 dv_cache_0005
      p0032
  have p0034 :=
    @g_syl
      (syn_w3a (syn_wa (.classMem (.cv m) (syn_cnnc)) (.classMem (.cv k) (syn_cnnc)))
        (syn_wa (.classMem (.cv m) X) (.classMem (.cv k) Y)) (syn_wa (syn_wa
            (syn_wral n (syn_cnnc) (.imp (.classMem (.cv n) X)
                (syn_wbr (.cv m) (syn_ckqrel (syn_clefin)) (.cv n)))) (syn_wral n (syn_cnnc)
              (.imp (.classMem (.cv n) Y) (syn_wbr (.cv k) (syn_ckqrel (syn_clefin)) (.cv n)))))
          (syn_wa (syn_wral n (syn_cnnc) (.imp (.classMem (.cv n) X) (.classMem (.cv n) Y)))
            (syn_wral n (syn_cnnc)
              (.imp (.classMem (.cv n) Y) (.classMem (syn_cplc (.cv n) (syn_c1c)) X))))))
      (syn_wa (syn_wral n (syn_cnnc) (.imp (.classMem (.cv n) X)
            (syn_wbr (.cv m) (syn_ckqrel (syn_clefin)) (.cv n))))
        (.classMem (syn_cplc (.cv k) (syn_c1c)) (syn_cnnc)))
      (.imp (.classMem (syn_cplc (.cv k) (syn_c1c)) X)
        (syn_wbr (.cv m) (syn_ckqrel (syn_clefin)) (syn_cplc (.cv k) (syn_c1c))))
      p0029 p0033
  have p0035 :=
    @g_mpd
      (syn_w3a (syn_wa (.classMem (.cv m) (syn_cnnc)) (.classMem (.cv k) (syn_cnnc)))
        (syn_wa (.classMem (.cv m) X) (.classMem (.cv k) Y)) (syn_wa (syn_wa
            (syn_wral n (syn_cnnc) (.imp (.classMem (.cv n) X)
                (syn_wbr (.cv m) (syn_ckqrel (syn_clefin)) (.cv n)))) (syn_wral n (syn_cnnc)
              (.imp (.classMem (.cv n) Y) (syn_wbr (.cv k) (syn_ckqrel (syn_clefin)) (.cv n)))))
          (syn_wa (syn_wral n (syn_cnnc) (.imp (.classMem (.cv n) X) (.classMem (.cv n) Y)))
            (syn_wral n (syn_cnnc)
              (.imp (.classMem (.cv n) Y) (.classMem (syn_cplc (.cv n) (syn_c1c)) X))))))
      (.classMem (syn_cplc (.cv k) (syn_c1c)) X)
      (syn_wbr (.cv m) (syn_ckqrel (syn_clefin)) (syn_cplc (.cv k) (syn_c1c))) p0018 p0034
  have p0040 := @g_simpl (.classMem (.cv m) (syn_cnnc)) (.classMem (.cv k) (syn_cnnc))
  have p0041 :=
    @g_syl
      (syn_w3a (syn_wa (.classMem (.cv m) (syn_cnnc)) (.classMem (.cv k) (syn_cnnc)))
        (syn_wa (.classMem (.cv m) X) (.classMem (.cv k) Y)) (syn_wa (syn_wa
            (syn_wral n (syn_cnnc) (.imp (.classMem (.cv n) X)
                (syn_wbr (.cv m) (syn_ckqrel (syn_clefin)) (.cv n)))) (syn_wral n (syn_cnnc)
              (.imp (.classMem (.cv n) Y) (syn_wbr (.cv k) (syn_ckqrel (syn_clefin)) (.cv n)))))
          (syn_wa (syn_wral n (syn_cnnc) (.imp (.classMem (.cv n) X) (.classMem (.cv n) Y)))
            (syn_wral n (syn_cnnc)
              (.imp (.classMem (.cv n) Y) (.classMem (syn_cplc (.cv n) (syn_c1c)) X))))))
      (syn_wa (.classMem (.cv m) (syn_cnnc)) (.classMem (.cv k) (syn_cnnc)))
      (.classMem (.cv m) (syn_cnnc)) p0008 p0040
  have p0042 :=
    @g_jca
      (syn_w3a (syn_wa (.classMem (.cv m) (syn_cnnc)) (.classMem (.cv k) (syn_cnnc)))
        (syn_wa (.classMem (.cv m) X) (.classMem (.cv k) Y)) (syn_wa (syn_wa
            (syn_wral n (syn_cnnc) (.imp (.classMem (.cv n) X)
                (syn_wbr (.cv m) (syn_ckqrel (syn_clefin)) (.cv n)))) (syn_wral n (syn_cnnc)
              (.imp (.classMem (.cv n) Y) (syn_wbr (.cv k) (syn_ckqrel (syn_clefin)) (.cv n)))))
          (syn_wa (syn_wral n (syn_cnnc) (.imp (.classMem (.cv n) X) (.classMem (.cv n) Y)))
            (syn_wral n (syn_cnnc)
              (.imp (.classMem (.cv n) Y) (.classMem (syn_cplc (.cv n) (syn_c1c)) X))))))
      (.classMem (.cv k) (syn_cnnc)) (.classMem (.cv m) (syn_cnnc)) p0010 p0041
  have p0043 := @g_kqfinsucsplit (.cv k) (.cv m)
  have p0044 :=
    @g_syl
      (syn_w3a (syn_wa (.classMem (.cv m) (syn_cnnc)) (.classMem (.cv k) (syn_cnnc)))
        (syn_wa (.classMem (.cv m) X) (.classMem (.cv k) Y)) (syn_wa (syn_wa
            (syn_wral n (syn_cnnc) (.imp (.classMem (.cv n) X)
                (syn_wbr (.cv m) (syn_ckqrel (syn_clefin)) (.cv n)))) (syn_wral n (syn_cnnc)
              (.imp (.classMem (.cv n) Y) (syn_wbr (.cv k) (syn_ckqrel (syn_clefin)) (.cv n)))))
          (syn_wa (syn_wral n (syn_cnnc) (.imp (.classMem (.cv n) X) (.classMem (.cv n) Y)))
            (syn_wral n (syn_cnnc)
              (.imp (.classMem (.cv n) Y) (.classMem (syn_cplc (.cv n) (syn_c1c)) X))))))
      (syn_wa (.classMem (.cv k) (syn_cnnc)) (.classMem (.cv m) (syn_cnnc)))
      (syn_wb (syn_wbr (.cv m) (syn_ckqrel (syn_clefin)) (syn_cplc (.cv k) (syn_c1c)))
        (syn_wo (syn_wbr (.cv m) (syn_ckqrel (syn_clefin)) (.cv k))
          (.classEq (.cv m) (syn_cplc (.cv k) (syn_c1c)))))
      p0042 p0043
  have p0045 :=
    @g_biimpd
      (syn_w3a (syn_wa (.classMem (.cv m) (syn_cnnc)) (.classMem (.cv k) (syn_cnnc)))
        (syn_wa (.classMem (.cv m) X) (.classMem (.cv k) Y)) (syn_wa (syn_wa
            (syn_wral n (syn_cnnc) (.imp (.classMem (.cv n) X)
                (syn_wbr (.cv m) (syn_ckqrel (syn_clefin)) (.cv n)))) (syn_wral n (syn_cnnc)
              (.imp (.classMem (.cv n) Y) (syn_wbr (.cv k) (syn_ckqrel (syn_clefin)) (.cv n)))))
          (syn_wa (syn_wral n (syn_cnnc) (.imp (.classMem (.cv n) X) (.classMem (.cv n) Y)))
            (syn_wral n (syn_cnnc)
              (.imp (.classMem (.cv n) Y) (.classMem (syn_cplc (.cv n) (syn_c1c)) X))))))
      (syn_wbr (.cv m) (syn_ckqrel (syn_clefin)) (syn_cplc (.cv k) (syn_c1c)))
      (syn_wo (syn_wbr (.cv m) (syn_ckqrel (syn_clefin)) (.cv k))
        (.classEq (.cv m) (syn_cplc (.cv k) (syn_c1c))))
      p0044
  have p0046 :=
    @g_mpd
      (syn_w3a (syn_wa (.classMem (.cv m) (syn_cnnc)) (.classMem (.cv k) (syn_cnnc)))
        (syn_wa (.classMem (.cv m) X) (.classMem (.cv k) Y)) (syn_wa (syn_wa
            (syn_wral n (syn_cnnc) (.imp (.classMem (.cv n) X)
                (syn_wbr (.cv m) (syn_ckqrel (syn_clefin)) (.cv n)))) (syn_wral n (syn_cnnc)
              (.imp (.classMem (.cv n) Y) (syn_wbr (.cv k) (syn_ckqrel (syn_clefin)) (.cv n)))))
          (syn_wa (syn_wral n (syn_cnnc) (.imp (.classMem (.cv n) X) (.classMem (.cv n) Y)))
            (syn_wral n (syn_cnnc)
              (.imp (.classMem (.cv n) Y) (.classMem (syn_cplc (.cv n) (syn_c1c)) X))))))
      (syn_wbr (.cv m) (syn_ckqrel (syn_clefin)) (syn_cplc (.cv k) (syn_c1c)))
      (syn_wo (syn_wbr (.cv m) (syn_ckqrel (syn_clefin)) (.cv k))
        (.classEq (.cv m) (syn_cplc (.cv k) (syn_c1c))))
      p0035 p0045
  have p0047 :=
    @g_simpr
      (syn_w3a (syn_wa (.classMem (.cv m) (syn_cnnc)) (.classMem (.cv k) (syn_cnnc)))
        (syn_wa (.classMem (.cv m) X) (.classMem (.cv k) Y)) (syn_wa (syn_wa
            (syn_wral n (syn_cnnc) (.imp (.classMem (.cv n) X)
                (syn_wbr (.cv m) (syn_ckqrel (syn_clefin)) (.cv n)))) (syn_wral n (syn_cnnc)
              (.imp (.classMem (.cv n) Y) (syn_wbr (.cv k) (syn_ckqrel (syn_clefin)) (.cv n)))))
          (syn_wa (syn_wral n (syn_cnnc) (.imp (.classMem (.cv n) X) (.classMem (.cv n) Y)))
            (syn_wral n (syn_cnnc)
              (.imp (.classMem (.cv n) Y) (.classMem (syn_cplc (.cv n) (syn_c1c)) X))))))
      (syn_wbr (.cv m) (syn_ckqrel (syn_clefin)) (.cv k))
  have p0048 :=
    @g_simpl
      (syn_w3a (syn_wa (.classMem (.cv m) (syn_cnnc)) (.classMem (.cv k) (syn_cnnc)))
        (syn_wa (.classMem (.cv m) X) (.classMem (.cv k) Y)) (syn_wa (syn_wa
            (syn_wral n (syn_cnnc) (.imp (.classMem (.cv n) X)
                (syn_wbr (.cv m) (syn_ckqrel (syn_clefin)) (.cv n)))) (syn_wral n (syn_cnnc)
              (.imp (.classMem (.cv n) Y) (syn_wbr (.cv k) (syn_ckqrel (syn_clefin)) (.cv n)))))
          (syn_wa (syn_wral n (syn_cnnc) (.imp (.classMem (.cv n) X) (.classMem (.cv n) Y)))
            (syn_wral n (syn_cnnc)
              (.imp (.classMem (.cv n) Y) (.classMem (syn_cplc (.cv n) (syn_c1c)) X))))))
      (syn_wbr (.cv m) (syn_ckqrel (syn_clefin)) (.cv k))
  have p0050 := @g_simpl (.classMem (.cv m) X) (.classMem (.cv k) Y)
  have p0051 :=
    @g_syl
      (syn_w3a (syn_wa (.classMem (.cv m) (syn_cnnc)) (.classMem (.cv k) (syn_cnnc)))
        (syn_wa (.classMem (.cv m) X) (.classMem (.cv k) Y)) (syn_wa (syn_wa
            (syn_wral n (syn_cnnc) (.imp (.classMem (.cv n) X)
                (syn_wbr (.cv m) (syn_ckqrel (syn_clefin)) (.cv n)))) (syn_wral n (syn_cnnc)
              (.imp (.classMem (.cv n) Y) (syn_wbr (.cv k) (syn_ckqrel (syn_clefin)) (.cv n)))))
          (syn_wa (syn_wral n (syn_cnnc) (.imp (.classMem (.cv n) X) (.classMem (.cv n) Y)))
            (syn_wral n (syn_cnnc)
              (.imp (.classMem (.cv n) Y) (.classMem (syn_cplc (.cv n) (syn_c1c)) X))))))
      (syn_wa (.classMem (.cv m) X) (.classMem (.cv k) Y)) (.classMem (.cv m) X) p0000
      p0050
  have p0055 :=
    @g_simpl (syn_wral n (syn_cnnc) (.imp (.classMem (.cv n) X) (.classMem (.cv n) Y)))
      (syn_wral n (syn_cnnc)
        (.imp (.classMem (.cv n) Y) (.classMem (syn_cplc (.cv n) (syn_c1c)) X)))
  have p0056 :=
    @g_syl
      (syn_w3a (syn_wa (.classMem (.cv m) (syn_cnnc)) (.classMem (.cv k) (syn_cnnc)))
        (syn_wa (.classMem (.cv m) X) (.classMem (.cv k) Y)) (syn_wa (syn_wa
            (syn_wral n (syn_cnnc) (.imp (.classMem (.cv n) X)
                (syn_wbr (.cv m) (syn_ckqrel (syn_clefin)) (.cv n)))) (syn_wral n (syn_cnnc)
              (.imp (.classMem (.cv n) Y) (syn_wbr (.cv k) (syn_ckqrel (syn_clefin)) (.cv n)))))
          (syn_wa (syn_wral n (syn_cnnc) (.imp (.classMem (.cv n) X) (.classMem (.cv n) Y)))
            (syn_wral n (syn_cnnc)
              (.imp (.classMem (.cv n) Y) (.classMem (syn_cplc (.cv n) (syn_c1c)) X))))))
      (syn_wa (syn_wral n (syn_cnnc) (.imp (.classMem (.cv n) X) (.classMem (.cv n) Y)))
        (syn_wral n (syn_cnnc)
          (.imp (.classMem (.cv n) Y) (.classMem (syn_cplc (.cv n) (syn_c1c)) X))))
      (syn_wral n (syn_cnnc) (.imp (.classMem (.cv n) X) (.classMem (.cv n) Y))) p0005
      p0055
  have p0060 :=
    @g_jca
      (syn_w3a (syn_wa (.classMem (.cv m) (syn_cnnc)) (.classMem (.cv k) (syn_cnnc)))
        (syn_wa (.classMem (.cv m) X) (.classMem (.cv k) Y)) (syn_wa (syn_wa
            (syn_wral n (syn_cnnc) (.imp (.classMem (.cv n) X)
                (syn_wbr (.cv m) (syn_ckqrel (syn_clefin)) (.cv n)))) (syn_wral n (syn_cnnc)
              (.imp (.classMem (.cv n) Y) (syn_wbr (.cv k) (syn_ckqrel (syn_clefin)) (.cv n)))))
          (syn_wa (syn_wral n (syn_cnnc) (.imp (.classMem (.cv n) X) (.classMem (.cv n) Y)))
            (syn_wral n (syn_cnnc)
              (.imp (.classMem (.cv n) Y) (.classMem (syn_cplc (.cv n) (syn_c1c)) X))))))
      (syn_wral n (syn_cnnc) (.imp (.classMem (.cv n) X) (.classMem (.cv n) Y)))
      (.classMem (.cv m) (syn_cnnc)) p0056 p0041
  have p0061 := @g_eleq1 (.cv n) (.cv m) X
  have p0062 := @g_eleq1 (.cv n) (.cv m) Y
  have p0063 :=
    @g_imbi12d (.classEq (.cv n) (.cv m)) (.classMem (.cv n) X) (.classMem (.cv m) X)
      (.classMem (.cv n) Y) (.classMem (.cv m) Y) p0061 p0062
  have p0064 :=
    @g_rspccva (.imp (.classMem (.cv n) X) (.classMem (.cv n) Y))
      (.imp (.classMem (.cv m) X) (.classMem (.cv m) Y)) n (.cv m) (syn_cnnc)
      dv_cache_0006 dv_cache_0002 dv_cache_0007 p0063
  have p0065 :=
    @g_syl
      (syn_w3a (syn_wa (.classMem (.cv m) (syn_cnnc)) (.classMem (.cv k) (syn_cnnc)))
        (syn_wa (.classMem (.cv m) X) (.classMem (.cv k) Y)) (syn_wa (syn_wa
            (syn_wral n (syn_cnnc) (.imp (.classMem (.cv n) X)
                (syn_wbr (.cv m) (syn_ckqrel (syn_clefin)) (.cv n)))) (syn_wral n (syn_cnnc)
              (.imp (.classMem (.cv n) Y) (syn_wbr (.cv k) (syn_ckqrel (syn_clefin)) (.cv n)))))
          (syn_wa (syn_wral n (syn_cnnc) (.imp (.classMem (.cv n) X) (.classMem (.cv n) Y)))
            (syn_wral n (syn_cnnc)
              (.imp (.classMem (.cv n) Y) (.classMem (syn_cplc (.cv n) (syn_c1c)) X))))))
      (syn_wa (syn_wral n (syn_cnnc) (.imp (.classMem (.cv n) X) (.classMem (.cv n) Y)))
        (.classMem (.cv m) (syn_cnnc)))
      (.imp (.classMem (.cv m) X) (.classMem (.cv m) Y)) p0060 p0064
  have p0066 :=
    @g_mpd
      (syn_w3a (syn_wa (.classMem (.cv m) (syn_cnnc)) (.classMem (.cv k) (syn_cnnc)))
        (syn_wa (.classMem (.cv m) X) (.classMem (.cv k) Y)) (syn_wa (syn_wa
            (syn_wral n (syn_cnnc) (.imp (.classMem (.cv n) X)
                (syn_wbr (.cv m) (syn_ckqrel (syn_clefin)) (.cv n)))) (syn_wral n (syn_cnnc)
              (.imp (.classMem (.cv n) Y) (syn_wbr (.cv k) (syn_ckqrel (syn_clefin)) (.cv n)))))
          (syn_wa (syn_wral n (syn_cnnc) (.imp (.classMem (.cv n) X) (.classMem (.cv n) Y)))
            (syn_wral n (syn_cnnc)
              (.imp (.classMem (.cv n) Y) (.classMem (syn_cplc (.cv n) (syn_c1c)) X))))))
      (.classMem (.cv m) X) (.classMem (.cv m) Y) p0051 p0065
  have p0070 :=
    @g_simpr
      (syn_wral n (syn_cnnc)
        (.imp (.classMem (.cv n) X) (syn_wbr (.cv m) (syn_ckqrel (syn_clefin)) (.cv n))))
      (syn_wral n (syn_cnnc)
        (.imp (.classMem (.cv n) Y) (syn_wbr (.cv k) (syn_ckqrel (syn_clefin)) (.cv n))))
  have p0071 :=
    @g_syl
      (syn_w3a (syn_wa (.classMem (.cv m) (syn_cnnc)) (.classMem (.cv k) (syn_cnnc)))
        (syn_wa (.classMem (.cv m) X) (.classMem (.cv k) Y)) (syn_wa (syn_wa
            (syn_wral n (syn_cnnc) (.imp (.classMem (.cv n) X)
                (syn_wbr (.cv m) (syn_ckqrel (syn_clefin)) (.cv n)))) (syn_wral n (syn_cnnc)
              (.imp (.classMem (.cv n) Y) (syn_wbr (.cv k) (syn_ckqrel (syn_clefin)) (.cv n)))))
          (syn_wa (syn_wral n (syn_cnnc) (.imp (.classMem (.cv n) X) (.classMem (.cv n) Y)))
            (syn_wral n (syn_cnnc)
              (.imp (.classMem (.cv n) Y) (.classMem (syn_cplc (.cv n) (syn_c1c)) X))))))
      (syn_wa (syn_wral n (syn_cnnc) (.imp (.classMem (.cv n) X)
            (syn_wbr (.cv m) (syn_ckqrel (syn_clefin)) (.cv n)))) (syn_wral n (syn_cnnc)
          (.imp (.classMem (.cv n) Y) (syn_wbr (.cv k) (syn_ckqrel (syn_clefin)) (.cv n)))))
      (syn_wral n (syn_cnnc)
        (.imp (.classMem (.cv n) Y) (syn_wbr (.cv k) (syn_ckqrel (syn_clefin)) (.cv n))))
      p0021 p0070
  have p0075 :=
    @g_jca
      (syn_w3a (syn_wa (.classMem (.cv m) (syn_cnnc)) (.classMem (.cv k) (syn_cnnc)))
        (syn_wa (.classMem (.cv m) X) (.classMem (.cv k) Y)) (syn_wa (syn_wa
            (syn_wral n (syn_cnnc) (.imp (.classMem (.cv n) X)
                (syn_wbr (.cv m) (syn_ckqrel (syn_clefin)) (.cv n)))) (syn_wral n (syn_cnnc)
              (.imp (.classMem (.cv n) Y) (syn_wbr (.cv k) (syn_ckqrel (syn_clefin)) (.cv n)))))
          (syn_wa (syn_wral n (syn_cnnc) (.imp (.classMem (.cv n) X) (.classMem (.cv n) Y)))
            (syn_wral n (syn_cnnc)
              (.imp (.classMem (.cv n) Y) (.classMem (syn_cplc (.cv n) (syn_c1c)) X))))))
      (syn_wral n (syn_cnnc)
        (.imp (.classMem (.cv n) Y) (syn_wbr (.cv k) (syn_ckqrel (syn_clefin)) (.cv n))))
      (.classMem (.cv m) (syn_cnnc)) p0071 p0041
  have p0077 := @g_breq2 (.cv n) (.cv m) (.cv k) (syn_ckqrel (syn_clefin))
  have p0078 :=
    @g_imbi12d (.classEq (.cv n) (.cv m)) (.classMem (.cv n) Y) (.classMem (.cv m) Y)
      (syn_wbr (.cv k) (syn_ckqrel (syn_clefin)) (.cv n))
      (syn_wbr (.cv k) (syn_ckqrel (syn_clefin)) (.cv m)) p0062 p0077
  have p0079 :=
    @g_rspccva
      (.imp (.classMem (.cv n) Y) (syn_wbr (.cv k) (syn_ckqrel (syn_clefin)) (.cv n)))
      (.imp (.classMem (.cv m) Y) (syn_wbr (.cv k) (syn_ckqrel (syn_clefin)) (.cv m))) n
      (.cv m) (syn_cnnc) dv_cache_0006 dv_cache_0002 dv_cache_0008 p0078
  have p0080 :=
    @g_syl
      (syn_w3a (syn_wa (.classMem (.cv m) (syn_cnnc)) (.classMem (.cv k) (syn_cnnc)))
        (syn_wa (.classMem (.cv m) X) (.classMem (.cv k) Y)) (syn_wa (syn_wa
            (syn_wral n (syn_cnnc) (.imp (.classMem (.cv n) X)
                (syn_wbr (.cv m) (syn_ckqrel (syn_clefin)) (.cv n)))) (syn_wral n (syn_cnnc)
              (.imp (.classMem (.cv n) Y) (syn_wbr (.cv k) (syn_ckqrel (syn_clefin)) (.cv n)))))
          (syn_wa (syn_wral n (syn_cnnc) (.imp (.classMem (.cv n) X) (.classMem (.cv n) Y)))
            (syn_wral n (syn_cnnc)
              (.imp (.classMem (.cv n) Y) (.classMem (syn_cplc (.cv n) (syn_c1c)) X))))))
      (syn_wa (syn_wral n (syn_cnnc) (.imp (.classMem (.cv n) Y)
            (syn_wbr (.cv k) (syn_ckqrel (syn_clefin)) (.cv n))))
        (.classMem (.cv m) (syn_cnnc)))
      (.imp (.classMem (.cv m) Y) (syn_wbr (.cv k) (syn_ckqrel (syn_clefin)) (.cv m)))
      p0075 p0079
  have p0081 :=
    @g_mpd
      (syn_w3a (syn_wa (.classMem (.cv m) (syn_cnnc)) (.classMem (.cv k) (syn_cnnc)))
        (syn_wa (.classMem (.cv m) X) (.classMem (.cv k) Y)) (syn_wa (syn_wa
            (syn_wral n (syn_cnnc) (.imp (.classMem (.cv n) X)
                (syn_wbr (.cv m) (syn_ckqrel (syn_clefin)) (.cv n)))) (syn_wral n (syn_cnnc)
              (.imp (.classMem (.cv n) Y) (syn_wbr (.cv k) (syn_ckqrel (syn_clefin)) (.cv n)))))
          (syn_wa (syn_wral n (syn_cnnc) (.imp (.classMem (.cv n) X) (.classMem (.cv n) Y)))
            (syn_wral n (syn_cnnc)
              (.imp (.classMem (.cv n) Y) (.classMem (syn_cplc (.cv n) (syn_c1c)) X))))))
      (.classMem (.cv m) Y) (syn_wbr (.cv k) (syn_ckqrel (syn_clefin)) (.cv m)) p0066
      p0080
  have p0082 :=
    @g_syl
      (syn_wa (syn_w3a (syn_wa (.classMem (.cv m) (syn_cnnc)) (.classMem (.cv k) (syn_cnnc)))
          (syn_wa (.classMem (.cv m) X) (.classMem (.cv k) Y)) (syn_wa (syn_wa
              (syn_wral n (syn_cnnc) (.imp (.classMem (.cv n) X)
                  (syn_wbr (.cv m) (syn_ckqrel (syn_clefin)) (.cv n)))) (syn_wral n (syn_cnnc)
                (.imp (.classMem (.cv n) Y)
                  (syn_wbr (.cv k) (syn_ckqrel (syn_clefin)) (.cv n))))) (syn_wa
              (syn_wral n (syn_cnnc) (.imp (.classMem (.cv n) X) (.classMem (.cv n) Y)))
              (syn_wral n (syn_cnnc) (.imp (.classMem (.cv n) Y)
                  (.classMem (syn_cplc (.cv n) (syn_c1c)) X))))))
        (syn_wbr (.cv m) (syn_ckqrel (syn_clefin)) (.cv k)))
      (syn_w3a (syn_wa (.classMem (.cv m) (syn_cnnc)) (.classMem (.cv k) (syn_cnnc)))
        (syn_wa (.classMem (.cv m) X) (.classMem (.cv k) Y)) (syn_wa (syn_wa
            (syn_wral n (syn_cnnc) (.imp (.classMem (.cv n) X)
                (syn_wbr (.cv m) (syn_ckqrel (syn_clefin)) (.cv n)))) (syn_wral n (syn_cnnc)
              (.imp (.classMem (.cv n) Y) (syn_wbr (.cv k) (syn_ckqrel (syn_clefin)) (.cv n)))))
          (syn_wa (syn_wral n (syn_cnnc) (.imp (.classMem (.cv n) X) (.classMem (.cv n) Y)))
            (syn_wral n (syn_cnnc)
              (.imp (.classMem (.cv n) Y) (.classMem (syn_cplc (.cv n) (syn_c1c)) X))))))
      (syn_wbr (.cv k) (syn_ckqrel (syn_clefin)) (.cv m)) p0048 p0081
  have p0083 :=
    @g_jca
      (syn_wa (syn_w3a (syn_wa (.classMem (.cv m) (syn_cnnc)) (.classMem (.cv k) (syn_cnnc)))
          (syn_wa (.classMem (.cv m) X) (.classMem (.cv k) Y)) (syn_wa (syn_wa
              (syn_wral n (syn_cnnc) (.imp (.classMem (.cv n) X)
                  (syn_wbr (.cv m) (syn_ckqrel (syn_clefin)) (.cv n)))) (syn_wral n (syn_cnnc)
                (.imp (.classMem (.cv n) Y)
                  (syn_wbr (.cv k) (syn_ckqrel (syn_clefin)) (.cv n))))) (syn_wa
              (syn_wral n (syn_cnnc) (.imp (.classMem (.cv n) X) (.classMem (.cv n) Y)))
              (syn_wral n (syn_cnnc) (.imp (.classMem (.cv n) Y)
                  (.classMem (syn_cplc (.cv n) (syn_c1c)) X))))))
        (syn_wbr (.cv m) (syn_ckqrel (syn_clefin)) (.cv k)))
      (syn_wbr (.cv m) (syn_ckqrel (syn_clefin)) (.cv k))
      (syn_wbr (.cv k) (syn_ckqrel (syn_clefin)) (.cv m)) p0047 p0082
  have p0086 := @g_kqfinantinn (.cv m) (.cv k)
  have p0087 :=
    @g_syl
      (syn_w3a (syn_wa (.classMem (.cv m) (syn_cnnc)) (.classMem (.cv k) (syn_cnnc)))
        (syn_wa (.classMem (.cv m) X) (.classMem (.cv k) Y)) (syn_wa (syn_wa
            (syn_wral n (syn_cnnc) (.imp (.classMem (.cv n) X)
                (syn_wbr (.cv m) (syn_ckqrel (syn_clefin)) (.cv n)))) (syn_wral n (syn_cnnc)
              (.imp (.classMem (.cv n) Y) (syn_wbr (.cv k) (syn_ckqrel (syn_clefin)) (.cv n)))))
          (syn_wa (syn_wral n (syn_cnnc) (.imp (.classMem (.cv n) X) (.classMem (.cv n) Y)))
            (syn_wral n (syn_cnnc)
              (.imp (.classMem (.cv n) Y) (.classMem (syn_cplc (.cv n) (syn_c1c)) X))))))
      (syn_wa (.classMem (.cv m) (syn_cnnc)) (.classMem (.cv k) (syn_cnnc)))
      (.imp (syn_wa (syn_wbr (.cv m) (syn_ckqrel (syn_clefin)) (.cv k))
          (syn_wbr (.cv k) (syn_ckqrel (syn_clefin)) (.cv m))) (.classEq (.cv m) (.cv k)))
      p0008 p0086
  have p0088 :=
    @g_syl
      (syn_wa (syn_w3a (syn_wa (.classMem (.cv m) (syn_cnnc)) (.classMem (.cv k) (syn_cnnc)))
          (syn_wa (.classMem (.cv m) X) (.classMem (.cv k) Y)) (syn_wa (syn_wa
              (syn_wral n (syn_cnnc) (.imp (.classMem (.cv n) X)
                  (syn_wbr (.cv m) (syn_ckqrel (syn_clefin)) (.cv n)))) (syn_wral n (syn_cnnc)
                (.imp (.classMem (.cv n) Y)
                  (syn_wbr (.cv k) (syn_ckqrel (syn_clefin)) (.cv n))))) (syn_wa
              (syn_wral n (syn_cnnc) (.imp (.classMem (.cv n) X) (.classMem (.cv n) Y)))
              (syn_wral n (syn_cnnc) (.imp (.classMem (.cv n) Y)
                  (.classMem (syn_cplc (.cv n) (syn_c1c)) X))))))
        (syn_wbr (.cv m) (syn_ckqrel (syn_clefin)) (.cv k)))
      (syn_w3a (syn_wa (.classMem (.cv m) (syn_cnnc)) (.classMem (.cv k) (syn_cnnc)))
        (syn_wa (.classMem (.cv m) X) (.classMem (.cv k) Y)) (syn_wa (syn_wa
            (syn_wral n (syn_cnnc) (.imp (.classMem (.cv n) X)
                (syn_wbr (.cv m) (syn_ckqrel (syn_clefin)) (.cv n)))) (syn_wral n (syn_cnnc)
              (.imp (.classMem (.cv n) Y) (syn_wbr (.cv k) (syn_ckqrel (syn_clefin)) (.cv n)))))
          (syn_wa (syn_wral n (syn_cnnc) (.imp (.classMem (.cv n) X) (.classMem (.cv n) Y)))
            (syn_wral n (syn_cnnc)
              (.imp (.classMem (.cv n) Y) (.classMem (syn_cplc (.cv n) (syn_c1c)) X))))))
      (.imp (syn_wa (syn_wbr (.cv m) (syn_ckqrel (syn_clefin)) (.cv k))
          (syn_wbr (.cv k) (syn_ckqrel (syn_clefin)) (.cv m))) (.classEq (.cv m) (.cv k)))
      p0048 p0087
  have p0089 :=
    @g_mpd
      (syn_wa (syn_w3a (syn_wa (.classMem (.cv m) (syn_cnnc)) (.classMem (.cv k) (syn_cnnc)))
          (syn_wa (.classMem (.cv m) X) (.classMem (.cv k) Y)) (syn_wa (syn_wa
              (syn_wral n (syn_cnnc) (.imp (.classMem (.cv n) X)
                  (syn_wbr (.cv m) (syn_ckqrel (syn_clefin)) (.cv n)))) (syn_wral n (syn_cnnc)
                (.imp (.classMem (.cv n) Y)
                  (syn_wbr (.cv k) (syn_ckqrel (syn_clefin)) (.cv n))))) (syn_wa
              (syn_wral n (syn_cnnc) (.imp (.classMem (.cv n) X) (.classMem (.cv n) Y)))
              (syn_wral n (syn_cnnc) (.imp (.classMem (.cv n) Y)
                  (.classMem (syn_cplc (.cv n) (syn_c1c)) X))))))
        (syn_wbr (.cv m) (syn_ckqrel (syn_clefin)) (.cv k)))
      (syn_wa (syn_wbr (.cv m) (syn_ckqrel (syn_clefin)) (.cv k))
        (syn_wbr (.cv k) (syn_ckqrel (syn_clefin)) (.cv m)))
      (.classEq (.cv m) (.cv k)) p0083 p0088
  have p0090 :=
    @g_orc (.classEq (.cv m) (.cv k)) (.classEq (.cv m) (syn_cplc (.cv k) (syn_c1c)))
  have p0091 :=
    @g_syl
      (syn_wa (syn_w3a (syn_wa (.classMem (.cv m) (syn_cnnc)) (.classMem (.cv k) (syn_cnnc)))
          (syn_wa (.classMem (.cv m) X) (.classMem (.cv k) Y)) (syn_wa (syn_wa
              (syn_wral n (syn_cnnc) (.imp (.classMem (.cv n) X)
                  (syn_wbr (.cv m) (syn_ckqrel (syn_clefin)) (.cv n)))) (syn_wral n (syn_cnnc)
                (.imp (.classMem (.cv n) Y)
                  (syn_wbr (.cv k) (syn_ckqrel (syn_clefin)) (.cv n))))) (syn_wa
              (syn_wral n (syn_cnnc) (.imp (.classMem (.cv n) X) (.classMem (.cv n) Y)))
              (syn_wral n (syn_cnnc) (.imp (.classMem (.cv n) Y)
                  (.classMem (syn_cplc (.cv n) (syn_c1c)) X))))))
        (syn_wbr (.cv m) (syn_ckqrel (syn_clefin)) (.cv k)))
      (.classEq (.cv m) (.cv k))
      (syn_wo (.classEq (.cv m) (.cv k)) (.classEq (.cv m) (syn_cplc (.cv k) (syn_c1c))))
      p0089 p0090
  have p0092 :=
    @g_ex
      (syn_w3a (syn_wa (.classMem (.cv m) (syn_cnnc)) (.classMem (.cv k) (syn_cnnc)))
        (syn_wa (.classMem (.cv m) X) (.classMem (.cv k) Y)) (syn_wa (syn_wa
            (syn_wral n (syn_cnnc) (.imp (.classMem (.cv n) X)
                (syn_wbr (.cv m) (syn_ckqrel (syn_clefin)) (.cv n)))) (syn_wral n (syn_cnnc)
              (.imp (.classMem (.cv n) Y) (syn_wbr (.cv k) (syn_ckqrel (syn_clefin)) (.cv n)))))
          (syn_wa (syn_wral n (syn_cnnc) (.imp (.classMem (.cv n) X) (.classMem (.cv n) Y)))
            (syn_wral n (syn_cnnc)
              (.imp (.classMem (.cv n) Y) (.classMem (syn_cplc (.cv n) (syn_c1c)) X))))))
      (syn_wbr (.cv m) (syn_ckqrel (syn_clefin)) (.cv k))
      (syn_wo (.classEq (.cv m) (.cv k)) (.classEq (.cv m) (syn_cplc (.cv k) (syn_c1c))))
      p0091
  have p0093 := @g_id (.classEq (.cv m) (syn_cplc (.cv k) (syn_c1c)))
  have p0094 :=
    @g_olc (.classEq (.cv m) (syn_cplc (.cv k) (syn_c1c))) (.classEq (.cv m) (.cv k))
  have p0095 :=
    @g_syl (.classEq (.cv m) (syn_cplc (.cv k) (syn_c1c)))
      (.classEq (.cv m) (syn_cplc (.cv k) (syn_c1c)))
      (syn_wo (.classEq (.cv m) (.cv k)) (.classEq (.cv m) (syn_cplc (.cv k) (syn_c1c))))
      p0093 p0094
  have p0096 :=
    @g_a1i
      (.imp (.classEq (.cv m) (syn_cplc (.cv k) (syn_c1c))) (syn_wo (.classEq (.cv m) (.cv k))
          (.classEq (.cv m) (syn_cplc (.cv k) (syn_c1c)))))
      (syn_w3a (syn_wa (.classMem (.cv m) (syn_cnnc)) (.classMem (.cv k) (syn_cnnc)))
        (syn_wa (.classMem (.cv m) X) (.classMem (.cv k) Y)) (syn_wa (syn_wa
            (syn_wral n (syn_cnnc) (.imp (.classMem (.cv n) X)
                (syn_wbr (.cv m) (syn_ckqrel (syn_clefin)) (.cv n)))) (syn_wral n (syn_cnnc)
              (.imp (.classMem (.cv n) Y) (syn_wbr (.cv k) (syn_ckqrel (syn_clefin)) (.cv n)))))
          (syn_wa (syn_wral n (syn_cnnc) (.imp (.classMem (.cv n) X) (.classMem (.cv n) Y)))
            (syn_wral n (syn_cnnc)
              (.imp (.classMem (.cv n) Y) (.classMem (syn_cplc (.cv n) (syn_c1c)) X))))))
      p0095
  have p0097 :=
    @g_jaod
      (syn_w3a (syn_wa (.classMem (.cv m) (syn_cnnc)) (.classMem (.cv k) (syn_cnnc)))
        (syn_wa (.classMem (.cv m) X) (.classMem (.cv k) Y)) (syn_wa (syn_wa
            (syn_wral n (syn_cnnc) (.imp (.classMem (.cv n) X)
                (syn_wbr (.cv m) (syn_ckqrel (syn_clefin)) (.cv n)))) (syn_wral n (syn_cnnc)
              (.imp (.classMem (.cv n) Y) (syn_wbr (.cv k) (syn_ckqrel (syn_clefin)) (.cv n)))))
          (syn_wa (syn_wral n (syn_cnnc) (.imp (.classMem (.cv n) X) (.classMem (.cv n) Y)))
            (syn_wral n (syn_cnnc)
              (.imp (.classMem (.cv n) Y) (.classMem (syn_cplc (.cv n) (syn_c1c)) X))))))
      (syn_wbr (.cv m) (syn_ckqrel (syn_clefin)) (.cv k))
      (syn_wo (.classEq (.cv m) (.cv k)) (.classEq (.cv m) (syn_cplc (.cv k) (syn_c1c))))
      (.classEq (.cv m) (syn_cplc (.cv k) (syn_c1c))) p0092 p0096
  have p0098 :=
    @g_mpd
      (syn_w3a (syn_wa (.classMem (.cv m) (syn_cnnc)) (.classMem (.cv k) (syn_cnnc)))
        (syn_wa (.classMem (.cv m) X) (.classMem (.cv k) Y)) (syn_wa (syn_wa
            (syn_wral n (syn_cnnc) (.imp (.classMem (.cv n) X)
                (syn_wbr (.cv m) (syn_ckqrel (syn_clefin)) (.cv n)))) (syn_wral n (syn_cnnc)
              (.imp (.classMem (.cv n) Y) (syn_wbr (.cv k) (syn_ckqrel (syn_clefin)) (.cv n)))))
          (syn_wa (syn_wral n (syn_cnnc) (.imp (.classMem (.cv n) X) (.classMem (.cv n) Y)))
            (syn_wral n (syn_cnnc)
              (.imp (.classMem (.cv n) Y) (.classMem (syn_cplc (.cv n) (syn_c1c)) X))))))
      (syn_wo (syn_wbr (.cv m) (syn_ckqrel (syn_clefin)) (.cv k))
        (.classEq (.cv m) (syn_cplc (.cv k) (syn_c1c))))
      (syn_wo (.classEq (.cv m) (.cv k)) (.classEq (.cv m) (syn_cplc (.cv k) (syn_c1c))))
      p0046 p0097
  exact p0098


end NFChoice.DirectNominalPrf.WPPReplay

end
