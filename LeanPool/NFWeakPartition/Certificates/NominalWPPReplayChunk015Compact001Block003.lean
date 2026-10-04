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

/-- Checked nominal proof certificate identified upstream as `g_lnqordor`. -/
@[expose]
noncomputable def gLnqordor (C : Class) (R : Class) (dv_C_R : Disjoint C.fv R.fv) :
    Nominal.NPrf
      (.imp (synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv))) (synWa
            (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
              (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))
        (synWbr (synClnqord R C) (synCstrict) (synClnquo R C))) :=
  by
  have dv_cache_0001 : Disjoint (C).fv (R).fv := by
    exact
      (show Disjoint (C).fv (R).fv from (show Disjoint (C).fv (R).fv from (by exact dv_C_R)))
  have p0000 := @gLnqordref C R dv_cache_0001
  have p0001 := @gLnqordtrans C R dv_cache_0001
  have p0002 := @gLnqordantisym C R dv_cache_0001
  have p0003 :=
    @gN3jca
      (synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv))) (synWa
          (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
            (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))
      (synWbr (synClnqord R C) (synCref) (synClnquo R C))
      (synWbr (synClnqord R C) (synCtrans) (synClnquo R C))
      (synWbr (synClnqord R C) (synCantisym) (synClnquo R C)) p0000 p0001 p0002
  have p0004 := @gPorta (synClnquo R C) (synClnqord R C)
  have p0005 :=
    @gA1i
      (synWb (synWbr (synClnqord R C) (synCpartial) (synClnquo R C))
        (synW3a (synWbr (synClnqord R C) (synCref) (synClnquo R C))
          (synWbr (synClnqord R C) (synCtrans) (synClnquo R C))
          (synWbr (synClnqord R C) (synCantisym) (synClnquo R C))))
      (synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv))) (synWa
          (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
            (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))
      p0004
  have p0006 :=
    @gMpbird
      (synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv))) (synWa
          (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
            (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))
      (synWbr (synClnqord R C) (synCpartial) (synClnquo R C))
      (synW3a (synWbr (synClnqord R C) (synCref) (synClnquo R C))
        (synWbr (synClnqord R C) (synCtrans) (synClnquo R C))
        (synWbr (synClnqord R C) (synCantisym) (synClnquo R C)))
      p0003 p0005
  have p0007 := @gLnqordconnex C R dv_cache_0001
  have p0008 :=
    @gJca
      (synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv))) (synWa
          (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
            (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))
      (synWbr (synClnqord R C) (synCpartial) (synClnquo R C))
      (synWbr (synClnqord R C) (synCconnex) (synClnquo R C)) p0006 p0007
  have p0009 := @gSopc (synClnquo R C) (synClnqord R C)
  have p0010 :=
    @gA1i
      (synWb (synWbr (synClnqord R C) (synCstrict) (synClnquo R C))
        (synWa (synWbr (synClnqord R C) (synCpartial) (synClnquo R C))
          (synWbr (synClnqord R C) (synCconnex) (synClnquo R C))))
      (synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv))) (synWa
          (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
            (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))
      p0009
  have p0011 :=
    @gMpbird
      (synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv))) (synWa
          (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
            (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))
      (synWbr (synClnqord R C) (synCstrict) (synClnquo R C))
      (synWa (synWbr (synClnqord R C) (synCpartial) (synClnquo R C))
        (synWbr (synClnqord R C) (synCconnex) (synClnquo R C)))
      p0008 p0010
  exact p0011

/-- Checked nominal proof certificate identified upstream as `g_lnkereceqb`. -/
@[expose]
noncomputable def gLnkereceqb (C : Class) (R : Class) (X : Class) (Y : Class)
    (dv_C_R : Disjoint C.fv R.fv) :
    Nominal.NPrf
      (.imp (synWa (synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv))) (synWa
              (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
                (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))
          (synWa (.classMem X C) (.classMem Y C)))
        (synWb (.classEq (synCec X (synClnker R)) (synCec Y (synClnker R)))
          (synWa (synWbr X R Y) (synWbr Y R X)))) :=
  by
  have dv_cache_0001 : Disjoint (C).fv (R).fv := by
    exact
      (show Disjoint (C).fv (R).fv from (show Disjoint (C).fv (R).fv from (by exact dv_C_R)))
  have p0000 :=
    @gSimpl
      (synWa (synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv))) (synWa
            (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
              (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))
        (synWa (.classMem X C) (.classMem Y C)))
      (.classEq (synCec X (synClnker R)) (synCec Y (synClnker R)))
  have p0001 :=
    @gSimpl
      (synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv))) (synWa
          (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
            (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))
      (synWa (.classMem X C) (.classMem Y C))
  have p0002 :=
    @gSimpr (synWa (.classMem R (synCvv)) (.classMem C (synCvv)))
      (synWa (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
          (synWbr R (synCconnex) C)) (synWss R (synCxp C C)))
  have p0003 :=
    @gSimpl
      (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
        (synWbr R (synCconnex) C))
      (synWss R (synCxp C C))
  have p0004 :=
    @gSyl
      (synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv))) (synWa
          (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
            (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))
      (synWa (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
          (synWbr R (synCconnex) C)) (synWss R (synCxp C C)))
      (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
        (synWbr R (synCconnex) C))
      p0002 p0003
  have p0005 :=
    @gSyl
      (synWa (synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv))) (synWa
            (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
              (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))
        (synWa (.classMem X C) (.classMem Y C)))
      (synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv))) (synWa
          (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
            (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))
      (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
        (synWbr R (synCconnex) C))
      p0001 p0004
  have p0006 :=
    @gSimpl (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
      (synWbr R (synCconnex) C)
  have p0007 :=
    @gSyl
      (synWa (synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv))) (synWa
            (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
              (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))
        (synWa (.classMem X C) (.classMem Y C)))
      (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
        (synWbr R (synCconnex) C))
      (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C)) p0005 p0006
  have p0008 := @gSimpl (synWbr R (synCref) C) (synWbr R (synCtrans) C)
  have p0009 :=
    @gSyl
      (synWa (synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv))) (synWa
            (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
              (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))
        (synWa (.classMem X C) (.classMem Y C)))
      (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
      (synWbr R (synCref) C) p0007 p0008
  have p0010 :=
    @gSyl
      (synWa (synWa (synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv))) (synWa
              (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
                (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))
          (synWa (.classMem X C) (.classMem Y C)))
        (.classEq (synCec X (synClnker R)) (synCec Y (synClnker R))))
      (synWa (synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv))) (synWa
            (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
              (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))
        (synWa (.classMem X C) (.classMem Y C)))
      (synWbr R (synCref) C) p0000 p0009
  have p0012 :=
    @gSimpr
      (synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv))) (synWa
          (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
            (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))
      (synWa (.classMem X C) (.classMem Y C))
  have p0013 := @gSimpr (.classMem X C) (.classMem Y C)
  have p0014 :=
    @gSyl
      (synWa (synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv))) (synWa
            (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
              (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))
        (synWa (.classMem X C) (.classMem Y C)))
      (synWa (.classMem X C) (.classMem Y C)) (.classMem Y C) p0012 p0013
  have p0015 :=
    @gSyl
      (synWa (synWa (synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv))) (synWa
              (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
                (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))
          (synWa (.classMem X C) (.classMem Y C)))
        (.classEq (synCec X (synClnker R)) (synCec Y (synClnker R))))
      (synWa (synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv))) (synWa
            (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
              (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))
        (synWa (.classMem X C) (.classMem Y C)))
      (.classMem Y C) p0000 p0014
  have p0016 :=
    @gRefd
      (synWa (synWa (synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv))) (synWa
              (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
                (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))
          (synWa (.classMem X C) (.classMem Y C)))
        (.classEq (synCec X (synClnker R)) (synCec Y (synClnker R))))
      C R Y p0010 p0015
  have p0034 :=
    @gJca
      (synWa (synWa (synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv))) (synWa
              (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
                (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))
          (synWa (.classMem X C) (.classMem Y C)))
        (.classEq (synCec X (synClnker R)) (synCec Y (synClnker R))))
      (synWbr Y R Y) (synWbr Y R Y) p0016 p0016
  have p0035 := @gEllnkerecg Y Y R
  have p0036 :=
    @gA1i
      (synWb (.classMem Y (synCec Y (synClnker R))) (synWa (synWbr Y R Y) (synWbr Y R Y)))
      (synWa (synWa (synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv))) (synWa
              (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
                (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))
          (synWa (.classMem X C) (.classMem Y C)))
        (.classEq (synCec X (synClnker R)) (synCec Y (synClnker R))))
      p0035
  have p0037 :=
    @gMpbird
      (synWa (synWa (synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv))) (synWa
              (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
                (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))
          (synWa (.classMem X C) (.classMem Y C)))
        (.classEq (synCec X (synClnker R)) (synCec Y (synClnker R))))
      (.classMem Y (synCec Y (synClnker R))) (synWa (synWbr Y R Y) (synWbr Y R Y))
      p0034 p0036
  have p0038 :=
    @gSimpr
      (synWa (synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv))) (synWa
            (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
              (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))
        (synWa (.classMem X C) (.classMem Y C)))
      (.classEq (synCec X (synClnker R)) (synCec Y (synClnker R)))
  have p0039 :=
    @gEleq2d
      (synWa (synWa (synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv))) (synWa
              (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
                (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))
          (synWa (.classMem X C) (.classMem Y C)))
        (.classEq (synCec X (synClnker R)) (synCec Y (synClnker R))))
      (synCec X (synClnker R)) (synCec Y (synClnker R)) Y p0038
  have p0040 :=
    @gMpbird
      (synWa (synWa (synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv))) (synWa
              (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
                (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))
          (synWa (.classMem X C) (.classMem Y C)))
        (.classEq (synCec X (synClnker R)) (synCec Y (synClnker R))))
      (.classMem Y (synCec X (synClnker R))) (.classMem Y (synCec Y (synClnker R)))
      p0037 p0039
  have p0041 := @gEllnkerecg Y X R
  have p0042 :=
    @gA1i
      (synWb (.classMem Y (synCec X (synClnker R))) (synWa (synWbr X R Y) (synWbr Y R X)))
      (synWa (synWa (synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv))) (synWa
              (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
                (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))
          (synWa (.classMem X C) (.classMem Y C)))
        (.classEq (synCec X (synClnker R)) (synCec Y (synClnker R))))
      p0041
  have p0043 :=
    @gMpbid
      (synWa (synWa (synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv))) (synWa
              (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
                (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))
          (synWa (.classMem X C) (.classMem Y C)))
        (.classEq (synCec X (synClnker R)) (synCec Y (synClnker R))))
      (.classMem Y (synCec X (synClnker R))) (synWa (synWbr X R Y) (synWbr Y R X))
      p0040 p0042
  have p0044 :=
    @gEx
      (synWa (synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv))) (synWa
            (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
              (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))
        (synWa (.classMem X C) (.classMem Y C)))
      (.classEq (synCec X (synClnker R)) (synCec Y (synClnker R)))
      (synWa (synWbr X R Y) (synWbr Y R X)) p0043
  have p0045 :=
    @gSimpl
      (synWa (synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv))) (synWa
            (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
              (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))
        (synWa (.classMem X C) (.classMem Y C)))
      (synWa (synWbr X R Y) (synWbr Y R X))
  have p0047 :=
    @gSyl
      (synWa (synWa (synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv))) (synWa
              (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
                (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))
          (synWa (.classMem X C) (.classMem Y C))) (synWa (synWbr X R Y) (synWbr Y R X)))
      (synWa (synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv))) (synWa
            (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
              (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))
        (synWa (.classMem X C) (.classMem Y C)))
      (synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv))) (synWa
          (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
            (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))
      p0045 p0001
  have p0048 := @gLnqordantisym C R dv_cache_0001
  have p0049 :=
    @gSyl
      (synWa (synWa (synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv))) (synWa
              (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
                (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))
          (synWa (.classMem X C) (.classMem Y C))) (synWa (synWbr X R Y) (synWbr Y R X)))
      (synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv))) (synWa
          (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
            (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))
      (synWbr (synClnqord R C) (synCantisym) (synClnquo R C)) p0047 p0048
  have p0052 :=
    @gSimpl (synWa (.classMem R (synCvv)) (.classMem C (synCvv)))
      (synWa (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
          (synWbr R (synCconnex) C)) (synWss R (synCxp C C)))
  have p0053 :=
    @gSyl
      (synWa (synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv))) (synWa
            (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
              (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))
        (synWa (.classMem X C) (.classMem Y C)))
      (synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv))) (synWa
          (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
            (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))
      (synWa (.classMem R (synCvv)) (.classMem C (synCvv))) p0001 p0052
  have p0054 := @gSimpl (.classMem R (synCvv)) (.classMem C (synCvv))
  have p0055 :=
    @gSyl
      (synWa (synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv))) (synWa
            (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
              (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))
        (synWa (.classMem X C) (.classMem Y C)))
      (synWa (.classMem R (synCvv)) (.classMem C (synCvv))) (.classMem R (synCvv))
      p0053 p0054
  have p0056 := @gLnkerexg R
  have p0057 :=
    @gSyl
      (synWa (synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv))) (synWa
            (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
              (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))
        (synWa (.classMem X C) (.classMem Y C)))
      (.classMem R (synCvv)) (.classMem (synClnker R) (synCvv)) p0055 p0056
  have p0059 := @gSimpl (.classMem X C) (.classMem Y C)
  have p0060 :=
    @gSyl
      (synWa (synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv))) (synWa
            (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
              (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))
        (synWa (.classMem X C) (.classMem Y C)))
      (synWa (.classMem X C) (.classMem Y C)) (.classMem X C) p0012 p0059
  have p0061 :=
    @gJca
      (synWa (synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv))) (synWa
            (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
              (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))
        (synWa (.classMem X C) (.classMem Y C)))
      (.classMem (synClnker R) (synCvv)) (.classMem X C) p0057 p0060
  have p0062 := @gEcelqsg C X (synClnker R) (synCvv)
  have p0063 :=
    @gSyl
      (synWa (synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv))) (synWa
            (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
              (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))
        (synWa (.classMem X C) (.classMem Y C)))
      (synWa (.classMem (synClnker R) (synCvv)) (.classMem X C))
      (.classMem (synCec X (synClnker R)) (synCqs C (synClnker R))) p0061 p0062
  have p0064 := (Nominal.classEqRefl (synClnquo R C))
  have p0065 :=
    @gSyl6eleqr
      (synWa (synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv))) (synWa
            (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
              (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))
        (synWa (.classMem X C) (.classMem Y C)))
      (synCec X (synClnker R)) (synCqs C (synClnker R)) (synClnquo R C) p0063 p0064
  have p0066 :=
    @gSyl
      (synWa (synWa (synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv))) (synWa
              (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
                (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))
          (synWa (.classMem X C) (.classMem Y C))) (synWa (synWbr X R Y) (synWbr Y R X)))
      (synWa (synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv))) (synWa
            (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
              (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))
        (synWa (.classMem X C) (.classMem Y C)))
      (.classMem (synCec X (synClnker R)) (synClnquo R C)) p0045 p0065
  have p0078 :=
    @gJca
      (synWa (synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv))) (synWa
            (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
              (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))
        (synWa (.classMem X C) (.classMem Y C)))
      (.classMem (synClnker R) (synCvv)) (.classMem Y C) p0057 p0014
  have p0079 := @gEcelqsg C Y (synClnker R) (synCvv)
  have p0080 :=
    @gSyl
      (synWa (synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv))) (synWa
            (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
              (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))
        (synWa (.classMem X C) (.classMem Y C)))
      (synWa (.classMem (synClnker R) (synCvv)) (.classMem Y C))
      (.classMem (synCec Y (synClnker R)) (synCqs C (synClnker R))) p0078 p0079
  have p0082 :=
    @gSyl6eleqr
      (synWa (synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv))) (synWa
            (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
              (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))
        (synWa (.classMem X C) (.classMem Y C)))
      (synCec Y (synClnker R)) (synCqs C (synClnker R)) (synClnquo R C) p0080 p0064
  have p0083 :=
    @gSyl
      (synWa (synWa (synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv))) (synWa
              (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
                (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))
          (synWa (.classMem X C) (.classMem Y C))) (synWa (synWbr X R Y) (synWbr Y R X)))
      (synWa (synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv))) (synWa
            (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
              (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))
        (synWa (.classMem X C) (.classMem Y C)))
      (.classMem (synCec Y (synClnker R)) (synClnquo R C)) p0045 p0082
  have p0084 :=
    @gSimpr
      (synWa (synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv))) (synWa
            (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
              (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))
        (synWa (.classMem X C) (.classMem Y C)))
      (synWa (synWbr X R Y) (synWbr Y R X))
  have p0085 := @gSimpl (synWbr X R Y) (synWbr Y R X)
  have p0086 :=
    @gSyl
      (synWa (synWa (synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv))) (synWa
              (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
                (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))
          (synWa (.classMem X C) (.classMem Y C))) (synWa (synWbr X R Y) (synWbr Y R X)))
      (synWa (synWbr X R Y) (synWbr Y R X)) (synWbr X R Y) p0084 p0085
  have p0102 :=
    @gSimpr
      (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
        (synWbr R (synCconnex) C))
      (synWss R (synCxp C C))
  have p0103 :=
    @gSyl
      (synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv))) (synWa
          (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
            (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))
      (synWa (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
          (synWbr R (synCconnex) C)) (synWss R (synCxp C C)))
      (synWss R (synCxp C C)) p0002 p0102
  have p0104 :=
    @gSyl
      (synWa (synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv))) (synWa
            (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
              (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))
        (synWa (.classMem X C) (.classMem Y C)))
      (synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv))) (synWa
          (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
            (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))
      (synWss R (synCxp C C)) p0001 p0103
  have p0105 :=
    @gJca
      (synWa (synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv))) (synWa
            (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
              (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))
        (synWa (.classMem X C) (.classMem Y C)))
      (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
      (synWss R (synCxp C C)) p0007 p0104
  have p0107 :=
    @gJca
      (synWa (synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv))) (synWa
            (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
              (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))
        (synWa (.classMem X C) (.classMem Y C)))
      (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
        (synWss R (synCxp C C)))
      (synWa (.classMem X C) (.classMem Y C)) p0105 p0012
  have p0108 :=
    @gJca
      (synWa (synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv))) (synWa
            (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
              (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))
        (synWa (.classMem X C) (.classMem Y C)))
      (.classMem R (synCvv))
      (synWa (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
          (synWss R (synCxp C C))) (synWa (.classMem X C) (.classMem Y C)))
      p0055 p0107
  have p0109 := @gBrlnqordkern C R X Y dv_cache_0001
  have p0110 :=
    @gSyl
      (synWa (synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv))) (synWa
            (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
              (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))
        (synWa (.classMem X C) (.classMem Y C)))
      (synWa (.classMem R (synCvv)) (synWa
          (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
            (synWss R (synCxp C C))) (synWa (.classMem X C) (.classMem Y C))))
      (synWb (synWbr (synCec X (synClnker R)) (synClnqord R C) (synCec Y (synClnker R)))
        (synWbr X R Y))
      p0108 p0109
  have p0111 :=
    @gSyl
      (synWa (synWa (synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv))) (synWa
              (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
                (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))
          (synWa (.classMem X C) (.classMem Y C))) (synWa (synWbr X R Y) (synWbr Y R X)))
      (synWa (synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv))) (synWa
            (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
              (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))
        (synWa (.classMem X C) (.classMem Y C)))
      (synWb (synWbr (synCec X (synClnker R)) (synClnqord R C) (synCec Y (synClnker R)))
        (synWbr X R Y))
      p0045 p0110
  have p0112 :=
    @gMpbird
      (synWa (synWa (synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv))) (synWa
              (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
                (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))
          (synWa (.classMem X C) (.classMem Y C))) (synWa (synWbr X R Y) (synWbr Y R X)))
      (synWbr (synCec X (synClnker R)) (synClnqord R C) (synCec Y (synClnker R)))
      (synWbr X R Y) p0086 p0111
  have p0114 := @gSimpr (synWbr X R Y) (synWbr Y R X)
  have p0115 :=
    @gSyl
      (synWa (synWa (synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv))) (synWa
              (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
                (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))
          (synWa (.classMem X C) (.classMem Y C))) (synWa (synWbr X R Y) (synWbr Y R X)))
      (synWa (synWbr X R Y) (synWbr Y R X)) (synWbr Y R X) p0084 p0114
  have p0141 :=
    @gJca
      (synWa (synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv))) (synWa
            (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
              (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))
        (synWa (.classMem X C) (.classMem Y C)))
      (.classMem Y C) (.classMem X C) p0014 p0060
  have p0142 :=
    @gJca
      (synWa (synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv))) (synWa
            (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
              (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))
        (synWa (.classMem X C) (.classMem Y C)))
      (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
        (synWss R (synCxp C C)))
      (synWa (.classMem Y C) (.classMem X C)) p0105 p0141
  have p0143 :=
    @gJca
      (synWa (synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv))) (synWa
            (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
              (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))
        (synWa (.classMem X C) (.classMem Y C)))
      (.classMem R (synCvv))
      (synWa (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
          (synWss R (synCxp C C))) (synWa (.classMem Y C) (.classMem X C)))
      p0055 p0142
  have p0144 := @gBrlnqordkern C R Y X dv_cache_0001
  have p0145 :=
    @gSyl
      (synWa (synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv))) (synWa
            (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
              (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))
        (synWa (.classMem X C) (.classMem Y C)))
      (synWa (.classMem R (synCvv)) (synWa
          (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
            (synWss R (synCxp C C))) (synWa (.classMem Y C) (.classMem X C))))
      (synWb (synWbr (synCec Y (synClnker R)) (synClnqord R C) (synCec X (synClnker R)))
        (synWbr Y R X))
      p0143 p0144
  have p0146 :=
    @gSyl
      (synWa (synWa (synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv))) (synWa
              (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
                (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))
          (synWa (.classMem X C) (.classMem Y C))) (synWa (synWbr X R Y) (synWbr Y R X)))
      (synWa (synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv))) (synWa
            (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
              (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))
        (synWa (.classMem X C) (.classMem Y C)))
      (synWb (synWbr (synCec Y (synClnker R)) (synClnqord R C) (synCec X (synClnker R)))
        (synWbr Y R X))
      p0045 p0145
  have p0147 :=
    @gMpbird
      (synWa (synWa (synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv))) (synWa
              (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
                (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))
          (synWa (.classMem X C) (.classMem Y C))) (synWa (synWbr X R Y) (synWbr Y R X)))
      (synWbr (synCec Y (synClnker R)) (synClnqord R C) (synCec X (synClnker R)))
      (synWbr Y R X) p0115 p0146
  have p0148 :=
    @gAntid
      (synWa (synWa (synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv))) (synWa
              (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
                (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))
          (synWa (.classMem X C) (.classMem Y C))) (synWa (synWbr X R Y) (synWbr Y R X)))
      (synClnquo R C) (synClnqord R C) (synCec X (synClnker R))
      (synCec Y (synClnker R)) p0049 p0066 p0083 p0112 p0147
  have p0149 :=
    @gEx
      (synWa (synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv))) (synWa
            (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
              (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))
        (synWa (.classMem X C) (.classMem Y C)))
      (synWa (synWbr X R Y) (synWbr Y R X))
      (.classEq (synCec X (synClnker R)) (synCec Y (synClnker R))) p0148
  have p0150 :=
    @gImpbid
      (synWa (synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv))) (synWa
            (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
              (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))
        (synWa (.classMem X C) (.classMem Y C)))
      (.classEq (synCec X (synClnker R)) (synCec Y (synClnker R)))
      (synWa (synWbr X R Y) (synWbr Y R X)) p0044 p0149
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

/-- Checked nominal proof certificate identified upstream as `g_brlnqordstrict`. -/
@[expose]
noncomputable def gBrlnqordstrict (C : Class) (R : Class) (X : Class) (Y : Class)
    (dv_C_R : Disjoint C.fv R.fv) :
    Nominal.NPrf
      (.imp (synWa (synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv))) (synWa
              (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
                (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))
          (synWa (.classMem X C) (.classMem Y C))) (synWb
          (synWbr (synCec X (synClnker R)) (synCdif (synClnqord R C) (synCid))
            (synCec Y (synClnker R))) (synWbr X (synCdif R (synCcnv R)) Y))) :=
  by
  have dv_cache_0001 : Disjoint (C).fv (R).fv := by
    exact
      (show Disjoint (C).fv (R).fv from (show Disjoint (C).fv (R).fv from (by exact dv_C_R)))
  have p0000 :=
    @gBrdif (synCec X (synClnker R)) (synCec Y (synClnker R)) (synClnqord R C)
      (synCid)
  have p0001 :=
    @gA1i
      (synWb (synWbr (synCec X (synClnker R)) (synCdif (synClnqord R C) (synCid))
          (synCec Y (synClnker R))) (synWa
          (synWbr (synCec X (synClnker R)) (synClnqord R C) (synCec Y (synClnker R)))
          (.neg (synWbr (synCec X (synClnker R)) (synCid) (synCec Y (synClnker R))))))
      (synWa (synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv))) (synWa
            (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
              (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))
        (synWa (.classMem X C) (.classMem Y C)))
      p0000
  have p0002 :=
    @gSimpl
      (synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv))) (synWa
          (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
            (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))
      (synWa (.classMem X C) (.classMem Y C))
  have p0003 :=
    @gSimpl (synWa (.classMem R (synCvv)) (.classMem C (synCvv)))
      (synWa (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
          (synWbr R (synCconnex) C)) (synWss R (synCxp C C)))
  have p0004 :=
    @gSyl
      (synWa (synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv))) (synWa
            (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
              (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))
        (synWa (.classMem X C) (.classMem Y C)))
      (synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv))) (synWa
          (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
            (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))
      (synWa (.classMem R (synCvv)) (.classMem C (synCvv))) p0002 p0003
  have p0005 := @gSimpl (.classMem R (synCvv)) (.classMem C (synCvv))
  have p0006 :=
    @gSyl
      (synWa (synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv))) (synWa
            (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
              (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))
        (synWa (.classMem X C) (.classMem Y C)))
      (synWa (.classMem R (synCvv)) (.classMem C (synCvv))) (.classMem R (synCvv))
      p0004 p0005
  have p0008 :=
    @gSimpr (synWa (.classMem R (synCvv)) (.classMem C (synCvv)))
      (synWa (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
          (synWbr R (synCconnex) C)) (synWss R (synCxp C C)))
  have p0009 :=
    @gSimpl
      (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
        (synWbr R (synCconnex) C))
      (synWss R (synCxp C C))
  have p0010 :=
    @gSyl
      (synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv))) (synWa
          (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
            (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))
      (synWa (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
          (synWbr R (synCconnex) C)) (synWss R (synCxp C C)))
      (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
        (synWbr R (synCconnex) C))
      p0008 p0009
  have p0011 :=
    @gSyl
      (synWa (synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv))) (synWa
            (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
              (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))
        (synWa (.classMem X C) (.classMem Y C)))
      (synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv))) (synWa
          (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
            (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))
      (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
        (synWbr R (synCconnex) C))
      p0002 p0010
  have p0012 :=
    @gSimpl (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
      (synWbr R (synCconnex) C)
  have p0013 :=
    @gSyl
      (synWa (synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv))) (synWa
            (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
              (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))
        (synWa (.classMem X C) (.classMem Y C)))
      (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
        (synWbr R (synCconnex) C))
      (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C)) p0011 p0012
  have p0016 :=
    @gSimpr
      (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
        (synWbr R (synCconnex) C))
      (synWss R (synCxp C C))
  have p0017 :=
    @gSyl
      (synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv))) (synWa
          (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
            (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))
      (synWa (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
          (synWbr R (synCconnex) C)) (synWss R (synCxp C C)))
      (synWss R (synCxp C C)) p0008 p0016
  have p0018 :=
    @gSyl
      (synWa (synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv))) (synWa
            (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
              (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))
        (synWa (.classMem X C) (.classMem Y C)))
      (synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv))) (synWa
          (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
            (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))
      (synWss R (synCxp C C)) p0002 p0017
  have p0019 :=
    @gJca
      (synWa (synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv))) (synWa
            (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
              (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))
        (synWa (.classMem X C) (.classMem Y C)))
      (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
      (synWss R (synCxp C C)) p0013 p0018
  have p0020 :=
    @gSimpr
      (synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv))) (synWa
          (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
            (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))
      (synWa (.classMem X C) (.classMem Y C))
  have p0021 :=
    @gJca
      (synWa (synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv))) (synWa
            (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
              (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))
        (synWa (.classMem X C) (.classMem Y C)))
      (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
        (synWss R (synCxp C C)))
      (synWa (.classMem X C) (.classMem Y C)) p0019 p0020
  have p0022 :=
    @gJca
      (synWa (synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv))) (synWa
            (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
              (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))
        (synWa (.classMem X C) (.classMem Y C)))
      (.classMem R (synCvv))
      (synWa (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
          (synWss R (synCxp C C))) (synWa (.classMem X C) (.classMem Y C)))
      p0006 p0021
  have p0023 := @gBrlnqordkern C R X Y dv_cache_0001
  have p0024 :=
    @gSyl
      (synWa (synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv))) (synWa
            (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
              (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))
        (synWa (.classMem X C) (.classMem Y C)))
      (synWa (.classMem R (synCvv)) (synWa
          (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
            (synWss R (synCxp C C))) (synWa (.classMem X C) (.classMem Y C))))
      (synWb (synWbr (synCec X (synClnker R)) (synClnqord R C) (synCec Y (synClnker R)))
        (synWbr X R Y))
      p0022 p0023
  have p0030 := @gLnkerexg R
  have p0031 :=
    @gSyl
      (synWa (synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv))) (synWa
            (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
              (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))
        (synWa (.classMem X C) (.classMem Y C)))
      (.classMem R (synCvv)) (.classMem (synClnker R) (synCvv)) p0006 p0030
  have p0032 := @gEcexg Y (synCvv) (synClnker R)
  have p0033 :=
    @gSyl
      (synWa (synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv))) (synWa
            (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
              (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))
        (synWa (.classMem X C) (.classMem Y C)))
      (.classMem (synClnker R) (synCvv))
      (.classMem (synCec Y (synClnker R)) (synCvv)) p0031 p0032
  have p0034 := @gIdeqg (synCec X (synClnker R)) (synCec Y (synClnker R)) (synCvv)
  have p0035 :=
    @gSyl
      (synWa (synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv))) (synWa
            (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
              (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))
        (synWa (.classMem X C) (.classMem Y C)))
      (.classMem (synCec Y (synClnker R)) (synCvv))
      (synWb (synWbr (synCec X (synClnker R)) (synCid) (synCec Y (synClnker R)))
        (.classEq (synCec X (synClnker R)) (synCec Y (synClnker R))))
      p0033 p0034
  have p0036 :=
    @gNotbid
      (synWa (synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv))) (synWa
            (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
              (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))
        (synWa (.classMem X C) (.classMem Y C)))
      (synWbr (synCec X (synClnker R)) (synCid) (synCec Y (synClnker R)))
      (.classEq (synCec X (synClnker R)) (synCec Y (synClnker R))) p0035
  have p0037 :=
    @gAnbi12d
      (synWa (synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv))) (synWa
            (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
              (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))
        (synWa (.classMem X C) (.classMem Y C)))
      (synWbr (synCec X (synClnker R)) (synClnqord R C) (synCec Y (synClnker R)))
      (synWbr X R Y)
      (.neg (synWbr (synCec X (synClnker R)) (synCid) (synCec Y (synClnker R))))
      (.neg (.classEq (synCec X (synClnker R)) (synCec Y (synClnker R)))) p0024 p0036
  have p0038 :=
    @gBitrd
      (synWa (synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv))) (synWa
            (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
              (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))
        (synWa (.classMem X C) (.classMem Y C)))
      (synWbr (synCec X (synClnker R)) (synCdif (synClnqord R C) (synCid))
        (synCec Y (synClnker R)))
      (synWa (synWbr (synCec X (synClnker R)) (synClnqord R C) (synCec Y (synClnker R)))
        (.neg (synWbr (synCec X (synClnker R)) (synCid) (synCec Y (synClnker R)))))
      (synWa (synWbr X R Y)
        (.neg (.classEq (synCec X (synClnker R)) (synCec Y (synClnker R)))))
      p0001 p0037
  have p0039 := @gLnkereceqb C R X Y dv_cache_0001
  have p0040 :=
    @gNotbid
      (synWa (synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv))) (synWa
            (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
              (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))
        (synWa (.classMem X C) (.classMem Y C)))
      (.classEq (synCec X (synClnker R)) (synCec Y (synClnker R)))
      (synWa (synWbr X R Y) (synWbr Y R X)) p0039
  have p0041 :=
    @gAnbi2d
      (synWa (synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv))) (synWa
            (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
              (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))
        (synWa (.classMem X C) (.classMem Y C)))
      (.neg (.classEq (synCec X (synClnker R)) (synCec Y (synClnker R))))
      (.neg (synWa (synWbr X R Y) (synWbr Y R X))) (synWbr X R Y) p0040
  have p0042 :=
    @gBitrd
      (synWa (synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv))) (synWa
            (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
              (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))
        (synWa (.classMem X C) (.classMem Y C)))
      (synWbr (synCec X (synClnker R)) (synCdif (synClnqord R C) (synCid))
        (synCec Y (synClnker R)))
      (synWa (synWbr X R Y)
        (.neg (.classEq (synCec X (synClnker R)) (synCec Y (synClnker R)))))
      (synWa (synWbr X R Y) (.neg (synWa (synWbr X R Y) (synWbr Y R X)))) p0038 p0041
  have p0043 := @gId (synWbr X R Y)
  have p0044 := @gBiantrurd (synWbr X R Y) (synWbr X R Y) (synWbr Y R X) p0043
  have p0045 :=
    @gNotbid (synWbr X R Y) (synWbr Y R X) (synWa (synWbr X R Y) (synWbr Y R X))
      p0044
  have p0046 :=
    @gPm532i (synWbr X R Y) (.neg (synWbr Y R X))
      (.neg (synWa (synWbr X R Y) (synWbr Y R X))) p0045
  have p0047 :=
    @gBicomi (synWa (synWbr X R Y) (.neg (synWbr Y R X)))
      (synWa (synWbr X R Y) (.neg (synWa (synWbr X R Y) (synWbr Y R X)))) p0046
  have p0048 :=
    @gA1i
      (synWb (synWa (synWbr X R Y) (.neg (synWa (synWbr X R Y) (synWbr Y R X))))
        (synWa (synWbr X R Y) (.neg (synWbr Y R X))))
      (synWa (synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv))) (synWa
            (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
              (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))
        (synWa (.classMem X C) (.classMem Y C)))
      p0047
  have p0049 :=
    @gBitrd
      (synWa (synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv))) (synWa
            (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
              (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))
        (synWa (.classMem X C) (.classMem Y C)))
      (synWbr (synCec X (synClnker R)) (synCdif (synClnqord R C) (synCid))
        (synCec Y (synClnker R)))
      (synWa (synWbr X R Y) (.neg (synWa (synWbr X R Y) (synWbr Y R X))))
      (synWa (synWbr X R Y) (.neg (synWbr Y R X))) p0042 p0048
  have p0050 := @gBrdif X Y R (synCcnv R)
  have p0051 := @gBrcnv X Y R
  have p0052 := @gNotbii (synWbr X (synCcnv R) Y) (synWbr Y R X) p0051
  have p0053 :=
    @gAnbi2i (.neg (synWbr X (synCcnv R) Y)) (.neg (synWbr Y R X)) (synWbr X R Y)
      p0052
  have p0054 :=
    @gBitri (synWbr X (synCdif R (synCcnv R)) Y)
      (synWa (synWbr X R Y) (.neg (synWbr X (synCcnv R) Y)))
      (synWa (synWbr X R Y) (.neg (synWbr Y R X))) p0050 p0053
  have p0055 :=
    @gA1i
      (synWb (synWbr X (synCdif R (synCcnv R)) Y)
        (synWa (synWbr X R Y) (.neg (synWbr Y R X))))
      (synWa (synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv))) (synWa
            (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
              (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))
        (synWa (.classMem X C) (.classMem Y C)))
      p0054
  have p0056 :=
    @gBitr4d
      (synWa (synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv))) (synWa
            (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
              (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))
        (synWa (.classMem X C) (.classMem Y C)))
      (synWbr (synCec X (synClnker R)) (synCdif (synClnqord R C) (synCid))
        (synCec Y (synClnker R)))
      (synWa (synWbr X R Y) (.neg (synWbr Y R X)))
      (synWbr X (synCdif R (synCcnv R)) Y) p0049 p0055
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

/-- Checked nominal proof certificate identified upstream as `g_lnquounionb`. -/
@[expose]
noncomputable def gLnquounionb (u : Var) (C : Class) (R : Class) (S : Class)
    (dv_C_R : Disjoint C.fv R.fv) :
    Nominal.NPrf
      (.imp (synWa (synWa (synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv)))
              (synWa (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
                  (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))
            (synWss S (synClnquo R C))) (.classMem (.cv u) C))
        (synWb (.classMem (.cv u) (synCuni S))
          (.classMem (synCec (.cv u) (synClnker R)) S))) :=
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
  have dv_cache_0009 : w ∉ ((Wff.classMem (synCec (.cv u) (synClnker R)) S)).fv :=
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
      ((synWa (synWa (synWa (synWa
                (synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv))) (synWa
                    (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
                      (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))
                (synWss S (synClnquo R C))) (.classMem (.cv u) C))
            (.classMem (.cv u) (synCuni S)))
          (synWa (.classMem (.cv b) S) (.classMem (.cv u) (.cv b))))).fv :=
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
  have dv_cache_0011 : b ∉ ((Wff.classMem (synCec (.cv u) (synClnker R)) S)).fv :=
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
      ((synWa (synWa (synWa (synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv)))
                (synWa (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
                    (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))
              (synWss S (synClnquo R C))) (.classMem (.cv u) C))
          (.classMem (.cv u) (synCuni S)))).fv :=
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
    @gSimpr
      (synWa (synWa (synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv))) (synWa
              (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
                (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))
          (synWss S (synClnquo R C))) (.classMem (.cv u) C))
      (.classMem (.cv u) (synCuni S))
  have p0001 := @gEluni2 b (.cv u) S dv_cache_0001 dv_cache_0002
  have p0002 :=
    @gBiimpi (.classMem (.cv u) (synCuni S)) (synWrex b S (.classMem (.cv u) (.cv b)))
      p0001
  have p0003 :=
    @gSyl
      (synWa (synWa (synWa (synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv)))
              (synWa (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
                  (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))
            (synWss S (synClnquo R C))) (.classMem (.cv u) C))
        (.classMem (.cv u) (synCuni S)))
      (.classMem (.cv u) (synCuni S)) (synWrex b S (.classMem (.cv u) (.cv b))) p0000
      p0002
  have p0004 :=
    @gSimpl
      (synWa (synWa (synWa (synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv)))
              (synWa (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
                  (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))
            (synWss S (synClnquo R C))) (.classMem (.cv u) C))
        (.classMem (.cv u) (synCuni S)))
      (synWa (.classMem (.cv b) S) (.classMem (.cv u) (.cv b)))
  have p0005 :=
    @gSimpl
      (synWa (synWa (synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv))) (synWa
              (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
                (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))
          (synWss S (synClnquo R C))) (.classMem (.cv u) C))
      (.classMem (.cv u) (synCuni S))
  have p0006 :=
    @gSyl
      (synWa (synWa (synWa (synWa
              (synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv))) (synWa
                  (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
                    (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))
              (synWss S (synClnquo R C))) (.classMem (.cv u) C))
          (.classMem (.cv u) (synCuni S)))
        (synWa (.classMem (.cv b) S) (.classMem (.cv u) (.cv b))))
      (synWa (synWa (synWa (synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv)))
              (synWa (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
                  (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))
            (synWss S (synClnquo R C))) (.classMem (.cv u) C))
        (.classMem (.cv u) (synCuni S)))
      (synWa (synWa (synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv))) (synWa
              (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
                (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))
          (synWss S (synClnquo R C))) (.classMem (.cv u) C))
      p0004 p0005
  have p0007 :=
    @gSimpl
      (synWa (synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv))) (synWa
            (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
              (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))
        (synWss S (synClnquo R C)))
      (.classMem (.cv u) C)
  have p0008 :=
    @gSimpr
      (synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv))) (synWa
          (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
            (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))
      (synWss S (synClnquo R C))
  have p0009 :=
    @gSyl
      (synWa (synWa (synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv))) (synWa
              (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
                (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))
          (synWss S (synClnquo R C))) (.classMem (.cv u) C))
      (synWa (synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv))) (synWa
            (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
              (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))
        (synWss S (synClnquo R C)))
      (synWss S (synClnquo R C)) p0007 p0008
  have p0010 :=
    @gSyl
      (synWa (synWa (synWa (synWa
              (synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv))) (synWa
                  (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
                    (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))
              (synWss S (synClnquo R C))) (.classMem (.cv u) C))
          (.classMem (.cv u) (synCuni S)))
        (synWa (.classMem (.cv b) S) (.classMem (.cv u) (.cv b))))
      (synWa (synWa (synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv))) (synWa
              (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
                (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))
          (synWss S (synClnquo R C))) (.classMem (.cv u) C))
      (synWss S (synClnquo R C)) p0006 p0009
  have p0011 :=
    @gSimpr
      (synWa (synWa (synWa (synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv)))
              (synWa (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
                  (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))
            (synWss S (synClnquo R C))) (.classMem (.cv u) C))
        (.classMem (.cv u) (synCuni S)))
      (synWa (.classMem (.cv b) S) (.classMem (.cv u) (.cv b)))
  have p0012 := @gSimpl (.classMem (.cv b) S) (.classMem (.cv u) (.cv b))
  have p0013 :=
    @gSyl
      (synWa (synWa (synWa (synWa
              (synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv))) (synWa
                  (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
                    (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))
              (synWss S (synClnquo R C))) (.classMem (.cv u) C))
          (.classMem (.cv u) (synCuni S)))
        (synWa (.classMem (.cv b) S) (.classMem (.cv u) (.cv b))))
      (synWa (.classMem (.cv b) S) (.classMem (.cv u) (.cv b))) (.classMem (.cv b) S)
      p0011 p0012
  have p0014 :=
    @gSseldd
      (synWa (synWa (synWa (synWa
              (synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv))) (synWa
                  (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
                    (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))
              (synWss S (synClnquo R C))) (.classMem (.cv u) C))
          (.classMem (.cv u) (synCuni S)))
        (synWa (.classMem (.cv b) S) (.classMem (.cv u) (.cv b))))
      S (synClnquo R C) (.cv b) p0010 p0013
  have p0015 := @gVex b
  have p0016 :=
    @gEllnquo w C (.cv b) R dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006
      dv_cache_0007 dv_cache_0008 p0015
  have p0017 :=
    @gA1i
      (synWb (.classMem (.cv b) (synClnquo R C))
        (synWrex w C (.classEq (.cv b) (synCec (.cv w) (synClnker R)))))
      (synWa (synWa (synWa (synWa
              (synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv))) (synWa
                  (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
                    (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))
              (synWss S (synClnquo R C))) (.classMem (.cv u) C))
          (.classMem (.cv u) (synCuni S)))
        (synWa (.classMem (.cv b) S) (.classMem (.cv u) (.cv b))))
      p0016
  have p0018 :=
    @gMpbid
      (synWa (synWa (synWa (synWa
              (synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv))) (synWa
                  (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
                    (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))
              (synWss S (synClnquo R C))) (.classMem (.cv u) C))
          (.classMem (.cv u) (synCuni S)))
        (synWa (.classMem (.cv b) S) (.classMem (.cv u) (.cv b))))
      (.classMem (.cv b) (synClnquo R C))
      (synWrex w C (.classEq (.cv b) (synCec (.cv w) (synClnker R)))) p0014 p0017
  have p0019 :=
    @gSimpr
      (synWa (synWa (synWa (synWa
              (synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv))) (synWa
                  (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
                    (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))
              (synWss S (synClnquo R C))) (.classMem (.cv u) C))
          (.classMem (.cv u) (synCuni S)))
        (synWa (.classMem (.cv b) S) (.classMem (.cv u) (.cv b))))
      (synWa (.classMem (.cv w) C) (.classEq (.cv b) (synCec (.cv w) (synClnker R))))
  have p0020 :=
    @gSimpr (.classMem (.cv w) C) (.classEq (.cv b) (synCec (.cv w) (synClnker R)))
  have p0021 :=
    @gSyl
      (synWa (synWa (synWa (synWa (synWa
                (synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv))) (synWa
                    (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
                      (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))
                (synWss S (synClnquo R C))) (.classMem (.cv u) C))
            (.classMem (.cv u) (synCuni S)))
          (synWa (.classMem (.cv b) S) (.classMem (.cv u) (.cv b))))
        (synWa (.classMem (.cv w) C) (.classEq (.cv b) (synCec (.cv w) (synClnker R)))))
      (synWa (.classMem (.cv w) C) (.classEq (.cv b) (synCec (.cv w) (synClnker R))))
      (.classEq (.cv b) (synCec (.cv w) (synClnker R))) p0019 p0020
  have p0022 :=
    @gSimpl
      (synWa (synWa (synWa (synWa
              (synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv))) (synWa
                  (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
                    (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))
              (synWss S (synClnquo R C))) (.classMem (.cv u) C))
          (.classMem (.cv u) (synCuni S)))
        (synWa (.classMem (.cv b) S) (.classMem (.cv u) (.cv b))))
      (synWa (.classMem (.cv w) C) (.classEq (.cv b) (synCec (.cv w) (synClnker R))))
  have p0024 := @gSimpr (.classMem (.cv b) S) (.classMem (.cv u) (.cv b))
  have p0025 :=
    @gSyl
      (synWa (synWa (synWa (synWa
              (synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv))) (synWa
                  (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
                    (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))
              (synWss S (synClnquo R C))) (.classMem (.cv u) C))
          (.classMem (.cv u) (synCuni S)))
        (synWa (.classMem (.cv b) S) (.classMem (.cv u) (.cv b))))
      (synWa (.classMem (.cv b) S) (.classMem (.cv u) (.cv b)))
      (.classMem (.cv u) (.cv b)) p0011 p0024
  have p0026 :=
    @gSyl
      (synWa (synWa (synWa (synWa (synWa
                (synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv))) (synWa
                    (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
                      (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))
                (synWss S (synClnquo R C))) (.classMem (.cv u) C))
            (.classMem (.cv u) (synCuni S)))
          (synWa (.classMem (.cv b) S) (.classMem (.cv u) (.cv b))))
        (synWa (.classMem (.cv w) C) (.classEq (.cv b) (synCec (.cv w) (synClnker R)))))
      (synWa (synWa (synWa (synWa
              (synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv))) (synWa
                  (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
                    (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))
              (synWss S (synClnquo R C))) (.classMem (.cv u) C))
          (.classMem (.cv u) (synCuni S)))
        (synWa (.classMem (.cv b) S) (.classMem (.cv u) (.cv b))))
      (.classMem (.cv u) (.cv b)) p0022 p0025
  have p0030 :=
    @gEleq2d
      (synWa (synWa (synWa (synWa (synWa
                (synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv))) (synWa
                    (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
                      (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))
                (synWss S (synClnquo R C))) (.classMem (.cv u) C))
            (.classMem (.cv u) (synCuni S)))
          (synWa (.classMem (.cv b) S) (.classMem (.cv u) (.cv b))))
        (synWa (.classMem (.cv w) C) (.classEq (.cv b) (synCec (.cv w) (synClnker R)))))
      (.cv b) (synCec (.cv w) (synClnker R)) (.cv u) p0021
  have p0031 :=
    @gMpbid
      (synWa (synWa (synWa (synWa (synWa
                (synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv))) (synWa
                    (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
                      (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))
                (synWss S (synClnquo R C))) (.classMem (.cv u) C))
            (.classMem (.cv u) (synCuni S)))
          (synWa (.classMem (.cv b) S) (.classMem (.cv u) (.cv b))))
        (synWa (.classMem (.cv w) C) (.classEq (.cv b) (synCec (.cv w) (synClnker R)))))
      (.classMem (.cv u) (.cv b)) (.classMem (.cv u) (synCec (.cv w) (synClnker R)))
      p0026 p0030
  have p0032 := @gEllnkerecg (.cv u) (.cv w) R
  have p0033 :=
    @gA1i
      (synWb (.classMem (.cv u) (synCec (.cv w) (synClnker R)))
        (synWa (synWbr (.cv w) R (.cv u)) (synWbr (.cv u) R (.cv w))))
      (synWa (synWa (synWa (synWa (synWa
                (synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv))) (synWa
                    (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
                      (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))
                (synWss S (synClnquo R C))) (.classMem (.cv u) C))
            (.classMem (.cv u) (synCuni S)))
          (synWa (.classMem (.cv b) S) (.classMem (.cv u) (.cv b))))
        (synWa (.classMem (.cv w) C) (.classEq (.cv b) (synCec (.cv w) (synClnker R)))))
      p0032
  have p0034 :=
    @gMpbid
      (synWa (synWa (synWa (synWa (synWa
                (synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv))) (synWa
                    (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
                      (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))
                (synWss S (synClnquo R C))) (.classMem (.cv u) C))
            (.classMem (.cv u) (synCuni S)))
          (synWa (.classMem (.cv b) S) (.classMem (.cv u) (.cv b))))
        (synWa (.classMem (.cv w) C) (.classEq (.cv b) (synCec (.cv w) (synClnker R)))))
      (.classMem (.cv u) (synCec (.cv w) (synClnker R)))
      (synWa (synWbr (.cv w) R (.cv u)) (synWbr (.cv u) R (.cv w))) p0031 p0033
  have p0039 :=
    @gSyl
      (synWa (synWa (synWa (synWa (synWa
                (synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv))) (synWa
                    (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
                      (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))
                (synWss S (synClnquo R C))) (.classMem (.cv u) C))
            (.classMem (.cv u) (synCuni S)))
          (synWa (.classMem (.cv b) S) (.classMem (.cv u) (.cv b))))
        (synWa (.classMem (.cv w) C) (.classEq (.cv b) (synCec (.cv w) (synClnker R)))))
      (synWa (synWa (synWa (synWa
              (synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv))) (synWa
                  (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
                    (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))
              (synWss S (synClnquo R C))) (.classMem (.cv u) C))
          (.classMem (.cv u) (synCuni S)))
        (synWa (.classMem (.cv b) S) (.classMem (.cv u) (.cv b))))
      (synWa (synWa (synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv))) (synWa
              (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
                (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))
          (synWss S (synClnquo R C))) (.classMem (.cv u) C))
      p0022 p0006
  have p0041 :=
    @gSimpl
      (synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv))) (synWa
          (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
            (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))
      (synWss S (synClnquo R C))
  have p0042 :=
    @gSyl
      (synWa (synWa (synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv))) (synWa
              (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
                (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))
          (synWss S (synClnquo R C))) (.classMem (.cv u) C))
      (synWa (synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv))) (synWa
            (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
              (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))
        (synWss S (synClnquo R C)))
      (synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv))) (synWa
          (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
            (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))
      p0007 p0041
  have p0043 :=
    @gSyl
      (synWa (synWa (synWa (synWa (synWa
                (synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv))) (synWa
                    (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
                      (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))
                (synWss S (synClnquo R C))) (.classMem (.cv u) C))
            (.classMem (.cv u) (synCuni S)))
          (synWa (.classMem (.cv b) S) (.classMem (.cv u) (.cv b))))
        (synWa (.classMem (.cv w) C) (.classEq (.cv b) (synCec (.cv w) (synClnker R)))))
      (synWa (synWa (synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv))) (synWa
              (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
                (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))
          (synWss S (synClnquo R C))) (.classMem (.cv u) C))
      (synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv))) (synWa
          (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
            (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))
      p0039 p0042
  have p0045 :=
    @gSimpl (.classMem (.cv w) C) (.classEq (.cv b) (synCec (.cv w) (synClnker R)))
  have p0046 :=
    @gSyl
      (synWa (synWa (synWa (synWa (synWa
                (synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv))) (synWa
                    (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
                      (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))
                (synWss S (synClnquo R C))) (.classMem (.cv u) C))
            (.classMem (.cv u) (synCuni S)))
          (synWa (.classMem (.cv b) S) (.classMem (.cv u) (.cv b))))
        (synWa (.classMem (.cv w) C) (.classEq (.cv b) (synCec (.cv w) (synClnker R)))))
      (synWa (.classMem (.cv w) C) (.classEq (.cv b) (synCec (.cv w) (synClnker R))))
      (.classMem (.cv w) C) p0019 p0045
  have p0052 :=
    @gSimpr
      (synWa (synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv))) (synWa
            (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
              (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))
        (synWss S (synClnquo R C)))
      (.classMem (.cv u) C)
  have p0053 :=
    @gSyl
      (synWa (synWa (synWa (synWa (synWa
                (synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv))) (synWa
                    (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
                      (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))
                (synWss S (synClnquo R C))) (.classMem (.cv u) C))
            (.classMem (.cv u) (synCuni S)))
          (synWa (.classMem (.cv b) S) (.classMem (.cv u) (.cv b))))
        (synWa (.classMem (.cv w) C) (.classEq (.cv b) (synCec (.cv w) (synClnker R)))))
      (synWa (synWa (synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv))) (synWa
              (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
                (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))
          (synWss S (synClnquo R C))) (.classMem (.cv u) C))
      (.classMem (.cv u) C) p0039 p0052
  have p0054 :=
    @gJca
      (synWa (synWa (synWa (synWa (synWa
                (synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv))) (synWa
                    (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
                      (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))
                (synWss S (synClnquo R C))) (.classMem (.cv u) C))
            (.classMem (.cv u) (synCuni S)))
          (synWa (.classMem (.cv b) S) (.classMem (.cv u) (.cv b))))
        (synWa (.classMem (.cv w) C) (.classEq (.cv b) (synCec (.cv w) (synClnker R)))))
      (.classMem (.cv w) C) (.classMem (.cv u) C) p0046 p0053
  have p0055 :=
    @gJca
      (synWa (synWa (synWa (synWa (synWa
                (synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv))) (synWa
                    (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
                      (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))
                (synWss S (synClnquo R C))) (.classMem (.cv u) C))
            (.classMem (.cv u) (synCuni S)))
          (synWa (.classMem (.cv b) S) (.classMem (.cv u) (.cv b))))
        (synWa (.classMem (.cv w) C) (.classEq (.cv b) (synCec (.cv w) (synClnker R)))))
      (synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv))) (synWa
          (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
            (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))
      (synWa (.classMem (.cv w) C) (.classMem (.cv u) C)) p0043 p0054
  have p0056 := @gLnkereceqb C R (.cv w) (.cv u) dv_cache_0004
  have p0057 :=
    @gSyl
      (synWa (synWa (synWa (synWa (synWa
                (synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv))) (synWa
                    (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
                      (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))
                (synWss S (synClnquo R C))) (.classMem (.cv u) C))
            (.classMem (.cv u) (synCuni S)))
          (synWa (.classMem (.cv b) S) (.classMem (.cv u) (.cv b))))
        (synWa (.classMem (.cv w) C) (.classEq (.cv b) (synCec (.cv w) (synClnker R)))))
      (synWa (synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv))) (synWa
            (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
              (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))
        (synWa (.classMem (.cv w) C) (.classMem (.cv u) C)))
      (synWb (.classEq (synCec (.cv w) (synClnker R)) (synCec (.cv u) (synClnker R)))
        (synWa (synWbr (.cv w) R (.cv u)) (synWbr (.cv u) R (.cv w))))
      p0055 p0056
  have p0058 :=
    @gMpbird
      (synWa (synWa (synWa (synWa (synWa
                (synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv))) (synWa
                    (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
                      (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))
                (synWss S (synClnquo R C))) (.classMem (.cv u) C))
            (.classMem (.cv u) (synCuni S)))
          (synWa (.classMem (.cv b) S) (.classMem (.cv u) (.cv b))))
        (synWa (.classMem (.cv w) C) (.classEq (.cv b) (synCec (.cv w) (synClnker R)))))
      (.classEq (synCec (.cv w) (synClnker R)) (synCec (.cv u) (synClnker R)))
      (synWa (synWbr (.cv w) R (.cv u)) (synWbr (.cv u) R (.cv w))) p0034 p0057
  have p0059 :=
    @gEqtrd
      (synWa (synWa (synWa (synWa (synWa
                (synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv))) (synWa
                    (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
                      (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))
                (synWss S (synClnquo R C))) (.classMem (.cv u) C))
            (.classMem (.cv u) (synCuni S)))
          (synWa (.classMem (.cv b) S) (.classMem (.cv u) (.cv b))))
        (synWa (.classMem (.cv w) C) (.classEq (.cv b) (synCec (.cv w) (synClnker R)))))
      (.cv b) (synCec (.cv w) (synClnker R)) (synCec (.cv u) (synClnker R)) p0021
      p0058
  have p0064 :=
    @gSyl
      (synWa (synWa (synWa (synWa (synWa
                (synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv))) (synWa
                    (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
                      (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))
                (synWss S (synClnquo R C))) (.classMem (.cv u) C))
            (.classMem (.cv u) (synCuni S)))
          (synWa (.classMem (.cv b) S) (.classMem (.cv u) (.cv b))))
        (synWa (.classMem (.cv w) C) (.classEq (.cv b) (synCec (.cv w) (synClnker R)))))
      (synWa (synWa (synWa (synWa
              (synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv))) (synWa
                  (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
                    (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))
              (synWss S (synClnquo R C))) (.classMem (.cv u) C))
          (.classMem (.cv u) (synCuni S)))
        (synWa (.classMem (.cv b) S) (.classMem (.cv u) (.cv b))))
      (.classMem (.cv b) S) p0022 p0013
  have p0065 :=
    @gEqeltrrd
      (synWa (synWa (synWa (synWa (synWa
                (synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv))) (synWa
                    (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
                      (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))
                (synWss S (synClnquo R C))) (.classMem (.cv u) C))
            (.classMem (.cv u) (synCuni S)))
          (synWa (.classMem (.cv b) S) (.classMem (.cv u) (.cv b))))
        (synWa (.classMem (.cv w) C) (.classEq (.cv b) (synCec (.cv w) (synClnker R)))))
      (.cv b) (synCec (.cv u) (synClnker R)) S p0059 p0064
  have p0066 :=
    @gRexlimddv
      (synWa (synWa (synWa (synWa
              (synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv))) (synWa
                  (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
                    (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))
              (synWss S (synClnquo R C))) (.classMem (.cv u) C))
          (.classMem (.cv u) (synCuni S)))
        (synWa (.classMem (.cv b) S) (.classMem (.cv u) (.cv b))))
      (.classEq (.cv b) (synCec (.cv w) (synClnker R)))
      (.classMem (synCec (.cv u) (synClnker R)) S) w C dv_cache_0009 dv_cache_0010 p0018
      p0065
  have p0067 :=
    @gRexlimddv
      (synWa (synWa (synWa (synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv)))
              (synWa (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
                  (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))
            (synWss S (synClnquo R C))) (.classMem (.cv u) C))
        (.classMem (.cv u) (synCuni S)))
      (.classMem (.cv u) (.cv b)) (.classMem (synCec (.cv u) (synClnker R)) S) b S
      dv_cache_0011 dv_cache_0012 p0003 p0066
  have p0068 :=
    @gEx
      (synWa (synWa (synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv))) (synWa
              (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
                (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))
          (synWss S (synClnquo R C))) (.classMem (.cv u) C))
      (.classMem (.cv u) (synCuni S)) (.classMem (synCec (.cv u) (synClnker R)) S)
      p0067
  have p0069 :=
    @gSimpl
      (synWa (synWa (synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv))) (synWa
              (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
                (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))
          (synWss S (synClnquo R C))) (.classMem (.cv u) C))
      (.classMem (synCec (.cv u) (synClnker R)) S)
  have p0073 :=
    @gSimpr (synWa (.classMem R (synCvv)) (.classMem C (synCvv)))
      (synWa (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
          (synWbr R (synCconnex) C)) (synWss R (synCxp C C)))
  have p0074 :=
    @gSyl
      (synWa (synWa (synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv))) (synWa
              (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
                (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))
          (synWss S (synClnquo R C))) (.classMem (.cv u) C))
      (synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv))) (synWa
          (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
            (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))
      (synWa (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
          (synWbr R (synCconnex) C)) (synWss R (synCxp C C)))
      p0042 p0073
  have p0075 :=
    @gSimpl
      (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
        (synWbr R (synCconnex) C))
      (synWss R (synCxp C C))
  have p0076 :=
    @gSyl
      (synWa (synWa (synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv))) (synWa
              (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
                (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))
          (synWss S (synClnquo R C))) (.classMem (.cv u) C))
      (synWa (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
          (synWbr R (synCconnex) C)) (synWss R (synCxp C C)))
      (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
        (synWbr R (synCconnex) C))
      p0074 p0075
  have p0077 :=
    @gSimpl (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
      (synWbr R (synCconnex) C)
  have p0078 :=
    @gSyl
      (synWa (synWa (synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv))) (synWa
              (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
                (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))
          (synWss S (synClnquo R C))) (.classMem (.cv u) C))
      (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
        (synWbr R (synCconnex) C))
      (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C)) p0076 p0077
  have p0079 := @gSimpl (synWbr R (synCref) C) (synWbr R (synCtrans) C)
  have p0080 :=
    @gSyl
      (synWa (synWa (synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv))) (synWa
              (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
                (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))
          (synWss S (synClnquo R C))) (.classMem (.cv u) C))
      (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
      (synWbr R (synCref) C) p0078 p0079
  have p0081 :=
    @gSyl
      (synWa (synWa (synWa (synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv)))
              (synWa (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
                  (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))
            (synWss S (synClnquo R C))) (.classMem (.cv u) C))
        (.classMem (synCec (.cv u) (synClnker R)) S))
      (synWa (synWa (synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv))) (synWa
              (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
                (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))
          (synWss S (synClnquo R C))) (.classMem (.cv u) C))
      (synWbr R (synCref) C) p0069 p0080
  have p0084 :=
    @gSyl
      (synWa (synWa (synWa (synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv)))
              (synWa (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
                  (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))
            (synWss S (synClnquo R C))) (.classMem (.cv u) C))
        (.classMem (synCec (.cv u) (synClnker R)) S))
      (synWa (synWa (synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv))) (synWa
              (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
                (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))
          (synWss S (synClnquo R C))) (.classMem (.cv u) C))
      (.classMem (.cv u) C) p0069 p0052
  have p0085 :=
    @gRefd
      (synWa (synWa (synWa (synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv)))
              (synWa (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
                  (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))
            (synWss S (synClnquo R C))) (.classMem (.cv u) C))
        (.classMem (synCec (.cv u) (synClnker R)) S))
      C R (.cv u) p0081 p0084
  have p0103 :=
    @gJca
      (synWa (synWa (synWa (synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv)))
              (synWa (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
                  (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))
            (synWss S (synClnquo R C))) (.classMem (.cv u) C))
        (.classMem (synCec (.cv u) (synClnker R)) S))
      (synWbr (.cv u) R (.cv u)) (synWbr (.cv u) R (.cv u)) p0085 p0085
  have p0104 := @gEllnkerecg (.cv u) (.cv u) R
  have p0105 :=
    @gA1i
      (synWb (.classMem (.cv u) (synCec (.cv u) (synClnker R)))
        (synWa (synWbr (.cv u) R (.cv u)) (synWbr (.cv u) R (.cv u))))
      (synWa (synWa (synWa (synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv)))
              (synWa (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
                  (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))
            (synWss S (synClnquo R C))) (.classMem (.cv u) C))
        (.classMem (synCec (.cv u) (synClnker R)) S))
      p0104
  have p0106 :=
    @gMpbird
      (synWa (synWa (synWa (synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv)))
              (synWa (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
                  (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))
            (synWss S (synClnquo R C))) (.classMem (.cv u) C))
        (.classMem (synCec (.cv u) (synClnker R)) S))
      (.classMem (.cv u) (synCec (.cv u) (synClnker R)))
      (synWa (synWbr (.cv u) R (.cv u)) (synWbr (.cv u) R (.cv u))) p0103 p0105
  have p0107 :=
    @gSimpr
      (synWa (synWa (synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv))) (synWa
              (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
                (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))
          (synWss S (synClnquo R C))) (.classMem (.cv u) C))
      (.classMem (synCec (.cv u) (synClnker R)) S)
  have p0108 :=
    @gJca
      (synWa (synWa (synWa (synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv)))
              (synWa (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
                  (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))
            (synWss S (synClnquo R C))) (.classMem (.cv u) C))
        (.classMem (synCec (.cv u) (synClnker R)) S))
      (.classMem (.cv u) (synCec (.cv u) (synClnker R)))
      (.classMem (synCec (.cv u) (synClnker R)) S) p0106 p0107
  have p0109 := @gElunii (.cv u) (synCec (.cv u) (synClnker R)) S
  have p0110 :=
    @gSyl
      (synWa (synWa (synWa (synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv)))
              (synWa (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
                  (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))
            (synWss S (synClnquo R C))) (.classMem (.cv u) C))
        (.classMem (synCec (.cv u) (synClnker R)) S))
      (synWa (.classMem (.cv u) (synCec (.cv u) (synClnker R)))
        (.classMem (synCec (.cv u) (synClnker R)) S))
      (.classMem (.cv u) (synCuni S)) p0108 p0109
  have p0111 :=
    @gEx
      (synWa (synWa (synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv))) (synWa
              (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
                (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))
          (synWss S (synClnquo R C))) (.classMem (.cv u) C))
      (.classMem (synCec (.cv u) (synClnker R)) S) (.classMem (.cv u) (synCuni S))
      p0110
  have p0112 :=
    @gImpbid
      (synWa (synWa (synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv))) (synWa
              (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
                (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))
          (synWss S (synClnquo R C))) (.classMem (.cv u) C))
      (.classMem (.cv u) (synCuni S)) (.classMem (synCec (.cv u) (synClnker R)) S)
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

/-- Checked nominal proof certificate identified upstream as `g_lnqordwe`. -/
@[expose]
noncomputable def gLnqordwe (C : Class) (R : Class) (dv_C_R : Disjoint C.fv R.fv) :
    Nominal.NPrf
      (.imp (synWa (synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv))) (synWa
              (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
                (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))
          (synWbr (synCdif R (synCcnv R)) (synCfound) C))
        (synWbr (synClnqord R C) (synCwe) (synClnquo R C))) :=
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
  have dv_cache_0002 : w ∉ ((synCuni (.cv x))).fv :=
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
      ((synWa (synWa (synWa (synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv)))
                (synWa (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
                    (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))
              (synWbr (synCdif R (synCcnv R)) (synCfound) C))
            (synWa (synWss (.cv x) (synClnquo R C)) (synWne (.cv x) (synC0))))
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
  have dv_cache_0010 : b ∉ ((synWrex w C (.classMem (.cv w) (synCuni (.cv x))))).fv :=
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
      ((synWa (synWa (synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv))) (synWa
                (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
                  (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))
            (synWbr (synCdif R (synCcnv R)) (synCfound) C))
          (synWa (synWss (.cv x) (synClnquo R C)) (synWne (.cv x) (synC0))))).fv :=
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
  have dv_cache_0014 : u ∉ ((synCdif R (synCcnv R))).fv :=
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
  have dv_cache_0015 : t ∉ ((synCdif R (synCcnv R))).fv :=
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
  have dv_cache_0016 : w ∉ ((Wff.classMem (.cv u) (synCuni (.cv x)))).fv :=
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
  have dv_cache_0017 : u ∉ ((Wff.classMem (.cv w) (synCuni (.cv x)))).fv :=
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
  have dv_cache_0018 : t ∉ ((Wff.classMem (.cv w) (synCuni (.cv x)))).fv :=
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
  have dv_cache_0019 : w ∉ ((Wff.classMem (.cv t) (synCuni (.cv x)))).fv :=
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
      ((Wff.imp (synWa (.classMem (.cv v) (synCuni (.cv x)))
            (synWbr (.cv v) (synCdif R (synCcnv R)) (.cv u)))
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
  have dv_cache_0030 : v ∉ ((Wff.classEq (.cv y) (synCec (.cv u) (synClnker R)))).fv :=
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
      ((synWa (synWa (synWa (synWa
                (synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv))) (synWa
                    (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
                      (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))
                (synWbr (synCdif R (synCcnv R)) (synCfound) C))
              (synWa (synWss (.cv x) (synClnquo R C)) (synWne (.cv x) (synC0))))
            (synWa (.classMem (.cv u) C) (synWa (.classMem (.cv u) (synCuni (.cv x)))
                (synWral t C (.imp (synWa (.classMem (.cv t) (synCuni (.cv x)))
                      (synWbr (.cv t) (synCdif R (synCcnv R)) (.cv u)))
                    (.classEq (.cv t) (.cv u))))))) (synWa (.classMem (.cv y) (.cv x))
            (synWbr (.cv y) (synClnqord R C) (synCec (.cv u) (synClnker R)))))).fv :=
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
      ((synWa (synWa (synWa (synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv)))
                (synWa (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
                    (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))
              (synWbr (synCdif R (synCcnv R)) (synCfound) C))
            (synWa (synWss (.cv x) (synClnquo R C)) (synWne (.cv x) (synC0))))
          (synWa (.classMem (.cv u) C) (synWa (.classMem (.cv u) (synCuni (.cv x)))
              (synWral t C (.imp (synWa (.classMem (.cv t) (synCuni (.cv x)))
                    (synWbr (.cv t) (synCdif R (synCcnv R)) (.cv u)))
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
  have dv_cache_0033 : y ∉ ((Wff.classEq (.cv z) (synCec (.cv u) (synClnker R)))).fv :=
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
  have dv_cache_0034 : z ∉ ((synCec (.cv u) (synClnker R))).fv :=
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
      ((synWral y (.cv x)
          (.imp (synWbr (.cv y) (synClnqord R C) (synCec (.cv u) (synClnker R)))
            (.classEq (.cv y) (synCec (.cv u) (synClnker R)))))).fv :=
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
      ((synWrex z (.cv x) (synWral y (.cv x) (.imp (synWbr (.cv y) (synClnqord R C) (.cv z))
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
      ((synWa (synWa (synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv))) (synWa
                (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
                  (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))
            (synWbr (synCdif R (synCcnv R)) (synCfound) C))
          (synWa (synWss (.cv x) (synClnquo R C)) (synWne (.cv x) (synC0))))).fv :=
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
  have dv_cache_0039 : x ∉ ((synClnquo R C)).fv :=
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
  have dv_cache_0040 : y ∉ ((synClnquo R C)).fv :=
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
  have dv_cache_0041 : z ∉ ((synClnquo R C)).fv :=
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
  have dv_cache_0042 : x ∉ ((synClnqord R C)).fv :=
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
  have dv_cache_0043 : y ∉ ((synClnqord R C)).fv :=
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
  have dv_cache_0044 : z ∉ ((synClnqord R C)).fv :=
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
      ((synWa (synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv))) (synWa
              (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
                (synWbr R (synCconnex) C)) (synWss R (synCxp C C))))
          (synWbr (synCdif R (synCcnv R)) (synCfound) C))).fv :=
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
    (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
      (synWbr R (synCconnex) C))
  let syntaxFormula0001 : Wff := (synWa syntaxFormula0000 (synWss R (synCxp C C)))
  let syntaxFormula0002 : Wff :=
    (synWa (synWa (.classMem R (synCvv)) (.classMem C (synCvv))) syntaxFormula0001)
  let syntaxFormula0003 : Wff :=
    (synWa syntaxFormula0002 (synWbr (synCdif R (synCcnv R)) (synCfound) C))
  let syntaxFormula0004 : Wff :=
    (synWa syntaxFormula0003
      (synWa (synWss (.cv x) (synClnquo R C)) (synWne (.cv x) (synC0))))
  let syntaxFormula0005 : Wff := (synWa syntaxFormula0004 (.classMem (.cv b) (.cv x)))
  let syntaxFormula0006 : Wff := (synWa syntaxFormula0005 (.classMem (.cv w) C))
  let syntaxFormula0007 : Wff :=
    (synWa syntaxFormula0006 (.classEq (.cv b) (synCec (.cv w) (synClnker R))))
  let syntaxFormula0008 : Wff :=
    (synWa syntaxFormula0002 (synWss (.cv x) (synClnquo R C)))
  let syntaxFormula0009 : Wff :=
    (synWa (.classMem (.cv t) (synCuni (.cv x)))
      (synWbr (.cv t) (synCdif R (synCcnv R)) (.cv u)))
  let syntaxFormula0010 : Wff := (.imp syntaxFormula0009 (.classEq (.cv t) (.cv u)))
  let syntaxFormula0011 : Wff := (synWral t C syntaxFormula0010)
  let syntaxFormula0012 : Wff :=
    (synWa (.classMem (.cv u) (synCuni (.cv x))) syntaxFormula0011)
  let syntaxFormula0013 : Wff := (synWa (.classMem (.cv u) C) syntaxFormula0012)
  let syntaxFormula0014 : Wff := (synWa syntaxFormula0004 syntaxFormula0013)
  let syntaxFormula0015 : Wff :=
    (synWa (.classMem (.cv y) (.cv x))
      (synWbr (.cv y) (synClnqord R C) (synCec (.cv u) (synClnker R))))
  let syntaxFormula0016 : Wff := (synWa syntaxFormula0014 syntaxFormula0015)
  let syntaxFormula0017 : Wff :=
    (synWa (.classMem (.cv v) C) (.classEq (.cv y) (synCec (.cv v) (synClnker R))))
  let syntaxFormula0018 : Wff := (synWa syntaxFormula0016 syntaxFormula0017)
  let syntaxFormula0019 : Wff := (synWa syntaxFormula0018 (synWbr (.cv u) R (.cv v)))
  let syntaxFormula0020 : Wff :=
    (synWa (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
      (synWss R (synCxp C C)))
  let syntaxFormula0021 : Wff :=
    (synWa syntaxFormula0020 (synWa (.classMem (.cv v) C) (.classMem (.cv u) C)))
  let syntaxFormula0022 : Wff := (synWa (.classMem R (synCvv)) syntaxFormula0021)
  let syntaxFormula0023 : Wff :=
    (synWbr (synCec (.cv v) (synClnker R)) (synClnqord R C)
      (synCec (.cv u) (synClnker R)))
  let syntaxFormula0024 : Wff :=
    (synWa syntaxFormula0018 (.neg (synWbr (.cv u) R (.cv v))))
  let syntaxFormula0025 : Wff :=
    (synWa (.classMem (.cv v) (synCuni (.cv x)))
      (synWbr (.cv v) (synCdif R (synCcnv R)) (.cv u)))
  let syntaxFormula0026 : Wff := (.imp syntaxFormula0025 (.classEq (.cv v) (.cv u)))
  let syntaxFormula0027 : Wff :=
    (.imp (synWbr (.cv y) (synClnqord R C) (synCec (.cv u) (synClnker R)))
      (.classEq (.cv y) (synCec (.cv u) (synClnker R))))
  let syntaxFormula0028 : Wff := (synWral y (.cv x) syntaxFormula0027)
  let syntaxFormula0029 : Wff :=
    (synWral y (.cv x)
      (.imp (synWbr (.cv y) (synClnqord R C) (.cv z)) (.classEq (.cv y) (.cv z))))
  let syntaxFormula0030 : Wff :=
    (synWa (synWbr (synClnqord R C) (synCstrict) (synClnquo R C))
      (synWbr (synClnqord R C) (synCfound) (synClnquo R C)))
  have p0000 :=
    @gSimpl syntaxFormula0002 (synWbr (synCdif R (synCcnv R)) (synCfound) C)
  have p0001 := @gLnqordor C R dv_cache_0001
  have p0002 :=
    @gSyl syntaxFormula0003 syntaxFormula0002
      (synWbr (synClnqord R C) (synCstrict) (synClnquo R C)) p0000 p0001
  have p0004 :=
    @gSimpl (synWa (.classMem R (synCvv)) (.classMem C (synCvv))) syntaxFormula0001
  have p0005 :=
    @gSyl syntaxFormula0003 syntaxFormula0002
      (synWa (.classMem R (synCvv)) (.classMem C (synCvv))) p0000 p0004
  have p0006 := @gLnqordexg C R dv_cache_0001
  have p0007 :=
    @gSyl syntaxFormula0003 (synWa (.classMem R (synCvv)) (.classMem C (synCvv)))
      (.classMem (synClnqord R C) (synCvv)) p0005 p0006
  have p0011 := @gLnquoexg C R dv_cache_0001
  have p0012 :=
    @gSyl syntaxFormula0003 (synWa (.classMem R (synCvv)) (.classMem C (synCvv)))
      (.classMem (synClnquo R C) (synCvv)) p0005 p0011
  have p0013 := @gAbid2 w (synCuni (.cv x)) dv_cache_0002
  have p0014 := @gVex x
  have p0015 := @gUniexg (.cv x) (synCvv)
  have p0016 := Nominal.mp p0014 p0015
  have p0017 :=
    @gEqeltri (.cab w (.classMem (.cv w) (synCuni (.cv x)))) (synCuni (.cv x))
      (synCvv) p0013 p0016
  have p0018 := @gEleq1 (.cv w) (.cv u) (synCuni (.cv x))
  have p0019 := @gEleq1 (.cv w) (.cv t) (synCuni (.cv x))
  have p0020 :=
    @gSimpl syntaxFormula0003
      (synWa (synWss (.cv x) (synClnquo R C)) (synWne (.cv x) (synC0)))
  have p0021 :=
    @gSimpr syntaxFormula0002 (synWbr (synCdif R (synCcnv R)) (synCfound) C)
  have p0022 :=
    @gSyl syntaxFormula0004 syntaxFormula0003
      (synWbr (synCdif R (synCcnv R)) (synCfound) C) p0020 p0021
  have p0023 :=
    @gSimpr syntaxFormula0003
      (synWa (synWss (.cv x) (synClnquo R C)) (synWne (.cv x) (synC0)))
  have p0024 := @gSimpr (synWss (.cv x) (synClnquo R C)) (synWne (.cv x) (synC0))
  have p0025 :=
    @gSyl syntaxFormula0004
      (synWa (synWss (.cv x) (synClnquo R C)) (synWne (.cv x) (synC0)))
      (synWne (.cv x) (synC0)) p0023 p0024
  have p0026 := @gN0 b (.cv x) dv_cache_0003
  have p0027 :=
    @gA1i (synWb (synWne (.cv x) (synC0)) (synWex b (.classMem (.cv b) (.cv x))))
      syntaxFormula0004 p0026
  have p0028 :=
    @gMpbid syntaxFormula0004 (synWne (.cv x) (synC0))
      (synWex b (.classMem (.cv b) (.cv x))) p0025 p0027
  have p0029 := @gSimpl syntaxFormula0004 (.classMem (.cv b) (.cv x))
  have p0030 :=
    @gSimpr syntaxFormula0003
      (synWa (synWss (.cv x) (synClnquo R C)) (synWne (.cv x) (synC0)))
  have p0031 := @gSimpl (synWss (.cv x) (synClnquo R C)) (synWne (.cv x) (synC0))
  have p0032 :=
    @gSyl syntaxFormula0004
      (synWa (synWss (.cv x) (synClnquo R C)) (synWne (.cv x) (synC0)))
      (synWss (.cv x) (synClnquo R C)) p0030 p0031
  have p0033 :=
    @gSyl syntaxFormula0005 syntaxFormula0004 (synWss (.cv x) (synClnquo R C)) p0029
      p0032
  have p0034 := @gSimpr syntaxFormula0004 (.classMem (.cv b) (.cv x))
  have p0035 := @gSseldd syntaxFormula0005 (.cv x) (synClnquo R C) (.cv b) p0033 p0034
  have p0036 := @gVex b
  have p0037 :=
    @gEllnquo w C (.cv b) R dv_cache_0004 dv_cache_0001 dv_cache_0005 dv_cache_0006
      dv_cache_0007 dv_cache_0008 p0036
  have p0038 :=
    @gA1i
      (synWb (.classMem (.cv b) (synClnquo R C))
        (synWrex w C (.classEq (.cv b) (synCec (.cv w) (synClnker R)))))
      syntaxFormula0005 p0037
  have p0039 :=
    @gMpbid syntaxFormula0005 (.classMem (.cv b) (synClnquo R C))
      (synWrex w C (.classEq (.cv b) (synCec (.cv w) (synClnker R)))) p0035 p0038
  have p0040 :=
    @gSimpr syntaxFormula0006 (.classEq (.cv b) (synCec (.cv w) (synClnker R)))
  have p0041 :=
    @gSimpl syntaxFormula0006 (.classEq (.cv b) (synCec (.cv w) (synClnker R)))
  have p0042 := @gSimpl syntaxFormula0005 (.classMem (.cv w) C)
  have p0043 := @gSyl syntaxFormula0007 syntaxFormula0006 syntaxFormula0005 p0041 p0042
  have p0044 := @gSimpr syntaxFormula0004 (.classMem (.cv b) (.cv x))
  have p0045 :=
    @gSyl syntaxFormula0007 syntaxFormula0005 (.classMem (.cv b) (.cv x)) p0043 p0044
  have p0046 :=
    @gEqeltrrd syntaxFormula0007 (.cv b) (synCec (.cv w) (synClnker R)) (.cv x) p0040
      p0045
  have p0047 :=
    @gSimpl syntaxFormula0006 (.classEq (.cv b) (synCec (.cv w) (synClnker R)))
  have p0048 := @gSimpl syntaxFormula0005 (.classMem (.cv w) C)
  have p0049 := @gSyl syntaxFormula0007 syntaxFormula0006 syntaxFormula0005 p0047 p0048
  have p0050 := @gSimpl syntaxFormula0004 (.classMem (.cv b) (.cv x))
  have p0051 := @gSyl syntaxFormula0007 syntaxFormula0005 syntaxFormula0004 p0049 p0050
  have p0052 :=
    @gSimpl syntaxFormula0003
      (synWa (synWss (.cv x) (synClnquo R C)) (synWne (.cv x) (synC0)))
  have p0053 :=
    @gSimpl syntaxFormula0002 (synWbr (synCdif R (synCcnv R)) (synCfound) C)
  have p0054 := @gSyl syntaxFormula0004 syntaxFormula0003 syntaxFormula0002 p0052 p0053
  have p0055 := @gSyl syntaxFormula0007 syntaxFormula0004 syntaxFormula0002 p0051 p0054
  have p0056 :=
    @gSimpl syntaxFormula0006 (.classEq (.cv b) (synCec (.cv w) (synClnker R)))
  have p0057 := @gSimpl syntaxFormula0005 (.classMem (.cv w) C)
  have p0058 := @gSyl syntaxFormula0007 syntaxFormula0006 syntaxFormula0005 p0056 p0057
  have p0059 := @gSimpl syntaxFormula0004 (.classMem (.cv b) (.cv x))
  have p0060 := @gSyl syntaxFormula0007 syntaxFormula0005 syntaxFormula0004 p0058 p0059
  have p0061 :=
    @gSimpr syntaxFormula0003
      (synWa (synWss (.cv x) (synClnquo R C)) (synWne (.cv x) (synC0)))
  have p0062 := @gSimpl (synWss (.cv x) (synClnquo R C)) (synWne (.cv x) (synC0))
  have p0063 :=
    @gSyl syntaxFormula0004
      (synWa (synWss (.cv x) (synClnquo R C)) (synWne (.cv x) (synC0)))
      (synWss (.cv x) (synClnquo R C)) p0061 p0062
  have p0064 :=
    @gSyl syntaxFormula0007 syntaxFormula0004 (synWss (.cv x) (synClnquo R C)) p0060
      p0063
  have p0065 :=
    @gJca syntaxFormula0007 syntaxFormula0002 (synWss (.cv x) (synClnquo R C)) p0055
      p0064
  have p0066 :=
    @gSimpl syntaxFormula0006 (.classEq (.cv b) (synCec (.cv w) (synClnker R)))
  have p0067 := @gSimpr syntaxFormula0005 (.classMem (.cv w) C)
  have p0068 :=
    @gSyl syntaxFormula0007 syntaxFormula0006 (.classMem (.cv w) C) p0066 p0067
  have p0069 :=
    @gJca syntaxFormula0007 syntaxFormula0008 (.classMem (.cv w) C) p0065 p0068
  have p0070 := @gLnquounionb w C R (.cv x) dv_cache_0001
  have p0071 :=
    @gSyl syntaxFormula0007 (synWa syntaxFormula0008 (.classMem (.cv w) C))
      (synWb (.classMem (.cv w) (synCuni (.cv x)))
        (.classMem (synCec (.cv w) (synClnker R)) (.cv x)))
      p0069 p0070
  have p0072 :=
    @gMpbird syntaxFormula0007 (.classMem (.cv w) (synCuni (.cv x)))
      (.classMem (synCec (.cv w) (synClnker R)) (.cv x)) p0046 p0071
  have p0073 :=
    @gEx syntaxFormula0006 (.classEq (.cv b) (synCec (.cv w) (synClnker R)))
      (.classMem (.cv w) (synCuni (.cv x))) p0072
  have p0074 :=
    @gReximdva syntaxFormula0005 (.classEq (.cv b) (synCec (.cv w) (synClnker R)))
      (.classMem (.cv w) (synCuni (.cv x))) w C dv_cache_0009 p0073
  have p0075 :=
    @gMpd syntaxFormula0005
      (synWrex w C (.classEq (.cv b) (synCec (.cv w) (synClnker R))))
      (synWrex w C (.classMem (.cv w) (synCuni (.cv x)))) p0039 p0074
  have p0076 :=
    @gExlimddv syntaxFormula0004 (.classMem (.cv b) (.cv x))
      (synWrex w C (.classMem (.cv w) (synCuni (.cv x)))) b dv_cache_0010 dv_cache_0011
      p0028 p0075
  have p0077_e01_recanon :
    Nominal.NPrf
      (.imp (.objEq w u) (synWb (.classMem (.cv w) (synCuni (.cv x)))
          (.classMem (.cv u) (synCuni (.cv x))))) :=
    Nominal.RecanonTransportDev.transport
      (by
        simp only [synWb, synCuni, synWex, synWa]
        simp (config :=
          { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_class_cv]
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
        · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0018
  have p0077_e02_recanon :
    Nominal.NPrf
      (.imp (.objEq w t) (synWb (.classMem (.cv w) (synCuni (.cv x)))
          (.classMem (.cv t) (synCuni (.cv x))))) :=
    Nominal.RecanonTransportDev.transport
      (by
        simp only [synWb, synCuni, synWex, synWa]
        simp (config :=
          { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_class_cv]
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
        · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0019
  have p0077 :=
    @gFrds syntaxFormula0004 (.classMem (.cv w) (synCuni (.cv x)))
      (.classMem (.cv u) (synCuni (.cv x))) (.classMem (.cv t) (synCuni (.cv x))) w u t
      C (synCdif R (synCcnv R)) dv_cache_0005 dv_cache_0012 dv_cache_0013 dv_cache_0014
      dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020
      dv_cache_0021 dv_cache_0022 p0017 p0077_e01_recanon p0077_e02_recanon p0022 p0076
  have p0078 := @gSimpr syntaxFormula0004 syntaxFormula0013
  have p0079 := @gSimpr (.classMem (.cv u) C) syntaxFormula0012
  have p0080 := @gSyl syntaxFormula0014 syntaxFormula0013 syntaxFormula0012 p0078 p0079
  have p0081 := @gSimpl (.classMem (.cv u) (synCuni (.cv x))) syntaxFormula0011
  have p0082 :=
    @gSyl syntaxFormula0014 syntaxFormula0012 (.classMem (.cv u) (synCuni (.cv x)))
      p0080 p0081
  have p0083 := @gSimpl syntaxFormula0004 syntaxFormula0013
  have p0084 :=
    @gSimpl syntaxFormula0003
      (synWa (synWss (.cv x) (synClnquo R C)) (synWne (.cv x) (synC0)))
  have p0085 :=
    @gSimpl syntaxFormula0002 (synWbr (synCdif R (synCcnv R)) (synCfound) C)
  have p0086 := @gSyl syntaxFormula0004 syntaxFormula0003 syntaxFormula0002 p0084 p0085
  have p0087 := @gSyl syntaxFormula0014 syntaxFormula0004 syntaxFormula0002 p0083 p0086
  have p0088 := @gSimpl syntaxFormula0004 syntaxFormula0013
  have p0089 :=
    @gSimpr syntaxFormula0003
      (synWa (synWss (.cv x) (synClnquo R C)) (synWne (.cv x) (synC0)))
  have p0090 := @gSimpl (synWss (.cv x) (synClnquo R C)) (synWne (.cv x) (synC0))
  have p0091 :=
    @gSyl syntaxFormula0004
      (synWa (synWss (.cv x) (synClnquo R C)) (synWne (.cv x) (synC0)))
      (synWss (.cv x) (synClnquo R C)) p0089 p0090
  have p0092 :=
    @gSyl syntaxFormula0014 syntaxFormula0004 (synWss (.cv x) (synClnquo R C)) p0088
      p0091
  have p0093 :=
    @gJca syntaxFormula0014 syntaxFormula0002 (synWss (.cv x) (synClnquo R C)) p0087
      p0092
  have p0094 := @gSimpr syntaxFormula0004 syntaxFormula0013
  have p0095 := @gSimpl (.classMem (.cv u) C) syntaxFormula0012
  have p0096 :=
    @gSyl syntaxFormula0014 syntaxFormula0013 (.classMem (.cv u) C) p0094 p0095
  have p0097 :=
    @gJca syntaxFormula0014 syntaxFormula0008 (.classMem (.cv u) C) p0093 p0096
  have p0098 := @gLnquounionb u C R (.cv x) dv_cache_0001
  have p0099 :=
    @gSyl syntaxFormula0014 (synWa syntaxFormula0008 (.classMem (.cv u) C))
      (synWb (.classMem (.cv u) (synCuni (.cv x)))
        (.classMem (synCec (.cv u) (synClnker R)) (.cv x)))
      p0097 p0098
  have p0100 :=
    @gMpbid syntaxFormula0014 (.classMem (.cv u) (synCuni (.cv x)))
      (.classMem (synCec (.cv u) (synClnker R)) (.cv x)) p0082 p0099
  have p0101 := @gSimpl syntaxFormula0014 syntaxFormula0015
  have p0102 := @gSimpl syntaxFormula0004 syntaxFormula0013
  have p0103 := @gSyl syntaxFormula0016 syntaxFormula0014 syntaxFormula0004 p0101 p0102
  have p0104 :=
    @gSimpr syntaxFormula0003
      (synWa (synWss (.cv x) (synClnquo R C)) (synWne (.cv x) (synC0)))
  have p0105 := @gSimpl (synWss (.cv x) (synClnquo R C)) (synWne (.cv x) (synC0))
  have p0106 :=
    @gSyl syntaxFormula0004
      (synWa (synWss (.cv x) (synClnquo R C)) (synWne (.cv x) (synC0)))
      (synWss (.cv x) (synClnquo R C)) p0104 p0105
  have p0107 :=
    @gSyl syntaxFormula0016 syntaxFormula0004 (synWss (.cv x) (synClnquo R C)) p0103
      p0106
  have p0108 := @gSimpr syntaxFormula0014 syntaxFormula0015
  have p0109 :=
    @gSimpl (.classMem (.cv y) (.cv x))
      (synWbr (.cv y) (synClnqord R C) (synCec (.cv u) (synClnker R)))
  have p0110 :=
    @gSyl syntaxFormula0016 syntaxFormula0015 (.classMem (.cv y) (.cv x)) p0108 p0109
  have p0111 := @gSseldd syntaxFormula0016 (.cv x) (synClnquo R C) (.cv y) p0107 p0110
  have p0112 := @gVex y
  have p0113 :=
    @gEllnquo v C (.cv y) R dv_cache_0023 dv_cache_0001 dv_cache_0024 dv_cache_0025
      dv_cache_0026 dv_cache_0027 p0112
  have p0114 :=
    @gA1i
      (synWb (.classMem (.cv y) (synClnquo R C))
        (synWrex v C (.classEq (.cv y) (synCec (.cv v) (synClnker R)))))
      syntaxFormula0016 p0113
  have p0115 :=
    @gMpbid syntaxFormula0016 (.classMem (.cv y) (synClnquo R C))
      (synWrex v C (.classEq (.cv y) (synCec (.cv v) (synClnker R)))) p0111 p0114
  have p0116 := @gSimpl syntaxFormula0018 (synWbr (.cv u) R (.cv v))
  have p0117 := @gSimpr syntaxFormula0016 syntaxFormula0017
  have p0118 :=
    @gSimpr (.classMem (.cv v) C) (.classEq (.cv y) (synCec (.cv v) (synClnker R)))
  have p0119 :=
    @gSyl syntaxFormula0018 syntaxFormula0017
      (.classEq (.cv y) (synCec (.cv v) (synClnker R))) p0117 p0118
  have p0120 :=
    @gSyl syntaxFormula0019 syntaxFormula0018
      (.classEq (.cv y) (synCec (.cv v) (synClnker R))) p0116 p0119
  have p0121 := @gSimpl syntaxFormula0018 (synWbr (.cv u) R (.cv v))
  have p0122 := @gSimpr syntaxFormula0016 syntaxFormula0017
  have p0123 :=
    @gSimpr (.classMem (.cv v) C) (.classEq (.cv y) (synCec (.cv v) (synClnker R)))
  have p0124 :=
    @gSyl syntaxFormula0018 syntaxFormula0017
      (.classEq (.cv y) (synCec (.cv v) (synClnker R))) p0122 p0123
  have p0125 := @gSimpl syntaxFormula0016 syntaxFormula0017
  have p0126 := @gSimpr syntaxFormula0014 syntaxFormula0015
  have p0127 :=
    @gSimpr (.classMem (.cv y) (.cv x))
      (synWbr (.cv y) (synClnqord R C) (synCec (.cv u) (synClnker R)))
  have p0128 :=
    @gSyl syntaxFormula0016 syntaxFormula0015
      (synWbr (.cv y) (synClnqord R C) (synCec (.cv u) (synClnker R))) p0126 p0127
  have p0129 :=
    @gSyl syntaxFormula0018 syntaxFormula0016
      (synWbr (.cv y) (synClnqord R C) (synCec (.cv u) (synClnker R))) p0125 p0128
  have p0130 :=
    @gEqbrtrrd syntaxFormula0018 (.cv y) (synCec (.cv v) (synClnker R))
      (synCec (.cv u) (synClnker R)) (synClnqord R C) p0124 p0129
  have p0131 := @gSimpl syntaxFormula0016 syntaxFormula0017
  have p0132 := @gSimpl syntaxFormula0014 syntaxFormula0015
  have p0133 := @gSimpl syntaxFormula0004 syntaxFormula0013
  have p0134 := @gSyl syntaxFormula0016 syntaxFormula0014 syntaxFormula0004 p0132 p0133
  have p0135 := @gSyl syntaxFormula0018 syntaxFormula0016 syntaxFormula0004 p0131 p0134
  have p0136 :=
    @gSimpl syntaxFormula0003
      (synWa (synWss (.cv x) (synClnquo R C)) (synWne (.cv x) (synC0)))
  have p0137 :=
    @gSimpl syntaxFormula0002 (synWbr (synCdif R (synCcnv R)) (synCfound) C)
  have p0138 := @gSyl syntaxFormula0004 syntaxFormula0003 syntaxFormula0002 p0136 p0137
  have p0139 :=
    @gSimpl (synWa (.classMem R (synCvv)) (.classMem C (synCvv))) syntaxFormula0001
  have p0140 :=
    @gSyl syntaxFormula0004 syntaxFormula0002
      (synWa (.classMem R (synCvv)) (.classMem C (synCvv))) p0138 p0139
  have p0141 := @gSimpl (.classMem R (synCvv)) (.classMem C (synCvv))
  have p0142 :=
    @gSyl syntaxFormula0004 (synWa (.classMem R (synCvv)) (.classMem C (synCvv)))
      (.classMem R (synCvv)) p0140 p0141
  have p0143 :=
    @gSyl syntaxFormula0018 syntaxFormula0004 (.classMem R (synCvv)) p0135 p0142
  have p0144 := @gSimpl syntaxFormula0016 syntaxFormula0017
  have p0145 := @gSimpl syntaxFormula0014 syntaxFormula0015
  have p0146 := @gSimpl syntaxFormula0004 syntaxFormula0013
  have p0147 := @gSyl syntaxFormula0016 syntaxFormula0014 syntaxFormula0004 p0145 p0146
  have p0148 := @gSyl syntaxFormula0018 syntaxFormula0016 syntaxFormula0004 p0144 p0147
  have p0149 :=
    @gSimpl syntaxFormula0003
      (synWa (synWss (.cv x) (synClnquo R C)) (synWne (.cv x) (synC0)))
  have p0150 :=
    @gSimpl syntaxFormula0002 (synWbr (synCdif R (synCcnv R)) (synCfound) C)
  have p0151 := @gSyl syntaxFormula0004 syntaxFormula0003 syntaxFormula0002 p0149 p0150
  have p0152 :=
    @gSimpr (synWa (.classMem R (synCvv)) (.classMem C (synCvv))) syntaxFormula0001
  have p0153 := @gSyl syntaxFormula0004 syntaxFormula0002 syntaxFormula0001 p0151 p0152
  have p0154 := @gSimpl syntaxFormula0000 (synWss R (synCxp C C))
  have p0155 := @gSyl syntaxFormula0004 syntaxFormula0001 syntaxFormula0000 p0153 p0154
  have p0156 :=
    @gSimpl (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
      (synWbr R (synCconnex) C)
  have p0157 :=
    @gSyl syntaxFormula0004 syntaxFormula0000
      (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C)) p0155 p0156
  have p0158 :=
    @gSyl syntaxFormula0018 syntaxFormula0004
      (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C)) p0148 p0157
  have p0159 := @gSimpl syntaxFormula0016 syntaxFormula0017
  have p0160 := @gSimpl syntaxFormula0014 syntaxFormula0015
  have p0161 := @gSimpl syntaxFormula0004 syntaxFormula0013
  have p0162 := @gSyl syntaxFormula0016 syntaxFormula0014 syntaxFormula0004 p0160 p0161
  have p0163 := @gSyl syntaxFormula0018 syntaxFormula0016 syntaxFormula0004 p0159 p0162
  have p0164 :=
    @gSimpl syntaxFormula0003
      (synWa (synWss (.cv x) (synClnquo R C)) (synWne (.cv x) (synC0)))
  have p0165 :=
    @gSimpl syntaxFormula0002 (synWbr (synCdif R (synCcnv R)) (synCfound) C)
  have p0166 := @gSyl syntaxFormula0004 syntaxFormula0003 syntaxFormula0002 p0164 p0165
  have p0167 :=
    @gSimpr (synWa (.classMem R (synCvv)) (.classMem C (synCvv))) syntaxFormula0001
  have p0168 := @gSyl syntaxFormula0004 syntaxFormula0002 syntaxFormula0001 p0166 p0167
  have p0169 := @gSimpr syntaxFormula0000 (synWss R (synCxp C C))
  have p0170 :=
    @gSyl syntaxFormula0004 syntaxFormula0001 (synWss R (synCxp C C)) p0168 p0169
  have p0171 :=
    @gSyl syntaxFormula0018 syntaxFormula0004 (synWss R (synCxp C C)) p0163 p0170
  have p0172 :=
    @gJca syntaxFormula0018 (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
      (synWss R (synCxp C C)) p0158 p0171
  have p0173 := @gSimpr syntaxFormula0016 syntaxFormula0017
  have p0174 :=
    @gSimpl (.classMem (.cv v) C) (.classEq (.cv y) (synCec (.cv v) (synClnker R)))
  have p0175 :=
    @gSyl syntaxFormula0018 syntaxFormula0017 (.classMem (.cv v) C) p0173 p0174
  have p0176 := @gSimpl syntaxFormula0016 syntaxFormula0017
  have p0177 := @gSimpl syntaxFormula0014 syntaxFormula0015
  have p0178 := @gSyl syntaxFormula0018 syntaxFormula0016 syntaxFormula0014 p0176 p0177
  have p0179 := @gSimpr syntaxFormula0004 syntaxFormula0013
  have p0180 := @gSimpl (.classMem (.cv u) C) syntaxFormula0012
  have p0181 :=
    @gSyl syntaxFormula0014 syntaxFormula0013 (.classMem (.cv u) C) p0179 p0180
  have p0182 :=
    @gSyl syntaxFormula0018 syntaxFormula0014 (.classMem (.cv u) C) p0178 p0181
  have p0183 :=
    @gJca syntaxFormula0018 (.classMem (.cv v) C) (.classMem (.cv u) C) p0175 p0182
  have p0184 :=
    @gJca syntaxFormula0018 syntaxFormula0020
      (synWa (.classMem (.cv v) C) (.classMem (.cv u) C)) p0172 p0183
  have p0185 :=
    @gJca syntaxFormula0018 (.classMem R (synCvv)) syntaxFormula0021 p0143 p0184
  have p0186 := @gBrlnqordkern C R (.cv v) (.cv u) dv_cache_0001
  have p0187 :=
    @gSyl syntaxFormula0018 syntaxFormula0022
      (synWb syntaxFormula0023 (synWbr (.cv v) R (.cv u))) p0185 p0186
  have p0188 :=
    @gMpbid syntaxFormula0018 syntaxFormula0023 (synWbr (.cv v) R (.cv u)) p0130 p0187
  have p0189 :=
    @gSyl syntaxFormula0019 syntaxFormula0018 (synWbr (.cv v) R (.cv u)) p0121 p0188
  have p0190 := @gSimpr syntaxFormula0018 (synWbr (.cv u) R (.cv v))
  have p0191 :=
    @gJca syntaxFormula0019 (synWbr (.cv v) R (.cv u)) (synWbr (.cv u) R (.cv v)) p0189
      p0190
  have p0192 := @gSimpl syntaxFormula0018 (synWbr (.cv u) R (.cv v))
  have p0193 := @gSimpl syntaxFormula0016 syntaxFormula0017
  have p0194 := @gSimpl syntaxFormula0014 syntaxFormula0015
  have p0195 := @gSimpl syntaxFormula0004 syntaxFormula0013
  have p0196 := @gSyl syntaxFormula0016 syntaxFormula0014 syntaxFormula0004 p0194 p0195
  have p0197 := @gSyl syntaxFormula0018 syntaxFormula0016 syntaxFormula0004 p0193 p0196
  have p0198 := @gSyl syntaxFormula0019 syntaxFormula0018 syntaxFormula0004 p0192 p0197
  have p0199 :=
    @gSimpl syntaxFormula0003
      (synWa (synWss (.cv x) (synClnquo R C)) (synWne (.cv x) (synC0)))
  have p0200 :=
    @gSimpl syntaxFormula0002 (synWbr (synCdif R (synCcnv R)) (synCfound) C)
  have p0201 := @gSyl syntaxFormula0004 syntaxFormula0003 syntaxFormula0002 p0199 p0200
  have p0202 := @gSyl syntaxFormula0019 syntaxFormula0004 syntaxFormula0002 p0198 p0201
  have p0203 := @gSimpl syntaxFormula0018 (synWbr (.cv u) R (.cv v))
  have p0204 := @gSimpr syntaxFormula0016 syntaxFormula0017
  have p0205 :=
    @gSimpl (.classMem (.cv v) C) (.classEq (.cv y) (synCec (.cv v) (synClnker R)))
  have p0206 :=
    @gSyl syntaxFormula0018 syntaxFormula0017 (.classMem (.cv v) C) p0204 p0205
  have p0207 :=
    @gSyl syntaxFormula0019 syntaxFormula0018 (.classMem (.cv v) C) p0203 p0206
  have p0208 := @gSimpl syntaxFormula0018 (synWbr (.cv u) R (.cv v))
  have p0209 := @gSimpl syntaxFormula0016 syntaxFormula0017
  have p0210 := @gSimpl syntaxFormula0014 syntaxFormula0015
  have p0211 := @gSyl syntaxFormula0018 syntaxFormula0016 syntaxFormula0014 p0209 p0210
  have p0212 := @gSimpr syntaxFormula0004 syntaxFormula0013
  have p0213 := @gSimpl (.classMem (.cv u) C) syntaxFormula0012
  have p0214 :=
    @gSyl syntaxFormula0014 syntaxFormula0013 (.classMem (.cv u) C) p0212 p0213
  have p0215 :=
    @gSyl syntaxFormula0018 syntaxFormula0014 (.classMem (.cv u) C) p0211 p0214
  have p0216 :=
    @gSyl syntaxFormula0019 syntaxFormula0018 (.classMem (.cv u) C) p0208 p0215
  have p0217 :=
    @gJca syntaxFormula0019 (.classMem (.cv v) C) (.classMem (.cv u) C) p0207 p0216
  have p0218 :=
    @gJca syntaxFormula0019 syntaxFormula0002
      (synWa (.classMem (.cv v) C) (.classMem (.cv u) C)) p0202 p0217
  have p0219 := @gLnkereceqb C R (.cv v) (.cv u) dv_cache_0001
  have p0220 :=
    @gSyl syntaxFormula0019
      (synWa syntaxFormula0002 (synWa (.classMem (.cv v) C) (.classMem (.cv u) C)))
      (synWb (.classEq (synCec (.cv v) (synClnker R)) (synCec (.cv u) (synClnker R)))
        (synWa (synWbr (.cv v) R (.cv u)) (synWbr (.cv u) R (.cv v))))
      p0218 p0219
  have p0221 :=
    @gMpbird syntaxFormula0019
      (.classEq (synCec (.cv v) (synClnker R)) (synCec (.cv u) (synClnker R)))
      (synWa (synWbr (.cv v) R (.cv u)) (synWbr (.cv u) R (.cv v))) p0191 p0220
  have p0222 :=
    @gEqtrd syntaxFormula0019 (.cv y) (synCec (.cv v) (synClnker R))
      (synCec (.cv u) (synClnker R)) p0120 p0221
  have p0223 :=
    @gEx syntaxFormula0018 (synWbr (.cv u) R (.cv v))
      (.classEq (.cv y) (synCec (.cv u) (synClnker R))) p0222
  have p0224 := @gSimpl syntaxFormula0018 (.neg (synWbr (.cv u) R (.cv v)))
  have p0225 := @gSimpr syntaxFormula0016 syntaxFormula0017
  have p0226 :=
    @gSimpr (.classMem (.cv v) C) (.classEq (.cv y) (synCec (.cv v) (synClnker R)))
  have p0227 :=
    @gSyl syntaxFormula0018 syntaxFormula0017
      (.classEq (.cv y) (synCec (.cv v) (synClnker R))) p0225 p0226
  have p0228 :=
    @gSyl syntaxFormula0024 syntaxFormula0018
      (.classEq (.cv y) (synCec (.cv v) (synClnker R))) p0224 p0227
  have p0229 := @gSimpl syntaxFormula0018 (.neg (synWbr (.cv u) R (.cv v)))
  have p0230 := @gSimpr syntaxFormula0016 syntaxFormula0017
  have p0231 :=
    @gSimpr (.classMem (.cv v) C) (.classEq (.cv y) (synCec (.cv v) (synClnker R)))
  have p0232 :=
    @gSyl syntaxFormula0018 syntaxFormula0017
      (.classEq (.cv y) (synCec (.cv v) (synClnker R))) p0230 p0231
  have p0233 :=
    @gSyl syntaxFormula0024 syntaxFormula0018
      (.classEq (.cv y) (synCec (.cv v) (synClnker R))) p0229 p0232
  have p0234 := @gSimpl syntaxFormula0018 (.neg (synWbr (.cv u) R (.cv v)))
  have p0235 := @gSimpl syntaxFormula0016 syntaxFormula0017
  have p0236 := @gSimpr syntaxFormula0014 syntaxFormula0015
  have p0237 :=
    @gSimpl (.classMem (.cv y) (.cv x))
      (synWbr (.cv y) (synClnqord R C) (synCec (.cv u) (synClnker R)))
  have p0238 :=
    @gSyl syntaxFormula0016 syntaxFormula0015 (.classMem (.cv y) (.cv x)) p0236 p0237
  have p0239 :=
    @gSyl syntaxFormula0018 syntaxFormula0016 (.classMem (.cv y) (.cv x)) p0235 p0238
  have p0240 :=
    @gSyl syntaxFormula0024 syntaxFormula0018 (.classMem (.cv y) (.cv x)) p0234 p0239
  have p0241 :=
    @gEqeltrrd syntaxFormula0024 (.cv y) (synCec (.cv v) (synClnker R)) (.cv x) p0233
      p0240
  have p0242 := @gSimpl syntaxFormula0018 (.neg (synWbr (.cv u) R (.cv v)))
  have p0243 := @gSimpl syntaxFormula0016 syntaxFormula0017
  have p0244 := @gSimpl syntaxFormula0014 syntaxFormula0015
  have p0245 := @gSimpl syntaxFormula0004 syntaxFormula0013
  have p0246 := @gSyl syntaxFormula0016 syntaxFormula0014 syntaxFormula0004 p0244 p0245
  have p0247 := @gSyl syntaxFormula0018 syntaxFormula0016 syntaxFormula0004 p0243 p0246
  have p0248 := @gSyl syntaxFormula0024 syntaxFormula0018 syntaxFormula0004 p0242 p0247
  have p0249 :=
    @gSimpl syntaxFormula0003
      (synWa (synWss (.cv x) (synClnquo R C)) (synWne (.cv x) (synC0)))
  have p0250 :=
    @gSimpl syntaxFormula0002 (synWbr (synCdif R (synCcnv R)) (synCfound) C)
  have p0251 := @gSyl syntaxFormula0004 syntaxFormula0003 syntaxFormula0002 p0249 p0250
  have p0252 := @gSyl syntaxFormula0024 syntaxFormula0004 syntaxFormula0002 p0248 p0251
  have p0253 := @gSimpl syntaxFormula0018 (.neg (synWbr (.cv u) R (.cv v)))
  have p0254 := @gSimpl syntaxFormula0016 syntaxFormula0017
  have p0255 := @gSimpl syntaxFormula0014 syntaxFormula0015
  have p0256 := @gSimpl syntaxFormula0004 syntaxFormula0013
  have p0257 := @gSyl syntaxFormula0016 syntaxFormula0014 syntaxFormula0004 p0255 p0256
  have p0258 := @gSyl syntaxFormula0018 syntaxFormula0016 syntaxFormula0004 p0254 p0257
  have p0259 := @gSyl syntaxFormula0024 syntaxFormula0018 syntaxFormula0004 p0253 p0258
  have p0260 :=
    @gSimpr syntaxFormula0003
      (synWa (synWss (.cv x) (synClnquo R C)) (synWne (.cv x) (synC0)))
  have p0261 := @gSimpl (synWss (.cv x) (synClnquo R C)) (synWne (.cv x) (synC0))
  have p0262 :=
    @gSyl syntaxFormula0004
      (synWa (synWss (.cv x) (synClnquo R C)) (synWne (.cv x) (synC0)))
      (synWss (.cv x) (synClnquo R C)) p0260 p0261
  have p0263 :=
    @gSyl syntaxFormula0024 syntaxFormula0004 (synWss (.cv x) (synClnquo R C)) p0259
      p0262
  have p0264 :=
    @gJca syntaxFormula0024 syntaxFormula0002 (synWss (.cv x) (synClnquo R C)) p0252
      p0263
  have p0265 := @gSimpl syntaxFormula0018 (.neg (synWbr (.cv u) R (.cv v)))
  have p0266 := @gSimpr syntaxFormula0016 syntaxFormula0017
  have p0267 :=
    @gSimpl (.classMem (.cv v) C) (.classEq (.cv y) (synCec (.cv v) (synClnker R)))
  have p0268 :=
    @gSyl syntaxFormula0018 syntaxFormula0017 (.classMem (.cv v) C) p0266 p0267
  have p0269 :=
    @gSyl syntaxFormula0024 syntaxFormula0018 (.classMem (.cv v) C) p0265 p0268
  have p0270 :=
    @gJca syntaxFormula0024 syntaxFormula0008 (.classMem (.cv v) C) p0264 p0269
  have p0271 := @gLnquounionb v C R (.cv x) dv_cache_0001
  have p0272 :=
    @gSyl syntaxFormula0024 (synWa syntaxFormula0008 (.classMem (.cv v) C))
      (synWb (.classMem (.cv v) (synCuni (.cv x)))
        (.classMem (synCec (.cv v) (synClnker R)) (.cv x)))
      p0270 p0271
  have p0273 :=
    @gMpbird syntaxFormula0024 (.classMem (.cv v) (synCuni (.cv x)))
      (.classMem (synCec (.cv v) (synClnker R)) (.cv x)) p0241 p0272
  have p0274 := @gSimpl syntaxFormula0018 (.neg (synWbr (.cv u) R (.cv v)))
  have p0275 := @gSimpr syntaxFormula0016 syntaxFormula0017
  have p0276 :=
    @gSimpr (.classMem (.cv v) C) (.classEq (.cv y) (synCec (.cv v) (synClnker R)))
  have p0277 :=
    @gSyl syntaxFormula0018 syntaxFormula0017
      (.classEq (.cv y) (synCec (.cv v) (synClnker R))) p0275 p0276
  have p0278 := @gSimpl syntaxFormula0016 syntaxFormula0017
  have p0279 := @gSimpr syntaxFormula0014 syntaxFormula0015
  have p0280 :=
    @gSimpr (.classMem (.cv y) (.cv x))
      (synWbr (.cv y) (synClnqord R C) (synCec (.cv u) (synClnker R)))
  have p0281 :=
    @gSyl syntaxFormula0016 syntaxFormula0015
      (synWbr (.cv y) (synClnqord R C) (synCec (.cv u) (synClnker R))) p0279 p0280
  have p0282 :=
    @gSyl syntaxFormula0018 syntaxFormula0016
      (synWbr (.cv y) (synClnqord R C) (synCec (.cv u) (synClnker R))) p0278 p0281
  have p0283 :=
    @gEqbrtrrd syntaxFormula0018 (.cv y) (synCec (.cv v) (synClnker R))
      (synCec (.cv u) (synClnker R)) (synClnqord R C) p0277 p0282
  have p0284 := @gSimpl syntaxFormula0016 syntaxFormula0017
  have p0285 := @gSimpl syntaxFormula0014 syntaxFormula0015
  have p0286 := @gSimpl syntaxFormula0004 syntaxFormula0013
  have p0287 := @gSyl syntaxFormula0016 syntaxFormula0014 syntaxFormula0004 p0285 p0286
  have p0288 := @gSyl syntaxFormula0018 syntaxFormula0016 syntaxFormula0004 p0284 p0287
  have p0289 :=
    @gSimpl syntaxFormula0003
      (synWa (synWss (.cv x) (synClnquo R C)) (synWne (.cv x) (synC0)))
  have p0290 :=
    @gSimpl syntaxFormula0002 (synWbr (synCdif R (synCcnv R)) (synCfound) C)
  have p0291 := @gSyl syntaxFormula0004 syntaxFormula0003 syntaxFormula0002 p0289 p0290
  have p0292 :=
    @gSimpl (synWa (.classMem R (synCvv)) (.classMem C (synCvv))) syntaxFormula0001
  have p0293 :=
    @gSyl syntaxFormula0004 syntaxFormula0002
      (synWa (.classMem R (synCvv)) (.classMem C (synCvv))) p0291 p0292
  have p0294 := @gSimpl (.classMem R (synCvv)) (.classMem C (synCvv))
  have p0295 :=
    @gSyl syntaxFormula0004 (synWa (.classMem R (synCvv)) (.classMem C (synCvv)))
      (.classMem R (synCvv)) p0293 p0294
  have p0296 :=
    @gSyl syntaxFormula0018 syntaxFormula0004 (.classMem R (synCvv)) p0288 p0295
  have p0297 := @gSimpl syntaxFormula0016 syntaxFormula0017
  have p0298 := @gSimpl syntaxFormula0014 syntaxFormula0015
  have p0299 := @gSimpl syntaxFormula0004 syntaxFormula0013
  have p0300 := @gSyl syntaxFormula0016 syntaxFormula0014 syntaxFormula0004 p0298 p0299
  have p0301 := @gSyl syntaxFormula0018 syntaxFormula0016 syntaxFormula0004 p0297 p0300
  have p0302 :=
    @gSimpl syntaxFormula0003
      (synWa (synWss (.cv x) (synClnquo R C)) (synWne (.cv x) (synC0)))
  have p0303 :=
    @gSimpl syntaxFormula0002 (synWbr (synCdif R (synCcnv R)) (synCfound) C)
  have p0304 := @gSyl syntaxFormula0004 syntaxFormula0003 syntaxFormula0002 p0302 p0303
  have p0305 :=
    @gSimpr (synWa (.classMem R (synCvv)) (.classMem C (synCvv))) syntaxFormula0001
  have p0306 := @gSyl syntaxFormula0004 syntaxFormula0002 syntaxFormula0001 p0304 p0305
  have p0307 := @gSimpl syntaxFormula0000 (synWss R (synCxp C C))
  have p0308 := @gSyl syntaxFormula0004 syntaxFormula0001 syntaxFormula0000 p0306 p0307
  have p0309 :=
    @gSimpl (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
      (synWbr R (synCconnex) C)
  have p0310 :=
    @gSyl syntaxFormula0004 syntaxFormula0000
      (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C)) p0308 p0309
  have p0311 :=
    @gSyl syntaxFormula0018 syntaxFormula0004
      (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C)) p0301 p0310
  have p0312 := @gSimpl syntaxFormula0016 syntaxFormula0017
  have p0313 := @gSimpl syntaxFormula0014 syntaxFormula0015
  have p0314 := @gSimpl syntaxFormula0004 syntaxFormula0013
  have p0315 := @gSyl syntaxFormula0016 syntaxFormula0014 syntaxFormula0004 p0313 p0314
  have p0316 := @gSyl syntaxFormula0018 syntaxFormula0016 syntaxFormula0004 p0312 p0315
  have p0317 :=
    @gSimpl syntaxFormula0003
      (synWa (synWss (.cv x) (synClnquo R C)) (synWne (.cv x) (synC0)))
  have p0318 :=
    @gSimpl syntaxFormula0002 (synWbr (synCdif R (synCcnv R)) (synCfound) C)
  have p0319 := @gSyl syntaxFormula0004 syntaxFormula0003 syntaxFormula0002 p0317 p0318
  have p0320 :=
    @gSimpr (synWa (.classMem R (synCvv)) (.classMem C (synCvv))) syntaxFormula0001
  have p0321 := @gSyl syntaxFormula0004 syntaxFormula0002 syntaxFormula0001 p0319 p0320
  have p0322 := @gSimpr syntaxFormula0000 (synWss R (synCxp C C))
  have p0323 :=
    @gSyl syntaxFormula0004 syntaxFormula0001 (synWss R (synCxp C C)) p0321 p0322
  have p0324 :=
    @gSyl syntaxFormula0018 syntaxFormula0004 (synWss R (synCxp C C)) p0316 p0323
  have p0325 :=
    @gJca syntaxFormula0018 (synWa (synWbr R (synCref) C) (synWbr R (synCtrans) C))
      (synWss R (synCxp C C)) p0311 p0324
  have p0326 := @gSimpr syntaxFormula0016 syntaxFormula0017
  have p0327 :=
    @gSimpl (.classMem (.cv v) C) (.classEq (.cv y) (synCec (.cv v) (synClnker R)))
  have p0328 :=
    @gSyl syntaxFormula0018 syntaxFormula0017 (.classMem (.cv v) C) p0326 p0327
  have p0329 := @gSimpl syntaxFormula0016 syntaxFormula0017
  have p0330 := @gSimpl syntaxFormula0014 syntaxFormula0015
  have p0331 := @gSyl syntaxFormula0018 syntaxFormula0016 syntaxFormula0014 p0329 p0330
  have p0332 := @gSimpr syntaxFormula0004 syntaxFormula0013
  have p0333 := @gSimpl (.classMem (.cv u) C) syntaxFormula0012
  have p0334 :=
    @gSyl syntaxFormula0014 syntaxFormula0013 (.classMem (.cv u) C) p0332 p0333
  have p0335 :=
    @gSyl syntaxFormula0018 syntaxFormula0014 (.classMem (.cv u) C) p0331 p0334
  have p0336 :=
    @gJca syntaxFormula0018 (.classMem (.cv v) C) (.classMem (.cv u) C) p0328 p0335
  have p0337 :=
    @gJca syntaxFormula0018 syntaxFormula0020
      (synWa (.classMem (.cv v) C) (.classMem (.cv u) C)) p0325 p0336
  have p0338 :=
    @gJca syntaxFormula0018 (.classMem R (synCvv)) syntaxFormula0021 p0296 p0337
  have p0339 := @gBrlnqordkern C R (.cv v) (.cv u) dv_cache_0001
  have p0340 :=
    @gSyl syntaxFormula0018 syntaxFormula0022
      (synWb syntaxFormula0023 (synWbr (.cv v) R (.cv u))) p0338 p0339
  have p0341 :=
    @gMpbid syntaxFormula0018 syntaxFormula0023 (synWbr (.cv v) R (.cv u)) p0283 p0340
  have p0342 :=
    @gSyl syntaxFormula0024 syntaxFormula0018 (synWbr (.cv v) R (.cv u)) p0274 p0341
  have p0343 := @gSimpr syntaxFormula0018 (.neg (synWbr (.cv u) R (.cv v)))
  have p0344 := @gBrcnv (.cv v) (.cv u) R
  have p0345 :=
    @gA1i (synWb (synWbr (.cv v) (synCcnv R) (.cv u)) (synWbr (.cv u) R (.cv v)))
      syntaxFormula0024 p0344
  have p0346 :=
    @gNotbid syntaxFormula0024 (synWbr (.cv v) (synCcnv R) (.cv u))
      (synWbr (.cv u) R (.cv v)) p0345
  have p0347 :=
    @gMpbird syntaxFormula0024 (.neg (synWbr (.cv v) (synCcnv R) (.cv u)))
      (.neg (synWbr (.cv u) R (.cv v))) p0343 p0346
  have p0348 :=
    @gJca syntaxFormula0024 (synWbr (.cv v) R (.cv u))
      (.neg (synWbr (.cv v) (synCcnv R) (.cv u))) p0342 p0347
  have p0349 := @gBrdif (.cv v) (.cv u) R (synCcnv R)
  have p0350 :=
    @gA1i
      (synWb (synWbr (.cv v) (synCdif R (synCcnv R)) (.cv u))
        (synWa (synWbr (.cv v) R (.cv u)) (.neg (synWbr (.cv v) (synCcnv R) (.cv u)))))
      syntaxFormula0024 p0349
  have p0351 :=
    @gMpbird syntaxFormula0024 (synWbr (.cv v) (synCdif R (synCcnv R)) (.cv u))
      (synWa (synWbr (.cv v) R (.cv u)) (.neg (synWbr (.cv v) (synCcnv R) (.cv u))))
      p0348 p0350
  have p0352 :=
    @gJca syntaxFormula0024 (.classMem (.cv v) (synCuni (.cv x)))
      (synWbr (.cv v) (synCdif R (synCcnv R)) (.cv u)) p0273 p0351
  have p0353 := @gSimpl syntaxFormula0018 (.neg (synWbr (.cv u) R (.cv v)))
  have p0354 := @gSimpl syntaxFormula0016 syntaxFormula0017
  have p0355 := @gSimpl syntaxFormula0014 syntaxFormula0015
  have p0356 := @gSyl syntaxFormula0018 syntaxFormula0016 syntaxFormula0014 p0354 p0355
  have p0357 := @gSimpr syntaxFormula0004 syntaxFormula0013
  have p0358 := @gSimpr (.classMem (.cv u) C) syntaxFormula0012
  have p0359 := @gSyl syntaxFormula0014 syntaxFormula0013 syntaxFormula0012 p0357 p0358
  have p0360 := @gSimpr (.classMem (.cv u) (synCuni (.cv x))) syntaxFormula0011
  have p0361 := @gSyl syntaxFormula0014 syntaxFormula0012 syntaxFormula0011 p0359 p0360
  have p0362 := @gSyl syntaxFormula0018 syntaxFormula0014 syntaxFormula0011 p0356 p0361
  have p0363 := @gSyl syntaxFormula0024 syntaxFormula0018 syntaxFormula0011 p0353 p0362
  have p0364 := @gSimpl syntaxFormula0018 (.neg (synWbr (.cv u) R (.cv v)))
  have p0365 := @gSimpr syntaxFormula0016 syntaxFormula0017
  have p0366 :=
    @gSimpl (.classMem (.cv v) C) (.classEq (.cv y) (synCec (.cv v) (synClnker R)))
  have p0367 :=
    @gSyl syntaxFormula0018 syntaxFormula0017 (.classMem (.cv v) C) p0365 p0366
  have p0368 :=
    @gSyl syntaxFormula0024 syntaxFormula0018 (.classMem (.cv v) C) p0364 p0367
  have p0369 := @gId (.classEq (.cv t) (.cv v))
  have p0370 :=
    @gEleq1d (.classEq (.cv t) (.cv v)) (.cv t) (.cv v) (synCuni (.cv x)) p0369
  have p0371 := @gId (.classEq (.cv t) (.cv v))
  have p0372 :=
    @gBreq1d (.classEq (.cv t) (.cv v)) (.cv t) (.cv v) (.cv u) (synCdif R (synCcnv R))
      p0371
  have p0373 :=
    @gAnbi12d (.classEq (.cv t) (.cv v)) (.classMem (.cv t) (synCuni (.cv x)))
      (.classMem (.cv v) (synCuni (.cv x)))
      (synWbr (.cv t) (synCdif R (synCcnv R)) (.cv u))
      (synWbr (.cv v) (synCdif R (synCcnv R)) (.cv u)) p0370 p0372
  have p0374 := @gId (.classEq (.cv t) (.cv v))
  have p0375 := @gEqeq1d (.classEq (.cv t) (.cv v)) (.cv t) (.cv v) (.cv u) p0374
  have p0376 :=
    @gImbi12d (.classEq (.cv t) (.cv v)) syntaxFormula0009 syntaxFormula0025
      (.classEq (.cv t) (.cv u)) (.classEq (.cv v) (.cv u)) p0373 p0375
  have p0377 :=
    @gRspcv syntaxFormula0010 syntaxFormula0026 t (.cv v) C dv_cache_0028 dv_cache_0013
      dv_cache_0029 p0376
  have p0378 :=
    @gSyl syntaxFormula0024 (.classMem (.cv v) C)
      (.imp syntaxFormula0011 syntaxFormula0026) p0368 p0377
  have p0379 := @gMpd syntaxFormula0024 syntaxFormula0011 syntaxFormula0026 p0363 p0378
  have p0380 :=
    @gMpd syntaxFormula0024 syntaxFormula0025 (.classEq (.cv v) (.cv u)) p0352 p0379
  have p0381 := @gEceq1 (.cv v) (.cv u) (synClnker R)
  have p0382 :=
    @gSyl syntaxFormula0024 (.classEq (.cv v) (.cv u))
      (.classEq (synCec (.cv v) (synClnker R)) (synCec (.cv u) (synClnker R))) p0380
      p0381
  have p0383 :=
    @gEqtrd syntaxFormula0024 (.cv y) (synCec (.cv v) (synClnker R))
      (synCec (.cv u) (synClnker R)) p0228 p0382
  have p0384 :=
    @gEx syntaxFormula0018 (.neg (synWbr (.cv u) R (.cv v)))
      (.classEq (.cv y) (synCec (.cv u) (synClnker R))) p0383
  have p0385 :=
    @gPm261d syntaxFormula0018 (synWbr (.cv u) R (.cv v))
      (.classEq (.cv y) (synCec (.cv u) (synClnker R))) p0223 p0384
  have p0386 :=
    @gRexlimddv syntaxFormula0016 (.classEq (.cv y) (synCec (.cv v) (synClnker R)))
      (.classEq (.cv y) (synCec (.cv u) (synClnker R))) v C dv_cache_0030 dv_cache_0031
      p0115 p0385
  have p0387 :=
    @gExp32 syntaxFormula0014 (.classMem (.cv y) (.cv x))
      (synWbr (.cv y) (synClnqord R C) (synCec (.cv u) (synClnker R)))
      (.classEq (.cv y) (synCec (.cv u) (synClnker R))) p0386
  have p0388 :=
    @gRalrimiv syntaxFormula0014 syntaxFormula0027 y (.cv x) dv_cache_0032 p0387
  have p0389 :=
    @gJca syntaxFormula0014 (.classMem (synCec (.cv u) (synClnker R)) (.cv x))
      syntaxFormula0028 p0100 p0388
  have p0390 := @gId (.classEq (.cv z) (synCec (.cv u) (synClnker R)))
  have p0391 :=
    @gBreq2d (.classEq (.cv z) (synCec (.cv u) (synClnker R))) (.cv z)
      (synCec (.cv u) (synClnker R)) (.cv y) (synClnqord R C) p0390
  have p0392 := @gId (.classEq (.cv z) (synCec (.cv u) (synClnker R)))
  have p0393 :=
    @gEqeq2d (.classEq (.cv z) (synCec (.cv u) (synClnker R))) (.cv z)
      (synCec (.cv u) (synClnker R)) (.cv y) p0392
  have p0394 :=
    @gImbi12d (.classEq (.cv z) (synCec (.cv u) (synClnker R)))
      (synWbr (.cv y) (synClnqord R C) (.cv z))
      (synWbr (.cv y) (synClnqord R C) (synCec (.cv u) (synClnker R)))
      (.classEq (.cv y) (.cv z)) (.classEq (.cv y) (synCec (.cv u) (synClnker R))) p0391
      p0393
  have p0395 :=
    @gRalbidv (.classEq (.cv z) (synCec (.cv u) (synClnker R)))
      (.imp (synWbr (.cv y) (synClnqord R C) (.cv z)) (.classEq (.cv y) (.cv z)))
      syntaxFormula0027 y (.cv x) dv_cache_0033 p0394
  have p0396 :=
    @gRspcev syntaxFormula0029 syntaxFormula0028 z (synCec (.cv u) (synClnker R))
      (.cv x) dv_cache_0034 dv_cache_0035 dv_cache_0036 p0395
  have p0397 :=
    @gSyl syntaxFormula0014
      (synWa (.classMem (synCec (.cv u) (synClnker R)) (.cv x)) syntaxFormula0028)
      (synWrex z (.cv x) syntaxFormula0029) p0389 p0396
  have p0398_e00_recanon :
    Nominal.NPrf (.imp syntaxFormula0004 (synWrex u C syntaxFormula0012)) :=
    Nominal.RecanonTransportDev.transport
      (by
        simp only [synWa, synWrex, synWex]
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
    @gRexlimddv syntaxFormula0004 syntaxFormula0012
      (synWrex z (.cv x) syntaxFormula0029) u C dv_cache_0037 dv_cache_0038
      p0398_e00_recanon p0397
  have p0399_e02_recanon :
    Nominal.NPrf
      (.imp syntaxFormula0004 (synWrex z (.cv x) (synWral y (.cv x)
            (.imp (synWbr (.cv y) (synClnqord R C) (.cv z)) (.objEq y z))))) :=
    Nominal.RecanonTransportDev.transport
      (by
        simp only [synWrex, synWex, synWral, synWa]
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
    @gFrrd syntaxFormula0003 x y z (synClnquo R C) (synClnqord R C) dv_cache_0039
      dv_cache_0040 dv_cache_0041 dv_cache_0042 dv_cache_0043 dv_cache_0044 dv_cache_0045
      dv_cache_0046 dv_cache_0047 dv_cache_0048 p0007 p0012 p0399_e02_recanon
  have p0400 :=
    @gJca syntaxFormula0003 (synWbr (synClnqord R C) (synCstrict) (synClnquo R C))
      (synWbr (synClnqord R C) (synCfound) (synClnquo R C)) p0002 p0399
  have p0401 := (Nominal.classEqRefl (synCwe))
  have p0402 :=
    @gBreqi (synClnqord R C) (synClnquo R C) (synCwe)
      (synCin (synCstrict) (synCfound)) p0401
  have p0403 := @gBrin (synClnqord R C) (synClnquo R C) (synCstrict) (synCfound)
  have p0404 :=
    @gBitri (synWbr (synClnqord R C) (synCwe) (synClnquo R C))
      (synWbr (synClnqord R C) (synCin (synCstrict) (synCfound)) (synClnquo R C))
      syntaxFormula0030 p0402 p0403
  have p0405 :=
    @gA1i
      (synWb (synWbr (synClnqord R C) (synCwe) (synClnquo R C)) syntaxFormula0030)
      syntaxFormula0003 p0404
  have p0406 :=
    @gMpbird syntaxFormula0003 (synWbr (synClnqord R C) (synCwe) (synClnquo R C))
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

/-- Checked nominal proof certificate identified upstream as `g_finleastadjndv`. -/
@[expose]
noncomputable def gFinleastadjndv (k : Var) (m : Var) (n : Var) (X : Class) (Y : Class)
    (_dv_X_k : k ∉ X.fv) (_dv_X_m : m ∉ X.fv) (dv_X_n : n ∉ X.fv) (_dv_Y_k : k ∉ Y.fv)
    (_dv_Y_m : m ∉ Y.fv) (dv_Y_n : n ∉ Y.fv) (_dv_k_m : k ≠ m) (dv_k_n : k ≠ n)
    (dv_m_n : m ≠ n) :
    Nominal.NPrf
      (.imp (synW3a (synWa (.classMem (.cv m) (synCnnc)) (.classMem (.cv k) (synCnnc)))
          (synWa (.classMem (.cv m) X) (.classMem (.cv k) Y)) (synWa (synWa
              (synWral n (synCnnc) (.imp (.classMem (.cv n) X)
                  (synWbr (.cv m) (synCkqrel (synClefin)) (.cv n)))) (synWral n (synCnnc)
                (.imp (.classMem (.cv n) Y)
                  (synWbr (.cv k) (synCkqrel (synClefin)) (.cv n))))) (synWa
              (synWral n (synCnnc) (.imp (.classMem (.cv n) X) (.classMem (.cv n) Y)))
              (synWral n (synCnnc) (.imp (.classMem (.cv n) Y)
                  (.classMem (synCplc (.cv n) (synC1c)) X))))))
        (synWo (.classEq (.cv m) (.cv k)) (.classEq (.cv m) (synCplc (.cv k) (synC1c))))) :=
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
  have dv_cache_0002 : n ∉ ((synCnnc)).fv :=
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
    n ∉ ((Wff.imp (.classMem (.cv k) Y) (.classMem (synCplc (.cv k) (synC1c)) X))).fv :=
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
  have dv_cache_0004 : n ∉ ((synCplc (.cv k) (synC1c))).fv :=
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
      ((Wff.imp (.classMem (synCplc (.cv k) (synC1c)) X)
          (synWbr (.cv m) (synCkqrel (synClefin)) (synCplc (.cv k) (synC1c))))).fv :=
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
          (synWbr (.cv k) (synCkqrel (synClefin)) (.cv m)))).fv :=
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
    @gSimp2 (synWa (.classMem (.cv m) (synCnnc)) (.classMem (.cv k) (synCnnc)))
      (synWa (.classMem (.cv m) X) (.classMem (.cv k) Y))
      (synWa (synWa (synWral n (synCnnc) (.imp (.classMem (.cv n) X)
              (synWbr (.cv m) (synCkqrel (synClefin)) (.cv n)))) (synWral n (synCnnc)
            (.imp (.classMem (.cv n) Y) (synWbr (.cv k) (synCkqrel (synClefin)) (.cv n)))))
        (synWa (synWral n (synCnnc) (.imp (.classMem (.cv n) X) (.classMem (.cv n) Y)))
          (synWral n (synCnnc)
            (.imp (.classMem (.cv n) Y) (.classMem (synCplc (.cv n) (synC1c)) X)))))
  have p0001 := @gSimpr (.classMem (.cv m) X) (.classMem (.cv k) Y)
  have p0002 :=
    @gSyl
      (synW3a (synWa (.classMem (.cv m) (synCnnc)) (.classMem (.cv k) (synCnnc)))
        (synWa (.classMem (.cv m) X) (.classMem (.cv k) Y)) (synWa (synWa
            (synWral n (synCnnc) (.imp (.classMem (.cv n) X)
                (synWbr (.cv m) (synCkqrel (synClefin)) (.cv n)))) (synWral n (synCnnc)
              (.imp (.classMem (.cv n) Y) (synWbr (.cv k) (synCkqrel (synClefin)) (.cv n)))))
          (synWa (synWral n (synCnnc) (.imp (.classMem (.cv n) X) (.classMem (.cv n) Y)))
            (synWral n (synCnnc)
              (.imp (.classMem (.cv n) Y) (.classMem (synCplc (.cv n) (synC1c)) X))))))
      (synWa (.classMem (.cv m) X) (.classMem (.cv k) Y)) (.classMem (.cv k) Y) p0000
      p0001
  have p0003 :=
    @gSimp3 (synWa (.classMem (.cv m) (synCnnc)) (.classMem (.cv k) (synCnnc)))
      (synWa (.classMem (.cv m) X) (.classMem (.cv k) Y))
      (synWa (synWa (synWral n (synCnnc) (.imp (.classMem (.cv n) X)
              (synWbr (.cv m) (synCkqrel (synClefin)) (.cv n)))) (synWral n (synCnnc)
            (.imp (.classMem (.cv n) Y) (synWbr (.cv k) (synCkqrel (synClefin)) (.cv n)))))
        (synWa (synWral n (synCnnc) (.imp (.classMem (.cv n) X) (.classMem (.cv n) Y)))
          (synWral n (synCnnc)
            (.imp (.classMem (.cv n) Y) (.classMem (synCplc (.cv n) (synC1c)) X)))))
  have p0004 :=
    @gSimpr
      (synWa (synWral n (synCnnc) (.imp (.classMem (.cv n) X)
            (synWbr (.cv m) (synCkqrel (synClefin)) (.cv n)))) (synWral n (synCnnc)
          (.imp (.classMem (.cv n) Y) (synWbr (.cv k) (synCkqrel (synClefin)) (.cv n)))))
      (synWa (synWral n (synCnnc) (.imp (.classMem (.cv n) X) (.classMem (.cv n) Y)))
        (synWral n (synCnnc)
          (.imp (.classMem (.cv n) Y) (.classMem (synCplc (.cv n) (synC1c)) X))))
  have p0005 :=
    @gSyl
      (synW3a (synWa (.classMem (.cv m) (synCnnc)) (.classMem (.cv k) (synCnnc)))
        (synWa (.classMem (.cv m) X) (.classMem (.cv k) Y)) (synWa (synWa
            (synWral n (synCnnc) (.imp (.classMem (.cv n) X)
                (synWbr (.cv m) (synCkqrel (synClefin)) (.cv n)))) (synWral n (synCnnc)
              (.imp (.classMem (.cv n) Y) (synWbr (.cv k) (synCkqrel (synClefin)) (.cv n)))))
          (synWa (synWral n (synCnnc) (.imp (.classMem (.cv n) X) (.classMem (.cv n) Y)))
            (synWral n (synCnnc)
              (.imp (.classMem (.cv n) Y) (.classMem (synCplc (.cv n) (synC1c)) X))))))
      (synWa (synWa (synWral n (synCnnc) (.imp (.classMem (.cv n) X)
              (synWbr (.cv m) (synCkqrel (synClefin)) (.cv n)))) (synWral n (synCnnc)
            (.imp (.classMem (.cv n) Y) (synWbr (.cv k) (synCkqrel (synClefin)) (.cv n)))))
        (synWa (synWral n (synCnnc) (.imp (.classMem (.cv n) X) (.classMem (.cv n) Y)))
          (synWral n (synCnnc)
            (.imp (.classMem (.cv n) Y) (.classMem (synCplc (.cv n) (synC1c)) X)))))
      (synWa (synWral n (synCnnc) (.imp (.classMem (.cv n) X) (.classMem (.cv n) Y)))
        (synWral n (synCnnc)
          (.imp (.classMem (.cv n) Y) (.classMem (synCplc (.cv n) (synC1c)) X))))
      p0003 p0004
  have p0006 :=
    @gSimpr (synWral n (synCnnc) (.imp (.classMem (.cv n) X) (.classMem (.cv n) Y)))
      (synWral n (synCnnc)
        (.imp (.classMem (.cv n) Y) (.classMem (synCplc (.cv n) (synC1c)) X)))
  have p0007 :=
    @gSyl
      (synW3a (synWa (.classMem (.cv m) (synCnnc)) (.classMem (.cv k) (synCnnc)))
        (synWa (.classMem (.cv m) X) (.classMem (.cv k) Y)) (synWa (synWa
            (synWral n (synCnnc) (.imp (.classMem (.cv n) X)
                (synWbr (.cv m) (synCkqrel (synClefin)) (.cv n)))) (synWral n (synCnnc)
              (.imp (.classMem (.cv n) Y) (synWbr (.cv k) (synCkqrel (synClefin)) (.cv n)))))
          (synWa (synWral n (synCnnc) (.imp (.classMem (.cv n) X) (.classMem (.cv n) Y)))
            (synWral n (synCnnc)
              (.imp (.classMem (.cv n) Y) (.classMem (synCplc (.cv n) (synC1c)) X))))))
      (synWa (synWral n (synCnnc) (.imp (.classMem (.cv n) X) (.classMem (.cv n) Y)))
        (synWral n (synCnnc)
          (.imp (.classMem (.cv n) Y) (.classMem (synCplc (.cv n) (synC1c)) X))))
      (synWral n (synCnnc)
        (.imp (.classMem (.cv n) Y) (.classMem (synCplc (.cv n) (synC1c)) X)))
      p0005 p0006
  have p0008 :=
    @gSimp1 (synWa (.classMem (.cv m) (synCnnc)) (.classMem (.cv k) (synCnnc)))
      (synWa (.classMem (.cv m) X) (.classMem (.cv k) Y))
      (synWa (synWa (synWral n (synCnnc) (.imp (.classMem (.cv n) X)
              (synWbr (.cv m) (synCkqrel (synClefin)) (.cv n)))) (synWral n (synCnnc)
            (.imp (.classMem (.cv n) Y) (synWbr (.cv k) (synCkqrel (synClefin)) (.cv n)))))
        (synWa (synWral n (synCnnc) (.imp (.classMem (.cv n) X) (.classMem (.cv n) Y)))
          (synWral n (synCnnc)
            (.imp (.classMem (.cv n) Y) (.classMem (synCplc (.cv n) (synC1c)) X)))))
  have p0009 := @gSimpr (.classMem (.cv m) (synCnnc)) (.classMem (.cv k) (synCnnc))
  have p0010 :=
    @gSyl
      (synW3a (synWa (.classMem (.cv m) (synCnnc)) (.classMem (.cv k) (synCnnc)))
        (synWa (.classMem (.cv m) X) (.classMem (.cv k) Y)) (synWa (synWa
            (synWral n (synCnnc) (.imp (.classMem (.cv n) X)
                (synWbr (.cv m) (synCkqrel (synClefin)) (.cv n)))) (synWral n (synCnnc)
              (.imp (.classMem (.cv n) Y) (synWbr (.cv k) (synCkqrel (synClefin)) (.cv n)))))
          (synWa (synWral n (synCnnc) (.imp (.classMem (.cv n) X) (.classMem (.cv n) Y)))
            (synWral n (synCnnc)
              (.imp (.classMem (.cv n) Y) (.classMem (synCplc (.cv n) (synC1c)) X))))))
      (synWa (.classMem (.cv m) (synCnnc)) (.classMem (.cv k) (synCnnc)))
      (.classMem (.cv k) (synCnnc)) p0008 p0009
  have p0011 :=
    @gJca
      (synW3a (synWa (.classMem (.cv m) (synCnnc)) (.classMem (.cv k) (synCnnc)))
        (synWa (.classMem (.cv m) X) (.classMem (.cv k) Y)) (synWa (synWa
            (synWral n (synCnnc) (.imp (.classMem (.cv n) X)
                (synWbr (.cv m) (synCkqrel (synClefin)) (.cv n)))) (synWral n (synCnnc)
              (.imp (.classMem (.cv n) Y) (synWbr (.cv k) (synCkqrel (synClefin)) (.cv n)))))
          (synWa (synWral n (synCnnc) (.imp (.classMem (.cv n) X) (.classMem (.cv n) Y)))
            (synWral n (synCnnc)
              (.imp (.classMem (.cv n) Y) (.classMem (synCplc (.cv n) (synC1c)) X))))))
      (synWral n (synCnnc)
        (.imp (.classMem (.cv n) Y) (.classMem (synCplc (.cv n) (synC1c)) X)))
      (.classMem (.cv k) (synCnnc)) p0007 p0010
  have p0012 := @gEleq1 (.cv n) (.cv k) Y
  have p0013 := @gAddceq1 (.cv n) (.cv k) (synC1c)
  have p0014 :=
    @gEleq1d (.classEq (.cv n) (.cv k)) (synCplc (.cv n) (synC1c))
      (synCplc (.cv k) (synC1c)) X p0013
  have p0015 :=
    @gImbi12d (.classEq (.cv n) (.cv k)) (.classMem (.cv n) Y) (.classMem (.cv k) Y)
      (.classMem (synCplc (.cv n) (synC1c)) X)
      (.classMem (synCplc (.cv k) (synC1c)) X) p0012 p0014
  have p0016 :=
    @gRspccva (.imp (.classMem (.cv n) Y) (.classMem (synCplc (.cv n) (synC1c)) X))
      (.imp (.classMem (.cv k) Y) (.classMem (synCplc (.cv k) (synC1c)) X)) n (.cv k)
      (synCnnc) dv_cache_0001 dv_cache_0002 dv_cache_0003 p0015
  have p0017 :=
    @gSyl
      (synW3a (synWa (.classMem (.cv m) (synCnnc)) (.classMem (.cv k) (synCnnc)))
        (synWa (.classMem (.cv m) X) (.classMem (.cv k) Y)) (synWa (synWa
            (synWral n (synCnnc) (.imp (.classMem (.cv n) X)
                (synWbr (.cv m) (synCkqrel (synClefin)) (.cv n)))) (synWral n (synCnnc)
              (.imp (.classMem (.cv n) Y) (synWbr (.cv k) (synCkqrel (synClefin)) (.cv n)))))
          (synWa (synWral n (synCnnc) (.imp (.classMem (.cv n) X) (.classMem (.cv n) Y)))
            (synWral n (synCnnc)
              (.imp (.classMem (.cv n) Y) (.classMem (synCplc (.cv n) (synC1c)) X))))))
      (synWa (synWral n (synCnnc)
          (.imp (.classMem (.cv n) Y) (.classMem (synCplc (.cv n) (synC1c)) X)))
        (.classMem (.cv k) (synCnnc)))
      (.imp (.classMem (.cv k) Y) (.classMem (synCplc (.cv k) (synC1c)) X)) p0011 p0016
  have p0018 :=
    @gMpd
      (synW3a (synWa (.classMem (.cv m) (synCnnc)) (.classMem (.cv k) (synCnnc)))
        (synWa (.classMem (.cv m) X) (.classMem (.cv k) Y)) (synWa (synWa
            (synWral n (synCnnc) (.imp (.classMem (.cv n) X)
                (synWbr (.cv m) (synCkqrel (synClefin)) (.cv n)))) (synWral n (synCnnc)
              (.imp (.classMem (.cv n) Y) (synWbr (.cv k) (synCkqrel (synClefin)) (.cv n)))))
          (synWa (synWral n (synCnnc) (.imp (.classMem (.cv n) X) (.classMem (.cv n) Y)))
            (synWral n (synCnnc)
              (.imp (.classMem (.cv n) Y) (.classMem (synCplc (.cv n) (synC1c)) X))))))
      (.classMem (.cv k) Y) (.classMem (synCplc (.cv k) (synC1c)) X) p0002 p0017
  have p0020 :=
    @gSimpl
      (synWa (synWral n (synCnnc) (.imp (.classMem (.cv n) X)
            (synWbr (.cv m) (synCkqrel (synClefin)) (.cv n)))) (synWral n (synCnnc)
          (.imp (.classMem (.cv n) Y) (synWbr (.cv k) (synCkqrel (synClefin)) (.cv n)))))
      (synWa (synWral n (synCnnc) (.imp (.classMem (.cv n) X) (.classMem (.cv n) Y)))
        (synWral n (synCnnc)
          (.imp (.classMem (.cv n) Y) (.classMem (synCplc (.cv n) (synC1c)) X))))
  have p0021 :=
    @gSyl
      (synW3a (synWa (.classMem (.cv m) (synCnnc)) (.classMem (.cv k) (synCnnc)))
        (synWa (.classMem (.cv m) X) (.classMem (.cv k) Y)) (synWa (synWa
            (synWral n (synCnnc) (.imp (.classMem (.cv n) X)
                (synWbr (.cv m) (synCkqrel (synClefin)) (.cv n)))) (synWral n (synCnnc)
              (.imp (.classMem (.cv n) Y) (synWbr (.cv k) (synCkqrel (synClefin)) (.cv n)))))
          (synWa (synWral n (synCnnc) (.imp (.classMem (.cv n) X) (.classMem (.cv n) Y)))
            (synWral n (synCnnc)
              (.imp (.classMem (.cv n) Y) (.classMem (synCplc (.cv n) (synC1c)) X))))))
      (synWa (synWa (synWral n (synCnnc) (.imp (.classMem (.cv n) X)
              (synWbr (.cv m) (synCkqrel (synClefin)) (.cv n)))) (synWral n (synCnnc)
            (.imp (.classMem (.cv n) Y) (synWbr (.cv k) (synCkqrel (synClefin)) (.cv n)))))
        (synWa (synWral n (synCnnc) (.imp (.classMem (.cv n) X) (.classMem (.cv n) Y)))
          (synWral n (synCnnc)
            (.imp (.classMem (.cv n) Y) (.classMem (synCplc (.cv n) (synC1c)) X)))))
      (synWa (synWral n (synCnnc) (.imp (.classMem (.cv n) X)
            (synWbr (.cv m) (synCkqrel (synClefin)) (.cv n)))) (synWral n (synCnnc)
          (.imp (.classMem (.cv n) Y) (synWbr (.cv k) (synCkqrel (synClefin)) (.cv n)))))
      p0003 p0020
  have p0022 :=
    @gSimpl
      (synWral n (synCnnc)
        (.imp (.classMem (.cv n) X) (synWbr (.cv m) (synCkqrel (synClefin)) (.cv n))))
      (synWral n (synCnnc)
        (.imp (.classMem (.cv n) Y) (synWbr (.cv k) (synCkqrel (synClefin)) (.cv n))))
  have p0023 :=
    @gSyl
      (synW3a (synWa (.classMem (.cv m) (synCnnc)) (.classMem (.cv k) (synCnnc)))
        (synWa (.classMem (.cv m) X) (.classMem (.cv k) Y)) (synWa (synWa
            (synWral n (synCnnc) (.imp (.classMem (.cv n) X)
                (synWbr (.cv m) (synCkqrel (synClefin)) (.cv n)))) (synWral n (synCnnc)
              (.imp (.classMem (.cv n) Y) (synWbr (.cv k) (synCkqrel (synClefin)) (.cv n)))))
          (synWa (synWral n (synCnnc) (.imp (.classMem (.cv n) X) (.classMem (.cv n) Y)))
            (synWral n (synCnnc)
              (.imp (.classMem (.cv n) Y) (.classMem (synCplc (.cv n) (synC1c)) X))))))
      (synWa (synWral n (synCnnc) (.imp (.classMem (.cv n) X)
            (synWbr (.cv m) (synCkqrel (synClefin)) (.cv n)))) (synWral n (synCnnc)
          (.imp (.classMem (.cv n) Y) (synWbr (.cv k) (synCkqrel (synClefin)) (.cv n)))))
      (synWral n (synCnnc)
        (.imp (.classMem (.cv n) X) (synWbr (.cv m) (synCkqrel (synClefin)) (.cv n))))
      p0021 p0022
  have p0027 := @gPeano2 (.cv k)
  have p0028 :=
    @gSyl
      (synW3a (synWa (.classMem (.cv m) (synCnnc)) (.classMem (.cv k) (synCnnc)))
        (synWa (.classMem (.cv m) X) (.classMem (.cv k) Y)) (synWa (synWa
            (synWral n (synCnnc) (.imp (.classMem (.cv n) X)
                (synWbr (.cv m) (synCkqrel (synClefin)) (.cv n)))) (synWral n (synCnnc)
              (.imp (.classMem (.cv n) Y) (synWbr (.cv k) (synCkqrel (synClefin)) (.cv n)))))
          (synWa (synWral n (synCnnc) (.imp (.classMem (.cv n) X) (.classMem (.cv n) Y)))
            (synWral n (synCnnc)
              (.imp (.classMem (.cv n) Y) (.classMem (synCplc (.cv n) (synC1c)) X))))))
      (.classMem (.cv k) (synCnnc)) (.classMem (synCplc (.cv k) (synC1c)) (synCnnc))
      p0010 p0027
  have p0029 :=
    @gJca
      (synW3a (synWa (.classMem (.cv m) (synCnnc)) (.classMem (.cv k) (synCnnc)))
        (synWa (.classMem (.cv m) X) (.classMem (.cv k) Y)) (synWa (synWa
            (synWral n (synCnnc) (.imp (.classMem (.cv n) X)
                (synWbr (.cv m) (synCkqrel (synClefin)) (.cv n)))) (synWral n (synCnnc)
              (.imp (.classMem (.cv n) Y) (synWbr (.cv k) (synCkqrel (synClefin)) (.cv n)))))
          (synWa (synWral n (synCnnc) (.imp (.classMem (.cv n) X) (.classMem (.cv n) Y)))
            (synWral n (synCnnc)
              (.imp (.classMem (.cv n) Y) (.classMem (synCplc (.cv n) (synC1c)) X))))))
      (synWral n (synCnnc)
        (.imp (.classMem (.cv n) X) (synWbr (.cv m) (synCkqrel (synClefin)) (.cv n))))
      (.classMem (synCplc (.cv k) (synC1c)) (synCnnc)) p0023 p0028
  have p0030 := @gEleq1 (.cv n) (synCplc (.cv k) (synC1c)) X
  have p0031 :=
    @gBreq2 (.cv n) (synCplc (.cv k) (synC1c)) (.cv m) (synCkqrel (synClefin))
  have p0032 :=
    @gImbi12d (.classEq (.cv n) (synCplc (.cv k) (synC1c))) (.classMem (.cv n) X)
      (.classMem (synCplc (.cv k) (synC1c)) X)
      (synWbr (.cv m) (synCkqrel (synClefin)) (.cv n))
      (synWbr (.cv m) (synCkqrel (synClefin)) (synCplc (.cv k) (synC1c))) p0030 p0031
  have p0033 :=
    @gRspccva
      (.imp (.classMem (.cv n) X) (synWbr (.cv m) (synCkqrel (synClefin)) (.cv n)))
      (.imp (.classMem (synCplc (.cv k) (synC1c)) X)
        (synWbr (.cv m) (synCkqrel (synClefin)) (synCplc (.cv k) (synC1c))))
      n (synCplc (.cv k) (synC1c)) (synCnnc) dv_cache_0004 dv_cache_0002 dv_cache_0005
      p0032
  have p0034 :=
    @gSyl
      (synW3a (synWa (.classMem (.cv m) (synCnnc)) (.classMem (.cv k) (synCnnc)))
        (synWa (.classMem (.cv m) X) (.classMem (.cv k) Y)) (synWa (synWa
            (synWral n (synCnnc) (.imp (.classMem (.cv n) X)
                (synWbr (.cv m) (synCkqrel (synClefin)) (.cv n)))) (synWral n (synCnnc)
              (.imp (.classMem (.cv n) Y) (synWbr (.cv k) (synCkqrel (synClefin)) (.cv n)))))
          (synWa (synWral n (synCnnc) (.imp (.classMem (.cv n) X) (.classMem (.cv n) Y)))
            (synWral n (synCnnc)
              (.imp (.classMem (.cv n) Y) (.classMem (synCplc (.cv n) (synC1c)) X))))))
      (synWa (synWral n (synCnnc) (.imp (.classMem (.cv n) X)
            (synWbr (.cv m) (synCkqrel (synClefin)) (.cv n))))
        (.classMem (synCplc (.cv k) (synC1c)) (synCnnc)))
      (.imp (.classMem (synCplc (.cv k) (synC1c)) X)
        (synWbr (.cv m) (synCkqrel (synClefin)) (synCplc (.cv k) (synC1c))))
      p0029 p0033
  have p0035 :=
    @gMpd
      (synW3a (synWa (.classMem (.cv m) (synCnnc)) (.classMem (.cv k) (synCnnc)))
        (synWa (.classMem (.cv m) X) (.classMem (.cv k) Y)) (synWa (synWa
            (synWral n (synCnnc) (.imp (.classMem (.cv n) X)
                (synWbr (.cv m) (synCkqrel (synClefin)) (.cv n)))) (synWral n (synCnnc)
              (.imp (.classMem (.cv n) Y) (synWbr (.cv k) (synCkqrel (synClefin)) (.cv n)))))
          (synWa (synWral n (synCnnc) (.imp (.classMem (.cv n) X) (.classMem (.cv n) Y)))
            (synWral n (synCnnc)
              (.imp (.classMem (.cv n) Y) (.classMem (synCplc (.cv n) (synC1c)) X))))))
      (.classMem (synCplc (.cv k) (synC1c)) X)
      (synWbr (.cv m) (synCkqrel (synClefin)) (synCplc (.cv k) (synC1c))) p0018 p0034
  have p0040 := @gSimpl (.classMem (.cv m) (synCnnc)) (.classMem (.cv k) (synCnnc))
  have p0041 :=
    @gSyl
      (synW3a (synWa (.classMem (.cv m) (synCnnc)) (.classMem (.cv k) (synCnnc)))
        (synWa (.classMem (.cv m) X) (.classMem (.cv k) Y)) (synWa (synWa
            (synWral n (synCnnc) (.imp (.classMem (.cv n) X)
                (synWbr (.cv m) (synCkqrel (synClefin)) (.cv n)))) (synWral n (synCnnc)
              (.imp (.classMem (.cv n) Y) (synWbr (.cv k) (synCkqrel (synClefin)) (.cv n)))))
          (synWa (synWral n (synCnnc) (.imp (.classMem (.cv n) X) (.classMem (.cv n) Y)))
            (synWral n (synCnnc)
              (.imp (.classMem (.cv n) Y) (.classMem (synCplc (.cv n) (synC1c)) X))))))
      (synWa (.classMem (.cv m) (synCnnc)) (.classMem (.cv k) (synCnnc)))
      (.classMem (.cv m) (synCnnc)) p0008 p0040
  have p0042 :=
    @gJca
      (synW3a (synWa (.classMem (.cv m) (synCnnc)) (.classMem (.cv k) (synCnnc)))
        (synWa (.classMem (.cv m) X) (.classMem (.cv k) Y)) (synWa (synWa
            (synWral n (synCnnc) (.imp (.classMem (.cv n) X)
                (synWbr (.cv m) (synCkqrel (synClefin)) (.cv n)))) (synWral n (synCnnc)
              (.imp (.classMem (.cv n) Y) (synWbr (.cv k) (synCkqrel (synClefin)) (.cv n)))))
          (synWa (synWral n (synCnnc) (.imp (.classMem (.cv n) X) (.classMem (.cv n) Y)))
            (synWral n (synCnnc)
              (.imp (.classMem (.cv n) Y) (.classMem (synCplc (.cv n) (synC1c)) X))))))
      (.classMem (.cv k) (synCnnc)) (.classMem (.cv m) (synCnnc)) p0010 p0041
  have p0043 := @gKqfinsucsplit (.cv k) (.cv m)
  have p0044 :=
    @gSyl
      (synW3a (synWa (.classMem (.cv m) (synCnnc)) (.classMem (.cv k) (synCnnc)))
        (synWa (.classMem (.cv m) X) (.classMem (.cv k) Y)) (synWa (synWa
            (synWral n (synCnnc) (.imp (.classMem (.cv n) X)
                (synWbr (.cv m) (synCkqrel (synClefin)) (.cv n)))) (synWral n (synCnnc)
              (.imp (.classMem (.cv n) Y) (synWbr (.cv k) (synCkqrel (synClefin)) (.cv n)))))
          (synWa (synWral n (synCnnc) (.imp (.classMem (.cv n) X) (.classMem (.cv n) Y)))
            (synWral n (synCnnc)
              (.imp (.classMem (.cv n) Y) (.classMem (synCplc (.cv n) (synC1c)) X))))))
      (synWa (.classMem (.cv k) (synCnnc)) (.classMem (.cv m) (synCnnc)))
      (synWb (synWbr (.cv m) (synCkqrel (synClefin)) (synCplc (.cv k) (synC1c)))
        (synWo (synWbr (.cv m) (synCkqrel (synClefin)) (.cv k))
          (.classEq (.cv m) (synCplc (.cv k) (synC1c)))))
      p0042 p0043
  have p0045 :=
    @gBiimpd
      (synW3a (synWa (.classMem (.cv m) (synCnnc)) (.classMem (.cv k) (synCnnc)))
        (synWa (.classMem (.cv m) X) (.classMem (.cv k) Y)) (synWa (synWa
            (synWral n (synCnnc) (.imp (.classMem (.cv n) X)
                (synWbr (.cv m) (synCkqrel (synClefin)) (.cv n)))) (synWral n (synCnnc)
              (.imp (.classMem (.cv n) Y) (synWbr (.cv k) (synCkqrel (synClefin)) (.cv n)))))
          (synWa (synWral n (synCnnc) (.imp (.classMem (.cv n) X) (.classMem (.cv n) Y)))
            (synWral n (synCnnc)
              (.imp (.classMem (.cv n) Y) (.classMem (synCplc (.cv n) (synC1c)) X))))))
      (synWbr (.cv m) (synCkqrel (synClefin)) (synCplc (.cv k) (synC1c)))
      (synWo (synWbr (.cv m) (synCkqrel (synClefin)) (.cv k))
        (.classEq (.cv m) (synCplc (.cv k) (synC1c))))
      p0044
  have p0046 :=
    @gMpd
      (synW3a (synWa (.classMem (.cv m) (synCnnc)) (.classMem (.cv k) (synCnnc)))
        (synWa (.classMem (.cv m) X) (.classMem (.cv k) Y)) (synWa (synWa
            (synWral n (synCnnc) (.imp (.classMem (.cv n) X)
                (synWbr (.cv m) (synCkqrel (synClefin)) (.cv n)))) (synWral n (synCnnc)
              (.imp (.classMem (.cv n) Y) (synWbr (.cv k) (synCkqrel (synClefin)) (.cv n)))))
          (synWa (synWral n (synCnnc) (.imp (.classMem (.cv n) X) (.classMem (.cv n) Y)))
            (synWral n (synCnnc)
              (.imp (.classMem (.cv n) Y) (.classMem (synCplc (.cv n) (synC1c)) X))))))
      (synWbr (.cv m) (synCkqrel (synClefin)) (synCplc (.cv k) (synC1c)))
      (synWo (synWbr (.cv m) (synCkqrel (synClefin)) (.cv k))
        (.classEq (.cv m) (synCplc (.cv k) (synC1c))))
      p0035 p0045
  have p0047 :=
    @gSimpr
      (synW3a (synWa (.classMem (.cv m) (synCnnc)) (.classMem (.cv k) (synCnnc)))
        (synWa (.classMem (.cv m) X) (.classMem (.cv k) Y)) (synWa (synWa
            (synWral n (synCnnc) (.imp (.classMem (.cv n) X)
                (synWbr (.cv m) (synCkqrel (synClefin)) (.cv n)))) (synWral n (synCnnc)
              (.imp (.classMem (.cv n) Y) (synWbr (.cv k) (synCkqrel (synClefin)) (.cv n)))))
          (synWa (synWral n (synCnnc) (.imp (.classMem (.cv n) X) (.classMem (.cv n) Y)))
            (synWral n (synCnnc)
              (.imp (.classMem (.cv n) Y) (.classMem (synCplc (.cv n) (synC1c)) X))))))
      (synWbr (.cv m) (synCkqrel (synClefin)) (.cv k))
  have p0048 :=
    @gSimpl
      (synW3a (synWa (.classMem (.cv m) (synCnnc)) (.classMem (.cv k) (synCnnc)))
        (synWa (.classMem (.cv m) X) (.classMem (.cv k) Y)) (synWa (synWa
            (synWral n (synCnnc) (.imp (.classMem (.cv n) X)
                (synWbr (.cv m) (synCkqrel (synClefin)) (.cv n)))) (synWral n (synCnnc)
              (.imp (.classMem (.cv n) Y) (synWbr (.cv k) (synCkqrel (synClefin)) (.cv n)))))
          (synWa (synWral n (synCnnc) (.imp (.classMem (.cv n) X) (.classMem (.cv n) Y)))
            (synWral n (synCnnc)
              (.imp (.classMem (.cv n) Y) (.classMem (synCplc (.cv n) (synC1c)) X))))))
      (synWbr (.cv m) (synCkqrel (synClefin)) (.cv k))
  have p0050 := @gSimpl (.classMem (.cv m) X) (.classMem (.cv k) Y)
  have p0051 :=
    @gSyl
      (synW3a (synWa (.classMem (.cv m) (synCnnc)) (.classMem (.cv k) (synCnnc)))
        (synWa (.classMem (.cv m) X) (.classMem (.cv k) Y)) (synWa (synWa
            (synWral n (synCnnc) (.imp (.classMem (.cv n) X)
                (synWbr (.cv m) (synCkqrel (synClefin)) (.cv n)))) (synWral n (synCnnc)
              (.imp (.classMem (.cv n) Y) (synWbr (.cv k) (synCkqrel (synClefin)) (.cv n)))))
          (synWa (synWral n (synCnnc) (.imp (.classMem (.cv n) X) (.classMem (.cv n) Y)))
            (synWral n (synCnnc)
              (.imp (.classMem (.cv n) Y) (.classMem (synCplc (.cv n) (synC1c)) X))))))
      (synWa (.classMem (.cv m) X) (.classMem (.cv k) Y)) (.classMem (.cv m) X) p0000
      p0050
  have p0055 :=
    @gSimpl (synWral n (synCnnc) (.imp (.classMem (.cv n) X) (.classMem (.cv n) Y)))
      (synWral n (synCnnc)
        (.imp (.classMem (.cv n) Y) (.classMem (synCplc (.cv n) (synC1c)) X)))
  have p0056 :=
    @gSyl
      (synW3a (synWa (.classMem (.cv m) (synCnnc)) (.classMem (.cv k) (synCnnc)))
        (synWa (.classMem (.cv m) X) (.classMem (.cv k) Y)) (synWa (synWa
            (synWral n (synCnnc) (.imp (.classMem (.cv n) X)
                (synWbr (.cv m) (synCkqrel (synClefin)) (.cv n)))) (synWral n (synCnnc)
              (.imp (.classMem (.cv n) Y) (synWbr (.cv k) (synCkqrel (synClefin)) (.cv n)))))
          (synWa (synWral n (synCnnc) (.imp (.classMem (.cv n) X) (.classMem (.cv n) Y)))
            (synWral n (synCnnc)
              (.imp (.classMem (.cv n) Y) (.classMem (synCplc (.cv n) (synC1c)) X))))))
      (synWa (synWral n (synCnnc) (.imp (.classMem (.cv n) X) (.classMem (.cv n) Y)))
        (synWral n (synCnnc)
          (.imp (.classMem (.cv n) Y) (.classMem (synCplc (.cv n) (synC1c)) X))))
      (synWral n (synCnnc) (.imp (.classMem (.cv n) X) (.classMem (.cv n) Y))) p0005
      p0055
  have p0060 :=
    @gJca
      (synW3a (synWa (.classMem (.cv m) (synCnnc)) (.classMem (.cv k) (synCnnc)))
        (synWa (.classMem (.cv m) X) (.classMem (.cv k) Y)) (synWa (synWa
            (synWral n (synCnnc) (.imp (.classMem (.cv n) X)
                (synWbr (.cv m) (synCkqrel (synClefin)) (.cv n)))) (synWral n (synCnnc)
              (.imp (.classMem (.cv n) Y) (synWbr (.cv k) (synCkqrel (synClefin)) (.cv n)))))
          (synWa (synWral n (synCnnc) (.imp (.classMem (.cv n) X) (.classMem (.cv n) Y)))
            (synWral n (synCnnc)
              (.imp (.classMem (.cv n) Y) (.classMem (synCplc (.cv n) (synC1c)) X))))))
      (synWral n (synCnnc) (.imp (.classMem (.cv n) X) (.classMem (.cv n) Y)))
      (.classMem (.cv m) (synCnnc)) p0056 p0041
  have p0061 := @gEleq1 (.cv n) (.cv m) X
  have p0062 := @gEleq1 (.cv n) (.cv m) Y
  have p0063 :=
    @gImbi12d (.classEq (.cv n) (.cv m)) (.classMem (.cv n) X) (.classMem (.cv m) X)
      (.classMem (.cv n) Y) (.classMem (.cv m) Y) p0061 p0062
  have p0064 :=
    @gRspccva (.imp (.classMem (.cv n) X) (.classMem (.cv n) Y))
      (.imp (.classMem (.cv m) X) (.classMem (.cv m) Y)) n (.cv m) (synCnnc)
      dv_cache_0006 dv_cache_0002 dv_cache_0007 p0063
  have p0065 :=
    @gSyl
      (synW3a (synWa (.classMem (.cv m) (synCnnc)) (.classMem (.cv k) (synCnnc)))
        (synWa (.classMem (.cv m) X) (.classMem (.cv k) Y)) (synWa (synWa
            (synWral n (synCnnc) (.imp (.classMem (.cv n) X)
                (synWbr (.cv m) (synCkqrel (synClefin)) (.cv n)))) (synWral n (synCnnc)
              (.imp (.classMem (.cv n) Y) (synWbr (.cv k) (synCkqrel (synClefin)) (.cv n)))))
          (synWa (synWral n (synCnnc) (.imp (.classMem (.cv n) X) (.classMem (.cv n) Y)))
            (synWral n (synCnnc)
              (.imp (.classMem (.cv n) Y) (.classMem (synCplc (.cv n) (synC1c)) X))))))
      (synWa (synWral n (synCnnc) (.imp (.classMem (.cv n) X) (.classMem (.cv n) Y)))
        (.classMem (.cv m) (synCnnc)))
      (.imp (.classMem (.cv m) X) (.classMem (.cv m) Y)) p0060 p0064
  have p0066 :=
    @gMpd
      (synW3a (synWa (.classMem (.cv m) (synCnnc)) (.classMem (.cv k) (synCnnc)))
        (synWa (.classMem (.cv m) X) (.classMem (.cv k) Y)) (synWa (synWa
            (synWral n (synCnnc) (.imp (.classMem (.cv n) X)
                (synWbr (.cv m) (synCkqrel (synClefin)) (.cv n)))) (synWral n (synCnnc)
              (.imp (.classMem (.cv n) Y) (synWbr (.cv k) (synCkqrel (synClefin)) (.cv n)))))
          (synWa (synWral n (synCnnc) (.imp (.classMem (.cv n) X) (.classMem (.cv n) Y)))
            (synWral n (synCnnc)
              (.imp (.classMem (.cv n) Y) (.classMem (synCplc (.cv n) (synC1c)) X))))))
      (.classMem (.cv m) X) (.classMem (.cv m) Y) p0051 p0065
  have p0070 :=
    @gSimpr
      (synWral n (synCnnc)
        (.imp (.classMem (.cv n) X) (synWbr (.cv m) (synCkqrel (synClefin)) (.cv n))))
      (synWral n (synCnnc)
        (.imp (.classMem (.cv n) Y) (synWbr (.cv k) (synCkqrel (synClefin)) (.cv n))))
  have p0071 :=
    @gSyl
      (synW3a (synWa (.classMem (.cv m) (synCnnc)) (.classMem (.cv k) (synCnnc)))
        (synWa (.classMem (.cv m) X) (.classMem (.cv k) Y)) (synWa (synWa
            (synWral n (synCnnc) (.imp (.classMem (.cv n) X)
                (synWbr (.cv m) (synCkqrel (synClefin)) (.cv n)))) (synWral n (synCnnc)
              (.imp (.classMem (.cv n) Y) (synWbr (.cv k) (synCkqrel (synClefin)) (.cv n)))))
          (synWa (synWral n (synCnnc) (.imp (.classMem (.cv n) X) (.classMem (.cv n) Y)))
            (synWral n (synCnnc)
              (.imp (.classMem (.cv n) Y) (.classMem (synCplc (.cv n) (synC1c)) X))))))
      (synWa (synWral n (synCnnc) (.imp (.classMem (.cv n) X)
            (synWbr (.cv m) (synCkqrel (synClefin)) (.cv n)))) (synWral n (synCnnc)
          (.imp (.classMem (.cv n) Y) (synWbr (.cv k) (synCkqrel (synClefin)) (.cv n)))))
      (synWral n (synCnnc)
        (.imp (.classMem (.cv n) Y) (synWbr (.cv k) (synCkqrel (synClefin)) (.cv n))))
      p0021 p0070
  have p0075 :=
    @gJca
      (synW3a (synWa (.classMem (.cv m) (synCnnc)) (.classMem (.cv k) (synCnnc)))
        (synWa (.classMem (.cv m) X) (.classMem (.cv k) Y)) (synWa (synWa
            (synWral n (synCnnc) (.imp (.classMem (.cv n) X)
                (synWbr (.cv m) (synCkqrel (synClefin)) (.cv n)))) (synWral n (synCnnc)
              (.imp (.classMem (.cv n) Y) (synWbr (.cv k) (synCkqrel (synClefin)) (.cv n)))))
          (synWa (synWral n (synCnnc) (.imp (.classMem (.cv n) X) (.classMem (.cv n) Y)))
            (synWral n (synCnnc)
              (.imp (.classMem (.cv n) Y) (.classMem (synCplc (.cv n) (synC1c)) X))))))
      (synWral n (synCnnc)
        (.imp (.classMem (.cv n) Y) (synWbr (.cv k) (synCkqrel (synClefin)) (.cv n))))
      (.classMem (.cv m) (synCnnc)) p0071 p0041
  have p0077 := @gBreq2 (.cv n) (.cv m) (.cv k) (synCkqrel (synClefin))
  have p0078 :=
    @gImbi12d (.classEq (.cv n) (.cv m)) (.classMem (.cv n) Y) (.classMem (.cv m) Y)
      (synWbr (.cv k) (synCkqrel (synClefin)) (.cv n))
      (synWbr (.cv k) (synCkqrel (synClefin)) (.cv m)) p0062 p0077
  have p0079 :=
    @gRspccva
      (.imp (.classMem (.cv n) Y) (synWbr (.cv k) (synCkqrel (synClefin)) (.cv n)))
      (.imp (.classMem (.cv m) Y) (synWbr (.cv k) (synCkqrel (synClefin)) (.cv m))) n
      (.cv m) (synCnnc) dv_cache_0006 dv_cache_0002 dv_cache_0008 p0078
  have p0080 :=
    @gSyl
      (synW3a (synWa (.classMem (.cv m) (synCnnc)) (.classMem (.cv k) (synCnnc)))
        (synWa (.classMem (.cv m) X) (.classMem (.cv k) Y)) (synWa (synWa
            (synWral n (synCnnc) (.imp (.classMem (.cv n) X)
                (synWbr (.cv m) (synCkqrel (synClefin)) (.cv n)))) (synWral n (synCnnc)
              (.imp (.classMem (.cv n) Y) (synWbr (.cv k) (synCkqrel (synClefin)) (.cv n)))))
          (synWa (synWral n (synCnnc) (.imp (.classMem (.cv n) X) (.classMem (.cv n) Y)))
            (synWral n (synCnnc)
              (.imp (.classMem (.cv n) Y) (.classMem (synCplc (.cv n) (synC1c)) X))))))
      (synWa (synWral n (synCnnc) (.imp (.classMem (.cv n) Y)
            (synWbr (.cv k) (synCkqrel (synClefin)) (.cv n))))
        (.classMem (.cv m) (synCnnc)))
      (.imp (.classMem (.cv m) Y) (synWbr (.cv k) (synCkqrel (synClefin)) (.cv m)))
      p0075 p0079
  have p0081 :=
    @gMpd
      (synW3a (synWa (.classMem (.cv m) (synCnnc)) (.classMem (.cv k) (synCnnc)))
        (synWa (.classMem (.cv m) X) (.classMem (.cv k) Y)) (synWa (synWa
            (synWral n (synCnnc) (.imp (.classMem (.cv n) X)
                (synWbr (.cv m) (synCkqrel (synClefin)) (.cv n)))) (synWral n (synCnnc)
              (.imp (.classMem (.cv n) Y) (synWbr (.cv k) (synCkqrel (synClefin)) (.cv n)))))
          (synWa (synWral n (synCnnc) (.imp (.classMem (.cv n) X) (.classMem (.cv n) Y)))
            (synWral n (synCnnc)
              (.imp (.classMem (.cv n) Y) (.classMem (synCplc (.cv n) (synC1c)) X))))))
      (.classMem (.cv m) Y) (synWbr (.cv k) (synCkqrel (synClefin)) (.cv m)) p0066
      p0080
  have p0082 :=
    @gSyl
      (synWa (synW3a (synWa (.classMem (.cv m) (synCnnc)) (.classMem (.cv k) (synCnnc)))
          (synWa (.classMem (.cv m) X) (.classMem (.cv k) Y)) (synWa (synWa
              (synWral n (synCnnc) (.imp (.classMem (.cv n) X)
                  (synWbr (.cv m) (synCkqrel (synClefin)) (.cv n)))) (synWral n (synCnnc)
                (.imp (.classMem (.cv n) Y)
                  (synWbr (.cv k) (synCkqrel (synClefin)) (.cv n))))) (synWa
              (synWral n (synCnnc) (.imp (.classMem (.cv n) X) (.classMem (.cv n) Y)))
              (synWral n (synCnnc) (.imp (.classMem (.cv n) Y)
                  (.classMem (synCplc (.cv n) (synC1c)) X))))))
        (synWbr (.cv m) (synCkqrel (synClefin)) (.cv k)))
      (synW3a (synWa (.classMem (.cv m) (synCnnc)) (.classMem (.cv k) (synCnnc)))
        (synWa (.classMem (.cv m) X) (.classMem (.cv k) Y)) (synWa (synWa
            (synWral n (synCnnc) (.imp (.classMem (.cv n) X)
                (synWbr (.cv m) (synCkqrel (synClefin)) (.cv n)))) (synWral n (synCnnc)
              (.imp (.classMem (.cv n) Y) (synWbr (.cv k) (synCkqrel (synClefin)) (.cv n)))))
          (synWa (synWral n (synCnnc) (.imp (.classMem (.cv n) X) (.classMem (.cv n) Y)))
            (synWral n (synCnnc)
              (.imp (.classMem (.cv n) Y) (.classMem (synCplc (.cv n) (synC1c)) X))))))
      (synWbr (.cv k) (synCkqrel (synClefin)) (.cv m)) p0048 p0081
  have p0083 :=
    @gJca
      (synWa (synW3a (synWa (.classMem (.cv m) (synCnnc)) (.classMem (.cv k) (synCnnc)))
          (synWa (.classMem (.cv m) X) (.classMem (.cv k) Y)) (synWa (synWa
              (synWral n (synCnnc) (.imp (.classMem (.cv n) X)
                  (synWbr (.cv m) (synCkqrel (synClefin)) (.cv n)))) (synWral n (synCnnc)
                (.imp (.classMem (.cv n) Y)
                  (synWbr (.cv k) (synCkqrel (synClefin)) (.cv n))))) (synWa
              (synWral n (synCnnc) (.imp (.classMem (.cv n) X) (.classMem (.cv n) Y)))
              (synWral n (synCnnc) (.imp (.classMem (.cv n) Y)
                  (.classMem (synCplc (.cv n) (synC1c)) X))))))
        (synWbr (.cv m) (synCkqrel (synClefin)) (.cv k)))
      (synWbr (.cv m) (synCkqrel (synClefin)) (.cv k))
      (synWbr (.cv k) (synCkqrel (synClefin)) (.cv m)) p0047 p0082
  have p0086 := @gKqfinantinn (.cv m) (.cv k)
  have p0087 :=
    @gSyl
      (synW3a (synWa (.classMem (.cv m) (synCnnc)) (.classMem (.cv k) (synCnnc)))
        (synWa (.classMem (.cv m) X) (.classMem (.cv k) Y)) (synWa (synWa
            (synWral n (synCnnc) (.imp (.classMem (.cv n) X)
                (synWbr (.cv m) (synCkqrel (synClefin)) (.cv n)))) (synWral n (synCnnc)
              (.imp (.classMem (.cv n) Y) (synWbr (.cv k) (synCkqrel (synClefin)) (.cv n)))))
          (synWa (synWral n (synCnnc) (.imp (.classMem (.cv n) X) (.classMem (.cv n) Y)))
            (synWral n (synCnnc)
              (.imp (.classMem (.cv n) Y) (.classMem (synCplc (.cv n) (synC1c)) X))))))
      (synWa (.classMem (.cv m) (synCnnc)) (.classMem (.cv k) (synCnnc)))
      (.imp (synWa (synWbr (.cv m) (synCkqrel (synClefin)) (.cv k))
          (synWbr (.cv k) (synCkqrel (synClefin)) (.cv m))) (.classEq (.cv m) (.cv k)))
      p0008 p0086
  have p0088 :=
    @gSyl
      (synWa (synW3a (synWa (.classMem (.cv m) (synCnnc)) (.classMem (.cv k) (synCnnc)))
          (synWa (.classMem (.cv m) X) (.classMem (.cv k) Y)) (synWa (synWa
              (synWral n (synCnnc) (.imp (.classMem (.cv n) X)
                  (synWbr (.cv m) (synCkqrel (synClefin)) (.cv n)))) (synWral n (synCnnc)
                (.imp (.classMem (.cv n) Y)
                  (synWbr (.cv k) (synCkqrel (synClefin)) (.cv n))))) (synWa
              (synWral n (synCnnc) (.imp (.classMem (.cv n) X) (.classMem (.cv n) Y)))
              (synWral n (synCnnc) (.imp (.classMem (.cv n) Y)
                  (.classMem (synCplc (.cv n) (synC1c)) X))))))
        (synWbr (.cv m) (synCkqrel (synClefin)) (.cv k)))
      (synW3a (synWa (.classMem (.cv m) (synCnnc)) (.classMem (.cv k) (synCnnc)))
        (synWa (.classMem (.cv m) X) (.classMem (.cv k) Y)) (synWa (synWa
            (synWral n (synCnnc) (.imp (.classMem (.cv n) X)
                (synWbr (.cv m) (synCkqrel (synClefin)) (.cv n)))) (synWral n (synCnnc)
              (.imp (.classMem (.cv n) Y) (synWbr (.cv k) (synCkqrel (synClefin)) (.cv n)))))
          (synWa (synWral n (synCnnc) (.imp (.classMem (.cv n) X) (.classMem (.cv n) Y)))
            (synWral n (synCnnc)
              (.imp (.classMem (.cv n) Y) (.classMem (synCplc (.cv n) (synC1c)) X))))))
      (.imp (synWa (synWbr (.cv m) (synCkqrel (synClefin)) (.cv k))
          (synWbr (.cv k) (synCkqrel (synClefin)) (.cv m))) (.classEq (.cv m) (.cv k)))
      p0048 p0087
  have p0089 :=
    @gMpd
      (synWa (synW3a (synWa (.classMem (.cv m) (synCnnc)) (.classMem (.cv k) (synCnnc)))
          (synWa (.classMem (.cv m) X) (.classMem (.cv k) Y)) (synWa (synWa
              (synWral n (synCnnc) (.imp (.classMem (.cv n) X)
                  (synWbr (.cv m) (synCkqrel (synClefin)) (.cv n)))) (synWral n (synCnnc)
                (.imp (.classMem (.cv n) Y)
                  (synWbr (.cv k) (synCkqrel (synClefin)) (.cv n))))) (synWa
              (synWral n (synCnnc) (.imp (.classMem (.cv n) X) (.classMem (.cv n) Y)))
              (synWral n (synCnnc) (.imp (.classMem (.cv n) Y)
                  (.classMem (synCplc (.cv n) (synC1c)) X))))))
        (synWbr (.cv m) (synCkqrel (synClefin)) (.cv k)))
      (synWa (synWbr (.cv m) (synCkqrel (synClefin)) (.cv k))
        (synWbr (.cv k) (synCkqrel (synClefin)) (.cv m)))
      (.classEq (.cv m) (.cv k)) p0083 p0088
  have p0090 :=
    @gOrc (.classEq (.cv m) (.cv k)) (.classEq (.cv m) (synCplc (.cv k) (synC1c)))
  have p0091 :=
    @gSyl
      (synWa (synW3a (synWa (.classMem (.cv m) (synCnnc)) (.classMem (.cv k) (synCnnc)))
          (synWa (.classMem (.cv m) X) (.classMem (.cv k) Y)) (synWa (synWa
              (synWral n (synCnnc) (.imp (.classMem (.cv n) X)
                  (synWbr (.cv m) (synCkqrel (synClefin)) (.cv n)))) (synWral n (synCnnc)
                (.imp (.classMem (.cv n) Y)
                  (synWbr (.cv k) (synCkqrel (synClefin)) (.cv n))))) (synWa
              (synWral n (synCnnc) (.imp (.classMem (.cv n) X) (.classMem (.cv n) Y)))
              (synWral n (synCnnc) (.imp (.classMem (.cv n) Y)
                  (.classMem (synCplc (.cv n) (synC1c)) X))))))
        (synWbr (.cv m) (synCkqrel (synClefin)) (.cv k)))
      (.classEq (.cv m) (.cv k))
      (synWo (.classEq (.cv m) (.cv k)) (.classEq (.cv m) (synCplc (.cv k) (synC1c))))
      p0089 p0090
  have p0092 :=
    @gEx
      (synW3a (synWa (.classMem (.cv m) (synCnnc)) (.classMem (.cv k) (synCnnc)))
        (synWa (.classMem (.cv m) X) (.classMem (.cv k) Y)) (synWa (synWa
            (synWral n (synCnnc) (.imp (.classMem (.cv n) X)
                (synWbr (.cv m) (synCkqrel (synClefin)) (.cv n)))) (synWral n (synCnnc)
              (.imp (.classMem (.cv n) Y) (synWbr (.cv k) (synCkqrel (synClefin)) (.cv n)))))
          (synWa (synWral n (synCnnc) (.imp (.classMem (.cv n) X) (.classMem (.cv n) Y)))
            (synWral n (synCnnc)
              (.imp (.classMem (.cv n) Y) (.classMem (synCplc (.cv n) (synC1c)) X))))))
      (synWbr (.cv m) (synCkqrel (synClefin)) (.cv k))
      (synWo (.classEq (.cv m) (.cv k)) (.classEq (.cv m) (synCplc (.cv k) (synC1c))))
      p0091
  have p0093 := @gId (.classEq (.cv m) (synCplc (.cv k) (synC1c)))
  have p0094 :=
    @gOlc (.classEq (.cv m) (synCplc (.cv k) (synC1c))) (.classEq (.cv m) (.cv k))
  have p0095 :=
    @gSyl (.classEq (.cv m) (synCplc (.cv k) (synC1c)))
      (.classEq (.cv m) (synCplc (.cv k) (synC1c)))
      (synWo (.classEq (.cv m) (.cv k)) (.classEq (.cv m) (synCplc (.cv k) (synC1c))))
      p0093 p0094
  have p0096 :=
    @gA1i
      (.imp (.classEq (.cv m) (synCplc (.cv k) (synC1c))) (synWo (.classEq (.cv m) (.cv k))
          (.classEq (.cv m) (synCplc (.cv k) (synC1c)))))
      (synW3a (synWa (.classMem (.cv m) (synCnnc)) (.classMem (.cv k) (synCnnc)))
        (synWa (.classMem (.cv m) X) (.classMem (.cv k) Y)) (synWa (synWa
            (synWral n (synCnnc) (.imp (.classMem (.cv n) X)
                (synWbr (.cv m) (synCkqrel (synClefin)) (.cv n)))) (synWral n (synCnnc)
              (.imp (.classMem (.cv n) Y) (synWbr (.cv k) (synCkqrel (synClefin)) (.cv n)))))
          (synWa (synWral n (synCnnc) (.imp (.classMem (.cv n) X) (.classMem (.cv n) Y)))
            (synWral n (synCnnc)
              (.imp (.classMem (.cv n) Y) (.classMem (synCplc (.cv n) (synC1c)) X))))))
      p0095
  have p0097 :=
    @gJaod
      (synW3a (synWa (.classMem (.cv m) (synCnnc)) (.classMem (.cv k) (synCnnc)))
        (synWa (.classMem (.cv m) X) (.classMem (.cv k) Y)) (synWa (synWa
            (synWral n (synCnnc) (.imp (.classMem (.cv n) X)
                (synWbr (.cv m) (synCkqrel (synClefin)) (.cv n)))) (synWral n (synCnnc)
              (.imp (.classMem (.cv n) Y) (synWbr (.cv k) (synCkqrel (synClefin)) (.cv n)))))
          (synWa (synWral n (synCnnc) (.imp (.classMem (.cv n) X) (.classMem (.cv n) Y)))
            (synWral n (synCnnc)
              (.imp (.classMem (.cv n) Y) (.classMem (synCplc (.cv n) (synC1c)) X))))))
      (synWbr (.cv m) (synCkqrel (synClefin)) (.cv k))
      (synWo (.classEq (.cv m) (.cv k)) (.classEq (.cv m) (synCplc (.cv k) (synC1c))))
      (.classEq (.cv m) (synCplc (.cv k) (synC1c))) p0092 p0096
  have p0098 :=
    @gMpd
      (synW3a (synWa (.classMem (.cv m) (synCnnc)) (.classMem (.cv k) (synCnnc)))
        (synWa (.classMem (.cv m) X) (.classMem (.cv k) Y)) (synWa (synWa
            (synWral n (synCnnc) (.imp (.classMem (.cv n) X)
                (synWbr (.cv m) (synCkqrel (synClefin)) (.cv n)))) (synWral n (synCnnc)
              (.imp (.classMem (.cv n) Y) (synWbr (.cv k) (synCkqrel (synClefin)) (.cv n)))))
          (synWa (synWral n (synCnnc) (.imp (.classMem (.cv n) X) (.classMem (.cv n) Y)))
            (synWral n (synCnnc)
              (.imp (.classMem (.cv n) Y) (.classMem (synCplc (.cv n) (synC1c)) X))))))
      (synWo (synWbr (.cv m) (synCkqrel (synClefin)) (.cv k))
        (.classEq (.cv m) (synCplc (.cv k) (synC1c))))
      (synWo (.classEq (.cv m) (.cv k)) (.classEq (.cv m) (synCplc (.cv k) (synC1c))))
      p0046 p0097
  exact p0098


end NFChoice.DirectNominalPrf.WPPReplay

end
