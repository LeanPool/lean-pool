/-
Copyright (c) 2026 Elliot Glazer and NFNotWPP contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elliot Glazer and NFNotWPP contributors
-/

module

public import LeanPool.NFWeakPartition.NominalAlphaRepairedBase001049OprabReflected001
public import LeanPool.NFWeakPartition.Certificates.NominalWPPReplayChunk011Compact001Block004

/-! Nominal proof certificates grouped in dependency order. -/


public section

/-! Certificates from `NominalWPPReplayChunk012ACompact002Part001`. -/


section

namespace NFChoice.DirectNominalPrf.WPPReplay

open scoped Fol
open NFChoice.Foundation
open NFChoice.SemanticCore
open NFChoice.ReplaySupport
open NFChoice.Compiler.CompactSourceSyntax

/-- Checked nominal proof certificate identified upstream as `g_f1oeq3`. -/
@[expose]
noncomputable def gF1oeq3 (A : Class) (B : Class) (C : Class) (F : Class) :
    Nominal.NPrf (.imp (.classEq A B) (synWb (synWf1o F C A) (synWf1o F C B))) :=
  by
  have p0000 := @gF1eq3 A B C F
  have p0001 := @gFoeq3 A B C F
  have p0002 :=
    @gAnbi12d (.classEq A B) (synWf1 F C A) (synWf1 F C B) (synWfo F C A)
      (synWfo F C B) p0000 p0001
  have p0003 := (Nominal.biimpRefl (synWf1o F C A))
  have p0004 := (Nominal.biimpRefl (synWf1o F C B))
  have p0005 :=
    @gN3bitr4g (.classEq A B) (synWa (synWf1 F C A) (synWfo F C A))
      (synWa (synWf1 F C B) (synWfo F C B)) (synWf1o F C A) (synWf1o F C B) p0002
      p0003 p0004
  exact p0005

/-- Checked nominal proof certificate identified upstream as `g_f1oeq23`. -/
@[expose]
noncomputable def gF1oeq23 (A : Class) (B : Class) (C : Class) (D : Class) (F : Class) :
    Nominal.NPrf
      (.imp (synWa (.classEq A B) (.classEq C D))
        (synWb (synWf1o F A C) (synWf1o F B D))) :=
  by
  have p0000 := @gF1oeq2 A B C F
  have p0001 := @gF1oeq3 C D B F
  have p0002 :=
    @gSylan9bb (.classEq A B) (synWf1o F A C) (synWf1o F B C) (.classEq C D)
      (synWf1o F B D) p0000 p0001
  exact p0002

/-- Checked nominal proof certificate identified upstream as `g_f1of1`. -/
@[expose]
noncomputable def gF1of1 (A : Class) (B : Class) (F : Class) :
    Nominal.NPrf (.imp (synWf1o F A B) (synWf1 F A B)) :=
  by
  have p0000 := (Nominal.biimpRefl (synWf1o F A B))
  have p0001 := @gSimplbi (synWf1o F A B) (synWf1 F A B) (synWfo F A B) p0000
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_f1of`. -/
@[expose]
noncomputable def gF1of (A : Class) (B : Class) (F : Class) :
    Nominal.NPrf (.imp (synWf1o F A B) (synWf F A B)) :=
  by
  have p0000 := @gF1of1 A B F
  have p0001 := @gF1f A B F
  have p0002 := @gSyl (synWf1o F A B) (synWf1 F A B) (synWf F A B) p0000 p0001
  exact p0002

/-- Checked nominal proof certificate identified upstream as `g_f1ofn`. -/
@[expose]
noncomputable def gF1ofn (A : Class) (B : Class) (F : Class) :
    Nominal.NPrf (.imp (synWf1o F A B) (synWfn F A)) :=
  by
  have p0000 := @gF1of A B F
  have p0001 := @gFfn A B F
  have p0002 := @gSyl (synWf1o F A B) (synWf F A B) (synWfn F A) p0000 p0001
  exact p0002

/-- Checked nominal proof certificate identified upstream as `g_f1ofun`. -/
@[expose]
noncomputable def gF1ofun (A : Class) (B : Class) (F : Class) :
    Nominal.NPrf (.imp (synWf1o F A B) (synWfun F)) :=
  by
  have p0000 := @gF1ofn A B F
  have p0001 := @gFnfun A F
  have p0002 := @gSyl (synWf1o F A B) (synWfn F A) (synWfun F) p0000 p0001
  exact p0002

/-- Checked nominal proof certificate identified upstream as `g_f1odm`. -/
@[expose]
noncomputable def gF1odm (A : Class) (B : Class) (F : Class) :
    Nominal.NPrf (.imp (synWf1o F A B) (.classEq (synCdm F) A)) :=
  by
  have p0000 := @gF1ofn A B F
  have p0001 := @gFndm A F
  have p0002 := @gSyl (synWf1o F A B) (synWfn F A) (.classEq (synCdm F) A) p0000 p0001
  exact p0002

/-- Checked nominal proof certificate identified upstream as `g_dff1o2`. -/
@[expose]
noncomputable def gDff1o2 (A : Class) (B : Class) (F : Class) :
    Nominal.NPrf
      (synWb (synWf1o F A B)
        (synW3a (synWfn F A) (synWfun (synCcnv F)) (.classEq (synCrn F) B))) :=
  by
  have p0000 := (Nominal.biimpRefl (synWf1o F A B))
  have p0001 := (Nominal.biimpRefl (synWf1 F A B))
  have p0002 := (Nominal.biimpRefl (synWfo F A B))
  have p0003 :=
    @gAnbi12i (synWf1 F A B) (synWa (synWf F A B) (synWfun (synCcnv F)))
      (synWfo F A B) (synWa (synWfn F A) (.classEq (synCrn F) B)) p0001 p0002
  have p0004 :=
    @gAncom (synWf F A B)
      (synWa (synWfun (synCcnv F)) (synWa (synWfn F A) (.classEq (synCrn F) B)))
  have p0005 := @gN3anass (synWfn F A) (synWfun (synCcnv F)) (.classEq (synCrn F) B)
  have p0006 := @gAn12 (synWfn F A) (synWfun (synCcnv F)) (.classEq (synCrn F) B)
  have p0007 :=
    @gBitri (synW3a (synWfn F A) (synWfun (synCcnv F)) (.classEq (synCrn F) B))
      (synWa (synWfn F A) (synWa (synWfun (synCcnv F)) (.classEq (synCrn F) B)))
      (synWa (synWfun (synCcnv F)) (synWa (synWfn F A) (.classEq (synCrn F) B)))
      p0005 p0006
  have p0008 :=
    @gAnbi1i (synW3a (synWfn F A) (synWfun (synCcnv F)) (.classEq (synCrn F) B))
      (synWa (synWfun (synCcnv F)) (synWa (synWfn F A) (.classEq (synCrn F) B)))
      (synWf F A B) p0007
  have p0009 :=
    @gBitr4i
      (synWa (synWf F A B)
        (synWa (synWfun (synCcnv F)) (synWa (synWfn F A) (.classEq (synCrn F) B))))
      (synWa (synWa (synWfun (synCcnv F)) (synWa (synWfn F A) (.classEq (synCrn F) B)))
        (synWf F A B))
      (synWa (synW3a (synWfn F A) (synWfun (synCcnv F)) (.classEq (synCrn F) B))
        (synWf F A B))
      p0004 p0008
  have p0010 :=
    @gAnass (synWf F A B) (synWfun (synCcnv F))
      (synWa (synWfn F A) (.classEq (synCrn F) B))
  have p0011 := @gEqimss (synCrn F) B
  have p0012 := (Nominal.biimpRefl (synWf F A B))
  have p0013 :=
    @gBiimpri (synWf F A B) (synWa (synWfn F A) (synWss (synCrn F) B)) p0012
  have p0014 :=
    @gSylan2 (.classEq (synCrn F) B) (synWfn F A) (synWss (synCrn F) B)
      (synWf F A B) p0011 p0013
  have p0015 :=
    @gN3adant2 (synWfn F A) (.classEq (synCrn F) B) (synWf F A B)
      (synWfun (synCcnv F)) p0014
  have p0016 :=
    @gPm471i (synW3a (synWfn F A) (synWfun (synCcnv F)) (.classEq (synCrn F) B))
      (synWf F A B) p0015
  have p0017 :=
    @gN3bitr4i
      (synWa (synWf F A B)
        (synWa (synWfun (synCcnv F)) (synWa (synWfn F A) (.classEq (synCrn F) B))))
      (synWa (synW3a (synWfn F A) (synWfun (synCcnv F)) (.classEq (synCrn F) B))
        (synWf F A B))
      (synWa (synWa (synWf F A B) (synWfun (synCcnv F)))
        (synWa (synWfn F A) (.classEq (synCrn F) B)))
      (synW3a (synWfn F A) (synWfun (synCcnv F)) (.classEq (synCrn F) B)) p0009 p0010
      p0016
  have p0018 :=
    @gN3bitri (synWf1o F A B) (synWa (synWf1 F A B) (synWfo F A B))
      (synWa (synWa (synWf F A B) (synWfun (synCcnv F)))
        (synWa (synWfn F A) (.classEq (synCrn F) B)))
      (synW3a (synWfn F A) (synWfun (synCcnv F)) (.classEq (synCrn F) B)) p0000 p0003
      p0017
  exact p0018

/-- Checked nominal proof certificate identified upstream as `g_dff1o3`. -/
@[expose]
noncomputable def gDff1o3 (A : Class) (B : Class) (F : Class) :
    Nominal.NPrf
      (synWb (synWf1o F A B) (synWa (synWfo F A B) (synWfun (synCcnv F)))) :=
  by
  have p0000 :=
    (Nominal.biimpRefl (synW3a (synWfn F A) (synWfun (synCcnv F)) (.classEq (synCrn F) B)))
  have p0001 := @gAn32 (synWfn F A) (synWfun (synCcnv F)) (.classEq (synCrn F) B)
  have p0002 :=
    @gBitri (synW3a (synWfn F A) (synWfun (synCcnv F)) (.classEq (synCrn F) B))
      (synWa (synWa (synWfn F A) (synWfun (synCcnv F))) (.classEq (synCrn F) B))
      (synWa (synWa (synWfn F A) (.classEq (synCrn F) B)) (synWfun (synCcnv F)))
      p0000 p0001
  have p0003 := @gDff1o2 A B F
  have p0004 := (Nominal.biimpRefl (synWfo F A B))
  have p0005 :=
    @gAnbi1i (synWfo F A B) (synWa (synWfn F A) (.classEq (synCrn F) B))
      (synWfun (synCcnv F)) p0004
  have p0006 :=
    @gN3bitr4i (synW3a (synWfn F A) (synWfun (synCcnv F)) (.classEq (synCrn F) B))
      (synWa (synWa (synWfn F A) (.classEq (synCrn F) B)) (synWfun (synCcnv F)))
      (synWf1o F A B) (synWa (synWfo F A B) (synWfun (synCcnv F))) p0002 p0003 p0005
  exact p0006

/-- Checked nominal proof certificate identified upstream as `g_f1ofo`. -/
@[expose]
noncomputable def gF1ofo (A : Class) (B : Class) (F : Class) :
    Nominal.NPrf (.imp (synWf1o F A B) (synWfo F A B)) :=
  by
  have p0000 := @gDff1o3 A B F
  have p0001 := @gSimplbi (synWf1o F A B) (synWfo F A B) (synWfun (synCcnv F)) p0000
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_dff1o4`. -/
@[expose]
noncomputable def gDff1o4 (A : Class) (B : Class) (F : Class) :
    Nominal.NPrf
      (synWb (synWf1o F A B) (synWa (synWfn F A) (synWfn (synCcnv F) B))) :=
  by
  have p0000 := @gDff1o2 A B F
  have p0001 := @gN3anass (synWfn F A) (synWfun (synCcnv F)) (.classEq (synCrn F) B)
  have p0002 := @gDfrn4 F
  have p0003 := @gEqeq1i (synCrn F) (synCdm (synCcnv F)) B p0002
  have p0004 :=
    @gAnbi2i (.classEq (synCrn F) B) (.classEq (synCdm (synCcnv F)) B)
      (synWfun (synCcnv F)) p0003
  have p0005 := (Nominal.biimpRefl (synWfn (synCcnv F) B))
  have p0006 :=
    @gBitr4i (synWa (synWfun (synCcnv F)) (.classEq (synCrn F) B))
      (synWa (synWfun (synCcnv F)) (.classEq (synCdm (synCcnv F)) B))
      (synWfn (synCcnv F) B) p0004 p0005
  have p0007 :=
    @gAnbi2i (synWa (synWfun (synCcnv F)) (.classEq (synCrn F) B))
      (synWfn (synCcnv F) B) (synWfn F A) p0006
  have p0008 :=
    @gN3bitri (synWf1o F A B)
      (synW3a (synWfn F A) (synWfun (synCcnv F)) (.classEq (synCrn F) B))
      (synWa (synWfn F A) (synWa (synWfun (synCcnv F)) (.classEq (synCrn F) B)))
      (synWa (synWfn F A) (synWfn (synCcnv F) B)) p0000 p0001 p0007
  exact p0008

/-- Checked nominal proof certificate identified upstream as `g_dff1o5`. -/
@[expose]
noncomputable def gDff1o5 (A : Class) (B : Class) (F : Class) :
    Nominal.NPrf
      (synWb (synWf1o F A B) (synWa (synWf1 F A B) (.classEq (synCrn F) B))) :=
  by
  have p0000 := (Nominal.biimpRefl (synWf1o F A B))
  have p0001 := @gF1f A B F
  have p0002 := @gBiantrurd (synWf1 F A B) (synWf F A B) (.classEq (synCrn F) B) p0001
  have p0003 := @gDffo2 A B F
  have p0004 :=
    @gSyl6rbbr (synWf1 F A B) (.classEq (synCrn F) B)
      (synWa (synWf F A B) (.classEq (synCrn F) B)) (synWfo F A B) p0002 p0003
  have p0005 := @gPm532i (synWf1 F A B) (synWfo F A B) (.classEq (synCrn F) B) p0004
  have p0006 :=
    @gBitri (synWf1o F A B) (synWa (synWf1 F A B) (synWfo F A B))
      (synWa (synWf1 F A B) (.classEq (synCrn F) B)) p0000 p0005
  exact p0006

/-- Checked nominal proof certificate identified upstream as `g_f1orn`. -/
@[expose]
noncomputable def gF1orn (A : Class) (F : Class) :
    Nominal.NPrf
      (synWb (synWf1o F A (synCrn F)) (synWa (synWfn F A) (synWfun (synCcnv F)))) :=
  by
  have p0000 :=
    (Nominal.biimpRefl
      (synW3a (synWfn F A) (synWfun (synCcnv F)) (.classEq (synCrn F) (synCrn F))))
  have p0001 := @gDff1o2 A (synCrn F) F
  have p0002 := @gEqid (synCrn F)
  have p0003 :=
    @gBiantru (.classEq (synCrn F) (synCrn F))
      (synWa (synWfn F A) (synWfun (synCcnv F))) p0002
  have p0004 :=
    @gN3bitr4i
      (synW3a (synWfn F A) (synWfun (synCcnv F)) (.classEq (synCrn F) (synCrn F)))
      (synWa (synWa (synWfn F A) (synWfun (synCcnv F))) (.classEq (synCrn F) (synCrn F)))
      (synWf1o F A (synCrn F)) (synWa (synWfn F A) (synWfun (synCcnv F))) p0000
      p0001 p0003
  exact p0004

/-- Checked nominal proof certificate identified upstream as `g_f1f1orn`. -/
@[expose]
noncomputable def gF1f1orn (A : Class) (B : Class) (F : Class) :
    Nominal.NPrf (.imp (synWf1 F A B) (synWf1o F A (synCrn F))) :=
  by
  have p0000 := @gF1fn A B F
  have p0001 := (Nominal.biimpRefl (synWf1 F A B))
  have p0002 := @gSimprbi (synWf1 F A B) (synWf F A B) (synWfun (synCcnv F)) p0001
  have p0003 := @gF1orn A F
  have p0004 :=
    @gSylanbrc (synWf1 F A B) (synWfn F A) (synWfun (synCcnv F))
      (synWf1o F A (synCrn F)) p0000 p0002 p0003
  exact p0004

/-- Checked nominal proof certificate identified upstream as `g_f1ocnvb`. -/
@[expose]
noncomputable def gF1ocnvb (A : Class) (B : Class) (F : Class) :
    Nominal.NPrf (synWb (synWf1o F A B) (synWf1o (synCcnv F) B A)) :=
  by
  have p0000 := @gCnvcnv F
  have p0001 := @gFneq1i A (synCcnv (synCcnv F)) F p0000
  have p0002 :=
    @gAnbi2i (synWfn (synCcnv (synCcnv F)) A) (synWfn F A) (synWfn (synCcnv F) B)
      p0001
  have p0003 := @gAncom (synWfn (synCcnv F) B) (synWfn F A)
  have p0004 :=
    @gBitri (synWa (synWfn (synCcnv F) B) (synWfn (synCcnv (synCcnv F)) A))
      (synWa (synWfn (synCcnv F) B) (synWfn F A))
      (synWa (synWfn F A) (synWfn (synCcnv F) B)) p0002 p0003
  have p0005 := @gDff1o4 B A (synCcnv F)
  have p0006 := @gDff1o4 A B F
  have p0007 :=
    @gN3bitr4ri (synWa (synWfn (synCcnv F) B) (synWfn (synCcnv (synCcnv F)) A))
      (synWa (synWfn F A) (synWfn (synCcnv F) B)) (synWf1o (synCcnv F) B A)
      (synWf1o F A B) p0004 p0005 p0006
  exact p0007

/-- Checked nominal proof certificate identified upstream as `g_f1ocnv`. -/
@[expose]
noncomputable def gF1ocnv (A : Class) (B : Class) (F : Class) :
    Nominal.NPrf (.imp (synWf1o F A B) (synWf1o (synCcnv F) B A)) :=
  by
  have p0000 := @gF1ocnvb A B F
  have p0001 := @gBiimpi (synWf1o F A B) (synWf1o (synCcnv F) B A) p0000
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_f1ores`. -/
@[expose]
noncomputable def gF1ores (A : Class) (B : Class) (C : Class) (F : Class) :
    Nominal.NPrf
      (.imp (synWa (synWf1 F A B) (synWss C A))
        (synWf1o (synCres F C) C (synCima F C))) :=
  by
  have p0000 := @gFfun A B F
  have p0001 := @gAdantr (synWf F A B) (synWfun F) (synWss C A) p0000
  have p0002 := @gFdm A B F
  have p0003 := @gSseq2d (synWf F A B) (synCdm F) A C p0002
  have p0004 := @gBiimpar (synWf F A B) (synWss C (synCdm F)) (synWss C A) p0003
  have p0005 := @gFores C F
  have p0006 :=
    @gSyl2anc (synWa (synWf F A B) (synWss C A)) (synWfun F) (synWss C (synCdm F))
      (synWfo (synCres F C) C (synCima F C)) p0001 p0004 p0005
  have p0007 := @gFunres11 C F
  have p0008 :=
    @gAnim12i (synWa (synWf F A B) (synWss C A))
      (synWfo (synCres F C) C (synCima F C)) (synWfun (synCcnv F))
      (synWfun (synCcnv (synCres F C))) p0006 p0007
  have p0009 :=
    @gAn32s (synWf F A B) (synWss C A) (synWfun (synCcnv F))
      (synWa (synWfo (synCres F C) C (synCima F C)) (synWfun (synCcnv (synCres F C))))
      p0008
  have p0010 := (Nominal.biimpRefl (synWf1 F A B))
  have p0011 :=
    @gAnbi1i (synWf1 F A B) (synWa (synWf F A B) (synWfun (synCcnv F)))
      (synWss C A) p0010
  have p0012 := @gDff1o3 C (synCima F C) (synCres F C)
  have p0013 :=
    @gN3imtr4i (synWa (synWa (synWf F A B) (synWfun (synCcnv F))) (synWss C A))
      (synWa (synWfo (synCres F C) C (synCima F C)) (synWfun (synCcnv (synCres F C))))
      (synWa (synWf1 F A B) (synWss C A)) (synWf1o (synCres F C) C (synCima F C))
      p0009 p0011 p0012
  exact p0013

/-- Checked nominal proof certificate identified upstream as `g_f1oun`. -/
@[expose]
noncomputable def gF1oun (A : Class) (B : Class) (C : Class) (D : Class) (F : Class)
    (G : Class) :
    Nominal.NPrf
      (.imp (synWa (synWa (synWf1o F A B) (synWf1o G C D))
          (synWa (.classEq (synCin A C) (synC0)) (.classEq (synCin B D) (synC0))))
        (synWf1o (synCun F G) (synCun A C) (synCun B D))) :=
  by
  have p0000 := @gDff1o4 A B F
  have p0001 := @gDff1o4 C D G
  have p0002 := @gFnun A C F G
  have p0003 :=
    @gEx (synWa (synWfn F A) (synWfn G C)) (.classEq (synCin A C) (synC0))
      (synWfn (synCun F G) (synCun A C)) p0002
  have p0004 := @gFnun B D (synCcnv F) (synCcnv G)
  have p0005 := @gCnvun F G
  have p0006 :=
    @gFneq1i (synCun B D) (synCcnv (synCun F G)) (synCun (synCcnv F) (synCcnv G))
      p0005
  have p0007 :=
    @gSylibr
      (synWa (synWa (synWfn (synCcnv F) B) (synWfn (synCcnv G) D))
        (.classEq (synCin B D) (synC0)))
      (synWfn (synCun (synCcnv F) (synCcnv G)) (synCun B D))
      (synWfn (synCcnv (synCun F G)) (synCun B D)) p0004 p0006
  have p0008 :=
    @gEx (synWa (synWfn (synCcnv F) B) (synWfn (synCcnv G) D))
      (.classEq (synCin B D) (synC0)) (synWfn (synCcnv (synCun F G)) (synCun B D))
      p0007
  have p0009 :=
    @gIm2anan9 (synWa (synWfn F A) (synWfn G C)) (.classEq (synCin A C) (synC0))
      (synWfn (synCun F G) (synCun A C))
      (synWa (synWfn (synCcnv F) B) (synWfn (synCcnv G) D))
      (.classEq (synCin B D) (synC0)) (synWfn (synCcnv (synCun F G)) (synCun B D))
      p0003 p0008
  have p0010 :=
    @gAn4s (synWfn F A) (synWfn G C) (synWfn (synCcnv F) B) (synWfn (synCcnv G) D)
      (.imp (synWa (.classEq (synCin A C) (synC0)) (.classEq (synCin B D) (synC0)))
        (synWa (synWfn (synCun F G) (synCun A C))
          (synWfn (synCcnv (synCun F G)) (synCun B D))))
      p0009
  have p0011 :=
    @gSyl2anb (synWf1o F A B) (synWa (synWfn F A) (synWfn (synCcnv F) B))
      (synWa (synWfn G C) (synWfn (synCcnv G) D))
      (.imp (synWa (.classEq (synCin A C) (synC0)) (.classEq (synCin B D) (synC0)))
        (synWa (synWfn (synCun F G) (synCun A C))
          (synWfn (synCcnv (synCun F G)) (synCun B D))))
      (synWf1o G C D) p0000 p0001 p0010
  have p0012 := @gDff1o4 (synCun A C) (synCun B D) (synCun F G)
  have p0013 :=
    @gSyl6ibr (synWa (synWf1o F A B) (synWf1o G C D))
      (synWa (.classEq (synCin A C) (synC0)) (.classEq (synCin B D) (synC0)))
      (synWa (synWfn (synCun F G) (synCun A C))
        (synWfn (synCcnv (synCun F G)) (synCun B D)))
      (synWf1o (synCun F G) (synCun A C) (synCun B D)) p0011 p0012
  have p0014 :=
    @gImp (synWa (synWf1o F A B) (synWf1o G C D))
      (synWa (.classEq (synCin A C) (synC0)) (.classEq (synCin B D) (synC0)))
      (synWf1o (synCun F G) (synCun A C) (synCun B D)) p0013
  exact p0014

/-- Checked nominal proof certificate identified upstream as `g_f1oco`. -/
@[expose]
noncomputable def gF1oco (A : Class) (B : Class) (C : Class) (F : Class) (G : Class) :
    Nominal.NPrf
      (.imp (synWa (synWf1o F B C) (synWf1o G A B)) (synWf1o (synCcom F G) A C)) :=
  by
  have p0000 := @gF1co A B C F G
  have p0001 := @gFoco A B C F G
  have p0002 :=
    @gAnim12i (synWa (synWf1 F B C) (synWf1 G A B)) (synWf1 (synCcom F G) A C)
      (synWa (synWfo F B C) (synWfo G A B)) (synWfo (synCcom F G) A C) p0000 p0001
  have p0003 :=
    @gAn4s (synWf1 F B C) (synWf1 G A B) (synWfo F B C) (synWfo G A B)
      (synWa (synWf1 (synCcom F G) A C) (synWfo (synCcom F G) A C)) p0002
  have p0004 := (Nominal.biimpRefl (synWf1o F B C))
  have p0005 := (Nominal.biimpRefl (synWf1o G A B))
  have p0006 :=
    @gAnbi12i (synWf1o F B C) (synWa (synWf1 F B C) (synWfo F B C)) (synWf1o G A B)
      (synWa (synWf1 G A B) (synWfo G A B)) p0004 p0005
  have p0007 := (Nominal.biimpRefl (synWf1o (synCcom F G) A C))
  have p0008 :=
    @gN3imtr4i
      (synWa (synWa (synWf1 F B C) (synWfo F B C)) (synWa (synWf1 G A B) (synWfo G A B)))
      (synWa (synWf1 (synCcom F G) A C) (synWfo (synCcom F G) A C))
      (synWa (synWf1o F B C) (synWf1o G A B)) (synWf1o (synCcom F G) A C) p0003 p0006
      p0007
  exact p0008

/-- Checked nominal proof certificate identified upstream as `g_f1ococnv2`. -/
@[expose]
noncomputable def gF1ococnv2 (A : Class) (B : Class) (F : Class) :
    Nominal.NPrf
      (.imp (synWf1o F A B) (.classEq (synCcom F (synCcnv F)) (synCres (synCid) B))) :=
  by
  have p0000 := @gF1ofun A B F
  have p0001 := (Nominal.biimpRefl (synWfun F))
  have p0002 := @gIss (synCcom F (synCcnv F))
  have p0003 :=
    @gBitri (synWfun F) (synWss (synCcom F (synCcnv F)) (synCid))
      (.classEq (synCcom F (synCcnv F))
        (synCres (synCid) (synCdm (synCcom F (synCcnv F)))))
      p0001 p0002
  have p0004 :=
    @gSylib (synWf1o F A B) (synWfun F)
      (.classEq (synCcom F (synCcnv F))
        (synCres (synCid) (synCdm (synCcom F (synCcnv F)))))
      p0000 p0003
  have p0005 := (Nominal.classEqRefl (synCdm F))
  have p0006 := @gDmcoeq F (synCcnv F)
  have p0007 := Nominal.mp p0005 p0006
  have p0008 := @gDfrn4 F
  have p0009 :=
    @gEqtr4i (synCdm (synCcom F (synCcnv F))) (synCdm (synCcnv F)) (synCrn F) p0007
      p0008
  have p0010 := @gF1ofo A B F
  have p0011 := @gForn A B F
  have p0012 :=
    @gSyl (synWf1o F A B) (synWfo F A B) (.classEq (synCrn F) B) p0010 p0011
  have p0013 :=
    @gSyl5eq (synWf1o F A B) (synCdm (synCcom F (synCcnv F))) (synCrn F) B p0009
      p0012
  have p0014 :=
    @gReseq2d (synWf1o F A B) (synCdm (synCcom F (synCcnv F))) B (synCid) p0013
  have p0015 :=
    @gEqtrd (synWf1o F A B) (synCcom F (synCcnv F))
      (synCres (synCid) (synCdm (synCcom F (synCcnv F)))) (synCres (synCid) B)
      p0004 p0014
  exact p0015

/-- Checked nominal proof certificate identified upstream as `g_f1ococnv1`. -/
@[expose]
noncomputable def gF1ococnv1 (A : Class) (B : Class) (F : Class) :
    Nominal.NPrf
      (.imp (synWf1o F A B) (.classEq (synCcom (synCcnv F) F) (synCres (synCid) A))) :=
  by
  have p0000 := @gCnvcnv F
  have p0001 := @gCoeq2i (synCcnv (synCcnv F)) F (synCcnv F) p0000
  have p0002 := @gF1ocnv A B F
  have p0003 := @gF1ococnv2 B A (synCcnv F)
  have p0004 :=
    @gSyl (synWf1o F A B) (synWf1o (synCcnv F) B A)
      (.classEq (synCcom (synCcnv F) (synCcnv (synCcnv F))) (synCres (synCid) A))
      p0002 p0003
  have p0005 :=
    @gSyl5eqr (synWf1o F A B) (synCcom (synCcnv F) F)
      (synCcom (synCcnv F) (synCcnv (synCcnv F))) (synCres (synCid) A) p0001 p0004
  exact p0005

/-- Checked nominal proof certificate identified upstream as `g_f1cnv`. -/
@[expose]
noncomputable def gF1cnv (A : Class) (B : Class) (F : Class) :
    Nominal.NPrf (.imp (synWf1 F A B) (synWf1o (synCcnv F) (synCrn F) A)) :=
  by
  have p0000 := @gF1f1orn A B F
  have p0001 := @gF1ocnv A (synCrn F) F
  have p0002 :=
    @gSyl (synWf1 F A B) (synWf1o F A (synCrn F))
      (synWf1o (synCcnv F) (synCrn F) A) p0000 p0001
  exact p0002

/-- Checked nominal proof certificate identified upstream as `g_f10`. -/
@[expose]
noncomputable def gF10 (A : Class) : Nominal.NPrf (synWf1 (synC0) (synC0) A) :=
  by
  have p0000 := @gF0 A
  have p0001 := @gFun0
  have p0002 := @gCnv0
  have p0003 := @gFuneqi (synCcnv (synC0)) (synC0) p0002
  have p0004 := @gMpbir (synWfun (synCcnv (synC0))) (synWfun (synC0)) p0001 p0003
  have p0005 := (Nominal.biimpRefl (synWf1 (synC0) (synC0) A))
  have p0006 :=
    @gMpbir2an (synWf1 (synC0) (synC0) A) (synWf (synC0) (synC0) A)
      (synWfun (synCcnv (synC0))) p0000 p0004 p0005
  exact p0006

/-- Checked nominal proof certificate identified upstream as `g_f1o00`. -/
@[expose]
noncomputable def gF1o00 (A : Class) (F : Class) :
    Nominal.NPrf
      (synWb (synWf1o F (synC0) A) (synWa (.classEq F (synC0)) (.classEq A (synC0)))) :=
  by
  have p0000 := @gDff1o4 (synC0) A F
  have p0001 := @gFn0 F
  have p0002 := @gBiimpi (synWfn F (synC0)) (.classEq F (synC0)) p0001
  have p0003 :=
    @gAdantr (synWfn F (synC0)) (.classEq F (synC0)) (synWfn (synCcnv F) A) p0002
  have p0004 := @gDm0
  have p0005 := @gCnveq F (synC0)
  have p0006 := @gCnv0
  have p0007 :=
    @gSyl6eq (.classEq F (synC0)) (synCcnv F) (synCcnv (synC0)) (synC0) p0005 p0006
  have p0008 :=
    @gSylbi (synWfn F (synC0)) (.classEq F (synC0)) (.classEq (synCcnv F) (synC0))
      p0001 p0007
  have p0009 := @gFneq1d (synWfn F (synC0)) A (synCcnv F) (synC0) p0008
  have p0010 :=
    @gBiimpa (synWfn F (synC0)) (synWfn (synCcnv F) A) (synWfn (synC0) A) p0009
  have p0011 := @gFndm A (synC0)
  have p0012 :=
    @gSyl (synWa (synWfn F (synC0)) (synWfn (synCcnv F) A)) (synWfn (synC0) A)
      (.classEq (synCdm (synC0)) A) p0010 p0011
  have p0013 :=
    @gSyl5reqr (synWa (synWfn F (synC0)) (synWfn (synCcnv F) A)) (synC0)
      (synCdm (synC0)) A p0004 p0012
  have p0014 :=
    @gJca (synWa (synWfn F (synC0)) (synWfn (synCcnv F) A)) (.classEq F (synC0))
      (.classEq A (synC0)) p0003 p0013
  have p0015 := @gBiimpri (synWfn F (synC0)) (.classEq F (synC0)) p0001
  have p0016 :=
    @gAdantr (.classEq F (synC0)) (synWfn F (synC0)) (.classEq A (synC0)) p0015
  have p0017 := @gEqid (synC0)
  have p0018 := @gFn0 (synC0)
  have p0019 :=
    @gMpbir (synWfn (synC0) (synC0)) (.classEq (synC0) (synC0)) p0017 p0018
  have p0020 := @gFneq1d (.classEq F (synC0)) A (synCcnv F) (synC0) p0007
  have p0021 := @gFneq2 A (synC0) (synC0)
  have p0022 :=
    @gSylan9bb (.classEq F (synC0)) (synWfn (synCcnv F) A) (synWfn (synC0) A)
      (.classEq A (synC0)) (synWfn (synC0) (synC0)) p0020 p0021
  have p0023 :=
    @gMpbiri (synWa (.classEq F (synC0)) (.classEq A (synC0)))
      (synWfn (synCcnv F) A) (synWfn (synC0) (synC0)) p0019 p0022
  have p0024 :=
    @gJca (synWa (.classEq F (synC0)) (.classEq A (synC0))) (synWfn F (synC0))
      (synWfn (synCcnv F) A) p0016 p0023
  have p0025 :=
    @gImpbii (synWa (synWfn F (synC0)) (synWfn (synCcnv F) A))
      (synWa (.classEq F (synC0)) (.classEq A (synC0))) p0014 p0024
  have p0026 :=
    @gBitri (synWf1o F (synC0) A)
      (synWa (synWfn F (synC0)) (synWfn (synCcnv F) A))
      (synWa (.classEq F (synC0)) (.classEq A (synC0))) p0000 p0025
  exact p0026

/-- Checked nominal proof certificate identified upstream as `g_f1o0`. -/
@[expose]
noncomputable def gF1o0 : Nominal.NPrf (synWf1o (synC0) (synC0) (synC0)) :=
  by
  have p0000 := @gF10 (synC0)
  have p0001 := @gFun0
  have p0002 := @gDm0
  have p0003 := (Nominal.biimpRefl (synWfn (synC0) (synC0)))
  have p0004 :=
    @gMpbir2an (synWfn (synC0) (synC0)) (synWfun (synC0))
      (.classEq (synCdm (synC0)) (synC0)) p0001 p0002 p0003
  have p0005 := @gRn0
  have p0006 := (Nominal.biimpRefl (synWfo (synC0) (synC0) (synC0)))
  have p0007 :=
    @gMpbir2an (synWfo (synC0) (synC0) (synC0)) (synWfn (synC0) (synC0))
      (.classEq (synCrn (synC0)) (synC0)) p0004 p0005 p0006
  have p0008 := (Nominal.biimpRefl (synWf1o (synC0) (synC0) (synC0)))
  have p0009 :=
    @gMpbir2an (synWf1o (synC0) (synC0) (synC0)) (synWf1 (synC0) (synC0) (synC0))
      (synWfo (synC0) (synC0) (synC0)) p0000 p0007 p0008
  exact p0009

/-- Checked nominal proof certificate identified upstream as `g_f1oi`. -/
@[expose]
noncomputable def gF1oi (A : Class) :
    Nominal.NPrf (synWf1o (synCres (synCid) A) A A) :=
  by
  have p0000 := @gFnresi A
  have p0001 := @gCnvresid A
  have p0002 := @gFneq1i A (synCcnv (synCres (synCid) A)) (synCres (synCid) A) p0001
  have p0003 :=
    @gMpbir (synWfn (synCcnv (synCres (synCid) A)) A)
      (synWfn (synCres (synCid) A) A) p0000 p0002
  have p0004 := @gDff1o4 A A (synCres (synCid) A)
  have p0005 :=
    @gMpbir2an (synWf1o (synCres (synCid) A) A A) (synWfn (synCres (synCid) A) A)
      (synWfn (synCcnv (synCres (synCid) A)) A) p0000 p0003 p0004
  exact p0005

/-- Checked nominal proof certificate identified upstream as `g_f1ovi`. -/
@[expose]
noncomputable def gF1ovi : Nominal.NPrf (synWf1o (synCid) (synCvv) (synCvv)) :=
  by
  have p0000 := @gFuni
  have p0001 := @gDmi
  have p0002 := (Nominal.biimpRefl (synWfn (synCid) (synCvv)))
  have p0003 :=
    @gMpbir2an (synWfn (synCid) (synCvv)) (synWfun (synCid))
      (.classEq (synCdm (synCid)) (synCvv)) p0000 p0001 p0002
  have p0004 := @gCnvi
  have p0005 := @gFneq1i (synCvv) (synCcnv (synCid)) (synCid) p0004
  have p0006 :=
    @gMpbir (synWfn (synCcnv (synCid)) (synCvv)) (synWfn (synCid) (synCvv)) p0003
      p0005
  have p0007 := @gDff1o4 (synCvv) (synCvv) (synCid)
  have p0008 :=
    @gMpbir2an (synWf1o (synCid) (synCvv) (synCvv)) (synWfn (synCid) (synCvv))
      (synWfn (synCcnv (synCid)) (synCvv)) p0003 p0006 p0007
  exact p0008

/-- Checked nominal proof certificate identified upstream as `g_f1osn`. -/
@[expose]
noncomputable def gF1osn (A : Class) (B : Class)
    (hyp_f1osn_1 : Nominal.NPrf (.classMem A (synCvv)))
    (hyp_f1osn_2 : Nominal.NPrf (.classMem B (synCvv))) :
    Nominal.NPrf (synWf1o (synCsn (synCop A B)) (synCsn A) (synCsn B)) :=
  by
  have p0000 := @gFnsn A B hyp_f1osn_1 hyp_f1osn_2
  have p0001 := @gFnsn B A hyp_f1osn_2 hyp_f1osn_1
  have p0002 := @gCnvsn A B hyp_f1osn_1 hyp_f1osn_2
  have p0003 :=
    @gFneq1i (synCsn B) (synCcnv (synCsn (synCop A B))) (synCsn (synCop B A)) p0002
  have p0004 :=
    @gMpbir (synWfn (synCcnv (synCsn (synCop A B))) (synCsn B))
      (synWfn (synCsn (synCop B A)) (synCsn B)) p0001 p0003
  have p0005 := @gDff1o4 (synCsn A) (synCsn B) (synCsn (synCop A B))
  have p0006 :=
    @gMpbir2an (synWf1o (synCsn (synCop A B)) (synCsn A) (synCsn B))
      (synWfn (synCsn (synCop A B)) (synCsn A))
      (synWfn (synCcnv (synCsn (synCop A B))) (synCsn B)) p0000 p0004 p0005
  exact p0006

/-- Checked nominal proof certificate identified upstream as `g_f1osng`. -/
@[expose]
noncomputable def gF1osng (A : Class) (B : Class) (V : Class) (W : Class) :
    Nominal.NPrf
      (.imp (synWa (.classMem A V) (.classMem B W))
        (synWf1o (synCsn (synCop A B)) (synCsn A) (synCsn B))) :=
  by
  let proofSupport : Finset Var := A.fv ∪ B.fv ∪ V.fv ∪ W.fv
  let a : Var := freshVar proofSupport 0
  let b : Var := freshVar proofSupport 1
  have fresh_a : a ∉ proofSupport :=
    by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_a_not_A : a ∉ A.fv := by
    intro h
    exact
      fresh_a
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (h))))
  have fresh_b : b ∉ proofSupport :=
    by
    change freshVar proofSupport 1 ∉ proofSupport
    exact freshVar_not_mem proofSupport 1
  have fresh_b_not_A : b ∉ A.fv := by
    intro h
    exact
      fresh_b
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (h))))
  have fresh_b_not_B : b ∉ B.fv := by
    intro h
    exact
      fresh_b
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))
  have fresh_a_ne_b : a ≠ b :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have dv_cache_0001 : a ∉ (A).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : a ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_a_not_A, not_false_eq_true])
  have dv_cache_0002 : b ∉ (A).fv :=
    by
    clear dv_cache_0001
    exact
      (by
        have compact_fv_not_mem_empty : b ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_b_not_A, not_false_eq_true])
  have dv_cache_0003 : b ∉ (B).fv :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact
      (by
        have compact_fv_not_mem_empty : b ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_b_not_B, not_false_eq_true])
  have dv_cache_0004 :
    b ∉ ((synWf1o (synCsn (synCop A B)) (synCsn A) (synCsn B))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact
      (by
        have compact_fv_not_mem_empty : b ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wf1o,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cop, Finset.mem_union,
          fresh_b_not_A, fresh_b_not_B, or_false, not_false_eq_true])
  have dv_cache_0005 :
    a ∉ ((synWf1o (synCsn (synCop A (.cv b))) (synCsn A) (synCsn (.cv b)))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact
      (by
        have compact_fv_not_mem_empty : a ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wf1o,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cop,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, fresh_a_not_A, fresh_a_ne_b, or_false, not_false_eq_true])
  have p0000 := @gSneq (.cv a) A
  have p0001 :=
    @gF1oeq2 (synCsn (.cv a)) (synCsn A) (synCsn (.cv b))
      (synCsn (synCop (.cv a) (.cv b)))
  have p0002 :=
    @gSyl (.classEq (.cv a) A) (.classEq (synCsn (.cv a)) (synCsn A))
      (synWb (synWf1o (synCsn (synCop (.cv a) (.cv b))) (synCsn (.cv a)) (synCsn (.cv b)))
        (synWf1o (synCsn (synCop (.cv a) (.cv b))) (synCsn A) (synCsn (.cv b))))
      p0000 p0001
  have p0003 := @gOpeq1 (.cv a) A (.cv b)
  have p0004 := @gSneq (synCop (.cv a) (.cv b)) (synCop A (.cv b))
  have p0005 :=
    @gF1oeq1 (synCsn A) (synCsn (.cv b)) (synCsn (synCop (.cv a) (.cv b)))
      (synCsn (synCop A (.cv b)))
  have p0006 :=
    @gN3syl (.classEq (.cv a) A)
      (.classEq (synCop (.cv a) (.cv b)) (synCop A (.cv b)))
      (.classEq (synCsn (synCop (.cv a) (.cv b))) (synCsn (synCop A (.cv b))))
      (synWb (synWf1o (synCsn (synCop (.cv a) (.cv b))) (synCsn A) (synCsn (.cv b)))
        (synWf1o (synCsn (synCop A (.cv b))) (synCsn A) (synCsn (.cv b))))
      p0003 p0004 p0005
  have p0007 :=
    @gBitrd (.classEq (.cv a) A)
      (synWf1o (synCsn (synCop (.cv a) (.cv b))) (synCsn (.cv a)) (synCsn (.cv b)))
      (synWf1o (synCsn (synCop (.cv a) (.cv b))) (synCsn A) (synCsn (.cv b)))
      (synWf1o (synCsn (synCop A (.cv b))) (synCsn A) (synCsn (.cv b))) p0002 p0006
  have p0008 := @gSneq (.cv b) B
  have p0009 :=
    @gF1oeq3 (synCsn (.cv b)) (synCsn B) (synCsn A) (synCsn (synCop A (.cv b)))
  have p0010 :=
    @gSyl (.classEq (.cv b) B) (.classEq (synCsn (.cv b)) (synCsn B))
      (synWb (synWf1o (synCsn (synCop A (.cv b))) (synCsn A) (synCsn (.cv b)))
        (synWf1o (synCsn (synCop A (.cv b))) (synCsn A) (synCsn B)))
      p0008 p0009
  have p0011 := @gOpeq2 (.cv b) B A
  have p0012 := @gSneq (synCop A (.cv b)) (synCop A B)
  have p0013 :=
    @gF1oeq1 (synCsn A) (synCsn B) (synCsn (synCop A (.cv b)))
      (synCsn (synCop A B))
  have p0014 :=
    @gN3syl (.classEq (.cv b) B) (.classEq (synCop A (.cv b)) (synCop A B))
      (.classEq (synCsn (synCop A (.cv b))) (synCsn (synCop A B)))
      (synWb (synWf1o (synCsn (synCop A (.cv b))) (synCsn A) (synCsn B))
        (synWf1o (synCsn (synCop A B)) (synCsn A) (synCsn B)))
      p0011 p0012 p0013
  have p0015 :=
    @gBitrd (.classEq (.cv b) B)
      (synWf1o (synCsn (synCop A (.cv b))) (synCsn A) (synCsn (.cv b)))
      (synWf1o (synCsn (synCop A (.cv b))) (synCsn A) (synCsn B))
      (synWf1o (synCsn (synCop A B)) (synCsn A) (synCsn B)) p0010 p0014
  have p0016 := @gVex a
  have p0017 := @gVex b
  have p0018 := @gF1osn (.cv a) (.cv b) p0016 p0017
  have p0019 :=
    @gVtocl2g
      (synWf1o (synCsn (synCop (.cv a) (.cv b))) (synCsn (.cv a)) (synCsn (.cv b)))
      (synWf1o (synCsn (synCop A (.cv b))) (synCsn A) (synCsn (.cv b)))
      (synWf1o (synCsn (synCop A B)) (synCsn A) (synCsn B)) a b A B V W dv_cache_0001
      dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 p0007 p0015 p0018
  exact p0019

/-- Checked nominal proof certificate identified upstream as `g_fv2`. -/
@[expose]
noncomputable def gFv2 (x : Var) (y : Var) (A : Class) (F : Class) (dv_A_x : x ∉ A.fv)
    (dv_A_y : y ∉ A.fv) (dv_F_x : x ∉ F.fv) (dv_F_y : y ∉ F.fv) (dv_x_y : x ≠ y) :
    Nominal.NPrf
      (.classEq (synCfv F A)
        (synCuni (.cab x (.all y (synWb (synWbr A F (.cv y)) (.objEq y x)))))) :=
  by
  have dv_cache_0001 : y ∉ (A).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_A_y, not_false_eq_true])
  have dv_cache_0002 : y ∉ (F).fv :=
    by
    clear dv_cache_0001
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_F_y, not_false_eq_true])
  have dv_cache_0003 : x ∉ ((synWbr A F (.cv y))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, dv_A_x, dv_x_y, dv_F_x, or_false, not_false_eq_true])
  have dv_cache_0004 : y ≠ x :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact (show y ≠ x from (by exact Ne.symm dv_x_y))
  have p0000 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominalDfFv y A F
      dv_cache_0001 dv_cache_0002
  have p0001 := @gDfiota2 (synWbr A F (.cv y)) y x dv_cache_0003 dv_cache_0004
  have p0002 :=
    @gEqtri (synCfv F A) (synCio y (synWbr A F (.cv y)))
      (synCuni (.cab x (.all y (synWb (synWbr A F (.cv y)) (.objEq y x))))) p0000 p0001
  exact p0002

/-- Checked nominal proof certificate identified upstream as `g_fvprc`. -/
@[expose]
noncomputable def gFvprc (A : Class) (F : Class) :
    Nominal.NPrf
      (.imp (.neg (.classMem A (synCvv))) (.classEq (synCfv F A) (synC0))) :=
  by
  let proofSupport : Finset Var := A.fv ∪ F.fv
  let x : Var := freshVar proofSupport 0
  have fresh_x : x ∉ proofSupport :=
    by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_x_not_A : x ∉ A.fv := by
    intro h
    exact fresh_x (Finset.mem_union_left _ (h))
  have fresh_x_not_F : x ∉ F.fv := by
    intro h
    exact fresh_x (Finset.mem_union_right _ (h))
  have dv_cache_0001 : x ∉ (A).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_x_not_A, not_false_eq_true])
  have dv_cache_0002 : x ∉ (F).fv :=
    by
    clear dv_cache_0001
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_x_not_F, not_false_eq_true])
  have dv_cache_0003 : x ∉ ((Wff.classMem A (synCvv))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv, Finset.mem_union,
          fresh_x_not_A, compact_fv_not_mem_empty, or_false, not_false_eq_true])
  have p0000 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominalDfFv x A F
      dv_cache_0001 dv_cache_0002
  have p0001 := @gEuex (synWbr A F (.cv x)) x
  have p0002 := @gBrex A (.cv x) F
  have p0003 :=
    @gSimpld (synWbr A F (.cv x)) (.classMem A (synCvv)) (.classMem (.cv x) (synCvv))
      p0002
  have p0004 :=
    @gExlimiv (synWbr A F (.cv x)) (.classMem A (synCvv)) x dv_cache_0003 p0003
  have p0005 :=
    @gSyl (synWeu x (synWbr A F (.cv x))) (synWex x (synWbr A F (.cv x)))
      (.classMem A (synCvv)) p0001 p0004
  have p0006 := @gCon3i (synWeu x (synWbr A F (.cv x))) (.classMem A (synCvv)) p0005
  have p0007 := @gIotanul (synWbr A F (.cv x)) x
  have p0008 :=
    @gSyl (.neg (.classMem A (synCvv))) (.neg (synWeu x (synWbr A F (.cv x))))
      (.classEq (synCio x (synWbr A F (.cv x))) (synC0)) p0006 p0007
  have p0009 :=
    @gSyl5eq (.neg (.classMem A (synCvv))) (synCfv F A)
      (synCio x (synWbr A F (.cv x))) (synC0) p0000 p0008
  exact p0009

/-- Checked nominal proof certificate identified upstream as `g_elfv`. -/
@[expose]
noncomputable def gElfv (x : Var) (y : Var) (A : Class) (B : Class) (F : Class)
    (dv_A_x : x ∉ A.fv) (dv_B_x : x ∉ B.fv) (dv_B_y : y ∉ B.fv) (dv_F_x : x ∉ F.fv)
    (dv_F_y : y ∉ F.fv) (dv_x_y : x ≠ y) :
    Nominal.NPrf
      (synWb (.classMem A (synCfv F B)) (synWex x (synWa (.classMem A (.cv x))
            (.all y (synWb (synWbr B F (.cv y)) (.objEq y x)))))) :=
  by
  have dv_cache_0001 : x ∉ (B).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_B_x, not_false_eq_true])
  have dv_cache_0002 : y ∉ (B).fv :=
    by
    clear dv_cache_0001
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_B_y, not_false_eq_true])
  have dv_cache_0003 : x ∉ (F).fv :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_F_x, not_false_eq_true])
  have dv_cache_0004 : y ∉ (F).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_F_y, not_false_eq_true])
  have dv_cache_0005 : x ≠ y :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact (show x ≠ y from (by exact dv_x_y))
  have dv_cache_0006 : x ∉ (A).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_A_x, not_false_eq_true])
  have p0000 :=
    @gFv2 x y B F dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
  have p0001 :=
    @gEleq2i (synCfv F B)
      (synCuni (.cab x (.all y (synWb (synWbr B F (.cv y)) (.objEq y x))))) A p0000
  have p0002 :=
    @gEluniab (.all y (synWb (synWbr B F (.cv y)) (.objEq y x))) x A dv_cache_0006
  have p0003 :=
    @gBitri (.classMem A (synCfv F B))
      (.classMem A (synCuni (.cab x (.all y (synWb (synWbr B F (.cv y)) (.objEq y x))))))
      (synWex x (synWa (.classMem A (.cv x))
          (.all y (synWb (synWbr B F (.cv y)) (.objEq y x)))))
      p0001 p0002
  exact p0003

/-- Checked nominal proof certificate identified upstream as `g_fveq1`. -/
@[expose]
noncomputable def gFveq1 (A : Class) (F : Class) (G : Class) :
    Nominal.NPrf (.imp (.classEq F G) (.classEq (synCfv F A) (synCfv G A))) :=
  by
  let proofSupport : Finset Var := A.fv ∪ F.fv ∪ G.fv
  let x : Var := freshVar proofSupport 0
  have fresh_x : x ∉ proofSupport :=
    by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_x_not_A : x ∉ A.fv := by
    intro h
    exact fresh_x (Finset.mem_union_left _ (Finset.mem_union_left _ (h)))
  have fresh_x_not_F : x ∉ F.fv := by
    intro h
    exact fresh_x (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_x_not_G : x ∉ G.fv := by
    intro h
    exact fresh_x (Finset.mem_union_right _ (h))
  have dv_cache_0001 : x ∉ ((Wff.classEq F G)).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, Finset.mem_union,
          fresh_x_not_F, fresh_x_not_G, or_false, not_false_eq_true])
  have dv_cache_0002 : x ∉ (A).fv :=
    by
    clear dv_cache_0001
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_x_not_A, not_false_eq_true])
  have dv_cache_0003 : x ∉ (F).fv :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_x_not_F, not_false_eq_true])
  have dv_cache_0004 : x ∉ (G).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_x_not_G, not_false_eq_true])
  have p0000 := @gBreq A (.cv x) F G
  have p0001 :=
    @gIotabidv (.classEq F G) (synWbr A F (.cv x)) (synWbr A G (.cv x)) x dv_cache_0001
      p0000
  have p0002 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominalDfFv x A F
      dv_cache_0002 dv_cache_0003
  have p0003 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominalDfFv x A G
      dv_cache_0002 dv_cache_0004
  have p0004 :=
    @gN3eqtr4g (.classEq F G) (synCio x (synWbr A F (.cv x)))
      (synCio x (synWbr A G (.cv x))) (synCfv F A) (synCfv G A) p0001 p0002 p0003
  exact p0004

/-- Checked nominal proof certificate identified upstream as `g_fveq2`. -/
@[expose]
noncomputable def gFveq2 (A : Class) (B : Class) (F : Class) :
    Nominal.NPrf (.imp (.classEq A B) (.classEq (synCfv F A) (synCfv F B))) :=
  by
  let proofSupport : Finset Var := A.fv ∪ B.fv ∪ F.fv
  let x : Var := freshVar proofSupport 0
  have fresh_x : x ∉ proofSupport :=
    by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_x_not_A : x ∉ A.fv := by
    intro h
    exact fresh_x (Finset.mem_union_left _ (Finset.mem_union_left _ (h)))
  have fresh_x_not_B : x ∉ B.fv := by
    intro h
    exact fresh_x (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_x_not_F : x ∉ F.fv := by
    intro h
    exact fresh_x (Finset.mem_union_right _ (h))
  have dv_cache_0001 : x ∉ ((Wff.classEq A B)).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, Finset.mem_union,
          fresh_x_not_A, fresh_x_not_B, or_false, not_false_eq_true])
  have dv_cache_0002 : x ∉ (A).fv :=
    by
    clear dv_cache_0001
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_x_not_A, not_false_eq_true])
  have dv_cache_0003 : x ∉ (F).fv :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_x_not_F, not_false_eq_true])
  have dv_cache_0004 : x ∉ (B).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_x_not_B, not_false_eq_true])
  have p0000 := @gBreq1 A B (.cv x) F
  have p0001 :=
    @gIotabidv (.classEq A B) (synWbr A F (.cv x)) (synWbr B F (.cv x)) x dv_cache_0001
      p0000
  have p0002 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominalDfFv x A F
      dv_cache_0002 dv_cache_0003
  have p0003 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominalDfFv x B F
      dv_cache_0004 dv_cache_0003
  have p0004 :=
    @gN3eqtr4g (.classEq A B) (synCio x (synWbr A F (.cv x)))
      (synCio x (synWbr B F (.cv x))) (synCfv F A) (synCfv F B) p0001 p0002 p0003
  exact p0004

/-- Checked nominal proof certificate identified upstream as `g_fveq1i`. -/
@[expose]
noncomputable def gFveq1i (A : Class) (F : Class) (G : Class)
    (hyp_fveq1i_1 : Nominal.NPrf (.classEq F G)) :
    Nominal.NPrf (.classEq (synCfv F A) (synCfv G A)) :=
  by
  have p0000 := @gFveq1 A F G
  have p0001 := Nominal.mp hyp_fveq1i_1 p0000
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_fveq1d`. -/
@[expose]
noncomputable def gFveq1d (ph : Wff) (A : Class) (F : Class) (G : Class)
    (hyp_fveq1d_1 : Nominal.NPrf (.imp ph (.classEq F G))) :
    Nominal.NPrf (.imp ph (.classEq (synCfv F A) (synCfv G A))) :=
  by
  have p0000 := @gFveq1 A F G
  have p0001 :=
    @gSyl ph (.classEq F G) (.classEq (synCfv F A) (synCfv G A)) hyp_fveq1d_1 p0000
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_fveq2i`. -/
@[expose]
noncomputable def gFveq2i (A : Class) (B : Class) (F : Class)
    (hyp_fveq2i_1 : Nominal.NPrf (.classEq A B)) :
    Nominal.NPrf (.classEq (synCfv F A) (synCfv F B)) :=
  by
  have p0000 := @gFveq2 A B F
  have p0001 := Nominal.mp hyp_fveq2i_1 p0000
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_fveq2d`. -/
@[expose]
noncomputable def gFveq2d (ph : Wff) (A : Class) (B : Class) (F : Class)
    (hyp_fveq2d_1 : Nominal.NPrf (.imp ph (.classEq A B))) :
    Nominal.NPrf (.imp ph (.classEq (synCfv F A) (synCfv F B))) :=
  by
  have p0000 := @gFveq2 A B F
  have p0001 :=
    @gSyl ph (.classEq A B) (.classEq (synCfv F A) (synCfv F B)) hyp_fveq2d_1 p0000
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_fvex`. -/
@[expose]
noncomputable def gFvex (A : Class) (F : Class) :
    Nominal.NPrf (.classMem (synCfv F A) (synCvv)) :=
  by
  let proofSupport : Finset Var := A.fv ∪ F.fv
  let x : Var := freshVar proofSupport 0
  have fresh_x : x ∉ proofSupport :=
    by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_x_not_A : x ∉ A.fv := by
    intro h
    exact fresh_x (Finset.mem_union_left _ (h))
  have fresh_x_not_F : x ∉ F.fv := by
    intro h
    exact fresh_x (Finset.mem_union_right _ (h))
  have dv_cache_0001 : x ∉ (A).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_x_not_A, not_false_eq_true])
  have dv_cache_0002 : x ∉ (F).fv :=
    by
    clear dv_cache_0001
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_x_not_F, not_false_eq_true])
  have p0000 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominalDfFv x A F
      dv_cache_0001 dv_cache_0002
  have p0001 := @gIotaex (synWbr A F (.cv x)) x
  have p0002 :=
    @gEqeltri (synCfv F A) (synCio x (synWbr A F (.cv x))) (synCvv) p0000 p0001
  exact p0002


end NFChoice.DirectNominalPrf.WPPReplay

end

/-! Certificates from `NominalWPPReplayChunk012ACompact002Part002`. -/


section

namespace NFChoice.DirectNominalPrf.WPPReplay

open scoped Fol
open NFChoice.Foundation
open NFChoice.SemanticCore
open NFChoice.ReplaySupport
open NFChoice.Compiler.CompactSourceSyntax

/-- Checked nominal proof certificate identified upstream as `g_fv3`. -/
@[expose]
noncomputable def gFv3 (x : Var) (y : Var) (A : Class) (F : Class) (dv_A_x : x ∉ A.fv)
    (dv_A_y : y ∉ A.fv) (dv_F_x : x ∉ F.fv) (dv_F_y : y ∉ F.fv) (dv_x_y : x ≠ y) :
    Nominal.NPrf
      (.classEq (synCfv F A) (.cab x
          (synWa (synWex y (synWa (.classMem (.cv x) (.cv y)) (synWbr A F (.cv y))))
            (synWeu y (synWbr A F (.cv y)))))) :=
  by
  let proofSupport : Finset Var :=
    ({ x } : Finset Var) ∪ ({ y } : Finset Var) ∪ A.fv ∪ F.fv
  let z : Var := freshVar proofSupport 0
  have fresh_z : z ∉ proofSupport :=
    by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_z_ne_x : z ≠ x := by
    intro h
    exact
      fresh_z
        (Finset.mem_union_left _ (Finset.mem_union_left _
            (Finset.mem_union_left _ (Finset.mem_singleton.mpr h))))
  have fresh_z_ne_y : z ≠ y := by
    intro h
    exact
      fresh_z
        (Finset.mem_union_left _ (Finset.mem_union_left _
            (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))))
  have fresh_y_ne_z : y ≠ z := Ne.symm fresh_z_ne_y
  have fresh_z_not_A : z ∉ A.fv := by
    intro h
    exact fresh_z (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_z_not_F : z ∉ F.fv := by
    intro h
    exact fresh_z (Finset.mem_union_right _ (h))
  have dv_cache_0001 : z ∉ ((Class.cv x)).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_z_ne_x, not_false_eq_true])
  have dv_cache_0002 : z ∉ (A).fv :=
    by
    clear dv_cache_0001
    exact
      (by
        have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_z_not_A, not_false_eq_true])
  have dv_cache_0003 : y ∉ (A).fv :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_A_y, not_false_eq_true])
  have dv_cache_0004 : z ∉ (F).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact
      (by
        have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_z_not_F, not_false_eq_true])
  have dv_cache_0005 : y ∉ (F).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_F_y, not_false_eq_true])
  have dv_cache_0006 : z ≠ y :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact (show z ≠ y from (by exact fresh_z_ne_y))
  have dv_cache_0007 : y ∉ ((Class.cv z)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_y_ne_z, not_false_eq_true])
  have dv_cache_0008 : y ∉ ((synWbr A F (.cv z))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, dv_A_y, fresh_y_ne_z, dv_F_y, or_false,
          not_false_eq_true])
  have dv_cache_0009 :
    y ∉ ((synWa (.classMem (.cv x) (.cv z)) (synWbr A F (.cv z)))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr, Finset.mem_union,
          Finset.mem_singleton, (Ne.symm dv_x_y), fresh_y_ne_z, dv_A_y, dv_F_y, or_false,
          not_false_eq_true])
  have dv_cache_0010 :
    z ∉ ((synWa (.classMem (.cv x) (.cv y)) (synWbr A F (.cv y)))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009
    exact
      (by
        have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr, Finset.mem_union,
          Finset.mem_singleton, fresh_z_ne_x, fresh_z_ne_y, fresh_z_not_A, fresh_z_not_F,
          or_false, not_false_eq_true])
  have dv_cache_0011 : y ≠ z :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010
    exact (show y ≠ z from (by exact fresh_y_ne_z))
  have dv_cache_0012 : z ∉ ((synWbr A F (.cv y))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
    exact
      (by
        have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, fresh_z_not_A, fresh_z_ne_y, fresh_z_not_F, or_false,
          not_false_eq_true])
  have dv_cache_0013 : y ∉ ((Wff.classMem (.cv x) (.cv z))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, (Ne.symm dv_x_y), fresh_y_ne_z, or_false,
          not_false_eq_true])
  have dv_cache_0014 : x ∉ ((synCfv F A)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv, Finset.mem_union,
          dv_A_x, dv_F_x, or_false, not_false_eq_true])
  have p0000 :=
    @gElfv z y (.cv x) A F dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
      dv_cache_0005 dv_cache_0006
  have p0001 := @gBi2 (synWbr A F (.cv y)) (.classEq (.cv y) (.cv z))
  have p0002 :=
    @gAlimi (synWb (synWbr A F (.cv y)) (.classEq (.cv y) (.cv z)))
      (.imp (.classEq (.cv y) (.cv z)) (synWbr A F (.cv y))) y p0001
  have p0003 := @gVex z
  have p0004 := @gBreq2 (.cv y) (.cv z) A F
  have p0005 :=
    @gCeqsalv (synWbr A F (.cv y)) (synWbr A F (.cv z)) y (.cv z) dv_cache_0007
      dv_cache_0008 p0003 p0004
  have p0006 :=
    @gSylib (.all y (synWb (synWbr A F (.cv y)) (.classEq (.cv y) (.cv z))))
      (.all y (.imp (.classEq (.cv y) (.cv z)) (synWbr A F (.cv y))))
      (synWbr A F (.cv z)) p0002 p0005
  have p0007 :=
    @gAnim2i (.all y (synWb (synWbr A F (.cv y)) (.classEq (.cv y) (.cv z))))
      (synWbr A F (.cv z)) (.classMem (.cv x) (.cv z)) p0006
  have p0008 :=
    @gEximi
      (synWa (.classMem (.cv x) (.cv z))
        (.all y (synWb (synWbr A F (.cv y)) (.classEq (.cv y) (.cv z)))))
      (synWa (.classMem (.cv x) (.cv z)) (synWbr A F (.cv z))) z p0007
  have p0009 := @gElequ2 z y x
  have p0010 := @gBreq2 (.cv z) (.cv y) A F
  have p0011_e00_recanon :
    Nominal.NPrf
      (.imp (.classEq (.cv z) (.cv y))
        (synWb (.classMem (.cv x) (.cv z)) (.classMem (.cv x) (.cv y)))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold synWb
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · exact Nominal.RecanonTransportDev.TRecanonWff.objEq_classEq _ _
        · apply Nominal.RecanonTransportDev.TRecanonWff.neg
          apply Nominal.RecanonTransportDev.TRecanonWff.imp
          · apply Nominal.RecanonTransportDev.TRecanonWff.imp
            · exact Nominal.RecanonTransportDev.TRecanonWff.objMem_classMem _ _
            · exact Nominal.RecanonTransportDev.TRecanonWff.objMem_classMem _ _
          · apply Nominal.RecanonTransportDev.TRecanonWff.neg
            apply Nominal.RecanonTransportDev.TRecanonWff.imp
            · exact Nominal.RecanonTransportDev.TRecanonWff.objMem_classMem _ _
            · exact Nominal.RecanonTransportDev.TRecanonWff.objMem_classMem _ _)
      p0009
  have p0011 :=
    @gAnbi12d (.classEq (.cv z) (.cv y)) (.classMem (.cv x) (.cv z))
      (.classMem (.cv x) (.cv y)) (synWbr A F (.cv z)) (synWbr A F (.cv y))
      p0011_e00_recanon p0010
  have p0012_e00_recanon :
    Nominal.NPrf
      (.imp (.objEq z y) (synWb (synWa (.classMem (.cv x) (.cv z)) (synWbr A F (.cv z)))
          (synWa (.classMem (.cv x) (.cv y)) (synWbr A F (.cv y))))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold synWb synWa synWbr synCop synCun synCnin synWnan synCcompl synWrex
          synWex synCphi
        simp (config :=
          { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_class_cv]
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
        · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0011
  have p0012 :=
    @gCbvexv (synWa (.classMem (.cv x) (.cv z)) (synWbr A F (.cv z)))
      (synWa (.classMem (.cv x) (.cv y)) (synWbr A F (.cv y))) z y dv_cache_0009
      dv_cache_0010 p0012_e00_recanon
  have p0013 :=
    @gSylib
      (synWex z (synWa (.classMem (.cv x) (.cv z))
          (.all y (synWb (synWbr A F (.cv y)) (.classEq (.cv y) (.cv z))))))
      (synWex z (synWa (.classMem (.cv x) (.cv z)) (synWbr A F (.cv z))))
      (synWex y (synWa (.classMem (.cv x) (.cv y)) (synWbr A F (.cv y)))) p0008 p0012
  have p0014 :=
    @gN1940 (.classMem (.cv x) (.cv z))
      (.all y (synWb (synWbr A F (.cv y)) (.classEq (.cv y) (.cv z)))) z
  have p0015 :=
    @gSimprd
      (synWex z (synWa (.classMem (.cv x) (.cv z))
          (.all y (synWb (synWbr A F (.cv y)) (.classEq (.cv y) (.cv z))))))
      (synWex z (.classMem (.cv x) (.cv z)))
      (synWex z (.all y (synWb (synWbr A F (.cv y)) (.classEq (.cv y) (.cv z))))) p0014
  have p0016 := Nominal.dfEu y z (synWbr A F (.cv y)) dv_cache_0011 dv_cache_0012
  have p0017_e01_recanon :
    Nominal.NPrf
      (synWb (synWeu y (synWbr A F (.cv y)))
        (synWex z (.all y (synWb (synWbr A F (.cv y)) (.classEq (.cv y) (.cv z)))))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold synWb synWeu synWex synWbr synCop synCun synCnin synWnan synWa
          synCcompl synWrex synCphi
        simp (config :=
          { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_class_cv]
        apply Nominal.RecanonTransportDev.TRecanonWff.neg
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · apply Nominal.RecanonTransportDev.TRecanonWff.imp
          · exact Nominal.RecanonTransportDev.TRecanonWff.same _
          · apply Nominal.RecanonTransportDev.TRecanonWff.neg
            apply Nominal.RecanonTransportDev.TRecanonWff.all
            apply Nominal.RecanonTransportDev.TRecanonWff.neg
            apply Nominal.RecanonTransportDev.TRecanonWff.all
            apply Nominal.RecanonTransportDev.TRecanonWff.neg
            apply Nominal.RecanonTransportDev.TRecanonWff.imp
            · apply Nominal.RecanonTransportDev.TRecanonWff.imp
              · exact Nominal.RecanonTransportDev.TRecanonWff.same _
              · exact Nominal.RecanonTransportDev.TRecanonWff.objEq_classEq _ _
            · apply Nominal.RecanonTransportDev.TRecanonWff.neg
              apply Nominal.RecanonTransportDev.TRecanonWff.imp
              · exact Nominal.RecanonTransportDev.TRecanonWff.objEq_classEq _ _
              · exact Nominal.RecanonTransportDev.TRecanonWff.same _
        · apply Nominal.RecanonTransportDev.TRecanonWff.neg
          apply Nominal.RecanonTransportDev.TRecanonWff.imp
          · apply Nominal.RecanonTransportDev.TRecanonWff.neg
            apply Nominal.RecanonTransportDev.TRecanonWff.all
            apply Nominal.RecanonTransportDev.TRecanonWff.neg
            apply Nominal.RecanonTransportDev.TRecanonWff.all
            apply Nominal.RecanonTransportDev.TRecanonWff.neg
            apply Nominal.RecanonTransportDev.TRecanonWff.imp
            · apply Nominal.RecanonTransportDev.TRecanonWff.imp
              · exact Nominal.RecanonTransportDev.TRecanonWff.same _
              · exact Nominal.RecanonTransportDev.TRecanonWff.objEq_classEq _ _
            · apply Nominal.RecanonTransportDev.TRecanonWff.neg
              apply Nominal.RecanonTransportDev.TRecanonWff.imp
              · exact Nominal.RecanonTransportDev.TRecanonWff.objEq_classEq _ _
              · exact Nominal.RecanonTransportDev.TRecanonWff.same _
          · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0016
  have p0017 :=
    @gSylibr
      (synWex z (synWa (.classMem (.cv x) (.cv z))
          (.all y (synWb (synWbr A F (.cv y)) (.classEq (.cv y) (.cv z))))))
      (synWex z (.all y (synWb (synWbr A F (.cv y)) (.classEq (.cv y) (.cv z)))))
      (synWeu y (synWbr A F (.cv y))) p0015 p0017_e01_recanon
  have p0018 :=
    @gJca
      (synWex z (synWa (.classMem (.cv x) (.cv z))
          (.all y (synWb (synWbr A F (.cv y)) (.classEq (.cv y) (.cv z))))))
      (synWex y (synWa (.classMem (.cv x) (.cv y)) (synWbr A F (.cv y))))
      (synWeu y (synWbr A F (.cv y))) p0013 p0017
  have p0019 := @gNfeu1 (synWbr A F (.cv y)) y
  have p0020 := @gNfv (.classMem (.cv x) (.cv z)) y dv_cache_0013
  have p0021 := @gNfa1 (synWb (synWbr A F (.cv y)) (.classEq (.cv y) (.cv z))) y
  have p0022 :=
    @gNfan (.classMem (.cv x) (.cv z))
      (.all y (synWb (synWbr A F (.cv y)) (.classEq (.cv y) (.cv z)))) y p0020 p0021
  have p0023 :=
    @gNfex
      (synWa (.classMem (.cv x) (.cv z))
        (.all y (synWb (synWbr A F (.cv y)) (.classEq (.cv y) (.cv z)))))
      y z p0022
  have p0024 :=
    @gNfim (synWeu y (synWbr A F (.cv y)))
      (synWex z (synWa (.classMem (.cv x) (.cv z))
          (.all y (synWb (synWbr A F (.cv y)) (.classEq (.cv y) (.cv z))))))
      y p0019 p0023
  have p0025 := @gBi1 (synWbr A F (.cv y)) (.classEq (.cv y) (.cv z))
  have p0026 := Nominal.ax14 y z x
  have p0027_e01_recanon :
    Nominal.NPrf
      (.imp (.classEq (.cv y) (.cv z))
        (.imp (.classMem (.cv x) (.cv y)) (.classMem (.cv x) (.cv z)))) :=
    Nominal.RecanonTransportDev.transport
      (by
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · exact Nominal.RecanonTransportDev.TRecanonWff.objEq_classEq _ _
        · apply Nominal.RecanonTransportDev.TRecanonWff.imp
          · exact Nominal.RecanonTransportDev.TRecanonWff.objMem_classMem _ _
          · exact Nominal.RecanonTransportDev.TRecanonWff.objMem_classMem _ _)
      p0026
  have p0027 :=
    @gSyl6 (synWb (synWbr A F (.cv y)) (.classEq (.cv y) (.cv z)))
      (synWbr A F (.cv y)) (.classEq (.cv y) (.cv z))
      (.imp (.classMem (.cv x) (.cv y)) (.classMem (.cv x) (.cv z))) p0025
      p0027_e01_recanon
  have p0028 :=
    @gCom23 (synWb (synWbr A F (.cv y)) (.classEq (.cv y) (.cv z)))
      (synWbr A F (.cv y)) (.classMem (.cv x) (.cv y)) (.classMem (.cv x) (.cv z)) p0027
  have p0029 :=
    @gImp3a (synWb (synWbr A F (.cv y)) (.classEq (.cv y) (.cv z)))
      (.classMem (.cv x) (.cv y)) (synWbr A F (.cv y)) (.classMem (.cv x) (.cv z)) p0028
  have p0030 :=
    @gSps (synWb (synWbr A F (.cv y)) (.classEq (.cv y) (.cv z)))
      (.imp (synWa (.classMem (.cv x) (.cv y)) (synWbr A F (.cv y)))
        (.classMem (.cv x) (.cv z)))
      y p0029
  have p0031 :=
    @gAnc2ri (.all y (synWb (synWbr A F (.cv y)) (.classEq (.cv y) (.cv z))))
      (synWa (.classMem (.cv x) (.cv y)) (synWbr A F (.cv y)))
      (.classMem (.cv x) (.cv z)) p0030
  have p0032 :=
    @gCom12 (.all y (synWb (synWbr A F (.cv y)) (.classEq (.cv y) (.cv z))))
      (synWa (.classMem (.cv x) (.cv y)) (synWbr A F (.cv y)))
      (synWa (.classMem (.cv x) (.cv z))
        (.all y (synWb (synWbr A F (.cv y)) (.classEq (.cv y) (.cv z)))))
      p0031
  have p0033 :=
    @gEximdv (synWa (.classMem (.cv x) (.cv y)) (synWbr A F (.cv y)))
      (.all y (synWb (synWbr A F (.cv y)) (.classEq (.cv y) (.cv z))))
      (synWa (.classMem (.cv x) (.cv z))
        (.all y (synWb (synWbr A F (.cv y)) (.classEq (.cv y) (.cv z)))))
      z dv_cache_0010 p0032
  have p0034_e00_recanon :
    Nominal.NPrf
      (synWb (synWeu y (synWbr A F (.cv y)))
        (synWex z (.all y (synWb (synWbr A F (.cv y)) (.classEq (.cv y) (.cv z)))))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold synWb synWeu synWex synWbr synCop synCun synCnin synWnan synWa
          synCcompl synWrex synCphi
        simp (config :=
          { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_class_cv]
        apply Nominal.RecanonTransportDev.TRecanonWff.neg
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · apply Nominal.RecanonTransportDev.TRecanonWff.imp
          · exact Nominal.RecanonTransportDev.TRecanonWff.same _
          · apply Nominal.RecanonTransportDev.TRecanonWff.neg
            apply Nominal.RecanonTransportDev.TRecanonWff.all
            apply Nominal.RecanonTransportDev.TRecanonWff.neg
            apply Nominal.RecanonTransportDev.TRecanonWff.all
            apply Nominal.RecanonTransportDev.TRecanonWff.neg
            apply Nominal.RecanonTransportDev.TRecanonWff.imp
            · apply Nominal.RecanonTransportDev.TRecanonWff.imp
              · exact Nominal.RecanonTransportDev.TRecanonWff.same _
              · exact Nominal.RecanonTransportDev.TRecanonWff.objEq_classEq _ _
            · apply Nominal.RecanonTransportDev.TRecanonWff.neg
              apply Nominal.RecanonTransportDev.TRecanonWff.imp
              · exact Nominal.RecanonTransportDev.TRecanonWff.objEq_classEq _ _
              · exact Nominal.RecanonTransportDev.TRecanonWff.same _
        · apply Nominal.RecanonTransportDev.TRecanonWff.neg
          apply Nominal.RecanonTransportDev.TRecanonWff.imp
          · apply Nominal.RecanonTransportDev.TRecanonWff.neg
            apply Nominal.RecanonTransportDev.TRecanonWff.all
            apply Nominal.RecanonTransportDev.TRecanonWff.neg
            apply Nominal.RecanonTransportDev.TRecanonWff.all
            apply Nominal.RecanonTransportDev.TRecanonWff.neg
            apply Nominal.RecanonTransportDev.TRecanonWff.imp
            · apply Nominal.RecanonTransportDev.TRecanonWff.imp
              · exact Nominal.RecanonTransportDev.TRecanonWff.same _
              · exact Nominal.RecanonTransportDev.TRecanonWff.objEq_classEq _ _
            · apply Nominal.RecanonTransportDev.TRecanonWff.neg
              apply Nominal.RecanonTransportDev.TRecanonWff.imp
              · exact Nominal.RecanonTransportDev.TRecanonWff.objEq_classEq _ _
              · exact Nominal.RecanonTransportDev.TRecanonWff.same _
          · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0016
  have p0034 :=
    @gSyl5bi (synWeu y (synWbr A F (.cv y)))
      (synWex z (.all y (synWb (synWbr A F (.cv y)) (.classEq (.cv y) (.cv z)))))
      (synWa (.classMem (.cv x) (.cv y)) (synWbr A F (.cv y)))
      (synWex z (synWa (.classMem (.cv x) (.cv z))
          (.all y (synWb (synWbr A F (.cv y)) (.classEq (.cv y) (.cv z))))))
      p0034_e00_recanon p0033
  have p0035 :=
    @gExlimi (synWa (.classMem (.cv x) (.cv y)) (synWbr A F (.cv y)))
      (.imp (synWeu y (synWbr A F (.cv y))) (synWex z (synWa (.classMem (.cv x) (.cv z))
            (.all y (synWb (synWbr A F (.cv y)) (.classEq (.cv y) (.cv z)))))))
      y p0024 p0034
  have p0036 :=
    @gImp (synWex y (synWa (.classMem (.cv x) (.cv y)) (synWbr A F (.cv y))))
      (synWeu y (synWbr A F (.cv y)))
      (synWex z (synWa (.classMem (.cv x) (.cv z))
          (.all y (synWb (synWbr A F (.cv y)) (.classEq (.cv y) (.cv z))))))
      p0035
  have p0037 :=
    @gImpbii
      (synWex z (synWa (.classMem (.cv x) (.cv z))
          (.all y (synWb (synWbr A F (.cv y)) (.classEq (.cv y) (.cv z))))))
      (synWa (synWex y (synWa (.classMem (.cv x) (.cv y)) (synWbr A F (.cv y))))
        (synWeu y (synWbr A F (.cv y))))
      p0018 p0036
  have p0038_e00_recanon :
    Nominal.NPrf
      (synWb (.classMem (.cv x) (synCfv F A)) (synWex z (synWa (.classMem (.cv x) (.cv z))
            (.all y (synWb (synWbr A F (.cv y)) (.classEq (.cv y) (.cv z))))))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold synWb synCfv synCio synCuni synWex synWa synCsn synWbr synCop
          synCun synCnin synWnan synCcompl synWrex synCphi
        simp (config :=
          {
            failIfUnchanged :=
              false }) only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv]
        apply Nominal.RecanonTransportDev.TRecanonWff.neg
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · apply Nominal.RecanonTransportDev.TRecanonWff.imp
          · exact Nominal.RecanonTransportDev.TRecanonWff.same _
          · apply Nominal.RecanonTransportDev.TRecanonWff.neg
            apply Nominal.RecanonTransportDev.TRecanonWff.all
            apply Nominal.RecanonTransportDev.TRecanonWff.neg
            apply Nominal.RecanonTransportDev.TRecanonWff.neg
            apply Nominal.RecanonTransportDev.TRecanonWff.imp
            · exact Nominal.RecanonTransportDev.TRecanonWff.same _
            · apply Nominal.RecanonTransportDev.TRecanonWff.neg
              apply Nominal.RecanonTransportDev.TRecanonWff.all
              apply Nominal.RecanonTransportDev.TRecanonWff.neg
              apply Nominal.RecanonTransportDev.TRecanonWff.imp
              · apply Nominal.RecanonTransportDev.TRecanonWff.imp
                · exact Nominal.RecanonTransportDev.TRecanonWff.same _
                · exact Nominal.RecanonTransportDev.TRecanonWff.objEq_classEq _ _
              · apply Nominal.RecanonTransportDev.TRecanonWff.neg
                apply Nominal.RecanonTransportDev.TRecanonWff.imp
                · exact Nominal.RecanonTransportDev.TRecanonWff.objEq_classEq _ _
                · exact Nominal.RecanonTransportDev.TRecanonWff.same _
        · apply Nominal.RecanonTransportDev.TRecanonWff.neg
          apply Nominal.RecanonTransportDev.TRecanonWff.imp
          · apply Nominal.RecanonTransportDev.TRecanonWff.neg
            apply Nominal.RecanonTransportDev.TRecanonWff.all
            apply Nominal.RecanonTransportDev.TRecanonWff.neg
            apply Nominal.RecanonTransportDev.TRecanonWff.neg
            apply Nominal.RecanonTransportDev.TRecanonWff.imp
            · exact Nominal.RecanonTransportDev.TRecanonWff.same _
            · apply Nominal.RecanonTransportDev.TRecanonWff.neg
              apply Nominal.RecanonTransportDev.TRecanonWff.all
              apply Nominal.RecanonTransportDev.TRecanonWff.neg
              apply Nominal.RecanonTransportDev.TRecanonWff.imp
              · apply Nominal.RecanonTransportDev.TRecanonWff.imp
                · exact Nominal.RecanonTransportDev.TRecanonWff.same _
                · exact Nominal.RecanonTransportDev.TRecanonWff.objEq_classEq _ _
              · apply Nominal.RecanonTransportDev.TRecanonWff.neg
                apply Nominal.RecanonTransportDev.TRecanonWff.imp
                · exact Nominal.RecanonTransportDev.TRecanonWff.objEq_classEq _ _
                · exact Nominal.RecanonTransportDev.TRecanonWff.same _
          · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0000
  have p0038 :=
    @gBitri (.classMem (.cv x) (synCfv F A))
      (synWex z (synWa (.classMem (.cv x) (.cv z))
          (.all y (synWb (synWbr A F (.cv y)) (.classEq (.cv y) (.cv z))))))
      (synWa (synWex y (synWa (.classMem (.cv x) (.cv y)) (synWbr A F (.cv y))))
        (synWeu y (synWbr A F (.cv y))))
      p0038_e00_recanon p0037
  have p0039 :=
    @gEqabi
      (synWa (synWex y (synWa (.classMem (.cv x) (.cv y)) (synWbr A F (.cv y))))
        (synWeu y (synWbr A F (.cv y))))
      x (synCfv F A) dv_cache_0014 p0038
  exact p0039

/-- Checked nominal proof certificate identified upstream as `g_fvres`. -/
@[expose]
noncomputable def gFvres (A : Class) (B : Class) (F : Class) :
    Nominal.NPrf
      (.imp (.classMem A B) (.classEq (synCfv (synCres F B) A) (synCfv F A))) :=
  by
  let proofSupport : Finset Var := A.fv ∪ B.fv ∪ F.fv
  let x : Var := freshVar proofSupport 0
  have fresh_x : x ∉ proofSupport :=
    by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_x_not_A : x ∉ A.fv := by
    intro h
    exact fresh_x (Finset.mem_union_left _ (Finset.mem_union_left _ (h)))
  have fresh_x_not_B : x ∉ B.fv := by
    intro h
    exact fresh_x (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_x_not_F : x ∉ F.fv := by
    intro h
    exact fresh_x (Finset.mem_union_right _ (h))
  have dv_cache_0001 : x ∉ ((Wff.classMem A B)).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, Finset.mem_union,
          fresh_x_not_A, fresh_x_not_B, or_false, not_false_eq_true])
  have dv_cache_0002 : x ∉ (A).fv :=
    by
    clear dv_cache_0001
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_x_not_A, not_false_eq_true])
  have dv_cache_0003 : x ∉ ((synCres F B)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cres,
          Finset.mem_union, fresh_x_not_F, fresh_x_not_B, or_false, not_false_eq_true])
  have dv_cache_0004 : x ∉ (F).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_x_not_F, not_false_eq_true])
  have p0000 := @gIba (.classMem A B) (synWbr A F (.cv x))
  have p0001 := @gBrres A (.cv x) F B
  have p0002 :=
    @gSyl6rbbr (.classMem A B) (synWbr A F (.cv x))
      (synWa (synWbr A F (.cv x)) (.classMem A B)) (synWbr A (synCres F B) (.cv x))
      p0000 p0001
  have p0003 :=
    @gIotabidv (.classMem A B) (synWbr A (synCres F B) (.cv x)) (synWbr A F (.cv x)) x
      dv_cache_0001 p0002
  have p0004 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominalDfFv x A
      (synCres F B) dv_cache_0002 dv_cache_0003
  have p0005 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominalDfFv x A F
      dv_cache_0002 dv_cache_0004
  have p0006 :=
    @gN3eqtr4g (.classMem A B) (synCio x (synWbr A (synCres F B) (.cv x)))
      (synCio x (synWbr A F (.cv x))) (synCfv (synCres F B) A) (synCfv F A) p0003
      p0004 p0005
  exact p0006

/-- Checked nominal proof certificate identified upstream as `g_funssfv`. -/
@[expose]
noncomputable def gFunssfv (A : Class) (F : Class) (G : Class) :
    Nominal.NPrf
      (.imp (synW3a (synWfun F) (synWss G F) (.classMem A (synCdm G)))
        (.classEq (synCfv F A) (synCfv G A))) :=
  by
  have p0000 := @gFvres A (synCdm G) F
  have p0001 :=
    @gEqcomd (.classMem A (synCdm G)) (synCfv (synCres F (synCdm G)) A) (synCfv F A)
      p0000
  have p0002 := @gFunssres F G
  have p0003 :=
    @gFveq1d (synWa (synWfun F) (synWss G F)) A (synCres F (synCdm G)) G p0002
  have p0004 :=
    @gSylan9eqr (.classMem A (synCdm G)) (synWa (synWfun F) (synWss G F))
      (synCfv F A) (synCfv (synCres F (synCdm G)) A) (synCfv G A) p0001 p0003
  have p0005 :=
    @gN3impa (synWfun F) (synWss G F) (.classMem A (synCdm G))
      (.classEq (synCfv F A) (synCfv G A)) p0004
  exact p0005

/-- Checked nominal proof certificate identified upstream as `g_tz6_12_1`. -/
@[expose]
noncomputable def g_tz6_12_1 (y : Var) (A : Class) (B : Class) (F : Class)
    (dv_A_y : y ∉ A.fv) (dv_F_y : y ∉ F.fv) :
    Nominal.NPrf
      (.imp (synWa (synWbr A F B) (synWeu y (synWbr A F (.cv y))))
        (.classEq (synCfv F A) B)) :=
  by
  let proofSupport : Finset Var := ({ y } : Finset Var) ∪ A.fv ∪ B.fv ∪ F.fv
  let x : Var := freshVar proofSupport 0
  have fresh_x : x ∉ proofSupport :=
    by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_x_ne_y : x ≠ y := by
    intro h
    exact
      fresh_x
        (Finset.mem_union_left _ (Finset.mem_union_left _
            (Finset.mem_union_left _ (Finset.mem_singleton.mpr h))))
  have fresh_y_ne_x : y ≠ x := Ne.symm fresh_x_ne_y
  have fresh_x_not_A : x ∉ A.fv := by
    intro h
    exact
      fresh_x
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))
  have fresh_x_not_B : x ∉ B.fv := by
    intro h
    exact fresh_x (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_x_not_F : x ∉ F.fv := by
    intro h
    exact fresh_x (Finset.mem_union_right _ (h))
  have dv_cache_0001 : x ∉ ((synWbr A F (.cv y))).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, fresh_x_not_A, fresh_x_ne_y, fresh_x_not_F, or_false,
          not_false_eq_true])
  have dv_cache_0002 : y ∉ ((synWbr A F (.cv x))).fv :=
    by
    clear dv_cache_0001
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, dv_A_y, fresh_y_ne_x, dv_F_y, or_false,
          not_false_eq_true])
  have dv_cache_0003 : x ∉ (A).fv :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_x_not_A, not_false_eq_true])
  have dv_cache_0004 : x ∉ (F).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_x_not_F, not_false_eq_true])
  have dv_cache_0005 : x ∉ (B).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_x_not_B, not_false_eq_true])
  have dv_cache_0006 : x ∉ ((synWbr A F B)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr, Finset.mem_union,
          fresh_x_not_A, fresh_x_not_B, fresh_x_not_F, or_false, not_false_eq_true])
  have p0000 := @gNfv (synWbr A F (.cv y)) x dv_cache_0001
  have p0001 := @gNfv (synWbr A F (.cv x)) y dv_cache_0002
  have p0002 := @gBreq2 (.cv y) (.cv x) A F
  have p0003_e02_recanon :
    Nominal.NPrf
      (.imp (.objEq y x) (synWb (synWbr A F (.cv y)) (synWbr A F (.cv x)))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold synWb synWbr synCop synCun synCnin synWnan synWa synCcompl synWrex
          synWex synCphi
        simp (config :=
          { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_class_cv]
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
        · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0002
  have p0003 :=
    @gCbveu (synWbr A F (.cv y)) (synWbr A F (.cv x)) y x p0000 p0001 p0003_e02_recanon
  have p0004 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominalDfFv x A F
      dv_cache_0003 dv_cache_0004
  have p0005 := @gBrrelrnex A B F
  have p0006 :=
    @gAdantr (synWbr A F B) (.classMem B (synCvv)) (synWeu x (synWbr A F (.cv x)))
      p0005
  have p0007 := @gBreq2 (.cv x) B A F
  have p0008 :=
    @gIota2 (synWbr A F (.cv x)) (synWbr A F B) x B (synCvv) dv_cache_0005
      dv_cache_0006 p0007
  have p0009 :=
    @gBiimpd (synWa (.classMem B (synCvv)) (synWeu x (synWbr A F (.cv x))))
      (synWbr A F B) (.classEq (synCio x (synWbr A F (.cv x))) B) p0008
  have p0010 :=
    @gEx (.classMem B (synCvv)) (synWeu x (synWbr A F (.cv x)))
      (.imp (synWbr A F B) (.classEq (synCio x (synWbr A F (.cv x))) B)) p0009
  have p0011 :=
    @gCom23 (.classMem B (synCvv)) (synWeu x (synWbr A F (.cv x))) (synWbr A F B)
      (.classEq (synCio x (synWbr A F (.cv x))) B) p0010
  have p0012 :=
    @gImp3a (.classMem B (synCvv)) (synWbr A F B) (synWeu x (synWbr A F (.cv x)))
      (.classEq (synCio x (synWbr A F (.cv x))) B) p0011
  have p0013 :=
    @gMpcom (.classMem B (synCvv))
      (synWa (synWbr A F B) (synWeu x (synWbr A F (.cv x))))
      (.classEq (synCio x (synWbr A F (.cv x))) B) p0006 p0012
  have p0014 :=
    @gSyl5eq (synWa (synWbr A F B) (synWeu x (synWbr A F (.cv x)))) (synCfv F A)
      (synCio x (synWbr A F (.cv x))) B p0004 p0013
  have p0015 :=
    @gSylan2b (synWeu y (synWbr A F (.cv y))) (synWbr A F B)
      (synWeu x (synWbr A F (.cv x))) (.classEq (synCfv F A) B) p0003 p0014
  exact p0015

/-- Checked nominal proof certificate identified upstream as `g_tz6_12_2`. -/
@[expose]
noncomputable def g_tz6_12_2 (y : Var) (A : Class) (F : Class) (dv_A_y : y ∉ A.fv)
    (dv_F_y : y ∉ F.fv) :
    Nominal.NPrf
      (.imp (.neg (synWeu y (synWbr A F (.cv y)))) (.classEq (synCfv F A) (synC0))) :=
  by
  let proofSupport : Finset Var := ({ y } : Finset Var) ∪ A.fv ∪ F.fv
  let x : Var := freshVar proofSupport 0
  let z : Var := freshVar proofSupport 1
  have fresh_x : x ∉ proofSupport :=
    by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_x_ne_y : x ≠ y := by
    intro h
    exact
      fresh_x
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_singleton.mpr h)))
  have fresh_y_ne_x : y ≠ x := Ne.symm fresh_x_ne_y
  have fresh_x_not_A : x ∉ A.fv := by
    intro h
    exact fresh_x (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_x_not_F : x ∉ F.fv := by
    intro h
    exact fresh_x (Finset.mem_union_right _ (h))
  have fresh_z : z ∉ proofSupport :=
    by
    change freshVar proofSupport 1 ∉ proofSupport
    exact freshVar_not_mem proofSupport 1
  have fresh_z_ne_y : z ≠ y := by
    intro h
    exact
      fresh_z
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_singleton.mpr h)))
  have fresh_y_ne_z : y ≠ z := Ne.symm fresh_z_ne_y
  have fresh_z_not_A : z ∉ A.fv := by
    intro h
    exact fresh_z (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_z_not_F : z ∉ F.fv := by
    intro h
    exact fresh_z (Finset.mem_union_right _ (h))
  have fresh_x_ne_z : x ≠ z :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have fresh_z_ne_x : z ≠ x := Ne.symm fresh_x_ne_z
  have dv_cache_0001 : x ∉ (A).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_x_not_A, not_false_eq_true])
  have dv_cache_0002 : y ∉ (A).fv :=
    by
    clear dv_cache_0001
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_A_y, not_false_eq_true])
  have dv_cache_0003 : x ∉ (F).fv :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_x_not_F, not_false_eq_true])
  have dv_cache_0004 : y ∉ (F).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_F_y, not_false_eq_true])
  have dv_cache_0005 : x ≠ y :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact (show x ≠ y from (by exact fresh_x_ne_y))
  have dv_cache_0006 : y ∉ ((Wff.objEq x z)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_objEq, Finset.mem_insert,
          Finset.mem_singleton, fresh_y_ne_x, fresh_y_ne_z, or_false, not_false_eq_true])
  have dv_cache_0007 : x ∉ ((Class.cv z)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_x_ne_z, not_false_eq_true])
  have dv_cache_0008 :
    x ∉
      ((synWa (synWex y (synWa (.objMem z y) (synWbr A F (.cv y))))
          (synWeu y (synWbr A F (.cv y))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wex,
          NFChoice.Compiler.CoreFVSimp.fv_wff_objMem,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_weu, Finset.mem_union,
          Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_x_ne_z,
          fresh_x_ne_y, fresh_x_not_A, fresh_x_not_F, or_false, and_false,
          not_false_eq_true])
  have dv_cache_0009 :
    z ∉
      ((Class.cab x (synWa (synWex y (synWa (.objMem x y) (synWbr A F (.cv y))))
            (synWeu y (synWbr A F (.cv y)))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008
    exact
      (by
        have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cab,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wex,
          NFChoice.Compiler.CoreFVSimp.fv_wff_objMem,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_weu, Finset.mem_union,
          Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, fresh_z_ne_x,
          fresh_z_ne_y, fresh_z_not_A, fresh_z_not_F, or_false, and_false,
          not_false_eq_true])
  have dv_cache_0010 : z ∉ ((Wff.neg (synWeu y (synWbr A F (.cv y))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009
    exact
      (by
        have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_neg,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_weu,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase,
          Finset.mem_singleton, fresh_z_not_A, fresh_z_ne_y, fresh_z_not_F, or_false,
          and_false, not_false_eq_true])
  have p0000 :=
    @gFv3 x y A F dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
  have p0001 := @gVex z
  have p0002 := @gElequ1 x z y
  have p0003 :=
    @gAnbi1d (.objEq x z) (.objMem x y) (.objMem z y) (synWbr A F (.cv y)) p0002
  have p0004 :=
    @gExbidv (.objEq x z) (synWa (.objMem x y) (synWbr A F (.cv y)))
      (synWa (.objMem z y) (synWbr A F (.cv y))) y dv_cache_0006 p0003
  have p0005 :=
    @gAnbi1d (.objEq x z) (synWex y (synWa (.objMem x y) (synWbr A F (.cv y))))
      (synWex y (synWa (.objMem z y) (synWbr A F (.cv y))))
      (synWeu y (synWbr A F (.cv y))) p0004
  have p0006_e01_recanon :
    Nominal.NPrf
      (.imp (.classEq (.cv x) (.cv z)) (synWb
          (synWa (synWex y (synWa (.objMem x y) (synWbr A F (.cv y))))
            (synWeu y (synWbr A F (.cv y))))
          (synWa (synWex y (synWa (.objMem z y) (synWbr A F (.cv y))))
            (synWeu y (synWbr A F (.cv y)))))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold synWb synWa synWex synWeu synWbr synCop synCun synCnin synWnan
          synCcompl synWrex synCphi
        simp (config :=
          { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_class_cv]
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · exact Nominal.RecanonTransportDev.TRecanonWff.objEq_classEq _ _
        · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0005
  have p0006 :=
    @gElab
      (synWa (synWex y (synWa (.objMem x y) (synWbr A F (.cv y))))
        (synWeu y (synWbr A F (.cv y))))
      (synWa (synWex y (synWa (.objMem z y) (synWbr A F (.cv y))))
        (synWeu y (synWbr A F (.cv y))))
      x (.cv z) dv_cache_0007 dv_cache_0008 p0001 p0006_e01_recanon
  have p0007 :=
    @gSimprbi
      (.classMem (.cv z) (.cab x
          (synWa (synWex y (synWa (.objMem x y) (synWbr A F (.cv y))))
            (synWeu y (synWbr A F (.cv y))))))
      (synWex y (synWa (.objMem z y) (synWbr A F (.cv y))))
      (synWeu y (synWbr A F (.cv y))) p0006
  have p0008 :=
    @gCon3i
      (.classMem (.cv z) (.cab x
          (synWa (synWex y (synWa (.objMem x y) (synWbr A F (.cv y))))
            (synWeu y (synWbr A F (.cv y))))))
      (synWeu y (synWbr A F (.cv y))) p0007
  have p0009 :=
    @gEq0rdv (.neg (synWeu y (synWbr A F (.cv y)))) z
      (.cab x (synWa (synWex y (synWa (.objMem x y) (synWbr A F (.cv y))))
          (synWeu y (synWbr A F (.cv y)))))
      dv_cache_0009 dv_cache_0010 p0008
  have p0010_e00_recanon :
    Nominal.NPrf
      (.classEq (synCfv F A) (.cab x
          (synWa (synWex y (synWa (.objMem x y) (synWbr A F (.cv y))))
            (synWeu y (synWbr A F (.cv y)))))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold synCfv synCio synCuni synWex synWa synCsn synWbr synCop synCun
          synCnin synWnan synCcompl synWrex synCphi
        simp (config :=
          { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CoreFVSimp.fv_class_cab,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv]
        apply Nominal.RecanonTransportDev.TRecanonWff.classEq
        · exact Nominal.RecanonTransportDev.TRecanonClass.same _
        · apply Nominal.RecanonTransportDev.TRecanonClass.cab
          apply Nominal.RecanonTransportDev.TRecanonWff.neg
          apply Nominal.RecanonTransportDev.TRecanonWff.imp
          · apply Nominal.RecanonTransportDev.TRecanonWff.neg
            apply Nominal.RecanonTransportDev.TRecanonWff.all
            apply Nominal.RecanonTransportDev.TRecanonWff.neg
            apply Nominal.RecanonTransportDev.TRecanonWff.neg
            apply Nominal.RecanonTransportDev.TRecanonWff.imp
            · exact Nominal.RecanonTransportDev.TRecanonWff.classMem_objMem _ _
            · exact Nominal.RecanonTransportDev.TRecanonWff.same _
          · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0000
  have p0010 :=
    @gSyl5eq (.neg (synWeu y (synWbr A F (.cv y)))) (synCfv F A)
      (.cab x (synWa (synWex y (synWa (.objMem x y) (synWbr A F (.cv y))))
          (synWeu y (synWbr A F (.cv y)))))
      (synC0) p0010_e00_recanon p0009
  exact p0010

/-- Checked nominal proof certificate identified upstream as `g_tz6_12c`. -/
@[expose]
noncomputable def gTz612c (y : Var) (A : Class) (B : Class) (F : Class)
    (dv_A_y : y ∉ A.fv) (dv_F_y : y ∉ F.fv) :
    Nominal.NPrf
      (.imp (synWeu y (synWbr A F (.cv y)))
        (synWb (.classEq (synCfv F A) B) (synWbr A F B))) :=
  by
  have dv_cache_0001 : y ∉ ((synWbr A F (synCfv F A))).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv, Finset.mem_union, dv_A_y,
          dv_F_y, or_false, not_false_eq_true])
  have dv_cache_0002 : y ∉ (A).fv :=
    by
    clear dv_cache_0001
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_A_y, not_false_eq_true])
  have dv_cache_0003 : y ∉ (F).fv :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_F_y, not_false_eq_true])
  have p0000 := @gEuex (synWbr A F (.cv y)) y
  have p0001 := @gNfeu1 (synWbr A F (.cv y)) y
  have p0002 := @gNfv (synWbr A F (synCfv F A)) y dv_cache_0001
  have p0003 :=
    @gNfim (synWeu y (synWbr A F (.cv y))) (synWbr A F (synCfv F A)) y p0001 p0002
  have p0004 := @g_tz6_12_1 y A (.cv y) F dv_cache_0002 dv_cache_0003
  have p0005 :=
    @gExpcom (synWbr A F (.cv y)) (synWeu y (synWbr A F (.cv y)))
      (.classEq (synCfv F A) (.cv y)) p0004
  have p0006 := @gBreq2 (synCfv F A) (.cv y) A F
  have p0007 :=
    @gBiimprd (.classEq (synCfv F A) (.cv y)) (synWbr A F (synCfv F A))
      (synWbr A F (.cv y)) p0006
  have p0008 :=
    @gSyli (synWbr A F (.cv y)) (synWeu y (synWbr A F (.cv y)))
      (.classEq (synCfv F A) (.cv y)) (synWbr A F (synCfv F A)) p0005 p0007
  have p0009 :=
    @gCom12 (synWeu y (synWbr A F (.cv y))) (synWbr A F (.cv y))
      (synWbr A F (synCfv F A)) p0008
  have p0010 :=
    @gExlimi (synWbr A F (.cv y))
      (.imp (synWeu y (synWbr A F (.cv y))) (synWbr A F (synCfv F A))) y p0003 p0009
  have p0011 :=
    @gMpcom (synWex y (synWbr A F (.cv y))) (synWeu y (synWbr A F (.cv y)))
      (synWbr A F (synCfv F A)) p0000 p0010
  have p0012 := @gBreq2 (synCfv F A) B A F
  have p0013 :=
    @gSyl5ibcom (synWeu y (synWbr A F (.cv y))) (synWbr A F (synCfv F A))
      (.classEq (synCfv F A) B) (synWbr A F B) p0011 p0012
  have p0014 := @g_tz6_12_1 y A B F dv_cache_0002 dv_cache_0003
  have p0015 :=
    @gExpcom (synWbr A F B) (synWeu y (synWbr A F (.cv y))) (.classEq (synCfv F A) B)
      p0014
  have p0016 :=
    @gImpbid (synWeu y (synWbr A F (.cv y))) (.classEq (synCfv F A) B) (synWbr A F B)
      p0013 p0015
  exact p0016

/-- Checked nominal proof certificate identified upstream as `g_ndmfv`. -/
@[expose]
noncomputable def gNdmfv (A : Class) (F : Class) :
    Nominal.NPrf
      (.imp (.neg (.classMem A (synCdm F))) (.classEq (synCfv F A) (synC0))) :=
  by
  let proofSupport : Finset Var := A.fv ∪ F.fv
  let x : Var := freshVar proofSupport 0
  have fresh_x : x ∉ proofSupport :=
    by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_x_not_A : x ∉ A.fv := by
    intro h
    exact fresh_x (Finset.mem_union_left _ (h))
  have fresh_x_not_F : x ∉ F.fv := by
    intro h
    exact fresh_x (Finset.mem_union_right _ (h))
  have dv_cache_0001 : x ∉ (A).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_x_not_A, not_false_eq_true])
  have dv_cache_0002 : x ∉ (F).fv :=
    by
    clear dv_cache_0001
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_x_not_F, not_false_eq_true])
  have p0000 := @gEldm x A F dv_cache_0001 dv_cache_0002
  have p0001 := @gEuex (synWbr A F (.cv x)) x
  have p0002 :=
    @gCon3i (synWeu x (synWbr A F (.cv x))) (synWex x (synWbr A F (.cv x))) p0001
  have p0003 := @g_tz6_12_2 x A F dv_cache_0001 dv_cache_0002
  have p0004 :=
    @gSyl (.neg (synWex x (synWbr A F (.cv x))))
      (.neg (synWeu x (synWbr A F (.cv x)))) (.classEq (synCfv F A) (synC0)) p0002
      p0003
  have p0005 :=
    @gSylnbi (.classMem A (synCdm F)) (synWex x (synWbr A F (.cv x)))
      (.classEq (synCfv F A) (synC0)) p0000 p0004
  exact p0005

/-- Checked nominal proof certificate identified upstream as `g_elfvdm`. -/
@[expose]
noncomputable def gElfvdm (A : Class) (B : Class) (F : Class) :
    Nominal.NPrf (.imp (.classMem A (synCfv F B)) (.classMem B (synCdm F))) :=
  by
  have p0000 := @gNe0i (synCfv F B) A
  have p0001 := @gNdmfv B F
  have p0002 := @gNecon1ai (.classMem B (synCdm F)) (synCfv F B) (synC0) p0001
  have p0003 :=
    @gSyl (.classMem A (synCfv F B)) (synWne (synCfv F B) (synC0))
      (.classMem B (synCdm F)) p0000 p0002
  exact p0003


end NFChoice.DirectNominalPrf.WPPReplay

end

/-! Certificates from `NominalWPPReplayChunk012ACompact002Part003`. -/


section

namespace NFChoice.DirectNominalPrf.WPPReplay

open scoped Fol
open NFChoice.Foundation
open NFChoice.SemanticCore
open NFChoice.ReplaySupport
open NFChoice.Compiler.CompactSourceSyntax

/-- Checked nominal proof certificate identified upstream as `g_funbrfv`. -/
@[expose]
noncomputable def gFunbrfv (A : Class) (B : Class) (F : Class) :
    Nominal.NPrf (.imp (synWfun F) (.imp (synWbr A F B) (.classEq (synCfv F A) B))) :=
  by
  let proofSupport : Finset Var := A.fv ∪ B.fv ∪ F.fv
  let y : Var := freshVar proofSupport 0
  have fresh_y : y ∉ proofSupport :=
    by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_y_not_A : y ∉ A.fv := by
    intro h
    exact fresh_y (Finset.mem_union_left _ (Finset.mem_union_left _ (h)))
  have fresh_y_not_F : y ∉ F.fv := by
    intro h
    exact fresh_y (Finset.mem_union_right _ (h))
  have dv_cache_0001 : y ∉ (A).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_y_not_A, not_false_eq_true])
  have dv_cache_0002 : y ∉ (F).fv :=
    by
    clear dv_cache_0001
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_y_not_F, not_false_eq_true])
  have p0000 := @gFuneu y A B F dv_cache_0001 dv_cache_0002
  have p0001 := @g_tz6_12_1 y A B F dv_cache_0001 dv_cache_0002
  have p0002 :=
    @gSylan2 (synWa (synWfun F) (synWbr A F B)) (synWbr A F B)
      (synWeu y (synWbr A F (.cv y))) (.classEq (synCfv F A) B) p0000 p0001
  have p0003 := @gAnabss7 (synWfun F) (synWbr A F B) (.classEq (synCfv F A) B) p0002
  have p0004 := @gEx (synWfun F) (synWbr A F B) (.classEq (synCfv F A) B) p0003
  exact p0004

/-- Checked nominal proof certificate identified upstream as `g_funopfv`. -/
@[expose]
noncomputable def gFunopfv (A : Class) (B : Class) (F : Class) :
    Nominal.NPrf
      (.imp (synWfun F) (.imp (.classMem (synCop A B) F) (.classEq (synCfv F A) B))) :=
  by
  have p0000 := (Nominal.biimpRefl (synWbr A F B))
  have p0001 := @gFunbrfv A B F
  have p0002 :=
    @gSyl5bir (.classMem (synCop A B) F) (synWbr A F B) (synWfun F)
      (.classEq (synCfv F A) B) p0000 p0001
  exact p0002

/-- Checked nominal proof certificate identified upstream as `g_fnbrfvb`. -/
@[expose]
noncomputable def gFnbrfvb (A : Class) (B : Class) (C : Class) (F : Class) :
    Nominal.NPrf
      (.imp (synWa (synWfn F A) (.classMem B A))
        (synWb (.classEq (synCfv F B) C) (synWbr B F C))) :=
  by
  let proofSupport : Finset Var := A.fv ∪ B.fv ∪ C.fv ∪ F.fv
  let x : Var := freshVar proofSupport 0
  have fresh_x : x ∉ proofSupport :=
    by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_x_not_B : x ∉ B.fv := by
    intro h
    exact
      fresh_x
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))
  have fresh_x_not_F : x ∉ F.fv := by
    intro h
    exact fresh_x (Finset.mem_union_right _ (h))
  have dv_cache_0001 : x ∉ (B).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_x_not_B, not_false_eq_true])
  have dv_cache_0002 : x ∉ (F).fv :=
    by
    clear dv_cache_0001
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_x_not_F, not_false_eq_true])
  have p0000 := @gFneu x A B F dv_cache_0001 dv_cache_0002
  have p0001 := @gTz612c x B C F dv_cache_0001 dv_cache_0002
  have p0002 :=
    @gSyl (synWa (synWfn F A) (.classMem B A)) (synWeu x (synWbr B F (.cv x)))
      (synWb (.classEq (synCfv F B) C) (synWbr B F C)) p0000 p0001
  exact p0002

/-- Checked nominal proof certificate identified upstream as `g_fnopfvb`. -/
@[expose]
noncomputable def gFnopfvb (A : Class) (B : Class) (C : Class) (F : Class) :
    Nominal.NPrf
      (.imp (synWa (synWfn F A) (.classMem B A))
        (synWb (.classEq (synCfv F B) C) (.classMem (synCop B C) F))) :=
  by
  have p0000 := @gFnbrfvb A B C F
  have p0001 := (Nominal.biimpRefl (synWbr B F C))
  have p0002 :=
    @gSyl6bb (synWa (synWfn F A) (.classMem B A)) (.classEq (synCfv F B) C)
      (synWbr B F C) (.classMem (synCop B C) F) p0000 p0001
  exact p0002

/-- Checked nominal proof certificate identified upstream as `g_funbrfvb`. -/
@[expose]
noncomputable def gFunbrfvb (A : Class) (B : Class) (F : Class) :
    Nominal.NPrf
      (.imp (synWa (synWfun F) (.classMem A (synCdm F)))
        (synWb (.classEq (synCfv F A) B) (synWbr A F B))) :=
  by
  have p0000 := @gFunfn F
  have p0001 := @gFnbrfvb (synCdm F) A B F
  have p0002 :=
    @gSylanb (synWfun F) (synWfn F (synCdm F)) (.classMem A (synCdm F))
      (synWb (.classEq (synCfv F A) B) (synWbr A F B)) p0000 p0001
  exact p0002

/-- Checked nominal proof certificate identified upstream as `g_funopfvb`. -/
@[expose]
noncomputable def gFunopfvb (A : Class) (B : Class) (F : Class) :
    Nominal.NPrf
      (.imp (synWa (synWfun F) (.classMem A (synCdm F)))
        (synWb (.classEq (synCfv F A) B) (.classMem (synCop A B) F))) :=
  by
  have p0000 := @gFunbrfvb A B F
  have p0001 := (Nominal.biimpRefl (synWbr A F B))
  have p0002 :=
    @gSyl6bb (synWa (synWfun F) (.classMem A (synCdm F))) (.classEq (synCfv F A) B)
      (synWbr A F B) (.classMem (synCop A B) F) p0000 p0001
  exact p0002

/-- Checked nominal proof certificate identified upstream as `g_funbrfv2b`. -/
@[expose]
noncomputable def gFunbrfv2b (A : Class) (B : Class) (F : Class) :
    Nominal.NPrf
      (.imp (synWfun F) (synWb (synWbr A F B)
          (synWa (.classMem A (synCdm F)) (.classEq (synCfv F A) B)))) :=
  by
  have p0000 := @gBreldm A B F
  have p0001 := @gA1i (.imp (synWbr A F B) (.classMem A (synCdm F))) (synWfun F) p0000
  have p0002 := @gPm471rd (synWfun F) (synWbr A F B) (.classMem A (synCdm F)) p0001
  have p0003 := @gFunbrfvb A B F
  have p0004 :=
    @gPm532da (synWfun F) (.classMem A (synCdm F)) (.classEq (synCfv F A) B)
      (synWbr A F B) p0003
  have p0005 :=
    @gBitr4d (synWfun F) (synWbr A F B)
      (synWa (.classMem A (synCdm F)) (synWbr A F B))
      (synWa (.classMem A (synCdm F)) (.classEq (synCfv F A) B)) p0002 p0004
  exact p0005

/-- Checked nominal proof certificate identified upstream as `g_fnrnfv`. -/
@[expose]
noncomputable def gFnrnfv (x : Var) (y : Var) (A : Class) (F : Class) (dv_A_x : x ∉ A.fv)
    (dv_A_y : y ∉ A.fv) (dv_F_x : x ∉ F.fv) (dv_F_y : y ∉ F.fv) (dv_x_y : x ≠ y) :
    Nominal.NPrf
      (.imp (synWfn F A) (.classEq (synCrn F)
          (.cab y (synWrex x A (.classEq (.cv y) (synCfv F (.cv x))))))) :=
  by
  have dv_cache_0001 : x ∉ (F).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_F_x, not_false_eq_true])
  have dv_cache_0002 : y ∉ (F).fv :=
    by
    clear dv_cache_0001
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_F_y, not_false_eq_true])
  have dv_cache_0003 : x ≠ y :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact (show x ≠ y from (by exact dv_x_y))
  have dv_cache_0004 : x ∉ ((synWfn F A)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wfn, Finset.mem_union,
          dv_F_x, dv_A_x, or_false, not_false_eq_true])
  have dv_cache_0005 : y ∉ ((synWfn F A)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wfn, Finset.mem_union,
          dv_F_y, dv_A_y, or_false, not_false_eq_true])
  have p0000 := @gDfrn3 x y F dv_cache_0001 dv_cache_0002 dv_cache_0003
  have p0001 := @gFnop A (.cv x) (.cv y) F
  have p0002 :=
    @gEx (synWfn F A) (.classMem (synCop (.cv x) (.cv y)) F) (.classMem (.cv x) A)
      p0001
  have p0003 :=
    @gPm471rd (synWfn F A) (.classMem (synCop (.cv x) (.cv y)) F)
      (.classMem (.cv x) A) p0002
  have p0004 := @gFnopfvb A (.cv x) (.cv y) F
  have p0005 :=
    @gPm532da (synWfn F A) (.classMem (.cv x) A) (.classEq (synCfv F (.cv x)) (.cv y))
      (.classMem (synCop (.cv x) (.cv y)) F) p0004
  have p0006 :=
    @gBitr4d (synWfn F A) (.classMem (synCop (.cv x) (.cv y)) F)
      (synWa (.classMem (.cv x) A) (.classMem (synCop (.cv x) (.cv y)) F))
      (synWa (.classMem (.cv x) A) (.classEq (synCfv F (.cv x)) (.cv y))) p0003 p0005
  have p0007 :=
    @gExbidv (synWfn F A) (.classMem (synCop (.cv x) (.cv y)) F)
      (synWa (.classMem (.cv x) A) (.classEq (synCfv F (.cv x)) (.cv y))) x
      dv_cache_0004 p0006
  have p0008 := @gEqcom (.cv y) (synCfv F (.cv x))
  have p0009 :=
    @gRexbii (.classEq (.cv y) (synCfv F (.cv x)))
      (.classEq (synCfv F (.cv x)) (.cv y)) x A p0008
  have p0010 := (Nominal.biimpRefl (synWrex x A (.classEq (synCfv F (.cv x)) (.cv y))))
  have p0011 :=
    @gBitri (synWrex x A (.classEq (.cv y) (synCfv F (.cv x))))
      (synWrex x A (.classEq (synCfv F (.cv x)) (.cv y)))
      (synWex x (synWa (.classMem (.cv x) A) (.classEq (synCfv F (.cv x)) (.cv y))))
      p0009 p0010
  have p0012 :=
    @gSyl6bbr (synWfn F A) (synWex x (.classMem (synCop (.cv x) (.cv y)) F))
      (synWex x (synWa (.classMem (.cv x) A) (.classEq (synCfv F (.cv x)) (.cv y))))
      (synWrex x A (.classEq (.cv y) (synCfv F (.cv x)))) p0007 p0011
  have p0013 :=
    @gAbbidv (synWfn F A) (synWex x (.classMem (synCop (.cv x) (.cv y)) F))
      (synWrex x A (.classEq (.cv y) (synCfv F (.cv x)))) y dv_cache_0005 p0012
  have p0014 :=
    @gSyl5eq (synWfn F A) (synCrn F)
      (.cab y (synWex x (.classMem (synCop (.cv x) (.cv y)) F)))
      (.cab y (synWrex x A (.classEq (.cv y) (synCfv F (.cv x))))) p0000 p0013
  exact p0014

/-- Checked nominal proof certificate identified upstream as `g_fvelrnb`. -/
@[expose]
noncomputable def gFvelrnb (x : Var) (A : Class) (B : Class) (F : Class)
    (dv_A_x : x ∉ A.fv) (dv_B_x : x ∉ B.fv) (dv_F_x : x ∉ F.fv) :
    Nominal.NPrf
      (.imp (synWfn F A) (synWb (.classMem B (synCrn F))
          (synWrex x A (.classEq (synCfv F (.cv x)) B)))) :=
  by
  let proofSupport : Finset Var := ({ x } : Finset Var) ∪ A.fv ∪ B.fv ∪ F.fv
  let y : Var := freshVar proofSupport 0
  have fresh_y : y ∉ proofSupport :=
    by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_y_ne_x : y ≠ x := by
    intro h
    exact
      fresh_y
        (Finset.mem_union_left _ (Finset.mem_union_left _
            (Finset.mem_union_left _ (Finset.mem_singleton.mpr h))))
  have fresh_x_ne_y : x ≠ y := Ne.symm fresh_y_ne_x
  have fresh_y_not_A : y ∉ A.fv := by
    intro h
    exact
      fresh_y
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))
  have fresh_y_not_B : y ∉ B.fv := by
    intro h
    exact fresh_y (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_y_not_F : y ∉ F.fv := by
    intro h
    exact fresh_y (Finset.mem_union_right _ (h))
  have dv_cache_0001 : x ∉ (A).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_A_x, not_false_eq_true])
  have dv_cache_0002 : y ∉ (A).fv :=
    by
    clear dv_cache_0001
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_y_not_A, not_false_eq_true])
  have dv_cache_0003 : x ∉ (F).fv :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_F_x, not_false_eq_true])
  have dv_cache_0004 : y ∉ (F).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_y_not_F, not_false_eq_true])
  have dv_cache_0005 : x ≠ y :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact (show x ≠ y from (by exact fresh_x_ne_y))
  have dv_cache_0006 : x ∉ ((Wff.classMem B (synCvv))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv, Finset.mem_union, dv_B_x,
          compact_fv_not_mem_empty, or_false, not_false_eq_true])
  have dv_cache_0007 : x ∉ ((Wff.classEq (.cv y) B)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, fresh_x_ne_y, dv_B_x, or_false, not_false_eq_true])
  have dv_cache_0008 : y ∉ (B).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_y_not_B, not_false_eq_true])
  have dv_cache_0009 : y ∉ ((synWrex x A (.classEq (synCfv F (.cv x)) B))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wrex,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase,
          Finset.mem_singleton, fresh_y_not_A, fresh_y_ne_x, fresh_y_not_F, fresh_y_not_B,
          or_false, and_false, not_false_eq_true])
  have p0000 :=
    @gFnrnfv x y A F dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
      dv_cache_0005
  have p0001 :=
    @gEleq2d (synWfn F A) (synCrn F)
      (.cab y (synWrex x A (.classEq (.cv y) (synCfv F (.cv x))))) B p0000
  have p0002 := @gFvex (.cv x) F
  have p0003 := @gEleq1 (synCfv F (.cv x)) B (synCvv)
  have p0004 :=
    @gMpbii (.classEq (synCfv F (.cv x)) B) (.classMem (synCfv F (.cv x)) (synCvv))
      (.classMem B (synCvv)) p0002 p0003
  have p0005 :=
    @gRexlimivw (.classEq (synCfv F (.cv x)) B) (.classMem B (synCvv)) x A
      dv_cache_0006 p0004
  have p0006 := @gEqeq1 (.cv y) B (synCfv F (.cv x))
  have p0007 := @gEqcom B (synCfv F (.cv x))
  have p0008 :=
    @gSyl6bb (.classEq (.cv y) B) (.classEq (.cv y) (synCfv F (.cv x)))
      (.classEq B (synCfv F (.cv x))) (.classEq (synCfv F (.cv x)) B) p0006 p0007
  have p0009 :=
    @gRexbidv (.classEq (.cv y) B) (.classEq (.cv y) (synCfv F (.cv x)))
      (.classEq (synCfv F (.cv x)) B) x A dv_cache_0007 p0008
  have p0010 :=
    @gElab3 (synWrex x A (.classEq (.cv y) (synCfv F (.cv x))))
      (synWrex x A (.classEq (synCfv F (.cv x)) B)) y B dv_cache_0008 dv_cache_0009
      p0005 p0009
  have p0011 :=
    @gSyl6bb (synWfn F A) (.classMem B (synCrn F))
      (.classMem B (.cab y (synWrex x A (.classEq (.cv y) (synCfv F (.cv x))))))
      (synWrex x A (.classEq (synCfv F (.cv x)) B)) p0001 p0010
  exact p0011

/-- Checked nominal proof certificate identified upstream as `g_dfimafn`. -/
@[expose]
noncomputable def gDfimafn (x : Var) (y : Var) (A : Class) (F : Class)
    (dv_A_x : x ∉ A.fv) (dv_A_y : y ∉ A.fv) (dv_F_x : x ∉ F.fv) (dv_F_y : y ∉ F.fv)
    (dv_x_y : x ≠ y) :
    Nominal.NPrf
      (.imp (synWa (synWfun F) (synWss A (synCdm F))) (.classEq (synCima F A)
          (.cab y (synWrex x A (.classEq (synCfv F (.cv x)) (.cv y)))))) :=
  by
  have dv_cache_0001 : x ∉ ((synWa (synWfun F) (synWss A (synCdm F)))).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wfun,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wss,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdm, Finset.mem_union, dv_F_x,
          dv_A_x, or_false, not_false_eq_true])
  have dv_cache_0002 : y ∉ ((synWa (synWfun F) (synWss A (synCdm F)))).fv :=
    by
    clear dv_cache_0001
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wfun,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wss,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdm, Finset.mem_union, dv_F_y,
          dv_A_y, or_false, not_false_eq_true])
  have dv_cache_0003 : y ∉ (F).fv :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_F_y, not_false_eq_true])
  have dv_cache_0004 : x ∉ (F).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_F_x, not_false_eq_true])
  have dv_cache_0005 : y ∉ (A).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_A_y, not_false_eq_true])
  have dv_cache_0006 : x ∉ (A).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_A_x, not_false_eq_true])
  have dv_cache_0007 : y ≠ x :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006
    exact (show y ≠ x from (by exact Ne.symm dv_x_y))
  have p0000 := @gSsel2 A (synCdm F) (.cv x)
  have p0001 := @gFunbrfvb (.cv x) (.cv y) F
  have p0002 :=
    @gSylan2 (synWa (synWss A (synCdm F)) (.classMem (.cv x) A)) (synWfun F)
      (.classMem (.cv x) (synCdm F))
      (synWb (.classEq (synCfv F (.cv x)) (.cv y)) (synWbr (.cv x) F (.cv y))) p0000
      p0001
  have p0003 :=
    @gAnassrs (synWfun F) (synWss A (synCdm F)) (.classMem (.cv x) A)
      (synWb (.classEq (synCfv F (.cv x)) (.cv y)) (synWbr (.cv x) F (.cv y))) p0002
  have p0004 :=
    @gRexbidva (synWa (synWfun F) (synWss A (synCdm F)))
      (.classEq (synCfv F (.cv x)) (.cv y)) (synWbr (.cv x) F (.cv y)) x A dv_cache_0001
      p0003
  have p0005 :=
    @gAbbidv (synWa (synWfun F) (synWss A (synCdm F)))
      (synWrex x A (.classEq (synCfv F (.cv x)) (.cv y)))
      (synWrex x A (synWbr (.cv x) F (.cv y))) y dv_cache_0002 p0004
  have p0006 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominalDfIma y x F A
      dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007
  have p0007 :=
    @gSyl6reqr (synWa (synWfun F) (synWss A (synCdm F)))
      (.cab y (synWrex x A (.classEq (synCfv F (.cv x)) (.cv y))))
      (.cab y (synWrex x A (synWbr (.cv x) F (.cv y)))) (synCima F A) p0005 p0006
  exact p0007

/-- Checked nominal proof certificate identified upstream as `g_funimass4`. -/
@[expose]
noncomputable def gFunimass4 (x : Var) (A : Class) (B : Class) (F : Class)
    (dv_A_x : x ∉ A.fv) (dv_B_x : x ∉ B.fv) (dv_F_x : x ∉ F.fv) :
    Nominal.NPrf
      (.imp (synWa (synWfun F) (synWss A (synCdm F))) (synWb (synWss (synCima F A) B)
          (synWral x A (.classMem (synCfv F (.cv x)) B)))) :=
  by
  let proofSupport : Finset Var := ({ x } : Finset Var) ∪ A.fv ∪ B.fv ∪ F.fv
  let y : Var := freshVar proofSupport 0
  have fresh_y : y ∉ proofSupport :=
    by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_y_ne_x : y ≠ x := by
    intro h
    exact
      fresh_y
        (Finset.mem_union_left _ (Finset.mem_union_left _
            (Finset.mem_union_left _ (Finset.mem_singleton.mpr h))))
  have fresh_x_ne_y : x ≠ y := Ne.symm fresh_y_ne_x
  have fresh_y_not_A : y ∉ A.fv := by
    intro h
    exact
      fresh_y
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))
  have fresh_y_not_B : y ∉ B.fv := by
    intro h
    exact fresh_y (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_y_not_F : y ∉ F.fv := by
    intro h
    exact fresh_y (Finset.mem_union_right _ (h))
  have dv_cache_0001 : y ∉ ((synCima F A)).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cima,
          Finset.mem_union, fresh_y_not_F, fresh_y_not_A, or_false, not_false_eq_true])
  have dv_cache_0002 : y ∉ (B).fv :=
    by
    clear dv_cache_0001
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_y_not_B, not_false_eq_true])
  have dv_cache_0003 : x ∉ ((synWa (synWfun F) (synWss A (synCdm F)))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wfun,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wss,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdm, Finset.mem_union, dv_F_x,
          dv_A_x, or_false, not_false_eq_true])
  have dv_cache_0004 : x ∉ ((Class.cv y)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_x_ne_y, not_false_eq_true])
  have dv_cache_0005 : x ∉ (F).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_F_x, not_false_eq_true])
  have dv_cache_0006 : x ∉ (A).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_A_x, not_false_eq_true])
  have dv_cache_0007 : x ∉ ((Wff.classMem (.cv y) B)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, fresh_x_ne_y, dv_B_x, or_false, not_false_eq_true])
  have dv_cache_0008 : y ∉ ((synWa (synWfun F) (synWss A (synCdm F)))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wfun,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wss,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdm, Finset.mem_union,
          fresh_y_not_F, fresh_y_not_A, or_false, not_false_eq_true])
  have dv_cache_0009 : y ∉ (A).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_y_not_A, not_false_eq_true])
  have dv_cache_0010 : x ≠ y :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009
    exact (show x ≠ y from (by exact fresh_x_ne_y))
  have dv_cache_0011 : y ∉ ((synCfv F (.cv x))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, fresh_y_ne_x, fresh_y_not_F, or_false, not_false_eq_true])
  have dv_cache_0012 : y ∉ ((Wff.classMem (synCfv F (.cv x)) B)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, fresh_y_ne_x, fresh_y_not_F, fresh_y_not_B, or_false,
          not_false_eq_true])
  have p0000 := @gDfss2 y (synCima F A) B dv_cache_0001 dv_cache_0002
  have p0001 := @gSsel2 A (synCdm F) (.cv x)
  have p0002 := @gEqcom (.cv y) (synCfv F (.cv x))
  have p0003 := @gFunbrfvb (.cv x) (.cv y) F
  have p0004 :=
    @gSyl5bb (.classEq (.cv y) (synCfv F (.cv x)))
      (.classEq (synCfv F (.cv x)) (.cv y))
      (synWa (synWfun F) (.classMem (.cv x) (synCdm F))) (synWbr (.cv x) F (.cv y))
      p0002 p0003
  have p0005 :=
    @gSylan2 (synWa (synWss A (synCdm F)) (.classMem (.cv x) A)) (synWfun F)
      (.classMem (.cv x) (synCdm F))
      (synWb (.classEq (.cv y) (synCfv F (.cv x))) (synWbr (.cv x) F (.cv y))) p0001
      p0004
  have p0006 :=
    @gAnassrs (synWfun F) (synWss A (synCdm F)) (.classMem (.cv x) A)
      (synWb (.classEq (.cv y) (synCfv F (.cv x))) (synWbr (.cv x) F (.cv y))) p0005
  have p0007 :=
    @gRexbidva (synWa (synWfun F) (synWss A (synCdm F)))
      (.classEq (.cv y) (synCfv F (.cv x))) (synWbr (.cv x) F (.cv y)) x A dv_cache_0003
      p0006
  have p0008 := @gElima x (.cv y) F A dv_cache_0004 dv_cache_0005 dv_cache_0006
  have p0009 :=
    @gSyl6rbbr (synWa (synWfun F) (synWss A (synCdm F)))
      (synWrex x A (.classEq (.cv y) (synCfv F (.cv x))))
      (synWrex x A (synWbr (.cv x) F (.cv y))) (.classMem (.cv y) (synCima F A)) p0007
      p0008
  have p0010 :=
    @gImbi1d (synWa (synWfun F) (synWss A (synCdm F)))
      (.classMem (.cv y) (synCima F A))
      (synWrex x A (.classEq (.cv y) (synCfv F (.cv x)))) (.classMem (.cv y) B) p0009
  have p0011 :=
    @gR1923v (.classEq (.cv y) (synCfv F (.cv x))) (.classMem (.cv y) B) x A
      dv_cache_0007
  have p0012 :=
    @gSyl6bbr (synWa (synWfun F) (synWss A (synCdm F)))
      (.imp (.classMem (.cv y) (synCima F A)) (.classMem (.cv y) B))
      (.imp (synWrex x A (.classEq (.cv y) (synCfv F (.cv x)))) (.classMem (.cv y) B))
      (synWral x A (.imp (.classEq (.cv y) (synCfv F (.cv x))) (.classMem (.cv y) B)))
      p0010 p0011
  have p0013 :=
    @gAlbidv (synWa (synWfun F) (synWss A (synCdm F)))
      (.imp (.classMem (.cv y) (synCima F A)) (.classMem (.cv y) B))
      (synWral x A (.imp (.classEq (.cv y) (synCfv F (.cv x))) (.classMem (.cv y) B))) y
      dv_cache_0008 p0012
  have p0014 :=
    @gRalcom4 (.imp (.classEq (.cv y) (synCfv F (.cv x))) (.classMem (.cv y) B)) x y A
      dv_cache_0009 dv_cache_0010
  have p0015 := @gFvex (.cv x) F
  have p0016 := @gEleq1 (.cv y) (synCfv F (.cv x)) B
  have p0017 :=
    @gCeqsalv (.classMem (.cv y) B) (.classMem (synCfv F (.cv x)) B) y
      (synCfv F (.cv x)) dv_cache_0011 dv_cache_0012 p0015 p0016
  have p0018 :=
    @gRalbii (.all y (.imp (.classEq (.cv y) (synCfv F (.cv x))) (.classMem (.cv y) B)))
      (.classMem (synCfv F (.cv x)) B) x A p0017
  have p0019 :=
    @gBitr3i
      (.all y (synWral x A
          (.imp (.classEq (.cv y) (synCfv F (.cv x))) (.classMem (.cv y) B))))
      (synWral x A
        (.all y (.imp (.classEq (.cv y) (synCfv F (.cv x))) (.classMem (.cv y) B))))
      (synWral x A (.classMem (synCfv F (.cv x)) B)) p0014 p0018
  have p0020 :=
    @gSyl6bb (synWa (synWfun F) (synWss A (synCdm F)))
      (.all y (.imp (.classMem (.cv y) (synCima F A)) (.classMem (.cv y) B)))
      (.all y (synWral x A
          (.imp (.classEq (.cv y) (synCfv F (.cv x))) (.classMem (.cv y) B))))
      (synWral x A (.classMem (synCfv F (.cv x)) B)) p0013 p0019
  have p0021 :=
    @gSyl5bb (synWss (synCima F A) B)
      (.all y (.imp (.classMem (.cv y) (synCima F A)) (.classMem (.cv y) B)))
      (synWa (synWfun F) (synWss A (synCdm F)))
      (synWral x A (.classMem (synCfv F (.cv x)) B)) p0000 p0020
  exact p0021

/-- Checked nominal proof certificate identified upstream as `g_fvelima`. -/
@[expose]
noncomputable def gFvelima (x : Var) (A : Class) (B : Class) (F : Class)
    (dv_A_x : x ∉ A.fv) (dv_B_x : x ∉ B.fv) (dv_F_x : x ∉ F.fv) :
    Nominal.NPrf
      (.imp (synWa (synWfun F) (.classMem A (synCima F B)))
        (synWrex x B (.classEq (synCfv F (.cv x)) A))) :=
  by
  have dv_cache_0001 : x ∉ (A).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_A_x, not_false_eq_true])
  have dv_cache_0002 : x ∉ (F).fv :=
    by
    clear dv_cache_0001
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_F_x, not_false_eq_true])
  have dv_cache_0003 : x ∉ (B).fv :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_B_x, not_false_eq_true])
  have dv_cache_0004 : x ∉ ((synWfun F)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wfun, dv_F_x,
          not_false_eq_true])
  have p0000 := @gElima x A F B dv_cache_0001 dv_cache_0002 dv_cache_0003
  have p0001 := @gFunbrfv (.cv x) A F
  have p0002 :=
    @gReximdv (synWfun F) (synWbr (.cv x) F A) (.classEq (synCfv F (.cv x)) A) x B
      dv_cache_0004 p0001
  have p0003 :=
    @gSyl5bi (.classMem A (synCima F B)) (synWrex x B (synWbr (.cv x) F A))
      (synWfun F) (synWrex x B (.classEq (synCfv F (.cv x)) A)) p0000 p0002
  have p0004 :=
    @gImp (synWfun F) (.classMem A (synCima F B))
      (synWrex x B (.classEq (synCfv F (.cv x)) A)) p0003
  exact p0004

/-- Checked nominal proof certificate identified upstream as `g_fvelimab`. -/
@[expose]
noncomputable def gFvelimab (x : Var) (A : Class) (B : Class) (C : Class) (F : Class)
    (dv_B_x : x ∉ B.fv) (dv_C_x : x ∉ C.fv) (dv_F_x : x ∉ F.fv) :
    Nominal.NPrf
      (.imp (synWa (synWfn F A) (synWss B A)) (synWb (.classMem C (synCima F B))
          (synWrex x B (.classEq (synCfv F (.cv x)) C)))) :=
  by
  let proofSupport : Finset Var := ({ x } : Finset Var) ∪ A.fv ∪ B.fv ∪ C.fv ∪ F.fv
  let y : Var := freshVar proofSupport 0
  have fresh_y : y ∉ proofSupport :=
    by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_y_ne_x : y ≠ x := by
    intro h
    exact
      fresh_y
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _
              (Finset.mem_union_left _ (Finset.mem_singleton.mpr h)))))
  have fresh_x_ne_y : x ≠ y := Ne.symm fresh_y_ne_x
  have fresh_y_not_A : y ∉ A.fv := by
    intro h
    exact
      fresh_y
        (Finset.mem_union_left _ (Finset.mem_union_left _
            (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))))
  have fresh_y_not_B : y ∉ B.fv := by
    intro h
    exact
      fresh_y
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))
  have fresh_y_not_C : y ∉ C.fv := by
    intro h
    exact fresh_y (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_y_not_F : y ∉ F.fv := by
    intro h
    exact fresh_y (Finset.mem_union_right _ (h))
  have dv_cache_0001 : x ∉ ((Wff.classMem C (synCvv))).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv, Finset.mem_union, dv_C_x,
          compact_fv_not_mem_empty, or_false, not_false_eq_true])
  have dv_cache_0002 : x ∉ ((Wff.classEq (.cv y) C)).fv :=
    by
    clear dv_cache_0001
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, fresh_x_ne_y, dv_C_x, or_false, not_false_eq_true])
  have dv_cache_0003 : x ∉ (B).fv :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_B_x, not_false_eq_true])
  have dv_cache_0004 : y ∉ (B).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_y_not_B, not_false_eq_true])
  have dv_cache_0005 : x ∉ (F).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_F_x, not_false_eq_true])
  have dv_cache_0006 : y ∉ (F).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_y_not_F, not_false_eq_true])
  have dv_cache_0007 : x ≠ y :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006
    exact (show x ≠ y from (by exact fresh_x_ne_y))
  have dv_cache_0008 : y ∉ (C).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_y_not_C, not_false_eq_true])
  have dv_cache_0009 :
    y ∉
      ((Wff.imp (synWa (synWfn F A) (synWss B A)) (synWb (.classMem C (synCima F B))
            (synWrex x B (.classEq (synCfv F (.cv x)) C))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wfn,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wss,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wb,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cima,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wrex,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase,
          Finset.mem_singleton, fresh_y_not_F, fresh_y_not_A, fresh_y_not_B,
          fresh_y_not_C, fresh_y_ne_x, or_false, and_false, not_false_eq_true])
  have p0000 := @gElex C (synCima F B)
  have p0001 :=
    @gAnim2i (.classMem C (synCima F B)) (.classMem C (synCvv))
      (synWa (synWfn F A) (synWss B A)) p0000
  have p0002 := @gFvex (.cv x) F
  have p0003 := @gEleq1 (synCfv F (.cv x)) C (synCvv)
  have p0004 :=
    @gMpbii (.classEq (synCfv F (.cv x)) C) (.classMem (synCfv F (.cv x)) (synCvv))
      (.classMem C (synCvv)) p0002 p0003
  have p0005 :=
    @gRexlimivw (.classEq (synCfv F (.cv x)) C) (.classMem C (synCvv)) x B
      dv_cache_0001 p0004
  have p0006 :=
    @gAnim2i (synWrex x B (.classEq (synCfv F (.cv x)) C)) (.classMem C (synCvv))
      (synWa (synWfn F A) (synWss B A)) p0005
  have p0007 := @gEleq1 (.cv y) C (synCima F B)
  have p0008 := @gEqeq2 (.cv y) C (synCfv F (.cv x))
  have p0009 :=
    @gRexbidv (.classEq (.cv y) C) (.classEq (synCfv F (.cv x)) (.cv y))
      (.classEq (synCfv F (.cv x)) C) x B dv_cache_0002 p0008
  have p0010 :=
    @gBibi12d (.classEq (.cv y) C) (.classMem (.cv y) (synCima F B))
      (.classMem C (synCima F B)) (synWrex x B (.classEq (synCfv F (.cv x)) (.cv y)))
      (synWrex x B (.classEq (synCfv F (.cv x)) C)) p0007 p0009
  have p0011 :=
    @gImbi2d (.classEq (.cv y) C)
      (synWb (.classMem (.cv y) (synCima F B))
        (synWrex x B (.classEq (synCfv F (.cv x)) (.cv y))))
      (synWb (.classMem C (synCima F B)) (synWrex x B (.classEq (synCfv F (.cv x)) C)))
      (synWa (synWfn F A) (synWss B A)) p0010
  have p0012 := @gFnfun A F
  have p0013 := @gAdantr (synWfn F A) (synWfun F) (synWss B A) p0012
  have p0014 := @gFndm A F
  have p0015 := @gSseq2d (synWfn F A) (synCdm F) A B p0014
  have p0016 := @gBiimpar (synWfn F A) (synWss B (synCdm F)) (synWss B A) p0015
  have p0017 :=
    @gDfimafn x y B F dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006
      dv_cache_0007
  have p0018 :=
    @gSyl2anc (synWa (synWfn F A) (synWss B A)) (synWfun F) (synWss B (synCdm F))
      (.classEq (synCima F B) (.cab y (synWrex x B (.classEq (synCfv F (.cv x)) (.cv y)))))
      p0013 p0016 p0017
  have p0019 :=
    @gEqabrd (synWa (synWfn F A) (synWss B A))
      (synWrex x B (.classEq (synCfv F (.cv x)) (.cv y))) y (synCima F B) p0018
  have p0020 :=
    @gVtoclg
      (.imp (synWa (synWfn F A) (synWss B A)) (synWb (.classMem (.cv y) (synCima F B))
          (synWrex x B (.classEq (synCfv F (.cv x)) (.cv y)))))
      (.imp (synWa (synWfn F A) (synWss B A)) (synWb (.classMem C (synCima F B))
          (synWrex x B (.classEq (synCfv F (.cv x)) C))))
      y C (synCvv) dv_cache_0008 dv_cache_0009 p0011 p0019
  have p0021 :=
    @gImpcom (.classMem C (synCvv)) (synWa (synWfn F A) (synWss B A))
      (synWb (.classMem C (synCima F B)) (synWrex x B (.classEq (synCfv F (.cv x)) C)))
      p0020
  have p0022 :=
    @gPm521nd (synWa (synWfn F A) (synWss B A)) (.classMem C (synCima F B))
      (synWrex x B (.classEq (synCfv F (.cv x)) C))
      (synWa (synWa (synWfn F A) (synWss B A)) (.classMem C (synCvv))) p0001 p0006
      p0021
  exact p0022

/-- Checked nominal proof certificate identified upstream as `g_fnsnfv`. -/
@[expose]
noncomputable def gFnsnfv (A : Class) (B : Class) (F : Class) :
    Nominal.NPrf
      (.imp (synWa (synWfn F A) (.classMem B A))
        (.classEq (synCsn (synCfv F B)) (synCima F (synCsn B)))) :=
  by
  let proofSupport : Finset Var := A.fv ∪ B.fv ∪ F.fv
  let y : Var := freshVar proofSupport 0
  have fresh_y : y ∉ proofSupport :=
    by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_y_not_A : y ∉ A.fv := by
    intro h
    exact fresh_y (Finset.mem_union_left _ (Finset.mem_union_left _ (h)))
  have fresh_y_not_B : y ∉ B.fv := by
    intro h
    exact fresh_y (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_y_not_F : y ∉ F.fv := by
    intro h
    exact fresh_y (Finset.mem_union_right _ (h))
  have dv_cache_0001 : y ∉ ((synWa (synWfn F A) (.classMem B A))).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wfn,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, Finset.mem_union, fresh_y_not_F,
          fresh_y_not_A, fresh_y_not_B, or_false, not_false_eq_true])
  have dv_cache_0002 : y ∉ ((synCfv F B)).fv :=
    by
    clear dv_cache_0001
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv, Finset.mem_union,
          fresh_y_not_B, fresh_y_not_F, or_false, not_false_eq_true])
  have dv_cache_0003 : y ∉ (B).fv :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_y_not_B, not_false_eq_true])
  have dv_cache_0004 : y ∉ (F).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_y_not_F, not_false_eq_true])
  have p0000 := @gEqcom (.cv y) (synCfv F B)
  have p0001 := @gFnbrfvb A B (.cv y) F
  have p0002 :=
    @gSyl5bb (.classEq (.cv y) (synCfv F B)) (.classEq (synCfv F B) (.cv y))
      (synWa (synWfn F A) (.classMem B A)) (synWbr B F (.cv y)) p0000 p0001
  have p0003 :=
    @gAbbidv (synWa (synWfn F A) (.classMem B A)) (.classEq (.cv y) (synCfv F B))
      (synWbr B F (.cv y)) y dv_cache_0001 p0002
  have p0004 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominalDfSn y (synCfv F B)
      dv_cache_0002
  have p0005 := @gImasn y B F dv_cache_0003 dv_cache_0004
  have p0006 :=
    @gN3eqtr4g (synWa (synWfn F A) (.classMem B A))
      (.cab y (.classEq (.cv y) (synCfv F B))) (.cab y (synWbr B F (.cv y)))
      (synCsn (synCfv F B)) (synCima F (synCsn B)) p0003 p0004 p0005
  exact p0006

/-- Checked nominal proof certificate identified upstream as `g_funfv`. -/
@[expose]
noncomputable def gFunfv (A : Class) (F : Class) :
    Nominal.NPrf
      (.imp (synWfun F) (.classEq (synCfv F A) (synCuni (synCima F (synCsn A))))) :=
  by
  have p0000 := @gFvex A F
  have p0001 := @gUnisn (synCfv F A) p0000
  have p0002 := @gEqid (synCdm F)
  have p0003 := (Nominal.biimpRefl (synWfn F (synCdm F)))
  have p0004 :=
    @gMpbiran2 (synWfn F (synCdm F)) (synWfun F) (.classEq (synCdm F) (synCdm F))
      p0002 p0003
  have p0005 := @gFnsnfv (synCdm F) A F
  have p0006 :=
    @gSylanbr (synWfun F) (synWfn F (synCdm F)) (.classMem A (synCdm F))
      (.classEq (synCsn (synCfv F A)) (synCima F (synCsn A))) p0004 p0005
  have p0007 :=
    @gUnieqd (synWa (synWfun F) (.classMem A (synCdm F))) (synCsn (synCfv F A))
      (synCima F (synCsn A)) p0006
  have p0008 :=
    @gSyl5eqr (synWa (synWfun F) (.classMem A (synCdm F))) (synCfv F A)
      (synCuni (synCsn (synCfv F A))) (synCuni (synCima F (synCsn A))) p0001 p0007
  have p0009 :=
    @gEx (synWfun F) (.classMem A (synCdm F))
      (.classEq (synCfv F A) (synCuni (synCima F (synCsn A)))) p0008
  have p0010 := @gNdmfv A F
  have p0011 := @gNdmima A F
  have p0012 :=
    @gUnieqd (.neg (.classMem A (synCdm F))) (synCima F (synCsn A)) (synC0) p0011
  have p0013 := @gUni0
  have p0014 :=
    @gSyl6eq (.neg (.classMem A (synCdm F))) (synCuni (synCima F (synCsn A)))
      (synCuni (synC0)) (synC0) p0012 p0013
  have p0015 :=
    @gEqtr4d (.neg (.classMem A (synCdm F))) (synCfv F A) (synC0)
      (synCuni (synCima F (synCsn A))) p0010 p0014
  have p0016 :=
    @gPm261d1 (synWfun F) (.classMem A (synCdm F))
      (.classEq (synCfv F A) (synCuni (synCima F (synCsn A)))) p0009 p0015
  exact p0016

/-- Checked nominal proof certificate identified upstream as `g_fvun`. -/
@[expose]
noncomputable def gFvun (A : Class) (F : Class) (G : Class) :
    Nominal.NPrf
      (.imp (synWa (synWa (synWfun F) (synWfun G))
          (.classEq (synCin (synCdm F) (synCdm G)) (synC0)))
        (.classEq (synCfv (synCun F G) A) (synCun (synCfv F A) (synCfv G A)))) :=
  by
  have p0000 := @gFunun F G
  have p0001 := @gFunfv A (synCun F G)
  have p0002 :=
    @gSyl
      (synWa (synWa (synWfun F) (synWfun G))
        (.classEq (synCin (synCdm F) (synCdm G)) (synC0)))
      (synWfun (synCun F G))
      (.classEq (synCfv (synCun F G) A) (synCuni (synCima (synCun F G) (synCsn A))))
      p0000 p0001
  have p0003 := @gImaundir F G (synCsn A)
  have p0004 :=
    @gA1i
      (.classEq (synCima (synCun F G) (synCsn A))
        (synCun (synCima F (synCsn A)) (synCima G (synCsn A))))
      (synWa (synWa (synWfun F) (synWfun G))
        (.classEq (synCin (synCdm F) (synCdm G)) (synC0)))
      p0003
  have p0005 :=
    @gUnieqd
      (synWa (synWa (synWfun F) (synWfun G))
        (.classEq (synCin (synCdm F) (synCdm G)) (synC0)))
      (synCima (synCun F G) (synCsn A))
      (synCun (synCima F (synCsn A)) (synCima G (synCsn A))) p0004
  have p0006 := @gUniun (synCima F (synCsn A)) (synCima G (synCsn A))
  have p0007 := @gFunfv A F
  have p0008 :=
    @gEqcomd (synWfun F) (synCfv F A) (synCuni (synCima F (synCsn A))) p0007
  have p0009 := @gFunfv A G
  have p0010 :=
    @gEqcomd (synWfun G) (synCfv G A) (synCuni (synCima G (synCsn A))) p0009
  have p0011 :=
    @gAnim12i (synWfun F) (.classEq (synCuni (synCima F (synCsn A))) (synCfv F A))
      (synWfun G) (.classEq (synCuni (synCima G (synCsn A))) (synCfv G A)) p0008
      p0010
  have p0012 :=
    @gAdantr (synWa (synWfun F) (synWfun G))
      (synWa (.classEq (synCuni (synCima F (synCsn A))) (synCfv F A))
        (.classEq (synCuni (synCima G (synCsn A))) (synCfv G A)))
      (.classEq (synCin (synCdm F) (synCdm G)) (synC0)) p0011
  have p0013 :=
    @gUneq12 (synCuni (synCima F (synCsn A))) (synCfv F A)
      (synCuni (synCima G (synCsn A))) (synCfv G A)
  have p0014 :=
    @gSyl
      (synWa (synWa (synWfun F) (synWfun G))
        (.classEq (synCin (synCdm F) (synCdm G)) (synC0)))
      (synWa (.classEq (synCuni (synCima F (synCsn A))) (synCfv F A))
        (.classEq (synCuni (synCima G (synCsn A))) (synCfv G A)))
      (.classEq
        (synCun (synCuni (synCima F (synCsn A))) (synCuni (synCima G (synCsn A))))
        (synCun (synCfv F A) (synCfv G A)))
      p0012 p0013
  have p0015 :=
    @gSyl5eq
      (synWa (synWa (synWfun F) (synWfun G))
        (.classEq (synCin (synCdm F) (synCdm G)) (synC0)))
      (synCuni (synCun (synCima F (synCsn A)) (synCima G (synCsn A))))
      (synCun (synCuni (synCima F (synCsn A))) (synCuni (synCima G (synCsn A))))
      (synCun (synCfv F A) (synCfv G A)) p0006 p0014
  have p0016 :=
    @gN3eqtrd
      (synWa (synWa (synWfun F) (synWfun G))
        (.classEq (synCin (synCdm F) (synCdm G)) (synC0)))
      (synCfv (synCun F G) A) (synCuni (synCima (synCun F G) (synCsn A)))
      (synCuni (synCun (synCima F (synCsn A)) (synCima G (synCsn A))))
      (synCun (synCfv F A) (synCfv G A)) p0002 p0005 p0015
  exact p0016


end NFChoice.DirectNominalPrf.WPPReplay

end

/-! Certificates from `NominalWPPReplayChunk012ACompact002Part004`. -/


section

namespace NFChoice.DirectNominalPrf.WPPReplay

open scoped Fol
open NFChoice.Foundation
open NFChoice.SemanticCore
open NFChoice.ReplaySupport
open NFChoice.Compiler.CompactSourceSyntax

/-- Checked nominal proof certificate identified upstream as `g_fvun1`. -/
@[expose]
noncomputable def gFvun1 (A : Class) (B : Class) (F : Class) (G : Class) (X : Class) :
    Nominal.NPrf
      (.imp (synW3a (synWfn F A) (synWfn G B)
          (synWa (.classEq (synCin A B) (synC0)) (.classMem X A)))
        (.classEq (synCfv (synCun F G) X) (synCfv F X))) :=
  by
  let proofSupport : Finset Var := A.fv ∪ B.fv ∪ F.fv ∪ G.fv ∪ X.fv
  let x : Var := freshVar proofSupport 0
  have fresh_x : x ∉ proofSupport :=
    by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_x_not_A : x ∉ A.fv := by
    intro h
    exact
      fresh_x
        (Finset.mem_union_left _ (Finset.mem_union_left _
            (Finset.mem_union_left _ (Finset.mem_union_left _ (h)))))
  have fresh_x_not_B : x ∉ B.fv := by
    intro h
    exact
      fresh_x
        (Finset.mem_union_left _ (Finset.mem_union_left _
            (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))))
  have fresh_x_not_X : x ∉ X.fv := by
    intro h
    exact fresh_x (Finset.mem_union_right _ (h))
  have dv_cache_0001 : x ∉ (A).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_x_not_A, not_false_eq_true])
  have dv_cache_0002 : x ∉ (B).fv :=
    by
    clear dv_cache_0001
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_x_not_B, not_false_eq_true])
  have dv_cache_0003 : x ∉ (X).fv :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_x_not_X, not_false_eq_true])
  have dv_cache_0004 : x ∉ ((Wff.neg (.classMem X B))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_neg,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, Finset.mem_union, fresh_x_not_X,
          fresh_x_not_B, or_false, not_false_eq_true])
  have p0000 := @gFnfun A F
  have p0001 :=
    @gN3ad2ant1 (synWfn F A) (synWfn G B) (synWfun F)
      (synWa (.classEq (synCin A B) (synC0)) (.classMem X A)) p0000
  have p0002 := @gFnfun B G
  have p0003 :=
    @gN3ad2ant2 (synWfn G B) (synWfn F A) (synWfun G)
      (synWa (.classEq (synCin A B) (synC0)) (.classMem X A)) p0002
  have p0004 := @gFndm A F
  have p0005 := @gFndm B G
  have p0006 := @gIneq12 (synCdm F) A (synCdm G) B
  have p0007 :=
    @gSyl2an (synWfn F A) (.classEq (synCdm F) A) (.classEq (synCdm G) B)
      (.classEq (synCin (synCdm F) (synCdm G)) (synCin A B)) (synWfn G B) p0004 p0005
      p0006
  have p0008 :=
    @gEqeq1d (synWa (synWfn F A) (synWfn G B)) (synCin (synCdm F) (synCdm G))
      (synCin A B) (synC0) p0007
  have p0009 :=
    @gBiimprd (synWa (synWfn F A) (synWfn G B))
      (.classEq (synCin (synCdm F) (synCdm G)) (synC0))
      (.classEq (synCin A B) (synC0)) p0008
  have p0010 :=
    @gAdantrd (synWa (synWfn F A) (synWfn G B)) (.classEq (synCin A B) (synC0))
      (.classEq (synCin (synCdm F) (synCdm G)) (synC0)) (.classMem X A) p0009
  have p0011 :=
    @gN3impia (synWfn F A) (synWfn G B)
      (synWa (.classEq (synCin A B) (synC0)) (.classMem X A))
      (.classEq (synCin (synCdm F) (synCdm G)) (synC0)) p0010
  have p0012 := @gFvun X F G
  have p0013 :=
    @gSyl21anc
      (synW3a (synWfn F A) (synWfn G B)
        (synWa (.classEq (synCin A B) (synC0)) (.classMem X A)))
      (synWfun F) (synWfun G) (.classEq (synCin (synCdm F) (synCdm G)) (synC0))
      (.classEq (synCfv (synCun F G) X) (synCun (synCfv F X) (synCfv G X))) p0001
      p0003 p0011 p0012
  have p0014 := @gDisj x A B dv_cache_0001 dv_cache_0002
  have p0015 := @gEleq1 (.cv x) X B
  have p0016 := @gNotbid (.classEq (.cv x) X) (.classMem (.cv x) B) (.classMem X B) p0015
  have p0017 :=
    @gRspccv (.neg (.classMem (.cv x) B)) (.neg (.classMem X B)) x X A dv_cache_0003
      dv_cache_0001 dv_cache_0004 p0016
  have p0018 :=
    @gSylbi (.classEq (synCin A B) (synC0)) (synWral x A (.neg (.classMem (.cv x) B)))
      (.imp (.classMem X A) (.neg (.classMem X B))) p0014 p0017
  have p0019 :=
    @gImp (.classEq (synCin A B) (synC0)) (.classMem X A) (.neg (.classMem X B)) p0018
  have p0020 :=
    @gN3ad2ant3 (synWa (.classEq (synCin A B) (synC0)) (.classMem X A)) (synWfn F A)
      (.neg (.classMem X B)) (synWfn G B) p0019
  have p0021 :=
    @gN3ad2ant2 (synWfn G B) (synWfn F A) (.classEq (synCdm G) B)
      (synWa (.classEq (synCin A B) (synC0)) (.classMem X A)) p0005
  have p0022 :=
    @gEleq2d
      (synW3a (synWfn F A) (synWfn G B)
        (synWa (.classEq (synCin A B) (synC0)) (.classMem X A)))
      (synCdm G) B X p0021
  have p0023 :=
    @gMtbird
      (synW3a (synWfn F A) (synWfn G B)
        (synWa (.classEq (synCin A B) (synC0)) (.classMem X A)))
      (.classMem X (synCdm G)) (.classMem X B) p0020 p0022
  have p0024 := @gNdmfv X G
  have p0025 :=
    @gSyl
      (synW3a (synWfn F A) (synWfn G B)
        (synWa (.classEq (synCin A B) (synC0)) (.classMem X A)))
      (.neg (.classMem X (synCdm G))) (.classEq (synCfv G X) (synC0)) p0023 p0024
  have p0026 :=
    @gUneq2d
      (synW3a (synWfn F A) (synWfn G B)
        (synWa (.classEq (synCin A B) (synC0)) (.classMem X A)))
      (synCfv G X) (synC0) (synCfv F X) p0025
  have p0027 :=
    @gEqtrd
      (synW3a (synWfn F A) (synWfn G B)
        (synWa (.classEq (synCin A B) (synC0)) (.classMem X A)))
      (synCfv (synCun F G) X) (synCun (synCfv F X) (synCfv G X))
      (synCun (synCfv F X) (synC0)) p0013 p0026
  have p0028 := @gUn0 (synCfv F X)
  have p0029 :=
    @gSyl6eq
      (synW3a (synWfn F A) (synWfn G B)
        (synWa (.classEq (synCin A B) (synC0)) (.classMem X A)))
      (synCfv (synCun F G) X) (synCun (synCfv F X) (synC0)) (synCfv F X) p0027 p0028
  exact p0029

/-- Checked nominal proof certificate identified upstream as `g_fvun2`. -/
@[expose]
noncomputable def gFvun2 (A : Class) (B : Class) (F : Class) (G : Class) (X : Class) :
    Nominal.NPrf
      (.imp (synW3a (synWfn F A) (synWfn G B)
          (synWa (.classEq (synCin A B) (synC0)) (.classMem X B)))
        (.classEq (synCfv (synCun F G) X) (synCfv G X))) :=
  by
  have p0000 := @gUncom F G
  have p0001 := @gFveq1i X (synCun F G) (synCun G F) p0000
  have p0002 := @gIncom A B
  have p0003 := @gEqeq1i (synCin A B) (synCin B A) (synC0) p0002
  have p0004 :=
    @gAnbi1i (.classEq (synCin A B) (synC0)) (.classEq (synCin B A) (synC0))
      (.classMem X B) p0003
  have p0005 := @gFvun1 B A G F X
  have p0006 :=
    @gSyl3an3b (synWa (.classEq (synCin A B) (synC0)) (.classMem X B)) (synWfn G B)
      (synWfn F A) (synWa (.classEq (synCin B A) (synC0)) (.classMem X B))
      (.classEq (synCfv (synCun G F) X) (synCfv G X)) p0004 p0005
  have p0007 :=
    @gN3com12 (synWfn G B) (synWfn F A)
      (synWa (.classEq (synCin A B) (synC0)) (.classMem X B))
      (.classEq (synCfv (synCun G F) X) (synCfv G X)) p0006
  have p0008 :=
    @gSyl5eq
      (synW3a (synWfn F A) (synWfn G B)
        (synWa (.classEq (synCin A B) (synC0)) (.classMem X B)))
      (synCfv (synCun F G) X) (synCfv (synCun G F) X) (synCfv G X) p0001 p0007
  exact p0008

/-- Checked nominal proof certificate identified upstream as `g_dmfco`. -/
@[expose]
noncomputable def gDmfco (A : Class) (F : Class) (G : Class) :
    Nominal.NPrf
      (.imp (synWa (synWfun G) (.classMem A (synCdm G)))
        (synWb (.classMem A (synCdm (synCcom F G)))
          (.classMem (synCfv G A) (synCdm F)))) :=
  by
  let proofSupport : Finset Var := A.fv ∪ F.fv ∪ G.fv
  let y : Var := freshVar proofSupport 0
  let z : Var := freshVar proofSupport 1
  have fresh_y : y ∉ proofSupport :=
    by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_y_not_A : y ∉ A.fv := by
    intro h
    exact fresh_y (Finset.mem_union_left _ (Finset.mem_union_left _ (h)))
  have fresh_y_not_F : y ∉ F.fv := by
    intro h
    exact fresh_y (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_y_not_G : y ∉ G.fv := by
    intro h
    exact fresh_y (Finset.mem_union_right _ (h))
  have fresh_z : z ∉ proofSupport :=
    by
    change freshVar proofSupport 1 ∉ proofSupport
    exact freshVar_not_mem proofSupport 1
  have fresh_z_not_A : z ∉ A.fv := by
    intro h
    exact fresh_z (Finset.mem_union_left _ (Finset.mem_union_left _ (h)))
  have fresh_z_not_F : z ∉ F.fv := by
    intro h
    exact fresh_z (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_z_not_G : z ∉ G.fv := by
    intro h
    exact fresh_z (Finset.mem_union_right _ (h))
  have fresh_y_ne_z : y ≠ z :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have dv_cache_0001 : y ∉ ((synCfv G A)).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv, Finset.mem_union,
          fresh_y_not_A, fresh_y_not_G, or_false, not_false_eq_true])
  have dv_cache_0002 : y ∉ ((synWbr (synCfv G A) F (.cv z))).fv :=
    by
    clear dv_cache_0001
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, fresh_y_not_A, fresh_y_not_G, fresh_y_ne_z, fresh_y_not_F,
          or_false, not_false_eq_true])
  have dv_cache_0003 : y ∉ ((synWa (synWfun G) (.classMem A (synCdm G)))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wfun,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdm, Finset.mem_union,
          fresh_y_not_G, fresh_y_not_A, or_false, not_false_eq_true])
  have dv_cache_0004 : z ∉ ((synWa (synWfun G) (.classMem A (synCdm G)))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact
      (by
        have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wfun,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdm, Finset.mem_union,
          fresh_z_not_G, fresh_z_not_A, or_false, not_false_eq_true])
  have dv_cache_0005 : z ∉ (A).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact
      (by
        have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_z_not_A, not_false_eq_true])
  have dv_cache_0006 : z ∉ ((synCcom F G)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact
      (by
        have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccom,
          Finset.mem_union, fresh_z_not_F, fresh_z_not_G, or_false, not_false_eq_true])
  have dv_cache_0007 : y ∉ (A).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_y_not_A, not_false_eq_true])
  have dv_cache_0008 : y ∉ ((Class.cv z)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_y_ne_z, not_false_eq_true])
  have dv_cache_0009 : y ∉ (F).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_y_not_F, not_false_eq_true])
  have dv_cache_0010 : y ∉ (G).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_y_not_G, not_false_eq_true])
  have dv_cache_0011 : z ∉ ((synCfv G A)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010
    exact
      (by
        have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv, Finset.mem_union,
          fresh_z_not_A, fresh_z_not_G, or_false, not_false_eq_true])
  have dv_cache_0012 : z ∉ (F).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
    exact
      (by
        have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_z_not_F, not_false_eq_true])
  have p0000 := @gFvex A G
  have p0001 := @gBreq1 (.cv y) (synCfv G A) (.cv z) F
  have p0002 :=
    @gCeqsexv (synWbr (.cv y) F (.cv z)) (synWbr (synCfv G A) F (.cv z)) y
      (synCfv G A) dv_cache_0001 dv_cache_0002 p0000 p0001
  have p0003 := @gEqcom (.cv y) (synCfv G A)
  have p0004 := @gFunbrfvb A (.cv y) G
  have p0005 :=
    @gSyl5bb (.classEq (.cv y) (synCfv G A)) (.classEq (synCfv G A) (.cv y))
      (synWa (synWfun G) (.classMem A (synCdm G))) (synWbr A G (.cv y)) p0003 p0004
  have p0006 :=
    @gAnbi1d (synWa (synWfun G) (.classMem A (synCdm G)))
      (.classEq (.cv y) (synCfv G A)) (synWbr A G (.cv y)) (synWbr (.cv y) F (.cv z))
      p0005
  have p0007 :=
    @gExbidv (synWa (synWfun G) (.classMem A (synCdm G)))
      (synWa (.classEq (.cv y) (synCfv G A)) (synWbr (.cv y) F (.cv z)))
      (synWa (synWbr A G (.cv y)) (synWbr (.cv y) F (.cv z))) y dv_cache_0003 p0006
  have p0008 :=
    @gSyl5rbbr (synWbr (synCfv G A) F (.cv z))
      (synWex y (synWa (.classEq (.cv y) (synCfv G A)) (synWbr (.cv y) F (.cv z))))
      (synWa (synWfun G) (.classMem A (synCdm G)))
      (synWex y (synWa (synWbr A G (.cv y)) (synWbr (.cv y) F (.cv z)))) p0002 p0007
  have p0009 :=
    @gExbidv (synWa (synWfun G) (.classMem A (synCdm G)))
      (synWex y (synWa (synWbr A G (.cv y)) (synWbr (.cv y) F (.cv z))))
      (synWbr (synCfv G A) F (.cv z)) z dv_cache_0004 p0008
  have p0010 := @gEldm z A (synCcom F G) dv_cache_0005 dv_cache_0006
  have p0011 :=
    @gBrco y A (.cv z) F G dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010
  have p0012 :=
    @gExbii (synWbr A (synCcom F G) (.cv z))
      (synWex y (synWa (synWbr A G (.cv y)) (synWbr (.cv y) F (.cv z)))) z p0011
  have p0013 :=
    @gBitri (.classMem A (synCdm (synCcom F G)))
      (synWex z (synWbr A (synCcom F G) (.cv z)))
      (synWex z (synWex y (synWa (synWbr A G (.cv y)) (synWbr (.cv y) F (.cv z)))))
      p0010 p0012
  have p0014 := @gEldm z (synCfv G A) F dv_cache_0011 dv_cache_0012
  have p0015 :=
    @gN3bitr4g (synWa (synWfun G) (.classMem A (synCdm G)))
      (synWex z (synWex y (synWa (synWbr A G (.cv y)) (synWbr (.cv y) F (.cv z)))))
      (synWex z (synWbr (synCfv G A) F (.cv z))) (.classMem A (synCdm (synCcom F G)))
      (.classMem (synCfv G A) (synCdm F)) p0009 p0013 p0014
  exact p0015

/-- Checked nominal proof certificate identified upstream as `g_fvco2`. -/
@[expose]
noncomputable def gFvco2 (A : Class) (C : Class) (F : Class) (G : Class) :
    Nominal.NPrf
      (.imp (synWa (synWfn G A) (.classMem C A))
        (.classEq (synCfv (synCcom F G) C) (synCfv F (synCfv G C)))) :=
  by
  let proofSupport : Finset Var := A.fv ∪ C.fv ∪ F.fv ∪ G.fv
  let y : Var := freshVar proofSupport 0
  let z : Var := freshVar proofSupport 1
  have fresh_y : y ∉ proofSupport :=
    by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_y_not_A : y ∉ A.fv := by
    intro h
    exact
      fresh_y
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (h))))
  have fresh_y_not_C : y ∉ C.fv := by
    intro h
    exact
      fresh_y
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))
  have fresh_y_not_F : y ∉ F.fv := by
    intro h
    exact fresh_y (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_y_not_G : y ∉ G.fv := by
    intro h
    exact fresh_y (Finset.mem_union_right _ (h))
  have fresh_z : z ∉ proofSupport :=
    by
    change freshVar proofSupport 1 ∉ proofSupport
    exact freshVar_not_mem proofSupport 1
  have fresh_z_not_C : z ∉ C.fv := by
    intro h
    exact
      fresh_z
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))
  have fresh_z_not_F : z ∉ F.fv := by
    intro h
    exact fresh_z (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_z_not_G : z ∉ G.fv := by
    intro h
    exact fresh_z (Finset.mem_union_right _ (h))
  have fresh_y_ne_z : y ≠ z :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have fresh_z_ne_y : z ≠ y := Ne.symm fresh_y_ne_z
  have dv_cache_0001 : y ∉ ((synWa (synWfn G A) (.classMem C A))).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wfn,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, Finset.mem_union, fresh_y_not_G,
          fresh_y_not_A, fresh_y_not_C, or_false, not_false_eq_true])
  have dv_cache_0002 : y ∉ ((synWbr C (synCcom F G) (.cv z))).fv :=
    by
    clear dv_cache_0001
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccom,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, fresh_y_not_C, fresh_y_ne_z, fresh_y_not_F, fresh_y_not_G,
          or_false, not_false_eq_true])
  have dv_cache_0003 : z ≠ y :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact (show z ≠ y from (by exact fresh_z_ne_y))
  have dv_cache_0004 : z ∉ (C).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact
      (by
        have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_z_not_C, not_false_eq_true])
  have dv_cache_0005 : z ∉ ((synCcom F G)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact
      (by
        have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccom,
          Finset.mem_union, fresh_z_not_F, fresh_z_not_G, or_false, not_false_eq_true])
  have dv_cache_0006 : y ∉ ((synWbr (synCfv G C) F (.cv z))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, fresh_y_not_C, fresh_y_not_G, fresh_y_ne_z, fresh_y_not_F,
          or_false, not_false_eq_true])
  have dv_cache_0007 : z ∉ ((synCfv G C)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006
    exact
      (by
        have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv, Finset.mem_union,
          fresh_z_not_C, fresh_z_not_G, or_false, not_false_eq_true])
  have dv_cache_0008 : z ∉ (F).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007
    exact
      (by
        have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_z_not_F, not_false_eq_true])
  have p0000 := @gFnsnfv A C G
  have p0001 :=
    @gImaeq2d (synWa (synWfn G A) (.classMem C A)) (synCsn (synCfv G C))
      (synCima G (synCsn C)) F p0000
  have p0002 := @gImaco F G (synCsn C)
  have p0003 :=
    @gSyl6reqr (synWa (synWfn G A) (.classMem C A))
      (synCima F (synCsn (synCfv G C))) (synCima F (synCima G (synCsn C)))
      (synCima (synCcom F G) (synCsn C)) p0001 p0002
  have p0004 :=
    @gEqeq1d (synWa (synWfn G A) (.classMem C A)) (synCima (synCcom F G) (synCsn C))
      (synCima F (synCsn (synCfv G C))) (synCsn (.cv y)) p0003
  have p0005 :=
    @gAbbidv (synWa (synWfn G A) (.classMem C A))
      (.classEq (synCima (synCcom F G) (synCsn C)) (synCsn (.cv y)))
      (.classEq (synCima F (synCsn (synCfv G C))) (synCsn (.cv y))) y dv_cache_0001
      p0004
  have p0006 :=
    @gUnieqd (synWa (synWfn G A) (.classMem C A))
      (.cab y (.classEq (synCima (synCcom F G) (synCsn C)) (synCsn (.cv y))))
      (.cab y (.classEq (synCima F (synCsn (synCfv G C))) (synCsn (.cv y)))) p0005
  have p0007 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominalDfIota
      (synWbr C (synCcom F G) (.cv z)) z y dv_cache_0002 dv_cache_0003
  have p0008 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominalDfFv z C
      (synCcom F G) dv_cache_0004 dv_cache_0005
  have p0009 := @gImasn z C (synCcom F G) dv_cache_0004 dv_cache_0005
  have p0010 :=
    @gEqeq1i (synCima (synCcom F G) (synCsn C))
      (.cab z (synWbr C (synCcom F G) (.cv z))) (synCsn (.cv y)) p0009
  have p0011 :=
    @gAbbii (.classEq (synCima (synCcom F G) (synCsn C)) (synCsn (.cv y)))
      (.classEq (.cab z (synWbr C (synCcom F G) (.cv z))) (synCsn (.cv y))) y p0010
  have p0012 :=
    @gUnieqi (.cab y (.classEq (synCima (synCcom F G) (synCsn C)) (synCsn (.cv y))))
      (.cab y (.classEq (.cab z (synWbr C (synCcom F G) (.cv z))) (synCsn (.cv y))))
      p0011
  have p0013 :=
    @gN3eqtr4i (synCio z (synWbr C (synCcom F G) (.cv z)))
      (synCuni
        (.cab y (.classEq (.cab z (synWbr C (synCcom F G) (.cv z))) (synCsn (.cv y)))))
      (synCfv (synCcom F G) C)
      (synCuni (.cab y (.classEq (synCima (synCcom F G) (synCsn C)) (synCsn (.cv y)))))
      p0007 p0008 p0012
  have p0014 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominalDfIota
      (synWbr (synCfv G C) F (.cv z)) z y dv_cache_0006 dv_cache_0003
  have p0015 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominalDfFv z (synCfv G C) F
      dv_cache_0007 dv_cache_0008
  have p0016 := @gImasn z (synCfv G C) F dv_cache_0007 dv_cache_0008
  have p0017 :=
    @gEqeq1i (synCima F (synCsn (synCfv G C)))
      (.cab z (synWbr (synCfv G C) F (.cv z))) (synCsn (.cv y)) p0016
  have p0018 :=
    @gAbbii (.classEq (synCima F (synCsn (synCfv G C))) (synCsn (.cv y)))
      (.classEq (.cab z (synWbr (synCfv G C) F (.cv z))) (synCsn (.cv y))) y p0017
  have p0019 :=
    @gUnieqi (.cab y (.classEq (synCima F (synCsn (synCfv G C))) (synCsn (.cv y))))
      (.cab y (.classEq (.cab z (synWbr (synCfv G C) F (.cv z))) (synCsn (.cv y))))
      p0018
  have p0020 :=
    @gN3eqtr4i (synCio z (synWbr (synCfv G C) F (.cv z)))
      (synCuni
        (.cab y (.classEq (.cab z (synWbr (synCfv G C) F (.cv z))) (synCsn (.cv y)))))
      (synCfv F (synCfv G C))
      (synCuni (.cab y (.classEq (synCima F (synCsn (synCfv G C))) (synCsn (.cv y)))))
      p0014 p0015 p0019
  have p0021 :=
    @gN3eqtr4g (synWa (synWfn G A) (.classMem C A))
      (synCuni (.cab y (.classEq (synCima (synCcom F G) (synCsn C)) (synCsn (.cv y)))))
      (synCuni (.cab y (.classEq (synCima F (synCsn (synCfv G C))) (synCsn (.cv y)))))
      (synCfv (synCcom F G) C) (synCfv F (synCfv G C)) p0006 p0013 p0020
  exact p0021

/-- Checked nominal proof certificate identified upstream as `g_fvco`. -/
@[expose]
noncomputable def gFvco (A : Class) (F : Class) (G : Class) :
    Nominal.NPrf
      (.imp (synWa (synWfun G) (.classMem A (synCdm G)))
        (.classEq (synCfv (synCcom F G) A) (synCfv F (synCfv G A)))) :=
  by
  have p0000 := @gFunfn G
  have p0001 := @gFvco2 (synCdm G) A F G
  have p0002 :=
    @gSylanb (synWfun G) (synWfn G (synCdm G)) (.classMem A (synCdm G))
      (.classEq (synCfv (synCcom F G) A) (synCfv F (synCfv G A))) p0000 p0001
  exact p0002

/-- Checked nominal proof certificate identified upstream as `g_fvco3`. -/
@[expose]
noncomputable def gFvco3 (A : Class) (B : Class) (C : Class) (F : Class) (G : Class) :
    Nominal.NPrf
      (.imp (synWa (synWf G A B) (.classMem C A))
        (.classEq (synCfv (synCcom F G) C) (synCfv F (synCfv G C)))) :=
  by
  have p0000 := @gFfn A B G
  have p0001 := @gFvco2 A C F G
  have p0002 :=
    @gSylan (synWf G A B) (synWfn G A) (.classMem C A)
      (.classEq (synCfv (synCcom F G) C) (synCfv F (synCfv G C))) p0000 p0001
  exact p0002

/-- Checked nominal proof certificate identified upstream as `g_fvopab3ig`. -/
@[expose]
noncomputable def gFvopab3ig (ph : Wff) (ps : Wff) (ch : Wff) (x : Var) (y : Var)
    (A : Class) (B : Class) (C : Class) (D : Class) (F : Class) (dv_A_x : x ∉ A.fv)
    (dv_A_y : y ∉ A.fv) (dv_B_x : x ∉ B.fv) (dv_B_y : y ∉ B.fv) (dv_C_x : x ∉ C.fv)
    (dv_C_y : y ∉ C.fv) (dv_ch_x : x ∉ ch.fv) (dv_ch_y : y ∉ ch.fv) (dv_x_y : x ≠ y)
    (hyp_fvopab3ig_1 : Nominal.NPrf (.imp (.classEq (.cv x) A) (synWb ph ps)))
    (hyp_fvopab3ig_2 : Nominal.NPrf (.imp (.classEq (.cv y) B) (synWb ps ch)))
    (hyp_fvopab3ig_3 : Nominal.NPrf (.imp (.classMem (.cv x) C) (synWmo y ph)))
    (hyp_fvopab3ig_4 :
      Nominal.NPrf (.classEq F (synCopab x y (synWa (.classMem (.cv x) C) ph)))) :
    Nominal.NPrf
      (.imp (synWa (.classMem A C) (.classMem B D)) (.imp ch (.classEq (synCfv F A) B))) :=
  by
  have dv_cache_0001 : x ≠ y := by exact (show x ≠ y from (by exact dv_x_y))
  have dv_cache_0002 : y ∉ ((Wff.classMem (.cv x) C)).fv :=
    by
    clear dv_cache_0001
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, (Ne.symm dv_x_y), dv_C_y, or_false, not_false_eq_true])
  have dv_cache_0003 : x ∉ (A).fv :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_A_x, not_false_eq_true])
  have dv_cache_0004 : y ∉ (A).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_A_y, not_false_eq_true])
  have dv_cache_0005 : x ∉ (B).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_B_x, not_false_eq_true])
  have dv_cache_0006 : y ∉ (B).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_B_y, not_false_eq_true])
  have dv_cache_0007 : x ∉ ((synWa (.classMem A C) ch)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, Finset.mem_union, dv_A_x, dv_C_x,
          dv_ch_x, or_false, not_false_eq_true])
  have dv_cache_0008 : y ∉ ((synWa (.classMem A C) ch)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, Finset.mem_union, dv_A_y, dv_C_y,
          dv_ch_y, or_false, not_false_eq_true])
  have p0000 := @gFunopab (synWa (.classMem (.cv x) C) ph) x y dv_cache_0001
  have p0001 := @gMoanimv (.classMem (.cv x) C) ph y dv_cache_0002
  have p0002 :=
    @gMpbir (synWmo y (synWa (.classMem (.cv x) C) ph))
      (.imp (.classMem (.cv x) C) (synWmo y ph)) hyp_fvopab3ig_3 p0001
  have p0003 :=
    @gMpgbir (synWfun (synCopab x y (synWa (.classMem (.cv x) C) ph)))
      (synWmo y (synWa (.classMem (.cv x) C) ph)) x p0000 p0002
  have p0004 := @gSimpl (.classMem A C) (.classMem B D)
  have p0005 := @gEleq1 (.cv x) A C
  have p0006 :=
    @gAnbi12d (.classEq (.cv x) A) (.classMem (.cv x) C) (.classMem A C) ph ps p0005
      hyp_fvopab3ig_1
  have p0007 := @gAnbi2d (.classEq (.cv y) B) ps ch (.classMem A C) hyp_fvopab3ig_2
  have p0008 :=
    @gOpelopabg (synWa (.classMem (.cv x) C) ph) (synWa (.classMem A C) ps)
      (synWa (.classMem A C) ch) x y A B C D dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0001 p0006 p0007
  have p0009 :=
    @gBiimprd (synWa (.classMem A C) (.classMem B D))
      (.classMem (synCop A B) (synCopab x y (synWa (.classMem (.cv x) C) ph)))
      (synWa (.classMem A C) ch) p0008
  have p0010 :=
    @gMpand (synWa (.classMem A C) (.classMem B D)) (.classMem A C) ch
      (.classMem (synCop A B) (synCopab x y (synWa (.classMem (.cv x) C) ph))) p0004
      p0009
  have p0011 := @gFunopfv A B (synCopab x y (synWa (.classMem (.cv x) C) ph))
  have p0012 :=
    @gEe02 (synWfun (synCopab x y (synWa (.classMem (.cv x) C) ph)))
      (synWa (.classMem A C) (.classMem B D)) ch
      (.classMem (synCop A B) (synCopab x y (synWa (.classMem (.cv x) C) ph)))
      (.classEq (synCfv (synCopab x y (synWa (.classMem (.cv x) C) ph)) A) B) p0003
      p0010 p0011
  have p0013 :=
    @gFveq1i A F (synCopab x y (synWa (.classMem (.cv x) C) ph)) hyp_fvopab3ig_4
  have p0014 :=
    @gEqeq1i (synCfv F A) (synCfv (synCopab x y (synWa (.classMem (.cv x) C) ph)) A)
      B p0013
  have p0015 :=
    @gSyl6ibr (synWa (.classMem A C) (.classMem B D)) ch
      (.classEq (synCfv (synCopab x y (synWa (.classMem (.cv x) C) ph)) A) B)
      (.classEq (synCfv F A) B) p0012 p0014
  exact p0015

/-- Checked nominal proof certificate identified upstream as `g_fvopab4g`. -/
@[expose]
noncomputable def gFvopab4g (x : Var) (y : Var) (A : Class) (B : Class) (C : Class)
    (D : Class) (R : Class) (F : Class) (dv_A_x : x ∉ A.fv) (dv_A_y : y ∉ A.fv)
    (dv_B_y : y ∉ B.fv) (dv_C_x : x ∉ C.fv) (dv_C_y : y ∉ C.fv) (dv_D_x : x ∉ D.fv)
    (dv_D_y : y ∉ D.fv) (dv_x_y : x ≠ y)
    (hyp_fvopab4g_1 : Nominal.NPrf (.imp (.classEq (.cv x) A) (.classEq B C)))
    (hyp_fvopab4g_2 : Nominal.NPrf (.classEq F
          (synCopab x y (synWa (.classMem (.cv x) D) (.classEq (.cv y) B))))) :
    Nominal.NPrf
      (.imp (synWa (.classMem A D) (.classMem C R)) (.classEq (synCfv F A) C)) :=
  by
  have dv_cache_0001 : y ∉ (B).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_B_y, not_false_eq_true])
  have dv_cache_0002 : x ∉ (A).fv :=
    by
    clear dv_cache_0001
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_A_x, not_false_eq_true])
  have dv_cache_0003 : y ∉ (A).fv :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_A_y, not_false_eq_true])
  have dv_cache_0004 : x ∉ (C).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_C_x, not_false_eq_true])
  have dv_cache_0005 : y ∉ (C).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_C_y, not_false_eq_true])
  have dv_cache_0006 : x ∉ (D).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_D_x, not_false_eq_true])
  have dv_cache_0007 : y ∉ (D).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_D_y, not_false_eq_true])
  have dv_cache_0008 : x ∉ ((Wff.classEq C C)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, Finset.mem_union, dv_C_x,
          or_false, not_false_eq_true])
  have dv_cache_0009 : y ∉ ((Wff.classEq C C)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, Finset.mem_union, dv_C_y,
          or_false, not_false_eq_true])
  have dv_cache_0010 : x ≠ y :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009
    exact (show x ≠ y from (by exact dv_x_y))
  have p0000 := @gEqid C
  have p0001 := @gEqeq2d (.classEq (.cv x) A) B C (.cv y) hyp_fvopab4g_1
  have p0002 := @gEqeq1 (.cv y) C C
  have p0003 := @gMoeq y B dv_cache_0001
  have p0004 := @gA1i (synWmo y (.classEq (.cv y) B)) (.classMem (.cv x) D) p0003
  have p0005 :=
    @gFvopab3ig (.classEq (.cv y) B) (.classEq (.cv y) C) (.classEq C C) x y A C D R F
      dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007
      dv_cache_0008 dv_cache_0009 dv_cache_0010 p0001 p0002 p0004 hyp_fvopab4g_2
  have p0006 :=
    @gMpi (synWa (.classMem A D) (.classMem C R)) (.classEq C C)
      (.classEq (synCfv F A) C) p0000 p0005
  exact p0006

/-- Checked nominal proof certificate identified upstream as `g_fvopab4`. -/
@[expose]
noncomputable def gFvopab4 (x : Var) (y : Var) (A : Class) (B : Class) (C : Class)
    (D : Class) (F : Class) (dv_A_x : x ∉ A.fv) (dv_A_y : y ∉ A.fv) (dv_B_y : y ∉ B.fv)
    (dv_C_x : x ∉ C.fv) (dv_C_y : y ∉ C.fv) (dv_D_x : x ∉ D.fv) (dv_D_y : y ∉ D.fv)
    (dv_x_y : x ≠ y)
    (hyp_fvopab4g_1 : Nominal.NPrf (.imp (.classEq (.cv x) A) (.classEq B C)))
    (hyp_fvopab4g_2 : Nominal.NPrf
        (.classEq F (synCopab x y (synWa (.classMem (.cv x) D) (.classEq (.cv y) B)))))
    (hyp_fvopab4_3 : Nominal.NPrf (.classMem C (synCvv))) :
    Nominal.NPrf (.imp (.classMem A D) (.classEq (synCfv F A) C)) :=
  by
  have dv_cache_0001 : x ∉ (A).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_A_x, not_false_eq_true])
  have dv_cache_0002 : y ∉ (A).fv :=
    by
    clear dv_cache_0001
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_A_y, not_false_eq_true])
  have dv_cache_0003 : y ∉ (B).fv :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_B_y, not_false_eq_true])
  have dv_cache_0004 : x ∉ (C).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_C_x, not_false_eq_true])
  have dv_cache_0005 : y ∉ (C).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_C_y, not_false_eq_true])
  have dv_cache_0006 : x ∉ (D).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_D_x, not_false_eq_true])
  have dv_cache_0007 : y ∉ (D).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_D_y, not_false_eq_true])
  have dv_cache_0008 : x ≠ y :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007
    exact (show x ≠ y from (by exact dv_x_y))
  have p0000 :=
    @gFvopab4g x y A B C D (synCvv) F dv_cache_0001 dv_cache_0002 dv_cache_0003
      dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 hyp_fvopab4g_1
      hyp_fvopab4g_2
  have p0001 :=
    @gMpan2 (.classMem A D) (.classMem C (synCvv)) (.classEq (synCfv F A) C)
      hyp_fvopab4_3 p0000
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_eqfnfv`. -/
@[expose]
noncomputable def gEqfnfv (x : Var) (A : Class) (F : Class) (G : Class)
    (dv_A_x : x ∉ A.fv) (dv_F_x : x ∉ F.fv) (dv_G_x : x ∉ G.fv) :
    Nominal.NPrf
      (.imp (synWa (synWfn F A) (synWfn G A)) (synWb (.classEq F G)
          (synWral x A (.classEq (synCfv F (.cv x)) (synCfv G (.cv x)))))) :=
  by
  let proofSupport : Finset Var := ({ x } : Finset Var) ∪ A.fv ∪ F.fv ∪ G.fv
  let y : Var := freshVar proofSupport 0
  have fresh_y : y ∉ proofSupport :=
    by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_y_ne_x : y ≠ x := by
    intro h
    exact
      fresh_y
        (Finset.mem_union_left _ (Finset.mem_union_left _
            (Finset.mem_union_left _ (Finset.mem_singleton.mpr h))))
  have fresh_x_ne_y : x ≠ y := Ne.symm fresh_y_ne_x
  have fresh_y_not_A : y ∉ A.fv := by
    intro h
    exact
      fresh_y
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))
  have fresh_y_not_F : y ∉ F.fv := by
    intro h
    exact fresh_y (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_y_not_G : y ∉ G.fv := by
    intro h
    exact fresh_y (Finset.mem_union_right _ (h))
  have dv_cache_0001 : x ∉ ((Wff.classEq F G)).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, Finset.mem_union, dv_F_x,
          dv_G_x, or_false, not_false_eq_true])
  have dv_cache_0002 : y ∉ ((synWa (synWfn F A) (synWfn G A))).fv :=
    by
    clear dv_cache_0001
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wfn, Finset.mem_union,
          fresh_y_not_F, fresh_y_not_A, fresh_y_not_G, or_false, not_false_eq_true])
  have dv_cache_0003 :
    y ∉
      ((Wff.imp (.classMem (.cv x) A) (.classEq (synCfv F (.cv x)) (synCfv G (.cv x))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv, Finset.mem_union,
          Finset.mem_singleton, fresh_y_ne_x, fresh_y_not_A, fresh_y_not_F, fresh_y_not_G,
          or_false, not_false_eq_true])
  have dv_cache_0004 : x ∉ ((synWa (synWfn F A) (synWfn G A))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wfn, Finset.mem_union, dv_F_x,
          dv_A_x, dv_G_x, or_false, not_false_eq_true])
  have dv_cache_0005 : x ∉ (F).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_F_x, not_false_eq_true])
  have dv_cache_0006 : y ∉ (F).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_y_not_F, not_false_eq_true])
  have dv_cache_0007 : x ∉ (G).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_G_x, not_false_eq_true])
  have dv_cache_0008 : y ∉ (G).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_y_not_G, not_false_eq_true])
  have dv_cache_0009 : x ≠ y :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008
    exact (show x ≠ y from (by exact fresh_x_ne_y))
  have p0000 := @gFveq1 (.cv x) F G
  have p0001 :=
    @gRalrimivw (.classEq F G) (.classEq (synCfv F (.cv x)) (synCfv G (.cv x))) x A
      dv_cache_0001 p0000
  have p0002 :=
    @gPm227 (.classMem (.cv x) A) (.classEq (synCfv F (.cv x)) (synCfv G (.cv x)))
  have p0003 :=
    @gAdantl (.classMem (.cv x) A)
      (.imp (.imp (.classMem (.cv x) A) (.classEq (synCfv F (.cv x)) (synCfv G (.cv x))))
        (.classEq (synCfv F (.cv x)) (synCfv G (.cv x))))
      (synWa (synWfn F A) (synWfn G A)) p0002
  have p0004 := @gEqeq1 (synCfv F (.cv x)) (synCfv G (.cv x)) (.cv y)
  have p0005 := @gFnopfvb A (.cv x) (.cv y) F
  have p0006 :=
    @gAdantlr (synWfn F A) (.classMem (.cv x) A)
      (synWb (.classEq (synCfv F (.cv x)) (.cv y)) (.classMem (synCop (.cv x) (.cv y)) F))
      (synWfn G A) p0005
  have p0007 := @gFnopfvb A (.cv x) (.cv y) G
  have p0008 :=
    @gAdantll (synWfn G A) (.classMem (.cv x) A)
      (synWb (.classEq (synCfv G (.cv x)) (.cv y)) (.classMem (synCop (.cv x) (.cv y)) G))
      (synWfn F A) p0007
  have p0009 :=
    @gBibi12d (synWa (synWa (synWfn F A) (synWfn G A)) (.classMem (.cv x) A))
      (.classEq (synCfv F (.cv x)) (.cv y)) (.classMem (synCop (.cv x) (.cv y)) F)
      (.classEq (synCfv G (.cv x)) (.cv y)) (.classMem (synCop (.cv x) (.cv y)) G) p0006
      p0008
  have p0010 :=
    @gSyl5ib (.classEq (synCfv F (.cv x)) (synCfv G (.cv x)))
      (synWb (.classEq (synCfv F (.cv x)) (.cv y)) (.classEq (synCfv G (.cv x)) (.cv y)))
      (synWa (synWa (synWfn F A) (synWfn G A)) (.classMem (.cv x) A))
      (synWb (.classMem (synCop (.cv x) (.cv y)) F) (.classMem (synCop (.cv x) (.cv y)) G))
      p0004 p0009
  have p0011 :=
    @gSyld (synWa (synWa (synWfn F A) (synWfn G A)) (.classMem (.cv x) A))
      (.imp (.classMem (.cv x) A) (.classEq (synCfv F (.cv x)) (synCfv G (.cv x))))
      (.classEq (synCfv F (.cv x)) (synCfv G (.cv x)))
      (synWb (.classMem (synCop (.cv x) (.cv y)) F) (.classMem (synCop (.cv x) (.cv y)) G))
      p0003 p0010
  have p0012 :=
    @gExpcom (synWa (synWfn F A) (synWfn G A)) (.classMem (.cv x) A)
      (.imp (.imp (.classMem (.cv x) A) (.classEq (synCfv F (.cv x)) (synCfv G (.cv x))))
        (synWb (.classMem (synCop (.cv x) (.cv y)) F)
          (.classMem (synCop (.cv x) (.cv y)) G)))
      p0011
  have p0013 := @gOpeldm (.cv x) (.cv y) F
  have p0014 := @gFndm A F
  have p0015 := @gEleq2d (synWfn F A) (synCdm F) A (.cv x) p0014
  have p0016 :=
    @gSyl5ib (.classMem (synCop (.cv x) (.cv y)) F) (.classMem (.cv x) (synCdm F))
      (synWfn F A) (.classMem (.cv x) A) p0013 p0015
  have p0017 :=
    @gAdantr (synWfn F A)
      (.imp (.classMem (synCop (.cv x) (.cv y)) F) (.classMem (.cv x) A)) (synWfn G A)
      p0016
  have p0018 :=
    @gCon3d (synWa (synWfn F A) (synWfn G A)) (.classMem (synCop (.cv x) (.cv y)) F)
      (.classMem (.cv x) A) p0017
  have p0019 :=
    @gImpcom (synWa (synWfn F A) (synWfn G A)) (.neg (.classMem (.cv x) A))
      (.neg (.classMem (synCop (.cv x) (.cv y)) F)) p0018
  have p0020 := @gOpeldm (.cv x) (.cv y) G
  have p0021 := @gFndm A G
  have p0022 := @gEleq2d (synWfn G A) (synCdm G) A (.cv x) p0021
  have p0023 :=
    @gSyl5ib (.classMem (synCop (.cv x) (.cv y)) G) (.classMem (.cv x) (synCdm G))
      (synWfn G A) (.classMem (.cv x) A) p0020 p0022
  have p0024 :=
    @gAdantl (synWfn G A)
      (.imp (.classMem (synCop (.cv x) (.cv y)) G) (.classMem (.cv x) A)) (synWfn F A)
      p0023
  have p0025 :=
    @gCon3d (synWa (synWfn F A) (synWfn G A)) (.classMem (synCop (.cv x) (.cv y)) G)
      (.classMem (.cv x) A) p0024
  have p0026 :=
    @gImpcom (synWa (synWfn F A) (synWfn G A)) (.neg (.classMem (.cv x) A))
      (.neg (.classMem (synCop (.cv x) (.cv y)) G)) p0025
  have p0027 :=
    @gN2falsed
      (synWa (.neg (.classMem (.cv x) A)) (synWa (synWfn F A) (synWfn G A)))
      (.classMem (synCop (.cv x) (.cv y)) F) (.classMem (synCop (.cv x) (.cv y)) G)
      p0019 p0026
  have p0028 :=
    @gEx (.neg (.classMem (.cv x) A)) (synWa (synWfn F A) (synWfn G A))
      (synWb (.classMem (synCop (.cv x) (.cv y)) F) (.classMem (synCop (.cv x) (.cv y)) G))
      p0027
  have p0029 :=
    @gA1dd (.neg (.classMem (.cv x) A)) (synWa (synWfn F A) (synWfn G A))
      (synWb (.classMem (synCop (.cv x) (.cv y)) F) (.classMem (synCop (.cv x) (.cv y)) G))
      (.imp (.classMem (.cv x) A) (.classEq (synCfv F (.cv x)) (synCfv G (.cv x))))
      p0028
  have p0030 :=
    @gPm261i (.classMem (.cv x) A)
      (.imp (synWa (synWfn F A) (synWfn G A)) (.imp
          (.imp (.classMem (.cv x) A) (.classEq (synCfv F (.cv x)) (synCfv G (.cv x))))
          (synWb (.classMem (synCop (.cv x) (.cv y)) F)
            (.classMem (synCop (.cv x) (.cv y)) G))))
      p0012 p0029
  have p0031 :=
    @gAlrimdv (synWa (synWfn F A) (synWfn G A))
      (.imp (.classMem (.cv x) A) (.classEq (synCfv F (.cv x)) (synCfv G (.cv x))))
      (synWb (.classMem (synCop (.cv x) (.cv y)) F) (.classMem (synCop (.cv x) (.cv y)) G))
      y dv_cache_0002 dv_cache_0003 p0030
  have p0032 :=
    @gAlimdv (synWa (synWfn F A) (synWfn G A))
      (.imp (.classMem (.cv x) A) (.classEq (synCfv F (.cv x)) (synCfv G (.cv x))))
      (.all y (synWb (.classMem (synCop (.cv x) (.cv y)) F)
          (.classMem (synCop (.cv x) (.cv y)) G)))
      x dv_cache_0004 p0031
  have p0033 :=
    (Nominal.biimpRefl (synWral x A (.classEq (synCfv F (.cv x)) (synCfv G (.cv x)))))
  have p0034 :=
    @gEqrel x y F G dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009
  have p0035 :=
    @gN3imtr4g (synWa (synWfn F A) (synWfn G A))
      (.all x (.imp (.classMem (.cv x) A) (.classEq (synCfv F (.cv x)) (synCfv G (.cv x)))))
      (.all x (.all y (synWb (.classMem (synCop (.cv x) (.cv y)) F)
            (.classMem (synCop (.cv x) (.cv y)) G))))
      (synWral x A (.classEq (synCfv F (.cv x)) (synCfv G (.cv x)))) (.classEq F G)
      p0032 p0033 p0034
  have p0036 :=
    @gImpbid2 (synWa (synWfn F A) (synWfn G A)) (.classEq F G)
      (synWral x A (.classEq (synCfv F (.cv x)) (synCfv G (.cv x)))) p0001 p0035
  exact p0036


end NFChoice.DirectNominalPrf.WPPReplay

end
