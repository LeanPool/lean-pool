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

@[expose]
noncomputable def g_f1oeq3 (A : Class) (B : Class) (C : Class) (F : Class) :
    Nominal.NPrf (.imp (.classEq A B) (syn_wb (syn_wf1o F C A) (syn_wf1o F C B))) :=
  by
  have p0000 := @g_f1eq3 A B C F
  have p0001 := @g_foeq3 A B C F
  have p0002 :=
    @g_anbi12d (.classEq A B) (syn_wf1 F C A) (syn_wf1 F C B) (syn_wfo F C A)
      (syn_wfo F C B) p0000 p0001
  have p0003 := (Nominal.biimpRefl (syn_wf1o F C A))
  have p0004 := (Nominal.biimpRefl (syn_wf1o F C B))
  have p0005 :=
    @g_n_3bitr4g (.classEq A B) (syn_wa (syn_wf1 F C A) (syn_wfo F C A))
      (syn_wa (syn_wf1 F C B) (syn_wfo F C B)) (syn_wf1o F C A) (syn_wf1o F C B) p0002
      p0003 p0004
  exact p0005

@[expose]
noncomputable def g_f1oeq23 (A : Class) (B : Class) (C : Class) (D : Class) (F : Class) :
    Nominal.NPrf
      (.imp (syn_wa (.classEq A B) (.classEq C D))
        (syn_wb (syn_wf1o F A C) (syn_wf1o F B D))) :=
  by
  have p0000 := @g_f1oeq2 A B C F
  have p0001 := @g_f1oeq3 C D B F
  have p0002 :=
    @g_sylan9bb (.classEq A B) (syn_wf1o F A C) (syn_wf1o F B C) (.classEq C D)
      (syn_wf1o F B D) p0000 p0001
  exact p0002

@[expose]
noncomputable def g_f1of1 (A : Class) (B : Class) (F : Class) :
    Nominal.NPrf (.imp (syn_wf1o F A B) (syn_wf1 F A B)) :=
  by
  have p0000 := (Nominal.biimpRefl (syn_wf1o F A B))
  have p0001 := @g_simplbi (syn_wf1o F A B) (syn_wf1 F A B) (syn_wfo F A B) p0000
  exact p0001

@[expose]
noncomputable def g_f1of (A : Class) (B : Class) (F : Class) :
    Nominal.NPrf (.imp (syn_wf1o F A B) (syn_wf F A B)) :=
  by
  have p0000 := @g_f1of1 A B F
  have p0001 := @g_f1f A B F
  have p0002 := @g_syl (syn_wf1o F A B) (syn_wf1 F A B) (syn_wf F A B) p0000 p0001
  exact p0002

@[expose]
noncomputable def g_f1ofn (A : Class) (B : Class) (F : Class) :
    Nominal.NPrf (.imp (syn_wf1o F A B) (syn_wfn F A)) :=
  by
  have p0000 := @g_f1of A B F
  have p0001 := @g_ffn A B F
  have p0002 := @g_syl (syn_wf1o F A B) (syn_wf F A B) (syn_wfn F A) p0000 p0001
  exact p0002

@[expose]
noncomputable def g_f1ofun (A : Class) (B : Class) (F : Class) :
    Nominal.NPrf (.imp (syn_wf1o F A B) (syn_wfun F)) :=
  by
  have p0000 := @g_f1ofn A B F
  have p0001 := @g_fnfun A F
  have p0002 := @g_syl (syn_wf1o F A B) (syn_wfn F A) (syn_wfun F) p0000 p0001
  exact p0002

@[expose]
noncomputable def g_f1odm (A : Class) (B : Class) (F : Class) :
    Nominal.NPrf (.imp (syn_wf1o F A B) (.classEq (syn_cdm F) A)) :=
  by
  have p0000 := @g_f1ofn A B F
  have p0001 := @g_fndm A F
  have p0002 := @g_syl (syn_wf1o F A B) (syn_wfn F A) (.classEq (syn_cdm F) A) p0000 p0001
  exact p0002

@[expose]
noncomputable def g_dff1o2 (A : Class) (B : Class) (F : Class) :
    Nominal.NPrf
      (syn_wb (syn_wf1o F A B)
        (syn_w3a (syn_wfn F A) (syn_wfun (syn_ccnv F)) (.classEq (syn_crn F) B))) :=
  by
  have p0000 := (Nominal.biimpRefl (syn_wf1o F A B))
  have p0001 := (Nominal.biimpRefl (syn_wf1 F A B))
  have p0002 := (Nominal.biimpRefl (syn_wfo F A B))
  have p0003 :=
    @g_anbi12i (syn_wf1 F A B) (syn_wa (syn_wf F A B) (syn_wfun (syn_ccnv F)))
      (syn_wfo F A B) (syn_wa (syn_wfn F A) (.classEq (syn_crn F) B)) p0001 p0002
  have p0004 :=
    @g_ancom (syn_wf F A B)
      (syn_wa (syn_wfun (syn_ccnv F)) (syn_wa (syn_wfn F A) (.classEq (syn_crn F) B)))
  have p0005 := @g_n_3anass (syn_wfn F A) (syn_wfun (syn_ccnv F)) (.classEq (syn_crn F) B)
  have p0006 := @g_an12 (syn_wfn F A) (syn_wfun (syn_ccnv F)) (.classEq (syn_crn F) B)
  have p0007 :=
    @g_bitri (syn_w3a (syn_wfn F A) (syn_wfun (syn_ccnv F)) (.classEq (syn_crn F) B))
      (syn_wa (syn_wfn F A) (syn_wa (syn_wfun (syn_ccnv F)) (.classEq (syn_crn F) B)))
      (syn_wa (syn_wfun (syn_ccnv F)) (syn_wa (syn_wfn F A) (.classEq (syn_crn F) B)))
      p0005 p0006
  have p0008 :=
    @g_anbi1i (syn_w3a (syn_wfn F A) (syn_wfun (syn_ccnv F)) (.classEq (syn_crn F) B))
      (syn_wa (syn_wfun (syn_ccnv F)) (syn_wa (syn_wfn F A) (.classEq (syn_crn F) B)))
      (syn_wf F A B) p0007
  have p0009 :=
    @g_bitr4i
      (syn_wa (syn_wf F A B)
        (syn_wa (syn_wfun (syn_ccnv F)) (syn_wa (syn_wfn F A) (.classEq (syn_crn F) B))))
      (syn_wa (syn_wa (syn_wfun (syn_ccnv F)) (syn_wa (syn_wfn F A) (.classEq (syn_crn F) B)))
        (syn_wf F A B))
      (syn_wa (syn_w3a (syn_wfn F A) (syn_wfun (syn_ccnv F)) (.classEq (syn_crn F) B))
        (syn_wf F A B))
      p0004 p0008
  have p0010 :=
    @g_anass (syn_wf F A B) (syn_wfun (syn_ccnv F))
      (syn_wa (syn_wfn F A) (.classEq (syn_crn F) B))
  have p0011 := @g_eqimss (syn_crn F) B
  have p0012 := (Nominal.biimpRefl (syn_wf F A B))
  have p0013 :=
    @g_biimpri (syn_wf F A B) (syn_wa (syn_wfn F A) (syn_wss (syn_crn F) B)) p0012
  have p0014 :=
    @g_sylan2 (.classEq (syn_crn F) B) (syn_wfn F A) (syn_wss (syn_crn F) B)
      (syn_wf F A B) p0011 p0013
  have p0015 :=
    @g_n_3adant2 (syn_wfn F A) (.classEq (syn_crn F) B) (syn_wf F A B)
      (syn_wfun (syn_ccnv F)) p0014
  have p0016 :=
    @g_pm4_71i (syn_w3a (syn_wfn F A) (syn_wfun (syn_ccnv F)) (.classEq (syn_crn F) B))
      (syn_wf F A B) p0015
  have p0017 :=
    @g_n_3bitr4i
      (syn_wa (syn_wf F A B)
        (syn_wa (syn_wfun (syn_ccnv F)) (syn_wa (syn_wfn F A) (.classEq (syn_crn F) B))))
      (syn_wa (syn_w3a (syn_wfn F A) (syn_wfun (syn_ccnv F)) (.classEq (syn_crn F) B))
        (syn_wf F A B))
      (syn_wa (syn_wa (syn_wf F A B) (syn_wfun (syn_ccnv F)))
        (syn_wa (syn_wfn F A) (.classEq (syn_crn F) B)))
      (syn_w3a (syn_wfn F A) (syn_wfun (syn_ccnv F)) (.classEq (syn_crn F) B)) p0009 p0010
      p0016
  have p0018 :=
    @g_n_3bitri (syn_wf1o F A B) (syn_wa (syn_wf1 F A B) (syn_wfo F A B))
      (syn_wa (syn_wa (syn_wf F A B) (syn_wfun (syn_ccnv F)))
        (syn_wa (syn_wfn F A) (.classEq (syn_crn F) B)))
      (syn_w3a (syn_wfn F A) (syn_wfun (syn_ccnv F)) (.classEq (syn_crn F) B)) p0000 p0003
      p0017
  exact p0018

@[expose]
noncomputable def g_dff1o3 (A : Class) (B : Class) (F : Class) :
    Nominal.NPrf
      (syn_wb (syn_wf1o F A B) (syn_wa (syn_wfo F A B) (syn_wfun (syn_ccnv F)))) :=
  by
  have p0000 :=
    (Nominal.biimpRefl (syn_w3a (syn_wfn F A) (syn_wfun (syn_ccnv F)) (.classEq (syn_crn F) B)))
  have p0001 := @g_an32 (syn_wfn F A) (syn_wfun (syn_ccnv F)) (.classEq (syn_crn F) B)
  have p0002 :=
    @g_bitri (syn_w3a (syn_wfn F A) (syn_wfun (syn_ccnv F)) (.classEq (syn_crn F) B))
      (syn_wa (syn_wa (syn_wfn F A) (syn_wfun (syn_ccnv F))) (.classEq (syn_crn F) B))
      (syn_wa (syn_wa (syn_wfn F A) (.classEq (syn_crn F) B)) (syn_wfun (syn_ccnv F)))
      p0000 p0001
  have p0003 := @g_dff1o2 A B F
  have p0004 := (Nominal.biimpRefl (syn_wfo F A B))
  have p0005 :=
    @g_anbi1i (syn_wfo F A B) (syn_wa (syn_wfn F A) (.classEq (syn_crn F) B))
      (syn_wfun (syn_ccnv F)) p0004
  have p0006 :=
    @g_n_3bitr4i (syn_w3a (syn_wfn F A) (syn_wfun (syn_ccnv F)) (.classEq (syn_crn F) B))
      (syn_wa (syn_wa (syn_wfn F A) (.classEq (syn_crn F) B)) (syn_wfun (syn_ccnv F)))
      (syn_wf1o F A B) (syn_wa (syn_wfo F A B) (syn_wfun (syn_ccnv F))) p0002 p0003 p0005
  exact p0006

@[expose]
noncomputable def g_f1ofo (A : Class) (B : Class) (F : Class) :
    Nominal.NPrf (.imp (syn_wf1o F A B) (syn_wfo F A B)) :=
  by
  have p0000 := @g_dff1o3 A B F
  have p0001 := @g_simplbi (syn_wf1o F A B) (syn_wfo F A B) (syn_wfun (syn_ccnv F)) p0000
  exact p0001

@[expose]
noncomputable def g_dff1o4 (A : Class) (B : Class) (F : Class) :
    Nominal.NPrf
      (syn_wb (syn_wf1o F A B) (syn_wa (syn_wfn F A) (syn_wfn (syn_ccnv F) B))) :=
  by
  have p0000 := @g_dff1o2 A B F
  have p0001 := @g_n_3anass (syn_wfn F A) (syn_wfun (syn_ccnv F)) (.classEq (syn_crn F) B)
  have p0002 := @g_dfrn4 F
  have p0003 := @g_eqeq1i (syn_crn F) (syn_cdm (syn_ccnv F)) B p0002
  have p0004 :=
    @g_anbi2i (.classEq (syn_crn F) B) (.classEq (syn_cdm (syn_ccnv F)) B)
      (syn_wfun (syn_ccnv F)) p0003
  have p0005 := (Nominal.biimpRefl (syn_wfn (syn_ccnv F) B))
  have p0006 :=
    @g_bitr4i (syn_wa (syn_wfun (syn_ccnv F)) (.classEq (syn_crn F) B))
      (syn_wa (syn_wfun (syn_ccnv F)) (.classEq (syn_cdm (syn_ccnv F)) B))
      (syn_wfn (syn_ccnv F) B) p0004 p0005
  have p0007 :=
    @g_anbi2i (syn_wa (syn_wfun (syn_ccnv F)) (.classEq (syn_crn F) B))
      (syn_wfn (syn_ccnv F) B) (syn_wfn F A) p0006
  have p0008 :=
    @g_n_3bitri (syn_wf1o F A B)
      (syn_w3a (syn_wfn F A) (syn_wfun (syn_ccnv F)) (.classEq (syn_crn F) B))
      (syn_wa (syn_wfn F A) (syn_wa (syn_wfun (syn_ccnv F)) (.classEq (syn_crn F) B)))
      (syn_wa (syn_wfn F A) (syn_wfn (syn_ccnv F) B)) p0000 p0001 p0007
  exact p0008

@[expose]
noncomputable def g_dff1o5 (A : Class) (B : Class) (F : Class) :
    Nominal.NPrf
      (syn_wb (syn_wf1o F A B) (syn_wa (syn_wf1 F A B) (.classEq (syn_crn F) B))) :=
  by
  have p0000 := (Nominal.biimpRefl (syn_wf1o F A B))
  have p0001 := @g_f1f A B F
  have p0002 := @g_biantrurd (syn_wf1 F A B) (syn_wf F A B) (.classEq (syn_crn F) B) p0001
  have p0003 := @g_dffo2 A B F
  have p0004 :=
    @g_syl6rbbr (syn_wf1 F A B) (.classEq (syn_crn F) B)
      (syn_wa (syn_wf F A B) (.classEq (syn_crn F) B)) (syn_wfo F A B) p0002 p0003
  have p0005 := @g_pm5_32i (syn_wf1 F A B) (syn_wfo F A B) (.classEq (syn_crn F) B) p0004
  have p0006 :=
    @g_bitri (syn_wf1o F A B) (syn_wa (syn_wf1 F A B) (syn_wfo F A B))
      (syn_wa (syn_wf1 F A B) (.classEq (syn_crn F) B)) p0000 p0005
  exact p0006

@[expose]
noncomputable def g_f1orn (A : Class) (F : Class) :
    Nominal.NPrf
      (syn_wb (syn_wf1o F A (syn_crn F)) (syn_wa (syn_wfn F A) (syn_wfun (syn_ccnv F)))) :=
  by
  have p0000 :=
    (Nominal.biimpRefl
      (syn_w3a (syn_wfn F A) (syn_wfun (syn_ccnv F)) (.classEq (syn_crn F) (syn_crn F))))
  have p0001 := @g_dff1o2 A (syn_crn F) F
  have p0002 := @g_eqid (syn_crn F)
  have p0003 :=
    @g_biantru (.classEq (syn_crn F) (syn_crn F))
      (syn_wa (syn_wfn F A) (syn_wfun (syn_ccnv F))) p0002
  have p0004 :=
    @g_n_3bitr4i
      (syn_w3a (syn_wfn F A) (syn_wfun (syn_ccnv F)) (.classEq (syn_crn F) (syn_crn F)))
      (syn_wa (syn_wa (syn_wfn F A) (syn_wfun (syn_ccnv F))) (.classEq (syn_crn F) (syn_crn F)))
      (syn_wf1o F A (syn_crn F)) (syn_wa (syn_wfn F A) (syn_wfun (syn_ccnv F))) p0000
      p0001 p0003
  exact p0004

@[expose]
noncomputable def g_f1f1orn (A : Class) (B : Class) (F : Class) :
    Nominal.NPrf (.imp (syn_wf1 F A B) (syn_wf1o F A (syn_crn F))) :=
  by
  have p0000 := @g_f1fn A B F
  have p0001 := (Nominal.biimpRefl (syn_wf1 F A B))
  have p0002 := @g_simprbi (syn_wf1 F A B) (syn_wf F A B) (syn_wfun (syn_ccnv F)) p0001
  have p0003 := @g_f1orn A F
  have p0004 :=
    @g_sylanbrc (syn_wf1 F A B) (syn_wfn F A) (syn_wfun (syn_ccnv F))
      (syn_wf1o F A (syn_crn F)) p0000 p0002 p0003
  exact p0004

@[expose]
noncomputable def g_f1ocnvb (A : Class) (B : Class) (F : Class) :
    Nominal.NPrf (syn_wb (syn_wf1o F A B) (syn_wf1o (syn_ccnv F) B A)) :=
  by
  have p0000 := @g_cnvcnv F
  have p0001 := @g_fneq1i A (syn_ccnv (syn_ccnv F)) F p0000
  have p0002 :=
    @g_anbi2i (syn_wfn (syn_ccnv (syn_ccnv F)) A) (syn_wfn F A) (syn_wfn (syn_ccnv F) B)
      p0001
  have p0003 := @g_ancom (syn_wfn (syn_ccnv F) B) (syn_wfn F A)
  have p0004 :=
    @g_bitri (syn_wa (syn_wfn (syn_ccnv F) B) (syn_wfn (syn_ccnv (syn_ccnv F)) A))
      (syn_wa (syn_wfn (syn_ccnv F) B) (syn_wfn F A))
      (syn_wa (syn_wfn F A) (syn_wfn (syn_ccnv F) B)) p0002 p0003
  have p0005 := @g_dff1o4 B A (syn_ccnv F)
  have p0006 := @g_dff1o4 A B F
  have p0007 :=
    @g_n_3bitr4ri (syn_wa (syn_wfn (syn_ccnv F) B) (syn_wfn (syn_ccnv (syn_ccnv F)) A))
      (syn_wa (syn_wfn F A) (syn_wfn (syn_ccnv F) B)) (syn_wf1o (syn_ccnv F) B A)
      (syn_wf1o F A B) p0004 p0005 p0006
  exact p0007

@[expose]
noncomputable def g_f1ocnv (A : Class) (B : Class) (F : Class) :
    Nominal.NPrf (.imp (syn_wf1o F A B) (syn_wf1o (syn_ccnv F) B A)) :=
  by
  have p0000 := @g_f1ocnvb A B F
  have p0001 := @g_biimpi (syn_wf1o F A B) (syn_wf1o (syn_ccnv F) B A) p0000
  exact p0001

@[expose]
noncomputable def g_f1ores (A : Class) (B : Class) (C : Class) (F : Class) :
    Nominal.NPrf
      (.imp (syn_wa (syn_wf1 F A B) (syn_wss C A))
        (syn_wf1o (syn_cres F C) C (syn_cima F C))) :=
  by
  have p0000 := @g_ffun A B F
  have p0001 := @g_adantr (syn_wf F A B) (syn_wfun F) (syn_wss C A) p0000
  have p0002 := @g_fdm A B F
  have p0003 := @g_sseq2d (syn_wf F A B) (syn_cdm F) A C p0002
  have p0004 := @g_biimpar (syn_wf F A B) (syn_wss C (syn_cdm F)) (syn_wss C A) p0003
  have p0005 := @g_fores C F
  have p0006 :=
    @g_syl2anc (syn_wa (syn_wf F A B) (syn_wss C A)) (syn_wfun F) (syn_wss C (syn_cdm F))
      (syn_wfo (syn_cres F C) C (syn_cima F C)) p0001 p0004 p0005
  have p0007 := @g_funres11 C F
  have p0008 :=
    @g_anim12i (syn_wa (syn_wf F A B) (syn_wss C A))
      (syn_wfo (syn_cres F C) C (syn_cima F C)) (syn_wfun (syn_ccnv F))
      (syn_wfun (syn_ccnv (syn_cres F C))) p0006 p0007
  have p0009 :=
    @g_an32s (syn_wf F A B) (syn_wss C A) (syn_wfun (syn_ccnv F))
      (syn_wa (syn_wfo (syn_cres F C) C (syn_cima F C)) (syn_wfun (syn_ccnv (syn_cres F C))))
      p0008
  have p0010 := (Nominal.biimpRefl (syn_wf1 F A B))
  have p0011 :=
    @g_anbi1i (syn_wf1 F A B) (syn_wa (syn_wf F A B) (syn_wfun (syn_ccnv F)))
      (syn_wss C A) p0010
  have p0012 := @g_dff1o3 C (syn_cima F C) (syn_cres F C)
  have p0013 :=
    @g_n_3imtr4i (syn_wa (syn_wa (syn_wf F A B) (syn_wfun (syn_ccnv F))) (syn_wss C A))
      (syn_wa (syn_wfo (syn_cres F C) C (syn_cima F C)) (syn_wfun (syn_ccnv (syn_cres F C))))
      (syn_wa (syn_wf1 F A B) (syn_wss C A)) (syn_wf1o (syn_cres F C) C (syn_cima F C))
      p0009 p0011 p0012
  exact p0013

@[expose]
noncomputable def g_f1oun (A : Class) (B : Class) (C : Class) (D : Class) (F : Class)
    (G : Class) :
    Nominal.NPrf
      (.imp (syn_wa (syn_wa (syn_wf1o F A B) (syn_wf1o G C D))
          (syn_wa (.classEq (syn_cin A C) (syn_c0)) (.classEq (syn_cin B D) (syn_c0))))
        (syn_wf1o (syn_cun F G) (syn_cun A C) (syn_cun B D))) :=
  by
  have p0000 := @g_dff1o4 A B F
  have p0001 := @g_dff1o4 C D G
  have p0002 := @g_fnun A C F G
  have p0003 :=
    @g_ex (syn_wa (syn_wfn F A) (syn_wfn G C)) (.classEq (syn_cin A C) (syn_c0))
      (syn_wfn (syn_cun F G) (syn_cun A C)) p0002
  have p0004 := @g_fnun B D (syn_ccnv F) (syn_ccnv G)
  have p0005 := @g_cnvun F G
  have p0006 :=
    @g_fneq1i (syn_cun B D) (syn_ccnv (syn_cun F G)) (syn_cun (syn_ccnv F) (syn_ccnv G))
      p0005
  have p0007 :=
    @g_sylibr
      (syn_wa (syn_wa (syn_wfn (syn_ccnv F) B) (syn_wfn (syn_ccnv G) D))
        (.classEq (syn_cin B D) (syn_c0)))
      (syn_wfn (syn_cun (syn_ccnv F) (syn_ccnv G)) (syn_cun B D))
      (syn_wfn (syn_ccnv (syn_cun F G)) (syn_cun B D)) p0004 p0006
  have p0008 :=
    @g_ex (syn_wa (syn_wfn (syn_ccnv F) B) (syn_wfn (syn_ccnv G) D))
      (.classEq (syn_cin B D) (syn_c0)) (syn_wfn (syn_ccnv (syn_cun F G)) (syn_cun B D))
      p0007
  have p0009 :=
    @g_im2anan9 (syn_wa (syn_wfn F A) (syn_wfn G C)) (.classEq (syn_cin A C) (syn_c0))
      (syn_wfn (syn_cun F G) (syn_cun A C))
      (syn_wa (syn_wfn (syn_ccnv F) B) (syn_wfn (syn_ccnv G) D))
      (.classEq (syn_cin B D) (syn_c0)) (syn_wfn (syn_ccnv (syn_cun F G)) (syn_cun B D))
      p0003 p0008
  have p0010 :=
    @g_an4s (syn_wfn F A) (syn_wfn G C) (syn_wfn (syn_ccnv F) B) (syn_wfn (syn_ccnv G) D)
      (.imp (syn_wa (.classEq (syn_cin A C) (syn_c0)) (.classEq (syn_cin B D) (syn_c0)))
        (syn_wa (syn_wfn (syn_cun F G) (syn_cun A C))
          (syn_wfn (syn_ccnv (syn_cun F G)) (syn_cun B D))))
      p0009
  have p0011 :=
    @g_syl2anb (syn_wf1o F A B) (syn_wa (syn_wfn F A) (syn_wfn (syn_ccnv F) B))
      (syn_wa (syn_wfn G C) (syn_wfn (syn_ccnv G) D))
      (.imp (syn_wa (.classEq (syn_cin A C) (syn_c0)) (.classEq (syn_cin B D) (syn_c0)))
        (syn_wa (syn_wfn (syn_cun F G) (syn_cun A C))
          (syn_wfn (syn_ccnv (syn_cun F G)) (syn_cun B D))))
      (syn_wf1o G C D) p0000 p0001 p0010
  have p0012 := @g_dff1o4 (syn_cun A C) (syn_cun B D) (syn_cun F G)
  have p0013 :=
    @g_syl6ibr (syn_wa (syn_wf1o F A B) (syn_wf1o G C D))
      (syn_wa (.classEq (syn_cin A C) (syn_c0)) (.classEq (syn_cin B D) (syn_c0)))
      (syn_wa (syn_wfn (syn_cun F G) (syn_cun A C))
        (syn_wfn (syn_ccnv (syn_cun F G)) (syn_cun B D)))
      (syn_wf1o (syn_cun F G) (syn_cun A C) (syn_cun B D)) p0011 p0012
  have p0014 :=
    @g_imp (syn_wa (syn_wf1o F A B) (syn_wf1o G C D))
      (syn_wa (.classEq (syn_cin A C) (syn_c0)) (.classEq (syn_cin B D) (syn_c0)))
      (syn_wf1o (syn_cun F G) (syn_cun A C) (syn_cun B D)) p0013
  exact p0014

@[expose]
noncomputable def g_f1oco (A : Class) (B : Class) (C : Class) (F : Class) (G : Class) :
    Nominal.NPrf
      (.imp (syn_wa (syn_wf1o F B C) (syn_wf1o G A B)) (syn_wf1o (syn_ccom F G) A C)) :=
  by
  have p0000 := @g_f1co A B C F G
  have p0001 := @g_foco A B C F G
  have p0002 :=
    @g_anim12i (syn_wa (syn_wf1 F B C) (syn_wf1 G A B)) (syn_wf1 (syn_ccom F G) A C)
      (syn_wa (syn_wfo F B C) (syn_wfo G A B)) (syn_wfo (syn_ccom F G) A C) p0000 p0001
  have p0003 :=
    @g_an4s (syn_wf1 F B C) (syn_wf1 G A B) (syn_wfo F B C) (syn_wfo G A B)
      (syn_wa (syn_wf1 (syn_ccom F G) A C) (syn_wfo (syn_ccom F G) A C)) p0002
  have p0004 := (Nominal.biimpRefl (syn_wf1o F B C))
  have p0005 := (Nominal.biimpRefl (syn_wf1o G A B))
  have p0006 :=
    @g_anbi12i (syn_wf1o F B C) (syn_wa (syn_wf1 F B C) (syn_wfo F B C)) (syn_wf1o G A B)
      (syn_wa (syn_wf1 G A B) (syn_wfo G A B)) p0004 p0005
  have p0007 := (Nominal.biimpRefl (syn_wf1o (syn_ccom F G) A C))
  have p0008 :=
    @g_n_3imtr4i
      (syn_wa (syn_wa (syn_wf1 F B C) (syn_wfo F B C)) (syn_wa (syn_wf1 G A B) (syn_wfo G A B)))
      (syn_wa (syn_wf1 (syn_ccom F G) A C) (syn_wfo (syn_ccom F G) A C))
      (syn_wa (syn_wf1o F B C) (syn_wf1o G A B)) (syn_wf1o (syn_ccom F G) A C) p0003 p0006
      p0007
  exact p0008

@[expose]
noncomputable def g_f1ococnv2 (A : Class) (B : Class) (F : Class) :
    Nominal.NPrf
      (.imp (syn_wf1o F A B) (.classEq (syn_ccom F (syn_ccnv F)) (syn_cres (syn_cid) B))) :=
  by
  have p0000 := @g_f1ofun A B F
  have p0001 := (Nominal.biimpRefl (syn_wfun F))
  have p0002 := @g_iss (syn_ccom F (syn_ccnv F))
  have p0003 :=
    @g_bitri (syn_wfun F) (syn_wss (syn_ccom F (syn_ccnv F)) (syn_cid))
      (.classEq (syn_ccom F (syn_ccnv F))
        (syn_cres (syn_cid) (syn_cdm (syn_ccom F (syn_ccnv F)))))
      p0001 p0002
  have p0004 :=
    @g_sylib (syn_wf1o F A B) (syn_wfun F)
      (.classEq (syn_ccom F (syn_ccnv F))
        (syn_cres (syn_cid) (syn_cdm (syn_ccom F (syn_ccnv F)))))
      p0000 p0003
  have p0005 := (Nominal.classEqRefl (syn_cdm F))
  have p0006 := @g_dmcoeq F (syn_ccnv F)
  have p0007 := Nominal.mp p0005 p0006
  have p0008 := @g_dfrn4 F
  have p0009 :=
    @g_eqtr4i (syn_cdm (syn_ccom F (syn_ccnv F))) (syn_cdm (syn_ccnv F)) (syn_crn F) p0007
      p0008
  have p0010 := @g_f1ofo A B F
  have p0011 := @g_forn A B F
  have p0012 :=
    @g_syl (syn_wf1o F A B) (syn_wfo F A B) (.classEq (syn_crn F) B) p0010 p0011
  have p0013 :=
    @g_syl5eq (syn_wf1o F A B) (syn_cdm (syn_ccom F (syn_ccnv F))) (syn_crn F) B p0009
      p0012
  have p0014 :=
    @g_reseq2d (syn_wf1o F A B) (syn_cdm (syn_ccom F (syn_ccnv F))) B (syn_cid) p0013
  have p0015 :=
    @g_eqtrd (syn_wf1o F A B) (syn_ccom F (syn_ccnv F))
      (syn_cres (syn_cid) (syn_cdm (syn_ccom F (syn_ccnv F)))) (syn_cres (syn_cid) B)
      p0004 p0014
  exact p0015

@[expose]
noncomputable def g_f1ococnv1 (A : Class) (B : Class) (F : Class) :
    Nominal.NPrf
      (.imp (syn_wf1o F A B) (.classEq (syn_ccom (syn_ccnv F) F) (syn_cres (syn_cid) A))) :=
  by
  have p0000 := @g_cnvcnv F
  have p0001 := @g_coeq2i (syn_ccnv (syn_ccnv F)) F (syn_ccnv F) p0000
  have p0002 := @g_f1ocnv A B F
  have p0003 := @g_f1ococnv2 B A (syn_ccnv F)
  have p0004 :=
    @g_syl (syn_wf1o F A B) (syn_wf1o (syn_ccnv F) B A)
      (.classEq (syn_ccom (syn_ccnv F) (syn_ccnv (syn_ccnv F))) (syn_cres (syn_cid) A))
      p0002 p0003
  have p0005 :=
    @g_syl5eqr (syn_wf1o F A B) (syn_ccom (syn_ccnv F) F)
      (syn_ccom (syn_ccnv F) (syn_ccnv (syn_ccnv F))) (syn_cres (syn_cid) A) p0001 p0004
  exact p0005

@[expose]
noncomputable def g_f1cnv (A : Class) (B : Class) (F : Class) :
    Nominal.NPrf (.imp (syn_wf1 F A B) (syn_wf1o (syn_ccnv F) (syn_crn F) A)) :=
  by
  have p0000 := @g_f1f1orn A B F
  have p0001 := @g_f1ocnv A (syn_crn F) F
  have p0002 :=
    @g_syl (syn_wf1 F A B) (syn_wf1o F A (syn_crn F))
      (syn_wf1o (syn_ccnv F) (syn_crn F) A) p0000 p0001
  exact p0002

@[expose]
noncomputable def g_f10 (A : Class) : Nominal.NPrf (syn_wf1 (syn_c0) (syn_c0) A) :=
  by
  have p0000 := @g_f0 A
  have p0001 := @g_fun0
  have p0002 := @g_cnv0
  have p0003 := @g_funeqi (syn_ccnv (syn_c0)) (syn_c0) p0002
  have p0004 := @g_mpbir (syn_wfun (syn_ccnv (syn_c0))) (syn_wfun (syn_c0)) p0001 p0003
  have p0005 := (Nominal.biimpRefl (syn_wf1 (syn_c0) (syn_c0) A))
  have p0006 :=
    @g_mpbir2an (syn_wf1 (syn_c0) (syn_c0) A) (syn_wf (syn_c0) (syn_c0) A)
      (syn_wfun (syn_ccnv (syn_c0))) p0000 p0004 p0005
  exact p0006

@[expose]
noncomputable def g_f1o00 (A : Class) (F : Class) :
    Nominal.NPrf
      (syn_wb (syn_wf1o F (syn_c0) A) (syn_wa (.classEq F (syn_c0)) (.classEq A (syn_c0)))) :=
  by
  have p0000 := @g_dff1o4 (syn_c0) A F
  have p0001 := @g_fn0 F
  have p0002 := @g_biimpi (syn_wfn F (syn_c0)) (.classEq F (syn_c0)) p0001
  have p0003 :=
    @g_adantr (syn_wfn F (syn_c0)) (.classEq F (syn_c0)) (syn_wfn (syn_ccnv F) A) p0002
  have p0004 := @g_dm0
  have p0005 := @g_cnveq F (syn_c0)
  have p0006 := @g_cnv0
  have p0007 :=
    @g_syl6eq (.classEq F (syn_c0)) (syn_ccnv F) (syn_ccnv (syn_c0)) (syn_c0) p0005 p0006
  have p0008 :=
    @g_sylbi (syn_wfn F (syn_c0)) (.classEq F (syn_c0)) (.classEq (syn_ccnv F) (syn_c0))
      p0001 p0007
  have p0009 := @g_fneq1d (syn_wfn F (syn_c0)) A (syn_ccnv F) (syn_c0) p0008
  have p0010 :=
    @g_biimpa (syn_wfn F (syn_c0)) (syn_wfn (syn_ccnv F) A) (syn_wfn (syn_c0) A) p0009
  have p0011 := @g_fndm A (syn_c0)
  have p0012 :=
    @g_syl (syn_wa (syn_wfn F (syn_c0)) (syn_wfn (syn_ccnv F) A)) (syn_wfn (syn_c0) A)
      (.classEq (syn_cdm (syn_c0)) A) p0010 p0011
  have p0013 :=
    @g_syl5reqr (syn_wa (syn_wfn F (syn_c0)) (syn_wfn (syn_ccnv F) A)) (syn_c0)
      (syn_cdm (syn_c0)) A p0004 p0012
  have p0014 :=
    @g_jca (syn_wa (syn_wfn F (syn_c0)) (syn_wfn (syn_ccnv F) A)) (.classEq F (syn_c0))
      (.classEq A (syn_c0)) p0003 p0013
  have p0015 := @g_biimpri (syn_wfn F (syn_c0)) (.classEq F (syn_c0)) p0001
  have p0016 :=
    @g_adantr (.classEq F (syn_c0)) (syn_wfn F (syn_c0)) (.classEq A (syn_c0)) p0015
  have p0017 := @g_eqid (syn_c0)
  have p0018 := @g_fn0 (syn_c0)
  have p0019 :=
    @g_mpbir (syn_wfn (syn_c0) (syn_c0)) (.classEq (syn_c0) (syn_c0)) p0017 p0018
  have p0020 := @g_fneq1d (.classEq F (syn_c0)) A (syn_ccnv F) (syn_c0) p0007
  have p0021 := @g_fneq2 A (syn_c0) (syn_c0)
  have p0022 :=
    @g_sylan9bb (.classEq F (syn_c0)) (syn_wfn (syn_ccnv F) A) (syn_wfn (syn_c0) A)
      (.classEq A (syn_c0)) (syn_wfn (syn_c0) (syn_c0)) p0020 p0021
  have p0023 :=
    @g_mpbiri (syn_wa (.classEq F (syn_c0)) (.classEq A (syn_c0)))
      (syn_wfn (syn_ccnv F) A) (syn_wfn (syn_c0) (syn_c0)) p0019 p0022
  have p0024 :=
    @g_jca (syn_wa (.classEq F (syn_c0)) (.classEq A (syn_c0))) (syn_wfn F (syn_c0))
      (syn_wfn (syn_ccnv F) A) p0016 p0023
  have p0025 :=
    @g_impbii (syn_wa (syn_wfn F (syn_c0)) (syn_wfn (syn_ccnv F) A))
      (syn_wa (.classEq F (syn_c0)) (.classEq A (syn_c0))) p0014 p0024
  have p0026 :=
    @g_bitri (syn_wf1o F (syn_c0) A)
      (syn_wa (syn_wfn F (syn_c0)) (syn_wfn (syn_ccnv F) A))
      (syn_wa (.classEq F (syn_c0)) (.classEq A (syn_c0))) p0000 p0025
  exact p0026

@[expose]
noncomputable def g_f1o0 : Nominal.NPrf (syn_wf1o (syn_c0) (syn_c0) (syn_c0)) :=
  by
  have p0000 := @g_f10 (syn_c0)
  have p0001 := @g_fun0
  have p0002 := @g_dm0
  have p0003 := (Nominal.biimpRefl (syn_wfn (syn_c0) (syn_c0)))
  have p0004 :=
    @g_mpbir2an (syn_wfn (syn_c0) (syn_c0)) (syn_wfun (syn_c0))
      (.classEq (syn_cdm (syn_c0)) (syn_c0)) p0001 p0002 p0003
  have p0005 := @g_rn0
  have p0006 := (Nominal.biimpRefl (syn_wfo (syn_c0) (syn_c0) (syn_c0)))
  have p0007 :=
    @g_mpbir2an (syn_wfo (syn_c0) (syn_c0) (syn_c0)) (syn_wfn (syn_c0) (syn_c0))
      (.classEq (syn_crn (syn_c0)) (syn_c0)) p0004 p0005 p0006
  have p0008 := (Nominal.biimpRefl (syn_wf1o (syn_c0) (syn_c0) (syn_c0)))
  have p0009 :=
    @g_mpbir2an (syn_wf1o (syn_c0) (syn_c0) (syn_c0)) (syn_wf1 (syn_c0) (syn_c0) (syn_c0))
      (syn_wfo (syn_c0) (syn_c0) (syn_c0)) p0000 p0007 p0008
  exact p0009

@[expose]
noncomputable def g_f1oi (A : Class) :
    Nominal.NPrf (syn_wf1o (syn_cres (syn_cid) A) A A) :=
  by
  have p0000 := @g_fnresi A
  have p0001 := @g_cnvresid A
  have p0002 := @g_fneq1i A (syn_ccnv (syn_cres (syn_cid) A)) (syn_cres (syn_cid) A) p0001
  have p0003 :=
    @g_mpbir (syn_wfn (syn_ccnv (syn_cres (syn_cid) A)) A)
      (syn_wfn (syn_cres (syn_cid) A) A) p0000 p0002
  have p0004 := @g_dff1o4 A A (syn_cres (syn_cid) A)
  have p0005 :=
    @g_mpbir2an (syn_wf1o (syn_cres (syn_cid) A) A A) (syn_wfn (syn_cres (syn_cid) A) A)
      (syn_wfn (syn_ccnv (syn_cres (syn_cid) A)) A) p0000 p0003 p0004
  exact p0005

@[expose]
noncomputable def g_f1ovi : Nominal.NPrf (syn_wf1o (syn_cid) (syn_cvv) (syn_cvv)) :=
  by
  have p0000 := @g_funi
  have p0001 := @g_dmi
  have p0002 := (Nominal.biimpRefl (syn_wfn (syn_cid) (syn_cvv)))
  have p0003 :=
    @g_mpbir2an (syn_wfn (syn_cid) (syn_cvv)) (syn_wfun (syn_cid))
      (.classEq (syn_cdm (syn_cid)) (syn_cvv)) p0000 p0001 p0002
  have p0004 := @g_cnvi
  have p0005 := @g_fneq1i (syn_cvv) (syn_ccnv (syn_cid)) (syn_cid) p0004
  have p0006 :=
    @g_mpbir (syn_wfn (syn_ccnv (syn_cid)) (syn_cvv)) (syn_wfn (syn_cid) (syn_cvv)) p0003
      p0005
  have p0007 := @g_dff1o4 (syn_cvv) (syn_cvv) (syn_cid)
  have p0008 :=
    @g_mpbir2an (syn_wf1o (syn_cid) (syn_cvv) (syn_cvv)) (syn_wfn (syn_cid) (syn_cvv))
      (syn_wfn (syn_ccnv (syn_cid)) (syn_cvv)) p0003 p0006 p0007
  exact p0008

@[expose]
noncomputable def g_f1osn (A : Class) (B : Class)
    (hyp_f1osn_1 : Nominal.NPrf (.classMem A (syn_cvv)))
    (hyp_f1osn_2 : Nominal.NPrf (.classMem B (syn_cvv))) :
    Nominal.NPrf (syn_wf1o (syn_csn (syn_cop A B)) (syn_csn A) (syn_csn B)) :=
  by
  have p0000 := @g_fnsn A B hyp_f1osn_1 hyp_f1osn_2
  have p0001 := @g_fnsn B A hyp_f1osn_2 hyp_f1osn_1
  have p0002 := @g_cnvsn A B hyp_f1osn_1 hyp_f1osn_2
  have p0003 :=
    @g_fneq1i (syn_csn B) (syn_ccnv (syn_csn (syn_cop A B))) (syn_csn (syn_cop B A)) p0002
  have p0004 :=
    @g_mpbir (syn_wfn (syn_ccnv (syn_csn (syn_cop A B))) (syn_csn B))
      (syn_wfn (syn_csn (syn_cop B A)) (syn_csn B)) p0001 p0003
  have p0005 := @g_dff1o4 (syn_csn A) (syn_csn B) (syn_csn (syn_cop A B))
  have p0006 :=
    @g_mpbir2an (syn_wf1o (syn_csn (syn_cop A B)) (syn_csn A) (syn_csn B))
      (syn_wfn (syn_csn (syn_cop A B)) (syn_csn A))
      (syn_wfn (syn_ccnv (syn_csn (syn_cop A B))) (syn_csn B)) p0000 p0004 p0005
  exact p0006

@[expose]
noncomputable def g_f1osng (A : Class) (B : Class) (V : Class) (W : Class) :
    Nominal.NPrf
      (.imp (syn_wa (.classMem A V) (.classMem B W))
        (syn_wf1o (syn_csn (syn_cop A B)) (syn_csn A) (syn_csn B))) :=
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
    b ∉ ((syn_wf1o (syn_csn (syn_cop A B)) (syn_csn A) (syn_csn B))).fv :=
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
    a ∉ ((syn_wf1o (syn_csn (syn_cop A (.cv b))) (syn_csn A) (syn_csn (.cv b)))).fv :=
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
  have p0000 := @g_sneq (.cv a) A
  have p0001 :=
    @g_f1oeq2 (syn_csn (.cv a)) (syn_csn A) (syn_csn (.cv b))
      (syn_csn (syn_cop (.cv a) (.cv b)))
  have p0002 :=
    @g_syl (.classEq (.cv a) A) (.classEq (syn_csn (.cv a)) (syn_csn A))
      (syn_wb (syn_wf1o (syn_csn (syn_cop (.cv a) (.cv b))) (syn_csn (.cv a)) (syn_csn (.cv b)))
        (syn_wf1o (syn_csn (syn_cop (.cv a) (.cv b))) (syn_csn A) (syn_csn (.cv b))))
      p0000 p0001
  have p0003 := @g_opeq1 (.cv a) A (.cv b)
  have p0004 := @g_sneq (syn_cop (.cv a) (.cv b)) (syn_cop A (.cv b))
  have p0005 :=
    @g_f1oeq1 (syn_csn A) (syn_csn (.cv b)) (syn_csn (syn_cop (.cv a) (.cv b)))
      (syn_csn (syn_cop A (.cv b)))
  have p0006 :=
    @g_n_3syl (.classEq (.cv a) A)
      (.classEq (syn_cop (.cv a) (.cv b)) (syn_cop A (.cv b)))
      (.classEq (syn_csn (syn_cop (.cv a) (.cv b))) (syn_csn (syn_cop A (.cv b))))
      (syn_wb (syn_wf1o (syn_csn (syn_cop (.cv a) (.cv b))) (syn_csn A) (syn_csn (.cv b)))
        (syn_wf1o (syn_csn (syn_cop A (.cv b))) (syn_csn A) (syn_csn (.cv b))))
      p0003 p0004 p0005
  have p0007 :=
    @g_bitrd (.classEq (.cv a) A)
      (syn_wf1o (syn_csn (syn_cop (.cv a) (.cv b))) (syn_csn (.cv a)) (syn_csn (.cv b)))
      (syn_wf1o (syn_csn (syn_cop (.cv a) (.cv b))) (syn_csn A) (syn_csn (.cv b)))
      (syn_wf1o (syn_csn (syn_cop A (.cv b))) (syn_csn A) (syn_csn (.cv b))) p0002 p0006
  have p0008 := @g_sneq (.cv b) B
  have p0009 :=
    @g_f1oeq3 (syn_csn (.cv b)) (syn_csn B) (syn_csn A) (syn_csn (syn_cop A (.cv b)))
  have p0010 :=
    @g_syl (.classEq (.cv b) B) (.classEq (syn_csn (.cv b)) (syn_csn B))
      (syn_wb (syn_wf1o (syn_csn (syn_cop A (.cv b))) (syn_csn A) (syn_csn (.cv b)))
        (syn_wf1o (syn_csn (syn_cop A (.cv b))) (syn_csn A) (syn_csn B)))
      p0008 p0009
  have p0011 := @g_opeq2 (.cv b) B A
  have p0012 := @g_sneq (syn_cop A (.cv b)) (syn_cop A B)
  have p0013 :=
    @g_f1oeq1 (syn_csn A) (syn_csn B) (syn_csn (syn_cop A (.cv b)))
      (syn_csn (syn_cop A B))
  have p0014 :=
    @g_n_3syl (.classEq (.cv b) B) (.classEq (syn_cop A (.cv b)) (syn_cop A B))
      (.classEq (syn_csn (syn_cop A (.cv b))) (syn_csn (syn_cop A B)))
      (syn_wb (syn_wf1o (syn_csn (syn_cop A (.cv b))) (syn_csn A) (syn_csn B))
        (syn_wf1o (syn_csn (syn_cop A B)) (syn_csn A) (syn_csn B)))
      p0011 p0012 p0013
  have p0015 :=
    @g_bitrd (.classEq (.cv b) B)
      (syn_wf1o (syn_csn (syn_cop A (.cv b))) (syn_csn A) (syn_csn (.cv b)))
      (syn_wf1o (syn_csn (syn_cop A (.cv b))) (syn_csn A) (syn_csn B))
      (syn_wf1o (syn_csn (syn_cop A B)) (syn_csn A) (syn_csn B)) p0010 p0014
  have p0016 := @g_vex a
  have p0017 := @g_vex b
  have p0018 := @g_f1osn (.cv a) (.cv b) p0016 p0017
  have p0019 :=
    @g_vtocl2g
      (syn_wf1o (syn_csn (syn_cop (.cv a) (.cv b))) (syn_csn (.cv a)) (syn_csn (.cv b)))
      (syn_wf1o (syn_csn (syn_cop A (.cv b))) (syn_csn A) (syn_csn (.cv b)))
      (syn_wf1o (syn_csn (syn_cop A B)) (syn_csn A) (syn_csn B)) a b A B V W dv_cache_0001
      dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 p0007 p0015 p0018
  exact p0019

@[expose]
noncomputable def g_fv2 (x : Var) (y : Var) (A : Class) (F : Class) (dv_A_x : x ∉ A.fv)
    (dv_A_y : y ∉ A.fv) (dv_F_x : x ∉ F.fv) (dv_F_y : y ∉ F.fv) (dv_x_y : x ≠ y) :
    Nominal.NPrf
      (.classEq (syn_cfv F A)
        (syn_cuni (.cab x (.all y (syn_wb (syn_wbr A F (.cv y)) (.objEq y x)))))) :=
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
  have dv_cache_0003 : x ∉ ((syn_wbr A F (.cv y))).fv :=
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
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominal_df_fv y A F
      dv_cache_0001 dv_cache_0002
  have p0001 := @g_dfiota2 (syn_wbr A F (.cv y)) y x dv_cache_0003 dv_cache_0004
  have p0002 :=
    @g_eqtri (syn_cfv F A) (syn_cio y (syn_wbr A F (.cv y)))
      (syn_cuni (.cab x (.all y (syn_wb (syn_wbr A F (.cv y)) (.objEq y x))))) p0000 p0001
  exact p0002

@[expose]
noncomputable def g_fvprc (A : Class) (F : Class) :
    Nominal.NPrf
      (.imp (.neg (.classMem A (syn_cvv))) (.classEq (syn_cfv F A) (syn_c0))) :=
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
  have dv_cache_0003 : x ∉ ((Wff.classMem A (syn_cvv))).fv :=
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
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominal_df_fv x A F
      dv_cache_0001 dv_cache_0002
  have p0001 := @g_euex (syn_wbr A F (.cv x)) x
  have p0002 := @g_brex A (.cv x) F
  have p0003 :=
    @g_simpld (syn_wbr A F (.cv x)) (.classMem A (syn_cvv)) (.classMem (.cv x) (syn_cvv))
      p0002
  have p0004 :=
    @g_exlimiv (syn_wbr A F (.cv x)) (.classMem A (syn_cvv)) x dv_cache_0003 p0003
  have p0005 :=
    @g_syl (syn_weu x (syn_wbr A F (.cv x))) (syn_wex x (syn_wbr A F (.cv x)))
      (.classMem A (syn_cvv)) p0001 p0004
  have p0006 := @g_con3i (syn_weu x (syn_wbr A F (.cv x))) (.classMem A (syn_cvv)) p0005
  have p0007 := @g_iotanul (syn_wbr A F (.cv x)) x
  have p0008 :=
    @g_syl (.neg (.classMem A (syn_cvv))) (.neg (syn_weu x (syn_wbr A F (.cv x))))
      (.classEq (syn_cio x (syn_wbr A F (.cv x))) (syn_c0)) p0006 p0007
  have p0009 :=
    @g_syl5eq (.neg (.classMem A (syn_cvv))) (syn_cfv F A)
      (syn_cio x (syn_wbr A F (.cv x))) (syn_c0) p0000 p0008
  exact p0009

@[expose]
noncomputable def g_elfv (x : Var) (y : Var) (A : Class) (B : Class) (F : Class)
    (dv_A_x : x ∉ A.fv) (dv_B_x : x ∉ B.fv) (dv_B_y : y ∉ B.fv) (dv_F_x : x ∉ F.fv)
    (dv_F_y : y ∉ F.fv) (dv_x_y : x ≠ y) :
    Nominal.NPrf
      (syn_wb (.classMem A (syn_cfv F B)) (syn_wex x (syn_wa (.classMem A (.cv x))
            (.all y (syn_wb (syn_wbr B F (.cv y)) (.objEq y x)))))) :=
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
    @g_fv2 x y B F dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
  have p0001 :=
    @g_eleq2i (syn_cfv F B)
      (syn_cuni (.cab x (.all y (syn_wb (syn_wbr B F (.cv y)) (.objEq y x))))) A p0000
  have p0002 :=
    @g_eluniab (.all y (syn_wb (syn_wbr B F (.cv y)) (.objEq y x))) x A dv_cache_0006
  have p0003 :=
    @g_bitri (.classMem A (syn_cfv F B))
      (.classMem A (syn_cuni (.cab x (.all y (syn_wb (syn_wbr B F (.cv y)) (.objEq y x))))))
      (syn_wex x (syn_wa (.classMem A (.cv x))
          (.all y (syn_wb (syn_wbr B F (.cv y)) (.objEq y x)))))
      p0001 p0002
  exact p0003

@[expose]
noncomputable def g_fveq1 (A : Class) (F : Class) (G : Class) :
    Nominal.NPrf (.imp (.classEq F G) (.classEq (syn_cfv F A) (syn_cfv G A))) :=
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
  have p0000 := @g_breq A (.cv x) F G
  have p0001 :=
    @g_iotabidv (.classEq F G) (syn_wbr A F (.cv x)) (syn_wbr A G (.cv x)) x dv_cache_0001
      p0000
  have p0002 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominal_df_fv x A F
      dv_cache_0002 dv_cache_0003
  have p0003 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominal_df_fv x A G
      dv_cache_0002 dv_cache_0004
  have p0004 :=
    @g_n_3eqtr4g (.classEq F G) (syn_cio x (syn_wbr A F (.cv x)))
      (syn_cio x (syn_wbr A G (.cv x))) (syn_cfv F A) (syn_cfv G A) p0001 p0002 p0003
  exact p0004

@[expose]
noncomputable def g_fveq2 (A : Class) (B : Class) (F : Class) :
    Nominal.NPrf (.imp (.classEq A B) (.classEq (syn_cfv F A) (syn_cfv F B))) :=
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
  have p0000 := @g_breq1 A B (.cv x) F
  have p0001 :=
    @g_iotabidv (.classEq A B) (syn_wbr A F (.cv x)) (syn_wbr B F (.cv x)) x dv_cache_0001
      p0000
  have p0002 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominal_df_fv x A F
      dv_cache_0002 dv_cache_0003
  have p0003 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominal_df_fv x B F
      dv_cache_0004 dv_cache_0003
  have p0004 :=
    @g_n_3eqtr4g (.classEq A B) (syn_cio x (syn_wbr A F (.cv x)))
      (syn_cio x (syn_wbr B F (.cv x))) (syn_cfv F A) (syn_cfv F B) p0001 p0002 p0003
  exact p0004

@[expose]
noncomputable def g_fveq1i (A : Class) (F : Class) (G : Class)
    (hyp_fveq1i_1 : Nominal.NPrf (.classEq F G)) :
    Nominal.NPrf (.classEq (syn_cfv F A) (syn_cfv G A)) :=
  by
  have p0000 := @g_fveq1 A F G
  have p0001 := Nominal.mp hyp_fveq1i_1 p0000
  exact p0001

@[expose]
noncomputable def g_fveq1d (ph : Wff) (A : Class) (F : Class) (G : Class)
    (hyp_fveq1d_1 : Nominal.NPrf (.imp ph (.classEq F G))) :
    Nominal.NPrf (.imp ph (.classEq (syn_cfv F A) (syn_cfv G A))) :=
  by
  have p0000 := @g_fveq1 A F G
  have p0001 :=
    @g_syl ph (.classEq F G) (.classEq (syn_cfv F A) (syn_cfv G A)) hyp_fveq1d_1 p0000
  exact p0001

@[expose]
noncomputable def g_fveq2i (A : Class) (B : Class) (F : Class)
    (hyp_fveq2i_1 : Nominal.NPrf (.classEq A B)) :
    Nominal.NPrf (.classEq (syn_cfv F A) (syn_cfv F B)) :=
  by
  have p0000 := @g_fveq2 A B F
  have p0001 := Nominal.mp hyp_fveq2i_1 p0000
  exact p0001

@[expose]
noncomputable def g_fveq2d (ph : Wff) (A : Class) (B : Class) (F : Class)
    (hyp_fveq2d_1 : Nominal.NPrf (.imp ph (.classEq A B))) :
    Nominal.NPrf (.imp ph (.classEq (syn_cfv F A) (syn_cfv F B))) :=
  by
  have p0000 := @g_fveq2 A B F
  have p0001 :=
    @g_syl ph (.classEq A B) (.classEq (syn_cfv F A) (syn_cfv F B)) hyp_fveq2d_1 p0000
  exact p0001

@[expose]
noncomputable def g_fvex (A : Class) (F : Class) :
    Nominal.NPrf (.classMem (syn_cfv F A) (syn_cvv)) :=
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
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominal_df_fv x A F
      dv_cache_0001 dv_cache_0002
  have p0001 := @g_iotaex (syn_wbr A F (.cv x)) x
  have p0002 :=
    @g_eqeltri (syn_cfv F A) (syn_cio x (syn_wbr A F (.cv x))) (syn_cvv) p0000 p0001
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

@[expose]
noncomputable def g_fv3 (x : Var) (y : Var) (A : Class) (F : Class) (dv_A_x : x ∉ A.fv)
    (dv_A_y : y ∉ A.fv) (dv_F_x : x ∉ F.fv) (dv_F_y : y ∉ F.fv) (dv_x_y : x ≠ y) :
    Nominal.NPrf
      (.classEq (syn_cfv F A) (.cab x
          (syn_wa (syn_wex y (syn_wa (.classMem (.cv x) (.cv y)) (syn_wbr A F (.cv y))))
            (syn_weu y (syn_wbr A F (.cv y)))))) :=
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
  have dv_cache_0008 : y ∉ ((syn_wbr A F (.cv z))).fv :=
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
    y ∉ ((syn_wa (.classMem (.cv x) (.cv z)) (syn_wbr A F (.cv z)))).fv :=
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
    z ∉ ((syn_wa (.classMem (.cv x) (.cv y)) (syn_wbr A F (.cv y)))).fv :=
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
  have dv_cache_0012 : z ∉ ((syn_wbr A F (.cv y))).fv :=
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
  have dv_cache_0014 : x ∉ ((syn_cfv F A)).fv :=
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
    @g_elfv z y (.cv x) A F dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
      dv_cache_0005 dv_cache_0006
  have p0001 := @g_bi2 (syn_wbr A F (.cv y)) (.classEq (.cv y) (.cv z))
  have p0002 :=
    @g_alimi (syn_wb (syn_wbr A F (.cv y)) (.classEq (.cv y) (.cv z)))
      (.imp (.classEq (.cv y) (.cv z)) (syn_wbr A F (.cv y))) y p0001
  have p0003 := @g_vex z
  have p0004 := @g_breq2 (.cv y) (.cv z) A F
  have p0005 :=
    @g_ceqsalv (syn_wbr A F (.cv y)) (syn_wbr A F (.cv z)) y (.cv z) dv_cache_0007
      dv_cache_0008 p0003 p0004
  have p0006 :=
    @g_sylib (.all y (syn_wb (syn_wbr A F (.cv y)) (.classEq (.cv y) (.cv z))))
      (.all y (.imp (.classEq (.cv y) (.cv z)) (syn_wbr A F (.cv y))))
      (syn_wbr A F (.cv z)) p0002 p0005
  have p0007 :=
    @g_anim2i (.all y (syn_wb (syn_wbr A F (.cv y)) (.classEq (.cv y) (.cv z))))
      (syn_wbr A F (.cv z)) (.classMem (.cv x) (.cv z)) p0006
  have p0008 :=
    @g_eximi
      (syn_wa (.classMem (.cv x) (.cv z))
        (.all y (syn_wb (syn_wbr A F (.cv y)) (.classEq (.cv y) (.cv z)))))
      (syn_wa (.classMem (.cv x) (.cv z)) (syn_wbr A F (.cv z))) z p0007
  have p0009 := @g_elequ2 z y x
  have p0010 := @g_breq2 (.cv z) (.cv y) A F
  have p0011_e00_recanon :
    Nominal.NPrf
      (.imp (.classEq (.cv z) (.cv y))
        (syn_wb (.classMem (.cv x) (.cv z)) (.classMem (.cv x) (.cv y)))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wb
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
    @g_anbi12d (.classEq (.cv z) (.cv y)) (.classMem (.cv x) (.cv z))
      (.classMem (.cv x) (.cv y)) (syn_wbr A F (.cv z)) (syn_wbr A F (.cv y))
      p0011_e00_recanon p0010
  have p0012_e00_recanon :
    Nominal.NPrf
      (.imp (.objEq z y) (syn_wb (syn_wa (.classMem (.cv x) (.cv z)) (syn_wbr A F (.cv z)))
          (syn_wa (.classMem (.cv x) (.cv y)) (syn_wbr A F (.cv y))))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wb syn_wa syn_wbr syn_cop syn_cun syn_cnin syn_wnan syn_ccompl syn_wrex
          syn_wex syn_cphi
        simp (config :=
          { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_class_cv]
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
        · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0011
  have p0012 :=
    @g_cbvexv (syn_wa (.classMem (.cv x) (.cv z)) (syn_wbr A F (.cv z)))
      (syn_wa (.classMem (.cv x) (.cv y)) (syn_wbr A F (.cv y))) z y dv_cache_0009
      dv_cache_0010 p0012_e00_recanon
  have p0013 :=
    @g_sylib
      (syn_wex z (syn_wa (.classMem (.cv x) (.cv z))
          (.all y (syn_wb (syn_wbr A F (.cv y)) (.classEq (.cv y) (.cv z))))))
      (syn_wex z (syn_wa (.classMem (.cv x) (.cv z)) (syn_wbr A F (.cv z))))
      (syn_wex y (syn_wa (.classMem (.cv x) (.cv y)) (syn_wbr A F (.cv y)))) p0008 p0012
  have p0014 :=
    @g_n_19_40 (.classMem (.cv x) (.cv z))
      (.all y (syn_wb (syn_wbr A F (.cv y)) (.classEq (.cv y) (.cv z)))) z
  have p0015 :=
    @g_simprd
      (syn_wex z (syn_wa (.classMem (.cv x) (.cv z))
          (.all y (syn_wb (syn_wbr A F (.cv y)) (.classEq (.cv y) (.cv z))))))
      (syn_wex z (.classMem (.cv x) (.cv z)))
      (syn_wex z (.all y (syn_wb (syn_wbr A F (.cv y)) (.classEq (.cv y) (.cv z))))) p0014
  have p0016 := Nominal.dfEu y z (syn_wbr A F (.cv y)) dv_cache_0011 dv_cache_0012
  have p0017_e01_recanon :
    Nominal.NPrf
      (syn_wb (syn_weu y (syn_wbr A F (.cv y)))
        (syn_wex z (.all y (syn_wb (syn_wbr A F (.cv y)) (.classEq (.cv y) (.cv z)))))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wb syn_weu syn_wex syn_wbr syn_cop syn_cun syn_cnin syn_wnan syn_wa
          syn_ccompl syn_wrex syn_cphi
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
    @g_sylibr
      (syn_wex z (syn_wa (.classMem (.cv x) (.cv z))
          (.all y (syn_wb (syn_wbr A F (.cv y)) (.classEq (.cv y) (.cv z))))))
      (syn_wex z (.all y (syn_wb (syn_wbr A F (.cv y)) (.classEq (.cv y) (.cv z)))))
      (syn_weu y (syn_wbr A F (.cv y))) p0015 p0017_e01_recanon
  have p0018 :=
    @g_jca
      (syn_wex z (syn_wa (.classMem (.cv x) (.cv z))
          (.all y (syn_wb (syn_wbr A F (.cv y)) (.classEq (.cv y) (.cv z))))))
      (syn_wex y (syn_wa (.classMem (.cv x) (.cv y)) (syn_wbr A F (.cv y))))
      (syn_weu y (syn_wbr A F (.cv y))) p0013 p0017
  have p0019 := @g_nfeu1 (syn_wbr A F (.cv y)) y
  have p0020 := @g_nfv (.classMem (.cv x) (.cv z)) y dv_cache_0013
  have p0021 := @g_nfa1 (syn_wb (syn_wbr A F (.cv y)) (.classEq (.cv y) (.cv z))) y
  have p0022 :=
    @g_nfan (.classMem (.cv x) (.cv z))
      (.all y (syn_wb (syn_wbr A F (.cv y)) (.classEq (.cv y) (.cv z)))) y p0020 p0021
  have p0023 :=
    @g_nfex
      (syn_wa (.classMem (.cv x) (.cv z))
        (.all y (syn_wb (syn_wbr A F (.cv y)) (.classEq (.cv y) (.cv z)))))
      y z p0022
  have p0024 :=
    @g_nfim (syn_weu y (syn_wbr A F (.cv y)))
      (syn_wex z (syn_wa (.classMem (.cv x) (.cv z))
          (.all y (syn_wb (syn_wbr A F (.cv y)) (.classEq (.cv y) (.cv z))))))
      y p0019 p0023
  have p0025 := @g_bi1 (syn_wbr A F (.cv y)) (.classEq (.cv y) (.cv z))
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
    @g_syl6 (syn_wb (syn_wbr A F (.cv y)) (.classEq (.cv y) (.cv z)))
      (syn_wbr A F (.cv y)) (.classEq (.cv y) (.cv z))
      (.imp (.classMem (.cv x) (.cv y)) (.classMem (.cv x) (.cv z))) p0025
      p0027_e01_recanon
  have p0028 :=
    @g_com23 (syn_wb (syn_wbr A F (.cv y)) (.classEq (.cv y) (.cv z)))
      (syn_wbr A F (.cv y)) (.classMem (.cv x) (.cv y)) (.classMem (.cv x) (.cv z)) p0027
  have p0029 :=
    @g_imp3a (syn_wb (syn_wbr A F (.cv y)) (.classEq (.cv y) (.cv z)))
      (.classMem (.cv x) (.cv y)) (syn_wbr A F (.cv y)) (.classMem (.cv x) (.cv z)) p0028
  have p0030 :=
    @g_sps (syn_wb (syn_wbr A F (.cv y)) (.classEq (.cv y) (.cv z)))
      (.imp (syn_wa (.classMem (.cv x) (.cv y)) (syn_wbr A F (.cv y)))
        (.classMem (.cv x) (.cv z)))
      y p0029
  have p0031 :=
    @g_anc2ri (.all y (syn_wb (syn_wbr A F (.cv y)) (.classEq (.cv y) (.cv z))))
      (syn_wa (.classMem (.cv x) (.cv y)) (syn_wbr A F (.cv y)))
      (.classMem (.cv x) (.cv z)) p0030
  have p0032 :=
    @g_com12 (.all y (syn_wb (syn_wbr A F (.cv y)) (.classEq (.cv y) (.cv z))))
      (syn_wa (.classMem (.cv x) (.cv y)) (syn_wbr A F (.cv y)))
      (syn_wa (.classMem (.cv x) (.cv z))
        (.all y (syn_wb (syn_wbr A F (.cv y)) (.classEq (.cv y) (.cv z)))))
      p0031
  have p0033 :=
    @g_eximdv (syn_wa (.classMem (.cv x) (.cv y)) (syn_wbr A F (.cv y)))
      (.all y (syn_wb (syn_wbr A F (.cv y)) (.classEq (.cv y) (.cv z))))
      (syn_wa (.classMem (.cv x) (.cv z))
        (.all y (syn_wb (syn_wbr A F (.cv y)) (.classEq (.cv y) (.cv z)))))
      z dv_cache_0010 p0032
  have p0034_e00_recanon :
    Nominal.NPrf
      (syn_wb (syn_weu y (syn_wbr A F (.cv y)))
        (syn_wex z (.all y (syn_wb (syn_wbr A F (.cv y)) (.classEq (.cv y) (.cv z)))))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wb syn_weu syn_wex syn_wbr syn_cop syn_cun syn_cnin syn_wnan syn_wa
          syn_ccompl syn_wrex syn_cphi
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
    @g_syl5bi (syn_weu y (syn_wbr A F (.cv y)))
      (syn_wex z (.all y (syn_wb (syn_wbr A F (.cv y)) (.classEq (.cv y) (.cv z)))))
      (syn_wa (.classMem (.cv x) (.cv y)) (syn_wbr A F (.cv y)))
      (syn_wex z (syn_wa (.classMem (.cv x) (.cv z))
          (.all y (syn_wb (syn_wbr A F (.cv y)) (.classEq (.cv y) (.cv z))))))
      p0034_e00_recanon p0033
  have p0035 :=
    @g_exlimi (syn_wa (.classMem (.cv x) (.cv y)) (syn_wbr A F (.cv y)))
      (.imp (syn_weu y (syn_wbr A F (.cv y))) (syn_wex z (syn_wa (.classMem (.cv x) (.cv z))
            (.all y (syn_wb (syn_wbr A F (.cv y)) (.classEq (.cv y) (.cv z)))))))
      y p0024 p0034
  have p0036 :=
    @g_imp (syn_wex y (syn_wa (.classMem (.cv x) (.cv y)) (syn_wbr A F (.cv y))))
      (syn_weu y (syn_wbr A F (.cv y)))
      (syn_wex z (syn_wa (.classMem (.cv x) (.cv z))
          (.all y (syn_wb (syn_wbr A F (.cv y)) (.classEq (.cv y) (.cv z))))))
      p0035
  have p0037 :=
    @g_impbii
      (syn_wex z (syn_wa (.classMem (.cv x) (.cv z))
          (.all y (syn_wb (syn_wbr A F (.cv y)) (.classEq (.cv y) (.cv z))))))
      (syn_wa (syn_wex y (syn_wa (.classMem (.cv x) (.cv y)) (syn_wbr A F (.cv y))))
        (syn_weu y (syn_wbr A F (.cv y))))
      p0018 p0036
  have p0038_e00_recanon :
    Nominal.NPrf
      (syn_wb (.classMem (.cv x) (syn_cfv F A)) (syn_wex z (syn_wa (.classMem (.cv x) (.cv z))
            (.all y (syn_wb (syn_wbr A F (.cv y)) (.classEq (.cv y) (.cv z))))))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wb syn_cfv syn_cio syn_cuni syn_wex syn_wa syn_csn syn_wbr syn_cop
          syn_cun syn_cnin syn_wnan syn_ccompl syn_wrex syn_cphi
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
    @g_bitri (.classMem (.cv x) (syn_cfv F A))
      (syn_wex z (syn_wa (.classMem (.cv x) (.cv z))
          (.all y (syn_wb (syn_wbr A F (.cv y)) (.classEq (.cv y) (.cv z))))))
      (syn_wa (syn_wex y (syn_wa (.classMem (.cv x) (.cv y)) (syn_wbr A F (.cv y))))
        (syn_weu y (syn_wbr A F (.cv y))))
      p0038_e00_recanon p0037
  have p0039 :=
    @g_eqabi
      (syn_wa (syn_wex y (syn_wa (.classMem (.cv x) (.cv y)) (syn_wbr A F (.cv y))))
        (syn_weu y (syn_wbr A F (.cv y))))
      x (syn_cfv F A) dv_cache_0014 p0038
  exact p0039

@[expose]
noncomputable def g_fvres (A : Class) (B : Class) (F : Class) :
    Nominal.NPrf
      (.imp (.classMem A B) (.classEq (syn_cfv (syn_cres F B) A) (syn_cfv F A))) :=
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
  have dv_cache_0003 : x ∉ ((syn_cres F B)).fv :=
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
  have p0000 := @g_iba (.classMem A B) (syn_wbr A F (.cv x))
  have p0001 := @g_brres A (.cv x) F B
  have p0002 :=
    @g_syl6rbbr (.classMem A B) (syn_wbr A F (.cv x))
      (syn_wa (syn_wbr A F (.cv x)) (.classMem A B)) (syn_wbr A (syn_cres F B) (.cv x))
      p0000 p0001
  have p0003 :=
    @g_iotabidv (.classMem A B) (syn_wbr A (syn_cres F B) (.cv x)) (syn_wbr A F (.cv x)) x
      dv_cache_0001 p0002
  have p0004 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominal_df_fv x A
      (syn_cres F B) dv_cache_0002 dv_cache_0003
  have p0005 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominal_df_fv x A F
      dv_cache_0002 dv_cache_0004
  have p0006 :=
    @g_n_3eqtr4g (.classMem A B) (syn_cio x (syn_wbr A (syn_cres F B) (.cv x)))
      (syn_cio x (syn_wbr A F (.cv x))) (syn_cfv (syn_cres F B) A) (syn_cfv F A) p0003
      p0004 p0005
  exact p0006

@[expose]
noncomputable def g_funssfv (A : Class) (F : Class) (G : Class) :
    Nominal.NPrf
      (.imp (syn_w3a (syn_wfun F) (syn_wss G F) (.classMem A (syn_cdm G)))
        (.classEq (syn_cfv F A) (syn_cfv G A))) :=
  by
  have p0000 := @g_fvres A (syn_cdm G) F
  have p0001 :=
    @g_eqcomd (.classMem A (syn_cdm G)) (syn_cfv (syn_cres F (syn_cdm G)) A) (syn_cfv F A)
      p0000
  have p0002 := @g_funssres F G
  have p0003 :=
    @g_fveq1d (syn_wa (syn_wfun F) (syn_wss G F)) A (syn_cres F (syn_cdm G)) G p0002
  have p0004 :=
    @g_sylan9eqr (.classMem A (syn_cdm G)) (syn_wa (syn_wfun F) (syn_wss G F))
      (syn_cfv F A) (syn_cfv (syn_cres F (syn_cdm G)) A) (syn_cfv G A) p0001 p0003
  have p0005 :=
    @g_n_3impa (syn_wfun F) (syn_wss G F) (.classMem A (syn_cdm G))
      (.classEq (syn_cfv F A) (syn_cfv G A)) p0004
  exact p0005

@[expose]
noncomputable def g_tz6_12_1 (y : Var) (A : Class) (B : Class) (F : Class)
    (dv_A_y : y ∉ A.fv) (dv_F_y : y ∉ F.fv) :
    Nominal.NPrf
      (.imp (syn_wa (syn_wbr A F B) (syn_weu y (syn_wbr A F (.cv y))))
        (.classEq (syn_cfv F A) B)) :=
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
  have dv_cache_0001 : x ∉ ((syn_wbr A F (.cv y))).fv := by
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
  have dv_cache_0002 : y ∉ ((syn_wbr A F (.cv x))).fv :=
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
  have dv_cache_0006 : x ∉ ((syn_wbr A F B)).fv :=
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
  have p0000 := @g_nfv (syn_wbr A F (.cv y)) x dv_cache_0001
  have p0001 := @g_nfv (syn_wbr A F (.cv x)) y dv_cache_0002
  have p0002 := @g_breq2 (.cv y) (.cv x) A F
  have p0003_e02_recanon :
    Nominal.NPrf
      (.imp (.objEq y x) (syn_wb (syn_wbr A F (.cv y)) (syn_wbr A F (.cv x)))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wb syn_wbr syn_cop syn_cun syn_cnin syn_wnan syn_wa syn_ccompl syn_wrex
          syn_wex syn_cphi
        simp (config :=
          { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_class_cv]
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
        · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0002
  have p0003 :=
    @g_cbveu (syn_wbr A F (.cv y)) (syn_wbr A F (.cv x)) y x p0000 p0001 p0003_e02_recanon
  have p0004 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominal_df_fv x A F
      dv_cache_0003 dv_cache_0004
  have p0005 := @g_brrelrnex A B F
  have p0006 :=
    @g_adantr (syn_wbr A F B) (.classMem B (syn_cvv)) (syn_weu x (syn_wbr A F (.cv x)))
      p0005
  have p0007 := @g_breq2 (.cv x) B A F
  have p0008 :=
    @g_iota2 (syn_wbr A F (.cv x)) (syn_wbr A F B) x B (syn_cvv) dv_cache_0005
      dv_cache_0006 p0007
  have p0009 :=
    @g_biimpd (syn_wa (.classMem B (syn_cvv)) (syn_weu x (syn_wbr A F (.cv x))))
      (syn_wbr A F B) (.classEq (syn_cio x (syn_wbr A F (.cv x))) B) p0008
  have p0010 :=
    @g_ex (.classMem B (syn_cvv)) (syn_weu x (syn_wbr A F (.cv x)))
      (.imp (syn_wbr A F B) (.classEq (syn_cio x (syn_wbr A F (.cv x))) B)) p0009
  have p0011 :=
    @g_com23 (.classMem B (syn_cvv)) (syn_weu x (syn_wbr A F (.cv x))) (syn_wbr A F B)
      (.classEq (syn_cio x (syn_wbr A F (.cv x))) B) p0010
  have p0012 :=
    @g_imp3a (.classMem B (syn_cvv)) (syn_wbr A F B) (syn_weu x (syn_wbr A F (.cv x)))
      (.classEq (syn_cio x (syn_wbr A F (.cv x))) B) p0011
  have p0013 :=
    @g_mpcom (.classMem B (syn_cvv))
      (syn_wa (syn_wbr A F B) (syn_weu x (syn_wbr A F (.cv x))))
      (.classEq (syn_cio x (syn_wbr A F (.cv x))) B) p0006 p0012
  have p0014 :=
    @g_syl5eq (syn_wa (syn_wbr A F B) (syn_weu x (syn_wbr A F (.cv x)))) (syn_cfv F A)
      (syn_cio x (syn_wbr A F (.cv x))) B p0004 p0013
  have p0015 :=
    @g_sylan2b (syn_weu y (syn_wbr A F (.cv y))) (syn_wbr A F B)
      (syn_weu x (syn_wbr A F (.cv x))) (.classEq (syn_cfv F A) B) p0003 p0014
  exact p0015

@[expose]
noncomputable def g_tz6_12_2 (y : Var) (A : Class) (F : Class) (dv_A_y : y ∉ A.fv)
    (dv_F_y : y ∉ F.fv) :
    Nominal.NPrf
      (.imp (.neg (syn_weu y (syn_wbr A F (.cv y)))) (.classEq (syn_cfv F A) (syn_c0))) :=
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
      ((syn_wa (syn_wex y (syn_wa (.objMem z y) (syn_wbr A F (.cv y))))
          (syn_weu y (syn_wbr A F (.cv y))))).fv :=
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
      ((Class.cab x (syn_wa (syn_wex y (syn_wa (.objMem x y) (syn_wbr A F (.cv y))))
            (syn_weu y (syn_wbr A F (.cv y)))))).fv :=
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
  have dv_cache_0010 : z ∉ ((Wff.neg (syn_weu y (syn_wbr A F (.cv y))))).fv :=
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
    @g_fv3 x y A F dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
  have p0001 := @g_vex z
  have p0002 := @g_elequ1 x z y
  have p0003 :=
    @g_anbi1d (.objEq x z) (.objMem x y) (.objMem z y) (syn_wbr A F (.cv y)) p0002
  have p0004 :=
    @g_exbidv (.objEq x z) (syn_wa (.objMem x y) (syn_wbr A F (.cv y)))
      (syn_wa (.objMem z y) (syn_wbr A F (.cv y))) y dv_cache_0006 p0003
  have p0005 :=
    @g_anbi1d (.objEq x z) (syn_wex y (syn_wa (.objMem x y) (syn_wbr A F (.cv y))))
      (syn_wex y (syn_wa (.objMem z y) (syn_wbr A F (.cv y))))
      (syn_weu y (syn_wbr A F (.cv y))) p0004
  have p0006_e01_recanon :
    Nominal.NPrf
      (.imp (.classEq (.cv x) (.cv z)) (syn_wb
          (syn_wa (syn_wex y (syn_wa (.objMem x y) (syn_wbr A F (.cv y))))
            (syn_weu y (syn_wbr A F (.cv y))))
          (syn_wa (syn_wex y (syn_wa (.objMem z y) (syn_wbr A F (.cv y))))
            (syn_weu y (syn_wbr A F (.cv y)))))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wb syn_wa syn_wex syn_weu syn_wbr syn_cop syn_cun syn_cnin syn_wnan
          syn_ccompl syn_wrex syn_cphi
        simp (config :=
          { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_class_cv]
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · exact Nominal.RecanonTransportDev.TRecanonWff.objEq_classEq _ _
        · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0005
  have p0006 :=
    @g_elab
      (syn_wa (syn_wex y (syn_wa (.objMem x y) (syn_wbr A F (.cv y))))
        (syn_weu y (syn_wbr A F (.cv y))))
      (syn_wa (syn_wex y (syn_wa (.objMem z y) (syn_wbr A F (.cv y))))
        (syn_weu y (syn_wbr A F (.cv y))))
      x (.cv z) dv_cache_0007 dv_cache_0008 p0001 p0006_e01_recanon
  have p0007 :=
    @g_simprbi
      (.classMem (.cv z) (.cab x
          (syn_wa (syn_wex y (syn_wa (.objMem x y) (syn_wbr A F (.cv y))))
            (syn_weu y (syn_wbr A F (.cv y))))))
      (syn_wex y (syn_wa (.objMem z y) (syn_wbr A F (.cv y))))
      (syn_weu y (syn_wbr A F (.cv y))) p0006
  have p0008 :=
    @g_con3i
      (.classMem (.cv z) (.cab x
          (syn_wa (syn_wex y (syn_wa (.objMem x y) (syn_wbr A F (.cv y))))
            (syn_weu y (syn_wbr A F (.cv y))))))
      (syn_weu y (syn_wbr A F (.cv y))) p0007
  have p0009 :=
    @g_eq0rdv (.neg (syn_weu y (syn_wbr A F (.cv y)))) z
      (.cab x (syn_wa (syn_wex y (syn_wa (.objMem x y) (syn_wbr A F (.cv y))))
          (syn_weu y (syn_wbr A F (.cv y)))))
      dv_cache_0009 dv_cache_0010 p0008
  have p0010_e00_recanon :
    Nominal.NPrf
      (.classEq (syn_cfv F A) (.cab x
          (syn_wa (syn_wex y (syn_wa (.objMem x y) (syn_wbr A F (.cv y))))
            (syn_weu y (syn_wbr A F (.cv y)))))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_cfv syn_cio syn_cuni syn_wex syn_wa syn_csn syn_wbr syn_cop syn_cun
          syn_cnin syn_wnan syn_ccompl syn_wrex syn_cphi
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
    @g_syl5eq (.neg (syn_weu y (syn_wbr A F (.cv y)))) (syn_cfv F A)
      (.cab x (syn_wa (syn_wex y (syn_wa (.objMem x y) (syn_wbr A F (.cv y))))
          (syn_weu y (syn_wbr A F (.cv y)))))
      (syn_c0) p0010_e00_recanon p0009
  exact p0010

@[expose]
noncomputable def g_tz6_12c (y : Var) (A : Class) (B : Class) (F : Class)
    (dv_A_y : y ∉ A.fv) (dv_F_y : y ∉ F.fv) :
    Nominal.NPrf
      (.imp (syn_weu y (syn_wbr A F (.cv y)))
        (syn_wb (.classEq (syn_cfv F A) B) (syn_wbr A F B))) :=
  by
  have dv_cache_0001 : y ∉ ((syn_wbr A F (syn_cfv F A))).fv := by
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
  have p0000 := @g_euex (syn_wbr A F (.cv y)) y
  have p0001 := @g_nfeu1 (syn_wbr A F (.cv y)) y
  have p0002 := @g_nfv (syn_wbr A F (syn_cfv F A)) y dv_cache_0001
  have p0003 :=
    @g_nfim (syn_weu y (syn_wbr A F (.cv y))) (syn_wbr A F (syn_cfv F A)) y p0001 p0002
  have p0004 := @g_tz6_12_1 y A (.cv y) F dv_cache_0002 dv_cache_0003
  have p0005 :=
    @g_expcom (syn_wbr A F (.cv y)) (syn_weu y (syn_wbr A F (.cv y)))
      (.classEq (syn_cfv F A) (.cv y)) p0004
  have p0006 := @g_breq2 (syn_cfv F A) (.cv y) A F
  have p0007 :=
    @g_biimprd (.classEq (syn_cfv F A) (.cv y)) (syn_wbr A F (syn_cfv F A))
      (syn_wbr A F (.cv y)) p0006
  have p0008 :=
    @g_syli (syn_wbr A F (.cv y)) (syn_weu y (syn_wbr A F (.cv y)))
      (.classEq (syn_cfv F A) (.cv y)) (syn_wbr A F (syn_cfv F A)) p0005 p0007
  have p0009 :=
    @g_com12 (syn_weu y (syn_wbr A F (.cv y))) (syn_wbr A F (.cv y))
      (syn_wbr A F (syn_cfv F A)) p0008
  have p0010 :=
    @g_exlimi (syn_wbr A F (.cv y))
      (.imp (syn_weu y (syn_wbr A F (.cv y))) (syn_wbr A F (syn_cfv F A))) y p0003 p0009
  have p0011 :=
    @g_mpcom (syn_wex y (syn_wbr A F (.cv y))) (syn_weu y (syn_wbr A F (.cv y)))
      (syn_wbr A F (syn_cfv F A)) p0000 p0010
  have p0012 := @g_breq2 (syn_cfv F A) B A F
  have p0013 :=
    @g_syl5ibcom (syn_weu y (syn_wbr A F (.cv y))) (syn_wbr A F (syn_cfv F A))
      (.classEq (syn_cfv F A) B) (syn_wbr A F B) p0011 p0012
  have p0014 := @g_tz6_12_1 y A B F dv_cache_0002 dv_cache_0003
  have p0015 :=
    @g_expcom (syn_wbr A F B) (syn_weu y (syn_wbr A F (.cv y))) (.classEq (syn_cfv F A) B)
      p0014
  have p0016 :=
    @g_impbid (syn_weu y (syn_wbr A F (.cv y))) (.classEq (syn_cfv F A) B) (syn_wbr A F B)
      p0013 p0015
  exact p0016

@[expose]
noncomputable def g_ndmfv (A : Class) (F : Class) :
    Nominal.NPrf
      (.imp (.neg (.classMem A (syn_cdm F))) (.classEq (syn_cfv F A) (syn_c0))) :=
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
  have p0000 := @g_eldm x A F dv_cache_0001 dv_cache_0002
  have p0001 := @g_euex (syn_wbr A F (.cv x)) x
  have p0002 :=
    @g_con3i (syn_weu x (syn_wbr A F (.cv x))) (syn_wex x (syn_wbr A F (.cv x))) p0001
  have p0003 := @g_tz6_12_2 x A F dv_cache_0001 dv_cache_0002
  have p0004 :=
    @g_syl (.neg (syn_wex x (syn_wbr A F (.cv x))))
      (.neg (syn_weu x (syn_wbr A F (.cv x)))) (.classEq (syn_cfv F A) (syn_c0)) p0002
      p0003
  have p0005 :=
    @g_sylnbi (.classMem A (syn_cdm F)) (syn_wex x (syn_wbr A F (.cv x)))
      (.classEq (syn_cfv F A) (syn_c0)) p0000 p0004
  exact p0005

@[expose]
noncomputable def g_elfvdm (A : Class) (B : Class) (F : Class) :
    Nominal.NPrf (.imp (.classMem A (syn_cfv F B)) (.classMem B (syn_cdm F))) :=
  by
  have p0000 := @g_ne0i (syn_cfv F B) A
  have p0001 := @g_ndmfv B F
  have p0002 := @g_necon1ai (.classMem B (syn_cdm F)) (syn_cfv F B) (syn_c0) p0001
  have p0003 :=
    @g_syl (.classMem A (syn_cfv F B)) (syn_wne (syn_cfv F B) (syn_c0))
      (.classMem B (syn_cdm F)) p0000 p0002
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

@[expose]
noncomputable def g_funbrfv (A : Class) (B : Class) (F : Class) :
    Nominal.NPrf (.imp (syn_wfun F) (.imp (syn_wbr A F B) (.classEq (syn_cfv F A) B))) :=
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
  have p0000 := @g_funeu y A B F dv_cache_0001 dv_cache_0002
  have p0001 := @g_tz6_12_1 y A B F dv_cache_0001 dv_cache_0002
  have p0002 :=
    @g_sylan2 (syn_wa (syn_wfun F) (syn_wbr A F B)) (syn_wbr A F B)
      (syn_weu y (syn_wbr A F (.cv y))) (.classEq (syn_cfv F A) B) p0000 p0001
  have p0003 := @g_anabss7 (syn_wfun F) (syn_wbr A F B) (.classEq (syn_cfv F A) B) p0002
  have p0004 := @g_ex (syn_wfun F) (syn_wbr A F B) (.classEq (syn_cfv F A) B) p0003
  exact p0004

@[expose]
noncomputable def g_funopfv (A : Class) (B : Class) (F : Class) :
    Nominal.NPrf
      (.imp (syn_wfun F) (.imp (.classMem (syn_cop A B) F) (.classEq (syn_cfv F A) B))) :=
  by
  have p0000 := (Nominal.biimpRefl (syn_wbr A F B))
  have p0001 := @g_funbrfv A B F
  have p0002 :=
    @g_syl5bir (.classMem (syn_cop A B) F) (syn_wbr A F B) (syn_wfun F)
      (.classEq (syn_cfv F A) B) p0000 p0001
  exact p0002

@[expose]
noncomputable def g_fnbrfvb (A : Class) (B : Class) (C : Class) (F : Class) :
    Nominal.NPrf
      (.imp (syn_wa (syn_wfn F A) (.classMem B A))
        (syn_wb (.classEq (syn_cfv F B) C) (syn_wbr B F C))) :=
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
  have p0000 := @g_fneu x A B F dv_cache_0001 dv_cache_0002
  have p0001 := @g_tz6_12c x B C F dv_cache_0001 dv_cache_0002
  have p0002 :=
    @g_syl (syn_wa (syn_wfn F A) (.classMem B A)) (syn_weu x (syn_wbr B F (.cv x)))
      (syn_wb (.classEq (syn_cfv F B) C) (syn_wbr B F C)) p0000 p0001
  exact p0002

@[expose]
noncomputable def g_fnopfvb (A : Class) (B : Class) (C : Class) (F : Class) :
    Nominal.NPrf
      (.imp (syn_wa (syn_wfn F A) (.classMem B A))
        (syn_wb (.classEq (syn_cfv F B) C) (.classMem (syn_cop B C) F))) :=
  by
  have p0000 := @g_fnbrfvb A B C F
  have p0001 := (Nominal.biimpRefl (syn_wbr B F C))
  have p0002 :=
    @g_syl6bb (syn_wa (syn_wfn F A) (.classMem B A)) (.classEq (syn_cfv F B) C)
      (syn_wbr B F C) (.classMem (syn_cop B C) F) p0000 p0001
  exact p0002

@[expose]
noncomputable def g_funbrfvb (A : Class) (B : Class) (F : Class) :
    Nominal.NPrf
      (.imp (syn_wa (syn_wfun F) (.classMem A (syn_cdm F)))
        (syn_wb (.classEq (syn_cfv F A) B) (syn_wbr A F B))) :=
  by
  have p0000 := @g_funfn F
  have p0001 := @g_fnbrfvb (syn_cdm F) A B F
  have p0002 :=
    @g_sylanb (syn_wfun F) (syn_wfn F (syn_cdm F)) (.classMem A (syn_cdm F))
      (syn_wb (.classEq (syn_cfv F A) B) (syn_wbr A F B)) p0000 p0001
  exact p0002

@[expose]
noncomputable def g_funopfvb (A : Class) (B : Class) (F : Class) :
    Nominal.NPrf
      (.imp (syn_wa (syn_wfun F) (.classMem A (syn_cdm F)))
        (syn_wb (.classEq (syn_cfv F A) B) (.classMem (syn_cop A B) F))) :=
  by
  have p0000 := @g_funbrfvb A B F
  have p0001 := (Nominal.biimpRefl (syn_wbr A F B))
  have p0002 :=
    @g_syl6bb (syn_wa (syn_wfun F) (.classMem A (syn_cdm F))) (.classEq (syn_cfv F A) B)
      (syn_wbr A F B) (.classMem (syn_cop A B) F) p0000 p0001
  exact p0002

@[expose]
noncomputable def g_funbrfv2b (A : Class) (B : Class) (F : Class) :
    Nominal.NPrf
      (.imp (syn_wfun F) (syn_wb (syn_wbr A F B)
          (syn_wa (.classMem A (syn_cdm F)) (.classEq (syn_cfv F A) B)))) :=
  by
  have p0000 := @g_breldm A B F
  have p0001 := @g_a1i (.imp (syn_wbr A F B) (.classMem A (syn_cdm F))) (syn_wfun F) p0000
  have p0002 := @g_pm4_71rd (syn_wfun F) (syn_wbr A F B) (.classMem A (syn_cdm F)) p0001
  have p0003 := @g_funbrfvb A B F
  have p0004 :=
    @g_pm5_32da (syn_wfun F) (.classMem A (syn_cdm F)) (.classEq (syn_cfv F A) B)
      (syn_wbr A F B) p0003
  have p0005 :=
    @g_bitr4d (syn_wfun F) (syn_wbr A F B)
      (syn_wa (.classMem A (syn_cdm F)) (syn_wbr A F B))
      (syn_wa (.classMem A (syn_cdm F)) (.classEq (syn_cfv F A) B)) p0002 p0004
  exact p0005

@[expose]
noncomputable def g_fnrnfv (x : Var) (y : Var) (A : Class) (F : Class) (dv_A_x : x ∉ A.fv)
    (dv_A_y : y ∉ A.fv) (dv_F_x : x ∉ F.fv) (dv_F_y : y ∉ F.fv) (dv_x_y : x ≠ y) :
    Nominal.NPrf
      (.imp (syn_wfn F A) (.classEq (syn_crn F)
          (.cab y (syn_wrex x A (.classEq (.cv y) (syn_cfv F (.cv x))))))) :=
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
  have dv_cache_0004 : x ∉ ((syn_wfn F A)).fv :=
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
  have dv_cache_0005 : y ∉ ((syn_wfn F A)).fv :=
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
  have p0000 := @g_dfrn3 x y F dv_cache_0001 dv_cache_0002 dv_cache_0003
  have p0001 := @g_fnop A (.cv x) (.cv y) F
  have p0002 :=
    @g_ex (syn_wfn F A) (.classMem (syn_cop (.cv x) (.cv y)) F) (.classMem (.cv x) A)
      p0001
  have p0003 :=
    @g_pm4_71rd (syn_wfn F A) (.classMem (syn_cop (.cv x) (.cv y)) F)
      (.classMem (.cv x) A) p0002
  have p0004 := @g_fnopfvb A (.cv x) (.cv y) F
  have p0005 :=
    @g_pm5_32da (syn_wfn F A) (.classMem (.cv x) A) (.classEq (syn_cfv F (.cv x)) (.cv y))
      (.classMem (syn_cop (.cv x) (.cv y)) F) p0004
  have p0006 :=
    @g_bitr4d (syn_wfn F A) (.classMem (syn_cop (.cv x) (.cv y)) F)
      (syn_wa (.classMem (.cv x) A) (.classMem (syn_cop (.cv x) (.cv y)) F))
      (syn_wa (.classMem (.cv x) A) (.classEq (syn_cfv F (.cv x)) (.cv y))) p0003 p0005
  have p0007 :=
    @g_exbidv (syn_wfn F A) (.classMem (syn_cop (.cv x) (.cv y)) F)
      (syn_wa (.classMem (.cv x) A) (.classEq (syn_cfv F (.cv x)) (.cv y))) x
      dv_cache_0004 p0006
  have p0008 := @g_eqcom (.cv y) (syn_cfv F (.cv x))
  have p0009 :=
    @g_rexbii (.classEq (.cv y) (syn_cfv F (.cv x)))
      (.classEq (syn_cfv F (.cv x)) (.cv y)) x A p0008
  have p0010 := (Nominal.biimpRefl (syn_wrex x A (.classEq (syn_cfv F (.cv x)) (.cv y))))
  have p0011 :=
    @g_bitri (syn_wrex x A (.classEq (.cv y) (syn_cfv F (.cv x))))
      (syn_wrex x A (.classEq (syn_cfv F (.cv x)) (.cv y)))
      (syn_wex x (syn_wa (.classMem (.cv x) A) (.classEq (syn_cfv F (.cv x)) (.cv y))))
      p0009 p0010
  have p0012 :=
    @g_syl6bbr (syn_wfn F A) (syn_wex x (.classMem (syn_cop (.cv x) (.cv y)) F))
      (syn_wex x (syn_wa (.classMem (.cv x) A) (.classEq (syn_cfv F (.cv x)) (.cv y))))
      (syn_wrex x A (.classEq (.cv y) (syn_cfv F (.cv x)))) p0007 p0011
  have p0013 :=
    @g_abbidv (syn_wfn F A) (syn_wex x (.classMem (syn_cop (.cv x) (.cv y)) F))
      (syn_wrex x A (.classEq (.cv y) (syn_cfv F (.cv x)))) y dv_cache_0005 p0012
  have p0014 :=
    @g_syl5eq (syn_wfn F A) (syn_crn F)
      (.cab y (syn_wex x (.classMem (syn_cop (.cv x) (.cv y)) F)))
      (.cab y (syn_wrex x A (.classEq (.cv y) (syn_cfv F (.cv x))))) p0000 p0013
  exact p0014

@[expose]
noncomputable def g_fvelrnb (x : Var) (A : Class) (B : Class) (F : Class)
    (dv_A_x : x ∉ A.fv) (dv_B_x : x ∉ B.fv) (dv_F_x : x ∉ F.fv) :
    Nominal.NPrf
      (.imp (syn_wfn F A) (syn_wb (.classMem B (syn_crn F))
          (syn_wrex x A (.classEq (syn_cfv F (.cv x)) B)))) :=
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
  have dv_cache_0006 : x ∉ ((Wff.classMem B (syn_cvv))).fv :=
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
  have dv_cache_0009 : y ∉ ((syn_wrex x A (.classEq (syn_cfv F (.cv x)) B))).fv :=
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
    @g_fnrnfv x y A F dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
      dv_cache_0005
  have p0001 :=
    @g_eleq2d (syn_wfn F A) (syn_crn F)
      (.cab y (syn_wrex x A (.classEq (.cv y) (syn_cfv F (.cv x))))) B p0000
  have p0002 := @g_fvex (.cv x) F
  have p0003 := @g_eleq1 (syn_cfv F (.cv x)) B (syn_cvv)
  have p0004 :=
    @g_mpbii (.classEq (syn_cfv F (.cv x)) B) (.classMem (syn_cfv F (.cv x)) (syn_cvv))
      (.classMem B (syn_cvv)) p0002 p0003
  have p0005 :=
    @g_rexlimivw (.classEq (syn_cfv F (.cv x)) B) (.classMem B (syn_cvv)) x A
      dv_cache_0006 p0004
  have p0006 := @g_eqeq1 (.cv y) B (syn_cfv F (.cv x))
  have p0007 := @g_eqcom B (syn_cfv F (.cv x))
  have p0008 :=
    @g_syl6bb (.classEq (.cv y) B) (.classEq (.cv y) (syn_cfv F (.cv x)))
      (.classEq B (syn_cfv F (.cv x))) (.classEq (syn_cfv F (.cv x)) B) p0006 p0007
  have p0009 :=
    @g_rexbidv (.classEq (.cv y) B) (.classEq (.cv y) (syn_cfv F (.cv x)))
      (.classEq (syn_cfv F (.cv x)) B) x A dv_cache_0007 p0008
  have p0010 :=
    @g_elab3 (syn_wrex x A (.classEq (.cv y) (syn_cfv F (.cv x))))
      (syn_wrex x A (.classEq (syn_cfv F (.cv x)) B)) y B dv_cache_0008 dv_cache_0009
      p0005 p0009
  have p0011 :=
    @g_syl6bb (syn_wfn F A) (.classMem B (syn_crn F))
      (.classMem B (.cab y (syn_wrex x A (.classEq (.cv y) (syn_cfv F (.cv x))))))
      (syn_wrex x A (.classEq (syn_cfv F (.cv x)) B)) p0001 p0010
  exact p0011

@[expose]
noncomputable def g_dfimafn (x : Var) (y : Var) (A : Class) (F : Class)
    (dv_A_x : x ∉ A.fv) (dv_A_y : y ∉ A.fv) (dv_F_x : x ∉ F.fv) (dv_F_y : y ∉ F.fv)
    (dv_x_y : x ≠ y) :
    Nominal.NPrf
      (.imp (syn_wa (syn_wfun F) (syn_wss A (syn_cdm F))) (.classEq (syn_cima F A)
          (.cab y (syn_wrex x A (.classEq (syn_cfv F (.cv x)) (.cv y)))))) :=
  by
  have dv_cache_0001 : x ∉ ((syn_wa (syn_wfun F) (syn_wss A (syn_cdm F)))).fv := by
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
  have dv_cache_0002 : y ∉ ((syn_wa (syn_wfun F) (syn_wss A (syn_cdm F)))).fv :=
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
  have p0000 := @g_ssel2 A (syn_cdm F) (.cv x)
  have p0001 := @g_funbrfvb (.cv x) (.cv y) F
  have p0002 :=
    @g_sylan2 (syn_wa (syn_wss A (syn_cdm F)) (.classMem (.cv x) A)) (syn_wfun F)
      (.classMem (.cv x) (syn_cdm F))
      (syn_wb (.classEq (syn_cfv F (.cv x)) (.cv y)) (syn_wbr (.cv x) F (.cv y))) p0000
      p0001
  have p0003 :=
    @g_anassrs (syn_wfun F) (syn_wss A (syn_cdm F)) (.classMem (.cv x) A)
      (syn_wb (.classEq (syn_cfv F (.cv x)) (.cv y)) (syn_wbr (.cv x) F (.cv y))) p0002
  have p0004 :=
    @g_rexbidva (syn_wa (syn_wfun F) (syn_wss A (syn_cdm F)))
      (.classEq (syn_cfv F (.cv x)) (.cv y)) (syn_wbr (.cv x) F (.cv y)) x A dv_cache_0001
      p0003
  have p0005 :=
    @g_abbidv (syn_wa (syn_wfun F) (syn_wss A (syn_cdm F)))
      (syn_wrex x A (.classEq (syn_cfv F (.cv x)) (.cv y)))
      (syn_wrex x A (syn_wbr (.cv x) F (.cv y))) y dv_cache_0002 p0004
  have p0006 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominal_df_ima y x F A
      dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007
  have p0007 :=
    @g_syl6reqr (syn_wa (syn_wfun F) (syn_wss A (syn_cdm F)))
      (.cab y (syn_wrex x A (.classEq (syn_cfv F (.cv x)) (.cv y))))
      (.cab y (syn_wrex x A (syn_wbr (.cv x) F (.cv y)))) (syn_cima F A) p0005 p0006
  exact p0007

@[expose]
noncomputable def g_funimass4 (x : Var) (A : Class) (B : Class) (F : Class)
    (dv_A_x : x ∉ A.fv) (dv_B_x : x ∉ B.fv) (dv_F_x : x ∉ F.fv) :
    Nominal.NPrf
      (.imp (syn_wa (syn_wfun F) (syn_wss A (syn_cdm F))) (syn_wb (syn_wss (syn_cima F A) B)
          (syn_wral x A (.classMem (syn_cfv F (.cv x)) B)))) :=
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
  have dv_cache_0001 : y ∉ ((syn_cima F A)).fv := by
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
  have dv_cache_0003 : x ∉ ((syn_wa (syn_wfun F) (syn_wss A (syn_cdm F)))).fv :=
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
  have dv_cache_0008 : y ∉ ((syn_wa (syn_wfun F) (syn_wss A (syn_cdm F)))).fv :=
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
  have dv_cache_0011 : y ∉ ((syn_cfv F (.cv x))).fv :=
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
  have dv_cache_0012 : y ∉ ((Wff.classMem (syn_cfv F (.cv x)) B)).fv :=
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
  have p0000 := @g_dfss2 y (syn_cima F A) B dv_cache_0001 dv_cache_0002
  have p0001 := @g_ssel2 A (syn_cdm F) (.cv x)
  have p0002 := @g_eqcom (.cv y) (syn_cfv F (.cv x))
  have p0003 := @g_funbrfvb (.cv x) (.cv y) F
  have p0004 :=
    @g_syl5bb (.classEq (.cv y) (syn_cfv F (.cv x)))
      (.classEq (syn_cfv F (.cv x)) (.cv y))
      (syn_wa (syn_wfun F) (.classMem (.cv x) (syn_cdm F))) (syn_wbr (.cv x) F (.cv y))
      p0002 p0003
  have p0005 :=
    @g_sylan2 (syn_wa (syn_wss A (syn_cdm F)) (.classMem (.cv x) A)) (syn_wfun F)
      (.classMem (.cv x) (syn_cdm F))
      (syn_wb (.classEq (.cv y) (syn_cfv F (.cv x))) (syn_wbr (.cv x) F (.cv y))) p0001
      p0004
  have p0006 :=
    @g_anassrs (syn_wfun F) (syn_wss A (syn_cdm F)) (.classMem (.cv x) A)
      (syn_wb (.classEq (.cv y) (syn_cfv F (.cv x))) (syn_wbr (.cv x) F (.cv y))) p0005
  have p0007 :=
    @g_rexbidva (syn_wa (syn_wfun F) (syn_wss A (syn_cdm F)))
      (.classEq (.cv y) (syn_cfv F (.cv x))) (syn_wbr (.cv x) F (.cv y)) x A dv_cache_0003
      p0006
  have p0008 := @g_elima x (.cv y) F A dv_cache_0004 dv_cache_0005 dv_cache_0006
  have p0009 :=
    @g_syl6rbbr (syn_wa (syn_wfun F) (syn_wss A (syn_cdm F)))
      (syn_wrex x A (.classEq (.cv y) (syn_cfv F (.cv x))))
      (syn_wrex x A (syn_wbr (.cv x) F (.cv y))) (.classMem (.cv y) (syn_cima F A)) p0007
      p0008
  have p0010 :=
    @g_imbi1d (syn_wa (syn_wfun F) (syn_wss A (syn_cdm F)))
      (.classMem (.cv y) (syn_cima F A))
      (syn_wrex x A (.classEq (.cv y) (syn_cfv F (.cv x)))) (.classMem (.cv y) B) p0009
  have p0011 :=
    @g_r19_23v (.classEq (.cv y) (syn_cfv F (.cv x))) (.classMem (.cv y) B) x A
      dv_cache_0007
  have p0012 :=
    @g_syl6bbr (syn_wa (syn_wfun F) (syn_wss A (syn_cdm F)))
      (.imp (.classMem (.cv y) (syn_cima F A)) (.classMem (.cv y) B))
      (.imp (syn_wrex x A (.classEq (.cv y) (syn_cfv F (.cv x)))) (.classMem (.cv y) B))
      (syn_wral x A (.imp (.classEq (.cv y) (syn_cfv F (.cv x))) (.classMem (.cv y) B)))
      p0010 p0011
  have p0013 :=
    @g_albidv (syn_wa (syn_wfun F) (syn_wss A (syn_cdm F)))
      (.imp (.classMem (.cv y) (syn_cima F A)) (.classMem (.cv y) B))
      (syn_wral x A (.imp (.classEq (.cv y) (syn_cfv F (.cv x))) (.classMem (.cv y) B))) y
      dv_cache_0008 p0012
  have p0014 :=
    @g_ralcom4 (.imp (.classEq (.cv y) (syn_cfv F (.cv x))) (.classMem (.cv y) B)) x y A
      dv_cache_0009 dv_cache_0010
  have p0015 := @g_fvex (.cv x) F
  have p0016 := @g_eleq1 (.cv y) (syn_cfv F (.cv x)) B
  have p0017 :=
    @g_ceqsalv (.classMem (.cv y) B) (.classMem (syn_cfv F (.cv x)) B) y
      (syn_cfv F (.cv x)) dv_cache_0011 dv_cache_0012 p0015 p0016
  have p0018 :=
    @g_ralbii (.all y (.imp (.classEq (.cv y) (syn_cfv F (.cv x))) (.classMem (.cv y) B)))
      (.classMem (syn_cfv F (.cv x)) B) x A p0017
  have p0019 :=
    @g_bitr3i
      (.all y (syn_wral x A
          (.imp (.classEq (.cv y) (syn_cfv F (.cv x))) (.classMem (.cv y) B))))
      (syn_wral x A
        (.all y (.imp (.classEq (.cv y) (syn_cfv F (.cv x))) (.classMem (.cv y) B))))
      (syn_wral x A (.classMem (syn_cfv F (.cv x)) B)) p0014 p0018
  have p0020 :=
    @g_syl6bb (syn_wa (syn_wfun F) (syn_wss A (syn_cdm F)))
      (.all y (.imp (.classMem (.cv y) (syn_cima F A)) (.classMem (.cv y) B)))
      (.all y (syn_wral x A
          (.imp (.classEq (.cv y) (syn_cfv F (.cv x))) (.classMem (.cv y) B))))
      (syn_wral x A (.classMem (syn_cfv F (.cv x)) B)) p0013 p0019
  have p0021 :=
    @g_syl5bb (syn_wss (syn_cima F A) B)
      (.all y (.imp (.classMem (.cv y) (syn_cima F A)) (.classMem (.cv y) B)))
      (syn_wa (syn_wfun F) (syn_wss A (syn_cdm F)))
      (syn_wral x A (.classMem (syn_cfv F (.cv x)) B)) p0000 p0020
  exact p0021

@[expose]
noncomputable def g_fvelima (x : Var) (A : Class) (B : Class) (F : Class)
    (dv_A_x : x ∉ A.fv) (dv_B_x : x ∉ B.fv) (dv_F_x : x ∉ F.fv) :
    Nominal.NPrf
      (.imp (syn_wa (syn_wfun F) (.classMem A (syn_cima F B)))
        (syn_wrex x B (.classEq (syn_cfv F (.cv x)) A))) :=
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
  have dv_cache_0004 : x ∉ ((syn_wfun F)).fv :=
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
  have p0000 := @g_elima x A F B dv_cache_0001 dv_cache_0002 dv_cache_0003
  have p0001 := @g_funbrfv (.cv x) A F
  have p0002 :=
    @g_reximdv (syn_wfun F) (syn_wbr (.cv x) F A) (.classEq (syn_cfv F (.cv x)) A) x B
      dv_cache_0004 p0001
  have p0003 :=
    @g_syl5bi (.classMem A (syn_cima F B)) (syn_wrex x B (syn_wbr (.cv x) F A))
      (syn_wfun F) (syn_wrex x B (.classEq (syn_cfv F (.cv x)) A)) p0000 p0002
  have p0004 :=
    @g_imp (syn_wfun F) (.classMem A (syn_cima F B))
      (syn_wrex x B (.classEq (syn_cfv F (.cv x)) A)) p0003
  exact p0004

@[expose]
noncomputable def g_fvelimab (x : Var) (A : Class) (B : Class) (C : Class) (F : Class)
    (dv_B_x : x ∉ B.fv) (dv_C_x : x ∉ C.fv) (dv_F_x : x ∉ F.fv) :
    Nominal.NPrf
      (.imp (syn_wa (syn_wfn F A) (syn_wss B A)) (syn_wb (.classMem C (syn_cima F B))
          (syn_wrex x B (.classEq (syn_cfv F (.cv x)) C)))) :=
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
  have dv_cache_0001 : x ∉ ((Wff.classMem C (syn_cvv))).fv := by
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
      ((Wff.imp (syn_wa (syn_wfn F A) (syn_wss B A)) (syn_wb (.classMem C (syn_cima F B))
            (syn_wrex x B (.classEq (syn_cfv F (.cv x)) C))))).fv :=
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
  have p0000 := @g_elex C (syn_cima F B)
  have p0001 :=
    @g_anim2i (.classMem C (syn_cima F B)) (.classMem C (syn_cvv))
      (syn_wa (syn_wfn F A) (syn_wss B A)) p0000
  have p0002 := @g_fvex (.cv x) F
  have p0003 := @g_eleq1 (syn_cfv F (.cv x)) C (syn_cvv)
  have p0004 :=
    @g_mpbii (.classEq (syn_cfv F (.cv x)) C) (.classMem (syn_cfv F (.cv x)) (syn_cvv))
      (.classMem C (syn_cvv)) p0002 p0003
  have p0005 :=
    @g_rexlimivw (.classEq (syn_cfv F (.cv x)) C) (.classMem C (syn_cvv)) x B
      dv_cache_0001 p0004
  have p0006 :=
    @g_anim2i (syn_wrex x B (.classEq (syn_cfv F (.cv x)) C)) (.classMem C (syn_cvv))
      (syn_wa (syn_wfn F A) (syn_wss B A)) p0005
  have p0007 := @g_eleq1 (.cv y) C (syn_cima F B)
  have p0008 := @g_eqeq2 (.cv y) C (syn_cfv F (.cv x))
  have p0009 :=
    @g_rexbidv (.classEq (.cv y) C) (.classEq (syn_cfv F (.cv x)) (.cv y))
      (.classEq (syn_cfv F (.cv x)) C) x B dv_cache_0002 p0008
  have p0010 :=
    @g_bibi12d (.classEq (.cv y) C) (.classMem (.cv y) (syn_cima F B))
      (.classMem C (syn_cima F B)) (syn_wrex x B (.classEq (syn_cfv F (.cv x)) (.cv y)))
      (syn_wrex x B (.classEq (syn_cfv F (.cv x)) C)) p0007 p0009
  have p0011 :=
    @g_imbi2d (.classEq (.cv y) C)
      (syn_wb (.classMem (.cv y) (syn_cima F B))
        (syn_wrex x B (.classEq (syn_cfv F (.cv x)) (.cv y))))
      (syn_wb (.classMem C (syn_cima F B)) (syn_wrex x B (.classEq (syn_cfv F (.cv x)) C)))
      (syn_wa (syn_wfn F A) (syn_wss B A)) p0010
  have p0012 := @g_fnfun A F
  have p0013 := @g_adantr (syn_wfn F A) (syn_wfun F) (syn_wss B A) p0012
  have p0014 := @g_fndm A F
  have p0015 := @g_sseq2d (syn_wfn F A) (syn_cdm F) A B p0014
  have p0016 := @g_biimpar (syn_wfn F A) (syn_wss B (syn_cdm F)) (syn_wss B A) p0015
  have p0017 :=
    @g_dfimafn x y B F dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006
      dv_cache_0007
  have p0018 :=
    @g_syl2anc (syn_wa (syn_wfn F A) (syn_wss B A)) (syn_wfun F) (syn_wss B (syn_cdm F))
      (.classEq (syn_cima F B) (.cab y (syn_wrex x B (.classEq (syn_cfv F (.cv x)) (.cv y)))))
      p0013 p0016 p0017
  have p0019 :=
    @g_eqabrd (syn_wa (syn_wfn F A) (syn_wss B A))
      (syn_wrex x B (.classEq (syn_cfv F (.cv x)) (.cv y))) y (syn_cima F B) p0018
  have p0020 :=
    @g_vtoclg
      (.imp (syn_wa (syn_wfn F A) (syn_wss B A)) (syn_wb (.classMem (.cv y) (syn_cima F B))
          (syn_wrex x B (.classEq (syn_cfv F (.cv x)) (.cv y)))))
      (.imp (syn_wa (syn_wfn F A) (syn_wss B A)) (syn_wb (.classMem C (syn_cima F B))
          (syn_wrex x B (.classEq (syn_cfv F (.cv x)) C))))
      y C (syn_cvv) dv_cache_0008 dv_cache_0009 p0011 p0019
  have p0021 :=
    @g_impcom (.classMem C (syn_cvv)) (syn_wa (syn_wfn F A) (syn_wss B A))
      (syn_wb (.classMem C (syn_cima F B)) (syn_wrex x B (.classEq (syn_cfv F (.cv x)) C)))
      p0020
  have p0022 :=
    @g_pm5_21nd (syn_wa (syn_wfn F A) (syn_wss B A)) (.classMem C (syn_cima F B))
      (syn_wrex x B (.classEq (syn_cfv F (.cv x)) C))
      (syn_wa (syn_wa (syn_wfn F A) (syn_wss B A)) (.classMem C (syn_cvv))) p0001 p0006
      p0021
  exact p0022

@[expose]
noncomputable def g_fnsnfv (A : Class) (B : Class) (F : Class) :
    Nominal.NPrf
      (.imp (syn_wa (syn_wfn F A) (.classMem B A))
        (.classEq (syn_csn (syn_cfv F B)) (syn_cima F (syn_csn B)))) :=
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
  have dv_cache_0001 : y ∉ ((syn_wa (syn_wfn F A) (.classMem B A))).fv := by
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
  have dv_cache_0002 : y ∉ ((syn_cfv F B)).fv :=
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
  have p0000 := @g_eqcom (.cv y) (syn_cfv F B)
  have p0001 := @g_fnbrfvb A B (.cv y) F
  have p0002 :=
    @g_syl5bb (.classEq (.cv y) (syn_cfv F B)) (.classEq (syn_cfv F B) (.cv y))
      (syn_wa (syn_wfn F A) (.classMem B A)) (syn_wbr B F (.cv y)) p0000 p0001
  have p0003 :=
    @g_abbidv (syn_wa (syn_wfn F A) (.classMem B A)) (.classEq (.cv y) (syn_cfv F B))
      (syn_wbr B F (.cv y)) y dv_cache_0001 p0002
  have p0004 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominal_df_sn y (syn_cfv F B)
      dv_cache_0002
  have p0005 := @g_imasn y B F dv_cache_0003 dv_cache_0004
  have p0006 :=
    @g_n_3eqtr4g (syn_wa (syn_wfn F A) (.classMem B A))
      (.cab y (.classEq (.cv y) (syn_cfv F B))) (.cab y (syn_wbr B F (.cv y)))
      (syn_csn (syn_cfv F B)) (syn_cima F (syn_csn B)) p0003 p0004 p0005
  exact p0006

@[expose]
noncomputable def g_funfv (A : Class) (F : Class) :
    Nominal.NPrf
      (.imp (syn_wfun F) (.classEq (syn_cfv F A) (syn_cuni (syn_cima F (syn_csn A))))) :=
  by
  have p0000 := @g_fvex A F
  have p0001 := @g_unisn (syn_cfv F A) p0000
  have p0002 := @g_eqid (syn_cdm F)
  have p0003 := (Nominal.biimpRefl (syn_wfn F (syn_cdm F)))
  have p0004 :=
    @g_mpbiran2 (syn_wfn F (syn_cdm F)) (syn_wfun F) (.classEq (syn_cdm F) (syn_cdm F))
      p0002 p0003
  have p0005 := @g_fnsnfv (syn_cdm F) A F
  have p0006 :=
    @g_sylanbr (syn_wfun F) (syn_wfn F (syn_cdm F)) (.classMem A (syn_cdm F))
      (.classEq (syn_csn (syn_cfv F A)) (syn_cima F (syn_csn A))) p0004 p0005
  have p0007 :=
    @g_unieqd (syn_wa (syn_wfun F) (.classMem A (syn_cdm F))) (syn_csn (syn_cfv F A))
      (syn_cima F (syn_csn A)) p0006
  have p0008 :=
    @g_syl5eqr (syn_wa (syn_wfun F) (.classMem A (syn_cdm F))) (syn_cfv F A)
      (syn_cuni (syn_csn (syn_cfv F A))) (syn_cuni (syn_cima F (syn_csn A))) p0001 p0007
  have p0009 :=
    @g_ex (syn_wfun F) (.classMem A (syn_cdm F))
      (.classEq (syn_cfv F A) (syn_cuni (syn_cima F (syn_csn A)))) p0008
  have p0010 := @g_ndmfv A F
  have p0011 := @g_ndmima A F
  have p0012 :=
    @g_unieqd (.neg (.classMem A (syn_cdm F))) (syn_cima F (syn_csn A)) (syn_c0) p0011
  have p0013 := @g_uni0
  have p0014 :=
    @g_syl6eq (.neg (.classMem A (syn_cdm F))) (syn_cuni (syn_cima F (syn_csn A)))
      (syn_cuni (syn_c0)) (syn_c0) p0012 p0013
  have p0015 :=
    @g_eqtr4d (.neg (.classMem A (syn_cdm F))) (syn_cfv F A) (syn_c0)
      (syn_cuni (syn_cima F (syn_csn A))) p0010 p0014
  have p0016 :=
    @g_pm2_61d1 (syn_wfun F) (.classMem A (syn_cdm F))
      (.classEq (syn_cfv F A) (syn_cuni (syn_cima F (syn_csn A)))) p0009 p0015
  exact p0016

@[expose]
noncomputable def g_fvun (A : Class) (F : Class) (G : Class) :
    Nominal.NPrf
      (.imp (syn_wa (syn_wa (syn_wfun F) (syn_wfun G))
          (.classEq (syn_cin (syn_cdm F) (syn_cdm G)) (syn_c0)))
        (.classEq (syn_cfv (syn_cun F G) A) (syn_cun (syn_cfv F A) (syn_cfv G A)))) :=
  by
  have p0000 := @g_funun F G
  have p0001 := @g_funfv A (syn_cun F G)
  have p0002 :=
    @g_syl
      (syn_wa (syn_wa (syn_wfun F) (syn_wfun G))
        (.classEq (syn_cin (syn_cdm F) (syn_cdm G)) (syn_c0)))
      (syn_wfun (syn_cun F G))
      (.classEq (syn_cfv (syn_cun F G) A) (syn_cuni (syn_cima (syn_cun F G) (syn_csn A))))
      p0000 p0001
  have p0003 := @g_imaundir F G (syn_csn A)
  have p0004 :=
    @g_a1i
      (.classEq (syn_cima (syn_cun F G) (syn_csn A))
        (syn_cun (syn_cima F (syn_csn A)) (syn_cima G (syn_csn A))))
      (syn_wa (syn_wa (syn_wfun F) (syn_wfun G))
        (.classEq (syn_cin (syn_cdm F) (syn_cdm G)) (syn_c0)))
      p0003
  have p0005 :=
    @g_unieqd
      (syn_wa (syn_wa (syn_wfun F) (syn_wfun G))
        (.classEq (syn_cin (syn_cdm F) (syn_cdm G)) (syn_c0)))
      (syn_cima (syn_cun F G) (syn_csn A))
      (syn_cun (syn_cima F (syn_csn A)) (syn_cima G (syn_csn A))) p0004
  have p0006 := @g_uniun (syn_cima F (syn_csn A)) (syn_cima G (syn_csn A))
  have p0007 := @g_funfv A F
  have p0008 :=
    @g_eqcomd (syn_wfun F) (syn_cfv F A) (syn_cuni (syn_cima F (syn_csn A))) p0007
  have p0009 := @g_funfv A G
  have p0010 :=
    @g_eqcomd (syn_wfun G) (syn_cfv G A) (syn_cuni (syn_cima G (syn_csn A))) p0009
  have p0011 :=
    @g_anim12i (syn_wfun F) (.classEq (syn_cuni (syn_cima F (syn_csn A))) (syn_cfv F A))
      (syn_wfun G) (.classEq (syn_cuni (syn_cima G (syn_csn A))) (syn_cfv G A)) p0008
      p0010
  have p0012 :=
    @g_adantr (syn_wa (syn_wfun F) (syn_wfun G))
      (syn_wa (.classEq (syn_cuni (syn_cima F (syn_csn A))) (syn_cfv F A))
        (.classEq (syn_cuni (syn_cima G (syn_csn A))) (syn_cfv G A)))
      (.classEq (syn_cin (syn_cdm F) (syn_cdm G)) (syn_c0)) p0011
  have p0013 :=
    @g_uneq12 (syn_cuni (syn_cima F (syn_csn A))) (syn_cfv F A)
      (syn_cuni (syn_cima G (syn_csn A))) (syn_cfv G A)
  have p0014 :=
    @g_syl
      (syn_wa (syn_wa (syn_wfun F) (syn_wfun G))
        (.classEq (syn_cin (syn_cdm F) (syn_cdm G)) (syn_c0)))
      (syn_wa (.classEq (syn_cuni (syn_cima F (syn_csn A))) (syn_cfv F A))
        (.classEq (syn_cuni (syn_cima G (syn_csn A))) (syn_cfv G A)))
      (.classEq
        (syn_cun (syn_cuni (syn_cima F (syn_csn A))) (syn_cuni (syn_cima G (syn_csn A))))
        (syn_cun (syn_cfv F A) (syn_cfv G A)))
      p0012 p0013
  have p0015 :=
    @g_syl5eq
      (syn_wa (syn_wa (syn_wfun F) (syn_wfun G))
        (.classEq (syn_cin (syn_cdm F) (syn_cdm G)) (syn_c0)))
      (syn_cuni (syn_cun (syn_cima F (syn_csn A)) (syn_cima G (syn_csn A))))
      (syn_cun (syn_cuni (syn_cima F (syn_csn A))) (syn_cuni (syn_cima G (syn_csn A))))
      (syn_cun (syn_cfv F A) (syn_cfv G A)) p0006 p0014
  have p0016 :=
    @g_n_3eqtrd
      (syn_wa (syn_wa (syn_wfun F) (syn_wfun G))
        (.classEq (syn_cin (syn_cdm F) (syn_cdm G)) (syn_c0)))
      (syn_cfv (syn_cun F G) A) (syn_cuni (syn_cima (syn_cun F G) (syn_csn A)))
      (syn_cuni (syn_cun (syn_cima F (syn_csn A)) (syn_cima G (syn_csn A))))
      (syn_cun (syn_cfv F A) (syn_cfv G A)) p0002 p0005 p0015
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

@[expose]
noncomputable def g_fvun1 (A : Class) (B : Class) (F : Class) (G : Class) (X : Class) :
    Nominal.NPrf
      (.imp (syn_w3a (syn_wfn F A) (syn_wfn G B)
          (syn_wa (.classEq (syn_cin A B) (syn_c0)) (.classMem X A)))
        (.classEq (syn_cfv (syn_cun F G) X) (syn_cfv F X))) :=
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
  have p0000 := @g_fnfun A F
  have p0001 :=
    @g_n_3ad2ant1 (syn_wfn F A) (syn_wfn G B) (syn_wfun F)
      (syn_wa (.classEq (syn_cin A B) (syn_c0)) (.classMem X A)) p0000
  have p0002 := @g_fnfun B G
  have p0003 :=
    @g_n_3ad2ant2 (syn_wfn G B) (syn_wfn F A) (syn_wfun G)
      (syn_wa (.classEq (syn_cin A B) (syn_c0)) (.classMem X A)) p0002
  have p0004 := @g_fndm A F
  have p0005 := @g_fndm B G
  have p0006 := @g_ineq12 (syn_cdm F) A (syn_cdm G) B
  have p0007 :=
    @g_syl2an (syn_wfn F A) (.classEq (syn_cdm F) A) (.classEq (syn_cdm G) B)
      (.classEq (syn_cin (syn_cdm F) (syn_cdm G)) (syn_cin A B)) (syn_wfn G B) p0004 p0005
      p0006
  have p0008 :=
    @g_eqeq1d (syn_wa (syn_wfn F A) (syn_wfn G B)) (syn_cin (syn_cdm F) (syn_cdm G))
      (syn_cin A B) (syn_c0) p0007
  have p0009 :=
    @g_biimprd (syn_wa (syn_wfn F A) (syn_wfn G B))
      (.classEq (syn_cin (syn_cdm F) (syn_cdm G)) (syn_c0))
      (.classEq (syn_cin A B) (syn_c0)) p0008
  have p0010 :=
    @g_adantrd (syn_wa (syn_wfn F A) (syn_wfn G B)) (.classEq (syn_cin A B) (syn_c0))
      (.classEq (syn_cin (syn_cdm F) (syn_cdm G)) (syn_c0)) (.classMem X A) p0009
  have p0011 :=
    @g_n_3impia (syn_wfn F A) (syn_wfn G B)
      (syn_wa (.classEq (syn_cin A B) (syn_c0)) (.classMem X A))
      (.classEq (syn_cin (syn_cdm F) (syn_cdm G)) (syn_c0)) p0010
  have p0012 := @g_fvun X F G
  have p0013 :=
    @g_syl21anc
      (syn_w3a (syn_wfn F A) (syn_wfn G B)
        (syn_wa (.classEq (syn_cin A B) (syn_c0)) (.classMem X A)))
      (syn_wfun F) (syn_wfun G) (.classEq (syn_cin (syn_cdm F) (syn_cdm G)) (syn_c0))
      (.classEq (syn_cfv (syn_cun F G) X) (syn_cun (syn_cfv F X) (syn_cfv G X))) p0001
      p0003 p0011 p0012
  have p0014 := @g_disj x A B dv_cache_0001 dv_cache_0002
  have p0015 := @g_eleq1 (.cv x) X B
  have p0016 := @g_notbid (.classEq (.cv x) X) (.classMem (.cv x) B) (.classMem X B) p0015
  have p0017 :=
    @g_rspccv (.neg (.classMem (.cv x) B)) (.neg (.classMem X B)) x X A dv_cache_0003
      dv_cache_0001 dv_cache_0004 p0016
  have p0018 :=
    @g_sylbi (.classEq (syn_cin A B) (syn_c0)) (syn_wral x A (.neg (.classMem (.cv x) B)))
      (.imp (.classMem X A) (.neg (.classMem X B))) p0014 p0017
  have p0019 :=
    @g_imp (.classEq (syn_cin A B) (syn_c0)) (.classMem X A) (.neg (.classMem X B)) p0018
  have p0020 :=
    @g_n_3ad2ant3 (syn_wa (.classEq (syn_cin A B) (syn_c0)) (.classMem X A)) (syn_wfn F A)
      (.neg (.classMem X B)) (syn_wfn G B) p0019
  have p0021 :=
    @g_n_3ad2ant2 (syn_wfn G B) (syn_wfn F A) (.classEq (syn_cdm G) B)
      (syn_wa (.classEq (syn_cin A B) (syn_c0)) (.classMem X A)) p0005
  have p0022 :=
    @g_eleq2d
      (syn_w3a (syn_wfn F A) (syn_wfn G B)
        (syn_wa (.classEq (syn_cin A B) (syn_c0)) (.classMem X A)))
      (syn_cdm G) B X p0021
  have p0023 :=
    @g_mtbird
      (syn_w3a (syn_wfn F A) (syn_wfn G B)
        (syn_wa (.classEq (syn_cin A B) (syn_c0)) (.classMem X A)))
      (.classMem X (syn_cdm G)) (.classMem X B) p0020 p0022
  have p0024 := @g_ndmfv X G
  have p0025 :=
    @g_syl
      (syn_w3a (syn_wfn F A) (syn_wfn G B)
        (syn_wa (.classEq (syn_cin A B) (syn_c0)) (.classMem X A)))
      (.neg (.classMem X (syn_cdm G))) (.classEq (syn_cfv G X) (syn_c0)) p0023 p0024
  have p0026 :=
    @g_uneq2d
      (syn_w3a (syn_wfn F A) (syn_wfn G B)
        (syn_wa (.classEq (syn_cin A B) (syn_c0)) (.classMem X A)))
      (syn_cfv G X) (syn_c0) (syn_cfv F X) p0025
  have p0027 :=
    @g_eqtrd
      (syn_w3a (syn_wfn F A) (syn_wfn G B)
        (syn_wa (.classEq (syn_cin A B) (syn_c0)) (.classMem X A)))
      (syn_cfv (syn_cun F G) X) (syn_cun (syn_cfv F X) (syn_cfv G X))
      (syn_cun (syn_cfv F X) (syn_c0)) p0013 p0026
  have p0028 := @g_un0 (syn_cfv F X)
  have p0029 :=
    @g_syl6eq
      (syn_w3a (syn_wfn F A) (syn_wfn G B)
        (syn_wa (.classEq (syn_cin A B) (syn_c0)) (.classMem X A)))
      (syn_cfv (syn_cun F G) X) (syn_cun (syn_cfv F X) (syn_c0)) (syn_cfv F X) p0027 p0028
  exact p0029

@[expose]
noncomputable def g_fvun2 (A : Class) (B : Class) (F : Class) (G : Class) (X : Class) :
    Nominal.NPrf
      (.imp (syn_w3a (syn_wfn F A) (syn_wfn G B)
          (syn_wa (.classEq (syn_cin A B) (syn_c0)) (.classMem X B)))
        (.classEq (syn_cfv (syn_cun F G) X) (syn_cfv G X))) :=
  by
  have p0000 := @g_uncom F G
  have p0001 := @g_fveq1i X (syn_cun F G) (syn_cun G F) p0000
  have p0002 := @g_incom A B
  have p0003 := @g_eqeq1i (syn_cin A B) (syn_cin B A) (syn_c0) p0002
  have p0004 :=
    @g_anbi1i (.classEq (syn_cin A B) (syn_c0)) (.classEq (syn_cin B A) (syn_c0))
      (.classMem X B) p0003
  have p0005 := @g_fvun1 B A G F X
  have p0006 :=
    @g_syl3an3b (syn_wa (.classEq (syn_cin A B) (syn_c0)) (.classMem X B)) (syn_wfn G B)
      (syn_wfn F A) (syn_wa (.classEq (syn_cin B A) (syn_c0)) (.classMem X B))
      (.classEq (syn_cfv (syn_cun G F) X) (syn_cfv G X)) p0004 p0005
  have p0007 :=
    @g_n_3com12 (syn_wfn G B) (syn_wfn F A)
      (syn_wa (.classEq (syn_cin A B) (syn_c0)) (.classMem X B))
      (.classEq (syn_cfv (syn_cun G F) X) (syn_cfv G X)) p0006
  have p0008 :=
    @g_syl5eq
      (syn_w3a (syn_wfn F A) (syn_wfn G B)
        (syn_wa (.classEq (syn_cin A B) (syn_c0)) (.classMem X B)))
      (syn_cfv (syn_cun F G) X) (syn_cfv (syn_cun G F) X) (syn_cfv G X) p0001 p0007
  exact p0008

@[expose]
noncomputable def g_dmfco (A : Class) (F : Class) (G : Class) :
    Nominal.NPrf
      (.imp (syn_wa (syn_wfun G) (.classMem A (syn_cdm G)))
        (syn_wb (.classMem A (syn_cdm (syn_ccom F G)))
          (.classMem (syn_cfv G A) (syn_cdm F)))) :=
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
  have dv_cache_0001 : y ∉ ((syn_cfv G A)).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv, Finset.mem_union,
          fresh_y_not_A, fresh_y_not_G, or_false, not_false_eq_true])
  have dv_cache_0002 : y ∉ ((syn_wbr (syn_cfv G A) F (.cv z))).fv :=
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
  have dv_cache_0003 : y ∉ ((syn_wa (syn_wfun G) (.classMem A (syn_cdm G)))).fv :=
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
  have dv_cache_0004 : z ∉ ((syn_wa (syn_wfun G) (.classMem A (syn_cdm G)))).fv :=
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
  have dv_cache_0006 : z ∉ ((syn_ccom F G)).fv :=
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
  have dv_cache_0011 : z ∉ ((syn_cfv G A)).fv :=
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
  have p0000 := @g_fvex A G
  have p0001 := @g_breq1 (.cv y) (syn_cfv G A) (.cv z) F
  have p0002 :=
    @g_ceqsexv (syn_wbr (.cv y) F (.cv z)) (syn_wbr (syn_cfv G A) F (.cv z)) y
      (syn_cfv G A) dv_cache_0001 dv_cache_0002 p0000 p0001
  have p0003 := @g_eqcom (.cv y) (syn_cfv G A)
  have p0004 := @g_funbrfvb A (.cv y) G
  have p0005 :=
    @g_syl5bb (.classEq (.cv y) (syn_cfv G A)) (.classEq (syn_cfv G A) (.cv y))
      (syn_wa (syn_wfun G) (.classMem A (syn_cdm G))) (syn_wbr A G (.cv y)) p0003 p0004
  have p0006 :=
    @g_anbi1d (syn_wa (syn_wfun G) (.classMem A (syn_cdm G)))
      (.classEq (.cv y) (syn_cfv G A)) (syn_wbr A G (.cv y)) (syn_wbr (.cv y) F (.cv z))
      p0005
  have p0007 :=
    @g_exbidv (syn_wa (syn_wfun G) (.classMem A (syn_cdm G)))
      (syn_wa (.classEq (.cv y) (syn_cfv G A)) (syn_wbr (.cv y) F (.cv z)))
      (syn_wa (syn_wbr A G (.cv y)) (syn_wbr (.cv y) F (.cv z))) y dv_cache_0003 p0006
  have p0008 :=
    @g_syl5rbbr (syn_wbr (syn_cfv G A) F (.cv z))
      (syn_wex y (syn_wa (.classEq (.cv y) (syn_cfv G A)) (syn_wbr (.cv y) F (.cv z))))
      (syn_wa (syn_wfun G) (.classMem A (syn_cdm G)))
      (syn_wex y (syn_wa (syn_wbr A G (.cv y)) (syn_wbr (.cv y) F (.cv z)))) p0002 p0007
  have p0009 :=
    @g_exbidv (syn_wa (syn_wfun G) (.classMem A (syn_cdm G)))
      (syn_wex y (syn_wa (syn_wbr A G (.cv y)) (syn_wbr (.cv y) F (.cv z))))
      (syn_wbr (syn_cfv G A) F (.cv z)) z dv_cache_0004 p0008
  have p0010 := @g_eldm z A (syn_ccom F G) dv_cache_0005 dv_cache_0006
  have p0011 :=
    @g_brco y A (.cv z) F G dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010
  have p0012 :=
    @g_exbii (syn_wbr A (syn_ccom F G) (.cv z))
      (syn_wex y (syn_wa (syn_wbr A G (.cv y)) (syn_wbr (.cv y) F (.cv z)))) z p0011
  have p0013 :=
    @g_bitri (.classMem A (syn_cdm (syn_ccom F G)))
      (syn_wex z (syn_wbr A (syn_ccom F G) (.cv z)))
      (syn_wex z (syn_wex y (syn_wa (syn_wbr A G (.cv y)) (syn_wbr (.cv y) F (.cv z)))))
      p0010 p0012
  have p0014 := @g_eldm z (syn_cfv G A) F dv_cache_0011 dv_cache_0012
  have p0015 :=
    @g_n_3bitr4g (syn_wa (syn_wfun G) (.classMem A (syn_cdm G)))
      (syn_wex z (syn_wex y (syn_wa (syn_wbr A G (.cv y)) (syn_wbr (.cv y) F (.cv z)))))
      (syn_wex z (syn_wbr (syn_cfv G A) F (.cv z))) (.classMem A (syn_cdm (syn_ccom F G)))
      (.classMem (syn_cfv G A) (syn_cdm F)) p0009 p0013 p0014
  exact p0015

@[expose]
noncomputable def g_fvco2 (A : Class) (C : Class) (F : Class) (G : Class) :
    Nominal.NPrf
      (.imp (syn_wa (syn_wfn G A) (.classMem C A))
        (.classEq (syn_cfv (syn_ccom F G) C) (syn_cfv F (syn_cfv G C)))) :=
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
  have dv_cache_0001 : y ∉ ((syn_wa (syn_wfn G A) (.classMem C A))).fv := by
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
  have dv_cache_0002 : y ∉ ((syn_wbr C (syn_ccom F G) (.cv z))).fv :=
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
  have dv_cache_0005 : z ∉ ((syn_ccom F G)).fv :=
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
  have dv_cache_0006 : y ∉ ((syn_wbr (syn_cfv G C) F (.cv z))).fv :=
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
  have dv_cache_0007 : z ∉ ((syn_cfv G C)).fv :=
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
  have p0000 := @g_fnsnfv A C G
  have p0001 :=
    @g_imaeq2d (syn_wa (syn_wfn G A) (.classMem C A)) (syn_csn (syn_cfv G C))
      (syn_cima G (syn_csn C)) F p0000
  have p0002 := @g_imaco F G (syn_csn C)
  have p0003 :=
    @g_syl6reqr (syn_wa (syn_wfn G A) (.classMem C A))
      (syn_cima F (syn_csn (syn_cfv G C))) (syn_cima F (syn_cima G (syn_csn C)))
      (syn_cima (syn_ccom F G) (syn_csn C)) p0001 p0002
  have p0004 :=
    @g_eqeq1d (syn_wa (syn_wfn G A) (.classMem C A)) (syn_cima (syn_ccom F G) (syn_csn C))
      (syn_cima F (syn_csn (syn_cfv G C))) (syn_csn (.cv y)) p0003
  have p0005 :=
    @g_abbidv (syn_wa (syn_wfn G A) (.classMem C A))
      (.classEq (syn_cima (syn_ccom F G) (syn_csn C)) (syn_csn (.cv y)))
      (.classEq (syn_cima F (syn_csn (syn_cfv G C))) (syn_csn (.cv y))) y dv_cache_0001
      p0004
  have p0006 :=
    @g_unieqd (syn_wa (syn_wfn G A) (.classMem C A))
      (.cab y (.classEq (syn_cima (syn_ccom F G) (syn_csn C)) (syn_csn (.cv y))))
      (.cab y (.classEq (syn_cima F (syn_csn (syn_cfv G C))) (syn_csn (.cv y)))) p0005
  have p0007 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominal_df_iota
      (syn_wbr C (syn_ccom F G) (.cv z)) z y dv_cache_0002 dv_cache_0003
  have p0008 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominal_df_fv z C
      (syn_ccom F G) dv_cache_0004 dv_cache_0005
  have p0009 := @g_imasn z C (syn_ccom F G) dv_cache_0004 dv_cache_0005
  have p0010 :=
    @g_eqeq1i (syn_cima (syn_ccom F G) (syn_csn C))
      (.cab z (syn_wbr C (syn_ccom F G) (.cv z))) (syn_csn (.cv y)) p0009
  have p0011 :=
    @g_abbii (.classEq (syn_cima (syn_ccom F G) (syn_csn C)) (syn_csn (.cv y)))
      (.classEq (.cab z (syn_wbr C (syn_ccom F G) (.cv z))) (syn_csn (.cv y))) y p0010
  have p0012 :=
    @g_unieqi (.cab y (.classEq (syn_cima (syn_ccom F G) (syn_csn C)) (syn_csn (.cv y))))
      (.cab y (.classEq (.cab z (syn_wbr C (syn_ccom F G) (.cv z))) (syn_csn (.cv y))))
      p0011
  have p0013 :=
    @g_n_3eqtr4i (syn_cio z (syn_wbr C (syn_ccom F G) (.cv z)))
      (syn_cuni
        (.cab y (.classEq (.cab z (syn_wbr C (syn_ccom F G) (.cv z))) (syn_csn (.cv y)))))
      (syn_cfv (syn_ccom F G) C)
      (syn_cuni (.cab y (.classEq (syn_cima (syn_ccom F G) (syn_csn C)) (syn_csn (.cv y)))))
      p0007 p0008 p0012
  have p0014 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominal_df_iota
      (syn_wbr (syn_cfv G C) F (.cv z)) z y dv_cache_0006 dv_cache_0003
  have p0015 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominal_df_fv z (syn_cfv G C) F
      dv_cache_0007 dv_cache_0008
  have p0016 := @g_imasn z (syn_cfv G C) F dv_cache_0007 dv_cache_0008
  have p0017 :=
    @g_eqeq1i (syn_cima F (syn_csn (syn_cfv G C)))
      (.cab z (syn_wbr (syn_cfv G C) F (.cv z))) (syn_csn (.cv y)) p0016
  have p0018 :=
    @g_abbii (.classEq (syn_cima F (syn_csn (syn_cfv G C))) (syn_csn (.cv y)))
      (.classEq (.cab z (syn_wbr (syn_cfv G C) F (.cv z))) (syn_csn (.cv y))) y p0017
  have p0019 :=
    @g_unieqi (.cab y (.classEq (syn_cima F (syn_csn (syn_cfv G C))) (syn_csn (.cv y))))
      (.cab y (.classEq (.cab z (syn_wbr (syn_cfv G C) F (.cv z))) (syn_csn (.cv y))))
      p0018
  have p0020 :=
    @g_n_3eqtr4i (syn_cio z (syn_wbr (syn_cfv G C) F (.cv z)))
      (syn_cuni
        (.cab y (.classEq (.cab z (syn_wbr (syn_cfv G C) F (.cv z))) (syn_csn (.cv y)))))
      (syn_cfv F (syn_cfv G C))
      (syn_cuni (.cab y (.classEq (syn_cima F (syn_csn (syn_cfv G C))) (syn_csn (.cv y)))))
      p0014 p0015 p0019
  have p0021 :=
    @g_n_3eqtr4g (syn_wa (syn_wfn G A) (.classMem C A))
      (syn_cuni (.cab y (.classEq (syn_cima (syn_ccom F G) (syn_csn C)) (syn_csn (.cv y)))))
      (syn_cuni (.cab y (.classEq (syn_cima F (syn_csn (syn_cfv G C))) (syn_csn (.cv y)))))
      (syn_cfv (syn_ccom F G) C) (syn_cfv F (syn_cfv G C)) p0006 p0013 p0020
  exact p0021

@[expose]
noncomputable def g_fvco (A : Class) (F : Class) (G : Class) :
    Nominal.NPrf
      (.imp (syn_wa (syn_wfun G) (.classMem A (syn_cdm G)))
        (.classEq (syn_cfv (syn_ccom F G) A) (syn_cfv F (syn_cfv G A)))) :=
  by
  have p0000 := @g_funfn G
  have p0001 := @g_fvco2 (syn_cdm G) A F G
  have p0002 :=
    @g_sylanb (syn_wfun G) (syn_wfn G (syn_cdm G)) (.classMem A (syn_cdm G))
      (.classEq (syn_cfv (syn_ccom F G) A) (syn_cfv F (syn_cfv G A))) p0000 p0001
  exact p0002

@[expose]
noncomputable def g_fvco3 (A : Class) (B : Class) (C : Class) (F : Class) (G : Class) :
    Nominal.NPrf
      (.imp (syn_wa (syn_wf G A B) (.classMem C A))
        (.classEq (syn_cfv (syn_ccom F G) C) (syn_cfv F (syn_cfv G C)))) :=
  by
  have p0000 := @g_ffn A B G
  have p0001 := @g_fvco2 A C F G
  have p0002 :=
    @g_sylan (syn_wf G A B) (syn_wfn G A) (.classMem C A)
      (.classEq (syn_cfv (syn_ccom F G) C) (syn_cfv F (syn_cfv G C))) p0000 p0001
  exact p0002

@[expose]
noncomputable def g_fvopab3ig (ph : Wff) (ps : Wff) (ch : Wff) (x : Var) (y : Var)
    (A : Class) (B : Class) (C : Class) (D : Class) (F : Class) (dv_A_x : x ∉ A.fv)
    (dv_A_y : y ∉ A.fv) (dv_B_x : x ∉ B.fv) (dv_B_y : y ∉ B.fv) (dv_C_x : x ∉ C.fv)
    (dv_C_y : y ∉ C.fv) (dv_ch_x : x ∉ ch.fv) (dv_ch_y : y ∉ ch.fv) (dv_x_y : x ≠ y)
    (hyp_fvopab3ig_1 : Nominal.NPrf (.imp (.classEq (.cv x) A) (syn_wb ph ps)))
    (hyp_fvopab3ig_2 : Nominal.NPrf (.imp (.classEq (.cv y) B) (syn_wb ps ch)))
    (hyp_fvopab3ig_3 : Nominal.NPrf (.imp (.classMem (.cv x) C) (syn_wmo y ph)))
    (hyp_fvopab3ig_4 :
      Nominal.NPrf (.classEq F (syn_copab x y (syn_wa (.classMem (.cv x) C) ph)))) :
    Nominal.NPrf
      (.imp (syn_wa (.classMem A C) (.classMem B D)) (.imp ch (.classEq (syn_cfv F A) B))) :=
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
  have dv_cache_0007 : x ∉ ((syn_wa (.classMem A C) ch)).fv :=
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
  have dv_cache_0008 : y ∉ ((syn_wa (.classMem A C) ch)).fv :=
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
  have p0000 := @g_funopab (syn_wa (.classMem (.cv x) C) ph) x y dv_cache_0001
  have p0001 := @g_moanimv (.classMem (.cv x) C) ph y dv_cache_0002
  have p0002 :=
    @g_mpbir (syn_wmo y (syn_wa (.classMem (.cv x) C) ph))
      (.imp (.classMem (.cv x) C) (syn_wmo y ph)) hyp_fvopab3ig_3 p0001
  have p0003 :=
    @g_mpgbir (syn_wfun (syn_copab x y (syn_wa (.classMem (.cv x) C) ph)))
      (syn_wmo y (syn_wa (.classMem (.cv x) C) ph)) x p0000 p0002
  have p0004 := @g_simpl (.classMem A C) (.classMem B D)
  have p0005 := @g_eleq1 (.cv x) A C
  have p0006 :=
    @g_anbi12d (.classEq (.cv x) A) (.classMem (.cv x) C) (.classMem A C) ph ps p0005
      hyp_fvopab3ig_1
  have p0007 := @g_anbi2d (.classEq (.cv y) B) ps ch (.classMem A C) hyp_fvopab3ig_2
  have p0008 :=
    @g_opelopabg (syn_wa (.classMem (.cv x) C) ph) (syn_wa (.classMem A C) ps)
      (syn_wa (.classMem A C) ch) x y A B C D dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0001 p0006 p0007
  have p0009 :=
    @g_biimprd (syn_wa (.classMem A C) (.classMem B D))
      (.classMem (syn_cop A B) (syn_copab x y (syn_wa (.classMem (.cv x) C) ph)))
      (syn_wa (.classMem A C) ch) p0008
  have p0010 :=
    @g_mpand (syn_wa (.classMem A C) (.classMem B D)) (.classMem A C) ch
      (.classMem (syn_cop A B) (syn_copab x y (syn_wa (.classMem (.cv x) C) ph))) p0004
      p0009
  have p0011 := @g_funopfv A B (syn_copab x y (syn_wa (.classMem (.cv x) C) ph))
  have p0012 :=
    @g_ee02 (syn_wfun (syn_copab x y (syn_wa (.classMem (.cv x) C) ph)))
      (syn_wa (.classMem A C) (.classMem B D)) ch
      (.classMem (syn_cop A B) (syn_copab x y (syn_wa (.classMem (.cv x) C) ph)))
      (.classEq (syn_cfv (syn_copab x y (syn_wa (.classMem (.cv x) C) ph)) A) B) p0003
      p0010 p0011
  have p0013 :=
    @g_fveq1i A F (syn_copab x y (syn_wa (.classMem (.cv x) C) ph)) hyp_fvopab3ig_4
  have p0014 :=
    @g_eqeq1i (syn_cfv F A) (syn_cfv (syn_copab x y (syn_wa (.classMem (.cv x) C) ph)) A)
      B p0013
  have p0015 :=
    @g_syl6ibr (syn_wa (.classMem A C) (.classMem B D)) ch
      (.classEq (syn_cfv (syn_copab x y (syn_wa (.classMem (.cv x) C) ph)) A) B)
      (.classEq (syn_cfv F A) B) p0012 p0014
  exact p0015

@[expose]
noncomputable def g_fvopab4g (x : Var) (y : Var) (A : Class) (B : Class) (C : Class)
    (D : Class) (R : Class) (F : Class) (dv_A_x : x ∉ A.fv) (dv_A_y : y ∉ A.fv)
    (dv_B_y : y ∉ B.fv) (dv_C_x : x ∉ C.fv) (dv_C_y : y ∉ C.fv) (dv_D_x : x ∉ D.fv)
    (dv_D_y : y ∉ D.fv) (dv_x_y : x ≠ y)
    (hyp_fvopab4g_1 : Nominal.NPrf (.imp (.classEq (.cv x) A) (.classEq B C)))
    (hyp_fvopab4g_2 : Nominal.NPrf (.classEq F
          (syn_copab x y (syn_wa (.classMem (.cv x) D) (.classEq (.cv y) B))))) :
    Nominal.NPrf
      (.imp (syn_wa (.classMem A D) (.classMem C R)) (.classEq (syn_cfv F A) C)) :=
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
  have p0000 := @g_eqid C
  have p0001 := @g_eqeq2d (.classEq (.cv x) A) B C (.cv y) hyp_fvopab4g_1
  have p0002 := @g_eqeq1 (.cv y) C C
  have p0003 := @g_moeq y B dv_cache_0001
  have p0004 := @g_a1i (syn_wmo y (.classEq (.cv y) B)) (.classMem (.cv x) D) p0003
  have p0005 :=
    @g_fvopab3ig (.classEq (.cv y) B) (.classEq (.cv y) C) (.classEq C C) x y A C D R F
      dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007
      dv_cache_0008 dv_cache_0009 dv_cache_0010 p0001 p0002 p0004 hyp_fvopab4g_2
  have p0006 :=
    @g_mpi (syn_wa (.classMem A D) (.classMem C R)) (.classEq C C)
      (.classEq (syn_cfv F A) C) p0000 p0005
  exact p0006

@[expose]
noncomputable def g_fvopab4 (x : Var) (y : Var) (A : Class) (B : Class) (C : Class)
    (D : Class) (F : Class) (dv_A_x : x ∉ A.fv) (dv_A_y : y ∉ A.fv) (dv_B_y : y ∉ B.fv)
    (dv_C_x : x ∉ C.fv) (dv_C_y : y ∉ C.fv) (dv_D_x : x ∉ D.fv) (dv_D_y : y ∉ D.fv)
    (dv_x_y : x ≠ y)
    (hyp_fvopab4g_1 : Nominal.NPrf (.imp (.classEq (.cv x) A) (.classEq B C)))
    (hyp_fvopab4g_2 : Nominal.NPrf
        (.classEq F (syn_copab x y (syn_wa (.classMem (.cv x) D) (.classEq (.cv y) B)))))
    (hyp_fvopab4_3 : Nominal.NPrf (.classMem C (syn_cvv))) :
    Nominal.NPrf (.imp (.classMem A D) (.classEq (syn_cfv F A) C)) :=
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
    @g_fvopab4g x y A B C D (syn_cvv) F dv_cache_0001 dv_cache_0002 dv_cache_0003
      dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 hyp_fvopab4g_1
      hyp_fvopab4g_2
  have p0001 :=
    @g_mpan2 (.classMem A D) (.classMem C (syn_cvv)) (.classEq (syn_cfv F A) C)
      hyp_fvopab4_3 p0000
  exact p0001

@[expose]
noncomputable def g_eqfnfv (x : Var) (A : Class) (F : Class) (G : Class)
    (dv_A_x : x ∉ A.fv) (dv_F_x : x ∉ F.fv) (dv_G_x : x ∉ G.fv) :
    Nominal.NPrf
      (.imp (syn_wa (syn_wfn F A) (syn_wfn G A)) (syn_wb (.classEq F G)
          (syn_wral x A (.classEq (syn_cfv F (.cv x)) (syn_cfv G (.cv x)))))) :=
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
  have dv_cache_0002 : y ∉ ((syn_wa (syn_wfn F A) (syn_wfn G A))).fv :=
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
      ((Wff.imp (.classMem (.cv x) A) (.classEq (syn_cfv F (.cv x)) (syn_cfv G (.cv x))))).fv :=
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
  have dv_cache_0004 : x ∉ ((syn_wa (syn_wfn F A) (syn_wfn G A))).fv :=
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
  have p0000 := @g_fveq1 (.cv x) F G
  have p0001 :=
    @g_ralrimivw (.classEq F G) (.classEq (syn_cfv F (.cv x)) (syn_cfv G (.cv x))) x A
      dv_cache_0001 p0000
  have p0002 :=
    @g_pm2_27 (.classMem (.cv x) A) (.classEq (syn_cfv F (.cv x)) (syn_cfv G (.cv x)))
  have p0003 :=
    @g_adantl (.classMem (.cv x) A)
      (.imp (.imp (.classMem (.cv x) A) (.classEq (syn_cfv F (.cv x)) (syn_cfv G (.cv x))))
        (.classEq (syn_cfv F (.cv x)) (syn_cfv G (.cv x))))
      (syn_wa (syn_wfn F A) (syn_wfn G A)) p0002
  have p0004 := @g_eqeq1 (syn_cfv F (.cv x)) (syn_cfv G (.cv x)) (.cv y)
  have p0005 := @g_fnopfvb A (.cv x) (.cv y) F
  have p0006 :=
    @g_adantlr (syn_wfn F A) (.classMem (.cv x) A)
      (syn_wb (.classEq (syn_cfv F (.cv x)) (.cv y)) (.classMem (syn_cop (.cv x) (.cv y)) F))
      (syn_wfn G A) p0005
  have p0007 := @g_fnopfvb A (.cv x) (.cv y) G
  have p0008 :=
    @g_adantll (syn_wfn G A) (.classMem (.cv x) A)
      (syn_wb (.classEq (syn_cfv G (.cv x)) (.cv y)) (.classMem (syn_cop (.cv x) (.cv y)) G))
      (syn_wfn F A) p0007
  have p0009 :=
    @g_bibi12d (syn_wa (syn_wa (syn_wfn F A) (syn_wfn G A)) (.classMem (.cv x) A))
      (.classEq (syn_cfv F (.cv x)) (.cv y)) (.classMem (syn_cop (.cv x) (.cv y)) F)
      (.classEq (syn_cfv G (.cv x)) (.cv y)) (.classMem (syn_cop (.cv x) (.cv y)) G) p0006
      p0008
  have p0010 :=
    @g_syl5ib (.classEq (syn_cfv F (.cv x)) (syn_cfv G (.cv x)))
      (syn_wb (.classEq (syn_cfv F (.cv x)) (.cv y)) (.classEq (syn_cfv G (.cv x)) (.cv y)))
      (syn_wa (syn_wa (syn_wfn F A) (syn_wfn G A)) (.classMem (.cv x) A))
      (syn_wb (.classMem (syn_cop (.cv x) (.cv y)) F) (.classMem (syn_cop (.cv x) (.cv y)) G))
      p0004 p0009
  have p0011 :=
    @g_syld (syn_wa (syn_wa (syn_wfn F A) (syn_wfn G A)) (.classMem (.cv x) A))
      (.imp (.classMem (.cv x) A) (.classEq (syn_cfv F (.cv x)) (syn_cfv G (.cv x))))
      (.classEq (syn_cfv F (.cv x)) (syn_cfv G (.cv x)))
      (syn_wb (.classMem (syn_cop (.cv x) (.cv y)) F) (.classMem (syn_cop (.cv x) (.cv y)) G))
      p0003 p0010
  have p0012 :=
    @g_expcom (syn_wa (syn_wfn F A) (syn_wfn G A)) (.classMem (.cv x) A)
      (.imp (.imp (.classMem (.cv x) A) (.classEq (syn_cfv F (.cv x)) (syn_cfv G (.cv x))))
        (syn_wb (.classMem (syn_cop (.cv x) (.cv y)) F)
          (.classMem (syn_cop (.cv x) (.cv y)) G)))
      p0011
  have p0013 := @g_opeldm (.cv x) (.cv y) F
  have p0014 := @g_fndm A F
  have p0015 := @g_eleq2d (syn_wfn F A) (syn_cdm F) A (.cv x) p0014
  have p0016 :=
    @g_syl5ib (.classMem (syn_cop (.cv x) (.cv y)) F) (.classMem (.cv x) (syn_cdm F))
      (syn_wfn F A) (.classMem (.cv x) A) p0013 p0015
  have p0017 :=
    @g_adantr (syn_wfn F A)
      (.imp (.classMem (syn_cop (.cv x) (.cv y)) F) (.classMem (.cv x) A)) (syn_wfn G A)
      p0016
  have p0018 :=
    @g_con3d (syn_wa (syn_wfn F A) (syn_wfn G A)) (.classMem (syn_cop (.cv x) (.cv y)) F)
      (.classMem (.cv x) A) p0017
  have p0019 :=
    @g_impcom (syn_wa (syn_wfn F A) (syn_wfn G A)) (.neg (.classMem (.cv x) A))
      (.neg (.classMem (syn_cop (.cv x) (.cv y)) F)) p0018
  have p0020 := @g_opeldm (.cv x) (.cv y) G
  have p0021 := @g_fndm A G
  have p0022 := @g_eleq2d (syn_wfn G A) (syn_cdm G) A (.cv x) p0021
  have p0023 :=
    @g_syl5ib (.classMem (syn_cop (.cv x) (.cv y)) G) (.classMem (.cv x) (syn_cdm G))
      (syn_wfn G A) (.classMem (.cv x) A) p0020 p0022
  have p0024 :=
    @g_adantl (syn_wfn G A)
      (.imp (.classMem (syn_cop (.cv x) (.cv y)) G) (.classMem (.cv x) A)) (syn_wfn F A)
      p0023
  have p0025 :=
    @g_con3d (syn_wa (syn_wfn F A) (syn_wfn G A)) (.classMem (syn_cop (.cv x) (.cv y)) G)
      (.classMem (.cv x) A) p0024
  have p0026 :=
    @g_impcom (syn_wa (syn_wfn F A) (syn_wfn G A)) (.neg (.classMem (.cv x) A))
      (.neg (.classMem (syn_cop (.cv x) (.cv y)) G)) p0025
  have p0027 :=
    @g_n_2falsed
      (syn_wa (.neg (.classMem (.cv x) A)) (syn_wa (syn_wfn F A) (syn_wfn G A)))
      (.classMem (syn_cop (.cv x) (.cv y)) F) (.classMem (syn_cop (.cv x) (.cv y)) G)
      p0019 p0026
  have p0028 :=
    @g_ex (.neg (.classMem (.cv x) A)) (syn_wa (syn_wfn F A) (syn_wfn G A))
      (syn_wb (.classMem (syn_cop (.cv x) (.cv y)) F) (.classMem (syn_cop (.cv x) (.cv y)) G))
      p0027
  have p0029 :=
    @g_a1dd (.neg (.classMem (.cv x) A)) (syn_wa (syn_wfn F A) (syn_wfn G A))
      (syn_wb (.classMem (syn_cop (.cv x) (.cv y)) F) (.classMem (syn_cop (.cv x) (.cv y)) G))
      (.imp (.classMem (.cv x) A) (.classEq (syn_cfv F (.cv x)) (syn_cfv G (.cv x))))
      p0028
  have p0030 :=
    @g_pm2_61i (.classMem (.cv x) A)
      (.imp (syn_wa (syn_wfn F A) (syn_wfn G A)) (.imp
          (.imp (.classMem (.cv x) A) (.classEq (syn_cfv F (.cv x)) (syn_cfv G (.cv x))))
          (syn_wb (.classMem (syn_cop (.cv x) (.cv y)) F)
            (.classMem (syn_cop (.cv x) (.cv y)) G))))
      p0012 p0029
  have p0031 :=
    @g_alrimdv (syn_wa (syn_wfn F A) (syn_wfn G A))
      (.imp (.classMem (.cv x) A) (.classEq (syn_cfv F (.cv x)) (syn_cfv G (.cv x))))
      (syn_wb (.classMem (syn_cop (.cv x) (.cv y)) F) (.classMem (syn_cop (.cv x) (.cv y)) G))
      y dv_cache_0002 dv_cache_0003 p0030
  have p0032 :=
    @g_alimdv (syn_wa (syn_wfn F A) (syn_wfn G A))
      (.imp (.classMem (.cv x) A) (.classEq (syn_cfv F (.cv x)) (syn_cfv G (.cv x))))
      (.all y (syn_wb (.classMem (syn_cop (.cv x) (.cv y)) F)
          (.classMem (syn_cop (.cv x) (.cv y)) G)))
      x dv_cache_0004 p0031
  have p0033 :=
    (Nominal.biimpRefl (syn_wral x A (.classEq (syn_cfv F (.cv x)) (syn_cfv G (.cv x)))))
  have p0034 :=
    @g_eqrel x y F G dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009
  have p0035 :=
    @g_n_3imtr4g (syn_wa (syn_wfn F A) (syn_wfn G A))
      (.all x (.imp (.classMem (.cv x) A) (.classEq (syn_cfv F (.cv x)) (syn_cfv G (.cv x)))))
      (.all x (.all y (syn_wb (.classMem (syn_cop (.cv x) (.cv y)) F)
            (.classMem (syn_cop (.cv x) (.cv y)) G))))
      (syn_wral x A (.classEq (syn_cfv F (.cv x)) (syn_cfv G (.cv x)))) (.classEq F G)
      p0032 p0033 p0034
  have p0036 :=
    @g_impbid2 (syn_wa (syn_wfn F A) (syn_wfn G A)) (.classEq F G)
      (syn_wral x A (.classEq (syn_cfv F (.cv x)) (syn_cfv G (.cv x)))) p0001 p0035
  exact p0036


end NFChoice.DirectNominalPrf.WPPReplay

end
