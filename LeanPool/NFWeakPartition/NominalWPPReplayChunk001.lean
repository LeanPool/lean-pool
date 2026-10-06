/-
Copyright (c) 2026 Elliot Glazer and NFNotWPP contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elliot Glazer and NFNotWPP contributors
-/

module

public import LeanPool.NFWeakPartition.NominalDefinitionRefl
public import LeanPool.NFWeakPartition.NominalAlphaRepairedDfNfc001
public import LeanPool.NFWeakPartition.NominalAlphaRepairedBase001003V
public import LeanPool.NFWeakPartition.NominalAlphaRepairedBase001004Csb
public import LeanPool.NFWeakPartition.NominalAlphaRepairedBase001005Nin
public import LeanPool.NFWeakPartition.NominalAlphaRepairedBase001006If
public import LeanPool.NFWeakPartition.NominalAlphaRepairedBase001007Pw
public import LeanPool.NFWeakPartition.NominalAlphaRepairedBase001008Sn
public import LeanPool.NFWeakPartition.NominalAlphaRepairedBase001009Uni
public import LeanPool.NFWeakPartition.NominalAlphaRepairedBase001010Int
public import LeanPool.NFWeakPartition.NominalAlphaRepairedBase001011Iun
public import LeanPool.NFWeakPartition.NominalAlphaRepairedBase001012Leaf1c
public import LeanPool.NFWeakPartition.NominalNFLiteralBaseFour
public import LeanPool.NFWeakPartition.NominalDefinitionLeafHandlersObjExtCompat001
public import LeanPool.NFWeakPartition.NominalRecanonTransportCompat001

/-! NF weak partition development: NominalWPPReplayChunk001. -/


public section


namespace NFChoice.DirectNominalPrf.WPPReplay

open scoped Fol
open NFChoice.Foundation
open NFChoice.SemanticCore
open NFChoice.ReplaySupport
open NFChoice.Compiler.CompactSourceSyntax

/-- Checked nominal proof certificate identified upstream as `g_a1ii`. -/
@[expose]
noncomputable def gA1ii (ph : Wff) (ps : Wff) (hyp_a1ii_1 : Nominal.NPrf ph)
    (_hyp_a1ii_2 : Nominal.NPrf ps) : Nominal.NPrf ph :=
  by
  let proofSupport : Finset Var := ph.fv ∪ ps.fv
  exact hyp_a1ii_1

/-- Checked nominal proof certificate identified upstream as `g_mp2b`. -/
@[expose]
noncomputable def gMp2b (ph : Wff) (ps : Wff) (ch : Wff) (hyp_mp2b_1 : Nominal.NPrf ph)
    (hyp_mp2b_2 : Nominal.NPrf (.imp ph ps)) (hyp_mp2b_3 : Nominal.NPrf (.imp ps ch)) :
    Nominal.NPrf ch :=
  by
  have p0000 := Nominal.mp hyp_mp2b_1 hyp_mp2b_2
  have p0001 := Nominal.mp p0000 hyp_mp2b_3
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_a1i`. -/
@[expose]
noncomputable def gA1i (ph : Wff) (ps : Wff) (hyp_a1i_1 : Nominal.NPrf ph) :
    Nominal.NPrf (.imp ps ph) :=
  by
  have p0000 := Nominal.ax1 ph ps
  have p0001 := Nominal.mp hyp_a1i_1 p0000
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_a2i`. -/
@[expose]
noncomputable def gA2i (ph : Wff) (ps : Wff) (ch : Wff)
    (hyp_a2i_1 : Nominal.NPrf (.imp ph (.imp ps ch))) :
    Nominal.NPrf (.imp (.imp ph ps) (.imp ph ch)) :=
  by
  have p0000 := Nominal.ax2 ph ps ch
  have p0001 := Nominal.mp hyp_a2i_1 p0000
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_imim2i`. -/
@[expose]
noncomputable def gImim2i (ph : Wff) (ps : Wff) (ch : Wff)
    (hyp_imim2i_1 : Nominal.NPrf (.imp ph ps)) :
    Nominal.NPrf (.imp (.imp ch ph) (.imp ch ps)) :=
  by
  have p0000 := @gA1i (.imp ph ps) ch hyp_imim2i_1
  have p0001 := @gA2i ch ph ps p0000
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_mpd`. -/
@[expose]
noncomputable def gMpd (ph : Wff) (ps : Wff) (ch : Wff)
    (hyp_mpd_1 : Nominal.NPrf (.imp ph ps))
    (hyp_mpd_2 : Nominal.NPrf (.imp ph (.imp ps ch))) : Nominal.NPrf (.imp ph ch) :=
  by
  have p0000 := @gA2i ph ps ch hyp_mpd_2
  have p0001 := Nominal.mp hyp_mpd_1 p0000
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_syl`. -/
@[expose]
noncomputable def gSyl (ph : Wff) (ps : Wff) (ch : Wff)
    (hyp_syl_1 : Nominal.NPrf (.imp ph ps)) (hyp_syl_2 : Nominal.NPrf (.imp ps ch)) :
    Nominal.NPrf (.imp ph ch) :=
  by
  have p0000 := @gA1i (.imp ps ch) ph hyp_syl_2
  have p0001 := @gMpd ph ps ch hyp_syl_1 p0000
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_mpi`. -/
@[expose]
noncomputable def gMpi (ph : Wff) (ps : Wff) (ch : Wff) (hyp_mpi_1 : Nominal.NPrf ps)
    (hyp_mpi_2 : Nominal.NPrf (.imp ph (.imp ps ch))) : Nominal.NPrf (.imp ph ch) :=
  by
  have p0000 := @gA1i ps ph hyp_mpi_1
  have p0001 := @gMpd ph ps ch p0000 hyp_mpi_2
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_mp2`. -/
@[expose]
noncomputable def gMp2 (ph : Wff) (ps : Wff) (ch : Wff) (hyp_mp2_1 : Nominal.NPrf ph)
    (hyp_mp2_2 : Nominal.NPrf ps) (hyp_mp2_3 : Nominal.NPrf (.imp ph (.imp ps ch))) :
    Nominal.NPrf ch :=
  by
  have p0000 := @gMpi ph ps ch hyp_mp2_2 hyp_mp2_3
  have p0001 := Nominal.mp hyp_mp2_1 p0000
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_n_3syl`. -/
@[expose]
noncomputable def gN3syl (ph : Wff) (ps : Wff) (ch : Wff) (th : Wff)
    (hyp_n_3syl_1 : Nominal.NPrf (.imp ph ps)) (hyp_n_3syl_2 : Nominal.NPrf (.imp ps ch))
    (hyp_n_3syl_3 : Nominal.NPrf (.imp ch th)) : Nominal.NPrf (.imp ph th) :=
  by
  have p0000 := @gSyl ph ps ch hyp_n_3syl_1 hyp_n_3syl_2
  have p0001 := @gSyl ph ch th p0000 hyp_n_3syl_3
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_id`. -/
@[expose]
noncomputable def gId (ph : Wff) : Nominal.NPrf (.imp ph ph) :=
  by
  have p0000 := Nominal.ax1 ph ph
  have p0001 := Nominal.ax1 ph (.imp ph ph)
  have p0002 := @gMpd ph (.imp ph ph) ph p0000 p0001
  exact p0002

/-- Checked nominal proof certificate identified upstream as `g_idd`. -/
@[expose]
noncomputable def gIdd (ph : Wff) (ps : Wff) : Nominal.NPrf (.imp ph (.imp ps ps)) :=
  by
  have p0000 := @gId ps
  have p0001 := @gA1i (.imp ps ps) ph p0000
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_a1d`. -/
@[expose]
noncomputable def gA1d (ph : Wff) (ps : Wff) (ch : Wff)
    (hyp_a1d_1 : Nominal.NPrf (.imp ph ps)) : Nominal.NPrf (.imp ph (.imp ch ps)) :=
  by
  have p0000 := Nominal.ax1 ps ch
  have p0001 := @gSyl ph ps (.imp ch ps) hyp_a1d_1 p0000
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_a2d`. -/
@[expose]
noncomputable def gA2d (ph : Wff) (ps : Wff) (ch : Wff) (th : Wff)
    (hyp_a2d_1 : Nominal.NPrf (.imp ph (.imp ps (.imp ch th)))) :
    Nominal.NPrf (.imp ph (.imp (.imp ps ch) (.imp ps th))) :=
  by
  have p0000 := Nominal.ax2 ps ch th
  have p0001 :=
    @gSyl ph (.imp ps (.imp ch th)) (.imp (.imp ps ch) (.imp ps th)) hyp_a2d_1 p0000
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_n_2a1i`. -/
@[expose]
noncomputable def gN2a1i (ph : Wff) (ps : Wff) (ch : Wff)
    (hyp_n_2a1i_1 : Nominal.NPrf ch) : Nominal.NPrf (.imp ph (.imp ps ch)) :=
  by
  have p0000 := @gA1i ch ph hyp_n_2a1i_1
  have p0001 := @gA1d ph ch ps p0000
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_sylcom`. -/
@[expose]
noncomputable def gSylcom (ph : Wff) (ps : Wff) (ch : Wff) (th : Wff)
    (hyp_sylcom_1 : Nominal.NPrf (.imp ph (.imp ps ch)))
    (hyp_sylcom_2 : Nominal.NPrf (.imp ps (.imp ch th))) :
    Nominal.NPrf (.imp ph (.imp ps th)) :=
  by
  have p0000 := @gA2i ps ch th hyp_sylcom_2
  have p0001 := @gSyl ph (.imp ps ch) (.imp ps th) hyp_sylcom_1 p0000
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_syl5com`. -/
@[expose]
noncomputable def gSyl5com (ph : Wff) (ps : Wff) (ch : Wff) (th : Wff)
    (hyp_syl5com_1 : Nominal.NPrf (.imp ph ps))
    (hyp_syl5com_2 : Nominal.NPrf (.imp ch (.imp ps th))) :
    Nominal.NPrf (.imp ph (.imp ch th)) :=
  by
  have p0000 := @gA1d ph ps ch hyp_syl5com_1
  have p0001 := @gSylcom ph ch ps th p0000 hyp_syl5com_2
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_com12`. -/
@[expose]
noncomputable def gCom12 (ph : Wff) (ps : Wff) (ch : Wff)
    (hyp_com12_1 : Nominal.NPrf (.imp ph (.imp ps ch))) :
    Nominal.NPrf (.imp ps (.imp ph ch)) :=
  by
  have p0000 := @gId ps
  have p0001 := @gSyl5com ps ps ph ch p0000 hyp_com12_1
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_syl5`. -/
@[expose]
noncomputable def gSyl5 (ph : Wff) (ps : Wff) (ch : Wff) (th : Wff)
    (hyp_syl5_1 : Nominal.NPrf (.imp ph ps))
    (hyp_syl5_2 : Nominal.NPrf (.imp ch (.imp ps th))) :
    Nominal.NPrf (.imp ch (.imp ph th)) :=
  by
  have p0000 := @gSyl5com ph ps ch th hyp_syl5_1 hyp_syl5_2
  have p0001 := @gCom12 ph ch th p0000
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_syl6`. -/
@[expose]
noncomputable def gSyl6 (ph : Wff) (ps : Wff) (ch : Wff) (th : Wff)
    (hyp_syl6_1 : Nominal.NPrf (.imp ph (.imp ps ch)))
    (hyp_syl6_2 : Nominal.NPrf (.imp ch th)) : Nominal.NPrf (.imp ph (.imp ps th)) :=
  by
  have p0000 := @gA1i (.imp ch th) ps hyp_syl6_2
  have p0001 := @gSylcom ph ps ch th hyp_syl6_1 p0000
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_syl56`. -/
@[expose]
noncomputable def gSyl56 (ph : Wff) (ps : Wff) (ch : Wff) (th : Wff) (ta : Wff)
    (hyp_syl56_1 : Nominal.NPrf (.imp ph ps))
    (hyp_syl56_2 : Nominal.NPrf (.imp ch (.imp ps th)))
    (hyp_syl56_3 : Nominal.NPrf (.imp th ta)) : Nominal.NPrf (.imp ch (.imp ph ta)) :=
  by
  have p0000 := @gSyl6 ch ps th ta hyp_syl56_2 hyp_syl56_3
  have p0001 := @gSyl5 ph ps ch ta hyp_syl56_1 p0000
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_syl6com`. -/
@[expose]
noncomputable def gSyl6com (ph : Wff) (ps : Wff) (ch : Wff) (th : Wff)
    (hyp_syl6com_1 : Nominal.NPrf (.imp ph (.imp ps ch)))
    (hyp_syl6com_2 : Nominal.NPrf (.imp ch th)) : Nominal.NPrf (.imp ps (.imp ph th)) :=
  by
  have p0000 := @gSyl6 ph ps ch th hyp_syl6com_1 hyp_syl6com_2
  have p0001 := @gCom12 ph ps th p0000
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_mpcom`. -/
@[expose]
noncomputable def gMpcom (ph : Wff) (ps : Wff) (ch : Wff)
    (hyp_mpcom_1 : Nominal.NPrf (.imp ps ph))
    (hyp_mpcom_2 : Nominal.NPrf (.imp ph (.imp ps ch))) : Nominal.NPrf (.imp ps ch) :=
  by
  have p0000 := @gCom12 ph ps ch hyp_mpcom_2
  have p0001 := @gMpd ps ph ch hyp_mpcom_1 p0000
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_syli`. -/
@[expose]
noncomputable def gSyli (ph : Wff) (ps : Wff) (ch : Wff) (th : Wff)
    (hyp_syli_1 : Nominal.NPrf (.imp ps (.imp ph ch)))
    (hyp_syli_2 : Nominal.NPrf (.imp ch (.imp ph th))) :
    Nominal.NPrf (.imp ps (.imp ph th)) :=
  by
  have p0000 := @gCom12 ch ph th hyp_syli_2
  have p0001 := @gSylcom ps ph ch th hyp_syli_1 p0000
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_syl2im`. -/
@[expose]
noncomputable def gSyl2im (ph : Wff) (ps : Wff) (ch : Wff) (th : Wff) (ta : Wff)
    (hyp_syl2im_1 : Nominal.NPrf (.imp ph ps)) (hyp_syl2im_2 : Nominal.NPrf (.imp ch th))
    (hyp_syl2im_3 : Nominal.NPrf (.imp ps (.imp th ta))) :
    Nominal.NPrf (.imp ph (.imp ch ta)) :=
  by
  have p0000 := @gSyl5 ch th ps ta hyp_syl2im_2 hyp_syl2im_3
  have p0001 := @gSyl ph ps (.imp ch ta) hyp_syl2im_1 p0000
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_pm2_27`. -/
@[expose]
noncomputable def gPm227 (ph : Wff) (ps : Wff) :
    Nominal.NPrf (.imp ph (.imp (.imp ph ps) ps)) :=
  by
  have p0000 := @gId (.imp ph ps)
  have p0001 := @gCom12 (.imp ph ps) ph ps p0000
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_mpdd`. -/
@[expose]
noncomputable def gMpdd (ph : Wff) (ps : Wff) (ch : Wff) (th : Wff)
    (hyp_mpdd_1 : Nominal.NPrf (.imp ph (.imp ps ch)))
    (hyp_mpdd_2 : Nominal.NPrf (.imp ph (.imp ps (.imp ch th)))) :
    Nominal.NPrf (.imp ph (.imp ps th)) :=
  by
  have p0000 := @gA2d ph ps ch th hyp_mpdd_2
  have p0001 := @gMpd ph (.imp ps ch) (.imp ps th) hyp_mpdd_1 p0000
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_mpid`. -/
@[expose]
noncomputable def gMpid (ph : Wff) (ps : Wff) (ch : Wff) (th : Wff)
    (hyp_mpid_1 : Nominal.NPrf (.imp ph ch))
    (hyp_mpid_2 : Nominal.NPrf (.imp ph (.imp ps (.imp ch th)))) :
    Nominal.NPrf (.imp ph (.imp ps th)) :=
  by
  have p0000 := @gA1d ph ch ps hyp_mpid_1
  have p0001 := @gMpdd ph ps ch th p0000 hyp_mpid_2
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_mpdi`. -/
@[expose]
noncomputable def gMpdi (ph : Wff) (ps : Wff) (ch : Wff) (th : Wff)
    (hyp_mpdi_1 : Nominal.NPrf (.imp ps ch))
    (hyp_mpdi_2 : Nominal.NPrf (.imp ph (.imp ps (.imp ch th)))) :
    Nominal.NPrf (.imp ph (.imp ps th)) :=
  by
  have p0000 := @gA1i (.imp ps ch) ph hyp_mpdi_1
  have p0001 := @gMpdd ph ps ch th p0000 hyp_mpdi_2
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_mpii`. -/
@[expose]
noncomputable def gMpii (ph : Wff) (ps : Wff) (ch : Wff) (th : Wff)
    (hyp_mpii_1 : Nominal.NPrf ch)
    (hyp_mpii_2 : Nominal.NPrf (.imp ph (.imp ps (.imp ch th)))) :
    Nominal.NPrf (.imp ph (.imp ps th)) :=
  by
  have p0000 := @gA1i ch ps hyp_mpii_1
  have p0001 := @gMpdi ph ps ch th p0000 hyp_mpii_2
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_syld`. -/
@[expose]
noncomputable def gSyld (ph : Wff) (ps : Wff) (ch : Wff) (th : Wff)
    (hyp_syld_1 : Nominal.NPrf (.imp ph (.imp ps ch)))
    (hyp_syld_2 : Nominal.NPrf (.imp ph (.imp ch th))) :
    Nominal.NPrf (.imp ph (.imp ps th)) :=
  by
  have p0000 := @gA1d ph (.imp ch th) ps hyp_syld_2
  have p0001 := @gMpdd ph ps ch th hyp_syld_1 p0000
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_a1dd`. -/
@[expose]
noncomputable def gA1dd (ph : Wff) (ps : Wff) (ch : Wff) (th : Wff)
    (hyp_a1dd_1 : Nominal.NPrf (.imp ph (.imp ps ch))) :
    Nominal.NPrf (.imp ph (.imp ps (.imp th ch))) :=
  by
  have p0000 := Nominal.ax1 ch th
  have p0001 := @gSyl6 ph ps ch (.imp th ch) hyp_a1dd_1 p0000
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_pm2_43i`. -/
@[expose]
noncomputable def gPm243i (ph : Wff) (ps : Wff)
    (hyp_pm2_43i_1 : Nominal.NPrf (.imp ph (.imp ph ps))) : Nominal.NPrf (.imp ph ps) :=
  by
  have p0000 := @gId ph
  have p0001 := @gMpd ph ph ps p0000 hyp_pm2_43i_1
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_pm2_43d`. -/
@[expose]
noncomputable def gPm243d (ph : Wff) (ps : Wff) (ch : Wff)
    (hyp_pm2_43d_1 : Nominal.NPrf (.imp ph (.imp ps (.imp ps ch)))) :
    Nominal.NPrf (.imp ph (.imp ps ch)) :=
  by
  have p0000 := @gId ps
  have p0001 := @gMpdi ph ps ps ch p0000 hyp_pm2_43d_1
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_pm2_43a`. -/
@[expose]
noncomputable def gPm243a (ph : Wff) (ps : Wff) (ch : Wff)
    (hyp_pm2_43a_1 : Nominal.NPrf (.imp ps (.imp ph (.imp ps ch)))) :
    Nominal.NPrf (.imp ps (.imp ph ch)) :=
  by
  have p0000 := @gId ps
  have p0001 := @gMpid ps ph ps ch p0000 hyp_pm2_43a_1
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_pm2_43b`. -/
@[expose]
noncomputable def gPm243b (ph : Wff) (ps : Wff) (ch : Wff)
    (hyp_pm2_43b_1 : Nominal.NPrf (.imp ps (.imp ph (.imp ps ch)))) :
    Nominal.NPrf (.imp ph (.imp ps ch)) :=
  by
  have p0000 := @gPm243a ph ps ch hyp_pm2_43b_1
  have p0001 := @gCom12 ps ph ch p0000
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_imim2d`. -/
@[expose]
noncomputable def gImim2d (ph : Wff) (ps : Wff) (ch : Wff) (th : Wff)
    (hyp_imim2d_1 : Nominal.NPrf (.imp ph (.imp ps ch))) :
    Nominal.NPrf (.imp ph (.imp (.imp th ps) (.imp th ch))) :=
  by
  have p0000 := @gA1d ph (.imp ps ch) th hyp_imim2d_1
  have p0001 := @gA2d ph th ps ch p0000
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_imim2`. -/
@[expose]
noncomputable def gImim2 (ph : Wff) (ps : Wff) (ch : Wff) :
    Nominal.NPrf (.imp (.imp ph ps) (.imp (.imp ch ph) (.imp ch ps))) :=
  by
  have p0000 := @gId (.imp ph ps)
  have p0001 := @gImim2d (.imp ph ps) ph ps ch p0000
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_embantd`. -/
@[expose]
noncomputable def gEmbantd (ph : Wff) (ps : Wff) (ch : Wff) (th : Wff)
    (hyp_embantd_1 : Nominal.NPrf (.imp ph ps))
    (hyp_embantd_2 : Nominal.NPrf (.imp ph (.imp ch th))) :
    Nominal.NPrf (.imp ph (.imp (.imp ps ch) th)) :=
  by
  have p0000 := @gImim2d ph ch th ps hyp_embantd_2
  have p0001 := @gMpid ph (.imp ps ch) ps th hyp_embantd_1 p0000
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_sylsyld`. -/
@[expose]
noncomputable def gSylsyld (ph : Wff) (ps : Wff) (ch : Wff) (th : Wff) (ta : Wff)
    (hyp_sylsyld_1 : Nominal.NPrf (.imp ph ps))
    (hyp_sylsyld_2 : Nominal.NPrf (.imp ph (.imp ch th)))
    (hyp_sylsyld_3 : Nominal.NPrf (.imp ps (.imp th ta))) :
    Nominal.NPrf (.imp ph (.imp ch ta)) :=
  by
  have p0000 := @gSyl ph ps (.imp th ta) hyp_sylsyld_1 hyp_sylsyld_3
  have p0001 := @gSyld ph ch th ta hyp_sylsyld_2 p0000
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_imim12i`. -/
@[expose]
noncomputable def gImim12i (ph : Wff) (ps : Wff) (ch : Wff) (th : Wff)
    (hyp_imim12i_1 : Nominal.NPrf (.imp ph ps))
    (hyp_imim12i_2 : Nominal.NPrf (.imp ch th)) :
    Nominal.NPrf (.imp (.imp ps ch) (.imp ph th)) :=
  by
  have p0000 := @gImim2i ch th ps hyp_imim12i_2
  have p0001 := @gSyl5 ph ps (.imp ps ch) th hyp_imim12i_1 p0000
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_imim1i`. -/
@[expose]
noncomputable def gImim1i (ph : Wff) (ps : Wff) (ch : Wff)
    (hyp_imim1i_1 : Nominal.NPrf (.imp ph ps)) :
    Nominal.NPrf (.imp (.imp ps ch) (.imp ph ch)) :=
  by
  have p0000 := @gId ch
  have p0001 := @gImim12i ph ps ch ch hyp_imim1i_1 p0000
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_imim3i`. -/
@[expose]
noncomputable def gImim3i (ph : Wff) (ps : Wff) (ch : Wff) (th : Wff)
    (hyp_imim3i_1 : Nominal.NPrf (.imp ph (.imp ps ch))) :
    Nominal.NPrf (.imp (.imp th ph) (.imp (.imp th ps) (.imp th ch))) :=
  by
  have p0000 := @gImim2i ph (.imp ps ch) th hyp_imim3i_1
  have p0001 := @gA2d (.imp th ph) th ps ch p0000
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_sylc`. -/
@[expose]
noncomputable def gSylc (ph : Wff) (ps : Wff) (ch : Wff) (th : Wff)
    (hyp_sylc_1 : Nominal.NPrf (.imp ph ps)) (hyp_sylc_2 : Nominal.NPrf (.imp ph ch))
    (hyp_sylc_3 : Nominal.NPrf (.imp ps (.imp ch th))) : Nominal.NPrf (.imp ph th) :=
  by
  have p0000 := @gSyl2im ph ps ph ch th hyp_sylc_1 hyp_sylc_2 hyp_sylc_3
  have p0001 := @gPm243i ph th p0000
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_syl3c`. -/
@[expose]
noncomputable def gSyl3c (ph : Wff) (ps : Wff) (ch : Wff) (th : Wff) (ta : Wff)
    (hyp_syl3c_1 : Nominal.NPrf (.imp ph ps)) (hyp_syl3c_2 : Nominal.NPrf (.imp ph ch))
    (hyp_syl3c_3 : Nominal.NPrf (.imp ph th))
    (hyp_syl3c_4 : Nominal.NPrf (.imp ps (.imp ch (.imp th ta)))) :
    Nominal.NPrf (.imp ph ta) :=
  by
  have p0000 := @gSylc ph ps ch (.imp th ta) hyp_syl3c_1 hyp_syl3c_2 hyp_syl3c_4
  have p0001 := @gMpd ph th ta hyp_syl3c_3 p0000
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_mpsyl`. -/
@[expose]
noncomputable def gMpsyl (ph : Wff) (ps : Wff) (ch : Wff) (th : Wff)
    (hyp_mpsyl_1 : Nominal.NPrf ph) (hyp_mpsyl_2 : Nominal.NPrf (.imp ps ch))
    (hyp_mpsyl_3 : Nominal.NPrf (.imp ph (.imp ch th))) : Nominal.NPrf (.imp ps th) :=
  by
  have p0000 := @gA1i ph ps hyp_mpsyl_1
  have p0001 := @gSylc ps ph ch th p0000 hyp_mpsyl_2 hyp_mpsyl_3
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_syl6c`. -/
@[expose]
noncomputable def gSyl6c (ph : Wff) (ps : Wff) (ch : Wff) (th : Wff) (ta : Wff)
    (hyp_syl6c_1 : Nominal.NPrf (.imp ph (.imp ps ch)))
    (hyp_syl6c_2 : Nominal.NPrf (.imp ph (.imp ps th)))
    (hyp_syl6c_3 : Nominal.NPrf (.imp ch (.imp th ta))) :
    Nominal.NPrf (.imp ph (.imp ps ta)) :=
  by
  have p0000 := @gSyl6 ph ps ch (.imp th ta) hyp_syl6c_1 hyp_syl6c_3
  have p0001 := @gMpdd ph ps th ta hyp_syl6c_2 p0000
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_syldd`. -/
@[expose]
noncomputable def gSyldd (ph : Wff) (ps : Wff) (ch : Wff) (th : Wff) (ta : Wff)
    (hyp_syldd_1 : Nominal.NPrf (.imp ph (.imp ps (.imp ch th))))
    (hyp_syldd_2 : Nominal.NPrf (.imp ph (.imp ps (.imp th ta)))) :
    Nominal.NPrf (.imp ph (.imp ps (.imp ch ta))) :=
  by
  have p0000 := @gImim2 th ta ch
  have p0001 :=
    @gSyl6c ph ps (.imp th ta) (.imp ch th) (.imp ch ta) hyp_syldd_2 hyp_syldd_1 p0000
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_syl5d`. -/
@[expose]
noncomputable def gSyl5d (ph : Wff) (ps : Wff) (ch : Wff) (th : Wff) (ta : Wff)
    (hyp_syl5d_1 : Nominal.NPrf (.imp ph (.imp ps ch)))
    (hyp_syl5d_2 : Nominal.NPrf (.imp ph (.imp th (.imp ch ta)))) :
    Nominal.NPrf (.imp ph (.imp th (.imp ps ta))) :=
  by
  have p0000 := @gA1d ph (.imp ps ch) th hyp_syl5d_1
  have p0001 := @gSyldd ph th ps ch ta p0000 hyp_syl5d_2
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_syl7`. -/
@[expose]
noncomputable def gSyl7 (ph : Wff) (ps : Wff) (ch : Wff) (th : Wff) (ta : Wff)
    (hyp_syl7_1 : Nominal.NPrf (.imp ph ps))
    (hyp_syl7_2 : Nominal.NPrf (.imp ch (.imp th (.imp ps ta)))) :
    Nominal.NPrf (.imp ch (.imp th (.imp ph ta))) :=
  by
  have p0000 := @gA1i (.imp ph ps) ch hyp_syl7_1
  have p0001 := @gSyl5d ch ph ps th ta p0000 hyp_syl7_2
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_syl6d`. -/
@[expose]
noncomputable def gSyl6d (ph : Wff) (ps : Wff) (ch : Wff) (th : Wff) (ta : Wff)
    (hyp_syl6d_1 : Nominal.NPrf (.imp ph (.imp ps (.imp ch th))))
    (hyp_syl6d_2 : Nominal.NPrf (.imp ph (.imp th ta))) :
    Nominal.NPrf (.imp ph (.imp ps (.imp ch ta))) :=
  by
  have p0000 := @gA1d ph (.imp th ta) ps hyp_syl6d_2
  have p0001 := @gSyldd ph ps ch th ta hyp_syl6d_1 p0000
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_syl8`. -/
@[expose]
noncomputable def gSyl8 (ph : Wff) (ps : Wff) (ch : Wff) (th : Wff) (ta : Wff)
    (hyp_syl8_1 : Nominal.NPrf (.imp ph (.imp ps (.imp ch th))))
    (hyp_syl8_2 : Nominal.NPrf (.imp th ta)) :
    Nominal.NPrf (.imp ph (.imp ps (.imp ch ta))) :=
  by
  have p0000 := @gA1i (.imp th ta) ph hyp_syl8_2
  have p0001 := @gSyl6d ph ps ch th ta hyp_syl8_1 p0000
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_syl9`. -/
@[expose]
noncomputable def gSyl9 (ph : Wff) (ps : Wff) (ch : Wff) (th : Wff) (ta : Wff)
    (hyp_syl9_1 : Nominal.NPrf (.imp ph (.imp ps ch)))
    (hyp_syl9_2 : Nominal.NPrf (.imp th (.imp ch ta))) :
    Nominal.NPrf (.imp ph (.imp th (.imp ps ta))) :=
  by
  have p0000 := @gA1i (.imp th (.imp ch ta)) ph hyp_syl9_2
  have p0001 := @gSyl5d ph ps ch th ta hyp_syl9_1 p0000
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_syl9r`. -/
@[expose]
noncomputable def gSyl9r (ph : Wff) (ps : Wff) (ch : Wff) (th : Wff) (ta : Wff)
    (hyp_syl9r_1 : Nominal.NPrf (.imp ph (.imp ps ch)))
    (hyp_syl9r_2 : Nominal.NPrf (.imp th (.imp ch ta))) :
    Nominal.NPrf (.imp th (.imp ph (.imp ps ta))) :=
  by
  have p0000 := @gSyl9 ph ps ch th ta hyp_syl9r_1 hyp_syl9r_2
  have p0001 := @gCom12 ph th (.imp ps ta) p0000
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_imim12d`. -/
@[expose]
noncomputable def gImim12d (ph : Wff) (ps : Wff) (ch : Wff) (th : Wff) (ta : Wff)
    (hyp_imim12d_1 : Nominal.NPrf (.imp ph (.imp ps ch)))
    (hyp_imim12d_2 : Nominal.NPrf (.imp ph (.imp th ta))) :
    Nominal.NPrf (.imp ph (.imp (.imp ch th) (.imp ps ta))) :=
  by
  have p0000 := @gImim2d ph th ta ch hyp_imim12d_2
  have p0001 := @gSyl5d ph ps ch (.imp ch th) ta hyp_imim12d_1 p0000
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_imim1d`. -/
@[expose]
noncomputable def gImim1d (ph : Wff) (ps : Wff) (ch : Wff) (th : Wff)
    (hyp_imim1d_1 : Nominal.NPrf (.imp ph (.imp ps ch))) :
    Nominal.NPrf (.imp ph (.imp (.imp ch th) (.imp ps th))) :=
  by
  have p0000 := @gIdd ph th
  have p0001 := @gImim12d ph ps ch th th hyp_imim1d_1 p0000
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_imim1`. -/
@[expose]
noncomputable def gImim1 (ph : Wff) (ps : Wff) (ch : Wff) :
    Nominal.NPrf (.imp (.imp ph ps) (.imp (.imp ps ch) (.imp ph ch))) :=
  by
  have p0000 := @gId (.imp ph ps)
  have p0001 := @gImim1d (.imp ph ps) ph ps ch p0000
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_com23`. -/
@[expose]
noncomputable def gCom23 (ph : Wff) (ps : Wff) (ch : Wff) (th : Wff)
    (hyp_com3_1 : Nominal.NPrf (.imp ph (.imp ps (.imp ch th)))) :
    Nominal.NPrf (.imp ph (.imp ch (.imp ps th))) :=
  by
  have p0000 := @gPm227 ch th
  have p0001 := @gSyl9 ph ps (.imp ch th) ch th hyp_com3_1 p0000
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_com3r`. -/
@[expose]
noncomputable def gCom3r (ph : Wff) (ps : Wff) (ch : Wff) (th : Wff)
    (hyp_com3_1 : Nominal.NPrf (.imp ph (.imp ps (.imp ch th)))) :
    Nominal.NPrf (.imp ch (.imp ph (.imp ps th))) :=
  by
  have p0000 := @gCom23 ph ps ch th hyp_com3_1
  have p0001 := @gCom12 ph ch (.imp ps th) p0000
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_com3l`. -/
@[expose]
noncomputable def gCom3l (ph : Wff) (ps : Wff) (ch : Wff) (th : Wff)
    (hyp_com3_1 : Nominal.NPrf (.imp ph (.imp ps (.imp ch th)))) :
    Nominal.NPrf (.imp ps (.imp ch (.imp ph th))) :=
  by
  have p0000 := @gCom3r ph ps ch th hyp_com3_1
  have p0001 := @gCom3r ch ph ps th p0000
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_pm2_04`. -/
@[expose]
noncomputable def gPm204 (ph : Wff) (ps : Wff) (ch : Wff) :
    Nominal.NPrf (.imp (.imp ph (.imp ps ch)) (.imp ps (.imp ph ch))) :=
  by
  have p0000 := @gId (.imp ph (.imp ps ch))
  have p0001 := @gCom23 (.imp ph (.imp ps ch)) ph ps ch p0000
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_com34`. -/
@[expose]
noncomputable def gCom34 (ph : Wff) (ps : Wff) (ch : Wff) (th : Wff) (ta : Wff)
    (hyp_com4_1 : Nominal.NPrf (.imp ph (.imp ps (.imp ch (.imp th ta))))) :
    Nominal.NPrf (.imp ph (.imp ps (.imp th (.imp ch ta)))) :=
  by
  have p0000 := @gPm204 ch th ta
  have p0001 :=
    @gSyl6 ph ps (.imp ch (.imp th ta)) (.imp th (.imp ch ta)) hyp_com4_1 p0000
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_com4l`. -/
@[expose]
noncomputable def gCom4l (ph : Wff) (ps : Wff) (ch : Wff) (th : Wff) (ta : Wff)
    (hyp_com4_1 : Nominal.NPrf (.imp ph (.imp ps (.imp ch (.imp th ta))))) :
    Nominal.NPrf (.imp ps (.imp ch (.imp th (.imp ph ta)))) :=
  by
  have p0000 := @gCom3l ph ps ch (.imp th ta) hyp_com4_1
  have p0001 := @gCom34 ps ch ph th ta p0000
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_com4t`. -/
@[expose]
noncomputable def gCom4t (ph : Wff) (ps : Wff) (ch : Wff) (th : Wff) (ta : Wff)
    (hyp_com4_1 : Nominal.NPrf (.imp ph (.imp ps (.imp ch (.imp th ta))))) :
    Nominal.NPrf (.imp ch (.imp th (.imp ph (.imp ps ta)))) :=
  by
  have p0000 := @gCom4l ph ps ch th ta hyp_com4_1
  have p0001 := @gCom4l ps ch th ph ta p0000
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_com4r`. -/
@[expose]
noncomputable def gCom4r (ph : Wff) (ps : Wff) (ch : Wff) (th : Wff) (ta : Wff)
    (hyp_com4_1 : Nominal.NPrf (.imp ph (.imp ps (.imp ch (.imp th ta))))) :
    Nominal.NPrf (.imp th (.imp ph (.imp ps (.imp ch ta)))) :=
  by
  have p0000 := @gCom4t ph ps ch th ta hyp_com4_1
  have p0001 := @gCom4l ch th ph ps ta p0000
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_pm2_86d`. -/
@[expose]
noncomputable def gPm286d (ph : Wff) (ps : Wff) (ch : Wff) (th : Wff)
    (hyp_pm2_86d_1 : Nominal.NPrf (.imp ph (.imp (.imp ps ch) (.imp ps th)))) :
    Nominal.NPrf (.imp ph (.imp ps (.imp ch th))) :=
  by
  have p0000 := Nominal.ax1 ch ps
  have p0001 := @gSyl5 ch (.imp ps ch) ph (.imp ps th) p0000 hyp_pm2_86d_1
  have p0002 := @gCom23 ph ch ps th p0001
  exact p0002

/-- Checked nominal proof certificate identified upstream as `g_con4d`. -/
@[expose]
noncomputable def gCon4d (ph : Wff) (ps : Wff) (ch : Wff)
    (hyp_con4d_1 : Nominal.NPrf (.imp ph (.imp (.neg ps) (.neg ch)))) :
    Nominal.NPrf (.imp ph (.imp ch ps)) :=
  by
  have p0000 := Nominal.ax3 ps ch
  have p0001 := @gSyl ph (.imp (.neg ps) (.neg ch)) (.imp ch ps) hyp_con4d_1 p0000
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_pm2_21d`. -/
@[expose]
noncomputable def gPm221d (ph : Wff) (ps : Wff) (ch : Wff)
    (hyp_pm2_21d_1 : Nominal.NPrf (.imp ph (.neg ps))) :
    Nominal.NPrf (.imp ph (.imp ps ch)) :=
  by
  have p0000 := @gA1d ph (.neg ps) (.neg ch) hyp_pm2_21d_1
  have p0001 := @gCon4d ph ch ps p0000
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_pm2_21dd`. -/
@[expose]
noncomputable def gPm221dd (ph : Wff) (ps : Wff) (ch : Wff)
    (hyp_pm2_21dd_1 : Nominal.NPrf (.imp ph ps))
    (hyp_pm2_21dd_2 : Nominal.NPrf (.imp ph (.neg ps))) : Nominal.NPrf (.imp ph ch) :=
  by
  have p0000 := @gPm221d ph ps ch hyp_pm2_21dd_2
  have p0001 := @gMpd ph ps ch hyp_pm2_21dd_1 p0000
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_pm2_21`. -/
@[expose]
noncomputable def gPm221 (ph : Wff) (ps : Wff) :
    Nominal.NPrf (.imp (.neg ph) (.imp ph ps)) :=
  by
  have p0000 := @gId (.neg ph)
  have p0001 := @gPm221d (.neg ph) ph ps p0000
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_pm2_24`. -/
@[expose]
noncomputable def gPm224 (ph : Wff) (ps : Wff) :
    Nominal.NPrf (.imp ph (.imp (.neg ph) ps)) :=
  by
  have p0000 := @gPm221 ph ps
  have p0001 := @gCom12 (.neg ph) ph ps p0000
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_pm2_18`. -/
@[expose]
noncomputable def gPm218 (ph : Wff) : Nominal.NPrf (.imp (.imp (.neg ph) ph) ph) :=
  by
  have p0000 := @gPm221 ph (.neg (.imp (.neg ph) ph))
  have p0001 := @gA2i (.neg ph) ph (.neg (.imp (.neg ph) ph)) p0000
  have p0002 := @gCon4d (.imp (.neg ph) ph) ph (.imp (.neg ph) ph) p0001
  have p0003 := @gPm243i (.imp (.neg ph) ph) ph p0002
  exact p0003

/-- Checked nominal proof certificate identified upstream as `g_pm2_18d`. -/
@[expose]
noncomputable def gPm218d (ph : Wff) (ps : Wff)
    (hyp_pm2_18d_1 : Nominal.NPrf (.imp ph (.imp (.neg ps) ps))) :
    Nominal.NPrf (.imp ph ps) :=
  by
  have p0000 := @gPm218 ps
  have p0001 := @gSyl ph (.imp (.neg ps) ps) ps hyp_pm2_18d_1 p0000
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_notnot2`. -/
@[expose]
noncomputable def gNotnot2 (ph : Wff) : Nominal.NPrf (.imp (.neg (.neg ph)) ph) :=
  by
  have p0000 := @gPm221 (.neg ph) ph
  have p0001 := @gPm218d (.neg (.neg ph)) ph p0000
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_notnotrd`. -/
@[expose]
noncomputable def gNotnotrd (ph : Wff) (ps : Wff)
    (hyp_notnotrd_1 : Nominal.NPrf (.imp ph (.neg (.neg ps)))) :
    Nominal.NPrf (.imp ph ps) :=
  by
  have p0000 := @gNotnot2 ps
  have p0001 := @gSyl ph (.neg (.neg ps)) ps hyp_notnotrd_1 p0000
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_notnotri`. -/
@[expose]
noncomputable def gNotnotri (ph : Wff) (hyp_notnotri_1 : Nominal.NPrf (.neg (.neg ph))) :
    Nominal.NPrf ph := by
  have p0000 := @gNotnot2 ph
  have p0001 := Nominal.mp hyp_notnotri_1 p0000
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_con2d`. -/
@[expose]
noncomputable def gCon2d (ph : Wff) (ps : Wff) (ch : Wff)
    (hyp_con2d_1 : Nominal.NPrf (.imp ph (.imp ps (.neg ch)))) :
    Nominal.NPrf (.imp ph (.imp ch (.neg ps))) :=
  by
  have p0000 := @gNotnot2 ps
  have p0001 := @gSyl5 (.neg (.neg ps)) ps ph (.neg ch) p0000 hyp_con2d_1
  have p0002 := @gCon4d ph (.neg ps) ch p0001
  exact p0002

/-- Checked nominal proof certificate identified upstream as `g_con2`. -/
@[expose]
noncomputable def gCon2 (ph : Wff) (ps : Wff) :
    Nominal.NPrf (.imp (.imp ph (.neg ps)) (.imp ps (.neg ph))) :=
  by
  have p0000 := @gId (.imp ph (.neg ps))
  have p0001 := @gCon2d (.imp ph (.neg ps)) ph ps p0000
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_mt2d`. -/
@[expose]
noncomputable def gMt2d (ph : Wff) (ps : Wff) (ch : Wff)
    (hyp_mt2d_1 : Nominal.NPrf (.imp ph ch))
    (hyp_mt2d_2 : Nominal.NPrf (.imp ph (.imp ps (.neg ch)))) :
    Nominal.NPrf (.imp ph (.neg ps)) :=
  by
  have p0000 := @gCon2d ph ps ch hyp_mt2d_2
  have p0001 := @gMpd ph ch (.neg ps) hyp_mt2d_1 p0000
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_nsyl3`. -/
@[expose]
noncomputable def gNsyl3 (ph : Wff) (ps : Wff) (ch : Wff)
    (hyp_nsyl3_1 : Nominal.NPrf (.imp ph (.neg ps)))
    (hyp_nsyl3_2 : Nominal.NPrf (.imp ch ps)) : Nominal.NPrf (.imp ch (.neg ph)) :=
  by
  have p0000 := @gA1i (.imp ph (.neg ps)) ch hyp_nsyl3_1
  have p0001 := @gMt2d ch ph ps hyp_nsyl3_2 p0000
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_con2i`. -/
@[expose]
noncomputable def gCon2i (ph : Wff) (ps : Wff)
    (hyp_con2i_a : Nominal.NPrf (.imp ph (.neg ps))) : Nominal.NPrf (.imp ps (.neg ph)) :=
  by
  have p0000 := @gId ps
  have p0001 := @gNsyl3 ph ps ps hyp_con2i_a p0000
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_nsyl`. -/
@[expose]
noncomputable def gNsyl (ph : Wff) (ps : Wff) (ch : Wff)
    (hyp_nsyl_1 : Nominal.NPrf (.imp ph (.neg ps)))
    (hyp_nsyl_2 : Nominal.NPrf (.imp ch ps)) : Nominal.NPrf (.imp ph (.neg ch)) :=
  by
  have p0000 := @gNsyl3 ph ps ch hyp_nsyl_1 hyp_nsyl_2
  have p0001 := @gCon2i ch ph p0000
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_notnot1`. -/
@[expose]
noncomputable def gNotnot1 (ph : Wff) : Nominal.NPrf (.imp ph (.neg (.neg ph))) :=
  by
  have p0000 := @gId (.neg ph)
  have p0001 := @gCon2i (.neg ph) ph p0000
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_notnoti`. -/
@[expose]
noncomputable def gNotnoti (ph : Wff) (hyp_negbi_1 : Nominal.NPrf ph) :
    Nominal.NPrf (.neg (.neg ph)) :=
  by
  have p0000 := @gNotnot1 ph
  have p0001 := Nominal.mp hyp_negbi_1 p0000
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_con1d`. -/
@[expose]
noncomputable def gCon1d (ph : Wff) (ps : Wff) (ch : Wff)
    (hyp_con1d_1 : Nominal.NPrf (.imp ph (.imp (.neg ps) ch))) :
    Nominal.NPrf (.imp ph (.imp (.neg ch) ps)) :=
  by
  have p0000 := @gNotnot1 ch
  have p0001 := @gSyl6 ph (.neg ps) ch (.neg (.neg ch)) hyp_con1d_1 p0000
  have p0002 := @gCon4d ph ps (.neg ch) p0001
  exact p0002

/-- Checked nominal proof certificate identified upstream as `g_mt3d`. -/
@[expose]
noncomputable def gMt3d (ph : Wff) (ps : Wff) (ch : Wff)
    (hyp_mt3d_1 : Nominal.NPrf (.imp ph (.neg ch)))
    (hyp_mt3d_2 : Nominal.NPrf (.imp ph (.imp (.neg ps) ch))) :
    Nominal.NPrf (.imp ph ps) :=
  by
  have p0000 := @gCon1d ph ps ch hyp_mt3d_2
  have p0001 := @gMpd ph (.neg ch) ps hyp_mt3d_1 p0000
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_nsyl2`. -/
@[expose]
noncomputable def gNsyl2 (ph : Wff) (ps : Wff) (ch : Wff)
    (hyp_nsyl2_1 : Nominal.NPrf (.imp ph (.neg ps)))
    (hyp_nsyl2_2 : Nominal.NPrf (.imp (.neg ch) ps)) : Nominal.NPrf (.imp ph ch) :=
  by
  have p0000 := @gA1i (.imp (.neg ch) ps) ph hyp_nsyl2_2
  have p0001 := @gMt3d ph ch ps hyp_nsyl2_1 p0000
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_con1`. -/
@[expose]
noncomputable def gCon1 (ph : Wff) (ps : Wff) :
    Nominal.NPrf (.imp (.imp (.neg ph) ps) (.imp (.neg ps) ph)) :=
  by
  have p0000 := @gId (.imp (.neg ph) ps)
  have p0001 := @gCon1d (.imp (.neg ph) ps) ph ps p0000
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_con1i`. -/
@[expose]
noncomputable def gCon1i (ph : Wff) (ps : Wff)
    (hyp_con1i_a : Nominal.NPrf (.imp (.neg ph) ps)) : Nominal.NPrf (.imp (.neg ps) ph) :=
  by
  have p0000 := @gId (.neg ps)
  have p0001 := @gNsyl2 (.neg ps) ps ph p0000 hyp_con1i_a
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_con4i`. -/
@[expose]
noncomputable def gCon4i (ph : Wff) (ps : Wff)
    (hyp_con4i_1 : Nominal.NPrf (.imp (.neg ph) (.neg ps))) : Nominal.NPrf (.imp ps ph) :=
  by
  have p0000 := @gNotnot1 ps
  have p0001 := @gNsyl2 ps (.neg ps) ph p0000 hyp_con4i_1
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_pm2_21i`. -/
@[expose]
noncomputable def gPm221i (ph : Wff) (ps : Wff)
    (hyp_pm2_21i_1 : Nominal.NPrf (.neg ph)) : Nominal.NPrf (.imp ph ps) :=
  by
  have p0000 := @gA1i (.neg ph) (.neg ps) hyp_pm2_21i_1
  have p0001 := @gCon4i ps ph p0000
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_con3d`. -/
@[expose]
noncomputable def gCon3d (ph : Wff) (ps : Wff) (ch : Wff)
    (hyp_con3d_1 : Nominal.NPrf (.imp ph (.imp ps ch))) :
    Nominal.NPrf (.imp ph (.imp (.neg ch) (.neg ps))) :=
  by
  have p0000 := @gNotnot2 ps
  have p0001 := @gSyl5 (.neg (.neg ps)) ps ph ch p0000 hyp_con3d_1
  have p0002 := @gCon1d ph (.neg ps) ch p0001
  exact p0002

/-- Checked nominal proof certificate identified upstream as `g_con3`. -/
@[expose]
noncomputable def gCon3 (ph : Wff) (ps : Wff) :
    Nominal.NPrf (.imp (.imp ph ps) (.imp (.neg ps) (.neg ph))) :=
  by
  have p0000 := @gId (.imp ph ps)
  have p0001 := @gCon3d (.imp ph ps) ph ps p0000
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_con3i`. -/
@[expose]
noncomputable def gCon3i (ph : Wff) (ps : Wff)
    (hyp_con3i_a : Nominal.NPrf (.imp ph ps)) : Nominal.NPrf (.imp (.neg ps) (.neg ph)) :=
  by
  have p0000 := @gId (.neg ps)
  have p0001 := @gNsyl (.neg ps) ps ph p0000 hyp_con3i_a
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_con3rr3`. -/
@[expose]
noncomputable def gCon3rr3 (ph : Wff) (ps : Wff) (ch : Wff)
    (hyp_con3rr3_1 : Nominal.NPrf (.imp ph (.imp ps ch))) :
    Nominal.NPrf (.imp (.neg ch) (.imp ph (.neg ps))) :=
  by
  have p0000 := @gCon3d ph ps ch hyp_con3rr3_1
  have p0001 := @gCom12 ph (.neg ch) (.neg ps) p0000
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_nsyld`. -/
@[expose]
noncomputable def gNsyld (ph : Wff) (ps : Wff) (ch : Wff) (ta : Wff)
    (hyp_nsyld_1 : Nominal.NPrf (.imp ph (.imp ps (.neg ch))))
    (hyp_nsyld_2 : Nominal.NPrf (.imp ph (.imp ta ch))) :
    Nominal.NPrf (.imp ph (.imp ps (.neg ta))) :=
  by
  have p0000 := @gCon3d ph ta ch hyp_nsyld_2
  have p0001 := @gSyld ph ps (.neg ch) (.neg ta) hyp_nsyld_1 p0000
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_nsyl4`. -/
@[expose]
noncomputable def gNsyl4 (ph : Wff) (ps : Wff) (ch : Wff)
    (hyp_nsyl4_1 : Nominal.NPrf (.imp ph ps))
    (hyp_nsyl4_2 : Nominal.NPrf (.imp (.neg ph) ch)) : Nominal.NPrf (.imp (.neg ch) ps) :=
  by
  have p0000 := @gCon1i ph ch hyp_nsyl4_2
  have p0001 := @gSyl (.neg ch) ph ps p0000 hyp_nsyl4_1
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_pm2_24i`. -/
@[expose]
noncomputable def gPm224i (ph : Wff) (ps : Wff) (hyp_pm2_24i_1 : Nominal.NPrf ph) :
    Nominal.NPrf (.imp (.neg ph) ps) :=
  by
  have p0000 := @gA1i ph (.neg ps) hyp_pm2_24i_1
  have p0001 := @gCon1i ps ph p0000
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_pm3_2im`. -/
@[expose]
noncomputable def gPm32im (ph : Wff) (ps : Wff) :
    Nominal.NPrf (.imp ph (.imp ps (.neg (.imp ph (.neg ps))))) :=
  by
  have p0000 := @gPm227 ph (.neg ps)
  have p0001 := @gCon2d ph (.imp ph (.neg ps)) ps p0000
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_impi`. -/
@[expose]
noncomputable def gImpi (ph : Wff) (ps : Wff) (ch : Wff)
    (hyp_impi_1 : Nominal.NPrf (.imp ph (.imp ps ch))) :
    Nominal.NPrf (.imp (.neg (.imp ph (.neg ps))) ch) :=
  by
  have p0000 := @gCon3rr3 ph ps ch hyp_impi_1
  have p0001 := @gCon1i ch (.imp ph (.neg ps)) p0000
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_expi`. -/
@[expose]
noncomputable def gExpi (ph : Wff) (ps : Wff) (ch : Wff)
    (hyp_expi_1 : Nominal.NPrf (.imp (.neg (.imp ph (.neg ps))) ch)) :
    Nominal.NPrf (.imp ph (.imp ps ch)) :=
  by
  have p0000 := @gPm32im ph ps
  have p0001 := @gSyl6 ph ps (.neg (.imp ph (.neg ps))) ch p0000 hyp_expi_1
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_simprim`. -/
@[expose]
noncomputable def gSimprim (ph : Wff) (ps : Wff) :
    Nominal.NPrf (.imp (.neg (.imp ph (.neg ps))) ps) :=
  by
  have p0000 := @gIdd ph ps
  have p0001 := @gImpi ph ps ps p0000
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_simplim`. -/
@[expose]
noncomputable def gSimplim (ph : Wff) (ps : Wff) :
    Nominal.NPrf (.imp (.neg (.imp ph ps)) ph) :=
  by
  have p0000 := @gPm221 ph ps
  have p0001 := @gCon1i ph (.imp ph ps) p0000
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_pm2_61d`. -/
@[expose]
noncomputable def gPm261d (ph : Wff) (ps : Wff) (ch : Wff)
    (hyp_pm2_61d_1 : Nominal.NPrf (.imp ph (.imp ps ch)))
    (hyp_pm2_61d_2 : Nominal.NPrf (.imp ph (.imp (.neg ps) ch))) :
    Nominal.NPrf (.imp ph ch) :=
  by
  have p0000 := @gCon1d ph ps ch hyp_pm2_61d_2
  have p0001 := @gSyld ph (.neg ch) ps ch p0000 hyp_pm2_61d_1
  have p0002 := @gPm218d ph ch p0001
  exact p0002

/-- Checked nominal proof certificate identified upstream as `g_pm2_61d1`. -/
@[expose]
noncomputable def gPm261d1 (ph : Wff) (ps : Wff) (ch : Wff)
    (hyp_pm2_61d1_1 : Nominal.NPrf (.imp ph (.imp ps ch)))
    (hyp_pm2_61d1_2 : Nominal.NPrf (.imp (.neg ps) ch)) : Nominal.NPrf (.imp ph ch) :=
  by
  have p0000 := @gA1i (.imp (.neg ps) ch) ph hyp_pm2_61d1_2
  have p0001 := @gPm261d ph ps ch hyp_pm2_61d1_1 p0000
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_pm2_61d2`. -/
@[expose]
noncomputable def gPm261d2 (ph : Wff) (ps : Wff) (ch : Wff)
    (hyp_pm2_61d2_1 : Nominal.NPrf (.imp ph (.imp (.neg ps) ch)))
    (hyp_pm2_61d2_2 : Nominal.NPrf (.imp ps ch)) : Nominal.NPrf (.imp ph ch) :=
  by
  have p0000 := @gA1i (.imp ps ch) ph hyp_pm2_61d2_2
  have p0001 := @gPm261d ph ps ch p0000 hyp_pm2_61d2_1
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_ja`. -/
@[expose]
noncomputable def gJa (ph : Wff) (ps : Wff) (ch : Wff)
    (hyp_ja_1 : Nominal.NPrf (.imp (.neg ph) ch)) (hyp_ja_2 : Nominal.NPrf (.imp ps ch)) :
    Nominal.NPrf (.imp (.imp ph ps) ch) :=
  by
  have p0000 := @gImim2i ps ch ph hyp_ja_2
  have p0001 := @gPm261d1 (.imp ph ps) ph ch p0000 hyp_ja_1
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_pm2_61i`. -/
@[expose]
noncomputable def gPm261i (ph : Wff) (ps : Wff)
    (hyp_pm2_61i_1 : Nominal.NPrf (.imp ph ps))
    (hyp_pm2_61i_2 : Nominal.NPrf (.imp (.neg ph) ps)) : Nominal.NPrf ps :=
  by
  have p0000 := @gId ph
  have p0001 := @gJa ph ph ps hyp_pm2_61i_2 hyp_pm2_61i_1
  have p0002 := Nominal.mp p0000 p0001
  exact p0002

/-- Checked nominal proof certificate identified upstream as `g_pm2_61ii`. -/
@[expose]
noncomputable def gPm261ii (ph : Wff) (ps : Wff) (ch : Wff)
    (hyp_pm2_61ii_1 : Nominal.NPrf (.imp (.neg ph) (.imp (.neg ps) ch)))
    (hyp_pm2_61ii_2 : Nominal.NPrf (.imp ph ch))
    (hyp_pm2_61ii_3 : Nominal.NPrf (.imp ps ch)) : Nominal.NPrf ch :=
  by
  have p0000 := @gPm261d2 (.neg ph) ps ch hyp_pm2_61ii_1 hyp_pm2_61ii_3
  have p0001 := @gPm261i ph ch hyp_pm2_61ii_2 p0000
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_pm2_01d`. -/
@[expose]
noncomputable def gPm201d (ph : Wff) (ps : Wff)
    (hyp_pm2_01d_1 : Nominal.NPrf (.imp ph (.imp ps (.neg ps)))) :
    Nominal.NPrf (.imp ph (.neg ps)) :=
  by
  have p0000 := @gId (.neg ps)
  have p0001 := @gPm261d1 ph ps (.neg ps) hyp_pm2_01d_1 p0000
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_pm2_65i`. -/
@[expose]
noncomputable def gPm265i (ph : Wff) (ps : Wff)
    (hyp_pm2_65i_1 : Nominal.NPrf (.imp ph ps))
    (hyp_pm2_65i_2 : Nominal.NPrf (.imp ph (.neg ps))) : Nominal.NPrf (.neg ph) :=
  by
  have p0000 := @gCon2i ph ps hyp_pm2_65i_2
  have p0001 := @gCon3i ph ps hyp_pm2_65i_1
  have p0002 := @gPm261i ps (.neg ph) p0000 p0001
  exact p0002

/-- Checked nominal proof certificate identified upstream as `g_pm2_65d`. -/
@[expose]
noncomputable def gPm265d (ph : Wff) (ps : Wff) (ch : Wff)
    (hyp_pm2_65d_1 : Nominal.NPrf (.imp ph (.imp ps ch)))
    (hyp_pm2_65d_2 : Nominal.NPrf (.imp ph (.imp ps (.neg ch)))) :
    Nominal.NPrf (.imp ph (.neg ps)) :=
  by
  have p0000 := @gNsyld ph ps ch ps hyp_pm2_65d_2 hyp_pm2_65d_1
  have p0001 := @gPm201d ph ps p0000
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_mto`. -/
@[expose]
noncomputable def gMto (ph : Wff) (ps : Wff) (hyp_mto_1 : Nominal.NPrf (.neg ps))
    (hyp_mto_2 : Nominal.NPrf (.imp ph ps)) : Nominal.NPrf (.neg ph) :=
  by
  have p0000 := @gA1i (.neg ps) ph hyp_mto_1
  have p0001 := @gPm265i ph ps hyp_mto_2 p0000
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_mtod`. -/
@[expose]
noncomputable def gMtod (ph : Wff) (ps : Wff) (ch : Wff)
    (hyp_mtod_1 : Nominal.NPrf (.imp ph (.neg ch)))
    (hyp_mtod_2 : Nominal.NPrf (.imp ph (.imp ps ch))) :
    Nominal.NPrf (.imp ph (.neg ps)) :=
  by
  have p0000 := @gA1d ph (.neg ch) ps hyp_mtod_1
  have p0001 := @gPm265d ph ps ch hyp_mtod_2 p0000
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_mtoi`. -/
@[expose]
noncomputable def gMtoi (ph : Wff) (ps : Wff) (ch : Wff)
    (hyp_mtoi_1 : Nominal.NPrf (.neg ch))
    (hyp_mtoi_2 : Nominal.NPrf (.imp ph (.imp ps ch))) :
    Nominal.NPrf (.imp ph (.neg ps)) :=
  by
  have p0000 := @gA1i (.neg ch) ph hyp_mtoi_1
  have p0001 := @gMtod ph ps ch p0000 hyp_mtoi_2
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_mt2`. -/
@[expose]
noncomputable def gMt2 (ph : Wff) (ps : Wff) (hyp_mt2_1 : Nominal.NPrf ps)
    (hyp_mt2_2 : Nominal.NPrf (.imp ph (.neg ps))) : Nominal.NPrf (.neg ph) :=
  by
  have p0000 := @gA1i ps ph hyp_mt2_1
  have p0001 := @gPm265i ph ps p0000 hyp_mt2_2
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_mt3`. -/
@[expose]
noncomputable def gMt3 (ph : Wff) (ps : Wff) (hyp_mt3_1 : Nominal.NPrf (.neg ps))
    (hyp_mt3_2 : Nominal.NPrf (.imp (.neg ph) ps)) : Nominal.NPrf ph :=
  by
  have p0000 := @gMto (.neg ph) ps hyp_mt3_1 hyp_mt3_2
  have p0001 := @gNotnotri ph p0000
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_bi1`. -/
@[expose]
noncomputable def gBi1 (ph : Wff) (ps : Wff) :
    Nominal.NPrf (.imp (synWb ph ps) (.imp ph ps)) :=
  by
  have p0000 := Nominal.biimpRefl (synWb ph ps)
  have p0001 :=
    @gSimplim (.imp (synWb ph ps) (.neg (.imp (.imp ph ps) (.neg (.imp ps ph)))))
      (.neg (.imp (.neg (.imp (.imp ph ps) (.neg (.imp ps ph)))) (synWb ph ps)))
  have p0002 := Nominal.mp p0000 p0001
  have p0003 := @gSimplim (.imp ph ps) (.neg (.imp ps ph))
  have p0004 :=
    @gSyl (synWb ph ps) (.neg (.imp (.imp ph ps) (.neg (.imp ps ph)))) (.imp ph ps)
      p0002 p0003
  exact p0004

/-- Checked nominal proof certificate identified upstream as `g_bi3`. -/
@[expose]
noncomputable def gBi3 (ph : Wff) (ps : Wff) :
    Nominal.NPrf (.imp (.imp ph ps) (.imp (.imp ps ph) (synWb ph ps))) :=
  by
  have p0000 := Nominal.biimpRefl (synWb ph ps)
  have p0001 :=
    @gSimprim (.imp (synWb ph ps) (.neg (.imp (.imp ph ps) (.neg (.imp ps ph)))))
      (.imp (.neg (.imp (.imp ph ps) (.neg (.imp ps ph)))) (synWb ph ps))
  have p0002 := Nominal.mp p0000 p0001
  have p0003 := @gExpi (.imp ph ps) (.imp ps ph) (synWb ph ps) p0002
  exact p0003

/-- Checked nominal proof certificate identified upstream as `g_impbii`. -/
@[expose]
noncomputable def gImpbii (ph : Wff) (ps : Wff)
    (hyp_impbii_1 : Nominal.NPrf (.imp ph ps))
    (hyp_impbii_2 : Nominal.NPrf (.imp ps ph)) : Nominal.NPrf (synWb ph ps) :=
  by
  have p0000 := @gBi3 ph ps
  have p0001 :=
    @gMp2 (.imp ph ps) (.imp ps ph) (synWb ph ps) hyp_impbii_1 hyp_impbii_2 p0000
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_impbidd`. -/
@[expose]
noncomputable def gImpbidd (ph : Wff) (ps : Wff) (ch : Wff) (th : Wff)
    (hyp_impbidd_1 : Nominal.NPrf (.imp ph (.imp ps (.imp ch th))))
    (hyp_impbidd_2 : Nominal.NPrf (.imp ph (.imp ps (.imp th ch)))) :
    Nominal.NPrf (.imp ph (.imp ps (synWb ch th))) :=
  by
  have p0000 := @gBi3 ch th
  have p0001 :=
    @gSyl6c ph ps (.imp ch th) (.imp th ch) (synWb ch th) hyp_impbidd_1 hyp_impbidd_2
      p0000
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_impbid21d`. -/
@[expose]
noncomputable def gImpbid21d (ph : Wff) (ps : Wff) (ch : Wff) (th : Wff)
    (hyp_impbid21d_1 : Nominal.NPrf (.imp ps (.imp ch th)))
    (hyp_impbid21d_2 : Nominal.NPrf (.imp ph (.imp th ch))) :
    Nominal.NPrf (.imp ph (.imp ps (synWb ch th))) :=
  by
  have p0000 := @gA1i (.imp ps (.imp ch th)) ph hyp_impbid21d_1
  have p0001 := @gA1d ph (.imp th ch) ps hyp_impbid21d_2
  have p0002 := @gImpbidd ph ps ch th p0000 p0001
  exact p0002

/-- Checked nominal proof certificate identified upstream as `g_impbid`. -/
@[expose]
noncomputable def gImpbid (ph : Wff) (ps : Wff) (ch : Wff)
    (hyp_impbid_1 : Nominal.NPrf (.imp ph (.imp ps ch)))
    (hyp_impbid_2 : Nominal.NPrf (.imp ph (.imp ch ps))) :
    Nominal.NPrf (.imp ph (synWb ps ch)) :=
  by
  have p0000 := @gImpbid21d ph ph ps ch hyp_impbid_1 hyp_impbid_2
  have p0001 := @gPm243i ph (synWb ps ch) p0000
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_dfbi1`. -/
@[expose]
noncomputable def gDfbi1 (ph : Wff) (ps : Wff) :
    Nominal.NPrf (synWb (synWb ph ps) (.neg (.imp (.imp ph ps) (.neg (.imp ps ph))))) :=
  by
  have p0000 := Nominal.biimpRefl (synWb ph ps)
  have p0001 :=
    @gSimplim (.imp (synWb ph ps) (.neg (.imp (.imp ph ps) (.neg (.imp ps ph)))))
      (.neg (.imp (.neg (.imp (.imp ph ps) (.neg (.imp ps ph)))) (synWb ph ps)))
  have p0002 := Nominal.mp p0000 p0001
  have p0003 := @gBi3 ph ps
  have p0004 := @gImpi (.imp ph ps) (.imp ps ph) (synWb ph ps) p0003
  have p0005 :=
    @gImpbii (synWb ph ps) (.neg (.imp (.imp ph ps) (.neg (.imp ps ph)))) p0002 p0004
  exact p0005

/-- Checked nominal proof certificate identified upstream as `g_biimpi`. -/
@[expose]
noncomputable def gBiimpi (ph : Wff) (ps : Wff)
    (hyp_biimpi_1 : Nominal.NPrf (synWb ph ps)) : Nominal.NPrf (.imp ph ps) :=
  by
  have p0000 := @gBi1 ph ps
  have p0001 := Nominal.mp hyp_biimpi_1 p0000
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_sylbi`. -/
@[expose]
noncomputable def gSylbi (ph : Wff) (ps : Wff) (ch : Wff)
    (hyp_sylbi_1 : Nominal.NPrf (synWb ph ps))
    (hyp_sylbi_2 : Nominal.NPrf (.imp ps ch)) : Nominal.NPrf (.imp ph ch) :=
  by
  have p0000 := @gBiimpi ph ps hyp_sylbi_1
  have p0001 := @gSyl ph ps ch p0000 hyp_sylbi_2
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_sylib`. -/
@[expose]
noncomputable def gSylib (ph : Wff) (ps : Wff) (ch : Wff)
    (hyp_sylib_1 : Nominal.NPrf (.imp ph ps))
    (hyp_sylib_2 : Nominal.NPrf (synWb ps ch)) : Nominal.NPrf (.imp ph ch) :=
  by
  have p0000 := @gBiimpi ps ch hyp_sylib_2
  have p0001 := @gSyl ph ps ch hyp_sylib_1 p0000
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_bi2`. -/
@[expose]
noncomputable def gBi2 (ph : Wff) (ps : Wff) :
    Nominal.NPrf (.imp (synWb ph ps) (.imp ps ph)) :=
  by
  have p0000 := @gDfbi1 ph ps
  have p0001 := @gSimprim (.imp ph ps) (.imp ps ph)
  have p0002 :=
    @gSylbi (synWb ph ps) (.neg (.imp (.imp ph ps) (.neg (.imp ps ph)))) (.imp ps ph)
      p0000 p0001
  exact p0002

/-- Checked nominal proof certificate identified upstream as `g_bicom1`. -/
@[expose]
noncomputable def gBicom1 (ph : Wff) (ps : Wff) :
    Nominal.NPrf (.imp (synWb ph ps) (synWb ps ph)) :=
  by
  have p0000 := @gBi2 ph ps
  have p0001 := @gBi1 ph ps
  have p0002 := @gImpbid (synWb ph ps) ps ph p0000 p0001
  exact p0002

/-- Checked nominal proof certificate identified upstream as `g_bicom`. -/
@[expose]
noncomputable def gBicom (ph : Wff) (ps : Wff) :
    Nominal.NPrf (synWb (synWb ph ps) (synWb ps ph)) :=
  by
  have p0000 := @gBicom1 ph ps
  have p0001 := @gBicom1 ps ph
  have p0002 := @gImpbii (synWb ph ps) (synWb ps ph) p0000 p0001
  exact p0002

/-- Checked nominal proof certificate identified upstream as `g_bicomd`. -/
@[expose]
noncomputable def gBicomd (ph : Wff) (ps : Wff) (ch : Wff)
    (hyp_bicomd_1 : Nominal.NPrf (.imp ph (synWb ps ch))) :
    Nominal.NPrf (.imp ph (synWb ch ps)) :=
  by
  have p0000 := @gBicom ps ch
  have p0001 := @gSylib ph (synWb ps ch) (synWb ch ps) hyp_bicomd_1 p0000
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_bicomi`. -/
@[expose]
noncomputable def gBicomi (ph : Wff) (ps : Wff)
    (hyp_bicomi_1 : Nominal.NPrf (synWb ph ps)) : Nominal.NPrf (synWb ps ph) :=
  by
  have p0000 := @gBicom1 ph ps
  have p0001 := Nominal.mp hyp_bicomi_1 p0000
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_impbid1`. -/
@[expose]
noncomputable def gImpbid1 (ph : Wff) (ps : Wff) (ch : Wff)
    (hyp_impbid1_1 : Nominal.NPrf (.imp ph (.imp ps ch)))
    (hyp_impbid1_2 : Nominal.NPrf (.imp ch ps)) : Nominal.NPrf (.imp ph (synWb ps ch)) :=
  by
  have p0000 := @gA1i (.imp ch ps) ph hyp_impbid1_2
  have p0001 := @gImpbid ph ps ch hyp_impbid1_1 p0000
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_impbid2`. -/
@[expose]
noncomputable def gImpbid2 (ph : Wff) (ps : Wff) (ch : Wff)
    (hyp_impbid2_1 : Nominal.NPrf (.imp ps ch))
    (hyp_impbid2_2 : Nominal.NPrf (.imp ph (.imp ch ps))) :
    Nominal.NPrf (.imp ph (synWb ps ch)) :=
  by
  have p0000 := @gImpbid1 ph ch ps hyp_impbid2_2 hyp_impbid2_1
  have p0001 := @gBicomd ph ch ps p0000
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_impcon4bid`. -/
@[expose]
noncomputable def gImpcon4bid (ph : Wff) (ps : Wff) (ch : Wff)
    (hyp_impcon4bid_1 : Nominal.NPrf (.imp ph (.imp ps ch)))
    (hyp_impcon4bid_2 : Nominal.NPrf (.imp ph (.imp (.neg ps) (.neg ch)))) :
    Nominal.NPrf (.imp ph (synWb ps ch)) :=
  by
  have p0000 := @gCon4d ph ps ch hyp_impcon4bid_2
  have p0001 := @gImpbid ph ps ch hyp_impcon4bid_1 p0000
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_biimpri`. -/
@[expose]
noncomputable def gBiimpri (ph : Wff) (ps : Wff)
    (hyp_biimpri_1 : Nominal.NPrf (synWb ph ps)) : Nominal.NPrf (.imp ps ph) :=
  by
  have p0000 := @gBicomi ph ps hyp_biimpri_1
  have p0001 := @gBiimpi ps ph p0000
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_biimpd`. -/
@[expose]
noncomputable def gBiimpd (ph : Wff) (ps : Wff) (ch : Wff)
    (hyp_biimpd_1 : Nominal.NPrf (.imp ph (synWb ps ch))) :
    Nominal.NPrf (.imp ph (.imp ps ch)) :=
  by
  have p0000 := @gBi1 ps ch
  have p0001 := @gSyl ph (synWb ps ch) (.imp ps ch) hyp_biimpd_1 p0000
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_mpbi`. -/
@[expose]
noncomputable def gMpbi (ph : Wff) (ps : Wff) (hyp_mpbi_min : Nominal.NPrf ph)
    (hyp_mpbi_maj : Nominal.NPrf (synWb ph ps)) : Nominal.NPrf ps :=
  by
  have p0000 := @gBiimpi ph ps hyp_mpbi_maj
  have p0001 := Nominal.mp hyp_mpbi_min p0000
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_mpbir`. -/
@[expose]
noncomputable def gMpbir (ph : Wff) (ps : Wff) (hyp_mpbir_min : Nominal.NPrf ps)
    (hyp_mpbir_maj : Nominal.NPrf (synWb ph ps)) : Nominal.NPrf ph :=
  by
  have p0000 := @gBiimpri ph ps hyp_mpbir_maj
  have p0001 := Nominal.mp hyp_mpbir_min p0000
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_mpbid`. -/
@[expose]
noncomputable def gMpbid (ph : Wff) (ps : Wff) (ch : Wff)
    (hyp_mpbid_min : Nominal.NPrf (.imp ph ps))
    (hyp_mpbid_maj : Nominal.NPrf (.imp ph (synWb ps ch))) : Nominal.NPrf (.imp ph ch) :=
  by
  have p0000 := @gBiimpd ph ps ch hyp_mpbid_maj
  have p0001 := @gMpd ph ps ch hyp_mpbid_min p0000
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_mpbii`. -/
@[expose]
noncomputable def gMpbii (ph : Wff) (ps : Wff) (ch : Wff)
    (hyp_mpbii_min : Nominal.NPrf ps)
    (hyp_mpbii_maj : Nominal.NPrf (.imp ph (synWb ps ch))) : Nominal.NPrf (.imp ph ch) :=
  by
  have p0000 := @gA1i ps ph hyp_mpbii_min
  have p0001 := @gMpbid ph ps ch p0000 hyp_mpbii_maj
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_sylibr`. -/
@[expose]
noncomputable def gSylibr (ph : Wff) (ps : Wff) (ch : Wff)
    (hyp_sylibr_1 : Nominal.NPrf (.imp ph ps))
    (hyp_sylibr_2 : Nominal.NPrf (synWb ch ps)) : Nominal.NPrf (.imp ph ch) :=
  by
  have p0000 := @gBiimpri ch ps hyp_sylibr_2
  have p0001 := @gSyl ph ps ch hyp_sylibr_1 p0000
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_sylbir`. -/
@[expose]
noncomputable def gSylbir (ph : Wff) (ps : Wff) (ch : Wff)
    (hyp_sylbir_1 : Nominal.NPrf (synWb ps ph))
    (hyp_sylbir_2 : Nominal.NPrf (.imp ps ch)) : Nominal.NPrf (.imp ph ch) :=
  by
  have p0000 := @gBiimpri ps ph hyp_sylbir_1
  have p0001 := @gSyl ph ps ch p0000 hyp_sylbir_2
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_sylibd`. -/
@[expose]
noncomputable def gSylibd (ph : Wff) (ps : Wff) (ch : Wff) (th : Wff)
    (hyp_sylibd_1 : Nominal.NPrf (.imp ph (.imp ps ch)))
    (hyp_sylibd_2 : Nominal.NPrf (.imp ph (synWb ch th))) :
    Nominal.NPrf (.imp ph (.imp ps th)) :=
  by
  have p0000 := @gBiimpd ph ch th hyp_sylibd_2
  have p0001 := @gSyld ph ps ch th hyp_sylibd_1 p0000
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_sylbid`. -/
@[expose]
noncomputable def gSylbid (ph : Wff) (ps : Wff) (ch : Wff) (th : Wff)
    (hyp_sylbid_1 : Nominal.NPrf (.imp ph (synWb ps ch)))
    (hyp_sylbid_2 : Nominal.NPrf (.imp ph (.imp ch th))) :
    Nominal.NPrf (.imp ph (.imp ps th)) :=
  by
  have p0000 := @gBiimpd ph ps ch hyp_sylbid_1
  have p0001 := @gSyld ph ps ch th p0000 hyp_sylbid_2
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_mpbidi`. -/
@[expose]
noncomputable def gMpbidi (ph : Wff) (ps : Wff) (ch : Wff) (th : Wff)
    (hyp_mpbidi_min : Nominal.NPrf (.imp th (.imp ph ps)))
    (hyp_mpbidi_maj : Nominal.NPrf (.imp ph (synWb ps ch))) :
    Nominal.NPrf (.imp th (.imp ph ch)) :=
  by
  have p0000 := @gBiimpd ph ps ch hyp_mpbidi_maj
  have p0001 := @gSylcom th ph ps ch hyp_mpbidi_min p0000
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_syl5bi`. -/
@[expose]
noncomputable def gSyl5bi (ph : Wff) (ps : Wff) (ch : Wff) (th : Wff)
    (hyp_syl5bi_1 : Nominal.NPrf (synWb ph ps))
    (hyp_syl5bi_2 : Nominal.NPrf (.imp ch (.imp ps th))) :
    Nominal.NPrf (.imp ch (.imp ph th)) :=
  by
  have p0000 := @gBiimpi ph ps hyp_syl5bi_1
  have p0001 := @gSyl5 ph ps ch th p0000 hyp_syl5bi_2
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_syl5bir`. -/
@[expose]
noncomputable def gSyl5bir (ph : Wff) (ps : Wff) (ch : Wff) (th : Wff)
    (hyp_syl5bir_1 : Nominal.NPrf (synWb ps ph))
    (hyp_syl5bir_2 : Nominal.NPrf (.imp ch (.imp ps th))) :
    Nominal.NPrf (.imp ch (.imp ph th)) :=
  by
  have p0000 := @gBiimpri ps ph hyp_syl5bir_1
  have p0001 := @gSyl5 ph ps ch th p0000 hyp_syl5bir_2
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_syl5ib`. -/
@[expose]
noncomputable def gSyl5ib (ph : Wff) (ps : Wff) (ch : Wff) (th : Wff)
    (hyp_syl5ib_1 : Nominal.NPrf (.imp ph ps))
    (hyp_syl5ib_2 : Nominal.NPrf (.imp ch (synWb ps th))) :
    Nominal.NPrf (.imp ch (.imp ph th)) :=
  by
  have p0000 := @gBiimpd ch ps th hyp_syl5ib_2
  have p0001 := @gSyl5 ph ps ch th hyp_syl5ib_1 p0000
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_syl5ibcom`. -/
@[expose]
noncomputable def gSyl5ibcom (ph : Wff) (ps : Wff) (ch : Wff) (th : Wff)
    (hyp_syl5ib_1 : Nominal.NPrf (.imp ph ps))
    (hyp_syl5ib_2 : Nominal.NPrf (.imp ch (synWb ps th))) :
    Nominal.NPrf (.imp ph (.imp ch th)) :=
  by
  have p0000 := @gSyl5ib ph ps ch th hyp_syl5ib_1 hyp_syl5ib_2
  have p0001 := @gCom12 ch ph th p0000
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_syl5ibr`. -/
@[expose]
noncomputable def gSyl5ibr (ph : Wff) (ps : Wff) (ch : Wff) (th : Wff)
    (hyp_syl5ibr_1 : Nominal.NPrf (.imp ph th))
    (hyp_syl5ibr_2 : Nominal.NPrf (.imp ch (synWb ps th))) :
    Nominal.NPrf (.imp ch (.imp ph ps)) :=
  by
  have p0000 := @gBicomd ch ps th hyp_syl5ibr_2
  have p0001 := @gSyl5ib ph th ch ps hyp_syl5ibr_1 p0000
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_syl5ibrcom`. -/
@[expose]
noncomputable def gSyl5ibrcom (ph : Wff) (ps : Wff) (ch : Wff) (th : Wff)
    (hyp_syl5ibr_1 : Nominal.NPrf (.imp ph th))
    (hyp_syl5ibr_2 : Nominal.NPrf (.imp ch (synWb ps th))) :
    Nominal.NPrf (.imp ph (.imp ch ps)) :=
  by
  have p0000 := @gSyl5ibr ph ps ch th hyp_syl5ibr_1 hyp_syl5ibr_2
  have p0001 := @gCom12 ch ph ps p0000
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_biimprd`. -/
@[expose]
noncomputable def gBiimprd (ph : Wff) (ps : Wff) (ch : Wff)
    (hyp_biimprd_1 : Nominal.NPrf (.imp ph (synWb ps ch))) :
    Nominal.NPrf (.imp ph (.imp ch ps)) :=
  by
  have p0000 := @gId ch
  have p0001 := @gSyl5ibr ch ps ph ch p0000 hyp_biimprd_1
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_biimpcd`. -/
@[expose]
noncomputable def gBiimpcd (ph : Wff) (ps : Wff) (ch : Wff)
    (hyp_biimpcd_1 : Nominal.NPrf (.imp ph (synWb ps ch))) :
    Nominal.NPrf (.imp ps (.imp ph ch)) :=
  by
  have p0000 := @gId ps
  have p0001 := @gSyl5ibcom ps ps ph ch p0000 hyp_biimpcd_1
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_biimprcd`. -/
@[expose]
noncomputable def gBiimprcd (ph : Wff) (ps : Wff) (ch : Wff)
    (hyp_biimpcd_1 : Nominal.NPrf (.imp ph (synWb ps ch))) :
    Nominal.NPrf (.imp ch (.imp ph ps)) :=
  by
  have p0000 := @gId ch
  have p0001 := @gSyl5ibrcom ch ps ph ch p0000 hyp_biimpcd_1
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_syl6ib`. -/
@[expose]
noncomputable def gSyl6ib (ph : Wff) (ps : Wff) (ch : Wff) (th : Wff)
    (hyp_syl6ib_1 : Nominal.NPrf (.imp ph (.imp ps ch)))
    (hyp_syl6ib_2 : Nominal.NPrf (synWb ch th)) : Nominal.NPrf (.imp ph (.imp ps th)) :=
  by
  have p0000 := @gBiimpi ch th hyp_syl6ib_2
  have p0001 := @gSyl6 ph ps ch th hyp_syl6ib_1 p0000
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_syl6ibr`. -/
@[expose]
noncomputable def gSyl6ibr (ph : Wff) (ps : Wff) (ch : Wff) (th : Wff)
    (hyp_syl6ibr_1 : Nominal.NPrf (.imp ph (.imp ps ch)))
    (hyp_syl6ibr_2 : Nominal.NPrf (synWb th ch)) : Nominal.NPrf (.imp ph (.imp ps th)) :=
  by
  have p0000 := @gBiimpri th ch hyp_syl6ibr_2
  have p0001 := @gSyl6 ph ps ch th hyp_syl6ibr_1 p0000
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_syl6bi`. -/
@[expose]
noncomputable def gSyl6bi (ph : Wff) (ps : Wff) (ch : Wff) (th : Wff)
    (hyp_syl6bi_1 : Nominal.NPrf (.imp ph (synWb ps ch)))
    (hyp_syl6bi_2 : Nominal.NPrf (.imp ch th)) : Nominal.NPrf (.imp ph (.imp ps th)) :=
  by
  have p0000 := @gBiimpd ph ps ch hyp_syl6bi_1
  have p0001 := @gSyl6 ph ps ch th p0000 hyp_syl6bi_2
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_syl6bir`. -/
@[expose]
noncomputable def gSyl6bir (ph : Wff) (ps : Wff) (ch : Wff) (th : Wff)
    (hyp_syl6bir_1 : Nominal.NPrf (.imp ph (synWb ch ps)))
    (hyp_syl6bir_2 : Nominal.NPrf (.imp ch th)) : Nominal.NPrf (.imp ph (.imp ps th)) :=
  by
  have p0000 := @gBiimprd ph ch ps hyp_syl6bir_1
  have p0001 := @gSyl6 ph ps ch th p0000 hyp_syl6bir_2
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_syl7bi`. -/
@[expose]
noncomputable def gSyl7bi (ph : Wff) (ps : Wff) (ch : Wff) (th : Wff) (ta : Wff)
    (hyp_syl7bi_1 : Nominal.NPrf (synWb ph ps))
    (hyp_syl7bi_2 : Nominal.NPrf (.imp ch (.imp th (.imp ps ta)))) :
    Nominal.NPrf (.imp ch (.imp th (.imp ph ta))) :=
  by
  have p0000 := @gBiimpi ph ps hyp_syl7bi_1
  have p0001 := @gSyl7 ph ps ch th ta p0000 hyp_syl7bi_2
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_syl8ib`. -/
@[expose]
noncomputable def gSyl8ib (ph : Wff) (ps : Wff) (ch : Wff) (th : Wff) (ta : Wff)
    (hyp_syl8ib_1 : Nominal.NPrf (.imp ph (.imp ps (.imp ch th))))
    (hyp_syl8ib_2 : Nominal.NPrf (synWb th ta)) :
    Nominal.NPrf (.imp ph (.imp ps (.imp ch ta))) :=
  by
  have p0000 := @gBiimpi th ta hyp_syl8ib_2
  have p0001 := @gSyl8 ph ps ch th ta hyp_syl8ib_1 p0000
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_mpbird`. -/
@[expose]
noncomputable def gMpbird (ph : Wff) (ps : Wff) (ch : Wff)
    (hyp_mpbird_min : Nominal.NPrf (.imp ph ch))
    (hyp_mpbird_maj : Nominal.NPrf (.imp ph (synWb ps ch))) :
    Nominal.NPrf (.imp ph ps) :=
  by
  have p0000 := @gBiimprd ph ps ch hyp_mpbird_maj
  have p0001 := @gMpd ph ch ps hyp_mpbird_min p0000
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_mpbiri`. -/
@[expose]
noncomputable def gMpbiri (ph : Wff) (ps : Wff) (ch : Wff)
    (hyp_mpbiri_min : Nominal.NPrf ch)
    (hyp_mpbiri_maj : Nominal.NPrf (.imp ph (synWb ps ch))) :
    Nominal.NPrf (.imp ph ps) :=
  by
  have p0000 := @gA1i ch ph hyp_mpbiri_min
  have p0001 := @gMpbird ph ps ch p0000 hyp_mpbiri_maj
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_sylibrd`. -/
@[expose]
noncomputable def gSylibrd (ph : Wff) (ps : Wff) (ch : Wff) (th : Wff)
    (hyp_sylibrd_1 : Nominal.NPrf (.imp ph (.imp ps ch)))
    (hyp_sylibrd_2 : Nominal.NPrf (.imp ph (synWb th ch))) :
    Nominal.NPrf (.imp ph (.imp ps th)) :=
  by
  have p0000 := @gBiimprd ph th ch hyp_sylibrd_2
  have p0001 := @gSyld ph ps ch th hyp_sylibrd_1 p0000
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_sylbird`. -/
@[expose]
noncomputable def gSylbird (ph : Wff) (ps : Wff) (ch : Wff) (th : Wff)
    (hyp_sylbird_1 : Nominal.NPrf (.imp ph (synWb ch ps)))
    (hyp_sylbird_2 : Nominal.NPrf (.imp ph (.imp ch th))) :
    Nominal.NPrf (.imp ph (.imp ps th)) :=
  by
  have p0000 := @gBiimprd ph ch ps hyp_sylbird_1
  have p0001 := @gSyld ph ps ch th p0000 hyp_sylbird_2
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_biid`. -/
@[expose]
noncomputable def gBiid (ph : Wff) : Nominal.NPrf (synWb ph ph) :=
  by
  have p0000 := @gId ph
  have p0001 := @gImpbii ph ph p0000 p0000
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_biidd`. -/
@[expose]
noncomputable def gBiidd (ph : Wff) (ps : Wff) : Nominal.NPrf (.imp ph (synWb ps ps)) :=
  by
  have p0000 := @gBiid ps
  have p0001 := @gA1i (synWb ps ps) ph p0000
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_pm5_1im`. -/
@[expose]
noncomputable def gPm51im (ph : Wff) (ps : Wff) :
    Nominal.NPrf (.imp ph (.imp ps (synWb ph ps))) :=
  by
  have p0000 := Nominal.ax1 ps ph
  have p0001 := Nominal.ax1 ph ps
  have p0002 := @gImpbid21d ph ps ph ps p0000 p0001
  exact p0002

/-- Checked nominal proof certificate identified upstream as `g_n_2th`. -/
@[expose]
noncomputable def gN2th (ph : Wff) (ps : Wff) (hyp_n_2th_1 : Nominal.NPrf ph)
    (hyp_n_2th_2 : Nominal.NPrf ps) : Nominal.NPrf (synWb ph ps) :=
  by
  have p0000 := @gA1i ps ph hyp_n_2th_2
  have p0001 := @gA1i ph ps hyp_n_2th_1
  have p0002 := @gImpbii ph ps p0000 p0001
  exact p0002

/-- Checked nominal proof certificate identified upstream as `g_n_2thd`. -/
@[expose]
noncomputable def gN2thd (ph : Wff) (ps : Wff) (ch : Wff)
    (hyp_n_2thd_1 : Nominal.NPrf (.imp ph ps))
    (hyp_n_2thd_2 : Nominal.NPrf (.imp ph ch)) : Nominal.NPrf (.imp ph (synWb ps ch)) :=
  by
  have p0000 := @gPm51im ps ch
  have p0001 := @gSylc ph ps ch (synWb ps ch) hyp_n_2thd_1 hyp_n_2thd_2 p0000
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_ibi`. -/
@[expose]
noncomputable def gIbi (ph : Wff) (ps : Wff)
    (hyp_ibi_1 : Nominal.NPrf (.imp ph (synWb ph ps))) : Nominal.NPrf (.imp ph ps) :=
  by
  have p0000 := @gBiimpd ph ph ps hyp_ibi_1
  have p0001 := @gPm243i ph ps p0000
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_ibir`. -/
@[expose]
noncomputable def gIbir (ph : Wff) (ps : Wff)
    (hyp_ibir_1 : Nominal.NPrf (.imp ph (synWb ps ph))) : Nominal.NPrf (.imp ph ps) :=
  by
  have p0000 := @gBicomd ph ps ph hyp_ibir_1
  have p0001 := @gIbi ph ps p0000
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_ibd`. -/
@[expose]
noncomputable def gIbd (ph : Wff) (ps : Wff) (ch : Wff)
    (hyp_ibd_1 : Nominal.NPrf (.imp ph (.imp ps (synWb ps ch)))) :
    Nominal.NPrf (.imp ph (.imp ps ch)) :=
  by
  have p0000 := @gBi1 ps ch
  have p0001 := @gSyli ps ph (synWb ps ch) ch hyp_ibd_1 p0000
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_pm5_74`. -/
@[expose]
noncomputable def gPm574 (ph : Wff) (ps : Wff) (ch : Wff) :
    Nominal.NPrf (synWb (.imp ph (synWb ps ch)) (synWb (.imp ph ps) (.imp ph ch))) :=
  by
  have p0000 := @gBi1 ps ch
  have p0001 := @gImim3i (synWb ps ch) ps ch ph p0000
  have p0002 := @gBi2 ps ch
  have p0003 := @gImim3i (synWb ps ch) ch ps ph p0002
  have p0004 := @gImpbid (.imp ph (synWb ps ch)) (.imp ph ps) (.imp ph ch) p0001 p0003
  have p0005 := @gBi1 (.imp ph ps) (.imp ph ch)
  have p0006 := @gPm286d (synWb (.imp ph ps) (.imp ph ch)) ph ps ch p0005
  have p0007 := @gBi2 (.imp ph ps) (.imp ph ch)
  have p0008 := @gPm286d (synWb (.imp ph ps) (.imp ph ch)) ph ch ps p0007
  have p0009 := @gImpbidd (synWb (.imp ph ps) (.imp ph ch)) ph ps ch p0006 p0008
  have p0010 :=
    @gImpbii (.imp ph (synWb ps ch)) (synWb (.imp ph ps) (.imp ph ch)) p0004 p0009
  exact p0010

/-- Checked nominal proof certificate identified upstream as `g_pm5_74i`. -/
@[expose]
noncomputable def gPm574i (ph : Wff) (ps : Wff) (ch : Wff)
    (hyp_pm5_74i_1 : Nominal.NPrf (.imp ph (synWb ps ch))) :
    Nominal.NPrf (synWb (.imp ph ps) (.imp ph ch)) :=
  by
  have p0000 := @gPm574 ph ps ch
  have p0001 :=
    @gMpbi (.imp ph (synWb ps ch)) (synWb (.imp ph ps) (.imp ph ch)) hyp_pm5_74i_1
      p0000
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_pm5_74ri`. -/
@[expose]
noncomputable def gPm574ri (ph : Wff) (ps : Wff) (ch : Wff)
    (hyp_pm5_74ri_1 : Nominal.NPrf (synWb (.imp ph ps) (.imp ph ch))) :
    Nominal.NPrf (.imp ph (synWb ps ch)) :=
  by
  have p0000 := @gPm574 ph ps ch
  have p0001 :=
    @gMpbir (.imp ph (synWb ps ch)) (synWb (.imp ph ps) (.imp ph ch)) hyp_pm5_74ri_1
      p0000
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_pm5_74d`. -/
@[expose]
noncomputable def gPm574d (ph : Wff) (ps : Wff) (ch : Wff) (th : Wff)
    (hyp_pm5_74d_1 : Nominal.NPrf (.imp ph (.imp ps (synWb ch th)))) :
    Nominal.NPrf (.imp ph (synWb (.imp ps ch) (.imp ps th))) :=
  by
  have p0000 := @gPm574 ps ch th
  have p0001 :=
    @gSylib ph (.imp ps (synWb ch th)) (synWb (.imp ps ch) (.imp ps th)) hyp_pm5_74d_1
      p0000
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_bitri`. -/
@[expose]
noncomputable def gBitri (ph : Wff) (ps : Wff) (ch : Wff)
    (hyp_bitri_1 : Nominal.NPrf (synWb ph ps))
    (hyp_bitri_2 : Nominal.NPrf (synWb ps ch)) : Nominal.NPrf (synWb ph ch) :=
  by
  have p0000 := @gBiimpi ph ps hyp_bitri_1
  have p0001 := @gSylib ph ps ch p0000 hyp_bitri_2
  have p0002 := @gBiimpri ps ch hyp_bitri_2
  have p0003 := @gSylibr ch ps ph p0002 hyp_bitri_1
  have p0004 := @gImpbii ph ch p0001 p0003
  exact p0004

/-- Checked nominal proof certificate identified upstream as `g_bitr2i`. -/
@[expose]
noncomputable def gBitr2i (ph : Wff) (ps : Wff) (ch : Wff)
    (hyp_bitr2i_1 : Nominal.NPrf (synWb ph ps))
    (hyp_bitr2i_2 : Nominal.NPrf (synWb ps ch)) : Nominal.NPrf (synWb ch ph) :=
  by
  have p0000 := @gBitri ph ps ch hyp_bitr2i_1 hyp_bitr2i_2
  have p0001 := @gBicomi ph ch p0000
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_bitr3i`. -/
@[expose]
noncomputable def gBitr3i (ph : Wff) (ps : Wff) (ch : Wff)
    (hyp_bitr3i_1 : Nominal.NPrf (synWb ps ph))
    (hyp_bitr3i_2 : Nominal.NPrf (synWb ps ch)) : Nominal.NPrf (synWb ph ch) :=
  by
  have p0000 := @gBicomi ps ph hyp_bitr3i_1
  have p0001 := @gBitri ph ps ch p0000 hyp_bitr3i_2
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_bitr4i`. -/
@[expose]
noncomputable def gBitr4i (ph : Wff) (ps : Wff) (ch : Wff)
    (hyp_bitr4i_1 : Nominal.NPrf (synWb ph ps))
    (hyp_bitr4i_2 : Nominal.NPrf (synWb ch ps)) : Nominal.NPrf (synWb ph ch) :=
  by
  have p0000 := @gBicomi ch ps hyp_bitr4i_2
  have p0001 := @gBitri ph ps ch hyp_bitr4i_1 p0000
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_bitrd`. -/
@[expose]
noncomputable def gBitrd (ph : Wff) (ps : Wff) (ch : Wff) (th : Wff)
    (hyp_bitrd_1 : Nominal.NPrf (.imp ph (synWb ps ch)))
    (hyp_bitrd_2 : Nominal.NPrf (.imp ph (synWb ch th))) :
    Nominal.NPrf (.imp ph (synWb ps th)) :=
  by
  have p0000 := @gPm574i ph ps ch hyp_bitrd_1
  have p0001 := @gPm574i ph ch th hyp_bitrd_2
  have p0002 := @gBitri (.imp ph ps) (.imp ph ch) (.imp ph th) p0000 p0001
  have p0003 := @gPm574ri ph ps th p0002
  exact p0003

/-- Checked nominal proof certificate identified upstream as `g_bitr2d`. -/
@[expose]
noncomputable def gBitr2d (ph : Wff) (ps : Wff) (ch : Wff) (th : Wff)
    (hyp_bitr2d_1 : Nominal.NPrf (.imp ph (synWb ps ch)))
    (hyp_bitr2d_2 : Nominal.NPrf (.imp ph (synWb ch th))) :
    Nominal.NPrf (.imp ph (synWb th ps)) :=
  by
  have p0000 := @gBitrd ph ps ch th hyp_bitr2d_1 hyp_bitr2d_2
  have p0001 := @gBicomd ph ps th p0000
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_bitr3d`. -/
@[expose]
noncomputable def gBitr3d (ph : Wff) (ps : Wff) (ch : Wff) (th : Wff)
    (hyp_bitr3d_1 : Nominal.NPrf (.imp ph (synWb ps ch)))
    (hyp_bitr3d_2 : Nominal.NPrf (.imp ph (synWb ps th))) :
    Nominal.NPrf (.imp ph (synWb ch th)) :=
  by
  have p0000 := @gBicomd ph ps ch hyp_bitr3d_1
  have p0001 := @gBitrd ph ch ps th p0000 hyp_bitr3d_2
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_bitr4d`. -/
@[expose]
noncomputable def gBitr4d (ph : Wff) (ps : Wff) (ch : Wff) (th : Wff)
    (hyp_bitr4d_1 : Nominal.NPrf (.imp ph (synWb ps ch)))
    (hyp_bitr4d_2 : Nominal.NPrf (.imp ph (synWb th ch))) :
    Nominal.NPrf (.imp ph (synWb ps th)) :=
  by
  have p0000 := @gBicomd ph th ch hyp_bitr4d_2
  have p0001 := @gBitrd ph ps ch th hyp_bitr4d_1 p0000
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_syl5bb`. -/
@[expose]
noncomputable def gSyl5bb (ph : Wff) (ps : Wff) (ch : Wff) (th : Wff)
    (hyp_syl5bb_1 : Nominal.NPrf (synWb ph ps))
    (hyp_syl5bb_2 : Nominal.NPrf (.imp ch (synWb ps th))) :
    Nominal.NPrf (.imp ch (synWb ph th)) :=
  by
  have p0000 := @gA1i (synWb ph ps) ch hyp_syl5bb_1
  have p0001 := @gBitrd ch ph ps th p0000 hyp_syl5bb_2
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_syl5rbb`. -/
@[expose]
noncomputable def gSyl5rbb (ph : Wff) (ps : Wff) (ch : Wff) (th : Wff)
    (hyp_syl5rbb_1 : Nominal.NPrf (synWb ph ps))
    (hyp_syl5rbb_2 : Nominal.NPrf (.imp ch (synWb ps th))) :
    Nominal.NPrf (.imp ch (synWb th ph)) :=
  by
  have p0000 := @gSyl5bb ph ps ch th hyp_syl5rbb_1 hyp_syl5rbb_2
  have p0001 := @gBicomd ch ph th p0000
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_syl5bbr`. -/
@[expose]
noncomputable def gSyl5bbr (ph : Wff) (ps : Wff) (ch : Wff) (th : Wff)
    (hyp_syl5bbr_1 : Nominal.NPrf (synWb ps ph))
    (hyp_syl5bbr_2 : Nominal.NPrf (.imp ch (synWb ps th))) :
    Nominal.NPrf (.imp ch (synWb ph th)) :=
  by
  have p0000 := @gBicomi ps ph hyp_syl5bbr_1
  have p0001 := @gSyl5bb ph ps ch th p0000 hyp_syl5bbr_2
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_syl5rbbr`. -/
@[expose]
noncomputable def gSyl5rbbr (ph : Wff) (ps : Wff) (ch : Wff) (th : Wff)
    (hyp_syl5rbbr_1 : Nominal.NPrf (synWb ps ph))
    (hyp_syl5rbbr_2 : Nominal.NPrf (.imp ch (synWb ps th))) :
    Nominal.NPrf (.imp ch (synWb th ph)) :=
  by
  have p0000 := @gBicomi ps ph hyp_syl5rbbr_1
  have p0001 := @gSyl5rbb ph ps ch th p0000 hyp_syl5rbbr_2
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_syl6bb`. -/
@[expose]
noncomputable def gSyl6bb (ph : Wff) (ps : Wff) (ch : Wff) (th : Wff)
    (hyp_syl6bb_1 : Nominal.NPrf (.imp ph (synWb ps ch)))
    (hyp_syl6bb_2 : Nominal.NPrf (synWb ch th)) :
    Nominal.NPrf (.imp ph (synWb ps th)) :=
  by
  have p0000 := @gA1i (synWb ch th) ph hyp_syl6bb_2
  have p0001 := @gBitrd ph ps ch th hyp_syl6bb_1 p0000
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_syl6rbb`. -/
@[expose]
noncomputable def gSyl6rbb (ph : Wff) (ps : Wff) (ch : Wff) (th : Wff)
    (hyp_syl6rbb_1 : Nominal.NPrf (.imp ph (synWb ps ch)))
    (hyp_syl6rbb_2 : Nominal.NPrf (synWb ch th)) :
    Nominal.NPrf (.imp ph (synWb th ps)) :=
  by
  have p0000 := @gSyl6bb ph ps ch th hyp_syl6rbb_1 hyp_syl6rbb_2
  have p0001 := @gBicomd ph ps th p0000
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_syl6bbr`. -/
@[expose]
noncomputable def gSyl6bbr (ph : Wff) (ps : Wff) (ch : Wff) (th : Wff)
    (hyp_syl6bbr_1 : Nominal.NPrf (.imp ph (synWb ps ch)))
    (hyp_syl6bbr_2 : Nominal.NPrf (synWb th ch)) :
    Nominal.NPrf (.imp ph (synWb ps th)) :=
  by
  have p0000 := @gBicomi th ch hyp_syl6bbr_2
  have p0001 := @gSyl6bb ph ps ch th hyp_syl6bbr_1 p0000
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_syl6rbbr`. -/
@[expose]
noncomputable def gSyl6rbbr (ph : Wff) (ps : Wff) (ch : Wff) (th : Wff)
    (hyp_syl6rbbr_1 : Nominal.NPrf (.imp ph (synWb ps ch)))
    (hyp_syl6rbbr_2 : Nominal.NPrf (synWb th ch)) :
    Nominal.NPrf (.imp ph (synWb th ps)) :=
  by
  have p0000 := @gBicomi th ch hyp_syl6rbbr_2
  have p0001 := @gSyl6rbb ph ps ch th hyp_syl6rbbr_1 p0000
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_n_3imtr3i`. -/
@[expose]
noncomputable def gN3imtr3i (ph : Wff) (ps : Wff) (ch : Wff) (th : Wff)
    (hyp_n_3imtr3_1 : Nominal.NPrf (.imp ph ps))
    (hyp_n_3imtr3_2 : Nominal.NPrf (synWb ph ch))
    (hyp_n_3imtr3_3 : Nominal.NPrf (synWb ps th)) : Nominal.NPrf (.imp ch th) :=
  by
  have p0000 := @gSylbir ch ph ps hyp_n_3imtr3_2 hyp_n_3imtr3_1
  have p0001 := @gSylib ch ps th p0000 hyp_n_3imtr3_3
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_n_3imtr4i`. -/
@[expose]
noncomputable def gN3imtr4i (ph : Wff) (ps : Wff) (ch : Wff) (th : Wff)
    (hyp_n_3imtr4_1 : Nominal.NPrf (.imp ph ps))
    (hyp_n_3imtr4_2 : Nominal.NPrf (synWb ch ph))
    (hyp_n_3imtr4_3 : Nominal.NPrf (synWb th ps)) : Nominal.NPrf (.imp ch th) :=
  by
  have p0000 := @gSylbi ch ph ps hyp_n_3imtr4_2 hyp_n_3imtr4_1
  have p0001 := @gSylibr ch ps th p0000 hyp_n_3imtr4_3
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_n_3imtr3d`. -/
@[expose]
noncomputable def gN3imtr3d (ph : Wff) (ps : Wff) (ch : Wff) (th : Wff) (ta : Wff)
    (hyp_n_3imtr3d_1 : Nominal.NPrf (.imp ph (.imp ps ch)))
    (hyp_n_3imtr3d_2 : Nominal.NPrf (.imp ph (synWb ps th)))
    (hyp_n_3imtr3d_3 : Nominal.NPrf (.imp ph (synWb ch ta))) :
    Nominal.NPrf (.imp ph (.imp th ta)) :=
  by
  have p0000 := @gSylibd ph ps ch ta hyp_n_3imtr3d_1 hyp_n_3imtr3d_3
  have p0001 := @gSylbird ph th ps ta hyp_n_3imtr3d_2 p0000
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_n_3imtr4d`. -/
@[expose]
noncomputable def gN3imtr4d (ph : Wff) (ps : Wff) (ch : Wff) (th : Wff) (ta : Wff)
    (hyp_n_3imtr4d_1 : Nominal.NPrf (.imp ph (.imp ps ch)))
    (hyp_n_3imtr4d_2 : Nominal.NPrf (.imp ph (synWb th ps)))
    (hyp_n_3imtr4d_3 : Nominal.NPrf (.imp ph (synWb ta ch))) :
    Nominal.NPrf (.imp ph (.imp th ta)) :=
  by
  have p0000 := @gSylibrd ph ps ch ta hyp_n_3imtr4d_1 hyp_n_3imtr4d_3
  have p0001 := @gSylbid ph th ps ta hyp_n_3imtr4d_2 p0000
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_n_3imtr3g`. -/
@[expose]
noncomputable def gN3imtr3g (ph : Wff) (ps : Wff) (ch : Wff) (th : Wff) (ta : Wff)
    (hyp_n_3imtr3g_1 : Nominal.NPrf (.imp ph (.imp ps ch)))
    (hyp_n_3imtr3g_2 : Nominal.NPrf (synWb ps th))
    (hyp_n_3imtr3g_3 : Nominal.NPrf (synWb ch ta)) :
    Nominal.NPrf (.imp ph (.imp th ta)) :=
  by
  have p0000 := @gSyl5bir th ps ph ch hyp_n_3imtr3g_2 hyp_n_3imtr3g_1
  have p0001 := @gSyl6ib ph th ch ta p0000 hyp_n_3imtr3g_3
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_n_3imtr4g`. -/
@[expose]
noncomputable def gN3imtr4g (ph : Wff) (ps : Wff) (ch : Wff) (th : Wff) (ta : Wff)
    (hyp_n_3imtr4g_1 : Nominal.NPrf (.imp ph (.imp ps ch)))
    (hyp_n_3imtr4g_2 : Nominal.NPrf (synWb th ps))
    (hyp_n_3imtr4g_3 : Nominal.NPrf (synWb ta ch)) :
    Nominal.NPrf (.imp ph (.imp th ta)) :=
  by
  have p0000 := @gSyl5bi th ps ph ch hyp_n_3imtr4g_2 hyp_n_3imtr4g_1
  have p0001 := @gSyl6ibr ph th ch ta p0000 hyp_n_3imtr4g_3
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_n_3bitri`. -/
@[expose]
noncomputable def gN3bitri (ph : Wff) (ps : Wff) (ch : Wff) (th : Wff)
    (hyp_n_3bitri_1 : Nominal.NPrf (synWb ph ps))
    (hyp_n_3bitri_2 : Nominal.NPrf (synWb ps ch))
    (hyp_n_3bitri_3 : Nominal.NPrf (synWb ch th)) : Nominal.NPrf (synWb ph th) :=
  by
  have p0000 := @gBitri ps ch th hyp_n_3bitri_2 hyp_n_3bitri_3
  have p0001 := @gBitri ph ps th hyp_n_3bitri_1 p0000
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_n_3bitrri`. -/
@[expose]
noncomputable def gN3bitrri (ph : Wff) (ps : Wff) (ch : Wff) (th : Wff)
    (hyp_n_3bitri_1 : Nominal.NPrf (synWb ph ps))
    (hyp_n_3bitri_2 : Nominal.NPrf (synWb ps ch))
    (hyp_n_3bitri_3 : Nominal.NPrf (synWb ch th)) : Nominal.NPrf (synWb th ph) :=
  by
  have p0000 := @gBitr2i ph ps ch hyp_n_3bitri_1 hyp_n_3bitri_2
  have p0001 := @gBitr3i th ch ph hyp_n_3bitri_3 p0000
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_n_3bitr2i`. -/
@[expose]
noncomputable def gN3bitr2i (ph : Wff) (ps : Wff) (ch : Wff) (th : Wff)
    (hyp_n_3bitr2i_1 : Nominal.NPrf (synWb ph ps))
    (hyp_n_3bitr2i_2 : Nominal.NPrf (synWb ch ps))
    (hyp_n_3bitr2i_3 : Nominal.NPrf (synWb ch th)) : Nominal.NPrf (synWb ph th) :=
  by
  have p0000 := @gBitr4i ph ps ch hyp_n_3bitr2i_1 hyp_n_3bitr2i_2
  have p0001 := @gBitri ph ch th p0000 hyp_n_3bitr2i_3
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_n_3bitr2ri`. -/
@[expose]
noncomputable def gN3bitr2ri (ph : Wff) (ps : Wff) (ch : Wff) (th : Wff)
    (hyp_n_3bitr2i_1 : Nominal.NPrf (synWb ph ps))
    (hyp_n_3bitr2i_2 : Nominal.NPrf (synWb ch ps))
    (hyp_n_3bitr2i_3 : Nominal.NPrf (synWb ch th)) : Nominal.NPrf (synWb th ph) :=
  by
  have p0000 := @gBitr4i ph ps ch hyp_n_3bitr2i_1 hyp_n_3bitr2i_2
  have p0001 := @gBitr2i ph ch th p0000 hyp_n_3bitr2i_3
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_n_3bitr3i`. -/
@[expose]
noncomputable def gN3bitr3i (ph : Wff) (ps : Wff) (ch : Wff) (th : Wff)
    (hyp_n_3bitr3i_1 : Nominal.NPrf (synWb ph ps))
    (hyp_n_3bitr3i_2 : Nominal.NPrf (synWb ph ch))
    (hyp_n_3bitr3i_3 : Nominal.NPrf (synWb ps th)) : Nominal.NPrf (synWb ch th) :=
  by
  have p0000 := @gBitr3i ch ph ps hyp_n_3bitr3i_2 hyp_n_3bitr3i_1
  have p0001 := @gBitri ch ps th p0000 hyp_n_3bitr3i_3
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_n_3bitr3ri`. -/
@[expose]
noncomputable def gN3bitr3ri (ph : Wff) (ps : Wff) (ch : Wff) (th : Wff)
    (hyp_n_3bitr3i_1 : Nominal.NPrf (synWb ph ps))
    (hyp_n_3bitr3i_2 : Nominal.NPrf (synWb ph ch))
    (hyp_n_3bitr3i_3 : Nominal.NPrf (synWb ps th)) : Nominal.NPrf (synWb th ch) :=
  by
  have p0000 := @gBitr3i ps ph ch hyp_n_3bitr3i_1 hyp_n_3bitr3i_2
  have p0001 := @gBitr3i th ps ch hyp_n_3bitr3i_3 p0000
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_n_3bitr4i`. -/
@[expose]
noncomputable def gN3bitr4i (ph : Wff) (ps : Wff) (ch : Wff) (th : Wff)
    (hyp_n_3bitr4i_1 : Nominal.NPrf (synWb ph ps))
    (hyp_n_3bitr4i_2 : Nominal.NPrf (synWb ch ph))
    (hyp_n_3bitr4i_3 : Nominal.NPrf (synWb th ps)) : Nominal.NPrf (synWb ch th) :=
  by
  have p0000 := @gBitr4i ph ps th hyp_n_3bitr4i_1 hyp_n_3bitr4i_3
  have p0001 := @gBitri ch ph th hyp_n_3bitr4i_2 p0000
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_n_3bitr4ri`. -/
@[expose]
noncomputable def gN3bitr4ri (ph : Wff) (ps : Wff) (ch : Wff) (th : Wff)
    (hyp_n_3bitr4i_1 : Nominal.NPrf (synWb ph ps))
    (hyp_n_3bitr4i_2 : Nominal.NPrf (synWb ch ph))
    (hyp_n_3bitr4i_3 : Nominal.NPrf (synWb th ps)) : Nominal.NPrf (synWb th ch) :=
  by
  have p0000 := @gBitr4i ph ps th hyp_n_3bitr4i_1 hyp_n_3bitr4i_3
  have p0001 := @gBitr2i ch ph th hyp_n_3bitr4i_2 p0000
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_n_3bitrd`. -/
@[expose]
noncomputable def gN3bitrd (ph : Wff) (ps : Wff) (ch : Wff) (th : Wff) (ta : Wff)
    (hyp_n_3bitrd_1 : Nominal.NPrf (.imp ph (synWb ps ch)))
    (hyp_n_3bitrd_2 : Nominal.NPrf (.imp ph (synWb ch th)))
    (hyp_n_3bitrd_3 : Nominal.NPrf (.imp ph (synWb th ta))) :
    Nominal.NPrf (.imp ph (synWb ps ta)) :=
  by
  have p0000 := @gBitrd ph ps ch th hyp_n_3bitrd_1 hyp_n_3bitrd_2
  have p0001 := @gBitrd ph ps th ta p0000 hyp_n_3bitrd_3
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_n_3bitr2rd`. -/
@[expose]
noncomputable def gN3bitr2rd (ph : Wff) (ps : Wff) (ch : Wff) (th : Wff) (ta : Wff)
    (hyp_n_3bitr2d_1 : Nominal.NPrf (.imp ph (synWb ps ch)))
    (hyp_n_3bitr2d_2 : Nominal.NPrf (.imp ph (synWb th ch)))
    (hyp_n_3bitr2d_3 : Nominal.NPrf (.imp ph (synWb th ta))) :
    Nominal.NPrf (.imp ph (synWb ta ps)) :=
  by
  have p0000 := @gBitr4d ph ps ch th hyp_n_3bitr2d_1 hyp_n_3bitr2d_2
  have p0001 := @gBitr2d ph ps th ta p0000 hyp_n_3bitr2d_3
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_n_3bitr3d`. -/
@[expose]
noncomputable def gN3bitr3d (ph : Wff) (ps : Wff) (ch : Wff) (th : Wff) (ta : Wff)
    (hyp_n_3bitr3d_1 : Nominal.NPrf (.imp ph (synWb ps ch)))
    (hyp_n_3bitr3d_2 : Nominal.NPrf (.imp ph (synWb ps th)))
    (hyp_n_3bitr3d_3 : Nominal.NPrf (.imp ph (synWb ch ta))) :
    Nominal.NPrf (.imp ph (synWb th ta)) :=
  by
  have p0000 := @gBitr3d ph ps th ch hyp_n_3bitr3d_2 hyp_n_3bitr3d_1
  have p0001 := @gBitrd ph th ch ta p0000 hyp_n_3bitr3d_3
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_n_3bitr4d`. -/
@[expose]
noncomputable def gN3bitr4d (ph : Wff) (ps : Wff) (ch : Wff) (th : Wff) (ta : Wff)
    (hyp_n_3bitr4d_1 : Nominal.NPrf (.imp ph (synWb ps ch)))
    (hyp_n_3bitr4d_2 : Nominal.NPrf (.imp ph (synWb th ps)))
    (hyp_n_3bitr4d_3 : Nominal.NPrf (.imp ph (synWb ta ch))) :
    Nominal.NPrf (.imp ph (synWb th ta)) :=
  by
  have p0000 := @gBitr4d ph ps ch ta hyp_n_3bitr4d_1 hyp_n_3bitr4d_3
  have p0001 := @gBitrd ph th ps ta hyp_n_3bitr4d_2 p0000
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_n_3bitr3g`. -/
@[expose]
noncomputable def gN3bitr3g (ph : Wff) (ps : Wff) (ch : Wff) (th : Wff) (ta : Wff)
    (hyp_n_3bitr3g_1 : Nominal.NPrf (.imp ph (synWb ps ch)))
    (hyp_n_3bitr3g_2 : Nominal.NPrf (synWb ps th))
    (hyp_n_3bitr3g_3 : Nominal.NPrf (synWb ch ta)) :
    Nominal.NPrf (.imp ph (synWb th ta)) :=
  by
  have p0000 := @gSyl5bbr th ps ph ch hyp_n_3bitr3g_2 hyp_n_3bitr3g_1
  have p0001 := @gSyl6bb ph th ch ta p0000 hyp_n_3bitr3g_3
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_n_3bitr4g`. -/
@[expose]
noncomputable def gN3bitr4g (ph : Wff) (ps : Wff) (ch : Wff) (th : Wff) (ta : Wff)
    (hyp_n_3bitr4g_1 : Nominal.NPrf (.imp ph (synWb ps ch)))
    (hyp_n_3bitr4g_2 : Nominal.NPrf (synWb th ps))
    (hyp_n_3bitr4g_3 : Nominal.NPrf (synWb ta ch)) :
    Nominal.NPrf (.imp ph (synWb th ta)) :=
  by
  have p0000 := @gSyl5bb th ps ph ch hyp_n_3bitr4g_2 hyp_n_3bitr4g_1
  have p0001 := @gSyl6bbr ph th ch ta p0000 hyp_n_3bitr4g_3
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_notnot`. -/
@[expose]
noncomputable def gNotnot (ph : Wff) : Nominal.NPrf (synWb ph (.neg (.neg ph))) :=
  by
  have p0000 := @gNotnot1 ph
  have p0001 := @gNotnot2 ph
  have p0002 := @gImpbii ph (.neg (.neg ph)) p0000 p0001
  exact p0002

/-- Checked nominal proof certificate identified upstream as `g_con34b`. -/
@[expose]
noncomputable def gCon34b (ph : Wff) (ps : Wff) :
    Nominal.NPrf (synWb (.imp ph ps) (.imp (.neg ps) (.neg ph))) :=
  by
  have p0000 := @gCon3 ph ps
  have p0001 := Nominal.ax3 ps ph
  have p0002 := @gImpbii (.imp ph ps) (.imp (.neg ps) (.neg ph)) p0000 p0001
  exact p0002

/-- Checked nominal proof certificate identified upstream as `g_con4bid`. -/
@[expose]
noncomputable def gCon4bid (ph : Wff) (ps : Wff) (ch : Wff)
    (hyp_con4bid_1 : Nominal.NPrf (.imp ph (synWb (.neg ps) (.neg ch)))) :
    Nominal.NPrf (.imp ph (synWb ps ch)) :=
  by
  have p0000 := @gBiimprd ph (.neg ps) (.neg ch) hyp_con4bid_1
  have p0001 := @gCon4d ph ch ps p0000
  have p0002 := @gBiimpd ph (.neg ps) (.neg ch) hyp_con4bid_1
  have p0003 := @gImpcon4bid ph ps ch p0001 p0002
  exact p0003

/-- Checked nominal proof certificate identified upstream as `g_notbid`. -/
@[expose]
noncomputable def gNotbid (ph : Wff) (ps : Wff) (ch : Wff)
    (hyp_notbid_1 : Nominal.NPrf (.imp ph (synWb ps ch))) :
    Nominal.NPrf (.imp ph (synWb (.neg ps) (.neg ch))) :=
  by
  have p0000 := @gNotnot ps
  have p0001 := @gNotnot ch
  have p0002 :=
    @gN3bitr3g ph ps ch (.neg (.neg ps)) (.neg (.neg ch)) hyp_notbid_1 p0000 p0001
  have p0003 := @gCon4bid ph (.neg ps) (.neg ch) p0002
  exact p0003

/-- Checked nominal proof certificate identified upstream as `g_notbi`. -/
@[expose]
noncomputable def gNotbi (ph : Wff) (ps : Wff) :
    Nominal.NPrf (synWb (synWb ph ps) (synWb (.neg ph) (.neg ps))) :=
  by
  have p0000 := @gId (synWb ph ps)
  have p0001 := @gNotbid (synWb ph ps) ph ps p0000
  have p0002 := @gId (synWb (.neg ph) (.neg ps))
  have p0003 := @gCon4bid (synWb (.neg ph) (.neg ps)) ph ps p0002
  have p0004 := @gImpbii (synWb ph ps) (synWb (.neg ph) (.neg ps)) p0001 p0003
  exact p0004

/-- Checked nominal proof certificate identified upstream as `g_notbii`. -/
@[expose]
noncomputable def gNotbii (ph : Wff) (ps : Wff)
    (hyp_notbii_1 : Nominal.NPrf (synWb ph ps)) :
    Nominal.NPrf (synWb (.neg ph) (.neg ps)) :=
  by
  have p0000 := @gNotbi ph ps
  have p0001 := @gMpbi (synWb ph ps) (synWb (.neg ph) (.neg ps)) hyp_notbii_1 p0000
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_con4bii`. -/
@[expose]
noncomputable def gCon4bii (ph : Wff) (ps : Wff)
    (hyp_con4bii_1 : Nominal.NPrf (synWb (.neg ph) (.neg ps))) :
    Nominal.NPrf (synWb ph ps) :=
  by
  have p0000 := @gNotbi ph ps
  have p0001 := @gMpbir (synWb ph ps) (synWb (.neg ph) (.neg ps)) hyp_con4bii_1 p0000
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_mtbi`. -/
@[expose]
noncomputable def gMtbi (ph : Wff) (ps : Wff) (hyp_mtbi_1 : Nominal.NPrf (.neg ph))
    (hyp_mtbi_2 : Nominal.NPrf (synWb ph ps)) : Nominal.NPrf (.neg ps) :=
  by
  have p0000 := @gBiimpri ph ps hyp_mtbi_2
  have p0001 := @gMto ps ph hyp_mtbi_1 p0000
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_mtbir`. -/
@[expose]
noncomputable def gMtbir (ph : Wff) (ps : Wff) (hyp_mtbir_1 : Nominal.NPrf (.neg ps))
    (hyp_mtbir_2 : Nominal.NPrf (synWb ph ps)) : Nominal.NPrf (.neg ph) :=
  by
  have p0000 := @gBicomi ph ps hyp_mtbir_2
  have p0001 := @gMtbi ps ph hyp_mtbir_1 p0000
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_mtbid`. -/
@[expose]
noncomputable def gMtbid (ph : Wff) (ps : Wff) (ch : Wff)
    (hyp_mtbid_min : Nominal.NPrf (.imp ph (.neg ps)))
    (hyp_mtbid_maj : Nominal.NPrf (.imp ph (synWb ps ch))) :
    Nominal.NPrf (.imp ph (.neg ch)) :=
  by
  have p0000 := @gBiimprd ph ps ch hyp_mtbid_maj
  have p0001 := @gMtod ph ch ps hyp_mtbid_min p0000
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_mtbird`. -/
@[expose]
noncomputable def gMtbird (ph : Wff) (ps : Wff) (ch : Wff)
    (hyp_mtbird_min : Nominal.NPrf (.imp ph (.neg ch)))
    (hyp_mtbird_maj : Nominal.NPrf (.imp ph (synWb ps ch))) :
    Nominal.NPrf (.imp ph (.neg ps)) :=
  by
  have p0000 := @gBiimpd ph ps ch hyp_mtbird_maj
  have p0001 := @gMtod ph ps ch hyp_mtbird_min p0000
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_mtbii`. -/
@[expose]
noncomputable def gMtbii (ph : Wff) (ps : Wff) (ch : Wff)
    (hyp_mtbii_min : Nominal.NPrf (.neg ps))
    (hyp_mtbii_maj : Nominal.NPrf (.imp ph (synWb ps ch))) :
    Nominal.NPrf (.imp ph (.neg ch)) :=
  by
  have p0000 := @gBiimprd ph ps ch hyp_mtbii_maj
  have p0001 := @gMtoi ph ch ps hyp_mtbii_min p0000
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_mtbiri`. -/
@[expose]
noncomputable def gMtbiri (ph : Wff) (ps : Wff) (ch : Wff)
    (hyp_mtbiri_min : Nominal.NPrf (.neg ch))
    (hyp_mtbiri_maj : Nominal.NPrf (.imp ph (synWb ps ch))) :
    Nominal.NPrf (.imp ph (.neg ps)) :=
  by
  have p0000 := @gBiimpd ph ps ch hyp_mtbiri_maj
  have p0001 := @gMtoi ph ps ch hyp_mtbiri_min p0000
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_sylnib`. -/
@[expose]
noncomputable def gSylnib (ph : Wff) (ps : Wff) (ch : Wff)
    (hyp_sylnib_1 : Nominal.NPrf (.imp ph (.neg ps)))
    (hyp_sylnib_2 : Nominal.NPrf (synWb ps ch)) : Nominal.NPrf (.imp ph (.neg ch)) :=
  by
  have p0000 := @gA1i (synWb ps ch) ph hyp_sylnib_2
  have p0001 := @gMtbid ph ps ch hyp_sylnib_1 p0000
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_sylnibr`. -/
@[expose]
noncomputable def gSylnibr (ph : Wff) (ps : Wff) (ch : Wff)
    (hyp_sylnibr_1 : Nominal.NPrf (.imp ph (.neg ps)))
    (hyp_sylnibr_2 : Nominal.NPrf (synWb ch ps)) : Nominal.NPrf (.imp ph (.neg ch)) :=
  by
  have p0000 := @gBicomi ch ps hyp_sylnibr_2
  have p0001 := @gSylnib ph ps ch hyp_sylnibr_1 p0000
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_sylnbi`. -/
@[expose]
noncomputable def gSylnbi (ph : Wff) (ps : Wff) (ch : Wff)
    (hyp_sylnbi_1 : Nominal.NPrf (synWb ph ps))
    (hyp_sylnbi_2 : Nominal.NPrf (.imp (.neg ps) ch)) :
    Nominal.NPrf (.imp (.neg ph) ch) :=
  by
  have p0000 := @gNotbii ph ps hyp_sylnbi_1
  have p0001 := @gSylbi (.neg ph) (.neg ps) ch p0000 hyp_sylnbi_2
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_sylnbir`. -/
@[expose]
noncomputable def gSylnbir (ph : Wff) (ps : Wff) (ch : Wff)
    (hyp_sylnbir_1 : Nominal.NPrf (synWb ps ph))
    (hyp_sylnbir_2 : Nominal.NPrf (.imp (.neg ps) ch)) :
    Nominal.NPrf (.imp (.neg ph) ch) :=
  by
  have p0000 := @gBicomi ps ph hyp_sylnbir_1
  have p0001 := @gSylnbi ph ps ch p0000 hyp_sylnbir_2
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_xchnxbi`. -/
@[expose]
noncomputable def gXchnxbi (ph : Wff) (ps : Wff) (ch : Wff)
    (hyp_xchnxbi_1 : Nominal.NPrf (synWb (.neg ph) ps))
    (hyp_xchnxbi_2 : Nominal.NPrf (synWb ph ch)) : Nominal.NPrf (synWb (.neg ch) ps) :=
  by
  have p0000 := @gNotbii ph ch hyp_xchnxbi_2
  have p0001 := @gBitr3i (.neg ch) (.neg ph) ps p0000 hyp_xchnxbi_1
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_xchbinx`. -/
@[expose]
noncomputable def gXchbinx (ph : Wff) (ps : Wff) (ch : Wff)
    (hyp_xchbinx_1 : Nominal.NPrf (synWb ph (.neg ps)))
    (hyp_xchbinx_2 : Nominal.NPrf (synWb ps ch)) : Nominal.NPrf (synWb ph (.neg ch)) :=
  by
  have p0000 := @gNotbii ps ch hyp_xchbinx_2
  have p0001 := @gBitri ph (.neg ps) (.neg ch) hyp_xchbinx_1 p0000
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_xchbinxr`. -/
@[expose]
noncomputable def gXchbinxr (ph : Wff) (ps : Wff) (ch : Wff)
    (hyp_xchbinxr_1 : Nominal.NPrf (synWb ph (.neg ps)))
    (hyp_xchbinxr_2 : Nominal.NPrf (synWb ch ps)) : Nominal.NPrf (synWb ph (.neg ch)) :=
  by
  have p0000 := @gBicomi ch ps hyp_xchbinxr_2
  have p0001 := @gXchbinx ph ps ch hyp_xchbinxr_1 p0000
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_imbi2i`. -/
@[expose]
noncomputable def gImbi2i (ph : Wff) (ps : Wff) (ch : Wff)
    (hyp_bi_a : Nominal.NPrf (synWb ph ps)) :
    Nominal.NPrf (synWb (.imp ch ph) (.imp ch ps)) :=
  by
  have p0000 := @gA1i (synWb ph ps) ch hyp_bi_a
  have p0001 := @gPm574i ch ph ps p0000
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_bibi2i`. -/
@[expose]
noncomputable def gBibi2i (ph : Wff) (ps : Wff) (ch : Wff)
    (hyp_bibi_a : Nominal.NPrf (synWb ph ps)) :
    Nominal.NPrf (synWb (synWb ch ph) (synWb ch ps)) :=
  by
  have p0000 := @gId (synWb ch ph)
  have p0001 := @gSyl6bb (synWb ch ph) ch ph ps p0000 hyp_bibi_a
  have p0002 := @gId (synWb ch ps)
  have p0003 := @gSyl6bbr (synWb ch ps) ch ps ph p0002 hyp_bibi_a
  have p0004 := @gImpbii (synWb ch ph) (synWb ch ps) p0001 p0003
  exact p0004

/-- Checked nominal proof certificate identified upstream as `g_bibi1i`. -/
@[expose]
noncomputable def gBibi1i (ph : Wff) (ps : Wff) (ch : Wff)
    (hyp_bibi_a : Nominal.NPrf (synWb ph ps)) :
    Nominal.NPrf (synWb (synWb ph ch) (synWb ps ch)) :=
  by
  have p0000 := @gBicom ph ch
  have p0001 := @gBibi2i ph ps ch hyp_bibi_a
  have p0002 := @gBicom ch ps
  have p0003 :=
    @gN3bitri (synWb ph ch) (synWb ch ph) (synWb ch ps) (synWb ps ch) p0000 p0001
      p0002
  exact p0003

/-- Checked nominal proof certificate identified upstream as `g_bibi12i`. -/
@[expose]
noncomputable def gBibi12i (ph : Wff) (ps : Wff) (ch : Wff) (th : Wff)
    (hyp_bibi_a : Nominal.NPrf (synWb ph ps))
    (hyp_bibi12_2 : Nominal.NPrf (synWb ch th)) :
    Nominal.NPrf (synWb (synWb ph ch) (synWb ps th)) :=
  by
  have p0000 := @gBibi2i ch th ph hyp_bibi12_2
  have p0001 := @gBibi1i ph ps th hyp_bibi_a
  have p0002 := @gBitri (synWb ph ch) (synWb ph th) (synWb ps th) p0000 p0001
  exact p0002

/-- Checked nominal proof certificate identified upstream as `g_imbi2d`. -/
@[expose]
noncomputable def gImbi2d (ph : Wff) (ps : Wff) (ch : Wff) (th : Wff)
    (hyp_imbid_1 : Nominal.NPrf (.imp ph (synWb ps ch))) :
    Nominal.NPrf (.imp ph (synWb (.imp th ps) (.imp th ch))) :=
  by
  have p0000 := @gA1d ph (synWb ps ch) th hyp_imbid_1
  have p0001 := @gPm574d ph th ps ch p0000
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_imbi1d`. -/
@[expose]
noncomputable def gImbi1d (ph : Wff) (ps : Wff) (ch : Wff) (th : Wff)
    (hyp_imbid_1 : Nominal.NPrf (.imp ph (synWb ps ch))) :
    Nominal.NPrf (.imp ph (synWb (.imp ps th) (.imp ch th))) :=
  by
  have p0000 := @gBiimprd ph ps ch hyp_imbid_1
  have p0001 := @gImim1d ph ch ps th p0000
  have p0002 := @gBiimpd ph ps ch hyp_imbid_1
  have p0003 := @gImim1d ph ps ch th p0002
  have p0004 := @gImpbid ph (.imp ps th) (.imp ch th) p0001 p0003
  exact p0004

/-- Checked nominal proof certificate identified upstream as `g_bibi2d`. -/
@[expose]
noncomputable def gBibi2d (ph : Wff) (ps : Wff) (ch : Wff) (th : Wff)
    (hyp_imbid_1 : Nominal.NPrf (.imp ph (synWb ps ch))) :
    Nominal.NPrf (.imp ph (synWb (synWb th ps) (synWb th ch))) :=
  by
  have p0000 := @gPm574i ph ps ch hyp_imbid_1
  have p0001 := @gBibi2i (.imp ph ps) (.imp ph ch) (.imp ph th) p0000
  have p0002 := @gPm574 ph th ps
  have p0003 := @gPm574 ph th ch
  have p0004 :=
    @gN3bitr4i (synWb (.imp ph th) (.imp ph ps)) (synWb (.imp ph th) (.imp ph ch))
      (.imp ph (synWb th ps)) (.imp ph (synWb th ch)) p0001 p0002 p0003
  have p0005 := @gPm574ri ph (synWb th ps) (synWb th ch) p0004
  exact p0005

/-- Checked nominal proof certificate identified upstream as `g_bibi1d`. -/
@[expose]
noncomputable def gBibi1d (ph : Wff) (ps : Wff) (ch : Wff) (th : Wff)
    (hyp_imbid_1 : Nominal.NPrf (.imp ph (synWb ps ch))) :
    Nominal.NPrf (.imp ph (synWb (synWb ps th) (synWb ch th))) :=
  by
  have p0000 := @gBibi2d ph ps ch th hyp_imbid_1
  have p0001 := @gBicom ps th
  have p0002 := @gBicom ch th
  have p0003 :=
    @gN3bitr4g ph (synWb th ps) (synWb th ch) (synWb ps th) (synWb ch th) p0000
      p0001 p0002
  exact p0003

/-- Checked nominal proof certificate identified upstream as `g_imbi12d`. -/
@[expose]
noncomputable def gImbi12d (ph : Wff) (ps : Wff) (ch : Wff) (th : Wff) (ta : Wff)
    (hyp_imbi12d_1 : Nominal.NPrf (.imp ph (synWb ps ch)))
    (hyp_imbi12d_2 : Nominal.NPrf (.imp ph (synWb th ta))) :
    Nominal.NPrf (.imp ph (synWb (.imp ps th) (.imp ch ta))) :=
  by
  have p0000 := @gImbi1d ph ps ch th hyp_imbi12d_1
  have p0001 := @gImbi2d ph th ta ch hyp_imbi12d_2
  have p0002 := @gBitrd ph (.imp ps th) (.imp ch th) (.imp ch ta) p0000 p0001
  exact p0002

/-- Checked nominal proof certificate identified upstream as `g_bibi12d`. -/
@[expose]
noncomputable def gBibi12d (ph : Wff) (ps : Wff) (ch : Wff) (th : Wff) (ta : Wff)
    (hyp_imbi12d_1 : Nominal.NPrf (.imp ph (synWb ps ch)))
    (hyp_imbi12d_2 : Nominal.NPrf (.imp ph (synWb th ta))) :
    Nominal.NPrf (.imp ph (synWb (synWb ps th) (synWb ch ta))) :=
  by
  have p0000 := @gBibi1d ph ps ch th hyp_imbi12d_1
  have p0001 := @gBibi2d ph th ta ch hyp_imbi12d_2
  have p0002 := @gBitrd ph (synWb ps th) (synWb ch th) (synWb ch ta) p0000 p0001
  exact p0002

/-- Checked nominal proof certificate identified upstream as `g_imbi1`. -/
@[expose]
noncomputable def gImbi1 (ph : Wff) (ps : Wff) (ch : Wff) :
    Nominal.NPrf (.imp (synWb ph ps) (synWb (.imp ph ch) (.imp ps ch))) :=
  by
  have p0000 := @gId (synWb ph ps)
  have p0001 := @gImbi1d (synWb ph ps) ph ps ch p0000
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_imbi1i`. -/
@[expose]
noncomputable def gImbi1i (ph : Wff) (ps : Wff) (ch : Wff)
    (hyp_imbi1i_1 : Nominal.NPrf (synWb ph ps)) :
    Nominal.NPrf (synWb (.imp ph ch) (.imp ps ch)) :=
  by
  have p0000 := @gImbi1 ph ps ch
  have p0001 := Nominal.mp hyp_imbi1i_1 p0000
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_imbi12i`. -/
@[expose]
noncomputable def gImbi12i (ph : Wff) (ps : Wff) (ch : Wff) (th : Wff)
    (hyp_imbi12i_1 : Nominal.NPrf (synWb ph ps))
    (hyp_imbi12i_2 : Nominal.NPrf (synWb ch th)) :
    Nominal.NPrf (synWb (.imp ph ch) (.imp ps th)) :=
  by
  have p0000 := @gImbi2i ch th ph hyp_imbi12i_2
  have p0001 := @gImbi1i ph ps th hyp_imbi12i_1
  have p0002 := @gBitri (.imp ph ch) (.imp ph th) (.imp ps th) p0000 p0001
  exact p0002

/-- Checked nominal proof certificate identified upstream as `g_bibi1`. -/
@[expose]
noncomputable def gBibi1 (ph : Wff) (ps : Wff) (ch : Wff) :
    Nominal.NPrf (.imp (synWb ph ps) (synWb (synWb ph ch) (synWb ps ch))) :=
  by
  have p0000 := @gId (synWb ph ps)
  have p0001 := @gBibi1d (synWb ph ps) ph ps ch p0000
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_con2bi`. -/
@[expose]
noncomputable def gCon2bi (ph : Wff) (ps : Wff) :
    Nominal.NPrf (synWb (synWb ph (.neg ps)) (synWb ps (.neg ph))) :=
  by
  have p0000 := @gNotbi ph (.neg ps)
  have p0001 := @gNotnot ps
  have p0002 := @gBibi2i ps (.neg (.neg ps)) (.neg ph) p0001
  have p0003 := @gBicom (.neg ph) ps
  have p0004 :=
    @gN3bitr2i (synWb ph (.neg ps)) (synWb (.neg ph) (.neg (.neg ps)))
      (synWb (.neg ph) ps) (synWb ps (.neg ph)) p0000 p0002 p0003
  exact p0004

/-- Checked nominal proof certificate identified upstream as `g_con2bid`. -/
@[expose]
noncomputable def gCon2bid (ph : Wff) (ps : Wff) (ch : Wff)
    (hyp_con2bid_1 : Nominal.NPrf (.imp ph (synWb ps (.neg ch)))) :
    Nominal.NPrf (.imp ph (synWb ch (.neg ps))) :=
  by
  have p0000 := @gCon2bi ch ps
  have p0001 :=
    @gSylibr ph (synWb ps (.neg ch)) (synWb ch (.neg ps)) hyp_con2bid_1 p0000
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_con1bid`. -/
@[expose]
noncomputable def gCon1bid (ph : Wff) (ps : Wff) (ch : Wff)
    (hyp_con1bid_1 : Nominal.NPrf (.imp ph (synWb (.neg ps) ch))) :
    Nominal.NPrf (.imp ph (synWb (.neg ch) ps)) :=
  by
  have p0000 := @gBicomd ph (.neg ps) ch hyp_con1bid_1
  have p0001 := @gCon2bid ph ch ps p0000
  have p0002 := @gBicomd ph ps (.neg ch) p0001
  exact p0002

/-- Checked nominal proof certificate identified upstream as `g_con1bii`. -/
@[expose]
noncomputable def gCon1bii (ph : Wff) (ps : Wff)
    (hyp_con1bii_1 : Nominal.NPrf (synWb (.neg ph) ps)) :
    Nominal.NPrf (synWb (.neg ps) ph) :=
  by
  have p0000 := @gNotnot ph
  have p0001 := @gXchbinx ph (.neg ph) ps p0000 hyp_con1bii_1
  have p0002 := @gBicomi ph (.neg ps) p0001
  exact p0002

/-- Checked nominal proof certificate identified upstream as `g_con2bii`. -/
@[expose]
noncomputable def gCon2bii (ph : Wff) (ps : Wff)
    (hyp_con2bii_1 : Nominal.NPrf (synWb ph (.neg ps))) :
    Nominal.NPrf (synWb ps (.neg ph)) :=
  by
  have p0000 := @gBicomi ph (.neg ps) hyp_con2bii_1
  have p0001 := @gCon1bii ps ph p0000
  have p0002 := @gBicomi (.neg ph) ps p0001
  exact p0002

/-- Checked nominal proof certificate identified upstream as `g_con2b`. -/
@[expose]
noncomputable def gCon2b (ph : Wff) (ps : Wff) :
    Nominal.NPrf (synWb (.imp ph (.neg ps)) (.imp ps (.neg ph))) :=
  by
  have p0000 := @gCon2 ph ps
  have p0001 := @gCon2 ps ph
  have p0002 := @gImpbii (.imp ph (.neg ps)) (.imp ps (.neg ph)) p0000 p0001
  exact p0002

/-- Checked nominal proof certificate identified upstream as `g_biimt`. -/
@[expose]
noncomputable def gBiimt (ph : Wff) (ps : Wff) :
    Nominal.NPrf (.imp ph (synWb ps (.imp ph ps))) :=
  by
  have p0000 := Nominal.ax1 ps ph
  have p0001 := @gPm227 ph ps
  have p0002 := @gImpbid2 ph ps (.imp ph ps) p0000 p0001
  exact p0002


end NFChoice.DirectNominalPrf.WPPReplay
