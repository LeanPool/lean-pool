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

@[expose]
noncomputable def g_a1ii (ph : Wff) (ps : Wff) (hyp_a1ii_1 : Nominal.NPrf ph)
    (_hyp_a1ii_2 : Nominal.NPrf ps) : Nominal.NPrf ph :=
  by
  let proofSupport : Finset Var := ph.fv ∪ ps.fv
  exact hyp_a1ii_1

@[expose]
noncomputable def g_mp2b (ph : Wff) (ps : Wff) (ch : Wff) (hyp_mp2b_1 : Nominal.NPrf ph)
    (hyp_mp2b_2 : Nominal.NPrf (.imp ph ps)) (hyp_mp2b_3 : Nominal.NPrf (.imp ps ch)) :
    Nominal.NPrf ch :=
  by
  have p0000 := Nominal.mp hyp_mp2b_1 hyp_mp2b_2
  have p0001 := Nominal.mp p0000 hyp_mp2b_3
  exact p0001

@[expose]
noncomputable def g_a1i (ph : Wff) (ps : Wff) (hyp_a1i_1 : Nominal.NPrf ph) :
    Nominal.NPrf (.imp ps ph) :=
  by
  have p0000 := Nominal.ax1 ph ps
  have p0001 := Nominal.mp hyp_a1i_1 p0000
  exact p0001

@[expose]
noncomputable def g_a2i (ph : Wff) (ps : Wff) (ch : Wff)
    (hyp_a2i_1 : Nominal.NPrf (.imp ph (.imp ps ch))) :
    Nominal.NPrf (.imp (.imp ph ps) (.imp ph ch)) :=
  by
  have p0000 := Nominal.ax2 ph ps ch
  have p0001 := Nominal.mp hyp_a2i_1 p0000
  exact p0001

@[expose]
noncomputable def g_imim2i (ph : Wff) (ps : Wff) (ch : Wff)
    (hyp_imim2i_1 : Nominal.NPrf (.imp ph ps)) :
    Nominal.NPrf (.imp (.imp ch ph) (.imp ch ps)) :=
  by
  have p0000 := @g_a1i (.imp ph ps) ch hyp_imim2i_1
  have p0001 := @g_a2i ch ph ps p0000
  exact p0001

@[expose]
noncomputable def g_mpd (ph : Wff) (ps : Wff) (ch : Wff)
    (hyp_mpd_1 : Nominal.NPrf (.imp ph ps))
    (hyp_mpd_2 : Nominal.NPrf (.imp ph (.imp ps ch))) : Nominal.NPrf (.imp ph ch) :=
  by
  have p0000 := @g_a2i ph ps ch hyp_mpd_2
  have p0001 := Nominal.mp hyp_mpd_1 p0000
  exact p0001

@[expose]
noncomputable def g_syl (ph : Wff) (ps : Wff) (ch : Wff)
    (hyp_syl_1 : Nominal.NPrf (.imp ph ps)) (hyp_syl_2 : Nominal.NPrf (.imp ps ch)) :
    Nominal.NPrf (.imp ph ch) :=
  by
  have p0000 := @g_a1i (.imp ps ch) ph hyp_syl_2
  have p0001 := @g_mpd ph ps ch hyp_syl_1 p0000
  exact p0001

@[expose]
noncomputable def g_mpi (ph : Wff) (ps : Wff) (ch : Wff) (hyp_mpi_1 : Nominal.NPrf ps)
    (hyp_mpi_2 : Nominal.NPrf (.imp ph (.imp ps ch))) : Nominal.NPrf (.imp ph ch) :=
  by
  have p0000 := @g_a1i ps ph hyp_mpi_1
  have p0001 := @g_mpd ph ps ch p0000 hyp_mpi_2
  exact p0001

@[expose]
noncomputable def g_mp2 (ph : Wff) (ps : Wff) (ch : Wff) (hyp_mp2_1 : Nominal.NPrf ph)
    (hyp_mp2_2 : Nominal.NPrf ps) (hyp_mp2_3 : Nominal.NPrf (.imp ph (.imp ps ch))) :
    Nominal.NPrf ch :=
  by
  have p0000 := @g_mpi ph ps ch hyp_mp2_2 hyp_mp2_3
  have p0001 := Nominal.mp hyp_mp2_1 p0000
  exact p0001

@[expose]
noncomputable def g_n_3syl (ph : Wff) (ps : Wff) (ch : Wff) (th : Wff)
    (hyp_n_3syl_1 : Nominal.NPrf (.imp ph ps)) (hyp_n_3syl_2 : Nominal.NPrf (.imp ps ch))
    (hyp_n_3syl_3 : Nominal.NPrf (.imp ch th)) : Nominal.NPrf (.imp ph th) :=
  by
  have p0000 := @g_syl ph ps ch hyp_n_3syl_1 hyp_n_3syl_2
  have p0001 := @g_syl ph ch th p0000 hyp_n_3syl_3
  exact p0001

@[expose]
noncomputable def g_id (ph : Wff) : Nominal.NPrf (.imp ph ph) :=
  by
  have p0000 := Nominal.ax1 ph ph
  have p0001 := Nominal.ax1 ph (.imp ph ph)
  have p0002 := @g_mpd ph (.imp ph ph) ph p0000 p0001
  exact p0002

@[expose]
noncomputable def g_idd (ph : Wff) (ps : Wff) : Nominal.NPrf (.imp ph (.imp ps ps)) :=
  by
  have p0000 := @g_id ps
  have p0001 := @g_a1i (.imp ps ps) ph p0000
  exact p0001

@[expose]
noncomputable def g_a1d (ph : Wff) (ps : Wff) (ch : Wff)
    (hyp_a1d_1 : Nominal.NPrf (.imp ph ps)) : Nominal.NPrf (.imp ph (.imp ch ps)) :=
  by
  have p0000 := Nominal.ax1 ps ch
  have p0001 := @g_syl ph ps (.imp ch ps) hyp_a1d_1 p0000
  exact p0001

@[expose]
noncomputable def g_a2d (ph : Wff) (ps : Wff) (ch : Wff) (th : Wff)
    (hyp_a2d_1 : Nominal.NPrf (.imp ph (.imp ps (.imp ch th)))) :
    Nominal.NPrf (.imp ph (.imp (.imp ps ch) (.imp ps th))) :=
  by
  have p0000 := Nominal.ax2 ps ch th
  have p0001 :=
    @g_syl ph (.imp ps (.imp ch th)) (.imp (.imp ps ch) (.imp ps th)) hyp_a2d_1 p0000
  exact p0001

@[expose]
noncomputable def g_n_2a1i (ph : Wff) (ps : Wff) (ch : Wff)
    (hyp_n_2a1i_1 : Nominal.NPrf ch) : Nominal.NPrf (.imp ph (.imp ps ch)) :=
  by
  have p0000 := @g_a1i ch ph hyp_n_2a1i_1
  have p0001 := @g_a1d ph ch ps p0000
  exact p0001

@[expose]
noncomputable def g_sylcom (ph : Wff) (ps : Wff) (ch : Wff) (th : Wff)
    (hyp_sylcom_1 : Nominal.NPrf (.imp ph (.imp ps ch)))
    (hyp_sylcom_2 : Nominal.NPrf (.imp ps (.imp ch th))) :
    Nominal.NPrf (.imp ph (.imp ps th)) :=
  by
  have p0000 := @g_a2i ps ch th hyp_sylcom_2
  have p0001 := @g_syl ph (.imp ps ch) (.imp ps th) hyp_sylcom_1 p0000
  exact p0001

@[expose]
noncomputable def g_syl5com (ph : Wff) (ps : Wff) (ch : Wff) (th : Wff)
    (hyp_syl5com_1 : Nominal.NPrf (.imp ph ps))
    (hyp_syl5com_2 : Nominal.NPrf (.imp ch (.imp ps th))) :
    Nominal.NPrf (.imp ph (.imp ch th)) :=
  by
  have p0000 := @g_a1d ph ps ch hyp_syl5com_1
  have p0001 := @g_sylcom ph ch ps th p0000 hyp_syl5com_2
  exact p0001

@[expose]
noncomputable def g_com12 (ph : Wff) (ps : Wff) (ch : Wff)
    (hyp_com12_1 : Nominal.NPrf (.imp ph (.imp ps ch))) :
    Nominal.NPrf (.imp ps (.imp ph ch)) :=
  by
  have p0000 := @g_id ps
  have p0001 := @g_syl5com ps ps ph ch p0000 hyp_com12_1
  exact p0001

@[expose]
noncomputable def g_syl5 (ph : Wff) (ps : Wff) (ch : Wff) (th : Wff)
    (hyp_syl5_1 : Nominal.NPrf (.imp ph ps))
    (hyp_syl5_2 : Nominal.NPrf (.imp ch (.imp ps th))) :
    Nominal.NPrf (.imp ch (.imp ph th)) :=
  by
  have p0000 := @g_syl5com ph ps ch th hyp_syl5_1 hyp_syl5_2
  have p0001 := @g_com12 ph ch th p0000
  exact p0001

@[expose]
noncomputable def g_syl6 (ph : Wff) (ps : Wff) (ch : Wff) (th : Wff)
    (hyp_syl6_1 : Nominal.NPrf (.imp ph (.imp ps ch)))
    (hyp_syl6_2 : Nominal.NPrf (.imp ch th)) : Nominal.NPrf (.imp ph (.imp ps th)) :=
  by
  have p0000 := @g_a1i (.imp ch th) ps hyp_syl6_2
  have p0001 := @g_sylcom ph ps ch th hyp_syl6_1 p0000
  exact p0001

@[expose]
noncomputable def g_syl56 (ph : Wff) (ps : Wff) (ch : Wff) (th : Wff) (ta : Wff)
    (hyp_syl56_1 : Nominal.NPrf (.imp ph ps))
    (hyp_syl56_2 : Nominal.NPrf (.imp ch (.imp ps th)))
    (hyp_syl56_3 : Nominal.NPrf (.imp th ta)) : Nominal.NPrf (.imp ch (.imp ph ta)) :=
  by
  have p0000 := @g_syl6 ch ps th ta hyp_syl56_2 hyp_syl56_3
  have p0001 := @g_syl5 ph ps ch ta hyp_syl56_1 p0000
  exact p0001

@[expose]
noncomputable def g_syl6com (ph : Wff) (ps : Wff) (ch : Wff) (th : Wff)
    (hyp_syl6com_1 : Nominal.NPrf (.imp ph (.imp ps ch)))
    (hyp_syl6com_2 : Nominal.NPrf (.imp ch th)) : Nominal.NPrf (.imp ps (.imp ph th)) :=
  by
  have p0000 := @g_syl6 ph ps ch th hyp_syl6com_1 hyp_syl6com_2
  have p0001 := @g_com12 ph ps th p0000
  exact p0001

@[expose]
noncomputable def g_mpcom (ph : Wff) (ps : Wff) (ch : Wff)
    (hyp_mpcom_1 : Nominal.NPrf (.imp ps ph))
    (hyp_mpcom_2 : Nominal.NPrf (.imp ph (.imp ps ch))) : Nominal.NPrf (.imp ps ch) :=
  by
  have p0000 := @g_com12 ph ps ch hyp_mpcom_2
  have p0001 := @g_mpd ps ph ch hyp_mpcom_1 p0000
  exact p0001

@[expose]
noncomputable def g_syli (ph : Wff) (ps : Wff) (ch : Wff) (th : Wff)
    (hyp_syli_1 : Nominal.NPrf (.imp ps (.imp ph ch)))
    (hyp_syli_2 : Nominal.NPrf (.imp ch (.imp ph th))) :
    Nominal.NPrf (.imp ps (.imp ph th)) :=
  by
  have p0000 := @g_com12 ch ph th hyp_syli_2
  have p0001 := @g_sylcom ps ph ch th hyp_syli_1 p0000
  exact p0001

@[expose]
noncomputable def g_syl2im (ph : Wff) (ps : Wff) (ch : Wff) (th : Wff) (ta : Wff)
    (hyp_syl2im_1 : Nominal.NPrf (.imp ph ps)) (hyp_syl2im_2 : Nominal.NPrf (.imp ch th))
    (hyp_syl2im_3 : Nominal.NPrf (.imp ps (.imp th ta))) :
    Nominal.NPrf (.imp ph (.imp ch ta)) :=
  by
  have p0000 := @g_syl5 ch th ps ta hyp_syl2im_2 hyp_syl2im_3
  have p0001 := @g_syl ph ps (.imp ch ta) hyp_syl2im_1 p0000
  exact p0001

@[expose]
noncomputable def g_pm2_27 (ph : Wff) (ps : Wff) :
    Nominal.NPrf (.imp ph (.imp (.imp ph ps) ps)) :=
  by
  have p0000 := @g_id (.imp ph ps)
  have p0001 := @g_com12 (.imp ph ps) ph ps p0000
  exact p0001

@[expose]
noncomputable def g_mpdd (ph : Wff) (ps : Wff) (ch : Wff) (th : Wff)
    (hyp_mpdd_1 : Nominal.NPrf (.imp ph (.imp ps ch)))
    (hyp_mpdd_2 : Nominal.NPrf (.imp ph (.imp ps (.imp ch th)))) :
    Nominal.NPrf (.imp ph (.imp ps th)) :=
  by
  have p0000 := @g_a2d ph ps ch th hyp_mpdd_2
  have p0001 := @g_mpd ph (.imp ps ch) (.imp ps th) hyp_mpdd_1 p0000
  exact p0001

@[expose]
noncomputable def g_mpid (ph : Wff) (ps : Wff) (ch : Wff) (th : Wff)
    (hyp_mpid_1 : Nominal.NPrf (.imp ph ch))
    (hyp_mpid_2 : Nominal.NPrf (.imp ph (.imp ps (.imp ch th)))) :
    Nominal.NPrf (.imp ph (.imp ps th)) :=
  by
  have p0000 := @g_a1d ph ch ps hyp_mpid_1
  have p0001 := @g_mpdd ph ps ch th p0000 hyp_mpid_2
  exact p0001

@[expose]
noncomputable def g_mpdi (ph : Wff) (ps : Wff) (ch : Wff) (th : Wff)
    (hyp_mpdi_1 : Nominal.NPrf (.imp ps ch))
    (hyp_mpdi_2 : Nominal.NPrf (.imp ph (.imp ps (.imp ch th)))) :
    Nominal.NPrf (.imp ph (.imp ps th)) :=
  by
  have p0000 := @g_a1i (.imp ps ch) ph hyp_mpdi_1
  have p0001 := @g_mpdd ph ps ch th p0000 hyp_mpdi_2
  exact p0001

@[expose]
noncomputable def g_mpii (ph : Wff) (ps : Wff) (ch : Wff) (th : Wff)
    (hyp_mpii_1 : Nominal.NPrf ch)
    (hyp_mpii_2 : Nominal.NPrf (.imp ph (.imp ps (.imp ch th)))) :
    Nominal.NPrf (.imp ph (.imp ps th)) :=
  by
  have p0000 := @g_a1i ch ps hyp_mpii_1
  have p0001 := @g_mpdi ph ps ch th p0000 hyp_mpii_2
  exact p0001

@[expose]
noncomputable def g_syld (ph : Wff) (ps : Wff) (ch : Wff) (th : Wff)
    (hyp_syld_1 : Nominal.NPrf (.imp ph (.imp ps ch)))
    (hyp_syld_2 : Nominal.NPrf (.imp ph (.imp ch th))) :
    Nominal.NPrf (.imp ph (.imp ps th)) :=
  by
  have p0000 := @g_a1d ph (.imp ch th) ps hyp_syld_2
  have p0001 := @g_mpdd ph ps ch th hyp_syld_1 p0000
  exact p0001

@[expose]
noncomputable def g_a1dd (ph : Wff) (ps : Wff) (ch : Wff) (th : Wff)
    (hyp_a1dd_1 : Nominal.NPrf (.imp ph (.imp ps ch))) :
    Nominal.NPrf (.imp ph (.imp ps (.imp th ch))) :=
  by
  have p0000 := Nominal.ax1 ch th
  have p0001 := @g_syl6 ph ps ch (.imp th ch) hyp_a1dd_1 p0000
  exact p0001

@[expose]
noncomputable def g_pm2_43i (ph : Wff) (ps : Wff)
    (hyp_pm2_43i_1 : Nominal.NPrf (.imp ph (.imp ph ps))) : Nominal.NPrf (.imp ph ps) :=
  by
  have p0000 := @g_id ph
  have p0001 := @g_mpd ph ph ps p0000 hyp_pm2_43i_1
  exact p0001

@[expose]
noncomputable def g_pm2_43d (ph : Wff) (ps : Wff) (ch : Wff)
    (hyp_pm2_43d_1 : Nominal.NPrf (.imp ph (.imp ps (.imp ps ch)))) :
    Nominal.NPrf (.imp ph (.imp ps ch)) :=
  by
  have p0000 := @g_id ps
  have p0001 := @g_mpdi ph ps ps ch p0000 hyp_pm2_43d_1
  exact p0001

@[expose]
noncomputable def g_pm2_43a (ph : Wff) (ps : Wff) (ch : Wff)
    (hyp_pm2_43a_1 : Nominal.NPrf (.imp ps (.imp ph (.imp ps ch)))) :
    Nominal.NPrf (.imp ps (.imp ph ch)) :=
  by
  have p0000 := @g_id ps
  have p0001 := @g_mpid ps ph ps ch p0000 hyp_pm2_43a_1
  exact p0001

@[expose]
noncomputable def g_pm2_43b (ph : Wff) (ps : Wff) (ch : Wff)
    (hyp_pm2_43b_1 : Nominal.NPrf (.imp ps (.imp ph (.imp ps ch)))) :
    Nominal.NPrf (.imp ph (.imp ps ch)) :=
  by
  have p0000 := @g_pm2_43a ph ps ch hyp_pm2_43b_1
  have p0001 := @g_com12 ps ph ch p0000
  exact p0001

@[expose]
noncomputable def g_imim2d (ph : Wff) (ps : Wff) (ch : Wff) (th : Wff)
    (hyp_imim2d_1 : Nominal.NPrf (.imp ph (.imp ps ch))) :
    Nominal.NPrf (.imp ph (.imp (.imp th ps) (.imp th ch))) :=
  by
  have p0000 := @g_a1d ph (.imp ps ch) th hyp_imim2d_1
  have p0001 := @g_a2d ph th ps ch p0000
  exact p0001

@[expose]
noncomputable def g_imim2 (ph : Wff) (ps : Wff) (ch : Wff) :
    Nominal.NPrf (.imp (.imp ph ps) (.imp (.imp ch ph) (.imp ch ps))) :=
  by
  have p0000 := @g_id (.imp ph ps)
  have p0001 := @g_imim2d (.imp ph ps) ph ps ch p0000
  exact p0001

@[expose]
noncomputable def g_embantd (ph : Wff) (ps : Wff) (ch : Wff) (th : Wff)
    (hyp_embantd_1 : Nominal.NPrf (.imp ph ps))
    (hyp_embantd_2 : Nominal.NPrf (.imp ph (.imp ch th))) :
    Nominal.NPrf (.imp ph (.imp (.imp ps ch) th)) :=
  by
  have p0000 := @g_imim2d ph ch th ps hyp_embantd_2
  have p0001 := @g_mpid ph (.imp ps ch) ps th hyp_embantd_1 p0000
  exact p0001

@[expose]
noncomputable def g_sylsyld (ph : Wff) (ps : Wff) (ch : Wff) (th : Wff) (ta : Wff)
    (hyp_sylsyld_1 : Nominal.NPrf (.imp ph ps))
    (hyp_sylsyld_2 : Nominal.NPrf (.imp ph (.imp ch th)))
    (hyp_sylsyld_3 : Nominal.NPrf (.imp ps (.imp th ta))) :
    Nominal.NPrf (.imp ph (.imp ch ta)) :=
  by
  have p0000 := @g_syl ph ps (.imp th ta) hyp_sylsyld_1 hyp_sylsyld_3
  have p0001 := @g_syld ph ch th ta hyp_sylsyld_2 p0000
  exact p0001

@[expose]
noncomputable def g_imim12i (ph : Wff) (ps : Wff) (ch : Wff) (th : Wff)
    (hyp_imim12i_1 : Nominal.NPrf (.imp ph ps))
    (hyp_imim12i_2 : Nominal.NPrf (.imp ch th)) :
    Nominal.NPrf (.imp (.imp ps ch) (.imp ph th)) :=
  by
  have p0000 := @g_imim2i ch th ps hyp_imim12i_2
  have p0001 := @g_syl5 ph ps (.imp ps ch) th hyp_imim12i_1 p0000
  exact p0001

@[expose]
noncomputable def g_imim1i (ph : Wff) (ps : Wff) (ch : Wff)
    (hyp_imim1i_1 : Nominal.NPrf (.imp ph ps)) :
    Nominal.NPrf (.imp (.imp ps ch) (.imp ph ch)) :=
  by
  have p0000 := @g_id ch
  have p0001 := @g_imim12i ph ps ch ch hyp_imim1i_1 p0000
  exact p0001

@[expose]
noncomputable def g_imim3i (ph : Wff) (ps : Wff) (ch : Wff) (th : Wff)
    (hyp_imim3i_1 : Nominal.NPrf (.imp ph (.imp ps ch))) :
    Nominal.NPrf (.imp (.imp th ph) (.imp (.imp th ps) (.imp th ch))) :=
  by
  have p0000 := @g_imim2i ph (.imp ps ch) th hyp_imim3i_1
  have p0001 := @g_a2d (.imp th ph) th ps ch p0000
  exact p0001

@[expose]
noncomputable def g_sylc (ph : Wff) (ps : Wff) (ch : Wff) (th : Wff)
    (hyp_sylc_1 : Nominal.NPrf (.imp ph ps)) (hyp_sylc_2 : Nominal.NPrf (.imp ph ch))
    (hyp_sylc_3 : Nominal.NPrf (.imp ps (.imp ch th))) : Nominal.NPrf (.imp ph th) :=
  by
  have p0000 := @g_syl2im ph ps ph ch th hyp_sylc_1 hyp_sylc_2 hyp_sylc_3
  have p0001 := @g_pm2_43i ph th p0000
  exact p0001

@[expose]
noncomputable def g_syl3c (ph : Wff) (ps : Wff) (ch : Wff) (th : Wff) (ta : Wff)
    (hyp_syl3c_1 : Nominal.NPrf (.imp ph ps)) (hyp_syl3c_2 : Nominal.NPrf (.imp ph ch))
    (hyp_syl3c_3 : Nominal.NPrf (.imp ph th))
    (hyp_syl3c_4 : Nominal.NPrf (.imp ps (.imp ch (.imp th ta)))) :
    Nominal.NPrf (.imp ph ta) :=
  by
  have p0000 := @g_sylc ph ps ch (.imp th ta) hyp_syl3c_1 hyp_syl3c_2 hyp_syl3c_4
  have p0001 := @g_mpd ph th ta hyp_syl3c_3 p0000
  exact p0001

@[expose]
noncomputable def g_mpsyl (ph : Wff) (ps : Wff) (ch : Wff) (th : Wff)
    (hyp_mpsyl_1 : Nominal.NPrf ph) (hyp_mpsyl_2 : Nominal.NPrf (.imp ps ch))
    (hyp_mpsyl_3 : Nominal.NPrf (.imp ph (.imp ch th))) : Nominal.NPrf (.imp ps th) :=
  by
  have p0000 := @g_a1i ph ps hyp_mpsyl_1
  have p0001 := @g_sylc ps ph ch th p0000 hyp_mpsyl_2 hyp_mpsyl_3
  exact p0001

@[expose]
noncomputable def g_syl6c (ph : Wff) (ps : Wff) (ch : Wff) (th : Wff) (ta : Wff)
    (hyp_syl6c_1 : Nominal.NPrf (.imp ph (.imp ps ch)))
    (hyp_syl6c_2 : Nominal.NPrf (.imp ph (.imp ps th)))
    (hyp_syl6c_3 : Nominal.NPrf (.imp ch (.imp th ta))) :
    Nominal.NPrf (.imp ph (.imp ps ta)) :=
  by
  have p0000 := @g_syl6 ph ps ch (.imp th ta) hyp_syl6c_1 hyp_syl6c_3
  have p0001 := @g_mpdd ph ps th ta hyp_syl6c_2 p0000
  exact p0001

@[expose]
noncomputable def g_syldd (ph : Wff) (ps : Wff) (ch : Wff) (th : Wff) (ta : Wff)
    (hyp_syldd_1 : Nominal.NPrf (.imp ph (.imp ps (.imp ch th))))
    (hyp_syldd_2 : Nominal.NPrf (.imp ph (.imp ps (.imp th ta)))) :
    Nominal.NPrf (.imp ph (.imp ps (.imp ch ta))) :=
  by
  have p0000 := @g_imim2 th ta ch
  have p0001 :=
    @g_syl6c ph ps (.imp th ta) (.imp ch th) (.imp ch ta) hyp_syldd_2 hyp_syldd_1 p0000
  exact p0001

@[expose]
noncomputable def g_syl5d (ph : Wff) (ps : Wff) (ch : Wff) (th : Wff) (ta : Wff)
    (hyp_syl5d_1 : Nominal.NPrf (.imp ph (.imp ps ch)))
    (hyp_syl5d_2 : Nominal.NPrf (.imp ph (.imp th (.imp ch ta)))) :
    Nominal.NPrf (.imp ph (.imp th (.imp ps ta))) :=
  by
  have p0000 := @g_a1d ph (.imp ps ch) th hyp_syl5d_1
  have p0001 := @g_syldd ph th ps ch ta p0000 hyp_syl5d_2
  exact p0001

@[expose]
noncomputable def g_syl7 (ph : Wff) (ps : Wff) (ch : Wff) (th : Wff) (ta : Wff)
    (hyp_syl7_1 : Nominal.NPrf (.imp ph ps))
    (hyp_syl7_2 : Nominal.NPrf (.imp ch (.imp th (.imp ps ta)))) :
    Nominal.NPrf (.imp ch (.imp th (.imp ph ta))) :=
  by
  have p0000 := @g_a1i (.imp ph ps) ch hyp_syl7_1
  have p0001 := @g_syl5d ch ph ps th ta p0000 hyp_syl7_2
  exact p0001

@[expose]
noncomputable def g_syl6d (ph : Wff) (ps : Wff) (ch : Wff) (th : Wff) (ta : Wff)
    (hyp_syl6d_1 : Nominal.NPrf (.imp ph (.imp ps (.imp ch th))))
    (hyp_syl6d_2 : Nominal.NPrf (.imp ph (.imp th ta))) :
    Nominal.NPrf (.imp ph (.imp ps (.imp ch ta))) :=
  by
  have p0000 := @g_a1d ph (.imp th ta) ps hyp_syl6d_2
  have p0001 := @g_syldd ph ps ch th ta hyp_syl6d_1 p0000
  exact p0001

@[expose]
noncomputable def g_syl8 (ph : Wff) (ps : Wff) (ch : Wff) (th : Wff) (ta : Wff)
    (hyp_syl8_1 : Nominal.NPrf (.imp ph (.imp ps (.imp ch th))))
    (hyp_syl8_2 : Nominal.NPrf (.imp th ta)) :
    Nominal.NPrf (.imp ph (.imp ps (.imp ch ta))) :=
  by
  have p0000 := @g_a1i (.imp th ta) ph hyp_syl8_2
  have p0001 := @g_syl6d ph ps ch th ta hyp_syl8_1 p0000
  exact p0001

@[expose]
noncomputable def g_syl9 (ph : Wff) (ps : Wff) (ch : Wff) (th : Wff) (ta : Wff)
    (hyp_syl9_1 : Nominal.NPrf (.imp ph (.imp ps ch)))
    (hyp_syl9_2 : Nominal.NPrf (.imp th (.imp ch ta))) :
    Nominal.NPrf (.imp ph (.imp th (.imp ps ta))) :=
  by
  have p0000 := @g_a1i (.imp th (.imp ch ta)) ph hyp_syl9_2
  have p0001 := @g_syl5d ph ps ch th ta hyp_syl9_1 p0000
  exact p0001

@[expose]
noncomputable def g_syl9r (ph : Wff) (ps : Wff) (ch : Wff) (th : Wff) (ta : Wff)
    (hyp_syl9r_1 : Nominal.NPrf (.imp ph (.imp ps ch)))
    (hyp_syl9r_2 : Nominal.NPrf (.imp th (.imp ch ta))) :
    Nominal.NPrf (.imp th (.imp ph (.imp ps ta))) :=
  by
  have p0000 := @g_syl9 ph ps ch th ta hyp_syl9r_1 hyp_syl9r_2
  have p0001 := @g_com12 ph th (.imp ps ta) p0000
  exact p0001

@[expose]
noncomputable def g_imim12d (ph : Wff) (ps : Wff) (ch : Wff) (th : Wff) (ta : Wff)
    (hyp_imim12d_1 : Nominal.NPrf (.imp ph (.imp ps ch)))
    (hyp_imim12d_2 : Nominal.NPrf (.imp ph (.imp th ta))) :
    Nominal.NPrf (.imp ph (.imp (.imp ch th) (.imp ps ta))) :=
  by
  have p0000 := @g_imim2d ph th ta ch hyp_imim12d_2
  have p0001 := @g_syl5d ph ps ch (.imp ch th) ta hyp_imim12d_1 p0000
  exact p0001

@[expose]
noncomputable def g_imim1d (ph : Wff) (ps : Wff) (ch : Wff) (th : Wff)
    (hyp_imim1d_1 : Nominal.NPrf (.imp ph (.imp ps ch))) :
    Nominal.NPrf (.imp ph (.imp (.imp ch th) (.imp ps th))) :=
  by
  have p0000 := @g_idd ph th
  have p0001 := @g_imim12d ph ps ch th th hyp_imim1d_1 p0000
  exact p0001

@[expose]
noncomputable def g_imim1 (ph : Wff) (ps : Wff) (ch : Wff) :
    Nominal.NPrf (.imp (.imp ph ps) (.imp (.imp ps ch) (.imp ph ch))) :=
  by
  have p0000 := @g_id (.imp ph ps)
  have p0001 := @g_imim1d (.imp ph ps) ph ps ch p0000
  exact p0001

@[expose]
noncomputable def g_com23 (ph : Wff) (ps : Wff) (ch : Wff) (th : Wff)
    (hyp_com3_1 : Nominal.NPrf (.imp ph (.imp ps (.imp ch th)))) :
    Nominal.NPrf (.imp ph (.imp ch (.imp ps th))) :=
  by
  have p0000 := @g_pm2_27 ch th
  have p0001 := @g_syl9 ph ps (.imp ch th) ch th hyp_com3_1 p0000
  exact p0001

@[expose]
noncomputable def g_com3r (ph : Wff) (ps : Wff) (ch : Wff) (th : Wff)
    (hyp_com3_1 : Nominal.NPrf (.imp ph (.imp ps (.imp ch th)))) :
    Nominal.NPrf (.imp ch (.imp ph (.imp ps th))) :=
  by
  have p0000 := @g_com23 ph ps ch th hyp_com3_1
  have p0001 := @g_com12 ph ch (.imp ps th) p0000
  exact p0001

@[expose]
noncomputable def g_com3l (ph : Wff) (ps : Wff) (ch : Wff) (th : Wff)
    (hyp_com3_1 : Nominal.NPrf (.imp ph (.imp ps (.imp ch th)))) :
    Nominal.NPrf (.imp ps (.imp ch (.imp ph th))) :=
  by
  have p0000 := @g_com3r ph ps ch th hyp_com3_1
  have p0001 := @g_com3r ch ph ps th p0000
  exact p0001

@[expose]
noncomputable def g_pm2_04 (ph : Wff) (ps : Wff) (ch : Wff) :
    Nominal.NPrf (.imp (.imp ph (.imp ps ch)) (.imp ps (.imp ph ch))) :=
  by
  have p0000 := @g_id (.imp ph (.imp ps ch))
  have p0001 := @g_com23 (.imp ph (.imp ps ch)) ph ps ch p0000
  exact p0001

@[expose]
noncomputable def g_com34 (ph : Wff) (ps : Wff) (ch : Wff) (th : Wff) (ta : Wff)
    (hyp_com4_1 : Nominal.NPrf (.imp ph (.imp ps (.imp ch (.imp th ta))))) :
    Nominal.NPrf (.imp ph (.imp ps (.imp th (.imp ch ta)))) :=
  by
  have p0000 := @g_pm2_04 ch th ta
  have p0001 :=
    @g_syl6 ph ps (.imp ch (.imp th ta)) (.imp th (.imp ch ta)) hyp_com4_1 p0000
  exact p0001

@[expose]
noncomputable def g_com4l (ph : Wff) (ps : Wff) (ch : Wff) (th : Wff) (ta : Wff)
    (hyp_com4_1 : Nominal.NPrf (.imp ph (.imp ps (.imp ch (.imp th ta))))) :
    Nominal.NPrf (.imp ps (.imp ch (.imp th (.imp ph ta)))) :=
  by
  have p0000 := @g_com3l ph ps ch (.imp th ta) hyp_com4_1
  have p0001 := @g_com34 ps ch ph th ta p0000
  exact p0001

@[expose]
noncomputable def g_com4t (ph : Wff) (ps : Wff) (ch : Wff) (th : Wff) (ta : Wff)
    (hyp_com4_1 : Nominal.NPrf (.imp ph (.imp ps (.imp ch (.imp th ta))))) :
    Nominal.NPrf (.imp ch (.imp th (.imp ph (.imp ps ta)))) :=
  by
  have p0000 := @g_com4l ph ps ch th ta hyp_com4_1
  have p0001 := @g_com4l ps ch th ph ta p0000
  exact p0001

@[expose]
noncomputable def g_com4r (ph : Wff) (ps : Wff) (ch : Wff) (th : Wff) (ta : Wff)
    (hyp_com4_1 : Nominal.NPrf (.imp ph (.imp ps (.imp ch (.imp th ta))))) :
    Nominal.NPrf (.imp th (.imp ph (.imp ps (.imp ch ta)))) :=
  by
  have p0000 := @g_com4t ph ps ch th ta hyp_com4_1
  have p0001 := @g_com4l ch th ph ps ta p0000
  exact p0001

@[expose]
noncomputable def g_pm2_86d (ph : Wff) (ps : Wff) (ch : Wff) (th : Wff)
    (hyp_pm2_86d_1 : Nominal.NPrf (.imp ph (.imp (.imp ps ch) (.imp ps th)))) :
    Nominal.NPrf (.imp ph (.imp ps (.imp ch th))) :=
  by
  have p0000 := Nominal.ax1 ch ps
  have p0001 := @g_syl5 ch (.imp ps ch) ph (.imp ps th) p0000 hyp_pm2_86d_1
  have p0002 := @g_com23 ph ch ps th p0001
  exact p0002

@[expose]
noncomputable def g_con4d (ph : Wff) (ps : Wff) (ch : Wff)
    (hyp_con4d_1 : Nominal.NPrf (.imp ph (.imp (.neg ps) (.neg ch)))) :
    Nominal.NPrf (.imp ph (.imp ch ps)) :=
  by
  have p0000 := Nominal.ax3 ps ch
  have p0001 := @g_syl ph (.imp (.neg ps) (.neg ch)) (.imp ch ps) hyp_con4d_1 p0000
  exact p0001

@[expose]
noncomputable def g_pm2_21d (ph : Wff) (ps : Wff) (ch : Wff)
    (hyp_pm2_21d_1 : Nominal.NPrf (.imp ph (.neg ps))) :
    Nominal.NPrf (.imp ph (.imp ps ch)) :=
  by
  have p0000 := @g_a1d ph (.neg ps) (.neg ch) hyp_pm2_21d_1
  have p0001 := @g_con4d ph ch ps p0000
  exact p0001

@[expose]
noncomputable def g_pm2_21dd (ph : Wff) (ps : Wff) (ch : Wff)
    (hyp_pm2_21dd_1 : Nominal.NPrf (.imp ph ps))
    (hyp_pm2_21dd_2 : Nominal.NPrf (.imp ph (.neg ps))) : Nominal.NPrf (.imp ph ch) :=
  by
  have p0000 := @g_pm2_21d ph ps ch hyp_pm2_21dd_2
  have p0001 := @g_mpd ph ps ch hyp_pm2_21dd_1 p0000
  exact p0001

@[expose]
noncomputable def g_pm2_21 (ph : Wff) (ps : Wff) :
    Nominal.NPrf (.imp (.neg ph) (.imp ph ps)) :=
  by
  have p0000 := @g_id (.neg ph)
  have p0001 := @g_pm2_21d (.neg ph) ph ps p0000
  exact p0001

@[expose]
noncomputable def g_pm2_24 (ph : Wff) (ps : Wff) :
    Nominal.NPrf (.imp ph (.imp (.neg ph) ps)) :=
  by
  have p0000 := @g_pm2_21 ph ps
  have p0001 := @g_com12 (.neg ph) ph ps p0000
  exact p0001

@[expose]
noncomputable def g_pm2_18 (ph : Wff) : Nominal.NPrf (.imp (.imp (.neg ph) ph) ph) :=
  by
  have p0000 := @g_pm2_21 ph (.neg (.imp (.neg ph) ph))
  have p0001 := @g_a2i (.neg ph) ph (.neg (.imp (.neg ph) ph)) p0000
  have p0002 := @g_con4d (.imp (.neg ph) ph) ph (.imp (.neg ph) ph) p0001
  have p0003 := @g_pm2_43i (.imp (.neg ph) ph) ph p0002
  exact p0003

@[expose]
noncomputable def g_pm2_18d (ph : Wff) (ps : Wff)
    (hyp_pm2_18d_1 : Nominal.NPrf (.imp ph (.imp (.neg ps) ps))) :
    Nominal.NPrf (.imp ph ps) :=
  by
  have p0000 := @g_pm2_18 ps
  have p0001 := @g_syl ph (.imp (.neg ps) ps) ps hyp_pm2_18d_1 p0000
  exact p0001

@[expose]
noncomputable def g_notnot2 (ph : Wff) : Nominal.NPrf (.imp (.neg (.neg ph)) ph) :=
  by
  have p0000 := @g_pm2_21 (.neg ph) ph
  have p0001 := @g_pm2_18d (.neg (.neg ph)) ph p0000
  exact p0001

@[expose]
noncomputable def g_notnotrd (ph : Wff) (ps : Wff)
    (hyp_notnotrd_1 : Nominal.NPrf (.imp ph (.neg (.neg ps)))) :
    Nominal.NPrf (.imp ph ps) :=
  by
  have p0000 := @g_notnot2 ps
  have p0001 := @g_syl ph (.neg (.neg ps)) ps hyp_notnotrd_1 p0000
  exact p0001

@[expose]
noncomputable def g_notnotri (ph : Wff) (hyp_notnotri_1 : Nominal.NPrf (.neg (.neg ph))) :
    Nominal.NPrf ph := by
  have p0000 := @g_notnot2 ph
  have p0001 := Nominal.mp hyp_notnotri_1 p0000
  exact p0001

@[expose]
noncomputable def g_con2d (ph : Wff) (ps : Wff) (ch : Wff)
    (hyp_con2d_1 : Nominal.NPrf (.imp ph (.imp ps (.neg ch)))) :
    Nominal.NPrf (.imp ph (.imp ch (.neg ps))) :=
  by
  have p0000 := @g_notnot2 ps
  have p0001 := @g_syl5 (.neg (.neg ps)) ps ph (.neg ch) p0000 hyp_con2d_1
  have p0002 := @g_con4d ph (.neg ps) ch p0001
  exact p0002

@[expose]
noncomputable def g_con2 (ph : Wff) (ps : Wff) :
    Nominal.NPrf (.imp (.imp ph (.neg ps)) (.imp ps (.neg ph))) :=
  by
  have p0000 := @g_id (.imp ph (.neg ps))
  have p0001 := @g_con2d (.imp ph (.neg ps)) ph ps p0000
  exact p0001

@[expose]
noncomputable def g_mt2d (ph : Wff) (ps : Wff) (ch : Wff)
    (hyp_mt2d_1 : Nominal.NPrf (.imp ph ch))
    (hyp_mt2d_2 : Nominal.NPrf (.imp ph (.imp ps (.neg ch)))) :
    Nominal.NPrf (.imp ph (.neg ps)) :=
  by
  have p0000 := @g_con2d ph ps ch hyp_mt2d_2
  have p0001 := @g_mpd ph ch (.neg ps) hyp_mt2d_1 p0000
  exact p0001

@[expose]
noncomputable def g_nsyl3 (ph : Wff) (ps : Wff) (ch : Wff)
    (hyp_nsyl3_1 : Nominal.NPrf (.imp ph (.neg ps)))
    (hyp_nsyl3_2 : Nominal.NPrf (.imp ch ps)) : Nominal.NPrf (.imp ch (.neg ph)) :=
  by
  have p0000 := @g_a1i (.imp ph (.neg ps)) ch hyp_nsyl3_1
  have p0001 := @g_mt2d ch ph ps hyp_nsyl3_2 p0000
  exact p0001

@[expose]
noncomputable def g_con2i (ph : Wff) (ps : Wff)
    (hyp_con2i_a : Nominal.NPrf (.imp ph (.neg ps))) : Nominal.NPrf (.imp ps (.neg ph)) :=
  by
  have p0000 := @g_id ps
  have p0001 := @g_nsyl3 ph ps ps hyp_con2i_a p0000
  exact p0001

@[expose]
noncomputable def g_nsyl (ph : Wff) (ps : Wff) (ch : Wff)
    (hyp_nsyl_1 : Nominal.NPrf (.imp ph (.neg ps)))
    (hyp_nsyl_2 : Nominal.NPrf (.imp ch ps)) : Nominal.NPrf (.imp ph (.neg ch)) :=
  by
  have p0000 := @g_nsyl3 ph ps ch hyp_nsyl_1 hyp_nsyl_2
  have p0001 := @g_con2i ch ph p0000
  exact p0001

@[expose]
noncomputable def g_notnot1 (ph : Wff) : Nominal.NPrf (.imp ph (.neg (.neg ph))) :=
  by
  have p0000 := @g_id (.neg ph)
  have p0001 := @g_con2i (.neg ph) ph p0000
  exact p0001

@[expose]
noncomputable def g_notnoti (ph : Wff) (hyp_negbi_1 : Nominal.NPrf ph) :
    Nominal.NPrf (.neg (.neg ph)) :=
  by
  have p0000 := @g_notnot1 ph
  have p0001 := Nominal.mp hyp_negbi_1 p0000
  exact p0001

@[expose]
noncomputable def g_con1d (ph : Wff) (ps : Wff) (ch : Wff)
    (hyp_con1d_1 : Nominal.NPrf (.imp ph (.imp (.neg ps) ch))) :
    Nominal.NPrf (.imp ph (.imp (.neg ch) ps)) :=
  by
  have p0000 := @g_notnot1 ch
  have p0001 := @g_syl6 ph (.neg ps) ch (.neg (.neg ch)) hyp_con1d_1 p0000
  have p0002 := @g_con4d ph ps (.neg ch) p0001
  exact p0002

@[expose]
noncomputable def g_mt3d (ph : Wff) (ps : Wff) (ch : Wff)
    (hyp_mt3d_1 : Nominal.NPrf (.imp ph (.neg ch)))
    (hyp_mt3d_2 : Nominal.NPrf (.imp ph (.imp (.neg ps) ch))) :
    Nominal.NPrf (.imp ph ps) :=
  by
  have p0000 := @g_con1d ph ps ch hyp_mt3d_2
  have p0001 := @g_mpd ph (.neg ch) ps hyp_mt3d_1 p0000
  exact p0001

@[expose]
noncomputable def g_nsyl2 (ph : Wff) (ps : Wff) (ch : Wff)
    (hyp_nsyl2_1 : Nominal.NPrf (.imp ph (.neg ps)))
    (hyp_nsyl2_2 : Nominal.NPrf (.imp (.neg ch) ps)) : Nominal.NPrf (.imp ph ch) :=
  by
  have p0000 := @g_a1i (.imp (.neg ch) ps) ph hyp_nsyl2_2
  have p0001 := @g_mt3d ph ch ps hyp_nsyl2_1 p0000
  exact p0001

@[expose]
noncomputable def g_con1 (ph : Wff) (ps : Wff) :
    Nominal.NPrf (.imp (.imp (.neg ph) ps) (.imp (.neg ps) ph)) :=
  by
  have p0000 := @g_id (.imp (.neg ph) ps)
  have p0001 := @g_con1d (.imp (.neg ph) ps) ph ps p0000
  exact p0001

@[expose]
noncomputable def g_con1i (ph : Wff) (ps : Wff)
    (hyp_con1i_a : Nominal.NPrf (.imp (.neg ph) ps)) : Nominal.NPrf (.imp (.neg ps) ph) :=
  by
  have p0000 := @g_id (.neg ps)
  have p0001 := @g_nsyl2 (.neg ps) ps ph p0000 hyp_con1i_a
  exact p0001

@[expose]
noncomputable def g_con4i (ph : Wff) (ps : Wff)
    (hyp_con4i_1 : Nominal.NPrf (.imp (.neg ph) (.neg ps))) : Nominal.NPrf (.imp ps ph) :=
  by
  have p0000 := @g_notnot1 ps
  have p0001 := @g_nsyl2 ps (.neg ps) ph p0000 hyp_con4i_1
  exact p0001

@[expose]
noncomputable def g_pm2_21i (ph : Wff) (ps : Wff)
    (hyp_pm2_21i_1 : Nominal.NPrf (.neg ph)) : Nominal.NPrf (.imp ph ps) :=
  by
  have p0000 := @g_a1i (.neg ph) (.neg ps) hyp_pm2_21i_1
  have p0001 := @g_con4i ps ph p0000
  exact p0001

@[expose]
noncomputable def g_con3d (ph : Wff) (ps : Wff) (ch : Wff)
    (hyp_con3d_1 : Nominal.NPrf (.imp ph (.imp ps ch))) :
    Nominal.NPrf (.imp ph (.imp (.neg ch) (.neg ps))) :=
  by
  have p0000 := @g_notnot2 ps
  have p0001 := @g_syl5 (.neg (.neg ps)) ps ph ch p0000 hyp_con3d_1
  have p0002 := @g_con1d ph (.neg ps) ch p0001
  exact p0002

@[expose]
noncomputable def g_con3 (ph : Wff) (ps : Wff) :
    Nominal.NPrf (.imp (.imp ph ps) (.imp (.neg ps) (.neg ph))) :=
  by
  have p0000 := @g_id (.imp ph ps)
  have p0001 := @g_con3d (.imp ph ps) ph ps p0000
  exact p0001

@[expose]
noncomputable def g_con3i (ph : Wff) (ps : Wff)
    (hyp_con3i_a : Nominal.NPrf (.imp ph ps)) : Nominal.NPrf (.imp (.neg ps) (.neg ph)) :=
  by
  have p0000 := @g_id (.neg ps)
  have p0001 := @g_nsyl (.neg ps) ps ph p0000 hyp_con3i_a
  exact p0001

@[expose]
noncomputable def g_con3rr3 (ph : Wff) (ps : Wff) (ch : Wff)
    (hyp_con3rr3_1 : Nominal.NPrf (.imp ph (.imp ps ch))) :
    Nominal.NPrf (.imp (.neg ch) (.imp ph (.neg ps))) :=
  by
  have p0000 := @g_con3d ph ps ch hyp_con3rr3_1
  have p0001 := @g_com12 ph (.neg ch) (.neg ps) p0000
  exact p0001

@[expose]
noncomputable def g_nsyld (ph : Wff) (ps : Wff) (ch : Wff) (ta : Wff)
    (hyp_nsyld_1 : Nominal.NPrf (.imp ph (.imp ps (.neg ch))))
    (hyp_nsyld_2 : Nominal.NPrf (.imp ph (.imp ta ch))) :
    Nominal.NPrf (.imp ph (.imp ps (.neg ta))) :=
  by
  have p0000 := @g_con3d ph ta ch hyp_nsyld_2
  have p0001 := @g_syld ph ps (.neg ch) (.neg ta) hyp_nsyld_1 p0000
  exact p0001

@[expose]
noncomputable def g_nsyl4 (ph : Wff) (ps : Wff) (ch : Wff)
    (hyp_nsyl4_1 : Nominal.NPrf (.imp ph ps))
    (hyp_nsyl4_2 : Nominal.NPrf (.imp (.neg ph) ch)) : Nominal.NPrf (.imp (.neg ch) ps) :=
  by
  have p0000 := @g_con1i ph ch hyp_nsyl4_2
  have p0001 := @g_syl (.neg ch) ph ps p0000 hyp_nsyl4_1
  exact p0001

@[expose]
noncomputable def g_pm2_24i (ph : Wff) (ps : Wff) (hyp_pm2_24i_1 : Nominal.NPrf ph) :
    Nominal.NPrf (.imp (.neg ph) ps) :=
  by
  have p0000 := @g_a1i ph (.neg ps) hyp_pm2_24i_1
  have p0001 := @g_con1i ps ph p0000
  exact p0001

@[expose]
noncomputable def g_pm3_2im (ph : Wff) (ps : Wff) :
    Nominal.NPrf (.imp ph (.imp ps (.neg (.imp ph (.neg ps))))) :=
  by
  have p0000 := @g_pm2_27 ph (.neg ps)
  have p0001 := @g_con2d ph (.imp ph (.neg ps)) ps p0000
  exact p0001

@[expose]
noncomputable def g_impi (ph : Wff) (ps : Wff) (ch : Wff)
    (hyp_impi_1 : Nominal.NPrf (.imp ph (.imp ps ch))) :
    Nominal.NPrf (.imp (.neg (.imp ph (.neg ps))) ch) :=
  by
  have p0000 := @g_con3rr3 ph ps ch hyp_impi_1
  have p0001 := @g_con1i ch (.imp ph (.neg ps)) p0000
  exact p0001

@[expose]
noncomputable def g_expi (ph : Wff) (ps : Wff) (ch : Wff)
    (hyp_expi_1 : Nominal.NPrf (.imp (.neg (.imp ph (.neg ps))) ch)) :
    Nominal.NPrf (.imp ph (.imp ps ch)) :=
  by
  have p0000 := @g_pm3_2im ph ps
  have p0001 := @g_syl6 ph ps (.neg (.imp ph (.neg ps))) ch p0000 hyp_expi_1
  exact p0001

@[expose]
noncomputable def g_simprim (ph : Wff) (ps : Wff) :
    Nominal.NPrf (.imp (.neg (.imp ph (.neg ps))) ps) :=
  by
  have p0000 := @g_idd ph ps
  have p0001 := @g_impi ph ps ps p0000
  exact p0001

@[expose]
noncomputable def g_simplim (ph : Wff) (ps : Wff) :
    Nominal.NPrf (.imp (.neg (.imp ph ps)) ph) :=
  by
  have p0000 := @g_pm2_21 ph ps
  have p0001 := @g_con1i ph (.imp ph ps) p0000
  exact p0001

@[expose]
noncomputable def g_pm2_61d (ph : Wff) (ps : Wff) (ch : Wff)
    (hyp_pm2_61d_1 : Nominal.NPrf (.imp ph (.imp ps ch)))
    (hyp_pm2_61d_2 : Nominal.NPrf (.imp ph (.imp (.neg ps) ch))) :
    Nominal.NPrf (.imp ph ch) :=
  by
  have p0000 := @g_con1d ph ps ch hyp_pm2_61d_2
  have p0001 := @g_syld ph (.neg ch) ps ch p0000 hyp_pm2_61d_1
  have p0002 := @g_pm2_18d ph ch p0001
  exact p0002

@[expose]
noncomputable def g_pm2_61d1 (ph : Wff) (ps : Wff) (ch : Wff)
    (hyp_pm2_61d1_1 : Nominal.NPrf (.imp ph (.imp ps ch)))
    (hyp_pm2_61d1_2 : Nominal.NPrf (.imp (.neg ps) ch)) : Nominal.NPrf (.imp ph ch) :=
  by
  have p0000 := @g_a1i (.imp (.neg ps) ch) ph hyp_pm2_61d1_2
  have p0001 := @g_pm2_61d ph ps ch hyp_pm2_61d1_1 p0000
  exact p0001

@[expose]
noncomputable def g_pm2_61d2 (ph : Wff) (ps : Wff) (ch : Wff)
    (hyp_pm2_61d2_1 : Nominal.NPrf (.imp ph (.imp (.neg ps) ch)))
    (hyp_pm2_61d2_2 : Nominal.NPrf (.imp ps ch)) : Nominal.NPrf (.imp ph ch) :=
  by
  have p0000 := @g_a1i (.imp ps ch) ph hyp_pm2_61d2_2
  have p0001 := @g_pm2_61d ph ps ch p0000 hyp_pm2_61d2_1
  exact p0001

@[expose]
noncomputable def g_ja (ph : Wff) (ps : Wff) (ch : Wff)
    (hyp_ja_1 : Nominal.NPrf (.imp (.neg ph) ch)) (hyp_ja_2 : Nominal.NPrf (.imp ps ch)) :
    Nominal.NPrf (.imp (.imp ph ps) ch) :=
  by
  have p0000 := @g_imim2i ps ch ph hyp_ja_2
  have p0001 := @g_pm2_61d1 (.imp ph ps) ph ch p0000 hyp_ja_1
  exact p0001

@[expose]
noncomputable def g_pm2_61i (ph : Wff) (ps : Wff)
    (hyp_pm2_61i_1 : Nominal.NPrf (.imp ph ps))
    (hyp_pm2_61i_2 : Nominal.NPrf (.imp (.neg ph) ps)) : Nominal.NPrf ps :=
  by
  have p0000 := @g_id ph
  have p0001 := @g_ja ph ph ps hyp_pm2_61i_2 hyp_pm2_61i_1
  have p0002 := Nominal.mp p0000 p0001
  exact p0002

@[expose]
noncomputable def g_pm2_61ii (ph : Wff) (ps : Wff) (ch : Wff)
    (hyp_pm2_61ii_1 : Nominal.NPrf (.imp (.neg ph) (.imp (.neg ps) ch)))
    (hyp_pm2_61ii_2 : Nominal.NPrf (.imp ph ch))
    (hyp_pm2_61ii_3 : Nominal.NPrf (.imp ps ch)) : Nominal.NPrf ch :=
  by
  have p0000 := @g_pm2_61d2 (.neg ph) ps ch hyp_pm2_61ii_1 hyp_pm2_61ii_3
  have p0001 := @g_pm2_61i ph ch hyp_pm2_61ii_2 p0000
  exact p0001

@[expose]
noncomputable def g_pm2_01d (ph : Wff) (ps : Wff)
    (hyp_pm2_01d_1 : Nominal.NPrf (.imp ph (.imp ps (.neg ps)))) :
    Nominal.NPrf (.imp ph (.neg ps)) :=
  by
  have p0000 := @g_id (.neg ps)
  have p0001 := @g_pm2_61d1 ph ps (.neg ps) hyp_pm2_01d_1 p0000
  exact p0001

@[expose]
noncomputable def g_pm2_65i (ph : Wff) (ps : Wff)
    (hyp_pm2_65i_1 : Nominal.NPrf (.imp ph ps))
    (hyp_pm2_65i_2 : Nominal.NPrf (.imp ph (.neg ps))) : Nominal.NPrf (.neg ph) :=
  by
  have p0000 := @g_con2i ph ps hyp_pm2_65i_2
  have p0001 := @g_con3i ph ps hyp_pm2_65i_1
  have p0002 := @g_pm2_61i ps (.neg ph) p0000 p0001
  exact p0002

@[expose]
noncomputable def g_pm2_65d (ph : Wff) (ps : Wff) (ch : Wff)
    (hyp_pm2_65d_1 : Nominal.NPrf (.imp ph (.imp ps ch)))
    (hyp_pm2_65d_2 : Nominal.NPrf (.imp ph (.imp ps (.neg ch)))) :
    Nominal.NPrf (.imp ph (.neg ps)) :=
  by
  have p0000 := @g_nsyld ph ps ch ps hyp_pm2_65d_2 hyp_pm2_65d_1
  have p0001 := @g_pm2_01d ph ps p0000
  exact p0001

@[expose]
noncomputable def g_mto (ph : Wff) (ps : Wff) (hyp_mto_1 : Nominal.NPrf (.neg ps))
    (hyp_mto_2 : Nominal.NPrf (.imp ph ps)) : Nominal.NPrf (.neg ph) :=
  by
  have p0000 := @g_a1i (.neg ps) ph hyp_mto_1
  have p0001 := @g_pm2_65i ph ps hyp_mto_2 p0000
  exact p0001

@[expose]
noncomputable def g_mtod (ph : Wff) (ps : Wff) (ch : Wff)
    (hyp_mtod_1 : Nominal.NPrf (.imp ph (.neg ch)))
    (hyp_mtod_2 : Nominal.NPrf (.imp ph (.imp ps ch))) :
    Nominal.NPrf (.imp ph (.neg ps)) :=
  by
  have p0000 := @g_a1d ph (.neg ch) ps hyp_mtod_1
  have p0001 := @g_pm2_65d ph ps ch hyp_mtod_2 p0000
  exact p0001

@[expose]
noncomputable def g_mtoi (ph : Wff) (ps : Wff) (ch : Wff)
    (hyp_mtoi_1 : Nominal.NPrf (.neg ch))
    (hyp_mtoi_2 : Nominal.NPrf (.imp ph (.imp ps ch))) :
    Nominal.NPrf (.imp ph (.neg ps)) :=
  by
  have p0000 := @g_a1i (.neg ch) ph hyp_mtoi_1
  have p0001 := @g_mtod ph ps ch p0000 hyp_mtoi_2
  exact p0001

@[expose]
noncomputable def g_mt2 (ph : Wff) (ps : Wff) (hyp_mt2_1 : Nominal.NPrf ps)
    (hyp_mt2_2 : Nominal.NPrf (.imp ph (.neg ps))) : Nominal.NPrf (.neg ph) :=
  by
  have p0000 := @g_a1i ps ph hyp_mt2_1
  have p0001 := @g_pm2_65i ph ps p0000 hyp_mt2_2
  exact p0001

@[expose]
noncomputable def g_mt3 (ph : Wff) (ps : Wff) (hyp_mt3_1 : Nominal.NPrf (.neg ps))
    (hyp_mt3_2 : Nominal.NPrf (.imp (.neg ph) ps)) : Nominal.NPrf ph :=
  by
  have p0000 := @g_mto (.neg ph) ps hyp_mt3_1 hyp_mt3_2
  have p0001 := @g_notnotri ph p0000
  exact p0001

@[expose]
noncomputable def g_bi1 (ph : Wff) (ps : Wff) :
    Nominal.NPrf (.imp (syn_wb ph ps) (.imp ph ps)) :=
  by
  have p0000 := Nominal.biimpRefl (syn_wb ph ps)
  have p0001 :=
    @g_simplim (.imp (syn_wb ph ps) (.neg (.imp (.imp ph ps) (.neg (.imp ps ph)))))
      (.neg (.imp (.neg (.imp (.imp ph ps) (.neg (.imp ps ph)))) (syn_wb ph ps)))
  have p0002 := Nominal.mp p0000 p0001
  have p0003 := @g_simplim (.imp ph ps) (.neg (.imp ps ph))
  have p0004 :=
    @g_syl (syn_wb ph ps) (.neg (.imp (.imp ph ps) (.neg (.imp ps ph)))) (.imp ph ps)
      p0002 p0003
  exact p0004

@[expose]
noncomputable def g_bi3 (ph : Wff) (ps : Wff) :
    Nominal.NPrf (.imp (.imp ph ps) (.imp (.imp ps ph) (syn_wb ph ps))) :=
  by
  have p0000 := Nominal.biimpRefl (syn_wb ph ps)
  have p0001 :=
    @g_simprim (.imp (syn_wb ph ps) (.neg (.imp (.imp ph ps) (.neg (.imp ps ph)))))
      (.imp (.neg (.imp (.imp ph ps) (.neg (.imp ps ph)))) (syn_wb ph ps))
  have p0002 := Nominal.mp p0000 p0001
  have p0003 := @g_expi (.imp ph ps) (.imp ps ph) (syn_wb ph ps) p0002
  exact p0003

@[expose]
noncomputable def g_impbii (ph : Wff) (ps : Wff)
    (hyp_impbii_1 : Nominal.NPrf (.imp ph ps))
    (hyp_impbii_2 : Nominal.NPrf (.imp ps ph)) : Nominal.NPrf (syn_wb ph ps) :=
  by
  have p0000 := @g_bi3 ph ps
  have p0001 :=
    @g_mp2 (.imp ph ps) (.imp ps ph) (syn_wb ph ps) hyp_impbii_1 hyp_impbii_2 p0000
  exact p0001

@[expose]
noncomputable def g_impbidd (ph : Wff) (ps : Wff) (ch : Wff) (th : Wff)
    (hyp_impbidd_1 : Nominal.NPrf (.imp ph (.imp ps (.imp ch th))))
    (hyp_impbidd_2 : Nominal.NPrf (.imp ph (.imp ps (.imp th ch)))) :
    Nominal.NPrf (.imp ph (.imp ps (syn_wb ch th))) :=
  by
  have p0000 := @g_bi3 ch th
  have p0001 :=
    @g_syl6c ph ps (.imp ch th) (.imp th ch) (syn_wb ch th) hyp_impbidd_1 hyp_impbidd_2
      p0000
  exact p0001

@[expose]
noncomputable def g_impbid21d (ph : Wff) (ps : Wff) (ch : Wff) (th : Wff)
    (hyp_impbid21d_1 : Nominal.NPrf (.imp ps (.imp ch th)))
    (hyp_impbid21d_2 : Nominal.NPrf (.imp ph (.imp th ch))) :
    Nominal.NPrf (.imp ph (.imp ps (syn_wb ch th))) :=
  by
  have p0000 := @g_a1i (.imp ps (.imp ch th)) ph hyp_impbid21d_1
  have p0001 := @g_a1d ph (.imp th ch) ps hyp_impbid21d_2
  have p0002 := @g_impbidd ph ps ch th p0000 p0001
  exact p0002

@[expose]
noncomputable def g_impbid (ph : Wff) (ps : Wff) (ch : Wff)
    (hyp_impbid_1 : Nominal.NPrf (.imp ph (.imp ps ch)))
    (hyp_impbid_2 : Nominal.NPrf (.imp ph (.imp ch ps))) :
    Nominal.NPrf (.imp ph (syn_wb ps ch)) :=
  by
  have p0000 := @g_impbid21d ph ph ps ch hyp_impbid_1 hyp_impbid_2
  have p0001 := @g_pm2_43i ph (syn_wb ps ch) p0000
  exact p0001

@[expose]
noncomputable def g_dfbi1 (ph : Wff) (ps : Wff) :
    Nominal.NPrf (syn_wb (syn_wb ph ps) (.neg (.imp (.imp ph ps) (.neg (.imp ps ph))))) :=
  by
  have p0000 := Nominal.biimpRefl (syn_wb ph ps)
  have p0001 :=
    @g_simplim (.imp (syn_wb ph ps) (.neg (.imp (.imp ph ps) (.neg (.imp ps ph)))))
      (.neg (.imp (.neg (.imp (.imp ph ps) (.neg (.imp ps ph)))) (syn_wb ph ps)))
  have p0002 := Nominal.mp p0000 p0001
  have p0003 := @g_bi3 ph ps
  have p0004 := @g_impi (.imp ph ps) (.imp ps ph) (syn_wb ph ps) p0003
  have p0005 :=
    @g_impbii (syn_wb ph ps) (.neg (.imp (.imp ph ps) (.neg (.imp ps ph)))) p0002 p0004
  exact p0005

@[expose]
noncomputable def g_biimpi (ph : Wff) (ps : Wff)
    (hyp_biimpi_1 : Nominal.NPrf (syn_wb ph ps)) : Nominal.NPrf (.imp ph ps) :=
  by
  have p0000 := @g_bi1 ph ps
  have p0001 := Nominal.mp hyp_biimpi_1 p0000
  exact p0001

@[expose]
noncomputable def g_sylbi (ph : Wff) (ps : Wff) (ch : Wff)
    (hyp_sylbi_1 : Nominal.NPrf (syn_wb ph ps))
    (hyp_sylbi_2 : Nominal.NPrf (.imp ps ch)) : Nominal.NPrf (.imp ph ch) :=
  by
  have p0000 := @g_biimpi ph ps hyp_sylbi_1
  have p0001 := @g_syl ph ps ch p0000 hyp_sylbi_2
  exact p0001

@[expose]
noncomputable def g_sylib (ph : Wff) (ps : Wff) (ch : Wff)
    (hyp_sylib_1 : Nominal.NPrf (.imp ph ps))
    (hyp_sylib_2 : Nominal.NPrf (syn_wb ps ch)) : Nominal.NPrf (.imp ph ch) :=
  by
  have p0000 := @g_biimpi ps ch hyp_sylib_2
  have p0001 := @g_syl ph ps ch hyp_sylib_1 p0000
  exact p0001

@[expose]
noncomputable def g_bi2 (ph : Wff) (ps : Wff) :
    Nominal.NPrf (.imp (syn_wb ph ps) (.imp ps ph)) :=
  by
  have p0000 := @g_dfbi1 ph ps
  have p0001 := @g_simprim (.imp ph ps) (.imp ps ph)
  have p0002 :=
    @g_sylbi (syn_wb ph ps) (.neg (.imp (.imp ph ps) (.neg (.imp ps ph)))) (.imp ps ph)
      p0000 p0001
  exact p0002

@[expose]
noncomputable def g_bicom1 (ph : Wff) (ps : Wff) :
    Nominal.NPrf (.imp (syn_wb ph ps) (syn_wb ps ph)) :=
  by
  have p0000 := @g_bi2 ph ps
  have p0001 := @g_bi1 ph ps
  have p0002 := @g_impbid (syn_wb ph ps) ps ph p0000 p0001
  exact p0002

@[expose]
noncomputable def g_bicom (ph : Wff) (ps : Wff) :
    Nominal.NPrf (syn_wb (syn_wb ph ps) (syn_wb ps ph)) :=
  by
  have p0000 := @g_bicom1 ph ps
  have p0001 := @g_bicom1 ps ph
  have p0002 := @g_impbii (syn_wb ph ps) (syn_wb ps ph) p0000 p0001
  exact p0002

@[expose]
noncomputable def g_bicomd (ph : Wff) (ps : Wff) (ch : Wff)
    (hyp_bicomd_1 : Nominal.NPrf (.imp ph (syn_wb ps ch))) :
    Nominal.NPrf (.imp ph (syn_wb ch ps)) :=
  by
  have p0000 := @g_bicom ps ch
  have p0001 := @g_sylib ph (syn_wb ps ch) (syn_wb ch ps) hyp_bicomd_1 p0000
  exact p0001

@[expose]
noncomputable def g_bicomi (ph : Wff) (ps : Wff)
    (hyp_bicomi_1 : Nominal.NPrf (syn_wb ph ps)) : Nominal.NPrf (syn_wb ps ph) :=
  by
  have p0000 := @g_bicom1 ph ps
  have p0001 := Nominal.mp hyp_bicomi_1 p0000
  exact p0001

@[expose]
noncomputable def g_impbid1 (ph : Wff) (ps : Wff) (ch : Wff)
    (hyp_impbid1_1 : Nominal.NPrf (.imp ph (.imp ps ch)))
    (hyp_impbid1_2 : Nominal.NPrf (.imp ch ps)) : Nominal.NPrf (.imp ph (syn_wb ps ch)) :=
  by
  have p0000 := @g_a1i (.imp ch ps) ph hyp_impbid1_2
  have p0001 := @g_impbid ph ps ch hyp_impbid1_1 p0000
  exact p0001

@[expose]
noncomputable def g_impbid2 (ph : Wff) (ps : Wff) (ch : Wff)
    (hyp_impbid2_1 : Nominal.NPrf (.imp ps ch))
    (hyp_impbid2_2 : Nominal.NPrf (.imp ph (.imp ch ps))) :
    Nominal.NPrf (.imp ph (syn_wb ps ch)) :=
  by
  have p0000 := @g_impbid1 ph ch ps hyp_impbid2_2 hyp_impbid2_1
  have p0001 := @g_bicomd ph ch ps p0000
  exact p0001

@[expose]
noncomputable def g_impcon4bid (ph : Wff) (ps : Wff) (ch : Wff)
    (hyp_impcon4bid_1 : Nominal.NPrf (.imp ph (.imp ps ch)))
    (hyp_impcon4bid_2 : Nominal.NPrf (.imp ph (.imp (.neg ps) (.neg ch)))) :
    Nominal.NPrf (.imp ph (syn_wb ps ch)) :=
  by
  have p0000 := @g_con4d ph ps ch hyp_impcon4bid_2
  have p0001 := @g_impbid ph ps ch hyp_impcon4bid_1 p0000
  exact p0001

@[expose]
noncomputable def g_biimpri (ph : Wff) (ps : Wff)
    (hyp_biimpri_1 : Nominal.NPrf (syn_wb ph ps)) : Nominal.NPrf (.imp ps ph) :=
  by
  have p0000 := @g_bicomi ph ps hyp_biimpri_1
  have p0001 := @g_biimpi ps ph p0000
  exact p0001

@[expose]
noncomputable def g_biimpd (ph : Wff) (ps : Wff) (ch : Wff)
    (hyp_biimpd_1 : Nominal.NPrf (.imp ph (syn_wb ps ch))) :
    Nominal.NPrf (.imp ph (.imp ps ch)) :=
  by
  have p0000 := @g_bi1 ps ch
  have p0001 := @g_syl ph (syn_wb ps ch) (.imp ps ch) hyp_biimpd_1 p0000
  exact p0001

@[expose]
noncomputable def g_mpbi (ph : Wff) (ps : Wff) (hyp_mpbi_min : Nominal.NPrf ph)
    (hyp_mpbi_maj : Nominal.NPrf (syn_wb ph ps)) : Nominal.NPrf ps :=
  by
  have p0000 := @g_biimpi ph ps hyp_mpbi_maj
  have p0001 := Nominal.mp hyp_mpbi_min p0000
  exact p0001

@[expose]
noncomputable def g_mpbir (ph : Wff) (ps : Wff) (hyp_mpbir_min : Nominal.NPrf ps)
    (hyp_mpbir_maj : Nominal.NPrf (syn_wb ph ps)) : Nominal.NPrf ph :=
  by
  have p0000 := @g_biimpri ph ps hyp_mpbir_maj
  have p0001 := Nominal.mp hyp_mpbir_min p0000
  exact p0001

@[expose]
noncomputable def g_mpbid (ph : Wff) (ps : Wff) (ch : Wff)
    (hyp_mpbid_min : Nominal.NPrf (.imp ph ps))
    (hyp_mpbid_maj : Nominal.NPrf (.imp ph (syn_wb ps ch))) : Nominal.NPrf (.imp ph ch) :=
  by
  have p0000 := @g_biimpd ph ps ch hyp_mpbid_maj
  have p0001 := @g_mpd ph ps ch hyp_mpbid_min p0000
  exact p0001

@[expose]
noncomputable def g_mpbii (ph : Wff) (ps : Wff) (ch : Wff)
    (hyp_mpbii_min : Nominal.NPrf ps)
    (hyp_mpbii_maj : Nominal.NPrf (.imp ph (syn_wb ps ch))) : Nominal.NPrf (.imp ph ch) :=
  by
  have p0000 := @g_a1i ps ph hyp_mpbii_min
  have p0001 := @g_mpbid ph ps ch p0000 hyp_mpbii_maj
  exact p0001

@[expose]
noncomputable def g_sylibr (ph : Wff) (ps : Wff) (ch : Wff)
    (hyp_sylibr_1 : Nominal.NPrf (.imp ph ps))
    (hyp_sylibr_2 : Nominal.NPrf (syn_wb ch ps)) : Nominal.NPrf (.imp ph ch) :=
  by
  have p0000 := @g_biimpri ch ps hyp_sylibr_2
  have p0001 := @g_syl ph ps ch hyp_sylibr_1 p0000
  exact p0001

@[expose]
noncomputable def g_sylbir (ph : Wff) (ps : Wff) (ch : Wff)
    (hyp_sylbir_1 : Nominal.NPrf (syn_wb ps ph))
    (hyp_sylbir_2 : Nominal.NPrf (.imp ps ch)) : Nominal.NPrf (.imp ph ch) :=
  by
  have p0000 := @g_biimpri ps ph hyp_sylbir_1
  have p0001 := @g_syl ph ps ch p0000 hyp_sylbir_2
  exact p0001

@[expose]
noncomputable def g_sylibd (ph : Wff) (ps : Wff) (ch : Wff) (th : Wff)
    (hyp_sylibd_1 : Nominal.NPrf (.imp ph (.imp ps ch)))
    (hyp_sylibd_2 : Nominal.NPrf (.imp ph (syn_wb ch th))) :
    Nominal.NPrf (.imp ph (.imp ps th)) :=
  by
  have p0000 := @g_biimpd ph ch th hyp_sylibd_2
  have p0001 := @g_syld ph ps ch th hyp_sylibd_1 p0000
  exact p0001

@[expose]
noncomputable def g_sylbid (ph : Wff) (ps : Wff) (ch : Wff) (th : Wff)
    (hyp_sylbid_1 : Nominal.NPrf (.imp ph (syn_wb ps ch)))
    (hyp_sylbid_2 : Nominal.NPrf (.imp ph (.imp ch th))) :
    Nominal.NPrf (.imp ph (.imp ps th)) :=
  by
  have p0000 := @g_biimpd ph ps ch hyp_sylbid_1
  have p0001 := @g_syld ph ps ch th p0000 hyp_sylbid_2
  exact p0001

@[expose]
noncomputable def g_mpbidi (ph : Wff) (ps : Wff) (ch : Wff) (th : Wff)
    (hyp_mpbidi_min : Nominal.NPrf (.imp th (.imp ph ps)))
    (hyp_mpbidi_maj : Nominal.NPrf (.imp ph (syn_wb ps ch))) :
    Nominal.NPrf (.imp th (.imp ph ch)) :=
  by
  have p0000 := @g_biimpd ph ps ch hyp_mpbidi_maj
  have p0001 := @g_sylcom th ph ps ch hyp_mpbidi_min p0000
  exact p0001

@[expose]
noncomputable def g_syl5bi (ph : Wff) (ps : Wff) (ch : Wff) (th : Wff)
    (hyp_syl5bi_1 : Nominal.NPrf (syn_wb ph ps))
    (hyp_syl5bi_2 : Nominal.NPrf (.imp ch (.imp ps th))) :
    Nominal.NPrf (.imp ch (.imp ph th)) :=
  by
  have p0000 := @g_biimpi ph ps hyp_syl5bi_1
  have p0001 := @g_syl5 ph ps ch th p0000 hyp_syl5bi_2
  exact p0001

@[expose]
noncomputable def g_syl5bir (ph : Wff) (ps : Wff) (ch : Wff) (th : Wff)
    (hyp_syl5bir_1 : Nominal.NPrf (syn_wb ps ph))
    (hyp_syl5bir_2 : Nominal.NPrf (.imp ch (.imp ps th))) :
    Nominal.NPrf (.imp ch (.imp ph th)) :=
  by
  have p0000 := @g_biimpri ps ph hyp_syl5bir_1
  have p0001 := @g_syl5 ph ps ch th p0000 hyp_syl5bir_2
  exact p0001

@[expose]
noncomputable def g_syl5ib (ph : Wff) (ps : Wff) (ch : Wff) (th : Wff)
    (hyp_syl5ib_1 : Nominal.NPrf (.imp ph ps))
    (hyp_syl5ib_2 : Nominal.NPrf (.imp ch (syn_wb ps th))) :
    Nominal.NPrf (.imp ch (.imp ph th)) :=
  by
  have p0000 := @g_biimpd ch ps th hyp_syl5ib_2
  have p0001 := @g_syl5 ph ps ch th hyp_syl5ib_1 p0000
  exact p0001

@[expose]
noncomputable def g_syl5ibcom (ph : Wff) (ps : Wff) (ch : Wff) (th : Wff)
    (hyp_syl5ib_1 : Nominal.NPrf (.imp ph ps))
    (hyp_syl5ib_2 : Nominal.NPrf (.imp ch (syn_wb ps th))) :
    Nominal.NPrf (.imp ph (.imp ch th)) :=
  by
  have p0000 := @g_syl5ib ph ps ch th hyp_syl5ib_1 hyp_syl5ib_2
  have p0001 := @g_com12 ch ph th p0000
  exact p0001

@[expose]
noncomputable def g_syl5ibr (ph : Wff) (ps : Wff) (ch : Wff) (th : Wff)
    (hyp_syl5ibr_1 : Nominal.NPrf (.imp ph th))
    (hyp_syl5ibr_2 : Nominal.NPrf (.imp ch (syn_wb ps th))) :
    Nominal.NPrf (.imp ch (.imp ph ps)) :=
  by
  have p0000 := @g_bicomd ch ps th hyp_syl5ibr_2
  have p0001 := @g_syl5ib ph th ch ps hyp_syl5ibr_1 p0000
  exact p0001

@[expose]
noncomputable def g_syl5ibrcom (ph : Wff) (ps : Wff) (ch : Wff) (th : Wff)
    (hyp_syl5ibr_1 : Nominal.NPrf (.imp ph th))
    (hyp_syl5ibr_2 : Nominal.NPrf (.imp ch (syn_wb ps th))) :
    Nominal.NPrf (.imp ph (.imp ch ps)) :=
  by
  have p0000 := @g_syl5ibr ph ps ch th hyp_syl5ibr_1 hyp_syl5ibr_2
  have p0001 := @g_com12 ch ph ps p0000
  exact p0001

@[expose]
noncomputable def g_biimprd (ph : Wff) (ps : Wff) (ch : Wff)
    (hyp_biimprd_1 : Nominal.NPrf (.imp ph (syn_wb ps ch))) :
    Nominal.NPrf (.imp ph (.imp ch ps)) :=
  by
  have p0000 := @g_id ch
  have p0001 := @g_syl5ibr ch ps ph ch p0000 hyp_biimprd_1
  exact p0001

@[expose]
noncomputable def g_biimpcd (ph : Wff) (ps : Wff) (ch : Wff)
    (hyp_biimpcd_1 : Nominal.NPrf (.imp ph (syn_wb ps ch))) :
    Nominal.NPrf (.imp ps (.imp ph ch)) :=
  by
  have p0000 := @g_id ps
  have p0001 := @g_syl5ibcom ps ps ph ch p0000 hyp_biimpcd_1
  exact p0001

@[expose]
noncomputable def g_biimprcd (ph : Wff) (ps : Wff) (ch : Wff)
    (hyp_biimpcd_1 : Nominal.NPrf (.imp ph (syn_wb ps ch))) :
    Nominal.NPrf (.imp ch (.imp ph ps)) :=
  by
  have p0000 := @g_id ch
  have p0001 := @g_syl5ibrcom ch ps ph ch p0000 hyp_biimpcd_1
  exact p0001

@[expose]
noncomputable def g_syl6ib (ph : Wff) (ps : Wff) (ch : Wff) (th : Wff)
    (hyp_syl6ib_1 : Nominal.NPrf (.imp ph (.imp ps ch)))
    (hyp_syl6ib_2 : Nominal.NPrf (syn_wb ch th)) : Nominal.NPrf (.imp ph (.imp ps th)) :=
  by
  have p0000 := @g_biimpi ch th hyp_syl6ib_2
  have p0001 := @g_syl6 ph ps ch th hyp_syl6ib_1 p0000
  exact p0001

@[expose]
noncomputable def g_syl6ibr (ph : Wff) (ps : Wff) (ch : Wff) (th : Wff)
    (hyp_syl6ibr_1 : Nominal.NPrf (.imp ph (.imp ps ch)))
    (hyp_syl6ibr_2 : Nominal.NPrf (syn_wb th ch)) : Nominal.NPrf (.imp ph (.imp ps th)) :=
  by
  have p0000 := @g_biimpri th ch hyp_syl6ibr_2
  have p0001 := @g_syl6 ph ps ch th hyp_syl6ibr_1 p0000
  exact p0001

@[expose]
noncomputable def g_syl6bi (ph : Wff) (ps : Wff) (ch : Wff) (th : Wff)
    (hyp_syl6bi_1 : Nominal.NPrf (.imp ph (syn_wb ps ch)))
    (hyp_syl6bi_2 : Nominal.NPrf (.imp ch th)) : Nominal.NPrf (.imp ph (.imp ps th)) :=
  by
  have p0000 := @g_biimpd ph ps ch hyp_syl6bi_1
  have p0001 := @g_syl6 ph ps ch th p0000 hyp_syl6bi_2
  exact p0001

@[expose]
noncomputable def g_syl6bir (ph : Wff) (ps : Wff) (ch : Wff) (th : Wff)
    (hyp_syl6bir_1 : Nominal.NPrf (.imp ph (syn_wb ch ps)))
    (hyp_syl6bir_2 : Nominal.NPrf (.imp ch th)) : Nominal.NPrf (.imp ph (.imp ps th)) :=
  by
  have p0000 := @g_biimprd ph ch ps hyp_syl6bir_1
  have p0001 := @g_syl6 ph ps ch th p0000 hyp_syl6bir_2
  exact p0001

@[expose]
noncomputable def g_syl7bi (ph : Wff) (ps : Wff) (ch : Wff) (th : Wff) (ta : Wff)
    (hyp_syl7bi_1 : Nominal.NPrf (syn_wb ph ps))
    (hyp_syl7bi_2 : Nominal.NPrf (.imp ch (.imp th (.imp ps ta)))) :
    Nominal.NPrf (.imp ch (.imp th (.imp ph ta))) :=
  by
  have p0000 := @g_biimpi ph ps hyp_syl7bi_1
  have p0001 := @g_syl7 ph ps ch th ta p0000 hyp_syl7bi_2
  exact p0001

@[expose]
noncomputable def g_syl8ib (ph : Wff) (ps : Wff) (ch : Wff) (th : Wff) (ta : Wff)
    (hyp_syl8ib_1 : Nominal.NPrf (.imp ph (.imp ps (.imp ch th))))
    (hyp_syl8ib_2 : Nominal.NPrf (syn_wb th ta)) :
    Nominal.NPrf (.imp ph (.imp ps (.imp ch ta))) :=
  by
  have p0000 := @g_biimpi th ta hyp_syl8ib_2
  have p0001 := @g_syl8 ph ps ch th ta hyp_syl8ib_1 p0000
  exact p0001

@[expose]
noncomputable def g_mpbird (ph : Wff) (ps : Wff) (ch : Wff)
    (hyp_mpbird_min : Nominal.NPrf (.imp ph ch))
    (hyp_mpbird_maj : Nominal.NPrf (.imp ph (syn_wb ps ch))) :
    Nominal.NPrf (.imp ph ps) :=
  by
  have p0000 := @g_biimprd ph ps ch hyp_mpbird_maj
  have p0001 := @g_mpd ph ch ps hyp_mpbird_min p0000
  exact p0001

@[expose]
noncomputable def g_mpbiri (ph : Wff) (ps : Wff) (ch : Wff)
    (hyp_mpbiri_min : Nominal.NPrf ch)
    (hyp_mpbiri_maj : Nominal.NPrf (.imp ph (syn_wb ps ch))) :
    Nominal.NPrf (.imp ph ps) :=
  by
  have p0000 := @g_a1i ch ph hyp_mpbiri_min
  have p0001 := @g_mpbird ph ps ch p0000 hyp_mpbiri_maj
  exact p0001

@[expose]
noncomputable def g_sylibrd (ph : Wff) (ps : Wff) (ch : Wff) (th : Wff)
    (hyp_sylibrd_1 : Nominal.NPrf (.imp ph (.imp ps ch)))
    (hyp_sylibrd_2 : Nominal.NPrf (.imp ph (syn_wb th ch))) :
    Nominal.NPrf (.imp ph (.imp ps th)) :=
  by
  have p0000 := @g_biimprd ph th ch hyp_sylibrd_2
  have p0001 := @g_syld ph ps ch th hyp_sylibrd_1 p0000
  exact p0001

@[expose]
noncomputable def g_sylbird (ph : Wff) (ps : Wff) (ch : Wff) (th : Wff)
    (hyp_sylbird_1 : Nominal.NPrf (.imp ph (syn_wb ch ps)))
    (hyp_sylbird_2 : Nominal.NPrf (.imp ph (.imp ch th))) :
    Nominal.NPrf (.imp ph (.imp ps th)) :=
  by
  have p0000 := @g_biimprd ph ch ps hyp_sylbird_1
  have p0001 := @g_syld ph ps ch th p0000 hyp_sylbird_2
  exact p0001

@[expose]
noncomputable def g_biid (ph : Wff) : Nominal.NPrf (syn_wb ph ph) :=
  by
  have p0000 := @g_id ph
  have p0001 := @g_impbii ph ph p0000 p0000
  exact p0001

@[expose]
noncomputable def g_biidd (ph : Wff) (ps : Wff) : Nominal.NPrf (.imp ph (syn_wb ps ps)) :=
  by
  have p0000 := @g_biid ps
  have p0001 := @g_a1i (syn_wb ps ps) ph p0000
  exact p0001

@[expose]
noncomputable def g_pm5_1im (ph : Wff) (ps : Wff) :
    Nominal.NPrf (.imp ph (.imp ps (syn_wb ph ps))) :=
  by
  have p0000 := Nominal.ax1 ps ph
  have p0001 := Nominal.ax1 ph ps
  have p0002 := @g_impbid21d ph ps ph ps p0000 p0001
  exact p0002

@[expose]
noncomputable def g_n_2th (ph : Wff) (ps : Wff) (hyp_n_2th_1 : Nominal.NPrf ph)
    (hyp_n_2th_2 : Nominal.NPrf ps) : Nominal.NPrf (syn_wb ph ps) :=
  by
  have p0000 := @g_a1i ps ph hyp_n_2th_2
  have p0001 := @g_a1i ph ps hyp_n_2th_1
  have p0002 := @g_impbii ph ps p0000 p0001
  exact p0002

@[expose]
noncomputable def g_n_2thd (ph : Wff) (ps : Wff) (ch : Wff)
    (hyp_n_2thd_1 : Nominal.NPrf (.imp ph ps))
    (hyp_n_2thd_2 : Nominal.NPrf (.imp ph ch)) : Nominal.NPrf (.imp ph (syn_wb ps ch)) :=
  by
  have p0000 := @g_pm5_1im ps ch
  have p0001 := @g_sylc ph ps ch (syn_wb ps ch) hyp_n_2thd_1 hyp_n_2thd_2 p0000
  exact p0001

@[expose]
noncomputable def g_ibi (ph : Wff) (ps : Wff)
    (hyp_ibi_1 : Nominal.NPrf (.imp ph (syn_wb ph ps))) : Nominal.NPrf (.imp ph ps) :=
  by
  have p0000 := @g_biimpd ph ph ps hyp_ibi_1
  have p0001 := @g_pm2_43i ph ps p0000
  exact p0001

@[expose]
noncomputable def g_ibir (ph : Wff) (ps : Wff)
    (hyp_ibir_1 : Nominal.NPrf (.imp ph (syn_wb ps ph))) : Nominal.NPrf (.imp ph ps) :=
  by
  have p0000 := @g_bicomd ph ps ph hyp_ibir_1
  have p0001 := @g_ibi ph ps p0000
  exact p0001

@[expose]
noncomputable def g_ibd (ph : Wff) (ps : Wff) (ch : Wff)
    (hyp_ibd_1 : Nominal.NPrf (.imp ph (.imp ps (syn_wb ps ch)))) :
    Nominal.NPrf (.imp ph (.imp ps ch)) :=
  by
  have p0000 := @g_bi1 ps ch
  have p0001 := @g_syli ps ph (syn_wb ps ch) ch hyp_ibd_1 p0000
  exact p0001

@[expose]
noncomputable def g_pm5_74 (ph : Wff) (ps : Wff) (ch : Wff) :
    Nominal.NPrf (syn_wb (.imp ph (syn_wb ps ch)) (syn_wb (.imp ph ps) (.imp ph ch))) :=
  by
  have p0000 := @g_bi1 ps ch
  have p0001 := @g_imim3i (syn_wb ps ch) ps ch ph p0000
  have p0002 := @g_bi2 ps ch
  have p0003 := @g_imim3i (syn_wb ps ch) ch ps ph p0002
  have p0004 := @g_impbid (.imp ph (syn_wb ps ch)) (.imp ph ps) (.imp ph ch) p0001 p0003
  have p0005 := @g_bi1 (.imp ph ps) (.imp ph ch)
  have p0006 := @g_pm2_86d (syn_wb (.imp ph ps) (.imp ph ch)) ph ps ch p0005
  have p0007 := @g_bi2 (.imp ph ps) (.imp ph ch)
  have p0008 := @g_pm2_86d (syn_wb (.imp ph ps) (.imp ph ch)) ph ch ps p0007
  have p0009 := @g_impbidd (syn_wb (.imp ph ps) (.imp ph ch)) ph ps ch p0006 p0008
  have p0010 :=
    @g_impbii (.imp ph (syn_wb ps ch)) (syn_wb (.imp ph ps) (.imp ph ch)) p0004 p0009
  exact p0010

@[expose]
noncomputable def g_pm5_74i (ph : Wff) (ps : Wff) (ch : Wff)
    (hyp_pm5_74i_1 : Nominal.NPrf (.imp ph (syn_wb ps ch))) :
    Nominal.NPrf (syn_wb (.imp ph ps) (.imp ph ch)) :=
  by
  have p0000 := @g_pm5_74 ph ps ch
  have p0001 :=
    @g_mpbi (.imp ph (syn_wb ps ch)) (syn_wb (.imp ph ps) (.imp ph ch)) hyp_pm5_74i_1
      p0000
  exact p0001

@[expose]
noncomputable def g_pm5_74ri (ph : Wff) (ps : Wff) (ch : Wff)
    (hyp_pm5_74ri_1 : Nominal.NPrf (syn_wb (.imp ph ps) (.imp ph ch))) :
    Nominal.NPrf (.imp ph (syn_wb ps ch)) :=
  by
  have p0000 := @g_pm5_74 ph ps ch
  have p0001 :=
    @g_mpbir (.imp ph (syn_wb ps ch)) (syn_wb (.imp ph ps) (.imp ph ch)) hyp_pm5_74ri_1
      p0000
  exact p0001

@[expose]
noncomputable def g_pm5_74d (ph : Wff) (ps : Wff) (ch : Wff) (th : Wff)
    (hyp_pm5_74d_1 : Nominal.NPrf (.imp ph (.imp ps (syn_wb ch th)))) :
    Nominal.NPrf (.imp ph (syn_wb (.imp ps ch) (.imp ps th))) :=
  by
  have p0000 := @g_pm5_74 ps ch th
  have p0001 :=
    @g_sylib ph (.imp ps (syn_wb ch th)) (syn_wb (.imp ps ch) (.imp ps th)) hyp_pm5_74d_1
      p0000
  exact p0001

@[expose]
noncomputable def g_bitri (ph : Wff) (ps : Wff) (ch : Wff)
    (hyp_bitri_1 : Nominal.NPrf (syn_wb ph ps))
    (hyp_bitri_2 : Nominal.NPrf (syn_wb ps ch)) : Nominal.NPrf (syn_wb ph ch) :=
  by
  have p0000 := @g_biimpi ph ps hyp_bitri_1
  have p0001 := @g_sylib ph ps ch p0000 hyp_bitri_2
  have p0002 := @g_biimpri ps ch hyp_bitri_2
  have p0003 := @g_sylibr ch ps ph p0002 hyp_bitri_1
  have p0004 := @g_impbii ph ch p0001 p0003
  exact p0004

@[expose]
noncomputable def g_bitr2i (ph : Wff) (ps : Wff) (ch : Wff)
    (hyp_bitr2i_1 : Nominal.NPrf (syn_wb ph ps))
    (hyp_bitr2i_2 : Nominal.NPrf (syn_wb ps ch)) : Nominal.NPrf (syn_wb ch ph) :=
  by
  have p0000 := @g_bitri ph ps ch hyp_bitr2i_1 hyp_bitr2i_2
  have p0001 := @g_bicomi ph ch p0000
  exact p0001

@[expose]
noncomputable def g_bitr3i (ph : Wff) (ps : Wff) (ch : Wff)
    (hyp_bitr3i_1 : Nominal.NPrf (syn_wb ps ph))
    (hyp_bitr3i_2 : Nominal.NPrf (syn_wb ps ch)) : Nominal.NPrf (syn_wb ph ch) :=
  by
  have p0000 := @g_bicomi ps ph hyp_bitr3i_1
  have p0001 := @g_bitri ph ps ch p0000 hyp_bitr3i_2
  exact p0001

@[expose]
noncomputable def g_bitr4i (ph : Wff) (ps : Wff) (ch : Wff)
    (hyp_bitr4i_1 : Nominal.NPrf (syn_wb ph ps))
    (hyp_bitr4i_2 : Nominal.NPrf (syn_wb ch ps)) : Nominal.NPrf (syn_wb ph ch) :=
  by
  have p0000 := @g_bicomi ch ps hyp_bitr4i_2
  have p0001 := @g_bitri ph ps ch hyp_bitr4i_1 p0000
  exact p0001

@[expose]
noncomputable def g_bitrd (ph : Wff) (ps : Wff) (ch : Wff) (th : Wff)
    (hyp_bitrd_1 : Nominal.NPrf (.imp ph (syn_wb ps ch)))
    (hyp_bitrd_2 : Nominal.NPrf (.imp ph (syn_wb ch th))) :
    Nominal.NPrf (.imp ph (syn_wb ps th)) :=
  by
  have p0000 := @g_pm5_74i ph ps ch hyp_bitrd_1
  have p0001 := @g_pm5_74i ph ch th hyp_bitrd_2
  have p0002 := @g_bitri (.imp ph ps) (.imp ph ch) (.imp ph th) p0000 p0001
  have p0003 := @g_pm5_74ri ph ps th p0002
  exact p0003

@[expose]
noncomputable def g_bitr2d (ph : Wff) (ps : Wff) (ch : Wff) (th : Wff)
    (hyp_bitr2d_1 : Nominal.NPrf (.imp ph (syn_wb ps ch)))
    (hyp_bitr2d_2 : Nominal.NPrf (.imp ph (syn_wb ch th))) :
    Nominal.NPrf (.imp ph (syn_wb th ps)) :=
  by
  have p0000 := @g_bitrd ph ps ch th hyp_bitr2d_1 hyp_bitr2d_2
  have p0001 := @g_bicomd ph ps th p0000
  exact p0001

@[expose]
noncomputable def g_bitr3d (ph : Wff) (ps : Wff) (ch : Wff) (th : Wff)
    (hyp_bitr3d_1 : Nominal.NPrf (.imp ph (syn_wb ps ch)))
    (hyp_bitr3d_2 : Nominal.NPrf (.imp ph (syn_wb ps th))) :
    Nominal.NPrf (.imp ph (syn_wb ch th)) :=
  by
  have p0000 := @g_bicomd ph ps ch hyp_bitr3d_1
  have p0001 := @g_bitrd ph ch ps th p0000 hyp_bitr3d_2
  exact p0001

@[expose]
noncomputable def g_bitr4d (ph : Wff) (ps : Wff) (ch : Wff) (th : Wff)
    (hyp_bitr4d_1 : Nominal.NPrf (.imp ph (syn_wb ps ch)))
    (hyp_bitr4d_2 : Nominal.NPrf (.imp ph (syn_wb th ch))) :
    Nominal.NPrf (.imp ph (syn_wb ps th)) :=
  by
  have p0000 := @g_bicomd ph th ch hyp_bitr4d_2
  have p0001 := @g_bitrd ph ps ch th hyp_bitr4d_1 p0000
  exact p0001

@[expose]
noncomputable def g_syl5bb (ph : Wff) (ps : Wff) (ch : Wff) (th : Wff)
    (hyp_syl5bb_1 : Nominal.NPrf (syn_wb ph ps))
    (hyp_syl5bb_2 : Nominal.NPrf (.imp ch (syn_wb ps th))) :
    Nominal.NPrf (.imp ch (syn_wb ph th)) :=
  by
  have p0000 := @g_a1i (syn_wb ph ps) ch hyp_syl5bb_1
  have p0001 := @g_bitrd ch ph ps th p0000 hyp_syl5bb_2
  exact p0001

@[expose]
noncomputable def g_syl5rbb (ph : Wff) (ps : Wff) (ch : Wff) (th : Wff)
    (hyp_syl5rbb_1 : Nominal.NPrf (syn_wb ph ps))
    (hyp_syl5rbb_2 : Nominal.NPrf (.imp ch (syn_wb ps th))) :
    Nominal.NPrf (.imp ch (syn_wb th ph)) :=
  by
  have p0000 := @g_syl5bb ph ps ch th hyp_syl5rbb_1 hyp_syl5rbb_2
  have p0001 := @g_bicomd ch ph th p0000
  exact p0001

@[expose]
noncomputable def g_syl5bbr (ph : Wff) (ps : Wff) (ch : Wff) (th : Wff)
    (hyp_syl5bbr_1 : Nominal.NPrf (syn_wb ps ph))
    (hyp_syl5bbr_2 : Nominal.NPrf (.imp ch (syn_wb ps th))) :
    Nominal.NPrf (.imp ch (syn_wb ph th)) :=
  by
  have p0000 := @g_bicomi ps ph hyp_syl5bbr_1
  have p0001 := @g_syl5bb ph ps ch th p0000 hyp_syl5bbr_2
  exact p0001

@[expose]
noncomputable def g_syl5rbbr (ph : Wff) (ps : Wff) (ch : Wff) (th : Wff)
    (hyp_syl5rbbr_1 : Nominal.NPrf (syn_wb ps ph))
    (hyp_syl5rbbr_2 : Nominal.NPrf (.imp ch (syn_wb ps th))) :
    Nominal.NPrf (.imp ch (syn_wb th ph)) :=
  by
  have p0000 := @g_bicomi ps ph hyp_syl5rbbr_1
  have p0001 := @g_syl5rbb ph ps ch th p0000 hyp_syl5rbbr_2
  exact p0001

@[expose]
noncomputable def g_syl6bb (ph : Wff) (ps : Wff) (ch : Wff) (th : Wff)
    (hyp_syl6bb_1 : Nominal.NPrf (.imp ph (syn_wb ps ch)))
    (hyp_syl6bb_2 : Nominal.NPrf (syn_wb ch th)) :
    Nominal.NPrf (.imp ph (syn_wb ps th)) :=
  by
  have p0000 := @g_a1i (syn_wb ch th) ph hyp_syl6bb_2
  have p0001 := @g_bitrd ph ps ch th hyp_syl6bb_1 p0000
  exact p0001

@[expose]
noncomputable def g_syl6rbb (ph : Wff) (ps : Wff) (ch : Wff) (th : Wff)
    (hyp_syl6rbb_1 : Nominal.NPrf (.imp ph (syn_wb ps ch)))
    (hyp_syl6rbb_2 : Nominal.NPrf (syn_wb ch th)) :
    Nominal.NPrf (.imp ph (syn_wb th ps)) :=
  by
  have p0000 := @g_syl6bb ph ps ch th hyp_syl6rbb_1 hyp_syl6rbb_2
  have p0001 := @g_bicomd ph ps th p0000
  exact p0001

@[expose]
noncomputable def g_syl6bbr (ph : Wff) (ps : Wff) (ch : Wff) (th : Wff)
    (hyp_syl6bbr_1 : Nominal.NPrf (.imp ph (syn_wb ps ch)))
    (hyp_syl6bbr_2 : Nominal.NPrf (syn_wb th ch)) :
    Nominal.NPrf (.imp ph (syn_wb ps th)) :=
  by
  have p0000 := @g_bicomi th ch hyp_syl6bbr_2
  have p0001 := @g_syl6bb ph ps ch th hyp_syl6bbr_1 p0000
  exact p0001

@[expose]
noncomputable def g_syl6rbbr (ph : Wff) (ps : Wff) (ch : Wff) (th : Wff)
    (hyp_syl6rbbr_1 : Nominal.NPrf (.imp ph (syn_wb ps ch)))
    (hyp_syl6rbbr_2 : Nominal.NPrf (syn_wb th ch)) :
    Nominal.NPrf (.imp ph (syn_wb th ps)) :=
  by
  have p0000 := @g_bicomi th ch hyp_syl6rbbr_2
  have p0001 := @g_syl6rbb ph ps ch th hyp_syl6rbbr_1 p0000
  exact p0001

@[expose]
noncomputable def g_n_3imtr3i (ph : Wff) (ps : Wff) (ch : Wff) (th : Wff)
    (hyp_n_3imtr3_1 : Nominal.NPrf (.imp ph ps))
    (hyp_n_3imtr3_2 : Nominal.NPrf (syn_wb ph ch))
    (hyp_n_3imtr3_3 : Nominal.NPrf (syn_wb ps th)) : Nominal.NPrf (.imp ch th) :=
  by
  have p0000 := @g_sylbir ch ph ps hyp_n_3imtr3_2 hyp_n_3imtr3_1
  have p0001 := @g_sylib ch ps th p0000 hyp_n_3imtr3_3
  exact p0001

@[expose]
noncomputable def g_n_3imtr4i (ph : Wff) (ps : Wff) (ch : Wff) (th : Wff)
    (hyp_n_3imtr4_1 : Nominal.NPrf (.imp ph ps))
    (hyp_n_3imtr4_2 : Nominal.NPrf (syn_wb ch ph))
    (hyp_n_3imtr4_3 : Nominal.NPrf (syn_wb th ps)) : Nominal.NPrf (.imp ch th) :=
  by
  have p0000 := @g_sylbi ch ph ps hyp_n_3imtr4_2 hyp_n_3imtr4_1
  have p0001 := @g_sylibr ch ps th p0000 hyp_n_3imtr4_3
  exact p0001

@[expose]
noncomputable def g_n_3imtr3d (ph : Wff) (ps : Wff) (ch : Wff) (th : Wff) (ta : Wff)
    (hyp_n_3imtr3d_1 : Nominal.NPrf (.imp ph (.imp ps ch)))
    (hyp_n_3imtr3d_2 : Nominal.NPrf (.imp ph (syn_wb ps th)))
    (hyp_n_3imtr3d_3 : Nominal.NPrf (.imp ph (syn_wb ch ta))) :
    Nominal.NPrf (.imp ph (.imp th ta)) :=
  by
  have p0000 := @g_sylibd ph ps ch ta hyp_n_3imtr3d_1 hyp_n_3imtr3d_3
  have p0001 := @g_sylbird ph th ps ta hyp_n_3imtr3d_2 p0000
  exact p0001

@[expose]
noncomputable def g_n_3imtr4d (ph : Wff) (ps : Wff) (ch : Wff) (th : Wff) (ta : Wff)
    (hyp_n_3imtr4d_1 : Nominal.NPrf (.imp ph (.imp ps ch)))
    (hyp_n_3imtr4d_2 : Nominal.NPrf (.imp ph (syn_wb th ps)))
    (hyp_n_3imtr4d_3 : Nominal.NPrf (.imp ph (syn_wb ta ch))) :
    Nominal.NPrf (.imp ph (.imp th ta)) :=
  by
  have p0000 := @g_sylibrd ph ps ch ta hyp_n_3imtr4d_1 hyp_n_3imtr4d_3
  have p0001 := @g_sylbid ph th ps ta hyp_n_3imtr4d_2 p0000
  exact p0001

@[expose]
noncomputable def g_n_3imtr3g (ph : Wff) (ps : Wff) (ch : Wff) (th : Wff) (ta : Wff)
    (hyp_n_3imtr3g_1 : Nominal.NPrf (.imp ph (.imp ps ch)))
    (hyp_n_3imtr3g_2 : Nominal.NPrf (syn_wb ps th))
    (hyp_n_3imtr3g_3 : Nominal.NPrf (syn_wb ch ta)) :
    Nominal.NPrf (.imp ph (.imp th ta)) :=
  by
  have p0000 := @g_syl5bir th ps ph ch hyp_n_3imtr3g_2 hyp_n_3imtr3g_1
  have p0001 := @g_syl6ib ph th ch ta p0000 hyp_n_3imtr3g_3
  exact p0001

@[expose]
noncomputable def g_n_3imtr4g (ph : Wff) (ps : Wff) (ch : Wff) (th : Wff) (ta : Wff)
    (hyp_n_3imtr4g_1 : Nominal.NPrf (.imp ph (.imp ps ch)))
    (hyp_n_3imtr4g_2 : Nominal.NPrf (syn_wb th ps))
    (hyp_n_3imtr4g_3 : Nominal.NPrf (syn_wb ta ch)) :
    Nominal.NPrf (.imp ph (.imp th ta)) :=
  by
  have p0000 := @g_syl5bi th ps ph ch hyp_n_3imtr4g_2 hyp_n_3imtr4g_1
  have p0001 := @g_syl6ibr ph th ch ta p0000 hyp_n_3imtr4g_3
  exact p0001

@[expose]
noncomputable def g_n_3bitri (ph : Wff) (ps : Wff) (ch : Wff) (th : Wff)
    (hyp_n_3bitri_1 : Nominal.NPrf (syn_wb ph ps))
    (hyp_n_3bitri_2 : Nominal.NPrf (syn_wb ps ch))
    (hyp_n_3bitri_3 : Nominal.NPrf (syn_wb ch th)) : Nominal.NPrf (syn_wb ph th) :=
  by
  have p0000 := @g_bitri ps ch th hyp_n_3bitri_2 hyp_n_3bitri_3
  have p0001 := @g_bitri ph ps th hyp_n_3bitri_1 p0000
  exact p0001

@[expose]
noncomputable def g_n_3bitrri (ph : Wff) (ps : Wff) (ch : Wff) (th : Wff)
    (hyp_n_3bitri_1 : Nominal.NPrf (syn_wb ph ps))
    (hyp_n_3bitri_2 : Nominal.NPrf (syn_wb ps ch))
    (hyp_n_3bitri_3 : Nominal.NPrf (syn_wb ch th)) : Nominal.NPrf (syn_wb th ph) :=
  by
  have p0000 := @g_bitr2i ph ps ch hyp_n_3bitri_1 hyp_n_3bitri_2
  have p0001 := @g_bitr3i th ch ph hyp_n_3bitri_3 p0000
  exact p0001

@[expose]
noncomputable def g_n_3bitr2i (ph : Wff) (ps : Wff) (ch : Wff) (th : Wff)
    (hyp_n_3bitr2i_1 : Nominal.NPrf (syn_wb ph ps))
    (hyp_n_3bitr2i_2 : Nominal.NPrf (syn_wb ch ps))
    (hyp_n_3bitr2i_3 : Nominal.NPrf (syn_wb ch th)) : Nominal.NPrf (syn_wb ph th) :=
  by
  have p0000 := @g_bitr4i ph ps ch hyp_n_3bitr2i_1 hyp_n_3bitr2i_2
  have p0001 := @g_bitri ph ch th p0000 hyp_n_3bitr2i_3
  exact p0001

@[expose]
noncomputable def g_n_3bitr2ri (ph : Wff) (ps : Wff) (ch : Wff) (th : Wff)
    (hyp_n_3bitr2i_1 : Nominal.NPrf (syn_wb ph ps))
    (hyp_n_3bitr2i_2 : Nominal.NPrf (syn_wb ch ps))
    (hyp_n_3bitr2i_3 : Nominal.NPrf (syn_wb ch th)) : Nominal.NPrf (syn_wb th ph) :=
  by
  have p0000 := @g_bitr4i ph ps ch hyp_n_3bitr2i_1 hyp_n_3bitr2i_2
  have p0001 := @g_bitr2i ph ch th p0000 hyp_n_3bitr2i_3
  exact p0001

@[expose]
noncomputable def g_n_3bitr3i (ph : Wff) (ps : Wff) (ch : Wff) (th : Wff)
    (hyp_n_3bitr3i_1 : Nominal.NPrf (syn_wb ph ps))
    (hyp_n_3bitr3i_2 : Nominal.NPrf (syn_wb ph ch))
    (hyp_n_3bitr3i_3 : Nominal.NPrf (syn_wb ps th)) : Nominal.NPrf (syn_wb ch th) :=
  by
  have p0000 := @g_bitr3i ch ph ps hyp_n_3bitr3i_2 hyp_n_3bitr3i_1
  have p0001 := @g_bitri ch ps th p0000 hyp_n_3bitr3i_3
  exact p0001

@[expose]
noncomputable def g_n_3bitr3ri (ph : Wff) (ps : Wff) (ch : Wff) (th : Wff)
    (hyp_n_3bitr3i_1 : Nominal.NPrf (syn_wb ph ps))
    (hyp_n_3bitr3i_2 : Nominal.NPrf (syn_wb ph ch))
    (hyp_n_3bitr3i_3 : Nominal.NPrf (syn_wb ps th)) : Nominal.NPrf (syn_wb th ch) :=
  by
  have p0000 := @g_bitr3i ps ph ch hyp_n_3bitr3i_1 hyp_n_3bitr3i_2
  have p0001 := @g_bitr3i th ps ch hyp_n_3bitr3i_3 p0000
  exact p0001

@[expose]
noncomputable def g_n_3bitr4i (ph : Wff) (ps : Wff) (ch : Wff) (th : Wff)
    (hyp_n_3bitr4i_1 : Nominal.NPrf (syn_wb ph ps))
    (hyp_n_3bitr4i_2 : Nominal.NPrf (syn_wb ch ph))
    (hyp_n_3bitr4i_3 : Nominal.NPrf (syn_wb th ps)) : Nominal.NPrf (syn_wb ch th) :=
  by
  have p0000 := @g_bitr4i ph ps th hyp_n_3bitr4i_1 hyp_n_3bitr4i_3
  have p0001 := @g_bitri ch ph th hyp_n_3bitr4i_2 p0000
  exact p0001

@[expose]
noncomputable def g_n_3bitr4ri (ph : Wff) (ps : Wff) (ch : Wff) (th : Wff)
    (hyp_n_3bitr4i_1 : Nominal.NPrf (syn_wb ph ps))
    (hyp_n_3bitr4i_2 : Nominal.NPrf (syn_wb ch ph))
    (hyp_n_3bitr4i_3 : Nominal.NPrf (syn_wb th ps)) : Nominal.NPrf (syn_wb th ch) :=
  by
  have p0000 := @g_bitr4i ph ps th hyp_n_3bitr4i_1 hyp_n_3bitr4i_3
  have p0001 := @g_bitr2i ch ph th hyp_n_3bitr4i_2 p0000
  exact p0001

@[expose]
noncomputable def g_n_3bitrd (ph : Wff) (ps : Wff) (ch : Wff) (th : Wff) (ta : Wff)
    (hyp_n_3bitrd_1 : Nominal.NPrf (.imp ph (syn_wb ps ch)))
    (hyp_n_3bitrd_2 : Nominal.NPrf (.imp ph (syn_wb ch th)))
    (hyp_n_3bitrd_3 : Nominal.NPrf (.imp ph (syn_wb th ta))) :
    Nominal.NPrf (.imp ph (syn_wb ps ta)) :=
  by
  have p0000 := @g_bitrd ph ps ch th hyp_n_3bitrd_1 hyp_n_3bitrd_2
  have p0001 := @g_bitrd ph ps th ta p0000 hyp_n_3bitrd_3
  exact p0001

@[expose]
noncomputable def g_n_3bitr2rd (ph : Wff) (ps : Wff) (ch : Wff) (th : Wff) (ta : Wff)
    (hyp_n_3bitr2d_1 : Nominal.NPrf (.imp ph (syn_wb ps ch)))
    (hyp_n_3bitr2d_2 : Nominal.NPrf (.imp ph (syn_wb th ch)))
    (hyp_n_3bitr2d_3 : Nominal.NPrf (.imp ph (syn_wb th ta))) :
    Nominal.NPrf (.imp ph (syn_wb ta ps)) :=
  by
  have p0000 := @g_bitr4d ph ps ch th hyp_n_3bitr2d_1 hyp_n_3bitr2d_2
  have p0001 := @g_bitr2d ph ps th ta p0000 hyp_n_3bitr2d_3
  exact p0001

@[expose]
noncomputable def g_n_3bitr3d (ph : Wff) (ps : Wff) (ch : Wff) (th : Wff) (ta : Wff)
    (hyp_n_3bitr3d_1 : Nominal.NPrf (.imp ph (syn_wb ps ch)))
    (hyp_n_3bitr3d_2 : Nominal.NPrf (.imp ph (syn_wb ps th)))
    (hyp_n_3bitr3d_3 : Nominal.NPrf (.imp ph (syn_wb ch ta))) :
    Nominal.NPrf (.imp ph (syn_wb th ta)) :=
  by
  have p0000 := @g_bitr3d ph ps th ch hyp_n_3bitr3d_2 hyp_n_3bitr3d_1
  have p0001 := @g_bitrd ph th ch ta p0000 hyp_n_3bitr3d_3
  exact p0001

@[expose]
noncomputable def g_n_3bitr4d (ph : Wff) (ps : Wff) (ch : Wff) (th : Wff) (ta : Wff)
    (hyp_n_3bitr4d_1 : Nominal.NPrf (.imp ph (syn_wb ps ch)))
    (hyp_n_3bitr4d_2 : Nominal.NPrf (.imp ph (syn_wb th ps)))
    (hyp_n_3bitr4d_3 : Nominal.NPrf (.imp ph (syn_wb ta ch))) :
    Nominal.NPrf (.imp ph (syn_wb th ta)) :=
  by
  have p0000 := @g_bitr4d ph ps ch ta hyp_n_3bitr4d_1 hyp_n_3bitr4d_3
  have p0001 := @g_bitrd ph th ps ta hyp_n_3bitr4d_2 p0000
  exact p0001

@[expose]
noncomputable def g_n_3bitr3g (ph : Wff) (ps : Wff) (ch : Wff) (th : Wff) (ta : Wff)
    (hyp_n_3bitr3g_1 : Nominal.NPrf (.imp ph (syn_wb ps ch)))
    (hyp_n_3bitr3g_2 : Nominal.NPrf (syn_wb ps th))
    (hyp_n_3bitr3g_3 : Nominal.NPrf (syn_wb ch ta)) :
    Nominal.NPrf (.imp ph (syn_wb th ta)) :=
  by
  have p0000 := @g_syl5bbr th ps ph ch hyp_n_3bitr3g_2 hyp_n_3bitr3g_1
  have p0001 := @g_syl6bb ph th ch ta p0000 hyp_n_3bitr3g_3
  exact p0001

@[expose]
noncomputable def g_n_3bitr4g (ph : Wff) (ps : Wff) (ch : Wff) (th : Wff) (ta : Wff)
    (hyp_n_3bitr4g_1 : Nominal.NPrf (.imp ph (syn_wb ps ch)))
    (hyp_n_3bitr4g_2 : Nominal.NPrf (syn_wb th ps))
    (hyp_n_3bitr4g_3 : Nominal.NPrf (syn_wb ta ch)) :
    Nominal.NPrf (.imp ph (syn_wb th ta)) :=
  by
  have p0000 := @g_syl5bb th ps ph ch hyp_n_3bitr4g_2 hyp_n_3bitr4g_1
  have p0001 := @g_syl6bbr ph th ch ta p0000 hyp_n_3bitr4g_3
  exact p0001

@[expose]
noncomputable def g_notnot (ph : Wff) : Nominal.NPrf (syn_wb ph (.neg (.neg ph))) :=
  by
  have p0000 := @g_notnot1 ph
  have p0001 := @g_notnot2 ph
  have p0002 := @g_impbii ph (.neg (.neg ph)) p0000 p0001
  exact p0002

@[expose]
noncomputable def g_con34b (ph : Wff) (ps : Wff) :
    Nominal.NPrf (syn_wb (.imp ph ps) (.imp (.neg ps) (.neg ph))) :=
  by
  have p0000 := @g_con3 ph ps
  have p0001 := Nominal.ax3 ps ph
  have p0002 := @g_impbii (.imp ph ps) (.imp (.neg ps) (.neg ph)) p0000 p0001
  exact p0002

@[expose]
noncomputable def g_con4bid (ph : Wff) (ps : Wff) (ch : Wff)
    (hyp_con4bid_1 : Nominal.NPrf (.imp ph (syn_wb (.neg ps) (.neg ch)))) :
    Nominal.NPrf (.imp ph (syn_wb ps ch)) :=
  by
  have p0000 := @g_biimprd ph (.neg ps) (.neg ch) hyp_con4bid_1
  have p0001 := @g_con4d ph ch ps p0000
  have p0002 := @g_biimpd ph (.neg ps) (.neg ch) hyp_con4bid_1
  have p0003 := @g_impcon4bid ph ps ch p0001 p0002
  exact p0003

@[expose]
noncomputable def g_notbid (ph : Wff) (ps : Wff) (ch : Wff)
    (hyp_notbid_1 : Nominal.NPrf (.imp ph (syn_wb ps ch))) :
    Nominal.NPrf (.imp ph (syn_wb (.neg ps) (.neg ch))) :=
  by
  have p0000 := @g_notnot ps
  have p0001 := @g_notnot ch
  have p0002 :=
    @g_n_3bitr3g ph ps ch (.neg (.neg ps)) (.neg (.neg ch)) hyp_notbid_1 p0000 p0001
  have p0003 := @g_con4bid ph (.neg ps) (.neg ch) p0002
  exact p0003

@[expose]
noncomputable def g_notbi (ph : Wff) (ps : Wff) :
    Nominal.NPrf (syn_wb (syn_wb ph ps) (syn_wb (.neg ph) (.neg ps))) :=
  by
  have p0000 := @g_id (syn_wb ph ps)
  have p0001 := @g_notbid (syn_wb ph ps) ph ps p0000
  have p0002 := @g_id (syn_wb (.neg ph) (.neg ps))
  have p0003 := @g_con4bid (syn_wb (.neg ph) (.neg ps)) ph ps p0002
  have p0004 := @g_impbii (syn_wb ph ps) (syn_wb (.neg ph) (.neg ps)) p0001 p0003
  exact p0004

@[expose]
noncomputable def g_notbii (ph : Wff) (ps : Wff)
    (hyp_notbii_1 : Nominal.NPrf (syn_wb ph ps)) :
    Nominal.NPrf (syn_wb (.neg ph) (.neg ps)) :=
  by
  have p0000 := @g_notbi ph ps
  have p0001 := @g_mpbi (syn_wb ph ps) (syn_wb (.neg ph) (.neg ps)) hyp_notbii_1 p0000
  exact p0001

@[expose]
noncomputable def g_con4bii (ph : Wff) (ps : Wff)
    (hyp_con4bii_1 : Nominal.NPrf (syn_wb (.neg ph) (.neg ps))) :
    Nominal.NPrf (syn_wb ph ps) :=
  by
  have p0000 := @g_notbi ph ps
  have p0001 := @g_mpbir (syn_wb ph ps) (syn_wb (.neg ph) (.neg ps)) hyp_con4bii_1 p0000
  exact p0001

@[expose]
noncomputable def g_mtbi (ph : Wff) (ps : Wff) (hyp_mtbi_1 : Nominal.NPrf (.neg ph))
    (hyp_mtbi_2 : Nominal.NPrf (syn_wb ph ps)) : Nominal.NPrf (.neg ps) :=
  by
  have p0000 := @g_biimpri ph ps hyp_mtbi_2
  have p0001 := @g_mto ps ph hyp_mtbi_1 p0000
  exact p0001

@[expose]
noncomputable def g_mtbir (ph : Wff) (ps : Wff) (hyp_mtbir_1 : Nominal.NPrf (.neg ps))
    (hyp_mtbir_2 : Nominal.NPrf (syn_wb ph ps)) : Nominal.NPrf (.neg ph) :=
  by
  have p0000 := @g_bicomi ph ps hyp_mtbir_2
  have p0001 := @g_mtbi ps ph hyp_mtbir_1 p0000
  exact p0001

@[expose]
noncomputable def g_mtbid (ph : Wff) (ps : Wff) (ch : Wff)
    (hyp_mtbid_min : Nominal.NPrf (.imp ph (.neg ps)))
    (hyp_mtbid_maj : Nominal.NPrf (.imp ph (syn_wb ps ch))) :
    Nominal.NPrf (.imp ph (.neg ch)) :=
  by
  have p0000 := @g_biimprd ph ps ch hyp_mtbid_maj
  have p0001 := @g_mtod ph ch ps hyp_mtbid_min p0000
  exact p0001

@[expose]
noncomputable def g_mtbird (ph : Wff) (ps : Wff) (ch : Wff)
    (hyp_mtbird_min : Nominal.NPrf (.imp ph (.neg ch)))
    (hyp_mtbird_maj : Nominal.NPrf (.imp ph (syn_wb ps ch))) :
    Nominal.NPrf (.imp ph (.neg ps)) :=
  by
  have p0000 := @g_biimpd ph ps ch hyp_mtbird_maj
  have p0001 := @g_mtod ph ps ch hyp_mtbird_min p0000
  exact p0001

@[expose]
noncomputable def g_mtbii (ph : Wff) (ps : Wff) (ch : Wff)
    (hyp_mtbii_min : Nominal.NPrf (.neg ps))
    (hyp_mtbii_maj : Nominal.NPrf (.imp ph (syn_wb ps ch))) :
    Nominal.NPrf (.imp ph (.neg ch)) :=
  by
  have p0000 := @g_biimprd ph ps ch hyp_mtbii_maj
  have p0001 := @g_mtoi ph ch ps hyp_mtbii_min p0000
  exact p0001

@[expose]
noncomputable def g_mtbiri (ph : Wff) (ps : Wff) (ch : Wff)
    (hyp_mtbiri_min : Nominal.NPrf (.neg ch))
    (hyp_mtbiri_maj : Nominal.NPrf (.imp ph (syn_wb ps ch))) :
    Nominal.NPrf (.imp ph (.neg ps)) :=
  by
  have p0000 := @g_biimpd ph ps ch hyp_mtbiri_maj
  have p0001 := @g_mtoi ph ps ch hyp_mtbiri_min p0000
  exact p0001

@[expose]
noncomputable def g_sylnib (ph : Wff) (ps : Wff) (ch : Wff)
    (hyp_sylnib_1 : Nominal.NPrf (.imp ph (.neg ps)))
    (hyp_sylnib_2 : Nominal.NPrf (syn_wb ps ch)) : Nominal.NPrf (.imp ph (.neg ch)) :=
  by
  have p0000 := @g_a1i (syn_wb ps ch) ph hyp_sylnib_2
  have p0001 := @g_mtbid ph ps ch hyp_sylnib_1 p0000
  exact p0001

@[expose]
noncomputable def g_sylnibr (ph : Wff) (ps : Wff) (ch : Wff)
    (hyp_sylnibr_1 : Nominal.NPrf (.imp ph (.neg ps)))
    (hyp_sylnibr_2 : Nominal.NPrf (syn_wb ch ps)) : Nominal.NPrf (.imp ph (.neg ch)) :=
  by
  have p0000 := @g_bicomi ch ps hyp_sylnibr_2
  have p0001 := @g_sylnib ph ps ch hyp_sylnibr_1 p0000
  exact p0001

@[expose]
noncomputable def g_sylnbi (ph : Wff) (ps : Wff) (ch : Wff)
    (hyp_sylnbi_1 : Nominal.NPrf (syn_wb ph ps))
    (hyp_sylnbi_2 : Nominal.NPrf (.imp (.neg ps) ch)) :
    Nominal.NPrf (.imp (.neg ph) ch) :=
  by
  have p0000 := @g_notbii ph ps hyp_sylnbi_1
  have p0001 := @g_sylbi (.neg ph) (.neg ps) ch p0000 hyp_sylnbi_2
  exact p0001

@[expose]
noncomputable def g_sylnbir (ph : Wff) (ps : Wff) (ch : Wff)
    (hyp_sylnbir_1 : Nominal.NPrf (syn_wb ps ph))
    (hyp_sylnbir_2 : Nominal.NPrf (.imp (.neg ps) ch)) :
    Nominal.NPrf (.imp (.neg ph) ch) :=
  by
  have p0000 := @g_bicomi ps ph hyp_sylnbir_1
  have p0001 := @g_sylnbi ph ps ch p0000 hyp_sylnbir_2
  exact p0001

@[expose]
noncomputable def g_xchnxbi (ph : Wff) (ps : Wff) (ch : Wff)
    (hyp_xchnxbi_1 : Nominal.NPrf (syn_wb (.neg ph) ps))
    (hyp_xchnxbi_2 : Nominal.NPrf (syn_wb ph ch)) : Nominal.NPrf (syn_wb (.neg ch) ps) :=
  by
  have p0000 := @g_notbii ph ch hyp_xchnxbi_2
  have p0001 := @g_bitr3i (.neg ch) (.neg ph) ps p0000 hyp_xchnxbi_1
  exact p0001

@[expose]
noncomputable def g_xchbinx (ph : Wff) (ps : Wff) (ch : Wff)
    (hyp_xchbinx_1 : Nominal.NPrf (syn_wb ph (.neg ps)))
    (hyp_xchbinx_2 : Nominal.NPrf (syn_wb ps ch)) : Nominal.NPrf (syn_wb ph (.neg ch)) :=
  by
  have p0000 := @g_notbii ps ch hyp_xchbinx_2
  have p0001 := @g_bitri ph (.neg ps) (.neg ch) hyp_xchbinx_1 p0000
  exact p0001

@[expose]
noncomputable def g_xchbinxr (ph : Wff) (ps : Wff) (ch : Wff)
    (hyp_xchbinxr_1 : Nominal.NPrf (syn_wb ph (.neg ps)))
    (hyp_xchbinxr_2 : Nominal.NPrf (syn_wb ch ps)) : Nominal.NPrf (syn_wb ph (.neg ch)) :=
  by
  have p0000 := @g_bicomi ch ps hyp_xchbinxr_2
  have p0001 := @g_xchbinx ph ps ch hyp_xchbinxr_1 p0000
  exact p0001

@[expose]
noncomputable def g_imbi2i (ph : Wff) (ps : Wff) (ch : Wff)
    (hyp_bi_a : Nominal.NPrf (syn_wb ph ps)) :
    Nominal.NPrf (syn_wb (.imp ch ph) (.imp ch ps)) :=
  by
  have p0000 := @g_a1i (syn_wb ph ps) ch hyp_bi_a
  have p0001 := @g_pm5_74i ch ph ps p0000
  exact p0001

@[expose]
noncomputable def g_bibi2i (ph : Wff) (ps : Wff) (ch : Wff)
    (hyp_bibi_a : Nominal.NPrf (syn_wb ph ps)) :
    Nominal.NPrf (syn_wb (syn_wb ch ph) (syn_wb ch ps)) :=
  by
  have p0000 := @g_id (syn_wb ch ph)
  have p0001 := @g_syl6bb (syn_wb ch ph) ch ph ps p0000 hyp_bibi_a
  have p0002 := @g_id (syn_wb ch ps)
  have p0003 := @g_syl6bbr (syn_wb ch ps) ch ps ph p0002 hyp_bibi_a
  have p0004 := @g_impbii (syn_wb ch ph) (syn_wb ch ps) p0001 p0003
  exact p0004

@[expose]
noncomputable def g_bibi1i (ph : Wff) (ps : Wff) (ch : Wff)
    (hyp_bibi_a : Nominal.NPrf (syn_wb ph ps)) :
    Nominal.NPrf (syn_wb (syn_wb ph ch) (syn_wb ps ch)) :=
  by
  have p0000 := @g_bicom ph ch
  have p0001 := @g_bibi2i ph ps ch hyp_bibi_a
  have p0002 := @g_bicom ch ps
  have p0003 :=
    @g_n_3bitri (syn_wb ph ch) (syn_wb ch ph) (syn_wb ch ps) (syn_wb ps ch) p0000 p0001
      p0002
  exact p0003

@[expose]
noncomputable def g_bibi12i (ph : Wff) (ps : Wff) (ch : Wff) (th : Wff)
    (hyp_bibi_a : Nominal.NPrf (syn_wb ph ps))
    (hyp_bibi12_2 : Nominal.NPrf (syn_wb ch th)) :
    Nominal.NPrf (syn_wb (syn_wb ph ch) (syn_wb ps th)) :=
  by
  have p0000 := @g_bibi2i ch th ph hyp_bibi12_2
  have p0001 := @g_bibi1i ph ps th hyp_bibi_a
  have p0002 := @g_bitri (syn_wb ph ch) (syn_wb ph th) (syn_wb ps th) p0000 p0001
  exact p0002

@[expose]
noncomputable def g_imbi2d (ph : Wff) (ps : Wff) (ch : Wff) (th : Wff)
    (hyp_imbid_1 : Nominal.NPrf (.imp ph (syn_wb ps ch))) :
    Nominal.NPrf (.imp ph (syn_wb (.imp th ps) (.imp th ch))) :=
  by
  have p0000 := @g_a1d ph (syn_wb ps ch) th hyp_imbid_1
  have p0001 := @g_pm5_74d ph th ps ch p0000
  exact p0001

@[expose]
noncomputable def g_imbi1d (ph : Wff) (ps : Wff) (ch : Wff) (th : Wff)
    (hyp_imbid_1 : Nominal.NPrf (.imp ph (syn_wb ps ch))) :
    Nominal.NPrf (.imp ph (syn_wb (.imp ps th) (.imp ch th))) :=
  by
  have p0000 := @g_biimprd ph ps ch hyp_imbid_1
  have p0001 := @g_imim1d ph ch ps th p0000
  have p0002 := @g_biimpd ph ps ch hyp_imbid_1
  have p0003 := @g_imim1d ph ps ch th p0002
  have p0004 := @g_impbid ph (.imp ps th) (.imp ch th) p0001 p0003
  exact p0004

@[expose]
noncomputable def g_bibi2d (ph : Wff) (ps : Wff) (ch : Wff) (th : Wff)
    (hyp_imbid_1 : Nominal.NPrf (.imp ph (syn_wb ps ch))) :
    Nominal.NPrf (.imp ph (syn_wb (syn_wb th ps) (syn_wb th ch))) :=
  by
  have p0000 := @g_pm5_74i ph ps ch hyp_imbid_1
  have p0001 := @g_bibi2i (.imp ph ps) (.imp ph ch) (.imp ph th) p0000
  have p0002 := @g_pm5_74 ph th ps
  have p0003 := @g_pm5_74 ph th ch
  have p0004 :=
    @g_n_3bitr4i (syn_wb (.imp ph th) (.imp ph ps)) (syn_wb (.imp ph th) (.imp ph ch))
      (.imp ph (syn_wb th ps)) (.imp ph (syn_wb th ch)) p0001 p0002 p0003
  have p0005 := @g_pm5_74ri ph (syn_wb th ps) (syn_wb th ch) p0004
  exact p0005

@[expose]
noncomputable def g_bibi1d (ph : Wff) (ps : Wff) (ch : Wff) (th : Wff)
    (hyp_imbid_1 : Nominal.NPrf (.imp ph (syn_wb ps ch))) :
    Nominal.NPrf (.imp ph (syn_wb (syn_wb ps th) (syn_wb ch th))) :=
  by
  have p0000 := @g_bibi2d ph ps ch th hyp_imbid_1
  have p0001 := @g_bicom ps th
  have p0002 := @g_bicom ch th
  have p0003 :=
    @g_n_3bitr4g ph (syn_wb th ps) (syn_wb th ch) (syn_wb ps th) (syn_wb ch th) p0000
      p0001 p0002
  exact p0003

@[expose]
noncomputable def g_imbi12d (ph : Wff) (ps : Wff) (ch : Wff) (th : Wff) (ta : Wff)
    (hyp_imbi12d_1 : Nominal.NPrf (.imp ph (syn_wb ps ch)))
    (hyp_imbi12d_2 : Nominal.NPrf (.imp ph (syn_wb th ta))) :
    Nominal.NPrf (.imp ph (syn_wb (.imp ps th) (.imp ch ta))) :=
  by
  have p0000 := @g_imbi1d ph ps ch th hyp_imbi12d_1
  have p0001 := @g_imbi2d ph th ta ch hyp_imbi12d_2
  have p0002 := @g_bitrd ph (.imp ps th) (.imp ch th) (.imp ch ta) p0000 p0001
  exact p0002

@[expose]
noncomputable def g_bibi12d (ph : Wff) (ps : Wff) (ch : Wff) (th : Wff) (ta : Wff)
    (hyp_imbi12d_1 : Nominal.NPrf (.imp ph (syn_wb ps ch)))
    (hyp_imbi12d_2 : Nominal.NPrf (.imp ph (syn_wb th ta))) :
    Nominal.NPrf (.imp ph (syn_wb (syn_wb ps th) (syn_wb ch ta))) :=
  by
  have p0000 := @g_bibi1d ph ps ch th hyp_imbi12d_1
  have p0001 := @g_bibi2d ph th ta ch hyp_imbi12d_2
  have p0002 := @g_bitrd ph (syn_wb ps th) (syn_wb ch th) (syn_wb ch ta) p0000 p0001
  exact p0002

@[expose]
noncomputable def g_imbi1 (ph : Wff) (ps : Wff) (ch : Wff) :
    Nominal.NPrf (.imp (syn_wb ph ps) (syn_wb (.imp ph ch) (.imp ps ch))) :=
  by
  have p0000 := @g_id (syn_wb ph ps)
  have p0001 := @g_imbi1d (syn_wb ph ps) ph ps ch p0000
  exact p0001

@[expose]
noncomputable def g_imbi1i (ph : Wff) (ps : Wff) (ch : Wff)
    (hyp_imbi1i_1 : Nominal.NPrf (syn_wb ph ps)) :
    Nominal.NPrf (syn_wb (.imp ph ch) (.imp ps ch)) :=
  by
  have p0000 := @g_imbi1 ph ps ch
  have p0001 := Nominal.mp hyp_imbi1i_1 p0000
  exact p0001

@[expose]
noncomputable def g_imbi12i (ph : Wff) (ps : Wff) (ch : Wff) (th : Wff)
    (hyp_imbi12i_1 : Nominal.NPrf (syn_wb ph ps))
    (hyp_imbi12i_2 : Nominal.NPrf (syn_wb ch th)) :
    Nominal.NPrf (syn_wb (.imp ph ch) (.imp ps th)) :=
  by
  have p0000 := @g_imbi2i ch th ph hyp_imbi12i_2
  have p0001 := @g_imbi1i ph ps th hyp_imbi12i_1
  have p0002 := @g_bitri (.imp ph ch) (.imp ph th) (.imp ps th) p0000 p0001
  exact p0002

@[expose]
noncomputable def g_bibi1 (ph : Wff) (ps : Wff) (ch : Wff) :
    Nominal.NPrf (.imp (syn_wb ph ps) (syn_wb (syn_wb ph ch) (syn_wb ps ch))) :=
  by
  have p0000 := @g_id (syn_wb ph ps)
  have p0001 := @g_bibi1d (syn_wb ph ps) ph ps ch p0000
  exact p0001

@[expose]
noncomputable def g_con2bi (ph : Wff) (ps : Wff) :
    Nominal.NPrf (syn_wb (syn_wb ph (.neg ps)) (syn_wb ps (.neg ph))) :=
  by
  have p0000 := @g_notbi ph (.neg ps)
  have p0001 := @g_notnot ps
  have p0002 := @g_bibi2i ps (.neg (.neg ps)) (.neg ph) p0001
  have p0003 := @g_bicom (.neg ph) ps
  have p0004 :=
    @g_n_3bitr2i (syn_wb ph (.neg ps)) (syn_wb (.neg ph) (.neg (.neg ps)))
      (syn_wb (.neg ph) ps) (syn_wb ps (.neg ph)) p0000 p0002 p0003
  exact p0004

@[expose]
noncomputable def g_con2bid (ph : Wff) (ps : Wff) (ch : Wff)
    (hyp_con2bid_1 : Nominal.NPrf (.imp ph (syn_wb ps (.neg ch)))) :
    Nominal.NPrf (.imp ph (syn_wb ch (.neg ps))) :=
  by
  have p0000 := @g_con2bi ch ps
  have p0001 :=
    @g_sylibr ph (syn_wb ps (.neg ch)) (syn_wb ch (.neg ps)) hyp_con2bid_1 p0000
  exact p0001

@[expose]
noncomputable def g_con1bid (ph : Wff) (ps : Wff) (ch : Wff)
    (hyp_con1bid_1 : Nominal.NPrf (.imp ph (syn_wb (.neg ps) ch))) :
    Nominal.NPrf (.imp ph (syn_wb (.neg ch) ps)) :=
  by
  have p0000 := @g_bicomd ph (.neg ps) ch hyp_con1bid_1
  have p0001 := @g_con2bid ph ch ps p0000
  have p0002 := @g_bicomd ph ps (.neg ch) p0001
  exact p0002

@[expose]
noncomputable def g_con1bii (ph : Wff) (ps : Wff)
    (hyp_con1bii_1 : Nominal.NPrf (syn_wb (.neg ph) ps)) :
    Nominal.NPrf (syn_wb (.neg ps) ph) :=
  by
  have p0000 := @g_notnot ph
  have p0001 := @g_xchbinx ph (.neg ph) ps p0000 hyp_con1bii_1
  have p0002 := @g_bicomi ph (.neg ps) p0001
  exact p0002

@[expose]
noncomputable def g_con2bii (ph : Wff) (ps : Wff)
    (hyp_con2bii_1 : Nominal.NPrf (syn_wb ph (.neg ps))) :
    Nominal.NPrf (syn_wb ps (.neg ph)) :=
  by
  have p0000 := @g_bicomi ph (.neg ps) hyp_con2bii_1
  have p0001 := @g_con1bii ps ph p0000
  have p0002 := @g_bicomi (.neg ph) ps p0001
  exact p0002

@[expose]
noncomputable def g_con2b (ph : Wff) (ps : Wff) :
    Nominal.NPrf (syn_wb (.imp ph (.neg ps)) (.imp ps (.neg ph))) :=
  by
  have p0000 := @g_con2 ph ps
  have p0001 := @g_con2 ps ph
  have p0002 := @g_impbii (.imp ph (.neg ps)) (.imp ps (.neg ph)) p0000 p0001
  exact p0002

@[expose]
noncomputable def g_biimt (ph : Wff) (ps : Wff) :
    Nominal.NPrf (.imp ph (syn_wb ps (.imp ph ps))) :=
  by
  have p0000 := Nominal.ax1 ps ph
  have p0001 := @g_pm2_27 ph ps
  have p0002 := @g_impbid2 ph ps (.imp ph ps) p0000 p0001
  exact p0002


end NFChoice.DirectNominalPrf.WPPReplay
