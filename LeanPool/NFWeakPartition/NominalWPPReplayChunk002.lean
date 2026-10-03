/-
Copyright (c) 2026 Elliot Glazer and NFNotWPP contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elliot Glazer and NFNotWPP contributors
-/

module

public import LeanPool.NFWeakPartition.NominalWPPReplayChunk001

/-! NF weak partition development: NominalWPPReplayChunk002. -/


public section


namespace NFChoice.DirectNominalPrf.WPPReplay

open scoped Fol
open NFChoice.Foundation
open NFChoice.SemanticCore
open NFChoice.ReplaySupport
open NFChoice.Compiler.CompactSourceSyntax

@[expose]
noncomputable def g_pm5_5 (ph : Wff) (ps : Wff) :
    Nominal.NPrf (.imp ph (syn_wb (.imp ph ps) ps)) :=
  by
  have p0000 := @g_biimt ph ps
  have p0001 := @g_bicomd ph ps (.imp ph ps) p0000
  exact p0001

@[expose]
noncomputable def g_a1bi (ph : Wff) (ps : Wff) (hyp_a1bi_1 : Nominal.NPrf ph) :
    Nominal.NPrf (syn_wb ps (.imp ph ps)) :=
  by
  have p0000 := @g_biimt ph ps
  have p0001 := Nominal.mp hyp_a1bi_1 p0000
  exact p0001

@[expose]
noncomputable def g_pm5_501 (ph : Wff) (ps : Wff) :
    Nominal.NPrf (.imp ph (syn_wb ps (syn_wb ph ps))) :=
  by
  have p0000 := @g_pm5_1im ph ps
  have p0001 := @g_bi1 ph ps
  have p0002 := @g_com12 (syn_wb ph ps) ph ps p0001
  have p0003 := @g_impbid ph ps (syn_wb ph ps) p0000 p0002
  exact p0003

@[expose]
noncomputable def g_ibibr (ph : Wff) (ps : Wff) :
    Nominal.NPrf (syn_wb (.imp ph ps) (.imp ph (syn_wb ps ph))) :=
  by
  have p0000 := @g_pm5_501 ph ps
  have p0001 := @g_bicom ph ps
  have p0002 := @g_syl6bb ph ps (syn_wb ph ps) (syn_wb ps ph) p0000 p0001
  have p0003 := @g_pm5_74i ph ps (syn_wb ps ph) p0002
  exact p0003

@[expose]
noncomputable def g_tbt (ph : Wff) (ps : Wff) (hyp_tbt_1 : Nominal.NPrf ph) :
    Nominal.NPrf (syn_wb ps (syn_wb ps ph)) :=
  by
  have p0000 := @g_ibibr ph ps
  have p0001 := @g_pm5_74ri ph ps (syn_wb ps ph) p0000
  have p0002 := Nominal.mp hyp_tbt_1 p0001
  exact p0002

@[expose]
noncomputable def g_nbn2 (ph : Wff) (ps : Wff) :
    Nominal.NPrf (.imp (.neg ph) (syn_wb (.neg ps) (syn_wb ph ps))) :=
  by
  have p0000 := @g_pm5_501 (.neg ph) (.neg ps)
  have p0001 := @g_notbi ph ps
  have p0002 :=
    @g_syl6bbr (.neg ph) (.neg ps) (syn_wb (.neg ph) (.neg ps)) (syn_wb ph ps) p0000 p0001
  exact p0002

@[expose]
noncomputable def g_bibif (ph : Wff) (ps : Wff) :
    Nominal.NPrf (.imp (.neg ps) (syn_wb (syn_wb ph ps) (.neg ph))) :=
  by
  have p0000 := @g_nbn2 ps ph
  have p0001 := @g_bicom ps ph
  have p0002 := @g_syl6rbb (.neg ps) (.neg ph) (syn_wb ps ph) (syn_wb ph ps) p0000 p0001
  exact p0002

@[expose]
noncomputable def g_nbn (ph : Wff) (ps : Wff) (hyp_nbn_1 : Nominal.NPrf (.neg ph)) :
    Nominal.NPrf (syn_wb (.neg ps) (syn_wb ps ph)) :=
  by
  have p0000 := @g_bibif ps ph
  have p0001 := Nominal.mp hyp_nbn_1 p0000
  have p0002 := @g_bicomi (syn_wb ps ph) (.neg ps) p0001
  exact p0002

@[expose]
noncomputable def g_pm5_21im (ph : Wff) (ps : Wff) :
    Nominal.NPrf (.imp (.neg ph) (.imp (.neg ps) (syn_wb ph ps))) :=
  by
  have p0000 := @g_nbn2 ph ps
  have p0001 := @g_biimpd (.neg ph) (.neg ps) (syn_wb ph ps) p0000
  exact p0001

@[expose]
noncomputable def g_n_2false (ph : Wff) (ps : Wff)
    (hyp_n_2false_1 : Nominal.NPrf (.neg ph)) (hyp_n_2false_2 : Nominal.NPrf (.neg ps)) :
    Nominal.NPrf (syn_wb ph ps) :=
  by
  have p0000 := @g_n_2th (.neg ph) (.neg ps) hyp_n_2false_1 hyp_n_2false_2
  have p0001 := @g_con4bii ph ps p0000
  exact p0001

@[expose]
noncomputable def g_n_2falsed (ph : Wff) (ps : Wff) (ch : Wff)
    (hyp_n_2falsed_1 : Nominal.NPrf (.imp ph (.neg ps)))
    (hyp_n_2falsed_2 : Nominal.NPrf (.imp ph (.neg ch))) :
    Nominal.NPrf (.imp ph (syn_wb ps ch)) :=
  by
  have p0000 := @g_pm2_21d ph ps ch hyp_n_2falsed_1
  have p0001 := @g_pm2_21d ph ch ps hyp_n_2falsed_2
  have p0002 := @g_impbid ph ps ch p0000 p0001
  exact p0002

@[expose]
noncomputable def g_pm5_21ni (ph : Wff) (ps : Wff) (ch : Wff)
    (hyp_pm5_21ni_1 : Nominal.NPrf (.imp ph ps))
    (hyp_pm5_21ni_2 : Nominal.NPrf (.imp ch ps)) :
    Nominal.NPrf (.imp (.neg ps) (syn_wb ph ch)) :=
  by
  have p0000 := @g_con3i ph ps hyp_pm5_21ni_1
  have p0001 := @g_con3i ch ps hyp_pm5_21ni_2
  have p0002 := @g_n_2falsed (.neg ps) ph ch p0000 p0001
  exact p0002

@[expose]
noncomputable def g_pm5_21nii (ph : Wff) (ps : Wff) (ch : Wff)
    (hyp_pm5_21ni_1 : Nominal.NPrf (.imp ph ps))
    (hyp_pm5_21ni_2 : Nominal.NPrf (.imp ch ps))
    (hyp_pm5_21nii_3 : Nominal.NPrf (.imp ps (syn_wb ph ch))) :
    Nominal.NPrf (syn_wb ph ch) :=
  by
  have p0000 := @g_pm5_21ni ph ps ch hyp_pm5_21ni_1 hyp_pm5_21ni_2
  have p0001 := @g_pm2_61i ps (syn_wb ph ch) hyp_pm5_21nii_3 p0000
  exact p0001

@[expose]
noncomputable def g_pm5_21ndd (ph : Wff) (ps : Wff) (ch : Wff) (th : Wff)
    (hyp_pm5_21ndd_1 : Nominal.NPrf (.imp ph (.imp ch ps)))
    (hyp_pm5_21ndd_2 : Nominal.NPrf (.imp ph (.imp th ps)))
    (hyp_pm5_21ndd_3 : Nominal.NPrf (.imp ph (.imp ps (syn_wb ch th)))) :
    Nominal.NPrf (.imp ph (syn_wb ch th)) :=
  by
  have p0000 := @g_con3d ph ch ps hyp_pm5_21ndd_1
  have p0001 := @g_con3d ph th ps hyp_pm5_21ndd_2
  have p0002 := @g_pm5_21im ch th
  have p0003 := @g_syl6c ph (.neg ps) (.neg ch) (.neg th) (syn_wb ch th) p0000 p0001 p0002
  have p0004 := @g_pm2_61d ph ps (syn_wb ch th) hyp_pm5_21ndd_3 p0003
  exact p0004

@[expose]
noncomputable def g_pm5_18 (ph : Wff) (ps : Wff) :
    Nominal.NPrf (syn_wb (syn_wb ph ps) (.neg (syn_wb ph (.neg ps)))) :=
  by
  have p0000 := @g_pm5_501 ph (.neg ps)
  have p0001 := @g_con1bid ph ps (syn_wb ph (.neg ps)) p0000
  have p0002 := @g_pm5_501 ph ps
  have p0003 := @g_bitr2d ph (.neg (syn_wb ph (.neg ps))) ps (syn_wb ph ps) p0001 p0002
  have p0004 := @g_nbn2 ph (.neg ps)
  have p0005 := @g_con1bid (.neg ph) (.neg ps) (syn_wb ph (.neg ps)) p0004
  have p0006 := @g_nbn2 ph ps
  have p0007 :=
    @g_bitr2d (.neg ph) (.neg (syn_wb ph (.neg ps))) (.neg ps) (syn_wb ph ps) p0005 p0006
  have p0008 :=
    @g_pm2_61i ph (syn_wb (syn_wb ph ps) (.neg (syn_wb ph (.neg ps)))) p0003 p0007
  exact p0008

@[expose]
noncomputable def g_pm5_19 (ph : Wff) : Nominal.NPrf (.neg (syn_wb ph (.neg ph))) :=
  by
  have p0000 := @g_biid ph
  have p0001 := @g_pm5_18 ph ph
  have p0002 := @g_mpbi (syn_wb ph ph) (.neg (syn_wb ph (.neg ph))) p0000 p0001
  exact p0002

@[expose]
noncomputable def g_bi2_04 (ph : Wff) (ps : Wff) (ch : Wff) :
    Nominal.NPrf (syn_wb (.imp ph (.imp ps ch)) (.imp ps (.imp ph ch))) :=
  by
  have p0000 := @g_pm2_04 ph ps ch
  have p0001 := @g_pm2_04 ps ph ch
  have p0002 := @g_impbii (.imp ph (.imp ps ch)) (.imp ps (.imp ph ch)) p0000 p0001
  exact p0002

@[expose]
noncomputable def g_pm4_64 (ph : Wff) (ps : Wff) :
    Nominal.NPrf (syn_wb (.imp (.neg ph) ps) (syn_wo ph ps)) :=
  by
  have p0000 := (Nominal.biimpRefl (syn_wo ph ps))
  have p0001 := @g_bicomi (syn_wo ph ps) (.imp (.neg ph) ps) p0000
  exact p0001

@[expose]
noncomputable def g_pm2_53 (ph : Wff) (ps : Wff) :
    Nominal.NPrf (.imp (syn_wo ph ps) (.imp (.neg ph) ps)) :=
  by
  have p0000 := (Nominal.biimpRefl (syn_wo ph ps))
  have p0001 := @g_biimpi (syn_wo ph ps) (.imp (.neg ph) ps) p0000
  exact p0001

@[expose]
noncomputable def g_pm2_54 (ph : Wff) (ps : Wff) :
    Nominal.NPrf (.imp (.imp (.neg ph) ps) (syn_wo ph ps)) :=
  by
  have p0000 := (Nominal.biimpRefl (syn_wo ph ps))
  have p0001 := @g_biimpri (syn_wo ph ps) (.imp (.neg ph) ps) p0000
  exact p0001

@[expose]
noncomputable def g_ori (ph : Wff) (ps : Wff) (hyp_ori_1 : Nominal.NPrf (syn_wo ph ps)) :
    Nominal.NPrf (.imp (.neg ph) ps) :=
  by
  have p0000 := (Nominal.biimpRefl (syn_wo ph ps))
  have p0001 := @g_mpbi (syn_wo ph ps) (.imp (.neg ph) ps) hyp_ori_1 p0000
  exact p0001

@[expose]
noncomputable def g_orri (ph : Wff) (ps : Wff)
    (hyp_orri_1 : Nominal.NPrf (.imp (.neg ph) ps)) : Nominal.NPrf (syn_wo ph ps) :=
  by
  have p0000 := (Nominal.biimpRefl (syn_wo ph ps))
  have p0001 := @g_mpbir (syn_wo ph ps) (.imp (.neg ph) ps) hyp_orri_1 p0000
  exact p0001

@[expose]
noncomputable def g_ord (ph : Wff) (ps : Wff) (ch : Wff)
    (hyp_ord_1 : Nominal.NPrf (.imp ph (syn_wo ps ch))) :
    Nominal.NPrf (.imp ph (.imp (.neg ps) ch)) :=
  by
  have p0000 := (Nominal.biimpRefl (syn_wo ps ch))
  have p0001 := @g_sylib ph (syn_wo ps ch) (.imp (.neg ps) ch) hyp_ord_1 p0000
  exact p0001

@[expose]
noncomputable def g_orrd (ph : Wff) (ps : Wff) (ch : Wff)
    (hyp_orrd_1 : Nominal.NPrf (.imp ph (.imp (.neg ps) ch))) :
    Nominal.NPrf (.imp ph (syn_wo ps ch)) :=
  by
  have p0000 := @g_pm2_54 ps ch
  have p0001 := @g_syl ph (.imp (.neg ps) ch) (syn_wo ps ch) hyp_orrd_1 p0000
  exact p0001

@[expose]
noncomputable def g_jaoi (ph : Wff) (ps : Wff) (ch : Wff)
    (hyp_jaoi_1 : Nominal.NPrf (.imp ph ps)) (hyp_jaoi_2 : Nominal.NPrf (.imp ch ps)) :
    Nominal.NPrf (.imp (syn_wo ph ch) ps) :=
  by
  have p0000 := @g_pm2_53 ph ch
  have p0001 := @g_syl6 (syn_wo ph ch) (.neg ph) ch ps p0000 hyp_jaoi_2
  have p0002 := @g_pm2_61d2 (syn_wo ph ch) ph ps p0001 hyp_jaoi_1
  exact p0002

@[expose]
noncomputable def g_jaod (ph : Wff) (ps : Wff) (ch : Wff) (th : Wff)
    (hyp_jaod_1 : Nominal.NPrf (.imp ph (.imp ps ch)))
    (hyp_jaod_2 : Nominal.NPrf (.imp ph (.imp th ch))) :
    Nominal.NPrf (.imp ph (.imp (syn_wo ps th) ch)) :=
  by
  have p0000 := @g_com12 ph ps ch hyp_jaod_1
  have p0001 := @g_com12 ph th ch hyp_jaod_2
  have p0002 := @g_jaoi ps (.imp ph ch) th p0000 p0001
  have p0003 := @g_com12 (syn_wo ps th) ph ch p0002
  exact p0003

@[expose]
noncomputable def g_mpjaod (ph : Wff) (ps : Wff) (ch : Wff) (th : Wff)
    (hyp_jaod_1 : Nominal.NPrf (.imp ph (.imp ps ch)))
    (hyp_jaod_2 : Nominal.NPrf (.imp ph (.imp th ch)))
    (hyp_jaod_3 : Nominal.NPrf (.imp ph (syn_wo ps th))) : Nominal.NPrf (.imp ph ch) :=
  by
  have p0000 := @g_jaod ph ps ch th hyp_jaod_1 hyp_jaod_2
  have p0001 := @g_mpd ph (syn_wo ps th) ch hyp_jaod_3 p0000
  exact p0001

@[expose]
noncomputable def g_orel1 (ph : Wff) (ps : Wff) :
    Nominal.NPrf (.imp (.neg ph) (.imp (syn_wo ph ps) ps)) :=
  by
  have p0000 := @g_pm2_53 ph ps
  have p0001 := @g_com12 (syn_wo ph ps) (.neg ph) ps p0000
  exact p0001

@[expose]
noncomputable def g_orel2 (ph : Wff) (ps : Wff) :
    Nominal.NPrf (.imp (.neg ph) (.imp (syn_wo ps ph) ps)) :=
  by
  have p0000 := @g_idd (.neg ph) ps
  have p0001 := @g_pm2_21 ph ps
  have p0002 := @g_jaod (.neg ph) ps ps ph p0000 p0001
  exact p0002

@[expose]
noncomputable def g_olc (ph : Wff) (ps : Wff) : Nominal.NPrf (.imp ph (syn_wo ps ph)) :=
  by
  have p0000 := Nominal.ax1 ph (.neg ps)
  have p0001 := @g_orrd ph ps ph p0000
  exact p0001

@[expose]
noncomputable def g_orc (ph : Wff) (ps : Wff) : Nominal.NPrf (.imp ph (syn_wo ph ps)) :=
  by
  have p0000 := @g_pm2_24 ph ps
  have p0001 := @g_orrd ph ph ps p0000
  exact p0001

@[expose]
noncomputable def g_pm1_4 (ph : Wff) (ps : Wff) :
    Nominal.NPrf (.imp (syn_wo ph ps) (syn_wo ps ph)) :=
  by
  have p0000 := @g_olc ph ps
  have p0001 := @g_orc ps ph
  have p0002 := @g_jaoi ph (syn_wo ps ph) ps p0000 p0001
  exact p0002

@[expose]
noncomputable def g_orcom (ph : Wff) (ps : Wff) :
    Nominal.NPrf (syn_wb (syn_wo ph ps) (syn_wo ps ph)) :=
  by
  have p0000 := @g_pm1_4 ph ps
  have p0001 := @g_pm1_4 ps ph
  have p0002 := @g_impbii (syn_wo ph ps) (syn_wo ps ph) p0000 p0001
  exact p0002

@[expose]
noncomputable def g_orcomd (ph : Wff) (ps : Wff) (ch : Wff)
    (hyp_orcomd_1 : Nominal.NPrf (.imp ph (syn_wo ps ch))) :
    Nominal.NPrf (.imp ph (syn_wo ch ps)) :=
  by
  have p0000 := @g_orcom ps ch
  have p0001 := @g_sylib ph (syn_wo ps ch) (syn_wo ch ps) hyp_orcomd_1 p0000
  exact p0001

@[expose]
noncomputable def g_orci (ph : Wff) (ps : Wff) (hyp_orci_1 : Nominal.NPrf ph) :
    Nominal.NPrf (syn_wo ph ps) :=
  by
  have p0000 := @g_pm2_24i ph ps hyp_orci_1
  have p0001 := @g_orri ph ps p0000
  exact p0001

@[expose]
noncomputable def g_orcd (ph : Wff) (ps : Wff) (ch : Wff)
    (hyp_orcd_1 : Nominal.NPrf (.imp ph ps)) : Nominal.NPrf (.imp ph (syn_wo ps ch)) :=
  by
  have p0000 := @g_orc ps ch
  have p0001 := @g_syl ph ps (syn_wo ps ch) hyp_orcd_1 p0000
  exact p0001

@[expose]
noncomputable def g_olcd (ph : Wff) (ps : Wff) (ch : Wff)
    (hyp_orcd_1 : Nominal.NPrf (.imp ph ps)) : Nominal.NPrf (.imp ph (syn_wo ch ps)) :=
  by
  have p0000 := @g_orcd ph ps ch hyp_orcd_1
  have p0001 := @g_orcomd ph ps ch p0000
  exact p0001

@[expose]
noncomputable def g_pm2_07 (ph : Wff) : Nominal.NPrf (.imp ph (syn_wo ph ph)) :=
  by
  have p0000 := @g_olc ph ph
  exact p0000

@[expose]
noncomputable def g_pm2_67_2 (ph : Wff) (ps : Wff) (ch : Wff) :
    Nominal.NPrf (.imp (.imp (syn_wo ph ch) ps) (.imp ph ps)) :=
  by
  have p0000 := @g_orc ph ch
  have p0001 := @g_imim1i ph (syn_wo ph ch) ps p0000
  exact p0001

@[expose]
noncomputable def g_biorf (ph : Wff) (ps : Wff) :
    Nominal.NPrf (.imp (.neg ph) (syn_wb ps (syn_wo ph ps))) :=
  by
  have p0000 := @g_olc ps ph
  have p0001 := @g_orel1 ph ps
  have p0002 := @g_impbid2 (.neg ph) ps (syn_wo ph ps) p0000 p0001
  exact p0002

@[expose]
noncomputable def g_biorfi (ph : Wff) (ps : Wff) (hyp_biorfi_1 : Nominal.NPrf (.neg ph)) :
    Nominal.NPrf (syn_wb ps (syn_wo ps ph)) :=
  by
  have p0000 := @g_orc ps ph
  have p0001 := @g_orel2 ph ps
  have p0002 := @g_impbid2 (.neg ph) ps (syn_wo ps ph) p0000 p0001
  have p0003 := Nominal.mp hyp_biorfi_1 p0002
  exact p0003

@[expose]
noncomputable def g_pm2_621 (ph : Wff) (ps : Wff) :
    Nominal.NPrf (.imp (.imp ph ps) (.imp (syn_wo ph ps) ps)) :=
  by
  have p0000 := @g_id (.imp ph ps)
  have p0001 := @g_idd (.imp ph ps) ps
  have p0002 := @g_jaod (.imp ph ps) ph ps ps p0000 p0001
  exact p0002

@[expose]
noncomputable def g_imor (ph : Wff) (ps : Wff) :
    Nominal.NPrf (syn_wb (.imp ph ps) (syn_wo (.neg ph) ps)) :=
  by
  have p0000 := @g_notnot ph
  have p0001 := @g_imbi1i ph (.neg (.neg ph)) ps p0000
  have p0002 := (Nominal.biimpRefl (syn_wo (.neg ph) ps))
  have p0003 :=
    @g_bitr4i (.imp ph ps) (.imp (.neg (.neg ph)) ps) (syn_wo (.neg ph) ps) p0001 p0002
  exact p0003

@[expose]
noncomputable def g_exmid (ph : Wff) : Nominal.NPrf (syn_wo ph (.neg ph)) :=
  by
  have p0000 := @g_id (.neg ph)
  have p0001 := @g_orri ph (.neg ph) p0000
  exact p0001

@[expose]
noncomputable def g_pm4_62 (ph : Wff) (ps : Wff) :
    Nominal.NPrf (syn_wb (.imp ph (.neg ps)) (syn_wo (.neg ph) (.neg ps))) :=
  by
  have p0000 := @g_imor ph (.neg ps)
  exact p0000

@[expose]
noncomputable def g_imnan (ph : Wff) (ps : Wff) :
    Nominal.NPrf (syn_wb (.imp ph (.neg ps)) (.neg (syn_wa ph ps))) :=
  by
  have p0000 := (Nominal.biimpRefl (syn_wa ph ps))
  have p0001 := @g_con2bii (syn_wa ph ps) (.imp ph (.neg ps)) p0000
  exact p0001

@[expose]
noncomputable def g_iman (ph : Wff) (ps : Wff) :
    Nominal.NPrf (syn_wb (.imp ph ps) (.neg (syn_wa ph (.neg ps)))) :=
  by
  have p0000 := @g_notnot ps
  have p0001 := @g_imbi2i ps (.neg (.neg ps)) ph p0000
  have p0002 := @g_imnan ph (.neg ps)
  have p0003 :=
    @g_bitri (.imp ph ps) (.imp ph (.neg (.neg ps))) (.neg (syn_wa ph (.neg ps))) p0001
      p0002
  exact p0003

@[expose]
noncomputable def g_annim (ph : Wff) (ps : Wff) :
    Nominal.NPrf (syn_wb (syn_wa ph (.neg ps)) (.neg (.imp ph ps))) :=
  by
  have p0000 := @g_iman ph ps
  have p0001 := @g_con2bii (.imp ph ps) (syn_wa ph (.neg ps)) p0000
  exact p0001

@[expose]
noncomputable def g_pm4_61 (ph : Wff) (ps : Wff) :
    Nominal.NPrf (syn_wb (.neg (.imp ph ps)) (syn_wa ph (.neg ps))) :=
  by
  have p0000 := @g_annim ph ps
  have p0001 := @g_bicomi (syn_wa ph (.neg ps)) (.neg (.imp ph ps)) p0000
  exact p0001

@[expose]
noncomputable def g_pm4_65 (ph : Wff) (ps : Wff) :
    Nominal.NPrf (syn_wb (.neg (.imp (.neg ph) ps)) (syn_wa (.neg ph) (.neg ps))) :=
  by
  have p0000 := @g_pm4_61 (.neg ph) ps
  exact p0000

@[expose]
noncomputable def g_imp (ph : Wff) (ps : Wff) (ch : Wff)
    (hyp_imp_1 : Nominal.NPrf (.imp ph (.imp ps ch))) :
    Nominal.NPrf (.imp (syn_wa ph ps) ch) :=
  by
  have p0000 := (Nominal.biimpRefl (syn_wa ph ps))
  have p0001 := @g_impi ph ps ch hyp_imp_1
  have p0002 := @g_sylbi (syn_wa ph ps) (.neg (.imp ph (.neg ps))) ch p0000 p0001
  exact p0002

@[expose]
noncomputable def g_impcom (ph : Wff) (ps : Wff) (ch : Wff)
    (hyp_imp_1 : Nominal.NPrf (.imp ph (.imp ps ch))) :
    Nominal.NPrf (.imp (syn_wa ps ph) ch) :=
  by
  have p0000 := @g_com12 ph ps ch hyp_imp_1
  have p0001 := @g_imp ps ph ch p0000
  exact p0001

@[expose]
noncomputable def g_imp3a (ph : Wff) (ps : Wff) (ch : Wff) (th : Wff)
    (hyp_imp3_1 : Nominal.NPrf (.imp ph (.imp ps (.imp ch th)))) :
    Nominal.NPrf (.imp ph (.imp (syn_wa ps ch) th)) :=
  by
  have p0000 := @g_com3l ph ps ch th hyp_imp3_1
  have p0001 := @g_imp ps ch (.imp ph th) p0000
  have p0002 := @g_com12 (syn_wa ps ch) ph th p0001
  exact p0002

@[expose]
noncomputable def g_imp31 (ph : Wff) (ps : Wff) (ch : Wff) (th : Wff)
    (hyp_imp3_1 : Nominal.NPrf (.imp ph (.imp ps (.imp ch th)))) :
    Nominal.NPrf (.imp (syn_wa (syn_wa ph ps) ch) th) :=
  by
  have p0000 := @g_imp ph ps (.imp ch th) hyp_imp3_1
  have p0001 := @g_imp (syn_wa ph ps) ch th p0000
  exact p0001

@[expose]
noncomputable def g_imp32 (ph : Wff) (ps : Wff) (ch : Wff) (th : Wff)
    (hyp_imp3_1 : Nominal.NPrf (.imp ph (.imp ps (.imp ch th)))) :
    Nominal.NPrf (.imp (syn_wa ph (syn_wa ps ch)) th) :=
  by
  have p0000 := @g_imp3a ph ps ch th hyp_imp3_1
  have p0001 := @g_imp ph (syn_wa ps ch) th p0000
  exact p0001

@[expose]
noncomputable def g_ex (ph : Wff) (ps : Wff) (ch : Wff)
    (hyp_exp_1 : Nominal.NPrf (.imp (syn_wa ph ps) ch)) :
    Nominal.NPrf (.imp ph (.imp ps ch)) :=
  by
  have p0000 := (Nominal.biimpRefl (syn_wa ph ps))
  have p0001 := @g_sylbir (.neg (.imp ph (.neg ps))) (syn_wa ph ps) ch p0000 hyp_exp_1
  have p0002 := @g_expi ph ps ch p0001
  exact p0002

@[expose]
noncomputable def g_expcom (ph : Wff) (ps : Wff) (ch : Wff)
    (hyp_exp_1 : Nominal.NPrf (.imp (syn_wa ph ps) ch)) :
    Nominal.NPrf (.imp ps (.imp ph ch)) :=
  by
  have p0000 := @g_ex ph ps ch hyp_exp_1
  have p0001 := @g_com12 ph ps ch p0000
  exact p0001

@[expose]
noncomputable def g_exp3a (ph : Wff) (ps : Wff) (ch : Wff) (th : Wff)
    (hyp_exp3a_1 : Nominal.NPrf (.imp ph (.imp (syn_wa ps ch) th))) :
    Nominal.NPrf (.imp ph (.imp ps (.imp ch th))) :=
  by
  have p0000 := @g_com12 ph (syn_wa ps ch) th hyp_exp3a_1
  have p0001 := @g_ex ps ch (.imp ph th) p0000
  have p0002 := @g_com3r ps ch ph th p0001
  exact p0002

@[expose]
noncomputable def g_expdimp (ph : Wff) (ps : Wff) (ch : Wff) (th : Wff)
    (hyp_exp3a_1 : Nominal.NPrf (.imp ph (.imp (syn_wa ps ch) th))) :
    Nominal.NPrf (.imp (syn_wa ph ps) (.imp ch th)) :=
  by
  have p0000 := @g_exp3a ph ps ch th hyp_exp3a_1
  have p0001 := @g_imp ph ps (.imp ch th) p0000
  exact p0001

@[expose]
noncomputable def g_impancom (ph : Wff) (ps : Wff) (ch : Wff) (th : Wff)
    (hyp_impancom_1 : Nominal.NPrf (.imp (syn_wa ph ps) (.imp ch th))) :
    Nominal.NPrf (.imp (syn_wa ph ch) (.imp ps th)) :=
  by
  have p0000 := @g_ex ph ps (.imp ch th) hyp_impancom_1
  have p0001 := @g_com23 ph ps ch th p0000
  have p0002 := @g_imp ph ch (.imp ps th) p0001
  exact p0002

@[expose]
noncomputable def g_con3and (ph : Wff) (ps : Wff) (ch : Wff)
    (hyp_con3and_1 : Nominal.NPrf (.imp ph (.imp ps ch))) :
    Nominal.NPrf (.imp (syn_wa ph (.neg ch)) (.neg ps)) :=
  by
  have p0000 := @g_con3d ph ps ch hyp_con3and_1
  have p0001 := @g_imp ph (.neg ch) (.neg ps) p0000
  exact p0001

@[expose]
noncomputable def g_pm2_01da (ph : Wff) (ps : Wff)
    (hyp_pm2_01da_1 : Nominal.NPrf (.imp (syn_wa ph ps) (.neg ps))) :
    Nominal.NPrf (.imp ph (.neg ps)) :=
  by
  have p0000 := @g_ex ph ps (.neg ps) hyp_pm2_01da_1
  have p0001 := @g_pm2_01d ph ps p0000
  exact p0001

@[expose]
noncomputable def g_pm3_3 (ph : Wff) (ps : Wff) (ch : Wff) :
    Nominal.NPrf (.imp (.imp (syn_wa ph ps) ch) (.imp ph (.imp ps ch))) :=
  by
  have p0000 := @g_id (.imp (syn_wa ph ps) ch)
  have p0001 := @g_exp3a (.imp (syn_wa ph ps) ch) ph ps ch p0000
  exact p0001

@[expose]
noncomputable def g_pm3_31 (ph : Wff) (ps : Wff) (ch : Wff) :
    Nominal.NPrf (.imp (.imp ph (.imp ps ch)) (.imp (syn_wa ph ps) ch)) :=
  by
  have p0000 := @g_id (.imp ph (.imp ps ch))
  have p0001 := @g_imp3a (.imp ph (.imp ps ch)) ph ps ch p0000
  exact p0001

@[expose]
noncomputable def g_impexp (ph : Wff) (ps : Wff) (ch : Wff) :
    Nominal.NPrf (syn_wb (.imp (syn_wa ph ps) ch) (.imp ph (.imp ps ch))) :=
  by
  have p0000 := @g_pm3_3 ph ps ch
  have p0001 := @g_pm3_31 ph ps ch
  have p0002 := @g_impbii (.imp (syn_wa ph ps) ch) (.imp ph (.imp ps ch)) p0000 p0001
  exact p0002

@[expose]
noncomputable def g_pm3_2 (ph : Wff) (ps : Wff) :
    Nominal.NPrf (.imp ph (.imp ps (syn_wa ph ps))) :=
  by
  have p0000 := @g_id (syn_wa ph ps)
  have p0001 := @g_ex ph ps (syn_wa ph ps) p0000
  exact p0001

@[expose]
noncomputable def g_pm3_21 (ph : Wff) (ps : Wff) :
    Nominal.NPrf (.imp ph (.imp ps (syn_wa ps ph))) :=
  by
  have p0000 := @g_pm3_2 ps ph
  have p0001 := @g_com12 ps ph (syn_wa ps ph) p0000
  exact p0001

@[expose]
noncomputable def g_pm3_22 (ph : Wff) (ps : Wff) :
    Nominal.NPrf (.imp (syn_wa ph ps) (syn_wa ps ph)) :=
  by
  have p0000 := @g_pm3_21 ph ps
  have p0001 := @g_imp ph ps (syn_wa ps ph) p0000
  exact p0001

@[expose]
noncomputable def g_ancom (ph : Wff) (ps : Wff) :
    Nominal.NPrf (syn_wb (syn_wa ph ps) (syn_wa ps ph)) :=
  by
  have p0000 := @g_pm3_22 ph ps
  have p0001 := @g_pm3_22 ps ph
  have p0002 := @g_impbii (syn_wa ph ps) (syn_wa ps ph) p0000 p0001
  exact p0002

@[expose]
noncomputable def g_ancomd (ph : Wff) (ps : Wff) (ch : Wff)
    (hyp_ancomd_1 : Nominal.NPrf (.imp ph (syn_wa ps ch))) :
    Nominal.NPrf (.imp ph (syn_wa ch ps)) :=
  by
  have p0000 := @g_ancom ps ch
  have p0001 := @g_sylib ph (syn_wa ps ch) (syn_wa ch ps) hyp_ancomd_1 p0000
  exact p0001

@[expose]
noncomputable def g_ancoms (ph : Wff) (ps : Wff) (ch : Wff)
    (hyp_ancoms_1 : Nominal.NPrf (.imp (syn_wa ph ps) ch)) :
    Nominal.NPrf (.imp (syn_wa ps ph) ch) :=
  by
  have p0000 := @g_expcom ph ps ch hyp_ancoms_1
  have p0001 := @g_imp ps ph ch p0000
  exact p0001

@[expose]
noncomputable def g_ancomsd (ph : Wff) (ps : Wff) (ch : Wff) (th : Wff)
    (hyp_ancomsd_1 : Nominal.NPrf (.imp ph (.imp (syn_wa ps ch) th))) :
    Nominal.NPrf (.imp ph (.imp (syn_wa ch ps) th)) :=
  by
  have p0000 := @g_ancom ch ps
  have p0001 := @g_syl5bi (syn_wa ch ps) (syn_wa ps ch) ph th p0000 hyp_ancomsd_1
  exact p0001

@[expose]
noncomputable def g_pm3_2i (ph : Wff) (ps : Wff) (hyp_pm3_2i_1 : Nominal.NPrf ph)
    (hyp_pm3_2i_2 : Nominal.NPrf ps) : Nominal.NPrf (syn_wa ph ps) :=
  by
  have p0000 := @g_pm3_2 ph ps
  have p0001 := @g_mp2 ph ps (syn_wa ph ps) hyp_pm3_2i_1 hyp_pm3_2i_2 p0000
  exact p0001

@[expose]
noncomputable def g_pm3_43i (ph : Wff) (ps : Wff) (ch : Wff) :
    Nominal.NPrf (.imp (.imp ph ps) (.imp (.imp ph ch) (.imp ph (syn_wa ps ch)))) :=
  by
  have p0000 := @g_pm3_2 ps ch
  have p0001 := @g_imim3i ps ch (syn_wa ps ch) ph p0000
  exact p0001

@[expose]
noncomputable def g_simpl (ph : Wff) (ps : Wff) : Nominal.NPrf (.imp (syn_wa ph ps) ph) :=
  by
  have p0000 := Nominal.ax1 ph ps
  have p0001 := @g_imp ph ps ph p0000
  exact p0001

@[expose]
noncomputable def g_simpli (ph : Wff) (ps : Wff)
    (hyp_simpli_1 : Nominal.NPrf (syn_wa ph ps)) : Nominal.NPrf ph :=
  by
  have p0000 := @g_simpl ph ps
  have p0001 := Nominal.mp hyp_simpli_1 p0000
  exact p0001

@[expose]
noncomputable def g_simpld (ph : Wff) (ps : Wff) (ch : Wff)
    (hyp_simpld_1 : Nominal.NPrf (.imp ph (syn_wa ps ch))) : Nominal.NPrf (.imp ph ps) :=
  by
  have p0000 := @g_simpl ps ch
  have p0001 := @g_syl ph (syn_wa ps ch) ps hyp_simpld_1 p0000
  exact p0001

@[expose]
noncomputable def g_simplbi (ph : Wff) (ps : Wff) (ch : Wff)
    (hyp_simplbi_1 : Nominal.NPrf (syn_wb ph (syn_wa ps ch))) :
    Nominal.NPrf (.imp ph ps) :=
  by
  have p0000 := @g_biimpi ph (syn_wa ps ch) hyp_simplbi_1
  have p0001 := @g_simpld ph ps ch p0000
  exact p0001

@[expose]
noncomputable def g_simpr (ph : Wff) (ps : Wff) : Nominal.NPrf (.imp (syn_wa ph ps) ps) :=
  by
  have p0000 := @g_idd ph ps
  have p0001 := @g_imp ph ps ps p0000
  exact p0001

@[expose]
noncomputable def g_simpri (ph : Wff) (ps : Wff)
    (hyp_simpri_1 : Nominal.NPrf (syn_wa ph ps)) : Nominal.NPrf ps :=
  by
  have p0000 := @g_simpr ph ps
  have p0001 := Nominal.mp hyp_simpri_1 p0000
  exact p0001

@[expose]
noncomputable def g_simprd (ph : Wff) (ps : Wff) (ch : Wff)
    (hyp_simprd_1 : Nominal.NPrf (.imp ph (syn_wa ps ch))) : Nominal.NPrf (.imp ph ch) :=
  by
  have p0000 := @g_ancomd ph ps ch hyp_simprd_1
  have p0001 := @g_simpld ph ch ps p0000
  exact p0001

@[expose]
noncomputable def g_simprbi (ph : Wff) (ps : Wff) (ch : Wff)
    (hyp_simprbi_1 : Nominal.NPrf (syn_wb ph (syn_wa ps ch))) :
    Nominal.NPrf (.imp ph ch) :=
  by
  have p0000 := @g_biimpi ph (syn_wa ps ch) hyp_simprbi_1
  have p0001 := @g_simprd ph ps ch p0000
  exact p0001

@[expose]
noncomputable def g_adantr (ph : Wff) (ps : Wff) (ch : Wff)
    (hyp_adantr_1 : Nominal.NPrf (.imp ph ps)) : Nominal.NPrf (.imp (syn_wa ph ch) ps) :=
  by
  have p0000 := @g_a1d ph ps ch hyp_adantr_1
  have p0001 := @g_imp ph ch ps p0000
  exact p0001

@[expose]
noncomputable def g_adantl (ph : Wff) (ps : Wff) (ch : Wff)
    (hyp_adantl_1 : Nominal.NPrf (.imp ph ps)) : Nominal.NPrf (.imp (syn_wa ch ph) ps) :=
  by
  have p0000 := @g_adantr ph ps ch hyp_adantl_1
  have p0001 := @g_ancoms ph ch ps p0000
  exact p0001

@[expose]
noncomputable def g_adantld (ph : Wff) (ps : Wff) (ch : Wff) (th : Wff)
    (hyp_adantld_1 : Nominal.NPrf (.imp ph (.imp ps ch))) :
    Nominal.NPrf (.imp ph (.imp (syn_wa th ps) ch)) :=
  by
  have p0000 := @g_simpr th ps
  have p0001 := @g_syl5 (syn_wa th ps) ps ph ch p0000 hyp_adantld_1
  exact p0001

@[expose]
noncomputable def g_adantrd (ph : Wff) (ps : Wff) (ch : Wff) (th : Wff)
    (hyp_adantrd_1 : Nominal.NPrf (.imp ph (.imp ps ch))) :
    Nominal.NPrf (.imp ph (.imp (syn_wa ps th) ch)) :=
  by
  have p0000 := @g_simpl ps th
  have p0001 := @g_syl5 (syn_wa ps th) ps ph ch p0000 hyp_adantrd_1
  exact p0001

@[expose]
noncomputable def g_mpan9 (ph : Wff) (ps : Wff) (ch : Wff) (th : Wff)
    (hyp_mpan9_1 : Nominal.NPrf (.imp ph ps))
    (hyp_mpan9_2 : Nominal.NPrf (.imp ch (.imp ps th))) :
    Nominal.NPrf (.imp (syn_wa ph ch) th) :=
  by
  have p0000 := @g_syl5 ph ps ch th hyp_mpan9_1 hyp_mpan9_2
  have p0001 := @g_impcom ch ph th p0000
  exact p0001

@[expose]
noncomputable def g_syldan (ph : Wff) (ps : Wff) (ch : Wff) (th : Wff)
    (hyp_syldan_1 : Nominal.NPrf (.imp (syn_wa ph ps) ch))
    (hyp_syldan_2 : Nominal.NPrf (.imp (syn_wa ph ch) th)) :
    Nominal.NPrf (.imp (syn_wa ph ps) th) :=
  by
  have p0000 := @g_expcom ph ch th hyp_syldan_2
  have p0001 := @g_adantrd ch ph th ps p0000
  have p0002 := @g_mpcom ch (syn_wa ph ps) th hyp_syldan_1 p0001
  exact p0002

@[expose]
noncomputable def g_sylan (ph : Wff) (ps : Wff) (ch : Wff) (th : Wff)
    (hyp_sylan_1 : Nominal.NPrf (.imp ph ps))
    (hyp_sylan_2 : Nominal.NPrf (.imp (syn_wa ps ch) th)) :
    Nominal.NPrf (.imp (syn_wa ph ch) th) :=
  by
  have p0000 := @g_expcom ps ch th hyp_sylan_2
  have p0001 := @g_mpan9 ph ps ch th hyp_sylan_1 p0000
  exact p0001

@[expose]
noncomputable def g_sylanb (ph : Wff) (ps : Wff) (ch : Wff) (th : Wff)
    (hyp_sylanb_1 : Nominal.NPrf (syn_wb ph ps))
    (hyp_sylanb_2 : Nominal.NPrf (.imp (syn_wa ps ch) th)) :
    Nominal.NPrf (.imp (syn_wa ph ch) th) :=
  by
  have p0000 := @g_biimpi ph ps hyp_sylanb_1
  have p0001 := @g_sylan ph ps ch th p0000 hyp_sylanb_2
  exact p0001

@[expose]
noncomputable def g_sylanbr (ph : Wff) (ps : Wff) (ch : Wff) (th : Wff)
    (hyp_sylanbr_1 : Nominal.NPrf (syn_wb ps ph))
    (hyp_sylanbr_2 : Nominal.NPrf (.imp (syn_wa ps ch) th)) :
    Nominal.NPrf (.imp (syn_wa ph ch) th) :=
  by
  have p0000 := @g_biimpri ps ph hyp_sylanbr_1
  have p0001 := @g_sylan ph ps ch th p0000 hyp_sylanbr_2
  exact p0001

@[expose]
noncomputable def g_sylan2 (ph : Wff) (ps : Wff) (ch : Wff) (th : Wff)
    (hyp_sylan2_1 : Nominal.NPrf (.imp ph ch))
    (hyp_sylan2_2 : Nominal.NPrf (.imp (syn_wa ps ch) th)) :
    Nominal.NPrf (.imp (syn_wa ps ph) th) :=
  by
  have p0000 := @g_adantl ph ch ps hyp_sylan2_1
  have p0001 := @g_syldan ps ph ch th p0000 hyp_sylan2_2
  exact p0001

@[expose]
noncomputable def g_sylan2b (ph : Wff) (ps : Wff) (ch : Wff) (th : Wff)
    (hyp_sylan2b_1 : Nominal.NPrf (syn_wb ph ch))
    (hyp_sylan2b_2 : Nominal.NPrf (.imp (syn_wa ps ch) th)) :
    Nominal.NPrf (.imp (syn_wa ps ph) th) :=
  by
  have p0000 := @g_biimpi ph ch hyp_sylan2b_1
  have p0001 := @g_sylan2 ph ps ch th p0000 hyp_sylan2b_2
  exact p0001

@[expose]
noncomputable def g_sylan2br (ph : Wff) (ps : Wff) (ch : Wff) (th : Wff)
    (hyp_sylan2br_1 : Nominal.NPrf (syn_wb ch ph))
    (hyp_sylan2br_2 : Nominal.NPrf (.imp (syn_wa ps ch) th)) :
    Nominal.NPrf (.imp (syn_wa ps ph) th) :=
  by
  have p0000 := @g_biimpri ch ph hyp_sylan2br_1
  have p0001 := @g_sylan2 ph ps ch th p0000 hyp_sylan2br_2
  exact p0001

@[expose]
noncomputable def g_syl2an (ph : Wff) (ps : Wff) (ch : Wff) (th : Wff) (ta : Wff)
    (hyp_syl2an_1 : Nominal.NPrf (.imp ph ps)) (hyp_syl2an_2 : Nominal.NPrf (.imp ta ch))
    (hyp_syl2an_3 : Nominal.NPrf (.imp (syn_wa ps ch) th)) :
    Nominal.NPrf (.imp (syn_wa ph ta) th) :=
  by
  have p0000 := @g_sylan ph ps ch th hyp_syl2an_1 hyp_syl2an_3
  have p0001 := @g_sylan2 ta ph ch th hyp_syl2an_2 p0000
  exact p0001

@[expose]
noncomputable def g_syl2anr (ph : Wff) (ps : Wff) (ch : Wff) (th : Wff) (ta : Wff)
    (hyp_syl2an_1 : Nominal.NPrf (.imp ph ps)) (hyp_syl2an_2 : Nominal.NPrf (.imp ta ch))
    (hyp_syl2an_3 : Nominal.NPrf (.imp (syn_wa ps ch) th)) :
    Nominal.NPrf (.imp (syn_wa ta ph) th) :=
  by
  have p0000 := @g_syl2an ph ps ch th ta hyp_syl2an_1 hyp_syl2an_2 hyp_syl2an_3
  have p0001 := @g_ancoms ph ta th p0000
  exact p0001

@[expose]
noncomputable def g_syl2anb (ph : Wff) (ps : Wff) (ch : Wff) (th : Wff) (ta : Wff)
    (hyp_syl2anb_1 : Nominal.NPrf (syn_wb ph ps))
    (hyp_syl2anb_2 : Nominal.NPrf (syn_wb ta ch))
    (hyp_syl2anb_3 : Nominal.NPrf (.imp (syn_wa ps ch) th)) :
    Nominal.NPrf (.imp (syn_wa ph ta) th) :=
  by
  have p0000 := @g_sylanb ph ps ch th hyp_syl2anb_1 hyp_syl2anb_3
  have p0001 := @g_sylan2b ta ph ch th hyp_syl2anb_2 p0000
  exact p0001

@[expose]
noncomputable def g_syland (ph : Wff) (ps : Wff) (ch : Wff) (th : Wff) (ta : Wff)
    (hyp_syland_1 : Nominal.NPrf (.imp ph (.imp ps ch)))
    (hyp_syland_2 : Nominal.NPrf (.imp ph (.imp (syn_wa ch th) ta))) :
    Nominal.NPrf (.imp ph (.imp (syn_wa ps th) ta)) :=
  by
  have p0000 := @g_exp3a ph ch th ta hyp_syland_2
  have p0001 := @g_syld ph ps ch (.imp th ta) hyp_syland_1 p0000
  have p0002 := @g_imp3a ph ps th ta p0001
  exact p0002

@[expose]
noncomputable def g_sylan2d (ph : Wff) (ps : Wff) (ch : Wff) (th : Wff) (ta : Wff)
    (hyp_sylan2d_1 : Nominal.NPrf (.imp ph (.imp ps ch)))
    (hyp_sylan2d_2 : Nominal.NPrf (.imp ph (.imp (syn_wa th ch) ta))) :
    Nominal.NPrf (.imp ph (.imp (syn_wa th ps) ta)) :=
  by
  have p0000 := @g_ancomsd ph th ch ta hyp_sylan2d_2
  have p0001 := @g_syland ph ps ch th ta hyp_sylan2d_1 p0000
  have p0002 := @g_ancomsd ph ps th ta p0001
  exact p0002

@[expose]
noncomputable def g_syl2and (ph : Wff) (ps : Wff) (ch : Wff) (th : Wff) (ta : Wff)
    (et : Wff) (hyp_syl2and_1 : Nominal.NPrf (.imp ph (.imp ps ch)))
    (hyp_syl2and_2 : Nominal.NPrf (.imp ph (.imp th ta)))
    (hyp_syl2and_3 : Nominal.NPrf (.imp ph (.imp (syn_wa ch ta) et))) :
    Nominal.NPrf (.imp ph (.imp (syn_wa ps th) et)) :=
  by
  have p0000 := @g_sylan2d ph th ta ch et hyp_syl2and_2 hyp_syl2and_3
  have p0001 := @g_syland ph ps ch th et hyp_syl2and_1 p0000
  exact p0001

@[expose]
noncomputable def g_biimpa (ph : Wff) (ps : Wff) (ch : Wff)
    (hyp_biimpa_1 : Nominal.NPrf (.imp ph (syn_wb ps ch))) :
    Nominal.NPrf (.imp (syn_wa ph ps) ch) :=
  by
  have p0000 := @g_biimpd ph ps ch hyp_biimpa_1
  have p0001 := @g_imp ph ps ch p0000
  exact p0001

@[expose]
noncomputable def g_biimpar (ph : Wff) (ps : Wff) (ch : Wff)
    (hyp_biimpa_1 : Nominal.NPrf (.imp ph (syn_wb ps ch))) :
    Nominal.NPrf (.imp (syn_wa ph ch) ps) :=
  by
  have p0000 := @g_biimprd ph ps ch hyp_biimpa_1
  have p0001 := @g_imp ph ch ps p0000
  exact p0001

@[expose]
noncomputable def g_biimpac (ph : Wff) (ps : Wff) (ch : Wff)
    (hyp_biimpa_1 : Nominal.NPrf (.imp ph (syn_wb ps ch))) :
    Nominal.NPrf (.imp (syn_wa ps ph) ch) :=
  by
  have p0000 := @g_biimpcd ph ps ch hyp_biimpa_1
  have p0001 := @g_imp ps ph ch p0000
  exact p0001

@[expose]
noncomputable def g_biimparc (ph : Wff) (ps : Wff) (ch : Wff)
    (hyp_biimpa_1 : Nominal.NPrf (.imp ph (syn_wb ps ch))) :
    Nominal.NPrf (.imp (syn_wa ch ph) ps) :=
  by
  have p0000 := @g_biimprcd ph ps ch hyp_biimpa_1
  have p0001 := @g_imp ch ph ps p0000
  exact p0001

@[expose]
noncomputable def g_ianor (ph : Wff) (ps : Wff) :
    Nominal.NPrf (syn_wb (.neg (syn_wa ph ps)) (syn_wo (.neg ph) (.neg ps))) :=
  by
  have p0000 := @g_imnan ph ps
  have p0001 := @g_pm4_62 ph ps
  have p0002 :=
    @g_bitr3i (.neg (syn_wa ph ps)) (.imp ph (.neg ps)) (syn_wo (.neg ph) (.neg ps)) p0000
      p0001
  exact p0002

@[expose]
noncomputable def g_ioran (ph : Wff) (ps : Wff) :
    Nominal.NPrf (syn_wb (.neg (syn_wo ph ps)) (syn_wa (.neg ph) (.neg ps))) :=
  by
  have p0000 := @g_pm4_65 ph ps
  have p0001 := @g_pm4_64 ph ps
  have p0002 :=
    @g_xchnxbi (.imp (.neg ph) ps) (syn_wa (.neg ph) (.neg ps)) (syn_wo ph ps) p0000 p0001
  exact p0002

@[expose]
noncomputable def g_pm4_56 (ph : Wff) (ps : Wff) :
    Nominal.NPrf (syn_wb (syn_wa (.neg ph) (.neg ps)) (.neg (syn_wo ph ps))) :=
  by
  have p0000 := @g_ioran ph ps
  have p0001 := @g_bicomi (.neg (syn_wo ph ps)) (syn_wa (.neg ph) (.neg ps)) p0000
  exact p0001

@[expose]
noncomputable def g_oran (ph : Wff) (ps : Wff) :
    Nominal.NPrf (syn_wb (syn_wo ph ps) (.neg (syn_wa (.neg ph) (.neg ps)))) :=
  by
  have p0000 := @g_pm4_56 ph ps
  have p0001 := @g_con2bii (syn_wa (.neg ph) (.neg ps)) (syn_wo ph ps) p0000
  exact p0001

@[expose]
noncomputable def g_iba (ph : Wff) (ps : Wff) :
    Nominal.NPrf (.imp ph (syn_wb ps (syn_wa ps ph))) :=
  by
  have p0000 := @g_pm3_21 ph ps
  have p0001 := @g_simpl ps ph
  have p0002 := @g_impbid1 ph ps (syn_wa ps ph) p0000 p0001
  exact p0002

@[expose]
noncomputable def g_ibar (ph : Wff) (ps : Wff) :
    Nominal.NPrf (.imp ph (syn_wb ps (syn_wa ph ps))) :=
  by
  have p0000 := @g_pm3_2 ph ps
  have p0001 := @g_simpr ph ps
  have p0002 := @g_impbid1 ph ps (syn_wa ph ps) p0000 p0001
  exact p0002

@[expose]
noncomputable def g_biantru (ph : Wff) (ps : Wff) (hyp_biantru_1 : Nominal.NPrf ph) :
    Nominal.NPrf (syn_wb ps (syn_wa ps ph)) :=
  by
  have p0000 := @g_iba ph ps
  have p0001 := Nominal.mp hyp_biantru_1 p0000
  exact p0001

@[expose]
noncomputable def g_biantrur (ph : Wff) (ps : Wff) (hyp_biantrur_1 : Nominal.NPrf ph) :
    Nominal.NPrf (syn_wb ps (syn_wa ph ps)) :=
  by
  have p0000 := @g_ibar ph ps
  have p0001 := Nominal.mp hyp_biantrur_1 p0000
  exact p0001

@[expose]
noncomputable def g_biantrud (ph : Wff) (ps : Wff) (ch : Wff)
    (hyp_biantrud_1 : Nominal.NPrf (.imp ph ps)) :
    Nominal.NPrf (.imp ph (syn_wb ch (syn_wa ch ps))) :=
  by
  have p0000 := @g_iba ps ch
  have p0001 := @g_syl ph ps (syn_wb ch (syn_wa ch ps)) hyp_biantrud_1 p0000
  exact p0001

@[expose]
noncomputable def g_biantrurd (ph : Wff) (ps : Wff) (ch : Wff)
    (hyp_biantrud_1 : Nominal.NPrf (.imp ph ps)) :
    Nominal.NPrf (.imp ph (syn_wb ch (syn_wa ps ch))) :=
  by
  have p0000 := @g_ibar ps ch
  have p0001 := @g_syl ph ps (syn_wb ch (syn_wa ps ch)) hyp_biantrud_1 p0000
  exact p0001

@[expose]
noncomputable def g_jaao (ph : Wff) (ps : Wff) (ch : Wff) (th : Wff) (ta : Wff)
    (hyp_jaao_1 : Nominal.NPrf (.imp ph (.imp ps ch)))
    (hyp_jaao_2 : Nominal.NPrf (.imp th (.imp ta ch))) :
    Nominal.NPrf (.imp (syn_wa ph th) (.imp (syn_wo ps ta) ch)) :=
  by
  have p0000 := @g_adantr ph (.imp ps ch) th hyp_jaao_1
  have p0001 := @g_adantl th (.imp ta ch) ph hyp_jaao_2
  have p0002 := @g_jaod (syn_wa ph th) ps ch ta p0000 p0001
  exact p0002

@[expose]
noncomputable def g_pm3_44 (ph : Wff) (ps : Wff) (ch : Wff) :
    Nominal.NPrf (.imp (syn_wa (.imp ps ph) (.imp ch ph)) (.imp (syn_wo ps ch) ph)) :=
  by
  have p0000 := @g_id (.imp ps ph)
  have p0001 := @g_id (.imp ch ph)
  have p0002 := @g_jaao (.imp ps ph) ps ph (.imp ch ph) ch p0000 p0001
  exact p0002

@[expose]
noncomputable def g_jao (ph : Wff) (ps : Wff) (ch : Wff) :
    Nominal.NPrf (.imp (.imp ph ps) (.imp (.imp ch ps) (.imp (syn_wo ph ch) ps))) :=
  by
  have p0000 := @g_pm3_44 ps ph ch
  have p0001 := @g_ex (.imp ph ps) (.imp ch ps) (.imp (syn_wo ph ch) ps) p0000
  exact p0001

@[expose]
noncomputable def g_pm1_2 (ph : Wff) : Nominal.NPrf (.imp (syn_wo ph ph) ph) :=
  by
  have p0000 := @g_id ph
  have p0001 := @g_jaoi ph ph ph p0000 p0000
  exact p0001

@[expose]
noncomputable def g_oridm (ph : Wff) : Nominal.NPrf (syn_wb (syn_wo ph ph) ph) :=
  by
  have p0000 := @g_pm1_2 ph
  have p0001 := @g_pm2_07 ph
  have p0002 := @g_impbii (syn_wo ph ph) ph p0000 p0001
  exact p0002

@[expose]
noncomputable def g_orim12i (ph : Wff) (ps : Wff) (ch : Wff) (th : Wff)
    (hyp_orim12i_1 : Nominal.NPrf (.imp ph ps))
    (hyp_orim12i_2 : Nominal.NPrf (.imp ch th)) :
    Nominal.NPrf (.imp (syn_wo ph ch) (syn_wo ps th)) :=
  by
  have p0000 := @g_orcd ph ps th hyp_orim12i_1
  have p0001 := @g_olcd ch th ps hyp_orim12i_2
  have p0002 := @g_jaoi ph (syn_wo ps th) ch p0000 p0001
  exact p0002

@[expose]
noncomputable def g_orim2i (ph : Wff) (ps : Wff) (ch : Wff)
    (hyp_orim1i_1 : Nominal.NPrf (.imp ph ps)) :
    Nominal.NPrf (.imp (syn_wo ch ph) (syn_wo ch ps)) :=
  by
  have p0000 := @g_id ch
  have p0001 := @g_orim12i ch ch ph ps p0000 hyp_orim1i_1
  exact p0001

@[expose]
noncomputable def g_orbi2i (ph : Wff) (ps : Wff) (ch : Wff)
    (hyp_orbi2i_1 : Nominal.NPrf (syn_wb ph ps)) :
    Nominal.NPrf (syn_wb (syn_wo ch ph) (syn_wo ch ps)) :=
  by
  have p0000 := @g_biimpi ph ps hyp_orbi2i_1
  have p0001 := @g_orim2i ph ps ch p0000
  have p0002 := @g_biimpri ph ps hyp_orbi2i_1
  have p0003 := @g_orim2i ps ph ch p0002
  have p0004 := @g_impbii (syn_wo ch ph) (syn_wo ch ps) p0001 p0003
  exact p0004

@[expose]
noncomputable def g_orbi1i (ph : Wff) (ps : Wff) (ch : Wff)
    (hyp_orbi2i_1 : Nominal.NPrf (syn_wb ph ps)) :
    Nominal.NPrf (syn_wb (syn_wo ph ch) (syn_wo ps ch)) :=
  by
  have p0000 := @g_orcom ph ch
  have p0001 := @g_orbi2i ph ps ch hyp_orbi2i_1
  have p0002 := @g_orcom ch ps
  have p0003 :=
    @g_n_3bitri (syn_wo ph ch) (syn_wo ch ph) (syn_wo ch ps) (syn_wo ps ch) p0000 p0001
      p0002
  exact p0003

@[expose]
noncomputable def g_orbi12i (ph : Wff) (ps : Wff) (ch : Wff) (th : Wff)
    (hyp_orbi12i_1 : Nominal.NPrf (syn_wb ph ps))
    (hyp_orbi12i_2 : Nominal.NPrf (syn_wb ch th)) :
    Nominal.NPrf (syn_wb (syn_wo ph ch) (syn_wo ps th)) :=
  by
  have p0000 := @g_orbi2i ch th ph hyp_orbi12i_2
  have p0001 := @g_orbi1i ph ps th hyp_orbi12i_1
  have p0002 := @g_bitri (syn_wo ph ch) (syn_wo ph th) (syn_wo ps th) p0000 p0001
  exact p0002

@[expose]
noncomputable def g_pm1_5 (ph : Wff) (ps : Wff) (ch : Wff) :
    Nominal.NPrf (.imp (syn_wo ph (syn_wo ps ch)) (syn_wo ps (syn_wo ph ch))) :=
  by
  have p0000 := @g_orc ph ch
  have p0001 := @g_olcd ph (syn_wo ph ch) ps p0000
  have p0002 := @g_olc ch ph
  have p0003 := @g_orim2i ch (syn_wo ph ch) ps p0002
  have p0004 := @g_jaoi ph (syn_wo ps (syn_wo ph ch)) (syn_wo ps ch) p0001 p0003
  exact p0004

@[expose]
noncomputable def g_or12 (ph : Wff) (ps : Wff) (ch : Wff) :
    Nominal.NPrf (syn_wb (syn_wo ph (syn_wo ps ch)) (syn_wo ps (syn_wo ph ch))) :=
  by
  have p0000 := @g_pm1_5 ph ps ch
  have p0001 := @g_pm1_5 ps ph ch
  have p0002 :=
    @g_impbii (syn_wo ph (syn_wo ps ch)) (syn_wo ps (syn_wo ph ch)) p0000 p0001
  exact p0002

@[expose]
noncomputable def g_orass (ph : Wff) (ps : Wff) (ch : Wff) :
    Nominal.NPrf (syn_wb (syn_wo (syn_wo ph ps) ch) (syn_wo ph (syn_wo ps ch))) :=
  by
  have p0000 := @g_orcom (syn_wo ph ps) ch
  have p0001 := @g_or12 ch ph ps
  have p0002 := @g_orcom ch ps
  have p0003 := @g_orbi2i (syn_wo ch ps) (syn_wo ps ch) ph p0002
  have p0004 :=
    @g_n_3bitri (syn_wo (syn_wo ph ps) ch) (syn_wo ch (syn_wo ph ps))
      (syn_wo ph (syn_wo ch ps)) (syn_wo ph (syn_wo ps ch)) p0000 p0001 p0003
  exact p0004

@[expose]
noncomputable def g_or32 (ph : Wff) (ps : Wff) (ch : Wff) :
    Nominal.NPrf (syn_wb (syn_wo (syn_wo ph ps) ch) (syn_wo (syn_wo ph ch) ps)) :=
  by
  have p0000 := @g_orass ph ps ch
  have p0001 := @g_or12 ph ps ch
  have p0002 := @g_orcom ps (syn_wo ph ch)
  have p0003 :=
    @g_n_3bitri (syn_wo (syn_wo ph ps) ch) (syn_wo ph (syn_wo ps ch))
      (syn_wo ps (syn_wo ph ch)) (syn_wo (syn_wo ph ch) ps) p0000 p0001 p0002
  exact p0003

@[expose]
noncomputable def g_jca (ph : Wff) (ps : Wff) (ch : Wff)
    (hyp_jca_1 : Nominal.NPrf (.imp ph ps)) (hyp_jca_2 : Nominal.NPrf (.imp ph ch)) :
    Nominal.NPrf (.imp ph (syn_wa ps ch)) :=
  by
  have p0000 := @g_pm3_2 ps ch
  have p0001 := @g_sylc ph ps ch (syn_wa ps ch) hyp_jca_1 hyp_jca_2 p0000
  exact p0001

@[expose]
noncomputable def g_jcad (ph : Wff) (ps : Wff) (ch : Wff) (th : Wff)
    (hyp_jcad_1 : Nominal.NPrf (.imp ph (.imp ps ch)))
    (hyp_jcad_2 : Nominal.NPrf (.imp ph (.imp ps th))) :
    Nominal.NPrf (.imp ph (.imp ps (syn_wa ch th))) :=
  by
  have p0000 := @g_pm3_2 ch th
  have p0001 := @g_syl6c ph ps ch th (syn_wa ch th) hyp_jcad_1 hyp_jcad_2 p0000
  exact p0001

@[expose]
noncomputable def g_jca31 (ph : Wff) (ps : Wff) (ch : Wff) (th : Wff)
    (hyp_jca31_1 : Nominal.NPrf (.imp ph ps)) (hyp_jca31_2 : Nominal.NPrf (.imp ph ch))
    (hyp_jca31_3 : Nominal.NPrf (.imp ph th)) :
    Nominal.NPrf (.imp ph (syn_wa (syn_wa ps ch) th)) :=
  by
  have p0000 := @g_jca ph ps ch hyp_jca31_1 hyp_jca31_2
  have p0001 := @g_jca ph (syn_wa ps ch) th p0000 hyp_jca31_3
  exact p0001

@[expose]
noncomputable def g_jca32 (ph : Wff) (ps : Wff) (ch : Wff) (th : Wff)
    (hyp_jca31_1 : Nominal.NPrf (.imp ph ps)) (hyp_jca31_2 : Nominal.NPrf (.imp ph ch))
    (hyp_jca31_3 : Nominal.NPrf (.imp ph th)) :
    Nominal.NPrf (.imp ph (syn_wa ps (syn_wa ch th))) :=
  by
  have p0000 := @g_jca ph ch th hyp_jca31_2 hyp_jca31_3
  have p0001 := @g_jca ph ps (syn_wa ch th) hyp_jca31_1 p0000
  exact p0001

@[expose]
noncomputable def g_jcai (ph : Wff) (ps : Wff) (ch : Wff)
    (hyp_jcai_1 : Nominal.NPrf (.imp ph ps))
    (hyp_jcai_2 : Nominal.NPrf (.imp ph (.imp ps ch))) :
    Nominal.NPrf (.imp ph (syn_wa ps ch)) :=
  by
  have p0000 := @g_mpd ph ps ch hyp_jcai_1 hyp_jcai_2
  have p0001 := @g_jca ph ps ch hyp_jcai_1 p0000
  exact p0001

@[expose]
noncomputable def g_jctil (ph : Wff) (ps : Wff) (ch : Wff)
    (hyp_jctil_1 : Nominal.NPrf (.imp ph ps)) (hyp_jctil_2 : Nominal.NPrf ch) :
    Nominal.NPrf (.imp ph (syn_wa ch ps)) :=
  by
  have p0000 := @g_a1i ch ph hyp_jctil_2
  have p0001 := @g_jca ph ch ps p0000 hyp_jctil_1
  exact p0001

@[expose]
noncomputable def g_jctir (ph : Wff) (ps : Wff) (ch : Wff)
    (hyp_jctil_1 : Nominal.NPrf (.imp ph ps)) (hyp_jctil_2 : Nominal.NPrf ch) :
    Nominal.NPrf (.imp ph (syn_wa ps ch)) :=
  by
  have p0000 := @g_a1i ch ph hyp_jctil_2
  have p0001 := @g_jca ph ps ch hyp_jctil_1 p0000
  exact p0001

@[expose]
noncomputable def g_jctl (ph : Wff) (ps : Wff) (hyp_jctl_1 : Nominal.NPrf ps) :
    Nominal.NPrf (.imp ph (syn_wa ps ph)) :=
  by
  have p0000 := @g_id ph
  have p0001 := @g_jctil ph ph ps p0000 hyp_jctl_1
  exact p0001

@[expose]
noncomputable def g_jctr (ph : Wff) (ps : Wff) (hyp_jctl_1 : Nominal.NPrf ps) :
    Nominal.NPrf (.imp ph (syn_wa ph ps)) :=
  by
  have p0000 := @g_id ph
  have p0001 := @g_jctir ph ph ps p0000 hyp_jctl_1
  exact p0001

@[expose]
noncomputable def g_jctild (ph : Wff) (ps : Wff) (ch : Wff) (th : Wff)
    (hyp_jctild_1 : Nominal.NPrf (.imp ph (.imp ps ch)))
    (hyp_jctild_2 : Nominal.NPrf (.imp ph th)) :
    Nominal.NPrf (.imp ph (.imp ps (syn_wa th ch))) :=
  by
  have p0000 := @g_a1d ph th ps hyp_jctild_2
  have p0001 := @g_jcad ph ps th ch p0000 hyp_jctild_1
  exact p0001

@[expose]
noncomputable def g_jctird (ph : Wff) (ps : Wff) (ch : Wff) (th : Wff)
    (hyp_jctird_1 : Nominal.NPrf (.imp ph (.imp ps ch)))
    (hyp_jctird_2 : Nominal.NPrf (.imp ph th)) :
    Nominal.NPrf (.imp ph (.imp ps (syn_wa ch th))) :=
  by
  have p0000 := @g_a1d ph th ps hyp_jctird_2
  have p0001 := @g_jcad ph ps ch th hyp_jctird_1 p0000
  exact p0001

@[expose]
noncomputable def g_ancl (ph : Wff) (ps : Wff) :
    Nominal.NPrf (.imp (.imp ph ps) (.imp ph (syn_wa ph ps))) :=
  by
  have p0000 := @g_pm3_2 ph ps
  have p0001 := @g_a2i ph ps (syn_wa ph ps) p0000
  exact p0001

@[expose]
noncomputable def g_anclb (ph : Wff) (ps : Wff) :
    Nominal.NPrf (syn_wb (.imp ph ps) (.imp ph (syn_wa ph ps))) :=
  by
  have p0000 := @g_ibar ph ps
  have p0001 := @g_pm5_74i ph ps (syn_wa ph ps) p0000
  exact p0001

@[expose]
noncomputable def g_ancli (ph : Wff) (ps : Wff)
    (hyp_ancli_1 : Nominal.NPrf (.imp ph ps)) : Nominal.NPrf (.imp ph (syn_wa ph ps)) :=
  by
  have p0000 := @g_id ph
  have p0001 := @g_jca ph ph ps p0000 hyp_ancli_1
  exact p0001

@[expose]
noncomputable def g_ancri (ph : Wff) (ps : Wff)
    (hyp_ancri_1 : Nominal.NPrf (.imp ph ps)) : Nominal.NPrf (.imp ph (syn_wa ps ph)) :=
  by
  have p0000 := @g_id ph
  have p0001 := @g_jca ph ps ph hyp_ancri_1 p0000
  exact p0001

@[expose]
noncomputable def g_ancld (ph : Wff) (ps : Wff) (ch : Wff)
    (hyp_ancld_1 : Nominal.NPrf (.imp ph (.imp ps ch))) :
    Nominal.NPrf (.imp ph (.imp ps (syn_wa ps ch))) :=
  by
  have p0000 := @g_idd ph ps
  have p0001 := @g_jcad ph ps ps ch p0000 hyp_ancld_1
  exact p0001

@[expose]
noncomputable def g_ancrd (ph : Wff) (ps : Wff) (ch : Wff)
    (hyp_ancrd_1 : Nominal.NPrf (.imp ph (.imp ps ch))) :
    Nominal.NPrf (.imp ph (.imp ps (syn_wa ch ps))) :=
  by
  have p0000 := @g_idd ph ps
  have p0001 := @g_jcad ph ps ch ps hyp_ancrd_1 p0000
  exact p0001

@[expose]
noncomputable def g_anc2li (ph : Wff) (ps : Wff) (ch : Wff)
    (hyp_anc2li_1 : Nominal.NPrf (.imp ph (.imp ps ch))) :
    Nominal.NPrf (.imp ph (.imp ps (syn_wa ph ch))) :=
  by
  have p0000 := @g_id ph
  have p0001 := @g_jctild ph ps ch ph hyp_anc2li_1 p0000
  exact p0001

@[expose]
noncomputable def g_anc2ri (ph : Wff) (ps : Wff) (ch : Wff)
    (hyp_anc2ri_1 : Nominal.NPrf (.imp ph (.imp ps ch))) :
    Nominal.NPrf (.imp ph (.imp ps (syn_wa ch ph))) :=
  by
  have p0000 := @g_id ph
  have p0001 := @g_jctird ph ps ch ph hyp_anc2ri_1 p0000
  exact p0001

@[expose]
noncomputable def g_pm3_4 (ph : Wff) (ps : Wff) :
    Nominal.NPrf (.imp (syn_wa ph ps) (.imp ph ps)) :=
  by
  have p0000 := @g_simpr ph ps
  have p0001 := @g_a1d (syn_wa ph ps) ps ph p0000
  exact p0001

@[expose]
noncomputable def g_pm4_45im (ph : Wff) (ps : Wff) :
    Nominal.NPrf (syn_wb ph (syn_wa ph (.imp ps ph))) :=
  by
  have p0000 := Nominal.ax1 ph ps
  have p0001 := @g_ancli ph (.imp ps ph) p0000
  have p0002 := @g_simpl ph (.imp ps ph)
  have p0003 := @g_impbii ph (syn_wa ph (.imp ps ph)) p0001 p0002
  exact p0003

@[expose]
noncomputable def g_anim12d (ph : Wff) (ps : Wff) (ch : Wff) (th : Wff) (ta : Wff)
    (hyp_anim12d_1 : Nominal.NPrf (.imp ph (.imp ps ch)))
    (hyp_anim12d_2 : Nominal.NPrf (.imp ph (.imp th ta))) :
    Nominal.NPrf (.imp ph (.imp (syn_wa ps th) (syn_wa ch ta))) :=
  by
  have p0000 := @g_idd ph (syn_wa ch ta)
  have p0001 := @g_syl2and ph ps ch th ta (syn_wa ch ta) hyp_anim12d_1 hyp_anim12d_2 p0000
  exact p0001

@[expose]
noncomputable def g_anim1d (ph : Wff) (ps : Wff) (ch : Wff) (th : Wff)
    (hyp_anim1d_1 : Nominal.NPrf (.imp ph (.imp ps ch))) :
    Nominal.NPrf (.imp ph (.imp (syn_wa ps th) (syn_wa ch th))) :=
  by
  have p0000 := @g_idd ph th
  have p0001 := @g_anim12d ph ps ch th th hyp_anim1d_1 p0000
  exact p0001

@[expose]
noncomputable def g_anim2d (ph : Wff) (ps : Wff) (ch : Wff) (th : Wff)
    (hyp_anim1d_1 : Nominal.NPrf (.imp ph (.imp ps ch))) :
    Nominal.NPrf (.imp ph (.imp (syn_wa th ps) (syn_wa th ch))) :=
  by
  have p0000 := @g_idd ph th
  have p0001 := @g_anim12d ph th th ps ch p0000 hyp_anim1d_1
  exact p0001

@[expose]
noncomputable def g_anim12i (ph : Wff) (ps : Wff) (ch : Wff) (th : Wff)
    (hyp_anim12i_1 : Nominal.NPrf (.imp ph ps))
    (hyp_anim12i_2 : Nominal.NPrf (.imp ch th)) :
    Nominal.NPrf (.imp (syn_wa ph ch) (syn_wa ps th)) :=
  by
  have p0000 := @g_id (syn_wa ps th)
  have p0001 := @g_syl2an ph ps th (syn_wa ps th) ch hyp_anim12i_1 hyp_anim12i_2 p0000
  exact p0001

@[expose]
noncomputable def g_anim12ci (ph : Wff) (ps : Wff) (ch : Wff) (th : Wff)
    (hyp_anim12i_1 : Nominal.NPrf (.imp ph ps))
    (hyp_anim12i_2 : Nominal.NPrf (.imp ch th)) :
    Nominal.NPrf (.imp (syn_wa ph ch) (syn_wa th ps)) :=
  by
  have p0000 := @g_anim12i ch th ph ps hyp_anim12i_2 hyp_anim12i_1
  have p0001 := @g_ancoms ch ph (syn_wa th ps) p0000
  exact p0001

@[expose]
noncomputable def g_anim1i (ph : Wff) (ps : Wff) (ch : Wff)
    (hyp_anim1i_1 : Nominal.NPrf (.imp ph ps)) :
    Nominal.NPrf (.imp (syn_wa ph ch) (syn_wa ps ch)) :=
  by
  have p0000 := @g_id ch
  have p0001 := @g_anim12i ph ps ch ch hyp_anim1i_1 p0000
  exact p0001

@[expose]
noncomputable def g_anim2i (ph : Wff) (ps : Wff) (ch : Wff)
    (hyp_anim1i_1 : Nominal.NPrf (.imp ph ps)) :
    Nominal.NPrf (.imp (syn_wa ch ph) (syn_wa ch ps)) :=
  by
  have p0000 := @g_id ch
  have p0001 := @g_anim12i ch ch ph ps p0000 hyp_anim1i_1
  exact p0001

@[expose]
noncomputable def g_anim12ii (ph : Wff) (ps : Wff) (ch : Wff) (th : Wff) (ta : Wff)
    (hyp_anim12ii_1 : Nominal.NPrf (.imp ph (.imp ps ch)))
    (hyp_anim12ii_2 : Nominal.NPrf (.imp th (.imp ps ta))) :
    Nominal.NPrf (.imp (syn_wa ph th) (.imp ps (syn_wa ch ta))) :=
  by
  have p0000 := @g_adantr ph (.imp ps ch) th hyp_anim12ii_1
  have p0001 := @g_adantl th (.imp ps ta) ph hyp_anim12ii_2
  have p0002 := @g_jcad (syn_wa ph th) ps ch ta p0000 p0001
  exact p0002

@[expose]
noncomputable def g_prth (ph : Wff) (ps : Wff) (ch : Wff) (th : Wff) :
    Nominal.NPrf
      (.imp (syn_wa (.imp ph ps) (.imp ch th)) (.imp (syn_wa ph ch) (syn_wa ps th))) :=
  by
  have p0000 := @g_simpl (.imp ph ps) (.imp ch th)
  have p0001 := @g_simpr (.imp ph ps) (.imp ch th)
  have p0002 := @g_anim12d (syn_wa (.imp ph ps) (.imp ch th)) ph ps ch th p0000 p0001
  exact p0002

@[expose]
noncomputable def g_pm3_35 (ph : Wff) (ps : Wff) :
    Nominal.NPrf (.imp (syn_wa ph (.imp ph ps)) ps) :=
  by
  have p0000 := @g_pm2_27 ph ps
  have p0001 := @g_imp ph (.imp ph ps) ps p0000
  exact p0001

@[expose]
noncomputable def g_imp4a (ph : Wff) (ps : Wff) (ch : Wff) (th : Wff) (ta : Wff)
    (hyp_imp4_1 : Nominal.NPrf (.imp ph (.imp ps (.imp ch (.imp th ta))))) :
    Nominal.NPrf (.imp ph (.imp ps (.imp (syn_wa ch th) ta))) :=
  by
  have p0000 := @g_impexp ch th ta
  have p0001 :=
    @g_syl6ibr ph ps (.imp ch (.imp th ta)) (.imp (syn_wa ch th) ta) hyp_imp4_1 p0000
  exact p0001

@[expose]
noncomputable def g_imp4c (ph : Wff) (ps : Wff) (ch : Wff) (th : Wff) (ta : Wff)
    (hyp_imp4_1 : Nominal.NPrf (.imp ph (.imp ps (.imp ch (.imp th ta))))) :
    Nominal.NPrf (.imp ph (.imp (syn_wa (syn_wa ps ch) th) ta)) :=
  by
  have p0000 := @g_imp3a ph ps ch (.imp th ta) hyp_imp4_1
  have p0001 := @g_imp3a ph (syn_wa ps ch) th ta p0000
  exact p0001

@[expose]
noncomputable def g_expimpd (ph : Wff) (ps : Wff) (ch : Wff) (th : Wff)
    (hyp_expimpd_1 : Nominal.NPrf (.imp (syn_wa ph ps) (.imp ch th))) :
    Nominal.NPrf (.imp ph (.imp (syn_wa ps ch) th)) :=
  by
  have p0000 := @g_ex ph ps (.imp ch th) hyp_expimpd_1
  have p0001 := @g_imp3a ph ps ch th p0000
  exact p0001

@[expose]
noncomputable def g_exp31 (ph : Wff) (ps : Wff) (ch : Wff) (th : Wff)
    (hyp_exp31_1 : Nominal.NPrf (.imp (syn_wa (syn_wa ph ps) ch) th)) :
    Nominal.NPrf (.imp ph (.imp ps (.imp ch th))) :=
  by
  have p0000 := @g_ex (syn_wa ph ps) ch th hyp_exp31_1
  have p0001 := @g_ex ph ps (.imp ch th) p0000
  exact p0001

@[expose]
noncomputable def g_exp32 (ph : Wff) (ps : Wff) (ch : Wff) (th : Wff)
    (hyp_exp32_1 : Nominal.NPrf (.imp (syn_wa ph (syn_wa ps ch)) th)) :
    Nominal.NPrf (.imp ph (.imp ps (.imp ch th))) :=
  by
  have p0000 := @g_ex ph (syn_wa ps ch) th hyp_exp32_1
  have p0001 := @g_exp3a ph ps ch th p0000
  exact p0001

@[expose]
noncomputable def g_exp4a (ph : Wff) (ps : Wff) (ch : Wff) (th : Wff) (ta : Wff)
    (hyp_exp4a_1 : Nominal.NPrf (.imp ph (.imp ps (.imp (syn_wa ch th) ta)))) :
    Nominal.NPrf (.imp ph (.imp ps (.imp ch (.imp th ta)))) :=
  by
  have p0000 := @g_impexp ch th ta
  have p0001 :=
    @g_syl6ib ph ps (.imp (syn_wa ch th) ta) (.imp ch (.imp th ta)) hyp_exp4a_1 p0000
  exact p0001

@[expose]
noncomputable def g_exp4b (ph : Wff) (ps : Wff) (ch : Wff) (th : Wff) (ta : Wff)
    (hyp_exp4b_1 : Nominal.NPrf (.imp (syn_wa ph ps) (.imp (syn_wa ch th) ta))) :
    Nominal.NPrf (.imp ph (.imp ps (.imp ch (.imp th ta)))) :=
  by
  have p0000 := @g_ex ph ps (.imp (syn_wa ch th) ta) hyp_exp4b_1
  have p0001 := @g_exp4a ph ps ch th ta p0000
  exact p0001

@[expose]
noncomputable def g_exp4d (ph : Wff) (ps : Wff) (ch : Wff) (th : Wff) (ta : Wff)
    (hyp_exp4d_1 : Nominal.NPrf (.imp ph (.imp (syn_wa ps (syn_wa ch th)) ta))) :
    Nominal.NPrf (.imp ph (.imp ps (.imp ch (.imp th ta)))) :=
  by
  have p0000 := @g_exp3a ph ps (syn_wa ch th) ta hyp_exp4d_1
  have p0001 := @g_exp4a ph ps ch th ta p0000
  exact p0001

@[expose]
noncomputable def g_exp42 (ph : Wff) (ps : Wff) (ch : Wff) (th : Wff) (ta : Wff)
    (hyp_exp42_1 : Nominal.NPrf (.imp (syn_wa (syn_wa ph (syn_wa ps ch)) th) ta)) :
    Nominal.NPrf (.imp ph (.imp ps (.imp ch (.imp th ta)))) :=
  by
  have p0000 := @g_exp31 ph (syn_wa ps ch) th ta hyp_exp42_1
  have p0001 := @g_exp3a ph ps ch (.imp th ta) p0000
  exact p0001

@[expose]
noncomputable def g_exp43 (ph : Wff) (ps : Wff) (ch : Wff) (th : Wff) (ta : Wff)
    (hyp_exp43_1 : Nominal.NPrf (.imp (syn_wa (syn_wa ph ps) (syn_wa ch th)) ta)) :
    Nominal.NPrf (.imp ph (.imp ps (.imp ch (.imp th ta)))) :=
  by
  have p0000 := @g_ex (syn_wa ph ps) (syn_wa ch th) ta hyp_exp43_1
  have p0001 := @g_exp4b ph ps ch th ta p0000
  exact p0001

@[expose]
noncomputable def g_exp45 (ph : Wff) (ps : Wff) (ch : Wff) (th : Wff) (ta : Wff)
    (hyp_exp45_1 : Nominal.NPrf (.imp (syn_wa ph (syn_wa ps (syn_wa ch th))) ta)) :
    Nominal.NPrf (.imp ph (.imp ps (.imp ch (.imp th ta)))) :=
  by
  have p0000 := @g_exp32 ph ps (syn_wa ch th) ta hyp_exp45_1
  have p0001 := @g_exp4a ph ps ch th ta p0000
  exact p0001

@[expose]
noncomputable def g_expr (ph : Wff) (ps : Wff) (ch : Wff) (th : Wff)
    (hyp_expr_1 : Nominal.NPrf (.imp (syn_wa ph (syn_wa ps ch)) th)) :
    Nominal.NPrf (.imp (syn_wa ph ps) (.imp ch th)) :=
  by
  have p0000 := @g_exp32 ph ps ch th hyp_expr_1
  have p0001 := @g_imp ph ps (.imp ch th) p0000
  exact p0001

@[expose]
noncomputable def g_exp5c (ph : Wff) (ps : Wff) (ch : Wff) (th : Wff) (ta : Wff)
    (et : Wff)
    (hyp_exp5c_1 : Nominal.NPrf (.imp ph (.imp (syn_wa ps ch) (.imp (syn_wa th ta) et)))) :
    Nominal.NPrf (.imp ph (.imp ps (.imp ch (.imp th (.imp ta et))))) :=
  by
  have p0000 := @g_exp4a ph (syn_wa ps ch) th ta et hyp_exp5c_1
  have p0001 := @g_exp3a ph ps ch (.imp th (.imp ta et)) p0000
  exact p0001

@[expose]
noncomputable def g_impr (ph : Wff) (ps : Wff) (ch : Wff) (th : Wff)
    (hyp_impr_1 : Nominal.NPrf (.imp (syn_wa ph ps) (.imp ch th))) :
    Nominal.NPrf (.imp (syn_wa ph (syn_wa ps ch)) th) :=
  by
  have p0000 := @g_ex ph ps (.imp ch th) hyp_impr_1
  have p0001 := @g_imp32 ph ps ch th p0000
  exact p0001

@[expose]
noncomputable def g_impac (ph : Wff) (ps : Wff) (ch : Wff)
    (hyp_impac_1 : Nominal.NPrf (.imp ph (.imp ps ch))) :
    Nominal.NPrf (.imp (syn_wa ph ps) (syn_wa ch ps)) :=
  by
  have p0000 := @g_ancrd ph ps ch hyp_impac_1
  have p0001 := @g_imp ph ps (syn_wa ch ps) p0000
  exact p0001

@[expose]
noncomputable def g_simprbda (ph : Wff) (ps : Wff) (ch : Wff) (th : Wff)
    (hyp_pm3_26bda_1 : Nominal.NPrf (.imp ph (syn_wb ps (syn_wa ch th)))) :
    Nominal.NPrf (.imp (syn_wa ph ps) ch) :=
  by
  have p0000 := @g_biimpa ph ps (syn_wa ch th) hyp_pm3_26bda_1
  have p0001 := @g_simpld (syn_wa ph ps) ch th p0000
  exact p0001

@[expose]
noncomputable def g_simplbi2 (ph : Wff) (ps : Wff) (ch : Wff)
    (hyp_pm3_26bi2_1 : Nominal.NPrf (syn_wb ph (syn_wa ps ch))) :
    Nominal.NPrf (.imp ps (.imp ch ph)) :=
  by
  have p0000 := @g_biimpri ph (syn_wa ps ch) hyp_pm3_26bi2_1
  have p0001 := @g_ex ps ch ph p0000
  exact p0001

@[expose]
noncomputable def g_dfbi2 (ph : Wff) (ps : Wff) :
    Nominal.NPrf (syn_wb (syn_wb ph ps) (syn_wa (.imp ph ps) (.imp ps ph))) :=
  by
  have p0000 := @g_dfbi1 ph ps
  have p0001 := (Nominal.biimpRefl (syn_wa (.imp ph ps) (.imp ps ph)))
  have p0002 :=
    @g_bitr4i (syn_wb ph ps) (.neg (.imp (.imp ph ps) (.neg (.imp ps ph))))
      (syn_wa (.imp ph ps) (.imp ps ph)) p0000 p0001
  exact p0002

@[expose]
noncomputable def g_pm4_71 (ph : Wff) (ps : Wff) :
    Nominal.NPrf (syn_wb (.imp ph ps) (syn_wb ph (syn_wa ph ps))) :=
  by
  have p0000 := @g_simpl ph ps
  have p0001 := @g_biantru (.imp (syn_wa ph ps) ph) (.imp ph (syn_wa ph ps)) p0000
  have p0002 := @g_anclb ph ps
  have p0003 := @g_dfbi2 ph (syn_wa ph ps)
  have p0004 :=
    @g_n_3bitr4i (.imp ph (syn_wa ph ps))
      (syn_wa (.imp ph (syn_wa ph ps)) (.imp (syn_wa ph ps) ph)) (.imp ph ps)
      (syn_wb ph (syn_wa ph ps)) p0001 p0002 p0003
  exact p0004

@[expose]
noncomputable def g_pm4_71r (ph : Wff) (ps : Wff) :
    Nominal.NPrf (syn_wb (.imp ph ps) (syn_wb ph (syn_wa ps ph))) :=
  by
  have p0000 := @g_pm4_71 ph ps
  have p0001 := @g_ancom ph ps
  have p0002 := @g_bibi2i (syn_wa ph ps) (syn_wa ps ph) ph p0001
  have p0003 :=
    @g_bitri (.imp ph ps) (syn_wb ph (syn_wa ph ps)) (syn_wb ph (syn_wa ps ph)) p0000
      p0002
  exact p0003

@[expose]
noncomputable def g_pm4_71i (ph : Wff) (ps : Wff)
    (hyp_pm4_71i_1 : Nominal.NPrf (.imp ph ps)) :
    Nominal.NPrf (syn_wb ph (syn_wa ph ps)) :=
  by
  have p0000 := @g_pm4_71 ph ps
  have p0001 := @g_mpbi (.imp ph ps) (syn_wb ph (syn_wa ph ps)) hyp_pm4_71i_1 p0000
  exact p0001

@[expose]
noncomputable def g_pm4_71ri (ph : Wff) (ps : Wff)
    (hyp_pm4_71ri_1 : Nominal.NPrf (.imp ph ps)) :
    Nominal.NPrf (syn_wb ph (syn_wa ps ph)) :=
  by
  have p0000 := @g_pm4_71r ph ps
  have p0001 := @g_mpbi (.imp ph ps) (syn_wb ph (syn_wa ps ph)) hyp_pm4_71ri_1 p0000
  exact p0001

@[expose]
noncomputable def g_pm4_71rd (ph : Wff) (ps : Wff) (ch : Wff)
    (hyp_pm4_71rd_1 : Nominal.NPrf (.imp ph (.imp ps ch))) :
    Nominal.NPrf (.imp ph (syn_wb ps (syn_wa ch ps))) :=
  by
  have p0000 := @g_pm4_71r ps ch
  have p0001 := @g_sylib ph (.imp ps ch) (syn_wb ps (syn_wa ch ps)) hyp_pm4_71rd_1 p0000
  exact p0001

@[expose]
noncomputable def g_pm5_32 (ph : Wff) (ps : Wff) (ch : Wff) :
    Nominal.NPrf
      (syn_wb (.imp ph (syn_wb ps ch)) (syn_wb (syn_wa ph ps) (syn_wa ph ch))) :=
  by
  have p0000 := @g_notbi ps ch
  have p0001 := @g_imbi2i (syn_wb ps ch) (syn_wb (.neg ps) (.neg ch)) ph p0000
  have p0002 := @g_pm5_74 ph (.neg ps) (.neg ch)
  have p0003 := @g_notbi (.imp ph (.neg ps)) (.imp ph (.neg ch))
  have p0004 :=
    @g_n_3bitri (.imp ph (syn_wb ps ch)) (.imp ph (syn_wb (.neg ps) (.neg ch)))
      (syn_wb (.imp ph (.neg ps)) (.imp ph (.neg ch)))
      (syn_wb (.neg (.imp ph (.neg ps))) (.neg (.imp ph (.neg ch)))) p0001 p0002 p0003
  have p0005 := (Nominal.biimpRefl (syn_wa ph ps))
  have p0006 := (Nominal.biimpRefl (syn_wa ph ch))
  have p0007 :=
    @g_bibi12i (syn_wa ph ps) (.neg (.imp ph (.neg ps))) (syn_wa ph ch)
      (.neg (.imp ph (.neg ch))) p0005 p0006
  have p0008 :=
    @g_bitr4i (.imp ph (syn_wb ps ch))
      (syn_wb (.neg (.imp ph (.neg ps))) (.neg (.imp ph (.neg ch))))
      (syn_wb (syn_wa ph ps) (syn_wa ph ch)) p0004 p0007
  exact p0008

@[expose]
noncomputable def g_pm5_32i (ph : Wff) (ps : Wff) (ch : Wff)
    (hyp_pm5_32i_1 : Nominal.NPrf (.imp ph (syn_wb ps ch))) :
    Nominal.NPrf (syn_wb (syn_wa ph ps) (syn_wa ph ch)) :=
  by
  have p0000 := @g_pm5_32 ph ps ch
  have p0001 :=
    @g_mpbi (.imp ph (syn_wb ps ch)) (syn_wb (syn_wa ph ps) (syn_wa ph ch)) hyp_pm5_32i_1
      p0000
  exact p0001

@[expose]
noncomputable def g_pm5_32ri (ph : Wff) (ps : Wff) (ch : Wff)
    (hyp_pm5_32i_1 : Nominal.NPrf (.imp ph (syn_wb ps ch))) :
    Nominal.NPrf (syn_wb (syn_wa ps ph) (syn_wa ch ph)) :=
  by
  have p0000 := @g_pm5_32i ph ps ch hyp_pm5_32i_1
  have p0001 := @g_ancom ps ph
  have p0002 := @g_ancom ch ph
  have p0003 :=
    @g_n_3bitr4i (syn_wa ph ps) (syn_wa ph ch) (syn_wa ps ph) (syn_wa ch ph) p0000 p0001
      p0002
  exact p0003

@[expose]
noncomputable def g_pm5_32d (ph : Wff) (ps : Wff) (ch : Wff) (th : Wff)
    (hyp_pm5_32d_1 : Nominal.NPrf (.imp ph (.imp ps (syn_wb ch th)))) :
    Nominal.NPrf (.imp ph (syn_wb (syn_wa ps ch) (syn_wa ps th))) :=
  by
  have p0000 := @g_pm5_32 ps ch th
  have p0001 :=
    @g_sylib ph (.imp ps (syn_wb ch th)) (syn_wb (syn_wa ps ch) (syn_wa ps th))
      hyp_pm5_32d_1 p0000
  exact p0001

@[expose]
noncomputable def g_pm5_32rd (ph : Wff) (ps : Wff) (ch : Wff) (th : Wff)
    (hyp_pm5_32d_1 : Nominal.NPrf (.imp ph (.imp ps (syn_wb ch th)))) :
    Nominal.NPrf (.imp ph (syn_wb (syn_wa ch ps) (syn_wa th ps))) :=
  by
  have p0000 := @g_pm5_32d ph ps ch th hyp_pm5_32d_1
  have p0001 := @g_ancom ch ps
  have p0002 := @g_ancom th ps
  have p0003 :=
    @g_n_3bitr4g ph (syn_wa ps ch) (syn_wa ps th) (syn_wa ch ps) (syn_wa th ps) p0000
      p0001 p0002
  exact p0003

@[expose]
noncomputable def g_pm5_32da (ph : Wff) (ps : Wff) (ch : Wff) (th : Wff)
    (hyp_pm5_32da_1 : Nominal.NPrf (.imp (syn_wa ph ps) (syn_wb ch th))) :
    Nominal.NPrf (.imp ph (syn_wb (syn_wa ps ch) (syn_wa ps th))) :=
  by
  have p0000 := @g_ex ph ps (syn_wb ch th) hyp_pm5_32da_1
  have p0001 := @g_pm5_32d ph ps ch th p0000
  exact p0001

@[expose]
noncomputable def g_biadan2 (ph : Wff) (ps : Wff) (ch : Wff)
    (hyp_biadan2_1 : Nominal.NPrf (.imp ph ps))
    (hyp_biadan2_2 : Nominal.NPrf (.imp ps (syn_wb ph ch))) :
    Nominal.NPrf (syn_wb ph (syn_wa ps ch)) :=
  by
  have p0000 := @g_pm4_71ri ph ps hyp_biadan2_1
  have p0001 := @g_pm5_32i ps ph ch hyp_biadan2_2
  have p0002 := @g_bitri ph (syn_wa ps ph) (syn_wa ps ch) p0000 p0001
  exact p0002

@[expose]
noncomputable def g_pm4_24 (ph : Wff) : Nominal.NPrf (syn_wb ph (syn_wa ph ph)) :=
  by
  have p0000 := @g_id ph
  have p0001 := @g_pm4_71i ph ph p0000
  exact p0001

@[expose]
noncomputable def g_anidm (ph : Wff) : Nominal.NPrf (syn_wb (syn_wa ph ph) ph) :=
  by
  have p0000 := @g_pm4_24 ph
  have p0001 := @g_bicomi ph (syn_wa ph ph) p0000
  exact p0001

@[expose]
noncomputable def g_anidms (ph : Wff) (ps : Wff)
    (hyp_anidms_1 : Nominal.NPrf (.imp (syn_wa ph ph) ps)) : Nominal.NPrf (.imp ph ps) :=
  by
  have p0000 := @g_ex ph ph ps hyp_anidms_1
  have p0001 := @g_pm2_43i ph ps p0000
  exact p0001

@[expose]
noncomputable def g_anasss (ph : Wff) (ps : Wff) (ch : Wff) (th : Wff)
    (hyp_anasss_1 : Nominal.NPrf (.imp (syn_wa (syn_wa ph ps) ch) th)) :
    Nominal.NPrf (.imp (syn_wa ph (syn_wa ps ch)) th) :=
  by
  have p0000 := @g_exp31 ph ps ch th hyp_anasss_1
  have p0001 := @g_imp32 ph ps ch th p0000
  exact p0001

@[expose]
noncomputable def g_anassrs (ph : Wff) (ps : Wff) (ch : Wff) (th : Wff)
    (hyp_anassrs_1 : Nominal.NPrf (.imp (syn_wa ph (syn_wa ps ch)) th)) :
    Nominal.NPrf (.imp (syn_wa (syn_wa ph ps) ch) th) :=
  by
  have p0000 := @g_exp32 ph ps ch th hyp_anassrs_1
  have p0001 := @g_imp31 ph ps ch th p0000
  exact p0001

@[expose]
noncomputable def g_anass (ph : Wff) (ps : Wff) (ch : Wff) :
    Nominal.NPrf (syn_wb (syn_wa (syn_wa ph ps) ch) (syn_wa ph (syn_wa ps ch))) :=
  by
  have p0000 := @g_id (syn_wa ph (syn_wa ps ch))
  have p0001 := @g_anassrs ph ps ch (syn_wa ph (syn_wa ps ch)) p0000
  have p0002 := @g_id (syn_wa (syn_wa ph ps) ch)
  have p0003 := @g_anasss ph ps ch (syn_wa (syn_wa ph ps) ch) p0002
  have p0004 :=
    @g_impbii (syn_wa (syn_wa ph ps) ch) (syn_wa ph (syn_wa ps ch)) p0001 p0003
  exact p0004

@[expose]
noncomputable def g_sylanl1 (ph : Wff) (ps : Wff) (ch : Wff) (th : Wff) (ta : Wff)
    (hyp_sylanl1_1 : Nominal.NPrf (.imp ph ps))
    (hyp_sylanl1_2 : Nominal.NPrf (.imp (syn_wa (syn_wa ps ch) th) ta)) :
    Nominal.NPrf (.imp (syn_wa (syn_wa ph ch) th) ta) :=
  by
  have p0000 := @g_anim1i ph ps ch hyp_sylanl1_1
  have p0001 := @g_sylan (syn_wa ph ch) (syn_wa ps ch) th ta p0000 hyp_sylanl1_2
  exact p0001

@[expose]
noncomputable def g_sylanl2 (ph : Wff) (ps : Wff) (ch : Wff) (th : Wff) (ta : Wff)
    (hyp_sylanl2_1 : Nominal.NPrf (.imp ph ch))
    (hyp_sylanl2_2 : Nominal.NPrf (.imp (syn_wa (syn_wa ps ch) th) ta)) :
    Nominal.NPrf (.imp (syn_wa (syn_wa ps ph) th) ta) :=
  by
  have p0000 := @g_anim2i ph ch ps hyp_sylanl2_1
  have p0001 := @g_sylan (syn_wa ps ph) (syn_wa ps ch) th ta p0000 hyp_sylanl2_2
  exact p0001

@[expose]
noncomputable def g_sylan2i (ph : Wff) (ps : Wff) (ch : Wff) (th : Wff) (ta : Wff)
    (hyp_sylan2i_1 : Nominal.NPrf (.imp ph th))
    (hyp_sylan2i_2 : Nominal.NPrf (.imp ps (.imp (syn_wa ch th) ta))) :
    Nominal.NPrf (.imp ps (.imp (syn_wa ch ph) ta)) :=
  by
  have p0000 := @g_a1i (.imp ph th) ps hyp_sylan2i_1
  have p0001 := @g_sylan2d ps ph th ch ta p0000 hyp_sylan2i_2
  exact p0001

@[expose]
noncomputable def g_sylan9 (ph : Wff) (ps : Wff) (ch : Wff) (th : Wff) (ta : Wff)
    (hyp_sylan9_1 : Nominal.NPrf (.imp ph (.imp ps ch)))
    (hyp_sylan9_2 : Nominal.NPrf (.imp th (.imp ch ta))) :
    Nominal.NPrf (.imp (syn_wa ph th) (.imp ps ta)) :=
  by
  have p0000 := @g_syl9 ph ps ch th ta hyp_sylan9_1 hyp_sylan9_2
  have p0001 := @g_imp ph th (.imp ps ta) p0000
  exact p0001

@[expose]
noncomputable def g_sylan9r (ph : Wff) (ps : Wff) (ch : Wff) (th : Wff) (ta : Wff)
    (hyp_sylan9r_1 : Nominal.NPrf (.imp ph (.imp ps ch)))
    (hyp_sylan9r_2 : Nominal.NPrf (.imp th (.imp ch ta))) :
    Nominal.NPrf (.imp (syn_wa th ph) (.imp ps ta)) :=
  by
  have p0000 := @g_syl9r ph ps ch th ta hyp_sylan9r_1 hyp_sylan9r_2
  have p0001 := @g_imp th ph (.imp ps ta) p0000
  exact p0001

@[expose]
noncomputable def g_mtand (ph : Wff) (ps : Wff) (ch : Wff)
    (hyp_mtand_1 : Nominal.NPrf (.imp ph (.neg ch)))
    (hyp_mtand_2 : Nominal.NPrf (.imp (syn_wa ph ps) ch)) :
    Nominal.NPrf (.imp ph (.neg ps)) :=
  by
  have p0000 := @g_ex ph ps ch hyp_mtand_2
  have p0001 := @g_mtod ph ps ch hyp_mtand_1 p0000
  exact p0001

@[expose]
noncomputable def g_syl2anc (ph : Wff) (ps : Wff) (ch : Wff) (th : Wff)
    (hyp_syl2anc_1 : Nominal.NPrf (.imp ph ps))
    (hyp_syl2anc_2 : Nominal.NPrf (.imp ph ch))
    (hyp_syl2anc_3 : Nominal.NPrf (.imp (syn_wa ps ch) th)) : Nominal.NPrf (.imp ph th) :=
  by
  have p0000 := @g_ex ps ch th hyp_syl2anc_3
  have p0001 := @g_sylc ph ps ch th hyp_syl2anc_1 hyp_syl2anc_2 p0000
  exact p0001

@[expose]
noncomputable def g_sylancl (ph : Wff) (ps : Wff) (ch : Wff) (th : Wff)
    (hyp_sylancl_1 : Nominal.NPrf (.imp ph ps)) (hyp_sylancl_2 : Nominal.NPrf ch)
    (hyp_sylancl_3 : Nominal.NPrf (.imp (syn_wa ps ch) th)) : Nominal.NPrf (.imp ph th) :=
  by
  have p0000 := @g_a1i ch ph hyp_sylancl_2
  have p0001 := @g_syl2anc ph ps ch th hyp_sylancl_1 p0000 hyp_sylancl_3
  exact p0001

@[expose]
noncomputable def g_sylancr (ph : Wff) (ps : Wff) (ch : Wff) (th : Wff)
    (hyp_sylancr_1 : Nominal.NPrf ps) (hyp_sylancr_2 : Nominal.NPrf (.imp ph ch))
    (hyp_sylancr_3 : Nominal.NPrf (.imp (syn_wa ps ch) th)) : Nominal.NPrf (.imp ph th) :=
  by
  have p0000 := @g_a1i ps ph hyp_sylancr_1
  have p0001 := @g_syl2anc ph ps ch th p0000 hyp_sylancr_2 hyp_sylancr_3
  exact p0001

@[expose]
noncomputable def g_sylanbrc (ph : Wff) (ps : Wff) (ch : Wff) (th : Wff)
    (hyp_sylanbrc_1 : Nominal.NPrf (.imp ph ps))
    (hyp_sylanbrc_2 : Nominal.NPrf (.imp ph ch))
    (hyp_sylanbrc_3 : Nominal.NPrf (syn_wb th (syn_wa ps ch))) :
    Nominal.NPrf (.imp ph th) :=
  by
  have p0000 := @g_jca ph ps ch hyp_sylanbrc_1 hyp_sylanbrc_2
  have p0001 := @g_sylibr ph (syn_wa ps ch) th p0000 hyp_sylanbrc_3
  exact p0001

@[expose]
noncomputable def g_mpdan (ph : Wff) (ps : Wff) (ch : Wff)
    (hyp_mpdan_1 : Nominal.NPrf (.imp ph ps))
    (hyp_mpdan_2 : Nominal.NPrf (.imp (syn_wa ph ps) ch)) : Nominal.NPrf (.imp ph ch) :=
  by
  have p0000 := @g_id ph
  have p0001 := @g_syl2anc ph ph ps ch p0000 hyp_mpdan_1 hyp_mpdan_2
  exact p0001

@[expose]
noncomputable def g_mpancom (ph : Wff) (ps : Wff) (ch : Wff)
    (hyp_mpancom_1 : Nominal.NPrf (.imp ps ph))
    (hyp_mpancom_2 : Nominal.NPrf (.imp (syn_wa ph ps) ch)) : Nominal.NPrf (.imp ps ch) :=
  by
  have p0000 := @g_id ps
  have p0001 := @g_syl2anc ps ph ps ch hyp_mpancom_1 p0000 hyp_mpancom_2
  exact p0001

@[expose]
noncomputable def g_mpan (ph : Wff) (ps : Wff) (ch : Wff) (hyp_mpan_1 : Nominal.NPrf ph)
    (hyp_mpan_2 : Nominal.NPrf (.imp (syn_wa ph ps) ch)) : Nominal.NPrf (.imp ps ch) :=
  by
  have p0000 := @g_a1i ph ps hyp_mpan_1
  have p0001 := @g_mpancom ph ps ch p0000 hyp_mpan_2
  exact p0001

@[expose]
noncomputable def g_mpan2 (ph : Wff) (ps : Wff) (ch : Wff) (hyp_mpan2_1 : Nominal.NPrf ps)
    (hyp_mpan2_2 : Nominal.NPrf (.imp (syn_wa ph ps) ch)) : Nominal.NPrf (.imp ph ch) :=
  by
  have p0000 := @g_a1i ps ph hyp_mpan2_1
  have p0001 := @g_mpdan ph ps ch p0000 hyp_mpan2_2
  exact p0001

@[expose]
noncomputable def g_mp2an (ph : Wff) (ps : Wff) (ch : Wff) (hyp_mp2an_1 : Nominal.NPrf ph)
    (hyp_mp2an_2 : Nominal.NPrf ps)
    (hyp_mp2an_3 : Nominal.NPrf (.imp (syn_wa ph ps) ch)) : Nominal.NPrf ch :=
  by
  have p0000 := @g_mpan ph ps ch hyp_mp2an_1 hyp_mp2an_3
  have p0001 := Nominal.mp hyp_mp2an_2 p0000
  exact p0001

@[expose]
noncomputable def g_mp4an (ph : Wff) (ps : Wff) (ch : Wff) (th : Wff) (ta : Wff)
    (hyp_mp4an_1 : Nominal.NPrf ph) (hyp_mp4an_2 : Nominal.NPrf ps)
    (hyp_mp4an_3 : Nominal.NPrf ch) (hyp_mp4an_4 : Nominal.NPrf th)
    (hyp_mp4an_5 : Nominal.NPrf (.imp (syn_wa (syn_wa ph ps) (syn_wa ch th)) ta)) :
    Nominal.NPrf ta :=
  by
  have p0000 := @g_pm3_2i ph ps hyp_mp4an_1 hyp_mp4an_2
  have p0001 := @g_pm3_2i ch th hyp_mp4an_3 hyp_mp4an_4
  have p0002 := @g_mp2an (syn_wa ph ps) (syn_wa ch th) ta p0000 p0001 hyp_mp4an_5
  exact p0002

@[expose]
noncomputable def g_mpan2d (ph : Wff) (ps : Wff) (ch : Wff) (th : Wff)
    (hyp_mpan2d_1 : Nominal.NPrf (.imp ph ch))
    (hyp_mpan2d_2 : Nominal.NPrf (.imp ph (.imp (syn_wa ps ch) th))) :
    Nominal.NPrf (.imp ph (.imp ps th)) :=
  by
  have p0000 := @g_exp3a ph ps ch th hyp_mpan2d_2
  have p0001 := @g_mpid ph ps ch th hyp_mpan2d_1 p0000
  exact p0001

@[expose]
noncomputable def g_mpand (ph : Wff) (ps : Wff) (ch : Wff) (th : Wff)
    (hyp_mpand_1 : Nominal.NPrf (.imp ph ps))
    (hyp_mpand_2 : Nominal.NPrf (.imp ph (.imp (syn_wa ps ch) th))) :
    Nominal.NPrf (.imp ph (.imp ch th)) :=
  by
  have p0000 := @g_ancomsd ph ps ch th hyp_mpand_2
  have p0001 := @g_mpan2d ph ch ps th hyp_mpand_1 p0000
  exact p0001

@[expose]
noncomputable def g_mpani (ph : Wff) (ps : Wff) (ch : Wff) (th : Wff)
    (hyp_mpani_1 : Nominal.NPrf ps)
    (hyp_mpani_2 : Nominal.NPrf (.imp ph (.imp (syn_wa ps ch) th))) :
    Nominal.NPrf (.imp ph (.imp ch th)) :=
  by
  have p0000 := @g_a1i ps ph hyp_mpani_1
  have p0001 := @g_mpand ph ps ch th p0000 hyp_mpani_2
  exact p0001

@[expose]
noncomputable def g_mpan2i (ph : Wff) (ps : Wff) (ch : Wff) (th : Wff)
    (hyp_mpan2i_1 : Nominal.NPrf ch)
    (hyp_mpan2i_2 : Nominal.NPrf (.imp ph (.imp (syn_wa ps ch) th))) :
    Nominal.NPrf (.imp ph (.imp ps th)) :=
  by
  have p0000 := @g_a1i ch ph hyp_mpan2i_1
  have p0001 := @g_mpan2d ph ps ch th p0000 hyp_mpan2i_2
  exact p0001

@[expose]
noncomputable def g_mp2ani (ph : Wff) (ps : Wff) (ch : Wff) (th : Wff)
    (hyp_mp2ani_1 : Nominal.NPrf ps) (hyp_mp2ani_2 : Nominal.NPrf ch)
    (hyp_mp2ani_3 : Nominal.NPrf (.imp ph (.imp (syn_wa ps ch) th))) :
    Nominal.NPrf (.imp ph th) :=
  by
  have p0000 := @g_mpani ph ps ch th hyp_mp2ani_1 hyp_mp2ani_3
  have p0001 := @g_mpi ph ch th hyp_mp2ani_2 p0000
  exact p0001

@[expose]
noncomputable def g_mp2and (ph : Wff) (ps : Wff) (ch : Wff) (th : Wff)
    (hyp_mp2and_1 : Nominal.NPrf (.imp ph ps)) (hyp_mp2and_2 : Nominal.NPrf (.imp ph ch))
    (hyp_mp2and_3 : Nominal.NPrf (.imp ph (.imp (syn_wa ps ch) th))) :
    Nominal.NPrf (.imp ph th) :=
  by
  have p0000 := @g_mpand ph ps ch th hyp_mp2and_1 hyp_mp2and_3
  have p0001 := @g_mpd ph ch th hyp_mp2and_2 p0000
  exact p0001

@[expose]
noncomputable def g_mpanl1 (ph : Wff) (ps : Wff) (ch : Wff) (th : Wff)
    (hyp_mpanl1_1 : Nominal.NPrf ph)
    (hyp_mpanl1_2 : Nominal.NPrf (.imp (syn_wa (syn_wa ph ps) ch) th)) :
    Nominal.NPrf (.imp (syn_wa ps ch) th) :=
  by
  have p0000 := @g_jctl ps ph hyp_mpanl1_1
  have p0001 := @g_sylan ps (syn_wa ph ps) ch th p0000 hyp_mpanl1_2
  exact p0001

@[expose]
noncomputable def g_mpanl2 (ph : Wff) (ps : Wff) (ch : Wff) (th : Wff)
    (hyp_mpanl2_1 : Nominal.NPrf ps)
    (hyp_mpanl2_2 : Nominal.NPrf (.imp (syn_wa (syn_wa ph ps) ch) th)) :
    Nominal.NPrf (.imp (syn_wa ph ch) th) :=
  by
  have p0000 := @g_jctr ph ps hyp_mpanl2_1
  have p0001 := @g_sylan ph (syn_wa ph ps) ch th p0000 hyp_mpanl2_2
  exact p0001

@[expose]
noncomputable def g_mpanl12 (ph : Wff) (ps : Wff) (ch : Wff) (th : Wff)
    (hyp_mpanl12_1 : Nominal.NPrf ph) (hyp_mpanl12_2 : Nominal.NPrf ps)
    (hyp_mpanl12_3 : Nominal.NPrf (.imp (syn_wa (syn_wa ph ps) ch) th)) :
    Nominal.NPrf (.imp ch th) :=
  by
  have p0000 := @g_mpanl1 ph ps ch th hyp_mpanl12_1 hyp_mpanl12_3
  have p0001 := @g_mpan ps ch th hyp_mpanl12_2 p0000
  exact p0001

@[expose]
noncomputable def g_mpanr1 (ph : Wff) (ps : Wff) (ch : Wff) (th : Wff)
    (hyp_mpanr1_1 : Nominal.NPrf ps)
    (hyp_mpanr1_2 : Nominal.NPrf (.imp (syn_wa ph (syn_wa ps ch)) th)) :
    Nominal.NPrf (.imp (syn_wa ph ch) th) :=
  by
  have p0000 := @g_anassrs ph ps ch th hyp_mpanr1_2
  have p0001 := @g_mpanl2 ph ps ch th hyp_mpanr1_1 p0000
  exact p0001

@[expose]
noncomputable def g_mpanr2 (ph : Wff) (ps : Wff) (ch : Wff) (th : Wff)
    (hyp_mpanr2_1 : Nominal.NPrf ch)
    (hyp_mpanr2_2 : Nominal.NPrf (.imp (syn_wa ph (syn_wa ps ch)) th)) :
    Nominal.NPrf (.imp (syn_wa ph ps) th) :=
  by
  have p0000 := @g_jctr ps ch hyp_mpanr2_1
  have p0001 := @g_sylan2 ps ph (syn_wa ps ch) th p0000 hyp_mpanr2_2
  exact p0001

@[expose]
noncomputable def g_mpanr12 (ph : Wff) (ps : Wff) (ch : Wff) (th : Wff)
    (hyp_mpanr12_1 : Nominal.NPrf ps) (hyp_mpanr12_2 : Nominal.NPrf ch)
    (hyp_mpanr12_3 : Nominal.NPrf (.imp (syn_wa ph (syn_wa ps ch)) th)) :
    Nominal.NPrf (.imp ph th) :=
  by
  have p0000 := @g_mpanr1 ph ps ch th hyp_mpanr12_1 hyp_mpanr12_3
  have p0001 := @g_mpan2 ph ch th hyp_mpanr12_2 p0000
  exact p0001

@[expose]
noncomputable def g_pm5_74da (ph : Wff) (ps : Wff) (ch : Wff) (th : Wff)
    (hyp_pm5_74da_1 : Nominal.NPrf (.imp (syn_wa ph ps) (syn_wb ch th))) :
    Nominal.NPrf (.imp ph (syn_wb (.imp ps ch) (.imp ps th))) :=
  by
  have p0000 := @g_ex ph ps (syn_wb ch th) hyp_pm5_74da_1
  have p0001 := @g_pm5_74d ph ps ch th p0000
  exact p0001

@[expose]
noncomputable def g_imdistani (ph : Wff) (ps : Wff) (ch : Wff)
    (hyp_imdistani_1 : Nominal.NPrf (.imp ph (.imp ps ch))) :
    Nominal.NPrf (.imp (syn_wa ph ps) (syn_wa ph ch)) :=
  by
  have p0000 := @g_anc2li ph ps ch hyp_imdistani_1
  have p0001 := @g_imp ph ps (syn_wa ph ch) p0000
  exact p0001

@[expose]
noncomputable def g_anbi2i (ph : Wff) (ps : Wff) (ch : Wff)
    (hyp_bi_aa : Nominal.NPrf (syn_wb ph ps)) :
    Nominal.NPrf (syn_wb (syn_wa ch ph) (syn_wa ch ps)) :=
  by
  have p0000 := @g_a1i (syn_wb ph ps) ch hyp_bi_aa
  have p0001 := @g_pm5_32i ch ph ps p0000
  exact p0001

@[expose]
noncomputable def g_anbi1i (ph : Wff) (ps : Wff) (ch : Wff)
    (hyp_bi_aa : Nominal.NPrf (syn_wb ph ps)) :
    Nominal.NPrf (syn_wb (syn_wa ph ch) (syn_wa ps ch)) :=
  by
  have p0000 := @g_a1i (syn_wb ph ps) ch hyp_bi_aa
  have p0001 := @g_pm5_32ri ch ph ps p0000
  exact p0001

@[expose]
noncomputable def g_anbi2ci (ph : Wff) (ps : Wff) (ch : Wff)
    (hyp_bi_aa : Nominal.NPrf (syn_wb ph ps)) :
    Nominal.NPrf (syn_wb (syn_wa ph ch) (syn_wa ch ps)) :=
  by
  have p0000 := @g_anbi1i ph ps ch hyp_bi_aa
  have p0001 := @g_ancom ps ch
  have p0002 := @g_bitri (syn_wa ph ch) (syn_wa ps ch) (syn_wa ch ps) p0000 p0001
  exact p0002

@[expose]
noncomputable def g_anbi12i (ph : Wff) (ps : Wff) (ch : Wff) (th : Wff)
    (hyp_anbi12_1 : Nominal.NPrf (syn_wb ph ps))
    (hyp_anbi12_2 : Nominal.NPrf (syn_wb ch th)) :
    Nominal.NPrf (syn_wb (syn_wa ph ch) (syn_wa ps th)) :=
  by
  have p0000 := @g_anbi1i ph ps ch hyp_anbi12_1
  have p0001 := @g_anbi2i ch th ps hyp_anbi12_2
  have p0002 := @g_bitri (syn_wa ph ch) (syn_wa ps ch) (syn_wa ps th) p0000 p0001
  exact p0002

@[expose]
noncomputable def g_anbi12ci (ph : Wff) (ps : Wff) (ch : Wff) (th : Wff)
    (hyp_anbi12_1 : Nominal.NPrf (syn_wb ph ps))
    (hyp_anbi12_2 : Nominal.NPrf (syn_wb ch th)) :
    Nominal.NPrf (syn_wb (syn_wa ph ch) (syn_wa th ps)) :=
  by
  have p0000 := @g_anbi12i ph ps ch th hyp_anbi12_1 hyp_anbi12_2
  have p0001 := @g_ancom ps th
  have p0002 := @g_bitri (syn_wa ph ch) (syn_wa ps th) (syn_wa th ps) p0000 p0001
  exact p0002

@[expose]
noncomputable def g_sylan9bb (ph : Wff) (ps : Wff) (ch : Wff) (th : Wff) (ta : Wff)
    (hyp_sylan9bb_1 : Nominal.NPrf (.imp ph (syn_wb ps ch)))
    (hyp_sylan9bb_2 : Nominal.NPrf (.imp th (syn_wb ch ta))) :
    Nominal.NPrf (.imp (syn_wa ph th) (syn_wb ps ta)) :=
  by
  have p0000 := @g_adantr ph (syn_wb ps ch) th hyp_sylan9bb_1
  have p0001 := @g_adantl th (syn_wb ch ta) ph hyp_sylan9bb_2
  have p0002 := @g_bitrd (syn_wa ph th) ps ch ta p0000 p0001
  exact p0002

@[expose]
noncomputable def g_sylan9bbr (ph : Wff) (ps : Wff) (ch : Wff) (th : Wff) (ta : Wff)
    (hyp_sylan9bbr_1 : Nominal.NPrf (.imp ph (syn_wb ps ch)))
    (hyp_sylan9bbr_2 : Nominal.NPrf (.imp th (syn_wb ch ta))) :
    Nominal.NPrf (.imp (syn_wa th ph) (syn_wb ps ta)) :=
  by
  have p0000 := @g_sylan9bb ph ps ch th ta hyp_sylan9bbr_1 hyp_sylan9bbr_2
  have p0001 := @g_ancoms ph th (syn_wb ps ta) p0000
  exact p0001

@[expose]
noncomputable def g_orbi2d (ph : Wff) (ps : Wff) (ch : Wff) (th : Wff)
    (hyp_bid_1 : Nominal.NPrf (.imp ph (syn_wb ps ch))) :
    Nominal.NPrf (.imp ph (syn_wb (syn_wo th ps) (syn_wo th ch))) :=
  by
  have p0000 := @g_imbi2d ph ps ch (.neg th) hyp_bid_1
  have p0001 := (Nominal.biimpRefl (syn_wo th ps))
  have p0002 := (Nominal.biimpRefl (syn_wo th ch))
  have p0003 :=
    @g_n_3bitr4g ph (.imp (.neg th) ps) (.imp (.neg th) ch) (syn_wo th ps) (syn_wo th ch)
      p0000 p0001 p0002
  exact p0003

@[expose]
noncomputable def g_orbi1d (ph : Wff) (ps : Wff) (ch : Wff) (th : Wff)
    (hyp_bid_1 : Nominal.NPrf (.imp ph (syn_wb ps ch))) :
    Nominal.NPrf (.imp ph (syn_wb (syn_wo ps th) (syn_wo ch th))) :=
  by
  have p0000 := @g_orbi2d ph ps ch th hyp_bid_1
  have p0001 := @g_orcom ps th
  have p0002 := @g_orcom ch th
  have p0003 :=
    @g_n_3bitr4g ph (syn_wo th ps) (syn_wo th ch) (syn_wo ps th) (syn_wo ch th) p0000
      p0001 p0002
  exact p0003

@[expose]
noncomputable def g_anbi2d (ph : Wff) (ps : Wff) (ch : Wff) (th : Wff)
    (hyp_bid_1 : Nominal.NPrf (.imp ph (syn_wb ps ch))) :
    Nominal.NPrf (.imp ph (syn_wb (syn_wa th ps) (syn_wa th ch))) :=
  by
  have p0000 := @g_a1d ph (syn_wb ps ch) th hyp_bid_1
  have p0001 := @g_pm5_32d ph th ps ch p0000
  exact p0001

@[expose]
noncomputable def g_anbi1d (ph : Wff) (ps : Wff) (ch : Wff) (th : Wff)
    (hyp_bid_1 : Nominal.NPrf (.imp ph (syn_wb ps ch))) :
    Nominal.NPrf (.imp ph (syn_wb (syn_wa ps th) (syn_wa ch th))) :=
  by
  have p0000 := @g_a1d ph (syn_wb ps ch) th hyp_bid_1
  have p0001 := @g_pm5_32rd ph th ps ch p0000
  exact p0001

@[expose]
noncomputable def g_anbi1 (ph : Wff) (ps : Wff) (ch : Wff) :
    Nominal.NPrf (.imp (syn_wb ph ps) (syn_wb (syn_wa ph ch) (syn_wa ps ch))) :=
  by
  have p0000 := @g_id (syn_wb ph ps)
  have p0001 := @g_anbi1d (syn_wb ph ps) ph ps ch p0000
  exact p0001

@[expose]
noncomputable def g_orbi12d (ph : Wff) (ps : Wff) (ch : Wff) (th : Wff) (ta : Wff)
    (hyp_bi12d_1 : Nominal.NPrf (.imp ph (syn_wb ps ch)))
    (hyp_bi12d_2 : Nominal.NPrf (.imp ph (syn_wb th ta))) :
    Nominal.NPrf (.imp ph (syn_wb (syn_wo ps th) (syn_wo ch ta))) :=
  by
  have p0000 := @g_orbi1d ph ps ch th hyp_bi12d_1
  have p0001 := @g_orbi2d ph th ta ch hyp_bi12d_2
  have p0002 := @g_bitrd ph (syn_wo ps th) (syn_wo ch th) (syn_wo ch ta) p0000 p0001
  exact p0002

@[expose]
noncomputable def g_anbi12d (ph : Wff) (ps : Wff) (ch : Wff) (th : Wff) (ta : Wff)
    (hyp_bi12d_1 : Nominal.NPrf (.imp ph (syn_wb ps ch)))
    (hyp_bi12d_2 : Nominal.NPrf (.imp ph (syn_wb th ta))) :
    Nominal.NPrf (.imp ph (syn_wb (syn_wa ps th) (syn_wa ch ta))) :=
  by
  have p0000 := @g_anbi1d ph ps ch th hyp_bi12d_1
  have p0001 := @g_anbi2d ph th ta ch hyp_bi12d_2
  have p0002 := @g_bitrd ph (syn_wa ps th) (syn_wa ch th) (syn_wa ch ta) p0000 p0001
  exact p0002

@[expose]
noncomputable def g_pm5_61 (ph : Wff) (ps : Wff) :
    Nominal.NPrf (syn_wb (syn_wa (syn_wo ph ps) (.neg ps)) (syn_wa ph (.neg ps))) :=
  by
  have p0000 := @g_biorf ps ph
  have p0001 := @g_orcom ps ph
  have p0002 := @g_syl6rbb (.neg ps) ph (syn_wo ps ph) (syn_wo ph ps) p0000 p0001
  have p0003 := @g_pm5_32ri (.neg ps) (syn_wo ph ps) ph p0002
  exact p0003

@[expose]
noncomputable def g_adantll (ph : Wff) (ps : Wff) (ch : Wff) (th : Wff)
    (hyp_adant2_1 : Nominal.NPrf (.imp (syn_wa ph ps) ch)) :
    Nominal.NPrf (.imp (syn_wa (syn_wa th ph) ps) ch) :=
  by
  have p0000 := @g_simpr th ph
  have p0001 := @g_sylan (syn_wa th ph) ph ps ch p0000 hyp_adant2_1
  exact p0001

@[expose]
noncomputable def g_adantlr (ph : Wff) (ps : Wff) (ch : Wff) (th : Wff)
    (hyp_adant2_1 : Nominal.NPrf (.imp (syn_wa ph ps) ch)) :
    Nominal.NPrf (.imp (syn_wa (syn_wa ph th) ps) ch) :=
  by
  have p0000 := @g_simpl ph th
  have p0001 := @g_sylan (syn_wa ph th) ph ps ch p0000 hyp_adant2_1
  exact p0001

@[expose]
noncomputable def g_adantrl (ph : Wff) (ps : Wff) (ch : Wff) (th : Wff)
    (hyp_adant2_1 : Nominal.NPrf (.imp (syn_wa ph ps) ch)) :
    Nominal.NPrf (.imp (syn_wa ph (syn_wa th ps)) ch) :=
  by
  have p0000 := @g_simpr th ps
  have p0001 := @g_sylan2 (syn_wa th ps) ph ps ch p0000 hyp_adant2_1
  exact p0001

@[expose]
noncomputable def g_adantrr (ph : Wff) (ps : Wff) (ch : Wff) (th : Wff)
    (hyp_adant2_1 : Nominal.NPrf (.imp (syn_wa ph ps) ch)) :
    Nominal.NPrf (.imp (syn_wa ph (syn_wa ps th)) ch) :=
  by
  have p0000 := @g_simpl ps th
  have p0001 := @g_sylan2 (syn_wa ps th) ph ps ch p0000 hyp_adant2_1
  exact p0001

@[expose]
noncomputable def g_adantllr (ph : Wff) (ps : Wff) (ch : Wff) (th : Wff) (ta : Wff)
    (hyp_adantl2_1 : Nominal.NPrf (.imp (syn_wa (syn_wa ph ps) ch) th)) :
    Nominal.NPrf (.imp (syn_wa (syn_wa (syn_wa ph ta) ps) ch) th) :=
  by
  have p0000 := @g_simpl ph ta
  have p0001 := @g_sylanl1 (syn_wa ph ta) ph ps ch th p0000 hyp_adantl2_1
  exact p0001

@[expose]
noncomputable def g_adantlrr (ph : Wff) (ps : Wff) (ch : Wff) (th : Wff) (ta : Wff)
    (hyp_adantl2_1 : Nominal.NPrf (.imp (syn_wa (syn_wa ph ps) ch) th)) :
    Nominal.NPrf (.imp (syn_wa (syn_wa ph (syn_wa ps ta)) ch) th) :=
  by
  have p0000 := @g_simpl ps ta
  have p0001 := @g_sylanl2 (syn_wa ps ta) ph ps ch th p0000 hyp_adantl2_1
  exact p0001

@[expose]
noncomputable def g_ad2antrr (ph : Wff) (ps : Wff) (ch : Wff) (th : Wff)
    (hyp_ad2ant_1 : Nominal.NPrf (.imp ph ps)) :
    Nominal.NPrf (.imp (syn_wa (syn_wa ph ch) th) ps) :=
  by
  have p0000 := @g_adantr ph ps th hyp_ad2ant_1
  have p0001 := @g_adantlr ph th ps ch p0000
  exact p0001

@[expose]
noncomputable def g_ad2antlr (ph : Wff) (ps : Wff) (ch : Wff) (th : Wff)
    (hyp_ad2ant_1 : Nominal.NPrf (.imp ph ps)) :
    Nominal.NPrf (.imp (syn_wa (syn_wa ch ph) th) ps) :=
  by
  have p0000 := @g_adantr ph ps th hyp_ad2ant_1
  have p0001 := @g_adantll ph th ps ch p0000
  exact p0001

@[expose]
noncomputable def g_ad2antrl (ph : Wff) (ps : Wff) (ch : Wff) (th : Wff)
    (hyp_ad2ant_1 : Nominal.NPrf (.imp ph ps)) :
    Nominal.NPrf (.imp (syn_wa ch (syn_wa ph th)) ps) :=
  by
  have p0000 := @g_adantr ph ps th hyp_ad2ant_1
  have p0001 := @g_adantl (syn_wa ph th) ps ch p0000
  exact p0001

@[expose]
noncomputable def g_ad2antll (ph : Wff) (ps : Wff) (ch : Wff) (th : Wff)
    (hyp_ad2ant_1 : Nominal.NPrf (.imp ph ps)) :
    Nominal.NPrf (.imp (syn_wa ch (syn_wa th ph)) ps) :=
  by
  have p0000 := @g_adantl ph ps th hyp_ad2ant_1
  have p0001 := @g_adantl (syn_wa th ph) ps ch p0000
  exact p0001


end NFChoice.DirectNominalPrf.WPPReplay
