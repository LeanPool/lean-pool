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

/-- Checked nominal proof certificate identified upstream as `g_pm5_5`. -/
@[expose]
noncomputable def gPm55 (ph : Wff) (ps : Wff) :
    Nominal.NPrf (.imp ph (synWb (.imp ph ps) ps)) :=
  by
  have p0000 := @gBiimt ph ps
  have p0001 := @gBicomd ph ps (.imp ph ps) p0000
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_a1bi`. -/
@[expose]
noncomputable def gA1bi (ph : Wff) (ps : Wff) (hyp_a1bi_1 : Nominal.NPrf ph) :
    Nominal.NPrf (synWb ps (.imp ph ps)) :=
  by
  have p0000 := @gBiimt ph ps
  have p0001 := Nominal.mp hyp_a1bi_1 p0000
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_pm5_501`. -/
@[expose]
noncomputable def gPm5501 (ph : Wff) (ps : Wff) :
    Nominal.NPrf (.imp ph (synWb ps (synWb ph ps))) :=
  by
  have p0000 := @gPm51im ph ps
  have p0001 := @gBi1 ph ps
  have p0002 := @gCom12 (synWb ph ps) ph ps p0001
  have p0003 := @gImpbid ph ps (synWb ph ps) p0000 p0002
  exact p0003

/-- Checked nominal proof certificate identified upstream as `g_ibibr`. -/
@[expose]
noncomputable def gIbibr (ph : Wff) (ps : Wff) :
    Nominal.NPrf (synWb (.imp ph ps) (.imp ph (synWb ps ph))) :=
  by
  have p0000 := @gPm5501 ph ps
  have p0001 := @gBicom ph ps
  have p0002 := @gSyl6bb ph ps (synWb ph ps) (synWb ps ph) p0000 p0001
  have p0003 := @gPm574i ph ps (synWb ps ph) p0002
  exact p0003

/-- Checked nominal proof certificate identified upstream as `g_tbt`. -/
@[expose]
noncomputable def gTbt (ph : Wff) (ps : Wff) (hyp_tbt_1 : Nominal.NPrf ph) :
    Nominal.NPrf (synWb ps (synWb ps ph)) :=
  by
  have p0000 := @gIbibr ph ps
  have p0001 := @gPm574ri ph ps (synWb ps ph) p0000
  have p0002 := Nominal.mp hyp_tbt_1 p0001
  exact p0002

/-- Checked nominal proof certificate identified upstream as `g_nbn2`. -/
@[expose]
noncomputable def gNbn2 (ph : Wff) (ps : Wff) :
    Nominal.NPrf (.imp (.neg ph) (synWb (.neg ps) (synWb ph ps))) :=
  by
  have p0000 := @gPm5501 (.neg ph) (.neg ps)
  have p0001 := @gNotbi ph ps
  have p0002 :=
    @gSyl6bbr (.neg ph) (.neg ps) (synWb (.neg ph) (.neg ps)) (synWb ph ps) p0000 p0001
  exact p0002

/-- Checked nominal proof certificate identified upstream as `g_bibif`. -/
@[expose]
noncomputable def gBibif (ph : Wff) (ps : Wff) :
    Nominal.NPrf (.imp (.neg ps) (synWb (synWb ph ps) (.neg ph))) :=
  by
  have p0000 := @gNbn2 ps ph
  have p0001 := @gBicom ps ph
  have p0002 := @gSyl6rbb (.neg ps) (.neg ph) (synWb ps ph) (synWb ph ps) p0000 p0001
  exact p0002

/-- Checked nominal proof certificate identified upstream as `g_nbn`. -/
@[expose]
noncomputable def gNbn (ph : Wff) (ps : Wff) (hyp_nbn_1 : Nominal.NPrf (.neg ph)) :
    Nominal.NPrf (synWb (.neg ps) (synWb ps ph)) :=
  by
  have p0000 := @gBibif ps ph
  have p0001 := Nominal.mp hyp_nbn_1 p0000
  have p0002 := @gBicomi (synWb ps ph) (.neg ps) p0001
  exact p0002

/-- Checked nominal proof certificate identified upstream as `g_pm5_21im`. -/
@[expose]
noncomputable def gPm521im (ph : Wff) (ps : Wff) :
    Nominal.NPrf (.imp (.neg ph) (.imp (.neg ps) (synWb ph ps))) :=
  by
  have p0000 := @gNbn2 ph ps
  have p0001 := @gBiimpd (.neg ph) (.neg ps) (synWb ph ps) p0000
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_n_2false`. -/
@[expose]
noncomputable def gN2false (ph : Wff) (ps : Wff)
    (hyp_n_2false_1 : Nominal.NPrf (.neg ph)) (hyp_n_2false_2 : Nominal.NPrf (.neg ps)) :
    Nominal.NPrf (synWb ph ps) :=
  by
  have p0000 := @gN2th (.neg ph) (.neg ps) hyp_n_2false_1 hyp_n_2false_2
  have p0001 := @gCon4bii ph ps p0000
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_n_2falsed`. -/
@[expose]
noncomputable def gN2falsed (ph : Wff) (ps : Wff) (ch : Wff)
    (hyp_n_2falsed_1 : Nominal.NPrf (.imp ph (.neg ps)))
    (hyp_n_2falsed_2 : Nominal.NPrf (.imp ph (.neg ch))) :
    Nominal.NPrf (.imp ph (synWb ps ch)) :=
  by
  have p0000 := @gPm221d ph ps ch hyp_n_2falsed_1
  have p0001 := @gPm221d ph ch ps hyp_n_2falsed_2
  have p0002 := @gImpbid ph ps ch p0000 p0001
  exact p0002

/-- Checked nominal proof certificate identified upstream as `g_pm5_21ni`. -/
@[expose]
noncomputable def gPm521ni (ph : Wff) (ps : Wff) (ch : Wff)
    (hyp_pm5_21ni_1 : Nominal.NPrf (.imp ph ps))
    (hyp_pm5_21ni_2 : Nominal.NPrf (.imp ch ps)) :
    Nominal.NPrf (.imp (.neg ps) (synWb ph ch)) :=
  by
  have p0000 := @gCon3i ph ps hyp_pm5_21ni_1
  have p0001 := @gCon3i ch ps hyp_pm5_21ni_2
  have p0002 := @gN2falsed (.neg ps) ph ch p0000 p0001
  exact p0002

/-- Checked nominal proof certificate identified upstream as `g_pm5_21nii`. -/
@[expose]
noncomputable def gPm521nii (ph : Wff) (ps : Wff) (ch : Wff)
    (hyp_pm5_21ni_1 : Nominal.NPrf (.imp ph ps))
    (hyp_pm5_21ni_2 : Nominal.NPrf (.imp ch ps))
    (hyp_pm5_21nii_3 : Nominal.NPrf (.imp ps (synWb ph ch))) :
    Nominal.NPrf (synWb ph ch) :=
  by
  have p0000 := @gPm521ni ph ps ch hyp_pm5_21ni_1 hyp_pm5_21ni_2
  have p0001 := @gPm261i ps (synWb ph ch) hyp_pm5_21nii_3 p0000
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_pm5_21ndd`. -/
@[expose]
noncomputable def gPm521ndd (ph : Wff) (ps : Wff) (ch : Wff) (th : Wff)
    (hyp_pm5_21ndd_1 : Nominal.NPrf (.imp ph (.imp ch ps)))
    (hyp_pm5_21ndd_2 : Nominal.NPrf (.imp ph (.imp th ps)))
    (hyp_pm5_21ndd_3 : Nominal.NPrf (.imp ph (.imp ps (synWb ch th)))) :
    Nominal.NPrf (.imp ph (synWb ch th)) :=
  by
  have p0000 := @gCon3d ph ch ps hyp_pm5_21ndd_1
  have p0001 := @gCon3d ph th ps hyp_pm5_21ndd_2
  have p0002 := @gPm521im ch th
  have p0003 := @gSyl6c ph (.neg ps) (.neg ch) (.neg th) (synWb ch th) p0000 p0001 p0002
  have p0004 := @gPm261d ph ps (synWb ch th) hyp_pm5_21ndd_3 p0003
  exact p0004

/-- Checked nominal proof certificate identified upstream as `g_pm5_18`. -/
@[expose]
noncomputable def gPm518 (ph : Wff) (ps : Wff) :
    Nominal.NPrf (synWb (synWb ph ps) (.neg (synWb ph (.neg ps)))) :=
  by
  have p0000 := @gPm5501 ph (.neg ps)
  have p0001 := @gCon1bid ph ps (synWb ph (.neg ps)) p0000
  have p0002 := @gPm5501 ph ps
  have p0003 := @gBitr2d ph (.neg (synWb ph (.neg ps))) ps (synWb ph ps) p0001 p0002
  have p0004 := @gNbn2 ph (.neg ps)
  have p0005 := @gCon1bid (.neg ph) (.neg ps) (synWb ph (.neg ps)) p0004
  have p0006 := @gNbn2 ph ps
  have p0007 :=
    @gBitr2d (.neg ph) (.neg (synWb ph (.neg ps))) (.neg ps) (synWb ph ps) p0005 p0006
  have p0008 :=
    @gPm261i ph (synWb (synWb ph ps) (.neg (synWb ph (.neg ps)))) p0003 p0007
  exact p0008

/-- Checked nominal proof certificate identified upstream as `g_pm5_19`. -/
@[expose]
noncomputable def gPm519 (ph : Wff) : Nominal.NPrf (.neg (synWb ph (.neg ph))) :=
  by
  have p0000 := @gBiid ph
  have p0001 := @gPm518 ph ph
  have p0002 := @gMpbi (synWb ph ph) (.neg (synWb ph (.neg ph))) p0000 p0001
  exact p0002

/-- Checked nominal proof certificate identified upstream as `g_bi2_04`. -/
@[expose]
noncomputable def gBi204 (ph : Wff) (ps : Wff) (ch : Wff) :
    Nominal.NPrf (synWb (.imp ph (.imp ps ch)) (.imp ps (.imp ph ch))) :=
  by
  have p0000 := @gPm204 ph ps ch
  have p0001 := @gPm204 ps ph ch
  have p0002 := @gImpbii (.imp ph (.imp ps ch)) (.imp ps (.imp ph ch)) p0000 p0001
  exact p0002

/-- Checked nominal proof certificate identified upstream as `g_pm4_64`. -/
@[expose]
noncomputable def gPm464 (ph : Wff) (ps : Wff) :
    Nominal.NPrf (synWb (.imp (.neg ph) ps) (synWo ph ps)) :=
  by
  have p0000 := (Nominal.biimpRefl (synWo ph ps))
  have p0001 := @gBicomi (synWo ph ps) (.imp (.neg ph) ps) p0000
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_pm2_53`. -/
@[expose]
noncomputable def gPm253 (ph : Wff) (ps : Wff) :
    Nominal.NPrf (.imp (synWo ph ps) (.imp (.neg ph) ps)) :=
  by
  have p0000 := (Nominal.biimpRefl (synWo ph ps))
  have p0001 := @gBiimpi (synWo ph ps) (.imp (.neg ph) ps) p0000
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_pm2_54`. -/
@[expose]
noncomputable def gPm254 (ph : Wff) (ps : Wff) :
    Nominal.NPrf (.imp (.imp (.neg ph) ps) (synWo ph ps)) :=
  by
  have p0000 := (Nominal.biimpRefl (synWo ph ps))
  have p0001 := @gBiimpri (synWo ph ps) (.imp (.neg ph) ps) p0000
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_ori`. -/
@[expose]
noncomputable def gOri (ph : Wff) (ps : Wff) (hyp_ori_1 : Nominal.NPrf (synWo ph ps)) :
    Nominal.NPrf (.imp (.neg ph) ps) :=
  by
  have p0000 := (Nominal.biimpRefl (synWo ph ps))
  have p0001 := @gMpbi (synWo ph ps) (.imp (.neg ph) ps) hyp_ori_1 p0000
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_orri`. -/
@[expose]
noncomputable def gOrri (ph : Wff) (ps : Wff)
    (hyp_orri_1 : Nominal.NPrf (.imp (.neg ph) ps)) : Nominal.NPrf (synWo ph ps) :=
  by
  have p0000 := (Nominal.biimpRefl (synWo ph ps))
  have p0001 := @gMpbir (synWo ph ps) (.imp (.neg ph) ps) hyp_orri_1 p0000
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_ord`. -/
@[expose]
noncomputable def gOrd (ph : Wff) (ps : Wff) (ch : Wff)
    (hyp_ord_1 : Nominal.NPrf (.imp ph (synWo ps ch))) :
    Nominal.NPrf (.imp ph (.imp (.neg ps) ch)) :=
  by
  have p0000 := (Nominal.biimpRefl (synWo ps ch))
  have p0001 := @gSylib ph (synWo ps ch) (.imp (.neg ps) ch) hyp_ord_1 p0000
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_orrd`. -/
@[expose]
noncomputable def gOrrd (ph : Wff) (ps : Wff) (ch : Wff)
    (hyp_orrd_1 : Nominal.NPrf (.imp ph (.imp (.neg ps) ch))) :
    Nominal.NPrf (.imp ph (synWo ps ch)) :=
  by
  have p0000 := @gPm254 ps ch
  have p0001 := @gSyl ph (.imp (.neg ps) ch) (synWo ps ch) hyp_orrd_1 p0000
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_jaoi`. -/
@[expose]
noncomputable def gJaoi (ph : Wff) (ps : Wff) (ch : Wff)
    (hyp_jaoi_1 : Nominal.NPrf (.imp ph ps)) (hyp_jaoi_2 : Nominal.NPrf (.imp ch ps)) :
    Nominal.NPrf (.imp (synWo ph ch) ps) :=
  by
  have p0000 := @gPm253 ph ch
  have p0001 := @gSyl6 (synWo ph ch) (.neg ph) ch ps p0000 hyp_jaoi_2
  have p0002 := @gPm261d2 (synWo ph ch) ph ps p0001 hyp_jaoi_1
  exact p0002

/-- Checked nominal proof certificate identified upstream as `g_jaod`. -/
@[expose]
noncomputable def gJaod (ph : Wff) (ps : Wff) (ch : Wff) (th : Wff)
    (hyp_jaod_1 : Nominal.NPrf (.imp ph (.imp ps ch)))
    (hyp_jaod_2 : Nominal.NPrf (.imp ph (.imp th ch))) :
    Nominal.NPrf (.imp ph (.imp (synWo ps th) ch)) :=
  by
  have p0000 := @gCom12 ph ps ch hyp_jaod_1
  have p0001 := @gCom12 ph th ch hyp_jaod_2
  have p0002 := @gJaoi ps (.imp ph ch) th p0000 p0001
  have p0003 := @gCom12 (synWo ps th) ph ch p0002
  exact p0003

/-- Checked nominal proof certificate identified upstream as `g_mpjaod`. -/
@[expose]
noncomputable def gMpjaod (ph : Wff) (ps : Wff) (ch : Wff) (th : Wff)
    (hyp_jaod_1 : Nominal.NPrf (.imp ph (.imp ps ch)))
    (hyp_jaod_2 : Nominal.NPrf (.imp ph (.imp th ch)))
    (hyp_jaod_3 : Nominal.NPrf (.imp ph (synWo ps th))) : Nominal.NPrf (.imp ph ch) :=
  by
  have p0000 := @gJaod ph ps ch th hyp_jaod_1 hyp_jaod_2
  have p0001 := @gMpd ph (synWo ps th) ch hyp_jaod_3 p0000
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_orel1`. -/
@[expose]
noncomputable def gOrel1 (ph : Wff) (ps : Wff) :
    Nominal.NPrf (.imp (.neg ph) (.imp (synWo ph ps) ps)) :=
  by
  have p0000 := @gPm253 ph ps
  have p0001 := @gCom12 (synWo ph ps) (.neg ph) ps p0000
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_orel2`. -/
@[expose]
noncomputable def gOrel2 (ph : Wff) (ps : Wff) :
    Nominal.NPrf (.imp (.neg ph) (.imp (synWo ps ph) ps)) :=
  by
  have p0000 := @gIdd (.neg ph) ps
  have p0001 := @gPm221 ph ps
  have p0002 := @gJaod (.neg ph) ps ps ph p0000 p0001
  exact p0002

/-- Checked nominal proof certificate identified upstream as `g_olc`. -/
@[expose]
noncomputable def gOlc (ph : Wff) (ps : Wff) : Nominal.NPrf (.imp ph (synWo ps ph)) :=
  by
  have p0000 := Nominal.ax1 ph (.neg ps)
  have p0001 := @gOrrd ph ps ph p0000
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_orc`. -/
@[expose]
noncomputable def gOrc (ph : Wff) (ps : Wff) : Nominal.NPrf (.imp ph (synWo ph ps)) :=
  by
  have p0000 := @gPm224 ph ps
  have p0001 := @gOrrd ph ph ps p0000
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_pm1_4`. -/
@[expose]
noncomputable def gPm14 (ph : Wff) (ps : Wff) :
    Nominal.NPrf (.imp (synWo ph ps) (synWo ps ph)) :=
  by
  have p0000 := @gOlc ph ps
  have p0001 := @gOrc ps ph
  have p0002 := @gJaoi ph (synWo ps ph) ps p0000 p0001
  exact p0002

/-- Checked nominal proof certificate identified upstream as `g_orcom`. -/
@[expose]
noncomputable def gOrcom (ph : Wff) (ps : Wff) :
    Nominal.NPrf (synWb (synWo ph ps) (synWo ps ph)) :=
  by
  have p0000 := @gPm14 ph ps
  have p0001 := @gPm14 ps ph
  have p0002 := @gImpbii (synWo ph ps) (synWo ps ph) p0000 p0001
  exact p0002

/-- Checked nominal proof certificate identified upstream as `g_orcomd`. -/
@[expose]
noncomputable def gOrcomd (ph : Wff) (ps : Wff) (ch : Wff)
    (hyp_orcomd_1 : Nominal.NPrf (.imp ph (synWo ps ch))) :
    Nominal.NPrf (.imp ph (synWo ch ps)) :=
  by
  have p0000 := @gOrcom ps ch
  have p0001 := @gSylib ph (synWo ps ch) (synWo ch ps) hyp_orcomd_1 p0000
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_orci`. -/
@[expose]
noncomputable def gOrci (ph : Wff) (ps : Wff) (hyp_orci_1 : Nominal.NPrf ph) :
    Nominal.NPrf (synWo ph ps) :=
  by
  have p0000 := @gPm224i ph ps hyp_orci_1
  have p0001 := @gOrri ph ps p0000
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_orcd`. -/
@[expose]
noncomputable def gOrcd (ph : Wff) (ps : Wff) (ch : Wff)
    (hyp_orcd_1 : Nominal.NPrf (.imp ph ps)) : Nominal.NPrf (.imp ph (synWo ps ch)) :=
  by
  have p0000 := @gOrc ps ch
  have p0001 := @gSyl ph ps (synWo ps ch) hyp_orcd_1 p0000
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_olcd`. -/
@[expose]
noncomputable def gOlcd (ph : Wff) (ps : Wff) (ch : Wff)
    (hyp_orcd_1 : Nominal.NPrf (.imp ph ps)) : Nominal.NPrf (.imp ph (synWo ch ps)) :=
  by
  have p0000 := @gOrcd ph ps ch hyp_orcd_1
  have p0001 := @gOrcomd ph ps ch p0000
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_pm2_07`. -/
@[expose]
noncomputable def gPm207 (ph : Wff) : Nominal.NPrf (.imp ph (synWo ph ph)) :=
  by
  have p0000 := @gOlc ph ph
  exact p0000

/-- Checked nominal proof certificate identified upstream as `g_pm2_67_2`. -/
@[expose]
noncomputable def g_pm2_67_2 (ph : Wff) (ps : Wff) (ch : Wff) :
    Nominal.NPrf (.imp (.imp (synWo ph ch) ps) (.imp ph ps)) :=
  by
  have p0000 := @gOrc ph ch
  have p0001 := @gImim1i ph (synWo ph ch) ps p0000
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_biorf`. -/
@[expose]
noncomputable def gBiorf (ph : Wff) (ps : Wff) :
    Nominal.NPrf (.imp (.neg ph) (synWb ps (synWo ph ps))) :=
  by
  have p0000 := @gOlc ps ph
  have p0001 := @gOrel1 ph ps
  have p0002 := @gImpbid2 (.neg ph) ps (synWo ph ps) p0000 p0001
  exact p0002

/-- Checked nominal proof certificate identified upstream as `g_biorfi`. -/
@[expose]
noncomputable def gBiorfi (ph : Wff) (ps : Wff) (hyp_biorfi_1 : Nominal.NPrf (.neg ph)) :
    Nominal.NPrf (synWb ps (synWo ps ph)) :=
  by
  have p0000 := @gOrc ps ph
  have p0001 := @gOrel2 ph ps
  have p0002 := @gImpbid2 (.neg ph) ps (synWo ps ph) p0000 p0001
  have p0003 := Nominal.mp hyp_biorfi_1 p0002
  exact p0003

/-- Checked nominal proof certificate identified upstream as `g_pm2_621`. -/
@[expose]
noncomputable def gPm2621 (ph : Wff) (ps : Wff) :
    Nominal.NPrf (.imp (.imp ph ps) (.imp (synWo ph ps) ps)) :=
  by
  have p0000 := @gId (.imp ph ps)
  have p0001 := @gIdd (.imp ph ps) ps
  have p0002 := @gJaod (.imp ph ps) ph ps ps p0000 p0001
  exact p0002

/-- Checked nominal proof certificate identified upstream as `g_imor`. -/
@[expose]
noncomputable def gImor (ph : Wff) (ps : Wff) :
    Nominal.NPrf (synWb (.imp ph ps) (synWo (.neg ph) ps)) :=
  by
  have p0000 := @gNotnot ph
  have p0001 := @gImbi1i ph (.neg (.neg ph)) ps p0000
  have p0002 := (Nominal.biimpRefl (synWo (.neg ph) ps))
  have p0003 :=
    @gBitr4i (.imp ph ps) (.imp (.neg (.neg ph)) ps) (synWo (.neg ph) ps) p0001 p0002
  exact p0003

/-- Checked nominal proof certificate identified upstream as `g_exmid`. -/
@[expose]
noncomputable def gExmid (ph : Wff) : Nominal.NPrf (synWo ph (.neg ph)) :=
  by
  have p0000 := @gId (.neg ph)
  have p0001 := @gOrri ph (.neg ph) p0000
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_pm4_62`. -/
@[expose]
noncomputable def gPm462 (ph : Wff) (ps : Wff) :
    Nominal.NPrf (synWb (.imp ph (.neg ps)) (synWo (.neg ph) (.neg ps))) :=
  by
  have p0000 := @gImor ph (.neg ps)
  exact p0000

/-- Checked nominal proof certificate identified upstream as `g_imnan`. -/
@[expose]
noncomputable def gImnan (ph : Wff) (ps : Wff) :
    Nominal.NPrf (synWb (.imp ph (.neg ps)) (.neg (synWa ph ps))) :=
  by
  have p0000 := (Nominal.biimpRefl (synWa ph ps))
  have p0001 := @gCon2bii (synWa ph ps) (.imp ph (.neg ps)) p0000
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_iman`. -/
@[expose]
noncomputable def gIman (ph : Wff) (ps : Wff) :
    Nominal.NPrf (synWb (.imp ph ps) (.neg (synWa ph (.neg ps)))) :=
  by
  have p0000 := @gNotnot ps
  have p0001 := @gImbi2i ps (.neg (.neg ps)) ph p0000
  have p0002 := @gImnan ph (.neg ps)
  have p0003 :=
    @gBitri (.imp ph ps) (.imp ph (.neg (.neg ps))) (.neg (synWa ph (.neg ps))) p0001
      p0002
  exact p0003

/-- Checked nominal proof certificate identified upstream as `g_annim`. -/
@[expose]
noncomputable def gAnnim (ph : Wff) (ps : Wff) :
    Nominal.NPrf (synWb (synWa ph (.neg ps)) (.neg (.imp ph ps))) :=
  by
  have p0000 := @gIman ph ps
  have p0001 := @gCon2bii (.imp ph ps) (synWa ph (.neg ps)) p0000
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_pm4_61`. -/
@[expose]
noncomputable def gPm461 (ph : Wff) (ps : Wff) :
    Nominal.NPrf (synWb (.neg (.imp ph ps)) (synWa ph (.neg ps))) :=
  by
  have p0000 := @gAnnim ph ps
  have p0001 := @gBicomi (synWa ph (.neg ps)) (.neg (.imp ph ps)) p0000
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_pm4_65`. -/
@[expose]
noncomputable def gPm465 (ph : Wff) (ps : Wff) :
    Nominal.NPrf (synWb (.neg (.imp (.neg ph) ps)) (synWa (.neg ph) (.neg ps))) :=
  by
  have p0000 := @gPm461 (.neg ph) ps
  exact p0000

/-- Checked nominal proof certificate identified upstream as `g_imp`. -/
@[expose]
noncomputable def gImp (ph : Wff) (ps : Wff) (ch : Wff)
    (hyp_imp_1 : Nominal.NPrf (.imp ph (.imp ps ch))) :
    Nominal.NPrf (.imp (synWa ph ps) ch) :=
  by
  have p0000 := (Nominal.biimpRefl (synWa ph ps))
  have p0001 := @gImpi ph ps ch hyp_imp_1
  have p0002 := @gSylbi (synWa ph ps) (.neg (.imp ph (.neg ps))) ch p0000 p0001
  exact p0002

/-- Checked nominal proof certificate identified upstream as `g_impcom`. -/
@[expose]
noncomputable def gImpcom (ph : Wff) (ps : Wff) (ch : Wff)
    (hyp_imp_1 : Nominal.NPrf (.imp ph (.imp ps ch))) :
    Nominal.NPrf (.imp (synWa ps ph) ch) :=
  by
  have p0000 := @gCom12 ph ps ch hyp_imp_1
  have p0001 := @gImp ps ph ch p0000
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_imp3a`. -/
@[expose]
noncomputable def gImp3a (ph : Wff) (ps : Wff) (ch : Wff) (th : Wff)
    (hyp_imp3_1 : Nominal.NPrf (.imp ph (.imp ps (.imp ch th)))) :
    Nominal.NPrf (.imp ph (.imp (synWa ps ch) th)) :=
  by
  have p0000 := @gCom3l ph ps ch th hyp_imp3_1
  have p0001 := @gImp ps ch (.imp ph th) p0000
  have p0002 := @gCom12 (synWa ps ch) ph th p0001
  exact p0002

/-- Checked nominal proof certificate identified upstream as `g_imp31`. -/
@[expose]
noncomputable def gImp31 (ph : Wff) (ps : Wff) (ch : Wff) (th : Wff)
    (hyp_imp3_1 : Nominal.NPrf (.imp ph (.imp ps (.imp ch th)))) :
    Nominal.NPrf (.imp (synWa (synWa ph ps) ch) th) :=
  by
  have p0000 := @gImp ph ps (.imp ch th) hyp_imp3_1
  have p0001 := @gImp (synWa ph ps) ch th p0000
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_imp32`. -/
@[expose]
noncomputable def gImp32 (ph : Wff) (ps : Wff) (ch : Wff) (th : Wff)
    (hyp_imp3_1 : Nominal.NPrf (.imp ph (.imp ps (.imp ch th)))) :
    Nominal.NPrf (.imp (synWa ph (synWa ps ch)) th) :=
  by
  have p0000 := @gImp3a ph ps ch th hyp_imp3_1
  have p0001 := @gImp ph (synWa ps ch) th p0000
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_ex`. -/
@[expose]
noncomputable def gEx (ph : Wff) (ps : Wff) (ch : Wff)
    (hyp_exp_1 : Nominal.NPrf (.imp (synWa ph ps) ch)) :
    Nominal.NPrf (.imp ph (.imp ps ch)) :=
  by
  have p0000 := (Nominal.biimpRefl (synWa ph ps))
  have p0001 := @gSylbir (.neg (.imp ph (.neg ps))) (synWa ph ps) ch p0000 hyp_exp_1
  have p0002 := @gExpi ph ps ch p0001
  exact p0002

/-- Checked nominal proof certificate identified upstream as `g_expcom`. -/
@[expose]
noncomputable def gExpcom (ph : Wff) (ps : Wff) (ch : Wff)
    (hyp_exp_1 : Nominal.NPrf (.imp (synWa ph ps) ch)) :
    Nominal.NPrf (.imp ps (.imp ph ch)) :=
  by
  have p0000 := @gEx ph ps ch hyp_exp_1
  have p0001 := @gCom12 ph ps ch p0000
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_exp3a`. -/
@[expose]
noncomputable def gExp3a (ph : Wff) (ps : Wff) (ch : Wff) (th : Wff)
    (hyp_exp3a_1 : Nominal.NPrf (.imp ph (.imp (synWa ps ch) th))) :
    Nominal.NPrf (.imp ph (.imp ps (.imp ch th))) :=
  by
  have p0000 := @gCom12 ph (synWa ps ch) th hyp_exp3a_1
  have p0001 := @gEx ps ch (.imp ph th) p0000
  have p0002 := @gCom3r ps ch ph th p0001
  exact p0002

/-- Checked nominal proof certificate identified upstream as `g_expdimp`. -/
@[expose]
noncomputable def gExpdimp (ph : Wff) (ps : Wff) (ch : Wff) (th : Wff)
    (hyp_exp3a_1 : Nominal.NPrf (.imp ph (.imp (synWa ps ch) th))) :
    Nominal.NPrf (.imp (synWa ph ps) (.imp ch th)) :=
  by
  have p0000 := @gExp3a ph ps ch th hyp_exp3a_1
  have p0001 := @gImp ph ps (.imp ch th) p0000
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_impancom`. -/
@[expose]
noncomputable def gImpancom (ph : Wff) (ps : Wff) (ch : Wff) (th : Wff)
    (hyp_impancom_1 : Nominal.NPrf (.imp (synWa ph ps) (.imp ch th))) :
    Nominal.NPrf (.imp (synWa ph ch) (.imp ps th)) :=
  by
  have p0000 := @gEx ph ps (.imp ch th) hyp_impancom_1
  have p0001 := @gCom23 ph ps ch th p0000
  have p0002 := @gImp ph ch (.imp ps th) p0001
  exact p0002

/-- Checked nominal proof certificate identified upstream as `g_con3and`. -/
@[expose]
noncomputable def gCon3and (ph : Wff) (ps : Wff) (ch : Wff)
    (hyp_con3and_1 : Nominal.NPrf (.imp ph (.imp ps ch))) :
    Nominal.NPrf (.imp (synWa ph (.neg ch)) (.neg ps)) :=
  by
  have p0000 := @gCon3d ph ps ch hyp_con3and_1
  have p0001 := @gImp ph (.neg ch) (.neg ps) p0000
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_pm2_01da`. -/
@[expose]
noncomputable def gPm201da (ph : Wff) (ps : Wff)
    (hyp_pm2_01da_1 : Nominal.NPrf (.imp (synWa ph ps) (.neg ps))) :
    Nominal.NPrf (.imp ph (.neg ps)) :=
  by
  have p0000 := @gEx ph ps (.neg ps) hyp_pm2_01da_1
  have p0001 := @gPm201d ph ps p0000
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_pm3_3`. -/
@[expose]
noncomputable def gPm33 (ph : Wff) (ps : Wff) (ch : Wff) :
    Nominal.NPrf (.imp (.imp (synWa ph ps) ch) (.imp ph (.imp ps ch))) :=
  by
  have p0000 := @gId (.imp (synWa ph ps) ch)
  have p0001 := @gExp3a (.imp (synWa ph ps) ch) ph ps ch p0000
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_pm3_31`. -/
@[expose]
noncomputable def gPm331 (ph : Wff) (ps : Wff) (ch : Wff) :
    Nominal.NPrf (.imp (.imp ph (.imp ps ch)) (.imp (synWa ph ps) ch)) :=
  by
  have p0000 := @gId (.imp ph (.imp ps ch))
  have p0001 := @gImp3a (.imp ph (.imp ps ch)) ph ps ch p0000
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_impexp`. -/
@[expose]
noncomputable def gImpexp (ph : Wff) (ps : Wff) (ch : Wff) :
    Nominal.NPrf (synWb (.imp (synWa ph ps) ch) (.imp ph (.imp ps ch))) :=
  by
  have p0000 := @gPm33 ph ps ch
  have p0001 := @gPm331 ph ps ch
  have p0002 := @gImpbii (.imp (synWa ph ps) ch) (.imp ph (.imp ps ch)) p0000 p0001
  exact p0002

/-- Checked nominal proof certificate identified upstream as `g_pm3_2`. -/
@[expose]
noncomputable def g_pm3_2 (ph : Wff) (ps : Wff) :
    Nominal.NPrf (.imp ph (.imp ps (synWa ph ps))) :=
  by
  have p0000 := @gId (synWa ph ps)
  have p0001 := @gEx ph ps (synWa ph ps) p0000
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_pm3_21`. -/
@[expose]
noncomputable def gPm321 (ph : Wff) (ps : Wff) :
    Nominal.NPrf (.imp ph (.imp ps (synWa ps ph))) :=
  by
  have p0000 := @g_pm3_2 ps ph
  have p0001 := @gCom12 ps ph (synWa ps ph) p0000
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_pm3_22`. -/
@[expose]
noncomputable def gPm322 (ph : Wff) (ps : Wff) :
    Nominal.NPrf (.imp (synWa ph ps) (synWa ps ph)) :=
  by
  have p0000 := @gPm321 ph ps
  have p0001 := @gImp ph ps (synWa ps ph) p0000
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_ancom`. -/
@[expose]
noncomputable def gAncom (ph : Wff) (ps : Wff) :
    Nominal.NPrf (synWb (synWa ph ps) (synWa ps ph)) :=
  by
  have p0000 := @gPm322 ph ps
  have p0001 := @gPm322 ps ph
  have p0002 := @gImpbii (synWa ph ps) (synWa ps ph) p0000 p0001
  exact p0002

/-- Checked nominal proof certificate identified upstream as `g_ancomd`. -/
@[expose]
noncomputable def gAncomd (ph : Wff) (ps : Wff) (ch : Wff)
    (hyp_ancomd_1 : Nominal.NPrf (.imp ph (synWa ps ch))) :
    Nominal.NPrf (.imp ph (synWa ch ps)) :=
  by
  have p0000 := @gAncom ps ch
  have p0001 := @gSylib ph (synWa ps ch) (synWa ch ps) hyp_ancomd_1 p0000
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_ancoms`. -/
@[expose]
noncomputable def gAncoms (ph : Wff) (ps : Wff) (ch : Wff)
    (hyp_ancoms_1 : Nominal.NPrf (.imp (synWa ph ps) ch)) :
    Nominal.NPrf (.imp (synWa ps ph) ch) :=
  by
  have p0000 := @gExpcom ph ps ch hyp_ancoms_1
  have p0001 := @gImp ps ph ch p0000
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_ancomsd`. -/
@[expose]
noncomputable def gAncomsd (ph : Wff) (ps : Wff) (ch : Wff) (th : Wff)
    (hyp_ancomsd_1 : Nominal.NPrf (.imp ph (.imp (synWa ps ch) th))) :
    Nominal.NPrf (.imp ph (.imp (synWa ch ps) th)) :=
  by
  have p0000 := @gAncom ch ps
  have p0001 := @gSyl5bi (synWa ch ps) (synWa ps ch) ph th p0000 hyp_ancomsd_1
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_pm3_2i`. -/
@[expose]
noncomputable def gPm32i (ph : Wff) (ps : Wff) (hyp_pm3_2i_1 : Nominal.NPrf ph)
    (hyp_pm3_2i_2 : Nominal.NPrf ps) : Nominal.NPrf (synWa ph ps) :=
  by
  have p0000 := @g_pm3_2 ph ps
  have p0001 := @gMp2 ph ps (synWa ph ps) hyp_pm3_2i_1 hyp_pm3_2i_2 p0000
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_pm3_43i`. -/
@[expose]
noncomputable def gPm343i (ph : Wff) (ps : Wff) (ch : Wff) :
    Nominal.NPrf (.imp (.imp ph ps) (.imp (.imp ph ch) (.imp ph (synWa ps ch)))) :=
  by
  have p0000 := @g_pm3_2 ps ch
  have p0001 := @gImim3i ps ch (synWa ps ch) ph p0000
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_simpl`. -/
@[expose]
noncomputable def gSimpl (ph : Wff) (ps : Wff) : Nominal.NPrf (.imp (synWa ph ps) ph) :=
  by
  have p0000 := Nominal.ax1 ph ps
  have p0001 := @gImp ph ps ph p0000
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_simpli`. -/
@[expose]
noncomputable def gSimpli (ph : Wff) (ps : Wff)
    (hyp_simpli_1 : Nominal.NPrf (synWa ph ps)) : Nominal.NPrf ph :=
  by
  have p0000 := @gSimpl ph ps
  have p0001 := Nominal.mp hyp_simpli_1 p0000
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_simpld`. -/
@[expose]
noncomputable def gSimpld (ph : Wff) (ps : Wff) (ch : Wff)
    (hyp_simpld_1 : Nominal.NPrf (.imp ph (synWa ps ch))) : Nominal.NPrf (.imp ph ps) :=
  by
  have p0000 := @gSimpl ps ch
  have p0001 := @gSyl ph (synWa ps ch) ps hyp_simpld_1 p0000
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_simplbi`. -/
@[expose]
noncomputable def gSimplbi (ph : Wff) (ps : Wff) (ch : Wff)
    (hyp_simplbi_1 : Nominal.NPrf (synWb ph (synWa ps ch))) :
    Nominal.NPrf (.imp ph ps) :=
  by
  have p0000 := @gBiimpi ph (synWa ps ch) hyp_simplbi_1
  have p0001 := @gSimpld ph ps ch p0000
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_simpr`. -/
@[expose]
noncomputable def gSimpr (ph : Wff) (ps : Wff) : Nominal.NPrf (.imp (synWa ph ps) ps) :=
  by
  have p0000 := @gIdd ph ps
  have p0001 := @gImp ph ps ps p0000
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_simpri`. -/
@[expose]
noncomputable def gSimpri (ph : Wff) (ps : Wff)
    (hyp_simpri_1 : Nominal.NPrf (synWa ph ps)) : Nominal.NPrf ps :=
  by
  have p0000 := @gSimpr ph ps
  have p0001 := Nominal.mp hyp_simpri_1 p0000
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_simprd`. -/
@[expose]
noncomputable def gSimprd (ph : Wff) (ps : Wff) (ch : Wff)
    (hyp_simprd_1 : Nominal.NPrf (.imp ph (synWa ps ch))) : Nominal.NPrf (.imp ph ch) :=
  by
  have p0000 := @gAncomd ph ps ch hyp_simprd_1
  have p0001 := @gSimpld ph ch ps p0000
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_simprbi`. -/
@[expose]
noncomputable def gSimprbi (ph : Wff) (ps : Wff) (ch : Wff)
    (hyp_simprbi_1 : Nominal.NPrf (synWb ph (synWa ps ch))) :
    Nominal.NPrf (.imp ph ch) :=
  by
  have p0000 := @gBiimpi ph (synWa ps ch) hyp_simprbi_1
  have p0001 := @gSimprd ph ps ch p0000
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_adantr`. -/
@[expose]
noncomputable def gAdantr (ph : Wff) (ps : Wff) (ch : Wff)
    (hyp_adantr_1 : Nominal.NPrf (.imp ph ps)) : Nominal.NPrf (.imp (synWa ph ch) ps) :=
  by
  have p0000 := @gA1d ph ps ch hyp_adantr_1
  have p0001 := @gImp ph ch ps p0000
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_adantl`. -/
@[expose]
noncomputable def gAdantl (ph : Wff) (ps : Wff) (ch : Wff)
    (hyp_adantl_1 : Nominal.NPrf (.imp ph ps)) : Nominal.NPrf (.imp (synWa ch ph) ps) :=
  by
  have p0000 := @gAdantr ph ps ch hyp_adantl_1
  have p0001 := @gAncoms ph ch ps p0000
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_adantld`. -/
@[expose]
noncomputable def gAdantld (ph : Wff) (ps : Wff) (ch : Wff) (th : Wff)
    (hyp_adantld_1 : Nominal.NPrf (.imp ph (.imp ps ch))) :
    Nominal.NPrf (.imp ph (.imp (synWa th ps) ch)) :=
  by
  have p0000 := @gSimpr th ps
  have p0001 := @gSyl5 (synWa th ps) ps ph ch p0000 hyp_adantld_1
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_adantrd`. -/
@[expose]
noncomputable def gAdantrd (ph : Wff) (ps : Wff) (ch : Wff) (th : Wff)
    (hyp_adantrd_1 : Nominal.NPrf (.imp ph (.imp ps ch))) :
    Nominal.NPrf (.imp ph (.imp (synWa ps th) ch)) :=
  by
  have p0000 := @gSimpl ps th
  have p0001 := @gSyl5 (synWa ps th) ps ph ch p0000 hyp_adantrd_1
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_mpan9`. -/
@[expose]
noncomputable def gMpan9 (ph : Wff) (ps : Wff) (ch : Wff) (th : Wff)
    (hyp_mpan9_1 : Nominal.NPrf (.imp ph ps))
    (hyp_mpan9_2 : Nominal.NPrf (.imp ch (.imp ps th))) :
    Nominal.NPrf (.imp (synWa ph ch) th) :=
  by
  have p0000 := @gSyl5 ph ps ch th hyp_mpan9_1 hyp_mpan9_2
  have p0001 := @gImpcom ch ph th p0000
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_syldan`. -/
@[expose]
noncomputable def gSyldan (ph : Wff) (ps : Wff) (ch : Wff) (th : Wff)
    (hyp_syldan_1 : Nominal.NPrf (.imp (synWa ph ps) ch))
    (hyp_syldan_2 : Nominal.NPrf (.imp (synWa ph ch) th)) :
    Nominal.NPrf (.imp (synWa ph ps) th) :=
  by
  have p0000 := @gExpcom ph ch th hyp_syldan_2
  have p0001 := @gAdantrd ch ph th ps p0000
  have p0002 := @gMpcom ch (synWa ph ps) th hyp_syldan_1 p0001
  exact p0002

/-- Checked nominal proof certificate identified upstream as `g_sylan`. -/
@[expose]
noncomputable def gSylan (ph : Wff) (ps : Wff) (ch : Wff) (th : Wff)
    (hyp_sylan_1 : Nominal.NPrf (.imp ph ps))
    (hyp_sylan_2 : Nominal.NPrf (.imp (synWa ps ch) th)) :
    Nominal.NPrf (.imp (synWa ph ch) th) :=
  by
  have p0000 := @gExpcom ps ch th hyp_sylan_2
  have p0001 := @gMpan9 ph ps ch th hyp_sylan_1 p0000
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_sylanb`. -/
@[expose]
noncomputable def gSylanb (ph : Wff) (ps : Wff) (ch : Wff) (th : Wff)
    (hyp_sylanb_1 : Nominal.NPrf (synWb ph ps))
    (hyp_sylanb_2 : Nominal.NPrf (.imp (synWa ps ch) th)) :
    Nominal.NPrf (.imp (synWa ph ch) th) :=
  by
  have p0000 := @gBiimpi ph ps hyp_sylanb_1
  have p0001 := @gSylan ph ps ch th p0000 hyp_sylanb_2
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_sylanbr`. -/
@[expose]
noncomputable def gSylanbr (ph : Wff) (ps : Wff) (ch : Wff) (th : Wff)
    (hyp_sylanbr_1 : Nominal.NPrf (synWb ps ph))
    (hyp_sylanbr_2 : Nominal.NPrf (.imp (synWa ps ch) th)) :
    Nominal.NPrf (.imp (synWa ph ch) th) :=
  by
  have p0000 := @gBiimpri ps ph hyp_sylanbr_1
  have p0001 := @gSylan ph ps ch th p0000 hyp_sylanbr_2
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_sylan2`. -/
@[expose]
noncomputable def gSylan2 (ph : Wff) (ps : Wff) (ch : Wff) (th : Wff)
    (hyp_sylan2_1 : Nominal.NPrf (.imp ph ch))
    (hyp_sylan2_2 : Nominal.NPrf (.imp (synWa ps ch) th)) :
    Nominal.NPrf (.imp (synWa ps ph) th) :=
  by
  have p0000 := @gAdantl ph ch ps hyp_sylan2_1
  have p0001 := @gSyldan ps ph ch th p0000 hyp_sylan2_2
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_sylan2b`. -/
@[expose]
noncomputable def gSylan2b (ph : Wff) (ps : Wff) (ch : Wff) (th : Wff)
    (hyp_sylan2b_1 : Nominal.NPrf (synWb ph ch))
    (hyp_sylan2b_2 : Nominal.NPrf (.imp (synWa ps ch) th)) :
    Nominal.NPrf (.imp (synWa ps ph) th) :=
  by
  have p0000 := @gBiimpi ph ch hyp_sylan2b_1
  have p0001 := @gSylan2 ph ps ch th p0000 hyp_sylan2b_2
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_sylan2br`. -/
@[expose]
noncomputable def gSylan2br (ph : Wff) (ps : Wff) (ch : Wff) (th : Wff)
    (hyp_sylan2br_1 : Nominal.NPrf (synWb ch ph))
    (hyp_sylan2br_2 : Nominal.NPrf (.imp (synWa ps ch) th)) :
    Nominal.NPrf (.imp (synWa ps ph) th) :=
  by
  have p0000 := @gBiimpri ch ph hyp_sylan2br_1
  have p0001 := @gSylan2 ph ps ch th p0000 hyp_sylan2br_2
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_syl2an`. -/
@[expose]
noncomputable def gSyl2an (ph : Wff) (ps : Wff) (ch : Wff) (th : Wff) (ta : Wff)
    (hyp_syl2an_1 : Nominal.NPrf (.imp ph ps)) (hyp_syl2an_2 : Nominal.NPrf (.imp ta ch))
    (hyp_syl2an_3 : Nominal.NPrf (.imp (synWa ps ch) th)) :
    Nominal.NPrf (.imp (synWa ph ta) th) :=
  by
  have p0000 := @gSylan ph ps ch th hyp_syl2an_1 hyp_syl2an_3
  have p0001 := @gSylan2 ta ph ch th hyp_syl2an_2 p0000
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_syl2anr`. -/
@[expose]
noncomputable def gSyl2anr (ph : Wff) (ps : Wff) (ch : Wff) (th : Wff) (ta : Wff)
    (hyp_syl2an_1 : Nominal.NPrf (.imp ph ps)) (hyp_syl2an_2 : Nominal.NPrf (.imp ta ch))
    (hyp_syl2an_3 : Nominal.NPrf (.imp (synWa ps ch) th)) :
    Nominal.NPrf (.imp (synWa ta ph) th) :=
  by
  have p0000 := @gSyl2an ph ps ch th ta hyp_syl2an_1 hyp_syl2an_2 hyp_syl2an_3
  have p0001 := @gAncoms ph ta th p0000
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_syl2anb`. -/
@[expose]
noncomputable def gSyl2anb (ph : Wff) (ps : Wff) (ch : Wff) (th : Wff) (ta : Wff)
    (hyp_syl2anb_1 : Nominal.NPrf (synWb ph ps))
    (hyp_syl2anb_2 : Nominal.NPrf (synWb ta ch))
    (hyp_syl2anb_3 : Nominal.NPrf (.imp (synWa ps ch) th)) :
    Nominal.NPrf (.imp (synWa ph ta) th) :=
  by
  have p0000 := @gSylanb ph ps ch th hyp_syl2anb_1 hyp_syl2anb_3
  have p0001 := @gSylan2b ta ph ch th hyp_syl2anb_2 p0000
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_syland`. -/
@[expose]
noncomputable def gSyland (ph : Wff) (ps : Wff) (ch : Wff) (th : Wff) (ta : Wff)
    (hyp_syland_1 : Nominal.NPrf (.imp ph (.imp ps ch)))
    (hyp_syland_2 : Nominal.NPrf (.imp ph (.imp (synWa ch th) ta))) :
    Nominal.NPrf (.imp ph (.imp (synWa ps th) ta)) :=
  by
  have p0000 := @gExp3a ph ch th ta hyp_syland_2
  have p0001 := @gSyld ph ps ch (.imp th ta) hyp_syland_1 p0000
  have p0002 := @gImp3a ph ps th ta p0001
  exact p0002

/-- Checked nominal proof certificate identified upstream as `g_sylan2d`. -/
@[expose]
noncomputable def gSylan2d (ph : Wff) (ps : Wff) (ch : Wff) (th : Wff) (ta : Wff)
    (hyp_sylan2d_1 : Nominal.NPrf (.imp ph (.imp ps ch)))
    (hyp_sylan2d_2 : Nominal.NPrf (.imp ph (.imp (synWa th ch) ta))) :
    Nominal.NPrf (.imp ph (.imp (synWa th ps) ta)) :=
  by
  have p0000 := @gAncomsd ph th ch ta hyp_sylan2d_2
  have p0001 := @gSyland ph ps ch th ta hyp_sylan2d_1 p0000
  have p0002 := @gAncomsd ph ps th ta p0001
  exact p0002

/-- Checked nominal proof certificate identified upstream as `g_syl2and`. -/
@[expose]
noncomputable def gSyl2and (ph : Wff) (ps : Wff) (ch : Wff) (th : Wff) (ta : Wff)
    (et : Wff) (hyp_syl2and_1 : Nominal.NPrf (.imp ph (.imp ps ch)))
    (hyp_syl2and_2 : Nominal.NPrf (.imp ph (.imp th ta)))
    (hyp_syl2and_3 : Nominal.NPrf (.imp ph (.imp (synWa ch ta) et))) :
    Nominal.NPrf (.imp ph (.imp (synWa ps th) et)) :=
  by
  have p0000 := @gSylan2d ph th ta ch et hyp_syl2and_2 hyp_syl2and_3
  have p0001 := @gSyland ph ps ch th et hyp_syl2and_1 p0000
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_biimpa`. -/
@[expose]
noncomputable def gBiimpa (ph : Wff) (ps : Wff) (ch : Wff)
    (hyp_biimpa_1 : Nominal.NPrf (.imp ph (synWb ps ch))) :
    Nominal.NPrf (.imp (synWa ph ps) ch) :=
  by
  have p0000 := @gBiimpd ph ps ch hyp_biimpa_1
  have p0001 := @gImp ph ps ch p0000
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_biimpar`. -/
@[expose]
noncomputable def gBiimpar (ph : Wff) (ps : Wff) (ch : Wff)
    (hyp_biimpa_1 : Nominal.NPrf (.imp ph (synWb ps ch))) :
    Nominal.NPrf (.imp (synWa ph ch) ps) :=
  by
  have p0000 := @gBiimprd ph ps ch hyp_biimpa_1
  have p0001 := @gImp ph ch ps p0000
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_biimpac`. -/
@[expose]
noncomputable def gBiimpac (ph : Wff) (ps : Wff) (ch : Wff)
    (hyp_biimpa_1 : Nominal.NPrf (.imp ph (synWb ps ch))) :
    Nominal.NPrf (.imp (synWa ps ph) ch) :=
  by
  have p0000 := @gBiimpcd ph ps ch hyp_biimpa_1
  have p0001 := @gImp ps ph ch p0000
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_biimparc`. -/
@[expose]
noncomputable def gBiimparc (ph : Wff) (ps : Wff) (ch : Wff)
    (hyp_biimpa_1 : Nominal.NPrf (.imp ph (synWb ps ch))) :
    Nominal.NPrf (.imp (synWa ch ph) ps) :=
  by
  have p0000 := @gBiimprcd ph ps ch hyp_biimpa_1
  have p0001 := @gImp ch ph ps p0000
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_ianor`. -/
@[expose]
noncomputable def gIanor (ph : Wff) (ps : Wff) :
    Nominal.NPrf (synWb (.neg (synWa ph ps)) (synWo (.neg ph) (.neg ps))) :=
  by
  have p0000 := @gImnan ph ps
  have p0001 := @gPm462 ph ps
  have p0002 :=
    @gBitr3i (.neg (synWa ph ps)) (.imp ph (.neg ps)) (synWo (.neg ph) (.neg ps)) p0000
      p0001
  exact p0002

/-- Checked nominal proof certificate identified upstream as `g_ioran`. -/
@[expose]
noncomputable def gIoran (ph : Wff) (ps : Wff) :
    Nominal.NPrf (synWb (.neg (synWo ph ps)) (synWa (.neg ph) (.neg ps))) :=
  by
  have p0000 := @gPm465 ph ps
  have p0001 := @gPm464 ph ps
  have p0002 :=
    @gXchnxbi (.imp (.neg ph) ps) (synWa (.neg ph) (.neg ps)) (synWo ph ps) p0000 p0001
  exact p0002

/-- Checked nominal proof certificate identified upstream as `g_pm4_56`. -/
@[expose]
noncomputable def gPm456 (ph : Wff) (ps : Wff) :
    Nominal.NPrf (synWb (synWa (.neg ph) (.neg ps)) (.neg (synWo ph ps))) :=
  by
  have p0000 := @gIoran ph ps
  have p0001 := @gBicomi (.neg (synWo ph ps)) (synWa (.neg ph) (.neg ps)) p0000
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_oran`. -/
@[expose]
noncomputable def gOran (ph : Wff) (ps : Wff) :
    Nominal.NPrf (synWb (synWo ph ps) (.neg (synWa (.neg ph) (.neg ps)))) :=
  by
  have p0000 := @gPm456 ph ps
  have p0001 := @gCon2bii (synWa (.neg ph) (.neg ps)) (synWo ph ps) p0000
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_iba`. -/
@[expose]
noncomputable def gIba (ph : Wff) (ps : Wff) :
    Nominal.NPrf (.imp ph (synWb ps (synWa ps ph))) :=
  by
  have p0000 := @gPm321 ph ps
  have p0001 := @gSimpl ps ph
  have p0002 := @gImpbid1 ph ps (synWa ps ph) p0000 p0001
  exact p0002

/-- Checked nominal proof certificate identified upstream as `g_ibar`. -/
@[expose]
noncomputable def gIbar (ph : Wff) (ps : Wff) :
    Nominal.NPrf (.imp ph (synWb ps (synWa ph ps))) :=
  by
  have p0000 := @g_pm3_2 ph ps
  have p0001 := @gSimpr ph ps
  have p0002 := @gImpbid1 ph ps (synWa ph ps) p0000 p0001
  exact p0002

/-- Checked nominal proof certificate identified upstream as `g_biantru`. -/
@[expose]
noncomputable def gBiantru (ph : Wff) (ps : Wff) (hyp_biantru_1 : Nominal.NPrf ph) :
    Nominal.NPrf (synWb ps (synWa ps ph)) :=
  by
  have p0000 := @gIba ph ps
  have p0001 := Nominal.mp hyp_biantru_1 p0000
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_biantrur`. -/
@[expose]
noncomputable def gBiantrur (ph : Wff) (ps : Wff) (hyp_biantrur_1 : Nominal.NPrf ph) :
    Nominal.NPrf (synWb ps (synWa ph ps)) :=
  by
  have p0000 := @gIbar ph ps
  have p0001 := Nominal.mp hyp_biantrur_1 p0000
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_biantrud`. -/
@[expose]
noncomputable def gBiantrud (ph : Wff) (ps : Wff) (ch : Wff)
    (hyp_biantrud_1 : Nominal.NPrf (.imp ph ps)) :
    Nominal.NPrf (.imp ph (synWb ch (synWa ch ps))) :=
  by
  have p0000 := @gIba ps ch
  have p0001 := @gSyl ph ps (synWb ch (synWa ch ps)) hyp_biantrud_1 p0000
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_biantrurd`. -/
@[expose]
noncomputable def gBiantrurd (ph : Wff) (ps : Wff) (ch : Wff)
    (hyp_biantrud_1 : Nominal.NPrf (.imp ph ps)) :
    Nominal.NPrf (.imp ph (synWb ch (synWa ps ch))) :=
  by
  have p0000 := @gIbar ps ch
  have p0001 := @gSyl ph ps (synWb ch (synWa ps ch)) hyp_biantrud_1 p0000
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_jaao`. -/
@[expose]
noncomputable def gJaao (ph : Wff) (ps : Wff) (ch : Wff) (th : Wff) (ta : Wff)
    (hyp_jaao_1 : Nominal.NPrf (.imp ph (.imp ps ch)))
    (hyp_jaao_2 : Nominal.NPrf (.imp th (.imp ta ch))) :
    Nominal.NPrf (.imp (synWa ph th) (.imp (synWo ps ta) ch)) :=
  by
  have p0000 := @gAdantr ph (.imp ps ch) th hyp_jaao_1
  have p0001 := @gAdantl th (.imp ta ch) ph hyp_jaao_2
  have p0002 := @gJaod (synWa ph th) ps ch ta p0000 p0001
  exact p0002

/-- Checked nominal proof certificate identified upstream as `g_pm3_44`. -/
@[expose]
noncomputable def gPm344 (ph : Wff) (ps : Wff) (ch : Wff) :
    Nominal.NPrf (.imp (synWa (.imp ps ph) (.imp ch ph)) (.imp (synWo ps ch) ph)) :=
  by
  have p0000 := @gId (.imp ps ph)
  have p0001 := @gId (.imp ch ph)
  have p0002 := @gJaao (.imp ps ph) ps ph (.imp ch ph) ch p0000 p0001
  exact p0002

/-- Checked nominal proof certificate identified upstream as `g_jao`. -/
@[expose]
noncomputable def gJao (ph : Wff) (ps : Wff) (ch : Wff) :
    Nominal.NPrf (.imp (.imp ph ps) (.imp (.imp ch ps) (.imp (synWo ph ch) ps))) :=
  by
  have p0000 := @gPm344 ps ph ch
  have p0001 := @gEx (.imp ph ps) (.imp ch ps) (.imp (synWo ph ch) ps) p0000
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_pm1_2`. -/
@[expose]
noncomputable def g_pm1_2 (ph : Wff) : Nominal.NPrf (.imp (synWo ph ph) ph) :=
  by
  have p0000 := @gId ph
  have p0001 := @gJaoi ph ph ph p0000 p0000
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_oridm`. -/
@[expose]
noncomputable def gOridm (ph : Wff) : Nominal.NPrf (synWb (synWo ph ph) ph) :=
  by
  have p0000 := @g_pm1_2 ph
  have p0001 := @gPm207 ph
  have p0002 := @gImpbii (synWo ph ph) ph p0000 p0001
  exact p0002

/-- Checked nominal proof certificate identified upstream as `g_orim12i`. -/
@[expose]
noncomputable def gOrim12i (ph : Wff) (ps : Wff) (ch : Wff) (th : Wff)
    (hyp_orim12i_1 : Nominal.NPrf (.imp ph ps))
    (hyp_orim12i_2 : Nominal.NPrf (.imp ch th)) :
    Nominal.NPrf (.imp (synWo ph ch) (synWo ps th)) :=
  by
  have p0000 := @gOrcd ph ps th hyp_orim12i_1
  have p0001 := @gOlcd ch th ps hyp_orim12i_2
  have p0002 := @gJaoi ph (synWo ps th) ch p0000 p0001
  exact p0002

/-- Checked nominal proof certificate identified upstream as `g_orim2i`. -/
@[expose]
noncomputable def gOrim2i (ph : Wff) (ps : Wff) (ch : Wff)
    (hyp_orim1i_1 : Nominal.NPrf (.imp ph ps)) :
    Nominal.NPrf (.imp (synWo ch ph) (synWo ch ps)) :=
  by
  have p0000 := @gId ch
  have p0001 := @gOrim12i ch ch ph ps p0000 hyp_orim1i_1
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_orbi2i`. -/
@[expose]
noncomputable def gOrbi2i (ph : Wff) (ps : Wff) (ch : Wff)
    (hyp_orbi2i_1 : Nominal.NPrf (synWb ph ps)) :
    Nominal.NPrf (synWb (synWo ch ph) (synWo ch ps)) :=
  by
  have p0000 := @gBiimpi ph ps hyp_orbi2i_1
  have p0001 := @gOrim2i ph ps ch p0000
  have p0002 := @gBiimpri ph ps hyp_orbi2i_1
  have p0003 := @gOrim2i ps ph ch p0002
  have p0004 := @gImpbii (synWo ch ph) (synWo ch ps) p0001 p0003
  exact p0004

/-- Checked nominal proof certificate identified upstream as `g_orbi1i`. -/
@[expose]
noncomputable def gOrbi1i (ph : Wff) (ps : Wff) (ch : Wff)
    (hyp_orbi2i_1 : Nominal.NPrf (synWb ph ps)) :
    Nominal.NPrf (synWb (synWo ph ch) (synWo ps ch)) :=
  by
  have p0000 := @gOrcom ph ch
  have p0001 := @gOrbi2i ph ps ch hyp_orbi2i_1
  have p0002 := @gOrcom ch ps
  have p0003 :=
    @gN3bitri (synWo ph ch) (synWo ch ph) (synWo ch ps) (synWo ps ch) p0000 p0001
      p0002
  exact p0003

/-- Checked nominal proof certificate identified upstream as `g_orbi12i`. -/
@[expose]
noncomputable def gOrbi12i (ph : Wff) (ps : Wff) (ch : Wff) (th : Wff)
    (hyp_orbi12i_1 : Nominal.NPrf (synWb ph ps))
    (hyp_orbi12i_2 : Nominal.NPrf (synWb ch th)) :
    Nominal.NPrf (synWb (synWo ph ch) (synWo ps th)) :=
  by
  have p0000 := @gOrbi2i ch th ph hyp_orbi12i_2
  have p0001 := @gOrbi1i ph ps th hyp_orbi12i_1
  have p0002 := @gBitri (synWo ph ch) (synWo ph th) (synWo ps th) p0000 p0001
  exact p0002

/-- Checked nominal proof certificate identified upstream as `g_pm1_5`. -/
@[expose]
noncomputable def gPm15 (ph : Wff) (ps : Wff) (ch : Wff) :
    Nominal.NPrf (.imp (synWo ph (synWo ps ch)) (synWo ps (synWo ph ch))) :=
  by
  have p0000 := @gOrc ph ch
  have p0001 := @gOlcd ph (synWo ph ch) ps p0000
  have p0002 := @gOlc ch ph
  have p0003 := @gOrim2i ch (synWo ph ch) ps p0002
  have p0004 := @gJaoi ph (synWo ps (synWo ph ch)) (synWo ps ch) p0001 p0003
  exact p0004

/-- Checked nominal proof certificate identified upstream as `g_or12`. -/
@[expose]
noncomputable def gOr12 (ph : Wff) (ps : Wff) (ch : Wff) :
    Nominal.NPrf (synWb (synWo ph (synWo ps ch)) (synWo ps (synWo ph ch))) :=
  by
  have p0000 := @gPm15 ph ps ch
  have p0001 := @gPm15 ps ph ch
  have p0002 :=
    @gImpbii (synWo ph (synWo ps ch)) (synWo ps (synWo ph ch)) p0000 p0001
  exact p0002

/-- Checked nominal proof certificate identified upstream as `g_orass`. -/
@[expose]
noncomputable def gOrass (ph : Wff) (ps : Wff) (ch : Wff) :
    Nominal.NPrf (synWb (synWo (synWo ph ps) ch) (synWo ph (synWo ps ch))) :=
  by
  have p0000 := @gOrcom (synWo ph ps) ch
  have p0001 := @gOr12 ch ph ps
  have p0002 := @gOrcom ch ps
  have p0003 := @gOrbi2i (synWo ch ps) (synWo ps ch) ph p0002
  have p0004 :=
    @gN3bitri (synWo (synWo ph ps) ch) (synWo ch (synWo ph ps))
      (synWo ph (synWo ch ps)) (synWo ph (synWo ps ch)) p0000 p0001 p0003
  exact p0004

/-- Checked nominal proof certificate identified upstream as `g_or32`. -/
@[expose]
noncomputable def gOr32 (ph : Wff) (ps : Wff) (ch : Wff) :
    Nominal.NPrf (synWb (synWo (synWo ph ps) ch) (synWo (synWo ph ch) ps)) :=
  by
  have p0000 := @gOrass ph ps ch
  have p0001 := @gOr12 ph ps ch
  have p0002 := @gOrcom ps (synWo ph ch)
  have p0003 :=
    @gN3bitri (synWo (synWo ph ps) ch) (synWo ph (synWo ps ch))
      (synWo ps (synWo ph ch)) (synWo (synWo ph ch) ps) p0000 p0001 p0002
  exact p0003

/-- Checked nominal proof certificate identified upstream as `g_jca`. -/
@[expose]
noncomputable def gJca (ph : Wff) (ps : Wff) (ch : Wff)
    (hyp_jca_1 : Nominal.NPrf (.imp ph ps)) (hyp_jca_2 : Nominal.NPrf (.imp ph ch)) :
    Nominal.NPrf (.imp ph (synWa ps ch)) :=
  by
  have p0000 := @g_pm3_2 ps ch
  have p0001 := @gSylc ph ps ch (synWa ps ch) hyp_jca_1 hyp_jca_2 p0000
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_jcad`. -/
@[expose]
noncomputable def gJcad (ph : Wff) (ps : Wff) (ch : Wff) (th : Wff)
    (hyp_jcad_1 : Nominal.NPrf (.imp ph (.imp ps ch)))
    (hyp_jcad_2 : Nominal.NPrf (.imp ph (.imp ps th))) :
    Nominal.NPrf (.imp ph (.imp ps (synWa ch th))) :=
  by
  have p0000 := @g_pm3_2 ch th
  have p0001 := @gSyl6c ph ps ch th (synWa ch th) hyp_jcad_1 hyp_jcad_2 p0000
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_jca31`. -/
@[expose]
noncomputable def gJca31 (ph : Wff) (ps : Wff) (ch : Wff) (th : Wff)
    (hyp_jca31_1 : Nominal.NPrf (.imp ph ps)) (hyp_jca31_2 : Nominal.NPrf (.imp ph ch))
    (hyp_jca31_3 : Nominal.NPrf (.imp ph th)) :
    Nominal.NPrf (.imp ph (synWa (synWa ps ch) th)) :=
  by
  have p0000 := @gJca ph ps ch hyp_jca31_1 hyp_jca31_2
  have p0001 := @gJca ph (synWa ps ch) th p0000 hyp_jca31_3
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_jca32`. -/
@[expose]
noncomputable def gJca32 (ph : Wff) (ps : Wff) (ch : Wff) (th : Wff)
    (hyp_jca31_1 : Nominal.NPrf (.imp ph ps)) (hyp_jca31_2 : Nominal.NPrf (.imp ph ch))
    (hyp_jca31_3 : Nominal.NPrf (.imp ph th)) :
    Nominal.NPrf (.imp ph (synWa ps (synWa ch th))) :=
  by
  have p0000 := @gJca ph ch th hyp_jca31_2 hyp_jca31_3
  have p0001 := @gJca ph ps (synWa ch th) hyp_jca31_1 p0000
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_jcai`. -/
@[expose]
noncomputable def gJcai (ph : Wff) (ps : Wff) (ch : Wff)
    (hyp_jcai_1 : Nominal.NPrf (.imp ph ps))
    (hyp_jcai_2 : Nominal.NPrf (.imp ph (.imp ps ch))) :
    Nominal.NPrf (.imp ph (synWa ps ch)) :=
  by
  have p0000 := @gMpd ph ps ch hyp_jcai_1 hyp_jcai_2
  have p0001 := @gJca ph ps ch hyp_jcai_1 p0000
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_jctil`. -/
@[expose]
noncomputable def gJctil (ph : Wff) (ps : Wff) (ch : Wff)
    (hyp_jctil_1 : Nominal.NPrf (.imp ph ps)) (hyp_jctil_2 : Nominal.NPrf ch) :
    Nominal.NPrf (.imp ph (synWa ch ps)) :=
  by
  have p0000 := @gA1i ch ph hyp_jctil_2
  have p0001 := @gJca ph ch ps p0000 hyp_jctil_1
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_jctir`. -/
@[expose]
noncomputable def gJctir (ph : Wff) (ps : Wff) (ch : Wff)
    (hyp_jctil_1 : Nominal.NPrf (.imp ph ps)) (hyp_jctil_2 : Nominal.NPrf ch) :
    Nominal.NPrf (.imp ph (synWa ps ch)) :=
  by
  have p0000 := @gA1i ch ph hyp_jctil_2
  have p0001 := @gJca ph ps ch hyp_jctil_1 p0000
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_jctl`. -/
@[expose]
noncomputable def gJctl (ph : Wff) (ps : Wff) (hyp_jctl_1 : Nominal.NPrf ps) :
    Nominal.NPrf (.imp ph (synWa ps ph)) :=
  by
  have p0000 := @gId ph
  have p0001 := @gJctil ph ph ps p0000 hyp_jctl_1
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_jctr`. -/
@[expose]
noncomputable def gJctr (ph : Wff) (ps : Wff) (hyp_jctl_1 : Nominal.NPrf ps) :
    Nominal.NPrf (.imp ph (synWa ph ps)) :=
  by
  have p0000 := @gId ph
  have p0001 := @gJctir ph ph ps p0000 hyp_jctl_1
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_jctild`. -/
@[expose]
noncomputable def gJctild (ph : Wff) (ps : Wff) (ch : Wff) (th : Wff)
    (hyp_jctild_1 : Nominal.NPrf (.imp ph (.imp ps ch)))
    (hyp_jctild_2 : Nominal.NPrf (.imp ph th)) :
    Nominal.NPrf (.imp ph (.imp ps (synWa th ch))) :=
  by
  have p0000 := @gA1d ph th ps hyp_jctild_2
  have p0001 := @gJcad ph ps th ch p0000 hyp_jctild_1
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_jctird`. -/
@[expose]
noncomputable def gJctird (ph : Wff) (ps : Wff) (ch : Wff) (th : Wff)
    (hyp_jctird_1 : Nominal.NPrf (.imp ph (.imp ps ch)))
    (hyp_jctird_2 : Nominal.NPrf (.imp ph th)) :
    Nominal.NPrf (.imp ph (.imp ps (synWa ch th))) :=
  by
  have p0000 := @gA1d ph th ps hyp_jctird_2
  have p0001 := @gJcad ph ps ch th hyp_jctird_1 p0000
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_ancl`. -/
@[expose]
noncomputable def gAncl (ph : Wff) (ps : Wff) :
    Nominal.NPrf (.imp (.imp ph ps) (.imp ph (synWa ph ps))) :=
  by
  have p0000 := @g_pm3_2 ph ps
  have p0001 := @gA2i ph ps (synWa ph ps) p0000
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_anclb`. -/
@[expose]
noncomputable def gAnclb (ph : Wff) (ps : Wff) :
    Nominal.NPrf (synWb (.imp ph ps) (.imp ph (synWa ph ps))) :=
  by
  have p0000 := @gIbar ph ps
  have p0001 := @gPm574i ph ps (synWa ph ps) p0000
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_ancli`. -/
@[expose]
noncomputable def gAncli (ph : Wff) (ps : Wff)
    (hyp_ancli_1 : Nominal.NPrf (.imp ph ps)) : Nominal.NPrf (.imp ph (synWa ph ps)) :=
  by
  have p0000 := @gId ph
  have p0001 := @gJca ph ph ps p0000 hyp_ancli_1
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_ancri`. -/
@[expose]
noncomputable def gAncri (ph : Wff) (ps : Wff)
    (hyp_ancri_1 : Nominal.NPrf (.imp ph ps)) : Nominal.NPrf (.imp ph (synWa ps ph)) :=
  by
  have p0000 := @gId ph
  have p0001 := @gJca ph ps ph hyp_ancri_1 p0000
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_ancld`. -/
@[expose]
noncomputable def gAncld (ph : Wff) (ps : Wff) (ch : Wff)
    (hyp_ancld_1 : Nominal.NPrf (.imp ph (.imp ps ch))) :
    Nominal.NPrf (.imp ph (.imp ps (synWa ps ch))) :=
  by
  have p0000 := @gIdd ph ps
  have p0001 := @gJcad ph ps ps ch p0000 hyp_ancld_1
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_ancrd`. -/
@[expose]
noncomputable def gAncrd (ph : Wff) (ps : Wff) (ch : Wff)
    (hyp_ancrd_1 : Nominal.NPrf (.imp ph (.imp ps ch))) :
    Nominal.NPrf (.imp ph (.imp ps (synWa ch ps))) :=
  by
  have p0000 := @gIdd ph ps
  have p0001 := @gJcad ph ps ch ps hyp_ancrd_1 p0000
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_anc2li`. -/
@[expose]
noncomputable def gAnc2li (ph : Wff) (ps : Wff) (ch : Wff)
    (hyp_anc2li_1 : Nominal.NPrf (.imp ph (.imp ps ch))) :
    Nominal.NPrf (.imp ph (.imp ps (synWa ph ch))) :=
  by
  have p0000 := @gId ph
  have p0001 := @gJctild ph ps ch ph hyp_anc2li_1 p0000
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_anc2ri`. -/
@[expose]
noncomputable def gAnc2ri (ph : Wff) (ps : Wff) (ch : Wff)
    (hyp_anc2ri_1 : Nominal.NPrf (.imp ph (.imp ps ch))) :
    Nominal.NPrf (.imp ph (.imp ps (synWa ch ph))) :=
  by
  have p0000 := @gId ph
  have p0001 := @gJctird ph ps ch ph hyp_anc2ri_1 p0000
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_pm3_4`. -/
@[expose]
noncomputable def gPm34 (ph : Wff) (ps : Wff) :
    Nominal.NPrf (.imp (synWa ph ps) (.imp ph ps)) :=
  by
  have p0000 := @gSimpr ph ps
  have p0001 := @gA1d (synWa ph ps) ps ph p0000
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_pm4_45im`. -/
@[expose]
noncomputable def gPm445im (ph : Wff) (ps : Wff) :
    Nominal.NPrf (synWb ph (synWa ph (.imp ps ph))) :=
  by
  have p0000 := Nominal.ax1 ph ps
  have p0001 := @gAncli ph (.imp ps ph) p0000
  have p0002 := @gSimpl ph (.imp ps ph)
  have p0003 := @gImpbii ph (synWa ph (.imp ps ph)) p0001 p0002
  exact p0003

/-- Checked nominal proof certificate identified upstream as `g_anim12d`. -/
@[expose]
noncomputable def gAnim12d (ph : Wff) (ps : Wff) (ch : Wff) (th : Wff) (ta : Wff)
    (hyp_anim12d_1 : Nominal.NPrf (.imp ph (.imp ps ch)))
    (hyp_anim12d_2 : Nominal.NPrf (.imp ph (.imp th ta))) :
    Nominal.NPrf (.imp ph (.imp (synWa ps th) (synWa ch ta))) :=
  by
  have p0000 := @gIdd ph (synWa ch ta)
  have p0001 := @gSyl2and ph ps ch th ta (synWa ch ta) hyp_anim12d_1 hyp_anim12d_2 p0000
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_anim1d`. -/
@[expose]
noncomputable def gAnim1d (ph : Wff) (ps : Wff) (ch : Wff) (th : Wff)
    (hyp_anim1d_1 : Nominal.NPrf (.imp ph (.imp ps ch))) :
    Nominal.NPrf (.imp ph (.imp (synWa ps th) (synWa ch th))) :=
  by
  have p0000 := @gIdd ph th
  have p0001 := @gAnim12d ph ps ch th th hyp_anim1d_1 p0000
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_anim2d`. -/
@[expose]
noncomputable def gAnim2d (ph : Wff) (ps : Wff) (ch : Wff) (th : Wff)
    (hyp_anim1d_1 : Nominal.NPrf (.imp ph (.imp ps ch))) :
    Nominal.NPrf (.imp ph (.imp (synWa th ps) (synWa th ch))) :=
  by
  have p0000 := @gIdd ph th
  have p0001 := @gAnim12d ph th th ps ch p0000 hyp_anim1d_1
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_anim12i`. -/
@[expose]
noncomputable def gAnim12i (ph : Wff) (ps : Wff) (ch : Wff) (th : Wff)
    (hyp_anim12i_1 : Nominal.NPrf (.imp ph ps))
    (hyp_anim12i_2 : Nominal.NPrf (.imp ch th)) :
    Nominal.NPrf (.imp (synWa ph ch) (synWa ps th)) :=
  by
  have p0000 := @gId (synWa ps th)
  have p0001 := @gSyl2an ph ps th (synWa ps th) ch hyp_anim12i_1 hyp_anim12i_2 p0000
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_anim12ci`. -/
@[expose]
noncomputable def gAnim12ci (ph : Wff) (ps : Wff) (ch : Wff) (th : Wff)
    (hyp_anim12i_1 : Nominal.NPrf (.imp ph ps))
    (hyp_anim12i_2 : Nominal.NPrf (.imp ch th)) :
    Nominal.NPrf (.imp (synWa ph ch) (synWa th ps)) :=
  by
  have p0000 := @gAnim12i ch th ph ps hyp_anim12i_2 hyp_anim12i_1
  have p0001 := @gAncoms ch ph (synWa th ps) p0000
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_anim1i`. -/
@[expose]
noncomputable def gAnim1i (ph : Wff) (ps : Wff) (ch : Wff)
    (hyp_anim1i_1 : Nominal.NPrf (.imp ph ps)) :
    Nominal.NPrf (.imp (synWa ph ch) (synWa ps ch)) :=
  by
  have p0000 := @gId ch
  have p0001 := @gAnim12i ph ps ch ch hyp_anim1i_1 p0000
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_anim2i`. -/
@[expose]
noncomputable def gAnim2i (ph : Wff) (ps : Wff) (ch : Wff)
    (hyp_anim1i_1 : Nominal.NPrf (.imp ph ps)) :
    Nominal.NPrf (.imp (synWa ch ph) (synWa ch ps)) :=
  by
  have p0000 := @gId ch
  have p0001 := @gAnim12i ch ch ph ps p0000 hyp_anim1i_1
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_anim12ii`. -/
@[expose]
noncomputable def gAnim12ii (ph : Wff) (ps : Wff) (ch : Wff) (th : Wff) (ta : Wff)
    (hyp_anim12ii_1 : Nominal.NPrf (.imp ph (.imp ps ch)))
    (hyp_anim12ii_2 : Nominal.NPrf (.imp th (.imp ps ta))) :
    Nominal.NPrf (.imp (synWa ph th) (.imp ps (synWa ch ta))) :=
  by
  have p0000 := @gAdantr ph (.imp ps ch) th hyp_anim12ii_1
  have p0001 := @gAdantl th (.imp ps ta) ph hyp_anim12ii_2
  have p0002 := @gJcad (synWa ph th) ps ch ta p0000 p0001
  exact p0002

/-- Checked nominal proof certificate identified upstream as `g_prth`. -/
@[expose]
noncomputable def gPrth (ph : Wff) (ps : Wff) (ch : Wff) (th : Wff) :
    Nominal.NPrf
      (.imp (synWa (.imp ph ps) (.imp ch th)) (.imp (synWa ph ch) (synWa ps th))) :=
  by
  have p0000 := @gSimpl (.imp ph ps) (.imp ch th)
  have p0001 := @gSimpr (.imp ph ps) (.imp ch th)
  have p0002 := @gAnim12d (synWa (.imp ph ps) (.imp ch th)) ph ps ch th p0000 p0001
  exact p0002

/-- Checked nominal proof certificate identified upstream as `g_pm3_35`. -/
@[expose]
noncomputable def gPm335 (ph : Wff) (ps : Wff) :
    Nominal.NPrf (.imp (synWa ph (.imp ph ps)) ps) :=
  by
  have p0000 := @gPm227 ph ps
  have p0001 := @gImp ph (.imp ph ps) ps p0000
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_imp4a`. -/
@[expose]
noncomputable def gImp4a (ph : Wff) (ps : Wff) (ch : Wff) (th : Wff) (ta : Wff)
    (hyp_imp4_1 : Nominal.NPrf (.imp ph (.imp ps (.imp ch (.imp th ta))))) :
    Nominal.NPrf (.imp ph (.imp ps (.imp (synWa ch th) ta))) :=
  by
  have p0000 := @gImpexp ch th ta
  have p0001 :=
    @gSyl6ibr ph ps (.imp ch (.imp th ta)) (.imp (synWa ch th) ta) hyp_imp4_1 p0000
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_imp4c`. -/
@[expose]
noncomputable def gImp4c (ph : Wff) (ps : Wff) (ch : Wff) (th : Wff) (ta : Wff)
    (hyp_imp4_1 : Nominal.NPrf (.imp ph (.imp ps (.imp ch (.imp th ta))))) :
    Nominal.NPrf (.imp ph (.imp (synWa (synWa ps ch) th) ta)) :=
  by
  have p0000 := @gImp3a ph ps ch (.imp th ta) hyp_imp4_1
  have p0001 := @gImp3a ph (synWa ps ch) th ta p0000
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_expimpd`. -/
@[expose]
noncomputable def gExpimpd (ph : Wff) (ps : Wff) (ch : Wff) (th : Wff)
    (hyp_expimpd_1 : Nominal.NPrf (.imp (synWa ph ps) (.imp ch th))) :
    Nominal.NPrf (.imp ph (.imp (synWa ps ch) th)) :=
  by
  have p0000 := @gEx ph ps (.imp ch th) hyp_expimpd_1
  have p0001 := @gImp3a ph ps ch th p0000
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_exp31`. -/
@[expose]
noncomputable def gExp31 (ph : Wff) (ps : Wff) (ch : Wff) (th : Wff)
    (hyp_exp31_1 : Nominal.NPrf (.imp (synWa (synWa ph ps) ch) th)) :
    Nominal.NPrf (.imp ph (.imp ps (.imp ch th))) :=
  by
  have p0000 := @gEx (synWa ph ps) ch th hyp_exp31_1
  have p0001 := @gEx ph ps (.imp ch th) p0000
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_exp32`. -/
@[expose]
noncomputable def gExp32 (ph : Wff) (ps : Wff) (ch : Wff) (th : Wff)
    (hyp_exp32_1 : Nominal.NPrf (.imp (synWa ph (synWa ps ch)) th)) :
    Nominal.NPrf (.imp ph (.imp ps (.imp ch th))) :=
  by
  have p0000 := @gEx ph (synWa ps ch) th hyp_exp32_1
  have p0001 := @gExp3a ph ps ch th p0000
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_exp4a`. -/
@[expose]
noncomputable def gExp4a (ph : Wff) (ps : Wff) (ch : Wff) (th : Wff) (ta : Wff)
    (hyp_exp4a_1 : Nominal.NPrf (.imp ph (.imp ps (.imp (synWa ch th) ta)))) :
    Nominal.NPrf (.imp ph (.imp ps (.imp ch (.imp th ta)))) :=
  by
  have p0000 := @gImpexp ch th ta
  have p0001 :=
    @gSyl6ib ph ps (.imp (synWa ch th) ta) (.imp ch (.imp th ta)) hyp_exp4a_1 p0000
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_exp4b`. -/
@[expose]
noncomputable def gExp4b (ph : Wff) (ps : Wff) (ch : Wff) (th : Wff) (ta : Wff)
    (hyp_exp4b_1 : Nominal.NPrf (.imp (synWa ph ps) (.imp (synWa ch th) ta))) :
    Nominal.NPrf (.imp ph (.imp ps (.imp ch (.imp th ta)))) :=
  by
  have p0000 := @gEx ph ps (.imp (synWa ch th) ta) hyp_exp4b_1
  have p0001 := @gExp4a ph ps ch th ta p0000
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_exp4d`. -/
@[expose]
noncomputable def gExp4d (ph : Wff) (ps : Wff) (ch : Wff) (th : Wff) (ta : Wff)
    (hyp_exp4d_1 : Nominal.NPrf (.imp ph (.imp (synWa ps (synWa ch th)) ta))) :
    Nominal.NPrf (.imp ph (.imp ps (.imp ch (.imp th ta)))) :=
  by
  have p0000 := @gExp3a ph ps (synWa ch th) ta hyp_exp4d_1
  have p0001 := @gExp4a ph ps ch th ta p0000
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_exp42`. -/
@[expose]
noncomputable def gExp42 (ph : Wff) (ps : Wff) (ch : Wff) (th : Wff) (ta : Wff)
    (hyp_exp42_1 : Nominal.NPrf (.imp (synWa (synWa ph (synWa ps ch)) th) ta)) :
    Nominal.NPrf (.imp ph (.imp ps (.imp ch (.imp th ta)))) :=
  by
  have p0000 := @gExp31 ph (synWa ps ch) th ta hyp_exp42_1
  have p0001 := @gExp3a ph ps ch (.imp th ta) p0000
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_exp43`. -/
@[expose]
noncomputable def gExp43 (ph : Wff) (ps : Wff) (ch : Wff) (th : Wff) (ta : Wff)
    (hyp_exp43_1 : Nominal.NPrf (.imp (synWa (synWa ph ps) (synWa ch th)) ta)) :
    Nominal.NPrf (.imp ph (.imp ps (.imp ch (.imp th ta)))) :=
  by
  have p0000 := @gEx (synWa ph ps) (synWa ch th) ta hyp_exp43_1
  have p0001 := @gExp4b ph ps ch th ta p0000
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_exp45`. -/
@[expose]
noncomputable def gExp45 (ph : Wff) (ps : Wff) (ch : Wff) (th : Wff) (ta : Wff)
    (hyp_exp45_1 : Nominal.NPrf (.imp (synWa ph (synWa ps (synWa ch th))) ta)) :
    Nominal.NPrf (.imp ph (.imp ps (.imp ch (.imp th ta)))) :=
  by
  have p0000 := @gExp32 ph ps (synWa ch th) ta hyp_exp45_1
  have p0001 := @gExp4a ph ps ch th ta p0000
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_expr`. -/
@[expose]
noncomputable def gExpr (ph : Wff) (ps : Wff) (ch : Wff) (th : Wff)
    (hyp_expr_1 : Nominal.NPrf (.imp (synWa ph (synWa ps ch)) th)) :
    Nominal.NPrf (.imp (synWa ph ps) (.imp ch th)) :=
  by
  have p0000 := @gExp32 ph ps ch th hyp_expr_1
  have p0001 := @gImp ph ps (.imp ch th) p0000
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_exp5c`. -/
@[expose]
noncomputable def gExp5c (ph : Wff) (ps : Wff) (ch : Wff) (th : Wff) (ta : Wff)
    (et : Wff)
    (hyp_exp5c_1 : Nominal.NPrf (.imp ph (.imp (synWa ps ch) (.imp (synWa th ta) et)))) :
    Nominal.NPrf (.imp ph (.imp ps (.imp ch (.imp th (.imp ta et))))) :=
  by
  have p0000 := @gExp4a ph (synWa ps ch) th ta et hyp_exp5c_1
  have p0001 := @gExp3a ph ps ch (.imp th (.imp ta et)) p0000
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_impr`. -/
@[expose]
noncomputable def gImpr (ph : Wff) (ps : Wff) (ch : Wff) (th : Wff)
    (hyp_impr_1 : Nominal.NPrf (.imp (synWa ph ps) (.imp ch th))) :
    Nominal.NPrf (.imp (synWa ph (synWa ps ch)) th) :=
  by
  have p0000 := @gEx ph ps (.imp ch th) hyp_impr_1
  have p0001 := @gImp32 ph ps ch th p0000
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_impac`. -/
@[expose]
noncomputable def gImpac (ph : Wff) (ps : Wff) (ch : Wff)
    (hyp_impac_1 : Nominal.NPrf (.imp ph (.imp ps ch))) :
    Nominal.NPrf (.imp (synWa ph ps) (synWa ch ps)) :=
  by
  have p0000 := @gAncrd ph ps ch hyp_impac_1
  have p0001 := @gImp ph ps (synWa ch ps) p0000
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_simprbda`. -/
@[expose]
noncomputable def gSimprbda (ph : Wff) (ps : Wff) (ch : Wff) (th : Wff)
    (hyp_pm3_26bda_1 : Nominal.NPrf (.imp ph (synWb ps (synWa ch th)))) :
    Nominal.NPrf (.imp (synWa ph ps) ch) :=
  by
  have p0000 := @gBiimpa ph ps (synWa ch th) hyp_pm3_26bda_1
  have p0001 := @gSimpld (synWa ph ps) ch th p0000
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_simplbi2`. -/
@[expose]
noncomputable def gSimplbi2 (ph : Wff) (ps : Wff) (ch : Wff)
    (hyp_pm3_26bi2_1 : Nominal.NPrf (synWb ph (synWa ps ch))) :
    Nominal.NPrf (.imp ps (.imp ch ph)) :=
  by
  have p0000 := @gBiimpri ph (synWa ps ch) hyp_pm3_26bi2_1
  have p0001 := @gEx ps ch ph p0000
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_dfbi2`. -/
@[expose]
noncomputable def gDfbi2 (ph : Wff) (ps : Wff) :
    Nominal.NPrf (synWb (synWb ph ps) (synWa (.imp ph ps) (.imp ps ph))) :=
  by
  have p0000 := @gDfbi1 ph ps
  have p0001 := (Nominal.biimpRefl (synWa (.imp ph ps) (.imp ps ph)))
  have p0002 :=
    @gBitr4i (synWb ph ps) (.neg (.imp (.imp ph ps) (.neg (.imp ps ph))))
      (synWa (.imp ph ps) (.imp ps ph)) p0000 p0001
  exact p0002

/-- Checked nominal proof certificate identified upstream as `g_pm4_71`. -/
@[expose]
noncomputable def gPm471 (ph : Wff) (ps : Wff) :
    Nominal.NPrf (synWb (.imp ph ps) (synWb ph (synWa ph ps))) :=
  by
  have p0000 := @gSimpl ph ps
  have p0001 := @gBiantru (.imp (synWa ph ps) ph) (.imp ph (synWa ph ps)) p0000
  have p0002 := @gAnclb ph ps
  have p0003 := @gDfbi2 ph (synWa ph ps)
  have p0004 :=
    @gN3bitr4i (.imp ph (synWa ph ps))
      (synWa (.imp ph (synWa ph ps)) (.imp (synWa ph ps) ph)) (.imp ph ps)
      (synWb ph (synWa ph ps)) p0001 p0002 p0003
  exact p0004

/-- Checked nominal proof certificate identified upstream as `g_pm4_71r`. -/
@[expose]
noncomputable def gPm471r (ph : Wff) (ps : Wff) :
    Nominal.NPrf (synWb (.imp ph ps) (synWb ph (synWa ps ph))) :=
  by
  have p0000 := @gPm471 ph ps
  have p0001 := @gAncom ph ps
  have p0002 := @gBibi2i (synWa ph ps) (synWa ps ph) ph p0001
  have p0003 :=
    @gBitri (.imp ph ps) (synWb ph (synWa ph ps)) (synWb ph (synWa ps ph)) p0000
      p0002
  exact p0003

/-- Checked nominal proof certificate identified upstream as `g_pm4_71i`. -/
@[expose]
noncomputable def gPm471i (ph : Wff) (ps : Wff)
    (hyp_pm4_71i_1 : Nominal.NPrf (.imp ph ps)) :
    Nominal.NPrf (synWb ph (synWa ph ps)) :=
  by
  have p0000 := @gPm471 ph ps
  have p0001 := @gMpbi (.imp ph ps) (synWb ph (synWa ph ps)) hyp_pm4_71i_1 p0000
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_pm4_71ri`. -/
@[expose]
noncomputable def gPm471ri (ph : Wff) (ps : Wff)
    (hyp_pm4_71ri_1 : Nominal.NPrf (.imp ph ps)) :
    Nominal.NPrf (synWb ph (synWa ps ph)) :=
  by
  have p0000 := @gPm471r ph ps
  have p0001 := @gMpbi (.imp ph ps) (synWb ph (synWa ps ph)) hyp_pm4_71ri_1 p0000
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_pm4_71rd`. -/
@[expose]
noncomputable def gPm471rd (ph : Wff) (ps : Wff) (ch : Wff)
    (hyp_pm4_71rd_1 : Nominal.NPrf (.imp ph (.imp ps ch))) :
    Nominal.NPrf (.imp ph (synWb ps (synWa ch ps))) :=
  by
  have p0000 := @gPm471r ps ch
  have p0001 := @gSylib ph (.imp ps ch) (synWb ps (synWa ch ps)) hyp_pm4_71rd_1 p0000
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_pm5_32`. -/
@[expose]
noncomputable def gPm532 (ph : Wff) (ps : Wff) (ch : Wff) :
    Nominal.NPrf
      (synWb (.imp ph (synWb ps ch)) (synWb (synWa ph ps) (synWa ph ch))) :=
  by
  have p0000 := @gNotbi ps ch
  have p0001 := @gImbi2i (synWb ps ch) (synWb (.neg ps) (.neg ch)) ph p0000
  have p0002 := @gPm574 ph (.neg ps) (.neg ch)
  have p0003 := @gNotbi (.imp ph (.neg ps)) (.imp ph (.neg ch))
  have p0004 :=
    @gN3bitri (.imp ph (synWb ps ch)) (.imp ph (synWb (.neg ps) (.neg ch)))
      (synWb (.imp ph (.neg ps)) (.imp ph (.neg ch)))
      (synWb (.neg (.imp ph (.neg ps))) (.neg (.imp ph (.neg ch)))) p0001 p0002 p0003
  have p0005 := (Nominal.biimpRefl (synWa ph ps))
  have p0006 := (Nominal.biimpRefl (synWa ph ch))
  have p0007 :=
    @gBibi12i (synWa ph ps) (.neg (.imp ph (.neg ps))) (synWa ph ch)
      (.neg (.imp ph (.neg ch))) p0005 p0006
  have p0008 :=
    @gBitr4i (.imp ph (synWb ps ch))
      (synWb (.neg (.imp ph (.neg ps))) (.neg (.imp ph (.neg ch))))
      (synWb (synWa ph ps) (synWa ph ch)) p0004 p0007
  exact p0008

/-- Checked nominal proof certificate identified upstream as `g_pm5_32i`. -/
@[expose]
noncomputable def gPm532i (ph : Wff) (ps : Wff) (ch : Wff)
    (hyp_pm5_32i_1 : Nominal.NPrf (.imp ph (synWb ps ch))) :
    Nominal.NPrf (synWb (synWa ph ps) (synWa ph ch)) :=
  by
  have p0000 := @gPm532 ph ps ch
  have p0001 :=
    @gMpbi (.imp ph (synWb ps ch)) (synWb (synWa ph ps) (synWa ph ch)) hyp_pm5_32i_1
      p0000
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_pm5_32ri`. -/
@[expose]
noncomputable def gPm532ri (ph : Wff) (ps : Wff) (ch : Wff)
    (hyp_pm5_32i_1 : Nominal.NPrf (.imp ph (synWb ps ch))) :
    Nominal.NPrf (synWb (synWa ps ph) (synWa ch ph)) :=
  by
  have p0000 := @gPm532i ph ps ch hyp_pm5_32i_1
  have p0001 := @gAncom ps ph
  have p0002 := @gAncom ch ph
  have p0003 :=
    @gN3bitr4i (synWa ph ps) (synWa ph ch) (synWa ps ph) (synWa ch ph) p0000 p0001
      p0002
  exact p0003

/-- Checked nominal proof certificate identified upstream as `g_pm5_32d`. -/
@[expose]
noncomputable def gPm532d (ph : Wff) (ps : Wff) (ch : Wff) (th : Wff)
    (hyp_pm5_32d_1 : Nominal.NPrf (.imp ph (.imp ps (synWb ch th)))) :
    Nominal.NPrf (.imp ph (synWb (synWa ps ch) (synWa ps th))) :=
  by
  have p0000 := @gPm532 ps ch th
  have p0001 :=
    @gSylib ph (.imp ps (synWb ch th)) (synWb (synWa ps ch) (synWa ps th))
      hyp_pm5_32d_1 p0000
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_pm5_32rd`. -/
@[expose]
noncomputable def gPm532rd (ph : Wff) (ps : Wff) (ch : Wff) (th : Wff)
    (hyp_pm5_32d_1 : Nominal.NPrf (.imp ph (.imp ps (synWb ch th)))) :
    Nominal.NPrf (.imp ph (synWb (synWa ch ps) (synWa th ps))) :=
  by
  have p0000 := @gPm532d ph ps ch th hyp_pm5_32d_1
  have p0001 := @gAncom ch ps
  have p0002 := @gAncom th ps
  have p0003 :=
    @gN3bitr4g ph (synWa ps ch) (synWa ps th) (synWa ch ps) (synWa th ps) p0000
      p0001 p0002
  exact p0003

/-- Checked nominal proof certificate identified upstream as `g_pm5_32da`. -/
@[expose]
noncomputable def gPm532da (ph : Wff) (ps : Wff) (ch : Wff) (th : Wff)
    (hyp_pm5_32da_1 : Nominal.NPrf (.imp (synWa ph ps) (synWb ch th))) :
    Nominal.NPrf (.imp ph (synWb (synWa ps ch) (synWa ps th))) :=
  by
  have p0000 := @gEx ph ps (synWb ch th) hyp_pm5_32da_1
  have p0001 := @gPm532d ph ps ch th p0000
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_biadan2`. -/
@[expose]
noncomputable def gBiadan2 (ph : Wff) (ps : Wff) (ch : Wff)
    (hyp_biadan2_1 : Nominal.NPrf (.imp ph ps))
    (hyp_biadan2_2 : Nominal.NPrf (.imp ps (synWb ph ch))) :
    Nominal.NPrf (synWb ph (synWa ps ch)) :=
  by
  have p0000 := @gPm471ri ph ps hyp_biadan2_1
  have p0001 := @gPm532i ps ph ch hyp_biadan2_2
  have p0002 := @gBitri ph (synWa ps ph) (synWa ps ch) p0000 p0001
  exact p0002

/-- Checked nominal proof certificate identified upstream as `g_pm4_24`. -/
@[expose]
noncomputable def gPm424 (ph : Wff) : Nominal.NPrf (synWb ph (synWa ph ph)) :=
  by
  have p0000 := @gId ph
  have p0001 := @gPm471i ph ph p0000
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_anidm`. -/
@[expose]
noncomputable def gAnidm (ph : Wff) : Nominal.NPrf (synWb (synWa ph ph) ph) :=
  by
  have p0000 := @gPm424 ph
  have p0001 := @gBicomi ph (synWa ph ph) p0000
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_anidms`. -/
@[expose]
noncomputable def gAnidms (ph : Wff) (ps : Wff)
    (hyp_anidms_1 : Nominal.NPrf (.imp (synWa ph ph) ps)) : Nominal.NPrf (.imp ph ps) :=
  by
  have p0000 := @gEx ph ph ps hyp_anidms_1
  have p0001 := @gPm243i ph ps p0000
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_anasss`. -/
@[expose]
noncomputable def gAnasss (ph : Wff) (ps : Wff) (ch : Wff) (th : Wff)
    (hyp_anasss_1 : Nominal.NPrf (.imp (synWa (synWa ph ps) ch) th)) :
    Nominal.NPrf (.imp (synWa ph (synWa ps ch)) th) :=
  by
  have p0000 := @gExp31 ph ps ch th hyp_anasss_1
  have p0001 := @gImp32 ph ps ch th p0000
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_anassrs`. -/
@[expose]
noncomputable def gAnassrs (ph : Wff) (ps : Wff) (ch : Wff) (th : Wff)
    (hyp_anassrs_1 : Nominal.NPrf (.imp (synWa ph (synWa ps ch)) th)) :
    Nominal.NPrf (.imp (synWa (synWa ph ps) ch) th) :=
  by
  have p0000 := @gExp32 ph ps ch th hyp_anassrs_1
  have p0001 := @gImp31 ph ps ch th p0000
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_anass`. -/
@[expose]
noncomputable def gAnass (ph : Wff) (ps : Wff) (ch : Wff) :
    Nominal.NPrf (synWb (synWa (synWa ph ps) ch) (synWa ph (synWa ps ch))) :=
  by
  have p0000 := @gId (synWa ph (synWa ps ch))
  have p0001 := @gAnassrs ph ps ch (synWa ph (synWa ps ch)) p0000
  have p0002 := @gId (synWa (synWa ph ps) ch)
  have p0003 := @gAnasss ph ps ch (synWa (synWa ph ps) ch) p0002
  have p0004 :=
    @gImpbii (synWa (synWa ph ps) ch) (synWa ph (synWa ps ch)) p0001 p0003
  exact p0004

/-- Checked nominal proof certificate identified upstream as `g_sylanl1`. -/
@[expose]
noncomputable def gSylanl1 (ph : Wff) (ps : Wff) (ch : Wff) (th : Wff) (ta : Wff)
    (hyp_sylanl1_1 : Nominal.NPrf (.imp ph ps))
    (hyp_sylanl1_2 : Nominal.NPrf (.imp (synWa (synWa ps ch) th) ta)) :
    Nominal.NPrf (.imp (synWa (synWa ph ch) th) ta) :=
  by
  have p0000 := @gAnim1i ph ps ch hyp_sylanl1_1
  have p0001 := @gSylan (synWa ph ch) (synWa ps ch) th ta p0000 hyp_sylanl1_2
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_sylanl2`. -/
@[expose]
noncomputable def gSylanl2 (ph : Wff) (ps : Wff) (ch : Wff) (th : Wff) (ta : Wff)
    (hyp_sylanl2_1 : Nominal.NPrf (.imp ph ch))
    (hyp_sylanl2_2 : Nominal.NPrf (.imp (synWa (synWa ps ch) th) ta)) :
    Nominal.NPrf (.imp (synWa (synWa ps ph) th) ta) :=
  by
  have p0000 := @gAnim2i ph ch ps hyp_sylanl2_1
  have p0001 := @gSylan (synWa ps ph) (synWa ps ch) th ta p0000 hyp_sylanl2_2
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_sylan2i`. -/
@[expose]
noncomputable def gSylan2i (ph : Wff) (ps : Wff) (ch : Wff) (th : Wff) (ta : Wff)
    (hyp_sylan2i_1 : Nominal.NPrf (.imp ph th))
    (hyp_sylan2i_2 : Nominal.NPrf (.imp ps (.imp (synWa ch th) ta))) :
    Nominal.NPrf (.imp ps (.imp (synWa ch ph) ta)) :=
  by
  have p0000 := @gA1i (.imp ph th) ps hyp_sylan2i_1
  have p0001 := @gSylan2d ps ph th ch ta p0000 hyp_sylan2i_2
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_sylan9`. -/
@[expose]
noncomputable def gSylan9 (ph : Wff) (ps : Wff) (ch : Wff) (th : Wff) (ta : Wff)
    (hyp_sylan9_1 : Nominal.NPrf (.imp ph (.imp ps ch)))
    (hyp_sylan9_2 : Nominal.NPrf (.imp th (.imp ch ta))) :
    Nominal.NPrf (.imp (synWa ph th) (.imp ps ta)) :=
  by
  have p0000 := @gSyl9 ph ps ch th ta hyp_sylan9_1 hyp_sylan9_2
  have p0001 := @gImp ph th (.imp ps ta) p0000
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_sylan9r`. -/
@[expose]
noncomputable def gSylan9r (ph : Wff) (ps : Wff) (ch : Wff) (th : Wff) (ta : Wff)
    (hyp_sylan9r_1 : Nominal.NPrf (.imp ph (.imp ps ch)))
    (hyp_sylan9r_2 : Nominal.NPrf (.imp th (.imp ch ta))) :
    Nominal.NPrf (.imp (synWa th ph) (.imp ps ta)) :=
  by
  have p0000 := @gSyl9r ph ps ch th ta hyp_sylan9r_1 hyp_sylan9r_2
  have p0001 := @gImp th ph (.imp ps ta) p0000
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_mtand`. -/
@[expose]
noncomputable def gMtand (ph : Wff) (ps : Wff) (ch : Wff)
    (hyp_mtand_1 : Nominal.NPrf (.imp ph (.neg ch)))
    (hyp_mtand_2 : Nominal.NPrf (.imp (synWa ph ps) ch)) :
    Nominal.NPrf (.imp ph (.neg ps)) :=
  by
  have p0000 := @gEx ph ps ch hyp_mtand_2
  have p0001 := @gMtod ph ps ch hyp_mtand_1 p0000
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_syl2anc`. -/
@[expose]
noncomputable def gSyl2anc (ph : Wff) (ps : Wff) (ch : Wff) (th : Wff)
    (hyp_syl2anc_1 : Nominal.NPrf (.imp ph ps))
    (hyp_syl2anc_2 : Nominal.NPrf (.imp ph ch))
    (hyp_syl2anc_3 : Nominal.NPrf (.imp (synWa ps ch) th)) : Nominal.NPrf (.imp ph th) :=
  by
  have p0000 := @gEx ps ch th hyp_syl2anc_3
  have p0001 := @gSylc ph ps ch th hyp_syl2anc_1 hyp_syl2anc_2 p0000
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_sylancl`. -/
@[expose]
noncomputable def gSylancl (ph : Wff) (ps : Wff) (ch : Wff) (th : Wff)
    (hyp_sylancl_1 : Nominal.NPrf (.imp ph ps)) (hyp_sylancl_2 : Nominal.NPrf ch)
    (hyp_sylancl_3 : Nominal.NPrf (.imp (synWa ps ch) th)) : Nominal.NPrf (.imp ph th) :=
  by
  have p0000 := @gA1i ch ph hyp_sylancl_2
  have p0001 := @gSyl2anc ph ps ch th hyp_sylancl_1 p0000 hyp_sylancl_3
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_sylancr`. -/
@[expose]
noncomputable def gSylancr (ph : Wff) (ps : Wff) (ch : Wff) (th : Wff)
    (hyp_sylancr_1 : Nominal.NPrf ps) (hyp_sylancr_2 : Nominal.NPrf (.imp ph ch))
    (hyp_sylancr_3 : Nominal.NPrf (.imp (synWa ps ch) th)) : Nominal.NPrf (.imp ph th) :=
  by
  have p0000 := @gA1i ps ph hyp_sylancr_1
  have p0001 := @gSyl2anc ph ps ch th p0000 hyp_sylancr_2 hyp_sylancr_3
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_sylanbrc`. -/
@[expose]
noncomputable def gSylanbrc (ph : Wff) (ps : Wff) (ch : Wff) (th : Wff)
    (hyp_sylanbrc_1 : Nominal.NPrf (.imp ph ps))
    (hyp_sylanbrc_2 : Nominal.NPrf (.imp ph ch))
    (hyp_sylanbrc_3 : Nominal.NPrf (synWb th (synWa ps ch))) :
    Nominal.NPrf (.imp ph th) :=
  by
  have p0000 := @gJca ph ps ch hyp_sylanbrc_1 hyp_sylanbrc_2
  have p0001 := @gSylibr ph (synWa ps ch) th p0000 hyp_sylanbrc_3
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_mpdan`. -/
@[expose]
noncomputable def gMpdan (ph : Wff) (ps : Wff) (ch : Wff)
    (hyp_mpdan_1 : Nominal.NPrf (.imp ph ps))
    (hyp_mpdan_2 : Nominal.NPrf (.imp (synWa ph ps) ch)) : Nominal.NPrf (.imp ph ch) :=
  by
  have p0000 := @gId ph
  have p0001 := @gSyl2anc ph ph ps ch p0000 hyp_mpdan_1 hyp_mpdan_2
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_mpancom`. -/
@[expose]
noncomputable def gMpancom (ph : Wff) (ps : Wff) (ch : Wff)
    (hyp_mpancom_1 : Nominal.NPrf (.imp ps ph))
    (hyp_mpancom_2 : Nominal.NPrf (.imp (synWa ph ps) ch)) : Nominal.NPrf (.imp ps ch) :=
  by
  have p0000 := @gId ps
  have p0001 := @gSyl2anc ps ph ps ch hyp_mpancom_1 p0000 hyp_mpancom_2
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_mpan`. -/
@[expose]
noncomputable def gMpan (ph : Wff) (ps : Wff) (ch : Wff) (hyp_mpan_1 : Nominal.NPrf ph)
    (hyp_mpan_2 : Nominal.NPrf (.imp (synWa ph ps) ch)) : Nominal.NPrf (.imp ps ch) :=
  by
  have p0000 := @gA1i ph ps hyp_mpan_1
  have p0001 := @gMpancom ph ps ch p0000 hyp_mpan_2
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_mpan2`. -/
@[expose]
noncomputable def gMpan2 (ph : Wff) (ps : Wff) (ch : Wff) (hyp_mpan2_1 : Nominal.NPrf ps)
    (hyp_mpan2_2 : Nominal.NPrf (.imp (synWa ph ps) ch)) : Nominal.NPrf (.imp ph ch) :=
  by
  have p0000 := @gA1i ps ph hyp_mpan2_1
  have p0001 := @gMpdan ph ps ch p0000 hyp_mpan2_2
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_mp2an`. -/
@[expose]
noncomputable def gMp2an (ph : Wff) (ps : Wff) (ch : Wff) (hyp_mp2an_1 : Nominal.NPrf ph)
    (hyp_mp2an_2 : Nominal.NPrf ps)
    (hyp_mp2an_3 : Nominal.NPrf (.imp (synWa ph ps) ch)) : Nominal.NPrf ch :=
  by
  have p0000 := @gMpan ph ps ch hyp_mp2an_1 hyp_mp2an_3
  have p0001 := Nominal.mp hyp_mp2an_2 p0000
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_mp4an`. -/
@[expose]
noncomputable def gMp4an (ph : Wff) (ps : Wff) (ch : Wff) (th : Wff) (ta : Wff)
    (hyp_mp4an_1 : Nominal.NPrf ph) (hyp_mp4an_2 : Nominal.NPrf ps)
    (hyp_mp4an_3 : Nominal.NPrf ch) (hyp_mp4an_4 : Nominal.NPrf th)
    (hyp_mp4an_5 : Nominal.NPrf (.imp (synWa (synWa ph ps) (synWa ch th)) ta)) :
    Nominal.NPrf ta :=
  by
  have p0000 := @gPm32i ph ps hyp_mp4an_1 hyp_mp4an_2
  have p0001 := @gPm32i ch th hyp_mp4an_3 hyp_mp4an_4
  have p0002 := @gMp2an (synWa ph ps) (synWa ch th) ta p0000 p0001 hyp_mp4an_5
  exact p0002

/-- Checked nominal proof certificate identified upstream as `g_mpan2d`. -/
@[expose]
noncomputable def gMpan2d (ph : Wff) (ps : Wff) (ch : Wff) (th : Wff)
    (hyp_mpan2d_1 : Nominal.NPrf (.imp ph ch))
    (hyp_mpan2d_2 : Nominal.NPrf (.imp ph (.imp (synWa ps ch) th))) :
    Nominal.NPrf (.imp ph (.imp ps th)) :=
  by
  have p0000 := @gExp3a ph ps ch th hyp_mpan2d_2
  have p0001 := @gMpid ph ps ch th hyp_mpan2d_1 p0000
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_mpand`. -/
@[expose]
noncomputable def gMpand (ph : Wff) (ps : Wff) (ch : Wff) (th : Wff)
    (hyp_mpand_1 : Nominal.NPrf (.imp ph ps))
    (hyp_mpand_2 : Nominal.NPrf (.imp ph (.imp (synWa ps ch) th))) :
    Nominal.NPrf (.imp ph (.imp ch th)) :=
  by
  have p0000 := @gAncomsd ph ps ch th hyp_mpand_2
  have p0001 := @gMpan2d ph ch ps th hyp_mpand_1 p0000
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_mpani`. -/
@[expose]
noncomputable def gMpani (ph : Wff) (ps : Wff) (ch : Wff) (th : Wff)
    (hyp_mpani_1 : Nominal.NPrf ps)
    (hyp_mpani_2 : Nominal.NPrf (.imp ph (.imp (synWa ps ch) th))) :
    Nominal.NPrf (.imp ph (.imp ch th)) :=
  by
  have p0000 := @gA1i ps ph hyp_mpani_1
  have p0001 := @gMpand ph ps ch th p0000 hyp_mpani_2
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_mpan2i`. -/
@[expose]
noncomputable def gMpan2i (ph : Wff) (ps : Wff) (ch : Wff) (th : Wff)
    (hyp_mpan2i_1 : Nominal.NPrf ch)
    (hyp_mpan2i_2 : Nominal.NPrf (.imp ph (.imp (synWa ps ch) th))) :
    Nominal.NPrf (.imp ph (.imp ps th)) :=
  by
  have p0000 := @gA1i ch ph hyp_mpan2i_1
  have p0001 := @gMpan2d ph ps ch th p0000 hyp_mpan2i_2
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_mp2ani`. -/
@[expose]
noncomputable def gMp2ani (ph : Wff) (ps : Wff) (ch : Wff) (th : Wff)
    (hyp_mp2ani_1 : Nominal.NPrf ps) (hyp_mp2ani_2 : Nominal.NPrf ch)
    (hyp_mp2ani_3 : Nominal.NPrf (.imp ph (.imp (synWa ps ch) th))) :
    Nominal.NPrf (.imp ph th) :=
  by
  have p0000 := @gMpani ph ps ch th hyp_mp2ani_1 hyp_mp2ani_3
  have p0001 := @gMpi ph ch th hyp_mp2ani_2 p0000
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_mp2and`. -/
@[expose]
noncomputable def gMp2and (ph : Wff) (ps : Wff) (ch : Wff) (th : Wff)
    (hyp_mp2and_1 : Nominal.NPrf (.imp ph ps)) (hyp_mp2and_2 : Nominal.NPrf (.imp ph ch))
    (hyp_mp2and_3 : Nominal.NPrf (.imp ph (.imp (synWa ps ch) th))) :
    Nominal.NPrf (.imp ph th) :=
  by
  have p0000 := @gMpand ph ps ch th hyp_mp2and_1 hyp_mp2and_3
  have p0001 := @gMpd ph ch th hyp_mp2and_2 p0000
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_mpanl1`. -/
@[expose]
noncomputable def gMpanl1 (ph : Wff) (ps : Wff) (ch : Wff) (th : Wff)
    (hyp_mpanl1_1 : Nominal.NPrf ph)
    (hyp_mpanl1_2 : Nominal.NPrf (.imp (synWa (synWa ph ps) ch) th)) :
    Nominal.NPrf (.imp (synWa ps ch) th) :=
  by
  have p0000 := @gJctl ps ph hyp_mpanl1_1
  have p0001 := @gSylan ps (synWa ph ps) ch th p0000 hyp_mpanl1_2
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_mpanl2`. -/
@[expose]
noncomputable def gMpanl2 (ph : Wff) (ps : Wff) (ch : Wff) (th : Wff)
    (hyp_mpanl2_1 : Nominal.NPrf ps)
    (hyp_mpanl2_2 : Nominal.NPrf (.imp (synWa (synWa ph ps) ch) th)) :
    Nominal.NPrf (.imp (synWa ph ch) th) :=
  by
  have p0000 := @gJctr ph ps hyp_mpanl2_1
  have p0001 := @gSylan ph (synWa ph ps) ch th p0000 hyp_mpanl2_2
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_mpanl12`. -/
@[expose]
noncomputable def gMpanl12 (ph : Wff) (ps : Wff) (ch : Wff) (th : Wff)
    (hyp_mpanl12_1 : Nominal.NPrf ph) (hyp_mpanl12_2 : Nominal.NPrf ps)
    (hyp_mpanl12_3 : Nominal.NPrf (.imp (synWa (synWa ph ps) ch) th)) :
    Nominal.NPrf (.imp ch th) :=
  by
  have p0000 := @gMpanl1 ph ps ch th hyp_mpanl12_1 hyp_mpanl12_3
  have p0001 := @gMpan ps ch th hyp_mpanl12_2 p0000
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_mpanr1`. -/
@[expose]
noncomputable def gMpanr1 (ph : Wff) (ps : Wff) (ch : Wff) (th : Wff)
    (hyp_mpanr1_1 : Nominal.NPrf ps)
    (hyp_mpanr1_2 : Nominal.NPrf (.imp (synWa ph (synWa ps ch)) th)) :
    Nominal.NPrf (.imp (synWa ph ch) th) :=
  by
  have p0000 := @gAnassrs ph ps ch th hyp_mpanr1_2
  have p0001 := @gMpanl2 ph ps ch th hyp_mpanr1_1 p0000
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_mpanr2`. -/
@[expose]
noncomputable def gMpanr2 (ph : Wff) (ps : Wff) (ch : Wff) (th : Wff)
    (hyp_mpanr2_1 : Nominal.NPrf ch)
    (hyp_mpanr2_2 : Nominal.NPrf (.imp (synWa ph (synWa ps ch)) th)) :
    Nominal.NPrf (.imp (synWa ph ps) th) :=
  by
  have p0000 := @gJctr ps ch hyp_mpanr2_1
  have p0001 := @gSylan2 ps ph (synWa ps ch) th p0000 hyp_mpanr2_2
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_mpanr12`. -/
@[expose]
noncomputable def gMpanr12 (ph : Wff) (ps : Wff) (ch : Wff) (th : Wff)
    (hyp_mpanr12_1 : Nominal.NPrf ps) (hyp_mpanr12_2 : Nominal.NPrf ch)
    (hyp_mpanr12_3 : Nominal.NPrf (.imp (synWa ph (synWa ps ch)) th)) :
    Nominal.NPrf (.imp ph th) :=
  by
  have p0000 := @gMpanr1 ph ps ch th hyp_mpanr12_1 hyp_mpanr12_3
  have p0001 := @gMpan2 ph ch th hyp_mpanr12_2 p0000
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_pm5_74da`. -/
@[expose]
noncomputable def gPm574da (ph : Wff) (ps : Wff) (ch : Wff) (th : Wff)
    (hyp_pm5_74da_1 : Nominal.NPrf (.imp (synWa ph ps) (synWb ch th))) :
    Nominal.NPrf (.imp ph (synWb (.imp ps ch) (.imp ps th))) :=
  by
  have p0000 := @gEx ph ps (synWb ch th) hyp_pm5_74da_1
  have p0001 := @gPm574d ph ps ch th p0000
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_imdistani`. -/
@[expose]
noncomputable def gImdistani (ph : Wff) (ps : Wff) (ch : Wff)
    (hyp_imdistani_1 : Nominal.NPrf (.imp ph (.imp ps ch))) :
    Nominal.NPrf (.imp (synWa ph ps) (synWa ph ch)) :=
  by
  have p0000 := @gAnc2li ph ps ch hyp_imdistani_1
  have p0001 := @gImp ph ps (synWa ph ch) p0000
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_anbi2i`. -/
@[expose]
noncomputable def gAnbi2i (ph : Wff) (ps : Wff) (ch : Wff)
    (hyp_bi_aa : Nominal.NPrf (synWb ph ps)) :
    Nominal.NPrf (synWb (synWa ch ph) (synWa ch ps)) :=
  by
  have p0000 := @gA1i (synWb ph ps) ch hyp_bi_aa
  have p0001 := @gPm532i ch ph ps p0000
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_anbi1i`. -/
@[expose]
noncomputable def gAnbi1i (ph : Wff) (ps : Wff) (ch : Wff)
    (hyp_bi_aa : Nominal.NPrf (synWb ph ps)) :
    Nominal.NPrf (synWb (synWa ph ch) (synWa ps ch)) :=
  by
  have p0000 := @gA1i (synWb ph ps) ch hyp_bi_aa
  have p0001 := @gPm532ri ch ph ps p0000
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_anbi2ci`. -/
@[expose]
noncomputable def gAnbi2ci (ph : Wff) (ps : Wff) (ch : Wff)
    (hyp_bi_aa : Nominal.NPrf (synWb ph ps)) :
    Nominal.NPrf (synWb (synWa ph ch) (synWa ch ps)) :=
  by
  have p0000 := @gAnbi1i ph ps ch hyp_bi_aa
  have p0001 := @gAncom ps ch
  have p0002 := @gBitri (synWa ph ch) (synWa ps ch) (synWa ch ps) p0000 p0001
  exact p0002

/-- Checked nominal proof certificate identified upstream as `g_anbi12i`. -/
@[expose]
noncomputable def gAnbi12i (ph : Wff) (ps : Wff) (ch : Wff) (th : Wff)
    (hyp_anbi12_1 : Nominal.NPrf (synWb ph ps))
    (hyp_anbi12_2 : Nominal.NPrf (synWb ch th)) :
    Nominal.NPrf (synWb (synWa ph ch) (synWa ps th)) :=
  by
  have p0000 := @gAnbi1i ph ps ch hyp_anbi12_1
  have p0001 := @gAnbi2i ch th ps hyp_anbi12_2
  have p0002 := @gBitri (synWa ph ch) (synWa ps ch) (synWa ps th) p0000 p0001
  exact p0002

/-- Checked nominal proof certificate identified upstream as `g_anbi12ci`. -/
@[expose]
noncomputable def gAnbi12ci (ph : Wff) (ps : Wff) (ch : Wff) (th : Wff)
    (hyp_anbi12_1 : Nominal.NPrf (synWb ph ps))
    (hyp_anbi12_2 : Nominal.NPrf (synWb ch th)) :
    Nominal.NPrf (synWb (synWa ph ch) (synWa th ps)) :=
  by
  have p0000 := @gAnbi12i ph ps ch th hyp_anbi12_1 hyp_anbi12_2
  have p0001 := @gAncom ps th
  have p0002 := @gBitri (synWa ph ch) (synWa ps th) (synWa th ps) p0000 p0001
  exact p0002

/-- Checked nominal proof certificate identified upstream as `g_sylan9bb`. -/
@[expose]
noncomputable def gSylan9bb (ph : Wff) (ps : Wff) (ch : Wff) (th : Wff) (ta : Wff)
    (hyp_sylan9bb_1 : Nominal.NPrf (.imp ph (synWb ps ch)))
    (hyp_sylan9bb_2 : Nominal.NPrf (.imp th (synWb ch ta))) :
    Nominal.NPrf (.imp (synWa ph th) (synWb ps ta)) :=
  by
  have p0000 := @gAdantr ph (synWb ps ch) th hyp_sylan9bb_1
  have p0001 := @gAdantl th (synWb ch ta) ph hyp_sylan9bb_2
  have p0002 := @gBitrd (synWa ph th) ps ch ta p0000 p0001
  exact p0002

/-- Checked nominal proof certificate identified upstream as `g_sylan9bbr`. -/
@[expose]
noncomputable def gSylan9bbr (ph : Wff) (ps : Wff) (ch : Wff) (th : Wff) (ta : Wff)
    (hyp_sylan9bbr_1 : Nominal.NPrf (.imp ph (synWb ps ch)))
    (hyp_sylan9bbr_2 : Nominal.NPrf (.imp th (synWb ch ta))) :
    Nominal.NPrf (.imp (synWa th ph) (synWb ps ta)) :=
  by
  have p0000 := @gSylan9bb ph ps ch th ta hyp_sylan9bbr_1 hyp_sylan9bbr_2
  have p0001 := @gAncoms ph th (synWb ps ta) p0000
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_orbi2d`. -/
@[expose]
noncomputable def gOrbi2d (ph : Wff) (ps : Wff) (ch : Wff) (th : Wff)
    (hyp_bid_1 : Nominal.NPrf (.imp ph (synWb ps ch))) :
    Nominal.NPrf (.imp ph (synWb (synWo th ps) (synWo th ch))) :=
  by
  have p0000 := @gImbi2d ph ps ch (.neg th) hyp_bid_1
  have p0001 := (Nominal.biimpRefl (synWo th ps))
  have p0002 := (Nominal.biimpRefl (synWo th ch))
  have p0003 :=
    @gN3bitr4g ph (.imp (.neg th) ps) (.imp (.neg th) ch) (synWo th ps) (synWo th ch)
      p0000 p0001 p0002
  exact p0003

/-- Checked nominal proof certificate identified upstream as `g_orbi1d`. -/
@[expose]
noncomputable def gOrbi1d (ph : Wff) (ps : Wff) (ch : Wff) (th : Wff)
    (hyp_bid_1 : Nominal.NPrf (.imp ph (synWb ps ch))) :
    Nominal.NPrf (.imp ph (synWb (synWo ps th) (synWo ch th))) :=
  by
  have p0000 := @gOrbi2d ph ps ch th hyp_bid_1
  have p0001 := @gOrcom ps th
  have p0002 := @gOrcom ch th
  have p0003 :=
    @gN3bitr4g ph (synWo th ps) (synWo th ch) (synWo ps th) (synWo ch th) p0000
      p0001 p0002
  exact p0003

/-- Checked nominal proof certificate identified upstream as `g_anbi2d`. -/
@[expose]
noncomputable def gAnbi2d (ph : Wff) (ps : Wff) (ch : Wff) (th : Wff)
    (hyp_bid_1 : Nominal.NPrf (.imp ph (synWb ps ch))) :
    Nominal.NPrf (.imp ph (synWb (synWa th ps) (synWa th ch))) :=
  by
  have p0000 := @gA1d ph (synWb ps ch) th hyp_bid_1
  have p0001 := @gPm532d ph th ps ch p0000
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_anbi1d`. -/
@[expose]
noncomputable def gAnbi1d (ph : Wff) (ps : Wff) (ch : Wff) (th : Wff)
    (hyp_bid_1 : Nominal.NPrf (.imp ph (synWb ps ch))) :
    Nominal.NPrf (.imp ph (synWb (synWa ps th) (synWa ch th))) :=
  by
  have p0000 := @gA1d ph (synWb ps ch) th hyp_bid_1
  have p0001 := @gPm532rd ph th ps ch p0000
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_anbi1`. -/
@[expose]
noncomputable def gAnbi1 (ph : Wff) (ps : Wff) (ch : Wff) :
    Nominal.NPrf (.imp (synWb ph ps) (synWb (synWa ph ch) (synWa ps ch))) :=
  by
  have p0000 := @gId (synWb ph ps)
  have p0001 := @gAnbi1d (synWb ph ps) ph ps ch p0000
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_orbi12d`. -/
@[expose]
noncomputable def gOrbi12d (ph : Wff) (ps : Wff) (ch : Wff) (th : Wff) (ta : Wff)
    (hyp_bi12d_1 : Nominal.NPrf (.imp ph (synWb ps ch)))
    (hyp_bi12d_2 : Nominal.NPrf (.imp ph (synWb th ta))) :
    Nominal.NPrf (.imp ph (synWb (synWo ps th) (synWo ch ta))) :=
  by
  have p0000 := @gOrbi1d ph ps ch th hyp_bi12d_1
  have p0001 := @gOrbi2d ph th ta ch hyp_bi12d_2
  have p0002 := @gBitrd ph (synWo ps th) (synWo ch th) (synWo ch ta) p0000 p0001
  exact p0002

/-- Checked nominal proof certificate identified upstream as `g_anbi12d`. -/
@[expose]
noncomputable def gAnbi12d (ph : Wff) (ps : Wff) (ch : Wff) (th : Wff) (ta : Wff)
    (hyp_bi12d_1 : Nominal.NPrf (.imp ph (synWb ps ch)))
    (hyp_bi12d_2 : Nominal.NPrf (.imp ph (synWb th ta))) :
    Nominal.NPrf (.imp ph (synWb (synWa ps th) (synWa ch ta))) :=
  by
  have p0000 := @gAnbi1d ph ps ch th hyp_bi12d_1
  have p0001 := @gAnbi2d ph th ta ch hyp_bi12d_2
  have p0002 := @gBitrd ph (synWa ps th) (synWa ch th) (synWa ch ta) p0000 p0001
  exact p0002

/-- Checked nominal proof certificate identified upstream as `g_pm5_61`. -/
@[expose]
noncomputable def gPm561 (ph : Wff) (ps : Wff) :
    Nominal.NPrf (synWb (synWa (synWo ph ps) (.neg ps)) (synWa ph (.neg ps))) :=
  by
  have p0000 := @gBiorf ps ph
  have p0001 := @gOrcom ps ph
  have p0002 := @gSyl6rbb (.neg ps) ph (synWo ps ph) (synWo ph ps) p0000 p0001
  have p0003 := @gPm532ri (.neg ps) (synWo ph ps) ph p0002
  exact p0003

/-- Checked nominal proof certificate identified upstream as `g_adantll`. -/
@[expose]
noncomputable def gAdantll (ph : Wff) (ps : Wff) (ch : Wff) (th : Wff)
    (hyp_adant2_1 : Nominal.NPrf (.imp (synWa ph ps) ch)) :
    Nominal.NPrf (.imp (synWa (synWa th ph) ps) ch) :=
  by
  have p0000 := @gSimpr th ph
  have p0001 := @gSylan (synWa th ph) ph ps ch p0000 hyp_adant2_1
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_adantlr`. -/
@[expose]
noncomputable def gAdantlr (ph : Wff) (ps : Wff) (ch : Wff) (th : Wff)
    (hyp_adant2_1 : Nominal.NPrf (.imp (synWa ph ps) ch)) :
    Nominal.NPrf (.imp (synWa (synWa ph th) ps) ch) :=
  by
  have p0000 := @gSimpl ph th
  have p0001 := @gSylan (synWa ph th) ph ps ch p0000 hyp_adant2_1
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_adantrl`. -/
@[expose]
noncomputable def gAdantrl (ph : Wff) (ps : Wff) (ch : Wff) (th : Wff)
    (hyp_adant2_1 : Nominal.NPrf (.imp (synWa ph ps) ch)) :
    Nominal.NPrf (.imp (synWa ph (synWa th ps)) ch) :=
  by
  have p0000 := @gSimpr th ps
  have p0001 := @gSylan2 (synWa th ps) ph ps ch p0000 hyp_adant2_1
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_adantrr`. -/
@[expose]
noncomputable def gAdantrr (ph : Wff) (ps : Wff) (ch : Wff) (th : Wff)
    (hyp_adant2_1 : Nominal.NPrf (.imp (synWa ph ps) ch)) :
    Nominal.NPrf (.imp (synWa ph (synWa ps th)) ch) :=
  by
  have p0000 := @gSimpl ps th
  have p0001 := @gSylan2 (synWa ps th) ph ps ch p0000 hyp_adant2_1
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_adantllr`. -/
@[expose]
noncomputable def gAdantllr (ph : Wff) (ps : Wff) (ch : Wff) (th : Wff) (ta : Wff)
    (hyp_adantl2_1 : Nominal.NPrf (.imp (synWa (synWa ph ps) ch) th)) :
    Nominal.NPrf (.imp (synWa (synWa (synWa ph ta) ps) ch) th) :=
  by
  have p0000 := @gSimpl ph ta
  have p0001 := @gSylanl1 (synWa ph ta) ph ps ch th p0000 hyp_adantl2_1
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_adantlrr`. -/
@[expose]
noncomputable def gAdantlrr (ph : Wff) (ps : Wff) (ch : Wff) (th : Wff) (ta : Wff)
    (hyp_adantl2_1 : Nominal.NPrf (.imp (synWa (synWa ph ps) ch) th)) :
    Nominal.NPrf (.imp (synWa (synWa ph (synWa ps ta)) ch) th) :=
  by
  have p0000 := @gSimpl ps ta
  have p0001 := @gSylanl2 (synWa ps ta) ph ps ch th p0000 hyp_adantl2_1
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_ad2antrr`. -/
@[expose]
noncomputable def gAd2antrr (ph : Wff) (ps : Wff) (ch : Wff) (th : Wff)
    (hyp_ad2ant_1 : Nominal.NPrf (.imp ph ps)) :
    Nominal.NPrf (.imp (synWa (synWa ph ch) th) ps) :=
  by
  have p0000 := @gAdantr ph ps th hyp_ad2ant_1
  have p0001 := @gAdantlr ph th ps ch p0000
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_ad2antlr`. -/
@[expose]
noncomputable def gAd2antlr (ph : Wff) (ps : Wff) (ch : Wff) (th : Wff)
    (hyp_ad2ant_1 : Nominal.NPrf (.imp ph ps)) :
    Nominal.NPrf (.imp (synWa (synWa ch ph) th) ps) :=
  by
  have p0000 := @gAdantr ph ps th hyp_ad2ant_1
  have p0001 := @gAdantll ph th ps ch p0000
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_ad2antrl`. -/
@[expose]
noncomputable def gAd2antrl (ph : Wff) (ps : Wff) (ch : Wff) (th : Wff)
    (hyp_ad2ant_1 : Nominal.NPrf (.imp ph ps)) :
    Nominal.NPrf (.imp (synWa ch (synWa ph th)) ps) :=
  by
  have p0000 := @gAdantr ph ps th hyp_ad2ant_1
  have p0001 := @gAdantl (synWa ph th) ps ch p0000
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_ad2antll`. -/
@[expose]
noncomputable def gAd2antll (ph : Wff) (ps : Wff) (ch : Wff) (th : Wff)
    (hyp_ad2ant_1 : Nominal.NPrf (.imp ph ps)) :
    Nominal.NPrf (.imp (synWa ch (synWa th ph)) ps) :=
  by
  have p0000 := @gAdantl ph ps th hyp_ad2ant_1
  have p0001 := @gAdantl (synWa th ph) ps ch p0000
  exact p0001


end NFChoice.DirectNominalPrf.WPPReplay
