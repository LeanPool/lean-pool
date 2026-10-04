/-
Copyright (c) 2026 Elliot Glazer and NFNotWPP contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elliot Glazer and NFNotWPP contributors
-/

module

public import LeanPool.NFWeakPartition.NominalWPPReplayChunk004

/-! NF weak partition development: NominalWPPReplayChunk005. -/


public section


namespace NFChoice.DirectNominalPrf.WPPReplay

open scoped Fol
open NFChoice.Foundation
open NFChoice.SemanticCore
open NFChoice.ReplaySupport
open NFChoice.Compiler.CompactSourceSyntax

/-- Checked nominal proof certificate identified upstream as `g_hbae`. -/
@[expose]
noncomputable def gHbae (x : Var) (y : Var) (z : Var) :
    Nominal.NPrf (.imp (.all x (.objEq x y)) (.all z (.all x (.objEq x y)))) :=
  by
  have p0000 := @gSp (.objEq x y) x
  have p0001 := @gAx12o x y z
  have p0002 :=
    @gSyl7 (.all x (.objEq x y)) (.objEq x y) (.neg (.all z (.objEq z x)))
      (.neg (.all z (.objEq z y))) (.all z (.objEq x y)) p0000 p0001
  have p0003 := @gAx10o (.objEq x y) x z
  have p0004 := @gAecoms (.imp (.all x (.objEq x y)) (.all z (.objEq x y))) x z p0003
  have p0005 := @gAx10o (.objEq x y) x y
  have p0006 := @gPm243i (.all x (.objEq x y)) (.all y (.objEq x y)) p0005
  have p0007 := @gAx10o (.objEq x y) y z
  have p0008 :=
    @gSyl5 (.all x (.objEq x y)) (.all y (.objEq x y)) (.all y (.objEq y z))
      (.all z (.objEq x y)) p0006 p0007
  have p0009 := @gAecoms (.imp (.all x (.objEq x y)) (.all z (.objEq x y))) y z p0008
  have p0010 :=
    @gPm261ii (.all z (.objEq z x)) (.all z (.objEq z y))
      (.imp (.all x (.objEq x y)) (.all z (.objEq x y))) p0002 p0004 p0009
  have p0011 := @gA5i (.objEq x y) (.all z (.objEq x y)) x p0010
  have p0012 := Nominal.ax7Structural x z (.objEq x y)
  have p0013 :=
    @gSyl (.all x (.objEq x y)) (.all x (.all z (.objEq x y)))
      (.all z (.all x (.objEq x y))) p0011 p0012
  exact p0013

/-- Checked nominal proof certificate identified upstream as `g_nfae`. -/
@[expose]
noncomputable def gNfae (x : Var) (y : Var) (z : Var) :
    Nominal.NPrf (synWnf z (.all x (.objEq x y))) :=
  by
  have p0000 := @gHbae x y z
  have p0001 := @gNfi (.all x (.objEq x y)) z p0000
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_nfnae`. -/
@[expose]
noncomputable def gNfnae (x : Var) (y : Var) (z : Var) :
    Nominal.NPrf (synWnf z (.neg (.all x (.objEq x y)))) :=
  by
  have p0000 := @gNfae x y z
  have p0001 := @gNfn (.all x (.objEq x y)) z p0000
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_nfeqf`. -/
@[expose]
noncomputable def gNfeqf (x : Var) (y : Var) (z : Var) :
    Nominal.NPrf
      (.imp (synWa (.neg (.all z (.objEq z x))) (.neg (.all z (.objEq z y))))
        (synWnf z (.objEq x y))) :=
  by
  have p0000 := @gNfnae z x z
  have p0001 := @gNfnae z y z
  have p0002 :=
    @gNfan (.neg (.all z (.objEq z x))) (.neg (.all z (.objEq z y))) z p0000 p0001
  have p0003 := @gAx12o x y z
  have p0004 :=
    @gImp (.neg (.all z (.objEq z x))) (.neg (.all z (.objEq z y)))
      (.imp (.objEq x y) (.all z (.objEq x y))) p0003
  have p0005 :=
    @gNfd (synWa (.neg (.all z (.objEq z x))) (.neg (.all z (.objEq z y)))) (.objEq x y)
      z p0002 p0004
  exact p0005

/-- Checked nominal proof certificate identified upstream as `g_equs4`. -/
@[expose]
noncomputable def gEqus4 (ph : Wff) (x : Var) (y : Var) :
    Nominal.NPrf
      (.imp (.all x (.imp (.objEq x y) ph)) (synWex x (synWa (.objEq x y) ph))) :=
  by
  have p0000 := @gA9e x y
  have p0001 := @gN1929 (.imp (.objEq x y) ph) (.objEq x y) x
  have p0002 :=
    @gMpan2 (.all x (.imp (.objEq x y) ph)) (synWex x (.objEq x y))
      (synWex x (synWa (.imp (.objEq x y) ph) (.objEq x y))) p0000 p0001
  have p0003 := @gAncl (.objEq x y) ph
  have p0004 := @gImp (.imp (.objEq x y) ph) (.objEq x y) (synWa (.objEq x y) ph) p0003
  have p0005 :=
    @gEximi (synWa (.imp (.objEq x y) ph) (.objEq x y)) (synWa (.objEq x y) ph) x p0004
  have p0006 :=
    @gSyl (.all x (.imp (.objEq x y) ph))
      (synWex x (synWa (.imp (.objEq x y) ph) (.objEq x y)))
      (synWex x (synWa (.objEq x y) ph)) p0002 p0005
  exact p0006

/-- Checked nominal proof certificate identified upstream as `g_equsal`. -/
@[expose]
noncomputable def gEqusal (ph : Wff) (ps : Wff) (x : Var) (y : Var)
    (hyp_equsal_1 : Nominal.NPrf (synWnf x ps))
    (hyp_equsal_2 : Nominal.NPrf (.imp (.objEq x y) (synWb ph ps))) :
    Nominal.NPrf (synWb (.all x (.imp (.objEq x y) ph)) ps) :=
  by
  have p0000 := @gN193 ps x hyp_equsal_1
  have p0001 := @gSyl6bbr (.objEq x y) ph ps (.all x ps) hyp_equsal_2 p0000
  have p0002 := @gPm574i (.objEq x y) ph (.all x ps) p0001
  have p0003 := @gAlbii (.imp (.objEq x y) ph) (.imp (.objEq x y) (.all x ps)) x p0002
  have p0004 := @gNfri ps x hyp_equsal_1
  have p0005 := @gA1d ps (.all x ps) (.objEq x y) p0004
  have p0006 := @gAlrimi ps (.imp (.objEq x y) (.all x ps)) x hyp_equsal_1 p0005
  have p0007 := @gAx9o ps x y
  have p0008 := @gImpbii ps (.all x (.imp (.objEq x y) (.all x ps))) p0006 p0007
  have p0009 :=
    @gBitr4i (.all x (.imp (.objEq x y) ph)) (.all x (.imp (.objEq x y) (.all x ps))) ps
      p0003 p0008
  exact p0009

/-- Checked nominal proof certificate identified upstream as `g_equsex`. -/
@[expose]
noncomputable def gEqusex (ph : Wff) (ps : Wff) (x : Var) (y : Var)
    (hyp_equsex_1 : Nominal.NPrf (synWnf x ps))
    (hyp_equsex_2 : Nominal.NPrf (.imp (.objEq x y) (synWb ph ps))) :
    Nominal.NPrf (synWb (synWex x (synWa (.objEq x y) ph)) ps) :=
  by
  have p0000 := @gExnal (.imp (.objEq x y) (.neg ph)) x
  have p0001 := (Nominal.biimpRefl (synWa (.objEq x y) ph))
  have p0002 :=
    @gExbii (synWa (.objEq x y) ph) (.neg (.imp (.objEq x y) (.neg ph))) x p0001
  have p0003 := @gNfn ps x hyp_equsex_1
  have p0004 := @gNotbid (.objEq x y) ph ps hyp_equsex_2
  have p0005 := @gEqusal (.neg ph) (.neg ps) x y p0003 p0004
  have p0006 := @gCon2bii (.all x (.imp (.objEq x y) (.neg ph))) ps p0005
  have p0007 :=
    @gN3bitr4i (synWex x (.neg (.imp (.objEq x y) (.neg ph))))
      (.neg (.all x (.imp (.objEq x y) (.neg ph)))) (synWex x (synWa (.objEq x y) ph))
      ps p0000 p0002 p0006
  exact p0007

/-- Checked nominal proof certificate identified upstream as `g_dral1`. -/
@[expose]
noncomputable def gDral1 (ph : Wff) (ps : Wff) (x : Var) (y : Var)
    (hyp_dral1_1 : Nominal.NPrf (.imp (.all x (.objEq x y)) (synWb ph ps))) :
    Nominal.NPrf (.imp (.all x (.objEq x y)) (synWb (.all x ph) (.all y ps))) :=
  by
  have p0000 := @gHbae x y x
  have p0001 := @gBiimpd (.all x (.objEq x y)) ph ps hyp_dral1_1
  have p0002 := @gAlimdh (.all x (.objEq x y)) ph ps x p0000 p0001
  have p0003 := @gAx10o ps x y
  have p0004 :=
    @gSyld (.all x (.objEq x y)) (.all x ph) (.all x ps) (.all y ps) p0002 p0003
  have p0005 := @gHbae x y y
  have p0006 := @gBiimprd (.all x (.objEq x y)) ph ps hyp_dral1_1
  have p0007 := @gAlimdh (.all x (.objEq x y)) ps ph y p0005 p0006
  have p0008 := @gAx10o ph y x
  have p0009 := @gAecoms (.imp (.all y ph) (.all x ph)) y x p0008
  have p0010 :=
    @gSyld (.all x (.objEq x y)) (.all y ps) (.all y ph) (.all x ph) p0007 p0009
  have p0011 := @gImpbid (.all x (.objEq x y)) (.all x ph) (.all y ps) p0004 p0010
  exact p0011

/-- Checked nominal proof certificate identified upstream as `g_dral2`. -/
@[expose]
noncomputable def gDral2 (ph : Wff) (ps : Wff) (x : Var) (y : Var) (z : Var)
    (hyp_dral1_1 : Nominal.NPrf (.imp (.all x (.objEq x y)) (synWb ph ps))) :
    Nominal.NPrf (.imp (.all x (.objEq x y)) (synWb (.all z ph) (.all z ps))) :=
  by
  have p0000 := @gHbae x y z
  have p0001 := @gAlbidh (.all x (.objEq x y)) ph ps z p0000 hyp_dral1_1
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_drex1`. -/
@[expose]
noncomputable def gDrex1 (ph : Wff) (ps : Wff) (x : Var) (y : Var)
    (hyp_dral1_1 : Nominal.NPrf (.imp (.all x (.objEq x y)) (synWb ph ps))) :
    Nominal.NPrf (.imp (.all x (.objEq x y)) (synWb (synWex x ph) (synWex y ps))) :=
  by
  have p0000 := @gNotbid (.all x (.objEq x y)) ph ps hyp_dral1_1
  have p0001 := @gDral1 (.neg ph) (.neg ps) x y p0000
  have p0002 :=
    @gNotbid (.all x (.objEq x y)) (.all x (.neg ph)) (.all y (.neg ps)) p0001
  have p0003 := (Nominal.biimpRefl (synWex x ph))
  have p0004 := (Nominal.biimpRefl (synWex y ps))
  have p0005 :=
    @gN3bitr4g (.all x (.objEq x y)) (.neg (.all x (.neg ph))) (.neg (.all y (.neg ps)))
      (synWex x ph) (synWex y ps) p0002 p0003 p0004
  exact p0005

/-- Checked nominal proof certificate identified upstream as `g_drnf1`. -/
@[expose]
noncomputable def gDrnf1 (ph : Wff) (ps : Wff) (x : Var) (y : Var)
    (hyp_dral1_1 : Nominal.NPrf (.imp (.all x (.objEq x y)) (synWb ph ps))) :
    Nominal.NPrf (.imp (.all x (.objEq x y)) (synWb (synWnf x ph) (synWnf y ps))) :=
  by
  have p0000 := @gDral1 ph ps x y hyp_dral1_1
  have p0001 :=
    @gImbi12d (.all x (.objEq x y)) ph ps (.all x ph) (.all y ps) hyp_dral1_1 p0000
  have p0002 := @gDral1 (.imp ph (.all x ph)) (.imp ps (.all y ps)) x y p0001
  have p0003 := (Nominal.biimpRefl (synWnf x ph))
  have p0004 := (Nominal.biimpRefl (synWnf y ps))
  have p0005 :=
    @gN3bitr4g (.all x (.objEq x y)) (.all x (.imp ph (.all x ph)))
      (.all y (.imp ps (.all y ps))) (synWnf x ph) (synWnf y ps) p0002 p0003 p0004
  exact p0005

/-- Checked nominal proof certificate identified upstream as `g_drnf2`. -/
@[expose]
noncomputable def gDrnf2 (ph : Wff) (ps : Wff) (x : Var) (y : Var) (z : Var)
    (hyp_dral1_1 : Nominal.NPrf (.imp (.all x (.objEq x y)) (synWb ph ps))) :
    Nominal.NPrf (.imp (.all x (.objEq x y)) (synWb (synWnf z ph) (synWnf z ps))) :=
  by
  have p0000 := @gDral2 ph ps x y z hyp_dral1_1
  have p0001 :=
    @gImbi12d (.all x (.objEq x y)) ph ps (.all z ph) (.all z ps) hyp_dral1_1 p0000
  have p0002 := @gDral2 (.imp ph (.all z ph)) (.imp ps (.all z ps)) x y z p0001
  have p0003 := (Nominal.biimpRefl (synWnf z ph))
  have p0004 := (Nominal.biimpRefl (synWnf z ps))
  have p0005 :=
    @gN3bitr4g (.all x (.objEq x y)) (.all z (.imp ph (.all z ph)))
      (.all z (.imp ps (.all z ps))) (synWnf z ph) (synWnf z ps) p0002 p0003 p0004
  exact p0005

/-- Checked nominal proof certificate identified upstream as `g_nfald2`. -/
@[expose]
noncomputable def gNfald2 (ph : Wff) (ps : Wff) (x : Var) (y : Var)
    (hyp_nfald2_1 : Nominal.NPrf (synWnf y ph))
    (hyp_nfald2_2 :
      Nominal.NPrf (.imp (synWa ph (.neg (.all x (.objEq x y)))) (synWnf x ps))) :
    Nominal.NPrf (.imp ph (synWnf x (.all y ps))) :=
  by
  have p0000 := @gNfnae x y y
  have p0001 := @gNfan ph (.neg (.all x (.objEq x y))) y hyp_nfald2_1 p0000
  have p0002 :=
    @gNfald (synWa ph (.neg (.all x (.objEq x y)))) ps x y p0001 hyp_nfald2_2
  have p0003 := @gEx ph (.neg (.all x (.objEq x y))) (synWnf x (.all y ps)) p0002
  have p0004 := @gNfa1 ps y
  have p0005 := @gBiidd (.all x (.objEq x y)) (.all y ps)
  have p0006 := @gDrnf1 (.all y ps) (.all y ps) x y p0005
  have p0007 :=
    @gMpbiri (.all x (.objEq x y)) (synWnf x (.all y ps)) (synWnf y (.all y ps)) p0004
      p0006
  have p0008 := @gPm261d2 ph (.all x (.objEq x y)) (synWnf x (.all y ps)) p0003 p0007
  exact p0008

/-- Checked nominal proof certificate identified upstream as `g_nfexd2`. -/
@[expose]
noncomputable def gNfexd2 (ph : Wff) (ps : Wff) (x : Var) (y : Var)
    (hyp_nfald2_1 : Nominal.NPrf (synWnf y ph))
    (hyp_nfald2_2 :
      Nominal.NPrf (.imp (synWa ph (.neg (.all x (.objEq x y)))) (synWnf x ps))) :
    Nominal.NPrf (.imp ph (synWnf x (synWex y ps))) :=
  by
  have p0000 := (Nominal.biimpRefl (synWex y ps))
  have p0001 := @gNfnd (synWa ph (.neg (.all x (.objEq x y)))) ps x hyp_nfald2_2
  have p0002 := @gNfald2 ph (.neg ps) x y hyp_nfald2_1 p0001
  have p0003 := @gNfnd ph (.all y (.neg ps)) x p0002
  have p0004 := @gNfxfrd (synWex y ps) (.neg (.all y (.neg ps))) ph x p0000 p0003
  exact p0004

/-- Checked nominal proof certificate identified upstream as `g_spimt`. -/
@[expose]
noncomputable def gSpimt (ph : Wff) (ps : Wff) (x : Var) (y : Var) :
    Nominal.NPrf
      (.imp (synWa (synWnf x ps) (.all x (.imp (.objEq x y) (.imp ph ps))))
        (.imp (.all x ph) ps)) :=
  by
  have p0000 := @gNfnf1 ps x
  have p0001 := @gNfa1 ph x
  have p0002 := @gNfan (synWnf x ps) (.all x ph) x p0000 p0001
  have p0003 := @gSp ph x
  have p0004 := @gAdantl (.all x ph) ph (synWnf x ps) p0003
  have p0005 := @gNfr ps x
  have p0006 := @gAdantr (synWnf x ps) (.imp ps (.all x ps)) (.all x ph) p0005
  have p0007 :=
    @gEmbantd (synWa (synWnf x ps) (.all x ph)) ph ps (.all x ps) p0004 p0006
  have p0008 :=
    @gImim2d (synWa (synWnf x ps) (.all x ph)) (.imp ph ps) (.all x ps) (.objEq x y)
      p0007
  have p0009 :=
    @gAlimd (synWa (synWnf x ps) (.all x ph)) (.imp (.objEq x y) (.imp ph ps))
      (.imp (.objEq x y) (.all x ps)) x p0002 p0008
  have p0010 :=
    @gImpancom (synWnf x ps) (.all x ph) (.all x (.imp (.objEq x y) (.imp ph ps)))
      (.all x (.imp (.objEq x y) (.all x ps))) p0009
  have p0011 := @gAx9o ps x y
  have p0012 :=
    @gSyl6 (synWa (synWnf x ps) (.all x (.imp (.objEq x y) (.imp ph ps)))) (.all x ph)
      (.all x (.imp (.objEq x y) (.all x ps))) ps p0010 p0011
  exact p0012

/-- Checked nominal proof certificate identified upstream as `g_spim`. -/
@[expose]
noncomputable def gSpim (ph : Wff) (ps : Wff) (x : Var) (y : Var)
    (hyp_spim_1 : Nominal.NPrf (synWnf x ps))
    (hyp_spim_2 : Nominal.NPrf (.imp (.objEq x y) (.imp ph ps))) :
    Nominal.NPrf (.imp (.all x ph) ps) :=
  by
  have p0000 := Nominal.gen hyp_spim_2 x
  have p0001 := @gSpimt ph ps x y
  have p0002 :=
    @gMp2an (synWnf x ps) (.all x (.imp (.objEq x y) (.imp ph ps)))
      (.imp (.all x ph) ps) hyp_spim_1 p0000 p0001
  exact p0002

/-- Checked nominal proof certificate identified upstream as `g_spime`. -/
@[expose]
noncomputable def gSpime (ph : Wff) (ps : Wff) (x : Var) (y : Var)
    (hyp_spime_1 : Nominal.NPrf (synWnf x ph))
    (hyp_spime_2 : Nominal.NPrf (.imp (.objEq x y) (.imp ph ps))) :
    Nominal.NPrf (.imp ph (synWex x ps)) :=
  by
  have p0000 := @gNfn ph x hyp_spime_1
  have p0001 := @gCon3d (.objEq x y) ph ps hyp_spime_2
  have p0002 := @gSpim (.neg ps) (.neg ph) x y p0000 p0001
  have p0003 := @gCon2i (.all x (.neg ps)) ph p0002
  have p0004 := (Nominal.biimpRefl (synWex x ps))
  have p0005 := @gSylibr ph (.neg (.all x (.neg ps))) (synWex x ps) p0003 p0004
  exact p0005

/-- Checked nominal proof certificate identified upstream as `g_spimed`. -/
@[expose]
noncomputable def gSpimed (ph : Wff) (ps : Wff) (ch : Wff) (x : Var) (y : Var)
    (hyp_spimed_1 : Nominal.NPrf (.imp ch (synWnf x ph)))
    (hyp_spimed_2 : Nominal.NPrf (.imp (.objEq x y) (.imp ph ps))) :
    Nominal.NPrf (.imp ch (.imp ph (synWex x ps))) :=
  by
  have p0000 := @gNfnf1 ph x
  have p0001 := @gId (synWnf x ph)
  have p0002 := @gNfan1 (synWnf x ph) ph x p0000 p0001
  have p0003 := @gAdantld (.objEq x y) ph ps (synWnf x ph) hyp_spimed_2
  have p0004 := @gSpime (synWa (synWnf x ph) ph) ps x y p0002 p0003
  have p0005 := @gEx (synWnf x ph) ph (synWex x ps) p0004
  have p0006 := @gSyl ch (synWnf x ph) (.imp ph (synWex x ps)) hyp_spimed_1 p0005
  exact p0006

/-- Checked nominal proof certificate identified upstream as `g_cbv1h`. -/
@[expose]
noncomputable def gCbv1h (ph : Wff) (ps : Wff) (ch : Wff) (x : Var) (y : Var)
    (hyp_cbv1h_1 : Nominal.NPrf (.imp ph (.imp ps (.all y ps))))
    (hyp_cbv1h_2 : Nominal.NPrf (.imp ph (.imp ch (.all x ch))))
    (hyp_cbv1h_3 : Nominal.NPrf (.imp ph (.imp (.objEq x y) (.imp ps ch)))) :
    Nominal.NPrf (.imp (.all x (.all y ph)) (.imp (.all x ps) (.all y ch))) :=
  by
  have p0000 := @gSps ph (.imp ps (.all y ps)) y hyp_cbv1h_1
  have p0001 := @gAl2imi (.all y ph) ps (.all y ps) x p0000
  have p0002 := Nominal.ax7Structural x y ps
  have p0003 :=
    @gSyl6 (.all x (.all y ph)) (.all x ps) (.all x (.all y ps)) (.all y (.all x ps))
      p0001 p0002
  have p0004 := @gCom23 ph (.objEq x y) ps ch hyp_cbv1h_3
  have p0005 := @gSyl6d ph ps (.objEq x y) ch (.all x ch) p0004 hyp_cbv1h_2
  have p0006 := @gAl2imi ph ps (.imp (.objEq x y) (.all x ch)) x p0005
  have p0007 := @gAx9o ch x y
  have p0008 :=
    @gSyl6 (.all x ph) (.all x ps) (.all x (.imp (.objEq x y) (.all x ch))) ch p0006
      p0007
  have p0009 := @gAl2imi (.all x ph) (.all x ps) ch y p0008
  have p0010 := @gA7s ph (.imp (.all y (.all x ps)) (.all y ch)) y x p0009
  have p0011 :=
    @gSyld (.all x (.all y ph)) (.all x ps) (.all y (.all x ps)) (.all y ch) p0003 p0010
  exact p0011

/-- Checked nominal proof certificate identified upstream as `g_cbv1`. -/
@[expose]
noncomputable def gCbv1 (ph : Wff) (ps : Wff) (ch : Wff) (x : Var) (y : Var)
    (hyp_cbv1_1 : Nominal.NPrf (.imp ph (synWnf y ps)))
    (hyp_cbv1_2 : Nominal.NPrf (.imp ph (synWnf x ch)))
    (hyp_cbv1_3 : Nominal.NPrf (.imp ph (.imp (.objEq x y) (.imp ps ch)))) :
    Nominal.NPrf (.imp (.all x (.all y ph)) (.imp (.all x ps) (.all y ch))) :=
  by
  have p0000 := @gNfrd ph ps y hyp_cbv1_1
  have p0001 := @gNfrd ph ch x hyp_cbv1_2
  have p0002 := @gCbv1h ph ps ch x y p0000 p0001 hyp_cbv1_3
  exact p0002

/-- Checked nominal proof certificate identified upstream as `g_cbv2h`. -/
@[expose]
noncomputable def gCbv2h (ph : Wff) (ps : Wff) (ch : Wff) (x : Var) (y : Var)
    (hyp_cbv2h_1 : Nominal.NPrf (.imp ph (.imp ps (.all y ps))))
    (hyp_cbv2h_2 : Nominal.NPrf (.imp ph (.imp ch (.all x ch))))
    (hyp_cbv2h_3 : Nominal.NPrf (.imp ph (.imp (.objEq x y) (synWb ps ch)))) :
    Nominal.NPrf (.imp (.all x (.all y ph)) (synWb (.all x ps) (.all y ch))) :=
  by
  have p0000 := @gBi1 ps ch
  have p0001 := @gSyl6 ph (.objEq x y) (synWb ps ch) (.imp ps ch) hyp_cbv2h_3 p0000
  have p0002 := @gCbv1h ph ps ch x y hyp_cbv2h_1 hyp_cbv2h_2 p0001
  have p0003 := @gEqucomi y x
  have p0004 := @gBi2 ps ch
  have p0005 :=
    @gSyl56 (.objEq y x) (.objEq x y) ph (synWb ps ch) (.imp ch ps) p0003 hyp_cbv2h_3
      p0004
  have p0006 := @gCbv1h ph ch ps y x hyp_cbv2h_2 hyp_cbv2h_1 p0005
  have p0007 := @gA7s ph (.imp (.all y ch) (.all x ps)) y x p0006
  have p0008 := @gImpbid (.all x (.all y ph)) (.all x ps) (.all y ch) p0002 p0007
  exact p0008

/-- Checked nominal proof certificate identified upstream as `g_cbv2`. -/
@[expose]
noncomputable def gCbv2 (ph : Wff) (ps : Wff) (ch : Wff) (x : Var) (y : Var)
    (hyp_cbv2_1 : Nominal.NPrf (.imp ph (synWnf y ps)))
    (hyp_cbv2_2 : Nominal.NPrf (.imp ph (synWnf x ch)))
    (hyp_cbv2_3 : Nominal.NPrf (.imp ph (.imp (.objEq x y) (synWb ps ch)))) :
    Nominal.NPrf (.imp (.all x (.all y ph)) (synWb (.all x ps) (.all y ch))) :=
  by
  have p0000 := @gNfrd ph ps y hyp_cbv2_1
  have p0001 := @gNfrd ph ch x hyp_cbv2_2
  have p0002 := @gCbv2h ph ps ch x y p0000 p0001 hyp_cbv2_3
  exact p0002

/-- Checked nominal proof certificate identified upstream as `g_cbv3`. -/
@[expose]
noncomputable def gCbv3 (ph : Wff) (ps : Wff) (x : Var) (y : Var)
    (hyp_cbv3_1 : Nominal.NPrf (synWnf y ph)) (hyp_cbv3_2 : Nominal.NPrf (synWnf x ps))
    (hyp_cbv3_3 : Nominal.NPrf (.imp (.objEq x y) (.imp ph ps))) :
    Nominal.NPrf (.imp (.all x ph) (.all y ps)) :=
  by
  have p0000 := @gA1i (synWnf y ph) synWtru hyp_cbv3_1
  have p0001 := @gA1i (synWnf x ps) synWtru hyp_cbv3_2
  have p0002 := @gA1i (.imp (.objEq x y) (.imp ph ps)) synWtru hyp_cbv3_3
  have p0003 := @gCbv1 synWtru ph ps x y p0000 p0001 p0002
  have p0004 := @gTru
  have p0005 := Nominal.gen p0004 y
  have p0006 := @gMpg (.all y synWtru) (.imp (.all x ph) (.all y ps)) x p0003 p0005
  exact p0006

/-- Checked nominal proof certificate identified upstream as `g_cbv3h`. -/
@[expose]
noncomputable def gCbv3h (ph : Wff) (ps : Wff) (x : Var) (y : Var)
    (hyp_cbv3h_1 : Nominal.NPrf (.imp ph (.all y ph)))
    (hyp_cbv3h_2 : Nominal.NPrf (.imp ps (.all x ps)))
    (hyp_cbv3h_3 : Nominal.NPrf (.imp (.objEq x y) (.imp ph ps))) :
    Nominal.NPrf (.imp (.all x ph) (.all y ps)) :=
  by
  have p0000 := @gA1i (.imp ph (.all y ph)) (.objEq y y) hyp_cbv3h_1
  have p0001 := @gA1i (.imp ps (.all x ps)) (.objEq y y) hyp_cbv3h_2
  have p0002 := @gA1i (.imp (.objEq x y) (.imp ph ps)) (.objEq y y) hyp_cbv3h_3
  have p0003 := @gCbv1h (.objEq y y) ph ps x y p0000 p0001 p0002
  have p0004 := @gStdpc6 y
  have p0005 := @gMpg (.all y (.objEq y y)) (.imp (.all x ph) (.all y ps)) x p0003 p0004
  exact p0005

/-- Checked nominal proof certificate identified upstream as `g_cbval`. -/
@[expose]
noncomputable def gCbval (ph : Wff) (ps : Wff) (x : Var) (y : Var)
    (hyp_cbval_1 : Nominal.NPrf (synWnf y ph))
    (hyp_cbval_2 : Nominal.NPrf (synWnf x ps))
    (hyp_cbval_3 : Nominal.NPrf (.imp (.objEq x y) (synWb ph ps))) :
    Nominal.NPrf (synWb (.all x ph) (.all y ps)) :=
  by
  have p0000 := @gBiimpd (.objEq x y) ph ps hyp_cbval_3
  have p0001 := @gCbv3 ph ps x y hyp_cbval_1 hyp_cbval_2 p0000
  have p0002 := @gBiimprd (.objEq x y) ph ps hyp_cbval_3
  have p0003 := @gEqucoms (.imp ps ph) x y p0002
  have p0004 := @gCbv3 ps ph y x hyp_cbval_2 hyp_cbval_1 p0003
  have p0005 := @gImpbii (.all x ph) (.all y ps) p0001 p0004
  exact p0005

/-- Checked nominal proof certificate identified upstream as `g_cbvex`. -/
@[expose]
noncomputable def gCbvex (ph : Wff) (ps : Wff) (x : Var) (y : Var)
    (hyp_cbvex_1 : Nominal.NPrf (synWnf y ph))
    (hyp_cbvex_2 : Nominal.NPrf (synWnf x ps))
    (hyp_cbvex_3 : Nominal.NPrf (.imp (.objEq x y) (synWb ph ps))) :
    Nominal.NPrf (synWb (synWex x ph) (synWex y ps)) :=
  by
  have p0000 := @gNfn ph y hyp_cbvex_1
  have p0001 := @gNfn ps x hyp_cbvex_2
  have p0002 := @gNotbid (.objEq x y) ph ps hyp_cbvex_3
  have p0003 := @gCbval (.neg ph) (.neg ps) x y p0000 p0001 p0002
  have p0004 := @gNotbii (.all x (.neg ph)) (.all y (.neg ps)) p0003
  have p0005 := (Nominal.biimpRefl (synWex x ph))
  have p0006 := (Nominal.biimpRefl (synWex y ps))
  have p0007 :=
    @gN3bitr4i (.neg (.all x (.neg ph))) (.neg (.all y (.neg ps))) (synWex x ph)
      (synWex y ps) p0004 p0005 p0006
  exact p0007

/-- Checked nominal proof certificate identified upstream as `g_chvar`. -/
@[expose]
noncomputable def gChvar (ph : Wff) (ps : Wff) (x : Var) (y : Var)
    (hyp_chvar_1 : Nominal.NPrf (synWnf x ps))
    (hyp_chvar_2 : Nominal.NPrf (.imp (.objEq x y) (synWb ph ps)))
    (hyp_chvar_3 : Nominal.NPrf ph) : Nominal.NPrf ps :=
  by
  have p0000 := @gBiimpd (.objEq x y) ph ps hyp_chvar_2
  have p0001 := @gSpim ph ps x y hyp_chvar_1 p0000
  have p0002 := @gMpg ph ps x p0001 hyp_chvar_3
  exact p0002

/-- Checked nominal proof certificate identified upstream as `g_equvini`. -/
@[expose]
noncomputable def gEquvini (x : Var) (y : Var) (z : Var) :
    Nominal.NPrf (.imp (.objEq x y) (synWex z (synWa (.objEq x z) (.objEq z y)))) :=
  by
  have p0000 := @gEqucomi z x
  have p0001 := @gAlimi (.objEq z x) (.objEq x z) z p0000
  have p0002 := @gA9e z y
  have p0003 :=
    @gJctir (.all z (.objEq z x)) (.all z (.objEq x z)) (synWex z (.objEq z y)) p0001
      p0002
  have p0004 :=
    @gA1d (.all z (.objEq z x)) (synWa (.all z (.objEq x z)) (synWex z (.objEq z y)))
      (.objEq x y) p0003
  have p0005 := @gN1929 (.objEq x z) (.objEq z y) z
  have p0006 :=
    @gSyl6 (.all z (.objEq z x)) (.objEq x y)
      (synWa (.all z (.objEq x z)) (synWex z (.objEq z y)))
      (synWex z (synWa (.objEq x z) (.objEq z y))) p0004 p0005
  have p0007 := @gA9e z x
  have p0008 := @gEximi (.objEq z x) (.objEq x z) z p0000
  have p0009 := Nominal.mp p0007 p0008
  have p0010 :=
    @gN2a1i (.all z (.objEq z y)) (.objEq x y) (synWex z (.objEq x z)) p0009
  have p0011 :=
    @gAnc2ri (.all z (.objEq z y)) (.objEq x y) (synWex z (.objEq x z)) p0010
  have p0012 := @gN1929r (.objEq x z) (.objEq z y) z
  have p0013 :=
    @gSyl6 (.all z (.objEq z y)) (.objEq x y)
      (synWa (synWex z (.objEq x z)) (.all z (.objEq z y)))
      (synWex z (synWa (.objEq x z) (.objEq z y))) p0011 p0012
  have p0014 := @gIoran (.all z (.objEq z x)) (.all z (.objEq z y))
  have p0015 := @gNfeqf x y z
  have p0016 := Nominal.ax8 x z y
  have p0017 := @gAnc2li (.objEq x z) (.objEq x y) (.objEq z y) p0016
  have p0018 :=
    @gEqucoms (.imp (.objEq x y) (synWa (.objEq x z) (.objEq z y))) x z p0017
  have p0019 :=
    @gSpimed (.objEq x y) (synWa (.objEq x z) (.objEq z y))
      (synWa (.neg (.all z (.objEq z x))) (.neg (.all z (.objEq z y)))) z x p0015 p0018
  have p0020 :=
    @gSylbi (.neg (synWo (.all z (.objEq z x)) (.all z (.objEq z y))))
      (synWa (.neg (.all z (.objEq z x))) (.neg (.all z (.objEq z y))))
      (.imp (.objEq x y) (synWex z (synWa (.objEq x z) (.objEq z y)))) p0014 p0019
  have p0021 :=
    @gEcase3 (.all z (.objEq z x)) (.all z (.objEq z y))
      (.imp (.objEq x y) (synWex z (synWa (.objEq x z) (.objEq z y)))) p0006 p0013 p0020
  exact p0021

/-- Checked nominal proof certificate identified upstream as `g_spimv`. -/
@[expose]
noncomputable def gSpimv (ph : Wff) (ps : Wff) (x : Var) (y : Var) (dv_ps_x : x ∉ ps.fv)
    (hyp_spimv_1 : Nominal.NPrf (.imp (.objEq x y) (.imp ph ps))) :
    Nominal.NPrf (.imp (.all x ph) ps) :=
  by
  let proofSupport : Finset Var :=
    ph.fv ∪ ps.fv ∪ ({ x } : Finset Var) ∪ ({ y } : Finset Var)
  have p0000 :=
    @gNfv ps x
      (by
        first
        | (aesop))
  have p0001 := @gSpim ph ps x y p0000 hyp_spimv_1
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_ax11v2`. -/
@[expose]
noncomputable def gAx11v2 (ph : Wff) (x : Var) (y : Var) (z : Var) (dv_ph_z : z ∉ ph.fv)
    (dv_x_z : x ≠ z) (dv_y_z : y ≠ z)
    (hyp_ax11v2_1 :
      Nominal.NPrf (.imp (.objEq x z) (.imp ph (.all x (.imp (.objEq x z) ph))))) :
    Nominal.NPrf
      (.imp (.neg (.all x (.objEq x y)))
        (.imp (.objEq x y) (.imp ph (.all x (.imp (.objEq x y) ph))))) :=
  by
  let proofSupport : Finset Var :=
    ph.fv ∪ ({ x } : Finset Var) ∪ ({ y } : Finset Var) ∪ ({ z } : Finset Var)
  have p0000 :=
    @gA9ev z y
      (by
        first
        | (aesop))
  have p0001 := @gEquequ2 z y x
  have p0002 :=
    @gAdantl (.objEq z y) (synWb (.objEq x z) (.objEq x y)) (.neg (.all x (.objEq x y)))
      p0001
  have p0003 :=
    @gDveeq2 x y z
      (by
        first
        | (aesop))
  have p0004 :=
    @gImp (.neg (.all x (.objEq x y))) (.objEq z y) (.all x (.objEq z y)) p0003
  have p0005 := @gNfa1 (.objEq z y) x
  have p0006 := @gImbi1d (.objEq z y) (.objEq x z) (.objEq x y) ph p0001
  have p0007 :=
    @gSps (.objEq z y) (synWb (.imp (.objEq x z) ph) (.imp (.objEq x y) ph)) x p0006
  have p0008 :=
    @gAlbid (.all x (.objEq z y)) (.imp (.objEq x z) ph) (.imp (.objEq x y) ph) x p0005
      p0007
  have p0009 :=
    @gSyl (synWa (.neg (.all x (.objEq x y))) (.objEq z y)) (.all x (.objEq z y))
      (synWb (.all x (.imp (.objEq x z) ph)) (.all x (.imp (.objEq x y) ph))) p0004 p0008
  have p0010 :=
    @gImbi2d (synWa (.neg (.all x (.objEq x y))) (.objEq z y))
      (.all x (.imp (.objEq x z) ph)) (.all x (.imp (.objEq x y) ph)) ph p0009
  have p0011 :=
    @gImbi12d (synWa (.neg (.all x (.objEq x y))) (.objEq z y)) (.objEq x z)
      (.objEq x y) (.imp ph (.all x (.imp (.objEq x z) ph)))
      (.imp ph (.all x (.imp (.objEq x y) ph))) p0002 p0010
  have p0012 :=
    @gMpbii (synWa (.neg (.all x (.objEq x y))) (.objEq z y))
      (.imp (.objEq x z) (.imp ph (.all x (.imp (.objEq x z) ph))))
      (.imp (.objEq x y) (.imp ph (.all x (.imp (.objEq x y) ph)))) hyp_ax11v2_1 p0011
  have p0013 :=
    @gEx (.neg (.all x (.objEq x y))) (.objEq z y)
      (.imp (.objEq x y) (.imp ph (.all x (.imp (.objEq x y) ph)))) p0012
  have p0014 :=
    @gExlimdv (.neg (.all x (.objEq x y))) (.objEq z y)
      (.imp (.objEq x y) (.imp ph (.all x (.imp (.objEq x y) ph)))) z
      (by
        first
        |
          (simp (config :=
              { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp,
              NFChoice.Compiler.CoreFVSimp.fv_wff_objEq,
              NFChoice.Compiler.CoreFVSimp.fv_wff_all, Finset.mem_union,
              Finset.mem_erase] at ⊢;
            aesop))
      (by
        first
        |
          (simp (config :=
              { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_wff_neg,
              NFChoice.Compiler.CoreFVSimp.fv_wff_all,
              NFChoice.Compiler.CoreFVSimp.fv_wff_objEq, Finset.mem_erase] at ⊢;
            aesop))
      p0013
  have p0015 :=
    @gMpi (.neg (.all x (.objEq x y))) (synWex z (.objEq z y))
      (.imp (.objEq x y) (.imp ph (.all x (.imp (.objEq x y) ph)))) p0000 p0014
  exact p0015

/-- Checked nominal proof certificate identified upstream as `g_ax11a2`. -/
@[expose]
noncomputable def gAx11a2 (ph : Wff) (x : Var) (y : Var) (z : Var) (dv_ph_z : z ∉ ph.fv)
    (dv_x_z : x ≠ z) (dv_y_z : y ≠ z)
    (hyp_ax11a2_1 : Nominal.NPrf
        (.imp (.objEq x z) (.imp (.all z ph) (.all x (.imp (.objEq x z) ph))))) :
    Nominal.NPrf
      (.imp (.neg (.all x (.objEq x y)))
        (.imp (.objEq x y) (.imp ph (.all x (.imp (.objEq x y) ph))))) :=
  by
  let proofSupport : Finset Var :=
    ph.fv ∪ ({ x } : Finset Var) ∪ ({ y } : Finset Var) ∪ ({ z } : Finset Var)
  have p0000 :=
    Nominal.ax17 ph z
      (by
        first
        | (aesop))
  have p0001 :=
    @gSyl5 ph (.all z ph) (.objEq x z) (.all x (.imp (.objEq x z) ph)) p0000 hyp_ax11a2_1
  have p0002 :=
    @gAx11v2 ph x y z
      (by
        first
        | (aesop))
      (by
        first
        | (aesop))
      (by
        first
        | (aesop))
      p0001
  exact p0002

/-- Checked nominal proof certificate identified upstream as `g_ax11o`. -/
@[expose]
noncomputable def gAx11o (ph : Wff) (x : Var) (y : Var) :
    Nominal.NPrf
      (.imp (.neg (.all x (.objEq x y)))
        (.imp (.objEq x y) (.imp ph (.all x (.imp (.objEq x y) ph))))) :=
  by
  let proofSupport : Finset Var := ph.fv ∪ ({ x } : Finset Var) ∪ ({ y } : Finset Var)
  let z : Var := freshVar proofSupport 0
  have fresh_z : z ∉ proofSupport :=
    by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_z_not_ph : z ∉ ph.fv := by
    intro h
    exact fresh_z (Finset.mem_union_left _ (Finset.mem_union_left _ (h)))
  have fresh_z_ne_x : z ≠ x := by
    intro h
    exact
      fresh_z
        (Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_singleton.mpr h)))
  have fresh_x_ne_z : x ≠ z := Ne.symm fresh_z_ne_x
  have fresh_z_ne_y : z ≠ y := by
    intro h
    exact fresh_z (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))
  have fresh_y_ne_z : y ≠ z := Ne.symm fresh_z_ne_y
  have p0000 := Nominal.ax11Structural x z ph
  have p0001 :=
    @gAx11a2 ph x y z
      (by
        first
        | (aesop))
      (by
        first
        | (aesop))
      (by
        first
        | (aesop))
      p0000
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_equs5`. -/
@[expose]
noncomputable def gEqus5 (ph : Wff) (x : Var) (y : Var) :
    Nominal.NPrf
      (.imp (.neg (.all x (.objEq x y)))
        (.imp (synWex x (synWa (.objEq x y) ph)) (.all x (.imp (.objEq x y) ph)))) :=
  by
  have p0000 := @gNfnae x y x
  have p0001 := @gNfa1 (.imp (.objEq x y) ph) x
  have p0002 := @gAx11o ph x y
  have p0003 :=
    @gImp3a (.neg (.all x (.objEq x y))) (.objEq x y) ph (.all x (.imp (.objEq x y) ph))
      p0002
  have p0004 :=
    @gExlimd (.neg (.all x (.objEq x y))) (synWa (.objEq x y) ph)
      (.all x (.imp (.objEq x y) ph)) x p0000 p0001 p0003
  exact p0004

/-- Checked nominal proof certificate identified upstream as `g_spv`. -/
@[expose]
noncomputable def gSpv (ph : Wff) (ps : Wff) (x : Var) (y : Var) (dv_ps_x : x ∉ ps.fv)
    (hyp_spv_1 : Nominal.NPrf (.imp (.objEq x y) (synWb ph ps))) :
    Nominal.NPrf (.imp (.all x ph) ps) :=
  by
  let proofSupport : Finset Var :=
    ph.fv ∪ ps.fv ∪ ({ x } : Finset Var) ∪ ({ y } : Finset Var)
  have p0000 := @gBiimpd (.objEq x y) ph ps hyp_spv_1
  have p0001 :=
    @gSpimv ph ps x y
      (by
        first
        | (aesop))
      p0000
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_cbvalv`. -/
@[expose]
noncomputable def gCbvalv (ph : Wff) (ps : Wff) (x : Var) (y : Var) (dv_ph_y : y ∉ ph.fv)
    (dv_ps_x : x ∉ ps.fv)
    (hyp_cbvalv_1 : Nominal.NPrf (.imp (.objEq x y) (synWb ph ps))) :
    Nominal.NPrf (synWb (.all x ph) (.all y ps)) :=
  by
  let proofSupport : Finset Var :=
    ph.fv ∪ ps.fv ∪ ({ x } : Finset Var) ∪ ({ y } : Finset Var)
  have p0000 :=
    @gNfv ph y
      (by
        first
        | (aesop))
  have p0001 :=
    @gNfv ps x
      (by
        first
        | (aesop))
  have p0002 := @gCbval ph ps x y p0000 p0001 hyp_cbvalv_1
  exact p0002

/-- Checked nominal proof certificate identified upstream as `g_cbvexv`. -/
@[expose]
noncomputable def gCbvexv (ph : Wff) (ps : Wff) (x : Var) (y : Var) (dv_ph_y : y ∉ ph.fv)
    (dv_ps_x : x ∉ ps.fv)
    (hyp_cbvalv_1 : Nominal.NPrf (.imp (.objEq x y) (synWb ph ps))) :
    Nominal.NPrf (synWb (synWex x ph) (synWex y ps)) :=
  by
  let proofSupport : Finset Var :=
    ph.fv ∪ ps.fv ∪ ({ x } : Finset Var) ∪ ({ y } : Finset Var)
  have p0000 :=
    @gNfv ph y
      (by
        first
        | (aesop))
  have p0001 :=
    @gNfv ps x
      (by
        first
        | (aesop))
  have p0002 := @gCbvex ph ps x y p0000 p0001 hyp_cbvalv_1
  exact p0002

/-- Checked nominal proof certificate identified upstream as `g_cbval2`. -/
@[expose]
noncomputable def gCbval2 (ph : Wff) (ps : Wff) (x : Var) (y : Var) (z : Var) (w : Var)
    (dv_w_x : w ≠ x) (dv_w_z : w ≠ z) (dv_x_y : x ≠ y) (dv_y_z : y ≠ z)
    (hyp_cbval2_1 : Nominal.NPrf (synWnf z ph))
    (hyp_cbval2_2 : Nominal.NPrf (synWnf w ph))
    (hyp_cbval2_3 : Nominal.NPrf (synWnf x ps))
    (hyp_cbval2_4 : Nominal.NPrf (synWnf y ps))
    (hyp_cbval2_5 : Nominal.NPrf (.imp (synWa (.objEq x z) (.objEq y w)) (synWb ph ps))) :
    Nominal.NPrf (synWb (.all x (.all y ph)) (.all z (.all w ps))) :=
  by
  let proofSupport : Finset Var :=
    ph.fv ∪ ps.fv ∪ ({ x } : Finset Var) ∪ ({ y } : Finset Var) ∪ ({ z } : Finset Var) ∪
      ({ w } : Finset Var)
  have p0000 := @gNfal ph z y hyp_cbval2_1
  have p0001 := @gNfal ps x w hyp_cbval2_3
  have p0002 :=
    @gNfv (.objEq x z) w
      (by
        first
        |
          (simp (config :=
              {
                failIfUnchanged :=
                  false }) only [NFChoice.Compiler.CoreFVSimp.fv_wff_objEq] at ⊢;
            aesop))
  have p0003 := @gNfan (.objEq x z) ph w p0002 hyp_cbval2_2
  have p0004 :=
    @gNfv (.objEq x z) y
      (by
        first
        |
          (simp (config :=
              {
                failIfUnchanged :=
                  false }) only [NFChoice.Compiler.CoreFVSimp.fv_wff_objEq] at ⊢;
            aesop))
  have p0005 := @gNfan (.objEq x z) ps y p0004 hyp_cbval2_4
  have p0006 := @gExpcom (.objEq x z) (.objEq y w) (synWb ph ps) hyp_cbval2_5
  have p0007 := @gPm532d (.objEq y w) (.objEq x z) ph ps p0006
  have p0008 :=
    @gCbval (synWa (.objEq x z) ph) (synWa (.objEq x z) ps) y w p0003 p0005 p0007
  have p0009 :=
    @gN1928v (.objEq x z) ph y
      (by
        first
        |
          (simp (config :=
              {
                failIfUnchanged :=
                  false }) only [NFChoice.Compiler.CoreFVSimp.fv_wff_objEq] at ⊢;
            aesop))
  have p0010 :=
    @gN1928v (.objEq x z) ps w
      (by
        first
        |
          (simp (config :=
              {
                failIfUnchanged :=
                  false }) only [NFChoice.Compiler.CoreFVSimp.fv_wff_objEq] at ⊢;
            aesop))
  have p0011 :=
    @gN3bitr3i (.all y (synWa (.objEq x z) ph)) (.all w (synWa (.objEq x z) ps))
      (synWa (.objEq x z) (.all y ph)) (synWa (.objEq x z) (.all w ps)) p0008 p0009
      p0010
  have p0012 := @gPm532 (.objEq x z) (.all y ph) (.all w ps)
  have p0013 :=
    @gMpbir (.imp (.objEq x z) (synWb (.all y ph) (.all w ps)))
      (synWb (synWa (.objEq x z) (.all y ph)) (synWa (.objEq x z) (.all w ps))) p0011
      p0012
  have p0014 := @gCbval (.all y ph) (.all w ps) x z p0000 p0001 p0013
  exact p0014

/-- Checked nominal proof certificate identified upstream as `g_cbvex2`. -/
@[expose]
noncomputable def gCbvex2 (ph : Wff) (ps : Wff) (x : Var) (y : Var) (z : Var) (w : Var)
    (dv_w_x : w ≠ x) (dv_w_z : w ≠ z) (dv_x_y : x ≠ y) (dv_y_z : y ≠ z)
    (hyp_cbval2_1 : Nominal.NPrf (synWnf z ph))
    (hyp_cbval2_2 : Nominal.NPrf (synWnf w ph))
    (hyp_cbval2_3 : Nominal.NPrf (synWnf x ps))
    (hyp_cbval2_4 : Nominal.NPrf (synWnf y ps))
    (hyp_cbval2_5 : Nominal.NPrf (.imp (synWa (.objEq x z) (.objEq y w)) (synWb ph ps))) :
    Nominal.NPrf (synWb (synWex x (synWex y ph)) (synWex z (synWex w ps))) :=
  by
  let proofSupport : Finset Var :=
    ph.fv ∪ ps.fv ∪ ({ x } : Finset Var) ∪ ({ y } : Finset Var) ∪ ({ z } : Finset Var) ∪
      ({ w } : Finset Var)
  have p0000 := @gNfex ph z y hyp_cbval2_1
  have p0001 := @gNfex ps x w hyp_cbval2_3
  have p0002 :=
    @gNfv (.objEq x z) w
      (by
        first
        |
          (simp (config :=
              {
                failIfUnchanged :=
                  false }) only [NFChoice.Compiler.CoreFVSimp.fv_wff_objEq] at ⊢;
            aesop))
  have p0003 := @gNfan (.objEq x z) ph w p0002 hyp_cbval2_2
  have p0004 :=
    @gNfv (.objEq x z) y
      (by
        first
        |
          (simp (config :=
              {
                failIfUnchanged :=
                  false }) only [NFChoice.Compiler.CoreFVSimp.fv_wff_objEq] at ⊢;
            aesop))
  have p0005 := @gNfan (.objEq x z) ps y p0004 hyp_cbval2_4
  have p0006 := @gExpcom (.objEq x z) (.objEq y w) (synWb ph ps) hyp_cbval2_5
  have p0007 := @gPm532d (.objEq y w) (.objEq x z) ph ps p0006
  have p0008 :=
    @gCbvex (synWa (.objEq x z) ph) (synWa (.objEq x z) ps) y w p0003 p0005 p0007
  have p0009 :=
    @gN1942v (.objEq x z) ph y
      (by
        first
        |
          (simp (config :=
              {
                failIfUnchanged :=
                  false }) only [NFChoice.Compiler.CoreFVSimp.fv_wff_objEq] at ⊢;
            aesop))
  have p0010 :=
    @gN1942v (.objEq x z) ps w
      (by
        first
        |
          (simp (config :=
              {
                failIfUnchanged :=
                  false }) only [NFChoice.Compiler.CoreFVSimp.fv_wff_objEq] at ⊢;
            aesop))
  have p0011 :=
    @gN3bitr3i (synWex y (synWa (.objEq x z) ph)) (synWex w (synWa (.objEq x z) ps))
      (synWa (.objEq x z) (synWex y ph)) (synWa (.objEq x z) (synWex w ps)) p0008
      p0009 p0010
  have p0012 := @gPm532 (.objEq x z) (synWex y ph) (synWex w ps)
  have p0013 :=
    @gMpbir (.imp (.objEq x z) (synWb (synWex y ph) (synWex w ps)))
      (synWb (synWa (.objEq x z) (synWex y ph)) (synWa (.objEq x z) (synWex w ps)))
      p0011 p0012
  have p0014 := @gCbvex (synWex y ph) (synWex w ps) x z p0000 p0001 p0013
  exact p0014

/-- Checked nominal proof certificate identified upstream as `g_cbval2v`. -/
@[expose]
noncomputable def gCbval2v (ph : Wff) (ps : Wff) (x : Var) (y : Var) (z : Var) (w : Var)
    (dv_ph_w : w ∉ ph.fv) (dv_ph_z : z ∉ ph.fv) (dv_ps_x : x ∉ ps.fv)
    (dv_ps_y : y ∉ ps.fv) (dv_w_x : w ≠ x) (dv_w_z : w ≠ z) (dv_x_y : x ≠ y)
    (dv_y_z : y ≠ z)
    (hyp_cbval2v_1 : Nominal.NPrf (.imp (synWa (.objEq x z) (.objEq y w)) (synWb ph ps))) :
    Nominal.NPrf (synWb (.all x (.all y ph)) (.all z (.all w ps))) :=
  by
  let proofSupport : Finset Var :=
    ph.fv ∪ ps.fv ∪ ({ x } : Finset Var) ∪ ({ y } : Finset Var) ∪ ({ z } : Finset Var) ∪
      ({ w } : Finset Var)
  have p0000 :=
    @gNfv ph z
      (by
        first
        | (aesop))
  have p0001 :=
    @gNfv ph w
      (by
        first
        | (aesop))
  have p0002 :=
    @gNfv ps x
      (by
        first
        | (aesop))
  have p0003 :=
    @gNfv ps y
      (by
        first
        | (aesop))
  have p0004 :=
    @gCbval2 ph ps x y z w
      (by
        first
        | (aesop))
      (by
        first
        | (aesop))
      (by
        first
        | (aesop))
      (by
        first
        | (aesop))
      p0000 p0001 p0002 p0003 hyp_cbval2v_1
  exact p0004

/-- Checked nominal proof certificate identified upstream as `g_cbvald`. -/
@[expose]
noncomputable def gCbvald (ph : Wff) (ps : Wff) (ch : Wff) (x : Var) (y : Var)
    (dv_ch_x : x ∉ ch.fv) (dv_ph_x : x ∉ ph.fv)
    (hyp_cbvald_1 : Nominal.NPrf (synWnf y ph))
    (hyp_cbvald_2 : Nominal.NPrf (.imp ph (synWnf y ps)))
    (hyp_cbvald_3 : Nominal.NPrf (.imp ph (.imp (.objEq x y) (synWb ps ch)))) :
    Nominal.NPrf (.imp ph (synWb (.all x ps) (.all y ch))) :=
  by
  let proofSupport : Finset Var :=
    ph.fv ∪ ps.fv ∪ ch.fv ∪ ({ x } : Finset Var) ∪ ({ y } : Finset Var)
  have p0000 := @gNfri ph y hyp_cbvald_1
  have p0001 :=
    @gAlrimiv ph (.all y ph) x
      (by
        first
        | (aesop))
      p0000
  have p0002 :=
    @gNfvd ph ch x
      (by
        first
        | (aesop))
  have p0003 := @gCbv2 ph ps ch x y hyp_cbvald_2 p0002 hyp_cbvald_3
  have p0004 :=
    @gSyl ph (.all x (.all y ph)) (synWb (.all x ps) (.all y ch)) p0001 p0003
  exact p0004

/-- Checked nominal proof certificate identified upstream as `g_cbvexd`. -/
@[expose]
noncomputable def gCbvexd (ph : Wff) (ps : Wff) (ch : Wff) (x : Var) (y : Var)
    (dv_ch_x : x ∉ ch.fv) (dv_ph_x : x ∉ ph.fv)
    (hyp_cbvald_1 : Nominal.NPrf (synWnf y ph))
    (hyp_cbvald_2 : Nominal.NPrf (.imp ph (synWnf y ps)))
    (hyp_cbvald_3 : Nominal.NPrf (.imp ph (.imp (.objEq x y) (synWb ps ch)))) :
    Nominal.NPrf (.imp ph (synWb (synWex x ps) (synWex y ch))) :=
  by
  let proofSupport : Finset Var :=
    ph.fv ∪ ps.fv ∪ ch.fv ∪ ({ x } : Finset Var) ∪ ({ y } : Finset Var)
  have p0000 := @gNfnd ph ps y hyp_cbvald_2
  have p0001 := @gNotbi ps ch
  have p0002 :=
    @gSyl6ib ph (.objEq x y) (synWb ps ch) (synWb (.neg ps) (.neg ch)) hyp_cbvald_3
      p0001
  have p0003 :=
    @gCbvald ph (.neg ps) (.neg ch) x y
      (by
        first
        |
          (simp (config :=
              {
                failIfUnchanged :=
                  false }) only [NFChoice.Compiler.CoreFVSimp.fv_wff_neg] at ⊢;
            aesop))
      (by
        first
        | (aesop))
      hyp_cbvald_1 p0000 p0002
  have p0004 := @gNotbid ph (.all x (.neg ps)) (.all y (.neg ch)) p0003
  have p0005 := (Nominal.biimpRefl (synWex x ps))
  have p0006 := (Nominal.biimpRefl (synWex y ch))
  have p0007 :=
    @gN3bitr4g ph (.neg (.all x (.neg ps))) (.neg (.all y (.neg ch))) (synWex x ps)
      (synWex y ch) p0004 p0005 p0006
  exact p0007

/-- Checked nominal proof certificate identified upstream as `g_drsb1`. -/
@[expose]
noncomputable def gDrsb1 (ph : Wff) (x : Var) (y : Var) (z : Var) :
    Nominal.NPrf
      (.imp (.all x (.objEq x y)) (synWb (synWsb z x ph) (synWsb z y ph))) :=
  by
  have p0000 := @gEquequ1 x y z
  have p0001 := @gSps (.objEq x y) (synWb (.objEq x z) (.objEq y z)) x p0000
  have p0002 := @gImbi1d (.all x (.objEq x y)) (.objEq x z) (.objEq y z) ph p0001
  have p0003 := @gAnbi1d (.all x (.objEq x y)) (.objEq x z) (.objEq y z) ph p0001
  have p0004 := @gDrex1 (synWa (.objEq x z) ph) (synWa (.objEq y z) ph) x y p0003
  have p0005 :=
    @gAnbi12d (.all x (.objEq x y)) (.imp (.objEq x z) ph) (.imp (.objEq y z) ph)
      (synWex x (synWa (.objEq x z) ph)) (synWex y (synWa (.objEq y z) ph)) p0002
      p0004
  have p0006 := (Nominal.biimpRefl (synWsb z x ph))
  have p0007 := (Nominal.biimpRefl (synWsb z y ph))
  have p0008 :=
    @gN3bitr4g (.all x (.objEq x y))
      (synWa (.imp (.objEq x z) ph) (synWex x (synWa (.objEq x z) ph)))
      (synWa (.imp (.objEq y z) ph) (synWex y (synWa (.objEq y z) ph)))
      (synWsb z x ph) (synWsb z y ph) p0005 p0006 p0007
  exact p0008

/-- Checked nominal proof certificate identified upstream as `g_sb2`. -/
@[expose]
noncomputable def gSb2 (ph : Wff) (x : Var) (y : Var) :
    Nominal.NPrf (.imp (.all x (.imp (.objEq x y) ph)) (synWsb y x ph)) :=
  by
  have p0000 := @gSp (.imp (.objEq x y) ph) x
  have p0001 := @gEqus4 ph x y
  have p0002 := (Nominal.biimpRefl (synWsb y x ph))
  have p0003 :=
    @gSylanbrc (.all x (.imp (.objEq x y) ph)) (.imp (.objEq x y) ph)
      (synWex x (synWa (.objEq x y) ph)) (synWsb y x ph) p0000 p0001 p0002
  exact p0003

/-- Checked nominal proof certificate identified upstream as `g_stdpc4`. -/
@[expose]
noncomputable def gStdpc4 (ph : Wff) (x : Var) (y : Var) :
    Nominal.NPrf (.imp (.all x ph) (synWsb y x ph)) :=
  by
  have p0000 := Nominal.ax1 ph (.objEq x y)
  have p0001 := @gAlimi ph (.imp (.objEq x y) ph) x p0000
  have p0002 := @gSb2 ph x y
  have p0003 :=
    @gSyl (.all x ph) (.all x (.imp (.objEq x y) ph)) (synWsb y x ph) p0001 p0002
  exact p0003

/-- Checked nominal proof certificate identified upstream as `g_sbft`. -/
@[expose]
noncomputable def gSbft (ph : Wff) (x : Var) (y : Var) :
    Nominal.NPrf (.imp (synWnf x ph) (synWb (synWsb y x ph) ph)) :=
  by
  have p0000 := @gSb1 ph x y
  have p0001 := @gSimpr (.objEq x y) ph
  have p0002 := Nominal.gen p0001 x
  have p0003 := @gN1923t (synWa (.objEq x y) ph) ph x
  have p0004 :=
    @gMpbii (synWnf x ph) (.all x (.imp (synWa (.objEq x y) ph) ph))
      (.imp (synWex x (synWa (.objEq x y) ph)) ph) p0002 p0003
  have p0005 :=
    @gSyl5 (synWsb y x ph) (synWex x (synWa (.objEq x y) ph)) (synWnf x ph) ph p0000
      p0004
  have p0006 := @gNfr ph x
  have p0007 := @gStdpc4 ph x y
  have p0008 := @gSyl6 (synWnf x ph) ph (.all x ph) (synWsb y x ph) p0006 p0007
  have p0009 := @gImpbid (synWnf x ph) (synWsb y x ph) ph p0005 p0008
  exact p0009

/-- Checked nominal proof certificate identified upstream as `g_sbf`. -/
@[expose]
noncomputable def gSbf (ph : Wff) (x : Var) (y : Var)
    (hyp_sbf_1 : Nominal.NPrf (synWnf x ph)) :
    Nominal.NPrf (synWb (synWsb y x ph) ph) :=
  by
  have p0000 := @gSbft ph x y
  have p0001 := Nominal.mp hyp_sbf_1 p0000
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_equsb2`. -/
@[expose]
noncomputable def gEqusb2 (x : Var) (y : Var) :
    Nominal.NPrf (synWsb y x (.objEq y x)) :=
  by
  have p0000 := @gSb2 (.objEq y x) x y
  have p0001 := @gEqucomi x y
  have p0002 :=
    @gMpg (.imp (.objEq x y) (.objEq y x)) (synWsb y x (.objEq y x)) x p0000 p0001
  exact p0002

/-- Checked nominal proof certificate identified upstream as `g_sbied`. -/
@[expose]
noncomputable def gSbied (ph : Wff) (ps : Wff) (ch : Wff) (x : Var) (y : Var)
    (hyp_sbied_1 : Nominal.NPrf (synWnf x ph))
    (hyp_sbied_2 : Nominal.NPrf (.imp ph (synWnf x ch)))
    (hyp_sbied_3 : Nominal.NPrf (.imp ph (.imp (.objEq x y) (synWb ps ch)))) :
    Nominal.NPrf (.imp ph (synWb (synWsb y x ps) ch)) :=
  by
  have p0000 := @gSb1 ps x y
  have p0001 := @gBi1 ps ch
  have p0002 := @gSyl6 ph (.objEq x y) (synWb ps ch) (.imp ps ch) hyp_sbied_3 p0001
  have p0003 := @gImp3a ph (.objEq x y) ps ch p0002
  have p0004 := @gEximd ph (synWa (.objEq x y) ps) ch x hyp_sbied_1 p0003
  have p0005 :=
    @gSyl5 (synWsb y x ps) (synWex x (synWa (.objEq x y) ps)) ph (synWex x ch) p0000
      p0004
  have p0006 := @gN199d ch ph x hyp_sbied_2
  have p0007 := @gSyld ph (synWsb y x ps) (synWex x ch) ch p0005 p0006
  have p0008 := @gNfrd ph ch x hyp_sbied_2
  have p0009 := @gBi2 ps ch
  have p0010 := @gSyl6 ph (.objEq x y) (synWb ps ch) (.imp ch ps) hyp_sbied_3 p0009
  have p0011 := @gCom23 ph (.objEq x y) ch ps p0010
  have p0012 := @gAlimd ph ch (.imp (.objEq x y) ps) x hyp_sbied_1 p0011
  have p0013 := @gSb2 ps x y
  have p0014 :=
    @gSyl6 ph (.all x ch) (.all x (.imp (.objEq x y) ps)) (synWsb y x ps) p0012 p0013
  have p0015 := @gSyld ph ch (.all x ch) (synWsb y x ps) p0008 p0014
  have p0016 := @gImpbid ph (synWsb y x ps) ch p0007 p0015
  exact p0016

/-- Checked nominal proof certificate identified upstream as `g_sbie`. -/
@[expose]
noncomputable def gSbie (ph : Wff) (ps : Wff) (x : Var) (y : Var)
    (hyp_sbie_1 : Nominal.NPrf (synWnf x ps))
    (hyp_sbie_2 : Nominal.NPrf (.imp (.objEq x y) (synWb ph ps))) :
    Nominal.NPrf (synWb (synWsb y x ph) ps) :=
  by
  have p0000 := @gNftru x
  have p0001 := @gA1i (synWnf x ps) synWtru hyp_sbie_1
  have p0002 := @gA1i (.imp (.objEq x y) (synWb ph ps)) synWtru hyp_sbie_2
  have p0003 := @gSbied synWtru ph ps x y p0000 p0001 p0002
  have p0004 := @gTrud (synWb (synWsb y x ph) ps) p0003
  exact p0004

/-- Checked nominal proof certificate identified upstream as `g_hbsb2a`. -/
@[expose]
noncomputable def gHbsb2a (ph : Wff) (x : Var) (y : Var) :
    Nominal.NPrf (.imp (synWsb y x (.all y ph)) (.all x (synWsb y x ph))) :=
  by
  have p0000 := @gSb4a ph x y
  have p0001 := @gSb2 ph x y
  have p0002 := @gA5i (.imp (.objEq x y) ph) (synWsb y x ph) x p0001
  have p0003 :=
    @gSyl (synWsb y x (.all y ph)) (.all x (.imp (.objEq x y) ph))
      (.all x (synWsb y x ph)) p0000 p0002
  exact p0003

/-- Checked nominal proof certificate identified upstream as `g_hbsb3`. -/
@[expose]
noncomputable def gHbsb3 (ph : Wff) (x : Var) (y : Var)
    (hyp_hbsb3_1 : Nominal.NPrf (.imp ph (.all y ph))) :
    Nominal.NPrf (.imp (synWsb y x ph) (.all x (synWsb y x ph))) :=
  by
  have p0000 := @gSbimi ph (.all y ph) x y hyp_hbsb3_1
  have p0001 := @gHbsb2a ph x y
  have p0002 :=
    @gSyl (synWsb y x ph) (synWsb y x (.all y ph)) (.all x (synWsb y x ph)) p0000
      p0001
  exact p0002

/-- Checked nominal proof certificate identified upstream as `g_nfs1`. -/
@[expose]
noncomputable def gNfs1 (ph : Wff) (x : Var) (y : Var)
    (hyp_nfs1_1 : Nominal.NPrf (synWnf y ph)) :
    Nominal.NPrf (synWnf x (synWsb y x ph)) :=
  by
  have p0000 := @gNfri ph y hyp_nfs1_1
  have p0001 := @gHbsb3 ph x y p0000
  have p0002 := @gNfi (synWsb y x ph) x p0001
  exact p0002

/-- Checked nominal proof certificate identified upstream as `g_ax16`. -/
@[expose]
noncomputable def gAx16 (ph : Wff) (x : Var) (y : Var) (dv_x_y : x ≠ y) :
    Nominal.NPrf (.imp (.all x (.objEq x y)) (.imp ph (.all x ph))) :=
  by
  let proofSupport : Finset Var := ph.fv ∪ ({ x } : Finset Var) ∪ ({ y } : Finset Var)
  have p0000 :=
    @gA16g ph x y x
      (by
        first
        | (aesop))
  exact p0000

/-- Checked nominal proof certificate identified upstream as `g_a16nf`. -/
@[expose]
noncomputable def gA16nf (ph : Wff) (x : Var) (y : Var) (z : Var) (dv_x_y : x ≠ y) :
    Nominal.NPrf (.imp (.all x (.objEq x y)) (synWnf z ph)) :=
  by
  let proofSupport : Finset Var :=
    ph.fv ∪ ({ x } : Finset Var) ∪ ({ y } : Finset Var) ∪ ({ z } : Finset Var)
  have p0000 := @gNfae x y z
  have p0001 :=
    @gA16g ph x y z
      (by
        first
        | (aesop))
  have p0002 := @gNfd (.all x (.objEq x y)) ph z p0000 p0001
  exact p0002

/-- Checked nominal proof certificate identified upstream as `g_sb4`. -/
@[expose]
noncomputable def gSb4 (ph : Wff) (x : Var) (y : Var) :
    Nominal.NPrf
      (.imp (.neg (.all x (.objEq x y)))
        (.imp (synWsb y x ph) (.all x (.imp (.objEq x y) ph)))) :=
  by
  have p0000 := @gSb1 ph x y
  have p0001 := @gEqus5 ph x y
  have p0002 :=
    @gSyl5 (synWsb y x ph) (synWex x (synWa (.objEq x y) ph))
      (.neg (.all x (.objEq x y))) (.all x (.imp (.objEq x y) ph)) p0000 p0001
  exact p0002

/-- Checked nominal proof certificate identified upstream as `g_sb4b`. -/
@[expose]
noncomputable def gSb4b (ph : Wff) (x : Var) (y : Var) :
    Nominal.NPrf
      (.imp (.neg (.all x (.objEq x y)))
        (synWb (synWsb y x ph) (.all x (.imp (.objEq x y) ph)))) :=
  by
  have p0000 := @gSb4 ph x y
  have p0001 := @gSb2 ph x y
  have p0002 :=
    @gImpbid1 (.neg (.all x (.objEq x y))) (synWsb y x ph)
      (.all x (.imp (.objEq x y) ph)) p0000 p0001
  exact p0002

/-- Checked nominal proof certificate identified upstream as `g_hbsb2`. -/
@[expose]
noncomputable def gHbsb2 (ph : Wff) (x : Var) (y : Var) :
    Nominal.NPrf
      (.imp (.neg (.all x (.objEq x y))) (.imp (synWsb y x ph) (.all x (synWsb y x ph)))) :=
  by
  have p0000 := @gSb4 ph x y
  have p0001 := @gSb2 ph x y
  have p0002 := @gA5i (.imp (.objEq x y) ph) (synWsb y x ph) x p0001
  have p0003 :=
    @gSyl6 (.neg (.all x (.objEq x y))) (synWsb y x ph) (.all x (.imp (.objEq x y) ph))
      (.all x (synWsb y x ph)) p0000 p0002
  exact p0003

/-- Checked nominal proof certificate identified upstream as `g_nfsb2`. -/
@[expose]
noncomputable def gNfsb2 (ph : Wff) (x : Var) (y : Var) :
    Nominal.NPrf (.imp (.neg (.all x (.objEq x y))) (synWnf x (synWsb y x ph))) :=
  by
  have p0000 := @gNfnae x y x
  have p0001 := @gHbsb2 ph x y
  have p0002 := @gNfd (.neg (.all x (.objEq x y))) (synWsb y x ph) x p0000 p0001
  exact p0002

/-- Checked nominal proof certificate identified upstream as `g_sbequi`. -/
@[expose]
noncomputable def gSbequi (ph : Wff) (x : Var) (y : Var) (z : Var) :
    Nominal.NPrf (.imp (.objEq x y) (.imp (synWsb x z ph) (synWsb y z ph))) :=
  by
  have p0000 := @gHbsb2 ph z x
  have p0001 := @gEquvini x y z
  have p0002 := @gStdpc7 ph x z
  have p0003 := @gSbequ1 ph z y
  have p0004 :=
    @gSylan9 (.objEq x z) (synWsb x z ph) ph (.objEq z y) (synWsb y z ph) p0002 p0003
  have p0005 :=
    @gEximi (synWa (.objEq x z) (.objEq z y)) (.imp (synWsb x z ph) (synWsb y z ph)) z
      p0004
  have p0006 :=
    @gSyl (.objEq x y) (synWex z (synWa (.objEq x z) (.objEq z y)))
      (synWex z (.imp (synWsb x z ph) (synWsb y z ph))) p0001 p0005
  have p0007 := @gN1935 (synWsb x z ph) (synWsb y z ph) z
  have p0008 :=
    @gSylib (.objEq x y) (synWex z (.imp (synWsb x z ph) (synWsb y z ph)))
      (.imp (.all z (synWsb x z ph)) (synWex z (synWsb y z ph))) p0006 p0007
  have p0009 :=
    @gSylan9 (.neg (.all z (.objEq z x))) (synWsb x z ph) (.all z (synWsb x z ph))
      (.objEq x y) (synWex z (synWsb y z ph)) p0000 p0008
  have p0010 := @gNfsb2 ph z y
  have p0011 := @gN199d (synWsb y z ph) (.neg (.all z (.objEq z y))) z p0010
  have p0012 :=
    @gSyl9 (synWa (.neg (.all z (.objEq z x))) (.objEq x y)) (synWsb x z ph)
      (synWex z (synWsb y z ph)) (.neg (.all z (.objEq z y))) (synWsb y z ph) p0009
      p0011
  have p0013 :=
    @gEx (.neg (.all z (.objEq z x))) (.objEq x y)
      (.imp (.neg (.all z (.objEq z y))) (.imp (synWsb x z ph) (synWsb y z ph))) p0012
  have p0014 :=
    @gCom23 (.neg (.all z (.objEq z x))) (.objEq x y) (.neg (.all z (.objEq z y)))
      (.imp (synWsb x z ph) (synWsb y z ph)) p0013
  have p0015 := @gSbequ2 ph z x
  have p0016 := @gSps (.objEq z x) (.imp (synWsb x z ph) ph) z p0015
  have p0017 :=
    @gAdantr (.all z (.objEq z x)) (.imp (synWsb x z ph) ph) (.objEq x y) p0016
  have p0018 := @gSbequ1 ph x y
  have p0019 := @gDrsb1 ph z x y
  have p0020 := @gBiimprd (.all z (.objEq z x)) (synWsb y z ph) (synWsb y x ph) p0019
  have p0021 :=
    @gSylan9r (.objEq x y) ph (synWsb y x ph) (.all z (.objEq z x)) (synWsb y z ph)
      p0018 p0020
  have p0022 :=
    @gSyld (synWa (.all z (.objEq z x)) (.objEq x y)) (synWsb x z ph) ph
      (synWsb y z ph) p0017 p0021
  have p0023 :=
    @gEx (.all z (.objEq z x)) (.objEq x y) (.imp (synWsb x z ph) (synWsb y z ph))
      p0022
  have p0024 := @gDrsb1 ph z y x
  have p0025 := @gBiimpd (.all z (.objEq z y)) (synWsb x z ph) (synWsb x y ph) p0024
  have p0026 := @gStdpc7 ph x y
  have p0027 :=
    @gSylan9 (.all z (.objEq z y)) (synWsb x z ph) (synWsb x y ph) (.objEq x y) ph
      p0025 p0026
  have p0028 := @gSps (.objEq z y) (.imp ph (synWsb y z ph)) z p0003
  have p0029 :=
    @gAdantr (.all z (.objEq z y)) (.imp ph (synWsb y z ph)) (.objEq x y) p0028
  have p0030 :=
    @gSyld (synWa (.all z (.objEq z y)) (.objEq x y)) (synWsb x z ph) ph
      (synWsb y z ph) p0027 p0029
  have p0031 :=
    @gEx (.all z (.objEq z y)) (.objEq x y) (.imp (synWsb x z ph) (synWsb y z ph))
      p0030
  have p0032 :=
    @gPm261ii (.all z (.objEq z x)) (.all z (.objEq z y))
      (.imp (.objEq x y) (.imp (synWsb x z ph) (synWsb y z ph))) p0014 p0023 p0031
  exact p0032

/-- Checked nominal proof certificate identified upstream as `g_sbequ`. -/
@[expose]
noncomputable def gSbequ (ph : Wff) (x : Var) (y : Var) (z : Var) :
    Nominal.NPrf (.imp (.objEq x y) (synWb (synWsb x z ph) (synWsb y z ph))) :=
  by
  have p0000 := @gSbequi ph x y z
  have p0001 := @gSbequi ph y x z
  have p0002 := @gEqucoms (.imp (synWsb y z ph) (synWsb x z ph)) y x p0001
  have p0003 := @gImpbid (.objEq x y) (synWsb x z ph) (synWsb y z ph) p0000 p0002
  exact p0003

/-- Checked nominal proof certificate identified upstream as `g_sbn`. -/
@[expose]
noncomputable def gSbn (ph : Wff) (x : Var) (y : Var) :
    Nominal.NPrf (synWb (synWsb y x (.neg ph)) (.neg (synWsb y x ph))) :=
  by
  have p0000 := @gSbequ2 (.neg ph) x y
  have p0001 := @gSbequ2 ph x y
  have p0002 :=
    @gNsyld (.objEq x y) (synWsb y x (.neg ph)) ph (synWsb y x ph) p0000 p0001
  have p0003 :=
    @gSps (.objEq x y) (.imp (synWsb y x (.neg ph)) (.neg (synWsb y x ph))) x p0002
  have p0004 := @gSb4 (.neg ph) x y
  have p0005 := @gSb1 ph x y
  have p0006 := @gEqus3 ph x y
  have p0007 :=
    @gSylib (synWsb y x ph) (synWex x (synWa (.objEq x y) ph))
      (.neg (.all x (.imp (.objEq x y) (.neg ph)))) p0005 p0006
  have p0008 := @gCon2i (synWsb y x ph) (.all x (.imp (.objEq x y) (.neg ph))) p0007
  have p0009 :=
    @gSyl6 (.neg (.all x (.objEq x y))) (synWsb y x (.neg ph))
      (.all x (.imp (.objEq x y) (.neg ph))) (.neg (synWsb y x ph)) p0004 p0008
  have p0010 :=
    @gPm261i (.all x (.objEq x y))
      (.imp (synWsb y x (.neg ph)) (.neg (synWsb y x ph))) p0003 p0009
  have p0011 := @gSbequ1 ph x y
  have p0012 := @gCon3rr3 (.objEq x y) ph (synWsb y x ph) p0011
  have p0013 := @gSb2 (.neg (.neg ph)) x y
  have p0014 := @gNotnot ph
  have p0015 := @gSbbii ph (.neg (.neg ph)) x y p0014
  have p0016 :=
    @gSylibr (.all x (.imp (.objEq x y) (.neg (.neg ph)))) (synWsb y x (.neg (.neg ph)))
      (synWsb y x ph) p0013 p0015
  have p0017 :=
    @gCon3i (.all x (.imp (.objEq x y) (.neg (.neg ph)))) (synWsb y x ph) p0016
  have p0018 := @gEqus3 (.neg ph) x y
  have p0019 :=
    @gSylibr (.neg (synWsb y x ph)) (.neg (.all x (.imp (.objEq x y) (.neg (.neg ph)))))
      (synWex x (synWa (.objEq x y) (.neg ph))) p0017 p0018
  have p0020 := (Nominal.biimpRefl (synWsb y x (.neg ph)))
  have p0021 :=
    @gSylanbrc (.neg (synWsb y x ph)) (.imp (.objEq x y) (.neg ph))
      (synWex x (synWa (.objEq x y) (.neg ph))) (synWsb y x (.neg ph)) p0012 p0019
      p0020
  have p0022 := @gImpbii (synWsb y x (.neg ph)) (.neg (synWsb y x ph)) p0010 p0021
  exact p0022

/-- Checked nominal proof certificate identified upstream as `g_sbi1`. -/
@[expose]
noncomputable def gSbi1 (ph : Wff) (ps : Wff) (x : Var) (y : Var) :
    Nominal.NPrf
      (.imp (synWsb y x (.imp ph ps)) (.imp (synWsb y x ph) (synWsb y x ps))) :=
  by
  have p0000 := @gSbequ2 ph x y
  have p0001 := @gSbequ2 (.imp ph ps) x y
  have p0002 :=
    @gSyl5d (.objEq x y) (synWsb y x ph) ph (synWsb y x (.imp ph ps)) ps p0000 p0001
  have p0003 := @gSbequ1 ps x y
  have p0004 :=
    @gSyl6d (.objEq x y) (synWsb y x (.imp ph ps)) (synWsb y x ph) ps (synWsb y x ps)
      p0002 p0003
  have p0005 :=
    @gSps (.objEq x y)
      (.imp (synWsb y x (.imp ph ps)) (.imp (synWsb y x ph) (synWsb y x ps))) x p0004
  have p0006 := @gSb4 ph x y
  have p0007 := @gSb4 (.imp ph ps) x y
  have p0008 := Nominal.ax2 (.objEq x y) ph ps
  have p0009 :=
    @gAl2imi (.imp (.objEq x y) (.imp ph ps)) (.imp (.objEq x y) ph)
      (.imp (.objEq x y) ps) x p0008
  have p0010 := @gSb2 ps x y
  have p0011 :=
    @gSyl6 (.all x (.imp (.objEq x y) (.imp ph ps))) (.all x (.imp (.objEq x y) ph))
      (.all x (.imp (.objEq x y) ps)) (synWsb y x ps) p0009 p0010
  have p0012 :=
    @gSyl6 (.neg (.all x (.objEq x y))) (synWsb y x (.imp ph ps))
      (.all x (.imp (.objEq x y) (.imp ph ps)))
      (.imp (.all x (.imp (.objEq x y) ph)) (synWsb y x ps)) p0007 p0011
  have p0013 :=
    @gSyl5d (.neg (.all x (.objEq x y))) (synWsb y x ph) (.all x (.imp (.objEq x y) ph))
      (synWsb y x (.imp ph ps)) (synWsb y x ps) p0006 p0012
  have p0014 :=
    @gPm261i (.all x (.objEq x y))
      (.imp (synWsb y x (.imp ph ps)) (.imp (synWsb y x ph) (synWsb y x ps))) p0005
      p0013
  exact p0014

/-- Checked nominal proof certificate identified upstream as `g_sbi2`. -/
@[expose]
noncomputable def gSbi2 (ph : Wff) (ps : Wff) (x : Var) (y : Var) :
    Nominal.NPrf
      (.imp (.imp (synWsb y x ph) (synWsb y x ps)) (synWsb y x (.imp ph ps))) :=
  by
  have p0000 := @gSbn ph x y
  have p0001 := @gPm221 ph ps
  have p0002 := @gSbimi (.neg ph) (.imp ph ps) x y p0001
  have p0003 :=
    @gSylbir (.neg (synWsb y x ph)) (synWsb y x (.neg ph)) (synWsb y x (.imp ph ps))
      p0000 p0002
  have p0004 := Nominal.ax1 ps ph
  have p0005 := @gSbimi ps (.imp ph ps) x y p0004
  have p0006 :=
    @gJa (synWsb y x ph) (synWsb y x ps) (synWsb y x (.imp ph ps)) p0003 p0005
  exact p0006

/-- Checked nominal proof certificate identified upstream as `g_sbim`. -/
@[expose]
noncomputable def gSbim (ph : Wff) (ps : Wff) (x : Var) (y : Var) :
    Nominal.NPrf
      (synWb (synWsb y x (.imp ph ps)) (.imp (synWsb y x ph) (synWsb y x ps))) :=
  by
  have p0000 := @gSbi1 ph ps x y
  have p0001 := @gSbi2 ph ps x y
  have p0002 :=
    @gImpbii (synWsb y x (.imp ph ps)) (.imp (synWsb y x ph) (synWsb y x ps)) p0000
      p0001
  exact p0002

/-- Checked nominal proof certificate identified upstream as `g_sbor`. -/
@[expose]
noncomputable def gSbor (ph : Wff) (ps : Wff) (x : Var) (y : Var) :
    Nominal.NPrf
      (synWb (synWsb y x (synWo ph ps)) (synWo (synWsb y x ph) (synWsb y x ps))) :=
  by
  have p0000 := @gSbim (.neg ph) ps x y
  have p0001 := @gSbn ph x y
  have p0002 :=
    @gImbi1i (synWsb y x (.neg ph)) (.neg (synWsb y x ph)) (synWsb y x ps) p0001
  have p0003 :=
    @gBitri (synWsb y x (.imp (.neg ph) ps))
      (.imp (synWsb y x (.neg ph)) (synWsb y x ps))
      (.imp (.neg (synWsb y x ph)) (synWsb y x ps)) p0000 p0002
  have p0004 := (Nominal.biimpRefl (synWo ph ps))
  have p0005 := @gSbbii (synWo ph ps) (.imp (.neg ph) ps) x y p0004
  have p0006 := (Nominal.biimpRefl (synWo (synWsb y x ph) (synWsb y x ps)))
  have p0007 :=
    @gN3bitr4i (synWsb y x (.imp (.neg ph) ps))
      (.imp (.neg (synWsb y x ph)) (synWsb y x ps)) (synWsb y x (synWo ph ps))
      (synWo (synWsb y x ph) (synWsb y x ps)) p0003 p0005 p0006
  exact p0007

/-- Checked nominal proof certificate identified upstream as `g_sban`. -/
@[expose]
noncomputable def gSban (ph : Wff) (ps : Wff) (x : Var) (y : Var) :
    Nominal.NPrf
      (synWb (synWsb y x (synWa ph ps)) (synWa (synWsb y x ph) (synWsb y x ps))) :=
  by
  have p0000 := @gSbn (.imp ph (.neg ps)) x y
  have p0001 := @gSbim ph (.neg ps) x y
  have p0002 := @gSbn ps x y
  have p0003 :=
    @gImbi2i (synWsb y x (.neg ps)) (.neg (synWsb y x ps)) (synWsb y x ph) p0002
  have p0004 :=
    @gBitri (synWsb y x (.imp ph (.neg ps)))
      (.imp (synWsb y x ph) (synWsb y x (.neg ps)))
      (.imp (synWsb y x ph) (.neg (synWsb y x ps))) p0001 p0003
  have p0005 :=
    @gXchbinx (synWsb y x (.neg (.imp ph (.neg ps)))) (synWsb y x (.imp ph (.neg ps)))
      (.imp (synWsb y x ph) (.neg (synWsb y x ps))) p0000 p0004
  have p0006 := (Nominal.biimpRefl (synWa ph ps))
  have p0007 := @gSbbii (synWa ph ps) (.neg (.imp ph (.neg ps))) x y p0006
  have p0008 := (Nominal.biimpRefl (synWa (synWsb y x ph) (synWsb y x ps)))
  have p0009 :=
    @gN3bitr4i (synWsb y x (.neg (.imp ph (.neg ps))))
      (.neg (.imp (synWsb y x ph) (.neg (synWsb y x ps)))) (synWsb y x (synWa ph ps))
      (synWa (synWsb y x ph) (synWsb y x ps)) p0005 p0007 p0008
  exact p0009

/-- Checked nominal proof certificate identified upstream as `g_sbbi`. -/
@[expose]
noncomputable def gSbbi (ph : Wff) (ps : Wff) (x : Var) (y : Var) :
    Nominal.NPrf
      (synWb (synWsb y x (synWb ph ps)) (synWb (synWsb y x ph) (synWsb y x ps))) :=
  by
  have p0000 := @gDfbi2 ph ps
  have p0001 := @gSbbii (synWb ph ps) (synWa (.imp ph ps) (.imp ps ph)) x y p0000
  have p0002 := @gSbim ph ps x y
  have p0003 := @gSbim ps ph x y
  have p0004 :=
    @gAnbi12i (synWsb y x (.imp ph ps)) (.imp (synWsb y x ph) (synWsb y x ps))
      (synWsb y x (.imp ps ph)) (.imp (synWsb y x ps) (synWsb y x ph)) p0002 p0003
  have p0005 := @gSban (.imp ph ps) (.imp ps ph) x y
  have p0006 := @gDfbi2 (synWsb y x ph) (synWsb y x ps)
  have p0007 :=
    @gN3bitr4i (synWa (synWsb y x (.imp ph ps)) (synWsb y x (.imp ps ph)))
      (synWa (.imp (synWsb y x ph) (synWsb y x ps)) (.imp (synWsb y x ps) (synWsb y x ph)))
      (synWsb y x (synWa (.imp ph ps) (.imp ps ph)))
      (synWb (synWsb y x ph) (synWsb y x ps)) p0004 p0005 p0006
  have p0008 :=
    @gBitri (synWsb y x (synWb ph ps)) (synWsb y x (synWa (.imp ph ps) (.imp ps ph)))
      (synWb (synWsb y x ph) (synWsb y x ps)) p0001 p0007
  exact p0008

/-- Checked nominal proof certificate identified upstream as `g_sblbis`. -/
@[expose]
noncomputable def gSblbis (ph : Wff) (ps : Wff) (ch : Wff) (x : Var) (y : Var)
    (hyp_sblbis_1 : Nominal.NPrf (synWb (synWsb y x ph) ps)) :
    Nominal.NPrf (synWb (synWsb y x (synWb ch ph)) (synWb (synWsb y x ch) ps)) :=
  by
  have p0000 := @gSbbi ch ph x y
  have p0001 := @gBibi2i (synWsb y x ph) ps (synWsb y x ch) hyp_sblbis_1
  have p0002 :=
    @gBitri (synWsb y x (synWb ch ph)) (synWb (synWsb y x ch) (synWsb y x ph))
      (synWb (synWsb y x ch) ps) p0000 p0001
  exact p0002

/-- Checked nominal proof certificate identified upstream as `g_nfsb4t`. -/
@[expose]
noncomputable def gNfsb4t (ph : Wff) (x : Var) (y : Var) (z : Var) :
    Nominal.NPrf
      (.imp (.all x (synWnf z ph))
        (.imp (.neg (.all z (.objEq z y))) (synWnf z (synWsb y x ph)))) :=
  by
  have p0000 := @gSbequ12 ph x y
  have p0001 := @gSps (.objEq x y) (synWb ph (synWsb y x ph)) x p0000
  have p0002 := @gDrnf2 ph (synWsb y x ph) x y z p0001
  have p0003 :=
    @gBiimpcd (.all x (.objEq x y)) (synWnf z ph) (synWnf z (synWsb y x ph)) p0002
  have p0004 :=
    @gSps (synWnf z ph) (.imp (.all x (.objEq x y)) (synWnf z (synWsb y x ph))) x
      p0003
  have p0005 :=
    @gA1dd (.all x (synWnf z ph)) (.all x (.objEq x y)) (synWnf z (synWsb y x ph))
      (synWa (.neg (.all z (.objEq z x))) (.neg (.all z (.objEq z y)))) p0004
  have p0006 := @gNfa1 (synWnf z ph) x
  have p0007 := @gNfnae z x x
  have p0008 := @gNfnae z y x
  have p0009 :=
    @gNfan (.neg (.all z (.objEq z x))) (.neg (.all z (.objEq z y))) x p0007 p0008
  have p0010 :=
    @gNfan (.all x (synWnf z ph))
      (synWa (.neg (.all z (.objEq z x))) (.neg (.all z (.objEq z y)))) x p0006 p0009
  have p0011 := @gNfeqf x y z
  have p0012 :=
    @gAdantl (synWa (.neg (.all z (.objEq z x))) (.neg (.all z (.objEq z y))))
      (synWnf z (.objEq x y)) (.all x (synWnf z ph)) p0011
  have p0013 := @gSp (synWnf z ph) x
  have p0014 :=
    @gAdantr (.all x (synWnf z ph)) (synWnf z ph)
      (synWa (.neg (.all z (.objEq z x))) (.neg (.all z (.objEq z y)))) p0013
  have p0015 :=
    @gNfimd
      (synWa (.all x (synWnf z ph))
        (synWa (.neg (.all z (.objEq z x))) (.neg (.all z (.objEq z y)))))
      (.objEq x y) ph z p0012 p0014
  have p0016 :=
    @gNfald
      (synWa (.all x (synWnf z ph))
        (synWa (.neg (.all z (.objEq z x))) (.neg (.all z (.objEq z y)))))
      (.imp (.objEq x y) ph) z x p0010 p0015
  have p0017 :=
    @gEx (.all x (synWnf z ph))
      (synWa (.neg (.all z (.objEq z x))) (.neg (.all z (.objEq z y))))
      (synWnf z (.all x (.imp (.objEq x y) ph))) p0016
  have p0018 := @gNfnae x y z
  have p0019 := @gSb4b ph x y
  have p0020 :=
    @gNfbidf (.neg (.all x (.objEq x y))) (synWsb y x ph)
      (.all x (.imp (.objEq x y) ph)) z p0018 p0019
  have p0021 :=
    @gImbi2d (.neg (.all x (.objEq x y))) (synWnf z (synWsb y x ph))
      (synWnf z (.all x (.imp (.objEq x y) ph)))
      (synWa (.neg (.all z (.objEq z x))) (.neg (.all z (.objEq z y)))) p0020
  have p0022 :=
    @gSyl5ibrcom (.all x (synWnf z ph))
      (.imp (synWa (.neg (.all z (.objEq z x))) (.neg (.all z (.objEq z y))))
        (synWnf z (synWsb y x ph)))
      (.neg (.all x (.objEq x y)))
      (.imp (synWa (.neg (.all z (.objEq z x))) (.neg (.all z (.objEq z y))))
        (synWnf z (.all x (.imp (.objEq x y) ph))))
      p0017 p0021
  have p0023 :=
    @gPm261d (.all x (synWnf z ph)) (.all x (.objEq x y))
      (.imp (synWa (.neg (.all z (.objEq z x))) (.neg (.all z (.objEq z y))))
        (synWnf z (synWsb y x ph)))
      p0005 p0022
  have p0024 :=
    @gExp3a (.all x (synWnf z ph)) (.neg (.all z (.objEq z x)))
      (.neg (.all z (.objEq z y))) (synWnf z (synWsb y x ph)) p0023
  have p0025 := @gNfsb2 ph z y
  have p0026 := @gDrsb1 ph z x y
  have p0027 := @gDrnf2 (synWsb y z ph) (synWsb y x ph) z x z p0026
  have p0028 :=
    @gSyl5ib (.neg (.all z (.objEq z y))) (synWnf z (synWsb y z ph))
      (.all z (.objEq z x)) (synWnf z (synWsb y x ph)) p0025 p0027
  have p0029 :=
    @gPm261d2 (.all x (synWnf z ph)) (.all z (.objEq z x))
      (.imp (.neg (.all z (.objEq z y))) (synWnf z (synWsb y x ph))) p0024 p0028
  exact p0029

/-- Checked nominal proof certificate identified upstream as `g_nfsb4`. -/
@[expose]
noncomputable def gNfsb4 (ph : Wff) (x : Var) (y : Var) (z : Var)
    (hyp_nfsb4_1 : Nominal.NPrf (synWnf z ph)) :
    Nominal.NPrf (.imp (.neg (.all z (.objEq z y))) (synWnf z (synWsb y x ph))) :=
  by
  have p0000 := @gNfsb4t ph x y z
  have p0001 :=
    @gMpg (synWnf z ph) (.imp (.neg (.all z (.objEq z y))) (synWnf z (synWsb y x ph)))
      x p0000 hyp_nfsb4_1
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_dvelimdf`. -/
@[expose]
noncomputable def gDvelimdf (ph : Wff) (ps : Wff) (ch : Wff) (x : Var) (y : Var)
    (z : Var) (hyp_dvelimdf_1 : Nominal.NPrf (synWnf x ph))
    (hyp_dvelimdf_2 : Nominal.NPrf (synWnf z ph))
    (hyp_dvelimdf_3 : Nominal.NPrf (.imp ph (synWnf x ps)))
    (hyp_dvelimdf_4 : Nominal.NPrf (.imp ph (synWnf z ch)))
    (hyp_dvelimdf_5 : Nominal.NPrf (.imp ph (.imp (.objEq z y) (synWb ps ch)))) :
    Nominal.NPrf (.imp ph (.imp (.neg (.all x (.objEq x y))) (synWnf x ch))) :=
  by
  have p0000 := @gAlrimi ph (synWnf x ps) z hyp_dvelimdf_2 hyp_dvelimdf_3
  have p0001 := @gNfsb4t ps z y x
  have p0002 :=
    @gSyl ph (.all z (synWnf x ps))
      (.imp (.neg (.all x (.objEq x y))) (synWnf x (synWsb y z ps))) p0000 p0001
  have p0003 := @gImp ph (.neg (.all x (.objEq x y))) (synWnf x (synWsb y z ps)) p0002
  have p0004 := @gNfnae x y x
  have p0005 := @gNfan ph (.neg (.all x (.objEq x y))) x hyp_dvelimdf_1 p0004
  have p0006 := @gSbied ph ps ch z y hyp_dvelimdf_2 hyp_dvelimdf_4 hyp_dvelimdf_5
  have p0007 :=
    @gAdantr ph (synWb (synWsb y z ps) ch) (.neg (.all x (.objEq x y))) p0006
  have p0008 :=
    @gNfbidf (synWa ph (.neg (.all x (.objEq x y)))) (synWsb y z ps) ch x p0005 p0007
  have p0009 :=
    @gMpbid (synWa ph (.neg (.all x (.objEq x y)))) (synWnf x (synWsb y z ps))
      (synWnf x ch) p0003 p0008
  have p0010 := @gEx ph (.neg (.all x (.objEq x y))) (synWnf x ch) p0009
  exact p0010

/-- Checked nominal proof certificate identified upstream as `g_sbco`. -/
@[expose]
noncomputable def gSbco (ph : Wff) (x : Var) (y : Var) :
    Nominal.NPrf (synWb (synWsb y x (synWsb x y ph)) (synWsb y x ph)) :=
  by
  have p0000 := @gEqusb2 x y
  have p0001 := @gSbequ12 ph y x
  have p0002 := @gBicomd (.objEq y x) ph (synWsb x y ph) p0001
  have p0003 := @gSbimi (.objEq y x) (synWb (synWsb x y ph) ph) x y p0002
  have p0004 := Nominal.mp p0000 p0003
  have p0005 := @gSbbi (synWsb x y ph) ph x y
  have p0006 :=
    @gMpbi (synWsb y x (synWb (synWsb x y ph) ph))
      (synWb (synWsb y x (synWsb x y ph)) (synWsb y x ph)) p0004 p0005
  exact p0006

/-- Checked nominal proof certificate identified upstream as `g_sbid2`. -/
@[expose]
noncomputable def gSbid2 (ph : Wff) (x : Var) (y : Var)
    (hyp_sbid2_1 : Nominal.NPrf (synWnf x ph)) :
    Nominal.NPrf (synWb (synWsb y x (synWsb x y ph)) ph) :=
  by
  have p0000 := @gSbco ph x y
  have p0001 := @gSbf ph x y hyp_sbid2_1
  have p0002 := @gBitri (synWsb y x (synWsb x y ph)) (synWsb y x ph) ph p0000 p0001
  exact p0002

/-- Checked nominal proof certificate identified upstream as `g_sbco2`. -/
@[expose]
noncomputable def gSbco2 (ph : Wff) (x : Var) (y : Var) (z : Var)
    (hyp_sbco2_1 : Nominal.NPrf (synWnf z ph)) :
    Nominal.NPrf (synWb (synWsb y z (synWsb z x ph)) (synWsb y x ph)) :=
  by
  have p0000 := @gSbid2 ph z x hyp_sbco2_1
  have p0001 := @gSbequ (synWsb z x ph) x y z
  have p0002 :=
    @gSyl5bbr ph (synWsb x z (synWsb z x ph)) (.objEq x y)
      (synWsb y z (synWsb z x ph)) p0000 p0001
  have p0003 := @gSbequ12 ph x y
  have p0004 :=
    @gBitr3d (.objEq x y) ph (synWsb y z (synWsb z x ph)) (synWsb y x ph) p0002 p0003
  have p0005 :=
    @gSps (.objEq x y) (synWb (synWsb y z (synWsb z x ph)) (synWsb y x ph)) x p0004
  have p0006 := @gNfnae x y x
  have p0007 := @gNfs1 ph x z hyp_sbco2_1
  have p0008 := @gNfsb4 (synWsb z x ph) z y x p0007
  have p0009 :=
    @gA1i (.imp (.objEq x y) (synWb ph (synWsb y z (synWsb z x ph))))
      (.neg (.all x (.objEq x y))) p0002
  have p0010 :=
    @gSbied (.neg (.all x (.objEq x y))) ph (synWsb y z (synWsb z x ph)) x y p0006
      p0008 p0009
  have p0011 :=
    @gBicomd (.neg (.all x (.objEq x y))) (synWsb y x ph) (synWsb y z (synWsb z x ph))
      p0010
  have p0012 :=
    @gPm261i (.all x (.objEq x y))
      (synWb (synWsb y z (synWsb z x ph)) (synWsb y x ph)) p0005 p0011
  exact p0012

/-- Checked nominal proof certificate identified upstream as `g_sb6rf`. -/
@[expose]
noncomputable def gSb6rf (ph : Wff) (x : Var) (y : Var)
    (hyp_sb5rf_1 : Nominal.NPrf (synWnf y ph)) :
    Nominal.NPrf (synWb ph (.all y (.imp (.objEq y x) (synWsb y x ph)))) :=
  by
  have p0000 := @gSbequ1 ph x y
  have p0001 := @gEqucoms (.imp ph (synWsb y x ph)) x y p0000
  have p0002 := @gCom12 (.objEq y x) ph (synWsb y x ph) p0001
  have p0003 := @gAlrimi ph (.imp (.objEq y x) (synWsb y x ph)) y hyp_sb5rf_1 p0002
  have p0004 := @gSb2 (synWsb y x ph) y x
  have p0005 := @gSbid2 ph y x hyp_sb5rf_1
  have p0006 :=
    @gSylib (.all y (.imp (.objEq y x) (synWsb y x ph))) (synWsb x y (synWsb y x ph))
      ph p0004 p0005
  have p0007 := @gImpbii ph (.all y (.imp (.objEq y x) (synWsb y x ph))) p0003 p0006
  exact p0007

/-- Checked nominal proof certificate identified upstream as `g_sb8`. -/
@[expose]
noncomputable def gSb8 (ph : Wff) (x : Var) (y : Var)
    (hyp_sb5rf_1 : Nominal.NPrf (synWnf y ph)) :
    Nominal.NPrf (synWb (.all x ph) (.all y (synWsb y x ph))) :=
  by
  have p0000 := @gNfal ph y x hyp_sb5rf_1
  have p0001 := @gStdpc4 ph x y
  have p0002 := @gAlrimi (.all x ph) (synWsb y x ph) y p0000 p0001
  have p0003 := @gNfs1 ph x y hyp_sb5rf_1
  have p0004 := @gStdpc7 ph y x
  have p0005 := @gCbv3 (synWsb y x ph) ph y x p0003 hyp_sb5rf_1 p0004
  have p0006 := @gImpbii (.all x ph) (.all y (synWsb y x ph)) p0002 p0005
  exact p0006

/-- Checked nominal proof certificate identified upstream as `g_ax11v`. -/
@[expose]
noncomputable def gAx11v (ph : Wff) (x : Var) (y : Var) (dv_x_y : x ≠ y) :
    Nominal.NPrf (.imp (.objEq x y) (.imp ph (.all x (.imp (.objEq x y) ph)))) :=
  by
  let proofSupport : Finset Var := ph.fv ∪ ({ x } : Finset Var) ∪ ({ y } : Finset Var)
  have p0000 := Nominal.ax1 ph (.objEq x y)
  have p0001 :=
    @gAx16 (.imp (.objEq x y) ph) x y
      (by
        first
        | (aesop))
  have p0002 :=
    @gSyl5 ph (.imp (.objEq x y) ph) (.all x (.objEq x y))
      (.all x (.imp (.objEq x y) ph)) p0000 p0001
  have p0003 :=
    @gA1d (.all x (.objEq x y)) (.imp ph (.all x (.imp (.objEq x y) ph))) (.objEq x y)
      p0002
  have p0004 := @gAx11o ph x y
  have p0005 :=
    @gPm261i (.all x (.objEq x y))
      (.imp (.objEq x y) (.imp ph (.all x (.imp (.objEq x y) ph)))) p0003 p0004
  exact p0005

/-- Checked nominal proof certificate identified upstream as `g_sb56`. -/
@[expose]
noncomputable def gSb56 (ph : Wff) (x : Var) (y : Var) (dv_x_y : x ≠ y) :
    Nominal.NPrf
      (synWb (synWex x (synWa (.objEq x y) ph)) (.all x (.imp (.objEq x y) ph))) :=
  by
  let proofSupport : Finset Var := ph.fv ∪ ({ x } : Finset Var) ∪ ({ y } : Finset Var)
  have p0000 := @gNfa1 (.imp (.objEq x y) ph) x
  have p0001 :=
    @gAx11v ph x y
      (by
        first
        | (aesop))
  have p0002 := @gSp (.imp (.objEq x y) ph) x
  have p0003 := @gCom12 (.all x (.imp (.objEq x y) ph)) (.objEq x y) ph p0002
  have p0004 := @gImpbid (.objEq x y) ph (.all x (.imp (.objEq x y) ph)) p0001 p0003
  have p0005 := @gEqusex ph (.all x (.imp (.objEq x y) ph)) x y p0000 p0004
  exact p0005

/-- Checked nominal proof certificate identified upstream as `g_sb6`. -/
@[expose]
noncomputable def gSb6 (ph : Wff) (x : Var) (y : Var) (dv_x_y : x ≠ y) :
    Nominal.NPrf (synWb (synWsb y x ph) (.all x (.imp (.objEq x y) ph))) :=
  by
  let proofSupport : Finset Var := ph.fv ∪ ({ x } : Finset Var) ∪ ({ y } : Finset Var)
  have p0000 :=
    @gSb56 ph x y
      (by
        first
        | (aesop))
  have p0001 :=
    @gAnbi2i (synWex x (synWa (.objEq x y) ph)) (.all x (.imp (.objEq x y) ph))
      (.imp (.objEq x y) ph) p0000
  have p0002 := (Nominal.biimpRefl (synWsb y x ph))
  have p0003 := @gSp (.imp (.objEq x y) ph) x
  have p0004 := @gPm471ri (.all x (.imp (.objEq x y) ph)) (.imp (.objEq x y) ph) p0003
  have p0005 :=
    @gN3bitr4i (synWa (.imp (.objEq x y) ph) (synWex x (synWa (.objEq x y) ph)))
      (synWa (.imp (.objEq x y) ph) (.all x (.imp (.objEq x y) ph))) (synWsb y x ph)
      (.all x (.imp (.objEq x y) ph)) p0001 p0002 p0004
  exact p0005

/-- Checked nominal proof certificate identified upstream as `g_sb5`. -/
@[expose]
noncomputable def gSb5 (ph : Wff) (x : Var) (y : Var) (dv_x_y : x ≠ y) :
    Nominal.NPrf (synWb (synWsb y x ph) (synWex x (synWa (.objEq x y) ph))) :=
  by
  let proofSupport : Finset Var := ph.fv ∪ ({ x } : Finset Var) ∪ ({ y } : Finset Var)
  have p0000 :=
    @gSb6 ph x y
      (by
        first
        | (aesop))
  have p0001 :=
    @gSb56 ph x y
      (by
        first
        | (aesop))
  have p0002 :=
    @gBitr4i (synWsb y x ph) (.all x (.imp (.objEq x y) ph))
      (synWex x (synWa (.objEq x y) ph)) p0000 p0001
  exact p0002

/-- Checked nominal proof certificate identified upstream as `g_equsb3lem`. -/
@[expose]
noncomputable def gEqusb3lem (x : Var) (y : Var) (z : Var) (dv_x_y : x ≠ y)
    (dv_x_z : x ≠ z) : Nominal.NPrf (synWb (synWsb y x (.objEq x z)) (.objEq y z)) :=
  by
  let proofSupport : Finset Var :=
    ({ x } : Finset Var) ∪ ({ y } : Finset Var) ∪ ({ z } : Finset Var)
  have p0000 :=
    @gNfv (.objEq y z) x
      (by
        first
        |
          (simp (config :=
              {
                failIfUnchanged :=
                  false }) only [NFChoice.Compiler.CoreFVSimp.fv_wff_objEq] at ⊢;
            aesop))
  have p0001 := @gEquequ1 x y z
  have p0002 := @gSbie (.objEq x z) (.objEq y z) x y p0000 p0001
  exact p0002

/-- Checked nominal proof certificate identified upstream as `g_equsb3`. -/
@[expose]
noncomputable def gEqusb3 (x : Var) (y : Var) (z : Var) (dv_x_z : x ≠ z) :
    Nominal.NPrf (synWb (synWsb y x (.objEq x z)) (.objEq y z)) :=
  by
  let proofSupport : Finset Var :=
    ({ x } : Finset Var) ∪ ({ y } : Finset Var) ∪ ({ z } : Finset Var)
  let w : Var := freshVar proofSupport 0
  have fresh_w : w ∉ proofSupport :=
    by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_w_ne_x : w ≠ x := by
    intro h
    exact
      fresh_w
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_singleton.mpr h)))
  have fresh_x_ne_w : x ≠ w := Ne.symm fresh_w_ne_x
  have fresh_w_ne_y : w ≠ y := by
    intro h
    exact
      fresh_w
        (Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_singleton.mpr h)))
  have fresh_y_ne_w : y ≠ w := Ne.symm fresh_w_ne_y
  have fresh_w_ne_z : w ≠ z := by
    intro h
    exact fresh_w (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))
  have fresh_z_ne_w : z ≠ w := Ne.symm fresh_w_ne_z
  have p0000 :=
    @gEqusb3lem x w z
      (by
        first
        | (aesop))
      (by
        first
        | (aesop))
  have p0001 := @gSbbii (synWsb w x (.objEq x z)) (.objEq w z) w y p0000
  have p0002 :=
    @gNfv (.objEq x z) w
      (by
        first
        |
          (simp (config :=
              {
                failIfUnchanged :=
                  false }) only [NFChoice.Compiler.CoreFVSimp.fv_wff_objEq] at ⊢;
            aesop))
  have p0003 := @gSbco2 (.objEq x z) x y w p0002
  have p0004 :=
    @gEqusb3lem w y z
      (by
        first
        | (aesop))
      (by
        first
        | (aesop))
  have p0005 :=
    @gN3bitr3i (synWsb y w (synWsb w x (.objEq x z))) (synWsb y w (.objEq w z))
      (synWsb y x (.objEq x z)) (.objEq y z) p0001 p0003 p0004
  exact p0005

/-- Checked nominal proof certificate identified upstream as `g_hbs1`. -/
@[expose]
noncomputable def gHbs1 (ph : Wff) (x : Var) (y : Var) (dv_x_y : x ≠ y) :
    Nominal.NPrf (.imp (synWsb y x ph) (.all x (synWsb y x ph))) :=
  by
  let proofSupport : Finset Var := ph.fv ∪ ({ x } : Finset Var) ∪ ({ y } : Finset Var)
  have p0000 :=
    @gAx16 (synWsb y x ph) x y
      (by
        first
        | (aesop))
  have p0001 := @gHbsb2 ph x y
  have p0002 :=
    @gPm261i (.all x (.objEq x y)) (.imp (synWsb y x ph) (.all x (synWsb y x ph)))
      p0000 p0001
  exact p0002

/-- Checked nominal proof certificate identified upstream as `g_nfs1v`. -/
@[expose]
noncomputable def gNfs1v (ph : Wff) (x : Var) (y : Var) (dv_x_y : x ≠ y) :
    Nominal.NPrf (synWnf x (synWsb y x ph)) :=
  by
  let proofSupport : Finset Var := ph.fv ∪ ({ x } : Finset Var) ∪ ({ y } : Finset Var)
  have p0000 :=
    @gHbs1 ph x y
      (by
        first
        | (aesop))
  have p0001 := @gNfi (synWsb y x ph) x p0000
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_nfsb`. -/
@[expose]
noncomputable def gNfsb (ph : Wff) (x : Var) (y : Var) (z : Var) (dv_y_z : y ≠ z)
    (hyp_nfsb_1 : Nominal.NPrf (synWnf z ph)) :
    Nominal.NPrf (synWnf z (synWsb y x ph)) :=
  by
  let proofSupport : Finset Var :=
    ph.fv ∪ ({ x } : Finset Var) ∪ ({ y } : Finset Var) ∪ ({ z } : Finset Var)
  have p0000 :=
    @gA16nf (synWsb y x ph) z y z
      (by
        first
        | (aesop))
  have p0001 := @gNfsb4 ph x y z hyp_nfsb_1
  have p0002 := @gPm261i (.all z (.objEq z y)) (synWnf z (synWsb y x ph)) p0000 p0001
  exact p0002

/-- Checked nominal proof certificate identified upstream as `g_hbsb`. -/
@[expose]
noncomputable def gHbsb (ph : Wff) (x : Var) (y : Var) (z : Var) (dv_y_z : y ≠ z)
    (hyp_hbsb_1 : Nominal.NPrf (.imp ph (.all z ph))) :
    Nominal.NPrf (.imp (synWsb y x ph) (.all z (synWsb y x ph))) :=
  by
  let proofSupport : Finset Var :=
    ph.fv ∪ ({ x } : Finset Var) ∪ ({ y } : Finset Var) ∪ ({ z } : Finset Var)
  have p0000 := @gNfi ph z hyp_hbsb_1
  have p0001 :=
    @gNfsb ph x y z
      (by
        first
        | (aesop))
      p0000
  have p0002 := @gNfri (synWsb y x ph) z p0001
  exact p0002

/-- Checked nominal proof certificate identified upstream as `g_nfsbd`. -/
@[expose]
noncomputable def gNfsbd (ph : Wff) (ps : Wff) (x : Var) (y : Var) (z : Var)
    (dv_y_z : y ≠ z) (hyp_nfsbd_1 : Nominal.NPrf (synWnf x ph))
    (hyp_nfsbd_2 : Nominal.NPrf (.imp ph (synWnf z ps))) :
    Nominal.NPrf (.imp ph (synWnf z (synWsb y x ps))) :=
  by
  let proofSupport : Finset Var :=
    ph.fv ∪ ps.fv ∪ ({ x } : Finset Var) ∪ ({ y } : Finset Var) ∪ ({ z } : Finset Var)
  have p0000 := @gAlrimi ph (synWnf z ps) x hyp_nfsbd_1 hyp_nfsbd_2
  have p0001 := @gNfsb4t ps x y z
  have p0002 :=
    @gSyl ph (.all x (synWnf z ps))
      (.imp (.neg (.all z (.objEq z y))) (synWnf z (synWsb y x ps))) p0000 p0001
  have p0003 :=
    @gA16nf (synWsb y x ps) z y z
      (by
        first
        | (aesop))
  have p0004 :=
    @gPm261d2 ph (.all z (.objEq z y)) (synWnf z (synWsb y x ps)) p0002 p0003
  exact p0004

/-- Checked nominal proof certificate identified upstream as `g_euf`. -/
@[expose]
noncomputable def gEuf (ph : Wff) (x : Var) (y : Var) (dv_x_y : x ≠ y)
    (hyp_euf_1 : Nominal.NPrf (synWnf y ph)) :
    Nominal.NPrf
      (synWb (synWeu x ph) (synWex y (.all x (synWb ph (.classEq (.cv x) (.cv y)))))) :=
  by
  let proofSupport : Finset Var := ph.fv ∪ ({ x } : Finset Var) ∪ ({ y } : Finset Var)
  let z : Var := freshVar proofSupport 0
  have fresh_z : z ∉ proofSupport :=
    by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_z_not_ph : z ∉ ph.fv := by
    intro h
    exact fresh_z (Finset.mem_union_left _ (Finset.mem_union_left _ (h)))
  have fresh_z_ne_x : z ≠ x := by
    intro h
    exact
      fresh_z
        (Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_singleton.mpr h)))
  have fresh_x_ne_z : x ≠ z := Ne.symm fresh_z_ne_x
  have fresh_z_ne_y : z ≠ y := by
    intro h
    exact fresh_z (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))
  have fresh_y_ne_z : y ≠ z := Ne.symm fresh_z_ne_y
  have p0000 :=
    Nominal.dfEu x z ph
      (by
        first
        | (aesop))
      (by
        first
        | (aesop))
  have p0001 :=
    @gNfv (.classEq (.cv x) (.cv z)) y
      (by
        first
        |
          (simp (config :=
              {
                failIfUnchanged :=
                  false }) only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
              NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
              Finset.mem_singleton] at ⊢;
            aesop))
  have p0002 := @gNfbi ph (.classEq (.cv x) (.cv z)) y hyp_euf_1 p0001
  have p0003 := @gNfal (synWb ph (.classEq (.cv x) (.cv z))) y x p0002
  have p0004 :=
    @gNfv ph z
      (by
        first
        | (aesop))
  have p0005 :=
    @gNfv (.classEq (.cv x) (.cv y)) z
      (by
        first
        |
          (simp (config :=
              {
                failIfUnchanged :=
                  false }) only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
              NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
              Finset.mem_singleton] at ⊢;
            aesop))
  have p0006 := @gNfbi ph (.classEq (.cv x) (.cv y)) z p0004 p0005
  have p0007 := @gNfal (synWb ph (.classEq (.cv x) (.cv y))) z x p0006
  have p0008 := @gEquequ2 z y x
  have p0009_e00_recanon :
    Nominal.NPrf
      (.imp (.classEq (.cv z) (.cv y))
        (synWb (.classEq (.cv x) (.cv z)) (.classEq (.cv x) (.cv y)))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold synWb
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · exact Nominal.RecanonTransportDev.TRecanonWff.objEq_classEq _ _
        · apply Nominal.RecanonTransportDev.TRecanonWff.neg
          apply Nominal.RecanonTransportDev.TRecanonWff.imp
          · apply Nominal.RecanonTransportDev.TRecanonWff.imp
            · exact Nominal.RecanonTransportDev.TRecanonWff.objEq_classEq _ _
            · exact Nominal.RecanonTransportDev.TRecanonWff.objEq_classEq _ _
          · apply Nominal.RecanonTransportDev.TRecanonWff.neg
            apply Nominal.RecanonTransportDev.TRecanonWff.imp
            · exact Nominal.RecanonTransportDev.TRecanonWff.objEq_classEq _ _
            · exact Nominal.RecanonTransportDev.TRecanonWff.objEq_classEq _ _)
      p0008
  have p0009 :=
    @gBibi2d (.classEq (.cv z) (.cv y)) (.classEq (.cv x) (.cv z))
      (.classEq (.cv x) (.cv y)) ph p0009_e00_recanon
  have p0010 :=
    @gAlbidv (.classEq (.cv z) (.cv y)) (synWb ph (.classEq (.cv x) (.cv z)))
      (synWb ph (.classEq (.cv x) (.cv y))) x
      (by
        first
        |
          (simp (config :=
              {
                failIfUnchanged :=
                  false }) only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
              NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
              Finset.mem_singleton] at ⊢;
            aesop))
      p0009
  have p0011_e02_recanon :
    Nominal.NPrf
      (.imp (.objEq z y) (synWb (.all x (synWb ph (.classEq (.cv x) (.cv z))))
          (.all x (synWb ph (.classEq (.cv x) (.cv y)))))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold synWb
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
        · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0010
  have p0011 :=
    @gCbvex (.all x (synWb ph (.classEq (.cv x) (.cv z))))
      (.all x (synWb ph (.classEq (.cv x) (.cv y)))) z y p0003 p0007 p0011_e02_recanon
  have p0012_e00_recanon :
    Nominal.NPrf
      (synWb (synWeu x ph) (synWex z (.all x (synWb ph (.classEq (.cv x) (.cv z)))))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold synWb synWeu synWex
        simp (config := { failIfUnchanged := false }) only []
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
      p0000
  have p0012 :=
    @gBitri (synWeu x ph) (synWex z (.all x (synWb ph (.classEq (.cv x) (.cv z)))))
      (synWex y (.all x (synWb ph (.classEq (.cv x) (.cv y))))) p0012_e00_recanon p0011
  exact p0012

/-- Checked nominal proof certificate identified upstream as `g_eubid`. -/
@[expose]
noncomputable def gEubid (ph : Wff) (ps : Wff) (ch : Wff) (x : Var)
    (hyp_eubid_1 : Nominal.NPrf (synWnf x ph))
    (hyp_eubid_2 : Nominal.NPrf (.imp ph (synWb ps ch))) :
    Nominal.NPrf (.imp ph (synWb (synWeu x ps) (synWeu x ch))) :=
  by
  let proofSupport : Finset Var := ph.fv ∪ ps.fv ∪ ch.fv ∪ ({ x } : Finset Var)
  let y : Var := freshVar proofSupport 0
  have fresh_y : y ∉ proofSupport :=
    by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_y_not_ph : y ∉ ph.fv := by
    intro h
    exact
      fresh_y
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (h))))
  have fresh_y_not_ps : y ∉ ps.fv := by
    intro h
    exact
      fresh_y
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))
  have fresh_y_not_ch : y ∉ ch.fv := by
    intro h
    exact fresh_y (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_y_ne_x : y ≠ x := by
    intro h
    exact fresh_y (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))
  have fresh_x_ne_y : x ≠ y := Ne.symm fresh_y_ne_x
  have p0000 := @gBibi1d ph ps ch (.classEq (.cv x) (.cv y)) hyp_eubid_2
  have p0001 :=
    @gAlbid ph (synWb ps (.classEq (.cv x) (.cv y)))
      (synWb ch (.classEq (.cv x) (.cv y))) x hyp_eubid_1 p0000
  have p0002 :=
    @gExbidv ph (.all x (synWb ps (.classEq (.cv x) (.cv y))))
      (.all x (synWb ch (.classEq (.cv x) (.cv y)))) y
      (by
        first
        | (aesop))
      p0001
  have p0003 :=
    Nominal.dfEu x y ps
      (by
        first
        | (aesop))
      (by
        first
        | (aesop))
  have p0004 :=
    Nominal.dfEu x y ch
      (by
        first
        | (aesop))
      (by
        first
        | (aesop))
  have p0005_e01_recanon :
    Nominal.NPrf
      (synWb (synWeu x ps) (synWex y (.all x (synWb ps (.classEq (.cv x) (.cv y)))))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold synWb synWeu synWex
        simp (config := { failIfUnchanged := false }) only []
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
      p0003
  have p0005_e02_recanon :
    Nominal.NPrf
      (synWb (synWeu x ch) (synWex y (.all x (synWb ch (.classEq (.cv x) (.cv y)))))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold synWb synWeu synWex
        simp (config := { failIfUnchanged := false }) only []
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
      p0004
  have p0005 :=
    @gN3bitr4g ph (synWex y (.all x (synWb ps (.classEq (.cv x) (.cv y)))))
      (synWex y (.all x (synWb ch (.classEq (.cv x) (.cv y))))) (synWeu x ps)
      (synWeu x ch) p0002 p0005_e01_recanon p0005_e02_recanon
  exact p0005

/-- Checked nominal proof certificate identified upstream as `g_eubidv`. -/
@[expose]
noncomputable def gEubidv (ph : Wff) (ps : Wff) (ch : Wff) (x : Var)
    (dv_ph_x : x ∉ ph.fv) (hyp_eubidv_1 : Nominal.NPrf (.imp ph (synWb ps ch))) :
    Nominal.NPrf (.imp ph (synWb (synWeu x ps) (synWeu x ch))) :=
  by
  let proofSupport : Finset Var := ph.fv ∪ ps.fv ∪ ch.fv ∪ ({ x } : Finset Var)
  have p0000 :=
    @gNfv ph x
      (by
        first
        | (aesop))
  have p0001 := @gEubid ph ps ch x p0000 hyp_eubidv_1
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_eubii`. -/
@[expose]
noncomputable def gEubii (ph : Wff) (ps : Wff) (x : Var)
    (hyp_eubii_1 : Nominal.NPrf (synWb ph ps)) :
    Nominal.NPrf (synWb (synWeu x ph) (synWeu x ps)) :=
  by
  let proofSupport : Finset Var := ph.fv ∪ ps.fv ∪ ({ x } : Finset Var)
  have p0000 := @gA1i (synWb ph ps) synWtru hyp_eubii_1
  have p0001 :=
    @gEubidv synWtru ph ps x
      (by
        first
        |
          (simp (config :=
              {
                failIfUnchanged :=
                  false }) only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wtru] at ⊢;
            aesop))
      p0000
  have p0002 := @gTrud (synWb (synWeu x ph) (synWeu x ps)) p0001
  exact p0002

/-- Checked nominal proof certificate identified upstream as `g_nfeu1`. -/
@[expose]
noncomputable def gNfeu1 (ph : Wff) (x : Var) :
    Nominal.NPrf (synWnf x (synWeu x ph)) :=
  by
  let proofSupport : Finset Var := ph.fv ∪ ({ x } : Finset Var)
  let y : Var := freshVar proofSupport 0
  have fresh_y : y ∉ proofSupport :=
    by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_y_not_ph : y ∉ ph.fv := by
    intro h
    exact fresh_y (Finset.mem_union_left _ (h))
  have fresh_y_ne_x : y ≠ x := by
    intro h
    exact fresh_y (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))
  have fresh_x_ne_y : x ≠ y := Ne.symm fresh_y_ne_x
  have p0000 :=
    Nominal.dfEu x y ph
      (by
        first
        | (aesop))
      (by
        first
        | (aesop))
  have p0001 := @gNfa1 (synWb ph (.classEq (.cv x) (.cv y))) x
  have p0002 := @gNfex (.all x (synWb ph (.classEq (.cv x) (.cv y)))) x y p0001
  have p0003_e00_recanon :
    Nominal.NPrf
      (synWb (synWeu x ph) (synWex y (.all x (synWb ph (.classEq (.cv x) (.cv y)))))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold synWb synWeu synWex
        simp (config := { failIfUnchanged := false }) only []
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
      p0000
  have p0003 :=
    @gNfxfr (synWeu x ph) (synWex y (.all x (synWb ph (.classEq (.cv x) (.cv y))))) x
      p0003_e00_recanon p0002
  exact p0003

/-- Checked nominal proof certificate identified upstream as `g_nfmo1`. -/
@[expose]
noncomputable def gNfmo1 (ph : Wff) (x : Var) :
    Nominal.NPrf (synWnf x (synWmo x ph)) :=
  by
  have p0000 := (Nominal.biimpRefl (synWmo x ph))
  have p0001 := @gNfe1 ph x
  have p0002 := @gNfeu1 ph x
  have p0003 := @gNfim (synWex x ph) (synWeu x ph) x p0001 p0002
  have p0004 := @gNfxfr (synWmo x ph) (.imp (synWex x ph) (synWeu x ph)) x p0000 p0003
  exact p0004

/-- Checked nominal proof certificate identified upstream as `g_nfeud2`. -/
@[expose]
noncomputable def gNfeud2 (ph : Wff) (ps : Wff) (x : Var) (y : Var)
    (hyp_nfeud2_1 : Nominal.NPrf (synWnf y ph))
    (hyp_nfeud2_2 :
      Nominal.NPrf (.imp (synWa ph (.neg (.all x (.objEq x y)))) (synWnf x ps))) :
    Nominal.NPrf (.imp ph (synWnf x (synWeu y ps))) :=
  by
  let proofSupport : Finset Var :=
    ph.fv ∪ ps.fv ∪ ({ x } : Finset Var) ∪ ({ y } : Finset Var)
  let z : Var := freshVar proofSupport 0
  have fresh_z : z ∉ proofSupport :=
    by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_z_not_ph : z ∉ ph.fv := by
    intro h
    exact
      fresh_z
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (h))))
  have fresh_z_not_ps : z ∉ ps.fv := by
    intro h
    exact
      fresh_z
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))
  have fresh_z_ne_x : z ≠ x := by
    intro h
    exact
      fresh_z
        (Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_singleton.mpr h)))
  have fresh_x_ne_z : x ≠ z := Ne.symm fresh_z_ne_x
  have fresh_z_ne_y : z ≠ y := by
    intro h
    exact fresh_z (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))
  have fresh_y_ne_z : y ≠ z := Ne.symm fresh_z_ne_y
  have p0000 :=
    Nominal.dfEu y z ps
      (by
        first
        | (aesop))
      (by
        first
        | (aesop))
  have p0001 :=
    @gNfv ph z
      (by
        first
        | (aesop))
  have p0002 := @gNfnae x z y
  have p0003_e01_recanon :
    Nominal.NPrf (synWnf y (.neg (.all x (.classEq (.cv x) (.cv z))))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold synWnf
        apply Nominal.RecanonTransportDev.TRecanonWff.all
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · apply Nominal.RecanonTransportDev.TRecanonWff.neg
          apply Nominal.RecanonTransportDev.TRecanonWff.all
          exact Nominal.RecanonTransportDev.TRecanonWff.objEq_classEq _ _
        · apply Nominal.RecanonTransportDev.TRecanonWff.all
          apply Nominal.RecanonTransportDev.TRecanonWff.neg
          apply Nominal.RecanonTransportDev.TRecanonWff.all
          exact Nominal.RecanonTransportDev.TRecanonWff.objEq_classEq _ _)
      p0002
  have p0003 :=
    @gNfan ph (.neg (.all x (.classEq (.cv x) (.cv z)))) y hyp_nfeud2_1 p0003_e01_recanon
  have p0004_e00_recanon :
    Nominal.NPrf
      (.imp (synWa ph (.neg (.all x (.classEq (.cv x) (.cv y))))) (synWnf x ps)) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold synWa synWnf
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · apply Nominal.RecanonTransportDev.TRecanonWff.neg
          apply Nominal.RecanonTransportDev.TRecanonWff.imp
          · exact Nominal.RecanonTransportDev.TRecanonWff.same _
          · apply Nominal.RecanonTransportDev.TRecanonWff.neg
            apply Nominal.RecanonTransportDev.TRecanonWff.neg
            apply Nominal.RecanonTransportDev.TRecanonWff.all
            exact Nominal.RecanonTransportDev.TRecanonWff.objEq_classEq _ _
        · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      hyp_nfeud2_2
  have p0004 :=
    @gAdantlr ph (.neg (.all x (.classEq (.cv x) (.cv y)))) (synWnf x ps)
      (.neg (.all x (.classEq (.cv x) (.cv z)))) p0004_e00_recanon
  have p0005 := @gNfeqf y z x
  have p0006_e00_recanon :
    Nominal.NPrf
      (.imp (synWa (.neg (.all x (.classEq (.cv x) (.cv y))))
          (.neg (.all x (.classEq (.cv x) (.cv z))))) (synWnf x (.classEq (.cv y) (.cv z)))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold synWa synWnf
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · apply Nominal.RecanonTransportDev.TRecanonWff.neg
          apply Nominal.RecanonTransportDev.TRecanonWff.imp
          · apply Nominal.RecanonTransportDev.TRecanonWff.neg
            apply Nominal.RecanonTransportDev.TRecanonWff.all
            exact Nominal.RecanonTransportDev.TRecanonWff.objEq_classEq _ _
          · apply Nominal.RecanonTransportDev.TRecanonWff.neg
            apply Nominal.RecanonTransportDev.TRecanonWff.neg
            apply Nominal.RecanonTransportDev.TRecanonWff.all
            exact Nominal.RecanonTransportDev.TRecanonWff.objEq_classEq _ _
        · apply Nominal.RecanonTransportDev.TRecanonWff.all
          apply Nominal.RecanonTransportDev.TRecanonWff.imp
          · exact Nominal.RecanonTransportDev.TRecanonWff.objEq_classEq _ _
          · apply Nominal.RecanonTransportDev.TRecanonWff.all
            exact Nominal.RecanonTransportDev.TRecanonWff.objEq_classEq _ _)
      p0005
  have p0006 :=
    @gAncoms (.neg (.all x (.classEq (.cv x) (.cv y))))
      (.neg (.all x (.classEq (.cv x) (.cv z)))) (synWnf x (.classEq (.cv y) (.cv z)))
      p0006_e00_recanon
  have p0007 :=
    @gAdantll (.neg (.all x (.classEq (.cv x) (.cv z))))
      (.neg (.all x (.classEq (.cv x) (.cv y)))) (synWnf x (.classEq (.cv y) (.cv z))) ph
      p0006
  have p0008 :=
    @gNfbid
      (synWa (synWa ph (.neg (.all x (.classEq (.cv x) (.cv z)))))
        (.neg (.all x (.classEq (.cv x) (.cv y)))))
      ps (.classEq (.cv y) (.cv z)) x p0004 p0007
  have p0009_e01_recanon :
    Nominal.NPrf
      (.imp (synWa (synWa ph (.neg (.all x (.classEq (.cv x) (.cv z)))))
          (.neg (.all x (.objEq x y)))) (synWnf x (synWb ps (.classEq (.cv y) (.cv z))))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold synWa synWnf synWb
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · apply Nominal.RecanonTransportDev.TRecanonWff.neg
          apply Nominal.RecanonTransportDev.TRecanonWff.imp
          · exact Nominal.RecanonTransportDev.TRecanonWff.same _
          · apply Nominal.RecanonTransportDev.TRecanonWff.neg
            apply Nominal.RecanonTransportDev.TRecanonWff.neg
            apply Nominal.RecanonTransportDev.TRecanonWff.all
            exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
        · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0008
  have p0009 :=
    @gNfald2 (synWa ph (.neg (.all x (.classEq (.cv x) (.cv z)))))
      (synWb ps (.classEq (.cv y) (.cv z))) x y p0003 p0009_e01_recanon
  have p0010_e01_recanon :
    Nominal.NPrf
      (.imp (synWa ph (.neg (.all x (.objEq x z))))
        (synWnf x (.all y (synWb ps (.classEq (.cv y) (.cv z)))))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold synWa synWnf synWb
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · apply Nominal.RecanonTransportDev.TRecanonWff.neg
          apply Nominal.RecanonTransportDev.TRecanonWff.imp
          · exact Nominal.RecanonTransportDev.TRecanonWff.same _
          · apply Nominal.RecanonTransportDev.TRecanonWff.neg
            apply Nominal.RecanonTransportDev.TRecanonWff.neg
            apply Nominal.RecanonTransportDev.TRecanonWff.all
            exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
        · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0009
  have p0010 :=
    @gNfexd2 ph (.all y (synWb ps (.classEq (.cv y) (.cv z)))) x z p0001
      p0010_e01_recanon
  have p0011_e00_recanon :
    Nominal.NPrf
      (synWb (synWeu y ps) (synWex z (.all y (synWb ps (.classEq (.cv y) (.cv z)))))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold synWb synWeu synWex
        simp (config := { failIfUnchanged := false }) only []
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
      p0000
  have p0011 :=
    @gNfxfrd (synWeu y ps) (synWex z (.all y (synWb ps (.classEq (.cv y) (.cv z)))))
      ph x p0011_e00_recanon p0010
  exact p0011

/-- Checked nominal proof certificate identified upstream as `g_nfmod2`. -/
@[expose]
noncomputable def gNfmod2 (ph : Wff) (ps : Wff) (x : Var) (y : Var)
    (hyp_nfeud2_1 : Nominal.NPrf (synWnf y ph))
    (hyp_nfeud2_2 :
      Nominal.NPrf (.imp (synWa ph (.neg (.all x (.objEq x y)))) (synWnf x ps))) :
    Nominal.NPrf (.imp ph (synWnf x (synWmo y ps))) :=
  by
  have p0000 := (Nominal.biimpRefl (synWmo y ps))
  have p0001 := @gNfexd2 ph ps x y hyp_nfeud2_1 hyp_nfeud2_2
  have p0002 := @gNfeud2 ph ps x y hyp_nfeud2_1 hyp_nfeud2_2
  have p0003 := @gNfimd ph (synWex y ps) (synWeu y ps) x p0001 p0002
  have p0004 :=
    @gNfxfrd (synWmo y ps) (.imp (synWex y ps) (synWeu y ps)) ph x p0000 p0003
  exact p0004

/-- Checked nominal proof certificate identified upstream as `g_nfmod`. -/
@[expose]
noncomputable def gNfmod (ph : Wff) (ps : Wff) (x : Var) (y : Var)
    (hyp_nfeud_1 : Nominal.NPrf (synWnf y ph))
    (hyp_nfeud_2 : Nominal.NPrf (.imp ph (synWnf x ps))) :
    Nominal.NPrf (.imp ph (synWnf x (synWmo y ps))) :=
  by
  have p0000 :=
    @gAdantr ph (synWnf x ps) (.neg (.all x (.classEq (.cv x) (.cv y)))) hyp_nfeud_2
  have p0001_e01_recanon :
    Nominal.NPrf (.imp (synWa ph (.neg (.all x (.objEq x y)))) (synWnf x ps)) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold synWa synWnf
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · apply Nominal.RecanonTransportDev.TRecanonWff.neg
          apply Nominal.RecanonTransportDev.TRecanonWff.imp
          · exact Nominal.RecanonTransportDev.TRecanonWff.same _
          · apply Nominal.RecanonTransportDev.TRecanonWff.neg
            apply Nominal.RecanonTransportDev.TRecanonWff.neg
            apply Nominal.RecanonTransportDev.TRecanonWff.all
            exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
        · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0000
  have p0001 := @gNfmod2 ph ps x y hyp_nfeud_1 p0001_e01_recanon
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_nfmo`. -/
@[expose]
noncomputable def gNfmo (ph : Wff) (x : Var) (y : Var)
    (hyp_nfeu_1 : Nominal.NPrf (synWnf x ph)) :
    Nominal.NPrf (synWnf x (synWmo y ph)) :=
  by
  have p0000 := @gNftru y
  have p0001 := @gA1i (synWnf x ph) synWtru hyp_nfeu_1
  have p0002 := @gNfmod synWtru ph x y p0000 p0001
  have p0003 := @gTrud (synWnf x (synWmo y ph)) p0002
  exact p0003

/-- Checked nominal proof certificate identified upstream as `g_sb8eu`. -/
@[expose]
noncomputable def gSb8eu (ph : Wff) (x : Var) (y : Var)
    (hyp_sb8eu_1 : Nominal.NPrf (synWnf y ph)) :
    Nominal.NPrf (synWb (synWeu x ph) (synWeu y (synWsb y x ph))) :=
  by
  let proofSupport : Finset Var := ph.fv ∪ ({ x } : Finset Var) ∪ ({ y } : Finset Var)
  let z : Var := freshVar proofSupport 0
  let w : Var := freshVar proofSupport 1
  have fresh_z : z ∉ proofSupport :=
    by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_z_not_ph : z ∉ ph.fv := by
    intro h
    exact fresh_z (Finset.mem_union_left _ (Finset.mem_union_left _ (h)))
  have fresh_z_ne_x : z ≠ x := by
    intro h
    exact
      fresh_z
        (Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_singleton.mpr h)))
  have fresh_x_ne_z : x ≠ z := Ne.symm fresh_z_ne_x
  have fresh_z_ne_y : z ≠ y := by
    intro h
    exact fresh_z (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))
  have fresh_y_ne_z : y ≠ z := Ne.symm fresh_z_ne_y
  have fresh_w : w ∉ proofSupport :=
    by
    change freshVar proofSupport 1 ∉ proofSupport
    exact freshVar_not_mem proofSupport 1
  have fresh_w_not_ph : w ∉ ph.fv := by
    intro h
    exact fresh_w (Finset.mem_union_left _ (Finset.mem_union_left _ (h)))
  have fresh_w_ne_x : w ≠ x := by
    intro h
    exact
      fresh_w
        (Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_singleton.mpr h)))
  have fresh_x_ne_w : x ≠ w := Ne.symm fresh_w_ne_x
  have fresh_w_ne_y : w ≠ y := by
    intro h
    exact fresh_w (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))
  have fresh_y_ne_w : y ≠ w := Ne.symm fresh_w_ne_y
  have fresh_z_ne_w : z ≠ w :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have fresh_w_ne_z : w ≠ z := Ne.symm fresh_z_ne_w
  have p0000 :=
    @gNfv (synWb ph (.classEq (.cv x) (.cv z))) w
      (by
        first
        |
          (simp (config :=
              {
                failIfUnchanged :=
                  false }) only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wb,
              NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
              NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
              Finset.mem_singleton] at ⊢;
            aesop))
  have p0001 := @gSb8 (synWb ph (.classEq (.cv x) (.cv z))) x w p0000
  have p0002 := @gSbbi ph (.classEq (.cv x) (.cv z)) x w
  have p0003 :=
    @gNfsb ph x w y
      (by
        first
        | (aesop))
      hyp_sb8eu_1
  have p0004 :=
    @gEqusb3 x w z
      (by
        first
        | (aesop))
  have p0005 :=
    @gNfv (.classEq (.cv w) (.cv z)) y
      (by
        first
        |
          (simp (config :=
              {
                failIfUnchanged :=
                  false }) only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
              NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
              Finset.mem_singleton] at ⊢;
            aesop))
  have p0006_e00_recanon :
    Nominal.NPrf
      (synWb (synWsb w x (.classEq (.cv x) (.cv z))) (.classEq (.cv w) (.cv z))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold synWb synWsb synWa synWex
        apply Nominal.RecanonTransportDev.TRecanonWff.neg
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · apply Nominal.RecanonTransportDev.TRecanonWff.imp
          · apply Nominal.RecanonTransportDev.TRecanonWff.neg
            apply Nominal.RecanonTransportDev.TRecanonWff.imp
            · apply Nominal.RecanonTransportDev.TRecanonWff.imp
              · exact Nominal.RecanonTransportDev.TRecanonWff.same _
              · exact Nominal.RecanonTransportDev.TRecanonWff.objEq_classEq _ _
            · apply Nominal.RecanonTransportDev.TRecanonWff.neg
              apply Nominal.RecanonTransportDev.TRecanonWff.neg
              apply Nominal.RecanonTransportDev.TRecanonWff.all
              apply Nominal.RecanonTransportDev.TRecanonWff.neg
              apply Nominal.RecanonTransportDev.TRecanonWff.neg
              apply Nominal.RecanonTransportDev.TRecanonWff.imp
              · exact Nominal.RecanonTransportDev.TRecanonWff.same _
              · apply Nominal.RecanonTransportDev.TRecanonWff.neg
                exact Nominal.RecanonTransportDev.TRecanonWff.objEq_classEq _ _
          · exact Nominal.RecanonTransportDev.TRecanonWff.objEq_classEq _ _
        · apply Nominal.RecanonTransportDev.TRecanonWff.neg
          apply Nominal.RecanonTransportDev.TRecanonWff.imp
          · exact Nominal.RecanonTransportDev.TRecanonWff.objEq_classEq _ _
          · apply Nominal.RecanonTransportDev.TRecanonWff.neg
            apply Nominal.RecanonTransportDev.TRecanonWff.imp
            · apply Nominal.RecanonTransportDev.TRecanonWff.imp
              · exact Nominal.RecanonTransportDev.TRecanonWff.same _
              · exact Nominal.RecanonTransportDev.TRecanonWff.objEq_classEq _ _
            · apply Nominal.RecanonTransportDev.TRecanonWff.neg
              apply Nominal.RecanonTransportDev.TRecanonWff.neg
              apply Nominal.RecanonTransportDev.TRecanonWff.all
              apply Nominal.RecanonTransportDev.TRecanonWff.neg
              apply Nominal.RecanonTransportDev.TRecanonWff.neg
              apply Nominal.RecanonTransportDev.TRecanonWff.imp
              · exact Nominal.RecanonTransportDev.TRecanonWff.same _
              · apply Nominal.RecanonTransportDev.TRecanonWff.neg
                exact Nominal.RecanonTransportDev.TRecanonWff.objEq_classEq _ _)
      p0004
  have p0006 :=
    @gNfxfr (synWsb w x (.classEq (.cv x) (.cv z))) (.classEq (.cv w) (.cv z)) y
      p0006_e00_recanon p0005
  have p0007 :=
    @gNfbi (synWsb w x ph) (synWsb w x (.classEq (.cv x) (.cv z))) y p0003 p0006
  have p0008 :=
    @gNfxfr (synWsb w x (synWb ph (.classEq (.cv x) (.cv z))))
      (synWb (synWsb w x ph) (synWsb w x (.classEq (.cv x) (.cv z)))) y p0002 p0007
  have p0009 :=
    @gNfv (synWsb y x (synWb ph (.classEq (.cv x) (.cv z)))) w
      (by
        first
        |
          (simp (config :=
              {
                failIfUnchanged :=
                  false }) only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wsb,
              NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wb,
              NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
              NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
              Finset.mem_erase, Finset.mem_singleton] at ⊢;
            aesop))
  have p0010 := @gSbequ (synWb ph (.classEq (.cv x) (.cv z))) w y x
  have p0011 :=
    @gCbval (synWsb w x (synWb ph (.classEq (.cv x) (.cv z))))
      (synWsb y x (synWb ph (.classEq (.cv x) (.cv z)))) w y p0008 p0009 p0010
  have p0012 :=
    @gEqusb3 x y z
      (by
        first
        | (aesop))
  have p0013_e00_recanon :
    Nominal.NPrf
      (synWb (synWsb y x (.classEq (.cv x) (.cv z))) (.classEq (.cv y) (.cv z))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold synWb synWsb synWa synWex
        apply Nominal.RecanonTransportDev.TRecanonWff.neg
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · apply Nominal.RecanonTransportDev.TRecanonWff.imp
          · apply Nominal.RecanonTransportDev.TRecanonWff.neg
            apply Nominal.RecanonTransportDev.TRecanonWff.imp
            · apply Nominal.RecanonTransportDev.TRecanonWff.imp
              · exact Nominal.RecanonTransportDev.TRecanonWff.same _
              · exact Nominal.RecanonTransportDev.TRecanonWff.objEq_classEq _ _
            · apply Nominal.RecanonTransportDev.TRecanonWff.neg
              apply Nominal.RecanonTransportDev.TRecanonWff.neg
              apply Nominal.RecanonTransportDev.TRecanonWff.all
              apply Nominal.RecanonTransportDev.TRecanonWff.neg
              apply Nominal.RecanonTransportDev.TRecanonWff.neg
              apply Nominal.RecanonTransportDev.TRecanonWff.imp
              · exact Nominal.RecanonTransportDev.TRecanonWff.same _
              · apply Nominal.RecanonTransportDev.TRecanonWff.neg
                exact Nominal.RecanonTransportDev.TRecanonWff.objEq_classEq _ _
          · exact Nominal.RecanonTransportDev.TRecanonWff.objEq_classEq _ _
        · apply Nominal.RecanonTransportDev.TRecanonWff.neg
          apply Nominal.RecanonTransportDev.TRecanonWff.imp
          · exact Nominal.RecanonTransportDev.TRecanonWff.objEq_classEq _ _
          · apply Nominal.RecanonTransportDev.TRecanonWff.neg
            apply Nominal.RecanonTransportDev.TRecanonWff.imp
            · apply Nominal.RecanonTransportDev.TRecanonWff.imp
              · exact Nominal.RecanonTransportDev.TRecanonWff.same _
              · exact Nominal.RecanonTransportDev.TRecanonWff.objEq_classEq _ _
            · apply Nominal.RecanonTransportDev.TRecanonWff.neg
              apply Nominal.RecanonTransportDev.TRecanonWff.neg
              apply Nominal.RecanonTransportDev.TRecanonWff.all
              apply Nominal.RecanonTransportDev.TRecanonWff.neg
              apply Nominal.RecanonTransportDev.TRecanonWff.neg
              apply Nominal.RecanonTransportDev.TRecanonWff.imp
              · exact Nominal.RecanonTransportDev.TRecanonWff.same _
              · apply Nominal.RecanonTransportDev.TRecanonWff.neg
                exact Nominal.RecanonTransportDev.TRecanonWff.objEq_classEq _ _)
      p0012
  have p0013 :=
    @gSblbis (.classEq (.cv x) (.cv z)) (.classEq (.cv y) (.cv z)) ph x y
      p0013_e00_recanon
  have p0014 :=
    @gAlbii (synWsb y x (synWb ph (.classEq (.cv x) (.cv z))))
      (synWb (synWsb y x ph) (.classEq (.cv y) (.cv z))) y p0013
  have p0015 :=
    @gN3bitri (.all x (synWb ph (.classEq (.cv x) (.cv z))))
      (.all w (synWsb w x (synWb ph (.classEq (.cv x) (.cv z)))))
      (.all y (synWsb y x (synWb ph (.classEq (.cv x) (.cv z)))))
      (.all y (synWb (synWsb y x ph) (.classEq (.cv y) (.cv z)))) p0001 p0011 p0014
  have p0016 :=
    @gExbii (.all x (synWb ph (.classEq (.cv x) (.cv z))))
      (.all y (synWb (synWsb y x ph) (.classEq (.cv y) (.cv z)))) z p0015
  have p0017 :=
    Nominal.dfEu x z ph
      (by
        first
        | (aesop))
      (by
        first
        | (aesop))
  have p0018 :=
    Nominal.dfEu y z (synWsb y x ph)
      (by
        first
        | (aesop))
      (by
        first
        |
          (simp (config :=
              {
                failIfUnchanged :=
                  false }) only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wsb,
              Finset.mem_union, Finset.mem_erase, Finset.mem_singleton] at ⊢;
            aesop))
  have p0019_e01_recanon :
    Nominal.NPrf
      (synWb (synWeu x ph) (synWex z (.all x (synWb ph (.classEq (.cv x) (.cv z)))))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold synWb synWeu synWex
        simp (config := { failIfUnchanged := false }) only []
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
      p0017
  have p0019_e02_recanon :
    Nominal.NPrf
      (synWb (synWeu y (synWsb y x ph))
        (synWex z (.all y (synWb (synWsb y x ph) (.classEq (.cv y) (.cv z)))))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold synWb synWeu synWex synWsb synWa
        simp (config := { failIfUnchanged := false }) only []
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
      p0018
  have p0019 :=
    @gN3bitr4i (synWex z (.all x (synWb ph (.classEq (.cv x) (.cv z)))))
      (synWex z (.all y (synWb (synWsb y x ph) (.classEq (.cv y) (.cv z)))))
      (synWeu x ph) (synWeu y (synWsb y x ph)) p0016 p0019_e01_recanon
      p0019_e02_recanon
  exact p0019

/-- Checked nominal proof certificate identified upstream as `g_cbveu`. -/
@[expose]
noncomputable def gCbveu (ph : Wff) (ps : Wff) (x : Var) (y : Var)
    (hyp_cbveu_1 : Nominal.NPrf (synWnf y ph))
    (hyp_cbveu_2 : Nominal.NPrf (synWnf x ps))
    (hyp_cbveu_3 : Nominal.NPrf (.imp (.objEq x y) (synWb ph ps))) :
    Nominal.NPrf (synWb (synWeu x ph) (synWeu y ps)) :=
  by
  have p0000 := @gSb8eu ph x y hyp_cbveu_1
  have p0001 := @gSbie ph ps x y hyp_cbveu_2 hyp_cbveu_3
  have p0002 := @gEubii (synWsb y x ph) ps y p0001
  have p0003 :=
    @gBitri (synWeu x ph) (synWeu y (synWsb y x ph)) (synWeu y ps) p0000 p0002
  exact p0003

/-- Checked nominal proof certificate identified upstream as `g_eu1`. -/
@[expose]
noncomputable def gEu1 (ph : Wff) (x : Var) (y : Var) (dv_x_y : x ≠ y)
    (hyp_eu1_1 : Nominal.NPrf (synWnf y ph)) :
    Nominal.NPrf
      (synWb (synWeu x ph) (synWex x
          (synWa ph (.all y (.imp (synWsb y x ph) (.classEq (.cv x) (.cv y))))))) :=
  by
  let proofSupport : Finset Var := ph.fv ∪ ({ x } : Finset Var) ∪ ({ y } : Finset Var)
  have p0000 :=
    @gNfs1v ph x y
      (by
        first
        | (aesop))
  have p0001 :=
    @gEuf (synWsb y x ph) y x
      (by
        first
        | (aesop))
      p0000
  have p0002 := @gSb8eu ph x y hyp_eu1_1
  have p0003 := @gEqucom x y
  have p0004_e00_recanon :
    Nominal.NPrf (synWb (.classEq (.cv x) (.cv y)) (.classEq (.cv y) (.cv x))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold synWb
        apply Nominal.RecanonTransportDev.TRecanonWff.neg
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · apply Nominal.RecanonTransportDev.TRecanonWff.imp
          · exact Nominal.RecanonTransportDev.TRecanonWff.objEq_classEq _ _
          · exact Nominal.RecanonTransportDev.TRecanonWff.objEq_classEq _ _
        · apply Nominal.RecanonTransportDev.TRecanonWff.neg
          apply Nominal.RecanonTransportDev.TRecanonWff.imp
          · exact Nominal.RecanonTransportDev.TRecanonWff.objEq_classEq _ _
          · exact Nominal.RecanonTransportDev.TRecanonWff.objEq_classEq _ _)
      p0003
  have p0004 :=
    @gImbi2i (.classEq (.cv x) (.cv y)) (.classEq (.cv y) (.cv x)) (synWsb y x ph)
      p0004_e00_recanon
  have p0005 :=
    @gAlbii (.imp (synWsb y x ph) (.classEq (.cv x) (.cv y)))
      (.imp (synWsb y x ph) (.classEq (.cv y) (.cv x))) y p0004
  have p0006 := @gSb6rf ph x y hyp_eu1_1
  have p0007_e01_recanon :
    Nominal.NPrf
      (synWb ph (.all y (.imp (.classEq (.cv y) (.cv x)) (synWsb y x ph)))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold synWb synWsb synWa synWex
        apply Nominal.RecanonTransportDev.TRecanonWff.neg
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · apply Nominal.RecanonTransportDev.TRecanonWff.imp
          · exact Nominal.RecanonTransportDev.TRecanonWff.same _
          · apply Nominal.RecanonTransportDev.TRecanonWff.all
            apply Nominal.RecanonTransportDev.TRecanonWff.imp
            · exact Nominal.RecanonTransportDev.TRecanonWff.objEq_classEq _ _
            · exact Nominal.RecanonTransportDev.TRecanonWff.same _
        · apply Nominal.RecanonTransportDev.TRecanonWff.neg
          apply Nominal.RecanonTransportDev.TRecanonWff.imp
          · apply Nominal.RecanonTransportDev.TRecanonWff.all
            apply Nominal.RecanonTransportDev.TRecanonWff.imp
            · exact Nominal.RecanonTransportDev.TRecanonWff.objEq_classEq _ _
            · exact Nominal.RecanonTransportDev.TRecanonWff.same _
          · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0006
  have p0007 :=
    @gAnbi12i (.all y (.imp (synWsb y x ph) (.classEq (.cv x) (.cv y))))
      (.all y (.imp (synWsb y x ph) (.classEq (.cv y) (.cv x)))) ph
      (.all y (.imp (.classEq (.cv y) (.cv x)) (synWsb y x ph))) p0005 p0007_e01_recanon
  have p0008 := @gAncom ph (.all y (.imp (synWsb y x ph) (.classEq (.cv x) (.cv y))))
  have p0009 := @gAlbiim (synWsb y x ph) (.classEq (.cv y) (.cv x)) y
  have p0010 :=
    @gN3bitr4i (synWa (.all y (.imp (synWsb y x ph) (.classEq (.cv x) (.cv y)))) ph)
      (synWa (.all y (.imp (synWsb y x ph) (.classEq (.cv y) (.cv x))))
        (.all y (.imp (.classEq (.cv y) (.cv x)) (synWsb y x ph))))
      (synWa ph (.all y (.imp (synWsb y x ph) (.classEq (.cv x) (.cv y)))))
      (.all y (synWb (synWsb y x ph) (.classEq (.cv y) (.cv x)))) p0007 p0008 p0009
  have p0011 :=
    @gExbii (synWa ph (.all y (.imp (synWsb y x ph) (.classEq (.cv x) (.cv y)))))
      (.all y (synWb (synWsb y x ph) (.classEq (.cv y) (.cv x)))) x p0010
  have p0012 :=
    @gN3bitr4i (synWeu y (synWsb y x ph))
      (synWex x (.all y (synWb (synWsb y x ph) (.classEq (.cv y) (.cv x)))))
      (synWeu x ph)
      (synWex x (synWa ph (.all y (.imp (synWsb y x ph) (.classEq (.cv x) (.cv y))))))
      p0001 p0002 p0011
  exact p0012

/-- Checked nominal proof certificate identified upstream as `g_mo`. -/
@[expose]
noncomputable def gMo (ph : Wff) (x : Var) (y : Var) (dv_x_y : x ≠ y)
    (hyp_mo_1 : Nominal.NPrf (synWnf y ph)) :
    Nominal.NPrf
      (synWb (synWex y (.all x (.imp ph (.classEq (.cv x) (.cv y))))) (.all x
          (.all y (.imp (synWa ph (synWsb y x ph)) (.classEq (.cv x) (.cv y)))))) :=
  by
  let proofSupport : Finset Var := ph.fv ∪ ({ x } : Finset Var) ∪ ({ y } : Finset Var)
  let z : Var := freshVar proofSupport 0
  have fresh_z : z ∉ proofSupport :=
    by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_z_not_ph : z ∉ ph.fv := by
    intro h
    exact fresh_z (Finset.mem_union_left _ (Finset.mem_union_left _ (h)))
  have fresh_z_ne_x : z ≠ x := by
    intro h
    exact
      fresh_z
        (Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_singleton.mpr h)))
  have fresh_x_ne_z : x ≠ z := Ne.symm fresh_z_ne_x
  have fresh_z_ne_y : z ≠ y := by
    intro h
    exact fresh_z (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))
  have fresh_y_ne_z : y ≠ z := Ne.symm fresh_z_ne_y
  have p0000 :=
    @gNfv (.classEq (.cv x) (.cv z)) y
      (by
        first
        |
          (simp (config :=
              {
                failIfUnchanged :=
                  false }) only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
              NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
              Finset.mem_singleton] at ⊢;
            aesop))
  have p0001 := @gNfim ph (.classEq (.cv x) (.cv z)) y hyp_mo_1 p0000
  have p0002 := @gNfal (.imp ph (.classEq (.cv x) (.cv z))) y x p0001
  have p0003 :=
    @gNfv (.all x (.imp ph (.classEq (.cv x) (.cv y)))) z
      (by
        first
        |
          (simp (config :=
              { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_wff_all,
              NFChoice.Compiler.CoreFVSimp.fv_wff_imp,
              NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
              NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
              Finset.mem_erase, Finset.mem_singleton] at ⊢;
            aesop))
  have p0004 := @gEquequ2 z y x
  have p0005_e00_recanon :
    Nominal.NPrf
      (.imp (.classEq (.cv z) (.cv y))
        (synWb (.classEq (.cv x) (.cv z)) (.classEq (.cv x) (.cv y)))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold synWb
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · exact Nominal.RecanonTransportDev.TRecanonWff.objEq_classEq _ _
        · apply Nominal.RecanonTransportDev.TRecanonWff.neg
          apply Nominal.RecanonTransportDev.TRecanonWff.imp
          · apply Nominal.RecanonTransportDev.TRecanonWff.imp
            · exact Nominal.RecanonTransportDev.TRecanonWff.objEq_classEq _ _
            · exact Nominal.RecanonTransportDev.TRecanonWff.objEq_classEq _ _
          · apply Nominal.RecanonTransportDev.TRecanonWff.neg
            apply Nominal.RecanonTransportDev.TRecanonWff.imp
            · exact Nominal.RecanonTransportDev.TRecanonWff.objEq_classEq _ _
            · exact Nominal.RecanonTransportDev.TRecanonWff.objEq_classEq _ _)
      p0004
  have p0005 :=
    @gImbi2d (.classEq (.cv z) (.cv y)) (.classEq (.cv x) (.cv z))
      (.classEq (.cv x) (.cv y)) ph p0005_e00_recanon
  have p0006 :=
    @gAlbidv (.classEq (.cv z) (.cv y)) (.imp ph (.classEq (.cv x) (.cv z)))
      (.imp ph (.classEq (.cv x) (.cv y))) x
      (by
        first
        |
          (simp (config :=
              {
                failIfUnchanged :=
                  false }) only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
              NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
              Finset.mem_singleton] at ⊢;
            aesop))
      p0005
  have p0007_e02_recanon :
    Nominal.NPrf
      (.imp (.objEq z y) (synWb (.all x (.imp ph (.classEq (.cv x) (.cv z))))
          (.all x (.imp ph (.classEq (.cv x) (.cv y)))))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold synWb
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
        · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0006
  have p0007 :=
    @gCbvex (.all x (.imp ph (.classEq (.cv x) (.cv z))))
      (.all x (.imp ph (.classEq (.cv x) (.cv y)))) z y p0002 p0003 p0007_e02_recanon
  have p0008 := @gNfs1 ph x y hyp_mo_1
  have p0009 :=
    @gNfv (.classEq (.cv y) (.cv z)) x
      (by
        first
        |
          (simp (config :=
              {
                failIfUnchanged :=
                  false }) only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
              NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
              Finset.mem_singleton] at ⊢;
            aesop))
  have p0010 := @gNfim (synWsb y x ph) (.classEq (.cv y) (.cv z)) x p0008 p0009
  have p0011 := @gSbequ2 ph x y
  have p0012 := Nominal.ax8 x y z
  have p0013_e00_recanon :
    Nominal.NPrf (.imp (.classEq (.cv x) (.cv y)) (.imp (synWsb y x ph) ph)) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold synWsb synWa synWex
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · exact Nominal.RecanonTransportDev.TRecanonWff.objEq_classEq _ _
        · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0011
  have p0013_e01_recanon :
    Nominal.NPrf
      (.imp (.classEq (.cv x) (.cv y))
        (.imp (.classEq (.cv x) (.cv z)) (.classEq (.cv y) (.cv z)))) :=
    Nominal.RecanonTransportDev.transport
      (by
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · exact Nominal.RecanonTransportDev.TRecanonWff.objEq_classEq _ _
        · apply Nominal.RecanonTransportDev.TRecanonWff.imp
          · exact Nominal.RecanonTransportDev.TRecanonWff.objEq_classEq _ _
          · exact Nominal.RecanonTransportDev.TRecanonWff.objEq_classEq _ _)
      p0012
  have p0013 :=
    @gImim12d (.classEq (.cv x) (.cv y)) (synWsb y x ph) ph (.classEq (.cv x) (.cv z))
      (.classEq (.cv y) (.cv z)) p0013_e00_recanon p0013_e01_recanon
  have p0014_e02_recanon :
    Nominal.NPrf
      (.imp (.objEq x y) (.imp (.imp ph (.classEq (.cv x) (.cv z)))
          (.imp (synWsb y x ph) (.classEq (.cv y) (.cv z))))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold synWsb synWa synWex
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
        · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0013
  have p0014 :=
    @gCbv3 (.imp ph (.classEq (.cv x) (.cv z)))
      (.imp (synWsb y x ph) (.classEq (.cv y) (.cv z))) x y p0001 p0010 p0014_e02_recanon
  have p0015 :=
    @gAncli (.all x (.imp ph (.classEq (.cv x) (.cv z))))
      (.all y (.imp (synWsb y x ph) (.classEq (.cv y) (.cv z)))) p0014
  have p0016 :=
    @gAaan (.imp ph (.classEq (.cv x) (.cv z)))
      (.imp (synWsb y x ph) (.classEq (.cv y) (.cv z))) x y p0001 p0010
  have p0017 :=
    @gSylibr (.all x (.imp ph (.classEq (.cv x) (.cv z))))
      (synWa (.all x (.imp ph (.classEq (.cv x) (.cv z))))
        (.all y (.imp (synWsb y x ph) (.classEq (.cv y) (.cv z)))))
      (.all x (.all y (synWa (.imp ph (.classEq (.cv x) (.cv z)))
            (.imp (synWsb y x ph) (.classEq (.cv y) (.cv z))))))
      p0015 p0016
  have p0018 :=
    @gPrth ph (.classEq (.cv x) (.cv z)) (synWsb y x ph) (.classEq (.cv y) (.cv z))
  have p0019 := @gEqutr2 x y z
  have p0020_e01_recanon :
    Nominal.NPrf
      (.imp (synWa (.classEq (.cv x) (.cv z)) (.classEq (.cv y) (.cv z)))
        (.classEq (.cv x) (.cv y))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold synWa
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · apply Nominal.RecanonTransportDev.TRecanonWff.neg
          apply Nominal.RecanonTransportDev.TRecanonWff.imp
          · exact Nominal.RecanonTransportDev.TRecanonWff.objEq_classEq _ _
          · apply Nominal.RecanonTransportDev.TRecanonWff.neg
            exact Nominal.RecanonTransportDev.TRecanonWff.objEq_classEq _ _
        · exact Nominal.RecanonTransportDev.TRecanonWff.objEq_classEq _ _)
      p0019
  have p0020 :=
    @gSyl6
      (synWa (.imp ph (.classEq (.cv x) (.cv z)))
        (.imp (synWsb y x ph) (.classEq (.cv y) (.cv z))))
      (synWa ph (synWsb y x ph))
      (synWa (.classEq (.cv x) (.cv z)) (.classEq (.cv y) (.cv z)))
      (.classEq (.cv x) (.cv y)) p0018 p0020_e01_recanon
  have p0021 :=
    @gN2alimi
      (synWa (.imp ph (.classEq (.cv x) (.cv z)))
        (.imp (synWsb y x ph) (.classEq (.cv y) (.cv z))))
      (.imp (synWa ph (synWsb y x ph)) (.classEq (.cv x) (.cv y))) x y p0020
  have p0022 :=
    @gSyl (.all x (.imp ph (.classEq (.cv x) (.cv z))))
      (.all x (.all y (synWa (.imp ph (.classEq (.cv x) (.cv z)))
            (.imp (synWsb y x ph) (.classEq (.cv y) (.cv z))))))
      (.all x (.all y (.imp (synWa ph (synWsb y x ph)) (.classEq (.cv x) (.cv y)))))
      p0017 p0021
  have p0023 :=
    @gExlimiv (.all x (.imp ph (.classEq (.cv x) (.cv z))))
      (.all x (.all y (.imp (synWa ph (synWsb y x ph)) (.classEq (.cv x) (.cv y))))) z
      (by
        first
        |
          (simp (config :=
              { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_wff_all,
              NFChoice.Compiler.CoreFVSimp.fv_wff_imp,
              NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
              NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wsb,
              NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
              NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
              Finset.mem_erase, Finset.mem_singleton] at ⊢;
            aesop))
      p0022
  have p0024 :=
    @gSylbir (synWex y (.all x (.imp ph (.classEq (.cv x) (.cv y)))))
      (synWex z (.all x (.imp ph (.classEq (.cv x) (.cv z)))))
      (.all x (.all y (.imp (synWa ph (synWsb y x ph)) (.classEq (.cv x) (.cv y)))))
      p0007 p0023
  have p0025 := @gNfa2 (.imp (synWa ph (synWsb y x ph)) (.classEq (.cv x) (.cv y))) y x
  have p0026 := @gSp (.imp (synWa ph (synWsb y x ph)) (.classEq (.cv x) (.cv y))) y
  have p0027 :=
    @gExp3a (.all y (.imp (synWa ph (synWsb y x ph)) (.classEq (.cv x) (.cv y)))) ph
      (synWsb y x ph) (.classEq (.cv x) (.cv y)) p0026
  have p0028 :=
    @gCom3r (.all y (.imp (synWa ph (synWsb y x ph)) (.classEq (.cv x) (.cv y)))) ph
      (synWsb y x ph) (.classEq (.cv x) (.cv y)) p0027
  have p0029 :=
    @gAlimd (synWsb y x ph)
      (.all y (.imp (synWa ph (synWsb y x ph)) (.classEq (.cv x) (.cv y))))
      (.imp ph (.classEq (.cv x) (.cv y))) x p0008 p0028
  have p0030 :=
    @gCom12 (synWsb y x ph)
      (.all x (.all y (.imp (synWa ph (synWsb y x ph)) (.classEq (.cv x) (.cv y)))))
      (.all x (.imp ph (.classEq (.cv x) (.cv y)))) p0029
  have p0031 :=
    @gEximd
      (.all x (.all y (.imp (synWa ph (synWsb y x ph)) (.classEq (.cv x) (.cv y)))))
      (synWsb y x ph) (.all x (.imp ph (.classEq (.cv x) (.cv y)))) y p0025 p0030
  have p0032 := @gAlnex (synWsb y x ph) y
  have p0033 := @gNfn (synWsb y x ph) x p0008
  have p0034 := @gNfn ph y hyp_mo_1
  have p0035 := @gSbequ1 ph x y
  have p0036 := @gEqucoms (.imp ph (synWsb y x ph)) x y p0035
  have p0037_e00_recanon :
    Nominal.NPrf (.imp (.classEq (.cv y) (.cv x)) (.imp ph (synWsb y x ph))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold synWsb synWa synWex
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · exact Nominal.RecanonTransportDev.TRecanonWff.objEq_classEq _ _
        · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0036
  have p0037 := @gCon3d (.classEq (.cv y) (.cv x)) ph (synWsb y x ph) p0037_e00_recanon
  have p0038_e02_recanon :
    Nominal.NPrf (.imp (.objEq y x) (.imp (.neg (synWsb y x ph)) (.neg ph))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold synWsb synWa synWex
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
        · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0037
  have p0038 :=
    @gCbv3 (.neg (synWsb y x ph)) (.neg ph) y x p0033 p0034 p0038_e02_recanon
  have p0039 := @gPm221 ph (.classEq (.cv x) (.cv y))
  have p0040 := @gAlimi (.neg ph) (.imp ph (.classEq (.cv x) (.cv y))) x p0039
  have p0041 := @gN198a (.all x (.imp ph (.classEq (.cv x) (.cv y)))) y
  have p0042 :=
    @gN3syl (.all y (.neg (synWsb y x ph))) (.all x (.neg ph))
      (.all x (.imp ph (.classEq (.cv x) (.cv y))))
      (synWex y (.all x (.imp ph (.classEq (.cv x) (.cv y))))) p0038 p0040 p0041
  have p0043 :=
    @gSylbir (.neg (synWex y (synWsb y x ph))) (.all y (.neg (synWsb y x ph)))
      (synWex y (.all x (.imp ph (.classEq (.cv x) (.cv y))))) p0032 p0042
  have p0044 :=
    @gPm261d1
      (.all x (.all y (.imp (synWa ph (synWsb y x ph)) (.classEq (.cv x) (.cv y)))))
      (synWex y (synWsb y x ph))
      (synWex y (.all x (.imp ph (.classEq (.cv x) (.cv y))))) p0031 p0043
  have p0045 :=
    @gImpbii (synWex y (.all x (.imp ph (.classEq (.cv x) (.cv y)))))
      (.all x (.all y (.imp (synWa ph (synWsb y x ph)) (.classEq (.cv x) (.cv y)))))
      p0024 p0044
  exact p0045

/-- Checked nominal proof certificate identified upstream as `g_euex`. -/
@[expose]
noncomputable def gEuex (ph : Wff) (x : Var) :
    Nominal.NPrf (.imp (synWeu x ph) (synWex x ph)) :=
  by
  let proofSupport : Finset Var := ph.fv ∪ ({ x } : Finset Var)
  let y : Var := freshVar proofSupport 0
  have fresh_y : y ∉ proofSupport :=
    by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_y_not_ph : y ∉ ph.fv := by
    intro h
    exact fresh_y (Finset.mem_union_left _ (h))
  have fresh_y_ne_x : y ≠ x := by
    intro h
    exact fresh_y (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))
  have fresh_x_ne_y : x ≠ y := Ne.symm fresh_y_ne_x
  have p0000 :=
    @gNfv ph y
      (by
        first
        | (aesop))
  have p0001 :=
    @gEu1 ph x y
      (by
        first
        | (aesop))
      p0000
  have p0002 :=
    @gExsimpl ph (.all y (.imp (synWsb y x ph) (.classEq (.cv x) (.cv y)))) x
  have p0003 :=
    @gSylbi (synWeu x ph)
      (synWex x (synWa ph (.all y (.imp (synWsb y x ph) (.classEq (.cv x) (.cv y))))))
      (synWex x ph) p0001 p0002
  exact p0003

/-- Checked nominal proof certificate identified upstream as `g_eumo0`. -/
@[expose]
noncomputable def gEumo0 (ph : Wff) (x : Var) (y : Var) (dv_x_y : x ≠ y)
    (hyp_eumo0_1 : Nominal.NPrf (synWnf y ph)) :
    Nominal.NPrf (.imp (synWeu x ph) (synWex y (.all x (.imp ph (.objEq x y))))) :=
  by
  let proofSupport : Finset Var := ph.fv ∪ ({ x } : Finset Var) ∪ ({ y } : Finset Var)
  have p0000 :=
    @gEuf ph x y
      (by
        first
        | (aesop))
      hyp_eumo0_1
  have p0001 := @gBi1 ph (.objEq x y)
  have p0002 := @gAlimi (synWb ph (.objEq x y)) (.imp ph (.objEq x y)) x p0001
  have p0003 :=
    @gEximi (.all x (synWb ph (.objEq x y))) (.all x (.imp ph (.objEq x y))) y p0002
  have p0004_e00_recanon :
    Nominal.NPrf (synWb (synWeu x ph) (synWex y (.all x (synWb ph (.objEq x y))))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold synWb synWeu synWex
        simp (config := { failIfUnchanged := false }) only []
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
              · exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
            · apply Nominal.RecanonTransportDev.TRecanonWff.neg
              apply Nominal.RecanonTransportDev.TRecanonWff.imp
              · exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
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
              · exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
            · apply Nominal.RecanonTransportDev.TRecanonWff.neg
              apply Nominal.RecanonTransportDev.TRecanonWff.imp
              · exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
              · exact Nominal.RecanonTransportDev.TRecanonWff.same _
          · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0000
  have p0004 :=
    @gSylbi (synWeu x ph) (synWex y (.all x (synWb ph (.objEq x y))))
      (synWex y (.all x (.imp ph (.objEq x y)))) p0004_e00_recanon p0003
  exact p0004

/-- Checked nominal proof certificate identified upstream as `g_eu2`. -/
@[expose]
noncomputable def gEu2 (ph : Wff) (x : Var) (y : Var) (dv_x_y : x ≠ y)
    (hyp_eu2_1 : Nominal.NPrf (synWnf y ph)) :
    Nominal.NPrf
      (synWb (synWeu x ph) (synWa (synWex x ph)
          (.all x (.all y (.imp (synWa ph (synWsb y x ph)) (.objEq x y)))))) :=
  by
  let proofSupport : Finset Var := ph.fv ∪ ({ x } : Finset Var) ∪ ({ y } : Finset Var)
  have p0000 := @gEuex ph x
  have p0001 :=
    @gEumo0 ph x y
      (by
        first
        | (aesop))
      hyp_eu2_1
  have p0002 :=
    @gMo ph x y
      (by
        first
        | (aesop))
      hyp_eu2_1
  have p0003_e01_recanon :
    Nominal.NPrf
      (synWb (synWex y (.all x (.imp ph (.objEq x y))))
        (.all x (.all y (.imp (synWa ph (synWsb y x ph)) (.objEq x y))))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold synWb synWex synWa synWsb
        apply Nominal.RecanonTransportDev.TRecanonWff.neg
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · apply Nominal.RecanonTransportDev.TRecanonWff.imp
          · apply Nominal.RecanonTransportDev.TRecanonWff.neg
            apply Nominal.RecanonTransportDev.TRecanonWff.all
            apply Nominal.RecanonTransportDev.TRecanonWff.neg
            apply Nominal.RecanonTransportDev.TRecanonWff.all
            apply Nominal.RecanonTransportDev.TRecanonWff.imp
            · exact Nominal.RecanonTransportDev.TRecanonWff.same _
            · exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
          · apply Nominal.RecanonTransportDev.TRecanonWff.all
            apply Nominal.RecanonTransportDev.TRecanonWff.all
            apply Nominal.RecanonTransportDev.TRecanonWff.imp
            · exact Nominal.RecanonTransportDev.TRecanonWff.same _
            · exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
        · apply Nominal.RecanonTransportDev.TRecanonWff.neg
          apply Nominal.RecanonTransportDev.TRecanonWff.imp
          · apply Nominal.RecanonTransportDev.TRecanonWff.all
            apply Nominal.RecanonTransportDev.TRecanonWff.all
            apply Nominal.RecanonTransportDev.TRecanonWff.imp
            · exact Nominal.RecanonTransportDev.TRecanonWff.same _
            · exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
          · apply Nominal.RecanonTransportDev.TRecanonWff.neg
            apply Nominal.RecanonTransportDev.TRecanonWff.all
            apply Nominal.RecanonTransportDev.TRecanonWff.neg
            apply Nominal.RecanonTransportDev.TRecanonWff.all
            apply Nominal.RecanonTransportDev.TRecanonWff.imp
            · exact Nominal.RecanonTransportDev.TRecanonWff.same _
            · exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _)
      p0002
  have p0003 :=
    @gSylib (synWeu x ph) (synWex y (.all x (.imp ph (.objEq x y))))
      (.all x (.all y (.imp (synWa ph (synWsb y x ph)) (.objEq x y)))) p0001
      p0003_e01_recanon
  have p0004 :=
    @gJca (synWeu x ph) (synWex x ph)
      (.all x (.all y (.imp (synWa ph (synWsb y x ph)) (.objEq x y)))) p0000 p0003
  have p0005 := @gN1929r ph (.all y (.imp (synWa ph (synWsb y x ph)) (.objEq x y))) x
  have p0006 := @gImpexp ph (synWsb y x ph) (.objEq x y)
  have p0007 :=
    @gAlbii (.imp (synWa ph (synWsb y x ph)) (.objEq x y))
      (.imp ph (.imp (synWsb y x ph) (.objEq x y))) y p0006
  have p0008 := @gN1921 ph (.imp (synWsb y x ph) (.objEq x y)) y hyp_eu2_1
  have p0009 :=
    @gBitri (.all y (.imp (synWa ph (synWsb y x ph)) (.objEq x y)))
      (.all y (.imp ph (.imp (synWsb y x ph) (.objEq x y))))
      (.imp ph (.all y (.imp (synWsb y x ph) (.objEq x y)))) p0007 p0008
  have p0010 :=
    @gAnbi2i (.all y (.imp (synWa ph (synWsb y x ph)) (.objEq x y)))
      (.imp ph (.all y (.imp (synWsb y x ph) (.objEq x y)))) ph p0009
  have p0011 := @gAbai ph (.all y (.imp (synWsb y x ph) (.objEq x y)))
  have p0012 :=
    @gBitr4i (synWa ph (.all y (.imp (synWa ph (synWsb y x ph)) (.objEq x y))))
      (synWa ph (.imp ph (.all y (.imp (synWsb y x ph) (.objEq x y)))))
      (synWa ph (.all y (.imp (synWsb y x ph) (.objEq x y)))) p0010 p0011
  have p0013 :=
    @gExbii (synWa ph (.all y (.imp (synWa ph (synWsb y x ph)) (.objEq x y))))
      (synWa ph (.all y (.imp (synWsb y x ph) (.objEq x y)))) x p0012
  have p0014 :=
    @gSylib
      (synWa (synWex x ph) (.all x (.all y (.imp (synWa ph (synWsb y x ph)) (.objEq x y)))))
      (synWex x (synWa ph (.all y (.imp (synWa ph (synWsb y x ph)) (.objEq x y)))))
      (synWex x (synWa ph (.all y (.imp (synWsb y x ph) (.objEq x y))))) p0005 p0013
  have p0015 :=
    @gEu1 ph x y
      (by
        first
        | (aesop))
      hyp_eu2_1
  have p0016_e01_recanon :
    Nominal.NPrf
      (synWb (synWeu x ph)
        (synWex x (synWa ph (.all y (.imp (synWsb y x ph) (.objEq x y)))))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold synWb synWeu synWex
        simp (config := { failIfUnchanged := false }) only []
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
              apply Nominal.RecanonTransportDev.TRecanonWff.imp
              · exact Nominal.RecanonTransportDev.TRecanonWff.same _
              · exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
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
              apply Nominal.RecanonTransportDev.TRecanonWff.imp
              · exact Nominal.RecanonTransportDev.TRecanonWff.same _
              · exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
          · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0015
  have p0016 :=
    @gSylibr
      (synWa (synWex x ph) (.all x (.all y (.imp (synWa ph (synWsb y x ph)) (.objEq x y)))))
      (synWex x (synWa ph (.all y (.imp (synWsb y x ph) (.objEq x y))))) (synWeu x ph)
      p0014 p0016_e01_recanon
  have p0017 :=
    @gImpbii (synWeu x ph)
      (synWa (synWex x ph) (.all x (.all y (.imp (synWa ph (synWsb y x ph)) (.objEq x y)))))
      p0004 p0016
  exact p0017

/-- Checked nominal proof certificate identified upstream as `g_eu3`. -/
@[expose]
noncomputable def gEu3 (ph : Wff) (x : Var) (y : Var) (dv_x_y : x ≠ y)
    (hyp_eu3_1 : Nominal.NPrf (synWnf y ph)) :
    Nominal.NPrf
      (synWb (synWeu x ph)
        (synWa (synWex x ph) (synWex y (.all x (.imp ph (.objEq x y)))))) :=
  by
  let proofSupport : Finset Var := ph.fv ∪ ({ x } : Finset Var) ∪ ({ y } : Finset Var)
  have p0000 :=
    @gEu2 ph x y
      (by
        first
        | (aesop))
      hyp_eu3_1
  have p0001 :=
    @gMo ph x y
      (by
        first
        | (aesop))
      hyp_eu3_1
  have p0002_e00_recanon :
    Nominal.NPrf
      (synWb (synWex y (.all x (.imp ph (.objEq x y))))
        (.all x (.all y (.imp (synWa ph (synWsb y x ph)) (.objEq x y))))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold synWb synWex synWa synWsb
        apply Nominal.RecanonTransportDev.TRecanonWff.neg
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · apply Nominal.RecanonTransportDev.TRecanonWff.imp
          · apply Nominal.RecanonTransportDev.TRecanonWff.neg
            apply Nominal.RecanonTransportDev.TRecanonWff.all
            apply Nominal.RecanonTransportDev.TRecanonWff.neg
            apply Nominal.RecanonTransportDev.TRecanonWff.all
            apply Nominal.RecanonTransportDev.TRecanonWff.imp
            · exact Nominal.RecanonTransportDev.TRecanonWff.same _
            · exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
          · apply Nominal.RecanonTransportDev.TRecanonWff.all
            apply Nominal.RecanonTransportDev.TRecanonWff.all
            apply Nominal.RecanonTransportDev.TRecanonWff.imp
            · exact Nominal.RecanonTransportDev.TRecanonWff.same _
            · exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
        · apply Nominal.RecanonTransportDev.TRecanonWff.neg
          apply Nominal.RecanonTransportDev.TRecanonWff.imp
          · apply Nominal.RecanonTransportDev.TRecanonWff.all
            apply Nominal.RecanonTransportDev.TRecanonWff.all
            apply Nominal.RecanonTransportDev.TRecanonWff.imp
            · exact Nominal.RecanonTransportDev.TRecanonWff.same _
            · exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
          · apply Nominal.RecanonTransportDev.TRecanonWff.neg
            apply Nominal.RecanonTransportDev.TRecanonWff.all
            apply Nominal.RecanonTransportDev.TRecanonWff.neg
            apply Nominal.RecanonTransportDev.TRecanonWff.all
            apply Nominal.RecanonTransportDev.TRecanonWff.imp
            · exact Nominal.RecanonTransportDev.TRecanonWff.same _
            · exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _)
      p0001
  have p0002 :=
    @gAnbi2i (synWex y (.all x (.imp ph (.objEq x y))))
      (.all x (.all y (.imp (synWa ph (synWsb y x ph)) (.objEq x y)))) (synWex x ph)
      p0002_e00_recanon
  have p0003 :=
    @gBitr4i (synWeu x ph)
      (synWa (synWex x ph) (.all x (.all y (.imp (synWa ph (synWsb y x ph)) (.objEq x y)))))
      (synWa (synWex x ph) (synWex y (.all x (.imp ph (.objEq x y))))) p0000 p0002
  exact p0003

/-- Checked nominal proof certificate identified upstream as `g_mo2`. -/
@[expose]
noncomputable def gMo2 (ph : Wff) (x : Var) (y : Var) (dv_x_y : x ≠ y)
    (hyp_mo2_1 : Nominal.NPrf (synWnf y ph)) :
    Nominal.NPrf (synWb (synWmo x ph) (synWex y (.all x (.imp ph (.objEq x y))))) :=
  by
  let proofSupport : Finset Var := ph.fv ∪ ({ x } : Finset Var) ∪ ({ y } : Finset Var)
  have p0000 := (Nominal.biimpRefl (synWmo x ph))
  have p0001 := @gAlnex ph x
  have p0002 := @gPm221 ph (.objEq x y)
  have p0003 := @gAlimi (.neg ph) (.imp ph (.objEq x y)) x p0002
  have p0004 := @gN198a (.all x (.imp ph (.objEq x y))) y
  have p0005 :=
    @gSyl (.all x (.neg ph)) (.all x (.imp ph (.objEq x y)))
      (synWex y (.all x (.imp ph (.objEq x y)))) p0003 p0004
  have p0006 :=
    @gSylbir (.neg (synWex x ph)) (.all x (.neg ph))
      (synWex y (.all x (.imp ph (.objEq x y)))) p0001 p0005
  have p0007 :=
    @gEumo0 ph x y
      (by
        first
        | (aesop))
      hyp_mo2_1
  have p0008 :=
    @gJa (synWex x ph) (synWeu x ph) (synWex y (.all x (.imp ph (.objEq x y)))) p0006
      p0007
  have p0009 :=
    @gEu3 ph x y
      (by
        first
        | (aesop))
      hyp_mo2_1
  have p0010 :=
    @gSimplbi2com (synWeu x ph) (synWex x ph)
      (synWex y (.all x (.imp ph (.objEq x y)))) p0009
  have p0011 :=
    @gImpbii (.imp (synWex x ph) (synWeu x ph))
      (synWex y (.all x (.imp ph (.objEq x y)))) p0008 p0010
  have p0012 :=
    @gBitri (synWmo x ph) (.imp (synWex x ph) (synWeu x ph))
      (synWex y (.all x (.imp ph (.objEq x y)))) p0000 p0011
  exact p0012

/-- Checked nominal proof certificate identified upstream as `g_mo3`. -/
@[expose]
noncomputable def gMo3 (ph : Wff) (x : Var) (y : Var) (dv_x_y : x ≠ y)
    (hyp_mo3_1 : Nominal.NPrf (synWnf y ph)) :
    Nominal.NPrf
      (synWb (synWmo x ph)
        (.all x (.all y (.imp (synWa ph (synWsb y x ph)) (.objEq x y))))) :=
  by
  let proofSupport : Finset Var := ph.fv ∪ ({ x } : Finset Var) ∪ ({ y } : Finset Var)
  have p0000 :=
    @gMo2 ph x y
      (by
        first
        | (aesop))
      hyp_mo3_1
  have p0001 :=
    @gMo ph x y
      (by
        first
        | (aesop))
      hyp_mo3_1
  have p0002_e01_recanon :
    Nominal.NPrf
      (synWb (synWex y (.all x (.imp ph (.objEq x y))))
        (.all x (.all y (.imp (synWa ph (synWsb y x ph)) (.objEq x y))))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold synWb synWex synWa synWsb
        apply Nominal.RecanonTransportDev.TRecanonWff.neg
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · apply Nominal.RecanonTransportDev.TRecanonWff.imp
          · apply Nominal.RecanonTransportDev.TRecanonWff.neg
            apply Nominal.RecanonTransportDev.TRecanonWff.all
            apply Nominal.RecanonTransportDev.TRecanonWff.neg
            apply Nominal.RecanonTransportDev.TRecanonWff.all
            apply Nominal.RecanonTransportDev.TRecanonWff.imp
            · exact Nominal.RecanonTransportDev.TRecanonWff.same _
            · exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
          · apply Nominal.RecanonTransportDev.TRecanonWff.all
            apply Nominal.RecanonTransportDev.TRecanonWff.all
            apply Nominal.RecanonTransportDev.TRecanonWff.imp
            · exact Nominal.RecanonTransportDev.TRecanonWff.same _
            · exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
        · apply Nominal.RecanonTransportDev.TRecanonWff.neg
          apply Nominal.RecanonTransportDev.TRecanonWff.imp
          · apply Nominal.RecanonTransportDev.TRecanonWff.all
            apply Nominal.RecanonTransportDev.TRecanonWff.all
            apply Nominal.RecanonTransportDev.TRecanonWff.imp
            · exact Nominal.RecanonTransportDev.TRecanonWff.same _
            · exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
          · apply Nominal.RecanonTransportDev.TRecanonWff.neg
            apply Nominal.RecanonTransportDev.TRecanonWff.all
            apply Nominal.RecanonTransportDev.TRecanonWff.neg
            apply Nominal.RecanonTransportDev.TRecanonWff.all
            apply Nominal.RecanonTransportDev.TRecanonWff.imp
            · exact Nominal.RecanonTransportDev.TRecanonWff.same _
            · exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _)
      p0001
  have p0002 :=
    @gBitri (synWmo x ph) (synWex y (.all x (.imp ph (.objEq x y))))
      (.all x (.all y (.imp (synWa ph (synWsb y x ph)) (.objEq x y)))) p0000
      p0002_e01_recanon
  exact p0002

/-- Checked nominal proof certificate identified upstream as `g_mo4f`. -/
@[expose]
noncomputable def gMo4f (ph : Wff) (ps : Wff) (x : Var) (y : Var) (dv_ph_y : y ∉ ph.fv)
    (dv_x_y : x ≠ y) (hyp_mo4f_1 : Nominal.NPrf (synWnf x ps))
    (hyp_mo4f_2 : Nominal.NPrf (.imp (.objEq x y) (synWb ph ps))) :
    Nominal.NPrf
      (synWb (synWmo x ph) (.all x (.all y (.imp (synWa ph ps) (.objEq x y))))) :=
  by
  let proofSupport : Finset Var :=
    ph.fv ∪ ps.fv ∪ ({ x } : Finset Var) ∪ ({ y } : Finset Var)
  have p0000 :=
    @gNfv ph y
      (by
        first
        | (aesop))
  have p0001 :=
    @gMo3 ph x y
      (by
        first
        | (aesop))
      p0000
  have p0002 := @gSbie ph ps x y hyp_mo4f_1 hyp_mo4f_2
  have p0003 := @gAnbi2i (synWsb y x ph) ps ph p0002
  have p0004 := @gImbi1i (synWa ph (synWsb y x ph)) (synWa ph ps) (.objEq x y) p0003
  have p0005 :=
    @gN2albii (.imp (synWa ph (synWsb y x ph)) (.objEq x y))
      (.imp (synWa ph ps) (.objEq x y)) x y p0004
  have p0006 :=
    @gBitri (synWmo x ph)
      (.all x (.all y (.imp (synWa ph (synWsb y x ph)) (.objEq x y))))
      (.all x (.all y (.imp (synWa ph ps) (.objEq x y)))) p0001 p0005
  exact p0006

/-- Checked nominal proof certificate identified upstream as `g_mo4`. -/
@[expose]
noncomputable def gMo4 (ph : Wff) (ps : Wff) (x : Var) (y : Var) (dv_ph_y : y ∉ ph.fv)
    (dv_ps_x : x ∉ ps.fv) (dv_x_y : x ≠ y)
    (hyp_mo4_1 : Nominal.NPrf (.imp (.objEq x y) (synWb ph ps))) :
    Nominal.NPrf
      (synWb (synWmo x ph) (.all x (.all y (.imp (synWa ph ps) (.objEq x y))))) :=
  by
  let proofSupport : Finset Var :=
    ph.fv ∪ ps.fv ∪ ({ x } : Finset Var) ∪ ({ y } : Finset Var)
  have p0000 :=
    @gNfv ps x
      (by
        first
        | (aesop))
  have p0001 :=
    @gMo4f ph ps x y
      (by
        first
        | (aesop))
      (by
        first
        | (aesop))
      p0000 hyp_mo4_1
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_mobid`. -/
@[expose]
noncomputable def gMobid (ph : Wff) (ps : Wff) (ch : Wff) (x : Var)
    (hyp_mobid_1 : Nominal.NPrf (synWnf x ph))
    (hyp_mobid_2 : Nominal.NPrf (.imp ph (synWb ps ch))) :
    Nominal.NPrf (.imp ph (synWb (synWmo x ps) (synWmo x ch))) :=
  by
  have p0000 := @gExbid ph ps ch x hyp_mobid_1 hyp_mobid_2
  have p0001 := @gEubid ph ps ch x hyp_mobid_1 hyp_mobid_2
  have p0002 :=
    @gImbi12d ph (synWex x ps) (synWex x ch) (synWeu x ps) (synWeu x ch) p0000 p0001
  have p0003 := (Nominal.biimpRefl (synWmo x ps))
  have p0004 := (Nominal.biimpRefl (synWmo x ch))
  have p0005 :=
    @gN3bitr4g ph (.imp (synWex x ps) (synWeu x ps))
      (.imp (synWex x ch) (synWeu x ch)) (synWmo x ps) (synWmo x ch) p0002 p0003 p0004
  exact p0005

/-- Checked nominal proof certificate identified upstream as `g_mobidv`. -/
@[expose]
noncomputable def gMobidv (ph : Wff) (ps : Wff) (ch : Wff) (x : Var)
    (dv_ph_x : x ∉ ph.fv) (hyp_mobidv_1 : Nominal.NPrf (.imp ph (synWb ps ch))) :
    Nominal.NPrf (.imp ph (synWb (synWmo x ps) (synWmo x ch))) :=
  by
  let proofSupport : Finset Var := ph.fv ∪ ps.fv ∪ ch.fv ∪ ({ x } : Finset Var)
  have p0000 :=
    @gNfv ph x
      (by
        first
        | (aesop))
  have p0001 := @gMobid ph ps ch x p0000 hyp_mobidv_1
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_mobii`. -/
@[expose]
noncomputable def gMobii (ps : Wff) (ch : Wff) (x : Var)
    (hyp_mobii_1 : Nominal.NPrf (synWb ps ch)) :
    Nominal.NPrf (synWb (synWmo x ps) (synWmo x ch)) :=
  by
  let proofSupport : Finset Var := ps.fv ∪ ch.fv ∪ ({ x } : Finset Var)
  have p0000 := @gA1i (synWb ps ch) synWtru hyp_mobii_1
  have p0001 :=
    @gMobidv synWtru ps ch x
      (by
        first
        |
          (simp (config :=
              {
                failIfUnchanged :=
                  false }) only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wtru] at ⊢;
            aesop))
      p0000
  have p0002 := @gTrud (synWb (synWmo x ps) (synWmo x ch)) p0001
  exact p0002

/-- Checked nominal proof certificate identified upstream as `g_cbvmo`. -/
@[expose]
noncomputable def gCbvmo (ph : Wff) (ps : Wff) (x : Var) (y : Var)
    (hyp_cbvmo_1 : Nominal.NPrf (synWnf y ph))
    (hyp_cbvmo_2 : Nominal.NPrf (synWnf x ps))
    (hyp_cbvmo_3 : Nominal.NPrf (.imp (.objEq x y) (synWb ph ps))) :
    Nominal.NPrf (synWb (synWmo x ph) (synWmo y ps)) :=
  by
  have p0000 := @gCbvex ph ps x y hyp_cbvmo_1 hyp_cbvmo_2 hyp_cbvmo_3
  have p0001 := @gCbveu ph ps x y hyp_cbvmo_1 hyp_cbvmo_2 hyp_cbvmo_3
  have p0002 :=
    @gImbi12i (synWex x ph) (synWex y ps) (synWeu x ph) (synWeu y ps) p0000 p0001
  have p0003 := (Nominal.biimpRefl (synWmo x ph))
  have p0004 := (Nominal.biimpRefl (synWmo y ps))
  have p0005 :=
    @gN3bitr4i (.imp (synWex x ph) (synWeu x ph)) (.imp (synWex y ps) (synWeu y ps))
      (synWmo x ph) (synWmo y ps) p0002 p0003 p0004
  exact p0005

/-- Checked nominal proof certificate identified upstream as `g_eu5`. -/
@[expose]
noncomputable def gEu5 (ph : Wff) (x : Var) :
    Nominal.NPrf (synWb (synWeu x ph) (synWa (synWex x ph) (synWmo x ph))) :=
  by
  let proofSupport : Finset Var := ph.fv ∪ ({ x } : Finset Var)
  let y : Var := freshVar proofSupport 0
  have fresh_y : y ∉ proofSupport :=
    by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_y_not_ph : y ∉ ph.fv := by
    intro h
    exact fresh_y (Finset.mem_union_left _ (h))
  have fresh_y_ne_x : y ≠ x := by
    intro h
    exact fresh_y (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))
  have fresh_x_ne_y : x ≠ y := Ne.symm fresh_y_ne_x
  have p0000 :=
    @gNfv ph y
      (by
        first
        | (aesop))
  have p0001 :=
    @gEu3 ph x y
      (by
        first
        | (aesop))
      p0000
  have p0002 :=
    @gMo2 ph x y
      (by
        first
        | (aesop))
      p0000
  have p0003_e00_recanon :
    Nominal.NPrf
      (synWb (synWmo x ph) (synWex y (.all x (.imp ph (.classEq (.cv x) (.cv y)))))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold synWb synWmo synWex synWeu
        simp (config := { failIfUnchanged := false }) only []
        apply Nominal.RecanonTransportDev.TRecanonWff.neg
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · apply Nominal.RecanonTransportDev.TRecanonWff.imp
          · exact Nominal.RecanonTransportDev.TRecanonWff.same _
          · apply Nominal.RecanonTransportDev.TRecanonWff.neg
            apply Nominal.RecanonTransportDev.TRecanonWff.all
            apply Nominal.RecanonTransportDev.TRecanonWff.neg
            apply Nominal.RecanonTransportDev.TRecanonWff.all
            apply Nominal.RecanonTransportDev.TRecanonWff.imp
            · exact Nominal.RecanonTransportDev.TRecanonWff.same _
            · exact Nominal.RecanonTransportDev.TRecanonWff.objEq_classEq _ _
        · apply Nominal.RecanonTransportDev.TRecanonWff.neg
          apply Nominal.RecanonTransportDev.TRecanonWff.imp
          · apply Nominal.RecanonTransportDev.TRecanonWff.neg
            apply Nominal.RecanonTransportDev.TRecanonWff.all
            apply Nominal.RecanonTransportDev.TRecanonWff.neg
            apply Nominal.RecanonTransportDev.TRecanonWff.all
            apply Nominal.RecanonTransportDev.TRecanonWff.imp
            · exact Nominal.RecanonTransportDev.TRecanonWff.same _
            · exact Nominal.RecanonTransportDev.TRecanonWff.objEq_classEq _ _
          · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0002
  have p0003 :=
    @gAnbi2i (synWmo x ph) (synWex y (.all x (.imp ph (.classEq (.cv x) (.cv y)))))
      (synWex x ph) p0003_e00_recanon
  have p0004_e00_recanon :
    Nominal.NPrf
      (synWb (synWeu x ph) (synWa (synWex x ph)
          (synWex y (.all x (.imp ph (.classEq (.cv x) (.cv y))))))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold synWb synWeu synWex synWa
        simp (config := { failIfUnchanged := false }) only []
        apply Nominal.RecanonTransportDev.TRecanonWff.neg
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · apply Nominal.RecanonTransportDev.TRecanonWff.imp
          · exact Nominal.RecanonTransportDev.TRecanonWff.same _
          · apply Nominal.RecanonTransportDev.TRecanonWff.neg
            apply Nominal.RecanonTransportDev.TRecanonWff.imp
            · exact Nominal.RecanonTransportDev.TRecanonWff.same _
            · apply Nominal.RecanonTransportDev.TRecanonWff.neg
              apply Nominal.RecanonTransportDev.TRecanonWff.neg
              apply Nominal.RecanonTransportDev.TRecanonWff.all
              apply Nominal.RecanonTransportDev.TRecanonWff.neg
              apply Nominal.RecanonTransportDev.TRecanonWff.all
              apply Nominal.RecanonTransportDev.TRecanonWff.imp
              · exact Nominal.RecanonTransportDev.TRecanonWff.same _
              · exact Nominal.RecanonTransportDev.TRecanonWff.objEq_classEq _ _
        · apply Nominal.RecanonTransportDev.TRecanonWff.neg
          apply Nominal.RecanonTransportDev.TRecanonWff.imp
          · apply Nominal.RecanonTransportDev.TRecanonWff.neg
            apply Nominal.RecanonTransportDev.TRecanonWff.imp
            · exact Nominal.RecanonTransportDev.TRecanonWff.same _
            · apply Nominal.RecanonTransportDev.TRecanonWff.neg
              apply Nominal.RecanonTransportDev.TRecanonWff.neg
              apply Nominal.RecanonTransportDev.TRecanonWff.all
              apply Nominal.RecanonTransportDev.TRecanonWff.neg
              apply Nominal.RecanonTransportDev.TRecanonWff.all
              apply Nominal.RecanonTransportDev.TRecanonWff.imp
              · exact Nominal.RecanonTransportDev.TRecanonWff.same _
              · exact Nominal.RecanonTransportDev.TRecanonWff.objEq_classEq _ _
          · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0001
  have p0004 :=
    @gBitr4i (synWeu x ph)
      (synWa (synWex x ph) (synWex y (.all x (.imp ph (.classEq (.cv x) (.cv y))))))
      (synWa (synWex x ph) (synWmo x ph)) p0004_e00_recanon p0003
  exact p0004

/-- Checked nominal proof certificate identified upstream as `g_eu4`. -/
@[expose]
noncomputable def gEu4 (ph : Wff) (ps : Wff) (x : Var) (y : Var) (dv_ph_y : y ∉ ph.fv)
    (dv_ps_x : x ∉ ps.fv) (dv_x_y : x ≠ y)
    (hyp_eu4_1 : Nominal.NPrf (.imp (.objEq x y) (synWb ph ps))) :
    Nominal.NPrf
      (synWb (synWeu x ph)
        (synWa (synWex x ph) (.all x (.all y (.imp (synWa ph ps) (.objEq x y)))))) :=
  by
  let proofSupport : Finset Var :=
    ph.fv ∪ ps.fv ∪ ({ x } : Finset Var) ∪ ({ y } : Finset Var)
  have p0000 := @gEu5 ph x
  have p0001 :=
    @gMo4 ph ps x y
      (by
        first
        | (aesop))
      (by
        first
        | (aesop))
      (by
        first
        | (aesop))
      hyp_eu4_1
  have p0002 :=
    @gAnbi2i (synWmo x ph) (.all x (.all y (.imp (synWa ph ps) (.objEq x y))))
      (synWex x ph) p0001
  have p0003 :=
    @gBitri (synWeu x ph) (synWa (synWex x ph) (synWmo x ph))
      (synWa (synWex x ph) (.all x (.all y (.imp (synWa ph ps) (.objEq x y))))) p0000
      p0002
  exact p0003

/-- Checked nominal proof certificate identified upstream as `g_eumo`. -/
@[expose]
noncomputable def gEumo (ph : Wff) (x : Var) :
    Nominal.NPrf (.imp (synWeu x ph) (synWmo x ph)) :=
  by
  have p0000 := @gEu5 ph x
  have p0001 := @gSimprbi (synWeu x ph) (synWex x ph) (synWmo x ph) p0000
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_exmoeu2`. -/
@[expose]
noncomputable def gExmoeu2 (ph : Wff) (x : Var) :
    Nominal.NPrf (.imp (synWex x ph) (synWb (synWmo x ph) (synWeu x ph))) :=
  by
  have p0000 := @gEu5 ph x
  have p0001 := @gBaibr (synWeu x ph) (synWex x ph) (synWmo x ph) p0000
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_exmo`. -/
@[expose]
noncomputable def gExmo (ph : Wff) (x : Var) :
    Nominal.NPrf (synWo (synWex x ph) (synWmo x ph)) :=
  by
  have p0000 := @gPm221 (synWex x ph) (synWeu x ph)
  have p0001 := (Nominal.biimpRefl (synWmo x ph))
  have p0002 :=
    @gSylibr (.neg (synWex x ph)) (.imp (synWex x ph) (synWeu x ph)) (synWmo x ph)
      p0000 p0001
  have p0003 := @gOrri (synWex x ph) (synWmo x ph) p0002
  exact p0003

/-- Checked nominal proof certificate identified upstream as `g_moim`. -/
@[expose]
noncomputable def gMoim (ph : Wff) (ps : Wff) (x : Var) :
    Nominal.NPrf (.imp (.all x (.imp ph ps)) (.imp (synWmo x ps) (synWmo x ph))) :=
  by
  let proofSupport : Finset Var := ph.fv ∪ ps.fv ∪ ({ x } : Finset Var)
  let y : Var := freshVar proofSupport 0
  have fresh_y : y ∉ proofSupport :=
    by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_y_not_ph : y ∉ ph.fv := by
    intro h
    exact fresh_y (Finset.mem_union_left _ (Finset.mem_union_left _ (h)))
  have fresh_y_not_ps : y ∉ ps.fv := by
    intro h
    exact fresh_y (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_y_ne_x : y ≠ x := by
    intro h
    exact fresh_y (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))
  have fresh_x_ne_y : x ≠ y := Ne.symm fresh_y_ne_x
  have p0000 := @gImim1 ph ps (.classEq (.cv x) (.cv y))
  have p0001 :=
    @gAl2imi (.imp ph ps) (.imp ps (.classEq (.cv x) (.cv y)))
      (.imp ph (.classEq (.cv x) (.cv y))) x p0000
  have p0002 :=
    @gEximdv (.all x (.imp ph ps)) (.all x (.imp ps (.classEq (.cv x) (.cv y))))
      (.all x (.imp ph (.classEq (.cv x) (.cv y)))) y
      (by
        first
        |
          (simp (config :=
              { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_wff_all,
              NFChoice.Compiler.CoreFVSimp.fv_wff_imp, Finset.mem_union,
              Finset.mem_erase] at ⊢;
            aesop))
      p0001
  have p0003 :=
    @gNfv ps y
      (by
        first
        | (aesop))
  have p0004 :=
    @gMo2 ps x y
      (by
        first
        | (aesop))
      p0003
  have p0005 :=
    @gNfv ph y
      (by
        first
        | (aesop))
  have p0006 :=
    @gMo2 ph x y
      (by
        first
        | (aesop))
      p0005
  have p0007_e01_recanon :
    Nominal.NPrf
      (synWb (synWmo x ps) (synWex y (.all x (.imp ps (.classEq (.cv x) (.cv y)))))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold synWb synWmo synWex synWeu
        simp (config := { failIfUnchanged := false }) only []
        apply Nominal.RecanonTransportDev.TRecanonWff.neg
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · apply Nominal.RecanonTransportDev.TRecanonWff.imp
          · exact Nominal.RecanonTransportDev.TRecanonWff.same _
          · apply Nominal.RecanonTransportDev.TRecanonWff.neg
            apply Nominal.RecanonTransportDev.TRecanonWff.all
            apply Nominal.RecanonTransportDev.TRecanonWff.neg
            apply Nominal.RecanonTransportDev.TRecanonWff.all
            apply Nominal.RecanonTransportDev.TRecanonWff.imp
            · exact Nominal.RecanonTransportDev.TRecanonWff.same _
            · exact Nominal.RecanonTransportDev.TRecanonWff.objEq_classEq _ _
        · apply Nominal.RecanonTransportDev.TRecanonWff.neg
          apply Nominal.RecanonTransportDev.TRecanonWff.imp
          · apply Nominal.RecanonTransportDev.TRecanonWff.neg
            apply Nominal.RecanonTransportDev.TRecanonWff.all
            apply Nominal.RecanonTransportDev.TRecanonWff.neg
            apply Nominal.RecanonTransportDev.TRecanonWff.all
            apply Nominal.RecanonTransportDev.TRecanonWff.imp
            · exact Nominal.RecanonTransportDev.TRecanonWff.same _
            · exact Nominal.RecanonTransportDev.TRecanonWff.objEq_classEq _ _
          · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0004
  have p0007_e02_recanon :
    Nominal.NPrf
      (synWb (synWmo x ph) (synWex y (.all x (.imp ph (.classEq (.cv x) (.cv y)))))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold synWb synWmo synWex synWeu
        simp (config := { failIfUnchanged := false }) only []
        apply Nominal.RecanonTransportDev.TRecanonWff.neg
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · apply Nominal.RecanonTransportDev.TRecanonWff.imp
          · exact Nominal.RecanonTransportDev.TRecanonWff.same _
          · apply Nominal.RecanonTransportDev.TRecanonWff.neg
            apply Nominal.RecanonTransportDev.TRecanonWff.all
            apply Nominal.RecanonTransportDev.TRecanonWff.neg
            apply Nominal.RecanonTransportDev.TRecanonWff.all
            apply Nominal.RecanonTransportDev.TRecanonWff.imp
            · exact Nominal.RecanonTransportDev.TRecanonWff.same _
            · exact Nominal.RecanonTransportDev.TRecanonWff.objEq_classEq _ _
        · apply Nominal.RecanonTransportDev.TRecanonWff.neg
          apply Nominal.RecanonTransportDev.TRecanonWff.imp
          · apply Nominal.RecanonTransportDev.TRecanonWff.neg
            apply Nominal.RecanonTransportDev.TRecanonWff.all
            apply Nominal.RecanonTransportDev.TRecanonWff.neg
            apply Nominal.RecanonTransportDev.TRecanonWff.all
            apply Nominal.RecanonTransportDev.TRecanonWff.imp
            · exact Nominal.RecanonTransportDev.TRecanonWff.same _
            · exact Nominal.RecanonTransportDev.TRecanonWff.objEq_classEq _ _
          · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0006
  have p0007 :=
    @gN3imtr4g (.all x (.imp ph ps))
      (synWex y (.all x (.imp ps (.classEq (.cv x) (.cv y)))))
      (synWex y (.all x (.imp ph (.classEq (.cv x) (.cv y))))) (synWmo x ps)
      (synWmo x ph) p0002 p0007_e01_recanon p0007_e02_recanon
  exact p0007

/-- Checked nominal proof certificate identified upstream as `g_moanim`. -/
@[expose]
noncomputable def gMoanim (ph : Wff) (ps : Wff) (x : Var)
    (hyp_moanim_1 : Nominal.NPrf (synWnf x ph)) :
    Nominal.NPrf (synWb (synWmo x (synWa ph ps)) (.imp ph (synWmo x ps))) :=
  by
  let proofSupport : Finset Var := ph.fv ∪ ps.fv ∪ ({ x } : Finset Var)
  let y : Var := freshVar proofSupport 0
  have fresh_y : y ∉ proofSupport :=
    by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_y_not_ph : y ∉ ph.fv := by
    intro h
    exact fresh_y (Finset.mem_union_left _ (Finset.mem_union_left _ (h)))
  have fresh_y_not_ps : y ∉ ps.fv := by
    intro h
    exact fresh_y (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_y_ne_x : y ≠ x := by
    intro h
    exact fresh_y (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))
  have fresh_x_ne_y : x ≠ y := Ne.symm fresh_y_ne_x
  have p0000 := @gImpexp ph ps (.objEq x y)
  have p0001 :=
    @gAlbii (.imp (synWa ph ps) (.objEq x y)) (.imp ph (.imp ps (.objEq x y))) x p0000
  have p0002 := @gN1921 ph (.imp ps (.objEq x y)) x hyp_moanim_1
  have p0003 :=
    @gBitri (.all x (.imp (synWa ph ps) (.objEq x y)))
      (.all x (.imp ph (.imp ps (.objEq x y)))) (.imp ph (.all x (.imp ps (.objEq x y))))
      p0001 p0002
  have p0004 :=
    @gExbii (.all x (.imp (synWa ph ps) (.objEq x y)))
      (.imp ph (.all x (.imp ps (.objEq x y)))) y p0003
  have p0005 :=
    @gNfv (synWa ph ps) y
      (by
        first
        |
          (simp (config :=
              {
                failIfUnchanged :=
                  false }) only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
              Finset.mem_union] at ⊢;
            aesop))
  have p0006 :=
    @gMo2 (synWa ph ps) x y
      (by
        first
        | (aesop))
      p0005
  have p0007 :=
    @gNfv ps y
      (by
        first
        | (aesop))
  have p0008 :=
    @gMo2 ps x y
      (by
        first
        | (aesop))
      p0007
  have p0009 :=
    @gImbi2i (synWmo x ps) (synWex y (.all x (.imp ps (.objEq x y)))) ph p0008
  have p0010 :=
    @gN1937v ph (.all x (.imp ps (.objEq x y))) y
      (by
        first
        | (aesop))
  have p0011 :=
    @gBitr4i (.imp ph (synWmo x ps))
      (.imp ph (synWex y (.all x (.imp ps (.objEq x y)))))
      (synWex y (.imp ph (.all x (.imp ps (.objEq x y))))) p0009 p0010
  have p0012 :=
    @gN3bitr4i (synWex y (.all x (.imp (synWa ph ps) (.objEq x y))))
      (synWex y (.imp ph (.all x (.imp ps (.objEq x y))))) (synWmo x (synWa ph ps))
      (.imp ph (synWmo x ps)) p0004 p0006 p0011
  exact p0012

/-- Checked nominal proof certificate identified upstream as `g_euan`. -/
@[expose]
noncomputable def gEuan (ph : Wff) (ps : Wff) (x : Var)
    (hyp_moanim_1 : Nominal.NPrf (synWnf x ph)) :
    Nominal.NPrf (synWb (synWeu x (synWa ph ps)) (synWa ph (synWeu x ps))) :=
  by
  have p0000 := @gSimpl ph ps
  have p0001 := @gExlimi (synWa ph ps) ph x hyp_moanim_1 p0000
  have p0002 := @gAdantr (synWex x (synWa ph ps)) ph (synWmo x (synWa ph ps)) p0001
  have p0003 := @gSimpr ph ps
  have p0004 := @gEximi (synWa ph ps) ps x p0003
  have p0005 :=
    @gAdantr (synWex x (synWa ph ps)) (synWex x ps) (synWmo x (synWa ph ps)) p0004
  have p0006 := @gNfe1 (synWa ph ps) x
  have p0007 := @gA1d (synWex x (synWa ph ps)) ph ps p0001
  have p0008 := @gAncrd (synWex x (synWa ph ps)) ps ph p0007
  have p0009 := @gImpbid2 (synWex x (synWa ph ps)) (synWa ph ps) ps p0003 p0008
  have p0010 := @gMobid (synWex x (synWa ph ps)) (synWa ph ps) ps x p0006 p0009
  have p0011 :=
    @gBiimpa (synWex x (synWa ph ps)) (synWmo x (synWa ph ps)) (synWmo x ps) p0010
  have p0012 :=
    @gJca32 (synWa (synWex x (synWa ph ps)) (synWmo x (synWa ph ps))) ph
      (synWex x ps) (synWmo x ps) p0002 p0005 p0011
  have p0013 := @gEu5 (synWa ph ps) x
  have p0014 := @gEu5 ps x
  have p0015 := @gAnbi2i (synWeu x ps) (synWa (synWex x ps) (synWmo x ps)) ph p0014
  have p0016 :=
    @gN3imtr4i (synWa (synWex x (synWa ph ps)) (synWmo x (synWa ph ps)))
      (synWa ph (synWa (synWex x ps) (synWmo x ps))) (synWeu x (synWa ph ps))
      (synWa ph (synWeu x ps)) p0012 p0013 p0015
  have p0017 := @gIbar ph ps
  have p0018 := @gEubid ph ps (synWa ph ps) x hyp_moanim_1 p0017
  have p0019 := @gBiimpa ph (synWeu x ps) (synWeu x (synWa ph ps)) p0018
  have p0020 :=
    @gImpbii (synWeu x (synWa ph ps)) (synWa ph (synWeu x ps)) p0016 p0019
  exact p0020

/-- Checked nominal proof certificate identified upstream as `g_moanimv`. -/
@[expose]
noncomputable def gMoanimv (ph : Wff) (ps : Wff) (x : Var) (dv_ph_x : x ∉ ph.fv) :
    Nominal.NPrf (synWb (synWmo x (synWa ph ps)) (.imp ph (synWmo x ps))) :=
  by
  let proofSupport : Finset Var := ph.fv ∪ ps.fv ∪ ({ x } : Finset Var)
  have p0000 :=
    @gNfv ph x
      (by
        first
        | (aesop))
  have p0001 := @gMoanim ph ps x p0000
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_euanv`. -/
@[expose]
noncomputable def gEuanv (ph : Wff) (ps : Wff) (x : Var) (dv_ph_x : x ∉ ph.fv) :
    Nominal.NPrf (synWb (synWeu x (synWa ph ps)) (synWa ph (synWeu x ps))) :=
  by
  let proofSupport : Finset Var := ph.fv ∪ ps.fv ∪ ({ x } : Finset Var)
  have p0000 :=
    @gNfv ph x
      (by
        first
        | (aesop))
  have p0001 := @gEuan ph ps x p0000
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_mopick`. -/
@[expose]
noncomputable def gMopick (ph : Wff) (ps : Wff) (x : Var) :
    Nominal.NPrf (.imp (synWa (synWmo x ph) (synWex x (synWa ph ps))) (.imp ph ps)) :=
  by
  let proofSupport : Finset Var := ph.fv ∪ ps.fv ∪ ({ x } : Finset Var)
  let y : Var := freshVar proofSupport 0
  have fresh_y : y ∉ proofSupport :=
    by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_y_not_ph : y ∉ ph.fv := by
    intro h
    exact fresh_y (Finset.mem_union_left _ (Finset.mem_union_left _ (h)))
  have fresh_y_not_ps : y ∉ ps.fv := by
    intro h
    exact fresh_y (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_y_ne_x : y ≠ x := by
    intro h
    exact fresh_y (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))
  have fresh_x_ne_y : x ≠ y := Ne.symm fresh_y_ne_x
  have p0000 :=
    @gNfv (synWa ph ps) y
      (by
        first
        |
          (simp (config :=
              {
                failIfUnchanged :=
                  false }) only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
              Finset.mem_union] at ⊢;
            aesop))
  have p0001 :=
    @gNfs1v ph x y
      (by
        first
        | (aesop))
  have p0002 :=
    @gNfs1v ps x y
      (by
        first
        | (aesop))
  have p0003 := @gNfan (synWsb y x ph) (synWsb y x ps) x p0001 p0002
  have p0004 := @gSbequ12 ph x y
  have p0005 := @gSbequ12 ps x y
  have p0006_e00_recanon :
    Nominal.NPrf (.imp (.classEq (.cv x) (.cv y)) (synWb ph (synWsb y x ph))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold synWb synWsb synWa synWex
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · exact Nominal.RecanonTransportDev.TRecanonWff.objEq_classEq _ _
        · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0004
  have p0006_e01_recanon :
    Nominal.NPrf (.imp (.classEq (.cv x) (.cv y)) (synWb ps (synWsb y x ps))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold synWb synWsb synWa synWex
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · exact Nominal.RecanonTransportDev.TRecanonWff.objEq_classEq _ _
        · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0005
  have p0006 :=
    @gAnbi12d (.classEq (.cv x) (.cv y)) ph (synWsb y x ph) ps (synWsb y x ps)
      p0006_e00_recanon p0006_e01_recanon
  have p0007_e02_recanon :
    Nominal.NPrf
      (.imp (.objEq x y) (synWb (synWa ph ps) (synWa (synWsb y x ph) (synWsb y x ps)))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold synWb synWa
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
        · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0006
  have p0007 :=
    @gCbvex (synWa ph ps) (synWa (synWsb y x ph) (synWsb y x ps)) x y p0000 p0003
      p0007_e02_recanon
  have p0008 :=
    @gNfv ph y
      (by
        first
        | (aesop))
  have p0009 :=
    @gMo3 ph x y
      (by
        first
        | (aesop))
      p0008
  have p0010 := @gSp (.imp (synWa ph (synWsb y x ph)) (.classEq (.cv x) (.cv y))) y
  have p0011 :=
    @gSps (.all y (.imp (synWa ph (synWsb y x ph)) (.classEq (.cv x) (.cv y))))
      (.imp (synWa ph (synWsb y x ph)) (.classEq (.cv x) (.cv y))) x p0010
  have p0012_e00_recanon :
    Nominal.NPrf
      (synWb (synWmo x ph) (.all x
          (.all y (.imp (synWa ph (synWsb y x ph)) (.classEq (.cv x) (.cv y)))))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold synWb synWmo synWex synWeu synWa synWsb
        simp (config := { failIfUnchanged := false }) only []
        apply Nominal.RecanonTransportDev.TRecanonWff.neg
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · apply Nominal.RecanonTransportDev.TRecanonWff.imp
          · exact Nominal.RecanonTransportDev.TRecanonWff.same _
          · apply Nominal.RecanonTransportDev.TRecanonWff.all
            apply Nominal.RecanonTransportDev.TRecanonWff.all
            apply Nominal.RecanonTransportDev.TRecanonWff.imp
            · exact Nominal.RecanonTransportDev.TRecanonWff.same _
            · exact Nominal.RecanonTransportDev.TRecanonWff.objEq_classEq _ _
        · apply Nominal.RecanonTransportDev.TRecanonWff.neg
          apply Nominal.RecanonTransportDev.TRecanonWff.imp
          · apply Nominal.RecanonTransportDev.TRecanonWff.all
            apply Nominal.RecanonTransportDev.TRecanonWff.all
            apply Nominal.RecanonTransportDev.TRecanonWff.imp
            · exact Nominal.RecanonTransportDev.TRecanonWff.same _
            · exact Nominal.RecanonTransportDev.TRecanonWff.objEq_classEq _ _
          · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0009
  have p0012 :=
    @gSylbi (synWmo x ph)
      (.all x (.all y (.imp (synWa ph (synWsb y x ph)) (.classEq (.cv x) (.cv y)))))
      (.imp (synWa ph (synWsb y x ph)) (.classEq (.cv x) (.cv y))) p0012_e00_recanon
      p0011
  have p0013 := @gSbequ2 ps x y
  have p0014_e00_recanon :
    Nominal.NPrf (.imp (.classEq (.cv x) (.cv y)) (.imp (synWsb y x ps) ps)) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold synWsb synWa synWex
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · exact Nominal.RecanonTransportDev.TRecanonWff.objEq_classEq _ _
        · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0013
  have p0014 :=
    @gImim2i (.classEq (.cv x) (.cv y)) (.imp (synWsb y x ps) ps)
      (synWa ph (synWsb y x ph)) p0014_e00_recanon
  have p0015 :=
    @gExp3a (.imp (synWa ph (synWsb y x ph)) (.classEq (.cv x) (.cv y))) ph
      (synWsb y x ph) (.imp (synWsb y x ps) ps) p0014
  have p0016 :=
    @gCom4t (.imp (synWa ph (synWsb y x ph)) (.classEq (.cv x) (.cv y))) ph
      (synWsb y x ph) (synWsb y x ps) ps p0015
  have p0017 :=
    @gImp (synWsb y x ph) (synWsb y x ps)
      (.imp (.imp (synWa ph (synWsb y x ph)) (.classEq (.cv x) (.cv y))) (.imp ph ps))
      p0016
  have p0018 :=
    @gSyl5 (synWmo x ph) (.imp (synWa ph (synWsb y x ph)) (.classEq (.cv x) (.cv y)))
      (synWa (synWsb y x ph) (synWsb y x ps)) (.imp ph ps) p0012 p0017
  have p0019 :=
    @gExlimiv (synWa (synWsb y x ph) (synWsb y x ps))
      (.imp (synWmo x ph) (.imp ph ps)) y
      (by
        first
        |
          (simp (config :=
              { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp,
              NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wmo, Finset.mem_union,
              Finset.mem_erase] at ⊢;
            aesop))
      p0018
  have p0020 :=
    @gSylbi (synWex x (synWa ph ps))
      (synWex y (synWa (synWsb y x ph) (synWsb y x ps)))
      (.imp (synWmo x ph) (.imp ph ps)) p0007 p0019
  have p0021 := @gImpcom (synWex x (synWa ph ps)) (synWmo x ph) (.imp ph ps) p0020
  exact p0021

/-- Checked nominal proof certificate identified upstream as `g_eupick`. -/
@[expose]
noncomputable def gEupick (ph : Wff) (ps : Wff) (x : Var) :
    Nominal.NPrf (.imp (synWa (synWeu x ph) (synWex x (synWa ph ps))) (.imp ph ps)) :=
  by
  have p0000 := @gEumo ph x
  have p0001 := @gMopick ph ps x
  have p0002 :=
    @gSylan (synWeu x ph) (synWmo x ph) (synWex x (synWa ph ps)) (.imp ph ps) p0000
      p0001
  exact p0002

/-- Checked nominal proof certificate identified upstream as `g_moexex`. -/
@[expose]
noncomputable def gMoexex (ph : Wff) (ps : Wff) (x : Var) (y : Var)
    (hyp_moexex_1 : Nominal.NPrf (synWnf y ph)) :
    Nominal.NPrf
      (.imp (synWa (synWmo x ph) (.all x (synWmo y ps)))
        (synWmo y (synWex x (synWa ph ps)))) :=
  by
  have p0000 := @gNfmo1 ph x
  have p0001 := @gNfa1 (synWmo y ps) x
  have p0002 := @gNfe1 (synWa ph ps) x
  have p0003 := @gNfmo (synWex x (synWa ph ps)) x y p0002
  have p0004 :=
    @gNfim (.all x (synWmo y ps)) (synWmo y (synWex x (synWa ph ps))) x p0001 p0003
  have p0005 :=
    @gNfim (synWmo x ph)
      (.imp (.all x (synWmo y ps)) (synWmo y (synWex x (synWa ph ps)))) x p0000 p0004
  have p0006 := @gNfmo ph y x hyp_moexex_1
  have p0007 := @gMopick ph ps x
  have p0008 := @gEx (synWmo x ph) (synWex x (synWa ph ps)) (.imp ph ps) p0007
  have p0009 := @gCom3r (synWmo x ph) (synWex x (synWa ph ps)) ph ps p0008
  have p0010 :=
    @gAlrimd ph (synWmo x ph) (.imp (synWex x (synWa ph ps)) ps) y hyp_moexex_1 p0006
      p0009
  have p0011 := @gMoim (synWex x (synWa ph ps)) ps y
  have p0012 :=
    @gSpsd (.all y (.imp (synWex x (synWa ph ps)) ps)) (synWmo y ps)
      (synWmo y (synWex x (synWa ph ps))) x p0011
  have p0013 :=
    @gSyl6 ph (synWmo x ph) (.all y (.imp (synWex x (synWa ph ps)) ps))
      (.imp (.all x (synWmo y ps)) (synWmo y (synWex x (synWa ph ps)))) p0010 p0012
  have p0014 :=
    @gExlimi ph
      (.imp (synWmo x ph)
        (.imp (.all x (synWmo y ps)) (synWmo y (synWex x (synWa ph ps)))))
      x p0005 p0013
  have p0015 := @gNfex ph y x hyp_moexex_1
  have p0016 := @gExsimpl ph ps x
  have p0017 := @gExlimi (synWex x (synWa ph ps)) (synWex x ph) y p0015 p0016
  have p0018 := @gCon3i (synWex y (synWex x (synWa ph ps))) (synWex x ph) p0017
  have p0019 := @gExmo (synWex x (synWa ph ps)) y
  have p0020 :=
    @gOri (synWex y (synWex x (synWa ph ps))) (synWmo y (synWex x (synWa ph ps)))
      p0019
  have p0021 :=
    @gSyl (.neg (synWex x ph)) (.neg (synWex y (synWex x (synWa ph ps))))
      (synWmo y (synWex x (synWa ph ps))) p0018 p0020
  have p0022 :=
    @gA1d (.neg (synWex x ph)) (synWmo y (synWex x (synWa ph ps)))
      (.all x (synWmo y ps)) p0021
  have p0023 :=
    @gA1d (.neg (synWex x ph))
      (.imp (.all x (synWmo y ps)) (synWmo y (synWex x (synWa ph ps)))) (synWmo x ph)
      p0022
  have p0024 :=
    @gPm261i (synWex x ph)
      (.imp (synWmo x ph)
        (.imp (.all x (synWmo y ps)) (synWmo y (synWex x (synWa ph ps)))))
      p0014 p0023
  have p0025 :=
    @gImp (synWmo x ph) (.all x (synWmo y ps)) (synWmo y (synWex x (synWa ph ps)))
      p0024
  exact p0025

/-- Checked nominal proof certificate identified upstream as `g_moexexv`. -/
@[expose]
noncomputable def gMoexexv (ph : Wff) (ps : Wff) (x : Var) (y : Var)
    (dv_ph_y : y ∉ ph.fv) :
    Nominal.NPrf
      (.imp (synWa (synWmo x ph) (.all x (synWmo y ps)))
        (synWmo y (synWex x (synWa ph ps)))) :=
  by
  let proofSupport : Finset Var :=
    ph.fv ∪ ps.fv ∪ ({ x } : Finset Var) ∪ ({ y } : Finset Var)
  have p0000 :=
    @gNfv ph y
      (by
        first
        | (aesop))
  have p0001 := @gMoexex ph ps x y p0000
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_euequ1`. -/
@[expose]
noncomputable def gEuequ1 (x : Var) (y : Var) (dv_x_y : x ≠ y) :
    Nominal.NPrf (synWeu x (.objEq x y)) :=
  by
  let proofSupport : Finset Var := ({ x } : Finset Var) ∪ ({ y } : Finset Var)
  let z : Var := freshVar proofSupport 0
  have fresh_z : z ∉ proofSupport :=
    by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_z_ne_x : z ≠ x := by
    intro h
    exact fresh_z (Finset.mem_union_left _ (Finset.mem_singleton.mpr h))
  have fresh_x_ne_z : x ≠ z := Ne.symm fresh_z_ne_x
  have fresh_z_ne_y : z ≠ y := by
    intro h
    exact fresh_z (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))
  have fresh_y_ne_z : y ≠ z := Ne.symm fresh_z_ne_y
  have p0000 :=
    @gA9ev x y
      (by
        first
        | (aesop))
  have p0001 := @gEqutr2 x z y
  have p0002 := @gGen2 (.imp (synWa (.objEq x y) (.objEq z y)) (.objEq x z)) x z p0001
  have p0003 := @gEquequ1 x z y
  have p0004 :=
    @gEu4 (.objEq x y) (.objEq z y) x z
      (by
        first
        |
          (simp (config :=
              {
                failIfUnchanged :=
                  false }) only [NFChoice.Compiler.CoreFVSimp.fv_wff_objEq] at ⊢;
            aesop))
      (by
        first
        |
          (simp (config :=
              {
                failIfUnchanged :=
                  false }) only [NFChoice.Compiler.CoreFVSimp.fv_wff_objEq] at ⊢;
            aesop))
      (by
        first
        | (aesop))
      p0003
  have p0005 :=
    @gMpbir2an (synWeu x (.objEq x y)) (synWex x (.objEq x y))
      (.all x (.all z (.imp (synWa (.objEq x y) (.objEq z y)) (.objEq x z)))) p0000 p0002
      p0004
  exact p0005

/-- Checked nominal proof certificate identified upstream as `g_abid`. -/
@[expose]
noncomputable def gAbid (ph : Wff) (x : Var) :
    Nominal.NPrf (synWb (.classMem (.cv x) (.cab x ph)) ph) :=
  by
  have p0000 :=
    (NFChoice.DirectNominalPrf.Nominal.DefinitionLeafHandlersCanonical001.dfClabStructural
      x x ph)
  have p0001 := @gSbid ph x
  have p0002 := @gBitri (.classMem (.cv x) (.cab x ph)) (synWsb x x ph) ph p0000 p0001
  exact p0002

/-- Checked nominal proof certificate identified upstream as `g_hbab1`. -/
@[expose]
noncomputable def gHbab1 (ph : Wff) (x : Var) (y : Var) (dv_x_y : x ≠ y) :
    Nominal.NPrf
      (.imp (.classMem (.cv y) (.cab x ph)) (.all x (.classMem (.cv y) (.cab x ph)))) :=
  by
  let proofSupport : Finset Var := ph.fv ∪ ({ x } : Finset Var) ∪ ({ y } : Finset Var)
  have p0000 :=
    (NFChoice.DirectNominalPrf.Nominal.DefinitionLeafHandlersCanonical001.dfClabStructural
      y x ph)
  have p0001 :=
    @gHbs1 ph x y
      (by
        first
        | (aesop))
  have p0002 := @gHbxfrbi (.classMem (.cv y) (.cab x ph)) (synWsb y x ph) x p0000 p0001
  exact p0002

/-- Checked nominal proof certificate identified upstream as `g_nfsab1`. -/
@[expose]
noncomputable def gNfsab1 (ph : Wff) (x : Var) (y : Var) (dv_x_y : x ≠ y) :
    Nominal.NPrf (synWnf x (.classMem (.cv y) (.cab x ph))) :=
  by
  let proofSupport : Finset Var := ph.fv ∪ ({ x } : Finset Var) ∪ ({ y } : Finset Var)
  have p0000 :=
    @gHbab1 ph x y
      (by
        first
        | (aesop))
  have p0001 := @gNfi (.classMem (.cv y) (.cab x ph)) x p0000
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_hbab`. -/
@[expose]
noncomputable def gHbab (ph : Wff) (x : Var) (y : Var) (z : Var) (dv_x_z : x ≠ z)
    (hyp_hbab_1 : Nominal.NPrf (.imp ph (.all x ph))) :
    Nominal.NPrf
      (.imp (.classMem (.cv z) (.cab y ph)) (.all x (.classMem (.cv z) (.cab y ph)))) :=
  by
  let proofSupport : Finset Var :=
    ph.fv ∪ ({ x } : Finset Var) ∪ ({ y } : Finset Var) ∪ ({ z } : Finset Var)
  have p0000 :=
    (NFChoice.DirectNominalPrf.Nominal.DefinitionLeafHandlersCanonical001.dfClabStructural
      z y ph)
  have p0001 :=
    @gHbsb ph y z x
      (by
        first
        | (aesop))
      hyp_hbab_1
  have p0002 := @gHbxfrbi (.classMem (.cv z) (.cab y ph)) (synWsb z y ph) x p0000 p0001
  exact p0002

/-- Checked nominal proof certificate identified upstream as `g_nfsab`. -/
@[expose]
noncomputable def gNfsab (ph : Wff) (x : Var) (y : Var) (z : Var) (dv_x_z : x ≠ z)
    (hyp_nfsab_1 : Nominal.NPrf (synWnf x ph)) :
    Nominal.NPrf (synWnf x (.classMem (.cv z) (.cab y ph))) :=
  by
  let proofSupport : Finset Var :=
    ph.fv ∪ ({ x } : Finset Var) ∪ ({ y } : Finset Var) ∪ ({ z } : Finset Var)
  have p0000 := @gNfri ph x hyp_nfsab_1
  have p0001 :=
    @gHbab ph x y z
      (by
        first
        | (aesop))
      p0000
  have p0002 := @gNfi (.classMem (.cv z) (.cab y ph)) x p0001
  exact p0002

/-- Checked nominal proof certificate identified upstream as `g_dfcleq`. -/
@[expose]
noncomputable def gDfcleq (x : Var) (A : Class) (B : Class) (dv_A_x : x ∉ A.fv)
    (dv_B_x : x ∉ B.fv) :
    Nominal.NPrf
      (synWb (.classEq A B) (.all x (synWb (.classMem (.cv x) A) (.classMem (.cv x) B)))) :=
  by
  let proofSupport : Finset Var := ({ x } : Finset Var) ∪ A.fv ∪ B.fv
  let y : Var := freshVar proofSupport 0
  let z : Var := freshVar proofSupport 1
  have fresh_y : y ∉ proofSupport :=
    by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_y_ne_x : y ≠ x := by
    intro h
    exact
      fresh_y
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_singleton.mpr h)))
  have fresh_x_ne_y : x ≠ y := Ne.symm fresh_y_ne_x
  have fresh_y_not_A : y ∉ A.fv := by
    intro h
    exact fresh_y (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_y_not_B : y ∉ B.fv := by
    intro h
    exact fresh_y (Finset.mem_union_right _ (h))
  have fresh_z : z ∉ proofSupport :=
    by
    change freshVar proofSupport 1 ∉ proofSupport
    exact freshVar_not_mem proofSupport 1
  have fresh_z_ne_x : z ≠ x := by
    intro h
    exact
      fresh_z
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_singleton.mpr h)))
  have fresh_x_ne_z : x ≠ z := Ne.symm fresh_z_ne_x
  have fresh_z_not_A : z ∉ A.fv := by
    intro h
    exact fresh_z (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_z_not_B : z ∉ B.fv := by
    intro h
    exact fresh_z (Finset.mem_union_right _ (h))
  have fresh_y_ne_z : y ≠ z :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have fresh_z_ne_y : z ≠ y := Ne.symm fresh_y_ne_z
  have p0000 :=
    NFChoice.DirectNominalPrf.Nominal.NFLiteralBaseFour.axExt y z x
      (by
        first
        | (aesop))
      (by
        first
        | (aesop))
      (by
        first
        | (aesop))
  have p0001 :=
    (NFChoice.DirectNominalPrf.Nominal.DefinitionLeafHandlersObjExtCompat001.dfCleqOfDVObjExt
      x y z A B p0000 (by
        first
        | (aesop)) (by
        first
        | (aesop)))
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_eqriv`. -/
@[expose]
noncomputable def gEqriv (x : Var) (A : Class) (B : Class) (dv_A_x : x ∉ A.fv)
    (dv_B_x : x ∉ B.fv)
    (hyp_eqriv_1 : Nominal.NPrf (synWb (.classMem (.cv x) A) (.classMem (.cv x) B))) :
    Nominal.NPrf (.classEq A B) :=
  by
  let proofSupport : Finset Var := ({ x } : Finset Var) ∪ A.fv ∪ B.fv
  have p0000 :=
    @gDfcleq x A B
      (by
        first
        | (aesop))
      (by
        first
        | (aesop))
  have p0001 :=
    @gMpgbir (.classEq A B) (synWb (.classMem (.cv x) A) (.classMem (.cv x) B)) x p0000
      hyp_eqriv_1
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_eqrdv`. -/
@[expose]
noncomputable def gEqrdv (ph : Wff) (x : Var) (A : Class) (B : Class) (dv_A_x : x ∉ A.fv)
    (dv_B_x : x ∉ B.fv) (dv_ph_x : x ∉ ph.fv)
    (hyp_eqrdv_1 :
      Nominal.NPrf (.imp ph (synWb (.classMem (.cv x) A) (.classMem (.cv x) B)))) :
    Nominal.NPrf (.imp ph (.classEq A B)) :=
  by
  let proofSupport : Finset Var := ph.fv ∪ ({ x } : Finset Var) ∪ A.fv ∪ B.fv
  have p0000 :=
    @gAlrimiv ph (synWb (.classMem (.cv x) A) (.classMem (.cv x) B)) x
      (by
        first
        | (aesop))
      hyp_eqrdv_1
  have p0001 :=
    @gDfcleq x A B
      (by
        first
        | (aesop))
      (by
        first
        | (aesop))
  have p0002 :=
    @gSylibr ph (.all x (synWb (.classMem (.cv x) A) (.classMem (.cv x) B)))
      (.classEq A B) p0000 p0001
  exact p0002

/-- Checked nominal proof certificate identified upstream as `g_eqid`. -/
@[expose]
noncomputable def gEqid (A : Class) : Nominal.NPrf (.classEq A A) :=
  by
  let proofSupport : Finset Var := A.fv
  let x : Var := freshVar proofSupport 0
  have fresh_x : x ∉ proofSupport :=
    by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_x_not_A : x ∉ A.fv := by
    intro h
    exact fresh_x (h)
  have p0000 := @gBiid (.classMem (.cv x) A)
  have p0001 :=
    @gEqriv x A A
      (by
        first
        | (aesop))
      (by
        first
        | (aesop))
      p0000
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_eqidd`. -/
@[expose]
noncomputable def gEqidd (ph : Wff) (A : Class) :
    Nominal.NPrf (.imp ph (.classEq A A)) :=
  by
  have p0000 := @gEqid A
  have p0001 := @gA1i (.classEq A A) ph p0000
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_eqcom`. -/
@[expose]
noncomputable def gEqcom (A : Class) (B : Class) :
    Nominal.NPrf (synWb (.classEq A B) (.classEq B A)) :=
  by
  let proofSupport : Finset Var := A.fv ∪ B.fv
  let x : Var := freshVar proofSupport 0
  have fresh_x : x ∉ proofSupport :=
    by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_x_not_A : x ∉ A.fv := by
    intro h
    exact fresh_x (Finset.mem_union_left _ (h))
  have fresh_x_not_B : x ∉ B.fv := by
    intro h
    exact fresh_x (Finset.mem_union_right _ (h))
  have p0000 := @gBicom (.classMem (.cv x) A) (.classMem (.cv x) B)
  have p0001 :=
    @gAlbii (synWb (.classMem (.cv x) A) (.classMem (.cv x) B))
      (synWb (.classMem (.cv x) B) (.classMem (.cv x) A)) x p0000
  have p0002 :=
    @gDfcleq x A B
      (by
        first
        | (aesop))
      (by
        first
        | (aesop))
  have p0003 :=
    @gDfcleq x B A
      (by
        first
        | (aesop))
      (by
        first
        | (aesop))
  have p0004 :=
    @gN3bitr4i (.all x (synWb (.classMem (.cv x) A) (.classMem (.cv x) B)))
      (.all x (synWb (.classMem (.cv x) B) (.classMem (.cv x) A))) (.classEq A B)
      (.classEq B A) p0001 p0002 p0003
  exact p0004

/-- Checked nominal proof certificate identified upstream as `g_eqcoms`. -/
@[expose]
noncomputable def gEqcoms (ph : Wff) (A : Class) (B : Class)
    (hyp_eqcoms_1 : Nominal.NPrf (.imp (.classEq A B) ph)) :
    Nominal.NPrf (.imp (.classEq B A) ph) :=
  by
  have p0000 := @gEqcom B A
  have p0001 := @gSylbi (.classEq B A) (.classEq A B) ph p0000 hyp_eqcoms_1
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_eqcomi`. -/
@[expose]
noncomputable def gEqcomi (A : Class) (B : Class)
    (hyp_eqcomi_1 : Nominal.NPrf (.classEq A B)) : Nominal.NPrf (.classEq B A) :=
  by
  have p0000 := @gEqcom A B
  have p0001 := @gMpbi (.classEq A B) (.classEq B A) hyp_eqcomi_1 p0000
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_eqcomd`. -/
@[expose]
noncomputable def gEqcomd (ph : Wff) (A : Class) (B : Class)
    (hyp_eqcomd_1 : Nominal.NPrf (.imp ph (.classEq A B))) :
    Nominal.NPrf (.imp ph (.classEq B A)) :=
  by
  have p0000 := @gEqcom A B
  have p0001 := @gSylib ph (.classEq A B) (.classEq B A) hyp_eqcomd_1 p0000
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_eqeq1`. -/
@[expose]
noncomputable def gEqeq1 (A : Class) (B : Class) (C : Class) :
    Nominal.NPrf (.imp (.classEq A B) (synWb (.classEq A C) (.classEq B C))) :=
  by
  let proofSupport : Finset Var := A.fv ∪ B.fv ∪ C.fv
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
  have fresh_x_not_C : x ∉ C.fv := by
    intro h
    exact fresh_x (Finset.mem_union_right _ (h))
  have p0000 :=
    @gDfcleq x A B
      (by
        first
        | (aesop))
      (by
        first
        | (aesop))
  have p0001 :=
    @gBiimpi (.classEq A B) (.all x (synWb (.classMem (.cv x) A) (.classMem (.cv x) B)))
      p0000
  have p0002 :=
    @gN1921bi (.classEq A B) (synWb (.classMem (.cv x) A) (.classMem (.cv x) B)) x
      p0001
  have p0003 :=
    @gBibi1d (.classEq A B) (.classMem (.cv x) A) (.classMem (.cv x) B)
      (.classMem (.cv x) C) p0002
  have p0004 :=
    @gAlbidv (.classEq A B) (synWb (.classMem (.cv x) A) (.classMem (.cv x) C))
      (synWb (.classMem (.cv x) B) (.classMem (.cv x) C)) x
      (by
        first
        |
          (simp (config :=
              {
                failIfUnchanged :=
                  false }) only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
              Finset.mem_union] at ⊢;
            aesop))
      p0003
  have p0005 :=
    @gDfcleq x A C
      (by
        first
        | (aesop))
      (by
        first
        | (aesop))
  have p0006 :=
    @gDfcleq x B C
      (by
        first
        | (aesop))
      (by
        first
        | (aesop))
  have p0007 :=
    @gN3bitr4g (.classEq A B)
      (.all x (synWb (.classMem (.cv x) A) (.classMem (.cv x) C)))
      (.all x (synWb (.classMem (.cv x) B) (.classMem (.cv x) C))) (.classEq A C)
      (.classEq B C) p0004 p0005 p0006
  exact p0007

/-- Checked nominal proof certificate identified upstream as `g_eqeq1i`. -/
@[expose]
noncomputable def gEqeq1i (A : Class) (B : Class) (C : Class)
    (hyp_eqeq1i_1 : Nominal.NPrf (.classEq A B)) :
    Nominal.NPrf (synWb (.classEq A C) (.classEq B C)) :=
  by
  have p0000 := @gEqeq1 A B C
  have p0001 := Nominal.mp hyp_eqeq1i_1 p0000
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_eqeq1d`. -/
@[expose]
noncomputable def gEqeq1d (ph : Wff) (A : Class) (B : Class) (C : Class)
    (hyp_eqeq1d_1 : Nominal.NPrf (.imp ph (.classEq A B))) :
    Nominal.NPrf (.imp ph (synWb (.classEq A C) (.classEq B C))) :=
  by
  have p0000 := @gEqeq1 A B C
  have p0001 :=
    @gSyl ph (.classEq A B) (synWb (.classEq A C) (.classEq B C)) hyp_eqeq1d_1 p0000
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_eqeq2`. -/
@[expose]
noncomputable def gEqeq2 (A : Class) (B : Class) (C : Class) :
    Nominal.NPrf (.imp (.classEq A B) (synWb (.classEq C A) (.classEq C B))) :=
  by
  have p0000 := @gEqeq1 A B C
  have p0001 := @gEqcom C A
  have p0002 := @gEqcom C B
  have p0003 :=
    @gN3bitr4g (.classEq A B) (.classEq A C) (.classEq B C) (.classEq C A)
      (.classEq C B) p0000 p0001 p0002
  exact p0003

/-- Checked nominal proof certificate identified upstream as `g_eqeq2i`. -/
@[expose]
noncomputable def gEqeq2i (A : Class) (B : Class) (C : Class)
    (hyp_eqeq2i_1 : Nominal.NPrf (.classEq A B)) :
    Nominal.NPrf (synWb (.classEq C A) (.classEq C B)) :=
  by
  have p0000 := @gEqeq2 A B C
  have p0001 := Nominal.mp hyp_eqeq2i_1 p0000
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_eqeq2d`. -/
@[expose]
noncomputable def gEqeq2d (ph : Wff) (A : Class) (B : Class) (C : Class)
    (hyp_eqeq2d_1 : Nominal.NPrf (.imp ph (.classEq A B))) :
    Nominal.NPrf (.imp ph (synWb (.classEq C A) (.classEq C B))) :=
  by
  have p0000 := @gEqeq2 A B C
  have p0001 :=
    @gSyl ph (.classEq A B) (synWb (.classEq C A) (.classEq C B)) hyp_eqeq2d_1 p0000
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_eqeq12`. -/
@[expose]
noncomputable def gEqeq12 (A : Class) (B : Class) (C : Class) (D : Class) :
    Nominal.NPrf
      (.imp (synWa (.classEq A B) (.classEq C D)) (synWb (.classEq A C) (.classEq B D))) :=
  by
  have p0000 := @gEqeq1 A B C
  have p0001 := @gEqeq2 C D B
  have p0002 :=
    @gSylan9bb (.classEq A B) (.classEq A C) (.classEq B C) (.classEq C D) (.classEq B D)
      p0000 p0001
  exact p0002

/-- Checked nominal proof certificate identified upstream as `g_eqeq12i`. -/
@[expose]
noncomputable def gEqeq12i (A : Class) (B : Class) (C : Class) (D : Class)
    (hyp_eqeq12i_1 : Nominal.NPrf (.classEq A B))
    (hyp_eqeq12i_2 : Nominal.NPrf (.classEq C D)) :
    Nominal.NPrf (synWb (.classEq A C) (.classEq B D)) :=
  by
  have p0000 := @gEqeq12 A B C D
  have p0001 :=
    @gMp2an (.classEq A B) (.classEq C D) (synWb (.classEq A C) (.classEq B D))
      hyp_eqeq12i_1 hyp_eqeq12i_2 p0000
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_eqeq12d`. -/
@[expose]
noncomputable def gEqeq12d (ph : Wff) (A : Class) (B : Class) (C : Class) (D : Class)
    (hyp_eqeq12d_1 : Nominal.NPrf (.imp ph (.classEq A B)))
    (hyp_eqeq12d_2 : Nominal.NPrf (.imp ph (.classEq C D))) :
    Nominal.NPrf (.imp ph (synWb (.classEq A C) (.classEq B D))) :=
  by
  have p0000 := @gEqeq12 A B C D
  have p0001 :=
    @gSyl2anc ph (.classEq A B) (.classEq C D) (synWb (.classEq A C) (.classEq B D))
      hyp_eqeq12d_1 hyp_eqeq12d_2 p0000
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_eqeqan12d`. -/
@[expose]
noncomputable def gEqeqan12d (ph : Wff) (ps : Wff) (A : Class) (B : Class) (C : Class)
    (D : Class) (hyp_eqeqan12d_1 : Nominal.NPrf (.imp ph (.classEq A B)))
    (hyp_eqeqan12d_2 : Nominal.NPrf (.imp ps (.classEq C D))) :
    Nominal.NPrf (.imp (synWa ph ps) (synWb (.classEq A C) (.classEq B D))) :=
  by
  have p0000 := @gEqeq12 A B C D
  have p0001 :=
    @gSyl2an ph (.classEq A B) (.classEq C D) (synWb (.classEq A C) (.classEq B D)) ps
      hyp_eqeqan12d_1 hyp_eqeqan12d_2 p0000
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_eqtr`. -/
@[expose]
noncomputable def gEqtr (A : Class) (B : Class) (C : Class) :
    Nominal.NPrf (.imp (synWa (.classEq A B) (.classEq B C)) (.classEq A C)) :=
  by
  have p0000 := @gEqeq1 A B C
  have p0001 := @gBiimpar (.classEq A B) (.classEq A C) (.classEq B C) p0000
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_eqtr2`. -/
@[expose]
noncomputable def gEqtr2 (A : Class) (B : Class) (C : Class) :
    Nominal.NPrf (.imp (synWa (.classEq A B) (.classEq A C)) (.classEq B C)) :=
  by
  have p0000 := @gEqcom A B
  have p0001 := @gEqtr B A C
  have p0002 :=
    @gSylanb (.classEq A B) (.classEq B A) (.classEq A C) (.classEq B C) p0000 p0001
  exact p0002

/-- Checked nominal proof certificate identified upstream as `g_eqtr3`. -/
@[expose]
noncomputable def gEqtr3 (A : Class) (B : Class) (C : Class) :
    Nominal.NPrf (.imp (synWa (.classEq A C) (.classEq B C)) (.classEq A B)) :=
  by
  have p0000 := @gEqcom B C
  have p0001 := @gEqtr A C B
  have p0002 :=
    @gSylan2b (.classEq B C) (.classEq A C) (.classEq C B) (.classEq A B) p0000 p0001
  exact p0002

/-- Checked nominal proof certificate identified upstream as `g_eqtri`. -/
@[expose]
noncomputable def gEqtri (A : Class) (B : Class) (C : Class)
    (hyp_eqtri_1 : Nominal.NPrf (.classEq A B))
    (hyp_eqtri_2 : Nominal.NPrf (.classEq B C)) : Nominal.NPrf (.classEq A C) :=
  by
  have p0000 := @gEqeq2i B C A hyp_eqtri_2
  have p0001 := @gMpbi (.classEq A B) (.classEq A C) hyp_eqtri_1 p0000
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_eqtr2i`. -/
@[expose]
noncomputable def gEqtr2i (A : Class) (B : Class) (C : Class)
    (hyp_eqtr2i_1 : Nominal.NPrf (.classEq A B))
    (hyp_eqtr2i_2 : Nominal.NPrf (.classEq B C)) : Nominal.NPrf (.classEq C A) :=
  by
  have p0000 := @gEqtri A B C hyp_eqtr2i_1 hyp_eqtr2i_2
  have p0001 := @gEqcomi A C p0000
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_eqtr3i`. -/
@[expose]
noncomputable def gEqtr3i (A : Class) (B : Class) (C : Class)
    (hyp_eqtr3i_1 : Nominal.NPrf (.classEq A B))
    (hyp_eqtr3i_2 : Nominal.NPrf (.classEq A C)) : Nominal.NPrf (.classEq B C) :=
  by
  have p0000 := @gEqcomi A B hyp_eqtr3i_1
  have p0001 := @gEqtri B A C p0000 hyp_eqtr3i_2
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_eqtr4i`. -/
@[expose]
noncomputable def gEqtr4i (A : Class) (B : Class) (C : Class)
    (hyp_eqtr4i_1 : Nominal.NPrf (.classEq A B))
    (hyp_eqtr4i_2 : Nominal.NPrf (.classEq C B)) : Nominal.NPrf (.classEq A C) :=
  by
  have p0000 := @gEqcomi C B hyp_eqtr4i_2
  have p0001 := @gEqtri A B C hyp_eqtr4i_1 p0000
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_n_3eqtri`. -/
@[expose]
noncomputable def gN3eqtri (A : Class) (B : Class) (C : Class) (D : Class)
    (hyp_n_3eqtri_1 : Nominal.NPrf (.classEq A B))
    (hyp_n_3eqtri_2 : Nominal.NPrf (.classEq B C))
    (hyp_n_3eqtri_3 : Nominal.NPrf (.classEq C D)) : Nominal.NPrf (.classEq A D) :=
  by
  have p0000 := @gEqtri B C D hyp_n_3eqtri_2 hyp_n_3eqtri_3
  have p0001 := @gEqtri A B D hyp_n_3eqtri_1 p0000
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_n_3eqtrri`. -/
@[expose]
noncomputable def gN3eqtrri (A : Class) (B : Class) (C : Class) (D : Class)
    (hyp_n_3eqtri_1 : Nominal.NPrf (.classEq A B))
    (hyp_n_3eqtri_2 : Nominal.NPrf (.classEq B C))
    (hyp_n_3eqtri_3 : Nominal.NPrf (.classEq C D)) : Nominal.NPrf (.classEq D A) :=
  by
  have p0000 := @gEqtri A B C hyp_n_3eqtri_1 hyp_n_3eqtri_2
  have p0001 := @gEqtr2i A C D p0000 hyp_n_3eqtri_3
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_n_3eqtr2i`. -/
@[expose]
noncomputable def gN3eqtr2i (A : Class) (B : Class) (C : Class) (D : Class)
    (hyp_n_3eqtr2i_1 : Nominal.NPrf (.classEq A B))
    (hyp_n_3eqtr2i_2 : Nominal.NPrf (.classEq C B))
    (hyp_n_3eqtr2i_3 : Nominal.NPrf (.classEq C D)) : Nominal.NPrf (.classEq A D) :=
  by
  have p0000 := @gEqtr4i A B C hyp_n_3eqtr2i_1 hyp_n_3eqtr2i_2
  have p0001 := @gEqtri A C D p0000 hyp_n_3eqtr2i_3
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_n_3eqtr2ri`. -/
@[expose]
noncomputable def gN3eqtr2ri (A : Class) (B : Class) (C : Class) (D : Class)
    (hyp_n_3eqtr2i_1 : Nominal.NPrf (.classEq A B))
    (hyp_n_3eqtr2i_2 : Nominal.NPrf (.classEq C B))
    (hyp_n_3eqtr2i_3 : Nominal.NPrf (.classEq C D)) : Nominal.NPrf (.classEq D A) :=
  by
  have p0000 := @gEqtr4i A B C hyp_n_3eqtr2i_1 hyp_n_3eqtr2i_2
  have p0001 := @gEqtr2i A C D p0000 hyp_n_3eqtr2i_3
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_n_3eqtr3i`. -/
@[expose]
noncomputable def gN3eqtr3i (A : Class) (B : Class) (C : Class) (D : Class)
    (hyp_n_3eqtr3i_1 : Nominal.NPrf (.classEq A B))
    (hyp_n_3eqtr3i_2 : Nominal.NPrf (.classEq A C))
    (hyp_n_3eqtr3i_3 : Nominal.NPrf (.classEq B D)) : Nominal.NPrf (.classEq C D) :=
  by
  have p0000 := @gEqtr3i A B C hyp_n_3eqtr3i_1 hyp_n_3eqtr3i_2
  have p0001 := @gEqtr3i B C D p0000 hyp_n_3eqtr3i_3
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_n_3eqtr4i`. -/
@[expose]
noncomputable def gN3eqtr4i (A : Class) (B : Class) (C : Class) (D : Class)
    (hyp_n_3eqtr4i_1 : Nominal.NPrf (.classEq A B))
    (hyp_n_3eqtr4i_2 : Nominal.NPrf (.classEq C A))
    (hyp_n_3eqtr4i_3 : Nominal.NPrf (.classEq D B)) : Nominal.NPrf (.classEq C D) :=
  by
  have p0000 := @gEqtr4i D B A hyp_n_3eqtr4i_3 hyp_n_3eqtr4i_1
  have p0001 := @gEqtr4i C A D hyp_n_3eqtr4i_2 p0000
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_n_3eqtr4ri`. -/
@[expose]
noncomputable def gN3eqtr4ri (A : Class) (B : Class) (C : Class) (D : Class)
    (hyp_n_3eqtr4i_1 : Nominal.NPrf (.classEq A B))
    (hyp_n_3eqtr4i_2 : Nominal.NPrf (.classEq C A))
    (hyp_n_3eqtr4i_3 : Nominal.NPrf (.classEq D B)) : Nominal.NPrf (.classEq D C) :=
  by
  have p0000 := @gEqtr4i D B A hyp_n_3eqtr4i_3 hyp_n_3eqtr4i_1
  have p0001 := @gEqtr4i D A C p0000 hyp_n_3eqtr4i_2
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_eqtrd`. -/
@[expose]
noncomputable def gEqtrd (ph : Wff) (A : Class) (B : Class) (C : Class)
    (hyp_eqtrd_1 : Nominal.NPrf (.imp ph (.classEq A B)))
    (hyp_eqtrd_2 : Nominal.NPrf (.imp ph (.classEq B C))) :
    Nominal.NPrf (.imp ph (.classEq A C)) :=
  by
  have p0000 := @gEqeq2d ph B C A hyp_eqtrd_2
  have p0001 := @gMpbid ph (.classEq A B) (.classEq A C) hyp_eqtrd_1 p0000
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_eqtr2d`. -/
@[expose]
noncomputable def gEqtr2d (ph : Wff) (A : Class) (B : Class) (C : Class)
    (hyp_eqtr2d_1 : Nominal.NPrf (.imp ph (.classEq A B)))
    (hyp_eqtr2d_2 : Nominal.NPrf (.imp ph (.classEq B C))) :
    Nominal.NPrf (.imp ph (.classEq C A)) :=
  by
  have p0000 := @gEqtrd ph A B C hyp_eqtr2d_1 hyp_eqtr2d_2
  have p0001 := @gEqcomd ph A C p0000
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_eqtr3d`. -/
@[expose]
noncomputable def gEqtr3d (ph : Wff) (A : Class) (B : Class) (C : Class)
    (hyp_eqtr3d_1 : Nominal.NPrf (.imp ph (.classEq A B)))
    (hyp_eqtr3d_2 : Nominal.NPrf (.imp ph (.classEq A C))) :
    Nominal.NPrf (.imp ph (.classEq B C)) :=
  by
  have p0000 := @gEqcomd ph A B hyp_eqtr3d_1
  have p0001 := @gEqtrd ph B A C p0000 hyp_eqtr3d_2
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_eqtr4d`. -/
@[expose]
noncomputable def gEqtr4d (ph : Wff) (A : Class) (B : Class) (C : Class)
    (hyp_eqtr4d_1 : Nominal.NPrf (.imp ph (.classEq A B)))
    (hyp_eqtr4d_2 : Nominal.NPrf (.imp ph (.classEq C B))) :
    Nominal.NPrf (.imp ph (.classEq A C)) :=
  by
  have p0000 := @gEqcomd ph C B hyp_eqtr4d_2
  have p0001 := @gEqtrd ph A B C hyp_eqtr4d_1 p0000
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_n_3eqtrd`. -/
@[expose]
noncomputable def gN3eqtrd (ph : Wff) (A : Class) (B : Class) (C : Class) (D : Class)
    (hyp_n_3eqtrd_1 : Nominal.NPrf (.imp ph (.classEq A B)))
    (hyp_n_3eqtrd_2 : Nominal.NPrf (.imp ph (.classEq B C)))
    (hyp_n_3eqtrd_3 : Nominal.NPrf (.imp ph (.classEq C D))) :
    Nominal.NPrf (.imp ph (.classEq A D)) :=
  by
  have p0000 := @gEqtrd ph B C D hyp_n_3eqtrd_2 hyp_n_3eqtrd_3
  have p0001 := @gEqtrd ph A B D hyp_n_3eqtrd_1 p0000
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_n_3eqtr3d`. -/
@[expose]
noncomputable def gN3eqtr3d (ph : Wff) (A : Class) (B : Class) (C : Class) (D : Class)
    (hyp_n_3eqtr3d_1 : Nominal.NPrf (.imp ph (.classEq A B)))
    (hyp_n_3eqtr3d_2 : Nominal.NPrf (.imp ph (.classEq A C)))
    (hyp_n_3eqtr3d_3 : Nominal.NPrf (.imp ph (.classEq B D))) :
    Nominal.NPrf (.imp ph (.classEq C D)) :=
  by
  have p0000 := @gEqtr3d ph A B C hyp_n_3eqtr3d_1 hyp_n_3eqtr3d_2
  have p0001 := @gEqtr3d ph B C D p0000 hyp_n_3eqtr3d_3
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_n_3eqtr4d`. -/
@[expose]
noncomputable def gN3eqtr4d (ph : Wff) (A : Class) (B : Class) (C : Class) (D : Class)
    (hyp_n_3eqtr4d_1 : Nominal.NPrf (.imp ph (.classEq A B)))
    (hyp_n_3eqtr4d_2 : Nominal.NPrf (.imp ph (.classEq C A)))
    (hyp_n_3eqtr4d_3 : Nominal.NPrf (.imp ph (.classEq D B))) :
    Nominal.NPrf (.imp ph (.classEq C D)) :=
  by
  have p0000 := @gEqtr4d ph D B A hyp_n_3eqtr4d_3 hyp_n_3eqtr4d_1
  have p0001 := @gEqtr4d ph C A D hyp_n_3eqtr4d_2 p0000
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_syl5eq`. -/
@[expose]
noncomputable def gSyl5eq (ph : Wff) (A : Class) (B : Class) (C : Class)
    (hyp_syl5eq_1 : Nominal.NPrf (.classEq A B))
    (hyp_syl5eq_2 : Nominal.NPrf (.imp ph (.classEq B C))) :
    Nominal.NPrf (.imp ph (.classEq A C)) :=
  by
  have p0000 := @gA1i (.classEq A B) ph hyp_syl5eq_1
  have p0001 := @gEqtrd ph A B C p0000 hyp_syl5eq_2
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_syl5req`. -/
@[expose]
noncomputable def gSyl5req (ph : Wff) (A : Class) (B : Class) (C : Class)
    (hyp_syl5req_1 : Nominal.NPrf (.classEq A B))
    (hyp_syl5req_2 : Nominal.NPrf (.imp ph (.classEq B C))) :
    Nominal.NPrf (.imp ph (.classEq C A)) :=
  by
  have p0000 := @gSyl5eq ph A B C hyp_syl5req_1 hyp_syl5req_2
  have p0001 := @gEqcomd ph A C p0000
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_syl5eqr`. -/
@[expose]
noncomputable def gSyl5eqr (ph : Wff) (A : Class) (B : Class) (C : Class)
    (hyp_syl5eqr_1 : Nominal.NPrf (.classEq B A))
    (hyp_syl5eqr_2 : Nominal.NPrf (.imp ph (.classEq B C))) :
    Nominal.NPrf (.imp ph (.classEq A C)) :=
  by
  have p0000 := @gEqcomi B A hyp_syl5eqr_1
  have p0001 := @gSyl5eq ph A B C p0000 hyp_syl5eqr_2
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_syl5reqr`. -/
@[expose]
noncomputable def gSyl5reqr (ph : Wff) (A : Class) (B : Class) (C : Class)
    (hyp_syl5reqr_1 : Nominal.NPrf (.classEq B A))
    (hyp_syl5reqr_2 : Nominal.NPrf (.imp ph (.classEq B C))) :
    Nominal.NPrf (.imp ph (.classEq C A)) :=
  by
  have p0000 := @gEqcomi B A hyp_syl5reqr_1
  have p0001 := @gSyl5req ph A B C p0000 hyp_syl5reqr_2
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_syl6eq`. -/
@[expose]
noncomputable def gSyl6eq (ph : Wff) (A : Class) (B : Class) (C : Class)
    (hyp_syl6eq_1 : Nominal.NPrf (.imp ph (.classEq A B)))
    (hyp_syl6eq_2 : Nominal.NPrf (.classEq B C)) :
    Nominal.NPrf (.imp ph (.classEq A C)) :=
  by
  have p0000 := @gA1i (.classEq B C) ph hyp_syl6eq_2
  have p0001 := @gEqtrd ph A B C hyp_syl6eq_1 p0000
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_syl6req`. -/
@[expose]
noncomputable def gSyl6req (ph : Wff) (A : Class) (B : Class) (C : Class)
    (hyp_syl6req_1 : Nominal.NPrf (.imp ph (.classEq A B)))
    (hyp_syl6req_2 : Nominal.NPrf (.classEq B C)) :
    Nominal.NPrf (.imp ph (.classEq C A)) :=
  by
  have p0000 := @gSyl6eq ph A B C hyp_syl6req_1 hyp_syl6req_2
  have p0001 := @gEqcomd ph A C p0000
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_syl6eqr`. -/
@[expose]
noncomputable def gSyl6eqr (ph : Wff) (A : Class) (B : Class) (C : Class)
    (hyp_syl6eqr_1 : Nominal.NPrf (.imp ph (.classEq A B)))
    (hyp_syl6eqr_2 : Nominal.NPrf (.classEq C B)) :
    Nominal.NPrf (.imp ph (.classEq A C)) :=
  by
  have p0000 := @gEqcomi C B hyp_syl6eqr_2
  have p0001 := @gSyl6eq ph A B C hyp_syl6eqr_1 p0000
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_syl6reqr`. -/
@[expose]
noncomputable def gSyl6reqr (ph : Wff) (A : Class) (B : Class) (C : Class)
    (hyp_syl6reqr_1 : Nominal.NPrf (.imp ph (.classEq A B)))
    (hyp_syl6reqr_2 : Nominal.NPrf (.classEq C B)) :
    Nominal.NPrf (.imp ph (.classEq C A)) :=
  by
  have p0000 := @gEqcomi C B hyp_syl6reqr_2
  have p0001 := @gSyl6req ph A B C hyp_syl6reqr_1 p0000
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_sylan9eq`. -/
@[expose]
noncomputable def gSylan9eq (ph : Wff) (ps : Wff) (A : Class) (B : Class) (C : Class)
    (hyp_sylan9eq_1 : Nominal.NPrf (.imp ph (.classEq A B)))
    (hyp_sylan9eq_2 : Nominal.NPrf (.imp ps (.classEq B C))) :
    Nominal.NPrf (.imp (synWa ph ps) (.classEq A C)) :=
  by
  have p0000 := @gEqtr A B C
  have p0001 :=
    @gSyl2an ph (.classEq A B) (.classEq B C) (.classEq A C) ps hyp_sylan9eq_1
      hyp_sylan9eq_2 p0000
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_sylan9eqr`. -/
@[expose]
noncomputable def gSylan9eqr (ph : Wff) (ps : Wff) (A : Class) (B : Class) (C : Class)
    (hyp_sylan9eqr_1 : Nominal.NPrf (.imp ph (.classEq A B)))
    (hyp_sylan9eqr_2 : Nominal.NPrf (.imp ps (.classEq B C))) :
    Nominal.NPrf (.imp (synWa ps ph) (.classEq A C)) :=
  by
  have p0000 := @gSylan9eq ph ps A B C hyp_sylan9eqr_1 hyp_sylan9eqr_2
  have p0001 := @gAncoms ph ps (.classEq A C) p0000
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_n_3eqtr3g`. -/
@[expose]
noncomputable def gN3eqtr3g (ph : Wff) (A : Class) (B : Class) (C : Class) (D : Class)
    (hyp_n_3eqtr3g_1 : Nominal.NPrf (.imp ph (.classEq A B)))
    (hyp_n_3eqtr3g_2 : Nominal.NPrf (.classEq A C))
    (hyp_n_3eqtr3g_3 : Nominal.NPrf (.classEq B D)) :
    Nominal.NPrf (.imp ph (.classEq C D)) :=
  by
  have p0000 := @gSyl5eqr ph C A B hyp_n_3eqtr3g_2 hyp_n_3eqtr3g_1
  have p0001 := @gSyl6eq ph C B D p0000 hyp_n_3eqtr3g_3
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_n_3eqtr4g`. -/
@[expose]
noncomputable def gN3eqtr4g (ph : Wff) (A : Class) (B : Class) (C : Class) (D : Class)
    (hyp_n_3eqtr4g_1 : Nominal.NPrf (.imp ph (.classEq A B)))
    (hyp_n_3eqtr4g_2 : Nominal.NPrf (.classEq C A))
    (hyp_n_3eqtr4g_3 : Nominal.NPrf (.classEq D B)) :
    Nominal.NPrf (.imp ph (.classEq C D)) :=
  by
  have p0000 := @gSyl5eq ph C A B hyp_n_3eqtr4g_2 hyp_n_3eqtr4g_1
  have p0001 := @gSyl6eqr ph C B D p0000 hyp_n_3eqtr4g_3
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_n_3eqtr4a`. -/
@[expose]
noncomputable def gN3eqtr4a (ph : Wff) (A : Class) (B : Class) (C : Class) (D : Class)
    (hyp_n_3eqtr4a_1 : Nominal.NPrf (.classEq A B))
    (hyp_n_3eqtr4a_2 : Nominal.NPrf (.imp ph (.classEq C A)))
    (hyp_n_3eqtr4a_3 : Nominal.NPrf (.imp ph (.classEq D B))) :
    Nominal.NPrf (.imp ph (.classEq C D)) :=
  by
  have p0000 := @gSyl6eq ph C A B hyp_n_3eqtr4a_2 hyp_n_3eqtr4a_1
  have p0001 := @gEqtr4d ph C B D p0000 hyp_n_3eqtr4a_3
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_eleq1`. -/
@[expose]
noncomputable def gEleq1 (A : Class) (B : Class) (C : Class) :
    Nominal.NPrf (.imp (.classEq A B) (synWb (.classMem A C) (.classMem B C))) :=
  by
  let proofSupport : Finset Var := A.fv ∪ B.fv ∪ C.fv
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
  have fresh_x_not_C : x ∉ C.fv := by
    intro h
    exact fresh_x (Finset.mem_union_right _ (h))
  have p0000 := @gEqeq2 A B (.cv x)
  have p0001 :=
    @gAnbi1d (.classEq A B) (.classEq (.cv x) A) (.classEq (.cv x) B)
      (.classMem (.cv x) C) p0000
  have p0002 :=
    @gExbidv (.classEq A B) (synWa (.classEq (.cv x) A) (.classMem (.cv x) C))
      (synWa (.classEq (.cv x) B) (.classMem (.cv x) C)) x
      (by
        first
        |
          (simp (config :=
              {
                failIfUnchanged :=
                  false }) only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
              Finset.mem_union] at ⊢;
            aesop))
      p0001
  have p0003 :=
    (NFChoice.DirectNominalPrf.Nominal.DefinitionLeafHandlersCanonical001.dfClelOfDV x A C (by
        first
        | (aesop)) (by
        first
        | (aesop)))
  have p0004 :=
    (NFChoice.DirectNominalPrf.Nominal.DefinitionLeafHandlersCanonical001.dfClelOfDV x B C (by
        first
        | (aesop)) (by
        first
        | (aesop)))
  have p0005 :=
    @gN3bitr4g (.classEq A B)
      (synWex x (synWa (.classEq (.cv x) A) (.classMem (.cv x) C)))
      (synWex x (synWa (.classEq (.cv x) B) (.classMem (.cv x) C))) (.classMem A C)
      (.classMem B C) p0002 p0003 p0004
  exact p0005

/-- Checked nominal proof certificate identified upstream as `g_eleq2`. -/
@[expose]
noncomputable def gEleq2 (A : Class) (B : Class) (C : Class) :
    Nominal.NPrf (.imp (.classEq A B) (synWb (.classMem C A) (.classMem C B))) :=
  by
  let proofSupport : Finset Var := A.fv ∪ B.fv ∪ C.fv
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
  have fresh_x_not_C : x ∉ C.fv := by
    intro h
    exact fresh_x (Finset.mem_union_right _ (h))
  have p0000 :=
    @gDfcleq x A B
      (by
        first
        | (aesop))
      (by
        first
        | (aesop))
  have p0001 :=
    @gBiimpi (.classEq A B) (.all x (synWb (.classMem (.cv x) A) (.classMem (.cv x) B)))
      p0000
  have p0002 :=
    @gN1921bi (.classEq A B) (synWb (.classMem (.cv x) A) (.classMem (.cv x) B)) x
      p0001
  have p0003 :=
    @gAnbi2d (.classEq A B) (.classMem (.cv x) A) (.classMem (.cv x) B)
      (.classEq (.cv x) C) p0002
  have p0004 :=
    @gExbidv (.classEq A B) (synWa (.classEq (.cv x) C) (.classMem (.cv x) A))
      (synWa (.classEq (.cv x) C) (.classMem (.cv x) B)) x
      (by
        first
        |
          (simp (config :=
              {
                failIfUnchanged :=
                  false }) only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
              Finset.mem_union] at ⊢;
            aesop))
      p0003
  have p0005 :=
    (NFChoice.DirectNominalPrf.Nominal.DefinitionLeafHandlersCanonical001.dfClelOfDV x C A (by
        first
        | (aesop)) (by
        first
        | (aesop)))
  have p0006 :=
    (NFChoice.DirectNominalPrf.Nominal.DefinitionLeafHandlersCanonical001.dfClelOfDV x C B (by
        first
        | (aesop)) (by
        first
        | (aesop)))
  have p0007 :=
    @gN3bitr4g (.classEq A B)
      (synWex x (synWa (.classEq (.cv x) C) (.classMem (.cv x) A)))
      (synWex x (synWa (.classEq (.cv x) C) (.classMem (.cv x) B))) (.classMem C A)
      (.classMem C B) p0004 p0005 p0006
  exact p0007

/-- Checked nominal proof certificate identified upstream as `g_eleq12`. -/
@[expose]
noncomputable def gEleq12 (A : Class) (B : Class) (C : Class) (D : Class) :
    Nominal.NPrf
      (.imp (synWa (.classEq A B) (.classEq C D)) (synWb (.classMem A C) (.classMem B D))) :=
  by
  have p0000 := @gEleq1 A B C
  have p0001 := @gEleq2 C D B
  have p0002 :=
    @gSylan9bb (.classEq A B) (.classMem A C) (.classMem B C) (.classEq C D)
      (.classMem B D) p0000 p0001
  exact p0002

/-- Checked nominal proof certificate identified upstream as `g_eleq1i`. -/
@[expose]
noncomputable def gEleq1i (A : Class) (B : Class) (C : Class)
    (hyp_eleq1i_1 : Nominal.NPrf (.classEq A B)) :
    Nominal.NPrf (synWb (.classMem A C) (.classMem B C)) :=
  by
  have p0000 := @gEleq1 A B C
  have p0001 := Nominal.mp hyp_eleq1i_1 p0000
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_eleq2i`. -/
@[expose]
noncomputable def gEleq2i (A : Class) (B : Class) (C : Class)
    (hyp_eleq1i_1 : Nominal.NPrf (.classEq A B)) :
    Nominal.NPrf (synWb (.classMem C A) (.classMem C B)) :=
  by
  have p0000 := @gEleq2 A B C
  have p0001 := Nominal.mp hyp_eleq1i_1 p0000
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_eleq1d`. -/
@[expose]
noncomputable def gEleq1d (ph : Wff) (A : Class) (B : Class) (C : Class)
    (hyp_eleq1d_1 : Nominal.NPrf (.imp ph (.classEq A B))) :
    Nominal.NPrf (.imp ph (synWb (.classMem A C) (.classMem B C))) :=
  by
  have p0000 := @gEleq1 A B C
  have p0001 :=
    @gSyl ph (.classEq A B) (synWb (.classMem A C) (.classMem B C)) hyp_eleq1d_1 p0000
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_eleq2d`. -/
@[expose]
noncomputable def gEleq2d (ph : Wff) (A : Class) (B : Class) (C : Class)
    (hyp_eleq1d_1 : Nominal.NPrf (.imp ph (.classEq A B))) :
    Nominal.NPrf (.imp ph (synWb (.classMem C A) (.classMem C B))) :=
  by
  have p0000 := @gEleq2 A B C
  have p0001 :=
    @gSyl ph (.classEq A B) (synWb (.classMem C A) (.classMem C B)) hyp_eleq1d_1 p0000
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_eleq1a`. -/
@[expose]
noncomputable def gEleq1a (A : Class) (B : Class) (C : Class) :
    Nominal.NPrf (.imp (.classMem A B) (.imp (.classEq C A) (.classMem C B))) :=
  by
  have p0000 := @gEleq1 C A B
  have p0001 := @gBiimprcd (.classEq C A) (.classMem C B) (.classMem A B) p0000
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_eqeltri`. -/
@[expose]
noncomputable def gEqeltri (A : Class) (B : Class) (C : Class)
    (hyp_eqeltr_1 : Nominal.NPrf (.classEq A B))
    (hyp_eqeltr_2 : Nominal.NPrf (.classMem B C)) : Nominal.NPrf (.classMem A C) :=
  by
  have p0000 := @gEleq1i A B C hyp_eqeltr_1
  have p0001 := @gMpbir (.classMem A C) (.classMem B C) hyp_eqeltr_2 p0000
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_eqeltrri`. -/
@[expose]
noncomputable def gEqeltrri (A : Class) (B : Class) (C : Class)
    (hyp_eqeltrr_1 : Nominal.NPrf (.classEq A B))
    (hyp_eqeltrr_2 : Nominal.NPrf (.classMem A C)) : Nominal.NPrf (.classMem B C) :=
  by
  have p0000 := @gEqcomi A B hyp_eqeltrr_1
  have p0001 := @gEqeltri B A C p0000 hyp_eqeltrr_2
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_eleqtri`. -/
@[expose]
noncomputable def gEleqtri (A : Class) (B : Class) (C : Class)
    (hyp_eleqtr_1 : Nominal.NPrf (.classMem A B))
    (hyp_eleqtr_2 : Nominal.NPrf (.classEq B C)) : Nominal.NPrf (.classMem A C) :=
  by
  have p0000 := @gEleq2i B C A hyp_eleqtr_2
  have p0001 := @gMpbi (.classMem A B) (.classMem A C) hyp_eleqtr_1 p0000
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_eleqtrri`. -/
@[expose]
noncomputable def gEleqtrri (A : Class) (B : Class) (C : Class)
    (hyp_eleqtrr_1 : Nominal.NPrf (.classMem A B))
    (hyp_eleqtrr_2 : Nominal.NPrf (.classEq C B)) : Nominal.NPrf (.classMem A C) :=
  by
  have p0000 := @gEqcomi C B hyp_eleqtrr_2
  have p0001 := @gEleqtri A B C hyp_eleqtrr_1 p0000
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_eqeltrd`. -/
@[expose]
noncomputable def gEqeltrd (ph : Wff) (A : Class) (B : Class) (C : Class)
    (hyp_eqeltrd_1 : Nominal.NPrf (.imp ph (.classEq A B)))
    (hyp_eqeltrd_2 : Nominal.NPrf (.imp ph (.classMem B C))) :
    Nominal.NPrf (.imp ph (.classMem A C)) :=
  by
  have p0000 := @gEleq1d ph A B C hyp_eqeltrd_1
  have p0001 := @gMpbird ph (.classMem A C) (.classMem B C) hyp_eqeltrd_2 p0000
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_eqeltrrd`. -/
@[expose]
noncomputable def gEqeltrrd (ph : Wff) (A : Class) (B : Class) (C : Class)
    (hyp_eqeltrrd_1 : Nominal.NPrf (.imp ph (.classEq A B)))
    (hyp_eqeltrrd_2 : Nominal.NPrf (.imp ph (.classMem A C))) :
    Nominal.NPrf (.imp ph (.classMem B C)) :=
  by
  have p0000 := @gEqcomd ph A B hyp_eqeltrrd_1
  have p0001 := @gEqeltrd ph B A C p0000 hyp_eqeltrrd_2
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_eleqtrd`. -/
@[expose]
noncomputable def gEleqtrd (ph : Wff) (A : Class) (B : Class) (C : Class)
    (hyp_eleqtrd_1 : Nominal.NPrf (.imp ph (.classMem A B)))
    (hyp_eleqtrd_2 : Nominal.NPrf (.imp ph (.classEq B C))) :
    Nominal.NPrf (.imp ph (.classMem A C)) :=
  by
  have p0000 := @gEleq2d ph B C A hyp_eleqtrd_2
  have p0001 := @gMpbid ph (.classMem A B) (.classMem A C) hyp_eleqtrd_1 p0000
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_eleqtrrd`. -/
@[expose]
noncomputable def gEleqtrrd (ph : Wff) (A : Class) (B : Class) (C : Class)
    (hyp_eleqtrrd_1 : Nominal.NPrf (.imp ph (.classMem A B)))
    (hyp_eleqtrrd_2 : Nominal.NPrf (.imp ph (.classEq C B))) :
    Nominal.NPrf (.imp ph (.classMem A C)) :=
  by
  have p0000 := @gEqcomd ph C B hyp_eleqtrrd_2
  have p0001 := @gEleqtrd ph A B C hyp_eleqtrrd_1 p0000
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_syl5eqel`. -/
@[expose]
noncomputable def gSyl5eqel (ph : Wff) (A : Class) (B : Class) (C : Class)
    (hyp_syl5eqel_1 : Nominal.NPrf (.classEq A B))
    (hyp_syl5eqel_2 : Nominal.NPrf (.imp ph (.classMem B C))) :
    Nominal.NPrf (.imp ph (.classMem A C)) :=
  by
  have p0000 := @gA1i (.classEq A B) ph hyp_syl5eqel_1
  have p0001 := @gEqeltrd ph A B C p0000 hyp_syl5eqel_2
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_syl5eqelr`. -/
@[expose]
noncomputable def gSyl5eqelr (ph : Wff) (A : Class) (B : Class) (C : Class)
    (hyp_syl5eqelr_1 : Nominal.NPrf (.classEq B A))
    (hyp_syl5eqelr_2 : Nominal.NPrf (.imp ph (.classMem B C))) :
    Nominal.NPrf (.imp ph (.classMem A C)) :=
  by
  have p0000 := @gEqcomi B A hyp_syl5eqelr_1
  have p0001 := @gSyl5eqel ph A B C p0000 hyp_syl5eqelr_2
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_syl5eleq`. -/
@[expose]
noncomputable def gSyl5eleq (ph : Wff) (A : Class) (B : Class) (C : Class)
    (hyp_syl5eleq_1 : Nominal.NPrf (.classMem A B))
    (hyp_syl5eleq_2 : Nominal.NPrf (.imp ph (.classEq B C))) :
    Nominal.NPrf (.imp ph (.classMem A C)) :=
  by
  have p0000 := @gA1i (.classMem A B) ph hyp_syl5eleq_1
  have p0001 := @gEleqtrd ph A B C p0000 hyp_syl5eleq_2
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_syl5eleqr`. -/
@[expose]
noncomputable def gSyl5eleqr (ph : Wff) (A : Class) (B : Class) (C : Class)
    (hyp_syl5eleqr_1 : Nominal.NPrf (.classMem A B))
    (hyp_syl5eleqr_2 : Nominal.NPrf (.imp ph (.classEq C B))) :
    Nominal.NPrf (.imp ph (.classMem A C)) :=
  by
  have p0000 := @gEqcomd ph C B hyp_syl5eleqr_2
  have p0001 := @gSyl5eleq ph A B C hyp_syl5eleqr_1 p0000
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_syl6eqel`. -/
@[expose]
noncomputable def gSyl6eqel (ph : Wff) (A : Class) (B : Class) (C : Class)
    (hyp_syl6eqel_1 : Nominal.NPrf (.imp ph (.classEq A B)))
    (hyp_syl6eqel_2 : Nominal.NPrf (.classMem B C)) :
    Nominal.NPrf (.imp ph (.classMem A C)) :=
  by
  have p0000 := @gA1i (.classMem B C) ph hyp_syl6eqel_2
  have p0001 := @gEqeltrd ph A B C hyp_syl6eqel_1 p0000
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_syl6eqelr`. -/
@[expose]
noncomputable def gSyl6eqelr (ph : Wff) (A : Class) (B : Class) (C : Class)
    (hyp_syl6eqelr_1 : Nominal.NPrf (.imp ph (.classEq B A)))
    (hyp_syl6eqelr_2 : Nominal.NPrf (.classMem B C)) :
    Nominal.NPrf (.imp ph (.classMem A C)) :=
  by
  have p0000 := @gEqcomd ph B A hyp_syl6eqelr_1
  have p0001 := @gSyl6eqel ph A B C p0000 hyp_syl6eqelr_2
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_syl6eleq`. -/
@[expose]
noncomputable def gSyl6eleq (ph : Wff) (A : Class) (B : Class) (C : Class)
    (hyp_syl6eleq_1 : Nominal.NPrf (.imp ph (.classMem A B)))
    (hyp_syl6eleq_2 : Nominal.NPrf (.classEq B C)) :
    Nominal.NPrf (.imp ph (.classMem A C)) :=
  by
  have p0000 := @gA1i (.classEq B C) ph hyp_syl6eleq_2
  have p0001 := @gEleqtrd ph A B C hyp_syl6eleq_1 p0000
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_syl6eleqr`. -/
@[expose]
noncomputable def gSyl6eleqr (ph : Wff) (A : Class) (B : Class) (C : Class)
    (hyp_syl6eleqr_1 : Nominal.NPrf (.imp ph (.classMem A B)))
    (hyp_syl6eleqr_2 : Nominal.NPrf (.classEq C B)) :
    Nominal.NPrf (.imp ph (.classMem A C)) :=
  by
  have p0000 := @gEqcomi C B hyp_syl6eleqr_2
  have p0001 := @gSyl6eleq ph A B C hyp_syl6eleqr_1 p0000
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_eleq2s`. -/
@[expose]
noncomputable def gEleq2s (ph : Wff) (A : Class) (B : Class) (C : Class)
    (hyp_eleq2s_1 : Nominal.NPrf (.imp (.classMem A B) ph))
    (hyp_eleq2s_2 : Nominal.NPrf (.classEq C B)) :
    Nominal.NPrf (.imp (.classMem A C) ph) :=
  by
  have p0000 := @gEleq2i C B A hyp_eleq2s_2
  have p0001 := @gSylbi (.classMem A C) (.classMem A B) ph p0000 hyp_eleq2s_1
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_neleqtrd`. -/
@[expose]
noncomputable def gNeleqtrd (ph : Wff) (A : Class) (B : Class) (C : Class)
    (hyp_neleqtrd_1 : Nominal.NPrf (.imp ph (.neg (.classMem C A))))
    (hyp_neleqtrd_2 : Nominal.NPrf (.imp ph (.classEq A B))) :
    Nominal.NPrf (.imp ph (.neg (.classMem C B))) :=
  by
  have p0000 := @gEleq2d ph A B C hyp_neleqtrd_2
  have p0001 := @gMtbid ph (.classMem C A) (.classMem C B) hyp_neleqtrd_1 p0000
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_cleqh`. -/
@[expose]
noncomputable def gCleqh (x : Var) (y : Var) (A : Class) (B : Class) (dv_A_y : y ∉ A.fv)
    (dv_B_y : y ∉ B.fv) (dv_x_y : x ≠ y)
    (hyp_cleqh_1 : Nominal.NPrf (.imp (.classMem (.cv y) A) (.all x (.classMem (.cv y) A))))
    (hyp_cleqh_2 : Nominal.NPrf (.imp (.classMem (.cv y) B) (.all x (.classMem (.cv y) B)))) :
    Nominal.NPrf
      (synWb (.classEq A B) (.all x (synWb (.classMem (.cv x) A) (.classMem (.cv x) B)))) :=
  by
  let proofSupport : Finset Var :=
    ({ x } : Finset Var) ∪ ({ y } : Finset Var) ∪ A.fv ∪ B.fv
  have p0000 :=
    @gDfcleq y A B
      (by
        first
        | (aesop))
      (by
        first
        | (aesop))
  have p0001 :=
    Nominal.ax17 (synWb (.classMem (.cv x) A) (.classMem (.cv x) B)) y
      (by
        first
        |
          (simp (config :=
              {
                failIfUnchanged :=
                  false }) only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wb,
              NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
              NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
              Finset.mem_singleton] at ⊢;
            aesop))
  have p0002 := @gDfbi2 (.classMem (.cv y) A) (.classMem (.cv y) B)
  have p0003 :=
    @gHbim (.classMem (.cv y) A) (.classMem (.cv y) B) x hyp_cleqh_1 hyp_cleqh_2
  have p0004 :=
    @gHbim (.classMem (.cv y) B) (.classMem (.cv y) A) x hyp_cleqh_2 hyp_cleqh_1
  have p0005 :=
    @gHban (.imp (.classMem (.cv y) A) (.classMem (.cv y) B))
      (.imp (.classMem (.cv y) B) (.classMem (.cv y) A)) x p0003 p0004
  have p0006 :=
    @gHbxfrbi (synWb (.classMem (.cv y) A) (.classMem (.cv y) B))
      (synWa (.imp (.classMem (.cv y) A) (.classMem (.cv y) B))
        (.imp (.classMem (.cv y) B) (.classMem (.cv y) A)))
      x p0002 p0005
  have p0007 := @gEleq1 (.cv x) (.cv y) A
  have p0008 := @gEleq1 (.cv x) (.cv y) B
  have p0009_e00_recanon :
    Nominal.NPrf
      (.imp (.objEq x y) (synWb (.classMem (.cv x) A) (.classMem (.cv y) A))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold synWb
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
        · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0007
  have p0009_e01_recanon :
    Nominal.NPrf
      (.imp (.objEq x y) (synWb (.classMem (.cv x) B) (.classMem (.cv y) B))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold synWb
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
        · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0008
  have p0009 :=
    @gBibi12d (.objEq x y) (.classMem (.cv x) A) (.classMem (.cv y) A)
      (.classMem (.cv x) B) (.classMem (.cv y) B) p0009_e00_recanon p0009_e01_recanon
  have p0010 :=
    @gBiimpd (.objEq x y) (synWb (.classMem (.cv x) A) (.classMem (.cv x) B))
      (synWb (.classMem (.cv y) A) (.classMem (.cv y) B)) p0009
  have p0011 :=
    @gCbv3h (synWb (.classMem (.cv x) A) (.classMem (.cv x) B))
      (synWb (.classMem (.cv y) A) (.classMem (.cv y) B)) x y p0001 p0006 p0010
  have p0012 :=
    @gEqucoms
      (synWb (synWb (.classMem (.cv x) A) (.classMem (.cv x) B))
        (synWb (.classMem (.cv y) A) (.classMem (.cv y) B)))
      x y p0009
  have p0013 :=
    @gBiimprd (.objEq y x) (synWb (.classMem (.cv x) A) (.classMem (.cv x) B))
      (synWb (.classMem (.cv y) A) (.classMem (.cv y) B)) p0012
  have p0014 :=
    @gCbv3h (synWb (.classMem (.cv y) A) (.classMem (.cv y) B))
      (synWb (.classMem (.cv x) A) (.classMem (.cv x) B)) y x p0006 p0001 p0013
  have p0015 :=
    @gImpbii (.all x (synWb (.classMem (.cv x) A) (.classMem (.cv x) B)))
      (.all y (synWb (.classMem (.cv y) A) (.classMem (.cv y) B))) p0011 p0014
  have p0016 :=
    @gBitr4i (.classEq A B) (.all y (synWb (.classMem (.cv y) A) (.classMem (.cv y) B)))
      (.all x (synWb (.classMem (.cv x) A) (.classMem (.cv x) B))) p0000 p0015
  exact p0016

/-- Checked nominal proof certificate identified upstream as `g_eqsb1lem`. -/
@[expose]
noncomputable def gEqsb1lem (x : Var) (y : Var) (A : Class) (dv_A_x : x ∉ A.fv)
    (dv_x_y : x ≠ y) :
    Nominal.NPrf (synWb (synWsb y x (.classEq (.cv x) A)) (.classEq (.cv y) A)) :=
  by
  let proofSupport : Finset Var := ({ x } : Finset Var) ∪ ({ y } : Finset Var) ∪ A.fv
  have p0000 :=
    @gNfv (.classEq (.cv y) A) x
      (by
        first
        |
          (simp (config :=
              {
                failIfUnchanged :=
                  false }) only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
              NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
              Finset.mem_singleton] at ⊢;
            aesop))
  have p0001 := @gEqeq1 (.cv x) (.cv y) A
  have p0002_e01_recanon :
    Nominal.NPrf (.imp (.objEq x y) (synWb (.classEq (.cv x) A) (.classEq (.cv y) A))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold synWb
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
        · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0001
  have p0002 :=
    @gSbie (.classEq (.cv x) A) (.classEq (.cv y) A) x y p0000 p0002_e01_recanon
  exact p0002

/-- Checked nominal proof certificate identified upstream as `g_eqsb1`. -/
@[expose]
noncomputable def gEqsb1 (x : Var) (y : Var) (A : Class) (dv_A_x : x ∉ A.fv) :
    Nominal.NPrf (synWb (synWsb y x (.classEq (.cv x) A)) (.classEq (.cv y) A)) :=
  by
  let proofSupport : Finset Var := ({ x } : Finset Var) ∪ ({ y } : Finset Var) ∪ A.fv
  let w : Var := freshVar proofSupport 0
  have fresh_w : w ∉ proofSupport :=
    by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_w_ne_x : w ≠ x := by
    intro h
    exact
      fresh_w
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_singleton.mpr h)))
  have fresh_x_ne_w : x ≠ w := Ne.symm fresh_w_ne_x
  have fresh_w_ne_y : w ≠ y := by
    intro h
    exact
      fresh_w
        (Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_singleton.mpr h)))
  have fresh_y_ne_w : y ≠ w := Ne.symm fresh_w_ne_y
  have fresh_w_not_A : w ∉ A.fv := by
    intro h
    exact fresh_w (Finset.mem_union_right _ (h))
  have p0000 :=
    @gEqsb1lem x w A
      (by
        first
        | (aesop))
      (by
        first
        | (aesop))
  have p0001 := @gSbbii (synWsb w x (.classEq (.cv x) A)) (.classEq (.cv w) A) w y p0000
  have p0002 :=
    @gNfv (.classEq (.cv x) A) w
      (by
        first
        |
          (simp (config :=
              {
                failIfUnchanged :=
                  false }) only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
              NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
              Finset.mem_singleton] at ⊢;
            aesop))
  have p0003 := @gSbco2 (.classEq (.cv x) A) x y w p0002
  have p0004 :=
    @gEqsb1lem w y A
      (by
        first
        | (aesop))
      (by
        first
        | (aesop))
  have p0005 :=
    @gN3bitr3i (synWsb y w (synWsb w x (.classEq (.cv x) A)))
      (synWsb y w (.classEq (.cv w) A)) (synWsb y x (.classEq (.cv x) A))
      (.classEq (.cv y) A) p0001 p0003 p0004
  exact p0005

/-- Checked nominal proof certificate identified upstream as `g_clelsb1`. -/
@[expose]
noncomputable def gClelsb1 (x : Var) (y : Var) (A : Class) (dv_A_x : x ∉ A.fv) :
    Nominal.NPrf (synWb (synWsb y x (.classMem (.cv x) A)) (.classMem (.cv y) A)) :=
  by
  let proofSupport : Finset Var := ({ x } : Finset Var) ∪ ({ y } : Finset Var) ∪ A.fv
  let w : Var := freshVar proofSupport 0
  have fresh_w : w ∉ proofSupport :=
    by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_w_ne_x : w ≠ x := by
    intro h
    exact
      fresh_w
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_singleton.mpr h)))
  have fresh_x_ne_w : x ≠ w := Ne.symm fresh_w_ne_x
  have fresh_w_ne_y : w ≠ y := by
    intro h
    exact
      fresh_w
        (Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_singleton.mpr h)))
  have fresh_y_ne_w : y ≠ w := Ne.symm fresh_w_ne_y
  have fresh_w_not_A : w ∉ A.fv := by
    intro h
    exact fresh_w (Finset.mem_union_right _ (h))
  have p0000 :=
    @gNfv (.classMem (.cv w) A) x
      (by
        first
        |
          (simp (config :=
              {
                failIfUnchanged :=
                  false }) only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
              NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
              Finset.mem_singleton] at ⊢;
            aesop))
  have p0001 := @gSbco2 (.classMem (.cv w) A) w y x p0000
  have p0002 :=
    @gNfv (.classMem (.cv x) A) w
      (by
        first
        |
          (simp (config :=
              {
                failIfUnchanged :=
                  false }) only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
              NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
              Finset.mem_singleton] at ⊢;
            aesop))
  have p0003 := @gEleq1 (.cv w) (.cv x) A
  have p0004_e01_recanon :
    Nominal.NPrf
      (.imp (.objEq w x) (synWb (.classMem (.cv w) A) (.classMem (.cv x) A))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold synWb
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
        · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0003
  have p0004 :=
    @gSbie (.classMem (.cv w) A) (.classMem (.cv x) A) w x p0002 p0004_e01_recanon
  have p0005 :=
    @gSbbii (synWsb x w (.classMem (.cv w) A)) (.classMem (.cv x) A) x y p0004
  have p0006 :=
    @gNfv (.classMem (.cv y) A) w
      (by
        first
        |
          (simp (config :=
              {
                failIfUnchanged :=
                  false }) only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
              NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
              Finset.mem_singleton] at ⊢;
            aesop))
  have p0007 := @gEleq1 (.cv w) (.cv y) A
  have p0008_e01_recanon :
    Nominal.NPrf
      (.imp (.objEq w y) (synWb (.classMem (.cv w) A) (.classMem (.cv y) A))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold synWb
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
        · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0007
  have p0008 :=
    @gSbie (.classMem (.cv w) A) (.classMem (.cv y) A) w y p0006 p0008_e01_recanon
  have p0009 :=
    @gN3bitr3i (synWsb y x (synWsb x w (.classMem (.cv w) A)))
      (synWsb y w (.classMem (.cv w) A)) (synWsb y x (.classMem (.cv x) A))
      (.classMem (.cv y) A) p0001 p0005 p0008
  exact p0009

/-- Checked nominal proof certificate identified upstream as `g_hblem`. -/
@[expose]
noncomputable def gHblem (x : Var) (y : Var) (z : Var) (A : Class) (dv_A_y : y ∉ A.fv)
    (dv_x_z : x ≠ z)
    (hyp_hblem_1 : Nominal.NPrf (.imp (.classMem (.cv y) A) (.all x (.classMem (.cv y) A)))) :
    Nominal.NPrf (.imp (.classMem (.cv z) A) (.all x (.classMem (.cv z) A))) :=
  by
  let proofSupport : Finset Var :=
    ({ x } : Finset Var) ∪ ({ y } : Finset Var) ∪ ({ z } : Finset Var) ∪ A.fv
  have p0000 :=
    @gHbsb (.classMem (.cv y) A) y z x
      (by
        first
        | (aesop))
      hyp_hblem_1
  have p0001 :=
    @gClelsb1 y z A
      (by
        first
        | (aesop))
  have p0002 := @gAlbii (synWsb z y (.classMem (.cv y) A)) (.classMem (.cv z) A) x p0001
  have p0003 :=
    @gN3imtr3i (synWsb z y (.classMem (.cv y) A))
      (.all x (synWsb z y (.classMem (.cv y) A))) (.classMem (.cv z) A)
      (.all x (.classMem (.cv z) A)) p0000 p0001 p0002
  exact p0003

/-- Checked nominal proof certificate identified upstream as `g_eqabb`. -/
@[expose]
noncomputable def gEqabb (ph : Wff) (x : Var) (A : Class) (dv_A_x : x ∉ A.fv) :
    Nominal.NPrf
      (synWb (.classEq A (.cab x ph)) (.all x (synWb (.classMem (.cv x) A) ph))) :=
  by
  let proofSupport : Finset Var := ph.fv ∪ ({ x } : Finset Var) ∪ A.fv
  let y : Var := freshVar proofSupport 0
  have fresh_y : y ∉ proofSupport :=
    by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_y_not_ph : y ∉ ph.fv := by
    intro h
    exact fresh_y (Finset.mem_union_left _ (Finset.mem_union_left _ (h)))
  have fresh_y_ne_x : y ≠ x := by
    intro h
    exact
      fresh_y
        (Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_singleton.mpr h)))
  have fresh_x_ne_y : x ≠ y := Ne.symm fresh_y_ne_x
  have fresh_y_not_A : y ∉ A.fv := by
    intro h
    exact fresh_y (Finset.mem_union_right _ (h))
  have p0000 :=
    Nominal.ax17 (.classMem (.cv y) A) x
      (by
        first
        |
          (simp (config :=
              {
                failIfUnchanged :=
                  false }) only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
              NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
              Finset.mem_singleton] at ⊢;
            aesop))
  have p0001 :=
    @gHbab1 ph x y
      (by
        first
        | (aesop))
  have p0002 :=
    @gCleqh x y A (.cab x ph)
      (by
        first
        | (aesop))
      (by
        first
        |
          (simp (config :=
              {
                failIfUnchanged :=
                  false }) only [NFChoice.Compiler.CoreFVSimp.fv_class_cab,
              Finset.mem_erase] at ⊢;
            aesop))
      (by
        first
        | (aesop))
      p0000 p0001
  have p0003 := @gAbid ph x
  have p0004 := @gBibi2i (.classMem (.cv x) (.cab x ph)) ph (.classMem (.cv x) A) p0003
  have p0005 :=
    @gAlbii (synWb (.classMem (.cv x) A) (.classMem (.cv x) (.cab x ph)))
      (synWb (.classMem (.cv x) A) ph) x p0004
  have p0006 :=
    @gBitri (.classEq A (.cab x ph))
      (.all x (synWb (.classMem (.cv x) A) (.classMem (.cv x) (.cab x ph))))
      (.all x (synWb (.classMem (.cv x) A) ph)) p0002 p0005
  exact p0006

/-- Checked nominal proof certificate identified upstream as `g_eqabcb`. -/
@[expose]
noncomputable def gEqabcb (ph : Wff) (x : Var) (A : Class) (dv_A_x : x ∉ A.fv) :
    Nominal.NPrf
      (synWb (.classEq (.cab x ph) A) (.all x (synWb ph (.classMem (.cv x) A)))) :=
  by
  let proofSupport : Finset Var := ph.fv ∪ ({ x } : Finset Var) ∪ A.fv
  have p0000 :=
    @gEqabb ph x A
      (by
        first
        | (aesop))
  have p0001 := @gEqcom (.cab x ph) A
  have p0002 := @gBicom ph (.classMem (.cv x) A)
  have p0003 :=
    @gAlbii (synWb ph (.classMem (.cv x) A)) (synWb (.classMem (.cv x) A) ph) x p0002
  have p0004 :=
    @gN3bitr4i (.classEq A (.cab x ph)) (.all x (synWb (.classMem (.cv x) A) ph))
      (.classEq (.cab x ph) A) (.all x (synWb ph (.classMem (.cv x) A))) p0000 p0001
      p0003
  exact p0004

/-- Checked nominal proof certificate identified upstream as `g_eqabri`. -/
@[expose]
noncomputable def gEqabri (ph : Wff) (x : Var) (A : Class)
    (hyp_eqabri_1 : Nominal.NPrf (.classEq A (.cab x ph))) :
    Nominal.NPrf (synWb (.classMem (.cv x) A) ph) :=
  by
  have p0000 := @gEleq2i A (.cab x ph) (.cv x) hyp_eqabri_1
  have p0001 := @gAbid ph x
  have p0002 :=
    @gBitri (.classMem (.cv x) A) (.classMem (.cv x) (.cab x ph)) ph p0000 p0001
  exact p0002

/-- Checked nominal proof certificate identified upstream as `g_eqabrd`. -/
@[expose]
noncomputable def gEqabrd (ph : Wff) (ps : Wff) (x : Var) (A : Class)
    (hyp_eqabrd_1 : Nominal.NPrf (.imp ph (.classEq A (.cab x ps)))) :
    Nominal.NPrf (.imp ph (synWb (.classMem (.cv x) A) ps)) :=
  by
  have p0000 := @gEleq2d ph A (.cab x ps) (.cv x) hyp_eqabrd_1
  have p0001 := @gAbid ps x
  have p0002 :=
    @gSyl6bb ph (.classMem (.cv x) A) (.classMem (.cv x) (.cab x ps)) ps p0000 p0001
  exact p0002

/-- Checked nominal proof certificate identified upstream as `g_abbib`. -/
@[expose]
noncomputable def gAbbib (ph : Wff) (ps : Wff) (x : Var) :
    Nominal.NPrf (synWb (.classEq (.cab x ph) (.cab x ps)) (.all x (synWb ph ps))) :=
  by
  let proofSupport : Finset Var := ph.fv ∪ ps.fv ∪ ({ x } : Finset Var)
  let y : Var := freshVar proofSupport 0
  have fresh_y : y ∉ proofSupport :=
    by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_y_not_ph : y ∉ ph.fv := by
    intro h
    exact fresh_y (Finset.mem_union_left _ (Finset.mem_union_left _ (h)))
  have fresh_y_not_ps : y ∉ ps.fv := by
    intro h
    exact fresh_y (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_y_ne_x : y ≠ x := by
    intro h
    exact fresh_y (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))
  have fresh_x_ne_y : x ≠ y := Ne.symm fresh_y_ne_x
  have p0000 :=
    @gDfcleq y (.cab x ph) (.cab x ps)
      (by
        first
        |
          (simp (config :=
              {
                failIfUnchanged :=
                  false }) only [NFChoice.Compiler.CoreFVSimp.fv_class_cab,
              Finset.mem_erase] at ⊢;
            aesop))
      (by
        first
        |
          (simp (config :=
              {
                failIfUnchanged :=
                  false }) only [NFChoice.Compiler.CoreFVSimp.fv_class_cab,
              Finset.mem_erase] at ⊢;
            aesop))
  have p0001 :=
    @gNfsab1 ph x y
      (by
        first
        | (aesop))
  have p0002 :=
    @gNfsab1 ps x y
      (by
        first
        | (aesop))
  have p0003 :=
    @gNfbi (.classMem (.cv y) (.cab x ph)) (.classMem (.cv y) (.cab x ps)) x p0001 p0002
  have p0004 :=
    @gNfv (synWb ph ps) y
      (by
        first
        |
          (simp (config :=
              {
                failIfUnchanged :=
                  false }) only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wb,
              Finset.mem_union] at ⊢;
            aesop))
  have p0005 :=
    (NFChoice.DirectNominalPrf.Nominal.DefinitionLeafHandlersCanonical001.dfClabStructural
      y x ph)
  have p0006 := @gSbequ12r ph y x
  have p0007 :=
    @gSyl5bb (.classMem (.cv y) (.cab x ph)) (synWsb y x ph) (.objEq y x) ph p0005 p0006
  have p0008 :=
    (NFChoice.DirectNominalPrf.Nominal.DefinitionLeafHandlersCanonical001.dfClabStructural
      y x ps)
  have p0009 := @gSbequ12r ps y x
  have p0010 :=
    @gSyl5bb (.classMem (.cv y) (.cab x ps)) (synWsb y x ps) (.objEq y x) ps p0008 p0009
  have p0011 :=
    @gBibi12d (.objEq y x) (.classMem (.cv y) (.cab x ph)) ph
      (.classMem (.cv y) (.cab x ps)) ps p0007 p0010
  have p0012 :=
    @gCbval (synWb (.classMem (.cv y) (.cab x ph)) (.classMem (.cv y) (.cab x ps)))
      (synWb ph ps) y x p0003 p0004 p0011
  have p0013 :=
    @gBitri (.classEq (.cab x ph) (.cab x ps))
      (.all y (synWb (.classMem (.cv y) (.cab x ph)) (.classMem (.cv y) (.cab x ps))))
      (.all x (synWb ph ps)) p0000 p0012
  exact p0013

/-- Checked nominal proof certificate identified upstream as `g_eqabi`. -/
@[expose]
noncomputable def gEqabi (ph : Wff) (x : Var) (A : Class) (dv_A_x : x ∉ A.fv)
    (hyp_abbiri_1 : Nominal.NPrf (synWb (.classMem (.cv x) A) ph)) :
    Nominal.NPrf (.classEq A (.cab x ph)) :=
  by
  let proofSupport : Finset Var := ph.fv ∪ ({ x } : Finset Var) ∪ A.fv
  have p0000 :=
    @gEqabb ph x A
      (by
        first
        | (aesop))
  have p0001 :=
    @gMpgbir (.classEq A (.cab x ph)) (synWb (.classMem (.cv x) A) ph) x p0000
      hyp_abbiri_1
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_abbii`. -/
@[expose]
noncomputable def gAbbii (ph : Wff) (ps : Wff) (x : Var)
    (hyp_abbii_1 : Nominal.NPrf (synWb ph ps)) :
    Nominal.NPrf (.classEq (.cab x ph) (.cab x ps)) :=
  by
  have p0000 := @gAbbib ph ps x
  have p0001 :=
    @gMpgbir (.classEq (.cab x ph) (.cab x ps)) (synWb ph ps) x p0000 hyp_abbii_1
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_abbid`. -/
@[expose]
noncomputable def gAbbid (ph : Wff) (ps : Wff) (ch : Wff) (x : Var)
    (hyp_abbid_1 : Nominal.NPrf (synWnf x ph))
    (hyp_abbid_2 : Nominal.NPrf (.imp ph (synWb ps ch))) :
    Nominal.NPrf (.imp ph (.classEq (.cab x ps) (.cab x ch))) :=
  by
  have p0000 := @gAlrimi ph (synWb ps ch) x hyp_abbid_1 hyp_abbid_2
  have p0001 := @gAbbib ps ch x
  have p0002 :=
    @gSylibr ph (.all x (synWb ps ch)) (.classEq (.cab x ps) (.cab x ch)) p0000 p0001
  exact p0002

/-- Checked nominal proof certificate identified upstream as `g_abbidv`. -/
@[expose]
noncomputable def gAbbidv (ph : Wff) (ps : Wff) (ch : Wff) (x : Var)
    (dv_ph_x : x ∉ ph.fv) (hyp_abbidv_1 : Nominal.NPrf (.imp ph (synWb ps ch))) :
    Nominal.NPrf (.imp ph (.classEq (.cab x ps) (.cab x ch))) :=
  by
  let proofSupport : Finset Var := ph.fv ∪ ps.fv ∪ ch.fv ∪ ({ x } : Finset Var)
  have p0000 :=
    @gNfv ph x
      (by
        first
        | (aesop))
  have p0001 := @gAbbid ph ps ch x p0000 hyp_abbidv_1
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_eqabdv`. -/
@[expose]
noncomputable def gEqabdv (ph : Wff) (ps : Wff) (x : Var) (A : Class) (dv_A_x : x ∉ A.fv)
    (dv_ph_x : x ∉ ph.fv)
    (hyp_eqabdv_1 : Nominal.NPrf (.imp ph (synWb (.classMem (.cv x) A) ps))) :
    Nominal.NPrf (.imp ph (.classEq A (.cab x ps))) :=
  by
  let proofSupport : Finset Var := ph.fv ∪ ps.fv ∪ ({ x } : Finset Var) ∪ A.fv
  have p0000 :=
    @gAlrimiv ph (synWb (.classMem (.cv x) A) ps) x
      (by
        first
        | (aesop))
      hyp_eqabdv_1
  have p0001 :=
    @gEqabb ps x A
      (by
        first
        | (aesop))
  have p0002 :=
    @gSylibr ph (.all x (synWb (.classMem (.cv x) A) ps)) (.classEq A (.cab x ps)) p0000
      p0001
  exact p0002

/-- Checked nominal proof certificate identified upstream as `g_eqabcdv`. -/
@[expose]
noncomputable def gEqabcdv (ph : Wff) (ps : Wff) (x : Var) (A : Class)
    (dv_A_x : x ∉ A.fv) (dv_ph_x : x ∉ ph.fv)
    (hyp_eqabcdv_1 : Nominal.NPrf (.imp ph (synWb ps (.classMem (.cv x) A)))) :
    Nominal.NPrf (.imp ph (.classEq (.cab x ps) A)) :=
  by
  let proofSupport : Finset Var := ph.fv ∪ ps.fv ∪ ({ x } : Finset Var) ∪ A.fv
  have p0000 :=
    @gAlrimiv ph (synWb ps (.classMem (.cv x) A)) x
      (by
        first
        | (aesop))
      hyp_eqabcdv_1
  have p0001 :=
    @gEqabcb ps x A
      (by
        first
        | (aesop))
  have p0002 :=
    @gSylibr ph (.all x (synWb ps (.classMem (.cv x) A))) (.classEq (.cab x ps) A) p0000
      p0001
  exact p0002

/-- Checked nominal proof certificate identified upstream as `g_abid2`. -/
@[expose]
noncomputable def gAbid2 (x : Var) (A : Class) (dv_A_x : x ∉ A.fv) :
    Nominal.NPrf (.classEq (.cab x (.classMem (.cv x) A)) A) :=
  by
  let proofSupport : Finset Var := ({ x } : Finset Var) ∪ A.fv
  have p0000 := @gBiid (.classMem (.cv x) A)
  have p0001 :=
    @gEqabi (.classMem (.cv x) A) x A
      (by
        first
        | (aesop))
      p0000
  have p0002 := @gEqcomi A (.cab x (.classMem (.cv x) A)) p0001
  exact p0002

/-- Checked nominal proof certificate identified upstream as `g_cbvab`. -/
@[expose]
noncomputable def gCbvab (ph : Wff) (ps : Wff) (x : Var) (y : Var)
    (hyp_cbvab_1 : Nominal.NPrf (synWnf y ph))
    (hyp_cbvab_2 : Nominal.NPrf (synWnf x ps))
    (hyp_cbvab_3 : Nominal.NPrf (.imp (.objEq x y) (synWb ph ps))) :
    Nominal.NPrf (.classEq (.cab x ph) (.cab y ps)) :=
  by
  let proofSupport : Finset Var :=
    ph.fv ∪ ps.fv ∪ ({ x } : Finset Var) ∪ ({ y } : Finset Var)
  let z : Var := freshVar proofSupport 0
  have fresh_z : z ∉ proofSupport :=
    by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_z_not_ph : z ∉ ph.fv := by
    intro h
    exact
      fresh_z
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (h))))
  have fresh_z_not_ps : z ∉ ps.fv := by
    intro h
    exact
      fresh_z
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))
  have fresh_z_ne_x : z ≠ x := by
    intro h
    exact
      fresh_z
        (Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_singleton.mpr h)))
  have fresh_x_ne_z : x ≠ z := Ne.symm fresh_z_ne_x
  have fresh_z_ne_y : z ≠ y := by
    intro h
    exact fresh_z (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))
  have fresh_y_ne_z : y ≠ z := Ne.symm fresh_z_ne_y
  have p0000 :=
    @gNfsb ps y z x
      (by
        first
        | (aesop))
      hyp_cbvab_2
  have p0001 := @gEqucoms (synWb ph ps) x y hyp_cbvab_3
  have p0002_e00_recanon :
    Nominal.NPrf (.imp (.classEq (.cv y) (.cv x)) (synWb ph ps)) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold synWb
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · exact Nominal.RecanonTransportDev.TRecanonWff.objEq_classEq _ _
        · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0001
  have p0002 := @gBicomd (.classEq (.cv y) (.cv x)) ph ps p0002_e00_recanon
  have p0003_e01_recanon : Nominal.NPrf (.imp (.objEq y x) (synWb ps ph)) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold synWb
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
        · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0002
  have p0003 := @gSbie ps ph y x hyp_cbvab_1 p0003_e01_recanon
  have p0004 := @gSbequ ps x z y
  have p0005_e01_recanon :
    Nominal.NPrf
      (.imp (.classEq (.cv x) (.cv z)) (synWb (synWsb x y ps) (synWsb z y ps))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold synWb synWsb synWa synWex
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · exact Nominal.RecanonTransportDev.TRecanonWff.objEq_classEq _ _
        · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0004
  have p0005 :=
    @gSyl5bbr ph (synWsb x y ps) (.classEq (.cv x) (.cv z)) (synWsb z y ps) p0003
      p0005_e01_recanon
  have p0006_e01_recanon :
    Nominal.NPrf (.imp (.objEq x z) (synWb ph (synWsb z y ps))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold synWb synWsb synWa synWex
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
        · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0005
  have p0006 := @gSbie ph (synWsb z y ps) x z p0000 p0006_e01_recanon
  have p0007 :=
    (NFChoice.DirectNominalPrf.Nominal.DefinitionLeafHandlersCanonical001.dfClabStructural
      z x ph)
  have p0008 :=
    (NFChoice.DirectNominalPrf.Nominal.DefinitionLeafHandlersCanonical001.dfClabStructural
      z y ps)
  have p0009 :=
    @gN3bitr4i (synWsb z x ph) (synWsb z y ps) (.classMem (.cv z) (.cab x ph))
      (.classMem (.cv z) (.cab y ps)) p0006 p0007 p0008
  have p0010 :=
    @gEqriv z (.cab x ph) (.cab y ps)
      (by
        first
        |
          (simp (config :=
              {
                failIfUnchanged :=
                  false }) only [NFChoice.Compiler.CoreFVSimp.fv_class_cab,
              Finset.mem_erase] at ⊢;
            aesop))
      (by
        first
        |
          (simp (config :=
              {
                failIfUnchanged :=
                  false }) only [NFChoice.Compiler.CoreFVSimp.fv_class_cab,
              Finset.mem_erase] at ⊢;
            aesop))
      p0009
  exact p0010

/-- Checked nominal proof certificate identified upstream as `g_nfci`. -/
@[expose]
noncomputable def gNfci (x : Var) (y : Var) (A : Class) (dv_A_y : y ∉ A.fv)
    (dv_x_y : x ≠ y) (hyp_nfci_1 : Nominal.NPrf (synWnf x (.classMem (.cv y) A))) :
    Nominal.NPrf (synWnfc x A) :=
  by
  let proofSupport : Finset Var := ({ x } : Finset Var) ∪ ({ y } : Finset Var) ∪ A.fv
  have p0000 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominalDfNfc x y A
      (by
        first
        | (aesop))
      (by
        first
        | (aesop))
  have p0001 :=
    @gMpgbir (synWnfc x A) (synWnf x (.classMem (.cv y) A)) y p0000 hyp_nfci_1
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_nfcr`. -/
@[expose]
noncomputable def gNfcr (x : Var) (y : Var) (A : Class) (dv_A_y : y ∉ A.fv)
    (dv_x_y : x ≠ y) :
    Nominal.NPrf (.imp (synWnfc x A) (synWnf x (.classMem (.cv y) A))) :=
  by
  let proofSupport : Finset Var := ({ x } : Finset Var) ∪ ({ y } : Finset Var) ∪ A.fv
  have p0000 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominalDfNfc x y A
      (by
        first
        | (aesop))
      (by
        first
        | (aesop))
  have p0001 := @gSp (synWnf x (.classMem (.cv y) A)) y
  have p0002 :=
    @gSylbi (synWnfc x A) (.all y (synWnf x (.classMem (.cv y) A)))
      (synWnf x (.classMem (.cv y) A)) p0000 p0001
  exact p0002

/-- Checked nominal proof certificate identified upstream as `g_nfcrii`. -/
@[expose]
noncomputable def gNfcrii (x : Var) (y : Var) (A : Class) (dv_x_y : x ≠ y)
    (hyp_nfcri_1 : Nominal.NPrf (synWnfc x A)) :
    Nominal.NPrf (.imp (.classMem (.cv y) A) (.all x (.classMem (.cv y) A))) :=
  by
  let proofSupport : Finset Var := ({ x } : Finset Var) ∪ ({ y } : Finset Var) ∪ A.fv
  let z : Var := freshVar proofSupport 0
  have fresh_z : z ∉ proofSupport :=
    by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_z_ne_x : z ≠ x := by
    intro h
    exact
      fresh_z
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_singleton.mpr h)))
  have fresh_x_ne_z : x ≠ z := Ne.symm fresh_z_ne_x
  have fresh_z_ne_y : z ≠ y := by
    intro h
    exact
      fresh_z
        (Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_singleton.mpr h)))
  have fresh_y_ne_z : y ≠ z := Ne.symm fresh_z_ne_y
  have fresh_z_not_A : z ∉ A.fv := by
    intro h
    exact fresh_z (Finset.mem_union_right _ (h))
  have p0000 :=
    @gNfcr x z A
      (by
        first
        | (aesop))
      (by
        first
        | (aesop))
  have p0001 := Nominal.mp hyp_nfcri_1 p0000
  have p0002 := @gNfri (.classMem (.cv z) A) x p0001
  have p0003 :=
    @gHblem x z y A
      (by
        first
        | (aesop))
      (by
        first
        | (aesop))
      p0002
  exact p0003

/-- Checked nominal proof certificate identified upstream as `g_nfcri`. -/
@[expose]
noncomputable def gNfcri (x : Var) (y : Var) (A : Class) (dv_x_y : x ≠ y)
    (hyp_nfcri_1 : Nominal.NPrf (synWnfc x A)) :
    Nominal.NPrf (synWnf x (.classMem (.cv y) A)) :=
  by
  let proofSupport : Finset Var := ({ x } : Finset Var) ∪ ({ y } : Finset Var) ∪ A.fv
  have p0000 :=
    @gNfcrii x y A
      (by
        first
        | (aesop))
      hyp_nfcri_1
  have p0001 := @gNfi (.classMem (.cv y) A) x p0000
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_nfcd`. -/
@[expose]
noncomputable def gNfcd (ph : Wff) (x : Var) (y : Var) (A : Class) (dv_A_y : y ∉ A.fv)
    (dv_x_y : x ≠ y) (hyp_nfcd_1 : Nominal.NPrf (synWnf y ph))
    (hyp_nfcd_2 : Nominal.NPrf (.imp ph (synWnf x (.classMem (.cv y) A)))) :
    Nominal.NPrf (.imp ph (synWnfc x A)) :=
  by
  let proofSupport : Finset Var :=
    ph.fv ∪ ({ x } : Finset Var) ∪ ({ y } : Finset Var) ∪ A.fv
  have p0000 := @gAlrimi ph (synWnf x (.classMem (.cv y) A)) y hyp_nfcd_1 hyp_nfcd_2
  have p0001 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominalDfNfc x y A
      (by
        first
        | (aesop))
      (by
        first
        | (aesop))
  have p0002 :=
    @gSylibr ph (.all y (synWnf x (.classMem (.cv y) A))) (synWnfc x A) p0000 p0001
  exact p0002

/-- Checked nominal proof certificate identified upstream as `g_nfceqi`. -/
@[expose]
noncomputable def gNfceqi (x : Var) (A : Class) (B : Class)
    (hyp_nfceqi_1 : Nominal.NPrf (.classEq A B)) :
    Nominal.NPrf (synWb (synWnfc x A) (synWnfc x B)) :=
  by
  let proofSupport : Finset Var := ({ x } : Finset Var) ∪ A.fv ∪ B.fv
  let y : Var := freshVar proofSupport 0
  have fresh_y : y ∉ proofSupport :=
    by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_y_ne_x : y ≠ x := by
    intro h
    exact
      fresh_y
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_singleton.mpr h)))
  have fresh_x_ne_y : x ≠ y := Ne.symm fresh_y_ne_x
  have fresh_y_not_A : y ∉ A.fv := by
    intro h
    exact fresh_y (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_y_not_B : y ∉ B.fv := by
    intro h
    exact fresh_y (Finset.mem_union_right _ (h))
  have p0000 := @gEleq2i A B (.cv y) hyp_nfceqi_1
  have p0001 := @gNfbii (.classMem (.cv y) A) (.classMem (.cv y) B) x p0000
  have p0002 :=
    @gAlbii (synWnf x (.classMem (.cv y) A)) (synWnf x (.classMem (.cv y) B)) y p0001
  have p0003 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominalDfNfc x y A
      (by
        first
        | (aesop))
      (by
        first
        | (aesop))
  have p0004 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominalDfNfc x y B
      (by
        first
        | (aesop))
      (by
        first
        | (aesop))
  have p0005 :=
    @gN3bitr4i (.all y (synWnf x (.classMem (.cv y) A)))
      (.all y (synWnf x (.classMem (.cv y) B))) (synWnfc x A) (synWnfc x B) p0002 p0003
      p0004
  exact p0005

/-- Checked nominal proof certificate identified upstream as `g_nfcxfr`. -/
@[expose]
noncomputable def gNfcxfr (x : Var) (A : Class) (B : Class)
    (hyp_nfceqi_1 : Nominal.NPrf (.classEq A B))
    (hyp_nfcxfr_2 : Nominal.NPrf (synWnfc x B)) : Nominal.NPrf (synWnfc x A) :=
  by
  have p0000 := @gNfceqi x A B hyp_nfceqi_1
  have p0001 := @gMpbir (synWnfc x A) (synWnfc x B) hyp_nfcxfr_2 p0000
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_nfcxfrd`. -/
@[expose]
noncomputable def gNfcxfrd (ph : Wff) (x : Var) (A : Class) (B : Class)
    (hyp_nfceqi_1 : Nominal.NPrf (.classEq A B))
    (hyp_nfcxfrd_2 : Nominal.NPrf (.imp ph (synWnfc x B))) :
    Nominal.NPrf (.imp ph (synWnfc x A)) :=
  by
  have p0000 := @gNfceqi x A B hyp_nfceqi_1
  have p0001 := @gSylibr ph (synWnfc x B) (synWnfc x A) hyp_nfcxfrd_2 p0000
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_nfceqdf`. -/
@[expose]
noncomputable def gNfceqdf (ph : Wff) (x : Var) (A : Class) (B : Class)
    (hyp_nfceqdf_1 : Nominal.NPrf (synWnf x ph))
    (hyp_nfceqdf_2 : Nominal.NPrf (.imp ph (.classEq A B))) :
    Nominal.NPrf (.imp ph (synWb (synWnfc x A) (synWnfc x B))) :=
  by
  let proofSupport : Finset Var := ph.fv ∪ ({ x } : Finset Var) ∪ A.fv ∪ B.fv
  let y : Var := freshVar proofSupport 0
  have fresh_y : y ∉ proofSupport :=
    by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_y_not_ph : y ∉ ph.fv := by
    intro h
    exact
      fresh_y
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (h))))
  have fresh_y_ne_x : y ≠ x := by
    intro h
    exact
      fresh_y
        (Finset.mem_union_left _ (Finset.mem_union_left _
            (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))))
  have fresh_x_ne_y : x ≠ y := Ne.symm fresh_y_ne_x
  have fresh_y_not_A : y ∉ A.fv := by
    intro h
    exact fresh_y (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_y_not_B : y ∉ B.fv := by
    intro h
    exact fresh_y (Finset.mem_union_right _ (h))
  have p0000 := @gEleq2d ph A B (.cv y) hyp_nfceqdf_2
  have p0001 :=
    @gNfbidf ph (.classMem (.cv y) A) (.classMem (.cv y) B) x hyp_nfceqdf_1 p0000
  have p0002 :=
    @gAlbidv ph (synWnf x (.classMem (.cv y) A)) (synWnf x (.classMem (.cv y) B)) y
      (by
        first
        | (aesop))
      p0001
  have p0003 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominalDfNfc x y A
      (by
        first
        | (aesop))
      (by
        first
        | (aesop))
  have p0004 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominalDfNfc x y B
      (by
        first
        | (aesop))
      (by
        first
        | (aesop))
  have p0005 :=
    @gN3bitr4g ph (.all y (synWnf x (.classMem (.cv y) A)))
      (.all y (synWnf x (.classMem (.cv y) B))) (synWnfc x A) (synWnfc x B) p0002 p0003
      p0004
  exact p0005

/-- Checked nominal proof certificate identified upstream as `g_nfcv`. -/
@[expose]
noncomputable def gNfcv (x : Var) (A : Class) (dv_A_x : x ∉ A.fv) :
    Nominal.NPrf (synWnfc x A) :=
  by
  let proofSupport : Finset Var := ({ x } : Finset Var) ∪ A.fv
  let y : Var := freshVar proofSupport 0
  have fresh_y : y ∉ proofSupport :=
    by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_y_ne_x : y ≠ x := by
    intro h
    exact fresh_y (Finset.mem_union_left _ (Finset.mem_singleton.mpr h))
  have fresh_x_ne_y : x ≠ y := Ne.symm fresh_y_ne_x
  have fresh_y_not_A : y ∉ A.fv := by
    intro h
    exact fresh_y (Finset.mem_union_right _ (h))
  have p0000 :=
    @gNfv (.classMem (.cv y) A) x
      (by
        first
        |
          (simp (config :=
              {
                failIfUnchanged :=
                  false }) only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
              NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
              Finset.mem_singleton] at ⊢;
            aesop))
  have p0001 :=
    @gNfci x y A
      (by
        first
        | (aesop))
      (by
        first
        | (aesop))
      p0000
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_nfcvd`. -/
@[expose]
noncomputable def gNfcvd (ph : Wff) (x : Var) (A : Class) (dv_A_x : x ∉ A.fv) :
    Nominal.NPrf (.imp ph (synWnfc x A)) :=
  by
  let proofSupport : Finset Var := ph.fv ∪ ({ x } : Finset Var) ∪ A.fv
  have p0000 :=
    @gNfcv x A
      (by
        first
        | (aesop))
  have p0001 := @gA1i (synWnfc x A) ph p0000
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_nfab1`. -/
@[expose]
noncomputable def gNfab1 (ph : Wff) (x : Var) : Nominal.NPrf (synWnfc x (.cab x ph)) :=
  by
  let proofSupport : Finset Var := ph.fv ∪ ({ x } : Finset Var)
  let y : Var := freshVar proofSupport 0
  have fresh_y : y ∉ proofSupport :=
    by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_y_not_ph : y ∉ ph.fv := by
    intro h
    exact fresh_y (Finset.mem_union_left _ (h))
  have fresh_y_ne_x : y ≠ x := by
    intro h
    exact fresh_y (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))
  have fresh_x_ne_y : x ≠ y := Ne.symm fresh_y_ne_x
  have p0000 :=
    @gNfsab1 ph x y
      (by
        first
        | (aesop))
  have p0001 :=
    @gNfci x y (.cab x ph)
      (by
        first
        |
          (simp (config :=
              {
                failIfUnchanged :=
                  false }) only [NFChoice.Compiler.CoreFVSimp.fv_class_cab,
              Finset.mem_erase] at ⊢;
            aesop))
      (by
        first
        | (aesop))
      p0000
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_nfnfc1`. -/
@[expose]
noncomputable def gNfnfc1 (x : Var) (A : Class) :
    Nominal.NPrf (synWnf x (synWnfc x A)) :=
  by
  let proofSupport : Finset Var := ({ x } : Finset Var) ∪ A.fv
  let y : Var := freshVar proofSupport 0
  have fresh_y : y ∉ proofSupport :=
    by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_y_ne_x : y ≠ x := by
    intro h
    exact fresh_y (Finset.mem_union_left _ (Finset.mem_singleton.mpr h))
  have fresh_x_ne_y : x ≠ y := Ne.symm fresh_y_ne_x
  have fresh_y_not_A : y ∉ A.fv := by
    intro h
    exact fresh_y (Finset.mem_union_right _ (h))
  have p0000 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominalDfNfc x y A
      (by
        first
        | (aesop))
      (by
        first
        | (aesop))
  have p0001 := @gNfnf1 (.classMem (.cv y) A) x
  have p0002 := @gNfal (synWnf x (.classMem (.cv y) A)) x y p0001
  have p0003 :=
    @gNfxfr (synWnfc x A) (.all y (synWnf x (.classMem (.cv y) A))) x p0000 p0002
  exact p0003

/-- Checked nominal proof certificate identified upstream as `g_nfab`. -/
@[expose]
noncomputable def gNfab (ph : Wff) (x : Var) (y : Var)
    (hyp_nfab_1 : Nominal.NPrf (synWnf x ph)) : Nominal.NPrf (synWnfc x (.cab y ph)) :=
  by
  let proofSupport : Finset Var := ph.fv ∪ ({ x } : Finset Var) ∪ ({ y } : Finset Var)
  let z : Var := freshVar proofSupport 0
  have fresh_z : z ∉ proofSupport :=
    by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_z_not_ph : z ∉ ph.fv := by
    intro h
    exact fresh_z (Finset.mem_union_left _ (Finset.mem_union_left _ (h)))
  have fresh_z_ne_x : z ≠ x := by
    intro h
    exact
      fresh_z
        (Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_singleton.mpr h)))
  have fresh_x_ne_z : x ≠ z := Ne.symm fresh_z_ne_x
  have fresh_z_ne_y : z ≠ y := by
    intro h
    exact fresh_z (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))
  have fresh_y_ne_z : y ≠ z := Ne.symm fresh_z_ne_y
  have p0000 :=
    @gNfsab ph x y z
      (by
        first
        | (aesop))
      hyp_nfab_1
  have p0001 :=
    @gNfci x z (.cab y ph)
      (by
        first
        |
          (simp (config :=
              {
                failIfUnchanged :=
                  false }) only [NFChoice.Compiler.CoreFVSimp.fv_class_cab,
              Finset.mem_erase] at ⊢;
            aesop))
      (by
        first
        | (aesop))
      p0000
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_nfaba1`. -/
@[expose]
noncomputable def gNfaba1 (ph : Wff) (x : Var) (y : Var) :
    Nominal.NPrf (synWnfc x (.cab y (.all x ph))) :=
  by
  have p0000 := @gNfa1 ph x
  have p0001 := @gNfab (.all x ph) x y p0000
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_nfeq`. -/
@[expose]
noncomputable def gNfeq (x : Var) (A : Class) (B : Class)
    (hyp_nfnfc_1 : Nominal.NPrf (synWnfc x A))
    (hyp_nfeq_2 : Nominal.NPrf (synWnfc x B)) :
    Nominal.NPrf (synWnf x (.classEq A B)) :=
  by
  let proofSupport : Finset Var := ({ x } : Finset Var) ∪ A.fv ∪ B.fv
  let z : Var := freshVar proofSupport 0
  have fresh_z : z ∉ proofSupport :=
    by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_z_ne_x : z ≠ x := by
    intro h
    exact
      fresh_z
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_singleton.mpr h)))
  have fresh_x_ne_z : x ≠ z := Ne.symm fresh_z_ne_x
  have fresh_z_not_A : z ∉ A.fv := by
    intro h
    exact fresh_z (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_z_not_B : z ∉ B.fv := by
    intro h
    exact fresh_z (Finset.mem_union_right _ (h))
  have p0000 :=
    @gDfcleq z A B
      (by
        first
        | (aesop))
      (by
        first
        | (aesop))
  have p0001 :=
    @gNfcri x z A
      (by
        first
        | (aesop))
      hyp_nfnfc_1
  have p0002 :=
    @gNfcri x z B
      (by
        first
        | (aesop))
      hyp_nfeq_2
  have p0003 := @gNfbi (.classMem (.cv z) A) (.classMem (.cv z) B) x p0001 p0002
  have p0004 := @gNfal (synWb (.classMem (.cv z) A) (.classMem (.cv z) B)) x z p0003
  have p0005 :=
    @gNfxfr (.classEq A B) (.all z (synWb (.classMem (.cv z) A) (.classMem (.cv z) B)))
      x p0000 p0004
  exact p0005

/-- Checked nominal proof certificate identified upstream as `g_nfel`. -/
@[expose]
noncomputable def gNfel (x : Var) (A : Class) (B : Class)
    (hyp_nfnfc_1 : Nominal.NPrf (synWnfc x A))
    (hyp_nfeq_2 : Nominal.NPrf (synWnfc x B)) :
    Nominal.NPrf (synWnf x (.classMem A B)) :=
  by
  let proofSupport : Finset Var := ({ x } : Finset Var) ∪ A.fv ∪ B.fv
  let z : Var := freshVar proofSupport 0
  have fresh_z : z ∉ proofSupport :=
    by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_z_ne_x : z ≠ x := by
    intro h
    exact
      fresh_z
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_singleton.mpr h)))
  have fresh_x_ne_z : x ≠ z := Ne.symm fresh_z_ne_x
  have fresh_z_not_A : z ∉ A.fv := by
    intro h
    exact fresh_z (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_z_not_B : z ∉ B.fv := by
    intro h
    exact fresh_z (Finset.mem_union_right _ (h))
  have p0000 :=
    (NFChoice.DirectNominalPrf.Nominal.DefinitionLeafHandlersCanonical001.dfClelOfDV z A B (by
        first
        | (aesop)) (by
        first
        | (aesop)))
  have p0001 :=
    @gNfcv x (.cv z)
      (by
        first
        |
          (simp (config :=
              {
                failIfUnchanged :=
                  false }) only [NFChoice.Compiler.CoreFVSimp.fv_class_cv,
              Finset.mem_singleton] at ⊢;
            aesop))
  have p0002 := @gNfeq x (.cv z) A p0001 hyp_nfnfc_1
  have p0003 :=
    @gNfcri x z B
      (by
        first
        | (aesop))
      hyp_nfeq_2
  have p0004 := @gNfan (.classEq (.cv z) A) (.classMem (.cv z) B) x p0002 p0003
  have p0005 := @gNfex (synWa (.classEq (.cv z) A) (.classMem (.cv z) B)) x z p0004
  have p0006 :=
    @gNfxfr (.classMem A B)
      (synWex z (synWa (.classEq (.cv z) A) (.classMem (.cv z) B))) x p0000 p0005
  exact p0006

/-- Checked nominal proof certificate identified upstream as `g_nfel1`. -/
@[expose]
noncomputable def gNfel1 (x : Var) (A : Class) (B : Class) (dv_B_x : x ∉ B.fv)
    (hyp_nfeq1_1 : Nominal.NPrf (synWnfc x A)) :
    Nominal.NPrf (synWnf x (.classMem A B)) :=
  by
  let proofSupport : Finset Var := ({ x } : Finset Var) ∪ A.fv ∪ B.fv
  have p0000 :=
    @gNfcv x B
      (by
        first
        | (aesop))
  have p0001 := @gNfel x A B hyp_nfeq1_1 p0000
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_nfeq2`. -/
@[expose]
noncomputable def gNfeq2 (x : Var) (A : Class) (B : Class) (dv_A_x : x ∉ A.fv)
    (hyp_nfeq2_1 : Nominal.NPrf (synWnfc x B)) :
    Nominal.NPrf (synWnf x (.classEq A B)) :=
  by
  let proofSupport : Finset Var := ({ x } : Finset Var) ∪ A.fv ∪ B.fv
  have p0000 :=
    @gNfcv x A
      (by
        first
        | (aesop))
  have p0001 := @gNfeq x A B p0000 hyp_nfeq2_1
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_nfel2`. -/
@[expose]
noncomputable def gNfel2 (x : Var) (A : Class) (B : Class) (dv_A_x : x ∉ A.fv)
    (hyp_nfeq2_1 : Nominal.NPrf (synWnfc x B)) :
    Nominal.NPrf (synWnf x (.classMem A B)) :=
  by
  let proofSupport : Finset Var := ({ x } : Finset Var) ∪ A.fv ∪ B.fv
  have p0000 :=
    @gNfcv x A
      (by
        first
        | (aesop))
  have p0001 := @gNfel x A B p0000 hyp_nfeq2_1
  exact p0001


end NFChoice.DirectNominalPrf.WPPReplay
