/-
Copyright (c) 2026 Elliot Glazer and NFNotWPP contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elliot Glazer and NFNotWPP contributors
-/

module

public import LeanPool.NFWeakPartition.NominalWPPReplayChunk003

/-! NF weak partition development: NominalWPPReplayChunk004. -/


public section


namespace NFChoice.DirectNominalPrf.WPPReplay

open scoped Fol
open NFChoice.Foundation
open NFChoice.SemanticCore
open NFChoice.ReplaySupport
open NFChoice.Compiler.CompactSourceSyntax

/-- Checked nominal proof certificate identified upstream as `g_merlem11`. -/
@[expose]
noncomputable def gMerlem11 (ph : Wff) (ps : Wff) :
    Nominal.NPrf (.imp (.imp ph (.imp ph ps)) (.imp ph ps)) :=
  by
  have p0000 := Nominal.axMeredith ph ph ph ph ph
  have p0001 := @gMerlem10 ph ps (.imp ph (.imp ph ps))
  have p0002 :=
    @gMerlem10 (.imp ph (.imp ph ps)) (.imp ph ps)
      (.imp (.imp (.imp (.imp (.imp ph ph) (.imp (.neg ph) (.neg ph))) ph) ph)
        (.imp (.imp ph ph) (.imp ph ph)))
  have p0003 := Nominal.mp p0001 p0002
  have p0004 := Nominal.mp p0000 p0003
  exact p0004

/-- Checked nominal proof certificate identified upstream as `g_merlem12`. -/
@[expose]
noncomputable def gMerlem12 (ph : Wff) (ch : Wff) (th : Wff) :
    Nominal.NPrf (.imp (.imp (.imp th (.imp (.neg (.neg ch)) ch)) ph) ph) :=
  by
  have p0000 := @gMerlem5 ch ch
  have p0001 := @gMerlem2 ch (.imp (.neg (.neg ch)) ch) th
  have p0002 := Nominal.mp p0000 p0001
  have p0003 :=
    @gMerlem4 ph (.imp (.imp th (.imp (.neg (.neg ch)) ch)) ph)
      (.imp th (.imp (.neg (.neg ch)) ch))
  have p0004 := Nominal.mp p0002 p0003
  have p0005 := @gMerlem11 (.imp (.imp th (.imp (.neg (.neg ch)) ch)) ph) ph
  have p0006 := Nominal.mp p0004 p0005
  exact p0006

/-- Checked nominal proof certificate identified upstream as `g_merlem13`. -/
@[expose]
noncomputable def gMerlem13 (ph : Wff) (ps : Wff) (ch : Wff) (th : Wff) :
    Nominal.NPrf
      (.imp (.imp ph ps)
        (.imp (.imp (.imp th (.imp (.neg (.neg ch)) ch)) (.neg (.neg ph))) ps)) :=
  by
  have p0000 :=
    @gMerlem12 (.neg (.imp (.imp th (.imp (.neg (.neg ch)) ch)) (.neg (.neg ph)))) ch th
  have p0001 := @gMerlem12 (.neg (.neg ph)) ch th
  have p0002 :=
    @gMerlem5 (.imp (.imp th (.imp (.neg (.neg ch)) ch)) (.neg (.neg ph)))
      (.neg (.neg ph))
  have p0003 := Nominal.mp p0001 p0002
  have p0004 :=
    @gMerlem6 (.neg (.imp (.imp th (.imp (.neg (.neg ch)) ch)) (.neg (.neg ph))))
      (.imp (.neg (.imp (.imp th (.imp (.neg (.neg ch)) ch)) (.neg (.neg ph)))) ps)
      (.imp (.neg (.neg (.imp (.imp th (.imp (.neg (.neg ch)) ch)) (.neg (.neg ph)))))
        (.neg (.neg ph)))
      (.imp th (.imp (.neg (.neg ch)) ch))
  have p0005 := Nominal.mp p0003 p0004
  have p0006 :=
    Nominal.axMeredith (.neg (.imp (.imp th (.imp (.neg (.neg ch)) ch)) (.neg (.neg ph))))
      ps (.neg (.imp (.imp th (.imp (.neg (.neg ch)) ch)) (.neg (.neg ph)))) (.neg ph)
      (.imp (.imp th (.imp (.neg (.neg ch)) ch))
        (.neg (.imp (.imp th (.imp (.neg (.neg ch)) ch)) (.neg (.neg ph)))))
  have p0007 := Nominal.mp p0005 p0006
  have p0008 := Nominal.mp p0000 p0007
  have p0009 :=
    @gMerlem6 ph (.imp ps ps)
      (.imp (.neg ph) (.neg (.imp (.imp th (.imp (.neg (.neg ch)) ch)) (.neg (.neg ph)))))
      (.imp (.imp (.imp ps ps) (.imp (.neg ph)
            (.neg (.imp (.imp th (.imp (.neg (.neg ch)) ch)) (.neg (.neg ph)))))) ph)
  have p0010 := Nominal.mp p0008 p0009
  have p0011 :=
    @gMerlem11
      (.imp (.imp (.imp ps ps) (.imp (.neg ph)
            (.neg (.imp (.imp th (.imp (.neg (.neg ch)) ch)) (.neg (.neg ph)))))) ph)
      ph
  have p0012 := Nominal.mp p0010 p0011
  have p0013 :=
    Nominal.axMeredith ps ps ph
      (.imp (.imp th (.imp (.neg (.neg ch)) ch)) (.neg (.neg ph))) ph
  have p0014 := Nominal.mp p0012 p0013
  exact p0014

/-- Checked nominal proof certificate identified upstream as `g_luk_1`. -/
@[expose]
noncomputable def g_luk_1 (ph : Wff) (ps : Wff) (ch : Wff) :
    Nominal.NPrf (.imp (.imp ph ps) (.imp (.imp ps ch) (.imp ph ch))) :=
  by
  have p0000 := Nominal.axMeredith ch ch (.neg (.neg ph)) ph ps
  have p0001 := @gMerlem13 ph ps (.neg ph) (.imp ch ch)
  have p0002 :=
    @gMerlem13 (.imp ph ps)
      (.imp (.imp (.imp (.imp ch ch) (.imp (.neg (.neg (.neg ph))) (.neg ph))) (.neg (.neg ph)))
        ps)
      (.neg (.imp ph ps)) (.imp (.imp (.imp ps ch) (.imp ph ch)) ph)
  have p0003 := Nominal.mp p0001 p0002
  have p0004 :=
    Nominal.axMeredith (.imp (.imp ps ch) (.imp ph ch)) ph (.neg (.neg (.imp ph ps)))
      (.imp ph ps)
      (.imp (.imp (.imp (.imp ch ch) (.imp (.neg (.neg (.neg ph))) (.neg ph))) (.neg (.neg ph)))
        ps)
  have p0005 := Nominal.mp p0003 p0004
  have p0006 := Nominal.mp p0000 p0005
  exact p0006

/-- Checked nominal proof certificate identified upstream as `g_luk_2`. -/
@[expose]
noncomputable def g_luk_2 (ph : Wff) : Nominal.NPrf (.imp (.imp (.neg ph) ph) ph) :=
  by
  have p0000 := @gMerlem5 ph (.neg (.imp (.neg ph) ph))
  have p0001 :=
    @gMerlem4 (.neg ph)
      (.imp (.imp (.imp ph (.neg (.imp (.neg ph) ph)))
          (.imp (.neg (.neg ph)) (.neg (.imp (.neg ph) ph)))) (.neg ph))
      (.imp (.imp ph (.neg (.imp (.neg ph) ph)))
        (.imp (.neg (.neg ph)) (.neg (.imp (.neg ph) ph))))
  have p0002 := Nominal.mp p0000 p0001
  have p0003 :=
    @gMerlem11
      (.imp (.imp (.imp ph (.neg (.imp (.neg ph) ph)))
          (.imp (.neg (.neg ph)) (.neg (.imp (.neg ph) ph)))) (.neg ph))
      (.neg ph)
  have p0004 := Nominal.mp p0002 p0003
  have p0005 :=
    Nominal.axMeredith ph (.neg (.imp (.neg ph) ph)) (.neg ph) (.imp (.neg ph) ph)
      (.neg ph)
  have p0006 := Nominal.mp p0004 p0005
  have p0007 := @gMerlem11 (.imp (.neg ph) ph) ph
  have p0008 := Nominal.mp p0006 p0007
  exact p0008

/-- Checked nominal proof certificate identified upstream as `g_luk_3`. -/
@[expose]
noncomputable def gLuk3 (ph : Wff) (ps : Wff) :
    Nominal.NPrf (.imp ph (.imp (.neg ph) ps)) :=
  by
  have p0000 := @gMerlem11 (.neg ph) ps
  have p0001 := @gMerlem1 ph ps (.neg ph) (.imp (.neg ph) ps)
  have p0002 := Nominal.mp p0000 p0001
  exact p0002

/-- Checked nominal proof certificate identified upstream as `g_luklem1`. -/
@[expose]
noncomputable def gLuklem1 (ph : Wff) (ps : Wff) (ch : Wff)
    (hyp_luklem1_1 : Nominal.NPrf (.imp ph ps))
    (hyp_luklem1_2 : Nominal.NPrf (.imp ps ch)) : Nominal.NPrf (.imp ph ch) :=
  by
  have p0000 := @g_luk_1 ph ps ch
  have p0001 := Nominal.mp hyp_luklem1_1 p0000
  have p0002 := Nominal.mp hyp_luklem1_2 p0001
  exact p0002

/-- Checked nominal proof certificate identified upstream as `g_luklem2`. -/
@[expose]
noncomputable def gLuklem2 (ph : Wff) (ps : Wff) (ch : Wff) (th : Wff) :
    Nominal.NPrf (.imp (.imp ph (.neg ps)) (.imp (.imp (.imp ph ch) th) (.imp ps th))) :=
  by
  have p0000 := @g_luk_1 ph (.neg ps) ch
  have p0001 := @gLuk3 ps ch
  have p0002 := @g_luk_1 ps (.imp (.neg ps) ch) (.imp ph ch)
  have p0003 := Nominal.mp p0001 p0002
  have p0004 :=
    @gLuklem1 (.imp ph (.neg ps)) (.imp (.imp (.neg ps) ch) (.imp ph ch))
      (.imp ps (.imp ph ch)) p0000 p0003
  have p0005 := @g_luk_1 ps (.imp ph ch) th
  have p0006 :=
    @gLuklem1 (.imp ph (.neg ps)) (.imp ps (.imp ph ch))
      (.imp (.imp (.imp ph ch) th) (.imp ps th)) p0004 p0005
  exact p0006

/-- Checked nominal proof certificate identified upstream as `g_luklem3`. -/
@[expose]
noncomputable def gLuklem3 (ph : Wff) (ps : Wff) (ch : Wff) (th : Wff) :
    Nominal.NPrf (.imp ph (.imp (.imp (.imp (.neg ph) ps) ch) (.imp th ch))) :=
  by
  have p0000 := @gLuk3 ph (.neg th)
  have p0001 := @gLuklem2 (.neg ph) th ps ch
  have p0002 :=
    @gLuklem1 ph (.imp (.neg ph) (.neg th))
      (.imp (.imp (.imp (.neg ph) ps) ch) (.imp th ch)) p0000 p0001
  exact p0002

/-- Checked nominal proof certificate identified upstream as `g_luklem4`. -/
@[expose]
noncomputable def gLuklem4 (ph : Wff) (ps : Wff) :
    Nominal.NPrf (.imp (.imp (.imp (.imp (.neg ph) ph) ph) ps) ps) :=
  by
  have p0000 := @g_luk_2 (.imp (.imp (.neg ph) ph) ph)
  have p0001 := @g_luk_2 ph
  have p0002 :=
    @gLuklem3 (.imp (.imp (.neg ph) ph) ph) (.imp (.imp (.neg ph) ph) ph)
      (.imp (.imp (.neg ph) ph) ph) (.neg ps)
  have p0003 := Nominal.mp p0001 p0002
  have p0004 := Nominal.mp p0000 p0003
  have p0005 := @g_luk_1 (.neg ps) (.imp (.imp (.neg ph) ph) ph) ps
  have p0006 := Nominal.mp p0004 p0005
  have p0007 := @g_luk_2 ps
  have p0008 :=
    @gLuklem1 (.imp (.imp (.imp (.neg ph) ph) ph) ps) (.imp (.neg ps) ps) ps p0006 p0007
  exact p0008

/-- Checked nominal proof certificate identified upstream as `g_luklem5`. -/
@[expose]
noncomputable def gLuklem5 (ph : Wff) (ps : Wff) : Nominal.NPrf (.imp ph (.imp ps ph)) :=
  by
  have p0000 := @gLuklem3 ph ph ph ps
  have p0001 := @gLuklem4 ph (.imp ps ph)
  have p0002 :=
    @gLuklem1 ph (.imp (.imp (.imp (.neg ph) ph) ph) (.imp ps ph)) (.imp ps ph) p0000
      p0001
  exact p0002

/-- Checked nominal proof certificate identified upstream as `g_ax1`. -/
@[expose]
noncomputable def gAx1 (ph : Wff) (ps : Wff) : Nominal.NPrf (.imp ph (.imp ps ph)) :=
  by
  have p0000 := @gLuklem5 ph ps
  exact p0000

/-- Checked nominal proof certificate identified upstream as `g_alnex`. -/
@[expose]
noncomputable def gAlnex (ph : Wff) (x : Var) :
    Nominal.NPrf (synWb (.all x (.neg ph)) (.neg (synWex x ph))) :=
  by
  have p0000 := (Nominal.biimpRefl (synWex x ph))
  have p0001 := @gCon2bii (synWex x ph) (.all x (.neg ph)) p0000
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_gen2`. -/
@[expose]
noncomputable def gGen2 (ph : Wff) (x : Var) (y : Var) (hyp_gen2_1 : Nominal.NPrf ph) :
    Nominal.NPrf (.all x (.all y ph)) :=
  by
  have p0000 := Nominal.gen hyp_gen2_1 y
  have p0001 := Nominal.gen p0000 x
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_mpg`. -/
@[expose]
noncomputable def gMpg (ph : Wff) (ps : Wff) (x : Var)
    (hyp_mpg_1 : Nominal.NPrf (.imp (.all x ph) ps)) (hyp_mpg_2 : Nominal.NPrf ph) :
    Nominal.NPrf ps := by
  have p0000 := Nominal.gen hyp_mpg_2 x
  have p0001 := Nominal.mp p0000 hyp_mpg_1
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_mpgbi`. -/
@[expose]
noncomputable def gMpgbi (ph : Wff) (ps : Wff) (x : Var)
    (hyp_mpgbi_1 : Nominal.NPrf (synWb (.all x ph) ps)) (hyp_mpgbi_2 : Nominal.NPrf ph) :
    Nominal.NPrf ps := by
  have p0000 := Nominal.gen hyp_mpgbi_2 x
  have p0001 := @gMpbi (.all x ph) ps p0000 hyp_mpgbi_1
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_mpgbir`. -/
@[expose]
noncomputable def gMpgbir (ph : Wff) (ps : Wff) (x : Var)
    (hyp_mpgbir_1 : Nominal.NPrf (synWb ph (.all x ps)))
    (hyp_mpgbir_2 : Nominal.NPrf ps) : Nominal.NPrf ph :=
  by
  have p0000 := Nominal.gen hyp_mpgbir_2 x
  have p0001 := @gMpbir ph (.all x ps) p0000 hyp_mpgbir_1
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_nfi`. -/
@[expose]
noncomputable def gNfi (ph : Wff) (x : Var)
    (hyp_nfi_1 : Nominal.NPrf (.imp ph (.all x ph))) : Nominal.NPrf (synWnf x ph) :=
  by
  have p0000 := (Nominal.biimpRefl (synWnf x ph))
  have p0001 := @gMpgbir (synWnf x ph) (.imp ph (.all x ph)) x p0000 hyp_nfi_1
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_hbth`. -/
@[expose]
noncomputable def gHbth (ph : Wff) (x : Var) (hyp_hbth_1 : Nominal.NPrf ph) :
    Nominal.NPrf (.imp ph (.all x ph)) :=
  by
  have p0000 := Nominal.gen hyp_hbth_1 x
  have p0001 := @gA1i (.all x ph) ph p0000
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_nfth`. -/
@[expose]
noncomputable def gNfth (ph : Wff) (x : Var) (hyp_hbth_1 : Nominal.NPrf ph) :
    Nominal.NPrf (synWnf x ph) :=
  by
  have p0000 := @gHbth ph x hyp_hbth_1
  have p0001 := @gNfi ph x p0000
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_nftru`. -/
@[expose]
noncomputable def gNftru (x : Var) : Nominal.NPrf (synWnf x synWtru) :=
  by
  have p0000 := @gTru
  have p0001 := @gNfth synWtru x p0000
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_nex`. -/
@[expose]
noncomputable def gNex (ph : Wff) (x : Var) (hyp_nex_1 : Nominal.NPrf (.neg ph)) :
    Nominal.NPrf (.neg (synWex x ph)) :=
  by
  have p0000 := @gAlnex ph x
  have p0001 := @gMpgbi (.neg ph) (.neg (synWex x ph)) x p0000 hyp_nex_1
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_alim`. -/
@[expose]
noncomputable def gAlim (ph : Wff) (ps : Wff) (x : Var) :
    Nominal.NPrf (.imp (.all x (.imp ph ps)) (.imp (.all x ph) (.all x ps))) :=
  by
  have p0000 := Nominal.ax5 x ph ps
  exact p0000

/-- Checked nominal proof certificate identified upstream as `g_alimi`. -/
@[expose]
noncomputable def gAlimi (ph : Wff) (ps : Wff) (x : Var)
    (hyp_alimi_1 : Nominal.NPrf (.imp ph ps)) :
    Nominal.NPrf (.imp (.all x ph) (.all x ps)) :=
  by
  have p0000 := Nominal.ax5 x ph ps
  have p0001 := @gMpg (.imp ph ps) (.imp (.all x ph) (.all x ps)) x p0000 hyp_alimi_1
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_n_2alimi`. -/
@[expose]
noncomputable def gN2alimi (ph : Wff) (ps : Wff) (x : Var) (y : Var)
    (hyp_alimi_1 : Nominal.NPrf (.imp ph ps)) :
    Nominal.NPrf (.imp (.all x (.all y ph)) (.all x (.all y ps))) :=
  by
  have p0000 := @gAlimi ph ps y hyp_alimi_1
  have p0001 := @gAlimi (.all y ph) (.all y ps) x p0000
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_al2imi`. -/
@[expose]
noncomputable def gAl2imi (ph : Wff) (ps : Wff) (ch : Wff) (x : Var)
    (hyp_al2imi_1 : Nominal.NPrf (.imp ph (.imp ps ch))) :
    Nominal.NPrf (.imp (.all x ph) (.imp (.all x ps) (.all x ch))) :=
  by
  have p0000 := @gAlimi ph (.imp ps ch) x hyp_al2imi_1
  have p0001 := @gAlim ps ch x
  have p0002 :=
    @gSyl (.all x ph) (.all x (.imp ps ch)) (.imp (.all x ps) (.all x ch)) p0000 p0001
  exact p0002

/-- Checked nominal proof certificate identified upstream as `g_alanimi`. -/
@[expose]
noncomputable def gAlanimi (ph : Wff) (ps : Wff) (ch : Wff) (x : Var)
    (hyp_alanimi_1 : Nominal.NPrf (.imp (synWa ph ps) ch)) :
    Nominal.NPrf (.imp (synWa (.all x ph) (.all x ps)) (.all x ch)) :=
  by
  have p0000 := @gEx ph ps ch hyp_alanimi_1
  have p0001 := @gAl2imi ph ps ch x p0000
  have p0002 := @gImp (.all x ph) (.all x ps) (.all x ch) p0001
  exact p0002

/-- Checked nominal proof certificate identified upstream as `g_alimdh`. -/
@[expose]
noncomputable def gAlimdh (ph : Wff) (ps : Wff) (ch : Wff) (x : Var)
    (hyp_alimdh_1 : Nominal.NPrf (.imp ph (.all x ph)))
    (hyp_alimdh_2 : Nominal.NPrf (.imp ph (.imp ps ch))) :
    Nominal.NPrf (.imp ph (.imp (.all x ps) (.all x ch))) :=
  by
  have p0000 := @gAl2imi ph ps ch x hyp_alimdh_2
  have p0001 := @gSyl ph (.all x ph) (.imp (.all x ps) (.all x ch)) hyp_alimdh_1 p0000
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_albi`. -/
@[expose]
noncomputable def gAlbi (ph : Wff) (ps : Wff) (x : Var) :
    Nominal.NPrf (.imp (.all x (synWb ph ps)) (synWb (.all x ph) (.all x ps))) :=
  by
  have p0000 := @gBi1 ph ps
  have p0001 := @gAl2imi (synWb ph ps) ph ps x p0000
  have p0002 := @gBi2 ph ps
  have p0003 := @gAl2imi (synWb ph ps) ps ph x p0002
  have p0004 := @gImpbid (.all x (synWb ph ps)) (.all x ph) (.all x ps) p0001 p0003
  exact p0004

/-- Checked nominal proof certificate identified upstream as `g_alrimih`. -/
@[expose]
noncomputable def gAlrimih (ph : Wff) (ps : Wff) (x : Var)
    (hyp_alrimih_1 : Nominal.NPrf (.imp ph (.all x ph)))
    (hyp_alrimih_2 : Nominal.NPrf (.imp ph ps)) : Nominal.NPrf (.imp ph (.all x ps)) :=
  by
  have p0000 := @gAlimi ph ps x hyp_alrimih_2
  have p0001 := @gSyl ph (.all x ph) (.all x ps) hyp_alrimih_1 p0000
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_albii`. -/
@[expose]
noncomputable def gAlbii (ph : Wff) (ps : Wff) (x : Var)
    (hyp_albii_1 : Nominal.NPrf (synWb ph ps)) :
    Nominal.NPrf (synWb (.all x ph) (.all x ps)) :=
  by
  have p0000 := @gAlbi ph ps x
  have p0001 := @gMpg (synWb ph ps) (synWb (.all x ph) (.all x ps)) x p0000 hyp_albii_1
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_n_2albii`. -/
@[expose]
noncomputable def gN2albii (ph : Wff) (ps : Wff) (x : Var) (y : Var)
    (hyp_albii_1 : Nominal.NPrf (synWb ph ps)) :
    Nominal.NPrf (synWb (.all x (.all y ph)) (.all x (.all y ps))) :=
  by
  have p0000 := @gAlbii ph ps y hyp_albii_1
  have p0001 := @gAlbii (.all y ph) (.all y ps) x p0000
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_hbxfrbi`. -/
@[expose]
noncomputable def gHbxfrbi (ph : Wff) (ps : Wff) (x : Var)
    (hyp_hbxfrbi_1 : Nominal.NPrf (synWb ph ps))
    (hyp_hbxfrbi_2 : Nominal.NPrf (.imp ps (.all x ps))) :
    Nominal.NPrf (.imp ph (.all x ph)) :=
  by
  have p0000 := @gAlbii ph ps x hyp_hbxfrbi_1
  have p0001 :=
    @gN3imtr4i ps (.all x ps) ph (.all x ph) hyp_hbxfrbi_2 hyp_hbxfrbi_1 p0000
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_nfbii`. -/
@[expose]
noncomputable def gNfbii (ph : Wff) (ps : Wff) (x : Var)
    (hyp_nfbii_1 : Nominal.NPrf (synWb ph ps)) :
    Nominal.NPrf (synWb (synWnf x ph) (synWnf x ps)) :=
  by
  have p0000 := @gAlbii ph ps x hyp_nfbii_1
  have p0001 := @gImbi12i ph ps (.all x ph) (.all x ps) hyp_nfbii_1 p0000
  have p0002 := @gAlbii (.imp ph (.all x ph)) (.imp ps (.all x ps)) x p0001
  have p0003 := (Nominal.biimpRefl (synWnf x ph))
  have p0004 := (Nominal.biimpRefl (synWnf x ps))
  have p0005 :=
    @gN3bitr4i (.all x (.imp ph (.all x ph))) (.all x (.imp ps (.all x ps)))
      (synWnf x ph) (synWnf x ps) p0002 p0003 p0004
  exact p0005

/-- Checked nominal proof certificate identified upstream as `g_nfxfr`. -/
@[expose]
noncomputable def gNfxfr (ph : Wff) (ps : Wff) (x : Var)
    (hyp_nfbii_1 : Nominal.NPrf (synWb ph ps))
    (hyp_nfxfr_2 : Nominal.NPrf (synWnf x ps)) : Nominal.NPrf (synWnf x ph) :=
  by
  have p0000 := @gNfbii ph ps x hyp_nfbii_1
  have p0001 := @gMpbir (synWnf x ph) (synWnf x ps) hyp_nfxfr_2 p0000
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_nfxfrd`. -/
@[expose]
noncomputable def gNfxfrd (ph : Wff) (ps : Wff) (ch : Wff) (x : Var)
    (hyp_nfbii_1 : Nominal.NPrf (synWb ph ps))
    (hyp_nfxfrd_2 : Nominal.NPrf (.imp ch (synWnf x ps))) :
    Nominal.NPrf (.imp ch (synWnf x ph)) :=
  by
  have p0000 := @gNfbii ph ps x hyp_nfbii_1
  have p0001 := @gSylibr ch (synWnf x ps) (synWnf x ph) hyp_nfxfrd_2 p0000
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_alex`. -/
@[expose]
noncomputable def gAlex (ph : Wff) (x : Var) :
    Nominal.NPrf (synWb (.all x ph) (.neg (synWex x (.neg ph)))) :=
  by
  have p0000 := @gNotnot ph
  have p0001 := @gAlbii ph (.neg (.neg ph)) x p0000
  have p0002 := @gAlnex (.neg ph) x
  have p0003 :=
    @gBitri (.all x ph) (.all x (.neg (.neg ph))) (.neg (synWex x (.neg ph))) p0001
      p0002
  exact p0003

/-- Checked nominal proof certificate identified upstream as `g_n_2nalexn`. -/
@[expose]
noncomputable def gN2nalexn (ph : Wff) (x : Var) (y : Var) :
    Nominal.NPrf (synWb (.neg (.all x (.all y ph))) (synWex x (synWex y (.neg ph)))) :=
  by
  have p0000 := (Nominal.biimpRefl (synWex x (synWex y (.neg ph))))
  have p0001 := @gAlex ph y
  have p0002 := @gAlbii (.all y ph) (.neg (synWex y (.neg ph))) x p0001
  have p0003 :=
    @gXchbinxr (synWex x (synWex y (.neg ph))) (.all x (.neg (synWex y (.neg ph))))
      (.all x (.all y ph)) p0000 p0002
  have p0004 :=
    @gBicomi (synWex x (synWex y (.neg ph))) (.neg (.all x (.all y ph))) p0003
  exact p0004

/-- Checked nominal proof certificate identified upstream as `g_exnal`. -/
@[expose]
noncomputable def gExnal (ph : Wff) (x : Var) :
    Nominal.NPrf (synWb (synWex x (.neg ph)) (.neg (.all x ph))) :=
  by
  have p0000 := @gAlex ph x
  have p0001 := @gCon2bii (.all x ph) (synWex x (.neg ph)) p0000
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_exim`. -/
@[expose]
noncomputable def gExim (ph : Wff) (ps : Wff) (x : Var) :
    Nominal.NPrf (.imp (.all x (.imp ph ps)) (.imp (synWex x ph) (synWex x ps))) :=
  by
  have p0000 := @gCon3 ph ps
  have p0001 := @gAl2imi (.imp ph ps) (.neg ps) (.neg ph) x p0000
  have p0002 := @gAlnex ps x
  have p0003 := @gAlnex ph x
  have p0004 :=
    @gN3imtr3g (.all x (.imp ph ps)) (.all x (.neg ps)) (.all x (.neg ph))
      (.neg (synWex x ps)) (.neg (synWex x ph)) p0001 p0002 p0003
  have p0005 := @gCon4d (.all x (.imp ph ps)) (synWex x ps) (synWex x ph) p0004
  exact p0005

/-- Checked nominal proof certificate identified upstream as `g_eximi`. -/
@[expose]
noncomputable def gEximi (ph : Wff) (ps : Wff) (x : Var)
    (hyp_eximi_1 : Nominal.NPrf (.imp ph ps)) :
    Nominal.NPrf (.imp (synWex x ph) (synWex x ps)) :=
  by
  have p0000 := @gExim ph ps x
  have p0001 :=
    @gMpg (.imp ph ps) (.imp (synWex x ph) (synWex x ps)) x p0000 hyp_eximi_1
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_n_2eximi`. -/
@[expose]
noncomputable def gN2eximi (ph : Wff) (ps : Wff) (x : Var) (y : Var)
    (hyp_eximi_1 : Nominal.NPrf (.imp ph ps)) :
    Nominal.NPrf (.imp (synWex x (synWex y ph)) (synWex x (synWex y ps))) :=
  by
  have p0000 := @gEximi ph ps y hyp_eximi_1
  have p0001 := @gEximi (synWex y ph) (synWex y ps) x p0000
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_alinexa`. -/
@[expose]
noncomputable def gAlinexa (ph : Wff) (ps : Wff) (x : Var) :
    Nominal.NPrf
      (synWb (.all x (.imp ph (.neg ps))) (.neg (synWex x (synWa ph ps)))) :=
  by
  have p0000 := @gImnan ph ps
  have p0001 := @gAlbii (.imp ph (.neg ps)) (.neg (synWa ph ps)) x p0000
  have p0002 := @gAlnex (synWa ph ps) x
  have p0003 :=
    @gBitri (.all x (.imp ph (.neg ps))) (.all x (.neg (synWa ph ps)))
      (.neg (synWex x (synWa ph ps))) p0001 p0002
  exact p0003

/-- Checked nominal proof certificate identified upstream as `g_exbi`. -/
@[expose]
noncomputable def gExbi (ph : Wff) (ps : Wff) (x : Var) :
    Nominal.NPrf (.imp (.all x (synWb ph ps)) (synWb (synWex x ph) (synWex x ps))) :=
  by
  have p0000 := @gBi1 ph ps
  have p0001 := @gAlimi (synWb ph ps) (.imp ph ps) x p0000
  have p0002 := @gExim ph ps x
  have p0003 :=
    @gSyl (.all x (synWb ph ps)) (.all x (.imp ph ps))
      (.imp (synWex x ph) (synWex x ps)) p0001 p0002
  have p0004 := @gBi2 ph ps
  have p0005 := @gAlimi (synWb ph ps) (.imp ps ph) x p0004
  have p0006 := @gExim ps ph x
  have p0007 :=
    @gSyl (.all x (synWb ph ps)) (.all x (.imp ps ph))
      (.imp (synWex x ps) (synWex x ph)) p0005 p0006
  have p0008 :=
    @gImpbid (.all x (synWb ph ps)) (synWex x ph) (synWex x ps) p0003 p0007
  exact p0008

/-- Checked nominal proof certificate identified upstream as `g_exbii`. -/
@[expose]
noncomputable def gExbii (ph : Wff) (ps : Wff) (x : Var)
    (hyp_exbii_1 : Nominal.NPrf (synWb ph ps)) :
    Nominal.NPrf (synWb (synWex x ph) (synWex x ps)) :=
  by
  have p0000 := @gExbi ph ps x
  have p0001 :=
    @gMpg (synWb ph ps) (synWb (synWex x ph) (synWex x ps)) x p0000 hyp_exbii_1
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_n_2exbii`. -/
@[expose]
noncomputable def gN2exbii (ph : Wff) (ps : Wff) (x : Var) (y : Var)
    (hyp_n_2exbii_1 : Nominal.NPrf (synWb ph ps)) :
    Nominal.NPrf (synWb (synWex x (synWex y ph)) (synWex x (synWex y ps))) :=
  by
  have p0000 := @gExbii ph ps y hyp_n_2exbii_1
  have p0001 := @gExbii (synWex y ph) (synWex y ps) x p0000
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_n_3exbii`. -/
@[expose]
noncomputable def gN3exbii (ph : Wff) (ps : Wff) (x : Var) (y : Var) (z : Var)
    (hyp_n_3exbii_1 : Nominal.NPrf (synWb ph ps)) :
    Nominal.NPrf
      (synWb (synWex x (synWex y (synWex z ph))) (synWex x (synWex y (synWex z ps)))) :=
  by
  have p0000 := @gExbii ph ps z hyp_n_3exbii_1
  have p0001 := @gN2exbii (synWex z ph) (synWex z ps) x y p0000
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_exanali`. -/
@[expose]
noncomputable def gExanali (ph : Wff) (ps : Wff) (x : Var) :
    Nominal.NPrf
      (synWb (synWex x (synWa ph (.neg ps))) (.neg (.all x (.imp ph ps)))) :=
  by
  have p0000 := @gAnnim ph ps
  have p0001 := @gExbii (synWa ph (.neg ps)) (.neg (.imp ph ps)) x p0000
  have p0002 := @gExnal (.imp ph ps) x
  have p0003 :=
    @gBitri (synWex x (synWa ph (.neg ps))) (synWex x (.neg (.imp ph ps)))
      (.neg (.all x (.imp ph ps))) p0001 p0002
  exact p0003

/-- Checked nominal proof certificate identified upstream as `g_exancom`. -/
@[expose]
noncomputable def gExancom (ph : Wff) (ps : Wff) (x : Var) :
    Nominal.NPrf (synWb (synWex x (synWa ph ps)) (synWex x (synWa ps ph))) :=
  by
  have p0000 := @gAncom ph ps
  have p0001 := @gExbii (synWa ph ps) (synWa ps ph) x p0000
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_alrimdh`. -/
@[expose]
noncomputable def gAlrimdh (ph : Wff) (ps : Wff) (ch : Wff) (x : Var)
    (hyp_alrimdh_1 : Nominal.NPrf (.imp ph (.all x ph)))
    (hyp_alrimdh_2 : Nominal.NPrf (.imp ps (.all x ps)))
    (hyp_alrimdh_3 : Nominal.NPrf (.imp ph (.imp ps ch))) :
    Nominal.NPrf (.imp ph (.imp ps (.all x ch))) :=
  by
  have p0000 := @gAlimdh ph ps ch x hyp_alrimdh_1 hyp_alrimdh_3
  have p0001 := @gSyl5 ps (.all x ps) ph (.all x ch) hyp_alrimdh_2 p0000
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_eximdh`. -/
@[expose]
noncomputable def gEximdh (ph : Wff) (ps : Wff) (ch : Wff) (x : Var)
    (hyp_eximdh_1 : Nominal.NPrf (.imp ph (.all x ph)))
    (hyp_eximdh_2 : Nominal.NPrf (.imp ph (.imp ps ch))) :
    Nominal.NPrf (.imp ph (.imp (synWex x ps) (synWex x ch))) :=
  by
  have p0000 := @gAlrimih ph (.imp ps ch) x hyp_eximdh_1 hyp_eximdh_2
  have p0001 := @gExim ps ch x
  have p0002 :=
    @gSyl ph (.all x (.imp ps ch)) (.imp (synWex x ps) (synWex x ch)) p0000 p0001
  exact p0002

/-- Checked nominal proof certificate identified upstream as `g_nexdh`. -/
@[expose]
noncomputable def gNexdh (ph : Wff) (ps : Wff) (x : Var)
    (hyp_nexdh_1 : Nominal.NPrf (.imp ph (.all x ph)))
    (hyp_nexdh_2 : Nominal.NPrf (.imp ph (.neg ps))) :
    Nominal.NPrf (.imp ph (.neg (synWex x ps))) :=
  by
  have p0000 := @gAlrimih ph (.neg ps) x hyp_nexdh_1 hyp_nexdh_2
  have p0001 := @gAlnex ps x
  have p0002 := @gSylib ph (.all x (.neg ps)) (.neg (synWex x ps)) p0000 p0001
  exact p0002

/-- Checked nominal proof certificate identified upstream as `g_albidh`. -/
@[expose]
noncomputable def gAlbidh (ph : Wff) (ps : Wff) (ch : Wff) (x : Var)
    (hyp_albidh_1 : Nominal.NPrf (.imp ph (.all x ph)))
    (hyp_albidh_2 : Nominal.NPrf (.imp ph (synWb ps ch))) :
    Nominal.NPrf (.imp ph (synWb (.all x ps) (.all x ch))) :=
  by
  have p0000 := @gAlrimih ph (synWb ps ch) x hyp_albidh_1 hyp_albidh_2
  have p0001 := @gAlbi ps ch x
  have p0002 :=
    @gSyl ph (.all x (synWb ps ch)) (synWb (.all x ps) (.all x ch)) p0000 p0001
  exact p0002

/-- Checked nominal proof certificate identified upstream as `g_exbidh`. -/
@[expose]
noncomputable def gExbidh (ph : Wff) (ps : Wff) (ch : Wff) (x : Var)
    (hyp_exbidh_1 : Nominal.NPrf (.imp ph (.all x ph)))
    (hyp_exbidh_2 : Nominal.NPrf (.imp ph (synWb ps ch))) :
    Nominal.NPrf (.imp ph (synWb (synWex x ps) (synWex x ch))) :=
  by
  have p0000 := @gAlrimih ph (synWb ps ch) x hyp_exbidh_1 hyp_exbidh_2
  have p0001 := @gExbi ps ch x
  have p0002 :=
    @gSyl ph (.all x (synWb ps ch)) (synWb (synWex x ps) (synWex x ch)) p0000 p0001
  exact p0002

/-- Checked nominal proof certificate identified upstream as `g_exsimpl`. -/
@[expose]
noncomputable def gExsimpl (ph : Wff) (ps : Wff) (x : Var) :
    Nominal.NPrf (.imp (synWex x (synWa ph ps)) (synWex x ph)) :=
  by
  have p0000 := @gSimpl ph ps
  have p0001 := @gEximi (synWa ph ps) ph x p0000
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_n_19_26`. -/
@[expose]
noncomputable def gN1926 (ph : Wff) (ps : Wff) (x : Var) :
    Nominal.NPrf (synWb (.all x (synWa ph ps)) (synWa (.all x ph) (.all x ps))) :=
  by
  have p0000 := @gSimpl ph ps
  have p0001 := @gAlimi (synWa ph ps) ph x p0000
  have p0002 := @gSimpr ph ps
  have p0003 := @gAlimi (synWa ph ps) ps x p0002
  have p0004 := @gJca (.all x (synWa ph ps)) (.all x ph) (.all x ps) p0001 p0003
  have p0005 := @gId (synWa ph ps)
  have p0006 := @gAlanimi ph ps (synWa ph ps) x p0005
  have p0007 :=
    @gImpbii (.all x (synWa ph ps)) (synWa (.all x ph) (.all x ps)) p0004 p0006
  exact p0007

/-- Checked nominal proof certificate identified upstream as `g_n_19_29`. -/
@[expose]
noncomputable def gN1929 (ph : Wff) (ps : Wff) (x : Var) :
    Nominal.NPrf (.imp (synWa (.all x ph) (synWex x ps)) (synWex x (synWa ph ps))) :=
  by
  have p0000 := @g_pm3_2 ph ps
  have p0001 := @gAlimi ph (.imp ps (synWa ph ps)) x p0000
  have p0002 := @gExim ps (synWa ph ps) x
  have p0003 :=
    @gSyl (.all x ph) (.all x (.imp ps (synWa ph ps)))
      (.imp (synWex x ps) (synWex x (synWa ph ps))) p0001 p0002
  have p0004 := @gImp (.all x ph) (synWex x ps) (synWex x (synWa ph ps)) p0003
  exact p0004

/-- Checked nominal proof certificate identified upstream as `g_n_19_29r`. -/
@[expose]
noncomputable def gN1929r (ph : Wff) (ps : Wff) (x : Var) :
    Nominal.NPrf (.imp (synWa (synWex x ph) (.all x ps)) (synWex x (synWa ph ps))) :=
  by
  have p0000 := @gN1929 ps ph x
  have p0001 := @gAncoms (.all x ps) (synWex x ph) (synWex x (synWa ps ph)) p0000
  have p0002 := @gExancom ph ps x
  have p0003 :=
    @gSylibr (synWa (synWex x ph) (.all x ps)) (synWex x (synWa ps ph))
      (synWex x (synWa ph ps)) p0001 p0002
  exact p0003

/-- Checked nominal proof certificate identified upstream as `g_n_19_35`. -/
@[expose]
noncomputable def gN1935 (ph : Wff) (ps : Wff) (x : Var) :
    Nominal.NPrf (synWb (synWex x (.imp ph ps)) (.imp (.all x ph) (synWex x ps))) :=
  by
  have p0000 := @gN1926 ph (.neg ps) x
  have p0001 := @gAnnim ph ps
  have p0002 := @gAlbii (synWa ph (.neg ps)) (.neg (.imp ph ps)) x p0001
  have p0003 := @gAlnex ps x
  have p0004 := @gAnbi2i (.all x (.neg ps)) (.neg (synWex x ps)) (.all x ph) p0003
  have p0005 :=
    @gN3bitr3i (.all x (synWa ph (.neg ps))) (synWa (.all x ph) (.all x (.neg ps)))
      (.all x (.neg (.imp ph ps))) (synWa (.all x ph) (.neg (synWex x ps))) p0000 p0002
      p0004
  have p0006 := @gAlnex (.imp ph ps) x
  have p0007 := @gAnnim (.all x ph) (synWex x ps)
  have p0008 :=
    @gN3bitr3i (.all x (.neg (.imp ph ps))) (synWa (.all x ph) (.neg (synWex x ps)))
      (.neg (synWex x (.imp ph ps))) (.neg (.imp (.all x ph) (synWex x ps))) p0005 p0006
      p0007
  have p0009 :=
    @gCon4bii (synWex x (.imp ph ps)) (.imp (.all x ph) (synWex x ps)) p0008
  exact p0009

/-- Checked nominal proof certificate identified upstream as `g_n_19_35i`. -/
@[expose]
noncomputable def gN1935i (ph : Wff) (ps : Wff) (x : Var)
    (hyp_n_19_35i_1 : Nominal.NPrf (synWex x (.imp ph ps))) :
    Nominal.NPrf (.imp (.all x ph) (synWex x ps)) :=
  by
  have p0000 := @gN1935 ph ps x
  have p0001 :=
    @gMpbi (synWex x (.imp ph ps)) (.imp (.all x ph) (synWex x ps)) hyp_n_19_35i_1
      p0000
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_n_19_43`. -/
@[expose]
noncomputable def gN1943 (ph : Wff) (ps : Wff) (x : Var) :
    Nominal.NPrf
      (synWb (synWex x (synWo ph ps)) (synWo (synWex x ph) (synWex x ps))) :=
  by
  have p0000 := (Nominal.biimpRefl (synWo ph ps))
  have p0001 := @gExbii (synWo ph ps) (.imp (.neg ph) ps) x p0000
  have p0002 := @gN1935 (.neg ph) ps x
  have p0003 := @gAlnex ph x
  have p0004 := @gImbi1i (.all x (.neg ph)) (.neg (synWex x ph)) (synWex x ps) p0003
  have p0005 :=
    @gN3bitri (synWex x (synWo ph ps)) (synWex x (.imp (.neg ph) ps))
      (.imp (.all x (.neg ph)) (synWex x ps)) (.imp (.neg (synWex x ph)) (synWex x ps))
      p0001 p0002 p0004
  have p0006 := (Nominal.biimpRefl (synWo (synWex x ph) (synWex x ps)))
  have p0007 :=
    @gBitr4i (synWex x (synWo ph ps)) (.imp (.neg (synWex x ph)) (synWex x ps))
      (synWo (synWex x ph) (synWex x ps)) p0005 p0006
  exact p0007

/-- Checked nominal proof certificate identified upstream as `g_n_19_40`. -/
@[expose]
noncomputable def gN1940 (ph : Wff) (ps : Wff) (x : Var) :
    Nominal.NPrf
      (.imp (synWex x (synWa ph ps)) (synWa (synWex x ph) (synWex x ps))) :=
  by
  have p0000 := @gExsimpl ph ps x
  have p0001 := @gSimpr ph ps
  have p0002 := @gEximi (synWa ph ps) ps x p0001
  have p0003 :=
    @gJca (synWex x (synWa ph ps)) (synWex x ph) (synWex x ps) p0000 p0002
  exact p0003

/-- Checked nominal proof certificate identified upstream as `g_albiim`. -/
@[expose]
noncomputable def gAlbiim (ph : Wff) (ps : Wff) (x : Var) :
    Nominal.NPrf
      (synWb (.all x (synWb ph ps)) (synWa (.all x (.imp ph ps)) (.all x (.imp ps ph)))) :=
  by
  have p0000 := @gDfbi2 ph ps
  have p0001 := @gAlbii (synWb ph ps) (synWa (.imp ph ps) (.imp ps ph)) x p0000
  have p0002 := @gN1926 (.imp ph ps) (.imp ps ph) x
  have p0003 :=
    @gBitri (.all x (synWb ph ps)) (.all x (synWa (.imp ph ps) (.imp ps ph)))
      (synWa (.all x (.imp ph ps)) (.all x (.imp ps ph))) p0001 p0002
  exact p0003

/-- Checked nominal proof certificate identified upstream as `g_n_2albiim`. -/
@[expose]
noncomputable def gN2albiim (ph : Wff) (ps : Wff) (x : Var) (y : Var) :
    Nominal.NPrf
      (synWb (.all x (.all y (synWb ph ps)))
        (synWa (.all x (.all y (.imp ph ps))) (.all x (.all y (.imp ps ph))))) :=
  by
  have p0000 := @gAlbiim ph ps y
  have p0001 :=
    @gAlbii (.all y (synWb ph ps)) (synWa (.all y (.imp ph ps)) (.all y (.imp ps ph)))
      x p0000
  have p0002 := @gN1926 (.all y (.imp ph ps)) (.all y (.imp ps ph)) x
  have p0003 :=
    @gBitri (.all x (.all y (synWb ph ps)))
      (.all x (synWa (.all y (.imp ph ps)) (.all y (.imp ps ph))))
      (synWa (.all x (.all y (.imp ph ps))) (.all x (.all y (.imp ps ph)))) p0001 p0002
  exact p0003

/-- Checked nominal proof certificate identified upstream as `g_exintrbi`. -/
@[expose]
noncomputable def gExintrbi (ph : Wff) (ps : Wff) (x : Var) :
    Nominal.NPrf
      (.imp (.all x (.imp ph ps)) (synWb (synWex x ph) (synWex x (synWa ph ps)))) :=
  by
  have p0000 := @gPm471 ph ps
  have p0001 := @gAlbii (.imp ph ps) (synWb ph (synWa ph ps)) x p0000
  have p0002 := @gExbi ph (synWa ph ps) x
  have p0003 :=
    @gSylbi (.all x (.imp ph ps)) (.all x (synWb ph (synWa ph ps)))
      (synWb (synWex x ph) (synWex x (synWa ph ps))) p0001 p0002
  exact p0003

/-- Checked nominal proof certificate identified upstream as `g_exintr`. -/
@[expose]
noncomputable def gExintr (ph : Wff) (ps : Wff) (x : Var) :
    Nominal.NPrf
      (.imp (.all x (.imp ph ps)) (.imp (synWex x ph) (synWex x (synWa ph ps)))) :=
  by
  have p0000 := @gExintrbi ph ps x
  have p0001 :=
    @gBiimpd (.all x (.imp ph ps)) (synWex x ph) (synWex x (synWa ph ps)) p0000
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_a17d`. -/
@[expose]
noncomputable def gA17d (ph : Wff) (ps : Wff) (x : Var) (dv_ps_x : x ∉ ps.fv) :
    Nominal.NPrf (.imp ph (.imp ps (.all x ps))) :=
  by
  let proofSupport : Finset Var := ph.fv ∪ ps.fv ∪ ({ x } : Finset Var)
  have p0000 :=
    Nominal.ax17 ps x
      (by
        first
        | (aesop))
  have p0001 := @gA1i (.imp ps (.all x ps)) ph p0000
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_ax17e`. -/
@[expose]
noncomputable def gAx17e (ph : Wff) (x : Var) (dv_ph_x : x ∉ ph.fv) :
    Nominal.NPrf (.imp (synWex x ph) ph) :=
  by
  let proofSupport : Finset Var := ph.fv ∪ ({ x } : Finset Var)
  have p0000 := (Nominal.biimpRefl (synWex x ph))
  have p0001 :=
    Nominal.ax17 (.neg ph) x
      (by
        first
        |
          (simp (config :=
              {
                failIfUnchanged :=
                  false }) only [NFChoice.Compiler.CoreFVSimp.fv_wff_neg] at ⊢;
            aesop))
  have p0002 := @gCon1i ph (.all x (.neg ph)) p0001
  have p0003 := @gSylbi (synWex x ph) (.neg (.all x (.neg ph))) ph p0000 p0002
  exact p0003

/-- Checked nominal proof certificate identified upstream as `g_nfv`. -/
@[expose]
noncomputable def gNfv (ph : Wff) (x : Var) (dv_ph_x : x ∉ ph.fv) :
    Nominal.NPrf (synWnf x ph) :=
  by
  let proofSupport : Finset Var := ph.fv ∪ ({ x } : Finset Var)
  have p0000 :=
    Nominal.ax17 ph x
      (by
        first
        | (aesop))
  have p0001 := @gNfi ph x p0000
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_nfvd`. -/
@[expose]
noncomputable def gNfvd (ph : Wff) (ps : Wff) (x : Var) (dv_ps_x : x ∉ ps.fv) :
    Nominal.NPrf (.imp ph (synWnf x ps)) :=
  by
  let proofSupport : Finset Var := ph.fv ∪ ps.fv ∪ ({ x } : Finset Var)
  have p0000 :=
    @gNfv ps x
      (by
        first
        | (aesop))
  have p0001 := @gA1i (synWnf x ps) ph p0000
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_alimdv`. -/
@[expose]
noncomputable def gAlimdv (ph : Wff) (ps : Wff) (ch : Wff) (x : Var)
    (dv_ph_x : x ∉ ph.fv) (hyp_alimdv_1 : Nominal.NPrf (.imp ph (.imp ps ch))) :
    Nominal.NPrf (.imp ph (.imp (.all x ps) (.all x ch))) :=
  by
  let proofSupport : Finset Var := ph.fv ∪ ps.fv ∪ ch.fv ∪ ({ x } : Finset Var)
  have p0000 :=
    Nominal.ax17 ph x
      (by
        first
        | (aesop))
  have p0001 := @gAlimdh ph ps ch x p0000 hyp_alimdv_1
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_eximdv`. -/
@[expose]
noncomputable def gEximdv (ph : Wff) (ps : Wff) (ch : Wff) (x : Var)
    (dv_ph_x : x ∉ ph.fv) (hyp_alimdv_1 : Nominal.NPrf (.imp ph (.imp ps ch))) :
    Nominal.NPrf (.imp ph (.imp (synWex x ps) (synWex x ch))) :=
  by
  let proofSupport : Finset Var := ph.fv ∪ ps.fv ∪ ch.fv ∪ ({ x } : Finset Var)
  have p0000 :=
    Nominal.ax17 ph x
      (by
        first
        | (aesop))
  have p0001 := @gEximdh ph ps ch x p0000 hyp_alimdv_1
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_n_2eximdv`. -/
@[expose]
noncomputable def gN2eximdv (ph : Wff) (ps : Wff) (ch : Wff) (x : Var) (y : Var)
    (dv_ph_x : x ∉ ph.fv) (dv_ph_y : y ∉ ph.fv)
    (hyp_n_2alimdv_1 : Nominal.NPrf (.imp ph (.imp ps ch))) :
    Nominal.NPrf (.imp ph (.imp (synWex x (synWex y ps)) (synWex x (synWex y ch)))) :=
  by
  let proofSupport : Finset Var :=
    ph.fv ∪ ps.fv ∪ ch.fv ∪ ({ x } : Finset Var) ∪ ({ y } : Finset Var)
  have p0000 :=
    @gEximdv ph ps ch y
      (by
        first
        | (aesop))
      hyp_n_2alimdv_1
  have p0001 :=
    @gEximdv ph (synWex y ps) (synWex y ch) x
      (by
        first
        | (aesop))
      p0000
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_albidv`. -/
@[expose]
noncomputable def gAlbidv (ph : Wff) (ps : Wff) (ch : Wff) (x : Var)
    (dv_ph_x : x ∉ ph.fv) (hyp_albidv_1 : Nominal.NPrf (.imp ph (synWb ps ch))) :
    Nominal.NPrf (.imp ph (synWb (.all x ps) (.all x ch))) :=
  by
  let proofSupport : Finset Var := ph.fv ∪ ps.fv ∪ ch.fv ∪ ({ x } : Finset Var)
  have p0000 :=
    Nominal.ax17 ph x
      (by
        first
        | (aesop))
  have p0001 := @gAlbidh ph ps ch x p0000 hyp_albidv_1
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_exbidv`. -/
@[expose]
noncomputable def gExbidv (ph : Wff) (ps : Wff) (ch : Wff) (x : Var)
    (dv_ph_x : x ∉ ph.fv) (hyp_albidv_1 : Nominal.NPrf (.imp ph (synWb ps ch))) :
    Nominal.NPrf (.imp ph (synWb (synWex x ps) (synWex x ch))) :=
  by
  let proofSupport : Finset Var := ph.fv ∪ ps.fv ∪ ch.fv ∪ ({ x } : Finset Var)
  have p0000 :=
    Nominal.ax17 ph x
      (by
        first
        | (aesop))
  have p0001 := @gExbidh ph ps ch x p0000 hyp_albidv_1
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_n_2albidv`. -/
@[expose]
noncomputable def gN2albidv (ph : Wff) (ps : Wff) (ch : Wff) (x : Var) (y : Var)
    (dv_ph_x : x ∉ ph.fv) (dv_ph_y : y ∉ ph.fv)
    (hyp_n_2albidv_1 : Nominal.NPrf (.imp ph (synWb ps ch))) :
    Nominal.NPrf (.imp ph (synWb (.all x (.all y ps)) (.all x (.all y ch)))) :=
  by
  let proofSupport : Finset Var :=
    ph.fv ∪ ps.fv ∪ ch.fv ∪ ({ x } : Finset Var) ∪ ({ y } : Finset Var)
  have p0000 :=
    @gAlbidv ph ps ch y
      (by
        first
        | (aesop))
      hyp_n_2albidv_1
  have p0001 :=
    @gAlbidv ph (.all y ps) (.all y ch) x
      (by
        first
        | (aesop))
      p0000
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_n_2exbidv`. -/
@[expose]
noncomputable def gN2exbidv (ph : Wff) (ps : Wff) (ch : Wff) (x : Var) (y : Var)
    (dv_ph_x : x ∉ ph.fv) (dv_ph_y : y ∉ ph.fv)
    (hyp_n_2albidv_1 : Nominal.NPrf (.imp ph (synWb ps ch))) :
    Nominal.NPrf
      (.imp ph (synWb (synWex x (synWex y ps)) (synWex x (synWex y ch)))) :=
  by
  let proofSupport : Finset Var :=
    ph.fv ∪ ps.fv ∪ ch.fv ∪ ({ x } : Finset Var) ∪ ({ y } : Finset Var)
  have p0000 :=
    @gExbidv ph ps ch y
      (by
        first
        | (aesop))
      hyp_n_2albidv_1
  have p0001 :=
    @gExbidv ph (synWex y ps) (synWex y ch) x
      (by
        first
        | (aesop))
      p0000
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_n_3exbidv`. -/
@[expose]
noncomputable def gN3exbidv (ph : Wff) (ps : Wff) (ch : Wff) (x : Var) (y : Var)
    (z : Var) (dv_ph_x : x ∉ ph.fv) (dv_ph_y : y ∉ ph.fv) (dv_ph_z : z ∉ ph.fv)
    (hyp_n_3exbidv_1 : Nominal.NPrf (.imp ph (synWb ps ch))) :
    Nominal.NPrf
      (.imp ph (synWb (synWex x (synWex y (synWex z ps)))
          (synWex x (synWex y (synWex z ch))))) :=
  by
  let proofSupport : Finset Var :=
    ph.fv ∪ ps.fv ∪ ch.fv ∪ ({ x } : Finset Var) ∪ ({ y } : Finset Var) ∪
      ({ z } : Finset Var)
  have p0000 :=
    @gExbidv ph ps ch z
      (by
        first
        | (aesop))
      hyp_n_3exbidv_1
  have p0001 :=
    @gN2exbidv ph (synWex z ps) (synWex z ch) x y
      (by
        first
        | (aesop))
      (by
        first
        | (aesop))
      p0000
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_alrimiv`. -/
@[expose]
noncomputable def gAlrimiv (ph : Wff) (ps : Wff) (x : Var) (dv_ph_x : x ∉ ph.fv)
    (hyp_alrimiv_1 : Nominal.NPrf (.imp ph ps)) : Nominal.NPrf (.imp ph (.all x ps)) :=
  by
  let proofSupport : Finset Var := ph.fv ∪ ps.fv ∪ ({ x } : Finset Var)
  have p0000 :=
    Nominal.ax17 ph x
      (by
        first
        | (aesop))
  have p0001 := @gAlrimih ph ps x p0000 hyp_alrimiv_1
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_alrimivv`. -/
@[expose]
noncomputable def gAlrimivv (ph : Wff) (ps : Wff) (x : Var) (y : Var)
    (dv_ph_x : x ∉ ph.fv) (dv_ph_y : y ∉ ph.fv)
    (hyp_alrimivv_1 : Nominal.NPrf (.imp ph ps)) :
    Nominal.NPrf (.imp ph (.all x (.all y ps))) :=
  by
  let proofSupport : Finset Var :=
    ph.fv ∪ ps.fv ∪ ({ x } : Finset Var) ∪ ({ y } : Finset Var)
  have p0000 :=
    @gAlrimiv ph ps y
      (by
        first
        | (aesop))
      hyp_alrimivv_1
  have p0001 :=
    @gAlrimiv ph (.all y ps) x
      (by
        first
        | (aesop))
      p0000
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_alrimdv`. -/
@[expose]
noncomputable def gAlrimdv (ph : Wff) (ps : Wff) (ch : Wff) (x : Var)
    (dv_ph_x : x ∉ ph.fv) (dv_ps_x : x ∉ ps.fv)
    (hyp_alrimdv_1 : Nominal.NPrf (.imp ph (.imp ps ch))) :
    Nominal.NPrf (.imp ph (.imp ps (.all x ch))) :=
  by
  let proofSupport : Finset Var := ph.fv ∪ ps.fv ∪ ch.fv ∪ ({ x } : Finset Var)
  have p0000 :=
    Nominal.ax17 ph x
      (by
        first
        | (aesop))
  have p0001 :=
    Nominal.ax17 ps x
      (by
        first
        | (aesop))
  have p0002 := @gAlrimdh ph ps ch x p0000 p0001 hyp_alrimdv_1
  exact p0002

/-- Checked nominal proof certificate identified upstream as `g_exlimiv`. -/
@[expose]
noncomputable def gExlimiv (ph : Wff) (ps : Wff) (x : Var) (dv_ps_x : x ∉ ps.fv)
    (hyp_exlimiv_1 : Nominal.NPrf (.imp ph ps)) : Nominal.NPrf (.imp (synWex x ph) ps) :=
  by
  let proofSupport : Finset Var := ph.fv ∪ ps.fv ∪ ({ x } : Finset Var)
  have p0000 := @gEximi ph ps x hyp_exlimiv_1
  have p0001 :=
    @gAx17e ps x
      (by
        first
        | (aesop))
  have p0002 := @gSyl (synWex x ph) (synWex x ps) ps p0000 p0001
  exact p0002

/-- Checked nominal proof certificate identified upstream as `g_exlimivv`. -/
@[expose]
noncomputable def gExlimivv (ph : Wff) (ps : Wff) (x : Var) (y : Var)
    (dv_ps_x : x ∉ ps.fv) (dv_ps_y : y ∉ ps.fv)
    (hyp_exlimivv_1 : Nominal.NPrf (.imp ph ps)) :
    Nominal.NPrf (.imp (synWex x (synWex y ph)) ps) :=
  by
  let proofSupport : Finset Var :=
    ph.fv ∪ ps.fv ∪ ({ x } : Finset Var) ∪ ({ y } : Finset Var)
  have p0000 :=
    @gExlimiv ph ps y
      (by
        first
        | (aesop))
      hyp_exlimivv_1
  have p0001 :=
    @gExlimiv (synWex y ph) ps x
      (by
        first
        | (aesop))
      p0000
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_exlimdv`. -/
@[expose]
noncomputable def gExlimdv (ph : Wff) (ps : Wff) (ch : Wff) (x : Var)
    (dv_ch_x : x ∉ ch.fv) (dv_ph_x : x ∉ ph.fv)
    (hyp_exlimdv_1 : Nominal.NPrf (.imp ph (.imp ps ch))) :
    Nominal.NPrf (.imp ph (.imp (synWex x ps) ch)) :=
  by
  let proofSupport : Finset Var := ph.fv ∪ ps.fv ∪ ch.fv ∪ ({ x } : Finset Var)
  have p0000 :=
    @gEximdv ph ps ch x
      (by
        first
        | (aesop))
      hyp_exlimdv_1
  have p0001 :=
    @gAx17e ch x
      (by
        first
        | (aesop))
  have p0002 := @gSyl6 ph (synWex x ps) (synWex x ch) ch p0000 p0001
  exact p0002

/-- Checked nominal proof certificate identified upstream as `g_exlimdvv`. -/
@[expose]
noncomputable def gExlimdvv (ph : Wff) (ps : Wff) (ch : Wff) (x : Var) (y : Var)
    (dv_ch_x : x ∉ ch.fv) (dv_ch_y : y ∉ ch.fv) (dv_ph_x : x ∉ ph.fv)
    (dv_ph_y : y ∉ ph.fv) (hyp_exlimdvv_1 : Nominal.NPrf (.imp ph (.imp ps ch))) :
    Nominal.NPrf (.imp ph (.imp (synWex x (synWex y ps)) ch)) :=
  by
  let proofSupport : Finset Var :=
    ph.fv ∪ ps.fv ∪ ch.fv ∪ ({ x } : Finset Var) ∪ ({ y } : Finset Var)
  have p0000 :=
    @gExlimdv ph ps ch y
      (by
        first
        | (aesop))
      (by
        first
        | (aesop))
      hyp_exlimdvv_1
  have p0001 :=
    @gExlimdv ph (synWex y ps) ch x
      (by
        first
        | (aesop))
      (by
        first
        | (aesop))
      p0000
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_exlimddv`. -/
@[expose]
noncomputable def gExlimddv (ph : Wff) (ps : Wff) (ch : Wff) (x : Var)
    (dv_ch_x : x ∉ ch.fv) (dv_ph_x : x ∉ ph.fv)
    (hyp_exlimddv_1 : Nominal.NPrf (.imp ph (synWex x ps)))
    (hyp_exlimddv_2 : Nominal.NPrf (.imp (synWa ph ps) ch)) :
    Nominal.NPrf (.imp ph ch) :=
  by
  let proofSupport : Finset Var := ph.fv ∪ ps.fv ∪ ch.fv ∪ ({ x } : Finset Var)
  have p0000 := @gEx ph ps ch hyp_exlimddv_2
  have p0001 :=
    @gExlimdv ph ps ch x
      (by
        first
        | (aesop))
      (by
        first
        | (aesop))
      p0000
  have p0002 := @gMpd ph (synWex x ps) ch hyp_exlimddv_1 p0001
  exact p0002

/-- Checked nominal proof certificate identified upstream as `g_equs3`. -/
@[expose]
noncomputable def gEqus3 (ph : Wff) (x : Var) (y : Var) :
    Nominal.NPrf
      (synWb (synWex x (synWa (.objEq x y) ph))
        (.neg (.all x (.imp (.objEq x y) (.neg ph))))) :=
  by
  have p0000 := @gAlinexa (.objEq x y) ph x
  have p0001 :=
    @gCon2bii (.all x (.imp (.objEq x y) (.neg ph))) (synWex x (synWa (.objEq x y) ph))
      p0000
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_speimfw`. -/
@[expose]
noncomputable def gSpeimfw (ph : Wff) (ps : Wff) (x : Var) (y : Var)
    (hyp_speimfw_2 : Nominal.NPrf (.imp (.objEq x y) (.imp ph ps))) :
    Nominal.NPrf
      (.imp (.neg (.all x (.neg (.objEq x y)))) (.imp (.all x ph) (synWex x ps))) :=
  by
  have p0000 := @gEximi (.objEq x y) (.imp ph ps) x hyp_speimfw_2
  have p0001 := (Nominal.biimpRefl (synWex x (.objEq x y)))
  have p0002 := @gN1935 ph ps x
  have p0003 :=
    @gN3imtr3i (synWex x (.objEq x y)) (synWex x (.imp ph ps))
      (.neg (.all x (.neg (.objEq x y)))) (.imp (.all x ph) (synWex x ps)) p0000 p0001
      p0002
  exact p0003

/-- Checked nominal proof certificate identified upstream as `g_spimfw`. -/
@[expose]
noncomputable def gSpimfw (ph : Wff) (ps : Wff) (x : Var) (y : Var)
    (hyp_spimfw_1 : Nominal.NPrf (.imp (.neg ps) (.all x (.neg ps))))
    (hyp_spimfw_2 : Nominal.NPrf (.imp (.objEq x y) (.imp ph ps))) :
    Nominal.NPrf (.imp (.neg (.all x (.neg (.objEq x y)))) (.imp (.all x ph) ps)) :=
  by
  have p0000 := @gSpeimfw ph ps x y hyp_spimfw_2
  have p0001 := (Nominal.biimpRefl (synWex x ps))
  have p0002 := @gCon1i ps (.all x (.neg ps)) hyp_spimfw_1
  have p0003 := @gSylbi (synWex x ps) (.neg (.all x (.neg ps))) ps p0001 p0002
  have p0004 :=
    @gSyl6 (.neg (.all x (.neg (.objEq x y)))) (.all x ph) (synWex x ps) ps p0000 p0003
  exact p0004

/-- Checked nominal proof certificate identified upstream as `g_sbequ2`. -/
@[expose]
noncomputable def gSbequ2 (ph : Wff) (x : Var) (y : Var) :
    Nominal.NPrf (.imp (.objEq x y) (.imp (synWsb y x ph) ph)) :=
  by
  have p0000 := (Nominal.biimpRefl (synWsb y x ph))
  have p0001 := @gSimpl (.imp (.objEq x y) ph) (synWex x (synWa (.objEq x y) ph))
  have p0002 :=
    @gCom12 (synWa (.imp (.objEq x y) ph) (synWex x (synWa (.objEq x y) ph)))
      (.objEq x y) ph p0001
  have p0003 :=
    @gSyl5bi (synWsb y x ph)
      (synWa (.imp (.objEq x y) ph) (synWex x (synWa (.objEq x y) ph))) (.objEq x y) ph
      p0000 p0002
  exact p0003

/-- Checked nominal proof certificate identified upstream as `g_sb1`. -/
@[expose]
noncomputable def gSb1 (ph : Wff) (x : Var) (y : Var) :
    Nominal.NPrf (.imp (synWsb y x ph) (synWex x (synWa (.objEq x y) ph))) :=
  by
  have p0000 := (Nominal.biimpRefl (synWsb y x ph))
  have p0001 :=
    @gSimprbi (synWsb y x ph) (.imp (.objEq x y) ph)
      (synWex x (synWa (.objEq x y) ph)) p0000
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_sbimi`. -/
@[expose]
noncomputable def gSbimi (ph : Wff) (ps : Wff) (x : Var) (y : Var)
    (hyp_sbimi_1 : Nominal.NPrf (.imp ph ps)) :
    Nominal.NPrf (.imp (synWsb y x ph) (synWsb y x ps)) :=
  by
  have p0000 := @gImim2i ph ps (.objEq x y) hyp_sbimi_1
  have p0001 := @gAnim2i ph ps (.objEq x y) hyp_sbimi_1
  have p0002 := @gEximi (synWa (.objEq x y) ph) (synWa (.objEq x y) ps) x p0001
  have p0003 :=
    @gAnim12i (.imp (.objEq x y) ph) (.imp (.objEq x y) ps)
      (synWex x (synWa (.objEq x y) ph)) (synWex x (synWa (.objEq x y) ps)) p0000
      p0002
  have p0004 := (Nominal.biimpRefl (synWsb y x ph))
  have p0005 := (Nominal.biimpRefl (synWsb y x ps))
  have p0006 :=
    @gN3imtr4i (synWa (.imp (.objEq x y) ph) (synWex x (synWa (.objEq x y) ph)))
      (synWa (.imp (.objEq x y) ps) (synWex x (synWa (.objEq x y) ps)))
      (synWsb y x ph) (synWsb y x ps) p0003 p0004 p0005
  exact p0006

/-- Checked nominal proof certificate identified upstream as `g_sbbii`. -/
@[expose]
noncomputable def gSbbii (ph : Wff) (ps : Wff) (x : Var) (y : Var)
    (hyp_sbbii_1 : Nominal.NPrf (synWb ph ps)) :
    Nominal.NPrf (synWb (synWsb y x ph) (synWsb y x ps)) :=
  by
  have p0000 := @gBiimpi ph ps hyp_sbbii_1
  have p0001 := @gSbimi ph ps x y p0000
  have p0002 := @gBiimpri ph ps hyp_sbbii_1
  have p0003 := @gSbimi ps ph x y p0002
  have p0004 := @gImpbii (synWsb y x ph) (synWsb y x ps) p0001 p0003
  exact p0004

/-- Checked nominal proof certificate identified upstream as `g_ax9v`. -/
@[expose]
noncomputable def gAx9v (x : Var) (y : Var) (_dv_x_y : x ≠ y) :
    Nominal.NPrf (.neg (.all x (.neg (.objEq x y)))) :=
  by
  have p0000 := Nominal.ax9 x y
  exact p0000

/-- Checked nominal proof certificate identified upstream as `g_a9ev`. -/
@[expose]
noncomputable def gA9ev (x : Var) (y : Var) (dv_x_y : x ≠ y) :
    Nominal.NPrf (synWex x (.objEq x y)) :=
  by
  let proofSupport : Finset Var := ({ x } : Finset Var) ∪ ({ y } : Finset Var)
  have p0000 :=
    @gAx9v x y
      (by
        first
        | (aesop))
  have p0001 := (Nominal.biimpRefl (synWex x (.objEq x y)))
  have p0002 :=
    @gMpbir (synWex x (.objEq x y)) (.neg (.all x (.neg (.objEq x y)))) p0000 p0001
  exact p0002

/-- Checked nominal proof certificate identified upstream as `g_spimeh`. -/
@[expose]
noncomputable def gSpimeh (ph : Wff) (ps : Wff) (x : Var) (z : Var) (dv_x_z : x ≠ z)
    (hyp_spimeh_1 : Nominal.NPrf (.imp ph (.all x ph)))
    (hyp_spimeh_2 : Nominal.NPrf (.imp (.objEq x z) (.imp ph ps))) :
    Nominal.NPrf (.imp ph (synWex x ps)) :=
  by
  let proofSupport : Finset Var :=
    ph.fv ∪ ps.fv ∪ ({ x } : Finset Var) ∪ ({ z } : Finset Var)
  have p0000 :=
    @gA9ev x z
      (by
        first
        | (aesop))
  have p0001 := @gEximi (.objEq x z) (.imp ph ps) x hyp_spimeh_2
  have p0002 := Nominal.mp p0000 p0001
  have p0003 := @gN1935i ph ps x p0002
  have p0004 := @gSyl ph (.all x ph) (synWex x ps) hyp_spimeh_1 p0003
  exact p0004

/-- Checked nominal proof certificate identified upstream as `g_spimw`. -/
@[expose]
noncomputable def gSpimw (ph : Wff) (ps : Wff) (x : Var) (y : Var) (dv_x_y : x ≠ y)
    (hyp_spimw_1 : Nominal.NPrf (.imp (.neg ps) (.all x (.neg ps))))
    (hyp_spimw_2 : Nominal.NPrf (.imp (.objEq x y) (.imp ph ps))) :
    Nominal.NPrf (.imp (.all x ph) ps) :=
  by
  let proofSupport : Finset Var :=
    ph.fv ∪ ps.fv ∪ ({ x } : Finset Var) ∪ ({ y } : Finset Var)
  have p0000 :=
    @gAx9v x y
      (by
        first
        | (aesop))
  have p0001 := @gSpimfw ph ps x y hyp_spimw_1 hyp_spimw_2
  have p0002 := Nominal.mp p0000 p0001
  exact p0002

/-- Checked nominal proof certificate identified upstream as `g_spimvw`. -/
@[expose]
noncomputable def gSpimvw (ph : Wff) (ps : Wff) (x : Var) (y : Var) (dv_ps_x : x ∉ ps.fv)
    (dv_x_y : x ≠ y) (hyp_spimvw_1 : Nominal.NPrf (.imp (.objEq x y) (.imp ph ps))) :
    Nominal.NPrf (.imp (.all x ph) ps) :=
  by
  let proofSupport : Finset Var :=
    ph.fv ∪ ps.fv ∪ ({ x } : Finset Var) ∪ ({ y } : Finset Var)
  have p0000 :=
    Nominal.ax17 (.neg ps) x
      (by
        first
        |
          (simp (config :=
              {
                failIfUnchanged :=
                  false }) only [NFChoice.Compiler.CoreFVSimp.fv_wff_neg] at ⊢;
            aesop))
  have p0001 :=
    @gSpimw ph ps x y
      (by
        first
        | (aesop))
      p0000 hyp_spimvw_1
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_cbvalivw`. -/
@[expose]
noncomputable def gCbvalivw (ph : Wff) (ps : Wff) (x : Var) (y : Var)
    (dv_ph_y : y ∉ ph.fv) (dv_ps_x : x ∉ ps.fv) (dv_x_y : x ≠ y)
    (hyp_cbvalivw_1 : Nominal.NPrf (.imp (.objEq x y) (.imp ph ps))) :
    Nominal.NPrf (.imp (.all x ph) (.all y ps)) :=
  by
  let proofSupport : Finset Var :=
    ph.fv ∪ ps.fv ∪ ({ x } : Finset Var) ∪ ({ y } : Finset Var)
  have p0000 :=
    @gSpimvw ph ps x y
      (by
        first
        | (aesop))
      (by
        first
        | (aesop))
      hyp_cbvalivw_1
  have p0001 :=
    @gAlrimiv (.all x ph) ps y
      (by
        first
        |
          (simp (config :=
              { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_wff_all,
              Finset.mem_erase] at ⊢;
            aesop))
      p0000
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_equid`. -/
@[expose]
noncomputable def gEquid (x : Var) : Nominal.NPrf (.objEq x x) :=
  by
  let proofSupport : Finset Var := ({ x } : Finset Var)
  let y : Var := freshVar proofSupport 0
  have fresh_y : y ∉ proofSupport :=
    by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_y_ne_x : y ≠ x := by
    intro h
    exact fresh_y (Finset.mem_singleton.mpr h)
  have fresh_x_ne_y : x ≠ y := Ne.symm fresh_y_ne_x
  have p0000 :=
    @gA9ev y x
      (by
        first
        | (aesop))
  have p0001 := Nominal.ax8 y x x
  have p0002 := @gPm243i (.objEq y x) (.objEq x x) p0001
  have p0003 := @gEximi (.objEq y x) (.objEq x x) y p0002
  have p0004 :=
    @gAx17e (.objEq x x) y
      (by
        first
        |
          (simp (config :=
              {
                failIfUnchanged :=
                  false }) only [NFChoice.Compiler.CoreFVSimp.fv_wff_objEq] at ⊢;
            aesop))
  have p0005 :=
    @gMp2b (synWex y (.objEq y x)) (synWex y (.objEq x x)) (.objEq x x) p0000 p0003
      p0004
  exact p0005

/-- Checked nominal proof certificate identified upstream as `g_equcomi`. -/
@[expose]
noncomputable def gEqucomi (x : Var) (y : Var) :
    Nominal.NPrf (.imp (.objEq x y) (.objEq y x)) :=
  by
  have p0000 := @gEquid x
  have p0001 := Nominal.ax8 x y x
  have p0002 := @gMpi (.objEq x y) (.objEq x x) (.objEq y x) p0000 p0001
  exact p0002

/-- Checked nominal proof certificate identified upstream as `g_equcom`. -/
@[expose]
noncomputable def gEqucom (x : Var) (y : Var) :
    Nominal.NPrf (synWb (.objEq x y) (.objEq y x)) :=
  by
  have p0000 := @gEqucomi x y
  have p0001 := @gEqucomi y x
  have p0002 := @gImpbii (.objEq x y) (.objEq y x) p0000 p0001
  exact p0002

/-- Checked nominal proof certificate identified upstream as `g_equcoms`. -/
@[expose]
noncomputable def gEqucoms (ph : Wff) (x : Var) (y : Var)
    (hyp_equcoms_1 : Nominal.NPrf (.imp (.objEq x y) ph)) :
    Nominal.NPrf (.imp (.objEq y x) ph) :=
  by
  have p0000 := @gEqucomi y x
  have p0001 := @gSyl (.objEq y x) (.objEq x y) ph p0000 hyp_equcoms_1
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_equtr`. -/
@[expose]
noncomputable def gEqutr (x : Var) (y : Var) (z : Var) :
    Nominal.NPrf (.imp (.objEq x y) (.imp (.objEq y z) (.objEq x z))) :=
  by
  have p0000 := Nominal.ax8 y x z
  have p0001 := @gEqucoms (.imp (.objEq y z) (.objEq x z)) y x p0000
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_equtrr`. -/
@[expose]
noncomputable def gEqutrr (x : Var) (y : Var) (z : Var) :
    Nominal.NPrf (.imp (.objEq x y) (.imp (.objEq z x) (.objEq z y))) :=
  by
  have p0000 := @gEqutr z x y
  have p0001 := @gCom12 (.objEq z x) (.objEq x y) (.objEq z y) p0000
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_equequ1`. -/
@[expose]
noncomputable def gEquequ1 (x : Var) (y : Var) (z : Var) :
    Nominal.NPrf (.imp (.objEq x y) (synWb (.objEq x z) (.objEq y z))) :=
  by
  have p0000 := Nominal.ax8 x y z
  have p0001 := @gEqutr x y z
  have p0002 := @gImpbid (.objEq x y) (.objEq x z) (.objEq y z) p0000 p0001
  exact p0002

/-- Checked nominal proof certificate identified upstream as `g_equequ2`. -/
@[expose]
noncomputable def gEquequ2 (x : Var) (y : Var) (z : Var) :
    Nominal.NPrf (.imp (.objEq x y) (synWb (.objEq z x) (.objEq z y))) :=
  by
  have p0000 := @gEquequ1 x y z
  have p0001 := @gEqucom x z
  have p0002 := @gEqucom y z
  have p0003 :=
    @gN3bitr3g (.objEq x y) (.objEq x z) (.objEq y z) (.objEq z x) (.objEq z y) p0000
      p0001 p0002
  exact p0003

/-- Checked nominal proof certificate identified upstream as `g_stdpc6`. -/
@[expose]
noncomputable def gStdpc6 (x : Var) : Nominal.NPrf (.all x (.objEq x x)) :=
  by
  have p0000 := @gEquid x
  have p0001 := Nominal.gen p0000 x
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_equtr2`. -/
@[expose]
noncomputable def gEqutr2 (x : Var) (y : Var) (z : Var) :
    Nominal.NPrf (.imp (synWa (.objEq x z) (.objEq y z)) (.objEq x y)) :=
  by
  have p0000 := @gEqutrr z y x
  have p0001 := @gEqucoms (.imp (.objEq x z) (.objEq x y)) z y p0000
  have p0002 := @gImpcom (.objEq y z) (.objEq x z) (.objEq x y) p0001
  exact p0002

/-- Checked nominal proof certificate identified upstream as `g_elequ1`. -/
@[expose]
noncomputable def gElequ1 (x : Var) (y : Var) (z : Var) :
    Nominal.NPrf (.imp (.objEq x y) (synWb (.objMem x z) (.objMem y z))) :=
  by
  have p0000 := Nominal.ax13 x y z
  have p0001 := Nominal.ax13 y x z
  have p0002 := @gEqucoms (.imp (.objMem y z) (.objMem x z)) y x p0001
  have p0003 := @gImpbid (.objEq x y) (.objMem x z) (.objMem y z) p0000 p0002
  exact p0003

/-- Checked nominal proof certificate identified upstream as `g_elequ2`. -/
@[expose]
noncomputable def gElequ2 (x : Var) (y : Var) (z : Var) :
    Nominal.NPrf (.imp (.objEq x y) (synWb (.objMem z x) (.objMem z y))) :=
  by
  have p0000 := Nominal.ax14 x y z
  have p0001 := Nominal.ax14 y x z
  have p0002 := @gEqucoms (.imp (.objMem z y) (.objMem z x)) y x p0001
  have p0003 := @gImpbid (.objEq x y) (.objMem z x) (.objMem z y) p0000 p0002
  exact p0003

/-- Checked nominal proof certificate identified upstream as `g_hbn1`. -/
@[expose]
noncomputable def gHbn1 (ph : Wff) (x : Var) :
    Nominal.NPrf (.imp (.neg (.all x ph)) (.all x (.neg (.all x ph)))) :=
  by
  have p0000 := Nominal.ax6 x ph
  exact p0000

/-- Checked nominal proof certificate identified upstream as `g_hbe1`. -/
@[expose]
noncomputable def gHbe1 (ph : Wff) (x : Var) :
    Nominal.NPrf (.imp (synWex x ph) (.all x (synWex x ph))) :=
  by
  have p0000 := (Nominal.biimpRefl (synWex x ph))
  have p0001 := @gHbn1 (.neg ph) x
  have p0002 := @gHbxfrbi (synWex x ph) (.neg (.all x (.neg ph))) x p0000 p0001
  exact p0002

/-- Checked nominal proof certificate identified upstream as `g_nfe1`. -/
@[expose]
noncomputable def gNfe1 (ph : Wff) (x : Var) : Nominal.NPrf (synWnf x (synWex x ph)) :=
  by
  have p0000 := @gHbe1 ph x
  have p0001 := @gNfi (synWex x ph) x p0000
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_a7s`. -/
@[expose]
noncomputable def gA7s (ph : Wff) (ps : Wff) (x : Var) (y : Var)
    (hyp_a7s_1 : Nominal.NPrf (.imp (.all x (.all y ph)) ps)) :
    Nominal.NPrf (.imp (.all y (.all x ph)) ps) :=
  by
  have p0000 := Nominal.ax7Structural y x ph
  have p0001 := @gSyl (.all y (.all x ph)) (.all x (.all y ph)) ps p0000 hyp_a7s_1
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_hbal`. -/
@[expose]
noncomputable def gHbal (ph : Wff) (x : Var) (y : Var)
    (hyp_hbal_1 : Nominal.NPrf (.imp ph (.all x ph))) :
    Nominal.NPrf (.imp (.all y ph) (.all x (.all y ph))) :=
  by
  have p0000 := @gAlimi ph (.all x ph) y hyp_hbal_1
  have p0001 := Nominal.ax7Structural y x ph
  have p0002 := @gSyl (.all y ph) (.all y (.all x ph)) (.all x (.all y ph)) p0000 p0001
  exact p0002

/-- Checked nominal proof certificate identified upstream as `g_alcom`. -/
@[expose]
noncomputable def gAlcom (ph : Wff) (x : Var) (y : Var) :
    Nominal.NPrf (synWb (.all x (.all y ph)) (.all y (.all x ph))) :=
  by
  have p0000 := Nominal.ax7Structural x y ph
  have p0001 := Nominal.ax7Structural y x ph
  have p0002 := @gImpbii (.all x (.all y ph)) (.all y (.all x ph)) p0000 p0001
  exact p0002

/-- Checked nominal proof certificate identified upstream as `g_alrot3`. -/
@[expose]
noncomputable def gAlrot3 (ph : Wff) (x : Var) (y : Var) (z : Var) :
    Nominal.NPrf (synWb (.all x (.all y (.all z ph))) (.all y (.all z (.all x ph)))) :=
  by
  have p0000 := @gAlcom (.all z ph) x y
  have p0001 := @gAlcom ph x z
  have p0002 := @gAlbii (.all x (.all z ph)) (.all z (.all x ph)) y p0001
  have p0003 :=
    @gBitri (.all x (.all y (.all z ph))) (.all y (.all x (.all z ph)))
      (.all y (.all z (.all x ph))) p0000 p0002
  exact p0003

/-- Checked nominal proof certificate identified upstream as `g_hbald`. -/
@[expose]
noncomputable def gHbald (ph : Wff) (ps : Wff) (x : Var) (y : Var)
    (hyp_hbald_1 : Nominal.NPrf (.imp ph (.all y ph)))
    (hyp_hbald_2 : Nominal.NPrf (.imp ph (.imp ps (.all x ps)))) :
    Nominal.NPrf (.imp ph (.imp (.all y ps) (.all x (.all y ps)))) :=
  by
  have p0000 := @gAlimdh ph ps (.all x ps) y hyp_hbald_1 hyp_hbald_2
  have p0001 := Nominal.ax7Structural y x ps
  have p0002 :=
    @gSyl6 ph (.all y ps) (.all y (.all x ps)) (.all x (.all y ps)) p0000 p0001
  exact p0002

/-- Checked nominal proof certificate identified upstream as `g_excom`. -/
@[expose]
noncomputable def gExcom (ph : Wff) (x : Var) (y : Var) :
    Nominal.NPrf (synWb (synWex x (synWex y ph)) (synWex y (synWex x ph))) :=
  by
  have p0000 := @gAlcom (.neg ph) x y
  have p0001 := @gNotbii (.all x (.all y (.neg ph))) (.all y (.all x (.neg ph))) p0000
  have p0002 := @gExnal (.all y (.neg ph)) x
  have p0003 := @gExnal (.all x (.neg ph)) y
  have p0004 :=
    @gN3bitr4i (.neg (.all x (.all y (.neg ph)))) (.neg (.all y (.all x (.neg ph))))
      (synWex x (.neg (.all y (.neg ph)))) (synWex y (.neg (.all x (.neg ph)))) p0001
      p0002 p0003
  have p0005 := (Nominal.biimpRefl (synWex y ph))
  have p0006 := @gExbii (synWex y ph) (.neg (.all y (.neg ph))) x p0005
  have p0007 := (Nominal.biimpRefl (synWex x ph))
  have p0008 := @gExbii (synWex x ph) (.neg (.all x (.neg ph))) y p0007
  have p0009 :=
    @gN3bitr4i (synWex x (.neg (.all y (.neg ph))))
      (synWex y (.neg (.all x (.neg ph)))) (synWex x (synWex y ph))
      (synWex y (synWex x ph)) p0004 p0006 p0008
  exact p0009

/-- Checked nominal proof certificate identified upstream as `g_excom13`. -/
@[expose]
noncomputable def gExcom13 (ph : Wff) (x : Var) (y : Var) (z : Var) :
    Nominal.NPrf
      (synWb (synWex x (synWex y (synWex z ph))) (synWex z (synWex y (synWex x ph)))) :=
  by
  have p0000 := @gExcom (synWex z ph) x y
  have p0001 := @gExcom ph x z
  have p0002 := @gExbii (synWex x (synWex z ph)) (synWex z (synWex x ph)) y p0001
  have p0003 := @gExcom (synWex x ph) y z
  have p0004 :=
    @gN3bitri (synWex x (synWex y (synWex z ph)))
      (synWex y (synWex x (synWex z ph))) (synWex y (synWex z (synWex x ph)))
      (synWex z (synWex y (synWex x ph))) p0000 p0002 p0003
  exact p0004

/-- Checked nominal proof certificate identified upstream as `g_exrot3`. -/
@[expose]
noncomputable def gExrot3 (ph : Wff) (x : Var) (y : Var) (z : Var) :
    Nominal.NPrf
      (synWb (synWex x (synWex y (synWex z ph))) (synWex y (synWex z (synWex x ph)))) :=
  by
  have p0000 := @gExcom13 ph x y z
  have p0001 := @gExcom (synWex x ph) z y
  have p0002 :=
    @gBitri (synWex x (synWex y (synWex z ph))) (synWex z (synWex y (synWex x ph)))
      (synWex y (synWex z (synWex x ph))) p0000 p0001
  exact p0002

/-- Checked nominal proof certificate identified upstream as `g_exrot4`. -/
@[expose]
noncomputable def gExrot4 (ph : Wff) (x : Var) (y : Var) (z : Var) (w : Var) :
    Nominal.NPrf
      (synWb (synWex x (synWex y (synWex z (synWex w ph))))
        (synWex z (synWex w (synWex x (synWex y ph))))) :=
  by
  have p0000 := @gExcom13 ph y z w
  have p0001 :=
    @gExbii (synWex y (synWex z (synWex w ph))) (synWex w (synWex z (synWex y ph)))
      x p0000
  have p0002 := @gExcom13 (synWex y ph) x w z
  have p0003 :=
    @gBitri (synWex x (synWex y (synWex z (synWex w ph))))
      (synWex x (synWex w (synWex z (synWex y ph))))
      (synWex z (synWex w (synWex x (synWex y ph)))) p0001 p0002
  exact p0003

/-- Checked nominal proof certificate identified upstream as `g_sp`. -/
@[expose]
noncomputable def gSp (ph : Wff) (x : Var) : Nominal.NPrf (.imp (.all x ph) ph) :=
  by
  let proofSupport : Finset Var := ph.fv ∪ ({ x } : Finset Var)
  let w : Var := freshVar proofSupport 0
  have fresh_w : w ∉ proofSupport :=
    by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_w_not_ph : w ∉ ph.fv := by
    intro h
    exact fresh_w (Finset.mem_union_left _ (h))
  have fresh_w_ne_x : w ≠ x := by
    intro h
    exact fresh_w (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))
  have fresh_x_ne_w : x ≠ w := Ne.symm fresh_w_ne_x
  have p0000 :=
    @gA9ev w x
      (by
        first
        | (aesop))
  have p0001 := @gEqucomi w x
  have p0002 :=
    Nominal.ax17 (.neg ph) w
      (by
        first
        |
          (simp (config :=
              {
                failIfUnchanged :=
                  false }) only [NFChoice.Compiler.CoreFVSimp.fv_wff_neg] at ⊢;
            aesop))
  have p0003 := Nominal.ax11Structural x w (.neg ph)
  have p0004 :=
    @gSyl2im (.objEq w x) (.objEq x w) (.neg ph) (.all w (.neg ph))
      (.all x (.imp (.objEq x w) (.neg ph))) p0001 p0002 p0003
  have p0005 :=
    @gAx9v x w
      (by
        first
        | (aesop))
  have p0006 := @gCon2 (.objEq x w) ph
  have p0007 := @gAl2imi (.imp (.objEq x w) (.neg ph)) ph (.neg (.objEq x w)) x p0006
  have p0008 :=
    @gMtoi (.all x (.imp (.objEq x w) (.neg ph))) (.all x ph)
      (.all x (.neg (.objEq x w))) p0005 p0007
  have p0009 :=
    @gSyl6 (.objEq w x) (.neg ph) (.all x (.imp (.objEq x w) (.neg ph)))
      (.neg (.all x ph)) p0004 p0008
  have p0010 := @gCon4d (.objEq w x) ph (.all x ph) p0009
  have p0011 :=
    @gExlimiv (.objEq w x) (.imp (.all x ph) ph) w
      (by
        first
        |
          (simp (config :=
              { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp,
              NFChoice.Compiler.CoreFVSimp.fv_wff_all, Finset.mem_union,
              Finset.mem_erase] at ⊢;
            aesop))
      p0010
  have p0012 := Nominal.mp p0000 p0011
  exact p0012

/-- Checked nominal proof certificate identified upstream as `g_ax6o`. -/
@[expose]
noncomputable def gAx6o (ph : Wff) (x : Var) :
    Nominal.NPrf (.imp (.neg (.all x (.neg (.all x ph)))) ph) :=
  by
  have p0000 := @gSp ph x
  have p0001 := Nominal.ax6 x ph
  have p0002 := @gNsyl4 (.all x ph) ph (.all x (.neg (.all x ph))) p0000 p0001
  exact p0002

/-- Checked nominal proof certificate identified upstream as `g_sps`. -/
@[expose]
noncomputable def gSps (ph : Wff) (ps : Wff) (x : Var)
    (hyp_sps_1 : Nominal.NPrf (.imp ph ps)) : Nominal.NPrf (.imp (.all x ph) ps) :=
  by
  have p0000 := @gSp ph x
  have p0001 := @gSyl (.all x ph) ph ps p0000 hyp_sps_1
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_spsd`. -/
@[expose]
noncomputable def gSpsd (ph : Wff) (ps : Wff) (ch : Wff) (x : Var)
    (hyp_spsd_1 : Nominal.NPrf (.imp ph (.imp ps ch))) :
    Nominal.NPrf (.imp ph (.imp (.all x ps) ch)) :=
  by
  have p0000 := @gSp ps x
  have p0001 := @gSyl5 (.all x ps) ps ph ch p0000 hyp_spsd_1
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_n_19_8a`. -/
@[expose]
noncomputable def gN198a (ph : Wff) (x : Var) :
    Nominal.NPrf (.imp ph (synWex x ph)) :=
  by
  have p0000 := @gSp (.neg ph) x
  have p0001 := @gCon2i (.all x (.neg ph)) ph p0000
  have p0002 := (Nominal.biimpRefl (synWex x ph))
  have p0003 := @gSylibr ph (.neg (.all x (.neg ph))) (synWex x ph) p0001 p0002
  exact p0003

/-- Checked nominal proof certificate identified upstream as `g_n_19_21bi`. -/
@[expose]
noncomputable def gN1921bi (ph : Wff) (ps : Wff) (x : Var)
    (hyp_n_19_21bi_1 : Nominal.NPrf (.imp ph (.all x ps))) : Nominal.NPrf (.imp ph ps) :=
  by
  have p0000 := @gSp ps x
  have p0001 := @gSyl ph (.all x ps) ps hyp_n_19_21bi_1 p0000
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_nfr`. -/
@[expose]
noncomputable def gNfr (ph : Wff) (x : Var) :
    Nominal.NPrf (.imp (synWnf x ph) (.imp ph (.all x ph))) :=
  by
  have p0000 := (Nominal.biimpRefl (synWnf x ph))
  have p0001 := @gSp (.imp ph (.all x ph)) x
  have p0002 :=
    @gSylbi (synWnf x ph) (.all x (.imp ph (.all x ph))) (.imp ph (.all x ph)) p0000
      p0001
  exact p0002

/-- Checked nominal proof certificate identified upstream as `g_nfri`. -/
@[expose]
noncomputable def gNfri (ph : Wff) (x : Var) (hyp_nfri_1 : Nominal.NPrf (synWnf x ph)) :
    Nominal.NPrf (.imp ph (.all x ph)) :=
  by
  have p0000 := @gNfr ph x
  have p0001 := Nominal.mp hyp_nfri_1 p0000
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_nfrd`. -/
@[expose]
noncomputable def gNfrd (ph : Wff) (ps : Wff) (x : Var)
    (hyp_nfrd_1 : Nominal.NPrf (.imp ph (synWnf x ps))) :
    Nominal.NPrf (.imp ph (.imp ps (.all x ps))) :=
  by
  have p0000 := @gNfr ps x
  have p0001 := @gSyl ph (synWnf x ps) (.imp ps (.all x ps)) hyp_nfrd_1 p0000
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_alimd`. -/
@[expose]
noncomputable def gAlimd (ph : Wff) (ps : Wff) (ch : Wff) (x : Var)
    (hyp_alimd_1 : Nominal.NPrf (synWnf x ph))
    (hyp_alimd_2 : Nominal.NPrf (.imp ph (.imp ps ch))) :
    Nominal.NPrf (.imp ph (.imp (.all x ps) (.all x ch))) :=
  by
  have p0000 := @gNfri ph x hyp_alimd_1
  have p0001 := @gAlimdh ph ps ch x p0000 hyp_alimd_2
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_alrimi`. -/
@[expose]
noncomputable def gAlrimi (ph : Wff) (ps : Wff) (x : Var)
    (hyp_alrimi_1 : Nominal.NPrf (synWnf x ph))
    (hyp_alrimi_2 : Nominal.NPrf (.imp ph ps)) : Nominal.NPrf (.imp ph (.all x ps)) :=
  by
  have p0000 := @gNfri ph x hyp_alrimi_1
  have p0001 := @gAlrimih ph ps x p0000 hyp_alrimi_2
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_nfd`. -/
@[expose]
noncomputable def gNfd (ph : Wff) (ps : Wff) (x : Var)
    (hyp_nfd_1 : Nominal.NPrf (synWnf x ph))
    (hyp_nfd_2 : Nominal.NPrf (.imp ph (.imp ps (.all x ps)))) :
    Nominal.NPrf (.imp ph (synWnf x ps)) :=
  by
  have p0000 := @gAlrimi ph (.imp ps (.all x ps)) x hyp_nfd_1 hyp_nfd_2
  have p0001 := (Nominal.biimpRefl (synWnf x ps))
  have p0002 := @gSylibr ph (.all x (.imp ps (.all x ps))) (synWnf x ps) p0000 p0001
  exact p0002

/-- Checked nominal proof certificate identified upstream as `g_nfdh`. -/
@[expose]
noncomputable def gNfdh (ph : Wff) (ps : Wff) (x : Var)
    (hyp_nfdh_1 : Nominal.NPrf (.imp ph (.all x ph)))
    (hyp_nfdh_2 : Nominal.NPrf (.imp ph (.imp ps (.all x ps)))) :
    Nominal.NPrf (.imp ph (synWnf x ps)) :=
  by
  have p0000 := @gNfi ph x hyp_nfdh_1
  have p0001 := @gNfd ph ps x p0000 hyp_nfdh_2
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_alrimdd`. -/
@[expose]
noncomputable def gAlrimdd (ph : Wff) (ps : Wff) (ch : Wff) (x : Var)
    (hyp_alrimdd_1 : Nominal.NPrf (synWnf x ph))
    (hyp_alrimdd_2 : Nominal.NPrf (.imp ph (synWnf x ps)))
    (hyp_alrimdd_3 : Nominal.NPrf (.imp ph (.imp ps ch))) :
    Nominal.NPrf (.imp ph (.imp ps (.all x ch))) :=
  by
  have p0000 := @gNfrd ph ps x hyp_alrimdd_2
  have p0001 := @gAlimd ph ps ch x hyp_alrimdd_1 hyp_alrimdd_3
  have p0002 := @gSyld ph ps (.all x ps) (.all x ch) p0000 p0001
  exact p0002

/-- Checked nominal proof certificate identified upstream as `g_alrimd`. -/
@[expose]
noncomputable def gAlrimd (ph : Wff) (ps : Wff) (ch : Wff) (x : Var)
    (hyp_alrimd_1 : Nominal.NPrf (synWnf x ph))
    (hyp_alrimd_2 : Nominal.NPrf (synWnf x ps))
    (hyp_alrimd_3 : Nominal.NPrf (.imp ph (.imp ps ch))) :
    Nominal.NPrf (.imp ph (.imp ps (.all x ch))) :=
  by
  have p0000 := @gA1i (synWnf x ps) ph hyp_alrimd_2
  have p0001 := @gAlrimdd ph ps ch x hyp_alrimd_1 p0000 hyp_alrimd_3
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_eximd`. -/
@[expose]
noncomputable def gEximd (ph : Wff) (ps : Wff) (ch : Wff) (x : Var)
    (hyp_eximd_1 : Nominal.NPrf (synWnf x ph))
    (hyp_eximd_2 : Nominal.NPrf (.imp ph (.imp ps ch))) :
    Nominal.NPrf (.imp ph (.imp (synWex x ps) (synWex x ch))) :=
  by
  have p0000 := @gNfri ph x hyp_eximd_1
  have p0001 := @gEximdh ph ps ch x p0000 hyp_eximd_2
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_nexd`. -/
@[expose]
noncomputable def gNexd (ph : Wff) (ps : Wff) (x : Var)
    (hyp_nexd_1 : Nominal.NPrf (synWnf x ph))
    (hyp_nexd_2 : Nominal.NPrf (.imp ph (.neg ps))) :
    Nominal.NPrf (.imp ph (.neg (synWex x ps))) :=
  by
  have p0000 := @gNfri ph x hyp_nexd_1
  have p0001 := @gNexdh ph ps x p0000 hyp_nexd_2
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_albid`. -/
@[expose]
noncomputable def gAlbid (ph : Wff) (ps : Wff) (ch : Wff) (x : Var)
    (hyp_albid_1 : Nominal.NPrf (synWnf x ph))
    (hyp_albid_2 : Nominal.NPrf (.imp ph (synWb ps ch))) :
    Nominal.NPrf (.imp ph (synWb (.all x ps) (.all x ch))) :=
  by
  have p0000 := @gNfri ph x hyp_albid_1
  have p0001 := @gAlbidh ph ps ch x p0000 hyp_albid_2
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_exbid`. -/
@[expose]
noncomputable def gExbid (ph : Wff) (ps : Wff) (ch : Wff) (x : Var)
    (hyp_exbid_1 : Nominal.NPrf (synWnf x ph))
    (hyp_exbid_2 : Nominal.NPrf (.imp ph (synWb ps ch))) :
    Nominal.NPrf (.imp ph (synWb (synWex x ps) (synWex x ch))) :=
  by
  have p0000 := @gNfri ph x hyp_exbid_1
  have p0001 := @gExbidh ph ps ch x p0000 hyp_exbid_2
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_nfbidf`. -/
@[expose]
noncomputable def gNfbidf (ph : Wff) (ps : Wff) (ch : Wff) (x : Var)
    (hyp_nfbidf_1 : Nominal.NPrf (synWnf x ph))
    (hyp_nfbidf_2 : Nominal.NPrf (.imp ph (synWb ps ch))) :
    Nominal.NPrf (.imp ph (synWb (synWnf x ps) (synWnf x ch))) :=
  by
  have p0000 := @gAlbid ph ps ch x hyp_nfbidf_1 hyp_nfbidf_2
  have p0001 := @gImbi12d ph ps ch (.all x ps) (.all x ch) hyp_nfbidf_2 p0000
  have p0002 :=
    @gAlbid ph (.imp ps (.all x ps)) (.imp ch (.all x ch)) x hyp_nfbidf_1 p0001
  have p0003 := (Nominal.biimpRefl (synWnf x ps))
  have p0004 := (Nominal.biimpRefl (synWnf x ch))
  have p0005 :=
    @gN3bitr4g ph (.all x (.imp ps (.all x ps))) (.all x (.imp ch (.all x ch)))
      (synWnf x ps) (synWnf x ch) p0002 p0003 p0004
  exact p0005

/-- Checked nominal proof certificate identified upstream as `g_hbnt`. -/
@[expose]
noncomputable def gHbnt (ph : Wff) (x : Var) :
    Nominal.NPrf
      (.imp (.all x (.imp ph (.all x ph))) (.imp (.neg ph) (.all x (.neg ph)))) :=
  by
  have p0000 := @gAx6o ph x
  have p0001 := @gCon1i (.all x (.neg (.all x ph))) ph p0000
  have p0002 := @gCon3 ph (.all x ph)
  have p0003 := @gAl2imi (.imp ph (.all x ph)) (.neg (.all x ph)) (.neg ph) x p0002
  have p0004 :=
    @gSyl5 (.neg ph) (.all x (.neg (.all x ph))) (.all x (.imp ph (.all x ph)))
      (.all x (.neg ph)) p0001 p0003
  exact p0004

/-- Checked nominal proof certificate identified upstream as `g_hbn`. -/
@[expose]
noncomputable def gHbn (ph : Wff) (x : Var)
    (hyp_hbn_1 : Nominal.NPrf (.imp ph (.all x ph))) :
    Nominal.NPrf (.imp (.neg ph) (.all x (.neg ph))) :=
  by
  have p0000 := @gHbnt ph x
  have p0001 :=
    @gMpg (.imp ph (.all x ph)) (.imp (.neg ph) (.all x (.neg ph))) x p0000 hyp_hbn_1
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_n_19_9ht`. -/
@[expose]
noncomputable def gN199ht (ph : Wff) (x : Var) :
    Nominal.NPrf (.imp (.all x (.imp ph (.all x ph))) (.imp (synWex x ph) ph)) :=
  by
  have p0000 := (Nominal.biimpRefl (synWex x ph))
  have p0001 := @gHbnt ph x
  have p0002 := @gCon1d (.all x (.imp ph (.all x ph))) ph (.all x (.neg ph)) p0001
  have p0003 :=
    @gSyl5bi (synWex x ph) (.neg (.all x (.neg ph))) (.all x (.imp ph (.all x ph))) ph
      p0000 p0002
  exact p0003

/-- Checked nominal proof certificate identified upstream as `g_n_19_9t`. -/
@[expose]
noncomputable def gN199t (ph : Wff) (x : Var) :
    Nominal.NPrf (.imp (synWnf x ph) (synWb (synWex x ph) ph)) :=
  by
  have p0000 := (Nominal.biimpRefl (synWnf x ph))
  have p0001 := @gN199ht ph x
  have p0002 :=
    @gSylbi (synWnf x ph) (.all x (.imp ph (.all x ph))) (.imp (synWex x ph) ph) p0000
      p0001
  have p0003 := @gN198a ph x
  have p0004 := @gImpbid1 (synWnf x ph) (synWex x ph) ph p0002 p0003
  exact p0004

/-- Checked nominal proof certificate identified upstream as `g_n_19_9h`. -/
@[expose]
noncomputable def gN199h (ph : Wff) (x : Var)
    (hyp_n_19_9h_1 : Nominal.NPrf (.imp ph (.all x ph))) :
    Nominal.NPrf (synWb (synWex x ph) ph) :=
  by
  have p0000 := @gNfi ph x hyp_n_19_9h_1
  have p0001 := @gN199t ph x
  have p0002 := Nominal.mp p0000 p0001
  exact p0002

/-- Checked nominal proof certificate identified upstream as `g_n_19_9d`. -/
@[expose]
noncomputable def gN199d (ph : Wff) (ps : Wff) (x : Var)
    (hyp_n_19_9d_1 : Nominal.NPrf (.imp ps (synWnf x ph))) :
    Nominal.NPrf (.imp ps (.imp (synWex x ph) ph)) :=
  by
  have p0000 := @gN199t ph x
  have p0001 := @gSyl ps (synWnf x ph) (synWb (synWex x ph) ph) hyp_n_19_9d_1 p0000
  have p0002 := @gBiimpd ps (synWex x ph) ph p0001
  exact p0002

/-- Checked nominal proof certificate identified upstream as `g_n_19_9`. -/
@[expose]
noncomputable def gN199 (ph : Wff) (x : Var)
    (hyp_n_19_9_1 : Nominal.NPrf (synWnf x ph)) :
    Nominal.NPrf (synWb (synWex x ph) ph) :=
  by
  have p0000 := @gNfri ph x hyp_n_19_9_1
  have p0001 := @gN199h ph x p0000
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_n_19_3`. -/
@[expose]
noncomputable def gN193 (ph : Wff) (x : Var)
    (hyp_n_19_3_1 : Nominal.NPrf (synWnf x ph)) : Nominal.NPrf (synWb (.all x ph) ph) :=
  by
  have p0000 := @gSp ph x
  have p0001 := @gNfri ph x hyp_n_19_3_1
  have p0002 := @gImpbii (.all x ph) ph p0000 p0001
  exact p0002

/-- Checked nominal proof certificate identified upstream as `g_hba1`. -/
@[expose]
noncomputable def gHba1 (ph : Wff) (x : Var) :
    Nominal.NPrf (.imp (.all x ph) (.all x (.all x ph))) :=
  by
  have p0000 := @gHbe1 (.neg ph) x
  have p0001 := @gHbn (synWex x (.neg ph)) x p0000
  have p0002 := @gAlex ph x
  have p0003 := @gAlbii (.all x ph) (.neg (synWex x (.neg ph))) x p0002
  have p0004 :=
    @gN3imtr4i (.neg (synWex x (.neg ph))) (.all x (.neg (synWex x (.neg ph))))
      (.all x ph) (.all x (.all x ph)) p0001 p0002 p0003
  exact p0004

/-- Checked nominal proof certificate identified upstream as `g_nfa1`. -/
@[expose]
noncomputable def gNfa1 (ph : Wff) (x : Var) : Nominal.NPrf (synWnf x (.all x ph)) :=
  by
  have p0000 := @gHba1 ph x
  have p0001 := @gNfi (.all x ph) x p0000
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_a5i`. -/
@[expose]
noncomputable def gA5i (ph : Wff) (ps : Wff) (x : Var)
    (hyp_a5i_1 : Nominal.NPrf (.imp (.all x ph) ps)) :
    Nominal.NPrf (.imp (.all x ph) (.all x ps)) :=
  by
  have p0000 := @gNfa1 ph x
  have p0001 := @gAlrimi (.all x ph) ps x p0000 hyp_a5i_1
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_nfnf1`. -/
@[expose]
noncomputable def gNfnf1 (ph : Wff) (x : Var) :
    Nominal.NPrf (synWnf x (synWnf x ph)) :=
  by
  have p0000 := (Nominal.biimpRefl (synWnf x ph))
  have p0001 := @gNfa1 (.imp ph (.all x ph)) x
  have p0002 := @gNfxfr (synWnf x ph) (.all x (.imp ph (.all x ph))) x p0000 p0001
  exact p0002

/-- Checked nominal proof certificate identified upstream as `g_nfnd`. -/
@[expose]
noncomputable def gNfnd (ph : Wff) (ps : Wff) (x : Var)
    (hyp_nfnd_1 : Nominal.NPrf (.imp ph (synWnf x ps))) :
    Nominal.NPrf (.imp ph (synWnf x (.neg ps))) :=
  by
  have p0000 := @gNfnf1 ps x
  have p0001 := (Nominal.biimpRefl (synWnf x ps))
  have p0002 := @gHbnt ps x
  have p0003 :=
    @gSylbi (synWnf x ps) (.all x (.imp ps (.all x ps)))
      (.imp (.neg ps) (.all x (.neg ps))) p0001 p0002
  have p0004 := @gNfd (synWnf x ps) (.neg ps) x p0000 p0003
  have p0005 := @gSyl ph (synWnf x ps) (synWnf x (.neg ps)) hyp_nfnd_1 p0004
  exact p0005

/-- Checked nominal proof certificate identified upstream as `g_nfn`. -/
@[expose]
noncomputable def gNfn (ph : Wff) (x : Var) (hyp_nfn_1 : Nominal.NPrf (synWnf x ph)) :
    Nominal.NPrf (synWnf x (.neg ph)) :=
  by
  have p0000 := @gA1i (synWnf x ph) synWtru hyp_nfn_1
  have p0001 := @gNfnd synWtru ph x p0000
  have p0002 := @gTrud (synWnf x (.neg ph)) p0001
  exact p0002

/-- Checked nominal proof certificate identified upstream as `g_n_19_38`. -/
@[expose]
noncomputable def gN1938 (ph : Wff) (ps : Wff) (x : Var) :
    Nominal.NPrf (.imp (.imp (synWex x ph) (.all x ps)) (.all x (.imp ph ps))) :=
  by
  have p0000 := @gAlnex ph x
  have p0001 := @gPm221 ph ps
  have p0002 := @gAlimi (.neg ph) (.imp ph ps) x p0001
  have p0003 :=
    @gSylbir (.neg (synWex x ph)) (.all x (.neg ph)) (.all x (.imp ph ps)) p0000 p0002
  have p0004 := Nominal.ax1 ps ph
  have p0005 := @gAlimi ps (.imp ph ps) x p0004
  have p0006 := @gJa (synWex x ph) (.all x ps) (.all x (.imp ph ps)) p0003 p0005
  exact p0006

/-- Checked nominal proof certificate identified upstream as `g_n_19_21t`. -/
@[expose]
noncomputable def gN1921t (ph : Wff) (ps : Wff) (x : Var) :
    Nominal.NPrf
      (.imp (synWnf x ph) (synWb (.all x (.imp ph ps)) (.imp ph (.all x ps)))) :=
  by
  have p0000 := @gNfr ph x
  have p0001 := Nominal.ax5 x ph ps
  have p0002 :=
    @gSyl9 (synWnf x ph) ph (.all x ph) (.all x (.imp ph ps)) (.all x ps) p0000 p0001
  have p0003 := @gN199t ph x
  have p0004 := @gImbi1d (synWnf x ph) (synWex x ph) ph (.all x ps) p0003
  have p0005 := @gN1938 ph ps x
  have p0006 :=
    @gSyl6bir (synWnf x ph) (.imp ph (.all x ps)) (.imp (synWex x ph) (.all x ps))
      (.all x (.imp ph ps)) p0004 p0005
  have p0007 :=
    @gImpbid (synWnf x ph) (.all x (.imp ph ps)) (.imp ph (.all x ps)) p0002 p0006
  exact p0007

/-- Checked nominal proof certificate identified upstream as `g_n_19_21`. -/
@[expose]
noncomputable def gN1921 (ph : Wff) (ps : Wff) (x : Var)
    (hyp_n_19_21_1 : Nominal.NPrf (synWnf x ph)) :
    Nominal.NPrf (synWb (.all x (.imp ph ps)) (.imp ph (.all x ps))) :=
  by
  have p0000 := @gN1921t ph ps x
  have p0001 := Nominal.mp hyp_n_19_21_1 p0000
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_n_19_21h`. -/
@[expose]
noncomputable def gN1921h (ph : Wff) (ps : Wff) (x : Var)
    (hyp_n_19_21h_1 : Nominal.NPrf (.imp ph (.all x ph))) :
    Nominal.NPrf (synWb (.all x (.imp ph ps)) (.imp ph (.all x ps))) :=
  by
  have p0000 := @gNfi ph x hyp_n_19_21h_1
  have p0001 := @gN1921 ph ps x p0000
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_n_19_23t`. -/
@[expose]
noncomputable def gN1923t (ph : Wff) (ps : Wff) (x : Var) :
    Nominal.NPrf
      (.imp (synWnf x ps) (synWb (.all x (.imp ph ps)) (.imp (synWex x ph) ps))) :=
  by
  have p0000 := @gExim ph ps x
  have p0001 := @gN199t ps x
  have p0002 := @gBiimpd (synWnf x ps) (synWex x ps) ps p0001
  have p0003 :=
    @gSyl9r (.all x (.imp ph ps)) (synWex x ph) (synWex x ps) (synWnf x ps) ps p0000
      p0002
  have p0004 := @gNfr ps x
  have p0005 := @gImim2d (synWnf x ps) ps (.all x ps) (synWex x ph) p0004
  have p0006 := @gN1938 ph ps x
  have p0007 :=
    @gSyl6 (synWnf x ps) (.imp (synWex x ph) ps) (.imp (synWex x ph) (.all x ps))
      (.all x (.imp ph ps)) p0005 p0006
  have p0008 :=
    @gImpbid (synWnf x ps) (.all x (.imp ph ps)) (.imp (synWex x ph) ps) p0003 p0007
  exact p0008

/-- Checked nominal proof certificate identified upstream as `g_n_19_23`. -/
@[expose]
noncomputable def gN1923 (ph : Wff) (ps : Wff) (x : Var)
    (hyp_n_19_23_1 : Nominal.NPrf (synWnf x ps)) :
    Nominal.NPrf (synWb (.all x (.imp ph ps)) (.imp (synWex x ph) ps)) :=
  by
  have p0000 := @gN1923t ph ps x
  have p0001 := Nominal.mp hyp_n_19_23_1 p0000
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_n_19_23h`. -/
@[expose]
noncomputable def gN1923h (ph : Wff) (ps : Wff) (x : Var)
    (hyp_n_19_23h_1 : Nominal.NPrf (.imp ps (.all x ps))) :
    Nominal.NPrf (synWb (.all x (.imp ph ps)) (.imp (synWex x ph) ps)) :=
  by
  have p0000 := @gNfi ps x hyp_n_19_23h_1
  have p0001 := @gN1923 ph ps x p0000
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_exlimi`. -/
@[expose]
noncomputable def gExlimi (ph : Wff) (ps : Wff) (x : Var)
    (hyp_exlimi_1 : Nominal.NPrf (synWnf x ps))
    (hyp_exlimi_2 : Nominal.NPrf (.imp ph ps)) : Nominal.NPrf (.imp (synWex x ph) ps) :=
  by
  have p0000 := @gN1923 ph ps x hyp_exlimi_1
  have p0001 := @gMpgbi (.imp ph ps) (.imp (synWex x ph) ps) x p0000 hyp_exlimi_2
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_exlimih`. -/
@[expose]
noncomputable def gExlimih (ph : Wff) (ps : Wff) (x : Var)
    (hyp_exlimih_1 : Nominal.NPrf (.imp ps (.all x ps)))
    (hyp_exlimih_2 : Nominal.NPrf (.imp ph ps)) : Nominal.NPrf (.imp (synWex x ph) ps) :=
  by
  have p0000 := @gNfi ps x hyp_exlimih_1
  have p0001 := @gExlimi ph ps x p0000 hyp_exlimih_2
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_exlimd`. -/
@[expose]
noncomputable def gExlimd (ph : Wff) (ps : Wff) (ch : Wff) (x : Var)
    (hyp_exlimd_1 : Nominal.NPrf (synWnf x ph))
    (hyp_exlimd_2 : Nominal.NPrf (synWnf x ch))
    (hyp_exlimd_3 : Nominal.NPrf (.imp ph (.imp ps ch))) :
    Nominal.NPrf (.imp ph (.imp (synWex x ps) ch)) :=
  by
  have p0000 := @gAlrimi ph (.imp ps ch) x hyp_exlimd_1 hyp_exlimd_3
  have p0001 := @gN1923 ps ch x hyp_exlimd_2
  have p0002 := @gSylib ph (.all x (.imp ps ch)) (.imp (synWex x ps) ch) p0000 p0001
  exact p0002

/-- Checked nominal proof certificate identified upstream as `g_nfimd`. -/
@[expose]
noncomputable def gNfimd (ph : Wff) (ps : Wff) (ch : Wff) (x : Var)
    (hyp_nfimd_1 : Nominal.NPrf (.imp ph (synWnf x ps)))
    (hyp_nfimd_2 : Nominal.NPrf (.imp ph (synWnf x ch))) :
    Nominal.NPrf (.imp ph (synWnf x (.imp ps ch))) :=
  by
  have p0000 := @gNfnf1 ps x
  have p0001 := @gNfnf1 ch x
  have p0002 := @gNfr ch x
  have p0003 := @gImim2d (synWnf x ch) ch (.all x ch) ps p0002
  have p0004 := @gN1921t ps ch x
  have p0005 :=
    @gBiimprd (synWnf x ps) (.all x (.imp ps ch)) (.imp ps (.all x ch)) p0004
  have p0006 :=
    @gSyl9r (synWnf x ch) (.imp ps ch) (.imp ps (.all x ch)) (synWnf x ps)
      (.all x (.imp ps ch)) p0003 p0005
  have p0007 :=
    @gAlrimd (synWnf x ps) (synWnf x ch) (.imp (.imp ps ch) (.all x (.imp ps ch))) x
      p0000 p0001 p0006
  have p0008 := (Nominal.biimpRefl (synWnf x (.imp ps ch)))
  have p0009 :=
    @gSyl6ibr (synWnf x ps) (synWnf x ch)
      (.all x (.imp (.imp ps ch) (.all x (.imp ps ch)))) (synWnf x (.imp ps ch)) p0007
      p0008
  have p0010 :=
    @gSylc ph (synWnf x ps) (synWnf x ch) (synWnf x (.imp ps ch)) hyp_nfimd_1
      hyp_nfimd_2 p0009
  exact p0010

/-- Checked nominal proof certificate identified upstream as `g_hbim1`. -/
@[expose]
noncomputable def gHbim1 (ph : Wff) (ps : Wff) (x : Var)
    (hyp_hbim1_1 : Nominal.NPrf (.imp ph (.all x ph)))
    (hyp_hbim1_2 : Nominal.NPrf (.imp ph (.imp ps (.all x ps)))) :
    Nominal.NPrf (.imp (.imp ph ps) (.all x (.imp ph ps))) :=
  by
  have p0000 := @gA2i ph ps (.all x ps) hyp_hbim1_2
  have p0001 := @gN1921h ph ps x hyp_hbim1_1
  have p0002 :=
    @gSylibr (.imp ph ps) (.imp ph (.all x ps)) (.all x (.imp ph ps)) p0000 p0001
  exact p0002

/-- Checked nominal proof certificate identified upstream as `g_nfim1`. -/
@[expose]
noncomputable def gNfim1 (ph : Wff) (ps : Wff) (x : Var)
    (hyp_nfim1_1 : Nominal.NPrf (synWnf x ph))
    (hyp_nfim1_2 : Nominal.NPrf (.imp ph (synWnf x ps))) :
    Nominal.NPrf (synWnf x (.imp ph ps)) :=
  by
  have p0000 := @gNfri ph x hyp_nfim1_1
  have p0001 := @gNfrd ph ps x hyp_nfim1_2
  have p0002 := @gHbim1 ph ps x p0000 p0001
  have p0003 := @gNfi (.imp ph ps) x p0002
  exact p0003

/-- Checked nominal proof certificate identified upstream as `g_nfim`. -/
@[expose]
noncomputable def gNfim (ph : Wff) (ps : Wff) (x : Var)
    (hyp_nfim_1 : Nominal.NPrf (synWnf x ph))
    (hyp_nfim_2 : Nominal.NPrf (synWnf x ps)) : Nominal.NPrf (synWnf x (.imp ph ps)) :=
  by
  have p0000 := @gA1i (synWnf x ps) ph hyp_nfim_2
  have p0001 := @gNfim1 ph ps x hyp_nfim_1 p0000
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_hbimd`. -/
@[expose]
noncomputable def gHbimd (ph : Wff) (ps : Wff) (ch : Wff) (x : Var)
    (hyp_hbimd_1 : Nominal.NPrf (.imp ph (.all x ph)))
    (hyp_hbimd_2 : Nominal.NPrf (.imp ph (.imp ps (.all x ps))))
    (hyp_hbimd_3 : Nominal.NPrf (.imp ph (.imp ch (.all x ch)))) :
    Nominal.NPrf (.imp ph (.imp (.imp ps ch) (.all x (.imp ps ch)))) :=
  by
  have p0000 := @gNfdh ph ps x hyp_hbimd_1 hyp_hbimd_2
  have p0001 := @gNfdh ph ch x hyp_hbimd_1 hyp_hbimd_3
  have p0002 := @gNfimd ph ps ch x p0000 p0001
  have p0003 := @gNfrd ph (.imp ps ch) x p0002
  exact p0003

/-- Checked nominal proof certificate identified upstream as `g_hbim`. -/
@[expose]
noncomputable def gHbim (ph : Wff) (ps : Wff) (x : Var)
    (hyp_hbim_1 : Nominal.NPrf (.imp ph (.all x ph)))
    (hyp_hbim_2 : Nominal.NPrf (.imp ps (.all x ps))) :
    Nominal.NPrf (.imp (.imp ph ps) (.all x (.imp ph ps))) :=
  by
  have p0000 := @gA1i (.imp ps (.all x ps)) ph hyp_hbim_2
  have p0001 := @gHbim1 ph ps x hyp_hbim_1 p0000
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_nfand`. -/
@[expose]
noncomputable def gNfand (ph : Wff) (ps : Wff) (ch : Wff) (x : Var)
    (hyp_nfand_1 : Nominal.NPrf (.imp ph (synWnf x ps)))
    (hyp_nfand_2 : Nominal.NPrf (.imp ph (synWnf x ch))) :
    Nominal.NPrf (.imp ph (synWnf x (synWa ps ch))) :=
  by
  have p0000 := (Nominal.biimpRefl (synWa ps ch))
  have p0001 := @gNfnd ph ch x hyp_nfand_2
  have p0002 := @gNfimd ph ps (.neg ch) x hyp_nfand_1 p0001
  have p0003 := @gNfnd ph (.imp ps (.neg ch)) x p0002
  have p0004 := @gNfxfrd (synWa ps ch) (.neg (.imp ps (.neg ch))) ph x p0000 p0003
  exact p0004

/-- Checked nominal proof certificate identified upstream as `g_nfan`. -/
@[expose]
noncomputable def gNfan (ph : Wff) (ps : Wff) (x : Var)
    (hyp_nfan_1 : Nominal.NPrf (synWnf x ph))
    (hyp_nfan_2 : Nominal.NPrf (synWnf x ps)) :
    Nominal.NPrf (synWnf x (synWa ph ps)) :=
  by
  have p0000 := @gA1i (synWnf x ph) synWtru hyp_nfan_1
  have p0001 := @gA1i (synWnf x ps) synWtru hyp_nfan_2
  have p0002 := @gNfand synWtru ph ps x p0000 p0001
  have p0003 := @gTrud (synWnf x (synWa ph ps)) p0002
  exact p0003

/-- Checked nominal proof certificate identified upstream as `g_nfnan`. -/
@[expose]
noncomputable def gNfnan (ph : Wff) (ps : Wff) (x : Var)
    (hyp_nfan_1 : Nominal.NPrf (synWnf x ph))
    (hyp_nfan_2 : Nominal.NPrf (synWnf x ps)) :
    Nominal.NPrf (synWnf x (synWnan ph ps)) :=
  by
  have p0000 := (Nominal.biimpRefl (synWnan ph ps))
  have p0001 := @gNfan ph ps x hyp_nfan_1 hyp_nfan_2
  have p0002 := @gNfn (synWa ph ps) x p0001
  have p0003 := @gNfxfr (synWnan ph ps) (.neg (synWa ph ps)) x p0000 p0002
  exact p0003

/-- Checked nominal proof certificate identified upstream as `g_hban`. -/
@[expose]
noncomputable def gHban (ph : Wff) (ps : Wff) (x : Var)
    (hyp_hb_1 : Nominal.NPrf (.imp ph (.all x ph)))
    (hyp_hb_2 : Nominal.NPrf (.imp ps (.all x ps))) :
    Nominal.NPrf (.imp (synWa ph ps) (.all x (synWa ph ps))) :=
  by
  have p0000 := @gNfi ph x hyp_hb_1
  have p0001 := @gNfi ps x hyp_hb_2
  have p0002 := @gNfan ph ps x p0000 p0001
  have p0003 := @gNfri (synWa ph ps) x p0002
  exact p0003

/-- Checked nominal proof certificate identified upstream as `g_nfbid`. -/
@[expose]
noncomputable def gNfbid (ph : Wff) (ps : Wff) (ch : Wff) (x : Var)
    (hyp_nfbid_1 : Nominal.NPrf (.imp ph (synWnf x ps)))
    (hyp_nfbid_2 : Nominal.NPrf (.imp ph (synWnf x ch))) :
    Nominal.NPrf (.imp ph (synWnf x (synWb ps ch))) :=
  by
  have p0000 := @gDfbi2 ps ch
  have p0001 := @gNfimd ph ps ch x hyp_nfbid_1 hyp_nfbid_2
  have p0002 := @gNfimd ph ch ps x hyp_nfbid_2 hyp_nfbid_1
  have p0003 := @gNfand ph (.imp ps ch) (.imp ch ps) x p0001 p0002
  have p0004 :=
    @gNfxfrd (synWb ps ch) (synWa (.imp ps ch) (.imp ch ps)) ph x p0000 p0003
  exact p0004

/-- Checked nominal proof certificate identified upstream as `g_nfbi`. -/
@[expose]
noncomputable def gNfbi (ph : Wff) (ps : Wff) (x : Var)
    (hyp_nf_1 : Nominal.NPrf (synWnf x ph)) (hyp_nf_2 : Nominal.NPrf (synWnf x ps)) :
    Nominal.NPrf (synWnf x (synWb ph ps)) :=
  by
  have p0000 := @gA1i (synWnf x ph) synWtru hyp_nf_1
  have p0001 := @gA1i (synWnf x ps) synWtru hyp_nf_2
  have p0002 := @gNfbid synWtru ph ps x p0000 p0001
  have p0003 := @gTrud (synWnf x (synWb ph ps)) p0002
  exact p0003

/-- Checked nominal proof certificate identified upstream as `g_equsalhw`. -/
@[expose]
noncomputable def gEqusalhw (ph : Wff) (ps : Wff) (x : Var) (y : Var) (dv_x_y : x ≠ y)
    (hyp_equsalhw_1 : Nominal.NPrf (.imp ps (.all x ps)))
    (hyp_equsalhw_2 : Nominal.NPrf (.imp (.objEq x y) (synWb ph ps))) :
    Nominal.NPrf (synWb (.all x (.imp (.objEq x y) ph)) ps) :=
  by
  let proofSupport : Finset Var :=
    ph.fv ∪ ps.fv ∪ ({ x } : Finset Var) ∪ ({ y } : Finset Var)
  have p0000 := @gN1923h (.objEq x y) ps x hyp_equsalhw_1
  have p0001 := @gPm574i (.objEq x y) ph ps hyp_equsalhw_2
  have p0002 := @gAlbii (.imp (.objEq x y) ph) (.imp (.objEq x y) ps) x p0001
  have p0003 :=
    @gA9ev x y
      (by
        first
        | (aesop))
  have p0004 := @gA1bi (synWex x (.objEq x y)) ps p0003
  have p0005 :=
    @gN3bitr4i (.all x (.imp (.objEq x y) ps)) (.imp (synWex x (.objEq x y)) ps)
      (.all x (.imp (.objEq x y) ph)) ps p0000 p0002 p0004
  exact p0005

/-- Checked nominal proof certificate identified upstream as `g_hbex`. -/
@[expose]
noncomputable def gHbex (ph : Wff) (x : Var) (y : Var)
    (hyp_hbex_1 : Nominal.NPrf (.imp ph (.all x ph))) :
    Nominal.NPrf (.imp (synWex y ph) (.all x (synWex y ph))) :=
  by
  have p0000 := (Nominal.biimpRefl (synWex y ph))
  have p0001 := @gHbn ph x hyp_hbex_1
  have p0002 := @gHbal (.neg ph) x y p0001
  have p0003 := @gHbn (.all y (.neg ph)) x p0002
  have p0004 := @gHbxfrbi (synWex y ph) (.neg (.all y (.neg ph))) x p0000 p0003
  exact p0004

/-- Checked nominal proof certificate identified upstream as `g_nfal`. -/
@[expose]
noncomputable def gNfal (ph : Wff) (x : Var) (y : Var)
    (hyp_nfal_1 : Nominal.NPrf (synWnf x ph)) : Nominal.NPrf (synWnf x (.all y ph)) :=
  by
  have p0000 := @gNfri ph x hyp_nfal_1
  have p0001 := @gHbal ph x y p0000
  have p0002 := @gNfi (.all y ph) x p0001
  exact p0002

/-- Checked nominal proof certificate identified upstream as `g_nfex`. -/
@[expose]
noncomputable def gNfex (ph : Wff) (x : Var) (y : Var)
    (hyp_nfal_1 : Nominal.NPrf (synWnf x ph)) :
    Nominal.NPrf (synWnf x (synWex y ph)) :=
  by
  have p0000 := @gNfri ph x hyp_nfal_1
  have p0001 := @gHbex ph x y p0000
  have p0002 := @gNfi (synWex y ph) x p0001
  exact p0002

/-- Checked nominal proof certificate identified upstream as `g_n_19_12`. -/
@[expose]
noncomputable def gN1912 (ph : Wff) (x : Var) (y : Var) :
    Nominal.NPrf (.imp (synWex x (.all y ph)) (.all y (synWex x ph))) :=
  by
  have p0000 := @gNfa1 ph y
  have p0001 := @gNfex (.all y ph) y x p0000
  have p0002 := @gSp ph y
  have p0003 := @gEximi (.all y ph) ph x p0002
  have p0004 := @gAlrimi (synWex x (.all y ph)) (synWex x ph) y p0001 p0003
  exact p0004

/-- Checked nominal proof certificate identified upstream as `g_dvelimhw`. -/
@[expose]
noncomputable def gDvelimhw (ph : Wff) (ps : Wff) (x : Var) (y : Var) (z : Var)
    (_dv_x_z : x ≠ z) (dv_y_z : y ≠ z)
    (hyp_dvelimhw_1 : Nominal.NPrf (.imp ph (.all x ph)))
    (hyp_dvelimhw_2 : Nominal.NPrf (.imp ps (.all z ps)))
    (hyp_dvelimhw_3 : Nominal.NPrf (.imp (.objEq z y) (synWb ph ps)))
    (hyp_dvelimhw_4 : Nominal.NPrf
        (.imp (.neg (.all x (.objEq x y))) (.imp (.objEq y z) (.all x (.objEq y z))))) :
    Nominal.NPrf (.imp (.neg (.all x (.objEq x y))) (.imp ps (.all x ps))) :=
  by
  let proofSupport : Finset Var :=
    ph.fv ∪ ps.fv ∪ ({ x } : Finset Var) ∪ ({ y } : Finset Var) ∪ ({ z } : Finset Var)
  have p0000 :=
    Nominal.ax17 (.neg (.all x (.objEq x y))) z
      (by
        first
        |
          (simp (config :=
              { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_wff_neg,
              NFChoice.Compiler.CoreFVSimp.fv_wff_all,
              NFChoice.Compiler.CoreFVSimp.fv_wff_objEq, Finset.mem_erase] at ⊢;
            aesop))
  have p0001 := @gHbn1 (.objEq x y) x
  have p0002 := @gEqucomi z y
  have p0003 := @gEqucomi y z
  have p0004 := @gAlimi (.objEq y z) (.objEq z y) x p0003
  have p0005 :=
    @gSyl56 (.objEq z y) (.objEq y z) (.neg (.all x (.objEq x y))) (.all x (.objEq y z))
      (.all x (.objEq z y)) p0002 hyp_dvelimhw_4 p0004
  have p0006 := @gA1i (.imp ph (.all x ph)) (.neg (.all x (.objEq x y))) hyp_dvelimhw_1
  have p0007 := @gHbimd (.neg (.all x (.objEq x y))) (.objEq z y) ph x p0001 p0005 p0006
  have p0008 :=
    @gHbald (.neg (.all x (.objEq x y))) (.imp (.objEq z y) ph) x z p0000 p0007
  have p0009 :=
    @gEqusalhw ph ps z y
      (by
        first
        | (aesop))
      hyp_dvelimhw_2 hyp_dvelimhw_3
  have p0010 := @gAlbii (.all z (.imp (.objEq z y) ph)) ps x p0009
  have p0011 :=
    @gN3imtr3g (.neg (.all x (.objEq x y))) (.all z (.imp (.objEq z y) ph))
      (.all x (.all z (.imp (.objEq z y) ph))) ps (.all x ps) p0008 p0009 p0010
  exact p0011

/-- Checked nominal proof certificate identified upstream as `g_nfald`. -/
@[expose]
noncomputable def gNfald (ph : Wff) (ps : Wff) (x : Var) (y : Var)
    (hyp_nfald_1 : Nominal.NPrf (synWnf y ph))
    (hyp_nfald_2 : Nominal.NPrf (.imp ph (synWnf x ps))) :
    Nominal.NPrf (.imp ph (synWnf x (.all y ps))) :=
  by
  have p0000 := @gAlrimi ph (synWnf x ps) y hyp_nfald_1 hyp_nfald_2
  have p0001 := @gNfnf1 ps x
  have p0002 := @gNfal (synWnf x ps) x y p0001
  have p0003 := @gHba1 (synWnf x ps) y
  have p0004 := @gSp (synWnf x ps) y
  have p0005 := @gNfrd (.all y (synWnf x ps)) ps x p0004
  have p0006 := @gHbald (.all y (synWnf x ps)) ps x y p0003 p0005
  have p0007 := @gNfd (.all y (synWnf x ps)) (.all y ps) x p0002 p0006
  have p0008 := @gSyl ph (.all y (synWnf x ps)) (synWnf x (.all y ps)) p0000 p0007
  exact p0008

/-- Checked nominal proof certificate identified upstream as `g_nfexd`. -/
@[expose]
noncomputable def gNfexd (ph : Wff) (ps : Wff) (x : Var) (y : Var)
    (hyp_nfald_1 : Nominal.NPrf (synWnf y ph))
    (hyp_nfald_2 : Nominal.NPrf (.imp ph (synWnf x ps))) :
    Nominal.NPrf (.imp ph (synWnf x (synWex y ps))) :=
  by
  have p0000 := (Nominal.biimpRefl (synWex y ps))
  have p0001 := @gNfnd ph ps x hyp_nfald_2
  have p0002 := @gNfald ph (.neg ps) x y hyp_nfald_1 p0001
  have p0003 := @gNfnd ph (.all y (.neg ps)) x p0002
  have p0004 := @gNfxfrd (synWex y ps) (.neg (.all y (.neg ps))) ph x p0000 p0003
  exact p0004

/-- Checked nominal proof certificate identified upstream as `g_nfa2`. -/
@[expose]
noncomputable def gNfa2 (ph : Wff) (x : Var) (y : Var) :
    Nominal.NPrf (synWnf x (.all y (.all x ph))) :=
  by
  have p0000 := @gNfa1 ph x
  have p0001 := @gNfal (.all x ph) x y p0000
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_n_19_21bbi`. -/
@[expose]
noncomputable def gN1921bbi (ph : Wff) (ps : Wff) (x : Var) (y : Var)
    (hyp_n_19_21bbi_1 : Nominal.NPrf (.imp ph (.all x (.all y ps)))) :
    Nominal.NPrf (.imp ph ps) :=
  by
  have p0000 := @gN1921bi ph (.all y ps) x hyp_n_19_21bbi_1
  have p0001 := @gN1921bi ph ps y p0000
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_n_19_27`. -/
@[expose]
noncomputable def gN1927 (ph : Wff) (ps : Wff) (x : Var)
    (hyp_n_19_27_1 : Nominal.NPrf (synWnf x ps)) :
    Nominal.NPrf (synWb (.all x (synWa ph ps)) (synWa (.all x ph) ps)) :=
  by
  have p0000 := @gN1926 ph ps x
  have p0001 := @gN193 ps x hyp_n_19_27_1
  have p0002 := @gAnbi2i (.all x ps) ps (.all x ph) p0001
  have p0003 :=
    @gBitri (.all x (synWa ph ps)) (synWa (.all x ph) (.all x ps))
      (synWa (.all x ph) ps) p0000 p0002
  exact p0003

/-- Checked nominal proof certificate identified upstream as `g_n_19_28`. -/
@[expose]
noncomputable def gN1928 (ph : Wff) (ps : Wff) (x : Var)
    (hyp_n_19_28_1 : Nominal.NPrf (synWnf x ph)) :
    Nominal.NPrf (synWb (.all x (synWa ph ps)) (synWa ph (.all x ps))) :=
  by
  have p0000 := @gN1926 ph ps x
  have p0001 := @gN193 ph x hyp_n_19_28_1
  have p0002 := @gAnbi1i (.all x ph) ph (.all x ps) p0001
  have p0003 :=
    @gBitri (.all x (synWa ph ps)) (synWa (.all x ph) (.all x ps))
      (synWa ph (.all x ps)) p0000 p0002
  exact p0003

/-- Checked nominal proof certificate identified upstream as `g_n_19_36`. -/
@[expose]
noncomputable def gN1936 (ph : Wff) (ps : Wff) (x : Var)
    (hyp_n_19_36_1 : Nominal.NPrf (synWnf x ps)) :
    Nominal.NPrf (synWb (synWex x (.imp ph ps)) (.imp (.all x ph) ps)) :=
  by
  have p0000 := @gN1935 ph ps x
  have p0001 := @gN199 ps x hyp_n_19_36_1
  have p0002 := @gImbi2i (synWex x ps) ps (.all x ph) p0001
  have p0003 :=
    @gBitri (synWex x (.imp ph ps)) (.imp (.all x ph) (synWex x ps))
      (.imp (.all x ph) ps) p0000 p0002
  exact p0003

/-- Checked nominal proof certificate identified upstream as `g_n_19_36i`. -/
@[expose]
noncomputable def gN1936i (ph : Wff) (ps : Wff) (x : Var)
    (hyp_n_19_36_1 : Nominal.NPrf (synWnf x ps))
    (hyp_n_19_36i_2 : Nominal.NPrf (synWex x (.imp ph ps))) :
    Nominal.NPrf (.imp (.all x ph) ps) :=
  by
  have p0000 := @gN1936 ph ps x hyp_n_19_36_1
  have p0001 :=
    @gMpbi (synWex x (.imp ph ps)) (.imp (.all x ph) ps) hyp_n_19_36i_2 p0000
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_n_19_37`. -/
@[expose]
noncomputable def gN1937 (ph : Wff) (ps : Wff) (x : Var)
    (hyp_n_19_37_1 : Nominal.NPrf (synWnf x ph)) :
    Nominal.NPrf (synWb (synWex x (.imp ph ps)) (.imp ph (synWex x ps))) :=
  by
  have p0000 := @gN1935 ph ps x
  have p0001 := @gN193 ph x hyp_n_19_37_1
  have p0002 := @gImbi1i (.all x ph) ph (synWex x ps) p0001
  have p0003 :=
    @gBitri (synWex x (.imp ph ps)) (.imp (.all x ph) (synWex x ps))
      (.imp ph (synWex x ps)) p0000 p0002
  exact p0003

/-- Checked nominal proof certificate identified upstream as `g_n_19_41`. -/
@[expose]
noncomputable def gN1941 (ph : Wff) (ps : Wff) (x : Var)
    (hyp_n_19_41_1 : Nominal.NPrf (synWnf x ps)) :
    Nominal.NPrf (synWb (synWex x (synWa ph ps)) (synWa (synWex x ph) ps)) :=
  by
  have p0000 := @gN1940 ph ps x
  have p0001 := @gId ps
  have p0002 := @gExlimi ps ps x hyp_n_19_41_1 p0001
  have p0003 := @gAnim2i (synWex x ps) ps (synWex x ph) p0002
  have p0004 :=
    @gSyl (synWex x (synWa ph ps)) (synWa (synWex x ph) (synWex x ps))
      (synWa (synWex x ph) ps) p0000 p0003
  have p0005 := @gPm321 ps ph
  have p0006 := @gEximd ps ph (synWa ph ps) x hyp_n_19_41_1 p0005
  have p0007 := @gImpcom ps (synWex x ph) (synWex x (synWa ph ps)) p0006
  have p0008 :=
    @gImpbii (synWex x (synWa ph ps)) (synWa (synWex x ph) ps) p0004 p0007
  exact p0008

/-- Checked nominal proof certificate identified upstream as `g_n_19_42`. -/
@[expose]
noncomputable def gN1942 (ph : Wff) (ps : Wff) (x : Var)
    (hyp_n_19_42_1 : Nominal.NPrf (synWnf x ph)) :
    Nominal.NPrf (synWb (synWex x (synWa ph ps)) (synWa ph (synWex x ps))) :=
  by
  have p0000 := @gN1941 ps ph x hyp_n_19_42_1
  have p0001 := @gExancom ph ps x
  have p0002 := @gAncom ph (synWex x ps)
  have p0003 :=
    @gN3bitr4i (synWex x (synWa ps ph)) (synWa (synWex x ps) ph)
      (synWex x (synWa ph ps)) (synWa ph (synWex x ps)) p0000 p0001 p0002
  exact p0003

/-- Checked nominal proof certificate identified upstream as `g_nfan1`. -/
@[expose]
noncomputable def gNfan1 (ph : Wff) (ps : Wff) (x : Var)
    (hyp_nfan1_1 : Nominal.NPrf (synWnf x ph))
    (hyp_nfan1_2 : Nominal.NPrf (.imp ph (synWnf x ps))) :
    Nominal.NPrf (synWnf x (synWa ph ps)) :=
  by
  have p0000 := @gNfrd ph ps x hyp_nfan1_2
  have p0001 := @gImdistani ph ps (.all x ps) p0000
  have p0002 := @gN1928 ph ps x hyp_nfan1_1
  have p0003 :=
    @gSylibr (synWa ph ps) (synWa ph (.all x ps)) (.all x (synWa ph ps)) p0001 p0002
  have p0004 := @gNfi (synWa ph ps) x p0003
  exact p0004

/-- Checked nominal proof certificate identified upstream as `g_aaan`. -/
@[expose]
noncomputable def gAaan (ph : Wff) (ps : Wff) (x : Var) (y : Var)
    (hyp_aaan_1 : Nominal.NPrf (synWnf y ph))
    (hyp_aaan_2 : Nominal.NPrf (synWnf x ps)) :
    Nominal.NPrf
      (synWb (.all x (.all y (synWa ph ps))) (synWa (.all x ph) (.all y ps))) :=
  by
  have p0000 := @gN1928 ph ps y hyp_aaan_1
  have p0001 := @gAlbii (.all y (synWa ph ps)) (synWa ph (.all y ps)) x p0000
  have p0002 := @gNfal ps x y hyp_aaan_2
  have p0003 := @gN1927 ph (.all y ps) x p0002
  have p0004 :=
    @gBitri (.all x (.all y (synWa ph ps))) (.all x (synWa ph (.all y ps)))
      (synWa (.all x ph) (.all y ps)) p0001 p0003
  exact p0004

/-- Checked nominal proof certificate identified upstream as `g_equs5a`. -/
@[expose]
noncomputable def gEqus5a (ph : Wff) (x : Var) (y : Var) :
    Nominal.NPrf
      (.imp (synWex x (synWa (.objEq x y) (.all y ph))) (.all x (.imp (.objEq x y) ph))) :=
  by
  have p0000 := @gNfa1 (.imp (.objEq x y) ph) x
  have p0001 := Nominal.ax11Structural x y ph
  have p0002 := @gImp (.objEq x y) (.all y ph) (.all x (.imp (.objEq x y) ph)) p0001
  have p0003 :=
    @gExlimi (synWa (.objEq x y) (.all y ph)) (.all x (.imp (.objEq x y) ph)) x p0000
      p0002
  exact p0003

/-- Checked nominal proof certificate identified upstream as `g_n_19_21v`. -/
@[expose]
noncomputable def gN1921v (ph : Wff) (ps : Wff) (x : Var) (dv_ph_x : x ∉ ph.fv) :
    Nominal.NPrf (synWb (.all x (.imp ph ps)) (.imp ph (.all x ps))) :=
  by
  let proofSupport : Finset Var := ph.fv ∪ ps.fv ∪ ({ x } : Finset Var)
  have p0000 :=
    @gNfv ph x
      (by
        first
        | (aesop))
  have p0001 := @gN1921 ph ps x p0000
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_n_19_23v`. -/
@[expose]
noncomputable def gN1923v (ph : Wff) (ps : Wff) (x : Var) (dv_ps_x : x ∉ ps.fv) :
    Nominal.NPrf (synWb (.all x (.imp ph ps)) (.imp (synWex x ph) ps)) :=
  by
  let proofSupport : Finset Var := ph.fv ∪ ps.fv ∪ ({ x } : Finset Var)
  have p0000 :=
    @gNfv ps x
      (by
        first
        | (aesop))
  have p0001 := @gN1923 ph ps x p0000
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_n_19_23vv`. -/
@[expose]
noncomputable def gN1923vv (ph : Wff) (ps : Wff) (x : Var) (y : Var)
    (dv_ps_x : x ∉ ps.fv) (dv_ps_y : y ∉ ps.fv) :
    Nominal.NPrf
      (synWb (.all x (.all y (.imp ph ps))) (.imp (synWex x (synWex y ph)) ps)) :=
  by
  let proofSupport : Finset Var :=
    ph.fv ∪ ps.fv ∪ ({ x } : Finset Var) ∪ ({ y } : Finset Var)
  have p0000 :=
    @gN1923v ph ps y
      (by
        first
        | (aesop))
  have p0001 := @gAlbii (.all y (.imp ph ps)) (.imp (synWex y ph) ps) x p0000
  have p0002 :=
    @gN1923v (synWex y ph) ps x
      (by
        first
        | (aesop))
  have p0003 :=
    @gBitri (.all x (.all y (.imp ph ps))) (.all x (.imp (synWex y ph) ps))
      (.imp (synWex x (synWex y ph)) ps) p0001 p0002
  exact p0003

/-- Checked nominal proof certificate identified upstream as `g_n_19_27v`. -/
@[expose]
noncomputable def gN1927v (ph : Wff) (ps : Wff) (x : Var) (dv_ps_x : x ∉ ps.fv) :
    Nominal.NPrf (synWb (.all x (synWa ph ps)) (synWa (.all x ph) ps)) :=
  by
  let proofSupport : Finset Var := ph.fv ∪ ps.fv ∪ ({ x } : Finset Var)
  have p0000 :=
    @gNfv ps x
      (by
        first
        | (aesop))
  have p0001 := @gN1927 ph ps x p0000
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_n_19_28v`. -/
@[expose]
noncomputable def gN1928v (ph : Wff) (ps : Wff) (x : Var) (dv_ph_x : x ∉ ph.fv) :
    Nominal.NPrf (synWb (.all x (synWa ph ps)) (synWa ph (.all x ps))) :=
  by
  let proofSupport : Finset Var := ph.fv ∪ ps.fv ∪ ({ x } : Finset Var)
  have p0000 :=
    @gNfv ph x
      (by
        first
        | (aesop))
  have p0001 := @gN1928 ph ps x p0000
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_n_19_36v`. -/
@[expose]
noncomputable def gN1936v (ph : Wff) (ps : Wff) (x : Var) (dv_ps_x : x ∉ ps.fv) :
    Nominal.NPrf (synWb (synWex x (.imp ph ps)) (.imp (.all x ph) ps)) :=
  by
  let proofSupport : Finset Var := ph.fv ∪ ps.fv ∪ ({ x } : Finset Var)
  have p0000 :=
    @gNfv ps x
      (by
        first
        | (aesop))
  have p0001 := @gN1936 ph ps x p0000
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_n_19_36aiv`. -/
@[expose]
noncomputable def gN1936aiv (ph : Wff) (ps : Wff) (x : Var) (dv_ps_x : x ∉ ps.fv)
    (hyp_n_19_36aiv_1 : Nominal.NPrf (synWex x (.imp ph ps))) :
    Nominal.NPrf (.imp (.all x ph) ps) :=
  by
  let proofSupport : Finset Var := ph.fv ∪ ps.fv ∪ ({ x } : Finset Var)
  have p0000 :=
    @gNfv ps x
      (by
        first
        | (aesop))
  have p0001 := @gN1936i ph ps x p0000 hyp_n_19_36aiv_1
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_n_19_37v`. -/
@[expose]
noncomputable def gN1937v (ph : Wff) (ps : Wff) (x : Var) (dv_ph_x : x ∉ ph.fv) :
    Nominal.NPrf (synWb (synWex x (.imp ph ps)) (.imp ph (synWex x ps))) :=
  by
  let proofSupport : Finset Var := ph.fv ∪ ps.fv ∪ ({ x } : Finset Var)
  have p0000 :=
    @gNfv ph x
      (by
        first
        | (aesop))
  have p0001 := @gN1937 ph ps x p0000
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_n_19_37aiv`. -/
@[expose]
noncomputable def gN1937aiv (ph : Wff) (ps : Wff) (x : Var) (dv_ph_x : x ∉ ph.fv)
    (hyp_n_19_37aiv_1 : Nominal.NPrf (synWex x (.imp ph ps))) :
    Nominal.NPrf (.imp ph (synWex x ps)) :=
  by
  let proofSupport : Finset Var := ph.fv ∪ ps.fv ∪ ({ x } : Finset Var)
  have p0000 :=
    @gN1937v ph ps x
      (by
        first
        | (aesop))
  have p0001 :=
    @gMpbi (synWex x (.imp ph ps)) (.imp ph (synWex x ps)) hyp_n_19_37aiv_1 p0000
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_n_19_41v`. -/
@[expose]
noncomputable def gN1941v (ph : Wff) (ps : Wff) (x : Var) (dv_ps_x : x ∉ ps.fv) :
    Nominal.NPrf (synWb (synWex x (synWa ph ps)) (synWa (synWex x ph) ps)) :=
  by
  let proofSupport : Finset Var := ph.fv ∪ ps.fv ∪ ({ x } : Finset Var)
  have p0000 :=
    @gNfv ps x
      (by
        first
        | (aesop))
  have p0001 := @gN1941 ph ps x p0000
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_n_19_41vv`. -/
@[expose]
noncomputable def gN1941vv (ph : Wff) (ps : Wff) (x : Var) (y : Var)
    (dv_ps_x : x ∉ ps.fv) (dv_ps_y : y ∉ ps.fv) :
    Nominal.NPrf
      (synWb (synWex x (synWex y (synWa ph ps))) (synWa (synWex x (synWex y ph)) ps)) :=
  by
  let proofSupport : Finset Var :=
    ph.fv ∪ ps.fv ∪ ({ x } : Finset Var) ∪ ({ y } : Finset Var)
  have p0000 :=
    @gN1941v ph ps y
      (by
        first
        | (aesop))
  have p0001 := @gExbii (synWex y (synWa ph ps)) (synWa (synWex y ph) ps) x p0000
  have p0002 :=
    @gN1941v (synWex y ph) ps x
      (by
        first
        | (aesop))
  have p0003 :=
    @gBitri (synWex x (synWex y (synWa ph ps))) (synWex x (synWa (synWex y ph) ps))
      (synWa (synWex x (synWex y ph)) ps) p0001 p0002
  exact p0003

/-- Checked nominal proof certificate identified upstream as `g_n_19_41vvv`. -/
@[expose]
noncomputable def gN1941vvv (ph : Wff) (ps : Wff) (x : Var) (y : Var) (z : Var)
    (dv_ps_x : x ∉ ps.fv) (dv_ps_y : y ∉ ps.fv) (dv_ps_z : z ∉ ps.fv) :
    Nominal.NPrf
      (synWb (synWex x (synWex y (synWex z (synWa ph ps))))
        (synWa (synWex x (synWex y (synWex z ph))) ps)) :=
  by
  let proofSupport : Finset Var :=
    ph.fv ∪ ps.fv ∪ ({ x } : Finset Var) ∪ ({ y } : Finset Var) ∪ ({ z } : Finset Var)
  have p0000 :=
    @gN1941vv ph ps y z
      (by
        first
        | (aesop))
      (by
        first
        | (aesop))
  have p0001 :=
    @gExbii (synWex y (synWex z (synWa ph ps))) (synWa (synWex y (synWex z ph)) ps)
      x p0000
  have p0002 :=
    @gN1941v (synWex y (synWex z ph)) ps x
      (by
        first
        | (aesop))
  have p0003 :=
    @gBitri (synWex x (synWex y (synWex z (synWa ph ps))))
      (synWex x (synWa (synWex y (synWex z ph)) ps))
      (synWa (synWex x (synWex y (synWex z ph))) ps) p0001 p0002
  exact p0003

/-- Checked nominal proof certificate identified upstream as `g_n_19_42v`. -/
@[expose]
noncomputable def gN1942v (ph : Wff) (ps : Wff) (x : Var) (dv_ph_x : x ∉ ph.fv) :
    Nominal.NPrf (synWb (synWex x (synWa ph ps)) (synWa ph (synWex x ps))) :=
  by
  let proofSupport : Finset Var := ph.fv ∪ ps.fv ∪ ({ x } : Finset Var)
  have p0000 :=
    @gNfv ph x
      (by
        first
        | (aesop))
  have p0001 := @gN1942 ph ps x p0000
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_exdistr`. -/
@[expose]
noncomputable def gExdistr (ph : Wff) (ps : Wff) (x : Var) (y : Var)
    (dv_ph_y : y ∉ ph.fv) :
    Nominal.NPrf
      (synWb (synWex x (synWex y (synWa ph ps))) (synWex x (synWa ph (synWex y ps)))) :=
  by
  let proofSupport : Finset Var :=
    ph.fv ∪ ps.fv ∪ ({ x } : Finset Var) ∪ ({ y } : Finset Var)
  have p0000 :=
    @gN1942v ph ps y
      (by
        first
        | (aesop))
  have p0001 := @gExbii (synWex y (synWa ph ps)) (synWa ph (synWex y ps)) x p0000
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_n_19_42vv`. -/
@[expose]
noncomputable def gN1942vv (ph : Wff) (ps : Wff) (x : Var) (y : Var)
    (dv_ph_x : x ∉ ph.fv) (dv_ph_y : y ∉ ph.fv) :
    Nominal.NPrf
      (synWb (synWex x (synWex y (synWa ph ps))) (synWa ph (synWex x (synWex y ps)))) :=
  by
  let proofSupport : Finset Var :=
    ph.fv ∪ ps.fv ∪ ({ x } : Finset Var) ∪ ({ y } : Finset Var)
  have p0000 :=
    @gExdistr ph ps x y
      (by
        first
        | (aesop))
  have p0001 :=
    @gN1942v ph (synWex y ps) x
      (by
        first
        | (aesop))
  have p0002 :=
    @gBitri (synWex x (synWex y (synWa ph ps))) (synWex x (synWa ph (synWex y ps)))
      (synWa ph (synWex x (synWex y ps))) p0000 p0001
  exact p0002

/-- Checked nominal proof certificate identified upstream as `g_eean`. -/
@[expose]
noncomputable def gEean (ph : Wff) (ps : Wff) (x : Var) (y : Var)
    (hyp_eean_1 : Nominal.NPrf (synWnf y ph))
    (hyp_eean_2 : Nominal.NPrf (synWnf x ps)) :
    Nominal.NPrf
      (synWb (synWex x (synWex y (synWa ph ps))) (synWa (synWex x ph) (synWex y ps))) :=
  by
  have p0000 := @gN1942 ph ps y hyp_eean_1
  have p0001 := @gExbii (synWex y (synWa ph ps)) (synWa ph (synWex y ps)) x p0000
  have p0002 := @gNfex ps x y hyp_eean_2
  have p0003 := @gN1941 ph (synWex y ps) x p0002
  have p0004 :=
    @gBitri (synWex x (synWex y (synWa ph ps))) (synWex x (synWa ph (synWex y ps)))
      (synWa (synWex x ph) (synWex y ps)) p0001 p0003
  exact p0004

/-- Checked nominal proof certificate identified upstream as `g_eeanv`. -/
@[expose]
noncomputable def gEeanv (ph : Wff) (ps : Wff) (x : Var) (y : Var) (dv_ph_y : y ∉ ph.fv)
    (dv_ps_x : x ∉ ps.fv) :
    Nominal.NPrf
      (synWb (synWex x (synWex y (synWa ph ps))) (synWa (synWex x ph) (synWex y ps))) :=
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
  have p0002 := @gEean ph ps x y p0000 p0001
  exact p0002

/-- Checked nominal proof certificate identified upstream as `g_eeeanv`. -/
@[expose]
noncomputable def gEeeanv (ph : Wff) (ps : Wff) (ch : Wff) (x : Var) (y : Var) (z : Var)
    (dv_ch_x : x ∉ ch.fv) (dv_ch_y : y ∉ ch.fv) (dv_ph_y : y ∉ ph.fv)
    (dv_ph_z : z ∉ ph.fv) (dv_ps_x : x ∉ ps.fv) (dv_ps_z : z ∉ ps.fv) (_dv_x_y : x ≠ y)
    (dv_x_z : x ≠ z) :
    Nominal.NPrf
      (synWb (synWex x (synWex y (synWex z (synW3a ph ps ch))))
        (synW3a (synWex x ph) (synWex y ps) (synWex z ch))) :=
  by
  let proofSupport : Finset Var :=
    ph.fv ∪ ps.fv ∪ ch.fv ∪ ({ x } : Finset Var) ∪ ({ y } : Finset Var) ∪
      ({ z } : Finset Var)
  have p0000 := (Nominal.biimpRefl (synW3a ph ps ch))
  have p0001 := @gN3exbii (synW3a ph ps ch) (synWa (synWa ph ps) ch) x y z p0000
  have p0002 :=
    @gEeanv (synWa ph ps) ch y z
      (by
        first
        |
          (simp (config :=
              {
                failIfUnchanged :=
                  false }) only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
              Finset.mem_union] at ⊢;
            aesop))
      (by
        first
        | (aesop))
  have p0003 :=
    @gExbii (synWex y (synWex z (synWa (synWa ph ps) ch)))
      (synWa (synWex y (synWa ph ps)) (synWex z ch)) x p0002
  have p0004 :=
    @gEeanv ph ps x y
      (by
        first
        | (aesop))
      (by
        first
        | (aesop))
  have p0005 :=
    @gAnbi1i (synWex x (synWex y (synWa ph ps)))
      (synWa (synWex x ph) (synWex y ps)) (synWex z ch) p0004
  have p0006 :=
    @gN1941v (synWex y (synWa ph ps)) (synWex z ch) x
      (by
        first
        |
          (simp (config :=
              {
                failIfUnchanged :=
                  false }) only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wex,
              Finset.mem_erase] at ⊢;
            aesop))
  have p0007 := (Nominal.biimpRefl (synW3a (synWex x ph) (synWex y ps) (synWex z ch)))
  have p0008 :=
    @gN3bitr4i (synWa (synWex x (synWex y (synWa ph ps))) (synWex z ch))
      (synWa (synWa (synWex x ph) (synWex y ps)) (synWex z ch))
      (synWex x (synWa (synWex y (synWa ph ps)) (synWex z ch)))
      (synW3a (synWex x ph) (synWex y ps) (synWex z ch)) p0005 p0006 p0007
  have p0009 :=
    @gN3bitri (synWex x (synWex y (synWex z (synW3a ph ps ch))))
      (synWex x (synWex y (synWex z (synWa (synWa ph ps) ch))))
      (synWex x (synWa (synWex y (synWa ph ps)) (synWex z ch)))
      (synW3a (synWex x ph) (synWex y ps) (synWex z ch)) p0001 p0003 p0008
  exact p0009

/-- Checked nominal proof certificate identified upstream as `g_ee4anv`. -/
@[expose]
noncomputable def gEe4anv (ph : Wff) (ps : Wff) (x : Var) (y : Var) (z : Var) (w : Var)
    (dv_ph_w : w ∉ ph.fv) (dv_ph_z : z ∉ ph.fv) (dv_ps_x : x ∉ ps.fv)
    (dv_ps_y : y ∉ ps.fv) (_dv_w_x : w ≠ x) (_dv_y_z : y ≠ z) :
    Nominal.NPrf
      (synWb (synWex x (synWex y (synWex z (synWex w (synWa ph ps)))))
        (synWa (synWex x (synWex y ph)) (synWex z (synWex w ps)))) :=
  by
  let proofSupport : Finset Var :=
    ph.fv ∪ ps.fv ∪ ({ x } : Finset Var) ∪ ({ y } : Finset Var) ∪ ({ z } : Finset Var) ∪
      ({ w } : Finset Var)
  have p0000 := @gExcom (synWex w (synWa ph ps)) y z
  have p0001 :=
    @gExbii (synWex y (synWex z (synWex w (synWa ph ps))))
      (synWex z (synWex y (synWex w (synWa ph ps)))) x p0000
  have p0002 :=
    @gEeanv ph ps y w
      (by
        first
        | (aesop))
      (by
        first
        | (aesop))
  have p0003 :=
    @gN2exbii (synWex y (synWex w (synWa ph ps)))
      (synWa (synWex y ph) (synWex w ps)) x z p0002
  have p0004 :=
    @gEeanv (synWex y ph) (synWex w ps) x z
      (by
        first
        |
          (simp (config :=
              {
                failIfUnchanged :=
                  false }) only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wex,
              Finset.mem_erase] at ⊢;
            aesop))
      (by
        first
        |
          (simp (config :=
              {
                failIfUnchanged :=
                  false }) only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wex,
              Finset.mem_erase] at ⊢;
            aesop))
  have p0005 :=
    @gN3bitri (synWex x (synWex y (synWex z (synWex w (synWa ph ps)))))
      (synWex x (synWex z (synWex y (synWex w (synWa ph ps)))))
      (synWex x (synWex z (synWa (synWex y ph) (synWex w ps))))
      (synWa (synWex x (synWex y ph)) (synWex z (synWex w ps))) p0001 p0003 p0004
  exact p0005

/-- Checked nominal proof certificate identified upstream as `g_nexdv`. -/
@[expose]
noncomputable def gNexdv (ph : Wff) (ps : Wff) (x : Var) (dv_ph_x : x ∉ ph.fv)
    (hyp_nexdv_1 : Nominal.NPrf (.imp ph (.neg ps))) :
    Nominal.NPrf (.imp ph (.neg (synWex x ps))) :=
  by
  let proofSupport : Finset Var := ph.fv ∪ ps.fv ∪ ({ x } : Finset Var)
  have p0000 :=
    @gNfv ph x
      (by
        first
        | (aesop))
  have p0001 := @gNexd ph ps x p0000 hyp_nexdv_1
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_stdpc7`. -/
@[expose]
noncomputable def gStdpc7 (ph : Wff) (x : Var) (y : Var) :
    Nominal.NPrf (.imp (.objEq x y) (.imp (synWsb x y ph) ph)) :=
  by
  have p0000 := @gSbequ2 ph y x
  have p0001 := @gEqucoms (.imp (synWsb x y ph) ph) y x p0000
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_sbequ1`. -/
@[expose]
noncomputable def gSbequ1 (ph : Wff) (x : Var) (y : Var) :
    Nominal.NPrf (.imp (.objEq x y) (.imp ph (synWsb y x ph))) :=
  by
  have p0000 := @gPm34 (.objEq x y) ph
  have p0001 := @gN198a (synWa (.objEq x y) ph) x
  have p0002 := (Nominal.biimpRefl (synWsb y x ph))
  have p0003 :=
    @gSylanbrc (synWa (.objEq x y) ph) (.imp (.objEq x y) ph)
      (synWex x (synWa (.objEq x y) ph)) (synWsb y x ph) p0000 p0001 p0002
  have p0004 := @gEx (.objEq x y) ph (synWsb y x ph) p0003
  exact p0004

/-- Checked nominal proof certificate identified upstream as `g_sbequ12`. -/
@[expose]
noncomputable def gSbequ12 (ph : Wff) (x : Var) (y : Var) :
    Nominal.NPrf (.imp (.objEq x y) (synWb ph (synWsb y x ph))) :=
  by
  have p0000 := @gSbequ1 ph x y
  have p0001 := @gSbequ2 ph x y
  have p0002 := @gImpbid (.objEq x y) ph (synWsb y x ph) p0000 p0001
  exact p0002

/-- Checked nominal proof certificate identified upstream as `g_sbequ12r`. -/
@[expose]
noncomputable def gSbequ12r (ph : Wff) (x : Var) (y : Var) :
    Nominal.NPrf (.imp (.objEq x y) (synWb (synWsb x y ph) ph)) :=
  by
  have p0000 := @gSbequ12 ph y x
  have p0001 := @gBicomd (.objEq y x) ph (synWsb x y ph) p0000
  have p0002 := @gEqucoms (synWb (synWsb x y ph) ph) y x p0001
  exact p0002

/-- Checked nominal proof certificate identified upstream as `g_sbid`. -/
@[expose]
noncomputable def gSbid (ph : Wff) (x : Var) :
    Nominal.NPrf (synWb (synWsb x x ph) ph) :=
  by
  have p0000 := @gEquid x
  have p0001 := @gSbequ12 ph x x
  have p0002 := Nominal.mp p0000 p0001
  have p0003 := @gBicomi ph (synWsb x x ph) p0002
  exact p0003

/-- Checked nominal proof certificate identified upstream as `g_sb4a`. -/
@[expose]
noncomputable def gSb4a (ph : Wff) (x : Var) (y : Var) :
    Nominal.NPrf (.imp (synWsb y x (.all y ph)) (.all x (.imp (.objEq x y) ph))) :=
  by
  have p0000 := @gSb1 (.all y ph) x y
  have p0001 := @gEqus5a ph x y
  have p0002 :=
    @gSyl (synWsb y x (.all y ph)) (synWex x (synWa (.objEq x y) (.all y ph)))
      (.all x (.imp (.objEq x y) ph)) p0000 p0001
  exact p0002

/-- Checked nominal proof certificate identified upstream as `g_ax12v`. -/
@[expose]
noncomputable def gAx12v (x : Var) (y : Var) (z : Var) (_dv_x_z : x ≠ z)
    (_dv_y_z : y ≠ z) :
    Nominal.NPrf (.imp (.neg (.objEq x y)) (.imp (.objEq y z) (.all x (.objEq y z)))) :=
  by
  have p0000 := Nominal.ax12 x y z
  exact p0000

/-- Checked nominal proof certificate identified upstream as `g_ax12olem1`. -/
@[expose]
noncomputable def gAx12olem1 (y : Var) (z : Var) (w : Var) (dv_w_y : w ≠ y)
    (dv_w_z : w ≠ z) :
    Nominal.NPrf
      (synWb (synWex w (synWa (.objEq y w) (.neg (.objEq z w)))) (.neg (.objEq y z))) :=
  by
  let proofSupport : Finset Var :=
    ({ y } : Finset Var) ∪ ({ z } : Finset Var) ∪ ({ w } : Finset Var)
  have p0000 := Nominal.ax8 y w z
  have p0001 := @gEqucomi w z
  have p0002 := @gSyl6 (.objEq y w) (.objEq y z) (.objEq w z) (.objEq z w) p0000 p0001
  have p0003 := @gCon3and (.objEq y w) (.objEq y z) (.objEq z w) p0002
  have p0004 :=
    @gExlimiv (synWa (.objEq y w) (.neg (.objEq z w))) (.neg (.objEq y z)) w
      (by
        first
        |
          (simp (config :=
              { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_wff_neg,
              NFChoice.Compiler.CoreFVSimp.fv_wff_objEq] at ⊢;
            aesop))
      p0003
  have p0005 :=
    Nominal.ax17 (.neg (.objEq y z)) w
      (by
        first
        |
          (simp (config :=
              { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_wff_neg,
              NFChoice.Compiler.CoreFVSimp.fv_wff_objEq] at ⊢;
            aesop))
  have p0006 := Nominal.ax8 w z y
  have p0007 := @gEqucomi z y
  have p0008 := @gSyl6 (.objEq w z) (.objEq w y) (.objEq z y) (.objEq y z) p0006 p0007
  have p0009 := @gEqucoms (.imp (.objEq w y) (.objEq y z)) w z p0008
  have p0010 := @gCom12 (.objEq z w) (.objEq w y) (.objEq y z) p0009
  have p0011 := @gCon3d (.objEq w y) (.objEq z w) (.objEq y z) p0010
  have p0012 := @gEqucomi w y
  have p0013 :=
    @gJctild (.objEq w y) (.neg (.objEq y z)) (.neg (.objEq z w)) (.objEq y w) p0011
      p0012
  have p0014 :=
    @gSpimeh (.neg (.objEq y z)) (synWa (.objEq y w) (.neg (.objEq z w))) w y
      (by
        first
        | (aesop))
      p0005 p0013
  have p0015 :=
    @gImpbii (synWex w (synWa (.objEq y w) (.neg (.objEq z w)))) (.neg (.objEq y z))
      p0004 p0014
  exact p0015

/-- Checked nominal proof certificate identified upstream as `g_ax12olem2`. -/
@[expose]
noncomputable def gAx12olem2 (x : Var) (y : Var) (z : Var) (w : Var) (dv_w_x : w ≠ x)
    (dv_w_y : w ≠ y) (dv_w_z : w ≠ z) (dv_x_z : x ≠ z)
    (hyp_ax12olem2_1 :
      Nominal.NPrf (.imp (.neg (.objEq x y)) (.imp (.objEq y w) (.all x (.objEq y w))))) :
    Nominal.NPrf
      (.imp (.neg (.objEq x y)) (.imp (.neg (.objEq y z)) (.all x (.neg (.objEq y z))))) :=
  by
  let proofSupport : Finset Var :=
    ({ x } : Finset Var) ∪ ({ y } : Finset Var) ∪ ({ z } : Finset Var) ∪
      ({ w } : Finset Var)
  have p0000 :=
    @gAnim1d (.neg (.objEq x y)) (.objEq y w) (.all x (.objEq y w)) (.neg (.objEq z w))
      hyp_ax12olem2_1
  have p0001 :=
    Nominal.ax17 (.neg (.objEq z w)) x
      (by
        first
        |
          (simp (config :=
              { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_wff_neg,
              NFChoice.Compiler.CoreFVSimp.fv_wff_objEq] at ⊢;
            aesop))
  have p0002 :=
    @gAnim2i (.neg (.objEq z w)) (.all x (.neg (.objEq z w))) (.all x (.objEq y w)) p0001
  have p0003 := @gN1926 (.objEq y w) (.neg (.objEq z w)) x
  have p0004 :=
    @gSylibr (synWa (.all x (.objEq y w)) (.neg (.objEq z w)))
      (synWa (.all x (.objEq y w)) (.all x (.neg (.objEq z w))))
      (.all x (synWa (.objEq y w) (.neg (.objEq z w)))) p0002 p0003
  have p0005 :=
    @gSyl6 (.neg (.objEq x y)) (synWa (.objEq y w) (.neg (.objEq z w)))
      (synWa (.all x (.objEq y w)) (.neg (.objEq z w)))
      (.all x (synWa (.objEq y w) (.neg (.objEq z w)))) p0000 p0004
  have p0006 :=
    @gEximdv (.neg (.objEq x y)) (synWa (.objEq y w) (.neg (.objEq z w)))
      (.all x (synWa (.objEq y w) (.neg (.objEq z w)))) w
      (by
        first
        |
          (simp (config :=
              { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_wff_neg,
              NFChoice.Compiler.CoreFVSimp.fv_wff_objEq] at ⊢;
            aesop))
      p0005
  have p0007 := @gN1912 (synWa (.objEq y w) (.neg (.objEq z w))) w x
  have p0008 :=
    @gSyl6 (.neg (.objEq x y)) (synWex w (synWa (.objEq y w) (.neg (.objEq z w))))
      (synWex w (.all x (synWa (.objEq y w) (.neg (.objEq z w)))))
      (.all x (synWex w (synWa (.objEq y w) (.neg (.objEq z w))))) p0006 p0007
  have p0009 :=
    @gAx12olem1 y z w
      (by
        first
        | (aesop))
      (by
        first
        | (aesop))
  have p0010 :=
    @gAlbii (synWex w (synWa (.objEq y w) (.neg (.objEq z w)))) (.neg (.objEq y z)) x
      p0009
  have p0011 :=
    @gN3imtr3g (.neg (.objEq x y)) (synWex w (synWa (.objEq y w) (.neg (.objEq z w))))
      (.all x (synWex w (synWa (.objEq y w) (.neg (.objEq z w))))) (.neg (.objEq y z))
      (.all x (.neg (.objEq y z))) p0008 p0009 p0010
  exact p0011

/-- Checked nominal proof certificate identified upstream as `g_ax12olem3`. -/
@[expose]
noncomputable def gAx12olem3 (x : Var) (y : Var) (z : Var) :
    Nominal.NPrf
      (synWb (.imp (.neg (.objEq x y))
          (.imp (.neg (.all x (.neg (.objEq y z)))) (.all x (.objEq y z))))
        (synWa (.imp (.neg (.objEq x y)) (.imp (.objEq y z) (.all x (.objEq y z))))
          (.imp (.neg (.objEq x y))
            (.imp (.neg (.objEq y z)) (.all x (.neg (.objEq y z))))))) :=
  by
  have p0000 := @gSp (.neg (.objEq y z)) x
  have p0001 := @gCon2i (.all x (.neg (.objEq y z))) (.objEq y z) p0000
  have p0002 :=
    @gImim1i (.objEq y z) (.neg (.all x (.neg (.objEq y z)))) (.all x (.objEq y z)) p0001
  have p0003 :=
    @gImim2i (.imp (.neg (.all x (.neg (.objEq y z)))) (.all x (.objEq y z)))
      (.imp (.objEq y z) (.all x (.objEq y z))) (.neg (.objEq x y)) p0002
  have p0004 := @gSp (.objEq y z) x
  have p0005 :=
    @gImim2i (.all x (.objEq y z)) (.objEq y z) (.neg (.all x (.neg (.objEq y z)))) p0004
  have p0006 :=
    @gCon1d (.imp (.neg (.all x (.neg (.objEq y z)))) (.all x (.objEq y z)))
      (.all x (.neg (.objEq y z))) (.objEq y z) p0005
  have p0007 :=
    @gImim2i (.imp (.neg (.all x (.neg (.objEq y z)))) (.all x (.objEq y z)))
      (.imp (.neg (.objEq y z)) (.all x (.neg (.objEq y z)))) (.neg (.objEq x y)) p0006
  have p0008 :=
    @gJca
      (.imp (.neg (.objEq x y))
        (.imp (.neg (.all x (.neg (.objEq y z)))) (.all x (.objEq y z))))
      (.imp (.neg (.objEq x y)) (.imp (.objEq y z) (.all x (.objEq y z))))
      (.imp (.neg (.objEq x y)) (.imp (.neg (.objEq y z)) (.all x (.neg (.objEq y z)))))
      p0003 p0007
  have p0009 := @gCon1 (.objEq y z) (.all x (.neg (.objEq y z)))
  have p0010 :=
    @gImim1d (.imp (.neg (.objEq y z)) (.all x (.neg (.objEq y z))))
      (.neg (.all x (.neg (.objEq y z)))) (.objEq y z) (.all x (.objEq y z)) p0009
  have p0011 :=
    @gCom12 (.imp (.neg (.objEq y z)) (.all x (.neg (.objEq y z))))
      (.imp (.objEq y z) (.all x (.objEq y z)))
      (.imp (.neg (.all x (.neg (.objEq y z)))) (.all x (.objEq y z))) p0010
  have p0012 :=
    @gImim3i (.imp (.objEq y z) (.all x (.objEq y z)))
      (.imp (.neg (.objEq y z)) (.all x (.neg (.objEq y z))))
      (.imp (.neg (.all x (.neg (.objEq y z)))) (.all x (.objEq y z))) (.neg (.objEq x y))
      p0011
  have p0013 :=
    @gImp (.imp (.neg (.objEq x y)) (.imp (.objEq y z) (.all x (.objEq y z))))
      (.imp (.neg (.objEq x y)) (.imp (.neg (.objEq y z)) (.all x (.neg (.objEq y z)))))
      (.imp (.neg (.objEq x y))
        (.imp (.neg (.all x (.neg (.objEq y z)))) (.all x (.objEq y z))))
      p0012
  have p0014 :=
    @gImpbii
      (.imp (.neg (.objEq x y))
        (.imp (.neg (.all x (.neg (.objEq y z)))) (.all x (.objEq y z))))
      (synWa (.imp (.neg (.objEq x y)) (.imp (.objEq y z) (.all x (.objEq y z))))
        (.imp (.neg (.objEq x y)) (.imp (.neg (.objEq y z)) (.all x (.neg (.objEq y z))))))
      p0008 p0013
  exact p0014

/-- Checked nominal proof certificate identified upstream as `g_ax12olem4`. -/
@[expose]
noncomputable def gAx12olem4 (x : Var) (y : Var) (z : Var) (w : Var) (dv_w_x : w ≠ x)
    (dv_w_y : w ≠ y) (dv_w_z : w ≠ z) (dv_x_z : x ≠ z) (_dv_y_z : y ≠ z)
    (hyp_ax12olem4_1 :
      Nominal.NPrf (.imp (.neg (.objEq x y)) (.imp (.objEq y z) (.all x (.objEq y z)))))
    (hyp_ax12olem4_2 :
      Nominal.NPrf (.imp (.neg (.objEq x y)) (.imp (.objEq y w) (.all x (.objEq y w))))) :
    Nominal.NPrf
      (.imp (.neg (.objEq x y))
        (.imp (.neg (.all x (.neg (.objEq y z)))) (.all x (.objEq y z)))) :=
  by
  let proofSupport : Finset Var :=
    ({ x } : Finset Var) ∪ ({ y } : Finset Var) ∪ ({ z } : Finset Var) ∪
      ({ w } : Finset Var)
  have p0000 :=
    @gAx12olem2 x y z w
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
      hyp_ax12olem4_2
  have p0001 := @gAx12olem3 x y z
  have p0002 :=
    @gMpbir2an
      (.imp (.neg (.objEq x y))
        (.imp (.neg (.all x (.neg (.objEq y z)))) (.all x (.objEq y z))))
      (.imp (.neg (.objEq x y)) (.imp (.objEq y z) (.all x (.objEq y z))))
      (.imp (.neg (.objEq x y)) (.imp (.neg (.objEq y z)) (.all x (.neg (.objEq y z)))))
      hyp_ax12olem4_1 p0000 p0001
  exact p0002

/-- Checked nominal proof certificate identified upstream as `g_ax12olem5`. -/
@[expose]
noncomputable def gAx12olem5 (x : Var) (y : Var) (z : Var)
    (hyp_ax12olem5_1 : Nominal.NPrf (.imp (.neg (.objEq x y))
          (.imp (.neg (.all x (.neg (.objEq y z)))) (.all x (.objEq y z))))) :
    Nominal.NPrf
      (.imp (.neg (.all x (.objEq x y))) (.imp (.objEq y z) (.all x (.objEq y z)))) :=
  by
  have p0000 := @gExnal (.objEq x y) x
  have p0001 := @gN198a (.objEq y z) x
  have p0002 := @gHbe1 (.objEq y z) x
  have p0003 := @gHba1 (.objEq y z) x
  have p0004 := @gHbim (synWex x (.objEq y z)) (.all x (.objEq y z)) x p0002 p0003
  have p0005 := (Nominal.biimpRefl (synWex x (.objEq y z)))
  have p0006 :=
    @gSyl5bi (synWex x (.objEq y z)) (.neg (.all x (.neg (.objEq y z))))
      (.neg (.objEq x y)) (.all x (.objEq y z)) p0005 hyp_ax12olem5_1
  have p0007 :=
    @gExlimih (.neg (.objEq x y)) (.imp (synWex x (.objEq y z)) (.all x (.objEq y z))) x
      p0004 p0006
  have p0008 :=
    @gSyl5 (.objEq y z) (synWex x (.objEq y z)) (synWex x (.neg (.objEq x y)))
      (.all x (.objEq y z)) p0001 p0007
  have p0009 :=
    @gSylbir (.neg (.all x (.objEq x y))) (synWex x (.neg (.objEq x y)))
      (.imp (.objEq y z) (.all x (.objEq y z))) p0000 p0008
  exact p0009

/-- Checked nominal proof certificate identified upstream as `g_ax12olem6`. -/
@[expose]
noncomputable def gAx12olem6 (x : Var) (y : Var) (z : Var) (w : Var) (dv_w_x : w ≠ x)
    (dv_w_y : w ≠ y) (dv_w_z : w ≠ z)
    (hyp_ax12olem6_1 : Nominal.NPrf
        (.imp (.neg (.all x (.objEq x z))) (.imp (.objEq z w) (.all x (.objEq z w)))))
    (hyp_ax12olem6_2 : Nominal.NPrf
        (.imp (.neg (.all x (.objEq x y))) (.imp (.objEq y w) (.all x (.objEq y w))))) :
    Nominal.NPrf
      (.imp (.neg (.all x (.objEq x y)))
        (.imp (.neg (.all x (.objEq x z))) (.imp (.objEq y z) (.all x (.objEq y z))))) :=
  by
  let proofSupport : Finset Var :=
    ({ x } : Finset Var) ∪ ({ y } : Finset Var) ∪ ({ z } : Finset Var) ∪
      ({ w } : Finset Var)
  have p0000 := @gHbn1 (.objEq x z) x
  have p0001 := @gHbim1 (.neg (.all x (.objEq x z))) (.objEq z w) x p0000 hyp_ax12olem6_1
  have p0002 :=
    Nominal.ax17 (.imp (.neg (.all x (.objEq x z))) (.objEq y z)) w
      (by
        first
        |
          (simp (config :=
              { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp,
              NFChoice.Compiler.CoreFVSimp.fv_wff_neg,
              NFChoice.Compiler.CoreFVSimp.fv_wff_all,
              NFChoice.Compiler.CoreFVSimp.fv_wff_objEq, Finset.mem_union,
              Finset.mem_erase] at ⊢;
            aesop))
  have p0003 := @gEqucom z w
  have p0004 := @gEquequ1 w y z
  have p0005 := @gSyl5bb (.objEq z w) (.objEq w z) (.objEq w y) (.objEq y z) p0003 p0004
  have p0006 :=
    @gImbi2d (.objEq w y) (.objEq z w) (.objEq y z) (.neg (.all x (.objEq x z))) p0005
  have p0007 :=
    @gDvelimhw (.imp (.neg (.all x (.objEq x z))) (.objEq z w))
      (.imp (.neg (.all x (.objEq x z))) (.objEq y z)) x y w
      (by
        first
        | (aesop))
      (by
        first
        | (aesop))
      p0001 p0002 p0006 hyp_ax12olem6_2
  have p0008 := @gN1921h (.neg (.all x (.objEq x z))) (.objEq y z) x p0000
  have p0009 :=
    @gSyl6ib (.neg (.all x (.objEq x y)))
      (.imp (.neg (.all x (.objEq x z))) (.objEq y z))
      (.all x (.imp (.neg (.all x (.objEq x z))) (.objEq y z)))
      (.imp (.neg (.all x (.objEq x z))) (.all x (.objEq y z))) p0007 p0008
  have p0010 :=
    @gPm286d (.neg (.all x (.objEq x y))) (.neg (.all x (.objEq x z))) (.objEq y z)
      (.all x (.objEq y z)) p0009
  exact p0010

/-- Checked nominal proof certificate identified upstream as `g_ax12olem7`. -/
@[expose]
noncomputable def gAx12olem7 (x : Var) (y : Var) (z : Var) (w : Var) (dv_w_x : w ≠ x)
    (dv_w_y : w ≠ y) (dv_w_z : w ≠ z)
    (hyp_ax12olem7_1 : Nominal.NPrf (.imp (.neg (.objEq x z))
          (.imp (.neg (.all x (.neg (.objEq z w)))) (.all x (.objEq z w)))))
    (hyp_ax12olem7_2 : Nominal.NPrf (.imp (.neg (.objEq x y))
          (.imp (.neg (.all x (.neg (.objEq y w)))) (.all x (.objEq y w))))) :
    Nominal.NPrf
      (.imp (.neg (.all x (.objEq x y)))
        (.imp (.neg (.all x (.objEq x z))) (.imp (.objEq y z) (.all x (.objEq y z))))) :=
  by
  let proofSupport : Finset Var :=
    ({ x } : Finset Var) ∪ ({ y } : Finset Var) ∪ ({ z } : Finset Var) ∪
      ({ w } : Finset Var)
  have p0000 := @gAx12olem5 x z w hyp_ax12olem7_1
  have p0001 := @gAx12olem5 x y w hyp_ax12olem7_2
  have p0002 :=
    @gAx12olem6 x y z w
      (by
        first
        | (aesop))
      (by
        first
        | (aesop))
      (by
        first
        | (aesop))
      p0000 p0001
  exact p0002

/-- Checked nominal proof certificate identified upstream as `g_ax12o`. -/
@[expose]
noncomputable def gAx12o (x : Var) (y : Var) (z : Var) :
    Nominal.NPrf
      (.imp (.neg (.all z (.objEq z x)))
        (.imp (.neg (.all z (.objEq z y))) (.imp (.objEq x y) (.all z (.objEq x y))))) :=
  by
  let proofSupport : Finset Var :=
    ({ x } : Finset Var) ∪ ({ y } : Finset Var) ∪ ({ z } : Finset Var)
  let w : Var := freshVar proofSupport 0
  let v : Var := freshVar proofSupport 1
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
  have fresh_v : v ∉ proofSupport :=
    by
    change freshVar proofSupport 1 ∉ proofSupport
    exact freshVar_not_mem proofSupport 1
  have fresh_v_ne_x : v ≠ x := by
    intro h
    exact
      fresh_v
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_singleton.mpr h)))
  have fresh_x_ne_v : x ≠ v := Ne.symm fresh_v_ne_x
  have fresh_v_ne_y : v ≠ y := by
    intro h
    exact
      fresh_v
        (Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_singleton.mpr h)))
  have fresh_y_ne_v : y ≠ v := Ne.symm fresh_v_ne_y
  have fresh_v_ne_z : v ≠ z := by
    intro h
    exact fresh_v (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))
  have fresh_z_ne_v : z ≠ v := Ne.symm fresh_v_ne_z
  have fresh_w_ne_v : w ≠ v :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have fresh_v_ne_w : v ≠ w := Ne.symm fresh_w_ne_v
  have p0000 :=
    @gAx12v z y w
      (by
        first
        | (aesop))
      (by
        first
        | (aesop))
  have p0001 :=
    @gAx12v z y v
      (by
        first
        | (aesop))
      (by
        first
        | (aesop))
  have p0002 :=
    @gAx12olem4 z y w v
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
      (by
        first
        | (aesop))
      p0000 p0001
  have p0003 :=
    @gAx12v z x w
      (by
        first
        | (aesop))
      (by
        first
        | (aesop))
  have p0004 :=
    @gAx12v z x v
      (by
        first
        | (aesop))
      (by
        first
        | (aesop))
  have p0005 :=
    @gAx12olem4 z x w v
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
      (by
        first
        | (aesop))
      p0003 p0004
  have p0006 :=
    @gAx12olem7 z x y w
      (by
        first
        | (aesop))
      (by
        first
        | (aesop))
      (by
        first
        | (aesop))
      p0002 p0005
  exact p0006

/-- Checked nominal proof certificate identified upstream as `g_ax10lem1`. -/
@[expose]
noncomputable def gAx10lem1 (x : Var) (y : Var) (w : Var) (dv_w_x : w ≠ x)
    (dv_w_y : w ≠ y) : Nominal.NPrf (.imp (.all x (.objEq x w)) (.all y (.objEq y w))) :=
  by
  let proofSupport : Finset Var :=
    ({ x } : Finset Var) ∪ ({ y } : Finset Var) ∪ ({ w } : Finset Var)
  let v : Var := freshVar proofSupport 0
  have fresh_v : v ∉ proofSupport :=
    by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_v_ne_x : v ≠ x := by
    intro h
    exact
      fresh_v
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_singleton.mpr h)))
  have fresh_x_ne_v : x ≠ v := Ne.symm fresh_v_ne_x
  have fresh_v_ne_y : v ≠ y := by
    intro h
    exact
      fresh_v
        (Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_singleton.mpr h)))
  have fresh_y_ne_v : y ≠ v := Ne.symm fresh_v_ne_y
  have fresh_v_ne_w : v ≠ w := by
    intro h
    exact fresh_v (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))
  have fresh_w_ne_v : w ≠ v := Ne.symm fresh_v_ne_w
  have p0000 := Nominal.ax8 x v w
  have p0001 :=
    @gCbvalivw (.objEq x w) (.objEq v w) x v
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
      p0000
  have p0002 := Nominal.ax8 v y w
  have p0003 :=
    @gCbvalivw (.objEq v w) (.objEq y w) v y
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
      p0002
  have p0004 :=
    @gSyl (.all x (.objEq x w)) (.all v (.objEq v w)) (.all y (.objEq y w)) p0001 p0003
  exact p0004

/-- Checked nominal proof certificate identified upstream as `g_ax10lem2`. -/
@[expose]
noncomputable def gAx10lem2 (x : Var) (y : Var) (z : Var) (dv_x_y : x ≠ y)
    (dv_x_z : x ≠ z) : Nominal.NPrf (.imp (.all x (.objEq x y)) (.all x (.objEq x z))) :=
  by
  let proofSupport : Finset Var :=
    ({ x } : Finset Var) ∪ ({ y } : Finset Var) ∪ ({ z } : Finset Var)
  have p0000 := @gHbe1 (.neg (.objEq x y)) x
  have p0001 := @gEquequ2 z y x
  have p0002 := @gBiimprd (.objEq z y) (.objEq x z) (.objEq x y) p0001
  have p0003 := @gCon3rr3 (.objEq z y) (.objEq x y) (.objEq x z) p0002
  have p0004 := @gN198a (.neg (.objEq x y)) x
  have p0005 :=
    @gSyl6 (.neg (.objEq x z)) (.objEq z y) (.neg (.objEq x y))
      (synWex x (.neg (.objEq x y))) p0003 p0004
  have p0006 :=
    Nominal.ax17 (.neg (.objEq z y)) x
      (by
        first
        |
          (simp (config :=
              { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_wff_neg,
              NFChoice.Compiler.CoreFVSimp.fv_wff_objEq] at ⊢;
            aesop))
  have p0007 := @gEquequ1 x z y
  have p0008 := @gNotbid (.objEq x z) (.objEq x y) (.objEq z y) p0007
  have p0009 := @gBiimprd (.objEq x z) (.neg (.objEq x y)) (.neg (.objEq z y)) p0008
  have p0010 :=
    @gSpimeh (.neg (.objEq z y)) (.neg (.objEq x y)) x z
      (by
        first
        | (aesop))
      p0006 p0009
  have p0011 :=
    @gPm261d1 (.neg (.objEq x z)) (.objEq z y) (synWex x (.neg (.objEq x y))) p0005
      p0010
  have p0012 :=
    @gExlimih (.neg (.objEq x z)) (synWex x (.neg (.objEq x y))) x p0000 p0011
  have p0013 := @gExnal (.objEq x z) x
  have p0014 := @gExnal (.objEq x y) x
  have p0015 :=
    @gN3imtr3i (synWex x (.neg (.objEq x z))) (synWex x (.neg (.objEq x y)))
      (.neg (.all x (.objEq x z))) (.neg (.all x (.objEq x y))) p0012 p0013 p0014
  have p0016 := @gCon4i (.all x (.objEq x z)) (.all x (.objEq x y)) p0015
  exact p0016

/-- Checked nominal proof certificate identified upstream as `g_ax10lem3`. -/
@[expose]
noncomputable def gAx10lem3 (x : Var) (y : Var) (dv_x_y : x ≠ y) :
    Nominal.NPrf (.imp (.all x (.objEq x y)) (.all y (.objEq y x))) :=
  by
  let proofSupport : Finset Var := ({ x } : Finset Var) ∪ ({ y } : Finset Var)
  let z : Var := freshVar proofSupport 0
  let w : Var := freshVar proofSupport 1
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
  have fresh_w : w ∉ proofSupport :=
    by
    change freshVar proofSupport 1 ∉ proofSupport
    exact freshVar_not_mem proofSupport 1
  have fresh_w_ne_x : w ≠ x := by
    intro h
    exact fresh_w (Finset.mem_union_left _ (Finset.mem_singleton.mpr h))
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
    @gAx10lem2 x y z
      (by
        first
        | (aesop))
      (by
        first
        | (aesop))
  have p0001 :=
    @gAx10lem1 x w z
      (by
        first
        | (aesop))
      (by
        first
        | (aesop))
  have p0002 :=
    @gAx10lem2 w z x
      (by
        first
        | (aesop))
      (by
        first
        | (aesop))
  have p0003 :=
    @gSyl (.all x (.objEq x z)) (.all w (.objEq w z)) (.all w (.objEq w x)) p0001 p0002
  have p0004 :=
    @gAx10lem1 w y x
      (by
        first
        | (aesop))
      (by
        first
        | (aesop))
  have p0005 :=
    @gSyl (.all x (.objEq x z)) (.all w (.objEq w x)) (.all y (.objEq y x)) p0003 p0004
  have p0006 :=
    @gSyl (.all x (.objEq x y)) (.all x (.objEq x z)) (.all y (.objEq y x)) p0000 p0005
  exact p0006

/-- Checked nominal proof certificate identified upstream as `g_dvelimv`. -/
@[expose]
noncomputable def gDvelimv (ph : Wff) (ps : Wff) (x : Var) (y : Var) (z : Var)
    (dv_ph_x : x ∉ ph.fv) (dv_ps_z : z ∉ ps.fv) (dv_x_z : x ≠ z) (dv_y_z : y ≠ z)
    (hyp_dvelimv_1 : Nominal.NPrf (.imp (.objEq z y) (synWb ph ps))) :
    Nominal.NPrf (.imp (.neg (.all x (.objEq x y))) (.imp ps (.all x ps))) :=
  by
  let proofSupport : Finset Var :=
    ph.fv ∪ ps.fv ∪ ({ x } : Finset Var) ∪ ({ y } : Finset Var) ∪ ({ z } : Finset Var)
  have p0000 :=
    Nominal.ax17 ps z
      (by
        first
        | (aesop))
  have p0001 := @gA1d ps (.all z ps) (.objEq z y) p0000
  have p0002 := @gAlrimih ps (.imp (.objEq z y) (.all z ps)) z p0000 p0001
  have p0003 := @gSp ps z
  have p0004 := @gSyl5ibr (.all z ps) ph (.objEq z y) ps p0003 hyp_dvelimv_1
  have p0005 := @gA2i (.objEq z y) (.all z ps) ph p0004
  have p0006 := @gAlimi (.imp (.objEq z y) (.all z ps)) (.imp (.objEq z y) ph) z p0005
  have p0007 :=
    @gSyl ps (.all z (.imp (.objEq z y) (.all z ps))) (.all z (.imp (.objEq z y) ph))
      p0002 p0006
  have p0008 :=
    @gAx10lem3 z x
      (by
        first
        | (aesop))
  have p0009 := @gCon3i (.all z (.objEq z x)) (.all x (.objEq x z)) p0008
  have p0010 := @gHbn1 (.objEq z x) z
  have p0011 :=
    @gAx10lem3 x z
      (by
        first
        | (aesop))
  have p0012 := @gCon3i (.all x (.objEq x z)) (.all z (.objEq z x)) p0011
  have p0013 :=
    @gAlrimih (.neg (.all z (.objEq z x))) (.neg (.all x (.objEq x z))) z p0010 p0012
  have p0014 :=
    @gSyl (.neg (.all x (.objEq x z))) (.neg (.all z (.objEq z x)))
      (.all z (.neg (.all x (.objEq x z)))) p0009 p0013
  have p0015 :=
    Nominal.ax17 (.neg (.all x (.objEq x y))) z
      (by
        first
        |
          (simp (config :=
              { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_wff_neg,
              NFChoice.Compiler.CoreFVSimp.fv_wff_all,
              NFChoice.Compiler.CoreFVSimp.fv_wff_objEq, Finset.mem_erase] at ⊢;
            aesop))
  have p0016 :=
    @gHban (.neg (.all x (.objEq x z))) (.neg (.all x (.objEq x y))) z p0014 p0015
  have p0017 := @gHbn1 (.objEq x z) x
  have p0018 := @gHbn1 (.objEq x y) x
  have p0019 :=
    @gHban (.neg (.all x (.objEq x z))) (.neg (.all x (.objEq x y))) x p0017 p0018
  have p0020 := @gAx12o z y x
  have p0021 :=
    @gImp (.neg (.all x (.objEq x z))) (.neg (.all x (.objEq x y)))
      (.imp (.objEq z y) (.all x (.objEq z y))) p0020
  have p0022 :=
    @gA17d (synWa (.neg (.all x (.objEq x z))) (.neg (.all x (.objEq x y)))) ph x
      (by
        first
        | (aesop))
  have p0023 :=
    @gHbimd (synWa (.neg (.all x (.objEq x z))) (.neg (.all x (.objEq x y))))
      (.objEq z y) ph x p0019 p0021 p0022
  have p0024 :=
    @gHbald (synWa (.neg (.all x (.objEq x z))) (.neg (.all x (.objEq x y))))
      (.imp (.objEq z y) ph) x z p0016 p0023
  have p0025 := @gBiimpd (.objEq z y) ph ps hyp_dvelimv_1
  have p0026 := @gA2i (.objEq z y) ph ps p0025
  have p0027 := @gAlimi (.imp (.objEq z y) ph) (.imp (.objEq z y) ps) z p0026
  have p0028 :=
    @gAx9v z y
      (by
        first
        | (aesop))
  have p0029 := @gCon3 (.objEq z y) ps
  have p0030 := @gAl2imi (.imp (.objEq z y) ps) (.neg ps) (.neg (.objEq z y)) z p0029
  have p0031 :=
    @gMtoi (.all z (.imp (.objEq z y) ps)) (.all z (.neg ps))
      (.all z (.neg (.objEq z y))) p0028 p0030
  have p0032 :=
    @gSyl (.all z (.imp (.objEq z y) ph)) (.all z (.imp (.objEq z y) ps))
      (.neg (.all z (.neg ps))) p0027 p0031
  have p0033 :=
    Nominal.ax17 (.neg ps) z
      (by
        first
        |
          (simp (config :=
              {
                failIfUnchanged :=
                  false }) only [NFChoice.Compiler.CoreFVSimp.fv_wff_neg] at ⊢;
            aesop))
  have p0034 := @gNsyl2 (.all z (.imp (.objEq z y) ph)) (.all z (.neg ps)) ps p0032 p0033
  have p0035 := @gAlimi (.all z (.imp (.objEq z y) ph)) ps x p0034
  have p0036 :=
    @gSyl56 ps (.all z (.imp (.objEq z y) ph))
      (synWa (.neg (.all x (.objEq x z))) (.neg (.all x (.objEq x y))))
      (.all x (.all z (.imp (.objEq z y) ph))) (.all x ps) p0007 p0024 p0035
  have p0037 :=
    @gExpcom (.neg (.all x (.objEq x z))) (.neg (.all x (.objEq x y)))
      (.imp ps (.all x ps)) p0036
  have p0038 := @gSp (.objEq x z) x
  have p0039 := Nominal.ax11Structural x z ps
  have p0040 :=
    @gSyl2im (.all x (.objEq x z)) (.objEq x z) ps (.all z ps)
      (.all x (.imp (.objEq x z) ps)) p0038 p0000 p0039
  have p0041 := @gPm227 (.objEq x z) ps
  have p0042 := @gAl2imi (.objEq x z) (.imp (.objEq x z) ps) ps x p0041
  have p0043 :=
    @gSyld (.all x (.objEq x z)) ps (.all x (.imp (.objEq x z) ps)) (.all x ps) p0040
      p0042
  have p0044 :=
    @gPm261d2 (.neg (.all x (.objEq x y))) (.all x (.objEq x z)) (.imp ps (.all x ps))
      p0037 p0043
  exact p0044

/-- Checked nominal proof certificate identified upstream as `g_dveeq2`. -/
@[expose]
noncomputable def gDveeq2 (x : Var) (y : Var) (z : Var) (dv_x_z : x ≠ z) :
    Nominal.NPrf
      (.imp (.neg (.all x (.objEq x y))) (.imp (.objEq z y) (.all x (.objEq z y)))) :=
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
  have p0000 := @gEquequ2 w y z
  have p0001 :=
    @gDvelimv (.objEq z w) (.objEq z y) x y w
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
      (by
        first
        | (aesop))
      p0000
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_ax10lem4`. -/
@[expose]
noncomputable def gAx10lem4 (x : Var) (y : Var) (w : Var) (dv_w_x : w ≠ x)
    (dv_w_y : w ≠ y) : Nominal.NPrf (.imp (.all x (.objEq x w)) (.all y (.objEq y x))) :=
  by
  let proofSupport : Finset Var :=
    ({ x } : Finset Var) ∪ ({ y } : Finset Var) ∪ ({ w } : Finset Var)
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
  have fresh_z_ne_w : z ≠ w := by
    intro h
    exact fresh_z (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))
  have fresh_w_ne_z : w ≠ z := Ne.symm fresh_z_ne_w
  have p0000 :=
    @gAx10lem1 x y w
      (by
        first
        | (aesop))
      (by
        first
        | (aesop))
  have p0001 := @gEquequ1 z x w
  have p0002 :=
    @gDvelimv (.objEq z w) (.objEq x w) y x z
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
      (by
        first
        | (aesop))
      p0001
  have p0003 := @gHba1 (.objEq x w) y
  have p0004 := @gEquequ2 x w y
  have p0005 := @gSps (.objEq x w) (synWb (.objEq y x) (.objEq y w)) y p0004
  have p0006 := @gAlbidh (.all y (.objEq x w)) (.objEq y x) (.objEq y w) y p0003 p0005
  have p0007 :=
    @gBiimprd (.all y (.objEq x w)) (.all y (.objEq y x)) (.all y (.objEq y w)) p0006
  have p0008 :=
    @gSyl6 (.neg (.all y (.objEq y x))) (.objEq x w) (.all y (.objEq x w))
      (.imp (.all y (.objEq y w)) (.all y (.objEq y x))) p0002 p0007
  have p0009 :=
    @gSyl7 (.all x (.objEq x w)) (.all y (.objEq y w)) (.neg (.all y (.objEq y x)))
      (.objEq x w) (.all y (.objEq y x)) p0000 p0008
  have p0010 :=
    @gSpsd (.neg (.all y (.objEq y x))) (.objEq x w)
      (.imp (.all x (.objEq x w)) (.all y (.objEq y x))) x p0009
  have p0011 :=
    @gPm243d (.neg (.all y (.objEq y x))) (.all x (.objEq x w)) (.all y (.objEq y x))
      p0010
  have p0012 :=
    @gCom12 (.neg (.all y (.objEq y x))) (.all x (.objEq x w)) (.all y (.objEq y x))
      p0011
  have p0013 := @gPm218d (.all x (.objEq x w)) (.all y (.objEq y x)) p0012
  exact p0013

/-- Checked nominal proof certificate identified upstream as `g_ax10lem5`. -/
@[expose]
noncomputable def gAx10lem5 (x : Var) (y : Var) (z : Var) (w : Var) (dv_w_z : w ≠ z) :
    Nominal.NPrf (.imp (.all z (.objEq z w)) (.all y (.objEq y x))) :=
  by
  let proofSupport : Finset Var :=
    ({ x } : Finset Var) ∪ ({ y } : Finset Var) ∪ ({ z } : Finset Var) ∪
      ({ w } : Finset Var)
  let v : Var := freshVar proofSupport 0
  let u : Var := freshVar proofSupport 1
  have fresh_v : v ∉ proofSupport :=
    by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_v_ne_x : v ≠ x := by
    intro h
    exact
      fresh_v
        (Finset.mem_union_left _ (Finset.mem_union_left _
            (Finset.mem_union_left _ (Finset.mem_singleton.mpr h))))
  have fresh_x_ne_v : x ≠ v := Ne.symm fresh_v_ne_x
  have fresh_v_ne_y : v ≠ y := by
    intro h
    exact
      fresh_v
        (Finset.mem_union_left _ (Finset.mem_union_left _
            (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))))
  have fresh_y_ne_v : y ≠ v := Ne.symm fresh_v_ne_y
  have fresh_v_ne_z : v ≠ z := by
    intro h
    exact
      fresh_v
        (Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_singleton.mpr h)))
  have fresh_z_ne_v : z ≠ v := Ne.symm fresh_v_ne_z
  have fresh_v_ne_w : v ≠ w := by
    intro h
    exact fresh_v (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))
  have fresh_w_ne_v : w ≠ v := Ne.symm fresh_v_ne_w
  have fresh_u : u ∉ proofSupport :=
    by
    change freshVar proofSupport 1 ∉ proofSupport
    exact freshVar_not_mem proofSupport 1
  have fresh_u_ne_x : u ≠ x := by
    intro h
    exact
      fresh_u
        (Finset.mem_union_left _ (Finset.mem_union_left _
            (Finset.mem_union_left _ (Finset.mem_singleton.mpr h))))
  have fresh_x_ne_u : x ≠ u := Ne.symm fresh_u_ne_x
  have fresh_u_ne_y : u ≠ y := by
    intro h
    exact
      fresh_u
        (Finset.mem_union_left _ (Finset.mem_union_left _
            (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))))
  have fresh_y_ne_u : y ≠ u := Ne.symm fresh_u_ne_y
  have fresh_u_ne_z : u ≠ z := by
    intro h
    exact
      fresh_u
        (Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_singleton.mpr h)))
  have fresh_z_ne_u : z ≠ u := Ne.symm fresh_u_ne_z
  have fresh_u_ne_w : u ≠ w := by
    intro h
    exact fresh_u (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))
  have fresh_w_ne_u : w ≠ u := Ne.symm fresh_u_ne_w
  have fresh_v_ne_u : v ≠ u :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have fresh_u_ne_v : u ≠ v := Ne.symm fresh_v_ne_u
  have p0000 :=
    @gAx10lem1 z v w
      (by
        first
        | (aesop))
      (by
        first
        | (aesop))
  have p0001 :=
    @gAx10lem4 v u w
      (by
        first
        | (aesop))
      (by
        first
        | (aesop))
  have p0002 :=
    @gSyl (.all z (.objEq z w)) (.all v (.objEq v w)) (.all u (.objEq u v)) p0000 p0001
  have p0003 :=
    @gAx10lem1 u x v
      (by
        first
        | (aesop))
      (by
        first
        | (aesop))
  have p0004 :=
    @gSyl (.all z (.objEq z w)) (.all u (.objEq u v)) (.all x (.objEq x v)) p0002 p0003
  have p0005 :=
    @gAx10lem4 x y v
      (by
        first
        | (aesop))
      (by
        first
        | (aesop))
  have p0006 :=
    @gSyl (.all z (.objEq z w)) (.all x (.objEq x v)) (.all y (.objEq y x)) p0004 p0005
  exact p0006

/-- Checked nominal proof certificate identified upstream as `g_ax10lem6`. -/
@[expose]
noncomputable def gAx10lem6 (ph : Wff) (x : Var) (y : Var) :
    Nominal.NPrf (.imp (.all y (.objEq y x)) (.imp (.all x ph) (.all y ph))) :=
  by
  have p0000 := Nominal.ax11Structural y x ph
  have p0001 :=
    @gSps (.objEq y x) (.imp (.all x ph) (.all y (.imp (.objEq y x) ph))) y p0000
  have p0002 := @gPm227 (.objEq y x) ph
  have p0003 := @gAl2imi (.objEq y x) (.imp (.objEq y x) ph) ph y p0002
  have p0004 :=
    @gSyld (.all y (.objEq y x)) (.all x ph) (.all y (.imp (.objEq y x) ph)) (.all y ph)
      p0001 p0003
  exact p0004

/-- Checked nominal proof certificate identified upstream as `g_ax10`. -/
@[expose]
noncomputable def gAx10 (x : Var) (y : Var) :
    Nominal.NPrf (.imp (.all x (.objEq x y)) (.all y (.objEq y x))) :=
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
    @gAx9v z x
      (by
        first
        | (aesop))
  have p0001 := (Nominal.biimpRefl (synWex z (.objEq z x)))
  have p0002 :=
    @gDveeq2 y x z
      (by
        first
        | (aesop))
  have p0003 :=
    @gImp (.neg (.all y (.objEq y x))) (.objEq z x) (.all y (.objEq z x)) p0002
  have p0004 := @gAx10lem6 (.objEq z x) y x
  have p0005 := @gEqucomi z x
  have p0006 := @gAlimi (.objEq z x) (.objEq x z) x p0005
  have p0007 :=
    @gSyl6 (.all x (.objEq x y)) (.all y (.objEq z x)) (.all x (.objEq z x))
      (.all x (.objEq x z)) p0004 p0006
  have p0008 :=
    @gAx10lem5 x y x z
      (by
        first
        | (aesop))
  have p0009 :=
    @gSyl56 (synWa (.neg (.all y (.objEq y x))) (.objEq z x)) (.all y (.objEq z x))
      (.all x (.objEq x y)) (.all x (.objEq x z)) (.all y (.objEq y x)) p0003 p0007 p0008
  have p0010 :=
    @gExp3acom23 (.all x (.objEq x y)) (.neg (.all y (.objEq y x))) (.objEq z x)
      (.all y (.objEq y x)) p0009
  have p0011 := @gPm218 (.all y (.objEq y x))
  have p0012 :=
    @gSyl6 (.all x (.objEq x y)) (.objEq z x)
      (.imp (.neg (.all y (.objEq y x))) (.all y (.objEq y x))) (.all y (.objEq y x))
      p0010 p0011
  have p0013 :=
    @gExlimdv (.all x (.objEq x y)) (.objEq z x) (.all y (.objEq y x)) z
      (by
        first
        |
          (simp (config :=
              { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_wff_all,
              NFChoice.Compiler.CoreFVSimp.fv_wff_objEq, Finset.mem_erase] at ⊢;
            aesop))
      (by
        first
        |
          (simp (config :=
              { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_wff_all,
              NFChoice.Compiler.CoreFVSimp.fv_wff_objEq, Finset.mem_erase] at ⊢;
            aesop))
      p0012
  have p0014 :=
    @gSyl5bir (.neg (.all z (.neg (.objEq z x)))) (synWex z (.objEq z x))
      (.all x (.objEq x y)) (.all y (.objEq y x)) p0001 p0013
  have p0015 :=
    @gMpi (.all x (.objEq x y)) (.neg (.all z (.neg (.objEq z x)))) (.all y (.objEq y x))
      p0000 p0014
  exact p0015

/-- Checked nominal proof certificate identified upstream as `g_a16g`. -/
@[expose]
noncomputable def gA16g (ph : Wff) (x : Var) (y : Var) (z : Var) (dv_x_y : x ≠ y) :
    Nominal.NPrf (.imp (.all x (.objEq x y)) (.imp ph (.all z ph))) :=
  by
  let proofSupport : Finset Var :=
    ph.fv ∪ ({ x } : Finset Var) ∪ ({ y } : Finset Var) ∪ ({ z } : Finset Var)
  let w : Var := freshVar proofSupport 0
  have fresh_w : w ∉ proofSupport :=
    by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_w_not_ph : w ∉ ph.fv := by
    intro h
    exact
      fresh_w
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (h))))
  have fresh_w_ne_x : w ≠ x := by
    intro h
    exact
      fresh_w
        (Finset.mem_union_left _ (Finset.mem_union_left _
            (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))))
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
    @gA9ev w z
      (by
        first
        | (aesop))
  have p0001 :=
    @gAx10lem5 z w x y
      (by
        first
        | (aesop))
  have p0002 := @gHbn1 (.objEq w z) w
  have p0003 := @gPm221 (.all w (.objEq w z)) (.imp ph (.all z ph))
  have p0004 :=
    @gAlrimih (.neg (.all w (.objEq w z)))
      (.imp (.all w (.objEq w z)) (.imp ph (.all z ph))) w p0002 p0003
  have p0005 :=
    Nominal.ax17 (.imp ph (.all z ph)) w
      (by
        first
        |
          (simp (config :=
              { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp,
              NFChoice.Compiler.CoreFVSimp.fv_wff_all, Finset.mem_union,
              Finset.mem_erase] at ⊢;
            aesop))
  have p0006 := Nominal.ax1 (.imp ph (.all z ph)) (.all w (.objEq w z))
  have p0007 :=
    @gAlrimih (.imp ph (.all z ph)) (.imp (.all w (.objEq w z)) (.imp ph (.all z ph))) w
      p0005 p0006
  have p0008 :=
    @gJa (.all w (.objEq w z)) (.imp ph (.all z ph))
      (.all w (.imp (.all w (.objEq w z)) (.imp ph (.all z ph)))) p0004 p0007
  have p0009 :=
    @gAx10lem5 w z w z
      (by
        first
        | (aesop))
  have p0010 := @gEqucomi w z
  have p0011 :=
    Nominal.ax17 ph w
      (by
        first
        | (aesop))
  have p0012 := Nominal.ax11Structural z w ph
  have p0013 :=
    @gSyl2im (.objEq w z) (.objEq z w) ph (.all w ph) (.all z (.imp (.objEq z w) ph))
      p0010 p0011 p0012
  have p0014 := Nominal.ax5 z (.objEq z w) ph
  have p0015 :=
    @gSyl6 (.objEq w z) ph (.all z (.imp (.objEq z w) ph))
      (.imp (.all z (.objEq z w)) (.all z ph)) p0013 p0014
  have p0016 := @gCom23 (.objEq w z) ph (.all z (.objEq z w)) (.all z ph) p0015
  have p0017 :=
    @gSyl5 (.all w (.objEq w z)) (.all z (.objEq z w)) (.objEq w z) (.imp ph (.all z ph))
      p0009 p0016
  have p0018 :=
    @gExlimih (.objEq w z) (.imp (.all w (.objEq w z)) (.imp ph (.all z ph))) w p0008
      p0017
  have p0019 :=
    @gMpsyl (synWex w (.objEq w z)) (.all x (.objEq x y)) (.all w (.objEq w z))
      (.imp ph (.all z ph)) p0000 p0001 p0018
  exact p0019

/-- Checked nominal proof certificate identified upstream as `g_aecom`. -/
@[expose]
noncomputable def gAecom (x : Var) (y : Var) :
    Nominal.NPrf (.imp (.all x (.objEq x y)) (.all y (.objEq y x))) :=
  by
  have p0000 := @gAx10 x y
  exact p0000

/-- Checked nominal proof certificate identified upstream as `g_aecoms`. -/
@[expose]
noncomputable def gAecoms (ph : Wff) (x : Var) (y : Var)
    (hyp_alequcoms_1 : Nominal.NPrf (.imp (.all x (.objEq x y)) ph)) :
    Nominal.NPrf (.imp (.all y (.objEq y x)) ph) :=
  by
  have p0000 := @gAecom y x
  have p0001 :=
    @gSyl (.all y (.objEq y x)) (.all x (.objEq x y)) ph p0000 hyp_alequcoms_1
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_ax9`. -/
@[expose]
noncomputable def gAx9 (x : Var) (y : Var) :
    Nominal.NPrf (.neg (.all x (.neg (.objEq x y)))) :=
  by
  let proofSupport : Finset Var := ({ x } : Finset Var) ∪ ({ y } : Finset Var)
  let v : Var := freshVar proofSupport 0
  have fresh_v : v ∉ proofSupport :=
    by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_v_ne_x : v ≠ x := by
    intro h
    exact fresh_v (Finset.mem_union_left _ (Finset.mem_singleton.mpr h))
  have fresh_x_ne_v : x ≠ v := Ne.symm fresh_v_ne_x
  have fresh_v_ne_y : v ≠ y := by
    intro h
    exact fresh_v (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))
  have fresh_y_ne_v : y ≠ v := Ne.symm fresh_v_ne_y
  have p0000 := @gSp (.neg (.objEq x y)) x
  have p0001 := @gSp (.objEq x y) x
  have p0002 :=
    @gNsyl3 (.all x (.neg (.objEq x y))) (.objEq x y) (.all x (.objEq x y)) p0000 p0001
  have p0003 :=
    @gAx9v v y
      (by
        first
        | (aesop))
  have p0004 :=
    @gDveeq2 x y v
      (by
        first
        | (aesop))
  have p0005 :=
    @gAx9v x v
      (by
        first
        | (aesop))
  have p0006 := @gHba1 (.objEq v y) x
  have p0007 := @gSp (.objEq v y) x
  have p0008 := @gEquequ2 v y x
  have p0009 :=
    @gSyl (.all x (.objEq v y)) (.objEq v y) (synWb (.objEq x v) (.objEq x y)) p0007
      p0008
  have p0010 := @gNotbid (.all x (.objEq v y)) (.objEq x v) (.objEq x y) p0009
  have p0011 :=
    @gAlbidh (.all x (.objEq v y)) (.neg (.objEq x v)) (.neg (.objEq x y)) x p0006 p0010
  have p0012 :=
    @gMtbii (.all x (.objEq v y)) (.all x (.neg (.objEq x v)))
      (.all x (.neg (.objEq x y))) p0005 p0011
  have p0013 :=
    @gSyl6com (.neg (.all x (.objEq x y))) (.objEq v y) (.all x (.objEq v y))
      (.neg (.all x (.neg (.objEq x y)))) p0004 p0012
  have p0014 :=
    @gCon3i (.objEq v y)
      (.imp (.neg (.all x (.objEq x y))) (.neg (.all x (.neg (.objEq x y))))) p0013
  have p0015 :=
    @gAlrimiv
      (.neg (.imp (.neg (.all x (.objEq x y))) (.neg (.all x (.neg (.objEq x y))))))
      (.neg (.objEq v y)) v
      (by
        first
        |
          (simp (config :=
              { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_wff_neg,
              NFChoice.Compiler.CoreFVSimp.fv_wff_imp,
              NFChoice.Compiler.CoreFVSimp.fv_wff_all,
              NFChoice.Compiler.CoreFVSimp.fv_wff_objEq, Finset.mem_union,
              Finset.mem_erase] at ⊢;
            aesop))
      p0014
  have p0016 :=
    @gMt3 (.imp (.neg (.all x (.objEq x y))) (.neg (.all x (.neg (.objEq x y)))))
      (.all v (.neg (.objEq v y))) p0003 p0015
  have p0017 :=
    @gPm261i (.all x (.objEq x y)) (.neg (.all x (.neg (.objEq x y)))) p0002 p0016
  exact p0017

/-- Checked nominal proof certificate identified upstream as `g_ax9o`. -/
@[expose]
noncomputable def gAx9o (ph : Wff) (x : Var) (y : Var) :
    Nominal.NPrf (.imp (.all x (.imp (.objEq x y) (.all x ph))) ph) :=
  by
  have p0000 := @gAx9 x y
  have p0001 := @gCon3 (.objEq x y) (.all x ph)
  have p0002 :=
    @gAl2imi (.imp (.objEq x y) (.all x ph)) (.neg (.all x ph)) (.neg (.objEq x y)) x
      p0001
  have p0003 :=
    @gMtoi (.all x (.imp (.objEq x y) (.all x ph))) (.all x (.neg (.all x ph)))
      (.all x (.neg (.objEq x y))) p0000 p0002
  have p0004 := @gAx6o ph x
  have p0005 :=
    @gSyl (.all x (.imp (.objEq x y) (.all x ph))) (.neg (.all x (.neg (.all x ph)))) ph
      p0003 p0004
  exact p0005

/-- Checked nominal proof certificate identified upstream as `g_a9e`. -/
@[expose]
noncomputable def gA9e (x : Var) (y : Var) : Nominal.NPrf (synWex x (.objEq x y)) :=
  by
  have p0000 := @gAx9 x y
  have p0001 := (Nominal.biimpRefl (synWex x (.objEq x y)))
  have p0002 :=
    @gMpbir (synWex x (.objEq x y)) (.neg (.all x (.neg (.objEq x y)))) p0000 p0001
  exact p0002

/-- Checked nominal proof certificate identified upstream as `g_ax10o`. -/
@[expose]
noncomputable def gAx10o (ph : Wff) (x : Var) (y : Var) :
    Nominal.NPrf (.imp (.all x (.objEq x y)) (.imp (.all x ph) (.all y ph))) :=
  by
  have p0000 := @gAx10 x y
  have p0001 := Nominal.ax11Structural y x ph
  have p0002 := @gEqucoms (.imp (.all x ph) (.all y (.imp (.objEq y x) ph))) y x p0001
  have p0003 :=
    @gSps (.objEq x y) (.imp (.all x ph) (.all y (.imp (.objEq y x) ph))) x p0002
  have p0004 := @gPm227 (.objEq y x) ph
  have p0005 := @gAl2imi (.objEq y x) (.imp (.objEq y x) ph) ph y p0004
  have p0006 :=
    @gSylsyld (.all x (.objEq x y)) (.all y (.objEq y x)) (.all x ph)
      (.all y (.imp (.objEq y x) ph)) (.all y ph) p0000 p0003 p0005
  exact p0006


end NFChoice.DirectNominalPrf.WPPReplay
