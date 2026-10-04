/-
Copyright (c) 2026 Elliot Glazer and NFNotWPP contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elliot Glazer and NFNotWPP contributors
-/

module

public import LeanPool.NFWeakPartition.NominalWPPReplayChunk002

/-! NF weak partition development: NominalWPPReplayChunk003. -/


public section


namespace NFChoice.DirectNominalPrf.WPPReplay

open scoped Fol
open NFChoice.Foundation
open NFChoice.SemanticCore
open NFChoice.ReplaySupport
open NFChoice.Compiler.CompactSourceSyntax

/-- Checked nominal proof certificate identified upstream as `g_ad3antrrr`. -/
@[expose]
noncomputable def gAd3antrrr (ph : Wff) (ps : Wff) (ch : Wff) (th : Wff) (ta : Wff)
    (hyp_ad2ant_1 : Nominal.NPrf (.imp ph ps)) :
    Nominal.NPrf (.imp (synWa (synWa (synWa ph ch) th) ta) ps) :=
  by
  have p0000 := @gAdantr ph ps ch hyp_ad2ant_1
  have p0001 := @gAd2antrr (synWa ph ch) ps th ta p0000
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_ad2ant2l`. -/
@[expose]
noncomputable def gAd2ant2l (ph : Wff) (ps : Wff) (ch : Wff) (th : Wff) (ta : Wff)
    (hyp_ad2ant2_1 : Nominal.NPrf (.imp (synWa ph ps) ch)) :
    Nominal.NPrf (.imp (synWa (synWa th ph) (synWa ta ps)) ch) :=
  by
  have p0000 := @gAdantrl ph ps ch ta hyp_ad2ant2_1
  have p0001 := @gAdantll ph (synWa ta ps) ch th p0000
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_ad2ant2r`. -/
@[expose]
noncomputable def gAd2ant2r (ph : Wff) (ps : Wff) (ch : Wff) (th : Wff) (ta : Wff)
    (hyp_ad2ant2_1 : Nominal.NPrf (.imp (synWa ph ps) ch)) :
    Nominal.NPrf (.imp (synWa (synWa ph th) (synWa ps ta)) ch) :=
  by
  have p0000 := @gAdantrr ph ps ch ta hyp_ad2ant2_1
  have p0001 := @gAdantlr ph (synWa ps ta) ch th p0000
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_ad2ant2rl`. -/
@[expose]
noncomputable def gAd2ant2rl (ph : Wff) (ps : Wff) (ch : Wff) (th : Wff) (ta : Wff)
    (hyp_ad2ant2_1 : Nominal.NPrf (.imp (synWa ph ps) ch)) :
    Nominal.NPrf (.imp (synWa (synWa ph th) (synWa ta ps)) ch) :=
  by
  have p0000 := @gAdantrl ph ps ch ta hyp_ad2ant2_1
  have p0001 := @gAdantlr ph (synWa ta ps) ch th p0000
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_simpll`. -/
@[expose]
noncomputable def gSimpll (ph : Wff) (ps : Wff) (ch : Wff) :
    Nominal.NPrf (.imp (synWa (synWa ph ps) ch) ph) :=
  by
  have p0000 := @gId ph
  have p0001 := @gAd2antrr ph ph ps ch p0000
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_simplr`. -/
@[expose]
noncomputable def gSimplr (ph : Wff) (ps : Wff) (ch : Wff) :
    Nominal.NPrf (.imp (synWa (synWa ph ps) ch) ps) :=
  by
  have p0000 := @gId ps
  have p0001 := @gAd2antlr ps ps ph ch p0000
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_simprl`. -/
@[expose]
noncomputable def gSimprl (ph : Wff) (ps : Wff) (ch : Wff) :
    Nominal.NPrf (.imp (synWa ph (synWa ps ch)) ps) :=
  by
  have p0000 := @gId ps
  have p0001 := @gAd2antrl ps ps ph ch p0000
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_simprr`. -/
@[expose]
noncomputable def gSimprr (ph : Wff) (ps : Wff) (ch : Wff) :
    Nominal.NPrf (.imp (synWa ph (synWa ps ch)) ch) :=
  by
  have p0000 := @gId ch
  have p0001 := @gAd2antll ch ch ph ps p0000
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_simplll`. -/
@[expose]
noncomputable def gSimplll (ph : Wff) (ps : Wff) (ch : Wff) (th : Wff) :
    Nominal.NPrf (.imp (synWa (synWa (synWa ph ps) ch) th) ph) :=
  by
  have p0000 := @gSimpl ph ps
  have p0001 := @gAd2antrr (synWa ph ps) ph ch th p0000
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_simpllr`. -/
@[expose]
noncomputable def gSimpllr (ph : Wff) (ps : Wff) (ch : Wff) (th : Wff) :
    Nominal.NPrf (.imp (synWa (synWa (synWa ph ps) ch) th) ps) :=
  by
  have p0000 := @gSimpr ph ps
  have p0001 := @gAd2antrr (synWa ph ps) ps ch th p0000
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_simplrl`. -/
@[expose]
noncomputable def gSimplrl (ph : Wff) (ps : Wff) (ch : Wff) (th : Wff) :
    Nominal.NPrf (.imp (synWa (synWa ph (synWa ps ch)) th) ps) :=
  by
  have p0000 := @gSimpl ps ch
  have p0001 := @gAd2antlr (synWa ps ch) ps ph th p0000
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_simplrr`. -/
@[expose]
noncomputable def gSimplrr (ph : Wff) (ps : Wff) (ch : Wff) (th : Wff) :
    Nominal.NPrf (.imp (synWa (synWa ph (synWa ps ch)) th) ch) :=
  by
  have p0000 := @gSimpr ps ch
  have p0001 := @gAd2antlr (synWa ps ch) ch ph th p0000
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_simprll`. -/
@[expose]
noncomputable def gSimprll (ph : Wff) (ps : Wff) (ch : Wff) (th : Wff) :
    Nominal.NPrf (.imp (synWa ph (synWa (synWa ps ch) th)) ps) :=
  by
  have p0000 := @gSimpl ps ch
  have p0001 := @gAd2antrl (synWa ps ch) ps ph th p0000
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_simprlr`. -/
@[expose]
noncomputable def gSimprlr (ph : Wff) (ps : Wff) (ch : Wff) (th : Wff) :
    Nominal.NPrf (.imp (synWa ph (synWa (synWa ps ch) th)) ch) :=
  by
  have p0000 := @gSimpr ps ch
  have p0001 := @gAd2antrl (synWa ps ch) ch ph th p0000
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_simprrl`. -/
@[expose]
noncomputable def gSimprrl (ph : Wff) (ps : Wff) (ch : Wff) (th : Wff) :
    Nominal.NPrf (.imp (synWa ph (synWa ps (synWa ch th))) ch) :=
  by
  have p0000 := @gSimpl ch th
  have p0001 := @gAd2antll (synWa ch th) ch ph ps p0000
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_simprrr`. -/
@[expose]
noncomputable def gSimprrr (ph : Wff) (ps : Wff) (ch : Wff) (th : Wff) :
    Nominal.NPrf (.imp (synWa ph (synWa ps (synWa ch th))) th) :=
  by
  have p0000 := @gSimpr ch th
  have p0001 := @gAd2antll (synWa ch th) th ph ps p0000
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_jaob`. -/
@[expose]
noncomputable def gJaob (ph : Wff) (ps : Wff) (ch : Wff) :
    Nominal.NPrf (synWb (.imp (synWo ph ch) ps) (synWa (.imp ph ps) (.imp ch ps))) :=
  by
  have p0000 := @g_pm2_67_2 ph ps ch
  have p0001 := @gOlc ch ph
  have p0002 := @gImim1i ch (synWo ph ch) ps p0001
  have p0003 := @gJca (.imp (synWo ph ch) ps) (.imp ph ps) (.imp ch ps) p0000 p0002
  have p0004 := @gPm344 ps ph ch
  have p0005 :=
    @gImpbii (.imp (synWo ph ch) ps) (synWa (.imp ph ps) (.imp ch ps)) p0003 p0004
  exact p0005

/-- Checked nominal proof certificate identified upstream as `g_jaoian`. -/
@[expose]
noncomputable def gJaoian (ph : Wff) (ps : Wff) (ch : Wff) (th : Wff)
    (hyp_jaoian_1 : Nominal.NPrf (.imp (synWa ph ps) ch))
    (hyp_jaoian_2 : Nominal.NPrf (.imp (synWa th ps) ch)) :
    Nominal.NPrf (.imp (synWa (synWo ph th) ps) ch) :=
  by
  have p0000 := @gEx ph ps ch hyp_jaoian_1
  have p0001 := @gEx th ps ch hyp_jaoian_2
  have p0002 := @gJaoi ph (.imp ps ch) th p0000 p0001
  have p0003 := @gImp (synWo ph th) ps ch p0002
  exact p0003

/-- Checked nominal proof certificate identified upstream as `g_jaodan`. -/
@[expose]
noncomputable def gJaodan (ph : Wff) (ps : Wff) (ch : Wff) (th : Wff)
    (hyp_jaodan_1 : Nominal.NPrf (.imp (synWa ph ps) ch))
    (hyp_jaodan_2 : Nominal.NPrf (.imp (synWa ph th) ch)) :
    Nominal.NPrf (.imp (synWa ph (synWo ps th)) ch) :=
  by
  have p0000 := @gEx ph ps ch hyp_jaodan_1
  have p0001 := @gEx ph th ch hyp_jaodan_2
  have p0002 := @gJaod ph ps ch th p0000 p0001
  have p0003 := @gImp ph (synWo ps th) ch p0002
  exact p0003

/-- Checked nominal proof certificate identified upstream as `g_pm2_61ian`. -/
@[expose]
noncomputable def gPm261ian (ph : Wff) (ps : Wff) (ch : Wff)
    (hyp_pm2_61ian_1 : Nominal.NPrf (.imp (synWa ph ps) ch))
    (hyp_pm2_61ian_2 : Nominal.NPrf (.imp (synWa (.neg ph) ps) ch)) :
    Nominal.NPrf (.imp ps ch) :=
  by
  have p0000 := @gEx ph ps ch hyp_pm2_61ian_1
  have p0001 := @gEx (.neg ph) ps ch hyp_pm2_61ian_2
  have p0002 := @gPm261i ph (.imp ps ch) p0000 p0001
  exact p0002

/-- Checked nominal proof certificate identified upstream as `g_pm2_61dan`. -/
@[expose]
noncomputable def gPm261dan (ph : Wff) (ps : Wff) (ch : Wff)
    (hyp_pm2_61dan_1 : Nominal.NPrf (.imp (synWa ph ps) ch))
    (hyp_pm2_61dan_2 : Nominal.NPrf (.imp (synWa ph (.neg ps)) ch)) :
    Nominal.NPrf (.imp ph ch) :=
  by
  have p0000 := @gEx ph ps ch hyp_pm2_61dan_1
  have p0001 := @gEx ph (.neg ps) ch hyp_pm2_61dan_2
  have p0002 := @gPm261d ph ps ch p0000 p0001
  exact p0002

/-- Checked nominal proof certificate identified upstream as `g_abai`. -/
@[expose]
noncomputable def gAbai (ph : Wff) (ps : Wff) :
    Nominal.NPrf (synWb (synWa ph ps) (synWa ph (.imp ph ps))) :=
  by
  have p0000 := @gBiimt ph ps
  have p0001 := @gPm532i ph ps (.imp ph ps) p0000
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_an12`. -/
@[expose]
noncomputable def gAn12 (ph : Wff) (ps : Wff) (ch : Wff) :
    Nominal.NPrf (synWb (synWa ph (synWa ps ch)) (synWa ps (synWa ph ch))) :=
  by
  have p0000 := @gAncom ph ps
  have p0001 := @gAnbi1i (synWa ph ps) (synWa ps ph) ch p0000
  have p0002 := @gAnass ph ps ch
  have p0003 := @gAnass ps ph ch
  have p0004 :=
    @gN3bitr3i (synWa (synWa ph ps) ch) (synWa (synWa ps ph) ch)
      (synWa ph (synWa ps ch)) (synWa ps (synWa ph ch)) p0001 p0002 p0003
  exact p0004

/-- Checked nominal proof certificate identified upstream as `g_an32`. -/
@[expose]
noncomputable def gAn32 (ph : Wff) (ps : Wff) (ch : Wff) :
    Nominal.NPrf (synWb (synWa (synWa ph ps) ch) (synWa (synWa ph ch) ps)) :=
  by
  have p0000 := @gAnass ph ps ch
  have p0001 := @gAn12 ph ps ch
  have p0002 := @gAncom ps (synWa ph ch)
  have p0003 :=
    @gN3bitri (synWa (synWa ph ps) ch) (synWa ph (synWa ps ch))
      (synWa ps (synWa ph ch)) (synWa (synWa ph ch) ps) p0000 p0001 p0002
  exact p0003

/-- Checked nominal proof certificate identified upstream as `g_an13`. -/
@[expose]
noncomputable def gAn13 (ph : Wff) (ps : Wff) (ch : Wff) :
    Nominal.NPrf (synWb (synWa ph (synWa ps ch)) (synWa ch (synWa ps ph))) :=
  by
  have p0000 := @gAn12 ph ps ch
  have p0001 := @gAnass ps ph ch
  have p0002 := @gAncom (synWa ps ph) ch
  have p0003 :=
    @gN3bitr2i (synWa ph (synWa ps ch)) (synWa ps (synWa ph ch))
      (synWa (synWa ps ph) ch) (synWa ch (synWa ps ph)) p0000 p0001 p0002
  exact p0003

/-- Checked nominal proof certificate identified upstream as `g_an12s`. -/
@[expose]
noncomputable def gAn12s (ph : Wff) (ps : Wff) (ch : Wff) (th : Wff)
    (hyp_an12s_1 : Nominal.NPrf (.imp (synWa ph (synWa ps ch)) th)) :
    Nominal.NPrf (.imp (synWa ps (synWa ph ch)) th) :=
  by
  have p0000 := @gAn12 ps ph ch
  have p0001 :=
    @gSylbi (synWa ps (synWa ph ch)) (synWa ph (synWa ps ch)) th p0000 hyp_an12s_1
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_ancom2s`. -/
@[expose]
noncomputable def gAncom2s (ph : Wff) (ps : Wff) (ch : Wff) (th : Wff)
    (hyp_an12s_1 : Nominal.NPrf (.imp (synWa ph (synWa ps ch)) th)) :
    Nominal.NPrf (.imp (synWa ph (synWa ch ps)) th) :=
  by
  have p0000 := @gPm322 ch ps
  have p0001 := @gSylan2 (synWa ch ps) ph (synWa ps ch) th p0000 hyp_an12s_1
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_an32s`. -/
@[expose]
noncomputable def gAn32s (ph : Wff) (ps : Wff) (ch : Wff) (th : Wff)
    (hyp_an32s_1 : Nominal.NPrf (.imp (synWa (synWa ph ps) ch) th)) :
    Nominal.NPrf (.imp (synWa (synWa ph ch) ps) th) :=
  by
  have p0000 := @gAn32 ph ch ps
  have p0001 :=
    @gSylbi (synWa (synWa ph ch) ps) (synWa (synWa ph ps) ch) th p0000 hyp_an32s_1
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_anabsan`. -/
@[expose]
noncomputable def gAnabsan (ph : Wff) (ps : Wff) (ch : Wff)
    (hyp_anabsan_1 : Nominal.NPrf (.imp (synWa (synWa ph ph) ps) ch)) :
    Nominal.NPrf (.imp (synWa ph ps) ch) :=
  by
  have p0000 := @gPm424 ph
  have p0001 := @gSylanb ph (synWa ph ph) ps ch p0000 hyp_anabsan_1
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_anabss1`. -/
@[expose]
noncomputable def gAnabss1 (ph : Wff) (ps : Wff) (ch : Wff)
    (hyp_anabss1_1 : Nominal.NPrf (.imp (synWa (synWa ph ps) ph) ch)) :
    Nominal.NPrf (.imp (synWa ph ps) ch) :=
  by
  have p0000 := @gAn32s ph ps ph ch hyp_anabss1_1
  have p0001 := @gAnabsan ph ps ch p0000
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_anabss4`. -/
@[expose]
noncomputable def gAnabss4 (ph : Wff) (ps : Wff) (ch : Wff)
    (hyp_anabss4_1 : Nominal.NPrf (.imp (synWa (synWa ps ph) ps) ch)) :
    Nominal.NPrf (.imp (synWa ph ps) ch) :=
  by
  have p0000 := @gAnabss1 ps ph ch hyp_anabss4_1
  have p0001 := @gAncoms ps ph ch p0000
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_anabss5`. -/
@[expose]
noncomputable def gAnabss5 (ph : Wff) (ps : Wff) (ch : Wff)
    (hyp_anabss5_1 : Nominal.NPrf (.imp (synWa ph (synWa ph ps)) ch)) :
    Nominal.NPrf (.imp (synWa ph ps) ch) :=
  by
  have p0000 := @gAnassrs ph ph ps ch hyp_anabss5_1
  have p0001 := @gAnabsan ph ps ch p0000
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_anabsi5`. -/
@[expose]
noncomputable def gAnabsi5 (ph : Wff) (ps : Wff) (ch : Wff)
    (hyp_anabsi5_1 : Nominal.NPrf (.imp ph (.imp (synWa ph ps) ch))) :
    Nominal.NPrf (.imp (synWa ph ps) ch) :=
  by
  have p0000 := @gImp ph (synWa ph ps) ch hyp_anabsi5_1
  have p0001 := @gAnabss5 ph ps ch p0000
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_anabsi6`. -/
@[expose]
noncomputable def gAnabsi6 (ph : Wff) (ps : Wff) (ch : Wff)
    (hyp_anabsi6_1 : Nominal.NPrf (.imp ph (.imp (synWa ps ph) ch))) :
    Nominal.NPrf (.imp (synWa ph ps) ch) :=
  by
  have p0000 := @gAncomsd ph ps ph ch hyp_anabsi6_1
  have p0001 := @gAnabsi5 ph ps ch p0000
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_anabsi7`. -/
@[expose]
noncomputable def gAnabsi7 (ph : Wff) (ps : Wff) (ch : Wff)
    (hyp_anabsi7_1 : Nominal.NPrf (.imp ps (.imp (synWa ph ps) ch))) :
    Nominal.NPrf (.imp (synWa ph ps) ch) :=
  by
  have p0000 := @gAnabsi6 ps ph ch hyp_anabsi7_1
  have p0001 := @gAncoms ps ph ch p0000
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_anabss7`. -/
@[expose]
noncomputable def gAnabss7 (ph : Wff) (ps : Wff) (ch : Wff)
    (hyp_anabss7_1 : Nominal.NPrf (.imp (synWa ps (synWa ph ps)) ch)) :
    Nominal.NPrf (.imp (synWa ph ps) ch) :=
  by
  have p0000 := @gAnassrs ps ph ps ch hyp_anabss7_1
  have p0001 := @gAnabss4 ph ps ch p0000
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_anabsan2`. -/
@[expose]
noncomputable def gAnabsan2 (ph : Wff) (ps : Wff) (ch : Wff)
    (hyp_anabsan2_1 : Nominal.NPrf (.imp (synWa ph (synWa ps ps)) ch)) :
    Nominal.NPrf (.imp (synWa ph ps) ch) :=
  by
  have p0000 := @gAn12s ph ps ps ch hyp_anabsan2_1
  have p0001 := @gAnabss7 ph ps ch p0000
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_anabss3`. -/
@[expose]
noncomputable def gAnabss3 (ph : Wff) (ps : Wff) (ch : Wff)
    (hyp_anabss3_1 : Nominal.NPrf (.imp (synWa (synWa ph ps) ps) ch)) :
    Nominal.NPrf (.imp (synWa ph ps) ch) :=
  by
  have p0000 := @gAnasss ph ps ps ch hyp_anabss3_1
  have p0001 := @gAnabsan2 ph ps ch p0000
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_an4`. -/
@[expose]
noncomputable def gAn4 (ph : Wff) (ps : Wff) (ch : Wff) (th : Wff) :
    Nominal.NPrf
      (synWb (synWa (synWa ph ps) (synWa ch th)) (synWa (synWa ph ch) (synWa ps th))) :=
  by
  have p0000 := @gAn12 ps ch th
  have p0001 := @gAnbi2i (synWa ps (synWa ch th)) (synWa ch (synWa ps th)) ph p0000
  have p0002 := @gAnass ph ps (synWa ch th)
  have p0003 := @gAnass ph ch (synWa ps th)
  have p0004 :=
    @gN3bitr4i (synWa ph (synWa ps (synWa ch th)))
      (synWa ph (synWa ch (synWa ps th))) (synWa (synWa ph ps) (synWa ch th))
      (synWa (synWa ph ch) (synWa ps th)) p0001 p0002 p0003
  exact p0004

/-- Checked nominal proof certificate identified upstream as `g_an42`. -/
@[expose]
noncomputable def gAn42 (ph : Wff) (ps : Wff) (ch : Wff) (th : Wff) :
    Nominal.NPrf
      (synWb (synWa (synWa ph ps) (synWa ch th)) (synWa (synWa ph ch) (synWa th ps))) :=
  by
  have p0000 := @gAn4 ph ps ch th
  have p0001 := @gAncom ps th
  have p0002 := @gAnbi2i (synWa ps th) (synWa th ps) (synWa ph ch) p0001
  have p0003 :=
    @gBitri (synWa (synWa ph ps) (synWa ch th)) (synWa (synWa ph ch) (synWa ps th))
      (synWa (synWa ph ch) (synWa th ps)) p0000 p0002
  exact p0003

/-- Checked nominal proof certificate identified upstream as `g_an4s`. -/
@[expose]
noncomputable def gAn4s (ph : Wff) (ps : Wff) (ch : Wff) (th : Wff) (ta : Wff)
    (hyp_an4s_1 : Nominal.NPrf (.imp (synWa (synWa ph ps) (synWa ch th)) ta)) :
    Nominal.NPrf (.imp (synWa (synWa ph ch) (synWa ps th)) ta) :=
  by
  have p0000 := @gAn4 ph ch ps th
  have p0001 :=
    @gSylbi (synWa (synWa ph ch) (synWa ps th)) (synWa (synWa ph ps) (synWa ch th))
      ta p0000 hyp_an4s_1
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_anandi`. -/
@[expose]
noncomputable def gAnandi (ph : Wff) (ps : Wff) (ch : Wff) :
    Nominal.NPrf
      (synWb (synWa ph (synWa ps ch)) (synWa (synWa ph ps) (synWa ph ch))) :=
  by
  have p0000 := @gAnidm ph
  have p0001 := @gAnbi1i (synWa ph ph) ph (synWa ps ch) p0000
  have p0002 := @gAn4 ph ph ps ch
  have p0003 :=
    @gBitr3i (synWa ph (synWa ps ch)) (synWa (synWa ph ph) (synWa ps ch))
      (synWa (synWa ph ps) (synWa ph ch)) p0001 p0002
  exact p0003

/-- Checked nominal proof certificate identified upstream as `g_anandir`. -/
@[expose]
noncomputable def gAnandir (ph : Wff) (ps : Wff) (ch : Wff) :
    Nominal.NPrf
      (synWb (synWa (synWa ph ps) ch) (synWa (synWa ph ch) (synWa ps ch))) :=
  by
  have p0000 := @gAnidm ch
  have p0001 := @gAnbi2i (synWa ch ch) ch (synWa ph ps) p0000
  have p0002 := @gAn4 ph ps ch ch
  have p0003 :=
    @gBitr3i (synWa (synWa ph ps) ch) (synWa (synWa ph ps) (synWa ch ch))
      (synWa (synWa ph ch) (synWa ps ch)) p0001 p0002
  exact p0003

/-- Checked nominal proof certificate identified upstream as `g_anandis`. -/
@[expose]
noncomputable def gAnandis (ph : Wff) (ps : Wff) (ch : Wff) (ta : Wff)
    (hyp_anandis_1 : Nominal.NPrf (.imp (synWa (synWa ph ps) (synWa ph ch)) ta)) :
    Nominal.NPrf (.imp (synWa ph (synWa ps ch)) ta) :=
  by
  have p0000 := @gAn4s ph ps ph ch ta hyp_anandis_1
  have p0001 := @gAnabsan ph (synWa ps ch) ta p0000
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_impbida`. -/
@[expose]
noncomputable def gImpbida (ph : Wff) (ps : Wff) (ch : Wff)
    (hyp_impbida_1 : Nominal.NPrf (.imp (synWa ph ps) ch))
    (hyp_impbida_2 : Nominal.NPrf (.imp (synWa ph ch) ps)) :
    Nominal.NPrf (.imp ph (synWb ps ch)) :=
  by
  have p0000 := @gEx ph ps ch hyp_impbida_1
  have p0001 := @gEx ph ch ps hyp_impbida_2
  have p0002 := @gImpbid ph ps ch p0000 p0001
  exact p0002

/-- Checked nominal proof certificate identified upstream as `g_pm3_48`. -/
@[expose]
noncomputable def gPm348 (ph : Wff) (ps : Wff) (ch : Wff) (th : Wff) :
    Nominal.NPrf
      (.imp (synWa (.imp ph ps) (.imp ch th)) (.imp (synWo ph ch) (synWo ps th))) :=
  by
  have p0000 := @gOrc ps th
  have p0001 := @gImim2i ps (synWo ps th) ph p0000
  have p0002 := @gOlc th ps
  have p0003 := @gImim2i th (synWo ps th) ch p0002
  have p0004 := @gJaao (.imp ph ps) ph (synWo ps th) (.imp ch th) ch p0001 p0003
  exact p0004

/-- Checked nominal proof certificate identified upstream as `g_im2anan9`. -/
@[expose]
noncomputable def gIm2anan9 (ph : Wff) (ps : Wff) (ch : Wff) (th : Wff) (ta : Wff)
    (et : Wff) (hyp_im2an9_1 : Nominal.NPrf (.imp ph (.imp ps ch)))
    (hyp_im2an9_2 : Nominal.NPrf (.imp th (.imp ta et))) :
    Nominal.NPrf (.imp (synWa ph th) (.imp (synWa ps ta) (synWa ch et))) :=
  by
  have p0000 := @gAdantr ph (.imp ps ch) th hyp_im2an9_1
  have p0001 := @gAdantl th (.imp ta et) ph hyp_im2an9_2
  have p0002 := @gAnim12d (synWa ph th) ps ch ta et p0000 p0001
  exact p0002

/-- Checked nominal proof certificate identified upstream as `g_anim12dan`. -/
@[expose]
noncomputable def gAnim12dan (ph : Wff) (ps : Wff) (ch : Wff) (th : Wff) (ta : Wff)
    (hyp_anim12dan_1 : Nominal.NPrf (.imp (synWa ph ps) ch))
    (hyp_anim12dan_2 : Nominal.NPrf (.imp (synWa ph th) ta)) :
    Nominal.NPrf (.imp (synWa ph (synWa ps th)) (synWa ch ta)) :=
  by
  have p0000 := @gEx ph ps ch hyp_anim12dan_1
  have p0001 := @gEx ph th ta hyp_anim12dan_2
  have p0002 := @gAnim12d ph ps ch th ta p0000 p0001
  have p0003 := @gImp ph (synWa ps th) (synWa ch ta) p0002
  exact p0003

/-- Checked nominal proof certificate identified upstream as `g_orim12d`. -/
@[expose]
noncomputable def gOrim12d (ph : Wff) (ps : Wff) (ch : Wff) (th : Wff) (ta : Wff)
    (hyp_orim12d_1 : Nominal.NPrf (.imp ph (.imp ps ch)))
    (hyp_orim12d_2 : Nominal.NPrf (.imp ph (.imp th ta))) :
    Nominal.NPrf (.imp ph (.imp (synWo ps th) (synWo ch ta))) :=
  by
  have p0000 := @gPm348 ps ch th ta
  have p0001 :=
    @gSyl2anc ph (.imp ps ch) (.imp th ta) (.imp (synWo ps th) (synWo ch ta))
      hyp_orim12d_1 hyp_orim12d_2 p0000
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_orim1d`. -/
@[expose]
noncomputable def gOrim1d (ph : Wff) (ps : Wff) (ch : Wff) (th : Wff)
    (hyp_orim1d_1 : Nominal.NPrf (.imp ph (.imp ps ch))) :
    Nominal.NPrf (.imp ph (.imp (synWo ps th) (synWo ch th))) :=
  by
  have p0000 := @gIdd ph th
  have p0001 := @gOrim12d ph ps ch th th hyp_orim1d_1 p0000
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_pm3_43`. -/
@[expose]
noncomputable def gPm343 (ph : Wff) (ps : Wff) (ch : Wff) :
    Nominal.NPrf (.imp (synWa (.imp ph ps) (.imp ph ch)) (.imp ph (synWa ps ch))) :=
  by
  have p0000 := @gPm343i ph ps ch
  have p0001 := @gImp (.imp ph ps) (.imp ph ch) (.imp ph (synWa ps ch)) p0000
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_jcab`. -/
@[expose]
noncomputable def gJcab (ph : Wff) (ps : Wff) (ch : Wff) :
    Nominal.NPrf (synWb (.imp ph (synWa ps ch)) (synWa (.imp ph ps) (.imp ph ch))) :=
  by
  have p0000 := @gSimpl ps ch
  have p0001 := @gImim2i (synWa ps ch) ps ph p0000
  have p0002 := @gSimpr ps ch
  have p0003 := @gImim2i (synWa ps ch) ch ph p0002
  have p0004 := @gJca (.imp ph (synWa ps ch)) (.imp ph ps) (.imp ph ch) p0001 p0003
  have p0005 := @gPm343 ph ps ch
  have p0006 :=
    @gImpbii (.imp ph (synWa ps ch)) (synWa (.imp ph ps) (.imp ph ch)) p0004 p0005
  exact p0006

/-- Checked nominal proof certificate identified upstream as `g_ordi`. -/
@[expose]
noncomputable def gOrdi (ph : Wff) (ps : Wff) (ch : Wff) :
    Nominal.NPrf
      (synWb (synWo ph (synWa ps ch)) (synWa (synWo ph ps) (synWo ph ch))) :=
  by
  have p0000 := @gJcab (.neg ph) ps ch
  have p0001 := (Nominal.biimpRefl (synWo ph (synWa ps ch)))
  have p0002 := (Nominal.biimpRefl (synWo ph ps))
  have p0003 := (Nominal.biimpRefl (synWo ph ch))
  have p0004 :=
    @gAnbi12i (synWo ph ps) (.imp (.neg ph) ps) (synWo ph ch) (.imp (.neg ph) ch) p0002
      p0003
  have p0005 :=
    @gN3bitr4i (.imp (.neg ph) (synWa ps ch))
      (synWa (.imp (.neg ph) ps) (.imp (.neg ph) ch)) (synWo ph (synWa ps ch))
      (synWa (synWo ph ps) (synWo ph ch)) p0000 p0001 p0004
  exact p0005

/-- Checked nominal proof certificate identified upstream as `g_andi`. -/
@[expose]
noncomputable def gAndi (ph : Wff) (ps : Wff) (ch : Wff) :
    Nominal.NPrf
      (synWb (synWa ph (synWo ps ch)) (synWo (synWa ph ps) (synWa ph ch))) :=
  by
  have p0000 := @gOrc (synWa ph ps) (synWa ph ch)
  have p0001 := @gOlc (synWa ph ch) (synWa ph ps)
  have p0002 := @gJaodan ph ps (synWo (synWa ph ps) (synWa ph ch)) ch p0000 p0001
  have p0003 := @gOrc ps ch
  have p0004 := @gAnim2i ps (synWo ps ch) ph p0003
  have p0005 := @gOlc ch ps
  have p0006 := @gAnim2i ch (synWo ps ch) ph p0005
  have p0007 :=
    @gJaoi (synWa ph ps) (synWa ph (synWo ps ch)) (synWa ph ch) p0004 p0006
  have p0008 :=
    @gImpbii (synWa ph (synWo ps ch)) (synWo (synWa ph ps) (synWa ph ch)) p0002
      p0007
  exact p0008

/-- Checked nominal proof certificate identified upstream as `g_andir`. -/
@[expose]
noncomputable def gAndir (ph : Wff) (ps : Wff) (ch : Wff) :
    Nominal.NPrf
      (synWb (synWa (synWo ph ps) ch) (synWo (synWa ph ch) (synWa ps ch))) :=
  by
  have p0000 := @gAndi ch ph ps
  have p0001 := @gAncom (synWo ph ps) ch
  have p0002 := @gAncom ph ch
  have p0003 := @gAncom ps ch
  have p0004 :=
    @gOrbi12i (synWa ph ch) (synWa ch ph) (synWa ps ch) (synWa ch ps) p0002 p0003
  have p0005 :=
    @gN3bitr4i (synWa ch (synWo ph ps)) (synWo (synWa ch ph) (synWa ch ps))
      (synWa (synWo ph ps) ch) (synWo (synWa ph ch) (synWa ps ch)) p0000 p0001 p0004
  exact p0005

/-- Checked nominal proof certificate identified upstream as `g_anddi`. -/
@[expose]
noncomputable def gAnddi (ph : Wff) (ps : Wff) (ch : Wff) (th : Wff) :
    Nominal.NPrf
      (synWb (synWa (synWo ph ps) (synWo ch th))
        (synWo (synWo (synWa ph ch) (synWa ph th))
          (synWo (synWa ps ch) (synWa ps th)))) :=
  by
  have p0000 := @gAndir ph ps (synWo ch th)
  have p0001 := @gAndi ph ch th
  have p0002 := @gAndi ps ch th
  have p0003 :=
    @gOrbi12i (synWa ph (synWo ch th)) (synWo (synWa ph ch) (synWa ph th))
      (synWa ps (synWo ch th)) (synWo (synWa ps ch) (synWa ps th)) p0001 p0002
  have p0004 :=
    @gBitri (synWa (synWo ph ps) (synWo ch th))
      (synWo (synWa ph (synWo ch th)) (synWa ps (synWo ch th)))
      (synWo (synWo (synWa ph ch) (synWa ph th)) (synWo (synWa ps ch) (synWa ps th)))
      p0000 p0003
  exact p0004

/-- Checked nominal proof certificate identified upstream as `g_bi2anan9`. -/
@[expose]
noncomputable def gBi2anan9 (ph : Wff) (ps : Wff) (ch : Wff) (th : Wff) (ta : Wff)
    (et : Wff) (hyp_bi2an9_1 : Nominal.NPrf (.imp ph (synWb ps ch)))
    (hyp_bi2an9_2 : Nominal.NPrf (.imp th (synWb ta et))) :
    Nominal.NPrf (.imp (synWa ph th) (synWb (synWa ps ta) (synWa ch et))) :=
  by
  have p0000 := @gAnbi1d ph ps ch ta hyp_bi2an9_1
  have p0001 := @gAnbi2d th ta et ch hyp_bi2an9_2
  have p0002 := @gSylan9bb ph (synWa ps ta) (synWa ch ta) th (synWa ch et) p0000 p0001
  exact p0002

/-- Checked nominal proof certificate identified upstream as `g_pm4_72`. -/
@[expose]
noncomputable def gPm472 (ph : Wff) (ps : Wff) :
    Nominal.NPrf (synWb (.imp ph ps) (synWb ps (synWo ph ps))) :=
  by
  have p0000 := @gOlc ps ph
  have p0001 := @gPm2621 ph ps
  have p0002 := @gImpbid2 (.imp ph ps) ps (synWo ph ps) p0000 p0001
  have p0003 := @gOrc ph ps
  have p0004 := @gBi2 ps (synWo ph ps)
  have p0005 := @gSyl5 ph (synWo ph ps) (synWb ps (synWo ph ps)) ps p0003 p0004
  have p0006 := @gImpbii (.imp ph ps) (synWb ps (synWo ph ps)) p0002 p0005
  exact p0006

/-- Checked nominal proof certificate identified upstream as `g_bianabs`. -/
@[expose]
noncomputable def gBianabs (ph : Wff) (ps : Wff) (ch : Wff)
    (hyp_bianabs_1 : Nominal.NPrf (.imp ph (synWb ps (synWa ph ch)))) :
    Nominal.NPrf (.imp ph (synWb ps ch)) :=
  by
  have p0000 := @gIbar ph ch
  have p0001 := @gBitr4d ph ps (synWa ph ch) ch hyp_bianabs_1 p0000
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_pm3_24`. -/
@[expose]
noncomputable def gPm324 (ph : Wff) : Nominal.NPrf (.neg (synWa ph (.neg ph))) :=
  by
  have p0000 := @gId ph
  have p0001 := @gIman ph ph
  have p0002 := @gMpbi (.imp ph ph) (.neg (synWa ph (.neg ph))) p0000 p0001
  exact p0002

/-- Checked nominal proof certificate identified upstream as `g_xor`. -/
@[expose]
noncomputable def gXor (ph : Wff) (ps : Wff) :
    Nominal.NPrf
      (synWb (.neg (synWb ph ps)) (synWo (synWa ph (.neg ps)) (synWa ps (.neg ph)))) :=
  by
  have p0000 := @gIman ph ps
  have p0001 := @gIman ps ph
  have p0002 :=
    @gAnbi12i (.imp ph ps) (.neg (synWa ph (.neg ps))) (.imp ps ph)
      (.neg (synWa ps (.neg ph))) p0000 p0001
  have p0003 := @gDfbi2 ph ps
  have p0004 := @gIoran (synWa ph (.neg ps)) (synWa ps (.neg ph))
  have p0005 :=
    @gN3bitr4ri (synWa (.imp ph ps) (.imp ps ph))
      (synWa (.neg (synWa ph (.neg ps))) (.neg (synWa ps (.neg ph)))) (synWb ph ps)
      (.neg (synWo (synWa ph (.neg ps)) (synWa ps (.neg ph)))) p0002 p0003 p0004
  have p0006 :=
    @gCon1bii (synWo (synWa ph (.neg ps)) (synWa ps (.neg ph))) (synWb ph ps) p0005
  exact p0006

/-- Checked nominal proof certificate identified upstream as `g_dfbi3`. -/
@[expose]
noncomputable def gDfbi3 (ph : Wff) (ps : Wff) :
    Nominal.NPrf
      (synWb (synWb ph ps) (synWo (synWa ph ps) (synWa (.neg ph) (.neg ps)))) :=
  by
  have p0000 := @gXor ph (.neg ps)
  have p0001 := @gPm518 ph ps
  have p0002 := @gNotnot ps
  have p0003 := @gAnbi2i ps (.neg (.neg ps)) ph p0002
  have p0004 := @gAncom (.neg ph) (.neg ps)
  have p0005 :=
    @gOrbi12i (synWa ph ps) (synWa ph (.neg (.neg ps))) (synWa (.neg ph) (.neg ps))
      (synWa (.neg ps) (.neg ph)) p0003 p0004
  have p0006 :=
    @gN3bitr4i (.neg (synWb ph (.neg ps)))
      (synWo (synWa ph (.neg (.neg ps))) (synWa (.neg ps) (.neg ph))) (synWb ph ps)
      (synWo (synWa ph ps) (synWa (.neg ph) (.neg ps))) p0000 p0001 p0005
  exact p0006

/-- Checked nominal proof certificate identified upstream as `g_xordi`. -/
@[expose]
noncomputable def gXordi (ph : Wff) (ps : Wff) (ch : Wff) :
    Nominal.NPrf
      (synWb (synWa ph (.neg (synWb ps ch)))
        (.neg (synWb (synWa ph ps) (synWa ph ch)))) :=
  by
  have p0000 := @gAnnim ph (synWb ps ch)
  have p0001 := @gPm532 ph ps ch
  have p0002 :=
    @gXchbinx (synWa ph (.neg (synWb ps ch))) (.imp ph (synWb ps ch))
      (synWb (synWa ph ps) (synWa ph ch)) p0000 p0001
  exact p0002

/-- Checked nominal proof certificate identified upstream as `g_pm5_21nd`. -/
@[expose]
noncomputable def gPm521nd (ph : Wff) (ps : Wff) (ch : Wff) (th : Wff)
    (hyp_pm5_21nd_1 : Nominal.NPrf (.imp (synWa ph ps) th))
    (hyp_pm5_21nd_2 : Nominal.NPrf (.imp (synWa ph ch) th))
    (hyp_pm5_21nd_3 : Nominal.NPrf (.imp th (synWb ps ch))) :
    Nominal.NPrf (.imp ph (synWb ps ch)) :=
  by
  have p0000 := @gEx ph ps th hyp_pm5_21nd_1
  have p0001 := @gEx ph ch th hyp_pm5_21nd_2
  have p0002 := @gA1i (.imp th (synWb ps ch)) ph hyp_pm5_21nd_3
  have p0003 := @gPm521ndd ph th ps ch p0000 p0001 p0002
  exact p0003

/-- Checked nominal proof certificate identified upstream as `g_baib`. -/
@[expose]
noncomputable def gBaib (ph : Wff) (ps : Wff) (ch : Wff)
    (hyp_baib_1 : Nominal.NPrf (synWb ph (synWa ps ch))) :
    Nominal.NPrf (.imp ps (synWb ph ch)) :=
  by
  have p0000 := @gIbar ps ch
  have p0001 := @gSyl6rbbr ps ch (synWa ps ch) ph p0000 hyp_baib_1
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_baibr`. -/
@[expose]
noncomputable def gBaibr (ph : Wff) (ps : Wff) (ch : Wff)
    (hyp_baib_1 : Nominal.NPrf (synWb ph (synWa ps ch))) :
    Nominal.NPrf (.imp ps (synWb ch ph)) :=
  by
  have p0000 := @gBaib ph ps ch hyp_baib_1
  have p0001 := @gBicomd ps ph ch p0000
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_pm5_6`. -/
@[expose]
noncomputable def gPm56 (ph : Wff) (ps : Wff) (ch : Wff) :
    Nominal.NPrf (synWb (.imp (synWa ph (.neg ps)) ch) (.imp ph (synWo ps ch))) :=
  by
  have p0000 := @gImpexp ph (.neg ps) ch
  have p0001 := (Nominal.biimpRefl (synWo ps ch))
  have p0002 := @gImbi2i (synWo ps ch) (.imp (.neg ps) ch) ph p0001
  have p0003 :=
    @gBitr4i (.imp (synWa ph (.neg ps)) ch) (.imp ph (.imp (.neg ps) ch))
      (.imp ph (synWo ps ch)) p0000 p0002
  exact p0003

/-- Checked nominal proof certificate identified upstream as `g_orcanai`. -/
@[expose]
noncomputable def gOrcanai (ph : Wff) (ps : Wff) (ch : Wff)
    (hyp_orcanai_1 : Nominal.NPrf (.imp ph (synWo ps ch))) :
    Nominal.NPrf (.imp (synWa ph (.neg ps)) ch) :=
  by
  have p0000 := @gOrd ph ps ch hyp_orcanai_1
  have p0001 := @gImp ph (.neg ps) ch p0000
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_intnan`. -/
@[expose]
noncomputable def gIntnan (ph : Wff) (ps : Wff) (hyp_intnan_1 : Nominal.NPrf (.neg ph)) :
    Nominal.NPrf (.neg (synWa ps ph)) :=
  by
  have p0000 := @gSimpr ps ph
  have p0001 := @gMto (synWa ps ph) ph hyp_intnan_1 p0000
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_intnanr`. -/
@[expose]
noncomputable def gIntnanr (ph : Wff) (ps : Wff)
    (hyp_intnan_1 : Nominal.NPrf (.neg ph)) : Nominal.NPrf (.neg (synWa ph ps)) :=
  by
  have p0000 := @gSimpl ph ps
  have p0001 := @gMto (synWa ph ps) ph hyp_intnan_1 p0000
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_intnand`. -/
@[expose]
noncomputable def gIntnand (ph : Wff) (ps : Wff) (ch : Wff)
    (hyp_intnand_1 : Nominal.NPrf (.imp ph (.neg ps))) :
    Nominal.NPrf (.imp ph (.neg (synWa ch ps))) :=
  by
  have p0000 := @gSimpr ch ps
  have p0001 := @gNsyl ph ps (synWa ch ps) hyp_intnand_1 p0000
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_intnanrd`. -/
@[expose]
noncomputable def gIntnanrd (ph : Wff) (ps : Wff) (ch : Wff)
    (hyp_intnand_1 : Nominal.NPrf (.imp ph (.neg ps))) :
    Nominal.NPrf (.imp ph (.neg (synWa ps ch))) :=
  by
  have p0000 := @gSimpl ps ch
  have p0001 := @gNsyl ph ps (synWa ps ch) hyp_intnand_1 p0000
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_mpbiran`. -/
@[expose]
noncomputable def gMpbiran (ph : Wff) (ps : Wff) (ch : Wff)
    (hyp_mpbiran_1 : Nominal.NPrf ps)
    (hyp_mpbiran_2 : Nominal.NPrf (synWb ph (synWa ps ch))) :
    Nominal.NPrf (synWb ph ch) :=
  by
  have p0000 := @gBiantrur ps ch hyp_mpbiran_1
  have p0001 := @gBitr4i ph (synWa ps ch) ch hyp_mpbiran_2 p0000
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_mpbiran2`. -/
@[expose]
noncomputable def gMpbiran2 (ph : Wff) (ps : Wff) (ch : Wff)
    (hyp_mpbiran2_1 : Nominal.NPrf ch)
    (hyp_mpbiran2_2 : Nominal.NPrf (synWb ph (synWa ps ch))) :
    Nominal.NPrf (synWb ph ps) :=
  by
  have p0000 := @gBiantru ch ps hyp_mpbiran2_1
  have p0001 := @gBitr4i ph (synWa ps ch) ps hyp_mpbiran2_2 p0000
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_mpbir2an`. -/
@[expose]
noncomputable def gMpbir2an (ph : Wff) (ps : Wff) (ch : Wff)
    (hyp_mpbir2an_1 : Nominal.NPrf ps) (hyp_mpbir2an_2 : Nominal.NPrf ch)
    (hyp_mpbiran2an_1 : Nominal.NPrf (synWb ph (synWa ps ch))) : Nominal.NPrf ph :=
  by
  have p0000 := @gMpbiran ph ps ch hyp_mpbir2an_1 hyp_mpbiran2an_1
  have p0001 := @gMpbir ph ch hyp_mpbir2an_2 p0000
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_bianfi`. -/
@[expose]
noncomputable def gBianfi (ph : Wff) (ps : Wff) (hyp_bianfi_1 : Nominal.NPrf (.neg ph)) :
    Nominal.NPrf (synWb ph (synWa ps ph)) :=
  by
  have p0000 := @gIntnan ph ps hyp_bianfi_1
  have p0001 := @gN2false ph (synWa ps ph) hyp_bianfi_1 p0000
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_ecase3`. -/
@[expose]
noncomputable def gEcase3 (ph : Wff) (ps : Wff) (ch : Wff)
    (hyp_ecase3_1 : Nominal.NPrf (.imp ph ch)) (hyp_ecase3_2 : Nominal.NPrf (.imp ps ch))
    (hyp_ecase3_3 : Nominal.NPrf (.imp (.neg (synWo ph ps)) ch)) : Nominal.NPrf ch :=
  by
  have p0000 := @gJaoi ph ch ps hyp_ecase3_1 hyp_ecase3_2
  have p0001 := @gPm261i (synWo ph ps) ch p0000 hyp_ecase3_3
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_dedlem0a`. -/
@[expose]
noncomputable def gDedlem0a (ph : Wff) (ps : Wff) (ch : Wff) :
    Nominal.NPrf (.imp ph (synWb ps (.imp (.imp ch ph) (synWa ps ph)))) :=
  by
  have p0000 := @gIba ph ps
  have p0001 := Nominal.ax1 ph ch
  have p0002 := @gBiimt (.imp ch ph) (synWa ps ph)
  have p0003 :=
    @gSyl ph (.imp ch ph) (synWb (synWa ps ph) (.imp (.imp ch ph) (synWa ps ph)))
      p0001 p0002
  have p0004 :=
    @gBitrd ph ps (synWa ps ph) (.imp (.imp ch ph) (synWa ps ph)) p0000 p0003
  exact p0004

/-- Checked nominal proof certificate identified upstream as `g_dedlema`. -/
@[expose]
noncomputable def gDedlema (ph : Wff) (ps : Wff) (ch : Wff) :
    Nominal.NPrf (.imp ph (synWb ps (synWo (synWa ps ph) (synWa ch (.neg ph))))) :=
  by
  have p0000 := @gOrc (synWa ps ph) (synWa ch (.neg ph))
  have p0001 := @gExpcom ps ph (synWo (synWa ps ph) (synWa ch (.neg ph))) p0000
  have p0002 := @gSimpl ps ph
  have p0003 := @gA1i (.imp (synWa ps ph) ps) ph p0002
  have p0004 := @gPm224 ph ps
  have p0005 := @gAdantld ph (.neg ph) ps ch p0004
  have p0006 := @gJaod ph (synWa ps ph) ps (synWa ch (.neg ph)) p0003 p0005
  have p0007 := @gImpbid ph ps (synWo (synWa ps ph) (synWa ch (.neg ph))) p0001 p0006
  exact p0007

/-- Checked nominal proof certificate identified upstream as `g_dedlemb`. -/
@[expose]
noncomputable def gDedlemb (ph : Wff) (ps : Wff) (ch : Wff) :
    Nominal.NPrf
      (.imp (.neg ph) (synWb ch (synWo (synWa ps ph) (synWa ch (.neg ph))))) :=
  by
  have p0000 := @gOlc (synWa ch (.neg ph)) (synWa ps ph)
  have p0001 := @gExpcom ch (.neg ph) (synWo (synWa ps ph) (synWa ch (.neg ph))) p0000
  have p0002 := @gPm221 ph ch
  have p0003 := @gAdantld (.neg ph) ph ch ps p0002
  have p0004 := @gSimpl ch (.neg ph)
  have p0005 := @gA1i (.imp (synWa ch (.neg ph)) ch) (.neg ph) p0004
  have p0006 := @gJaod (.neg ph) (synWa ps ph) ch (synWa ch (.neg ph)) p0003 p0005
  have p0007 :=
    @gImpbid (.neg ph) ch (synWo (synWa ps ph) (synWa ch (.neg ph))) p0001 p0006
  exact p0007

/-- Checked nominal proof certificate identified upstream as `g_pm4_42`. -/
@[expose]
noncomputable def gPm442 (ph : Wff) (ps : Wff) :
    Nominal.NPrf (synWb ph (synWo (synWa ph ps) (synWa ph (.neg ps)))) :=
  by
  have p0000 := @gDedlema ps ph ph
  have p0001 := @gDedlemb ps ph ph
  have p0002 :=
    @gPm261i ps (synWb ph (synWo (synWa ph ps) (synWa ph (.neg ps)))) p0000 p0001
  exact p0002

/-- Checked nominal proof certificate identified upstream as `g_oplem1`. -/
@[expose]
noncomputable def gOplem1 (ph : Wff) (ps : Wff) (ch : Wff) (th : Wff) (ta : Wff)
    (hyp_oplem1_1 : Nominal.NPrf (.imp ph (synWo ps ch)))
    (hyp_oplem1_2 : Nominal.NPrf (.imp ph (synWo th ta)))
    (hyp_oplem1_3 : Nominal.NPrf (synWb ps th))
    (hyp_oplem1_4 : Nominal.NPrf (.imp ch (synWb th ta))) : Nominal.NPrf (.imp ph ps) :=
  by
  have p0000 := @gNotbii ps th hyp_oplem1_3
  have p0001 := @gOrd ph ps ch hyp_oplem1_1
  have p0002 := @gSyl5bir (.neg th) (.neg ps) ph ch p0000 p0001
  have p0003 := @gOrd ph th ta hyp_oplem1_2
  have p0004 := @gJcad ph (.neg th) ch ta p0002 p0003
  have p0005 := @gBiimpar ch th ta hyp_oplem1_4
  have p0006 := @gSyl6 ph (.neg th) (synWa ch ta) th p0004 p0005
  have p0007 := @gPm218d ph th p0006
  have p0008 := @gSylibr ph th ps p0007 hyp_oplem1_3
  exact p0008

/-- Checked nominal proof certificate identified upstream as `g_n_3orass`. -/
@[expose]
noncomputable def gN3orass (ph : Wff) (ps : Wff) (ch : Wff) :
    Nominal.NPrf (synWb (synW3o ph ps ch) (synWo ph (synWo ps ch))) :=
  by
  have p0000 := (Nominal.biimpRefl (synW3o ph ps ch))
  have p0001 := @gOrass ph ps ch
  have p0002 :=
    @gBitri (synW3o ph ps ch) (synWo (synWo ph ps) ch) (synWo ph (synWo ps ch))
      p0000 p0001
  exact p0002

/-- Checked nominal proof certificate identified upstream as `g_n_3anass`. -/
@[expose]
noncomputable def gN3anass (ph : Wff) (ps : Wff) (ch : Wff) :
    Nominal.NPrf (synWb (synW3a ph ps ch) (synWa ph (synWa ps ch))) :=
  by
  have p0000 := (Nominal.biimpRefl (synW3a ph ps ch))
  have p0001 := @gAnass ph ps ch
  have p0002 :=
    @gBitri (synW3a ph ps ch) (synWa (synWa ph ps) ch) (synWa ph (synWa ps ch))
      p0000 p0001
  exact p0002

/-- Checked nominal proof certificate identified upstream as `g_n_3anrot`. -/
@[expose]
noncomputable def gN3anrot (ph : Wff) (ps : Wff) (ch : Wff) :
    Nominal.NPrf (synWb (synW3a ph ps ch) (synW3a ps ch ph)) :=
  by
  have p0000 := @gAncom ph (synWa ps ch)
  have p0001 := @gN3anass ph ps ch
  have p0002 := (Nominal.biimpRefl (synW3a ps ch ph))
  have p0003 :=
    @gN3bitr4i (synWa ph (synWa ps ch)) (synWa (synWa ps ch) ph) (synW3a ph ps ch)
      (synW3a ps ch ph) p0000 p0001 p0002
  exact p0003

/-- Checked nominal proof certificate identified upstream as `g_n_3orrot`. -/
@[expose]
noncomputable def gN3orrot (ph : Wff) (ps : Wff) (ch : Wff) :
    Nominal.NPrf (synWb (synW3o ph ps ch) (synW3o ps ch ph)) :=
  by
  have p0000 := @gOrcom ph (synWo ps ch)
  have p0001 := @gN3orass ph ps ch
  have p0002 := (Nominal.biimpRefl (synW3o ps ch ph))
  have p0003 :=
    @gN3bitr4i (synWo ph (synWo ps ch)) (synWo (synWo ps ch) ph) (synW3o ph ps ch)
      (synW3o ps ch ph) p0000 p0001 p0002
  exact p0003

/-- Checked nominal proof certificate identified upstream as `g_n_3ancoma`. -/
@[expose]
noncomputable def gN3ancoma (ph : Wff) (ps : Wff) (ch : Wff) :
    Nominal.NPrf (synWb (synW3a ph ps ch) (synW3a ps ph ch)) :=
  by
  have p0000 := @gAncom ph ps
  have p0001 := @gAnbi1i (synWa ph ps) (synWa ps ph) ch p0000
  have p0002 := (Nominal.biimpRefl (synW3a ph ps ch))
  have p0003 := (Nominal.biimpRefl (synW3a ps ph ch))
  have p0004 :=
    @gN3bitr4i (synWa (synWa ph ps) ch) (synWa (synWa ps ph) ch) (synW3a ph ps ch)
      (synW3a ps ph ch) p0001 p0002 p0003
  exact p0004

/-- Checked nominal proof certificate identified upstream as `g_n_3ancomb`. -/
@[expose]
noncomputable def gN3ancomb (ph : Wff) (ps : Wff) (ch : Wff) :
    Nominal.NPrf (synWb (synW3a ph ps ch) (synW3a ph ch ps)) :=
  by
  have p0000 := @gN3ancoma ph ps ch
  have p0001 := @gN3anrot ps ph ch
  have p0002 :=
    @gBitri (synW3a ph ps ch) (synW3a ps ph ch) (synW3a ph ch ps) p0000 p0001
  exact p0002

/-- Checked nominal proof certificate identified upstream as `g_n_3anrev`. -/
@[expose]
noncomputable def gN3anrev (ph : Wff) (ps : Wff) (ch : Wff) :
    Nominal.NPrf (synWb (synW3a ph ps ch) (synW3a ch ps ph)) :=
  by
  have p0000 := @gN3ancoma ph ps ch
  have p0001 := @gN3anrot ch ps ph
  have p0002 :=
    @gBitr4i (synW3a ph ps ch) (synW3a ps ph ch) (synW3a ch ps ph) p0000 p0001
  exact p0002

/-- Checked nominal proof certificate identified upstream as `g_n_3simpa`. -/
@[expose]
noncomputable def gN3simpa (ph : Wff) (ps : Wff) (ch : Wff) :
    Nominal.NPrf (.imp (synW3a ph ps ch) (synWa ph ps)) :=
  by
  have p0000 := (Nominal.biimpRefl (synW3a ph ps ch))
  have p0001 := @gSimplbi (synW3a ph ps ch) (synWa ph ps) ch p0000
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_n_3simpb`. -/
@[expose]
noncomputable def gN3simpb (ph : Wff) (ps : Wff) (ch : Wff) :
    Nominal.NPrf (.imp (synW3a ph ps ch) (synWa ph ch)) :=
  by
  have p0000 := @gN3ancomb ph ps ch
  have p0001 := @gN3simpa ph ch ps
  have p0002 := @gSylbi (synW3a ph ps ch) (synW3a ph ch ps) (synWa ph ch) p0000 p0001
  exact p0002

/-- Checked nominal proof certificate identified upstream as `g_n_3simpc`. -/
@[expose]
noncomputable def gN3simpc (ph : Wff) (ps : Wff) (ch : Wff) :
    Nominal.NPrf (.imp (synW3a ph ps ch) (synWa ps ch)) :=
  by
  have p0000 := @gN3anrot ph ps ch
  have p0001 := @gN3simpa ps ch ph
  have p0002 := @gSylbi (synW3a ph ps ch) (synW3a ps ch ph) (synWa ps ch) p0000 p0001
  exact p0002

/-- Checked nominal proof certificate identified upstream as `g_simp1`. -/
@[expose]
noncomputable def gSimp1 (ph : Wff) (ps : Wff) (ch : Wff) :
    Nominal.NPrf (.imp (synW3a ph ps ch) ph) :=
  by
  have p0000 := @gN3simpa ph ps ch
  have p0001 := @gSimpld (synW3a ph ps ch) ph ps p0000
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_simp2`. -/
@[expose]
noncomputable def gSimp2 (ph : Wff) (ps : Wff) (ch : Wff) :
    Nominal.NPrf (.imp (synW3a ph ps ch) ps) :=
  by
  have p0000 := @gN3simpa ph ps ch
  have p0001 := @gSimprd (synW3a ph ps ch) ph ps p0000
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_simp3`. -/
@[expose]
noncomputable def gSimp3 (ph : Wff) (ps : Wff) (ch : Wff) :
    Nominal.NPrf (.imp (synW3a ph ps ch) ch) :=
  by
  have p0000 := @gN3simpc ph ps ch
  have p0001 := @gSimprd (synW3a ph ps ch) ps ch p0000
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_simpl1`. -/
@[expose]
noncomputable def gSimpl1 (ph : Wff) (ps : Wff) (ch : Wff) (th : Wff) :
    Nominal.NPrf (.imp (synWa (synW3a ph ps ch) th) ph) :=
  by
  have p0000 := @gSimp1 ph ps ch
  have p0001 := @gAdantr (synW3a ph ps ch) ph th p0000
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_simpl2`. -/
@[expose]
noncomputable def gSimpl2 (ph : Wff) (ps : Wff) (ch : Wff) (th : Wff) :
    Nominal.NPrf (.imp (synWa (synW3a ph ps ch) th) ps) :=
  by
  have p0000 := @gSimp2 ph ps ch
  have p0001 := @gAdantr (synW3a ph ps ch) ps th p0000
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_simpl3`. -/
@[expose]
noncomputable def gSimpl3 (ph : Wff) (ps : Wff) (ch : Wff) (th : Wff) :
    Nominal.NPrf (.imp (synWa (synW3a ph ps ch) th) ch) :=
  by
  have p0000 := @gSimp3 ph ps ch
  have p0001 := @gAdantr (synW3a ph ps ch) ch th p0000
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_simpr1`. -/
@[expose]
noncomputable def gSimpr1 (ph : Wff) (ps : Wff) (ch : Wff) (th : Wff) :
    Nominal.NPrf (.imp (synWa ph (synW3a ps ch th)) ps) :=
  by
  have p0000 := @gSimp1 ps ch th
  have p0001 := @gAdantl (synW3a ps ch th) ps ph p0000
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_simp1d`. -/
@[expose]
noncomputable def gSimp1d (ph : Wff) (ps : Wff) (ch : Wff) (th : Wff)
    (hyp_n_3simp1d_1 : Nominal.NPrf (.imp ph (synW3a ps ch th))) :
    Nominal.NPrf (.imp ph ps) :=
  by
  have p0000 := @gSimp1 ps ch th
  have p0001 := @gSyl ph (synW3a ps ch th) ps hyp_n_3simp1d_1 p0000
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_simp2d`. -/
@[expose]
noncomputable def gSimp2d (ph : Wff) (ps : Wff) (ch : Wff) (th : Wff)
    (hyp_n_3simp1d_1 : Nominal.NPrf (.imp ph (synW3a ps ch th))) :
    Nominal.NPrf (.imp ph ch) :=
  by
  have p0000 := @gSimp2 ps ch th
  have p0001 := @gSyl ph (synW3a ps ch th) ch hyp_n_3simp1d_1 p0000
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_simp3d`. -/
@[expose]
noncomputable def gSimp3d (ph : Wff) (ps : Wff) (ch : Wff) (th : Wff)
    (hyp_n_3simp1d_1 : Nominal.NPrf (.imp ph (synW3a ps ch th))) :
    Nominal.NPrf (.imp ph th) :=
  by
  have p0000 := @gSimp3 ps ch th
  have p0001 := @gSyl ph (synW3a ps ch th) th hyp_n_3simp1d_1 p0000
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_simp1bi`. -/
@[expose]
noncomputable def gSimp1bi (ph : Wff) (ps : Wff) (ch : Wff) (th : Wff)
    (hyp_n_3simp1bi_1 : Nominal.NPrf (synWb ph (synW3a ps ch th))) :
    Nominal.NPrf (.imp ph ps) :=
  by
  have p0000 := @gBiimpi ph (synW3a ps ch th) hyp_n_3simp1bi_1
  have p0001 := @gSimp1d ph ps ch th p0000
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_simp2bi`. -/
@[expose]
noncomputable def gSimp2bi (ph : Wff) (ps : Wff) (ch : Wff) (th : Wff)
    (hyp_n_3simp1bi_1 : Nominal.NPrf (synWb ph (synW3a ps ch th))) :
    Nominal.NPrf (.imp ph ch) :=
  by
  have p0000 := @gBiimpi ph (synW3a ps ch th) hyp_n_3simp1bi_1
  have p0001 := @gSimp2d ph ps ch th p0000
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_simp3bi`. -/
@[expose]
noncomputable def gSimp3bi (ph : Wff) (ps : Wff) (ch : Wff) (th : Wff)
    (hyp_n_3simp1bi_1 : Nominal.NPrf (synWb ph (synW3a ps ch th))) :
    Nominal.NPrf (.imp ph th) :=
  by
  have p0000 := @gBiimpi ph (synW3a ps ch th) hyp_n_3simp1bi_1
  have p0001 := @gSimp3d ph ps ch th p0000
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_n_3adant1`. -/
@[expose]
noncomputable def gN3adant1 (ph : Wff) (ps : Wff) (ch : Wff) (th : Wff)
    (hyp_n_3adant_1 : Nominal.NPrf (.imp (synWa ph ps) ch)) :
    Nominal.NPrf (.imp (synW3a th ph ps) ch) :=
  by
  have p0000 := @gN3simpc th ph ps
  have p0001 := @gSyl (synW3a th ph ps) (synWa ph ps) ch p0000 hyp_n_3adant_1
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_n_3adant2`. -/
@[expose]
noncomputable def gN3adant2 (ph : Wff) (ps : Wff) (ch : Wff) (th : Wff)
    (hyp_n_3adant_1 : Nominal.NPrf (.imp (synWa ph ps) ch)) :
    Nominal.NPrf (.imp (synW3a ph th ps) ch) :=
  by
  have p0000 := @gN3simpb ph th ps
  have p0001 := @gSyl (synW3a ph th ps) (synWa ph ps) ch p0000 hyp_n_3adant_1
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_n_3adant3`. -/
@[expose]
noncomputable def gN3adant3 (ph : Wff) (ps : Wff) (ch : Wff) (th : Wff)
    (hyp_n_3adant_1 : Nominal.NPrf (.imp (synWa ph ps) ch)) :
    Nominal.NPrf (.imp (synW3a ph ps th) ch) :=
  by
  have p0000 := @gN3simpa ph ps th
  have p0001 := @gSyl (synW3a ph ps th) (synWa ph ps) ch p0000 hyp_n_3adant_1
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_n_3ad2ant1`. -/
@[expose]
noncomputable def gN3ad2ant1 (ph : Wff) (ps : Wff) (ch : Wff) (th : Wff)
    (hyp_n_3ad2ant_1 : Nominal.NPrf (.imp ph ch)) :
    Nominal.NPrf (.imp (synW3a ph ps th) ch) :=
  by
  have p0000 := @gAdantr ph ch th hyp_n_3ad2ant_1
  have p0001 := @gN3adant2 ph th ch ps p0000
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_n_3ad2ant2`. -/
@[expose]
noncomputable def gN3ad2ant2 (ph : Wff) (ps : Wff) (ch : Wff) (th : Wff)
    (hyp_n_3ad2ant_1 : Nominal.NPrf (.imp ph ch)) :
    Nominal.NPrf (.imp (synW3a ps ph th) ch) :=
  by
  have p0000 := @gAdantr ph ch th hyp_n_3ad2ant_1
  have p0001 := @gN3adant1 ph th ch ps p0000
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_n_3ad2ant3`. -/
@[expose]
noncomputable def gN3ad2ant3 (ph : Wff) (ps : Wff) (ch : Wff) (th : Wff)
    (hyp_n_3ad2ant_1 : Nominal.NPrf (.imp ph ch)) :
    Nominal.NPrf (.imp (synW3a ps th ph) ch) :=
  by
  have p0000 := @gAdantl ph ch th hyp_n_3ad2ant_1
  have p0001 := @gN3adant1 th ph ch ps p0000
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_simp1l`. -/
@[expose]
noncomputable def gSimp1l (ph : Wff) (ps : Wff) (ch : Wff) (th : Wff) :
    Nominal.NPrf (.imp (synW3a (synWa ph ps) ch th) ph) :=
  by
  have p0000 := @gSimpl ph ps
  have p0001 := @gN3ad2ant1 (synWa ph ps) ch ph th p0000
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_simp1r`. -/
@[expose]
noncomputable def gSimp1r (ph : Wff) (ps : Wff) (ch : Wff) (th : Wff) :
    Nominal.NPrf (.imp (synW3a (synWa ph ps) ch th) ps) :=
  by
  have p0000 := @gSimpr ph ps
  have p0001 := @gN3ad2ant1 (synWa ph ps) ch ps th p0000
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_simp2l`. -/
@[expose]
noncomputable def gSimp2l (ph : Wff) (ps : Wff) (ch : Wff) (th : Wff) :
    Nominal.NPrf (.imp (synW3a ph (synWa ps ch) th) ps) :=
  by
  have p0000 := @gSimpl ps ch
  have p0001 := @gN3ad2ant2 (synWa ps ch) ph ps th p0000
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_simp2r`. -/
@[expose]
noncomputable def gSimp2r (ph : Wff) (ps : Wff) (ch : Wff) (th : Wff) :
    Nominal.NPrf (.imp (synW3a ph (synWa ps ch) th) ch) :=
  by
  have p0000 := @gSimpr ps ch
  have p0001 := @gN3ad2ant2 (synWa ps ch) ph ch th p0000
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_simp3l`. -/
@[expose]
noncomputable def gSimp3l (ph : Wff) (ps : Wff) (ch : Wff) (th : Wff) :
    Nominal.NPrf (.imp (synW3a ph ps (synWa ch th)) ch) :=
  by
  have p0000 := @gSimpl ch th
  have p0001 := @gN3ad2ant3 (synWa ch th) ph ch ps p0000
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_simp3r`. -/
@[expose]
noncomputable def gSimp3r (ph : Wff) (ps : Wff) (ch : Wff) (th : Wff) :
    Nominal.NPrf (.imp (synW3a ph ps (synWa ch th)) th) :=
  by
  have p0000 := @gSimpr ch th
  have p0001 := @gN3ad2ant3 (synWa ch th) ph th ps p0000
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_simp21`. -/
@[expose]
noncomputable def gSimp21 (ph : Wff) (ps : Wff) (ch : Wff) (th : Wff) (ta : Wff) :
    Nominal.NPrf (.imp (synW3a ph (synW3a ps ch th) ta) ps) :=
  by
  have p0000 := @gSimp1 ps ch th
  have p0001 := @gN3ad2ant2 (synW3a ps ch th) ph ps ta p0000
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_simp23`. -/
@[expose]
noncomputable def gSimp23 (ph : Wff) (ps : Wff) (ch : Wff) (th : Wff) (ta : Wff) :
    Nominal.NPrf (.imp (synW3a ph (synW3a ps ch th) ta) th) :=
  by
  have p0000 := @gSimp3 ps ch th
  have p0001 := @gN3ad2ant2 (synW3a ps ch th) ph th ta p0000
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_simp31`. -/
@[expose]
noncomputable def gSimp31 (ph : Wff) (ps : Wff) (ch : Wff) (th : Wff) (ta : Wff) :
    Nominal.NPrf (.imp (synW3a ph ps (synW3a ch th ta)) ch) :=
  by
  have p0000 := @gSimp1 ch th ta
  have p0001 := @gN3ad2ant3 (synW3a ch th ta) ph ch ps p0000
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_simp32`. -/
@[expose]
noncomputable def gSimp32 (ph : Wff) (ps : Wff) (ch : Wff) (th : Wff) (ta : Wff) :
    Nominal.NPrf (.imp (synW3a ph ps (synW3a ch th ta)) th) :=
  by
  have p0000 := @gSimp2 ch th ta
  have p0001 := @gN3ad2ant3 (synW3a ch th ta) ph th ps p0000
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_simp33`. -/
@[expose]
noncomputable def gSimp33 (ph : Wff) (ps : Wff) (ch : Wff) (th : Wff) (ta : Wff) :
    Nominal.NPrf (.imp (synW3a ph ps (synW3a ch th ta)) ta) :=
  by
  have p0000 := @gSimp3 ch th ta
  have p0001 := @gN3ad2ant3 (synW3a ch th ta) ph ta ps p0000
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_simpl1l`. -/
@[expose]
noncomputable def gSimpl1l (ph : Wff) (ps : Wff) (ch : Wff) (th : Wff) (ta : Wff) :
    Nominal.NPrf (.imp (synWa (synW3a (synWa ph ps) ch th) ta) ph) :=
  by
  have p0000 := @gSimp1l ph ps ch th
  have p0001 := @gAdantr (synW3a (synWa ph ps) ch th) ph ta p0000
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_simpl1r`. -/
@[expose]
noncomputable def gSimpl1r (ph : Wff) (ps : Wff) (ch : Wff) (th : Wff) (ta : Wff) :
    Nominal.NPrf (.imp (synWa (synW3a (synWa ph ps) ch th) ta) ps) :=
  by
  have p0000 := @gSimp1r ph ps ch th
  have p0001 := @gAdantr (synW3a (synWa ph ps) ch th) ps ta p0000
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_simpl2l`. -/
@[expose]
noncomputable def gSimpl2l (ph : Wff) (ps : Wff) (ch : Wff) (th : Wff) (ta : Wff) :
    Nominal.NPrf (.imp (synWa (synW3a ch (synWa ph ps) th) ta) ph) :=
  by
  have p0000 := @gSimp2l ch ph ps th
  have p0001 := @gAdantr (synW3a ch (synWa ph ps) th) ph ta p0000
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_simpl2r`. -/
@[expose]
noncomputable def gSimpl2r (ph : Wff) (ps : Wff) (ch : Wff) (th : Wff) (ta : Wff) :
    Nominal.NPrf (.imp (synWa (synW3a ch (synWa ph ps) th) ta) ps) :=
  by
  have p0000 := @gSimp2r ch ph ps th
  have p0001 := @gAdantr (synW3a ch (synWa ph ps) th) ps ta p0000
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_simpl3l`. -/
@[expose]
noncomputable def gSimpl3l (ph : Wff) (ps : Wff) (ch : Wff) (th : Wff) (ta : Wff) :
    Nominal.NPrf (.imp (synWa (synW3a ch th (synWa ph ps)) ta) ph) :=
  by
  have p0000 := @gSimp3l ch th ph ps
  have p0001 := @gAdantr (synW3a ch th (synWa ph ps)) ph ta p0000
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_simpl3r`. -/
@[expose]
noncomputable def gSimpl3r (ph : Wff) (ps : Wff) (ch : Wff) (th : Wff) (ta : Wff) :
    Nominal.NPrf (.imp (synWa (synW3a ch th (synWa ph ps)) ta) ps) :=
  by
  have p0000 := @gSimp3r ch th ph ps
  have p0001 := @gAdantr (synW3a ch th (synWa ph ps)) ps ta p0000
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_simpr2l`. -/
@[expose]
noncomputable def gSimpr2l (ph : Wff) (ps : Wff) (ch : Wff) (th : Wff) (ta : Wff) :
    Nominal.NPrf (.imp (synWa ta (synW3a ch (synWa ph ps) th)) ph) :=
  by
  have p0000 := @gSimp2l ch ph ps th
  have p0001 := @gAdantl (synW3a ch (synWa ph ps) th) ph ta p0000
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_simpr2r`. -/
@[expose]
noncomputable def gSimpr2r (ph : Wff) (ps : Wff) (ch : Wff) (th : Wff) (ta : Wff) :
    Nominal.NPrf (.imp (synWa ta (synW3a ch (synWa ph ps) th)) ps) :=
  by
  have p0000 := @gSimp2r ch ph ps th
  have p0001 := @gAdantl (synW3a ch (synWa ph ps) th) ps ta p0000
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_simpr3l`. -/
@[expose]
noncomputable def gSimpr3l (ph : Wff) (ps : Wff) (ch : Wff) (th : Wff) (ta : Wff) :
    Nominal.NPrf (.imp (synWa ta (synW3a ch th (synWa ph ps))) ph) :=
  by
  have p0000 := @gSimp3l ch th ph ps
  have p0001 := @gAdantl (synW3a ch th (synWa ph ps)) ph ta p0000
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_simpr3r`. -/
@[expose]
noncomputable def gSimpr3r (ph : Wff) (ps : Wff) (ch : Wff) (th : Wff) (ta : Wff) :
    Nominal.NPrf (.imp (synWa ta (synW3a ch th (synWa ph ps))) ps) :=
  by
  have p0000 := @gSimp3r ch th ph ps
  have p0001 := @gAdantl (synW3a ch th (synWa ph ps)) ps ta p0000
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_simp1rl`. -/
@[expose]
noncomputable def gSimp1rl (ph : Wff) (ps : Wff) (ch : Wff) (th : Wff) (ta : Wff) :
    Nominal.NPrf (.imp (synW3a (synWa ch (synWa ph ps)) th ta) ph) :=
  by
  have p0000 := @gSimprl ch ph ps
  have p0001 := @gN3ad2ant1 (synWa ch (synWa ph ps)) th ph ta p0000
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_simp1rr`. -/
@[expose]
noncomputable def gSimp1rr (ph : Wff) (ps : Wff) (ch : Wff) (th : Wff) (ta : Wff) :
    Nominal.NPrf (.imp (synW3a (synWa ch (synWa ph ps)) th ta) ps) :=
  by
  have p0000 := @gSimprr ch ph ps
  have p0001 := @gN3ad2ant1 (synWa ch (synWa ph ps)) th ps ta p0000
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_simp2ll`. -/
@[expose]
noncomputable def gSimp2ll (ph : Wff) (ps : Wff) (ch : Wff) (th : Wff) (ta : Wff) :
    Nominal.NPrf (.imp (synW3a th (synWa (synWa ph ps) ch) ta) ph) :=
  by
  have p0000 := @gSimpll ph ps ch
  have p0001 := @gN3ad2ant2 (synWa (synWa ph ps) ch) th ph ta p0000
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_simp2lr`. -/
@[expose]
noncomputable def gSimp2lr (ph : Wff) (ps : Wff) (ch : Wff) (th : Wff) (ta : Wff) :
    Nominal.NPrf (.imp (synW3a th (synWa (synWa ph ps) ch) ta) ps) :=
  by
  have p0000 := @gSimplr ph ps ch
  have p0001 := @gN3ad2ant2 (synWa (synWa ph ps) ch) th ps ta p0000
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_simp2rl`. -/
@[expose]
noncomputable def gSimp2rl (ph : Wff) (ps : Wff) (ch : Wff) (th : Wff) (ta : Wff) :
    Nominal.NPrf (.imp (synW3a th (synWa ch (synWa ph ps)) ta) ph) :=
  by
  have p0000 := @gSimprl ch ph ps
  have p0001 := @gN3ad2ant2 (synWa ch (synWa ph ps)) th ph ta p0000
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_simp2rr`. -/
@[expose]
noncomputable def gSimp2rr (ph : Wff) (ps : Wff) (ch : Wff) (th : Wff) (ta : Wff) :
    Nominal.NPrf (.imp (synW3a th (synWa ch (synWa ph ps)) ta) ps) :=
  by
  have p0000 := @gSimprr ch ph ps
  have p0001 := @gN3ad2ant2 (synWa ch (synWa ph ps)) th ps ta p0000
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_simp3ll`. -/
@[expose]
noncomputable def gSimp3ll (ph : Wff) (ps : Wff) (ch : Wff) (th : Wff) (ta : Wff) :
    Nominal.NPrf (.imp (synW3a th ta (synWa (synWa ph ps) ch)) ph) :=
  by
  have p0000 := @gSimpll ph ps ch
  have p0001 := @gN3ad2ant3 (synWa (synWa ph ps) ch) th ph ta p0000
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_simp3lr`. -/
@[expose]
noncomputable def gSimp3lr (ph : Wff) (ps : Wff) (ch : Wff) (th : Wff) (ta : Wff) :
    Nominal.NPrf (.imp (synW3a th ta (synWa (synWa ph ps) ch)) ps) :=
  by
  have p0000 := @gSimplr ph ps ch
  have p0001 := @gN3ad2ant3 (synWa (synWa ph ps) ch) th ps ta p0000
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_simp3rl`. -/
@[expose]
noncomputable def gSimp3rl (ph : Wff) (ps : Wff) (ch : Wff) (th : Wff) (ta : Wff) :
    Nominal.NPrf (.imp (synW3a th ta (synWa ch (synWa ph ps))) ph) :=
  by
  have p0000 := @gSimprl ch ph ps
  have p0001 := @gN3ad2ant3 (synWa ch (synWa ph ps)) th ph ta p0000
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_simp3rr`. -/
@[expose]
noncomputable def gSimp3rr (ph : Wff) (ps : Wff) (ch : Wff) (th : Wff) (ta : Wff) :
    Nominal.NPrf (.imp (synW3a th ta (synWa ch (synWa ph ps))) ps) :=
  by
  have p0000 := @gSimprr ch ph ps
  have p0001 := @gN3ad2ant3 (synWa ch (synWa ph ps)) th ps ta p0000
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_simpl31`. -/
@[expose]
noncomputable def gSimpl31 (ph : Wff) (ps : Wff) (ch : Wff) (th : Wff) (ta : Wff)
    (et : Wff) : Nominal.NPrf (.imp (synWa (synW3a th ta (synW3a ph ps ch)) et) ph) :=
  by
  have p0000 := @gSimp31 th ta ph ps ch
  have p0001 := @gAdantr (synW3a th ta (synW3a ph ps ch)) ph et p0000
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_simpl32`. -/
@[expose]
noncomputable def gSimpl32 (ph : Wff) (ps : Wff) (ch : Wff) (th : Wff) (ta : Wff)
    (et : Wff) : Nominal.NPrf (.imp (synWa (synW3a th ta (synW3a ph ps ch)) et) ps) :=
  by
  have p0000 := @gSimp32 th ta ph ps ch
  have p0001 := @gAdantr (synW3a th ta (synW3a ph ps ch)) ps et p0000
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_simp12l`. -/
@[expose]
noncomputable def gSimp12l (ph : Wff) (ps : Wff) (ch : Wff) (th : Wff) (ta : Wff)
    (et : Wff) : Nominal.NPrf (.imp (synW3a (synW3a ch (synWa ph ps) th) ta et) ph) :=
  by
  have p0000 := @gSimp2l ch ph ps th
  have p0001 := @gN3ad2ant1 (synW3a ch (synWa ph ps) th) ta ph et p0000
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_simp12r`. -/
@[expose]
noncomputable def gSimp12r (ph : Wff) (ps : Wff) (ch : Wff) (th : Wff) (ta : Wff)
    (et : Wff) : Nominal.NPrf (.imp (synW3a (synW3a ch (synWa ph ps) th) ta et) ps) :=
  by
  have p0000 := @gSimp2r ch ph ps th
  have p0001 := @gN3ad2ant1 (synW3a ch (synWa ph ps) th) ta ps et p0000
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_simp22r`. -/
@[expose]
noncomputable def gSimp22r (ph : Wff) (ps : Wff) (ch : Wff) (th : Wff) (ta : Wff)
    (et : Wff) : Nominal.NPrf (.imp (synW3a ta (synW3a ch (synWa ph ps) th) et) ps) :=
  by
  have p0000 := @gSimp2r ch ph ps th
  have p0001 := @gN3ad2ant2 (synW3a ch (synWa ph ps) th) ta ps et p0000
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_simp23l`. -/
@[expose]
noncomputable def gSimp23l (ph : Wff) (ps : Wff) (ch : Wff) (th : Wff) (ta : Wff)
    (et : Wff) : Nominal.NPrf (.imp (synW3a ta (synW3a ch th (synWa ph ps)) et) ph) :=
  by
  have p0000 := @gSimp3l ch th ph ps
  have p0001 := @gN3ad2ant2 (synW3a ch th (synWa ph ps)) ta ph et p0000
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_n_3adantl1`. -/
@[expose]
noncomputable def gN3adantl1 (ph : Wff) (ps : Wff) (ch : Wff) (th : Wff) (ta : Wff)
    (hyp_n_3adantl_1 : Nominal.NPrf (.imp (synWa (synWa ph ps) ch) th)) :
    Nominal.NPrf (.imp (synWa (synW3a ta ph ps) ch) th) :=
  by
  have p0000 := @gN3simpc ta ph ps
  have p0001 := @gSylan (synW3a ta ph ps) (synWa ph ps) ch th p0000 hyp_n_3adantl_1
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_n_3adantl2`. -/
@[expose]
noncomputable def gN3adantl2 (ph : Wff) (ps : Wff) (ch : Wff) (th : Wff) (ta : Wff)
    (hyp_n_3adantl_1 : Nominal.NPrf (.imp (synWa (synWa ph ps) ch) th)) :
    Nominal.NPrf (.imp (synWa (synW3a ph ta ps) ch) th) :=
  by
  have p0000 := @gN3simpb ph ta ps
  have p0001 := @gSylan (synW3a ph ta ps) (synWa ph ps) ch th p0000 hyp_n_3adantl_1
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_n_3adantr1`. -/
@[expose]
noncomputable def gN3adantr1 (ph : Wff) (ps : Wff) (ch : Wff) (th : Wff) (ta : Wff)
    (hyp_n_3adantr_1 : Nominal.NPrf (.imp (synWa ph (synWa ps ch)) th)) :
    Nominal.NPrf (.imp (synWa ph (synW3a ta ps ch)) th) :=
  by
  have p0000 := @gN3simpc ta ps ch
  have p0001 := @gSylan2 (synW3a ta ps ch) ph (synWa ps ch) th p0000 hyp_n_3adantr_1
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_n_3ad2antl1`. -/
@[expose]
noncomputable def gN3ad2antl1 (ph : Wff) (ps : Wff) (ch : Wff) (th : Wff) (ta : Wff)
    (hyp_n_3ad2antl_1 : Nominal.NPrf (.imp (synWa ph ch) th)) :
    Nominal.NPrf (.imp (synWa (synW3a ph ps ta) ch) th) :=
  by
  have p0000 := @gAdantlr ph ch th ta hyp_n_3ad2antl_1
  have p0001 := @gN3adantl2 ph ta ch th ps p0000
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_n_3ad2antl3`. -/
@[expose]
noncomputable def gN3ad2antl3 (ph : Wff) (ps : Wff) (ch : Wff) (th : Wff) (ta : Wff)
    (hyp_n_3ad2antl_1 : Nominal.NPrf (.imp (synWa ph ch) th)) :
    Nominal.NPrf (.imp (synWa (synW3a ps ta ph) ch) th) :=
  by
  have p0000 := @gAdantll ph ch th ta hyp_n_3ad2antl_1
  have p0001 := @gN3adantl1 ta ph ch th ps p0000
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_n_3mix1`. -/
@[expose]
noncomputable def gN3mix1 (ph : Wff) (ps : Wff) (ch : Wff) :
    Nominal.NPrf (.imp ph (synW3o ph ps ch)) :=
  by
  have p0000 := @gOrc ph (synWo ps ch)
  have p0001 := @gN3orass ph ps ch
  have p0002 := @gSylibr ph (synWo ph (synWo ps ch)) (synW3o ph ps ch) p0000 p0001
  exact p0002

/-- Checked nominal proof certificate identified upstream as `g_n_3mix2`. -/
@[expose]
noncomputable def gN3mix2 (ph : Wff) (ps : Wff) (ch : Wff) :
    Nominal.NPrf (.imp ph (synW3o ps ph ch)) :=
  by
  have p0000 := @gN3mix1 ph ch ps
  have p0001 := @gN3orrot ps ph ch
  have p0002 := @gSylibr ph (synW3o ph ch ps) (synW3o ps ph ch) p0000 p0001
  exact p0002

/-- Checked nominal proof certificate identified upstream as `g_n_3mix3`. -/
@[expose]
noncomputable def gN3mix3 (ph : Wff) (ps : Wff) (ch : Wff) :
    Nominal.NPrf (.imp ph (synW3o ps ch ph)) :=
  by
  have p0000 := @gN3mix1 ph ps ch
  have p0001 := @gN3orrot ph ps ch
  have p0002 := @gSylib ph (synW3o ph ps ch) (synW3o ps ch ph) p0000 p0001
  exact p0002

/-- Checked nominal proof certificate identified upstream as `g_n_3pm3_2i`. -/
@[expose]
noncomputable def gN3pm32i (ph : Wff) (ps : Wff) (ch : Wff)
    (hyp_n_3pm3_2i_1 : Nominal.NPrf ph) (hyp_n_3pm3_2i_2 : Nominal.NPrf ps)
    (hyp_n_3pm3_2i_3 : Nominal.NPrf ch) : Nominal.NPrf (synW3a ph ps ch) :=
  by
  have p0000 := @gPm32i ph ps hyp_n_3pm3_2i_1 hyp_n_3pm3_2i_2
  have p0001 := (Nominal.biimpRefl (synW3a ph ps ch))
  have p0002 :=
    @gMpbir2an (synW3a ph ps ch) (synWa ph ps) ch p0000 hyp_n_3pm3_2i_3 p0001
  exact p0002

/-- Checked nominal proof certificate identified upstream as `g_pm3_2an3`. -/
@[expose]
noncomputable def gPm32an3 (ph : Wff) (ps : Wff) (ch : Wff) :
    Nominal.NPrf (.imp ph (.imp ps (.imp ch (synW3a ph ps ch)))) :=
  by
  have p0000 := @g_pm3_2 (synWa ph ps) ch
  have p0001 := @gEx ph ps (.imp ch (synWa (synWa ph ps) ch)) p0000
  have p0002 := (Nominal.biimpRefl (synW3a ph ps ch))
  have p0003 := @gBicomi (synW3a ph ps ch) (synWa (synWa ph ps) ch) p0002
  have p0004 :=
    @gSyl8ib ph ps ch (synWa (synWa ph ps) ch) (synW3a ph ps ch) p0001 p0003
  exact p0004

/-- Checked nominal proof certificate identified upstream as `g_n_3jca`. -/
@[expose]
noncomputable def gN3jca (ph : Wff) (ps : Wff) (ch : Wff) (th : Wff)
    (hyp_n_3jca_1 : Nominal.NPrf (.imp ph ps)) (hyp_n_3jca_2 : Nominal.NPrf (.imp ph ch))
    (hyp_n_3jca_3 : Nominal.NPrf (.imp ph th)) :
    Nominal.NPrf (.imp ph (synW3a ps ch th)) :=
  by
  have p0000 := @gJca31 ph ps ch th hyp_n_3jca_1 hyp_n_3jca_2 hyp_n_3jca_3
  have p0001 := (Nominal.biimpRefl (synW3a ps ch th))
  have p0002 := @gSylibr ph (synWa (synWa ps ch) th) (synW3a ps ch th) p0000 p0001
  exact p0002

/-- Checked nominal proof certificate identified upstream as `g_n_3jcad`. -/
@[expose]
noncomputable def gN3jcad (ph : Wff) (ps : Wff) (ch : Wff) (th : Wff) (ta : Wff)
    (hyp_n_3jcad_1 : Nominal.NPrf (.imp ph (.imp ps ch)))
    (hyp_n_3jcad_2 : Nominal.NPrf (.imp ph (.imp ps th)))
    (hyp_n_3jcad_3 : Nominal.NPrf (.imp ph (.imp ps ta))) :
    Nominal.NPrf (.imp ph (.imp ps (synW3a ch th ta))) :=
  by
  have p0000 := @gImp ph ps ch hyp_n_3jcad_1
  have p0001 := @gImp ph ps th hyp_n_3jcad_2
  have p0002 := @gImp ph ps ta hyp_n_3jcad_3
  have p0003 := @gN3jca (synWa ph ps) ch th ta p0000 p0001 p0002
  have p0004 := @gEx ph ps (synW3a ch th ta) p0003
  exact p0004

/-- Checked nominal proof certificate identified upstream as `g_mpbir3an`. -/
@[expose]
noncomputable def gMpbir3an (ph : Wff) (ps : Wff) (ch : Wff) (th : Wff)
    (hyp_mpbir3an_1 : Nominal.NPrf ps) (hyp_mpbir3an_2 : Nominal.NPrf ch)
    (hyp_mpbir3an_3 : Nominal.NPrf th)
    (hyp_mpbir3an_4 : Nominal.NPrf (synWb ph (synW3a ps ch th))) : Nominal.NPrf ph :=
  by
  have p0000 := @gN3pm32i ps ch th hyp_mpbir3an_1 hyp_mpbir3an_2 hyp_mpbir3an_3
  have p0001 := @gMpbir ph (synW3a ps ch th) p0000 hyp_mpbir3an_4
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_syl3anbrc`. -/
@[expose]
noncomputable def gSyl3anbrc (ph : Wff) (ps : Wff) (ch : Wff) (th : Wff) (ta : Wff)
    (hyp_syl3anbrc_1 : Nominal.NPrf (.imp ph ps))
    (hyp_syl3anbrc_2 : Nominal.NPrf (.imp ph ch))
    (hyp_syl3anbrc_3 : Nominal.NPrf (.imp ph th))
    (hyp_syl3anbrc_4 : Nominal.NPrf (synWb ta (synW3a ps ch th))) :
    Nominal.NPrf (.imp ph ta) :=
  by
  have p0000 := @gN3jca ph ps ch th hyp_syl3anbrc_1 hyp_syl3anbrc_2 hyp_syl3anbrc_3
  have p0001 := @gSylibr ph (synW3a ps ch th) ta p0000 hyp_syl3anbrc_4
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_n_3anim123i`. -/
@[expose]
noncomputable def gN3anim123i (ph : Wff) (ps : Wff) (ch : Wff) (th : Wff) (ta : Wff)
    (et : Wff) (hyp_n_3anim123i_1 : Nominal.NPrf (.imp ph ps))
    (hyp_n_3anim123i_2 : Nominal.NPrf (.imp ch th))
    (hyp_n_3anim123i_3 : Nominal.NPrf (.imp ta et)) :
    Nominal.NPrf (.imp (synW3a ph ch ta) (synW3a ps th et)) :=
  by
  have p0000 := @gN3ad2ant1 ph ch ps ta hyp_n_3anim123i_1
  have p0001 := @gN3ad2ant2 ch ph th ta hyp_n_3anim123i_2
  have p0002 := @gN3ad2ant3 ta ph et ch hyp_n_3anim123i_3
  have p0003 := @gN3jca (synW3a ph ch ta) ps th et p0000 p0001 p0002
  exact p0003

/-- Checked nominal proof certificate identified upstream as `g_n_3anim1i`. -/
@[expose]
noncomputable def gN3anim1i (ph : Wff) (ps : Wff) (ch : Wff) (th : Wff)
    (hyp_n_3animi_1 : Nominal.NPrf (.imp ph ps)) :
    Nominal.NPrf (.imp (synW3a ph ch th) (synW3a ps ch th)) :=
  by
  have p0000 := @gId ch
  have p0001 := @gId th
  have p0002 := @gN3anim123i ph ps ch ch th th hyp_n_3animi_1 p0000 p0001
  exact p0002

/-- Checked nominal proof certificate identified upstream as `g_n_3anbi123i`. -/
@[expose]
noncomputable def gN3anbi123i (ph : Wff) (ps : Wff) (ch : Wff) (th : Wff) (ta : Wff)
    (et : Wff) (hyp_bi3_1 : Nominal.NPrf (synWb ph ps))
    (hyp_bi3_2 : Nominal.NPrf (synWb ch th)) (hyp_bi3_3 : Nominal.NPrf (synWb ta et)) :
    Nominal.NPrf (synWb (synW3a ph ch ta) (synW3a ps th et)) :=
  by
  have p0000 := @gAnbi12i ph ps ch th hyp_bi3_1 hyp_bi3_2
  have p0001 := @gAnbi12i (synWa ph ch) (synWa ps th) ta et p0000 hyp_bi3_3
  have p0002 := (Nominal.biimpRefl (synW3a ph ch ta))
  have p0003 := (Nominal.biimpRefl (synW3a ps th et))
  have p0004 :=
    @gN3bitr4i (synWa (synWa ph ch) ta) (synWa (synWa ps th) et) (synW3a ph ch ta)
      (synW3a ps th et) p0001 p0002 p0003
  exact p0004

/-- Checked nominal proof certificate identified upstream as `g_n_3anbi1i`. -/
@[expose]
noncomputable def gN3anbi1i (ph : Wff) (ps : Wff) (ch : Wff) (th : Wff)
    (hyp_n_3anbi1i_1 : Nominal.NPrf (synWb ph ps)) :
    Nominal.NPrf (synWb (synW3a ph ch th) (synW3a ps ch th)) :=
  by
  have p0000 := @gBiid ch
  have p0001 := @gBiid th
  have p0002 := @gN3anbi123i ph ps ch ch th th hyp_n_3anbi1i_1 p0000 p0001
  exact p0002

/-- Checked nominal proof certificate identified upstream as `g_n_3anbi2i`. -/
@[expose]
noncomputable def gN3anbi2i (ph : Wff) (ps : Wff) (ch : Wff) (th : Wff)
    (hyp_n_3anbi1i_1 : Nominal.NPrf (synWb ph ps)) :
    Nominal.NPrf (synWb (synW3a ch ph th) (synW3a ch ps th)) :=
  by
  have p0000 := @gBiid ch
  have p0001 := @gBiid th
  have p0002 := @gN3anbi123i ch ch ph ps th th p0000 hyp_n_3anbi1i_1 p0001
  exact p0002

/-- Checked nominal proof certificate identified upstream as `g_n_3anbi3i`. -/
@[expose]
noncomputable def gN3anbi3i (ph : Wff) (ps : Wff) (ch : Wff) (th : Wff)
    (hyp_n_3anbi1i_1 : Nominal.NPrf (synWb ph ps)) :
    Nominal.NPrf (synWb (synW3a ch th ph) (synW3a ch th ps)) :=
  by
  have p0000 := @gBiid ch
  have p0001 := @gBiid th
  have p0002 := @gN3anbi123i ch ch th th ph ps p0000 p0001 hyp_n_3anbi1i_1
  exact p0002

/-- Checked nominal proof certificate identified upstream as `g_n_3imp`. -/
@[expose]
noncomputable def gN3imp (ph : Wff) (ps : Wff) (ch : Wff) (th : Wff)
    (hyp_n_3imp_1 : Nominal.NPrf (.imp ph (.imp ps (.imp ch th)))) :
    Nominal.NPrf (.imp (synW3a ph ps ch) th) :=
  by
  have p0000 := (Nominal.biimpRefl (synW3a ph ps ch))
  have p0001 := @gImp31 ph ps ch th hyp_n_3imp_1
  have p0002 := @gSylbi (synW3a ph ps ch) (synWa (synWa ph ps) ch) th p0000 p0001
  exact p0002

/-- Checked nominal proof certificate identified upstream as `g_n_3impa`. -/
@[expose]
noncomputable def gN3impa (ph : Wff) (ps : Wff) (ch : Wff) (th : Wff)
    (hyp_n_3impa_1 : Nominal.NPrf (.imp (synWa (synWa ph ps) ch) th)) :
    Nominal.NPrf (.imp (synW3a ph ps ch) th) :=
  by
  have p0000 := @gExp31 ph ps ch th hyp_n_3impa_1
  have p0001 := @gN3imp ph ps ch th p0000
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_n_3impb`. -/
@[expose]
noncomputable def gN3impb (ph : Wff) (ps : Wff) (ch : Wff) (th : Wff)
    (hyp_n_3impb_1 : Nominal.NPrf (.imp (synWa ph (synWa ps ch)) th)) :
    Nominal.NPrf (.imp (synW3a ph ps ch) th) :=
  by
  have p0000 := @gExp32 ph ps ch th hyp_n_3impb_1
  have p0001 := @gN3imp ph ps ch th p0000
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_n_3impia`. -/
@[expose]
noncomputable def gN3impia (ph : Wff) (ps : Wff) (ch : Wff) (th : Wff)
    (hyp_n_3impia_1 : Nominal.NPrf (.imp (synWa ph ps) (.imp ch th))) :
    Nominal.NPrf (.imp (synW3a ph ps ch) th) :=
  by
  have p0000 := @gEx ph ps (.imp ch th) hyp_n_3impia_1
  have p0001 := @gN3imp ph ps ch th p0000
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_n_3impib`. -/
@[expose]
noncomputable def gN3impib (ph : Wff) (ps : Wff) (ch : Wff) (th : Wff)
    (hyp_n_3impib_1 : Nominal.NPrf (.imp ph (.imp (synWa ps ch) th))) :
    Nominal.NPrf (.imp (synW3a ph ps ch) th) :=
  by
  have p0000 := @gExp3a ph ps ch th hyp_n_3impib_1
  have p0001 := @gN3imp ph ps ch th p0000
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_n_3exp`. -/
@[expose]
noncomputable def gN3exp (ph : Wff) (ps : Wff) (ch : Wff) (th : Wff)
    (hyp_n_3exp_1 : Nominal.NPrf (.imp (synW3a ph ps ch) th)) :
    Nominal.NPrf (.imp ph (.imp ps (.imp ch th))) :=
  by
  have p0000 := @gPm32an3 ph ps ch
  have p0001 := @gSyl8 ph ps ch (synW3a ph ps ch) th p0000 hyp_n_3exp_1
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_n_3expa`. -/
@[expose]
noncomputable def gN3expa (ph : Wff) (ps : Wff) (ch : Wff) (th : Wff)
    (hyp_n_3exp_1 : Nominal.NPrf (.imp (synW3a ph ps ch) th)) :
    Nominal.NPrf (.imp (synWa (synWa ph ps) ch) th) :=
  by
  have p0000 := @gN3exp ph ps ch th hyp_n_3exp_1
  have p0001 := @gImp31 ph ps ch th p0000
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_n_3expb`. -/
@[expose]
noncomputable def gN3expb (ph : Wff) (ps : Wff) (ch : Wff) (th : Wff)
    (hyp_n_3exp_1 : Nominal.NPrf (.imp (synW3a ph ps ch) th)) :
    Nominal.NPrf (.imp (synWa ph (synWa ps ch)) th) :=
  by
  have p0000 := @gN3exp ph ps ch th hyp_n_3exp_1
  have p0001 := @gImp32 ph ps ch th p0000
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_n_3expia`. -/
@[expose]
noncomputable def gN3expia (ph : Wff) (ps : Wff) (ch : Wff) (th : Wff)
    (hyp_n_3exp_1 : Nominal.NPrf (.imp (synW3a ph ps ch) th)) :
    Nominal.NPrf (.imp (synWa ph ps) (.imp ch th)) :=
  by
  have p0000 := @gN3exp ph ps ch th hyp_n_3exp_1
  have p0001 := @gImp ph ps (.imp ch th) p0000
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_n_3expib`. -/
@[expose]
noncomputable def gN3expib (ph : Wff) (ps : Wff) (ch : Wff) (th : Wff)
    (hyp_n_3exp_1 : Nominal.NPrf (.imp (synW3a ph ps ch) th)) :
    Nominal.NPrf (.imp ph (.imp (synWa ps ch) th)) :=
  by
  have p0000 := @gN3exp ph ps ch th hyp_n_3exp_1
  have p0001 := @gImp3a ph ps ch th p0000
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_n_3com12`. -/
@[expose]
noncomputable def gN3com12 (ph : Wff) (ps : Wff) (ch : Wff) (th : Wff)
    (hyp_n_3exp_1 : Nominal.NPrf (.imp (synW3a ph ps ch) th)) :
    Nominal.NPrf (.imp (synW3a ps ph ch) th) :=
  by
  have p0000 := @gN3ancoma ps ph ch
  have p0001 := @gSylbi (synW3a ps ph ch) (synW3a ph ps ch) th p0000 hyp_n_3exp_1
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_n_3com13`. -/
@[expose]
noncomputable def gN3com13 (ph : Wff) (ps : Wff) (ch : Wff) (th : Wff)
    (hyp_n_3exp_1 : Nominal.NPrf (.imp (synW3a ph ps ch) th)) :
    Nominal.NPrf (.imp (synW3a ch ps ph) th) :=
  by
  have p0000 := @gN3anrev ch ps ph
  have p0001 := @gSylbi (synW3a ch ps ph) (synW3a ph ps ch) th p0000 hyp_n_3exp_1
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_n_3com23`. -/
@[expose]
noncomputable def gN3com23 (ph : Wff) (ps : Wff) (ch : Wff) (th : Wff)
    (hyp_n_3exp_1 : Nominal.NPrf (.imp (synW3a ph ps ch) th)) :
    Nominal.NPrf (.imp (synW3a ph ch ps) th) :=
  by
  have p0000 := @gN3exp ph ps ch th hyp_n_3exp_1
  have p0001 := @gCom23 ph ps ch th p0000
  have p0002 := @gN3imp ph ch ps th p0001
  exact p0002

/-- Checked nominal proof certificate identified upstream as `g_n_3coml`. -/
@[expose]
noncomputable def gN3coml (ph : Wff) (ps : Wff) (ch : Wff) (th : Wff)
    (hyp_n_3exp_1 : Nominal.NPrf (.imp (synW3a ph ps ch) th)) :
    Nominal.NPrf (.imp (synW3a ps ch ph) th) :=
  by
  have p0000 := @gN3com23 ph ps ch th hyp_n_3exp_1
  have p0001 := @gN3com13 ph ch ps th p0000
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_n_3impd`. -/
@[expose]
noncomputable def gN3impd (ph : Wff) (ps : Wff) (ch : Wff) (th : Wff) (ta : Wff)
    (hyp_n_3imp1_1 : Nominal.NPrf (.imp ph (.imp ps (.imp ch (.imp th ta))))) :
    Nominal.NPrf (.imp ph (.imp (synW3a ps ch th) ta)) :=
  by
  have p0000 := @gCom4l ph ps ch th ta hyp_n_3imp1_1
  have p0001 := @gN3imp ps ch th (.imp ph ta) p0000
  have p0002 := @gCom12 (synW3a ps ch th) ph ta p0001
  exact p0002

/-- Checked nominal proof certificate identified upstream as `g_n_3expd`. -/
@[expose]
noncomputable def gN3expd (ph : Wff) (ps : Wff) (ch : Wff) (th : Wff) (ta : Wff)
    (hyp_n_3expd_1 : Nominal.NPrf (.imp ph (.imp (synW3a ps ch th) ta))) :
    Nominal.NPrf (.imp ph (.imp ps (.imp ch (.imp th ta)))) :=
  by
  have p0000 := @gCom12 ph (synW3a ps ch th) ta hyp_n_3expd_1
  have p0001 := @gN3exp ps ch th (.imp ph ta) p0000
  have p0002 := @gCom4r ps ch th ph ta p0001
  exact p0002

/-- Checked nominal proof certificate identified upstream as `g_n_3exp2`. -/
@[expose]
noncomputable def gN3exp2 (ph : Wff) (ps : Wff) (ch : Wff) (th : Wff) (ta : Wff)
    (hyp_n_3exp2_1 : Nominal.NPrf (.imp (synWa ph (synW3a ps ch th)) ta)) :
    Nominal.NPrf (.imp ph (.imp ps (.imp ch (.imp th ta)))) :=
  by
  have p0000 := @gEx ph (synW3a ps ch th) ta hyp_n_3exp2_1
  have p0001 := @gN3expd ph ps ch th ta p0000
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_n_3adant1r`. -/
@[expose]
noncomputable def gN3adant1r (ph : Wff) (ps : Wff) (ch : Wff) (th : Wff) (ta : Wff)
    (hyp_n_3adant1l_1 : Nominal.NPrf (.imp (synW3a ph ps ch) th)) :
    Nominal.NPrf (.imp (synW3a (synWa ph ta) ps ch) th) :=
  by
  have p0000 := @gN3expb ph ps ch th hyp_n_3adant1l_1
  have p0001 := @gAdantlr ph (synWa ps ch) th ta p0000
  have p0002 := @gN3impb (synWa ph ta) ps ch th p0001
  exact p0002

/-- Checked nominal proof certificate identified upstream as `g_syl12anc`. -/
@[expose]
noncomputable def gSyl12anc (ph : Wff) (ps : Wff) (ch : Wff) (th : Wff) (ta : Wff)
    (hyp_sylXanc_1 : Nominal.NPrf (.imp ph ps))
    (hyp_sylXanc_2 : Nominal.NPrf (.imp ph ch))
    (hyp_sylXanc_3 : Nominal.NPrf (.imp ph th))
    (hyp_syl12anc_4 : Nominal.NPrf (.imp (synWa ps (synWa ch th)) ta)) :
    Nominal.NPrf (.imp ph ta) :=
  by
  have p0000 := @gJca32 ph ps ch th hyp_sylXanc_1 hyp_sylXanc_2 hyp_sylXanc_3
  have p0001 := @gSyl ph (synWa ps (synWa ch th)) ta p0000 hyp_syl12anc_4
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_syl21anc`. -/
@[expose]
noncomputable def gSyl21anc (ph : Wff) (ps : Wff) (ch : Wff) (th : Wff) (ta : Wff)
    (hyp_sylXanc_1 : Nominal.NPrf (.imp ph ps))
    (hyp_sylXanc_2 : Nominal.NPrf (.imp ph ch))
    (hyp_sylXanc_3 : Nominal.NPrf (.imp ph th))
    (hyp_syl21anc_4 : Nominal.NPrf (.imp (synWa (synWa ps ch) th) ta)) :
    Nominal.NPrf (.imp ph ta) :=
  by
  have p0000 := @gJca31 ph ps ch th hyp_sylXanc_1 hyp_sylXanc_2 hyp_sylXanc_3
  have p0001 := @gSyl ph (synWa (synWa ps ch) th) ta p0000 hyp_syl21anc_4
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_syl3anc`. -/
@[expose]
noncomputable def gSyl3anc (ph : Wff) (ps : Wff) (ch : Wff) (th : Wff) (ta : Wff)
    (hyp_sylXanc_1 : Nominal.NPrf (.imp ph ps))
    (hyp_sylXanc_2 : Nominal.NPrf (.imp ph ch))
    (hyp_sylXanc_3 : Nominal.NPrf (.imp ph th))
    (hyp_syl111anc_4 : Nominal.NPrf (.imp (synW3a ps ch th) ta)) :
    Nominal.NPrf (.imp ph ta) :=
  by
  have p0000 := @gN3jca ph ps ch th hyp_sylXanc_1 hyp_sylXanc_2 hyp_sylXanc_3
  have p0001 := @gSyl ph (synW3a ps ch th) ta p0000 hyp_syl111anc_4
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_syl22anc`. -/
@[expose]
noncomputable def gSyl22anc (ph : Wff) (ps : Wff) (ch : Wff) (th : Wff) (ta : Wff)
    (et : Wff) (hyp_sylXanc_1 : Nominal.NPrf (.imp ph ps))
    (hyp_sylXanc_2 : Nominal.NPrf (.imp ph ch))
    (hyp_sylXanc_3 : Nominal.NPrf (.imp ph th))
    (hyp_sylXanc_4 : Nominal.NPrf (.imp ph ta))
    (hyp_syl22anc_5 : Nominal.NPrf (.imp (synWa (synWa ps ch) (synWa th ta)) et)) :
    Nominal.NPrf (.imp ph et) :=
  by
  have p0000 := @gJca ph ps ch hyp_sylXanc_1 hyp_sylXanc_2
  have p0001 :=
    @gSyl12anc ph (synWa ps ch) th ta et p0000 hyp_sylXanc_3 hyp_sylXanc_4
      hyp_syl22anc_5
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_syl13anc`. -/
@[expose]
noncomputable def gSyl13anc (ph : Wff) (ps : Wff) (ch : Wff) (th : Wff) (ta : Wff)
    (et : Wff) (hyp_sylXanc_1 : Nominal.NPrf (.imp ph ps))
    (hyp_sylXanc_2 : Nominal.NPrf (.imp ph ch))
    (hyp_sylXanc_3 : Nominal.NPrf (.imp ph th))
    (hyp_sylXanc_4 : Nominal.NPrf (.imp ph ta))
    (hyp_syl13anc_5 : Nominal.NPrf (.imp (synWa ps (synW3a ch th ta)) et)) :
    Nominal.NPrf (.imp ph et) :=
  by
  have p0000 := @gN3jca ph ch th ta hyp_sylXanc_2 hyp_sylXanc_3 hyp_sylXanc_4
  have p0001 := @gSyl2anc ph ps (synW3a ch th ta) et hyp_sylXanc_1 p0000 hyp_syl13anc_5
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_syl31anc`. -/
@[expose]
noncomputable def gSyl31anc (ph : Wff) (ps : Wff) (ch : Wff) (th : Wff) (ta : Wff)
    (et : Wff) (hyp_sylXanc_1 : Nominal.NPrf (.imp ph ps))
    (hyp_sylXanc_2 : Nominal.NPrf (.imp ph ch))
    (hyp_sylXanc_3 : Nominal.NPrf (.imp ph th))
    (hyp_sylXanc_4 : Nominal.NPrf (.imp ph ta))
    (hyp_syl31anc_5 : Nominal.NPrf (.imp (synWa (synW3a ps ch th) ta) et)) :
    Nominal.NPrf (.imp ph et) :=
  by
  have p0000 := @gN3jca ph ps ch th hyp_sylXanc_1 hyp_sylXanc_2 hyp_sylXanc_3
  have p0001 := @gSyl2anc ph (synW3a ps ch th) ta et p0000 hyp_sylXanc_4 hyp_syl31anc_5
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_syl211anc`. -/
@[expose]
noncomputable def gSyl211anc (ph : Wff) (ps : Wff) (ch : Wff) (th : Wff) (ta : Wff)
    (et : Wff) (hyp_sylXanc_1 : Nominal.NPrf (.imp ph ps))
    (hyp_sylXanc_2 : Nominal.NPrf (.imp ph ch))
    (hyp_sylXanc_3 : Nominal.NPrf (.imp ph th))
    (hyp_sylXanc_4 : Nominal.NPrf (.imp ph ta))
    (hyp_syl211anc_5 : Nominal.NPrf (.imp (synW3a (synWa ps ch) th ta) et)) :
    Nominal.NPrf (.imp ph et) :=
  by
  have p0000 := @gJca ph ps ch hyp_sylXanc_1 hyp_sylXanc_2
  have p0001 :=
    @gSyl3anc ph (synWa ps ch) th ta et p0000 hyp_sylXanc_3 hyp_sylXanc_4
      hyp_syl211anc_5
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_syl221anc`. -/
@[expose]
noncomputable def gSyl221anc (ph : Wff) (ps : Wff) (ch : Wff) (th : Wff) (ta : Wff)
    (et : Wff) (ze : Wff) (hyp_sylXanc_1 : Nominal.NPrf (.imp ph ps))
    (hyp_sylXanc_2 : Nominal.NPrf (.imp ph ch))
    (hyp_sylXanc_3 : Nominal.NPrf (.imp ph th))
    (hyp_sylXanc_4 : Nominal.NPrf (.imp ph ta))
    (hyp_sylXanc_5 : Nominal.NPrf (.imp ph et))
    (hyp_syl221anc_6 : Nominal.NPrf (.imp (synW3a (synWa ps ch) (synWa th ta) et) ze)) :
    Nominal.NPrf (.imp ph ze) :=
  by
  have p0000 := @gJca ph th ta hyp_sylXanc_3 hyp_sylXanc_4
  have p0001 :=
    @gSyl211anc ph ps ch (synWa th ta) et ze hyp_sylXanc_1 hyp_sylXanc_2 p0000
      hyp_sylXanc_5 hyp_syl221anc_6
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_syl3an1`. -/
@[expose]
noncomputable def gSyl3an1 (ph : Wff) (ps : Wff) (ch : Wff) (th : Wff) (ta : Wff)
    (hyp_syl3an1_1 : Nominal.NPrf (.imp ph ps))
    (hyp_syl3an1_2 : Nominal.NPrf (.imp (synW3a ps ch th) ta)) :
    Nominal.NPrf (.imp (synW3a ph ch th) ta) :=
  by
  have p0000 := @gN3anim1i ph ps ch th hyp_syl3an1_1
  have p0001 := @gSyl (synW3a ph ch th) (synW3a ps ch th) ta p0000 hyp_syl3an1_2
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_syl3an3`. -/
@[expose]
noncomputable def gSyl3an3 (ph : Wff) (ps : Wff) (ch : Wff) (th : Wff) (ta : Wff)
    (hyp_syl3an3_1 : Nominal.NPrf (.imp ph th))
    (hyp_syl3an3_2 : Nominal.NPrf (.imp (synW3a ps ch th) ta)) :
    Nominal.NPrf (.imp (synW3a ps ch ph) ta) :=
  by
  have p0000 := @gN3exp ps ch th ta hyp_syl3an3_2
  have p0001 := @gSyl7 ph th ps ch ta hyp_syl3an3_1 p0000
  have p0002 := @gN3imp ps ch ph ta p0001
  exact p0002

/-- Checked nominal proof certificate identified upstream as `g_syl3an3b`. -/
@[expose]
noncomputable def gSyl3an3b (ph : Wff) (ps : Wff) (ch : Wff) (th : Wff) (ta : Wff)
    (hyp_syl3an3b_1 : Nominal.NPrf (synWb ph th))
    (hyp_syl3an3b_2 : Nominal.NPrf (.imp (synW3a ps ch th) ta)) :
    Nominal.NPrf (.imp (synW3a ps ch ph) ta) :=
  by
  have p0000 := @gBiimpi ph th hyp_syl3an3b_1
  have p0001 := @gSyl3an3 ph ps ch th ta p0000 hyp_syl3an3b_2
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_syl3an`. -/
@[expose]
noncomputable def gSyl3an (ph : Wff) (ps : Wff) (ch : Wff) (th : Wff) (ta : Wff)
    (et : Wff) (ze : Wff) (hyp_syl3an_1 : Nominal.NPrf (.imp ph ps))
    (hyp_syl3an_2 : Nominal.NPrf (.imp ch th)) (hyp_syl3an_3 : Nominal.NPrf (.imp ta et))
    (hyp_syl3an_4 : Nominal.NPrf (.imp (synW3a ps th et) ze)) :
    Nominal.NPrf (.imp (synW3a ph ch ta) ze) :=
  by
  have p0000 := @gN3anim123i ph ps ch th ta et hyp_syl3an_1 hyp_syl3an_2 hyp_syl3an_3
  have p0001 := @gSyl (synW3a ph ch ta) (synW3a ps th et) ze p0000 hyp_syl3an_4
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_n_3anidm12`. -/
@[expose]
noncomputable def gN3anidm12 (ph : Wff) (ps : Wff) (ch : Wff)
    (hyp_n_3anidm12_1 : Nominal.NPrf (.imp (synW3a ph ph ps) ch)) :
    Nominal.NPrf (.imp (synWa ph ps) ch) :=
  by
  have p0000 := @gN3expib ph ph ps ch hyp_n_3anidm12_1
  have p0001 := @gAnabsi5 ph ps ch p0000
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_n_3anidm13`. -/
@[expose]
noncomputable def gN3anidm13 (ph : Wff) (ps : Wff) (ch : Wff)
    (hyp_n_3anidm13_1 : Nominal.NPrf (.imp (synW3a ph ps ph) ch)) :
    Nominal.NPrf (.imp (synWa ph ps) ch) :=
  by
  have p0000 := @gN3com23 ph ps ph ch hyp_n_3anidm13_1
  have p0001 := @gN3anidm12 ph ps ch p0000
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_n_3anidm23`. -/
@[expose]
noncomputable def gN3anidm23 (ph : Wff) (ps : Wff) (ch : Wff)
    (hyp_n_3anidm23_1 : Nominal.NPrf (.imp (synW3a ph ps ps) ch)) :
    Nominal.NPrf (.imp (synWa ph ps) ch) :=
  by
  have p0000 := @gN3expa ph ps ps ch hyp_n_3anidm23_1
  have p0001 := @gAnabss3 ph ps ch p0000
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_n_3jao`. -/
@[expose]
noncomputable def gN3jao (ph : Wff) (ps : Wff) (ch : Wff) (th : Wff) :
    Nominal.NPrf
      (.imp (synW3a (.imp ph ps) (.imp ch ps) (.imp th ps)) (.imp (synW3o ph ch th) ps)) :=
  by
  have p0000 := (Nominal.biimpRefl (synW3o ph ch th))
  have p0001 := @gJao ph ps ch
  have p0002 := @gJao (synWo ph ch) ps th
  have p0003 :=
    @gSyl6 (.imp ph ps) (.imp ch ps) (.imp (synWo ph ch) ps)
      (.imp (.imp th ps) (.imp (synWo (synWo ph ch) th) ps)) p0001 p0002
  have p0004 :=
    @gN3imp (.imp ph ps) (.imp ch ps) (.imp th ps) (.imp (synWo (synWo ph ch) th) ps)
      p0003
  have p0005 :=
    @gSyl5bi (synW3o ph ch th) (synWo (synWo ph ch) th)
      (synW3a (.imp ph ps) (.imp ch ps) (.imp th ps)) ps p0000 p0004
  exact p0005

/-- Checked nominal proof certificate identified upstream as `g_n_3jaoi`. -/
@[expose]
noncomputable def gN3jaoi (ph : Wff) (ps : Wff) (ch : Wff) (th : Wff)
    (hyp_n_3jaoi_1 : Nominal.NPrf (.imp ph ps))
    (hyp_n_3jaoi_2 : Nominal.NPrf (.imp ch ps))
    (hyp_n_3jaoi_3 : Nominal.NPrf (.imp th ps)) :
    Nominal.NPrf (.imp (synW3o ph ch th) ps) :=
  by
  have p0000 :=
    @gN3pm32i (.imp ph ps) (.imp ch ps) (.imp th ps) hyp_n_3jaoi_1 hyp_n_3jaoi_2
      hyp_n_3jaoi_3
  have p0001 := @gN3jao ph ps ch th
  have p0002 := Nominal.mp p0000 p0001
  exact p0002

/-- Checked nominal proof certificate identified upstream as `g_n_3jaod`. -/
@[expose]
noncomputable def gN3jaod (ph : Wff) (ps : Wff) (ch : Wff) (th : Wff) (ta : Wff)
    (hyp_n_3jaod_1 : Nominal.NPrf (.imp ph (.imp ps ch)))
    (hyp_n_3jaod_2 : Nominal.NPrf (.imp ph (.imp th ch)))
    (hyp_n_3jaod_3 : Nominal.NPrf (.imp ph (.imp ta ch))) :
    Nominal.NPrf (.imp ph (.imp (synW3o ps th ta) ch)) :=
  by
  have p0000 := @gN3jao ps ch th ta
  have p0001 :=
    @gSyl3anc ph (.imp ps ch) (.imp th ch) (.imp ta ch) (.imp (synW3o ps th ta) ch)
      hyp_n_3jaod_1 hyp_n_3jaod_2 hyp_n_3jaod_3 p0000
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_syl3an9b`. -/
@[expose]
noncomputable def gSyl3an9b (ph : Wff) (ps : Wff) (ch : Wff) (th : Wff) (ta : Wff)
    (et : Wff) (ze : Wff) (hyp_syl3an9b_1 : Nominal.NPrf (.imp ph (synWb ps ch)))
    (hyp_syl3an9b_2 : Nominal.NPrf (.imp th (synWb ch ta)))
    (hyp_syl3an9b_3 : Nominal.NPrf (.imp et (synWb ta ze))) :
    Nominal.NPrf (.imp (synW3a ph th et) (synWb ps ze)) :=
  by
  have p0000 := @gSylan9bb ph ps ch th ta hyp_syl3an9b_1 hyp_syl3an9b_2
  have p0001 := @gSylan9bb (synWa ph th) ps ta et ze p0000 hyp_syl3an9b_3
  have p0002 := @gN3impa ph th et (synWb ps ze) p0001
  exact p0002

/-- Checked nominal proof certificate identified upstream as `g_n_3orbi123d`. -/
@[expose]
noncomputable def gN3orbi123d (ph : Wff) (ps : Wff) (ch : Wff) (th : Wff) (ta : Wff)
    (et : Wff) (ze : Wff) (hyp_bi3d_1 : Nominal.NPrf (.imp ph (synWb ps ch)))
    (hyp_bi3d_2 : Nominal.NPrf (.imp ph (synWb th ta)))
    (hyp_bi3d_3 : Nominal.NPrf (.imp ph (synWb et ze))) :
    Nominal.NPrf (.imp ph (synWb (synW3o ps th et) (synW3o ch ta ze))) :=
  by
  have p0000 := @gOrbi12d ph ps ch th ta hyp_bi3d_1 hyp_bi3d_2
  have p0001 := @gOrbi12d ph (synWo ps th) (synWo ch ta) et ze p0000 hyp_bi3d_3
  have p0002 := (Nominal.biimpRefl (synW3o ps th et))
  have p0003 := (Nominal.biimpRefl (synW3o ch ta ze))
  have p0004 :=
    @gN3bitr4g ph (synWo (synWo ps th) et) (synWo (synWo ch ta) ze)
      (synW3o ps th et) (synW3o ch ta ze) p0001 p0002 p0003
  exact p0004

/-- Checked nominal proof certificate identified upstream as `g_n_3anbi123d`. -/
@[expose]
noncomputable def gN3anbi123d (ph : Wff) (ps : Wff) (ch : Wff) (th : Wff) (ta : Wff)
    (et : Wff) (ze : Wff) (hyp_bi3d_1 : Nominal.NPrf (.imp ph (synWb ps ch)))
    (hyp_bi3d_2 : Nominal.NPrf (.imp ph (synWb th ta)))
    (hyp_bi3d_3 : Nominal.NPrf (.imp ph (synWb et ze))) :
    Nominal.NPrf (.imp ph (synWb (synW3a ps th et) (synW3a ch ta ze))) :=
  by
  have p0000 := @gAnbi12d ph ps ch th ta hyp_bi3d_1 hyp_bi3d_2
  have p0001 := @gAnbi12d ph (synWa ps th) (synWa ch ta) et ze p0000 hyp_bi3d_3
  have p0002 := (Nominal.biimpRefl (synW3a ps th et))
  have p0003 := (Nominal.biimpRefl (synW3a ch ta ze))
  have p0004 :=
    @gN3bitr4g ph (synWa (synWa ps th) et) (synWa (synWa ch ta) ze)
      (synW3a ps th et) (synW3a ch ta ze) p0001 p0002 p0003
  exact p0004

/-- Checked nominal proof certificate identified upstream as `g_n_3anbi12d`. -/
@[expose]
noncomputable def gN3anbi12d (ph : Wff) (ps : Wff) (ch : Wff) (th : Wff) (ta : Wff)
    (et : Wff) (hyp_n_3anbi12d_1 : Nominal.NPrf (.imp ph (synWb ps ch)))
    (hyp_n_3anbi12d_2 : Nominal.NPrf (.imp ph (synWb th ta))) :
    Nominal.NPrf (.imp ph (synWb (synW3a ps th et) (synW3a ch ta et))) :=
  by
  have p0000 := @gBiidd ph et
  have p0001 :=
    @gN3anbi123d ph ps ch th ta et et hyp_n_3anbi12d_1 hyp_n_3anbi12d_2 p0000
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_n_3anbi13d`. -/
@[expose]
noncomputable def gN3anbi13d (ph : Wff) (ps : Wff) (ch : Wff) (th : Wff) (ta : Wff)
    (et : Wff) (hyp_n_3anbi12d_1 : Nominal.NPrf (.imp ph (synWb ps ch)))
    (hyp_n_3anbi12d_2 : Nominal.NPrf (.imp ph (synWb th ta))) :
    Nominal.NPrf (.imp ph (synWb (synW3a ps et th) (synW3a ch et ta))) :=
  by
  have p0000 := @gBiidd ph et
  have p0001 :=
    @gN3anbi123d ph ps ch et et th ta hyp_n_3anbi12d_1 p0000 hyp_n_3anbi12d_2
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_n_3anbi23d`. -/
@[expose]
noncomputable def gN3anbi23d (ph : Wff) (ps : Wff) (ch : Wff) (th : Wff) (ta : Wff)
    (et : Wff) (hyp_n_3anbi12d_1 : Nominal.NPrf (.imp ph (synWb ps ch)))
    (hyp_n_3anbi12d_2 : Nominal.NPrf (.imp ph (synWb th ta))) :
    Nominal.NPrf (.imp ph (synWb (synW3a et ps th) (synW3a et ch ta))) :=
  by
  have p0000 := @gBiidd ph et
  have p0001 :=
    @gN3anbi123d ph et et ps ch th ta p0000 hyp_n_3anbi12d_1 hyp_n_3anbi12d_2
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_n_3anbi1d`. -/
@[expose]
noncomputable def gN3anbi1d (ph : Wff) (ps : Wff) (ch : Wff) (th : Wff) (ta : Wff)
    (hyp_n_3anbi1d_1 : Nominal.NPrf (.imp ph (synWb ps ch))) :
    Nominal.NPrf (.imp ph (synWb (synW3a ps th ta) (synW3a ch th ta))) :=
  by
  have p0000 := @gBiidd ph th
  have p0001 := @gN3anbi12d ph ps ch th th ta hyp_n_3anbi1d_1 p0000
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_n_3anbi2d`. -/
@[expose]
noncomputable def gN3anbi2d (ph : Wff) (ps : Wff) (ch : Wff) (th : Wff) (ta : Wff)
    (hyp_n_3anbi1d_1 : Nominal.NPrf (.imp ph (synWb ps ch))) :
    Nominal.NPrf (.imp ph (synWb (synW3a th ps ta) (synW3a th ch ta))) :=
  by
  have p0000 := @gBiidd ph th
  have p0001 := @gN3anbi12d ph th th ps ch ta p0000 hyp_n_3anbi1d_1
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_n_3anbi3d`. -/
@[expose]
noncomputable def gN3anbi3d (ph : Wff) (ps : Wff) (ch : Wff) (th : Wff) (ta : Wff)
    (hyp_n_3anbi1d_1 : Nominal.NPrf (.imp ph (synWb ps ch))) :
    Nominal.NPrf (.imp ph (synWb (synW3a th ta ps) (synW3a th ta ch))) :=
  by
  have p0000 := @gBiidd ph th
  have p0001 := @gN3anbi13d ph th th ps ch ta p0000 hyp_n_3anbi1d_1
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_n_3orim123d`. -/
@[expose]
noncomputable def gN3orim123d (ph : Wff) (ps : Wff) (ch : Wff) (th : Wff) (ta : Wff)
    (et : Wff) (ze : Wff) (hyp_n_3anim123d_1 : Nominal.NPrf (.imp ph (.imp ps ch)))
    (hyp_n_3anim123d_2 : Nominal.NPrf (.imp ph (.imp th ta)))
    (hyp_n_3anim123d_3 : Nominal.NPrf (.imp ph (.imp et ze))) :
    Nominal.NPrf (.imp ph (.imp (synW3o ps th et) (synW3o ch ta ze))) :=
  by
  have p0000 := @gOrim12d ph ps ch th ta hyp_n_3anim123d_1 hyp_n_3anim123d_2
  have p0001 := @gOrim12d ph (synWo ps th) (synWo ch ta) et ze p0000 hyp_n_3anim123d_3
  have p0002 := (Nominal.biimpRefl (synW3o ps th et))
  have p0003 := (Nominal.biimpRefl (synW3o ch ta ze))
  have p0004 :=
    @gN3imtr4g ph (synWo (synWo ps th) et) (synWo (synWo ch ta) ze)
      (synW3o ps th et) (synW3o ch ta ze) p0001 p0002 p0003
  exact p0004

/-- Checked nominal proof certificate identified upstream as `g_an6`. -/
@[expose]
noncomputable def gAn6 (ph : Wff) (ps : Wff) (ch : Wff) (th : Wff) (ta : Wff)
    (et : Wff) :
    Nominal.NPrf
      (synWb (synWa (synW3a ph ps ch) (synW3a th ta et))
        (synW3a (synWa ph th) (synWa ps ta) (synWa ch et))) :=
  by
  have p0000 := @gAn4 (synWa ph ps) ch (synWa th ta) et
  have p0001 := @gAn4 ph ps th ta
  have p0002 :=
    @gAnbi1i (synWa (synWa ph ps) (synWa th ta))
      (synWa (synWa ph th) (synWa ps ta)) (synWa ch et) p0001
  have p0003 :=
    @gBitri (synWa (synWa (synWa ph ps) ch) (synWa (synWa th ta) et))
      (synWa (synWa (synWa ph ps) (synWa th ta)) (synWa ch et))
      (synWa (synWa (synWa ph th) (synWa ps ta)) (synWa ch et)) p0000 p0002
  have p0004 := (Nominal.biimpRefl (synW3a ph ps ch))
  have p0005 := (Nominal.biimpRefl (synW3a th ta et))
  have p0006 :=
    @gAnbi12i (synW3a ph ps ch) (synWa (synWa ph ps) ch) (synW3a th ta et)
      (synWa (synWa th ta) et) p0004 p0005
  have p0007 := (Nominal.biimpRefl (synW3a (synWa ph th) (synWa ps ta) (synWa ch et)))
  have p0008 :=
    @gN3bitr4i (synWa (synWa (synWa ph ps) ch) (synWa (synWa th ta) et))
      (synWa (synWa (synWa ph th) (synWa ps ta)) (synWa ch et))
      (synWa (synW3a ph ps ch) (synW3a th ta et))
      (synW3a (synWa ph th) (synWa ps ta) (synWa ch et)) p0003 p0006 p0007
  exact p0008

/-- Checked nominal proof certificate identified upstream as `g_n_3an6`. -/
@[expose]
noncomputable def gN3an6 (ph : Wff) (ps : Wff) (ch : Wff) (th : Wff) (ta : Wff)
    (et : Wff) :
    Nominal.NPrf
      (synWb (synW3a (synWa ph ps) (synWa ch th) (synWa ta et))
        (synWa (synW3a ph ch ta) (synW3a ps th et))) :=
  by
  have p0000 := @gAn6 ph ch ta ps th et
  have p0001 :=
    @gBicomi (synWa (synW3a ph ch ta) (synW3a ps th et))
      (synW3a (synWa ph ps) (synWa ch th) (synWa ta et)) p0000
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_mp3an1`. -/
@[expose]
noncomputable def gMp3an1 (ph : Wff) (ps : Wff) (ch : Wff) (th : Wff)
    (hyp_mp3an1_1 : Nominal.NPrf ph)
    (hyp_mp3an1_2 : Nominal.NPrf (.imp (synW3a ph ps ch) th)) :
    Nominal.NPrf (.imp (synWa ps ch) th) :=
  by
  have p0000 := @gN3expb ph ps ch th hyp_mp3an1_2
  have p0001 := @gMpan ph (synWa ps ch) th hyp_mp3an1_1 p0000
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_mp3an2`. -/
@[expose]
noncomputable def gMp3an2 (ph : Wff) (ps : Wff) (ch : Wff) (th : Wff)
    (hyp_mp3an2_1 : Nominal.NPrf ps)
    (hyp_mp3an2_2 : Nominal.NPrf (.imp (synW3a ph ps ch) th)) :
    Nominal.NPrf (.imp (synWa ph ch) th) :=
  by
  have p0000 := @gN3expa ph ps ch th hyp_mp3an2_2
  have p0001 := @gMpanl2 ph ps ch th hyp_mp3an2_1 p0000
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_mp3an3`. -/
@[expose]
noncomputable def gMp3an3 (ph : Wff) (ps : Wff) (ch : Wff) (th : Wff)
    (hyp_mp3an3_1 : Nominal.NPrf ch)
    (hyp_mp3an3_2 : Nominal.NPrf (.imp (synW3a ph ps ch) th)) :
    Nominal.NPrf (.imp (synWa ph ps) th) :=
  by
  have p0000 := @gN3expia ph ps ch th hyp_mp3an3_2
  have p0001 := @gMpi (synWa ph ps) ch th hyp_mp3an3_1 p0000
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_mp3an12`. -/
@[expose]
noncomputable def gMp3an12 (ph : Wff) (ps : Wff) (ch : Wff) (th : Wff)
    (hyp_mp3an12_1 : Nominal.NPrf ph) (hyp_mp3an12_2 : Nominal.NPrf ps)
    (hyp_mp3an12_3 : Nominal.NPrf (.imp (synW3a ph ps ch) th)) :
    Nominal.NPrf (.imp ch th) :=
  by
  have p0000 := @gMp3an1 ph ps ch th hyp_mp3an12_1 hyp_mp3an12_3
  have p0001 := @gMpan ps ch th hyp_mp3an12_2 p0000
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_mp3an13`. -/
@[expose]
noncomputable def gMp3an13 (ph : Wff) (ps : Wff) (ch : Wff) (th : Wff)
    (hyp_mp3an13_1 : Nominal.NPrf ph) (hyp_mp3an13_2 : Nominal.NPrf ch)
    (hyp_mp3an13_3 : Nominal.NPrf (.imp (synW3a ph ps ch) th)) :
    Nominal.NPrf (.imp ps th) :=
  by
  have p0000 := @gMp3an3 ph ps ch th hyp_mp3an13_2 hyp_mp3an13_3
  have p0001 := @gMpan ph ps th hyp_mp3an13_1 p0000
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_mp3an23`. -/
@[expose]
noncomputable def gMp3an23 (ph : Wff) (ps : Wff) (ch : Wff) (th : Wff)
    (hyp_mp3an23_1 : Nominal.NPrf ps) (hyp_mp3an23_2 : Nominal.NPrf ch)
    (hyp_mp3an23_3 : Nominal.NPrf (.imp (synW3a ph ps ch) th)) :
    Nominal.NPrf (.imp ph th) :=
  by
  have p0000 := @gMp3an3 ph ps ch th hyp_mp3an23_2 hyp_mp3an23_3
  have p0001 := @gMpan2 ph ps th hyp_mp3an23_1 p0000
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_mp3an`. -/
@[expose]
noncomputable def gMp3an (ph : Wff) (ps : Wff) (ch : Wff) (th : Wff)
    (hyp_mp3an_1 : Nominal.NPrf ph) (hyp_mp3an_2 : Nominal.NPrf ps)
    (hyp_mp3an_3 : Nominal.NPrf ch)
    (hyp_mp3an_4 : Nominal.NPrf (.imp (synW3a ph ps ch) th)) : Nominal.NPrf th :=
  by
  have p0000 := @gMp3an1 ph ps ch th hyp_mp3an_1 hyp_mp3an_4
  have p0001 := @gMp2an ps ch th hyp_mp3an_2 hyp_mp3an_3 p0000
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_mpd3an3`. -/
@[expose]
noncomputable def gMpd3an3 (ph : Wff) (ps : Wff) (ch : Wff) (th : Wff)
    (hyp_mpd3an3_2 : Nominal.NPrf (.imp (synWa ph ps) ch))
    (hyp_mpd3an3_3 : Nominal.NPrf (.imp (synW3a ph ps ch) th)) :
    Nominal.NPrf (.imp (synWa ph ps) th) :=
  by
  have p0000 := @gN3expa ph ps ch th hyp_mpd3an3_3
  have p0001 := @gMpdan (synWa ph ps) ch th hyp_mpd3an3_2 p0000
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_ecase23d`. -/
@[expose]
noncomputable def gEcase23d (ph : Wff) (ps : Wff) (ch : Wff) (th : Wff)
    (hyp_ecase23d_1 : Nominal.NPrf (.imp ph (.neg ch)))
    (hyp_ecase23d_2 : Nominal.NPrf (.imp ph (.neg th)))
    (hyp_ecase23d_3 : Nominal.NPrf (.imp ph (synW3o ps ch th))) :
    Nominal.NPrf (.imp ph ps) :=
  by
  have p0000 := @gIoran ch th
  have p0001 :=
    @gSylanbrc ph (.neg ch) (.neg th) (.neg (synWo ch th)) hyp_ecase23d_1 hyp_ecase23d_2
      p0000
  have p0002 := @gN3orass ps ch th
  have p0003 :=
    @gSylib ph (synW3o ps ch th) (synWo ps (synWo ch th)) hyp_ecase23d_3 p0002
  have p0004 := @gOrd ph ps (synWo ch th) p0003
  have p0005 := @gMt3d ph ps (synWo ch th) p0001 p0004
  exact p0005

/-- Checked nominal proof certificate identified upstream as `g_nancom`. -/
@[expose]
noncomputable def gNancom (ph : Wff) (ps : Wff) :
    Nominal.NPrf (synWb (synWnan ph ps) (synWnan ps ph)) :=
  by
  have p0000 := @gAncom ph ps
  have p0001 := @gNotbii (synWa ph ps) (synWa ps ph) p0000
  have p0002 := (Nominal.biimpRefl (synWnan ph ps))
  have p0003 := (Nominal.biimpRefl (synWnan ps ph))
  have p0004 :=
    @gN3bitr4i (.neg (synWa ph ps)) (.neg (synWa ps ph)) (synWnan ph ps)
      (synWnan ps ph) p0001 p0002 p0003
  exact p0004

/-- Checked nominal proof certificate identified upstream as `g_nanbi1`. -/
@[expose]
noncomputable def gNanbi1 (ph : Wff) (ps : Wff) (ch : Wff) :
    Nominal.NPrf (.imp (synWb ph ps) (synWb (synWnan ph ch) (synWnan ps ch))) :=
  by
  have p0000 := @gAnbi1 ph ps ch
  have p0001 := @gNotbid (synWb ph ps) (synWa ph ch) (synWa ps ch) p0000
  have p0002 := (Nominal.biimpRefl (synWnan ph ch))
  have p0003 := (Nominal.biimpRefl (synWnan ps ch))
  have p0004 :=
    @gN3bitr4g (synWb ph ps) (.neg (synWa ph ch)) (.neg (synWa ps ch))
      (synWnan ph ch) (synWnan ps ch) p0001 p0002 p0003
  exact p0004

/-- Checked nominal proof certificate identified upstream as `g_nanbi2`. -/
@[expose]
noncomputable def gNanbi2 (ph : Wff) (ps : Wff) (ch : Wff) :
    Nominal.NPrf (.imp (synWb ph ps) (synWb (synWnan ch ph) (synWnan ch ps))) :=
  by
  have p0000 := @gNanbi1 ph ps ch
  have p0001 := @gNancom ch ph
  have p0002 := @gNancom ch ps
  have p0003 :=
    @gN3bitr4g (synWb ph ps) (synWnan ph ch) (synWnan ps ch) (synWnan ch ph)
      (synWnan ch ps) p0000 p0001 p0002
  exact p0003

/-- Checked nominal proof certificate identified upstream as `g_nanbi12`. -/
@[expose]
noncomputable def gNanbi12 (ph : Wff) (ps : Wff) (ch : Wff) (th : Wff) :
    Nominal.NPrf
      (.imp (synWa (synWb ph ps) (synWb ch th))
        (synWb (synWnan ph ch) (synWnan ps th))) :=
  by
  have p0000 := @gNanbi1 ph ps ch
  have p0001 := @gNanbi2 ch th ps
  have p0002 :=
    @gSylan9bb (synWb ph ps) (synWnan ph ch) (synWnan ps ch) (synWb ch th)
      (synWnan ps th) p0000 p0001
  exact p0002

/-- Checked nominal proof certificate identified upstream as `g_nanbi2i`. -/
@[expose]
noncomputable def gNanbi2i (ph : Wff) (ps : Wff) (ch : Wff)
    (hyp_nanbii_1 : Nominal.NPrf (synWb ph ps)) :
    Nominal.NPrf (synWb (synWnan ch ph) (synWnan ch ps)) :=
  by
  have p0000 := @gNanbi2 ph ps ch
  have p0001 := Nominal.mp hyp_nanbii_1 p0000
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_nanbi1d`. -/
@[expose]
noncomputable def gNanbi1d (ph : Wff) (ps : Wff) (ch : Wff) (th : Wff)
    (hyp_nanbid_1 : Nominal.NPrf (.imp ph (synWb ps ch))) :
    Nominal.NPrf (.imp ph (synWb (synWnan ps th) (synWnan ch th))) :=
  by
  have p0000 := @gNanbi1 ps ch th
  have p0001 :=
    @gSyl ph (synWb ps ch) (synWb (synWnan ps th) (synWnan ch th)) hyp_nanbid_1 p0000
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_nanbi12d`. -/
@[expose]
noncomputable def gNanbi12d (ph : Wff) (ps : Wff) (ch : Wff) (th : Wff) (ta : Wff)
    (hyp_nanbid_1 : Nominal.NPrf (.imp ph (synWb ps ch)))
    (hyp_nanbi12d_2 : Nominal.NPrf (.imp ph (synWb th ta))) :
    Nominal.NPrf (.imp ph (synWb (synWnan ps th) (synWnan ch ta))) :=
  by
  have p0000 := @gNanbi12 ps ch th ta
  have p0001 :=
    @gSyl2anc ph (synWb ps ch) (synWb th ta) (synWb (synWnan ps th) (synWnan ch ta))
      hyp_nanbid_1 hyp_nanbi12d_2 p0000
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_tru`. -/
@[expose]
noncomputable def gTru : Nominal.NPrf synWtru :=
  by
  let ph : Wff := .falsum
  have p0000 := @gBiid ph
  have p0001 : Nominal.NPrf (Wff.biimp synWtru (synWb ph ph)) :=
    (by
      have hTrue : Nominal.NPrf synWtru := by simpa [synWtru] using (@gId Wff.falsum)
      have hRhs : Nominal.NPrf (synWb ph ph) := @gBiid ph
      exact
        @gImpbii synWtru (synWb ph ph)
          (Nominal.mp hRhs (Nominal.ax1 (synWb ph ph) synWtru))
          (Nominal.mp hTrue (Nominal.ax1 synWtru (synWb ph ph))))
  have p0002 := @gMpbir synWtru (synWb ph ph) p0000 p0001
  exact p0002

/-- Checked nominal proof certificate identified upstream as `g_trud`. -/
@[expose]
noncomputable def gTrud (ph : Wff) (hyp_trud_1 : Nominal.NPrf (.imp synWtru ph)) :
    Nominal.NPrf ph := by
  have p0000 := @gTru
  have p0001 := Nominal.mp p0000 hyp_trud_1
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_ee22`. -/
@[expose]
noncomputable def gEe22 (ph : Wff) (ps : Wff) (ch : Wff) (th : Wff) (ta : Wff)
    (hyp_ee22_1 : Nominal.NPrf (.imp ph (.imp ps ch)))
    (hyp_ee22_2 : Nominal.NPrf (.imp ph (.imp ps th)))
    (hyp_ee22_3 : Nominal.NPrf (.imp ch (.imp th ta))) :
    Nominal.NPrf (.imp ph (.imp ps ta)) :=
  by
  have p0000 := @gSyl6c ph ps ch th ta hyp_ee22_1 hyp_ee22_2 hyp_ee22_3
  exact p0000

/-- Checked nominal proof certificate identified upstream as `g_ancomsimp`. -/
@[expose]
noncomputable def gAncomsimp (ph : Wff) (ps : Wff) (ch : Wff) :
    Nominal.NPrf (synWb (.imp (synWa ph ps) ch) (.imp (synWa ps ph) ch)) :=
  by
  have p0000 := @gAncom ph ps
  have p0001 := @gImbi1i (synWa ph ps) (synWa ps ph) ch p0000
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_exp3acom23`. -/
@[expose]
noncomputable def gExp3acom23 (ph : Wff) (ps : Wff) (ch : Wff) (th : Wff)
    (hyp_exp3acom23_1 : Nominal.NPrf (.imp ph (.imp (synWa ps ch) th))) :
    Nominal.NPrf (.imp ph (.imp ch (.imp ps th))) :=
  by
  have p0000 := @gExp3a ph ps ch th hyp_exp3acom23_1
  have p0001 := @gCom23 ph ps ch th p0000
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_simplbi2com`. -/
@[expose]
noncomputable def gSimplbi2com (ph : Wff) (ps : Wff) (ch : Wff)
    (hyp_simplbi2com_1 : Nominal.NPrf (synWb ph (synWa ps ch))) :
    Nominal.NPrf (.imp ch (.imp ps ph)) :=
  by
  have p0000 := @gSimplbi2 ph ps ch hyp_simplbi2com_1
  have p0001 := @gCom12 ps ch ph p0000
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_ee10`. -/
@[expose]
noncomputable def gEe10 (ph : Wff) (ps : Wff) (ch : Wff) (th : Wff)
    (hyp_ee10_1 : Nominal.NPrf (.imp ph ps)) (hyp_ee10_2 : Nominal.NPrf ch)
    (hyp_ee10_3 : Nominal.NPrf (.imp ps (.imp ch th))) : Nominal.NPrf (.imp ph th) :=
  by
  have p0000 := @gMpi ps ch th hyp_ee10_2 hyp_ee10_3
  have p0001 := @gSyl ph ps th hyp_ee10_1 p0000
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_ee02`. -/
@[expose]
noncomputable def gEe02 (ph : Wff) (ps : Wff) (ch : Wff) (th : Wff) (ta : Wff)
    (hyp_ee02_1 : Nominal.NPrf ph) (hyp_ee02_2 : Nominal.NPrf (.imp ps (.imp ch th)))
    (hyp_ee02_3 : Nominal.NPrf (.imp ph (.imp th ta))) :
    Nominal.NPrf (.imp ps (.imp ch ta)) :=
  by
  have p0000 := @gA1i ph ps hyp_ee02_1
  have p0001 := @gSylsyld ps ph ch th ta p0000 hyp_ee02_2 hyp_ee02_3
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_merlem1`. -/
@[expose]
noncomputable def gMerlem1 (ph : Wff) (ps : Wff) (ch : Wff) (ta : Wff) :
    Nominal.NPrf (.imp (.imp (.imp ch (.imp (.neg ph) ps)) ta) (.imp ph ta)) :=
  by
  have p0000 :=
    Nominal.axMeredith (.neg ph) ps (.imp (.neg ta) (.neg ch)) (.neg (.imp (.neg ph) ps))
      ta
  have p0001 :=
    Nominal.axMeredith (.imp (.neg ph) ps)
      (.imp (.neg (.imp (.neg ta) (.neg ch))) (.neg (.neg (.imp (.neg ph) ps)))) ta ch
      (.imp (.imp ta (.neg ph)) (.imp (.neg (.imp (.neg ph) ps)) (.neg ph)))
  have p0002 := Nominal.mp p0000 p0001
  have p0003 :=
    Nominal.axMeredith ta (.neg ph) (.imp (.neg ph) ps) ph (.imp ch (.imp (.neg ph) ps))
  have p0004 := Nominal.mp p0002 p0003
  exact p0004

/-- Checked nominal proof certificate identified upstream as `g_merlem2`. -/
@[expose]
noncomputable def gMerlem2 (ph : Wff) (ch : Wff) (th : Wff) :
    Nominal.NPrf (.imp (.imp (.imp ph ph) ch) (.imp th ch)) :=
  by
  have p0000 := @gMerlem1 ph (.neg th) (.imp ch ch) ph
  have p0001 := Nominal.axMeredith ch ch ph th (.imp ph ph)
  have p0002 := Nominal.mp p0000 p0001
  exact p0002

/-- Checked nominal proof certificate identified upstream as `g_merlem3`. -/
@[expose]
noncomputable def gMerlem3 (ph : Wff) (ps : Wff) (ch : Wff) :
    Nominal.NPrf (.imp (.imp (.imp ps ch) ph) (.imp ch ph)) :=
  by
  have p0000 := @gMerlem2 (.neg ch) (.imp (.neg ch) (.neg ch)) (.imp ph ph)
  have p0001 :=
    @gMerlem2 (.imp (.neg ch) (.neg ch)) (.imp (.imp ph ph) (.imp (.neg ch) (.neg ch)))
      (.imp (.imp (.imp ch ph) (.imp (.neg ps) (.neg ps))) ps)
  have p0002 := Nominal.mp p0000 p0001
  have p0003 :=
    Nominal.axMeredith ch ph ps ps (.imp (.imp ph ph) (.imp (.neg ch) (.neg ch)))
  have p0004 := Nominal.mp p0002 p0003
  have p0005 := Nominal.axMeredith ph ph ch ch (.imp ps ch)
  have p0006 := Nominal.mp p0004 p0005
  exact p0006

/-- Checked nominal proof certificate identified upstream as `g_merlem4`. -/
@[expose]
noncomputable def gMerlem4 (ph : Wff) (th : Wff) (ta : Wff) :
    Nominal.NPrf (.imp ta (.imp (.imp ta ph) (.imp th ph))) :=
  by
  have p0000 := Nominal.axMeredith ph ph th th ta
  have p0001 :=
    @gMerlem3 (.imp (.imp ta ph) (.imp th ph))
      (.imp (.imp (.imp ph ph) (.imp (.neg th) (.neg th))) th) ta
  have p0002 := Nominal.mp p0000 p0001
  exact p0002

/-- Checked nominal proof certificate identified upstream as `g_merlem5`. -/
@[expose]
noncomputable def gMerlem5 (ph : Wff) (ps : Wff) :
    Nominal.NPrf (.imp (.imp ph ps) (.imp (.neg (.neg ph)) ps)) :=
  by
  have p0000 := Nominal.axMeredith ps ps ps ps ps
  have p0001 := Nominal.axMeredith ps ps ps (.neg (.neg ph)) ph
  have p0002 :=
    @gMerlem1 (.neg ph) ps (.imp ph ps)
      (.neg (.imp (.imp (.imp (.imp (.imp ps ps) (.imp (.neg ps) (.neg ps))) ps) ps)
          (.imp (.imp ps ps) (.imp ps ps))))
  have p0003 :=
    @gMerlem4 ph (.imp (.imp (.imp ps ps) (.imp (.neg ps) (.neg (.neg (.neg ph))))) ps)
      (.imp (.imp (.imp (.imp ph ps) (.imp (.neg (.neg ph)) ps)) (.neg
            (.imp (.imp (.imp (.imp (.imp ps ps) (.imp (.neg ps) (.neg ps))) ps) ps)
              (.imp (.imp ps ps) (.imp ps ps))))) (.imp (.neg ph) (.neg
            (.imp (.imp (.imp (.imp (.imp ps ps) (.imp (.neg ps) (.neg ps))) ps) ps)
              (.imp (.imp ps ps) (.imp ps ps))))))
  have p0004 := Nominal.mp p0002 p0003
  have p0005 :=
    Nominal.axMeredith (.imp (.imp ph ps) (.imp (.neg (.neg ph)) ps))
      (.neg (.imp (.imp (.imp (.imp (.imp ps ps) (.imp (.neg ps) (.neg ps))) ps) ps)
          (.imp (.imp ps ps) (.imp ps ps))))
      ph
      (.imp (.imp (.imp (.imp (.imp ps ps) (.imp (.neg ps) (.neg ps))) ps) ps)
        (.imp (.imp ps ps) (.imp ps ps)))
      (.imp (.imp (.imp (.imp ps ps) (.imp (.neg ps) (.neg (.neg (.neg ph))))) ps) ph)
  have p0006 := Nominal.mp p0004 p0005
  have p0007 := Nominal.mp p0001 p0006
  have p0008 := Nominal.mp p0000 p0007
  exact p0008

/-- Checked nominal proof certificate identified upstream as `g_merlem6`. -/
@[expose]
noncomputable def gMerlem6 (ph : Wff) (ps : Wff) (ch : Wff) (th : Wff) :
    Nominal.NPrf (.imp ch (.imp (.imp (.imp ps ch) ph) (.imp th ph))) :=
  by
  have p0000 := @gMerlem4 ph th (.imp ps ch)
  have p0001 := @gMerlem3 (.imp (.imp (.imp ps ch) ph) (.imp th ph)) ps ch
  have p0002 := Nominal.mp p0000 p0001
  exact p0002

/-- Checked nominal proof certificate identified upstream as `g_merlem7`. -/
@[expose]
noncomputable def gMerlem7 (ph : Wff) (ps : Wff) (ch : Wff) (th : Wff) (ta : Wff) :
    Nominal.NPrf
      (.imp ph (.imp (.imp (.imp ps ch) th)
          (.imp (.imp (.imp ch ta) (.imp (.neg th) (.neg ps))) th))) :=
  by
  have p0000 := @gMerlem4 th (.imp (.imp ch ta) (.imp (.neg th) (.neg ps))) (.imp ps ch)
  have p0001 :=
    @gMerlem6 (.neg ph) (.imp (.imp ps ch) th)
      (.imp (.imp (.imp ch ta) (.imp (.neg th) (.neg ps))) th) (.neg ch)
  have p0002 :=
    Nominal.axMeredith ch ta th ps
      (.imp (.imp (.imp (.imp (.imp ps ch) th)
            (.imp (.imp (.imp ch ta) (.imp (.neg th) (.neg ps))) th)) (.neg ph))
        (.imp (.neg ch) (.neg ph)))
  have p0003 := Nominal.mp p0001 p0002
  have p0004 :=
    Nominal.axMeredith
      (.imp (.imp (.imp ps ch) th) (.imp (.imp (.imp ch ta) (.imp (.neg th) (.neg ps))) th))
      (.neg ph) ch ph (.imp ps ch)
  have p0005 := Nominal.mp p0003 p0004
  have p0006 := Nominal.mp p0000 p0005
  exact p0006

/-- Checked nominal proof certificate identified upstream as `g_merlem8`. -/
@[expose]
noncomputable def gMerlem8 (ps : Wff) (ch : Wff) (th : Wff) (ta : Wff) :
    Nominal.NPrf
      (.imp (.imp (.imp ps ch) th) (.imp (.imp (.imp ch ta) (.imp (.neg th) (.neg ps))) th)) :=
  by
  let ph : Wff := .falsum
  have p0000 := Nominal.axMeredith ph ph ph ph ph
  have p0001 :=
    @gMerlem7
      (.imp (.imp (.imp (.imp (.imp ph ph) (.imp (.neg ph) (.neg ph))) ph) ph)
        (.imp (.imp ph ph) (.imp ph ph)))
      ps ch th ta
  have p0002 := Nominal.mp p0000 p0001
  exact p0002

/-- Checked nominal proof certificate identified upstream as `g_merlem9`. -/
@[expose]
noncomputable def gMerlem9 (ph : Wff) (ps : Wff) (ch : Wff) (th : Wff) (ta : Wff)
    (et : Wff) :
    Nominal.NPrf
      (.imp (.imp (.imp ph ps) (.imp ch (.imp th (.imp ps ta))))
        (.imp et (.imp ch (.imp th (.imp ps ta))))) :=
  by
  have p0000 := @gMerlem6 (.neg et) ch (.imp th (.imp ps ta)) (.neg ps)
  have p0001 :=
    @gMerlem8 th (.imp ps ta)
      (.imp (.imp (.imp ch (.imp th (.imp ps ta))) (.neg et)) (.imp (.neg ps) (.neg et)))
      (.imp (.neg (.imp (.neg (.imp (.imp (.imp ch (.imp th (.imp ps ta))) (.neg et))
                (.imp (.neg ps) (.neg et)))) (.neg th))) (.neg ph))
  have p0002 := Nominal.mp p0000 p0001
  have p0003 :=
    Nominal.axMeredith ps ta
      (.imp (.neg (.imp (.imp (.imp ch (.imp th (.imp ps ta))) (.neg et))
            (.imp (.neg ps) (.neg et)))) (.neg th))
      ph
      (.imp (.imp (.imp ch (.imp th (.imp ps ta))) (.neg et)) (.imp (.neg ps) (.neg et)))
  have p0004 := Nominal.mp p0002 p0003
  have p0005 :=
    Nominal.axMeredith (.imp ch (.imp th (.imp ps ta))) (.neg et) ps et (.imp ph ps)
  have p0006 := Nominal.mp p0004 p0005
  exact p0006

/-- Checked nominal proof certificate identified upstream as `g_merlem10`. -/
@[expose]
noncomputable def gMerlem10 (ph : Wff) (ps : Wff) (th : Wff) :
    Nominal.NPrf (.imp (.imp ph (.imp ph ps)) (.imp th (.imp ph ps))) :=
  by
  have p0000 := Nominal.axMeredith ph ph ph ph ph
  have p0001 := Nominal.axMeredith (.imp ph ps) ph ph th ph
  have p0002 :=
    @gMerlem9 (.imp (.imp (.imp (.imp ph ps) ph) (.imp (.neg ph) (.neg th))) ph) ph
      (.imp ph (.imp ph ps)) th ps
      (.imp (.imp (.imp (.imp (.imp ph ph) (.imp (.neg ph) (.neg ph))) ph) ph)
        (.imp (.imp ph ph) (.imp ph ph)))
  have p0003 := Nominal.mp p0001 p0002
  have p0004 := Nominal.mp p0000 p0003
  exact p0004


end NFChoice.DirectNominalPrf.WPPReplay
