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

@[expose]
noncomputable def g_ad3antrrr (ph : Wff) (ps : Wff) (ch : Wff) (th : Wff) (ta : Wff)
    (hyp_ad2ant_1 : Nominal.NPrf (.imp ph ps)) :
    Nominal.NPrf (.imp (syn_wa (syn_wa (syn_wa ph ch) th) ta) ps) :=
  by
  have p0000 := @g_adantr ph ps ch hyp_ad2ant_1
  have p0001 := @g_ad2antrr (syn_wa ph ch) ps th ta p0000
  exact p0001

@[expose]
noncomputable def g_ad2ant2l (ph : Wff) (ps : Wff) (ch : Wff) (th : Wff) (ta : Wff)
    (hyp_ad2ant2_1 : Nominal.NPrf (.imp (syn_wa ph ps) ch)) :
    Nominal.NPrf (.imp (syn_wa (syn_wa th ph) (syn_wa ta ps)) ch) :=
  by
  have p0000 := @g_adantrl ph ps ch ta hyp_ad2ant2_1
  have p0001 := @g_adantll ph (syn_wa ta ps) ch th p0000
  exact p0001

@[expose]
noncomputable def g_ad2ant2r (ph : Wff) (ps : Wff) (ch : Wff) (th : Wff) (ta : Wff)
    (hyp_ad2ant2_1 : Nominal.NPrf (.imp (syn_wa ph ps) ch)) :
    Nominal.NPrf (.imp (syn_wa (syn_wa ph th) (syn_wa ps ta)) ch) :=
  by
  have p0000 := @g_adantrr ph ps ch ta hyp_ad2ant2_1
  have p0001 := @g_adantlr ph (syn_wa ps ta) ch th p0000
  exact p0001

@[expose]
noncomputable def g_ad2ant2rl (ph : Wff) (ps : Wff) (ch : Wff) (th : Wff) (ta : Wff)
    (hyp_ad2ant2_1 : Nominal.NPrf (.imp (syn_wa ph ps) ch)) :
    Nominal.NPrf (.imp (syn_wa (syn_wa ph th) (syn_wa ta ps)) ch) :=
  by
  have p0000 := @g_adantrl ph ps ch ta hyp_ad2ant2_1
  have p0001 := @g_adantlr ph (syn_wa ta ps) ch th p0000
  exact p0001

@[expose]
noncomputable def g_simpll (ph : Wff) (ps : Wff) (ch : Wff) :
    Nominal.NPrf (.imp (syn_wa (syn_wa ph ps) ch) ph) :=
  by
  have p0000 := @g_id ph
  have p0001 := @g_ad2antrr ph ph ps ch p0000
  exact p0001

@[expose]
noncomputable def g_simplr (ph : Wff) (ps : Wff) (ch : Wff) :
    Nominal.NPrf (.imp (syn_wa (syn_wa ph ps) ch) ps) :=
  by
  have p0000 := @g_id ps
  have p0001 := @g_ad2antlr ps ps ph ch p0000
  exact p0001

@[expose]
noncomputable def g_simprl (ph : Wff) (ps : Wff) (ch : Wff) :
    Nominal.NPrf (.imp (syn_wa ph (syn_wa ps ch)) ps) :=
  by
  have p0000 := @g_id ps
  have p0001 := @g_ad2antrl ps ps ph ch p0000
  exact p0001

@[expose]
noncomputable def g_simprr (ph : Wff) (ps : Wff) (ch : Wff) :
    Nominal.NPrf (.imp (syn_wa ph (syn_wa ps ch)) ch) :=
  by
  have p0000 := @g_id ch
  have p0001 := @g_ad2antll ch ch ph ps p0000
  exact p0001

@[expose]
noncomputable def g_simplll (ph : Wff) (ps : Wff) (ch : Wff) (th : Wff) :
    Nominal.NPrf (.imp (syn_wa (syn_wa (syn_wa ph ps) ch) th) ph) :=
  by
  have p0000 := @g_simpl ph ps
  have p0001 := @g_ad2antrr (syn_wa ph ps) ph ch th p0000
  exact p0001

@[expose]
noncomputable def g_simpllr (ph : Wff) (ps : Wff) (ch : Wff) (th : Wff) :
    Nominal.NPrf (.imp (syn_wa (syn_wa (syn_wa ph ps) ch) th) ps) :=
  by
  have p0000 := @g_simpr ph ps
  have p0001 := @g_ad2antrr (syn_wa ph ps) ps ch th p0000
  exact p0001

@[expose]
noncomputable def g_simplrl (ph : Wff) (ps : Wff) (ch : Wff) (th : Wff) :
    Nominal.NPrf (.imp (syn_wa (syn_wa ph (syn_wa ps ch)) th) ps) :=
  by
  have p0000 := @g_simpl ps ch
  have p0001 := @g_ad2antlr (syn_wa ps ch) ps ph th p0000
  exact p0001

@[expose]
noncomputable def g_simplrr (ph : Wff) (ps : Wff) (ch : Wff) (th : Wff) :
    Nominal.NPrf (.imp (syn_wa (syn_wa ph (syn_wa ps ch)) th) ch) :=
  by
  have p0000 := @g_simpr ps ch
  have p0001 := @g_ad2antlr (syn_wa ps ch) ch ph th p0000
  exact p0001

@[expose]
noncomputable def g_simprll (ph : Wff) (ps : Wff) (ch : Wff) (th : Wff) :
    Nominal.NPrf (.imp (syn_wa ph (syn_wa (syn_wa ps ch) th)) ps) :=
  by
  have p0000 := @g_simpl ps ch
  have p0001 := @g_ad2antrl (syn_wa ps ch) ps ph th p0000
  exact p0001

@[expose]
noncomputable def g_simprlr (ph : Wff) (ps : Wff) (ch : Wff) (th : Wff) :
    Nominal.NPrf (.imp (syn_wa ph (syn_wa (syn_wa ps ch) th)) ch) :=
  by
  have p0000 := @g_simpr ps ch
  have p0001 := @g_ad2antrl (syn_wa ps ch) ch ph th p0000
  exact p0001

@[expose]
noncomputable def g_simprrl (ph : Wff) (ps : Wff) (ch : Wff) (th : Wff) :
    Nominal.NPrf (.imp (syn_wa ph (syn_wa ps (syn_wa ch th))) ch) :=
  by
  have p0000 := @g_simpl ch th
  have p0001 := @g_ad2antll (syn_wa ch th) ch ph ps p0000
  exact p0001

@[expose]
noncomputable def g_simprrr (ph : Wff) (ps : Wff) (ch : Wff) (th : Wff) :
    Nominal.NPrf (.imp (syn_wa ph (syn_wa ps (syn_wa ch th))) th) :=
  by
  have p0000 := @g_simpr ch th
  have p0001 := @g_ad2antll (syn_wa ch th) th ph ps p0000
  exact p0001

@[expose]
noncomputable def g_jaob (ph : Wff) (ps : Wff) (ch : Wff) :
    Nominal.NPrf (syn_wb (.imp (syn_wo ph ch) ps) (syn_wa (.imp ph ps) (.imp ch ps))) :=
  by
  have p0000 := @g_pm2_67_2 ph ps ch
  have p0001 := @g_olc ch ph
  have p0002 := @g_imim1i ch (syn_wo ph ch) ps p0001
  have p0003 := @g_jca (.imp (syn_wo ph ch) ps) (.imp ph ps) (.imp ch ps) p0000 p0002
  have p0004 := @g_pm3_44 ps ph ch
  have p0005 :=
    @g_impbii (.imp (syn_wo ph ch) ps) (syn_wa (.imp ph ps) (.imp ch ps)) p0003 p0004
  exact p0005

@[expose]
noncomputable def g_jaoian (ph : Wff) (ps : Wff) (ch : Wff) (th : Wff)
    (hyp_jaoian_1 : Nominal.NPrf (.imp (syn_wa ph ps) ch))
    (hyp_jaoian_2 : Nominal.NPrf (.imp (syn_wa th ps) ch)) :
    Nominal.NPrf (.imp (syn_wa (syn_wo ph th) ps) ch) :=
  by
  have p0000 := @g_ex ph ps ch hyp_jaoian_1
  have p0001 := @g_ex th ps ch hyp_jaoian_2
  have p0002 := @g_jaoi ph (.imp ps ch) th p0000 p0001
  have p0003 := @g_imp (syn_wo ph th) ps ch p0002
  exact p0003

@[expose]
noncomputable def g_jaodan (ph : Wff) (ps : Wff) (ch : Wff) (th : Wff)
    (hyp_jaodan_1 : Nominal.NPrf (.imp (syn_wa ph ps) ch))
    (hyp_jaodan_2 : Nominal.NPrf (.imp (syn_wa ph th) ch)) :
    Nominal.NPrf (.imp (syn_wa ph (syn_wo ps th)) ch) :=
  by
  have p0000 := @g_ex ph ps ch hyp_jaodan_1
  have p0001 := @g_ex ph th ch hyp_jaodan_2
  have p0002 := @g_jaod ph ps ch th p0000 p0001
  have p0003 := @g_imp ph (syn_wo ps th) ch p0002
  exact p0003

@[expose]
noncomputable def g_pm2_61ian (ph : Wff) (ps : Wff) (ch : Wff)
    (hyp_pm2_61ian_1 : Nominal.NPrf (.imp (syn_wa ph ps) ch))
    (hyp_pm2_61ian_2 : Nominal.NPrf (.imp (syn_wa (.neg ph) ps) ch)) :
    Nominal.NPrf (.imp ps ch) :=
  by
  have p0000 := @g_ex ph ps ch hyp_pm2_61ian_1
  have p0001 := @g_ex (.neg ph) ps ch hyp_pm2_61ian_2
  have p0002 := @g_pm2_61i ph (.imp ps ch) p0000 p0001
  exact p0002

@[expose]
noncomputable def g_pm2_61dan (ph : Wff) (ps : Wff) (ch : Wff)
    (hyp_pm2_61dan_1 : Nominal.NPrf (.imp (syn_wa ph ps) ch))
    (hyp_pm2_61dan_2 : Nominal.NPrf (.imp (syn_wa ph (.neg ps)) ch)) :
    Nominal.NPrf (.imp ph ch) :=
  by
  have p0000 := @g_ex ph ps ch hyp_pm2_61dan_1
  have p0001 := @g_ex ph (.neg ps) ch hyp_pm2_61dan_2
  have p0002 := @g_pm2_61d ph ps ch p0000 p0001
  exact p0002

@[expose]
noncomputable def g_abai (ph : Wff) (ps : Wff) :
    Nominal.NPrf (syn_wb (syn_wa ph ps) (syn_wa ph (.imp ph ps))) :=
  by
  have p0000 := @g_biimt ph ps
  have p0001 := @g_pm5_32i ph ps (.imp ph ps) p0000
  exact p0001

@[expose]
noncomputable def g_an12 (ph : Wff) (ps : Wff) (ch : Wff) :
    Nominal.NPrf (syn_wb (syn_wa ph (syn_wa ps ch)) (syn_wa ps (syn_wa ph ch))) :=
  by
  have p0000 := @g_ancom ph ps
  have p0001 := @g_anbi1i (syn_wa ph ps) (syn_wa ps ph) ch p0000
  have p0002 := @g_anass ph ps ch
  have p0003 := @g_anass ps ph ch
  have p0004 :=
    @g_n_3bitr3i (syn_wa (syn_wa ph ps) ch) (syn_wa (syn_wa ps ph) ch)
      (syn_wa ph (syn_wa ps ch)) (syn_wa ps (syn_wa ph ch)) p0001 p0002 p0003
  exact p0004

@[expose]
noncomputable def g_an32 (ph : Wff) (ps : Wff) (ch : Wff) :
    Nominal.NPrf (syn_wb (syn_wa (syn_wa ph ps) ch) (syn_wa (syn_wa ph ch) ps)) :=
  by
  have p0000 := @g_anass ph ps ch
  have p0001 := @g_an12 ph ps ch
  have p0002 := @g_ancom ps (syn_wa ph ch)
  have p0003 :=
    @g_n_3bitri (syn_wa (syn_wa ph ps) ch) (syn_wa ph (syn_wa ps ch))
      (syn_wa ps (syn_wa ph ch)) (syn_wa (syn_wa ph ch) ps) p0000 p0001 p0002
  exact p0003

@[expose]
noncomputable def g_an13 (ph : Wff) (ps : Wff) (ch : Wff) :
    Nominal.NPrf (syn_wb (syn_wa ph (syn_wa ps ch)) (syn_wa ch (syn_wa ps ph))) :=
  by
  have p0000 := @g_an12 ph ps ch
  have p0001 := @g_anass ps ph ch
  have p0002 := @g_ancom (syn_wa ps ph) ch
  have p0003 :=
    @g_n_3bitr2i (syn_wa ph (syn_wa ps ch)) (syn_wa ps (syn_wa ph ch))
      (syn_wa (syn_wa ps ph) ch) (syn_wa ch (syn_wa ps ph)) p0000 p0001 p0002
  exact p0003

@[expose]
noncomputable def g_an12s (ph : Wff) (ps : Wff) (ch : Wff) (th : Wff)
    (hyp_an12s_1 : Nominal.NPrf (.imp (syn_wa ph (syn_wa ps ch)) th)) :
    Nominal.NPrf (.imp (syn_wa ps (syn_wa ph ch)) th) :=
  by
  have p0000 := @g_an12 ps ph ch
  have p0001 :=
    @g_sylbi (syn_wa ps (syn_wa ph ch)) (syn_wa ph (syn_wa ps ch)) th p0000 hyp_an12s_1
  exact p0001

@[expose]
noncomputable def g_ancom2s (ph : Wff) (ps : Wff) (ch : Wff) (th : Wff)
    (hyp_an12s_1 : Nominal.NPrf (.imp (syn_wa ph (syn_wa ps ch)) th)) :
    Nominal.NPrf (.imp (syn_wa ph (syn_wa ch ps)) th) :=
  by
  have p0000 := @g_pm3_22 ch ps
  have p0001 := @g_sylan2 (syn_wa ch ps) ph (syn_wa ps ch) th p0000 hyp_an12s_1
  exact p0001

@[expose]
noncomputable def g_an32s (ph : Wff) (ps : Wff) (ch : Wff) (th : Wff)
    (hyp_an32s_1 : Nominal.NPrf (.imp (syn_wa (syn_wa ph ps) ch) th)) :
    Nominal.NPrf (.imp (syn_wa (syn_wa ph ch) ps) th) :=
  by
  have p0000 := @g_an32 ph ch ps
  have p0001 :=
    @g_sylbi (syn_wa (syn_wa ph ch) ps) (syn_wa (syn_wa ph ps) ch) th p0000 hyp_an32s_1
  exact p0001

@[expose]
noncomputable def g_anabsan (ph : Wff) (ps : Wff) (ch : Wff)
    (hyp_anabsan_1 : Nominal.NPrf (.imp (syn_wa (syn_wa ph ph) ps) ch)) :
    Nominal.NPrf (.imp (syn_wa ph ps) ch) :=
  by
  have p0000 := @g_pm4_24 ph
  have p0001 := @g_sylanb ph (syn_wa ph ph) ps ch p0000 hyp_anabsan_1
  exact p0001

@[expose]
noncomputable def g_anabss1 (ph : Wff) (ps : Wff) (ch : Wff)
    (hyp_anabss1_1 : Nominal.NPrf (.imp (syn_wa (syn_wa ph ps) ph) ch)) :
    Nominal.NPrf (.imp (syn_wa ph ps) ch) :=
  by
  have p0000 := @g_an32s ph ps ph ch hyp_anabss1_1
  have p0001 := @g_anabsan ph ps ch p0000
  exact p0001

@[expose]
noncomputable def g_anabss4 (ph : Wff) (ps : Wff) (ch : Wff)
    (hyp_anabss4_1 : Nominal.NPrf (.imp (syn_wa (syn_wa ps ph) ps) ch)) :
    Nominal.NPrf (.imp (syn_wa ph ps) ch) :=
  by
  have p0000 := @g_anabss1 ps ph ch hyp_anabss4_1
  have p0001 := @g_ancoms ps ph ch p0000
  exact p0001

@[expose]
noncomputable def g_anabss5 (ph : Wff) (ps : Wff) (ch : Wff)
    (hyp_anabss5_1 : Nominal.NPrf (.imp (syn_wa ph (syn_wa ph ps)) ch)) :
    Nominal.NPrf (.imp (syn_wa ph ps) ch) :=
  by
  have p0000 := @g_anassrs ph ph ps ch hyp_anabss5_1
  have p0001 := @g_anabsan ph ps ch p0000
  exact p0001

@[expose]
noncomputable def g_anabsi5 (ph : Wff) (ps : Wff) (ch : Wff)
    (hyp_anabsi5_1 : Nominal.NPrf (.imp ph (.imp (syn_wa ph ps) ch))) :
    Nominal.NPrf (.imp (syn_wa ph ps) ch) :=
  by
  have p0000 := @g_imp ph (syn_wa ph ps) ch hyp_anabsi5_1
  have p0001 := @g_anabss5 ph ps ch p0000
  exact p0001

@[expose]
noncomputable def g_anabsi6 (ph : Wff) (ps : Wff) (ch : Wff)
    (hyp_anabsi6_1 : Nominal.NPrf (.imp ph (.imp (syn_wa ps ph) ch))) :
    Nominal.NPrf (.imp (syn_wa ph ps) ch) :=
  by
  have p0000 := @g_ancomsd ph ps ph ch hyp_anabsi6_1
  have p0001 := @g_anabsi5 ph ps ch p0000
  exact p0001

@[expose]
noncomputable def g_anabsi7 (ph : Wff) (ps : Wff) (ch : Wff)
    (hyp_anabsi7_1 : Nominal.NPrf (.imp ps (.imp (syn_wa ph ps) ch))) :
    Nominal.NPrf (.imp (syn_wa ph ps) ch) :=
  by
  have p0000 := @g_anabsi6 ps ph ch hyp_anabsi7_1
  have p0001 := @g_ancoms ps ph ch p0000
  exact p0001

@[expose]
noncomputable def g_anabss7 (ph : Wff) (ps : Wff) (ch : Wff)
    (hyp_anabss7_1 : Nominal.NPrf (.imp (syn_wa ps (syn_wa ph ps)) ch)) :
    Nominal.NPrf (.imp (syn_wa ph ps) ch) :=
  by
  have p0000 := @g_anassrs ps ph ps ch hyp_anabss7_1
  have p0001 := @g_anabss4 ph ps ch p0000
  exact p0001

@[expose]
noncomputable def g_anabsan2 (ph : Wff) (ps : Wff) (ch : Wff)
    (hyp_anabsan2_1 : Nominal.NPrf (.imp (syn_wa ph (syn_wa ps ps)) ch)) :
    Nominal.NPrf (.imp (syn_wa ph ps) ch) :=
  by
  have p0000 := @g_an12s ph ps ps ch hyp_anabsan2_1
  have p0001 := @g_anabss7 ph ps ch p0000
  exact p0001

@[expose]
noncomputable def g_anabss3 (ph : Wff) (ps : Wff) (ch : Wff)
    (hyp_anabss3_1 : Nominal.NPrf (.imp (syn_wa (syn_wa ph ps) ps) ch)) :
    Nominal.NPrf (.imp (syn_wa ph ps) ch) :=
  by
  have p0000 := @g_anasss ph ps ps ch hyp_anabss3_1
  have p0001 := @g_anabsan2 ph ps ch p0000
  exact p0001

@[expose]
noncomputable def g_an4 (ph : Wff) (ps : Wff) (ch : Wff) (th : Wff) :
    Nominal.NPrf
      (syn_wb (syn_wa (syn_wa ph ps) (syn_wa ch th)) (syn_wa (syn_wa ph ch) (syn_wa ps th))) :=
  by
  have p0000 := @g_an12 ps ch th
  have p0001 := @g_anbi2i (syn_wa ps (syn_wa ch th)) (syn_wa ch (syn_wa ps th)) ph p0000
  have p0002 := @g_anass ph ps (syn_wa ch th)
  have p0003 := @g_anass ph ch (syn_wa ps th)
  have p0004 :=
    @g_n_3bitr4i (syn_wa ph (syn_wa ps (syn_wa ch th)))
      (syn_wa ph (syn_wa ch (syn_wa ps th))) (syn_wa (syn_wa ph ps) (syn_wa ch th))
      (syn_wa (syn_wa ph ch) (syn_wa ps th)) p0001 p0002 p0003
  exact p0004

@[expose]
noncomputable def g_an42 (ph : Wff) (ps : Wff) (ch : Wff) (th : Wff) :
    Nominal.NPrf
      (syn_wb (syn_wa (syn_wa ph ps) (syn_wa ch th)) (syn_wa (syn_wa ph ch) (syn_wa th ps))) :=
  by
  have p0000 := @g_an4 ph ps ch th
  have p0001 := @g_ancom ps th
  have p0002 := @g_anbi2i (syn_wa ps th) (syn_wa th ps) (syn_wa ph ch) p0001
  have p0003 :=
    @g_bitri (syn_wa (syn_wa ph ps) (syn_wa ch th)) (syn_wa (syn_wa ph ch) (syn_wa ps th))
      (syn_wa (syn_wa ph ch) (syn_wa th ps)) p0000 p0002
  exact p0003

@[expose]
noncomputable def g_an4s (ph : Wff) (ps : Wff) (ch : Wff) (th : Wff) (ta : Wff)
    (hyp_an4s_1 : Nominal.NPrf (.imp (syn_wa (syn_wa ph ps) (syn_wa ch th)) ta)) :
    Nominal.NPrf (.imp (syn_wa (syn_wa ph ch) (syn_wa ps th)) ta) :=
  by
  have p0000 := @g_an4 ph ch ps th
  have p0001 :=
    @g_sylbi (syn_wa (syn_wa ph ch) (syn_wa ps th)) (syn_wa (syn_wa ph ps) (syn_wa ch th))
      ta p0000 hyp_an4s_1
  exact p0001

@[expose]
noncomputable def g_anandi (ph : Wff) (ps : Wff) (ch : Wff) :
    Nominal.NPrf
      (syn_wb (syn_wa ph (syn_wa ps ch)) (syn_wa (syn_wa ph ps) (syn_wa ph ch))) :=
  by
  have p0000 := @g_anidm ph
  have p0001 := @g_anbi1i (syn_wa ph ph) ph (syn_wa ps ch) p0000
  have p0002 := @g_an4 ph ph ps ch
  have p0003 :=
    @g_bitr3i (syn_wa ph (syn_wa ps ch)) (syn_wa (syn_wa ph ph) (syn_wa ps ch))
      (syn_wa (syn_wa ph ps) (syn_wa ph ch)) p0001 p0002
  exact p0003

@[expose]
noncomputable def g_anandir (ph : Wff) (ps : Wff) (ch : Wff) :
    Nominal.NPrf
      (syn_wb (syn_wa (syn_wa ph ps) ch) (syn_wa (syn_wa ph ch) (syn_wa ps ch))) :=
  by
  have p0000 := @g_anidm ch
  have p0001 := @g_anbi2i (syn_wa ch ch) ch (syn_wa ph ps) p0000
  have p0002 := @g_an4 ph ps ch ch
  have p0003 :=
    @g_bitr3i (syn_wa (syn_wa ph ps) ch) (syn_wa (syn_wa ph ps) (syn_wa ch ch))
      (syn_wa (syn_wa ph ch) (syn_wa ps ch)) p0001 p0002
  exact p0003

@[expose]
noncomputable def g_anandis (ph : Wff) (ps : Wff) (ch : Wff) (ta : Wff)
    (hyp_anandis_1 : Nominal.NPrf (.imp (syn_wa (syn_wa ph ps) (syn_wa ph ch)) ta)) :
    Nominal.NPrf (.imp (syn_wa ph (syn_wa ps ch)) ta) :=
  by
  have p0000 := @g_an4s ph ps ph ch ta hyp_anandis_1
  have p0001 := @g_anabsan ph (syn_wa ps ch) ta p0000
  exact p0001

@[expose]
noncomputable def g_impbida (ph : Wff) (ps : Wff) (ch : Wff)
    (hyp_impbida_1 : Nominal.NPrf (.imp (syn_wa ph ps) ch))
    (hyp_impbida_2 : Nominal.NPrf (.imp (syn_wa ph ch) ps)) :
    Nominal.NPrf (.imp ph (syn_wb ps ch)) :=
  by
  have p0000 := @g_ex ph ps ch hyp_impbida_1
  have p0001 := @g_ex ph ch ps hyp_impbida_2
  have p0002 := @g_impbid ph ps ch p0000 p0001
  exact p0002

@[expose]
noncomputable def g_pm3_48 (ph : Wff) (ps : Wff) (ch : Wff) (th : Wff) :
    Nominal.NPrf
      (.imp (syn_wa (.imp ph ps) (.imp ch th)) (.imp (syn_wo ph ch) (syn_wo ps th))) :=
  by
  have p0000 := @g_orc ps th
  have p0001 := @g_imim2i ps (syn_wo ps th) ph p0000
  have p0002 := @g_olc th ps
  have p0003 := @g_imim2i th (syn_wo ps th) ch p0002
  have p0004 := @g_jaao (.imp ph ps) ph (syn_wo ps th) (.imp ch th) ch p0001 p0003
  exact p0004

@[expose]
noncomputable def g_im2anan9 (ph : Wff) (ps : Wff) (ch : Wff) (th : Wff) (ta : Wff)
    (et : Wff) (hyp_im2an9_1 : Nominal.NPrf (.imp ph (.imp ps ch)))
    (hyp_im2an9_2 : Nominal.NPrf (.imp th (.imp ta et))) :
    Nominal.NPrf (.imp (syn_wa ph th) (.imp (syn_wa ps ta) (syn_wa ch et))) :=
  by
  have p0000 := @g_adantr ph (.imp ps ch) th hyp_im2an9_1
  have p0001 := @g_adantl th (.imp ta et) ph hyp_im2an9_2
  have p0002 := @g_anim12d (syn_wa ph th) ps ch ta et p0000 p0001
  exact p0002

@[expose]
noncomputable def g_anim12dan (ph : Wff) (ps : Wff) (ch : Wff) (th : Wff) (ta : Wff)
    (hyp_anim12dan_1 : Nominal.NPrf (.imp (syn_wa ph ps) ch))
    (hyp_anim12dan_2 : Nominal.NPrf (.imp (syn_wa ph th) ta)) :
    Nominal.NPrf (.imp (syn_wa ph (syn_wa ps th)) (syn_wa ch ta)) :=
  by
  have p0000 := @g_ex ph ps ch hyp_anim12dan_1
  have p0001 := @g_ex ph th ta hyp_anim12dan_2
  have p0002 := @g_anim12d ph ps ch th ta p0000 p0001
  have p0003 := @g_imp ph (syn_wa ps th) (syn_wa ch ta) p0002
  exact p0003

@[expose]
noncomputable def g_orim12d (ph : Wff) (ps : Wff) (ch : Wff) (th : Wff) (ta : Wff)
    (hyp_orim12d_1 : Nominal.NPrf (.imp ph (.imp ps ch)))
    (hyp_orim12d_2 : Nominal.NPrf (.imp ph (.imp th ta))) :
    Nominal.NPrf (.imp ph (.imp (syn_wo ps th) (syn_wo ch ta))) :=
  by
  have p0000 := @g_pm3_48 ps ch th ta
  have p0001 :=
    @g_syl2anc ph (.imp ps ch) (.imp th ta) (.imp (syn_wo ps th) (syn_wo ch ta))
      hyp_orim12d_1 hyp_orim12d_2 p0000
  exact p0001

@[expose]
noncomputable def g_orim1d (ph : Wff) (ps : Wff) (ch : Wff) (th : Wff)
    (hyp_orim1d_1 : Nominal.NPrf (.imp ph (.imp ps ch))) :
    Nominal.NPrf (.imp ph (.imp (syn_wo ps th) (syn_wo ch th))) :=
  by
  have p0000 := @g_idd ph th
  have p0001 := @g_orim12d ph ps ch th th hyp_orim1d_1 p0000
  exact p0001

@[expose]
noncomputable def g_pm3_43 (ph : Wff) (ps : Wff) (ch : Wff) :
    Nominal.NPrf (.imp (syn_wa (.imp ph ps) (.imp ph ch)) (.imp ph (syn_wa ps ch))) :=
  by
  have p0000 := @g_pm3_43i ph ps ch
  have p0001 := @g_imp (.imp ph ps) (.imp ph ch) (.imp ph (syn_wa ps ch)) p0000
  exact p0001

@[expose]
noncomputable def g_jcab (ph : Wff) (ps : Wff) (ch : Wff) :
    Nominal.NPrf (syn_wb (.imp ph (syn_wa ps ch)) (syn_wa (.imp ph ps) (.imp ph ch))) :=
  by
  have p0000 := @g_simpl ps ch
  have p0001 := @g_imim2i (syn_wa ps ch) ps ph p0000
  have p0002 := @g_simpr ps ch
  have p0003 := @g_imim2i (syn_wa ps ch) ch ph p0002
  have p0004 := @g_jca (.imp ph (syn_wa ps ch)) (.imp ph ps) (.imp ph ch) p0001 p0003
  have p0005 := @g_pm3_43 ph ps ch
  have p0006 :=
    @g_impbii (.imp ph (syn_wa ps ch)) (syn_wa (.imp ph ps) (.imp ph ch)) p0004 p0005
  exact p0006

@[expose]
noncomputable def g_ordi (ph : Wff) (ps : Wff) (ch : Wff) :
    Nominal.NPrf
      (syn_wb (syn_wo ph (syn_wa ps ch)) (syn_wa (syn_wo ph ps) (syn_wo ph ch))) :=
  by
  have p0000 := @g_jcab (.neg ph) ps ch
  have p0001 := (Nominal.biimpRefl (syn_wo ph (syn_wa ps ch)))
  have p0002 := (Nominal.biimpRefl (syn_wo ph ps))
  have p0003 := (Nominal.biimpRefl (syn_wo ph ch))
  have p0004 :=
    @g_anbi12i (syn_wo ph ps) (.imp (.neg ph) ps) (syn_wo ph ch) (.imp (.neg ph) ch) p0002
      p0003
  have p0005 :=
    @g_n_3bitr4i (.imp (.neg ph) (syn_wa ps ch))
      (syn_wa (.imp (.neg ph) ps) (.imp (.neg ph) ch)) (syn_wo ph (syn_wa ps ch))
      (syn_wa (syn_wo ph ps) (syn_wo ph ch)) p0000 p0001 p0004
  exact p0005

@[expose]
noncomputable def g_andi (ph : Wff) (ps : Wff) (ch : Wff) :
    Nominal.NPrf
      (syn_wb (syn_wa ph (syn_wo ps ch)) (syn_wo (syn_wa ph ps) (syn_wa ph ch))) :=
  by
  have p0000 := @g_orc (syn_wa ph ps) (syn_wa ph ch)
  have p0001 := @g_olc (syn_wa ph ch) (syn_wa ph ps)
  have p0002 := @g_jaodan ph ps (syn_wo (syn_wa ph ps) (syn_wa ph ch)) ch p0000 p0001
  have p0003 := @g_orc ps ch
  have p0004 := @g_anim2i ps (syn_wo ps ch) ph p0003
  have p0005 := @g_olc ch ps
  have p0006 := @g_anim2i ch (syn_wo ps ch) ph p0005
  have p0007 :=
    @g_jaoi (syn_wa ph ps) (syn_wa ph (syn_wo ps ch)) (syn_wa ph ch) p0004 p0006
  have p0008 :=
    @g_impbii (syn_wa ph (syn_wo ps ch)) (syn_wo (syn_wa ph ps) (syn_wa ph ch)) p0002
      p0007
  exact p0008

@[expose]
noncomputable def g_andir (ph : Wff) (ps : Wff) (ch : Wff) :
    Nominal.NPrf
      (syn_wb (syn_wa (syn_wo ph ps) ch) (syn_wo (syn_wa ph ch) (syn_wa ps ch))) :=
  by
  have p0000 := @g_andi ch ph ps
  have p0001 := @g_ancom (syn_wo ph ps) ch
  have p0002 := @g_ancom ph ch
  have p0003 := @g_ancom ps ch
  have p0004 :=
    @g_orbi12i (syn_wa ph ch) (syn_wa ch ph) (syn_wa ps ch) (syn_wa ch ps) p0002 p0003
  have p0005 :=
    @g_n_3bitr4i (syn_wa ch (syn_wo ph ps)) (syn_wo (syn_wa ch ph) (syn_wa ch ps))
      (syn_wa (syn_wo ph ps) ch) (syn_wo (syn_wa ph ch) (syn_wa ps ch)) p0000 p0001 p0004
  exact p0005

@[expose]
noncomputable def g_anddi (ph : Wff) (ps : Wff) (ch : Wff) (th : Wff) :
    Nominal.NPrf
      (syn_wb (syn_wa (syn_wo ph ps) (syn_wo ch th))
        (syn_wo (syn_wo (syn_wa ph ch) (syn_wa ph th))
          (syn_wo (syn_wa ps ch) (syn_wa ps th)))) :=
  by
  have p0000 := @g_andir ph ps (syn_wo ch th)
  have p0001 := @g_andi ph ch th
  have p0002 := @g_andi ps ch th
  have p0003 :=
    @g_orbi12i (syn_wa ph (syn_wo ch th)) (syn_wo (syn_wa ph ch) (syn_wa ph th))
      (syn_wa ps (syn_wo ch th)) (syn_wo (syn_wa ps ch) (syn_wa ps th)) p0001 p0002
  have p0004 :=
    @g_bitri (syn_wa (syn_wo ph ps) (syn_wo ch th))
      (syn_wo (syn_wa ph (syn_wo ch th)) (syn_wa ps (syn_wo ch th)))
      (syn_wo (syn_wo (syn_wa ph ch) (syn_wa ph th)) (syn_wo (syn_wa ps ch) (syn_wa ps th)))
      p0000 p0003
  exact p0004

@[expose]
noncomputable def g_bi2anan9 (ph : Wff) (ps : Wff) (ch : Wff) (th : Wff) (ta : Wff)
    (et : Wff) (hyp_bi2an9_1 : Nominal.NPrf (.imp ph (syn_wb ps ch)))
    (hyp_bi2an9_2 : Nominal.NPrf (.imp th (syn_wb ta et))) :
    Nominal.NPrf (.imp (syn_wa ph th) (syn_wb (syn_wa ps ta) (syn_wa ch et))) :=
  by
  have p0000 := @g_anbi1d ph ps ch ta hyp_bi2an9_1
  have p0001 := @g_anbi2d th ta et ch hyp_bi2an9_2
  have p0002 := @g_sylan9bb ph (syn_wa ps ta) (syn_wa ch ta) th (syn_wa ch et) p0000 p0001
  exact p0002

@[expose]
noncomputable def g_pm4_72 (ph : Wff) (ps : Wff) :
    Nominal.NPrf (syn_wb (.imp ph ps) (syn_wb ps (syn_wo ph ps))) :=
  by
  have p0000 := @g_olc ps ph
  have p0001 := @g_pm2_621 ph ps
  have p0002 := @g_impbid2 (.imp ph ps) ps (syn_wo ph ps) p0000 p0001
  have p0003 := @g_orc ph ps
  have p0004 := @g_bi2 ps (syn_wo ph ps)
  have p0005 := @g_syl5 ph (syn_wo ph ps) (syn_wb ps (syn_wo ph ps)) ps p0003 p0004
  have p0006 := @g_impbii (.imp ph ps) (syn_wb ps (syn_wo ph ps)) p0002 p0005
  exact p0006

@[expose]
noncomputable def g_bianabs (ph : Wff) (ps : Wff) (ch : Wff)
    (hyp_bianabs_1 : Nominal.NPrf (.imp ph (syn_wb ps (syn_wa ph ch)))) :
    Nominal.NPrf (.imp ph (syn_wb ps ch)) :=
  by
  have p0000 := @g_ibar ph ch
  have p0001 := @g_bitr4d ph ps (syn_wa ph ch) ch hyp_bianabs_1 p0000
  exact p0001

@[expose]
noncomputable def g_pm3_24 (ph : Wff) : Nominal.NPrf (.neg (syn_wa ph (.neg ph))) :=
  by
  have p0000 := @g_id ph
  have p0001 := @g_iman ph ph
  have p0002 := @g_mpbi (.imp ph ph) (.neg (syn_wa ph (.neg ph))) p0000 p0001
  exact p0002

@[expose]
noncomputable def g_xor (ph : Wff) (ps : Wff) :
    Nominal.NPrf
      (syn_wb (.neg (syn_wb ph ps)) (syn_wo (syn_wa ph (.neg ps)) (syn_wa ps (.neg ph)))) :=
  by
  have p0000 := @g_iman ph ps
  have p0001 := @g_iman ps ph
  have p0002 :=
    @g_anbi12i (.imp ph ps) (.neg (syn_wa ph (.neg ps))) (.imp ps ph)
      (.neg (syn_wa ps (.neg ph))) p0000 p0001
  have p0003 := @g_dfbi2 ph ps
  have p0004 := @g_ioran (syn_wa ph (.neg ps)) (syn_wa ps (.neg ph))
  have p0005 :=
    @g_n_3bitr4ri (syn_wa (.imp ph ps) (.imp ps ph))
      (syn_wa (.neg (syn_wa ph (.neg ps))) (.neg (syn_wa ps (.neg ph)))) (syn_wb ph ps)
      (.neg (syn_wo (syn_wa ph (.neg ps)) (syn_wa ps (.neg ph)))) p0002 p0003 p0004
  have p0006 :=
    @g_con1bii (syn_wo (syn_wa ph (.neg ps)) (syn_wa ps (.neg ph))) (syn_wb ph ps) p0005
  exact p0006

@[expose]
noncomputable def g_dfbi3 (ph : Wff) (ps : Wff) :
    Nominal.NPrf
      (syn_wb (syn_wb ph ps) (syn_wo (syn_wa ph ps) (syn_wa (.neg ph) (.neg ps)))) :=
  by
  have p0000 := @g_xor ph (.neg ps)
  have p0001 := @g_pm5_18 ph ps
  have p0002 := @g_notnot ps
  have p0003 := @g_anbi2i ps (.neg (.neg ps)) ph p0002
  have p0004 := @g_ancom (.neg ph) (.neg ps)
  have p0005 :=
    @g_orbi12i (syn_wa ph ps) (syn_wa ph (.neg (.neg ps))) (syn_wa (.neg ph) (.neg ps))
      (syn_wa (.neg ps) (.neg ph)) p0003 p0004
  have p0006 :=
    @g_n_3bitr4i (.neg (syn_wb ph (.neg ps)))
      (syn_wo (syn_wa ph (.neg (.neg ps))) (syn_wa (.neg ps) (.neg ph))) (syn_wb ph ps)
      (syn_wo (syn_wa ph ps) (syn_wa (.neg ph) (.neg ps))) p0000 p0001 p0005
  exact p0006

@[expose]
noncomputable def g_xordi (ph : Wff) (ps : Wff) (ch : Wff) :
    Nominal.NPrf
      (syn_wb (syn_wa ph (.neg (syn_wb ps ch)))
        (.neg (syn_wb (syn_wa ph ps) (syn_wa ph ch)))) :=
  by
  have p0000 := @g_annim ph (syn_wb ps ch)
  have p0001 := @g_pm5_32 ph ps ch
  have p0002 :=
    @g_xchbinx (syn_wa ph (.neg (syn_wb ps ch))) (.imp ph (syn_wb ps ch))
      (syn_wb (syn_wa ph ps) (syn_wa ph ch)) p0000 p0001
  exact p0002

@[expose]
noncomputable def g_pm5_21nd (ph : Wff) (ps : Wff) (ch : Wff) (th : Wff)
    (hyp_pm5_21nd_1 : Nominal.NPrf (.imp (syn_wa ph ps) th))
    (hyp_pm5_21nd_2 : Nominal.NPrf (.imp (syn_wa ph ch) th))
    (hyp_pm5_21nd_3 : Nominal.NPrf (.imp th (syn_wb ps ch))) :
    Nominal.NPrf (.imp ph (syn_wb ps ch)) :=
  by
  have p0000 := @g_ex ph ps th hyp_pm5_21nd_1
  have p0001 := @g_ex ph ch th hyp_pm5_21nd_2
  have p0002 := @g_a1i (.imp th (syn_wb ps ch)) ph hyp_pm5_21nd_3
  have p0003 := @g_pm5_21ndd ph th ps ch p0000 p0001 p0002
  exact p0003

@[expose]
noncomputable def g_baib (ph : Wff) (ps : Wff) (ch : Wff)
    (hyp_baib_1 : Nominal.NPrf (syn_wb ph (syn_wa ps ch))) :
    Nominal.NPrf (.imp ps (syn_wb ph ch)) :=
  by
  have p0000 := @g_ibar ps ch
  have p0001 := @g_syl6rbbr ps ch (syn_wa ps ch) ph p0000 hyp_baib_1
  exact p0001

@[expose]
noncomputable def g_baibr (ph : Wff) (ps : Wff) (ch : Wff)
    (hyp_baib_1 : Nominal.NPrf (syn_wb ph (syn_wa ps ch))) :
    Nominal.NPrf (.imp ps (syn_wb ch ph)) :=
  by
  have p0000 := @g_baib ph ps ch hyp_baib_1
  have p0001 := @g_bicomd ps ph ch p0000
  exact p0001

@[expose]
noncomputable def g_pm5_6 (ph : Wff) (ps : Wff) (ch : Wff) :
    Nominal.NPrf (syn_wb (.imp (syn_wa ph (.neg ps)) ch) (.imp ph (syn_wo ps ch))) :=
  by
  have p0000 := @g_impexp ph (.neg ps) ch
  have p0001 := (Nominal.biimpRefl (syn_wo ps ch))
  have p0002 := @g_imbi2i (syn_wo ps ch) (.imp (.neg ps) ch) ph p0001
  have p0003 :=
    @g_bitr4i (.imp (syn_wa ph (.neg ps)) ch) (.imp ph (.imp (.neg ps) ch))
      (.imp ph (syn_wo ps ch)) p0000 p0002
  exact p0003

@[expose]
noncomputable def g_orcanai (ph : Wff) (ps : Wff) (ch : Wff)
    (hyp_orcanai_1 : Nominal.NPrf (.imp ph (syn_wo ps ch))) :
    Nominal.NPrf (.imp (syn_wa ph (.neg ps)) ch) :=
  by
  have p0000 := @g_ord ph ps ch hyp_orcanai_1
  have p0001 := @g_imp ph (.neg ps) ch p0000
  exact p0001

@[expose]
noncomputable def g_intnan (ph : Wff) (ps : Wff) (hyp_intnan_1 : Nominal.NPrf (.neg ph)) :
    Nominal.NPrf (.neg (syn_wa ps ph)) :=
  by
  have p0000 := @g_simpr ps ph
  have p0001 := @g_mto (syn_wa ps ph) ph hyp_intnan_1 p0000
  exact p0001

@[expose]
noncomputable def g_intnanr (ph : Wff) (ps : Wff)
    (hyp_intnan_1 : Nominal.NPrf (.neg ph)) : Nominal.NPrf (.neg (syn_wa ph ps)) :=
  by
  have p0000 := @g_simpl ph ps
  have p0001 := @g_mto (syn_wa ph ps) ph hyp_intnan_1 p0000
  exact p0001

@[expose]
noncomputable def g_intnand (ph : Wff) (ps : Wff) (ch : Wff)
    (hyp_intnand_1 : Nominal.NPrf (.imp ph (.neg ps))) :
    Nominal.NPrf (.imp ph (.neg (syn_wa ch ps))) :=
  by
  have p0000 := @g_simpr ch ps
  have p0001 := @g_nsyl ph ps (syn_wa ch ps) hyp_intnand_1 p0000
  exact p0001

@[expose]
noncomputable def g_intnanrd (ph : Wff) (ps : Wff) (ch : Wff)
    (hyp_intnand_1 : Nominal.NPrf (.imp ph (.neg ps))) :
    Nominal.NPrf (.imp ph (.neg (syn_wa ps ch))) :=
  by
  have p0000 := @g_simpl ps ch
  have p0001 := @g_nsyl ph ps (syn_wa ps ch) hyp_intnand_1 p0000
  exact p0001

@[expose]
noncomputable def g_mpbiran (ph : Wff) (ps : Wff) (ch : Wff)
    (hyp_mpbiran_1 : Nominal.NPrf ps)
    (hyp_mpbiran_2 : Nominal.NPrf (syn_wb ph (syn_wa ps ch))) :
    Nominal.NPrf (syn_wb ph ch) :=
  by
  have p0000 := @g_biantrur ps ch hyp_mpbiran_1
  have p0001 := @g_bitr4i ph (syn_wa ps ch) ch hyp_mpbiran_2 p0000
  exact p0001

@[expose]
noncomputable def g_mpbiran2 (ph : Wff) (ps : Wff) (ch : Wff)
    (hyp_mpbiran2_1 : Nominal.NPrf ch)
    (hyp_mpbiran2_2 : Nominal.NPrf (syn_wb ph (syn_wa ps ch))) :
    Nominal.NPrf (syn_wb ph ps) :=
  by
  have p0000 := @g_biantru ch ps hyp_mpbiran2_1
  have p0001 := @g_bitr4i ph (syn_wa ps ch) ps hyp_mpbiran2_2 p0000
  exact p0001

@[expose]
noncomputable def g_mpbir2an (ph : Wff) (ps : Wff) (ch : Wff)
    (hyp_mpbir2an_1 : Nominal.NPrf ps) (hyp_mpbir2an_2 : Nominal.NPrf ch)
    (hyp_mpbiran2an_1 : Nominal.NPrf (syn_wb ph (syn_wa ps ch))) : Nominal.NPrf ph :=
  by
  have p0000 := @g_mpbiran ph ps ch hyp_mpbir2an_1 hyp_mpbiran2an_1
  have p0001 := @g_mpbir ph ch hyp_mpbir2an_2 p0000
  exact p0001

@[expose]
noncomputable def g_bianfi (ph : Wff) (ps : Wff) (hyp_bianfi_1 : Nominal.NPrf (.neg ph)) :
    Nominal.NPrf (syn_wb ph (syn_wa ps ph)) :=
  by
  have p0000 := @g_intnan ph ps hyp_bianfi_1
  have p0001 := @g_n_2false ph (syn_wa ps ph) hyp_bianfi_1 p0000
  exact p0001

@[expose]
noncomputable def g_ecase3 (ph : Wff) (ps : Wff) (ch : Wff)
    (hyp_ecase3_1 : Nominal.NPrf (.imp ph ch)) (hyp_ecase3_2 : Nominal.NPrf (.imp ps ch))
    (hyp_ecase3_3 : Nominal.NPrf (.imp (.neg (syn_wo ph ps)) ch)) : Nominal.NPrf ch :=
  by
  have p0000 := @g_jaoi ph ch ps hyp_ecase3_1 hyp_ecase3_2
  have p0001 := @g_pm2_61i (syn_wo ph ps) ch p0000 hyp_ecase3_3
  exact p0001

@[expose]
noncomputable def g_dedlem0a (ph : Wff) (ps : Wff) (ch : Wff) :
    Nominal.NPrf (.imp ph (syn_wb ps (.imp (.imp ch ph) (syn_wa ps ph)))) :=
  by
  have p0000 := @g_iba ph ps
  have p0001 := Nominal.ax1 ph ch
  have p0002 := @g_biimt (.imp ch ph) (syn_wa ps ph)
  have p0003 :=
    @g_syl ph (.imp ch ph) (syn_wb (syn_wa ps ph) (.imp (.imp ch ph) (syn_wa ps ph)))
      p0001 p0002
  have p0004 :=
    @g_bitrd ph ps (syn_wa ps ph) (.imp (.imp ch ph) (syn_wa ps ph)) p0000 p0003
  exact p0004

@[expose]
noncomputable def g_dedlema (ph : Wff) (ps : Wff) (ch : Wff) :
    Nominal.NPrf (.imp ph (syn_wb ps (syn_wo (syn_wa ps ph) (syn_wa ch (.neg ph))))) :=
  by
  have p0000 := @g_orc (syn_wa ps ph) (syn_wa ch (.neg ph))
  have p0001 := @g_expcom ps ph (syn_wo (syn_wa ps ph) (syn_wa ch (.neg ph))) p0000
  have p0002 := @g_simpl ps ph
  have p0003 := @g_a1i (.imp (syn_wa ps ph) ps) ph p0002
  have p0004 := @g_pm2_24 ph ps
  have p0005 := @g_adantld ph (.neg ph) ps ch p0004
  have p0006 := @g_jaod ph (syn_wa ps ph) ps (syn_wa ch (.neg ph)) p0003 p0005
  have p0007 := @g_impbid ph ps (syn_wo (syn_wa ps ph) (syn_wa ch (.neg ph))) p0001 p0006
  exact p0007

@[expose]
noncomputable def g_dedlemb (ph : Wff) (ps : Wff) (ch : Wff) :
    Nominal.NPrf
      (.imp (.neg ph) (syn_wb ch (syn_wo (syn_wa ps ph) (syn_wa ch (.neg ph))))) :=
  by
  have p0000 := @g_olc (syn_wa ch (.neg ph)) (syn_wa ps ph)
  have p0001 := @g_expcom ch (.neg ph) (syn_wo (syn_wa ps ph) (syn_wa ch (.neg ph))) p0000
  have p0002 := @g_pm2_21 ph ch
  have p0003 := @g_adantld (.neg ph) ph ch ps p0002
  have p0004 := @g_simpl ch (.neg ph)
  have p0005 := @g_a1i (.imp (syn_wa ch (.neg ph)) ch) (.neg ph) p0004
  have p0006 := @g_jaod (.neg ph) (syn_wa ps ph) ch (syn_wa ch (.neg ph)) p0003 p0005
  have p0007 :=
    @g_impbid (.neg ph) ch (syn_wo (syn_wa ps ph) (syn_wa ch (.neg ph))) p0001 p0006
  exact p0007

@[expose]
noncomputable def g_pm4_42 (ph : Wff) (ps : Wff) :
    Nominal.NPrf (syn_wb ph (syn_wo (syn_wa ph ps) (syn_wa ph (.neg ps)))) :=
  by
  have p0000 := @g_dedlema ps ph ph
  have p0001 := @g_dedlemb ps ph ph
  have p0002 :=
    @g_pm2_61i ps (syn_wb ph (syn_wo (syn_wa ph ps) (syn_wa ph (.neg ps)))) p0000 p0001
  exact p0002

@[expose]
noncomputable def g_oplem1 (ph : Wff) (ps : Wff) (ch : Wff) (th : Wff) (ta : Wff)
    (hyp_oplem1_1 : Nominal.NPrf (.imp ph (syn_wo ps ch)))
    (hyp_oplem1_2 : Nominal.NPrf (.imp ph (syn_wo th ta)))
    (hyp_oplem1_3 : Nominal.NPrf (syn_wb ps th))
    (hyp_oplem1_4 : Nominal.NPrf (.imp ch (syn_wb th ta))) : Nominal.NPrf (.imp ph ps) :=
  by
  have p0000 := @g_notbii ps th hyp_oplem1_3
  have p0001 := @g_ord ph ps ch hyp_oplem1_1
  have p0002 := @g_syl5bir (.neg th) (.neg ps) ph ch p0000 p0001
  have p0003 := @g_ord ph th ta hyp_oplem1_2
  have p0004 := @g_jcad ph (.neg th) ch ta p0002 p0003
  have p0005 := @g_biimpar ch th ta hyp_oplem1_4
  have p0006 := @g_syl6 ph (.neg th) (syn_wa ch ta) th p0004 p0005
  have p0007 := @g_pm2_18d ph th p0006
  have p0008 := @g_sylibr ph th ps p0007 hyp_oplem1_3
  exact p0008

@[expose]
noncomputable def g_n_3orass (ph : Wff) (ps : Wff) (ch : Wff) :
    Nominal.NPrf (syn_wb (syn_w3o ph ps ch) (syn_wo ph (syn_wo ps ch))) :=
  by
  have p0000 := (Nominal.biimpRefl (syn_w3o ph ps ch))
  have p0001 := @g_orass ph ps ch
  have p0002 :=
    @g_bitri (syn_w3o ph ps ch) (syn_wo (syn_wo ph ps) ch) (syn_wo ph (syn_wo ps ch))
      p0000 p0001
  exact p0002

@[expose]
noncomputable def g_n_3anass (ph : Wff) (ps : Wff) (ch : Wff) :
    Nominal.NPrf (syn_wb (syn_w3a ph ps ch) (syn_wa ph (syn_wa ps ch))) :=
  by
  have p0000 := (Nominal.biimpRefl (syn_w3a ph ps ch))
  have p0001 := @g_anass ph ps ch
  have p0002 :=
    @g_bitri (syn_w3a ph ps ch) (syn_wa (syn_wa ph ps) ch) (syn_wa ph (syn_wa ps ch))
      p0000 p0001
  exact p0002

@[expose]
noncomputable def g_n_3anrot (ph : Wff) (ps : Wff) (ch : Wff) :
    Nominal.NPrf (syn_wb (syn_w3a ph ps ch) (syn_w3a ps ch ph)) :=
  by
  have p0000 := @g_ancom ph (syn_wa ps ch)
  have p0001 := @g_n_3anass ph ps ch
  have p0002 := (Nominal.biimpRefl (syn_w3a ps ch ph))
  have p0003 :=
    @g_n_3bitr4i (syn_wa ph (syn_wa ps ch)) (syn_wa (syn_wa ps ch) ph) (syn_w3a ph ps ch)
      (syn_w3a ps ch ph) p0000 p0001 p0002
  exact p0003

@[expose]
noncomputable def g_n_3orrot (ph : Wff) (ps : Wff) (ch : Wff) :
    Nominal.NPrf (syn_wb (syn_w3o ph ps ch) (syn_w3o ps ch ph)) :=
  by
  have p0000 := @g_orcom ph (syn_wo ps ch)
  have p0001 := @g_n_3orass ph ps ch
  have p0002 := (Nominal.biimpRefl (syn_w3o ps ch ph))
  have p0003 :=
    @g_n_3bitr4i (syn_wo ph (syn_wo ps ch)) (syn_wo (syn_wo ps ch) ph) (syn_w3o ph ps ch)
      (syn_w3o ps ch ph) p0000 p0001 p0002
  exact p0003

@[expose]
noncomputable def g_n_3ancoma (ph : Wff) (ps : Wff) (ch : Wff) :
    Nominal.NPrf (syn_wb (syn_w3a ph ps ch) (syn_w3a ps ph ch)) :=
  by
  have p0000 := @g_ancom ph ps
  have p0001 := @g_anbi1i (syn_wa ph ps) (syn_wa ps ph) ch p0000
  have p0002 := (Nominal.biimpRefl (syn_w3a ph ps ch))
  have p0003 := (Nominal.biimpRefl (syn_w3a ps ph ch))
  have p0004 :=
    @g_n_3bitr4i (syn_wa (syn_wa ph ps) ch) (syn_wa (syn_wa ps ph) ch) (syn_w3a ph ps ch)
      (syn_w3a ps ph ch) p0001 p0002 p0003
  exact p0004

@[expose]
noncomputable def g_n_3ancomb (ph : Wff) (ps : Wff) (ch : Wff) :
    Nominal.NPrf (syn_wb (syn_w3a ph ps ch) (syn_w3a ph ch ps)) :=
  by
  have p0000 := @g_n_3ancoma ph ps ch
  have p0001 := @g_n_3anrot ps ph ch
  have p0002 :=
    @g_bitri (syn_w3a ph ps ch) (syn_w3a ps ph ch) (syn_w3a ph ch ps) p0000 p0001
  exact p0002

@[expose]
noncomputable def g_n_3anrev (ph : Wff) (ps : Wff) (ch : Wff) :
    Nominal.NPrf (syn_wb (syn_w3a ph ps ch) (syn_w3a ch ps ph)) :=
  by
  have p0000 := @g_n_3ancoma ph ps ch
  have p0001 := @g_n_3anrot ch ps ph
  have p0002 :=
    @g_bitr4i (syn_w3a ph ps ch) (syn_w3a ps ph ch) (syn_w3a ch ps ph) p0000 p0001
  exact p0002

@[expose]
noncomputable def g_n_3simpa (ph : Wff) (ps : Wff) (ch : Wff) :
    Nominal.NPrf (.imp (syn_w3a ph ps ch) (syn_wa ph ps)) :=
  by
  have p0000 := (Nominal.biimpRefl (syn_w3a ph ps ch))
  have p0001 := @g_simplbi (syn_w3a ph ps ch) (syn_wa ph ps) ch p0000
  exact p0001

@[expose]
noncomputable def g_n_3simpb (ph : Wff) (ps : Wff) (ch : Wff) :
    Nominal.NPrf (.imp (syn_w3a ph ps ch) (syn_wa ph ch)) :=
  by
  have p0000 := @g_n_3ancomb ph ps ch
  have p0001 := @g_n_3simpa ph ch ps
  have p0002 := @g_sylbi (syn_w3a ph ps ch) (syn_w3a ph ch ps) (syn_wa ph ch) p0000 p0001
  exact p0002

@[expose]
noncomputable def g_n_3simpc (ph : Wff) (ps : Wff) (ch : Wff) :
    Nominal.NPrf (.imp (syn_w3a ph ps ch) (syn_wa ps ch)) :=
  by
  have p0000 := @g_n_3anrot ph ps ch
  have p0001 := @g_n_3simpa ps ch ph
  have p0002 := @g_sylbi (syn_w3a ph ps ch) (syn_w3a ps ch ph) (syn_wa ps ch) p0000 p0001
  exact p0002

@[expose]
noncomputable def g_simp1 (ph : Wff) (ps : Wff) (ch : Wff) :
    Nominal.NPrf (.imp (syn_w3a ph ps ch) ph) :=
  by
  have p0000 := @g_n_3simpa ph ps ch
  have p0001 := @g_simpld (syn_w3a ph ps ch) ph ps p0000
  exact p0001

@[expose]
noncomputable def g_simp2 (ph : Wff) (ps : Wff) (ch : Wff) :
    Nominal.NPrf (.imp (syn_w3a ph ps ch) ps) :=
  by
  have p0000 := @g_n_3simpa ph ps ch
  have p0001 := @g_simprd (syn_w3a ph ps ch) ph ps p0000
  exact p0001

@[expose]
noncomputable def g_simp3 (ph : Wff) (ps : Wff) (ch : Wff) :
    Nominal.NPrf (.imp (syn_w3a ph ps ch) ch) :=
  by
  have p0000 := @g_n_3simpc ph ps ch
  have p0001 := @g_simprd (syn_w3a ph ps ch) ps ch p0000
  exact p0001

@[expose]
noncomputable def g_simpl1 (ph : Wff) (ps : Wff) (ch : Wff) (th : Wff) :
    Nominal.NPrf (.imp (syn_wa (syn_w3a ph ps ch) th) ph) :=
  by
  have p0000 := @g_simp1 ph ps ch
  have p0001 := @g_adantr (syn_w3a ph ps ch) ph th p0000
  exact p0001

@[expose]
noncomputable def g_simpl2 (ph : Wff) (ps : Wff) (ch : Wff) (th : Wff) :
    Nominal.NPrf (.imp (syn_wa (syn_w3a ph ps ch) th) ps) :=
  by
  have p0000 := @g_simp2 ph ps ch
  have p0001 := @g_adantr (syn_w3a ph ps ch) ps th p0000
  exact p0001

@[expose]
noncomputable def g_simpl3 (ph : Wff) (ps : Wff) (ch : Wff) (th : Wff) :
    Nominal.NPrf (.imp (syn_wa (syn_w3a ph ps ch) th) ch) :=
  by
  have p0000 := @g_simp3 ph ps ch
  have p0001 := @g_adantr (syn_w3a ph ps ch) ch th p0000
  exact p0001

@[expose]
noncomputable def g_simpr1 (ph : Wff) (ps : Wff) (ch : Wff) (th : Wff) :
    Nominal.NPrf (.imp (syn_wa ph (syn_w3a ps ch th)) ps) :=
  by
  have p0000 := @g_simp1 ps ch th
  have p0001 := @g_adantl (syn_w3a ps ch th) ps ph p0000
  exact p0001

@[expose]
noncomputable def g_simp1d (ph : Wff) (ps : Wff) (ch : Wff) (th : Wff)
    (hyp_n_3simp1d_1 : Nominal.NPrf (.imp ph (syn_w3a ps ch th))) :
    Nominal.NPrf (.imp ph ps) :=
  by
  have p0000 := @g_simp1 ps ch th
  have p0001 := @g_syl ph (syn_w3a ps ch th) ps hyp_n_3simp1d_1 p0000
  exact p0001

@[expose]
noncomputable def g_simp2d (ph : Wff) (ps : Wff) (ch : Wff) (th : Wff)
    (hyp_n_3simp1d_1 : Nominal.NPrf (.imp ph (syn_w3a ps ch th))) :
    Nominal.NPrf (.imp ph ch) :=
  by
  have p0000 := @g_simp2 ps ch th
  have p0001 := @g_syl ph (syn_w3a ps ch th) ch hyp_n_3simp1d_1 p0000
  exact p0001

@[expose]
noncomputable def g_simp3d (ph : Wff) (ps : Wff) (ch : Wff) (th : Wff)
    (hyp_n_3simp1d_1 : Nominal.NPrf (.imp ph (syn_w3a ps ch th))) :
    Nominal.NPrf (.imp ph th) :=
  by
  have p0000 := @g_simp3 ps ch th
  have p0001 := @g_syl ph (syn_w3a ps ch th) th hyp_n_3simp1d_1 p0000
  exact p0001

@[expose]
noncomputable def g_simp1bi (ph : Wff) (ps : Wff) (ch : Wff) (th : Wff)
    (hyp_n_3simp1bi_1 : Nominal.NPrf (syn_wb ph (syn_w3a ps ch th))) :
    Nominal.NPrf (.imp ph ps) :=
  by
  have p0000 := @g_biimpi ph (syn_w3a ps ch th) hyp_n_3simp1bi_1
  have p0001 := @g_simp1d ph ps ch th p0000
  exact p0001

@[expose]
noncomputable def g_simp2bi (ph : Wff) (ps : Wff) (ch : Wff) (th : Wff)
    (hyp_n_3simp1bi_1 : Nominal.NPrf (syn_wb ph (syn_w3a ps ch th))) :
    Nominal.NPrf (.imp ph ch) :=
  by
  have p0000 := @g_biimpi ph (syn_w3a ps ch th) hyp_n_3simp1bi_1
  have p0001 := @g_simp2d ph ps ch th p0000
  exact p0001

@[expose]
noncomputable def g_simp3bi (ph : Wff) (ps : Wff) (ch : Wff) (th : Wff)
    (hyp_n_3simp1bi_1 : Nominal.NPrf (syn_wb ph (syn_w3a ps ch th))) :
    Nominal.NPrf (.imp ph th) :=
  by
  have p0000 := @g_biimpi ph (syn_w3a ps ch th) hyp_n_3simp1bi_1
  have p0001 := @g_simp3d ph ps ch th p0000
  exact p0001

@[expose]
noncomputable def g_n_3adant1 (ph : Wff) (ps : Wff) (ch : Wff) (th : Wff)
    (hyp_n_3adant_1 : Nominal.NPrf (.imp (syn_wa ph ps) ch)) :
    Nominal.NPrf (.imp (syn_w3a th ph ps) ch) :=
  by
  have p0000 := @g_n_3simpc th ph ps
  have p0001 := @g_syl (syn_w3a th ph ps) (syn_wa ph ps) ch p0000 hyp_n_3adant_1
  exact p0001

@[expose]
noncomputable def g_n_3adant2 (ph : Wff) (ps : Wff) (ch : Wff) (th : Wff)
    (hyp_n_3adant_1 : Nominal.NPrf (.imp (syn_wa ph ps) ch)) :
    Nominal.NPrf (.imp (syn_w3a ph th ps) ch) :=
  by
  have p0000 := @g_n_3simpb ph th ps
  have p0001 := @g_syl (syn_w3a ph th ps) (syn_wa ph ps) ch p0000 hyp_n_3adant_1
  exact p0001

@[expose]
noncomputable def g_n_3adant3 (ph : Wff) (ps : Wff) (ch : Wff) (th : Wff)
    (hyp_n_3adant_1 : Nominal.NPrf (.imp (syn_wa ph ps) ch)) :
    Nominal.NPrf (.imp (syn_w3a ph ps th) ch) :=
  by
  have p0000 := @g_n_3simpa ph ps th
  have p0001 := @g_syl (syn_w3a ph ps th) (syn_wa ph ps) ch p0000 hyp_n_3adant_1
  exact p0001

@[expose]
noncomputable def g_n_3ad2ant1 (ph : Wff) (ps : Wff) (ch : Wff) (th : Wff)
    (hyp_n_3ad2ant_1 : Nominal.NPrf (.imp ph ch)) :
    Nominal.NPrf (.imp (syn_w3a ph ps th) ch) :=
  by
  have p0000 := @g_adantr ph ch th hyp_n_3ad2ant_1
  have p0001 := @g_n_3adant2 ph th ch ps p0000
  exact p0001

@[expose]
noncomputable def g_n_3ad2ant2 (ph : Wff) (ps : Wff) (ch : Wff) (th : Wff)
    (hyp_n_3ad2ant_1 : Nominal.NPrf (.imp ph ch)) :
    Nominal.NPrf (.imp (syn_w3a ps ph th) ch) :=
  by
  have p0000 := @g_adantr ph ch th hyp_n_3ad2ant_1
  have p0001 := @g_n_3adant1 ph th ch ps p0000
  exact p0001

@[expose]
noncomputable def g_n_3ad2ant3 (ph : Wff) (ps : Wff) (ch : Wff) (th : Wff)
    (hyp_n_3ad2ant_1 : Nominal.NPrf (.imp ph ch)) :
    Nominal.NPrf (.imp (syn_w3a ps th ph) ch) :=
  by
  have p0000 := @g_adantl ph ch th hyp_n_3ad2ant_1
  have p0001 := @g_n_3adant1 th ph ch ps p0000
  exact p0001

@[expose]
noncomputable def g_simp1l (ph : Wff) (ps : Wff) (ch : Wff) (th : Wff) :
    Nominal.NPrf (.imp (syn_w3a (syn_wa ph ps) ch th) ph) :=
  by
  have p0000 := @g_simpl ph ps
  have p0001 := @g_n_3ad2ant1 (syn_wa ph ps) ch ph th p0000
  exact p0001

@[expose]
noncomputable def g_simp1r (ph : Wff) (ps : Wff) (ch : Wff) (th : Wff) :
    Nominal.NPrf (.imp (syn_w3a (syn_wa ph ps) ch th) ps) :=
  by
  have p0000 := @g_simpr ph ps
  have p0001 := @g_n_3ad2ant1 (syn_wa ph ps) ch ps th p0000
  exact p0001

@[expose]
noncomputable def g_simp2l (ph : Wff) (ps : Wff) (ch : Wff) (th : Wff) :
    Nominal.NPrf (.imp (syn_w3a ph (syn_wa ps ch) th) ps) :=
  by
  have p0000 := @g_simpl ps ch
  have p0001 := @g_n_3ad2ant2 (syn_wa ps ch) ph ps th p0000
  exact p0001

@[expose]
noncomputable def g_simp2r (ph : Wff) (ps : Wff) (ch : Wff) (th : Wff) :
    Nominal.NPrf (.imp (syn_w3a ph (syn_wa ps ch) th) ch) :=
  by
  have p0000 := @g_simpr ps ch
  have p0001 := @g_n_3ad2ant2 (syn_wa ps ch) ph ch th p0000
  exact p0001

@[expose]
noncomputable def g_simp3l (ph : Wff) (ps : Wff) (ch : Wff) (th : Wff) :
    Nominal.NPrf (.imp (syn_w3a ph ps (syn_wa ch th)) ch) :=
  by
  have p0000 := @g_simpl ch th
  have p0001 := @g_n_3ad2ant3 (syn_wa ch th) ph ch ps p0000
  exact p0001

@[expose]
noncomputable def g_simp3r (ph : Wff) (ps : Wff) (ch : Wff) (th : Wff) :
    Nominal.NPrf (.imp (syn_w3a ph ps (syn_wa ch th)) th) :=
  by
  have p0000 := @g_simpr ch th
  have p0001 := @g_n_3ad2ant3 (syn_wa ch th) ph th ps p0000
  exact p0001

@[expose]
noncomputable def g_simp21 (ph : Wff) (ps : Wff) (ch : Wff) (th : Wff) (ta : Wff) :
    Nominal.NPrf (.imp (syn_w3a ph (syn_w3a ps ch th) ta) ps) :=
  by
  have p0000 := @g_simp1 ps ch th
  have p0001 := @g_n_3ad2ant2 (syn_w3a ps ch th) ph ps ta p0000
  exact p0001

@[expose]
noncomputable def g_simp23 (ph : Wff) (ps : Wff) (ch : Wff) (th : Wff) (ta : Wff) :
    Nominal.NPrf (.imp (syn_w3a ph (syn_w3a ps ch th) ta) th) :=
  by
  have p0000 := @g_simp3 ps ch th
  have p0001 := @g_n_3ad2ant2 (syn_w3a ps ch th) ph th ta p0000
  exact p0001

@[expose]
noncomputable def g_simp31 (ph : Wff) (ps : Wff) (ch : Wff) (th : Wff) (ta : Wff) :
    Nominal.NPrf (.imp (syn_w3a ph ps (syn_w3a ch th ta)) ch) :=
  by
  have p0000 := @g_simp1 ch th ta
  have p0001 := @g_n_3ad2ant3 (syn_w3a ch th ta) ph ch ps p0000
  exact p0001

@[expose]
noncomputable def g_simp32 (ph : Wff) (ps : Wff) (ch : Wff) (th : Wff) (ta : Wff) :
    Nominal.NPrf (.imp (syn_w3a ph ps (syn_w3a ch th ta)) th) :=
  by
  have p0000 := @g_simp2 ch th ta
  have p0001 := @g_n_3ad2ant3 (syn_w3a ch th ta) ph th ps p0000
  exact p0001

@[expose]
noncomputable def g_simp33 (ph : Wff) (ps : Wff) (ch : Wff) (th : Wff) (ta : Wff) :
    Nominal.NPrf (.imp (syn_w3a ph ps (syn_w3a ch th ta)) ta) :=
  by
  have p0000 := @g_simp3 ch th ta
  have p0001 := @g_n_3ad2ant3 (syn_w3a ch th ta) ph ta ps p0000
  exact p0001

@[expose]
noncomputable def g_simpl1l (ph : Wff) (ps : Wff) (ch : Wff) (th : Wff) (ta : Wff) :
    Nominal.NPrf (.imp (syn_wa (syn_w3a (syn_wa ph ps) ch th) ta) ph) :=
  by
  have p0000 := @g_simp1l ph ps ch th
  have p0001 := @g_adantr (syn_w3a (syn_wa ph ps) ch th) ph ta p0000
  exact p0001

@[expose]
noncomputable def g_simpl1r (ph : Wff) (ps : Wff) (ch : Wff) (th : Wff) (ta : Wff) :
    Nominal.NPrf (.imp (syn_wa (syn_w3a (syn_wa ph ps) ch th) ta) ps) :=
  by
  have p0000 := @g_simp1r ph ps ch th
  have p0001 := @g_adantr (syn_w3a (syn_wa ph ps) ch th) ps ta p0000
  exact p0001

@[expose]
noncomputable def g_simpl2l (ph : Wff) (ps : Wff) (ch : Wff) (th : Wff) (ta : Wff) :
    Nominal.NPrf (.imp (syn_wa (syn_w3a ch (syn_wa ph ps) th) ta) ph) :=
  by
  have p0000 := @g_simp2l ch ph ps th
  have p0001 := @g_adantr (syn_w3a ch (syn_wa ph ps) th) ph ta p0000
  exact p0001

@[expose]
noncomputable def g_simpl2r (ph : Wff) (ps : Wff) (ch : Wff) (th : Wff) (ta : Wff) :
    Nominal.NPrf (.imp (syn_wa (syn_w3a ch (syn_wa ph ps) th) ta) ps) :=
  by
  have p0000 := @g_simp2r ch ph ps th
  have p0001 := @g_adantr (syn_w3a ch (syn_wa ph ps) th) ps ta p0000
  exact p0001

@[expose]
noncomputable def g_simpl3l (ph : Wff) (ps : Wff) (ch : Wff) (th : Wff) (ta : Wff) :
    Nominal.NPrf (.imp (syn_wa (syn_w3a ch th (syn_wa ph ps)) ta) ph) :=
  by
  have p0000 := @g_simp3l ch th ph ps
  have p0001 := @g_adantr (syn_w3a ch th (syn_wa ph ps)) ph ta p0000
  exact p0001

@[expose]
noncomputable def g_simpl3r (ph : Wff) (ps : Wff) (ch : Wff) (th : Wff) (ta : Wff) :
    Nominal.NPrf (.imp (syn_wa (syn_w3a ch th (syn_wa ph ps)) ta) ps) :=
  by
  have p0000 := @g_simp3r ch th ph ps
  have p0001 := @g_adantr (syn_w3a ch th (syn_wa ph ps)) ps ta p0000
  exact p0001

@[expose]
noncomputable def g_simpr2l (ph : Wff) (ps : Wff) (ch : Wff) (th : Wff) (ta : Wff) :
    Nominal.NPrf (.imp (syn_wa ta (syn_w3a ch (syn_wa ph ps) th)) ph) :=
  by
  have p0000 := @g_simp2l ch ph ps th
  have p0001 := @g_adantl (syn_w3a ch (syn_wa ph ps) th) ph ta p0000
  exact p0001

@[expose]
noncomputable def g_simpr2r (ph : Wff) (ps : Wff) (ch : Wff) (th : Wff) (ta : Wff) :
    Nominal.NPrf (.imp (syn_wa ta (syn_w3a ch (syn_wa ph ps) th)) ps) :=
  by
  have p0000 := @g_simp2r ch ph ps th
  have p0001 := @g_adantl (syn_w3a ch (syn_wa ph ps) th) ps ta p0000
  exact p0001

@[expose]
noncomputable def g_simpr3l (ph : Wff) (ps : Wff) (ch : Wff) (th : Wff) (ta : Wff) :
    Nominal.NPrf (.imp (syn_wa ta (syn_w3a ch th (syn_wa ph ps))) ph) :=
  by
  have p0000 := @g_simp3l ch th ph ps
  have p0001 := @g_adantl (syn_w3a ch th (syn_wa ph ps)) ph ta p0000
  exact p0001

@[expose]
noncomputable def g_simpr3r (ph : Wff) (ps : Wff) (ch : Wff) (th : Wff) (ta : Wff) :
    Nominal.NPrf (.imp (syn_wa ta (syn_w3a ch th (syn_wa ph ps))) ps) :=
  by
  have p0000 := @g_simp3r ch th ph ps
  have p0001 := @g_adantl (syn_w3a ch th (syn_wa ph ps)) ps ta p0000
  exact p0001

@[expose]
noncomputable def g_simp1rl (ph : Wff) (ps : Wff) (ch : Wff) (th : Wff) (ta : Wff) :
    Nominal.NPrf (.imp (syn_w3a (syn_wa ch (syn_wa ph ps)) th ta) ph) :=
  by
  have p0000 := @g_simprl ch ph ps
  have p0001 := @g_n_3ad2ant1 (syn_wa ch (syn_wa ph ps)) th ph ta p0000
  exact p0001

@[expose]
noncomputable def g_simp1rr (ph : Wff) (ps : Wff) (ch : Wff) (th : Wff) (ta : Wff) :
    Nominal.NPrf (.imp (syn_w3a (syn_wa ch (syn_wa ph ps)) th ta) ps) :=
  by
  have p0000 := @g_simprr ch ph ps
  have p0001 := @g_n_3ad2ant1 (syn_wa ch (syn_wa ph ps)) th ps ta p0000
  exact p0001

@[expose]
noncomputable def g_simp2ll (ph : Wff) (ps : Wff) (ch : Wff) (th : Wff) (ta : Wff) :
    Nominal.NPrf (.imp (syn_w3a th (syn_wa (syn_wa ph ps) ch) ta) ph) :=
  by
  have p0000 := @g_simpll ph ps ch
  have p0001 := @g_n_3ad2ant2 (syn_wa (syn_wa ph ps) ch) th ph ta p0000
  exact p0001

@[expose]
noncomputable def g_simp2lr (ph : Wff) (ps : Wff) (ch : Wff) (th : Wff) (ta : Wff) :
    Nominal.NPrf (.imp (syn_w3a th (syn_wa (syn_wa ph ps) ch) ta) ps) :=
  by
  have p0000 := @g_simplr ph ps ch
  have p0001 := @g_n_3ad2ant2 (syn_wa (syn_wa ph ps) ch) th ps ta p0000
  exact p0001

@[expose]
noncomputable def g_simp2rl (ph : Wff) (ps : Wff) (ch : Wff) (th : Wff) (ta : Wff) :
    Nominal.NPrf (.imp (syn_w3a th (syn_wa ch (syn_wa ph ps)) ta) ph) :=
  by
  have p0000 := @g_simprl ch ph ps
  have p0001 := @g_n_3ad2ant2 (syn_wa ch (syn_wa ph ps)) th ph ta p0000
  exact p0001

@[expose]
noncomputable def g_simp2rr (ph : Wff) (ps : Wff) (ch : Wff) (th : Wff) (ta : Wff) :
    Nominal.NPrf (.imp (syn_w3a th (syn_wa ch (syn_wa ph ps)) ta) ps) :=
  by
  have p0000 := @g_simprr ch ph ps
  have p0001 := @g_n_3ad2ant2 (syn_wa ch (syn_wa ph ps)) th ps ta p0000
  exact p0001

@[expose]
noncomputable def g_simp3ll (ph : Wff) (ps : Wff) (ch : Wff) (th : Wff) (ta : Wff) :
    Nominal.NPrf (.imp (syn_w3a th ta (syn_wa (syn_wa ph ps) ch)) ph) :=
  by
  have p0000 := @g_simpll ph ps ch
  have p0001 := @g_n_3ad2ant3 (syn_wa (syn_wa ph ps) ch) th ph ta p0000
  exact p0001

@[expose]
noncomputable def g_simp3lr (ph : Wff) (ps : Wff) (ch : Wff) (th : Wff) (ta : Wff) :
    Nominal.NPrf (.imp (syn_w3a th ta (syn_wa (syn_wa ph ps) ch)) ps) :=
  by
  have p0000 := @g_simplr ph ps ch
  have p0001 := @g_n_3ad2ant3 (syn_wa (syn_wa ph ps) ch) th ps ta p0000
  exact p0001

@[expose]
noncomputable def g_simp3rl (ph : Wff) (ps : Wff) (ch : Wff) (th : Wff) (ta : Wff) :
    Nominal.NPrf (.imp (syn_w3a th ta (syn_wa ch (syn_wa ph ps))) ph) :=
  by
  have p0000 := @g_simprl ch ph ps
  have p0001 := @g_n_3ad2ant3 (syn_wa ch (syn_wa ph ps)) th ph ta p0000
  exact p0001

@[expose]
noncomputable def g_simp3rr (ph : Wff) (ps : Wff) (ch : Wff) (th : Wff) (ta : Wff) :
    Nominal.NPrf (.imp (syn_w3a th ta (syn_wa ch (syn_wa ph ps))) ps) :=
  by
  have p0000 := @g_simprr ch ph ps
  have p0001 := @g_n_3ad2ant3 (syn_wa ch (syn_wa ph ps)) th ps ta p0000
  exact p0001

@[expose]
noncomputable def g_simpl31 (ph : Wff) (ps : Wff) (ch : Wff) (th : Wff) (ta : Wff)
    (et : Wff) : Nominal.NPrf (.imp (syn_wa (syn_w3a th ta (syn_w3a ph ps ch)) et) ph) :=
  by
  have p0000 := @g_simp31 th ta ph ps ch
  have p0001 := @g_adantr (syn_w3a th ta (syn_w3a ph ps ch)) ph et p0000
  exact p0001

@[expose]
noncomputable def g_simpl32 (ph : Wff) (ps : Wff) (ch : Wff) (th : Wff) (ta : Wff)
    (et : Wff) : Nominal.NPrf (.imp (syn_wa (syn_w3a th ta (syn_w3a ph ps ch)) et) ps) :=
  by
  have p0000 := @g_simp32 th ta ph ps ch
  have p0001 := @g_adantr (syn_w3a th ta (syn_w3a ph ps ch)) ps et p0000
  exact p0001

@[expose]
noncomputable def g_simp12l (ph : Wff) (ps : Wff) (ch : Wff) (th : Wff) (ta : Wff)
    (et : Wff) : Nominal.NPrf (.imp (syn_w3a (syn_w3a ch (syn_wa ph ps) th) ta et) ph) :=
  by
  have p0000 := @g_simp2l ch ph ps th
  have p0001 := @g_n_3ad2ant1 (syn_w3a ch (syn_wa ph ps) th) ta ph et p0000
  exact p0001

@[expose]
noncomputable def g_simp12r (ph : Wff) (ps : Wff) (ch : Wff) (th : Wff) (ta : Wff)
    (et : Wff) : Nominal.NPrf (.imp (syn_w3a (syn_w3a ch (syn_wa ph ps) th) ta et) ps) :=
  by
  have p0000 := @g_simp2r ch ph ps th
  have p0001 := @g_n_3ad2ant1 (syn_w3a ch (syn_wa ph ps) th) ta ps et p0000
  exact p0001

@[expose]
noncomputable def g_simp22r (ph : Wff) (ps : Wff) (ch : Wff) (th : Wff) (ta : Wff)
    (et : Wff) : Nominal.NPrf (.imp (syn_w3a ta (syn_w3a ch (syn_wa ph ps) th) et) ps) :=
  by
  have p0000 := @g_simp2r ch ph ps th
  have p0001 := @g_n_3ad2ant2 (syn_w3a ch (syn_wa ph ps) th) ta ps et p0000
  exact p0001

@[expose]
noncomputable def g_simp23l (ph : Wff) (ps : Wff) (ch : Wff) (th : Wff) (ta : Wff)
    (et : Wff) : Nominal.NPrf (.imp (syn_w3a ta (syn_w3a ch th (syn_wa ph ps)) et) ph) :=
  by
  have p0000 := @g_simp3l ch th ph ps
  have p0001 := @g_n_3ad2ant2 (syn_w3a ch th (syn_wa ph ps)) ta ph et p0000
  exact p0001

@[expose]
noncomputable def g_n_3adantl1 (ph : Wff) (ps : Wff) (ch : Wff) (th : Wff) (ta : Wff)
    (hyp_n_3adantl_1 : Nominal.NPrf (.imp (syn_wa (syn_wa ph ps) ch) th)) :
    Nominal.NPrf (.imp (syn_wa (syn_w3a ta ph ps) ch) th) :=
  by
  have p0000 := @g_n_3simpc ta ph ps
  have p0001 := @g_sylan (syn_w3a ta ph ps) (syn_wa ph ps) ch th p0000 hyp_n_3adantl_1
  exact p0001

@[expose]
noncomputable def g_n_3adantl2 (ph : Wff) (ps : Wff) (ch : Wff) (th : Wff) (ta : Wff)
    (hyp_n_3adantl_1 : Nominal.NPrf (.imp (syn_wa (syn_wa ph ps) ch) th)) :
    Nominal.NPrf (.imp (syn_wa (syn_w3a ph ta ps) ch) th) :=
  by
  have p0000 := @g_n_3simpb ph ta ps
  have p0001 := @g_sylan (syn_w3a ph ta ps) (syn_wa ph ps) ch th p0000 hyp_n_3adantl_1
  exact p0001

@[expose]
noncomputable def g_n_3adantr1 (ph : Wff) (ps : Wff) (ch : Wff) (th : Wff) (ta : Wff)
    (hyp_n_3adantr_1 : Nominal.NPrf (.imp (syn_wa ph (syn_wa ps ch)) th)) :
    Nominal.NPrf (.imp (syn_wa ph (syn_w3a ta ps ch)) th) :=
  by
  have p0000 := @g_n_3simpc ta ps ch
  have p0001 := @g_sylan2 (syn_w3a ta ps ch) ph (syn_wa ps ch) th p0000 hyp_n_3adantr_1
  exact p0001

@[expose]
noncomputable def g_n_3ad2antl1 (ph : Wff) (ps : Wff) (ch : Wff) (th : Wff) (ta : Wff)
    (hyp_n_3ad2antl_1 : Nominal.NPrf (.imp (syn_wa ph ch) th)) :
    Nominal.NPrf (.imp (syn_wa (syn_w3a ph ps ta) ch) th) :=
  by
  have p0000 := @g_adantlr ph ch th ta hyp_n_3ad2antl_1
  have p0001 := @g_n_3adantl2 ph ta ch th ps p0000
  exact p0001

@[expose]
noncomputable def g_n_3ad2antl3 (ph : Wff) (ps : Wff) (ch : Wff) (th : Wff) (ta : Wff)
    (hyp_n_3ad2antl_1 : Nominal.NPrf (.imp (syn_wa ph ch) th)) :
    Nominal.NPrf (.imp (syn_wa (syn_w3a ps ta ph) ch) th) :=
  by
  have p0000 := @g_adantll ph ch th ta hyp_n_3ad2antl_1
  have p0001 := @g_n_3adantl1 ta ph ch th ps p0000
  exact p0001

@[expose]
noncomputable def g_n_3mix1 (ph : Wff) (ps : Wff) (ch : Wff) :
    Nominal.NPrf (.imp ph (syn_w3o ph ps ch)) :=
  by
  have p0000 := @g_orc ph (syn_wo ps ch)
  have p0001 := @g_n_3orass ph ps ch
  have p0002 := @g_sylibr ph (syn_wo ph (syn_wo ps ch)) (syn_w3o ph ps ch) p0000 p0001
  exact p0002

@[expose]
noncomputable def g_n_3mix2 (ph : Wff) (ps : Wff) (ch : Wff) :
    Nominal.NPrf (.imp ph (syn_w3o ps ph ch)) :=
  by
  have p0000 := @g_n_3mix1 ph ch ps
  have p0001 := @g_n_3orrot ps ph ch
  have p0002 := @g_sylibr ph (syn_w3o ph ch ps) (syn_w3o ps ph ch) p0000 p0001
  exact p0002

@[expose]
noncomputable def g_n_3mix3 (ph : Wff) (ps : Wff) (ch : Wff) :
    Nominal.NPrf (.imp ph (syn_w3o ps ch ph)) :=
  by
  have p0000 := @g_n_3mix1 ph ps ch
  have p0001 := @g_n_3orrot ph ps ch
  have p0002 := @g_sylib ph (syn_w3o ph ps ch) (syn_w3o ps ch ph) p0000 p0001
  exact p0002

@[expose]
noncomputable def g_n_3pm3_2i (ph : Wff) (ps : Wff) (ch : Wff)
    (hyp_n_3pm3_2i_1 : Nominal.NPrf ph) (hyp_n_3pm3_2i_2 : Nominal.NPrf ps)
    (hyp_n_3pm3_2i_3 : Nominal.NPrf ch) : Nominal.NPrf (syn_w3a ph ps ch) :=
  by
  have p0000 := @g_pm3_2i ph ps hyp_n_3pm3_2i_1 hyp_n_3pm3_2i_2
  have p0001 := (Nominal.biimpRefl (syn_w3a ph ps ch))
  have p0002 :=
    @g_mpbir2an (syn_w3a ph ps ch) (syn_wa ph ps) ch p0000 hyp_n_3pm3_2i_3 p0001
  exact p0002

@[expose]
noncomputable def g_pm3_2an3 (ph : Wff) (ps : Wff) (ch : Wff) :
    Nominal.NPrf (.imp ph (.imp ps (.imp ch (syn_w3a ph ps ch)))) :=
  by
  have p0000 := @g_pm3_2 (syn_wa ph ps) ch
  have p0001 := @g_ex ph ps (.imp ch (syn_wa (syn_wa ph ps) ch)) p0000
  have p0002 := (Nominal.biimpRefl (syn_w3a ph ps ch))
  have p0003 := @g_bicomi (syn_w3a ph ps ch) (syn_wa (syn_wa ph ps) ch) p0002
  have p0004 :=
    @g_syl8ib ph ps ch (syn_wa (syn_wa ph ps) ch) (syn_w3a ph ps ch) p0001 p0003
  exact p0004

@[expose]
noncomputable def g_n_3jca (ph : Wff) (ps : Wff) (ch : Wff) (th : Wff)
    (hyp_n_3jca_1 : Nominal.NPrf (.imp ph ps)) (hyp_n_3jca_2 : Nominal.NPrf (.imp ph ch))
    (hyp_n_3jca_3 : Nominal.NPrf (.imp ph th)) :
    Nominal.NPrf (.imp ph (syn_w3a ps ch th)) :=
  by
  have p0000 := @g_jca31 ph ps ch th hyp_n_3jca_1 hyp_n_3jca_2 hyp_n_3jca_3
  have p0001 := (Nominal.biimpRefl (syn_w3a ps ch th))
  have p0002 := @g_sylibr ph (syn_wa (syn_wa ps ch) th) (syn_w3a ps ch th) p0000 p0001
  exact p0002

@[expose]
noncomputable def g_n_3jcad (ph : Wff) (ps : Wff) (ch : Wff) (th : Wff) (ta : Wff)
    (hyp_n_3jcad_1 : Nominal.NPrf (.imp ph (.imp ps ch)))
    (hyp_n_3jcad_2 : Nominal.NPrf (.imp ph (.imp ps th)))
    (hyp_n_3jcad_3 : Nominal.NPrf (.imp ph (.imp ps ta))) :
    Nominal.NPrf (.imp ph (.imp ps (syn_w3a ch th ta))) :=
  by
  have p0000 := @g_imp ph ps ch hyp_n_3jcad_1
  have p0001 := @g_imp ph ps th hyp_n_3jcad_2
  have p0002 := @g_imp ph ps ta hyp_n_3jcad_3
  have p0003 := @g_n_3jca (syn_wa ph ps) ch th ta p0000 p0001 p0002
  have p0004 := @g_ex ph ps (syn_w3a ch th ta) p0003
  exact p0004

@[expose]
noncomputable def g_mpbir3an (ph : Wff) (ps : Wff) (ch : Wff) (th : Wff)
    (hyp_mpbir3an_1 : Nominal.NPrf ps) (hyp_mpbir3an_2 : Nominal.NPrf ch)
    (hyp_mpbir3an_3 : Nominal.NPrf th)
    (hyp_mpbir3an_4 : Nominal.NPrf (syn_wb ph (syn_w3a ps ch th))) : Nominal.NPrf ph :=
  by
  have p0000 := @g_n_3pm3_2i ps ch th hyp_mpbir3an_1 hyp_mpbir3an_2 hyp_mpbir3an_3
  have p0001 := @g_mpbir ph (syn_w3a ps ch th) p0000 hyp_mpbir3an_4
  exact p0001

@[expose]
noncomputable def g_syl3anbrc (ph : Wff) (ps : Wff) (ch : Wff) (th : Wff) (ta : Wff)
    (hyp_syl3anbrc_1 : Nominal.NPrf (.imp ph ps))
    (hyp_syl3anbrc_2 : Nominal.NPrf (.imp ph ch))
    (hyp_syl3anbrc_3 : Nominal.NPrf (.imp ph th))
    (hyp_syl3anbrc_4 : Nominal.NPrf (syn_wb ta (syn_w3a ps ch th))) :
    Nominal.NPrf (.imp ph ta) :=
  by
  have p0000 := @g_n_3jca ph ps ch th hyp_syl3anbrc_1 hyp_syl3anbrc_2 hyp_syl3anbrc_3
  have p0001 := @g_sylibr ph (syn_w3a ps ch th) ta p0000 hyp_syl3anbrc_4
  exact p0001

@[expose]
noncomputable def g_n_3anim123i (ph : Wff) (ps : Wff) (ch : Wff) (th : Wff) (ta : Wff)
    (et : Wff) (hyp_n_3anim123i_1 : Nominal.NPrf (.imp ph ps))
    (hyp_n_3anim123i_2 : Nominal.NPrf (.imp ch th))
    (hyp_n_3anim123i_3 : Nominal.NPrf (.imp ta et)) :
    Nominal.NPrf (.imp (syn_w3a ph ch ta) (syn_w3a ps th et)) :=
  by
  have p0000 := @g_n_3ad2ant1 ph ch ps ta hyp_n_3anim123i_1
  have p0001 := @g_n_3ad2ant2 ch ph th ta hyp_n_3anim123i_2
  have p0002 := @g_n_3ad2ant3 ta ph et ch hyp_n_3anim123i_3
  have p0003 := @g_n_3jca (syn_w3a ph ch ta) ps th et p0000 p0001 p0002
  exact p0003

@[expose]
noncomputable def g_n_3anim1i (ph : Wff) (ps : Wff) (ch : Wff) (th : Wff)
    (hyp_n_3animi_1 : Nominal.NPrf (.imp ph ps)) :
    Nominal.NPrf (.imp (syn_w3a ph ch th) (syn_w3a ps ch th)) :=
  by
  have p0000 := @g_id ch
  have p0001 := @g_id th
  have p0002 := @g_n_3anim123i ph ps ch ch th th hyp_n_3animi_1 p0000 p0001
  exact p0002

@[expose]
noncomputable def g_n_3anbi123i (ph : Wff) (ps : Wff) (ch : Wff) (th : Wff) (ta : Wff)
    (et : Wff) (hyp_bi3_1 : Nominal.NPrf (syn_wb ph ps))
    (hyp_bi3_2 : Nominal.NPrf (syn_wb ch th)) (hyp_bi3_3 : Nominal.NPrf (syn_wb ta et)) :
    Nominal.NPrf (syn_wb (syn_w3a ph ch ta) (syn_w3a ps th et)) :=
  by
  have p0000 := @g_anbi12i ph ps ch th hyp_bi3_1 hyp_bi3_2
  have p0001 := @g_anbi12i (syn_wa ph ch) (syn_wa ps th) ta et p0000 hyp_bi3_3
  have p0002 := (Nominal.biimpRefl (syn_w3a ph ch ta))
  have p0003 := (Nominal.biimpRefl (syn_w3a ps th et))
  have p0004 :=
    @g_n_3bitr4i (syn_wa (syn_wa ph ch) ta) (syn_wa (syn_wa ps th) et) (syn_w3a ph ch ta)
      (syn_w3a ps th et) p0001 p0002 p0003
  exact p0004

@[expose]
noncomputable def g_n_3anbi1i (ph : Wff) (ps : Wff) (ch : Wff) (th : Wff)
    (hyp_n_3anbi1i_1 : Nominal.NPrf (syn_wb ph ps)) :
    Nominal.NPrf (syn_wb (syn_w3a ph ch th) (syn_w3a ps ch th)) :=
  by
  have p0000 := @g_biid ch
  have p0001 := @g_biid th
  have p0002 := @g_n_3anbi123i ph ps ch ch th th hyp_n_3anbi1i_1 p0000 p0001
  exact p0002

@[expose]
noncomputable def g_n_3anbi2i (ph : Wff) (ps : Wff) (ch : Wff) (th : Wff)
    (hyp_n_3anbi1i_1 : Nominal.NPrf (syn_wb ph ps)) :
    Nominal.NPrf (syn_wb (syn_w3a ch ph th) (syn_w3a ch ps th)) :=
  by
  have p0000 := @g_biid ch
  have p0001 := @g_biid th
  have p0002 := @g_n_3anbi123i ch ch ph ps th th p0000 hyp_n_3anbi1i_1 p0001
  exact p0002

@[expose]
noncomputable def g_n_3anbi3i (ph : Wff) (ps : Wff) (ch : Wff) (th : Wff)
    (hyp_n_3anbi1i_1 : Nominal.NPrf (syn_wb ph ps)) :
    Nominal.NPrf (syn_wb (syn_w3a ch th ph) (syn_w3a ch th ps)) :=
  by
  have p0000 := @g_biid ch
  have p0001 := @g_biid th
  have p0002 := @g_n_3anbi123i ch ch th th ph ps p0000 p0001 hyp_n_3anbi1i_1
  exact p0002

@[expose]
noncomputable def g_n_3imp (ph : Wff) (ps : Wff) (ch : Wff) (th : Wff)
    (hyp_n_3imp_1 : Nominal.NPrf (.imp ph (.imp ps (.imp ch th)))) :
    Nominal.NPrf (.imp (syn_w3a ph ps ch) th) :=
  by
  have p0000 := (Nominal.biimpRefl (syn_w3a ph ps ch))
  have p0001 := @g_imp31 ph ps ch th hyp_n_3imp_1
  have p0002 := @g_sylbi (syn_w3a ph ps ch) (syn_wa (syn_wa ph ps) ch) th p0000 p0001
  exact p0002

@[expose]
noncomputable def g_n_3impa (ph : Wff) (ps : Wff) (ch : Wff) (th : Wff)
    (hyp_n_3impa_1 : Nominal.NPrf (.imp (syn_wa (syn_wa ph ps) ch) th)) :
    Nominal.NPrf (.imp (syn_w3a ph ps ch) th) :=
  by
  have p0000 := @g_exp31 ph ps ch th hyp_n_3impa_1
  have p0001 := @g_n_3imp ph ps ch th p0000
  exact p0001

@[expose]
noncomputable def g_n_3impb (ph : Wff) (ps : Wff) (ch : Wff) (th : Wff)
    (hyp_n_3impb_1 : Nominal.NPrf (.imp (syn_wa ph (syn_wa ps ch)) th)) :
    Nominal.NPrf (.imp (syn_w3a ph ps ch) th) :=
  by
  have p0000 := @g_exp32 ph ps ch th hyp_n_3impb_1
  have p0001 := @g_n_3imp ph ps ch th p0000
  exact p0001

@[expose]
noncomputable def g_n_3impia (ph : Wff) (ps : Wff) (ch : Wff) (th : Wff)
    (hyp_n_3impia_1 : Nominal.NPrf (.imp (syn_wa ph ps) (.imp ch th))) :
    Nominal.NPrf (.imp (syn_w3a ph ps ch) th) :=
  by
  have p0000 := @g_ex ph ps (.imp ch th) hyp_n_3impia_1
  have p0001 := @g_n_3imp ph ps ch th p0000
  exact p0001

@[expose]
noncomputable def g_n_3impib (ph : Wff) (ps : Wff) (ch : Wff) (th : Wff)
    (hyp_n_3impib_1 : Nominal.NPrf (.imp ph (.imp (syn_wa ps ch) th))) :
    Nominal.NPrf (.imp (syn_w3a ph ps ch) th) :=
  by
  have p0000 := @g_exp3a ph ps ch th hyp_n_3impib_1
  have p0001 := @g_n_3imp ph ps ch th p0000
  exact p0001

@[expose]
noncomputable def g_n_3exp (ph : Wff) (ps : Wff) (ch : Wff) (th : Wff)
    (hyp_n_3exp_1 : Nominal.NPrf (.imp (syn_w3a ph ps ch) th)) :
    Nominal.NPrf (.imp ph (.imp ps (.imp ch th))) :=
  by
  have p0000 := @g_pm3_2an3 ph ps ch
  have p0001 := @g_syl8 ph ps ch (syn_w3a ph ps ch) th p0000 hyp_n_3exp_1
  exact p0001

@[expose]
noncomputable def g_n_3expa (ph : Wff) (ps : Wff) (ch : Wff) (th : Wff)
    (hyp_n_3exp_1 : Nominal.NPrf (.imp (syn_w3a ph ps ch) th)) :
    Nominal.NPrf (.imp (syn_wa (syn_wa ph ps) ch) th) :=
  by
  have p0000 := @g_n_3exp ph ps ch th hyp_n_3exp_1
  have p0001 := @g_imp31 ph ps ch th p0000
  exact p0001

@[expose]
noncomputable def g_n_3expb (ph : Wff) (ps : Wff) (ch : Wff) (th : Wff)
    (hyp_n_3exp_1 : Nominal.NPrf (.imp (syn_w3a ph ps ch) th)) :
    Nominal.NPrf (.imp (syn_wa ph (syn_wa ps ch)) th) :=
  by
  have p0000 := @g_n_3exp ph ps ch th hyp_n_3exp_1
  have p0001 := @g_imp32 ph ps ch th p0000
  exact p0001

@[expose]
noncomputable def g_n_3expia (ph : Wff) (ps : Wff) (ch : Wff) (th : Wff)
    (hyp_n_3exp_1 : Nominal.NPrf (.imp (syn_w3a ph ps ch) th)) :
    Nominal.NPrf (.imp (syn_wa ph ps) (.imp ch th)) :=
  by
  have p0000 := @g_n_3exp ph ps ch th hyp_n_3exp_1
  have p0001 := @g_imp ph ps (.imp ch th) p0000
  exact p0001

@[expose]
noncomputable def g_n_3expib (ph : Wff) (ps : Wff) (ch : Wff) (th : Wff)
    (hyp_n_3exp_1 : Nominal.NPrf (.imp (syn_w3a ph ps ch) th)) :
    Nominal.NPrf (.imp ph (.imp (syn_wa ps ch) th)) :=
  by
  have p0000 := @g_n_3exp ph ps ch th hyp_n_3exp_1
  have p0001 := @g_imp3a ph ps ch th p0000
  exact p0001

@[expose]
noncomputable def g_n_3com12 (ph : Wff) (ps : Wff) (ch : Wff) (th : Wff)
    (hyp_n_3exp_1 : Nominal.NPrf (.imp (syn_w3a ph ps ch) th)) :
    Nominal.NPrf (.imp (syn_w3a ps ph ch) th) :=
  by
  have p0000 := @g_n_3ancoma ps ph ch
  have p0001 := @g_sylbi (syn_w3a ps ph ch) (syn_w3a ph ps ch) th p0000 hyp_n_3exp_1
  exact p0001

@[expose]
noncomputable def g_n_3com13 (ph : Wff) (ps : Wff) (ch : Wff) (th : Wff)
    (hyp_n_3exp_1 : Nominal.NPrf (.imp (syn_w3a ph ps ch) th)) :
    Nominal.NPrf (.imp (syn_w3a ch ps ph) th) :=
  by
  have p0000 := @g_n_3anrev ch ps ph
  have p0001 := @g_sylbi (syn_w3a ch ps ph) (syn_w3a ph ps ch) th p0000 hyp_n_3exp_1
  exact p0001

@[expose]
noncomputable def g_n_3com23 (ph : Wff) (ps : Wff) (ch : Wff) (th : Wff)
    (hyp_n_3exp_1 : Nominal.NPrf (.imp (syn_w3a ph ps ch) th)) :
    Nominal.NPrf (.imp (syn_w3a ph ch ps) th) :=
  by
  have p0000 := @g_n_3exp ph ps ch th hyp_n_3exp_1
  have p0001 := @g_com23 ph ps ch th p0000
  have p0002 := @g_n_3imp ph ch ps th p0001
  exact p0002

@[expose]
noncomputable def g_n_3coml (ph : Wff) (ps : Wff) (ch : Wff) (th : Wff)
    (hyp_n_3exp_1 : Nominal.NPrf (.imp (syn_w3a ph ps ch) th)) :
    Nominal.NPrf (.imp (syn_w3a ps ch ph) th) :=
  by
  have p0000 := @g_n_3com23 ph ps ch th hyp_n_3exp_1
  have p0001 := @g_n_3com13 ph ch ps th p0000
  exact p0001

@[expose]
noncomputable def g_n_3impd (ph : Wff) (ps : Wff) (ch : Wff) (th : Wff) (ta : Wff)
    (hyp_n_3imp1_1 : Nominal.NPrf (.imp ph (.imp ps (.imp ch (.imp th ta))))) :
    Nominal.NPrf (.imp ph (.imp (syn_w3a ps ch th) ta)) :=
  by
  have p0000 := @g_com4l ph ps ch th ta hyp_n_3imp1_1
  have p0001 := @g_n_3imp ps ch th (.imp ph ta) p0000
  have p0002 := @g_com12 (syn_w3a ps ch th) ph ta p0001
  exact p0002

@[expose]
noncomputable def g_n_3expd (ph : Wff) (ps : Wff) (ch : Wff) (th : Wff) (ta : Wff)
    (hyp_n_3expd_1 : Nominal.NPrf (.imp ph (.imp (syn_w3a ps ch th) ta))) :
    Nominal.NPrf (.imp ph (.imp ps (.imp ch (.imp th ta)))) :=
  by
  have p0000 := @g_com12 ph (syn_w3a ps ch th) ta hyp_n_3expd_1
  have p0001 := @g_n_3exp ps ch th (.imp ph ta) p0000
  have p0002 := @g_com4r ps ch th ph ta p0001
  exact p0002

@[expose]
noncomputable def g_n_3exp2 (ph : Wff) (ps : Wff) (ch : Wff) (th : Wff) (ta : Wff)
    (hyp_n_3exp2_1 : Nominal.NPrf (.imp (syn_wa ph (syn_w3a ps ch th)) ta)) :
    Nominal.NPrf (.imp ph (.imp ps (.imp ch (.imp th ta)))) :=
  by
  have p0000 := @g_ex ph (syn_w3a ps ch th) ta hyp_n_3exp2_1
  have p0001 := @g_n_3expd ph ps ch th ta p0000
  exact p0001

@[expose]
noncomputable def g_n_3adant1r (ph : Wff) (ps : Wff) (ch : Wff) (th : Wff) (ta : Wff)
    (hyp_n_3adant1l_1 : Nominal.NPrf (.imp (syn_w3a ph ps ch) th)) :
    Nominal.NPrf (.imp (syn_w3a (syn_wa ph ta) ps ch) th) :=
  by
  have p0000 := @g_n_3expb ph ps ch th hyp_n_3adant1l_1
  have p0001 := @g_adantlr ph (syn_wa ps ch) th ta p0000
  have p0002 := @g_n_3impb (syn_wa ph ta) ps ch th p0001
  exact p0002

@[expose]
noncomputable def g_syl12anc (ph : Wff) (ps : Wff) (ch : Wff) (th : Wff) (ta : Wff)
    (hyp_sylXanc_1 : Nominal.NPrf (.imp ph ps))
    (hyp_sylXanc_2 : Nominal.NPrf (.imp ph ch))
    (hyp_sylXanc_3 : Nominal.NPrf (.imp ph th))
    (hyp_syl12anc_4 : Nominal.NPrf (.imp (syn_wa ps (syn_wa ch th)) ta)) :
    Nominal.NPrf (.imp ph ta) :=
  by
  have p0000 := @g_jca32 ph ps ch th hyp_sylXanc_1 hyp_sylXanc_2 hyp_sylXanc_3
  have p0001 := @g_syl ph (syn_wa ps (syn_wa ch th)) ta p0000 hyp_syl12anc_4
  exact p0001

@[expose]
noncomputable def g_syl21anc (ph : Wff) (ps : Wff) (ch : Wff) (th : Wff) (ta : Wff)
    (hyp_sylXanc_1 : Nominal.NPrf (.imp ph ps))
    (hyp_sylXanc_2 : Nominal.NPrf (.imp ph ch))
    (hyp_sylXanc_3 : Nominal.NPrf (.imp ph th))
    (hyp_syl21anc_4 : Nominal.NPrf (.imp (syn_wa (syn_wa ps ch) th) ta)) :
    Nominal.NPrf (.imp ph ta) :=
  by
  have p0000 := @g_jca31 ph ps ch th hyp_sylXanc_1 hyp_sylXanc_2 hyp_sylXanc_3
  have p0001 := @g_syl ph (syn_wa (syn_wa ps ch) th) ta p0000 hyp_syl21anc_4
  exact p0001

@[expose]
noncomputable def g_syl3anc (ph : Wff) (ps : Wff) (ch : Wff) (th : Wff) (ta : Wff)
    (hyp_sylXanc_1 : Nominal.NPrf (.imp ph ps))
    (hyp_sylXanc_2 : Nominal.NPrf (.imp ph ch))
    (hyp_sylXanc_3 : Nominal.NPrf (.imp ph th))
    (hyp_syl111anc_4 : Nominal.NPrf (.imp (syn_w3a ps ch th) ta)) :
    Nominal.NPrf (.imp ph ta) :=
  by
  have p0000 := @g_n_3jca ph ps ch th hyp_sylXanc_1 hyp_sylXanc_2 hyp_sylXanc_3
  have p0001 := @g_syl ph (syn_w3a ps ch th) ta p0000 hyp_syl111anc_4
  exact p0001

@[expose]
noncomputable def g_syl22anc (ph : Wff) (ps : Wff) (ch : Wff) (th : Wff) (ta : Wff)
    (et : Wff) (hyp_sylXanc_1 : Nominal.NPrf (.imp ph ps))
    (hyp_sylXanc_2 : Nominal.NPrf (.imp ph ch))
    (hyp_sylXanc_3 : Nominal.NPrf (.imp ph th))
    (hyp_sylXanc_4 : Nominal.NPrf (.imp ph ta))
    (hyp_syl22anc_5 : Nominal.NPrf (.imp (syn_wa (syn_wa ps ch) (syn_wa th ta)) et)) :
    Nominal.NPrf (.imp ph et) :=
  by
  have p0000 := @g_jca ph ps ch hyp_sylXanc_1 hyp_sylXanc_2
  have p0001 :=
    @g_syl12anc ph (syn_wa ps ch) th ta et p0000 hyp_sylXanc_3 hyp_sylXanc_4
      hyp_syl22anc_5
  exact p0001

@[expose]
noncomputable def g_syl13anc (ph : Wff) (ps : Wff) (ch : Wff) (th : Wff) (ta : Wff)
    (et : Wff) (hyp_sylXanc_1 : Nominal.NPrf (.imp ph ps))
    (hyp_sylXanc_2 : Nominal.NPrf (.imp ph ch))
    (hyp_sylXanc_3 : Nominal.NPrf (.imp ph th))
    (hyp_sylXanc_4 : Nominal.NPrf (.imp ph ta))
    (hyp_syl13anc_5 : Nominal.NPrf (.imp (syn_wa ps (syn_w3a ch th ta)) et)) :
    Nominal.NPrf (.imp ph et) :=
  by
  have p0000 := @g_n_3jca ph ch th ta hyp_sylXanc_2 hyp_sylXanc_3 hyp_sylXanc_4
  have p0001 := @g_syl2anc ph ps (syn_w3a ch th ta) et hyp_sylXanc_1 p0000 hyp_syl13anc_5
  exact p0001

@[expose]
noncomputable def g_syl31anc (ph : Wff) (ps : Wff) (ch : Wff) (th : Wff) (ta : Wff)
    (et : Wff) (hyp_sylXanc_1 : Nominal.NPrf (.imp ph ps))
    (hyp_sylXanc_2 : Nominal.NPrf (.imp ph ch))
    (hyp_sylXanc_3 : Nominal.NPrf (.imp ph th))
    (hyp_sylXanc_4 : Nominal.NPrf (.imp ph ta))
    (hyp_syl31anc_5 : Nominal.NPrf (.imp (syn_wa (syn_w3a ps ch th) ta) et)) :
    Nominal.NPrf (.imp ph et) :=
  by
  have p0000 := @g_n_3jca ph ps ch th hyp_sylXanc_1 hyp_sylXanc_2 hyp_sylXanc_3
  have p0001 := @g_syl2anc ph (syn_w3a ps ch th) ta et p0000 hyp_sylXanc_4 hyp_syl31anc_5
  exact p0001

@[expose]
noncomputable def g_syl211anc (ph : Wff) (ps : Wff) (ch : Wff) (th : Wff) (ta : Wff)
    (et : Wff) (hyp_sylXanc_1 : Nominal.NPrf (.imp ph ps))
    (hyp_sylXanc_2 : Nominal.NPrf (.imp ph ch))
    (hyp_sylXanc_3 : Nominal.NPrf (.imp ph th))
    (hyp_sylXanc_4 : Nominal.NPrf (.imp ph ta))
    (hyp_syl211anc_5 : Nominal.NPrf (.imp (syn_w3a (syn_wa ps ch) th ta) et)) :
    Nominal.NPrf (.imp ph et) :=
  by
  have p0000 := @g_jca ph ps ch hyp_sylXanc_1 hyp_sylXanc_2
  have p0001 :=
    @g_syl3anc ph (syn_wa ps ch) th ta et p0000 hyp_sylXanc_3 hyp_sylXanc_4
      hyp_syl211anc_5
  exact p0001

@[expose]
noncomputable def g_syl221anc (ph : Wff) (ps : Wff) (ch : Wff) (th : Wff) (ta : Wff)
    (et : Wff) (ze : Wff) (hyp_sylXanc_1 : Nominal.NPrf (.imp ph ps))
    (hyp_sylXanc_2 : Nominal.NPrf (.imp ph ch))
    (hyp_sylXanc_3 : Nominal.NPrf (.imp ph th))
    (hyp_sylXanc_4 : Nominal.NPrf (.imp ph ta))
    (hyp_sylXanc_5 : Nominal.NPrf (.imp ph et))
    (hyp_syl221anc_6 : Nominal.NPrf (.imp (syn_w3a (syn_wa ps ch) (syn_wa th ta) et) ze)) :
    Nominal.NPrf (.imp ph ze) :=
  by
  have p0000 := @g_jca ph th ta hyp_sylXanc_3 hyp_sylXanc_4
  have p0001 :=
    @g_syl211anc ph ps ch (syn_wa th ta) et ze hyp_sylXanc_1 hyp_sylXanc_2 p0000
      hyp_sylXanc_5 hyp_syl221anc_6
  exact p0001

@[expose]
noncomputable def g_syl3an1 (ph : Wff) (ps : Wff) (ch : Wff) (th : Wff) (ta : Wff)
    (hyp_syl3an1_1 : Nominal.NPrf (.imp ph ps))
    (hyp_syl3an1_2 : Nominal.NPrf (.imp (syn_w3a ps ch th) ta)) :
    Nominal.NPrf (.imp (syn_w3a ph ch th) ta) :=
  by
  have p0000 := @g_n_3anim1i ph ps ch th hyp_syl3an1_1
  have p0001 := @g_syl (syn_w3a ph ch th) (syn_w3a ps ch th) ta p0000 hyp_syl3an1_2
  exact p0001

@[expose]
noncomputable def g_syl3an3 (ph : Wff) (ps : Wff) (ch : Wff) (th : Wff) (ta : Wff)
    (hyp_syl3an3_1 : Nominal.NPrf (.imp ph th))
    (hyp_syl3an3_2 : Nominal.NPrf (.imp (syn_w3a ps ch th) ta)) :
    Nominal.NPrf (.imp (syn_w3a ps ch ph) ta) :=
  by
  have p0000 := @g_n_3exp ps ch th ta hyp_syl3an3_2
  have p0001 := @g_syl7 ph th ps ch ta hyp_syl3an3_1 p0000
  have p0002 := @g_n_3imp ps ch ph ta p0001
  exact p0002

@[expose]
noncomputable def g_syl3an3b (ph : Wff) (ps : Wff) (ch : Wff) (th : Wff) (ta : Wff)
    (hyp_syl3an3b_1 : Nominal.NPrf (syn_wb ph th))
    (hyp_syl3an3b_2 : Nominal.NPrf (.imp (syn_w3a ps ch th) ta)) :
    Nominal.NPrf (.imp (syn_w3a ps ch ph) ta) :=
  by
  have p0000 := @g_biimpi ph th hyp_syl3an3b_1
  have p0001 := @g_syl3an3 ph ps ch th ta p0000 hyp_syl3an3b_2
  exact p0001

@[expose]
noncomputable def g_syl3an (ph : Wff) (ps : Wff) (ch : Wff) (th : Wff) (ta : Wff)
    (et : Wff) (ze : Wff) (hyp_syl3an_1 : Nominal.NPrf (.imp ph ps))
    (hyp_syl3an_2 : Nominal.NPrf (.imp ch th)) (hyp_syl3an_3 : Nominal.NPrf (.imp ta et))
    (hyp_syl3an_4 : Nominal.NPrf (.imp (syn_w3a ps th et) ze)) :
    Nominal.NPrf (.imp (syn_w3a ph ch ta) ze) :=
  by
  have p0000 := @g_n_3anim123i ph ps ch th ta et hyp_syl3an_1 hyp_syl3an_2 hyp_syl3an_3
  have p0001 := @g_syl (syn_w3a ph ch ta) (syn_w3a ps th et) ze p0000 hyp_syl3an_4
  exact p0001

@[expose]
noncomputable def g_n_3anidm12 (ph : Wff) (ps : Wff) (ch : Wff)
    (hyp_n_3anidm12_1 : Nominal.NPrf (.imp (syn_w3a ph ph ps) ch)) :
    Nominal.NPrf (.imp (syn_wa ph ps) ch) :=
  by
  have p0000 := @g_n_3expib ph ph ps ch hyp_n_3anidm12_1
  have p0001 := @g_anabsi5 ph ps ch p0000
  exact p0001

@[expose]
noncomputable def g_n_3anidm13 (ph : Wff) (ps : Wff) (ch : Wff)
    (hyp_n_3anidm13_1 : Nominal.NPrf (.imp (syn_w3a ph ps ph) ch)) :
    Nominal.NPrf (.imp (syn_wa ph ps) ch) :=
  by
  have p0000 := @g_n_3com23 ph ps ph ch hyp_n_3anidm13_1
  have p0001 := @g_n_3anidm12 ph ps ch p0000
  exact p0001

@[expose]
noncomputable def g_n_3anidm23 (ph : Wff) (ps : Wff) (ch : Wff)
    (hyp_n_3anidm23_1 : Nominal.NPrf (.imp (syn_w3a ph ps ps) ch)) :
    Nominal.NPrf (.imp (syn_wa ph ps) ch) :=
  by
  have p0000 := @g_n_3expa ph ps ps ch hyp_n_3anidm23_1
  have p0001 := @g_anabss3 ph ps ch p0000
  exact p0001

@[expose]
noncomputable def g_n_3jao (ph : Wff) (ps : Wff) (ch : Wff) (th : Wff) :
    Nominal.NPrf
      (.imp (syn_w3a (.imp ph ps) (.imp ch ps) (.imp th ps)) (.imp (syn_w3o ph ch th) ps)) :=
  by
  have p0000 := (Nominal.biimpRefl (syn_w3o ph ch th))
  have p0001 := @g_jao ph ps ch
  have p0002 := @g_jao (syn_wo ph ch) ps th
  have p0003 :=
    @g_syl6 (.imp ph ps) (.imp ch ps) (.imp (syn_wo ph ch) ps)
      (.imp (.imp th ps) (.imp (syn_wo (syn_wo ph ch) th) ps)) p0001 p0002
  have p0004 :=
    @g_n_3imp (.imp ph ps) (.imp ch ps) (.imp th ps) (.imp (syn_wo (syn_wo ph ch) th) ps)
      p0003
  have p0005 :=
    @g_syl5bi (syn_w3o ph ch th) (syn_wo (syn_wo ph ch) th)
      (syn_w3a (.imp ph ps) (.imp ch ps) (.imp th ps)) ps p0000 p0004
  exact p0005

@[expose]
noncomputable def g_n_3jaoi (ph : Wff) (ps : Wff) (ch : Wff) (th : Wff)
    (hyp_n_3jaoi_1 : Nominal.NPrf (.imp ph ps))
    (hyp_n_3jaoi_2 : Nominal.NPrf (.imp ch ps))
    (hyp_n_3jaoi_3 : Nominal.NPrf (.imp th ps)) :
    Nominal.NPrf (.imp (syn_w3o ph ch th) ps) :=
  by
  have p0000 :=
    @g_n_3pm3_2i (.imp ph ps) (.imp ch ps) (.imp th ps) hyp_n_3jaoi_1 hyp_n_3jaoi_2
      hyp_n_3jaoi_3
  have p0001 := @g_n_3jao ph ps ch th
  have p0002 := Nominal.mp p0000 p0001
  exact p0002

@[expose]
noncomputable def g_n_3jaod (ph : Wff) (ps : Wff) (ch : Wff) (th : Wff) (ta : Wff)
    (hyp_n_3jaod_1 : Nominal.NPrf (.imp ph (.imp ps ch)))
    (hyp_n_3jaod_2 : Nominal.NPrf (.imp ph (.imp th ch)))
    (hyp_n_3jaod_3 : Nominal.NPrf (.imp ph (.imp ta ch))) :
    Nominal.NPrf (.imp ph (.imp (syn_w3o ps th ta) ch)) :=
  by
  have p0000 := @g_n_3jao ps ch th ta
  have p0001 :=
    @g_syl3anc ph (.imp ps ch) (.imp th ch) (.imp ta ch) (.imp (syn_w3o ps th ta) ch)
      hyp_n_3jaod_1 hyp_n_3jaod_2 hyp_n_3jaod_3 p0000
  exact p0001

@[expose]
noncomputable def g_syl3an9b (ph : Wff) (ps : Wff) (ch : Wff) (th : Wff) (ta : Wff)
    (et : Wff) (ze : Wff) (hyp_syl3an9b_1 : Nominal.NPrf (.imp ph (syn_wb ps ch)))
    (hyp_syl3an9b_2 : Nominal.NPrf (.imp th (syn_wb ch ta)))
    (hyp_syl3an9b_3 : Nominal.NPrf (.imp et (syn_wb ta ze))) :
    Nominal.NPrf (.imp (syn_w3a ph th et) (syn_wb ps ze)) :=
  by
  have p0000 := @g_sylan9bb ph ps ch th ta hyp_syl3an9b_1 hyp_syl3an9b_2
  have p0001 := @g_sylan9bb (syn_wa ph th) ps ta et ze p0000 hyp_syl3an9b_3
  have p0002 := @g_n_3impa ph th et (syn_wb ps ze) p0001
  exact p0002

@[expose]
noncomputable def g_n_3orbi123d (ph : Wff) (ps : Wff) (ch : Wff) (th : Wff) (ta : Wff)
    (et : Wff) (ze : Wff) (hyp_bi3d_1 : Nominal.NPrf (.imp ph (syn_wb ps ch)))
    (hyp_bi3d_2 : Nominal.NPrf (.imp ph (syn_wb th ta)))
    (hyp_bi3d_3 : Nominal.NPrf (.imp ph (syn_wb et ze))) :
    Nominal.NPrf (.imp ph (syn_wb (syn_w3o ps th et) (syn_w3o ch ta ze))) :=
  by
  have p0000 := @g_orbi12d ph ps ch th ta hyp_bi3d_1 hyp_bi3d_2
  have p0001 := @g_orbi12d ph (syn_wo ps th) (syn_wo ch ta) et ze p0000 hyp_bi3d_3
  have p0002 := (Nominal.biimpRefl (syn_w3o ps th et))
  have p0003 := (Nominal.biimpRefl (syn_w3o ch ta ze))
  have p0004 :=
    @g_n_3bitr4g ph (syn_wo (syn_wo ps th) et) (syn_wo (syn_wo ch ta) ze)
      (syn_w3o ps th et) (syn_w3o ch ta ze) p0001 p0002 p0003
  exact p0004

@[expose]
noncomputable def g_n_3anbi123d (ph : Wff) (ps : Wff) (ch : Wff) (th : Wff) (ta : Wff)
    (et : Wff) (ze : Wff) (hyp_bi3d_1 : Nominal.NPrf (.imp ph (syn_wb ps ch)))
    (hyp_bi3d_2 : Nominal.NPrf (.imp ph (syn_wb th ta)))
    (hyp_bi3d_3 : Nominal.NPrf (.imp ph (syn_wb et ze))) :
    Nominal.NPrf (.imp ph (syn_wb (syn_w3a ps th et) (syn_w3a ch ta ze))) :=
  by
  have p0000 := @g_anbi12d ph ps ch th ta hyp_bi3d_1 hyp_bi3d_2
  have p0001 := @g_anbi12d ph (syn_wa ps th) (syn_wa ch ta) et ze p0000 hyp_bi3d_3
  have p0002 := (Nominal.biimpRefl (syn_w3a ps th et))
  have p0003 := (Nominal.biimpRefl (syn_w3a ch ta ze))
  have p0004 :=
    @g_n_3bitr4g ph (syn_wa (syn_wa ps th) et) (syn_wa (syn_wa ch ta) ze)
      (syn_w3a ps th et) (syn_w3a ch ta ze) p0001 p0002 p0003
  exact p0004

@[expose]
noncomputable def g_n_3anbi12d (ph : Wff) (ps : Wff) (ch : Wff) (th : Wff) (ta : Wff)
    (et : Wff) (hyp_n_3anbi12d_1 : Nominal.NPrf (.imp ph (syn_wb ps ch)))
    (hyp_n_3anbi12d_2 : Nominal.NPrf (.imp ph (syn_wb th ta))) :
    Nominal.NPrf (.imp ph (syn_wb (syn_w3a ps th et) (syn_w3a ch ta et))) :=
  by
  have p0000 := @g_biidd ph et
  have p0001 :=
    @g_n_3anbi123d ph ps ch th ta et et hyp_n_3anbi12d_1 hyp_n_3anbi12d_2 p0000
  exact p0001

@[expose]
noncomputable def g_n_3anbi13d (ph : Wff) (ps : Wff) (ch : Wff) (th : Wff) (ta : Wff)
    (et : Wff) (hyp_n_3anbi12d_1 : Nominal.NPrf (.imp ph (syn_wb ps ch)))
    (hyp_n_3anbi12d_2 : Nominal.NPrf (.imp ph (syn_wb th ta))) :
    Nominal.NPrf (.imp ph (syn_wb (syn_w3a ps et th) (syn_w3a ch et ta))) :=
  by
  have p0000 := @g_biidd ph et
  have p0001 :=
    @g_n_3anbi123d ph ps ch et et th ta hyp_n_3anbi12d_1 p0000 hyp_n_3anbi12d_2
  exact p0001

@[expose]
noncomputable def g_n_3anbi23d (ph : Wff) (ps : Wff) (ch : Wff) (th : Wff) (ta : Wff)
    (et : Wff) (hyp_n_3anbi12d_1 : Nominal.NPrf (.imp ph (syn_wb ps ch)))
    (hyp_n_3anbi12d_2 : Nominal.NPrf (.imp ph (syn_wb th ta))) :
    Nominal.NPrf (.imp ph (syn_wb (syn_w3a et ps th) (syn_w3a et ch ta))) :=
  by
  have p0000 := @g_biidd ph et
  have p0001 :=
    @g_n_3anbi123d ph et et ps ch th ta p0000 hyp_n_3anbi12d_1 hyp_n_3anbi12d_2
  exact p0001

@[expose]
noncomputable def g_n_3anbi1d (ph : Wff) (ps : Wff) (ch : Wff) (th : Wff) (ta : Wff)
    (hyp_n_3anbi1d_1 : Nominal.NPrf (.imp ph (syn_wb ps ch))) :
    Nominal.NPrf (.imp ph (syn_wb (syn_w3a ps th ta) (syn_w3a ch th ta))) :=
  by
  have p0000 := @g_biidd ph th
  have p0001 := @g_n_3anbi12d ph ps ch th th ta hyp_n_3anbi1d_1 p0000
  exact p0001

@[expose]
noncomputable def g_n_3anbi2d (ph : Wff) (ps : Wff) (ch : Wff) (th : Wff) (ta : Wff)
    (hyp_n_3anbi1d_1 : Nominal.NPrf (.imp ph (syn_wb ps ch))) :
    Nominal.NPrf (.imp ph (syn_wb (syn_w3a th ps ta) (syn_w3a th ch ta))) :=
  by
  have p0000 := @g_biidd ph th
  have p0001 := @g_n_3anbi12d ph th th ps ch ta p0000 hyp_n_3anbi1d_1
  exact p0001

@[expose]
noncomputable def g_n_3anbi3d (ph : Wff) (ps : Wff) (ch : Wff) (th : Wff) (ta : Wff)
    (hyp_n_3anbi1d_1 : Nominal.NPrf (.imp ph (syn_wb ps ch))) :
    Nominal.NPrf (.imp ph (syn_wb (syn_w3a th ta ps) (syn_w3a th ta ch))) :=
  by
  have p0000 := @g_biidd ph th
  have p0001 := @g_n_3anbi13d ph th th ps ch ta p0000 hyp_n_3anbi1d_1
  exact p0001

@[expose]
noncomputable def g_n_3orim123d (ph : Wff) (ps : Wff) (ch : Wff) (th : Wff) (ta : Wff)
    (et : Wff) (ze : Wff) (hyp_n_3anim123d_1 : Nominal.NPrf (.imp ph (.imp ps ch)))
    (hyp_n_3anim123d_2 : Nominal.NPrf (.imp ph (.imp th ta)))
    (hyp_n_3anim123d_3 : Nominal.NPrf (.imp ph (.imp et ze))) :
    Nominal.NPrf (.imp ph (.imp (syn_w3o ps th et) (syn_w3o ch ta ze))) :=
  by
  have p0000 := @g_orim12d ph ps ch th ta hyp_n_3anim123d_1 hyp_n_3anim123d_2
  have p0001 := @g_orim12d ph (syn_wo ps th) (syn_wo ch ta) et ze p0000 hyp_n_3anim123d_3
  have p0002 := (Nominal.biimpRefl (syn_w3o ps th et))
  have p0003 := (Nominal.biimpRefl (syn_w3o ch ta ze))
  have p0004 :=
    @g_n_3imtr4g ph (syn_wo (syn_wo ps th) et) (syn_wo (syn_wo ch ta) ze)
      (syn_w3o ps th et) (syn_w3o ch ta ze) p0001 p0002 p0003
  exact p0004

@[expose]
noncomputable def g_an6 (ph : Wff) (ps : Wff) (ch : Wff) (th : Wff) (ta : Wff)
    (et : Wff) :
    Nominal.NPrf
      (syn_wb (syn_wa (syn_w3a ph ps ch) (syn_w3a th ta et))
        (syn_w3a (syn_wa ph th) (syn_wa ps ta) (syn_wa ch et))) :=
  by
  have p0000 := @g_an4 (syn_wa ph ps) ch (syn_wa th ta) et
  have p0001 := @g_an4 ph ps th ta
  have p0002 :=
    @g_anbi1i (syn_wa (syn_wa ph ps) (syn_wa th ta))
      (syn_wa (syn_wa ph th) (syn_wa ps ta)) (syn_wa ch et) p0001
  have p0003 :=
    @g_bitri (syn_wa (syn_wa (syn_wa ph ps) ch) (syn_wa (syn_wa th ta) et))
      (syn_wa (syn_wa (syn_wa ph ps) (syn_wa th ta)) (syn_wa ch et))
      (syn_wa (syn_wa (syn_wa ph th) (syn_wa ps ta)) (syn_wa ch et)) p0000 p0002
  have p0004 := (Nominal.biimpRefl (syn_w3a ph ps ch))
  have p0005 := (Nominal.biimpRefl (syn_w3a th ta et))
  have p0006 :=
    @g_anbi12i (syn_w3a ph ps ch) (syn_wa (syn_wa ph ps) ch) (syn_w3a th ta et)
      (syn_wa (syn_wa th ta) et) p0004 p0005
  have p0007 := (Nominal.biimpRefl (syn_w3a (syn_wa ph th) (syn_wa ps ta) (syn_wa ch et)))
  have p0008 :=
    @g_n_3bitr4i (syn_wa (syn_wa (syn_wa ph ps) ch) (syn_wa (syn_wa th ta) et))
      (syn_wa (syn_wa (syn_wa ph th) (syn_wa ps ta)) (syn_wa ch et))
      (syn_wa (syn_w3a ph ps ch) (syn_w3a th ta et))
      (syn_w3a (syn_wa ph th) (syn_wa ps ta) (syn_wa ch et)) p0003 p0006 p0007
  exact p0008

@[expose]
noncomputable def g_n_3an6 (ph : Wff) (ps : Wff) (ch : Wff) (th : Wff) (ta : Wff)
    (et : Wff) :
    Nominal.NPrf
      (syn_wb (syn_w3a (syn_wa ph ps) (syn_wa ch th) (syn_wa ta et))
        (syn_wa (syn_w3a ph ch ta) (syn_w3a ps th et))) :=
  by
  have p0000 := @g_an6 ph ch ta ps th et
  have p0001 :=
    @g_bicomi (syn_wa (syn_w3a ph ch ta) (syn_w3a ps th et))
      (syn_w3a (syn_wa ph ps) (syn_wa ch th) (syn_wa ta et)) p0000
  exact p0001

@[expose]
noncomputable def g_mp3an1 (ph : Wff) (ps : Wff) (ch : Wff) (th : Wff)
    (hyp_mp3an1_1 : Nominal.NPrf ph)
    (hyp_mp3an1_2 : Nominal.NPrf (.imp (syn_w3a ph ps ch) th)) :
    Nominal.NPrf (.imp (syn_wa ps ch) th) :=
  by
  have p0000 := @g_n_3expb ph ps ch th hyp_mp3an1_2
  have p0001 := @g_mpan ph (syn_wa ps ch) th hyp_mp3an1_1 p0000
  exact p0001

@[expose]
noncomputable def g_mp3an2 (ph : Wff) (ps : Wff) (ch : Wff) (th : Wff)
    (hyp_mp3an2_1 : Nominal.NPrf ps)
    (hyp_mp3an2_2 : Nominal.NPrf (.imp (syn_w3a ph ps ch) th)) :
    Nominal.NPrf (.imp (syn_wa ph ch) th) :=
  by
  have p0000 := @g_n_3expa ph ps ch th hyp_mp3an2_2
  have p0001 := @g_mpanl2 ph ps ch th hyp_mp3an2_1 p0000
  exact p0001

@[expose]
noncomputable def g_mp3an3 (ph : Wff) (ps : Wff) (ch : Wff) (th : Wff)
    (hyp_mp3an3_1 : Nominal.NPrf ch)
    (hyp_mp3an3_2 : Nominal.NPrf (.imp (syn_w3a ph ps ch) th)) :
    Nominal.NPrf (.imp (syn_wa ph ps) th) :=
  by
  have p0000 := @g_n_3expia ph ps ch th hyp_mp3an3_2
  have p0001 := @g_mpi (syn_wa ph ps) ch th hyp_mp3an3_1 p0000
  exact p0001

@[expose]
noncomputable def g_mp3an12 (ph : Wff) (ps : Wff) (ch : Wff) (th : Wff)
    (hyp_mp3an12_1 : Nominal.NPrf ph) (hyp_mp3an12_2 : Nominal.NPrf ps)
    (hyp_mp3an12_3 : Nominal.NPrf (.imp (syn_w3a ph ps ch) th)) :
    Nominal.NPrf (.imp ch th) :=
  by
  have p0000 := @g_mp3an1 ph ps ch th hyp_mp3an12_1 hyp_mp3an12_3
  have p0001 := @g_mpan ps ch th hyp_mp3an12_2 p0000
  exact p0001

@[expose]
noncomputable def g_mp3an13 (ph : Wff) (ps : Wff) (ch : Wff) (th : Wff)
    (hyp_mp3an13_1 : Nominal.NPrf ph) (hyp_mp3an13_2 : Nominal.NPrf ch)
    (hyp_mp3an13_3 : Nominal.NPrf (.imp (syn_w3a ph ps ch) th)) :
    Nominal.NPrf (.imp ps th) :=
  by
  have p0000 := @g_mp3an3 ph ps ch th hyp_mp3an13_2 hyp_mp3an13_3
  have p0001 := @g_mpan ph ps th hyp_mp3an13_1 p0000
  exact p0001

@[expose]
noncomputable def g_mp3an23 (ph : Wff) (ps : Wff) (ch : Wff) (th : Wff)
    (hyp_mp3an23_1 : Nominal.NPrf ps) (hyp_mp3an23_2 : Nominal.NPrf ch)
    (hyp_mp3an23_3 : Nominal.NPrf (.imp (syn_w3a ph ps ch) th)) :
    Nominal.NPrf (.imp ph th) :=
  by
  have p0000 := @g_mp3an3 ph ps ch th hyp_mp3an23_2 hyp_mp3an23_3
  have p0001 := @g_mpan2 ph ps th hyp_mp3an23_1 p0000
  exact p0001

@[expose]
noncomputable def g_mp3an (ph : Wff) (ps : Wff) (ch : Wff) (th : Wff)
    (hyp_mp3an_1 : Nominal.NPrf ph) (hyp_mp3an_2 : Nominal.NPrf ps)
    (hyp_mp3an_3 : Nominal.NPrf ch)
    (hyp_mp3an_4 : Nominal.NPrf (.imp (syn_w3a ph ps ch) th)) : Nominal.NPrf th :=
  by
  have p0000 := @g_mp3an1 ph ps ch th hyp_mp3an_1 hyp_mp3an_4
  have p0001 := @g_mp2an ps ch th hyp_mp3an_2 hyp_mp3an_3 p0000
  exact p0001

@[expose]
noncomputable def g_mpd3an3 (ph : Wff) (ps : Wff) (ch : Wff) (th : Wff)
    (hyp_mpd3an3_2 : Nominal.NPrf (.imp (syn_wa ph ps) ch))
    (hyp_mpd3an3_3 : Nominal.NPrf (.imp (syn_w3a ph ps ch) th)) :
    Nominal.NPrf (.imp (syn_wa ph ps) th) :=
  by
  have p0000 := @g_n_3expa ph ps ch th hyp_mpd3an3_3
  have p0001 := @g_mpdan (syn_wa ph ps) ch th hyp_mpd3an3_2 p0000
  exact p0001

@[expose]
noncomputable def g_ecase23d (ph : Wff) (ps : Wff) (ch : Wff) (th : Wff)
    (hyp_ecase23d_1 : Nominal.NPrf (.imp ph (.neg ch)))
    (hyp_ecase23d_2 : Nominal.NPrf (.imp ph (.neg th)))
    (hyp_ecase23d_3 : Nominal.NPrf (.imp ph (syn_w3o ps ch th))) :
    Nominal.NPrf (.imp ph ps) :=
  by
  have p0000 := @g_ioran ch th
  have p0001 :=
    @g_sylanbrc ph (.neg ch) (.neg th) (.neg (syn_wo ch th)) hyp_ecase23d_1 hyp_ecase23d_2
      p0000
  have p0002 := @g_n_3orass ps ch th
  have p0003 :=
    @g_sylib ph (syn_w3o ps ch th) (syn_wo ps (syn_wo ch th)) hyp_ecase23d_3 p0002
  have p0004 := @g_ord ph ps (syn_wo ch th) p0003
  have p0005 := @g_mt3d ph ps (syn_wo ch th) p0001 p0004
  exact p0005

@[expose]
noncomputable def g_nancom (ph : Wff) (ps : Wff) :
    Nominal.NPrf (syn_wb (syn_wnan ph ps) (syn_wnan ps ph)) :=
  by
  have p0000 := @g_ancom ph ps
  have p0001 := @g_notbii (syn_wa ph ps) (syn_wa ps ph) p0000
  have p0002 := (Nominal.biimpRefl (syn_wnan ph ps))
  have p0003 := (Nominal.biimpRefl (syn_wnan ps ph))
  have p0004 :=
    @g_n_3bitr4i (.neg (syn_wa ph ps)) (.neg (syn_wa ps ph)) (syn_wnan ph ps)
      (syn_wnan ps ph) p0001 p0002 p0003
  exact p0004

@[expose]
noncomputable def g_nanbi1 (ph : Wff) (ps : Wff) (ch : Wff) :
    Nominal.NPrf (.imp (syn_wb ph ps) (syn_wb (syn_wnan ph ch) (syn_wnan ps ch))) :=
  by
  have p0000 := @g_anbi1 ph ps ch
  have p0001 := @g_notbid (syn_wb ph ps) (syn_wa ph ch) (syn_wa ps ch) p0000
  have p0002 := (Nominal.biimpRefl (syn_wnan ph ch))
  have p0003 := (Nominal.biimpRefl (syn_wnan ps ch))
  have p0004 :=
    @g_n_3bitr4g (syn_wb ph ps) (.neg (syn_wa ph ch)) (.neg (syn_wa ps ch))
      (syn_wnan ph ch) (syn_wnan ps ch) p0001 p0002 p0003
  exact p0004

@[expose]
noncomputable def g_nanbi2 (ph : Wff) (ps : Wff) (ch : Wff) :
    Nominal.NPrf (.imp (syn_wb ph ps) (syn_wb (syn_wnan ch ph) (syn_wnan ch ps))) :=
  by
  have p0000 := @g_nanbi1 ph ps ch
  have p0001 := @g_nancom ch ph
  have p0002 := @g_nancom ch ps
  have p0003 :=
    @g_n_3bitr4g (syn_wb ph ps) (syn_wnan ph ch) (syn_wnan ps ch) (syn_wnan ch ph)
      (syn_wnan ch ps) p0000 p0001 p0002
  exact p0003

@[expose]
noncomputable def g_nanbi12 (ph : Wff) (ps : Wff) (ch : Wff) (th : Wff) :
    Nominal.NPrf
      (.imp (syn_wa (syn_wb ph ps) (syn_wb ch th))
        (syn_wb (syn_wnan ph ch) (syn_wnan ps th))) :=
  by
  have p0000 := @g_nanbi1 ph ps ch
  have p0001 := @g_nanbi2 ch th ps
  have p0002 :=
    @g_sylan9bb (syn_wb ph ps) (syn_wnan ph ch) (syn_wnan ps ch) (syn_wb ch th)
      (syn_wnan ps th) p0000 p0001
  exact p0002

@[expose]
noncomputable def g_nanbi2i (ph : Wff) (ps : Wff) (ch : Wff)
    (hyp_nanbii_1 : Nominal.NPrf (syn_wb ph ps)) :
    Nominal.NPrf (syn_wb (syn_wnan ch ph) (syn_wnan ch ps)) :=
  by
  have p0000 := @g_nanbi2 ph ps ch
  have p0001 := Nominal.mp hyp_nanbii_1 p0000
  exact p0001

@[expose]
noncomputable def g_nanbi1d (ph : Wff) (ps : Wff) (ch : Wff) (th : Wff)
    (hyp_nanbid_1 : Nominal.NPrf (.imp ph (syn_wb ps ch))) :
    Nominal.NPrf (.imp ph (syn_wb (syn_wnan ps th) (syn_wnan ch th))) :=
  by
  have p0000 := @g_nanbi1 ps ch th
  have p0001 :=
    @g_syl ph (syn_wb ps ch) (syn_wb (syn_wnan ps th) (syn_wnan ch th)) hyp_nanbid_1 p0000
  exact p0001

@[expose]
noncomputable def g_nanbi12d (ph : Wff) (ps : Wff) (ch : Wff) (th : Wff) (ta : Wff)
    (hyp_nanbid_1 : Nominal.NPrf (.imp ph (syn_wb ps ch)))
    (hyp_nanbi12d_2 : Nominal.NPrf (.imp ph (syn_wb th ta))) :
    Nominal.NPrf (.imp ph (syn_wb (syn_wnan ps th) (syn_wnan ch ta))) :=
  by
  have p0000 := @g_nanbi12 ps ch th ta
  have p0001 :=
    @g_syl2anc ph (syn_wb ps ch) (syn_wb th ta) (syn_wb (syn_wnan ps th) (syn_wnan ch ta))
      hyp_nanbid_1 hyp_nanbi12d_2 p0000
  exact p0001

@[expose]
noncomputable def g_tru : Nominal.NPrf syn_wtru :=
  by
  let ph : Wff := .falsum
  have p0000 := @g_biid ph
  have p0001 : Nominal.NPrf (Wff.biimp syn_wtru (syn_wb ph ph)) :=
    (by
      have hTrue : Nominal.NPrf syn_wtru := by simpa [syn_wtru] using (@g_id Wff.falsum)
      have hRhs : Nominal.NPrf (syn_wb ph ph) := @g_biid ph
      exact
        @g_impbii syn_wtru (syn_wb ph ph)
          (Nominal.mp hRhs (Nominal.ax1 (syn_wb ph ph) syn_wtru))
          (Nominal.mp hTrue (Nominal.ax1 syn_wtru (syn_wb ph ph))))
  have p0002 := @g_mpbir syn_wtru (syn_wb ph ph) p0000 p0001
  exact p0002

@[expose]
noncomputable def g_trud (ph : Wff) (hyp_trud_1 : Nominal.NPrf (.imp syn_wtru ph)) :
    Nominal.NPrf ph := by
  have p0000 := @g_tru
  have p0001 := Nominal.mp p0000 hyp_trud_1
  exact p0001

@[expose]
noncomputable def g_ee22 (ph : Wff) (ps : Wff) (ch : Wff) (th : Wff) (ta : Wff)
    (hyp_ee22_1 : Nominal.NPrf (.imp ph (.imp ps ch)))
    (hyp_ee22_2 : Nominal.NPrf (.imp ph (.imp ps th)))
    (hyp_ee22_3 : Nominal.NPrf (.imp ch (.imp th ta))) :
    Nominal.NPrf (.imp ph (.imp ps ta)) :=
  by
  have p0000 := @g_syl6c ph ps ch th ta hyp_ee22_1 hyp_ee22_2 hyp_ee22_3
  exact p0000

@[expose]
noncomputable def g_ancomsimp (ph : Wff) (ps : Wff) (ch : Wff) :
    Nominal.NPrf (syn_wb (.imp (syn_wa ph ps) ch) (.imp (syn_wa ps ph) ch)) :=
  by
  have p0000 := @g_ancom ph ps
  have p0001 := @g_imbi1i (syn_wa ph ps) (syn_wa ps ph) ch p0000
  exact p0001

@[expose]
noncomputable def g_exp3acom23 (ph : Wff) (ps : Wff) (ch : Wff) (th : Wff)
    (hyp_exp3acom23_1 : Nominal.NPrf (.imp ph (.imp (syn_wa ps ch) th))) :
    Nominal.NPrf (.imp ph (.imp ch (.imp ps th))) :=
  by
  have p0000 := @g_exp3a ph ps ch th hyp_exp3acom23_1
  have p0001 := @g_com23 ph ps ch th p0000
  exact p0001

@[expose]
noncomputable def g_simplbi2com (ph : Wff) (ps : Wff) (ch : Wff)
    (hyp_simplbi2com_1 : Nominal.NPrf (syn_wb ph (syn_wa ps ch))) :
    Nominal.NPrf (.imp ch (.imp ps ph)) :=
  by
  have p0000 := @g_simplbi2 ph ps ch hyp_simplbi2com_1
  have p0001 := @g_com12 ps ch ph p0000
  exact p0001

@[expose]
noncomputable def g_ee10 (ph : Wff) (ps : Wff) (ch : Wff) (th : Wff)
    (hyp_ee10_1 : Nominal.NPrf (.imp ph ps)) (hyp_ee10_2 : Nominal.NPrf ch)
    (hyp_ee10_3 : Nominal.NPrf (.imp ps (.imp ch th))) : Nominal.NPrf (.imp ph th) :=
  by
  have p0000 := @g_mpi ps ch th hyp_ee10_2 hyp_ee10_3
  have p0001 := @g_syl ph ps th hyp_ee10_1 p0000
  exact p0001

@[expose]
noncomputable def g_ee02 (ph : Wff) (ps : Wff) (ch : Wff) (th : Wff) (ta : Wff)
    (hyp_ee02_1 : Nominal.NPrf ph) (hyp_ee02_2 : Nominal.NPrf (.imp ps (.imp ch th)))
    (hyp_ee02_3 : Nominal.NPrf (.imp ph (.imp th ta))) :
    Nominal.NPrf (.imp ps (.imp ch ta)) :=
  by
  have p0000 := @g_a1i ph ps hyp_ee02_1
  have p0001 := @g_sylsyld ps ph ch th ta p0000 hyp_ee02_2 hyp_ee02_3
  exact p0001

@[expose]
noncomputable def g_merlem1 (ph : Wff) (ps : Wff) (ch : Wff) (ta : Wff) :
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

@[expose]
noncomputable def g_merlem2 (ph : Wff) (ch : Wff) (th : Wff) :
    Nominal.NPrf (.imp (.imp (.imp ph ph) ch) (.imp th ch)) :=
  by
  have p0000 := @g_merlem1 ph (.neg th) (.imp ch ch) ph
  have p0001 := Nominal.axMeredith ch ch ph th (.imp ph ph)
  have p0002 := Nominal.mp p0000 p0001
  exact p0002

@[expose]
noncomputable def g_merlem3 (ph : Wff) (ps : Wff) (ch : Wff) :
    Nominal.NPrf (.imp (.imp (.imp ps ch) ph) (.imp ch ph)) :=
  by
  have p0000 := @g_merlem2 (.neg ch) (.imp (.neg ch) (.neg ch)) (.imp ph ph)
  have p0001 :=
    @g_merlem2 (.imp (.neg ch) (.neg ch)) (.imp (.imp ph ph) (.imp (.neg ch) (.neg ch)))
      (.imp (.imp (.imp ch ph) (.imp (.neg ps) (.neg ps))) ps)
  have p0002 := Nominal.mp p0000 p0001
  have p0003 :=
    Nominal.axMeredith ch ph ps ps (.imp (.imp ph ph) (.imp (.neg ch) (.neg ch)))
  have p0004 := Nominal.mp p0002 p0003
  have p0005 := Nominal.axMeredith ph ph ch ch (.imp ps ch)
  have p0006 := Nominal.mp p0004 p0005
  exact p0006

@[expose]
noncomputable def g_merlem4 (ph : Wff) (th : Wff) (ta : Wff) :
    Nominal.NPrf (.imp ta (.imp (.imp ta ph) (.imp th ph))) :=
  by
  have p0000 := Nominal.axMeredith ph ph th th ta
  have p0001 :=
    @g_merlem3 (.imp (.imp ta ph) (.imp th ph))
      (.imp (.imp (.imp ph ph) (.imp (.neg th) (.neg th))) th) ta
  have p0002 := Nominal.mp p0000 p0001
  exact p0002

@[expose]
noncomputable def g_merlem5 (ph : Wff) (ps : Wff) :
    Nominal.NPrf (.imp (.imp ph ps) (.imp (.neg (.neg ph)) ps)) :=
  by
  have p0000 := Nominal.axMeredith ps ps ps ps ps
  have p0001 := Nominal.axMeredith ps ps ps (.neg (.neg ph)) ph
  have p0002 :=
    @g_merlem1 (.neg ph) ps (.imp ph ps)
      (.neg (.imp (.imp (.imp (.imp (.imp ps ps) (.imp (.neg ps) (.neg ps))) ps) ps)
          (.imp (.imp ps ps) (.imp ps ps))))
  have p0003 :=
    @g_merlem4 ph (.imp (.imp (.imp ps ps) (.imp (.neg ps) (.neg (.neg (.neg ph))))) ps)
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

@[expose]
noncomputable def g_merlem6 (ph : Wff) (ps : Wff) (ch : Wff) (th : Wff) :
    Nominal.NPrf (.imp ch (.imp (.imp (.imp ps ch) ph) (.imp th ph))) :=
  by
  have p0000 := @g_merlem4 ph th (.imp ps ch)
  have p0001 := @g_merlem3 (.imp (.imp (.imp ps ch) ph) (.imp th ph)) ps ch
  have p0002 := Nominal.mp p0000 p0001
  exact p0002

@[expose]
noncomputable def g_merlem7 (ph : Wff) (ps : Wff) (ch : Wff) (th : Wff) (ta : Wff) :
    Nominal.NPrf
      (.imp ph (.imp (.imp (.imp ps ch) th)
          (.imp (.imp (.imp ch ta) (.imp (.neg th) (.neg ps))) th))) :=
  by
  have p0000 := @g_merlem4 th (.imp (.imp ch ta) (.imp (.neg th) (.neg ps))) (.imp ps ch)
  have p0001 :=
    @g_merlem6 (.neg ph) (.imp (.imp ps ch) th)
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

@[expose]
noncomputable def g_merlem8 (ps : Wff) (ch : Wff) (th : Wff) (ta : Wff) :
    Nominal.NPrf
      (.imp (.imp (.imp ps ch) th) (.imp (.imp (.imp ch ta) (.imp (.neg th) (.neg ps))) th)) :=
  by
  let ph : Wff := .falsum
  have p0000 := Nominal.axMeredith ph ph ph ph ph
  have p0001 :=
    @g_merlem7
      (.imp (.imp (.imp (.imp (.imp ph ph) (.imp (.neg ph) (.neg ph))) ph) ph)
        (.imp (.imp ph ph) (.imp ph ph)))
      ps ch th ta
  have p0002 := Nominal.mp p0000 p0001
  exact p0002

@[expose]
noncomputable def g_merlem9 (ph : Wff) (ps : Wff) (ch : Wff) (th : Wff) (ta : Wff)
    (et : Wff) :
    Nominal.NPrf
      (.imp (.imp (.imp ph ps) (.imp ch (.imp th (.imp ps ta))))
        (.imp et (.imp ch (.imp th (.imp ps ta))))) :=
  by
  have p0000 := @g_merlem6 (.neg et) ch (.imp th (.imp ps ta)) (.neg ps)
  have p0001 :=
    @g_merlem8 th (.imp ps ta)
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

@[expose]
noncomputable def g_merlem10 (ph : Wff) (ps : Wff) (th : Wff) :
    Nominal.NPrf (.imp (.imp ph (.imp ph ps)) (.imp th (.imp ph ps))) :=
  by
  have p0000 := Nominal.axMeredith ph ph ph ph ph
  have p0001 := Nominal.axMeredith (.imp ph ps) ph ph th ph
  have p0002 :=
    @g_merlem9 (.imp (.imp (.imp (.imp ph ps) ph) (.imp (.neg ph) (.neg th))) ph) ph
      (.imp ph (.imp ph ps)) th ps
      (.imp (.imp (.imp (.imp (.imp ph ph) (.imp (.neg ph) (.neg ph))) ph) ph)
        (.imp (.imp ph ph) (.imp ph ph)))
  have p0003 := Nominal.mp p0001 p0002
  have p0004 := Nominal.mp p0000 p0003
  exact p0004


end NFChoice.DirectNominalPrf.WPPReplay
