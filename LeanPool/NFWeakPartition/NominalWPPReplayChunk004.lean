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

@[expose]
noncomputable def g_merlem11 (ph : Wff) (ps : Wff) :
    Nominal.NPrf (.imp (.imp ph (.imp ph ps)) (.imp ph ps)) :=
  by
  have p0000 := Nominal.axMeredith ph ph ph ph ph
  have p0001 := @g_merlem10 ph ps (.imp ph (.imp ph ps))
  have p0002 :=
    @g_merlem10 (.imp ph (.imp ph ps)) (.imp ph ps)
      (.imp (.imp (.imp (.imp (.imp ph ph) (.imp (.neg ph) (.neg ph))) ph) ph)
        (.imp (.imp ph ph) (.imp ph ph)))
  have p0003 := Nominal.mp p0001 p0002
  have p0004 := Nominal.mp p0000 p0003
  exact p0004

@[expose]
noncomputable def g_merlem12 (ph : Wff) (ch : Wff) (th : Wff) :
    Nominal.NPrf (.imp (.imp (.imp th (.imp (.neg (.neg ch)) ch)) ph) ph) :=
  by
  have p0000 := @g_merlem5 ch ch
  have p0001 := @g_merlem2 ch (.imp (.neg (.neg ch)) ch) th
  have p0002 := Nominal.mp p0000 p0001
  have p0003 :=
    @g_merlem4 ph (.imp (.imp th (.imp (.neg (.neg ch)) ch)) ph)
      (.imp th (.imp (.neg (.neg ch)) ch))
  have p0004 := Nominal.mp p0002 p0003
  have p0005 := @g_merlem11 (.imp (.imp th (.imp (.neg (.neg ch)) ch)) ph) ph
  have p0006 := Nominal.mp p0004 p0005
  exact p0006

@[expose]
noncomputable def g_merlem13 (ph : Wff) (ps : Wff) (ch : Wff) (th : Wff) :
    Nominal.NPrf
      (.imp (.imp ph ps)
        (.imp (.imp (.imp th (.imp (.neg (.neg ch)) ch)) (.neg (.neg ph))) ps)) :=
  by
  have p0000 :=
    @g_merlem12 (.neg (.imp (.imp th (.imp (.neg (.neg ch)) ch)) (.neg (.neg ph)))) ch th
  have p0001 := @g_merlem12 (.neg (.neg ph)) ch th
  have p0002 :=
    @g_merlem5 (.imp (.imp th (.imp (.neg (.neg ch)) ch)) (.neg (.neg ph)))
      (.neg (.neg ph))
  have p0003 := Nominal.mp p0001 p0002
  have p0004 :=
    @g_merlem6 (.neg (.imp (.imp th (.imp (.neg (.neg ch)) ch)) (.neg (.neg ph))))
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
    @g_merlem6 ph (.imp ps ps)
      (.imp (.neg ph) (.neg (.imp (.imp th (.imp (.neg (.neg ch)) ch)) (.neg (.neg ph)))))
      (.imp (.imp (.imp ps ps) (.imp (.neg ph)
            (.neg (.imp (.imp th (.imp (.neg (.neg ch)) ch)) (.neg (.neg ph)))))) ph)
  have p0010 := Nominal.mp p0008 p0009
  have p0011 :=
    @g_merlem11
      (.imp (.imp (.imp ps ps) (.imp (.neg ph)
            (.neg (.imp (.imp th (.imp (.neg (.neg ch)) ch)) (.neg (.neg ph)))))) ph)
      ph
  have p0012 := Nominal.mp p0010 p0011
  have p0013 :=
    Nominal.axMeredith ps ps ph
      (.imp (.imp th (.imp (.neg (.neg ch)) ch)) (.neg (.neg ph))) ph
  have p0014 := Nominal.mp p0012 p0013
  exact p0014

@[expose]
noncomputable def g_luk_1 (ph : Wff) (ps : Wff) (ch : Wff) :
    Nominal.NPrf (.imp (.imp ph ps) (.imp (.imp ps ch) (.imp ph ch))) :=
  by
  have p0000 := Nominal.axMeredith ch ch (.neg (.neg ph)) ph ps
  have p0001 := @g_merlem13 ph ps (.neg ph) (.imp ch ch)
  have p0002 :=
    @g_merlem13 (.imp ph ps)
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

@[expose]
noncomputable def g_luk_2 (ph : Wff) : Nominal.NPrf (.imp (.imp (.neg ph) ph) ph) :=
  by
  have p0000 := @g_merlem5 ph (.neg (.imp (.neg ph) ph))
  have p0001 :=
    @g_merlem4 (.neg ph)
      (.imp (.imp (.imp ph (.neg (.imp (.neg ph) ph)))
          (.imp (.neg (.neg ph)) (.neg (.imp (.neg ph) ph)))) (.neg ph))
      (.imp (.imp ph (.neg (.imp (.neg ph) ph)))
        (.imp (.neg (.neg ph)) (.neg (.imp (.neg ph) ph))))
  have p0002 := Nominal.mp p0000 p0001
  have p0003 :=
    @g_merlem11
      (.imp (.imp (.imp ph (.neg (.imp (.neg ph) ph)))
          (.imp (.neg (.neg ph)) (.neg (.imp (.neg ph) ph)))) (.neg ph))
      (.neg ph)
  have p0004 := Nominal.mp p0002 p0003
  have p0005 :=
    Nominal.axMeredith ph (.neg (.imp (.neg ph) ph)) (.neg ph) (.imp (.neg ph) ph)
      (.neg ph)
  have p0006 := Nominal.mp p0004 p0005
  have p0007 := @g_merlem11 (.imp (.neg ph) ph) ph
  have p0008 := Nominal.mp p0006 p0007
  exact p0008

@[expose]
noncomputable def g_luk_3 (ph : Wff) (ps : Wff) :
    Nominal.NPrf (.imp ph (.imp (.neg ph) ps)) :=
  by
  have p0000 := @g_merlem11 (.neg ph) ps
  have p0001 := @g_merlem1 ph ps (.neg ph) (.imp (.neg ph) ps)
  have p0002 := Nominal.mp p0000 p0001
  exact p0002

@[expose]
noncomputable def g_luklem1 (ph : Wff) (ps : Wff) (ch : Wff)
    (hyp_luklem1_1 : Nominal.NPrf (.imp ph ps))
    (hyp_luklem1_2 : Nominal.NPrf (.imp ps ch)) : Nominal.NPrf (.imp ph ch) :=
  by
  have p0000 := @g_luk_1 ph ps ch
  have p0001 := Nominal.mp hyp_luklem1_1 p0000
  have p0002 := Nominal.mp hyp_luklem1_2 p0001
  exact p0002

@[expose]
noncomputable def g_luklem2 (ph : Wff) (ps : Wff) (ch : Wff) (th : Wff) :
    Nominal.NPrf (.imp (.imp ph (.neg ps)) (.imp (.imp (.imp ph ch) th) (.imp ps th))) :=
  by
  have p0000 := @g_luk_1 ph (.neg ps) ch
  have p0001 := @g_luk_3 ps ch
  have p0002 := @g_luk_1 ps (.imp (.neg ps) ch) (.imp ph ch)
  have p0003 := Nominal.mp p0001 p0002
  have p0004 :=
    @g_luklem1 (.imp ph (.neg ps)) (.imp (.imp (.neg ps) ch) (.imp ph ch))
      (.imp ps (.imp ph ch)) p0000 p0003
  have p0005 := @g_luk_1 ps (.imp ph ch) th
  have p0006 :=
    @g_luklem1 (.imp ph (.neg ps)) (.imp ps (.imp ph ch))
      (.imp (.imp (.imp ph ch) th) (.imp ps th)) p0004 p0005
  exact p0006

@[expose]
noncomputable def g_luklem3 (ph : Wff) (ps : Wff) (ch : Wff) (th : Wff) :
    Nominal.NPrf (.imp ph (.imp (.imp (.imp (.neg ph) ps) ch) (.imp th ch))) :=
  by
  have p0000 := @g_luk_3 ph (.neg th)
  have p0001 := @g_luklem2 (.neg ph) th ps ch
  have p0002 :=
    @g_luklem1 ph (.imp (.neg ph) (.neg th))
      (.imp (.imp (.imp (.neg ph) ps) ch) (.imp th ch)) p0000 p0001
  exact p0002

@[expose]
noncomputable def g_luklem4 (ph : Wff) (ps : Wff) :
    Nominal.NPrf (.imp (.imp (.imp (.imp (.neg ph) ph) ph) ps) ps) :=
  by
  have p0000 := @g_luk_2 (.imp (.imp (.neg ph) ph) ph)
  have p0001 := @g_luk_2 ph
  have p0002 :=
    @g_luklem3 (.imp (.imp (.neg ph) ph) ph) (.imp (.imp (.neg ph) ph) ph)
      (.imp (.imp (.neg ph) ph) ph) (.neg ps)
  have p0003 := Nominal.mp p0001 p0002
  have p0004 := Nominal.mp p0000 p0003
  have p0005 := @g_luk_1 (.neg ps) (.imp (.imp (.neg ph) ph) ph) ps
  have p0006 := Nominal.mp p0004 p0005
  have p0007 := @g_luk_2 ps
  have p0008 :=
    @g_luklem1 (.imp (.imp (.imp (.neg ph) ph) ph) ps) (.imp (.neg ps) ps) ps p0006 p0007
  exact p0008

@[expose]
noncomputable def g_luklem5 (ph : Wff) (ps : Wff) : Nominal.NPrf (.imp ph (.imp ps ph)) :=
  by
  have p0000 := @g_luklem3 ph ph ph ps
  have p0001 := @g_luklem4 ph (.imp ps ph)
  have p0002 :=
    @g_luklem1 ph (.imp (.imp (.imp (.neg ph) ph) ph) (.imp ps ph)) (.imp ps ph) p0000
      p0001
  exact p0002

@[expose]
noncomputable def g_ax1 (ph : Wff) (ps : Wff) : Nominal.NPrf (.imp ph (.imp ps ph)) :=
  by
  have p0000 := @g_luklem5 ph ps
  exact p0000

@[expose]
noncomputable def g_alnex (ph : Wff) (x : Var) :
    Nominal.NPrf (syn_wb (.all x (.neg ph)) (.neg (syn_wex x ph))) :=
  by
  have p0000 := (Nominal.biimpRefl (syn_wex x ph))
  have p0001 := @g_con2bii (syn_wex x ph) (.all x (.neg ph)) p0000
  exact p0001

@[expose]
noncomputable def g_gen2 (ph : Wff) (x : Var) (y : Var) (hyp_gen2_1 : Nominal.NPrf ph) :
    Nominal.NPrf (.all x (.all y ph)) :=
  by
  have p0000 := Nominal.gen hyp_gen2_1 y
  have p0001 := Nominal.gen p0000 x
  exact p0001

@[expose]
noncomputable def g_mpg (ph : Wff) (ps : Wff) (x : Var)
    (hyp_mpg_1 : Nominal.NPrf (.imp (.all x ph) ps)) (hyp_mpg_2 : Nominal.NPrf ph) :
    Nominal.NPrf ps := by
  have p0000 := Nominal.gen hyp_mpg_2 x
  have p0001 := Nominal.mp p0000 hyp_mpg_1
  exact p0001

@[expose]
noncomputable def g_mpgbi (ph : Wff) (ps : Wff) (x : Var)
    (hyp_mpgbi_1 : Nominal.NPrf (syn_wb (.all x ph) ps)) (hyp_mpgbi_2 : Nominal.NPrf ph) :
    Nominal.NPrf ps := by
  have p0000 := Nominal.gen hyp_mpgbi_2 x
  have p0001 := @g_mpbi (.all x ph) ps p0000 hyp_mpgbi_1
  exact p0001

@[expose]
noncomputable def g_mpgbir (ph : Wff) (ps : Wff) (x : Var)
    (hyp_mpgbir_1 : Nominal.NPrf (syn_wb ph (.all x ps)))
    (hyp_mpgbir_2 : Nominal.NPrf ps) : Nominal.NPrf ph :=
  by
  have p0000 := Nominal.gen hyp_mpgbir_2 x
  have p0001 := @g_mpbir ph (.all x ps) p0000 hyp_mpgbir_1
  exact p0001

@[expose]
noncomputable def g_nfi (ph : Wff) (x : Var)
    (hyp_nfi_1 : Nominal.NPrf (.imp ph (.all x ph))) : Nominal.NPrf (syn_wnf x ph) :=
  by
  have p0000 := (Nominal.biimpRefl (syn_wnf x ph))
  have p0001 := @g_mpgbir (syn_wnf x ph) (.imp ph (.all x ph)) x p0000 hyp_nfi_1
  exact p0001

@[expose]
noncomputable def g_hbth (ph : Wff) (x : Var) (hyp_hbth_1 : Nominal.NPrf ph) :
    Nominal.NPrf (.imp ph (.all x ph)) :=
  by
  have p0000 := Nominal.gen hyp_hbth_1 x
  have p0001 := @g_a1i (.all x ph) ph p0000
  exact p0001

@[expose]
noncomputable def g_nfth (ph : Wff) (x : Var) (hyp_hbth_1 : Nominal.NPrf ph) :
    Nominal.NPrf (syn_wnf x ph) :=
  by
  have p0000 := @g_hbth ph x hyp_hbth_1
  have p0001 := @g_nfi ph x p0000
  exact p0001

@[expose]
noncomputable def g_nftru (x : Var) : Nominal.NPrf (syn_wnf x syn_wtru) :=
  by
  have p0000 := @g_tru
  have p0001 := @g_nfth syn_wtru x p0000
  exact p0001

@[expose]
noncomputable def g_nex (ph : Wff) (x : Var) (hyp_nex_1 : Nominal.NPrf (.neg ph)) :
    Nominal.NPrf (.neg (syn_wex x ph)) :=
  by
  have p0000 := @g_alnex ph x
  have p0001 := @g_mpgbi (.neg ph) (.neg (syn_wex x ph)) x p0000 hyp_nex_1
  exact p0001

@[expose]
noncomputable def g_alim (ph : Wff) (ps : Wff) (x : Var) :
    Nominal.NPrf (.imp (.all x (.imp ph ps)) (.imp (.all x ph) (.all x ps))) :=
  by
  have p0000 := Nominal.ax5 x ph ps
  exact p0000

@[expose]
noncomputable def g_alimi (ph : Wff) (ps : Wff) (x : Var)
    (hyp_alimi_1 : Nominal.NPrf (.imp ph ps)) :
    Nominal.NPrf (.imp (.all x ph) (.all x ps)) :=
  by
  have p0000 := Nominal.ax5 x ph ps
  have p0001 := @g_mpg (.imp ph ps) (.imp (.all x ph) (.all x ps)) x p0000 hyp_alimi_1
  exact p0001

@[expose]
noncomputable def g_n_2alimi (ph : Wff) (ps : Wff) (x : Var) (y : Var)
    (hyp_alimi_1 : Nominal.NPrf (.imp ph ps)) :
    Nominal.NPrf (.imp (.all x (.all y ph)) (.all x (.all y ps))) :=
  by
  have p0000 := @g_alimi ph ps y hyp_alimi_1
  have p0001 := @g_alimi (.all y ph) (.all y ps) x p0000
  exact p0001

@[expose]
noncomputable def g_al2imi (ph : Wff) (ps : Wff) (ch : Wff) (x : Var)
    (hyp_al2imi_1 : Nominal.NPrf (.imp ph (.imp ps ch))) :
    Nominal.NPrf (.imp (.all x ph) (.imp (.all x ps) (.all x ch))) :=
  by
  have p0000 := @g_alimi ph (.imp ps ch) x hyp_al2imi_1
  have p0001 := @g_alim ps ch x
  have p0002 :=
    @g_syl (.all x ph) (.all x (.imp ps ch)) (.imp (.all x ps) (.all x ch)) p0000 p0001
  exact p0002

@[expose]
noncomputable def g_alanimi (ph : Wff) (ps : Wff) (ch : Wff) (x : Var)
    (hyp_alanimi_1 : Nominal.NPrf (.imp (syn_wa ph ps) ch)) :
    Nominal.NPrf (.imp (syn_wa (.all x ph) (.all x ps)) (.all x ch)) :=
  by
  have p0000 := @g_ex ph ps ch hyp_alanimi_1
  have p0001 := @g_al2imi ph ps ch x p0000
  have p0002 := @g_imp (.all x ph) (.all x ps) (.all x ch) p0001
  exact p0002

@[expose]
noncomputable def g_alimdh (ph : Wff) (ps : Wff) (ch : Wff) (x : Var)
    (hyp_alimdh_1 : Nominal.NPrf (.imp ph (.all x ph)))
    (hyp_alimdh_2 : Nominal.NPrf (.imp ph (.imp ps ch))) :
    Nominal.NPrf (.imp ph (.imp (.all x ps) (.all x ch))) :=
  by
  have p0000 := @g_al2imi ph ps ch x hyp_alimdh_2
  have p0001 := @g_syl ph (.all x ph) (.imp (.all x ps) (.all x ch)) hyp_alimdh_1 p0000
  exact p0001

@[expose]
noncomputable def g_albi (ph : Wff) (ps : Wff) (x : Var) :
    Nominal.NPrf (.imp (.all x (syn_wb ph ps)) (syn_wb (.all x ph) (.all x ps))) :=
  by
  have p0000 := @g_bi1 ph ps
  have p0001 := @g_al2imi (syn_wb ph ps) ph ps x p0000
  have p0002 := @g_bi2 ph ps
  have p0003 := @g_al2imi (syn_wb ph ps) ps ph x p0002
  have p0004 := @g_impbid (.all x (syn_wb ph ps)) (.all x ph) (.all x ps) p0001 p0003
  exact p0004

@[expose]
noncomputable def g_alrimih (ph : Wff) (ps : Wff) (x : Var)
    (hyp_alrimih_1 : Nominal.NPrf (.imp ph (.all x ph)))
    (hyp_alrimih_2 : Nominal.NPrf (.imp ph ps)) : Nominal.NPrf (.imp ph (.all x ps)) :=
  by
  have p0000 := @g_alimi ph ps x hyp_alrimih_2
  have p0001 := @g_syl ph (.all x ph) (.all x ps) hyp_alrimih_1 p0000
  exact p0001

@[expose]
noncomputable def g_albii (ph : Wff) (ps : Wff) (x : Var)
    (hyp_albii_1 : Nominal.NPrf (syn_wb ph ps)) :
    Nominal.NPrf (syn_wb (.all x ph) (.all x ps)) :=
  by
  have p0000 := @g_albi ph ps x
  have p0001 := @g_mpg (syn_wb ph ps) (syn_wb (.all x ph) (.all x ps)) x p0000 hyp_albii_1
  exact p0001

@[expose]
noncomputable def g_n_2albii (ph : Wff) (ps : Wff) (x : Var) (y : Var)
    (hyp_albii_1 : Nominal.NPrf (syn_wb ph ps)) :
    Nominal.NPrf (syn_wb (.all x (.all y ph)) (.all x (.all y ps))) :=
  by
  have p0000 := @g_albii ph ps y hyp_albii_1
  have p0001 := @g_albii (.all y ph) (.all y ps) x p0000
  exact p0001

@[expose]
noncomputable def g_hbxfrbi (ph : Wff) (ps : Wff) (x : Var)
    (hyp_hbxfrbi_1 : Nominal.NPrf (syn_wb ph ps))
    (hyp_hbxfrbi_2 : Nominal.NPrf (.imp ps (.all x ps))) :
    Nominal.NPrf (.imp ph (.all x ph)) :=
  by
  have p0000 := @g_albii ph ps x hyp_hbxfrbi_1
  have p0001 :=
    @g_n_3imtr4i ps (.all x ps) ph (.all x ph) hyp_hbxfrbi_2 hyp_hbxfrbi_1 p0000
  exact p0001

@[expose]
noncomputable def g_nfbii (ph : Wff) (ps : Wff) (x : Var)
    (hyp_nfbii_1 : Nominal.NPrf (syn_wb ph ps)) :
    Nominal.NPrf (syn_wb (syn_wnf x ph) (syn_wnf x ps)) :=
  by
  have p0000 := @g_albii ph ps x hyp_nfbii_1
  have p0001 := @g_imbi12i ph ps (.all x ph) (.all x ps) hyp_nfbii_1 p0000
  have p0002 := @g_albii (.imp ph (.all x ph)) (.imp ps (.all x ps)) x p0001
  have p0003 := (Nominal.biimpRefl (syn_wnf x ph))
  have p0004 := (Nominal.biimpRefl (syn_wnf x ps))
  have p0005 :=
    @g_n_3bitr4i (.all x (.imp ph (.all x ph))) (.all x (.imp ps (.all x ps)))
      (syn_wnf x ph) (syn_wnf x ps) p0002 p0003 p0004
  exact p0005

@[expose]
noncomputable def g_nfxfr (ph : Wff) (ps : Wff) (x : Var)
    (hyp_nfbii_1 : Nominal.NPrf (syn_wb ph ps))
    (hyp_nfxfr_2 : Nominal.NPrf (syn_wnf x ps)) : Nominal.NPrf (syn_wnf x ph) :=
  by
  have p0000 := @g_nfbii ph ps x hyp_nfbii_1
  have p0001 := @g_mpbir (syn_wnf x ph) (syn_wnf x ps) hyp_nfxfr_2 p0000
  exact p0001

@[expose]
noncomputable def g_nfxfrd (ph : Wff) (ps : Wff) (ch : Wff) (x : Var)
    (hyp_nfbii_1 : Nominal.NPrf (syn_wb ph ps))
    (hyp_nfxfrd_2 : Nominal.NPrf (.imp ch (syn_wnf x ps))) :
    Nominal.NPrf (.imp ch (syn_wnf x ph)) :=
  by
  have p0000 := @g_nfbii ph ps x hyp_nfbii_1
  have p0001 := @g_sylibr ch (syn_wnf x ps) (syn_wnf x ph) hyp_nfxfrd_2 p0000
  exact p0001

@[expose]
noncomputable def g_alex (ph : Wff) (x : Var) :
    Nominal.NPrf (syn_wb (.all x ph) (.neg (syn_wex x (.neg ph)))) :=
  by
  have p0000 := @g_notnot ph
  have p0001 := @g_albii ph (.neg (.neg ph)) x p0000
  have p0002 := @g_alnex (.neg ph) x
  have p0003 :=
    @g_bitri (.all x ph) (.all x (.neg (.neg ph))) (.neg (syn_wex x (.neg ph))) p0001
      p0002
  exact p0003

@[expose]
noncomputable def g_n_2nalexn (ph : Wff) (x : Var) (y : Var) :
    Nominal.NPrf (syn_wb (.neg (.all x (.all y ph))) (syn_wex x (syn_wex y (.neg ph)))) :=
  by
  have p0000 := (Nominal.biimpRefl (syn_wex x (syn_wex y (.neg ph))))
  have p0001 := @g_alex ph y
  have p0002 := @g_albii (.all y ph) (.neg (syn_wex y (.neg ph))) x p0001
  have p0003 :=
    @g_xchbinxr (syn_wex x (syn_wex y (.neg ph))) (.all x (.neg (syn_wex y (.neg ph))))
      (.all x (.all y ph)) p0000 p0002
  have p0004 :=
    @g_bicomi (syn_wex x (syn_wex y (.neg ph))) (.neg (.all x (.all y ph))) p0003
  exact p0004

@[expose]
noncomputable def g_exnal (ph : Wff) (x : Var) :
    Nominal.NPrf (syn_wb (syn_wex x (.neg ph)) (.neg (.all x ph))) :=
  by
  have p0000 := @g_alex ph x
  have p0001 := @g_con2bii (.all x ph) (syn_wex x (.neg ph)) p0000
  exact p0001

@[expose]
noncomputable def g_exim (ph : Wff) (ps : Wff) (x : Var) :
    Nominal.NPrf (.imp (.all x (.imp ph ps)) (.imp (syn_wex x ph) (syn_wex x ps))) :=
  by
  have p0000 := @g_con3 ph ps
  have p0001 := @g_al2imi (.imp ph ps) (.neg ps) (.neg ph) x p0000
  have p0002 := @g_alnex ps x
  have p0003 := @g_alnex ph x
  have p0004 :=
    @g_n_3imtr3g (.all x (.imp ph ps)) (.all x (.neg ps)) (.all x (.neg ph))
      (.neg (syn_wex x ps)) (.neg (syn_wex x ph)) p0001 p0002 p0003
  have p0005 := @g_con4d (.all x (.imp ph ps)) (syn_wex x ps) (syn_wex x ph) p0004
  exact p0005

@[expose]
noncomputable def g_eximi (ph : Wff) (ps : Wff) (x : Var)
    (hyp_eximi_1 : Nominal.NPrf (.imp ph ps)) :
    Nominal.NPrf (.imp (syn_wex x ph) (syn_wex x ps)) :=
  by
  have p0000 := @g_exim ph ps x
  have p0001 :=
    @g_mpg (.imp ph ps) (.imp (syn_wex x ph) (syn_wex x ps)) x p0000 hyp_eximi_1
  exact p0001

@[expose]
noncomputable def g_n_2eximi (ph : Wff) (ps : Wff) (x : Var) (y : Var)
    (hyp_eximi_1 : Nominal.NPrf (.imp ph ps)) :
    Nominal.NPrf (.imp (syn_wex x (syn_wex y ph)) (syn_wex x (syn_wex y ps))) :=
  by
  have p0000 := @g_eximi ph ps y hyp_eximi_1
  have p0001 := @g_eximi (syn_wex y ph) (syn_wex y ps) x p0000
  exact p0001

@[expose]
noncomputable def g_alinexa (ph : Wff) (ps : Wff) (x : Var) :
    Nominal.NPrf
      (syn_wb (.all x (.imp ph (.neg ps))) (.neg (syn_wex x (syn_wa ph ps)))) :=
  by
  have p0000 := @g_imnan ph ps
  have p0001 := @g_albii (.imp ph (.neg ps)) (.neg (syn_wa ph ps)) x p0000
  have p0002 := @g_alnex (syn_wa ph ps) x
  have p0003 :=
    @g_bitri (.all x (.imp ph (.neg ps))) (.all x (.neg (syn_wa ph ps)))
      (.neg (syn_wex x (syn_wa ph ps))) p0001 p0002
  exact p0003

@[expose]
noncomputable def g_exbi (ph : Wff) (ps : Wff) (x : Var) :
    Nominal.NPrf (.imp (.all x (syn_wb ph ps)) (syn_wb (syn_wex x ph) (syn_wex x ps))) :=
  by
  have p0000 := @g_bi1 ph ps
  have p0001 := @g_alimi (syn_wb ph ps) (.imp ph ps) x p0000
  have p0002 := @g_exim ph ps x
  have p0003 :=
    @g_syl (.all x (syn_wb ph ps)) (.all x (.imp ph ps))
      (.imp (syn_wex x ph) (syn_wex x ps)) p0001 p0002
  have p0004 := @g_bi2 ph ps
  have p0005 := @g_alimi (syn_wb ph ps) (.imp ps ph) x p0004
  have p0006 := @g_exim ps ph x
  have p0007 :=
    @g_syl (.all x (syn_wb ph ps)) (.all x (.imp ps ph))
      (.imp (syn_wex x ps) (syn_wex x ph)) p0005 p0006
  have p0008 :=
    @g_impbid (.all x (syn_wb ph ps)) (syn_wex x ph) (syn_wex x ps) p0003 p0007
  exact p0008

@[expose]
noncomputable def g_exbii (ph : Wff) (ps : Wff) (x : Var)
    (hyp_exbii_1 : Nominal.NPrf (syn_wb ph ps)) :
    Nominal.NPrf (syn_wb (syn_wex x ph) (syn_wex x ps)) :=
  by
  have p0000 := @g_exbi ph ps x
  have p0001 :=
    @g_mpg (syn_wb ph ps) (syn_wb (syn_wex x ph) (syn_wex x ps)) x p0000 hyp_exbii_1
  exact p0001

@[expose]
noncomputable def g_n_2exbii (ph : Wff) (ps : Wff) (x : Var) (y : Var)
    (hyp_n_2exbii_1 : Nominal.NPrf (syn_wb ph ps)) :
    Nominal.NPrf (syn_wb (syn_wex x (syn_wex y ph)) (syn_wex x (syn_wex y ps))) :=
  by
  have p0000 := @g_exbii ph ps y hyp_n_2exbii_1
  have p0001 := @g_exbii (syn_wex y ph) (syn_wex y ps) x p0000
  exact p0001

@[expose]
noncomputable def g_n_3exbii (ph : Wff) (ps : Wff) (x : Var) (y : Var) (z : Var)
    (hyp_n_3exbii_1 : Nominal.NPrf (syn_wb ph ps)) :
    Nominal.NPrf
      (syn_wb (syn_wex x (syn_wex y (syn_wex z ph))) (syn_wex x (syn_wex y (syn_wex z ps)))) :=
  by
  have p0000 := @g_exbii ph ps z hyp_n_3exbii_1
  have p0001 := @g_n_2exbii (syn_wex z ph) (syn_wex z ps) x y p0000
  exact p0001

@[expose]
noncomputable def g_exanali (ph : Wff) (ps : Wff) (x : Var) :
    Nominal.NPrf
      (syn_wb (syn_wex x (syn_wa ph (.neg ps))) (.neg (.all x (.imp ph ps)))) :=
  by
  have p0000 := @g_annim ph ps
  have p0001 := @g_exbii (syn_wa ph (.neg ps)) (.neg (.imp ph ps)) x p0000
  have p0002 := @g_exnal (.imp ph ps) x
  have p0003 :=
    @g_bitri (syn_wex x (syn_wa ph (.neg ps))) (syn_wex x (.neg (.imp ph ps)))
      (.neg (.all x (.imp ph ps))) p0001 p0002
  exact p0003

@[expose]
noncomputable def g_exancom (ph : Wff) (ps : Wff) (x : Var) :
    Nominal.NPrf (syn_wb (syn_wex x (syn_wa ph ps)) (syn_wex x (syn_wa ps ph))) :=
  by
  have p0000 := @g_ancom ph ps
  have p0001 := @g_exbii (syn_wa ph ps) (syn_wa ps ph) x p0000
  exact p0001

@[expose]
noncomputable def g_alrimdh (ph : Wff) (ps : Wff) (ch : Wff) (x : Var)
    (hyp_alrimdh_1 : Nominal.NPrf (.imp ph (.all x ph)))
    (hyp_alrimdh_2 : Nominal.NPrf (.imp ps (.all x ps)))
    (hyp_alrimdh_3 : Nominal.NPrf (.imp ph (.imp ps ch))) :
    Nominal.NPrf (.imp ph (.imp ps (.all x ch))) :=
  by
  have p0000 := @g_alimdh ph ps ch x hyp_alrimdh_1 hyp_alrimdh_3
  have p0001 := @g_syl5 ps (.all x ps) ph (.all x ch) hyp_alrimdh_2 p0000
  exact p0001

@[expose]
noncomputable def g_eximdh (ph : Wff) (ps : Wff) (ch : Wff) (x : Var)
    (hyp_eximdh_1 : Nominal.NPrf (.imp ph (.all x ph)))
    (hyp_eximdh_2 : Nominal.NPrf (.imp ph (.imp ps ch))) :
    Nominal.NPrf (.imp ph (.imp (syn_wex x ps) (syn_wex x ch))) :=
  by
  have p0000 := @g_alrimih ph (.imp ps ch) x hyp_eximdh_1 hyp_eximdh_2
  have p0001 := @g_exim ps ch x
  have p0002 :=
    @g_syl ph (.all x (.imp ps ch)) (.imp (syn_wex x ps) (syn_wex x ch)) p0000 p0001
  exact p0002

@[expose]
noncomputable def g_nexdh (ph : Wff) (ps : Wff) (x : Var)
    (hyp_nexdh_1 : Nominal.NPrf (.imp ph (.all x ph)))
    (hyp_nexdh_2 : Nominal.NPrf (.imp ph (.neg ps))) :
    Nominal.NPrf (.imp ph (.neg (syn_wex x ps))) :=
  by
  have p0000 := @g_alrimih ph (.neg ps) x hyp_nexdh_1 hyp_nexdh_2
  have p0001 := @g_alnex ps x
  have p0002 := @g_sylib ph (.all x (.neg ps)) (.neg (syn_wex x ps)) p0000 p0001
  exact p0002

@[expose]
noncomputable def g_albidh (ph : Wff) (ps : Wff) (ch : Wff) (x : Var)
    (hyp_albidh_1 : Nominal.NPrf (.imp ph (.all x ph)))
    (hyp_albidh_2 : Nominal.NPrf (.imp ph (syn_wb ps ch))) :
    Nominal.NPrf (.imp ph (syn_wb (.all x ps) (.all x ch))) :=
  by
  have p0000 := @g_alrimih ph (syn_wb ps ch) x hyp_albidh_1 hyp_albidh_2
  have p0001 := @g_albi ps ch x
  have p0002 :=
    @g_syl ph (.all x (syn_wb ps ch)) (syn_wb (.all x ps) (.all x ch)) p0000 p0001
  exact p0002

@[expose]
noncomputable def g_exbidh (ph : Wff) (ps : Wff) (ch : Wff) (x : Var)
    (hyp_exbidh_1 : Nominal.NPrf (.imp ph (.all x ph)))
    (hyp_exbidh_2 : Nominal.NPrf (.imp ph (syn_wb ps ch))) :
    Nominal.NPrf (.imp ph (syn_wb (syn_wex x ps) (syn_wex x ch))) :=
  by
  have p0000 := @g_alrimih ph (syn_wb ps ch) x hyp_exbidh_1 hyp_exbidh_2
  have p0001 := @g_exbi ps ch x
  have p0002 :=
    @g_syl ph (.all x (syn_wb ps ch)) (syn_wb (syn_wex x ps) (syn_wex x ch)) p0000 p0001
  exact p0002

@[expose]
noncomputable def g_exsimpl (ph : Wff) (ps : Wff) (x : Var) :
    Nominal.NPrf (.imp (syn_wex x (syn_wa ph ps)) (syn_wex x ph)) :=
  by
  have p0000 := @g_simpl ph ps
  have p0001 := @g_eximi (syn_wa ph ps) ph x p0000
  exact p0001

@[expose]
noncomputable def g_n_19_26 (ph : Wff) (ps : Wff) (x : Var) :
    Nominal.NPrf (syn_wb (.all x (syn_wa ph ps)) (syn_wa (.all x ph) (.all x ps))) :=
  by
  have p0000 := @g_simpl ph ps
  have p0001 := @g_alimi (syn_wa ph ps) ph x p0000
  have p0002 := @g_simpr ph ps
  have p0003 := @g_alimi (syn_wa ph ps) ps x p0002
  have p0004 := @g_jca (.all x (syn_wa ph ps)) (.all x ph) (.all x ps) p0001 p0003
  have p0005 := @g_id (syn_wa ph ps)
  have p0006 := @g_alanimi ph ps (syn_wa ph ps) x p0005
  have p0007 :=
    @g_impbii (.all x (syn_wa ph ps)) (syn_wa (.all x ph) (.all x ps)) p0004 p0006
  exact p0007

@[expose]
noncomputable def g_n_19_29 (ph : Wff) (ps : Wff) (x : Var) :
    Nominal.NPrf (.imp (syn_wa (.all x ph) (syn_wex x ps)) (syn_wex x (syn_wa ph ps))) :=
  by
  have p0000 := @g_pm3_2 ph ps
  have p0001 := @g_alimi ph (.imp ps (syn_wa ph ps)) x p0000
  have p0002 := @g_exim ps (syn_wa ph ps) x
  have p0003 :=
    @g_syl (.all x ph) (.all x (.imp ps (syn_wa ph ps)))
      (.imp (syn_wex x ps) (syn_wex x (syn_wa ph ps))) p0001 p0002
  have p0004 := @g_imp (.all x ph) (syn_wex x ps) (syn_wex x (syn_wa ph ps)) p0003
  exact p0004

@[expose]
noncomputable def g_n_19_29r (ph : Wff) (ps : Wff) (x : Var) :
    Nominal.NPrf (.imp (syn_wa (syn_wex x ph) (.all x ps)) (syn_wex x (syn_wa ph ps))) :=
  by
  have p0000 := @g_n_19_29 ps ph x
  have p0001 := @g_ancoms (.all x ps) (syn_wex x ph) (syn_wex x (syn_wa ps ph)) p0000
  have p0002 := @g_exancom ph ps x
  have p0003 :=
    @g_sylibr (syn_wa (syn_wex x ph) (.all x ps)) (syn_wex x (syn_wa ps ph))
      (syn_wex x (syn_wa ph ps)) p0001 p0002
  exact p0003

@[expose]
noncomputable def g_n_19_35 (ph : Wff) (ps : Wff) (x : Var) :
    Nominal.NPrf (syn_wb (syn_wex x (.imp ph ps)) (.imp (.all x ph) (syn_wex x ps))) :=
  by
  have p0000 := @g_n_19_26 ph (.neg ps) x
  have p0001 := @g_annim ph ps
  have p0002 := @g_albii (syn_wa ph (.neg ps)) (.neg (.imp ph ps)) x p0001
  have p0003 := @g_alnex ps x
  have p0004 := @g_anbi2i (.all x (.neg ps)) (.neg (syn_wex x ps)) (.all x ph) p0003
  have p0005 :=
    @g_n_3bitr3i (.all x (syn_wa ph (.neg ps))) (syn_wa (.all x ph) (.all x (.neg ps)))
      (.all x (.neg (.imp ph ps))) (syn_wa (.all x ph) (.neg (syn_wex x ps))) p0000 p0002
      p0004
  have p0006 := @g_alnex (.imp ph ps) x
  have p0007 := @g_annim (.all x ph) (syn_wex x ps)
  have p0008 :=
    @g_n_3bitr3i (.all x (.neg (.imp ph ps))) (syn_wa (.all x ph) (.neg (syn_wex x ps)))
      (.neg (syn_wex x (.imp ph ps))) (.neg (.imp (.all x ph) (syn_wex x ps))) p0005 p0006
      p0007
  have p0009 :=
    @g_con4bii (syn_wex x (.imp ph ps)) (.imp (.all x ph) (syn_wex x ps)) p0008
  exact p0009

@[expose]
noncomputable def g_n_19_35i (ph : Wff) (ps : Wff) (x : Var)
    (hyp_n_19_35i_1 : Nominal.NPrf (syn_wex x (.imp ph ps))) :
    Nominal.NPrf (.imp (.all x ph) (syn_wex x ps)) :=
  by
  have p0000 := @g_n_19_35 ph ps x
  have p0001 :=
    @g_mpbi (syn_wex x (.imp ph ps)) (.imp (.all x ph) (syn_wex x ps)) hyp_n_19_35i_1
      p0000
  exact p0001

@[expose]
noncomputable def g_n_19_43 (ph : Wff) (ps : Wff) (x : Var) :
    Nominal.NPrf
      (syn_wb (syn_wex x (syn_wo ph ps)) (syn_wo (syn_wex x ph) (syn_wex x ps))) :=
  by
  have p0000 := (Nominal.biimpRefl (syn_wo ph ps))
  have p0001 := @g_exbii (syn_wo ph ps) (.imp (.neg ph) ps) x p0000
  have p0002 := @g_n_19_35 (.neg ph) ps x
  have p0003 := @g_alnex ph x
  have p0004 := @g_imbi1i (.all x (.neg ph)) (.neg (syn_wex x ph)) (syn_wex x ps) p0003
  have p0005 :=
    @g_n_3bitri (syn_wex x (syn_wo ph ps)) (syn_wex x (.imp (.neg ph) ps))
      (.imp (.all x (.neg ph)) (syn_wex x ps)) (.imp (.neg (syn_wex x ph)) (syn_wex x ps))
      p0001 p0002 p0004
  have p0006 := (Nominal.biimpRefl (syn_wo (syn_wex x ph) (syn_wex x ps)))
  have p0007 :=
    @g_bitr4i (syn_wex x (syn_wo ph ps)) (.imp (.neg (syn_wex x ph)) (syn_wex x ps))
      (syn_wo (syn_wex x ph) (syn_wex x ps)) p0005 p0006
  exact p0007

@[expose]
noncomputable def g_n_19_40 (ph : Wff) (ps : Wff) (x : Var) :
    Nominal.NPrf
      (.imp (syn_wex x (syn_wa ph ps)) (syn_wa (syn_wex x ph) (syn_wex x ps))) :=
  by
  have p0000 := @g_exsimpl ph ps x
  have p0001 := @g_simpr ph ps
  have p0002 := @g_eximi (syn_wa ph ps) ps x p0001
  have p0003 :=
    @g_jca (syn_wex x (syn_wa ph ps)) (syn_wex x ph) (syn_wex x ps) p0000 p0002
  exact p0003

@[expose]
noncomputable def g_albiim (ph : Wff) (ps : Wff) (x : Var) :
    Nominal.NPrf
      (syn_wb (.all x (syn_wb ph ps)) (syn_wa (.all x (.imp ph ps)) (.all x (.imp ps ph)))) :=
  by
  have p0000 := @g_dfbi2 ph ps
  have p0001 := @g_albii (syn_wb ph ps) (syn_wa (.imp ph ps) (.imp ps ph)) x p0000
  have p0002 := @g_n_19_26 (.imp ph ps) (.imp ps ph) x
  have p0003 :=
    @g_bitri (.all x (syn_wb ph ps)) (.all x (syn_wa (.imp ph ps) (.imp ps ph)))
      (syn_wa (.all x (.imp ph ps)) (.all x (.imp ps ph))) p0001 p0002
  exact p0003

@[expose]
noncomputable def g_n_2albiim (ph : Wff) (ps : Wff) (x : Var) (y : Var) :
    Nominal.NPrf
      (syn_wb (.all x (.all y (syn_wb ph ps)))
        (syn_wa (.all x (.all y (.imp ph ps))) (.all x (.all y (.imp ps ph))))) :=
  by
  have p0000 := @g_albiim ph ps y
  have p0001 :=
    @g_albii (.all y (syn_wb ph ps)) (syn_wa (.all y (.imp ph ps)) (.all y (.imp ps ph)))
      x p0000
  have p0002 := @g_n_19_26 (.all y (.imp ph ps)) (.all y (.imp ps ph)) x
  have p0003 :=
    @g_bitri (.all x (.all y (syn_wb ph ps)))
      (.all x (syn_wa (.all y (.imp ph ps)) (.all y (.imp ps ph))))
      (syn_wa (.all x (.all y (.imp ph ps))) (.all x (.all y (.imp ps ph)))) p0001 p0002
  exact p0003

@[expose]
noncomputable def g_exintrbi (ph : Wff) (ps : Wff) (x : Var) :
    Nominal.NPrf
      (.imp (.all x (.imp ph ps)) (syn_wb (syn_wex x ph) (syn_wex x (syn_wa ph ps)))) :=
  by
  have p0000 := @g_pm4_71 ph ps
  have p0001 := @g_albii (.imp ph ps) (syn_wb ph (syn_wa ph ps)) x p0000
  have p0002 := @g_exbi ph (syn_wa ph ps) x
  have p0003 :=
    @g_sylbi (.all x (.imp ph ps)) (.all x (syn_wb ph (syn_wa ph ps)))
      (syn_wb (syn_wex x ph) (syn_wex x (syn_wa ph ps))) p0001 p0002
  exact p0003

@[expose]
noncomputable def g_exintr (ph : Wff) (ps : Wff) (x : Var) :
    Nominal.NPrf
      (.imp (.all x (.imp ph ps)) (.imp (syn_wex x ph) (syn_wex x (syn_wa ph ps)))) :=
  by
  have p0000 := @g_exintrbi ph ps x
  have p0001 :=
    @g_biimpd (.all x (.imp ph ps)) (syn_wex x ph) (syn_wex x (syn_wa ph ps)) p0000
  exact p0001

@[expose]
noncomputable def g_a17d (ph : Wff) (ps : Wff) (x : Var) (dv_ps_x : x ∉ ps.fv) :
    Nominal.NPrf (.imp ph (.imp ps (.all x ps))) :=
  by
  let proofSupport : Finset Var := ph.fv ∪ ps.fv ∪ ({ x } : Finset Var)
  have p0000 :=
    Nominal.ax17 ps x
      (by
        first
        | (aesop))
  have p0001 := @g_a1i (.imp ps (.all x ps)) ph p0000
  exact p0001

@[expose]
noncomputable def g_ax17e (ph : Wff) (x : Var) (dv_ph_x : x ∉ ph.fv) :
    Nominal.NPrf (.imp (syn_wex x ph) ph) :=
  by
  let proofSupport : Finset Var := ph.fv ∪ ({ x } : Finset Var)
  have p0000 := (Nominal.biimpRefl (syn_wex x ph))
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
  have p0002 := @g_con1i ph (.all x (.neg ph)) p0001
  have p0003 := @g_sylbi (syn_wex x ph) (.neg (.all x (.neg ph))) ph p0000 p0002
  exact p0003

@[expose]
noncomputable def g_nfv (ph : Wff) (x : Var) (dv_ph_x : x ∉ ph.fv) :
    Nominal.NPrf (syn_wnf x ph) :=
  by
  let proofSupport : Finset Var := ph.fv ∪ ({ x } : Finset Var)
  have p0000 :=
    Nominal.ax17 ph x
      (by
        first
        | (aesop))
  have p0001 := @g_nfi ph x p0000
  exact p0001

@[expose]
noncomputable def g_nfvd (ph : Wff) (ps : Wff) (x : Var) (dv_ps_x : x ∉ ps.fv) :
    Nominal.NPrf (.imp ph (syn_wnf x ps)) :=
  by
  let proofSupport : Finset Var := ph.fv ∪ ps.fv ∪ ({ x } : Finset Var)
  have p0000 :=
    @g_nfv ps x
      (by
        first
        | (aesop))
  have p0001 := @g_a1i (syn_wnf x ps) ph p0000
  exact p0001

@[expose]
noncomputable def g_alimdv (ph : Wff) (ps : Wff) (ch : Wff) (x : Var)
    (dv_ph_x : x ∉ ph.fv) (hyp_alimdv_1 : Nominal.NPrf (.imp ph (.imp ps ch))) :
    Nominal.NPrf (.imp ph (.imp (.all x ps) (.all x ch))) :=
  by
  let proofSupport : Finset Var := ph.fv ∪ ps.fv ∪ ch.fv ∪ ({ x } : Finset Var)
  have p0000 :=
    Nominal.ax17 ph x
      (by
        first
        | (aesop))
  have p0001 := @g_alimdh ph ps ch x p0000 hyp_alimdv_1
  exact p0001

@[expose]
noncomputable def g_eximdv (ph : Wff) (ps : Wff) (ch : Wff) (x : Var)
    (dv_ph_x : x ∉ ph.fv) (hyp_alimdv_1 : Nominal.NPrf (.imp ph (.imp ps ch))) :
    Nominal.NPrf (.imp ph (.imp (syn_wex x ps) (syn_wex x ch))) :=
  by
  let proofSupport : Finset Var := ph.fv ∪ ps.fv ∪ ch.fv ∪ ({ x } : Finset Var)
  have p0000 :=
    Nominal.ax17 ph x
      (by
        first
        | (aesop))
  have p0001 := @g_eximdh ph ps ch x p0000 hyp_alimdv_1
  exact p0001

@[expose]
noncomputable def g_n_2eximdv (ph : Wff) (ps : Wff) (ch : Wff) (x : Var) (y : Var)
    (dv_ph_x : x ∉ ph.fv) (dv_ph_y : y ∉ ph.fv)
    (hyp_n_2alimdv_1 : Nominal.NPrf (.imp ph (.imp ps ch))) :
    Nominal.NPrf (.imp ph (.imp (syn_wex x (syn_wex y ps)) (syn_wex x (syn_wex y ch)))) :=
  by
  let proofSupport : Finset Var :=
    ph.fv ∪ ps.fv ∪ ch.fv ∪ ({ x } : Finset Var) ∪ ({ y } : Finset Var)
  have p0000 :=
    @g_eximdv ph ps ch y
      (by
        first
        | (aesop))
      hyp_n_2alimdv_1
  have p0001 :=
    @g_eximdv ph (syn_wex y ps) (syn_wex y ch) x
      (by
        first
        | (aesop))
      p0000
  exact p0001

@[expose]
noncomputable def g_albidv (ph : Wff) (ps : Wff) (ch : Wff) (x : Var)
    (dv_ph_x : x ∉ ph.fv) (hyp_albidv_1 : Nominal.NPrf (.imp ph (syn_wb ps ch))) :
    Nominal.NPrf (.imp ph (syn_wb (.all x ps) (.all x ch))) :=
  by
  let proofSupport : Finset Var := ph.fv ∪ ps.fv ∪ ch.fv ∪ ({ x } : Finset Var)
  have p0000 :=
    Nominal.ax17 ph x
      (by
        first
        | (aesop))
  have p0001 := @g_albidh ph ps ch x p0000 hyp_albidv_1
  exact p0001

@[expose]
noncomputable def g_exbidv (ph : Wff) (ps : Wff) (ch : Wff) (x : Var)
    (dv_ph_x : x ∉ ph.fv) (hyp_albidv_1 : Nominal.NPrf (.imp ph (syn_wb ps ch))) :
    Nominal.NPrf (.imp ph (syn_wb (syn_wex x ps) (syn_wex x ch))) :=
  by
  let proofSupport : Finset Var := ph.fv ∪ ps.fv ∪ ch.fv ∪ ({ x } : Finset Var)
  have p0000 :=
    Nominal.ax17 ph x
      (by
        first
        | (aesop))
  have p0001 := @g_exbidh ph ps ch x p0000 hyp_albidv_1
  exact p0001

@[expose]
noncomputable def g_n_2albidv (ph : Wff) (ps : Wff) (ch : Wff) (x : Var) (y : Var)
    (dv_ph_x : x ∉ ph.fv) (dv_ph_y : y ∉ ph.fv)
    (hyp_n_2albidv_1 : Nominal.NPrf (.imp ph (syn_wb ps ch))) :
    Nominal.NPrf (.imp ph (syn_wb (.all x (.all y ps)) (.all x (.all y ch)))) :=
  by
  let proofSupport : Finset Var :=
    ph.fv ∪ ps.fv ∪ ch.fv ∪ ({ x } : Finset Var) ∪ ({ y } : Finset Var)
  have p0000 :=
    @g_albidv ph ps ch y
      (by
        first
        | (aesop))
      hyp_n_2albidv_1
  have p0001 :=
    @g_albidv ph (.all y ps) (.all y ch) x
      (by
        first
        | (aesop))
      p0000
  exact p0001

@[expose]
noncomputable def g_n_2exbidv (ph : Wff) (ps : Wff) (ch : Wff) (x : Var) (y : Var)
    (dv_ph_x : x ∉ ph.fv) (dv_ph_y : y ∉ ph.fv)
    (hyp_n_2albidv_1 : Nominal.NPrf (.imp ph (syn_wb ps ch))) :
    Nominal.NPrf
      (.imp ph (syn_wb (syn_wex x (syn_wex y ps)) (syn_wex x (syn_wex y ch)))) :=
  by
  let proofSupport : Finset Var :=
    ph.fv ∪ ps.fv ∪ ch.fv ∪ ({ x } : Finset Var) ∪ ({ y } : Finset Var)
  have p0000 :=
    @g_exbidv ph ps ch y
      (by
        first
        | (aesop))
      hyp_n_2albidv_1
  have p0001 :=
    @g_exbidv ph (syn_wex y ps) (syn_wex y ch) x
      (by
        first
        | (aesop))
      p0000
  exact p0001

@[expose]
noncomputable def g_n_3exbidv (ph : Wff) (ps : Wff) (ch : Wff) (x : Var) (y : Var)
    (z : Var) (dv_ph_x : x ∉ ph.fv) (dv_ph_y : y ∉ ph.fv) (dv_ph_z : z ∉ ph.fv)
    (hyp_n_3exbidv_1 : Nominal.NPrf (.imp ph (syn_wb ps ch))) :
    Nominal.NPrf
      (.imp ph (syn_wb (syn_wex x (syn_wex y (syn_wex z ps)))
          (syn_wex x (syn_wex y (syn_wex z ch))))) :=
  by
  let proofSupport : Finset Var :=
    ph.fv ∪ ps.fv ∪ ch.fv ∪ ({ x } : Finset Var) ∪ ({ y } : Finset Var) ∪
      ({ z } : Finset Var)
  have p0000 :=
    @g_exbidv ph ps ch z
      (by
        first
        | (aesop))
      hyp_n_3exbidv_1
  have p0001 :=
    @g_n_2exbidv ph (syn_wex z ps) (syn_wex z ch) x y
      (by
        first
        | (aesop))
      (by
        first
        | (aesop))
      p0000
  exact p0001

@[expose]
noncomputable def g_alrimiv (ph : Wff) (ps : Wff) (x : Var) (dv_ph_x : x ∉ ph.fv)
    (hyp_alrimiv_1 : Nominal.NPrf (.imp ph ps)) : Nominal.NPrf (.imp ph (.all x ps)) :=
  by
  let proofSupport : Finset Var := ph.fv ∪ ps.fv ∪ ({ x } : Finset Var)
  have p0000 :=
    Nominal.ax17 ph x
      (by
        first
        | (aesop))
  have p0001 := @g_alrimih ph ps x p0000 hyp_alrimiv_1
  exact p0001

@[expose]
noncomputable def g_alrimivv (ph : Wff) (ps : Wff) (x : Var) (y : Var)
    (dv_ph_x : x ∉ ph.fv) (dv_ph_y : y ∉ ph.fv)
    (hyp_alrimivv_1 : Nominal.NPrf (.imp ph ps)) :
    Nominal.NPrf (.imp ph (.all x (.all y ps))) :=
  by
  let proofSupport : Finset Var :=
    ph.fv ∪ ps.fv ∪ ({ x } : Finset Var) ∪ ({ y } : Finset Var)
  have p0000 :=
    @g_alrimiv ph ps y
      (by
        first
        | (aesop))
      hyp_alrimivv_1
  have p0001 :=
    @g_alrimiv ph (.all y ps) x
      (by
        first
        | (aesop))
      p0000
  exact p0001

@[expose]
noncomputable def g_alrimdv (ph : Wff) (ps : Wff) (ch : Wff) (x : Var)
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
  have p0002 := @g_alrimdh ph ps ch x p0000 p0001 hyp_alrimdv_1
  exact p0002

@[expose]
noncomputable def g_exlimiv (ph : Wff) (ps : Wff) (x : Var) (dv_ps_x : x ∉ ps.fv)
    (hyp_exlimiv_1 : Nominal.NPrf (.imp ph ps)) : Nominal.NPrf (.imp (syn_wex x ph) ps) :=
  by
  let proofSupport : Finset Var := ph.fv ∪ ps.fv ∪ ({ x } : Finset Var)
  have p0000 := @g_eximi ph ps x hyp_exlimiv_1
  have p0001 :=
    @g_ax17e ps x
      (by
        first
        | (aesop))
  have p0002 := @g_syl (syn_wex x ph) (syn_wex x ps) ps p0000 p0001
  exact p0002

@[expose]
noncomputable def g_exlimivv (ph : Wff) (ps : Wff) (x : Var) (y : Var)
    (dv_ps_x : x ∉ ps.fv) (dv_ps_y : y ∉ ps.fv)
    (hyp_exlimivv_1 : Nominal.NPrf (.imp ph ps)) :
    Nominal.NPrf (.imp (syn_wex x (syn_wex y ph)) ps) :=
  by
  let proofSupport : Finset Var :=
    ph.fv ∪ ps.fv ∪ ({ x } : Finset Var) ∪ ({ y } : Finset Var)
  have p0000 :=
    @g_exlimiv ph ps y
      (by
        first
        | (aesop))
      hyp_exlimivv_1
  have p0001 :=
    @g_exlimiv (syn_wex y ph) ps x
      (by
        first
        | (aesop))
      p0000
  exact p0001

@[expose]
noncomputable def g_exlimdv (ph : Wff) (ps : Wff) (ch : Wff) (x : Var)
    (dv_ch_x : x ∉ ch.fv) (dv_ph_x : x ∉ ph.fv)
    (hyp_exlimdv_1 : Nominal.NPrf (.imp ph (.imp ps ch))) :
    Nominal.NPrf (.imp ph (.imp (syn_wex x ps) ch)) :=
  by
  let proofSupport : Finset Var := ph.fv ∪ ps.fv ∪ ch.fv ∪ ({ x } : Finset Var)
  have p0000 :=
    @g_eximdv ph ps ch x
      (by
        first
        | (aesop))
      hyp_exlimdv_1
  have p0001 :=
    @g_ax17e ch x
      (by
        first
        | (aesop))
  have p0002 := @g_syl6 ph (syn_wex x ps) (syn_wex x ch) ch p0000 p0001
  exact p0002

@[expose]
noncomputable def g_exlimdvv (ph : Wff) (ps : Wff) (ch : Wff) (x : Var) (y : Var)
    (dv_ch_x : x ∉ ch.fv) (dv_ch_y : y ∉ ch.fv) (dv_ph_x : x ∉ ph.fv)
    (dv_ph_y : y ∉ ph.fv) (hyp_exlimdvv_1 : Nominal.NPrf (.imp ph (.imp ps ch))) :
    Nominal.NPrf (.imp ph (.imp (syn_wex x (syn_wex y ps)) ch)) :=
  by
  let proofSupport : Finset Var :=
    ph.fv ∪ ps.fv ∪ ch.fv ∪ ({ x } : Finset Var) ∪ ({ y } : Finset Var)
  have p0000 :=
    @g_exlimdv ph ps ch y
      (by
        first
        | (aesop))
      (by
        first
        | (aesop))
      hyp_exlimdvv_1
  have p0001 :=
    @g_exlimdv ph (syn_wex y ps) ch x
      (by
        first
        | (aesop))
      (by
        first
        | (aesop))
      p0000
  exact p0001

@[expose]
noncomputable def g_exlimddv (ph : Wff) (ps : Wff) (ch : Wff) (x : Var)
    (dv_ch_x : x ∉ ch.fv) (dv_ph_x : x ∉ ph.fv)
    (hyp_exlimddv_1 : Nominal.NPrf (.imp ph (syn_wex x ps)))
    (hyp_exlimddv_2 : Nominal.NPrf (.imp (syn_wa ph ps) ch)) :
    Nominal.NPrf (.imp ph ch) :=
  by
  let proofSupport : Finset Var := ph.fv ∪ ps.fv ∪ ch.fv ∪ ({ x } : Finset Var)
  have p0000 := @g_ex ph ps ch hyp_exlimddv_2
  have p0001 :=
    @g_exlimdv ph ps ch x
      (by
        first
        | (aesop))
      (by
        first
        | (aesop))
      p0000
  have p0002 := @g_mpd ph (syn_wex x ps) ch hyp_exlimddv_1 p0001
  exact p0002

@[expose]
noncomputable def g_equs3 (ph : Wff) (x : Var) (y : Var) :
    Nominal.NPrf
      (syn_wb (syn_wex x (syn_wa (.objEq x y) ph))
        (.neg (.all x (.imp (.objEq x y) (.neg ph))))) :=
  by
  have p0000 := @g_alinexa (.objEq x y) ph x
  have p0001 :=
    @g_con2bii (.all x (.imp (.objEq x y) (.neg ph))) (syn_wex x (syn_wa (.objEq x y) ph))
      p0000
  exact p0001

@[expose]
noncomputable def g_speimfw (ph : Wff) (ps : Wff) (x : Var) (y : Var)
    (hyp_speimfw_2 : Nominal.NPrf (.imp (.objEq x y) (.imp ph ps))) :
    Nominal.NPrf
      (.imp (.neg (.all x (.neg (.objEq x y)))) (.imp (.all x ph) (syn_wex x ps))) :=
  by
  have p0000 := @g_eximi (.objEq x y) (.imp ph ps) x hyp_speimfw_2
  have p0001 := (Nominal.biimpRefl (syn_wex x (.objEq x y)))
  have p0002 := @g_n_19_35 ph ps x
  have p0003 :=
    @g_n_3imtr3i (syn_wex x (.objEq x y)) (syn_wex x (.imp ph ps))
      (.neg (.all x (.neg (.objEq x y)))) (.imp (.all x ph) (syn_wex x ps)) p0000 p0001
      p0002
  exact p0003

@[expose]
noncomputable def g_spimfw (ph : Wff) (ps : Wff) (x : Var) (y : Var)
    (hyp_spimfw_1 : Nominal.NPrf (.imp (.neg ps) (.all x (.neg ps))))
    (hyp_spimfw_2 : Nominal.NPrf (.imp (.objEq x y) (.imp ph ps))) :
    Nominal.NPrf (.imp (.neg (.all x (.neg (.objEq x y)))) (.imp (.all x ph) ps)) :=
  by
  have p0000 := @g_speimfw ph ps x y hyp_spimfw_2
  have p0001 := (Nominal.biimpRefl (syn_wex x ps))
  have p0002 := @g_con1i ps (.all x (.neg ps)) hyp_spimfw_1
  have p0003 := @g_sylbi (syn_wex x ps) (.neg (.all x (.neg ps))) ps p0001 p0002
  have p0004 :=
    @g_syl6 (.neg (.all x (.neg (.objEq x y)))) (.all x ph) (syn_wex x ps) ps p0000 p0003
  exact p0004

@[expose]
noncomputable def g_sbequ2 (ph : Wff) (x : Var) (y : Var) :
    Nominal.NPrf (.imp (.objEq x y) (.imp (syn_wsb y x ph) ph)) :=
  by
  have p0000 := (Nominal.biimpRefl (syn_wsb y x ph))
  have p0001 := @g_simpl (.imp (.objEq x y) ph) (syn_wex x (syn_wa (.objEq x y) ph))
  have p0002 :=
    @g_com12 (syn_wa (.imp (.objEq x y) ph) (syn_wex x (syn_wa (.objEq x y) ph)))
      (.objEq x y) ph p0001
  have p0003 :=
    @g_syl5bi (syn_wsb y x ph)
      (syn_wa (.imp (.objEq x y) ph) (syn_wex x (syn_wa (.objEq x y) ph))) (.objEq x y) ph
      p0000 p0002
  exact p0003

@[expose]
noncomputable def g_sb1 (ph : Wff) (x : Var) (y : Var) :
    Nominal.NPrf (.imp (syn_wsb y x ph) (syn_wex x (syn_wa (.objEq x y) ph))) :=
  by
  have p0000 := (Nominal.biimpRefl (syn_wsb y x ph))
  have p0001 :=
    @g_simprbi (syn_wsb y x ph) (.imp (.objEq x y) ph)
      (syn_wex x (syn_wa (.objEq x y) ph)) p0000
  exact p0001

@[expose]
noncomputable def g_sbimi (ph : Wff) (ps : Wff) (x : Var) (y : Var)
    (hyp_sbimi_1 : Nominal.NPrf (.imp ph ps)) :
    Nominal.NPrf (.imp (syn_wsb y x ph) (syn_wsb y x ps)) :=
  by
  have p0000 := @g_imim2i ph ps (.objEq x y) hyp_sbimi_1
  have p0001 := @g_anim2i ph ps (.objEq x y) hyp_sbimi_1
  have p0002 := @g_eximi (syn_wa (.objEq x y) ph) (syn_wa (.objEq x y) ps) x p0001
  have p0003 :=
    @g_anim12i (.imp (.objEq x y) ph) (.imp (.objEq x y) ps)
      (syn_wex x (syn_wa (.objEq x y) ph)) (syn_wex x (syn_wa (.objEq x y) ps)) p0000
      p0002
  have p0004 := (Nominal.biimpRefl (syn_wsb y x ph))
  have p0005 := (Nominal.biimpRefl (syn_wsb y x ps))
  have p0006 :=
    @g_n_3imtr4i (syn_wa (.imp (.objEq x y) ph) (syn_wex x (syn_wa (.objEq x y) ph)))
      (syn_wa (.imp (.objEq x y) ps) (syn_wex x (syn_wa (.objEq x y) ps)))
      (syn_wsb y x ph) (syn_wsb y x ps) p0003 p0004 p0005
  exact p0006

@[expose]
noncomputable def g_sbbii (ph : Wff) (ps : Wff) (x : Var) (y : Var)
    (hyp_sbbii_1 : Nominal.NPrf (syn_wb ph ps)) :
    Nominal.NPrf (syn_wb (syn_wsb y x ph) (syn_wsb y x ps)) :=
  by
  have p0000 := @g_biimpi ph ps hyp_sbbii_1
  have p0001 := @g_sbimi ph ps x y p0000
  have p0002 := @g_biimpri ph ps hyp_sbbii_1
  have p0003 := @g_sbimi ps ph x y p0002
  have p0004 := @g_impbii (syn_wsb y x ph) (syn_wsb y x ps) p0001 p0003
  exact p0004

@[expose]
noncomputable def g_ax9v (x : Var) (y : Var) (_dv_x_y : x ≠ y) :
    Nominal.NPrf (.neg (.all x (.neg (.objEq x y)))) :=
  by
  have p0000 := Nominal.ax9 x y
  exact p0000

@[expose]
noncomputable def g_a9ev (x : Var) (y : Var) (dv_x_y : x ≠ y) :
    Nominal.NPrf (syn_wex x (.objEq x y)) :=
  by
  let proofSupport : Finset Var := ({ x } : Finset Var) ∪ ({ y } : Finset Var)
  have p0000 :=
    @g_ax9v x y
      (by
        first
        | (aesop))
  have p0001 := (Nominal.biimpRefl (syn_wex x (.objEq x y)))
  have p0002 :=
    @g_mpbir (syn_wex x (.objEq x y)) (.neg (.all x (.neg (.objEq x y)))) p0000 p0001
  exact p0002

@[expose]
noncomputable def g_spimeh (ph : Wff) (ps : Wff) (x : Var) (z : Var) (dv_x_z : x ≠ z)
    (hyp_spimeh_1 : Nominal.NPrf (.imp ph (.all x ph)))
    (hyp_spimeh_2 : Nominal.NPrf (.imp (.objEq x z) (.imp ph ps))) :
    Nominal.NPrf (.imp ph (syn_wex x ps)) :=
  by
  let proofSupport : Finset Var :=
    ph.fv ∪ ps.fv ∪ ({ x } : Finset Var) ∪ ({ z } : Finset Var)
  have p0000 :=
    @g_a9ev x z
      (by
        first
        | (aesop))
  have p0001 := @g_eximi (.objEq x z) (.imp ph ps) x hyp_spimeh_2
  have p0002 := Nominal.mp p0000 p0001
  have p0003 := @g_n_19_35i ph ps x p0002
  have p0004 := @g_syl ph (.all x ph) (syn_wex x ps) hyp_spimeh_1 p0003
  exact p0004

@[expose]
noncomputable def g_spimw (ph : Wff) (ps : Wff) (x : Var) (y : Var) (dv_x_y : x ≠ y)
    (hyp_spimw_1 : Nominal.NPrf (.imp (.neg ps) (.all x (.neg ps))))
    (hyp_spimw_2 : Nominal.NPrf (.imp (.objEq x y) (.imp ph ps))) :
    Nominal.NPrf (.imp (.all x ph) ps) :=
  by
  let proofSupport : Finset Var :=
    ph.fv ∪ ps.fv ∪ ({ x } : Finset Var) ∪ ({ y } : Finset Var)
  have p0000 :=
    @g_ax9v x y
      (by
        first
        | (aesop))
  have p0001 := @g_spimfw ph ps x y hyp_spimw_1 hyp_spimw_2
  have p0002 := Nominal.mp p0000 p0001
  exact p0002

@[expose]
noncomputable def g_spimvw (ph : Wff) (ps : Wff) (x : Var) (y : Var) (dv_ps_x : x ∉ ps.fv)
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
    @g_spimw ph ps x y
      (by
        first
        | (aesop))
      p0000 hyp_spimvw_1
  exact p0001

@[expose]
noncomputable def g_cbvalivw (ph : Wff) (ps : Wff) (x : Var) (y : Var)
    (dv_ph_y : y ∉ ph.fv) (dv_ps_x : x ∉ ps.fv) (dv_x_y : x ≠ y)
    (hyp_cbvalivw_1 : Nominal.NPrf (.imp (.objEq x y) (.imp ph ps))) :
    Nominal.NPrf (.imp (.all x ph) (.all y ps)) :=
  by
  let proofSupport : Finset Var :=
    ph.fv ∪ ps.fv ∪ ({ x } : Finset Var) ∪ ({ y } : Finset Var)
  have p0000 :=
    @g_spimvw ph ps x y
      (by
        first
        | (aesop))
      (by
        first
        | (aesop))
      hyp_cbvalivw_1
  have p0001 :=
    @g_alrimiv (.all x ph) ps y
      (by
        first
        |
          (simp (config :=
              { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_wff_all,
              Finset.mem_erase] at ⊢;
            aesop))
      p0000
  exact p0001

@[expose]
noncomputable def g_equid (x : Var) : Nominal.NPrf (.objEq x x) :=
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
    @g_a9ev y x
      (by
        first
        | (aesop))
  have p0001 := Nominal.ax8 y x x
  have p0002 := @g_pm2_43i (.objEq y x) (.objEq x x) p0001
  have p0003 := @g_eximi (.objEq y x) (.objEq x x) y p0002
  have p0004 :=
    @g_ax17e (.objEq x x) y
      (by
        first
        |
          (simp (config :=
              {
                failIfUnchanged :=
                  false }) only [NFChoice.Compiler.CoreFVSimp.fv_wff_objEq] at ⊢;
            aesop))
  have p0005 :=
    @g_mp2b (syn_wex y (.objEq y x)) (syn_wex y (.objEq x x)) (.objEq x x) p0000 p0003
      p0004
  exact p0005

@[expose]
noncomputable def g_equcomi (x : Var) (y : Var) :
    Nominal.NPrf (.imp (.objEq x y) (.objEq y x)) :=
  by
  have p0000 := @g_equid x
  have p0001 := Nominal.ax8 x y x
  have p0002 := @g_mpi (.objEq x y) (.objEq x x) (.objEq y x) p0000 p0001
  exact p0002

@[expose]
noncomputable def g_equcom (x : Var) (y : Var) :
    Nominal.NPrf (syn_wb (.objEq x y) (.objEq y x)) :=
  by
  have p0000 := @g_equcomi x y
  have p0001 := @g_equcomi y x
  have p0002 := @g_impbii (.objEq x y) (.objEq y x) p0000 p0001
  exact p0002

@[expose]
noncomputable def g_equcoms (ph : Wff) (x : Var) (y : Var)
    (hyp_equcoms_1 : Nominal.NPrf (.imp (.objEq x y) ph)) :
    Nominal.NPrf (.imp (.objEq y x) ph) :=
  by
  have p0000 := @g_equcomi y x
  have p0001 := @g_syl (.objEq y x) (.objEq x y) ph p0000 hyp_equcoms_1
  exact p0001

@[expose]
noncomputable def g_equtr (x : Var) (y : Var) (z : Var) :
    Nominal.NPrf (.imp (.objEq x y) (.imp (.objEq y z) (.objEq x z))) :=
  by
  have p0000 := Nominal.ax8 y x z
  have p0001 := @g_equcoms (.imp (.objEq y z) (.objEq x z)) y x p0000
  exact p0001

@[expose]
noncomputable def g_equtrr (x : Var) (y : Var) (z : Var) :
    Nominal.NPrf (.imp (.objEq x y) (.imp (.objEq z x) (.objEq z y))) :=
  by
  have p0000 := @g_equtr z x y
  have p0001 := @g_com12 (.objEq z x) (.objEq x y) (.objEq z y) p0000
  exact p0001

@[expose]
noncomputable def g_equequ1 (x : Var) (y : Var) (z : Var) :
    Nominal.NPrf (.imp (.objEq x y) (syn_wb (.objEq x z) (.objEq y z))) :=
  by
  have p0000 := Nominal.ax8 x y z
  have p0001 := @g_equtr x y z
  have p0002 := @g_impbid (.objEq x y) (.objEq x z) (.objEq y z) p0000 p0001
  exact p0002

@[expose]
noncomputable def g_equequ2 (x : Var) (y : Var) (z : Var) :
    Nominal.NPrf (.imp (.objEq x y) (syn_wb (.objEq z x) (.objEq z y))) :=
  by
  have p0000 := @g_equequ1 x y z
  have p0001 := @g_equcom x z
  have p0002 := @g_equcom y z
  have p0003 :=
    @g_n_3bitr3g (.objEq x y) (.objEq x z) (.objEq y z) (.objEq z x) (.objEq z y) p0000
      p0001 p0002
  exact p0003

@[expose]
noncomputable def g_stdpc6 (x : Var) : Nominal.NPrf (.all x (.objEq x x)) :=
  by
  have p0000 := @g_equid x
  have p0001 := Nominal.gen p0000 x
  exact p0001

@[expose]
noncomputable def g_equtr2 (x : Var) (y : Var) (z : Var) :
    Nominal.NPrf (.imp (syn_wa (.objEq x z) (.objEq y z)) (.objEq x y)) :=
  by
  have p0000 := @g_equtrr z y x
  have p0001 := @g_equcoms (.imp (.objEq x z) (.objEq x y)) z y p0000
  have p0002 := @g_impcom (.objEq y z) (.objEq x z) (.objEq x y) p0001
  exact p0002

@[expose]
noncomputable def g_elequ1 (x : Var) (y : Var) (z : Var) :
    Nominal.NPrf (.imp (.objEq x y) (syn_wb (.objMem x z) (.objMem y z))) :=
  by
  have p0000 := Nominal.ax13 x y z
  have p0001 := Nominal.ax13 y x z
  have p0002 := @g_equcoms (.imp (.objMem y z) (.objMem x z)) y x p0001
  have p0003 := @g_impbid (.objEq x y) (.objMem x z) (.objMem y z) p0000 p0002
  exact p0003

@[expose]
noncomputable def g_elequ2 (x : Var) (y : Var) (z : Var) :
    Nominal.NPrf (.imp (.objEq x y) (syn_wb (.objMem z x) (.objMem z y))) :=
  by
  have p0000 := Nominal.ax14 x y z
  have p0001 := Nominal.ax14 y x z
  have p0002 := @g_equcoms (.imp (.objMem z y) (.objMem z x)) y x p0001
  have p0003 := @g_impbid (.objEq x y) (.objMem z x) (.objMem z y) p0000 p0002
  exact p0003

@[expose]
noncomputable def g_hbn1 (ph : Wff) (x : Var) :
    Nominal.NPrf (.imp (.neg (.all x ph)) (.all x (.neg (.all x ph)))) :=
  by
  have p0000 := Nominal.ax6 x ph
  exact p0000

@[expose]
noncomputable def g_hbe1 (ph : Wff) (x : Var) :
    Nominal.NPrf (.imp (syn_wex x ph) (.all x (syn_wex x ph))) :=
  by
  have p0000 := (Nominal.biimpRefl (syn_wex x ph))
  have p0001 := @g_hbn1 (.neg ph) x
  have p0002 := @g_hbxfrbi (syn_wex x ph) (.neg (.all x (.neg ph))) x p0000 p0001
  exact p0002

@[expose]
noncomputable def g_nfe1 (ph : Wff) (x : Var) : Nominal.NPrf (syn_wnf x (syn_wex x ph)) :=
  by
  have p0000 := @g_hbe1 ph x
  have p0001 := @g_nfi (syn_wex x ph) x p0000
  exact p0001

@[expose]
noncomputable def g_a7s (ph : Wff) (ps : Wff) (x : Var) (y : Var)
    (hyp_a7s_1 : Nominal.NPrf (.imp (.all x (.all y ph)) ps)) :
    Nominal.NPrf (.imp (.all y (.all x ph)) ps) :=
  by
  have p0000 := Nominal.ax7Structural y x ph
  have p0001 := @g_syl (.all y (.all x ph)) (.all x (.all y ph)) ps p0000 hyp_a7s_1
  exact p0001

@[expose]
noncomputable def g_hbal (ph : Wff) (x : Var) (y : Var)
    (hyp_hbal_1 : Nominal.NPrf (.imp ph (.all x ph))) :
    Nominal.NPrf (.imp (.all y ph) (.all x (.all y ph))) :=
  by
  have p0000 := @g_alimi ph (.all x ph) y hyp_hbal_1
  have p0001 := Nominal.ax7Structural y x ph
  have p0002 := @g_syl (.all y ph) (.all y (.all x ph)) (.all x (.all y ph)) p0000 p0001
  exact p0002

@[expose]
noncomputable def g_alcom (ph : Wff) (x : Var) (y : Var) :
    Nominal.NPrf (syn_wb (.all x (.all y ph)) (.all y (.all x ph))) :=
  by
  have p0000 := Nominal.ax7Structural x y ph
  have p0001 := Nominal.ax7Structural y x ph
  have p0002 := @g_impbii (.all x (.all y ph)) (.all y (.all x ph)) p0000 p0001
  exact p0002

@[expose]
noncomputable def g_alrot3 (ph : Wff) (x : Var) (y : Var) (z : Var) :
    Nominal.NPrf (syn_wb (.all x (.all y (.all z ph))) (.all y (.all z (.all x ph)))) :=
  by
  have p0000 := @g_alcom (.all z ph) x y
  have p0001 := @g_alcom ph x z
  have p0002 := @g_albii (.all x (.all z ph)) (.all z (.all x ph)) y p0001
  have p0003 :=
    @g_bitri (.all x (.all y (.all z ph))) (.all y (.all x (.all z ph)))
      (.all y (.all z (.all x ph))) p0000 p0002
  exact p0003

@[expose]
noncomputable def g_hbald (ph : Wff) (ps : Wff) (x : Var) (y : Var)
    (hyp_hbald_1 : Nominal.NPrf (.imp ph (.all y ph)))
    (hyp_hbald_2 : Nominal.NPrf (.imp ph (.imp ps (.all x ps)))) :
    Nominal.NPrf (.imp ph (.imp (.all y ps) (.all x (.all y ps)))) :=
  by
  have p0000 := @g_alimdh ph ps (.all x ps) y hyp_hbald_1 hyp_hbald_2
  have p0001 := Nominal.ax7Structural y x ps
  have p0002 :=
    @g_syl6 ph (.all y ps) (.all y (.all x ps)) (.all x (.all y ps)) p0000 p0001
  exact p0002

@[expose]
noncomputable def g_excom (ph : Wff) (x : Var) (y : Var) :
    Nominal.NPrf (syn_wb (syn_wex x (syn_wex y ph)) (syn_wex y (syn_wex x ph))) :=
  by
  have p0000 := @g_alcom (.neg ph) x y
  have p0001 := @g_notbii (.all x (.all y (.neg ph))) (.all y (.all x (.neg ph))) p0000
  have p0002 := @g_exnal (.all y (.neg ph)) x
  have p0003 := @g_exnal (.all x (.neg ph)) y
  have p0004 :=
    @g_n_3bitr4i (.neg (.all x (.all y (.neg ph)))) (.neg (.all y (.all x (.neg ph))))
      (syn_wex x (.neg (.all y (.neg ph)))) (syn_wex y (.neg (.all x (.neg ph)))) p0001
      p0002 p0003
  have p0005 := (Nominal.biimpRefl (syn_wex y ph))
  have p0006 := @g_exbii (syn_wex y ph) (.neg (.all y (.neg ph))) x p0005
  have p0007 := (Nominal.biimpRefl (syn_wex x ph))
  have p0008 := @g_exbii (syn_wex x ph) (.neg (.all x (.neg ph))) y p0007
  have p0009 :=
    @g_n_3bitr4i (syn_wex x (.neg (.all y (.neg ph))))
      (syn_wex y (.neg (.all x (.neg ph)))) (syn_wex x (syn_wex y ph))
      (syn_wex y (syn_wex x ph)) p0004 p0006 p0008
  exact p0009

@[expose]
noncomputable def g_excom13 (ph : Wff) (x : Var) (y : Var) (z : Var) :
    Nominal.NPrf
      (syn_wb (syn_wex x (syn_wex y (syn_wex z ph))) (syn_wex z (syn_wex y (syn_wex x ph)))) :=
  by
  have p0000 := @g_excom (syn_wex z ph) x y
  have p0001 := @g_excom ph x z
  have p0002 := @g_exbii (syn_wex x (syn_wex z ph)) (syn_wex z (syn_wex x ph)) y p0001
  have p0003 := @g_excom (syn_wex x ph) y z
  have p0004 :=
    @g_n_3bitri (syn_wex x (syn_wex y (syn_wex z ph)))
      (syn_wex y (syn_wex x (syn_wex z ph))) (syn_wex y (syn_wex z (syn_wex x ph)))
      (syn_wex z (syn_wex y (syn_wex x ph))) p0000 p0002 p0003
  exact p0004

@[expose]
noncomputable def g_exrot3 (ph : Wff) (x : Var) (y : Var) (z : Var) :
    Nominal.NPrf
      (syn_wb (syn_wex x (syn_wex y (syn_wex z ph))) (syn_wex y (syn_wex z (syn_wex x ph)))) :=
  by
  have p0000 := @g_excom13 ph x y z
  have p0001 := @g_excom (syn_wex x ph) z y
  have p0002 :=
    @g_bitri (syn_wex x (syn_wex y (syn_wex z ph))) (syn_wex z (syn_wex y (syn_wex x ph)))
      (syn_wex y (syn_wex z (syn_wex x ph))) p0000 p0001
  exact p0002

@[expose]
noncomputable def g_exrot4 (ph : Wff) (x : Var) (y : Var) (z : Var) (w : Var) :
    Nominal.NPrf
      (syn_wb (syn_wex x (syn_wex y (syn_wex z (syn_wex w ph))))
        (syn_wex z (syn_wex w (syn_wex x (syn_wex y ph))))) :=
  by
  have p0000 := @g_excom13 ph y z w
  have p0001 :=
    @g_exbii (syn_wex y (syn_wex z (syn_wex w ph))) (syn_wex w (syn_wex z (syn_wex y ph)))
      x p0000
  have p0002 := @g_excom13 (syn_wex y ph) x w z
  have p0003 :=
    @g_bitri (syn_wex x (syn_wex y (syn_wex z (syn_wex w ph))))
      (syn_wex x (syn_wex w (syn_wex z (syn_wex y ph))))
      (syn_wex z (syn_wex w (syn_wex x (syn_wex y ph)))) p0001 p0002
  exact p0003

@[expose]
noncomputable def g_sp (ph : Wff) (x : Var) : Nominal.NPrf (.imp (.all x ph) ph) :=
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
    @g_a9ev w x
      (by
        first
        | (aesop))
  have p0001 := @g_equcomi w x
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
    @g_syl2im (.objEq w x) (.objEq x w) (.neg ph) (.all w (.neg ph))
      (.all x (.imp (.objEq x w) (.neg ph))) p0001 p0002 p0003
  have p0005 :=
    @g_ax9v x w
      (by
        first
        | (aesop))
  have p0006 := @g_con2 (.objEq x w) ph
  have p0007 := @g_al2imi (.imp (.objEq x w) (.neg ph)) ph (.neg (.objEq x w)) x p0006
  have p0008 :=
    @g_mtoi (.all x (.imp (.objEq x w) (.neg ph))) (.all x ph)
      (.all x (.neg (.objEq x w))) p0005 p0007
  have p0009 :=
    @g_syl6 (.objEq w x) (.neg ph) (.all x (.imp (.objEq x w) (.neg ph)))
      (.neg (.all x ph)) p0004 p0008
  have p0010 := @g_con4d (.objEq w x) ph (.all x ph) p0009
  have p0011 :=
    @g_exlimiv (.objEq w x) (.imp (.all x ph) ph) w
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

@[expose]
noncomputable def g_ax6o (ph : Wff) (x : Var) :
    Nominal.NPrf (.imp (.neg (.all x (.neg (.all x ph)))) ph) :=
  by
  have p0000 := @g_sp ph x
  have p0001 := Nominal.ax6 x ph
  have p0002 := @g_nsyl4 (.all x ph) ph (.all x (.neg (.all x ph))) p0000 p0001
  exact p0002

@[expose]
noncomputable def g_sps (ph : Wff) (ps : Wff) (x : Var)
    (hyp_sps_1 : Nominal.NPrf (.imp ph ps)) : Nominal.NPrf (.imp (.all x ph) ps) :=
  by
  have p0000 := @g_sp ph x
  have p0001 := @g_syl (.all x ph) ph ps p0000 hyp_sps_1
  exact p0001

@[expose]
noncomputable def g_spsd (ph : Wff) (ps : Wff) (ch : Wff) (x : Var)
    (hyp_spsd_1 : Nominal.NPrf (.imp ph (.imp ps ch))) :
    Nominal.NPrf (.imp ph (.imp (.all x ps) ch)) :=
  by
  have p0000 := @g_sp ps x
  have p0001 := @g_syl5 (.all x ps) ps ph ch p0000 hyp_spsd_1
  exact p0001

@[expose]
noncomputable def g_n_19_8a (ph : Wff) (x : Var) :
    Nominal.NPrf (.imp ph (syn_wex x ph)) :=
  by
  have p0000 := @g_sp (.neg ph) x
  have p0001 := @g_con2i (.all x (.neg ph)) ph p0000
  have p0002 := (Nominal.biimpRefl (syn_wex x ph))
  have p0003 := @g_sylibr ph (.neg (.all x (.neg ph))) (syn_wex x ph) p0001 p0002
  exact p0003

@[expose]
noncomputable def g_n_19_21bi (ph : Wff) (ps : Wff) (x : Var)
    (hyp_n_19_21bi_1 : Nominal.NPrf (.imp ph (.all x ps))) : Nominal.NPrf (.imp ph ps) :=
  by
  have p0000 := @g_sp ps x
  have p0001 := @g_syl ph (.all x ps) ps hyp_n_19_21bi_1 p0000
  exact p0001

@[expose]
noncomputable def g_nfr (ph : Wff) (x : Var) :
    Nominal.NPrf (.imp (syn_wnf x ph) (.imp ph (.all x ph))) :=
  by
  have p0000 := (Nominal.biimpRefl (syn_wnf x ph))
  have p0001 := @g_sp (.imp ph (.all x ph)) x
  have p0002 :=
    @g_sylbi (syn_wnf x ph) (.all x (.imp ph (.all x ph))) (.imp ph (.all x ph)) p0000
      p0001
  exact p0002

@[expose]
noncomputable def g_nfri (ph : Wff) (x : Var) (hyp_nfri_1 : Nominal.NPrf (syn_wnf x ph)) :
    Nominal.NPrf (.imp ph (.all x ph)) :=
  by
  have p0000 := @g_nfr ph x
  have p0001 := Nominal.mp hyp_nfri_1 p0000
  exact p0001

@[expose]
noncomputable def g_nfrd (ph : Wff) (ps : Wff) (x : Var)
    (hyp_nfrd_1 : Nominal.NPrf (.imp ph (syn_wnf x ps))) :
    Nominal.NPrf (.imp ph (.imp ps (.all x ps))) :=
  by
  have p0000 := @g_nfr ps x
  have p0001 := @g_syl ph (syn_wnf x ps) (.imp ps (.all x ps)) hyp_nfrd_1 p0000
  exact p0001

@[expose]
noncomputable def g_alimd (ph : Wff) (ps : Wff) (ch : Wff) (x : Var)
    (hyp_alimd_1 : Nominal.NPrf (syn_wnf x ph))
    (hyp_alimd_2 : Nominal.NPrf (.imp ph (.imp ps ch))) :
    Nominal.NPrf (.imp ph (.imp (.all x ps) (.all x ch))) :=
  by
  have p0000 := @g_nfri ph x hyp_alimd_1
  have p0001 := @g_alimdh ph ps ch x p0000 hyp_alimd_2
  exact p0001

@[expose]
noncomputable def g_alrimi (ph : Wff) (ps : Wff) (x : Var)
    (hyp_alrimi_1 : Nominal.NPrf (syn_wnf x ph))
    (hyp_alrimi_2 : Nominal.NPrf (.imp ph ps)) : Nominal.NPrf (.imp ph (.all x ps)) :=
  by
  have p0000 := @g_nfri ph x hyp_alrimi_1
  have p0001 := @g_alrimih ph ps x p0000 hyp_alrimi_2
  exact p0001

@[expose]
noncomputable def g_nfd (ph : Wff) (ps : Wff) (x : Var)
    (hyp_nfd_1 : Nominal.NPrf (syn_wnf x ph))
    (hyp_nfd_2 : Nominal.NPrf (.imp ph (.imp ps (.all x ps)))) :
    Nominal.NPrf (.imp ph (syn_wnf x ps)) :=
  by
  have p0000 := @g_alrimi ph (.imp ps (.all x ps)) x hyp_nfd_1 hyp_nfd_2
  have p0001 := (Nominal.biimpRefl (syn_wnf x ps))
  have p0002 := @g_sylibr ph (.all x (.imp ps (.all x ps))) (syn_wnf x ps) p0000 p0001
  exact p0002

@[expose]
noncomputable def g_nfdh (ph : Wff) (ps : Wff) (x : Var)
    (hyp_nfdh_1 : Nominal.NPrf (.imp ph (.all x ph)))
    (hyp_nfdh_2 : Nominal.NPrf (.imp ph (.imp ps (.all x ps)))) :
    Nominal.NPrf (.imp ph (syn_wnf x ps)) :=
  by
  have p0000 := @g_nfi ph x hyp_nfdh_1
  have p0001 := @g_nfd ph ps x p0000 hyp_nfdh_2
  exact p0001

@[expose]
noncomputable def g_alrimdd (ph : Wff) (ps : Wff) (ch : Wff) (x : Var)
    (hyp_alrimdd_1 : Nominal.NPrf (syn_wnf x ph))
    (hyp_alrimdd_2 : Nominal.NPrf (.imp ph (syn_wnf x ps)))
    (hyp_alrimdd_3 : Nominal.NPrf (.imp ph (.imp ps ch))) :
    Nominal.NPrf (.imp ph (.imp ps (.all x ch))) :=
  by
  have p0000 := @g_nfrd ph ps x hyp_alrimdd_2
  have p0001 := @g_alimd ph ps ch x hyp_alrimdd_1 hyp_alrimdd_3
  have p0002 := @g_syld ph ps (.all x ps) (.all x ch) p0000 p0001
  exact p0002

@[expose]
noncomputable def g_alrimd (ph : Wff) (ps : Wff) (ch : Wff) (x : Var)
    (hyp_alrimd_1 : Nominal.NPrf (syn_wnf x ph))
    (hyp_alrimd_2 : Nominal.NPrf (syn_wnf x ps))
    (hyp_alrimd_3 : Nominal.NPrf (.imp ph (.imp ps ch))) :
    Nominal.NPrf (.imp ph (.imp ps (.all x ch))) :=
  by
  have p0000 := @g_a1i (syn_wnf x ps) ph hyp_alrimd_2
  have p0001 := @g_alrimdd ph ps ch x hyp_alrimd_1 p0000 hyp_alrimd_3
  exact p0001

@[expose]
noncomputable def g_eximd (ph : Wff) (ps : Wff) (ch : Wff) (x : Var)
    (hyp_eximd_1 : Nominal.NPrf (syn_wnf x ph))
    (hyp_eximd_2 : Nominal.NPrf (.imp ph (.imp ps ch))) :
    Nominal.NPrf (.imp ph (.imp (syn_wex x ps) (syn_wex x ch))) :=
  by
  have p0000 := @g_nfri ph x hyp_eximd_1
  have p0001 := @g_eximdh ph ps ch x p0000 hyp_eximd_2
  exact p0001

@[expose]
noncomputable def g_nexd (ph : Wff) (ps : Wff) (x : Var)
    (hyp_nexd_1 : Nominal.NPrf (syn_wnf x ph))
    (hyp_nexd_2 : Nominal.NPrf (.imp ph (.neg ps))) :
    Nominal.NPrf (.imp ph (.neg (syn_wex x ps))) :=
  by
  have p0000 := @g_nfri ph x hyp_nexd_1
  have p0001 := @g_nexdh ph ps x p0000 hyp_nexd_2
  exact p0001

@[expose]
noncomputable def g_albid (ph : Wff) (ps : Wff) (ch : Wff) (x : Var)
    (hyp_albid_1 : Nominal.NPrf (syn_wnf x ph))
    (hyp_albid_2 : Nominal.NPrf (.imp ph (syn_wb ps ch))) :
    Nominal.NPrf (.imp ph (syn_wb (.all x ps) (.all x ch))) :=
  by
  have p0000 := @g_nfri ph x hyp_albid_1
  have p0001 := @g_albidh ph ps ch x p0000 hyp_albid_2
  exact p0001

@[expose]
noncomputable def g_exbid (ph : Wff) (ps : Wff) (ch : Wff) (x : Var)
    (hyp_exbid_1 : Nominal.NPrf (syn_wnf x ph))
    (hyp_exbid_2 : Nominal.NPrf (.imp ph (syn_wb ps ch))) :
    Nominal.NPrf (.imp ph (syn_wb (syn_wex x ps) (syn_wex x ch))) :=
  by
  have p0000 := @g_nfri ph x hyp_exbid_1
  have p0001 := @g_exbidh ph ps ch x p0000 hyp_exbid_2
  exact p0001

@[expose]
noncomputable def g_nfbidf (ph : Wff) (ps : Wff) (ch : Wff) (x : Var)
    (hyp_nfbidf_1 : Nominal.NPrf (syn_wnf x ph))
    (hyp_nfbidf_2 : Nominal.NPrf (.imp ph (syn_wb ps ch))) :
    Nominal.NPrf (.imp ph (syn_wb (syn_wnf x ps) (syn_wnf x ch))) :=
  by
  have p0000 := @g_albid ph ps ch x hyp_nfbidf_1 hyp_nfbidf_2
  have p0001 := @g_imbi12d ph ps ch (.all x ps) (.all x ch) hyp_nfbidf_2 p0000
  have p0002 :=
    @g_albid ph (.imp ps (.all x ps)) (.imp ch (.all x ch)) x hyp_nfbidf_1 p0001
  have p0003 := (Nominal.biimpRefl (syn_wnf x ps))
  have p0004 := (Nominal.biimpRefl (syn_wnf x ch))
  have p0005 :=
    @g_n_3bitr4g ph (.all x (.imp ps (.all x ps))) (.all x (.imp ch (.all x ch)))
      (syn_wnf x ps) (syn_wnf x ch) p0002 p0003 p0004
  exact p0005

@[expose]
noncomputable def g_hbnt (ph : Wff) (x : Var) :
    Nominal.NPrf
      (.imp (.all x (.imp ph (.all x ph))) (.imp (.neg ph) (.all x (.neg ph)))) :=
  by
  have p0000 := @g_ax6o ph x
  have p0001 := @g_con1i (.all x (.neg (.all x ph))) ph p0000
  have p0002 := @g_con3 ph (.all x ph)
  have p0003 := @g_al2imi (.imp ph (.all x ph)) (.neg (.all x ph)) (.neg ph) x p0002
  have p0004 :=
    @g_syl5 (.neg ph) (.all x (.neg (.all x ph))) (.all x (.imp ph (.all x ph)))
      (.all x (.neg ph)) p0001 p0003
  exact p0004

@[expose]
noncomputable def g_hbn (ph : Wff) (x : Var)
    (hyp_hbn_1 : Nominal.NPrf (.imp ph (.all x ph))) :
    Nominal.NPrf (.imp (.neg ph) (.all x (.neg ph))) :=
  by
  have p0000 := @g_hbnt ph x
  have p0001 :=
    @g_mpg (.imp ph (.all x ph)) (.imp (.neg ph) (.all x (.neg ph))) x p0000 hyp_hbn_1
  exact p0001

@[expose]
noncomputable def g_n_19_9ht (ph : Wff) (x : Var) :
    Nominal.NPrf (.imp (.all x (.imp ph (.all x ph))) (.imp (syn_wex x ph) ph)) :=
  by
  have p0000 := (Nominal.biimpRefl (syn_wex x ph))
  have p0001 := @g_hbnt ph x
  have p0002 := @g_con1d (.all x (.imp ph (.all x ph))) ph (.all x (.neg ph)) p0001
  have p0003 :=
    @g_syl5bi (syn_wex x ph) (.neg (.all x (.neg ph))) (.all x (.imp ph (.all x ph))) ph
      p0000 p0002
  exact p0003

@[expose]
noncomputable def g_n_19_9t (ph : Wff) (x : Var) :
    Nominal.NPrf (.imp (syn_wnf x ph) (syn_wb (syn_wex x ph) ph)) :=
  by
  have p0000 := (Nominal.biimpRefl (syn_wnf x ph))
  have p0001 := @g_n_19_9ht ph x
  have p0002 :=
    @g_sylbi (syn_wnf x ph) (.all x (.imp ph (.all x ph))) (.imp (syn_wex x ph) ph) p0000
      p0001
  have p0003 := @g_n_19_8a ph x
  have p0004 := @g_impbid1 (syn_wnf x ph) (syn_wex x ph) ph p0002 p0003
  exact p0004

@[expose]
noncomputable def g_n_19_9h (ph : Wff) (x : Var)
    (hyp_n_19_9h_1 : Nominal.NPrf (.imp ph (.all x ph))) :
    Nominal.NPrf (syn_wb (syn_wex x ph) ph) :=
  by
  have p0000 := @g_nfi ph x hyp_n_19_9h_1
  have p0001 := @g_n_19_9t ph x
  have p0002 := Nominal.mp p0000 p0001
  exact p0002

@[expose]
noncomputable def g_n_19_9d (ph : Wff) (ps : Wff) (x : Var)
    (hyp_n_19_9d_1 : Nominal.NPrf (.imp ps (syn_wnf x ph))) :
    Nominal.NPrf (.imp ps (.imp (syn_wex x ph) ph)) :=
  by
  have p0000 := @g_n_19_9t ph x
  have p0001 := @g_syl ps (syn_wnf x ph) (syn_wb (syn_wex x ph) ph) hyp_n_19_9d_1 p0000
  have p0002 := @g_biimpd ps (syn_wex x ph) ph p0001
  exact p0002

@[expose]
noncomputable def g_n_19_9 (ph : Wff) (x : Var)
    (hyp_n_19_9_1 : Nominal.NPrf (syn_wnf x ph)) :
    Nominal.NPrf (syn_wb (syn_wex x ph) ph) :=
  by
  have p0000 := @g_nfri ph x hyp_n_19_9_1
  have p0001 := @g_n_19_9h ph x p0000
  exact p0001

@[expose]
noncomputable def g_n_19_3 (ph : Wff) (x : Var)
    (hyp_n_19_3_1 : Nominal.NPrf (syn_wnf x ph)) : Nominal.NPrf (syn_wb (.all x ph) ph) :=
  by
  have p0000 := @g_sp ph x
  have p0001 := @g_nfri ph x hyp_n_19_3_1
  have p0002 := @g_impbii (.all x ph) ph p0000 p0001
  exact p0002

@[expose]
noncomputable def g_hba1 (ph : Wff) (x : Var) :
    Nominal.NPrf (.imp (.all x ph) (.all x (.all x ph))) :=
  by
  have p0000 := @g_hbe1 (.neg ph) x
  have p0001 := @g_hbn (syn_wex x (.neg ph)) x p0000
  have p0002 := @g_alex ph x
  have p0003 := @g_albii (.all x ph) (.neg (syn_wex x (.neg ph))) x p0002
  have p0004 :=
    @g_n_3imtr4i (.neg (syn_wex x (.neg ph))) (.all x (.neg (syn_wex x (.neg ph))))
      (.all x ph) (.all x (.all x ph)) p0001 p0002 p0003
  exact p0004

@[expose]
noncomputable def g_nfa1 (ph : Wff) (x : Var) : Nominal.NPrf (syn_wnf x (.all x ph)) :=
  by
  have p0000 := @g_hba1 ph x
  have p0001 := @g_nfi (.all x ph) x p0000
  exact p0001

@[expose]
noncomputable def g_a5i (ph : Wff) (ps : Wff) (x : Var)
    (hyp_a5i_1 : Nominal.NPrf (.imp (.all x ph) ps)) :
    Nominal.NPrf (.imp (.all x ph) (.all x ps)) :=
  by
  have p0000 := @g_nfa1 ph x
  have p0001 := @g_alrimi (.all x ph) ps x p0000 hyp_a5i_1
  exact p0001

@[expose]
noncomputable def g_nfnf1 (ph : Wff) (x : Var) :
    Nominal.NPrf (syn_wnf x (syn_wnf x ph)) :=
  by
  have p0000 := (Nominal.biimpRefl (syn_wnf x ph))
  have p0001 := @g_nfa1 (.imp ph (.all x ph)) x
  have p0002 := @g_nfxfr (syn_wnf x ph) (.all x (.imp ph (.all x ph))) x p0000 p0001
  exact p0002

@[expose]
noncomputable def g_nfnd (ph : Wff) (ps : Wff) (x : Var)
    (hyp_nfnd_1 : Nominal.NPrf (.imp ph (syn_wnf x ps))) :
    Nominal.NPrf (.imp ph (syn_wnf x (.neg ps))) :=
  by
  have p0000 := @g_nfnf1 ps x
  have p0001 := (Nominal.biimpRefl (syn_wnf x ps))
  have p0002 := @g_hbnt ps x
  have p0003 :=
    @g_sylbi (syn_wnf x ps) (.all x (.imp ps (.all x ps)))
      (.imp (.neg ps) (.all x (.neg ps))) p0001 p0002
  have p0004 := @g_nfd (syn_wnf x ps) (.neg ps) x p0000 p0003
  have p0005 := @g_syl ph (syn_wnf x ps) (syn_wnf x (.neg ps)) hyp_nfnd_1 p0004
  exact p0005

@[expose]
noncomputable def g_nfn (ph : Wff) (x : Var) (hyp_nfn_1 : Nominal.NPrf (syn_wnf x ph)) :
    Nominal.NPrf (syn_wnf x (.neg ph)) :=
  by
  have p0000 := @g_a1i (syn_wnf x ph) syn_wtru hyp_nfn_1
  have p0001 := @g_nfnd syn_wtru ph x p0000
  have p0002 := @g_trud (syn_wnf x (.neg ph)) p0001
  exact p0002

@[expose]
noncomputable def g_n_19_38 (ph : Wff) (ps : Wff) (x : Var) :
    Nominal.NPrf (.imp (.imp (syn_wex x ph) (.all x ps)) (.all x (.imp ph ps))) :=
  by
  have p0000 := @g_alnex ph x
  have p0001 := @g_pm2_21 ph ps
  have p0002 := @g_alimi (.neg ph) (.imp ph ps) x p0001
  have p0003 :=
    @g_sylbir (.neg (syn_wex x ph)) (.all x (.neg ph)) (.all x (.imp ph ps)) p0000 p0002
  have p0004 := Nominal.ax1 ps ph
  have p0005 := @g_alimi ps (.imp ph ps) x p0004
  have p0006 := @g_ja (syn_wex x ph) (.all x ps) (.all x (.imp ph ps)) p0003 p0005
  exact p0006

@[expose]
noncomputable def g_n_19_21t (ph : Wff) (ps : Wff) (x : Var) :
    Nominal.NPrf
      (.imp (syn_wnf x ph) (syn_wb (.all x (.imp ph ps)) (.imp ph (.all x ps)))) :=
  by
  have p0000 := @g_nfr ph x
  have p0001 := Nominal.ax5 x ph ps
  have p0002 :=
    @g_syl9 (syn_wnf x ph) ph (.all x ph) (.all x (.imp ph ps)) (.all x ps) p0000 p0001
  have p0003 := @g_n_19_9t ph x
  have p0004 := @g_imbi1d (syn_wnf x ph) (syn_wex x ph) ph (.all x ps) p0003
  have p0005 := @g_n_19_38 ph ps x
  have p0006 :=
    @g_syl6bir (syn_wnf x ph) (.imp ph (.all x ps)) (.imp (syn_wex x ph) (.all x ps))
      (.all x (.imp ph ps)) p0004 p0005
  have p0007 :=
    @g_impbid (syn_wnf x ph) (.all x (.imp ph ps)) (.imp ph (.all x ps)) p0002 p0006
  exact p0007

@[expose]
noncomputable def g_n_19_21 (ph : Wff) (ps : Wff) (x : Var)
    (hyp_n_19_21_1 : Nominal.NPrf (syn_wnf x ph)) :
    Nominal.NPrf (syn_wb (.all x (.imp ph ps)) (.imp ph (.all x ps))) :=
  by
  have p0000 := @g_n_19_21t ph ps x
  have p0001 := Nominal.mp hyp_n_19_21_1 p0000
  exact p0001

@[expose]
noncomputable def g_n_19_21h (ph : Wff) (ps : Wff) (x : Var)
    (hyp_n_19_21h_1 : Nominal.NPrf (.imp ph (.all x ph))) :
    Nominal.NPrf (syn_wb (.all x (.imp ph ps)) (.imp ph (.all x ps))) :=
  by
  have p0000 := @g_nfi ph x hyp_n_19_21h_1
  have p0001 := @g_n_19_21 ph ps x p0000
  exact p0001

@[expose]
noncomputable def g_n_19_23t (ph : Wff) (ps : Wff) (x : Var) :
    Nominal.NPrf
      (.imp (syn_wnf x ps) (syn_wb (.all x (.imp ph ps)) (.imp (syn_wex x ph) ps))) :=
  by
  have p0000 := @g_exim ph ps x
  have p0001 := @g_n_19_9t ps x
  have p0002 := @g_biimpd (syn_wnf x ps) (syn_wex x ps) ps p0001
  have p0003 :=
    @g_syl9r (.all x (.imp ph ps)) (syn_wex x ph) (syn_wex x ps) (syn_wnf x ps) ps p0000
      p0002
  have p0004 := @g_nfr ps x
  have p0005 := @g_imim2d (syn_wnf x ps) ps (.all x ps) (syn_wex x ph) p0004
  have p0006 := @g_n_19_38 ph ps x
  have p0007 :=
    @g_syl6 (syn_wnf x ps) (.imp (syn_wex x ph) ps) (.imp (syn_wex x ph) (.all x ps))
      (.all x (.imp ph ps)) p0005 p0006
  have p0008 :=
    @g_impbid (syn_wnf x ps) (.all x (.imp ph ps)) (.imp (syn_wex x ph) ps) p0003 p0007
  exact p0008

@[expose]
noncomputable def g_n_19_23 (ph : Wff) (ps : Wff) (x : Var)
    (hyp_n_19_23_1 : Nominal.NPrf (syn_wnf x ps)) :
    Nominal.NPrf (syn_wb (.all x (.imp ph ps)) (.imp (syn_wex x ph) ps)) :=
  by
  have p0000 := @g_n_19_23t ph ps x
  have p0001 := Nominal.mp hyp_n_19_23_1 p0000
  exact p0001

@[expose]
noncomputable def g_n_19_23h (ph : Wff) (ps : Wff) (x : Var)
    (hyp_n_19_23h_1 : Nominal.NPrf (.imp ps (.all x ps))) :
    Nominal.NPrf (syn_wb (.all x (.imp ph ps)) (.imp (syn_wex x ph) ps)) :=
  by
  have p0000 := @g_nfi ps x hyp_n_19_23h_1
  have p0001 := @g_n_19_23 ph ps x p0000
  exact p0001

@[expose]
noncomputable def g_exlimi (ph : Wff) (ps : Wff) (x : Var)
    (hyp_exlimi_1 : Nominal.NPrf (syn_wnf x ps))
    (hyp_exlimi_2 : Nominal.NPrf (.imp ph ps)) : Nominal.NPrf (.imp (syn_wex x ph) ps) :=
  by
  have p0000 := @g_n_19_23 ph ps x hyp_exlimi_1
  have p0001 := @g_mpgbi (.imp ph ps) (.imp (syn_wex x ph) ps) x p0000 hyp_exlimi_2
  exact p0001

@[expose]
noncomputable def g_exlimih (ph : Wff) (ps : Wff) (x : Var)
    (hyp_exlimih_1 : Nominal.NPrf (.imp ps (.all x ps)))
    (hyp_exlimih_2 : Nominal.NPrf (.imp ph ps)) : Nominal.NPrf (.imp (syn_wex x ph) ps) :=
  by
  have p0000 := @g_nfi ps x hyp_exlimih_1
  have p0001 := @g_exlimi ph ps x p0000 hyp_exlimih_2
  exact p0001

@[expose]
noncomputable def g_exlimd (ph : Wff) (ps : Wff) (ch : Wff) (x : Var)
    (hyp_exlimd_1 : Nominal.NPrf (syn_wnf x ph))
    (hyp_exlimd_2 : Nominal.NPrf (syn_wnf x ch))
    (hyp_exlimd_3 : Nominal.NPrf (.imp ph (.imp ps ch))) :
    Nominal.NPrf (.imp ph (.imp (syn_wex x ps) ch)) :=
  by
  have p0000 := @g_alrimi ph (.imp ps ch) x hyp_exlimd_1 hyp_exlimd_3
  have p0001 := @g_n_19_23 ps ch x hyp_exlimd_2
  have p0002 := @g_sylib ph (.all x (.imp ps ch)) (.imp (syn_wex x ps) ch) p0000 p0001
  exact p0002

@[expose]
noncomputable def g_nfimd (ph : Wff) (ps : Wff) (ch : Wff) (x : Var)
    (hyp_nfimd_1 : Nominal.NPrf (.imp ph (syn_wnf x ps)))
    (hyp_nfimd_2 : Nominal.NPrf (.imp ph (syn_wnf x ch))) :
    Nominal.NPrf (.imp ph (syn_wnf x (.imp ps ch))) :=
  by
  have p0000 := @g_nfnf1 ps x
  have p0001 := @g_nfnf1 ch x
  have p0002 := @g_nfr ch x
  have p0003 := @g_imim2d (syn_wnf x ch) ch (.all x ch) ps p0002
  have p0004 := @g_n_19_21t ps ch x
  have p0005 :=
    @g_biimprd (syn_wnf x ps) (.all x (.imp ps ch)) (.imp ps (.all x ch)) p0004
  have p0006 :=
    @g_syl9r (syn_wnf x ch) (.imp ps ch) (.imp ps (.all x ch)) (syn_wnf x ps)
      (.all x (.imp ps ch)) p0003 p0005
  have p0007 :=
    @g_alrimd (syn_wnf x ps) (syn_wnf x ch) (.imp (.imp ps ch) (.all x (.imp ps ch))) x
      p0000 p0001 p0006
  have p0008 := (Nominal.biimpRefl (syn_wnf x (.imp ps ch)))
  have p0009 :=
    @g_syl6ibr (syn_wnf x ps) (syn_wnf x ch)
      (.all x (.imp (.imp ps ch) (.all x (.imp ps ch)))) (syn_wnf x (.imp ps ch)) p0007
      p0008
  have p0010 :=
    @g_sylc ph (syn_wnf x ps) (syn_wnf x ch) (syn_wnf x (.imp ps ch)) hyp_nfimd_1
      hyp_nfimd_2 p0009
  exact p0010

@[expose]
noncomputable def g_hbim1 (ph : Wff) (ps : Wff) (x : Var)
    (hyp_hbim1_1 : Nominal.NPrf (.imp ph (.all x ph)))
    (hyp_hbim1_2 : Nominal.NPrf (.imp ph (.imp ps (.all x ps)))) :
    Nominal.NPrf (.imp (.imp ph ps) (.all x (.imp ph ps))) :=
  by
  have p0000 := @g_a2i ph ps (.all x ps) hyp_hbim1_2
  have p0001 := @g_n_19_21h ph ps x hyp_hbim1_1
  have p0002 :=
    @g_sylibr (.imp ph ps) (.imp ph (.all x ps)) (.all x (.imp ph ps)) p0000 p0001
  exact p0002

@[expose]
noncomputable def g_nfim1 (ph : Wff) (ps : Wff) (x : Var)
    (hyp_nfim1_1 : Nominal.NPrf (syn_wnf x ph))
    (hyp_nfim1_2 : Nominal.NPrf (.imp ph (syn_wnf x ps))) :
    Nominal.NPrf (syn_wnf x (.imp ph ps)) :=
  by
  have p0000 := @g_nfri ph x hyp_nfim1_1
  have p0001 := @g_nfrd ph ps x hyp_nfim1_2
  have p0002 := @g_hbim1 ph ps x p0000 p0001
  have p0003 := @g_nfi (.imp ph ps) x p0002
  exact p0003

@[expose]
noncomputable def g_nfim (ph : Wff) (ps : Wff) (x : Var)
    (hyp_nfim_1 : Nominal.NPrf (syn_wnf x ph))
    (hyp_nfim_2 : Nominal.NPrf (syn_wnf x ps)) : Nominal.NPrf (syn_wnf x (.imp ph ps)) :=
  by
  have p0000 := @g_a1i (syn_wnf x ps) ph hyp_nfim_2
  have p0001 := @g_nfim1 ph ps x hyp_nfim_1 p0000
  exact p0001

@[expose]
noncomputable def g_hbimd (ph : Wff) (ps : Wff) (ch : Wff) (x : Var)
    (hyp_hbimd_1 : Nominal.NPrf (.imp ph (.all x ph)))
    (hyp_hbimd_2 : Nominal.NPrf (.imp ph (.imp ps (.all x ps))))
    (hyp_hbimd_3 : Nominal.NPrf (.imp ph (.imp ch (.all x ch)))) :
    Nominal.NPrf (.imp ph (.imp (.imp ps ch) (.all x (.imp ps ch)))) :=
  by
  have p0000 := @g_nfdh ph ps x hyp_hbimd_1 hyp_hbimd_2
  have p0001 := @g_nfdh ph ch x hyp_hbimd_1 hyp_hbimd_3
  have p0002 := @g_nfimd ph ps ch x p0000 p0001
  have p0003 := @g_nfrd ph (.imp ps ch) x p0002
  exact p0003

@[expose]
noncomputable def g_hbim (ph : Wff) (ps : Wff) (x : Var)
    (hyp_hbim_1 : Nominal.NPrf (.imp ph (.all x ph)))
    (hyp_hbim_2 : Nominal.NPrf (.imp ps (.all x ps))) :
    Nominal.NPrf (.imp (.imp ph ps) (.all x (.imp ph ps))) :=
  by
  have p0000 := @g_a1i (.imp ps (.all x ps)) ph hyp_hbim_2
  have p0001 := @g_hbim1 ph ps x hyp_hbim_1 p0000
  exact p0001

@[expose]
noncomputable def g_nfand (ph : Wff) (ps : Wff) (ch : Wff) (x : Var)
    (hyp_nfand_1 : Nominal.NPrf (.imp ph (syn_wnf x ps)))
    (hyp_nfand_2 : Nominal.NPrf (.imp ph (syn_wnf x ch))) :
    Nominal.NPrf (.imp ph (syn_wnf x (syn_wa ps ch))) :=
  by
  have p0000 := (Nominal.biimpRefl (syn_wa ps ch))
  have p0001 := @g_nfnd ph ch x hyp_nfand_2
  have p0002 := @g_nfimd ph ps (.neg ch) x hyp_nfand_1 p0001
  have p0003 := @g_nfnd ph (.imp ps (.neg ch)) x p0002
  have p0004 := @g_nfxfrd (syn_wa ps ch) (.neg (.imp ps (.neg ch))) ph x p0000 p0003
  exact p0004

@[expose]
noncomputable def g_nfan (ph : Wff) (ps : Wff) (x : Var)
    (hyp_nfan_1 : Nominal.NPrf (syn_wnf x ph))
    (hyp_nfan_2 : Nominal.NPrf (syn_wnf x ps)) :
    Nominal.NPrf (syn_wnf x (syn_wa ph ps)) :=
  by
  have p0000 := @g_a1i (syn_wnf x ph) syn_wtru hyp_nfan_1
  have p0001 := @g_a1i (syn_wnf x ps) syn_wtru hyp_nfan_2
  have p0002 := @g_nfand syn_wtru ph ps x p0000 p0001
  have p0003 := @g_trud (syn_wnf x (syn_wa ph ps)) p0002
  exact p0003

@[expose]
noncomputable def g_nfnan (ph : Wff) (ps : Wff) (x : Var)
    (hyp_nfan_1 : Nominal.NPrf (syn_wnf x ph))
    (hyp_nfan_2 : Nominal.NPrf (syn_wnf x ps)) :
    Nominal.NPrf (syn_wnf x (syn_wnan ph ps)) :=
  by
  have p0000 := (Nominal.biimpRefl (syn_wnan ph ps))
  have p0001 := @g_nfan ph ps x hyp_nfan_1 hyp_nfan_2
  have p0002 := @g_nfn (syn_wa ph ps) x p0001
  have p0003 := @g_nfxfr (syn_wnan ph ps) (.neg (syn_wa ph ps)) x p0000 p0002
  exact p0003

@[expose]
noncomputable def g_hban (ph : Wff) (ps : Wff) (x : Var)
    (hyp_hb_1 : Nominal.NPrf (.imp ph (.all x ph)))
    (hyp_hb_2 : Nominal.NPrf (.imp ps (.all x ps))) :
    Nominal.NPrf (.imp (syn_wa ph ps) (.all x (syn_wa ph ps))) :=
  by
  have p0000 := @g_nfi ph x hyp_hb_1
  have p0001 := @g_nfi ps x hyp_hb_2
  have p0002 := @g_nfan ph ps x p0000 p0001
  have p0003 := @g_nfri (syn_wa ph ps) x p0002
  exact p0003

@[expose]
noncomputable def g_nfbid (ph : Wff) (ps : Wff) (ch : Wff) (x : Var)
    (hyp_nfbid_1 : Nominal.NPrf (.imp ph (syn_wnf x ps)))
    (hyp_nfbid_2 : Nominal.NPrf (.imp ph (syn_wnf x ch))) :
    Nominal.NPrf (.imp ph (syn_wnf x (syn_wb ps ch))) :=
  by
  have p0000 := @g_dfbi2 ps ch
  have p0001 := @g_nfimd ph ps ch x hyp_nfbid_1 hyp_nfbid_2
  have p0002 := @g_nfimd ph ch ps x hyp_nfbid_2 hyp_nfbid_1
  have p0003 := @g_nfand ph (.imp ps ch) (.imp ch ps) x p0001 p0002
  have p0004 :=
    @g_nfxfrd (syn_wb ps ch) (syn_wa (.imp ps ch) (.imp ch ps)) ph x p0000 p0003
  exact p0004

@[expose]
noncomputable def g_nfbi (ph : Wff) (ps : Wff) (x : Var)
    (hyp_nf_1 : Nominal.NPrf (syn_wnf x ph)) (hyp_nf_2 : Nominal.NPrf (syn_wnf x ps)) :
    Nominal.NPrf (syn_wnf x (syn_wb ph ps)) :=
  by
  have p0000 := @g_a1i (syn_wnf x ph) syn_wtru hyp_nf_1
  have p0001 := @g_a1i (syn_wnf x ps) syn_wtru hyp_nf_2
  have p0002 := @g_nfbid syn_wtru ph ps x p0000 p0001
  have p0003 := @g_trud (syn_wnf x (syn_wb ph ps)) p0002
  exact p0003

@[expose]
noncomputable def g_equsalhw (ph : Wff) (ps : Wff) (x : Var) (y : Var) (dv_x_y : x ≠ y)
    (hyp_equsalhw_1 : Nominal.NPrf (.imp ps (.all x ps)))
    (hyp_equsalhw_2 : Nominal.NPrf (.imp (.objEq x y) (syn_wb ph ps))) :
    Nominal.NPrf (syn_wb (.all x (.imp (.objEq x y) ph)) ps) :=
  by
  let proofSupport : Finset Var :=
    ph.fv ∪ ps.fv ∪ ({ x } : Finset Var) ∪ ({ y } : Finset Var)
  have p0000 := @g_n_19_23h (.objEq x y) ps x hyp_equsalhw_1
  have p0001 := @g_pm5_74i (.objEq x y) ph ps hyp_equsalhw_2
  have p0002 := @g_albii (.imp (.objEq x y) ph) (.imp (.objEq x y) ps) x p0001
  have p0003 :=
    @g_a9ev x y
      (by
        first
        | (aesop))
  have p0004 := @g_a1bi (syn_wex x (.objEq x y)) ps p0003
  have p0005 :=
    @g_n_3bitr4i (.all x (.imp (.objEq x y) ps)) (.imp (syn_wex x (.objEq x y)) ps)
      (.all x (.imp (.objEq x y) ph)) ps p0000 p0002 p0004
  exact p0005

@[expose]
noncomputable def g_hbex (ph : Wff) (x : Var) (y : Var)
    (hyp_hbex_1 : Nominal.NPrf (.imp ph (.all x ph))) :
    Nominal.NPrf (.imp (syn_wex y ph) (.all x (syn_wex y ph))) :=
  by
  have p0000 := (Nominal.biimpRefl (syn_wex y ph))
  have p0001 := @g_hbn ph x hyp_hbex_1
  have p0002 := @g_hbal (.neg ph) x y p0001
  have p0003 := @g_hbn (.all y (.neg ph)) x p0002
  have p0004 := @g_hbxfrbi (syn_wex y ph) (.neg (.all y (.neg ph))) x p0000 p0003
  exact p0004

@[expose]
noncomputable def g_nfal (ph : Wff) (x : Var) (y : Var)
    (hyp_nfal_1 : Nominal.NPrf (syn_wnf x ph)) : Nominal.NPrf (syn_wnf x (.all y ph)) :=
  by
  have p0000 := @g_nfri ph x hyp_nfal_1
  have p0001 := @g_hbal ph x y p0000
  have p0002 := @g_nfi (.all y ph) x p0001
  exact p0002

@[expose]
noncomputable def g_nfex (ph : Wff) (x : Var) (y : Var)
    (hyp_nfal_1 : Nominal.NPrf (syn_wnf x ph)) :
    Nominal.NPrf (syn_wnf x (syn_wex y ph)) :=
  by
  have p0000 := @g_nfri ph x hyp_nfal_1
  have p0001 := @g_hbex ph x y p0000
  have p0002 := @g_nfi (syn_wex y ph) x p0001
  exact p0002

@[expose]
noncomputable def g_n_19_12 (ph : Wff) (x : Var) (y : Var) :
    Nominal.NPrf (.imp (syn_wex x (.all y ph)) (.all y (syn_wex x ph))) :=
  by
  have p0000 := @g_nfa1 ph y
  have p0001 := @g_nfex (.all y ph) y x p0000
  have p0002 := @g_sp ph y
  have p0003 := @g_eximi (.all y ph) ph x p0002
  have p0004 := @g_alrimi (syn_wex x (.all y ph)) (syn_wex x ph) y p0001 p0003
  exact p0004

@[expose]
noncomputable def g_dvelimhw (ph : Wff) (ps : Wff) (x : Var) (y : Var) (z : Var)
    (_dv_x_z : x ≠ z) (dv_y_z : y ≠ z)
    (hyp_dvelimhw_1 : Nominal.NPrf (.imp ph (.all x ph)))
    (hyp_dvelimhw_2 : Nominal.NPrf (.imp ps (.all z ps)))
    (hyp_dvelimhw_3 : Nominal.NPrf (.imp (.objEq z y) (syn_wb ph ps)))
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
  have p0001 := @g_hbn1 (.objEq x y) x
  have p0002 := @g_equcomi z y
  have p0003 := @g_equcomi y z
  have p0004 := @g_alimi (.objEq y z) (.objEq z y) x p0003
  have p0005 :=
    @g_syl56 (.objEq z y) (.objEq y z) (.neg (.all x (.objEq x y))) (.all x (.objEq y z))
      (.all x (.objEq z y)) p0002 hyp_dvelimhw_4 p0004
  have p0006 := @g_a1i (.imp ph (.all x ph)) (.neg (.all x (.objEq x y))) hyp_dvelimhw_1
  have p0007 := @g_hbimd (.neg (.all x (.objEq x y))) (.objEq z y) ph x p0001 p0005 p0006
  have p0008 :=
    @g_hbald (.neg (.all x (.objEq x y))) (.imp (.objEq z y) ph) x z p0000 p0007
  have p0009 :=
    @g_equsalhw ph ps z y
      (by
        first
        | (aesop))
      hyp_dvelimhw_2 hyp_dvelimhw_3
  have p0010 := @g_albii (.all z (.imp (.objEq z y) ph)) ps x p0009
  have p0011 :=
    @g_n_3imtr3g (.neg (.all x (.objEq x y))) (.all z (.imp (.objEq z y) ph))
      (.all x (.all z (.imp (.objEq z y) ph))) ps (.all x ps) p0008 p0009 p0010
  exact p0011

@[expose]
noncomputable def g_nfald (ph : Wff) (ps : Wff) (x : Var) (y : Var)
    (hyp_nfald_1 : Nominal.NPrf (syn_wnf y ph))
    (hyp_nfald_2 : Nominal.NPrf (.imp ph (syn_wnf x ps))) :
    Nominal.NPrf (.imp ph (syn_wnf x (.all y ps))) :=
  by
  have p0000 := @g_alrimi ph (syn_wnf x ps) y hyp_nfald_1 hyp_nfald_2
  have p0001 := @g_nfnf1 ps x
  have p0002 := @g_nfal (syn_wnf x ps) x y p0001
  have p0003 := @g_hba1 (syn_wnf x ps) y
  have p0004 := @g_sp (syn_wnf x ps) y
  have p0005 := @g_nfrd (.all y (syn_wnf x ps)) ps x p0004
  have p0006 := @g_hbald (.all y (syn_wnf x ps)) ps x y p0003 p0005
  have p0007 := @g_nfd (.all y (syn_wnf x ps)) (.all y ps) x p0002 p0006
  have p0008 := @g_syl ph (.all y (syn_wnf x ps)) (syn_wnf x (.all y ps)) p0000 p0007
  exact p0008

@[expose]
noncomputable def g_nfexd (ph : Wff) (ps : Wff) (x : Var) (y : Var)
    (hyp_nfald_1 : Nominal.NPrf (syn_wnf y ph))
    (hyp_nfald_2 : Nominal.NPrf (.imp ph (syn_wnf x ps))) :
    Nominal.NPrf (.imp ph (syn_wnf x (syn_wex y ps))) :=
  by
  have p0000 := (Nominal.biimpRefl (syn_wex y ps))
  have p0001 := @g_nfnd ph ps x hyp_nfald_2
  have p0002 := @g_nfald ph (.neg ps) x y hyp_nfald_1 p0001
  have p0003 := @g_nfnd ph (.all y (.neg ps)) x p0002
  have p0004 := @g_nfxfrd (syn_wex y ps) (.neg (.all y (.neg ps))) ph x p0000 p0003
  exact p0004

@[expose]
noncomputable def g_nfa2 (ph : Wff) (x : Var) (y : Var) :
    Nominal.NPrf (syn_wnf x (.all y (.all x ph))) :=
  by
  have p0000 := @g_nfa1 ph x
  have p0001 := @g_nfal (.all x ph) x y p0000
  exact p0001

@[expose]
noncomputable def g_n_19_21bbi (ph : Wff) (ps : Wff) (x : Var) (y : Var)
    (hyp_n_19_21bbi_1 : Nominal.NPrf (.imp ph (.all x (.all y ps)))) :
    Nominal.NPrf (.imp ph ps) :=
  by
  have p0000 := @g_n_19_21bi ph (.all y ps) x hyp_n_19_21bbi_1
  have p0001 := @g_n_19_21bi ph ps y p0000
  exact p0001

@[expose]
noncomputable def g_n_19_27 (ph : Wff) (ps : Wff) (x : Var)
    (hyp_n_19_27_1 : Nominal.NPrf (syn_wnf x ps)) :
    Nominal.NPrf (syn_wb (.all x (syn_wa ph ps)) (syn_wa (.all x ph) ps)) :=
  by
  have p0000 := @g_n_19_26 ph ps x
  have p0001 := @g_n_19_3 ps x hyp_n_19_27_1
  have p0002 := @g_anbi2i (.all x ps) ps (.all x ph) p0001
  have p0003 :=
    @g_bitri (.all x (syn_wa ph ps)) (syn_wa (.all x ph) (.all x ps))
      (syn_wa (.all x ph) ps) p0000 p0002
  exact p0003

@[expose]
noncomputable def g_n_19_28 (ph : Wff) (ps : Wff) (x : Var)
    (hyp_n_19_28_1 : Nominal.NPrf (syn_wnf x ph)) :
    Nominal.NPrf (syn_wb (.all x (syn_wa ph ps)) (syn_wa ph (.all x ps))) :=
  by
  have p0000 := @g_n_19_26 ph ps x
  have p0001 := @g_n_19_3 ph x hyp_n_19_28_1
  have p0002 := @g_anbi1i (.all x ph) ph (.all x ps) p0001
  have p0003 :=
    @g_bitri (.all x (syn_wa ph ps)) (syn_wa (.all x ph) (.all x ps))
      (syn_wa ph (.all x ps)) p0000 p0002
  exact p0003

@[expose]
noncomputable def g_n_19_36 (ph : Wff) (ps : Wff) (x : Var)
    (hyp_n_19_36_1 : Nominal.NPrf (syn_wnf x ps)) :
    Nominal.NPrf (syn_wb (syn_wex x (.imp ph ps)) (.imp (.all x ph) ps)) :=
  by
  have p0000 := @g_n_19_35 ph ps x
  have p0001 := @g_n_19_9 ps x hyp_n_19_36_1
  have p0002 := @g_imbi2i (syn_wex x ps) ps (.all x ph) p0001
  have p0003 :=
    @g_bitri (syn_wex x (.imp ph ps)) (.imp (.all x ph) (syn_wex x ps))
      (.imp (.all x ph) ps) p0000 p0002
  exact p0003

@[expose]
noncomputable def g_n_19_36i (ph : Wff) (ps : Wff) (x : Var)
    (hyp_n_19_36_1 : Nominal.NPrf (syn_wnf x ps))
    (hyp_n_19_36i_2 : Nominal.NPrf (syn_wex x (.imp ph ps))) :
    Nominal.NPrf (.imp (.all x ph) ps) :=
  by
  have p0000 := @g_n_19_36 ph ps x hyp_n_19_36_1
  have p0001 :=
    @g_mpbi (syn_wex x (.imp ph ps)) (.imp (.all x ph) ps) hyp_n_19_36i_2 p0000
  exact p0001

@[expose]
noncomputable def g_n_19_37 (ph : Wff) (ps : Wff) (x : Var)
    (hyp_n_19_37_1 : Nominal.NPrf (syn_wnf x ph)) :
    Nominal.NPrf (syn_wb (syn_wex x (.imp ph ps)) (.imp ph (syn_wex x ps))) :=
  by
  have p0000 := @g_n_19_35 ph ps x
  have p0001 := @g_n_19_3 ph x hyp_n_19_37_1
  have p0002 := @g_imbi1i (.all x ph) ph (syn_wex x ps) p0001
  have p0003 :=
    @g_bitri (syn_wex x (.imp ph ps)) (.imp (.all x ph) (syn_wex x ps))
      (.imp ph (syn_wex x ps)) p0000 p0002
  exact p0003

@[expose]
noncomputable def g_n_19_41 (ph : Wff) (ps : Wff) (x : Var)
    (hyp_n_19_41_1 : Nominal.NPrf (syn_wnf x ps)) :
    Nominal.NPrf (syn_wb (syn_wex x (syn_wa ph ps)) (syn_wa (syn_wex x ph) ps)) :=
  by
  have p0000 := @g_n_19_40 ph ps x
  have p0001 := @g_id ps
  have p0002 := @g_exlimi ps ps x hyp_n_19_41_1 p0001
  have p0003 := @g_anim2i (syn_wex x ps) ps (syn_wex x ph) p0002
  have p0004 :=
    @g_syl (syn_wex x (syn_wa ph ps)) (syn_wa (syn_wex x ph) (syn_wex x ps))
      (syn_wa (syn_wex x ph) ps) p0000 p0003
  have p0005 := @g_pm3_21 ps ph
  have p0006 := @g_eximd ps ph (syn_wa ph ps) x hyp_n_19_41_1 p0005
  have p0007 := @g_impcom ps (syn_wex x ph) (syn_wex x (syn_wa ph ps)) p0006
  have p0008 :=
    @g_impbii (syn_wex x (syn_wa ph ps)) (syn_wa (syn_wex x ph) ps) p0004 p0007
  exact p0008

@[expose]
noncomputable def g_n_19_42 (ph : Wff) (ps : Wff) (x : Var)
    (hyp_n_19_42_1 : Nominal.NPrf (syn_wnf x ph)) :
    Nominal.NPrf (syn_wb (syn_wex x (syn_wa ph ps)) (syn_wa ph (syn_wex x ps))) :=
  by
  have p0000 := @g_n_19_41 ps ph x hyp_n_19_42_1
  have p0001 := @g_exancom ph ps x
  have p0002 := @g_ancom ph (syn_wex x ps)
  have p0003 :=
    @g_n_3bitr4i (syn_wex x (syn_wa ps ph)) (syn_wa (syn_wex x ps) ph)
      (syn_wex x (syn_wa ph ps)) (syn_wa ph (syn_wex x ps)) p0000 p0001 p0002
  exact p0003

@[expose]
noncomputable def g_nfan1 (ph : Wff) (ps : Wff) (x : Var)
    (hyp_nfan1_1 : Nominal.NPrf (syn_wnf x ph))
    (hyp_nfan1_2 : Nominal.NPrf (.imp ph (syn_wnf x ps))) :
    Nominal.NPrf (syn_wnf x (syn_wa ph ps)) :=
  by
  have p0000 := @g_nfrd ph ps x hyp_nfan1_2
  have p0001 := @g_imdistani ph ps (.all x ps) p0000
  have p0002 := @g_n_19_28 ph ps x hyp_nfan1_1
  have p0003 :=
    @g_sylibr (syn_wa ph ps) (syn_wa ph (.all x ps)) (.all x (syn_wa ph ps)) p0001 p0002
  have p0004 := @g_nfi (syn_wa ph ps) x p0003
  exact p0004

@[expose]
noncomputable def g_aaan (ph : Wff) (ps : Wff) (x : Var) (y : Var)
    (hyp_aaan_1 : Nominal.NPrf (syn_wnf y ph))
    (hyp_aaan_2 : Nominal.NPrf (syn_wnf x ps)) :
    Nominal.NPrf
      (syn_wb (.all x (.all y (syn_wa ph ps))) (syn_wa (.all x ph) (.all y ps))) :=
  by
  have p0000 := @g_n_19_28 ph ps y hyp_aaan_1
  have p0001 := @g_albii (.all y (syn_wa ph ps)) (syn_wa ph (.all y ps)) x p0000
  have p0002 := @g_nfal ps x y hyp_aaan_2
  have p0003 := @g_n_19_27 ph (.all y ps) x p0002
  have p0004 :=
    @g_bitri (.all x (.all y (syn_wa ph ps))) (.all x (syn_wa ph (.all y ps)))
      (syn_wa (.all x ph) (.all y ps)) p0001 p0003
  exact p0004

@[expose]
noncomputable def g_equs5a (ph : Wff) (x : Var) (y : Var) :
    Nominal.NPrf
      (.imp (syn_wex x (syn_wa (.objEq x y) (.all y ph))) (.all x (.imp (.objEq x y) ph))) :=
  by
  have p0000 := @g_nfa1 (.imp (.objEq x y) ph) x
  have p0001 := Nominal.ax11Structural x y ph
  have p0002 := @g_imp (.objEq x y) (.all y ph) (.all x (.imp (.objEq x y) ph)) p0001
  have p0003 :=
    @g_exlimi (syn_wa (.objEq x y) (.all y ph)) (.all x (.imp (.objEq x y) ph)) x p0000
      p0002
  exact p0003

@[expose]
noncomputable def g_n_19_21v (ph : Wff) (ps : Wff) (x : Var) (dv_ph_x : x ∉ ph.fv) :
    Nominal.NPrf (syn_wb (.all x (.imp ph ps)) (.imp ph (.all x ps))) :=
  by
  let proofSupport : Finset Var := ph.fv ∪ ps.fv ∪ ({ x } : Finset Var)
  have p0000 :=
    @g_nfv ph x
      (by
        first
        | (aesop))
  have p0001 := @g_n_19_21 ph ps x p0000
  exact p0001

@[expose]
noncomputable def g_n_19_23v (ph : Wff) (ps : Wff) (x : Var) (dv_ps_x : x ∉ ps.fv) :
    Nominal.NPrf (syn_wb (.all x (.imp ph ps)) (.imp (syn_wex x ph) ps)) :=
  by
  let proofSupport : Finset Var := ph.fv ∪ ps.fv ∪ ({ x } : Finset Var)
  have p0000 :=
    @g_nfv ps x
      (by
        first
        | (aesop))
  have p0001 := @g_n_19_23 ph ps x p0000
  exact p0001

@[expose]
noncomputable def g_n_19_23vv (ph : Wff) (ps : Wff) (x : Var) (y : Var)
    (dv_ps_x : x ∉ ps.fv) (dv_ps_y : y ∉ ps.fv) :
    Nominal.NPrf
      (syn_wb (.all x (.all y (.imp ph ps))) (.imp (syn_wex x (syn_wex y ph)) ps)) :=
  by
  let proofSupport : Finset Var :=
    ph.fv ∪ ps.fv ∪ ({ x } : Finset Var) ∪ ({ y } : Finset Var)
  have p0000 :=
    @g_n_19_23v ph ps y
      (by
        first
        | (aesop))
  have p0001 := @g_albii (.all y (.imp ph ps)) (.imp (syn_wex y ph) ps) x p0000
  have p0002 :=
    @g_n_19_23v (syn_wex y ph) ps x
      (by
        first
        | (aesop))
  have p0003 :=
    @g_bitri (.all x (.all y (.imp ph ps))) (.all x (.imp (syn_wex y ph) ps))
      (.imp (syn_wex x (syn_wex y ph)) ps) p0001 p0002
  exact p0003

@[expose]
noncomputable def g_n_19_27v (ph : Wff) (ps : Wff) (x : Var) (dv_ps_x : x ∉ ps.fv) :
    Nominal.NPrf (syn_wb (.all x (syn_wa ph ps)) (syn_wa (.all x ph) ps)) :=
  by
  let proofSupport : Finset Var := ph.fv ∪ ps.fv ∪ ({ x } : Finset Var)
  have p0000 :=
    @g_nfv ps x
      (by
        first
        | (aesop))
  have p0001 := @g_n_19_27 ph ps x p0000
  exact p0001

@[expose]
noncomputable def g_n_19_28v (ph : Wff) (ps : Wff) (x : Var) (dv_ph_x : x ∉ ph.fv) :
    Nominal.NPrf (syn_wb (.all x (syn_wa ph ps)) (syn_wa ph (.all x ps))) :=
  by
  let proofSupport : Finset Var := ph.fv ∪ ps.fv ∪ ({ x } : Finset Var)
  have p0000 :=
    @g_nfv ph x
      (by
        first
        | (aesop))
  have p0001 := @g_n_19_28 ph ps x p0000
  exact p0001

@[expose]
noncomputable def g_n_19_36v (ph : Wff) (ps : Wff) (x : Var) (dv_ps_x : x ∉ ps.fv) :
    Nominal.NPrf (syn_wb (syn_wex x (.imp ph ps)) (.imp (.all x ph) ps)) :=
  by
  let proofSupport : Finset Var := ph.fv ∪ ps.fv ∪ ({ x } : Finset Var)
  have p0000 :=
    @g_nfv ps x
      (by
        first
        | (aesop))
  have p0001 := @g_n_19_36 ph ps x p0000
  exact p0001

@[expose]
noncomputable def g_n_19_36aiv (ph : Wff) (ps : Wff) (x : Var) (dv_ps_x : x ∉ ps.fv)
    (hyp_n_19_36aiv_1 : Nominal.NPrf (syn_wex x (.imp ph ps))) :
    Nominal.NPrf (.imp (.all x ph) ps) :=
  by
  let proofSupport : Finset Var := ph.fv ∪ ps.fv ∪ ({ x } : Finset Var)
  have p0000 :=
    @g_nfv ps x
      (by
        first
        | (aesop))
  have p0001 := @g_n_19_36i ph ps x p0000 hyp_n_19_36aiv_1
  exact p0001

@[expose]
noncomputable def g_n_19_37v (ph : Wff) (ps : Wff) (x : Var) (dv_ph_x : x ∉ ph.fv) :
    Nominal.NPrf (syn_wb (syn_wex x (.imp ph ps)) (.imp ph (syn_wex x ps))) :=
  by
  let proofSupport : Finset Var := ph.fv ∪ ps.fv ∪ ({ x } : Finset Var)
  have p0000 :=
    @g_nfv ph x
      (by
        first
        | (aesop))
  have p0001 := @g_n_19_37 ph ps x p0000
  exact p0001

@[expose]
noncomputable def g_n_19_37aiv (ph : Wff) (ps : Wff) (x : Var) (dv_ph_x : x ∉ ph.fv)
    (hyp_n_19_37aiv_1 : Nominal.NPrf (syn_wex x (.imp ph ps))) :
    Nominal.NPrf (.imp ph (syn_wex x ps)) :=
  by
  let proofSupport : Finset Var := ph.fv ∪ ps.fv ∪ ({ x } : Finset Var)
  have p0000 :=
    @g_n_19_37v ph ps x
      (by
        first
        | (aesop))
  have p0001 :=
    @g_mpbi (syn_wex x (.imp ph ps)) (.imp ph (syn_wex x ps)) hyp_n_19_37aiv_1 p0000
  exact p0001

@[expose]
noncomputable def g_n_19_41v (ph : Wff) (ps : Wff) (x : Var) (dv_ps_x : x ∉ ps.fv) :
    Nominal.NPrf (syn_wb (syn_wex x (syn_wa ph ps)) (syn_wa (syn_wex x ph) ps)) :=
  by
  let proofSupport : Finset Var := ph.fv ∪ ps.fv ∪ ({ x } : Finset Var)
  have p0000 :=
    @g_nfv ps x
      (by
        first
        | (aesop))
  have p0001 := @g_n_19_41 ph ps x p0000
  exact p0001

@[expose]
noncomputable def g_n_19_41vv (ph : Wff) (ps : Wff) (x : Var) (y : Var)
    (dv_ps_x : x ∉ ps.fv) (dv_ps_y : y ∉ ps.fv) :
    Nominal.NPrf
      (syn_wb (syn_wex x (syn_wex y (syn_wa ph ps))) (syn_wa (syn_wex x (syn_wex y ph)) ps)) :=
  by
  let proofSupport : Finset Var :=
    ph.fv ∪ ps.fv ∪ ({ x } : Finset Var) ∪ ({ y } : Finset Var)
  have p0000 :=
    @g_n_19_41v ph ps y
      (by
        first
        | (aesop))
  have p0001 := @g_exbii (syn_wex y (syn_wa ph ps)) (syn_wa (syn_wex y ph) ps) x p0000
  have p0002 :=
    @g_n_19_41v (syn_wex y ph) ps x
      (by
        first
        | (aesop))
  have p0003 :=
    @g_bitri (syn_wex x (syn_wex y (syn_wa ph ps))) (syn_wex x (syn_wa (syn_wex y ph) ps))
      (syn_wa (syn_wex x (syn_wex y ph)) ps) p0001 p0002
  exact p0003

@[expose]
noncomputable def g_n_19_41vvv (ph : Wff) (ps : Wff) (x : Var) (y : Var) (z : Var)
    (dv_ps_x : x ∉ ps.fv) (dv_ps_y : y ∉ ps.fv) (dv_ps_z : z ∉ ps.fv) :
    Nominal.NPrf
      (syn_wb (syn_wex x (syn_wex y (syn_wex z (syn_wa ph ps))))
        (syn_wa (syn_wex x (syn_wex y (syn_wex z ph))) ps)) :=
  by
  let proofSupport : Finset Var :=
    ph.fv ∪ ps.fv ∪ ({ x } : Finset Var) ∪ ({ y } : Finset Var) ∪ ({ z } : Finset Var)
  have p0000 :=
    @g_n_19_41vv ph ps y z
      (by
        first
        | (aesop))
      (by
        first
        | (aesop))
  have p0001 :=
    @g_exbii (syn_wex y (syn_wex z (syn_wa ph ps))) (syn_wa (syn_wex y (syn_wex z ph)) ps)
      x p0000
  have p0002 :=
    @g_n_19_41v (syn_wex y (syn_wex z ph)) ps x
      (by
        first
        | (aesop))
  have p0003 :=
    @g_bitri (syn_wex x (syn_wex y (syn_wex z (syn_wa ph ps))))
      (syn_wex x (syn_wa (syn_wex y (syn_wex z ph)) ps))
      (syn_wa (syn_wex x (syn_wex y (syn_wex z ph))) ps) p0001 p0002
  exact p0003

@[expose]
noncomputable def g_n_19_42v (ph : Wff) (ps : Wff) (x : Var) (dv_ph_x : x ∉ ph.fv) :
    Nominal.NPrf (syn_wb (syn_wex x (syn_wa ph ps)) (syn_wa ph (syn_wex x ps))) :=
  by
  let proofSupport : Finset Var := ph.fv ∪ ps.fv ∪ ({ x } : Finset Var)
  have p0000 :=
    @g_nfv ph x
      (by
        first
        | (aesop))
  have p0001 := @g_n_19_42 ph ps x p0000
  exact p0001

@[expose]
noncomputable def g_exdistr (ph : Wff) (ps : Wff) (x : Var) (y : Var)
    (dv_ph_y : y ∉ ph.fv) :
    Nominal.NPrf
      (syn_wb (syn_wex x (syn_wex y (syn_wa ph ps))) (syn_wex x (syn_wa ph (syn_wex y ps)))) :=
  by
  let proofSupport : Finset Var :=
    ph.fv ∪ ps.fv ∪ ({ x } : Finset Var) ∪ ({ y } : Finset Var)
  have p0000 :=
    @g_n_19_42v ph ps y
      (by
        first
        | (aesop))
  have p0001 := @g_exbii (syn_wex y (syn_wa ph ps)) (syn_wa ph (syn_wex y ps)) x p0000
  exact p0001

@[expose]
noncomputable def g_n_19_42vv (ph : Wff) (ps : Wff) (x : Var) (y : Var)
    (dv_ph_x : x ∉ ph.fv) (dv_ph_y : y ∉ ph.fv) :
    Nominal.NPrf
      (syn_wb (syn_wex x (syn_wex y (syn_wa ph ps))) (syn_wa ph (syn_wex x (syn_wex y ps)))) :=
  by
  let proofSupport : Finset Var :=
    ph.fv ∪ ps.fv ∪ ({ x } : Finset Var) ∪ ({ y } : Finset Var)
  have p0000 :=
    @g_exdistr ph ps x y
      (by
        first
        | (aesop))
  have p0001 :=
    @g_n_19_42v ph (syn_wex y ps) x
      (by
        first
        | (aesop))
  have p0002 :=
    @g_bitri (syn_wex x (syn_wex y (syn_wa ph ps))) (syn_wex x (syn_wa ph (syn_wex y ps)))
      (syn_wa ph (syn_wex x (syn_wex y ps))) p0000 p0001
  exact p0002

@[expose]
noncomputable def g_eean (ph : Wff) (ps : Wff) (x : Var) (y : Var)
    (hyp_eean_1 : Nominal.NPrf (syn_wnf y ph))
    (hyp_eean_2 : Nominal.NPrf (syn_wnf x ps)) :
    Nominal.NPrf
      (syn_wb (syn_wex x (syn_wex y (syn_wa ph ps))) (syn_wa (syn_wex x ph) (syn_wex y ps))) :=
  by
  have p0000 := @g_n_19_42 ph ps y hyp_eean_1
  have p0001 := @g_exbii (syn_wex y (syn_wa ph ps)) (syn_wa ph (syn_wex y ps)) x p0000
  have p0002 := @g_nfex ps x y hyp_eean_2
  have p0003 := @g_n_19_41 ph (syn_wex y ps) x p0002
  have p0004 :=
    @g_bitri (syn_wex x (syn_wex y (syn_wa ph ps))) (syn_wex x (syn_wa ph (syn_wex y ps)))
      (syn_wa (syn_wex x ph) (syn_wex y ps)) p0001 p0003
  exact p0004

@[expose]
noncomputable def g_eeanv (ph : Wff) (ps : Wff) (x : Var) (y : Var) (dv_ph_y : y ∉ ph.fv)
    (dv_ps_x : x ∉ ps.fv) :
    Nominal.NPrf
      (syn_wb (syn_wex x (syn_wex y (syn_wa ph ps))) (syn_wa (syn_wex x ph) (syn_wex y ps))) :=
  by
  let proofSupport : Finset Var :=
    ph.fv ∪ ps.fv ∪ ({ x } : Finset Var) ∪ ({ y } : Finset Var)
  have p0000 :=
    @g_nfv ph y
      (by
        first
        | (aesop))
  have p0001 :=
    @g_nfv ps x
      (by
        first
        | (aesop))
  have p0002 := @g_eean ph ps x y p0000 p0001
  exact p0002

@[expose]
noncomputable def g_eeeanv (ph : Wff) (ps : Wff) (ch : Wff) (x : Var) (y : Var) (z : Var)
    (dv_ch_x : x ∉ ch.fv) (dv_ch_y : y ∉ ch.fv) (dv_ph_y : y ∉ ph.fv)
    (dv_ph_z : z ∉ ph.fv) (dv_ps_x : x ∉ ps.fv) (dv_ps_z : z ∉ ps.fv) (_dv_x_y : x ≠ y)
    (dv_x_z : x ≠ z) :
    Nominal.NPrf
      (syn_wb (syn_wex x (syn_wex y (syn_wex z (syn_w3a ph ps ch))))
        (syn_w3a (syn_wex x ph) (syn_wex y ps) (syn_wex z ch))) :=
  by
  let proofSupport : Finset Var :=
    ph.fv ∪ ps.fv ∪ ch.fv ∪ ({ x } : Finset Var) ∪ ({ y } : Finset Var) ∪
      ({ z } : Finset Var)
  have p0000 := (Nominal.biimpRefl (syn_w3a ph ps ch))
  have p0001 := @g_n_3exbii (syn_w3a ph ps ch) (syn_wa (syn_wa ph ps) ch) x y z p0000
  have p0002 :=
    @g_eeanv (syn_wa ph ps) ch y z
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
    @g_exbii (syn_wex y (syn_wex z (syn_wa (syn_wa ph ps) ch)))
      (syn_wa (syn_wex y (syn_wa ph ps)) (syn_wex z ch)) x p0002
  have p0004 :=
    @g_eeanv ph ps x y
      (by
        first
        | (aesop))
      (by
        first
        | (aesop))
  have p0005 :=
    @g_anbi1i (syn_wex x (syn_wex y (syn_wa ph ps)))
      (syn_wa (syn_wex x ph) (syn_wex y ps)) (syn_wex z ch) p0004
  have p0006 :=
    @g_n_19_41v (syn_wex y (syn_wa ph ps)) (syn_wex z ch) x
      (by
        first
        |
          (simp (config :=
              {
                failIfUnchanged :=
                  false }) only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wex,
              Finset.mem_erase] at ⊢;
            aesop))
  have p0007 := (Nominal.biimpRefl (syn_w3a (syn_wex x ph) (syn_wex y ps) (syn_wex z ch)))
  have p0008 :=
    @g_n_3bitr4i (syn_wa (syn_wex x (syn_wex y (syn_wa ph ps))) (syn_wex z ch))
      (syn_wa (syn_wa (syn_wex x ph) (syn_wex y ps)) (syn_wex z ch))
      (syn_wex x (syn_wa (syn_wex y (syn_wa ph ps)) (syn_wex z ch)))
      (syn_w3a (syn_wex x ph) (syn_wex y ps) (syn_wex z ch)) p0005 p0006 p0007
  have p0009 :=
    @g_n_3bitri (syn_wex x (syn_wex y (syn_wex z (syn_w3a ph ps ch))))
      (syn_wex x (syn_wex y (syn_wex z (syn_wa (syn_wa ph ps) ch))))
      (syn_wex x (syn_wa (syn_wex y (syn_wa ph ps)) (syn_wex z ch)))
      (syn_w3a (syn_wex x ph) (syn_wex y ps) (syn_wex z ch)) p0001 p0003 p0008
  exact p0009

@[expose]
noncomputable def g_ee4anv (ph : Wff) (ps : Wff) (x : Var) (y : Var) (z : Var) (w : Var)
    (dv_ph_w : w ∉ ph.fv) (dv_ph_z : z ∉ ph.fv) (dv_ps_x : x ∉ ps.fv)
    (dv_ps_y : y ∉ ps.fv) (_dv_w_x : w ≠ x) (_dv_y_z : y ≠ z) :
    Nominal.NPrf
      (syn_wb (syn_wex x (syn_wex y (syn_wex z (syn_wex w (syn_wa ph ps)))))
        (syn_wa (syn_wex x (syn_wex y ph)) (syn_wex z (syn_wex w ps)))) :=
  by
  let proofSupport : Finset Var :=
    ph.fv ∪ ps.fv ∪ ({ x } : Finset Var) ∪ ({ y } : Finset Var) ∪ ({ z } : Finset Var) ∪
      ({ w } : Finset Var)
  have p0000 := @g_excom (syn_wex w (syn_wa ph ps)) y z
  have p0001 :=
    @g_exbii (syn_wex y (syn_wex z (syn_wex w (syn_wa ph ps))))
      (syn_wex z (syn_wex y (syn_wex w (syn_wa ph ps)))) x p0000
  have p0002 :=
    @g_eeanv ph ps y w
      (by
        first
        | (aesop))
      (by
        first
        | (aesop))
  have p0003 :=
    @g_n_2exbii (syn_wex y (syn_wex w (syn_wa ph ps)))
      (syn_wa (syn_wex y ph) (syn_wex w ps)) x z p0002
  have p0004 :=
    @g_eeanv (syn_wex y ph) (syn_wex w ps) x z
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
    @g_n_3bitri (syn_wex x (syn_wex y (syn_wex z (syn_wex w (syn_wa ph ps)))))
      (syn_wex x (syn_wex z (syn_wex y (syn_wex w (syn_wa ph ps)))))
      (syn_wex x (syn_wex z (syn_wa (syn_wex y ph) (syn_wex w ps))))
      (syn_wa (syn_wex x (syn_wex y ph)) (syn_wex z (syn_wex w ps))) p0001 p0003 p0004
  exact p0005

@[expose]
noncomputable def g_nexdv (ph : Wff) (ps : Wff) (x : Var) (dv_ph_x : x ∉ ph.fv)
    (hyp_nexdv_1 : Nominal.NPrf (.imp ph (.neg ps))) :
    Nominal.NPrf (.imp ph (.neg (syn_wex x ps))) :=
  by
  let proofSupport : Finset Var := ph.fv ∪ ps.fv ∪ ({ x } : Finset Var)
  have p0000 :=
    @g_nfv ph x
      (by
        first
        | (aesop))
  have p0001 := @g_nexd ph ps x p0000 hyp_nexdv_1
  exact p0001

@[expose]
noncomputable def g_stdpc7 (ph : Wff) (x : Var) (y : Var) :
    Nominal.NPrf (.imp (.objEq x y) (.imp (syn_wsb x y ph) ph)) :=
  by
  have p0000 := @g_sbequ2 ph y x
  have p0001 := @g_equcoms (.imp (syn_wsb x y ph) ph) y x p0000
  exact p0001

@[expose]
noncomputable def g_sbequ1 (ph : Wff) (x : Var) (y : Var) :
    Nominal.NPrf (.imp (.objEq x y) (.imp ph (syn_wsb y x ph))) :=
  by
  have p0000 := @g_pm3_4 (.objEq x y) ph
  have p0001 := @g_n_19_8a (syn_wa (.objEq x y) ph) x
  have p0002 := (Nominal.biimpRefl (syn_wsb y x ph))
  have p0003 :=
    @g_sylanbrc (syn_wa (.objEq x y) ph) (.imp (.objEq x y) ph)
      (syn_wex x (syn_wa (.objEq x y) ph)) (syn_wsb y x ph) p0000 p0001 p0002
  have p0004 := @g_ex (.objEq x y) ph (syn_wsb y x ph) p0003
  exact p0004

@[expose]
noncomputable def g_sbequ12 (ph : Wff) (x : Var) (y : Var) :
    Nominal.NPrf (.imp (.objEq x y) (syn_wb ph (syn_wsb y x ph))) :=
  by
  have p0000 := @g_sbequ1 ph x y
  have p0001 := @g_sbequ2 ph x y
  have p0002 := @g_impbid (.objEq x y) ph (syn_wsb y x ph) p0000 p0001
  exact p0002

@[expose]
noncomputable def g_sbequ12r (ph : Wff) (x : Var) (y : Var) :
    Nominal.NPrf (.imp (.objEq x y) (syn_wb (syn_wsb x y ph) ph)) :=
  by
  have p0000 := @g_sbequ12 ph y x
  have p0001 := @g_bicomd (.objEq y x) ph (syn_wsb x y ph) p0000
  have p0002 := @g_equcoms (syn_wb (syn_wsb x y ph) ph) y x p0001
  exact p0002

@[expose]
noncomputable def g_sbid (ph : Wff) (x : Var) :
    Nominal.NPrf (syn_wb (syn_wsb x x ph) ph) :=
  by
  have p0000 := @g_equid x
  have p0001 := @g_sbequ12 ph x x
  have p0002 := Nominal.mp p0000 p0001
  have p0003 := @g_bicomi ph (syn_wsb x x ph) p0002
  exact p0003

@[expose]
noncomputable def g_sb4a (ph : Wff) (x : Var) (y : Var) :
    Nominal.NPrf (.imp (syn_wsb y x (.all y ph)) (.all x (.imp (.objEq x y) ph))) :=
  by
  have p0000 := @g_sb1 (.all y ph) x y
  have p0001 := @g_equs5a ph x y
  have p0002 :=
    @g_syl (syn_wsb y x (.all y ph)) (syn_wex x (syn_wa (.objEq x y) (.all y ph)))
      (.all x (.imp (.objEq x y) ph)) p0000 p0001
  exact p0002

@[expose]
noncomputable def g_ax12v (x : Var) (y : Var) (z : Var) (_dv_x_z : x ≠ z)
    (_dv_y_z : y ≠ z) :
    Nominal.NPrf (.imp (.neg (.objEq x y)) (.imp (.objEq y z) (.all x (.objEq y z)))) :=
  by
  have p0000 := Nominal.ax12 x y z
  exact p0000

@[expose]
noncomputable def g_ax12olem1 (y : Var) (z : Var) (w : Var) (dv_w_y : w ≠ y)
    (dv_w_z : w ≠ z) :
    Nominal.NPrf
      (syn_wb (syn_wex w (syn_wa (.objEq y w) (.neg (.objEq z w)))) (.neg (.objEq y z))) :=
  by
  let proofSupport : Finset Var :=
    ({ y } : Finset Var) ∪ ({ z } : Finset Var) ∪ ({ w } : Finset Var)
  have p0000 := Nominal.ax8 y w z
  have p0001 := @g_equcomi w z
  have p0002 := @g_syl6 (.objEq y w) (.objEq y z) (.objEq w z) (.objEq z w) p0000 p0001
  have p0003 := @g_con3and (.objEq y w) (.objEq y z) (.objEq z w) p0002
  have p0004 :=
    @g_exlimiv (syn_wa (.objEq y w) (.neg (.objEq z w))) (.neg (.objEq y z)) w
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
  have p0007 := @g_equcomi z y
  have p0008 := @g_syl6 (.objEq w z) (.objEq w y) (.objEq z y) (.objEq y z) p0006 p0007
  have p0009 := @g_equcoms (.imp (.objEq w y) (.objEq y z)) w z p0008
  have p0010 := @g_com12 (.objEq z w) (.objEq w y) (.objEq y z) p0009
  have p0011 := @g_con3d (.objEq w y) (.objEq z w) (.objEq y z) p0010
  have p0012 := @g_equcomi w y
  have p0013 :=
    @g_jctild (.objEq w y) (.neg (.objEq y z)) (.neg (.objEq z w)) (.objEq y w) p0011
      p0012
  have p0014 :=
    @g_spimeh (.neg (.objEq y z)) (syn_wa (.objEq y w) (.neg (.objEq z w))) w y
      (by
        first
        | (aesop))
      p0005 p0013
  have p0015 :=
    @g_impbii (syn_wex w (syn_wa (.objEq y w) (.neg (.objEq z w)))) (.neg (.objEq y z))
      p0004 p0014
  exact p0015

@[expose]
noncomputable def g_ax12olem2 (x : Var) (y : Var) (z : Var) (w : Var) (dv_w_x : w ≠ x)
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
    @g_anim1d (.neg (.objEq x y)) (.objEq y w) (.all x (.objEq y w)) (.neg (.objEq z w))
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
    @g_anim2i (.neg (.objEq z w)) (.all x (.neg (.objEq z w))) (.all x (.objEq y w)) p0001
  have p0003 := @g_n_19_26 (.objEq y w) (.neg (.objEq z w)) x
  have p0004 :=
    @g_sylibr (syn_wa (.all x (.objEq y w)) (.neg (.objEq z w)))
      (syn_wa (.all x (.objEq y w)) (.all x (.neg (.objEq z w))))
      (.all x (syn_wa (.objEq y w) (.neg (.objEq z w)))) p0002 p0003
  have p0005 :=
    @g_syl6 (.neg (.objEq x y)) (syn_wa (.objEq y w) (.neg (.objEq z w)))
      (syn_wa (.all x (.objEq y w)) (.neg (.objEq z w)))
      (.all x (syn_wa (.objEq y w) (.neg (.objEq z w)))) p0000 p0004
  have p0006 :=
    @g_eximdv (.neg (.objEq x y)) (syn_wa (.objEq y w) (.neg (.objEq z w)))
      (.all x (syn_wa (.objEq y w) (.neg (.objEq z w)))) w
      (by
        first
        |
          (simp (config :=
              { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_wff_neg,
              NFChoice.Compiler.CoreFVSimp.fv_wff_objEq] at ⊢;
            aesop))
      p0005
  have p0007 := @g_n_19_12 (syn_wa (.objEq y w) (.neg (.objEq z w))) w x
  have p0008 :=
    @g_syl6 (.neg (.objEq x y)) (syn_wex w (syn_wa (.objEq y w) (.neg (.objEq z w))))
      (syn_wex w (.all x (syn_wa (.objEq y w) (.neg (.objEq z w)))))
      (.all x (syn_wex w (syn_wa (.objEq y w) (.neg (.objEq z w))))) p0006 p0007
  have p0009 :=
    @g_ax12olem1 y z w
      (by
        first
        | (aesop))
      (by
        first
        | (aesop))
  have p0010 :=
    @g_albii (syn_wex w (syn_wa (.objEq y w) (.neg (.objEq z w)))) (.neg (.objEq y z)) x
      p0009
  have p0011 :=
    @g_n_3imtr3g (.neg (.objEq x y)) (syn_wex w (syn_wa (.objEq y w) (.neg (.objEq z w))))
      (.all x (syn_wex w (syn_wa (.objEq y w) (.neg (.objEq z w))))) (.neg (.objEq y z))
      (.all x (.neg (.objEq y z))) p0008 p0009 p0010
  exact p0011

@[expose]
noncomputable def g_ax12olem3 (x : Var) (y : Var) (z : Var) :
    Nominal.NPrf
      (syn_wb (.imp (.neg (.objEq x y))
          (.imp (.neg (.all x (.neg (.objEq y z)))) (.all x (.objEq y z))))
        (syn_wa (.imp (.neg (.objEq x y)) (.imp (.objEq y z) (.all x (.objEq y z))))
          (.imp (.neg (.objEq x y))
            (.imp (.neg (.objEq y z)) (.all x (.neg (.objEq y z))))))) :=
  by
  have p0000 := @g_sp (.neg (.objEq y z)) x
  have p0001 := @g_con2i (.all x (.neg (.objEq y z))) (.objEq y z) p0000
  have p0002 :=
    @g_imim1i (.objEq y z) (.neg (.all x (.neg (.objEq y z)))) (.all x (.objEq y z)) p0001
  have p0003 :=
    @g_imim2i (.imp (.neg (.all x (.neg (.objEq y z)))) (.all x (.objEq y z)))
      (.imp (.objEq y z) (.all x (.objEq y z))) (.neg (.objEq x y)) p0002
  have p0004 := @g_sp (.objEq y z) x
  have p0005 :=
    @g_imim2i (.all x (.objEq y z)) (.objEq y z) (.neg (.all x (.neg (.objEq y z)))) p0004
  have p0006 :=
    @g_con1d (.imp (.neg (.all x (.neg (.objEq y z)))) (.all x (.objEq y z)))
      (.all x (.neg (.objEq y z))) (.objEq y z) p0005
  have p0007 :=
    @g_imim2i (.imp (.neg (.all x (.neg (.objEq y z)))) (.all x (.objEq y z)))
      (.imp (.neg (.objEq y z)) (.all x (.neg (.objEq y z)))) (.neg (.objEq x y)) p0006
  have p0008 :=
    @g_jca
      (.imp (.neg (.objEq x y))
        (.imp (.neg (.all x (.neg (.objEq y z)))) (.all x (.objEq y z))))
      (.imp (.neg (.objEq x y)) (.imp (.objEq y z) (.all x (.objEq y z))))
      (.imp (.neg (.objEq x y)) (.imp (.neg (.objEq y z)) (.all x (.neg (.objEq y z)))))
      p0003 p0007
  have p0009 := @g_con1 (.objEq y z) (.all x (.neg (.objEq y z)))
  have p0010 :=
    @g_imim1d (.imp (.neg (.objEq y z)) (.all x (.neg (.objEq y z))))
      (.neg (.all x (.neg (.objEq y z)))) (.objEq y z) (.all x (.objEq y z)) p0009
  have p0011 :=
    @g_com12 (.imp (.neg (.objEq y z)) (.all x (.neg (.objEq y z))))
      (.imp (.objEq y z) (.all x (.objEq y z)))
      (.imp (.neg (.all x (.neg (.objEq y z)))) (.all x (.objEq y z))) p0010
  have p0012 :=
    @g_imim3i (.imp (.objEq y z) (.all x (.objEq y z)))
      (.imp (.neg (.objEq y z)) (.all x (.neg (.objEq y z))))
      (.imp (.neg (.all x (.neg (.objEq y z)))) (.all x (.objEq y z))) (.neg (.objEq x y))
      p0011
  have p0013 :=
    @g_imp (.imp (.neg (.objEq x y)) (.imp (.objEq y z) (.all x (.objEq y z))))
      (.imp (.neg (.objEq x y)) (.imp (.neg (.objEq y z)) (.all x (.neg (.objEq y z)))))
      (.imp (.neg (.objEq x y))
        (.imp (.neg (.all x (.neg (.objEq y z)))) (.all x (.objEq y z))))
      p0012
  have p0014 :=
    @g_impbii
      (.imp (.neg (.objEq x y))
        (.imp (.neg (.all x (.neg (.objEq y z)))) (.all x (.objEq y z))))
      (syn_wa (.imp (.neg (.objEq x y)) (.imp (.objEq y z) (.all x (.objEq y z))))
        (.imp (.neg (.objEq x y)) (.imp (.neg (.objEq y z)) (.all x (.neg (.objEq y z))))))
      p0008 p0013
  exact p0014

@[expose]
noncomputable def g_ax12olem4 (x : Var) (y : Var) (z : Var) (w : Var) (dv_w_x : w ≠ x)
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
    @g_ax12olem2 x y z w
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
  have p0001 := @g_ax12olem3 x y z
  have p0002 :=
    @g_mpbir2an
      (.imp (.neg (.objEq x y))
        (.imp (.neg (.all x (.neg (.objEq y z)))) (.all x (.objEq y z))))
      (.imp (.neg (.objEq x y)) (.imp (.objEq y z) (.all x (.objEq y z))))
      (.imp (.neg (.objEq x y)) (.imp (.neg (.objEq y z)) (.all x (.neg (.objEq y z)))))
      hyp_ax12olem4_1 p0000 p0001
  exact p0002

@[expose]
noncomputable def g_ax12olem5 (x : Var) (y : Var) (z : Var)
    (hyp_ax12olem5_1 : Nominal.NPrf (.imp (.neg (.objEq x y))
          (.imp (.neg (.all x (.neg (.objEq y z)))) (.all x (.objEq y z))))) :
    Nominal.NPrf
      (.imp (.neg (.all x (.objEq x y))) (.imp (.objEq y z) (.all x (.objEq y z)))) :=
  by
  have p0000 := @g_exnal (.objEq x y) x
  have p0001 := @g_n_19_8a (.objEq y z) x
  have p0002 := @g_hbe1 (.objEq y z) x
  have p0003 := @g_hba1 (.objEq y z) x
  have p0004 := @g_hbim (syn_wex x (.objEq y z)) (.all x (.objEq y z)) x p0002 p0003
  have p0005 := (Nominal.biimpRefl (syn_wex x (.objEq y z)))
  have p0006 :=
    @g_syl5bi (syn_wex x (.objEq y z)) (.neg (.all x (.neg (.objEq y z))))
      (.neg (.objEq x y)) (.all x (.objEq y z)) p0005 hyp_ax12olem5_1
  have p0007 :=
    @g_exlimih (.neg (.objEq x y)) (.imp (syn_wex x (.objEq y z)) (.all x (.objEq y z))) x
      p0004 p0006
  have p0008 :=
    @g_syl5 (.objEq y z) (syn_wex x (.objEq y z)) (syn_wex x (.neg (.objEq x y)))
      (.all x (.objEq y z)) p0001 p0007
  have p0009 :=
    @g_sylbir (.neg (.all x (.objEq x y))) (syn_wex x (.neg (.objEq x y)))
      (.imp (.objEq y z) (.all x (.objEq y z))) p0000 p0008
  exact p0009

@[expose]
noncomputable def g_ax12olem6 (x : Var) (y : Var) (z : Var) (w : Var) (dv_w_x : w ≠ x)
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
  have p0000 := @g_hbn1 (.objEq x z) x
  have p0001 := @g_hbim1 (.neg (.all x (.objEq x z))) (.objEq z w) x p0000 hyp_ax12olem6_1
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
  have p0003 := @g_equcom z w
  have p0004 := @g_equequ1 w y z
  have p0005 := @g_syl5bb (.objEq z w) (.objEq w z) (.objEq w y) (.objEq y z) p0003 p0004
  have p0006 :=
    @g_imbi2d (.objEq w y) (.objEq z w) (.objEq y z) (.neg (.all x (.objEq x z))) p0005
  have p0007 :=
    @g_dvelimhw (.imp (.neg (.all x (.objEq x z))) (.objEq z w))
      (.imp (.neg (.all x (.objEq x z))) (.objEq y z)) x y w
      (by
        first
        | (aesop))
      (by
        first
        | (aesop))
      p0001 p0002 p0006 hyp_ax12olem6_2
  have p0008 := @g_n_19_21h (.neg (.all x (.objEq x z))) (.objEq y z) x p0000
  have p0009 :=
    @g_syl6ib (.neg (.all x (.objEq x y)))
      (.imp (.neg (.all x (.objEq x z))) (.objEq y z))
      (.all x (.imp (.neg (.all x (.objEq x z))) (.objEq y z)))
      (.imp (.neg (.all x (.objEq x z))) (.all x (.objEq y z))) p0007 p0008
  have p0010 :=
    @g_pm2_86d (.neg (.all x (.objEq x y))) (.neg (.all x (.objEq x z))) (.objEq y z)
      (.all x (.objEq y z)) p0009
  exact p0010

@[expose]
noncomputable def g_ax12olem7 (x : Var) (y : Var) (z : Var) (w : Var) (dv_w_x : w ≠ x)
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
  have p0000 := @g_ax12olem5 x z w hyp_ax12olem7_1
  have p0001 := @g_ax12olem5 x y w hyp_ax12olem7_2
  have p0002 :=
    @g_ax12olem6 x y z w
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

@[expose]
noncomputable def g_ax12o (x : Var) (y : Var) (z : Var) :
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
    @g_ax12v z y w
      (by
        first
        | (aesop))
      (by
        first
        | (aesop))
  have p0001 :=
    @g_ax12v z y v
      (by
        first
        | (aesop))
      (by
        first
        | (aesop))
  have p0002 :=
    @g_ax12olem4 z y w v
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
    @g_ax12v z x w
      (by
        first
        | (aesop))
      (by
        first
        | (aesop))
  have p0004 :=
    @g_ax12v z x v
      (by
        first
        | (aesop))
      (by
        first
        | (aesop))
  have p0005 :=
    @g_ax12olem4 z x w v
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
    @g_ax12olem7 z x y w
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

@[expose]
noncomputable def g_ax10lem1 (x : Var) (y : Var) (w : Var) (dv_w_x : w ≠ x)
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
    @g_cbvalivw (.objEq x w) (.objEq v w) x v
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
    @g_cbvalivw (.objEq v w) (.objEq y w) v y
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
    @g_syl (.all x (.objEq x w)) (.all v (.objEq v w)) (.all y (.objEq y w)) p0001 p0003
  exact p0004

@[expose]
noncomputable def g_ax10lem2 (x : Var) (y : Var) (z : Var) (dv_x_y : x ≠ y)
    (dv_x_z : x ≠ z) : Nominal.NPrf (.imp (.all x (.objEq x y)) (.all x (.objEq x z))) :=
  by
  let proofSupport : Finset Var :=
    ({ x } : Finset Var) ∪ ({ y } : Finset Var) ∪ ({ z } : Finset Var)
  have p0000 := @g_hbe1 (.neg (.objEq x y)) x
  have p0001 := @g_equequ2 z y x
  have p0002 := @g_biimprd (.objEq z y) (.objEq x z) (.objEq x y) p0001
  have p0003 := @g_con3rr3 (.objEq z y) (.objEq x y) (.objEq x z) p0002
  have p0004 := @g_n_19_8a (.neg (.objEq x y)) x
  have p0005 :=
    @g_syl6 (.neg (.objEq x z)) (.objEq z y) (.neg (.objEq x y))
      (syn_wex x (.neg (.objEq x y))) p0003 p0004
  have p0006 :=
    Nominal.ax17 (.neg (.objEq z y)) x
      (by
        first
        |
          (simp (config :=
              { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_wff_neg,
              NFChoice.Compiler.CoreFVSimp.fv_wff_objEq] at ⊢;
            aesop))
  have p0007 := @g_equequ1 x z y
  have p0008 := @g_notbid (.objEq x z) (.objEq x y) (.objEq z y) p0007
  have p0009 := @g_biimprd (.objEq x z) (.neg (.objEq x y)) (.neg (.objEq z y)) p0008
  have p0010 :=
    @g_spimeh (.neg (.objEq z y)) (.neg (.objEq x y)) x z
      (by
        first
        | (aesop))
      p0006 p0009
  have p0011 :=
    @g_pm2_61d1 (.neg (.objEq x z)) (.objEq z y) (syn_wex x (.neg (.objEq x y))) p0005
      p0010
  have p0012 :=
    @g_exlimih (.neg (.objEq x z)) (syn_wex x (.neg (.objEq x y))) x p0000 p0011
  have p0013 := @g_exnal (.objEq x z) x
  have p0014 := @g_exnal (.objEq x y) x
  have p0015 :=
    @g_n_3imtr3i (syn_wex x (.neg (.objEq x z))) (syn_wex x (.neg (.objEq x y)))
      (.neg (.all x (.objEq x z))) (.neg (.all x (.objEq x y))) p0012 p0013 p0014
  have p0016 := @g_con4i (.all x (.objEq x z)) (.all x (.objEq x y)) p0015
  exact p0016

@[expose]
noncomputable def g_ax10lem3 (x : Var) (y : Var) (dv_x_y : x ≠ y) :
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
    @g_ax10lem2 x y z
      (by
        first
        | (aesop))
      (by
        first
        | (aesop))
  have p0001 :=
    @g_ax10lem1 x w z
      (by
        first
        | (aesop))
      (by
        first
        | (aesop))
  have p0002 :=
    @g_ax10lem2 w z x
      (by
        first
        | (aesop))
      (by
        first
        | (aesop))
  have p0003 :=
    @g_syl (.all x (.objEq x z)) (.all w (.objEq w z)) (.all w (.objEq w x)) p0001 p0002
  have p0004 :=
    @g_ax10lem1 w y x
      (by
        first
        | (aesop))
      (by
        first
        | (aesop))
  have p0005 :=
    @g_syl (.all x (.objEq x z)) (.all w (.objEq w x)) (.all y (.objEq y x)) p0003 p0004
  have p0006 :=
    @g_syl (.all x (.objEq x y)) (.all x (.objEq x z)) (.all y (.objEq y x)) p0000 p0005
  exact p0006

@[expose]
noncomputable def g_dvelimv (ph : Wff) (ps : Wff) (x : Var) (y : Var) (z : Var)
    (dv_ph_x : x ∉ ph.fv) (dv_ps_z : z ∉ ps.fv) (dv_x_z : x ≠ z) (dv_y_z : y ≠ z)
    (hyp_dvelimv_1 : Nominal.NPrf (.imp (.objEq z y) (syn_wb ph ps))) :
    Nominal.NPrf (.imp (.neg (.all x (.objEq x y))) (.imp ps (.all x ps))) :=
  by
  let proofSupport : Finset Var :=
    ph.fv ∪ ps.fv ∪ ({ x } : Finset Var) ∪ ({ y } : Finset Var) ∪ ({ z } : Finset Var)
  have p0000 :=
    Nominal.ax17 ps z
      (by
        first
        | (aesop))
  have p0001 := @g_a1d ps (.all z ps) (.objEq z y) p0000
  have p0002 := @g_alrimih ps (.imp (.objEq z y) (.all z ps)) z p0000 p0001
  have p0003 := @g_sp ps z
  have p0004 := @g_syl5ibr (.all z ps) ph (.objEq z y) ps p0003 hyp_dvelimv_1
  have p0005 := @g_a2i (.objEq z y) (.all z ps) ph p0004
  have p0006 := @g_alimi (.imp (.objEq z y) (.all z ps)) (.imp (.objEq z y) ph) z p0005
  have p0007 :=
    @g_syl ps (.all z (.imp (.objEq z y) (.all z ps))) (.all z (.imp (.objEq z y) ph))
      p0002 p0006
  have p0008 :=
    @g_ax10lem3 z x
      (by
        first
        | (aesop))
  have p0009 := @g_con3i (.all z (.objEq z x)) (.all x (.objEq x z)) p0008
  have p0010 := @g_hbn1 (.objEq z x) z
  have p0011 :=
    @g_ax10lem3 x z
      (by
        first
        | (aesop))
  have p0012 := @g_con3i (.all x (.objEq x z)) (.all z (.objEq z x)) p0011
  have p0013 :=
    @g_alrimih (.neg (.all z (.objEq z x))) (.neg (.all x (.objEq x z))) z p0010 p0012
  have p0014 :=
    @g_syl (.neg (.all x (.objEq x z))) (.neg (.all z (.objEq z x)))
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
    @g_hban (.neg (.all x (.objEq x z))) (.neg (.all x (.objEq x y))) z p0014 p0015
  have p0017 := @g_hbn1 (.objEq x z) x
  have p0018 := @g_hbn1 (.objEq x y) x
  have p0019 :=
    @g_hban (.neg (.all x (.objEq x z))) (.neg (.all x (.objEq x y))) x p0017 p0018
  have p0020 := @g_ax12o z y x
  have p0021 :=
    @g_imp (.neg (.all x (.objEq x z))) (.neg (.all x (.objEq x y)))
      (.imp (.objEq z y) (.all x (.objEq z y))) p0020
  have p0022 :=
    @g_a17d (syn_wa (.neg (.all x (.objEq x z))) (.neg (.all x (.objEq x y)))) ph x
      (by
        first
        | (aesop))
  have p0023 :=
    @g_hbimd (syn_wa (.neg (.all x (.objEq x z))) (.neg (.all x (.objEq x y))))
      (.objEq z y) ph x p0019 p0021 p0022
  have p0024 :=
    @g_hbald (syn_wa (.neg (.all x (.objEq x z))) (.neg (.all x (.objEq x y))))
      (.imp (.objEq z y) ph) x z p0016 p0023
  have p0025 := @g_biimpd (.objEq z y) ph ps hyp_dvelimv_1
  have p0026 := @g_a2i (.objEq z y) ph ps p0025
  have p0027 := @g_alimi (.imp (.objEq z y) ph) (.imp (.objEq z y) ps) z p0026
  have p0028 :=
    @g_ax9v z y
      (by
        first
        | (aesop))
  have p0029 := @g_con3 (.objEq z y) ps
  have p0030 := @g_al2imi (.imp (.objEq z y) ps) (.neg ps) (.neg (.objEq z y)) z p0029
  have p0031 :=
    @g_mtoi (.all z (.imp (.objEq z y) ps)) (.all z (.neg ps))
      (.all z (.neg (.objEq z y))) p0028 p0030
  have p0032 :=
    @g_syl (.all z (.imp (.objEq z y) ph)) (.all z (.imp (.objEq z y) ps))
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
  have p0034 := @g_nsyl2 (.all z (.imp (.objEq z y) ph)) (.all z (.neg ps)) ps p0032 p0033
  have p0035 := @g_alimi (.all z (.imp (.objEq z y) ph)) ps x p0034
  have p0036 :=
    @g_syl56 ps (.all z (.imp (.objEq z y) ph))
      (syn_wa (.neg (.all x (.objEq x z))) (.neg (.all x (.objEq x y))))
      (.all x (.all z (.imp (.objEq z y) ph))) (.all x ps) p0007 p0024 p0035
  have p0037 :=
    @g_expcom (.neg (.all x (.objEq x z))) (.neg (.all x (.objEq x y)))
      (.imp ps (.all x ps)) p0036
  have p0038 := @g_sp (.objEq x z) x
  have p0039 := Nominal.ax11Structural x z ps
  have p0040 :=
    @g_syl2im (.all x (.objEq x z)) (.objEq x z) ps (.all z ps)
      (.all x (.imp (.objEq x z) ps)) p0038 p0000 p0039
  have p0041 := @g_pm2_27 (.objEq x z) ps
  have p0042 := @g_al2imi (.objEq x z) (.imp (.objEq x z) ps) ps x p0041
  have p0043 :=
    @g_syld (.all x (.objEq x z)) ps (.all x (.imp (.objEq x z) ps)) (.all x ps) p0040
      p0042
  have p0044 :=
    @g_pm2_61d2 (.neg (.all x (.objEq x y))) (.all x (.objEq x z)) (.imp ps (.all x ps))
      p0037 p0043
  exact p0044

@[expose]
noncomputable def g_dveeq2 (x : Var) (y : Var) (z : Var) (dv_x_z : x ≠ z) :
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
  have p0000 := @g_equequ2 w y z
  have p0001 :=
    @g_dvelimv (.objEq z w) (.objEq z y) x y w
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

@[expose]
noncomputable def g_ax10lem4 (x : Var) (y : Var) (w : Var) (dv_w_x : w ≠ x)
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
    @g_ax10lem1 x y w
      (by
        first
        | (aesop))
      (by
        first
        | (aesop))
  have p0001 := @g_equequ1 z x w
  have p0002 :=
    @g_dvelimv (.objEq z w) (.objEq x w) y x z
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
  have p0003 := @g_hba1 (.objEq x w) y
  have p0004 := @g_equequ2 x w y
  have p0005 := @g_sps (.objEq x w) (syn_wb (.objEq y x) (.objEq y w)) y p0004
  have p0006 := @g_albidh (.all y (.objEq x w)) (.objEq y x) (.objEq y w) y p0003 p0005
  have p0007 :=
    @g_biimprd (.all y (.objEq x w)) (.all y (.objEq y x)) (.all y (.objEq y w)) p0006
  have p0008 :=
    @g_syl6 (.neg (.all y (.objEq y x))) (.objEq x w) (.all y (.objEq x w))
      (.imp (.all y (.objEq y w)) (.all y (.objEq y x))) p0002 p0007
  have p0009 :=
    @g_syl7 (.all x (.objEq x w)) (.all y (.objEq y w)) (.neg (.all y (.objEq y x)))
      (.objEq x w) (.all y (.objEq y x)) p0000 p0008
  have p0010 :=
    @g_spsd (.neg (.all y (.objEq y x))) (.objEq x w)
      (.imp (.all x (.objEq x w)) (.all y (.objEq y x))) x p0009
  have p0011 :=
    @g_pm2_43d (.neg (.all y (.objEq y x))) (.all x (.objEq x w)) (.all y (.objEq y x))
      p0010
  have p0012 :=
    @g_com12 (.neg (.all y (.objEq y x))) (.all x (.objEq x w)) (.all y (.objEq y x))
      p0011
  have p0013 := @g_pm2_18d (.all x (.objEq x w)) (.all y (.objEq y x)) p0012
  exact p0013

@[expose]
noncomputable def g_ax10lem5 (x : Var) (y : Var) (z : Var) (w : Var) (dv_w_z : w ≠ z) :
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
    @g_ax10lem1 z v w
      (by
        first
        | (aesop))
      (by
        first
        | (aesop))
  have p0001 :=
    @g_ax10lem4 v u w
      (by
        first
        | (aesop))
      (by
        first
        | (aesop))
  have p0002 :=
    @g_syl (.all z (.objEq z w)) (.all v (.objEq v w)) (.all u (.objEq u v)) p0000 p0001
  have p0003 :=
    @g_ax10lem1 u x v
      (by
        first
        | (aesop))
      (by
        first
        | (aesop))
  have p0004 :=
    @g_syl (.all z (.objEq z w)) (.all u (.objEq u v)) (.all x (.objEq x v)) p0002 p0003
  have p0005 :=
    @g_ax10lem4 x y v
      (by
        first
        | (aesop))
      (by
        first
        | (aesop))
  have p0006 :=
    @g_syl (.all z (.objEq z w)) (.all x (.objEq x v)) (.all y (.objEq y x)) p0004 p0005
  exact p0006

@[expose]
noncomputable def g_ax10lem6 (ph : Wff) (x : Var) (y : Var) :
    Nominal.NPrf (.imp (.all y (.objEq y x)) (.imp (.all x ph) (.all y ph))) :=
  by
  have p0000 := Nominal.ax11Structural y x ph
  have p0001 :=
    @g_sps (.objEq y x) (.imp (.all x ph) (.all y (.imp (.objEq y x) ph))) y p0000
  have p0002 := @g_pm2_27 (.objEq y x) ph
  have p0003 := @g_al2imi (.objEq y x) (.imp (.objEq y x) ph) ph y p0002
  have p0004 :=
    @g_syld (.all y (.objEq y x)) (.all x ph) (.all y (.imp (.objEq y x) ph)) (.all y ph)
      p0001 p0003
  exact p0004

@[expose]
noncomputable def g_ax10 (x : Var) (y : Var) :
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
    @g_ax9v z x
      (by
        first
        | (aesop))
  have p0001 := (Nominal.biimpRefl (syn_wex z (.objEq z x)))
  have p0002 :=
    @g_dveeq2 y x z
      (by
        first
        | (aesop))
  have p0003 :=
    @g_imp (.neg (.all y (.objEq y x))) (.objEq z x) (.all y (.objEq z x)) p0002
  have p0004 := @g_ax10lem6 (.objEq z x) y x
  have p0005 := @g_equcomi z x
  have p0006 := @g_alimi (.objEq z x) (.objEq x z) x p0005
  have p0007 :=
    @g_syl6 (.all x (.objEq x y)) (.all y (.objEq z x)) (.all x (.objEq z x))
      (.all x (.objEq x z)) p0004 p0006
  have p0008 :=
    @g_ax10lem5 x y x z
      (by
        first
        | (aesop))
  have p0009 :=
    @g_syl56 (syn_wa (.neg (.all y (.objEq y x))) (.objEq z x)) (.all y (.objEq z x))
      (.all x (.objEq x y)) (.all x (.objEq x z)) (.all y (.objEq y x)) p0003 p0007 p0008
  have p0010 :=
    @g_exp3acom23 (.all x (.objEq x y)) (.neg (.all y (.objEq y x))) (.objEq z x)
      (.all y (.objEq y x)) p0009
  have p0011 := @g_pm2_18 (.all y (.objEq y x))
  have p0012 :=
    @g_syl6 (.all x (.objEq x y)) (.objEq z x)
      (.imp (.neg (.all y (.objEq y x))) (.all y (.objEq y x))) (.all y (.objEq y x))
      p0010 p0011
  have p0013 :=
    @g_exlimdv (.all x (.objEq x y)) (.objEq z x) (.all y (.objEq y x)) z
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
    @g_syl5bir (.neg (.all z (.neg (.objEq z x)))) (syn_wex z (.objEq z x))
      (.all x (.objEq x y)) (.all y (.objEq y x)) p0001 p0013
  have p0015 :=
    @g_mpi (.all x (.objEq x y)) (.neg (.all z (.neg (.objEq z x)))) (.all y (.objEq y x))
      p0000 p0014
  exact p0015

@[expose]
noncomputable def g_a16g (ph : Wff) (x : Var) (y : Var) (z : Var) (dv_x_y : x ≠ y) :
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
    @g_a9ev w z
      (by
        first
        | (aesop))
  have p0001 :=
    @g_ax10lem5 z w x y
      (by
        first
        | (aesop))
  have p0002 := @g_hbn1 (.objEq w z) w
  have p0003 := @g_pm2_21 (.all w (.objEq w z)) (.imp ph (.all z ph))
  have p0004 :=
    @g_alrimih (.neg (.all w (.objEq w z)))
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
    @g_alrimih (.imp ph (.all z ph)) (.imp (.all w (.objEq w z)) (.imp ph (.all z ph))) w
      p0005 p0006
  have p0008 :=
    @g_ja (.all w (.objEq w z)) (.imp ph (.all z ph))
      (.all w (.imp (.all w (.objEq w z)) (.imp ph (.all z ph)))) p0004 p0007
  have p0009 :=
    @g_ax10lem5 w z w z
      (by
        first
        | (aesop))
  have p0010 := @g_equcomi w z
  have p0011 :=
    Nominal.ax17 ph w
      (by
        first
        | (aesop))
  have p0012 := Nominal.ax11Structural z w ph
  have p0013 :=
    @g_syl2im (.objEq w z) (.objEq z w) ph (.all w ph) (.all z (.imp (.objEq z w) ph))
      p0010 p0011 p0012
  have p0014 := Nominal.ax5 z (.objEq z w) ph
  have p0015 :=
    @g_syl6 (.objEq w z) ph (.all z (.imp (.objEq z w) ph))
      (.imp (.all z (.objEq z w)) (.all z ph)) p0013 p0014
  have p0016 := @g_com23 (.objEq w z) ph (.all z (.objEq z w)) (.all z ph) p0015
  have p0017 :=
    @g_syl5 (.all w (.objEq w z)) (.all z (.objEq z w)) (.objEq w z) (.imp ph (.all z ph))
      p0009 p0016
  have p0018 :=
    @g_exlimih (.objEq w z) (.imp (.all w (.objEq w z)) (.imp ph (.all z ph))) w p0008
      p0017
  have p0019 :=
    @g_mpsyl (syn_wex w (.objEq w z)) (.all x (.objEq x y)) (.all w (.objEq w z))
      (.imp ph (.all z ph)) p0000 p0001 p0018
  exact p0019

@[expose]
noncomputable def g_aecom (x : Var) (y : Var) :
    Nominal.NPrf (.imp (.all x (.objEq x y)) (.all y (.objEq y x))) :=
  by
  have p0000 := @g_ax10 x y
  exact p0000

@[expose]
noncomputable def g_aecoms (ph : Wff) (x : Var) (y : Var)
    (hyp_alequcoms_1 : Nominal.NPrf (.imp (.all x (.objEq x y)) ph)) :
    Nominal.NPrf (.imp (.all y (.objEq y x)) ph) :=
  by
  have p0000 := @g_aecom y x
  have p0001 :=
    @g_syl (.all y (.objEq y x)) (.all x (.objEq x y)) ph p0000 hyp_alequcoms_1
  exact p0001

@[expose]
noncomputable def g_ax9 (x : Var) (y : Var) :
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
  have p0000 := @g_sp (.neg (.objEq x y)) x
  have p0001 := @g_sp (.objEq x y) x
  have p0002 :=
    @g_nsyl3 (.all x (.neg (.objEq x y))) (.objEq x y) (.all x (.objEq x y)) p0000 p0001
  have p0003 :=
    @g_ax9v v y
      (by
        first
        | (aesop))
  have p0004 :=
    @g_dveeq2 x y v
      (by
        first
        | (aesop))
  have p0005 :=
    @g_ax9v x v
      (by
        first
        | (aesop))
  have p0006 := @g_hba1 (.objEq v y) x
  have p0007 := @g_sp (.objEq v y) x
  have p0008 := @g_equequ2 v y x
  have p0009 :=
    @g_syl (.all x (.objEq v y)) (.objEq v y) (syn_wb (.objEq x v) (.objEq x y)) p0007
      p0008
  have p0010 := @g_notbid (.all x (.objEq v y)) (.objEq x v) (.objEq x y) p0009
  have p0011 :=
    @g_albidh (.all x (.objEq v y)) (.neg (.objEq x v)) (.neg (.objEq x y)) x p0006 p0010
  have p0012 :=
    @g_mtbii (.all x (.objEq v y)) (.all x (.neg (.objEq x v)))
      (.all x (.neg (.objEq x y))) p0005 p0011
  have p0013 :=
    @g_syl6com (.neg (.all x (.objEq x y))) (.objEq v y) (.all x (.objEq v y))
      (.neg (.all x (.neg (.objEq x y)))) p0004 p0012
  have p0014 :=
    @g_con3i (.objEq v y)
      (.imp (.neg (.all x (.objEq x y))) (.neg (.all x (.neg (.objEq x y))))) p0013
  have p0015 :=
    @g_alrimiv
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
    @g_mt3 (.imp (.neg (.all x (.objEq x y))) (.neg (.all x (.neg (.objEq x y)))))
      (.all v (.neg (.objEq v y))) p0003 p0015
  have p0017 :=
    @g_pm2_61i (.all x (.objEq x y)) (.neg (.all x (.neg (.objEq x y)))) p0002 p0016
  exact p0017

@[expose]
noncomputable def g_ax9o (ph : Wff) (x : Var) (y : Var) :
    Nominal.NPrf (.imp (.all x (.imp (.objEq x y) (.all x ph))) ph) :=
  by
  have p0000 := @g_ax9 x y
  have p0001 := @g_con3 (.objEq x y) (.all x ph)
  have p0002 :=
    @g_al2imi (.imp (.objEq x y) (.all x ph)) (.neg (.all x ph)) (.neg (.objEq x y)) x
      p0001
  have p0003 :=
    @g_mtoi (.all x (.imp (.objEq x y) (.all x ph))) (.all x (.neg (.all x ph)))
      (.all x (.neg (.objEq x y))) p0000 p0002
  have p0004 := @g_ax6o ph x
  have p0005 :=
    @g_syl (.all x (.imp (.objEq x y) (.all x ph))) (.neg (.all x (.neg (.all x ph)))) ph
      p0003 p0004
  exact p0005

@[expose]
noncomputable def g_a9e (x : Var) (y : Var) : Nominal.NPrf (syn_wex x (.objEq x y)) :=
  by
  have p0000 := @g_ax9 x y
  have p0001 := (Nominal.biimpRefl (syn_wex x (.objEq x y)))
  have p0002 :=
    @g_mpbir (syn_wex x (.objEq x y)) (.neg (.all x (.neg (.objEq x y)))) p0000 p0001
  exact p0002

@[expose]
noncomputable def g_ax10o (ph : Wff) (x : Var) (y : Var) :
    Nominal.NPrf (.imp (.all x (.objEq x y)) (.imp (.all x ph) (.all y ph))) :=
  by
  have p0000 := @g_ax10 x y
  have p0001 := Nominal.ax11Structural y x ph
  have p0002 := @g_equcoms (.imp (.all x ph) (.all y (.imp (.objEq y x) ph))) y x p0001
  have p0003 :=
    @g_sps (.objEq x y) (.imp (.all x ph) (.all y (.imp (.objEq y x) ph))) x p0002
  have p0004 := @g_pm2_27 (.objEq y x) ph
  have p0005 := @g_al2imi (.objEq y x) (.imp (.objEq y x) ph) ph y p0004
  have p0006 :=
    @g_sylsyld (.all x (.objEq x y)) (.all y (.objEq y x)) (.all x ph)
      (.all y (.imp (.objEq y x) ph)) (.all y ph) p0000 p0003 p0005
  exact p0006


end NFChoice.DirectNominalPrf.WPPReplay
