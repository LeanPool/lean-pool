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

@[expose]
noncomputable def g_hbae (x : Var) (y : Var) (z : Var) :
    Nominal.NPrf (.imp (.all x (.objEq x y)) (.all z (.all x (.objEq x y)))) :=
  by
  have p0000 := @g_sp (.objEq x y) x
  have p0001 := @g_ax12o x y z
  have p0002 :=
    @g_syl7 (.all x (.objEq x y)) (.objEq x y) (.neg (.all z (.objEq z x)))
      (.neg (.all z (.objEq z y))) (.all z (.objEq x y)) p0000 p0001
  have p0003 := @g_ax10o (.objEq x y) x z
  have p0004 := @g_aecoms (.imp (.all x (.objEq x y)) (.all z (.objEq x y))) x z p0003
  have p0005 := @g_ax10o (.objEq x y) x y
  have p0006 := @g_pm2_43i (.all x (.objEq x y)) (.all y (.objEq x y)) p0005
  have p0007 := @g_ax10o (.objEq x y) y z
  have p0008 :=
    @g_syl5 (.all x (.objEq x y)) (.all y (.objEq x y)) (.all y (.objEq y z))
      (.all z (.objEq x y)) p0006 p0007
  have p0009 := @g_aecoms (.imp (.all x (.objEq x y)) (.all z (.objEq x y))) y z p0008
  have p0010 :=
    @g_pm2_61ii (.all z (.objEq z x)) (.all z (.objEq z y))
      (.imp (.all x (.objEq x y)) (.all z (.objEq x y))) p0002 p0004 p0009
  have p0011 := @g_a5i (.objEq x y) (.all z (.objEq x y)) x p0010
  have p0012 := Nominal.ax7Structural x z (.objEq x y)
  have p0013 :=
    @g_syl (.all x (.objEq x y)) (.all x (.all z (.objEq x y)))
      (.all z (.all x (.objEq x y))) p0011 p0012
  exact p0013

@[expose]
noncomputable def g_nfae (x : Var) (y : Var) (z : Var) :
    Nominal.NPrf (syn_wnf z (.all x (.objEq x y))) :=
  by
  have p0000 := @g_hbae x y z
  have p0001 := @g_nfi (.all x (.objEq x y)) z p0000
  exact p0001

@[expose]
noncomputable def g_nfnae (x : Var) (y : Var) (z : Var) :
    Nominal.NPrf (syn_wnf z (.neg (.all x (.objEq x y)))) :=
  by
  have p0000 := @g_nfae x y z
  have p0001 := @g_nfn (.all x (.objEq x y)) z p0000
  exact p0001

@[expose]
noncomputable def g_nfeqf (x : Var) (y : Var) (z : Var) :
    Nominal.NPrf
      (.imp (syn_wa (.neg (.all z (.objEq z x))) (.neg (.all z (.objEq z y))))
        (syn_wnf z (.objEq x y))) :=
  by
  have p0000 := @g_nfnae z x z
  have p0001 := @g_nfnae z y z
  have p0002 :=
    @g_nfan (.neg (.all z (.objEq z x))) (.neg (.all z (.objEq z y))) z p0000 p0001
  have p0003 := @g_ax12o x y z
  have p0004 :=
    @g_imp (.neg (.all z (.objEq z x))) (.neg (.all z (.objEq z y)))
      (.imp (.objEq x y) (.all z (.objEq x y))) p0003
  have p0005 :=
    @g_nfd (syn_wa (.neg (.all z (.objEq z x))) (.neg (.all z (.objEq z y)))) (.objEq x y)
      z p0002 p0004
  exact p0005

@[expose]
noncomputable def g_equs4 (ph : Wff) (x : Var) (y : Var) :
    Nominal.NPrf
      (.imp (.all x (.imp (.objEq x y) ph)) (syn_wex x (syn_wa (.objEq x y) ph))) :=
  by
  have p0000 := @g_a9e x y
  have p0001 := @g_n_19_29 (.imp (.objEq x y) ph) (.objEq x y) x
  have p0002 :=
    @g_mpan2 (.all x (.imp (.objEq x y) ph)) (syn_wex x (.objEq x y))
      (syn_wex x (syn_wa (.imp (.objEq x y) ph) (.objEq x y))) p0000 p0001
  have p0003 := @g_ancl (.objEq x y) ph
  have p0004 := @g_imp (.imp (.objEq x y) ph) (.objEq x y) (syn_wa (.objEq x y) ph) p0003
  have p0005 :=
    @g_eximi (syn_wa (.imp (.objEq x y) ph) (.objEq x y)) (syn_wa (.objEq x y) ph) x p0004
  have p0006 :=
    @g_syl (.all x (.imp (.objEq x y) ph))
      (syn_wex x (syn_wa (.imp (.objEq x y) ph) (.objEq x y)))
      (syn_wex x (syn_wa (.objEq x y) ph)) p0002 p0005
  exact p0006

@[expose]
noncomputable def g_equsal (ph : Wff) (ps : Wff) (x : Var) (y : Var)
    (hyp_equsal_1 : Nominal.NPrf (syn_wnf x ps))
    (hyp_equsal_2 : Nominal.NPrf (.imp (.objEq x y) (syn_wb ph ps))) :
    Nominal.NPrf (syn_wb (.all x (.imp (.objEq x y) ph)) ps) :=
  by
  have p0000 := @g_n_19_3 ps x hyp_equsal_1
  have p0001 := @g_syl6bbr (.objEq x y) ph ps (.all x ps) hyp_equsal_2 p0000
  have p0002 := @g_pm5_74i (.objEq x y) ph (.all x ps) p0001
  have p0003 := @g_albii (.imp (.objEq x y) ph) (.imp (.objEq x y) (.all x ps)) x p0002
  have p0004 := @g_nfri ps x hyp_equsal_1
  have p0005 := @g_a1d ps (.all x ps) (.objEq x y) p0004
  have p0006 := @g_alrimi ps (.imp (.objEq x y) (.all x ps)) x hyp_equsal_1 p0005
  have p0007 := @g_ax9o ps x y
  have p0008 := @g_impbii ps (.all x (.imp (.objEq x y) (.all x ps))) p0006 p0007
  have p0009 :=
    @g_bitr4i (.all x (.imp (.objEq x y) ph)) (.all x (.imp (.objEq x y) (.all x ps))) ps
      p0003 p0008
  exact p0009

@[expose]
noncomputable def g_equsex (ph : Wff) (ps : Wff) (x : Var) (y : Var)
    (hyp_equsex_1 : Nominal.NPrf (syn_wnf x ps))
    (hyp_equsex_2 : Nominal.NPrf (.imp (.objEq x y) (syn_wb ph ps))) :
    Nominal.NPrf (syn_wb (syn_wex x (syn_wa (.objEq x y) ph)) ps) :=
  by
  have p0000 := @g_exnal (.imp (.objEq x y) (.neg ph)) x
  have p0001 := (Nominal.biimpRefl (syn_wa (.objEq x y) ph))
  have p0002 :=
    @g_exbii (syn_wa (.objEq x y) ph) (.neg (.imp (.objEq x y) (.neg ph))) x p0001
  have p0003 := @g_nfn ps x hyp_equsex_1
  have p0004 := @g_notbid (.objEq x y) ph ps hyp_equsex_2
  have p0005 := @g_equsal (.neg ph) (.neg ps) x y p0003 p0004
  have p0006 := @g_con2bii (.all x (.imp (.objEq x y) (.neg ph))) ps p0005
  have p0007 :=
    @g_n_3bitr4i (syn_wex x (.neg (.imp (.objEq x y) (.neg ph))))
      (.neg (.all x (.imp (.objEq x y) (.neg ph)))) (syn_wex x (syn_wa (.objEq x y) ph))
      ps p0000 p0002 p0006
  exact p0007

@[expose]
noncomputable def g_dral1 (ph : Wff) (ps : Wff) (x : Var) (y : Var)
    (hyp_dral1_1 : Nominal.NPrf (.imp (.all x (.objEq x y)) (syn_wb ph ps))) :
    Nominal.NPrf (.imp (.all x (.objEq x y)) (syn_wb (.all x ph) (.all y ps))) :=
  by
  have p0000 := @g_hbae x y x
  have p0001 := @g_biimpd (.all x (.objEq x y)) ph ps hyp_dral1_1
  have p0002 := @g_alimdh (.all x (.objEq x y)) ph ps x p0000 p0001
  have p0003 := @g_ax10o ps x y
  have p0004 :=
    @g_syld (.all x (.objEq x y)) (.all x ph) (.all x ps) (.all y ps) p0002 p0003
  have p0005 := @g_hbae x y y
  have p0006 := @g_biimprd (.all x (.objEq x y)) ph ps hyp_dral1_1
  have p0007 := @g_alimdh (.all x (.objEq x y)) ps ph y p0005 p0006
  have p0008 := @g_ax10o ph y x
  have p0009 := @g_aecoms (.imp (.all y ph) (.all x ph)) y x p0008
  have p0010 :=
    @g_syld (.all x (.objEq x y)) (.all y ps) (.all y ph) (.all x ph) p0007 p0009
  have p0011 := @g_impbid (.all x (.objEq x y)) (.all x ph) (.all y ps) p0004 p0010
  exact p0011

@[expose]
noncomputable def g_dral2 (ph : Wff) (ps : Wff) (x : Var) (y : Var) (z : Var)
    (hyp_dral1_1 : Nominal.NPrf (.imp (.all x (.objEq x y)) (syn_wb ph ps))) :
    Nominal.NPrf (.imp (.all x (.objEq x y)) (syn_wb (.all z ph) (.all z ps))) :=
  by
  have p0000 := @g_hbae x y z
  have p0001 := @g_albidh (.all x (.objEq x y)) ph ps z p0000 hyp_dral1_1
  exact p0001

@[expose]
noncomputable def g_drex1 (ph : Wff) (ps : Wff) (x : Var) (y : Var)
    (hyp_dral1_1 : Nominal.NPrf (.imp (.all x (.objEq x y)) (syn_wb ph ps))) :
    Nominal.NPrf (.imp (.all x (.objEq x y)) (syn_wb (syn_wex x ph) (syn_wex y ps))) :=
  by
  have p0000 := @g_notbid (.all x (.objEq x y)) ph ps hyp_dral1_1
  have p0001 := @g_dral1 (.neg ph) (.neg ps) x y p0000
  have p0002 :=
    @g_notbid (.all x (.objEq x y)) (.all x (.neg ph)) (.all y (.neg ps)) p0001
  have p0003 := (Nominal.biimpRefl (syn_wex x ph))
  have p0004 := (Nominal.biimpRefl (syn_wex y ps))
  have p0005 :=
    @g_n_3bitr4g (.all x (.objEq x y)) (.neg (.all x (.neg ph))) (.neg (.all y (.neg ps)))
      (syn_wex x ph) (syn_wex y ps) p0002 p0003 p0004
  exact p0005

@[expose]
noncomputable def g_drnf1 (ph : Wff) (ps : Wff) (x : Var) (y : Var)
    (hyp_dral1_1 : Nominal.NPrf (.imp (.all x (.objEq x y)) (syn_wb ph ps))) :
    Nominal.NPrf (.imp (.all x (.objEq x y)) (syn_wb (syn_wnf x ph) (syn_wnf y ps))) :=
  by
  have p0000 := @g_dral1 ph ps x y hyp_dral1_1
  have p0001 :=
    @g_imbi12d (.all x (.objEq x y)) ph ps (.all x ph) (.all y ps) hyp_dral1_1 p0000
  have p0002 := @g_dral1 (.imp ph (.all x ph)) (.imp ps (.all y ps)) x y p0001
  have p0003 := (Nominal.biimpRefl (syn_wnf x ph))
  have p0004 := (Nominal.biimpRefl (syn_wnf y ps))
  have p0005 :=
    @g_n_3bitr4g (.all x (.objEq x y)) (.all x (.imp ph (.all x ph)))
      (.all y (.imp ps (.all y ps))) (syn_wnf x ph) (syn_wnf y ps) p0002 p0003 p0004
  exact p0005

@[expose]
noncomputable def g_drnf2 (ph : Wff) (ps : Wff) (x : Var) (y : Var) (z : Var)
    (hyp_dral1_1 : Nominal.NPrf (.imp (.all x (.objEq x y)) (syn_wb ph ps))) :
    Nominal.NPrf (.imp (.all x (.objEq x y)) (syn_wb (syn_wnf z ph) (syn_wnf z ps))) :=
  by
  have p0000 := @g_dral2 ph ps x y z hyp_dral1_1
  have p0001 :=
    @g_imbi12d (.all x (.objEq x y)) ph ps (.all z ph) (.all z ps) hyp_dral1_1 p0000
  have p0002 := @g_dral2 (.imp ph (.all z ph)) (.imp ps (.all z ps)) x y z p0001
  have p0003 := (Nominal.biimpRefl (syn_wnf z ph))
  have p0004 := (Nominal.biimpRefl (syn_wnf z ps))
  have p0005 :=
    @g_n_3bitr4g (.all x (.objEq x y)) (.all z (.imp ph (.all z ph)))
      (.all z (.imp ps (.all z ps))) (syn_wnf z ph) (syn_wnf z ps) p0002 p0003 p0004
  exact p0005

@[expose]
noncomputable def g_nfald2 (ph : Wff) (ps : Wff) (x : Var) (y : Var)
    (hyp_nfald2_1 : Nominal.NPrf (syn_wnf y ph))
    (hyp_nfald2_2 :
      Nominal.NPrf (.imp (syn_wa ph (.neg (.all x (.objEq x y)))) (syn_wnf x ps))) :
    Nominal.NPrf (.imp ph (syn_wnf x (.all y ps))) :=
  by
  have p0000 := @g_nfnae x y y
  have p0001 := @g_nfan ph (.neg (.all x (.objEq x y))) y hyp_nfald2_1 p0000
  have p0002 :=
    @g_nfald (syn_wa ph (.neg (.all x (.objEq x y)))) ps x y p0001 hyp_nfald2_2
  have p0003 := @g_ex ph (.neg (.all x (.objEq x y))) (syn_wnf x (.all y ps)) p0002
  have p0004 := @g_nfa1 ps y
  have p0005 := @g_biidd (.all x (.objEq x y)) (.all y ps)
  have p0006 := @g_drnf1 (.all y ps) (.all y ps) x y p0005
  have p0007 :=
    @g_mpbiri (.all x (.objEq x y)) (syn_wnf x (.all y ps)) (syn_wnf y (.all y ps)) p0004
      p0006
  have p0008 := @g_pm2_61d2 ph (.all x (.objEq x y)) (syn_wnf x (.all y ps)) p0003 p0007
  exact p0008

@[expose]
noncomputable def g_nfexd2 (ph : Wff) (ps : Wff) (x : Var) (y : Var)
    (hyp_nfald2_1 : Nominal.NPrf (syn_wnf y ph))
    (hyp_nfald2_2 :
      Nominal.NPrf (.imp (syn_wa ph (.neg (.all x (.objEq x y)))) (syn_wnf x ps))) :
    Nominal.NPrf (.imp ph (syn_wnf x (syn_wex y ps))) :=
  by
  have p0000 := (Nominal.biimpRefl (syn_wex y ps))
  have p0001 := @g_nfnd (syn_wa ph (.neg (.all x (.objEq x y)))) ps x hyp_nfald2_2
  have p0002 := @g_nfald2 ph (.neg ps) x y hyp_nfald2_1 p0001
  have p0003 := @g_nfnd ph (.all y (.neg ps)) x p0002
  have p0004 := @g_nfxfrd (syn_wex y ps) (.neg (.all y (.neg ps))) ph x p0000 p0003
  exact p0004

@[expose]
noncomputable def g_spimt (ph : Wff) (ps : Wff) (x : Var) (y : Var) :
    Nominal.NPrf
      (.imp (syn_wa (syn_wnf x ps) (.all x (.imp (.objEq x y) (.imp ph ps))))
        (.imp (.all x ph) ps)) :=
  by
  have p0000 := @g_nfnf1 ps x
  have p0001 := @g_nfa1 ph x
  have p0002 := @g_nfan (syn_wnf x ps) (.all x ph) x p0000 p0001
  have p0003 := @g_sp ph x
  have p0004 := @g_adantl (.all x ph) ph (syn_wnf x ps) p0003
  have p0005 := @g_nfr ps x
  have p0006 := @g_adantr (syn_wnf x ps) (.imp ps (.all x ps)) (.all x ph) p0005
  have p0007 :=
    @g_embantd (syn_wa (syn_wnf x ps) (.all x ph)) ph ps (.all x ps) p0004 p0006
  have p0008 :=
    @g_imim2d (syn_wa (syn_wnf x ps) (.all x ph)) (.imp ph ps) (.all x ps) (.objEq x y)
      p0007
  have p0009 :=
    @g_alimd (syn_wa (syn_wnf x ps) (.all x ph)) (.imp (.objEq x y) (.imp ph ps))
      (.imp (.objEq x y) (.all x ps)) x p0002 p0008
  have p0010 :=
    @g_impancom (syn_wnf x ps) (.all x ph) (.all x (.imp (.objEq x y) (.imp ph ps)))
      (.all x (.imp (.objEq x y) (.all x ps))) p0009
  have p0011 := @g_ax9o ps x y
  have p0012 :=
    @g_syl6 (syn_wa (syn_wnf x ps) (.all x (.imp (.objEq x y) (.imp ph ps)))) (.all x ph)
      (.all x (.imp (.objEq x y) (.all x ps))) ps p0010 p0011
  exact p0012

@[expose]
noncomputable def g_spim (ph : Wff) (ps : Wff) (x : Var) (y : Var)
    (hyp_spim_1 : Nominal.NPrf (syn_wnf x ps))
    (hyp_spim_2 : Nominal.NPrf (.imp (.objEq x y) (.imp ph ps))) :
    Nominal.NPrf (.imp (.all x ph) ps) :=
  by
  have p0000 := Nominal.gen hyp_spim_2 x
  have p0001 := @g_spimt ph ps x y
  have p0002 :=
    @g_mp2an (syn_wnf x ps) (.all x (.imp (.objEq x y) (.imp ph ps)))
      (.imp (.all x ph) ps) hyp_spim_1 p0000 p0001
  exact p0002

@[expose]
noncomputable def g_spime (ph : Wff) (ps : Wff) (x : Var) (y : Var)
    (hyp_spime_1 : Nominal.NPrf (syn_wnf x ph))
    (hyp_spime_2 : Nominal.NPrf (.imp (.objEq x y) (.imp ph ps))) :
    Nominal.NPrf (.imp ph (syn_wex x ps)) :=
  by
  have p0000 := @g_nfn ph x hyp_spime_1
  have p0001 := @g_con3d (.objEq x y) ph ps hyp_spime_2
  have p0002 := @g_spim (.neg ps) (.neg ph) x y p0000 p0001
  have p0003 := @g_con2i (.all x (.neg ps)) ph p0002
  have p0004 := (Nominal.biimpRefl (syn_wex x ps))
  have p0005 := @g_sylibr ph (.neg (.all x (.neg ps))) (syn_wex x ps) p0003 p0004
  exact p0005

@[expose]
noncomputable def g_spimed (ph : Wff) (ps : Wff) (ch : Wff) (x : Var) (y : Var)
    (hyp_spimed_1 : Nominal.NPrf (.imp ch (syn_wnf x ph)))
    (hyp_spimed_2 : Nominal.NPrf (.imp (.objEq x y) (.imp ph ps))) :
    Nominal.NPrf (.imp ch (.imp ph (syn_wex x ps))) :=
  by
  have p0000 := @g_nfnf1 ph x
  have p0001 := @g_id (syn_wnf x ph)
  have p0002 := @g_nfan1 (syn_wnf x ph) ph x p0000 p0001
  have p0003 := @g_adantld (.objEq x y) ph ps (syn_wnf x ph) hyp_spimed_2
  have p0004 := @g_spime (syn_wa (syn_wnf x ph) ph) ps x y p0002 p0003
  have p0005 := @g_ex (syn_wnf x ph) ph (syn_wex x ps) p0004
  have p0006 := @g_syl ch (syn_wnf x ph) (.imp ph (syn_wex x ps)) hyp_spimed_1 p0005
  exact p0006

@[expose]
noncomputable def g_cbv1h (ph : Wff) (ps : Wff) (ch : Wff) (x : Var) (y : Var)
    (hyp_cbv1h_1 : Nominal.NPrf (.imp ph (.imp ps (.all y ps))))
    (hyp_cbv1h_2 : Nominal.NPrf (.imp ph (.imp ch (.all x ch))))
    (hyp_cbv1h_3 : Nominal.NPrf (.imp ph (.imp (.objEq x y) (.imp ps ch)))) :
    Nominal.NPrf (.imp (.all x (.all y ph)) (.imp (.all x ps) (.all y ch))) :=
  by
  have p0000 := @g_sps ph (.imp ps (.all y ps)) y hyp_cbv1h_1
  have p0001 := @g_al2imi (.all y ph) ps (.all y ps) x p0000
  have p0002 := Nominal.ax7Structural x y ps
  have p0003 :=
    @g_syl6 (.all x (.all y ph)) (.all x ps) (.all x (.all y ps)) (.all y (.all x ps))
      p0001 p0002
  have p0004 := @g_com23 ph (.objEq x y) ps ch hyp_cbv1h_3
  have p0005 := @g_syl6d ph ps (.objEq x y) ch (.all x ch) p0004 hyp_cbv1h_2
  have p0006 := @g_al2imi ph ps (.imp (.objEq x y) (.all x ch)) x p0005
  have p0007 := @g_ax9o ch x y
  have p0008 :=
    @g_syl6 (.all x ph) (.all x ps) (.all x (.imp (.objEq x y) (.all x ch))) ch p0006
      p0007
  have p0009 := @g_al2imi (.all x ph) (.all x ps) ch y p0008
  have p0010 := @g_a7s ph (.imp (.all y (.all x ps)) (.all y ch)) y x p0009
  have p0011 :=
    @g_syld (.all x (.all y ph)) (.all x ps) (.all y (.all x ps)) (.all y ch) p0003 p0010
  exact p0011

@[expose]
noncomputable def g_cbv1 (ph : Wff) (ps : Wff) (ch : Wff) (x : Var) (y : Var)
    (hyp_cbv1_1 : Nominal.NPrf (.imp ph (syn_wnf y ps)))
    (hyp_cbv1_2 : Nominal.NPrf (.imp ph (syn_wnf x ch)))
    (hyp_cbv1_3 : Nominal.NPrf (.imp ph (.imp (.objEq x y) (.imp ps ch)))) :
    Nominal.NPrf (.imp (.all x (.all y ph)) (.imp (.all x ps) (.all y ch))) :=
  by
  have p0000 := @g_nfrd ph ps y hyp_cbv1_1
  have p0001 := @g_nfrd ph ch x hyp_cbv1_2
  have p0002 := @g_cbv1h ph ps ch x y p0000 p0001 hyp_cbv1_3
  exact p0002

@[expose]
noncomputable def g_cbv2h (ph : Wff) (ps : Wff) (ch : Wff) (x : Var) (y : Var)
    (hyp_cbv2h_1 : Nominal.NPrf (.imp ph (.imp ps (.all y ps))))
    (hyp_cbv2h_2 : Nominal.NPrf (.imp ph (.imp ch (.all x ch))))
    (hyp_cbv2h_3 : Nominal.NPrf (.imp ph (.imp (.objEq x y) (syn_wb ps ch)))) :
    Nominal.NPrf (.imp (.all x (.all y ph)) (syn_wb (.all x ps) (.all y ch))) :=
  by
  have p0000 := @g_bi1 ps ch
  have p0001 := @g_syl6 ph (.objEq x y) (syn_wb ps ch) (.imp ps ch) hyp_cbv2h_3 p0000
  have p0002 := @g_cbv1h ph ps ch x y hyp_cbv2h_1 hyp_cbv2h_2 p0001
  have p0003 := @g_equcomi y x
  have p0004 := @g_bi2 ps ch
  have p0005 :=
    @g_syl56 (.objEq y x) (.objEq x y) ph (syn_wb ps ch) (.imp ch ps) p0003 hyp_cbv2h_3
      p0004
  have p0006 := @g_cbv1h ph ch ps y x hyp_cbv2h_2 hyp_cbv2h_1 p0005
  have p0007 := @g_a7s ph (.imp (.all y ch) (.all x ps)) y x p0006
  have p0008 := @g_impbid (.all x (.all y ph)) (.all x ps) (.all y ch) p0002 p0007
  exact p0008

@[expose]
noncomputable def g_cbv2 (ph : Wff) (ps : Wff) (ch : Wff) (x : Var) (y : Var)
    (hyp_cbv2_1 : Nominal.NPrf (.imp ph (syn_wnf y ps)))
    (hyp_cbv2_2 : Nominal.NPrf (.imp ph (syn_wnf x ch)))
    (hyp_cbv2_3 : Nominal.NPrf (.imp ph (.imp (.objEq x y) (syn_wb ps ch)))) :
    Nominal.NPrf (.imp (.all x (.all y ph)) (syn_wb (.all x ps) (.all y ch))) :=
  by
  have p0000 := @g_nfrd ph ps y hyp_cbv2_1
  have p0001 := @g_nfrd ph ch x hyp_cbv2_2
  have p0002 := @g_cbv2h ph ps ch x y p0000 p0001 hyp_cbv2_3
  exact p0002

@[expose]
noncomputable def g_cbv3 (ph : Wff) (ps : Wff) (x : Var) (y : Var)
    (hyp_cbv3_1 : Nominal.NPrf (syn_wnf y ph)) (hyp_cbv3_2 : Nominal.NPrf (syn_wnf x ps))
    (hyp_cbv3_3 : Nominal.NPrf (.imp (.objEq x y) (.imp ph ps))) :
    Nominal.NPrf (.imp (.all x ph) (.all y ps)) :=
  by
  have p0000 := @g_a1i (syn_wnf y ph) syn_wtru hyp_cbv3_1
  have p0001 := @g_a1i (syn_wnf x ps) syn_wtru hyp_cbv3_2
  have p0002 := @g_a1i (.imp (.objEq x y) (.imp ph ps)) syn_wtru hyp_cbv3_3
  have p0003 := @g_cbv1 syn_wtru ph ps x y p0000 p0001 p0002
  have p0004 := @g_tru
  have p0005 := Nominal.gen p0004 y
  have p0006 := @g_mpg (.all y syn_wtru) (.imp (.all x ph) (.all y ps)) x p0003 p0005
  exact p0006

@[expose]
noncomputable def g_cbv3h (ph : Wff) (ps : Wff) (x : Var) (y : Var)
    (hyp_cbv3h_1 : Nominal.NPrf (.imp ph (.all y ph)))
    (hyp_cbv3h_2 : Nominal.NPrf (.imp ps (.all x ps)))
    (hyp_cbv3h_3 : Nominal.NPrf (.imp (.objEq x y) (.imp ph ps))) :
    Nominal.NPrf (.imp (.all x ph) (.all y ps)) :=
  by
  have p0000 := @g_a1i (.imp ph (.all y ph)) (.objEq y y) hyp_cbv3h_1
  have p0001 := @g_a1i (.imp ps (.all x ps)) (.objEq y y) hyp_cbv3h_2
  have p0002 := @g_a1i (.imp (.objEq x y) (.imp ph ps)) (.objEq y y) hyp_cbv3h_3
  have p0003 := @g_cbv1h (.objEq y y) ph ps x y p0000 p0001 p0002
  have p0004 := @g_stdpc6 y
  have p0005 := @g_mpg (.all y (.objEq y y)) (.imp (.all x ph) (.all y ps)) x p0003 p0004
  exact p0005

@[expose]
noncomputable def g_cbval (ph : Wff) (ps : Wff) (x : Var) (y : Var)
    (hyp_cbval_1 : Nominal.NPrf (syn_wnf y ph))
    (hyp_cbval_2 : Nominal.NPrf (syn_wnf x ps))
    (hyp_cbval_3 : Nominal.NPrf (.imp (.objEq x y) (syn_wb ph ps))) :
    Nominal.NPrf (syn_wb (.all x ph) (.all y ps)) :=
  by
  have p0000 := @g_biimpd (.objEq x y) ph ps hyp_cbval_3
  have p0001 := @g_cbv3 ph ps x y hyp_cbval_1 hyp_cbval_2 p0000
  have p0002 := @g_biimprd (.objEq x y) ph ps hyp_cbval_3
  have p0003 := @g_equcoms (.imp ps ph) x y p0002
  have p0004 := @g_cbv3 ps ph y x hyp_cbval_2 hyp_cbval_1 p0003
  have p0005 := @g_impbii (.all x ph) (.all y ps) p0001 p0004
  exact p0005

@[expose]
noncomputable def g_cbvex (ph : Wff) (ps : Wff) (x : Var) (y : Var)
    (hyp_cbvex_1 : Nominal.NPrf (syn_wnf y ph))
    (hyp_cbvex_2 : Nominal.NPrf (syn_wnf x ps))
    (hyp_cbvex_3 : Nominal.NPrf (.imp (.objEq x y) (syn_wb ph ps))) :
    Nominal.NPrf (syn_wb (syn_wex x ph) (syn_wex y ps)) :=
  by
  have p0000 := @g_nfn ph y hyp_cbvex_1
  have p0001 := @g_nfn ps x hyp_cbvex_2
  have p0002 := @g_notbid (.objEq x y) ph ps hyp_cbvex_3
  have p0003 := @g_cbval (.neg ph) (.neg ps) x y p0000 p0001 p0002
  have p0004 := @g_notbii (.all x (.neg ph)) (.all y (.neg ps)) p0003
  have p0005 := (Nominal.biimpRefl (syn_wex x ph))
  have p0006 := (Nominal.biimpRefl (syn_wex y ps))
  have p0007 :=
    @g_n_3bitr4i (.neg (.all x (.neg ph))) (.neg (.all y (.neg ps))) (syn_wex x ph)
      (syn_wex y ps) p0004 p0005 p0006
  exact p0007

@[expose]
noncomputable def g_chvar (ph : Wff) (ps : Wff) (x : Var) (y : Var)
    (hyp_chvar_1 : Nominal.NPrf (syn_wnf x ps))
    (hyp_chvar_2 : Nominal.NPrf (.imp (.objEq x y) (syn_wb ph ps)))
    (hyp_chvar_3 : Nominal.NPrf ph) : Nominal.NPrf ps :=
  by
  have p0000 := @g_biimpd (.objEq x y) ph ps hyp_chvar_2
  have p0001 := @g_spim ph ps x y hyp_chvar_1 p0000
  have p0002 := @g_mpg ph ps x p0001 hyp_chvar_3
  exact p0002

@[expose]
noncomputable def g_equvini (x : Var) (y : Var) (z : Var) :
    Nominal.NPrf (.imp (.objEq x y) (syn_wex z (syn_wa (.objEq x z) (.objEq z y)))) :=
  by
  have p0000 := @g_equcomi z x
  have p0001 := @g_alimi (.objEq z x) (.objEq x z) z p0000
  have p0002 := @g_a9e z y
  have p0003 :=
    @g_jctir (.all z (.objEq z x)) (.all z (.objEq x z)) (syn_wex z (.objEq z y)) p0001
      p0002
  have p0004 :=
    @g_a1d (.all z (.objEq z x)) (syn_wa (.all z (.objEq x z)) (syn_wex z (.objEq z y)))
      (.objEq x y) p0003
  have p0005 := @g_n_19_29 (.objEq x z) (.objEq z y) z
  have p0006 :=
    @g_syl6 (.all z (.objEq z x)) (.objEq x y)
      (syn_wa (.all z (.objEq x z)) (syn_wex z (.objEq z y)))
      (syn_wex z (syn_wa (.objEq x z) (.objEq z y))) p0004 p0005
  have p0007 := @g_a9e z x
  have p0008 := @g_eximi (.objEq z x) (.objEq x z) z p0000
  have p0009 := Nominal.mp p0007 p0008
  have p0010 :=
    @g_n_2a1i (.all z (.objEq z y)) (.objEq x y) (syn_wex z (.objEq x z)) p0009
  have p0011 :=
    @g_anc2ri (.all z (.objEq z y)) (.objEq x y) (syn_wex z (.objEq x z)) p0010
  have p0012 := @g_n_19_29r (.objEq x z) (.objEq z y) z
  have p0013 :=
    @g_syl6 (.all z (.objEq z y)) (.objEq x y)
      (syn_wa (syn_wex z (.objEq x z)) (.all z (.objEq z y)))
      (syn_wex z (syn_wa (.objEq x z) (.objEq z y))) p0011 p0012
  have p0014 := @g_ioran (.all z (.objEq z x)) (.all z (.objEq z y))
  have p0015 := @g_nfeqf x y z
  have p0016 := Nominal.ax8 x z y
  have p0017 := @g_anc2li (.objEq x z) (.objEq x y) (.objEq z y) p0016
  have p0018 :=
    @g_equcoms (.imp (.objEq x y) (syn_wa (.objEq x z) (.objEq z y))) x z p0017
  have p0019 :=
    @g_spimed (.objEq x y) (syn_wa (.objEq x z) (.objEq z y))
      (syn_wa (.neg (.all z (.objEq z x))) (.neg (.all z (.objEq z y)))) z x p0015 p0018
  have p0020 :=
    @g_sylbi (.neg (syn_wo (.all z (.objEq z x)) (.all z (.objEq z y))))
      (syn_wa (.neg (.all z (.objEq z x))) (.neg (.all z (.objEq z y))))
      (.imp (.objEq x y) (syn_wex z (syn_wa (.objEq x z) (.objEq z y)))) p0014 p0019
  have p0021 :=
    @g_ecase3 (.all z (.objEq z x)) (.all z (.objEq z y))
      (.imp (.objEq x y) (syn_wex z (syn_wa (.objEq x z) (.objEq z y)))) p0006 p0013 p0020
  exact p0021

@[expose]
noncomputable def g_spimv (ph : Wff) (ps : Wff) (x : Var) (y : Var) (dv_ps_x : x ∉ ps.fv)
    (hyp_spimv_1 : Nominal.NPrf (.imp (.objEq x y) (.imp ph ps))) :
    Nominal.NPrf (.imp (.all x ph) ps) :=
  by
  let proofSupport : Finset Var :=
    ph.fv ∪ ps.fv ∪ ({ x } : Finset Var) ∪ ({ y } : Finset Var)
  have p0000 :=
    @g_nfv ps x
      (by
        first
        | (aesop))
  have p0001 := @g_spim ph ps x y p0000 hyp_spimv_1
  exact p0001

@[expose]
noncomputable def g_ax11v2 (ph : Wff) (x : Var) (y : Var) (z : Var) (dv_ph_z : z ∉ ph.fv)
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
    @g_a9ev z y
      (by
        first
        | (aesop))
  have p0001 := @g_equequ2 z y x
  have p0002 :=
    @g_adantl (.objEq z y) (syn_wb (.objEq x z) (.objEq x y)) (.neg (.all x (.objEq x y)))
      p0001
  have p0003 :=
    @g_dveeq2 x y z
      (by
        first
        | (aesop))
  have p0004 :=
    @g_imp (.neg (.all x (.objEq x y))) (.objEq z y) (.all x (.objEq z y)) p0003
  have p0005 := @g_nfa1 (.objEq z y) x
  have p0006 := @g_imbi1d (.objEq z y) (.objEq x z) (.objEq x y) ph p0001
  have p0007 :=
    @g_sps (.objEq z y) (syn_wb (.imp (.objEq x z) ph) (.imp (.objEq x y) ph)) x p0006
  have p0008 :=
    @g_albid (.all x (.objEq z y)) (.imp (.objEq x z) ph) (.imp (.objEq x y) ph) x p0005
      p0007
  have p0009 :=
    @g_syl (syn_wa (.neg (.all x (.objEq x y))) (.objEq z y)) (.all x (.objEq z y))
      (syn_wb (.all x (.imp (.objEq x z) ph)) (.all x (.imp (.objEq x y) ph))) p0004 p0008
  have p0010 :=
    @g_imbi2d (syn_wa (.neg (.all x (.objEq x y))) (.objEq z y))
      (.all x (.imp (.objEq x z) ph)) (.all x (.imp (.objEq x y) ph)) ph p0009
  have p0011 :=
    @g_imbi12d (syn_wa (.neg (.all x (.objEq x y))) (.objEq z y)) (.objEq x z)
      (.objEq x y) (.imp ph (.all x (.imp (.objEq x z) ph)))
      (.imp ph (.all x (.imp (.objEq x y) ph))) p0002 p0010
  have p0012 :=
    @g_mpbii (syn_wa (.neg (.all x (.objEq x y))) (.objEq z y))
      (.imp (.objEq x z) (.imp ph (.all x (.imp (.objEq x z) ph))))
      (.imp (.objEq x y) (.imp ph (.all x (.imp (.objEq x y) ph)))) hyp_ax11v2_1 p0011
  have p0013 :=
    @g_ex (.neg (.all x (.objEq x y))) (.objEq z y)
      (.imp (.objEq x y) (.imp ph (.all x (.imp (.objEq x y) ph)))) p0012
  have p0014 :=
    @g_exlimdv (.neg (.all x (.objEq x y))) (.objEq z y)
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
    @g_mpi (.neg (.all x (.objEq x y))) (syn_wex z (.objEq z y))
      (.imp (.objEq x y) (.imp ph (.all x (.imp (.objEq x y) ph)))) p0000 p0014
  exact p0015

@[expose]
noncomputable def g_ax11a2 (ph : Wff) (x : Var) (y : Var) (z : Var) (dv_ph_z : z ∉ ph.fv)
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
    @g_syl5 ph (.all z ph) (.objEq x z) (.all x (.imp (.objEq x z) ph)) p0000 hyp_ax11a2_1
  have p0002 :=
    @g_ax11v2 ph x y z
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

@[expose]
noncomputable def g_ax11o (ph : Wff) (x : Var) (y : Var) :
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
    @g_ax11a2 ph x y z
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

@[expose]
noncomputable def g_equs5 (ph : Wff) (x : Var) (y : Var) :
    Nominal.NPrf
      (.imp (.neg (.all x (.objEq x y)))
        (.imp (syn_wex x (syn_wa (.objEq x y) ph)) (.all x (.imp (.objEq x y) ph)))) :=
  by
  have p0000 := @g_nfnae x y x
  have p0001 := @g_nfa1 (.imp (.objEq x y) ph) x
  have p0002 := @g_ax11o ph x y
  have p0003 :=
    @g_imp3a (.neg (.all x (.objEq x y))) (.objEq x y) ph (.all x (.imp (.objEq x y) ph))
      p0002
  have p0004 :=
    @g_exlimd (.neg (.all x (.objEq x y))) (syn_wa (.objEq x y) ph)
      (.all x (.imp (.objEq x y) ph)) x p0000 p0001 p0003
  exact p0004

@[expose]
noncomputable def g_spv (ph : Wff) (ps : Wff) (x : Var) (y : Var) (dv_ps_x : x ∉ ps.fv)
    (hyp_spv_1 : Nominal.NPrf (.imp (.objEq x y) (syn_wb ph ps))) :
    Nominal.NPrf (.imp (.all x ph) ps) :=
  by
  let proofSupport : Finset Var :=
    ph.fv ∪ ps.fv ∪ ({ x } : Finset Var) ∪ ({ y } : Finset Var)
  have p0000 := @g_biimpd (.objEq x y) ph ps hyp_spv_1
  have p0001 :=
    @g_spimv ph ps x y
      (by
        first
        | (aesop))
      p0000
  exact p0001

@[expose]
noncomputable def g_cbvalv (ph : Wff) (ps : Wff) (x : Var) (y : Var) (dv_ph_y : y ∉ ph.fv)
    (dv_ps_x : x ∉ ps.fv)
    (hyp_cbvalv_1 : Nominal.NPrf (.imp (.objEq x y) (syn_wb ph ps))) :
    Nominal.NPrf (syn_wb (.all x ph) (.all y ps)) :=
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
  have p0002 := @g_cbval ph ps x y p0000 p0001 hyp_cbvalv_1
  exact p0002

@[expose]
noncomputable def g_cbvexv (ph : Wff) (ps : Wff) (x : Var) (y : Var) (dv_ph_y : y ∉ ph.fv)
    (dv_ps_x : x ∉ ps.fv)
    (hyp_cbvalv_1 : Nominal.NPrf (.imp (.objEq x y) (syn_wb ph ps))) :
    Nominal.NPrf (syn_wb (syn_wex x ph) (syn_wex y ps)) :=
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
  have p0002 := @g_cbvex ph ps x y p0000 p0001 hyp_cbvalv_1
  exact p0002

@[expose]
noncomputable def g_cbval2 (ph : Wff) (ps : Wff) (x : Var) (y : Var) (z : Var) (w : Var)
    (dv_w_x : w ≠ x) (dv_w_z : w ≠ z) (dv_x_y : x ≠ y) (dv_y_z : y ≠ z)
    (hyp_cbval2_1 : Nominal.NPrf (syn_wnf z ph))
    (hyp_cbval2_2 : Nominal.NPrf (syn_wnf w ph))
    (hyp_cbval2_3 : Nominal.NPrf (syn_wnf x ps))
    (hyp_cbval2_4 : Nominal.NPrf (syn_wnf y ps))
    (hyp_cbval2_5 : Nominal.NPrf (.imp (syn_wa (.objEq x z) (.objEq y w)) (syn_wb ph ps))) :
    Nominal.NPrf (syn_wb (.all x (.all y ph)) (.all z (.all w ps))) :=
  by
  let proofSupport : Finset Var :=
    ph.fv ∪ ps.fv ∪ ({ x } : Finset Var) ∪ ({ y } : Finset Var) ∪ ({ z } : Finset Var) ∪
      ({ w } : Finset Var)
  have p0000 := @g_nfal ph z y hyp_cbval2_1
  have p0001 := @g_nfal ps x w hyp_cbval2_3
  have p0002 :=
    @g_nfv (.objEq x z) w
      (by
        first
        |
          (simp (config :=
              {
                failIfUnchanged :=
                  false }) only [NFChoice.Compiler.CoreFVSimp.fv_wff_objEq] at ⊢;
            aesop))
  have p0003 := @g_nfan (.objEq x z) ph w p0002 hyp_cbval2_2
  have p0004 :=
    @g_nfv (.objEq x z) y
      (by
        first
        |
          (simp (config :=
              {
                failIfUnchanged :=
                  false }) only [NFChoice.Compiler.CoreFVSimp.fv_wff_objEq] at ⊢;
            aesop))
  have p0005 := @g_nfan (.objEq x z) ps y p0004 hyp_cbval2_4
  have p0006 := @g_expcom (.objEq x z) (.objEq y w) (syn_wb ph ps) hyp_cbval2_5
  have p0007 := @g_pm5_32d (.objEq y w) (.objEq x z) ph ps p0006
  have p0008 :=
    @g_cbval (syn_wa (.objEq x z) ph) (syn_wa (.objEq x z) ps) y w p0003 p0005 p0007
  have p0009 :=
    @g_n_19_28v (.objEq x z) ph y
      (by
        first
        |
          (simp (config :=
              {
                failIfUnchanged :=
                  false }) only [NFChoice.Compiler.CoreFVSimp.fv_wff_objEq] at ⊢;
            aesop))
  have p0010 :=
    @g_n_19_28v (.objEq x z) ps w
      (by
        first
        |
          (simp (config :=
              {
                failIfUnchanged :=
                  false }) only [NFChoice.Compiler.CoreFVSimp.fv_wff_objEq] at ⊢;
            aesop))
  have p0011 :=
    @g_n_3bitr3i (.all y (syn_wa (.objEq x z) ph)) (.all w (syn_wa (.objEq x z) ps))
      (syn_wa (.objEq x z) (.all y ph)) (syn_wa (.objEq x z) (.all w ps)) p0008 p0009
      p0010
  have p0012 := @g_pm5_32 (.objEq x z) (.all y ph) (.all w ps)
  have p0013 :=
    @g_mpbir (.imp (.objEq x z) (syn_wb (.all y ph) (.all w ps)))
      (syn_wb (syn_wa (.objEq x z) (.all y ph)) (syn_wa (.objEq x z) (.all w ps))) p0011
      p0012
  have p0014 := @g_cbval (.all y ph) (.all w ps) x z p0000 p0001 p0013
  exact p0014

@[expose]
noncomputable def g_cbvex2 (ph : Wff) (ps : Wff) (x : Var) (y : Var) (z : Var) (w : Var)
    (dv_w_x : w ≠ x) (dv_w_z : w ≠ z) (dv_x_y : x ≠ y) (dv_y_z : y ≠ z)
    (hyp_cbval2_1 : Nominal.NPrf (syn_wnf z ph))
    (hyp_cbval2_2 : Nominal.NPrf (syn_wnf w ph))
    (hyp_cbval2_3 : Nominal.NPrf (syn_wnf x ps))
    (hyp_cbval2_4 : Nominal.NPrf (syn_wnf y ps))
    (hyp_cbval2_5 : Nominal.NPrf (.imp (syn_wa (.objEq x z) (.objEq y w)) (syn_wb ph ps))) :
    Nominal.NPrf (syn_wb (syn_wex x (syn_wex y ph)) (syn_wex z (syn_wex w ps))) :=
  by
  let proofSupport : Finset Var :=
    ph.fv ∪ ps.fv ∪ ({ x } : Finset Var) ∪ ({ y } : Finset Var) ∪ ({ z } : Finset Var) ∪
      ({ w } : Finset Var)
  have p0000 := @g_nfex ph z y hyp_cbval2_1
  have p0001 := @g_nfex ps x w hyp_cbval2_3
  have p0002 :=
    @g_nfv (.objEq x z) w
      (by
        first
        |
          (simp (config :=
              {
                failIfUnchanged :=
                  false }) only [NFChoice.Compiler.CoreFVSimp.fv_wff_objEq] at ⊢;
            aesop))
  have p0003 := @g_nfan (.objEq x z) ph w p0002 hyp_cbval2_2
  have p0004 :=
    @g_nfv (.objEq x z) y
      (by
        first
        |
          (simp (config :=
              {
                failIfUnchanged :=
                  false }) only [NFChoice.Compiler.CoreFVSimp.fv_wff_objEq] at ⊢;
            aesop))
  have p0005 := @g_nfan (.objEq x z) ps y p0004 hyp_cbval2_4
  have p0006 := @g_expcom (.objEq x z) (.objEq y w) (syn_wb ph ps) hyp_cbval2_5
  have p0007 := @g_pm5_32d (.objEq y w) (.objEq x z) ph ps p0006
  have p0008 :=
    @g_cbvex (syn_wa (.objEq x z) ph) (syn_wa (.objEq x z) ps) y w p0003 p0005 p0007
  have p0009 :=
    @g_n_19_42v (.objEq x z) ph y
      (by
        first
        |
          (simp (config :=
              {
                failIfUnchanged :=
                  false }) only [NFChoice.Compiler.CoreFVSimp.fv_wff_objEq] at ⊢;
            aesop))
  have p0010 :=
    @g_n_19_42v (.objEq x z) ps w
      (by
        first
        |
          (simp (config :=
              {
                failIfUnchanged :=
                  false }) only [NFChoice.Compiler.CoreFVSimp.fv_wff_objEq] at ⊢;
            aesop))
  have p0011 :=
    @g_n_3bitr3i (syn_wex y (syn_wa (.objEq x z) ph)) (syn_wex w (syn_wa (.objEq x z) ps))
      (syn_wa (.objEq x z) (syn_wex y ph)) (syn_wa (.objEq x z) (syn_wex w ps)) p0008
      p0009 p0010
  have p0012 := @g_pm5_32 (.objEq x z) (syn_wex y ph) (syn_wex w ps)
  have p0013 :=
    @g_mpbir (.imp (.objEq x z) (syn_wb (syn_wex y ph) (syn_wex w ps)))
      (syn_wb (syn_wa (.objEq x z) (syn_wex y ph)) (syn_wa (.objEq x z) (syn_wex w ps)))
      p0011 p0012
  have p0014 := @g_cbvex (syn_wex y ph) (syn_wex w ps) x z p0000 p0001 p0013
  exact p0014

@[expose]
noncomputable def g_cbval2v (ph : Wff) (ps : Wff) (x : Var) (y : Var) (z : Var) (w : Var)
    (dv_ph_w : w ∉ ph.fv) (dv_ph_z : z ∉ ph.fv) (dv_ps_x : x ∉ ps.fv)
    (dv_ps_y : y ∉ ps.fv) (dv_w_x : w ≠ x) (dv_w_z : w ≠ z) (dv_x_y : x ≠ y)
    (dv_y_z : y ≠ z)
    (hyp_cbval2v_1 : Nominal.NPrf (.imp (syn_wa (.objEq x z) (.objEq y w)) (syn_wb ph ps))) :
    Nominal.NPrf (syn_wb (.all x (.all y ph)) (.all z (.all w ps))) :=
  by
  let proofSupport : Finset Var :=
    ph.fv ∪ ps.fv ∪ ({ x } : Finset Var) ∪ ({ y } : Finset Var) ∪ ({ z } : Finset Var) ∪
      ({ w } : Finset Var)
  have p0000 :=
    @g_nfv ph z
      (by
        first
        | (aesop))
  have p0001 :=
    @g_nfv ph w
      (by
        first
        | (aesop))
  have p0002 :=
    @g_nfv ps x
      (by
        first
        | (aesop))
  have p0003 :=
    @g_nfv ps y
      (by
        first
        | (aesop))
  have p0004 :=
    @g_cbval2 ph ps x y z w
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

@[expose]
noncomputable def g_cbvald (ph : Wff) (ps : Wff) (ch : Wff) (x : Var) (y : Var)
    (dv_ch_x : x ∉ ch.fv) (dv_ph_x : x ∉ ph.fv)
    (hyp_cbvald_1 : Nominal.NPrf (syn_wnf y ph))
    (hyp_cbvald_2 : Nominal.NPrf (.imp ph (syn_wnf y ps)))
    (hyp_cbvald_3 : Nominal.NPrf (.imp ph (.imp (.objEq x y) (syn_wb ps ch)))) :
    Nominal.NPrf (.imp ph (syn_wb (.all x ps) (.all y ch))) :=
  by
  let proofSupport : Finset Var :=
    ph.fv ∪ ps.fv ∪ ch.fv ∪ ({ x } : Finset Var) ∪ ({ y } : Finset Var)
  have p0000 := @g_nfri ph y hyp_cbvald_1
  have p0001 :=
    @g_alrimiv ph (.all y ph) x
      (by
        first
        | (aesop))
      p0000
  have p0002 :=
    @g_nfvd ph ch x
      (by
        first
        | (aesop))
  have p0003 := @g_cbv2 ph ps ch x y hyp_cbvald_2 p0002 hyp_cbvald_3
  have p0004 :=
    @g_syl ph (.all x (.all y ph)) (syn_wb (.all x ps) (.all y ch)) p0001 p0003
  exact p0004

@[expose]
noncomputable def g_cbvexd (ph : Wff) (ps : Wff) (ch : Wff) (x : Var) (y : Var)
    (dv_ch_x : x ∉ ch.fv) (dv_ph_x : x ∉ ph.fv)
    (hyp_cbvald_1 : Nominal.NPrf (syn_wnf y ph))
    (hyp_cbvald_2 : Nominal.NPrf (.imp ph (syn_wnf y ps)))
    (hyp_cbvald_3 : Nominal.NPrf (.imp ph (.imp (.objEq x y) (syn_wb ps ch)))) :
    Nominal.NPrf (.imp ph (syn_wb (syn_wex x ps) (syn_wex y ch))) :=
  by
  let proofSupport : Finset Var :=
    ph.fv ∪ ps.fv ∪ ch.fv ∪ ({ x } : Finset Var) ∪ ({ y } : Finset Var)
  have p0000 := @g_nfnd ph ps y hyp_cbvald_2
  have p0001 := @g_notbi ps ch
  have p0002 :=
    @g_syl6ib ph (.objEq x y) (syn_wb ps ch) (syn_wb (.neg ps) (.neg ch)) hyp_cbvald_3
      p0001
  have p0003 :=
    @g_cbvald ph (.neg ps) (.neg ch) x y
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
  have p0004 := @g_notbid ph (.all x (.neg ps)) (.all y (.neg ch)) p0003
  have p0005 := (Nominal.biimpRefl (syn_wex x ps))
  have p0006 := (Nominal.biimpRefl (syn_wex y ch))
  have p0007 :=
    @g_n_3bitr4g ph (.neg (.all x (.neg ps))) (.neg (.all y (.neg ch))) (syn_wex x ps)
      (syn_wex y ch) p0004 p0005 p0006
  exact p0007

@[expose]
noncomputable def g_drsb1 (ph : Wff) (x : Var) (y : Var) (z : Var) :
    Nominal.NPrf
      (.imp (.all x (.objEq x y)) (syn_wb (syn_wsb z x ph) (syn_wsb z y ph))) :=
  by
  have p0000 := @g_equequ1 x y z
  have p0001 := @g_sps (.objEq x y) (syn_wb (.objEq x z) (.objEq y z)) x p0000
  have p0002 := @g_imbi1d (.all x (.objEq x y)) (.objEq x z) (.objEq y z) ph p0001
  have p0003 := @g_anbi1d (.all x (.objEq x y)) (.objEq x z) (.objEq y z) ph p0001
  have p0004 := @g_drex1 (syn_wa (.objEq x z) ph) (syn_wa (.objEq y z) ph) x y p0003
  have p0005 :=
    @g_anbi12d (.all x (.objEq x y)) (.imp (.objEq x z) ph) (.imp (.objEq y z) ph)
      (syn_wex x (syn_wa (.objEq x z) ph)) (syn_wex y (syn_wa (.objEq y z) ph)) p0002
      p0004
  have p0006 := (Nominal.biimpRefl (syn_wsb z x ph))
  have p0007 := (Nominal.biimpRefl (syn_wsb z y ph))
  have p0008 :=
    @g_n_3bitr4g (.all x (.objEq x y))
      (syn_wa (.imp (.objEq x z) ph) (syn_wex x (syn_wa (.objEq x z) ph)))
      (syn_wa (.imp (.objEq y z) ph) (syn_wex y (syn_wa (.objEq y z) ph)))
      (syn_wsb z x ph) (syn_wsb z y ph) p0005 p0006 p0007
  exact p0008

@[expose]
noncomputable def g_sb2 (ph : Wff) (x : Var) (y : Var) :
    Nominal.NPrf (.imp (.all x (.imp (.objEq x y) ph)) (syn_wsb y x ph)) :=
  by
  have p0000 := @g_sp (.imp (.objEq x y) ph) x
  have p0001 := @g_equs4 ph x y
  have p0002 := (Nominal.biimpRefl (syn_wsb y x ph))
  have p0003 :=
    @g_sylanbrc (.all x (.imp (.objEq x y) ph)) (.imp (.objEq x y) ph)
      (syn_wex x (syn_wa (.objEq x y) ph)) (syn_wsb y x ph) p0000 p0001 p0002
  exact p0003

@[expose]
noncomputable def g_stdpc4 (ph : Wff) (x : Var) (y : Var) :
    Nominal.NPrf (.imp (.all x ph) (syn_wsb y x ph)) :=
  by
  have p0000 := Nominal.ax1 ph (.objEq x y)
  have p0001 := @g_alimi ph (.imp (.objEq x y) ph) x p0000
  have p0002 := @g_sb2 ph x y
  have p0003 :=
    @g_syl (.all x ph) (.all x (.imp (.objEq x y) ph)) (syn_wsb y x ph) p0001 p0002
  exact p0003

@[expose]
noncomputable def g_sbft (ph : Wff) (x : Var) (y : Var) :
    Nominal.NPrf (.imp (syn_wnf x ph) (syn_wb (syn_wsb y x ph) ph)) :=
  by
  have p0000 := @g_sb1 ph x y
  have p0001 := @g_simpr (.objEq x y) ph
  have p0002 := Nominal.gen p0001 x
  have p0003 := @g_n_19_23t (syn_wa (.objEq x y) ph) ph x
  have p0004 :=
    @g_mpbii (syn_wnf x ph) (.all x (.imp (syn_wa (.objEq x y) ph) ph))
      (.imp (syn_wex x (syn_wa (.objEq x y) ph)) ph) p0002 p0003
  have p0005 :=
    @g_syl5 (syn_wsb y x ph) (syn_wex x (syn_wa (.objEq x y) ph)) (syn_wnf x ph) ph p0000
      p0004
  have p0006 := @g_nfr ph x
  have p0007 := @g_stdpc4 ph x y
  have p0008 := @g_syl6 (syn_wnf x ph) ph (.all x ph) (syn_wsb y x ph) p0006 p0007
  have p0009 := @g_impbid (syn_wnf x ph) (syn_wsb y x ph) ph p0005 p0008
  exact p0009

@[expose]
noncomputable def g_sbf (ph : Wff) (x : Var) (y : Var)
    (hyp_sbf_1 : Nominal.NPrf (syn_wnf x ph)) :
    Nominal.NPrf (syn_wb (syn_wsb y x ph) ph) :=
  by
  have p0000 := @g_sbft ph x y
  have p0001 := Nominal.mp hyp_sbf_1 p0000
  exact p0001

@[expose]
noncomputable def g_equsb2 (x : Var) (y : Var) :
    Nominal.NPrf (syn_wsb y x (.objEq y x)) :=
  by
  have p0000 := @g_sb2 (.objEq y x) x y
  have p0001 := @g_equcomi x y
  have p0002 :=
    @g_mpg (.imp (.objEq x y) (.objEq y x)) (syn_wsb y x (.objEq y x)) x p0000 p0001
  exact p0002

@[expose]
noncomputable def g_sbied (ph : Wff) (ps : Wff) (ch : Wff) (x : Var) (y : Var)
    (hyp_sbied_1 : Nominal.NPrf (syn_wnf x ph))
    (hyp_sbied_2 : Nominal.NPrf (.imp ph (syn_wnf x ch)))
    (hyp_sbied_3 : Nominal.NPrf (.imp ph (.imp (.objEq x y) (syn_wb ps ch)))) :
    Nominal.NPrf (.imp ph (syn_wb (syn_wsb y x ps) ch)) :=
  by
  have p0000 := @g_sb1 ps x y
  have p0001 := @g_bi1 ps ch
  have p0002 := @g_syl6 ph (.objEq x y) (syn_wb ps ch) (.imp ps ch) hyp_sbied_3 p0001
  have p0003 := @g_imp3a ph (.objEq x y) ps ch p0002
  have p0004 := @g_eximd ph (syn_wa (.objEq x y) ps) ch x hyp_sbied_1 p0003
  have p0005 :=
    @g_syl5 (syn_wsb y x ps) (syn_wex x (syn_wa (.objEq x y) ps)) ph (syn_wex x ch) p0000
      p0004
  have p0006 := @g_n_19_9d ch ph x hyp_sbied_2
  have p0007 := @g_syld ph (syn_wsb y x ps) (syn_wex x ch) ch p0005 p0006
  have p0008 := @g_nfrd ph ch x hyp_sbied_2
  have p0009 := @g_bi2 ps ch
  have p0010 := @g_syl6 ph (.objEq x y) (syn_wb ps ch) (.imp ch ps) hyp_sbied_3 p0009
  have p0011 := @g_com23 ph (.objEq x y) ch ps p0010
  have p0012 := @g_alimd ph ch (.imp (.objEq x y) ps) x hyp_sbied_1 p0011
  have p0013 := @g_sb2 ps x y
  have p0014 :=
    @g_syl6 ph (.all x ch) (.all x (.imp (.objEq x y) ps)) (syn_wsb y x ps) p0012 p0013
  have p0015 := @g_syld ph ch (.all x ch) (syn_wsb y x ps) p0008 p0014
  have p0016 := @g_impbid ph (syn_wsb y x ps) ch p0007 p0015
  exact p0016

@[expose]
noncomputable def g_sbie (ph : Wff) (ps : Wff) (x : Var) (y : Var)
    (hyp_sbie_1 : Nominal.NPrf (syn_wnf x ps))
    (hyp_sbie_2 : Nominal.NPrf (.imp (.objEq x y) (syn_wb ph ps))) :
    Nominal.NPrf (syn_wb (syn_wsb y x ph) ps) :=
  by
  have p0000 := @g_nftru x
  have p0001 := @g_a1i (syn_wnf x ps) syn_wtru hyp_sbie_1
  have p0002 := @g_a1i (.imp (.objEq x y) (syn_wb ph ps)) syn_wtru hyp_sbie_2
  have p0003 := @g_sbied syn_wtru ph ps x y p0000 p0001 p0002
  have p0004 := @g_trud (syn_wb (syn_wsb y x ph) ps) p0003
  exact p0004

@[expose]
noncomputable def g_hbsb2a (ph : Wff) (x : Var) (y : Var) :
    Nominal.NPrf (.imp (syn_wsb y x (.all y ph)) (.all x (syn_wsb y x ph))) :=
  by
  have p0000 := @g_sb4a ph x y
  have p0001 := @g_sb2 ph x y
  have p0002 := @g_a5i (.imp (.objEq x y) ph) (syn_wsb y x ph) x p0001
  have p0003 :=
    @g_syl (syn_wsb y x (.all y ph)) (.all x (.imp (.objEq x y) ph))
      (.all x (syn_wsb y x ph)) p0000 p0002
  exact p0003

@[expose]
noncomputable def g_hbsb3 (ph : Wff) (x : Var) (y : Var)
    (hyp_hbsb3_1 : Nominal.NPrf (.imp ph (.all y ph))) :
    Nominal.NPrf (.imp (syn_wsb y x ph) (.all x (syn_wsb y x ph))) :=
  by
  have p0000 := @g_sbimi ph (.all y ph) x y hyp_hbsb3_1
  have p0001 := @g_hbsb2a ph x y
  have p0002 :=
    @g_syl (syn_wsb y x ph) (syn_wsb y x (.all y ph)) (.all x (syn_wsb y x ph)) p0000
      p0001
  exact p0002

@[expose]
noncomputable def g_nfs1 (ph : Wff) (x : Var) (y : Var)
    (hyp_nfs1_1 : Nominal.NPrf (syn_wnf y ph)) :
    Nominal.NPrf (syn_wnf x (syn_wsb y x ph)) :=
  by
  have p0000 := @g_nfri ph y hyp_nfs1_1
  have p0001 := @g_hbsb3 ph x y p0000
  have p0002 := @g_nfi (syn_wsb y x ph) x p0001
  exact p0002

@[expose]
noncomputable def g_ax16 (ph : Wff) (x : Var) (y : Var) (dv_x_y : x ≠ y) :
    Nominal.NPrf (.imp (.all x (.objEq x y)) (.imp ph (.all x ph))) :=
  by
  let proofSupport : Finset Var := ph.fv ∪ ({ x } : Finset Var) ∪ ({ y } : Finset Var)
  have p0000 :=
    @g_a16g ph x y x
      (by
        first
        | (aesop))
  exact p0000

@[expose]
noncomputable def g_a16nf (ph : Wff) (x : Var) (y : Var) (z : Var) (dv_x_y : x ≠ y) :
    Nominal.NPrf (.imp (.all x (.objEq x y)) (syn_wnf z ph)) :=
  by
  let proofSupport : Finset Var :=
    ph.fv ∪ ({ x } : Finset Var) ∪ ({ y } : Finset Var) ∪ ({ z } : Finset Var)
  have p0000 := @g_nfae x y z
  have p0001 :=
    @g_a16g ph x y z
      (by
        first
        | (aesop))
  have p0002 := @g_nfd (.all x (.objEq x y)) ph z p0000 p0001
  exact p0002

@[expose]
noncomputable def g_sb4 (ph : Wff) (x : Var) (y : Var) :
    Nominal.NPrf
      (.imp (.neg (.all x (.objEq x y)))
        (.imp (syn_wsb y x ph) (.all x (.imp (.objEq x y) ph)))) :=
  by
  have p0000 := @g_sb1 ph x y
  have p0001 := @g_equs5 ph x y
  have p0002 :=
    @g_syl5 (syn_wsb y x ph) (syn_wex x (syn_wa (.objEq x y) ph))
      (.neg (.all x (.objEq x y))) (.all x (.imp (.objEq x y) ph)) p0000 p0001
  exact p0002

@[expose]
noncomputable def g_sb4b (ph : Wff) (x : Var) (y : Var) :
    Nominal.NPrf
      (.imp (.neg (.all x (.objEq x y)))
        (syn_wb (syn_wsb y x ph) (.all x (.imp (.objEq x y) ph)))) :=
  by
  have p0000 := @g_sb4 ph x y
  have p0001 := @g_sb2 ph x y
  have p0002 :=
    @g_impbid1 (.neg (.all x (.objEq x y))) (syn_wsb y x ph)
      (.all x (.imp (.objEq x y) ph)) p0000 p0001
  exact p0002

@[expose]
noncomputable def g_hbsb2 (ph : Wff) (x : Var) (y : Var) :
    Nominal.NPrf
      (.imp (.neg (.all x (.objEq x y))) (.imp (syn_wsb y x ph) (.all x (syn_wsb y x ph)))) :=
  by
  have p0000 := @g_sb4 ph x y
  have p0001 := @g_sb2 ph x y
  have p0002 := @g_a5i (.imp (.objEq x y) ph) (syn_wsb y x ph) x p0001
  have p0003 :=
    @g_syl6 (.neg (.all x (.objEq x y))) (syn_wsb y x ph) (.all x (.imp (.objEq x y) ph))
      (.all x (syn_wsb y x ph)) p0000 p0002
  exact p0003

@[expose]
noncomputable def g_nfsb2 (ph : Wff) (x : Var) (y : Var) :
    Nominal.NPrf (.imp (.neg (.all x (.objEq x y))) (syn_wnf x (syn_wsb y x ph))) :=
  by
  have p0000 := @g_nfnae x y x
  have p0001 := @g_hbsb2 ph x y
  have p0002 := @g_nfd (.neg (.all x (.objEq x y))) (syn_wsb y x ph) x p0000 p0001
  exact p0002

@[expose]
noncomputable def g_sbequi (ph : Wff) (x : Var) (y : Var) (z : Var) :
    Nominal.NPrf (.imp (.objEq x y) (.imp (syn_wsb x z ph) (syn_wsb y z ph))) :=
  by
  have p0000 := @g_hbsb2 ph z x
  have p0001 := @g_equvini x y z
  have p0002 := @g_stdpc7 ph x z
  have p0003 := @g_sbequ1 ph z y
  have p0004 :=
    @g_sylan9 (.objEq x z) (syn_wsb x z ph) ph (.objEq z y) (syn_wsb y z ph) p0002 p0003
  have p0005 :=
    @g_eximi (syn_wa (.objEq x z) (.objEq z y)) (.imp (syn_wsb x z ph) (syn_wsb y z ph)) z
      p0004
  have p0006 :=
    @g_syl (.objEq x y) (syn_wex z (syn_wa (.objEq x z) (.objEq z y)))
      (syn_wex z (.imp (syn_wsb x z ph) (syn_wsb y z ph))) p0001 p0005
  have p0007 := @g_n_19_35 (syn_wsb x z ph) (syn_wsb y z ph) z
  have p0008 :=
    @g_sylib (.objEq x y) (syn_wex z (.imp (syn_wsb x z ph) (syn_wsb y z ph)))
      (.imp (.all z (syn_wsb x z ph)) (syn_wex z (syn_wsb y z ph))) p0006 p0007
  have p0009 :=
    @g_sylan9 (.neg (.all z (.objEq z x))) (syn_wsb x z ph) (.all z (syn_wsb x z ph))
      (.objEq x y) (syn_wex z (syn_wsb y z ph)) p0000 p0008
  have p0010 := @g_nfsb2 ph z y
  have p0011 := @g_n_19_9d (syn_wsb y z ph) (.neg (.all z (.objEq z y))) z p0010
  have p0012 :=
    @g_syl9 (syn_wa (.neg (.all z (.objEq z x))) (.objEq x y)) (syn_wsb x z ph)
      (syn_wex z (syn_wsb y z ph)) (.neg (.all z (.objEq z y))) (syn_wsb y z ph) p0009
      p0011
  have p0013 :=
    @g_ex (.neg (.all z (.objEq z x))) (.objEq x y)
      (.imp (.neg (.all z (.objEq z y))) (.imp (syn_wsb x z ph) (syn_wsb y z ph))) p0012
  have p0014 :=
    @g_com23 (.neg (.all z (.objEq z x))) (.objEq x y) (.neg (.all z (.objEq z y)))
      (.imp (syn_wsb x z ph) (syn_wsb y z ph)) p0013
  have p0015 := @g_sbequ2 ph z x
  have p0016 := @g_sps (.objEq z x) (.imp (syn_wsb x z ph) ph) z p0015
  have p0017 :=
    @g_adantr (.all z (.objEq z x)) (.imp (syn_wsb x z ph) ph) (.objEq x y) p0016
  have p0018 := @g_sbequ1 ph x y
  have p0019 := @g_drsb1 ph z x y
  have p0020 := @g_biimprd (.all z (.objEq z x)) (syn_wsb y z ph) (syn_wsb y x ph) p0019
  have p0021 :=
    @g_sylan9r (.objEq x y) ph (syn_wsb y x ph) (.all z (.objEq z x)) (syn_wsb y z ph)
      p0018 p0020
  have p0022 :=
    @g_syld (syn_wa (.all z (.objEq z x)) (.objEq x y)) (syn_wsb x z ph) ph
      (syn_wsb y z ph) p0017 p0021
  have p0023 :=
    @g_ex (.all z (.objEq z x)) (.objEq x y) (.imp (syn_wsb x z ph) (syn_wsb y z ph))
      p0022
  have p0024 := @g_drsb1 ph z y x
  have p0025 := @g_biimpd (.all z (.objEq z y)) (syn_wsb x z ph) (syn_wsb x y ph) p0024
  have p0026 := @g_stdpc7 ph x y
  have p0027 :=
    @g_sylan9 (.all z (.objEq z y)) (syn_wsb x z ph) (syn_wsb x y ph) (.objEq x y) ph
      p0025 p0026
  have p0028 := @g_sps (.objEq z y) (.imp ph (syn_wsb y z ph)) z p0003
  have p0029 :=
    @g_adantr (.all z (.objEq z y)) (.imp ph (syn_wsb y z ph)) (.objEq x y) p0028
  have p0030 :=
    @g_syld (syn_wa (.all z (.objEq z y)) (.objEq x y)) (syn_wsb x z ph) ph
      (syn_wsb y z ph) p0027 p0029
  have p0031 :=
    @g_ex (.all z (.objEq z y)) (.objEq x y) (.imp (syn_wsb x z ph) (syn_wsb y z ph))
      p0030
  have p0032 :=
    @g_pm2_61ii (.all z (.objEq z x)) (.all z (.objEq z y))
      (.imp (.objEq x y) (.imp (syn_wsb x z ph) (syn_wsb y z ph))) p0014 p0023 p0031
  exact p0032

@[expose]
noncomputable def g_sbequ (ph : Wff) (x : Var) (y : Var) (z : Var) :
    Nominal.NPrf (.imp (.objEq x y) (syn_wb (syn_wsb x z ph) (syn_wsb y z ph))) :=
  by
  have p0000 := @g_sbequi ph x y z
  have p0001 := @g_sbequi ph y x z
  have p0002 := @g_equcoms (.imp (syn_wsb y z ph) (syn_wsb x z ph)) y x p0001
  have p0003 := @g_impbid (.objEq x y) (syn_wsb x z ph) (syn_wsb y z ph) p0000 p0002
  exact p0003

@[expose]
noncomputable def g_sbn (ph : Wff) (x : Var) (y : Var) :
    Nominal.NPrf (syn_wb (syn_wsb y x (.neg ph)) (.neg (syn_wsb y x ph))) :=
  by
  have p0000 := @g_sbequ2 (.neg ph) x y
  have p0001 := @g_sbequ2 ph x y
  have p0002 :=
    @g_nsyld (.objEq x y) (syn_wsb y x (.neg ph)) ph (syn_wsb y x ph) p0000 p0001
  have p0003 :=
    @g_sps (.objEq x y) (.imp (syn_wsb y x (.neg ph)) (.neg (syn_wsb y x ph))) x p0002
  have p0004 := @g_sb4 (.neg ph) x y
  have p0005 := @g_sb1 ph x y
  have p0006 := @g_equs3 ph x y
  have p0007 :=
    @g_sylib (syn_wsb y x ph) (syn_wex x (syn_wa (.objEq x y) ph))
      (.neg (.all x (.imp (.objEq x y) (.neg ph)))) p0005 p0006
  have p0008 := @g_con2i (syn_wsb y x ph) (.all x (.imp (.objEq x y) (.neg ph))) p0007
  have p0009 :=
    @g_syl6 (.neg (.all x (.objEq x y))) (syn_wsb y x (.neg ph))
      (.all x (.imp (.objEq x y) (.neg ph))) (.neg (syn_wsb y x ph)) p0004 p0008
  have p0010 :=
    @g_pm2_61i (.all x (.objEq x y))
      (.imp (syn_wsb y x (.neg ph)) (.neg (syn_wsb y x ph))) p0003 p0009
  have p0011 := @g_sbequ1 ph x y
  have p0012 := @g_con3rr3 (.objEq x y) ph (syn_wsb y x ph) p0011
  have p0013 := @g_sb2 (.neg (.neg ph)) x y
  have p0014 := @g_notnot ph
  have p0015 := @g_sbbii ph (.neg (.neg ph)) x y p0014
  have p0016 :=
    @g_sylibr (.all x (.imp (.objEq x y) (.neg (.neg ph)))) (syn_wsb y x (.neg (.neg ph)))
      (syn_wsb y x ph) p0013 p0015
  have p0017 :=
    @g_con3i (.all x (.imp (.objEq x y) (.neg (.neg ph)))) (syn_wsb y x ph) p0016
  have p0018 := @g_equs3 (.neg ph) x y
  have p0019 :=
    @g_sylibr (.neg (syn_wsb y x ph)) (.neg (.all x (.imp (.objEq x y) (.neg (.neg ph)))))
      (syn_wex x (syn_wa (.objEq x y) (.neg ph))) p0017 p0018
  have p0020 := (Nominal.biimpRefl (syn_wsb y x (.neg ph)))
  have p0021 :=
    @g_sylanbrc (.neg (syn_wsb y x ph)) (.imp (.objEq x y) (.neg ph))
      (syn_wex x (syn_wa (.objEq x y) (.neg ph))) (syn_wsb y x (.neg ph)) p0012 p0019
      p0020
  have p0022 := @g_impbii (syn_wsb y x (.neg ph)) (.neg (syn_wsb y x ph)) p0010 p0021
  exact p0022

@[expose]
noncomputable def g_sbi1 (ph : Wff) (ps : Wff) (x : Var) (y : Var) :
    Nominal.NPrf
      (.imp (syn_wsb y x (.imp ph ps)) (.imp (syn_wsb y x ph) (syn_wsb y x ps))) :=
  by
  have p0000 := @g_sbequ2 ph x y
  have p0001 := @g_sbequ2 (.imp ph ps) x y
  have p0002 :=
    @g_syl5d (.objEq x y) (syn_wsb y x ph) ph (syn_wsb y x (.imp ph ps)) ps p0000 p0001
  have p0003 := @g_sbequ1 ps x y
  have p0004 :=
    @g_syl6d (.objEq x y) (syn_wsb y x (.imp ph ps)) (syn_wsb y x ph) ps (syn_wsb y x ps)
      p0002 p0003
  have p0005 :=
    @g_sps (.objEq x y)
      (.imp (syn_wsb y x (.imp ph ps)) (.imp (syn_wsb y x ph) (syn_wsb y x ps))) x p0004
  have p0006 := @g_sb4 ph x y
  have p0007 := @g_sb4 (.imp ph ps) x y
  have p0008 := Nominal.ax2 (.objEq x y) ph ps
  have p0009 :=
    @g_al2imi (.imp (.objEq x y) (.imp ph ps)) (.imp (.objEq x y) ph)
      (.imp (.objEq x y) ps) x p0008
  have p0010 := @g_sb2 ps x y
  have p0011 :=
    @g_syl6 (.all x (.imp (.objEq x y) (.imp ph ps))) (.all x (.imp (.objEq x y) ph))
      (.all x (.imp (.objEq x y) ps)) (syn_wsb y x ps) p0009 p0010
  have p0012 :=
    @g_syl6 (.neg (.all x (.objEq x y))) (syn_wsb y x (.imp ph ps))
      (.all x (.imp (.objEq x y) (.imp ph ps)))
      (.imp (.all x (.imp (.objEq x y) ph)) (syn_wsb y x ps)) p0007 p0011
  have p0013 :=
    @g_syl5d (.neg (.all x (.objEq x y))) (syn_wsb y x ph) (.all x (.imp (.objEq x y) ph))
      (syn_wsb y x (.imp ph ps)) (syn_wsb y x ps) p0006 p0012
  have p0014 :=
    @g_pm2_61i (.all x (.objEq x y))
      (.imp (syn_wsb y x (.imp ph ps)) (.imp (syn_wsb y x ph) (syn_wsb y x ps))) p0005
      p0013
  exact p0014

@[expose]
noncomputable def g_sbi2 (ph : Wff) (ps : Wff) (x : Var) (y : Var) :
    Nominal.NPrf
      (.imp (.imp (syn_wsb y x ph) (syn_wsb y x ps)) (syn_wsb y x (.imp ph ps))) :=
  by
  have p0000 := @g_sbn ph x y
  have p0001 := @g_pm2_21 ph ps
  have p0002 := @g_sbimi (.neg ph) (.imp ph ps) x y p0001
  have p0003 :=
    @g_sylbir (.neg (syn_wsb y x ph)) (syn_wsb y x (.neg ph)) (syn_wsb y x (.imp ph ps))
      p0000 p0002
  have p0004 := Nominal.ax1 ps ph
  have p0005 := @g_sbimi ps (.imp ph ps) x y p0004
  have p0006 :=
    @g_ja (syn_wsb y x ph) (syn_wsb y x ps) (syn_wsb y x (.imp ph ps)) p0003 p0005
  exact p0006

@[expose]
noncomputable def g_sbim (ph : Wff) (ps : Wff) (x : Var) (y : Var) :
    Nominal.NPrf
      (syn_wb (syn_wsb y x (.imp ph ps)) (.imp (syn_wsb y x ph) (syn_wsb y x ps))) :=
  by
  have p0000 := @g_sbi1 ph ps x y
  have p0001 := @g_sbi2 ph ps x y
  have p0002 :=
    @g_impbii (syn_wsb y x (.imp ph ps)) (.imp (syn_wsb y x ph) (syn_wsb y x ps)) p0000
      p0001
  exact p0002

@[expose]
noncomputable def g_sbor (ph : Wff) (ps : Wff) (x : Var) (y : Var) :
    Nominal.NPrf
      (syn_wb (syn_wsb y x (syn_wo ph ps)) (syn_wo (syn_wsb y x ph) (syn_wsb y x ps))) :=
  by
  have p0000 := @g_sbim (.neg ph) ps x y
  have p0001 := @g_sbn ph x y
  have p0002 :=
    @g_imbi1i (syn_wsb y x (.neg ph)) (.neg (syn_wsb y x ph)) (syn_wsb y x ps) p0001
  have p0003 :=
    @g_bitri (syn_wsb y x (.imp (.neg ph) ps))
      (.imp (syn_wsb y x (.neg ph)) (syn_wsb y x ps))
      (.imp (.neg (syn_wsb y x ph)) (syn_wsb y x ps)) p0000 p0002
  have p0004 := (Nominal.biimpRefl (syn_wo ph ps))
  have p0005 := @g_sbbii (syn_wo ph ps) (.imp (.neg ph) ps) x y p0004
  have p0006 := (Nominal.biimpRefl (syn_wo (syn_wsb y x ph) (syn_wsb y x ps)))
  have p0007 :=
    @g_n_3bitr4i (syn_wsb y x (.imp (.neg ph) ps))
      (.imp (.neg (syn_wsb y x ph)) (syn_wsb y x ps)) (syn_wsb y x (syn_wo ph ps))
      (syn_wo (syn_wsb y x ph) (syn_wsb y x ps)) p0003 p0005 p0006
  exact p0007

@[expose]
noncomputable def g_sban (ph : Wff) (ps : Wff) (x : Var) (y : Var) :
    Nominal.NPrf
      (syn_wb (syn_wsb y x (syn_wa ph ps)) (syn_wa (syn_wsb y x ph) (syn_wsb y x ps))) :=
  by
  have p0000 := @g_sbn (.imp ph (.neg ps)) x y
  have p0001 := @g_sbim ph (.neg ps) x y
  have p0002 := @g_sbn ps x y
  have p0003 :=
    @g_imbi2i (syn_wsb y x (.neg ps)) (.neg (syn_wsb y x ps)) (syn_wsb y x ph) p0002
  have p0004 :=
    @g_bitri (syn_wsb y x (.imp ph (.neg ps)))
      (.imp (syn_wsb y x ph) (syn_wsb y x (.neg ps)))
      (.imp (syn_wsb y x ph) (.neg (syn_wsb y x ps))) p0001 p0003
  have p0005 :=
    @g_xchbinx (syn_wsb y x (.neg (.imp ph (.neg ps)))) (syn_wsb y x (.imp ph (.neg ps)))
      (.imp (syn_wsb y x ph) (.neg (syn_wsb y x ps))) p0000 p0004
  have p0006 := (Nominal.biimpRefl (syn_wa ph ps))
  have p0007 := @g_sbbii (syn_wa ph ps) (.neg (.imp ph (.neg ps))) x y p0006
  have p0008 := (Nominal.biimpRefl (syn_wa (syn_wsb y x ph) (syn_wsb y x ps)))
  have p0009 :=
    @g_n_3bitr4i (syn_wsb y x (.neg (.imp ph (.neg ps))))
      (.neg (.imp (syn_wsb y x ph) (.neg (syn_wsb y x ps)))) (syn_wsb y x (syn_wa ph ps))
      (syn_wa (syn_wsb y x ph) (syn_wsb y x ps)) p0005 p0007 p0008
  exact p0009

@[expose]
noncomputable def g_sbbi (ph : Wff) (ps : Wff) (x : Var) (y : Var) :
    Nominal.NPrf
      (syn_wb (syn_wsb y x (syn_wb ph ps)) (syn_wb (syn_wsb y x ph) (syn_wsb y x ps))) :=
  by
  have p0000 := @g_dfbi2 ph ps
  have p0001 := @g_sbbii (syn_wb ph ps) (syn_wa (.imp ph ps) (.imp ps ph)) x y p0000
  have p0002 := @g_sbim ph ps x y
  have p0003 := @g_sbim ps ph x y
  have p0004 :=
    @g_anbi12i (syn_wsb y x (.imp ph ps)) (.imp (syn_wsb y x ph) (syn_wsb y x ps))
      (syn_wsb y x (.imp ps ph)) (.imp (syn_wsb y x ps) (syn_wsb y x ph)) p0002 p0003
  have p0005 := @g_sban (.imp ph ps) (.imp ps ph) x y
  have p0006 := @g_dfbi2 (syn_wsb y x ph) (syn_wsb y x ps)
  have p0007 :=
    @g_n_3bitr4i (syn_wa (syn_wsb y x (.imp ph ps)) (syn_wsb y x (.imp ps ph)))
      (syn_wa (.imp (syn_wsb y x ph) (syn_wsb y x ps)) (.imp (syn_wsb y x ps) (syn_wsb y x ph)))
      (syn_wsb y x (syn_wa (.imp ph ps) (.imp ps ph)))
      (syn_wb (syn_wsb y x ph) (syn_wsb y x ps)) p0004 p0005 p0006
  have p0008 :=
    @g_bitri (syn_wsb y x (syn_wb ph ps)) (syn_wsb y x (syn_wa (.imp ph ps) (.imp ps ph)))
      (syn_wb (syn_wsb y x ph) (syn_wsb y x ps)) p0001 p0007
  exact p0008

@[expose]
noncomputable def g_sblbis (ph : Wff) (ps : Wff) (ch : Wff) (x : Var) (y : Var)
    (hyp_sblbis_1 : Nominal.NPrf (syn_wb (syn_wsb y x ph) ps)) :
    Nominal.NPrf (syn_wb (syn_wsb y x (syn_wb ch ph)) (syn_wb (syn_wsb y x ch) ps)) :=
  by
  have p0000 := @g_sbbi ch ph x y
  have p0001 := @g_bibi2i (syn_wsb y x ph) ps (syn_wsb y x ch) hyp_sblbis_1
  have p0002 :=
    @g_bitri (syn_wsb y x (syn_wb ch ph)) (syn_wb (syn_wsb y x ch) (syn_wsb y x ph))
      (syn_wb (syn_wsb y x ch) ps) p0000 p0001
  exact p0002

@[expose]
noncomputable def g_nfsb4t (ph : Wff) (x : Var) (y : Var) (z : Var) :
    Nominal.NPrf
      (.imp (.all x (syn_wnf z ph))
        (.imp (.neg (.all z (.objEq z y))) (syn_wnf z (syn_wsb y x ph)))) :=
  by
  have p0000 := @g_sbequ12 ph x y
  have p0001 := @g_sps (.objEq x y) (syn_wb ph (syn_wsb y x ph)) x p0000
  have p0002 := @g_drnf2 ph (syn_wsb y x ph) x y z p0001
  have p0003 :=
    @g_biimpcd (.all x (.objEq x y)) (syn_wnf z ph) (syn_wnf z (syn_wsb y x ph)) p0002
  have p0004 :=
    @g_sps (syn_wnf z ph) (.imp (.all x (.objEq x y)) (syn_wnf z (syn_wsb y x ph))) x
      p0003
  have p0005 :=
    @g_a1dd (.all x (syn_wnf z ph)) (.all x (.objEq x y)) (syn_wnf z (syn_wsb y x ph))
      (syn_wa (.neg (.all z (.objEq z x))) (.neg (.all z (.objEq z y)))) p0004
  have p0006 := @g_nfa1 (syn_wnf z ph) x
  have p0007 := @g_nfnae z x x
  have p0008 := @g_nfnae z y x
  have p0009 :=
    @g_nfan (.neg (.all z (.objEq z x))) (.neg (.all z (.objEq z y))) x p0007 p0008
  have p0010 :=
    @g_nfan (.all x (syn_wnf z ph))
      (syn_wa (.neg (.all z (.objEq z x))) (.neg (.all z (.objEq z y)))) x p0006 p0009
  have p0011 := @g_nfeqf x y z
  have p0012 :=
    @g_adantl (syn_wa (.neg (.all z (.objEq z x))) (.neg (.all z (.objEq z y))))
      (syn_wnf z (.objEq x y)) (.all x (syn_wnf z ph)) p0011
  have p0013 := @g_sp (syn_wnf z ph) x
  have p0014 :=
    @g_adantr (.all x (syn_wnf z ph)) (syn_wnf z ph)
      (syn_wa (.neg (.all z (.objEq z x))) (.neg (.all z (.objEq z y)))) p0013
  have p0015 :=
    @g_nfimd
      (syn_wa (.all x (syn_wnf z ph))
        (syn_wa (.neg (.all z (.objEq z x))) (.neg (.all z (.objEq z y)))))
      (.objEq x y) ph z p0012 p0014
  have p0016 :=
    @g_nfald
      (syn_wa (.all x (syn_wnf z ph))
        (syn_wa (.neg (.all z (.objEq z x))) (.neg (.all z (.objEq z y)))))
      (.imp (.objEq x y) ph) z x p0010 p0015
  have p0017 :=
    @g_ex (.all x (syn_wnf z ph))
      (syn_wa (.neg (.all z (.objEq z x))) (.neg (.all z (.objEq z y))))
      (syn_wnf z (.all x (.imp (.objEq x y) ph))) p0016
  have p0018 := @g_nfnae x y z
  have p0019 := @g_sb4b ph x y
  have p0020 :=
    @g_nfbidf (.neg (.all x (.objEq x y))) (syn_wsb y x ph)
      (.all x (.imp (.objEq x y) ph)) z p0018 p0019
  have p0021 :=
    @g_imbi2d (.neg (.all x (.objEq x y))) (syn_wnf z (syn_wsb y x ph))
      (syn_wnf z (.all x (.imp (.objEq x y) ph)))
      (syn_wa (.neg (.all z (.objEq z x))) (.neg (.all z (.objEq z y)))) p0020
  have p0022 :=
    @g_syl5ibrcom (.all x (syn_wnf z ph))
      (.imp (syn_wa (.neg (.all z (.objEq z x))) (.neg (.all z (.objEq z y))))
        (syn_wnf z (syn_wsb y x ph)))
      (.neg (.all x (.objEq x y)))
      (.imp (syn_wa (.neg (.all z (.objEq z x))) (.neg (.all z (.objEq z y))))
        (syn_wnf z (.all x (.imp (.objEq x y) ph))))
      p0017 p0021
  have p0023 :=
    @g_pm2_61d (.all x (syn_wnf z ph)) (.all x (.objEq x y))
      (.imp (syn_wa (.neg (.all z (.objEq z x))) (.neg (.all z (.objEq z y))))
        (syn_wnf z (syn_wsb y x ph)))
      p0005 p0022
  have p0024 :=
    @g_exp3a (.all x (syn_wnf z ph)) (.neg (.all z (.objEq z x)))
      (.neg (.all z (.objEq z y))) (syn_wnf z (syn_wsb y x ph)) p0023
  have p0025 := @g_nfsb2 ph z y
  have p0026 := @g_drsb1 ph z x y
  have p0027 := @g_drnf2 (syn_wsb y z ph) (syn_wsb y x ph) z x z p0026
  have p0028 :=
    @g_syl5ib (.neg (.all z (.objEq z y))) (syn_wnf z (syn_wsb y z ph))
      (.all z (.objEq z x)) (syn_wnf z (syn_wsb y x ph)) p0025 p0027
  have p0029 :=
    @g_pm2_61d2 (.all x (syn_wnf z ph)) (.all z (.objEq z x))
      (.imp (.neg (.all z (.objEq z y))) (syn_wnf z (syn_wsb y x ph))) p0024 p0028
  exact p0029

@[expose]
noncomputable def g_nfsb4 (ph : Wff) (x : Var) (y : Var) (z : Var)
    (hyp_nfsb4_1 : Nominal.NPrf (syn_wnf z ph)) :
    Nominal.NPrf (.imp (.neg (.all z (.objEq z y))) (syn_wnf z (syn_wsb y x ph))) :=
  by
  have p0000 := @g_nfsb4t ph x y z
  have p0001 :=
    @g_mpg (syn_wnf z ph) (.imp (.neg (.all z (.objEq z y))) (syn_wnf z (syn_wsb y x ph)))
      x p0000 hyp_nfsb4_1
  exact p0001

@[expose]
noncomputable def g_dvelimdf (ph : Wff) (ps : Wff) (ch : Wff) (x : Var) (y : Var)
    (z : Var) (hyp_dvelimdf_1 : Nominal.NPrf (syn_wnf x ph))
    (hyp_dvelimdf_2 : Nominal.NPrf (syn_wnf z ph))
    (hyp_dvelimdf_3 : Nominal.NPrf (.imp ph (syn_wnf x ps)))
    (hyp_dvelimdf_4 : Nominal.NPrf (.imp ph (syn_wnf z ch)))
    (hyp_dvelimdf_5 : Nominal.NPrf (.imp ph (.imp (.objEq z y) (syn_wb ps ch)))) :
    Nominal.NPrf (.imp ph (.imp (.neg (.all x (.objEq x y))) (syn_wnf x ch))) :=
  by
  have p0000 := @g_alrimi ph (syn_wnf x ps) z hyp_dvelimdf_2 hyp_dvelimdf_3
  have p0001 := @g_nfsb4t ps z y x
  have p0002 :=
    @g_syl ph (.all z (syn_wnf x ps))
      (.imp (.neg (.all x (.objEq x y))) (syn_wnf x (syn_wsb y z ps))) p0000 p0001
  have p0003 := @g_imp ph (.neg (.all x (.objEq x y))) (syn_wnf x (syn_wsb y z ps)) p0002
  have p0004 := @g_nfnae x y x
  have p0005 := @g_nfan ph (.neg (.all x (.objEq x y))) x hyp_dvelimdf_1 p0004
  have p0006 := @g_sbied ph ps ch z y hyp_dvelimdf_2 hyp_dvelimdf_4 hyp_dvelimdf_5
  have p0007 :=
    @g_adantr ph (syn_wb (syn_wsb y z ps) ch) (.neg (.all x (.objEq x y))) p0006
  have p0008 :=
    @g_nfbidf (syn_wa ph (.neg (.all x (.objEq x y)))) (syn_wsb y z ps) ch x p0005 p0007
  have p0009 :=
    @g_mpbid (syn_wa ph (.neg (.all x (.objEq x y)))) (syn_wnf x (syn_wsb y z ps))
      (syn_wnf x ch) p0003 p0008
  have p0010 := @g_ex ph (.neg (.all x (.objEq x y))) (syn_wnf x ch) p0009
  exact p0010

@[expose]
noncomputable def g_sbco (ph : Wff) (x : Var) (y : Var) :
    Nominal.NPrf (syn_wb (syn_wsb y x (syn_wsb x y ph)) (syn_wsb y x ph)) :=
  by
  have p0000 := @g_equsb2 x y
  have p0001 := @g_sbequ12 ph y x
  have p0002 := @g_bicomd (.objEq y x) ph (syn_wsb x y ph) p0001
  have p0003 := @g_sbimi (.objEq y x) (syn_wb (syn_wsb x y ph) ph) x y p0002
  have p0004 := Nominal.mp p0000 p0003
  have p0005 := @g_sbbi (syn_wsb x y ph) ph x y
  have p0006 :=
    @g_mpbi (syn_wsb y x (syn_wb (syn_wsb x y ph) ph))
      (syn_wb (syn_wsb y x (syn_wsb x y ph)) (syn_wsb y x ph)) p0004 p0005
  exact p0006

@[expose]
noncomputable def g_sbid2 (ph : Wff) (x : Var) (y : Var)
    (hyp_sbid2_1 : Nominal.NPrf (syn_wnf x ph)) :
    Nominal.NPrf (syn_wb (syn_wsb y x (syn_wsb x y ph)) ph) :=
  by
  have p0000 := @g_sbco ph x y
  have p0001 := @g_sbf ph x y hyp_sbid2_1
  have p0002 := @g_bitri (syn_wsb y x (syn_wsb x y ph)) (syn_wsb y x ph) ph p0000 p0001
  exact p0002

@[expose]
noncomputable def g_sbco2 (ph : Wff) (x : Var) (y : Var) (z : Var)
    (hyp_sbco2_1 : Nominal.NPrf (syn_wnf z ph)) :
    Nominal.NPrf (syn_wb (syn_wsb y z (syn_wsb z x ph)) (syn_wsb y x ph)) :=
  by
  have p0000 := @g_sbid2 ph z x hyp_sbco2_1
  have p0001 := @g_sbequ (syn_wsb z x ph) x y z
  have p0002 :=
    @g_syl5bbr ph (syn_wsb x z (syn_wsb z x ph)) (.objEq x y)
      (syn_wsb y z (syn_wsb z x ph)) p0000 p0001
  have p0003 := @g_sbequ12 ph x y
  have p0004 :=
    @g_bitr3d (.objEq x y) ph (syn_wsb y z (syn_wsb z x ph)) (syn_wsb y x ph) p0002 p0003
  have p0005 :=
    @g_sps (.objEq x y) (syn_wb (syn_wsb y z (syn_wsb z x ph)) (syn_wsb y x ph)) x p0004
  have p0006 := @g_nfnae x y x
  have p0007 := @g_nfs1 ph x z hyp_sbco2_1
  have p0008 := @g_nfsb4 (syn_wsb z x ph) z y x p0007
  have p0009 :=
    @g_a1i (.imp (.objEq x y) (syn_wb ph (syn_wsb y z (syn_wsb z x ph))))
      (.neg (.all x (.objEq x y))) p0002
  have p0010 :=
    @g_sbied (.neg (.all x (.objEq x y))) ph (syn_wsb y z (syn_wsb z x ph)) x y p0006
      p0008 p0009
  have p0011 :=
    @g_bicomd (.neg (.all x (.objEq x y))) (syn_wsb y x ph) (syn_wsb y z (syn_wsb z x ph))
      p0010
  have p0012 :=
    @g_pm2_61i (.all x (.objEq x y))
      (syn_wb (syn_wsb y z (syn_wsb z x ph)) (syn_wsb y x ph)) p0005 p0011
  exact p0012

@[expose]
noncomputable def g_sb6rf (ph : Wff) (x : Var) (y : Var)
    (hyp_sb5rf_1 : Nominal.NPrf (syn_wnf y ph)) :
    Nominal.NPrf (syn_wb ph (.all y (.imp (.objEq y x) (syn_wsb y x ph)))) :=
  by
  have p0000 := @g_sbequ1 ph x y
  have p0001 := @g_equcoms (.imp ph (syn_wsb y x ph)) x y p0000
  have p0002 := @g_com12 (.objEq y x) ph (syn_wsb y x ph) p0001
  have p0003 := @g_alrimi ph (.imp (.objEq y x) (syn_wsb y x ph)) y hyp_sb5rf_1 p0002
  have p0004 := @g_sb2 (syn_wsb y x ph) y x
  have p0005 := @g_sbid2 ph y x hyp_sb5rf_1
  have p0006 :=
    @g_sylib (.all y (.imp (.objEq y x) (syn_wsb y x ph))) (syn_wsb x y (syn_wsb y x ph))
      ph p0004 p0005
  have p0007 := @g_impbii ph (.all y (.imp (.objEq y x) (syn_wsb y x ph))) p0003 p0006
  exact p0007

@[expose]
noncomputable def g_sb8 (ph : Wff) (x : Var) (y : Var)
    (hyp_sb5rf_1 : Nominal.NPrf (syn_wnf y ph)) :
    Nominal.NPrf (syn_wb (.all x ph) (.all y (syn_wsb y x ph))) :=
  by
  have p0000 := @g_nfal ph y x hyp_sb5rf_1
  have p0001 := @g_stdpc4 ph x y
  have p0002 := @g_alrimi (.all x ph) (syn_wsb y x ph) y p0000 p0001
  have p0003 := @g_nfs1 ph x y hyp_sb5rf_1
  have p0004 := @g_stdpc7 ph y x
  have p0005 := @g_cbv3 (syn_wsb y x ph) ph y x p0003 hyp_sb5rf_1 p0004
  have p0006 := @g_impbii (.all x ph) (.all y (syn_wsb y x ph)) p0002 p0005
  exact p0006

@[expose]
noncomputable def g_ax11v (ph : Wff) (x : Var) (y : Var) (dv_x_y : x ≠ y) :
    Nominal.NPrf (.imp (.objEq x y) (.imp ph (.all x (.imp (.objEq x y) ph)))) :=
  by
  let proofSupport : Finset Var := ph.fv ∪ ({ x } : Finset Var) ∪ ({ y } : Finset Var)
  have p0000 := Nominal.ax1 ph (.objEq x y)
  have p0001 :=
    @g_ax16 (.imp (.objEq x y) ph) x y
      (by
        first
        | (aesop))
  have p0002 :=
    @g_syl5 ph (.imp (.objEq x y) ph) (.all x (.objEq x y))
      (.all x (.imp (.objEq x y) ph)) p0000 p0001
  have p0003 :=
    @g_a1d (.all x (.objEq x y)) (.imp ph (.all x (.imp (.objEq x y) ph))) (.objEq x y)
      p0002
  have p0004 := @g_ax11o ph x y
  have p0005 :=
    @g_pm2_61i (.all x (.objEq x y))
      (.imp (.objEq x y) (.imp ph (.all x (.imp (.objEq x y) ph)))) p0003 p0004
  exact p0005

@[expose]
noncomputable def g_sb56 (ph : Wff) (x : Var) (y : Var) (dv_x_y : x ≠ y) :
    Nominal.NPrf
      (syn_wb (syn_wex x (syn_wa (.objEq x y) ph)) (.all x (.imp (.objEq x y) ph))) :=
  by
  let proofSupport : Finset Var := ph.fv ∪ ({ x } : Finset Var) ∪ ({ y } : Finset Var)
  have p0000 := @g_nfa1 (.imp (.objEq x y) ph) x
  have p0001 :=
    @g_ax11v ph x y
      (by
        first
        | (aesop))
  have p0002 := @g_sp (.imp (.objEq x y) ph) x
  have p0003 := @g_com12 (.all x (.imp (.objEq x y) ph)) (.objEq x y) ph p0002
  have p0004 := @g_impbid (.objEq x y) ph (.all x (.imp (.objEq x y) ph)) p0001 p0003
  have p0005 := @g_equsex ph (.all x (.imp (.objEq x y) ph)) x y p0000 p0004
  exact p0005

@[expose]
noncomputable def g_sb6 (ph : Wff) (x : Var) (y : Var) (dv_x_y : x ≠ y) :
    Nominal.NPrf (syn_wb (syn_wsb y x ph) (.all x (.imp (.objEq x y) ph))) :=
  by
  let proofSupport : Finset Var := ph.fv ∪ ({ x } : Finset Var) ∪ ({ y } : Finset Var)
  have p0000 :=
    @g_sb56 ph x y
      (by
        first
        | (aesop))
  have p0001 :=
    @g_anbi2i (syn_wex x (syn_wa (.objEq x y) ph)) (.all x (.imp (.objEq x y) ph))
      (.imp (.objEq x y) ph) p0000
  have p0002 := (Nominal.biimpRefl (syn_wsb y x ph))
  have p0003 := @g_sp (.imp (.objEq x y) ph) x
  have p0004 := @g_pm4_71ri (.all x (.imp (.objEq x y) ph)) (.imp (.objEq x y) ph) p0003
  have p0005 :=
    @g_n_3bitr4i (syn_wa (.imp (.objEq x y) ph) (syn_wex x (syn_wa (.objEq x y) ph)))
      (syn_wa (.imp (.objEq x y) ph) (.all x (.imp (.objEq x y) ph))) (syn_wsb y x ph)
      (.all x (.imp (.objEq x y) ph)) p0001 p0002 p0004
  exact p0005

@[expose]
noncomputable def g_sb5 (ph : Wff) (x : Var) (y : Var) (dv_x_y : x ≠ y) :
    Nominal.NPrf (syn_wb (syn_wsb y x ph) (syn_wex x (syn_wa (.objEq x y) ph))) :=
  by
  let proofSupport : Finset Var := ph.fv ∪ ({ x } : Finset Var) ∪ ({ y } : Finset Var)
  have p0000 :=
    @g_sb6 ph x y
      (by
        first
        | (aesop))
  have p0001 :=
    @g_sb56 ph x y
      (by
        first
        | (aesop))
  have p0002 :=
    @g_bitr4i (syn_wsb y x ph) (.all x (.imp (.objEq x y) ph))
      (syn_wex x (syn_wa (.objEq x y) ph)) p0000 p0001
  exact p0002

@[expose]
noncomputable def g_equsb3lem (x : Var) (y : Var) (z : Var) (dv_x_y : x ≠ y)
    (dv_x_z : x ≠ z) : Nominal.NPrf (syn_wb (syn_wsb y x (.objEq x z)) (.objEq y z)) :=
  by
  let proofSupport : Finset Var :=
    ({ x } : Finset Var) ∪ ({ y } : Finset Var) ∪ ({ z } : Finset Var)
  have p0000 :=
    @g_nfv (.objEq y z) x
      (by
        first
        |
          (simp (config :=
              {
                failIfUnchanged :=
                  false }) only [NFChoice.Compiler.CoreFVSimp.fv_wff_objEq] at ⊢;
            aesop))
  have p0001 := @g_equequ1 x y z
  have p0002 := @g_sbie (.objEq x z) (.objEq y z) x y p0000 p0001
  exact p0002

@[expose]
noncomputable def g_equsb3 (x : Var) (y : Var) (z : Var) (dv_x_z : x ≠ z) :
    Nominal.NPrf (syn_wb (syn_wsb y x (.objEq x z)) (.objEq y z)) :=
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
    @g_equsb3lem x w z
      (by
        first
        | (aesop))
      (by
        first
        | (aesop))
  have p0001 := @g_sbbii (syn_wsb w x (.objEq x z)) (.objEq w z) w y p0000
  have p0002 :=
    @g_nfv (.objEq x z) w
      (by
        first
        |
          (simp (config :=
              {
                failIfUnchanged :=
                  false }) only [NFChoice.Compiler.CoreFVSimp.fv_wff_objEq] at ⊢;
            aesop))
  have p0003 := @g_sbco2 (.objEq x z) x y w p0002
  have p0004 :=
    @g_equsb3lem w y z
      (by
        first
        | (aesop))
      (by
        first
        | (aesop))
  have p0005 :=
    @g_n_3bitr3i (syn_wsb y w (syn_wsb w x (.objEq x z))) (syn_wsb y w (.objEq w z))
      (syn_wsb y x (.objEq x z)) (.objEq y z) p0001 p0003 p0004
  exact p0005

@[expose]
noncomputable def g_hbs1 (ph : Wff) (x : Var) (y : Var) (dv_x_y : x ≠ y) :
    Nominal.NPrf (.imp (syn_wsb y x ph) (.all x (syn_wsb y x ph))) :=
  by
  let proofSupport : Finset Var := ph.fv ∪ ({ x } : Finset Var) ∪ ({ y } : Finset Var)
  have p0000 :=
    @g_ax16 (syn_wsb y x ph) x y
      (by
        first
        | (aesop))
  have p0001 := @g_hbsb2 ph x y
  have p0002 :=
    @g_pm2_61i (.all x (.objEq x y)) (.imp (syn_wsb y x ph) (.all x (syn_wsb y x ph)))
      p0000 p0001
  exact p0002

@[expose]
noncomputable def g_nfs1v (ph : Wff) (x : Var) (y : Var) (dv_x_y : x ≠ y) :
    Nominal.NPrf (syn_wnf x (syn_wsb y x ph)) :=
  by
  let proofSupport : Finset Var := ph.fv ∪ ({ x } : Finset Var) ∪ ({ y } : Finset Var)
  have p0000 :=
    @g_hbs1 ph x y
      (by
        first
        | (aesop))
  have p0001 := @g_nfi (syn_wsb y x ph) x p0000
  exact p0001

@[expose]
noncomputable def g_nfsb (ph : Wff) (x : Var) (y : Var) (z : Var) (dv_y_z : y ≠ z)
    (hyp_nfsb_1 : Nominal.NPrf (syn_wnf z ph)) :
    Nominal.NPrf (syn_wnf z (syn_wsb y x ph)) :=
  by
  let proofSupport : Finset Var :=
    ph.fv ∪ ({ x } : Finset Var) ∪ ({ y } : Finset Var) ∪ ({ z } : Finset Var)
  have p0000 :=
    @g_a16nf (syn_wsb y x ph) z y z
      (by
        first
        | (aesop))
  have p0001 := @g_nfsb4 ph x y z hyp_nfsb_1
  have p0002 := @g_pm2_61i (.all z (.objEq z y)) (syn_wnf z (syn_wsb y x ph)) p0000 p0001
  exact p0002

@[expose]
noncomputable def g_hbsb (ph : Wff) (x : Var) (y : Var) (z : Var) (dv_y_z : y ≠ z)
    (hyp_hbsb_1 : Nominal.NPrf (.imp ph (.all z ph))) :
    Nominal.NPrf (.imp (syn_wsb y x ph) (.all z (syn_wsb y x ph))) :=
  by
  let proofSupport : Finset Var :=
    ph.fv ∪ ({ x } : Finset Var) ∪ ({ y } : Finset Var) ∪ ({ z } : Finset Var)
  have p0000 := @g_nfi ph z hyp_hbsb_1
  have p0001 :=
    @g_nfsb ph x y z
      (by
        first
        | (aesop))
      p0000
  have p0002 := @g_nfri (syn_wsb y x ph) z p0001
  exact p0002

@[expose]
noncomputable def g_nfsbd (ph : Wff) (ps : Wff) (x : Var) (y : Var) (z : Var)
    (dv_y_z : y ≠ z) (hyp_nfsbd_1 : Nominal.NPrf (syn_wnf x ph))
    (hyp_nfsbd_2 : Nominal.NPrf (.imp ph (syn_wnf z ps))) :
    Nominal.NPrf (.imp ph (syn_wnf z (syn_wsb y x ps))) :=
  by
  let proofSupport : Finset Var :=
    ph.fv ∪ ps.fv ∪ ({ x } : Finset Var) ∪ ({ y } : Finset Var) ∪ ({ z } : Finset Var)
  have p0000 := @g_alrimi ph (syn_wnf z ps) x hyp_nfsbd_1 hyp_nfsbd_2
  have p0001 := @g_nfsb4t ps x y z
  have p0002 :=
    @g_syl ph (.all x (syn_wnf z ps))
      (.imp (.neg (.all z (.objEq z y))) (syn_wnf z (syn_wsb y x ps))) p0000 p0001
  have p0003 :=
    @g_a16nf (syn_wsb y x ps) z y z
      (by
        first
        | (aesop))
  have p0004 :=
    @g_pm2_61d2 ph (.all z (.objEq z y)) (syn_wnf z (syn_wsb y x ps)) p0002 p0003
  exact p0004

@[expose]
noncomputable def g_euf (ph : Wff) (x : Var) (y : Var) (dv_x_y : x ≠ y)
    (hyp_euf_1 : Nominal.NPrf (syn_wnf y ph)) :
    Nominal.NPrf
      (syn_wb (syn_weu x ph) (syn_wex y (.all x (syn_wb ph (.classEq (.cv x) (.cv y)))))) :=
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
    @g_nfv (.classEq (.cv x) (.cv z)) y
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
  have p0002 := @g_nfbi ph (.classEq (.cv x) (.cv z)) y hyp_euf_1 p0001
  have p0003 := @g_nfal (syn_wb ph (.classEq (.cv x) (.cv z))) y x p0002
  have p0004 :=
    @g_nfv ph z
      (by
        first
        | (aesop))
  have p0005 :=
    @g_nfv (.classEq (.cv x) (.cv y)) z
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
  have p0006 := @g_nfbi ph (.classEq (.cv x) (.cv y)) z p0004 p0005
  have p0007 := @g_nfal (syn_wb ph (.classEq (.cv x) (.cv y))) z x p0006
  have p0008 := @g_equequ2 z y x
  have p0009_e00_recanon :
    Nominal.NPrf
      (.imp (.classEq (.cv z) (.cv y))
        (syn_wb (.classEq (.cv x) (.cv z)) (.classEq (.cv x) (.cv y)))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wb
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
    @g_bibi2d (.classEq (.cv z) (.cv y)) (.classEq (.cv x) (.cv z))
      (.classEq (.cv x) (.cv y)) ph p0009_e00_recanon
  have p0010 :=
    @g_albidv (.classEq (.cv z) (.cv y)) (syn_wb ph (.classEq (.cv x) (.cv z)))
      (syn_wb ph (.classEq (.cv x) (.cv y))) x
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
      (.imp (.objEq z y) (syn_wb (.all x (syn_wb ph (.classEq (.cv x) (.cv z))))
          (.all x (syn_wb ph (.classEq (.cv x) (.cv y)))))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wb
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
        · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0010
  have p0011 :=
    @g_cbvex (.all x (syn_wb ph (.classEq (.cv x) (.cv z))))
      (.all x (syn_wb ph (.classEq (.cv x) (.cv y)))) z y p0003 p0007 p0011_e02_recanon
  have p0012_e00_recanon :
    Nominal.NPrf
      (syn_wb (syn_weu x ph) (syn_wex z (.all x (syn_wb ph (.classEq (.cv x) (.cv z)))))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wb syn_weu syn_wex
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
    @g_bitri (syn_weu x ph) (syn_wex z (.all x (syn_wb ph (.classEq (.cv x) (.cv z)))))
      (syn_wex y (.all x (syn_wb ph (.classEq (.cv x) (.cv y))))) p0012_e00_recanon p0011
  exact p0012

@[expose]
noncomputable def g_eubid (ph : Wff) (ps : Wff) (ch : Wff) (x : Var)
    (hyp_eubid_1 : Nominal.NPrf (syn_wnf x ph))
    (hyp_eubid_2 : Nominal.NPrf (.imp ph (syn_wb ps ch))) :
    Nominal.NPrf (.imp ph (syn_wb (syn_weu x ps) (syn_weu x ch))) :=
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
  have p0000 := @g_bibi1d ph ps ch (.classEq (.cv x) (.cv y)) hyp_eubid_2
  have p0001 :=
    @g_albid ph (syn_wb ps (.classEq (.cv x) (.cv y)))
      (syn_wb ch (.classEq (.cv x) (.cv y))) x hyp_eubid_1 p0000
  have p0002 :=
    @g_exbidv ph (.all x (syn_wb ps (.classEq (.cv x) (.cv y))))
      (.all x (syn_wb ch (.classEq (.cv x) (.cv y)))) y
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
      (syn_wb (syn_weu x ps) (syn_wex y (.all x (syn_wb ps (.classEq (.cv x) (.cv y)))))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wb syn_weu syn_wex
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
      (syn_wb (syn_weu x ch) (syn_wex y (.all x (syn_wb ch (.classEq (.cv x) (.cv y)))))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wb syn_weu syn_wex
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
    @g_n_3bitr4g ph (syn_wex y (.all x (syn_wb ps (.classEq (.cv x) (.cv y)))))
      (syn_wex y (.all x (syn_wb ch (.classEq (.cv x) (.cv y))))) (syn_weu x ps)
      (syn_weu x ch) p0002 p0005_e01_recanon p0005_e02_recanon
  exact p0005

@[expose]
noncomputable def g_eubidv (ph : Wff) (ps : Wff) (ch : Wff) (x : Var)
    (dv_ph_x : x ∉ ph.fv) (hyp_eubidv_1 : Nominal.NPrf (.imp ph (syn_wb ps ch))) :
    Nominal.NPrf (.imp ph (syn_wb (syn_weu x ps) (syn_weu x ch))) :=
  by
  let proofSupport : Finset Var := ph.fv ∪ ps.fv ∪ ch.fv ∪ ({ x } : Finset Var)
  have p0000 :=
    @g_nfv ph x
      (by
        first
        | (aesop))
  have p0001 := @g_eubid ph ps ch x p0000 hyp_eubidv_1
  exact p0001

@[expose]
noncomputable def g_eubii (ph : Wff) (ps : Wff) (x : Var)
    (hyp_eubii_1 : Nominal.NPrf (syn_wb ph ps)) :
    Nominal.NPrf (syn_wb (syn_weu x ph) (syn_weu x ps)) :=
  by
  let proofSupport : Finset Var := ph.fv ∪ ps.fv ∪ ({ x } : Finset Var)
  have p0000 := @g_a1i (syn_wb ph ps) syn_wtru hyp_eubii_1
  have p0001 :=
    @g_eubidv syn_wtru ph ps x
      (by
        first
        |
          (simp (config :=
              {
                failIfUnchanged :=
                  false }) only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wtru] at ⊢;
            aesop))
      p0000
  have p0002 := @g_trud (syn_wb (syn_weu x ph) (syn_weu x ps)) p0001
  exact p0002

@[expose]
noncomputable def g_nfeu1 (ph : Wff) (x : Var) :
    Nominal.NPrf (syn_wnf x (syn_weu x ph)) :=
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
  have p0001 := @g_nfa1 (syn_wb ph (.classEq (.cv x) (.cv y))) x
  have p0002 := @g_nfex (.all x (syn_wb ph (.classEq (.cv x) (.cv y)))) x y p0001
  have p0003_e00_recanon :
    Nominal.NPrf
      (syn_wb (syn_weu x ph) (syn_wex y (.all x (syn_wb ph (.classEq (.cv x) (.cv y)))))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wb syn_weu syn_wex
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
    @g_nfxfr (syn_weu x ph) (syn_wex y (.all x (syn_wb ph (.classEq (.cv x) (.cv y))))) x
      p0003_e00_recanon p0002
  exact p0003

@[expose]
noncomputable def g_nfmo1 (ph : Wff) (x : Var) :
    Nominal.NPrf (syn_wnf x (syn_wmo x ph)) :=
  by
  have p0000 := (Nominal.biimpRefl (syn_wmo x ph))
  have p0001 := @g_nfe1 ph x
  have p0002 := @g_nfeu1 ph x
  have p0003 := @g_nfim (syn_wex x ph) (syn_weu x ph) x p0001 p0002
  have p0004 := @g_nfxfr (syn_wmo x ph) (.imp (syn_wex x ph) (syn_weu x ph)) x p0000 p0003
  exact p0004

@[expose]
noncomputable def g_nfeud2 (ph : Wff) (ps : Wff) (x : Var) (y : Var)
    (hyp_nfeud2_1 : Nominal.NPrf (syn_wnf y ph))
    (hyp_nfeud2_2 :
      Nominal.NPrf (.imp (syn_wa ph (.neg (.all x (.objEq x y)))) (syn_wnf x ps))) :
    Nominal.NPrf (.imp ph (syn_wnf x (syn_weu y ps))) :=
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
    @g_nfv ph z
      (by
        first
        | (aesop))
  have p0002 := @g_nfnae x z y
  have p0003_e01_recanon :
    Nominal.NPrf (syn_wnf y (.neg (.all x (.classEq (.cv x) (.cv z))))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wnf
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
    @g_nfan ph (.neg (.all x (.classEq (.cv x) (.cv z)))) y hyp_nfeud2_1 p0003_e01_recanon
  have p0004_e00_recanon :
    Nominal.NPrf
      (.imp (syn_wa ph (.neg (.all x (.classEq (.cv x) (.cv y))))) (syn_wnf x ps)) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wa syn_wnf
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
    @g_adantlr ph (.neg (.all x (.classEq (.cv x) (.cv y)))) (syn_wnf x ps)
      (.neg (.all x (.classEq (.cv x) (.cv z)))) p0004_e00_recanon
  have p0005 := @g_nfeqf y z x
  have p0006_e00_recanon :
    Nominal.NPrf
      (.imp (syn_wa (.neg (.all x (.classEq (.cv x) (.cv y))))
          (.neg (.all x (.classEq (.cv x) (.cv z))))) (syn_wnf x (.classEq (.cv y) (.cv z)))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wa syn_wnf
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
    @g_ancoms (.neg (.all x (.classEq (.cv x) (.cv y))))
      (.neg (.all x (.classEq (.cv x) (.cv z)))) (syn_wnf x (.classEq (.cv y) (.cv z)))
      p0006_e00_recanon
  have p0007 :=
    @g_adantll (.neg (.all x (.classEq (.cv x) (.cv z))))
      (.neg (.all x (.classEq (.cv x) (.cv y)))) (syn_wnf x (.classEq (.cv y) (.cv z))) ph
      p0006
  have p0008 :=
    @g_nfbid
      (syn_wa (syn_wa ph (.neg (.all x (.classEq (.cv x) (.cv z)))))
        (.neg (.all x (.classEq (.cv x) (.cv y)))))
      ps (.classEq (.cv y) (.cv z)) x p0004 p0007
  have p0009_e01_recanon :
    Nominal.NPrf
      (.imp (syn_wa (syn_wa ph (.neg (.all x (.classEq (.cv x) (.cv z)))))
          (.neg (.all x (.objEq x y)))) (syn_wnf x (syn_wb ps (.classEq (.cv y) (.cv z))))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wa syn_wnf syn_wb
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
    @g_nfald2 (syn_wa ph (.neg (.all x (.classEq (.cv x) (.cv z)))))
      (syn_wb ps (.classEq (.cv y) (.cv z))) x y p0003 p0009_e01_recanon
  have p0010_e01_recanon :
    Nominal.NPrf
      (.imp (syn_wa ph (.neg (.all x (.objEq x z))))
        (syn_wnf x (.all y (syn_wb ps (.classEq (.cv y) (.cv z)))))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wa syn_wnf syn_wb
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
    @g_nfexd2 ph (.all y (syn_wb ps (.classEq (.cv y) (.cv z)))) x z p0001
      p0010_e01_recanon
  have p0011_e00_recanon :
    Nominal.NPrf
      (syn_wb (syn_weu y ps) (syn_wex z (.all y (syn_wb ps (.classEq (.cv y) (.cv z)))))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wb syn_weu syn_wex
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
    @g_nfxfrd (syn_weu y ps) (syn_wex z (.all y (syn_wb ps (.classEq (.cv y) (.cv z)))))
      ph x p0011_e00_recanon p0010
  exact p0011

@[expose]
noncomputable def g_nfmod2 (ph : Wff) (ps : Wff) (x : Var) (y : Var)
    (hyp_nfeud2_1 : Nominal.NPrf (syn_wnf y ph))
    (hyp_nfeud2_2 :
      Nominal.NPrf (.imp (syn_wa ph (.neg (.all x (.objEq x y)))) (syn_wnf x ps))) :
    Nominal.NPrf (.imp ph (syn_wnf x (syn_wmo y ps))) :=
  by
  have p0000 := (Nominal.biimpRefl (syn_wmo y ps))
  have p0001 := @g_nfexd2 ph ps x y hyp_nfeud2_1 hyp_nfeud2_2
  have p0002 := @g_nfeud2 ph ps x y hyp_nfeud2_1 hyp_nfeud2_2
  have p0003 := @g_nfimd ph (syn_wex y ps) (syn_weu y ps) x p0001 p0002
  have p0004 :=
    @g_nfxfrd (syn_wmo y ps) (.imp (syn_wex y ps) (syn_weu y ps)) ph x p0000 p0003
  exact p0004

@[expose]
noncomputable def g_nfmod (ph : Wff) (ps : Wff) (x : Var) (y : Var)
    (hyp_nfeud_1 : Nominal.NPrf (syn_wnf y ph))
    (hyp_nfeud_2 : Nominal.NPrf (.imp ph (syn_wnf x ps))) :
    Nominal.NPrf (.imp ph (syn_wnf x (syn_wmo y ps))) :=
  by
  have p0000 :=
    @g_adantr ph (syn_wnf x ps) (.neg (.all x (.classEq (.cv x) (.cv y)))) hyp_nfeud_2
  have p0001_e01_recanon :
    Nominal.NPrf (.imp (syn_wa ph (.neg (.all x (.objEq x y)))) (syn_wnf x ps)) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wa syn_wnf
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
  have p0001 := @g_nfmod2 ph ps x y hyp_nfeud_1 p0001_e01_recanon
  exact p0001

@[expose]
noncomputable def g_nfmo (ph : Wff) (x : Var) (y : Var)
    (hyp_nfeu_1 : Nominal.NPrf (syn_wnf x ph)) :
    Nominal.NPrf (syn_wnf x (syn_wmo y ph)) :=
  by
  have p0000 := @g_nftru y
  have p0001 := @g_a1i (syn_wnf x ph) syn_wtru hyp_nfeu_1
  have p0002 := @g_nfmod syn_wtru ph x y p0000 p0001
  have p0003 := @g_trud (syn_wnf x (syn_wmo y ph)) p0002
  exact p0003

@[expose]
noncomputable def g_sb8eu (ph : Wff) (x : Var) (y : Var)
    (hyp_sb8eu_1 : Nominal.NPrf (syn_wnf y ph)) :
    Nominal.NPrf (syn_wb (syn_weu x ph) (syn_weu y (syn_wsb y x ph))) :=
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
    @g_nfv (syn_wb ph (.classEq (.cv x) (.cv z))) w
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
  have p0001 := @g_sb8 (syn_wb ph (.classEq (.cv x) (.cv z))) x w p0000
  have p0002 := @g_sbbi ph (.classEq (.cv x) (.cv z)) x w
  have p0003 :=
    @g_nfsb ph x w y
      (by
        first
        | (aesop))
      hyp_sb8eu_1
  have p0004 :=
    @g_equsb3 x w z
      (by
        first
        | (aesop))
  have p0005 :=
    @g_nfv (.classEq (.cv w) (.cv z)) y
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
      (syn_wb (syn_wsb w x (.classEq (.cv x) (.cv z))) (.classEq (.cv w) (.cv z))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wb syn_wsb syn_wa syn_wex
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
    @g_nfxfr (syn_wsb w x (.classEq (.cv x) (.cv z))) (.classEq (.cv w) (.cv z)) y
      p0006_e00_recanon p0005
  have p0007 :=
    @g_nfbi (syn_wsb w x ph) (syn_wsb w x (.classEq (.cv x) (.cv z))) y p0003 p0006
  have p0008 :=
    @g_nfxfr (syn_wsb w x (syn_wb ph (.classEq (.cv x) (.cv z))))
      (syn_wb (syn_wsb w x ph) (syn_wsb w x (.classEq (.cv x) (.cv z)))) y p0002 p0007
  have p0009 :=
    @g_nfv (syn_wsb y x (syn_wb ph (.classEq (.cv x) (.cv z)))) w
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
  have p0010 := @g_sbequ (syn_wb ph (.classEq (.cv x) (.cv z))) w y x
  have p0011 :=
    @g_cbval (syn_wsb w x (syn_wb ph (.classEq (.cv x) (.cv z))))
      (syn_wsb y x (syn_wb ph (.classEq (.cv x) (.cv z)))) w y p0008 p0009 p0010
  have p0012 :=
    @g_equsb3 x y z
      (by
        first
        | (aesop))
  have p0013_e00_recanon :
    Nominal.NPrf
      (syn_wb (syn_wsb y x (.classEq (.cv x) (.cv z))) (.classEq (.cv y) (.cv z))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wb syn_wsb syn_wa syn_wex
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
    @g_sblbis (.classEq (.cv x) (.cv z)) (.classEq (.cv y) (.cv z)) ph x y
      p0013_e00_recanon
  have p0014 :=
    @g_albii (syn_wsb y x (syn_wb ph (.classEq (.cv x) (.cv z))))
      (syn_wb (syn_wsb y x ph) (.classEq (.cv y) (.cv z))) y p0013
  have p0015 :=
    @g_n_3bitri (.all x (syn_wb ph (.classEq (.cv x) (.cv z))))
      (.all w (syn_wsb w x (syn_wb ph (.classEq (.cv x) (.cv z)))))
      (.all y (syn_wsb y x (syn_wb ph (.classEq (.cv x) (.cv z)))))
      (.all y (syn_wb (syn_wsb y x ph) (.classEq (.cv y) (.cv z)))) p0001 p0011 p0014
  have p0016 :=
    @g_exbii (.all x (syn_wb ph (.classEq (.cv x) (.cv z))))
      (.all y (syn_wb (syn_wsb y x ph) (.classEq (.cv y) (.cv z)))) z p0015
  have p0017 :=
    Nominal.dfEu x z ph
      (by
        first
        | (aesop))
      (by
        first
        | (aesop))
  have p0018 :=
    Nominal.dfEu y z (syn_wsb y x ph)
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
      (syn_wb (syn_weu x ph) (syn_wex z (.all x (syn_wb ph (.classEq (.cv x) (.cv z)))))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wb syn_weu syn_wex
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
      (syn_wb (syn_weu y (syn_wsb y x ph))
        (syn_wex z (.all y (syn_wb (syn_wsb y x ph) (.classEq (.cv y) (.cv z)))))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wb syn_weu syn_wex syn_wsb syn_wa
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
    @g_n_3bitr4i (syn_wex z (.all x (syn_wb ph (.classEq (.cv x) (.cv z)))))
      (syn_wex z (.all y (syn_wb (syn_wsb y x ph) (.classEq (.cv y) (.cv z)))))
      (syn_weu x ph) (syn_weu y (syn_wsb y x ph)) p0016 p0019_e01_recanon
      p0019_e02_recanon
  exact p0019

@[expose]
noncomputable def g_cbveu (ph : Wff) (ps : Wff) (x : Var) (y : Var)
    (hyp_cbveu_1 : Nominal.NPrf (syn_wnf y ph))
    (hyp_cbveu_2 : Nominal.NPrf (syn_wnf x ps))
    (hyp_cbveu_3 : Nominal.NPrf (.imp (.objEq x y) (syn_wb ph ps))) :
    Nominal.NPrf (syn_wb (syn_weu x ph) (syn_weu y ps)) :=
  by
  have p0000 := @g_sb8eu ph x y hyp_cbveu_1
  have p0001 := @g_sbie ph ps x y hyp_cbveu_2 hyp_cbveu_3
  have p0002 := @g_eubii (syn_wsb y x ph) ps y p0001
  have p0003 :=
    @g_bitri (syn_weu x ph) (syn_weu y (syn_wsb y x ph)) (syn_weu y ps) p0000 p0002
  exact p0003

@[expose]
noncomputable def g_eu1 (ph : Wff) (x : Var) (y : Var) (dv_x_y : x ≠ y)
    (hyp_eu1_1 : Nominal.NPrf (syn_wnf y ph)) :
    Nominal.NPrf
      (syn_wb (syn_weu x ph) (syn_wex x
          (syn_wa ph (.all y (.imp (syn_wsb y x ph) (.classEq (.cv x) (.cv y))))))) :=
  by
  let proofSupport : Finset Var := ph.fv ∪ ({ x } : Finset Var) ∪ ({ y } : Finset Var)
  have p0000 :=
    @g_nfs1v ph x y
      (by
        first
        | (aesop))
  have p0001 :=
    @g_euf (syn_wsb y x ph) y x
      (by
        first
        | (aesop))
      p0000
  have p0002 := @g_sb8eu ph x y hyp_eu1_1
  have p0003 := @g_equcom x y
  have p0004_e00_recanon :
    Nominal.NPrf (syn_wb (.classEq (.cv x) (.cv y)) (.classEq (.cv y) (.cv x))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wb
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
    @g_imbi2i (.classEq (.cv x) (.cv y)) (.classEq (.cv y) (.cv x)) (syn_wsb y x ph)
      p0004_e00_recanon
  have p0005 :=
    @g_albii (.imp (syn_wsb y x ph) (.classEq (.cv x) (.cv y)))
      (.imp (syn_wsb y x ph) (.classEq (.cv y) (.cv x))) y p0004
  have p0006 := @g_sb6rf ph x y hyp_eu1_1
  have p0007_e01_recanon :
    Nominal.NPrf
      (syn_wb ph (.all y (.imp (.classEq (.cv y) (.cv x)) (syn_wsb y x ph)))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wb syn_wsb syn_wa syn_wex
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
    @g_anbi12i (.all y (.imp (syn_wsb y x ph) (.classEq (.cv x) (.cv y))))
      (.all y (.imp (syn_wsb y x ph) (.classEq (.cv y) (.cv x)))) ph
      (.all y (.imp (.classEq (.cv y) (.cv x)) (syn_wsb y x ph))) p0005 p0007_e01_recanon
  have p0008 := @g_ancom ph (.all y (.imp (syn_wsb y x ph) (.classEq (.cv x) (.cv y))))
  have p0009 := @g_albiim (syn_wsb y x ph) (.classEq (.cv y) (.cv x)) y
  have p0010 :=
    @g_n_3bitr4i (syn_wa (.all y (.imp (syn_wsb y x ph) (.classEq (.cv x) (.cv y)))) ph)
      (syn_wa (.all y (.imp (syn_wsb y x ph) (.classEq (.cv y) (.cv x))))
        (.all y (.imp (.classEq (.cv y) (.cv x)) (syn_wsb y x ph))))
      (syn_wa ph (.all y (.imp (syn_wsb y x ph) (.classEq (.cv x) (.cv y)))))
      (.all y (syn_wb (syn_wsb y x ph) (.classEq (.cv y) (.cv x)))) p0007 p0008 p0009
  have p0011 :=
    @g_exbii (syn_wa ph (.all y (.imp (syn_wsb y x ph) (.classEq (.cv x) (.cv y)))))
      (.all y (syn_wb (syn_wsb y x ph) (.classEq (.cv y) (.cv x)))) x p0010
  have p0012 :=
    @g_n_3bitr4i (syn_weu y (syn_wsb y x ph))
      (syn_wex x (.all y (syn_wb (syn_wsb y x ph) (.classEq (.cv y) (.cv x)))))
      (syn_weu x ph)
      (syn_wex x (syn_wa ph (.all y (.imp (syn_wsb y x ph) (.classEq (.cv x) (.cv y))))))
      p0001 p0002 p0011
  exact p0012

@[expose]
noncomputable def g_mo (ph : Wff) (x : Var) (y : Var) (dv_x_y : x ≠ y)
    (hyp_mo_1 : Nominal.NPrf (syn_wnf y ph)) :
    Nominal.NPrf
      (syn_wb (syn_wex y (.all x (.imp ph (.classEq (.cv x) (.cv y))))) (.all x
          (.all y (.imp (syn_wa ph (syn_wsb y x ph)) (.classEq (.cv x) (.cv y)))))) :=
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
    @g_nfv (.classEq (.cv x) (.cv z)) y
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
  have p0001 := @g_nfim ph (.classEq (.cv x) (.cv z)) y hyp_mo_1 p0000
  have p0002 := @g_nfal (.imp ph (.classEq (.cv x) (.cv z))) y x p0001
  have p0003 :=
    @g_nfv (.all x (.imp ph (.classEq (.cv x) (.cv y)))) z
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
  have p0004 := @g_equequ2 z y x
  have p0005_e00_recanon :
    Nominal.NPrf
      (.imp (.classEq (.cv z) (.cv y))
        (syn_wb (.classEq (.cv x) (.cv z)) (.classEq (.cv x) (.cv y)))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wb
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
    @g_imbi2d (.classEq (.cv z) (.cv y)) (.classEq (.cv x) (.cv z))
      (.classEq (.cv x) (.cv y)) ph p0005_e00_recanon
  have p0006 :=
    @g_albidv (.classEq (.cv z) (.cv y)) (.imp ph (.classEq (.cv x) (.cv z)))
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
      (.imp (.objEq z y) (syn_wb (.all x (.imp ph (.classEq (.cv x) (.cv z))))
          (.all x (.imp ph (.classEq (.cv x) (.cv y)))))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wb
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
        · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0006
  have p0007 :=
    @g_cbvex (.all x (.imp ph (.classEq (.cv x) (.cv z))))
      (.all x (.imp ph (.classEq (.cv x) (.cv y)))) z y p0002 p0003 p0007_e02_recanon
  have p0008 := @g_nfs1 ph x y hyp_mo_1
  have p0009 :=
    @g_nfv (.classEq (.cv y) (.cv z)) x
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
  have p0010 := @g_nfim (syn_wsb y x ph) (.classEq (.cv y) (.cv z)) x p0008 p0009
  have p0011 := @g_sbequ2 ph x y
  have p0012 := Nominal.ax8 x y z
  have p0013_e00_recanon :
    Nominal.NPrf (.imp (.classEq (.cv x) (.cv y)) (.imp (syn_wsb y x ph) ph)) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wsb syn_wa syn_wex
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
    @g_imim12d (.classEq (.cv x) (.cv y)) (syn_wsb y x ph) ph (.classEq (.cv x) (.cv z))
      (.classEq (.cv y) (.cv z)) p0013_e00_recanon p0013_e01_recanon
  have p0014_e02_recanon :
    Nominal.NPrf
      (.imp (.objEq x y) (.imp (.imp ph (.classEq (.cv x) (.cv z)))
          (.imp (syn_wsb y x ph) (.classEq (.cv y) (.cv z))))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wsb syn_wa syn_wex
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
        · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0013
  have p0014 :=
    @g_cbv3 (.imp ph (.classEq (.cv x) (.cv z)))
      (.imp (syn_wsb y x ph) (.classEq (.cv y) (.cv z))) x y p0001 p0010 p0014_e02_recanon
  have p0015 :=
    @g_ancli (.all x (.imp ph (.classEq (.cv x) (.cv z))))
      (.all y (.imp (syn_wsb y x ph) (.classEq (.cv y) (.cv z)))) p0014
  have p0016 :=
    @g_aaan (.imp ph (.classEq (.cv x) (.cv z)))
      (.imp (syn_wsb y x ph) (.classEq (.cv y) (.cv z))) x y p0001 p0010
  have p0017 :=
    @g_sylibr (.all x (.imp ph (.classEq (.cv x) (.cv z))))
      (syn_wa (.all x (.imp ph (.classEq (.cv x) (.cv z))))
        (.all y (.imp (syn_wsb y x ph) (.classEq (.cv y) (.cv z)))))
      (.all x (.all y (syn_wa (.imp ph (.classEq (.cv x) (.cv z)))
            (.imp (syn_wsb y x ph) (.classEq (.cv y) (.cv z))))))
      p0015 p0016
  have p0018 :=
    @g_prth ph (.classEq (.cv x) (.cv z)) (syn_wsb y x ph) (.classEq (.cv y) (.cv z))
  have p0019 := @g_equtr2 x y z
  have p0020_e01_recanon :
    Nominal.NPrf
      (.imp (syn_wa (.classEq (.cv x) (.cv z)) (.classEq (.cv y) (.cv z)))
        (.classEq (.cv x) (.cv y))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wa
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · apply Nominal.RecanonTransportDev.TRecanonWff.neg
          apply Nominal.RecanonTransportDev.TRecanonWff.imp
          · exact Nominal.RecanonTransportDev.TRecanonWff.objEq_classEq _ _
          · apply Nominal.RecanonTransportDev.TRecanonWff.neg
            exact Nominal.RecanonTransportDev.TRecanonWff.objEq_classEq _ _
        · exact Nominal.RecanonTransportDev.TRecanonWff.objEq_classEq _ _)
      p0019
  have p0020 :=
    @g_syl6
      (syn_wa (.imp ph (.classEq (.cv x) (.cv z)))
        (.imp (syn_wsb y x ph) (.classEq (.cv y) (.cv z))))
      (syn_wa ph (syn_wsb y x ph))
      (syn_wa (.classEq (.cv x) (.cv z)) (.classEq (.cv y) (.cv z)))
      (.classEq (.cv x) (.cv y)) p0018 p0020_e01_recanon
  have p0021 :=
    @g_n_2alimi
      (syn_wa (.imp ph (.classEq (.cv x) (.cv z)))
        (.imp (syn_wsb y x ph) (.classEq (.cv y) (.cv z))))
      (.imp (syn_wa ph (syn_wsb y x ph)) (.classEq (.cv x) (.cv y))) x y p0020
  have p0022 :=
    @g_syl (.all x (.imp ph (.classEq (.cv x) (.cv z))))
      (.all x (.all y (syn_wa (.imp ph (.classEq (.cv x) (.cv z)))
            (.imp (syn_wsb y x ph) (.classEq (.cv y) (.cv z))))))
      (.all x (.all y (.imp (syn_wa ph (syn_wsb y x ph)) (.classEq (.cv x) (.cv y)))))
      p0017 p0021
  have p0023 :=
    @g_exlimiv (.all x (.imp ph (.classEq (.cv x) (.cv z))))
      (.all x (.all y (.imp (syn_wa ph (syn_wsb y x ph)) (.classEq (.cv x) (.cv y))))) z
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
    @g_sylbir (syn_wex y (.all x (.imp ph (.classEq (.cv x) (.cv y)))))
      (syn_wex z (.all x (.imp ph (.classEq (.cv x) (.cv z)))))
      (.all x (.all y (.imp (syn_wa ph (syn_wsb y x ph)) (.classEq (.cv x) (.cv y)))))
      p0007 p0023
  have p0025 := @g_nfa2 (.imp (syn_wa ph (syn_wsb y x ph)) (.classEq (.cv x) (.cv y))) y x
  have p0026 := @g_sp (.imp (syn_wa ph (syn_wsb y x ph)) (.classEq (.cv x) (.cv y))) y
  have p0027 :=
    @g_exp3a (.all y (.imp (syn_wa ph (syn_wsb y x ph)) (.classEq (.cv x) (.cv y)))) ph
      (syn_wsb y x ph) (.classEq (.cv x) (.cv y)) p0026
  have p0028 :=
    @g_com3r (.all y (.imp (syn_wa ph (syn_wsb y x ph)) (.classEq (.cv x) (.cv y)))) ph
      (syn_wsb y x ph) (.classEq (.cv x) (.cv y)) p0027
  have p0029 :=
    @g_alimd (syn_wsb y x ph)
      (.all y (.imp (syn_wa ph (syn_wsb y x ph)) (.classEq (.cv x) (.cv y))))
      (.imp ph (.classEq (.cv x) (.cv y))) x p0008 p0028
  have p0030 :=
    @g_com12 (syn_wsb y x ph)
      (.all x (.all y (.imp (syn_wa ph (syn_wsb y x ph)) (.classEq (.cv x) (.cv y)))))
      (.all x (.imp ph (.classEq (.cv x) (.cv y)))) p0029
  have p0031 :=
    @g_eximd
      (.all x (.all y (.imp (syn_wa ph (syn_wsb y x ph)) (.classEq (.cv x) (.cv y)))))
      (syn_wsb y x ph) (.all x (.imp ph (.classEq (.cv x) (.cv y)))) y p0025 p0030
  have p0032 := @g_alnex (syn_wsb y x ph) y
  have p0033 := @g_nfn (syn_wsb y x ph) x p0008
  have p0034 := @g_nfn ph y hyp_mo_1
  have p0035 := @g_sbequ1 ph x y
  have p0036 := @g_equcoms (.imp ph (syn_wsb y x ph)) x y p0035
  have p0037_e00_recanon :
    Nominal.NPrf (.imp (.classEq (.cv y) (.cv x)) (.imp ph (syn_wsb y x ph))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wsb syn_wa syn_wex
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · exact Nominal.RecanonTransportDev.TRecanonWff.objEq_classEq _ _
        · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0036
  have p0037 := @g_con3d (.classEq (.cv y) (.cv x)) ph (syn_wsb y x ph) p0037_e00_recanon
  have p0038_e02_recanon :
    Nominal.NPrf (.imp (.objEq y x) (.imp (.neg (syn_wsb y x ph)) (.neg ph))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wsb syn_wa syn_wex
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
        · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0037
  have p0038 :=
    @g_cbv3 (.neg (syn_wsb y x ph)) (.neg ph) y x p0033 p0034 p0038_e02_recanon
  have p0039 := @g_pm2_21 ph (.classEq (.cv x) (.cv y))
  have p0040 := @g_alimi (.neg ph) (.imp ph (.classEq (.cv x) (.cv y))) x p0039
  have p0041 := @g_n_19_8a (.all x (.imp ph (.classEq (.cv x) (.cv y)))) y
  have p0042 :=
    @g_n_3syl (.all y (.neg (syn_wsb y x ph))) (.all x (.neg ph))
      (.all x (.imp ph (.classEq (.cv x) (.cv y))))
      (syn_wex y (.all x (.imp ph (.classEq (.cv x) (.cv y))))) p0038 p0040 p0041
  have p0043 :=
    @g_sylbir (.neg (syn_wex y (syn_wsb y x ph))) (.all y (.neg (syn_wsb y x ph)))
      (syn_wex y (.all x (.imp ph (.classEq (.cv x) (.cv y))))) p0032 p0042
  have p0044 :=
    @g_pm2_61d1
      (.all x (.all y (.imp (syn_wa ph (syn_wsb y x ph)) (.classEq (.cv x) (.cv y)))))
      (syn_wex y (syn_wsb y x ph))
      (syn_wex y (.all x (.imp ph (.classEq (.cv x) (.cv y))))) p0031 p0043
  have p0045 :=
    @g_impbii (syn_wex y (.all x (.imp ph (.classEq (.cv x) (.cv y)))))
      (.all x (.all y (.imp (syn_wa ph (syn_wsb y x ph)) (.classEq (.cv x) (.cv y)))))
      p0024 p0044
  exact p0045

@[expose]
noncomputable def g_euex (ph : Wff) (x : Var) :
    Nominal.NPrf (.imp (syn_weu x ph) (syn_wex x ph)) :=
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
    @g_nfv ph y
      (by
        first
        | (aesop))
  have p0001 :=
    @g_eu1 ph x y
      (by
        first
        | (aesop))
      p0000
  have p0002 :=
    @g_exsimpl ph (.all y (.imp (syn_wsb y x ph) (.classEq (.cv x) (.cv y)))) x
  have p0003 :=
    @g_sylbi (syn_weu x ph)
      (syn_wex x (syn_wa ph (.all y (.imp (syn_wsb y x ph) (.classEq (.cv x) (.cv y))))))
      (syn_wex x ph) p0001 p0002
  exact p0003

@[expose]
noncomputable def g_eumo0 (ph : Wff) (x : Var) (y : Var) (dv_x_y : x ≠ y)
    (hyp_eumo0_1 : Nominal.NPrf (syn_wnf y ph)) :
    Nominal.NPrf (.imp (syn_weu x ph) (syn_wex y (.all x (.imp ph (.objEq x y))))) :=
  by
  let proofSupport : Finset Var := ph.fv ∪ ({ x } : Finset Var) ∪ ({ y } : Finset Var)
  have p0000 :=
    @g_euf ph x y
      (by
        first
        | (aesop))
      hyp_eumo0_1
  have p0001 := @g_bi1 ph (.objEq x y)
  have p0002 := @g_alimi (syn_wb ph (.objEq x y)) (.imp ph (.objEq x y)) x p0001
  have p0003 :=
    @g_eximi (.all x (syn_wb ph (.objEq x y))) (.all x (.imp ph (.objEq x y))) y p0002
  have p0004_e00_recanon :
    Nominal.NPrf (syn_wb (syn_weu x ph) (syn_wex y (.all x (syn_wb ph (.objEq x y))))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wb syn_weu syn_wex
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
    @g_sylbi (syn_weu x ph) (syn_wex y (.all x (syn_wb ph (.objEq x y))))
      (syn_wex y (.all x (.imp ph (.objEq x y)))) p0004_e00_recanon p0003
  exact p0004

@[expose]
noncomputable def g_eu2 (ph : Wff) (x : Var) (y : Var) (dv_x_y : x ≠ y)
    (hyp_eu2_1 : Nominal.NPrf (syn_wnf y ph)) :
    Nominal.NPrf
      (syn_wb (syn_weu x ph) (syn_wa (syn_wex x ph)
          (.all x (.all y (.imp (syn_wa ph (syn_wsb y x ph)) (.objEq x y)))))) :=
  by
  let proofSupport : Finset Var := ph.fv ∪ ({ x } : Finset Var) ∪ ({ y } : Finset Var)
  have p0000 := @g_euex ph x
  have p0001 :=
    @g_eumo0 ph x y
      (by
        first
        | (aesop))
      hyp_eu2_1
  have p0002 :=
    @g_mo ph x y
      (by
        first
        | (aesop))
      hyp_eu2_1
  have p0003_e01_recanon :
    Nominal.NPrf
      (syn_wb (syn_wex y (.all x (.imp ph (.objEq x y))))
        (.all x (.all y (.imp (syn_wa ph (syn_wsb y x ph)) (.objEq x y))))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wb syn_wex syn_wa syn_wsb
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
    @g_sylib (syn_weu x ph) (syn_wex y (.all x (.imp ph (.objEq x y))))
      (.all x (.all y (.imp (syn_wa ph (syn_wsb y x ph)) (.objEq x y)))) p0001
      p0003_e01_recanon
  have p0004 :=
    @g_jca (syn_weu x ph) (syn_wex x ph)
      (.all x (.all y (.imp (syn_wa ph (syn_wsb y x ph)) (.objEq x y)))) p0000 p0003
  have p0005 := @g_n_19_29r ph (.all y (.imp (syn_wa ph (syn_wsb y x ph)) (.objEq x y))) x
  have p0006 := @g_impexp ph (syn_wsb y x ph) (.objEq x y)
  have p0007 :=
    @g_albii (.imp (syn_wa ph (syn_wsb y x ph)) (.objEq x y))
      (.imp ph (.imp (syn_wsb y x ph) (.objEq x y))) y p0006
  have p0008 := @g_n_19_21 ph (.imp (syn_wsb y x ph) (.objEq x y)) y hyp_eu2_1
  have p0009 :=
    @g_bitri (.all y (.imp (syn_wa ph (syn_wsb y x ph)) (.objEq x y)))
      (.all y (.imp ph (.imp (syn_wsb y x ph) (.objEq x y))))
      (.imp ph (.all y (.imp (syn_wsb y x ph) (.objEq x y)))) p0007 p0008
  have p0010 :=
    @g_anbi2i (.all y (.imp (syn_wa ph (syn_wsb y x ph)) (.objEq x y)))
      (.imp ph (.all y (.imp (syn_wsb y x ph) (.objEq x y)))) ph p0009
  have p0011 := @g_abai ph (.all y (.imp (syn_wsb y x ph) (.objEq x y)))
  have p0012 :=
    @g_bitr4i (syn_wa ph (.all y (.imp (syn_wa ph (syn_wsb y x ph)) (.objEq x y))))
      (syn_wa ph (.imp ph (.all y (.imp (syn_wsb y x ph) (.objEq x y)))))
      (syn_wa ph (.all y (.imp (syn_wsb y x ph) (.objEq x y)))) p0010 p0011
  have p0013 :=
    @g_exbii (syn_wa ph (.all y (.imp (syn_wa ph (syn_wsb y x ph)) (.objEq x y))))
      (syn_wa ph (.all y (.imp (syn_wsb y x ph) (.objEq x y)))) x p0012
  have p0014 :=
    @g_sylib
      (syn_wa (syn_wex x ph) (.all x (.all y (.imp (syn_wa ph (syn_wsb y x ph)) (.objEq x y)))))
      (syn_wex x (syn_wa ph (.all y (.imp (syn_wa ph (syn_wsb y x ph)) (.objEq x y)))))
      (syn_wex x (syn_wa ph (.all y (.imp (syn_wsb y x ph) (.objEq x y))))) p0005 p0013
  have p0015 :=
    @g_eu1 ph x y
      (by
        first
        | (aesop))
      hyp_eu2_1
  have p0016_e01_recanon :
    Nominal.NPrf
      (syn_wb (syn_weu x ph)
        (syn_wex x (syn_wa ph (.all y (.imp (syn_wsb y x ph) (.objEq x y)))))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wb syn_weu syn_wex
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
    @g_sylibr
      (syn_wa (syn_wex x ph) (.all x (.all y (.imp (syn_wa ph (syn_wsb y x ph)) (.objEq x y)))))
      (syn_wex x (syn_wa ph (.all y (.imp (syn_wsb y x ph) (.objEq x y))))) (syn_weu x ph)
      p0014 p0016_e01_recanon
  have p0017 :=
    @g_impbii (syn_weu x ph)
      (syn_wa (syn_wex x ph) (.all x (.all y (.imp (syn_wa ph (syn_wsb y x ph)) (.objEq x y)))))
      p0004 p0016
  exact p0017

@[expose]
noncomputable def g_eu3 (ph : Wff) (x : Var) (y : Var) (dv_x_y : x ≠ y)
    (hyp_eu3_1 : Nominal.NPrf (syn_wnf y ph)) :
    Nominal.NPrf
      (syn_wb (syn_weu x ph)
        (syn_wa (syn_wex x ph) (syn_wex y (.all x (.imp ph (.objEq x y)))))) :=
  by
  let proofSupport : Finset Var := ph.fv ∪ ({ x } : Finset Var) ∪ ({ y } : Finset Var)
  have p0000 :=
    @g_eu2 ph x y
      (by
        first
        | (aesop))
      hyp_eu3_1
  have p0001 :=
    @g_mo ph x y
      (by
        first
        | (aesop))
      hyp_eu3_1
  have p0002_e00_recanon :
    Nominal.NPrf
      (syn_wb (syn_wex y (.all x (.imp ph (.objEq x y))))
        (.all x (.all y (.imp (syn_wa ph (syn_wsb y x ph)) (.objEq x y))))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wb syn_wex syn_wa syn_wsb
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
    @g_anbi2i (syn_wex y (.all x (.imp ph (.objEq x y))))
      (.all x (.all y (.imp (syn_wa ph (syn_wsb y x ph)) (.objEq x y)))) (syn_wex x ph)
      p0002_e00_recanon
  have p0003 :=
    @g_bitr4i (syn_weu x ph)
      (syn_wa (syn_wex x ph) (.all x (.all y (.imp (syn_wa ph (syn_wsb y x ph)) (.objEq x y)))))
      (syn_wa (syn_wex x ph) (syn_wex y (.all x (.imp ph (.objEq x y))))) p0000 p0002
  exact p0003

@[expose]
noncomputable def g_mo2 (ph : Wff) (x : Var) (y : Var) (dv_x_y : x ≠ y)
    (hyp_mo2_1 : Nominal.NPrf (syn_wnf y ph)) :
    Nominal.NPrf (syn_wb (syn_wmo x ph) (syn_wex y (.all x (.imp ph (.objEq x y))))) :=
  by
  let proofSupport : Finset Var := ph.fv ∪ ({ x } : Finset Var) ∪ ({ y } : Finset Var)
  have p0000 := (Nominal.biimpRefl (syn_wmo x ph))
  have p0001 := @g_alnex ph x
  have p0002 := @g_pm2_21 ph (.objEq x y)
  have p0003 := @g_alimi (.neg ph) (.imp ph (.objEq x y)) x p0002
  have p0004 := @g_n_19_8a (.all x (.imp ph (.objEq x y))) y
  have p0005 :=
    @g_syl (.all x (.neg ph)) (.all x (.imp ph (.objEq x y)))
      (syn_wex y (.all x (.imp ph (.objEq x y)))) p0003 p0004
  have p0006 :=
    @g_sylbir (.neg (syn_wex x ph)) (.all x (.neg ph))
      (syn_wex y (.all x (.imp ph (.objEq x y)))) p0001 p0005
  have p0007 :=
    @g_eumo0 ph x y
      (by
        first
        | (aesop))
      hyp_mo2_1
  have p0008 :=
    @g_ja (syn_wex x ph) (syn_weu x ph) (syn_wex y (.all x (.imp ph (.objEq x y)))) p0006
      p0007
  have p0009 :=
    @g_eu3 ph x y
      (by
        first
        | (aesop))
      hyp_mo2_1
  have p0010 :=
    @g_simplbi2com (syn_weu x ph) (syn_wex x ph)
      (syn_wex y (.all x (.imp ph (.objEq x y)))) p0009
  have p0011 :=
    @g_impbii (.imp (syn_wex x ph) (syn_weu x ph))
      (syn_wex y (.all x (.imp ph (.objEq x y)))) p0008 p0010
  have p0012 :=
    @g_bitri (syn_wmo x ph) (.imp (syn_wex x ph) (syn_weu x ph))
      (syn_wex y (.all x (.imp ph (.objEq x y)))) p0000 p0011
  exact p0012

@[expose]
noncomputable def g_mo3 (ph : Wff) (x : Var) (y : Var) (dv_x_y : x ≠ y)
    (hyp_mo3_1 : Nominal.NPrf (syn_wnf y ph)) :
    Nominal.NPrf
      (syn_wb (syn_wmo x ph)
        (.all x (.all y (.imp (syn_wa ph (syn_wsb y x ph)) (.objEq x y))))) :=
  by
  let proofSupport : Finset Var := ph.fv ∪ ({ x } : Finset Var) ∪ ({ y } : Finset Var)
  have p0000 :=
    @g_mo2 ph x y
      (by
        first
        | (aesop))
      hyp_mo3_1
  have p0001 :=
    @g_mo ph x y
      (by
        first
        | (aesop))
      hyp_mo3_1
  have p0002_e01_recanon :
    Nominal.NPrf
      (syn_wb (syn_wex y (.all x (.imp ph (.objEq x y))))
        (.all x (.all y (.imp (syn_wa ph (syn_wsb y x ph)) (.objEq x y))))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wb syn_wex syn_wa syn_wsb
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
    @g_bitri (syn_wmo x ph) (syn_wex y (.all x (.imp ph (.objEq x y))))
      (.all x (.all y (.imp (syn_wa ph (syn_wsb y x ph)) (.objEq x y)))) p0000
      p0002_e01_recanon
  exact p0002

@[expose]
noncomputable def g_mo4f (ph : Wff) (ps : Wff) (x : Var) (y : Var) (dv_ph_y : y ∉ ph.fv)
    (dv_x_y : x ≠ y) (hyp_mo4f_1 : Nominal.NPrf (syn_wnf x ps))
    (hyp_mo4f_2 : Nominal.NPrf (.imp (.objEq x y) (syn_wb ph ps))) :
    Nominal.NPrf
      (syn_wb (syn_wmo x ph) (.all x (.all y (.imp (syn_wa ph ps) (.objEq x y))))) :=
  by
  let proofSupport : Finset Var :=
    ph.fv ∪ ps.fv ∪ ({ x } : Finset Var) ∪ ({ y } : Finset Var)
  have p0000 :=
    @g_nfv ph y
      (by
        first
        | (aesop))
  have p0001 :=
    @g_mo3 ph x y
      (by
        first
        | (aesop))
      p0000
  have p0002 := @g_sbie ph ps x y hyp_mo4f_1 hyp_mo4f_2
  have p0003 := @g_anbi2i (syn_wsb y x ph) ps ph p0002
  have p0004 := @g_imbi1i (syn_wa ph (syn_wsb y x ph)) (syn_wa ph ps) (.objEq x y) p0003
  have p0005 :=
    @g_n_2albii (.imp (syn_wa ph (syn_wsb y x ph)) (.objEq x y))
      (.imp (syn_wa ph ps) (.objEq x y)) x y p0004
  have p0006 :=
    @g_bitri (syn_wmo x ph)
      (.all x (.all y (.imp (syn_wa ph (syn_wsb y x ph)) (.objEq x y))))
      (.all x (.all y (.imp (syn_wa ph ps) (.objEq x y)))) p0001 p0005
  exact p0006

@[expose]
noncomputable def g_mo4 (ph : Wff) (ps : Wff) (x : Var) (y : Var) (dv_ph_y : y ∉ ph.fv)
    (dv_ps_x : x ∉ ps.fv) (dv_x_y : x ≠ y)
    (hyp_mo4_1 : Nominal.NPrf (.imp (.objEq x y) (syn_wb ph ps))) :
    Nominal.NPrf
      (syn_wb (syn_wmo x ph) (.all x (.all y (.imp (syn_wa ph ps) (.objEq x y))))) :=
  by
  let proofSupport : Finset Var :=
    ph.fv ∪ ps.fv ∪ ({ x } : Finset Var) ∪ ({ y } : Finset Var)
  have p0000 :=
    @g_nfv ps x
      (by
        first
        | (aesop))
  have p0001 :=
    @g_mo4f ph ps x y
      (by
        first
        | (aesop))
      (by
        first
        | (aesop))
      p0000 hyp_mo4_1
  exact p0001

@[expose]
noncomputable def g_mobid (ph : Wff) (ps : Wff) (ch : Wff) (x : Var)
    (hyp_mobid_1 : Nominal.NPrf (syn_wnf x ph))
    (hyp_mobid_2 : Nominal.NPrf (.imp ph (syn_wb ps ch))) :
    Nominal.NPrf (.imp ph (syn_wb (syn_wmo x ps) (syn_wmo x ch))) :=
  by
  have p0000 := @g_exbid ph ps ch x hyp_mobid_1 hyp_mobid_2
  have p0001 := @g_eubid ph ps ch x hyp_mobid_1 hyp_mobid_2
  have p0002 :=
    @g_imbi12d ph (syn_wex x ps) (syn_wex x ch) (syn_weu x ps) (syn_weu x ch) p0000 p0001
  have p0003 := (Nominal.biimpRefl (syn_wmo x ps))
  have p0004 := (Nominal.biimpRefl (syn_wmo x ch))
  have p0005 :=
    @g_n_3bitr4g ph (.imp (syn_wex x ps) (syn_weu x ps))
      (.imp (syn_wex x ch) (syn_weu x ch)) (syn_wmo x ps) (syn_wmo x ch) p0002 p0003 p0004
  exact p0005

@[expose]
noncomputable def g_mobidv (ph : Wff) (ps : Wff) (ch : Wff) (x : Var)
    (dv_ph_x : x ∉ ph.fv) (hyp_mobidv_1 : Nominal.NPrf (.imp ph (syn_wb ps ch))) :
    Nominal.NPrf (.imp ph (syn_wb (syn_wmo x ps) (syn_wmo x ch))) :=
  by
  let proofSupport : Finset Var := ph.fv ∪ ps.fv ∪ ch.fv ∪ ({ x } : Finset Var)
  have p0000 :=
    @g_nfv ph x
      (by
        first
        | (aesop))
  have p0001 := @g_mobid ph ps ch x p0000 hyp_mobidv_1
  exact p0001

@[expose]
noncomputable def g_mobii (ps : Wff) (ch : Wff) (x : Var)
    (hyp_mobii_1 : Nominal.NPrf (syn_wb ps ch)) :
    Nominal.NPrf (syn_wb (syn_wmo x ps) (syn_wmo x ch)) :=
  by
  let proofSupport : Finset Var := ps.fv ∪ ch.fv ∪ ({ x } : Finset Var)
  have p0000 := @g_a1i (syn_wb ps ch) syn_wtru hyp_mobii_1
  have p0001 :=
    @g_mobidv syn_wtru ps ch x
      (by
        first
        |
          (simp (config :=
              {
                failIfUnchanged :=
                  false }) only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wtru] at ⊢;
            aesop))
      p0000
  have p0002 := @g_trud (syn_wb (syn_wmo x ps) (syn_wmo x ch)) p0001
  exact p0002

@[expose]
noncomputable def g_cbvmo (ph : Wff) (ps : Wff) (x : Var) (y : Var)
    (hyp_cbvmo_1 : Nominal.NPrf (syn_wnf y ph))
    (hyp_cbvmo_2 : Nominal.NPrf (syn_wnf x ps))
    (hyp_cbvmo_3 : Nominal.NPrf (.imp (.objEq x y) (syn_wb ph ps))) :
    Nominal.NPrf (syn_wb (syn_wmo x ph) (syn_wmo y ps)) :=
  by
  have p0000 := @g_cbvex ph ps x y hyp_cbvmo_1 hyp_cbvmo_2 hyp_cbvmo_3
  have p0001 := @g_cbveu ph ps x y hyp_cbvmo_1 hyp_cbvmo_2 hyp_cbvmo_3
  have p0002 :=
    @g_imbi12i (syn_wex x ph) (syn_wex y ps) (syn_weu x ph) (syn_weu y ps) p0000 p0001
  have p0003 := (Nominal.biimpRefl (syn_wmo x ph))
  have p0004 := (Nominal.biimpRefl (syn_wmo y ps))
  have p0005 :=
    @g_n_3bitr4i (.imp (syn_wex x ph) (syn_weu x ph)) (.imp (syn_wex y ps) (syn_weu y ps))
      (syn_wmo x ph) (syn_wmo y ps) p0002 p0003 p0004
  exact p0005

@[expose]
noncomputable def g_eu5 (ph : Wff) (x : Var) :
    Nominal.NPrf (syn_wb (syn_weu x ph) (syn_wa (syn_wex x ph) (syn_wmo x ph))) :=
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
    @g_nfv ph y
      (by
        first
        | (aesop))
  have p0001 :=
    @g_eu3 ph x y
      (by
        first
        | (aesop))
      p0000
  have p0002 :=
    @g_mo2 ph x y
      (by
        first
        | (aesop))
      p0000
  have p0003_e00_recanon :
    Nominal.NPrf
      (syn_wb (syn_wmo x ph) (syn_wex y (.all x (.imp ph (.classEq (.cv x) (.cv y)))))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wb syn_wmo syn_wex syn_weu
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
    @g_anbi2i (syn_wmo x ph) (syn_wex y (.all x (.imp ph (.classEq (.cv x) (.cv y)))))
      (syn_wex x ph) p0003_e00_recanon
  have p0004_e00_recanon :
    Nominal.NPrf
      (syn_wb (syn_weu x ph) (syn_wa (syn_wex x ph)
          (syn_wex y (.all x (.imp ph (.classEq (.cv x) (.cv y))))))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wb syn_weu syn_wex syn_wa
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
    @g_bitr4i (syn_weu x ph)
      (syn_wa (syn_wex x ph) (syn_wex y (.all x (.imp ph (.classEq (.cv x) (.cv y))))))
      (syn_wa (syn_wex x ph) (syn_wmo x ph)) p0004_e00_recanon p0003
  exact p0004

@[expose]
noncomputable def g_eu4 (ph : Wff) (ps : Wff) (x : Var) (y : Var) (dv_ph_y : y ∉ ph.fv)
    (dv_ps_x : x ∉ ps.fv) (dv_x_y : x ≠ y)
    (hyp_eu4_1 : Nominal.NPrf (.imp (.objEq x y) (syn_wb ph ps))) :
    Nominal.NPrf
      (syn_wb (syn_weu x ph)
        (syn_wa (syn_wex x ph) (.all x (.all y (.imp (syn_wa ph ps) (.objEq x y)))))) :=
  by
  let proofSupport : Finset Var :=
    ph.fv ∪ ps.fv ∪ ({ x } : Finset Var) ∪ ({ y } : Finset Var)
  have p0000 := @g_eu5 ph x
  have p0001 :=
    @g_mo4 ph ps x y
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
    @g_anbi2i (syn_wmo x ph) (.all x (.all y (.imp (syn_wa ph ps) (.objEq x y))))
      (syn_wex x ph) p0001
  have p0003 :=
    @g_bitri (syn_weu x ph) (syn_wa (syn_wex x ph) (syn_wmo x ph))
      (syn_wa (syn_wex x ph) (.all x (.all y (.imp (syn_wa ph ps) (.objEq x y))))) p0000
      p0002
  exact p0003

@[expose]
noncomputable def g_eumo (ph : Wff) (x : Var) :
    Nominal.NPrf (.imp (syn_weu x ph) (syn_wmo x ph)) :=
  by
  have p0000 := @g_eu5 ph x
  have p0001 := @g_simprbi (syn_weu x ph) (syn_wex x ph) (syn_wmo x ph) p0000
  exact p0001

@[expose]
noncomputable def g_exmoeu2 (ph : Wff) (x : Var) :
    Nominal.NPrf (.imp (syn_wex x ph) (syn_wb (syn_wmo x ph) (syn_weu x ph))) :=
  by
  have p0000 := @g_eu5 ph x
  have p0001 := @g_baibr (syn_weu x ph) (syn_wex x ph) (syn_wmo x ph) p0000
  exact p0001

@[expose]
noncomputable def g_exmo (ph : Wff) (x : Var) :
    Nominal.NPrf (syn_wo (syn_wex x ph) (syn_wmo x ph)) :=
  by
  have p0000 := @g_pm2_21 (syn_wex x ph) (syn_weu x ph)
  have p0001 := (Nominal.biimpRefl (syn_wmo x ph))
  have p0002 :=
    @g_sylibr (.neg (syn_wex x ph)) (.imp (syn_wex x ph) (syn_weu x ph)) (syn_wmo x ph)
      p0000 p0001
  have p0003 := @g_orri (syn_wex x ph) (syn_wmo x ph) p0002
  exact p0003

@[expose]
noncomputable def g_moim (ph : Wff) (ps : Wff) (x : Var) :
    Nominal.NPrf (.imp (.all x (.imp ph ps)) (.imp (syn_wmo x ps) (syn_wmo x ph))) :=
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
  have p0000 := @g_imim1 ph ps (.classEq (.cv x) (.cv y))
  have p0001 :=
    @g_al2imi (.imp ph ps) (.imp ps (.classEq (.cv x) (.cv y)))
      (.imp ph (.classEq (.cv x) (.cv y))) x p0000
  have p0002 :=
    @g_eximdv (.all x (.imp ph ps)) (.all x (.imp ps (.classEq (.cv x) (.cv y))))
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
    @g_nfv ps y
      (by
        first
        | (aesop))
  have p0004 :=
    @g_mo2 ps x y
      (by
        first
        | (aesop))
      p0003
  have p0005 :=
    @g_nfv ph y
      (by
        first
        | (aesop))
  have p0006 :=
    @g_mo2 ph x y
      (by
        first
        | (aesop))
      p0005
  have p0007_e01_recanon :
    Nominal.NPrf
      (syn_wb (syn_wmo x ps) (syn_wex y (.all x (.imp ps (.classEq (.cv x) (.cv y)))))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wb syn_wmo syn_wex syn_weu
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
      (syn_wb (syn_wmo x ph) (syn_wex y (.all x (.imp ph (.classEq (.cv x) (.cv y)))))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wb syn_wmo syn_wex syn_weu
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
    @g_n_3imtr4g (.all x (.imp ph ps))
      (syn_wex y (.all x (.imp ps (.classEq (.cv x) (.cv y)))))
      (syn_wex y (.all x (.imp ph (.classEq (.cv x) (.cv y))))) (syn_wmo x ps)
      (syn_wmo x ph) p0002 p0007_e01_recanon p0007_e02_recanon
  exact p0007

@[expose]
noncomputable def g_moanim (ph : Wff) (ps : Wff) (x : Var)
    (hyp_moanim_1 : Nominal.NPrf (syn_wnf x ph)) :
    Nominal.NPrf (syn_wb (syn_wmo x (syn_wa ph ps)) (.imp ph (syn_wmo x ps))) :=
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
  have p0000 := @g_impexp ph ps (.objEq x y)
  have p0001 :=
    @g_albii (.imp (syn_wa ph ps) (.objEq x y)) (.imp ph (.imp ps (.objEq x y))) x p0000
  have p0002 := @g_n_19_21 ph (.imp ps (.objEq x y)) x hyp_moanim_1
  have p0003 :=
    @g_bitri (.all x (.imp (syn_wa ph ps) (.objEq x y)))
      (.all x (.imp ph (.imp ps (.objEq x y)))) (.imp ph (.all x (.imp ps (.objEq x y))))
      p0001 p0002
  have p0004 :=
    @g_exbii (.all x (.imp (syn_wa ph ps) (.objEq x y)))
      (.imp ph (.all x (.imp ps (.objEq x y)))) y p0003
  have p0005 :=
    @g_nfv (syn_wa ph ps) y
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
    @g_mo2 (syn_wa ph ps) x y
      (by
        first
        | (aesop))
      p0005
  have p0007 :=
    @g_nfv ps y
      (by
        first
        | (aesop))
  have p0008 :=
    @g_mo2 ps x y
      (by
        first
        | (aesop))
      p0007
  have p0009 :=
    @g_imbi2i (syn_wmo x ps) (syn_wex y (.all x (.imp ps (.objEq x y)))) ph p0008
  have p0010 :=
    @g_n_19_37v ph (.all x (.imp ps (.objEq x y))) y
      (by
        first
        | (aesop))
  have p0011 :=
    @g_bitr4i (.imp ph (syn_wmo x ps))
      (.imp ph (syn_wex y (.all x (.imp ps (.objEq x y)))))
      (syn_wex y (.imp ph (.all x (.imp ps (.objEq x y))))) p0009 p0010
  have p0012 :=
    @g_n_3bitr4i (syn_wex y (.all x (.imp (syn_wa ph ps) (.objEq x y))))
      (syn_wex y (.imp ph (.all x (.imp ps (.objEq x y))))) (syn_wmo x (syn_wa ph ps))
      (.imp ph (syn_wmo x ps)) p0004 p0006 p0011
  exact p0012

@[expose]
noncomputable def g_euan (ph : Wff) (ps : Wff) (x : Var)
    (hyp_moanim_1 : Nominal.NPrf (syn_wnf x ph)) :
    Nominal.NPrf (syn_wb (syn_weu x (syn_wa ph ps)) (syn_wa ph (syn_weu x ps))) :=
  by
  have p0000 := @g_simpl ph ps
  have p0001 := @g_exlimi (syn_wa ph ps) ph x hyp_moanim_1 p0000
  have p0002 := @g_adantr (syn_wex x (syn_wa ph ps)) ph (syn_wmo x (syn_wa ph ps)) p0001
  have p0003 := @g_simpr ph ps
  have p0004 := @g_eximi (syn_wa ph ps) ps x p0003
  have p0005 :=
    @g_adantr (syn_wex x (syn_wa ph ps)) (syn_wex x ps) (syn_wmo x (syn_wa ph ps)) p0004
  have p0006 := @g_nfe1 (syn_wa ph ps) x
  have p0007 := @g_a1d (syn_wex x (syn_wa ph ps)) ph ps p0001
  have p0008 := @g_ancrd (syn_wex x (syn_wa ph ps)) ps ph p0007
  have p0009 := @g_impbid2 (syn_wex x (syn_wa ph ps)) (syn_wa ph ps) ps p0003 p0008
  have p0010 := @g_mobid (syn_wex x (syn_wa ph ps)) (syn_wa ph ps) ps x p0006 p0009
  have p0011 :=
    @g_biimpa (syn_wex x (syn_wa ph ps)) (syn_wmo x (syn_wa ph ps)) (syn_wmo x ps) p0010
  have p0012 :=
    @g_jca32 (syn_wa (syn_wex x (syn_wa ph ps)) (syn_wmo x (syn_wa ph ps))) ph
      (syn_wex x ps) (syn_wmo x ps) p0002 p0005 p0011
  have p0013 := @g_eu5 (syn_wa ph ps) x
  have p0014 := @g_eu5 ps x
  have p0015 := @g_anbi2i (syn_weu x ps) (syn_wa (syn_wex x ps) (syn_wmo x ps)) ph p0014
  have p0016 :=
    @g_n_3imtr4i (syn_wa (syn_wex x (syn_wa ph ps)) (syn_wmo x (syn_wa ph ps)))
      (syn_wa ph (syn_wa (syn_wex x ps) (syn_wmo x ps))) (syn_weu x (syn_wa ph ps))
      (syn_wa ph (syn_weu x ps)) p0012 p0013 p0015
  have p0017 := @g_ibar ph ps
  have p0018 := @g_eubid ph ps (syn_wa ph ps) x hyp_moanim_1 p0017
  have p0019 := @g_biimpa ph (syn_weu x ps) (syn_weu x (syn_wa ph ps)) p0018
  have p0020 :=
    @g_impbii (syn_weu x (syn_wa ph ps)) (syn_wa ph (syn_weu x ps)) p0016 p0019
  exact p0020

@[expose]
noncomputable def g_moanimv (ph : Wff) (ps : Wff) (x : Var) (dv_ph_x : x ∉ ph.fv) :
    Nominal.NPrf (syn_wb (syn_wmo x (syn_wa ph ps)) (.imp ph (syn_wmo x ps))) :=
  by
  let proofSupport : Finset Var := ph.fv ∪ ps.fv ∪ ({ x } : Finset Var)
  have p0000 :=
    @g_nfv ph x
      (by
        first
        | (aesop))
  have p0001 := @g_moanim ph ps x p0000
  exact p0001

@[expose]
noncomputable def g_euanv (ph : Wff) (ps : Wff) (x : Var) (dv_ph_x : x ∉ ph.fv) :
    Nominal.NPrf (syn_wb (syn_weu x (syn_wa ph ps)) (syn_wa ph (syn_weu x ps))) :=
  by
  let proofSupport : Finset Var := ph.fv ∪ ps.fv ∪ ({ x } : Finset Var)
  have p0000 :=
    @g_nfv ph x
      (by
        first
        | (aesop))
  have p0001 := @g_euan ph ps x p0000
  exact p0001

@[expose]
noncomputable def g_mopick (ph : Wff) (ps : Wff) (x : Var) :
    Nominal.NPrf (.imp (syn_wa (syn_wmo x ph) (syn_wex x (syn_wa ph ps))) (.imp ph ps)) :=
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
    @g_nfv (syn_wa ph ps) y
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
    @g_nfs1v ph x y
      (by
        first
        | (aesop))
  have p0002 :=
    @g_nfs1v ps x y
      (by
        first
        | (aesop))
  have p0003 := @g_nfan (syn_wsb y x ph) (syn_wsb y x ps) x p0001 p0002
  have p0004 := @g_sbequ12 ph x y
  have p0005 := @g_sbequ12 ps x y
  have p0006_e00_recanon :
    Nominal.NPrf (.imp (.classEq (.cv x) (.cv y)) (syn_wb ph (syn_wsb y x ph))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wb syn_wsb syn_wa syn_wex
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · exact Nominal.RecanonTransportDev.TRecanonWff.objEq_classEq _ _
        · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0004
  have p0006_e01_recanon :
    Nominal.NPrf (.imp (.classEq (.cv x) (.cv y)) (syn_wb ps (syn_wsb y x ps))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wb syn_wsb syn_wa syn_wex
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · exact Nominal.RecanonTransportDev.TRecanonWff.objEq_classEq _ _
        · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0005
  have p0006 :=
    @g_anbi12d (.classEq (.cv x) (.cv y)) ph (syn_wsb y x ph) ps (syn_wsb y x ps)
      p0006_e00_recanon p0006_e01_recanon
  have p0007_e02_recanon :
    Nominal.NPrf
      (.imp (.objEq x y) (syn_wb (syn_wa ph ps) (syn_wa (syn_wsb y x ph) (syn_wsb y x ps)))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wb syn_wa
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
        · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0006
  have p0007 :=
    @g_cbvex (syn_wa ph ps) (syn_wa (syn_wsb y x ph) (syn_wsb y x ps)) x y p0000 p0003
      p0007_e02_recanon
  have p0008 :=
    @g_nfv ph y
      (by
        first
        | (aesop))
  have p0009 :=
    @g_mo3 ph x y
      (by
        first
        | (aesop))
      p0008
  have p0010 := @g_sp (.imp (syn_wa ph (syn_wsb y x ph)) (.classEq (.cv x) (.cv y))) y
  have p0011 :=
    @g_sps (.all y (.imp (syn_wa ph (syn_wsb y x ph)) (.classEq (.cv x) (.cv y))))
      (.imp (syn_wa ph (syn_wsb y x ph)) (.classEq (.cv x) (.cv y))) x p0010
  have p0012_e00_recanon :
    Nominal.NPrf
      (syn_wb (syn_wmo x ph) (.all x
          (.all y (.imp (syn_wa ph (syn_wsb y x ph)) (.classEq (.cv x) (.cv y)))))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wb syn_wmo syn_wex syn_weu syn_wa syn_wsb
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
    @g_sylbi (syn_wmo x ph)
      (.all x (.all y (.imp (syn_wa ph (syn_wsb y x ph)) (.classEq (.cv x) (.cv y)))))
      (.imp (syn_wa ph (syn_wsb y x ph)) (.classEq (.cv x) (.cv y))) p0012_e00_recanon
      p0011
  have p0013 := @g_sbequ2 ps x y
  have p0014_e00_recanon :
    Nominal.NPrf (.imp (.classEq (.cv x) (.cv y)) (.imp (syn_wsb y x ps) ps)) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wsb syn_wa syn_wex
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · exact Nominal.RecanonTransportDev.TRecanonWff.objEq_classEq _ _
        · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0013
  have p0014 :=
    @g_imim2i (.classEq (.cv x) (.cv y)) (.imp (syn_wsb y x ps) ps)
      (syn_wa ph (syn_wsb y x ph)) p0014_e00_recanon
  have p0015 :=
    @g_exp3a (.imp (syn_wa ph (syn_wsb y x ph)) (.classEq (.cv x) (.cv y))) ph
      (syn_wsb y x ph) (.imp (syn_wsb y x ps) ps) p0014
  have p0016 :=
    @g_com4t (.imp (syn_wa ph (syn_wsb y x ph)) (.classEq (.cv x) (.cv y))) ph
      (syn_wsb y x ph) (syn_wsb y x ps) ps p0015
  have p0017 :=
    @g_imp (syn_wsb y x ph) (syn_wsb y x ps)
      (.imp (.imp (syn_wa ph (syn_wsb y x ph)) (.classEq (.cv x) (.cv y))) (.imp ph ps))
      p0016
  have p0018 :=
    @g_syl5 (syn_wmo x ph) (.imp (syn_wa ph (syn_wsb y x ph)) (.classEq (.cv x) (.cv y)))
      (syn_wa (syn_wsb y x ph) (syn_wsb y x ps)) (.imp ph ps) p0012 p0017
  have p0019 :=
    @g_exlimiv (syn_wa (syn_wsb y x ph) (syn_wsb y x ps))
      (.imp (syn_wmo x ph) (.imp ph ps)) y
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
    @g_sylbi (syn_wex x (syn_wa ph ps))
      (syn_wex y (syn_wa (syn_wsb y x ph) (syn_wsb y x ps)))
      (.imp (syn_wmo x ph) (.imp ph ps)) p0007 p0019
  have p0021 := @g_impcom (syn_wex x (syn_wa ph ps)) (syn_wmo x ph) (.imp ph ps) p0020
  exact p0021

@[expose]
noncomputable def g_eupick (ph : Wff) (ps : Wff) (x : Var) :
    Nominal.NPrf (.imp (syn_wa (syn_weu x ph) (syn_wex x (syn_wa ph ps))) (.imp ph ps)) :=
  by
  have p0000 := @g_eumo ph x
  have p0001 := @g_mopick ph ps x
  have p0002 :=
    @g_sylan (syn_weu x ph) (syn_wmo x ph) (syn_wex x (syn_wa ph ps)) (.imp ph ps) p0000
      p0001
  exact p0002

@[expose]
noncomputable def g_moexex (ph : Wff) (ps : Wff) (x : Var) (y : Var)
    (hyp_moexex_1 : Nominal.NPrf (syn_wnf y ph)) :
    Nominal.NPrf
      (.imp (syn_wa (syn_wmo x ph) (.all x (syn_wmo y ps)))
        (syn_wmo y (syn_wex x (syn_wa ph ps)))) :=
  by
  have p0000 := @g_nfmo1 ph x
  have p0001 := @g_nfa1 (syn_wmo y ps) x
  have p0002 := @g_nfe1 (syn_wa ph ps) x
  have p0003 := @g_nfmo (syn_wex x (syn_wa ph ps)) x y p0002
  have p0004 :=
    @g_nfim (.all x (syn_wmo y ps)) (syn_wmo y (syn_wex x (syn_wa ph ps))) x p0001 p0003
  have p0005 :=
    @g_nfim (syn_wmo x ph)
      (.imp (.all x (syn_wmo y ps)) (syn_wmo y (syn_wex x (syn_wa ph ps)))) x p0000 p0004
  have p0006 := @g_nfmo ph y x hyp_moexex_1
  have p0007 := @g_mopick ph ps x
  have p0008 := @g_ex (syn_wmo x ph) (syn_wex x (syn_wa ph ps)) (.imp ph ps) p0007
  have p0009 := @g_com3r (syn_wmo x ph) (syn_wex x (syn_wa ph ps)) ph ps p0008
  have p0010 :=
    @g_alrimd ph (syn_wmo x ph) (.imp (syn_wex x (syn_wa ph ps)) ps) y hyp_moexex_1 p0006
      p0009
  have p0011 := @g_moim (syn_wex x (syn_wa ph ps)) ps y
  have p0012 :=
    @g_spsd (.all y (.imp (syn_wex x (syn_wa ph ps)) ps)) (syn_wmo y ps)
      (syn_wmo y (syn_wex x (syn_wa ph ps))) x p0011
  have p0013 :=
    @g_syl6 ph (syn_wmo x ph) (.all y (.imp (syn_wex x (syn_wa ph ps)) ps))
      (.imp (.all x (syn_wmo y ps)) (syn_wmo y (syn_wex x (syn_wa ph ps)))) p0010 p0012
  have p0014 :=
    @g_exlimi ph
      (.imp (syn_wmo x ph)
        (.imp (.all x (syn_wmo y ps)) (syn_wmo y (syn_wex x (syn_wa ph ps)))))
      x p0005 p0013
  have p0015 := @g_nfex ph y x hyp_moexex_1
  have p0016 := @g_exsimpl ph ps x
  have p0017 := @g_exlimi (syn_wex x (syn_wa ph ps)) (syn_wex x ph) y p0015 p0016
  have p0018 := @g_con3i (syn_wex y (syn_wex x (syn_wa ph ps))) (syn_wex x ph) p0017
  have p0019 := @g_exmo (syn_wex x (syn_wa ph ps)) y
  have p0020 :=
    @g_ori (syn_wex y (syn_wex x (syn_wa ph ps))) (syn_wmo y (syn_wex x (syn_wa ph ps)))
      p0019
  have p0021 :=
    @g_syl (.neg (syn_wex x ph)) (.neg (syn_wex y (syn_wex x (syn_wa ph ps))))
      (syn_wmo y (syn_wex x (syn_wa ph ps))) p0018 p0020
  have p0022 :=
    @g_a1d (.neg (syn_wex x ph)) (syn_wmo y (syn_wex x (syn_wa ph ps)))
      (.all x (syn_wmo y ps)) p0021
  have p0023 :=
    @g_a1d (.neg (syn_wex x ph))
      (.imp (.all x (syn_wmo y ps)) (syn_wmo y (syn_wex x (syn_wa ph ps)))) (syn_wmo x ph)
      p0022
  have p0024 :=
    @g_pm2_61i (syn_wex x ph)
      (.imp (syn_wmo x ph)
        (.imp (.all x (syn_wmo y ps)) (syn_wmo y (syn_wex x (syn_wa ph ps)))))
      p0014 p0023
  have p0025 :=
    @g_imp (syn_wmo x ph) (.all x (syn_wmo y ps)) (syn_wmo y (syn_wex x (syn_wa ph ps)))
      p0024
  exact p0025

@[expose]
noncomputable def g_moexexv (ph : Wff) (ps : Wff) (x : Var) (y : Var)
    (dv_ph_y : y ∉ ph.fv) :
    Nominal.NPrf
      (.imp (syn_wa (syn_wmo x ph) (.all x (syn_wmo y ps)))
        (syn_wmo y (syn_wex x (syn_wa ph ps)))) :=
  by
  let proofSupport : Finset Var :=
    ph.fv ∪ ps.fv ∪ ({ x } : Finset Var) ∪ ({ y } : Finset Var)
  have p0000 :=
    @g_nfv ph y
      (by
        first
        | (aesop))
  have p0001 := @g_moexex ph ps x y p0000
  exact p0001

@[expose]
noncomputable def g_euequ1 (x : Var) (y : Var) (dv_x_y : x ≠ y) :
    Nominal.NPrf (syn_weu x (.objEq x y)) :=
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
    @g_a9ev x y
      (by
        first
        | (aesop))
  have p0001 := @g_equtr2 x z y
  have p0002 := @g_gen2 (.imp (syn_wa (.objEq x y) (.objEq z y)) (.objEq x z)) x z p0001
  have p0003 := @g_equequ1 x z y
  have p0004 :=
    @g_eu4 (.objEq x y) (.objEq z y) x z
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
    @g_mpbir2an (syn_weu x (.objEq x y)) (syn_wex x (.objEq x y))
      (.all x (.all z (.imp (syn_wa (.objEq x y) (.objEq z y)) (.objEq x z)))) p0000 p0002
      p0004
  exact p0005

@[expose]
noncomputable def g_abid (ph : Wff) (x : Var) :
    Nominal.NPrf (syn_wb (.classMem (.cv x) (.cab x ph)) ph) :=
  by
  have p0000 :=
    (NFChoice.DirectNominalPrf.Nominal.DefinitionLeafHandlersCanonical001.dfClabStructural
      x x ph)
  have p0001 := @g_sbid ph x
  have p0002 := @g_bitri (.classMem (.cv x) (.cab x ph)) (syn_wsb x x ph) ph p0000 p0001
  exact p0002

@[expose]
noncomputable def g_hbab1 (ph : Wff) (x : Var) (y : Var) (dv_x_y : x ≠ y) :
    Nominal.NPrf
      (.imp (.classMem (.cv y) (.cab x ph)) (.all x (.classMem (.cv y) (.cab x ph)))) :=
  by
  let proofSupport : Finset Var := ph.fv ∪ ({ x } : Finset Var) ∪ ({ y } : Finset Var)
  have p0000 :=
    (NFChoice.DirectNominalPrf.Nominal.DefinitionLeafHandlersCanonical001.dfClabStructural
      y x ph)
  have p0001 :=
    @g_hbs1 ph x y
      (by
        first
        | (aesop))
  have p0002 := @g_hbxfrbi (.classMem (.cv y) (.cab x ph)) (syn_wsb y x ph) x p0000 p0001
  exact p0002

@[expose]
noncomputable def g_nfsab1 (ph : Wff) (x : Var) (y : Var) (dv_x_y : x ≠ y) :
    Nominal.NPrf (syn_wnf x (.classMem (.cv y) (.cab x ph))) :=
  by
  let proofSupport : Finset Var := ph.fv ∪ ({ x } : Finset Var) ∪ ({ y } : Finset Var)
  have p0000 :=
    @g_hbab1 ph x y
      (by
        first
        | (aesop))
  have p0001 := @g_nfi (.classMem (.cv y) (.cab x ph)) x p0000
  exact p0001

@[expose]
noncomputable def g_hbab (ph : Wff) (x : Var) (y : Var) (z : Var) (dv_x_z : x ≠ z)
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
    @g_hbsb ph y z x
      (by
        first
        | (aesop))
      hyp_hbab_1
  have p0002 := @g_hbxfrbi (.classMem (.cv z) (.cab y ph)) (syn_wsb z y ph) x p0000 p0001
  exact p0002

@[expose]
noncomputable def g_nfsab (ph : Wff) (x : Var) (y : Var) (z : Var) (dv_x_z : x ≠ z)
    (hyp_nfsab_1 : Nominal.NPrf (syn_wnf x ph)) :
    Nominal.NPrf (syn_wnf x (.classMem (.cv z) (.cab y ph))) :=
  by
  let proofSupport : Finset Var :=
    ph.fv ∪ ({ x } : Finset Var) ∪ ({ y } : Finset Var) ∪ ({ z } : Finset Var)
  have p0000 := @g_nfri ph x hyp_nfsab_1
  have p0001 :=
    @g_hbab ph x y z
      (by
        first
        | (aesop))
      p0000
  have p0002 := @g_nfi (.classMem (.cv z) (.cab y ph)) x p0001
  exact p0002

@[expose]
noncomputable def g_dfcleq (x : Var) (A : Class) (B : Class) (dv_A_x : x ∉ A.fv)
    (dv_B_x : x ∉ B.fv) :
    Nominal.NPrf
      (syn_wb (.classEq A B) (.all x (syn_wb (.classMem (.cv x) A) (.classMem (.cv x) B)))) :=
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

@[expose]
noncomputable def g_eqriv (x : Var) (A : Class) (B : Class) (dv_A_x : x ∉ A.fv)
    (dv_B_x : x ∉ B.fv)
    (hyp_eqriv_1 : Nominal.NPrf (syn_wb (.classMem (.cv x) A) (.classMem (.cv x) B))) :
    Nominal.NPrf (.classEq A B) :=
  by
  let proofSupport : Finset Var := ({ x } : Finset Var) ∪ A.fv ∪ B.fv
  have p0000 :=
    @g_dfcleq x A B
      (by
        first
        | (aesop))
      (by
        first
        | (aesop))
  have p0001 :=
    @g_mpgbir (.classEq A B) (syn_wb (.classMem (.cv x) A) (.classMem (.cv x) B)) x p0000
      hyp_eqriv_1
  exact p0001

@[expose]
noncomputable def g_eqrdv (ph : Wff) (x : Var) (A : Class) (B : Class) (dv_A_x : x ∉ A.fv)
    (dv_B_x : x ∉ B.fv) (dv_ph_x : x ∉ ph.fv)
    (hyp_eqrdv_1 :
      Nominal.NPrf (.imp ph (syn_wb (.classMem (.cv x) A) (.classMem (.cv x) B)))) :
    Nominal.NPrf (.imp ph (.classEq A B)) :=
  by
  let proofSupport : Finset Var := ph.fv ∪ ({ x } : Finset Var) ∪ A.fv ∪ B.fv
  have p0000 :=
    @g_alrimiv ph (syn_wb (.classMem (.cv x) A) (.classMem (.cv x) B)) x
      (by
        first
        | (aesop))
      hyp_eqrdv_1
  have p0001 :=
    @g_dfcleq x A B
      (by
        first
        | (aesop))
      (by
        first
        | (aesop))
  have p0002 :=
    @g_sylibr ph (.all x (syn_wb (.classMem (.cv x) A) (.classMem (.cv x) B)))
      (.classEq A B) p0000 p0001
  exact p0002

@[expose]
noncomputable def g_eqid (A : Class) : Nominal.NPrf (.classEq A A) :=
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
  have p0000 := @g_biid (.classMem (.cv x) A)
  have p0001 :=
    @g_eqriv x A A
      (by
        first
        | (aesop))
      (by
        first
        | (aesop))
      p0000
  exact p0001

@[expose]
noncomputable def g_eqidd (ph : Wff) (A : Class) :
    Nominal.NPrf (.imp ph (.classEq A A)) :=
  by
  have p0000 := @g_eqid A
  have p0001 := @g_a1i (.classEq A A) ph p0000
  exact p0001

@[expose]
noncomputable def g_eqcom (A : Class) (B : Class) :
    Nominal.NPrf (syn_wb (.classEq A B) (.classEq B A)) :=
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
  have p0000 := @g_bicom (.classMem (.cv x) A) (.classMem (.cv x) B)
  have p0001 :=
    @g_albii (syn_wb (.classMem (.cv x) A) (.classMem (.cv x) B))
      (syn_wb (.classMem (.cv x) B) (.classMem (.cv x) A)) x p0000
  have p0002 :=
    @g_dfcleq x A B
      (by
        first
        | (aesop))
      (by
        first
        | (aesop))
  have p0003 :=
    @g_dfcleq x B A
      (by
        first
        | (aesop))
      (by
        first
        | (aesop))
  have p0004 :=
    @g_n_3bitr4i (.all x (syn_wb (.classMem (.cv x) A) (.classMem (.cv x) B)))
      (.all x (syn_wb (.classMem (.cv x) B) (.classMem (.cv x) A))) (.classEq A B)
      (.classEq B A) p0001 p0002 p0003
  exact p0004

@[expose]
noncomputable def g_eqcoms (ph : Wff) (A : Class) (B : Class)
    (hyp_eqcoms_1 : Nominal.NPrf (.imp (.classEq A B) ph)) :
    Nominal.NPrf (.imp (.classEq B A) ph) :=
  by
  have p0000 := @g_eqcom B A
  have p0001 := @g_sylbi (.classEq B A) (.classEq A B) ph p0000 hyp_eqcoms_1
  exact p0001

@[expose]
noncomputable def g_eqcomi (A : Class) (B : Class)
    (hyp_eqcomi_1 : Nominal.NPrf (.classEq A B)) : Nominal.NPrf (.classEq B A) :=
  by
  have p0000 := @g_eqcom A B
  have p0001 := @g_mpbi (.classEq A B) (.classEq B A) hyp_eqcomi_1 p0000
  exact p0001

@[expose]
noncomputable def g_eqcomd (ph : Wff) (A : Class) (B : Class)
    (hyp_eqcomd_1 : Nominal.NPrf (.imp ph (.classEq A B))) :
    Nominal.NPrf (.imp ph (.classEq B A)) :=
  by
  have p0000 := @g_eqcom A B
  have p0001 := @g_sylib ph (.classEq A B) (.classEq B A) hyp_eqcomd_1 p0000
  exact p0001

@[expose]
noncomputable def g_eqeq1 (A : Class) (B : Class) (C : Class) :
    Nominal.NPrf (.imp (.classEq A B) (syn_wb (.classEq A C) (.classEq B C))) :=
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
    @g_dfcleq x A B
      (by
        first
        | (aesop))
      (by
        first
        | (aesop))
  have p0001 :=
    @g_biimpi (.classEq A B) (.all x (syn_wb (.classMem (.cv x) A) (.classMem (.cv x) B)))
      p0000
  have p0002 :=
    @g_n_19_21bi (.classEq A B) (syn_wb (.classMem (.cv x) A) (.classMem (.cv x) B)) x
      p0001
  have p0003 :=
    @g_bibi1d (.classEq A B) (.classMem (.cv x) A) (.classMem (.cv x) B)
      (.classMem (.cv x) C) p0002
  have p0004 :=
    @g_albidv (.classEq A B) (syn_wb (.classMem (.cv x) A) (.classMem (.cv x) C))
      (syn_wb (.classMem (.cv x) B) (.classMem (.cv x) C)) x
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
    @g_dfcleq x A C
      (by
        first
        | (aesop))
      (by
        first
        | (aesop))
  have p0006 :=
    @g_dfcleq x B C
      (by
        first
        | (aesop))
      (by
        first
        | (aesop))
  have p0007 :=
    @g_n_3bitr4g (.classEq A B)
      (.all x (syn_wb (.classMem (.cv x) A) (.classMem (.cv x) C)))
      (.all x (syn_wb (.classMem (.cv x) B) (.classMem (.cv x) C))) (.classEq A C)
      (.classEq B C) p0004 p0005 p0006
  exact p0007

@[expose]
noncomputable def g_eqeq1i (A : Class) (B : Class) (C : Class)
    (hyp_eqeq1i_1 : Nominal.NPrf (.classEq A B)) :
    Nominal.NPrf (syn_wb (.classEq A C) (.classEq B C)) :=
  by
  have p0000 := @g_eqeq1 A B C
  have p0001 := Nominal.mp hyp_eqeq1i_1 p0000
  exact p0001

@[expose]
noncomputable def g_eqeq1d (ph : Wff) (A : Class) (B : Class) (C : Class)
    (hyp_eqeq1d_1 : Nominal.NPrf (.imp ph (.classEq A B))) :
    Nominal.NPrf (.imp ph (syn_wb (.classEq A C) (.classEq B C))) :=
  by
  have p0000 := @g_eqeq1 A B C
  have p0001 :=
    @g_syl ph (.classEq A B) (syn_wb (.classEq A C) (.classEq B C)) hyp_eqeq1d_1 p0000
  exact p0001

@[expose]
noncomputable def g_eqeq2 (A : Class) (B : Class) (C : Class) :
    Nominal.NPrf (.imp (.classEq A B) (syn_wb (.classEq C A) (.classEq C B))) :=
  by
  have p0000 := @g_eqeq1 A B C
  have p0001 := @g_eqcom C A
  have p0002 := @g_eqcom C B
  have p0003 :=
    @g_n_3bitr4g (.classEq A B) (.classEq A C) (.classEq B C) (.classEq C A)
      (.classEq C B) p0000 p0001 p0002
  exact p0003

@[expose]
noncomputable def g_eqeq2i (A : Class) (B : Class) (C : Class)
    (hyp_eqeq2i_1 : Nominal.NPrf (.classEq A B)) :
    Nominal.NPrf (syn_wb (.classEq C A) (.classEq C B)) :=
  by
  have p0000 := @g_eqeq2 A B C
  have p0001 := Nominal.mp hyp_eqeq2i_1 p0000
  exact p0001

@[expose]
noncomputable def g_eqeq2d (ph : Wff) (A : Class) (B : Class) (C : Class)
    (hyp_eqeq2d_1 : Nominal.NPrf (.imp ph (.classEq A B))) :
    Nominal.NPrf (.imp ph (syn_wb (.classEq C A) (.classEq C B))) :=
  by
  have p0000 := @g_eqeq2 A B C
  have p0001 :=
    @g_syl ph (.classEq A B) (syn_wb (.classEq C A) (.classEq C B)) hyp_eqeq2d_1 p0000
  exact p0001

@[expose]
noncomputable def g_eqeq12 (A : Class) (B : Class) (C : Class) (D : Class) :
    Nominal.NPrf
      (.imp (syn_wa (.classEq A B) (.classEq C D)) (syn_wb (.classEq A C) (.classEq B D))) :=
  by
  have p0000 := @g_eqeq1 A B C
  have p0001 := @g_eqeq2 C D B
  have p0002 :=
    @g_sylan9bb (.classEq A B) (.classEq A C) (.classEq B C) (.classEq C D) (.classEq B D)
      p0000 p0001
  exact p0002

@[expose]
noncomputable def g_eqeq12i (A : Class) (B : Class) (C : Class) (D : Class)
    (hyp_eqeq12i_1 : Nominal.NPrf (.classEq A B))
    (hyp_eqeq12i_2 : Nominal.NPrf (.classEq C D)) :
    Nominal.NPrf (syn_wb (.classEq A C) (.classEq B D)) :=
  by
  have p0000 := @g_eqeq12 A B C D
  have p0001 :=
    @g_mp2an (.classEq A B) (.classEq C D) (syn_wb (.classEq A C) (.classEq B D))
      hyp_eqeq12i_1 hyp_eqeq12i_2 p0000
  exact p0001

@[expose]
noncomputable def g_eqeq12d (ph : Wff) (A : Class) (B : Class) (C : Class) (D : Class)
    (hyp_eqeq12d_1 : Nominal.NPrf (.imp ph (.classEq A B)))
    (hyp_eqeq12d_2 : Nominal.NPrf (.imp ph (.classEq C D))) :
    Nominal.NPrf (.imp ph (syn_wb (.classEq A C) (.classEq B D))) :=
  by
  have p0000 := @g_eqeq12 A B C D
  have p0001 :=
    @g_syl2anc ph (.classEq A B) (.classEq C D) (syn_wb (.classEq A C) (.classEq B D))
      hyp_eqeq12d_1 hyp_eqeq12d_2 p0000
  exact p0001

@[expose]
noncomputable def g_eqeqan12d (ph : Wff) (ps : Wff) (A : Class) (B : Class) (C : Class)
    (D : Class) (hyp_eqeqan12d_1 : Nominal.NPrf (.imp ph (.classEq A B)))
    (hyp_eqeqan12d_2 : Nominal.NPrf (.imp ps (.classEq C D))) :
    Nominal.NPrf (.imp (syn_wa ph ps) (syn_wb (.classEq A C) (.classEq B D))) :=
  by
  have p0000 := @g_eqeq12 A B C D
  have p0001 :=
    @g_syl2an ph (.classEq A B) (.classEq C D) (syn_wb (.classEq A C) (.classEq B D)) ps
      hyp_eqeqan12d_1 hyp_eqeqan12d_2 p0000
  exact p0001

@[expose]
noncomputable def g_eqtr (A : Class) (B : Class) (C : Class) :
    Nominal.NPrf (.imp (syn_wa (.classEq A B) (.classEq B C)) (.classEq A C)) :=
  by
  have p0000 := @g_eqeq1 A B C
  have p0001 := @g_biimpar (.classEq A B) (.classEq A C) (.classEq B C) p0000
  exact p0001

@[expose]
noncomputable def g_eqtr2 (A : Class) (B : Class) (C : Class) :
    Nominal.NPrf (.imp (syn_wa (.classEq A B) (.classEq A C)) (.classEq B C)) :=
  by
  have p0000 := @g_eqcom A B
  have p0001 := @g_eqtr B A C
  have p0002 :=
    @g_sylanb (.classEq A B) (.classEq B A) (.classEq A C) (.classEq B C) p0000 p0001
  exact p0002

@[expose]
noncomputable def g_eqtr3 (A : Class) (B : Class) (C : Class) :
    Nominal.NPrf (.imp (syn_wa (.classEq A C) (.classEq B C)) (.classEq A B)) :=
  by
  have p0000 := @g_eqcom B C
  have p0001 := @g_eqtr A C B
  have p0002 :=
    @g_sylan2b (.classEq B C) (.classEq A C) (.classEq C B) (.classEq A B) p0000 p0001
  exact p0002

@[expose]
noncomputable def g_eqtri (A : Class) (B : Class) (C : Class)
    (hyp_eqtri_1 : Nominal.NPrf (.classEq A B))
    (hyp_eqtri_2 : Nominal.NPrf (.classEq B C)) : Nominal.NPrf (.classEq A C) :=
  by
  have p0000 := @g_eqeq2i B C A hyp_eqtri_2
  have p0001 := @g_mpbi (.classEq A B) (.classEq A C) hyp_eqtri_1 p0000
  exact p0001

@[expose]
noncomputable def g_eqtr2i (A : Class) (B : Class) (C : Class)
    (hyp_eqtr2i_1 : Nominal.NPrf (.classEq A B))
    (hyp_eqtr2i_2 : Nominal.NPrf (.classEq B C)) : Nominal.NPrf (.classEq C A) :=
  by
  have p0000 := @g_eqtri A B C hyp_eqtr2i_1 hyp_eqtr2i_2
  have p0001 := @g_eqcomi A C p0000
  exact p0001

@[expose]
noncomputable def g_eqtr3i (A : Class) (B : Class) (C : Class)
    (hyp_eqtr3i_1 : Nominal.NPrf (.classEq A B))
    (hyp_eqtr3i_2 : Nominal.NPrf (.classEq A C)) : Nominal.NPrf (.classEq B C) :=
  by
  have p0000 := @g_eqcomi A B hyp_eqtr3i_1
  have p0001 := @g_eqtri B A C p0000 hyp_eqtr3i_2
  exact p0001

@[expose]
noncomputable def g_eqtr4i (A : Class) (B : Class) (C : Class)
    (hyp_eqtr4i_1 : Nominal.NPrf (.classEq A B))
    (hyp_eqtr4i_2 : Nominal.NPrf (.classEq C B)) : Nominal.NPrf (.classEq A C) :=
  by
  have p0000 := @g_eqcomi C B hyp_eqtr4i_2
  have p0001 := @g_eqtri A B C hyp_eqtr4i_1 p0000
  exact p0001

@[expose]
noncomputable def g_n_3eqtri (A : Class) (B : Class) (C : Class) (D : Class)
    (hyp_n_3eqtri_1 : Nominal.NPrf (.classEq A B))
    (hyp_n_3eqtri_2 : Nominal.NPrf (.classEq B C))
    (hyp_n_3eqtri_3 : Nominal.NPrf (.classEq C D)) : Nominal.NPrf (.classEq A D) :=
  by
  have p0000 := @g_eqtri B C D hyp_n_3eqtri_2 hyp_n_3eqtri_3
  have p0001 := @g_eqtri A B D hyp_n_3eqtri_1 p0000
  exact p0001

@[expose]
noncomputable def g_n_3eqtrri (A : Class) (B : Class) (C : Class) (D : Class)
    (hyp_n_3eqtri_1 : Nominal.NPrf (.classEq A B))
    (hyp_n_3eqtri_2 : Nominal.NPrf (.classEq B C))
    (hyp_n_3eqtri_3 : Nominal.NPrf (.classEq C D)) : Nominal.NPrf (.classEq D A) :=
  by
  have p0000 := @g_eqtri A B C hyp_n_3eqtri_1 hyp_n_3eqtri_2
  have p0001 := @g_eqtr2i A C D p0000 hyp_n_3eqtri_3
  exact p0001

@[expose]
noncomputable def g_n_3eqtr2i (A : Class) (B : Class) (C : Class) (D : Class)
    (hyp_n_3eqtr2i_1 : Nominal.NPrf (.classEq A B))
    (hyp_n_3eqtr2i_2 : Nominal.NPrf (.classEq C B))
    (hyp_n_3eqtr2i_3 : Nominal.NPrf (.classEq C D)) : Nominal.NPrf (.classEq A D) :=
  by
  have p0000 := @g_eqtr4i A B C hyp_n_3eqtr2i_1 hyp_n_3eqtr2i_2
  have p0001 := @g_eqtri A C D p0000 hyp_n_3eqtr2i_3
  exact p0001

@[expose]
noncomputable def g_n_3eqtr2ri (A : Class) (B : Class) (C : Class) (D : Class)
    (hyp_n_3eqtr2i_1 : Nominal.NPrf (.classEq A B))
    (hyp_n_3eqtr2i_2 : Nominal.NPrf (.classEq C B))
    (hyp_n_3eqtr2i_3 : Nominal.NPrf (.classEq C D)) : Nominal.NPrf (.classEq D A) :=
  by
  have p0000 := @g_eqtr4i A B C hyp_n_3eqtr2i_1 hyp_n_3eqtr2i_2
  have p0001 := @g_eqtr2i A C D p0000 hyp_n_3eqtr2i_3
  exact p0001

@[expose]
noncomputable def g_n_3eqtr3i (A : Class) (B : Class) (C : Class) (D : Class)
    (hyp_n_3eqtr3i_1 : Nominal.NPrf (.classEq A B))
    (hyp_n_3eqtr3i_2 : Nominal.NPrf (.classEq A C))
    (hyp_n_3eqtr3i_3 : Nominal.NPrf (.classEq B D)) : Nominal.NPrf (.classEq C D) :=
  by
  have p0000 := @g_eqtr3i A B C hyp_n_3eqtr3i_1 hyp_n_3eqtr3i_2
  have p0001 := @g_eqtr3i B C D p0000 hyp_n_3eqtr3i_3
  exact p0001

@[expose]
noncomputable def g_n_3eqtr4i (A : Class) (B : Class) (C : Class) (D : Class)
    (hyp_n_3eqtr4i_1 : Nominal.NPrf (.classEq A B))
    (hyp_n_3eqtr4i_2 : Nominal.NPrf (.classEq C A))
    (hyp_n_3eqtr4i_3 : Nominal.NPrf (.classEq D B)) : Nominal.NPrf (.classEq C D) :=
  by
  have p0000 := @g_eqtr4i D B A hyp_n_3eqtr4i_3 hyp_n_3eqtr4i_1
  have p0001 := @g_eqtr4i C A D hyp_n_3eqtr4i_2 p0000
  exact p0001

@[expose]
noncomputable def g_n_3eqtr4ri (A : Class) (B : Class) (C : Class) (D : Class)
    (hyp_n_3eqtr4i_1 : Nominal.NPrf (.classEq A B))
    (hyp_n_3eqtr4i_2 : Nominal.NPrf (.classEq C A))
    (hyp_n_3eqtr4i_3 : Nominal.NPrf (.classEq D B)) : Nominal.NPrf (.classEq D C) :=
  by
  have p0000 := @g_eqtr4i D B A hyp_n_3eqtr4i_3 hyp_n_3eqtr4i_1
  have p0001 := @g_eqtr4i D A C p0000 hyp_n_3eqtr4i_2
  exact p0001

@[expose]
noncomputable def g_eqtrd (ph : Wff) (A : Class) (B : Class) (C : Class)
    (hyp_eqtrd_1 : Nominal.NPrf (.imp ph (.classEq A B)))
    (hyp_eqtrd_2 : Nominal.NPrf (.imp ph (.classEq B C))) :
    Nominal.NPrf (.imp ph (.classEq A C)) :=
  by
  have p0000 := @g_eqeq2d ph B C A hyp_eqtrd_2
  have p0001 := @g_mpbid ph (.classEq A B) (.classEq A C) hyp_eqtrd_1 p0000
  exact p0001

@[expose]
noncomputable def g_eqtr2d (ph : Wff) (A : Class) (B : Class) (C : Class)
    (hyp_eqtr2d_1 : Nominal.NPrf (.imp ph (.classEq A B)))
    (hyp_eqtr2d_2 : Nominal.NPrf (.imp ph (.classEq B C))) :
    Nominal.NPrf (.imp ph (.classEq C A)) :=
  by
  have p0000 := @g_eqtrd ph A B C hyp_eqtr2d_1 hyp_eqtr2d_2
  have p0001 := @g_eqcomd ph A C p0000
  exact p0001

@[expose]
noncomputable def g_eqtr3d (ph : Wff) (A : Class) (B : Class) (C : Class)
    (hyp_eqtr3d_1 : Nominal.NPrf (.imp ph (.classEq A B)))
    (hyp_eqtr3d_2 : Nominal.NPrf (.imp ph (.classEq A C))) :
    Nominal.NPrf (.imp ph (.classEq B C)) :=
  by
  have p0000 := @g_eqcomd ph A B hyp_eqtr3d_1
  have p0001 := @g_eqtrd ph B A C p0000 hyp_eqtr3d_2
  exact p0001

@[expose]
noncomputable def g_eqtr4d (ph : Wff) (A : Class) (B : Class) (C : Class)
    (hyp_eqtr4d_1 : Nominal.NPrf (.imp ph (.classEq A B)))
    (hyp_eqtr4d_2 : Nominal.NPrf (.imp ph (.classEq C B))) :
    Nominal.NPrf (.imp ph (.classEq A C)) :=
  by
  have p0000 := @g_eqcomd ph C B hyp_eqtr4d_2
  have p0001 := @g_eqtrd ph A B C hyp_eqtr4d_1 p0000
  exact p0001

@[expose]
noncomputable def g_n_3eqtrd (ph : Wff) (A : Class) (B : Class) (C : Class) (D : Class)
    (hyp_n_3eqtrd_1 : Nominal.NPrf (.imp ph (.classEq A B)))
    (hyp_n_3eqtrd_2 : Nominal.NPrf (.imp ph (.classEq B C)))
    (hyp_n_3eqtrd_3 : Nominal.NPrf (.imp ph (.classEq C D))) :
    Nominal.NPrf (.imp ph (.classEq A D)) :=
  by
  have p0000 := @g_eqtrd ph B C D hyp_n_3eqtrd_2 hyp_n_3eqtrd_3
  have p0001 := @g_eqtrd ph A B D hyp_n_3eqtrd_1 p0000
  exact p0001

@[expose]
noncomputable def g_n_3eqtr3d (ph : Wff) (A : Class) (B : Class) (C : Class) (D : Class)
    (hyp_n_3eqtr3d_1 : Nominal.NPrf (.imp ph (.classEq A B)))
    (hyp_n_3eqtr3d_2 : Nominal.NPrf (.imp ph (.classEq A C)))
    (hyp_n_3eqtr3d_3 : Nominal.NPrf (.imp ph (.classEq B D))) :
    Nominal.NPrf (.imp ph (.classEq C D)) :=
  by
  have p0000 := @g_eqtr3d ph A B C hyp_n_3eqtr3d_1 hyp_n_3eqtr3d_2
  have p0001 := @g_eqtr3d ph B C D p0000 hyp_n_3eqtr3d_3
  exact p0001

@[expose]
noncomputable def g_n_3eqtr4d (ph : Wff) (A : Class) (B : Class) (C : Class) (D : Class)
    (hyp_n_3eqtr4d_1 : Nominal.NPrf (.imp ph (.classEq A B)))
    (hyp_n_3eqtr4d_2 : Nominal.NPrf (.imp ph (.classEq C A)))
    (hyp_n_3eqtr4d_3 : Nominal.NPrf (.imp ph (.classEq D B))) :
    Nominal.NPrf (.imp ph (.classEq C D)) :=
  by
  have p0000 := @g_eqtr4d ph D B A hyp_n_3eqtr4d_3 hyp_n_3eqtr4d_1
  have p0001 := @g_eqtr4d ph C A D hyp_n_3eqtr4d_2 p0000
  exact p0001

@[expose]
noncomputable def g_syl5eq (ph : Wff) (A : Class) (B : Class) (C : Class)
    (hyp_syl5eq_1 : Nominal.NPrf (.classEq A B))
    (hyp_syl5eq_2 : Nominal.NPrf (.imp ph (.classEq B C))) :
    Nominal.NPrf (.imp ph (.classEq A C)) :=
  by
  have p0000 := @g_a1i (.classEq A B) ph hyp_syl5eq_1
  have p0001 := @g_eqtrd ph A B C p0000 hyp_syl5eq_2
  exact p0001

@[expose]
noncomputable def g_syl5req (ph : Wff) (A : Class) (B : Class) (C : Class)
    (hyp_syl5req_1 : Nominal.NPrf (.classEq A B))
    (hyp_syl5req_2 : Nominal.NPrf (.imp ph (.classEq B C))) :
    Nominal.NPrf (.imp ph (.classEq C A)) :=
  by
  have p0000 := @g_syl5eq ph A B C hyp_syl5req_1 hyp_syl5req_2
  have p0001 := @g_eqcomd ph A C p0000
  exact p0001

@[expose]
noncomputable def g_syl5eqr (ph : Wff) (A : Class) (B : Class) (C : Class)
    (hyp_syl5eqr_1 : Nominal.NPrf (.classEq B A))
    (hyp_syl5eqr_2 : Nominal.NPrf (.imp ph (.classEq B C))) :
    Nominal.NPrf (.imp ph (.classEq A C)) :=
  by
  have p0000 := @g_eqcomi B A hyp_syl5eqr_1
  have p0001 := @g_syl5eq ph A B C p0000 hyp_syl5eqr_2
  exact p0001

@[expose]
noncomputable def g_syl5reqr (ph : Wff) (A : Class) (B : Class) (C : Class)
    (hyp_syl5reqr_1 : Nominal.NPrf (.classEq B A))
    (hyp_syl5reqr_2 : Nominal.NPrf (.imp ph (.classEq B C))) :
    Nominal.NPrf (.imp ph (.classEq C A)) :=
  by
  have p0000 := @g_eqcomi B A hyp_syl5reqr_1
  have p0001 := @g_syl5req ph A B C p0000 hyp_syl5reqr_2
  exact p0001

@[expose]
noncomputable def g_syl6eq (ph : Wff) (A : Class) (B : Class) (C : Class)
    (hyp_syl6eq_1 : Nominal.NPrf (.imp ph (.classEq A B)))
    (hyp_syl6eq_2 : Nominal.NPrf (.classEq B C)) :
    Nominal.NPrf (.imp ph (.classEq A C)) :=
  by
  have p0000 := @g_a1i (.classEq B C) ph hyp_syl6eq_2
  have p0001 := @g_eqtrd ph A B C hyp_syl6eq_1 p0000
  exact p0001

@[expose]
noncomputable def g_syl6req (ph : Wff) (A : Class) (B : Class) (C : Class)
    (hyp_syl6req_1 : Nominal.NPrf (.imp ph (.classEq A B)))
    (hyp_syl6req_2 : Nominal.NPrf (.classEq B C)) :
    Nominal.NPrf (.imp ph (.classEq C A)) :=
  by
  have p0000 := @g_syl6eq ph A B C hyp_syl6req_1 hyp_syl6req_2
  have p0001 := @g_eqcomd ph A C p0000
  exact p0001

@[expose]
noncomputable def g_syl6eqr (ph : Wff) (A : Class) (B : Class) (C : Class)
    (hyp_syl6eqr_1 : Nominal.NPrf (.imp ph (.classEq A B)))
    (hyp_syl6eqr_2 : Nominal.NPrf (.classEq C B)) :
    Nominal.NPrf (.imp ph (.classEq A C)) :=
  by
  have p0000 := @g_eqcomi C B hyp_syl6eqr_2
  have p0001 := @g_syl6eq ph A B C hyp_syl6eqr_1 p0000
  exact p0001

@[expose]
noncomputable def g_syl6reqr (ph : Wff) (A : Class) (B : Class) (C : Class)
    (hyp_syl6reqr_1 : Nominal.NPrf (.imp ph (.classEq A B)))
    (hyp_syl6reqr_2 : Nominal.NPrf (.classEq C B)) :
    Nominal.NPrf (.imp ph (.classEq C A)) :=
  by
  have p0000 := @g_eqcomi C B hyp_syl6reqr_2
  have p0001 := @g_syl6req ph A B C hyp_syl6reqr_1 p0000
  exact p0001

@[expose]
noncomputable def g_sylan9eq (ph : Wff) (ps : Wff) (A : Class) (B : Class) (C : Class)
    (hyp_sylan9eq_1 : Nominal.NPrf (.imp ph (.classEq A B)))
    (hyp_sylan9eq_2 : Nominal.NPrf (.imp ps (.classEq B C))) :
    Nominal.NPrf (.imp (syn_wa ph ps) (.classEq A C)) :=
  by
  have p0000 := @g_eqtr A B C
  have p0001 :=
    @g_syl2an ph (.classEq A B) (.classEq B C) (.classEq A C) ps hyp_sylan9eq_1
      hyp_sylan9eq_2 p0000
  exact p0001

@[expose]
noncomputable def g_sylan9eqr (ph : Wff) (ps : Wff) (A : Class) (B : Class) (C : Class)
    (hyp_sylan9eqr_1 : Nominal.NPrf (.imp ph (.classEq A B)))
    (hyp_sylan9eqr_2 : Nominal.NPrf (.imp ps (.classEq B C))) :
    Nominal.NPrf (.imp (syn_wa ps ph) (.classEq A C)) :=
  by
  have p0000 := @g_sylan9eq ph ps A B C hyp_sylan9eqr_1 hyp_sylan9eqr_2
  have p0001 := @g_ancoms ph ps (.classEq A C) p0000
  exact p0001

@[expose]
noncomputable def g_n_3eqtr3g (ph : Wff) (A : Class) (B : Class) (C : Class) (D : Class)
    (hyp_n_3eqtr3g_1 : Nominal.NPrf (.imp ph (.classEq A B)))
    (hyp_n_3eqtr3g_2 : Nominal.NPrf (.classEq A C))
    (hyp_n_3eqtr3g_3 : Nominal.NPrf (.classEq B D)) :
    Nominal.NPrf (.imp ph (.classEq C D)) :=
  by
  have p0000 := @g_syl5eqr ph C A B hyp_n_3eqtr3g_2 hyp_n_3eqtr3g_1
  have p0001 := @g_syl6eq ph C B D p0000 hyp_n_3eqtr3g_3
  exact p0001

@[expose]
noncomputable def g_n_3eqtr4g (ph : Wff) (A : Class) (B : Class) (C : Class) (D : Class)
    (hyp_n_3eqtr4g_1 : Nominal.NPrf (.imp ph (.classEq A B)))
    (hyp_n_3eqtr4g_2 : Nominal.NPrf (.classEq C A))
    (hyp_n_3eqtr4g_3 : Nominal.NPrf (.classEq D B)) :
    Nominal.NPrf (.imp ph (.classEq C D)) :=
  by
  have p0000 := @g_syl5eq ph C A B hyp_n_3eqtr4g_2 hyp_n_3eqtr4g_1
  have p0001 := @g_syl6eqr ph C B D p0000 hyp_n_3eqtr4g_3
  exact p0001

@[expose]
noncomputable def g_n_3eqtr4a (ph : Wff) (A : Class) (B : Class) (C : Class) (D : Class)
    (hyp_n_3eqtr4a_1 : Nominal.NPrf (.classEq A B))
    (hyp_n_3eqtr4a_2 : Nominal.NPrf (.imp ph (.classEq C A)))
    (hyp_n_3eqtr4a_3 : Nominal.NPrf (.imp ph (.classEq D B))) :
    Nominal.NPrf (.imp ph (.classEq C D)) :=
  by
  have p0000 := @g_syl6eq ph C A B hyp_n_3eqtr4a_2 hyp_n_3eqtr4a_1
  have p0001 := @g_eqtr4d ph C B D p0000 hyp_n_3eqtr4a_3
  exact p0001

@[expose]
noncomputable def g_eleq1 (A : Class) (B : Class) (C : Class) :
    Nominal.NPrf (.imp (.classEq A B) (syn_wb (.classMem A C) (.classMem B C))) :=
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
  have p0000 := @g_eqeq2 A B (.cv x)
  have p0001 :=
    @g_anbi1d (.classEq A B) (.classEq (.cv x) A) (.classEq (.cv x) B)
      (.classMem (.cv x) C) p0000
  have p0002 :=
    @g_exbidv (.classEq A B) (syn_wa (.classEq (.cv x) A) (.classMem (.cv x) C))
      (syn_wa (.classEq (.cv x) B) (.classMem (.cv x) C)) x
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
    @g_n_3bitr4g (.classEq A B)
      (syn_wex x (syn_wa (.classEq (.cv x) A) (.classMem (.cv x) C)))
      (syn_wex x (syn_wa (.classEq (.cv x) B) (.classMem (.cv x) C))) (.classMem A C)
      (.classMem B C) p0002 p0003 p0004
  exact p0005

@[expose]
noncomputable def g_eleq2 (A : Class) (B : Class) (C : Class) :
    Nominal.NPrf (.imp (.classEq A B) (syn_wb (.classMem C A) (.classMem C B))) :=
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
    @g_dfcleq x A B
      (by
        first
        | (aesop))
      (by
        first
        | (aesop))
  have p0001 :=
    @g_biimpi (.classEq A B) (.all x (syn_wb (.classMem (.cv x) A) (.classMem (.cv x) B)))
      p0000
  have p0002 :=
    @g_n_19_21bi (.classEq A B) (syn_wb (.classMem (.cv x) A) (.classMem (.cv x) B)) x
      p0001
  have p0003 :=
    @g_anbi2d (.classEq A B) (.classMem (.cv x) A) (.classMem (.cv x) B)
      (.classEq (.cv x) C) p0002
  have p0004 :=
    @g_exbidv (.classEq A B) (syn_wa (.classEq (.cv x) C) (.classMem (.cv x) A))
      (syn_wa (.classEq (.cv x) C) (.classMem (.cv x) B)) x
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
    @g_n_3bitr4g (.classEq A B)
      (syn_wex x (syn_wa (.classEq (.cv x) C) (.classMem (.cv x) A)))
      (syn_wex x (syn_wa (.classEq (.cv x) C) (.classMem (.cv x) B))) (.classMem C A)
      (.classMem C B) p0004 p0005 p0006
  exact p0007

@[expose]
noncomputable def g_eleq12 (A : Class) (B : Class) (C : Class) (D : Class) :
    Nominal.NPrf
      (.imp (syn_wa (.classEq A B) (.classEq C D)) (syn_wb (.classMem A C) (.classMem B D))) :=
  by
  have p0000 := @g_eleq1 A B C
  have p0001 := @g_eleq2 C D B
  have p0002 :=
    @g_sylan9bb (.classEq A B) (.classMem A C) (.classMem B C) (.classEq C D)
      (.classMem B D) p0000 p0001
  exact p0002

@[expose]
noncomputable def g_eleq1i (A : Class) (B : Class) (C : Class)
    (hyp_eleq1i_1 : Nominal.NPrf (.classEq A B)) :
    Nominal.NPrf (syn_wb (.classMem A C) (.classMem B C)) :=
  by
  have p0000 := @g_eleq1 A B C
  have p0001 := Nominal.mp hyp_eleq1i_1 p0000
  exact p0001

@[expose]
noncomputable def g_eleq2i (A : Class) (B : Class) (C : Class)
    (hyp_eleq1i_1 : Nominal.NPrf (.classEq A B)) :
    Nominal.NPrf (syn_wb (.classMem C A) (.classMem C B)) :=
  by
  have p0000 := @g_eleq2 A B C
  have p0001 := Nominal.mp hyp_eleq1i_1 p0000
  exact p0001

@[expose]
noncomputable def g_eleq1d (ph : Wff) (A : Class) (B : Class) (C : Class)
    (hyp_eleq1d_1 : Nominal.NPrf (.imp ph (.classEq A B))) :
    Nominal.NPrf (.imp ph (syn_wb (.classMem A C) (.classMem B C))) :=
  by
  have p0000 := @g_eleq1 A B C
  have p0001 :=
    @g_syl ph (.classEq A B) (syn_wb (.classMem A C) (.classMem B C)) hyp_eleq1d_1 p0000
  exact p0001

@[expose]
noncomputable def g_eleq2d (ph : Wff) (A : Class) (B : Class) (C : Class)
    (hyp_eleq1d_1 : Nominal.NPrf (.imp ph (.classEq A B))) :
    Nominal.NPrf (.imp ph (syn_wb (.classMem C A) (.classMem C B))) :=
  by
  have p0000 := @g_eleq2 A B C
  have p0001 :=
    @g_syl ph (.classEq A B) (syn_wb (.classMem C A) (.classMem C B)) hyp_eleq1d_1 p0000
  exact p0001

@[expose]
noncomputable def g_eleq1a (A : Class) (B : Class) (C : Class) :
    Nominal.NPrf (.imp (.classMem A B) (.imp (.classEq C A) (.classMem C B))) :=
  by
  have p0000 := @g_eleq1 C A B
  have p0001 := @g_biimprcd (.classEq C A) (.classMem C B) (.classMem A B) p0000
  exact p0001

@[expose]
noncomputable def g_eqeltri (A : Class) (B : Class) (C : Class)
    (hyp_eqeltr_1 : Nominal.NPrf (.classEq A B))
    (hyp_eqeltr_2 : Nominal.NPrf (.classMem B C)) : Nominal.NPrf (.classMem A C) :=
  by
  have p0000 := @g_eleq1i A B C hyp_eqeltr_1
  have p0001 := @g_mpbir (.classMem A C) (.classMem B C) hyp_eqeltr_2 p0000
  exact p0001

@[expose]
noncomputable def g_eqeltrri (A : Class) (B : Class) (C : Class)
    (hyp_eqeltrr_1 : Nominal.NPrf (.classEq A B))
    (hyp_eqeltrr_2 : Nominal.NPrf (.classMem A C)) : Nominal.NPrf (.classMem B C) :=
  by
  have p0000 := @g_eqcomi A B hyp_eqeltrr_1
  have p0001 := @g_eqeltri B A C p0000 hyp_eqeltrr_2
  exact p0001

@[expose]
noncomputable def g_eleqtri (A : Class) (B : Class) (C : Class)
    (hyp_eleqtr_1 : Nominal.NPrf (.classMem A B))
    (hyp_eleqtr_2 : Nominal.NPrf (.classEq B C)) : Nominal.NPrf (.classMem A C) :=
  by
  have p0000 := @g_eleq2i B C A hyp_eleqtr_2
  have p0001 := @g_mpbi (.classMem A B) (.classMem A C) hyp_eleqtr_1 p0000
  exact p0001

@[expose]
noncomputable def g_eleqtrri (A : Class) (B : Class) (C : Class)
    (hyp_eleqtrr_1 : Nominal.NPrf (.classMem A B))
    (hyp_eleqtrr_2 : Nominal.NPrf (.classEq C B)) : Nominal.NPrf (.classMem A C) :=
  by
  have p0000 := @g_eqcomi C B hyp_eleqtrr_2
  have p0001 := @g_eleqtri A B C hyp_eleqtrr_1 p0000
  exact p0001

@[expose]
noncomputable def g_eqeltrd (ph : Wff) (A : Class) (B : Class) (C : Class)
    (hyp_eqeltrd_1 : Nominal.NPrf (.imp ph (.classEq A B)))
    (hyp_eqeltrd_2 : Nominal.NPrf (.imp ph (.classMem B C))) :
    Nominal.NPrf (.imp ph (.classMem A C)) :=
  by
  have p0000 := @g_eleq1d ph A B C hyp_eqeltrd_1
  have p0001 := @g_mpbird ph (.classMem A C) (.classMem B C) hyp_eqeltrd_2 p0000
  exact p0001

@[expose]
noncomputable def g_eqeltrrd (ph : Wff) (A : Class) (B : Class) (C : Class)
    (hyp_eqeltrrd_1 : Nominal.NPrf (.imp ph (.classEq A B)))
    (hyp_eqeltrrd_2 : Nominal.NPrf (.imp ph (.classMem A C))) :
    Nominal.NPrf (.imp ph (.classMem B C)) :=
  by
  have p0000 := @g_eqcomd ph A B hyp_eqeltrrd_1
  have p0001 := @g_eqeltrd ph B A C p0000 hyp_eqeltrrd_2
  exact p0001

@[expose]
noncomputable def g_eleqtrd (ph : Wff) (A : Class) (B : Class) (C : Class)
    (hyp_eleqtrd_1 : Nominal.NPrf (.imp ph (.classMem A B)))
    (hyp_eleqtrd_2 : Nominal.NPrf (.imp ph (.classEq B C))) :
    Nominal.NPrf (.imp ph (.classMem A C)) :=
  by
  have p0000 := @g_eleq2d ph B C A hyp_eleqtrd_2
  have p0001 := @g_mpbid ph (.classMem A B) (.classMem A C) hyp_eleqtrd_1 p0000
  exact p0001

@[expose]
noncomputable def g_eleqtrrd (ph : Wff) (A : Class) (B : Class) (C : Class)
    (hyp_eleqtrrd_1 : Nominal.NPrf (.imp ph (.classMem A B)))
    (hyp_eleqtrrd_2 : Nominal.NPrf (.imp ph (.classEq C B))) :
    Nominal.NPrf (.imp ph (.classMem A C)) :=
  by
  have p0000 := @g_eqcomd ph C B hyp_eleqtrrd_2
  have p0001 := @g_eleqtrd ph A B C hyp_eleqtrrd_1 p0000
  exact p0001

@[expose]
noncomputable def g_syl5eqel (ph : Wff) (A : Class) (B : Class) (C : Class)
    (hyp_syl5eqel_1 : Nominal.NPrf (.classEq A B))
    (hyp_syl5eqel_2 : Nominal.NPrf (.imp ph (.classMem B C))) :
    Nominal.NPrf (.imp ph (.classMem A C)) :=
  by
  have p0000 := @g_a1i (.classEq A B) ph hyp_syl5eqel_1
  have p0001 := @g_eqeltrd ph A B C p0000 hyp_syl5eqel_2
  exact p0001

@[expose]
noncomputable def g_syl5eqelr (ph : Wff) (A : Class) (B : Class) (C : Class)
    (hyp_syl5eqelr_1 : Nominal.NPrf (.classEq B A))
    (hyp_syl5eqelr_2 : Nominal.NPrf (.imp ph (.classMem B C))) :
    Nominal.NPrf (.imp ph (.classMem A C)) :=
  by
  have p0000 := @g_eqcomi B A hyp_syl5eqelr_1
  have p0001 := @g_syl5eqel ph A B C p0000 hyp_syl5eqelr_2
  exact p0001

@[expose]
noncomputable def g_syl5eleq (ph : Wff) (A : Class) (B : Class) (C : Class)
    (hyp_syl5eleq_1 : Nominal.NPrf (.classMem A B))
    (hyp_syl5eleq_2 : Nominal.NPrf (.imp ph (.classEq B C))) :
    Nominal.NPrf (.imp ph (.classMem A C)) :=
  by
  have p0000 := @g_a1i (.classMem A B) ph hyp_syl5eleq_1
  have p0001 := @g_eleqtrd ph A B C p0000 hyp_syl5eleq_2
  exact p0001

@[expose]
noncomputable def g_syl5eleqr (ph : Wff) (A : Class) (B : Class) (C : Class)
    (hyp_syl5eleqr_1 : Nominal.NPrf (.classMem A B))
    (hyp_syl5eleqr_2 : Nominal.NPrf (.imp ph (.classEq C B))) :
    Nominal.NPrf (.imp ph (.classMem A C)) :=
  by
  have p0000 := @g_eqcomd ph C B hyp_syl5eleqr_2
  have p0001 := @g_syl5eleq ph A B C hyp_syl5eleqr_1 p0000
  exact p0001

@[expose]
noncomputable def g_syl6eqel (ph : Wff) (A : Class) (B : Class) (C : Class)
    (hyp_syl6eqel_1 : Nominal.NPrf (.imp ph (.classEq A B)))
    (hyp_syl6eqel_2 : Nominal.NPrf (.classMem B C)) :
    Nominal.NPrf (.imp ph (.classMem A C)) :=
  by
  have p0000 := @g_a1i (.classMem B C) ph hyp_syl6eqel_2
  have p0001 := @g_eqeltrd ph A B C hyp_syl6eqel_1 p0000
  exact p0001

@[expose]
noncomputable def g_syl6eqelr (ph : Wff) (A : Class) (B : Class) (C : Class)
    (hyp_syl6eqelr_1 : Nominal.NPrf (.imp ph (.classEq B A)))
    (hyp_syl6eqelr_2 : Nominal.NPrf (.classMem B C)) :
    Nominal.NPrf (.imp ph (.classMem A C)) :=
  by
  have p0000 := @g_eqcomd ph B A hyp_syl6eqelr_1
  have p0001 := @g_syl6eqel ph A B C p0000 hyp_syl6eqelr_2
  exact p0001

@[expose]
noncomputable def g_syl6eleq (ph : Wff) (A : Class) (B : Class) (C : Class)
    (hyp_syl6eleq_1 : Nominal.NPrf (.imp ph (.classMem A B)))
    (hyp_syl6eleq_2 : Nominal.NPrf (.classEq B C)) :
    Nominal.NPrf (.imp ph (.classMem A C)) :=
  by
  have p0000 := @g_a1i (.classEq B C) ph hyp_syl6eleq_2
  have p0001 := @g_eleqtrd ph A B C hyp_syl6eleq_1 p0000
  exact p0001

@[expose]
noncomputable def g_syl6eleqr (ph : Wff) (A : Class) (B : Class) (C : Class)
    (hyp_syl6eleqr_1 : Nominal.NPrf (.imp ph (.classMem A B)))
    (hyp_syl6eleqr_2 : Nominal.NPrf (.classEq C B)) :
    Nominal.NPrf (.imp ph (.classMem A C)) :=
  by
  have p0000 := @g_eqcomi C B hyp_syl6eleqr_2
  have p0001 := @g_syl6eleq ph A B C hyp_syl6eleqr_1 p0000
  exact p0001

@[expose]
noncomputable def g_eleq2s (ph : Wff) (A : Class) (B : Class) (C : Class)
    (hyp_eleq2s_1 : Nominal.NPrf (.imp (.classMem A B) ph))
    (hyp_eleq2s_2 : Nominal.NPrf (.classEq C B)) :
    Nominal.NPrf (.imp (.classMem A C) ph) :=
  by
  have p0000 := @g_eleq2i C B A hyp_eleq2s_2
  have p0001 := @g_sylbi (.classMem A C) (.classMem A B) ph p0000 hyp_eleq2s_1
  exact p0001

@[expose]
noncomputable def g_neleqtrd (ph : Wff) (A : Class) (B : Class) (C : Class)
    (hyp_neleqtrd_1 : Nominal.NPrf (.imp ph (.neg (.classMem C A))))
    (hyp_neleqtrd_2 : Nominal.NPrf (.imp ph (.classEq A B))) :
    Nominal.NPrf (.imp ph (.neg (.classMem C B))) :=
  by
  have p0000 := @g_eleq2d ph A B C hyp_neleqtrd_2
  have p0001 := @g_mtbid ph (.classMem C A) (.classMem C B) hyp_neleqtrd_1 p0000
  exact p0001

@[expose]
noncomputable def g_cleqh (x : Var) (y : Var) (A : Class) (B : Class) (dv_A_y : y ∉ A.fv)
    (dv_B_y : y ∉ B.fv) (dv_x_y : x ≠ y)
    (hyp_cleqh_1 : Nominal.NPrf (.imp (.classMem (.cv y) A) (.all x (.classMem (.cv y) A))))
    (hyp_cleqh_2 : Nominal.NPrf (.imp (.classMem (.cv y) B) (.all x (.classMem (.cv y) B)))) :
    Nominal.NPrf
      (syn_wb (.classEq A B) (.all x (syn_wb (.classMem (.cv x) A) (.classMem (.cv x) B)))) :=
  by
  let proofSupport : Finset Var :=
    ({ x } : Finset Var) ∪ ({ y } : Finset Var) ∪ A.fv ∪ B.fv
  have p0000 :=
    @g_dfcleq y A B
      (by
        first
        | (aesop))
      (by
        first
        | (aesop))
  have p0001 :=
    Nominal.ax17 (syn_wb (.classMem (.cv x) A) (.classMem (.cv x) B)) y
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
  have p0002 := @g_dfbi2 (.classMem (.cv y) A) (.classMem (.cv y) B)
  have p0003 :=
    @g_hbim (.classMem (.cv y) A) (.classMem (.cv y) B) x hyp_cleqh_1 hyp_cleqh_2
  have p0004 :=
    @g_hbim (.classMem (.cv y) B) (.classMem (.cv y) A) x hyp_cleqh_2 hyp_cleqh_1
  have p0005 :=
    @g_hban (.imp (.classMem (.cv y) A) (.classMem (.cv y) B))
      (.imp (.classMem (.cv y) B) (.classMem (.cv y) A)) x p0003 p0004
  have p0006 :=
    @g_hbxfrbi (syn_wb (.classMem (.cv y) A) (.classMem (.cv y) B))
      (syn_wa (.imp (.classMem (.cv y) A) (.classMem (.cv y) B))
        (.imp (.classMem (.cv y) B) (.classMem (.cv y) A)))
      x p0002 p0005
  have p0007 := @g_eleq1 (.cv x) (.cv y) A
  have p0008 := @g_eleq1 (.cv x) (.cv y) B
  have p0009_e00_recanon :
    Nominal.NPrf
      (.imp (.objEq x y) (syn_wb (.classMem (.cv x) A) (.classMem (.cv y) A))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wb
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
        · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0007
  have p0009_e01_recanon :
    Nominal.NPrf
      (.imp (.objEq x y) (syn_wb (.classMem (.cv x) B) (.classMem (.cv y) B))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wb
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
        · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0008
  have p0009 :=
    @g_bibi12d (.objEq x y) (.classMem (.cv x) A) (.classMem (.cv y) A)
      (.classMem (.cv x) B) (.classMem (.cv y) B) p0009_e00_recanon p0009_e01_recanon
  have p0010 :=
    @g_biimpd (.objEq x y) (syn_wb (.classMem (.cv x) A) (.classMem (.cv x) B))
      (syn_wb (.classMem (.cv y) A) (.classMem (.cv y) B)) p0009
  have p0011 :=
    @g_cbv3h (syn_wb (.classMem (.cv x) A) (.classMem (.cv x) B))
      (syn_wb (.classMem (.cv y) A) (.classMem (.cv y) B)) x y p0001 p0006 p0010
  have p0012 :=
    @g_equcoms
      (syn_wb (syn_wb (.classMem (.cv x) A) (.classMem (.cv x) B))
        (syn_wb (.classMem (.cv y) A) (.classMem (.cv y) B)))
      x y p0009
  have p0013 :=
    @g_biimprd (.objEq y x) (syn_wb (.classMem (.cv x) A) (.classMem (.cv x) B))
      (syn_wb (.classMem (.cv y) A) (.classMem (.cv y) B)) p0012
  have p0014 :=
    @g_cbv3h (syn_wb (.classMem (.cv y) A) (.classMem (.cv y) B))
      (syn_wb (.classMem (.cv x) A) (.classMem (.cv x) B)) y x p0006 p0001 p0013
  have p0015 :=
    @g_impbii (.all x (syn_wb (.classMem (.cv x) A) (.classMem (.cv x) B)))
      (.all y (syn_wb (.classMem (.cv y) A) (.classMem (.cv y) B))) p0011 p0014
  have p0016 :=
    @g_bitr4i (.classEq A B) (.all y (syn_wb (.classMem (.cv y) A) (.classMem (.cv y) B)))
      (.all x (syn_wb (.classMem (.cv x) A) (.classMem (.cv x) B))) p0000 p0015
  exact p0016

@[expose]
noncomputable def g_eqsb1lem (x : Var) (y : Var) (A : Class) (dv_A_x : x ∉ A.fv)
    (dv_x_y : x ≠ y) :
    Nominal.NPrf (syn_wb (syn_wsb y x (.classEq (.cv x) A)) (.classEq (.cv y) A)) :=
  by
  let proofSupport : Finset Var := ({ x } : Finset Var) ∪ ({ y } : Finset Var) ∪ A.fv
  have p0000 :=
    @g_nfv (.classEq (.cv y) A) x
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
  have p0001 := @g_eqeq1 (.cv x) (.cv y) A
  have p0002_e01_recanon :
    Nominal.NPrf (.imp (.objEq x y) (syn_wb (.classEq (.cv x) A) (.classEq (.cv y) A))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wb
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
        · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0001
  have p0002 :=
    @g_sbie (.classEq (.cv x) A) (.classEq (.cv y) A) x y p0000 p0002_e01_recanon
  exact p0002

@[expose]
noncomputable def g_eqsb1 (x : Var) (y : Var) (A : Class) (dv_A_x : x ∉ A.fv) :
    Nominal.NPrf (syn_wb (syn_wsb y x (.classEq (.cv x) A)) (.classEq (.cv y) A)) :=
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
    @g_eqsb1lem x w A
      (by
        first
        | (aesop))
      (by
        first
        | (aesop))
  have p0001 := @g_sbbii (syn_wsb w x (.classEq (.cv x) A)) (.classEq (.cv w) A) w y p0000
  have p0002 :=
    @g_nfv (.classEq (.cv x) A) w
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
  have p0003 := @g_sbco2 (.classEq (.cv x) A) x y w p0002
  have p0004 :=
    @g_eqsb1lem w y A
      (by
        first
        | (aesop))
      (by
        first
        | (aesop))
  have p0005 :=
    @g_n_3bitr3i (syn_wsb y w (syn_wsb w x (.classEq (.cv x) A)))
      (syn_wsb y w (.classEq (.cv w) A)) (syn_wsb y x (.classEq (.cv x) A))
      (.classEq (.cv y) A) p0001 p0003 p0004
  exact p0005

@[expose]
noncomputable def g_clelsb1 (x : Var) (y : Var) (A : Class) (dv_A_x : x ∉ A.fv) :
    Nominal.NPrf (syn_wb (syn_wsb y x (.classMem (.cv x) A)) (.classMem (.cv y) A)) :=
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
    @g_nfv (.classMem (.cv w) A) x
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
  have p0001 := @g_sbco2 (.classMem (.cv w) A) w y x p0000
  have p0002 :=
    @g_nfv (.classMem (.cv x) A) w
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
  have p0003 := @g_eleq1 (.cv w) (.cv x) A
  have p0004_e01_recanon :
    Nominal.NPrf
      (.imp (.objEq w x) (syn_wb (.classMem (.cv w) A) (.classMem (.cv x) A))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wb
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
        · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0003
  have p0004 :=
    @g_sbie (.classMem (.cv w) A) (.classMem (.cv x) A) w x p0002 p0004_e01_recanon
  have p0005 :=
    @g_sbbii (syn_wsb x w (.classMem (.cv w) A)) (.classMem (.cv x) A) x y p0004
  have p0006 :=
    @g_nfv (.classMem (.cv y) A) w
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
  have p0007 := @g_eleq1 (.cv w) (.cv y) A
  have p0008_e01_recanon :
    Nominal.NPrf
      (.imp (.objEq w y) (syn_wb (.classMem (.cv w) A) (.classMem (.cv y) A))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wb
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
        · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0007
  have p0008 :=
    @g_sbie (.classMem (.cv w) A) (.classMem (.cv y) A) w y p0006 p0008_e01_recanon
  have p0009 :=
    @g_n_3bitr3i (syn_wsb y x (syn_wsb x w (.classMem (.cv w) A)))
      (syn_wsb y w (.classMem (.cv w) A)) (syn_wsb y x (.classMem (.cv x) A))
      (.classMem (.cv y) A) p0001 p0005 p0008
  exact p0009

@[expose]
noncomputable def g_hblem (x : Var) (y : Var) (z : Var) (A : Class) (dv_A_y : y ∉ A.fv)
    (dv_x_z : x ≠ z)
    (hyp_hblem_1 : Nominal.NPrf (.imp (.classMem (.cv y) A) (.all x (.classMem (.cv y) A)))) :
    Nominal.NPrf (.imp (.classMem (.cv z) A) (.all x (.classMem (.cv z) A))) :=
  by
  let proofSupport : Finset Var :=
    ({ x } : Finset Var) ∪ ({ y } : Finset Var) ∪ ({ z } : Finset Var) ∪ A.fv
  have p0000 :=
    @g_hbsb (.classMem (.cv y) A) y z x
      (by
        first
        | (aesop))
      hyp_hblem_1
  have p0001 :=
    @g_clelsb1 y z A
      (by
        first
        | (aesop))
  have p0002 := @g_albii (syn_wsb z y (.classMem (.cv y) A)) (.classMem (.cv z) A) x p0001
  have p0003 :=
    @g_n_3imtr3i (syn_wsb z y (.classMem (.cv y) A))
      (.all x (syn_wsb z y (.classMem (.cv y) A))) (.classMem (.cv z) A)
      (.all x (.classMem (.cv z) A)) p0000 p0001 p0002
  exact p0003

@[expose]
noncomputable def g_eqabb (ph : Wff) (x : Var) (A : Class) (dv_A_x : x ∉ A.fv) :
    Nominal.NPrf
      (syn_wb (.classEq A (.cab x ph)) (.all x (syn_wb (.classMem (.cv x) A) ph))) :=
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
    @g_hbab1 ph x y
      (by
        first
        | (aesop))
  have p0002 :=
    @g_cleqh x y A (.cab x ph)
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
  have p0003 := @g_abid ph x
  have p0004 := @g_bibi2i (.classMem (.cv x) (.cab x ph)) ph (.classMem (.cv x) A) p0003
  have p0005 :=
    @g_albii (syn_wb (.classMem (.cv x) A) (.classMem (.cv x) (.cab x ph)))
      (syn_wb (.classMem (.cv x) A) ph) x p0004
  have p0006 :=
    @g_bitri (.classEq A (.cab x ph))
      (.all x (syn_wb (.classMem (.cv x) A) (.classMem (.cv x) (.cab x ph))))
      (.all x (syn_wb (.classMem (.cv x) A) ph)) p0002 p0005
  exact p0006

@[expose]
noncomputable def g_eqabcb (ph : Wff) (x : Var) (A : Class) (dv_A_x : x ∉ A.fv) :
    Nominal.NPrf
      (syn_wb (.classEq (.cab x ph) A) (.all x (syn_wb ph (.classMem (.cv x) A)))) :=
  by
  let proofSupport : Finset Var := ph.fv ∪ ({ x } : Finset Var) ∪ A.fv
  have p0000 :=
    @g_eqabb ph x A
      (by
        first
        | (aesop))
  have p0001 := @g_eqcom (.cab x ph) A
  have p0002 := @g_bicom ph (.classMem (.cv x) A)
  have p0003 :=
    @g_albii (syn_wb ph (.classMem (.cv x) A)) (syn_wb (.classMem (.cv x) A) ph) x p0002
  have p0004 :=
    @g_n_3bitr4i (.classEq A (.cab x ph)) (.all x (syn_wb (.classMem (.cv x) A) ph))
      (.classEq (.cab x ph) A) (.all x (syn_wb ph (.classMem (.cv x) A))) p0000 p0001
      p0003
  exact p0004

@[expose]
noncomputable def g_eqabri (ph : Wff) (x : Var) (A : Class)
    (hyp_eqabri_1 : Nominal.NPrf (.classEq A (.cab x ph))) :
    Nominal.NPrf (syn_wb (.classMem (.cv x) A) ph) :=
  by
  have p0000 := @g_eleq2i A (.cab x ph) (.cv x) hyp_eqabri_1
  have p0001 := @g_abid ph x
  have p0002 :=
    @g_bitri (.classMem (.cv x) A) (.classMem (.cv x) (.cab x ph)) ph p0000 p0001
  exact p0002

@[expose]
noncomputable def g_eqabrd (ph : Wff) (ps : Wff) (x : Var) (A : Class)
    (hyp_eqabrd_1 : Nominal.NPrf (.imp ph (.classEq A (.cab x ps)))) :
    Nominal.NPrf (.imp ph (syn_wb (.classMem (.cv x) A) ps)) :=
  by
  have p0000 := @g_eleq2d ph A (.cab x ps) (.cv x) hyp_eqabrd_1
  have p0001 := @g_abid ps x
  have p0002 :=
    @g_syl6bb ph (.classMem (.cv x) A) (.classMem (.cv x) (.cab x ps)) ps p0000 p0001
  exact p0002

@[expose]
noncomputable def g_abbib (ph : Wff) (ps : Wff) (x : Var) :
    Nominal.NPrf (syn_wb (.classEq (.cab x ph) (.cab x ps)) (.all x (syn_wb ph ps))) :=
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
    @g_dfcleq y (.cab x ph) (.cab x ps)
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
    @g_nfsab1 ph x y
      (by
        first
        | (aesop))
  have p0002 :=
    @g_nfsab1 ps x y
      (by
        first
        | (aesop))
  have p0003 :=
    @g_nfbi (.classMem (.cv y) (.cab x ph)) (.classMem (.cv y) (.cab x ps)) x p0001 p0002
  have p0004 :=
    @g_nfv (syn_wb ph ps) y
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
  have p0006 := @g_sbequ12r ph y x
  have p0007 :=
    @g_syl5bb (.classMem (.cv y) (.cab x ph)) (syn_wsb y x ph) (.objEq y x) ph p0005 p0006
  have p0008 :=
    (NFChoice.DirectNominalPrf.Nominal.DefinitionLeafHandlersCanonical001.dfClabStructural
      y x ps)
  have p0009 := @g_sbequ12r ps y x
  have p0010 :=
    @g_syl5bb (.classMem (.cv y) (.cab x ps)) (syn_wsb y x ps) (.objEq y x) ps p0008 p0009
  have p0011 :=
    @g_bibi12d (.objEq y x) (.classMem (.cv y) (.cab x ph)) ph
      (.classMem (.cv y) (.cab x ps)) ps p0007 p0010
  have p0012 :=
    @g_cbval (syn_wb (.classMem (.cv y) (.cab x ph)) (.classMem (.cv y) (.cab x ps)))
      (syn_wb ph ps) y x p0003 p0004 p0011
  have p0013 :=
    @g_bitri (.classEq (.cab x ph) (.cab x ps))
      (.all y (syn_wb (.classMem (.cv y) (.cab x ph)) (.classMem (.cv y) (.cab x ps))))
      (.all x (syn_wb ph ps)) p0000 p0012
  exact p0013

@[expose]
noncomputable def g_eqabi (ph : Wff) (x : Var) (A : Class) (dv_A_x : x ∉ A.fv)
    (hyp_abbiri_1 : Nominal.NPrf (syn_wb (.classMem (.cv x) A) ph)) :
    Nominal.NPrf (.classEq A (.cab x ph)) :=
  by
  let proofSupport : Finset Var := ph.fv ∪ ({ x } : Finset Var) ∪ A.fv
  have p0000 :=
    @g_eqabb ph x A
      (by
        first
        | (aesop))
  have p0001 :=
    @g_mpgbir (.classEq A (.cab x ph)) (syn_wb (.classMem (.cv x) A) ph) x p0000
      hyp_abbiri_1
  exact p0001

@[expose]
noncomputable def g_abbii (ph : Wff) (ps : Wff) (x : Var)
    (hyp_abbii_1 : Nominal.NPrf (syn_wb ph ps)) :
    Nominal.NPrf (.classEq (.cab x ph) (.cab x ps)) :=
  by
  have p0000 := @g_abbib ph ps x
  have p0001 :=
    @g_mpgbir (.classEq (.cab x ph) (.cab x ps)) (syn_wb ph ps) x p0000 hyp_abbii_1
  exact p0001

@[expose]
noncomputable def g_abbid (ph : Wff) (ps : Wff) (ch : Wff) (x : Var)
    (hyp_abbid_1 : Nominal.NPrf (syn_wnf x ph))
    (hyp_abbid_2 : Nominal.NPrf (.imp ph (syn_wb ps ch))) :
    Nominal.NPrf (.imp ph (.classEq (.cab x ps) (.cab x ch))) :=
  by
  have p0000 := @g_alrimi ph (syn_wb ps ch) x hyp_abbid_1 hyp_abbid_2
  have p0001 := @g_abbib ps ch x
  have p0002 :=
    @g_sylibr ph (.all x (syn_wb ps ch)) (.classEq (.cab x ps) (.cab x ch)) p0000 p0001
  exact p0002

@[expose]
noncomputable def g_abbidv (ph : Wff) (ps : Wff) (ch : Wff) (x : Var)
    (dv_ph_x : x ∉ ph.fv) (hyp_abbidv_1 : Nominal.NPrf (.imp ph (syn_wb ps ch))) :
    Nominal.NPrf (.imp ph (.classEq (.cab x ps) (.cab x ch))) :=
  by
  let proofSupport : Finset Var := ph.fv ∪ ps.fv ∪ ch.fv ∪ ({ x } : Finset Var)
  have p0000 :=
    @g_nfv ph x
      (by
        first
        | (aesop))
  have p0001 := @g_abbid ph ps ch x p0000 hyp_abbidv_1
  exact p0001

@[expose]
noncomputable def g_eqabdv (ph : Wff) (ps : Wff) (x : Var) (A : Class) (dv_A_x : x ∉ A.fv)
    (dv_ph_x : x ∉ ph.fv)
    (hyp_eqabdv_1 : Nominal.NPrf (.imp ph (syn_wb (.classMem (.cv x) A) ps))) :
    Nominal.NPrf (.imp ph (.classEq A (.cab x ps))) :=
  by
  let proofSupport : Finset Var := ph.fv ∪ ps.fv ∪ ({ x } : Finset Var) ∪ A.fv
  have p0000 :=
    @g_alrimiv ph (syn_wb (.classMem (.cv x) A) ps) x
      (by
        first
        | (aesop))
      hyp_eqabdv_1
  have p0001 :=
    @g_eqabb ps x A
      (by
        first
        | (aesop))
  have p0002 :=
    @g_sylibr ph (.all x (syn_wb (.classMem (.cv x) A) ps)) (.classEq A (.cab x ps)) p0000
      p0001
  exact p0002

@[expose]
noncomputable def g_eqabcdv (ph : Wff) (ps : Wff) (x : Var) (A : Class)
    (dv_A_x : x ∉ A.fv) (dv_ph_x : x ∉ ph.fv)
    (hyp_eqabcdv_1 : Nominal.NPrf (.imp ph (syn_wb ps (.classMem (.cv x) A)))) :
    Nominal.NPrf (.imp ph (.classEq (.cab x ps) A)) :=
  by
  let proofSupport : Finset Var := ph.fv ∪ ps.fv ∪ ({ x } : Finset Var) ∪ A.fv
  have p0000 :=
    @g_alrimiv ph (syn_wb ps (.classMem (.cv x) A)) x
      (by
        first
        | (aesop))
      hyp_eqabcdv_1
  have p0001 :=
    @g_eqabcb ps x A
      (by
        first
        | (aesop))
  have p0002 :=
    @g_sylibr ph (.all x (syn_wb ps (.classMem (.cv x) A))) (.classEq (.cab x ps) A) p0000
      p0001
  exact p0002

@[expose]
noncomputable def g_abid2 (x : Var) (A : Class) (dv_A_x : x ∉ A.fv) :
    Nominal.NPrf (.classEq (.cab x (.classMem (.cv x) A)) A) :=
  by
  let proofSupport : Finset Var := ({ x } : Finset Var) ∪ A.fv
  have p0000 := @g_biid (.classMem (.cv x) A)
  have p0001 :=
    @g_eqabi (.classMem (.cv x) A) x A
      (by
        first
        | (aesop))
      p0000
  have p0002 := @g_eqcomi A (.cab x (.classMem (.cv x) A)) p0001
  exact p0002

@[expose]
noncomputable def g_cbvab (ph : Wff) (ps : Wff) (x : Var) (y : Var)
    (hyp_cbvab_1 : Nominal.NPrf (syn_wnf y ph))
    (hyp_cbvab_2 : Nominal.NPrf (syn_wnf x ps))
    (hyp_cbvab_3 : Nominal.NPrf (.imp (.objEq x y) (syn_wb ph ps))) :
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
    @g_nfsb ps y z x
      (by
        first
        | (aesop))
      hyp_cbvab_2
  have p0001 := @g_equcoms (syn_wb ph ps) x y hyp_cbvab_3
  have p0002_e00_recanon :
    Nominal.NPrf (.imp (.classEq (.cv y) (.cv x)) (syn_wb ph ps)) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wb
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · exact Nominal.RecanonTransportDev.TRecanonWff.objEq_classEq _ _
        · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0001
  have p0002 := @g_bicomd (.classEq (.cv y) (.cv x)) ph ps p0002_e00_recanon
  have p0003_e01_recanon : Nominal.NPrf (.imp (.objEq y x) (syn_wb ps ph)) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wb
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
        · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0002
  have p0003 := @g_sbie ps ph y x hyp_cbvab_1 p0003_e01_recanon
  have p0004 := @g_sbequ ps x z y
  have p0005_e01_recanon :
    Nominal.NPrf
      (.imp (.classEq (.cv x) (.cv z)) (syn_wb (syn_wsb x y ps) (syn_wsb z y ps))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wb syn_wsb syn_wa syn_wex
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · exact Nominal.RecanonTransportDev.TRecanonWff.objEq_classEq _ _
        · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0004
  have p0005 :=
    @g_syl5bbr ph (syn_wsb x y ps) (.classEq (.cv x) (.cv z)) (syn_wsb z y ps) p0003
      p0005_e01_recanon
  have p0006_e01_recanon :
    Nominal.NPrf (.imp (.objEq x z) (syn_wb ph (syn_wsb z y ps))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wb syn_wsb syn_wa syn_wex
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
        · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0005
  have p0006 := @g_sbie ph (syn_wsb z y ps) x z p0000 p0006_e01_recanon
  have p0007 :=
    (NFChoice.DirectNominalPrf.Nominal.DefinitionLeafHandlersCanonical001.dfClabStructural
      z x ph)
  have p0008 :=
    (NFChoice.DirectNominalPrf.Nominal.DefinitionLeafHandlersCanonical001.dfClabStructural
      z y ps)
  have p0009 :=
    @g_n_3bitr4i (syn_wsb z x ph) (syn_wsb z y ps) (.classMem (.cv z) (.cab x ph))
      (.classMem (.cv z) (.cab y ps)) p0006 p0007 p0008
  have p0010 :=
    @g_eqriv z (.cab x ph) (.cab y ps)
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

@[expose]
noncomputable def g_nfci (x : Var) (y : Var) (A : Class) (dv_A_y : y ∉ A.fv)
    (dv_x_y : x ≠ y) (hyp_nfci_1 : Nominal.NPrf (syn_wnf x (.classMem (.cv y) A))) :
    Nominal.NPrf (syn_wnfc x A) :=
  by
  let proofSupport : Finset Var := ({ x } : Finset Var) ∪ ({ y } : Finset Var) ∪ A.fv
  have p0000 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominal_df_nfc x y A
      (by
        first
        | (aesop))
      (by
        first
        | (aesop))
  have p0001 :=
    @g_mpgbir (syn_wnfc x A) (syn_wnf x (.classMem (.cv y) A)) y p0000 hyp_nfci_1
  exact p0001

@[expose]
noncomputable def g_nfcr (x : Var) (y : Var) (A : Class) (dv_A_y : y ∉ A.fv)
    (dv_x_y : x ≠ y) :
    Nominal.NPrf (.imp (syn_wnfc x A) (syn_wnf x (.classMem (.cv y) A))) :=
  by
  let proofSupport : Finset Var := ({ x } : Finset Var) ∪ ({ y } : Finset Var) ∪ A.fv
  have p0000 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominal_df_nfc x y A
      (by
        first
        | (aesop))
      (by
        first
        | (aesop))
  have p0001 := @g_sp (syn_wnf x (.classMem (.cv y) A)) y
  have p0002 :=
    @g_sylbi (syn_wnfc x A) (.all y (syn_wnf x (.classMem (.cv y) A)))
      (syn_wnf x (.classMem (.cv y) A)) p0000 p0001
  exact p0002

@[expose]
noncomputable def g_nfcrii (x : Var) (y : Var) (A : Class) (dv_x_y : x ≠ y)
    (hyp_nfcri_1 : Nominal.NPrf (syn_wnfc x A)) :
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
    @g_nfcr x z A
      (by
        first
        | (aesop))
      (by
        first
        | (aesop))
  have p0001 := Nominal.mp hyp_nfcri_1 p0000
  have p0002 := @g_nfri (.classMem (.cv z) A) x p0001
  have p0003 :=
    @g_hblem x z y A
      (by
        first
        | (aesop))
      (by
        first
        | (aesop))
      p0002
  exact p0003

@[expose]
noncomputable def g_nfcri (x : Var) (y : Var) (A : Class) (dv_x_y : x ≠ y)
    (hyp_nfcri_1 : Nominal.NPrf (syn_wnfc x A)) :
    Nominal.NPrf (syn_wnf x (.classMem (.cv y) A)) :=
  by
  let proofSupport : Finset Var := ({ x } : Finset Var) ∪ ({ y } : Finset Var) ∪ A.fv
  have p0000 :=
    @g_nfcrii x y A
      (by
        first
        | (aesop))
      hyp_nfcri_1
  have p0001 := @g_nfi (.classMem (.cv y) A) x p0000
  exact p0001

@[expose]
noncomputable def g_nfcd (ph : Wff) (x : Var) (y : Var) (A : Class) (dv_A_y : y ∉ A.fv)
    (dv_x_y : x ≠ y) (hyp_nfcd_1 : Nominal.NPrf (syn_wnf y ph))
    (hyp_nfcd_2 : Nominal.NPrf (.imp ph (syn_wnf x (.classMem (.cv y) A)))) :
    Nominal.NPrf (.imp ph (syn_wnfc x A)) :=
  by
  let proofSupport : Finset Var :=
    ph.fv ∪ ({ x } : Finset Var) ∪ ({ y } : Finset Var) ∪ A.fv
  have p0000 := @g_alrimi ph (syn_wnf x (.classMem (.cv y) A)) y hyp_nfcd_1 hyp_nfcd_2
  have p0001 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominal_df_nfc x y A
      (by
        first
        | (aesop))
      (by
        first
        | (aesop))
  have p0002 :=
    @g_sylibr ph (.all y (syn_wnf x (.classMem (.cv y) A))) (syn_wnfc x A) p0000 p0001
  exact p0002

@[expose]
noncomputable def g_nfceqi (x : Var) (A : Class) (B : Class)
    (hyp_nfceqi_1 : Nominal.NPrf (.classEq A B)) :
    Nominal.NPrf (syn_wb (syn_wnfc x A) (syn_wnfc x B)) :=
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
  have p0000 := @g_eleq2i A B (.cv y) hyp_nfceqi_1
  have p0001 := @g_nfbii (.classMem (.cv y) A) (.classMem (.cv y) B) x p0000
  have p0002 :=
    @g_albii (syn_wnf x (.classMem (.cv y) A)) (syn_wnf x (.classMem (.cv y) B)) y p0001
  have p0003 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominal_df_nfc x y A
      (by
        first
        | (aesop))
      (by
        first
        | (aesop))
  have p0004 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominal_df_nfc x y B
      (by
        first
        | (aesop))
      (by
        first
        | (aesop))
  have p0005 :=
    @g_n_3bitr4i (.all y (syn_wnf x (.classMem (.cv y) A)))
      (.all y (syn_wnf x (.classMem (.cv y) B))) (syn_wnfc x A) (syn_wnfc x B) p0002 p0003
      p0004
  exact p0005

@[expose]
noncomputable def g_nfcxfr (x : Var) (A : Class) (B : Class)
    (hyp_nfceqi_1 : Nominal.NPrf (.classEq A B))
    (hyp_nfcxfr_2 : Nominal.NPrf (syn_wnfc x B)) : Nominal.NPrf (syn_wnfc x A) :=
  by
  have p0000 := @g_nfceqi x A B hyp_nfceqi_1
  have p0001 := @g_mpbir (syn_wnfc x A) (syn_wnfc x B) hyp_nfcxfr_2 p0000
  exact p0001

@[expose]
noncomputable def g_nfcxfrd (ph : Wff) (x : Var) (A : Class) (B : Class)
    (hyp_nfceqi_1 : Nominal.NPrf (.classEq A B))
    (hyp_nfcxfrd_2 : Nominal.NPrf (.imp ph (syn_wnfc x B))) :
    Nominal.NPrf (.imp ph (syn_wnfc x A)) :=
  by
  have p0000 := @g_nfceqi x A B hyp_nfceqi_1
  have p0001 := @g_sylibr ph (syn_wnfc x B) (syn_wnfc x A) hyp_nfcxfrd_2 p0000
  exact p0001

@[expose]
noncomputable def g_nfceqdf (ph : Wff) (x : Var) (A : Class) (B : Class)
    (hyp_nfceqdf_1 : Nominal.NPrf (syn_wnf x ph))
    (hyp_nfceqdf_2 : Nominal.NPrf (.imp ph (.classEq A B))) :
    Nominal.NPrf (.imp ph (syn_wb (syn_wnfc x A) (syn_wnfc x B))) :=
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
  have p0000 := @g_eleq2d ph A B (.cv y) hyp_nfceqdf_2
  have p0001 :=
    @g_nfbidf ph (.classMem (.cv y) A) (.classMem (.cv y) B) x hyp_nfceqdf_1 p0000
  have p0002 :=
    @g_albidv ph (syn_wnf x (.classMem (.cv y) A)) (syn_wnf x (.classMem (.cv y) B)) y
      (by
        first
        | (aesop))
      p0001
  have p0003 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominal_df_nfc x y A
      (by
        first
        | (aesop))
      (by
        first
        | (aesop))
  have p0004 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominal_df_nfc x y B
      (by
        first
        | (aesop))
      (by
        first
        | (aesop))
  have p0005 :=
    @g_n_3bitr4g ph (.all y (syn_wnf x (.classMem (.cv y) A)))
      (.all y (syn_wnf x (.classMem (.cv y) B))) (syn_wnfc x A) (syn_wnfc x B) p0002 p0003
      p0004
  exact p0005

@[expose]
noncomputable def g_nfcv (x : Var) (A : Class) (dv_A_x : x ∉ A.fv) :
    Nominal.NPrf (syn_wnfc x A) :=
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
    @g_nfv (.classMem (.cv y) A) x
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
    @g_nfci x y A
      (by
        first
        | (aesop))
      (by
        first
        | (aesop))
      p0000
  exact p0001

@[expose]
noncomputable def g_nfcvd (ph : Wff) (x : Var) (A : Class) (dv_A_x : x ∉ A.fv) :
    Nominal.NPrf (.imp ph (syn_wnfc x A)) :=
  by
  let proofSupport : Finset Var := ph.fv ∪ ({ x } : Finset Var) ∪ A.fv
  have p0000 :=
    @g_nfcv x A
      (by
        first
        | (aesop))
  have p0001 := @g_a1i (syn_wnfc x A) ph p0000
  exact p0001

@[expose]
noncomputable def g_nfab1 (ph : Wff) (x : Var) : Nominal.NPrf (syn_wnfc x (.cab x ph)) :=
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
    @g_nfsab1 ph x y
      (by
        first
        | (aesop))
  have p0001 :=
    @g_nfci x y (.cab x ph)
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

@[expose]
noncomputable def g_nfnfc1 (x : Var) (A : Class) :
    Nominal.NPrf (syn_wnf x (syn_wnfc x A)) :=
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
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominal_df_nfc x y A
      (by
        first
        | (aesop))
      (by
        first
        | (aesop))
  have p0001 := @g_nfnf1 (.classMem (.cv y) A) x
  have p0002 := @g_nfal (syn_wnf x (.classMem (.cv y) A)) x y p0001
  have p0003 :=
    @g_nfxfr (syn_wnfc x A) (.all y (syn_wnf x (.classMem (.cv y) A))) x p0000 p0002
  exact p0003

@[expose]
noncomputable def g_nfab (ph : Wff) (x : Var) (y : Var)
    (hyp_nfab_1 : Nominal.NPrf (syn_wnf x ph)) : Nominal.NPrf (syn_wnfc x (.cab y ph)) :=
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
    @g_nfsab ph x y z
      (by
        first
        | (aesop))
      hyp_nfab_1
  have p0001 :=
    @g_nfci x z (.cab y ph)
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

@[expose]
noncomputable def g_nfaba1 (ph : Wff) (x : Var) (y : Var) :
    Nominal.NPrf (syn_wnfc x (.cab y (.all x ph))) :=
  by
  have p0000 := @g_nfa1 ph x
  have p0001 := @g_nfab (.all x ph) x y p0000
  exact p0001

@[expose]
noncomputable def g_nfeq (x : Var) (A : Class) (B : Class)
    (hyp_nfnfc_1 : Nominal.NPrf (syn_wnfc x A))
    (hyp_nfeq_2 : Nominal.NPrf (syn_wnfc x B)) :
    Nominal.NPrf (syn_wnf x (.classEq A B)) :=
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
    @g_dfcleq z A B
      (by
        first
        | (aesop))
      (by
        first
        | (aesop))
  have p0001 :=
    @g_nfcri x z A
      (by
        first
        | (aesop))
      hyp_nfnfc_1
  have p0002 :=
    @g_nfcri x z B
      (by
        first
        | (aesop))
      hyp_nfeq_2
  have p0003 := @g_nfbi (.classMem (.cv z) A) (.classMem (.cv z) B) x p0001 p0002
  have p0004 := @g_nfal (syn_wb (.classMem (.cv z) A) (.classMem (.cv z) B)) x z p0003
  have p0005 :=
    @g_nfxfr (.classEq A B) (.all z (syn_wb (.classMem (.cv z) A) (.classMem (.cv z) B)))
      x p0000 p0004
  exact p0005

@[expose]
noncomputable def g_nfel (x : Var) (A : Class) (B : Class)
    (hyp_nfnfc_1 : Nominal.NPrf (syn_wnfc x A))
    (hyp_nfeq_2 : Nominal.NPrf (syn_wnfc x B)) :
    Nominal.NPrf (syn_wnf x (.classMem A B)) :=
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
    @g_nfcv x (.cv z)
      (by
        first
        |
          (simp (config :=
              {
                failIfUnchanged :=
                  false }) only [NFChoice.Compiler.CoreFVSimp.fv_class_cv,
              Finset.mem_singleton] at ⊢;
            aesop))
  have p0002 := @g_nfeq x (.cv z) A p0001 hyp_nfnfc_1
  have p0003 :=
    @g_nfcri x z B
      (by
        first
        | (aesop))
      hyp_nfeq_2
  have p0004 := @g_nfan (.classEq (.cv z) A) (.classMem (.cv z) B) x p0002 p0003
  have p0005 := @g_nfex (syn_wa (.classEq (.cv z) A) (.classMem (.cv z) B)) x z p0004
  have p0006 :=
    @g_nfxfr (.classMem A B)
      (syn_wex z (syn_wa (.classEq (.cv z) A) (.classMem (.cv z) B))) x p0000 p0005
  exact p0006

@[expose]
noncomputable def g_nfel1 (x : Var) (A : Class) (B : Class) (dv_B_x : x ∉ B.fv)
    (hyp_nfeq1_1 : Nominal.NPrf (syn_wnfc x A)) :
    Nominal.NPrf (syn_wnf x (.classMem A B)) :=
  by
  let proofSupport : Finset Var := ({ x } : Finset Var) ∪ A.fv ∪ B.fv
  have p0000 :=
    @g_nfcv x B
      (by
        first
        | (aesop))
  have p0001 := @g_nfel x A B hyp_nfeq1_1 p0000
  exact p0001

@[expose]
noncomputable def g_nfeq2 (x : Var) (A : Class) (B : Class) (dv_A_x : x ∉ A.fv)
    (hyp_nfeq2_1 : Nominal.NPrf (syn_wnfc x B)) :
    Nominal.NPrf (syn_wnf x (.classEq A B)) :=
  by
  let proofSupport : Finset Var := ({ x } : Finset Var) ∪ A.fv ∪ B.fv
  have p0000 :=
    @g_nfcv x A
      (by
        first
        | (aesop))
  have p0001 := @g_nfeq x A B p0000 hyp_nfeq2_1
  exact p0001

@[expose]
noncomputable def g_nfel2 (x : Var) (A : Class) (B : Class) (dv_A_x : x ∉ A.fv)
    (hyp_nfeq2_1 : Nominal.NPrf (syn_wnfc x B)) :
    Nominal.NPrf (syn_wnf x (.classMem A B)) :=
  by
  let proofSupport : Finset Var := ({ x } : Finset Var) ∪ A.fv ∪ B.fv
  have p0000 :=
    @g_nfcv x A
      (by
        first
        | (aesop))
  have p0001 := @g_nfel x A B p0000 hyp_nfeq2_1
  exact p0001


end NFChoice.DirectNominalPrf.WPPReplay
