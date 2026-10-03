/-
Copyright (c) 2026 Elliot Glazer and NFNotWPP contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elliot Glazer and NFNotWPP contributors
-/

module

public import LeanPool.NFWeakPartition.ReplaySupport.SetOperations1


/-! NF weak partition development: NominalWPPReplayChunk008. -/


public section


namespace NFChoice.DirectNominalPrf.WPPReplay

open scoped Fol
open NFChoice.Foundation
open NFChoice.SemanticCore
open NFChoice.ReplaySupport
open NFChoice.Compiler.CompactSourceSyntax

@[expose]
noncomputable def g_dedth2h (ph : Wff) (ps : Wff) (ch : Wff) (th : Wff) (ta : Wff)
    (A : Class) (B : Class) (C : Class) (D : Class)
    (hyp_dedth2h_1 : Nominal.NPrf (.imp (.classEq A (syn_cif ph A C)) (syn_wb ch th)))
    (hyp_dedth2h_2 : Nominal.NPrf (.imp (.classEq B (syn_cif ps B D)) (syn_wb th ta)))
    (hyp_dedth2h_3 : Nominal.NPrf ta) : Nominal.NPrf (.imp (syn_wa ph ps) ch) :=
  by
  have p0000 := @g_imbi2d (.classEq A (syn_cif ph A C)) ch th ps hyp_dedth2h_1
  have p0001 := @g_dedth ps th ta B D hyp_dedth2h_2 hyp_dedth2h_3
  have p0002 := @g_dedth ph (.imp ps ch) (.imp ps th) A C p0000 p0001
  have p0003 := @g_imp ph ps ch p0002
  exact p0003

@[expose]
noncomputable def g_dedth3h (ph : Wff) (ps : Wff) (ch : Wff) (th : Wff) (ta : Wff)
    (et : Wff) (ze : Wff) (A : Class) (B : Class) (C : Class) (D : Class) (R : Class)
    (S : Class)
    (hyp_dedth3h_1 : Nominal.NPrf (.imp (.classEq A (syn_cif ph A D)) (syn_wb th ta)))
    (hyp_dedth3h_2 : Nominal.NPrf (.imp (.classEq B (syn_cif ps B R)) (syn_wb ta et)))
    (hyp_dedth3h_3 : Nominal.NPrf (.imp (.classEq C (syn_cif ch C S)) (syn_wb et ze)))
    (hyp_dedth3h_4 : Nominal.NPrf ze) : Nominal.NPrf (.imp (syn_w3a ph ps ch) th) :=
  by
  have p0000 := @g_imbi2d (.classEq A (syn_cif ph A D)) th ta (syn_wa ps ch) hyp_dedth3h_1
  have p0001 :=
    @g_dedth2h ps ch ta et ze B C R S hyp_dedth3h_2 hyp_dedth3h_3 hyp_dedth3h_4
  have p0002 :=
    @g_dedth ph (.imp (syn_wa ps ch) th) (.imp (syn_wa ps ch) ta) A D p0000 p0001
  have p0003 := @g_n_3impib ph ps ch th p0002
  exact p0003

@[expose]
noncomputable def g_dedth4h (ph : Wff) (ps : Wff) (ch : Wff) (th : Wff) (ta : Wff)
    (et : Wff) (ze : Wff) (si : Wff) (rh : Wff) (A : Class) (B : Class) (C : Class)
    (D : Class) (R : Class) (S : Class) (F : Class) (G : Class)
    (hyp_dedth4h_1 : Nominal.NPrf (.imp (.classEq A (syn_cif ph A R)) (syn_wb ta et)))
    (hyp_dedth4h_2 : Nominal.NPrf (.imp (.classEq B (syn_cif ps B S)) (syn_wb et ze)))
    (hyp_dedth4h_3 : Nominal.NPrf (.imp (.classEq C (syn_cif ch C F)) (syn_wb ze si)))
    (hyp_dedth4h_4 : Nominal.NPrf (.imp (.classEq D (syn_cif th D G)) (syn_wb si rh)))
    (hyp_dedth4h_5 : Nominal.NPrf rh) :
    Nominal.NPrf (.imp (syn_wa (syn_wa ph ps) (syn_wa ch th)) ta) :=
  by
  have p0000 := @g_imbi2d (.classEq A (syn_cif ph A R)) ta et (syn_wa ch th) hyp_dedth4h_1
  have p0001 := @g_imbi2d (.classEq B (syn_cif ps B S)) et ze (syn_wa ch th) hyp_dedth4h_2
  have p0002 :=
    @g_dedth2h ch th ze si rh C D F G hyp_dedth4h_3 hyp_dedth4h_4 hyp_dedth4h_5
  have p0003 :=
    @g_dedth2h ph ps (.imp (syn_wa ch th) ta) (.imp (syn_wa ch th) et)
      (.imp (syn_wa ch th) ze) A B R S p0000 p0001 p0002
  have p0004 := @g_imp (syn_wa ph ps) (syn_wa ch th) ta p0003
  exact p0004

@[expose]
noncomputable def g_dedth2v (ph : Wff) (ps : Wff) (ch : Wff) (th : Wff) (A : Class)
    (B : Class) (C : Class) (D : Class)
    (hyp_dedth2v_1 : Nominal.NPrf (.imp (.classEq A (syn_cif ph A C)) (syn_wb ps ch)))
    (hyp_dedth2v_2 : Nominal.NPrf (.imp (.classEq B (syn_cif ph B D)) (syn_wb ch th)))
    (hyp_dedth2v_3 : Nominal.NPrf th) : Nominal.NPrf (.imp ph ps) :=
  by
  have p0000 :=
    @g_dedth2h ph ph ps ch th A B C D hyp_dedth2v_1 hyp_dedth2v_2 hyp_dedth2v_3
  have p0001 := @g_anidms ph ps p0000
  exact p0001

@[expose]
noncomputable def g_dedth3v (ph : Wff) (ps : Wff) (ch : Wff) (th : Wff) (ta : Wff)
    (A : Class) (B : Class) (C : Class) (D : Class) (R : Class) (S : Class)
    (hyp_dedth3v_1 : Nominal.NPrf (.imp (.classEq A (syn_cif ph A D)) (syn_wb ps ch)))
    (hyp_dedth3v_2 : Nominal.NPrf (.imp (.classEq B (syn_cif ph B R)) (syn_wb ch th)))
    (hyp_dedth3v_3 : Nominal.NPrf (.imp (.classEq C (syn_cif ph C S)) (syn_wb th ta)))
    (hyp_dedth3v_4 : Nominal.NPrf ta) : Nominal.NPrf (.imp ph ps) :=
  by
  have p0000 :=
    @g_dedth3h ph ph ph ps ch th ta A B C D R S hyp_dedth3v_1 hyp_dedth3v_2 hyp_dedth3v_3
      hyp_dedth3v_4
  have p0001 := @g_n_3anidm12 ph ph ps p0000
  have p0002 := @g_anidms ph ps p0001
  exact p0002

@[expose]
noncomputable def g_dedth4v (ph : Wff) (ps : Wff) (ch : Wff) (th : Wff) (ta : Wff)
    (et : Wff) (A : Class) (B : Class) (C : Class) (D : Class) (R : Class) (S : Class)
    (T : Class) (U : Class)
    (hyp_dedth4v_1 : Nominal.NPrf (.imp (.classEq A (syn_cif ph A R)) (syn_wb ps ch)))
    (hyp_dedth4v_2 : Nominal.NPrf (.imp (.classEq B (syn_cif ph B S)) (syn_wb ch th)))
    (hyp_dedth4v_3 : Nominal.NPrf (.imp (.classEq C (syn_cif ph C T)) (syn_wb th ta)))
    (hyp_dedth4v_4 : Nominal.NPrf (.imp (.classEq D (syn_cif ph D U)) (syn_wb ta et)))
    (hyp_dedth4v_5 : Nominal.NPrf et) : Nominal.NPrf (.imp ph ps) :=
  by
  have p0000 :=
    @g_dedth4h ph ph ph ph ps ch th ta et A B C D R S T U hyp_dedth4v_1 hyp_dedth4v_2
      hyp_dedth4v_3 hyp_dedth4v_4 hyp_dedth4v_5
  have p0001 := @g_anidms (syn_wa ph ph) ps p0000
  have p0002 := @g_anidms ph ps p0001
  exact p0002

@[expose]
noncomputable def g_elimhyp2v (ph : Wff) (ch : Wff) (th : Wff) (ta : Wff) (et : Wff)
    (A : Class) (B : Class) (C : Class) (D : Class)
    (hyp_elimhyp2v_1 : Nominal.NPrf (.imp (.classEq A (syn_cif ph A C)) (syn_wb ph ch)))
    (hyp_elimhyp2v_2 : Nominal.NPrf (.imp (.classEq B (syn_cif ph B D)) (syn_wb ch th)))
    (hyp_elimhyp2v_3 : Nominal.NPrf (.imp (.classEq C (syn_cif ph A C)) (syn_wb ta et)))
    (hyp_elimhyp2v_4 : Nominal.NPrf (.imp (.classEq D (syn_cif ph B D)) (syn_wb et th)))
    (hyp_elimhyp2v_5 : Nominal.NPrf ta) : Nominal.NPrf th :=
  by
  have p0000 := @g_iftrue ph A C
  have p0001 := @g_eqcomd ph (syn_cif ph A C) A p0000
  have p0002 :=
    @g_syl ph (.classEq A (syn_cif ph A C)) (syn_wb ph ch) p0001 hyp_elimhyp2v_1
  have p0003 := @g_iftrue ph B D
  have p0004 := @g_eqcomd ph (syn_cif ph B D) B p0003
  have p0005 :=
    @g_syl ph (.classEq B (syn_cif ph B D)) (syn_wb ch th) p0004 hyp_elimhyp2v_2
  have p0006 := @g_bitrd ph ph ch th p0002 p0005
  have p0007 := @g_ibi ph th p0006
  have p0008 := @g_iffalse ph A C
  have p0009 := @g_eqcomd (.neg ph) (syn_cif ph A C) C p0008
  have p0010 :=
    @g_syl (.neg ph) (.classEq C (syn_cif ph A C)) (syn_wb ta et) p0009 hyp_elimhyp2v_3
  have p0011 := @g_iffalse ph B D
  have p0012 := @g_eqcomd (.neg ph) (syn_cif ph B D) D p0011
  have p0013 :=
    @g_syl (.neg ph) (.classEq D (syn_cif ph B D)) (syn_wb et th) p0012 hyp_elimhyp2v_4
  have p0014 := @g_bitrd (.neg ph) ta et th p0010 p0013
  have p0015 := @g_mpbii (.neg ph) ta th hyp_elimhyp2v_5 p0014
  have p0016 := @g_pm2_61i ph th p0007 p0015
  exact p0016

@[expose]
noncomputable def g_elimhyp3v (ph : Wff) (ch : Wff) (th : Wff) (ta : Wff) (et : Wff)
    (ze : Wff) (si : Wff) (A : Class) (B : Class) (C : Class) (D : Class) (R : Class)
    (S : Class)
    (hyp_elimhyp3v_1 : Nominal.NPrf (.imp (.classEq A (syn_cif ph A D)) (syn_wb ph ch)))
    (hyp_elimhyp3v_2 : Nominal.NPrf (.imp (.classEq B (syn_cif ph B R)) (syn_wb ch th)))
    (hyp_elimhyp3v_3 : Nominal.NPrf (.imp (.classEq C (syn_cif ph C S)) (syn_wb th ta)))
    (hyp_elimhyp3v_4 : Nominal.NPrf (.imp (.classEq D (syn_cif ph A D)) (syn_wb et ze)))
    (hyp_elimhyp3v_5 : Nominal.NPrf (.imp (.classEq R (syn_cif ph B R)) (syn_wb ze si)))
    (hyp_elimhyp3v_6 : Nominal.NPrf (.imp (.classEq S (syn_cif ph C S)) (syn_wb si ta)))
    (hyp_elimhyp3v_7 : Nominal.NPrf et) : Nominal.NPrf ta :=
  by
  have p0000 := @g_iftrue ph A D
  have p0001 := @g_eqcomd ph (syn_cif ph A D) A p0000
  have p0002 :=
    @g_syl ph (.classEq A (syn_cif ph A D)) (syn_wb ph ch) p0001 hyp_elimhyp3v_1
  have p0003 := @g_iftrue ph B R
  have p0004 := @g_eqcomd ph (syn_cif ph B R) B p0003
  have p0005 :=
    @g_syl ph (.classEq B (syn_cif ph B R)) (syn_wb ch th) p0004 hyp_elimhyp3v_2
  have p0006 := @g_iftrue ph C S
  have p0007 := @g_eqcomd ph (syn_cif ph C S) C p0006
  have p0008 :=
    @g_syl ph (.classEq C (syn_cif ph C S)) (syn_wb th ta) p0007 hyp_elimhyp3v_3
  have p0009 := @g_n_3bitrd ph ph ch th ta p0002 p0005 p0008
  have p0010 := @g_ibi ph ta p0009
  have p0011 := @g_iffalse ph A D
  have p0012 := @g_eqcomd (.neg ph) (syn_cif ph A D) D p0011
  have p0013 :=
    @g_syl (.neg ph) (.classEq D (syn_cif ph A D)) (syn_wb et ze) p0012 hyp_elimhyp3v_4
  have p0014 := @g_iffalse ph B R
  have p0015 := @g_eqcomd (.neg ph) (syn_cif ph B R) R p0014
  have p0016 :=
    @g_syl (.neg ph) (.classEq R (syn_cif ph B R)) (syn_wb ze si) p0015 hyp_elimhyp3v_5
  have p0017 := @g_iffalse ph C S
  have p0018 := @g_eqcomd (.neg ph) (syn_cif ph C S) S p0017
  have p0019 :=
    @g_syl (.neg ph) (.classEq S (syn_cif ph C S)) (syn_wb si ta) p0018 hyp_elimhyp3v_6
  have p0020 := @g_n_3bitrd (.neg ph) et ze si ta p0013 p0016 p0019
  have p0021 := @g_mpbii (.neg ph) et ta hyp_elimhyp3v_7 p0020
  have p0022 := @g_pm2_61i ph ta p0010 p0021
  exact p0022

@[expose]
noncomputable def g_elimhyp4v (ph : Wff) (ps : Wff) (ch : Wff) (th : Wff) (ta : Wff)
    (et : Wff) (ze : Wff) (si : Wff) (rh : Wff) (A : Class) (B : Class) (C : Class)
    (D : Class) (R : Class) (S : Class) (F : Class) (G : Class)
    (hyp_elimhyp4v_1 : Nominal.NPrf (.imp (.classEq A (syn_cif ph A D)) (syn_wb ph ch)))
    (hyp_elimhyp4v_2 : Nominal.NPrf (.imp (.classEq B (syn_cif ph B R)) (syn_wb ch th)))
    (hyp_elimhyp4v_3 : Nominal.NPrf (.imp (.classEq C (syn_cif ph C S)) (syn_wb th ta)))
    (hyp_elimhyp4v_4 : Nominal.NPrf (.imp (.classEq F (syn_cif ph F G)) (syn_wb ta ps)))
    (hyp_elimhyp4v_5 : Nominal.NPrf (.imp (.classEq D (syn_cif ph A D)) (syn_wb et ze)))
    (hyp_elimhyp4v_6 : Nominal.NPrf (.imp (.classEq R (syn_cif ph B R)) (syn_wb ze si)))
    (hyp_elimhyp4v_7 : Nominal.NPrf (.imp (.classEq S (syn_cif ph C S)) (syn_wb si rh)))
    (hyp_elimhyp4v_8 : Nominal.NPrf (.imp (.classEq G (syn_cif ph F G)) (syn_wb rh ps)))
    (hyp_elimhyp4v_9 : Nominal.NPrf et) : Nominal.NPrf ps :=
  by
  have p0000 := @g_iftrue ph A D
  have p0001 := @g_eqcomd ph (syn_cif ph A D) A p0000
  have p0002 :=
    @g_syl ph (.classEq A (syn_cif ph A D)) (syn_wb ph ch) p0001 hyp_elimhyp4v_1
  have p0003 := @g_iftrue ph B R
  have p0004 := @g_eqcomd ph (syn_cif ph B R) B p0003
  have p0005 :=
    @g_syl ph (.classEq B (syn_cif ph B R)) (syn_wb ch th) p0004 hyp_elimhyp4v_2
  have p0006 := @g_bitrd ph ph ch th p0002 p0005
  have p0007 := @g_iftrue ph C S
  have p0008 := @g_eqcomd ph (syn_cif ph C S) C p0007
  have p0009 :=
    @g_syl ph (.classEq C (syn_cif ph C S)) (syn_wb th ta) p0008 hyp_elimhyp4v_3
  have p0010 := @g_iftrue ph F G
  have p0011 := @g_eqcomd ph (syn_cif ph F G) F p0010
  have p0012 :=
    @g_syl ph (.classEq F (syn_cif ph F G)) (syn_wb ta ps) p0011 hyp_elimhyp4v_4
  have p0013 := @g_n_3bitrd ph ph th ta ps p0006 p0009 p0012
  have p0014 := @g_ibi ph ps p0013
  have p0015 := @g_iffalse ph A D
  have p0016 := @g_eqcomd (.neg ph) (syn_cif ph A D) D p0015
  have p0017 :=
    @g_syl (.neg ph) (.classEq D (syn_cif ph A D)) (syn_wb et ze) p0016 hyp_elimhyp4v_5
  have p0018 := @g_iffalse ph B R
  have p0019 := @g_eqcomd (.neg ph) (syn_cif ph B R) R p0018
  have p0020 :=
    @g_syl (.neg ph) (.classEq R (syn_cif ph B R)) (syn_wb ze si) p0019 hyp_elimhyp4v_6
  have p0021 := @g_bitrd (.neg ph) et ze si p0017 p0020
  have p0022 := @g_iffalse ph C S
  have p0023 := @g_eqcomd (.neg ph) (syn_cif ph C S) S p0022
  have p0024 :=
    @g_syl (.neg ph) (.classEq S (syn_cif ph C S)) (syn_wb si rh) p0023 hyp_elimhyp4v_7
  have p0025 := @g_iffalse ph F G
  have p0026 := @g_eqcomd (.neg ph) (syn_cif ph F G) G p0025
  have p0027 :=
    @g_syl (.neg ph) (.classEq G (syn_cif ph F G)) (syn_wb rh ps) p0026 hyp_elimhyp4v_8
  have p0028 := @g_n_3bitrd (.neg ph) et si rh ps p0021 p0024 p0027
  have p0029 := @g_mpbii (.neg ph) et ps hyp_elimhyp4v_9 p0028
  have p0030 := @g_pm2_61i ph ps p0014 p0029
  exact p0030

@[expose]
noncomputable def g_keephyp (ph : Wff) (ps : Wff) (ch : Wff) (th : Wff) (A : Class)
    (B : Class)
    (hyp_keephyp_1 : Nominal.NPrf (.imp (.classEq A (syn_cif ph A B)) (syn_wb ps th)))
    (hyp_keephyp_2 : Nominal.NPrf (.imp (.classEq B (syn_cif ph A B)) (syn_wb ch th)))
    (hyp_keephyp_3 : Nominal.NPrf ps) (hyp_keephyp_4 : Nominal.NPrf ch) :
    Nominal.NPrf th :=
  by
  have p0000 := @g_ifboth ph ps ch th A B hyp_keephyp_1 hyp_keephyp_2
  have p0001 := @g_mp2an ps ch th hyp_keephyp_3 hyp_keephyp_4 p0000
  exact p0001

@[expose]
noncomputable def g_keephyp2v (ph : Wff) (ps : Wff) (ch : Wff) (th : Wff) (ta : Wff)
    (et : Wff) (A : Class) (B : Class) (C : Class) (D : Class)
    (hyp_keephyp2v_1 : Nominal.NPrf (.imp (.classEq A (syn_cif ph A C)) (syn_wb ps ch)))
    (hyp_keephyp2v_2 : Nominal.NPrf (.imp (.classEq B (syn_cif ph B D)) (syn_wb ch th)))
    (hyp_keephyp2v_3 : Nominal.NPrf (.imp (.classEq C (syn_cif ph A C)) (syn_wb ta et)))
    (hyp_keephyp2v_4 : Nominal.NPrf (.imp (.classEq D (syn_cif ph B D)) (syn_wb et th)))
    (hyp_keephyp2v_5 : Nominal.NPrf ps) (hyp_keephyp2v_6 : Nominal.NPrf ta) :
    Nominal.NPrf th := by
  have p0000 := @g_iftrue ph A C
  have p0001 := @g_eqcomd ph (syn_cif ph A C) A p0000
  have p0002 :=
    @g_syl ph (.classEq A (syn_cif ph A C)) (syn_wb ps ch) p0001 hyp_keephyp2v_1
  have p0003 := @g_iftrue ph B D
  have p0004 := @g_eqcomd ph (syn_cif ph B D) B p0003
  have p0005 :=
    @g_syl ph (.classEq B (syn_cif ph B D)) (syn_wb ch th) p0004 hyp_keephyp2v_2
  have p0006 := @g_bitrd ph ps ch th p0002 p0005
  have p0007 := @g_mpbii ph ps th hyp_keephyp2v_5 p0006
  have p0008 := @g_iffalse ph A C
  have p0009 := @g_eqcomd (.neg ph) (syn_cif ph A C) C p0008
  have p0010 :=
    @g_syl (.neg ph) (.classEq C (syn_cif ph A C)) (syn_wb ta et) p0009 hyp_keephyp2v_3
  have p0011 := @g_iffalse ph B D
  have p0012 := @g_eqcomd (.neg ph) (syn_cif ph B D) D p0011
  have p0013 :=
    @g_syl (.neg ph) (.classEq D (syn_cif ph B D)) (syn_wb et th) p0012 hyp_keephyp2v_4
  have p0014 := @g_bitrd (.neg ph) ta et th p0010 p0013
  have p0015 := @g_mpbii (.neg ph) ta th hyp_keephyp2v_6 p0014
  have p0016 := @g_pm2_61i ph th p0007 p0015
  exact p0016

@[expose]
noncomputable def g_keepel (ph : Wff) (A : Class) (B : Class) (C : Class)
    (hyp_keepel_1 : Nominal.NPrf (.classMem A C))
    (hyp_keepel_2 : Nominal.NPrf (.classMem B C)) :
    Nominal.NPrf (.classMem (syn_cif ph A B) C) :=
  by
  have p0000 := @g_eleq1 A (syn_cif ph A B) C
  have p0001 := @g_eleq1 B (syn_cif ph A B) C
  have p0002 :=
    @g_keephyp ph (.classMem A C) (.classMem B C) (.classMem (syn_cif ph A B) C) A B p0000
      p0001 hyp_keepel_1 hyp_keepel_2
  exact p0002

@[expose]
noncomputable def g_ifex (ph : Wff) (A : Class) (B : Class)
    (hyp_dedex_1 : Nominal.NPrf (.classMem A (syn_cvv)))
    (hyp_dedex_2 : Nominal.NPrf (.classMem B (syn_cvv))) :
    Nominal.NPrf (.classMem (syn_cif ph A B) (syn_cvv)) :=
  by
  have p0000 := @g_keepel ph A B (syn_cvv) hyp_dedex_1 hyp_dedex_2
  exact p0000

@[expose]
noncomputable def g_pweq (A : Class) (B : Class) :
    Nominal.NPrf (.imp (.classEq A B) (.classEq (syn_cpw A) (syn_cpw B))) :=
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
  have p0000 := @g_sseq2 A B (.cv x)
  have p0001 :=
    @g_abbidv (.classEq A B) (syn_wss (.cv x) A) (syn_wss (.cv x) B) x
      (by
        first
        |
          (simp (config :=
              {
                failIfUnchanged :=
                  false }) only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
              Finset.mem_union] at ⊢;
            aesop))
      p0000
  have p0002 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominal_df_pw x A
      (by
        first
        | (aesop))
  have p0003 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominal_df_pw x B
      (by
        first
        | (aesop))
  have p0004 :=
    @g_n_3eqtr4g (.classEq A B) (.cab x (syn_wss (.cv x) A)) (.cab x (syn_wss (.cv x) B))
      (syn_cpw A) (syn_cpw B) p0001 p0002 p0003
  exact p0004

@[expose]
noncomputable def g_pweqi (A : Class) (B : Class)
    (hyp_pweqi_1 : Nominal.NPrf (.classEq A B)) :
    Nominal.NPrf (.classEq (syn_cpw A) (syn_cpw B)) :=
  by
  have p0000 := @g_pweq A B
  have p0001 := Nominal.mp hyp_pweqi_1 p0000
  exact p0001

@[expose]
noncomputable def g_pweqd (ph : Wff) (A : Class) (B : Class)
    (hyp_pweqd_1 : Nominal.NPrf (.imp ph (.classEq A B))) :
    Nominal.NPrf (.imp ph (.classEq (syn_cpw A) (syn_cpw B))) :=
  by
  have p0000 := @g_pweq A B
  have p0001 :=
    @g_syl ph (.classEq A B) (.classEq (syn_cpw A) (syn_cpw B)) hyp_pweqd_1 p0000
  exact p0001

@[expose]
noncomputable def g_elpw (A : Class) (B : Class)
    (hyp_elpw_1 : Nominal.NPrf (.classMem A (syn_cvv))) :
    Nominal.NPrf (syn_wb (.classMem A (syn_cpw B)) (syn_wss A B)) :=
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
  have p0000 := @g_sseq1 (.cv x) A B
  have p0001 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominal_df_pw x B
      (by
        first
        | (aesop))
  have p0002 :=
    @g_elab2 (syn_wss (.cv x) B) (syn_wss A B) x A (syn_cpw B)
      (by
        first
        | (aesop))
      (by
        first
        |
          (simp (config :=
              {
                failIfUnchanged :=
                  false }) only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wss,
              Finset.mem_union] at ⊢;
            aesop))
      hyp_elpw_1 p0000 p0001
  exact p0002

@[expose]
noncomputable def g_elpwg (A : Class) (B : Class) (V : Class) :
    Nominal.NPrf
      (.imp (.classMem A V) (syn_wb (.classMem A (syn_cpw B)) (syn_wss A B))) :=
  by
  let proofSupport : Finset Var := A.fv ∪ B.fv ∪ V.fv
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
  have fresh_x_not_V : x ∉ V.fv := by
    intro h
    exact fresh_x (Finset.mem_union_right _ (h))
  have p0000 := @g_eleq1 (.cv x) A (syn_cpw B)
  have p0001 := @g_sseq1 (.cv x) A B
  have p0002 := @g_vex x
  have p0003 := @g_elpw (.cv x) B p0002
  have p0004 :=
    @g_vtoclbg (.classMem (.cv x) (syn_cpw B)) (syn_wss (.cv x) B)
      (.classMem A (syn_cpw B)) (syn_wss A B) x A V
      (by
        first
        | (aesop))
      (by
        first
        |
          (simp (config :=
              {
                failIfUnchanged :=
                  false }) only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
              NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw,
              Finset.mem_union] at ⊢;
            aesop))
      (by
        first
        |
          (simp (config :=
              {
                failIfUnchanged :=
                  false }) only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wss,
              Finset.mem_union] at ⊢;
            aesop))
      p0000 p0001 p0003
  exact p0004

@[expose]
noncomputable def g_sneq (A : Class) (B : Class) :
    Nominal.NPrf (.imp (.classEq A B) (.classEq (syn_csn A) (syn_csn B))) :=
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
  have p0000 := @g_eqeq2 A B (.cv x)
  have p0001 :=
    @g_abbidv (.classEq A B) (.classEq (.cv x) A) (.classEq (.cv x) B) x
      (by
        first
        |
          (simp (config :=
              {
                failIfUnchanged :=
                  false }) only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
              Finset.mem_union] at ⊢;
            aesop))
      p0000
  have p0002 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominal_df_sn x A
      (by
        first
        | (aesop))
  have p0003 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominal_df_sn x B
      (by
        first
        | (aesop))
  have p0004 :=
    @g_n_3eqtr4g (.classEq A B) (.cab x (.classEq (.cv x) A))
      (.cab x (.classEq (.cv x) B)) (syn_csn A) (syn_csn B) p0001 p0002 p0003
  exact p0004

@[expose]
noncomputable def g_sneqi (A : Class) (B : Class)
    (hyp_sneqi_1 : Nominal.NPrf (.classEq A B)) :
    Nominal.NPrf (.classEq (syn_csn A) (syn_csn B)) :=
  by
  have p0000 := @g_sneq A B
  have p0001 := Nominal.mp hyp_sneqi_1 p0000
  exact p0001

@[expose]
noncomputable def g_sneqd (ph : Wff) (A : Class) (B : Class)
    (hyp_sneqd_1 : Nominal.NPrf (.imp ph (.classEq A B))) :
    Nominal.NPrf (.imp ph (.classEq (syn_csn A) (syn_csn B))) :=
  by
  have p0000 := @g_sneq A B
  have p0001 :=
    @g_syl ph (.classEq A B) (.classEq (syn_csn A) (syn_csn B)) hyp_sneqd_1 p0000
  exact p0001

@[expose]
noncomputable def g_dfsn2 (A : Class) :
    Nominal.NPrf (.classEq (syn_csn A) (syn_cpr A A)) :=
  by
  have p0000 := (Nominal.classEqRefl (syn_cpr A A))
  have p0001 := @g_unidm (syn_csn A)
  have p0002 :=
    @g_eqtr2i (syn_cpr A A) (syn_cun (syn_csn A) (syn_csn A)) (syn_csn A) p0000 p0001
  exact p0002

@[expose]
noncomputable def g_elsn (x : Var) (A : Class) (dv_A_x : x ∉ A.fv) :
    Nominal.NPrf (syn_wb (.classMem (.cv x) (syn_csn A)) (.classEq (.cv x) A)) :=
  by
  let proofSupport : Finset Var := ({ x } : Finset Var) ∪ A.fv
  have p0000 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominal_df_sn x A
      (by
        first
        | (aesop))
  have p0001 := @g_eqabri (.classEq (.cv x) A) x (syn_csn A) p0000
  exact p0001

@[expose]
noncomputable def g_dfpr2 (x : Var) (A : Class) (B : Class) (dv_A_x : x ∉ A.fv)
    (dv_B_x : x ∉ B.fv) :
    Nominal.NPrf
      (.classEq (syn_cpr A B) (.cab x (syn_wo (.classEq (.cv x) A) (.classEq (.cv x) B)))) :=
  by
  let proofSupport : Finset Var := ({ x } : Finset Var) ∪ A.fv ∪ B.fv
  have p0000 := (Nominal.classEqRefl (syn_cpr A B))
  have p0001 := @g_elun (.cv x) (syn_csn A) (syn_csn B)
  have p0002 :=
    @g_elsn x A
      (by
        first
        | (aesop))
  have p0003 :=
    @g_elsn x B
      (by
        first
        | (aesop))
  have p0004 :=
    @g_orbi12i (.classMem (.cv x) (syn_csn A)) (.classEq (.cv x) A)
      (.classMem (.cv x) (syn_csn B)) (.classEq (.cv x) B) p0002 p0003
  have p0005 :=
    @g_bitri (.classMem (.cv x) (syn_cun (syn_csn A) (syn_csn B)))
      (syn_wo (.classMem (.cv x) (syn_csn A)) (.classMem (.cv x) (syn_csn B)))
      (syn_wo (.classEq (.cv x) A) (.classEq (.cv x) B)) p0001 p0004
  have p0006 :=
    @g_eqabi (syn_wo (.classEq (.cv x) A) (.classEq (.cv x) B)) x
      (syn_cun (syn_csn A) (syn_csn B))
      (by
        first
        |
          (simp (config :=
              {
                failIfUnchanged :=
                  false }) only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cun,
              NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn,
              Finset.mem_union] at ⊢;
            aesop))
      p0005
  have p0007 :=
    @g_eqtri (syn_cpr A B) (syn_cun (syn_csn A) (syn_csn B))
      (.cab x (syn_wo (.classEq (.cv x) A) (.classEq (.cv x) B))) p0000 p0006
  exact p0007

@[expose]
noncomputable def g_elprg (A : Class) (B : Class) (C : Class) (V : Class) :
    Nominal.NPrf
      (.imp (.classMem A V)
        (syn_wb (.classMem A (syn_cpr B C)) (syn_wo (.classEq A B) (.classEq A C)))) :=
  by
  let proofSupport : Finset Var := A.fv ∪ B.fv ∪ C.fv ∪ V.fv
  let x : Var := freshVar proofSupport 0
  have fresh_x : x ∉ proofSupport :=
    by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_x_not_A : x ∉ A.fv := by
    intro h
    exact
      fresh_x
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (h))))
  have fresh_x_not_B : x ∉ B.fv := by
    intro h
    exact
      fresh_x
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))
  have fresh_x_not_C : x ∉ C.fv := by
    intro h
    exact fresh_x (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_x_not_V : x ∉ V.fv := by
    intro h
    exact fresh_x (Finset.mem_union_right _ (h))
  have p0000 := @g_eqeq1 (.cv x) A B
  have p0001 := @g_eqeq1 (.cv x) A C
  have p0002 :=
    @g_orbi12d (.classEq (.cv x) A) (.classEq (.cv x) B) (.classEq A B)
      (.classEq (.cv x) C) (.classEq A C) p0000 p0001
  have p0003 :=
    @g_dfpr2 x B C
      (by
        first
        | (aesop))
      (by
        first
        | (aesop))
  have p0004 :=
    @g_elab2g (syn_wo (.classEq (.cv x) B) (.classEq (.cv x) C))
      (syn_wo (.classEq A B) (.classEq A C)) x A (syn_cpr B C) V
      (by
        first
        | (aesop))
      (by
        first
        |
          (simp (config :=
              {
                failIfUnchanged :=
                  false }) only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wo,
              NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, Finset.mem_union] at ⊢;
            aesop))
      p0002 p0003
  exact p0004

@[expose]
noncomputable def g_elpr (A : Class) (B : Class) (C : Class)
    (hyp_elpr_1 : Nominal.NPrf (.classMem A (syn_cvv))) :
    Nominal.NPrf
      (syn_wb (.classMem A (syn_cpr B C)) (syn_wo (.classEq A B) (.classEq A C))) :=
  by
  have p0000 := @g_elprg A B C (syn_cvv)
  have p0001 := Nominal.mp hyp_elpr_1 p0000
  exact p0001

@[expose]
noncomputable def g_elpr2 (A : Class) (B : Class) (C : Class)
    (hyp_elpr2_1 : Nominal.NPrf (.classMem B (syn_cvv)))
    (hyp_elpr2_2 : Nominal.NPrf (.classMem C (syn_cvv))) :
    Nominal.NPrf
      (syn_wb (.classMem A (syn_cpr B C)) (syn_wo (.classEq A B) (.classEq A C))) :=
  by
  have p0000 := @g_elprg A B C (syn_cpr B C)
  have p0001 :=
    @g_ibi (.classMem A (syn_cpr B C)) (syn_wo (.classEq A B) (.classEq A C)) p0000
  have p0002 := @g_eleq1 A B (syn_cvv)
  have p0003 :=
    @g_mpbiri (.classEq A B) (.classMem A (syn_cvv)) (.classMem B (syn_cvv)) hyp_elpr2_1
      p0002
  have p0004 := @g_eleq1 A C (syn_cvv)
  have p0005 :=
    @g_mpbiri (.classEq A C) (.classMem A (syn_cvv)) (.classMem C (syn_cvv)) hyp_elpr2_2
      p0004
  have p0006 := @g_jaoi (.classEq A B) (.classMem A (syn_cvv)) (.classEq A C) p0003 p0005
  have p0007 := @g_elprg A B C (syn_cvv)
  have p0008 :=
    @g_syl (syn_wo (.classEq A B) (.classEq A C)) (.classMem A (syn_cvv))
      (syn_wb (.classMem A (syn_cpr B C)) (syn_wo (.classEq A B) (.classEq A C))) p0006
      p0007
  have p0009 :=
    @g_ibir (syn_wo (.classEq A B) (.classEq A C)) (.classMem A (syn_cpr B C)) p0008
  have p0010 :=
    @g_impbii (.classMem A (syn_cpr B C)) (syn_wo (.classEq A B) (.classEq A C)) p0001
      p0009
  exact p0010

@[expose]
noncomputable def g_elsncg (A : Class) (B : Class) (V : Class) :
    Nominal.NPrf
      (.imp (.classMem A V) (syn_wb (.classMem A (syn_csn B)) (.classEq A B))) :=
  by
  let proofSupport : Finset Var := A.fv ∪ B.fv ∪ V.fv
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
  have fresh_x_not_V : x ∉ V.fv := by
    intro h
    exact fresh_x (Finset.mem_union_right _ (h))
  have p0000 := @g_eqeq1 (.cv x) A B
  have p0001 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominal_df_sn x B
      (by
        first
        | (aesop))
  have p0002 :=
    @g_elab2g (.classEq (.cv x) B) (.classEq A B) x A (syn_csn B) V
      (by
        first
        | (aesop))
      (by
        first
        |
          (simp (config :=
              {
                failIfUnchanged :=
                  false }) only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
              Finset.mem_union] at ⊢;
            aesop))
      p0000 p0001
  exact p0002

@[expose]
noncomputable def g_elsnc (A : Class) (B : Class)
    (hyp_elsnc_1 : Nominal.NPrf (.classMem A (syn_cvv))) :
    Nominal.NPrf (syn_wb (.classMem A (syn_csn B)) (.classEq A B)) :=
  by
  have p0000 := @g_elsncg A B (syn_cvv)
  have p0001 := Nominal.mp hyp_elsnc_1 p0000
  exact p0001

@[expose]
noncomputable def g_elsni (A : Class) (B : Class) :
    Nominal.NPrf (.imp (.classMem A (syn_csn B)) (.classEq A B)) :=
  by
  have p0000 := @g_elsncg A B (syn_csn B)
  have p0001 := @g_ibi (.classMem A (syn_csn B)) (.classEq A B) p0000
  exact p0001

@[expose]
noncomputable def g_snidg (A : Class) (V : Class) :
    Nominal.NPrf (.imp (.classMem A V) (.classMem A (syn_csn A))) :=
  by
  have p0000 := @g_eqid A
  have p0001 := @g_elsncg A A V
  have p0002 :=
    @g_mpbiri (.classMem A V) (.classMem A (syn_csn A)) (.classEq A A) p0000 p0001
  exact p0002

@[expose]
noncomputable def g_snidb (A : Class) :
    Nominal.NPrf (syn_wb (.classMem A (syn_cvv)) (.classMem A (syn_csn A))) :=
  by
  have p0000 := @g_snidg A (syn_cvv)
  have p0001 := @g_elex A (syn_csn A)
  have p0002 := @g_impbii (.classMem A (syn_cvv)) (.classMem A (syn_csn A)) p0000 p0001
  exact p0002

@[expose]
noncomputable def g_snid (A : Class) (hyp_snid_1 : Nominal.NPrf (.classMem A (syn_cvv))) :
    Nominal.NPrf (.classMem A (syn_csn A)) :=
  by
  have p0000 := @g_snidb A
  have p0001 := @g_mpbi (.classMem A (syn_cvv)) (.classMem A (syn_csn A)) hyp_snid_1 p0000
  exact p0001

@[expose]
noncomputable def g_elsnc2g (A : Class) (B : Class) (V : Class) :
    Nominal.NPrf
      (.imp (.classMem B V) (syn_wb (.classMem A (syn_csn B)) (.classEq A B))) :=
  by
  have p0000 := @g_elsni A B
  have p0001 := @g_snidg B V
  have p0002 := @g_eleq1 A B (syn_csn B)
  have p0003 :=
    @g_syl5ibrcom (.classMem B V) (.classMem A (syn_csn B)) (.classEq A B)
      (.classMem B (syn_csn B)) p0001 p0002
  have p0004 :=
    @g_impbid2 (.classMem B V) (.classMem A (syn_csn B)) (.classEq A B) p0000 p0003
  exact p0004

@[expose]
noncomputable def g_elsnc2 (A : Class) (B : Class)
    (hyp_elsnc2_1 : Nominal.NPrf (.classMem B (syn_cvv))) :
    Nominal.NPrf (syn_wb (.classMem A (syn_csn B)) (.classEq A B)) :=
  by
  have p0000 := @g_elsnc2g A B (syn_cvv)
  have p0001 := Nominal.mp hyp_elsnc2_1 p0000
  exact p0001

@[expose]
noncomputable def g_rexsns (ph : Wff) (x : Var) (A : Class) (V : Class)
    (dv_A_x : x ∉ A.fv) :
    Nominal.NPrf
      (.imp (.classMem A V) (syn_wb (syn_wrex x (syn_csn A) ph) (syn_wsbc A x ph))) :=
  by
  let proofSupport : Finset Var := ph.fv ∪ ({ x } : Finset Var) ∪ A.fv ∪ V.fv
  have p0000 :=
    @g_sbc5 ph x A
      (by
        first
        | (aesop))
  have p0001 :=
    @g_a1i (syn_wb (syn_wsbc A x ph) (syn_wex x (syn_wa (.classEq (.cv x) A) ph)))
      (.classMem A V) p0000
  have p0002 := (Nominal.biimpRefl (syn_wrex x (syn_csn A) ph))
  have p0003 :=
    @g_elsn x A
      (by
        first
        | (aesop))
  have p0004 := @g_anbi1i (.classMem (.cv x) (syn_csn A)) (.classEq (.cv x) A) ph p0003
  have p0005 :=
    @g_exbii (syn_wa (.classMem (.cv x) (syn_csn A)) ph) (syn_wa (.classEq (.cv x) A) ph)
      x p0004
  have p0006 :=
    @g_bitri (syn_wrex x (syn_csn A) ph)
      (syn_wex x (syn_wa (.classMem (.cv x) (syn_csn A)) ph))
      (syn_wex x (syn_wa (.classEq (.cv x) A) ph)) p0002 p0005
  have p0007 :=
    @g_syl6rbbr (.classMem A V) (syn_wsbc A x ph)
      (syn_wex x (syn_wa (.classEq (.cv x) A) ph)) (syn_wrex x (syn_csn A) ph) p0001 p0006
  exact p0007

@[expose]
noncomputable def g_rexsng (ph : Wff) (ps : Wff) (x : Var) (A : Class) (V : Class)
    (dv_A_x : x ∉ A.fv) (dv_ps_x : x ∉ ps.fv)
    (hyp_ralsng_1 : Nominal.NPrf (.imp (.classEq (.cv x) A) (syn_wb ph ps))) :
    Nominal.NPrf (.imp (.classMem A V) (syn_wb (syn_wrex x (syn_csn A) ph) ps)) :=
  by
  let proofSupport : Finset Var := ph.fv ∪ ps.fv ∪ ({ x } : Finset Var) ∪ A.fv ∪ V.fv
  have p0000 :=
    @g_rexsns ph x A V
      (by
        first
        | (aesop))
  have p0001 :=
    @g_sbcieg ph ps x A V
      (by
        first
        | (aesop))
      (by
        first
        | (aesop))
      hyp_ralsng_1
  have p0002 :=
    @g_bitrd (.classMem A V) (syn_wrex x (syn_csn A) ph) (syn_wsbc A x ph) ps p0000 p0001
  exact p0002

@[expose]
noncomputable def g_rexsn (ph : Wff) (ps : Wff) (x : Var) (A : Class) (dv_A_x : x ∉ A.fv)
    (dv_ps_x : x ∉ ps.fv) (hyp_ralsn_1 : Nominal.NPrf (.classMem A (syn_cvv)))
    (hyp_ralsn_2 : Nominal.NPrf (.imp (.classEq (.cv x) A) (syn_wb ph ps))) :
    Nominal.NPrf (syn_wb (syn_wrex x (syn_csn A) ph) ps) :=
  by
  let proofSupport : Finset Var := ph.fv ∪ ps.fv ∪ ({ x } : Finset Var) ∪ A.fv
  have p0000 :=
    @g_rexsng ph ps x A (syn_cvv)
      (by
        first
        | (aesop))
      (by
        first
        | (aesop))
      hyp_ralsn_2
  have p0001 := Nominal.mp hyp_ralsn_1 p0000
  exact p0001

@[expose]
noncomputable def g_disjsn (A : Class) (B : Class) :
    Nominal.NPrf
      (syn_wb (.classEq (syn_cin A (syn_csn B)) (syn_c0)) (.neg (.classMem B A))) :=
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
  have p0000 :=
    @g_disj1 x A (syn_csn B)
      (by
        first
        | (aesop))
      (by
        first
        |
          (simp (config :=
              {
                failIfUnchanged :=
                  false }) only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn] at ⊢;
            aesop))
  have p0001 := @g_con2b (.classMem (.cv x) A) (.classMem (.cv x) (syn_csn B))
  have p0002 :=
    @g_elsn x B
      (by
        first
        | (aesop))
  have p0003 :=
    @g_imbi1i (.classMem (.cv x) (syn_csn B)) (.classEq (.cv x) B)
      (.neg (.classMem (.cv x) A)) p0002
  have p0004 := @g_imnan (.classEq (.cv x) B) (.classMem (.cv x) A)
  have p0005 :=
    @g_n_3bitri (.imp (.classMem (.cv x) A) (.neg (.classMem (.cv x) (syn_csn B))))
      (.imp (.classMem (.cv x) (syn_csn B)) (.neg (.classMem (.cv x) A)))
      (.imp (.classEq (.cv x) B) (.neg (.classMem (.cv x) A)))
      (.neg (syn_wa (.classEq (.cv x) B) (.classMem (.cv x) A))) p0001 p0003 p0004
  have p0006 :=
    @g_albii (.imp (.classMem (.cv x) A) (.neg (.classMem (.cv x) (syn_csn B))))
      (.neg (syn_wa (.classEq (.cv x) B) (.classMem (.cv x) A))) x p0005
  have p0007 := @g_alnex (syn_wa (.classEq (.cv x) B) (.classMem (.cv x) A)) x
  have p0008 :=
    (NFChoice.DirectNominalPrf.Nominal.DefinitionLeafHandlersCanonical001.dfClelOfDV x B A (by
        first
        | (aesop)) (by
        first
        | (aesop)))
  have p0009 :=
    @g_xchbinxr (.all x (.neg (syn_wa (.classEq (.cv x) B) (.classMem (.cv x) A))))
      (syn_wex x (syn_wa (.classEq (.cv x) B) (.classMem (.cv x) A))) (.classMem B A)
      p0007 p0008
  have p0010 :=
    @g_n_3bitri (.classEq (syn_cin A (syn_csn B)) (syn_c0))
      (.all x (.imp (.classMem (.cv x) A) (.neg (.classMem (.cv x) (syn_csn B)))))
      (.all x (.neg (syn_wa (.classEq (.cv x) B) (.classMem (.cv x) A))))
      (.neg (.classMem B A)) p0000 p0006 p0009
  exact p0010

@[expose]
noncomputable def g_snprc (A : Class) :
    Nominal.NPrf
      (syn_wb (.neg (.classMem A (syn_cvv))) (.classEq (syn_csn A) (syn_c0))) :=
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
  have p0000 :=
    @g_elsn x A
      (by
        first
        | (aesop))
  have p0001 := @g_exbii (.classMem (.cv x) (syn_csn A)) (.classEq (.cv x) A) x p0000
  have p0002 :=
    @g_neq0 x (syn_csn A)
      (by
        first
        |
          (simp (config :=
              {
                failIfUnchanged :=
                  false }) only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn] at ⊢;
            aesop))
  have p0003 :=
    @g_isset x A
      (by
        first
        | (aesop))
  have p0004 :=
    @g_n_3bitr4i (syn_wex x (.classMem (.cv x) (syn_csn A)))
      (syn_wex x (.classEq (.cv x) A)) (.neg (.classEq (syn_csn A) (syn_c0)))
      (.classMem A (syn_cvv)) p0001 p0002 p0003
  have p0005 := @g_con1bii (.classEq (syn_csn A) (syn_c0)) (.classMem A (syn_cvv)) p0004
  exact p0005

@[expose]
noncomputable def g_rabsn (x : Var) (A : Class) (B : Class) (dv_A_x : x ∉ A.fv)
    (dv_B_x : x ∉ B.fv) :
    Nominal.NPrf
      (.imp (.classMem B A) (.classEq (syn_crab x A (.classEq (.cv x) B)) (syn_csn B))) :=
  by
  let proofSupport : Finset Var := ({ x } : Finset Var) ∪ A.fv ∪ B.fv
  have p0000 := @g_eleq1 (.cv x) B A
  have p0001 :=
    @g_pm5_32ri (.classEq (.cv x) B) (.classMem (.cv x) A) (.classMem B A) p0000
  have p0002 :=
    @g_baib (syn_wa (.classMem (.cv x) A) (.classEq (.cv x) B)) (.classMem B A)
      (.classEq (.cv x) B) p0001
  have p0003 :=
    @g_abbidv (.classMem B A) (syn_wa (.classMem (.cv x) A) (.classEq (.cv x) B))
      (.classEq (.cv x) B) x
      (by
        first
        |
          (simp (config :=
              {
                failIfUnchanged :=
                  false }) only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
              Finset.mem_union] at ⊢;
            aesop))
      p0002
  have p0004 := (Nominal.classEqRefl (syn_crab x A (.classEq (.cv x) B)))
  have p0005 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominal_df_sn x B
      (by
        first
        | (aesop))
  have p0006 :=
    @g_n_3eqtr4g (.classMem B A)
      (.cab x (syn_wa (.classMem (.cv x) A) (.classEq (.cv x) B)))
      (.cab x (.classEq (.cv x) B)) (syn_crab x A (.classEq (.cv x) B)) (syn_csn B) p0003
      p0004 p0005
  exact p0006

@[expose]
noncomputable def g_prcom (A : Class) (B : Class) :
    Nominal.NPrf (.classEq (syn_cpr A B) (syn_cpr B A)) :=
  by
  have p0000 := @g_uncom (syn_csn A) (syn_csn B)
  have p0001 := (Nominal.classEqRefl (syn_cpr A B))
  have p0002 := (Nominal.classEqRefl (syn_cpr B A))
  have p0003 :=
    @g_n_3eqtr4i (syn_cun (syn_csn A) (syn_csn B)) (syn_cun (syn_csn B) (syn_csn A))
      (syn_cpr A B) (syn_cpr B A) p0000 p0001 p0002
  exact p0003

@[expose]
noncomputable def g_preq1 (A : Class) (B : Class) (C : Class) :
    Nominal.NPrf (.imp (.classEq A B) (.classEq (syn_cpr A C) (syn_cpr B C))) :=
  by
  have p0000 := @g_sneq A B
  have p0001 := @g_uneq1d (.classEq A B) (syn_csn A) (syn_csn B) (syn_csn C) p0000
  have p0002 := (Nominal.classEqRefl (syn_cpr A C))
  have p0003 := (Nominal.classEqRefl (syn_cpr B C))
  have p0004 :=
    @g_n_3eqtr4g (.classEq A B) (syn_cun (syn_csn A) (syn_csn C))
      (syn_cun (syn_csn B) (syn_csn C)) (syn_cpr A C) (syn_cpr B C) p0001 p0002 p0003
  exact p0004

@[expose]
noncomputable def g_preq2 (A : Class) (B : Class) (C : Class) :
    Nominal.NPrf (.imp (.classEq A B) (.classEq (syn_cpr C A) (syn_cpr C B))) :=
  by
  have p0000 := @g_preq1 A B C
  have p0001 := @g_prcom C A
  have p0002 := @g_prcom C B
  have p0003 :=
    @g_n_3eqtr4g (.classEq A B) (syn_cpr A C) (syn_cpr B C) (syn_cpr C A) (syn_cpr C B)
      p0000 p0001 p0002
  exact p0003

@[expose]
noncomputable def g_preq12 (A : Class) (B : Class) (C : Class) (D : Class) :
    Nominal.NPrf
      (.imp (syn_wa (.classEq A C) (.classEq B D)) (.classEq (syn_cpr A B) (syn_cpr C D))) :=
  by
  have p0000 := @g_preq1 A C B
  have p0001 := @g_preq2 B D C
  have p0002 :=
    @g_sylan9eq (.classEq A C) (.classEq B D) (syn_cpr A B) (syn_cpr C B) (syn_cpr C D)
      p0000 p0001
  exact p0002

@[expose]
noncomputable def g_preq2d (ph : Wff) (A : Class) (B : Class) (C : Class)
    (hyp_preq1d_1 : Nominal.NPrf (.imp ph (.classEq A B))) :
    Nominal.NPrf (.imp ph (.classEq (syn_cpr C A) (syn_cpr C B))) :=
  by
  have p0000 := @g_preq2 A B C
  have p0001 :=
    @g_syl ph (.classEq A B) (.classEq (syn_cpr C A) (syn_cpr C B)) hyp_preq1d_1 p0000
  exact p0001

@[expose]
noncomputable def g_preq12d (ph : Wff) (A : Class) (B : Class) (C : Class) (D : Class)
    (hyp_preq1d_1 : Nominal.NPrf (.imp ph (.classEq A B)))
    (hyp_preq12d_2 : Nominal.NPrf (.imp ph (.classEq C D))) :
    Nominal.NPrf (.imp ph (.classEq (syn_cpr A C) (syn_cpr B D))) :=
  by
  have p0000 := @g_preq12 A C B D
  have p0001 :=
    @g_syl2anc ph (.classEq A B) (.classEq C D) (.classEq (syn_cpr A C) (syn_cpr B D))
      hyp_preq1d_1 hyp_preq12d_2 p0000
  exact p0001

@[expose]
noncomputable def g_prid1g (A : Class) (B : Class) (V : Class) :
    Nominal.NPrf (.imp (.classMem A V) (.classMem A (syn_cpr A B))) :=
  by
  have p0000 := @g_eqid A
  have p0001 := @g_orci (.classEq A A) (.classEq A B) p0000
  have p0002 := @g_elprg A A B V
  have p0003 :=
    @g_mpbiri (.classMem A V) (.classMem A (syn_cpr A B))
      (syn_wo (.classEq A A) (.classEq A B)) p0001 p0002
  exact p0003

@[expose]
noncomputable def g_prid1 (A : Class) (B : Class)
    (hyp_prid1_1 : Nominal.NPrf (.classMem A (syn_cvv))) :
    Nominal.NPrf (.classMem A (syn_cpr A B)) :=
  by
  have p0000 := @g_prid1g A B (syn_cvv)
  have p0001 := Nominal.mp hyp_prid1_1 p0000
  exact p0001

@[expose]
noncomputable def g_snnzg (A : Class) (V : Class) :
    Nominal.NPrf (.imp (.classMem A V) (syn_wne (syn_csn A) (syn_c0))) :=
  by
  have p0000 := @g_snidg A V
  have p0001 := @g_ne0i (syn_csn A) A
  have p0002 :=
    @g_syl (.classMem A V) (.classMem A (syn_csn A)) (syn_wne (syn_csn A) (syn_c0)) p0000
      p0001
  exact p0002

@[expose]
noncomputable def g_snnz (A : Class) (hyp_snnz_1 : Nominal.NPrf (.classMem A (syn_cvv))) :
    Nominal.NPrf (syn_wne (syn_csn A) (syn_c0)) :=
  by
  have p0000 := @g_snnzg A (syn_cvv)
  have p0001 := Nominal.mp hyp_snnz_1 p0000
  exact p0001

@[expose]
noncomputable def g_snss (A : Class) (B : Class)
    (hyp_snss_1 : Nominal.NPrf (.classMem A (syn_cvv))) :
    Nominal.NPrf (syn_wb (.classMem A B) (syn_wss (syn_csn A) B)) :=
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
  have p0000 :=
    @g_elsn x A
      (by
        first
        | (aesop))
  have p0001 :=
    @g_imbi1i (.classMem (.cv x) (syn_csn A)) (.classEq (.cv x) A) (.classMem (.cv x) B)
      p0000
  have p0002 :=
    @g_albii (.imp (.classMem (.cv x) (syn_csn A)) (.classMem (.cv x) B))
      (.imp (.classEq (.cv x) A) (.classMem (.cv x) B)) x p0001
  have p0003 :=
    @g_dfss2 x (syn_csn A) B
      (by
        first
        |
          (simp (config :=
              {
                failIfUnchanged :=
                  false }) only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn] at ⊢;
            aesop))
      (by
        first
        | (aesop))
  have p0004 :=
    @g_clel2 x A B
      (by
        first
        | (aesop))
      (by
        first
        | (aesop))
      hyp_snss_1
  have p0005 :=
    @g_n_3bitr4ri (.all x (.imp (.classMem (.cv x) (syn_csn A)) (.classMem (.cv x) B)))
      (.all x (.imp (.classEq (.cv x) A) (.classMem (.cv x) B))) (syn_wss (syn_csn A) B)
      (.classMem A B) p0002 p0003 p0004
  exact p0005

@[expose]
noncomputable def g_eldifsn (A : Class) (B : Class) (C : Class) :
    Nominal.NPrf
      (syn_wb (.classMem A (syn_cdif B (syn_csn C))) (syn_wa (.classMem A B) (syn_wne A C))) :=
  by
  have p0000 := @g_eldif A B (syn_csn C)
  have p0001 := @g_elsncg A C B
  have p0002 := @g_necon3bbid (.classMem A B) (.classMem A (syn_csn C)) A C p0001
  have p0003 :=
    @g_pm5_32i (.classMem A B) (.neg (.classMem A (syn_csn C))) (syn_wne A C) p0002
  have p0004 :=
    @g_bitri (.classMem A (syn_cdif B (syn_csn C)))
      (syn_wa (.classMem A B) (.neg (.classMem A (syn_csn C))))
      (syn_wa (.classMem A B) (syn_wne A C)) p0000 p0003
  exact p0004

@[expose]
noncomputable def g_eldifsni (A : Class) (B : Class) (C : Class) :
    Nominal.NPrf (.imp (.classMem A (syn_cdif B (syn_csn C))) (syn_wne A C)) :=
  by
  have p0000 := @g_eldifsn A B C
  have p0001 :=
    @g_simprbi (.classMem A (syn_cdif B (syn_csn C))) (.classMem A B) (syn_wne A C) p0000
  exact p0001

@[expose]
noncomputable def g_neldifsn (A : Class) (B : Class) :
    Nominal.NPrf (.neg (.classMem A (syn_cdif B (syn_csn A)))) :=
  by
  have p0000 := @g_neirr A
  have p0001 := @g_eldifsni A B A
  have p0002 := @g_mto (.classMem A (syn_cdif B (syn_csn A))) (syn_wne A A) p0000 p0001
  exact p0002

@[expose]
noncomputable def g_snssg (A : Class) (B : Class) (V : Class) :
    Nominal.NPrf
      (.imp (.classMem A V) (syn_wb (.classMem A B) (syn_wss (syn_csn A) B))) :=
  by
  let proofSupport : Finset Var := A.fv ∪ B.fv ∪ V.fv
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
  have fresh_x_not_V : x ∉ V.fv := by
    intro h
    exact fresh_x (Finset.mem_union_right _ (h))
  have p0000 := @g_eleq1 (.cv x) A B
  have p0001 := @g_sneq (.cv x) A
  have p0002 := @g_sseq1d (.classEq (.cv x) A) (syn_csn (.cv x)) (syn_csn A) B p0001
  have p0003 := @g_vex x
  have p0004 := @g_snss (.cv x) B p0003
  have p0005 :=
    @g_vtoclbg (.classMem (.cv x) B) (syn_wss (syn_csn (.cv x)) B) (.classMem A B)
      (syn_wss (syn_csn A) B) x A V
      (by
        first
        | (aesop))
      (by
        first
        |
          (simp (config :=
              {
                failIfUnchanged :=
                  false }) only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
              Finset.mem_union] at ⊢;
            aesop))
      (by
        first
        |
          (simp (config :=
              {
                failIfUnchanged :=
                  false }) only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wss,
              NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn,
              Finset.mem_union] at ⊢;
            aesop))
      p0000 p0002 p0004
  exact p0005

@[expose]
noncomputable def g_difsn (A : Class) (B : Class) :
    Nominal.NPrf (.imp (.neg (.classMem A B)) (.classEq (syn_cdif B (syn_csn A)) B)) :=
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
  have p0000 := @g_eldifsn (.cv x) B A
  have p0001 := @g_simpl (.classMem (.cv x) B) (syn_wne (.cv x) A)
  have p0002 := @g_eleq1 (.cv x) A B
  have p0003 :=
    @g_biimpcd (.classEq (.cv x) A) (.classMem (.cv x) B) (.classMem A B) p0002
  have p0004 := @g_necon3bd (.classMem (.cv x) B) (.classMem A B) (.cv x) A p0003
  have p0005 :=
    @g_com12 (.classMem (.cv x) B) (.neg (.classMem A B)) (syn_wne (.cv x) A) p0004
  have p0006 :=
    @g_ancld (.neg (.classMem A B)) (.classMem (.cv x) B) (syn_wne (.cv x) A) p0005
  have p0007 :=
    @g_impbid2 (.neg (.classMem A B)) (syn_wa (.classMem (.cv x) B) (syn_wne (.cv x) A))
      (.classMem (.cv x) B) p0001 p0006
  have p0008 :=
    @g_syl5bb (.classMem (.cv x) (syn_cdif B (syn_csn A)))
      (syn_wa (.classMem (.cv x) B) (syn_wne (.cv x) A)) (.neg (.classMem A B))
      (.classMem (.cv x) B) p0000 p0007
  have p0009 :=
    @g_eqrdv (.neg (.classMem A B)) x (syn_cdif B (syn_csn A)) B
      (by
        first
        |
          (simp (config :=
              {
                failIfUnchanged :=
                  false }) only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdif,
              NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn,
              Finset.mem_union] at ⊢;
            aesop))
      (by
        first
        | (aesop))
      (by
        first
        |
          (simp (config :=
              { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_wff_neg,
              NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, Finset.mem_union] at ⊢;
            aesop))
      p0008
  exact p0009

@[expose]
noncomputable def g_snssi (A : Class) (B : Class) :
    Nominal.NPrf (.imp (.classMem A B) (syn_wss (syn_csn A) B)) :=
  by
  have p0000 := @g_snssg A B B
  have p0001 := @g_ibi (.classMem A B) (syn_wss (syn_csn A) B) p0000
  exact p0001

@[expose]
noncomputable def g_snssd (ph : Wff) (A : Class) (B : Class)
    (hyp_snssd_1 : Nominal.NPrf (.imp ph (.classMem A B))) :
    Nominal.NPrf (.imp ph (syn_wss (syn_csn A) B)) :=
  by
  have p0000 := @g_snssg A B B
  have p0001 :=
    @g_syl ph (.classMem A B) (syn_wb (.classMem A B) (syn_wss (syn_csn A) B)) hyp_snssd_1
      p0000
  have p0002 := @g_mpbid ph (.classMem A B) (syn_wss (syn_csn A) B) hyp_snssd_1 p0001
  exact p0002

@[expose]
noncomputable def g_difsnid (A : Class) (B : Class) :
    Nominal.NPrf
      (.imp (.classMem B A) (.classEq (syn_cun (syn_cdif A (syn_csn B)) (syn_csn B)) A)) :=
  by
  have p0000 := @g_uncom (syn_cdif A (syn_csn B)) (syn_csn B)
  have p0001 := @g_snssi B A
  have p0002 := @g_undif (syn_csn B) A
  have p0003 :=
    @g_sylib (.classMem B A) (syn_wss (syn_csn B) A)
      (.classEq (syn_cun (syn_csn B) (syn_cdif A (syn_csn B))) A) p0001 p0002
  have p0004 :=
    @g_syl5eq (.classMem B A) (syn_cun (syn_cdif A (syn_csn B)) (syn_csn B))
      (syn_cun (syn_csn B) (syn_cdif A (syn_csn B))) A p0000 p0003
  exact p0004

@[expose]
noncomputable def g_sssn (A : Class) (B : Class) :
    Nominal.NPrf
      (syn_wb (syn_wss A (syn_csn B))
        (syn_wo (.classEq A (syn_c0)) (.classEq A (syn_csn B)))) :=
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
  have p0000 :=
    @g_neq0 x A
      (by
        first
        | (aesop))
  have p0001 := @g_ssel A (syn_csn B) (.cv x)
  have p0002 := @g_elsni (.cv x) B
  have p0003 :=
    @g_syl6 (syn_wss A (syn_csn B)) (.classMem (.cv x) A) (.classMem (.cv x) (syn_csn B))
      (.classEq (.cv x) B) p0001 p0002
  have p0004 := @g_eleq1 (.cv x) B A
  have p0005 :=
    @g_syl6 (syn_wss A (syn_csn B)) (.classMem (.cv x) A) (.classEq (.cv x) B)
      (syn_wb (.classMem (.cv x) A) (.classMem B A)) p0003 p0004
  have p0006 := @g_ibd (syn_wss A (syn_csn B)) (.classMem (.cv x) A) (.classMem B A) p0005
  have p0007 :=
    @g_exlimdv (syn_wss A (syn_csn B)) (.classMem (.cv x) A) (.classMem B A) x
      (by
        first
        |
          (simp (config :=
              {
                failIfUnchanged :=
                  false }) only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
              Finset.mem_union] at ⊢;
            aesop))
      (by
        first
        |
          (simp (config :=
              {
                failIfUnchanged :=
                  false }) only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wss,
              NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn,
              Finset.mem_union] at ⊢;
            aesop))
      p0006
  have p0008 :=
    @g_syl5bi (.neg (.classEq A (syn_c0))) (syn_wex x (.classMem (.cv x) A))
      (syn_wss A (syn_csn B)) (.classMem B A) p0000 p0007
  have p0009 := @g_snssi B A
  have p0010 :=
    @g_syl6 (syn_wss A (syn_csn B)) (.neg (.classEq A (syn_c0))) (.classMem B A)
      (syn_wss (syn_csn B) A) p0008 p0009
  have p0011 :=
    @g_anc2li (syn_wss A (syn_csn B)) (.neg (.classEq A (syn_c0))) (syn_wss (syn_csn B) A)
      p0010
  have p0012 := @g_eqss A (syn_csn B)
  have p0013 :=
    @g_syl6ibr (syn_wss A (syn_csn B)) (.neg (.classEq A (syn_c0)))
      (syn_wa (syn_wss A (syn_csn B)) (syn_wss (syn_csn B) A)) (.classEq A (syn_csn B))
      p0011 p0012
  have p0014 :=
    @g_orrd (syn_wss A (syn_csn B)) (.classEq A (syn_c0)) (.classEq A (syn_csn B)) p0013
  have p0015 := @g_n_0ss (syn_csn B)
  have p0016 := @g_sseq1 A (syn_c0) (syn_csn B)
  have p0017 :=
    @g_mpbiri (.classEq A (syn_c0)) (syn_wss A (syn_csn B)) (syn_wss (syn_c0) (syn_csn B))
      p0015 p0016
  have p0018 := @g_eqimss A (syn_csn B)
  have p0019 :=
    @g_jaoi (.classEq A (syn_c0)) (syn_wss A (syn_csn B)) (.classEq A (syn_csn B)) p0017
      p0018
  have p0020 :=
    @g_impbii (syn_wss A (syn_csn B))
      (syn_wo (.classEq A (syn_c0)) (.classEq A (syn_csn B))) p0014 p0019
  exact p0020

@[expose]
noncomputable def g_sneqr (A : Class) (B : Class)
    (hyp_sneqr_1 : Nominal.NPrf (.classMem A (syn_cvv))) :
    Nominal.NPrf (.imp (.classEq (syn_csn A) (syn_csn B)) (.classEq A B)) :=
  by
  have p0000 := @g_snid A hyp_sneqr_1
  have p0001 := @g_eleq2 (syn_csn A) (syn_csn B) A
  have p0002 :=
    @g_mpbii (.classEq (syn_csn A) (syn_csn B)) (.classMem A (syn_csn A))
      (.classMem A (syn_csn B)) p0000 p0001
  have p0003 := @g_elsnc A B hyp_sneqr_1
  have p0004 :=
    @g_sylib (.classEq (syn_csn A) (syn_csn B)) (.classMem A (syn_csn B)) (.classEq A B)
      p0002 p0003
  exact p0004

@[expose]
noncomputable def g_sneqrg (A : Class) (B : Class) (V : Class) :
    Nominal.NPrf
      (.imp (.classMem A V) (.imp (.classEq (syn_csn A) (syn_csn B)) (.classEq A B))) :=
  by
  let proofSupport : Finset Var := A.fv ∪ B.fv ∪ V.fv
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
  have fresh_x_not_V : x ∉ V.fv := by
    intro h
    exact fresh_x (Finset.mem_union_right _ (h))
  have p0000 := @g_sneq (.cv x) A
  have p0001 :=
    @g_eqeq1d (.classEq (.cv x) A) (syn_csn (.cv x)) (syn_csn A) (syn_csn B) p0000
  have p0002 := @g_eqeq1 (.cv x) A B
  have p0003 :=
    @g_imbi12d (.classEq (.cv x) A) (.classEq (syn_csn (.cv x)) (syn_csn B))
      (.classEq (syn_csn A) (syn_csn B)) (.classEq (.cv x) B) (.classEq A B) p0001 p0002
  have p0004 := @g_vex x
  have p0005 := @g_sneqr (.cv x) B p0004
  have p0006 :=
    @g_vtoclg (.imp (.classEq (syn_csn (.cv x)) (syn_csn B)) (.classEq (.cv x) B))
      (.imp (.classEq (syn_csn A) (syn_csn B)) (.classEq A B)) x A V
      (by
        first
        | (aesop))
      (by
        first
        |
          (simp (config :=
              { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp,
              NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
              NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn,
              Finset.mem_union] at ⊢;
            aesop))
      p0003 p0005
  exact p0006

@[expose]
noncomputable def g_sneqbg (A : Class) (B : Class) (V : Class) :
    Nominal.NPrf
      (.imp (.classMem A V) (syn_wb (.classEq (syn_csn A) (syn_csn B)) (.classEq A B))) :=
  by
  have p0000 := @g_sneqrg A B V
  have p0001 := @g_sneq A B
  have p0002 :=
    @g_impbid1 (.classMem A V) (.classEq (syn_csn A) (syn_csn B)) (.classEq A B) p0000
      p0001
  exact p0002

@[expose]
noncomputable def g_sneqb (A : Class) (B : Class)
    (hyp_sneqb_1 : Nominal.NPrf (.classMem A (syn_cvv))) :
    Nominal.NPrf (syn_wb (.classEq (syn_csn A) (syn_csn B)) (.classEq A B)) :=
  by
  have p0000 := @g_sneqbg A B (syn_cvv)
  have p0001 := Nominal.mp hyp_sneqb_1 p0000
  exact p0001

@[expose]
noncomputable def g_pwv : Nominal.NPrf (.classEq (syn_cpw (syn_cvv)) (syn_cvv)) :=
  by
  let proofSupport : Finset Var := (∅ : Finset Var)
  let x : Var := freshVar proofSupport 0
  have fresh_x : x ∉ proofSupport :=
    by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have p0000 := @g_ssv (.cv x)
  have p0001 := @g_vex x
  have p0002 := @g_elpw (.cv x) (syn_cvv) p0001
  have p0003 :=
    @g_mpbir (.classMem (.cv x) (syn_cpw (syn_cvv))) (syn_wss (.cv x) (syn_cvv)) p0000
      p0002
  have p0004 :=
    @g_n_2th (.classMem (.cv x) (syn_cpw (syn_cvv))) (.classMem (.cv x) (syn_cvv)) p0003
      p0001
  have p0005 :=
    @g_eqriv x (syn_cpw (syn_cvv)) (syn_cvv)
      (by
        first
        |
          (simp (config :=
              {
                failIfUnchanged :=
                  false }) only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw,
              NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv] at ⊢;
            aesop))
      (by
        first
        |
          (simp (config :=
              {
                failIfUnchanged :=
                  false }) only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv] at ⊢;
            aesop))
      p0004
  exact p0005

@[expose]
noncomputable def g_unsneqsn (A : Class) (B : Class) (C : Class)
    (hyp_unsneqsn_1 : Nominal.NPrf (.classMem B (syn_cvv))) :
    Nominal.NPrf
      (.imp (.classEq (syn_cun A (syn_csn B)) (syn_csn C))
        (syn_wo (.classEq A (syn_c0)) (.classEq A (syn_csn B)))) :=
  by
  have p0000 := @g_ssun2 (syn_csn B) A
  have p0001 := @g_snid B hyp_unsneqsn_1
  have p0002 := @g_sselii (syn_csn B) (syn_cun A (syn_csn B)) B p0000 p0001
  have p0003 := @g_eleq2 (syn_cun A (syn_csn B)) (syn_csn C) B
  have p0004 :=
    @g_mpbii (.classEq (syn_cun A (syn_csn B)) (syn_csn C))
      (.classMem B (syn_cun A (syn_csn B))) (.classMem B (syn_csn C)) p0002 p0003
  have p0005 := @g_elsni B C
  have p0006 :=
    @g_syl (.classEq (syn_cun A (syn_csn B)) (syn_csn C)) (.classMem B (syn_csn C))
      (.classEq B C) p0004 p0005
  have p0007 := @g_sneq B C
  have p0008 :=
    @g_eqeq2d (.classEq B C) (syn_csn B) (syn_csn C) (syn_cun A (syn_csn B)) p0007
  have p0009 :=
    @g_biimprd (.classEq B C) (.classEq (syn_cun A (syn_csn B)) (syn_csn B))
      (.classEq (syn_cun A (syn_csn B)) (syn_csn C)) p0008
  have p0010 :=
    @g_mpcom (.classEq B C) (.classEq (syn_cun A (syn_csn B)) (syn_csn C))
      (.classEq (syn_cun A (syn_csn B)) (syn_csn B)) p0006 p0009
  have p0011 := @g_ssequn1 A (syn_csn B)
  have p0012 :=
    @g_sylibr (.classEq (syn_cun A (syn_csn B)) (syn_csn C))
      (.classEq (syn_cun A (syn_csn B)) (syn_csn B)) (syn_wss A (syn_csn B)) p0010 p0011
  have p0013 := @g_sssn A B
  have p0014 :=
    @g_sylib (.classEq (syn_cun A (syn_csn B)) (syn_csn C)) (syn_wss A (syn_csn B))
      (syn_wo (.classEq A (syn_c0)) (.classEq A (syn_csn B))) p0012 p0013
  exact p0014

@[expose]
noncomputable def g_dfpss4 (x : Var) (A : Class) (B : Class) (dv_A_x : x ∉ A.fv)
    (dv_B_x : x ∉ B.fv) :
    Nominal.NPrf
      (syn_wb (syn_wpss A B)
        (syn_wa (syn_wss A B) (syn_wrex x B (.neg (.classMem (.cv x) A))))) :=
  by
  let proofSupport : Finset Var := ({ x } : Finset Var) ∪ A.fv ∪ B.fv
  have p0000 := @g_dfpss3 A B
  have p0001 :=
    @g_dfss3 x B A
      (by
        first
        | (aesop))
      (by
        first
        | (aesop))
  have p0002 := @g_dfral2 (.classMem (.cv x) A) x B
  have p0003 :=
    @g_bitr2i (syn_wss B A) (syn_wral x B (.classMem (.cv x) A))
      (.neg (syn_wrex x B (.neg (.classMem (.cv x) A)))) p0001 p0002
  have p0004 := @g_con1bii (syn_wrex x B (.neg (.classMem (.cv x) A))) (syn_wss B A) p0003
  have p0005 :=
    @g_anbi2i (.neg (syn_wss B A)) (syn_wrex x B (.neg (.classMem (.cv x) A)))
      (syn_wss A B) p0004
  have p0006 :=
    @g_bitri (syn_wpss A B) (syn_wa (syn_wss A B) (.neg (syn_wss B A)))
      (syn_wa (syn_wss A B) (syn_wrex x B (.neg (.classMem (.cv x) A)))) p0000 p0005
  exact p0006

@[expose]
noncomputable def g_adj11 (A : Class) (B : Class) (C : Class) :
    Nominal.NPrf
      (.imp (syn_wa (.neg (.classMem C A)) (.neg (.classMem C B)))
        (syn_wb (.classEq (syn_cun A (syn_csn C)) (syn_cun B (syn_csn C))) (.classEq A B))) :=
  by
  have p0000 := @g_difeq1 (syn_cun A (syn_csn C)) (syn_cun B (syn_csn C)) (syn_csn C)
  have p0001 := @g_difun2 A (syn_csn C)
  have p0002 := @g_difun2 B (syn_csn C)
  have p0003 :=
    @g_n_3eqtr3g (.classEq (syn_cun A (syn_csn C)) (syn_cun B (syn_csn C)))
      (syn_cdif (syn_cun A (syn_csn C)) (syn_csn C))
      (syn_cdif (syn_cun B (syn_csn C)) (syn_csn C)) (syn_cdif A (syn_csn C))
      (syn_cdif B (syn_csn C)) p0000 p0001 p0002
  have p0004 := @g_difsn C A
  have p0005 := @g_difsn C B
  have p0006 :=
    @g_eqeqan12d (.neg (.classMem C A)) (.neg (.classMem C B)) (syn_cdif A (syn_csn C)) A
      (syn_cdif B (syn_csn C)) B p0004 p0005
  have p0007 :=
    @g_syl5ib (.classEq (syn_cun A (syn_csn C)) (syn_cun B (syn_csn C)))
      (.classEq (syn_cdif A (syn_csn C)) (syn_cdif B (syn_csn C)))
      (syn_wa (.neg (.classMem C A)) (.neg (.classMem C B))) (.classEq A B) p0003 p0006
  have p0008 := @g_uneq1 A B (syn_csn C)
  have p0009 :=
    @g_impbid1 (syn_wa (.neg (.classMem C A)) (.neg (.classMem C B)))
      (.classEq (syn_cun A (syn_csn C)) (syn_cun B (syn_csn C))) (.classEq A B) p0007
      p0008
  exact p0009

@[expose]
noncomputable def g_dfuni2 (x : Var) (y : Var) (A : Class) (dv_A_x : x ∉ A.fv)
    (dv_A_y : y ∉ A.fv) (dv_x_y : x ≠ y) :
    Nominal.NPrf
      (.classEq (syn_cuni A) (.cab x (syn_wrex y A (.classMem (.cv x) (.cv y))))) :=
  by
  let proofSupport : Finset Var := ({ x } : Finset Var) ∪ ({ y } : Finset Var) ∪ A.fv
  have p0000 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominal_df_uni x y A
      (by
        first
        | (aesop))
      (by
        first
        | (aesop))
      (by
        first
        | (aesop))
  have p0001 := @g_exancom (.classMem (.cv x) (.cv y)) (.classMem (.cv y) A) y
  have p0002 := (Nominal.biimpRefl (syn_wrex y A (.classMem (.cv x) (.cv y))))
  have p0003 :=
    @g_bitr4i (syn_wex y (syn_wa (.classMem (.cv x) (.cv y)) (.classMem (.cv y) A)))
      (syn_wex y (syn_wa (.classMem (.cv y) A) (.classMem (.cv x) (.cv y))))
      (syn_wrex y A (.classMem (.cv x) (.cv y))) p0001 p0002
  have p0004 :=
    @g_abbii (syn_wex y (syn_wa (.classMem (.cv x) (.cv y)) (.classMem (.cv y) A)))
      (syn_wrex y A (.classMem (.cv x) (.cv y))) x p0003
  have p0005_e00_recanon :
    Nominal.NPrf
      (.classEq (syn_cuni A) (.cab x
          (syn_wex y (syn_wa (.classMem (.cv x) (.cv y)) (.classMem (.cv y) A))))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_cuni syn_wex syn_wa
        simp (config := { failIfUnchanged := false }) only []
        apply Nominal.RecanonTransportDev.TRecanonWff.classEq
        · exact Nominal.RecanonTransportDev.TRecanonClass.same _
        · apply Nominal.RecanonTransportDev.TRecanonClass.cab
          apply Nominal.RecanonTransportDev.TRecanonWff.neg
          apply Nominal.RecanonTransportDev.TRecanonWff.all
          apply Nominal.RecanonTransportDev.TRecanonWff.neg
          apply Nominal.RecanonTransportDev.TRecanonWff.neg
          apply Nominal.RecanonTransportDev.TRecanonWff.imp
          · exact Nominal.RecanonTransportDev.TRecanonWff.objMem_classMem _ _
          · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0000
  have p0005 :=
    @g_eqtri (syn_cuni A)
      (.cab x (syn_wex y (syn_wa (.classMem (.cv x) (.cv y)) (.classMem (.cv y) A))))
      (.cab x (syn_wrex y A (.classMem (.cv x) (.cv y)))) p0005_e00_recanon p0004
  exact p0005

@[expose]
noncomputable def g_eluni (x : Var) (A : Class) (B : Class) (dv_A_x : x ∉ A.fv)
    (dv_B_x : x ∉ B.fv) :
    Nominal.NPrf
      (syn_wb (.classMem A (syn_cuni B))
        (syn_wex x (syn_wa (.classMem A (.cv x)) (.classMem (.cv x) B)))) :=
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
  have p0000 := @g_elex A (syn_cuni B)
  have p0001 := @g_elex A (.cv x)
  have p0002 :=
    @g_adantr (.classMem A (.cv x)) (.classMem A (syn_cvv)) (.classMem (.cv x) B) p0001
  have p0003 :=
    @g_exlimiv (syn_wa (.classMem A (.cv x)) (.classMem (.cv x) B))
      (.classMem A (syn_cvv)) x
      (by
        first
        |
          (simp (config :=
              {
                failIfUnchanged :=
                  false }) only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
              NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv,
              Finset.mem_union] at ⊢;
            aesop))
      p0002
  have p0004 := @g_eleq1 (.cv y) A (.cv x)
  have p0005 :=
    @g_anbi1d (.classEq (.cv y) A) (.classMem (.cv y) (.cv x)) (.classMem A (.cv x))
      (.classMem (.cv x) B) p0004
  have p0006 :=
    @g_exbidv (.classEq (.cv y) A)
      (syn_wa (.classMem (.cv y) (.cv x)) (.classMem (.cv x) B))
      (syn_wa (.classMem A (.cv x)) (.classMem (.cv x) B)) x
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
  have p0007 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominal_df_uni y x B
      (by
        first
        | (aesop))
      (by
        first
        | (aesop))
      (by
        first
        | (aesop))
  have p0008_e01_recanon :
    Nominal.NPrf
      (.classEq (syn_cuni B) (.cab y
          (syn_wex x (syn_wa (.classMem (.cv y) (.cv x)) (.classMem (.cv x) B))))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_cuni syn_wex syn_wa
        simp (config := { failIfUnchanged := false }) only []
        apply Nominal.RecanonTransportDev.TRecanonWff.classEq
        · exact Nominal.RecanonTransportDev.TRecanonClass.same _
        · apply Nominal.RecanonTransportDev.TRecanonClass.cab
          apply Nominal.RecanonTransportDev.TRecanonWff.neg
          apply Nominal.RecanonTransportDev.TRecanonWff.all
          apply Nominal.RecanonTransportDev.TRecanonWff.neg
          apply Nominal.RecanonTransportDev.TRecanonWff.neg
          apply Nominal.RecanonTransportDev.TRecanonWff.imp
          · exact Nominal.RecanonTransportDev.TRecanonWff.objMem_classMem _ _
          · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0007
  have p0008 :=
    @g_elab2g (syn_wex x (syn_wa (.classMem (.cv y) (.cv x)) (.classMem (.cv x) B)))
      (syn_wex x (syn_wa (.classMem A (.cv x)) (.classMem (.cv x) B))) y A (syn_cuni B)
      (syn_cvv)
      (by
        first
        | (aesop))
      (by
        first
        |
          (simp (config :=
              {
                failIfUnchanged :=
                  false }) only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wex,
              NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
              NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
              NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
              Finset.mem_erase, Finset.mem_singleton] at ⊢;
            aesop))
      p0006 p0008_e01_recanon
  have p0009 :=
    @g_pm5_21nii (.classMem A (syn_cuni B)) (.classMem A (syn_cvv))
      (syn_wex x (syn_wa (.classMem A (.cv x)) (.classMem (.cv x) B))) p0000 p0003 p0008
  exact p0009

@[expose]
noncomputable def g_eluni2 (x : Var) (A : Class) (B : Class) (dv_A_x : x ∉ A.fv)
    (dv_B_x : x ∉ B.fv) :
    Nominal.NPrf
      (syn_wb (.classMem A (syn_cuni B)) (syn_wrex x B (.classMem A (.cv x)))) :=
  by
  let proofSupport : Finset Var := ({ x } : Finset Var) ∪ A.fv ∪ B.fv
  have p0000 := @g_exancom (.classMem A (.cv x)) (.classMem (.cv x) B) x
  have p0001 :=
    @g_eluni x A B
      (by
        first
        | (aesop))
      (by
        first
        | (aesop))
  have p0002 := (Nominal.biimpRefl (syn_wrex x B (.classMem A (.cv x))))
  have p0003 :=
    @g_n_3bitr4i (syn_wex x (syn_wa (.classMem A (.cv x)) (.classMem (.cv x) B)))
      (syn_wex x (syn_wa (.classMem (.cv x) B) (.classMem A (.cv x))))
      (.classMem A (syn_cuni B)) (syn_wrex x B (.classMem A (.cv x))) p0000 p0001 p0002
  exact p0003

@[expose]
noncomputable def g_elunii (A : Class) (B : Class) (C : Class) :
    Nominal.NPrf
      (.imp (syn_wa (.classMem A B) (.classMem B C)) (.classMem A (syn_cuni C))) :=
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
  have p0000 := @g_eleq2 (.cv x) B A
  have p0001 := @g_eleq1 (.cv x) B C
  have p0002 :=
    @g_anbi12d (.classEq (.cv x) B) (.classMem A (.cv x)) (.classMem A B)
      (.classMem (.cv x) C) (.classMem B C) p0000 p0001
  have p0003 :=
    @g_spcegv (syn_wa (.classMem A (.cv x)) (.classMem (.cv x) C))
      (syn_wa (.classMem A B) (.classMem B C)) x B C
      (by
        first
        | (aesop))
      (by
        first
        |
          (simp (config :=
              {
                failIfUnchanged :=
                  false }) only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
              NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, Finset.mem_union] at ⊢;
            aesop))
      p0002
  have p0004 :=
    @g_anabsi7 (.classMem A B) (.classMem B C)
      (syn_wex x (syn_wa (.classMem A (.cv x)) (.classMem (.cv x) C))) p0003
  have p0005 :=
    @g_eluni x A C
      (by
        first
        | (aesop))
      (by
        first
        | (aesop))
  have p0006 :=
    @g_sylibr (syn_wa (.classMem A B) (.classMem B C))
      (syn_wex x (syn_wa (.classMem A (.cv x)) (.classMem (.cv x) C)))
      (.classMem A (syn_cuni C)) p0004 p0005
  exact p0006

@[expose]
noncomputable def g_nfuni (x : Var) (A : Class)
    (hyp_nfuni_1 : Nominal.NPrf (syn_wnfc x A)) :
    Nominal.NPrf (syn_wnfc x (syn_cuni A)) :=
  by
  let proofSupport : Finset Var := ({ x } : Finset Var) ∪ A.fv
  let y : Var := freshVar proofSupport 0
  let z : Var := freshVar proofSupport 1
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
  have fresh_z : z ∉ proofSupport :=
    by
    change freshVar proofSupport 1 ∉ proofSupport
    exact freshVar_not_mem proofSupport 1
  have fresh_z_ne_x : z ≠ x := by
    intro h
    exact fresh_z (Finset.mem_union_left _ (Finset.mem_singleton.mpr h))
  have fresh_x_ne_z : x ≠ z := Ne.symm fresh_z_ne_x
  have fresh_z_not_A : z ∉ A.fv := by
    intro h
    exact fresh_z (Finset.mem_union_right _ (h))
  have fresh_y_ne_z : y ≠ z :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have fresh_z_ne_y : z ≠ y := Ne.symm fresh_y_ne_z
  have p0000 :=
    @g_dfuni2 y z A
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
    @g_nfv (.classMem (.cv y) (.cv z)) x
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
  have p0002 := @g_nfrex (.classMem (.cv y) (.cv z)) x z A hyp_nfuni_1 p0001
  have p0003 := @g_nfab (syn_wrex z A (.classMem (.cv y) (.cv z))) x y p0002
  have p0004 :=
    @g_nfcxfr x (syn_cuni A) (.cab y (syn_wrex z A (.classMem (.cv y) (.cv z)))) p0000
      p0003
  exact p0004

@[expose]
noncomputable def g_unieq (A : Class) (B : Class) :
    Nominal.NPrf (.imp (.classEq A B) (.classEq (syn_cuni A) (syn_cuni B))) :=
  by
  let proofSupport : Finset Var := A.fv ∪ B.fv
  let y : Var := freshVar proofSupport 0
  let x : Var := freshVar proofSupport 1
  have fresh_y : y ∉ proofSupport :=
    by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_y_not_A : y ∉ A.fv := by
    intro h
    exact fresh_y (Finset.mem_union_left _ (h))
  have fresh_y_not_B : y ∉ B.fv := by
    intro h
    exact fresh_y (Finset.mem_union_right _ (h))
  have fresh_x : x ∉ proofSupport :=
    by
    change freshVar proofSupport 1 ∉ proofSupport
    exact freshVar_not_mem proofSupport 1
  have fresh_x_not_A : x ∉ A.fv := by
    intro h
    exact fresh_x (Finset.mem_union_left _ (h))
  have fresh_x_not_B : x ∉ B.fv := by
    intro h
    exact fresh_x (Finset.mem_union_right _ (h))
  have fresh_y_ne_x : y ≠ x :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have fresh_x_ne_y : x ≠ y := Ne.symm fresh_y_ne_x
  have p0000 :=
    @g_rexeq (.classMem (.cv y) (.cv x)) x A B
      (by
        first
        | (aesop))
      (by
        first
        | (aesop))
  have p0001 :=
    @g_abbidv (.classEq A B) (syn_wrex x A (.classMem (.cv y) (.cv x)))
      (syn_wrex x B (.classMem (.cv y) (.cv x))) y
      (by
        first
        |
          (simp (config :=
              {
                failIfUnchanged :=
                  false }) only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
              Finset.mem_union] at ⊢;
            aesop))
      p0000
  have p0002 :=
    @g_dfuni2 y x A
      (by
        first
        | (aesop))
      (by
        first
        | (aesop))
      (by
        first
        | (aesop))
  have p0003 :=
    @g_dfuni2 y x B
      (by
        first
        | (aesop))
      (by
        first
        | (aesop))
      (by
        first
        | (aesop))
  have p0004 :=
    @g_n_3eqtr4g (.classEq A B) (.cab y (syn_wrex x A (.classMem (.cv y) (.cv x))))
      (.cab y (syn_wrex x B (.classMem (.cv y) (.cv x)))) (syn_cuni A) (syn_cuni B) p0001
      p0002 p0003
  exact p0004

@[expose]
noncomputable def g_unieqi (A : Class) (B : Class)
    (hyp_unieqi_1 : Nominal.NPrf (.classEq A B)) :
    Nominal.NPrf (.classEq (syn_cuni A) (syn_cuni B)) :=
  by
  have p0000 := @g_unieq A B
  have p0001 := Nominal.mp hyp_unieqi_1 p0000
  exact p0001

@[expose]
noncomputable def g_unieqd (ph : Wff) (A : Class) (B : Class)
    (hyp_unieqd_1 : Nominal.NPrf (.imp ph (.classEq A B))) :
    Nominal.NPrf (.imp ph (.classEq (syn_cuni A) (syn_cuni B))) :=
  by
  have p0000 := @g_unieq A B
  have p0001 :=
    @g_syl ph (.classEq A B) (.classEq (syn_cuni A) (syn_cuni B)) hyp_unieqd_1 p0000
  exact p0001

@[expose]
noncomputable def g_eluniab (ph : Wff) (x : Var) (A : Class) (dv_A_x : x ∉ A.fv) :
    Nominal.NPrf
      (syn_wb (.classMem A (syn_cuni (.cab x ph)))
        (syn_wex x (syn_wa (.classMem A (.cv x)) ph))) :=
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
    @g_eluni y A (.cab x ph)
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
  have p0001 :=
    @g_nfv (.classMem A (.cv y)) x
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
  have p0002 :=
    @g_nfsab1 ph x y
      (by
        first
        | (aesop))
  have p0003 :=
    @g_nfan (.classMem A (.cv y)) (.classMem (.cv y) (.cab x ph)) x p0001 p0002
  have p0004 :=
    @g_nfv (syn_wa (.classMem A (.cv x)) ph) y
      (by
        first
        |
          (simp (config :=
              {
                failIfUnchanged :=
                  false }) only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
              NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
              NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
              Finset.mem_singleton] at ⊢;
            aesop))
  have p0005 := @g_eleq2 (.cv y) (.cv x) A
  have p0006 := @g_eleq1 (.cv y) (.cv x) (.cab x ph)
  have p0007 := @g_abid ph x
  have p0008 :=
    @g_syl6bb (.classEq (.cv y) (.cv x)) (.classMem (.cv y) (.cab x ph))
      (.classMem (.cv x) (.cab x ph)) ph p0006 p0007
  have p0009 :=
    @g_anbi12d (.classEq (.cv y) (.cv x)) (.classMem A (.cv y)) (.classMem A (.cv x))
      (.classMem (.cv y) (.cab x ph)) ph p0005 p0008
  have p0010_e02_recanon :
    Nominal.NPrf
      (.imp (.objEq y x) (syn_wb (syn_wa (.classMem A (.cv y)) (.classMem (.cv y) (.cab x ph)))
          (syn_wa (.classMem A (.cv x)) ph))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wb syn_wa
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
        · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0009
  have p0010 :=
    @g_cbvex (syn_wa (.classMem A (.cv y)) (.classMem (.cv y) (.cab x ph)))
      (syn_wa (.classMem A (.cv x)) ph) y x p0003 p0004 p0010_e02_recanon
  have p0011 :=
    @g_bitri (.classMem A (syn_cuni (.cab x ph)))
      (syn_wex y (syn_wa (.classMem A (.cv y)) (.classMem (.cv y) (.cab x ph))))
      (syn_wex x (syn_wa (.classMem A (.cv x)) ph)) p0000 p0010
  exact p0011

@[expose]
noncomputable def g_unipr (A : Class) (B : Class)
    (hyp_unipr_1 : Nominal.NPrf (.classMem A (syn_cvv)))
    (hyp_unipr_2 : Nominal.NPrf (.classMem B (syn_cvv))) :
    Nominal.NPrf (.classEq (syn_cuni (syn_cpr A B)) (syn_cun A B)) :=
  by
  let proofSupport : Finset Var := A.fv ∪ B.fv
  let x : Var := freshVar proofSupport 0
  let y : Var := freshVar proofSupport 1
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
  have fresh_y : y ∉ proofSupport :=
    by
    change freshVar proofSupport 1 ∉ proofSupport
    exact freshVar_not_mem proofSupport 1
  have fresh_y_not_A : y ∉ A.fv := by
    intro h
    exact fresh_y (Finset.mem_union_left _ (h))
  have fresh_y_not_B : y ∉ B.fv := by
    intro h
    exact fresh_y (Finset.mem_union_right _ (h))
  have fresh_x_ne_y : x ≠ y :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have fresh_y_ne_x : y ≠ x := Ne.symm fresh_x_ne_y
  have p0000 := @g_vex y
  have p0001 := @g_elpr (.cv y) A B p0000
  have p0002 :=
    @g_anbi2i (.classMem (.cv y) (syn_cpr A B))
      (syn_wo (.classEq (.cv y) A) (.classEq (.cv y) B)) (.objMem x y) p0001
  have p0003 := @g_andi (.objMem x y) (.classEq (.cv y) A) (.classEq (.cv y) B)
  have p0004 :=
    @g_bitri (syn_wa (.objMem x y) (.classMem (.cv y) (syn_cpr A B)))
      (syn_wa (.objMem x y) (syn_wo (.classEq (.cv y) A) (.classEq (.cv y) B)))
      (syn_wo (syn_wa (.objMem x y) (.classEq (.cv y) A))
        (syn_wa (.objMem x y) (.classEq (.cv y) B)))
      p0002 p0003
  have p0005 :=
    @g_exbii (syn_wa (.objMem x y) (.classMem (.cv y) (syn_cpr A B)))
      (syn_wo (syn_wa (.objMem x y) (.classEq (.cv y) A))
        (syn_wa (.objMem x y) (.classEq (.cv y) B)))
      y p0004
  have p0006 :=
    @g_n_19_43 (syn_wa (.objMem x y) (.classEq (.cv y) A))
      (syn_wa (.objMem x y) (.classEq (.cv y) B)) y
  have p0007 :=
    @g_bitri (syn_wex y (syn_wa (.objMem x y) (.classMem (.cv y) (syn_cpr A B))))
      (syn_wex y (syn_wo (syn_wa (.objMem x y) (.classEq (.cv y) A))
          (syn_wa (.objMem x y) (.classEq (.cv y) B))))
      (syn_wo (syn_wex y (syn_wa (.objMem x y) (.classEq (.cv y) A)))
        (syn_wex y (syn_wa (.objMem x y) (.classEq (.cv y) B))))
      p0005 p0006
  have p0008 :=
    @g_eluni y (.cv x) (syn_cpr A B)
      (by
        first
        |
          (simp (config :=
              {
                failIfUnchanged :=
                  false }) only [NFChoice.Compiler.CoreFVSimp.fv_class_cv,
              Finset.mem_singleton] at ⊢;
            aesop))
      (by
        first
        |
          (simp (config :=
              {
                failIfUnchanged :=
                  false }) only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpr,
              Finset.mem_union] at ⊢;
            aesop))
  have p0009 := @g_elun (.cv x) A B
  have p0010 :=
    @g_clel3 y (.cv x) A
      (by
        first
        |
          (simp (config :=
              {
                failIfUnchanged :=
                  false }) only [NFChoice.Compiler.CoreFVSimp.fv_class_cv,
              Finset.mem_singleton] at ⊢;
            aesop))
      (by
        first
        | (aesop))
      hyp_unipr_1
  have p0011 := @g_exancom (.classEq (.cv y) A) (.objMem x y) y
  have p0012_e00_recanon :
    Nominal.NPrf
      (syn_wb (.classMem (.cv x) A) (syn_wex y (syn_wa (.classEq (.cv y) A) (.objMem x y)))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wb syn_wex syn_wa
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
              exact Nominal.RecanonTransportDev.TRecanonWff.classMem_objMem _ _
        · apply Nominal.RecanonTransportDev.TRecanonWff.neg
          apply Nominal.RecanonTransportDev.TRecanonWff.imp
          · apply Nominal.RecanonTransportDev.TRecanonWff.neg
            apply Nominal.RecanonTransportDev.TRecanonWff.all
            apply Nominal.RecanonTransportDev.TRecanonWff.neg
            apply Nominal.RecanonTransportDev.TRecanonWff.neg
            apply Nominal.RecanonTransportDev.TRecanonWff.imp
            · exact Nominal.RecanonTransportDev.TRecanonWff.same _
            · apply Nominal.RecanonTransportDev.TRecanonWff.neg
              exact Nominal.RecanonTransportDev.TRecanonWff.classMem_objMem _ _
          · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0010
  have p0012 :=
    @g_bitri (.classMem (.cv x) A) (syn_wex y (syn_wa (.classEq (.cv y) A) (.objMem x y)))
      (syn_wex y (syn_wa (.objMem x y) (.classEq (.cv y) A))) p0012_e00_recanon p0011
  have p0013 :=
    @g_clel3 y (.cv x) B
      (by
        first
        |
          (simp (config :=
              {
                failIfUnchanged :=
                  false }) only [NFChoice.Compiler.CoreFVSimp.fv_class_cv,
              Finset.mem_singleton] at ⊢;
            aesop))
      (by
        first
        | (aesop))
      hyp_unipr_2
  have p0014 := @g_exancom (.classEq (.cv y) B) (.objMem x y) y
  have p0015_e00_recanon :
    Nominal.NPrf
      (syn_wb (.classMem (.cv x) B) (syn_wex y (syn_wa (.classEq (.cv y) B) (.objMem x y)))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wb syn_wex syn_wa
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
              exact Nominal.RecanonTransportDev.TRecanonWff.classMem_objMem _ _
        · apply Nominal.RecanonTransportDev.TRecanonWff.neg
          apply Nominal.RecanonTransportDev.TRecanonWff.imp
          · apply Nominal.RecanonTransportDev.TRecanonWff.neg
            apply Nominal.RecanonTransportDev.TRecanonWff.all
            apply Nominal.RecanonTransportDev.TRecanonWff.neg
            apply Nominal.RecanonTransportDev.TRecanonWff.neg
            apply Nominal.RecanonTransportDev.TRecanonWff.imp
            · exact Nominal.RecanonTransportDev.TRecanonWff.same _
            · apply Nominal.RecanonTransportDev.TRecanonWff.neg
              exact Nominal.RecanonTransportDev.TRecanonWff.classMem_objMem _ _
          · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0013
  have p0015 :=
    @g_bitri (.classMem (.cv x) B) (syn_wex y (syn_wa (.classEq (.cv y) B) (.objMem x y)))
      (syn_wex y (syn_wa (.objMem x y) (.classEq (.cv y) B))) p0015_e00_recanon p0014
  have p0016 :=
    @g_orbi12i (.classMem (.cv x) A)
      (syn_wex y (syn_wa (.objMem x y) (.classEq (.cv y) A))) (.classMem (.cv x) B)
      (syn_wex y (syn_wa (.objMem x y) (.classEq (.cv y) B))) p0012 p0015
  have p0017 :=
    @g_bitri (.classMem (.cv x) (syn_cun A B))
      (syn_wo (.classMem (.cv x) A) (.classMem (.cv x) B))
      (syn_wo (syn_wex y (syn_wa (.objMem x y) (.classEq (.cv y) A)))
        (syn_wex y (syn_wa (.objMem x y) (.classEq (.cv y) B))))
      p0009 p0016
  have p0018_e01_recanon :
    Nominal.NPrf
      (syn_wb (.classMem (.cv x) (syn_cuni (syn_cpr A B)))
        (syn_wex y (syn_wa (.objMem x y) (.classMem (.cv y) (syn_cpr A B))))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wb syn_cuni syn_wex syn_wa syn_cpr syn_cun syn_cnin syn_wnan syn_ccompl
          syn_csn
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
            · exact Nominal.RecanonTransportDev.TRecanonWff.classMem_objMem _ _
            · exact Nominal.RecanonTransportDev.TRecanonWff.same _
        · apply Nominal.RecanonTransportDev.TRecanonWff.neg
          apply Nominal.RecanonTransportDev.TRecanonWff.imp
          · apply Nominal.RecanonTransportDev.TRecanonWff.neg
            apply Nominal.RecanonTransportDev.TRecanonWff.all
            apply Nominal.RecanonTransportDev.TRecanonWff.neg
            apply Nominal.RecanonTransportDev.TRecanonWff.neg
            apply Nominal.RecanonTransportDev.TRecanonWff.imp
            · exact Nominal.RecanonTransportDev.TRecanonWff.classMem_objMem _ _
            · exact Nominal.RecanonTransportDev.TRecanonWff.same _
          · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0008
  have p0018 :=
    @g_n_3bitr4i (syn_wex y (syn_wa (.objMem x y) (.classMem (.cv y) (syn_cpr A B))))
      (syn_wo (syn_wex y (syn_wa (.objMem x y) (.classEq (.cv y) A)))
        (syn_wex y (syn_wa (.objMem x y) (.classEq (.cv y) B))))
      (.classMem (.cv x) (syn_cuni (syn_cpr A B))) (.classMem (.cv x) (syn_cun A B)) p0007
      p0018_e01_recanon p0017
  have p0019 :=
    @g_eqriv x (syn_cuni (syn_cpr A B)) (syn_cun A B)
      (by
        first
        |
          (simp (config :=
              {
                failIfUnchanged :=
                  false }) only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cuni,
              NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpr,
              Finset.mem_union] at ⊢;
            aesop))
      (by
        first
        |
          (simp (config :=
              {
                failIfUnchanged :=
                  false }) only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cun,
              Finset.mem_union] at ⊢;
            aesop))
      p0018
  exact p0019

@[expose]
noncomputable def g_unisn (A : Class)
    (hyp_unisn_1 : Nominal.NPrf (.classMem A (syn_cvv))) :
    Nominal.NPrf (.classEq (syn_cuni (syn_csn A)) A) :=
  by
  have p0000 := @g_dfsn2 A
  have p0001 := @g_unieqi (syn_csn A) (syn_cpr A A) p0000
  have p0002 := @g_unipr A A hyp_unisn_1 hyp_unisn_1
  have p0003 := @g_unidm A
  have p0004 :=
    @g_n_3eqtri (syn_cuni (syn_csn A)) (syn_cuni (syn_cpr A A)) (syn_cun A A) A p0001
      p0002 p0003
  exact p0004


end NFChoice.DirectNominalPrf.WPPReplay
