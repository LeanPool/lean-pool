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

/-- Checked nominal proof certificate identified upstream as `g_dedth2h`. -/
@[expose]
noncomputable def gDedth2h (ph : Wff) (ps : Wff) (ch : Wff) (th : Wff) (ta : Wff)
    (A : Class) (B : Class) (C : Class) (D : Class)
    (hyp_dedth2h_1 : Nominal.NPrf (.imp (.classEq A (synCif ph A C)) (synWb ch th)))
    (hyp_dedth2h_2 : Nominal.NPrf (.imp (.classEq B (synCif ps B D)) (synWb th ta)))
    (hyp_dedth2h_3 : Nominal.NPrf ta) : Nominal.NPrf (.imp (synWa ph ps) ch) :=
  by
  have p0000 := @gImbi2d (.classEq A (synCif ph A C)) ch th ps hyp_dedth2h_1
  have p0001 := @gDedth ps th ta B D hyp_dedth2h_2 hyp_dedth2h_3
  have p0002 := @gDedth ph (.imp ps ch) (.imp ps th) A C p0000 p0001
  have p0003 := @gImp ph ps ch p0002
  exact p0003

/-- Checked nominal proof certificate identified upstream as `g_dedth3h`. -/
@[expose]
noncomputable def gDedth3h (ph : Wff) (ps : Wff) (ch : Wff) (th : Wff) (ta : Wff)
    (et : Wff) (ze : Wff) (A : Class) (B : Class) (C : Class) (D : Class) (R : Class)
    (S : Class)
    (hyp_dedth3h_1 : Nominal.NPrf (.imp (.classEq A (synCif ph A D)) (synWb th ta)))
    (hyp_dedth3h_2 : Nominal.NPrf (.imp (.classEq B (synCif ps B R)) (synWb ta et)))
    (hyp_dedth3h_3 : Nominal.NPrf (.imp (.classEq C (synCif ch C S)) (synWb et ze)))
    (hyp_dedth3h_4 : Nominal.NPrf ze) : Nominal.NPrf (.imp (synW3a ph ps ch) th) :=
  by
  have p0000 := @gImbi2d (.classEq A (synCif ph A D)) th ta (synWa ps ch) hyp_dedth3h_1
  have p0001 :=
    @gDedth2h ps ch ta et ze B C R S hyp_dedth3h_2 hyp_dedth3h_3 hyp_dedth3h_4
  have p0002 :=
    @gDedth ph (.imp (synWa ps ch) th) (.imp (synWa ps ch) ta) A D p0000 p0001
  have p0003 := @gN3impib ph ps ch th p0002
  exact p0003

/-- Checked nominal proof certificate identified upstream as `g_dedth4h`. -/
@[expose]
noncomputable def gDedth4h (ph : Wff) (ps : Wff) (ch : Wff) (th : Wff) (ta : Wff)
    (et : Wff) (ze : Wff) (si : Wff) (rh : Wff) (A : Class) (B : Class) (C : Class)
    (D : Class) (R : Class) (S : Class) (F : Class) (G : Class)
    (hyp_dedth4h_1 : Nominal.NPrf (.imp (.classEq A (synCif ph A R)) (synWb ta et)))
    (hyp_dedth4h_2 : Nominal.NPrf (.imp (.classEq B (synCif ps B S)) (synWb et ze)))
    (hyp_dedth4h_3 : Nominal.NPrf (.imp (.classEq C (synCif ch C F)) (synWb ze si)))
    (hyp_dedth4h_4 : Nominal.NPrf (.imp (.classEq D (synCif th D G)) (synWb si rh)))
    (hyp_dedth4h_5 : Nominal.NPrf rh) :
    Nominal.NPrf (.imp (synWa (synWa ph ps) (synWa ch th)) ta) :=
  by
  have p0000 := @gImbi2d (.classEq A (synCif ph A R)) ta et (synWa ch th) hyp_dedth4h_1
  have p0001 := @gImbi2d (.classEq B (synCif ps B S)) et ze (synWa ch th) hyp_dedth4h_2
  have p0002 :=
    @gDedth2h ch th ze si rh C D F G hyp_dedth4h_3 hyp_dedth4h_4 hyp_dedth4h_5
  have p0003 :=
    @gDedth2h ph ps (.imp (synWa ch th) ta) (.imp (synWa ch th) et)
      (.imp (synWa ch th) ze) A B R S p0000 p0001 p0002
  have p0004 := @gImp (synWa ph ps) (synWa ch th) ta p0003
  exact p0004

/-- Checked nominal proof certificate identified upstream as `g_dedth2v`. -/
@[expose]
noncomputable def gDedth2v (ph : Wff) (ps : Wff) (ch : Wff) (th : Wff) (A : Class)
    (B : Class) (C : Class) (D : Class)
    (hyp_dedth2v_1 : Nominal.NPrf (.imp (.classEq A (synCif ph A C)) (synWb ps ch)))
    (hyp_dedth2v_2 : Nominal.NPrf (.imp (.classEq B (synCif ph B D)) (synWb ch th)))
    (hyp_dedth2v_3 : Nominal.NPrf th) : Nominal.NPrf (.imp ph ps) :=
  by
  have p0000 :=
    @gDedth2h ph ph ps ch th A B C D hyp_dedth2v_1 hyp_dedth2v_2 hyp_dedth2v_3
  have p0001 := @gAnidms ph ps p0000
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_dedth3v`. -/
@[expose]
noncomputable def gDedth3v (ph : Wff) (ps : Wff) (ch : Wff) (th : Wff) (ta : Wff)
    (A : Class) (B : Class) (C : Class) (D : Class) (R : Class) (S : Class)
    (hyp_dedth3v_1 : Nominal.NPrf (.imp (.classEq A (synCif ph A D)) (synWb ps ch)))
    (hyp_dedth3v_2 : Nominal.NPrf (.imp (.classEq B (synCif ph B R)) (synWb ch th)))
    (hyp_dedth3v_3 : Nominal.NPrf (.imp (.classEq C (synCif ph C S)) (synWb th ta)))
    (hyp_dedth3v_4 : Nominal.NPrf ta) : Nominal.NPrf (.imp ph ps) :=
  by
  have p0000 :=
    @gDedth3h ph ph ph ps ch th ta A B C D R S hyp_dedth3v_1 hyp_dedth3v_2 hyp_dedth3v_3
      hyp_dedth3v_4
  have p0001 := @gN3anidm12 ph ph ps p0000
  have p0002 := @gAnidms ph ps p0001
  exact p0002

/-- Checked nominal proof certificate identified upstream as `g_dedth4v`. -/
@[expose]
noncomputable def gDedth4v (ph : Wff) (ps : Wff) (ch : Wff) (th : Wff) (ta : Wff)
    (et : Wff) (A : Class) (B : Class) (C : Class) (D : Class) (R : Class) (S : Class)
    (T : Class) (U : Class)
    (hyp_dedth4v_1 : Nominal.NPrf (.imp (.classEq A (synCif ph A R)) (synWb ps ch)))
    (hyp_dedth4v_2 : Nominal.NPrf (.imp (.classEq B (synCif ph B S)) (synWb ch th)))
    (hyp_dedth4v_3 : Nominal.NPrf (.imp (.classEq C (synCif ph C T)) (synWb th ta)))
    (hyp_dedth4v_4 : Nominal.NPrf (.imp (.classEq D (synCif ph D U)) (synWb ta et)))
    (hyp_dedth4v_5 : Nominal.NPrf et) : Nominal.NPrf (.imp ph ps) :=
  by
  have p0000 :=
    @gDedth4h ph ph ph ph ps ch th ta et A B C D R S T U hyp_dedth4v_1 hyp_dedth4v_2
      hyp_dedth4v_3 hyp_dedth4v_4 hyp_dedth4v_5
  have p0001 := @gAnidms (synWa ph ph) ps p0000
  have p0002 := @gAnidms ph ps p0001
  exact p0002

/-- Checked nominal proof certificate identified upstream as `g_elimhyp2v`. -/
@[expose]
noncomputable def gElimhyp2v (ph : Wff) (ch : Wff) (th : Wff) (ta : Wff) (et : Wff)
    (A : Class) (B : Class) (C : Class) (D : Class)
    (hyp_elimhyp2v_1 : Nominal.NPrf (.imp (.classEq A (synCif ph A C)) (synWb ph ch)))
    (hyp_elimhyp2v_2 : Nominal.NPrf (.imp (.classEq B (synCif ph B D)) (synWb ch th)))
    (hyp_elimhyp2v_3 : Nominal.NPrf (.imp (.classEq C (synCif ph A C)) (synWb ta et)))
    (hyp_elimhyp2v_4 : Nominal.NPrf (.imp (.classEq D (synCif ph B D)) (synWb et th)))
    (hyp_elimhyp2v_5 : Nominal.NPrf ta) : Nominal.NPrf th :=
  by
  have p0000 := @gIftrue ph A C
  have p0001 := @gEqcomd ph (synCif ph A C) A p0000
  have p0002 :=
    @gSyl ph (.classEq A (synCif ph A C)) (synWb ph ch) p0001 hyp_elimhyp2v_1
  have p0003 := @gIftrue ph B D
  have p0004 := @gEqcomd ph (synCif ph B D) B p0003
  have p0005 :=
    @gSyl ph (.classEq B (synCif ph B D)) (synWb ch th) p0004 hyp_elimhyp2v_2
  have p0006 := @gBitrd ph ph ch th p0002 p0005
  have p0007 := @gIbi ph th p0006
  have p0008 := @gIffalse ph A C
  have p0009 := @gEqcomd (.neg ph) (synCif ph A C) C p0008
  have p0010 :=
    @gSyl (.neg ph) (.classEq C (synCif ph A C)) (synWb ta et) p0009 hyp_elimhyp2v_3
  have p0011 := @gIffalse ph B D
  have p0012 := @gEqcomd (.neg ph) (synCif ph B D) D p0011
  have p0013 :=
    @gSyl (.neg ph) (.classEq D (synCif ph B D)) (synWb et th) p0012 hyp_elimhyp2v_4
  have p0014 := @gBitrd (.neg ph) ta et th p0010 p0013
  have p0015 := @gMpbii (.neg ph) ta th hyp_elimhyp2v_5 p0014
  have p0016 := @gPm261i ph th p0007 p0015
  exact p0016

/-- Checked nominal proof certificate identified upstream as `g_elimhyp3v`. -/
@[expose]
noncomputable def gElimhyp3v (ph : Wff) (ch : Wff) (th : Wff) (ta : Wff) (et : Wff)
    (ze : Wff) (si : Wff) (A : Class) (B : Class) (C : Class) (D : Class) (R : Class)
    (S : Class)
    (hyp_elimhyp3v_1 : Nominal.NPrf (.imp (.classEq A (synCif ph A D)) (synWb ph ch)))
    (hyp_elimhyp3v_2 : Nominal.NPrf (.imp (.classEq B (synCif ph B R)) (synWb ch th)))
    (hyp_elimhyp3v_3 : Nominal.NPrf (.imp (.classEq C (synCif ph C S)) (synWb th ta)))
    (hyp_elimhyp3v_4 : Nominal.NPrf (.imp (.classEq D (synCif ph A D)) (synWb et ze)))
    (hyp_elimhyp3v_5 : Nominal.NPrf (.imp (.classEq R (synCif ph B R)) (synWb ze si)))
    (hyp_elimhyp3v_6 : Nominal.NPrf (.imp (.classEq S (synCif ph C S)) (synWb si ta)))
    (hyp_elimhyp3v_7 : Nominal.NPrf et) : Nominal.NPrf ta :=
  by
  have p0000 := @gIftrue ph A D
  have p0001 := @gEqcomd ph (synCif ph A D) A p0000
  have p0002 :=
    @gSyl ph (.classEq A (synCif ph A D)) (synWb ph ch) p0001 hyp_elimhyp3v_1
  have p0003 := @gIftrue ph B R
  have p0004 := @gEqcomd ph (synCif ph B R) B p0003
  have p0005 :=
    @gSyl ph (.classEq B (synCif ph B R)) (synWb ch th) p0004 hyp_elimhyp3v_2
  have p0006 := @gIftrue ph C S
  have p0007 := @gEqcomd ph (synCif ph C S) C p0006
  have p0008 :=
    @gSyl ph (.classEq C (synCif ph C S)) (synWb th ta) p0007 hyp_elimhyp3v_3
  have p0009 := @gN3bitrd ph ph ch th ta p0002 p0005 p0008
  have p0010 := @gIbi ph ta p0009
  have p0011 := @gIffalse ph A D
  have p0012 := @gEqcomd (.neg ph) (synCif ph A D) D p0011
  have p0013 :=
    @gSyl (.neg ph) (.classEq D (synCif ph A D)) (synWb et ze) p0012 hyp_elimhyp3v_4
  have p0014 := @gIffalse ph B R
  have p0015 := @gEqcomd (.neg ph) (synCif ph B R) R p0014
  have p0016 :=
    @gSyl (.neg ph) (.classEq R (synCif ph B R)) (synWb ze si) p0015 hyp_elimhyp3v_5
  have p0017 := @gIffalse ph C S
  have p0018 := @gEqcomd (.neg ph) (synCif ph C S) S p0017
  have p0019 :=
    @gSyl (.neg ph) (.classEq S (synCif ph C S)) (synWb si ta) p0018 hyp_elimhyp3v_6
  have p0020 := @gN3bitrd (.neg ph) et ze si ta p0013 p0016 p0019
  have p0021 := @gMpbii (.neg ph) et ta hyp_elimhyp3v_7 p0020
  have p0022 := @gPm261i ph ta p0010 p0021
  exact p0022

/-- Checked nominal proof certificate identified upstream as `g_elimhyp4v`. -/
@[expose]
noncomputable def gElimhyp4v (ph : Wff) (ps : Wff) (ch : Wff) (th : Wff) (ta : Wff)
    (et : Wff) (ze : Wff) (si : Wff) (rh : Wff) (A : Class) (B : Class) (C : Class)
    (D : Class) (R : Class) (S : Class) (F : Class) (G : Class)
    (hyp_elimhyp4v_1 : Nominal.NPrf (.imp (.classEq A (synCif ph A D)) (synWb ph ch)))
    (hyp_elimhyp4v_2 : Nominal.NPrf (.imp (.classEq B (synCif ph B R)) (synWb ch th)))
    (hyp_elimhyp4v_3 : Nominal.NPrf (.imp (.classEq C (synCif ph C S)) (synWb th ta)))
    (hyp_elimhyp4v_4 : Nominal.NPrf (.imp (.classEq F (synCif ph F G)) (synWb ta ps)))
    (hyp_elimhyp4v_5 : Nominal.NPrf (.imp (.classEq D (synCif ph A D)) (synWb et ze)))
    (hyp_elimhyp4v_6 : Nominal.NPrf (.imp (.classEq R (synCif ph B R)) (synWb ze si)))
    (hyp_elimhyp4v_7 : Nominal.NPrf (.imp (.classEq S (synCif ph C S)) (synWb si rh)))
    (hyp_elimhyp4v_8 : Nominal.NPrf (.imp (.classEq G (synCif ph F G)) (synWb rh ps)))
    (hyp_elimhyp4v_9 : Nominal.NPrf et) : Nominal.NPrf ps :=
  by
  have p0000 := @gIftrue ph A D
  have p0001 := @gEqcomd ph (synCif ph A D) A p0000
  have p0002 :=
    @gSyl ph (.classEq A (synCif ph A D)) (synWb ph ch) p0001 hyp_elimhyp4v_1
  have p0003 := @gIftrue ph B R
  have p0004 := @gEqcomd ph (synCif ph B R) B p0003
  have p0005 :=
    @gSyl ph (.classEq B (synCif ph B R)) (synWb ch th) p0004 hyp_elimhyp4v_2
  have p0006 := @gBitrd ph ph ch th p0002 p0005
  have p0007 := @gIftrue ph C S
  have p0008 := @gEqcomd ph (synCif ph C S) C p0007
  have p0009 :=
    @gSyl ph (.classEq C (synCif ph C S)) (synWb th ta) p0008 hyp_elimhyp4v_3
  have p0010 := @gIftrue ph F G
  have p0011 := @gEqcomd ph (synCif ph F G) F p0010
  have p0012 :=
    @gSyl ph (.classEq F (synCif ph F G)) (synWb ta ps) p0011 hyp_elimhyp4v_4
  have p0013 := @gN3bitrd ph ph th ta ps p0006 p0009 p0012
  have p0014 := @gIbi ph ps p0013
  have p0015 := @gIffalse ph A D
  have p0016 := @gEqcomd (.neg ph) (synCif ph A D) D p0015
  have p0017 :=
    @gSyl (.neg ph) (.classEq D (synCif ph A D)) (synWb et ze) p0016 hyp_elimhyp4v_5
  have p0018 := @gIffalse ph B R
  have p0019 := @gEqcomd (.neg ph) (synCif ph B R) R p0018
  have p0020 :=
    @gSyl (.neg ph) (.classEq R (synCif ph B R)) (synWb ze si) p0019 hyp_elimhyp4v_6
  have p0021 := @gBitrd (.neg ph) et ze si p0017 p0020
  have p0022 := @gIffalse ph C S
  have p0023 := @gEqcomd (.neg ph) (synCif ph C S) S p0022
  have p0024 :=
    @gSyl (.neg ph) (.classEq S (synCif ph C S)) (synWb si rh) p0023 hyp_elimhyp4v_7
  have p0025 := @gIffalse ph F G
  have p0026 := @gEqcomd (.neg ph) (synCif ph F G) G p0025
  have p0027 :=
    @gSyl (.neg ph) (.classEq G (synCif ph F G)) (synWb rh ps) p0026 hyp_elimhyp4v_8
  have p0028 := @gN3bitrd (.neg ph) et si rh ps p0021 p0024 p0027
  have p0029 := @gMpbii (.neg ph) et ps hyp_elimhyp4v_9 p0028
  have p0030 := @gPm261i ph ps p0014 p0029
  exact p0030

/-- Checked nominal proof certificate identified upstream as `g_keephyp`. -/
@[expose]
noncomputable def gKeephyp (ph : Wff) (ps : Wff) (ch : Wff) (th : Wff) (A : Class)
    (B : Class)
    (hyp_keephyp_1 : Nominal.NPrf (.imp (.classEq A (synCif ph A B)) (synWb ps th)))
    (hyp_keephyp_2 : Nominal.NPrf (.imp (.classEq B (synCif ph A B)) (synWb ch th)))
    (hyp_keephyp_3 : Nominal.NPrf ps) (hyp_keephyp_4 : Nominal.NPrf ch) :
    Nominal.NPrf th :=
  by
  have p0000 := @gIfboth ph ps ch th A B hyp_keephyp_1 hyp_keephyp_2
  have p0001 := @gMp2an ps ch th hyp_keephyp_3 hyp_keephyp_4 p0000
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_keephyp2v`. -/
@[expose]
noncomputable def gKeephyp2v (ph : Wff) (ps : Wff) (ch : Wff) (th : Wff) (ta : Wff)
    (et : Wff) (A : Class) (B : Class) (C : Class) (D : Class)
    (hyp_keephyp2v_1 : Nominal.NPrf (.imp (.classEq A (synCif ph A C)) (synWb ps ch)))
    (hyp_keephyp2v_2 : Nominal.NPrf (.imp (.classEq B (synCif ph B D)) (synWb ch th)))
    (hyp_keephyp2v_3 : Nominal.NPrf (.imp (.classEq C (synCif ph A C)) (synWb ta et)))
    (hyp_keephyp2v_4 : Nominal.NPrf (.imp (.classEq D (synCif ph B D)) (synWb et th)))
    (hyp_keephyp2v_5 : Nominal.NPrf ps) (hyp_keephyp2v_6 : Nominal.NPrf ta) :
    Nominal.NPrf th := by
  have p0000 := @gIftrue ph A C
  have p0001 := @gEqcomd ph (synCif ph A C) A p0000
  have p0002 :=
    @gSyl ph (.classEq A (synCif ph A C)) (synWb ps ch) p0001 hyp_keephyp2v_1
  have p0003 := @gIftrue ph B D
  have p0004 := @gEqcomd ph (synCif ph B D) B p0003
  have p0005 :=
    @gSyl ph (.classEq B (synCif ph B D)) (synWb ch th) p0004 hyp_keephyp2v_2
  have p0006 := @gBitrd ph ps ch th p0002 p0005
  have p0007 := @gMpbii ph ps th hyp_keephyp2v_5 p0006
  have p0008 := @gIffalse ph A C
  have p0009 := @gEqcomd (.neg ph) (synCif ph A C) C p0008
  have p0010 :=
    @gSyl (.neg ph) (.classEq C (synCif ph A C)) (synWb ta et) p0009 hyp_keephyp2v_3
  have p0011 := @gIffalse ph B D
  have p0012 := @gEqcomd (.neg ph) (synCif ph B D) D p0011
  have p0013 :=
    @gSyl (.neg ph) (.classEq D (synCif ph B D)) (synWb et th) p0012 hyp_keephyp2v_4
  have p0014 := @gBitrd (.neg ph) ta et th p0010 p0013
  have p0015 := @gMpbii (.neg ph) ta th hyp_keephyp2v_6 p0014
  have p0016 := @gPm261i ph th p0007 p0015
  exact p0016

/-- Checked nominal proof certificate identified upstream as `g_keepel`. -/
@[expose]
noncomputable def gKeepel (ph : Wff) (A : Class) (B : Class) (C : Class)
    (hyp_keepel_1 : Nominal.NPrf (.classMem A C))
    (hyp_keepel_2 : Nominal.NPrf (.classMem B C)) :
    Nominal.NPrf (.classMem (synCif ph A B) C) :=
  by
  have p0000 := @gEleq1 A (synCif ph A B) C
  have p0001 := @gEleq1 B (synCif ph A B) C
  have p0002 :=
    @gKeephyp ph (.classMem A C) (.classMem B C) (.classMem (synCif ph A B) C) A B p0000
      p0001 hyp_keepel_1 hyp_keepel_2
  exact p0002

/-- Checked nominal proof certificate identified upstream as `g_ifex`. -/
@[expose]
noncomputable def gIfex (ph : Wff) (A : Class) (B : Class)
    (hyp_dedex_1 : Nominal.NPrf (.classMem A (synCvv)))
    (hyp_dedex_2 : Nominal.NPrf (.classMem B (synCvv))) :
    Nominal.NPrf (.classMem (synCif ph A B) (synCvv)) :=
  by
  have p0000 := @gKeepel ph A B (synCvv) hyp_dedex_1 hyp_dedex_2
  exact p0000

/-- Checked nominal proof certificate identified upstream as `g_pweq`. -/
@[expose]
noncomputable def gPweq (A : Class) (B : Class) :
    Nominal.NPrf (.imp (.classEq A B) (.classEq (synCpw A) (synCpw B))) :=
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
  have p0000 := @gSseq2 A B (.cv x)
  have p0001 :=
    @gAbbidv (.classEq A B) (synWss (.cv x) A) (synWss (.cv x) B) x
      (by
        (simp (config :=
              {
                failIfUnchanged :=
                  false }) only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
              Finset.mem_union] at ⊢;
            aesop))
      p0000
  have p0002 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominalDfPw x A
      (by
        aesop)
  have p0003 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominalDfPw x B
      (by
        aesop)
  have p0004 :=
    @gN3eqtr4g (.classEq A B) (.cab x (synWss (.cv x) A)) (.cab x (synWss (.cv x) B))
      (synCpw A) (synCpw B) p0001 p0002 p0003
  exact p0004

/-- Checked nominal proof certificate identified upstream as `g_pweqi`. -/
@[expose]
noncomputable def gPweqi (A : Class) (B : Class)
    (hyp_pweqi_1 : Nominal.NPrf (.classEq A B)) :
    Nominal.NPrf (.classEq (synCpw A) (synCpw B)) :=
  by
  have p0000 := @gPweq A B
  have p0001 := Nominal.mp hyp_pweqi_1 p0000
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_pweqd`. -/
@[expose]
noncomputable def gPweqd (ph : Wff) (A : Class) (B : Class)
    (hyp_pweqd_1 : Nominal.NPrf (.imp ph (.classEq A B))) :
    Nominal.NPrf (.imp ph (.classEq (synCpw A) (synCpw B))) :=
  by
  have p0000 := @gPweq A B
  have p0001 :=
    @gSyl ph (.classEq A B) (.classEq (synCpw A) (synCpw B)) hyp_pweqd_1 p0000
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_elpw`. -/
@[expose]
noncomputable def gElpw (A : Class) (B : Class)
    (hyp_elpw_1 : Nominal.NPrf (.classMem A (synCvv))) :
    Nominal.NPrf (synWb (.classMem A (synCpw B)) (synWss A B)) :=
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
  have p0000 := @gSseq1 (.cv x) A B
  have p0001 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominalDfPw x B
      (by
        aesop)
  have p0002 :=
    @gElab2 (synWss (.cv x) B) (synWss A B) x A (synCpw B)
      (by
        aesop)
      (by
        (simp (config :=
              {
                failIfUnchanged :=
                  false }) only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wss,
              Finset.mem_union] at ⊢;
            aesop))
      hyp_elpw_1 p0000 p0001
  exact p0002

/-- Checked nominal proof certificate identified upstream as `g_elpwg`. -/
@[expose]
noncomputable def gElpwg (A : Class) (B : Class) (V : Class) :
    Nominal.NPrf
      (.imp (.classMem A V) (synWb (.classMem A (synCpw B)) (synWss A B))) :=
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
  have p0000 := @gEleq1 (.cv x) A (synCpw B)
  have p0001 := @gSseq1 (.cv x) A B
  have p0002 := @gVex x
  have p0003 := @gElpw (.cv x) B p0002
  have p0004 :=
    @gVtoclbg (.classMem (.cv x) (synCpw B)) (synWss (.cv x) B)
      (.classMem A (synCpw B)) (synWss A B) x A V
      (by
        aesop)
      (by
        (simp (config :=
              {
                failIfUnchanged :=
                  false }) only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
              NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw,
              Finset.mem_union] at ⊢;
            aesop))
      (by
        (simp (config :=
              {
                failIfUnchanged :=
                  false }) only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wss,
              Finset.mem_union] at ⊢;
            aesop))
      p0000 p0001 p0003
  exact p0004

/-- Checked nominal proof certificate identified upstream as `g_sneq`. -/
@[expose]
noncomputable def gSneq (A : Class) (B : Class) :
    Nominal.NPrf (.imp (.classEq A B) (.classEq (synCsn A) (synCsn B))) :=
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
  have p0000 := @gEqeq2 A B (.cv x)
  have p0001 :=
    @gAbbidv (.classEq A B) (.classEq (.cv x) A) (.classEq (.cv x) B) x
      (by
        (simp (config :=
              {
                failIfUnchanged :=
                  false }) only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
              Finset.mem_union] at ⊢;
            aesop))
      p0000
  have p0002 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominalDfSn x A
      (by
        aesop)
  have p0003 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominalDfSn x B
      (by
        aesop)
  have p0004 :=
    @gN3eqtr4g (.classEq A B) (.cab x (.classEq (.cv x) A))
      (.cab x (.classEq (.cv x) B)) (synCsn A) (synCsn B) p0001 p0002 p0003
  exact p0004

/-- Checked nominal proof certificate identified upstream as `g_sneqi`. -/
@[expose]
noncomputable def gSneqi (A : Class) (B : Class)
    (hyp_sneqi_1 : Nominal.NPrf (.classEq A B)) :
    Nominal.NPrf (.classEq (synCsn A) (synCsn B)) :=
  by
  have p0000 := @gSneq A B
  have p0001 := Nominal.mp hyp_sneqi_1 p0000
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_sneqd`. -/
@[expose]
noncomputable def gSneqd (ph : Wff) (A : Class) (B : Class)
    (hyp_sneqd_1 : Nominal.NPrf (.imp ph (.classEq A B))) :
    Nominal.NPrf (.imp ph (.classEq (synCsn A) (synCsn B))) :=
  by
  have p0000 := @gSneq A B
  have p0001 :=
    @gSyl ph (.classEq A B) (.classEq (synCsn A) (synCsn B)) hyp_sneqd_1 p0000
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_dfsn2`. -/
@[expose]
noncomputable def gDfsn2 (A : Class) :
    Nominal.NPrf (.classEq (synCsn A) (synCpr A A)) :=
  by
  have p0000 := (Nominal.classEqRefl (synCpr A A))
  have p0001 := @gUnidm (synCsn A)
  have p0002 :=
    @gEqtr2i (synCpr A A) (synCun (synCsn A) (synCsn A)) (synCsn A) p0000 p0001
  exact p0002

/-- Checked nominal proof certificate identified upstream as `g_elsn`. -/
@[expose]
noncomputable def gElsn (x : Var) (A : Class) (dv_A_x : x ∉ A.fv) :
    Nominal.NPrf (synWb (.classMem (.cv x) (synCsn A)) (.classEq (.cv x) A)) :=
  by
  have p0000 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominalDfSn x A
      (by
        aesop)
  have p0001 := @gEqabri (.classEq (.cv x) A) x (synCsn A) p0000
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_dfpr2`. -/
@[expose]
noncomputable def gDfpr2 (x : Var) (A : Class) (B : Class) (dv_A_x : x ∉ A.fv)
    (dv_B_x : x ∉ B.fv) :
    Nominal.NPrf
      (.classEq (synCpr A B) (.cab x (synWo (.classEq (.cv x) A) (.classEq (.cv x) B)))) :=
  by
  have p0000 := (Nominal.classEqRefl (synCpr A B))
  have p0001 := @gElun (.cv x) (synCsn A) (synCsn B)
  have p0002 :=
    @gElsn x A
      (by
        aesop)
  have p0003 :=
    @gElsn x B
      (by
        aesop)
  have p0004 :=
    @gOrbi12i (.classMem (.cv x) (synCsn A)) (.classEq (.cv x) A)
      (.classMem (.cv x) (synCsn B)) (.classEq (.cv x) B) p0002 p0003
  have p0005 :=
    @gBitri (.classMem (.cv x) (synCun (synCsn A) (synCsn B)))
      (synWo (.classMem (.cv x) (synCsn A)) (.classMem (.cv x) (synCsn B)))
      (synWo (.classEq (.cv x) A) (.classEq (.cv x) B)) p0001 p0004
  have p0006 :=
    @gEqabi (synWo (.classEq (.cv x) A) (.classEq (.cv x) B)) x
      (synCun (synCsn A) (synCsn B))
      (by
        (simp (config :=
              {
                failIfUnchanged :=
                  false }) only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cun,
              NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn,
              Finset.mem_union] at ⊢;
            aesop))
      p0005
  have p0007 :=
    @gEqtri (synCpr A B) (synCun (synCsn A) (synCsn B))
      (.cab x (synWo (.classEq (.cv x) A) (.classEq (.cv x) B))) p0000 p0006
  exact p0007

/-- Checked nominal proof certificate identified upstream as `g_elprg`. -/
@[expose]
noncomputable def gElprg (A : Class) (B : Class) (C : Class) (V : Class) :
    Nominal.NPrf
      (.imp (.classMem A V)
        (synWb (.classMem A (synCpr B C)) (synWo (.classEq A B) (.classEq A C)))) :=
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
  have p0000 := @gEqeq1 (.cv x) A B
  have p0001 := @gEqeq1 (.cv x) A C
  have p0002 :=
    @gOrbi12d (.classEq (.cv x) A) (.classEq (.cv x) B) (.classEq A B)
      (.classEq (.cv x) C) (.classEq A C) p0000 p0001
  have p0003 :=
    @gDfpr2 x B C
      (by
        aesop)
      (by
        aesop)
  have p0004 :=
    @gElab2g (synWo (.classEq (.cv x) B) (.classEq (.cv x) C))
      (synWo (.classEq A B) (.classEq A C)) x A (synCpr B C) V
      (by
        aesop)
      (by
        (simp (config :=
              {
                failIfUnchanged :=
                  false }) only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wo,
              NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, Finset.mem_union] at ⊢;
            aesop))
      p0002 p0003
  exact p0004

/-- Checked nominal proof certificate identified upstream as `g_elpr`. -/
@[expose]
noncomputable def gElpr (A : Class) (B : Class) (C : Class)
    (hyp_elpr_1 : Nominal.NPrf (.classMem A (synCvv))) :
    Nominal.NPrf
      (synWb (.classMem A (synCpr B C)) (synWo (.classEq A B) (.classEq A C))) :=
  by
  have p0000 := @gElprg A B C (synCvv)
  have p0001 := Nominal.mp hyp_elpr_1 p0000
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_elpr2`. -/
@[expose]
noncomputable def gElpr2 (A : Class) (B : Class) (C : Class)
    (hyp_elpr2_1 : Nominal.NPrf (.classMem B (synCvv)))
    (hyp_elpr2_2 : Nominal.NPrf (.classMem C (synCvv))) :
    Nominal.NPrf
      (synWb (.classMem A (synCpr B C)) (synWo (.classEq A B) (.classEq A C))) :=
  by
  have p0000 := @gElprg A B C (synCpr B C)
  have p0001 :=
    @gIbi (.classMem A (synCpr B C)) (synWo (.classEq A B) (.classEq A C)) p0000
  have p0002 := @gEleq1 A B (synCvv)
  have p0003 :=
    @gMpbiri (.classEq A B) (.classMem A (synCvv)) (.classMem B (synCvv)) hyp_elpr2_1
      p0002
  have p0004 := @gEleq1 A C (synCvv)
  have p0005 :=
    @gMpbiri (.classEq A C) (.classMem A (synCvv)) (.classMem C (synCvv)) hyp_elpr2_2
      p0004
  have p0006 := @gJaoi (.classEq A B) (.classMem A (synCvv)) (.classEq A C) p0003 p0005
  have p0007 := @gElprg A B C (synCvv)
  have p0008 :=
    @gSyl (synWo (.classEq A B) (.classEq A C)) (.classMem A (synCvv))
      (synWb (.classMem A (synCpr B C)) (synWo (.classEq A B) (.classEq A C))) p0006
      p0007
  have p0009 :=
    @gIbir (synWo (.classEq A B) (.classEq A C)) (.classMem A (synCpr B C)) p0008
  have p0010 :=
    @gImpbii (.classMem A (synCpr B C)) (synWo (.classEq A B) (.classEq A C)) p0001
      p0009
  exact p0010

/-- Checked nominal proof certificate identified upstream as `g_elsncg`. -/
@[expose]
noncomputable def gElsncg (A : Class) (B : Class) (V : Class) :
    Nominal.NPrf
      (.imp (.classMem A V) (synWb (.classMem A (synCsn B)) (.classEq A B))) :=
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
  have p0000 := @gEqeq1 (.cv x) A B
  have p0001 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominalDfSn x B
      (by
        aesop)
  have p0002 :=
    @gElab2g (.classEq (.cv x) B) (.classEq A B) x A (synCsn B) V
      (by
        aesop)
      (by
        (simp (config :=
              {
                failIfUnchanged :=
                  false }) only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
              Finset.mem_union] at ⊢;
            aesop))
      p0000 p0001
  exact p0002

/-- Checked nominal proof certificate identified upstream as `g_elsnc`. -/
@[expose]
noncomputable def gElsnc (A : Class) (B : Class)
    (hyp_elsnc_1 : Nominal.NPrf (.classMem A (synCvv))) :
    Nominal.NPrf (synWb (.classMem A (synCsn B)) (.classEq A B)) :=
  by
  have p0000 := @gElsncg A B (synCvv)
  have p0001 := Nominal.mp hyp_elsnc_1 p0000
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_elsni`. -/
@[expose]
noncomputable def gElsni (A : Class) (B : Class) :
    Nominal.NPrf (.imp (.classMem A (synCsn B)) (.classEq A B)) :=
  by
  have p0000 := @gElsncg A B (synCsn B)
  have p0001 := @gIbi (.classMem A (synCsn B)) (.classEq A B) p0000
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_snidg`. -/
@[expose]
noncomputable def gSnidg (A : Class) (V : Class) :
    Nominal.NPrf (.imp (.classMem A V) (.classMem A (synCsn A))) :=
  by
  have p0000 := @gEqid A
  have p0001 := @gElsncg A A V
  have p0002 :=
    @gMpbiri (.classMem A V) (.classMem A (synCsn A)) (.classEq A A) p0000 p0001
  exact p0002

/-- Checked nominal proof certificate identified upstream as `g_snidb`. -/
@[expose]
noncomputable def gSnidb (A : Class) :
    Nominal.NPrf (synWb (.classMem A (synCvv)) (.classMem A (synCsn A))) :=
  by
  have p0000 := @gSnidg A (synCvv)
  have p0001 := @gElex A (synCsn A)
  have p0002 := @gImpbii (.classMem A (synCvv)) (.classMem A (synCsn A)) p0000 p0001
  exact p0002

/-- Checked nominal proof certificate identified upstream as `g_snid`. -/
@[expose]
noncomputable def gSnid (A : Class) (hyp_snid_1 : Nominal.NPrf (.classMem A (synCvv))) :
    Nominal.NPrf (.classMem A (synCsn A)) :=
  by
  have p0000 := @gSnidb A
  have p0001 := @gMpbi (.classMem A (synCvv)) (.classMem A (synCsn A)) hyp_snid_1 p0000
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_elsnc2g`. -/
@[expose]
noncomputable def gElsnc2g (A : Class) (B : Class) (V : Class) :
    Nominal.NPrf
      (.imp (.classMem B V) (synWb (.classMem A (synCsn B)) (.classEq A B))) :=
  by
  have p0000 := @gElsni A B
  have p0001 := @gSnidg B V
  have p0002 := @gEleq1 A B (synCsn B)
  have p0003 :=
    @gSyl5ibrcom (.classMem B V) (.classMem A (synCsn B)) (.classEq A B)
      (.classMem B (synCsn B)) p0001 p0002
  have p0004 :=
    @gImpbid2 (.classMem B V) (.classMem A (synCsn B)) (.classEq A B) p0000 p0003
  exact p0004

/-- Checked nominal proof certificate identified upstream as `g_elsnc2`. -/
@[expose]
noncomputable def gElsnc2 (A : Class) (B : Class)
    (hyp_elsnc2_1 : Nominal.NPrf (.classMem B (synCvv))) :
    Nominal.NPrf (synWb (.classMem A (synCsn B)) (.classEq A B)) :=
  by
  have p0000 := @gElsnc2g A B (synCvv)
  have p0001 := Nominal.mp hyp_elsnc2_1 p0000
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_rexsns`. -/
@[expose]
noncomputable def gRexsns (ph : Wff) (x : Var) (A : Class) (V : Class)
    (dv_A_x : x ∉ A.fv) :
    Nominal.NPrf
      (.imp (.classMem A V) (synWb (synWrex x (synCsn A) ph) (synWsbc A x ph))) :=
  by
  have p0000 :=
    @gSbc5 ph x A
      (by
        aesop)
  have p0001 :=
    @gA1i (synWb (synWsbc A x ph) (synWex x (synWa (.classEq (.cv x) A) ph)))
      (.classMem A V) p0000
  have p0002 := (Nominal.biimpRefl (synWrex x (synCsn A) ph))
  have p0003 :=
    @gElsn x A
      (by
        aesop)
  have p0004 := @gAnbi1i (.classMem (.cv x) (synCsn A)) (.classEq (.cv x) A) ph p0003
  have p0005 :=
    @gExbii (synWa (.classMem (.cv x) (synCsn A)) ph) (synWa (.classEq (.cv x) A) ph)
      x p0004
  have p0006 :=
    @gBitri (synWrex x (synCsn A) ph)
      (synWex x (synWa (.classMem (.cv x) (synCsn A)) ph))
      (synWex x (synWa (.classEq (.cv x) A) ph)) p0002 p0005
  have p0007 :=
    @gSyl6rbbr (.classMem A V) (synWsbc A x ph)
      (synWex x (synWa (.classEq (.cv x) A) ph)) (synWrex x (synCsn A) ph) p0001 p0006
  exact p0007

/-- Checked nominal proof certificate identified upstream as `g_rexsng`. -/
@[expose]
noncomputable def gRexsng (ph : Wff) (ps : Wff) (x : Var) (A : Class) (V : Class)
    (dv_A_x : x ∉ A.fv) (dv_ps_x : x ∉ ps.fv)
    (hyp_ralsng_1 : Nominal.NPrf (.imp (.classEq (.cv x) A) (synWb ph ps))) :
    Nominal.NPrf (.imp (.classMem A V) (synWb (synWrex x (synCsn A) ph) ps)) :=
  by
  have p0000 :=
    @gRexsns ph x A V
      (by
        aesop)
  have p0001 :=
    @gSbcieg ph ps x A V
      (by
        aesop)
      (by
        aesop)
      hyp_ralsng_1
  have p0002 :=
    @gBitrd (.classMem A V) (synWrex x (synCsn A) ph) (synWsbc A x ph) ps p0000 p0001
  exact p0002

/-- Checked nominal proof certificate identified upstream as `g_rexsn`. -/
@[expose]
noncomputable def gRexsn (ph : Wff) (ps : Wff) (x : Var) (A : Class) (dv_A_x : x ∉ A.fv)
    (dv_ps_x : x ∉ ps.fv) (hyp_ralsn_1 : Nominal.NPrf (.classMem A (synCvv)))
    (hyp_ralsn_2 : Nominal.NPrf (.imp (.classEq (.cv x) A) (synWb ph ps))) :
    Nominal.NPrf (synWb (synWrex x (synCsn A) ph) ps) :=
  by
  have p0000 :=
    @gRexsng ph ps x A (synCvv)
      (by
        aesop)
      (by
        aesop)
      hyp_ralsn_2
  have p0001 := Nominal.mp hyp_ralsn_1 p0000
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_disjsn`. -/
@[expose]
noncomputable def gDisjsn (A : Class) (B : Class) :
    Nominal.NPrf
      (synWb (.classEq (synCin A (synCsn B)) (synC0)) (.neg (.classMem B A))) :=
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
    @gDisj1 x A (synCsn B)
      (by
        aesop)
      (by
        (simp (config :=
              {
                failIfUnchanged :=
                  false }) only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn] at ⊢;
            aesop))
  have p0001 := @gCon2b (.classMem (.cv x) A) (.classMem (.cv x) (synCsn B))
  have p0002 :=
    @gElsn x B
      (by
        aesop)
  have p0003 :=
    @gImbi1i (.classMem (.cv x) (synCsn B)) (.classEq (.cv x) B)
      (.neg (.classMem (.cv x) A)) p0002
  have p0004 := @gImnan (.classEq (.cv x) B) (.classMem (.cv x) A)
  have p0005 :=
    @gN3bitri (.imp (.classMem (.cv x) A) (.neg (.classMem (.cv x) (synCsn B))))
      (.imp (.classMem (.cv x) (synCsn B)) (.neg (.classMem (.cv x) A)))
      (.imp (.classEq (.cv x) B) (.neg (.classMem (.cv x) A)))
      (.neg (synWa (.classEq (.cv x) B) (.classMem (.cv x) A))) p0001 p0003 p0004
  have p0006 :=
    @gAlbii (.imp (.classMem (.cv x) A) (.neg (.classMem (.cv x) (synCsn B))))
      (.neg (synWa (.classEq (.cv x) B) (.classMem (.cv x) A))) x p0005
  have p0007 := @gAlnex (synWa (.classEq (.cv x) B) (.classMem (.cv x) A)) x
  have p0008 :=
    (NFChoice.DirectNominalPrf.Nominal.DefinitionLeafHandlersCanonical001.dfClelOfDV x B A (by
        aesop) (by
        aesop))
  have p0009 :=
    @gXchbinxr (.all x (.neg (synWa (.classEq (.cv x) B) (.classMem (.cv x) A))))
      (synWex x (synWa (.classEq (.cv x) B) (.classMem (.cv x) A))) (.classMem B A)
      p0007 p0008
  have p0010 :=
    @gN3bitri (.classEq (synCin A (synCsn B)) (synC0))
      (.all x (.imp (.classMem (.cv x) A) (.neg (.classMem (.cv x) (synCsn B)))))
      (.all x (.neg (synWa (.classEq (.cv x) B) (.classMem (.cv x) A))))
      (.neg (.classMem B A)) p0000 p0006 p0009
  exact p0010

/-- Checked nominal proof certificate identified upstream as `g_snprc`. -/
@[expose]
noncomputable def gSnprc (A : Class) :
    Nominal.NPrf
      (synWb (.neg (.classMem A (synCvv))) (.classEq (synCsn A) (synC0))) :=
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
    @gElsn x A
      (by
        aesop)
  have p0001 := @gExbii (.classMem (.cv x) (synCsn A)) (.classEq (.cv x) A) x p0000
  have p0002 :=
    @gNeq0 x (synCsn A)
      (by
        (simp (config :=
              {
                failIfUnchanged :=
                  false }) only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn] at ⊢;
            aesop))
  have p0003 :=
    @gIsset x A
      (by
        aesop)
  have p0004 :=
    @gN3bitr4i (synWex x (.classMem (.cv x) (synCsn A)))
      (synWex x (.classEq (.cv x) A)) (.neg (.classEq (synCsn A) (synC0)))
      (.classMem A (synCvv)) p0001 p0002 p0003
  have p0005 := @gCon1bii (.classEq (synCsn A) (synC0)) (.classMem A (synCvv)) p0004
  exact p0005

/-- Checked nominal proof certificate identified upstream as `g_rabsn`. -/
@[expose]
noncomputable def gRabsn (x : Var) (A : Class) (B : Class) (dv_A_x : x ∉ A.fv)
    (dv_B_x : x ∉ B.fv) :
    Nominal.NPrf
      (.imp (.classMem B A) (.classEq (synCrab x A (.classEq (.cv x) B)) (synCsn B))) :=
  by
  have p0000 := @gEleq1 (.cv x) B A
  have p0001 :=
    @gPm532ri (.classEq (.cv x) B) (.classMem (.cv x) A) (.classMem B A) p0000
  have p0002 :=
    @gBaib (synWa (.classMem (.cv x) A) (.classEq (.cv x) B)) (.classMem B A)
      (.classEq (.cv x) B) p0001
  have p0003 :=
    @gAbbidv (.classMem B A) (synWa (.classMem (.cv x) A) (.classEq (.cv x) B))
      (.classEq (.cv x) B) x
      (by
        (simp (config :=
              {
                failIfUnchanged :=
                  false }) only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
              Finset.mem_union] at ⊢;
            aesop))
      p0002
  have p0004 := (Nominal.classEqRefl (synCrab x A (.classEq (.cv x) B)))
  have p0005 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominalDfSn x B
      (by
        aesop)
  have p0006 :=
    @gN3eqtr4g (.classMem B A)
      (.cab x (synWa (.classMem (.cv x) A) (.classEq (.cv x) B)))
      (.cab x (.classEq (.cv x) B)) (synCrab x A (.classEq (.cv x) B)) (synCsn B) p0003
      p0004 p0005
  exact p0006

/-- Checked nominal proof certificate identified upstream as `g_prcom`. -/
@[expose]
noncomputable def gPrcom (A : Class) (B : Class) :
    Nominal.NPrf (.classEq (synCpr A B) (synCpr B A)) :=
  by
  have p0000 := @gUncom (synCsn A) (synCsn B)
  have p0001 := (Nominal.classEqRefl (synCpr A B))
  have p0002 := (Nominal.classEqRefl (synCpr B A))
  have p0003 :=
    @gN3eqtr4i (synCun (synCsn A) (synCsn B)) (synCun (synCsn B) (synCsn A))
      (synCpr A B) (synCpr B A) p0000 p0001 p0002
  exact p0003

/-- Checked nominal proof certificate identified upstream as `g_preq1`. -/
@[expose]
noncomputable def gPreq1 (A : Class) (B : Class) (C : Class) :
    Nominal.NPrf (.imp (.classEq A B) (.classEq (synCpr A C) (synCpr B C))) :=
  by
  have p0000 := @gSneq A B
  have p0001 := @gUneq1d (.classEq A B) (synCsn A) (synCsn B) (synCsn C) p0000
  have p0002 := (Nominal.classEqRefl (synCpr A C))
  have p0003 := (Nominal.classEqRefl (synCpr B C))
  have p0004 :=
    @gN3eqtr4g (.classEq A B) (synCun (synCsn A) (synCsn C))
      (synCun (synCsn B) (synCsn C)) (synCpr A C) (synCpr B C) p0001 p0002 p0003
  exact p0004

/-- Checked nominal proof certificate identified upstream as `g_preq2`. -/
@[expose]
noncomputable def gPreq2 (A : Class) (B : Class) (C : Class) :
    Nominal.NPrf (.imp (.classEq A B) (.classEq (synCpr C A) (synCpr C B))) :=
  by
  have p0000 := @gPreq1 A B C
  have p0001 := @gPrcom C A
  have p0002 := @gPrcom C B
  have p0003 :=
    @gN3eqtr4g (.classEq A B) (synCpr A C) (synCpr B C) (synCpr C A) (synCpr C B)
      p0000 p0001 p0002
  exact p0003

/-- Checked nominal proof certificate identified upstream as `g_preq12`. -/
@[expose]
noncomputable def gPreq12 (A : Class) (B : Class) (C : Class) (D : Class) :
    Nominal.NPrf
      (.imp (synWa (.classEq A C) (.classEq B D)) (.classEq (synCpr A B) (synCpr C D))) :=
  by
  have p0000 := @gPreq1 A C B
  have p0001 := @gPreq2 B D C
  have p0002 :=
    @gSylan9eq (.classEq A C) (.classEq B D) (synCpr A B) (synCpr C B) (synCpr C D)
      p0000 p0001
  exact p0002

/-- Checked nominal proof certificate identified upstream as `g_preq2d`. -/
@[expose]
noncomputable def gPreq2d (ph : Wff) (A : Class) (B : Class) (C : Class)
    (hyp_preq1d_1 : Nominal.NPrf (.imp ph (.classEq A B))) :
    Nominal.NPrf (.imp ph (.classEq (synCpr C A) (synCpr C B))) :=
  by
  have p0000 := @gPreq2 A B C
  have p0001 :=
    @gSyl ph (.classEq A B) (.classEq (synCpr C A) (synCpr C B)) hyp_preq1d_1 p0000
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_preq12d`. -/
@[expose]
noncomputable def gPreq12d (ph : Wff) (A : Class) (B : Class) (C : Class) (D : Class)
    (hyp_preq1d_1 : Nominal.NPrf (.imp ph (.classEq A B)))
    (hyp_preq12d_2 : Nominal.NPrf (.imp ph (.classEq C D))) :
    Nominal.NPrf (.imp ph (.classEq (synCpr A C) (synCpr B D))) :=
  by
  have p0000 := @gPreq12 A C B D
  have p0001 :=
    @gSyl2anc ph (.classEq A B) (.classEq C D) (.classEq (synCpr A C) (synCpr B D))
      hyp_preq1d_1 hyp_preq12d_2 p0000
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_prid1g`. -/
@[expose]
noncomputable def gPrid1g (A : Class) (B : Class) (V : Class) :
    Nominal.NPrf (.imp (.classMem A V) (.classMem A (synCpr A B))) :=
  by
  have p0000 := @gEqid A
  have p0001 := @gOrci (.classEq A A) (.classEq A B) p0000
  have p0002 := @gElprg A A B V
  have p0003 :=
    @gMpbiri (.classMem A V) (.classMem A (synCpr A B))
      (synWo (.classEq A A) (.classEq A B)) p0001 p0002
  exact p0003

/-- Checked nominal proof certificate identified upstream as `g_prid1`. -/
@[expose]
noncomputable def gPrid1 (A : Class) (B : Class)
    (hyp_prid1_1 : Nominal.NPrf (.classMem A (synCvv))) :
    Nominal.NPrf (.classMem A (synCpr A B)) :=
  by
  have p0000 := @gPrid1g A B (synCvv)
  have p0001 := Nominal.mp hyp_prid1_1 p0000
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_snnzg`. -/
@[expose]
noncomputable def gSnnzg (A : Class) (V : Class) :
    Nominal.NPrf (.imp (.classMem A V) (synWne (synCsn A) (synC0))) :=
  by
  have p0000 := @gSnidg A V
  have p0001 := @gNe0i (synCsn A) A
  have p0002 :=
    @gSyl (.classMem A V) (.classMem A (synCsn A)) (synWne (synCsn A) (synC0)) p0000
      p0001
  exact p0002

/-- Checked nominal proof certificate identified upstream as `g_snnz`. -/
@[expose]
noncomputable def gSnnz (A : Class) (hyp_snnz_1 : Nominal.NPrf (.classMem A (synCvv))) :
    Nominal.NPrf (synWne (synCsn A) (synC0)) :=
  by
  have p0000 := @gSnnzg A (synCvv)
  have p0001 := Nominal.mp hyp_snnz_1 p0000
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_snss`. -/
@[expose]
noncomputable def gSnss (A : Class) (B : Class)
    (hyp_snss_1 : Nominal.NPrf (.classMem A (synCvv))) :
    Nominal.NPrf (synWb (.classMem A B) (synWss (synCsn A) B)) :=
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
    @gElsn x A
      (by
        aesop)
  have p0001 :=
    @gImbi1i (.classMem (.cv x) (synCsn A)) (.classEq (.cv x) A) (.classMem (.cv x) B)
      p0000
  have p0002 :=
    @gAlbii (.imp (.classMem (.cv x) (synCsn A)) (.classMem (.cv x) B))
      (.imp (.classEq (.cv x) A) (.classMem (.cv x) B)) x p0001
  have p0003 :=
    @gDfss2 x (synCsn A) B
      (by
        (simp (config :=
              {
                failIfUnchanged :=
                  false }) only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn] at ⊢;
            aesop))
      (by
        aesop)
  have p0004 :=
    @gClel2 x A B
      (by
        aesop)
      (by
        aesop)
      hyp_snss_1
  have p0005 :=
    @gN3bitr4ri (.all x (.imp (.classMem (.cv x) (synCsn A)) (.classMem (.cv x) B)))
      (.all x (.imp (.classEq (.cv x) A) (.classMem (.cv x) B))) (synWss (synCsn A) B)
      (.classMem A B) p0002 p0003 p0004
  exact p0005

/-- Checked nominal proof certificate identified upstream as `g_eldifsn`. -/
@[expose]
noncomputable def gEldifsn (A : Class) (B : Class) (C : Class) :
    Nominal.NPrf
      (synWb (.classMem A (synCdif B (synCsn C))) (synWa (.classMem A B) (synWne A C))) :=
  by
  have p0000 := @gEldif A B (synCsn C)
  have p0001 := @gElsncg A C B
  have p0002 := @gNecon3bbid (.classMem A B) (.classMem A (synCsn C)) A C p0001
  have p0003 :=
    @gPm532i (.classMem A B) (.neg (.classMem A (synCsn C))) (synWne A C) p0002
  have p0004 :=
    @gBitri (.classMem A (synCdif B (synCsn C)))
      (synWa (.classMem A B) (.neg (.classMem A (synCsn C))))
      (synWa (.classMem A B) (synWne A C)) p0000 p0003
  exact p0004

/-- Checked nominal proof certificate identified upstream as `g_eldifsni`. -/
@[expose]
noncomputable def gEldifsni (A : Class) (B : Class) (C : Class) :
    Nominal.NPrf (.imp (.classMem A (synCdif B (synCsn C))) (synWne A C)) :=
  by
  have p0000 := @gEldifsn A B C
  have p0001 :=
    @gSimprbi (.classMem A (synCdif B (synCsn C))) (.classMem A B) (synWne A C) p0000
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_neldifsn`. -/
@[expose]
noncomputable def gNeldifsn (A : Class) (B : Class) :
    Nominal.NPrf (.neg (.classMem A (synCdif B (synCsn A)))) :=
  by
  have p0000 := @gNeirr A
  have p0001 := @gEldifsni A B A
  have p0002 := @gMto (.classMem A (synCdif B (synCsn A))) (synWne A A) p0000 p0001
  exact p0002

/-- Checked nominal proof certificate identified upstream as `g_snssg`. -/
@[expose]
noncomputable def gSnssg (A : Class) (B : Class) (V : Class) :
    Nominal.NPrf
      (.imp (.classMem A V) (synWb (.classMem A B) (synWss (synCsn A) B))) :=
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
  have p0000 := @gEleq1 (.cv x) A B
  have p0001 := @gSneq (.cv x) A
  have p0002 := @gSseq1d (.classEq (.cv x) A) (synCsn (.cv x)) (synCsn A) B p0001
  have p0003 := @gVex x
  have p0004 := @gSnss (.cv x) B p0003
  have p0005 :=
    @gVtoclbg (.classMem (.cv x) B) (synWss (synCsn (.cv x)) B) (.classMem A B)
      (synWss (synCsn A) B) x A V
      (by
        aesop)
      (by
        (simp (config :=
              {
                failIfUnchanged :=
                  false }) only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
              Finset.mem_union] at ⊢;
            aesop))
      (by
        (simp (config :=
              {
                failIfUnchanged :=
                  false }) only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wss,
              NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn,
              Finset.mem_union] at ⊢;
            aesop))
      p0000 p0002 p0004
  exact p0005

/-- Checked nominal proof certificate identified upstream as `g_difsn`. -/
@[expose]
noncomputable def gDifsn (A : Class) (B : Class) :
    Nominal.NPrf (.imp (.neg (.classMem A B)) (.classEq (synCdif B (synCsn A)) B)) :=
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
  have p0000 := @gEldifsn (.cv x) B A
  have p0001 := @gSimpl (.classMem (.cv x) B) (synWne (.cv x) A)
  have p0002 := @gEleq1 (.cv x) A B
  have p0003 :=
    @gBiimpcd (.classEq (.cv x) A) (.classMem (.cv x) B) (.classMem A B) p0002
  have p0004 := @gNecon3bd (.classMem (.cv x) B) (.classMem A B) (.cv x) A p0003
  have p0005 :=
    @gCom12 (.classMem (.cv x) B) (.neg (.classMem A B)) (synWne (.cv x) A) p0004
  have p0006 :=
    @gAncld (.neg (.classMem A B)) (.classMem (.cv x) B) (synWne (.cv x) A) p0005
  have p0007 :=
    @gImpbid2 (.neg (.classMem A B)) (synWa (.classMem (.cv x) B) (synWne (.cv x) A))
      (.classMem (.cv x) B) p0001 p0006
  have p0008 :=
    @gSyl5bb (.classMem (.cv x) (synCdif B (synCsn A)))
      (synWa (.classMem (.cv x) B) (synWne (.cv x) A)) (.neg (.classMem A B))
      (.classMem (.cv x) B) p0000 p0007
  have p0009 :=
    @gEqrdv (.neg (.classMem A B)) x (synCdif B (synCsn A)) B
      (by
        (simp (config :=
              {
                failIfUnchanged :=
                  false }) only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdif,
              NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn,
              Finset.mem_union] at ⊢;
            aesop))
      (by
        aesop)
      (by
        (simp (config :=
              { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_wff_neg,
              NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, Finset.mem_union] at ⊢;
            aesop))
      p0008
  exact p0009

/-- Checked nominal proof certificate identified upstream as `g_snssi`. -/
@[expose]
noncomputable def gSnssi (A : Class) (B : Class) :
    Nominal.NPrf (.imp (.classMem A B) (synWss (synCsn A) B)) :=
  by
  have p0000 := @gSnssg A B B
  have p0001 := @gIbi (.classMem A B) (synWss (synCsn A) B) p0000
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_snssd`. -/
@[expose]
noncomputable def gSnssd (ph : Wff) (A : Class) (B : Class)
    (hyp_snssd_1 : Nominal.NPrf (.imp ph (.classMem A B))) :
    Nominal.NPrf (.imp ph (synWss (synCsn A) B)) :=
  by
  have p0000 := @gSnssg A B B
  have p0001 :=
    @gSyl ph (.classMem A B) (synWb (.classMem A B) (synWss (synCsn A) B)) hyp_snssd_1
      p0000
  have p0002 := @gMpbid ph (.classMem A B) (synWss (synCsn A) B) hyp_snssd_1 p0001
  exact p0002

/-- Checked nominal proof certificate identified upstream as `g_difsnid`. -/
@[expose]
noncomputable def gDifsnid (A : Class) (B : Class) :
    Nominal.NPrf
      (.imp (.classMem B A) (.classEq (synCun (synCdif A (synCsn B)) (synCsn B)) A)) :=
  by
  have p0000 := @gUncom (synCdif A (synCsn B)) (synCsn B)
  have p0001 := @gSnssi B A
  have p0002 := @gUndif (synCsn B) A
  have p0003 :=
    @gSylib (.classMem B A) (synWss (synCsn B) A)
      (.classEq (synCun (synCsn B) (synCdif A (synCsn B))) A) p0001 p0002
  have p0004 :=
    @gSyl5eq (.classMem B A) (synCun (synCdif A (synCsn B)) (synCsn B))
      (synCun (synCsn B) (synCdif A (synCsn B))) A p0000 p0003
  exact p0004

/-- Checked nominal proof certificate identified upstream as `g_sssn`. -/
@[expose]
noncomputable def gSssn (A : Class) (B : Class) :
    Nominal.NPrf
      (synWb (synWss A (synCsn B))
        (synWo (.classEq A (synC0)) (.classEq A (synCsn B)))) :=
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
    @gNeq0 x A
      (by
        aesop)
  have p0001 := @gSsel A (synCsn B) (.cv x)
  have p0002 := @gElsni (.cv x) B
  have p0003 :=
    @gSyl6 (synWss A (synCsn B)) (.classMem (.cv x) A) (.classMem (.cv x) (synCsn B))
      (.classEq (.cv x) B) p0001 p0002
  have p0004 := @gEleq1 (.cv x) B A
  have p0005 :=
    @gSyl6 (synWss A (synCsn B)) (.classMem (.cv x) A) (.classEq (.cv x) B)
      (synWb (.classMem (.cv x) A) (.classMem B A)) p0003 p0004
  have p0006 := @gIbd (synWss A (synCsn B)) (.classMem (.cv x) A) (.classMem B A) p0005
  have p0007 :=
    @gExlimdv (synWss A (synCsn B)) (.classMem (.cv x) A) (.classMem B A) x
      (by
        (simp (config :=
              {
                failIfUnchanged :=
                  false }) only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
              Finset.mem_union] at ⊢;
            aesop))
      (by
        (simp (config :=
              {
                failIfUnchanged :=
                  false }) only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wss,
              NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn,
              Finset.mem_union] at ⊢;
            aesop))
      p0006
  have p0008 :=
    @gSyl5bi (.neg (.classEq A (synC0))) (synWex x (.classMem (.cv x) A))
      (synWss A (synCsn B)) (.classMem B A) p0000 p0007
  have p0009 := @gSnssi B A
  have p0010 :=
    @gSyl6 (synWss A (synCsn B)) (.neg (.classEq A (synC0))) (.classMem B A)
      (synWss (synCsn B) A) p0008 p0009
  have p0011 :=
    @gAnc2li (synWss A (synCsn B)) (.neg (.classEq A (synC0))) (synWss (synCsn B) A)
      p0010
  have p0012 := @gEqss A (synCsn B)
  have p0013 :=
    @gSyl6ibr (synWss A (synCsn B)) (.neg (.classEq A (synC0)))
      (synWa (synWss A (synCsn B)) (synWss (synCsn B) A)) (.classEq A (synCsn B))
      p0011 p0012
  have p0014 :=
    @gOrrd (synWss A (synCsn B)) (.classEq A (synC0)) (.classEq A (synCsn B)) p0013
  have p0015 := @gN0ss (synCsn B)
  have p0016 := @gSseq1 A (synC0) (synCsn B)
  have p0017 :=
    @gMpbiri (.classEq A (synC0)) (synWss A (synCsn B)) (synWss (synC0) (synCsn B))
      p0015 p0016
  have p0018 := @gEqimss A (synCsn B)
  have p0019 :=
    @gJaoi (.classEq A (synC0)) (synWss A (synCsn B)) (.classEq A (synCsn B)) p0017
      p0018
  have p0020 :=
    @gImpbii (synWss A (synCsn B))
      (synWo (.classEq A (synC0)) (.classEq A (synCsn B))) p0014 p0019
  exact p0020

/-- Checked nominal proof certificate identified upstream as `g_sneqr`. -/
@[expose]
noncomputable def gSneqr (A : Class) (B : Class)
    (hyp_sneqr_1 : Nominal.NPrf (.classMem A (synCvv))) :
    Nominal.NPrf (.imp (.classEq (synCsn A) (synCsn B)) (.classEq A B)) :=
  by
  have p0000 := @gSnid A hyp_sneqr_1
  have p0001 := @gEleq2 (synCsn A) (synCsn B) A
  have p0002 :=
    @gMpbii (.classEq (synCsn A) (synCsn B)) (.classMem A (synCsn A))
      (.classMem A (synCsn B)) p0000 p0001
  have p0003 := @gElsnc A B hyp_sneqr_1
  have p0004 :=
    @gSylib (.classEq (synCsn A) (synCsn B)) (.classMem A (synCsn B)) (.classEq A B)
      p0002 p0003
  exact p0004

/-- Checked nominal proof certificate identified upstream as `g_sneqrg`. -/
@[expose]
noncomputable def gSneqrg (A : Class) (B : Class) (V : Class) :
    Nominal.NPrf
      (.imp (.classMem A V) (.imp (.classEq (synCsn A) (synCsn B)) (.classEq A B))) :=
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
  have p0000 := @gSneq (.cv x) A
  have p0001 :=
    @gEqeq1d (.classEq (.cv x) A) (synCsn (.cv x)) (synCsn A) (synCsn B) p0000
  have p0002 := @gEqeq1 (.cv x) A B
  have p0003 :=
    @gImbi12d (.classEq (.cv x) A) (.classEq (synCsn (.cv x)) (synCsn B))
      (.classEq (synCsn A) (synCsn B)) (.classEq (.cv x) B) (.classEq A B) p0001 p0002
  have p0004 := @gVex x
  have p0005 := @gSneqr (.cv x) B p0004
  have p0006 :=
    @gVtoclg (.imp (.classEq (synCsn (.cv x)) (synCsn B)) (.classEq (.cv x) B))
      (.imp (.classEq (synCsn A) (synCsn B)) (.classEq A B)) x A V
      (by
        aesop)
      (by
        (simp (config :=
              { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp,
              NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
              NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn,
              Finset.mem_union] at ⊢;
            aesop))
      p0003 p0005
  exact p0006

/-- Checked nominal proof certificate identified upstream as `g_sneqbg`. -/
@[expose]
noncomputable def gSneqbg (A : Class) (B : Class) (V : Class) :
    Nominal.NPrf
      (.imp (.classMem A V) (synWb (.classEq (synCsn A) (synCsn B)) (.classEq A B))) :=
  by
  have p0000 := @gSneqrg A B V
  have p0001 := @gSneq A B
  have p0002 :=
    @gImpbid1 (.classMem A V) (.classEq (synCsn A) (synCsn B)) (.classEq A B) p0000
      p0001
  exact p0002

/-- Checked nominal proof certificate identified upstream as `g_sneqb`. -/
@[expose]
noncomputable def gSneqb (A : Class) (B : Class)
    (hyp_sneqb_1 : Nominal.NPrf (.classMem A (synCvv))) :
    Nominal.NPrf (synWb (.classEq (synCsn A) (synCsn B)) (.classEq A B)) :=
  by
  have p0000 := @gSneqbg A B (synCvv)
  have p0001 := Nominal.mp hyp_sneqb_1 p0000
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_pwv`. -/
@[expose]
noncomputable def gPwv : Nominal.NPrf (.classEq (synCpw (synCvv)) (synCvv)) :=
  by
  let proofSupport : Finset Var := (∅ : Finset Var)
  let x : Var := freshVar proofSupport 0
  have fresh_x : x ∉ proofSupport :=
    by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have p0000 := @gSsv (.cv x)
  have p0001 := @gVex x
  have p0002 := @gElpw (.cv x) (synCvv) p0001
  have p0003 :=
    @gMpbir (.classMem (.cv x) (synCpw (synCvv))) (synWss (.cv x) (synCvv)) p0000
      p0002
  have p0004 :=
    @gN2th (.classMem (.cv x) (synCpw (synCvv))) (.classMem (.cv x) (synCvv)) p0003
      p0001
  have p0005 :=
    @gEqriv x (synCpw (synCvv)) (synCvv)
      (by
        (simp (config :=
              {
                failIfUnchanged :=
                  false }) only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw,
              NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv] at ⊢;
            aesop))
      (by
        (simp (config :=
              {
                failIfUnchanged :=
                  false }) only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv] at ⊢;
            aesop))
      p0004
  exact p0005

/-- Checked nominal proof certificate identified upstream as `g_unsneqsn`. -/
@[expose]
noncomputable def gUnsneqsn (A : Class) (B : Class) (C : Class)
    (hyp_unsneqsn_1 : Nominal.NPrf (.classMem B (synCvv))) :
    Nominal.NPrf
      (.imp (.classEq (synCun A (synCsn B)) (synCsn C))
        (synWo (.classEq A (synC0)) (.classEq A (synCsn B)))) :=
  by
  have p0000 := @gSsun2 (synCsn B) A
  have p0001 := @gSnid B hyp_unsneqsn_1
  have p0002 := @gSselii (synCsn B) (synCun A (synCsn B)) B p0000 p0001
  have p0003 := @gEleq2 (synCun A (synCsn B)) (synCsn C) B
  have p0004 :=
    @gMpbii (.classEq (synCun A (synCsn B)) (synCsn C))
      (.classMem B (synCun A (synCsn B))) (.classMem B (synCsn C)) p0002 p0003
  have p0005 := @gElsni B C
  have p0006 :=
    @gSyl (.classEq (synCun A (synCsn B)) (synCsn C)) (.classMem B (synCsn C))
      (.classEq B C) p0004 p0005
  have p0007 := @gSneq B C
  have p0008 :=
    @gEqeq2d (.classEq B C) (synCsn B) (synCsn C) (synCun A (synCsn B)) p0007
  have p0009 :=
    @gBiimprd (.classEq B C) (.classEq (synCun A (synCsn B)) (synCsn B))
      (.classEq (synCun A (synCsn B)) (synCsn C)) p0008
  have p0010 :=
    @gMpcom (.classEq B C) (.classEq (synCun A (synCsn B)) (synCsn C))
      (.classEq (synCun A (synCsn B)) (synCsn B)) p0006 p0009
  have p0011 := @gSsequn1 A (synCsn B)
  have p0012 :=
    @gSylibr (.classEq (synCun A (synCsn B)) (synCsn C))
      (.classEq (synCun A (synCsn B)) (synCsn B)) (synWss A (synCsn B)) p0010 p0011
  have p0013 := @gSssn A B
  have p0014 :=
    @gSylib (.classEq (synCun A (synCsn B)) (synCsn C)) (synWss A (synCsn B))
      (synWo (.classEq A (synC0)) (.classEq A (synCsn B))) p0012 p0013
  exact p0014

/-- Checked nominal proof certificate identified upstream as `g_dfpss4`. -/
@[expose]
noncomputable def gDfpss4 (x : Var) (A : Class) (B : Class) (dv_A_x : x ∉ A.fv)
    (dv_B_x : x ∉ B.fv) :
    Nominal.NPrf
      (synWb (synWpss A B)
        (synWa (synWss A B) (synWrex x B (.neg (.classMem (.cv x) A))))) :=
  by
  have p0000 := @gDfpss3 A B
  have p0001 :=
    @gDfss3 x B A
      (by
        aesop)
      (by
        aesop)
  have p0002 := @gDfral2 (.classMem (.cv x) A) x B
  have p0003 :=
    @gBitr2i (synWss B A) (synWral x B (.classMem (.cv x) A))
      (.neg (synWrex x B (.neg (.classMem (.cv x) A)))) p0001 p0002
  have p0004 := @gCon1bii (synWrex x B (.neg (.classMem (.cv x) A))) (synWss B A) p0003
  have p0005 :=
    @gAnbi2i (.neg (synWss B A)) (synWrex x B (.neg (.classMem (.cv x) A)))
      (synWss A B) p0004
  have p0006 :=
    @gBitri (synWpss A B) (synWa (synWss A B) (.neg (synWss B A)))
      (synWa (synWss A B) (synWrex x B (.neg (.classMem (.cv x) A)))) p0000 p0005
  exact p0006

/-- Checked nominal proof certificate identified upstream as `g_adj11`. -/
@[expose]
noncomputable def gAdj11 (A : Class) (B : Class) (C : Class) :
    Nominal.NPrf
      (.imp (synWa (.neg (.classMem C A)) (.neg (.classMem C B)))
        (synWb (.classEq (synCun A (synCsn C)) (synCun B (synCsn C))) (.classEq A B))) :=
  by
  have p0000 := @gDifeq1 (synCun A (synCsn C)) (synCun B (synCsn C)) (synCsn C)
  have p0001 := @gDifun2 A (synCsn C)
  have p0002 := @gDifun2 B (synCsn C)
  have p0003 :=
    @gN3eqtr3g (.classEq (synCun A (synCsn C)) (synCun B (synCsn C)))
      (synCdif (synCun A (synCsn C)) (synCsn C))
      (synCdif (synCun B (synCsn C)) (synCsn C)) (synCdif A (synCsn C))
      (synCdif B (synCsn C)) p0000 p0001 p0002
  have p0004 := @gDifsn C A
  have p0005 := @gDifsn C B
  have p0006 :=
    @gEqeqan12d (.neg (.classMem C A)) (.neg (.classMem C B)) (synCdif A (synCsn C)) A
      (synCdif B (synCsn C)) B p0004 p0005
  have p0007 :=
    @gSyl5ib (.classEq (synCun A (synCsn C)) (synCun B (synCsn C)))
      (.classEq (synCdif A (synCsn C)) (synCdif B (synCsn C)))
      (synWa (.neg (.classMem C A)) (.neg (.classMem C B))) (.classEq A B) p0003 p0006
  have p0008 := @gUneq1 A B (synCsn C)
  have p0009 :=
    @gImpbid1 (synWa (.neg (.classMem C A)) (.neg (.classMem C B)))
      (.classEq (synCun A (synCsn C)) (synCun B (synCsn C))) (.classEq A B) p0007
      p0008
  exact p0009

/-- Checked nominal proof certificate identified upstream as `g_dfuni2`. -/
@[expose]
noncomputable def gDfuni2 (x : Var) (y : Var) (A : Class) (dv_A_x : x ∉ A.fv)
    (dv_A_y : y ∉ A.fv) (dv_x_y : x ≠ y) :
    Nominal.NPrf
      (.classEq (synCuni A) (.cab x (synWrex y A (.classMem (.cv x) (.cv y))))) :=
  by
  have p0000 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominalDfUni x y A
      (by
        aesop)
      (by
        aesop)
      (by
        aesop)
  have p0001 := @gExancom (.classMem (.cv x) (.cv y)) (.classMem (.cv y) A) y
  have p0002 := (Nominal.biimpRefl (synWrex y A (.classMem (.cv x) (.cv y))))
  have p0003 :=
    @gBitr4i (synWex y (synWa (.classMem (.cv x) (.cv y)) (.classMem (.cv y) A)))
      (synWex y (synWa (.classMem (.cv y) A) (.classMem (.cv x) (.cv y))))
      (synWrex y A (.classMem (.cv x) (.cv y))) p0001 p0002
  have p0004 :=
    @gAbbii (synWex y (synWa (.classMem (.cv x) (.cv y)) (.classMem (.cv y) A)))
      (synWrex y A (.classMem (.cv x) (.cv y))) x p0003
  have p0005_e00_recanon :
    Nominal.NPrf
      (.classEq (synCuni A) (.cab x
          (synWex y (synWa (.classMem (.cv x) (.cv y)) (.classMem (.cv y) A))))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold synCuni synWex synWa
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
    @gEqtri (synCuni A)
      (.cab x (synWex y (synWa (.classMem (.cv x) (.cv y)) (.classMem (.cv y) A))))
      (.cab x (synWrex y A (.classMem (.cv x) (.cv y)))) p0005_e00_recanon p0004
  exact p0005

/-- Checked nominal proof certificate identified upstream as `g_eluni`. -/
@[expose]
noncomputable def gEluni (x : Var) (A : Class) (B : Class) (dv_A_x : x ∉ A.fv)
    (dv_B_x : x ∉ B.fv) :
    Nominal.NPrf
      (synWb (.classMem A (synCuni B))
        (synWex x (synWa (.classMem A (.cv x)) (.classMem (.cv x) B)))) :=
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
  have p0000 := @gElex A (synCuni B)
  have p0001 := @gElex A (.cv x)
  have p0002 :=
    @gAdantr (.classMem A (.cv x)) (.classMem A (synCvv)) (.classMem (.cv x) B) p0001
  have p0003 :=
    @gExlimiv (synWa (.classMem A (.cv x)) (.classMem (.cv x) B))
      (.classMem A (synCvv)) x
      (by
        (simp (config :=
              {
                failIfUnchanged :=
                  false }) only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
              NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv,
              Finset.mem_union] at ⊢;
            aesop))
      p0002
  have p0004 := @gEleq1 (.cv y) A (.cv x)
  have p0005 :=
    @gAnbi1d (.classEq (.cv y) A) (.classMem (.cv y) (.cv x)) (.classMem A (.cv x))
      (.classMem (.cv x) B) p0004
  have p0006 :=
    @gExbidv (.classEq (.cv y) A)
      (synWa (.classMem (.cv y) (.cv x)) (.classMem (.cv x) B))
      (synWa (.classMem A (.cv x)) (.classMem (.cv x) B)) x
      (by
        (simp (config :=
              {
                failIfUnchanged :=
                  false }) only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
              NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
              Finset.mem_singleton] at ⊢;
            aesop))
      p0005
  have p0007 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominalDfUni y x B
      (by
        aesop)
      (by
        aesop)
      (by
        aesop)
  have p0008_e01_recanon :
    Nominal.NPrf
      (.classEq (synCuni B) (.cab y
          (synWex x (synWa (.classMem (.cv y) (.cv x)) (.classMem (.cv x) B))))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold synCuni synWex synWa
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
    @gElab2g (synWex x (synWa (.classMem (.cv y) (.cv x)) (.classMem (.cv x) B)))
      (synWex x (synWa (.classMem A (.cv x)) (.classMem (.cv x) B))) y A (synCuni B)
      (synCvv)
      (by
        aesop)
      (by
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
    @gPm521nii (.classMem A (synCuni B)) (.classMem A (synCvv))
      (synWex x (synWa (.classMem A (.cv x)) (.classMem (.cv x) B))) p0000 p0003 p0008
  exact p0009

/-- Checked nominal proof certificate identified upstream as `g_eluni2`. -/
@[expose]
noncomputable def gEluni2 (x : Var) (A : Class) (B : Class) (dv_A_x : x ∉ A.fv)
    (dv_B_x : x ∉ B.fv) :
    Nominal.NPrf
      (synWb (.classMem A (synCuni B)) (synWrex x B (.classMem A (.cv x)))) :=
  by
  have p0000 := @gExancom (.classMem A (.cv x)) (.classMem (.cv x) B) x
  have p0001 :=
    @gEluni x A B
      (by
        aesop)
      (by
        aesop)
  have p0002 := (Nominal.biimpRefl (synWrex x B (.classMem A (.cv x))))
  have p0003 :=
    @gN3bitr4i (synWex x (synWa (.classMem A (.cv x)) (.classMem (.cv x) B)))
      (synWex x (synWa (.classMem (.cv x) B) (.classMem A (.cv x))))
      (.classMem A (synCuni B)) (synWrex x B (.classMem A (.cv x))) p0000 p0001 p0002
  exact p0003

/-- Checked nominal proof certificate identified upstream as `g_elunii`. -/
@[expose]
noncomputable def gElunii (A : Class) (B : Class) (C : Class) :
    Nominal.NPrf
      (.imp (synWa (.classMem A B) (.classMem B C)) (.classMem A (synCuni C))) :=
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
  have p0000 := @gEleq2 (.cv x) B A
  have p0001 := @gEleq1 (.cv x) B C
  have p0002 :=
    @gAnbi12d (.classEq (.cv x) B) (.classMem A (.cv x)) (.classMem A B)
      (.classMem (.cv x) C) (.classMem B C) p0000 p0001
  have p0003 :=
    @gSpcegv (synWa (.classMem A (.cv x)) (.classMem (.cv x) C))
      (synWa (.classMem A B) (.classMem B C)) x B C
      (by
        aesop)
      (by
        (simp (config :=
              {
                failIfUnchanged :=
                  false }) only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
              NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, Finset.mem_union] at ⊢;
            aesop))
      p0002
  have p0004 :=
    @gAnabsi7 (.classMem A B) (.classMem B C)
      (synWex x (synWa (.classMem A (.cv x)) (.classMem (.cv x) C))) p0003
  have p0005 :=
    @gEluni x A C
      (by
        aesop)
      (by
        aesop)
  have p0006 :=
    @gSylibr (synWa (.classMem A B) (.classMem B C))
      (synWex x (synWa (.classMem A (.cv x)) (.classMem (.cv x) C)))
      (.classMem A (synCuni C)) p0004 p0005
  exact p0006

/-- Checked nominal proof certificate identified upstream as `g_nfuni`. -/
@[expose]
noncomputable def gNfuni (x : Var) (A : Class)
    (hyp_nfuni_1 : Nominal.NPrf (synWnfc x A)) :
    Nominal.NPrf (synWnfc x (synCuni A)) :=
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
    @gDfuni2 y z A
      (by
        aesop)
      (by
        aesop)
      (by
        aesop)
  have p0001 :=
    @gNfv (.classMem (.cv y) (.cv z)) x
      (by
        (simp (config :=
              {
                failIfUnchanged :=
                  false }) only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
              NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
              Finset.mem_singleton] at ⊢;
            aesop))
  have p0002 := @gNfrex (.classMem (.cv y) (.cv z)) x z A hyp_nfuni_1 p0001
  have p0003 := @gNfab (synWrex z A (.classMem (.cv y) (.cv z))) x y p0002
  have p0004 :=
    @gNfcxfr x (synCuni A) (.cab y (synWrex z A (.classMem (.cv y) (.cv z)))) p0000
      p0003
  exact p0004

/-- Checked nominal proof certificate identified upstream as `g_unieq`. -/
@[expose]
noncomputable def gUnieq (A : Class) (B : Class) :
    Nominal.NPrf (.imp (.classEq A B) (.classEq (synCuni A) (synCuni B))) :=
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
    @gRexeq (.classMem (.cv y) (.cv x)) x A B
      (by
        aesop)
      (by
        aesop)
  have p0001 :=
    @gAbbidv (.classEq A B) (synWrex x A (.classMem (.cv y) (.cv x)))
      (synWrex x B (.classMem (.cv y) (.cv x))) y
      (by
        (simp (config :=
              {
                failIfUnchanged :=
                  false }) only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
              Finset.mem_union] at ⊢;
            aesop))
      p0000
  have p0002 :=
    @gDfuni2 y x A
      (by
        aesop)
      (by
        aesop)
      (by
        aesop)
  have p0003 :=
    @gDfuni2 y x B
      (by
        aesop)
      (by
        aesop)
      (by
        aesop)
  have p0004 :=
    @gN3eqtr4g (.classEq A B) (.cab y (synWrex x A (.classMem (.cv y) (.cv x))))
      (.cab y (synWrex x B (.classMem (.cv y) (.cv x)))) (synCuni A) (synCuni B) p0001
      p0002 p0003
  exact p0004

/-- Checked nominal proof certificate identified upstream as `g_unieqi`. -/
@[expose]
noncomputable def gUnieqi (A : Class) (B : Class)
    (hyp_unieqi_1 : Nominal.NPrf (.classEq A B)) :
    Nominal.NPrf (.classEq (synCuni A) (synCuni B)) :=
  by
  have p0000 := @gUnieq A B
  have p0001 := Nominal.mp hyp_unieqi_1 p0000
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_unieqd`. -/
@[expose]
noncomputable def gUnieqd (ph : Wff) (A : Class) (B : Class)
    (hyp_unieqd_1 : Nominal.NPrf (.imp ph (.classEq A B))) :
    Nominal.NPrf (.imp ph (.classEq (synCuni A) (synCuni B))) :=
  by
  have p0000 := @gUnieq A B
  have p0001 :=
    @gSyl ph (.classEq A B) (.classEq (synCuni A) (synCuni B)) hyp_unieqd_1 p0000
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_eluniab`. -/
@[expose]
noncomputable def gEluniab (ph : Wff) (x : Var) (A : Class) (dv_A_x : x ∉ A.fv) :
    Nominal.NPrf
      (synWb (.classMem A (synCuni (.cab x ph)))
        (synWex x (synWa (.classMem A (.cv x)) ph))) :=
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
    @gEluni y A (.cab x ph)
      (by
        aesop)
      (by
        (simp (config :=
              {
                failIfUnchanged :=
                  false }) only [NFChoice.Compiler.CoreFVSimp.fv_class_cab,
              Finset.mem_erase] at ⊢;
            aesop))
  have p0001 :=
    @gNfv (.classMem A (.cv y)) x
      (by
        (simp (config :=
              {
                failIfUnchanged :=
                  false }) only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
              NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
              Finset.mem_singleton] at ⊢;
            aesop))
  have p0002 :=
    @gNfsab1 ph x y
      (by
        aesop)
  have p0003 :=
    @gNfan (.classMem A (.cv y)) (.classMem (.cv y) (.cab x ph)) x p0001 p0002
  have p0004 :=
    @gNfv (synWa (.classMem A (.cv x)) ph) y
      (by
        (simp (config :=
              {
                failIfUnchanged :=
                  false }) only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
              NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
              NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
              Finset.mem_singleton] at ⊢;
            aesop))
  have p0005 := @gEleq2 (.cv y) (.cv x) A
  have p0006 := @gEleq1 (.cv y) (.cv x) (.cab x ph)
  have p0007 := @gAbid ph x
  have p0008 :=
    @gSyl6bb (.classEq (.cv y) (.cv x)) (.classMem (.cv y) (.cab x ph))
      (.classMem (.cv x) (.cab x ph)) ph p0006 p0007
  have p0009 :=
    @gAnbi12d (.classEq (.cv y) (.cv x)) (.classMem A (.cv y)) (.classMem A (.cv x))
      (.classMem (.cv y) (.cab x ph)) ph p0005 p0008
  have p0010_e02_recanon :
    Nominal.NPrf
      (.imp (.objEq y x) (synWb (synWa (.classMem A (.cv y)) (.classMem (.cv y) (.cab x ph)))
          (synWa (.classMem A (.cv x)) ph))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold synWb synWa
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
        · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0009
  have p0010 :=
    @gCbvex (synWa (.classMem A (.cv y)) (.classMem (.cv y) (.cab x ph)))
      (synWa (.classMem A (.cv x)) ph) y x p0003 p0004 p0010_e02_recanon
  have p0011 :=
    @gBitri (.classMem A (synCuni (.cab x ph)))
      (synWex y (synWa (.classMem A (.cv y)) (.classMem (.cv y) (.cab x ph))))
      (synWex x (synWa (.classMem A (.cv x)) ph)) p0000 p0010
  exact p0011

/-- Checked nominal proof certificate identified upstream as `g_unipr`. -/
@[expose]
noncomputable def gUnipr (A : Class) (B : Class)
    (hyp_unipr_1 : Nominal.NPrf (.classMem A (synCvv)))
    (hyp_unipr_2 : Nominal.NPrf (.classMem B (synCvv))) :
    Nominal.NPrf (.classEq (synCuni (synCpr A B)) (synCun A B)) :=
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
  have p0000 := @gVex y
  have p0001 := @gElpr (.cv y) A B p0000
  have p0002 :=
    @gAnbi2i (.classMem (.cv y) (synCpr A B))
      (synWo (.classEq (.cv y) A) (.classEq (.cv y) B)) (.objMem x y) p0001
  have p0003 := @gAndi (.objMem x y) (.classEq (.cv y) A) (.classEq (.cv y) B)
  have p0004 :=
    @gBitri (synWa (.objMem x y) (.classMem (.cv y) (synCpr A B)))
      (synWa (.objMem x y) (synWo (.classEq (.cv y) A) (.classEq (.cv y) B)))
      (synWo (synWa (.objMem x y) (.classEq (.cv y) A))
        (synWa (.objMem x y) (.classEq (.cv y) B)))
      p0002 p0003
  have p0005 :=
    @gExbii (synWa (.objMem x y) (.classMem (.cv y) (synCpr A B)))
      (synWo (synWa (.objMem x y) (.classEq (.cv y) A))
        (synWa (.objMem x y) (.classEq (.cv y) B)))
      y p0004
  have p0006 :=
    @gN1943 (synWa (.objMem x y) (.classEq (.cv y) A))
      (synWa (.objMem x y) (.classEq (.cv y) B)) y
  have p0007 :=
    @gBitri (synWex y (synWa (.objMem x y) (.classMem (.cv y) (synCpr A B))))
      (synWex y (synWo (synWa (.objMem x y) (.classEq (.cv y) A))
          (synWa (.objMem x y) (.classEq (.cv y) B))))
      (synWo (synWex y (synWa (.objMem x y) (.classEq (.cv y) A)))
        (synWex y (synWa (.objMem x y) (.classEq (.cv y) B))))
      p0005 p0006
  have p0008 :=
    @gEluni y (.cv x) (synCpr A B)
      (by
        (simp (config :=
              {
                failIfUnchanged :=
                  false }) only [NFChoice.Compiler.CoreFVSimp.fv_class_cv,
              Finset.mem_singleton] at ⊢;
            aesop))
      (by
        (simp (config :=
              {
                failIfUnchanged :=
                  false }) only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpr,
              Finset.mem_union] at ⊢;
            aesop))
  have p0009 := @gElun (.cv x) A B
  have p0010 :=
    @gClel3 y (.cv x) A
      (by
        (simp (config :=
              {
                failIfUnchanged :=
                  false }) only [NFChoice.Compiler.CoreFVSimp.fv_class_cv,
              Finset.mem_singleton] at ⊢;
            aesop))
      (by
        aesop)
      hyp_unipr_1
  have p0011 := @gExancom (.classEq (.cv y) A) (.objMem x y) y
  have p0012_e00_recanon :
    Nominal.NPrf
      (synWb (.classMem (.cv x) A) (synWex y (synWa (.classEq (.cv y) A) (.objMem x y)))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold synWb synWex synWa
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
    @gBitri (.classMem (.cv x) A) (synWex y (synWa (.classEq (.cv y) A) (.objMem x y)))
      (synWex y (synWa (.objMem x y) (.classEq (.cv y) A))) p0012_e00_recanon p0011
  have p0013 :=
    @gClel3 y (.cv x) B
      (by
        (simp (config :=
              {
                failIfUnchanged :=
                  false }) only [NFChoice.Compiler.CoreFVSimp.fv_class_cv,
              Finset.mem_singleton] at ⊢;
            aesop))
      (by
        aesop)
      hyp_unipr_2
  have p0014 := @gExancom (.classEq (.cv y) B) (.objMem x y) y
  have p0015_e00_recanon :
    Nominal.NPrf
      (synWb (.classMem (.cv x) B) (synWex y (synWa (.classEq (.cv y) B) (.objMem x y)))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold synWb synWex synWa
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
    @gBitri (.classMem (.cv x) B) (synWex y (synWa (.classEq (.cv y) B) (.objMem x y)))
      (synWex y (synWa (.objMem x y) (.classEq (.cv y) B))) p0015_e00_recanon p0014
  have p0016 :=
    @gOrbi12i (.classMem (.cv x) A)
      (synWex y (synWa (.objMem x y) (.classEq (.cv y) A))) (.classMem (.cv x) B)
      (synWex y (synWa (.objMem x y) (.classEq (.cv y) B))) p0012 p0015
  have p0017 :=
    @gBitri (.classMem (.cv x) (synCun A B))
      (synWo (.classMem (.cv x) A) (.classMem (.cv x) B))
      (synWo (synWex y (synWa (.objMem x y) (.classEq (.cv y) A)))
        (synWex y (synWa (.objMem x y) (.classEq (.cv y) B))))
      p0009 p0016
  have p0018_e01_recanon :
    Nominal.NPrf
      (synWb (.classMem (.cv x) (synCuni (synCpr A B)))
        (synWex y (synWa (.objMem x y) (.classMem (.cv y) (synCpr A B))))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold synWb synCuni synWex synWa synCpr synCun synCnin synWnan synCcompl
          synCsn
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
    @gN3bitr4i (synWex y (synWa (.objMem x y) (.classMem (.cv y) (synCpr A B))))
      (synWo (synWex y (synWa (.objMem x y) (.classEq (.cv y) A)))
        (synWex y (synWa (.objMem x y) (.classEq (.cv y) B))))
      (.classMem (.cv x) (synCuni (synCpr A B))) (.classMem (.cv x) (synCun A B)) p0007
      p0018_e01_recanon p0017
  have p0019 :=
    @gEqriv x (synCuni (synCpr A B)) (synCun A B)
      (by
        (simp (config :=
              {
                failIfUnchanged :=
                  false }) only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cuni,
              NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpr,
              Finset.mem_union] at ⊢;
            aesop))
      (by
        (simp (config :=
              {
                failIfUnchanged :=
                  false }) only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cun,
              Finset.mem_union] at ⊢;
            aesop))
      p0018
  exact p0019

/-- Checked nominal proof certificate identified upstream as `g_unisn`. -/
@[expose]
noncomputable def gUnisn (A : Class)
    (hyp_unisn_1 : Nominal.NPrf (.classMem A (synCvv))) :
    Nominal.NPrf (.classEq (synCuni (synCsn A)) A) :=
  by
  have p0000 := @gDfsn2 A
  have p0001 := @gUnieqi (synCsn A) (synCpr A A) p0000
  have p0002 := @gUnipr A A hyp_unisn_1 hyp_unisn_1
  have p0003 := @gUnidm A
  have p0004 :=
    @gN3eqtri (synCuni (synCsn A)) (synCuni (synCpr A A)) (synCun A A) A p0001
      p0002 p0003
  exact p0004


end NFChoice.DirectNominalPrf.WPPReplay
