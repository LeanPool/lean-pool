/-
Copyright (c) 2026 Elliot Glazer and NFNotWPP contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elliot Glazer and NFNotWPP contributors
-/

module

public import LeanPool.NFWeakPartition.Certificates.NominalWPPReplayChunk010Compact001Block012

/-! Nominal proof certificates grouped in dependency order. -/


public section

/-! Certificates from `NominalWPPReplayChunk010Compact001Part039`. -/


section

namespace NFChoice.DirectNominalPrf.WPPReplay

open scoped Fol
open NFChoice.Foundation
open NFChoice.SemanticCore
open NFChoice.ReplaySupport
open NFChoice.Compiler.CompactSourceSyntax

/-- Checked nominal proof certificate identified upstream as `g_unopab`. -/
@[expose]
noncomputable def gUnopab (ph : Wff) (ps : Wff) (x : Var) (y : Var) :
    Nominal.NPrf
      (.classEq (synCun (synCopab x y ph) (synCopab x y ps))
        (synCopab x y (synWo ph ps))) :=
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
  have dv_cache_0001 : z ∉ (ph).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_z_not_ph, not_false_eq_true])
  have dv_cache_0002 : x ≠ z := by
    clear dv_cache_0001
    exact (show x ≠ z from (by exact fresh_x_ne_z))
  have dv_cache_0003 : y ≠ z :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact (show y ≠ z from (by exact fresh_y_ne_z))
  have dv_cache_0004 : z ∉ (ps).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact
      (by
        have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_z_not_ps, not_false_eq_true])
  have dv_cache_0005 : z ∉ ((synWo ph ps)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact
      (by
        have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wo, Finset.mem_union,
          fresh_z_not_ph, fresh_z_not_ps, or_false, not_false_eq_true])
  have p0000 :=
    @gUnab
      (synWex x (synWex y (synWa (.classEq (.cv z) (synCop (.cv x) (.cv y))) ph)))
      (synWex x (synWex y (synWa (.classEq (.cv z) (synCop (.cv x) (.cv y))) ps))) z
  have p0001 :=
    @gN1943 (synWex y (synWa (.classEq (.cv z) (synCop (.cv x) (.cv y))) ph))
      (synWex y (synWa (.classEq (.cv z) (synCop (.cv x) (.cv y))) ps)) x
  have p0002 := @gAndi (.classEq (.cv z) (synCop (.cv x) (.cv y))) ph ps
  have p0003 :=
    @gExbii (synWa (.classEq (.cv z) (synCop (.cv x) (.cv y))) (synWo ph ps))
      (synWo (synWa (.classEq (.cv z) (synCop (.cv x) (.cv y))) ph)
        (synWa (.classEq (.cv z) (synCop (.cv x) (.cv y))) ps))
      y p0002
  have p0004 :=
    @gN1943 (synWa (.classEq (.cv z) (synCop (.cv x) (.cv y))) ph)
      (synWa (.classEq (.cv z) (synCop (.cv x) (.cv y))) ps) y
  have p0005 :=
    @gBitr2i
      (synWex y (synWa (.classEq (.cv z) (synCop (.cv x) (.cv y))) (synWo ph ps)))
      (synWex y (synWo (synWa (.classEq (.cv z) (synCop (.cv x) (.cv y))) ph)
          (synWa (.classEq (.cv z) (synCop (.cv x) (.cv y))) ps)))
      (synWo (synWex y (synWa (.classEq (.cv z) (synCop (.cv x) (.cv y))) ph))
        (synWex y (synWa (.classEq (.cv z) (synCop (.cv x) (.cv y))) ps)))
      p0003 p0004
  have p0006 :=
    @gExbii
      (synWo (synWex y (synWa (.classEq (.cv z) (synCop (.cv x) (.cv y))) ph))
        (synWex y (synWa (.classEq (.cv z) (synCop (.cv x) (.cv y))) ps)))
      (synWex y (synWa (.classEq (.cv z) (synCop (.cv x) (.cv y))) (synWo ph ps))) x
      p0005
  have p0007 :=
    @gBitr3i
      (synWo (synWex x (synWex y (synWa (.classEq (.cv z) (synCop (.cv x) (.cv y))) ph)))
        (synWex x (synWex y (synWa (.classEq (.cv z) (synCop (.cv x) (.cv y))) ps))))
      (synWex x (synWo (synWex y (synWa (.classEq (.cv z) (synCop (.cv x) (.cv y))) ph))
          (synWex y (synWa (.classEq (.cv z) (synCop (.cv x) (.cv y))) ps))))
      (synWex x
        (synWex y (synWa (.classEq (.cv z) (synCop (.cv x) (.cv y))) (synWo ph ps))))
      p0001 p0006
  have p0008 :=
    @gAbbii
      (synWo (synWex x (synWex y (synWa (.classEq (.cv z) (synCop (.cv x) (.cv y))) ph)))
        (synWex x (synWex y (synWa (.classEq (.cv z) (synCop (.cv x) (.cv y))) ps))))
      (synWex x
        (synWex y (synWa (.classEq (.cv z) (synCop (.cv x) (.cv y))) (synWo ph ps))))
      z p0007
  have p0009 :=
    @gEqtri
      (synCun (.cab z (synWex x
            (synWex y (synWa (.classEq (.cv z) (synCop (.cv x) (.cv y))) ph)))) (.cab z
          (synWex x (synWex y (synWa (.classEq (.cv z) (synCop (.cv x) (.cv y))) ps)))))
      (.cab z (synWo
          (synWex x (synWex y (synWa (.classEq (.cv z) (synCop (.cv x) (.cv y))) ph)))
          (synWex x (synWex y (synWa (.classEq (.cv z) (synCop (.cv x) (.cv y))) ps)))))
      (.cab z (synWex x (synWex y
            (synWa (.classEq (.cv z) (synCop (.cv x) (.cv y))) (synWo ph ps)))))
      p0000 p0008
  have p0010 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominalDfOpab ph x y z
      dv_cache_0001 dv_cache_0002 dv_cache_0003
  have p0011 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominalDfOpab ps x y z
      dv_cache_0004 dv_cache_0002 dv_cache_0003
  have p0012 :=
    @gUneq12i (synCopab x y ph)
      (.cab z (synWex x (synWex y (synWa (.classEq (.cv z) (synCop (.cv x) (.cv y))) ph))))
      (synCopab x y ps)
      (.cab z (synWex x (synWex y (synWa (.classEq (.cv z) (synCop (.cv x) (.cv y))) ps))))
      p0010 p0011
  have p0013 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominalDfOpab (synWo ph ps)
      x y z dv_cache_0005 dv_cache_0002 dv_cache_0003
  have p0014 :=
    @gN3eqtr4i
      (synCun (.cab z (synWex x
            (synWex y (synWa (.classEq (.cv z) (synCop (.cv x) (.cv y))) ph)))) (.cab z
          (synWex x (synWex y (synWa (.classEq (.cv z) (synCop (.cv x) (.cv y))) ps)))))
      (.cab z (synWex x (synWex y
            (synWa (.classEq (.cv z) (synCop (.cv x) (.cv y))) (synWo ph ps)))))
      (synCun (synCopab x y ph) (synCopab x y ps)) (synCopab x y (synWo ph ps)) p0009
      p0012 p0013
  exact p0014

/-- Checked nominal proof certificate identified upstream as `g_breq`. -/
@[expose]
noncomputable def gBreq (A : Class) (B : Class) (R : Class) (S : Class) :
    Nominal.NPrf (.imp (.classEq R S) (synWb (synWbr A R B) (synWbr A S B))) :=
  by
  have p0000 := @gEleq2 R S (synCop A B)
  have p0001 := (Nominal.biimpRefl (synWbr A R B))
  have p0002 := (Nominal.biimpRefl (synWbr A S B))
  have p0003 :=
    @gN3bitr4g (.classEq R S) (.classMem (synCop A B) R) (.classMem (synCop A B) S)
      (synWbr A R B) (synWbr A S B) p0000 p0001 p0002
  exact p0003

/-- Checked nominal proof certificate identified upstream as `g_breq1`. -/
@[expose]
noncomputable def gBreq1 (A : Class) (B : Class) (C : Class) (R : Class) :
    Nominal.NPrf (.imp (.classEq A B) (synWb (synWbr A R C) (synWbr B R C))) :=
  by
  have p0000 := @gOpeq1 A B C
  have p0001 := @gEleq1d (.classEq A B) (synCop A C) (synCop B C) R p0000
  have p0002 := (Nominal.biimpRefl (synWbr A R C))
  have p0003 := (Nominal.biimpRefl (synWbr B R C))
  have p0004 :=
    @gN3bitr4g (.classEq A B) (.classMem (synCop A C) R) (.classMem (synCop B C) R)
      (synWbr A R C) (synWbr B R C) p0001 p0002 p0003
  exact p0004

/-- Checked nominal proof certificate identified upstream as `g_breq2`. -/
@[expose]
noncomputable def gBreq2 (A : Class) (B : Class) (C : Class) (R : Class) :
    Nominal.NPrf (.imp (.classEq A B) (synWb (synWbr C R A) (synWbr C R B))) :=
  by
  have p0000 := @gOpeq2 A B C
  have p0001 := @gEleq1d (.classEq A B) (synCop C A) (synCop C B) R p0000
  have p0002 := (Nominal.biimpRefl (synWbr C R A))
  have p0003 := (Nominal.biimpRefl (synWbr C R B))
  have p0004 :=
    @gN3bitr4g (.classEq A B) (.classMem (synCop C A) R) (.classMem (synCop C B) R)
      (synWbr C R A) (synWbr C R B) p0001 p0002 p0003
  exact p0004

/-- Checked nominal proof certificate identified upstream as `g_breq12`. -/
@[expose]
noncomputable def gBreq12 (A : Class) (B : Class) (C : Class) (D : Class) (R : Class) :
    Nominal.NPrf
      (.imp (synWa (.classEq A B) (.classEq C D)) (synWb (synWbr A R C) (synWbr B R D))) :=
  by
  have p0000 := @gBreq1 A B C R
  have p0001 := @gBreq2 C D B R
  have p0002 :=
    @gSylan9bb (.classEq A B) (synWbr A R C) (synWbr B R C) (.classEq C D)
      (synWbr B R D) p0000 p0001
  exact p0002

/-- Checked nominal proof certificate identified upstream as `g_breqi`. -/
@[expose]
noncomputable def gBreqi (A : Class) (B : Class) (R : Class) (S : Class)
    (hyp_breqi_1 : Nominal.NPrf (.classEq R S)) :
    Nominal.NPrf (synWb (synWbr A R B) (synWbr A S B)) :=
  by
  have p0000 := @gBreq A B R S
  have p0001 := Nominal.mp hyp_breqi_1 p0000
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_breq1i`. -/
@[expose]
noncomputable def gBreq1i (A : Class) (B : Class) (C : Class) (R : Class)
    (hyp_breq1i_1 : Nominal.NPrf (.classEq A B)) :
    Nominal.NPrf (synWb (synWbr A R C) (synWbr B R C)) :=
  by
  have p0000 := @gBreq1 A B C R
  have p0001 := Nominal.mp hyp_breq1i_1 p0000
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_breq2i`. -/
@[expose]
noncomputable def gBreq2i (A : Class) (B : Class) (C : Class) (R : Class)
    (hyp_breq1i_1 : Nominal.NPrf (.classEq A B)) :
    Nominal.NPrf (synWb (synWbr C R A) (synWbr C R B)) :=
  by
  have p0000 := @gBreq2 A B C R
  have p0001 := Nominal.mp hyp_breq1i_1 p0000
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_breq12i`. -/
@[expose]
noncomputable def gBreq12i (A : Class) (B : Class) (C : Class) (D : Class) (R : Class)
    (hyp_breq1i_1 : Nominal.NPrf (.classEq A B))
    (hyp_breq12i_2 : Nominal.NPrf (.classEq C D)) :
    Nominal.NPrf (synWb (synWbr A R C) (synWbr B R D)) :=
  by
  have p0000 := @gBreq12 A B C D R
  have p0001 :=
    @gMp2an (.classEq A B) (.classEq C D) (synWb (synWbr A R C) (synWbr B R D))
      hyp_breq1i_1 hyp_breq12i_2 p0000
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_breq1d`. -/
@[expose]
noncomputable def gBreq1d (ph : Wff) (A : Class) (B : Class) (C : Class) (R : Class)
    (hyp_breq1d_1 : Nominal.NPrf (.imp ph (.classEq A B))) :
    Nominal.NPrf (.imp ph (synWb (synWbr A R C) (synWbr B R C))) :=
  by
  have p0000 := @gBreq1 A B C R
  have p0001 :=
    @gSyl ph (.classEq A B) (synWb (synWbr A R C) (synWbr B R C)) hyp_breq1d_1 p0000
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_breqd`. -/
@[expose]
noncomputable def gBreqd (ph : Wff) (A : Class) (B : Class) (C : Class) (D : Class)
    (hyp_breq1d_1 : Nominal.NPrf (.imp ph (.classEq A B))) :
    Nominal.NPrf (.imp ph (synWb (synWbr C A D) (synWbr C B D))) :=
  by
  have p0000 := @gBreq C D A B
  have p0001 :=
    @gSyl ph (.classEq A B) (synWb (synWbr C A D) (synWbr C B D)) hyp_breq1d_1 p0000
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_breq2d`. -/
@[expose]
noncomputable def gBreq2d (ph : Wff) (A : Class) (B : Class) (C : Class) (R : Class)
    (hyp_breq1d_1 : Nominal.NPrf (.imp ph (.classEq A B))) :
    Nominal.NPrf (.imp ph (synWb (synWbr C R A) (synWbr C R B))) :=
  by
  have p0000 := @gBreq2 A B C R
  have p0001 :=
    @gSyl ph (.classEq A B) (synWb (synWbr C R A) (synWbr C R B)) hyp_breq1d_1 p0000
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_breq12d`. -/
@[expose]
noncomputable def gBreq12d (ph : Wff) (A : Class) (B : Class) (C : Class) (D : Class)
    (R : Class) (hyp_breq1d_1 : Nominal.NPrf (.imp ph (.classEq A B)))
    (hyp_breq12d_2 : Nominal.NPrf (.imp ph (.classEq C D))) :
    Nominal.NPrf (.imp ph (synWb (synWbr A R C) (synWbr B R D))) :=
  by
  have p0000 := @gBreq12 A B C D R
  have p0001 :=
    @gSyl2anc ph (.classEq A B) (.classEq C D) (synWb (synWbr A R C) (synWbr B R D))
      hyp_breq1d_1 hyp_breq12d_2 p0000
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_breqan12d`. -/
@[expose]
noncomputable def gBreqan12d (ph : Wff) (ps : Wff) (A : Class) (B : Class) (C : Class)
    (D : Class) (R : Class) (hyp_breq1d_1 : Nominal.NPrf (.imp ph (.classEq A B)))
    (hyp_breqan12i_2 : Nominal.NPrf (.imp ps (.classEq C D))) :
    Nominal.NPrf (.imp (synWa ph ps) (synWb (synWbr A R C) (synWbr B R D))) :=
  by
  have p0000 := @gBreq12 A B C D R
  have p0001 :=
    @gSyl2an ph (.classEq A B) (.classEq C D) (synWb (synWbr A R C) (synWbr B R D)) ps
      hyp_breq1d_1 hyp_breqan12i_2 p0000
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_eqbrtri`. -/
@[expose]
noncomputable def gEqbrtri (A : Class) (B : Class) (C : Class) (R : Class)
    (hyp_eqbrtr_1 : Nominal.NPrf (.classEq A B))
    (hyp_eqbrtr_2 : Nominal.NPrf (synWbr B R C)) : Nominal.NPrf (synWbr A R C) :=
  by
  have p0000 := @gBreq1i A B C R hyp_eqbrtr_1
  have p0001 := @gMpbir (synWbr A R C) (synWbr B R C) hyp_eqbrtr_2 p0000
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_eqbrtrd`. -/
@[expose]
noncomputable def gEqbrtrd (ph : Wff) (A : Class) (B : Class) (C : Class) (R : Class)
    (hyp_eqbrtrd_1 : Nominal.NPrf (.imp ph (.classEq A B)))
    (hyp_eqbrtrd_2 : Nominal.NPrf (.imp ph (synWbr B R C))) :
    Nominal.NPrf (.imp ph (synWbr A R C)) :=
  by
  have p0000 := @gBreq1d ph A B C R hyp_eqbrtrd_1
  have p0001 := @gMpbird ph (synWbr A R C) (synWbr B R C) hyp_eqbrtrd_2 p0000
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_eqbrtrri`. -/
@[expose]
noncomputable def gEqbrtrri (A : Class) (B : Class) (C : Class) (R : Class)
    (hyp_eqbrtrr_1 : Nominal.NPrf (.classEq A B))
    (hyp_eqbrtrr_2 : Nominal.NPrf (synWbr A R C)) : Nominal.NPrf (synWbr B R C) :=
  by
  have p0000 := @gEqcomi A B hyp_eqbrtrr_1
  have p0001 := @gEqbrtri B A C R p0000 hyp_eqbrtrr_2
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_eqbrtrrd`. -/
@[expose]
noncomputable def gEqbrtrrd (ph : Wff) (A : Class) (B : Class) (C : Class) (R : Class)
    (hyp_eqbrtrrd_1 : Nominal.NPrf (.imp ph (.classEq A B)))
    (hyp_eqbrtrrd_2 : Nominal.NPrf (.imp ph (synWbr A R C))) :
    Nominal.NPrf (.imp ph (synWbr B R C)) :=
  by
  have p0000 := @gEqcomd ph A B hyp_eqbrtrrd_1
  have p0001 := @gEqbrtrd ph B A C R p0000 hyp_eqbrtrrd_2
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_breqtri`. -/
@[expose]
noncomputable def gBreqtri (A : Class) (B : Class) (C : Class) (R : Class)
    (hyp_breqtr_1 : Nominal.NPrf (synWbr A R B))
    (hyp_breqtr_2 : Nominal.NPrf (.classEq B C)) : Nominal.NPrf (synWbr A R C) :=
  by
  have p0000 := @gBreq2i B C A R hyp_breqtr_2
  have p0001 := @gMpbi (synWbr A R B) (synWbr A R C) hyp_breqtr_1 p0000
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_breqtrd`. -/
@[expose]
noncomputable def gBreqtrd (ph : Wff) (A : Class) (B : Class) (C : Class) (R : Class)
    (hyp_breqtrd_1 : Nominal.NPrf (.imp ph (synWbr A R B)))
    (hyp_breqtrd_2 : Nominal.NPrf (.imp ph (.classEq B C))) :
    Nominal.NPrf (.imp ph (synWbr A R C)) :=
  by
  have p0000 := @gBreq2d ph B C A R hyp_breqtrd_2
  have p0001 := @gMpbid ph (synWbr A R B) (synWbr A R C) hyp_breqtrd_1 p0000
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_breqtrri`. -/
@[expose]
noncomputable def gBreqtrri (A : Class) (B : Class) (C : Class) (R : Class)
    (hyp_breqtrr_1 : Nominal.NPrf (synWbr A R B))
    (hyp_breqtrr_2 : Nominal.NPrf (.classEq C B)) : Nominal.NPrf (synWbr A R C) :=
  by
  have p0000 := @gEqcomi C B hyp_breqtrr_2
  have p0001 := @gBreqtri A B C R hyp_breqtrr_1 p0000
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_breqtrrd`. -/
@[expose]
noncomputable def gBreqtrrd (ph : Wff) (A : Class) (B : Class) (C : Class) (R : Class)
    (hyp_breqtrrd_1 : Nominal.NPrf (.imp ph (synWbr A R B)))
    (hyp_breqtrrd_2 : Nominal.NPrf (.imp ph (.classEq C B))) :
    Nominal.NPrf (.imp ph (synWbr A R C)) :=
  by
  have p0000 := @gEqcomd ph C B hyp_breqtrrd_2
  have p0001 := @gBreqtrd ph A B C R hyp_breqtrrd_1 p0000
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_n_3brtr3i`. -/
@[expose]
noncomputable def gN3brtr3i (A : Class) (B : Class) (C : Class) (D : Class) (R : Class)
    (hyp_n_3brtr3_1 : Nominal.NPrf (synWbr A R B))
    (hyp_n_3brtr3_2 : Nominal.NPrf (.classEq A C))
    (hyp_n_3brtr3_3 : Nominal.NPrf (.classEq B D)) : Nominal.NPrf (synWbr C R D) :=
  by
  have p0000 := @gEqbrtrri A C B R hyp_n_3brtr3_2 hyp_n_3brtr3_1
  have p0001 := @gBreqtri C B D R p0000 hyp_n_3brtr3_3
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_n_3brtr4d`. -/
@[expose]
noncomputable def gN3brtr4d (ph : Wff) (A : Class) (B : Class) (C : Class) (D : Class)
    (R : Class) (hyp_n_3brtr4d_1 : Nominal.NPrf (.imp ph (synWbr A R B)))
    (hyp_n_3brtr4d_2 : Nominal.NPrf (.imp ph (.classEq C A)))
    (hyp_n_3brtr4d_3 : Nominal.NPrf (.imp ph (.classEq D B))) :
    Nominal.NPrf (.imp ph (synWbr C R D)) :=
  by
  have p0000 := @gBreq12d ph C A D B R hyp_n_3brtr4d_2 hyp_n_3brtr4d_3
  have p0001 := @gMpbird ph (synWbr C R D) (synWbr A R B) hyp_n_3brtr4d_1 p0000
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_n_3brtr3g`. -/
@[expose]
noncomputable def gN3brtr3g (ph : Wff) (A : Class) (B : Class) (C : Class) (D : Class)
    (R : Class) (hyp_n_3brtr3g_1 : Nominal.NPrf (.imp ph (synWbr A R B)))
    (hyp_n_3brtr3g_2 : Nominal.NPrf (.classEq A C))
    (hyp_n_3brtr3g_3 : Nominal.NPrf (.classEq B D)) :
    Nominal.NPrf (.imp ph (synWbr C R D)) :=
  by
  have p0000 := @gBreq12i A C B D R hyp_n_3brtr3g_2 hyp_n_3brtr3g_3
  have p0001 := @gSylib ph (synWbr A R B) (synWbr C R D) hyp_n_3brtr3g_1 p0000
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_syl5eqbrr`. -/
@[expose]
noncomputable def gSyl5eqbrr (ph : Wff) (A : Class) (B : Class) (C : Class) (R : Class)
    (hyp_syl5eqbrr_1 : Nominal.NPrf (.classEq B A))
    (hyp_syl5eqbrr_2 : Nominal.NPrf (.imp ph (synWbr B R C))) :
    Nominal.NPrf (.imp ph (synWbr A R C)) :=
  by
  have p0000 := @gEqid C
  have p0001 := @gN3brtr3g ph B C A C R hyp_syl5eqbrr_2 hyp_syl5eqbrr_1 p0000
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_syl5breq`. -/
@[expose]
noncomputable def gSyl5breq (ph : Wff) (A : Class) (B : Class) (C : Class) (R : Class)
    (hyp_syl5breq_1 : Nominal.NPrf (synWbr A R B))
    (hyp_syl5breq_2 : Nominal.NPrf (.imp ph (.classEq B C))) :
    Nominal.NPrf (.imp ph (synWbr A R C)) :=
  by
  have p0000 := @gA1i (synWbr A R B) ph hyp_syl5breq_1
  have p0001 := @gBreqtrd ph A B C R p0000 hyp_syl5breq_2
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_syl6eqbr`. -/
@[expose]
noncomputable def gSyl6eqbr (ph : Wff) (A : Class) (B : Class) (C : Class) (R : Class)
    (hyp_syl6eqbr_1 : Nominal.NPrf (.imp ph (.classEq A B)))
    (hyp_syl6eqbr_2 : Nominal.NPrf (synWbr B R C)) :
    Nominal.NPrf (.imp ph (synWbr A R C)) :=
  by
  have p0000 := @gBreq1d ph A B C R hyp_syl6eqbr_1
  have p0001 := @gMpbiri ph (synWbr A R C) (synWbr B R C) hyp_syl6eqbr_2 p0000
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_ssbrd`. -/
@[expose]
noncomputable def gSsbrd (ph : Wff) (A : Class) (B : Class) (C : Class) (D : Class)
    (hyp_ssbrd_1 : Nominal.NPrf (.imp ph (synWss A B))) :
    Nominal.NPrf (.imp ph (.imp (synWbr C A D) (synWbr C B D))) :=
  by
  have p0000 := @gSseld ph A B (synCop C D) hyp_ssbrd_1
  have p0001 := (Nominal.biimpRefl (synWbr C A D))
  have p0002 := (Nominal.biimpRefl (synWbr C B D))
  have p0003 :=
    @gN3imtr4g ph (.classMem (synCop C D) A) (.classMem (synCop C D) B)
      (synWbr C A D) (synWbr C B D) p0000 p0001 p0002
  exact p0003

/-- Checked nominal proof certificate identified upstream as `g_ssbri`. -/
@[expose]
noncomputable def gSsbri (A : Class) (B : Class) (C : Class) (D : Class)
    (hyp_ssbri_1 : Nominal.NPrf (synWss A B)) :
    Nominal.NPrf (.imp (synWbr C A D) (synWbr C B D)) :=
  by
  have p0000 := @gSsid A
  have p0001 := @gA1i (synWss A B) (synWss A A) hyp_ssbri_1
  have p0002 := @gSsbrd (synWss A A) A B C D p0001
  have p0003 := Nominal.mp p0000 p0002
  exact p0003

/-- Checked nominal proof certificate identified upstream as `g_nfbrd`. -/
@[expose]
noncomputable def gNfbrd (ph : Wff) (x : Var) (A : Class) (B : Class) (R : Class)
    (hyp_nfbrd_2 : Nominal.NPrf (.imp ph (synWnfc x A)))
    (hyp_nfbrd_3 : Nominal.NPrf (.imp ph (synWnfc x R)))
    (hyp_nfbrd_4 : Nominal.NPrf (.imp ph (synWnfc x B))) :
    Nominal.NPrf (.imp ph (synWnf x (synWbr A R B))) :=
  by
  have p0000 := (Nominal.biimpRefl (synWbr A R B))
  have p0001 := @gNfopd ph x A B hyp_nfbrd_2 hyp_nfbrd_4
  have p0002 := @gNfeld ph x (synCop A B) R p0001 hyp_nfbrd_3
  have p0003 := @gNfxfrd (synWbr A R B) (.classMem (synCop A B) R) ph x p0000 p0002
  exact p0003

/-- Checked nominal proof certificate identified upstream as `g_nfbr`. -/
@[expose]
noncomputable def gNfbr (x : Var) (A : Class) (B : Class) (R : Class)
    (hyp_nfbr_1 : Nominal.NPrf (synWnfc x A)) (hyp_nfbr_2 : Nominal.NPrf (synWnfc x R))
    (hyp_nfbr_3 : Nominal.NPrf (synWnfc x B)) :
    Nominal.NPrf (synWnf x (synWbr A R B)) :=
  by
  have p0000 := @gA1i (synWnfc x A) synWtru hyp_nfbr_1
  have p0001 := @gA1i (synWnfc x R) synWtru hyp_nfbr_2
  have p0002 := @gA1i (synWnfc x B) synWtru hyp_nfbr_3
  have p0003 := @gNfbrd synWtru x A B R p0000 p0001 p0002
  have p0004 := @gTrud (synWnf x (synWbr A R B)) p0003
  exact p0004

/-- Checked nominal proof certificate identified upstream as `g_brex`. -/
@[expose]
noncomputable def gBrex (A : Class) (B : Class) (R : Class) :
    Nominal.NPrf
      (.imp (synWbr A R B) (synWa (.classMem A (synCvv)) (.classMem B (synCvv)))) :=
  by
  have p0000 := @gElex (synCop A B) R
  have p0001 := (Nominal.biimpRefl (synWbr A R B))
  have p0002 := @gOpexb A B
  have p0003 :=
    @gBicomi (.classMem (synCop A B) (synCvv))
      (synWa (.classMem A (synCvv)) (.classMem B (synCvv))) p0002
  have p0004 :=
    @gN3imtr4i (.classMem (synCop A B) R) (.classMem (synCop A B) (synCvv))
      (synWbr A R B) (synWa (.classMem A (synCvv)) (.classMem B (synCvv))) p0000 p0001
      p0003
  exact p0004

/-- Checked nominal proof certificate identified upstream as `g_brreldmex`. -/
@[expose]
noncomputable def gBrreldmex (A : Class) (B : Class) (R : Class) :
    Nominal.NPrf (.imp (synWbr A R B) (.classMem A (synCvv))) :=
  by
  have p0000 := @gBrex A B R
  have p0001 :=
    @gSimpld (synWbr A R B) (.classMem A (synCvv)) (.classMem B (synCvv)) p0000
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_brrelrnex`. -/
@[expose]
noncomputable def gBrrelrnex (A : Class) (B : Class) (R : Class) :
    Nominal.NPrf (.imp (synWbr A R B) (.classMem B (synCvv))) :=
  by
  have p0000 := @gBrex A B R
  have p0001 :=
    @gSimprd (synWbr A R B) (.classMem A (synCvv)) (.classMem B (synCvv)) p0000
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_brun`. -/
@[expose]
noncomputable def gBrun (A : Class) (B : Class) (R : Class) (S : Class) :
    Nominal.NPrf
      (synWb (synWbr A (synCun R S) B) (synWo (synWbr A R B) (synWbr A S B))) :=
  by
  have p0000 := @gElun (synCop A B) R S
  have p0001 := (Nominal.biimpRefl (synWbr A (synCun R S) B))
  have p0002 := (Nominal.biimpRefl (synWbr A R B))
  have p0003 := (Nominal.biimpRefl (synWbr A S B))
  have p0004 :=
    @gOrbi12i (synWbr A R B) (.classMem (synCop A B) R) (synWbr A S B)
      (.classMem (synCop A B) S) p0002 p0003
  have p0005 :=
    @gN3bitr4i (.classMem (synCop A B) (synCun R S))
      (synWo (.classMem (synCop A B) R) (.classMem (synCop A B) S))
      (synWbr A (synCun R S) B) (synWo (synWbr A R B) (synWbr A S B)) p0000 p0001
      p0004
  exact p0005

/-- Checked nominal proof certificate identified upstream as `g_brin`. -/
@[expose]
noncomputable def gBrin (A : Class) (B : Class) (R : Class) (S : Class) :
    Nominal.NPrf
      (synWb (synWbr A (synCin R S) B) (synWa (synWbr A R B) (synWbr A S B))) :=
  by
  have p0000 := @gElin (synCop A B) R S
  have p0001 := (Nominal.biimpRefl (synWbr A (synCin R S) B))
  have p0002 := (Nominal.biimpRefl (synWbr A R B))
  have p0003 := (Nominal.biimpRefl (synWbr A S B))
  have p0004 :=
    @gAnbi12i (synWbr A R B) (.classMem (synCop A B) R) (synWbr A S B)
      (.classMem (synCop A B) S) p0002 p0003
  have p0005 :=
    @gN3bitr4i (.classMem (synCop A B) (synCin R S))
      (synWa (.classMem (synCop A B) R) (.classMem (synCop A B) S))
      (synWbr A (synCin R S) B) (synWa (synWbr A R B) (synWbr A S B)) p0000 p0001
      p0004
  exact p0005

/-- Checked nominal proof certificate identified upstream as `g_brdif`. -/
@[expose]
noncomputable def gBrdif (A : Class) (B : Class) (R : Class) (S : Class) :
    Nominal.NPrf
      (synWb (synWbr A (synCdif R S) B) (synWa (synWbr A R B) (.neg (synWbr A S B)))) :=
  by
  have p0000 := @gEldif (synCop A B) R S
  have p0001 := (Nominal.biimpRefl (synWbr A (synCdif R S) B))
  have p0002 := (Nominal.biimpRefl (synWbr A R B))
  have p0003 := (Nominal.biimpRefl (synWbr A S B))
  have p0004 := @gNotbii (synWbr A S B) (.classMem (synCop A B) S) p0003
  have p0005 :=
    @gAnbi12i (synWbr A R B) (.classMem (synCop A B) R) (.neg (synWbr A S B))
      (.neg (.classMem (synCop A B) S)) p0002 p0004
  have p0006 :=
    @gN3bitr4i (.classMem (synCop A B) (synCdif R S))
      (synWa (.classMem (synCop A B) R) (.neg (.classMem (synCop A B) S)))
      (synWbr A (synCdif R S) B) (synWa (synWbr A R B) (.neg (synWbr A S B))) p0000
      p0001 p0005
  exact p0006

/-- Checked nominal proof certificate identified upstream as `g_opabid`. -/
@[expose]
noncomputable def gOpabid (ph : Wff) (x : Var) (y : Var) :
    Nominal.NPrf (synWb (.classMem (synCop (.cv x) (.cv y)) (synCopab x y ph)) ph) :=
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
  have dv_cache_0001 : x ∉ ((Class.cv z)).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_x_ne_z, not_false_eq_true])
  have dv_cache_0002 : y ∉ ((Class.cv z)).fv :=
    by
    clear dv_cache_0001
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_y_ne_z, not_false_eq_true])
  have dv_cache_0003 : z ∉ (ph).fv :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact
      (by
        have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_z_not_ph, not_false_eq_true])
  have dv_cache_0004 : x ≠ z :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact (show x ≠ z from (by exact fresh_x_ne_z))
  have dv_cache_0005 : y ≠ z :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact (show y ≠ z from (by exact fresh_y_ne_z))
  have dv_cache_0006 : z ∉ ((synCop (.cv x) (.cv y))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact
      (by
        have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cop,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, fresh_z_ne_x, fresh_z_ne_y, or_false, not_false_eq_true])
  have p0000 := @gVex x
  have p0001 := @gVex y
  have p0002 := @gOpex (.cv x) (.cv y) p0000 p0001
  have p0003 := @gCopsexg ph x y (.cv z) dv_cache_0001 dv_cache_0002
  have p0004 :=
    @gBicomd (.classEq (.cv z) (synCop (.cv x) (.cv y))) ph
      (synWex x (synWex y (synWa (.classEq (.cv z) (synCop (.cv x) (.cv y))) ph)))
      p0003
  have p0005 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominalDfOpab ph x y z
      dv_cache_0003 dv_cache_0004 dv_cache_0005
  have p0006 :=
    @gElab2
      (synWex x (synWex y (synWa (.classEq (.cv z) (synCop (.cv x) (.cv y))) ph))) ph
      z (synCop (.cv x) (.cv y)) (synCopab x y ph) dv_cache_0006 dv_cache_0003 p0002
      p0004 p0005
  exact p0006

/-- Checked nominal proof certificate identified upstream as `g_elopab`. -/
@[expose]
noncomputable def gElopab (ph : Wff) (x : Var) (y : Var) (A : Class) (dv_A_x : x ∉ A.fv)
    (dv_A_y : y ∉ A.fv) :
    Nominal.NPrf
      (synWb (.classMem A (synCopab x y ph))
        (synWex x (synWex y (synWa (.classEq A (synCop (.cv x) (.cv y))) ph)))) :=
  by
  let proofSupport : Finset Var :=
    ph.fv ∪ ({ x } : Finset Var) ∪ ({ y } : Finset Var) ∪ A.fv
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
  have fresh_z_ne_x : z ≠ x := by
    intro h
    exact
      fresh_z
        (Finset.mem_union_left _ (Finset.mem_union_left _
            (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))))
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
  have dv_cache_0001 : x ∉ ((Wff.classMem A (synCvv))).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv, Finset.mem_union, dv_A_x,
          compact_fv_not_mem_empty, or_false, not_false_eq_true])
  have dv_cache_0002 : y ∉ ((Wff.classMem A (synCvv))).fv :=
    by
    clear dv_cache_0001
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv, Finset.mem_union, dv_A_y,
          compact_fv_not_mem_empty, or_false, not_false_eq_true])
  have dv_cache_0003 : x ∉ ((Wff.classEq (.cv z) A)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, fresh_x_ne_z, dv_A_x, or_false, not_false_eq_true])
  have dv_cache_0004 : y ∉ ((Wff.classEq (.cv z) A)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, fresh_y_ne_z, dv_A_y, or_false, not_false_eq_true])
  have dv_cache_0005 : z ∉ (ph).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact
      (by
        have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_z_not_ph, not_false_eq_true])
  have dv_cache_0006 : x ≠ z :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact (show x ≠ z from (by exact fresh_x_ne_z))
  have dv_cache_0007 : y ≠ z :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006
    exact (show y ≠ z from (by exact fresh_y_ne_z))
  have dv_cache_0008 : z ∉ (A).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007
    exact
      (by
        have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_z_not_A, not_false_eq_true])
  have dv_cache_0009 :
    z ∉ ((synWex x (synWex y (synWa (.classEq A (synCop (.cv x) (.cv y))) ph)))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008
    exact
      (by
        have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wex,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cop,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase,
          Finset.mem_singleton, fresh_z_not_A, fresh_z_ne_x, fresh_z_ne_y, fresh_z_not_ph,
          or_false, and_false, not_false_eq_true])
  have p0000 := @gElex A (synCopab x y ph)
  have p0001 := @gVex x
  have p0002 := @gVex y
  have p0003 := @gOpex (.cv x) (.cv y) p0001 p0002
  have p0004 := @gEleq1 A (synCop (.cv x) (.cv y)) (synCvv)
  have p0005 :=
    @gMpbiri (.classEq A (synCop (.cv x) (.cv y))) (.classMem A (synCvv))
      (.classMem (synCop (.cv x) (.cv y)) (synCvv)) p0003 p0004
  have p0006 :=
    @gAdantr (.classEq A (synCop (.cv x) (.cv y))) (.classMem A (synCvv)) ph p0005
  have p0007 :=
    @gExlimivv (synWa (.classEq A (synCop (.cv x) (.cv y))) ph) (.classMem A (synCvv))
      x y dv_cache_0001 dv_cache_0002 p0006
  have p0008 := @gEqeq1 (.cv z) A (synCop (.cv x) (.cv y))
  have p0009 :=
    @gAnbi1d (.classEq (.cv z) A) (.classEq (.cv z) (synCop (.cv x) (.cv y)))
      (.classEq A (synCop (.cv x) (.cv y))) ph p0008
  have p0010 :=
    @gN2exbidv (.classEq (.cv z) A)
      (synWa (.classEq (.cv z) (synCop (.cv x) (.cv y))) ph)
      (synWa (.classEq A (synCop (.cv x) (.cv y))) ph) x y dv_cache_0003 dv_cache_0004
      p0009
  have p0011 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominalDfOpab ph x y z
      dv_cache_0005 dv_cache_0006 dv_cache_0007
  have p0012 :=
    @gElab2g
      (synWex x (synWex y (synWa (.classEq (.cv z) (synCop (.cv x) (.cv y))) ph)))
      (synWex x (synWex y (synWa (.classEq A (synCop (.cv x) (.cv y))) ph))) z A
      (synCopab x y ph) (synCvv) dv_cache_0008 dv_cache_0009 p0010 p0011
  have p0013 :=
    @gPm521nii (.classMem A (synCopab x y ph)) (.classMem A (synCvv))
      (synWex x (synWex y (synWa (.classEq A (synCop (.cv x) (.cv y))) ph))) p0000
      p0007 p0012
  exact p0013

/-- Checked nominal proof certificate identified upstream as `g_opelopabsb`. -/
@[expose]
noncomputable def gOpelopabsb (ph : Wff) (x : Var) (y : Var) (A : Class) (B : Class)
    (dv_B_x : x ∉ B.fv) (dv_x_y : x ≠ y) :
    Nominal.NPrf
      (synWb (.classMem (synCop A B) (synCopab x y ph)) (synWsbc A x (synWsbc B y ph))) :=
  by
  let proofSupport : Finset Var :=
    ph.fv ∪ ({ x } : Finset Var) ∪ ({ y } : Finset Var) ∪ A.fv ∪ B.fv
  let z : Var := freshVar proofSupport 0
  let w : Var := freshVar proofSupport 1
  have fresh_z : z ∉ proofSupport :=
    by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_z_not_ph : z ∉ ph.fv := by
    intro h
    exact
      fresh_z
        (Finset.mem_union_left _ (Finset.mem_union_left _
            (Finset.mem_union_left _ (Finset.mem_union_left _ (h)))))
  have fresh_z_ne_x : z ≠ x := by
    intro h
    exact
      fresh_z
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _
              (Finset.mem_union_right _ (Finset.mem_singleton.mpr h)))))
  have fresh_x_ne_z : x ≠ z := Ne.symm fresh_z_ne_x
  have fresh_z_ne_y : z ≠ y := by
    intro h
    exact
      fresh_z
        (Finset.mem_union_left _ (Finset.mem_union_left _
            (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))))
  have fresh_z_not_A : z ∉ A.fv := by
    intro h
    exact fresh_z (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_w : w ∉ proofSupport :=
    by
    change freshVar proofSupport 1 ∉ proofSupport
    exact freshVar_not_mem proofSupport 1
  have fresh_w_not_ph : w ∉ ph.fv := by
    intro h
    exact
      fresh_w
        (Finset.mem_union_left _ (Finset.mem_union_left _
            (Finset.mem_union_left _ (Finset.mem_union_left _ (h)))))
  have fresh_w_ne_x : w ≠ x := by
    intro h
    exact
      fresh_w
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _
              (Finset.mem_union_right _ (Finset.mem_singleton.mpr h)))))
  have fresh_x_ne_w : x ≠ w := Ne.symm fresh_w_ne_x
  have fresh_w_ne_y : w ≠ y := by
    intro h
    exact
      fresh_w
        (Finset.mem_union_left _ (Finset.mem_union_left _
            (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))))
  have fresh_y_ne_w : y ≠ w := Ne.symm fresh_w_ne_y
  have fresh_w_not_A : w ∉ A.fv := by
    intro h
    exact fresh_w (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_w_not_B : w ∉ B.fv := by
    intro h
    exact fresh_w (Finset.mem_union_right _ (h))
  have fresh_z_ne_w : z ≠ w :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have dv_cache_0001 : x ∉ ((Wff.classMem B (synCvv))).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv, Finset.mem_union, dv_B_x,
          compact_fv_not_mem_empty, or_false, not_false_eq_true])
  have dv_cache_0002 : x ∉ ((Wff.classEq (.cv w) B)).fv :=
    by
    clear dv_cache_0001
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, fresh_x_ne_w, dv_B_x, or_false, not_false_eq_true])
  have dv_cache_0003 : x ∉ ((synCop (.cv z) (.cv w))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cop,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, fresh_x_ne_z, fresh_x_ne_w, or_false, not_false_eq_true])
  have dv_cache_0004 : x ≠ z :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact (show x ≠ z from (by exact fresh_x_ne_z))
  have dv_cache_0005 : y ∉ ((synCop (.cv x) (.cv w))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cop,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, (Ne.symm dv_x_y), fresh_y_ne_w, or_false,
          not_false_eq_true])
  have dv_cache_0006 : y ≠ w :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact (show y ≠ w from (by exact fresh_y_ne_w))
  have dv_cache_0007 : z ∉ (A).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006
    exact
      (by
        have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_z_not_A, not_false_eq_true])
  have dv_cache_0008 : w ∉ (A).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007
    exact
      (by
        have compact_fv_not_mem_empty : w ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_w_not_A, not_false_eq_true])
  have dv_cache_0009 : w ∉ (B).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008
    exact
      (by
        have compact_fv_not_mem_empty : w ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_w_not_B, not_false_eq_true])
  have dv_cache_0010 :
    w ∉
      ((synWb (.classMem (synCop A B) (synCopab x y ph))
          (synWsbc A x (synWsbc B y ph)))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009
    exact
      (by
        have compact_fv_not_mem_empty : w ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wb,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cop,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_copab,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wsbc, Finset.mem_union,
          Finset.mem_erase, Finset.mem_singleton, fresh_w_not_A, fresh_w_not_B,
          fresh_w_not_ph, fresh_w_ne_x, or_false, and_false, not_false_eq_true])
  have dv_cache_0011 :
    z ∉
      ((synWb (.classMem (synCop A (.cv w)) (synCopab x y ph))
          (synWsbc A x (synWsb w y ph)))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010
    exact
      (by
        have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wb,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cop,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_copab,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wsbc,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wsb, Finset.mem_union,
          Finset.mem_erase, Finset.mem_singleton, fresh_z_not_A, fresh_z_ne_w,
          fresh_z_not_ph, fresh_z_ne_x, fresh_z_ne_y, or_false, and_false,
          not_false_eq_true])
  have p0000 := (Nominal.biimpRefl (synWbr A (synCopab x y ph) B))
  have p0001 := @gBrex A B (synCopab x y ph)
  have p0002 :=
    @gSylbir (.classMem (synCop A B) (synCopab x y ph))
      (synWbr A (synCopab x y ph) B)
      (synWa (.classMem A (synCvv)) (.classMem B (synCvv))) p0000 p0001
  have p0003 := @gSbcex (synWsbc B y ph) x A
  have p0004 := @gSpesbc (synWsbc B y ph) x A
  have p0005 := @gSbcex ph y B
  have p0006 := @gExlimiv (synWsbc B y ph) (.classMem B (synCvv)) x dv_cache_0001 p0005
  have p0007 :=
    @gSyl (synWsbc A x (synWsbc B y ph)) (synWex x (synWsbc B y ph))
      (.classMem B (synCvv)) p0004 p0006
  have p0008 :=
    @gJca (synWsbc A x (synWsbc B y ph)) (.classMem A (synCvv))
      (.classMem B (synCvv)) p0003 p0007
  have p0009 := @gOpeq1 (.cv z) A (.cv w)
  have p0010 :=
    @gEleq1d (.classEq (.cv z) A) (synCop (.cv z) (.cv w)) (synCop A (.cv w))
      (synCopab x y ph) p0009
  have p0011 := @gDfsbcq2 (synWsb w y ph) x z A
  have p0012 :=
    @gBibi12d (.classEq (.cv z) A)
      (.classMem (synCop (.cv z) (.cv w)) (synCopab x y ph))
      (.classMem (synCop A (.cv w)) (synCopab x y ph)) (synWsb z x (synWsb w y ph))
      (synWsbc A x (synWsb w y ph)) p0010 p0011
  have p0013 := @gOpeq2 (.cv w) B A
  have p0014 :=
    @gEleq1d (.classEq (.cv w) B) (synCop A (.cv w)) (synCop A B) (synCopab x y ph)
      p0013
  have p0015 := @gDfsbcq2 ph y w B
  have p0016 :=
    @gSbcbidv (.classEq (.cv w) B) (synWsb w y ph) (synWsbc B y ph) x A dv_cache_0002
      p0015
  have p0017 :=
    @gBibi12d (.classEq (.cv w) B) (.classMem (synCop A (.cv w)) (synCopab x y ph))
      (.classMem (synCop A B) (synCopab x y ph)) (synWsbc A x (synWsb w y ph))
      (synWsbc A x (synWsbc B y ph)) p0014 p0016
  have p0018 := @gNfopab1 ph x y
  have p0019 :=
    @gNfel2 x (synCop (.cv z) (.cv w)) (synCopab x y ph) dv_cache_0003 p0018
  have p0020 := @gNfs1v (synWsb w y ph) x z dv_cache_0004
  have p0021 :=
    @gNfbi (.classMem (synCop (.cv z) (.cv w)) (synCopab x y ph))
      (synWsb z x (synWsb w y ph)) x p0019 p0020
  have p0022 := @gOpeq1 (.cv x) (.cv z) (.cv w)
  have p0023_e00_recanon :
    Nominal.NPrf
      (.imp (.objEq x z) (.classEq (synCop (.cv x) (.cv w)) (synCop (.cv z) (.cv w)))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold synCop synCun synCnin synWnan synWa synCcompl synWrex synWex
          synCphi
        simp (config :=
          { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_class_cv]
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
        · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0022
  have p0023 :=
    @gEleq1d (.objEq x z) (synCop (.cv x) (.cv w)) (synCop (.cv z) (.cv w))
      (synCopab x y ph) p0023_e00_recanon
  have p0024 := @gSbequ12 (synWsb w y ph) x z
  have p0025 :=
    @gBibi12d (.objEq x z) (.classMem (synCop (.cv x) (.cv w)) (synCopab x y ph))
      (.classMem (synCop (.cv z) (.cv w)) (synCopab x y ph)) (synWsb w y ph)
      (synWsb z x (synWsb w y ph)) p0023 p0024
  have p0026 := @gNfopab2 ph x y
  have p0027 :=
    @gNfel2 y (synCop (.cv x) (.cv w)) (synCopab x y ph) dv_cache_0005 p0026
  have p0028 := @gNfs1v ph y w dv_cache_0006
  have p0029 :=
    @gNfbi (.classMem (synCop (.cv x) (.cv w)) (synCopab x y ph)) (synWsb w y ph) y
      p0027 p0028
  have p0030 := @gOpeq2 (.cv y) (.cv w) (.cv x)
  have p0031_e00_recanon :
    Nominal.NPrf
      (.imp (.objEq y w) (.classEq (synCop (.cv x) (.cv y)) (synCop (.cv x) (.cv w)))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold synCop synCun synCnin synWnan synWa synCcompl synWrex synWex
          synCphi
        simp (config :=
          { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_class_cv]
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
        · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0030
  have p0031 :=
    @gEleq1d (.objEq y w) (synCop (.cv x) (.cv y)) (synCop (.cv x) (.cv w))
      (synCopab x y ph) p0031_e00_recanon
  have p0032 := @gSbequ12 ph y w
  have p0033 :=
    @gBibi12d (.objEq y w) (.classMem (synCop (.cv x) (.cv y)) (synCopab x y ph))
      (.classMem (synCop (.cv x) (.cv w)) (synCopab x y ph)) ph (synWsb w y ph) p0031
      p0032
  have p0034 := @gOpabid ph x y
  have p0035 :=
    @gChvar (synWb (.classMem (synCop (.cv x) (.cv y)) (synCopab x y ph)) ph)
      (synWb (.classMem (synCop (.cv x) (.cv w)) (synCopab x y ph)) (synWsb w y ph)) y
      w p0029 p0033 p0034
  have p0036 :=
    @gChvar
      (synWb (.classMem (synCop (.cv x) (.cv w)) (synCopab x y ph)) (synWsb w y ph))
      (synWb (.classMem (synCop (.cv z) (.cv w)) (synCopab x y ph))
        (synWsb z x (synWsb w y ph)))
      x z p0021 p0025 p0035
  have p0037 :=
    @gVtocl2g
      (synWb (.classMem (synCop (.cv z) (.cv w)) (synCopab x y ph))
        (synWsb z x (synWsb w y ph)))
      (synWb (.classMem (synCop A (.cv w)) (synCopab x y ph))
        (synWsbc A x (synWsb w y ph)))
      (synWb (.classMem (synCop A B) (synCopab x y ph)) (synWsbc A x (synWsbc B y ph)))
      z w A B (synCvv) (synCvv) dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010
      dv_cache_0011 p0012 p0017 p0036
  have p0038 :=
    @gPm521nii (.classMem (synCop A B) (synCopab x y ph))
      (synWa (.classMem A (synCvv)) (.classMem B (synCvv)))
      (synWsbc A x (synWsbc B y ph)) p0002 p0008 p0037
  exact p0038

/-- Checked nominal proof certificate identified upstream as `g_opelopabga`. -/
@[expose]
noncomputable def gOpelopabga (ph : Wff) (ps : Wff) (x : Var) (y : Var) (A : Class)
    (B : Class) (V : Class) (W : Class) (dv_A_x : x ∉ A.fv) (dv_A_y : y ∉ A.fv)
    (dv_B_x : x ∉ B.fv) (dv_B_y : y ∉ B.fv) (dv_ps_x : x ∉ ps.fv) (dv_ps_y : y ∉ ps.fv)
    (dv_x_y : x ≠ y)
    (hyp_opelopabga_1 : Nominal.NPrf
        (.imp (synWa (.classEq (.cv x) A) (.classEq (.cv y) B)) (synWb ph ps))) :
    Nominal.NPrf
      (.imp (synWa (.classMem A V) (.classMem B W))
        (synWb (.classMem (synCop A B) (synCopab x y ph)) ps)) :=
  by
  have dv_cache_0001 : x ∉ ((synCop A B)).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cop, Finset.mem_union,
          dv_A_x, dv_B_x, or_false, not_false_eq_true])
  have dv_cache_0002 : y ∉ ((synCop A B)).fv :=
    by
    clear dv_cache_0001
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cop, Finset.mem_union,
          dv_A_y, dv_B_y, or_false, not_false_eq_true])
  have dv_cache_0003 : x ∉ (A).fv :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_A_x, not_false_eq_true])
  have dv_cache_0004 : y ∉ (A).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_A_y, not_false_eq_true])
  have dv_cache_0005 : x ∉ (B).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_B_x, not_false_eq_true])
  have dv_cache_0006 : y ∉ (B).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_B_y, not_false_eq_true])
  have dv_cache_0007 : x ∉ (ps).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_ps_x, not_false_eq_true])
  have dv_cache_0008 : y ∉ (ps).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_ps_y, not_false_eq_true])
  have dv_cache_0009 : x ≠ y :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008
    exact (show x ≠ y from (by exact dv_x_y))
  have p0000 := @gElopab ph x y (synCop A B) dv_cache_0001 dv_cache_0002
  have p0001 :=
    @gCopsex2g ph ps x y A B V W dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006
      dv_cache_0007 dv_cache_0008 dv_cache_0009 hyp_opelopabga_1
  have p0002 :=
    @gSyl5bb (.classMem (synCop A B) (synCopab x y ph))
      (synWex x (synWex y (synWa (.classEq (synCop A B) (synCop (.cv x) (.cv y))) ph)))
      (synWa (.classMem A V) (.classMem B W)) ps p0000 p0001
  exact p0002


end NFChoice.DirectNominalPrf.WPPReplay

end

/-! Certificates from `NominalWPPReplayChunk010Compact001Part040`. -/


section

namespace NFChoice.DirectNominalPrf.WPPReplay

open scoped Fol
open NFChoice.Foundation
open NFChoice.SemanticCore
open NFChoice.ReplaySupport
open NFChoice.Compiler.CompactSourceSyntax

/-- Checked nominal proof certificate identified upstream as `g_brabga`. -/
@[expose]
noncomputable def gBrabga (ph : Wff) (ps : Wff) (x : Var) (y : Var) (A : Class)
    (B : Class) (R : Class) (V : Class) (W : Class) (dv_A_x : x ∉ A.fv)
    (dv_A_y : y ∉ A.fv) (dv_B_x : x ∉ B.fv) (dv_B_y : y ∉ B.fv) (dv_ps_x : x ∉ ps.fv)
    (dv_ps_y : y ∉ ps.fv) (dv_x_y : x ≠ y)
    (hyp_opelopabga_1 : Nominal.NPrf
        (.imp (synWa (.classEq (.cv x) A) (.classEq (.cv y) B)) (synWb ph ps)))
    (hyp_brabga_2 : Nominal.NPrf (.classEq R (synCopab x y ph))) :
    Nominal.NPrf
      (.imp (synWa (.classMem A V) (.classMem B W)) (synWb (synWbr A R B) ps)) :=
  by
  have dv_cache_0001 : x ∉ (A).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_A_x, not_false_eq_true])
  have dv_cache_0002 : y ∉ (A).fv :=
    by
    clear dv_cache_0001
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_A_y, not_false_eq_true])
  have dv_cache_0003 : x ∉ (B).fv :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_B_x, not_false_eq_true])
  have dv_cache_0004 : y ∉ (B).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_B_y, not_false_eq_true])
  have dv_cache_0005 : x ∉ (ps).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_ps_x, not_false_eq_true])
  have dv_cache_0006 : y ∉ (ps).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_ps_y, not_false_eq_true])
  have dv_cache_0007 : x ≠ y :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006
    exact (show x ≠ y from (by exact dv_x_y))
  have p0000 := (Nominal.biimpRefl (synWbr A R B))
  have p0001 := @gEleq2i R (synCopab x y ph) (synCop A B) hyp_brabga_2
  have p0002 :=
    @gBitri (synWbr A R B) (.classMem (synCop A B) R)
      (.classMem (synCop A B) (synCopab x y ph)) p0000 p0001
  have p0003 :=
    @gOpelopabga ph ps x y A B V W dv_cache_0001 dv_cache_0002 dv_cache_0003
      dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 hyp_opelopabga_1
  have p0004 :=
    @gSyl5bb (synWbr A R B) (.classMem (synCop A B) (synCopab x y ph))
      (synWa (.classMem A V) (.classMem B W)) ps p0002 p0003
  exact p0004

/-- Checked nominal proof certificate identified upstream as `g_opelopaba`. -/
@[expose]
noncomputable def gOpelopaba (ph : Wff) (ps : Wff) (x : Var) (y : Var) (A : Class)
    (B : Class) (dv_A_x : x ∉ A.fv) (dv_A_y : y ∉ A.fv) (dv_B_x : x ∉ B.fv)
    (dv_B_y : y ∉ B.fv) (dv_ps_x : x ∉ ps.fv) (dv_ps_y : y ∉ ps.fv) (dv_x_y : x ≠ y)
    (hyp_opelopaba_1 : Nominal.NPrf (.classMem A (synCvv)))
    (hyp_opelopaba_2 : Nominal.NPrf (.classMem B (synCvv)))
    (hyp_opelopaba_3 : Nominal.NPrf
        (.imp (synWa (.classEq (.cv x) A) (.classEq (.cv y) B)) (synWb ph ps))) :
    Nominal.NPrf (synWb (.classMem (synCop A B) (synCopab x y ph)) ps) :=
  by
  have dv_cache_0001 : x ∉ (A).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_A_x, not_false_eq_true])
  have dv_cache_0002 : y ∉ (A).fv :=
    by
    clear dv_cache_0001
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_A_y, not_false_eq_true])
  have dv_cache_0003 : x ∉ (B).fv :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_B_x, not_false_eq_true])
  have dv_cache_0004 : y ∉ (B).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_B_y, not_false_eq_true])
  have dv_cache_0005 : x ∉ (ps).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_ps_x, not_false_eq_true])
  have dv_cache_0006 : y ∉ (ps).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_ps_y, not_false_eq_true])
  have dv_cache_0007 : x ≠ y :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006
    exact (show x ≠ y from (by exact dv_x_y))
  have p0000 :=
    @gOpelopabga ph ps x y A B (synCvv) (synCvv) dv_cache_0001 dv_cache_0002
      dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007
      hyp_opelopaba_3
  have p0001 :=
    @gMp2an (.classMem A (synCvv)) (.classMem B (synCvv))
      (synWb (.classMem (synCop A B) (synCopab x y ph)) ps) hyp_opelopaba_1
      hyp_opelopaba_2 p0000
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_braba`. -/
@[expose]
noncomputable def gBraba (ph : Wff) (ps : Wff) (x : Var) (y : Var) (A : Class)
    (B : Class) (R : Class) (dv_A_x : x ∉ A.fv) (dv_A_y : y ∉ A.fv) (dv_B_x : x ∉ B.fv)
    (dv_B_y : y ∉ B.fv) (dv_ps_x : x ∉ ps.fv) (dv_ps_y : y ∉ ps.fv) (dv_x_y : x ≠ y)
    (hyp_opelopaba_1 : Nominal.NPrf (.classMem A (synCvv)))
    (hyp_opelopaba_2 : Nominal.NPrf (.classMem B (synCvv)))
    (hyp_opelopaba_3 : Nominal.NPrf
        (.imp (synWa (.classEq (.cv x) A) (.classEq (.cv y) B)) (synWb ph ps)))
    (hyp_braba_4 : Nominal.NPrf (.classEq R (synCopab x y ph))) :
    Nominal.NPrf (synWb (synWbr A R B) ps) :=
  by
  have dv_cache_0001 : x ∉ (A).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_A_x, not_false_eq_true])
  have dv_cache_0002 : y ∉ (A).fv :=
    by
    clear dv_cache_0001
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_A_y, not_false_eq_true])
  have dv_cache_0003 : x ∉ (B).fv :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_B_x, not_false_eq_true])
  have dv_cache_0004 : y ∉ (B).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_B_y, not_false_eq_true])
  have dv_cache_0005 : x ∉ (ps).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_ps_x, not_false_eq_true])
  have dv_cache_0006 : y ∉ (ps).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_ps_y, not_false_eq_true])
  have dv_cache_0007 : x ≠ y :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006
    exact (show x ≠ y from (by exact dv_x_y))
  have p0000 :=
    @gBrabga ph ps x y A B R (synCvv) (synCvv) dv_cache_0001 dv_cache_0002
      dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007
      hyp_opelopaba_3 hyp_braba_4
  have p0001 :=
    @gMp2an (.classMem A (synCvv)) (.classMem B (synCvv)) (synWb (synWbr A R B) ps)
      hyp_opelopaba_1 hyp_opelopaba_2 p0000
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_opelopabg`. -/
@[expose]
noncomputable def gOpelopabg (ph : Wff) (ps : Wff) (ch : Wff) (x : Var) (y : Var)
    (A : Class) (B : Class) (V : Class) (W : Class) (dv_A_x : x ∉ A.fv)
    (dv_A_y : y ∉ A.fv) (dv_B_x : x ∉ B.fv) (dv_B_y : y ∉ B.fv) (dv_ch_x : x ∉ ch.fv)
    (dv_ch_y : y ∉ ch.fv) (dv_x_y : x ≠ y)
    (hyp_opelopabg_1 : Nominal.NPrf (.imp (.classEq (.cv x) A) (synWb ph ps)))
    (hyp_opelopabg_2 : Nominal.NPrf (.imp (.classEq (.cv y) B) (synWb ps ch))) :
    Nominal.NPrf
      (.imp (synWa (.classMem A V) (.classMem B W))
        (synWb (.classMem (synCop A B) (synCopab x y ph)) ch)) :=
  by
  have dv_cache_0001 : x ∉ (A).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_A_x, not_false_eq_true])
  have dv_cache_0002 : y ∉ (A).fv :=
    by
    clear dv_cache_0001
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_A_y, not_false_eq_true])
  have dv_cache_0003 : x ∉ (B).fv :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_B_x, not_false_eq_true])
  have dv_cache_0004 : y ∉ (B).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_B_y, not_false_eq_true])
  have dv_cache_0005 : x ∉ (ch).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_ch_x, not_false_eq_true])
  have dv_cache_0006 : y ∉ (ch).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_ch_y, not_false_eq_true])
  have dv_cache_0007 : x ≠ y :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006
    exact (show x ≠ y from (by exact dv_x_y))
  have p0000 :=
    @gSylan9bb (.classEq (.cv x) A) ph ps (.classEq (.cv y) B) ch hyp_opelopabg_1
      hyp_opelopabg_2
  have p0001 :=
    @gOpelopabga ph ch x y A B V W dv_cache_0001 dv_cache_0002 dv_cache_0003
      dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 p0000
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_brabg`. -/
@[expose]
noncomputable def gBrabg (ph : Wff) (ps : Wff) (ch : Wff) (x : Var) (y : Var) (A : Class)
    (B : Class) (C : Class) (D : Class) (R : Class) (dv_A_x : x ∉ A.fv)
    (dv_A_y : y ∉ A.fv) (dv_B_x : x ∉ B.fv) (dv_B_y : y ∉ B.fv) (dv_ch_x : x ∉ ch.fv)
    (dv_ch_y : y ∉ ch.fv) (dv_x_y : x ≠ y)
    (hyp_opelopabg_1 : Nominal.NPrf (.imp (.classEq (.cv x) A) (synWb ph ps)))
    (hyp_opelopabg_2 : Nominal.NPrf (.imp (.classEq (.cv y) B) (synWb ps ch)))
    (hyp_brabg_5 : Nominal.NPrf (.classEq R (synCopab x y ph))) :
    Nominal.NPrf
      (.imp (synWa (.classMem A C) (.classMem B D)) (synWb (synWbr A R B) ch)) :=
  by
  have dv_cache_0001 : x ∉ (A).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_A_x, not_false_eq_true])
  have dv_cache_0002 : y ∉ (A).fv :=
    by
    clear dv_cache_0001
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_A_y, not_false_eq_true])
  have dv_cache_0003 : x ∉ (B).fv :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_B_x, not_false_eq_true])
  have dv_cache_0004 : y ∉ (B).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_B_y, not_false_eq_true])
  have dv_cache_0005 : x ∉ (ch).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_ch_x, not_false_eq_true])
  have dv_cache_0006 : y ∉ (ch).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_ch_y, not_false_eq_true])
  have dv_cache_0007 : x ≠ y :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006
    exact (show x ≠ y from (by exact dv_x_y))
  have p0000 :=
    @gSylan9bb (.classEq (.cv x) A) ph ps (.classEq (.cv y) B) ch hyp_opelopabg_1
      hyp_opelopabg_2
  have p0001 :=
    @gBrabga ph ch x y A B R C D dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
      dv_cache_0005 dv_cache_0006 dv_cache_0007 p0000 hyp_brabg_5
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_opelopab`. -/
@[expose]
noncomputable def gOpelopab (ph : Wff) (ps : Wff) (ch : Wff) (x : Var) (y : Var)
    (A : Class) (B : Class) (dv_A_x : x ∉ A.fv) (dv_A_y : y ∉ A.fv) (dv_B_x : x ∉ B.fv)
    (dv_B_y : y ∉ B.fv) (dv_ch_x : x ∉ ch.fv) (dv_ch_y : y ∉ ch.fv) (dv_x_y : x ≠ y)
    (hyp_opelopab_1 : Nominal.NPrf (.classMem A (synCvv)))
    (hyp_opelopab_2 : Nominal.NPrf (.classMem B (synCvv)))
    (hyp_opelopab_3 : Nominal.NPrf (.imp (.classEq (.cv x) A) (synWb ph ps)))
    (hyp_opelopab_4 : Nominal.NPrf (.imp (.classEq (.cv y) B) (synWb ps ch))) :
    Nominal.NPrf (synWb (.classMem (synCop A B) (synCopab x y ph)) ch) :=
  by
  have dv_cache_0001 : x ∉ (A).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_A_x, not_false_eq_true])
  have dv_cache_0002 : y ∉ (A).fv :=
    by
    clear dv_cache_0001
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_A_y, not_false_eq_true])
  have dv_cache_0003 : x ∉ (B).fv :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_B_x, not_false_eq_true])
  have dv_cache_0004 : y ∉ (B).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_B_y, not_false_eq_true])
  have dv_cache_0005 : x ∉ (ch).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_ch_x, not_false_eq_true])
  have dv_cache_0006 : y ∉ (ch).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_ch_y, not_false_eq_true])
  have dv_cache_0007 : x ≠ y :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006
    exact (show x ≠ y from (by exact dv_x_y))
  have p0000 :=
    @gOpelopabg ph ps ch x y A B (synCvv) (synCvv) dv_cache_0001 dv_cache_0002
      dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 hyp_opelopab_3
      hyp_opelopab_4
  have p0001 :=
    @gMp2an (.classMem A (synCvv)) (.classMem B (synCvv))
      (synWb (.classMem (synCop A B) (synCopab x y ph)) ch) hyp_opelopab_1
      hyp_opelopab_2 p0000
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_brab`. -/
@[expose]
noncomputable def gBrab (ph : Wff) (ps : Wff) (ch : Wff) (x : Var) (y : Var) (A : Class)
    (B : Class) (R : Class) (dv_A_x : x ∉ A.fv) (dv_A_y : y ∉ A.fv) (dv_B_x : x ∉ B.fv)
    (dv_B_y : y ∉ B.fv) (dv_ch_x : x ∉ ch.fv) (dv_ch_y : y ∉ ch.fv) (dv_x_y : x ≠ y)
    (hyp_opelopab_1 : Nominal.NPrf (.classMem A (synCvv)))
    (hyp_opelopab_2 : Nominal.NPrf (.classMem B (synCvv)))
    (hyp_opelopab_3 : Nominal.NPrf (.imp (.classEq (.cv x) A) (synWb ph ps)))
    (hyp_opelopab_4 : Nominal.NPrf (.imp (.classEq (.cv y) B) (synWb ps ch)))
    (hyp_brab_5 : Nominal.NPrf (.classEq R (synCopab x y ph))) :
    Nominal.NPrf (synWb (synWbr A R B) ch) :=
  by
  have dv_cache_0001 : x ∉ (A).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_A_x, not_false_eq_true])
  have dv_cache_0002 : y ∉ (A).fv :=
    by
    clear dv_cache_0001
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_A_y, not_false_eq_true])
  have dv_cache_0003 : x ∉ (B).fv :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_B_x, not_false_eq_true])
  have dv_cache_0004 : y ∉ (B).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_B_y, not_false_eq_true])
  have dv_cache_0005 : x ∉ (ch).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_ch_x, not_false_eq_true])
  have dv_cache_0006 : y ∉ (ch).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_ch_y, not_false_eq_true])
  have dv_cache_0007 : x ≠ y :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006
    exact (show x ≠ y from (by exact dv_x_y))
  have p0000 :=
    @gBrabg ph ps ch x y A B (synCvv) (synCvv) R dv_cache_0001 dv_cache_0002
      dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 hyp_opelopab_3
      hyp_opelopab_4 hyp_brab_5
  have p0001 :=
    @gMp2an (.classMem A (synCvv)) (.classMem B (synCvv)) (synWb (synWbr A R B) ch)
      hyp_opelopab_1 hyp_opelopab_2 p0000
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_ssopab2`. -/
@[expose]
noncomputable def gSsopab2 (ph : Wff) (ps : Wff) (x : Var) (y : Var) :
    Nominal.NPrf
      (.imp (.all x (.all y (.imp ph ps))) (synWss (synCopab x y ph) (synCopab x y ps))) :=
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
  have dv_cache_0001 : z ∉ ((Wff.all x (.all y (.imp ph ps)))).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_all,
          NFChoice.Compiler.CoreFVSimp.fv_wff_imp, Finset.mem_union, Finset.mem_erase,
          fresh_z_not_ph, fresh_z_not_ps, or_false, and_false, not_false_eq_true])
  have dv_cache_0002 : z ∉ (ph).fv :=
    by
    clear dv_cache_0001
    exact
      (by
        have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_z_not_ph, not_false_eq_true])
  have dv_cache_0003 : x ≠ z :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact (show x ≠ z from (by exact fresh_x_ne_z))
  have dv_cache_0004 : y ≠ z :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact (show y ≠ z from (by exact fresh_y_ne_z))
  have dv_cache_0005 : z ∉ (ps).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact
      (by
        have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_z_not_ps, not_false_eq_true])
  have p0000 := @gNfa1 (.all y (.imp ph ps)) x
  have p0001 := @gNfa1 (.imp ph ps) y
  have p0002 := @gSp (.imp ph ps) y
  have p0003 :=
    @gAnim2d (.all y (.imp ph ps)) ph ps (.classEq (.cv z) (synCop (.cv x) (.cv y)))
      p0002
  have p0004 :=
    @gEximd (.all y (.imp ph ps))
      (synWa (.classEq (.cv z) (synCop (.cv x) (.cv y))) ph)
      (synWa (.classEq (.cv z) (synCop (.cv x) (.cv y))) ps) y p0001 p0003
  have p0005 :=
    @gSps (.all y (.imp ph ps))
      (.imp (synWex y (synWa (.classEq (.cv z) (synCop (.cv x) (.cv y))) ph))
        (synWex y (synWa (.classEq (.cv z) (synCop (.cv x) (.cv y))) ps)))
      x p0004
  have p0006 :=
    @gEximd (.all x (.all y (.imp ph ps)))
      (synWex y (synWa (.classEq (.cv z) (synCop (.cv x) (.cv y))) ph))
      (synWex y (synWa (.classEq (.cv z) (synCop (.cv x) (.cv y))) ps)) x p0000 p0005
  have p0007 :=
    @gSs2abdv (.all x (.all y (.imp ph ps)))
      (synWex x (synWex y (synWa (.classEq (.cv z) (synCop (.cv x) (.cv y))) ph)))
      (synWex x (synWex y (synWa (.classEq (.cv z) (synCop (.cv x) (.cv y))) ps))) z
      dv_cache_0001 p0006
  have p0008 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominalDfOpab ph x y z
      dv_cache_0002 dv_cache_0003 dv_cache_0004
  have p0009 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominalDfOpab ps x y z
      dv_cache_0005 dv_cache_0003 dv_cache_0004
  have p0010 :=
    @gN3sstr4g (.all x (.all y (.imp ph ps)))
      (.cab z (synWex x (synWex y (synWa (.classEq (.cv z) (synCop (.cv x) (.cv y))) ph))))
      (.cab z (synWex x (synWex y (synWa (.classEq (.cv z) (synCop (.cv x) (.cv y))) ps))))
      (synCopab x y ph) (synCopab x y ps) p0007 p0008 p0009
  exact p0010

/-- Checked nominal proof certificate identified upstream as `g_ssopab2dv`. -/
@[expose]
noncomputable def gSsopab2dv (ph : Wff) (ps : Wff) (ch : Wff) (x : Var) (y : Var)
    (dv_ph_x : x ∉ ph.fv) (dv_ph_y : y ∉ ph.fv)
    (hyp_ssopab2dv_1 : Nominal.NPrf (.imp ph (.imp ps ch))) :
    Nominal.NPrf (.imp ph (synWss (synCopab x y ps) (synCopab x y ch))) :=
  by
  have dv_cache_0001 : x ∉ (ph).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_ph_x, not_false_eq_true])
  have dv_cache_0002 : y ∉ (ph).fv :=
    by
    clear dv_cache_0001
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_ph_y, not_false_eq_true])
  have p0000 :=
    @gAlrimivv ph (.imp ps ch) x y dv_cache_0001 dv_cache_0002 hyp_ssopab2dv_1
  have p0001 := @gSsopab2 ps ch x y
  have p0002 :=
    @gSyl ph (.all x (.all y (.imp ps ch)))
      (synWss (synCopab x y ps) (synCopab x y ch)) p0000 p0001
  exact p0002


end NFChoice.DirectNominalPrf.WPPReplay

end

/-! Certificates from `NominalWPPReplayChunk010Compact001Part041`. -/


section

namespace NFChoice.DirectNominalPrf.WPPReplay

open scoped Fol
open NFChoice.Foundation
open NFChoice.SemanticCore
open NFChoice.ReplaySupport
open NFChoice.Compiler.CompactSourceSyntax

/-- Checked nominal proof certificate identified upstream as `g_setconslem1`. -/
@[expose]
noncomputable def gSetconslem1 (x : Var) (A : Class) (B : Class) (dv_A_x : x ∉ A.fv)
    (dv_B_x : x ∉ B.fv) (hyp_setconslem1_1 : Nominal.NPrf (.classMem A (synCvv)))
    (hyp_setconslem1_2 : Nominal.NPrf (.classMem B (synCvv))) :
    Nominal.NPrf
      (synWb (.classMem (synCopk (synCsn A) B) (synCcomk (synCssetk) (synCsik (synCcnvk
                (synCimagek (synCun (synCin (synCimagek (synCimak (synCdif (synCins3k
                              (synCcompl (synCimak (synCin (synCins3k (synCssetk))
                                    (synCins2k (synCssetk)))
                                  (synCpw1 (synCpw1 (synC1c)))))) (synCimak
                              (synCsymdif (synCins2k (synCins2k (synCssetk)))
                                (synCun (synCins2k (synCins3k (synCssetk)))
                                  (synCins3k (synCsik (synCsik (synCssetk))))))
                              (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))
                          (synCpw1 (synCpw1 (synC1c))))) (synCxpk (synCnnc) (synCvv)))
                    (synCin (synCidk) (synCxpk (synCcompl (synCnnc)) (synCvv)))))))))
        (synWrex x B (.classEq A (synCphi (.cv x))))) :=
  by
  let proofSupport : Finset Var := ({ x } : Finset Var) ∪ A.fv ∪ B.fv
  let t : Var := freshVar proofSupport 0
  let z : Var := freshVar proofSupport 1
  have fresh_t : t ∉ proofSupport :=
    by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_t_ne_x : t ≠ x := by
    intro h
    exact
      fresh_t
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_singleton.mpr h)))
  have fresh_x_ne_t : x ≠ t := Ne.symm fresh_t_ne_x
  have fresh_t_not_A : t ∉ A.fv := by
    intro h
    exact fresh_t (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_t_not_B : t ∉ B.fv := by
    intro h
    exact fresh_t (Finset.mem_union_right _ (h))
  have fresh_z : z ∉ proofSupport :=
    by
    change freshVar proofSupport 1 ∉ proofSupport
    exact freshVar_not_mem proofSupport 1
  have fresh_z_ne_x : z ≠ x := by
    intro h
    exact
      fresh_z
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_singleton.mpr h)))
  have fresh_z_not_A : z ∉ A.fv := by
    intro h
    exact fresh_z (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_t_ne_z : t ≠ z :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have fresh_z_ne_t : z ≠ t := Ne.symm fresh_t_ne_z
  have dv_cache_0001 : z ∉ ((synCsn A)).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, fresh_z_not_A,
          not_false_eq_true])
  have dv_cache_0002 : x ∉ ((synCsn A)).fv :=
    by
    clear dv_cache_0001
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, dv_A_x,
          not_false_eq_true])
  have dv_cache_0003 : z ∉ ((Class.cv t)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact
      (by
        have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_z_ne_t, not_false_eq_true])
  have dv_cache_0004 : x ∉ ((Class.cv t)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_x_ne_t, not_false_eq_true])
  have dv_cache_0005 :
    z ∉
      ((synCcnvk (synCimagek (synCun (synCin (synCimagek (synCimak (synCdif (synCins3k
                        (synCcompl (synCimak
                            (synCin (synCins3k (synCssetk)) (synCins2k (synCssetk)))
                            (synCpw1 (synCpw1 (synC1c)))))) (synCimak
                        (synCsymdif (synCins2k (synCins2k (synCssetk)))
                          (synCun (synCins2k (synCins3k (synCssetk)))
                            (synCins3k (synCsik (synCsik (synCssetk))))))
                        (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))
                    (synCpw1 (synCpw1 (synC1c))))) (synCxpk (synCnnc) (synCvv)))
              (synCin (synCidk) (synCxpk (synCcompl (synCnnc)) (synCvv))))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact
      (by
        have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnvk,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cimagek,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cun,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cimak,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdif,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins3k,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccompl,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cssetk,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins2k,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csymdif,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csik,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxpk,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cidk, Finset.mem_union,
          compact_fv_not_mem_empty, or_false, not_false_eq_true])
  have dv_cache_0006 :
    x ∉
      ((synCcnvk (synCimagek (synCun (synCin (synCimagek (synCimak (synCdif (synCins3k
                        (synCcompl (synCimak
                            (synCin (synCins3k (synCssetk)) (synCins2k (synCssetk)))
                            (synCpw1 (synCpw1 (synC1c)))))) (synCimak
                        (synCsymdif (synCins2k (synCins2k (synCssetk)))
                          (synCun (synCins2k (synCins3k (synCssetk)))
                            (synCins3k (synCsik (synCsik (synCssetk))))))
                        (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))
                    (synCpw1 (synCpw1 (synC1c))))) (synCxpk (synCnnc) (synCvv)))
              (synCin (synCidk) (synCxpk (synCcompl (synCnnc)) (synCvv))))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnvk,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cimagek,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cun,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cimak,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdif,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins3k,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccompl,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cssetk,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins2k,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csymdif,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csik,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxpk,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cidk, Finset.mem_union,
          compact_fv_not_mem_empty, or_false, not_false_eq_true])
  have dv_cache_0007 : z ≠ x :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006
    exact (show z ≠ x from (by exact fresh_z_ne_x))
  have dv_cache_0008 : z ∉ (A).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007
    exact
      (by
        have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_z_not_A, not_false_eq_true])
  have dv_cache_0009 :
    z ∉
      ((synWa (.classEq (.cv t) (synCsn (.cv x))) (.classMem (synCopk A (.cv x)) (synCcnvk
              (synCimagek (synCun (synCin (synCimagek (synCimak (synCdif (synCins3k
                            (synCcompl (synCimak (synCin (synCins3k (synCssetk))
                                  (synCins2k (synCssetk))) (synCpw1 (synCpw1 (synC1c))))))
                          (synCimak (synCsymdif (synCins2k (synCins2k (synCssetk)))
                              (synCun (synCins2k (synCins3k (synCssetk)))
                                (synCins3k (synCsik (synCsik (synCssetk))))))
                            (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))
                        (synCpw1 (synCpw1 (synC1c))))) (synCxpk (synCnnc) (synCvv)))
                  (synCin (synCidk) (synCxpk (synCcompl (synCnnc)) (synCvv))))))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008
    exact
      (by
        have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_copk,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnvk,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cimagek,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cun,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cimak,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdif,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins3k,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccompl,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cssetk,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins2k,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csymdif,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csik,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxpk,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cidk, Finset.mem_union,
          Finset.mem_singleton, fresh_z_ne_t, fresh_z_ne_x, fresh_z_not_A,
          compact_fv_not_mem_empty, or_false, not_false_eq_true])
  have dv_cache_0010 : x ∉ ((Wff.classMem (synCopk (.cv t) B) (synCssetk))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_copk,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cssetk, Finset.mem_union,
          Finset.mem_singleton, fresh_x_ne_t, dv_B_x, compact_fv_not_mem_empty, or_false,
          not_false_eq_true])
  have dv_cache_0011 : t ∉ ((synCsn (.cv x))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010
    exact
      (by
        have compact_fv_not_mem_empty : t ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton, fresh_t_ne_x,
          not_false_eq_true])
  have dv_cache_0012 :
    t ∉
      ((synWa (.classMem (synCopk A (.cv x)) (synCcnvk (synCimagek (synCun (synCin
                    (synCimagek (synCimak (synCdif (synCins3k (synCcompl (synCimak
                                (synCin (synCins3k (synCssetk)) (synCins2k (synCssetk)))
                                (synCpw1 (synCpw1 (synC1c)))))) (synCimak
                            (synCsymdif (synCins2k (synCins2k (synCssetk)))
                              (synCun (synCins2k (synCins3k (synCssetk)))
                                (synCins3k (synCsik (synCsik (synCssetk))))))
                            (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))
                        (synCpw1 (synCpw1 (synC1c))))) (synCxpk (synCnnc) (synCvv)))
                  (synCin (synCidk) (synCxpk (synCcompl (synCnnc)) (synCvv)))))))
          (.classMem (synCopk (synCsn (.cv x)) B) (synCssetk)))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
    exact
      (by
        have compact_fv_not_mem_empty : t ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_copk,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnvk,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cimagek,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cun,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cimak,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdif,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins3k,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccompl,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cssetk,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins2k,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csymdif,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csik,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxpk,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cidk,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, Finset.mem_union,
          Finset.mem_singleton, fresh_t_not_A, fresh_t_ne_x, fresh_t_not_B,
          compact_fv_not_mem_empty, or_false, not_false_eq_true])
  have dv_cache_0013 : t ∉ ((synCsn A)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012
    exact
      (by
        have compact_fv_not_mem_empty : t ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, fresh_t_not_A,
          not_false_eq_true])
  have dv_cache_0014 : t ∉ (B).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013
    exact
      (by
        have compact_fv_not_mem_empty : t ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_t_not_B, not_false_eq_true])
  have dv_cache_0015 : t ∉ ((synCssetk)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014
    exact
      (by
        have compact_fv_not_mem_empty : t ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cssetk,
          compact_fv_not_mem_empty, not_false_eq_true])
  have dv_cache_0016 :
    t ∉
      ((synCsik (synCcnvk (synCimagek (synCun (synCin (synCimagek (synCimak (synCdif
                        (synCins3k (synCcompl (synCimak (synCin (synCins3k (synCssetk))
                                (synCins2k (synCssetk))) (synCpw1 (synCpw1 (synC1c))))))
                        (synCimak (synCsymdif (synCins2k (synCins2k (synCssetk)))
                            (synCun (synCins2k (synCins3k (synCssetk)))
                              (synCins3k (synCsik (synCsik (synCssetk))))))
                          (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))
                      (synCpw1 (synCpw1 (synC1c))))) (synCxpk (synCnnc) (synCvv)))
                (synCin (synCidk) (synCxpk (synCcompl (synCnnc)) (synCvv)))))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015
    exact
      (by
        have compact_fv_not_mem_empty : t ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csik,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnvk,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cimagek,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cun,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cimak,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdif,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins3k,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccompl,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cssetk,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins2k,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csymdif,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxpk,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cidk, Finset.mem_union,
          compact_fv_not_mem_empty, or_false, not_false_eq_true])
  have p0000 := @gSnex A
  have p0001 := @gVex t
  have p0002 :=
    @gOpkelsikg z x (synCsn A) (.cv t)
      (synCcnvk (synCimagek (synCun (synCin (synCimagek (synCimak (synCdif (synCins3k
                      (synCcompl (synCimak
                          (synCin (synCins3k (synCssetk)) (synCins2k (synCssetk)))
                          (synCpw1 (synCpw1 (synC1c)))))) (synCimak
                      (synCsymdif (synCins2k (synCins2k (synCssetk)))
                        (synCun (synCins2k (synCins3k (synCssetk)))
                          (synCins3k (synCsik (synCsik (synCssetk))))))
                      (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))
                  (synCpw1 (synCpw1 (synC1c))))) (synCxpk (synCnnc) (synCvv)))
            (synCin (synCidk) (synCxpk (synCcompl (synCnnc)) (synCvv))))))
      (synCvv) (synCvv) dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
      dv_cache_0005 dv_cache_0006 dv_cache_0007
  have p0003 :=
    @gMp2an (.classMem (synCsn A) (synCvv)) (.classMem (.cv t) (synCvv))
      (synWb (.classMem (synCopk (synCsn A) (.cv t)) (synCsik (synCcnvk (synCimagek
                (synCun (synCin (synCimagek (synCimak (synCdif (synCins3k (synCcompl
                              (synCimak (synCin (synCins3k (synCssetk))
                                  (synCins2k (synCssetk))) (synCpw1 (synCpw1 (synC1c))))))
                          (synCimak (synCsymdif (synCins2k (synCins2k (synCssetk)))
                              (synCun (synCins2k (synCins3k (synCssetk)))
                                (synCins3k (synCsik (synCsik (synCssetk))))))
                            (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))
                        (synCpw1 (synCpw1 (synC1c))))) (synCxpk (synCnnc) (synCvv)))
                  (synCin (synCidk) (synCxpk (synCcompl (synCnnc)) (synCvv))))))))
        (synWex z (synWex x (synW3a (.classEq (synCsn A) (synCsn (.cv z)))
              (.classEq (.cv t) (synCsn (.cv x))) (.classMem (synCopk (.cv z) (.cv x))
                (synCcnvk (synCimagek (synCun (synCin (synCimagek (synCimak (synCdif
                              (synCins3k (synCcompl (synCimak
                                    (synCin (synCins3k (synCssetk))
                                      (synCins2k (synCssetk)))
                                    (synCpw1 (synCpw1 (synC1c)))))) (synCimak
                                (synCsymdif (synCins2k (synCins2k (synCssetk)))
                                  (synCun (synCins2k (synCins3k (synCssetk)))
                                    (synCins3k (synCsik (synCsik (synCssetk))))))
                                (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))
                            (synCpw1 (synCpw1 (synC1c))))) (synCxpk (synCnnc) (synCvv)))
                      (synCin (synCidk) (synCxpk (synCcompl (synCnnc)) (synCvv)))))))))))
      p0000 p0001 p0002
  have p0004 :=
    @gExcom
      (synW3a (.classEq (synCsn A) (synCsn (.cv z))) (.classEq (.cv t) (synCsn (.cv x)))
        (.classMem (synCopk (.cv z) (.cv x)) (synCcnvk (synCimagek (synCun (synCin
                  (synCimagek (synCimak (synCdif (synCins3k (synCcompl (synCimak
                              (synCin (synCins3k (synCssetk)) (synCins2k (synCssetk)))
                              (synCpw1 (synCpw1 (synC1c)))))) (synCimak
                          (synCsymdif (synCins2k (synCins2k (synCssetk)))
                            (synCun (synCins2k (synCins3k (synCssetk)))
                              (synCins3k (synCsik (synCsik (synCssetk))))))
                          (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))
                      (synCpw1 (synCpw1 (synC1c))))) (synCxpk (synCnnc) (synCvv)))
                (synCin (synCidk) (synCxpk (synCcompl (synCnnc)) (synCvv))))))))
      z x
  have p0005 :=
    @gN3anass (.classEq (synCsn A) (synCsn (.cv z)))
      (.classEq (.cv t) (synCsn (.cv x)))
      (.classMem (synCopk (.cv z) (.cv x)) (synCcnvk (synCimagek (synCun (synCin
                (synCimagek (synCimak (synCdif (synCins3k (synCcompl (synCimak
                            (synCin (synCins3k (synCssetk)) (synCins2k (synCssetk)))
                            (synCpw1 (synCpw1 (synC1c)))))) (synCimak
                        (synCsymdif (synCins2k (synCins2k (synCssetk)))
                          (synCun (synCins2k (synCins3k (synCssetk)))
                            (synCins3k (synCsik (synCsik (synCssetk))))))
                        (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))
                    (synCpw1 (synCpw1 (synC1c))))) (synCxpk (synCnnc) (synCvv)))
              (synCin (synCidk) (synCxpk (synCcompl (synCnnc)) (synCvv)))))))
  have p0006 := @gEqcom (synCsn A) (synCsn (.cv z))
  have p0007 := @gVex z
  have p0008 := @gSneqb (.cv z) A p0007
  have p0009 :=
    @gBitri (.classEq (synCsn A) (synCsn (.cv z)))
      (.classEq (synCsn (.cv z)) (synCsn A)) (.classEq (.cv z) A) p0006 p0008
  have p0010 :=
    @gAnbi1i (.classEq (synCsn A) (synCsn (.cv z))) (.classEq (.cv z) A)
      (synWa (.classEq (.cv t) (synCsn (.cv x))) (.classMem (synCopk (.cv z) (.cv x))
          (synCcnvk (synCimagek (synCun (synCin (synCimagek (synCimak (synCdif
                        (synCins3k (synCcompl (synCimak (synCin (synCins3k (synCssetk))
                                (synCins2k (synCssetk))) (synCpw1 (synCpw1 (synC1c))))))
                        (synCimak (synCsymdif (synCins2k (synCins2k (synCssetk)))
                            (synCun (synCins2k (synCins3k (synCssetk)))
                              (synCins3k (synCsik (synCsik (synCssetk))))))
                          (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))
                      (synCpw1 (synCpw1 (synC1c))))) (synCxpk (synCnnc) (synCvv)))
                (synCin (synCidk) (synCxpk (synCcompl (synCnnc)) (synCvv))))))))
      p0009
  have p0011 :=
    @gBitri
      (synW3a (.classEq (synCsn A) (synCsn (.cv z))) (.classEq (.cv t) (synCsn (.cv x)))
        (.classMem (synCopk (.cv z) (.cv x)) (synCcnvk (synCimagek (synCun (synCin
                  (synCimagek (synCimak (synCdif (synCins3k (synCcompl (synCimak
                              (synCin (synCins3k (synCssetk)) (synCins2k (synCssetk)))
                              (synCpw1 (synCpw1 (synC1c)))))) (synCimak
                          (synCsymdif (synCins2k (synCins2k (synCssetk)))
                            (synCun (synCins2k (synCins3k (synCssetk)))
                              (synCins3k (synCsik (synCsik (synCssetk))))))
                          (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))
                      (synCpw1 (synCpw1 (synC1c))))) (synCxpk (synCnnc) (synCvv)))
                (synCin (synCidk) (synCxpk (synCcompl (synCnnc)) (synCvv))))))))
      (synWa (.classEq (synCsn A) (synCsn (.cv z)))
        (synWa (.classEq (.cv t) (synCsn (.cv x))) (.classMem (synCopk (.cv z) (.cv x))
            (synCcnvk (synCimagek (synCun (synCin (synCimagek (synCimak (synCdif
                          (synCins3k (synCcompl (synCimak (synCin (synCins3k (synCssetk))
                                  (synCins2k (synCssetk))) (synCpw1 (synCpw1 (synC1c))))))
                          (synCimak (synCsymdif (synCins2k (synCins2k (synCssetk)))
                              (synCun (synCins2k (synCins3k (synCssetk)))
                                (synCins3k (synCsik (synCsik (synCssetk))))))
                            (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))
                        (synCpw1 (synCpw1 (synC1c))))) (synCxpk (synCnnc) (synCvv)))
                  (synCin (synCidk) (synCxpk (synCcompl (synCnnc)) (synCvv)))))))))
      (synWa (.classEq (.cv z) A) (synWa (.classEq (.cv t) (synCsn (.cv x)))
          (.classMem (synCopk (.cv z) (.cv x)) (synCcnvk (synCimagek (synCun (synCin
                    (synCimagek (synCimak (synCdif (synCins3k (synCcompl (synCimak
                                (synCin (synCins3k (synCssetk)) (synCins2k (synCssetk)))
                                (synCpw1 (synCpw1 (synC1c)))))) (synCimak
                            (synCsymdif (synCins2k (synCins2k (synCssetk)))
                              (synCun (synCins2k (synCins3k (synCssetk)))
                                (synCins3k (synCsik (synCsik (synCssetk))))))
                            (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))
                        (synCpw1 (synCpw1 (synC1c))))) (synCxpk (synCnnc) (synCvv)))
                  (synCin (synCidk) (synCxpk (synCcompl (synCnnc)) (synCvv)))))))))
      p0005 p0010
  have p0012 :=
    @gExbii
      (synW3a (.classEq (synCsn A) (synCsn (.cv z))) (.classEq (.cv t) (synCsn (.cv x)))
        (.classMem (synCopk (.cv z) (.cv x)) (synCcnvk (synCimagek (synCun (synCin
                  (synCimagek (synCimak (synCdif (synCins3k (synCcompl (synCimak
                              (synCin (synCins3k (synCssetk)) (synCins2k (synCssetk)))
                              (synCpw1 (synCpw1 (synC1c)))))) (synCimak
                          (synCsymdif (synCins2k (synCins2k (synCssetk)))
                            (synCun (synCins2k (synCins3k (synCssetk)))
                              (synCins3k (synCsik (synCsik (synCssetk))))))
                          (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))
                      (synCpw1 (synCpw1 (synC1c))))) (synCxpk (synCnnc) (synCvv)))
                (synCin (synCidk) (synCxpk (synCcompl (synCnnc)) (synCvv))))))))
      (synWa (.classEq (.cv z) A) (synWa (.classEq (.cv t) (synCsn (.cv x)))
          (.classMem (synCopk (.cv z) (.cv x)) (synCcnvk (synCimagek (synCun (synCin
                    (synCimagek (synCimak (synCdif (synCins3k (synCcompl (synCimak
                                (synCin (synCins3k (synCssetk)) (synCins2k (synCssetk)))
                                (synCpw1 (synCpw1 (synC1c)))))) (synCimak
                            (synCsymdif (synCins2k (synCins2k (synCssetk)))
                              (synCun (synCins2k (synCins3k (synCssetk)))
                                (synCins3k (synCsik (synCsik (synCssetk))))))
                            (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))
                        (synCpw1 (synCpw1 (synC1c))))) (synCxpk (synCnnc) (synCvv)))
                  (synCin (synCidk) (synCxpk (synCcompl (synCnnc)) (synCvv)))))))))
      z p0011
  have p0013 := @gOpkeq1 (.cv z) A (.cv x)
  have p0014 :=
    @gEleq1d (.classEq (.cv z) A) (synCopk (.cv z) (.cv x)) (synCopk A (.cv x))
      (synCcnvk (synCimagek (synCun (synCin (synCimagek (synCimak (synCdif (synCins3k
                      (synCcompl (synCimak
                          (synCin (synCins3k (synCssetk)) (synCins2k (synCssetk)))
                          (synCpw1 (synCpw1 (synC1c)))))) (synCimak
                      (synCsymdif (synCins2k (synCins2k (synCssetk)))
                        (synCun (synCins2k (synCins3k (synCssetk)))
                          (synCins3k (synCsik (synCsik (synCssetk))))))
                      (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))
                  (synCpw1 (synCpw1 (synC1c))))) (synCxpk (synCnnc) (synCvv)))
            (synCin (synCidk) (synCxpk (synCcompl (synCnnc)) (synCvv))))))
      p0013
  have p0015 :=
    @gAnbi2d (.classEq (.cv z) A)
      (.classMem (synCopk (.cv z) (.cv x)) (synCcnvk (synCimagek (synCun (synCin
                (synCimagek (synCimak (synCdif (synCins3k (synCcompl (synCimak
                            (synCin (synCins3k (synCssetk)) (synCins2k (synCssetk)))
                            (synCpw1 (synCpw1 (synC1c)))))) (synCimak
                        (synCsymdif (synCins2k (synCins2k (synCssetk)))
                          (synCun (synCins2k (synCins3k (synCssetk)))
                            (synCins3k (synCsik (synCsik (synCssetk))))))
                        (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))
                    (synCpw1 (synCpw1 (synC1c))))) (synCxpk (synCnnc) (synCvv)))
              (synCin (synCidk) (synCxpk (synCcompl (synCnnc)) (synCvv)))))))
      (.classMem (synCopk A (.cv x)) (synCcnvk (synCimagek (synCun (synCin (synCimagek
                  (synCimak (synCdif (synCins3k (synCcompl (synCimak
                            (synCin (synCins3k (synCssetk)) (synCins2k (synCssetk)))
                            (synCpw1 (synCpw1 (synC1c)))))) (synCimak
                        (synCsymdif (synCins2k (synCins2k (synCssetk)))
                          (synCun (synCins2k (synCins3k (synCssetk)))
                            (synCins3k (synCsik (synCsik (synCssetk))))))
                        (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))
                    (synCpw1 (synCpw1 (synC1c))))) (synCxpk (synCnnc) (synCvv)))
              (synCin (synCidk) (synCxpk (synCcompl (synCnnc)) (synCvv)))))))
      (.classEq (.cv t) (synCsn (.cv x))) p0014
  have p0016 :=
    @gCeqsexv
      (synWa (.classEq (.cv t) (synCsn (.cv x))) (.classMem (synCopk (.cv z) (.cv x))
          (synCcnvk (synCimagek (synCun (synCin (synCimagek (synCimak (synCdif
                        (synCins3k (synCcompl (synCimak (synCin (synCins3k (synCssetk))
                                (synCins2k (synCssetk))) (synCpw1 (synCpw1 (synC1c))))))
                        (synCimak (synCsymdif (synCins2k (synCins2k (synCssetk)))
                            (synCun (synCins2k (synCins3k (synCssetk)))
                              (synCins3k (synCsik (synCsik (synCssetk))))))
                          (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))
                      (synCpw1 (synCpw1 (synC1c))))) (synCxpk (synCnnc) (synCvv)))
                (synCin (synCidk) (synCxpk (synCcompl (synCnnc)) (synCvv))))))))
      (synWa (.classEq (.cv t) (synCsn (.cv x))) (.classMem (synCopk A (.cv x)) (synCcnvk
            (synCimagek (synCun (synCin (synCimagek (synCimak (synCdif (synCins3k
                          (synCcompl (synCimak (synCin (synCins3k (synCssetk))
                                (synCins2k (synCssetk))) (synCpw1 (synCpw1 (synC1c))))))
                        (synCimak (synCsymdif (synCins2k (synCins2k (synCssetk)))
                            (synCun (synCins2k (synCins3k (synCssetk)))
                              (synCins3k (synCsik (synCsik (synCssetk))))))
                          (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))
                      (synCpw1 (synCpw1 (synC1c))))) (synCxpk (synCnnc) (synCvv)))
                (synCin (synCidk) (synCxpk (synCcompl (synCnnc)) (synCvv))))))))
      z A dv_cache_0008 dv_cache_0009 hyp_setconslem1_1 p0015
  have p0017 :=
    @gBitri
      (synWex z (synW3a (.classEq (synCsn A) (synCsn (.cv z)))
          (.classEq (.cv t) (synCsn (.cv x))) (.classMem (synCopk (.cv z) (.cv x)) (synCcnvk
              (synCimagek (synCun (synCin (synCimagek (synCimak (synCdif (synCins3k
                            (synCcompl (synCimak (synCin (synCins3k (synCssetk))
                                  (synCins2k (synCssetk))) (synCpw1 (synCpw1 (synC1c))))))
                          (synCimak (synCsymdif (synCins2k (synCins2k (synCssetk)))
                              (synCun (synCins2k (synCins3k (synCssetk)))
                                (synCins3k (synCsik (synCsik (synCssetk))))))
                            (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))
                        (synCpw1 (synCpw1 (synC1c))))) (synCxpk (synCnnc) (synCvv)))
                  (synCin (synCidk) (synCxpk (synCcompl (synCnnc)) (synCvv)))))))))
      (synWex z (synWa (.classEq (.cv z) A) (synWa (.classEq (.cv t) (synCsn (.cv x)))
            (.classMem (synCopk (.cv z) (.cv x)) (synCcnvk (synCimagek (synCun (synCin
                      (synCimagek (synCimak (synCdif (synCins3k (synCcompl (synCimak
                                  (synCin (synCins3k (synCssetk)) (synCins2k (synCssetk)))
                                  (synCpw1 (synCpw1 (synC1c)))))) (synCimak
                              (synCsymdif (synCins2k (synCins2k (synCssetk)))
                                (synCun (synCins2k (synCins3k (synCssetk)))
                                  (synCins3k (synCsik (synCsik (synCssetk))))))
                              (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))
                          (synCpw1 (synCpw1 (synC1c))))) (synCxpk (synCnnc) (synCvv)))
                    (synCin (synCidk) (synCxpk (synCcompl (synCnnc)) (synCvv))))))))))
      (synWa (.classEq (.cv t) (synCsn (.cv x))) (.classMem (synCopk A (.cv x)) (synCcnvk
            (synCimagek (synCun (synCin (synCimagek (synCimak (synCdif (synCins3k
                          (synCcompl (synCimak (synCin (synCins3k (synCssetk))
                                (synCins2k (synCssetk))) (synCpw1 (synCpw1 (synC1c))))))
                        (synCimak (synCsymdif (synCins2k (synCins2k (synCssetk)))
                            (synCun (synCins2k (synCins3k (synCssetk)))
                              (synCins3k (synCsik (synCsik (synCssetk))))))
                          (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))
                      (synCpw1 (synCpw1 (synC1c))))) (synCxpk (synCnnc) (synCvv)))
                (synCin (synCidk) (synCxpk (synCcompl (synCnnc)) (synCvv))))))))
      p0012 p0016
  have p0018 :=
    @gExbii
      (synWex z (synW3a (.classEq (synCsn A) (synCsn (.cv z)))
          (.classEq (.cv t) (synCsn (.cv x))) (.classMem (synCopk (.cv z) (.cv x)) (synCcnvk
              (synCimagek (synCun (synCin (synCimagek (synCimak (synCdif (synCins3k
                            (synCcompl (synCimak (synCin (synCins3k (synCssetk))
                                  (synCins2k (synCssetk))) (synCpw1 (synCpw1 (synC1c))))))
                          (synCimak (synCsymdif (synCins2k (synCins2k (synCssetk)))
                              (synCun (synCins2k (synCins3k (synCssetk)))
                                (synCins3k (synCsik (synCsik (synCssetk))))))
                            (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))
                        (synCpw1 (synCpw1 (synC1c))))) (synCxpk (synCnnc) (synCvv)))
                  (synCin (synCidk) (synCxpk (synCcompl (synCnnc)) (synCvv)))))))))
      (synWa (.classEq (.cv t) (synCsn (.cv x))) (.classMem (synCopk A (.cv x)) (synCcnvk
            (synCimagek (synCun (synCin (synCimagek (synCimak (synCdif (synCins3k
                          (synCcompl (synCimak (synCin (synCins3k (synCssetk))
                                (synCins2k (synCssetk))) (synCpw1 (synCpw1 (synC1c))))))
                        (synCimak (synCsymdif (synCins2k (synCins2k (synCssetk)))
                            (synCun (synCins2k (synCins3k (synCssetk)))
                              (synCins3k (synCsik (synCsik (synCssetk))))))
                          (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))
                      (synCpw1 (synCpw1 (synC1c))))) (synCxpk (synCnnc) (synCvv)))
                (synCin (synCidk) (synCxpk (synCcompl (synCnnc)) (synCvv))))))))
      x p0017
  have p0019 :=
    @gN3bitri
      (.classMem (synCopk (synCsn A) (.cv t)) (synCsik (synCcnvk (synCimagek (synCun
                (synCin (synCimagek (synCimak (synCdif (synCins3k (synCcompl (synCimak
                              (synCin (synCins3k (synCssetk)) (synCins2k (synCssetk)))
                              (synCpw1 (synCpw1 (synC1c)))))) (synCimak
                          (synCsymdif (synCins2k (synCins2k (synCssetk)))
                            (synCun (synCins2k (synCins3k (synCssetk)))
                              (synCins3k (synCsik (synCsik (synCssetk))))))
                          (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))
                      (synCpw1 (synCpw1 (synC1c))))) (synCxpk (synCnnc) (synCvv)))
                (synCin (synCidk) (synCxpk (synCcompl (synCnnc)) (synCvv))))))))
      (synWex z (synWex x (synW3a (.classEq (synCsn A) (synCsn (.cv z)))
            (.classEq (.cv t) (synCsn (.cv x))) (.classMem (synCopk (.cv z) (.cv x))
              (synCcnvk (synCimagek (synCun (synCin (synCimagek (synCimak (synCdif
                            (synCins3k (synCcompl (synCimak
                                  (synCin (synCins3k (synCssetk)) (synCins2k (synCssetk)))
                                  (synCpw1 (synCpw1 (synC1c)))))) (synCimak
                              (synCsymdif (synCins2k (synCins2k (synCssetk)))
                                (synCun (synCins2k (synCins3k (synCssetk)))
                                  (synCins3k (synCsik (synCsik (synCssetk))))))
                              (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))
                          (synCpw1 (synCpw1 (synC1c))))) (synCxpk (synCnnc) (synCvv)))
                    (synCin (synCidk) (synCxpk (synCcompl (synCnnc)) (synCvv))))))))))
      (synWex x (synWex z (synW3a (.classEq (synCsn A) (synCsn (.cv z)))
            (.classEq (.cv t) (synCsn (.cv x))) (.classMem (synCopk (.cv z) (.cv x))
              (synCcnvk (synCimagek (synCun (synCin (synCimagek (synCimak (synCdif
                            (synCins3k (synCcompl (synCimak
                                  (synCin (synCins3k (synCssetk)) (synCins2k (synCssetk)))
                                  (synCpw1 (synCpw1 (synC1c)))))) (synCimak
                              (synCsymdif (synCins2k (synCins2k (synCssetk)))
                                (synCun (synCins2k (synCins3k (synCssetk)))
                                  (synCins3k (synCsik (synCsik (synCssetk))))))
                              (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))
                          (synCpw1 (synCpw1 (synC1c))))) (synCxpk (synCnnc) (synCvv)))
                    (synCin (synCidk) (synCxpk (synCcompl (synCnnc)) (synCvv))))))))))
      (synWex x (synWa (.classEq (.cv t) (synCsn (.cv x))) (.classMem (synCopk A (.cv x))
            (synCcnvk (synCimagek (synCun (synCin (synCimagek (synCimak (synCdif
                          (synCins3k (synCcompl (synCimak (synCin (synCins3k (synCssetk))
                                  (synCins2k (synCssetk))) (synCpw1 (synCpw1 (synC1c))))))
                          (synCimak (synCsymdif (synCins2k (synCins2k (synCssetk)))
                              (synCun (synCins2k (synCins3k (synCssetk)))
                                (synCins3k (synCsik (synCsik (synCssetk))))))
                            (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))
                        (synCpw1 (synCpw1 (synC1c))))) (synCxpk (synCnnc) (synCvv)))
                  (synCin (synCidk) (synCxpk (synCcompl (synCnnc)) (synCvv)))))))))
      p0003 p0004 p0018
  have p0020 :=
    @gAnbi1i
      (.classMem (synCopk (synCsn A) (.cv t)) (synCsik (synCcnvk (synCimagek (synCun
                (synCin (synCimagek (synCimak (synCdif (synCins3k (synCcompl (synCimak
                              (synCin (synCins3k (synCssetk)) (synCins2k (synCssetk)))
                              (synCpw1 (synCpw1 (synC1c)))))) (synCimak
                          (synCsymdif (synCins2k (synCins2k (synCssetk)))
                            (synCun (synCins2k (synCins3k (synCssetk)))
                              (synCins3k (synCsik (synCsik (synCssetk))))))
                          (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))
                      (synCpw1 (synCpw1 (synC1c))))) (synCxpk (synCnnc) (synCvv)))
                (synCin (synCidk) (synCxpk (synCcompl (synCnnc)) (synCvv))))))))
      (synWex x (synWa (.classEq (.cv t) (synCsn (.cv x))) (.classMem (synCopk A (.cv x))
            (synCcnvk (synCimagek (synCun (synCin (synCimagek (synCimak (synCdif
                          (synCins3k (synCcompl (synCimak (synCin (synCins3k (synCssetk))
                                  (synCins2k (synCssetk))) (synCpw1 (synCpw1 (synC1c))))))
                          (synCimak (synCsymdif (synCins2k (synCins2k (synCssetk)))
                              (synCun (synCins2k (synCins3k (synCssetk)))
                                (synCins3k (synCsik (synCsik (synCssetk))))))
                            (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))
                        (synCpw1 (synCpw1 (synC1c))))) (synCxpk (synCnnc) (synCvv)))
                  (synCin (synCidk) (synCxpk (synCcompl (synCnnc)) (synCvv)))))))))
      (.classMem (synCopk (.cv t) B) (synCssetk)) p0019
  have p0021 :=
    @gN1941v
      (synWa (.classEq (.cv t) (synCsn (.cv x))) (.classMem (synCopk A (.cv x)) (synCcnvk
            (synCimagek (synCun (synCin (synCimagek (synCimak (synCdif (synCins3k
                          (synCcompl (synCimak (synCin (synCins3k (synCssetk))
                                (synCins2k (synCssetk))) (synCpw1 (synCpw1 (synC1c))))))
                        (synCimak (synCsymdif (synCins2k (synCins2k (synCssetk)))
                            (synCun (synCins2k (synCins3k (synCssetk)))
                              (synCins3k (synCsik (synCsik (synCssetk))))))
                          (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))
                      (synCpw1 (synCpw1 (synC1c))))) (synCxpk (synCnnc) (synCvv)))
                (synCin (synCidk) (synCxpk (synCcompl (synCnnc)) (synCvv))))))))
      (.classMem (synCopk (.cv t) B) (synCssetk)) x dv_cache_0010
  have p0022 :=
    @gAnass (.classEq (.cv t) (synCsn (.cv x)))
      (.classMem (synCopk A (.cv x)) (synCcnvk (synCimagek (synCun (synCin (synCimagek
                  (synCimak (synCdif (synCins3k (synCcompl (synCimak
                            (synCin (synCins3k (synCssetk)) (synCins2k (synCssetk)))
                            (synCpw1 (synCpw1 (synC1c)))))) (synCimak
                        (synCsymdif (synCins2k (synCins2k (synCssetk)))
                          (synCun (synCins2k (synCins3k (synCssetk)))
                            (synCins3k (synCsik (synCsik (synCssetk))))))
                        (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))
                    (synCpw1 (synCpw1 (synC1c))))) (synCxpk (synCnnc) (synCvv)))
              (synCin (synCidk) (synCxpk (synCcompl (synCnnc)) (synCvv)))))))
      (.classMem (synCopk (.cv t) B) (synCssetk))
  have p0023 :=
    @gExbii
      (synWa (synWa (.classEq (.cv t) (synCsn (.cv x))) (.classMem (synCopk A (.cv x))
            (synCcnvk (synCimagek (synCun (synCin (synCimagek (synCimak (synCdif
                          (synCins3k (synCcompl (synCimak (synCin (synCins3k (synCssetk))
                                  (synCins2k (synCssetk))) (synCpw1 (synCpw1 (synC1c))))))
                          (synCimak (synCsymdif (synCins2k (synCins2k (synCssetk)))
                              (synCun (synCins2k (synCins3k (synCssetk)))
                                (synCins3k (synCsik (synCsik (synCssetk))))))
                            (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))
                        (synCpw1 (synCpw1 (synC1c))))) (synCxpk (synCnnc) (synCvv)))
                  (synCin (synCidk) (synCxpk (synCcompl (synCnnc)) (synCvv))))))))
        (.classMem (synCopk (.cv t) B) (synCssetk)))
      (synWa (.classEq (.cv t) (synCsn (.cv x))) (synWa (.classMem (synCopk A (.cv x))
            (synCcnvk (synCimagek (synCun (synCin (synCimagek (synCimak (synCdif
                          (synCins3k (synCcompl (synCimak (synCin (synCins3k (synCssetk))
                                  (synCins2k (synCssetk))) (synCpw1 (synCpw1 (synC1c))))))
                          (synCimak (synCsymdif (synCins2k (synCins2k (synCssetk)))
                              (synCun (synCins2k (synCins3k (synCssetk)))
                                (synCins3k (synCsik (synCsik (synCssetk))))))
                            (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))
                        (synCpw1 (synCpw1 (synC1c))))) (synCxpk (synCnnc) (synCvv)))
                  (synCin (synCidk) (synCxpk (synCcompl (synCnnc)) (synCvv)))))))
          (.classMem (synCopk (.cv t) B) (synCssetk))))
      x p0022
  have p0024 :=
    @gN3bitr2i
      (synWa (.classMem (synCopk (synCsn A) (.cv t)) (synCsik (synCcnvk (synCimagek
                (synCun (synCin (synCimagek (synCimak (synCdif (synCins3k (synCcompl
                              (synCimak (synCin (synCins3k (synCssetk))
                                  (synCins2k (synCssetk))) (synCpw1 (synCpw1 (synC1c))))))
                          (synCimak (synCsymdif (synCins2k (synCins2k (synCssetk)))
                              (synCun (synCins2k (synCins3k (synCssetk)))
                                (synCins3k (synCsik (synCsik (synCssetk))))))
                            (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))
                        (synCpw1 (synCpw1 (synC1c))))) (synCxpk (synCnnc) (synCvv)))
                  (synCin (synCidk) (synCxpk (synCcompl (synCnnc)) (synCvv))))))))
        (.classMem (synCopk (.cv t) B) (synCssetk)))
      (synWa (synWex x (synWa (.classEq (.cv t) (synCsn (.cv x)))
            (.classMem (synCopk A (.cv x)) (synCcnvk (synCimagek (synCun (synCin
                      (synCimagek (synCimak (synCdif (synCins3k (synCcompl (synCimak
                                  (synCin (synCins3k (synCssetk)) (synCins2k (synCssetk)))
                                  (synCpw1 (synCpw1 (synC1c)))))) (synCimak
                              (synCsymdif (synCins2k (synCins2k (synCssetk)))
                                (synCun (synCins2k (synCins3k (synCssetk)))
                                  (synCins3k (synCsik (synCsik (synCssetk))))))
                              (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))
                          (synCpw1 (synCpw1 (synC1c))))) (synCxpk (synCnnc) (synCvv)))
                    (synCin (synCidk) (synCxpk (synCcompl (synCnnc)) (synCvv)))))))))
        (.classMem (synCopk (.cv t) B) (synCssetk)))
      (synWex x (synWa (synWa (.classEq (.cv t) (synCsn (.cv x)))
            (.classMem (synCopk A (.cv x)) (synCcnvk (synCimagek (synCun (synCin
                      (synCimagek (synCimak (synCdif (synCins3k (synCcompl (synCimak
                                  (synCin (synCins3k (synCssetk)) (synCins2k (synCssetk)))
                                  (synCpw1 (synCpw1 (synC1c)))))) (synCimak
                              (synCsymdif (synCins2k (synCins2k (synCssetk)))
                                (synCun (synCins2k (synCins3k (synCssetk)))
                                  (synCins3k (synCsik (synCsik (synCssetk))))))
                              (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))
                          (synCpw1 (synCpw1 (synC1c))))) (synCxpk (synCnnc) (synCvv)))
                    (synCin (synCidk) (synCxpk (synCcompl (synCnnc)) (synCvv))))))))
          (.classMem (synCopk (.cv t) B) (synCssetk))))
      (synWex x (synWa (.classEq (.cv t) (synCsn (.cv x))) (synWa
            (.classMem (synCopk A (.cv x)) (synCcnvk (synCimagek (synCun (synCin
                      (synCimagek (synCimak (synCdif (synCins3k (synCcompl (synCimak
                                  (synCin (synCins3k (synCssetk)) (synCins2k (synCssetk)))
                                  (synCpw1 (synCpw1 (synC1c)))))) (synCimak
                              (synCsymdif (synCins2k (synCins2k (synCssetk)))
                                (synCun (synCins2k (synCins3k (synCssetk)))
                                  (synCins3k (synCsik (synCsik (synCssetk))))))
                              (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))
                          (synCpw1 (synCpw1 (synC1c))))) (synCxpk (synCnnc) (synCvv)))
                    (synCin (synCidk) (synCxpk (synCcompl (synCnnc)) (synCvv)))))))
            (.classMem (synCopk (.cv t) B) (synCssetk)))))
      p0020 p0021 p0023
  have p0025 :=
    @gExbii
      (synWa (.classMem (synCopk (synCsn A) (.cv t)) (synCsik (synCcnvk (synCimagek
                (synCun (synCin (synCimagek (synCimak (synCdif (synCins3k (synCcompl
                              (synCimak (synCin (synCins3k (synCssetk))
                                  (synCins2k (synCssetk))) (synCpw1 (synCpw1 (synC1c))))))
                          (synCimak (synCsymdif (synCins2k (synCins2k (synCssetk)))
                              (synCun (synCins2k (synCins3k (synCssetk)))
                                (synCins3k (synCsik (synCsik (synCssetk))))))
                            (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))
                        (synCpw1 (synCpw1 (synC1c))))) (synCxpk (synCnnc) (synCvv)))
                  (synCin (synCidk) (synCxpk (synCcompl (synCnnc)) (synCvv))))))))
        (.classMem (synCopk (.cv t) B) (synCssetk)))
      (synWex x (synWa (.classEq (.cv t) (synCsn (.cv x))) (synWa
            (.classMem (synCopk A (.cv x)) (synCcnvk (synCimagek (synCun (synCin
                      (synCimagek (synCimak (synCdif (synCins3k (synCcompl (synCimak
                                  (synCin (synCins3k (synCssetk)) (synCins2k (synCssetk)))
                                  (synCpw1 (synCpw1 (synC1c)))))) (synCimak
                              (synCsymdif (synCins2k (synCins2k (synCssetk)))
                                (synCun (synCins2k (synCins3k (synCssetk)))
                                  (synCins3k (synCsik (synCsik (synCssetk))))))
                              (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))
                          (synCpw1 (synCpw1 (synC1c))))) (synCxpk (synCnnc) (synCvv)))
                    (synCin (synCidk) (synCxpk (synCcompl (synCnnc)) (synCvv)))))))
            (.classMem (synCopk (.cv t) B) (synCssetk)))))
      t p0024
  have p0026 :=
    @gExcom
      (synWa (.classEq (.cv t) (synCsn (.cv x))) (synWa (.classMem (synCopk A (.cv x))
            (synCcnvk (synCimagek (synCun (synCin (synCimagek (synCimak (synCdif
                          (synCins3k (synCcompl (synCimak (synCin (synCins3k (synCssetk))
                                  (synCins2k (synCssetk))) (synCpw1 (synCpw1 (synC1c))))))
                          (synCimak (synCsymdif (synCins2k (synCins2k (synCssetk)))
                              (synCun (synCins2k (synCins3k (synCssetk)))
                                (synCins3k (synCsik (synCsik (synCssetk))))))
                            (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))
                        (synCpw1 (synCpw1 (synC1c))))) (synCxpk (synCnnc) (synCvv)))
                  (synCin (synCidk) (synCxpk (synCcompl (synCnnc)) (synCvv)))))))
          (.classMem (synCopk (.cv t) B) (synCssetk))))
      x t
  have p0027 := @gSnex (.cv x)
  have p0028 := @gOpkeq1 (.cv t) (synCsn (.cv x)) B
  have p0029 :=
    @gEleq1d (.classEq (.cv t) (synCsn (.cv x))) (synCopk (.cv t) B)
      (synCopk (synCsn (.cv x)) B) (synCssetk) p0028
  have p0030 :=
    @gAnbi2d (.classEq (.cv t) (synCsn (.cv x)))
      (.classMem (synCopk (.cv t) B) (synCssetk))
      (.classMem (synCopk (synCsn (.cv x)) B) (synCssetk))
      (.classMem (synCopk A (.cv x)) (synCcnvk (synCimagek (synCun (synCin (synCimagek
                  (synCimak (synCdif (synCins3k (synCcompl (synCimak
                            (synCin (synCins3k (synCssetk)) (synCins2k (synCssetk)))
                            (synCpw1 (synCpw1 (synC1c)))))) (synCimak
                        (synCsymdif (synCins2k (synCins2k (synCssetk)))
                          (synCun (synCins2k (synCins3k (synCssetk)))
                            (synCins3k (synCsik (synCsik (synCssetk))))))
                        (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))
                    (synCpw1 (synCpw1 (synC1c))))) (synCxpk (synCnnc) (synCvv)))
              (synCin (synCidk) (synCxpk (synCcompl (synCnnc)) (synCvv)))))))
      p0029
  have p0031 :=
    @gCeqsexv
      (synWa (.classMem (synCopk A (.cv x)) (synCcnvk (synCimagek (synCun (synCin
                  (synCimagek (synCimak (synCdif (synCins3k (synCcompl (synCimak
                              (synCin (synCins3k (synCssetk)) (synCins2k (synCssetk)))
                              (synCpw1 (synCpw1 (synC1c)))))) (synCimak
                          (synCsymdif (synCins2k (synCins2k (synCssetk)))
                            (synCun (synCins2k (synCins3k (synCssetk)))
                              (synCins3k (synCsik (synCsik (synCssetk))))))
                          (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))
                      (synCpw1 (synCpw1 (synC1c))))) (synCxpk (synCnnc) (synCvv)))
                (synCin (synCidk) (synCxpk (synCcompl (synCnnc)) (synCvv)))))))
        (.classMem (synCopk (.cv t) B) (synCssetk)))
      (synWa (.classMem (synCopk A (.cv x)) (synCcnvk (synCimagek (synCun (synCin
                  (synCimagek (synCimak (synCdif (synCins3k (synCcompl (synCimak
                              (synCin (synCins3k (synCssetk)) (synCins2k (synCssetk)))
                              (synCpw1 (synCpw1 (synC1c)))))) (synCimak
                          (synCsymdif (synCins2k (synCins2k (synCssetk)))
                            (synCun (synCins2k (synCins3k (synCssetk)))
                              (synCins3k (synCsik (synCsik (synCssetk))))))
                          (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))
                      (synCpw1 (synCpw1 (synC1c))))) (synCxpk (synCnnc) (synCvv)))
                (synCin (synCidk) (synCxpk (synCcompl (synCnnc)) (synCvv)))))))
        (.classMem (synCopk (synCsn (.cv x)) B) (synCssetk)))
      t (synCsn (.cv x)) dv_cache_0011 dv_cache_0012 p0027 p0030
  have p0032 := @gVex x
  have p0033 :=
    @gOpkelimagek (.cv x) A
      (synCun (synCin (synCimagek (synCimak (synCdif (synCins3k (synCcompl (synCimak
                      (synCin (synCins3k (synCssetk)) (synCins2k (synCssetk)))
                      (synCpw1 (synCpw1 (synC1c)))))) (synCimak
                  (synCsymdif (synCins2k (synCins2k (synCssetk)))
                    (synCun (synCins2k (synCins3k (synCssetk)))
                      (synCins3k (synCsik (synCsik (synCssetk))))))
                  (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))
              (synCpw1 (synCpw1 (synC1c))))) (synCxpk (synCnnc) (synCvv)))
        (synCin (synCidk) (synCxpk (synCcompl (synCnnc)) (synCvv))))
      p0032 hyp_setconslem1_1
  have p0034 :=
    @gOpkelcnvk A (.cv x)
      (synCimagek (synCun (synCin (synCimagek (synCimak (synCdif (synCins3k (synCcompl
                      (synCimak (synCin (synCins3k (synCssetk)) (synCins2k (synCssetk)))
                        (synCpw1 (synCpw1 (synC1c)))))) (synCimak
                    (synCsymdif (synCins2k (synCins2k (synCssetk)))
                      (synCun (synCins2k (synCins3k (synCssetk)))
                        (synCins3k (synCsik (synCsik (synCssetk))))))
                    (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))
                (synCpw1 (synCpw1 (synC1c))))) (synCxpk (synCnnc) (synCvv)))
          (synCin (synCidk) (synCxpk (synCcompl (synCnnc)) (synCvv)))))
      hyp_setconslem1_1 p0032
  have p0035 := @gDfphi2 (.cv x)
  have p0036 :=
    @gEqeq2i (synCphi (.cv x))
      (synCimak (synCun (synCin (synCimagek (synCimak (synCdif (synCins3k (synCcompl
                      (synCimak (synCin (synCins3k (synCssetk)) (synCins2k (synCssetk)))
                        (synCpw1 (synCpw1 (synC1c)))))) (synCimak
                    (synCsymdif (synCins2k (synCins2k (synCssetk)))
                      (synCun (synCins2k (synCins3k (synCssetk)))
                        (synCins3k (synCsik (synCsik (synCssetk))))))
                    (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))
                (synCpw1 (synCpw1 (synC1c))))) (synCxpk (synCnnc) (synCvv)))
          (synCin (synCidk) (synCxpk (synCcompl (synCnnc)) (synCvv)))) (.cv x))
      A p0035
  have p0037 :=
    @gN3bitr4i
      (.classMem (synCopk (.cv x) A) (synCimagek (synCun (synCin (synCimagek (synCimak
                  (synCdif (synCins3k (synCcompl (synCimak
                          (synCin (synCins3k (synCssetk)) (synCins2k (synCssetk)))
                          (synCpw1 (synCpw1 (synC1c)))))) (synCimak
                      (synCsymdif (synCins2k (synCins2k (synCssetk)))
                        (synCun (synCins2k (synCins3k (synCssetk)))
                          (synCins3k (synCsik (synCsik (synCssetk))))))
                      (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))
                  (synCpw1 (synCpw1 (synC1c))))) (synCxpk (synCnnc) (synCvv)))
            (synCin (synCidk) (synCxpk (synCcompl (synCnnc)) (synCvv))))))
      (.classEq A (synCimak (synCun (synCin (synCimagek (synCimak (synCdif (synCins3k
                      (synCcompl (synCimak
                          (synCin (synCins3k (synCssetk)) (synCins2k (synCssetk)))
                          (synCpw1 (synCpw1 (synC1c)))))) (synCimak
                      (synCsymdif (synCins2k (synCins2k (synCssetk)))
                        (synCun (synCins2k (synCins3k (synCssetk)))
                          (synCins3k (synCsik (synCsik (synCssetk))))))
                      (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))
                  (synCpw1 (synCpw1 (synC1c))))) (synCxpk (synCnnc) (synCvv)))
            (synCin (synCidk) (synCxpk (synCcompl (synCnnc)) (synCvv)))) (.cv x)))
      (.classMem (synCopk A (.cv x)) (synCcnvk (synCimagek (synCun (synCin (synCimagek
                  (synCimak (synCdif (synCins3k (synCcompl (synCimak
                            (synCin (synCins3k (synCssetk)) (synCins2k (synCssetk)))
                            (synCpw1 (synCpw1 (synC1c)))))) (synCimak
                        (synCsymdif (synCins2k (synCins2k (synCssetk)))
                          (synCun (synCins2k (synCins3k (synCssetk)))
                            (synCins3k (synCsik (synCsik (synCssetk))))))
                        (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))
                    (synCpw1 (synCpw1 (synC1c))))) (synCxpk (synCnnc) (synCvv)))
              (synCin (synCidk) (synCxpk (synCcompl (synCnnc)) (synCvv)))))))
      (.classEq A (synCphi (.cv x))) p0033 p0034 p0036
  have p0038 := @gElssetk (.cv x) B p0032 hyp_setconslem1_2
  have p0039 :=
    @gAnbi12i
      (.classMem (synCopk A (.cv x)) (synCcnvk (synCimagek (synCun (synCin (synCimagek
                  (synCimak (synCdif (synCins3k (synCcompl (synCimak
                            (synCin (synCins3k (synCssetk)) (synCins2k (synCssetk)))
                            (synCpw1 (synCpw1 (synC1c)))))) (synCimak
                        (synCsymdif (synCins2k (synCins2k (synCssetk)))
                          (synCun (synCins2k (synCins3k (synCssetk)))
                            (synCins3k (synCsik (synCsik (synCssetk))))))
                        (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))
                    (synCpw1 (synCpw1 (synC1c))))) (synCxpk (synCnnc) (synCvv)))
              (synCin (synCidk) (synCxpk (synCcompl (synCnnc)) (synCvv)))))))
      (.classEq A (synCphi (.cv x)))
      (.classMem (synCopk (synCsn (.cv x)) B) (synCssetk)) (.classMem (.cv x) B) p0037
      p0038
  have p0040 := @gAncom (.classEq A (synCphi (.cv x))) (.classMem (.cv x) B)
  have p0041 :=
    @gN3bitri
      (synWex t (synWa (.classEq (.cv t) (synCsn (.cv x))) (synWa
            (.classMem (synCopk A (.cv x)) (synCcnvk (synCimagek (synCun (synCin
                      (synCimagek (synCimak (synCdif (synCins3k (synCcompl (synCimak
                                  (synCin (synCins3k (synCssetk)) (synCins2k (synCssetk)))
                                  (synCpw1 (synCpw1 (synC1c)))))) (synCimak
                              (synCsymdif (synCins2k (synCins2k (synCssetk)))
                                (synCun (synCins2k (synCins3k (synCssetk)))
                                  (synCins3k (synCsik (synCsik (synCssetk))))))
                              (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))
                          (synCpw1 (synCpw1 (synC1c))))) (synCxpk (synCnnc) (synCvv)))
                    (synCin (synCidk) (synCxpk (synCcompl (synCnnc)) (synCvv)))))))
            (.classMem (synCopk (.cv t) B) (synCssetk)))))
      (synWa (.classMem (synCopk A (.cv x)) (synCcnvk (synCimagek (synCun (synCin
                  (synCimagek (synCimak (synCdif (synCins3k (synCcompl (synCimak
                              (synCin (synCins3k (synCssetk)) (synCins2k (synCssetk)))
                              (synCpw1 (synCpw1 (synC1c)))))) (synCimak
                          (synCsymdif (synCins2k (synCins2k (synCssetk)))
                            (synCun (synCins2k (synCins3k (synCssetk)))
                              (synCins3k (synCsik (synCsik (synCssetk))))))
                          (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))
                      (synCpw1 (synCpw1 (synC1c))))) (synCxpk (synCnnc) (synCvv)))
                (synCin (synCidk) (synCxpk (synCcompl (synCnnc)) (synCvv)))))))
        (.classMem (synCopk (synCsn (.cv x)) B) (synCssetk)))
      (synWa (.classEq A (synCphi (.cv x))) (.classMem (.cv x) B))
      (synWa (.classMem (.cv x) B) (.classEq A (synCphi (.cv x)))) p0031 p0039 p0040
  have p0042 :=
    @gExbii
      (synWex t (synWa (.classEq (.cv t) (synCsn (.cv x))) (synWa
            (.classMem (synCopk A (.cv x)) (synCcnvk (synCimagek (synCun (synCin
                      (synCimagek (synCimak (synCdif (synCins3k (synCcompl (synCimak
                                  (synCin (synCins3k (synCssetk)) (synCins2k (synCssetk)))
                                  (synCpw1 (synCpw1 (synC1c)))))) (synCimak
                              (synCsymdif (synCins2k (synCins2k (synCssetk)))
                                (synCun (synCins2k (synCins3k (synCssetk)))
                                  (synCins3k (synCsik (synCsik (synCssetk))))))
                              (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))
                          (synCpw1 (synCpw1 (synC1c))))) (synCxpk (synCnnc) (synCvv)))
                    (synCin (synCidk) (synCxpk (synCcompl (synCnnc)) (synCvv)))))))
            (.classMem (synCopk (.cv t) B) (synCssetk)))))
      (synWa (.classMem (.cv x) B) (.classEq A (synCphi (.cv x)))) x p0041
  have p0043 :=
    @gN3bitr2i
      (synWex t (synWa (.classMem (synCopk (synCsn A) (.cv t)) (synCsik (synCcnvk
                (synCimagek (synCun (synCin (synCimagek (synCimak (synCdif (synCins3k
                              (synCcompl (synCimak (synCin (synCins3k (synCssetk))
                                    (synCins2k (synCssetk)))
                                  (synCpw1 (synCpw1 (synC1c)))))) (synCimak
                              (synCsymdif (synCins2k (synCins2k (synCssetk)))
                                (synCun (synCins2k (synCins3k (synCssetk)))
                                  (synCins3k (synCsik (synCsik (synCssetk))))))
                              (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))
                          (synCpw1 (synCpw1 (synC1c))))) (synCxpk (synCnnc) (synCvv)))
                    (synCin (synCidk) (synCxpk (synCcompl (synCnnc)) (synCvv))))))))
          (.classMem (synCopk (.cv t) B) (synCssetk))))
      (synWex t (synWex x (synWa (.classEq (.cv t) (synCsn (.cv x))) (synWa
              (.classMem (synCopk A (.cv x)) (synCcnvk (synCimagek (synCun (synCin
                        (synCimagek (synCimak (synCdif (synCins3k (synCcompl (synCimak
                                    (synCin (synCins3k (synCssetk))
                                      (synCins2k (synCssetk)))
                                    (synCpw1 (synCpw1 (synC1c)))))) (synCimak
                                (synCsymdif (synCins2k (synCins2k (synCssetk)))
                                  (synCun (synCins2k (synCins3k (synCssetk)))
                                    (synCins3k (synCsik (synCsik (synCssetk))))))
                                (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))
                            (synCpw1 (synCpw1 (synC1c))))) (synCxpk (synCnnc) (synCvv)))
                      (synCin (synCidk) (synCxpk (synCcompl (synCnnc)) (synCvv)))))))
              (.classMem (synCopk (.cv t) B) (synCssetk))))))
      (synWex x (synWex t (synWa (.classEq (.cv t) (synCsn (.cv x))) (synWa
              (.classMem (synCopk A (.cv x)) (synCcnvk (synCimagek (synCun (synCin
                        (synCimagek (synCimak (synCdif (synCins3k (synCcompl (synCimak
                                    (synCin (synCins3k (synCssetk))
                                      (synCins2k (synCssetk)))
                                    (synCpw1 (synCpw1 (synC1c)))))) (synCimak
                                (synCsymdif (synCins2k (synCins2k (synCssetk)))
                                  (synCun (synCins2k (synCins3k (synCssetk)))
                                    (synCins3k (synCsik (synCsik (synCssetk))))))
                                (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))
                            (synCpw1 (synCpw1 (synC1c))))) (synCxpk (synCnnc) (synCvv)))
                      (synCin (synCidk) (synCxpk (synCcompl (synCnnc)) (synCvv)))))))
              (.classMem (synCopk (.cv t) B) (synCssetk))))))
      (synWex x (synWa (.classMem (.cv x) B) (.classEq A (synCphi (.cv x))))) p0025
      p0026 p0042
  have p0044 :=
    @gOpkelcok t (synCsn A) B (synCssetk)
      (synCsik (synCcnvk (synCimagek (synCun (synCin (synCimagek (synCimak (synCdif
                      (synCins3k (synCcompl (synCimak
                            (synCin (synCins3k (synCssetk)) (synCins2k (synCssetk)))
                            (synCpw1 (synCpw1 (synC1c)))))) (synCimak
                        (synCsymdif (synCins2k (synCins2k (synCssetk)))
                          (synCun (synCins2k (synCins3k (synCssetk)))
                            (synCins3k (synCsik (synCsik (synCssetk))))))
                        (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))
                    (synCpw1 (synCpw1 (synC1c))))) (synCxpk (synCnnc) (synCvv)))
              (synCin (synCidk) (synCxpk (synCcompl (synCnnc)) (synCvv)))))))
      dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 p0000 hyp_setconslem1_2
  have p0045 := (Nominal.biimpRefl (synWrex x B (.classEq A (synCphi (.cv x)))))
  have p0046 :=
    @gN3bitr4i
      (synWex t (synWa (.classMem (synCopk (synCsn A) (.cv t)) (synCsik (synCcnvk
                (synCimagek (synCun (synCin (synCimagek (synCimak (synCdif (synCins3k
                              (synCcompl (synCimak (synCin (synCins3k (synCssetk))
                                    (synCins2k (synCssetk)))
                                  (synCpw1 (synCpw1 (synC1c)))))) (synCimak
                              (synCsymdif (synCins2k (synCins2k (synCssetk)))
                                (synCun (synCins2k (synCins3k (synCssetk)))
                                  (synCins3k (synCsik (synCsik (synCssetk))))))
                              (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))
                          (synCpw1 (synCpw1 (synC1c))))) (synCxpk (synCnnc) (synCvv)))
                    (synCin (synCidk) (synCxpk (synCcompl (synCnnc)) (synCvv))))))))
          (.classMem (synCopk (.cv t) B) (synCssetk))))
      (synWex x (synWa (.classMem (.cv x) B) (.classEq A (synCphi (.cv x)))))
      (.classMem (synCopk (synCsn A) B) (synCcomk (synCssetk) (synCsik (synCcnvk
              (synCimagek (synCun (synCin (synCimagek (synCimak (synCdif (synCins3k
                            (synCcompl (synCimak (synCin (synCins3k (synCssetk))
                                  (synCins2k (synCssetk))) (synCpw1 (synCpw1 (synC1c))))))
                          (synCimak (synCsymdif (synCins2k (synCins2k (synCssetk)))
                              (synCun (synCins2k (synCins3k (synCssetk)))
                                (synCins3k (synCsik (synCsik (synCssetk))))))
                            (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))
                        (synCpw1 (synCpw1 (synC1c))))) (synCxpk (synCnnc) (synCvv)))
                  (synCin (synCidk) (synCxpk (synCcompl (synCnnc)) (synCvv)))))))))
      (synWrex x B (.classEq A (synCphi (.cv x)))) p0043 p0044 p0045
  exact p0046


end NFChoice.DirectNominalPrf.WPPReplay

end
