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

@[expose]
noncomputable def g_unopab (ph : Wff) (ps : Wff) (x : Var) (y : Var) :
    Nominal.NPrf
      (.classEq (syn_cun (syn_copab x y ph) (syn_copab x y ps))
        (syn_copab x y (syn_wo ph ps))) :=
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
  have dv_cache_0005 : z ∉ ((syn_wo ph ps)).fv :=
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
    @g_unab
      (syn_wex x (syn_wex y (syn_wa (.classEq (.cv z) (syn_cop (.cv x) (.cv y))) ph)))
      (syn_wex x (syn_wex y (syn_wa (.classEq (.cv z) (syn_cop (.cv x) (.cv y))) ps))) z
  have p0001 :=
    @g_n_19_43 (syn_wex y (syn_wa (.classEq (.cv z) (syn_cop (.cv x) (.cv y))) ph))
      (syn_wex y (syn_wa (.classEq (.cv z) (syn_cop (.cv x) (.cv y))) ps)) x
  have p0002 := @g_andi (.classEq (.cv z) (syn_cop (.cv x) (.cv y))) ph ps
  have p0003 :=
    @g_exbii (syn_wa (.classEq (.cv z) (syn_cop (.cv x) (.cv y))) (syn_wo ph ps))
      (syn_wo (syn_wa (.classEq (.cv z) (syn_cop (.cv x) (.cv y))) ph)
        (syn_wa (.classEq (.cv z) (syn_cop (.cv x) (.cv y))) ps))
      y p0002
  have p0004 :=
    @g_n_19_43 (syn_wa (.classEq (.cv z) (syn_cop (.cv x) (.cv y))) ph)
      (syn_wa (.classEq (.cv z) (syn_cop (.cv x) (.cv y))) ps) y
  have p0005 :=
    @g_bitr2i
      (syn_wex y (syn_wa (.classEq (.cv z) (syn_cop (.cv x) (.cv y))) (syn_wo ph ps)))
      (syn_wex y (syn_wo (syn_wa (.classEq (.cv z) (syn_cop (.cv x) (.cv y))) ph)
          (syn_wa (.classEq (.cv z) (syn_cop (.cv x) (.cv y))) ps)))
      (syn_wo (syn_wex y (syn_wa (.classEq (.cv z) (syn_cop (.cv x) (.cv y))) ph))
        (syn_wex y (syn_wa (.classEq (.cv z) (syn_cop (.cv x) (.cv y))) ps)))
      p0003 p0004
  have p0006 :=
    @g_exbii
      (syn_wo (syn_wex y (syn_wa (.classEq (.cv z) (syn_cop (.cv x) (.cv y))) ph))
        (syn_wex y (syn_wa (.classEq (.cv z) (syn_cop (.cv x) (.cv y))) ps)))
      (syn_wex y (syn_wa (.classEq (.cv z) (syn_cop (.cv x) (.cv y))) (syn_wo ph ps))) x
      p0005
  have p0007 :=
    @g_bitr3i
      (syn_wo (syn_wex x (syn_wex y (syn_wa (.classEq (.cv z) (syn_cop (.cv x) (.cv y))) ph)))
        (syn_wex x (syn_wex y (syn_wa (.classEq (.cv z) (syn_cop (.cv x) (.cv y))) ps))))
      (syn_wex x (syn_wo (syn_wex y (syn_wa (.classEq (.cv z) (syn_cop (.cv x) (.cv y))) ph))
          (syn_wex y (syn_wa (.classEq (.cv z) (syn_cop (.cv x) (.cv y))) ps))))
      (syn_wex x
        (syn_wex y (syn_wa (.classEq (.cv z) (syn_cop (.cv x) (.cv y))) (syn_wo ph ps))))
      p0001 p0006
  have p0008 :=
    @g_abbii
      (syn_wo (syn_wex x (syn_wex y (syn_wa (.classEq (.cv z) (syn_cop (.cv x) (.cv y))) ph)))
        (syn_wex x (syn_wex y (syn_wa (.classEq (.cv z) (syn_cop (.cv x) (.cv y))) ps))))
      (syn_wex x
        (syn_wex y (syn_wa (.classEq (.cv z) (syn_cop (.cv x) (.cv y))) (syn_wo ph ps))))
      z p0007
  have p0009 :=
    @g_eqtri
      (syn_cun (.cab z (syn_wex x
            (syn_wex y (syn_wa (.classEq (.cv z) (syn_cop (.cv x) (.cv y))) ph)))) (.cab z
          (syn_wex x (syn_wex y (syn_wa (.classEq (.cv z) (syn_cop (.cv x) (.cv y))) ps)))))
      (.cab z (syn_wo
          (syn_wex x (syn_wex y (syn_wa (.classEq (.cv z) (syn_cop (.cv x) (.cv y))) ph)))
          (syn_wex x (syn_wex y (syn_wa (.classEq (.cv z) (syn_cop (.cv x) (.cv y))) ps)))))
      (.cab z (syn_wex x (syn_wex y
            (syn_wa (.classEq (.cv z) (syn_cop (.cv x) (.cv y))) (syn_wo ph ps)))))
      p0000 p0008
  have p0010 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominal_df_opab ph x y z
      dv_cache_0001 dv_cache_0002 dv_cache_0003
  have p0011 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominal_df_opab ps x y z
      dv_cache_0004 dv_cache_0002 dv_cache_0003
  have p0012 :=
    @g_uneq12i (syn_copab x y ph)
      (.cab z (syn_wex x (syn_wex y (syn_wa (.classEq (.cv z) (syn_cop (.cv x) (.cv y))) ph))))
      (syn_copab x y ps)
      (.cab z (syn_wex x (syn_wex y (syn_wa (.classEq (.cv z) (syn_cop (.cv x) (.cv y))) ps))))
      p0010 p0011
  have p0013 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominal_df_opab (syn_wo ph ps)
      x y z dv_cache_0005 dv_cache_0002 dv_cache_0003
  have p0014 :=
    @g_n_3eqtr4i
      (syn_cun (.cab z (syn_wex x
            (syn_wex y (syn_wa (.classEq (.cv z) (syn_cop (.cv x) (.cv y))) ph)))) (.cab z
          (syn_wex x (syn_wex y (syn_wa (.classEq (.cv z) (syn_cop (.cv x) (.cv y))) ps)))))
      (.cab z (syn_wex x (syn_wex y
            (syn_wa (.classEq (.cv z) (syn_cop (.cv x) (.cv y))) (syn_wo ph ps)))))
      (syn_cun (syn_copab x y ph) (syn_copab x y ps)) (syn_copab x y (syn_wo ph ps)) p0009
      p0012 p0013
  exact p0014

@[expose]
noncomputable def g_breq (A : Class) (B : Class) (R : Class) (S : Class) :
    Nominal.NPrf (.imp (.classEq R S) (syn_wb (syn_wbr A R B) (syn_wbr A S B))) :=
  by
  have p0000 := @g_eleq2 R S (syn_cop A B)
  have p0001 := (Nominal.biimpRefl (syn_wbr A R B))
  have p0002 := (Nominal.biimpRefl (syn_wbr A S B))
  have p0003 :=
    @g_n_3bitr4g (.classEq R S) (.classMem (syn_cop A B) R) (.classMem (syn_cop A B) S)
      (syn_wbr A R B) (syn_wbr A S B) p0000 p0001 p0002
  exact p0003

@[expose]
noncomputable def g_breq1 (A : Class) (B : Class) (C : Class) (R : Class) :
    Nominal.NPrf (.imp (.classEq A B) (syn_wb (syn_wbr A R C) (syn_wbr B R C))) :=
  by
  have p0000 := @g_opeq1 A B C
  have p0001 := @g_eleq1d (.classEq A B) (syn_cop A C) (syn_cop B C) R p0000
  have p0002 := (Nominal.biimpRefl (syn_wbr A R C))
  have p0003 := (Nominal.biimpRefl (syn_wbr B R C))
  have p0004 :=
    @g_n_3bitr4g (.classEq A B) (.classMem (syn_cop A C) R) (.classMem (syn_cop B C) R)
      (syn_wbr A R C) (syn_wbr B R C) p0001 p0002 p0003
  exact p0004

@[expose]
noncomputable def g_breq2 (A : Class) (B : Class) (C : Class) (R : Class) :
    Nominal.NPrf (.imp (.classEq A B) (syn_wb (syn_wbr C R A) (syn_wbr C R B))) :=
  by
  have p0000 := @g_opeq2 A B C
  have p0001 := @g_eleq1d (.classEq A B) (syn_cop C A) (syn_cop C B) R p0000
  have p0002 := (Nominal.biimpRefl (syn_wbr C R A))
  have p0003 := (Nominal.biimpRefl (syn_wbr C R B))
  have p0004 :=
    @g_n_3bitr4g (.classEq A B) (.classMem (syn_cop C A) R) (.classMem (syn_cop C B) R)
      (syn_wbr C R A) (syn_wbr C R B) p0001 p0002 p0003
  exact p0004

@[expose]
noncomputable def g_breq12 (A : Class) (B : Class) (C : Class) (D : Class) (R : Class) :
    Nominal.NPrf
      (.imp (syn_wa (.classEq A B) (.classEq C D)) (syn_wb (syn_wbr A R C) (syn_wbr B R D))) :=
  by
  have p0000 := @g_breq1 A B C R
  have p0001 := @g_breq2 C D B R
  have p0002 :=
    @g_sylan9bb (.classEq A B) (syn_wbr A R C) (syn_wbr B R C) (.classEq C D)
      (syn_wbr B R D) p0000 p0001
  exact p0002

@[expose]
noncomputable def g_breqi (A : Class) (B : Class) (R : Class) (S : Class)
    (hyp_breqi_1 : Nominal.NPrf (.classEq R S)) :
    Nominal.NPrf (syn_wb (syn_wbr A R B) (syn_wbr A S B)) :=
  by
  have p0000 := @g_breq A B R S
  have p0001 := Nominal.mp hyp_breqi_1 p0000
  exact p0001

@[expose]
noncomputable def g_breq1i (A : Class) (B : Class) (C : Class) (R : Class)
    (hyp_breq1i_1 : Nominal.NPrf (.classEq A B)) :
    Nominal.NPrf (syn_wb (syn_wbr A R C) (syn_wbr B R C)) :=
  by
  have p0000 := @g_breq1 A B C R
  have p0001 := Nominal.mp hyp_breq1i_1 p0000
  exact p0001

@[expose]
noncomputable def g_breq2i (A : Class) (B : Class) (C : Class) (R : Class)
    (hyp_breq1i_1 : Nominal.NPrf (.classEq A B)) :
    Nominal.NPrf (syn_wb (syn_wbr C R A) (syn_wbr C R B)) :=
  by
  have p0000 := @g_breq2 A B C R
  have p0001 := Nominal.mp hyp_breq1i_1 p0000
  exact p0001

@[expose]
noncomputable def g_breq12i (A : Class) (B : Class) (C : Class) (D : Class) (R : Class)
    (hyp_breq1i_1 : Nominal.NPrf (.classEq A B))
    (hyp_breq12i_2 : Nominal.NPrf (.classEq C D)) :
    Nominal.NPrf (syn_wb (syn_wbr A R C) (syn_wbr B R D)) :=
  by
  have p0000 := @g_breq12 A B C D R
  have p0001 :=
    @g_mp2an (.classEq A B) (.classEq C D) (syn_wb (syn_wbr A R C) (syn_wbr B R D))
      hyp_breq1i_1 hyp_breq12i_2 p0000
  exact p0001

@[expose]
noncomputable def g_breq1d (ph : Wff) (A : Class) (B : Class) (C : Class) (R : Class)
    (hyp_breq1d_1 : Nominal.NPrf (.imp ph (.classEq A B))) :
    Nominal.NPrf (.imp ph (syn_wb (syn_wbr A R C) (syn_wbr B R C))) :=
  by
  have p0000 := @g_breq1 A B C R
  have p0001 :=
    @g_syl ph (.classEq A B) (syn_wb (syn_wbr A R C) (syn_wbr B R C)) hyp_breq1d_1 p0000
  exact p0001

@[expose]
noncomputable def g_breqd (ph : Wff) (A : Class) (B : Class) (C : Class) (D : Class)
    (hyp_breq1d_1 : Nominal.NPrf (.imp ph (.classEq A B))) :
    Nominal.NPrf (.imp ph (syn_wb (syn_wbr C A D) (syn_wbr C B D))) :=
  by
  have p0000 := @g_breq C D A B
  have p0001 :=
    @g_syl ph (.classEq A B) (syn_wb (syn_wbr C A D) (syn_wbr C B D)) hyp_breq1d_1 p0000
  exact p0001

@[expose]
noncomputable def g_breq2d (ph : Wff) (A : Class) (B : Class) (C : Class) (R : Class)
    (hyp_breq1d_1 : Nominal.NPrf (.imp ph (.classEq A B))) :
    Nominal.NPrf (.imp ph (syn_wb (syn_wbr C R A) (syn_wbr C R B))) :=
  by
  have p0000 := @g_breq2 A B C R
  have p0001 :=
    @g_syl ph (.classEq A B) (syn_wb (syn_wbr C R A) (syn_wbr C R B)) hyp_breq1d_1 p0000
  exact p0001

@[expose]
noncomputable def g_breq12d (ph : Wff) (A : Class) (B : Class) (C : Class) (D : Class)
    (R : Class) (hyp_breq1d_1 : Nominal.NPrf (.imp ph (.classEq A B)))
    (hyp_breq12d_2 : Nominal.NPrf (.imp ph (.classEq C D))) :
    Nominal.NPrf (.imp ph (syn_wb (syn_wbr A R C) (syn_wbr B R D))) :=
  by
  have p0000 := @g_breq12 A B C D R
  have p0001 :=
    @g_syl2anc ph (.classEq A B) (.classEq C D) (syn_wb (syn_wbr A R C) (syn_wbr B R D))
      hyp_breq1d_1 hyp_breq12d_2 p0000
  exact p0001

@[expose]
noncomputable def g_breqan12d (ph : Wff) (ps : Wff) (A : Class) (B : Class) (C : Class)
    (D : Class) (R : Class) (hyp_breq1d_1 : Nominal.NPrf (.imp ph (.classEq A B)))
    (hyp_breqan12i_2 : Nominal.NPrf (.imp ps (.classEq C D))) :
    Nominal.NPrf (.imp (syn_wa ph ps) (syn_wb (syn_wbr A R C) (syn_wbr B R D))) :=
  by
  have p0000 := @g_breq12 A B C D R
  have p0001 :=
    @g_syl2an ph (.classEq A B) (.classEq C D) (syn_wb (syn_wbr A R C) (syn_wbr B R D)) ps
      hyp_breq1d_1 hyp_breqan12i_2 p0000
  exact p0001

@[expose]
noncomputable def g_eqbrtri (A : Class) (B : Class) (C : Class) (R : Class)
    (hyp_eqbrtr_1 : Nominal.NPrf (.classEq A B))
    (hyp_eqbrtr_2 : Nominal.NPrf (syn_wbr B R C)) : Nominal.NPrf (syn_wbr A R C) :=
  by
  have p0000 := @g_breq1i A B C R hyp_eqbrtr_1
  have p0001 := @g_mpbir (syn_wbr A R C) (syn_wbr B R C) hyp_eqbrtr_2 p0000
  exact p0001

@[expose]
noncomputable def g_eqbrtrd (ph : Wff) (A : Class) (B : Class) (C : Class) (R : Class)
    (hyp_eqbrtrd_1 : Nominal.NPrf (.imp ph (.classEq A B)))
    (hyp_eqbrtrd_2 : Nominal.NPrf (.imp ph (syn_wbr B R C))) :
    Nominal.NPrf (.imp ph (syn_wbr A R C)) :=
  by
  have p0000 := @g_breq1d ph A B C R hyp_eqbrtrd_1
  have p0001 := @g_mpbird ph (syn_wbr A R C) (syn_wbr B R C) hyp_eqbrtrd_2 p0000
  exact p0001

@[expose]
noncomputable def g_eqbrtrri (A : Class) (B : Class) (C : Class) (R : Class)
    (hyp_eqbrtrr_1 : Nominal.NPrf (.classEq A B))
    (hyp_eqbrtrr_2 : Nominal.NPrf (syn_wbr A R C)) : Nominal.NPrf (syn_wbr B R C) :=
  by
  have p0000 := @g_eqcomi A B hyp_eqbrtrr_1
  have p0001 := @g_eqbrtri B A C R p0000 hyp_eqbrtrr_2
  exact p0001

@[expose]
noncomputable def g_eqbrtrrd (ph : Wff) (A : Class) (B : Class) (C : Class) (R : Class)
    (hyp_eqbrtrrd_1 : Nominal.NPrf (.imp ph (.classEq A B)))
    (hyp_eqbrtrrd_2 : Nominal.NPrf (.imp ph (syn_wbr A R C))) :
    Nominal.NPrf (.imp ph (syn_wbr B R C)) :=
  by
  have p0000 := @g_eqcomd ph A B hyp_eqbrtrrd_1
  have p0001 := @g_eqbrtrd ph B A C R p0000 hyp_eqbrtrrd_2
  exact p0001

@[expose]
noncomputable def g_breqtri (A : Class) (B : Class) (C : Class) (R : Class)
    (hyp_breqtr_1 : Nominal.NPrf (syn_wbr A R B))
    (hyp_breqtr_2 : Nominal.NPrf (.classEq B C)) : Nominal.NPrf (syn_wbr A R C) :=
  by
  have p0000 := @g_breq2i B C A R hyp_breqtr_2
  have p0001 := @g_mpbi (syn_wbr A R B) (syn_wbr A R C) hyp_breqtr_1 p0000
  exact p0001

@[expose]
noncomputable def g_breqtrd (ph : Wff) (A : Class) (B : Class) (C : Class) (R : Class)
    (hyp_breqtrd_1 : Nominal.NPrf (.imp ph (syn_wbr A R B)))
    (hyp_breqtrd_2 : Nominal.NPrf (.imp ph (.classEq B C))) :
    Nominal.NPrf (.imp ph (syn_wbr A R C)) :=
  by
  have p0000 := @g_breq2d ph B C A R hyp_breqtrd_2
  have p0001 := @g_mpbid ph (syn_wbr A R B) (syn_wbr A R C) hyp_breqtrd_1 p0000
  exact p0001

@[expose]
noncomputable def g_breqtrri (A : Class) (B : Class) (C : Class) (R : Class)
    (hyp_breqtrr_1 : Nominal.NPrf (syn_wbr A R B))
    (hyp_breqtrr_2 : Nominal.NPrf (.classEq C B)) : Nominal.NPrf (syn_wbr A R C) :=
  by
  have p0000 := @g_eqcomi C B hyp_breqtrr_2
  have p0001 := @g_breqtri A B C R hyp_breqtrr_1 p0000
  exact p0001

@[expose]
noncomputable def g_breqtrrd (ph : Wff) (A : Class) (B : Class) (C : Class) (R : Class)
    (hyp_breqtrrd_1 : Nominal.NPrf (.imp ph (syn_wbr A R B)))
    (hyp_breqtrrd_2 : Nominal.NPrf (.imp ph (.classEq C B))) :
    Nominal.NPrf (.imp ph (syn_wbr A R C)) :=
  by
  have p0000 := @g_eqcomd ph C B hyp_breqtrrd_2
  have p0001 := @g_breqtrd ph A B C R hyp_breqtrrd_1 p0000
  exact p0001

@[expose]
noncomputable def g_n_3brtr3i (A : Class) (B : Class) (C : Class) (D : Class) (R : Class)
    (hyp_n_3brtr3_1 : Nominal.NPrf (syn_wbr A R B))
    (hyp_n_3brtr3_2 : Nominal.NPrf (.classEq A C))
    (hyp_n_3brtr3_3 : Nominal.NPrf (.classEq B D)) : Nominal.NPrf (syn_wbr C R D) :=
  by
  have p0000 := @g_eqbrtrri A C B R hyp_n_3brtr3_2 hyp_n_3brtr3_1
  have p0001 := @g_breqtri C B D R p0000 hyp_n_3brtr3_3
  exact p0001

@[expose]
noncomputable def g_n_3brtr4d (ph : Wff) (A : Class) (B : Class) (C : Class) (D : Class)
    (R : Class) (hyp_n_3brtr4d_1 : Nominal.NPrf (.imp ph (syn_wbr A R B)))
    (hyp_n_3brtr4d_2 : Nominal.NPrf (.imp ph (.classEq C A)))
    (hyp_n_3brtr4d_3 : Nominal.NPrf (.imp ph (.classEq D B))) :
    Nominal.NPrf (.imp ph (syn_wbr C R D)) :=
  by
  have p0000 := @g_breq12d ph C A D B R hyp_n_3brtr4d_2 hyp_n_3brtr4d_3
  have p0001 := @g_mpbird ph (syn_wbr C R D) (syn_wbr A R B) hyp_n_3brtr4d_1 p0000
  exact p0001

@[expose]
noncomputable def g_n_3brtr3g (ph : Wff) (A : Class) (B : Class) (C : Class) (D : Class)
    (R : Class) (hyp_n_3brtr3g_1 : Nominal.NPrf (.imp ph (syn_wbr A R B)))
    (hyp_n_3brtr3g_2 : Nominal.NPrf (.classEq A C))
    (hyp_n_3brtr3g_3 : Nominal.NPrf (.classEq B D)) :
    Nominal.NPrf (.imp ph (syn_wbr C R D)) :=
  by
  have p0000 := @g_breq12i A C B D R hyp_n_3brtr3g_2 hyp_n_3brtr3g_3
  have p0001 := @g_sylib ph (syn_wbr A R B) (syn_wbr C R D) hyp_n_3brtr3g_1 p0000
  exact p0001

@[expose]
noncomputable def g_syl5eqbrr (ph : Wff) (A : Class) (B : Class) (C : Class) (R : Class)
    (hyp_syl5eqbrr_1 : Nominal.NPrf (.classEq B A))
    (hyp_syl5eqbrr_2 : Nominal.NPrf (.imp ph (syn_wbr B R C))) :
    Nominal.NPrf (.imp ph (syn_wbr A R C)) :=
  by
  have p0000 := @g_eqid C
  have p0001 := @g_n_3brtr3g ph B C A C R hyp_syl5eqbrr_2 hyp_syl5eqbrr_1 p0000
  exact p0001

@[expose]
noncomputable def g_syl5breq (ph : Wff) (A : Class) (B : Class) (C : Class) (R : Class)
    (hyp_syl5breq_1 : Nominal.NPrf (syn_wbr A R B))
    (hyp_syl5breq_2 : Nominal.NPrf (.imp ph (.classEq B C))) :
    Nominal.NPrf (.imp ph (syn_wbr A R C)) :=
  by
  have p0000 := @g_a1i (syn_wbr A R B) ph hyp_syl5breq_1
  have p0001 := @g_breqtrd ph A B C R p0000 hyp_syl5breq_2
  exact p0001

@[expose]
noncomputable def g_syl6eqbr (ph : Wff) (A : Class) (B : Class) (C : Class) (R : Class)
    (hyp_syl6eqbr_1 : Nominal.NPrf (.imp ph (.classEq A B)))
    (hyp_syl6eqbr_2 : Nominal.NPrf (syn_wbr B R C)) :
    Nominal.NPrf (.imp ph (syn_wbr A R C)) :=
  by
  have p0000 := @g_breq1d ph A B C R hyp_syl6eqbr_1
  have p0001 := @g_mpbiri ph (syn_wbr A R C) (syn_wbr B R C) hyp_syl6eqbr_2 p0000
  exact p0001

@[expose]
noncomputable def g_ssbrd (ph : Wff) (A : Class) (B : Class) (C : Class) (D : Class)
    (hyp_ssbrd_1 : Nominal.NPrf (.imp ph (syn_wss A B))) :
    Nominal.NPrf (.imp ph (.imp (syn_wbr C A D) (syn_wbr C B D))) :=
  by
  have p0000 := @g_sseld ph A B (syn_cop C D) hyp_ssbrd_1
  have p0001 := (Nominal.biimpRefl (syn_wbr C A D))
  have p0002 := (Nominal.biimpRefl (syn_wbr C B D))
  have p0003 :=
    @g_n_3imtr4g ph (.classMem (syn_cop C D) A) (.classMem (syn_cop C D) B)
      (syn_wbr C A D) (syn_wbr C B D) p0000 p0001 p0002
  exact p0003

@[expose]
noncomputable def g_ssbri (A : Class) (B : Class) (C : Class) (D : Class)
    (hyp_ssbri_1 : Nominal.NPrf (syn_wss A B)) :
    Nominal.NPrf (.imp (syn_wbr C A D) (syn_wbr C B D)) :=
  by
  have p0000 := @g_ssid A
  have p0001 := @g_a1i (syn_wss A B) (syn_wss A A) hyp_ssbri_1
  have p0002 := @g_ssbrd (syn_wss A A) A B C D p0001
  have p0003 := Nominal.mp p0000 p0002
  exact p0003

@[expose]
noncomputable def g_nfbrd (ph : Wff) (x : Var) (A : Class) (B : Class) (R : Class)
    (hyp_nfbrd_2 : Nominal.NPrf (.imp ph (syn_wnfc x A)))
    (hyp_nfbrd_3 : Nominal.NPrf (.imp ph (syn_wnfc x R)))
    (hyp_nfbrd_4 : Nominal.NPrf (.imp ph (syn_wnfc x B))) :
    Nominal.NPrf (.imp ph (syn_wnf x (syn_wbr A R B))) :=
  by
  have p0000 := (Nominal.biimpRefl (syn_wbr A R B))
  have p0001 := @g_nfopd ph x A B hyp_nfbrd_2 hyp_nfbrd_4
  have p0002 := @g_nfeld ph x (syn_cop A B) R p0001 hyp_nfbrd_3
  have p0003 := @g_nfxfrd (syn_wbr A R B) (.classMem (syn_cop A B) R) ph x p0000 p0002
  exact p0003

@[expose]
noncomputable def g_nfbr (x : Var) (A : Class) (B : Class) (R : Class)
    (hyp_nfbr_1 : Nominal.NPrf (syn_wnfc x A)) (hyp_nfbr_2 : Nominal.NPrf (syn_wnfc x R))
    (hyp_nfbr_3 : Nominal.NPrf (syn_wnfc x B)) :
    Nominal.NPrf (syn_wnf x (syn_wbr A R B)) :=
  by
  have p0000 := @g_a1i (syn_wnfc x A) syn_wtru hyp_nfbr_1
  have p0001 := @g_a1i (syn_wnfc x R) syn_wtru hyp_nfbr_2
  have p0002 := @g_a1i (syn_wnfc x B) syn_wtru hyp_nfbr_3
  have p0003 := @g_nfbrd syn_wtru x A B R p0000 p0001 p0002
  have p0004 := @g_trud (syn_wnf x (syn_wbr A R B)) p0003
  exact p0004

@[expose]
noncomputable def g_brex (A : Class) (B : Class) (R : Class) :
    Nominal.NPrf
      (.imp (syn_wbr A R B) (syn_wa (.classMem A (syn_cvv)) (.classMem B (syn_cvv)))) :=
  by
  have p0000 := @g_elex (syn_cop A B) R
  have p0001 := (Nominal.biimpRefl (syn_wbr A R B))
  have p0002 := @g_opexb A B
  have p0003 :=
    @g_bicomi (.classMem (syn_cop A B) (syn_cvv))
      (syn_wa (.classMem A (syn_cvv)) (.classMem B (syn_cvv))) p0002
  have p0004 :=
    @g_n_3imtr4i (.classMem (syn_cop A B) R) (.classMem (syn_cop A B) (syn_cvv))
      (syn_wbr A R B) (syn_wa (.classMem A (syn_cvv)) (.classMem B (syn_cvv))) p0000 p0001
      p0003
  exact p0004

@[expose]
noncomputable def g_brreldmex (A : Class) (B : Class) (R : Class) :
    Nominal.NPrf (.imp (syn_wbr A R B) (.classMem A (syn_cvv))) :=
  by
  have p0000 := @g_brex A B R
  have p0001 :=
    @g_simpld (syn_wbr A R B) (.classMem A (syn_cvv)) (.classMem B (syn_cvv)) p0000
  exact p0001

@[expose]
noncomputable def g_brrelrnex (A : Class) (B : Class) (R : Class) :
    Nominal.NPrf (.imp (syn_wbr A R B) (.classMem B (syn_cvv))) :=
  by
  have p0000 := @g_brex A B R
  have p0001 :=
    @g_simprd (syn_wbr A R B) (.classMem A (syn_cvv)) (.classMem B (syn_cvv)) p0000
  exact p0001

@[expose]
noncomputable def g_brun (A : Class) (B : Class) (R : Class) (S : Class) :
    Nominal.NPrf
      (syn_wb (syn_wbr A (syn_cun R S) B) (syn_wo (syn_wbr A R B) (syn_wbr A S B))) :=
  by
  have p0000 := @g_elun (syn_cop A B) R S
  have p0001 := (Nominal.biimpRefl (syn_wbr A (syn_cun R S) B))
  have p0002 := (Nominal.biimpRefl (syn_wbr A R B))
  have p0003 := (Nominal.biimpRefl (syn_wbr A S B))
  have p0004 :=
    @g_orbi12i (syn_wbr A R B) (.classMem (syn_cop A B) R) (syn_wbr A S B)
      (.classMem (syn_cop A B) S) p0002 p0003
  have p0005 :=
    @g_n_3bitr4i (.classMem (syn_cop A B) (syn_cun R S))
      (syn_wo (.classMem (syn_cop A B) R) (.classMem (syn_cop A B) S))
      (syn_wbr A (syn_cun R S) B) (syn_wo (syn_wbr A R B) (syn_wbr A S B)) p0000 p0001
      p0004
  exact p0005

@[expose]
noncomputable def g_brin (A : Class) (B : Class) (R : Class) (S : Class) :
    Nominal.NPrf
      (syn_wb (syn_wbr A (syn_cin R S) B) (syn_wa (syn_wbr A R B) (syn_wbr A S B))) :=
  by
  have p0000 := @g_elin (syn_cop A B) R S
  have p0001 := (Nominal.biimpRefl (syn_wbr A (syn_cin R S) B))
  have p0002 := (Nominal.biimpRefl (syn_wbr A R B))
  have p0003 := (Nominal.biimpRefl (syn_wbr A S B))
  have p0004 :=
    @g_anbi12i (syn_wbr A R B) (.classMem (syn_cop A B) R) (syn_wbr A S B)
      (.classMem (syn_cop A B) S) p0002 p0003
  have p0005 :=
    @g_n_3bitr4i (.classMem (syn_cop A B) (syn_cin R S))
      (syn_wa (.classMem (syn_cop A B) R) (.classMem (syn_cop A B) S))
      (syn_wbr A (syn_cin R S) B) (syn_wa (syn_wbr A R B) (syn_wbr A S B)) p0000 p0001
      p0004
  exact p0005

@[expose]
noncomputable def g_brdif (A : Class) (B : Class) (R : Class) (S : Class) :
    Nominal.NPrf
      (syn_wb (syn_wbr A (syn_cdif R S) B) (syn_wa (syn_wbr A R B) (.neg (syn_wbr A S B)))) :=
  by
  have p0000 := @g_eldif (syn_cop A B) R S
  have p0001 := (Nominal.biimpRefl (syn_wbr A (syn_cdif R S) B))
  have p0002 := (Nominal.biimpRefl (syn_wbr A R B))
  have p0003 := (Nominal.biimpRefl (syn_wbr A S B))
  have p0004 := @g_notbii (syn_wbr A S B) (.classMem (syn_cop A B) S) p0003
  have p0005 :=
    @g_anbi12i (syn_wbr A R B) (.classMem (syn_cop A B) R) (.neg (syn_wbr A S B))
      (.neg (.classMem (syn_cop A B) S)) p0002 p0004
  have p0006 :=
    @g_n_3bitr4i (.classMem (syn_cop A B) (syn_cdif R S))
      (syn_wa (.classMem (syn_cop A B) R) (.neg (.classMem (syn_cop A B) S)))
      (syn_wbr A (syn_cdif R S) B) (syn_wa (syn_wbr A R B) (.neg (syn_wbr A S B))) p0000
      p0001 p0005
  exact p0006

@[expose]
noncomputable def g_opabid (ph : Wff) (x : Var) (y : Var) :
    Nominal.NPrf (syn_wb (.classMem (syn_cop (.cv x) (.cv y)) (syn_copab x y ph)) ph) :=
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
  have dv_cache_0006 : z ∉ ((syn_cop (.cv x) (.cv y))).fv :=
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
  have p0000 := @g_vex x
  have p0001 := @g_vex y
  have p0002 := @g_opex (.cv x) (.cv y) p0000 p0001
  have p0003 := @g_copsexg ph x y (.cv z) dv_cache_0001 dv_cache_0002
  have p0004 :=
    @g_bicomd (.classEq (.cv z) (syn_cop (.cv x) (.cv y))) ph
      (syn_wex x (syn_wex y (syn_wa (.classEq (.cv z) (syn_cop (.cv x) (.cv y))) ph)))
      p0003
  have p0005 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominal_df_opab ph x y z
      dv_cache_0003 dv_cache_0004 dv_cache_0005
  have p0006 :=
    @g_elab2
      (syn_wex x (syn_wex y (syn_wa (.classEq (.cv z) (syn_cop (.cv x) (.cv y))) ph))) ph
      z (syn_cop (.cv x) (.cv y)) (syn_copab x y ph) dv_cache_0006 dv_cache_0003 p0002
      p0004 p0005
  exact p0006

@[expose]
noncomputable def g_elopab (ph : Wff) (x : Var) (y : Var) (A : Class) (dv_A_x : x ∉ A.fv)
    (dv_A_y : y ∉ A.fv) :
    Nominal.NPrf
      (syn_wb (.classMem A (syn_copab x y ph))
        (syn_wex x (syn_wex y (syn_wa (.classEq A (syn_cop (.cv x) (.cv y))) ph)))) :=
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
  have dv_cache_0001 : x ∉ ((Wff.classMem A (syn_cvv))).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv, Finset.mem_union, dv_A_x,
          compact_fv_not_mem_empty, or_false, not_false_eq_true])
  have dv_cache_0002 : y ∉ ((Wff.classMem A (syn_cvv))).fv :=
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
    z ∉ ((syn_wex x (syn_wex y (syn_wa (.classEq A (syn_cop (.cv x) (.cv y))) ph)))).fv :=
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
  have p0000 := @g_elex A (syn_copab x y ph)
  have p0001 := @g_vex x
  have p0002 := @g_vex y
  have p0003 := @g_opex (.cv x) (.cv y) p0001 p0002
  have p0004 := @g_eleq1 A (syn_cop (.cv x) (.cv y)) (syn_cvv)
  have p0005 :=
    @g_mpbiri (.classEq A (syn_cop (.cv x) (.cv y))) (.classMem A (syn_cvv))
      (.classMem (syn_cop (.cv x) (.cv y)) (syn_cvv)) p0003 p0004
  have p0006 :=
    @g_adantr (.classEq A (syn_cop (.cv x) (.cv y))) (.classMem A (syn_cvv)) ph p0005
  have p0007 :=
    @g_exlimivv (syn_wa (.classEq A (syn_cop (.cv x) (.cv y))) ph) (.classMem A (syn_cvv))
      x y dv_cache_0001 dv_cache_0002 p0006
  have p0008 := @g_eqeq1 (.cv z) A (syn_cop (.cv x) (.cv y))
  have p0009 :=
    @g_anbi1d (.classEq (.cv z) A) (.classEq (.cv z) (syn_cop (.cv x) (.cv y)))
      (.classEq A (syn_cop (.cv x) (.cv y))) ph p0008
  have p0010 :=
    @g_n_2exbidv (.classEq (.cv z) A)
      (syn_wa (.classEq (.cv z) (syn_cop (.cv x) (.cv y))) ph)
      (syn_wa (.classEq A (syn_cop (.cv x) (.cv y))) ph) x y dv_cache_0003 dv_cache_0004
      p0009
  have p0011 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominal_df_opab ph x y z
      dv_cache_0005 dv_cache_0006 dv_cache_0007
  have p0012 :=
    @g_elab2g
      (syn_wex x (syn_wex y (syn_wa (.classEq (.cv z) (syn_cop (.cv x) (.cv y))) ph)))
      (syn_wex x (syn_wex y (syn_wa (.classEq A (syn_cop (.cv x) (.cv y))) ph))) z A
      (syn_copab x y ph) (syn_cvv) dv_cache_0008 dv_cache_0009 p0010 p0011
  have p0013 :=
    @g_pm5_21nii (.classMem A (syn_copab x y ph)) (.classMem A (syn_cvv))
      (syn_wex x (syn_wex y (syn_wa (.classEq A (syn_cop (.cv x) (.cv y))) ph))) p0000
      p0007 p0012
  exact p0013

@[expose]
noncomputable def g_opelopabsb (ph : Wff) (x : Var) (y : Var) (A : Class) (B : Class)
    (dv_B_x : x ∉ B.fv) (dv_x_y : x ≠ y) :
    Nominal.NPrf
      (syn_wb (.classMem (syn_cop A B) (syn_copab x y ph)) (syn_wsbc A x (syn_wsbc B y ph))) :=
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
  have dv_cache_0001 : x ∉ ((Wff.classMem B (syn_cvv))).fv := by
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
  have dv_cache_0003 : x ∉ ((syn_cop (.cv z) (.cv w))).fv :=
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
  have dv_cache_0005 : y ∉ ((syn_cop (.cv x) (.cv w))).fv :=
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
      ((syn_wb (.classMem (syn_cop A B) (syn_copab x y ph))
          (syn_wsbc A x (syn_wsbc B y ph)))).fv :=
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
      ((syn_wb (.classMem (syn_cop A (.cv w)) (syn_copab x y ph))
          (syn_wsbc A x (syn_wsb w y ph)))).fv :=
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
  have p0000 := (Nominal.biimpRefl (syn_wbr A (syn_copab x y ph) B))
  have p0001 := @g_brex A B (syn_copab x y ph)
  have p0002 :=
    @g_sylbir (.classMem (syn_cop A B) (syn_copab x y ph))
      (syn_wbr A (syn_copab x y ph) B)
      (syn_wa (.classMem A (syn_cvv)) (.classMem B (syn_cvv))) p0000 p0001
  have p0003 := @g_sbcex (syn_wsbc B y ph) x A
  have p0004 := @g_spesbc (syn_wsbc B y ph) x A
  have p0005 := @g_sbcex ph y B
  have p0006 := @g_exlimiv (syn_wsbc B y ph) (.classMem B (syn_cvv)) x dv_cache_0001 p0005
  have p0007 :=
    @g_syl (syn_wsbc A x (syn_wsbc B y ph)) (syn_wex x (syn_wsbc B y ph))
      (.classMem B (syn_cvv)) p0004 p0006
  have p0008 :=
    @g_jca (syn_wsbc A x (syn_wsbc B y ph)) (.classMem A (syn_cvv))
      (.classMem B (syn_cvv)) p0003 p0007
  have p0009 := @g_opeq1 (.cv z) A (.cv w)
  have p0010 :=
    @g_eleq1d (.classEq (.cv z) A) (syn_cop (.cv z) (.cv w)) (syn_cop A (.cv w))
      (syn_copab x y ph) p0009
  have p0011 := @g_dfsbcq2 (syn_wsb w y ph) x z A
  have p0012 :=
    @g_bibi12d (.classEq (.cv z) A)
      (.classMem (syn_cop (.cv z) (.cv w)) (syn_copab x y ph))
      (.classMem (syn_cop A (.cv w)) (syn_copab x y ph)) (syn_wsb z x (syn_wsb w y ph))
      (syn_wsbc A x (syn_wsb w y ph)) p0010 p0011
  have p0013 := @g_opeq2 (.cv w) B A
  have p0014 :=
    @g_eleq1d (.classEq (.cv w) B) (syn_cop A (.cv w)) (syn_cop A B) (syn_copab x y ph)
      p0013
  have p0015 := @g_dfsbcq2 ph y w B
  have p0016 :=
    @g_sbcbidv (.classEq (.cv w) B) (syn_wsb w y ph) (syn_wsbc B y ph) x A dv_cache_0002
      p0015
  have p0017 :=
    @g_bibi12d (.classEq (.cv w) B) (.classMem (syn_cop A (.cv w)) (syn_copab x y ph))
      (.classMem (syn_cop A B) (syn_copab x y ph)) (syn_wsbc A x (syn_wsb w y ph))
      (syn_wsbc A x (syn_wsbc B y ph)) p0014 p0016
  have p0018 := @g_nfopab1 ph x y
  have p0019 :=
    @g_nfel2 x (syn_cop (.cv z) (.cv w)) (syn_copab x y ph) dv_cache_0003 p0018
  have p0020 := @g_nfs1v (syn_wsb w y ph) x z dv_cache_0004
  have p0021 :=
    @g_nfbi (.classMem (syn_cop (.cv z) (.cv w)) (syn_copab x y ph))
      (syn_wsb z x (syn_wsb w y ph)) x p0019 p0020
  have p0022 := @g_opeq1 (.cv x) (.cv z) (.cv w)
  have p0023_e00_recanon :
    Nominal.NPrf
      (.imp (.objEq x z) (.classEq (syn_cop (.cv x) (.cv w)) (syn_cop (.cv z) (.cv w)))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_cop syn_cun syn_cnin syn_wnan syn_wa syn_ccompl syn_wrex syn_wex
          syn_cphi
        simp (config :=
          { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_class_cv]
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
        · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0022
  have p0023 :=
    @g_eleq1d (.objEq x z) (syn_cop (.cv x) (.cv w)) (syn_cop (.cv z) (.cv w))
      (syn_copab x y ph) p0023_e00_recanon
  have p0024 := @g_sbequ12 (syn_wsb w y ph) x z
  have p0025 :=
    @g_bibi12d (.objEq x z) (.classMem (syn_cop (.cv x) (.cv w)) (syn_copab x y ph))
      (.classMem (syn_cop (.cv z) (.cv w)) (syn_copab x y ph)) (syn_wsb w y ph)
      (syn_wsb z x (syn_wsb w y ph)) p0023 p0024
  have p0026 := @g_nfopab2 ph x y
  have p0027 :=
    @g_nfel2 y (syn_cop (.cv x) (.cv w)) (syn_copab x y ph) dv_cache_0005 p0026
  have p0028 := @g_nfs1v ph y w dv_cache_0006
  have p0029 :=
    @g_nfbi (.classMem (syn_cop (.cv x) (.cv w)) (syn_copab x y ph)) (syn_wsb w y ph) y
      p0027 p0028
  have p0030 := @g_opeq2 (.cv y) (.cv w) (.cv x)
  have p0031_e00_recanon :
    Nominal.NPrf
      (.imp (.objEq y w) (.classEq (syn_cop (.cv x) (.cv y)) (syn_cop (.cv x) (.cv w)))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_cop syn_cun syn_cnin syn_wnan syn_wa syn_ccompl syn_wrex syn_wex
          syn_cphi
        simp (config :=
          { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_class_cv]
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
        · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0030
  have p0031 :=
    @g_eleq1d (.objEq y w) (syn_cop (.cv x) (.cv y)) (syn_cop (.cv x) (.cv w))
      (syn_copab x y ph) p0031_e00_recanon
  have p0032 := @g_sbequ12 ph y w
  have p0033 :=
    @g_bibi12d (.objEq y w) (.classMem (syn_cop (.cv x) (.cv y)) (syn_copab x y ph))
      (.classMem (syn_cop (.cv x) (.cv w)) (syn_copab x y ph)) ph (syn_wsb w y ph) p0031
      p0032
  have p0034 := @g_opabid ph x y
  have p0035 :=
    @g_chvar (syn_wb (.classMem (syn_cop (.cv x) (.cv y)) (syn_copab x y ph)) ph)
      (syn_wb (.classMem (syn_cop (.cv x) (.cv w)) (syn_copab x y ph)) (syn_wsb w y ph)) y
      w p0029 p0033 p0034
  have p0036 :=
    @g_chvar
      (syn_wb (.classMem (syn_cop (.cv x) (.cv w)) (syn_copab x y ph)) (syn_wsb w y ph))
      (syn_wb (.classMem (syn_cop (.cv z) (.cv w)) (syn_copab x y ph))
        (syn_wsb z x (syn_wsb w y ph)))
      x z p0021 p0025 p0035
  have p0037 :=
    @g_vtocl2g
      (syn_wb (.classMem (syn_cop (.cv z) (.cv w)) (syn_copab x y ph))
        (syn_wsb z x (syn_wsb w y ph)))
      (syn_wb (.classMem (syn_cop A (.cv w)) (syn_copab x y ph))
        (syn_wsbc A x (syn_wsb w y ph)))
      (syn_wb (.classMem (syn_cop A B) (syn_copab x y ph)) (syn_wsbc A x (syn_wsbc B y ph)))
      z w A B (syn_cvv) (syn_cvv) dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010
      dv_cache_0011 p0012 p0017 p0036
  have p0038 :=
    @g_pm5_21nii (.classMem (syn_cop A B) (syn_copab x y ph))
      (syn_wa (.classMem A (syn_cvv)) (.classMem B (syn_cvv)))
      (syn_wsbc A x (syn_wsbc B y ph)) p0002 p0008 p0037
  exact p0038

@[expose]
noncomputable def g_opelopabga (ph : Wff) (ps : Wff) (x : Var) (y : Var) (A : Class)
    (B : Class) (V : Class) (W : Class) (dv_A_x : x ∉ A.fv) (dv_A_y : y ∉ A.fv)
    (dv_B_x : x ∉ B.fv) (dv_B_y : y ∉ B.fv) (dv_ps_x : x ∉ ps.fv) (dv_ps_y : y ∉ ps.fv)
    (dv_x_y : x ≠ y)
    (hyp_opelopabga_1 : Nominal.NPrf
        (.imp (syn_wa (.classEq (.cv x) A) (.classEq (.cv y) B)) (syn_wb ph ps))) :
    Nominal.NPrf
      (.imp (syn_wa (.classMem A V) (.classMem B W))
        (syn_wb (.classMem (syn_cop A B) (syn_copab x y ph)) ps)) :=
  by
  have dv_cache_0001 : x ∉ ((syn_cop A B)).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cop, Finset.mem_union,
          dv_A_x, dv_B_x, or_false, not_false_eq_true])
  have dv_cache_0002 : y ∉ ((syn_cop A B)).fv :=
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
  have p0000 := @g_elopab ph x y (syn_cop A B) dv_cache_0001 dv_cache_0002
  have p0001 :=
    @g_copsex2g ph ps x y A B V W dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006
      dv_cache_0007 dv_cache_0008 dv_cache_0009 hyp_opelopabga_1
  have p0002 :=
    @g_syl5bb (.classMem (syn_cop A B) (syn_copab x y ph))
      (syn_wex x (syn_wex y (syn_wa (.classEq (syn_cop A B) (syn_cop (.cv x) (.cv y))) ph)))
      (syn_wa (.classMem A V) (.classMem B W)) ps p0000 p0001
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

@[expose]
noncomputable def g_brabga (ph : Wff) (ps : Wff) (x : Var) (y : Var) (A : Class)
    (B : Class) (R : Class) (V : Class) (W : Class) (dv_A_x : x ∉ A.fv)
    (dv_A_y : y ∉ A.fv) (dv_B_x : x ∉ B.fv) (dv_B_y : y ∉ B.fv) (dv_ps_x : x ∉ ps.fv)
    (dv_ps_y : y ∉ ps.fv) (dv_x_y : x ≠ y)
    (hyp_opelopabga_1 : Nominal.NPrf
        (.imp (syn_wa (.classEq (.cv x) A) (.classEq (.cv y) B)) (syn_wb ph ps)))
    (hyp_brabga_2 : Nominal.NPrf (.classEq R (syn_copab x y ph))) :
    Nominal.NPrf
      (.imp (syn_wa (.classMem A V) (.classMem B W)) (syn_wb (syn_wbr A R B) ps)) :=
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
  have p0000 := (Nominal.biimpRefl (syn_wbr A R B))
  have p0001 := @g_eleq2i R (syn_copab x y ph) (syn_cop A B) hyp_brabga_2
  have p0002 :=
    @g_bitri (syn_wbr A R B) (.classMem (syn_cop A B) R)
      (.classMem (syn_cop A B) (syn_copab x y ph)) p0000 p0001
  have p0003 :=
    @g_opelopabga ph ps x y A B V W dv_cache_0001 dv_cache_0002 dv_cache_0003
      dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 hyp_opelopabga_1
  have p0004 :=
    @g_syl5bb (syn_wbr A R B) (.classMem (syn_cop A B) (syn_copab x y ph))
      (syn_wa (.classMem A V) (.classMem B W)) ps p0002 p0003
  exact p0004

@[expose]
noncomputable def g_opelopaba (ph : Wff) (ps : Wff) (x : Var) (y : Var) (A : Class)
    (B : Class) (dv_A_x : x ∉ A.fv) (dv_A_y : y ∉ A.fv) (dv_B_x : x ∉ B.fv)
    (dv_B_y : y ∉ B.fv) (dv_ps_x : x ∉ ps.fv) (dv_ps_y : y ∉ ps.fv) (dv_x_y : x ≠ y)
    (hyp_opelopaba_1 : Nominal.NPrf (.classMem A (syn_cvv)))
    (hyp_opelopaba_2 : Nominal.NPrf (.classMem B (syn_cvv)))
    (hyp_opelopaba_3 : Nominal.NPrf
        (.imp (syn_wa (.classEq (.cv x) A) (.classEq (.cv y) B)) (syn_wb ph ps))) :
    Nominal.NPrf (syn_wb (.classMem (syn_cop A B) (syn_copab x y ph)) ps) :=
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
    @g_opelopabga ph ps x y A B (syn_cvv) (syn_cvv) dv_cache_0001 dv_cache_0002
      dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007
      hyp_opelopaba_3
  have p0001 :=
    @g_mp2an (.classMem A (syn_cvv)) (.classMem B (syn_cvv))
      (syn_wb (.classMem (syn_cop A B) (syn_copab x y ph)) ps) hyp_opelopaba_1
      hyp_opelopaba_2 p0000
  exact p0001

@[expose]
noncomputable def g_braba (ph : Wff) (ps : Wff) (x : Var) (y : Var) (A : Class)
    (B : Class) (R : Class) (dv_A_x : x ∉ A.fv) (dv_A_y : y ∉ A.fv) (dv_B_x : x ∉ B.fv)
    (dv_B_y : y ∉ B.fv) (dv_ps_x : x ∉ ps.fv) (dv_ps_y : y ∉ ps.fv) (dv_x_y : x ≠ y)
    (hyp_opelopaba_1 : Nominal.NPrf (.classMem A (syn_cvv)))
    (hyp_opelopaba_2 : Nominal.NPrf (.classMem B (syn_cvv)))
    (hyp_opelopaba_3 : Nominal.NPrf
        (.imp (syn_wa (.classEq (.cv x) A) (.classEq (.cv y) B)) (syn_wb ph ps)))
    (hyp_braba_4 : Nominal.NPrf (.classEq R (syn_copab x y ph))) :
    Nominal.NPrf (syn_wb (syn_wbr A R B) ps) :=
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
    @g_brabga ph ps x y A B R (syn_cvv) (syn_cvv) dv_cache_0001 dv_cache_0002
      dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007
      hyp_opelopaba_3 hyp_braba_4
  have p0001 :=
    @g_mp2an (.classMem A (syn_cvv)) (.classMem B (syn_cvv)) (syn_wb (syn_wbr A R B) ps)
      hyp_opelopaba_1 hyp_opelopaba_2 p0000
  exact p0001

@[expose]
noncomputable def g_opelopabg (ph : Wff) (ps : Wff) (ch : Wff) (x : Var) (y : Var)
    (A : Class) (B : Class) (V : Class) (W : Class) (dv_A_x : x ∉ A.fv)
    (dv_A_y : y ∉ A.fv) (dv_B_x : x ∉ B.fv) (dv_B_y : y ∉ B.fv) (dv_ch_x : x ∉ ch.fv)
    (dv_ch_y : y ∉ ch.fv) (dv_x_y : x ≠ y)
    (hyp_opelopabg_1 : Nominal.NPrf (.imp (.classEq (.cv x) A) (syn_wb ph ps)))
    (hyp_opelopabg_2 : Nominal.NPrf (.imp (.classEq (.cv y) B) (syn_wb ps ch))) :
    Nominal.NPrf
      (.imp (syn_wa (.classMem A V) (.classMem B W))
        (syn_wb (.classMem (syn_cop A B) (syn_copab x y ph)) ch)) :=
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
    @g_sylan9bb (.classEq (.cv x) A) ph ps (.classEq (.cv y) B) ch hyp_opelopabg_1
      hyp_opelopabg_2
  have p0001 :=
    @g_opelopabga ph ch x y A B V W dv_cache_0001 dv_cache_0002 dv_cache_0003
      dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 p0000
  exact p0001

@[expose]
noncomputable def g_brabg (ph : Wff) (ps : Wff) (ch : Wff) (x : Var) (y : Var) (A : Class)
    (B : Class) (C : Class) (D : Class) (R : Class) (dv_A_x : x ∉ A.fv)
    (dv_A_y : y ∉ A.fv) (dv_B_x : x ∉ B.fv) (dv_B_y : y ∉ B.fv) (dv_ch_x : x ∉ ch.fv)
    (dv_ch_y : y ∉ ch.fv) (dv_x_y : x ≠ y)
    (hyp_opelopabg_1 : Nominal.NPrf (.imp (.classEq (.cv x) A) (syn_wb ph ps)))
    (hyp_opelopabg_2 : Nominal.NPrf (.imp (.classEq (.cv y) B) (syn_wb ps ch)))
    (hyp_brabg_5 : Nominal.NPrf (.classEq R (syn_copab x y ph))) :
    Nominal.NPrf
      (.imp (syn_wa (.classMem A C) (.classMem B D)) (syn_wb (syn_wbr A R B) ch)) :=
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
    @g_sylan9bb (.classEq (.cv x) A) ph ps (.classEq (.cv y) B) ch hyp_opelopabg_1
      hyp_opelopabg_2
  have p0001 :=
    @g_brabga ph ch x y A B R C D dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
      dv_cache_0005 dv_cache_0006 dv_cache_0007 p0000 hyp_brabg_5
  exact p0001

@[expose]
noncomputable def g_opelopab (ph : Wff) (ps : Wff) (ch : Wff) (x : Var) (y : Var)
    (A : Class) (B : Class) (dv_A_x : x ∉ A.fv) (dv_A_y : y ∉ A.fv) (dv_B_x : x ∉ B.fv)
    (dv_B_y : y ∉ B.fv) (dv_ch_x : x ∉ ch.fv) (dv_ch_y : y ∉ ch.fv) (dv_x_y : x ≠ y)
    (hyp_opelopab_1 : Nominal.NPrf (.classMem A (syn_cvv)))
    (hyp_opelopab_2 : Nominal.NPrf (.classMem B (syn_cvv)))
    (hyp_opelopab_3 : Nominal.NPrf (.imp (.classEq (.cv x) A) (syn_wb ph ps)))
    (hyp_opelopab_4 : Nominal.NPrf (.imp (.classEq (.cv y) B) (syn_wb ps ch))) :
    Nominal.NPrf (syn_wb (.classMem (syn_cop A B) (syn_copab x y ph)) ch) :=
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
    @g_opelopabg ph ps ch x y A B (syn_cvv) (syn_cvv) dv_cache_0001 dv_cache_0002
      dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 hyp_opelopab_3
      hyp_opelopab_4
  have p0001 :=
    @g_mp2an (.classMem A (syn_cvv)) (.classMem B (syn_cvv))
      (syn_wb (.classMem (syn_cop A B) (syn_copab x y ph)) ch) hyp_opelopab_1
      hyp_opelopab_2 p0000
  exact p0001

@[expose]
noncomputable def g_brab (ph : Wff) (ps : Wff) (ch : Wff) (x : Var) (y : Var) (A : Class)
    (B : Class) (R : Class) (dv_A_x : x ∉ A.fv) (dv_A_y : y ∉ A.fv) (dv_B_x : x ∉ B.fv)
    (dv_B_y : y ∉ B.fv) (dv_ch_x : x ∉ ch.fv) (dv_ch_y : y ∉ ch.fv) (dv_x_y : x ≠ y)
    (hyp_opelopab_1 : Nominal.NPrf (.classMem A (syn_cvv)))
    (hyp_opelopab_2 : Nominal.NPrf (.classMem B (syn_cvv)))
    (hyp_opelopab_3 : Nominal.NPrf (.imp (.classEq (.cv x) A) (syn_wb ph ps)))
    (hyp_opelopab_4 : Nominal.NPrf (.imp (.classEq (.cv y) B) (syn_wb ps ch)))
    (hyp_brab_5 : Nominal.NPrf (.classEq R (syn_copab x y ph))) :
    Nominal.NPrf (syn_wb (syn_wbr A R B) ch) :=
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
    @g_brabg ph ps ch x y A B (syn_cvv) (syn_cvv) R dv_cache_0001 dv_cache_0002
      dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 hyp_opelopab_3
      hyp_opelopab_4 hyp_brab_5
  have p0001 :=
    @g_mp2an (.classMem A (syn_cvv)) (.classMem B (syn_cvv)) (syn_wb (syn_wbr A R B) ch)
      hyp_opelopab_1 hyp_opelopab_2 p0000
  exact p0001

@[expose]
noncomputable def g_ssopab2 (ph : Wff) (ps : Wff) (x : Var) (y : Var) :
    Nominal.NPrf
      (.imp (.all x (.all y (.imp ph ps))) (syn_wss (syn_copab x y ph) (syn_copab x y ps))) :=
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
  have p0000 := @g_nfa1 (.all y (.imp ph ps)) x
  have p0001 := @g_nfa1 (.imp ph ps) y
  have p0002 := @g_sp (.imp ph ps) y
  have p0003 :=
    @g_anim2d (.all y (.imp ph ps)) ph ps (.classEq (.cv z) (syn_cop (.cv x) (.cv y)))
      p0002
  have p0004 :=
    @g_eximd (.all y (.imp ph ps))
      (syn_wa (.classEq (.cv z) (syn_cop (.cv x) (.cv y))) ph)
      (syn_wa (.classEq (.cv z) (syn_cop (.cv x) (.cv y))) ps) y p0001 p0003
  have p0005 :=
    @g_sps (.all y (.imp ph ps))
      (.imp (syn_wex y (syn_wa (.classEq (.cv z) (syn_cop (.cv x) (.cv y))) ph))
        (syn_wex y (syn_wa (.classEq (.cv z) (syn_cop (.cv x) (.cv y))) ps)))
      x p0004
  have p0006 :=
    @g_eximd (.all x (.all y (.imp ph ps)))
      (syn_wex y (syn_wa (.classEq (.cv z) (syn_cop (.cv x) (.cv y))) ph))
      (syn_wex y (syn_wa (.classEq (.cv z) (syn_cop (.cv x) (.cv y))) ps)) x p0000 p0005
  have p0007 :=
    @g_ss2abdv (.all x (.all y (.imp ph ps)))
      (syn_wex x (syn_wex y (syn_wa (.classEq (.cv z) (syn_cop (.cv x) (.cv y))) ph)))
      (syn_wex x (syn_wex y (syn_wa (.classEq (.cv z) (syn_cop (.cv x) (.cv y))) ps))) z
      dv_cache_0001 p0006
  have p0008 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominal_df_opab ph x y z
      dv_cache_0002 dv_cache_0003 dv_cache_0004
  have p0009 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominal_df_opab ps x y z
      dv_cache_0005 dv_cache_0003 dv_cache_0004
  have p0010 :=
    @g_n_3sstr4g (.all x (.all y (.imp ph ps)))
      (.cab z (syn_wex x (syn_wex y (syn_wa (.classEq (.cv z) (syn_cop (.cv x) (.cv y))) ph))))
      (.cab z (syn_wex x (syn_wex y (syn_wa (.classEq (.cv z) (syn_cop (.cv x) (.cv y))) ps))))
      (syn_copab x y ph) (syn_copab x y ps) p0007 p0008 p0009
  exact p0010

@[expose]
noncomputable def g_ssopab2dv (ph : Wff) (ps : Wff) (ch : Wff) (x : Var) (y : Var)
    (dv_ph_x : x ∉ ph.fv) (dv_ph_y : y ∉ ph.fv)
    (hyp_ssopab2dv_1 : Nominal.NPrf (.imp ph (.imp ps ch))) :
    Nominal.NPrf (.imp ph (syn_wss (syn_copab x y ps) (syn_copab x y ch))) :=
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
    @g_alrimivv ph (.imp ps ch) x y dv_cache_0001 dv_cache_0002 hyp_ssopab2dv_1
  have p0001 := @g_ssopab2 ps ch x y
  have p0002 :=
    @g_syl ph (.all x (.all y (.imp ps ch)))
      (syn_wss (syn_copab x y ps) (syn_copab x y ch)) p0000 p0001
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

@[expose]
noncomputable def g_setconslem1 (x : Var) (A : Class) (B : Class) (dv_A_x : x ∉ A.fv)
    (dv_B_x : x ∉ B.fv) (hyp_setconslem1_1 : Nominal.NPrf (.classMem A (syn_cvv)))
    (hyp_setconslem1_2 : Nominal.NPrf (.classMem B (syn_cvv))) :
    Nominal.NPrf
      (syn_wb (.classMem (syn_copk (syn_csn A) B) (syn_ccomk (syn_cssetk) (syn_csik (syn_ccnvk
                (syn_cimagek (syn_cun (syn_cin (syn_cimagek (syn_cimak (syn_cdif (syn_cins3k
                              (syn_ccompl (syn_cimak (syn_cin (syn_cins3k (syn_cssetk))
                                    (syn_cins2k (syn_cssetk)))
                                  (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cimak
                              (syn_csymdif (syn_cins2k (syn_cins2k (syn_cssetk)))
                                (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk)))
                                  (syn_cins3k (syn_csik (syn_csik (syn_cssetk))))))
                              (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))
                          (syn_cpw1 (syn_cpw1 (syn_c1c))))) (syn_cxpk (syn_cnnc) (syn_cvv)))
                    (syn_cin (syn_cidk) (syn_cxpk (syn_ccompl (syn_cnnc)) (syn_cvv)))))))))
        (syn_wrex x B (.classEq A (syn_cphi (.cv x))))) :=
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
  have dv_cache_0001 : z ∉ ((syn_csn A)).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, fresh_z_not_A,
          not_false_eq_true])
  have dv_cache_0002 : x ∉ ((syn_csn A)).fv :=
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
      ((syn_ccnvk (syn_cimagek (syn_cun (syn_cin (syn_cimagek (syn_cimak (syn_cdif (syn_cins3k
                        (syn_ccompl (syn_cimak
                            (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk)))
                            (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cimak
                        (syn_csymdif (syn_cins2k (syn_cins2k (syn_cssetk)))
                          (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk)))
                            (syn_cins3k (syn_csik (syn_csik (syn_cssetk))))))
                        (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))
                    (syn_cpw1 (syn_cpw1 (syn_c1c))))) (syn_cxpk (syn_cnnc) (syn_cvv)))
              (syn_cin (syn_cidk) (syn_cxpk (syn_ccompl (syn_cnnc)) (syn_cvv))))))).fv :=
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
      ((syn_ccnvk (syn_cimagek (syn_cun (syn_cin (syn_cimagek (syn_cimak (syn_cdif (syn_cins3k
                        (syn_ccompl (syn_cimak
                            (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk)))
                            (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cimak
                        (syn_csymdif (syn_cins2k (syn_cins2k (syn_cssetk)))
                          (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk)))
                            (syn_cins3k (syn_csik (syn_csik (syn_cssetk))))))
                        (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))
                    (syn_cpw1 (syn_cpw1 (syn_c1c))))) (syn_cxpk (syn_cnnc) (syn_cvv)))
              (syn_cin (syn_cidk) (syn_cxpk (syn_ccompl (syn_cnnc)) (syn_cvv))))))).fv :=
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
      ((syn_wa (.classEq (.cv t) (syn_csn (.cv x))) (.classMem (syn_copk A (.cv x)) (syn_ccnvk
              (syn_cimagek (syn_cun (syn_cin (syn_cimagek (syn_cimak (syn_cdif (syn_cins3k
                            (syn_ccompl (syn_cimak (syn_cin (syn_cins3k (syn_cssetk))
                                  (syn_cins2k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c))))))
                          (syn_cimak (syn_csymdif (syn_cins2k (syn_cins2k (syn_cssetk)))
                              (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk)))
                                (syn_cins3k (syn_csik (syn_csik (syn_cssetk))))))
                            (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))
                        (syn_cpw1 (syn_cpw1 (syn_c1c))))) (syn_cxpk (syn_cnnc) (syn_cvv)))
                  (syn_cin (syn_cidk) (syn_cxpk (syn_ccompl (syn_cnnc)) (syn_cvv))))))))).fv :=
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
  have dv_cache_0010 : x ∉ ((Wff.classMem (syn_copk (.cv t) B) (syn_cssetk))).fv :=
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
  have dv_cache_0011 : t ∉ ((syn_csn (.cv x))).fv :=
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
      ((syn_wa (.classMem (syn_copk A (.cv x)) (syn_ccnvk (syn_cimagek (syn_cun (syn_cin
                    (syn_cimagek (syn_cimak (syn_cdif (syn_cins3k (syn_ccompl (syn_cimak
                                (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk)))
                                (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cimak
                            (syn_csymdif (syn_cins2k (syn_cins2k (syn_cssetk)))
                              (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk)))
                                (syn_cins3k (syn_csik (syn_csik (syn_cssetk))))))
                            (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))
                        (syn_cpw1 (syn_cpw1 (syn_c1c))))) (syn_cxpk (syn_cnnc) (syn_cvv)))
                  (syn_cin (syn_cidk) (syn_cxpk (syn_ccompl (syn_cnnc)) (syn_cvv)))))))
          (.classMem (syn_copk (syn_csn (.cv x)) B) (syn_cssetk)))).fv :=
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
  have dv_cache_0013 : t ∉ ((syn_csn A)).fv :=
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
  have dv_cache_0015 : t ∉ ((syn_cssetk)).fv :=
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
      ((syn_csik (syn_ccnvk (syn_cimagek (syn_cun (syn_cin (syn_cimagek (syn_cimak (syn_cdif
                        (syn_cins3k (syn_ccompl (syn_cimak (syn_cin (syn_cins3k (syn_cssetk))
                                (syn_cins2k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c))))))
                        (syn_cimak (syn_csymdif (syn_cins2k (syn_cins2k (syn_cssetk)))
                            (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk)))
                              (syn_cins3k (syn_csik (syn_csik (syn_cssetk))))))
                          (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))
                      (syn_cpw1 (syn_cpw1 (syn_c1c))))) (syn_cxpk (syn_cnnc) (syn_cvv)))
                (syn_cin (syn_cidk) (syn_cxpk (syn_ccompl (syn_cnnc)) (syn_cvv)))))))).fv :=
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
  have p0000 := @g_snex A
  have p0001 := @g_vex t
  have p0002 :=
    @g_opkelsikg z x (syn_csn A) (.cv t)
      (syn_ccnvk (syn_cimagek (syn_cun (syn_cin (syn_cimagek (syn_cimak (syn_cdif (syn_cins3k
                      (syn_ccompl (syn_cimak
                          (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk)))
                          (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cimak
                      (syn_csymdif (syn_cins2k (syn_cins2k (syn_cssetk)))
                        (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk)))
                          (syn_cins3k (syn_csik (syn_csik (syn_cssetk))))))
                      (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))
                  (syn_cpw1 (syn_cpw1 (syn_c1c))))) (syn_cxpk (syn_cnnc) (syn_cvv)))
            (syn_cin (syn_cidk) (syn_cxpk (syn_ccompl (syn_cnnc)) (syn_cvv))))))
      (syn_cvv) (syn_cvv) dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
      dv_cache_0005 dv_cache_0006 dv_cache_0007
  have p0003 :=
    @g_mp2an (.classMem (syn_csn A) (syn_cvv)) (.classMem (.cv t) (syn_cvv))
      (syn_wb (.classMem (syn_copk (syn_csn A) (.cv t)) (syn_csik (syn_ccnvk (syn_cimagek
                (syn_cun (syn_cin (syn_cimagek (syn_cimak (syn_cdif (syn_cins3k (syn_ccompl
                              (syn_cimak (syn_cin (syn_cins3k (syn_cssetk))
                                  (syn_cins2k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c))))))
                          (syn_cimak (syn_csymdif (syn_cins2k (syn_cins2k (syn_cssetk)))
                              (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk)))
                                (syn_cins3k (syn_csik (syn_csik (syn_cssetk))))))
                            (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))
                        (syn_cpw1 (syn_cpw1 (syn_c1c))))) (syn_cxpk (syn_cnnc) (syn_cvv)))
                  (syn_cin (syn_cidk) (syn_cxpk (syn_ccompl (syn_cnnc)) (syn_cvv))))))))
        (syn_wex z (syn_wex x (syn_w3a (.classEq (syn_csn A) (syn_csn (.cv z)))
              (.classEq (.cv t) (syn_csn (.cv x))) (.classMem (syn_copk (.cv z) (.cv x))
                (syn_ccnvk (syn_cimagek (syn_cun (syn_cin (syn_cimagek (syn_cimak (syn_cdif
                              (syn_cins3k (syn_ccompl (syn_cimak
                                    (syn_cin (syn_cins3k (syn_cssetk))
                                      (syn_cins2k (syn_cssetk)))
                                    (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cimak
                                (syn_csymdif (syn_cins2k (syn_cins2k (syn_cssetk)))
                                  (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk)))
                                    (syn_cins3k (syn_csik (syn_csik (syn_cssetk))))))
                                (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))
                            (syn_cpw1 (syn_cpw1 (syn_c1c))))) (syn_cxpk (syn_cnnc) (syn_cvv)))
                      (syn_cin (syn_cidk) (syn_cxpk (syn_ccompl (syn_cnnc)) (syn_cvv)))))))))))
      p0000 p0001 p0002
  have p0004 :=
    @g_excom
      (syn_w3a (.classEq (syn_csn A) (syn_csn (.cv z))) (.classEq (.cv t) (syn_csn (.cv x)))
        (.classMem (syn_copk (.cv z) (.cv x)) (syn_ccnvk (syn_cimagek (syn_cun (syn_cin
                  (syn_cimagek (syn_cimak (syn_cdif (syn_cins3k (syn_ccompl (syn_cimak
                              (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk)))
                              (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cimak
                          (syn_csymdif (syn_cins2k (syn_cins2k (syn_cssetk)))
                            (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk)))
                              (syn_cins3k (syn_csik (syn_csik (syn_cssetk))))))
                          (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))
                      (syn_cpw1 (syn_cpw1 (syn_c1c))))) (syn_cxpk (syn_cnnc) (syn_cvv)))
                (syn_cin (syn_cidk) (syn_cxpk (syn_ccompl (syn_cnnc)) (syn_cvv))))))))
      z x
  have p0005 :=
    @g_n_3anass (.classEq (syn_csn A) (syn_csn (.cv z)))
      (.classEq (.cv t) (syn_csn (.cv x)))
      (.classMem (syn_copk (.cv z) (.cv x)) (syn_ccnvk (syn_cimagek (syn_cun (syn_cin
                (syn_cimagek (syn_cimak (syn_cdif (syn_cins3k (syn_ccompl (syn_cimak
                            (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk)))
                            (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cimak
                        (syn_csymdif (syn_cins2k (syn_cins2k (syn_cssetk)))
                          (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk)))
                            (syn_cins3k (syn_csik (syn_csik (syn_cssetk))))))
                        (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))
                    (syn_cpw1 (syn_cpw1 (syn_c1c))))) (syn_cxpk (syn_cnnc) (syn_cvv)))
              (syn_cin (syn_cidk) (syn_cxpk (syn_ccompl (syn_cnnc)) (syn_cvv)))))))
  have p0006 := @g_eqcom (syn_csn A) (syn_csn (.cv z))
  have p0007 := @g_vex z
  have p0008 := @g_sneqb (.cv z) A p0007
  have p0009 :=
    @g_bitri (.classEq (syn_csn A) (syn_csn (.cv z)))
      (.classEq (syn_csn (.cv z)) (syn_csn A)) (.classEq (.cv z) A) p0006 p0008
  have p0010 :=
    @g_anbi1i (.classEq (syn_csn A) (syn_csn (.cv z))) (.classEq (.cv z) A)
      (syn_wa (.classEq (.cv t) (syn_csn (.cv x))) (.classMem (syn_copk (.cv z) (.cv x))
          (syn_ccnvk (syn_cimagek (syn_cun (syn_cin (syn_cimagek (syn_cimak (syn_cdif
                        (syn_cins3k (syn_ccompl (syn_cimak (syn_cin (syn_cins3k (syn_cssetk))
                                (syn_cins2k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c))))))
                        (syn_cimak (syn_csymdif (syn_cins2k (syn_cins2k (syn_cssetk)))
                            (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk)))
                              (syn_cins3k (syn_csik (syn_csik (syn_cssetk))))))
                          (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))
                      (syn_cpw1 (syn_cpw1 (syn_c1c))))) (syn_cxpk (syn_cnnc) (syn_cvv)))
                (syn_cin (syn_cidk) (syn_cxpk (syn_ccompl (syn_cnnc)) (syn_cvv))))))))
      p0009
  have p0011 :=
    @g_bitri
      (syn_w3a (.classEq (syn_csn A) (syn_csn (.cv z))) (.classEq (.cv t) (syn_csn (.cv x)))
        (.classMem (syn_copk (.cv z) (.cv x)) (syn_ccnvk (syn_cimagek (syn_cun (syn_cin
                  (syn_cimagek (syn_cimak (syn_cdif (syn_cins3k (syn_ccompl (syn_cimak
                              (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk)))
                              (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cimak
                          (syn_csymdif (syn_cins2k (syn_cins2k (syn_cssetk)))
                            (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk)))
                              (syn_cins3k (syn_csik (syn_csik (syn_cssetk))))))
                          (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))
                      (syn_cpw1 (syn_cpw1 (syn_c1c))))) (syn_cxpk (syn_cnnc) (syn_cvv)))
                (syn_cin (syn_cidk) (syn_cxpk (syn_ccompl (syn_cnnc)) (syn_cvv))))))))
      (syn_wa (.classEq (syn_csn A) (syn_csn (.cv z)))
        (syn_wa (.classEq (.cv t) (syn_csn (.cv x))) (.classMem (syn_copk (.cv z) (.cv x))
            (syn_ccnvk (syn_cimagek (syn_cun (syn_cin (syn_cimagek (syn_cimak (syn_cdif
                          (syn_cins3k (syn_ccompl (syn_cimak (syn_cin (syn_cins3k (syn_cssetk))
                                  (syn_cins2k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c))))))
                          (syn_cimak (syn_csymdif (syn_cins2k (syn_cins2k (syn_cssetk)))
                              (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk)))
                                (syn_cins3k (syn_csik (syn_csik (syn_cssetk))))))
                            (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))
                        (syn_cpw1 (syn_cpw1 (syn_c1c))))) (syn_cxpk (syn_cnnc) (syn_cvv)))
                  (syn_cin (syn_cidk) (syn_cxpk (syn_ccompl (syn_cnnc)) (syn_cvv)))))))))
      (syn_wa (.classEq (.cv z) A) (syn_wa (.classEq (.cv t) (syn_csn (.cv x)))
          (.classMem (syn_copk (.cv z) (.cv x)) (syn_ccnvk (syn_cimagek (syn_cun (syn_cin
                    (syn_cimagek (syn_cimak (syn_cdif (syn_cins3k (syn_ccompl (syn_cimak
                                (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk)))
                                (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cimak
                            (syn_csymdif (syn_cins2k (syn_cins2k (syn_cssetk)))
                              (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk)))
                                (syn_cins3k (syn_csik (syn_csik (syn_cssetk))))))
                            (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))
                        (syn_cpw1 (syn_cpw1 (syn_c1c))))) (syn_cxpk (syn_cnnc) (syn_cvv)))
                  (syn_cin (syn_cidk) (syn_cxpk (syn_ccompl (syn_cnnc)) (syn_cvv)))))))))
      p0005 p0010
  have p0012 :=
    @g_exbii
      (syn_w3a (.classEq (syn_csn A) (syn_csn (.cv z))) (.classEq (.cv t) (syn_csn (.cv x)))
        (.classMem (syn_copk (.cv z) (.cv x)) (syn_ccnvk (syn_cimagek (syn_cun (syn_cin
                  (syn_cimagek (syn_cimak (syn_cdif (syn_cins3k (syn_ccompl (syn_cimak
                              (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk)))
                              (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cimak
                          (syn_csymdif (syn_cins2k (syn_cins2k (syn_cssetk)))
                            (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk)))
                              (syn_cins3k (syn_csik (syn_csik (syn_cssetk))))))
                          (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))
                      (syn_cpw1 (syn_cpw1 (syn_c1c))))) (syn_cxpk (syn_cnnc) (syn_cvv)))
                (syn_cin (syn_cidk) (syn_cxpk (syn_ccompl (syn_cnnc)) (syn_cvv))))))))
      (syn_wa (.classEq (.cv z) A) (syn_wa (.classEq (.cv t) (syn_csn (.cv x)))
          (.classMem (syn_copk (.cv z) (.cv x)) (syn_ccnvk (syn_cimagek (syn_cun (syn_cin
                    (syn_cimagek (syn_cimak (syn_cdif (syn_cins3k (syn_ccompl (syn_cimak
                                (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk)))
                                (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cimak
                            (syn_csymdif (syn_cins2k (syn_cins2k (syn_cssetk)))
                              (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk)))
                                (syn_cins3k (syn_csik (syn_csik (syn_cssetk))))))
                            (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))
                        (syn_cpw1 (syn_cpw1 (syn_c1c))))) (syn_cxpk (syn_cnnc) (syn_cvv)))
                  (syn_cin (syn_cidk) (syn_cxpk (syn_ccompl (syn_cnnc)) (syn_cvv)))))))))
      z p0011
  have p0013 := @g_opkeq1 (.cv z) A (.cv x)
  have p0014 :=
    @g_eleq1d (.classEq (.cv z) A) (syn_copk (.cv z) (.cv x)) (syn_copk A (.cv x))
      (syn_ccnvk (syn_cimagek (syn_cun (syn_cin (syn_cimagek (syn_cimak (syn_cdif (syn_cins3k
                      (syn_ccompl (syn_cimak
                          (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk)))
                          (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cimak
                      (syn_csymdif (syn_cins2k (syn_cins2k (syn_cssetk)))
                        (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk)))
                          (syn_cins3k (syn_csik (syn_csik (syn_cssetk))))))
                      (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))
                  (syn_cpw1 (syn_cpw1 (syn_c1c))))) (syn_cxpk (syn_cnnc) (syn_cvv)))
            (syn_cin (syn_cidk) (syn_cxpk (syn_ccompl (syn_cnnc)) (syn_cvv))))))
      p0013
  have p0015 :=
    @g_anbi2d (.classEq (.cv z) A)
      (.classMem (syn_copk (.cv z) (.cv x)) (syn_ccnvk (syn_cimagek (syn_cun (syn_cin
                (syn_cimagek (syn_cimak (syn_cdif (syn_cins3k (syn_ccompl (syn_cimak
                            (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk)))
                            (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cimak
                        (syn_csymdif (syn_cins2k (syn_cins2k (syn_cssetk)))
                          (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk)))
                            (syn_cins3k (syn_csik (syn_csik (syn_cssetk))))))
                        (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))
                    (syn_cpw1 (syn_cpw1 (syn_c1c))))) (syn_cxpk (syn_cnnc) (syn_cvv)))
              (syn_cin (syn_cidk) (syn_cxpk (syn_ccompl (syn_cnnc)) (syn_cvv)))))))
      (.classMem (syn_copk A (.cv x)) (syn_ccnvk (syn_cimagek (syn_cun (syn_cin (syn_cimagek
                  (syn_cimak (syn_cdif (syn_cins3k (syn_ccompl (syn_cimak
                            (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk)))
                            (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cimak
                        (syn_csymdif (syn_cins2k (syn_cins2k (syn_cssetk)))
                          (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk)))
                            (syn_cins3k (syn_csik (syn_csik (syn_cssetk))))))
                        (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))
                    (syn_cpw1 (syn_cpw1 (syn_c1c))))) (syn_cxpk (syn_cnnc) (syn_cvv)))
              (syn_cin (syn_cidk) (syn_cxpk (syn_ccompl (syn_cnnc)) (syn_cvv)))))))
      (.classEq (.cv t) (syn_csn (.cv x))) p0014
  have p0016 :=
    @g_ceqsexv
      (syn_wa (.classEq (.cv t) (syn_csn (.cv x))) (.classMem (syn_copk (.cv z) (.cv x))
          (syn_ccnvk (syn_cimagek (syn_cun (syn_cin (syn_cimagek (syn_cimak (syn_cdif
                        (syn_cins3k (syn_ccompl (syn_cimak (syn_cin (syn_cins3k (syn_cssetk))
                                (syn_cins2k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c))))))
                        (syn_cimak (syn_csymdif (syn_cins2k (syn_cins2k (syn_cssetk)))
                            (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk)))
                              (syn_cins3k (syn_csik (syn_csik (syn_cssetk))))))
                          (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))
                      (syn_cpw1 (syn_cpw1 (syn_c1c))))) (syn_cxpk (syn_cnnc) (syn_cvv)))
                (syn_cin (syn_cidk) (syn_cxpk (syn_ccompl (syn_cnnc)) (syn_cvv))))))))
      (syn_wa (.classEq (.cv t) (syn_csn (.cv x))) (.classMem (syn_copk A (.cv x)) (syn_ccnvk
            (syn_cimagek (syn_cun (syn_cin (syn_cimagek (syn_cimak (syn_cdif (syn_cins3k
                          (syn_ccompl (syn_cimak (syn_cin (syn_cins3k (syn_cssetk))
                                (syn_cins2k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c))))))
                        (syn_cimak (syn_csymdif (syn_cins2k (syn_cins2k (syn_cssetk)))
                            (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk)))
                              (syn_cins3k (syn_csik (syn_csik (syn_cssetk))))))
                          (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))
                      (syn_cpw1 (syn_cpw1 (syn_c1c))))) (syn_cxpk (syn_cnnc) (syn_cvv)))
                (syn_cin (syn_cidk) (syn_cxpk (syn_ccompl (syn_cnnc)) (syn_cvv))))))))
      z A dv_cache_0008 dv_cache_0009 hyp_setconslem1_1 p0015
  have p0017 :=
    @g_bitri
      (syn_wex z (syn_w3a (.classEq (syn_csn A) (syn_csn (.cv z)))
          (.classEq (.cv t) (syn_csn (.cv x))) (.classMem (syn_copk (.cv z) (.cv x)) (syn_ccnvk
              (syn_cimagek (syn_cun (syn_cin (syn_cimagek (syn_cimak (syn_cdif (syn_cins3k
                            (syn_ccompl (syn_cimak (syn_cin (syn_cins3k (syn_cssetk))
                                  (syn_cins2k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c))))))
                          (syn_cimak (syn_csymdif (syn_cins2k (syn_cins2k (syn_cssetk)))
                              (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk)))
                                (syn_cins3k (syn_csik (syn_csik (syn_cssetk))))))
                            (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))
                        (syn_cpw1 (syn_cpw1 (syn_c1c))))) (syn_cxpk (syn_cnnc) (syn_cvv)))
                  (syn_cin (syn_cidk) (syn_cxpk (syn_ccompl (syn_cnnc)) (syn_cvv)))))))))
      (syn_wex z (syn_wa (.classEq (.cv z) A) (syn_wa (.classEq (.cv t) (syn_csn (.cv x)))
            (.classMem (syn_copk (.cv z) (.cv x)) (syn_ccnvk (syn_cimagek (syn_cun (syn_cin
                      (syn_cimagek (syn_cimak (syn_cdif (syn_cins3k (syn_ccompl (syn_cimak
                                  (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk)))
                                  (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cimak
                              (syn_csymdif (syn_cins2k (syn_cins2k (syn_cssetk)))
                                (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk)))
                                  (syn_cins3k (syn_csik (syn_csik (syn_cssetk))))))
                              (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))
                          (syn_cpw1 (syn_cpw1 (syn_c1c))))) (syn_cxpk (syn_cnnc) (syn_cvv)))
                    (syn_cin (syn_cidk) (syn_cxpk (syn_ccompl (syn_cnnc)) (syn_cvv))))))))))
      (syn_wa (.classEq (.cv t) (syn_csn (.cv x))) (.classMem (syn_copk A (.cv x)) (syn_ccnvk
            (syn_cimagek (syn_cun (syn_cin (syn_cimagek (syn_cimak (syn_cdif (syn_cins3k
                          (syn_ccompl (syn_cimak (syn_cin (syn_cins3k (syn_cssetk))
                                (syn_cins2k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c))))))
                        (syn_cimak (syn_csymdif (syn_cins2k (syn_cins2k (syn_cssetk)))
                            (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk)))
                              (syn_cins3k (syn_csik (syn_csik (syn_cssetk))))))
                          (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))
                      (syn_cpw1 (syn_cpw1 (syn_c1c))))) (syn_cxpk (syn_cnnc) (syn_cvv)))
                (syn_cin (syn_cidk) (syn_cxpk (syn_ccompl (syn_cnnc)) (syn_cvv))))))))
      p0012 p0016
  have p0018 :=
    @g_exbii
      (syn_wex z (syn_w3a (.classEq (syn_csn A) (syn_csn (.cv z)))
          (.classEq (.cv t) (syn_csn (.cv x))) (.classMem (syn_copk (.cv z) (.cv x)) (syn_ccnvk
              (syn_cimagek (syn_cun (syn_cin (syn_cimagek (syn_cimak (syn_cdif (syn_cins3k
                            (syn_ccompl (syn_cimak (syn_cin (syn_cins3k (syn_cssetk))
                                  (syn_cins2k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c))))))
                          (syn_cimak (syn_csymdif (syn_cins2k (syn_cins2k (syn_cssetk)))
                              (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk)))
                                (syn_cins3k (syn_csik (syn_csik (syn_cssetk))))))
                            (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))
                        (syn_cpw1 (syn_cpw1 (syn_c1c))))) (syn_cxpk (syn_cnnc) (syn_cvv)))
                  (syn_cin (syn_cidk) (syn_cxpk (syn_ccompl (syn_cnnc)) (syn_cvv)))))))))
      (syn_wa (.classEq (.cv t) (syn_csn (.cv x))) (.classMem (syn_copk A (.cv x)) (syn_ccnvk
            (syn_cimagek (syn_cun (syn_cin (syn_cimagek (syn_cimak (syn_cdif (syn_cins3k
                          (syn_ccompl (syn_cimak (syn_cin (syn_cins3k (syn_cssetk))
                                (syn_cins2k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c))))))
                        (syn_cimak (syn_csymdif (syn_cins2k (syn_cins2k (syn_cssetk)))
                            (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk)))
                              (syn_cins3k (syn_csik (syn_csik (syn_cssetk))))))
                          (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))
                      (syn_cpw1 (syn_cpw1 (syn_c1c))))) (syn_cxpk (syn_cnnc) (syn_cvv)))
                (syn_cin (syn_cidk) (syn_cxpk (syn_ccompl (syn_cnnc)) (syn_cvv))))))))
      x p0017
  have p0019 :=
    @g_n_3bitri
      (.classMem (syn_copk (syn_csn A) (.cv t)) (syn_csik (syn_ccnvk (syn_cimagek (syn_cun
                (syn_cin (syn_cimagek (syn_cimak (syn_cdif (syn_cins3k (syn_ccompl (syn_cimak
                              (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk)))
                              (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cimak
                          (syn_csymdif (syn_cins2k (syn_cins2k (syn_cssetk)))
                            (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk)))
                              (syn_cins3k (syn_csik (syn_csik (syn_cssetk))))))
                          (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))
                      (syn_cpw1 (syn_cpw1 (syn_c1c))))) (syn_cxpk (syn_cnnc) (syn_cvv)))
                (syn_cin (syn_cidk) (syn_cxpk (syn_ccompl (syn_cnnc)) (syn_cvv))))))))
      (syn_wex z (syn_wex x (syn_w3a (.classEq (syn_csn A) (syn_csn (.cv z)))
            (.classEq (.cv t) (syn_csn (.cv x))) (.classMem (syn_copk (.cv z) (.cv x))
              (syn_ccnvk (syn_cimagek (syn_cun (syn_cin (syn_cimagek (syn_cimak (syn_cdif
                            (syn_cins3k (syn_ccompl (syn_cimak
                                  (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk)))
                                  (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cimak
                              (syn_csymdif (syn_cins2k (syn_cins2k (syn_cssetk)))
                                (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk)))
                                  (syn_cins3k (syn_csik (syn_csik (syn_cssetk))))))
                              (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))
                          (syn_cpw1 (syn_cpw1 (syn_c1c))))) (syn_cxpk (syn_cnnc) (syn_cvv)))
                    (syn_cin (syn_cidk) (syn_cxpk (syn_ccompl (syn_cnnc)) (syn_cvv))))))))))
      (syn_wex x (syn_wex z (syn_w3a (.classEq (syn_csn A) (syn_csn (.cv z)))
            (.classEq (.cv t) (syn_csn (.cv x))) (.classMem (syn_copk (.cv z) (.cv x))
              (syn_ccnvk (syn_cimagek (syn_cun (syn_cin (syn_cimagek (syn_cimak (syn_cdif
                            (syn_cins3k (syn_ccompl (syn_cimak
                                  (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk)))
                                  (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cimak
                              (syn_csymdif (syn_cins2k (syn_cins2k (syn_cssetk)))
                                (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk)))
                                  (syn_cins3k (syn_csik (syn_csik (syn_cssetk))))))
                              (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))
                          (syn_cpw1 (syn_cpw1 (syn_c1c))))) (syn_cxpk (syn_cnnc) (syn_cvv)))
                    (syn_cin (syn_cidk) (syn_cxpk (syn_ccompl (syn_cnnc)) (syn_cvv))))))))))
      (syn_wex x (syn_wa (.classEq (.cv t) (syn_csn (.cv x))) (.classMem (syn_copk A (.cv x))
            (syn_ccnvk (syn_cimagek (syn_cun (syn_cin (syn_cimagek (syn_cimak (syn_cdif
                          (syn_cins3k (syn_ccompl (syn_cimak (syn_cin (syn_cins3k (syn_cssetk))
                                  (syn_cins2k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c))))))
                          (syn_cimak (syn_csymdif (syn_cins2k (syn_cins2k (syn_cssetk)))
                              (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk)))
                                (syn_cins3k (syn_csik (syn_csik (syn_cssetk))))))
                            (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))
                        (syn_cpw1 (syn_cpw1 (syn_c1c))))) (syn_cxpk (syn_cnnc) (syn_cvv)))
                  (syn_cin (syn_cidk) (syn_cxpk (syn_ccompl (syn_cnnc)) (syn_cvv)))))))))
      p0003 p0004 p0018
  have p0020 :=
    @g_anbi1i
      (.classMem (syn_copk (syn_csn A) (.cv t)) (syn_csik (syn_ccnvk (syn_cimagek (syn_cun
                (syn_cin (syn_cimagek (syn_cimak (syn_cdif (syn_cins3k (syn_ccompl (syn_cimak
                              (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk)))
                              (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cimak
                          (syn_csymdif (syn_cins2k (syn_cins2k (syn_cssetk)))
                            (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk)))
                              (syn_cins3k (syn_csik (syn_csik (syn_cssetk))))))
                          (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))
                      (syn_cpw1 (syn_cpw1 (syn_c1c))))) (syn_cxpk (syn_cnnc) (syn_cvv)))
                (syn_cin (syn_cidk) (syn_cxpk (syn_ccompl (syn_cnnc)) (syn_cvv))))))))
      (syn_wex x (syn_wa (.classEq (.cv t) (syn_csn (.cv x))) (.classMem (syn_copk A (.cv x))
            (syn_ccnvk (syn_cimagek (syn_cun (syn_cin (syn_cimagek (syn_cimak (syn_cdif
                          (syn_cins3k (syn_ccompl (syn_cimak (syn_cin (syn_cins3k (syn_cssetk))
                                  (syn_cins2k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c))))))
                          (syn_cimak (syn_csymdif (syn_cins2k (syn_cins2k (syn_cssetk)))
                              (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk)))
                                (syn_cins3k (syn_csik (syn_csik (syn_cssetk))))))
                            (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))
                        (syn_cpw1 (syn_cpw1 (syn_c1c))))) (syn_cxpk (syn_cnnc) (syn_cvv)))
                  (syn_cin (syn_cidk) (syn_cxpk (syn_ccompl (syn_cnnc)) (syn_cvv)))))))))
      (.classMem (syn_copk (.cv t) B) (syn_cssetk)) p0019
  have p0021 :=
    @g_n_19_41v
      (syn_wa (.classEq (.cv t) (syn_csn (.cv x))) (.classMem (syn_copk A (.cv x)) (syn_ccnvk
            (syn_cimagek (syn_cun (syn_cin (syn_cimagek (syn_cimak (syn_cdif (syn_cins3k
                          (syn_ccompl (syn_cimak (syn_cin (syn_cins3k (syn_cssetk))
                                (syn_cins2k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c))))))
                        (syn_cimak (syn_csymdif (syn_cins2k (syn_cins2k (syn_cssetk)))
                            (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk)))
                              (syn_cins3k (syn_csik (syn_csik (syn_cssetk))))))
                          (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))
                      (syn_cpw1 (syn_cpw1 (syn_c1c))))) (syn_cxpk (syn_cnnc) (syn_cvv)))
                (syn_cin (syn_cidk) (syn_cxpk (syn_ccompl (syn_cnnc)) (syn_cvv))))))))
      (.classMem (syn_copk (.cv t) B) (syn_cssetk)) x dv_cache_0010
  have p0022 :=
    @g_anass (.classEq (.cv t) (syn_csn (.cv x)))
      (.classMem (syn_copk A (.cv x)) (syn_ccnvk (syn_cimagek (syn_cun (syn_cin (syn_cimagek
                  (syn_cimak (syn_cdif (syn_cins3k (syn_ccompl (syn_cimak
                            (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk)))
                            (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cimak
                        (syn_csymdif (syn_cins2k (syn_cins2k (syn_cssetk)))
                          (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk)))
                            (syn_cins3k (syn_csik (syn_csik (syn_cssetk))))))
                        (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))
                    (syn_cpw1 (syn_cpw1 (syn_c1c))))) (syn_cxpk (syn_cnnc) (syn_cvv)))
              (syn_cin (syn_cidk) (syn_cxpk (syn_ccompl (syn_cnnc)) (syn_cvv)))))))
      (.classMem (syn_copk (.cv t) B) (syn_cssetk))
  have p0023 :=
    @g_exbii
      (syn_wa (syn_wa (.classEq (.cv t) (syn_csn (.cv x))) (.classMem (syn_copk A (.cv x))
            (syn_ccnvk (syn_cimagek (syn_cun (syn_cin (syn_cimagek (syn_cimak (syn_cdif
                          (syn_cins3k (syn_ccompl (syn_cimak (syn_cin (syn_cins3k (syn_cssetk))
                                  (syn_cins2k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c))))))
                          (syn_cimak (syn_csymdif (syn_cins2k (syn_cins2k (syn_cssetk)))
                              (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk)))
                                (syn_cins3k (syn_csik (syn_csik (syn_cssetk))))))
                            (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))
                        (syn_cpw1 (syn_cpw1 (syn_c1c))))) (syn_cxpk (syn_cnnc) (syn_cvv)))
                  (syn_cin (syn_cidk) (syn_cxpk (syn_ccompl (syn_cnnc)) (syn_cvv))))))))
        (.classMem (syn_copk (.cv t) B) (syn_cssetk)))
      (syn_wa (.classEq (.cv t) (syn_csn (.cv x))) (syn_wa (.classMem (syn_copk A (.cv x))
            (syn_ccnvk (syn_cimagek (syn_cun (syn_cin (syn_cimagek (syn_cimak (syn_cdif
                          (syn_cins3k (syn_ccompl (syn_cimak (syn_cin (syn_cins3k (syn_cssetk))
                                  (syn_cins2k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c))))))
                          (syn_cimak (syn_csymdif (syn_cins2k (syn_cins2k (syn_cssetk)))
                              (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk)))
                                (syn_cins3k (syn_csik (syn_csik (syn_cssetk))))))
                            (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))
                        (syn_cpw1 (syn_cpw1 (syn_c1c))))) (syn_cxpk (syn_cnnc) (syn_cvv)))
                  (syn_cin (syn_cidk) (syn_cxpk (syn_ccompl (syn_cnnc)) (syn_cvv)))))))
          (.classMem (syn_copk (.cv t) B) (syn_cssetk))))
      x p0022
  have p0024 :=
    @g_n_3bitr2i
      (syn_wa (.classMem (syn_copk (syn_csn A) (.cv t)) (syn_csik (syn_ccnvk (syn_cimagek
                (syn_cun (syn_cin (syn_cimagek (syn_cimak (syn_cdif (syn_cins3k (syn_ccompl
                              (syn_cimak (syn_cin (syn_cins3k (syn_cssetk))
                                  (syn_cins2k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c))))))
                          (syn_cimak (syn_csymdif (syn_cins2k (syn_cins2k (syn_cssetk)))
                              (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk)))
                                (syn_cins3k (syn_csik (syn_csik (syn_cssetk))))))
                            (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))
                        (syn_cpw1 (syn_cpw1 (syn_c1c))))) (syn_cxpk (syn_cnnc) (syn_cvv)))
                  (syn_cin (syn_cidk) (syn_cxpk (syn_ccompl (syn_cnnc)) (syn_cvv))))))))
        (.classMem (syn_copk (.cv t) B) (syn_cssetk)))
      (syn_wa (syn_wex x (syn_wa (.classEq (.cv t) (syn_csn (.cv x)))
            (.classMem (syn_copk A (.cv x)) (syn_ccnvk (syn_cimagek (syn_cun (syn_cin
                      (syn_cimagek (syn_cimak (syn_cdif (syn_cins3k (syn_ccompl (syn_cimak
                                  (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk)))
                                  (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cimak
                              (syn_csymdif (syn_cins2k (syn_cins2k (syn_cssetk)))
                                (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk)))
                                  (syn_cins3k (syn_csik (syn_csik (syn_cssetk))))))
                              (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))
                          (syn_cpw1 (syn_cpw1 (syn_c1c))))) (syn_cxpk (syn_cnnc) (syn_cvv)))
                    (syn_cin (syn_cidk) (syn_cxpk (syn_ccompl (syn_cnnc)) (syn_cvv)))))))))
        (.classMem (syn_copk (.cv t) B) (syn_cssetk)))
      (syn_wex x (syn_wa (syn_wa (.classEq (.cv t) (syn_csn (.cv x)))
            (.classMem (syn_copk A (.cv x)) (syn_ccnvk (syn_cimagek (syn_cun (syn_cin
                      (syn_cimagek (syn_cimak (syn_cdif (syn_cins3k (syn_ccompl (syn_cimak
                                  (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk)))
                                  (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cimak
                              (syn_csymdif (syn_cins2k (syn_cins2k (syn_cssetk)))
                                (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk)))
                                  (syn_cins3k (syn_csik (syn_csik (syn_cssetk))))))
                              (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))
                          (syn_cpw1 (syn_cpw1 (syn_c1c))))) (syn_cxpk (syn_cnnc) (syn_cvv)))
                    (syn_cin (syn_cidk) (syn_cxpk (syn_ccompl (syn_cnnc)) (syn_cvv))))))))
          (.classMem (syn_copk (.cv t) B) (syn_cssetk))))
      (syn_wex x (syn_wa (.classEq (.cv t) (syn_csn (.cv x))) (syn_wa
            (.classMem (syn_copk A (.cv x)) (syn_ccnvk (syn_cimagek (syn_cun (syn_cin
                      (syn_cimagek (syn_cimak (syn_cdif (syn_cins3k (syn_ccompl (syn_cimak
                                  (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk)))
                                  (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cimak
                              (syn_csymdif (syn_cins2k (syn_cins2k (syn_cssetk)))
                                (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk)))
                                  (syn_cins3k (syn_csik (syn_csik (syn_cssetk))))))
                              (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))
                          (syn_cpw1 (syn_cpw1 (syn_c1c))))) (syn_cxpk (syn_cnnc) (syn_cvv)))
                    (syn_cin (syn_cidk) (syn_cxpk (syn_ccompl (syn_cnnc)) (syn_cvv)))))))
            (.classMem (syn_copk (.cv t) B) (syn_cssetk)))))
      p0020 p0021 p0023
  have p0025 :=
    @g_exbii
      (syn_wa (.classMem (syn_copk (syn_csn A) (.cv t)) (syn_csik (syn_ccnvk (syn_cimagek
                (syn_cun (syn_cin (syn_cimagek (syn_cimak (syn_cdif (syn_cins3k (syn_ccompl
                              (syn_cimak (syn_cin (syn_cins3k (syn_cssetk))
                                  (syn_cins2k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c))))))
                          (syn_cimak (syn_csymdif (syn_cins2k (syn_cins2k (syn_cssetk)))
                              (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk)))
                                (syn_cins3k (syn_csik (syn_csik (syn_cssetk))))))
                            (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))
                        (syn_cpw1 (syn_cpw1 (syn_c1c))))) (syn_cxpk (syn_cnnc) (syn_cvv)))
                  (syn_cin (syn_cidk) (syn_cxpk (syn_ccompl (syn_cnnc)) (syn_cvv))))))))
        (.classMem (syn_copk (.cv t) B) (syn_cssetk)))
      (syn_wex x (syn_wa (.classEq (.cv t) (syn_csn (.cv x))) (syn_wa
            (.classMem (syn_copk A (.cv x)) (syn_ccnvk (syn_cimagek (syn_cun (syn_cin
                      (syn_cimagek (syn_cimak (syn_cdif (syn_cins3k (syn_ccompl (syn_cimak
                                  (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk)))
                                  (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cimak
                              (syn_csymdif (syn_cins2k (syn_cins2k (syn_cssetk)))
                                (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk)))
                                  (syn_cins3k (syn_csik (syn_csik (syn_cssetk))))))
                              (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))
                          (syn_cpw1 (syn_cpw1 (syn_c1c))))) (syn_cxpk (syn_cnnc) (syn_cvv)))
                    (syn_cin (syn_cidk) (syn_cxpk (syn_ccompl (syn_cnnc)) (syn_cvv)))))))
            (.classMem (syn_copk (.cv t) B) (syn_cssetk)))))
      t p0024
  have p0026 :=
    @g_excom
      (syn_wa (.classEq (.cv t) (syn_csn (.cv x))) (syn_wa (.classMem (syn_copk A (.cv x))
            (syn_ccnvk (syn_cimagek (syn_cun (syn_cin (syn_cimagek (syn_cimak (syn_cdif
                          (syn_cins3k (syn_ccompl (syn_cimak (syn_cin (syn_cins3k (syn_cssetk))
                                  (syn_cins2k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c))))))
                          (syn_cimak (syn_csymdif (syn_cins2k (syn_cins2k (syn_cssetk)))
                              (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk)))
                                (syn_cins3k (syn_csik (syn_csik (syn_cssetk))))))
                            (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))
                        (syn_cpw1 (syn_cpw1 (syn_c1c))))) (syn_cxpk (syn_cnnc) (syn_cvv)))
                  (syn_cin (syn_cidk) (syn_cxpk (syn_ccompl (syn_cnnc)) (syn_cvv)))))))
          (.classMem (syn_copk (.cv t) B) (syn_cssetk))))
      x t
  have p0027 := @g_snex (.cv x)
  have p0028 := @g_opkeq1 (.cv t) (syn_csn (.cv x)) B
  have p0029 :=
    @g_eleq1d (.classEq (.cv t) (syn_csn (.cv x))) (syn_copk (.cv t) B)
      (syn_copk (syn_csn (.cv x)) B) (syn_cssetk) p0028
  have p0030 :=
    @g_anbi2d (.classEq (.cv t) (syn_csn (.cv x)))
      (.classMem (syn_copk (.cv t) B) (syn_cssetk))
      (.classMem (syn_copk (syn_csn (.cv x)) B) (syn_cssetk))
      (.classMem (syn_copk A (.cv x)) (syn_ccnvk (syn_cimagek (syn_cun (syn_cin (syn_cimagek
                  (syn_cimak (syn_cdif (syn_cins3k (syn_ccompl (syn_cimak
                            (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk)))
                            (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cimak
                        (syn_csymdif (syn_cins2k (syn_cins2k (syn_cssetk)))
                          (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk)))
                            (syn_cins3k (syn_csik (syn_csik (syn_cssetk))))))
                        (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))
                    (syn_cpw1 (syn_cpw1 (syn_c1c))))) (syn_cxpk (syn_cnnc) (syn_cvv)))
              (syn_cin (syn_cidk) (syn_cxpk (syn_ccompl (syn_cnnc)) (syn_cvv)))))))
      p0029
  have p0031 :=
    @g_ceqsexv
      (syn_wa (.classMem (syn_copk A (.cv x)) (syn_ccnvk (syn_cimagek (syn_cun (syn_cin
                  (syn_cimagek (syn_cimak (syn_cdif (syn_cins3k (syn_ccompl (syn_cimak
                              (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk)))
                              (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cimak
                          (syn_csymdif (syn_cins2k (syn_cins2k (syn_cssetk)))
                            (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk)))
                              (syn_cins3k (syn_csik (syn_csik (syn_cssetk))))))
                          (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))
                      (syn_cpw1 (syn_cpw1 (syn_c1c))))) (syn_cxpk (syn_cnnc) (syn_cvv)))
                (syn_cin (syn_cidk) (syn_cxpk (syn_ccompl (syn_cnnc)) (syn_cvv)))))))
        (.classMem (syn_copk (.cv t) B) (syn_cssetk)))
      (syn_wa (.classMem (syn_copk A (.cv x)) (syn_ccnvk (syn_cimagek (syn_cun (syn_cin
                  (syn_cimagek (syn_cimak (syn_cdif (syn_cins3k (syn_ccompl (syn_cimak
                              (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk)))
                              (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cimak
                          (syn_csymdif (syn_cins2k (syn_cins2k (syn_cssetk)))
                            (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk)))
                              (syn_cins3k (syn_csik (syn_csik (syn_cssetk))))))
                          (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))
                      (syn_cpw1 (syn_cpw1 (syn_c1c))))) (syn_cxpk (syn_cnnc) (syn_cvv)))
                (syn_cin (syn_cidk) (syn_cxpk (syn_ccompl (syn_cnnc)) (syn_cvv)))))))
        (.classMem (syn_copk (syn_csn (.cv x)) B) (syn_cssetk)))
      t (syn_csn (.cv x)) dv_cache_0011 dv_cache_0012 p0027 p0030
  have p0032 := @g_vex x
  have p0033 :=
    @g_opkelimagek (.cv x) A
      (syn_cun (syn_cin (syn_cimagek (syn_cimak (syn_cdif (syn_cins3k (syn_ccompl (syn_cimak
                      (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk)))
                      (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cimak
                  (syn_csymdif (syn_cins2k (syn_cins2k (syn_cssetk)))
                    (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk)))
                      (syn_cins3k (syn_csik (syn_csik (syn_cssetk))))))
                  (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))
              (syn_cpw1 (syn_cpw1 (syn_c1c))))) (syn_cxpk (syn_cnnc) (syn_cvv)))
        (syn_cin (syn_cidk) (syn_cxpk (syn_ccompl (syn_cnnc)) (syn_cvv))))
      p0032 hyp_setconslem1_1
  have p0034 :=
    @g_opkelcnvk A (.cv x)
      (syn_cimagek (syn_cun (syn_cin (syn_cimagek (syn_cimak (syn_cdif (syn_cins3k (syn_ccompl
                      (syn_cimak (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk)))
                        (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cimak
                    (syn_csymdif (syn_cins2k (syn_cins2k (syn_cssetk)))
                      (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk)))
                        (syn_cins3k (syn_csik (syn_csik (syn_cssetk))))))
                    (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))
                (syn_cpw1 (syn_cpw1 (syn_c1c))))) (syn_cxpk (syn_cnnc) (syn_cvv)))
          (syn_cin (syn_cidk) (syn_cxpk (syn_ccompl (syn_cnnc)) (syn_cvv)))))
      hyp_setconslem1_1 p0032
  have p0035 := @g_dfphi2 (.cv x)
  have p0036 :=
    @g_eqeq2i (syn_cphi (.cv x))
      (syn_cimak (syn_cun (syn_cin (syn_cimagek (syn_cimak (syn_cdif (syn_cins3k (syn_ccompl
                      (syn_cimak (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk)))
                        (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cimak
                    (syn_csymdif (syn_cins2k (syn_cins2k (syn_cssetk)))
                      (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk)))
                        (syn_cins3k (syn_csik (syn_csik (syn_cssetk))))))
                    (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))
                (syn_cpw1 (syn_cpw1 (syn_c1c))))) (syn_cxpk (syn_cnnc) (syn_cvv)))
          (syn_cin (syn_cidk) (syn_cxpk (syn_ccompl (syn_cnnc)) (syn_cvv)))) (.cv x))
      A p0035
  have p0037 :=
    @g_n_3bitr4i
      (.classMem (syn_copk (.cv x) A) (syn_cimagek (syn_cun (syn_cin (syn_cimagek (syn_cimak
                  (syn_cdif (syn_cins3k (syn_ccompl (syn_cimak
                          (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk)))
                          (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cimak
                      (syn_csymdif (syn_cins2k (syn_cins2k (syn_cssetk)))
                        (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk)))
                          (syn_cins3k (syn_csik (syn_csik (syn_cssetk))))))
                      (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))
                  (syn_cpw1 (syn_cpw1 (syn_c1c))))) (syn_cxpk (syn_cnnc) (syn_cvv)))
            (syn_cin (syn_cidk) (syn_cxpk (syn_ccompl (syn_cnnc)) (syn_cvv))))))
      (.classEq A (syn_cimak (syn_cun (syn_cin (syn_cimagek (syn_cimak (syn_cdif (syn_cins3k
                      (syn_ccompl (syn_cimak
                          (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk)))
                          (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cimak
                      (syn_csymdif (syn_cins2k (syn_cins2k (syn_cssetk)))
                        (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk)))
                          (syn_cins3k (syn_csik (syn_csik (syn_cssetk))))))
                      (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))
                  (syn_cpw1 (syn_cpw1 (syn_c1c))))) (syn_cxpk (syn_cnnc) (syn_cvv)))
            (syn_cin (syn_cidk) (syn_cxpk (syn_ccompl (syn_cnnc)) (syn_cvv)))) (.cv x)))
      (.classMem (syn_copk A (.cv x)) (syn_ccnvk (syn_cimagek (syn_cun (syn_cin (syn_cimagek
                  (syn_cimak (syn_cdif (syn_cins3k (syn_ccompl (syn_cimak
                            (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk)))
                            (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cimak
                        (syn_csymdif (syn_cins2k (syn_cins2k (syn_cssetk)))
                          (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk)))
                            (syn_cins3k (syn_csik (syn_csik (syn_cssetk))))))
                        (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))
                    (syn_cpw1 (syn_cpw1 (syn_c1c))))) (syn_cxpk (syn_cnnc) (syn_cvv)))
              (syn_cin (syn_cidk) (syn_cxpk (syn_ccompl (syn_cnnc)) (syn_cvv)))))))
      (.classEq A (syn_cphi (.cv x))) p0033 p0034 p0036
  have p0038 := @g_elssetk (.cv x) B p0032 hyp_setconslem1_2
  have p0039 :=
    @g_anbi12i
      (.classMem (syn_copk A (.cv x)) (syn_ccnvk (syn_cimagek (syn_cun (syn_cin (syn_cimagek
                  (syn_cimak (syn_cdif (syn_cins3k (syn_ccompl (syn_cimak
                            (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk)))
                            (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cimak
                        (syn_csymdif (syn_cins2k (syn_cins2k (syn_cssetk)))
                          (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk)))
                            (syn_cins3k (syn_csik (syn_csik (syn_cssetk))))))
                        (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))
                    (syn_cpw1 (syn_cpw1 (syn_c1c))))) (syn_cxpk (syn_cnnc) (syn_cvv)))
              (syn_cin (syn_cidk) (syn_cxpk (syn_ccompl (syn_cnnc)) (syn_cvv)))))))
      (.classEq A (syn_cphi (.cv x)))
      (.classMem (syn_copk (syn_csn (.cv x)) B) (syn_cssetk)) (.classMem (.cv x) B) p0037
      p0038
  have p0040 := @g_ancom (.classEq A (syn_cphi (.cv x))) (.classMem (.cv x) B)
  have p0041 :=
    @g_n_3bitri
      (syn_wex t (syn_wa (.classEq (.cv t) (syn_csn (.cv x))) (syn_wa
            (.classMem (syn_copk A (.cv x)) (syn_ccnvk (syn_cimagek (syn_cun (syn_cin
                      (syn_cimagek (syn_cimak (syn_cdif (syn_cins3k (syn_ccompl (syn_cimak
                                  (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk)))
                                  (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cimak
                              (syn_csymdif (syn_cins2k (syn_cins2k (syn_cssetk)))
                                (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk)))
                                  (syn_cins3k (syn_csik (syn_csik (syn_cssetk))))))
                              (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))
                          (syn_cpw1 (syn_cpw1 (syn_c1c))))) (syn_cxpk (syn_cnnc) (syn_cvv)))
                    (syn_cin (syn_cidk) (syn_cxpk (syn_ccompl (syn_cnnc)) (syn_cvv)))))))
            (.classMem (syn_copk (.cv t) B) (syn_cssetk)))))
      (syn_wa (.classMem (syn_copk A (.cv x)) (syn_ccnvk (syn_cimagek (syn_cun (syn_cin
                  (syn_cimagek (syn_cimak (syn_cdif (syn_cins3k (syn_ccompl (syn_cimak
                              (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk)))
                              (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cimak
                          (syn_csymdif (syn_cins2k (syn_cins2k (syn_cssetk)))
                            (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk)))
                              (syn_cins3k (syn_csik (syn_csik (syn_cssetk))))))
                          (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))
                      (syn_cpw1 (syn_cpw1 (syn_c1c))))) (syn_cxpk (syn_cnnc) (syn_cvv)))
                (syn_cin (syn_cidk) (syn_cxpk (syn_ccompl (syn_cnnc)) (syn_cvv)))))))
        (.classMem (syn_copk (syn_csn (.cv x)) B) (syn_cssetk)))
      (syn_wa (.classEq A (syn_cphi (.cv x))) (.classMem (.cv x) B))
      (syn_wa (.classMem (.cv x) B) (.classEq A (syn_cphi (.cv x)))) p0031 p0039 p0040
  have p0042 :=
    @g_exbii
      (syn_wex t (syn_wa (.classEq (.cv t) (syn_csn (.cv x))) (syn_wa
            (.classMem (syn_copk A (.cv x)) (syn_ccnvk (syn_cimagek (syn_cun (syn_cin
                      (syn_cimagek (syn_cimak (syn_cdif (syn_cins3k (syn_ccompl (syn_cimak
                                  (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk)))
                                  (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cimak
                              (syn_csymdif (syn_cins2k (syn_cins2k (syn_cssetk)))
                                (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk)))
                                  (syn_cins3k (syn_csik (syn_csik (syn_cssetk))))))
                              (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))
                          (syn_cpw1 (syn_cpw1 (syn_c1c))))) (syn_cxpk (syn_cnnc) (syn_cvv)))
                    (syn_cin (syn_cidk) (syn_cxpk (syn_ccompl (syn_cnnc)) (syn_cvv)))))))
            (.classMem (syn_copk (.cv t) B) (syn_cssetk)))))
      (syn_wa (.classMem (.cv x) B) (.classEq A (syn_cphi (.cv x)))) x p0041
  have p0043 :=
    @g_n_3bitr2i
      (syn_wex t (syn_wa (.classMem (syn_copk (syn_csn A) (.cv t)) (syn_csik (syn_ccnvk
                (syn_cimagek (syn_cun (syn_cin (syn_cimagek (syn_cimak (syn_cdif (syn_cins3k
                              (syn_ccompl (syn_cimak (syn_cin (syn_cins3k (syn_cssetk))
                                    (syn_cins2k (syn_cssetk)))
                                  (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cimak
                              (syn_csymdif (syn_cins2k (syn_cins2k (syn_cssetk)))
                                (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk)))
                                  (syn_cins3k (syn_csik (syn_csik (syn_cssetk))))))
                              (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))
                          (syn_cpw1 (syn_cpw1 (syn_c1c))))) (syn_cxpk (syn_cnnc) (syn_cvv)))
                    (syn_cin (syn_cidk) (syn_cxpk (syn_ccompl (syn_cnnc)) (syn_cvv))))))))
          (.classMem (syn_copk (.cv t) B) (syn_cssetk))))
      (syn_wex t (syn_wex x (syn_wa (.classEq (.cv t) (syn_csn (.cv x))) (syn_wa
              (.classMem (syn_copk A (.cv x)) (syn_ccnvk (syn_cimagek (syn_cun (syn_cin
                        (syn_cimagek (syn_cimak (syn_cdif (syn_cins3k (syn_ccompl (syn_cimak
                                    (syn_cin (syn_cins3k (syn_cssetk))
                                      (syn_cins2k (syn_cssetk)))
                                    (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cimak
                                (syn_csymdif (syn_cins2k (syn_cins2k (syn_cssetk)))
                                  (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk)))
                                    (syn_cins3k (syn_csik (syn_csik (syn_cssetk))))))
                                (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))
                            (syn_cpw1 (syn_cpw1 (syn_c1c))))) (syn_cxpk (syn_cnnc) (syn_cvv)))
                      (syn_cin (syn_cidk) (syn_cxpk (syn_ccompl (syn_cnnc)) (syn_cvv)))))))
              (.classMem (syn_copk (.cv t) B) (syn_cssetk))))))
      (syn_wex x (syn_wex t (syn_wa (.classEq (.cv t) (syn_csn (.cv x))) (syn_wa
              (.classMem (syn_copk A (.cv x)) (syn_ccnvk (syn_cimagek (syn_cun (syn_cin
                        (syn_cimagek (syn_cimak (syn_cdif (syn_cins3k (syn_ccompl (syn_cimak
                                    (syn_cin (syn_cins3k (syn_cssetk))
                                      (syn_cins2k (syn_cssetk)))
                                    (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cimak
                                (syn_csymdif (syn_cins2k (syn_cins2k (syn_cssetk)))
                                  (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk)))
                                    (syn_cins3k (syn_csik (syn_csik (syn_cssetk))))))
                                (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))
                            (syn_cpw1 (syn_cpw1 (syn_c1c))))) (syn_cxpk (syn_cnnc) (syn_cvv)))
                      (syn_cin (syn_cidk) (syn_cxpk (syn_ccompl (syn_cnnc)) (syn_cvv)))))))
              (.classMem (syn_copk (.cv t) B) (syn_cssetk))))))
      (syn_wex x (syn_wa (.classMem (.cv x) B) (.classEq A (syn_cphi (.cv x))))) p0025
      p0026 p0042
  have p0044 :=
    @g_opkelcok t (syn_csn A) B (syn_cssetk)
      (syn_csik (syn_ccnvk (syn_cimagek (syn_cun (syn_cin (syn_cimagek (syn_cimak (syn_cdif
                      (syn_cins3k (syn_ccompl (syn_cimak
                            (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk)))
                            (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cimak
                        (syn_csymdif (syn_cins2k (syn_cins2k (syn_cssetk)))
                          (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk)))
                            (syn_cins3k (syn_csik (syn_csik (syn_cssetk))))))
                        (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))
                    (syn_cpw1 (syn_cpw1 (syn_c1c))))) (syn_cxpk (syn_cnnc) (syn_cvv)))
              (syn_cin (syn_cidk) (syn_cxpk (syn_ccompl (syn_cnnc)) (syn_cvv)))))))
      dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 p0000 hyp_setconslem1_2
  have p0045 := (Nominal.biimpRefl (syn_wrex x B (.classEq A (syn_cphi (.cv x)))))
  have p0046 :=
    @g_n_3bitr4i
      (syn_wex t (syn_wa (.classMem (syn_copk (syn_csn A) (.cv t)) (syn_csik (syn_ccnvk
                (syn_cimagek (syn_cun (syn_cin (syn_cimagek (syn_cimak (syn_cdif (syn_cins3k
                              (syn_ccompl (syn_cimak (syn_cin (syn_cins3k (syn_cssetk))
                                    (syn_cins2k (syn_cssetk)))
                                  (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cimak
                              (syn_csymdif (syn_cins2k (syn_cins2k (syn_cssetk)))
                                (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk)))
                                  (syn_cins3k (syn_csik (syn_csik (syn_cssetk))))))
                              (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))
                          (syn_cpw1 (syn_cpw1 (syn_c1c))))) (syn_cxpk (syn_cnnc) (syn_cvv)))
                    (syn_cin (syn_cidk) (syn_cxpk (syn_ccompl (syn_cnnc)) (syn_cvv))))))))
          (.classMem (syn_copk (.cv t) B) (syn_cssetk))))
      (syn_wex x (syn_wa (.classMem (.cv x) B) (.classEq A (syn_cphi (.cv x)))))
      (.classMem (syn_copk (syn_csn A) B) (syn_ccomk (syn_cssetk) (syn_csik (syn_ccnvk
              (syn_cimagek (syn_cun (syn_cin (syn_cimagek (syn_cimak (syn_cdif (syn_cins3k
                            (syn_ccompl (syn_cimak (syn_cin (syn_cins3k (syn_cssetk))
                                  (syn_cins2k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c))))))
                          (syn_cimak (syn_csymdif (syn_cins2k (syn_cins2k (syn_cssetk)))
                              (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk)))
                                (syn_cins3k (syn_csik (syn_csik (syn_cssetk))))))
                            (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))
                        (syn_cpw1 (syn_cpw1 (syn_c1c))))) (syn_cxpk (syn_cnnc) (syn_cvv)))
                  (syn_cin (syn_cidk) (syn_cxpk (syn_ccompl (syn_cnnc)) (syn_cvv)))))))))
      (syn_wrex x B (.classEq A (syn_cphi (.cv x)))) p0043 p0044 p0045
  exact p0046


end NFChoice.DirectNominalPrf.WPPReplay

end
