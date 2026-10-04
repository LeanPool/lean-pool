/-
Copyright (c) 2026 Elliot Glazer and NFNotWPP contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elliot Glazer and NFNotWPP contributors
-/

module

public import LeanPool.NFWeakPartition.Certificates.NominalWPPReplayChunk013Compact001Block006

/-! Nominal proof certificates grouped in dependency order. -/


public section

/-! Certificates from `NominalWPPReplayChunk013Compact001Part029`. -/


section

namespace NFChoice.DirectNominalPrf.WPPReplay

open scoped Fol
open NFChoice.Foundation
open NFChoice.SemanticCore
open NFChoice.ReplaySupport
open NFChoice.Compiler.CompactSourceSyntax

/-- Checked nominal proof certificate identified upstream as `g_erth`. -/
@[expose]
noncomputable def gErth (ph : Wff) (A : Class) (B : Class) (R : Class) (V : Class)
    (X : Class) (hyp_erth_1 : Nominal.NPrf (.imp ph (synWbr R (synCer) (synCvv))))
    (hyp_erth_2 : Nominal.NPrf (.imp ph (.classEq (synCdm R) X)))
    (hyp_erth_3 : Nominal.NPrf (.imp ph (.classMem A X)))
    (hyp_erth_4 : Nominal.NPrf (.imp ph (.classMem B V))) :
    Nominal.NPrf
      (.imp ph (synWb (synWbr A R B) (.classEq (synCec A R) (synCec B R)))) :=
  by
  let proofSupport : Finset Var := ph.fv ∪ A.fv ∪ B.fv ∪ R.fv ∪ V.fv ∪ X.fv
  let x : Var := freshVar proofSupport 0
  have fresh_x : x ∉ proofSupport :=
    by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_x_not_ph : x ∉ ph.fv := by
    intro h
    exact
      fresh_x
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _
              (Finset.mem_union_left _ (Finset.mem_union_left _ (h))))))
  have fresh_x_not_A : x ∉ A.fv := by
    intro h
    exact
      fresh_x
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _
              (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))))
  have fresh_x_not_B : x ∉ B.fv := by
    intro h
    exact
      fresh_x
        (Finset.mem_union_left _ (Finset.mem_union_left _
            (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))))
  have fresh_x_not_R : x ∉ R.fv := by
    intro h
    exact
      fresh_x
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))
  have dv_cache_0001 : x ∉ ((synWa ph (synWbr A R B))).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr, Finset.mem_union,
          fresh_x_not_ph, fresh_x_not_A, fresh_x_not_B, fresh_x_not_R, or_false,
          not_false_eq_true])
  have dv_cache_0002 : x ∉ (A).fv :=
    by
    clear dv_cache_0001
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_x_not_A, not_false_eq_true])
  have dv_cache_0003 : x ∉ (R).fv :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_x_not_R, not_false_eq_true])
  have dv_cache_0004 : x ∉ (B).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_x_not_B, not_false_eq_true])
  have p0000 :=
    @gAdantr ph (synWbr R (synCer) (synCvv))
      (synWa (synWbr A R B) (synWbr A R (.cv x))) hyp_erth_1
  have p0001 := @gElex B V
  have p0002 := @gSyl ph (.classMem B V) (.classMem B (synCvv)) hyp_erth_4 p0001
  have p0003 :=
    @gAdantr ph (.classMem B (synCvv)) (synWa (synWbr A R B) (synWbr A R (.cv x)))
      p0002
  have p0004 := @gElex A X
  have p0005 := @gSyl ph (.classMem A X) (.classMem A (synCvv)) hyp_erth_3 p0004
  have p0006 :=
    @gAdantr ph (.classMem A (synCvv)) (synWa (synWbr A R B) (synWbr A R (.cv x)))
      p0005
  have p0007 := @gVex x
  have p0008 :=
    @gA1i (.classMem (.cv x) (synCvv))
      (synWa ph (synWa (synWbr A R B) (synWbr A R (.cv x)))) p0007
  have p0009 := @gSimprl ph (synWbr A R B) (synWbr A R (.cv x))
  have p0010 := @gSimprr ph (synWbr A R B) (synWbr A R (.cv x))
  have p0011 :=
    @gErtr3d (synWa ph (synWa (synWbr A R B) (synWbr A R (.cv x)))) (synCvv) R B A
      (.cv x) p0000 p0003 p0006 p0008 p0009 p0010
  have p0012 :=
    @gExpr ph (synWbr A R B) (synWbr A R (.cv x)) (synWbr B R (.cv x)) p0011
  have p0013 := @gA1i (.classMem (.cv x) (synCvv)) ph p0007
  have p0014 := @gErtr ph (synCvv) R A B (.cv x) hyp_erth_1 p0005 p0002 p0013
  have p0015 :=
    @gExpdimp ph (synWbr A R B) (synWbr B R (.cv x)) (synWbr A R (.cv x)) p0014
  have p0016 :=
    @gImpbid (synWa ph (synWbr A R B)) (synWbr A R (.cv x)) (synWbr B R (.cv x))
      p0012 p0015
  have p0017 :=
    @gAbbidv (synWa ph (synWbr A R B)) (synWbr A R (.cv x)) (synWbr B R (.cv x)) x
      dv_cache_0001 p0016
  have p0018 := @gDfec2 x A R dv_cache_0002 dv_cache_0003
  have p0019 := @gDfec2 x B R dv_cache_0004 dv_cache_0003
  have p0020 :=
    @gN3eqtr4g (synWa ph (synWbr A R B)) (.cab x (synWbr A R (.cv x)))
      (.cab x (synWbr B R (.cv x))) (synCec A R) (synCec B R) p0017 p0018 p0019
  have p0021 :=
    @gAdantr ph (synWbr R (synCer) (synCvv)) (.classEq (synCec A R) (synCec B R))
      hyp_erth_1
  have p0022 := @gSimpl ph (.classEq (synCec A R) (synCec B R))
  have p0023 :=
    @gN3syl (synWa ph (.classEq (synCec A R) (synCec B R))) ph (.classMem B V)
      (.classMem B (synCvv)) p0022 hyp_erth_4 p0001
  have p0024 :=
    @gN3syl (synWa ph (.classEq (synCec A R) (synCec B R))) ph (.classMem A X)
      (.classMem A (synCvv)) p0022 hyp_erth_3 p0004
  have p0025 := @gErref ph X R A hyp_erth_1 hyp_erth_2 hyp_erth_3
  have p0026 := @gElec A A R
  have p0027 := @gSylibr ph (synWbr A R A) (.classMem A (synCec A R)) p0025 p0026
  have p0028 := @gEleq2 (synCec A R) (synCec B R) A
  have p0029 :=
    @gSyl5ibcom ph (.classMem A (synCec A R)) (.classEq (synCec A R) (synCec B R))
      (.classMem A (synCec B R)) p0027 p0028
  have p0030 :=
    @gImp ph (.classEq (synCec A R) (synCec B R)) (.classMem A (synCec B R)) p0029
  have p0031 := @gElec A B R
  have p0032 :=
    @gSylib (synWa ph (.classEq (synCec A R) (synCec B R)))
      (.classMem A (synCec B R)) (synWbr B R A) p0030 p0031
  have p0033 :=
    @gErsym (synWa ph (.classEq (synCec A R) (synCec B R))) (synCvv) R B A p0021
      p0023 p0024 p0032
  have p0034 :=
    @gImpbida ph (synWbr A R B) (.classEq (synCec A R) (synCec B R)) p0020 p0033
  exact p0034

/-- Checked nominal proof certificate identified upstream as `g_erth2`. -/
@[expose]
noncomputable def gErth2 (ph : Wff) (A : Class) (B : Class) (R : Class) (V : Class)
    (X : Class) (hyp_erth2_1 : Nominal.NPrf (.imp ph (synWbr R (synCer) (synCvv))))
    (hyp_erth2_2 : Nominal.NPrf (.imp ph (.classEq (synCdm R) X)))
    (hyp_erth2_3 : Nominal.NPrf (.imp ph (.classMem A V)))
    (hyp_erth2_4 : Nominal.NPrf (.imp ph (.classMem B X))) :
    Nominal.NPrf
      (.imp ph (synWb (synWbr A R B) (.classEq (synCec A R) (synCec B R)))) :=
  by
  have p0000 := @gElex A V
  have p0001 := @gSyl ph (.classMem A V) (.classMem A (synCvv)) hyp_erth2_3 p0000
  have p0002 := @gElex B X
  have p0003 := @gSyl ph (.classMem B X) (.classMem B (synCvv)) hyp_erth2_4 p0002
  have p0004 := @gErsymb ph (synCvv) R A B hyp_erth2_1 p0001 p0003
  have p0005 := @gErth ph B A R V X hyp_erth2_1 hyp_erth2_2 hyp_erth2_4 hyp_erth2_3
  have p0006 := @gEqcom (synCec B R) (synCec A R)
  have p0007 :=
    @gSyl6bb ph (synWbr B R A) (.classEq (synCec B R) (synCec A R))
      (.classEq (synCec A R) (synCec B R)) p0005 p0006
  have p0008 :=
    @gBitrd ph (synWbr A R B) (synWbr B R A) (.classEq (synCec A R) (synCec B R))
      p0004 p0007
  exact p0008

/-- Checked nominal proof certificate identified upstream as `g_erthi`. -/
@[expose]
noncomputable def gErthi (ph : Wff) (A : Class) (B : Class) (R : Class)
    (hyp_erthi_1 : Nominal.NPrf (.imp ph (synWbr R (synCer) (synCvv))))
    (hyp_erthi_4 : Nominal.NPrf (.imp ph (synWbr A R B))) :
    Nominal.NPrf (.imp ph (.classEq (synCec A R) (synCec B R))) :=
  by
  have p0000 := @gEqidd ph (synCdm R)
  have p0001 := @gBreldm A B R
  have p0002 := @gSyl ph (synWbr A R B) (.classMem A (synCdm R)) hyp_erthi_4 p0001
  have p0003 := @gBrelrn A B R
  have p0004 := @gSyl ph (synWbr A R B) (.classMem B (synCrn R)) hyp_erthi_4 p0003
  have p0005 := @gErth ph A B R (synCrn R) (synCdm R) hyp_erthi_1 p0000 p0002 p0004
  have p0006 :=
    @gMpbid ph (synWbr A R B) (.classEq (synCec A R) (synCec B R)) hyp_erthi_4 p0005
  exact p0006

/-- Checked nominal proof certificate identified upstream as `g_erdisj`. -/
@[expose]
noncomputable def gErdisj (A : Class) (B : Class) (R : Class) :
    Nominal.NPrf
      (.imp (synWbr R (synCer) (synCvv)) (synWo (.classEq (synCec A R) (synCec B R))
          (.classEq (synCin (synCec A R) (synCec B R)) (synC0)))) :=
  by
  let proofSupport : Finset Var := A.fv ∪ B.fv ∪ R.fv
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
  have fresh_x_not_R : x ∉ R.fv := by
    intro h
    exact fresh_x (Finset.mem_union_right _ (h))
  have dv_cache_0001 : x ∉ ((synCin (synCec A R) (synCec B R))).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cec, Finset.mem_union,
          fresh_x_not_A, fresh_x_not_R, fresh_x_not_B, or_false, not_false_eq_true])
  have dv_cache_0002 : x ∉ ((Wff.classEq (synCec A R) (synCec B R))).fv :=
    by
    clear dv_cache_0001
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cec, Finset.mem_union,
          fresh_x_not_A, fresh_x_not_R, fresh_x_not_B, or_false, not_false_eq_true])
  have dv_cache_0003 : x ∉ ((synWbr R (synCer) (synCvv))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cer,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv, Finset.mem_union,
          fresh_x_not_R, compact_fv_not_mem_empty, or_false, not_false_eq_true])
  have p0000 := @gNeq0 x (synCin (synCec A R) (synCec B R)) dv_cache_0001
  have p0001 :=
    @gSimpl (synWbr R (synCer) (synCvv))
      (.classMem (.cv x) (synCin (synCec A R) (synCec B R)))
  have p0002 := @gInss1 (synCec A R) (synCec B R)
  have p0003 := @gSseli (synCin (synCec A R) (synCec B R)) (synCec A R) (.cv x) p0002
  have p0004 :=
    @gAdantl (.classMem (.cv x) (synCin (synCec A R) (synCec B R)))
      (.classMem (.cv x) (synCec A R)) (synWbr R (synCer) (synCvv)) p0003
  have p0005 := @gEcexr (.cv x) A R
  have p0006 :=
    @gSyl
      (synWa (synWbr R (synCer) (synCvv))
        (.classMem (.cv x) (synCin (synCec A R) (synCec B R))))
      (.classMem (.cv x) (synCec A R)) (.classMem A (synCvv)) p0004 p0005
  have p0007 := @gVex x
  have p0008 :=
    @gA1i (.classMem (.cv x) (synCvv))
      (synWa (synWbr R (synCer) (synCvv))
        (.classMem (.cv x) (synCin (synCec A R) (synCec B R))))
      p0007
  have p0009 := @gInss2 (synCec A R) (synCec B R)
  have p0010 := @gSseli (synCin (synCec A R) (synCec B R)) (synCec B R) (.cv x) p0009
  have p0011 :=
    @gAdantl (.classMem (.cv x) (synCin (synCec A R) (synCec B R)))
      (.classMem (.cv x) (synCec B R)) (synWbr R (synCer) (synCvv)) p0010
  have p0012 := @gEcexr (.cv x) B R
  have p0013 :=
    @gSyl
      (synWa (synWbr R (synCer) (synCvv))
        (.classMem (.cv x) (synCin (synCec A R) (synCec B R))))
      (.classMem (.cv x) (synCec B R)) (.classMem B (synCvv)) p0011 p0012
  have p0014 := @gElec (.cv x) A R
  have p0015 :=
    @gSylib (.classMem (.cv x) (synCin (synCec A R) (synCec B R)))
      (.classMem (.cv x) (synCec A R)) (synWbr A R (.cv x)) p0003 p0014
  have p0016 :=
    @gAdantl (.classMem (.cv x) (synCin (synCec A R) (synCec B R)))
      (synWbr A R (.cv x)) (synWbr R (synCer) (synCvv)) p0015
  have p0017 := @gElec (.cv x) B R
  have p0018 :=
    @gSylib (.classMem (.cv x) (synCin (synCec A R) (synCec B R)))
      (.classMem (.cv x) (synCec B R)) (synWbr B R (.cv x)) p0010 p0017
  have p0019 :=
    @gAdantl (.classMem (.cv x) (synCin (synCec A R) (synCec B R)))
      (synWbr B R (.cv x)) (synWbr R (synCer) (synCvv)) p0018
  have p0020 :=
    @gErtr4d
      (synWa (synWbr R (synCer) (synCvv))
        (.classMem (.cv x) (synCin (synCec A R) (synCec B R))))
      (synCvv) R A (.cv x) B p0001 p0006 p0008 p0013 p0016 p0019
  have p0021 :=
    @gErthi
      (synWa (synWbr R (synCer) (synCvv))
        (.classMem (.cv x) (synCin (synCec A R) (synCec B R))))
      A B R p0001 p0020
  have p0022 :=
    @gEx (synWbr R (synCer) (synCvv))
      (.classMem (.cv x) (synCin (synCec A R) (synCec B R)))
      (.classEq (synCec A R) (synCec B R)) p0021
  have p0023 :=
    @gExlimdv (synWbr R (synCer) (synCvv))
      (.classMem (.cv x) (synCin (synCec A R) (synCec B R)))
      (.classEq (synCec A R) (synCec B R)) x dv_cache_0002 dv_cache_0003 p0022
  have p0024 :=
    @gSyl5bi (.neg (.classEq (synCin (synCec A R) (synCec B R)) (synC0)))
      (synWex x (.classMem (.cv x) (synCin (synCec A R) (synCec B R))))
      (synWbr R (synCer) (synCvv)) (.classEq (synCec A R) (synCec B R)) p0000 p0023
  have p0025 :=
    @gOrrd (synWbr R (synCer) (synCvv))
      (.classEq (synCin (synCec A R) (synCec B R)) (synC0))
      (.classEq (synCec A R) (synCec B R)) p0024
  have p0026 :=
    @gOrcomd (synWbr R (synCer) (synCvv))
      (.classEq (synCin (synCec A R) (synCec B R)) (synC0))
      (.classEq (synCec A R) (synCec B R)) p0025
  exact p0026

/-- Checked nominal proof certificate identified upstream as `g_qseq1`. -/
@[expose]
noncomputable def gQseq1 (A : Class) (B : Class) (C : Class) :
    Nominal.NPrf (.imp (.classEq A B) (.classEq (synCqs A C) (synCqs B C))) :=
  by
  let proofSupport : Finset Var := A.fv ∪ B.fv ∪ C.fv
  let y : Var := freshVar proofSupport 0
  let x : Var := freshVar proofSupport 1
  have fresh_y : y ∉ proofSupport :=
    by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_y_not_A : y ∉ A.fv := by
    intro h
    exact fresh_y (Finset.mem_union_left _ (Finset.mem_union_left _ (h)))
  have fresh_y_not_B : y ∉ B.fv := by
    intro h
    exact fresh_y (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_y_not_C : y ∉ C.fv := by
    intro h
    exact fresh_y (Finset.mem_union_right _ (h))
  have fresh_x : x ∉ proofSupport :=
    by
    change freshVar proofSupport 1 ∉ proofSupport
    exact freshVar_not_mem proofSupport 1
  have fresh_x_not_A : x ∉ A.fv := by
    intro h
    exact fresh_x (Finset.mem_union_left _ (Finset.mem_union_left _ (h)))
  have fresh_x_not_B : x ∉ B.fv := by
    intro h
    exact fresh_x (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_x_not_C : x ∉ C.fv := by
    intro h
    exact fresh_x (Finset.mem_union_right _ (h))
  have fresh_y_ne_x : y ≠ x :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have fresh_x_ne_y : x ≠ y := Ne.symm fresh_y_ne_x
  have dv_cache_0001 : x ∉ (A).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_x_not_A, not_false_eq_true])
  have dv_cache_0002 : x ∉ (B).fv :=
    by
    clear dv_cache_0001
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_x_not_B, not_false_eq_true])
  have dv_cache_0003 : y ∉ ((Wff.classEq A B)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, Finset.mem_union,
          fresh_y_not_A, fresh_y_not_B, or_false, not_false_eq_true])
  have dv_cache_0004 : y ∉ (A).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_y_not_A, not_false_eq_true])
  have dv_cache_0005 : x ∉ (C).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_x_not_C, not_false_eq_true])
  have dv_cache_0006 : y ∉ (C).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_y_not_C, not_false_eq_true])
  have dv_cache_0007 : x ≠ y :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006
    exact (show x ≠ y from (by exact fresh_x_ne_y))
  have dv_cache_0008 : y ∉ (B).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_y_not_B, not_false_eq_true])
  have p0000 :=
    @gRexeq (.classEq (.cv y) (synCec (.cv x) C)) x A B dv_cache_0001 dv_cache_0002
  have p0001 :=
    @gAbbidv (.classEq A B) (synWrex x A (.classEq (.cv y) (synCec (.cv x) C)))
      (synWrex x B (.classEq (.cv y) (synCec (.cv x) C))) y dv_cache_0003 p0000
  have p0002 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominalDfQs x y A C
      dv_cache_0001 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007
  have p0003 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominalDfQs x y B C
      dv_cache_0002 dv_cache_0008 dv_cache_0005 dv_cache_0006 dv_cache_0007
  have p0004 :=
    @gN3eqtr4g (.classEq A B)
      (.cab y (synWrex x A (.classEq (.cv y) (synCec (.cv x) C))))
      (.cab y (synWrex x B (.classEq (.cv y) (synCec (.cv x) C)))) (synCqs A C)
      (synCqs B C) p0001 p0002 p0003
  exact p0004

/-- Checked nominal proof certificate identified upstream as `g_qseq2`. -/
@[expose]
noncomputable def gQseq2 (A : Class) (B : Class) (C : Class) :
    Nominal.NPrf (.imp (.classEq A B) (.classEq (synCqs C A) (synCqs C B))) :=
  by
  let proofSupport : Finset Var := A.fv ∪ B.fv ∪ C.fv
  let y : Var := freshVar proofSupport 0
  let x : Var := freshVar proofSupport 1
  have fresh_y : y ∉ proofSupport :=
    by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_y_not_A : y ∉ A.fv := by
    intro h
    exact fresh_y (Finset.mem_union_left _ (Finset.mem_union_left _ (h)))
  have fresh_y_not_B : y ∉ B.fv := by
    intro h
    exact fresh_y (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_y_not_C : y ∉ C.fv := by
    intro h
    exact fresh_y (Finset.mem_union_right _ (h))
  have fresh_x : x ∉ proofSupport :=
    by
    change freshVar proofSupport 1 ∉ proofSupport
    exact freshVar_not_mem proofSupport 1
  have fresh_x_not_A : x ∉ A.fv := by
    intro h
    exact fresh_x (Finset.mem_union_left _ (Finset.mem_union_left _ (h)))
  have fresh_x_not_B : x ∉ B.fv := by
    intro h
    exact fresh_x (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_x_not_C : x ∉ C.fv := by
    intro h
    exact fresh_x (Finset.mem_union_right _ (h))
  have fresh_y_ne_x : y ≠ x :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have fresh_x_ne_y : x ≠ y := Ne.symm fresh_y_ne_x
  have dv_cache_0001 : x ∉ ((Wff.classEq A B)).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, Finset.mem_union,
          fresh_x_not_A, fresh_x_not_B, or_false, not_false_eq_true])
  have dv_cache_0002 : y ∉ ((Wff.classEq A B)).fv :=
    by
    clear dv_cache_0001
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, Finset.mem_union,
          fresh_y_not_A, fresh_y_not_B, or_false, not_false_eq_true])
  have dv_cache_0003 : x ∉ (C).fv :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_x_not_C, not_false_eq_true])
  have dv_cache_0004 : y ∉ (C).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_y_not_C, not_false_eq_true])
  have dv_cache_0005 : x ∉ (A).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_x_not_A, not_false_eq_true])
  have dv_cache_0006 : y ∉ (A).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_y_not_A, not_false_eq_true])
  have dv_cache_0007 : x ≠ y :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006
    exact (show x ≠ y from (by exact fresh_x_ne_y))
  have dv_cache_0008 : x ∉ (B).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_x_not_B, not_false_eq_true])
  have dv_cache_0009 : y ∉ (B).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_y_not_B, not_false_eq_true])
  have p0000 := @gEceq2 A B (.cv x)
  have p0001 :=
    @gEqeq2d (.classEq A B) (synCec (.cv x) A) (synCec (.cv x) B) (.cv y) p0000
  have p0002 :=
    @gRexbidv (.classEq A B) (.classEq (.cv y) (synCec (.cv x) A))
      (.classEq (.cv y) (synCec (.cv x) B)) x C dv_cache_0001 p0001
  have p0003 :=
    @gAbbidv (.classEq A B) (synWrex x C (.classEq (.cv y) (synCec (.cv x) A)))
      (synWrex x C (.classEq (.cv y) (synCec (.cv x) B))) y dv_cache_0002 p0002
  have p0004 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominalDfQs x y C A
      dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007
  have p0005 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominalDfQs x y C B
      dv_cache_0003 dv_cache_0004 dv_cache_0008 dv_cache_0009 dv_cache_0007
  have p0006 :=
    @gN3eqtr4g (.classEq A B)
      (.cab y (synWrex x C (.classEq (.cv y) (synCec (.cv x) A))))
      (.cab y (synWrex x C (.classEq (.cv y) (synCec (.cv x) B)))) (synCqs C A)
      (synCqs C B) p0003 p0004 p0005
  exact p0006

/-- Checked nominal proof certificate identified upstream as `g_elqsg`. -/
@[expose]
noncomputable def gElqsg (x : Var) (A : Class) (B : Class) (R : Class) (V : Class)
    (dv_A_x : x ∉ A.fv) (dv_B_x : x ∉ B.fv) (dv_R_x : x ∉ R.fv) :
    Nominal.NPrf
      (.imp (.classMem B V) (synWb (.classMem B (synCqs A R))
          (synWrex x A (.classEq B (synCec (.cv x) R))))) :=
  by
  let proofSupport : Finset Var := ({ x } : Finset Var) ∪ A.fv ∪ B.fv ∪ R.fv ∪ V.fv
  let y : Var := freshVar proofSupport 0
  have fresh_y : y ∉ proofSupport :=
    by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_y_ne_x : y ≠ x := by
    intro h
    exact
      fresh_y
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _
              (Finset.mem_union_left _ (Finset.mem_singleton.mpr h)))))
  have fresh_x_ne_y : x ≠ y := Ne.symm fresh_y_ne_x
  have fresh_y_not_A : y ∉ A.fv := by
    intro h
    exact
      fresh_y
        (Finset.mem_union_left _ (Finset.mem_union_left _
            (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))))
  have fresh_y_not_B : y ∉ B.fv := by
    intro h
    exact
      fresh_y
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))
  have fresh_y_not_R : y ∉ R.fv := by
    intro h
    exact fresh_y (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have dv_cache_0001 : x ∉ ((Wff.classEq (.cv y) B)).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, fresh_x_ne_y, dv_B_x, or_false, not_false_eq_true])
  have dv_cache_0002 : x ∉ (A).fv :=
    by
    clear dv_cache_0001
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_A_x, not_false_eq_true])
  have dv_cache_0003 : y ∉ (A).fv :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_y_not_A, not_false_eq_true])
  have dv_cache_0004 : x ∉ (R).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_R_x, not_false_eq_true])
  have dv_cache_0005 : y ∉ (R).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_y_not_R, not_false_eq_true])
  have dv_cache_0006 : x ≠ y :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact (show x ≠ y from (by exact fresh_x_ne_y))
  have dv_cache_0007 : y ∉ (B).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_y_not_B, not_false_eq_true])
  have dv_cache_0008 : y ∉ ((synWrex x A (.classEq B (synCec (.cv x) R)))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wrex,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cec,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase,
          Finset.mem_singleton, fresh_y_not_A, fresh_y_not_B, fresh_y_ne_x, fresh_y_not_R,
          or_false, and_false, not_false_eq_true])
  have p0000 := @gEqeq1 (.cv y) B (synCec (.cv x) R)
  have p0001 :=
    @gRexbidv (.classEq (.cv y) B) (.classEq (.cv y) (synCec (.cv x) R))
      (.classEq B (synCec (.cv x) R)) x A dv_cache_0001 p0000
  have p0002 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominalDfQs x y A R
      dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006
  have p0003 :=
    @gElab2g (synWrex x A (.classEq (.cv y) (synCec (.cv x) R)))
      (synWrex x A (.classEq B (synCec (.cv x) R))) y B (synCqs A R) V dv_cache_0007
      dv_cache_0008 p0001 p0002
  exact p0003

/-- Checked nominal proof certificate identified upstream as `g_elqs`. -/
@[expose]
noncomputable def gElqs (x : Var) (A : Class) (B : Class) (R : Class) (dv_A_x : x ∉ A.fv)
    (dv_B_x : x ∉ B.fv) (dv_R_x : x ∉ R.fv)
    (hyp_elqs_1 : Nominal.NPrf (.classMem B (synCvv))) :
    Nominal.NPrf
      (synWb (.classMem B (synCqs A R)) (synWrex x A (.classEq B (synCec (.cv x) R)))) :=
  by
  have dv_cache_0001 : x ∉ (A).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_A_x, not_false_eq_true])
  have dv_cache_0002 : x ∉ (B).fv :=
    by
    clear dv_cache_0001
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_B_x, not_false_eq_true])
  have dv_cache_0003 : x ∉ (R).fv :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_R_x, not_false_eq_true])
  have p0000 := @gElqsg x A B R (synCvv) dv_cache_0001 dv_cache_0002 dv_cache_0003
  have p0001 := Nominal.mp hyp_elqs_1 p0000
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_elqsi`. -/
@[expose]
noncomputable def gElqsi (x : Var) (A : Class) (B : Class) (R : Class)
    (dv_A_x : x ∉ A.fv) (dv_B_x : x ∉ B.fv) (dv_R_x : x ∉ R.fv) :
    Nominal.NPrf
      (.imp (.classMem B (synCqs A R)) (synWrex x A (.classEq B (synCec (.cv x) R)))) :=
  by
  have dv_cache_0001 : x ∉ (A).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_A_x, not_false_eq_true])
  have dv_cache_0002 : x ∉ (B).fv :=
    by
    clear dv_cache_0001
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_B_x, not_false_eq_true])
  have dv_cache_0003 : x ∉ (R).fv :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_R_x, not_false_eq_true])
  have p0000 := @gElqsg x A B R (synCqs A R) dv_cache_0001 dv_cache_0002 dv_cache_0003
  have p0001 :=
    @gIbi (.classMem B (synCqs A R)) (synWrex x A (.classEq B (synCec (.cv x) R)))
      p0000
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_ecelqsg`. -/
@[expose]
noncomputable def gEcelqsg (A : Class) (B : Class) (R : Class) (V : Class) :
    Nominal.NPrf
      (.imp (synWa (.classMem R V) (.classMem B A)) (.classMem (synCec B R) (synCqs A R))) :=
  by
  let proofSupport : Finset Var := A.fv ∪ B.fv ∪ R.fv ∪ V.fv
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
  have fresh_x_not_R : x ∉ R.fv := by
    intro h
    exact fresh_x (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have dv_cache_0001 : x ∉ (B).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_x_not_B, not_false_eq_true])
  have dv_cache_0002 : x ∉ (A).fv :=
    by
    clear dv_cache_0001
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_x_not_A, not_false_eq_true])
  have dv_cache_0003 : x ∉ ((Wff.classEq (synCec B R) (synCec B R))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cec, Finset.mem_union,
          fresh_x_not_B, fresh_x_not_R, or_false, not_false_eq_true])
  have dv_cache_0004 : x ∉ ((synCec B R)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cec, Finset.mem_union,
          fresh_x_not_B, fresh_x_not_R, or_false, not_false_eq_true])
  have dv_cache_0005 : x ∉ (R).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_x_not_R, not_false_eq_true])
  have p0000 := @gEqid (synCec B R)
  have p0001 := @gEceq1 (.cv x) B R
  have p0002 :=
    @gEqeq2d (.classEq (.cv x) B) (synCec (.cv x) R) (synCec B R) (synCec B R) p0001
  have p0003 :=
    @gRspcev (.classEq (synCec B R) (synCec (.cv x) R))
      (.classEq (synCec B R) (synCec B R)) x B A dv_cache_0001 dv_cache_0002
      dv_cache_0003 p0002
  have p0004 :=
    @gMpan2 (.classMem B A) (.classEq (synCec B R) (synCec B R))
      (synWrex x A (.classEq (synCec B R) (synCec (.cv x) R))) p0000 p0003
  have p0005 := @gEcexg B V R
  have p0006 :=
    @gElqsg x A (synCec B R) R (synCvv) dv_cache_0002 dv_cache_0004 dv_cache_0005
  have p0007 :=
    @gSyl (.classMem R V) (.classMem (synCec B R) (synCvv))
      (synWb (.classMem (synCec B R) (synCqs A R))
        (synWrex x A (.classEq (synCec B R) (synCec (.cv x) R))))
      p0005 p0006
  have p0008 :=
    @gBiimpar (.classMem R V) (.classMem (synCec B R) (synCqs A R))
      (synWrex x A (.classEq (synCec B R) (synCec (.cv x) R))) p0007
  have p0009 :=
    @gSylan2 (.classMem B A) (.classMem R V)
      (synWrex x A (.classEq (synCec B R) (synCec (.cv x) R)))
      (.classMem (synCec B R) (synCqs A R)) p0004 p0008
  exact p0009

/-- Checked nominal proof certificate identified upstream as `g_ecelqsi`. -/
@[expose]
noncomputable def gEcelqsi (A : Class) (B : Class) (R : Class)
    (hyp_ecelqsi_1 : Nominal.NPrf (.classMem R (synCvv))) :
    Nominal.NPrf (.imp (.classMem B A) (.classMem (synCec B R) (synCqs A R))) :=
  by
  have p0000 := @gEcelqsg A B R (synCvv)
  have p0001 :=
    @gMpan (.classMem R (synCvv)) (.classMem B A)
      (.classMem (synCec B R) (synCqs A R)) hyp_ecelqsi_1 p0000
  exact p0001


end NFChoice.DirectNominalPrf.WPPReplay

end

/-! Certificates from `NominalWPPReplayChunk013Compact001Part030`. -/


section

namespace NFChoice.DirectNominalPrf.WPPReplay

open scoped Fol
open NFChoice.Foundation
open NFChoice.SemanticCore
open NFChoice.ReplaySupport
open NFChoice.Compiler.CompactSourceSyntax

/-- Checked nominal proof certificate identified upstream as `g_qsexg`. -/
@[expose]
noncomputable def gQsexg (A : Class) (R : Class) (V : Class) (W : Class) :
    Nominal.NPrf
      (.imp (synWa (.classMem R V) (.classMem A W)) (.classMem (synCqs A R) (synCvv))) :=
  by
  let proofSupport : Finset Var := A.fv ∪ R.fv ∪ V.fv ∪ W.fv
  let x : Var := freshVar proofSupport 0
  let y : Var := freshVar proofSupport 1
  let z : Var := freshVar proofSupport 2
  have fresh_x : x ∉ proofSupport :=
    by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_x_not_A : x ∉ A.fv := by
    intro h
    exact
      fresh_x
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (h))))
  have fresh_x_not_R : x ∉ R.fv := by
    intro h
    exact
      fresh_x
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))
  have fresh_y : y ∉ proofSupport :=
    by
    change freshVar proofSupport 1 ∉ proofSupport
    exact freshVar_not_mem proofSupport 1
  have fresh_y_not_A : y ∉ A.fv := by
    intro h
    exact
      fresh_y
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (h))))
  have fresh_y_not_R : y ∉ R.fv := by
    intro h
    exact
      fresh_y
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))
  have fresh_z : z ∉ proofSupport :=
    by
    change freshVar proofSupport 2 ∉ proofSupport
    exact freshVar_not_mem proofSupport 2
  have fresh_z_not_R : z ∉ R.fv := by
    intro h
    exact
      fresh_z
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))
  have fresh_x_ne_y : x ≠ y :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have fresh_y_ne_x : y ≠ x := Ne.symm fresh_x_ne_y
  have fresh_x_ne_z : x ≠ z :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 2
    exact freshVar_injective proofSupport (i := 0) (j := 2) (by decide)
  have fresh_z_ne_x : z ≠ x := Ne.symm fresh_x_ne_z
  have fresh_y_ne_z : y ≠ z :=
    by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 2
    exact freshVar_injective proofSupport (i := 1) (j := 2) (by decide)
  have fresh_z_ne_y : z ≠ y := Ne.symm fresh_y_ne_z
  have dv_cache_0001 : y ∉ (A).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_y_not_A, not_false_eq_true])
  have dv_cache_0002 : x ∉ (A).fv :=
    by
    clear dv_cache_0001
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_x_not_A, not_false_eq_true])
  have dv_cache_0003 : y ∉ (R).fv :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_y_not_R, not_false_eq_true])
  have dv_cache_0004 : x ∉ (R).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_x_not_R, not_false_eq_true])
  have dv_cache_0005 : y ≠ x :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact (show y ≠ x from (by exact fresh_y_ne_x))
  have dv_cache_0006 : y ∉ ((Class.cv x)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_y_ne_x, not_false_eq_true])
  have dv_cache_0007 :
    y ∉
      ((synCcompl (synCima
            (synCsymdif (synCins2 (synCsset)) (synCins3 (synCsi (synCcnv R))))
            (synC1c)))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccompl,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cima,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csymdif,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins2,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csset,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins3,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csi,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c, Finset.mem_union,
          fresh_y_not_R, compact_fv_not_mem_empty, or_false, not_false_eq_true])
  have dv_cache_0008 : z ∉ ((synCop (synCsn (.cv y)) (.cv x))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007
    exact
      (by
        have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cop,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, fresh_z_ne_y, fresh_z_ne_x, or_false, not_false_eq_true])
  have dv_cache_0009 :
    z ∉ ((synCsymdif (synCins2 (synCsset)) (synCins3 (synCsi (synCcnv R))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008
    exact
      (by
        have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csymdif,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins2,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csset,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins3,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csi,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv, Finset.mem_union,
          fresh_z_not_R, compact_fv_not_mem_empty, or_false, not_false_eq_true])
  have dv_cache_0010 : z ∉ ((Class.cv x)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009
    exact
      (by
        have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_z_ne_x, not_false_eq_true])
  have dv_cache_0011 : z ∉ ((synCec (.cv y) R)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010
    exact
      (by
        have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cec,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, fresh_z_ne_y, fresh_z_not_R, or_false, not_false_eq_true])
  have dv_cache_0012 :
    x ∉
      ((synCima (synCcompl (synCima
              (synCsymdif (synCins2 (synCsset)) (synCins3 (synCsi (synCcnv R))))
              (synC1c))) (synCpw1 A))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cima,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccompl,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csymdif,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins2,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csset,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins3,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csi,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1, Finset.mem_union,
          fresh_x_not_R, fresh_x_not_A, compact_fv_not_mem_empty, or_false,
          not_false_eq_true])
  have p0000 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominalDfQs y x A R
      dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
  have p0001 :=
    @gElimapw1 y (.cv x)
      (synCcompl
        (synCima (synCsymdif (synCins2 (synCsset)) (synCins3 (synCsi (synCcnv R))))
          (synC1c)))
      A dv_cache_0006 dv_cache_0007 dv_cache_0001
  have p0002 :=
    @gElima1c z (synCop (synCsn (.cv y)) (.cv x))
      (synCsymdif (synCins2 (synCsset)) (synCins3 (synCsi (synCcnv R))))
      dv_cache_0008 dv_cache_0009
  have p0003 :=
    @gElsymdif (synCop (synCsn (.cv z)) (synCop (synCsn (.cv y)) (.cv x)))
      (synCins2 (synCsset)) (synCins3 (synCsi (synCcnv R)))
  have p0004 := @gSnex (.cv y)
  have p0005 := @gOtelins2 (synCsn (.cv z)) (synCsn (.cv y)) (.cv x) (synCsset) p0004
  have p0006 := @gVex z
  have p0007 := @gVex x
  have p0008 := @gOpelssetsn (.cv z) (.cv x) p0006 p0007
  have p0009_e01_recanon :
    Nominal.NPrf
      (synWb (.classMem (synCop (synCsn (.cv z)) (.cv x)) (synCsset)) (.objMem z x)) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold synWb synCop synCun synCnin synWnan synWa synCcompl synWrex synWex
          synCphi synCsn synCsset synCopab synWss synCin
        simp (config :=
          { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_class_cv]
        apply Nominal.RecanonTransportDev.TRecanonWff.neg
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · apply Nominal.RecanonTransportDev.TRecanonWff.imp
          · exact Nominal.RecanonTransportDev.TRecanonWff.same _
          · exact Nominal.RecanonTransportDev.TRecanonWff.classMem_objMem _ _
        · apply Nominal.RecanonTransportDev.TRecanonWff.neg
          apply Nominal.RecanonTransportDev.TRecanonWff.imp
          · exact Nominal.RecanonTransportDev.TRecanonWff.classMem_objMem _ _
          · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0008
  have p0009 :=
    @gBitri
      (.classMem (synCop (synCsn (.cv z)) (synCop (synCsn (.cv y)) (.cv x)))
        (synCins2 (synCsset)))
      (.classMem (synCop (synCsn (.cv z)) (.cv x)) (synCsset)) (.objMem z x) p0005
      p0009_e01_recanon
  have p0010 :=
    @gOtelins3 (synCsn (.cv z)) (synCsn (.cv y)) (.cv x) (synCsi (synCcnv R)) p0007
  have p0011 := (Nominal.biimpRefl (synWbr (.cv z) (synCcnv R) (.cv y)))
  have p0012 := @gBrcnv (.cv z) (.cv y) R
  have p0013 :=
    @gBitr3i (.classMem (synCop (.cv z) (.cv y)) (synCcnv R))
      (synWbr (.cv z) (synCcnv R) (.cv y)) (synWbr (.cv y) R (.cv z)) p0011 p0012
  have p0014 := @gVex y
  have p0015 := @gOpsnelsi (.cv z) (.cv y) (synCcnv R) p0006 p0014
  have p0016 := @gElec (.cv z) (.cv y) R
  have p0017 :=
    @gN3bitr4i (.classMem (synCop (.cv z) (.cv y)) (synCcnv R))
      (synWbr (.cv y) R (.cv z))
      (.classMem (synCop (synCsn (.cv z)) (synCsn (.cv y))) (synCsi (synCcnv R)))
      (.classMem (.cv z) (synCec (.cv y) R)) p0013 p0015 p0016
  have p0018 :=
    @gBitri
      (.classMem (synCop (synCsn (.cv z)) (synCop (synCsn (.cv y)) (.cv x)))
        (synCins3 (synCsi (synCcnv R))))
      (.classMem (synCop (synCsn (.cv z)) (synCsn (.cv y))) (synCsi (synCcnv R)))
      (.classMem (.cv z) (synCec (.cv y) R)) p0010 p0017
  have p0019 :=
    @gBibi12i
      (.classMem (synCop (synCsn (.cv z)) (synCop (synCsn (.cv y)) (.cv x)))
        (synCins2 (synCsset)))
      (.objMem z x)
      (.classMem (synCop (synCsn (.cv z)) (synCop (synCsn (.cv y)) (.cv x)))
        (synCins3 (synCsi (synCcnv R))))
      (.classMem (.cv z) (synCec (.cv y) R)) p0009 p0018
  have p0020 :=
    @gNotbii
      (synWb (.classMem (synCop (synCsn (.cv z)) (synCop (synCsn (.cv y)) (.cv x)))
          (synCins2 (synCsset)))
        (.classMem (synCop (synCsn (.cv z)) (synCop (synCsn (.cv y)) (.cv x)))
          (synCins3 (synCsi (synCcnv R)))))
      (synWb (.objMem z x) (.classMem (.cv z) (synCec (.cv y) R))) p0019
  have p0021 :=
    @gBitri
      (.classMem (synCop (synCsn (.cv z)) (synCop (synCsn (.cv y)) (.cv x)))
        (synCsymdif (synCins2 (synCsset)) (synCins3 (synCsi (synCcnv R)))))
      (.neg (synWb (.classMem (synCop (synCsn (.cv z)) (synCop (synCsn (.cv y)) (.cv x)))
            (synCins2 (synCsset)))
          (.classMem (synCop (synCsn (.cv z)) (synCop (synCsn (.cv y)) (.cv x)))
            (synCins3 (synCsi (synCcnv R))))))
      (.neg (synWb (.objMem z x) (.classMem (.cv z) (synCec (.cv y) R)))) p0003 p0020
  have p0022 :=
    @gExbii
      (.classMem (synCop (synCsn (.cv z)) (synCop (synCsn (.cv y)) (.cv x)))
        (synCsymdif (synCins2 (synCsset)) (synCins3 (synCsi (synCcnv R)))))
      (.neg (synWb (.objMem z x) (.classMem (.cv z) (synCec (.cv y) R)))) z p0021
  have p0023 :=
    @gBitri
      (.classMem (synCop (synCsn (.cv y)) (.cv x))
        (synCima (synCsymdif (synCins2 (synCsset)) (synCins3 (synCsi (synCcnv R))))
          (synC1c)))
      (synWex z (.classMem (synCop (synCsn (.cv z)) (synCop (synCsn (.cv y)) (.cv x)))
          (synCsymdif (synCins2 (synCsset)) (synCins3 (synCsi (synCcnv R))))))
      (synWex z (.neg (synWb (.objMem z x) (.classMem (.cv z) (synCec (.cv y) R)))))
      p0002 p0022
  have p0024 :=
    @gNotbii
      (.classMem (synCop (synCsn (.cv y)) (.cv x))
        (synCima (synCsymdif (synCins2 (synCsset)) (synCins3 (synCsi (synCcnv R))))
          (synC1c)))
      (synWex z (.neg (synWb (.objMem z x) (.classMem (.cv z) (synCec (.cv y) R)))))
      p0023
  have p0025 := @gOpex (synCsn (.cv y)) (.cv x) p0004 p0007
  have p0026 :=
    @gElcompl (synCop (synCsn (.cv y)) (.cv x))
      (synCima (synCsymdif (synCins2 (synCsset)) (synCins3 (synCsi (synCcnv R))))
        (synC1c))
      p0025
  have p0027 := @gAlex (synWb (.objMem z x) (.classMem (.cv z) (synCec (.cv y) R))) z
  have p0028 :=
    @gN3bitr4i
      (.neg (.classMem (synCop (synCsn (.cv y)) (.cv x)) (synCima
            (synCsymdif (synCins2 (synCsset)) (synCins3 (synCsi (synCcnv R))))
            (synC1c))))
      (.neg (synWex z (.neg (synWb (.objMem z x) (.classMem (.cv z) (synCec (.cv y) R))))))
      (.classMem (synCop (synCsn (.cv y)) (.cv x)) (synCcompl (synCima
            (synCsymdif (synCins2 (synCsset)) (synCins3 (synCsi (synCcnv R))))
            (synC1c))))
      (.all z (synWb (.objMem z x) (.classMem (.cv z) (synCec (.cv y) R)))) p0024 p0026
      p0027
  have p0029 := @gDfcleq z (.cv x) (synCec (.cv y) R) dv_cache_0010 dv_cache_0011
  have p0030_e01_recanon :
    Nominal.NPrf
      (synWb (.classEq (.cv x) (synCec (.cv y) R))
        (.all z (synWb (.objMem z x) (.classMem (.cv z) (synCec (.cv y) R))))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold synWb synCec synCima synWrex synWex synWa synWbr synCop synCun
          synCnin synWnan synCcompl synCsn
        simp (config :=
          { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_class_cv]
        apply Nominal.RecanonTransportDev.TRecanonWff.neg
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · apply Nominal.RecanonTransportDev.TRecanonWff.imp
          · exact Nominal.RecanonTransportDev.TRecanonWff.same _
          · apply Nominal.RecanonTransportDev.TRecanonWff.all
            apply Nominal.RecanonTransportDev.TRecanonWff.neg
            apply Nominal.RecanonTransportDev.TRecanonWff.imp
            · apply Nominal.RecanonTransportDev.TRecanonWff.imp
              · exact Nominal.RecanonTransportDev.TRecanonWff.classMem_objMem _ _
              · exact Nominal.RecanonTransportDev.TRecanonWff.same _
            · apply Nominal.RecanonTransportDev.TRecanonWff.neg
              apply Nominal.RecanonTransportDev.TRecanonWff.imp
              · exact Nominal.RecanonTransportDev.TRecanonWff.same _
              · exact Nominal.RecanonTransportDev.TRecanonWff.classMem_objMem _ _
        · apply Nominal.RecanonTransportDev.TRecanonWff.neg
          apply Nominal.RecanonTransportDev.TRecanonWff.imp
          · apply Nominal.RecanonTransportDev.TRecanonWff.all
            apply Nominal.RecanonTransportDev.TRecanonWff.neg
            apply Nominal.RecanonTransportDev.TRecanonWff.imp
            · apply Nominal.RecanonTransportDev.TRecanonWff.imp
              · exact Nominal.RecanonTransportDev.TRecanonWff.classMem_objMem _ _
              · exact Nominal.RecanonTransportDev.TRecanonWff.same _
            · apply Nominal.RecanonTransportDev.TRecanonWff.neg
              apply Nominal.RecanonTransportDev.TRecanonWff.imp
              · exact Nominal.RecanonTransportDev.TRecanonWff.same _
              · exact Nominal.RecanonTransportDev.TRecanonWff.classMem_objMem _ _
          · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0029
  have p0030 :=
    @gBitr4i
      (.classMem (synCop (synCsn (.cv y)) (.cv x)) (synCcompl (synCima
            (synCsymdif (synCins2 (synCsset)) (synCins3 (synCsi (synCcnv R))))
            (synC1c))))
      (.all z (synWb (.objMem z x) (.classMem (.cv z) (synCec (.cv y) R))))
      (.classEq (.cv x) (synCec (.cv y) R)) p0028 p0030_e01_recanon
  have p0031 :=
    @gRexbii
      (.classMem (synCop (synCsn (.cv y)) (.cv x)) (synCcompl (synCima
            (synCsymdif (synCins2 (synCsset)) (synCins3 (synCsi (synCcnv R))))
            (synC1c))))
      (.classEq (.cv x) (synCec (.cv y) R)) y A p0030
  have p0032 :=
    @gBitri
      (.classMem (.cv x) (synCima (synCcompl (synCima
              (synCsymdif (synCins2 (synCsset)) (synCins3 (synCsi (synCcnv R))))
              (synC1c))) (synCpw1 A)))
      (synWrex y A (.classMem (synCop (synCsn (.cv y)) (.cv x)) (synCcompl (synCima
              (synCsymdif (synCins2 (synCsset)) (synCins3 (synCsi (synCcnv R))))
              (synC1c)))))
      (synWrex y A (.classEq (.cv x) (synCec (.cv y) R))) p0001 p0031
  have p0033 :=
    @gEqabi (synWrex y A (.classEq (.cv x) (synCec (.cv y) R))) x
      (synCima (synCcompl (synCima
            (synCsymdif (synCins2 (synCsset)) (synCins3 (synCsi (synCcnv R)))) (synC1c)))
        (synCpw1 A))
      dv_cache_0012 p0032
  have p0034 :=
    @gEqtr4i (synCqs A R) (.cab x (synWrex y A (.classEq (.cv x) (synCec (.cv y) R))))
      (synCima (synCcompl (synCima
            (synCsymdif (synCins2 (synCsset)) (synCins3 (synCsi (synCcnv R)))) (synC1c)))
        (synCpw1 A))
      p0000 p0033
  have p0035 := @gSsetex
  have p0036 := @gIns2ex (synCsset) p0035
  have p0037 := @gCnvexg R V
  have p0038 := @gSiexg (synCcnv R) (synCvv)
  have p0039 := @gIns3exg (synCsi (synCcnv R)) (synCvv)
  have p0040 :=
    @gN3syl (.classMem R V) (.classMem (synCcnv R) (synCvv))
      (.classMem (synCsi (synCcnv R)) (synCvv))
      (.classMem (synCins3 (synCsi (synCcnv R))) (synCvv)) p0037 p0038 p0039
  have p0041 :=
    @gSymdifexg (synCins2 (synCsset)) (synCins3 (synCsi (synCcnv R))) (synCvv)
      (synCvv)
  have p0042 :=
    @gSylancr (.classMem R V) (.classMem (synCins2 (synCsset)) (synCvv))
      (.classMem (synCins3 (synCsi (synCcnv R))) (synCvv))
      (.classMem (synCsymdif (synCins2 (synCsset)) (synCins3 (synCsi (synCcnv R))))
        (synCvv))
      p0036 p0040 p0041
  have p0043 := @gN1cex
  have p0044 :=
    @gImaexg (synCsymdif (synCins2 (synCsset)) (synCins3 (synCsi (synCcnv R))))
      (synC1c) (synCvv) (synCvv)
  have p0045 :=
    @gSylancl (.classMem R V)
      (.classMem (synCsymdif (synCins2 (synCsset)) (synCins3 (synCsi (synCcnv R))))
        (synCvv))
      (.classMem (synC1c) (synCvv))
      (.classMem
        (synCima (synCsymdif (synCins2 (synCsset)) (synCins3 (synCsi (synCcnv R))))
          (synC1c)) (synCvv))
      p0042 p0043 p0044
  have p0046 :=
    @gComplexg
      (synCima (synCsymdif (synCins2 (synCsset)) (synCins3 (synCsi (synCcnv R))))
        (synC1c))
      (synCvv)
  have p0047 :=
    @gSyl (.classMem R V)
      (.classMem
        (synCima (synCsymdif (synCins2 (synCsset)) (synCins3 (synCsi (synCcnv R))))
          (synC1c)) (synCvv))
      (.classMem (synCcompl (synCima
            (synCsymdif (synCins2 (synCsset)) (synCins3 (synCsi (synCcnv R)))) (synC1c)))
        (synCvv))
      p0045 p0046
  have p0048 := @gPw1exg A W
  have p0049 :=
    @gImaexg
      (synCcompl
        (synCima (synCsymdif (synCins2 (synCsset)) (synCins3 (synCsi (synCcnv R))))
          (synC1c)))
      (synCpw1 A) (synCvv) (synCvv)
  have p0050 :=
    @gSyl2an (.classMem R V)
      (.classMem (synCcompl (synCima
            (synCsymdif (synCins2 (synCsset)) (synCins3 (synCsi (synCcnv R)))) (synC1c)))
        (synCvv))
      (.classMem (synCpw1 A) (synCvv))
      (.classMem (synCima (synCcompl (synCima
              (synCsymdif (synCins2 (synCsset)) (synCins3 (synCsi (synCcnv R))))
              (synC1c))) (synCpw1 A)) (synCvv))
      (.classMem A W) p0047 p0048 p0049
  have p0051 :=
    @gSyl5eqel (synWa (.classMem R V) (.classMem A W)) (synCqs A R)
      (synCima (synCcompl (synCima
            (synCsymdif (synCins2 (synCsset)) (synCins3 (synCsi (synCcnv R)))) (synC1c)))
        (synCpw1 A))
      (synCvv) p0034 p0050
  exact p0051

/-- Checked nominal proof certificate identified upstream as `g_qsex`. -/
@[expose]
noncomputable def gQsex (A : Class) (R : Class)
    (hyp_qsex_1 : Nominal.NPrf (.classMem R (synCvv)))
    (hyp_qsex_2 : Nominal.NPrf (.classMem A (synCvv))) :
    Nominal.NPrf (.classMem (synCqs A R) (synCvv)) :=
  by
  have p0000 := @gQsexg A R (synCvv) (synCvv)
  have p0001 :=
    @gMp2an (.classMem R (synCvv)) (.classMem A (synCvv))
      (.classMem (synCqs A R) (synCvv)) hyp_qsex_1 hyp_qsex_2 p0000
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_ectocld`. -/
@[expose]
noncomputable def gEctocld (ph : Wff) (ps : Wff) (ch : Wff) (x : Var) (A : Class)
    (B : Class) (R : Class) (S : Class) (dv_A_x : x ∉ A.fv) (dv_B_x : x ∉ B.fv)
    (dv_R_x : x ∉ R.fv) (dv_ch_x : x ∉ ch.fv) (dv_ps_x : x ∉ ps.fv)
    (hyp_ectocl_1 : Nominal.NPrf (.classEq S (synCqs B R)))
    (hyp_ectocl_2 : Nominal.NPrf (.imp (.classEq (synCec (.cv x) R) A) (synWb ph ps)))
    (hyp_ectocld_3 : Nominal.NPrf (.imp (synWa ch (.classMem (.cv x) B)) ph)) :
    Nominal.NPrf (.imp (synWa ch (.classMem A S)) ps) :=
  by
  have dv_cache_0001 : x ∉ (B).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_B_x, not_false_eq_true])
  have dv_cache_0002 : x ∉ (A).fv :=
    by
    clear dv_cache_0001
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_A_x, not_false_eq_true])
  have dv_cache_0003 : x ∉ (R).fv :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_R_x, not_false_eq_true])
  have dv_cache_0004 : x ∉ (ps).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_ps_x, not_false_eq_true])
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
  have p0000 := @gElqsi x B A R dv_cache_0001 dv_cache_0002 dv_cache_0003
  have p0001 :=
    @gEleq2s (synWrex x B (.classEq A (synCec (.cv x) R))) A (synCqs B R) S p0000
      hyp_ectocl_1
  have p0002 := @gEqcoms (synWb ph ps) (synCec (.cv x) R) A hyp_ectocl_2
  have p0003 :=
    @gSyl5ibcom (synWa ch (.classMem (.cv x) B)) ph (.classEq A (synCec (.cv x) R)) ps
      hyp_ectocld_3 p0002
  have p0004 :=
    @gRexlimdva ch (.classEq A (synCec (.cv x) R)) ps x B dv_cache_0004 dv_cache_0005
      p0003
  have p0005 :=
    @gSyl5 (.classMem A S) (synWrex x B (.classEq A (synCec (.cv x) R))) ch ps p0001
      p0004
  have p0006 := @gImp ch (.classMem A S) ps p0005
  exact p0006

/-- Checked nominal proof certificate identified upstream as `g_ectocl`. -/
@[expose]
noncomputable def gEctocl (ph : Wff) (ps : Wff) (x : Var) (A : Class) (B : Class)
    (R : Class) (S : Class) (dv_A_x : x ∉ A.fv) (dv_B_x : x ∉ B.fv) (dv_R_x : x ∉ R.fv)
    (dv_ps_x : x ∉ ps.fv) (hyp_ectocl_1 : Nominal.NPrf (.classEq S (synCqs B R)))
    (hyp_ectocl_2 : Nominal.NPrf (.imp (.classEq (synCec (.cv x) R) A) (synWb ph ps)))
    (hyp_ectocl_3 : Nominal.NPrf (.imp (.classMem (.cv x) B) ph)) :
    Nominal.NPrf (.imp (.classMem A S) ps) :=
  by
  have dv_cache_0001 : x ∉ (A).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_A_x, not_false_eq_true])
  have dv_cache_0002 : x ∉ (B).fv :=
    by
    clear dv_cache_0001
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_B_x, not_false_eq_true])
  have dv_cache_0003 : x ∉ (R).fv :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_R_x, not_false_eq_true])
  have dv_cache_0004 : x ∉ (synWtru).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wtru,
          compact_fv_not_mem_empty, not_false_eq_true])
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
  have p0000 := @gTru
  have p0001 := @gAdantl (.classMem (.cv x) B) ph synWtru hyp_ectocl_3
  have p0002 :=
    @gEctocld ph ps synWtru x A B R S dv_cache_0001 dv_cache_0002 dv_cache_0003
      dv_cache_0004 dv_cache_0005 hyp_ectocl_1 hyp_ectocl_2 p0001
  have p0003 := @gMpan synWtru (.classMem A S) ps p0000 p0002
  exact p0003

/-- Checked nominal proof certificate identified upstream as `g_elqsn0`. -/
@[expose]
noncomputable def gElqsn0 (A : Class) (B : Class) (R : Class) :
    Nominal.NPrf
      (.imp (synWa (.classEq (synCdm R) A) (.classMem B (synCqs A R)))
        (synWne B (synC0))) :=
  by
  let proofSupport : Finset Var := A.fv ∪ B.fv ∪ R.fv
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
  have fresh_x_not_R : x ∉ R.fv := by
    intro h
    exact fresh_x (Finset.mem_union_right _ (h))
  have dv_cache_0001 : x ∉ (B).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_x_not_B, not_false_eq_true])
  have dv_cache_0002 : x ∉ (A).fv :=
    by
    clear dv_cache_0001
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_x_not_A, not_false_eq_true])
  have dv_cache_0003 : x ∉ (R).fv :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_x_not_R, not_false_eq_true])
  have dv_cache_0004 : x ∉ ((Wff.classEq (synCdm R) A)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdm, Finset.mem_union,
          fresh_x_not_R, fresh_x_not_A, or_false, not_false_eq_true])
  have dv_cache_0005 : x ∉ ((synWne B (synC0))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wne,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0, Finset.mem_union,
          fresh_x_not_B, compact_fv_not_mem_empty, or_false, not_false_eq_true])
  have p0000 := @gEqid (synCqs A R)
  have p0001 := @gNeeq1 (synCec (.cv x) R) B (synC0)
  have p0002 := @gEleq2 (synCdm R) A (.cv x)
  have p0003 :=
    @gBiimpar (.classEq (synCdm R) A) (.classMem (.cv x) (synCdm R))
      (.classMem (.cv x) A) p0002
  have p0004 := @gEcdmn0 (.cv x) R
  have p0005 :=
    @gSylib (synWa (.classEq (synCdm R) A) (.classMem (.cv x) A))
      (.classMem (.cv x) (synCdm R)) (synWne (synCec (.cv x) R) (synC0)) p0003 p0004
  have p0006 :=
    @gEctocld (synWne (synCec (.cv x) R) (synC0)) (synWne B (synC0))
      (.classEq (synCdm R) A) x B A R (synCqs A R) dv_cache_0001 dv_cache_0002
      dv_cache_0003 dv_cache_0004 dv_cache_0005 p0000 p0001 p0005
  exact p0006

/-- Checked nominal proof certificate identified upstream as `g_mapexi`. -/
@[expose]
noncomputable def gMapexi (A : Class) (B : Class) (f : Var) (dv_A_f : f ∉ A.fv)
    (dv_B_f : f ∉ B.fv) (hyp_mapexi_1 : Nominal.NPrf (.classMem A (synCvv)))
    (hyp_mapexi_2 : Nominal.NPrf (.classMem B (synCvv))) :
    Nominal.NPrf (.classMem (.cab f (synWf (.cv f) A B)) (synCvv)) :=
  by
  let proofSupport : Finset Var := A.fv ∪ B.fv ∪ ({ f } : Finset Var)
  let x : Var := freshVar proofSupport 0
  have fresh_x : x ∉ proofSupport :=
    by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_x_not_B : x ∉ B.fv := by
    intro h
    exact fresh_x (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_x_ne_f : x ≠ f := by
    intro h
    exact fresh_x (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))
  have dv_cache_0001 : x ∉ ((Class.cv f)).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_x_ne_f, not_false_eq_true])
  have dv_cache_0002 : x ∉ ((synCcnv (synCimage (synC2nd)))).fv :=
    by
    clear dv_cache_0001
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cimage,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c2nd, compact_fv_not_mem_empty,
          not_false_eq_true])
  have dv_cache_0003 : x ∉ ((synCpw B)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw, fresh_x_not_B,
          not_false_eq_true])
  have dv_cache_0004 : x ∉ ((synCrn (.cv f))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_crn,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton, fresh_x_ne_f,
          not_false_eq_true])
  have dv_cache_0005 :
    f ∉
      ((synCin (synCin (synCfuns) (synCima (synCcnv (synCimage (synC1st))) (synCsn A)))
          (synCima (synCcnv (synCimage (synC2nd))) (synCpw B)))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact
      (by
        have compact_fv_not_mem_empty : f ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfuns,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cima,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cimage,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1st,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c2nd,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw, Finset.mem_union, dv_A_f,
          dv_B_f, compact_fv_not_mem_empty, or_false, not_false_eq_true])
  have p0000 :=
    @gElin (.cv f) (synCfuns) (synCima (synCcnv (synCimage (synC1st))) (synCsn A))
  have p0001 := @gVex f
  have p0002 := @gElfuns (.cv f) p0001
  have p0003 := @gElimasn (synCcnv (synCimage (synC1st))) A (.cv f)
  have p0004 := (Nominal.biimpRefl (synWbr A (synCcnv (synCimage (synC1st))) (.cv f)))
  have p0005 := @gBrcnv A (.cv f) (synCimage (synC1st))
  have p0006 := @gBrimage (.cv f) A (synC1st) p0001 hyp_mapexi_1
  have p0007 := @gDfdm4 (.cv f)
  have p0008 := @gEqeq2i (synCdm (.cv f)) (synCima (synC1st) (.cv f)) A p0007
  have p0009 := @gEqcom A (synCdm (.cv f))
  have p0010 :=
    @gN3bitr2i (synWbr (.cv f) (synCimage (synC1st)) A)
      (.classEq A (synCima (synC1st) (.cv f))) (.classEq A (synCdm (.cv f)))
      (.classEq (synCdm (.cv f)) A) p0006 p0008 p0009
  have p0011 :=
    @gBitri (synWbr A (synCcnv (synCimage (synC1st))) (.cv f))
      (synWbr (.cv f) (synCimage (synC1st)) A) (.classEq (synCdm (.cv f)) A) p0005
      p0010
  have p0012 :=
    @gN3bitr2i
      (.classMem (.cv f) (synCima (synCcnv (synCimage (synC1st))) (synCsn A)))
      (.classMem (synCop A (.cv f)) (synCcnv (synCimage (synC1st))))
      (synWbr A (synCcnv (synCimage (synC1st))) (.cv f))
      (.classEq (synCdm (.cv f)) A) p0003 p0004 p0011
  have p0013 :=
    @gAnbi12i (.classMem (.cv f) (synCfuns)) (synWfun (.cv f))
      (.classMem (.cv f) (synCima (synCcnv (synCimage (synC1st))) (synCsn A)))
      (.classEq (synCdm (.cv f)) A) p0002 p0012
  have p0014 :=
    @gBitri
      (.classMem (.cv f)
        (synCin (synCfuns) (synCima (synCcnv (synCimage (synC1st))) (synCsn A))))
      (synWa (.classMem (.cv f) (synCfuns))
        (.classMem (.cv f) (synCima (synCcnv (synCimage (synC1st))) (synCsn A))))
      (synWa (synWfun (.cv f)) (.classEq (synCdm (.cv f)) A)) p0000 p0013
  have p0015 := @gVex x
  have p0016 := @gBrimage (.cv f) (.cv x) (synC2nd) p0001 p0015
  have p0017 := @gBrcnv (.cv x) (.cv f) (synCimage (synC2nd))
  have p0018 := @gDfrn5 (.cv f)
  have p0019 := @gEqeq2i (synCrn (.cv f)) (synCima (synC2nd) (.cv f)) (.cv x) p0018
  have p0020 :=
    @gN3bitr4i (synWbr (.cv f) (synCimage (synC2nd)) (.cv x))
      (.classEq (.cv x) (synCima (synC2nd) (.cv f)))
      (synWbr (.cv x) (synCcnv (synCimage (synC2nd))) (.cv f))
      (.classEq (.cv x) (synCrn (.cv f))) p0016 p0017 p0019
  have p0021 :=
    @gRexbii (synWbr (.cv x) (synCcnv (synCimage (synC2nd))) (.cv f))
      (.classEq (.cv x) (synCrn (.cv f))) x (synCpw B) p0020
  have p0022 :=
    @gElima x (.cv f) (synCcnv (synCimage (synC2nd))) (synCpw B) dv_cache_0001
      dv_cache_0002 dv_cache_0003
  have p0023 := @gRisset x (synCrn (.cv f)) (synCpw B) dv_cache_0004 dv_cache_0003
  have p0024 :=
    @gN3bitr4i
      (synWrex x (synCpw B) (synWbr (.cv x) (synCcnv (synCimage (synC2nd))) (.cv f)))
      (synWrex x (synCpw B) (.classEq (.cv x) (synCrn (.cv f))))
      (.classMem (.cv f) (synCima (synCcnv (synCimage (synC2nd))) (synCpw B)))
      (.classMem (synCrn (.cv f)) (synCpw B)) p0021 p0022 p0023
  have p0025 := @gRnex (.cv f) p0001
  have p0026 := @gElpw (synCrn (.cv f)) B p0025
  have p0027 :=
    @gBitri (.classMem (.cv f) (synCima (synCcnv (synCimage (synC2nd))) (synCpw B)))
      (.classMem (synCrn (.cv f)) (synCpw B)) (synWss (synCrn (.cv f)) B) p0024 p0026
  have p0028 :=
    @gAnbi12i
      (.classMem (.cv f)
        (synCin (synCfuns) (synCima (synCcnv (synCimage (synC1st))) (synCsn A))))
      (synWa (synWfun (.cv f)) (.classEq (synCdm (.cv f)) A))
      (.classMem (.cv f) (synCima (synCcnv (synCimage (synC2nd))) (synCpw B)))
      (synWss (synCrn (.cv f)) B) p0014 p0027
  have p0029 :=
    @gElin (.cv f)
      (synCin (synCfuns) (synCima (synCcnv (synCimage (synC1st))) (synCsn A)))
      (synCima (synCcnv (synCimage (synC2nd))) (synCpw B))
  have p0030 := (Nominal.biimpRefl (synWf (.cv f) A B))
  have p0031 := (Nominal.biimpRefl (synWfn (.cv f) A))
  have p0032 :=
    @gAnbi1i (synWfn (.cv f) A)
      (synWa (synWfun (.cv f)) (.classEq (synCdm (.cv f)) A))
      (synWss (synCrn (.cv f)) B) p0031
  have p0033 :=
    @gBitri (synWf (.cv f) A B)
      (synWa (synWfn (.cv f) A) (synWss (synCrn (.cv f)) B))
      (synWa (synWa (synWfun (.cv f)) (.classEq (synCdm (.cv f)) A))
        (synWss (synCrn (.cv f)) B))
      p0030 p0032
  have p0034 :=
    @gN3bitr4i
      (synWa (.classMem (.cv f)
          (synCin (synCfuns) (synCima (synCcnv (synCimage (synC1st))) (synCsn A))))
        (.classMem (.cv f) (synCima (synCcnv (synCimage (synC2nd))) (synCpw B))))
      (synWa (synWa (synWfun (.cv f)) (.classEq (synCdm (.cv f)) A))
        (synWss (synCrn (.cv f)) B))
      (.classMem (.cv f) (synCin
          (synCin (synCfuns) (synCima (synCcnv (synCimage (synC1st))) (synCsn A)))
          (synCima (synCcnv (synCimage (synC2nd))) (synCpw B))))
      (synWf (.cv f) A B) p0028 p0029 p0033
  have p0035 :=
    @gEqabi (synWf (.cv f) A B) f
      (synCin (synCin (synCfuns) (synCima (synCcnv (synCimage (synC1st))) (synCsn A)))
        (synCima (synCcnv (synCimage (synC2nd))) (synCpw B)))
      dv_cache_0005 p0034
  have p0036 := @gFunsex
  have p0037 := @gN1stex
  have p0038 := @gImageex (synC1st) p0037
  have p0039 := @gCnvex (synCimage (synC1st)) p0038
  have p0040 := @gSnex A
  have p0041 := @gImaex (synCcnv (synCimage (synC1st))) (synCsn A) p0039 p0040
  have p0042 :=
    @gInex (synCfuns) (synCima (synCcnv (synCimage (synC1st))) (synCsn A)) p0036
      p0041
  have p0043 := @gN2ndex
  have p0044 := @gImageex (synC2nd) p0043
  have p0045 := @gCnvex (synCimage (synC2nd)) p0044
  have p0046 := @gPwex B hyp_mapexi_2
  have p0047 := @gImaex (synCcnv (synCimage (synC2nd))) (synCpw B) p0045 p0046
  have p0048 :=
    @gInex
      (synCin (synCfuns) (synCima (synCcnv (synCimage (synC1st))) (synCsn A)))
      (synCima (synCcnv (synCimage (synC2nd))) (synCpw B)) p0042 p0047
  have p0049 :=
    @gEqeltrri
      (synCin (synCin (synCfuns) (synCima (synCcnv (synCimage (synC1st))) (synCsn A)))
        (synCima (synCcnv (synCimage (synC2nd))) (synCpw B)))
      (.cab f (synWf (.cv f) A B)) (synCvv) p0035 p0048
  exact p0049

/-- Checked nominal proof certificate identified upstream as `g_mapex`. -/
@[expose]
noncomputable def gMapex (A : Class) (B : Class) (C : Class) (D : Class) (f : Var)
    (dv_A_f : f ∉ A.fv) (dv_B_f : f ∉ B.fv) :
    Nominal.NPrf
      (.imp (synWa (.classMem A C) (.classMem B D))
        (.classMem (.cab f (synWf (.cv f) A B)) (synCvv))) :=
  by
  let proofSupport : Finset Var := A.fv ∪ B.fv ∪ C.fv ∪ D.fv ∪ ({ f } : Finset Var)
  let a : Var := freshVar proofSupport 0
  let b : Var := freshVar proofSupport 1
  have fresh_a : a ∉ proofSupport :=
    by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_a_not_A : a ∉ A.fv := by
    intro h
    exact
      fresh_a
        (Finset.mem_union_left _ (Finset.mem_union_left _
            (Finset.mem_union_left _ (Finset.mem_union_left _ (h)))))
  have fresh_a_ne_f : a ≠ f := by
    intro h
    exact fresh_a (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))
  have fresh_f_ne_a : f ≠ a := Ne.symm fresh_a_ne_f
  have fresh_b : b ∉ proofSupport :=
    by
    change freshVar proofSupport 1 ∉ proofSupport
    exact freshVar_not_mem proofSupport 1
  have fresh_b_not_A : b ∉ A.fv := by
    intro h
    exact
      fresh_b
        (Finset.mem_union_left _ (Finset.mem_union_left _
            (Finset.mem_union_left _ (Finset.mem_union_left _ (h)))))
  have fresh_b_not_B : b ∉ B.fv := by
    intro h
    exact
      fresh_b
        (Finset.mem_union_left _ (Finset.mem_union_left _
            (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))))
  have fresh_b_ne_f : b ≠ f := by
    intro h
    exact fresh_b (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))
  have fresh_f_ne_b : f ≠ b := Ne.symm fresh_b_ne_f
  have fresh_a_ne_b : a ≠ b :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have dv_cache_0001 : f ∉ ((Wff.classEq (.cv a) A)).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : f ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, fresh_f_ne_a, dv_A_f, or_false, not_false_eq_true])
  have dv_cache_0002 : f ∉ ((Wff.classEq (.cv b) B)).fv :=
    by
    clear dv_cache_0001
    exact
      (by
        have compact_fv_not_mem_empty : f ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, fresh_f_ne_b, dv_B_f, or_false, not_false_eq_true])
  have dv_cache_0003 : f ∉ ((Class.cv a)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact
      (by
        have compact_fv_not_mem_empty : f ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_f_ne_a, not_false_eq_true])
  have dv_cache_0004 : f ∉ ((Class.cv b)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact
      (by
        have compact_fv_not_mem_empty : f ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_f_ne_b, not_false_eq_true])
  have dv_cache_0005 : a ∉ (A).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact
      (by
        have compact_fv_not_mem_empty : a ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_a_not_A, not_false_eq_true])
  have dv_cache_0006 : b ∉ (A).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact
      (by
        have compact_fv_not_mem_empty : b ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_b_not_A, not_false_eq_true])
  have dv_cache_0007 : b ∉ (B).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006
    exact
      (by
        have compact_fv_not_mem_empty : b ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_b_not_B, not_false_eq_true])
  have dv_cache_0008 : b ∉ ((Wff.classMem (.cab f (synWf (.cv f) A B)) (synCvv))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007
    exact
      (by
        have compact_fv_not_mem_empty : b ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CoreFVSimp.fv_class_cab,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wf,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv, Finset.mem_union,
          Finset.mem_erase, Finset.mem_singleton, fresh_b_not_A, fresh_b_not_B,
          fresh_b_ne_f, compact_fv_not_mem_empty, or_false, and_false, not_false_eq_true])
  have dv_cache_0009 :
    a ∉ ((Wff.classMem (.cab f (synWf (.cv f) A (.cv b))) (synCvv))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008
    exact
      (by
        have compact_fv_not_mem_empty : a ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CoreFVSimp.fv_class_cab,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wf,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv, Finset.mem_union,
          Finset.mem_erase, Finset.mem_singleton, fresh_a_not_A, fresh_a_ne_b,
          fresh_a_ne_f, compact_fv_not_mem_empty, or_false, and_false, not_false_eq_true])
  have p0000 := @gFeq2 (.cv a) A (.cv b) (.cv f)
  have p0001 :=
    @gAbbidv (.classEq (.cv a) A) (synWf (.cv f) (.cv a) (.cv b))
      (synWf (.cv f) A (.cv b)) f dv_cache_0001 p0000
  have p0002 :=
    @gEleq1d (.classEq (.cv a) A) (.cab f (synWf (.cv f) (.cv a) (.cv b)))
      (.cab f (synWf (.cv f) A (.cv b))) (synCvv) p0001
  have p0003 := @gFeq3 (.cv b) B A (.cv f)
  have p0004 :=
    @gAbbidv (.classEq (.cv b) B) (synWf (.cv f) A (.cv b)) (synWf (.cv f) A B) f
      dv_cache_0002 p0003
  have p0005 :=
    @gEleq1d (.classEq (.cv b) B) (.cab f (synWf (.cv f) A (.cv b)))
      (.cab f (synWf (.cv f) A B)) (synCvv) p0004
  have p0006 := @gVex a
  have p0007 := @gVex b
  have p0008 := @gMapexi (.cv a) (.cv b) f dv_cache_0003 dv_cache_0004 p0006 p0007
  have p0009 :=
    @gVtocl2g (.classMem (.cab f (synWf (.cv f) (.cv a) (.cv b))) (synCvv))
      (.classMem (.cab f (synWf (.cv f) A (.cv b))) (synCvv))
      (.classMem (.cab f (synWf (.cv f) A B)) (synCvv)) a b A B C D dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 p0002 p0005 p0008
  exact p0009


end NFChoice.DirectNominalPrf.WPPReplay

end

/-! Certificates from `NominalWPPReplayChunk013Compact001Part031`. -/


section

namespace NFChoice.DirectNominalPrf.WPPReplay

open scoped Fol
open NFChoice.Foundation
open NFChoice.SemanticCore
open NFChoice.ReplaySupport
open NFChoice.Compiler.CompactSourceSyntax

/-- Checked nominal proof certificate identified upstream as `g_mapvalg`. -/
@[expose]
noncomputable def gMapvalg (A : Class) (B : Class) (C : Class) (D : Class) (f : Var)
    (dv_A_f : f ∉ A.fv) (dv_B_f : f ∉ B.fv) :
    Nominal.NPrf
      (.imp (synWa (.classMem A C) (.classMem B D))
        (.classEq (synCo A (synCmap) B) (.cab f (synWf (.cv f) B A)))) :=
  by
  let proofSupport : Finset Var := A.fv ∪ B.fv ∪ C.fv ∪ D.fv ∪ ({ f } : Finset Var)
  let x : Var := freshVar proofSupport 0
  let y : Var := freshVar proofSupport 1
  have fresh_x : x ∉ proofSupport :=
    by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_x_not_A : x ∉ A.fv := by
    intro h
    exact
      fresh_x
        (Finset.mem_union_left _ (Finset.mem_union_left _
            (Finset.mem_union_left _ (Finset.mem_union_left _ (h)))))
  have fresh_x_not_B : x ∉ B.fv := by
    intro h
    exact
      fresh_x
        (Finset.mem_union_left _ (Finset.mem_union_left _
            (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))))
  have fresh_x_ne_f : x ≠ f := by
    intro h
    exact fresh_x (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))
  have fresh_f_ne_x : f ≠ x := Ne.symm fresh_x_ne_f
  have fresh_y : y ∉ proofSupport :=
    by
    change freshVar proofSupport 1 ∉ proofSupport
    exact freshVar_not_mem proofSupport 1
  have fresh_y_not_A : y ∉ A.fv := by
    intro h
    exact
      fresh_y
        (Finset.mem_union_left _ (Finset.mem_union_left _
            (Finset.mem_union_left _ (Finset.mem_union_left _ (h)))))
  have fresh_y_not_B : y ∉ B.fv := by
    intro h
    exact
      fresh_y
        (Finset.mem_union_left _ (Finset.mem_union_left _
            (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))))
  have fresh_y_ne_f : y ≠ f := by
    intro h
    exact fresh_y (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))
  have fresh_f_ne_y : f ≠ y := Ne.symm fresh_y_ne_f
  have fresh_x_ne_y : x ≠ y :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have dv_cache_0001 : f ∉ (B).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : f ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_B_f, not_false_eq_true])
  have dv_cache_0002 : f ∉ (A).fv :=
    by
    clear dv_cache_0001
    exact
      (by
        have compact_fv_not_mem_empty : f ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_A_f, not_false_eq_true])
  have dv_cache_0003 : f ∉ ((Wff.classEq (.cv x) A)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact
      (by
        have compact_fv_not_mem_empty : f ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, fresh_f_ne_x, dv_A_f, or_false, not_false_eq_true])
  have dv_cache_0004 : f ∉ ((Wff.classEq (.cv y) B)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact
      (by
        have compact_fv_not_mem_empty : f ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, fresh_f_ne_y, dv_B_f, or_false, not_false_eq_true])
  have dv_cache_0005 : f ≠ x :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact (show f ≠ x from (by exact fresh_f_ne_x))
  have dv_cache_0006 : f ≠ y :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact (show f ≠ y from (by exact fresh_f_ne_y))
  have dv_cache_0007 : x ≠ y :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006
    exact (show x ≠ y from (by exact fresh_x_ne_y))
  have dv_cache_0008 : x ∉ (A).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_x_not_A, not_false_eq_true])
  have dv_cache_0009 : y ∉ (A).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_y_not_A, not_false_eq_true])
  have dv_cache_0010 : x ∉ (B).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_x_not_B, not_false_eq_true])
  have dv_cache_0011 : y ∉ (B).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_y_not_B, not_false_eq_true])
  have dv_cache_0012 : x ∉ ((synCvv)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv,
          compact_fv_not_mem_empty, not_false_eq_true])
  have dv_cache_0013 : y ∉ ((synCvv)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv,
          compact_fv_not_mem_empty, not_false_eq_true])
  have dv_cache_0014 : x ∉ ((Class.cab f (synWf (.cv f) (.cv y) A))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cab,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wf,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase,
          Finset.mem_singleton, fresh_x_ne_y, fresh_x_not_A, fresh_x_ne_f, or_false,
          and_false, not_false_eq_true])
  have dv_cache_0015 : x ∉ ((Class.cab f (synWf (.cv f) B A))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cab,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wf,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase,
          Finset.mem_singleton, fresh_x_not_B, fresh_x_not_A, fresh_x_ne_f, or_false,
          and_false, not_false_eq_true])
  have dv_cache_0016 : y ∉ ((Class.cab f (synWf (.cv f) B A))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cab,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wf,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase,
          Finset.mem_singleton, fresh_y_not_B, fresh_y_not_A, fresh_y_ne_f, or_false,
          and_false, not_false_eq_true])
  have p0000 := @gMapex B A D C f dv_cache_0001 dv_cache_0002
  have p0001 :=
    @gAncoms (.classMem B D) (.classMem A C)
      (.classMem (.cab f (synWf (.cv f) B A)) (synCvv)) p0000
  have p0002 := @gElex A C
  have p0003 := @gElex B D
  have p0004 := @gFeq3 (.cv x) A (.cv y) (.cv f)
  have p0005 :=
    @gAbbidv (.classEq (.cv x) A) (synWf (.cv f) (.cv y) (.cv x))
      (synWf (.cv f) (.cv y) A) f dv_cache_0003 p0004
  have p0006 := @gFeq2 (.cv y) B A (.cv f)
  have p0007 :=
    @gAbbidv (.classEq (.cv y) B) (synWf (.cv f) (.cv y) A) (synWf (.cv f) B A) f
      dv_cache_0004 p0006
  have p0008 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominalDfMap x y f
      dv_cache_0005 dv_cache_0006 dv_cache_0007
  have p0009 :=
    @gOvmpt2g x y A B (synCvv) (synCvv) (.cab f (synWf (.cv f) (.cv y) (.cv x)))
      (.cab f (synWf (.cv f) B A)) (synCmap) (.cab f (synWf (.cv f) (.cv y) A))
      (synCvv) dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012
      dv_cache_0013 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016
      dv_cache_0007 p0005 p0007 p0008
  have p0010 :=
    @gN3expia (.classMem A (synCvv)) (.classMem B (synCvv))
      (.classMem (.cab f (synWf (.cv f) B A)) (synCvv))
      (.classEq (synCo A (synCmap) B) (.cab f (synWf (.cv f) B A))) p0009
  have p0011 :=
    @gSyl2an (.classMem A C) (.classMem A (synCvv)) (.classMem B (synCvv))
      (.imp (.classMem (.cab f (synWf (.cv f) B A)) (synCvv))
        (.classEq (synCo A (synCmap) B) (.cab f (synWf (.cv f) B A))))
      (.classMem B D) p0002 p0003 p0010
  have p0012 :=
    @gMpd (synWa (.classMem A C) (.classMem B D))
      (.classMem (.cab f (synWf (.cv f) B A)) (synCvv))
      (.classEq (synCo A (synCmap) B) (.cab f (synWf (.cv f) B A))) p0001 p0011
  exact p0012

/-- Checked nominal proof certificate identified upstream as `g_elmapg`. -/
@[expose]
noncomputable def gElmapg (A : Class) (B : Class) (C : Class) (V : Class) (W : Class)
    (X : Class) :
    Nominal.NPrf
      (.imp (synW3a (.classMem A V) (.classMem B W) (.classMem C X))
        (synWb (.classMem C (synCo A (synCmap) B)) (synWf C B A))) :=
  by
  let proofSupport : Finset Var := A.fv ∪ B.fv ∪ C.fv ∪ V.fv ∪ W.fv ∪ X.fv
  let g : Var := freshVar proofSupport 0
  have fresh_g : g ∉ proofSupport :=
    by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_g_not_A : g ∉ A.fv := by
    intro h
    exact
      fresh_g
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _
              (Finset.mem_union_left _ (Finset.mem_union_left _ (h))))))
  have fresh_g_not_B : g ∉ B.fv := by
    intro h
    exact
      fresh_g
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _
              (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))))
  have fresh_g_not_C : g ∉ C.fv := by
    intro h
    exact
      fresh_g
        (Finset.mem_union_left _ (Finset.mem_union_left _
            (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))))
  have dv_cache_0001 : g ∉ (A).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : g ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_g_not_A, not_false_eq_true])
  have dv_cache_0002 : g ∉ (B).fv :=
    by
    clear dv_cache_0001
    exact
      (by
        have compact_fv_not_mem_empty : g ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_g_not_B, not_false_eq_true])
  have dv_cache_0003 : g ∉ (C).fv :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact
      (by
        have compact_fv_not_mem_empty : g ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_g_not_C, not_false_eq_true])
  have dv_cache_0004 : g ∉ ((synWf C B A)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact
      (by
        have compact_fv_not_mem_empty : g ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wf, Finset.mem_union,
          fresh_g_not_B, fresh_g_not_A, fresh_g_not_C, or_false, not_false_eq_true])
  have p0000 := @gMapvalg A B V W g dv_cache_0001 dv_cache_0002
  have p0001 :=
    @gEleq2d (synWa (.classMem A V) (.classMem B W)) (synCo A (synCmap) B)
      (.cab g (synWf (.cv g) B A)) C p0000
  have p0002 :=
    @gN3adant3 (.classMem A V) (.classMem B W)
      (synWb (.classMem C (synCo A (synCmap) B)) (.classMem C (.cab g (synWf (.cv g) B A))))
      (.classMem C X) p0001
  have p0003 := @gFeq1 B A (.cv g) C
  have p0004 :=
    @gElabg (synWf (.cv g) B A) (synWf C B A) g C X dv_cache_0003 dv_cache_0004 p0003
  have p0005 :=
    @gN3ad2ant3 (.classMem C X) (.classMem A V)
      (synWb (.classMem C (.cab g (synWf (.cv g) B A))) (synWf C B A)) (.classMem B W)
      p0004
  have p0006 :=
    @gBitrd (synW3a (.classMem A V) (.classMem B W) (.classMem C X))
      (.classMem C (synCo A (synCmap) B)) (.classMem C (.cab g (synWf (.cv g) B A)))
      (synWf C B A) p0002 p0005
  exact p0006

/-- Checked nominal proof certificate identified upstream as `g_elmapi`. -/
@[expose]
noncomputable def gElmapi (A : Class) (B : Class) (C : Class) :
    Nominal.NPrf (.imp (.classMem A (synCo B (synCmap) C)) (synWf A C B)) :=
  by
  have p0000 := @gElovex1 A B C (synCmap)
  have p0001 := @gElovex2 A B C (synCmap)
  have p0002 := @gId (.classMem A (synCo B (synCmap) C))
  have p0003 := @gElmapg B C A (synCvv) (synCvv) (synCo B (synCmap) C)
  have p0004 :=
    @gSyl3anc (.classMem A (synCo B (synCmap) C)) (.classMem B (synCvv))
      (.classMem C (synCvv)) (.classMem A (synCo B (synCmap) C))
      (synWb (.classMem A (synCo B (synCmap) C)) (synWf A C B)) p0000 p0001 p0002
      p0003
  have p0005 := @gIbi (.classMem A (synCo B (synCmap) C)) (synWf A C B) p0004
  exact p0005

/-- Checked nominal proof certificate identified upstream as `g_bren`. -/
@[expose]
noncomputable def gBren (A : Class) (B : Class) (f : Var) (dv_A_f : f ∉ A.fv)
    (dv_B_f : f ∉ B.fv) :
    Nominal.NPrf (synWb (synWbr A (synCen) B) (synWex f (synWf1o (.cv f) A B))) :=
  by
  let proofSupport : Finset Var := A.fv ∪ B.fv ∪ ({ f } : Finset Var)
  let x : Var := freshVar proofSupport 0
  let y : Var := freshVar proofSupport 1
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
  have fresh_x_ne_f : x ≠ f := by
    intro h
    exact fresh_x (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))
  have fresh_f_ne_x : f ≠ x := Ne.symm fresh_x_ne_f
  have fresh_y : y ∉ proofSupport :=
    by
    change freshVar proofSupport 1 ∉ proofSupport
    exact freshVar_not_mem proofSupport 1
  have fresh_y_not_A : y ∉ A.fv := by
    intro h
    exact fresh_y (Finset.mem_union_left _ (Finset.mem_union_left _ (h)))
  have fresh_y_not_B : y ∉ B.fv := by
    intro h
    exact fresh_y (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_y_ne_f : y ≠ f := by
    intro h
    exact fresh_y (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))
  have fresh_f_ne_y : f ≠ y := Ne.symm fresh_y_ne_f
  have fresh_x_ne_y : x ≠ y :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have dv_cache_0001 :
    f ∉ ((synWa (.classMem A (synCvv)) (.classMem B (synCvv)))).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : f ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv, Finset.mem_union, dv_A_f,
          dv_B_f, compact_fv_not_mem_empty, or_false, not_false_eq_true])
  have dv_cache_0002 : f ∉ ((Wff.classEq (.cv x) A)).fv :=
    by
    clear dv_cache_0001
    exact
      (by
        have compact_fv_not_mem_empty : f ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, fresh_f_ne_x, dv_A_f, or_false, not_false_eq_true])
  have dv_cache_0003 : f ∉ ((Wff.classEq (.cv y) B)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact
      (by
        have compact_fv_not_mem_empty : f ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, fresh_f_ne_y, dv_B_f, or_false, not_false_eq_true])
  have dv_cache_0004 : f ≠ x :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact (show f ≠ x from (by exact fresh_f_ne_x))
  have dv_cache_0005 : f ≠ y :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact (show f ≠ y from (by exact fresh_f_ne_y))
  have dv_cache_0006 : x ≠ y :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact (show x ≠ y from (by exact fresh_x_ne_y))
  have dv_cache_0007 : x ∉ (A).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_x_not_A, not_false_eq_true])
  have dv_cache_0008 : y ∉ (A).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_y_not_A, not_false_eq_true])
  have dv_cache_0009 : x ∉ (B).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_x_not_B, not_false_eq_true])
  have dv_cache_0010 : y ∉ (B).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_y_not_B, not_false_eq_true])
  have dv_cache_0011 : x ∉ ((synWex f (synWf1o (.cv f) A B))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wex,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wf1o,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase,
          Finset.mem_singleton, fresh_x_not_A, fresh_x_not_B, fresh_x_ne_f, or_false,
          and_false, not_false_eq_true])
  have dv_cache_0012 : y ∉ ((synWex f (synWf1o (.cv f) A B))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wex,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wf1o,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase,
          Finset.mem_singleton, fresh_y_not_A, fresh_y_not_B, fresh_y_ne_f, or_false,
          and_false, not_false_eq_true])
  have p0000 := @gBrex A B (synCen)
  have p0001 := @gVex f
  have p0002 := @gDmex (.cv f) p0001
  have p0003 := @gRnex (.cv f) p0001
  have p0004 :=
    @gPm32i (.classMem (synCdm (.cv f)) (synCvv))
      (.classMem (synCrn (.cv f)) (synCvv)) p0002 p0003
  have p0005 := @gF1odm A B (.cv f)
  have p0006 := @gEleq1d (synWf1o (.cv f) A B) (synCdm (.cv f)) A (synCvv) p0005
  have p0007 := @gF1ofo A B (.cv f)
  have p0008 := @gForn A B (.cv f)
  have p0009 :=
    @gSyl (synWf1o (.cv f) A B) (synWfo (.cv f) A B) (.classEq (synCrn (.cv f)) B)
      p0007 p0008
  have p0010 := @gEleq1d (synWf1o (.cv f) A B) (synCrn (.cv f)) B (synCvv) p0009
  have p0011 :=
    @gAnbi12d (synWf1o (.cv f) A B) (.classMem (synCdm (.cv f)) (synCvv))
      (.classMem A (synCvv)) (.classMem (synCrn (.cv f)) (synCvv))
      (.classMem B (synCvv)) p0006 p0010
  have p0012 :=
    @gMpbii (synWf1o (.cv f) A B)
      (synWa (.classMem (synCdm (.cv f)) (synCvv)) (.classMem (synCrn (.cv f)) (synCvv)))
      (synWa (.classMem A (synCvv)) (.classMem B (synCvv))) p0004 p0011
  have p0013 :=
    @gExlimiv (synWf1o (.cv f) A B)
      (synWa (.classMem A (synCvv)) (.classMem B (synCvv))) f dv_cache_0001 p0012
  have p0014 := @gF1oeq2 (.cv x) A (.cv y) (.cv f)
  have p0015 :=
    @gExbidv (.classEq (.cv x) A) (synWf1o (.cv f) (.cv x) (.cv y))
      (synWf1o (.cv f) A (.cv y)) f dv_cache_0002 p0014
  have p0016 := @gF1oeq3 (.cv y) B A (.cv f)
  have p0017 :=
    @gExbidv (.classEq (.cv y) B) (synWf1o (.cv f) A (.cv y)) (synWf1o (.cv f) A B) f
      dv_cache_0003 p0016
  have p0018 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominalDfEn x y f
      dv_cache_0004 dv_cache_0005 dv_cache_0006
  have p0019 :=
    @gBrabg (synWex f (synWf1o (.cv f) (.cv x) (.cv y)))
      (synWex f (synWf1o (.cv f) A (.cv y))) (synWex f (synWf1o (.cv f) A B)) x y A B
      (synCvv) (synCvv) (synCen) dv_cache_0007 dv_cache_0008 dv_cache_0009
      dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0006 p0015 p0017 p0018
  have p0020 :=
    @gPm521nii (synWbr A (synCen) B)
      (synWa (.classMem A (synCvv)) (.classMem B (synCvv)))
      (synWex f (synWf1o (.cv f) A B)) p0000 p0013 p0019
  exact p0020

/-- Checked nominal proof certificate identified upstream as `g_enex`. -/
@[expose]
noncomputable def gEnex : Nominal.NPrf (.classMem (synCen) (synCvv)) :=
  by
  let proofSupport : Finset Var := (∅ : Finset Var)
  let x : Var := freshVar proofSupport 0
  let y : Var := freshVar proofSupport 1
  let f : Var := freshVar proofSupport 2
  let g : Var := freshVar proofSupport 3
  have fresh_x_ne_y : x ≠ y :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have fresh_x_ne_f : x ≠ f :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 2
    exact freshVar_injective proofSupport (i := 0) (j := 2) (by decide)
  have fresh_f_ne_x : f ≠ x := Ne.symm fresh_x_ne_f
  have fresh_y_ne_f : y ≠ f :=
    by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 2
    exact freshVar_injective proofSupport (i := 1) (j := 2) (by decide)
  have fresh_f_ne_y : f ≠ y := Ne.symm fresh_y_ne_f
  have fresh_y_ne_g : y ≠ g :=
    by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 3
    exact freshVar_injective proofSupport (i := 1) (j := 3) (by decide)
  have fresh_g_ne_y : g ≠ y := Ne.symm fresh_y_ne_g
  have fresh_f_ne_g : f ≠ g :=
    by
    change freshVar proofSupport 2 ≠ freshVar proofSupport 3
    exact freshVar_injective proofSupport (i := 2) (j := 3) (by decide)
  have fresh_g_ne_f : g ≠ f := Ne.symm fresh_f_ne_g
  have dv_cache_0001 : f ≠ x := by exact (show f ≠ x from (by exact fresh_f_ne_x))
  have dv_cache_0002 : f ≠ y := by
    clear dv_cache_0001
    exact (show f ≠ y from (by exact fresh_f_ne_y))
  have dv_cache_0003 : x ≠ y :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact (show x ≠ y from (by exact fresh_x_ne_y))
  have dv_cache_0004 : f ∉ ((synCop (.cv x) (.cv y))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact
      (by
        have compact_fv_not_mem_empty : f ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cop,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, fresh_f_ne_x, fresh_f_ne_y, or_false, not_false_eq_true])
  have dv_cache_0005 :
    f ∉
      ((synCtxp (synCfns)
          (synCrn (synCtxp (synCcnv (synCimage (synCswap))) (synCfns))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact
      (by
        have compact_fv_not_mem_empty : f ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ctxp,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfns,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_crn,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cimage,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cswap, Finset.mem_union,
          compact_fv_not_mem_empty, or_false, not_false_eq_true])
  have dv_cache_0006 : g ∉ ((synCop (.cv f) (.cv y))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact
      (by
        have compact_fv_not_mem_empty : g ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cop,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, fresh_g_ne_f, fresh_g_ne_y, or_false, not_false_eq_true])
  have dv_cache_0007 :
    g ∉ ((synCtxp (synCcnv (synCimage (synCswap))) (synCfns))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006
    exact
      (by
        have compact_fv_not_mem_empty : g ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ctxp,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cimage,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cswap,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfns, Finset.mem_union,
          compact_fv_not_mem_empty, or_false, not_false_eq_true])
  have dv_cache_0008 : g ∉ ((synCcnv (.cv f))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007
    exact
      (by
        have compact_fv_not_mem_empty : g ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton, fresh_g_ne_f,
          not_false_eq_true])
  have dv_cache_0009 : g ∉ ((synWfn (synCcnv (.cv f)) (.cv y))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008
    exact
      (by
        have compact_fv_not_mem_empty : g ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wfn,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, fresh_g_ne_f, fresh_g_ne_y, or_false, not_false_eq_true])
  have dv_cache_0010 :
    x ∉
      ((synCrn (synCtxp (synCfns)
            (synCrn (synCtxp (synCcnv (synCimage (synCswap))) (synCfns)))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_crn,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ctxp,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfns,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cimage,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cswap, Finset.mem_union,
          compact_fv_not_mem_empty, or_false, not_false_eq_true])
  have dv_cache_0011 :
    y ∉
      ((synCrn (synCtxp (synCfns)
            (synCrn (synCtxp (synCcnv (synCimage (synCswap))) (synCfns)))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_crn,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ctxp,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfns,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cimage,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cswap, Finset.mem_union,
          compact_fv_not_mem_empty, or_false, not_false_eq_true])
  have p0000 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominalDfEn x y f
      dv_cache_0001 dv_cache_0002 dv_cache_0003
  have p0001 :=
    @gElrn2 f (synCop (.cv x) (.cv y))
      (synCtxp (synCfns) (synCrn (synCtxp (synCcnv (synCimage (synCswap))) (synCfns))))
      dv_cache_0004 dv_cache_0005
  have p0002 := (Nominal.biimpRefl (synWbr (.cv f) (synCfns) (.cv x)))
  have p0003 := @gVex f
  have p0004 := @gBrfns (.cv x) (.cv f) p0003
  have p0005 :=
    @gBitr3i (.classMem (synCop (.cv f) (.cv x)) (synCfns))
      (synWbr (.cv f) (synCfns) (.cv x)) (synWfn (.cv f) (.cv x)) p0002 p0004
  have p0006 :=
    @gElrn2 g (synCop (.cv f) (.cv y))
      (synCtxp (synCcnv (synCimage (synCswap))) (synCfns)) dv_cache_0006
      dv_cache_0007
  have p0007 :=
    @gOteltxp (.cv g) (.cv f) (.cv y) (synCcnv (synCimage (synCswap))) (synCfns)
  have p0008 := @gOpelcnv (.cv g) (.cv f) (synCimage (synCswap))
  have p0009 := @gDfcnv2 (.cv f)
  have p0010 := @gEqeq2i (synCcnv (.cv f)) (synCima (synCswap) (.cv f)) (.cv g) p0009
  have p0011 := @gVex g
  have p0012 := @gBrimage (.cv f) (.cv g) (synCswap) p0003 p0011
  have p0013 := (Nominal.biimpRefl (synWbr (.cv f) (synCimage (synCswap)) (.cv g)))
  have p0014 :=
    @gN3bitr2ri (.classEq (.cv g) (synCcnv (.cv f)))
      (.classEq (.cv g) (synCima (synCswap) (.cv f)))
      (synWbr (.cv f) (synCimage (synCswap)) (.cv g))
      (.classMem (synCop (.cv f) (.cv g)) (synCimage (synCswap))) p0010 p0012 p0013
  have p0015 :=
    @gBitri (.classMem (synCop (.cv g) (.cv f)) (synCcnv (synCimage (synCswap))))
      (.classMem (synCop (.cv f) (.cv g)) (synCimage (synCswap)))
      (.classEq (.cv g) (synCcnv (.cv f))) p0008 p0014
  have p0016 := (Nominal.biimpRefl (synWbr (.cv g) (synCfns) (.cv y)))
  have p0017 := @gBrfns (.cv y) (.cv g) p0011
  have p0018 :=
    @gBitr3i (.classMem (synCop (.cv g) (.cv y)) (synCfns))
      (synWbr (.cv g) (synCfns) (.cv y)) (synWfn (.cv g) (.cv y)) p0016 p0017
  have p0019 :=
    @gAnbi12i (.classMem (synCop (.cv g) (.cv f)) (synCcnv (synCimage (synCswap))))
      (.classEq (.cv g) (synCcnv (.cv f)))
      (.classMem (synCop (.cv g) (.cv y)) (synCfns)) (synWfn (.cv g) (.cv y)) p0015
      p0018
  have p0020 :=
    @gBitri
      (.classMem (synCop (.cv g) (synCop (.cv f) (.cv y)))
        (synCtxp (synCcnv (synCimage (synCswap))) (synCfns)))
      (synWa (.classMem (synCop (.cv g) (.cv f)) (synCcnv (synCimage (synCswap))))
        (.classMem (synCop (.cv g) (.cv y)) (synCfns)))
      (synWa (.classEq (.cv g) (synCcnv (.cv f))) (synWfn (.cv g) (.cv y))) p0007 p0019
  have p0021 :=
    @gExbii
      (.classMem (synCop (.cv g) (synCop (.cv f) (.cv y)))
        (synCtxp (synCcnv (synCimage (synCswap))) (synCfns)))
      (synWa (.classEq (.cv g) (synCcnv (.cv f))) (synWfn (.cv g) (.cv y))) g p0020
  have p0022 := @gCnvex (.cv f) p0003
  have p0023 := @gFneq1 (.cv y) (.cv g) (synCcnv (.cv f))
  have p0024 :=
    @gCeqsexv (synWfn (.cv g) (.cv y)) (synWfn (synCcnv (.cv f)) (.cv y)) g
      (synCcnv (.cv f)) dv_cache_0008 dv_cache_0009 p0022 p0023
  have p0025 :=
    @gBitri
      (synWex g (.classMem (synCop (.cv g) (synCop (.cv f) (.cv y)))
          (synCtxp (synCcnv (synCimage (synCswap))) (synCfns))))
      (synWex g (synWa (.classEq (.cv g) (synCcnv (.cv f))) (synWfn (.cv g) (.cv y))))
      (synWfn (synCcnv (.cv f)) (.cv y)) p0021 p0024
  have p0026 :=
    @gBitri
      (.classMem (synCop (.cv f) (.cv y))
        (synCrn (synCtxp (synCcnv (synCimage (synCswap))) (synCfns))))
      (synWex g (.classMem (synCop (.cv g) (synCop (.cv f) (.cv y)))
          (synCtxp (synCcnv (synCimage (synCswap))) (synCfns))))
      (synWfn (synCcnv (.cv f)) (.cv y)) p0006 p0025
  have p0027 :=
    @gAnbi12i (.classMem (synCop (.cv f) (.cv x)) (synCfns)) (synWfn (.cv f) (.cv x))
      (.classMem (synCop (.cv f) (.cv y))
        (synCrn (synCtxp (synCcnv (synCimage (synCswap))) (synCfns))))
      (synWfn (synCcnv (.cv f)) (.cv y)) p0005 p0026
  have p0028 :=
    @gOteltxp (.cv f) (.cv x) (.cv y) (synCfns)
      (synCrn (synCtxp (synCcnv (synCimage (synCswap))) (synCfns)))
  have p0029 := @gDff1o4 (.cv x) (.cv y) (.cv f)
  have p0030 :=
    @gN3bitr4i
      (synWa (.classMem (synCop (.cv f) (.cv x)) (synCfns))
        (.classMem (synCop (.cv f) (.cv y))
          (synCrn (synCtxp (synCcnv (synCimage (synCswap))) (synCfns)))))
      (synWa (synWfn (.cv f) (.cv x)) (synWfn (synCcnv (.cv f)) (.cv y)))
      (.classMem (synCop (.cv f) (synCop (.cv x) (.cv y))) (synCtxp (synCfns)
          (synCrn (synCtxp (synCcnv (synCimage (synCswap))) (synCfns)))))
      (synWf1o (.cv f) (.cv x) (.cv y)) p0027 p0028 p0029
  have p0031 :=
    @gExbii
      (.classMem (synCop (.cv f) (synCop (.cv x) (.cv y))) (synCtxp (synCfns)
          (synCrn (synCtxp (synCcnv (synCimage (synCswap))) (synCfns)))))
      (synWf1o (.cv f) (.cv x) (.cv y)) f p0030
  have p0032 :=
    @gBitri
      (.classMem (synCop (.cv x) (.cv y)) (synCrn (synCtxp (synCfns)
            (synCrn (synCtxp (synCcnv (synCimage (synCswap))) (synCfns))))))
      (synWex f (.classMem (synCop (.cv f) (synCop (.cv x) (.cv y))) (synCtxp (synCfns)
            (synCrn (synCtxp (synCcnv (synCimage (synCswap))) (synCfns))))))
      (synWex f (synWf1o (.cv f) (.cv x) (.cv y))) p0001 p0031
  have p0033 :=
    @gOpabbi2i (synWex f (synWf1o (.cv f) (.cv x) (.cv y))) x y
      (synCrn (synCtxp (synCfns)
          (synCrn (synCtxp (synCcnv (synCimage (synCswap))) (synCfns)))))
      dv_cache_0010 dv_cache_0011 dv_cache_0003 p0032
  have p0034 :=
    @gEqtr4i (synCen) (synCopab x y (synWex f (synWf1o (.cv f) (.cv x) (.cv y))))
      (synCrn (synCtxp (synCfns)
          (synCrn (synCtxp (synCcnv (synCimage (synCswap))) (synCfns)))))
      p0000 p0033
  have p0035 := @gFnsex
  have p0036 := @gSwapex
  have p0037 := @gImageex (synCswap) p0036
  have p0038 := @gCnvex (synCimage (synCswap)) p0037
  have p0040 := @gTxpex (synCcnv (synCimage (synCswap))) (synCfns) p0038 p0035
  have p0041 := @gRnex (synCtxp (synCcnv (synCimage (synCswap))) (synCfns)) p0040
  have p0042 :=
    @gTxpex (synCfns)
      (synCrn (synCtxp (synCcnv (synCimage (synCswap))) (synCfns))) p0035 p0041
  have p0043 :=
    @gRnex
      (synCtxp (synCfns) (synCrn (synCtxp (synCcnv (synCimage (synCswap))) (synCfns))))
      p0042
  have p0044 :=
    @gEqeltri (synCen)
      (synCrn (synCtxp (synCfns)
          (synCrn (synCtxp (synCcnv (synCimage (synCswap))) (synCfns)))))
      (synCvv) p0034 p0043
  exact p0044

/-- Checked nominal proof certificate identified upstream as `g_f1oeng`. -/
@[expose]
noncomputable def gF1oeng (A : Class) (B : Class) (C : Class) (F : Class) :
    Nominal.NPrf
      (.imp (synWa (.classMem F C) (synWf1o F A B)) (synWbr A (synCen) B)) :=
  by
  let proofSupport : Finset Var := A.fv ∪ B.fv ∪ C.fv ∪ F.fv
  let f : Var := freshVar proofSupport 0
  have fresh_f : f ∉ proofSupport :=
    by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_f_not_A : f ∉ A.fv := by
    intro h
    exact
      fresh_f
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (h))))
  have fresh_f_not_B : f ∉ B.fv := by
    intro h
    exact
      fresh_f
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))
  have fresh_f_not_F : f ∉ F.fv := by
    intro h
    exact fresh_f (Finset.mem_union_right _ (h))
  have dv_cache_0001 : f ∉ (F).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : f ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_f_not_F, not_false_eq_true])
  have dv_cache_0002 : f ∉ ((synWf1o F A B)).fv :=
    by
    clear dv_cache_0001
    exact
      (by
        have compact_fv_not_mem_empty : f ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wf1o,
          Finset.mem_union, fresh_f_not_A, fresh_f_not_B, fresh_f_not_F, or_false,
          not_false_eq_true])
  have dv_cache_0003 : f ∉ (A).fv :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact
      (by
        have compact_fv_not_mem_empty : f ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_f_not_A, not_false_eq_true])
  have dv_cache_0004 : f ∉ (B).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact
      (by
        have compact_fv_not_mem_empty : f ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_f_not_B, not_false_eq_true])
  have p0000 := @gF1oeq1 A B (.cv f) F
  have p0001 :=
    @gSpcegv (synWf1o (.cv f) A B) (synWf1o F A B) f F C dv_cache_0001 dv_cache_0002
      p0000
  have p0002 :=
    @gImp (.classMem F C) (synWf1o F A B) (synWex f (synWf1o (.cv f) A B)) p0001
  have p0003 := @gBren A B f dv_cache_0003 dv_cache_0004
  have p0004 :=
    @gSylibr (synWa (.classMem F C) (synWf1o F A B)) (synWex f (synWf1o (.cv f) A B))
      (synWbr A (synCen) B) p0002 p0003
  exact p0004

/-- Checked nominal proof certificate identified upstream as `g_f1oen`. -/
@[expose]
noncomputable def gF1oen (A : Class) (B : Class) (F : Class)
    (hyp_f1oen_1 : Nominal.NPrf (.classMem F (synCvv))) :
    Nominal.NPrf (.imp (synWf1o F A B) (synWbr A (synCen) B)) :=
  by
  have p0000 := @gF1oeng A B (synCvv) F
  have p0001 :=
    @gMpan (.classMem F (synCvv)) (synWf1o F A B) (synWbr A (synCen) B) hyp_f1oen_1
      p0000
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_enrflxg`. -/
@[expose]
noncomputable def gEnrflxg (A : Class) (V : Class) :
    Nominal.NPrf (.imp (.classMem A V) (synWbr A (synCen) A)) :=
  by
  have p0000 := @gIdex
  have p0001 := @gResexg (synCid) A (synCvv) V
  have p0002 :=
    @gMpan (.classMem (synCid) (synCvv)) (.classMem A V)
      (.classMem (synCres (synCid) A) (synCvv)) p0000 p0001
  have p0003 := @gF1oi A
  have p0004 := @gF1oeng A A (synCvv) (synCres (synCid) A)
  have p0005 :=
    @gSylancl (.classMem A V) (.classMem (synCres (synCid) A) (synCvv))
      (synWf1o (synCres (synCid) A) A A) (synWbr A (synCen) A) p0002 p0003 p0004
  exact p0005

/-- Checked nominal proof certificate identified upstream as `g_enrflx`. -/
@[expose]
noncomputable def gEnrflx (A : Class)
    (hyp_enrflx_1 : Nominal.NPrf (.classMem A (synCvv))) :
    Nominal.NPrf (synWbr A (synCen) A) :=
  by
  have p0000 := @gEnrflxg A (synCvv)
  have p0001 := Nominal.mp hyp_enrflx_1 p0000
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_ensymi`. -/
@[expose]
noncomputable def gEnsymi (A : Class) (B : Class) :
    Nominal.NPrf (.imp (synWbr A (synCen) B) (synWbr B (synCen) A)) :=
  by
  let proofSupport : Finset Var := A.fv ∪ B.fv
  let f : Var := freshVar proofSupport 0
  have fresh_f : f ∉ proofSupport :=
    by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_f_not_A : f ∉ A.fv := by
    intro h
    exact fresh_f (Finset.mem_union_left _ (h))
  have fresh_f_not_B : f ∉ B.fv := by
    intro h
    exact fresh_f (Finset.mem_union_right _ (h))
  have dv_cache_0001 : f ∉ (A).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : f ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_f_not_A, not_false_eq_true])
  have dv_cache_0002 : f ∉ (B).fv :=
    by
    clear dv_cache_0001
    exact
      (by
        have compact_fv_not_mem_empty : f ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_f_not_B, not_false_eq_true])
  have dv_cache_0003 : f ∉ ((synWbr B (synCen) A)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact
      (by
        have compact_fv_not_mem_empty : f ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cen, Finset.mem_union,
          fresh_f_not_B, fresh_f_not_A, compact_fv_not_mem_empty, or_false,
          not_false_eq_true])
  have p0000 := @gBren A B f dv_cache_0001 dv_cache_0002
  have p0001 := @gF1ocnv A B (.cv f)
  have p0002 := @gVex f
  have p0003 := @gCnvex (.cv f) p0002
  have p0004 := @gF1oen B A (synCcnv (.cv f)) p0003
  have p0005 :=
    @gSyl (synWf1o (.cv f) A B) (synWf1o (synCcnv (.cv f)) B A)
      (synWbr B (synCen) A) p0001 p0004
  have p0006 :=
    @gExlimiv (synWf1o (.cv f) A B) (synWbr B (synCen) A) f dv_cache_0003 p0005
  have p0007 :=
    @gSylbi (synWbr A (synCen) B) (synWex f (synWf1o (.cv f) A B))
      (synWbr B (synCen) A) p0000 p0006
  exact p0007

/-- Checked nominal proof certificate identified upstream as `g_ensym`. -/
@[expose]
noncomputable def gEnsym (A : Class) (B : Class) :
    Nominal.NPrf (synWb (synWbr A (synCen) B) (synWbr B (synCen) A)) :=
  by
  have p0000 := @gEnsymi A B
  have p0001 := @gEnsymi B A
  have p0002 := @gImpbii (synWbr A (synCen) B) (synWbr B (synCen) A) p0000 p0001
  exact p0002

/-- Checked nominal proof certificate identified upstream as `g_entr`. -/
@[expose]
noncomputable def gEntr (A : Class) (B : Class) (C : Class) :
    Nominal.NPrf
      (.imp (synWa (synWbr A (synCen) B) (synWbr B (synCen) C)) (synWbr A (synCen) C)) :=
  by
  let proofSupport : Finset Var := A.fv ∪ B.fv ∪ C.fv
  let f : Var := freshVar proofSupport 0
  let g : Var := freshVar proofSupport 1
  have fresh_f : f ∉ proofSupport :=
    by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_f_not_A : f ∉ A.fv := by
    intro h
    exact fresh_f (Finset.mem_union_left _ (Finset.mem_union_left _ (h)))
  have fresh_f_not_B : f ∉ B.fv := by
    intro h
    exact fresh_f (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_f_not_C : f ∉ C.fv := by
    intro h
    exact fresh_f (Finset.mem_union_right _ (h))
  have fresh_g : g ∉ proofSupport :=
    by
    change freshVar proofSupport 1 ∉ proofSupport
    exact freshVar_not_mem proofSupport 1
  have fresh_g_not_A : g ∉ A.fv := by
    intro h
    exact fresh_g (Finset.mem_union_left _ (Finset.mem_union_left _ (h)))
  have fresh_g_not_B : g ∉ B.fv := by
    intro h
    exact fresh_g (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_g_not_C : g ∉ C.fv := by
    intro h
    exact fresh_g (Finset.mem_union_right _ (h))
  have fresh_f_ne_g : f ≠ g :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have fresh_g_ne_f : g ≠ f := Ne.symm fresh_f_ne_g
  have dv_cache_0001 : f ∉ (A).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : f ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_f_not_A, not_false_eq_true])
  have dv_cache_0002 : f ∉ (B).fv :=
    by
    clear dv_cache_0001
    exact
      (by
        have compact_fv_not_mem_empty : f ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_f_not_B, not_false_eq_true])
  have dv_cache_0003 : g ∉ (B).fv :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact
      (by
        have compact_fv_not_mem_empty : g ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_g_not_B, not_false_eq_true])
  have dv_cache_0004 : g ∉ (C).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact
      (by
        have compact_fv_not_mem_empty : g ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_g_not_C, not_false_eq_true])
  have dv_cache_0005 : g ∉ ((synWf1o (.cv f) A B)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact
      (by
        have compact_fv_not_mem_empty : g ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wf1o,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, fresh_g_not_A, fresh_g_not_B, fresh_g_ne_f, or_false,
          not_false_eq_true])
  have dv_cache_0006 : f ∉ ((synWf1o (.cv g) B C)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact
      (by
        have compact_fv_not_mem_empty : f ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wf1o,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, fresh_f_not_B, fresh_f_not_C, fresh_f_ne_g, or_false,
          not_false_eq_true])
  have dv_cache_0007 : f ∉ ((synWbr A (synCen) C)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006
    exact
      (by
        have compact_fv_not_mem_empty : f ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cen, Finset.mem_union,
          fresh_f_not_A, fresh_f_not_C, compact_fv_not_mem_empty, or_false,
          not_false_eq_true])
  have dv_cache_0008 : g ∉ ((synWbr A (synCen) C)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007
    exact
      (by
        have compact_fv_not_mem_empty : g ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cen, Finset.mem_union,
          fresh_g_not_A, fresh_g_not_C, compact_fv_not_mem_empty, or_false,
          not_false_eq_true])
  have p0000 := @gBren A B f dv_cache_0001 dv_cache_0002
  have p0001 := @gBren B C g dv_cache_0003 dv_cache_0004
  have p0002 :=
    @gAnbi12i (synWbr A (synCen) B) (synWex f (synWf1o (.cv f) A B))
      (synWbr B (synCen) C) (synWex g (synWf1o (.cv g) B C)) p0000 p0001
  have p0003 :=
    @gEeanv (synWf1o (.cv f) A B) (synWf1o (.cv g) B C) f g dv_cache_0005 dv_cache_0006
  have p0004 :=
    @gBitr4i (synWa (synWbr A (synCen) B) (synWbr B (synCen) C))
      (synWa (synWex f (synWf1o (.cv f) A B)) (synWex g (synWf1o (.cv g) B C)))
      (synWex f (synWex g (synWa (synWf1o (.cv f) A B) (synWf1o (.cv g) B C)))) p0002
      p0003
  have p0005 := @gF1oco A B C (.cv g) (.cv f)
  have p0006 :=
    @gAncoms (synWf1o (.cv g) B C) (synWf1o (.cv f) A B)
      (synWf1o (synCcom (.cv g) (.cv f)) A C) p0005
  have p0007 := @gVex g
  have p0008 := @gVex f
  have p0009 := @gCoex (.cv g) (.cv f) p0007 p0008
  have p0010 := @gF1oen A C (synCcom (.cv g) (.cv f)) p0009
  have p0011 :=
    @gSyl (synWa (synWf1o (.cv f) A B) (synWf1o (.cv g) B C))
      (synWf1o (synCcom (.cv g) (.cv f)) A C) (synWbr A (synCen) C) p0006 p0010
  have p0012 :=
    @gExlimivv (synWa (synWf1o (.cv f) A B) (synWf1o (.cv g) B C))
      (synWbr A (synCen) C) f g dv_cache_0007 dv_cache_0008 p0011
  have p0013 :=
    @gSylbi (synWa (synWbr A (synCen) B) (synWbr B (synCen) C))
      (synWex f (synWex g (synWa (synWf1o (.cv f) A B) (synWf1o (.cv g) B C))))
      (synWbr A (synCen) C) p0004 p0012
  exact p0013


end NFChoice.DirectNominalPrf.WPPReplay

end

/-! Certificates from `NominalWPPReplayChunk013Compact001Part032`. -/


section

namespace NFChoice.DirectNominalPrf.WPPReplay

open scoped Fol
open NFChoice.Foundation
open NFChoice.SemanticCore
open NFChoice.ReplaySupport
open NFChoice.Compiler.CompactSourceSyntax

/-- Checked nominal proof certificate identified upstream as `g_ener`. -/
@[expose]
noncomputable def gEner : Nominal.NPrf (synWbr (synCen) (synCer) (synCvv)) :=
  by
  let proofSupport : Finset Var := (∅ : Finset Var)
  let x : Var := freshVar proofSupport 0
  let y : Var := freshVar proofSupport 1
  let z : Var := freshVar proofSupport 2
  have fresh_x_ne_y : x ≠ y :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have fresh_x_ne_z : x ≠ z :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 2
    exact freshVar_injective proofSupport (i := 0) (j := 2) (by decide)
  have fresh_y_ne_z : y ≠ z :=
    by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 2
    exact freshVar_injective proofSupport (i := 1) (j := 2) (by decide)
  have dv_cache_0001 : x ∉ ((synCvv)).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv,
          compact_fv_not_mem_empty, not_false_eq_true])
  have dv_cache_0002 : y ∉ ((synCvv)).fv :=
    by
    clear dv_cache_0001
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv,
          compact_fv_not_mem_empty, not_false_eq_true])
  have dv_cache_0003 : z ∉ ((synCvv)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact
      (by
        have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv,
          compact_fv_not_mem_empty, not_false_eq_true])
  have dv_cache_0004 : x ∉ ((synCen)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cen,
          compact_fv_not_mem_empty, not_false_eq_true])
  have dv_cache_0005 : y ∉ ((synCen)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cen,
          compact_fv_not_mem_empty, not_false_eq_true])
  have dv_cache_0006 : z ∉ ((synCen)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact
      (by
        have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cen,
          compact_fv_not_mem_empty, not_false_eq_true])
  have dv_cache_0007 : x ∉ (synWtru).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wtru,
          compact_fv_not_mem_empty, not_false_eq_true])
  have dv_cache_0008 : y ∉ (synWtru).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wtru,
          compact_fv_not_mem_empty, not_false_eq_true])
  have dv_cache_0009 : z ∉ (synWtru).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008
    exact
      (by
        have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wtru,
          compact_fv_not_mem_empty, not_false_eq_true])
  have dv_cache_0010 : x ≠ y :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009
    exact (show x ≠ y from (by exact fresh_x_ne_y))
  have dv_cache_0011 : x ≠ z :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010
    exact (show x ≠ z from (by exact fresh_x_ne_z))
  have dv_cache_0012 : y ≠ z :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
    exact (show y ≠ z from (by exact fresh_y_ne_z))
  have p0000 := @gEnex
  have p0001 := @gA1i (.classMem (synCen) (synCvv)) synWtru p0000
  have p0002 := @gVvex
  have p0003 := @gA1i (.classMem (synCvv) (synCvv)) synWtru p0002
  have p0004 := @gEnsymi (.cv x) (.cv y)
  have p0005 :=
    @gN3ad2ant3 (synWbr (.cv x) (synCen) (.cv y)) synWtru
      (synWbr (.cv y) (synCen) (.cv x))
      (synWa (.classMem (.cv x) (synCvv)) (.classMem (.cv y) (synCvv))) p0004
  have p0006 := @gEntr (.cv x) (.cv y) (.cv z)
  have p0007 :=
    @gN3ad2ant3
      (synWa (synWbr (.cv x) (synCen) (.cv y)) (synWbr (.cv y) (synCen) (.cv z)))
      synWtru (synWbr (.cv x) (synCen) (.cv z))
      (synW3a (.classMem (.cv x) (synCvv)) (.classMem (.cv y) (synCvv))
        (.classMem (.cv z) (synCvv)))
      p0006
  have p0008 :=
    @gIserd synWtru x y z (synCvv) (synCen) (synCvv) (synCvv) dv_cache_0001
      dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007
      dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 p0001 p0003
      p0005 p0007
  have p0009 := @gTrud (synWbr (synCen) (synCer) (synCvv)) p0008
  exact p0009

/-- Checked nominal proof certificate identified upstream as `g_idssen`. -/
@[expose]
noncomputable def gIdssen : Nominal.NPrf (synWss (synCid) (synCen)) :=
  by
  let proofSupport : Finset Var := (∅ : Finset Var)
  let x : Var := freshVar proofSupport 0
  let y : Var := freshVar proofSupport 1
  have fresh_x_ne_y : x ≠ y :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have dv_cache_0001 : x ∉ ((synCid)).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cid,
          compact_fv_not_mem_empty, not_false_eq_true])
  have dv_cache_0002 : y ∉ ((synCid)).fv :=
    by
    clear dv_cache_0001
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cid,
          compact_fv_not_mem_empty, not_false_eq_true])
  have dv_cache_0003 : x ∉ ((synCen)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cen,
          compact_fv_not_mem_empty, not_false_eq_true])
  have dv_cache_0004 : y ∉ ((synCen)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cen,
          compact_fv_not_mem_empty, not_false_eq_true])
  have dv_cache_0005 : x ≠ y :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact (show x ≠ y from (by exact fresh_x_ne_y))
  have p0000 := @gVex y
  have p0001 := @gIdeq (.cv x) (.cv y) p0000
  have p0002 := @gVex x
  have p0003 := @gEnrflx (.cv x) p0002
  have p0004 := @gBreq2 (.cv x) (.cv y) (.cv x) (synCen)
  have p0005_e01_recanon :
    Nominal.NPrf
      (.imp (.objEq x y) (synWb (synWbr (.cv x) (synCen) (.cv x))
          (synWbr (.cv x) (synCen) (.cv y)))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold synWb synWbr synCop synCun synCnin synWnan synWa synCcompl synWrex
          synWex synCphi synCen synCopab
        simp (config :=
          { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_class_cv]
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
        · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0004
  have p0005 :=
    @gMpbii (.objEq x y) (synWbr (.cv x) (synCen) (.cv x))
      (synWbr (.cv x) (synCen) (.cv y)) p0003 p0005_e01_recanon
  have p0006_e00_recanon :
    Nominal.NPrf (synWb (synWbr (.cv x) (synCid) (.cv y)) (.objEq x y)) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold synWb synWbr synCop synCun synCnin synWnan synWa synCcompl synWrex
          synWex synCphi synCid synCopab
        simp (config :=
          { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CoreFVSimp.fv_wff_objEq]
        apply Nominal.RecanonTransportDev.TRecanonWff.neg
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · apply Nominal.RecanonTransportDev.TRecanonWff.imp
          · exact Nominal.RecanonTransportDev.TRecanonWff.same _
          · exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
        · apply Nominal.RecanonTransportDev.TRecanonWff.neg
          apply Nominal.RecanonTransportDev.TRecanonWff.imp
          · exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
          · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0001
  have p0006 :=
    @gSylbi (synWbr (.cv x) (synCid) (.cv y)) (.objEq x y)
      (synWbr (.cv x) (synCen) (.cv y)) p0006_e00_recanon p0005
  have p0007 := (Nominal.biimpRefl (synWbr (.cv x) (synCid) (.cv y)))
  have p0008 := (Nominal.biimpRefl (synWbr (.cv x) (synCen) (.cv y)))
  have p0009 :=
    @gN3imtr3i (synWbr (.cv x) (synCid) (.cv y)) (synWbr (.cv x) (synCen) (.cv y))
      (.classMem (synCop (.cv x) (.cv y)) (synCid))
      (.classMem (synCop (.cv x) (.cv y)) (synCen)) p0006 p0007 p0008
  have p0010 :=
    @gRelssi x y (synCid) (synCen) dv_cache_0001 dv_cache_0002 dv_cache_0003
      dv_cache_0004 dv_cache_0005 p0009
  exact p0010

/-- Checked nominal proof certificate identified upstream as `g_dmen`. -/
@[expose]
noncomputable def gDmen : Nominal.NPrf (.classEq (synCdm (synCen)) (synCvv)) :=
  by
  have p0000 := @gIdssen
  have p0001 := @gDmi
  have p0002 := @gDmss (synCid) (synCen)
  have p0003 :=
    @gSyl5eqssr (synWss (synCid) (synCen)) (synCvv) (synCdm (synCid))
      (synCdm (synCen)) p0001 p0002
  have p0004 := Nominal.mp p0000 p0003
  have p0005 := @gVss (synCdm (synCen))
  have p0006 :=
    @gMpbi (synWss (synCvv) (synCdm (synCen)))
      (.classEq (synCdm (synCen)) (synCvv)) p0004 p0005
  exact p0006

/-- Checked nominal proof certificate identified upstream as `g_en0`. -/
@[expose]
noncomputable def gEn0 (A : Class) :
    Nominal.NPrf (synWb (synWbr A (synCen) (synC0)) (.classEq A (synC0))) :=
  by
  let proofSupport : Finset Var := A.fv
  let f : Var := freshVar proofSupport 0
  have fresh_f : f ∉ proofSupport :=
    by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_f_not_A : f ∉ A.fv := by
    intro h
    exact fresh_f (h)
  have dv_cache_0001 : f ∉ (A).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : f ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_f_not_A, not_false_eq_true])
  have dv_cache_0002 : f ∉ ((synC0)).fv :=
    by
    clear dv_cache_0001
    exact
      (by
        have compact_fv_not_mem_empty : f ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0,
          compact_fv_not_mem_empty, not_false_eq_true])
  have dv_cache_0003 : f ∉ ((Wff.classEq A (synC0))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact
      (by
        have compact_fv_not_mem_empty : f ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0, Finset.mem_union,
          fresh_f_not_A, compact_fv_not_mem_empty, or_false, not_false_eq_true])
  have p0000 := @gBren A (synC0) f dv_cache_0001 dv_cache_0002
  have p0001 := @gF1ocnv A (synC0) (.cv f)
  have p0002 := @gF1o00 A (synCcnv (.cv f))
  have p0003 :=
    @gSimprbi (synWf1o (synCcnv (.cv f)) (synC0) A)
      (.classEq (synCcnv (.cv f)) (synC0)) (.classEq A (synC0)) p0002
  have p0004 :=
    @gSyl (synWf1o (.cv f) A (synC0)) (synWf1o (synCcnv (.cv f)) (synC0) A)
      (.classEq A (synC0)) p0001 p0003
  have p0005 :=
    @gExlimiv (synWf1o (.cv f) A (synC0)) (.classEq A (synC0)) f dv_cache_0003 p0004
  have p0006 :=
    @gSylbi (synWbr A (synCen) (synC0)) (synWex f (synWf1o (.cv f) A (synC0)))
      (.classEq A (synC0)) p0000 p0005
  have p0007 := @gN0ex
  have p0008 := @gEnrflx (synC0) p0007
  have p0009 := @gBreq1 A (synC0) (synC0) (synCen)
  have p0010 :=
    @gMpbiri (.classEq A (synC0)) (synWbr A (synCen) (synC0))
      (synWbr (synC0) (synCen) (synC0)) p0008 p0009
  have p0011 := @gImpbii (synWbr A (synCen) (synC0)) (.classEq A (synC0)) p0006 p0010
  exact p0011

/-- Checked nominal proof certificate identified upstream as `g_fundmen`. -/
@[expose]
noncomputable def gFundmen (F : Class)
    (hyp_fundmen_1 : Nominal.NPrf (.classMem F (synCvv))) :
    Nominal.NPrf (.imp (synWfun F) (synWbr (synCdm F) (synCen) F)) :=
  by
  let proofSupport : Finset Var := F.fv
  let x : Var := freshVar proofSupport 0
  let y : Var := freshVar proofSupport 1
  let z : Var := freshVar proofSupport 2
  let a : Var := freshVar proofSupport 3
  let b : Var := freshVar proofSupport 4
  have fresh_x : x ∉ proofSupport :=
    by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_x_not_F : x ∉ F.fv := by
    intro h
    exact fresh_x (h)
  have fresh_y : y ∉ proofSupport :=
    by
    change freshVar proofSupport 1 ∉ proofSupport
    exact freshVar_not_mem proofSupport 1
  have fresh_y_not_F : y ∉ F.fv := by
    intro h
    exact fresh_y (h)
  have fresh_z : z ∉ proofSupport :=
    by
    change freshVar proofSupport 2 ∉ proofSupport
    exact freshVar_not_mem proofSupport 2
  have fresh_z_not_F : z ∉ F.fv := by
    intro h
    exact fresh_z (h)
  have fresh_a : a ∉ proofSupport :=
    by
    change freshVar proofSupport 3 ∉ proofSupport
    exact freshVar_not_mem proofSupport 3
  have fresh_a_not_F : a ∉ F.fv := by
    intro h
    exact fresh_a (h)
  have fresh_b : b ∉ proofSupport :=
    by
    change freshVar proofSupport 4 ∉ proofSupport
    exact freshVar_not_mem proofSupport 4
  have fresh_b_not_F : b ∉ F.fv := by
    intro h
    exact fresh_b (h)
  have fresh_x_ne_y : x ≠ y :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have fresh_x_ne_z : x ≠ z :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 2
    exact freshVar_injective proofSupport (i := 0) (j := 2) (by decide)
  have fresh_x_ne_a : x ≠ a :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 3
    exact freshVar_injective proofSupport (i := 0) (j := 3) (by decide)
  have fresh_a_ne_x : a ≠ x := Ne.symm fresh_x_ne_a
  have fresh_x_ne_b : x ≠ b :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 4
    exact freshVar_injective proofSupport (i := 0) (j := 4) (by decide)
  have fresh_b_ne_x : b ≠ x := Ne.symm fresh_x_ne_b
  have fresh_y_ne_z : y ≠ z :=
    by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 2
    exact freshVar_injective proofSupport (i := 1) (j := 2) (by decide)
  have fresh_y_ne_a : y ≠ a :=
    by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 3
    exact freshVar_injective proofSupport (i := 1) (j := 3) (by decide)
  have fresh_a_ne_y : a ≠ y := Ne.symm fresh_y_ne_a
  have fresh_y_ne_b : y ≠ b :=
    by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 4
    exact freshVar_injective proofSupport (i := 1) (j := 4) (by decide)
  have fresh_b_ne_y : b ≠ y := Ne.symm fresh_y_ne_b
  have fresh_z_ne_a : z ≠ a :=
    by
    change freshVar proofSupport 2 ≠ freshVar proofSupport 3
    exact freshVar_injective proofSupport (i := 2) (j := 3) (by decide)
  have fresh_a_ne_z : a ≠ z := Ne.symm fresh_z_ne_a
  have fresh_z_ne_b : z ≠ b :=
    by
    change freshVar proofSupport 2 ≠ freshVar proofSupport 4
    exact freshVar_injective proofSupport (i := 2) (j := 4) (by decide)
  have fresh_b_ne_z : b ≠ z := Ne.symm fresh_z_ne_b
  have fresh_a_ne_b : a ≠ b :=
    by
    change freshVar proofSupport 3 ≠ freshVar proofSupport 4
    exact freshVar_injective proofSupport (i := 3) (j := 4) (by decide)
  have fresh_b_ne_a : b ≠ a := Ne.symm fresh_a_ne_b
  have dv_cache_0001 : a ∉ ((Class.cv y)).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : a ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_a_ne_y, not_false_eq_true])
  have dv_cache_0002 : a ∉ ((Class.cv x)).fv :=
    by
    clear dv_cache_0001
    exact
      (by
        have compact_fv_not_mem_empty : a ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_a_ne_x, not_false_eq_true])
  have dv_cache_0003 : a ∉ ((Wff.classMem (.cv y) F)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact
      (by
        have compact_fv_not_mem_empty : a ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, fresh_a_ne_y, fresh_a_not_F, or_false, not_false_eq_true])
  have dv_cache_0004 : b ∉ ((Class.cv z)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact
      (by
        have compact_fv_not_mem_empty : b ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_b_ne_z, not_false_eq_true])
  have dv_cache_0005 : b ∉ ((Class.cv x)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact
      (by
        have compact_fv_not_mem_empty : b ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_b_ne_x, not_false_eq_true])
  have dv_cache_0006 : b ∉ ((Wff.classMem (.cv z) F)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact
      (by
        have compact_fv_not_mem_empty : b ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, fresh_b_ne_z, fresh_b_not_F, or_false, not_false_eq_true])
  have dv_cache_0007 :
    b ∉
      ((synWa (.classEq (.cv y) (synCop (.cv x) (.cv a))) (.classMem (.cv y) F))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006
    exact
      (by
        have compact_fv_not_mem_empty : b ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cop,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, Finset.mem_union,
          Finset.mem_singleton, fresh_b_ne_y, fresh_b_ne_x, fresh_b_ne_a, fresh_b_not_F,
          or_false, not_false_eq_true])
  have dv_cache_0008 :
    a ∉
      ((synWa (.classEq (.cv z) (synCop (.cv x) (.cv b))) (.classMem (.cv z) F))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007
    exact
      (by
        have compact_fv_not_mem_empty : a ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cop,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, Finset.mem_union,
          Finset.mem_singleton, fresh_a_ne_z, fresh_a_ne_x, fresh_a_ne_b, fresh_a_not_F,
          or_false, not_false_eq_true])
  have dv_cache_0009 : x ∉ (F).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_x_not_F, not_false_eq_true])
  have dv_cache_0010 : a ∉ (F).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009
    exact
      (by
        have compact_fv_not_mem_empty : a ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_a_not_F, not_false_eq_true])
  have dv_cache_0011 : b ∉ (F).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010
    exact
      (by
        have compact_fv_not_mem_empty : b ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_b_not_F, not_false_eq_true])
  have dv_cache_0012 : x ≠ a :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
    exact (show x ≠ a from (by exact fresh_x_ne_a))
  have dv_cache_0013 : x ≠ b :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012
    exact (show x ≠ b from (by exact fresh_x_ne_b))
  have dv_cache_0014 : a ≠ b :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013
    exact (show a ≠ b from (by exact fresh_a_ne_b))
  have dv_cache_0015 : a ∉ ((Wff.objEq y z)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014
    exact
      (by
        have compact_fv_not_mem_empty : a ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_objEq, Finset.mem_insert,
          Finset.mem_singleton, fresh_a_ne_y, fresh_a_ne_z, or_false, not_false_eq_true])
  have dv_cache_0016 : b ∉ ((Wff.objEq y z)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015
    exact
      (by
        have compact_fv_not_mem_empty : b ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_objEq, Finset.mem_insert,
          Finset.mem_singleton, fresh_b_ne_y, fresh_b_ne_z, or_false, not_false_eq_true])
  have dv_cache_0017 : a ∉ ((synWfun F)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016
    exact
      (by
        have compact_fv_not_mem_empty : a ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wfun, fresh_a_not_F,
          not_false_eq_true])
  have dv_cache_0018 : b ∉ ((synWfun F)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
    exact
      (by
        have compact_fv_not_mem_empty : b ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wfun, fresh_b_not_F,
          not_false_eq_true])
  have dv_cache_0019 : z ∉ ((synWfun F)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018
    exact
      (by
        have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wfun, fresh_z_not_F,
          not_false_eq_true])
  have dv_cache_0020 : x ∉ ((synWfun F)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wfun, fresh_x_not_F,
          not_false_eq_true])
  have dv_cache_0021 : y ∉ ((synWfun F)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wfun, fresh_y_not_F,
          not_false_eq_true])
  have dv_cache_0022 : x ∉ ((synCcnv (synCres (synC1st) F))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cres,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1st, Finset.mem_union,
          fresh_x_not_F, compact_fv_not_mem_empty, or_false, not_false_eq_true])
  have dv_cache_0023 : y ∉ ((synCcnv (synCres (synC1st) F))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cres,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1st, Finset.mem_union,
          fresh_y_not_F, compact_fv_not_mem_empty, or_false, not_false_eq_true])
  have dv_cache_0024 : z ∉ ((synCcnv (synCres (synC1st) F))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
    exact
      (by
        have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cres,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1st, Finset.mem_union,
          fresh_z_not_F, compact_fv_not_mem_empty, or_false, not_false_eq_true])
  have dv_cache_0025 : x ≠ y :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024
    exact (show x ≠ y from (by exact fresh_x_ne_y))
  have dv_cache_0026 : x ≠ z :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025
    exact (show x ≠ z from (by exact fresh_x_ne_z))
  have dv_cache_0027 : y ≠ z :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026
    exact (show y ≠ z from (by exact fresh_y_ne_z))
  have p0000 := @gSsv F
  have p0001 := @gN1stfo
  have p0002 := @gFofn (synCvv) (synCvv) (synC1st)
  have p0003 := @gFnssresb (synCvv) F (synC1st)
  have p0004 :=
    @gMp2b (synWfo (synC1st) (synCvv) (synCvv)) (synWfn (synC1st) (synCvv))
      (synWb (synWfn (synCres (synC1st) F) F) (synWss F (synCvv))) p0001 p0002 p0003
  have p0005 :=
    @gMpbir (synWfn (synCres (synC1st) F) F) (synWss F (synCvv)) p0000 p0004
  have p0006 := @gA1i (synWfn (synCres (synC1st) F) F) (synWfun F) p0005
  have p0007 := @gBrcnv (.cv x) (.cv y) (synCres (synC1st) F)
  have p0008 := @gBrres (.cv y) (.cv x) (synC1st) F
  have p0009 := @gVex x
  have p0010 := @gBr1st a (.cv y) (.cv x) dv_cache_0001 dv_cache_0002 p0009
  have p0011 :=
    @gAnbi1i (synWbr (.cv y) (synC1st) (.cv x))
      (synWex a (.classEq (.cv y) (synCop (.cv x) (.cv a)))) (.classMem (.cv y) F) p0010
  have p0012 :=
    @gN1941v (.classEq (.cv y) (synCop (.cv x) (.cv a))) (.classMem (.cv y) F) a
      dv_cache_0003
  have p0013 :=
    @gBitr4i (synWa (synWbr (.cv y) (synC1st) (.cv x)) (.classMem (.cv y) F))
      (synWa (synWex a (.classEq (.cv y) (synCop (.cv x) (.cv a)))) (.classMem (.cv y) F))
      (synWex a (synWa (.classEq (.cv y) (synCop (.cv x) (.cv a))) (.classMem (.cv y) F)))
      p0011 p0012
  have p0014 :=
    @gN3bitri (synWbr (.cv x) (synCcnv (synCres (synC1st) F)) (.cv y))
      (synWbr (.cv y) (synCres (synC1st) F) (.cv x))
      (synWa (synWbr (.cv y) (synC1st) (.cv x)) (.classMem (.cv y) F))
      (synWex a (synWa (.classEq (.cv y) (synCop (.cv x) (.cv a))) (.classMem (.cv y) F)))
      p0007 p0008 p0013
  have p0015 := @gBrcnv (.cv x) (.cv z) (synCres (synC1st) F)
  have p0016 := @gBrres (.cv z) (.cv x) (synC1st) F
  have p0017 := @gBr1st b (.cv z) (.cv x) dv_cache_0004 dv_cache_0005 p0009
  have p0018 :=
    @gAnbi1i (synWbr (.cv z) (synC1st) (.cv x))
      (synWex b (.classEq (.cv z) (synCop (.cv x) (.cv b)))) (.classMem (.cv z) F) p0017
  have p0019 :=
    @gN3bitri (synWbr (.cv x) (synCcnv (synCres (synC1st) F)) (.cv z))
      (synWbr (.cv z) (synCres (synC1st) F) (.cv x))
      (synWa (synWbr (.cv z) (synC1st) (.cv x)) (.classMem (.cv z) F))
      (synWa (synWex b (.classEq (.cv z) (synCop (.cv x) (.cv b)))) (.classMem (.cv z) F))
      p0015 p0016 p0018
  have p0020 :=
    @gN1941v (.classEq (.cv z) (synCop (.cv x) (.cv b))) (.classMem (.cv z) F) b
      dv_cache_0006
  have p0021 :=
    @gBitr4i (synWbr (.cv x) (synCcnv (synCres (synC1st) F)) (.cv z))
      (synWa (synWex b (.classEq (.cv z) (synCop (.cv x) (.cv b)))) (.classMem (.cv z) F))
      (synWex b (synWa (.classEq (.cv z) (synCop (.cv x) (.cv b))) (.classMem (.cv z) F)))
      p0019 p0020
  have p0022 :=
    @gAnbi12i (synWbr (.cv x) (synCcnv (synCres (synC1st) F)) (.cv y))
      (synWex a (synWa (.classEq (.cv y) (synCop (.cv x) (.cv a))) (.classMem (.cv y) F)))
      (synWbr (.cv x) (synCcnv (synCres (synC1st) F)) (.cv z))
      (synWex b (synWa (.classEq (.cv z) (synCop (.cv x) (.cv b))) (.classMem (.cv z) F)))
      p0014 p0021
  have p0023 :=
    @gEeanv (synWa (.classEq (.cv y) (synCop (.cv x) (.cv a))) (.classMem (.cv y) F))
      (synWa (.classEq (.cv z) (synCop (.cv x) (.cv b))) (.classMem (.cv z) F)) a b
      dv_cache_0007 dv_cache_0008
  have p0024 :=
    @gBitr4i
      (synWa (synWbr (.cv x) (synCcnv (synCres (synC1st) F)) (.cv y))
        (synWbr (.cv x) (synCcnv (synCres (synC1st) F)) (.cv z)))
      (synWa (synWex a
          (synWa (.classEq (.cv y) (synCop (.cv x) (.cv a))) (.classMem (.cv y) F)))
        (synWex b (synWa (.classEq (.cv z) (synCop (.cv x) (.cv b))) (.classMem (.cv z) F))))
      (synWex a (synWex b (synWa
            (synWa (.classEq (.cv y) (synCop (.cv x) (.cv a))) (.classMem (.cv y) F))
            (synWa (.classEq (.cv z) (synCop (.cv x) (.cv b))) (.classMem (.cv z) F)))))
      p0022 p0023
  have p0025 :=
    @gAn4 (.classEq (.cv y) (synCop (.cv x) (.cv a))) (.classMem (.cv y) F)
      (.classEq (.cv z) (synCop (.cv x) (.cv b))) (.classMem (.cv z) F)
  have p0026 :=
    @gDffun4 x a b F dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012
      dv_cache_0013 dv_cache_0014
  have p0027 :=
    @gSp
      (.imp (synWa (.classMem (synCop (.cv x) (.cv a)) F)
          (.classMem (synCop (.cv x) (.cv b)) F)) (.objEq a b))
      b
  have p0028 :=
    @gSps
      (.all b (.imp (synWa (.classMem (synCop (.cv x) (.cv a)) F)
            (.classMem (synCop (.cv x) (.cv b)) F)) (.objEq a b)))
      (.imp (synWa (.classMem (synCop (.cv x) (.cv a)) F)
          (.classMem (synCop (.cv x) (.cv b)) F)) (.objEq a b))
      a p0027
  have p0029 :=
    @gSps
      (.all a (.all b (.imp (synWa (.classMem (synCop (.cv x) (.cv a)) F)
              (.classMem (synCop (.cv x) (.cv b)) F)) (.objEq a b))))
      (.imp (synWa (.classMem (synCop (.cv x) (.cv a)) F)
          (.classMem (synCop (.cv x) (.cv b)) F)) (.objEq a b))
      x p0028
  have p0030 :=
    @gSylbi (synWfun F)
      (.all x (.all a (.all b (.imp (synWa (.classMem (synCop (.cv x) (.cv a)) F)
                (.classMem (synCop (.cv x) (.cv b)) F)) (.objEq a b)))))
      (.imp (synWa (.classMem (synCop (.cv x) (.cv a)) F)
          (.classMem (synCop (.cv x) (.cv b)) F)) (.objEq a b))
      p0026 p0029
  have p0031 := @gOpeq2 (.cv a) (.cv b) (.cv x)
  have p0032_e01_recanon :
    Nominal.NPrf
      (.imp (.objEq a b) (.classEq (synCop (.cv x) (.cv a)) (synCop (.cv x) (.cv b)))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold synCop synCun synCnin synWnan synWa synCcompl synWrex synWex
          synCphi
        simp (config :=
          { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_class_cv]
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
        · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0031
  have p0032 :=
    @gSyl6 (synWfun F)
      (synWa (.classMem (synCop (.cv x) (.cv a)) F) (.classMem (synCop (.cv x) (.cv b)) F))
      (.objEq a b) (.classEq (synCop (.cv x) (.cv a)) (synCop (.cv x) (.cv b))) p0030
      p0032_e01_recanon
  have p0033 := @gEleq1 (.cv y) (synCop (.cv x) (.cv a)) F
  have p0034 := @gEleq1 (.cv z) (synCop (.cv x) (.cv b)) F
  have p0035 :=
    @gBi2anan9 (.classEq (.cv y) (synCop (.cv x) (.cv a))) (.classMem (.cv y) F)
      (.classMem (synCop (.cv x) (.cv a)) F) (.classEq (.cv z) (synCop (.cv x) (.cv b)))
      (.classMem (.cv z) F) (.classMem (synCop (.cv x) (.cv b)) F) p0033 p0034
  have p0036 :=
    @gEqeq12 (.cv y) (synCop (.cv x) (.cv a)) (.cv z) (synCop (.cv x) (.cv b))
  have p0037_e01_recanon :
    Nominal.NPrf
      (.imp (synWa (.classEq (.cv y) (synCop (.cv x) (.cv a)))
          (.classEq (.cv z) (synCop (.cv x) (.cv b)))) (synWb (.objEq y z)
          (.classEq (synCop (.cv x) (.cv a)) (synCop (.cv x) (.cv b))))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold synWa synCop synCun synCnin synWnan synCcompl synWrex synWex
          synCphi synWb
        simp (config :=
          { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_class_cv]
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · exact Nominal.RecanonTransportDev.TRecanonWff.same _
        · apply Nominal.RecanonTransportDev.TRecanonWff.neg
          apply Nominal.RecanonTransportDev.TRecanonWff.imp
          · apply Nominal.RecanonTransportDev.TRecanonWff.imp
            · exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
            · exact Nominal.RecanonTransportDev.TRecanonWff.same _
          · apply Nominal.RecanonTransportDev.TRecanonWff.neg
            apply Nominal.RecanonTransportDev.TRecanonWff.imp
            · exact Nominal.RecanonTransportDev.TRecanonWff.same _
            · exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _)
      p0036
  have p0037 :=
    @gImbi12d
      (synWa (.classEq (.cv y) (synCop (.cv x) (.cv a)))
        (.classEq (.cv z) (synCop (.cv x) (.cv b))))
      (synWa (.classMem (.cv y) F) (.classMem (.cv z) F))
      (synWa (.classMem (synCop (.cv x) (.cv a)) F) (.classMem (synCop (.cv x) (.cv b)) F))
      (.objEq y z) (.classEq (synCop (.cv x) (.cv a)) (synCop (.cv x) (.cv b))) p0035
      p0037_e01_recanon
  have p0038 :=
    @gBiimprcd
      (synWa (.classEq (.cv y) (synCop (.cv x) (.cv a)))
        (.classEq (.cv z) (synCop (.cv x) (.cv b))))
      (.imp (synWa (.classMem (.cv y) F) (.classMem (.cv z) F)) (.objEq y z))
      (.imp (synWa (.classMem (synCop (.cv x) (.cv a)) F)
          (.classMem (synCop (.cv x) (.cv b)) F))
        (.classEq (synCop (.cv x) (.cv a)) (synCop (.cv x) (.cv b))))
      p0037
  have p0039 :=
    @gImp3a
      (.imp (synWa (.classMem (synCop (.cv x) (.cv a)) F)
          (.classMem (synCop (.cv x) (.cv b)) F))
        (.classEq (synCop (.cv x) (.cv a)) (synCop (.cv x) (.cv b))))
      (synWa (.classEq (.cv y) (synCop (.cv x) (.cv a)))
        (.classEq (.cv z) (synCop (.cv x) (.cv b))))
      (synWa (.classMem (.cv y) F) (.classMem (.cv z) F)) (.objEq y z) p0038
  have p0040 :=
    @gSyl (synWfun F)
      (.imp (synWa (.classMem (synCop (.cv x) (.cv a)) F)
          (.classMem (synCop (.cv x) (.cv b)) F))
        (.classEq (synCop (.cv x) (.cv a)) (synCop (.cv x) (.cv b))))
      (.imp (synWa (synWa (.classEq (.cv y) (synCop (.cv x) (.cv a)))
            (.classEq (.cv z) (synCop (.cv x) (.cv b))))
          (synWa (.classMem (.cv y) F) (.classMem (.cv z) F))) (.objEq y z))
      p0032 p0039
  have p0041 :=
    @gSyl5bi
      (synWa (synWa (.classEq (.cv y) (synCop (.cv x) (.cv a))) (.classMem (.cv y) F))
        (synWa (.classEq (.cv z) (synCop (.cv x) (.cv b))) (.classMem (.cv z) F)))
      (synWa (synWa (.classEq (.cv y) (synCop (.cv x) (.cv a)))
          (.classEq (.cv z) (synCop (.cv x) (.cv b))))
        (synWa (.classMem (.cv y) F) (.classMem (.cv z) F)))
      (synWfun F) (.objEq y z) p0025 p0040
  have p0042 :=
    @gExlimdvv (synWfun F)
      (synWa (synWa (.classEq (.cv y) (synCop (.cv x) (.cv a))) (.classMem (.cv y) F))
        (synWa (.classEq (.cv z) (synCop (.cv x) (.cv b))) (.classMem (.cv z) F)))
      (.objEq y z) a b dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 p0041
  have p0043 :=
    @gSyl5bi
      (synWa (synWbr (.cv x) (synCcnv (synCres (synC1st) F)) (.cv y))
        (synWbr (.cv x) (synCcnv (synCres (synC1st) F)) (.cv z)))
      (synWex a (synWex b (synWa
            (synWa (.classEq (.cv y) (synCop (.cv x) (.cv a))) (.classMem (.cv y) F))
            (synWa (.classEq (.cv z) (synCop (.cv x) (.cv b))) (.classMem (.cv z) F)))))
      (synWfun F) (.objEq y z) p0024 p0042
  have p0044 :=
    @gAlrimiv (synWfun F)
      (.imp (synWa (synWbr (.cv x) (synCcnv (synCres (synC1st) F)) (.cv y))
          (synWbr (.cv x) (synCcnv (synCres (synC1st) F)) (.cv z))) (.objEq y z))
      z dv_cache_0019 p0043
  have p0045 :=
    @gAlrimivv (synWfun F)
      (.all z (.imp (synWa (synWbr (.cv x) (synCcnv (synCres (synC1st) F)) (.cv y))
            (synWbr (.cv x) (synCcnv (synCres (synC1st) F)) (.cv z))) (.objEq y z)))
      x y dv_cache_0020 dv_cache_0021 p0044
  have p0046 :=
    @gDffun2 x y z (synCcnv (synCres (synC1st) F)) dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027
  have p0047 :=
    @gSylibr (synWfun F)
      (.all x (.all y (.all z (.imp
              (synWa (synWbr (.cv x) (synCcnv (synCres (synC1st) F)) (.cv y))
                (synWbr (.cv x) (synCcnv (synCres (synC1st) F)) (.cv z))) (.objEq y z)))))
      (synWfun (synCcnv (synCres (synC1st) F))) p0045 p0046
  have p0048 := @gDfdm4 F
  have p0049 := @gDfima3 (synC1st) F
  have p0050 :=
    @gEqtr2i (synCdm F) (synCima (synC1st) F) (synCrn (synCres (synC1st) F)) p0048
      p0049
  have p0051 :=
    @gA1i (.classEq (synCrn (synCres (synC1st) F)) (synCdm F)) (synWfun F) p0050
  have p0052 := @gDff1o2 F (synCdm F) (synCres (synC1st) F)
  have p0053 :=
    @gSyl3anbrc (synWfun F) (synWfn (synCres (synC1st) F) F)
      (synWfun (synCcnv (synCres (synC1st) F)))
      (.classEq (synCrn (synCres (synC1st) F)) (synCdm F))
      (synWf1o (synCres (synC1st) F) F (synCdm F)) p0006 p0047 p0051 p0052
  have p0054 := @gN1stex
  have p0055 := @gResex (synC1st) F p0054 hyp_fundmen_1
  have p0056 := @gF1oen F (synCdm F) (synCres (synC1st) F) p0055
  have p0057 :=
    @gSyl (synWfun F) (synWf1o (synCres (synC1st) F) F (synCdm F))
      (synWbr F (synCen) (synCdm F)) p0053 p0056
  have p0058 := @gEnsym F (synCdm F)
  have p0059 :=
    @gSylib (synWfun F) (synWbr F (synCen) (synCdm F))
      (synWbr (synCdm F) (synCen) F) p0057 p0058
  exact p0059

/-- Checked nominal proof certificate identified upstream as `g_en2sn`. -/
@[expose]
noncomputable def gEn2sn (A : Class) (B : Class) (C : Class) (D : Class) :
    Nominal.NPrf
      (.imp (synWa (.classMem A C) (.classMem B D))
        (synWbr (synCsn A) (synCen) (synCsn B))) :=
  by
  have p0000 := @gF1osng A B C D
  have p0001 := @gSnex (synCop A B)
  have p0002 := @gF1oen (synCsn A) (synCsn B) (synCsn (synCop A B)) p0001
  have p0003 :=
    @gSyl (synWa (.classMem A C) (.classMem B D))
      (synWf1o (synCsn (synCop A B)) (synCsn A) (synCsn B))
      (synWbr (synCsn A) (synCen) (synCsn B)) p0000 p0002
  exact p0003


end NFChoice.DirectNominalPrf.WPPReplay

end

/-! Certificates from `NominalWPPReplayChunk013Compact001Part033`. -/


section

namespace NFChoice.DirectNominalPrf.WPPReplay

open scoped Fol
open NFChoice.Foundation
open NFChoice.SemanticCore
open NFChoice.ReplaySupport
open NFChoice.Compiler.CompactSourceSyntax

/-- Checked nominal proof certificate identified upstream as `g_unen`. -/
@[expose]
noncomputable def gUnen (A : Class) (B : Class) (C : Class) (D : Class) :
    Nominal.NPrf
      (.imp (synWa (synWa (synWbr A (synCen) B) (synWbr C (synCen) D))
          (synWa (.classEq (synCin A C) (synC0)) (.classEq (synCin B D) (synC0))))
        (synWbr (synCun A C) (synCen) (synCun B D))) :=
  by
  let proofSupport : Finset Var := A.fv ∪ B.fv ∪ C.fv ∪ D.fv
  let f : Var := freshVar proofSupport 0
  let g : Var := freshVar proofSupport 1
  let h : Var := freshVar proofSupport 2
  have fresh_f : f ∉ proofSupport :=
    by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_f_not_A : f ∉ A.fv := by
    intro h
    exact
      fresh_f
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (h))))
  have fresh_f_not_B : f ∉ B.fv := by
    intro h
    exact
      fresh_f
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))
  have fresh_f_not_C : f ∉ C.fv := by
    intro h
    exact fresh_f (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_f_not_D : f ∉ D.fv := by
    intro h
    exact fresh_f (Finset.mem_union_right _ (h))
  have fresh_g : g ∉ proofSupport :=
    by
    change freshVar proofSupport 1 ∉ proofSupport
    exact freshVar_not_mem proofSupport 1
  have fresh_g_not_A : g ∉ A.fv := by
    intro h
    exact
      fresh_g
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (h))))
  have fresh_g_not_B : g ∉ B.fv := by
    intro h
    exact
      fresh_g
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))
  have fresh_g_not_C : g ∉ C.fv := by
    intro h
    exact fresh_g (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_g_not_D : g ∉ D.fv := by
    intro h
    exact fresh_g (Finset.mem_union_right _ (h))
  have fresh_h : h ∉ proofSupport :=
    by
    change freshVar proofSupport 2 ∉ proofSupport
    exact freshVar_not_mem proofSupport 2
  have fresh_h_not_A : h ∉ A.fv := by
    intro h
    exact
      fresh_h
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (h))))
  have fresh_h_not_B : h ∉ B.fv := by
    intro h
    exact
      fresh_h
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))
  have fresh_h_not_C : h ∉ C.fv := by
    intro h
    exact fresh_h (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_h_not_D : h ∉ D.fv := by
    intro h
    exact fresh_h (Finset.mem_union_right _ (h))
  have fresh_f_ne_g : f ≠ g :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have fresh_g_ne_f : g ≠ f := Ne.symm fresh_f_ne_g
  have fresh_f_ne_h : f ≠ h :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 2
    exact freshVar_injective proofSupport (i := 0) (j := 2) (by decide)
  have fresh_h_ne_f : h ≠ f := Ne.symm fresh_f_ne_h
  have fresh_g_ne_h : g ≠ h :=
    by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 2
    exact freshVar_injective proofSupport (i := 1) (j := 2) (by decide)
  have fresh_h_ne_g : h ≠ g := Ne.symm fresh_g_ne_h
  have dv_cache_0001 : h ∉ ((synCun (.cv f) (.cv g))).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : h ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cun,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, fresh_h_ne_f, fresh_h_ne_g, or_false, not_false_eq_true])
  have dv_cache_0002 :
    h ∉ ((synWf1o (synCun (.cv f) (.cv g)) (synCun A C) (synCun B D))).fv :=
    by
    clear dv_cache_0001
    exact
      (by
        have compact_fv_not_mem_empty : h ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wf1o,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cun,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, fresh_h_not_A, fresh_h_not_C, fresh_h_not_B,
          fresh_h_not_D, fresh_h_ne_f, fresh_h_ne_g, or_false, not_false_eq_true])
  have dv_cache_0003 :
    f ∉
      ((Wff.imp (synWa (.classEq (synCin A C) (synC0)) (.classEq (synCin B D) (synC0)))
          (synWex h (synWf1o (.cv h) (synCun A C) (synCun B D))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact
      (by
        have compact_fv_not_mem_empty : f ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wex,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wf1o,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cun, Finset.mem_union,
          Finset.mem_erase, Finset.mem_singleton, fresh_f_not_A, fresh_f_not_C,
          fresh_f_not_B, fresh_f_not_D, fresh_f_ne_h, compact_fv_not_mem_empty, or_false,
          and_false, not_false_eq_true])
  have dv_cache_0004 :
    g ∉
      ((Wff.imp (synWa (.classEq (synCin A C) (synC0)) (.classEq (synCin B D) (synC0)))
          (synWex h (synWf1o (.cv h) (synCun A C) (synCun B D))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact
      (by
        have compact_fv_not_mem_empty : g ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wex,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wf1o,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cun, Finset.mem_union,
          Finset.mem_erase, Finset.mem_singleton, fresh_g_not_A, fresh_g_not_C,
          fresh_g_not_B, fresh_g_not_D, fresh_g_ne_h, compact_fv_not_mem_empty, or_false,
          and_false, not_false_eq_true])
  have dv_cache_0005 : f ∉ (A).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact
      (by
        have compact_fv_not_mem_empty : f ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_f_not_A, not_false_eq_true])
  have dv_cache_0006 : f ∉ (B).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact
      (by
        have compact_fv_not_mem_empty : f ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_f_not_B, not_false_eq_true])
  have dv_cache_0007 : g ∉ (C).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006
    exact
      (by
        have compact_fv_not_mem_empty : g ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_g_not_C, not_false_eq_true])
  have dv_cache_0008 : g ∉ (D).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007
    exact
      (by
        have compact_fv_not_mem_empty : g ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_g_not_D, not_false_eq_true])
  have dv_cache_0009 : g ∉ ((synWf1o (.cv f) A B)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008
    exact
      (by
        have compact_fv_not_mem_empty : g ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wf1o,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, fresh_g_not_A, fresh_g_not_B, fresh_g_ne_f, or_false,
          not_false_eq_true])
  have dv_cache_0010 : f ∉ ((synWf1o (.cv g) C D)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009
    exact
      (by
        have compact_fv_not_mem_empty : f ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wf1o,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, fresh_f_not_C, fresh_f_not_D, fresh_f_ne_g, or_false,
          not_false_eq_true])
  have dv_cache_0011 : h ∉ ((synCun A C)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010
    exact
      (by
        have compact_fv_not_mem_empty : h ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cun, Finset.mem_union,
          fresh_h_not_A, fresh_h_not_C, or_false, not_false_eq_true])
  have dv_cache_0012 : h ∉ ((synCun B D)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
    exact
      (by
        have compact_fv_not_mem_empty : h ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cun, Finset.mem_union,
          fresh_h_not_B, fresh_h_not_D, or_false, not_false_eq_true])
  have p0000 := @gF1oun A B C D (.cv f) (.cv g)
  have p0001 := @gVex f
  have p0002 := @gVex g
  have p0003 := @gUnex (.cv f) (.cv g) p0001 p0002
  have p0004 := @gF1oeq1 (synCun A C) (synCun B D) (.cv h) (synCun (.cv f) (.cv g))
  have p0005 :=
    @gSpcev (synWf1o (.cv h) (synCun A C) (synCun B D))
      (synWf1o (synCun (.cv f) (.cv g)) (synCun A C) (synCun B D)) h
      (synCun (.cv f) (.cv g)) dv_cache_0001 dv_cache_0002 p0003 p0004
  have p0006 :=
    @gSyl
      (synWa (synWa (synWf1o (.cv f) A B) (synWf1o (.cv g) C D))
        (synWa (.classEq (synCin A C) (synC0)) (.classEq (synCin B D) (synC0))))
      (synWf1o (synCun (.cv f) (.cv g)) (synCun A C) (synCun B D))
      (synWex h (synWf1o (.cv h) (synCun A C) (synCun B D))) p0000 p0005
  have p0007 :=
    @gEx (synWa (synWf1o (.cv f) A B) (synWf1o (.cv g) C D))
      (synWa (.classEq (synCin A C) (synC0)) (.classEq (synCin B D) (synC0)))
      (synWex h (synWf1o (.cv h) (synCun A C) (synCun B D))) p0006
  have p0008 :=
    @gExlimivv (synWa (synWf1o (.cv f) A B) (synWf1o (.cv g) C D))
      (.imp (synWa (.classEq (synCin A C) (synC0)) (.classEq (synCin B D) (synC0)))
        (synWex h (synWf1o (.cv h) (synCun A C) (synCun B D))))
      f g dv_cache_0003 dv_cache_0004 p0007
  have p0009 :=
    @gImp (synWex f (synWex g (synWa (synWf1o (.cv f) A B) (synWf1o (.cv g) C D))))
      (synWa (.classEq (synCin A C) (synC0)) (.classEq (synCin B D) (synC0)))
      (synWex h (synWf1o (.cv h) (synCun A C) (synCun B D))) p0008
  have p0010 := @gBren A B f dv_cache_0005 dv_cache_0006
  have p0011 := @gBren C D g dv_cache_0007 dv_cache_0008
  have p0012 :=
    @gAnbi12i (synWbr A (synCen) B) (synWex f (synWf1o (.cv f) A B))
      (synWbr C (synCen) D) (synWex g (synWf1o (.cv g) C D)) p0010 p0011
  have p0013 :=
    @gEeanv (synWf1o (.cv f) A B) (synWf1o (.cv g) C D) f g dv_cache_0009 dv_cache_0010
  have p0014 :=
    @gBitr4i (synWa (synWbr A (synCen) B) (synWbr C (synCen) D))
      (synWa (synWex f (synWf1o (.cv f) A B)) (synWex g (synWf1o (.cv g) C D)))
      (synWex f (synWex g (synWa (synWf1o (.cv f) A B) (synWf1o (.cv g) C D)))) p0012
      p0013
  have p0015 :=
    @gAnbi1i (synWa (synWbr A (synCen) B) (synWbr C (synCen) D))
      (synWex f (synWex g (synWa (synWf1o (.cv f) A B) (synWf1o (.cv g) C D))))
      (synWa (.classEq (synCin A C) (synC0)) (.classEq (synCin B D) (synC0))) p0014
  have p0016 := @gBren (synCun A C) (synCun B D) h dv_cache_0011 dv_cache_0012
  have p0017 :=
    @gN3imtr4i
      (synWa (synWex f (synWex g (synWa (synWf1o (.cv f) A B) (synWf1o (.cv g) C D))))
        (synWa (.classEq (synCin A C) (synC0)) (.classEq (synCin B D) (synC0))))
      (synWex h (synWf1o (.cv h) (synCun A C) (synCun B D)))
      (synWa (synWa (synWbr A (synCen) B) (synWbr C (synCen) D))
        (synWa (.classEq (synCin A C) (synC0)) (.classEq (synCin B D) (synC0))))
      (synWbr (synCun A C) (synCen) (synCun B D)) p0009 p0015 p0016
  exact p0017

/-- Checked nominal proof certificate identified upstream as `g_xpsnen`. -/
@[expose]
noncomputable def gXpsnen (A : Class) (B : Class)
    (hyp_xpsnen_1 : Nominal.NPrf (.classMem A (synCvv)))
    (hyp_xpsnen_2 : Nominal.NPrf (.classMem B (synCvv))) :
    Nominal.NPrf (synWbr (synCxp A (synCsn B)) (synCen) A) :=
  by
  have p0000 := @gSnid B hyp_xpsnen_2
  have p0001 := @gNe0i (synCsn B) B
  have p0002 := @gDmxp A (synCsn B)
  have p0003 :=
    @gMp2b (.classMem B (synCsn B)) (synWne (synCsn B) (synC0))
      (.classEq (synCdm (synCxp A (synCsn B))) A) p0000 p0001 p0002
  have p0004 := @gFconst A B hyp_xpsnen_2
  have p0005 := @gFfun A (synCsn B) (synCxp A (synCsn B))
  have p0006 := @gSnex B
  have p0007 := @gXpex A (synCsn B) hyp_xpsnen_1 p0006
  have p0008 := @gFundmen (synCxp A (synCsn B)) p0007
  have p0009 :=
    @gMp2b (synWf (synCxp A (synCsn B)) A (synCsn B))
      (synWfun (synCxp A (synCsn B)))
      (synWbr (synCdm (synCxp A (synCsn B))) (synCen) (synCxp A (synCsn B))) p0004
      p0005 p0008
  have p0010 :=
    @gEqbrtrri (synCdm (synCxp A (synCsn B))) A (synCxp A (synCsn B)) (synCen)
      p0003 p0009
  have p0011 := @gEnsym A (synCxp A (synCsn B))
  have p0012 :=
    @gMpbi (synWbr A (synCen) (synCxp A (synCsn B)))
      (synWbr (synCxp A (synCsn B)) (synCen) A) p0010 p0011
  exact p0012

/-- Checked nominal proof certificate identified upstream as `g_xpcomen`. -/
@[expose]
noncomputable def gXpcomen (A : Class) (B : Class)
    (hyp_xpcomen_1 : Nominal.NPrf (.classMem A (synCvv)))
    (hyp_xpcomen_2 : Nominal.NPrf (.classMem B (synCvv))) :
    Nominal.NPrf (synWbr (synCxp A B) (synCen) (synCxp B A)) :=
  by
  have p0000 := @gSwapres (synCxp A B)
  have p0001 := @gCnvxp A B
  have p0002 :=
    @gF1oeq3 (synCcnv (synCxp A B)) (synCxp B A) (synCxp A B)
      (synCres (synCswap) (synCxp A B))
  have p0003 := Nominal.mp p0001 p0002
  have p0004 :=
    @gMpbi
      (synWf1o (synCres (synCswap) (synCxp A B)) (synCxp A B) (synCcnv (synCxp A B)))
      (synWf1o (synCres (synCswap) (synCxp A B)) (synCxp A B) (synCxp B A)) p0000
      p0003
  have p0005 := @gSwapex
  have p0006 := @gXpex A B hyp_xpcomen_1 hyp_xpcomen_2
  have p0007 := @gResex (synCswap) (synCxp A B) p0005 p0006
  have p0008 :=
    @gF1oen (synCxp A B) (synCxp B A) (synCres (synCswap) (synCxp A B)) p0007
  have p0009 := Nominal.mp p0004 p0008
  exact p0009

/-- Checked nominal proof certificate identified upstream as `g_xpen`. -/
@[expose]
noncomputable def gXpen (A : Class) (B : Class) (C : Class) (D : Class) :
    Nominal.NPrf
      (.imp (synWa (synWbr A (synCen) B) (synWbr C (synCen) D))
        (synWbr (synCxp A C) (synCen) (synCxp B D))) :=
  by
  let proofSupport : Finset Var := A.fv ∪ B.fv ∪ C.fv ∪ D.fv
  let f : Var := freshVar proofSupport 0
  let g : Var := freshVar proofSupport 1
  have fresh_f : f ∉ proofSupport :=
    by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_f_not_A : f ∉ A.fv := by
    intro h
    exact
      fresh_f
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (h))))
  have fresh_f_not_B : f ∉ B.fv := by
    intro h
    exact
      fresh_f
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))
  have fresh_f_not_C : f ∉ C.fv := by
    intro h
    exact fresh_f (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_f_not_D : f ∉ D.fv := by
    intro h
    exact fresh_f (Finset.mem_union_right _ (h))
  have fresh_g : g ∉ proofSupport :=
    by
    change freshVar proofSupport 1 ∉ proofSupport
    exact freshVar_not_mem proofSupport 1
  have fresh_g_not_A : g ∉ A.fv := by
    intro h
    exact
      fresh_g
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (h))))
  have fresh_g_not_B : g ∉ B.fv := by
    intro h
    exact
      fresh_g
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))
  have fresh_g_not_C : g ∉ C.fv := by
    intro h
    exact fresh_g (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_g_not_D : g ∉ D.fv := by
    intro h
    exact fresh_g (Finset.mem_union_right _ (h))
  have fresh_f_ne_g : f ≠ g :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have fresh_g_ne_f : g ≠ f := Ne.symm fresh_f_ne_g
  have dv_cache_0001 : f ∉ (A).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : f ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_f_not_A, not_false_eq_true])
  have dv_cache_0002 : f ∉ (B).fv :=
    by
    clear dv_cache_0001
    exact
      (by
        have compact_fv_not_mem_empty : f ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_f_not_B, not_false_eq_true])
  have dv_cache_0003 : g ∉ (C).fv :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact
      (by
        have compact_fv_not_mem_empty : g ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_g_not_C, not_false_eq_true])
  have dv_cache_0004 : g ∉ (D).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact
      (by
        have compact_fv_not_mem_empty : g ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_g_not_D, not_false_eq_true])
  have dv_cache_0005 : g ∉ ((synWf1o (.cv f) A B)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact
      (by
        have compact_fv_not_mem_empty : g ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wf1o,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, fresh_g_not_A, fresh_g_not_B, fresh_g_ne_f, or_false,
          not_false_eq_true])
  have dv_cache_0006 : f ∉ ((synWf1o (.cv g) C D)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact
      (by
        have compact_fv_not_mem_empty : f ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wf1o,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, fresh_f_not_C, fresh_f_not_D, fresh_f_ne_g, or_false,
          not_false_eq_true])
  have dv_cache_0007 : f ∉ ((synWbr (synCxp A C) (synCen) (synCxp B D))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006
    exact
      (by
        have compact_fv_not_mem_empty : f ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxp,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cen, Finset.mem_union,
          fresh_f_not_A, fresh_f_not_C, fresh_f_not_B, fresh_f_not_D,
          compact_fv_not_mem_empty, or_false, not_false_eq_true])
  have dv_cache_0008 : g ∉ ((synWbr (synCxp A C) (synCen) (synCxp B D))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007
    exact
      (by
        have compact_fv_not_mem_empty : g ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxp,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cen, Finset.mem_union,
          fresh_g_not_A, fresh_g_not_C, fresh_g_not_B, fresh_g_not_D,
          compact_fv_not_mem_empty, or_false, not_false_eq_true])
  have p0000 := @gBren A B f dv_cache_0001 dv_cache_0002
  have p0001 := @gBren C D g dv_cache_0003 dv_cache_0004
  have p0002 :=
    @gAnbi12i (synWbr A (synCen) B) (synWex f (synWf1o (.cv f) A B))
      (synWbr C (synCen) D) (synWex g (synWf1o (.cv g) C D)) p0000 p0001
  have p0003 :=
    @gEeanv (synWf1o (.cv f) A B) (synWf1o (.cv g) C D) f g dv_cache_0005 dv_cache_0006
  have p0004 :=
    @gBitr4i (synWa (synWbr A (synCen) B) (synWbr C (synCen) D))
      (synWa (synWex f (synWf1o (.cv f) A B)) (synWex g (synWf1o (.cv g) C D)))
      (synWex f (synWex g (synWa (synWf1o (.cv f) A B) (synWf1o (.cv g) C D)))) p0002
      p0003
  have p0005 := @gF1opprod A C B D (.cv f) (.cv g)
  have p0006 := @gVex f
  have p0007 := @gVex g
  have p0008 := @gPprodex (.cv f) (.cv g) p0006 p0007
  have p0009 := @gF1oen (synCxp A C) (synCxp B D) (synCpprod (.cv f) (.cv g)) p0008
  have p0010 :=
    @gSyl (synWa (synWf1o (.cv f) A B) (synWf1o (.cv g) C D))
      (synWf1o (synCpprod (.cv f) (.cv g)) (synCxp A C) (synCxp B D))
      (synWbr (synCxp A C) (synCen) (synCxp B D)) p0005 p0009
  have p0011 :=
    @gExlimivv (synWa (synWf1o (.cv f) A B) (synWf1o (.cv g) C D))
      (synWbr (synCxp A C) (synCen) (synCxp B D)) f g dv_cache_0007 dv_cache_0008
      p0010
  have p0012 :=
    @gSylbi (synWa (synWbr A (synCen) B) (synWbr C (synCen) D))
      (synWex f (synWex g (synWa (synWf1o (.cv f) A B) (synWf1o (.cv g) C D))))
      (synWbr (synCxp A C) (synCen) (synCxp B D)) p0004 p0011
  exact p0012


end NFChoice.DirectNominalPrf.WPPReplay

end
