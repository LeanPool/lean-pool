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

@[expose]
noncomputable def g_erth (ph : Wff) (A : Class) (B : Class) (R : Class) (V : Class)
    (X : Class) (hyp_erth_1 : Nominal.NPrf (.imp ph (syn_wbr R (syn_cer) (syn_cvv))))
    (hyp_erth_2 : Nominal.NPrf (.imp ph (.classEq (syn_cdm R) X)))
    (hyp_erth_3 : Nominal.NPrf (.imp ph (.classMem A X)))
    (hyp_erth_4 : Nominal.NPrf (.imp ph (.classMem B V))) :
    Nominal.NPrf
      (.imp ph (syn_wb (syn_wbr A R B) (.classEq (syn_cec A R) (syn_cec B R)))) :=
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
  have dv_cache_0001 : x ∉ ((syn_wa ph (syn_wbr A R B))).fv := by
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
    @g_adantr ph (syn_wbr R (syn_cer) (syn_cvv))
      (syn_wa (syn_wbr A R B) (syn_wbr A R (.cv x))) hyp_erth_1
  have p0001 := @g_elex B V
  have p0002 := @g_syl ph (.classMem B V) (.classMem B (syn_cvv)) hyp_erth_4 p0001
  have p0003 :=
    @g_adantr ph (.classMem B (syn_cvv)) (syn_wa (syn_wbr A R B) (syn_wbr A R (.cv x)))
      p0002
  have p0004 := @g_elex A X
  have p0005 := @g_syl ph (.classMem A X) (.classMem A (syn_cvv)) hyp_erth_3 p0004
  have p0006 :=
    @g_adantr ph (.classMem A (syn_cvv)) (syn_wa (syn_wbr A R B) (syn_wbr A R (.cv x)))
      p0005
  have p0007 := @g_vex x
  have p0008 :=
    @g_a1i (.classMem (.cv x) (syn_cvv))
      (syn_wa ph (syn_wa (syn_wbr A R B) (syn_wbr A R (.cv x)))) p0007
  have p0009 := @g_simprl ph (syn_wbr A R B) (syn_wbr A R (.cv x))
  have p0010 := @g_simprr ph (syn_wbr A R B) (syn_wbr A R (.cv x))
  have p0011 :=
    @g_ertr3d (syn_wa ph (syn_wa (syn_wbr A R B) (syn_wbr A R (.cv x)))) (syn_cvv) R B A
      (.cv x) p0000 p0003 p0006 p0008 p0009 p0010
  have p0012 :=
    @g_expr ph (syn_wbr A R B) (syn_wbr A R (.cv x)) (syn_wbr B R (.cv x)) p0011
  have p0013 := @g_a1i (.classMem (.cv x) (syn_cvv)) ph p0007
  have p0014 := @g_ertr ph (syn_cvv) R A B (.cv x) hyp_erth_1 p0005 p0002 p0013
  have p0015 :=
    @g_expdimp ph (syn_wbr A R B) (syn_wbr B R (.cv x)) (syn_wbr A R (.cv x)) p0014
  have p0016 :=
    @g_impbid (syn_wa ph (syn_wbr A R B)) (syn_wbr A R (.cv x)) (syn_wbr B R (.cv x))
      p0012 p0015
  have p0017 :=
    @g_abbidv (syn_wa ph (syn_wbr A R B)) (syn_wbr A R (.cv x)) (syn_wbr B R (.cv x)) x
      dv_cache_0001 p0016
  have p0018 := @g_dfec2 x A R dv_cache_0002 dv_cache_0003
  have p0019 := @g_dfec2 x B R dv_cache_0004 dv_cache_0003
  have p0020 :=
    @g_n_3eqtr4g (syn_wa ph (syn_wbr A R B)) (.cab x (syn_wbr A R (.cv x)))
      (.cab x (syn_wbr B R (.cv x))) (syn_cec A R) (syn_cec B R) p0017 p0018 p0019
  have p0021 :=
    @g_adantr ph (syn_wbr R (syn_cer) (syn_cvv)) (.classEq (syn_cec A R) (syn_cec B R))
      hyp_erth_1
  have p0022 := @g_simpl ph (.classEq (syn_cec A R) (syn_cec B R))
  have p0023 :=
    @g_n_3syl (syn_wa ph (.classEq (syn_cec A R) (syn_cec B R))) ph (.classMem B V)
      (.classMem B (syn_cvv)) p0022 hyp_erth_4 p0001
  have p0024 :=
    @g_n_3syl (syn_wa ph (.classEq (syn_cec A R) (syn_cec B R))) ph (.classMem A X)
      (.classMem A (syn_cvv)) p0022 hyp_erth_3 p0004
  have p0025 := @g_erref ph X R A hyp_erth_1 hyp_erth_2 hyp_erth_3
  have p0026 := @g_elec A A R
  have p0027 := @g_sylibr ph (syn_wbr A R A) (.classMem A (syn_cec A R)) p0025 p0026
  have p0028 := @g_eleq2 (syn_cec A R) (syn_cec B R) A
  have p0029 :=
    @g_syl5ibcom ph (.classMem A (syn_cec A R)) (.classEq (syn_cec A R) (syn_cec B R))
      (.classMem A (syn_cec B R)) p0027 p0028
  have p0030 :=
    @g_imp ph (.classEq (syn_cec A R) (syn_cec B R)) (.classMem A (syn_cec B R)) p0029
  have p0031 := @g_elec A B R
  have p0032 :=
    @g_sylib (syn_wa ph (.classEq (syn_cec A R) (syn_cec B R)))
      (.classMem A (syn_cec B R)) (syn_wbr B R A) p0030 p0031
  have p0033 :=
    @g_ersym (syn_wa ph (.classEq (syn_cec A R) (syn_cec B R))) (syn_cvv) R B A p0021
      p0023 p0024 p0032
  have p0034 :=
    @g_impbida ph (syn_wbr A R B) (.classEq (syn_cec A R) (syn_cec B R)) p0020 p0033
  exact p0034

@[expose]
noncomputable def g_erth2 (ph : Wff) (A : Class) (B : Class) (R : Class) (V : Class)
    (X : Class) (hyp_erth2_1 : Nominal.NPrf (.imp ph (syn_wbr R (syn_cer) (syn_cvv))))
    (hyp_erth2_2 : Nominal.NPrf (.imp ph (.classEq (syn_cdm R) X)))
    (hyp_erth2_3 : Nominal.NPrf (.imp ph (.classMem A V)))
    (hyp_erth2_4 : Nominal.NPrf (.imp ph (.classMem B X))) :
    Nominal.NPrf
      (.imp ph (syn_wb (syn_wbr A R B) (.classEq (syn_cec A R) (syn_cec B R)))) :=
  by
  have p0000 := @g_elex A V
  have p0001 := @g_syl ph (.classMem A V) (.classMem A (syn_cvv)) hyp_erth2_3 p0000
  have p0002 := @g_elex B X
  have p0003 := @g_syl ph (.classMem B X) (.classMem B (syn_cvv)) hyp_erth2_4 p0002
  have p0004 := @g_ersymb ph (syn_cvv) R A B hyp_erth2_1 p0001 p0003
  have p0005 := @g_erth ph B A R V X hyp_erth2_1 hyp_erth2_2 hyp_erth2_4 hyp_erth2_3
  have p0006 := @g_eqcom (syn_cec B R) (syn_cec A R)
  have p0007 :=
    @g_syl6bb ph (syn_wbr B R A) (.classEq (syn_cec B R) (syn_cec A R))
      (.classEq (syn_cec A R) (syn_cec B R)) p0005 p0006
  have p0008 :=
    @g_bitrd ph (syn_wbr A R B) (syn_wbr B R A) (.classEq (syn_cec A R) (syn_cec B R))
      p0004 p0007
  exact p0008

@[expose]
noncomputable def g_erthi (ph : Wff) (A : Class) (B : Class) (R : Class)
    (hyp_erthi_1 : Nominal.NPrf (.imp ph (syn_wbr R (syn_cer) (syn_cvv))))
    (hyp_erthi_4 : Nominal.NPrf (.imp ph (syn_wbr A R B))) :
    Nominal.NPrf (.imp ph (.classEq (syn_cec A R) (syn_cec B R))) :=
  by
  have p0000 := @g_eqidd ph (syn_cdm R)
  have p0001 := @g_breldm A B R
  have p0002 := @g_syl ph (syn_wbr A R B) (.classMem A (syn_cdm R)) hyp_erthi_4 p0001
  have p0003 := @g_brelrn A B R
  have p0004 := @g_syl ph (syn_wbr A R B) (.classMem B (syn_crn R)) hyp_erthi_4 p0003
  have p0005 := @g_erth ph A B R (syn_crn R) (syn_cdm R) hyp_erthi_1 p0000 p0002 p0004
  have p0006 :=
    @g_mpbid ph (syn_wbr A R B) (.classEq (syn_cec A R) (syn_cec B R)) hyp_erthi_4 p0005
  exact p0006

@[expose]
noncomputable def g_erdisj (A : Class) (B : Class) (R : Class) :
    Nominal.NPrf
      (.imp (syn_wbr R (syn_cer) (syn_cvv)) (syn_wo (.classEq (syn_cec A R) (syn_cec B R))
          (.classEq (syn_cin (syn_cec A R) (syn_cec B R)) (syn_c0)))) :=
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
  have dv_cache_0001 : x ∉ ((syn_cin (syn_cec A R) (syn_cec B R))).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cec, Finset.mem_union,
          fresh_x_not_A, fresh_x_not_R, fresh_x_not_B, or_false, not_false_eq_true])
  have dv_cache_0002 : x ∉ ((Wff.classEq (syn_cec A R) (syn_cec B R))).fv :=
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
  have dv_cache_0003 : x ∉ ((syn_wbr R (syn_cer) (syn_cvv))).fv :=
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
  have p0000 := @g_neq0 x (syn_cin (syn_cec A R) (syn_cec B R)) dv_cache_0001
  have p0001 :=
    @g_simpl (syn_wbr R (syn_cer) (syn_cvv))
      (.classMem (.cv x) (syn_cin (syn_cec A R) (syn_cec B R)))
  have p0002 := @g_inss1 (syn_cec A R) (syn_cec B R)
  have p0003 := @g_sseli (syn_cin (syn_cec A R) (syn_cec B R)) (syn_cec A R) (.cv x) p0002
  have p0004 :=
    @g_adantl (.classMem (.cv x) (syn_cin (syn_cec A R) (syn_cec B R)))
      (.classMem (.cv x) (syn_cec A R)) (syn_wbr R (syn_cer) (syn_cvv)) p0003
  have p0005 := @g_ecexr (.cv x) A R
  have p0006 :=
    @g_syl
      (syn_wa (syn_wbr R (syn_cer) (syn_cvv))
        (.classMem (.cv x) (syn_cin (syn_cec A R) (syn_cec B R))))
      (.classMem (.cv x) (syn_cec A R)) (.classMem A (syn_cvv)) p0004 p0005
  have p0007 := @g_vex x
  have p0008 :=
    @g_a1i (.classMem (.cv x) (syn_cvv))
      (syn_wa (syn_wbr R (syn_cer) (syn_cvv))
        (.classMem (.cv x) (syn_cin (syn_cec A R) (syn_cec B R))))
      p0007
  have p0009 := @g_inss2 (syn_cec A R) (syn_cec B R)
  have p0010 := @g_sseli (syn_cin (syn_cec A R) (syn_cec B R)) (syn_cec B R) (.cv x) p0009
  have p0011 :=
    @g_adantl (.classMem (.cv x) (syn_cin (syn_cec A R) (syn_cec B R)))
      (.classMem (.cv x) (syn_cec B R)) (syn_wbr R (syn_cer) (syn_cvv)) p0010
  have p0012 := @g_ecexr (.cv x) B R
  have p0013 :=
    @g_syl
      (syn_wa (syn_wbr R (syn_cer) (syn_cvv))
        (.classMem (.cv x) (syn_cin (syn_cec A R) (syn_cec B R))))
      (.classMem (.cv x) (syn_cec B R)) (.classMem B (syn_cvv)) p0011 p0012
  have p0014 := @g_elec (.cv x) A R
  have p0015 :=
    @g_sylib (.classMem (.cv x) (syn_cin (syn_cec A R) (syn_cec B R)))
      (.classMem (.cv x) (syn_cec A R)) (syn_wbr A R (.cv x)) p0003 p0014
  have p0016 :=
    @g_adantl (.classMem (.cv x) (syn_cin (syn_cec A R) (syn_cec B R)))
      (syn_wbr A R (.cv x)) (syn_wbr R (syn_cer) (syn_cvv)) p0015
  have p0017 := @g_elec (.cv x) B R
  have p0018 :=
    @g_sylib (.classMem (.cv x) (syn_cin (syn_cec A R) (syn_cec B R)))
      (.classMem (.cv x) (syn_cec B R)) (syn_wbr B R (.cv x)) p0010 p0017
  have p0019 :=
    @g_adantl (.classMem (.cv x) (syn_cin (syn_cec A R) (syn_cec B R)))
      (syn_wbr B R (.cv x)) (syn_wbr R (syn_cer) (syn_cvv)) p0018
  have p0020 :=
    @g_ertr4d
      (syn_wa (syn_wbr R (syn_cer) (syn_cvv))
        (.classMem (.cv x) (syn_cin (syn_cec A R) (syn_cec B R))))
      (syn_cvv) R A (.cv x) B p0001 p0006 p0008 p0013 p0016 p0019
  have p0021 :=
    @g_erthi
      (syn_wa (syn_wbr R (syn_cer) (syn_cvv))
        (.classMem (.cv x) (syn_cin (syn_cec A R) (syn_cec B R))))
      A B R p0001 p0020
  have p0022 :=
    @g_ex (syn_wbr R (syn_cer) (syn_cvv))
      (.classMem (.cv x) (syn_cin (syn_cec A R) (syn_cec B R)))
      (.classEq (syn_cec A R) (syn_cec B R)) p0021
  have p0023 :=
    @g_exlimdv (syn_wbr R (syn_cer) (syn_cvv))
      (.classMem (.cv x) (syn_cin (syn_cec A R) (syn_cec B R)))
      (.classEq (syn_cec A R) (syn_cec B R)) x dv_cache_0002 dv_cache_0003 p0022
  have p0024 :=
    @g_syl5bi (.neg (.classEq (syn_cin (syn_cec A R) (syn_cec B R)) (syn_c0)))
      (syn_wex x (.classMem (.cv x) (syn_cin (syn_cec A R) (syn_cec B R))))
      (syn_wbr R (syn_cer) (syn_cvv)) (.classEq (syn_cec A R) (syn_cec B R)) p0000 p0023
  have p0025 :=
    @g_orrd (syn_wbr R (syn_cer) (syn_cvv))
      (.classEq (syn_cin (syn_cec A R) (syn_cec B R)) (syn_c0))
      (.classEq (syn_cec A R) (syn_cec B R)) p0024
  have p0026 :=
    @g_orcomd (syn_wbr R (syn_cer) (syn_cvv))
      (.classEq (syn_cin (syn_cec A R) (syn_cec B R)) (syn_c0))
      (.classEq (syn_cec A R) (syn_cec B R)) p0025
  exact p0026

@[expose]
noncomputable def g_qseq1 (A : Class) (B : Class) (C : Class) :
    Nominal.NPrf (.imp (.classEq A B) (.classEq (syn_cqs A C) (syn_cqs B C))) :=
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
    @g_rexeq (.classEq (.cv y) (syn_cec (.cv x) C)) x A B dv_cache_0001 dv_cache_0002
  have p0001 :=
    @g_abbidv (.classEq A B) (syn_wrex x A (.classEq (.cv y) (syn_cec (.cv x) C)))
      (syn_wrex x B (.classEq (.cv y) (syn_cec (.cv x) C))) y dv_cache_0003 p0000
  have p0002 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominal_df_qs x y A C
      dv_cache_0001 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007
  have p0003 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominal_df_qs x y B C
      dv_cache_0002 dv_cache_0008 dv_cache_0005 dv_cache_0006 dv_cache_0007
  have p0004 :=
    @g_n_3eqtr4g (.classEq A B)
      (.cab y (syn_wrex x A (.classEq (.cv y) (syn_cec (.cv x) C))))
      (.cab y (syn_wrex x B (.classEq (.cv y) (syn_cec (.cv x) C)))) (syn_cqs A C)
      (syn_cqs B C) p0001 p0002 p0003
  exact p0004

@[expose]
noncomputable def g_qseq2 (A : Class) (B : Class) (C : Class) :
    Nominal.NPrf (.imp (.classEq A B) (.classEq (syn_cqs C A) (syn_cqs C B))) :=
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
  have p0000 := @g_eceq2 A B (.cv x)
  have p0001 :=
    @g_eqeq2d (.classEq A B) (syn_cec (.cv x) A) (syn_cec (.cv x) B) (.cv y) p0000
  have p0002 :=
    @g_rexbidv (.classEq A B) (.classEq (.cv y) (syn_cec (.cv x) A))
      (.classEq (.cv y) (syn_cec (.cv x) B)) x C dv_cache_0001 p0001
  have p0003 :=
    @g_abbidv (.classEq A B) (syn_wrex x C (.classEq (.cv y) (syn_cec (.cv x) A)))
      (syn_wrex x C (.classEq (.cv y) (syn_cec (.cv x) B))) y dv_cache_0002 p0002
  have p0004 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominal_df_qs x y C A
      dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007
  have p0005 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominal_df_qs x y C B
      dv_cache_0003 dv_cache_0004 dv_cache_0008 dv_cache_0009 dv_cache_0007
  have p0006 :=
    @g_n_3eqtr4g (.classEq A B)
      (.cab y (syn_wrex x C (.classEq (.cv y) (syn_cec (.cv x) A))))
      (.cab y (syn_wrex x C (.classEq (.cv y) (syn_cec (.cv x) B)))) (syn_cqs C A)
      (syn_cqs C B) p0003 p0004 p0005
  exact p0006

@[expose]
noncomputable def g_elqsg (x : Var) (A : Class) (B : Class) (R : Class) (V : Class)
    (dv_A_x : x ∉ A.fv) (dv_B_x : x ∉ B.fv) (dv_R_x : x ∉ R.fv) :
    Nominal.NPrf
      (.imp (.classMem B V) (syn_wb (.classMem B (syn_cqs A R))
          (syn_wrex x A (.classEq B (syn_cec (.cv x) R))))) :=
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
  have dv_cache_0008 : y ∉ ((syn_wrex x A (.classEq B (syn_cec (.cv x) R)))).fv :=
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
  have p0000 := @g_eqeq1 (.cv y) B (syn_cec (.cv x) R)
  have p0001 :=
    @g_rexbidv (.classEq (.cv y) B) (.classEq (.cv y) (syn_cec (.cv x) R))
      (.classEq B (syn_cec (.cv x) R)) x A dv_cache_0001 p0000
  have p0002 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominal_df_qs x y A R
      dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006
  have p0003 :=
    @g_elab2g (syn_wrex x A (.classEq (.cv y) (syn_cec (.cv x) R)))
      (syn_wrex x A (.classEq B (syn_cec (.cv x) R))) y B (syn_cqs A R) V dv_cache_0007
      dv_cache_0008 p0001 p0002
  exact p0003

@[expose]
noncomputable def g_elqs (x : Var) (A : Class) (B : Class) (R : Class) (dv_A_x : x ∉ A.fv)
    (dv_B_x : x ∉ B.fv) (dv_R_x : x ∉ R.fv)
    (hyp_elqs_1 : Nominal.NPrf (.classMem B (syn_cvv))) :
    Nominal.NPrf
      (syn_wb (.classMem B (syn_cqs A R)) (syn_wrex x A (.classEq B (syn_cec (.cv x) R)))) :=
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
  have p0000 := @g_elqsg x A B R (syn_cvv) dv_cache_0001 dv_cache_0002 dv_cache_0003
  have p0001 := Nominal.mp hyp_elqs_1 p0000
  exact p0001

@[expose]
noncomputable def g_elqsi (x : Var) (A : Class) (B : Class) (R : Class)
    (dv_A_x : x ∉ A.fv) (dv_B_x : x ∉ B.fv) (dv_R_x : x ∉ R.fv) :
    Nominal.NPrf
      (.imp (.classMem B (syn_cqs A R)) (syn_wrex x A (.classEq B (syn_cec (.cv x) R)))) :=
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
  have p0000 := @g_elqsg x A B R (syn_cqs A R) dv_cache_0001 dv_cache_0002 dv_cache_0003
  have p0001 :=
    @g_ibi (.classMem B (syn_cqs A R)) (syn_wrex x A (.classEq B (syn_cec (.cv x) R)))
      p0000
  exact p0001

@[expose]
noncomputable def g_ecelqsg (A : Class) (B : Class) (R : Class) (V : Class) :
    Nominal.NPrf
      (.imp (syn_wa (.classMem R V) (.classMem B A)) (.classMem (syn_cec B R) (syn_cqs A R))) :=
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
  have dv_cache_0003 : x ∉ ((Wff.classEq (syn_cec B R) (syn_cec B R))).fv :=
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
  have dv_cache_0004 : x ∉ ((syn_cec B R)).fv :=
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
  have p0000 := @g_eqid (syn_cec B R)
  have p0001 := @g_eceq1 (.cv x) B R
  have p0002 :=
    @g_eqeq2d (.classEq (.cv x) B) (syn_cec (.cv x) R) (syn_cec B R) (syn_cec B R) p0001
  have p0003 :=
    @g_rspcev (.classEq (syn_cec B R) (syn_cec (.cv x) R))
      (.classEq (syn_cec B R) (syn_cec B R)) x B A dv_cache_0001 dv_cache_0002
      dv_cache_0003 p0002
  have p0004 :=
    @g_mpan2 (.classMem B A) (.classEq (syn_cec B R) (syn_cec B R))
      (syn_wrex x A (.classEq (syn_cec B R) (syn_cec (.cv x) R))) p0000 p0003
  have p0005 := @g_ecexg B V R
  have p0006 :=
    @g_elqsg x A (syn_cec B R) R (syn_cvv) dv_cache_0002 dv_cache_0004 dv_cache_0005
  have p0007 :=
    @g_syl (.classMem R V) (.classMem (syn_cec B R) (syn_cvv))
      (syn_wb (.classMem (syn_cec B R) (syn_cqs A R))
        (syn_wrex x A (.classEq (syn_cec B R) (syn_cec (.cv x) R))))
      p0005 p0006
  have p0008 :=
    @g_biimpar (.classMem R V) (.classMem (syn_cec B R) (syn_cqs A R))
      (syn_wrex x A (.classEq (syn_cec B R) (syn_cec (.cv x) R))) p0007
  have p0009 :=
    @g_sylan2 (.classMem B A) (.classMem R V)
      (syn_wrex x A (.classEq (syn_cec B R) (syn_cec (.cv x) R)))
      (.classMem (syn_cec B R) (syn_cqs A R)) p0004 p0008
  exact p0009

@[expose]
noncomputable def g_ecelqsi (A : Class) (B : Class) (R : Class)
    (hyp_ecelqsi_1 : Nominal.NPrf (.classMem R (syn_cvv))) :
    Nominal.NPrf (.imp (.classMem B A) (.classMem (syn_cec B R) (syn_cqs A R))) :=
  by
  have p0000 := @g_ecelqsg A B R (syn_cvv)
  have p0001 :=
    @g_mpan (.classMem R (syn_cvv)) (.classMem B A)
      (.classMem (syn_cec B R) (syn_cqs A R)) hyp_ecelqsi_1 p0000
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

@[expose]
noncomputable def g_qsexg (A : Class) (R : Class) (V : Class) (W : Class) :
    Nominal.NPrf
      (.imp (syn_wa (.classMem R V) (.classMem A W)) (.classMem (syn_cqs A R) (syn_cvv))) :=
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
      ((syn_ccompl (syn_cima
            (syn_csymdif (syn_cins2 (syn_csset)) (syn_cins3 (syn_csi (syn_ccnv R))))
            (syn_c1c)))).fv :=
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
  have dv_cache_0008 : z ∉ ((syn_cop (syn_csn (.cv y)) (.cv x))).fv :=
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
    z ∉ ((syn_csymdif (syn_cins2 (syn_csset)) (syn_cins3 (syn_csi (syn_ccnv R))))).fv :=
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
  have dv_cache_0011 : z ∉ ((syn_cec (.cv y) R)).fv :=
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
      ((syn_cima (syn_ccompl (syn_cima
              (syn_csymdif (syn_cins2 (syn_csset)) (syn_cins3 (syn_csi (syn_ccnv R))))
              (syn_c1c))) (syn_cpw1 A))).fv :=
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
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominal_df_qs y x A R
      dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
  have p0001 :=
    @g_elimapw1 y (.cv x)
      (syn_ccompl
        (syn_cima (syn_csymdif (syn_cins2 (syn_csset)) (syn_cins3 (syn_csi (syn_ccnv R))))
          (syn_c1c)))
      A dv_cache_0006 dv_cache_0007 dv_cache_0001
  have p0002 :=
    @g_elima1c z (syn_cop (syn_csn (.cv y)) (.cv x))
      (syn_csymdif (syn_cins2 (syn_csset)) (syn_cins3 (syn_csi (syn_ccnv R))))
      dv_cache_0008 dv_cache_0009
  have p0003 :=
    @g_elsymdif (syn_cop (syn_csn (.cv z)) (syn_cop (syn_csn (.cv y)) (.cv x)))
      (syn_cins2 (syn_csset)) (syn_cins3 (syn_csi (syn_ccnv R)))
  have p0004 := @g_snex (.cv y)
  have p0005 := @g_otelins2 (syn_csn (.cv z)) (syn_csn (.cv y)) (.cv x) (syn_csset) p0004
  have p0006 := @g_vex z
  have p0007 := @g_vex x
  have p0008 := @g_opelssetsn (.cv z) (.cv x) p0006 p0007
  have p0009_e01_recanon :
    Nominal.NPrf
      (syn_wb (.classMem (syn_cop (syn_csn (.cv z)) (.cv x)) (syn_csset)) (.objMem z x)) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wb syn_cop syn_cun syn_cnin syn_wnan syn_wa syn_ccompl syn_wrex syn_wex
          syn_cphi syn_csn syn_csset syn_copab syn_wss syn_cin
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
    @g_bitri
      (.classMem (syn_cop (syn_csn (.cv z)) (syn_cop (syn_csn (.cv y)) (.cv x)))
        (syn_cins2 (syn_csset)))
      (.classMem (syn_cop (syn_csn (.cv z)) (.cv x)) (syn_csset)) (.objMem z x) p0005
      p0009_e01_recanon
  have p0010 :=
    @g_otelins3 (syn_csn (.cv z)) (syn_csn (.cv y)) (.cv x) (syn_csi (syn_ccnv R)) p0007
  have p0011 := (Nominal.biimpRefl (syn_wbr (.cv z) (syn_ccnv R) (.cv y)))
  have p0012 := @g_brcnv (.cv z) (.cv y) R
  have p0013 :=
    @g_bitr3i (.classMem (syn_cop (.cv z) (.cv y)) (syn_ccnv R))
      (syn_wbr (.cv z) (syn_ccnv R) (.cv y)) (syn_wbr (.cv y) R (.cv z)) p0011 p0012
  have p0014 := @g_vex y
  have p0015 := @g_opsnelsi (.cv z) (.cv y) (syn_ccnv R) p0006 p0014
  have p0016 := @g_elec (.cv z) (.cv y) R
  have p0017 :=
    @g_n_3bitr4i (.classMem (syn_cop (.cv z) (.cv y)) (syn_ccnv R))
      (syn_wbr (.cv y) R (.cv z))
      (.classMem (syn_cop (syn_csn (.cv z)) (syn_csn (.cv y))) (syn_csi (syn_ccnv R)))
      (.classMem (.cv z) (syn_cec (.cv y) R)) p0013 p0015 p0016
  have p0018 :=
    @g_bitri
      (.classMem (syn_cop (syn_csn (.cv z)) (syn_cop (syn_csn (.cv y)) (.cv x)))
        (syn_cins3 (syn_csi (syn_ccnv R))))
      (.classMem (syn_cop (syn_csn (.cv z)) (syn_csn (.cv y))) (syn_csi (syn_ccnv R)))
      (.classMem (.cv z) (syn_cec (.cv y) R)) p0010 p0017
  have p0019 :=
    @g_bibi12i
      (.classMem (syn_cop (syn_csn (.cv z)) (syn_cop (syn_csn (.cv y)) (.cv x)))
        (syn_cins2 (syn_csset)))
      (.objMem z x)
      (.classMem (syn_cop (syn_csn (.cv z)) (syn_cop (syn_csn (.cv y)) (.cv x)))
        (syn_cins3 (syn_csi (syn_ccnv R))))
      (.classMem (.cv z) (syn_cec (.cv y) R)) p0009 p0018
  have p0020 :=
    @g_notbii
      (syn_wb (.classMem (syn_cop (syn_csn (.cv z)) (syn_cop (syn_csn (.cv y)) (.cv x)))
          (syn_cins2 (syn_csset)))
        (.classMem (syn_cop (syn_csn (.cv z)) (syn_cop (syn_csn (.cv y)) (.cv x)))
          (syn_cins3 (syn_csi (syn_ccnv R)))))
      (syn_wb (.objMem z x) (.classMem (.cv z) (syn_cec (.cv y) R))) p0019
  have p0021 :=
    @g_bitri
      (.classMem (syn_cop (syn_csn (.cv z)) (syn_cop (syn_csn (.cv y)) (.cv x)))
        (syn_csymdif (syn_cins2 (syn_csset)) (syn_cins3 (syn_csi (syn_ccnv R)))))
      (.neg (syn_wb (.classMem (syn_cop (syn_csn (.cv z)) (syn_cop (syn_csn (.cv y)) (.cv x)))
            (syn_cins2 (syn_csset)))
          (.classMem (syn_cop (syn_csn (.cv z)) (syn_cop (syn_csn (.cv y)) (.cv x)))
            (syn_cins3 (syn_csi (syn_ccnv R))))))
      (.neg (syn_wb (.objMem z x) (.classMem (.cv z) (syn_cec (.cv y) R)))) p0003 p0020
  have p0022 :=
    @g_exbii
      (.classMem (syn_cop (syn_csn (.cv z)) (syn_cop (syn_csn (.cv y)) (.cv x)))
        (syn_csymdif (syn_cins2 (syn_csset)) (syn_cins3 (syn_csi (syn_ccnv R)))))
      (.neg (syn_wb (.objMem z x) (.classMem (.cv z) (syn_cec (.cv y) R)))) z p0021
  have p0023 :=
    @g_bitri
      (.classMem (syn_cop (syn_csn (.cv y)) (.cv x))
        (syn_cima (syn_csymdif (syn_cins2 (syn_csset)) (syn_cins3 (syn_csi (syn_ccnv R))))
          (syn_c1c)))
      (syn_wex z (.classMem (syn_cop (syn_csn (.cv z)) (syn_cop (syn_csn (.cv y)) (.cv x)))
          (syn_csymdif (syn_cins2 (syn_csset)) (syn_cins3 (syn_csi (syn_ccnv R))))))
      (syn_wex z (.neg (syn_wb (.objMem z x) (.classMem (.cv z) (syn_cec (.cv y) R)))))
      p0002 p0022
  have p0024 :=
    @g_notbii
      (.classMem (syn_cop (syn_csn (.cv y)) (.cv x))
        (syn_cima (syn_csymdif (syn_cins2 (syn_csset)) (syn_cins3 (syn_csi (syn_ccnv R))))
          (syn_c1c)))
      (syn_wex z (.neg (syn_wb (.objMem z x) (.classMem (.cv z) (syn_cec (.cv y) R)))))
      p0023
  have p0025 := @g_opex (syn_csn (.cv y)) (.cv x) p0004 p0007
  have p0026 :=
    @g_elcompl (syn_cop (syn_csn (.cv y)) (.cv x))
      (syn_cima (syn_csymdif (syn_cins2 (syn_csset)) (syn_cins3 (syn_csi (syn_ccnv R))))
        (syn_c1c))
      p0025
  have p0027 := @g_alex (syn_wb (.objMem z x) (.classMem (.cv z) (syn_cec (.cv y) R))) z
  have p0028 :=
    @g_n_3bitr4i
      (.neg (.classMem (syn_cop (syn_csn (.cv y)) (.cv x)) (syn_cima
            (syn_csymdif (syn_cins2 (syn_csset)) (syn_cins3 (syn_csi (syn_ccnv R))))
            (syn_c1c))))
      (.neg (syn_wex z (.neg (syn_wb (.objMem z x) (.classMem (.cv z) (syn_cec (.cv y) R))))))
      (.classMem (syn_cop (syn_csn (.cv y)) (.cv x)) (syn_ccompl (syn_cima
            (syn_csymdif (syn_cins2 (syn_csset)) (syn_cins3 (syn_csi (syn_ccnv R))))
            (syn_c1c))))
      (.all z (syn_wb (.objMem z x) (.classMem (.cv z) (syn_cec (.cv y) R)))) p0024 p0026
      p0027
  have p0029 := @g_dfcleq z (.cv x) (syn_cec (.cv y) R) dv_cache_0010 dv_cache_0011
  have p0030_e01_recanon :
    Nominal.NPrf
      (syn_wb (.classEq (.cv x) (syn_cec (.cv y) R))
        (.all z (syn_wb (.objMem z x) (.classMem (.cv z) (syn_cec (.cv y) R))))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wb syn_cec syn_cima syn_wrex syn_wex syn_wa syn_wbr syn_cop syn_cun
          syn_cnin syn_wnan syn_ccompl syn_csn
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
    @g_bitr4i
      (.classMem (syn_cop (syn_csn (.cv y)) (.cv x)) (syn_ccompl (syn_cima
            (syn_csymdif (syn_cins2 (syn_csset)) (syn_cins3 (syn_csi (syn_ccnv R))))
            (syn_c1c))))
      (.all z (syn_wb (.objMem z x) (.classMem (.cv z) (syn_cec (.cv y) R))))
      (.classEq (.cv x) (syn_cec (.cv y) R)) p0028 p0030_e01_recanon
  have p0031 :=
    @g_rexbii
      (.classMem (syn_cop (syn_csn (.cv y)) (.cv x)) (syn_ccompl (syn_cima
            (syn_csymdif (syn_cins2 (syn_csset)) (syn_cins3 (syn_csi (syn_ccnv R))))
            (syn_c1c))))
      (.classEq (.cv x) (syn_cec (.cv y) R)) y A p0030
  have p0032 :=
    @g_bitri
      (.classMem (.cv x) (syn_cima (syn_ccompl (syn_cima
              (syn_csymdif (syn_cins2 (syn_csset)) (syn_cins3 (syn_csi (syn_ccnv R))))
              (syn_c1c))) (syn_cpw1 A)))
      (syn_wrex y A (.classMem (syn_cop (syn_csn (.cv y)) (.cv x)) (syn_ccompl (syn_cima
              (syn_csymdif (syn_cins2 (syn_csset)) (syn_cins3 (syn_csi (syn_ccnv R))))
              (syn_c1c)))))
      (syn_wrex y A (.classEq (.cv x) (syn_cec (.cv y) R))) p0001 p0031
  have p0033 :=
    @g_eqabi (syn_wrex y A (.classEq (.cv x) (syn_cec (.cv y) R))) x
      (syn_cima (syn_ccompl (syn_cima
            (syn_csymdif (syn_cins2 (syn_csset)) (syn_cins3 (syn_csi (syn_ccnv R)))) (syn_c1c)))
        (syn_cpw1 A))
      dv_cache_0012 p0032
  have p0034 :=
    @g_eqtr4i (syn_cqs A R) (.cab x (syn_wrex y A (.classEq (.cv x) (syn_cec (.cv y) R))))
      (syn_cima (syn_ccompl (syn_cima
            (syn_csymdif (syn_cins2 (syn_csset)) (syn_cins3 (syn_csi (syn_ccnv R)))) (syn_c1c)))
        (syn_cpw1 A))
      p0000 p0033
  have p0035 := @g_ssetex
  have p0036 := @g_ins2ex (syn_csset) p0035
  have p0037 := @g_cnvexg R V
  have p0038 := @g_siexg (syn_ccnv R) (syn_cvv)
  have p0039 := @g_ins3exg (syn_csi (syn_ccnv R)) (syn_cvv)
  have p0040 :=
    @g_n_3syl (.classMem R V) (.classMem (syn_ccnv R) (syn_cvv))
      (.classMem (syn_csi (syn_ccnv R)) (syn_cvv))
      (.classMem (syn_cins3 (syn_csi (syn_ccnv R))) (syn_cvv)) p0037 p0038 p0039
  have p0041 :=
    @g_symdifexg (syn_cins2 (syn_csset)) (syn_cins3 (syn_csi (syn_ccnv R))) (syn_cvv)
      (syn_cvv)
  have p0042 :=
    @g_sylancr (.classMem R V) (.classMem (syn_cins2 (syn_csset)) (syn_cvv))
      (.classMem (syn_cins3 (syn_csi (syn_ccnv R))) (syn_cvv))
      (.classMem (syn_csymdif (syn_cins2 (syn_csset)) (syn_cins3 (syn_csi (syn_ccnv R))))
        (syn_cvv))
      p0036 p0040 p0041
  have p0043 := @g_n_1cex
  have p0044 :=
    @g_imaexg (syn_csymdif (syn_cins2 (syn_csset)) (syn_cins3 (syn_csi (syn_ccnv R))))
      (syn_c1c) (syn_cvv) (syn_cvv)
  have p0045 :=
    @g_sylancl (.classMem R V)
      (.classMem (syn_csymdif (syn_cins2 (syn_csset)) (syn_cins3 (syn_csi (syn_ccnv R))))
        (syn_cvv))
      (.classMem (syn_c1c) (syn_cvv))
      (.classMem
        (syn_cima (syn_csymdif (syn_cins2 (syn_csset)) (syn_cins3 (syn_csi (syn_ccnv R))))
          (syn_c1c)) (syn_cvv))
      p0042 p0043 p0044
  have p0046 :=
    @g_complexg
      (syn_cima (syn_csymdif (syn_cins2 (syn_csset)) (syn_cins3 (syn_csi (syn_ccnv R))))
        (syn_c1c))
      (syn_cvv)
  have p0047 :=
    @g_syl (.classMem R V)
      (.classMem
        (syn_cima (syn_csymdif (syn_cins2 (syn_csset)) (syn_cins3 (syn_csi (syn_ccnv R))))
          (syn_c1c)) (syn_cvv))
      (.classMem (syn_ccompl (syn_cima
            (syn_csymdif (syn_cins2 (syn_csset)) (syn_cins3 (syn_csi (syn_ccnv R)))) (syn_c1c)))
        (syn_cvv))
      p0045 p0046
  have p0048 := @g_pw1exg A W
  have p0049 :=
    @g_imaexg
      (syn_ccompl
        (syn_cima (syn_csymdif (syn_cins2 (syn_csset)) (syn_cins3 (syn_csi (syn_ccnv R))))
          (syn_c1c)))
      (syn_cpw1 A) (syn_cvv) (syn_cvv)
  have p0050 :=
    @g_syl2an (.classMem R V)
      (.classMem (syn_ccompl (syn_cima
            (syn_csymdif (syn_cins2 (syn_csset)) (syn_cins3 (syn_csi (syn_ccnv R)))) (syn_c1c)))
        (syn_cvv))
      (.classMem (syn_cpw1 A) (syn_cvv))
      (.classMem (syn_cima (syn_ccompl (syn_cima
              (syn_csymdif (syn_cins2 (syn_csset)) (syn_cins3 (syn_csi (syn_ccnv R))))
              (syn_c1c))) (syn_cpw1 A)) (syn_cvv))
      (.classMem A W) p0047 p0048 p0049
  have p0051 :=
    @g_syl5eqel (syn_wa (.classMem R V) (.classMem A W)) (syn_cqs A R)
      (syn_cima (syn_ccompl (syn_cima
            (syn_csymdif (syn_cins2 (syn_csset)) (syn_cins3 (syn_csi (syn_ccnv R)))) (syn_c1c)))
        (syn_cpw1 A))
      (syn_cvv) p0034 p0050
  exact p0051

@[expose]
noncomputable def g_qsex (A : Class) (R : Class)
    (hyp_qsex_1 : Nominal.NPrf (.classMem R (syn_cvv)))
    (hyp_qsex_2 : Nominal.NPrf (.classMem A (syn_cvv))) :
    Nominal.NPrf (.classMem (syn_cqs A R) (syn_cvv)) :=
  by
  have p0000 := @g_qsexg A R (syn_cvv) (syn_cvv)
  have p0001 :=
    @g_mp2an (.classMem R (syn_cvv)) (.classMem A (syn_cvv))
      (.classMem (syn_cqs A R) (syn_cvv)) hyp_qsex_1 hyp_qsex_2 p0000
  exact p0001

@[expose]
noncomputable def g_ectocld (ph : Wff) (ps : Wff) (ch : Wff) (x : Var) (A : Class)
    (B : Class) (R : Class) (S : Class) (dv_A_x : x ∉ A.fv) (dv_B_x : x ∉ B.fv)
    (dv_R_x : x ∉ R.fv) (dv_ch_x : x ∉ ch.fv) (dv_ps_x : x ∉ ps.fv)
    (hyp_ectocl_1 : Nominal.NPrf (.classEq S (syn_cqs B R)))
    (hyp_ectocl_2 : Nominal.NPrf (.imp (.classEq (syn_cec (.cv x) R) A) (syn_wb ph ps)))
    (hyp_ectocld_3 : Nominal.NPrf (.imp (syn_wa ch (.classMem (.cv x) B)) ph)) :
    Nominal.NPrf (.imp (syn_wa ch (.classMem A S)) ps) :=
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
  have p0000 := @g_elqsi x B A R dv_cache_0001 dv_cache_0002 dv_cache_0003
  have p0001 :=
    @g_eleq2s (syn_wrex x B (.classEq A (syn_cec (.cv x) R))) A (syn_cqs B R) S p0000
      hyp_ectocl_1
  have p0002 := @g_eqcoms (syn_wb ph ps) (syn_cec (.cv x) R) A hyp_ectocl_2
  have p0003 :=
    @g_syl5ibcom (syn_wa ch (.classMem (.cv x) B)) ph (.classEq A (syn_cec (.cv x) R)) ps
      hyp_ectocld_3 p0002
  have p0004 :=
    @g_rexlimdva ch (.classEq A (syn_cec (.cv x) R)) ps x B dv_cache_0004 dv_cache_0005
      p0003
  have p0005 :=
    @g_syl5 (.classMem A S) (syn_wrex x B (.classEq A (syn_cec (.cv x) R))) ch ps p0001
      p0004
  have p0006 := @g_imp ch (.classMem A S) ps p0005
  exact p0006

@[expose]
noncomputable def g_ectocl (ph : Wff) (ps : Wff) (x : Var) (A : Class) (B : Class)
    (R : Class) (S : Class) (dv_A_x : x ∉ A.fv) (dv_B_x : x ∉ B.fv) (dv_R_x : x ∉ R.fv)
    (dv_ps_x : x ∉ ps.fv) (hyp_ectocl_1 : Nominal.NPrf (.classEq S (syn_cqs B R)))
    (hyp_ectocl_2 : Nominal.NPrf (.imp (.classEq (syn_cec (.cv x) R) A) (syn_wb ph ps)))
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
  have dv_cache_0004 : x ∉ (syn_wtru).fv :=
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
  have p0000 := @g_tru
  have p0001 := @g_adantl (.classMem (.cv x) B) ph syn_wtru hyp_ectocl_3
  have p0002 :=
    @g_ectocld ph ps syn_wtru x A B R S dv_cache_0001 dv_cache_0002 dv_cache_0003
      dv_cache_0004 dv_cache_0005 hyp_ectocl_1 hyp_ectocl_2 p0001
  have p0003 := @g_mpan syn_wtru (.classMem A S) ps p0000 p0002
  exact p0003

@[expose]
noncomputable def g_elqsn0 (A : Class) (B : Class) (R : Class) :
    Nominal.NPrf
      (.imp (syn_wa (.classEq (syn_cdm R) A) (.classMem B (syn_cqs A R)))
        (syn_wne B (syn_c0))) :=
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
  have dv_cache_0004 : x ∉ ((Wff.classEq (syn_cdm R) A)).fv :=
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
  have dv_cache_0005 : x ∉ ((syn_wne B (syn_c0))).fv :=
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
  have p0000 := @g_eqid (syn_cqs A R)
  have p0001 := @g_neeq1 (syn_cec (.cv x) R) B (syn_c0)
  have p0002 := @g_eleq2 (syn_cdm R) A (.cv x)
  have p0003 :=
    @g_biimpar (.classEq (syn_cdm R) A) (.classMem (.cv x) (syn_cdm R))
      (.classMem (.cv x) A) p0002
  have p0004 := @g_ecdmn0 (.cv x) R
  have p0005 :=
    @g_sylib (syn_wa (.classEq (syn_cdm R) A) (.classMem (.cv x) A))
      (.classMem (.cv x) (syn_cdm R)) (syn_wne (syn_cec (.cv x) R) (syn_c0)) p0003 p0004
  have p0006 :=
    @g_ectocld (syn_wne (syn_cec (.cv x) R) (syn_c0)) (syn_wne B (syn_c0))
      (.classEq (syn_cdm R) A) x B A R (syn_cqs A R) dv_cache_0001 dv_cache_0002
      dv_cache_0003 dv_cache_0004 dv_cache_0005 p0000 p0001 p0005
  exact p0006

@[expose]
noncomputable def g_mapexi (A : Class) (B : Class) (f : Var) (dv_A_f : f ∉ A.fv)
    (dv_B_f : f ∉ B.fv) (hyp_mapexi_1 : Nominal.NPrf (.classMem A (syn_cvv)))
    (hyp_mapexi_2 : Nominal.NPrf (.classMem B (syn_cvv))) :
    Nominal.NPrf (.classMem (.cab f (syn_wf (.cv f) A B)) (syn_cvv)) :=
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
  have dv_cache_0002 : x ∉ ((syn_ccnv (syn_cimage (syn_c2nd)))).fv :=
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
  have dv_cache_0003 : x ∉ ((syn_cpw B)).fv :=
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
  have dv_cache_0004 : x ∉ ((syn_crn (.cv f))).fv :=
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
      ((syn_cin (syn_cin (syn_cfuns) (syn_cima (syn_ccnv (syn_cimage (syn_c1st))) (syn_csn A)))
          (syn_cima (syn_ccnv (syn_cimage (syn_c2nd))) (syn_cpw B)))).fv :=
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
    @g_elin (.cv f) (syn_cfuns) (syn_cima (syn_ccnv (syn_cimage (syn_c1st))) (syn_csn A))
  have p0001 := @g_vex f
  have p0002 := @g_elfuns (.cv f) p0001
  have p0003 := @g_elimasn (syn_ccnv (syn_cimage (syn_c1st))) A (.cv f)
  have p0004 := (Nominal.biimpRefl (syn_wbr A (syn_ccnv (syn_cimage (syn_c1st))) (.cv f)))
  have p0005 := @g_brcnv A (.cv f) (syn_cimage (syn_c1st))
  have p0006 := @g_brimage (.cv f) A (syn_c1st) p0001 hyp_mapexi_1
  have p0007 := @g_dfdm4 (.cv f)
  have p0008 := @g_eqeq2i (syn_cdm (.cv f)) (syn_cima (syn_c1st) (.cv f)) A p0007
  have p0009 := @g_eqcom A (syn_cdm (.cv f))
  have p0010 :=
    @g_n_3bitr2i (syn_wbr (.cv f) (syn_cimage (syn_c1st)) A)
      (.classEq A (syn_cima (syn_c1st) (.cv f))) (.classEq A (syn_cdm (.cv f)))
      (.classEq (syn_cdm (.cv f)) A) p0006 p0008 p0009
  have p0011 :=
    @g_bitri (syn_wbr A (syn_ccnv (syn_cimage (syn_c1st))) (.cv f))
      (syn_wbr (.cv f) (syn_cimage (syn_c1st)) A) (.classEq (syn_cdm (.cv f)) A) p0005
      p0010
  have p0012 :=
    @g_n_3bitr2i
      (.classMem (.cv f) (syn_cima (syn_ccnv (syn_cimage (syn_c1st))) (syn_csn A)))
      (.classMem (syn_cop A (.cv f)) (syn_ccnv (syn_cimage (syn_c1st))))
      (syn_wbr A (syn_ccnv (syn_cimage (syn_c1st))) (.cv f))
      (.classEq (syn_cdm (.cv f)) A) p0003 p0004 p0011
  have p0013 :=
    @g_anbi12i (.classMem (.cv f) (syn_cfuns)) (syn_wfun (.cv f))
      (.classMem (.cv f) (syn_cima (syn_ccnv (syn_cimage (syn_c1st))) (syn_csn A)))
      (.classEq (syn_cdm (.cv f)) A) p0002 p0012
  have p0014 :=
    @g_bitri
      (.classMem (.cv f)
        (syn_cin (syn_cfuns) (syn_cima (syn_ccnv (syn_cimage (syn_c1st))) (syn_csn A))))
      (syn_wa (.classMem (.cv f) (syn_cfuns))
        (.classMem (.cv f) (syn_cima (syn_ccnv (syn_cimage (syn_c1st))) (syn_csn A))))
      (syn_wa (syn_wfun (.cv f)) (.classEq (syn_cdm (.cv f)) A)) p0000 p0013
  have p0015 := @g_vex x
  have p0016 := @g_brimage (.cv f) (.cv x) (syn_c2nd) p0001 p0015
  have p0017 := @g_brcnv (.cv x) (.cv f) (syn_cimage (syn_c2nd))
  have p0018 := @g_dfrn5 (.cv f)
  have p0019 := @g_eqeq2i (syn_crn (.cv f)) (syn_cima (syn_c2nd) (.cv f)) (.cv x) p0018
  have p0020 :=
    @g_n_3bitr4i (syn_wbr (.cv f) (syn_cimage (syn_c2nd)) (.cv x))
      (.classEq (.cv x) (syn_cima (syn_c2nd) (.cv f)))
      (syn_wbr (.cv x) (syn_ccnv (syn_cimage (syn_c2nd))) (.cv f))
      (.classEq (.cv x) (syn_crn (.cv f))) p0016 p0017 p0019
  have p0021 :=
    @g_rexbii (syn_wbr (.cv x) (syn_ccnv (syn_cimage (syn_c2nd))) (.cv f))
      (.classEq (.cv x) (syn_crn (.cv f))) x (syn_cpw B) p0020
  have p0022 :=
    @g_elima x (.cv f) (syn_ccnv (syn_cimage (syn_c2nd))) (syn_cpw B) dv_cache_0001
      dv_cache_0002 dv_cache_0003
  have p0023 := @g_risset x (syn_crn (.cv f)) (syn_cpw B) dv_cache_0004 dv_cache_0003
  have p0024 :=
    @g_n_3bitr4i
      (syn_wrex x (syn_cpw B) (syn_wbr (.cv x) (syn_ccnv (syn_cimage (syn_c2nd))) (.cv f)))
      (syn_wrex x (syn_cpw B) (.classEq (.cv x) (syn_crn (.cv f))))
      (.classMem (.cv f) (syn_cima (syn_ccnv (syn_cimage (syn_c2nd))) (syn_cpw B)))
      (.classMem (syn_crn (.cv f)) (syn_cpw B)) p0021 p0022 p0023
  have p0025 := @g_rnex (.cv f) p0001
  have p0026 := @g_elpw (syn_crn (.cv f)) B p0025
  have p0027 :=
    @g_bitri (.classMem (.cv f) (syn_cima (syn_ccnv (syn_cimage (syn_c2nd))) (syn_cpw B)))
      (.classMem (syn_crn (.cv f)) (syn_cpw B)) (syn_wss (syn_crn (.cv f)) B) p0024 p0026
  have p0028 :=
    @g_anbi12i
      (.classMem (.cv f)
        (syn_cin (syn_cfuns) (syn_cima (syn_ccnv (syn_cimage (syn_c1st))) (syn_csn A))))
      (syn_wa (syn_wfun (.cv f)) (.classEq (syn_cdm (.cv f)) A))
      (.classMem (.cv f) (syn_cima (syn_ccnv (syn_cimage (syn_c2nd))) (syn_cpw B)))
      (syn_wss (syn_crn (.cv f)) B) p0014 p0027
  have p0029 :=
    @g_elin (.cv f)
      (syn_cin (syn_cfuns) (syn_cima (syn_ccnv (syn_cimage (syn_c1st))) (syn_csn A)))
      (syn_cima (syn_ccnv (syn_cimage (syn_c2nd))) (syn_cpw B))
  have p0030 := (Nominal.biimpRefl (syn_wf (.cv f) A B))
  have p0031 := (Nominal.biimpRefl (syn_wfn (.cv f) A))
  have p0032 :=
    @g_anbi1i (syn_wfn (.cv f) A)
      (syn_wa (syn_wfun (.cv f)) (.classEq (syn_cdm (.cv f)) A))
      (syn_wss (syn_crn (.cv f)) B) p0031
  have p0033 :=
    @g_bitri (syn_wf (.cv f) A B)
      (syn_wa (syn_wfn (.cv f) A) (syn_wss (syn_crn (.cv f)) B))
      (syn_wa (syn_wa (syn_wfun (.cv f)) (.classEq (syn_cdm (.cv f)) A))
        (syn_wss (syn_crn (.cv f)) B))
      p0030 p0032
  have p0034 :=
    @g_n_3bitr4i
      (syn_wa (.classMem (.cv f)
          (syn_cin (syn_cfuns) (syn_cima (syn_ccnv (syn_cimage (syn_c1st))) (syn_csn A))))
        (.classMem (.cv f) (syn_cima (syn_ccnv (syn_cimage (syn_c2nd))) (syn_cpw B))))
      (syn_wa (syn_wa (syn_wfun (.cv f)) (.classEq (syn_cdm (.cv f)) A))
        (syn_wss (syn_crn (.cv f)) B))
      (.classMem (.cv f) (syn_cin
          (syn_cin (syn_cfuns) (syn_cima (syn_ccnv (syn_cimage (syn_c1st))) (syn_csn A)))
          (syn_cima (syn_ccnv (syn_cimage (syn_c2nd))) (syn_cpw B))))
      (syn_wf (.cv f) A B) p0028 p0029 p0033
  have p0035 :=
    @g_eqabi (syn_wf (.cv f) A B) f
      (syn_cin (syn_cin (syn_cfuns) (syn_cima (syn_ccnv (syn_cimage (syn_c1st))) (syn_csn A)))
        (syn_cima (syn_ccnv (syn_cimage (syn_c2nd))) (syn_cpw B)))
      dv_cache_0005 p0034
  have p0036 := @g_funsex
  have p0037 := @g_n_1stex
  have p0038 := @g_imageex (syn_c1st) p0037
  have p0039 := @g_cnvex (syn_cimage (syn_c1st)) p0038
  have p0040 := @g_snex A
  have p0041 := @g_imaex (syn_ccnv (syn_cimage (syn_c1st))) (syn_csn A) p0039 p0040
  have p0042 :=
    @g_inex (syn_cfuns) (syn_cima (syn_ccnv (syn_cimage (syn_c1st))) (syn_csn A)) p0036
      p0041
  have p0043 := @g_n_2ndex
  have p0044 := @g_imageex (syn_c2nd) p0043
  have p0045 := @g_cnvex (syn_cimage (syn_c2nd)) p0044
  have p0046 := @g_pwex B hyp_mapexi_2
  have p0047 := @g_imaex (syn_ccnv (syn_cimage (syn_c2nd))) (syn_cpw B) p0045 p0046
  have p0048 :=
    @g_inex
      (syn_cin (syn_cfuns) (syn_cima (syn_ccnv (syn_cimage (syn_c1st))) (syn_csn A)))
      (syn_cima (syn_ccnv (syn_cimage (syn_c2nd))) (syn_cpw B)) p0042 p0047
  have p0049 :=
    @g_eqeltrri
      (syn_cin (syn_cin (syn_cfuns) (syn_cima (syn_ccnv (syn_cimage (syn_c1st))) (syn_csn A)))
        (syn_cima (syn_ccnv (syn_cimage (syn_c2nd))) (syn_cpw B)))
      (.cab f (syn_wf (.cv f) A B)) (syn_cvv) p0035 p0048
  exact p0049

@[expose]
noncomputable def g_mapex (A : Class) (B : Class) (C : Class) (D : Class) (f : Var)
    (dv_A_f : f ∉ A.fv) (dv_B_f : f ∉ B.fv) :
    Nominal.NPrf
      (.imp (syn_wa (.classMem A C) (.classMem B D))
        (.classMem (.cab f (syn_wf (.cv f) A B)) (syn_cvv))) :=
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
  have dv_cache_0008 : b ∉ ((Wff.classMem (.cab f (syn_wf (.cv f) A B)) (syn_cvv))).fv :=
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
    a ∉ ((Wff.classMem (.cab f (syn_wf (.cv f) A (.cv b))) (syn_cvv))).fv :=
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
  have p0000 := @g_feq2 (.cv a) A (.cv b) (.cv f)
  have p0001 :=
    @g_abbidv (.classEq (.cv a) A) (syn_wf (.cv f) (.cv a) (.cv b))
      (syn_wf (.cv f) A (.cv b)) f dv_cache_0001 p0000
  have p0002 :=
    @g_eleq1d (.classEq (.cv a) A) (.cab f (syn_wf (.cv f) (.cv a) (.cv b)))
      (.cab f (syn_wf (.cv f) A (.cv b))) (syn_cvv) p0001
  have p0003 := @g_feq3 (.cv b) B A (.cv f)
  have p0004 :=
    @g_abbidv (.classEq (.cv b) B) (syn_wf (.cv f) A (.cv b)) (syn_wf (.cv f) A B) f
      dv_cache_0002 p0003
  have p0005 :=
    @g_eleq1d (.classEq (.cv b) B) (.cab f (syn_wf (.cv f) A (.cv b)))
      (.cab f (syn_wf (.cv f) A B)) (syn_cvv) p0004
  have p0006 := @g_vex a
  have p0007 := @g_vex b
  have p0008 := @g_mapexi (.cv a) (.cv b) f dv_cache_0003 dv_cache_0004 p0006 p0007
  have p0009 :=
    @g_vtocl2g (.classMem (.cab f (syn_wf (.cv f) (.cv a) (.cv b))) (syn_cvv))
      (.classMem (.cab f (syn_wf (.cv f) A (.cv b))) (syn_cvv))
      (.classMem (.cab f (syn_wf (.cv f) A B)) (syn_cvv)) a b A B C D dv_cache_0005
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

@[expose]
noncomputable def g_mapvalg (A : Class) (B : Class) (C : Class) (D : Class) (f : Var)
    (dv_A_f : f ∉ A.fv) (dv_B_f : f ∉ B.fv) :
    Nominal.NPrf
      (.imp (syn_wa (.classMem A C) (.classMem B D))
        (.classEq (syn_co A (syn_cmap) B) (.cab f (syn_wf (.cv f) B A)))) :=
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
  have dv_cache_0012 : x ∉ ((syn_cvv)).fv :=
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
  have dv_cache_0013 : y ∉ ((syn_cvv)).fv :=
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
  have dv_cache_0014 : x ∉ ((Class.cab f (syn_wf (.cv f) (.cv y) A))).fv :=
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
  have dv_cache_0015 : x ∉ ((Class.cab f (syn_wf (.cv f) B A))).fv :=
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
  have dv_cache_0016 : y ∉ ((Class.cab f (syn_wf (.cv f) B A))).fv :=
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
  have p0000 := @g_mapex B A D C f dv_cache_0001 dv_cache_0002
  have p0001 :=
    @g_ancoms (.classMem B D) (.classMem A C)
      (.classMem (.cab f (syn_wf (.cv f) B A)) (syn_cvv)) p0000
  have p0002 := @g_elex A C
  have p0003 := @g_elex B D
  have p0004 := @g_feq3 (.cv x) A (.cv y) (.cv f)
  have p0005 :=
    @g_abbidv (.classEq (.cv x) A) (syn_wf (.cv f) (.cv y) (.cv x))
      (syn_wf (.cv f) (.cv y) A) f dv_cache_0003 p0004
  have p0006 := @g_feq2 (.cv y) B A (.cv f)
  have p0007 :=
    @g_abbidv (.classEq (.cv y) B) (syn_wf (.cv f) (.cv y) A) (syn_wf (.cv f) B A) f
      dv_cache_0004 p0006
  have p0008 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominal_df_map x y f
      dv_cache_0005 dv_cache_0006 dv_cache_0007
  have p0009 :=
    @g_ovmpt2g x y A B (syn_cvv) (syn_cvv) (.cab f (syn_wf (.cv f) (.cv y) (.cv x)))
      (.cab f (syn_wf (.cv f) B A)) (syn_cmap) (.cab f (syn_wf (.cv f) (.cv y) A))
      (syn_cvv) dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012
      dv_cache_0013 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016
      dv_cache_0007 p0005 p0007 p0008
  have p0010 :=
    @g_n_3expia (.classMem A (syn_cvv)) (.classMem B (syn_cvv))
      (.classMem (.cab f (syn_wf (.cv f) B A)) (syn_cvv))
      (.classEq (syn_co A (syn_cmap) B) (.cab f (syn_wf (.cv f) B A))) p0009
  have p0011 :=
    @g_syl2an (.classMem A C) (.classMem A (syn_cvv)) (.classMem B (syn_cvv))
      (.imp (.classMem (.cab f (syn_wf (.cv f) B A)) (syn_cvv))
        (.classEq (syn_co A (syn_cmap) B) (.cab f (syn_wf (.cv f) B A))))
      (.classMem B D) p0002 p0003 p0010
  have p0012 :=
    @g_mpd (syn_wa (.classMem A C) (.classMem B D))
      (.classMem (.cab f (syn_wf (.cv f) B A)) (syn_cvv))
      (.classEq (syn_co A (syn_cmap) B) (.cab f (syn_wf (.cv f) B A))) p0001 p0011
  exact p0012

@[expose]
noncomputable def g_elmapg (A : Class) (B : Class) (C : Class) (V : Class) (W : Class)
    (X : Class) :
    Nominal.NPrf
      (.imp (syn_w3a (.classMem A V) (.classMem B W) (.classMem C X))
        (syn_wb (.classMem C (syn_co A (syn_cmap) B)) (syn_wf C B A))) :=
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
  have dv_cache_0004 : g ∉ ((syn_wf C B A)).fv :=
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
  have p0000 := @g_mapvalg A B V W g dv_cache_0001 dv_cache_0002
  have p0001 :=
    @g_eleq2d (syn_wa (.classMem A V) (.classMem B W)) (syn_co A (syn_cmap) B)
      (.cab g (syn_wf (.cv g) B A)) C p0000
  have p0002 :=
    @g_n_3adant3 (.classMem A V) (.classMem B W)
      (syn_wb (.classMem C (syn_co A (syn_cmap) B)) (.classMem C (.cab g (syn_wf (.cv g) B A))))
      (.classMem C X) p0001
  have p0003 := @g_feq1 B A (.cv g) C
  have p0004 :=
    @g_elabg (syn_wf (.cv g) B A) (syn_wf C B A) g C X dv_cache_0003 dv_cache_0004 p0003
  have p0005 :=
    @g_n_3ad2ant3 (.classMem C X) (.classMem A V)
      (syn_wb (.classMem C (.cab g (syn_wf (.cv g) B A))) (syn_wf C B A)) (.classMem B W)
      p0004
  have p0006 :=
    @g_bitrd (syn_w3a (.classMem A V) (.classMem B W) (.classMem C X))
      (.classMem C (syn_co A (syn_cmap) B)) (.classMem C (.cab g (syn_wf (.cv g) B A)))
      (syn_wf C B A) p0002 p0005
  exact p0006

@[expose]
noncomputable def g_elmapi (A : Class) (B : Class) (C : Class) :
    Nominal.NPrf (.imp (.classMem A (syn_co B (syn_cmap) C)) (syn_wf A C B)) :=
  by
  have p0000 := @g_elovex1 A B C (syn_cmap)
  have p0001 := @g_elovex2 A B C (syn_cmap)
  have p0002 := @g_id (.classMem A (syn_co B (syn_cmap) C))
  have p0003 := @g_elmapg B C A (syn_cvv) (syn_cvv) (syn_co B (syn_cmap) C)
  have p0004 :=
    @g_syl3anc (.classMem A (syn_co B (syn_cmap) C)) (.classMem B (syn_cvv))
      (.classMem C (syn_cvv)) (.classMem A (syn_co B (syn_cmap) C))
      (syn_wb (.classMem A (syn_co B (syn_cmap) C)) (syn_wf A C B)) p0000 p0001 p0002
      p0003
  have p0005 := @g_ibi (.classMem A (syn_co B (syn_cmap) C)) (syn_wf A C B) p0004
  exact p0005

@[expose]
noncomputable def g_bren (A : Class) (B : Class) (f : Var) (dv_A_f : f ∉ A.fv)
    (dv_B_f : f ∉ B.fv) :
    Nominal.NPrf (syn_wb (syn_wbr A (syn_cen) B) (syn_wex f (syn_wf1o (.cv f) A B))) :=
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
    f ∉ ((syn_wa (.classMem A (syn_cvv)) (.classMem B (syn_cvv)))).fv := by
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
  have dv_cache_0011 : x ∉ ((syn_wex f (syn_wf1o (.cv f) A B))).fv :=
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
  have dv_cache_0012 : y ∉ ((syn_wex f (syn_wf1o (.cv f) A B))).fv :=
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
  have p0000 := @g_brex A B (syn_cen)
  have p0001 := @g_vex f
  have p0002 := @g_dmex (.cv f) p0001
  have p0003 := @g_rnex (.cv f) p0001
  have p0004 :=
    @g_pm3_2i (.classMem (syn_cdm (.cv f)) (syn_cvv))
      (.classMem (syn_crn (.cv f)) (syn_cvv)) p0002 p0003
  have p0005 := @g_f1odm A B (.cv f)
  have p0006 := @g_eleq1d (syn_wf1o (.cv f) A B) (syn_cdm (.cv f)) A (syn_cvv) p0005
  have p0007 := @g_f1ofo A B (.cv f)
  have p0008 := @g_forn A B (.cv f)
  have p0009 :=
    @g_syl (syn_wf1o (.cv f) A B) (syn_wfo (.cv f) A B) (.classEq (syn_crn (.cv f)) B)
      p0007 p0008
  have p0010 := @g_eleq1d (syn_wf1o (.cv f) A B) (syn_crn (.cv f)) B (syn_cvv) p0009
  have p0011 :=
    @g_anbi12d (syn_wf1o (.cv f) A B) (.classMem (syn_cdm (.cv f)) (syn_cvv))
      (.classMem A (syn_cvv)) (.classMem (syn_crn (.cv f)) (syn_cvv))
      (.classMem B (syn_cvv)) p0006 p0010
  have p0012 :=
    @g_mpbii (syn_wf1o (.cv f) A B)
      (syn_wa (.classMem (syn_cdm (.cv f)) (syn_cvv)) (.classMem (syn_crn (.cv f)) (syn_cvv)))
      (syn_wa (.classMem A (syn_cvv)) (.classMem B (syn_cvv))) p0004 p0011
  have p0013 :=
    @g_exlimiv (syn_wf1o (.cv f) A B)
      (syn_wa (.classMem A (syn_cvv)) (.classMem B (syn_cvv))) f dv_cache_0001 p0012
  have p0014 := @g_f1oeq2 (.cv x) A (.cv y) (.cv f)
  have p0015 :=
    @g_exbidv (.classEq (.cv x) A) (syn_wf1o (.cv f) (.cv x) (.cv y))
      (syn_wf1o (.cv f) A (.cv y)) f dv_cache_0002 p0014
  have p0016 := @g_f1oeq3 (.cv y) B A (.cv f)
  have p0017 :=
    @g_exbidv (.classEq (.cv y) B) (syn_wf1o (.cv f) A (.cv y)) (syn_wf1o (.cv f) A B) f
      dv_cache_0003 p0016
  have p0018 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominal_df_en x y f
      dv_cache_0004 dv_cache_0005 dv_cache_0006
  have p0019 :=
    @g_brabg (syn_wex f (syn_wf1o (.cv f) (.cv x) (.cv y)))
      (syn_wex f (syn_wf1o (.cv f) A (.cv y))) (syn_wex f (syn_wf1o (.cv f) A B)) x y A B
      (syn_cvv) (syn_cvv) (syn_cen) dv_cache_0007 dv_cache_0008 dv_cache_0009
      dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0006 p0015 p0017 p0018
  have p0020 :=
    @g_pm5_21nii (syn_wbr A (syn_cen) B)
      (syn_wa (.classMem A (syn_cvv)) (.classMem B (syn_cvv)))
      (syn_wex f (syn_wf1o (.cv f) A B)) p0000 p0013 p0019
  exact p0020

@[expose]
noncomputable def g_enex : Nominal.NPrf (.classMem (syn_cen) (syn_cvv)) :=
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
  have dv_cache_0004 : f ∉ ((syn_cop (.cv x) (.cv y))).fv :=
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
      ((syn_ctxp (syn_cfns)
          (syn_crn (syn_ctxp (syn_ccnv (syn_cimage (syn_cswap))) (syn_cfns))))).fv :=
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
  have dv_cache_0006 : g ∉ ((syn_cop (.cv f) (.cv y))).fv :=
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
    g ∉ ((syn_ctxp (syn_ccnv (syn_cimage (syn_cswap))) (syn_cfns))).fv :=
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
  have dv_cache_0008 : g ∉ ((syn_ccnv (.cv f))).fv :=
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
  have dv_cache_0009 : g ∉ ((syn_wfn (syn_ccnv (.cv f)) (.cv y))).fv :=
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
      ((syn_crn (syn_ctxp (syn_cfns)
            (syn_crn (syn_ctxp (syn_ccnv (syn_cimage (syn_cswap))) (syn_cfns)))))).fv :=
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
      ((syn_crn (syn_ctxp (syn_cfns)
            (syn_crn (syn_ctxp (syn_ccnv (syn_cimage (syn_cswap))) (syn_cfns)))))).fv :=
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
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominal_df_en x y f
      dv_cache_0001 dv_cache_0002 dv_cache_0003
  have p0001 :=
    @g_elrn2 f (syn_cop (.cv x) (.cv y))
      (syn_ctxp (syn_cfns) (syn_crn (syn_ctxp (syn_ccnv (syn_cimage (syn_cswap))) (syn_cfns))))
      dv_cache_0004 dv_cache_0005
  have p0002 := (Nominal.biimpRefl (syn_wbr (.cv f) (syn_cfns) (.cv x)))
  have p0003 := @g_vex f
  have p0004 := @g_brfns (.cv x) (.cv f) p0003
  have p0005 :=
    @g_bitr3i (.classMem (syn_cop (.cv f) (.cv x)) (syn_cfns))
      (syn_wbr (.cv f) (syn_cfns) (.cv x)) (syn_wfn (.cv f) (.cv x)) p0002 p0004
  have p0006 :=
    @g_elrn2 g (syn_cop (.cv f) (.cv y))
      (syn_ctxp (syn_ccnv (syn_cimage (syn_cswap))) (syn_cfns)) dv_cache_0006
      dv_cache_0007
  have p0007 :=
    @g_oteltxp (.cv g) (.cv f) (.cv y) (syn_ccnv (syn_cimage (syn_cswap))) (syn_cfns)
  have p0008 := @g_opelcnv (.cv g) (.cv f) (syn_cimage (syn_cswap))
  have p0009 := @g_dfcnv2 (.cv f)
  have p0010 := @g_eqeq2i (syn_ccnv (.cv f)) (syn_cima (syn_cswap) (.cv f)) (.cv g) p0009
  have p0011 := @g_vex g
  have p0012 := @g_brimage (.cv f) (.cv g) (syn_cswap) p0003 p0011
  have p0013 := (Nominal.biimpRefl (syn_wbr (.cv f) (syn_cimage (syn_cswap)) (.cv g)))
  have p0014 :=
    @g_n_3bitr2ri (.classEq (.cv g) (syn_ccnv (.cv f)))
      (.classEq (.cv g) (syn_cima (syn_cswap) (.cv f)))
      (syn_wbr (.cv f) (syn_cimage (syn_cswap)) (.cv g))
      (.classMem (syn_cop (.cv f) (.cv g)) (syn_cimage (syn_cswap))) p0010 p0012 p0013
  have p0015 :=
    @g_bitri (.classMem (syn_cop (.cv g) (.cv f)) (syn_ccnv (syn_cimage (syn_cswap))))
      (.classMem (syn_cop (.cv f) (.cv g)) (syn_cimage (syn_cswap)))
      (.classEq (.cv g) (syn_ccnv (.cv f))) p0008 p0014
  have p0016 := (Nominal.biimpRefl (syn_wbr (.cv g) (syn_cfns) (.cv y)))
  have p0017 := @g_brfns (.cv y) (.cv g) p0011
  have p0018 :=
    @g_bitr3i (.classMem (syn_cop (.cv g) (.cv y)) (syn_cfns))
      (syn_wbr (.cv g) (syn_cfns) (.cv y)) (syn_wfn (.cv g) (.cv y)) p0016 p0017
  have p0019 :=
    @g_anbi12i (.classMem (syn_cop (.cv g) (.cv f)) (syn_ccnv (syn_cimage (syn_cswap))))
      (.classEq (.cv g) (syn_ccnv (.cv f)))
      (.classMem (syn_cop (.cv g) (.cv y)) (syn_cfns)) (syn_wfn (.cv g) (.cv y)) p0015
      p0018
  have p0020 :=
    @g_bitri
      (.classMem (syn_cop (.cv g) (syn_cop (.cv f) (.cv y)))
        (syn_ctxp (syn_ccnv (syn_cimage (syn_cswap))) (syn_cfns)))
      (syn_wa (.classMem (syn_cop (.cv g) (.cv f)) (syn_ccnv (syn_cimage (syn_cswap))))
        (.classMem (syn_cop (.cv g) (.cv y)) (syn_cfns)))
      (syn_wa (.classEq (.cv g) (syn_ccnv (.cv f))) (syn_wfn (.cv g) (.cv y))) p0007 p0019
  have p0021 :=
    @g_exbii
      (.classMem (syn_cop (.cv g) (syn_cop (.cv f) (.cv y)))
        (syn_ctxp (syn_ccnv (syn_cimage (syn_cswap))) (syn_cfns)))
      (syn_wa (.classEq (.cv g) (syn_ccnv (.cv f))) (syn_wfn (.cv g) (.cv y))) g p0020
  have p0022 := @g_cnvex (.cv f) p0003
  have p0023 := @g_fneq1 (.cv y) (.cv g) (syn_ccnv (.cv f))
  have p0024 :=
    @g_ceqsexv (syn_wfn (.cv g) (.cv y)) (syn_wfn (syn_ccnv (.cv f)) (.cv y)) g
      (syn_ccnv (.cv f)) dv_cache_0008 dv_cache_0009 p0022 p0023
  have p0025 :=
    @g_bitri
      (syn_wex g (.classMem (syn_cop (.cv g) (syn_cop (.cv f) (.cv y)))
          (syn_ctxp (syn_ccnv (syn_cimage (syn_cswap))) (syn_cfns))))
      (syn_wex g (syn_wa (.classEq (.cv g) (syn_ccnv (.cv f))) (syn_wfn (.cv g) (.cv y))))
      (syn_wfn (syn_ccnv (.cv f)) (.cv y)) p0021 p0024
  have p0026 :=
    @g_bitri
      (.classMem (syn_cop (.cv f) (.cv y))
        (syn_crn (syn_ctxp (syn_ccnv (syn_cimage (syn_cswap))) (syn_cfns))))
      (syn_wex g (.classMem (syn_cop (.cv g) (syn_cop (.cv f) (.cv y)))
          (syn_ctxp (syn_ccnv (syn_cimage (syn_cswap))) (syn_cfns))))
      (syn_wfn (syn_ccnv (.cv f)) (.cv y)) p0006 p0025
  have p0027 :=
    @g_anbi12i (.classMem (syn_cop (.cv f) (.cv x)) (syn_cfns)) (syn_wfn (.cv f) (.cv x))
      (.classMem (syn_cop (.cv f) (.cv y))
        (syn_crn (syn_ctxp (syn_ccnv (syn_cimage (syn_cswap))) (syn_cfns))))
      (syn_wfn (syn_ccnv (.cv f)) (.cv y)) p0005 p0026
  have p0028 :=
    @g_oteltxp (.cv f) (.cv x) (.cv y) (syn_cfns)
      (syn_crn (syn_ctxp (syn_ccnv (syn_cimage (syn_cswap))) (syn_cfns)))
  have p0029 := @g_dff1o4 (.cv x) (.cv y) (.cv f)
  have p0030 :=
    @g_n_3bitr4i
      (syn_wa (.classMem (syn_cop (.cv f) (.cv x)) (syn_cfns))
        (.classMem (syn_cop (.cv f) (.cv y))
          (syn_crn (syn_ctxp (syn_ccnv (syn_cimage (syn_cswap))) (syn_cfns)))))
      (syn_wa (syn_wfn (.cv f) (.cv x)) (syn_wfn (syn_ccnv (.cv f)) (.cv y)))
      (.classMem (syn_cop (.cv f) (syn_cop (.cv x) (.cv y))) (syn_ctxp (syn_cfns)
          (syn_crn (syn_ctxp (syn_ccnv (syn_cimage (syn_cswap))) (syn_cfns)))))
      (syn_wf1o (.cv f) (.cv x) (.cv y)) p0027 p0028 p0029
  have p0031 :=
    @g_exbii
      (.classMem (syn_cop (.cv f) (syn_cop (.cv x) (.cv y))) (syn_ctxp (syn_cfns)
          (syn_crn (syn_ctxp (syn_ccnv (syn_cimage (syn_cswap))) (syn_cfns)))))
      (syn_wf1o (.cv f) (.cv x) (.cv y)) f p0030
  have p0032 :=
    @g_bitri
      (.classMem (syn_cop (.cv x) (.cv y)) (syn_crn (syn_ctxp (syn_cfns)
            (syn_crn (syn_ctxp (syn_ccnv (syn_cimage (syn_cswap))) (syn_cfns))))))
      (syn_wex f (.classMem (syn_cop (.cv f) (syn_cop (.cv x) (.cv y))) (syn_ctxp (syn_cfns)
            (syn_crn (syn_ctxp (syn_ccnv (syn_cimage (syn_cswap))) (syn_cfns))))))
      (syn_wex f (syn_wf1o (.cv f) (.cv x) (.cv y))) p0001 p0031
  have p0033 :=
    @g_opabbi2i (syn_wex f (syn_wf1o (.cv f) (.cv x) (.cv y))) x y
      (syn_crn (syn_ctxp (syn_cfns)
          (syn_crn (syn_ctxp (syn_ccnv (syn_cimage (syn_cswap))) (syn_cfns)))))
      dv_cache_0010 dv_cache_0011 dv_cache_0003 p0032
  have p0034 :=
    @g_eqtr4i (syn_cen) (syn_copab x y (syn_wex f (syn_wf1o (.cv f) (.cv x) (.cv y))))
      (syn_crn (syn_ctxp (syn_cfns)
          (syn_crn (syn_ctxp (syn_ccnv (syn_cimage (syn_cswap))) (syn_cfns)))))
      p0000 p0033
  have p0035 := @g_fnsex
  have p0036 := @g_swapex
  have p0037 := @g_imageex (syn_cswap) p0036
  have p0038 := @g_cnvex (syn_cimage (syn_cswap)) p0037
  have p0040 := @g_txpex (syn_ccnv (syn_cimage (syn_cswap))) (syn_cfns) p0038 p0035
  have p0041 := @g_rnex (syn_ctxp (syn_ccnv (syn_cimage (syn_cswap))) (syn_cfns)) p0040
  have p0042 :=
    @g_txpex (syn_cfns)
      (syn_crn (syn_ctxp (syn_ccnv (syn_cimage (syn_cswap))) (syn_cfns))) p0035 p0041
  have p0043 :=
    @g_rnex
      (syn_ctxp (syn_cfns) (syn_crn (syn_ctxp (syn_ccnv (syn_cimage (syn_cswap))) (syn_cfns))))
      p0042
  have p0044 :=
    @g_eqeltri (syn_cen)
      (syn_crn (syn_ctxp (syn_cfns)
          (syn_crn (syn_ctxp (syn_ccnv (syn_cimage (syn_cswap))) (syn_cfns)))))
      (syn_cvv) p0034 p0043
  exact p0044

@[expose]
noncomputable def g_f1oeng (A : Class) (B : Class) (C : Class) (F : Class) :
    Nominal.NPrf
      (.imp (syn_wa (.classMem F C) (syn_wf1o F A B)) (syn_wbr A (syn_cen) B)) :=
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
  have dv_cache_0002 : f ∉ ((syn_wf1o F A B)).fv :=
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
  have p0000 := @g_f1oeq1 A B (.cv f) F
  have p0001 :=
    @g_spcegv (syn_wf1o (.cv f) A B) (syn_wf1o F A B) f F C dv_cache_0001 dv_cache_0002
      p0000
  have p0002 :=
    @g_imp (.classMem F C) (syn_wf1o F A B) (syn_wex f (syn_wf1o (.cv f) A B)) p0001
  have p0003 := @g_bren A B f dv_cache_0003 dv_cache_0004
  have p0004 :=
    @g_sylibr (syn_wa (.classMem F C) (syn_wf1o F A B)) (syn_wex f (syn_wf1o (.cv f) A B))
      (syn_wbr A (syn_cen) B) p0002 p0003
  exact p0004

@[expose]
noncomputable def g_f1oen (A : Class) (B : Class) (F : Class)
    (hyp_f1oen_1 : Nominal.NPrf (.classMem F (syn_cvv))) :
    Nominal.NPrf (.imp (syn_wf1o F A B) (syn_wbr A (syn_cen) B)) :=
  by
  have p0000 := @g_f1oeng A B (syn_cvv) F
  have p0001 :=
    @g_mpan (.classMem F (syn_cvv)) (syn_wf1o F A B) (syn_wbr A (syn_cen) B) hyp_f1oen_1
      p0000
  exact p0001

@[expose]
noncomputable def g_enrflxg (A : Class) (V : Class) :
    Nominal.NPrf (.imp (.classMem A V) (syn_wbr A (syn_cen) A)) :=
  by
  have p0000 := @g_idex
  have p0001 := @g_resexg (syn_cid) A (syn_cvv) V
  have p0002 :=
    @g_mpan (.classMem (syn_cid) (syn_cvv)) (.classMem A V)
      (.classMem (syn_cres (syn_cid) A) (syn_cvv)) p0000 p0001
  have p0003 := @g_f1oi A
  have p0004 := @g_f1oeng A A (syn_cvv) (syn_cres (syn_cid) A)
  have p0005 :=
    @g_sylancl (.classMem A V) (.classMem (syn_cres (syn_cid) A) (syn_cvv))
      (syn_wf1o (syn_cres (syn_cid) A) A A) (syn_wbr A (syn_cen) A) p0002 p0003 p0004
  exact p0005

@[expose]
noncomputable def g_enrflx (A : Class)
    (hyp_enrflx_1 : Nominal.NPrf (.classMem A (syn_cvv))) :
    Nominal.NPrf (syn_wbr A (syn_cen) A) :=
  by
  have p0000 := @g_enrflxg A (syn_cvv)
  have p0001 := Nominal.mp hyp_enrflx_1 p0000
  exact p0001

@[expose]
noncomputable def g_ensymi (A : Class) (B : Class) :
    Nominal.NPrf (.imp (syn_wbr A (syn_cen) B) (syn_wbr B (syn_cen) A)) :=
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
  have dv_cache_0003 : f ∉ ((syn_wbr B (syn_cen) A)).fv :=
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
  have p0000 := @g_bren A B f dv_cache_0001 dv_cache_0002
  have p0001 := @g_f1ocnv A B (.cv f)
  have p0002 := @g_vex f
  have p0003 := @g_cnvex (.cv f) p0002
  have p0004 := @g_f1oen B A (syn_ccnv (.cv f)) p0003
  have p0005 :=
    @g_syl (syn_wf1o (.cv f) A B) (syn_wf1o (syn_ccnv (.cv f)) B A)
      (syn_wbr B (syn_cen) A) p0001 p0004
  have p0006 :=
    @g_exlimiv (syn_wf1o (.cv f) A B) (syn_wbr B (syn_cen) A) f dv_cache_0003 p0005
  have p0007 :=
    @g_sylbi (syn_wbr A (syn_cen) B) (syn_wex f (syn_wf1o (.cv f) A B))
      (syn_wbr B (syn_cen) A) p0000 p0006
  exact p0007

@[expose]
noncomputable def g_ensym (A : Class) (B : Class) :
    Nominal.NPrf (syn_wb (syn_wbr A (syn_cen) B) (syn_wbr B (syn_cen) A)) :=
  by
  have p0000 := @g_ensymi A B
  have p0001 := @g_ensymi B A
  have p0002 := @g_impbii (syn_wbr A (syn_cen) B) (syn_wbr B (syn_cen) A) p0000 p0001
  exact p0002

@[expose]
noncomputable def g_entr (A : Class) (B : Class) (C : Class) :
    Nominal.NPrf
      (.imp (syn_wa (syn_wbr A (syn_cen) B) (syn_wbr B (syn_cen) C)) (syn_wbr A (syn_cen) C)) :=
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
  have dv_cache_0005 : g ∉ ((syn_wf1o (.cv f) A B)).fv :=
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
  have dv_cache_0006 : f ∉ ((syn_wf1o (.cv g) B C)).fv :=
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
  have dv_cache_0007 : f ∉ ((syn_wbr A (syn_cen) C)).fv :=
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
  have dv_cache_0008 : g ∉ ((syn_wbr A (syn_cen) C)).fv :=
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
  have p0000 := @g_bren A B f dv_cache_0001 dv_cache_0002
  have p0001 := @g_bren B C g dv_cache_0003 dv_cache_0004
  have p0002 :=
    @g_anbi12i (syn_wbr A (syn_cen) B) (syn_wex f (syn_wf1o (.cv f) A B))
      (syn_wbr B (syn_cen) C) (syn_wex g (syn_wf1o (.cv g) B C)) p0000 p0001
  have p0003 :=
    @g_eeanv (syn_wf1o (.cv f) A B) (syn_wf1o (.cv g) B C) f g dv_cache_0005 dv_cache_0006
  have p0004 :=
    @g_bitr4i (syn_wa (syn_wbr A (syn_cen) B) (syn_wbr B (syn_cen) C))
      (syn_wa (syn_wex f (syn_wf1o (.cv f) A B)) (syn_wex g (syn_wf1o (.cv g) B C)))
      (syn_wex f (syn_wex g (syn_wa (syn_wf1o (.cv f) A B) (syn_wf1o (.cv g) B C)))) p0002
      p0003
  have p0005 := @g_f1oco A B C (.cv g) (.cv f)
  have p0006 :=
    @g_ancoms (syn_wf1o (.cv g) B C) (syn_wf1o (.cv f) A B)
      (syn_wf1o (syn_ccom (.cv g) (.cv f)) A C) p0005
  have p0007 := @g_vex g
  have p0008 := @g_vex f
  have p0009 := @g_coex (.cv g) (.cv f) p0007 p0008
  have p0010 := @g_f1oen A C (syn_ccom (.cv g) (.cv f)) p0009
  have p0011 :=
    @g_syl (syn_wa (syn_wf1o (.cv f) A B) (syn_wf1o (.cv g) B C))
      (syn_wf1o (syn_ccom (.cv g) (.cv f)) A C) (syn_wbr A (syn_cen) C) p0006 p0010
  have p0012 :=
    @g_exlimivv (syn_wa (syn_wf1o (.cv f) A B) (syn_wf1o (.cv g) B C))
      (syn_wbr A (syn_cen) C) f g dv_cache_0007 dv_cache_0008 p0011
  have p0013 :=
    @g_sylbi (syn_wa (syn_wbr A (syn_cen) B) (syn_wbr B (syn_cen) C))
      (syn_wex f (syn_wex g (syn_wa (syn_wf1o (.cv f) A B) (syn_wf1o (.cv g) B C))))
      (syn_wbr A (syn_cen) C) p0004 p0012
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

@[expose]
noncomputable def g_ener : Nominal.NPrf (syn_wbr (syn_cen) (syn_cer) (syn_cvv)) :=
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
  have dv_cache_0001 : x ∉ ((syn_cvv)).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv,
          compact_fv_not_mem_empty, not_false_eq_true])
  have dv_cache_0002 : y ∉ ((syn_cvv)).fv :=
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
  have dv_cache_0003 : z ∉ ((syn_cvv)).fv :=
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
  have dv_cache_0004 : x ∉ ((syn_cen)).fv :=
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
  have dv_cache_0005 : y ∉ ((syn_cen)).fv :=
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
  have dv_cache_0006 : z ∉ ((syn_cen)).fv :=
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
  have dv_cache_0007 : x ∉ (syn_wtru).fv :=
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
  have dv_cache_0008 : y ∉ (syn_wtru).fv :=
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
  have dv_cache_0009 : z ∉ (syn_wtru).fv :=
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
  have p0000 := @g_enex
  have p0001 := @g_a1i (.classMem (syn_cen) (syn_cvv)) syn_wtru p0000
  have p0002 := @g_vvex
  have p0003 := @g_a1i (.classMem (syn_cvv) (syn_cvv)) syn_wtru p0002
  have p0004 := @g_ensymi (.cv x) (.cv y)
  have p0005 :=
    @g_n_3ad2ant3 (syn_wbr (.cv x) (syn_cen) (.cv y)) syn_wtru
      (syn_wbr (.cv y) (syn_cen) (.cv x))
      (syn_wa (.classMem (.cv x) (syn_cvv)) (.classMem (.cv y) (syn_cvv))) p0004
  have p0006 := @g_entr (.cv x) (.cv y) (.cv z)
  have p0007 :=
    @g_n_3ad2ant3
      (syn_wa (syn_wbr (.cv x) (syn_cen) (.cv y)) (syn_wbr (.cv y) (syn_cen) (.cv z)))
      syn_wtru (syn_wbr (.cv x) (syn_cen) (.cv z))
      (syn_w3a (.classMem (.cv x) (syn_cvv)) (.classMem (.cv y) (syn_cvv))
        (.classMem (.cv z) (syn_cvv)))
      p0006
  have p0008 :=
    @g_iserd syn_wtru x y z (syn_cvv) (syn_cen) (syn_cvv) (syn_cvv) dv_cache_0001
      dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007
      dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 p0001 p0003
      p0005 p0007
  have p0009 := @g_trud (syn_wbr (syn_cen) (syn_cer) (syn_cvv)) p0008
  exact p0009

@[expose]
noncomputable def g_idssen : Nominal.NPrf (syn_wss (syn_cid) (syn_cen)) :=
  by
  let proofSupport : Finset Var := (∅ : Finset Var)
  let x : Var := freshVar proofSupport 0
  let y : Var := freshVar proofSupport 1
  have fresh_x_ne_y : x ≠ y :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have dv_cache_0001 : x ∉ ((syn_cid)).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cid,
          compact_fv_not_mem_empty, not_false_eq_true])
  have dv_cache_0002 : y ∉ ((syn_cid)).fv :=
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
  have dv_cache_0003 : x ∉ ((syn_cen)).fv :=
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
  have dv_cache_0004 : y ∉ ((syn_cen)).fv :=
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
  have p0000 := @g_vex y
  have p0001 := @g_ideq (.cv x) (.cv y) p0000
  have p0002 := @g_vex x
  have p0003 := @g_enrflx (.cv x) p0002
  have p0004 := @g_breq2 (.cv x) (.cv y) (.cv x) (syn_cen)
  have p0005_e01_recanon :
    Nominal.NPrf
      (.imp (.objEq x y) (syn_wb (syn_wbr (.cv x) (syn_cen) (.cv x))
          (syn_wbr (.cv x) (syn_cen) (.cv y)))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wb syn_wbr syn_cop syn_cun syn_cnin syn_wnan syn_wa syn_ccompl syn_wrex
          syn_wex syn_cphi syn_cen syn_copab
        simp (config :=
          { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_class_cv]
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
        · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0004
  have p0005 :=
    @g_mpbii (.objEq x y) (syn_wbr (.cv x) (syn_cen) (.cv x))
      (syn_wbr (.cv x) (syn_cen) (.cv y)) p0003 p0005_e01_recanon
  have p0006_e00_recanon :
    Nominal.NPrf (syn_wb (syn_wbr (.cv x) (syn_cid) (.cv y)) (.objEq x y)) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wb syn_wbr syn_cop syn_cun syn_cnin syn_wnan syn_wa syn_ccompl syn_wrex
          syn_wex syn_cphi syn_cid syn_copab
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
    @g_sylbi (syn_wbr (.cv x) (syn_cid) (.cv y)) (.objEq x y)
      (syn_wbr (.cv x) (syn_cen) (.cv y)) p0006_e00_recanon p0005
  have p0007 := (Nominal.biimpRefl (syn_wbr (.cv x) (syn_cid) (.cv y)))
  have p0008 := (Nominal.biimpRefl (syn_wbr (.cv x) (syn_cen) (.cv y)))
  have p0009 :=
    @g_n_3imtr3i (syn_wbr (.cv x) (syn_cid) (.cv y)) (syn_wbr (.cv x) (syn_cen) (.cv y))
      (.classMem (syn_cop (.cv x) (.cv y)) (syn_cid))
      (.classMem (syn_cop (.cv x) (.cv y)) (syn_cen)) p0006 p0007 p0008
  have p0010 :=
    @g_relssi x y (syn_cid) (syn_cen) dv_cache_0001 dv_cache_0002 dv_cache_0003
      dv_cache_0004 dv_cache_0005 p0009
  exact p0010

@[expose]
noncomputable def g_dmen : Nominal.NPrf (.classEq (syn_cdm (syn_cen)) (syn_cvv)) :=
  by
  have p0000 := @g_idssen
  have p0001 := @g_dmi
  have p0002 := @g_dmss (syn_cid) (syn_cen)
  have p0003 :=
    @g_syl5eqssr (syn_wss (syn_cid) (syn_cen)) (syn_cvv) (syn_cdm (syn_cid))
      (syn_cdm (syn_cen)) p0001 p0002
  have p0004 := Nominal.mp p0000 p0003
  have p0005 := @g_vss (syn_cdm (syn_cen))
  have p0006 :=
    @g_mpbi (syn_wss (syn_cvv) (syn_cdm (syn_cen)))
      (.classEq (syn_cdm (syn_cen)) (syn_cvv)) p0004 p0005
  exact p0006

@[expose]
noncomputable def g_en0 (A : Class) :
    Nominal.NPrf (syn_wb (syn_wbr A (syn_cen) (syn_c0)) (.classEq A (syn_c0))) :=
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
  have dv_cache_0002 : f ∉ ((syn_c0)).fv :=
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
  have dv_cache_0003 : f ∉ ((Wff.classEq A (syn_c0))).fv :=
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
  have p0000 := @g_bren A (syn_c0) f dv_cache_0001 dv_cache_0002
  have p0001 := @g_f1ocnv A (syn_c0) (.cv f)
  have p0002 := @g_f1o00 A (syn_ccnv (.cv f))
  have p0003 :=
    @g_simprbi (syn_wf1o (syn_ccnv (.cv f)) (syn_c0) A)
      (.classEq (syn_ccnv (.cv f)) (syn_c0)) (.classEq A (syn_c0)) p0002
  have p0004 :=
    @g_syl (syn_wf1o (.cv f) A (syn_c0)) (syn_wf1o (syn_ccnv (.cv f)) (syn_c0) A)
      (.classEq A (syn_c0)) p0001 p0003
  have p0005 :=
    @g_exlimiv (syn_wf1o (.cv f) A (syn_c0)) (.classEq A (syn_c0)) f dv_cache_0003 p0004
  have p0006 :=
    @g_sylbi (syn_wbr A (syn_cen) (syn_c0)) (syn_wex f (syn_wf1o (.cv f) A (syn_c0)))
      (.classEq A (syn_c0)) p0000 p0005
  have p0007 := @g_n_0ex
  have p0008 := @g_enrflx (syn_c0) p0007
  have p0009 := @g_breq1 A (syn_c0) (syn_c0) (syn_cen)
  have p0010 :=
    @g_mpbiri (.classEq A (syn_c0)) (syn_wbr A (syn_cen) (syn_c0))
      (syn_wbr (syn_c0) (syn_cen) (syn_c0)) p0008 p0009
  have p0011 := @g_impbii (syn_wbr A (syn_cen) (syn_c0)) (.classEq A (syn_c0)) p0006 p0010
  exact p0011

@[expose]
noncomputable def g_fundmen (F : Class)
    (hyp_fundmen_1 : Nominal.NPrf (.classMem F (syn_cvv))) :
    Nominal.NPrf (.imp (syn_wfun F) (syn_wbr (syn_cdm F) (syn_cen) F)) :=
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
      ((syn_wa (.classEq (.cv y) (syn_cop (.cv x) (.cv a))) (.classMem (.cv y) F))).fv :=
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
      ((syn_wa (.classEq (.cv z) (syn_cop (.cv x) (.cv b))) (.classMem (.cv z) F))).fv :=
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
  have dv_cache_0017 : a ∉ ((syn_wfun F)).fv :=
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
  have dv_cache_0018 : b ∉ ((syn_wfun F)).fv :=
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
  have dv_cache_0019 : z ∉ ((syn_wfun F)).fv :=
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
  have dv_cache_0020 : x ∉ ((syn_wfun F)).fv :=
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
  have dv_cache_0021 : y ∉ ((syn_wfun F)).fv :=
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
  have dv_cache_0022 : x ∉ ((syn_ccnv (syn_cres (syn_c1st) F))).fv :=
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
  have dv_cache_0023 : y ∉ ((syn_ccnv (syn_cres (syn_c1st) F))).fv :=
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
  have dv_cache_0024 : z ∉ ((syn_ccnv (syn_cres (syn_c1st) F))).fv :=
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
  have p0000 := @g_ssv F
  have p0001 := @g_n_1stfo
  have p0002 := @g_fofn (syn_cvv) (syn_cvv) (syn_c1st)
  have p0003 := @g_fnssresb (syn_cvv) F (syn_c1st)
  have p0004 :=
    @g_mp2b (syn_wfo (syn_c1st) (syn_cvv) (syn_cvv)) (syn_wfn (syn_c1st) (syn_cvv))
      (syn_wb (syn_wfn (syn_cres (syn_c1st) F) F) (syn_wss F (syn_cvv))) p0001 p0002 p0003
  have p0005 :=
    @g_mpbir (syn_wfn (syn_cres (syn_c1st) F) F) (syn_wss F (syn_cvv)) p0000 p0004
  have p0006 := @g_a1i (syn_wfn (syn_cres (syn_c1st) F) F) (syn_wfun F) p0005
  have p0007 := @g_brcnv (.cv x) (.cv y) (syn_cres (syn_c1st) F)
  have p0008 := @g_brres (.cv y) (.cv x) (syn_c1st) F
  have p0009 := @g_vex x
  have p0010 := @g_br1st a (.cv y) (.cv x) dv_cache_0001 dv_cache_0002 p0009
  have p0011 :=
    @g_anbi1i (syn_wbr (.cv y) (syn_c1st) (.cv x))
      (syn_wex a (.classEq (.cv y) (syn_cop (.cv x) (.cv a)))) (.classMem (.cv y) F) p0010
  have p0012 :=
    @g_n_19_41v (.classEq (.cv y) (syn_cop (.cv x) (.cv a))) (.classMem (.cv y) F) a
      dv_cache_0003
  have p0013 :=
    @g_bitr4i (syn_wa (syn_wbr (.cv y) (syn_c1st) (.cv x)) (.classMem (.cv y) F))
      (syn_wa (syn_wex a (.classEq (.cv y) (syn_cop (.cv x) (.cv a)))) (.classMem (.cv y) F))
      (syn_wex a (syn_wa (.classEq (.cv y) (syn_cop (.cv x) (.cv a))) (.classMem (.cv y) F)))
      p0011 p0012
  have p0014 :=
    @g_n_3bitri (syn_wbr (.cv x) (syn_ccnv (syn_cres (syn_c1st) F)) (.cv y))
      (syn_wbr (.cv y) (syn_cres (syn_c1st) F) (.cv x))
      (syn_wa (syn_wbr (.cv y) (syn_c1st) (.cv x)) (.classMem (.cv y) F))
      (syn_wex a (syn_wa (.classEq (.cv y) (syn_cop (.cv x) (.cv a))) (.classMem (.cv y) F)))
      p0007 p0008 p0013
  have p0015 := @g_brcnv (.cv x) (.cv z) (syn_cres (syn_c1st) F)
  have p0016 := @g_brres (.cv z) (.cv x) (syn_c1st) F
  have p0017 := @g_br1st b (.cv z) (.cv x) dv_cache_0004 dv_cache_0005 p0009
  have p0018 :=
    @g_anbi1i (syn_wbr (.cv z) (syn_c1st) (.cv x))
      (syn_wex b (.classEq (.cv z) (syn_cop (.cv x) (.cv b)))) (.classMem (.cv z) F) p0017
  have p0019 :=
    @g_n_3bitri (syn_wbr (.cv x) (syn_ccnv (syn_cres (syn_c1st) F)) (.cv z))
      (syn_wbr (.cv z) (syn_cres (syn_c1st) F) (.cv x))
      (syn_wa (syn_wbr (.cv z) (syn_c1st) (.cv x)) (.classMem (.cv z) F))
      (syn_wa (syn_wex b (.classEq (.cv z) (syn_cop (.cv x) (.cv b)))) (.classMem (.cv z) F))
      p0015 p0016 p0018
  have p0020 :=
    @g_n_19_41v (.classEq (.cv z) (syn_cop (.cv x) (.cv b))) (.classMem (.cv z) F) b
      dv_cache_0006
  have p0021 :=
    @g_bitr4i (syn_wbr (.cv x) (syn_ccnv (syn_cres (syn_c1st) F)) (.cv z))
      (syn_wa (syn_wex b (.classEq (.cv z) (syn_cop (.cv x) (.cv b)))) (.classMem (.cv z) F))
      (syn_wex b (syn_wa (.classEq (.cv z) (syn_cop (.cv x) (.cv b))) (.classMem (.cv z) F)))
      p0019 p0020
  have p0022 :=
    @g_anbi12i (syn_wbr (.cv x) (syn_ccnv (syn_cres (syn_c1st) F)) (.cv y))
      (syn_wex a (syn_wa (.classEq (.cv y) (syn_cop (.cv x) (.cv a))) (.classMem (.cv y) F)))
      (syn_wbr (.cv x) (syn_ccnv (syn_cres (syn_c1st) F)) (.cv z))
      (syn_wex b (syn_wa (.classEq (.cv z) (syn_cop (.cv x) (.cv b))) (.classMem (.cv z) F)))
      p0014 p0021
  have p0023 :=
    @g_eeanv (syn_wa (.classEq (.cv y) (syn_cop (.cv x) (.cv a))) (.classMem (.cv y) F))
      (syn_wa (.classEq (.cv z) (syn_cop (.cv x) (.cv b))) (.classMem (.cv z) F)) a b
      dv_cache_0007 dv_cache_0008
  have p0024 :=
    @g_bitr4i
      (syn_wa (syn_wbr (.cv x) (syn_ccnv (syn_cres (syn_c1st) F)) (.cv y))
        (syn_wbr (.cv x) (syn_ccnv (syn_cres (syn_c1st) F)) (.cv z)))
      (syn_wa (syn_wex a
          (syn_wa (.classEq (.cv y) (syn_cop (.cv x) (.cv a))) (.classMem (.cv y) F)))
        (syn_wex b (syn_wa (.classEq (.cv z) (syn_cop (.cv x) (.cv b))) (.classMem (.cv z) F))))
      (syn_wex a (syn_wex b (syn_wa
            (syn_wa (.classEq (.cv y) (syn_cop (.cv x) (.cv a))) (.classMem (.cv y) F))
            (syn_wa (.classEq (.cv z) (syn_cop (.cv x) (.cv b))) (.classMem (.cv z) F)))))
      p0022 p0023
  have p0025 :=
    @g_an4 (.classEq (.cv y) (syn_cop (.cv x) (.cv a))) (.classMem (.cv y) F)
      (.classEq (.cv z) (syn_cop (.cv x) (.cv b))) (.classMem (.cv z) F)
  have p0026 :=
    @g_dffun4 x a b F dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012
      dv_cache_0013 dv_cache_0014
  have p0027 :=
    @g_sp
      (.imp (syn_wa (.classMem (syn_cop (.cv x) (.cv a)) F)
          (.classMem (syn_cop (.cv x) (.cv b)) F)) (.objEq a b))
      b
  have p0028 :=
    @g_sps
      (.all b (.imp (syn_wa (.classMem (syn_cop (.cv x) (.cv a)) F)
            (.classMem (syn_cop (.cv x) (.cv b)) F)) (.objEq a b)))
      (.imp (syn_wa (.classMem (syn_cop (.cv x) (.cv a)) F)
          (.classMem (syn_cop (.cv x) (.cv b)) F)) (.objEq a b))
      a p0027
  have p0029 :=
    @g_sps
      (.all a (.all b (.imp (syn_wa (.classMem (syn_cop (.cv x) (.cv a)) F)
              (.classMem (syn_cop (.cv x) (.cv b)) F)) (.objEq a b))))
      (.imp (syn_wa (.classMem (syn_cop (.cv x) (.cv a)) F)
          (.classMem (syn_cop (.cv x) (.cv b)) F)) (.objEq a b))
      x p0028
  have p0030 :=
    @g_sylbi (syn_wfun F)
      (.all x (.all a (.all b (.imp (syn_wa (.classMem (syn_cop (.cv x) (.cv a)) F)
                (.classMem (syn_cop (.cv x) (.cv b)) F)) (.objEq a b)))))
      (.imp (syn_wa (.classMem (syn_cop (.cv x) (.cv a)) F)
          (.classMem (syn_cop (.cv x) (.cv b)) F)) (.objEq a b))
      p0026 p0029
  have p0031 := @g_opeq2 (.cv a) (.cv b) (.cv x)
  have p0032_e01_recanon :
    Nominal.NPrf
      (.imp (.objEq a b) (.classEq (syn_cop (.cv x) (.cv a)) (syn_cop (.cv x) (.cv b)))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_cop syn_cun syn_cnin syn_wnan syn_wa syn_ccompl syn_wrex syn_wex
          syn_cphi
        simp (config :=
          { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_class_cv]
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
        · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0031
  have p0032 :=
    @g_syl6 (syn_wfun F)
      (syn_wa (.classMem (syn_cop (.cv x) (.cv a)) F) (.classMem (syn_cop (.cv x) (.cv b)) F))
      (.objEq a b) (.classEq (syn_cop (.cv x) (.cv a)) (syn_cop (.cv x) (.cv b))) p0030
      p0032_e01_recanon
  have p0033 := @g_eleq1 (.cv y) (syn_cop (.cv x) (.cv a)) F
  have p0034 := @g_eleq1 (.cv z) (syn_cop (.cv x) (.cv b)) F
  have p0035 :=
    @g_bi2anan9 (.classEq (.cv y) (syn_cop (.cv x) (.cv a))) (.classMem (.cv y) F)
      (.classMem (syn_cop (.cv x) (.cv a)) F) (.classEq (.cv z) (syn_cop (.cv x) (.cv b)))
      (.classMem (.cv z) F) (.classMem (syn_cop (.cv x) (.cv b)) F) p0033 p0034
  have p0036 :=
    @g_eqeq12 (.cv y) (syn_cop (.cv x) (.cv a)) (.cv z) (syn_cop (.cv x) (.cv b))
  have p0037_e01_recanon :
    Nominal.NPrf
      (.imp (syn_wa (.classEq (.cv y) (syn_cop (.cv x) (.cv a)))
          (.classEq (.cv z) (syn_cop (.cv x) (.cv b)))) (syn_wb (.objEq y z)
          (.classEq (syn_cop (.cv x) (.cv a)) (syn_cop (.cv x) (.cv b))))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wa syn_cop syn_cun syn_cnin syn_wnan syn_ccompl syn_wrex syn_wex
          syn_cphi syn_wb
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
    @g_imbi12d
      (syn_wa (.classEq (.cv y) (syn_cop (.cv x) (.cv a)))
        (.classEq (.cv z) (syn_cop (.cv x) (.cv b))))
      (syn_wa (.classMem (.cv y) F) (.classMem (.cv z) F))
      (syn_wa (.classMem (syn_cop (.cv x) (.cv a)) F) (.classMem (syn_cop (.cv x) (.cv b)) F))
      (.objEq y z) (.classEq (syn_cop (.cv x) (.cv a)) (syn_cop (.cv x) (.cv b))) p0035
      p0037_e01_recanon
  have p0038 :=
    @g_biimprcd
      (syn_wa (.classEq (.cv y) (syn_cop (.cv x) (.cv a)))
        (.classEq (.cv z) (syn_cop (.cv x) (.cv b))))
      (.imp (syn_wa (.classMem (.cv y) F) (.classMem (.cv z) F)) (.objEq y z))
      (.imp (syn_wa (.classMem (syn_cop (.cv x) (.cv a)) F)
          (.classMem (syn_cop (.cv x) (.cv b)) F))
        (.classEq (syn_cop (.cv x) (.cv a)) (syn_cop (.cv x) (.cv b))))
      p0037
  have p0039 :=
    @g_imp3a
      (.imp (syn_wa (.classMem (syn_cop (.cv x) (.cv a)) F)
          (.classMem (syn_cop (.cv x) (.cv b)) F))
        (.classEq (syn_cop (.cv x) (.cv a)) (syn_cop (.cv x) (.cv b))))
      (syn_wa (.classEq (.cv y) (syn_cop (.cv x) (.cv a)))
        (.classEq (.cv z) (syn_cop (.cv x) (.cv b))))
      (syn_wa (.classMem (.cv y) F) (.classMem (.cv z) F)) (.objEq y z) p0038
  have p0040 :=
    @g_syl (syn_wfun F)
      (.imp (syn_wa (.classMem (syn_cop (.cv x) (.cv a)) F)
          (.classMem (syn_cop (.cv x) (.cv b)) F))
        (.classEq (syn_cop (.cv x) (.cv a)) (syn_cop (.cv x) (.cv b))))
      (.imp (syn_wa (syn_wa (.classEq (.cv y) (syn_cop (.cv x) (.cv a)))
            (.classEq (.cv z) (syn_cop (.cv x) (.cv b))))
          (syn_wa (.classMem (.cv y) F) (.classMem (.cv z) F))) (.objEq y z))
      p0032 p0039
  have p0041 :=
    @g_syl5bi
      (syn_wa (syn_wa (.classEq (.cv y) (syn_cop (.cv x) (.cv a))) (.classMem (.cv y) F))
        (syn_wa (.classEq (.cv z) (syn_cop (.cv x) (.cv b))) (.classMem (.cv z) F)))
      (syn_wa (syn_wa (.classEq (.cv y) (syn_cop (.cv x) (.cv a)))
          (.classEq (.cv z) (syn_cop (.cv x) (.cv b))))
        (syn_wa (.classMem (.cv y) F) (.classMem (.cv z) F)))
      (syn_wfun F) (.objEq y z) p0025 p0040
  have p0042 :=
    @g_exlimdvv (syn_wfun F)
      (syn_wa (syn_wa (.classEq (.cv y) (syn_cop (.cv x) (.cv a))) (.classMem (.cv y) F))
        (syn_wa (.classEq (.cv z) (syn_cop (.cv x) (.cv b))) (.classMem (.cv z) F)))
      (.objEq y z) a b dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 p0041
  have p0043 :=
    @g_syl5bi
      (syn_wa (syn_wbr (.cv x) (syn_ccnv (syn_cres (syn_c1st) F)) (.cv y))
        (syn_wbr (.cv x) (syn_ccnv (syn_cres (syn_c1st) F)) (.cv z)))
      (syn_wex a (syn_wex b (syn_wa
            (syn_wa (.classEq (.cv y) (syn_cop (.cv x) (.cv a))) (.classMem (.cv y) F))
            (syn_wa (.classEq (.cv z) (syn_cop (.cv x) (.cv b))) (.classMem (.cv z) F)))))
      (syn_wfun F) (.objEq y z) p0024 p0042
  have p0044 :=
    @g_alrimiv (syn_wfun F)
      (.imp (syn_wa (syn_wbr (.cv x) (syn_ccnv (syn_cres (syn_c1st) F)) (.cv y))
          (syn_wbr (.cv x) (syn_ccnv (syn_cres (syn_c1st) F)) (.cv z))) (.objEq y z))
      z dv_cache_0019 p0043
  have p0045 :=
    @g_alrimivv (syn_wfun F)
      (.all z (.imp (syn_wa (syn_wbr (.cv x) (syn_ccnv (syn_cres (syn_c1st) F)) (.cv y))
            (syn_wbr (.cv x) (syn_ccnv (syn_cres (syn_c1st) F)) (.cv z))) (.objEq y z)))
      x y dv_cache_0020 dv_cache_0021 p0044
  have p0046 :=
    @g_dffun2 x y z (syn_ccnv (syn_cres (syn_c1st) F)) dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027
  have p0047 :=
    @g_sylibr (syn_wfun F)
      (.all x (.all y (.all z (.imp
              (syn_wa (syn_wbr (.cv x) (syn_ccnv (syn_cres (syn_c1st) F)) (.cv y))
                (syn_wbr (.cv x) (syn_ccnv (syn_cres (syn_c1st) F)) (.cv z))) (.objEq y z)))))
      (syn_wfun (syn_ccnv (syn_cres (syn_c1st) F))) p0045 p0046
  have p0048 := @g_dfdm4 F
  have p0049 := @g_dfima3 (syn_c1st) F
  have p0050 :=
    @g_eqtr2i (syn_cdm F) (syn_cima (syn_c1st) F) (syn_crn (syn_cres (syn_c1st) F)) p0048
      p0049
  have p0051 :=
    @g_a1i (.classEq (syn_crn (syn_cres (syn_c1st) F)) (syn_cdm F)) (syn_wfun F) p0050
  have p0052 := @g_dff1o2 F (syn_cdm F) (syn_cres (syn_c1st) F)
  have p0053 :=
    @g_syl3anbrc (syn_wfun F) (syn_wfn (syn_cres (syn_c1st) F) F)
      (syn_wfun (syn_ccnv (syn_cres (syn_c1st) F)))
      (.classEq (syn_crn (syn_cres (syn_c1st) F)) (syn_cdm F))
      (syn_wf1o (syn_cres (syn_c1st) F) F (syn_cdm F)) p0006 p0047 p0051 p0052
  have p0054 := @g_n_1stex
  have p0055 := @g_resex (syn_c1st) F p0054 hyp_fundmen_1
  have p0056 := @g_f1oen F (syn_cdm F) (syn_cres (syn_c1st) F) p0055
  have p0057 :=
    @g_syl (syn_wfun F) (syn_wf1o (syn_cres (syn_c1st) F) F (syn_cdm F))
      (syn_wbr F (syn_cen) (syn_cdm F)) p0053 p0056
  have p0058 := @g_ensym F (syn_cdm F)
  have p0059 :=
    @g_sylib (syn_wfun F) (syn_wbr F (syn_cen) (syn_cdm F))
      (syn_wbr (syn_cdm F) (syn_cen) F) p0057 p0058
  exact p0059

@[expose]
noncomputable def g_en2sn (A : Class) (B : Class) (C : Class) (D : Class) :
    Nominal.NPrf
      (.imp (syn_wa (.classMem A C) (.classMem B D))
        (syn_wbr (syn_csn A) (syn_cen) (syn_csn B))) :=
  by
  have p0000 := @g_f1osng A B C D
  have p0001 := @g_snex (syn_cop A B)
  have p0002 := @g_f1oen (syn_csn A) (syn_csn B) (syn_csn (syn_cop A B)) p0001
  have p0003 :=
    @g_syl (syn_wa (.classMem A C) (.classMem B D))
      (syn_wf1o (syn_csn (syn_cop A B)) (syn_csn A) (syn_csn B))
      (syn_wbr (syn_csn A) (syn_cen) (syn_csn B)) p0000 p0002
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

@[expose]
noncomputable def g_unen (A : Class) (B : Class) (C : Class) (D : Class) :
    Nominal.NPrf
      (.imp (syn_wa (syn_wa (syn_wbr A (syn_cen) B) (syn_wbr C (syn_cen) D))
          (syn_wa (.classEq (syn_cin A C) (syn_c0)) (.classEq (syn_cin B D) (syn_c0))))
        (syn_wbr (syn_cun A C) (syn_cen) (syn_cun B D))) :=
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
  have dv_cache_0001 : h ∉ ((syn_cun (.cv f) (.cv g))).fv := by
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
    h ∉ ((syn_wf1o (syn_cun (.cv f) (.cv g)) (syn_cun A C) (syn_cun B D))).fv :=
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
      ((Wff.imp (syn_wa (.classEq (syn_cin A C) (syn_c0)) (.classEq (syn_cin B D) (syn_c0)))
          (syn_wex h (syn_wf1o (.cv h) (syn_cun A C) (syn_cun B D))))).fv :=
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
      ((Wff.imp (syn_wa (.classEq (syn_cin A C) (syn_c0)) (.classEq (syn_cin B D) (syn_c0)))
          (syn_wex h (syn_wf1o (.cv h) (syn_cun A C) (syn_cun B D))))).fv :=
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
  have dv_cache_0009 : g ∉ ((syn_wf1o (.cv f) A B)).fv :=
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
  have dv_cache_0010 : f ∉ ((syn_wf1o (.cv g) C D)).fv :=
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
  have dv_cache_0011 : h ∉ ((syn_cun A C)).fv :=
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
  have dv_cache_0012 : h ∉ ((syn_cun B D)).fv :=
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
  have p0000 := @g_f1oun A B C D (.cv f) (.cv g)
  have p0001 := @g_vex f
  have p0002 := @g_vex g
  have p0003 := @g_unex (.cv f) (.cv g) p0001 p0002
  have p0004 := @g_f1oeq1 (syn_cun A C) (syn_cun B D) (.cv h) (syn_cun (.cv f) (.cv g))
  have p0005 :=
    @g_spcev (syn_wf1o (.cv h) (syn_cun A C) (syn_cun B D))
      (syn_wf1o (syn_cun (.cv f) (.cv g)) (syn_cun A C) (syn_cun B D)) h
      (syn_cun (.cv f) (.cv g)) dv_cache_0001 dv_cache_0002 p0003 p0004
  have p0006 :=
    @g_syl
      (syn_wa (syn_wa (syn_wf1o (.cv f) A B) (syn_wf1o (.cv g) C D))
        (syn_wa (.classEq (syn_cin A C) (syn_c0)) (.classEq (syn_cin B D) (syn_c0))))
      (syn_wf1o (syn_cun (.cv f) (.cv g)) (syn_cun A C) (syn_cun B D))
      (syn_wex h (syn_wf1o (.cv h) (syn_cun A C) (syn_cun B D))) p0000 p0005
  have p0007 :=
    @g_ex (syn_wa (syn_wf1o (.cv f) A B) (syn_wf1o (.cv g) C D))
      (syn_wa (.classEq (syn_cin A C) (syn_c0)) (.classEq (syn_cin B D) (syn_c0)))
      (syn_wex h (syn_wf1o (.cv h) (syn_cun A C) (syn_cun B D))) p0006
  have p0008 :=
    @g_exlimivv (syn_wa (syn_wf1o (.cv f) A B) (syn_wf1o (.cv g) C D))
      (.imp (syn_wa (.classEq (syn_cin A C) (syn_c0)) (.classEq (syn_cin B D) (syn_c0)))
        (syn_wex h (syn_wf1o (.cv h) (syn_cun A C) (syn_cun B D))))
      f g dv_cache_0003 dv_cache_0004 p0007
  have p0009 :=
    @g_imp (syn_wex f (syn_wex g (syn_wa (syn_wf1o (.cv f) A B) (syn_wf1o (.cv g) C D))))
      (syn_wa (.classEq (syn_cin A C) (syn_c0)) (.classEq (syn_cin B D) (syn_c0)))
      (syn_wex h (syn_wf1o (.cv h) (syn_cun A C) (syn_cun B D))) p0008
  have p0010 := @g_bren A B f dv_cache_0005 dv_cache_0006
  have p0011 := @g_bren C D g dv_cache_0007 dv_cache_0008
  have p0012 :=
    @g_anbi12i (syn_wbr A (syn_cen) B) (syn_wex f (syn_wf1o (.cv f) A B))
      (syn_wbr C (syn_cen) D) (syn_wex g (syn_wf1o (.cv g) C D)) p0010 p0011
  have p0013 :=
    @g_eeanv (syn_wf1o (.cv f) A B) (syn_wf1o (.cv g) C D) f g dv_cache_0009 dv_cache_0010
  have p0014 :=
    @g_bitr4i (syn_wa (syn_wbr A (syn_cen) B) (syn_wbr C (syn_cen) D))
      (syn_wa (syn_wex f (syn_wf1o (.cv f) A B)) (syn_wex g (syn_wf1o (.cv g) C D)))
      (syn_wex f (syn_wex g (syn_wa (syn_wf1o (.cv f) A B) (syn_wf1o (.cv g) C D)))) p0012
      p0013
  have p0015 :=
    @g_anbi1i (syn_wa (syn_wbr A (syn_cen) B) (syn_wbr C (syn_cen) D))
      (syn_wex f (syn_wex g (syn_wa (syn_wf1o (.cv f) A B) (syn_wf1o (.cv g) C D))))
      (syn_wa (.classEq (syn_cin A C) (syn_c0)) (.classEq (syn_cin B D) (syn_c0))) p0014
  have p0016 := @g_bren (syn_cun A C) (syn_cun B D) h dv_cache_0011 dv_cache_0012
  have p0017 :=
    @g_n_3imtr4i
      (syn_wa (syn_wex f (syn_wex g (syn_wa (syn_wf1o (.cv f) A B) (syn_wf1o (.cv g) C D))))
        (syn_wa (.classEq (syn_cin A C) (syn_c0)) (.classEq (syn_cin B D) (syn_c0))))
      (syn_wex h (syn_wf1o (.cv h) (syn_cun A C) (syn_cun B D)))
      (syn_wa (syn_wa (syn_wbr A (syn_cen) B) (syn_wbr C (syn_cen) D))
        (syn_wa (.classEq (syn_cin A C) (syn_c0)) (.classEq (syn_cin B D) (syn_c0))))
      (syn_wbr (syn_cun A C) (syn_cen) (syn_cun B D)) p0009 p0015 p0016
  exact p0017

@[expose]
noncomputable def g_xpsnen (A : Class) (B : Class)
    (hyp_xpsnen_1 : Nominal.NPrf (.classMem A (syn_cvv)))
    (hyp_xpsnen_2 : Nominal.NPrf (.classMem B (syn_cvv))) :
    Nominal.NPrf (syn_wbr (syn_cxp A (syn_csn B)) (syn_cen) A) :=
  by
  have p0000 := @g_snid B hyp_xpsnen_2
  have p0001 := @g_ne0i (syn_csn B) B
  have p0002 := @g_dmxp A (syn_csn B)
  have p0003 :=
    @g_mp2b (.classMem B (syn_csn B)) (syn_wne (syn_csn B) (syn_c0))
      (.classEq (syn_cdm (syn_cxp A (syn_csn B))) A) p0000 p0001 p0002
  have p0004 := @g_fconst A B hyp_xpsnen_2
  have p0005 := @g_ffun A (syn_csn B) (syn_cxp A (syn_csn B))
  have p0006 := @g_snex B
  have p0007 := @g_xpex A (syn_csn B) hyp_xpsnen_1 p0006
  have p0008 := @g_fundmen (syn_cxp A (syn_csn B)) p0007
  have p0009 :=
    @g_mp2b (syn_wf (syn_cxp A (syn_csn B)) A (syn_csn B))
      (syn_wfun (syn_cxp A (syn_csn B)))
      (syn_wbr (syn_cdm (syn_cxp A (syn_csn B))) (syn_cen) (syn_cxp A (syn_csn B))) p0004
      p0005 p0008
  have p0010 :=
    @g_eqbrtrri (syn_cdm (syn_cxp A (syn_csn B))) A (syn_cxp A (syn_csn B)) (syn_cen)
      p0003 p0009
  have p0011 := @g_ensym A (syn_cxp A (syn_csn B))
  have p0012 :=
    @g_mpbi (syn_wbr A (syn_cen) (syn_cxp A (syn_csn B)))
      (syn_wbr (syn_cxp A (syn_csn B)) (syn_cen) A) p0010 p0011
  exact p0012

@[expose]
noncomputable def g_xpcomen (A : Class) (B : Class)
    (hyp_xpcomen_1 : Nominal.NPrf (.classMem A (syn_cvv)))
    (hyp_xpcomen_2 : Nominal.NPrf (.classMem B (syn_cvv))) :
    Nominal.NPrf (syn_wbr (syn_cxp A B) (syn_cen) (syn_cxp B A)) :=
  by
  have p0000 := @g_swapres (syn_cxp A B)
  have p0001 := @g_cnvxp A B
  have p0002 :=
    @g_f1oeq3 (syn_ccnv (syn_cxp A B)) (syn_cxp B A) (syn_cxp A B)
      (syn_cres (syn_cswap) (syn_cxp A B))
  have p0003 := Nominal.mp p0001 p0002
  have p0004 :=
    @g_mpbi
      (syn_wf1o (syn_cres (syn_cswap) (syn_cxp A B)) (syn_cxp A B) (syn_ccnv (syn_cxp A B)))
      (syn_wf1o (syn_cres (syn_cswap) (syn_cxp A B)) (syn_cxp A B) (syn_cxp B A)) p0000
      p0003
  have p0005 := @g_swapex
  have p0006 := @g_xpex A B hyp_xpcomen_1 hyp_xpcomen_2
  have p0007 := @g_resex (syn_cswap) (syn_cxp A B) p0005 p0006
  have p0008 :=
    @g_f1oen (syn_cxp A B) (syn_cxp B A) (syn_cres (syn_cswap) (syn_cxp A B)) p0007
  have p0009 := Nominal.mp p0004 p0008
  exact p0009

@[expose]
noncomputable def g_xpen (A : Class) (B : Class) (C : Class) (D : Class) :
    Nominal.NPrf
      (.imp (syn_wa (syn_wbr A (syn_cen) B) (syn_wbr C (syn_cen) D))
        (syn_wbr (syn_cxp A C) (syn_cen) (syn_cxp B D))) :=
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
  have dv_cache_0005 : g ∉ ((syn_wf1o (.cv f) A B)).fv :=
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
  have dv_cache_0006 : f ∉ ((syn_wf1o (.cv g) C D)).fv :=
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
  have dv_cache_0007 : f ∉ ((syn_wbr (syn_cxp A C) (syn_cen) (syn_cxp B D))).fv :=
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
  have dv_cache_0008 : g ∉ ((syn_wbr (syn_cxp A C) (syn_cen) (syn_cxp B D))).fv :=
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
  have p0000 := @g_bren A B f dv_cache_0001 dv_cache_0002
  have p0001 := @g_bren C D g dv_cache_0003 dv_cache_0004
  have p0002 :=
    @g_anbi12i (syn_wbr A (syn_cen) B) (syn_wex f (syn_wf1o (.cv f) A B))
      (syn_wbr C (syn_cen) D) (syn_wex g (syn_wf1o (.cv g) C D)) p0000 p0001
  have p0003 :=
    @g_eeanv (syn_wf1o (.cv f) A B) (syn_wf1o (.cv g) C D) f g dv_cache_0005 dv_cache_0006
  have p0004 :=
    @g_bitr4i (syn_wa (syn_wbr A (syn_cen) B) (syn_wbr C (syn_cen) D))
      (syn_wa (syn_wex f (syn_wf1o (.cv f) A B)) (syn_wex g (syn_wf1o (.cv g) C D)))
      (syn_wex f (syn_wex g (syn_wa (syn_wf1o (.cv f) A B) (syn_wf1o (.cv g) C D)))) p0002
      p0003
  have p0005 := @g_f1opprod A C B D (.cv f) (.cv g)
  have p0006 := @g_vex f
  have p0007 := @g_vex g
  have p0008 := @g_pprodex (.cv f) (.cv g) p0006 p0007
  have p0009 := @g_f1oen (syn_cxp A C) (syn_cxp B D) (syn_cpprod (.cv f) (.cv g)) p0008
  have p0010 :=
    @g_syl (syn_wa (syn_wf1o (.cv f) A B) (syn_wf1o (.cv g) C D))
      (syn_wf1o (syn_cpprod (.cv f) (.cv g)) (syn_cxp A C) (syn_cxp B D))
      (syn_wbr (syn_cxp A C) (syn_cen) (syn_cxp B D)) p0005 p0009
  have p0011 :=
    @g_exlimivv (syn_wa (syn_wf1o (.cv f) A B) (syn_wf1o (.cv g) C D))
      (syn_wbr (syn_cxp A C) (syn_cen) (syn_cxp B D)) f g dv_cache_0007 dv_cache_0008
      p0010
  have p0012 :=
    @g_sylbi (syn_wa (syn_wbr A (syn_cen) B) (syn_wbr C (syn_cen) D))
      (syn_wex f (syn_wex g (syn_wa (syn_wf1o (.cv f) A B) (syn_wf1o (.cv g) C D))))
      (syn_wbr (syn_cxp A C) (syn_cen) (syn_cxp B D)) p0004 p0011
  exact p0012


end NFChoice.DirectNominalPrf.WPPReplay

end
