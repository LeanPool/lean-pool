/-
Copyright (c) 2026 Goran Zuzic et al. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Goran Zuzic, David P. Woodruff, Vahab Mirrokni
-/

module

import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.NormNum

public import Mathlib.Combinatorics.SimpleGraph.Paths
public import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.Complex.ExponentialBounds
public import Mathlib.Analysis.Normed.Lp.PiLp

public import LeanPool.SteinerSpanners.Defs

/-! # Glue infrastructure for Steiner spanners

Ported from the upstream formalization to Lean Pool’s pinned Lean and Mathlib. -/

@[expose] public section

open scoped ENNReal
open HighDimSteinerSpanners

namespace HighDimSteinerSpanners.Proofs.Glue

/-- Zero-`sorry` proof of `lpDist_eq_toLp_dist`. -/
theorem lpDist_eq_toLp_dist_proof :
    ∀ (p : ℝ), 1 ≤ p →
      ∀ {d : ℕ} (x y : Fin d → ℝ),
        lpDist p x y =
          dist (WithLp.toLp (ENNReal.ofReal p) x) (WithLp.toLp (ENNReal.ofReal p) y) := by
  intro p hp d x y
  have hp0 : 0 < p := by linarith
  have hp_ne_zero : ENNReal.ofReal p ≠ 0 := by positivity
  have hp_ne_top : ENNReal.ofReal p ≠ ⊤ := ENNReal.ofReal_ne_top
  rw [PiLp.dist_eq_sum (p := ENNReal.ofReal p) (ENNReal.toReal_pos hp_ne_zero hp_ne_top)]
  simp only [ENNReal.toReal_ofReal hp0.le, lpDist, Real.dist_eq, one_div]

/-- Zero-`sorry` proof of Lemma 5.1 (`lem_5_1_interval_crossing`). -/
theorem lem_5_1_proof :
    ∀ (α β : ℤ), 1 ≤ α → α ≤ β →
      ∀ (L R : ℤ → ℤ),
        (∀ s : ℤ, α ≤ s → s ≤ β →
          α - 1 ≤ L s ∧ L s ≤ s - 1 ∧ s ≤ R s ∧ R s ≤ β ∧ (L s, R s) ≠ (α - 1, β)) →
        ∃ s t : ℤ,
          α ≤ s ∧ s < t ∧ t ≤ β ∧
          L s < L t ∧ L t ≤ s ∧ t ≤ R s + 1 ∧ R s + 1 ≤ R t := by
  have key : ∀ (n : ℕ) (α β : ℤ), β - α = n → 1 ≤ α → α ≤ β →
      ∀ (L R : ℤ → ℤ),
        (∀ s : ℤ, α ≤ s → s ≤ β →
          α - 1 ≤ L s ∧ L s ≤ s - 1 ∧ s ≤ R s ∧ R s ≤ β ∧ (L s, R s) ≠ (α - 1, β)) →
        ∃ s t : ℤ,
          α ≤ s ∧ s < t ∧ t ≤ β ∧
          L s < L t ∧ L t ≤ s ∧ t ≤ R s + 1 ∧ R s + 1 ≤ R t := by
    intro n
    induction n using Nat.strong_induction_on
    rename_i n ih
    intro α β hdiff hα hαβ L R hLR
    by_cases heq : α = β
    · subst heq
      obtain ⟨h1, h2, h3, h4, hne⟩ := hLR α le_rfl le_rfl
      exfalso; apply hne
      ext <;> omega
    · have hlt : α < β := lt_of_le_of_ne hαβ heq
      let S := (Finset.Icc α β).filter (fun s => L s = α - 1)
      have hα_mem : α ∈ S := by
        simp only [S, Finset.mem_filter, Finset.mem_Icc]
        obtain ⟨h1, h2, _⟩ := hLR α le_rfl hαβ
        exact ⟨⟨le_rfl, hαβ⟩, by omega⟩
      let u := S.max' ⟨α, hα_mem⟩
      have hu_mem : u ∈ S := Finset.max'_mem S ⟨α, hα_mem⟩
      simp only [S, Finset.mem_filter, Finset.mem_Icc] at hu_mem
      obtain ⟨⟨hαu, huβ⟩, hLu⟩ := hu_mem
      obtain ⟨_, _, huRu, hRuβ, hune⟩ := hLR u hαu huβ
      have hRu_lt : R u < β := by
        by_contra! hge
        have hRu_eq : R u = β := by omega
        exact hune (Prod.ext hLu hRu_eq)
      have hLw_gt : ∀ w : ℤ, u + 1 ≤ w → w ≤ R u + 1 → α ≤ L w := by
        intro w hwu hwR
        obtain ⟨h1, _⟩ := hLR w (by omega) (by omega)
        by_contra! hlt_α
        have hLw_eq : L w = α - 1 := by omega
        have hw_mem : w ∈ S := by
          simp only [S, Finset.mem_filter, Finset.mem_Icc]
          exact ⟨⟨by omega, by omega⟩, hLw_eq⟩
        have hw_le_u : w ≤ u := Finset.le_max' S w hw_mem
        omega
      by_cases hcase1 : ∃ v ∈ Finset.Icc (u + 1) (R u + 1), L v ≤ u ∧ R u + 1 ≤ R v
      · obtain ⟨v, hv_mem, hLvu, hRuv⟩ := hcase1
        rw [Finset.mem_Icc] at hv_mem
        have hLv_ge := hLw_gt v hv_mem.1 hv_mem.2
        exact ⟨u, v, hαu, by omega, by omega, by omega, hLvu, hv_mem.2, hRuv⟩
      · push Not at hcase1
        let α' := u + 1
        let β' := R u + 1
        let L' (w : ℤ) := max (L w) u
        let R' (w : ℤ) := min (R w) (R u + 1)
        have hm_lt : (β' - α').toNat < n := by
          dsimp [α', β']
          omega
        obtain ⟨s, t, hα's, hst, htβ', hL'st, hL'ts, htR's, hR'st⟩ :=
          ih (β' - α').toNat hm_lt α' β' (by dsimp [α', β']; omega) (by dsimp [α']; omega)
            (by dsimp [α', β']; omega) L' R' (by
              intro w hα'w hwβ'
              dsimp [α', β'] at hα'w hwβ'
              obtain ⟨_, hLw_ub, hwRw, _, _⟩ := hLR w (by omega) (by omega)
              refine ⟨by dsimp [L', α']; omega, by dsimp [L']; omega,
                by dsimp [R']; omega, by dsimp [R', β']; omega, ?_⟩
              intro heq_pair
              have h1 : max (L w) u = u + 1 - 1 := congr_arg Prod.fst heq_pair
              have h2 : min (R w) (R u + 1) = R u + 1 := congr_arg Prod.snd heq_pair
              have hLwu : L w ≤ u := by omega
              have hlt_R : R w < R u + 1 := hcase1 w (Finset.mem_Icc.mpr ⟨hα'w, hwβ'⟩) hLwu
              omega)
        dsimp [α', β', L', R'] at hα's htβ' hL'st hL'ts htR's hR'st
        exact ⟨s, t, by omega, hst, by omega, by omega, by omega, by omega, by omega⟩
  intro α β hα hαβ L R hLR
  exact key (β - α).toNat α β (by omega) hα hαβ L R hLR

/-- Zero-`sorry` derivation of Lemma 6.3 (`lem_6_3_biclique_list_hit`) from Theorem 2.2(b). -/
theorem lem_6_3_from_2_2b
    (h22b : ∀ (C₁ rStar N ℓ : ℕ), 2 ≤ C₁ → 1 ≤ rStar → 1 ≤ N → 1 ≤ ℓ →
      ∀ (F : Fin (ℓ + 1) → Finset (Fin N)),
        (∀ i : Fin (ℓ + 1), (F i).card ≤ C₁ * rStar) →
        ((F 0 ∩ F (Fin.last ℓ)).card : ℝ) ≤ (rStar : ℝ) / 4 →
        ∃ (s : Fin ℓ) (k : ℕ), k ≤ 8 * C₁ ∧
          ∃ (t : Fin k → Fin (ℓ + 1)) (A : Fin k → Finset (Fin N)) (I_k : Finset (Fin N)),
            Pairwise (fun i j => Disjoint (A i) (A j)) ∧
            (∀ r : Fin k, Disjoint (A r) I_k) ∧
            Finset.univ.biUnion A ∪ I_k = F s.castSucc ∩ F s.succ ∧
            (I_k.card : ℝ) ≤ (rStar : ℝ) / 2 ∧
            ∀ r : Fin k,
              let I_rem := (Finset.univ.filter (fun j : Fin k => r < j)).biUnion A ∪ I_k
              Disjoint (A r) (F (t r)) ∧
              I_rem ⊆ F (t r) ∧
              ((A r).card : ℝ) - (rStar : ℝ) / 4 ≤
                ((((F s.castSucc ∪ F s.succ) ∩ F (t r)) \ (A r ∪ I_rem)).card : ℝ)) :
    ∀ (N q C₁ rStar : ℕ), 2 ≤ N → 2 ≤ q → 3 ≤ C₁ → 1 ≤ rStar →
      ∀ (R : Fin N → Fin N → Fin q → Fin q → Prop),
        Symmetric2CSP R →
        ∀ (X : Finset (Fin N → Fin q)),
          X ⊆ satisfyingSet R →
          let η₀ : ℝ := 1 / 80
          (∀ x ∈ X, ∀ u ∈ X, ∀ z ∈ satisfyingSet R,
            hammingDist x u ≤ C₁ * rStar →
            hammingDist x z ≤ C₁ * rStar →
            ((threeWayDisagree x u z).card : ℝ) ≤ η₀ * (rStar : ℝ)) →
          let L_X : ↥X → ↥X → Finset ↥X := fun a b =>
            if 0 < hammingDist a.val b.val ∧ hammingDist a.val b.val ≤ C₁ * rStar then
              Finset.univ.filter (fun x : ↥X => x.val ∈ bicliqueWitnessList R C₁ rStar a.val b.val)
            else ∅
          ListHitCond C₁ rStar X L_X := by
  intro N q C₁ rStar hN hq hC₁ hrStar R hSym X hXsat η₀ hD3 L_X x ℓ hℓ w hw_ball hw_step hw_end
      hw_ov
  have hdis_card : ∀ a b : Fin N → Fin q, (disagreeSet a b).card = hammingDist a b := by
    intro a b; rfl
  let F : Fin (ℓ + 1) → Finset (Fin N) := fun i => disagreeSet x.val (w i).val
  obtain ⟨s, k, hk_max, t, A, I_k, hA_pw, hA_Ik, hA_part, hIk_card, h_step⟩ :=
    h22b C₁ rStar N ℓ (by omega) hrStar (by omega) hℓ F
      (fun i => by rw [hdis_card]; exact (hw_ball i).2) hw_ov
  refine ⟨s, ?_⟩
  let a := w s.castSucc
  let b := w s.succ
  have hab_step := hw_step s
  dsimp only [L_X]
  rw [ite_eq_left hab_step, Finset.mem_filter]
  refine ⟨Finset.mem_univ x, ?_⟩
  simp only [bicliqueWitnessList, Finset.mem_filter]
  refine ⟨hXsat x.prop, (hw_ball s.castSucc).1.symm ∘ Subtype.ext,
    (hw_ball s.succ).1.symm ∘ Subtype.ext,
    (hw_ball s.castSucc).2, (hw_ball s.succ).2, ?_⟩
  let I_rem : Fin k → Finset (Fin N) :=
    fun r => (Finset.univ.filter (fun j : Fin k => r < j)).biUnion A ∪ I_k
  let B_fut : Fin k → Finset (Fin N) :=
    fun r => I_rem r \ threeWayDisagree x.val a.val (w (t r)).val
  let B_out : Fin k → Finset (Fin N) :=
    fun r =>
      (((F s.castSucc ∪ F s.succ) ∩ F (t r)) \ (A r ∪ I_rem r)) \
        (threeWayDisagree x.val a.val (w (t r)).val ∪
         threeWayDisagree x.val b.val (w (t r)).val)
  refine ⟨k, hk_max, A, B_fut, B_out, I_k, hA_pw, hA_Ik, hA_part, hIk_card, ?_⟩
  intro r
  obtain ⟨hA_disj, hI_sub, h_out_lb⟩ := h_step r
  have ha3 : ((threeWayDisagree x.val a.val (w (t r)).val).card : ℝ) ≤ η₀ * (rStar : ℝ) :=
    hD3 x.val x.prop a.val a.prop (w (t r)).val (hXsat (w (t r)).prop)
      (hw_ball s.castSucc).2 (hw_ball (t r)).2
  have hb3 : ((threeWayDisagree x.val b.val (w (t r)).val).card : ℝ) ≤ η₀ * (rStar : ℝ) :=
    hD3 x.val x.prop b.val b.prop (w (t r)).val (hXsat (w (t r)).prop)
      (hw_ball s.succ).2 (hw_ball (t r)).2
  refine ⟨Finset.sdiff_subset,
    Finset.sdiff_subset.trans (Finset.sdiff_subset_sdiff Finset.inter_subset_left
        (Finset.Subset.refl _)),
    ?_, ?_, ?_⟩
  · intro u huA v hvB
    have hu_not : u ∉ F (t r) := Finset.disjoint_left.mp hA_disj huA
    have hwu : (w (t r)).val u = x.val u := by
      simp only [F, disagreeSet, Finset.mem_filter, Finset.mem_univ, true_and] at hu_not
      push Not at hu_not
      exact hu_not.symm
    have hsat_w := hXsat (w (t r)).prop
    simp only [satisfyingSet, Finset.mem_filter, Finset.mem_univ, true_and] at hsat_w
    have hv_Ft_act : v ∈ F (t r) ∧ (w (t r)).val v = activeColor x.val a.val b.val v := by
      rcases Finset.mem_union.mp hvB with hv_fut | hv_out
      · obtain ⟨hv_rem, hv_notD3a⟩ := Finset.mem_sdiff.mp hv_fut
        have hv_Ft : v ∈ F (t r) := hI_sub hv_rem
        have hv_I : v ∈ F s.castSucc ∩ F s.succ := by
          rw [← hA_part]
          rcases Finset.mem_union.mp hv_rem with hv_bi | hv_Ik
          · obtain ⟨j, _, hvAj⟩ := Finset.mem_biUnion.mp hv_bi
            exact Finset.mem_union_left _ (Finset.mem_biUnion.mpr ⟨j, Finset.mem_univ j, hvAj⟩)
          · exact Finset.mem_union_right _ hv_Ik
        have hav : a.val v ≠ x.val v := by
          have h1 := (Finset.mem_inter.mp hv_I).1
          simp only [F, disagreeSet, Finset.mem_filter, Finset.mem_univ, true_and] at h1
          exact h1.symm
        have hwv_ne : x.val v ≠ (w (t r)).val v := by
          simpa [F, disagreeSet] using hv_Ft
        refine ⟨hv_Ft, ?_⟩
        dsimp [activeColor]
        rw [ite_eq_left hav]
        simp only [threeWayDisagree, Finset.mem_filter, Finset.mem_univ, true_and] at hv_notD3a
        by_contra hne
        exact hv_notD3a ⟨hav.symm, hwv_ne, Ne.symm hne⟩
      · obtain ⟨hv_sdiff, hv_notD3⟩ := Finset.mem_sdiff.mp hv_out
        obtain ⟨hv_W, hv_Ft⟩ := Finset.mem_inter.mp (Finset.mem_sdiff.mp hv_sdiff).1
        simp only [Finset.mem_union, not_or] at hv_notD3
        have hwv_ne : x.val v ≠ (w (t r)).val v := by
          simpa [F, disagreeSet] using hv_Ft
        refine ⟨hv_Ft, ?_⟩
        dsimp [activeColor]
        by_cases hav : a.val v ≠ x.val v
        · rw [ite_eq_left hav]
          have hnot3 := hv_notD3.1
          simp only [threeWayDisagree, Finset.mem_filter, Finset.mem_univ, true_and] at hnot3
          by_contra hne
          exact hnot3 ⟨Ne.symm hav, hwv_ne, Ne.symm hne⟩
        · rw [ite_eq_right hav]
          push Not at hav
          simp only [F, disagreeSet, Finset.mem_union, Finset.mem_filter, Finset.mem_univ,
            true_and] at hv_W
          have hbv : x.val v ≠ b.val v := by
            rcases hv_W with h1 | h2
            · exact absurd hav.symm h1
            · exact h2
          have hnot3 := hv_notD3.2
          simp only [threeWayDisagree, Finset.mem_filter, Finset.mem_univ, true_and] at hnot3
          by_contra hne
          exact hnot3 ⟨hbv, hwv_ne, Ne.symm hne⟩
    have huv_ne : u ≠ v := by
      intro heq; subst heq; exact hu_not hv_Ft_act.1
    rw [← hwu, ← hv_Ft_act.2]
    rcases lt_trichotomy u v with hlt | rfl | hgt
    · exact hsat_w u v hlt
    · exact absurd rfl huv_ne
    · exact (hSym v u _ _).mp (hsat_w v u hgt)
  · have hsub : I_rem r \ B_fut r ⊆ threeWayDisagree x.val a.val (w (t r)).val := by
      intro v hv
      obtain ⟨hv1, hv2⟩ := Finset.mem_sdiff.mp hv
      by_contra hnot
      exact hv2 (Finset.mem_sdiff.mpr ⟨hv1, hnot⟩)
    have hcard : ((I_rem r \ B_fut r).card : ℝ) ≤
        ((threeWayDisagree x.val a.val (w (t r)).val).card : ℝ) := by
      exact_mod_cast Finset.card_le_card hsub
    dsimp [η₀] at ha3
    linarith
  · let S_out := ((F s.castSucc ∪ F s.succ) ∩ F (t r)) \ (A r ∪ I_rem r)
    let D3ab := threeWayDisagree x.val a.val (w (t r)).val ∪
        threeWayDisagree x.val b.val (w (t r)).val
    have hsub : S_out ⊆ B_out r ∪ D3ab := by
      intro v hv
      by_cases hvD : v ∈ D3ab
      · exact Finset.mem_union_right _ hvD
      · exact Finset.mem_union_left _ (Finset.mem_sdiff.mpr ⟨hv, hvD⟩)
    have hcard1 : (S_out.card : ℝ) ≤ ((B_out r).card : ℝ) + (D3ab.card : ℝ) := by
      have h := (Finset.card_le_card hsub).trans (Finset.card_union_le _ _)
      exact_mod_cast h
    have hcard2 : (D3ab.card : ℝ) ≤
        ((threeWayDisagree x.val a.val (w (t r)).val).card : ℝ) +
        ((threeWayDisagree x.val b.val (w (t r)).val).card : ℝ) := by
      exact_mod_cast Finset.card_union_le _ _
    change ((A r).card : ℝ) - (rStar : ℝ) / 4 ≤ (S_out.card : ℝ) at h_out_lb
    dsimp [η₀] at ha3 hb3
    linarith

open Classical in
private lemma glue_hc_bound_4p :
    ∀ (M_L : ℝ),
      (0 : ℝ) < M_L →
        let M : ℝ := (2 : ℝ) * M_L + (5 : ℝ);
        ∀ (p C : ℝ),
          (1 : ℝ) ≤ C →
            (1 : ℝ) ≤ C ^ p →
              (2 : ℝ) ^ (-((81 : ℝ) * M) * C ^ ((4 : ℝ) * p)) ≤
                (2 : ℝ) ^ (-((81 : ℝ) * M) * C ^ ((3 : ℝ) * p) * Real.logb (2 : ℝ) (C ^ p + (1 :
                    ℝ))) := by
  classical
  intro M_L hML_pos M p C hC hCp1
  apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
  have hexp_le : C ^ p + 1 ≤ (2 : ℝ) ^ (C ^ p) := by
    have h2log2 : (1 : ℝ) ≤ 2 * Real.log 2 := by
      have hexp4 : Real.exp 1 ≤ (4 : ℝ) := by linarith [Real.exp_one_lt_d9]
      have hlog4 : Real.log (Real.exp 1) ≤ Real.log 4 :=
        Real.log_le_log (Real.exp_pos 1) hexp4
      have h4eq : Real.log (4 : ℝ) = 2 * Real.log 2 := by
        have : (4 : ℝ) = (2 : ℝ) ^ (2 : ℕ) := by norm_num
        rw [this, Real.log_pow]; ring
      rw [Real.log_exp, h4eq] at hlog4
      exact hlog4
    have hlin : C ^ p + 1 ≤ 2 * (1 + (C ^ p - 1) * Real.log 2) := by nlinarith
    have hexp_t : 1 + (C ^ p - 1) * Real.log 2 ≤ Real.exp ((C ^ p - 1) * Real.log 2) := by
      linarith [Real.add_one_le_exp ((C ^ p - 1) * Real.log 2)]
    have hrpow_eq : (2 : ℝ) ^ (C ^ p) = 2 * Real.exp ((C ^ p - 1) * Real.log 2) := by
      have hsplit : C ^ p = 1 + (C ^ p - 1) := by ring
      rw [hsplit, Real.rpow_add (by norm_num), Real.rpow_one,
        Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 2)]
      congr 2; ring
    linarith
  have hlog_Cp : Real.logb 2 (C ^ p + 1) ≤ C ^ p := by
    have hb : Real.logb 2 (C ^ p + 1) ≤ Real.logb 2 ((2 : ℝ) ^ (C ^ p)) :=
      Real.logb_le_logb_of_le (by norm_num) (by positivity) hexp_le
    rwa [Real.logb_rpow (by norm_num) (by norm_num)] at hb
  have hC4p : C ^ (3 * p) * C ^ p = C ^ (4 * p) := by
    rw [← Real.rpow_add (by positivity)]
    congr 1; ring
  have hMC_nn : 0 ≤ 81 * M * C ^ (3 * p) := by dsimp [M]; positivity
  have hmul := mul_le_mul_of_nonneg_left hlog_Cp hMC_nn
  have hrhs : 81 * M * C ^ (3 * p) * C ^ p = 81 * M * C ^ (4 * p) := by
    rw [mul_assoc, hC4p]
  linarith

private lemma spanner_exponent_bound (M_L : ℝ) (C₁ L : ℕ) (hC₁ : 3 ≤ C₁)
    (hL_ub : (L : ℝ) ≤ M_L * (C₁ : ℝ) ^ 3 * Real.logb 2 (C₁ : ℝ)) :
    ((2 * L + 5 : ℕ) : ℝ) ≤ (2 * M_L + 5) * (C₁ : ℝ) ^ 3 * Real.logb 2 (C₁ : ℝ) := by
  have hC1_pow : (1 : ℝ) ≤ (C₁ : ℝ) ^ 3 := by
    have : (1 : ℝ) ≤ (C₁ : ℝ) := by exact_mod_cast (by omega : 1 ≤ C₁)
    exact one_le_pow₀ this
  have hlog1 : (1 : ℝ) ≤ Real.logb 2 (C₁ : ℝ) := by
    have h1 : Real.logb 2 (2 : ℝ) = 1 := Real.logb_self_eq_one (by norm_num)
    have h2 : Real.logb 2 (2 : ℝ) ≤ Real.logb 2 (C₁ : ℝ) :=
      Real.logb_le_logb_of_le (by norm_num) (by norm_num) (by exact_mod_cast (by omega : 2 ≤ C₁))
    linarith
  have hprod1 : (1 : ℝ) ≤ (C₁ : ℝ) ^ 3 * Real.logb 2 (C₁ : ℝ) := by nlinarith
  push_cast
  nlinarith

/-- Zero-`sorry` derivation of Theorem 1.3
(`thm_1_3_non_metric_steiner_spanner_lower_bound`) from Modules 1–3 (`thm_2_1b`,
`thm_2_2a`, `thm_2_3`). -/
theorem thm_1_3_from_modules
    (h21b : ∀ (N q L rStar C₁ : ℕ), 2 ≤ N → 2 ≤ q → 1 ≤ rStar → N = 2 ^ L * rStar →
      ∀ (p C : ℝ), 1 ≤ p → 1 ≤ C → ⌈C ^ p⌉₊ ≤ C₁ →
        (∀ x y : Fin N → Fin q,
          lpDist p (oneHotEmbed x) (oneHotEmbed y) = (2 * (hammingDist x y : ℝ)) ^ (1 / p)) ∧
        (∀ (X : Finset (Fin N → Fin q)),
          2 ≤ X.card →
          (∀ x ∈ X, ∀ y ∈ X, x ≠ y → (rStar : ℝ) / 2 ≤ (hammingDist x y : ℝ)) →
          ∀ (e : Fin X.card ≃ ↥X),
            let P : Fin X.card → (Fin (N * q) → ℝ) := fun i => oneHotEmbed (e i).val
            (∀ i : Fin X.card, ∀ k : Fin (N * q), P i k = 0 ∨ P i k = 1) ∧
            Function.Injective P ∧
            aspectRatio p P ≤ (2 : ℝ) ^ (L + 1) ∧
            ∀ (S : Type) [Fintype S]
              (H : SimpleGraph (Fin X.card ⊕ S))
              (w : Sym2 (Fin X.card ⊕ S) → ℝ),
              IsNonMetricSteinerSpanner p P C H w →
              ∃ G_hat : SimpleGraph ↥X,
                Nat.card G_hat.edgeSet ≤ Nat.card H.edgeSet ∧
                (∀ a b : ↥X, G_hat.Adj a b →
                  0 < hammingDist a.val b.val ∧ hammingDist a.val b.val ≤ C₁ * rStar) ∧
                (∀ x y : ↥X, hammingDist x.val y.val = rStar →
                  ∃ q_walk : G_hat.Walk x y,
                    q_walk.IsPath ∧
                    ∀ z ∈ q_walk.support, hammingDist x.val z.val ≤ C₁ * rStar)))
    (h22a : ∀ (C₁ rStar N q K : ℕ), 2 ≤ C₁ → 1 ≤ rStar → 2 ≤ N → 2 ≤ q → 1 ≤ K →
      ∀ (X : Finset (Fin N → Fin q)) (G_hat : SimpleGraph ↥X)
        (L : ↥X → ↥X → Finset ↥X),
        (∀ a b : ↥X, G_hat.Adj a b →
          0 < hammingDist a.val b.val ∧ hammingDist a.val b.val ≤ C₁ * rStar) →
        (∀ x y : ↥X, hammingDist x.val y.val = rStar →
          ∃ q_walk : G_hat.Walk x y,
            q_walk.IsPath ∧ ∀ z ∈ q_walk.support, hammingDist x.val z.val ≤ C₁ * rStar) →
        ListSizeCond C₁ rStar K X L →
        OverlapCond C₁ rStar K X →
        ListHitCond C₁ rStar X L →
        (exactDistPairs X rStar).card ≤ 2 * K ^ 2 * Nat.card G_hat.edgeSet)
    (h23 : ∃ M_L : ℝ, 0 < M_L ∧
      ∀ C₁ : ℕ, 3 ≤ C₁ →
        ∃ (L q K R₀ : ℕ) (μ₀ : ℝ),
          2 ≤ L ∧ (L : ℝ) ≤ M_L * (C₁ : ℝ) ^ 3 * Real.logb 2 (C₁ : ℝ) ∧
          2 ≤ q ∧ K = 20 * C₁ ^ 2 ∧ 160 * C₁ < R₀ ∧ 0 < μ₀ ∧
          let c : ℝ := (2 : ℝ) ^ (-((2 * L + 5 : ℕ) : ℝ))
          ∀ rStar : ℕ, R₀ ≤ rStar →
            let N : ℕ := 2 ^ L * rStar
            ∃ (X : Finset (Fin N → Fin q)) (L_X : ↥X → ↥X → Finset ↥X),
              2 ≤ X.card ∧
              (2 : ℝ) / 5 * μ₀ * (rStar : ℝ) ≤ Real.logb 2 (X.card : ℝ) ∧
              Real.logb 2 (X.card : ℝ) ≤ (3 : ℝ) / 2 * μ₀ * (rStar : ℝ) ∧
              (1 : ℝ) / 192 * (X.card : ℝ) ^ (1 + c) ≤ ((exactDistPairs X rStar).card : ℝ) ∧
              (∀ x ∈ X, ∀ y ∈ X, x ≠ y → (rStar : ℝ) / 2 ≤ (hammingDist x y : ℝ)) ∧
              ListSizeCond C₁ rStar K X L_X ∧
              OverlapCond C₁ rStar K X ∧
              ListHitCond C₁ rStar X L_X) :
    ∃ (M : ℝ) (c c₀ β₁ β₂ A : ℕ → ℝ),
      0 < M ∧
      (∀ C₁ : ℕ, 3 ≤ C₁ →
        (2 : ℝ) ^ (-M * (C₁ : ℝ) ^ 3 * Real.logb 2 (C₁ : ℝ)) ≤ c C₁ ∧
        0 < c₀ C₁ ∧ 0 < β₁ C₁ ∧ β₁ C₁ ≤ β₂ C₁ ∧ 0 < A C₁) ∧
      ∀ (p : ℝ), 1 ≤ p →
        ∀ (C : ℝ), 1 ≤ C →
          let C₁ : ℕ := max 3 ⌈C ^ p⌉₊
          (2 : ℝ) ^ (-(81 * M) * C ^ (4 * p)) ≤
            (2 : ℝ) ^ (-(81 * M) * C ^ (3 * p) * Real.logb 2 (C ^ p + 1)) ∧
          (2 : ℝ) ^ (-(81 * M) * C ^ (3 * p) * Real.logb 2 (C ^ p + 1)) ≤ c C₁ ∧
          ∃ nSeq : ℕ → ℕ, StrictMono nSeq ∧ (∀ j : ℕ, 2 ≤ nSeq j) ∧
            ∀ j : ℕ,
              ∃ (d : ℕ) (P : Fin (nSeq j) → (Fin d → ℝ)),
                1 ≤ d ∧
                β₁ C₁ * Real.logb 2 (nSeq j : ℝ) ≤ (d : ℝ) ∧
                (d : ℝ) ≤ β₂ C₁ * Real.logb 2 (nSeq j : ℝ) ∧
                (∀ i : Fin (nSeq j), ∀ k : Fin d, P i k = 0 ∨ P i k = 1) ∧
                Function.Injective P ∧
                aspectRatio p P ≤ A C₁ ∧
                ∀ (S : Type) [Fintype S]
                  (H : SimpleGraph (Fin (nSeq j) ⊕ S))
                  (w : Sym2 (Fin (nSeq j) ⊕ S) → ℝ),
                  IsNonMetricSteinerSpanner p P C H w →
                  c₀ C₁ * (nSeq j : ℝ) ^ (1 + c C₁) ≤ (Nat.card H.edgeSet : ℝ) := by
  obtain ⟨M_L, hML_pos, h23_C1⟩ := h23
  choose L_f q_f K_f R0_f mu_f h_spec using fun (C₁ : {x : ℕ // 3 ≤ x}) => h23_C1 C₁.1 C₁.2
  let M : ℝ := 2 * M_L + 5
  let c_fn (C₁ : ℕ) : ℝ :=
    if h : 3 ≤ C₁ then (2 : ℝ) ^ (-((2 * L_f ⟨C₁, h⟩ + 5 : ℕ) : ℝ)) else 1
  let c0_fn (C₁ : ℕ) : ℝ :=
    if h : 3 ≤ C₁ then 1 / (384 * (K_f ⟨C₁, h⟩ : ℝ) ^ 2) else 1
  let beta1_fn (C₁ : ℕ) : ℝ :=
    if h : 3 ≤ C₁ then 2 * (2 : ℝ) ^ (L_f ⟨C₁, h⟩) * (q_f ⟨C₁, h⟩ : ℝ) / (3 * mu_f ⟨C₁, h⟩) else 1
  let beta2_fn (C₁ : ℕ) : ℝ :=
    if h : 3 ≤ C₁ then 5 * (2 : ℝ) ^ (L_f ⟨C₁, h⟩) * (q_f ⟨C₁, h⟩ : ℝ) / (2 * mu_f ⟨C₁, h⟩) else 1
  let A_fn (C₁ : ℕ) : ℝ :=
    if h : 3 ≤ C₁ then (2 : ℝ) ^ (L_f ⟨C₁, h⟩ + 1) else 1
  have hc_C1 : ∀ (C₁ : ℕ) (hC₁ : 3 ≤ C₁),
      ((2 * L_f ⟨C₁, hC₁⟩ + 5 : ℕ) : ℝ) ≤ M * (C₁ : ℝ) ^ 3 * Real.logb 2 (C₁ : ℝ) := by
    intro C₁ hC₁
    exact spanner_exponent_bound M_L C₁ (L_f ⟨C₁, hC₁⟩) hC₁ (h_spec ⟨C₁, hC₁⟩).2.1
  refine ⟨M, c_fn, c0_fn, beta1_fn, beta2_fn, A_fn, by positivity, ?_, ?_⟩
  · intro C₁ hC₁
    simp only [c_fn, c0_fn, beta1_fn, beta2_fn, A_fn, dite_eq_left hC₁]
    obtain ⟨hL2, _, hq2, hK_eq, hR0, hmu_pos, _⟩ := h_spec ⟨C₁, hC₁⟩
    have hc_le :
        (2 : ℝ) ^ (-M * (C₁ : ℝ) ^ 3 * Real.logb 2 (C₁ : ℝ)) ≤
          (2 : ℝ) ^ (-((2 * L_f ⟨C₁, hC₁⟩ + 5 : ℕ) : ℝ)) := by
      apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
      linarith [hc_C1 C₁ hC₁]
    have hK_pos : (0 : ℝ) < (K_f ⟨C₁, hC₁⟩ : ℝ) := by
      rw [hK_eq]; push_cast; positivity
    refine ⟨hc_le, by positivity, by positivity, ?_, by positivity⟩
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    have : (0 : ℝ) ≤ (2 : ℝ) ^ L_f ⟨C₁, hC₁⟩ * (q_f ⟨C₁, hC₁⟩ : ℝ) := by positivity
    nlinarith
  · intro p hp C hC
    dsimp only
    set C₁ : ℕ := max 3 ⌈C ^ p⌉₊
    have hC₁ : 3 ≤ C₁ := le_max_left 3 _
    have hC₁_ceil : ⌈C ^ p⌉₊ ≤ C₁ := le_max_right 3 _
    obtain ⟨hL2, hL_ub, hq2, hK_eq, hR0, hmu_pos, h_cloud⟩ := h_spec ⟨C₁, hC₁⟩
    have hCp1 : 1 ≤ C ^ p := Real.one_le_rpow hC (by linarith)
    have hceil : (⌈C ^ p⌉₊ : ℝ) ≤ 3 * C ^ p := by
      have h1 : (⌈C ^ p⌉₊ : ℝ) < C ^ p + 1 := Nat.ceil_lt_add_one (by positivity)
      linarith
    have hC1_le : (C₁ : ℝ) ≤ 3 * C ^ p := by
      dsimp [C₁]; push_cast; exact max_le (by linarith) hceil
    have hC1_cubed : (C₁ : ℝ) ^ 3 ≤ 27 * C ^ (3 * p) := by
      calc (C₁ : ℝ) ^ 3
          ≤ (3 * C ^ p) ^ 3 := pow_le_pow_left₀ (by positivity) hC1_le 3
        _ = 27 * (C ^ p) ^ (3 : ℕ) := by ring
        _ = 27 * C ^ (p * 3) := by
            rw [← Real.rpow_natCast (C ^ p) 3, ← Real.rpow_mul (by linarith)]
            push_cast; rfl
        _ = 27 * C ^ (3 * p) := by ring_nf
    have hC1_log : Real.logb 2 (C₁ : ℝ) ≤ 3 * Real.logb 2 (C ^ p + 1) := by
      have hle_pow : (C₁ : ℝ) ≤ (C ^ p + 1) ^ (3 : ℕ) := by
        have hpos_Cp : 0 ≤ C ^ p := by linarith
        nlinarith [sq_nonneg (C ^ p), pow_nonneg hpos_Cp 3]
      have hC1_pos : (0 : ℝ) < (C₁ : ℝ) := by exact_mod_cast (by omega : 0 < C₁)
      have hb : Real.logb 2 (C₁ : ℝ) ≤ Real.logb 2 ((C ^ p + 1) ^ (3 : ℕ)) :=
        Real.logb_le_logb_of_le (by norm_num) hC1_pos hle_pow
      have heq : Real.logb 2 ((C ^ p + 1) ^ (3 : ℕ)) = 3 * Real.logb 2 (C ^ p + 1) := by
        simp only [Real.logb, Real.log_pow]; ring
      linarith
    have hc_bound_3p :
        (2 : ℝ) ^ (-(81 * M) * C ^ (3 * p) * Real.logb 2 (C ^ p + 1)) ≤ c_fn C₁ := by
      simp only [c_fn, dite_eq_left hC₁]
      apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
      have hlog_C1_nn : 0 ≤ Real.logb 2 (C₁ : ℝ) :=
        Real.logb_nonneg (by norm_num) (by exact_mod_cast (by omega : 1 ≤ C₁))
      have hprod :
          (C₁ : ℝ) ^ 3 * Real.logb 2 (C₁ : ℝ) ≤
            (27 * C ^ (3 * p)) * (3 * Real.logb 2 (C ^ p + 1)) :=
        mul_le_mul hC1_cubed hC1_log hlog_C1_nn (by positivity)
      have hM_nn : 0 ≤ M := by dsimp [M]; positivity
      have hMprod := mul_le_mul_of_nonneg_left hprod hM_nn
      linarith [hc_C1 C₁ hC₁]
    have hc_bound_4p :=
      @glue_hc_bound_4p M_L hML_pos p C hC hCp1
    refine ⟨hc_bound_4p, hc_bound_3p, ?_⟩
    let r_seq (j : ℕ) : ℕ := 4 ^ (j + 1) * R0_f ⟨C₁, hC₁⟩
    have hr_ge : ∀ j : ℕ, R0_f ⟨C₁, hC₁⟩ ≤ r_seq j := by
      intro j
      dsimp [r_seq]
      exact Nat.le_mul_of_pos_left _ (by positivity)
    choose X_seq LX_seq hX_spec using fun j => h_cloud (r_seq j) (hr_ge j)
    refine ⟨fun j => (X_seq j).card, ?_, fun j => (hX_spec j).1, ?_⟩
    · apply strictMono_nat_of_lt_succ
      intro j
      have h_lo := (hX_spec (j + 1)).2.1
      have h_hi := (hX_spec j).2.2.1
      have hr_pos : (0 : ℝ) < (R0_f ⟨C₁, hC₁⟩ : ℝ) := by
        have : 0 < R0_f ⟨C₁, hC₁⟩ := by omega
        exact_mod_cast this
      have h_strict_log : Real.logb 2 ((X_seq j).card : ℝ) < Real.logb 2 ((X_seq (j + 1)).card :
          ℝ) := by
        have h_r : (r_seq (j + 1) : ℝ) = 4 * (r_seq j : ℝ) := by
          dsimp [r_seq]; push_cast; ring
        have hrj_pos : (0 : ℝ) < (r_seq j : ℝ) := by
          have : 0 < r_seq j := by
            have := hr_ge j
            omega
          exact_mod_cast this
        nlinarith
      by_contra! hle
      have h1 : (0 : ℝ) < ((X_seq (j + 1)).card : ℝ) := by
        have := (hX_spec (j + 1)).1; exact_mod_cast (by omega : 0 < (X_seq (j + 1)).card)
      have hmono : Real.logb 2 ((X_seq (j + 1)).card : ℝ) ≤ Real.logb 2 ((X_seq j).card : ℝ) :=
        Real.logb_le_logb_of_le (by norm_num) h1 (by exact_mod_cast hle)
      linarith
    · intro j
      obtain ⟨hXcard2, hlog_lo, hlog_hi, hE_lb, hmin_dist, hLS, hOv, hLH⟩ := hX_spec j
      let L := L_f ⟨C₁, hC₁⟩
      let q := q_f ⟨C₁, hC₁⟩
      let K := K_f ⟨C₁, hC₁⟩
      let rStar := r_seq j
      let N := 2 ^ L * rStar
      let d := N * q
      let e : Fin (X_seq j).card ≃ ↥(X_seq j) :=
        (Fin.castOrderIso (Fintype.card_coe (X_seq j)).symm).toEquiv.trans (Fintype.equivFin
            ↥(X_seq j)).symm
      let P : Fin (X_seq j).card → (Fin d → ℝ) := fun i => oneHotEmbed (e i).val
      have hrStar1 : 1 ≤ rStar := by
        have := hr_ge j
        have : 3 ≤ (⟨C₁, hC₁⟩ : {x : ℕ // 3 ≤ x}).1 := hC₁
        omega
      have hN2 : 2 ≤ N := by
        dsimp [N]
        have : 4 ≤ 2 ^ L := Nat.pow_le_pow_right (by norm_num : 0 < 2) hL2
        nlinarith
      have hd1 : 1 ≤ d := by dsimp [d]; nlinarith
      have h_mod1 := (h21b N q L rStar C₁ hN2 hq2 hrStar1 rfl p C hp hC hC₁_ceil).2
        (X_seq j) hXcard2 hmin_dist e
      obtain ⟨hP_bool, hP_inj, hP_ar, hP_proj⟩ := h_mod1
      refine ⟨d, P, hd1, ?_, ?_, hP_bool, hP_inj, ?_, ?_⟩
      · simp only [beta1_fn, dite_eq_left hC₁]
        have hd_eq : (d : ℝ) = (2 : ℝ) ^ L * (q : ℝ) * (rStar : ℝ) := by
          dsimp [d, N]; push_cast; ring
        rw [hd_eq, div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
        have : (0 : ℝ) ≤ (2 : ℝ) ^ L * (q : ℝ) := by positivity
        nlinarith
      · simp only [beta2_fn, dite_eq_left hC₁]
        have hd_eq : (d : ℝ) = (2 : ℝ) ^ L * (q : ℝ) * (rStar : ℝ) := by
          dsimp [d, N]; push_cast; ring
        rw [hd_eq, div_mul_eq_mul_div, le_div_iff₀ (by positivity)]
        have : (0 : ℝ) ≤ (2 : ℝ) ^ L * (q : ℝ) := by positivity
        nlinarith
      · simp only [A_fn, dite_eq_left hC₁]
        exact hP_ar
      · intro S _ H w hH
        obtain ⟨G_hat, hG_edges, hG_adj, hG_path⟩ := hP_proj S H w hH
        have hK1 : 1 ≤ K := by
          dsimp [K]
          rw [hK_eq]
          change 1 ≤ 20 * C₁ ^ 2
          nlinarith only [hC₁]
        have h_charge := h22a C₁ rStar N q K (le_trans (by norm_num) hC₁) hrStar1 hN2 hq2 hK1
          (X_seq j) G_hat (LX_seq j) hG_adj hG_path hLS hOv hLH
        dsimp only [c0_fn, c_fn]
        rw [dite_eq_left hC₁, dite_eq_left hC₁]
        have hK_pos : (0 : ℝ) < (K : ℝ) ^ 2 := by
          have : 0 < K := by omega
          positivity
        have h_card_ineq : ((exactDistPairs (X_seq j) rStar).card : ℝ) ≤
            2 * (K : ℝ) ^ 2 * (Nat.card H.edgeSet : ℝ) := by
          have h1 : ((exactDistPairs (X_seq j) rStar).card : ℝ) ≤
              2 * (K : ℝ) ^ 2 * (Nat.card G_hat.edgeSet : ℝ) := by exact_mod_cast h_charge
          have h2 : (Nat.card G_hat.edgeSet : ℝ) ≤ (Nat.card H.edgeSet : ℝ) := by exact_mod_cast
              hG_edges
          nlinarith only [h1, h2]
        rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
        nlinarith only [hE_lb, h_card_ineq]

end HighDimSteinerSpanners.Proofs.Glue
