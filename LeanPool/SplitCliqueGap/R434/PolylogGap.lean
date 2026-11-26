/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
/- Modified by Lean Pool contributors for the current Lean and Mathlib toolchain. -/
module

public import LeanPool.SplitCliqueGap.R434.UniversalR434
public import LeanPool.SplitCliqueGap.R434.PolylogOrder
public import LeanPool.SplitCliqueGap.R434.GroupedGap
import Mathlib.Tactic.Convert
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Push
import Mathlib.Tactic.Ring

/-! The endpoint coefficient with a logarithmic prefactor at every large order. -/

@[expose] public section

namespace GapExtremal.R434

open Real EHPS

/-- The coefficient in the polylogarithmic cut-survival estimate. -/
noncomputable def connectivityConstant : ℝ := sqrt (log (24/7)) / (1050015 * exp 1)

/-- The leading coefficient of the basic nearly quadratic gap bound. -/
noncomputable def gapConstant : ℝ := 2 * orderAmplitude 1050015 (200*(1080/7)^2) (log (24/7))

private theorem universal_R434_with (H : ℕ → ℕ) (A : ℝ) (hA : 1 ≤ A)
    (hH : ∀ j : ℕ, 1 ≤ j → 1 ≤ H j ∧ (H j : ℝ) ≤ A * (j : ℝ))
    (loss : ∀ {U : Type} [Fintype U] [DecidableEq U], SimpleGraph U → ℝ)
    (cut : ℕ → ℕ → ℕ → ℕ)
    (realize : ∀ {ε : ℝ} {m j n : ℕ} [NeZero m], 0 < ε → ε ≤ 1 → Odd m →
      1 ≤ j → 100 ≤ n → H j * (m^2)^j ≤ n →
      ∃ (V : Type) (_ : Fintype V) (_ : DecidableEq V) (G : SimpleGraph V),
        Fintype.card V = n ∧ IsSplit G ∧ G.Connected ∧ SurvivesCuts G (cut n m j) ∧
        6 * (((gridSupport ε m).card : ℝ)^j * ((m : ℝ)^2)^j) /
          (27 * (1 + 200 / ε^2 * (j : ℝ) * (m : ℝ)^2)) ≤ loss G) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      ∃ (V : Type) (_ : Fintype V) (_ : DecidableEq V) (G : SimpleGraph V),
        Fintype.card V = n ∧ IsSplit G ∧ G.Connected ∧
        (∃ m j : ℕ, SurvivesCuts G (cut n m j) ∧
          sqrt (log (24/7)) / (A * exp 1) * n / sqrt (log n) ≤ (m : ℝ)^(2*j)) ∧
        2 * orderAmplitude A (200*(1080/7)^2) (log (24/7)) * n^2 /
          (log n)^(5/2 : ℝ) * exp (-2 * sqrt (log (24/7) * log n)) ≤ loss G := by
  let c := log (24/7)
  have hc : 0 < c := log_pos (by norm_num)
  obtain ⟨N,hN⟩ := joint_order_parameters H A (200*(1080/7)^2) c 24000
    hA (by norm_num) hc (by norm_num) hH
  refine ⟨max N 100, fun n hn => ?_⟩
  have hn₀ : 100 ≤ n := (le_max_right _ _).trans hn
  obtain ⟨m,j,hm,hod,hj,horder,hw,hconnect,hsize⟩ := hN n ((le_max_left _ _).trans hn)
  have horder' : H j * (m^2)^j ≤ n := by simpa only [pow_mul] using horder
  let : NeZero m := ⟨by omega⟩
  have hj1 : (1 : ℝ) ≤ j := by exact_mod_cast hj
  have hjp : 0 < (j : ℝ) := by linarith
  let ε := 7 / (1080*(j : ℝ))
  have he : 0 < ε := by dsimp [ε]; positivity
  have hem : ε ≤ 7 / 1080 := by
    dsimp [ε]
    apply (div_le_div_iff₀ (by positivity) (by norm_num)).mpr
    linarith
  have hgrid := density_grid_uniform he (by linarith : 0 ≤ 1/12 - 3*ε) (m := m)
    (by dsimp [ε]; field_simp; linarith only [hw])
  obtain ⟨V,fV,dV,G,hcard,hsplit,hconn,hcuts,hgap⟩ :=
    realize he (by linarith) hod hj hn₀ horder'
  refine ⟨V,fV,dV,G,hcard,hsplit,hconn,⟨m,j,hcuts,hconnect⟩,?_⟩
  let ρ : ℝ := 7/24
  let u : ℝ := -(2/(3*(j : ℝ)))
  have hu : -(2/3 : ℝ) ≤ u := by
    apply neg_le_neg
    apply (div_le_div_iff₀ (by positivity) (by norm_num)).mpr
    linarith
  have hb := one_add_mul_le_pow (show -2 ≤ u by linarith) j
  have hju : (j : ℝ)*u = -(2/3 : ℝ) := by dsimp [u]; field_simp
  have hb' : 1/3 ≤ (1+u)^j := by linarith only [hb,hju]
  have hd : ρ*(1+u) ≤ 7/24-30*ε := by dsimp [ρ,u,ε]; field_simp; linarith
  have hbase : 0 ≤ ρ*(1+u)*(m : ℝ)^2 := by
    apply mul_nonneg _ (sq_nonneg _)
    exact mul_nonneg (by norm_num [ρ]) (by linarith)
  have hp := pow_le_pow_left₀ hbase ((mul_le_mul_of_nonneg_right hd (sq_nonneg _)).trans hgrid) j
  have hρ : ρ^j = exp (-c*(j : ℝ)) := by
    have hr : ρ = exp (-c) := by rw [exp_neg, exp_log (by norm_num : (0 : ℝ) < 24/7)]; norm_num [ρ]
    rw [hr, ← exp_nat_mul, mul_comm]
  rw [mul_pow, mul_pow, hρ] at hp
  have hnum : exp (-c*(j : ℝ)) / 3 * (m : ℝ)^(4*j) ≤
      ((gridSupport ε m).card : ℝ)^j * ((m : ℝ)^2)^j := by
    have hb'' := mul_le_mul_of_nonneg_left hb' (exp_pos (-c*(j : ℝ))).le
    have hjj : (m : ℝ)^(4*j) = ((m : ℝ)^2)^j * ((m : ℝ)^2)^j := by
      rw [← pow_add, ← pow_mul]; congr 1; omega
    rw [hjj]
    have h := mul_le_mul_of_nonneg_right hb'' (show 0 ≤ ((m : ℝ)^2)^j by positivity)
    have h' := mul_le_mul_of_nonneg_right (h.trans hp) (show 0 ≤ ((m : ℝ)^2)^j by positivity)
    linarith only [h']
  have hd' : 200/ε^2*(j : ℝ) = (200*(1080/7)^2)*(j : ℝ)^3 := by dsimp [ε]; field_simp
  rw [hd'] at hgap
  have hfin := div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hnum (by norm_num : (0 : ℝ)
    ≤ 6))
    (show 0 ≤ 27*(1+200*(1080/7)^2*(j : ℝ)^3*(m : ℝ)^2) by positivity)
  change _ ≤ loss G
  have hs := (mul_le_mul_of_nonneg_right hsize (by norm_num : (0 : ℝ) ≤ 2))
  change 2 * orderAmplitude A (200*(1080/7)^2) (log (24/7)) * _ / _ * _ ≤ _
  dsimp only [c] at hs hfin hgap ⊢
  convert hs.trans (le_trans (le_of_eq ?_) (hfin.trans hgap)) using 1 <;> ring


theorem universal_R434_robust :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      ∃ (V : Type) (_ : Fintype V) (_ : DecidableEq V) (G : SimpleGraph V),
        Fintype.card V = n ∧ IsSplit G ∧ G.Connected ∧
        (∃ d : ℕ, SurvivesCuts G d ∧ connectivityConstant * n / sqrt (log n) ≤ d) ∧
        gapConstant * n^2 / (log n)^(5/2 : ℝ) * exp (-2 * sqrt (log (24/7) * log n)) ≤ gap G := by
  have hH (j : ℕ) (hj : 1 ≤ j) : 1 ≤ hostFactor j ∧ (hostFactor j : ℝ) ≤ 1050015*(j : ℝ) := by
    have hjR : (1 : ℝ) ≤ j := by exact_mod_cast hj
    unfold hostFactor
    constructor
    · omega
    · push_cast
      linarith
  obtain ⟨N,hN⟩ := universal_R434_with hostFactor 1050015 (by norm_num) hH gap
    (fun _ m j => (m^2)^j)
    (fun he he₁ hm _ _ h => finite_gap_of_product_robust he he₁ hm h)
  refine ⟨N, fun n hn => ?_⟩
  obtain ⟨V,fV,dV,G,hcard,hs,hconn,⟨m,j,hc,hb⟩,hg⟩ := hN n hn
  exact ⟨V,fV,dV,G,hcard,hs,hconn,⟨_,hc,by simpa only [connectivityConstant, Nat.cast_pow,
    ← pow_mul, Nat.cast_ofNat] using hb⟩,hg⟩

theorem universal_R434_compact :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      ∃ (V : Type) (_ : Fintype V) (_ : DecidableEq V) (G : SimpleGraph V),
        Fintype.card V = n ∧ IsSplit G ∧ G.Connected ∧
        (∃ d : ℕ, SurvivesCuts G d ∧ sqrt (log (24/7)) / (3135 * exp 1) * n / sqrt (log n) ≤ d) ∧
        2 * orderAmplitude 3135 (200*(1080/7)^2) (log (24/7)) * n^2 /
          (log n)^(5/2 : ℝ) * exp (-2 * sqrt (log (24/7) * log n)) ≤ gap G := by
  have hH (j : ℕ) (hj : 1 ≤ j) : 1 ≤ compactHostFactor j ∧ (compactHostFactor j : ℝ) ≤ 3135*(j :
    ℝ) := by
    have hjR : (1 : ℝ) ≤ j := by exact_mod_cast hj
    unfold compactHostFactor
    constructor
    · omega
    · push_cast
      linarith
  obtain ⟨N,hN⟩ := universal_R434_with compactHostFactor 3135 (by norm_num) hH gap
    (fun _ m j => (m^2)^j) (fun he he₁ hm _ _ h => finite_gap_of_product_compact he he₁ hm h)
  refine ⟨N, fun n hn => ?_⟩
  obtain ⟨V,fV,dV,G,hcard,hs,hconn,⟨m,j,hc,hb⟩,hg⟩ := hN n hn
  exact ⟨V,fV,dV,G,hcard,hs,hconn,⟨_,hc,by simpa only [Nat.cast_pow, ← pow_mul, Nat.cast_ofNat]
    using hb⟩,hg⟩

theorem universal_R434_linear_mixed :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      ∃ (V : Type) (_ : Fintype V) (_ : DecidableEq V) (G : SimpleGraph V),
        Fintype.card V = n ∧ IsSplit G ∧ G.Connected ∧
        SurvivesCuts G ((n+4)/5) ∧
        2 * orderAmplitude 78375 (200*(1080/7)^2) (log (24/7)) * n^2 /
          (log n)^(5/2 : ℝ) * exp (-2 * sqrt (log (24/7) * log n)) ≤ gapWithFracFour G := by
  have hH (j : ℕ) (hj : 1 ≤ j) : 1 ≤ linearHostFactor j ∧ (linearHostFactor j : ℝ) ≤ 78375*(j : ℝ)
    := by
    have hjR : (1 : ℝ) ≤ j := by exact_mod_cast hj
    unfold linearHostFactor compactHostFactor
    constructor
    · omega
    · push_cast
      linarith
  obtain ⟨N,hN⟩ := universal_R434_with linearHostFactor 78375 (by norm_num) hH gapWithFracFour
    (fun n _ _ => (n+4)/5)
    (fun he he₁ hm _ hn h => finite_gap_of_product_linear_mixed he he₁ hm hn h)
  refine ⟨N, fun n hn => ?_⟩
  obtain ⟨V,fV,dV,G,hcard,hs,hconn,⟨m,j,hc,hb⟩,hg⟩ := hN n hn
  exact ⟨V,fV,dV,G,hcard,hs,hconn,hc,hg⟩

theorem universal_R434_linear :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      ∃ (V : Type) (_ : Fintype V) (_ : DecidableEq V) (G : SimpleGraph V),
        Fintype.card V = n ∧ IsSplit G ∧ G.Connected ∧
        SurvivesCuts G ((n+4)/5) ∧
        2 * orderAmplitude 78375 (200*(1080/7)^2) (log (24/7)) * n^2 /
          (log n)^(5/2 : ℝ) * exp (-2 * sqrt (log (24/7) * log n)) ≤ gap G := by
  obtain ⟨N,hN⟩ := universal_R434_linear_mixed
  refine ⟨N, fun n hn => ?_⟩
  obtain ⟨V,fV,dV,G,hcard,hs,hconn,hcuts,hgap⟩ := hN n hn
  exact ⟨V,fV,dV,G,hcard,hs,hconn,hcuts,hgap.trans (gapWithFracFour_le_gap G)⟩

theorem universal_R434_grouped :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      ∃ (V : Type) (_ : Fintype V) (_ : DecidableEq V) (G : SimpleGraph V),
        Fintype.card V = n ∧ IsSplit G ∧ G.Connected ∧
        2 * orderAmplitude 369 (200*(1080/7)^2) (log (24/7)) * n^2 /
          (log n)^(5/2 : ℝ) * exp (-2 * sqrt (log (24/7) * log n)) ≤ gap G := by
  have hH (j : ℕ) (hj : 1 ≤ j) : 1 ≤ groupedHostFactor j ∧ (groupedHostFactor j : ℝ) ≤ 369 * j := by
    have hjR : (1 : ℝ) ≤ j := by exact_mod_cast hj
    unfold groupedHostFactor
    constructor
    · omega
    · push_cast
      linarith
  obtain ⟨N,hN⟩ := universal_R434_with groupedHostFactor 369 (by norm_num) hH gap
    (fun _ _ _ => 0) (fun he he₁ hm hj hn h => finite_gap_of_product_grouped he he₁ hm hj (by
      omega) h)
  refine ⟨N, fun n hn => ?_⟩
  obtain ⟨V,fV,dV,G,hcard,hs,hconn,_,hg⟩ := hN n hn
  exact ⟨V,fV,dV,G,hcard,hs,hconn,hg⟩

theorem universal_R434_polylog :
    ∃ k : ℝ, 0 < k ∧ ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      ∃ (V : Type) (_ : Fintype V) (_ : DecidableEq V) (G : SimpleGraph V),
        Fintype.card V = n ∧ IsSplit G ∧ G.Connected ∧
        k * n^2 / (log n)^(5/2 : ℝ) * exp (-2 * sqrt (log (24/7) * log n)) ≤ gap G := by
  obtain ⟨N,hN⟩ := universal_R434_robust
  refine ⟨gapConstant, by unfold gapConstant orderAmplitude; positivity, N, fun n hn => ?_⟩
  obtain ⟨V,fV,dV,G,hcard,hs,hconn,_,hg⟩ := hN n hn
  exact ⟨V,fV,dV,G,hcard,hs,hconn,hg⟩

end GapExtremal.R434
