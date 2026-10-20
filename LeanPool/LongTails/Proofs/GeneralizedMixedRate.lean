/-
Copyright (c) 2026 LongTails contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Tyurin, QuocViet Pham, Valentin Khrulkov, Ivan Oseledets
-/
module

public import Mathlib.Analysis.Convex.SpecificFunctions.Basic
public import Mathlib.Data.Finset.Max
public import LeanPool.LongTails.Proofs.DampedGeneralizedDynamics
public import LeanPool.LongTails.Proofs.GeneralizedCharging

/-!
Adapted from k3nfalt/longtails, commit 269cbc764dd36851fd0b64f2f950f329ee127de4.
Modified for Lean Pool: module visibility, namespace isolation, and current Mathlib.
-/

@[expose] public section

open Finset

namespace LongTails.OracleTemplate.GeneralizedAccelerated

open LongTails.Setups.GeneralizedSmoothAndConvex

lemma weighted_holder_cube {ι : Type*} (s : Finset ι) (x y z : ι → ℝ)
    (hx : ∀ i ∈ s, 0 ≤ x i) (hy : ∀ i ∈ s, 0 < y i)
    (hz : ∀ i ∈ s, 0 ≤ z i) (hxyz : ∀ i ∈ s, z i ^ 3 ≤ x i * y i ^ 2) :
    (∑ i ∈ s, z i) ^ 3 ≤ (∑ i ∈ s, x i) * (∑ i ∈ s, y i) ^ 2 := by
  let v := fun i => z i ^ 2 / y i
  have hv : ∀ i ∈ s, 0 ≤ v i := fun i hi => div_nonneg (sq_nonneg _) (hy i hi).le
  have hfirst : (∑ i ∈ s, z i) ^ 2 ≤ (∑ i ∈ s, v i) * (∑ i ∈ s, y i) := by
    apply sum_sq_le_sum_mul_sum_of_sq_le_mul s hv (fun i hi => (hy i hi).le)
    intro i hi
    simp [v, (hy i hi).ne']
  have hsecond : (∑ i ∈ s, v i) ^ 2 ≤ (∑ i ∈ s, x i) * (∑ i ∈ s, z i) := by
    apply sum_sq_le_sum_mul_sum_of_sq_le_mul s hx hz
    intro i hi
    dsimp [v]
    rw [div_pow]
    apply (div_le_iff₀ (sq_pos_of_pos (hy i hi))).mpr
    have h := mul_le_mul_of_nonneg_right (hxyz i hi) (hz i hi)
    nlinarith only [h]
  have hsum : 0 ≤ ∑ i ∈ s, z i := sum_nonneg hz
  have hsquare := mul_self_le_mul_self (sq_nonneg (∑ i ∈ s, z i)) hfirst
  have hmul := mul_le_mul_of_nonneg_right hsecond (sq_nonneg (∑ i ∈ s, y i))
  by_cases hzero : ∑ i ∈ s, z i = 0
  · rw [hzero]
    simpa only [zero_pow (by decide : 3 ≠ 0)] using
      mul_nonneg (sum_nonneg hx) (sq_nonneg (∑ i ∈ s, y i))
  · have hpos : 0 < ∑ i ∈ s, z i := lt_of_le_of_ne hsum (Ne.symm hzero)
    apply (mul_le_mul_iff_left₀ hpos).mp
    nlinarith only [hsquare, hmul]

lemma weighted_exp_cube (A : ℝ) (hA : 0 ≤ A) (q : ℕ) :
    (A ^ (1 / 3 : ℝ) * Real.exp ((2 * Real.log 2 / 3) * q)) ^ 3 =
      A * ((2 : ℝ) ^ q) ^ 2 := by
  have hroot : (A ^ (1 / 3 : ℝ)) ^ 3 = A := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hA]
    norm_num
  have ht : (2 : ℝ) ^ q = Real.exp ((q : ℝ) * Real.log 2) := by
    rw [Real.exp_nat_mul, Real.exp_log (by norm_num : (0 : ℝ) < 2)]
  rw [mul_pow, hroot, ht, ← Real.exp_nat_mul, ← Real.exp_nat_mul]
  congr 2
  ring

lemma weighted_curvature_holder {ι : Type*} (s : Finset ι) (A G : ι → ℝ) (q : ι → ℕ)
    (hA : ∀ i ∈ s, 0 ≤ A i) (hG : ∀ i ∈ s, 0 < G i) :
    (∑ i ∈ s, A i ^ (1 / 3 : ℝ) * Real.exp ((2 * Real.log 2 / 3) * q i)) ^ 3 ≤
      (∑ i ∈ s, A i * G i) * (∑ i ∈ s, (2 : ℝ) ^ q i / Real.sqrt (G i)) ^ 2 := by
  apply weighted_holder_cube s (fun i => A i * G i)
    (fun i => (2 : ℝ) ^ q i / Real.sqrt (G i))
    (fun i => A i ^ (1 / 3 : ℝ) * Real.exp ((2 * Real.log 2 / 3) * q i))
    (fun i hi => mul_nonneg (hA i hi) (hG i hi).le)
    (fun i hi => div_pos (by positivity) (Real.sqrt_pos.mpr (hG i hi)))
    (fun i hi => mul_nonneg (Real.rpow_nonneg (hA i hi) _) (Real.exp_pos _).le)
  intro i hi
  rw [weighted_exp_cube _ (hA i hi), div_pow, Real.sq_sqrt (hG i hi).le]
  have he : A i * G i * ((2 ^ q i) ^ 2 / G i) = A i * (2 ^ q i) ^ 2 := by
    field_simp [(hG i hi).ne']
  rw [he]

lemma weighted_curvature_growth {ι : Type*} (s : Finset ι) (A G : ι → ℝ) (q : ι → ℕ)
    {H C β Afinal : ℝ} (hA : ∀ i ∈ s, 0 ≤ A i) (hG : ∀ i ∈ s, 0 < G i)
    (hH : 0 ≤ H) (hβ : 0 ≤ β) (hAf : 0 ≤ Afinal)
    (henergy : (∑ i ∈ s, A i * G i) ≤ H)
    (hweights : (∑ i ∈ s, (2 : ℝ) ^ q i / Real.sqrt (G i)) ≤ C * Real.sqrt Afinal)
    (htuning : β ^ 3 * H * C ^ 2 ≤ 1) :
    β * (∑ i ∈ s, A i ^ (1 / 3 : ℝ) * Real.exp ((2 * Real.log 2 / 3) * q i)) ≤
      Afinal ^ (1 / 3 : ℝ) := by
  have hw : 0 ≤ ∑ i ∈ s, (2 : ℝ) ^ q i / Real.sqrt (G i) := by
    apply sum_nonneg
    intro i hi
    positivity
  have hz : 0 ≤ ∑ i ∈ s, A i ^ (1 / 3 : ℝ) * Real.exp ((2 * Real.log 2 / 3) * q i) := by
    apply sum_nonneg
    intro i hi
    exact mul_nonneg (Real.rpow_nonneg (hA i hi) _) (Real.exp_pos _).le
  have hw2 := pow_le_pow_left₀ hw hweights 2
  have hb := mul_le_mul henergy hw2 (sq_nonneg _) hH
  rw [mul_pow, Real.sq_sqrt hAf] at hb
  have hh := (weighted_curvature_holder s A G q hA hG).trans hb
  have hh' := mul_le_mul_of_nonneg_left hh (pow_nonneg hβ 3)
  have ht := mul_le_mul_of_nonneg_right htuning hAf
  have hroot : (Afinal ^ (1 / 3 : ℝ)) ^ 3 = Afinal := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hAf]
    norm_num
  apply (pow_le_pow_iff_left₀ (mul_nonneg hβ hz) (Real.rpow_nonneg hAf _) (by decide : 3 ≠ 0)).mp
  nlinarith only [hh', ht, hroot]

lemma exp_growth_log_bound {B0 β c S Bfinal : ℝ}
    (hB0 : 0 < B0) (hβ : 0 < β) (hc : 0 < c) (hBf : 0 < Bfinal)
    (h : B0 / 2 * Real.exp (β * c / 2 * S) ≤ Bfinal) :
    S ≤ 2 * Real.log (2 * Bfinal / B0) / (β * c) := by
  have he : Real.exp (β * c / 2 * S) ≤ 2 * Bfinal / B0 := by
    apply (le_div_iff₀ hB0).mpr
    nlinarith only [h]
  have hl := (Real.le_log_iff_exp_le (show 0 < 2 * Bfinal / B0 by positivity)).mpr he
  apply (le_div_iff₀ (mul_pos hβ hc)).mpr
  nlinarith only [hl]

lemma exp_scaled_le {θ : ℝ} (hθ : 0 ≤ θ) (hθ1 : θ ≤ 1) (x : ℝ) :
    Real.exp (θ * x) ≤ 1 + θ * Real.exp x := by
  have h := convexOn_exp.2 (Set.mem_univ (0 : ℝ)) (Set.mem_univ x)
    (show 0 ≤ 1 - θ by linarith) hθ (show 1 - θ + θ = 1 by ring)
  simp only [smul_eq_mul, mul_zero, zero_add, Real.exp_zero, mul_one] at h
  linarith

lemma finite_prefix_exponential_growth {ι : Type*}
    (s : Finset ι) (time : ι → ℕ) (B r : ι → ℝ) {B0 β c Bfinal : ℝ}
    (hB0 : 0 < B0) (hβ : 0 < β) (hβ1 : β ≤ 1)
    (hinj : Set.InjOn time (s : Set ι))
    (hbase : ∀ i ∈ s, B0 ≤ B i)
    (hprefix : ∀ i ∈ s,
      β * (∑ j ∈ s.filter (fun j => time j < time i), B j * Real.exp (c * r j)) ≤ B i)
    (hfinalbase : B0 ≤ Bfinal)
    (hfinal : β * (∑ i ∈ s, B i * Real.exp (c * r i)) ≤ Bfinal) :
    B0 / 2 * Real.exp (β * c / 2 * ∑ i ∈ s, r i) ≤ Bfinal := by
  classical
  have hgrowth : ∀ t : Finset ι, t ⊆ s →
      B0 / β * Real.exp (β * c / 2 * ∑ i ∈ t, r i) ≤
        B0 / β + ∑ i ∈ t, B i * Real.exp (c * r i) := by
    intro t
    induction t using Finset.induction_on_max_value time with
    | empty => intro _; simp
    | insert a t ha hmax ih =>
      intro hsub
      have haS : a ∈ s := hsub (mem_insert_self _ _)
      have htS : t ⊆ s := fun i hi => hsub (mem_insert_of_mem hi)
      have hlt : ∀ i ∈ t, time i < time a := by
        intro i hi
        apply lt_of_le_of_ne (hmax i hi)
        intro he
        have heq := hinj (htS hi) haS he
        exact ha (heq ▸ hi)
      have hsubset : t ⊆ s.filter (fun i => time i < time a) :=
        fun i hi => mem_filter.mpr ⟨htS hi, hlt i hi⟩
      have hsum := sum_le_sum_of_subset_of_nonneg (f := fun i => B i * Real.exp (c * r i)) hsubset
        (fun i hi _ => mul_nonneg (hB0.le.trans (hbase i (mem_filter.mp hi).1))
          (Real.exp_pos _).le)
      have hp := mul_le_mul_of_nonneg_left hsum hβ.le
      have hsmall : β * (∑ i ∈ t, B i * Real.exp (c * r i)) ≤ B a :=
        hp.trans (hprefix a haS)
      let Q := B0 / β + ∑ i ∈ t, B i * Real.exp (c * r i)
      have hQ : β * Q ≤ 2 * B a := by
        have he : β * Q = B0 + β * (∑ i ∈ t, B i * Real.exp (c * r i)) := by
          dsimp [Q]
          field_simp
        rw [he]
        linarith [hbase a haS]
      have hQnonneg : 0 ≤ Q := by
        apply add_nonneg (div_pos hB0 hβ).le
        exact sum_nonneg (fun i hi => mul_nonneg (hB0.le.trans (hbase i (htS hi)))
          (Real.exp_pos _).le)
      have hexp := exp_scaled_le (θ := β / 2) (by positivity) (by linarith) (c * r a)
      have he : β / 2 * (c * r a) = β * c / 2 * r a := by ring
      rw [he] at hexp
      have hm := mul_le_mul_of_nonneg_left hexp hQnonneg
      have hbound := mul_le_mul_of_nonneg_right hQ (Real.exp_pos (c * r a)).le
      have hrec : Q * Real.exp (β * c / 2 * r a) ≤ Q + B a * Real.exp (c * r a) := by
        nlinarith only [hm, hbound]
      have hi := mul_le_mul_of_nonneg_right (ih htS) (Real.exp_pos (β * c / 2 * r a)).le
      rw [sum_insert ha, sum_insert ha, mul_add, Real.exp_add]
      dsimp [Q] at hrec
      nlinarith only [hi, hrec]
  have hg := mul_le_mul_of_nonneg_left (hgrowth s (Subset.refl _)) hβ.le
  have he (X : ℝ) : β * (B0 / β * X) = B0 * X := by field_simp
  have he' (X : ℝ) : β * (B0 / β + X) = B0 + β * X := by field_simp
  rw [he, he'] at hg
  linarith

lemma high_count_log_bound {ι : Type*}
    (s : Finset ι) (time : ι → ℕ) (A G : ι → ℝ) (q : ι → ℕ)
    {A0 Afinal H β : ℝ} (hA0 : 0 < A0) (hAF : A0 ≤ Afinal)
    (hA : ∀ i ∈ s, A0 ≤ A i) (hG : ∀ i ∈ s, 0 < G i)
    (hH : 0 ≤ H) (hβ : 0 < β) (hβ1 : β ≤ 1)
    (hinj : Set.InjOn time (s : Set ι))
    (henergy : (∑ i ∈ s, A i * G i) ≤ H)
    (hweights : (∑ i ∈ s, (2 : ℝ) ^ q i / Real.sqrt (G i)) ≤ 32 * Real.sqrt Afinal)
    (hprefix : ∀ i ∈ s,
      (∑ j ∈ s.filter (fun j => time j < time i), (2 : ℝ) ^ q j / Real.sqrt (G j)) ≤
        32 * Real.sqrt (A i))
    (htuning : β ^ 3 * H * 32 ^ 2 ≤ 1) :
    (∑ i ∈ s, (q i : ℝ)) ≤
      2 * Real.log (2 * Afinal ^ (1 / 3 : ℝ) / A0 ^ (1 / 3 : ℝ)) /
        (β * (2 * Real.log 2 / 3)) := by
  classical
  have hAnonneg : ∀ i ∈ s, 0 ≤ A i := fun i hi => hA0.le.trans (hA i hi)
  have hAFpos : 0 < Afinal := hA0.trans_le hAF
  have hB0 : 0 < A0 ^ (1 / 3 : ℝ) := Real.rpow_pos_of_pos hA0 _
  have hBf : 0 < Afinal ^ (1 / 3 : ℝ) := Real.rpow_pos_of_pos hAFpos _
  have hc : 0 < 2 * Real.log 2 / 3 := by
    have hh := Real.log_pos (by norm_num : (1 : ℝ) < 2)
    positivity
  have hfinal := weighted_curvature_growth s A G q hAnonneg hG hH hβ.le hAFpos.le
    henergy hweights htuning
  have hprefix' : ∀ i ∈ s,
      β * (∑ j ∈ s.filter (fun j => time j < time i),
        A j ^ (1 / 3 : ℝ) * Real.exp ((2 * Real.log 2 / 3) * q j)) ≤ A i ^ (1 / 3 : ℝ) := by
    intro i hi
    have hsub : s.filter (fun j => time j < time i) ⊆ s := filter_subset _ _
    have hsum := sum_le_sum_of_subset_of_nonneg (f := fun j => A j * G j) hsub
      (fun j hj _ => mul_nonneg (hAnonneg j hj) (hG j hj).le)
    exact weighted_curvature_growth _ A G q (fun j hj => hAnonneg j (hsub hj))
      (fun j hj => hG j (hsub hj)) hH hβ.le (hAnonneg i hi)
      (hsum.trans henergy) (hprefix i hi) htuning
  have hexp := finite_prefix_exponential_growth s time (fun i => A i ^ (1 / 3 : ℝ))
    (fun i => (q i : ℝ)) hB0 hβ hβ1 hinj
    (fun i hi => Real.rpow_le_rpow hA0.le (hA i hi) (by norm_num)) hprefix'
    (Real.rpow_le_rpow hA0.le hAF (by norm_num)) hfinal
  exact exp_growth_log_bound hB0 hβ hc hBf hexp

lemma low_count_bound {ι : Type*} (s : Finset ι) (G : ι → ℝ) (q : ι → ℕ)
    {K W : ℝ} (hG : ∀ i ∈ s, 0 < G i) (hK : ∀ i ∈ s, G i ≤ K)
    (hweights : (∑ i ∈ s, (2 : ℝ) ^ q i / Real.sqrt (G i)) ≤ W) :
    (∑ i ∈ s, (q i : ℝ)) ≤ Real.sqrt K * W := by
  calc
    _ ≤ ∑ i ∈ s, Real.sqrt K * ((2 : ℝ) ^ q i / Real.sqrt (G i)) := by
      apply sum_le_sum
      intro i hi
      have hq : (q i : ℝ) ≤ (2 : ℝ) ^ q i := by
        exact_mod_cast (Nat.lt_two_pow_self (n := q i)).le
      have hs := Real.sqrt_le_sqrt (hK i hi)
      have hm := mul_le_mul_of_nonneg_right hs
        (show 0 ≤ (2 : ℝ) ^ q i / Real.sqrt (G i) by positivity)
      have he : Real.sqrt (G i) * ((2 : ℝ) ^ q i / Real.sqrt (G i)) = (2 : ℝ) ^ q i := by
        field_simp [(Real.sqrt_pos.mpr (hG i hi)).ne']
      rw [he] at hm
      exact hq.trans hm
    _ = Real.sqrt K * (∑ i ∈ s, (2 : ℝ) ^ q i / Real.sqrt (G i)) := (mul_sum _ _ _).symm
    _ ≤ Real.sqrt K * W := mul_le_mul_of_nonneg_left hweights (Real.sqrt_nonneg K)

lemma low_count_sqrt_bound {ι : Type*} (s : Finset ι) (G : ι → ℝ) (q : ι → ℕ)
    {L0 Afinal : ℝ} (hL0 : 0 ≤ L0) (hG : ∀ i ∈ s, 0 < G i)
    (hK : ∀ i ∈ s, G i ≤ 8 * L0)
    (hweights : (∑ i ∈ s, (2 : ℝ) ^ q i / Real.sqrt (G i)) ≤ 32 * Real.sqrt Afinal) :
    (∑ i ∈ s, (q i : ℝ)) ≤ 96 * Real.sqrt (L0 * Afinal) := by
  have h := low_count_bound s G q hG hK hweights
  have h8 : Real.sqrt (8 : ℝ) ≤ 3 := (Real.sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  have hs := mul_le_mul_of_nonneg_right h8 (Real.sqrt_nonneg L0)
  rw [← Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 8)] at hs
  have hm := mul_le_mul_of_nonneg_right hs (show 0 ≤ 32 * Real.sqrt Afinal by positivity)
  rw [Real.sqrt_mul hL0]
  nlinarith only [h, hm]

lemma mixed_tuning {a : ℝ} (ha : 0 ≤ a) :
    let β := 1 / (64 * (1 + a ^ (2 / 3 : ℝ)))
    0 < β ∧ β ≤ 1 ∧ β ^ 3 * ((512 / 3) * a ^ 2) * 32 ^ 2 ≤ 1 := by
  let t := a ^ (2 / 3 : ℝ)
  have ht : 0 ≤ t := Real.rpow_nonneg ha _
  have ht3 : t ^ 3 = a ^ 2 := by
    dsimp [t]
    rw [← Real.rpow_natCast, ← Real.rpow_mul ha]
    norm_num
  have hd : 0 < 64 * (1 + t) := by positivity
  change 0 < 1 / (64 * (1 + t)) ∧ _ ≤ 1 ∧ _ ≤ 1
  refine ⟨one_div_pos.mpr hd, (div_le_one hd).mpr (by linarith), ?_⟩
  change (1 / (64 * (1 + t))) ^ 3 * ((512 / 3) * a ^ 2) * 32 ^ 2 ≤ 1
  rw [div_pow]
  have hpow : 0 < (64 * (1 + t)) ^ 3 := pow_pos hd 3
  field_simp
  nlinarith [sq_nonneg t, pow_nonneg ht 3]

lemma count_exponent_lower : (1 / 3 : ℝ) ≤ 2 * Real.log 2 / 3 := by
  have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 1 / 2)
  norm_num [Real.log_div] at h
  linarith

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- Whether the current local curvature exceeds the algorithm curvature guess. -/
noncomputable def runUp (L0 L1 : ℝ) (g : E → E) (s : Iterate E) (n : ℕ) : Bool := by
  classical
  exact decide ((run L0 L1 g s n).guess <
    localCurvature L0 L1 (g (coupling (run L0 L1 g s n))))

omit [CompleteSpace E] in
lemma run_charging_bound {g : E → E} {L0 L1 : ℝ}
    (hL0 : 0 < L0) (hL1 : 0 ≤ L1) (s : Iterate E)
    (hA : 0 ≤ s.A) (hG : 0 < s.guess)
    (hfirst : localCurvature L0 L1 (g (coupling s)) ≤ s.guess) (n : ℕ) :
    let w := fun i => 1 / Real.sqrt (run L0 L1 g s i).guess
    let up := runUp L0 L1 g s
    (∑ b ∈ chargingSet up n, chargeValue w b) ≤ 32 * Real.sqrt (run L0 L1 g s (n + 1)).A ∧
    ∀ b ∈ chargingSet up n,
      (∑ a ∈ (chargingSet up n).filter (fun a => a.1 < b.1), chargeValue w a) ≤
        32 * Real.sqrt (run L0 L1 g s (b.1 + 1)).A := by
  let w := fun i => 1 / Real.sqrt (run L0 L1 g s i).guess
  let up := runUp L0 L1 g s
  have hzero : up 0 = false := by simp [up, runUp, run, not_lt_of_ge hfirst]
  have hw : ∀ i, 0 ≤ w i := fun i => one_div_nonneg.mpr (Real.sqrt_nonneg _)
  have hnext : ∀ i, w (i + 1) = if up i then w i / 4 else 4 * w i := by
    intro i
    have hv := run_valid (g := g) hL0 hL1 s hA hG i
    have hs := step_inverse_sqrt_guess (g := g) (L0 := L0) (L1 := L1)
      (run L0 L1 g s i) hv.2
    dsimp [w, up, runUp]
    simp only [decide_eq_true_eq, ← not_le, ite_not]
    exact hs
  have hmass (i : ℕ) : downMass up w i ≤ 2 * Real.sqrt (run L0 L1 g s (i + 1)).A := by
    have hs := down_sum_le_sqrt (g := g) hL0 hL1 s hA hG (i + 1)
    simpa only [downMass, up, runUp, w, decide_eq_true_eq, ← not_le, ite_not] using hs
  have htotal (i : ℕ) : chargeTotal w (charging up i) ≤
      32 * Real.sqrt (run L0 L1 g s (i + 1)).A := by
    have hs := charging_total_le hzero hw hnext i
    linarith [hmass i]
  have hmono : Monotone (fun i => 32 * Real.sqrt (run L0 L1 g s (i + 1)).A) := by
    intro i j hij
    have h := Real.sqrt_le_sqrt
      (run_weight_mono (g := g) hL0 hL1 s hA hG (Nat.add_le_add_right hij 1))
    linarith
  have hprefix := charging_prefix_bound
    (show 0 ≤ 32 * Real.sqrt (run L0 L1 g s (0 + 1)).A by positivity)
    hmono htotal n
  dsimp only
  constructor
  · rw [charging_sum]
    exact htotal n
  · intro b hb
    rw [charging_sum_prefix]
    exact hprefix b (List.mem_toFinset.mp hb)

omit [CompleteSpace E] in
lemma charging_selected_curvature {g : E → E} {L0 L1 : ℝ} (s : Iterate E)
    (hfirst : localCurvature L0 L1 (g (coupling s)) = s.guess)
    (n : ℕ) (b : ℕ × ℕ) (hb : b ∈ chargingSet (runUp L0 L1 g s) n) :
    (run L0 L1 g s b.1).guess ≤ localCurvature L0 L1 (g (coupling (run L0 L1 g s b.1))) := by
  have h := (charging_indices (runUp L0 L1 g s) n).2.2.2 b (List.mem_toFinset.mp hb)
  rcases h with h | h
  · rw [h]
    simpa only [run] using hfirst.ge
  · have ht : (run L0 L1 g s b.1).guess <
        localCurvature L0 L1 (g (coupling (run L0 L1 g s b.1))) := of_decide_eq_true h
    exact ht.le

lemma charged_high_energy {f : E → ℝ} {g : E → E} {L0 L1 : ℝ}
    (hL0 : 0 < L0) (hL1 : 0 < L1)
    (hc : ConvexOn ℝ Set.univ f) (hg : ∀ x, HasGradientAt f (g x) x)
    (hgd : Differentiable ℝ g)
    (hH : ∀ x, ‖fderiv ℝ g x‖ ≤ L0 + L1 * ‖g x‖)
    (s : Iterate E) (u : E) (hmin : IsMinOn f Set.univ u)
    (hA : 0 ≤ s.A) (hG : 0 < s.guess)
    (hfirst : localCurvature L0 L1 (g (coupling s)) = s.guess)
    (n : ℕ) (Q : Finset (ℕ × ℕ)) (hQ : Q ⊆ chargingSet (runUp L0 L1 g s) n)
    (hhigh : ∀ b ∈ Q, 8 * L0 < localCurvature L0 L1 (g (coupling (run L0 L1 g s b.1)))) :
    (∑ b ∈ Q, (run L0 L1 g s (b.1 + 1)).A * (run L0 L1 g s b.1).guess) ≤
      (512 / 3) * L1 ^ 2 * energy f u s := by
  have hindex : Q.image Prod.fst ⊆ range (n + 1) := by
    intro i hi
    obtain ⟨b, hb, rfl⟩ := mem_image.mp hi
    exact mem_range.mpr (Nat.lt_succ_of_le
      (charging_index_le _ n b (List.mem_toFinset.mp (hQ hb))))
  have hup : ∀ i ∈ Q.image Prod.fst, (run L0 L1 g s i).guess ≤
      localCurvature L0 L1 (g (coupling (run L0 L1 g s i))) := by
    intro i hi
    obtain ⟨b, hb, rfl⟩ := mem_image.mp hi
    exact charging_selected_curvature s hfirst n b (hQ hb)
  have hhigh' : ∀ i ∈ Q.image Prod.fst,
      8 * L0 < localCurvature L0 L1 (g (coupling (run L0 L1 g s i))) := by
    intro i hi
    obtain ⟨b, hb, rfl⟩ := mem_image.mp hi
    exact hhigh b hb
  have he := run_high_sum_le hL0 hL1 hc hg hgd hH s u hmin hA hG (n + 1)
    (Q.image Prod.fst) hindex hup hhigh'
  have hinj : ∀ a ∈ Q, ∀ b ∈ Q, a.1 = b.1 → a = b := by
    intro a ha b hb hab
    exact charging_unique_index _ n (List.mem_toFinset.mp (hQ ha))
      (List.mem_toFinset.mp (hQ hb)) hab
  rw [sum_image hinj] at he
  exact he

/-- Shared low/high-curvature charging facts for both accelerated iteration-count bounds. -/
lemma run_charging_geometry {f : E → ℝ} {g : E → E} {L0 L1 R : ℝ}
    (hL0 : 0 < L0) (hL1 : 0 < L1)
    (hc : ConvexOn ℝ Set.univ f) (hg : ∀ x, HasGradientAt f (g x) x)
    (hgd : Differentiable ℝ g)
    (hH : ∀ x, ‖fderiv ℝ g x‖ ≤ L0 + L1 * ‖g x‖)
    (s : Iterate E) (u : E) (hmin : IsMinOn f Set.univ u)
    (hA : 0 < s.A) (hG : 0 < s.guess) (hE : energy f u s ≤ R ^ 2)
    (hfirst : localCurvature L0 L1 (g (coupling s)) = s.guess) (n : ℕ) :
    let Q := chargingSet (runUp L0 L1 g s) n
    let A := fun b : ℕ × ℕ => (run L0 L1 g s (b.1 + 1)).A
    let G := fun b : ℕ × ℕ => (run L0 L1 g s b.1).guess
    let M := fun b : ℕ × ℕ => localCurvature L0 L1 (g (coupling (run L0 L1 g s b.1)))
    let low := Q.filter (fun b => M b ≤ 8 * L0)
    let high := Q.filter (fun b => ¬M b ≤ 8 * L0)
    let Afinal := (run L0 L1 g s (n + 1)).A
    (∀ i, s.A ≤ (run L0 L1 g s i).A) ∧
    (∀ i, 0 < (run L0 L1 g s i).guess) ∧
    (∑ b ∈ low, (b.2 : ℝ)) ≤ 96 * Real.sqrt (L0 * Afinal) ∧
    (∑ b ∈ high, A b * G b) ≤ (512 / 3) * (L1 * R) ^ 2 ∧
    (∑ b ∈ high, (2 : ℝ) ^ b.2 / Real.sqrt (G b)) ≤ 32 * Real.sqrt Afinal ∧
    (∀ b ∈ high,
      (∑ a ∈ high.filter (fun a => a.1 < b.1), (2 : ℝ) ^ a.2 / Real.sqrt (G a)) ≤
        32 * Real.sqrt (A b)) ∧
    Set.InjOn Prod.fst (high : Set (ℕ × ℕ)) ∧
    (∑ b ∈ low, (b.2 : ℝ)) + (∑ b ∈ high, (b.2 : ℝ)) = n := by
  classical
  let Q := chargingSet (runUp L0 L1 g s) n
  let A := fun b : ℕ × ℕ => (run L0 L1 g s (b.1 + 1)).A
  let G := fun b : ℕ × ℕ => (run L0 L1 g s b.1).guess
  let M := fun b : ℕ × ℕ => localCurvature L0 L1 (g (coupling (run L0 L1 g s b.1)))
  let low := Q.filter (fun b => M b ≤ 8 * L0)
  let high := Q.filter (fun b => ¬M b ≤ 8 * L0)
  let Afinal := (run L0 L1 g s (n + 1)).A
  have hv (i : ℕ) := run_valid (g := g) hL0 hL1.le s hA.le hG i
  have hbase (i : ℕ) : s.A ≤ (run L0 L1 g s i).A :=
    run_weight_mono (g := g) hL0 hL1.le s hA.le hG (Nat.zero_le i)
  have hcharge := run_charging_bound (g := g) hL0 hL1.le s hA.le hG hfirst.le n
  have hweights : (∑ b ∈ Q, (2 : ℝ) ^ b.2 / Real.sqrt (G b)) ≤ 32 * Real.sqrt Afinal := by
    simpa only [chargeValue, mul_one_div] using hcharge.1
  have hsubset (T : Finset (ℕ × ℕ)) (hT : T ⊆ Q) :
      (∑ b ∈ T, (2 : ℝ) ^ b.2 / Real.sqrt (G b)) ≤ 32 * Real.sqrt Afinal := by
    apply le_trans (sum_le_sum_of_subset_of_nonneg hT ?_) hweights
    intro b _ _
    positivity
  have hlow := low_count_sqrt_bound low G Prod.snd hL0.le
    (fun b _ => (hv b.1).2)
    (fun b hb => (charging_selected_curvature s hfirst n b (mem_filter.mp hb).1).trans
      (mem_filter.mp hb).2)
    (hsubset low (filter_subset _ _))
  have henergy : (∑ b ∈ high, A b * G b) ≤ (512 / 3) * (L1 * R) ^ 2 := by
    have he := charged_high_energy hL0 hL1 hc hg hgd hH s u hmin hA.le hG hfirst n high
      (filter_subset _ _) (fun b hb => lt_of_not_ge (mem_filter.mp hb).2)
    have hm := mul_le_mul_of_nonneg_left hE (show 0 ≤ (512 / 3) * L1 ^ 2 by positivity)
    change (∑ b ∈ high, A b * G b) ≤ _ at he
    nlinarith only [he, hm]
  have hprefix : ∀ b ∈ high,
      (∑ a ∈ high.filter (fun a => a.1 < b.1), (2 : ℝ) ^ a.2 / Real.sqrt (G a)) ≤
        32 * Real.sqrt (A b) := by
    intro b hb
    have hsub : high.filter (fun a => a.1 < b.1) ⊆ Q.filter (fun a => a.1 < b.1) := by
      intro a ha
      exact mem_filter.mpr ⟨(mem_filter.mp (mem_filter.mp ha).1).1, (mem_filter.mp ha).2⟩
    have hs := sum_le_sum_of_subset_of_nonneg
      (f := fun a => (2 : ℝ) ^ a.2 / Real.sqrt (G a)) hsub (fun a _ _ => by positivity)
    have hp := hcharge.2 b (mem_filter.mp hb).1
    simp only [chargeValue, mul_one_div] at hp
    exact hs.trans hp
  have hinj : Set.InjOn Prod.fst (high : Set (ℕ × ℕ)) := by
    intro a ha b hb hab
    exact charging_unique_index _ n (List.mem_toFinset.mp (mem_filter.mp ha).1)
      (List.mem_toFinset.mp (mem_filter.mp hb).1) hab
  have hcount : (∑ b ∈ Q, (b.2 : ℝ)) = n := by
    exact_mod_cast charging_sum_count (runUp L0 L1 g s) n
  have hsplit : (∑ b ∈ low, (b.2 : ℝ)) + (∑ b ∈ high, (b.2 : ℝ)) = n := by
    rw [← hcount]
    exact sum_filter_add_sum_filter_not Q _ _
  exact ⟨hbase, fun i => (hv i).2, hlow, henergy,
    hsubset high (filter_subset _ _), hprefix, hinj, hsplit⟩

end LongTails.OracleTemplate.GeneralizedAccelerated
