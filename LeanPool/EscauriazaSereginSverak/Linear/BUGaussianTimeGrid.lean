/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.CaffarelliKohnNirenberg.Foundation.CollarCover

/-!
# Finite time cells for the Gaussian collar

The Caccioppoli cylinders use open time intervals. Half-step starts ensure
that these intervals cover the collar while keeping a uniform overlap bound.
-/

public section

open CKN


open Set Classical

noncomputable section

namespace ESS

/-- The finite number of time cells needed to cover `(σ,T)`. -/
@[expose] def buGaussianTimeGridCount (σ T δ : ℝ) : ℕ :=
  Nat.ceil (2 * (T - σ) / δ) + 1

/-- The start of a half-step time cell. -/
@[expose] def buGaussianTimeGridStart (σ δ : ℝ) (j : ℕ) : ℝ :=
  σ + (j : ℝ) * δ / 2

/-- The inner time interval in a half-step grid. -/
@[expose] def buGaussianTimeGridInner (σ δ : ℝ) (j : ℕ) : Set ℝ :=
  Ioo (buGaussianTimeGridStart σ δ j)
    (buGaussianTimeGridStart σ δ j + δ)

/-- The outer time interval needed by `ESS.caccioppoli`. -/
@[expose] def buGaussianTimeGridOuter (σ δ : ℝ) (j : ℕ) : Set ℝ :=
  Ioo (buGaussianTimeGridStart σ δ j)
    (buGaussianTimeGridStart σ δ j + 4 * δ)

/-- Every point strictly between `σ` and `T` is in one of the inner cells. -/
theorem buGaussian_time_grid_covers {σ T δ : ℝ}
    (hσT : σ < T) (hδ : 0 < δ) (s : ℝ) (hs : s ∈ Ioo σ T) :
    ∃ j ∈ Finset.range (buGaussianTimeGridCount σ T δ),
      s ∈ buGaussianTimeGridInner σ δ j := by
  let q : ℝ := 2 * (s - σ) / δ
  let k : ℕ := ⌊q⌋₊
  let j : ℕ := if q < 1 then 0 else k - 1
  have hqpos : 0 < q := by
    dsimp [q]
    exact div_pos (by linarith only [hs.1]) hδ
  have hqT : q < 2 * (T - σ) / δ := by
    dsimp [q]
    apply (div_lt_div_iff_of_pos_right hδ).2
    nlinarith only [hs.2]
  have hTδ : 0 < 2 * (T - σ) / δ := by positivity
  have hqfloor : (k : ℝ) ≤ q := by
    dsimp [k]
    exact Nat.floor_le (le_of_lt hqpos)
  have hqfloorlt : q < (k : ℝ) + 1 := by
    dsimp [k]
    exact Nat.lt_floor_add_one q
  have hjlo : (j : ℝ) < q := by
    by_cases hq1 : q < 1
    · have hjdef : j = 0 := by simp [j, hq1]
      rw [hjdef]
      exact_mod_cast hqpos
    · have hkpos : 0 < k := by
        dsimp [k]
        exact Nat.floor_pos.2 (le_of_not_gt hq1)
      have hkcast : ((k - 1 : ℕ) : ℝ) = (k : ℝ) - 1 := by
        exact_mod_cast Nat.cast_sub (by omega)
      have hjdef : j = k - 1 := by simp [j, hq1]
      rw [hjdef, hkcast]
      linarith only [hqfloor, hq1]
  have hjhi : q < (j : ℝ) + 2 := by
    by_cases hq1 : q < 1
    · have hjdef : j = 0 := by simp [j, hq1]
      rw [hjdef]
      linarith only [hq1]
    · have hkpos : 0 < k := by
        dsimp [k]
        exact Nat.floor_pos.2 (le_of_not_gt hq1)
      have hkcast : ((k - 1 : ℕ) : ℝ) = (k : ℝ) - 1 := by
        exact_mod_cast Nat.cast_sub (by omega)
      have hjdef : j = k - 1 := by simp [j, hq1]
      rw [hjdef, hkcast]
      linarith only [hqfloorlt]
  have hjbound : j < buGaussianTimeGridCount σ T δ := by
    by_cases hq1 : q < 1
    · have hjdef : j = 0 := by simp [j, hq1]
      rw [hjdef]
      simp [buGaussianTimeGridCount]
    · have hceil : 2 * (T - σ) / δ ≤
          (Nat.ceil (2 * (T - σ) / δ) : ℝ) := Nat.le_ceil _
      have hjk : j ≤ k := by
        have hjdef : j = k - 1 := by simp [j, hq1]
        rw [hjdef]
        omega
      have hjk' : (j : ℝ) ≤ (k : ℝ) := by exact_mod_cast hjk
      have hkc : (k : ℝ) < (Nat.ceil (2 * (T - σ) / δ) : ℝ) :=
        lt_of_le_of_lt hqfloor (lt_of_lt_of_le hqT hceil)
      have hjceil : j < Nat.ceil (2 * (T - σ) / δ) := by
        exact_mod_cast lt_of_le_of_lt hjk' hkc
      change j < Nat.ceil (2 * (T - σ) / δ) + 1
      exact Nat.lt_succ_of_le hjceil.le
  have hsrepr : s = σ + q * δ / 2 := by
    dsimp [q]
    field_simp [ne_of_gt hδ]
    ring
  have hleft : buGaussianTimeGridStart σ δ j < s := by
    rw [hsrepr]
    dsimp [buGaussianTimeGridStart]
    have hmul := mul_lt_mul_of_pos_right hjlo (by positivity : 0 < δ / 2)
    nlinarith only [hmul]
  have hright : s < buGaussianTimeGridStart σ δ j + δ := by
    rw [hsrepr]
    dsimp [buGaussianTimeGridStart]
    have hmul := mul_lt_mul_of_pos_right hjhi (by positivity : 0 < δ / 2)
    nlinarith only [hmul]
  exact ⟨j, Finset.mem_range.mpr hjbound, ⟨hleft, hright⟩⟩

/-- All outer time cells stay in `(σ,2)` when their terminal range has a
small fixed margin before time `2`. -/
theorem buGaussian_time_grid_outer_subset {σ T δ : ℝ}
    (hσT : σ < T) (hδ : 0 < δ) (hmargin : T + 5 * δ ≤ 2)
    (j : ℕ) (hj : j < buGaussianTimeGridCount σ T δ) :
    buGaussianTimeGridOuter σ δ j ⊆ Ioo σ 2 := by
  intro s hs
  have hqpos : 0 < 2 * (T - σ) / δ := by
    exact div_pos (by linarith only [hσT]) hδ
  have hceil : (Nat.ceil (2 * (T - σ) / δ) : ℝ) <
      2 * (T - σ) / δ + 1 := Nat.ceil_lt_add_one hqpos.le
  have hδhalf : 0 < δ / 2 := div_pos hδ (by norm_num)
  have hjbound : (j : ℝ) ≤ Nat.ceil (2 * (T - σ) / δ) := by
    have := hj
    simp only [buGaussianTimeGridCount] at this
    exact_mod_cast (Nat.lt_succ_iff.mp this)
  dsimp [buGaussianTimeGridOuter, buGaussianTimeGridStart] at hs ⊢
  constructor
  · have hjnonneg : 0 ≤ (j : ℝ) * δ / 2 := by positivity
    linarith only [hs.1, hjnonneg]
  · have hupper : s < σ + (j : ℝ) * δ / 2 + 4 * δ := hs.2
    have hmul : (j : ℝ) * δ / 2 ≤
        (Nat.ceil (2 * (T - σ) / δ) : ℝ) * δ / 2 := by
      exact div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_right hjbound hδ.le) (by norm_num)
    have hceilbound : (Nat.ceil (2 * (T - σ) / δ) : ℝ) * δ / 2 <
        T - σ + δ / 2 := by
      calc
        (Nat.ceil (2 * (T - σ) / δ) : ℝ) * δ / 2 =
            (Nat.ceil (2 * (T - σ) / δ) : ℝ) * (δ / 2) := by ring
        _ <
            (2 * (T - σ) / δ + 1) * (δ / 2) :=
          mul_lt_mul_of_pos_right hceil hδhalf
        _ = T - σ + δ / 2 := by
          field_simp [ne_of_gt hδ]
    have hmargin' : σ + (T - σ + δ / 2) + 4 * δ < 2 := by
      have : T + 5 * δ ≤ 2 := hmargin
      nlinarith only [this, hδ]
    linarith only [hupper, hmul, hceilbound, hmargin']

/-- The outer time windows of a half-step grid have multiplicity at most
eight, uniformly in the cell length. -/
theorem buGaussian_time_grid_outer_multiplicity
    {σ δ : ℝ} (hδ : 0 < δ) (J : Finset ℕ) (s : ℝ) :
    (∑ j ∈ J, if s ∈ buGaussianTimeGridOuter σ δ j then 1 else 0) ≤ 8 := by
  classical
  let q : ℝ := 2 * (s - σ) / δ
  let k : ℕ := ⌊q⌋₊
  let F := J.filter fun j => s ∈ buGaussianTimeGridOuter σ δ j
  have hFsub : F ⊆ Finset.Icc (k - 7) k := by
    intro j hj
    have hjF : j ∈ J ∧ s ∈ buGaussianTimeGridOuter σ δ j :=
      Finset.mem_filter.mp hj
    have hs := hjF.2
    change σ + (j : ℝ) * δ / 2 < s ∧
      s < σ + (j : ℝ) * δ / 2 + 4 * δ at hs
    have hqfloor : (k : ℝ) ≤ q := by
      dsimp [k, q]
      have hqpos : 0 < 2 * (s - σ) / δ := by
        apply div_pos _ hδ
        have hjnonneg : 0 ≤ (j : ℝ) * δ / 2 := by positivity
        nlinarith only [hs.1, hjnonneg]
      exact Nat.floor_le (le_of_lt hqpos)
    have hqfloorlt : q < (k : ℝ) + 1 := by
      dsimp [k, q]
      exact Nat.lt_floor_add_one _
    have hjltq : (j : ℝ) < q := by
      dsimp [q]
      apply (lt_div_iff₀ hδ).2
      nlinarith only [hs.1]
    have hqj8 : q < (j : ℝ) + 8 := by
      dsimp [q]
      apply (div_lt_iff₀ hδ).2
      nlinarith only [hs.2]
    have hjle : j ≤ k := by
      have hreal : (j : ℝ) < (k : ℝ) + 1 := lt_trans hjltq hqfloorlt
      have hnat : j < k + 1 := by exact_mod_cast hreal
      omega
    have hkltj8 : (k : ℝ) < (j : ℝ) + 8 := lt_of_le_of_lt hqfloor hqj8
    have hkbound : k ≤ j + 7 := by
      have hnat : k < j + 8 := by exact_mod_cast hkltj8
      omega
    exact Finset.mem_Icc.mpr ⟨by omega, hjle⟩
  have hcardIcc : (Finset.Icc (k - 7) k).card ≤ 8 := by
    simp only [Nat.card_Icc]
    omega
  have hsum : (∑ j ∈ J, if s ∈ buGaussianTimeGridOuter σ δ j then 1 else 0) = F.card := by
    simp [F]
  rw [hsum]
  exact (Finset.card_le_card hFsub).trans hcardIcc

end ESS

end
