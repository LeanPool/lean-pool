/-
Copyright (c) 2026 Bjørn Kjos-Hanssen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bjørn Kjos-Hanssen
-/

-- Modified for Lean Pool.

module

public import LeanPool.KLRandomness.PoolSelection
public import LeanPool.KLRandomness.PoolQueryLimit
public import LeanPool.KLRandomness.PoolWeighted
public import LeanPool.KLRandomness.PoolSoundness

/-!
# Actual finite witnesses for the pool search

The weak-limit selection is applied to the actual query indicators. It gives
arbitrarily large finite pools with small missed mass on the fixed high sets,
small L1 distance to the fixed limits, and the required weighted coverage.
Finite-horizon convergence then supplies an actual pair accepted by the
executable checker. No convergence modulus is supplied to that checker.
-/

@[expose] public section

namespace Klr.Pool

open Filter MeasureTheory
open scoped Topology BigOperators symmDiff

theorem advice_weight_cast (i : ℕ) : (PoolAdvice.weight i : ℝ) = weight i := by
  simp [PoolAdvice.weight, weight]

/-- Weighted eventual coverage using a finite prefix of the scans. -/
noncomputable def finitePoolMass (π : ℕ → ScanRule) (k : ℕ) (G : Finset ℕ) : ℝ :=
  ∑ i ∈ Finset.range k, weight i * ∫ Z, PoolQuery.readFraction (π i) G Z ∂fairCoin

theorem integral_readFraction (π : ScanRule) (G : Finset ℕ) :
    (∫ Z, PoolQuery.readFraction π G Z ∂fairCoin) =
      (∑ a ∈ G, queryProbability π a) / G.card := by
  unfold PoolQuery.readFraction queryProbability
  rw [integral_div, integral_finsetSum _ (fun a _ => PoolQuery.integrable_indicator π a)]

/-- Average weighted coverage is the average of the positions' weighted
query probabilities. -/
theorem finitePoolMass_eq_average (π : ℕ → ScanRule) (k : ℕ) (G : Finset ℕ) :
    finitePoolMass π k G =
      (∑ a ∈ G, ∑ i ∈ Finset.range k, weight i * queryProbability (π i) a) / G.card := by
  unfold finitePoolMass
  simp_rw [integral_readFraction, ← mul_div_assoc, Finset.mul_sum]
  rw [← Finset.sum_div, Finset.sum_comm]

/-- Reindexing a distinct selection of indices gives the actual centered pool
average, with no multiplicities hidden in the finite set. -/
theorem averageL2_image_sub (π : ScanRule) (a : ℕ → ℕ) (F : Finset ℕ)
    (hinj : Set.InjOn a F) (hF : F.Nonempty) (g : Lp ℝ 2 fairCoin) :
    averageL2 π (F.image a) - g =
      (F.card : ℝ)⁻¹ • ∑ n ∈ F, (queryL2 π (a n) - g) := by
  classical
  have hc : (F.card : ℝ) ≠ 0 := by exact_mod_cast hF.card_ne_zero
  rw [averageL2, Finset.card_image_of_injOn hinj,
    Finset.sum_image (fun n hn m hm h => hinj hn hm h), Finset.sum_sub_distrib,
    Finset.sum_const, ← Nat.cast_smul_eq_nsmul ℝ, smul_sub, smul_smul,
    inv_mul_cancel₀ hc, one_smul]

namespace QueryPartition

variable {π : ℕ → ScanRule} {a : ℕ → ℕ} (D : QueryPartition π a)

/-- Actual finite pools satisfying the limiting tests exist at every
sufficiently large size. The weighted lower bound is an eventual property of
the chosen query positions; `PoolWeighted` obtains it from the limsup. -/
theorem eventually_exists_final_pool (ha : Tendsto D.position atTop atTop)
    (ℓ k z : ℕ) {δ γ : ℝ} (hδ : 0 < δ)
    (hweighted : ∀ᶠ n : ℕ in atTop,
      γ < ∑ i ∈ Finset.range k, weight i * queryProbability (π i) (D.position n)) :
    ∀ᶠ M : ℕ in atTop, ∃ G : Finset ℕ,
      G.card = M ∧ (∀ b ∈ G, z ≤ b) ∧
      (∀ i < ℓ, fairCoin.real {Z | Z ∈ D.high i ∧ PoolQuery.readFraction (π i) G Z < 1} < δ) ∧
      (∀ i < ℓ, (∫ Z, |PoolQuery.readFraction (π i) G Z - D.representative i Z| ∂fairCoin) < δ) ∧
      γ < finitePoolMass π k G := by
  classical
  have hselect := eventually_exists_finite_weak_average
    (fun i n => queryL2 (π i) (D.position n)) D.limit D.weak
    (fun i n => norm_queryL2_le_one (π i) (D.position n))
    (fun i => norm_le_one_of_ae_unitInterval (D.limit_nonneg i) (D.limit_le_one i))
    D.position ha ℓ hδ
  filter_upwards [eventually_ge_atTop 1, hselect] with M hM hselect
  have hMr : (0 : ℝ) < M := by exact_mod_cast (show 0 < M by omega)
  let P : ℕ → Prop := fun n => z ≤ D.position n ∧
    (∀ i < ℓ, fairCoin.real (D.high i \ {Z | PoolQuery.Reads (π i) (D.position n) Z}) <
      δ / M) ∧ γ < ∑ i ∈ Finset.range k, weight i * queryProbability (π i) (D.position n)
  have hP : ∀ᶠ n : ℕ in atTop, P n := by
    have hhigh : ∀ᶠ n : ℕ in atTop, ∀ i : Fin ℓ,
        fairCoin.real (D.high i \ {Z | PoolQuery.Reads (π i) (D.position n) Z}) < δ / M :=
      Filter.eventually_all.mpr fun i => (D.high_miss_tendsto_zero i).eventually
        (gt_mem_nhds (div_pos hδ hMr))
    filter_upwards [ha.eventually (eventually_ge_atTop z), hhigh, hweighted] with n hz hh hw
    exact ⟨hz, fun i hi => hh ⟨i, hi⟩, hw⟩
  obtain ⟨F, hcard, hPF, hinj, hnorm⟩ := hselect P hP
  let G := F.image D.position
  have hGcard : G.card = M := (Finset.card_image_of_injOn hinj).trans hcard
  have hG : G.Nonempty := Finset.card_pos.mp (by omega)
  have hF : F.Nonempty := Finset.card_pos.mp (by omega)
  have hside : ∀ b ∈ G, z ≤ b ∧
      (∀ i < ℓ, fairCoin.real (D.high i \ {Z | PoolQuery.Reads (π i) b Z}) < δ / M) ∧
      γ < ∑ i ∈ Finset.range k, weight i * queryProbability (π i) b := by
    intro b hb
    obtain ⟨n, hn, rfl⟩ := Finset.mem_image.mp hb
    exact hPF n hn
  refine ⟨G, hGcard, fun b hb => (hside b hb).1, ?_, ?_, ?_⟩
  · intro i hi
    calc
      _ ≤ ∑ b ∈ G, fairCoin.real (D.high i \ {Z | PoolQuery.Reads (π i) b Z}) :=
        PoolQuery.high_miss_le_sum (π i) hG (D.high i)
      _ < ∑ _b ∈ G, δ / (M : ℝ) :=
        Finset.sum_lt_sum_of_nonempty hG (fun b hb => (hside b hb).2.1 i hi)
      _ = δ := by simp [hGcard, nsmul_eq_mul, mul_div_cancel₀ δ hMr.ne']
  · intro i hi
    apply (D.integral_abs_readFraction_sub_representative_le i G).trans_lt
    rw [show G = F.image D.position from rfl, averageL2_image_sub _ _ _ hinj hF]
    exact hnorm i hi
  · rw [finitePoolMass_eq_average]
    apply (lt_div_iff₀ (by exact_mod_cast hG.card_pos)).mpr
    calc
      γ * (G.card : ℝ) = ∑ _b ∈ G, γ := by simp [mul_comm]
      _ < _ := Finset.sum_lt_sum_of_nonempty hG (fun b hb => (hside b hb).2.2)

end QueryPartition

end Klr.Pool
