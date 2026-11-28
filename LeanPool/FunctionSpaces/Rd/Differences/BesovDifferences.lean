/-
Copyright (c) 2026 Mario Ullrich. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Ullrich
-/
module

public import LeanPool.FunctionSpaces.Rd.Approximation.BandJackson
public import LeanPool.FunctionSpaces.Rd.Approximation.BandInverse
public import LeanPool.FunctionSpaces.Rd.LittlewoodPaley.LittlewoodPaley
public import LeanPool.FunctionSpaces.ApproximationSpaces.Moduli

/-
Modified for Lean Pool: module names and imports adapted.
-/

/-!
# Besov spaces on `V` by differences

For `1 ≤ p < ∞` and `r ≥ 1`, the modulus of smoothness `ω_r(f, t)_p` of `f ∈ L_p(V)` is
compatible with the band-limited scheme with inverse order `r` (`Rd.bandModulusData`):
Jackson's inequality `E(f, E_k)_p ≤ C_J ω_r(f, 2^(-k))_p` (`Rd.approxError_bandScheme_le`) and the
inverse inequality `ω_r(a, 2^(-k))_p ≤ C_B 2^(-(k-j) r) ‖a‖_p` for `a ∈ E_j`
(`Rd.lpModulus_le_of_mem_bandSpace`). Its classical quasi-norm is
`‖f‖_p + ‖(2^(ks) ω_r(f, 2^(-k))_p)_k‖_{ℓ_q}` (`Rd.modNorm_bandModulusData`). The
coincidence theorem for moduli (`ApproximationScheme.ModulusData.memApprox_iff_modNorm_lt_top`)
gives, for `0 ≤ s < r`:

`f ∈ A^s_q(L_p, (E_k))  ↔  ‖f‖_p + ‖(2^(ks) ω_r(f, 2^(-k))_p)_k‖_{ℓ_q} < ∞`

(`Rd.memApprox_bandScheme_iff_modulus`). With the Littlewood–Paley characterisation
(`Rd.memApprox_bandScheme_iff`), the three descriptions of `B^s_{p,q}(V)` coincide for `0 < s < r`:
by approximation with band-limited functions, by Littlewood–Paley blocks, and by differences
(`Rd.littlewoodPaleyNorm_lt_top_iff_modulus`). Since `ω_{r+l} ≤ 2^l ω_r`
(`Rd.lpModulus_add_order_le`), the norm with moduli of order `L ≥ r` is at most `2^(L-r)` times
the norm with order `r` (`Rd.modNorm_order_le_of_le`), and the norm with moduli in `ℓ_1` is
countably subadditive (`Rd.modNorm_one_tsum_le`).
-/

@[expose] public section

open MeasureTheory
open scoped ENNReal

namespace Rd

open ENNReal (lqNorm dyadicWeight)

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V] {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- **The modulus of smoothness is compatible with the band-limited scheme**, with inverse order
`r`: Jackson's inequality from level `0` on, and the inverse inequality for band-limited
functions. -/
noncomputable def bandModulusData (hp : p ≠ ∞) (r : ℕ) :
    ApproximationScheme.ModulusData (bandScheme (V := V) hp) r where
  modulus f k := lpModulus p r f k
  add_le f g k := lpModulus_add_le r f g k
  C0 := 2 ^ r
  C0_ne_top := by simp
  le_enorm f k := lpModulus_le r f k
  jacksonStart := 0
  CJ := jacksonConst V r p
  CJ_ne_top := jacksonConst_ne_top Fact.out hp r
  jackson f k _ := approxError_bandScheme_le hp r k f
  CB := bandInverseConst V r
  CB_ne_top := bandInverseConst_ne_top r
  inverse _ _ _ ha := lpModulus_le_of_mem_bandSpace hp r (mem_bandScheme_two_pow.1 ha)

/-- The classical quasi-norm of `Rd.bandModulusData hp r` is
`‖f‖_p + ‖(2^(ks) ω_r(f, 2^(-k))_p)_k‖_{ℓ_q}`. -/
theorem modNorm_bandModulusData (hp : p ≠ ∞) (r : ℕ) (s : ℝ) (q : ℝ≥0∞)
    (f : Lp ℂ p (volume : Measure V)) :
    (bandModulusData hp r).modNorm s q f =
      ‖f‖ₑ + lqNorm q (fun k => dyadicWeight s k * lpModulus p r f k) := rfl

/-- **Band-limited approximation and moduli of smoothness**: for `1 ≤ p < ∞`, `0 ≤ s < r` and
`1 ≤ q ≤ ∞`, `f ∈ A^s_q(L_p, (E_k))` iff `‖f‖_p + ‖(2^(ks) ω_r(f, 2^(-k))_p)_k‖_{ℓ_q} < ∞`. -/
theorem memApprox_bandScheme_iff_modulus (hp : p ≠ ∞) {r : ℕ} {s : ℝ} (hs : 0 ≤ s)
    (hsr : s < r) {q : ℝ≥0∞} (hq : 1 ≤ q) (f : Lp ℂ p (volume : Measure V)) :
    (bandScheme hp).MemApprox s q f ↔
      ‖f‖ₑ + lqNorm q (fun k => dyadicWeight s k * lpModulus p r f k) < ∞ :=
  (bandModulusData hp r).memApprox_iff_modNorm_lt_top hq hs hsr f

/-- **Littlewood–Paley blocks and moduli of smoothness**: for `1 ≤ p < ∞`, `0 < s < r` and
`1 ≤ q ≤ ∞`, `(2^(js) ‖ψ_j ⋆ f‖_p)_j ∈ ℓ_q` iff
`‖f‖_p + ‖(2^(ks) ω_r(f, 2^(-k))_p)_k‖_{ℓ_q} < ∞`. -/
theorem littlewoodPaleyNorm_lt_top_iff_modulus (hp : p ≠ ∞) {r : ℕ} {s : ℝ} (hs : 0 < s)
    (hsr : s < r) {q : ℝ≥0∞} (hq : 1 ≤ q) (f : Lp ℂ p (volume : Measure V)) :
    littlewoodPaleyNorm hp s q f < ∞ ↔
      ‖f‖ₑ + lqNorm q (fun k => dyadicWeight s k * lpModulus p r f k) < ∞ := by
  rw [← memApprox_bandScheme_iff hp hs hq, memApprox_bandScheme_iff_modulus hp hs.le hsr hq f]

/-- **The order of the differences does not matter**: for `0 ≤ s < r'` and every order `r`,
`‖F‖_p + ‖(2^(ks) ω_{r'}(F, 2^(-k))_p)_k‖_{ℓ_q} ≤ C (‖F‖_p + ‖(2^(ks) ω_r(F, 2^(-k))_p)_k‖_{ℓ_q})`,
through the band-limited approximation norm: the inverse direction of
`Rd.bandModulusData hp r'` and Jackson's direction of `Rd.bandModulusData hp r`. -/
theorem modNorm_le_modNorm_of_lt (hp : p ≠ ∞) (r : ℕ) {r' : ℕ} {s : ℝ} (hs : 0 ≤ s)
    (hsr' : s < r') {q : ℝ≥0∞} (hq : 1 ≤ q) :
    ∃ C : ℝ≥0∞, C ≠ ∞ ∧ ∀ F : Lp ℂ p (volume : Measure V),
      ‖F‖ₑ + lqNorm q (fun k => dyadicWeight s k * lpModulus p r' F k) ≤
        C * (‖F‖ₑ + lqNorm q (fun k => dyadicWeight s k * lpModulus p r F k)) := by
  set M' := bandModulusData (V := V) hp r'
  set M := bandModulusData (V := V) hp r
  refine ⟨M'.inverseConst s * M.directConst s,
    ENNReal.mul_ne_top (M'.inverseConst_ne_top hsr') (M.directConst_ne_top s), fun F => ?_⟩
  rw [mul_assoc]
  exact (M'.modNorm_le_approxNormDyadic hq hs hsr' F).trans
    (mul_le_mul' le_rfl (M.approxNormDyadic_le_modNorm hq F))

/-- The norm with moduli of order `L ≥ r` is at most `2^(L-r)` times that with order `r`
(`Rd.lpModulus_add_order_le`). -/
theorem modNorm_order_le_of_le {r L : ℕ} (hrL : r ≤ L) (σ : ℝ) (q : ℝ≥0∞)
    (G : Lp ℂ p (volume : Measure V)) :
    ‖G‖ₑ + lqNorm q (fun k => dyadicWeight σ k * lpModulus p L G k) ≤
      2 ^ (L - r) * (‖G‖ₑ + lqNorm q (fun k => dyadicWeight σ k * lpModulus p r G k)) := by
  have hL' : L = r + (L - r) := by omega
  rw [mul_add]
  refine add_le_add (le_mul_of_one_le_left' (one_le_pow₀ one_le_two)) ?_
  rw [← ENNReal.lqNorm_const_mul]
  refine ENNReal.lqNorm_mono fun k => ?_
  calc dyadicWeight σ k * lpModulus p L G k
      ≤ dyadicWeight σ k * (2 ^ (L - r) * lpModulus p r G k) := by
        refine mul_le_mul' le_rfl ?_
        conv_lhs => rw [hL']
        exact lpModulus_add_order_le r (L - r) G k
    _ = 2 ^ (L - r) * (dyadicWeight σ k * lpModulus p r G k) := by ring

/-- **The norm with moduli is countably subadditive in `ℓ_1`**: for a summable series in `L_p`
and `N(G) = ‖G‖ + ‖(2^(kσ) ω_L(G, 2^(-k)))_k‖_{ℓ_1}`, `N(∑ G_i) ≤ ∑_i N(G_i)`, by
`ENNReal.le_tsum_of_tendsto_sum` for the modulus at each scale. -/
theorem modNorm_one_tsum_le (L : ℕ) (σ : ℝ) {G : ℕ → Lp ℂ p (volume : Measure V)}
    (hG : Summable G) :
    ‖∑' i, G i‖ₑ + lqNorm 1 (fun k => dyadicWeight σ k * lpModulus p L (∑' i, G i) k) ≤
      ∑' i, (‖G i‖ₑ + lqNorm 1 (fun k => dyadicWeight σ k * lpModulus p L (G i) k)) := by
  have htend : Filter.Tendsto (fun I => ∑ i ∈ Finset.range (I + 1), G i) Filter.atTop
      (nhds (∑' i, G i)) :=
    (hG.hasSum.tendsto_sum_nat).comp (Filter.tendsto_add_atTop_nat 1)
  have hmod : ∀ k, lpModulus p L (∑' i, G i) k ≤ ∑' i, lpModulus p L (G i) k := fun k =>
    ENNReal.le_tsum_of_tendsto_sum (C := 2 ^ L) (by simp) (fun x y => lpModulus_add_le L x y k)
      (fun x => lpModulus_le L x k) htend
  calc ‖∑' i, G i‖ₑ + lqNorm 1 (fun k => dyadicWeight σ k * lpModulus p L (∑' i, G i) k)
      ≤ ∑' i, ‖G i‖ₑ + ∑' i, lqNorm 1 (fun k => dyadicWeight σ k * lpModulus p L (G i) k) := by
        refine add_le_add eNorm_tsum_le_tsum_eNorm ?_
        rw [ENNReal.lqNorm_one]
        simp_rw [ENNReal.lqNorm_one]
        rw [tsum_comm]
        refine tsum_le_tsum fun k => ?_
        rw [ENNReal.tsum_mul_left]
        exact mul_le_mul' le_rfl (hmod k)
    _ = _ := (tsum_add).symm

end Rd
