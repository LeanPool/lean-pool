/-
Copyright (c) 2026 Mario Ullrich. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Ullrich
-/
module

public import LeanPool.FunctionSpaces.Torus.Modulus
public import LeanPool.FunctionSpaces.ApproximationSpaces.Moduli

/-
Modified for Lean Pool: module names and imports adapted.
-/

/-!
# Besov spaces through moduli of smoothness: the coincidence theorem in `L_2(𝕋^d)`

The classical definition of the Besov space `B^s_{2,q}(𝕋^d)`, `0 < s < 1`, uses the modulus of
smoothness `ω(f, t)_2 = sup_{‖h‖ ≤ t} ‖f(· + h) - f‖_2` at the dyadic scales `t = 2^(-k)`.  This
modulus is compatible with the trigonometric scheme, with inverse order `θ = 1`
(`Torus.trigModulusData`, a `ModulusData`):

* it is subadditive and at most `2 ‖f‖_2` (`Rd.lpModulus_add_le`, `Rd.lpModulus_le`);
* **Jackson's inequality** `E_n(f)_2 ≤ (d + 1) ω(f, 1/n)_2` (`Torus.approxError_le_modulus`);
* **the inverse inequality** `ω(a, 2^(-k))_2 ≤ max(2, 2πd) 2^(-(k-j)) ‖a‖_2` for trigonometric
  polynomials `a` of degree `< 2^j` (`Torus.modulus_le_of_mem`), from Bernstein's inequality
  `‖τ_h a - a‖_2 ≤ 2πd 2^j ‖h‖ ‖a‖_2` (`Torus.enorm_translate_sub_le_of_mem`).

**Coincidence theorem** (`Torus.memBesov_iff_modulusNorm_lt_top`): for `0 < s < 1` and
`1 ≤ q ≤ ∞`, `f` lies in the approximation space `B^s_{2,q}(𝕋^d)` of trigonometric polynomials
iff `‖f‖_2 + ‖(2^(js) ω(f, 2^(-j))_2)_{j ≥ 0}‖_{ℓ_q} < ∞`, with the norm equivalence of
`ModulusData` (`Torus.approxNormDyadic_le_modulusNorm`, `Torus.modulusNorm_le_approxNormDyadic`).
The restriction `s < 1` is that of differences of first order.

The modulus is also controlled by the dyadic Fourier blocks: a translation by `h` multiplies the
block `Δ_K f` by at most `min(2, 2πd 2^(K+1) ‖h‖)` (`Torus.enorm_translate_sub_sq_le`), so
`ω(f, t)_2 ≤ ∑_K min(2, 2πd 2^(K+1) t) ‖Δ_K f‖_2` (`Torus.modulus_le_tsum_block`).
-/

@[expose] public section

open MeasureTheory UnitAddTorus Set ApproximationScheme
open scoped ENNReal TorusHaar lp Real

namespace Torus

open ENNReal (lqNorm dyadicWeight)

variable {d : Type*} [Fintype d] {s : ℝ} {q : ℝ≥0∞}

/-! ### Jackson's inequality -/

/-- Jackson's theorem in the form `E_n(f) ≤ (d + 1) ω(f, 1/n)`. -/
theorem approxError_le_modulus {n : ℕ} (hn : 1 ≤ n)
    (f : Lp ℂ 2 (volume : Measure (UnitAddTorus d))) :
    ((trigScheme d).toLp volume 2).approxError f n ≤
      ((Fintype.card d : ℝ≥0∞) + 1) * modulus f (1 / n) := by
  have h := approxError_sq_le_card_mul_modulus_sq hn f
  have hd : (Fintype.card d : ℝ≥0∞) ≤ ((Fintype.card d : ℝ≥0∞) + 1) ^ 2 := by
    calc (Fintype.card d : ℝ≥0∞) ≤ (Fintype.card d : ℝ≥0∞) + 1 := le_self_add
      _ ≤ ((Fintype.card d : ℝ≥0∞) + 1) ^ 2 := by
          rw [sq]; exact le_mul_of_one_le_left' le_add_self
  have h2 : ((trigScheme d).toLp volume 2).approxError f n ^ 2 ≤
      (((Fintype.card d : ℝ≥0∞) + 1) * modulus f (1 / n)) ^ 2 := by
    rw [mul_pow]; exact h.trans (by gcongr)
  rw [← ENNReal.rpow_two, ← ENNReal.rpow_two] at h2
  exact (ENNReal.rpow_le_rpow_iff (by norm_num)).1 h2

/-! ### The inverse inequality -/

/-- **Trigonometric polynomials have no high frequencies**: for `a` of degree `< n`,
`â(k) = 0` whenever `deg k ≥ n` (`SpectralScheme.repr_eq_zero_of_mem_span`). -/
theorem mFourierCoeff_eq_zero_of_mem {n : ℕ} {a : Lp ℂ 2 (volume : Measure (UnitAddTorus d))}
    (ha : a ∈ (trigScheme d).toLp volume 2 n) {k : d → ℤ} (hk : n ≤ deg k) :
    mFourierCoeff a k = 0 := by
  rw [toLp_trigScheme_eq d] at ha
  rw [← mFourierBasis_repr]
  exact (fourierScheme d).repr_eq_zero_of_mem_span ha hk

/-- **Bernstein's inequality for translations**: a trigonometric polynomial `a` of degree `< n`
satisfies `‖τ_h a - a‖_2 ≤ 2πd n ‖h‖ ‖a‖_2`, by Parseval and `|e_k(h) - 1| ≤ 2πd deg k ‖h‖`
(`Torus.norm_mFourier_sub_one_le`). -/
theorem enorm_translate_sub_le_of_mem {n : ℕ} {a : Lp ℂ 2 (volume : Measure (UnitAddTorus d))}
    (ha : a ∈ (trigScheme d).toLp volume 2 n) (h : UnitAddTorus d) :
    ‖translate h a - a‖ₑ ≤ ENNReal.ofReal (2 * π * Fintype.card d * n * ‖h‖) * ‖a‖ₑ := by
  have hpars : ‖a‖ₑ ^ 2 = ∑' k, ‖mFourierCoeff a k‖ₑ ^ 2 := by
    rw [← mFourierBasis.repr.eNorm_map, lp.enorm_sq_eq_tsum]
    simp only [mFourierBasis_repr]
  refine (ENNReal.pow_le_pow_left_iff two_ne_zero).1 ?_
  rw [enorm_translate_sub_sq, mul_pow, hpars, ← ENNReal.tsum_mul_left]
  refine tsum_le_tsum fun k => ?_
  rcases le_or_gt n (deg k) with hk | hk
  · simp [mFourierCoeff_eq_zero_of_mem ha hk]
  · gcongr
    rw [← ofReal_norm]
    refine ENNReal.ofReal_le_ofReal ((norm_mFourier_sub_one_le k h).trans ?_)
    gcongr

/-- **The inverse inequality for the modulus**: a trigonometric polynomial `a` of degree `< 2^j`
satisfies `ω(a, 2^(-k))_2 ≤ max(2, 2πd) 2^(-(k-j)) ‖a‖_2`: for `k < j` the modulus is at most
`2 ‖a‖_2`, and for `k ≥ j` Bernstein's inequality gives `2πd 2^(j-k) ‖a‖_2`. -/
theorem modulus_le_of_mem {j : ℕ} {a : Lp ℂ 2 (volume : Measure (UnitAddTorus d))}
    (ha : a ∈ (trigScheme d).toLp volume 2 (2 ^ j)) (k : ℕ) :
    modulus a (1 / 2 ^ k) ≤
      ENNReal.ofReal (max 2 (2 * π * Fintype.card d)) * dyadicWeight (-1) (k - j) * ‖a‖ₑ := by
  rcases lt_or_ge k j with hkj | hjk
  · rw [Nat.sub_eq_zero_of_le hkj.le, ENNReal.dyadicWeight_zero_right, mul_one]
    refine (Rd.lpModulus_le 1 a k).trans ?_
    gcongr
    rw [pow_one, ← ENNReal.ofReal_ofNat 2]
    exact ENNReal.ofReal_le_ofReal (le_max_left _ _)
  · rw [modulus_eq_iSup]
    refine iSup₂_le fun h hh => (enorm_translate_sub_le_of_mem ha h).trans ?_
    have h1 : ENNReal.ofReal (2 * π * Fintype.card d * ((2 ^ j : ℕ) : ℝ) * ‖h‖) =
        ENNReal.ofReal (2 * π * Fintype.card d) * ENNReal.ofReal (2 ^ j * ‖h‖) := by
      rw [show 2 * π * Fintype.card d * ((2 ^ j : ℕ) : ℝ) * ‖h‖ =
          (2 * π * Fintype.card d) * (2 ^ j * ‖h‖) by push_cast; ring,
        ENNReal.ofReal_mul (by positivity)]
    rw [h1]
    refine mul_le_mul' (mul_le_mul' (ENNReal.ofReal_le_ofReal (le_max_right _ _)) ?_) le_rfl
    simpa using ENNReal.ofReal_two_pow_mul_rpow_le hjk hh zero_le_one

/-! ### The coincidence theorem -/

/-- **The modulus is compatible with the trigonometric scheme**, with inverse order `θ = 1`: at
the scales `2^(-k)` it is subadditive and at most `2 ‖f‖_2`, Jackson's inequality holds from
`k = 0` on with the constant `d + 1`, and the inverse inequality with the constant
`max(2, 2πd)`. -/
noncomputable def trigModulusData (d : Type*) [Fintype d] :
    ModulusData ((trigScheme d).toLp volume 2) 1 where
  modulus f k := modulus f (1 / 2 ^ k)
  add_le f g k := Rd.lpModulus_add_le 1 f g k
  C0 := 2
  C0_ne_top := by norm_num
  le_enorm f k := (Rd.lpModulus_le 1 f k).trans_eq (by rw [pow_one])
  jacksonStart := 0
  CJ := Fintype.card d + 1
  CJ_ne_top := ENNReal.add_ne_top.2 ⟨ENNReal.natCast_ne_top _, ENNReal.one_ne_top⟩
  jackson f k _ := by simpa using approxError_le_modulus (Nat.one_le_two_pow (n := k)) f
  CB := ENNReal.ofReal (max 2 (2 * π * Fintype.card d))
  CB_ne_top := ENNReal.ofReal_ne_top
  inverse _ k _ ha := modulus_le_of_mem ha k

/-- **Jackson's half of the coincidence theorem**: `‖f‖_{B^s_{2,q}} ≤ (d + 2) ‖f‖^ω_{s,q}` in the
dyadic quasi-norm, with the constant `1 + C_J` of `ModulusData.approxNormDyadic_le_modNorm`. -/
theorem approxNormDyadic_le_modulusNorm (hq : 1 ≤ q)
    (f : Lp ℂ 2 (volume : Measure (UnitAddTorus d))) :
    ((trigScheme d).toLp volume 2).approxNormDyadic s q f ≤
      (trigModulusData d).directConst s * (trigModulusData d).modNorm s q f :=
  (trigModulusData d).approxNormDyadic_le_modNorm hq f

/-- **The second half of the coincidence theorem**: for `0 ≤ s < 1`,
`‖f‖^ω_{s,q} ≤ K ‖f‖_{B^s_{2,q}}` in the dyadic quasi-norm, with the constant `K` of
`ModulusData.modNorm_le_approxNormDyadic`. -/
theorem modulusNorm_le_approxNormDyadic (hq : 1 ≤ q) (hs : 0 ≤ s) (hs1 : s < 1)
    (f : Lp ℂ 2 (volume : Measure (UnitAddTorus d))) :
    (trigModulusData d).modNorm s q f ≤
      (trigModulusData d).inverseConst s * ((trigScheme d).toLp volume 2).approxNormDyadic s q f :=
  (trigModulusData d).modNorm_le_approxNormDyadic hq hs hs1 f

/-- **The coincidence theorem in `L_2(𝕋^d)`**: for `0 < s < 1` and `1 ≤ q ≤ ∞`, the Besov space
`B^s_{2,q}(𝕋^d)` defined by approximation with trigonometric polynomials is the Besov space
defined by the modulus of smoothness: `f ∈ B^s_{2,q}` iff
`‖f‖_2 + ‖(2^(js) ω(f, 2^(-j))_2)_j‖_{ℓ_q} < ∞`. -/
theorem memBesov_iff_modulusNorm_lt_top (hs : 0 < s) (hs1 : s < 1) (hq : 1 ≤ q)
    (f : Lp ℂ 2 (volume : Measure (UnitAddTorus d))) :
    (trigScheme d).MemBesov volume 2 s q f ↔ (trigModulusData d).modNorm s q f < ∞ :=
  (trigModulusData d).memApprox_iff_modNorm_lt_top hq hs.le hs1 f

/-! ### The modulus and the dyadic Fourier blocks -/

/-- The multiplier bound of a translation by `‖h‖ ≤ t` on the dyadic block `K`:
`min(2, 2πd 2^(K+1) t)`. -/
noncomputable def blockMult (d : Type*) [Fintype d] (K : ℕ) (t : ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal (min 2 (2 * π * Fintype.card d * 2 ^ (K + 1) * t))

/-- On the block `K`, `|e_k(h) - 1| ≤ min(2, 2πd 2^(K+1) ‖h‖)`. -/
theorem enorm_mFourier_sub_one_le_blockMult {k : d → ℤ} {K : ℕ} (hk : deg k < 2 ^ (K + 1))
    {h : UnitAddTorus d} {t : ℝ} (hh : ‖h‖ ≤ t) :
    ‖mFourier k h - 1‖ₑ ≤ blockMult d K t := by
  rw [blockMult, ← ofReal_norm]
  refine ENNReal.ofReal_le_ofReal (le_min ?_ ?_)
  · calc ‖mFourier k h - 1‖ ≤ ‖mFourier k h‖ + ‖(1 : ℂ)‖ := norm_sub_le _ _
      _ = 2 := by
          rw [norm_one, show ‖mFourier k h‖ = 1 from norm_trigMonomial_apply k h]; norm_num
  · calc ‖mFourier k h - 1‖ ≤ 2 * π * Fintype.card d * deg k * ‖h‖ :=
          norm_mFourier_sub_one_le k h
      _ ≤ 2 * π * Fintype.card d * 2 ^ (K + 1) * t := by
          gcongr
          exact_mod_cast hk.le

/-- **A translation acts on the dyadic blocks with bounded multipliers**: for `‖h‖ ≤ t`,
`‖f(· + h) - f‖² ≤ ∑_K min(2, 2πd 2^(K+1) t)² ‖Δ_K f‖²`. -/
theorem enorm_translate_sub_sq_le {h : UnitAddTorus d} {t : ℝ} (hh : ‖h‖ ≤ t)
    (f : Lp ℂ 2 (volume : Measure (UnitAddTorus d))) :
    ‖translate h f - f‖ₑ ^ 2 ≤ ∑' K, blockMult d K t ^ 2 * ‖fourierBlock K f‖ₑ ^ 2 := by
  rw [enorm_translate_sub_sq]
  simp_rw [enorm_fourierBlock_sq, ← ENNReal.tsum_mul_left]
  rw [tsum_comm]
  refine tsum_le_tsum fun k => ?_
  rcases Nat.eq_zero_or_pos (deg k) with h0 | hpos
  · have hk : k = 0 := by
      funext i; have := natAbs_le_deg k i; rw [h0] at this; simpa using this
    subst hk
    simp [mFourier_zero]
  set K0 := Nat.log 2 (deg k)
  have hK0 : 2 ^ K0 ≤ deg k ∧ deg k < 2 ^ (K0 + 1) :=
    ⟨Nat.pow_log_le_self 2 hpos.ne', Nat.lt_pow_succ_log_self Nat.one_lt_two _⟩
  calc ‖mFourier k h - 1‖ₑ ^ 2 * ‖mFourierCoeff f k‖ₑ ^ 2
      ≤ blockMult d K0 t ^ 2 * ‖mFourierCoeff f k‖ₑ ^ 2 := by
        gcongr; exact enorm_mFourier_sub_one_le_blockMult hK0.2 hh
    _ = blockMult d K0 t ^ 2 * (if 2 ^ K0 ≤ deg k ∧ deg k < 2 ^ (K0 + 1) then
          ‖mFourierCoeff f k‖ₑ ^ 2 else 0) := by simp only [hK0, and_self, ↓reduceIte]
    _ ≤ ∑' K, blockMult d K t ^ 2 * (if 2 ^ K ≤ deg k ∧ deg k < 2 ^ (K + 1) then
          ‖mFourierCoeff f k‖ₑ ^ 2 else 0) :=
        le_tsum (f := fun K => blockMult d K t ^ 2 * (if 2 ^ K ≤ deg k ∧
          deg k < 2 ^ (K + 1) then ‖mFourierCoeff f k‖ₑ ^ 2 else 0)) K0

/-- **The modulus is controlled by the dyadic blocks**:
`ω(f, t) ≤ ∑_K min(2, 2πd 2^(K+1) t) ‖Δ_K f‖`. The square-sum bound
`enorm_translate_sub_sq_le` passes to the sum through `∑ b_K² ≤ (∑ b_K)²`. -/
theorem modulus_le_tsum_block (f : Lp ℂ 2 (volume : Measure (UnitAddTorus d))) (t : ℝ) :
    modulus f t ≤ ∑' K, blockMult d K t * ‖fourierBlock K f‖ₑ := by
  rw [modulus_eq_iSup]
  refine iSup₂_le fun h hh => (ENNReal.pow_le_pow_left_iff two_ne_zero).1 ?_
  calc ‖translate h f - f‖ₑ ^ 2 ≤ ∑' K, (blockMult d K t * ‖fourierBlock K f‖ₑ) ^ 2 := by
        simpa only [mul_pow] using enorm_translate_sub_sq_le hh f
    _ ≤ (∑' K, blockMult d K t * ‖fourierBlock K f‖ₑ) ^ 2 := by
        simp only [sq, ← ENNReal.tsum_mul_right]
        exact tsum_le_tsum fun K => by
          gcongr; exact le_tsum (f := fun K => blockMult d K t * ‖fourierBlock K f‖ₑ) K

/-- At `t = 2^(-j)` the block multipliers are `≤ 2` for `K ≥ j` and `≤ 4πd 2^(K-j)` for
`K ≤ j`. -/
theorem blockMult_le (K j : ℕ) :
    blockMult d K (1 / 2 ^ j) ≤ (if j ≤ K then 2 else 0) +
      (if K ≤ j then ENNReal.ofReal (4 * π * Fintype.card d) *
        (dyadicWeight (-1) j * dyadicWeight 1 K) else 0) := by
  by_cases hjK : j ≤ K
  · simp only [hjK, ↓reduceIte]
    refine le_trans ?_ le_self_add
    rw [blockMult, ← ENNReal.ofReal_ofNat 2]
    exact ENNReal.ofReal_le_ofReal (min_le_left _ _)
  · simp only [hjK, show K ≤ j by omega, ↓reduceIte, zero_add]
    have h1 : ENNReal.ofReal ((2 : ℝ) ^ K * (1 / 2 ^ j)) =
        dyadicWeight (-1) j * dyadicWeight 1 K := by
      rw [ENNReal.ofReal_mul (by positivity), one_div, ENNReal.ofReal_inv_of_pos (by positivity),
        show ((2 : ℝ) ^ K) = ((2 ^ K : ℕ) : ℝ) by push_cast; rfl,
        show ((2 : ℝ) ^ j) = ((2 ^ j : ℕ) : ℝ) by push_cast; rfl, ENNReal.ofReal_natCast,
        ENNReal.ofReal_natCast, ENNReal.natCast_two_pow_eq, ENNReal.natCast_two_pow_eq,
        ← ENNReal.dyadicWeight_neg, mul_comm]
    calc blockMult d K (1 / 2 ^ j)
        ≤ ENNReal.ofReal (4 * π * Fintype.card d * ((2 : ℝ) ^ K * (1 / 2 ^ j))) := by
          rw [blockMult]
          refine ENNReal.ofReal_le_ofReal ((min_le_right _ _).trans_eq ?_)
          ring
      _ = ENNReal.ofReal (4 * π * Fintype.card d) * (dyadicWeight (-1) j * dyadicWeight 1 K) := by
          rw [ENNReal.ofReal_mul (by positivity), h1]

end Torus
