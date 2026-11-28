/-
Copyright (c) 2026 Mario Ullrich. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Ullrich
-/
module

public import LeanPool.FunctionSpaces.ApproximationSpaces.Lift
public import LeanPool.FunctionSpaces.ApproximationSpaces.Sequences.Hardy
public import LeanPool.FunctionSpaces.ApproximationSpaces.Interpolation.ApproxSpaces

/-
Modified for Lean Pool: module names and imports adapted.
-/

/-!
# Moduli of smoothness and approximation: the coincidence theorem

Classical function spaces are defined by a **modulus of smoothness** `ω(f, 2^(-k))`, approximation
spaces by the errors `E_{2^k}(f)`.  They coincide when the scheme and the modulus are linked by

* a **Jackson inequality** `E_{2^k}(f) ≤ C_J ω(f, 2^(-k))` for `k ≥ k₀`, and
* an **inverse inequality** of order `θ`: `ω(a, 2^(-k)) ≤ C_B 2^(-(k-j)θ) ‖a‖` for `a ∈ A_{2^j}`
  (with `k - j` truncated at `0`, so for `k < j` this is a bound by `‖a‖`).

A `ModulusData A θ` bundles the modulus (sampled at dyadic scales, `modulus f k = ω(f,
2^(-k))`), its
subadditivity and bound `ω(f) ≤ C₀ ‖f‖`, and the two inequalities; `ModulusData.ofExists`
builds one from existence statements for the constants `C_J`, `C_B`.  With the classical
quasi-norm `‖f‖ + ‖(2^(ks) ω(f, 2^(-k)))_k‖_{ℓ_q}` (`ModulusData.modNorm`):

* `‖f‖_{A^s_q} ≤ (1 + ∑_{k<k₀} 2^(ks) + C_J) ‖f‖^ω_{s,q}` for all `s ≥ 0`
  (`ModulusData.approxNormDyadic_le_modNorm`): the finitely many levels `k < k₀` are bounded by
  `E_{2^k}(f) ≤ ‖f‖`, so Jackson is needed only from `k₀` on;
* `‖f‖^ω_{s,q} ≤ K ‖f‖_{A^s_q}` for `0 ≤ s < θ` (`ModulusData.modNorm_le_approxNormDyadic`),
  by writing `f` as `(f - a_k) + a_0 + ∑_{j<k} (a_{j+1} - a_j)` with near-best approximants and
  applying the inverse inequality to each block and Hardy's inequality to the sum.

So `A^s_q` is the classical space for `0 < s < θ` (`ModulusData.memApprox_iff_modNorm_lt_top`).
With the sandwich principle of `ApproximationSpaces.Interpolation.ApproxSpaces`, the classical
spaces of smoothness `0 < s₀ < s₁ < θ` interpolate to the classical space of smoothness
`(1-η)s₀ + ηs₁`, and `X` with the classical space of smoothness `s₁` to that of smoothness `ηs₁`
(`ModulusData.memKMethod_modCouple_iff`, `ModulusData.memKMethod_leftModCouple_iff`).
The same theorem serves trigonometric polynomials (`θ = r` for `ω_r`), piecewise polynomials
(`θ = 1/p`), splines and wavelets.
-/

@[expose] public section

open Filter Topology Finset
open scoped ENNReal

namespace ApproximationScheme

open ENNReal (lqNorm dyadicWeight)

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
  {A : ApproximationScheme X} {s : ℝ} {q : ℝ≥0∞}

/-- A **modulus of smoothness compatible with the scheme `A`**, with inverse order `θ`: the
modulus at the dyadic scales `modulus f k = ω(f, 2^(-k))`, subadditive and bounded by `C₀ ‖f‖`,
with a
Jackson inequality `E_{2^k}(f) ≤ C_J ω(f, 2^(-k))` for `k ≥ k₀` and an inverse inequality
`ω(a, 2^(-k)) ≤ C_B 2^(-(k-j)θ) ‖a‖` for `a ∈ A_{2^j}`. -/
structure ModulusData (A : ApproximationScheme X) (θ : ℝ) where
  /-- The modulus at the dyadic scales. -/
  modulus : X → ℕ → ℝ≥0∞
  add_le : ∀ f g k, modulus (f + g) k ≤ modulus f k + modulus g k
  /-- The constant of `ω(f) ≤ C₀ ‖f‖`. -/
  C0 : ℝ≥0∞
  C0_ne_top : C0 ≠ ∞
  le_enorm : ∀ f k, modulus f k ≤ C0 * ‖f‖ₑ
  /-- The level `k₀` from which on the Jackson inequality holds. -/
  jacksonStart : ℕ
  /-- The Jackson constant. -/
  CJ : ℝ≥0∞
  CJ_ne_top : CJ ≠ ∞
  jackson : ∀ f k, jacksonStart ≤ k → A.approxError f (2 ^ k) ≤ CJ * modulus f k
  /-- The constant of the inverse inequality. -/
  CB : ℝ≥0∞
  CB_ne_top : CB ≠ ∞
  inverse : ∀ j k, ∀ a ∈ A (2 ^ j), modulus a k ≤ CB * dyadicWeight (-θ) (k - j) * ‖a‖ₑ

namespace ModulusData

variable {θ : ℝ}

/-- A modulus compatible with the scheme from **existence statements** for the two constants:
the modulus with its subadditivity and the bound `ω(f) ≤ C₀ ‖f‖`, a Jackson inequality
`E_{2^k}(f) ≤ C_J ω(f, 2^(-k))` for `k ≥ k₀` with some finite `C_J`, and an inverse inequality
`ω(a, 2^(-k)) ≤ C_B 2^(-(k-j)θ) ‖a‖`, `a ∈ A_{2^j}`, with some finite `C_B`.  The constants
`C_J`, `C_B` are chosen with `Exists.choose`. -/
noncomputable def ofExists (modulus : X → ℕ → ℝ≥0∞)
    (add_le : ∀ f g k, modulus (f + g) k ≤ modulus f k + modulus g k) (C0 : ℝ≥0∞)
    (C0_ne_top : C0 ≠ ∞) (le_enorm : ∀ f k, modulus f k ≤ C0 * ‖f‖ₑ) (jacksonStart : ℕ)
    (hJ : ∃ CJ : ℝ≥0∞, CJ ≠ ∞ ∧
      ∀ f k, jacksonStart ≤ k → A.approxError f (2 ^ k) ≤ CJ * modulus f k)
    (hB : ∃ CB : ℝ≥0∞, CB ≠ ∞ ∧
      ∀ j k, ∀ a ∈ A (2 ^ j), modulus a k ≤ CB * dyadicWeight (-θ) (k - j) * ‖a‖ₑ) :
    ModulusData A θ where
  modulus := modulus
  add_le := add_le
  C0 := C0
  C0_ne_top := C0_ne_top
  le_enorm := le_enorm
  jacksonStart := jacksonStart
  CJ := hJ.choose
  CJ_ne_top := hJ.choose_spec.1
  jackson := hJ.choose_spec.2
  CB := hB.choose
  CB_ne_top := hB.choose_spec.1
  inverse := hB.choose_spec.2

variable (M : ModulusData A θ)

/-- The **classical quasi-norm** `‖f‖ + ‖(2^(ks) ω(f, 2^(-k)))_k‖_{ℓ_q}`. -/
noncomputable def modNorm (s : ℝ) (q : ℝ≥0∞) (f : X) : ℝ≥0∞ :=
  ‖f‖ₑ + lqNorm q (fun k => dyadicWeight s k * M.modulus f k)

/-- The modulus of `0` vanishes. -/
theorem modulus_zero (k : ℕ) : M.modulus 0 k = 0 :=
  le_antisymm ((M.le_enorm 0 k).trans (by simp)) bot_le

/-- The modulus is subadditive on finite sums (Mathlib's `Finset.le_sum_of_subadditive`). -/
theorem modulus_sum_le {ι : Type*} (t : Finset ι) (g : ι → X) (k : ℕ) :
    M.modulus (∑ i ∈ t, g i) k ≤ ∑ i ∈ t, M.modulus (g i) k :=
  Finset.le_sum_of_subadditive (M.modulus · k) (M.modulus_zero k).le (fun f g => M.add_le f g k)
    t g

/-- The constant of Jackson's direction, `1 + ∑_{k<k₀} 2^(ks) + C_J`. -/
noncomputable def directConst (s : ℝ) : ℝ≥0∞ :=
  1 + ∑ k ∈ range M.jacksonStart, dyadicWeight s k + M.CJ

/-- The constant of Jackson's direction is finite. -/
theorem directConst_ne_top (s : ℝ) : M.directConst s ≠ ∞ :=
  ENNReal.add_ne_top.2 ⟨ENNReal.add_ne_top.2 ⟨ENNReal.one_ne_top,
    ENNReal.sum_ne_top.2 fun k _ => ENNReal.dyadicWeight_ne_top s k⟩, M.CJ_ne_top⟩

/-- **Jackson's direction**: `‖f‖_{A^s_q} ≤ (1 + ∑_{k<k₀} 2^(ks) + C_J) ‖f‖^ω_{s,q}`. -/
theorem approxNormDyadic_le_modNorm (hq : 1 ≤ q) (f : X) :
    A.approxNormDyadic s q f ≤ M.directConst s * M.modNorm s q f := by
  set L := lqNorm q (fun k => dyadicWeight s k * M.modulus f k)
  set W := ∑ k ∈ range M.jacksonStart, dyadicWeight s k
  -- the levels below `k₀` and from `k₀` on
  have hpt : ∀ k, A.approxSeqDyadic s f k ≤
      (if k < M.jacksonStart then dyadicWeight s k * ‖f‖ₑ else 0) +
        M.CJ * (dyadicWeight s k * M.modulus f k) := fun k => by
    rw [approxSeqDyadic]
    split_ifs with hk
    · exact le_add_right (by gcongr; exact approxError_le_enorm f _)
    · rw [zero_add, mul_left_comm]
      gcongr
      exact M.jackson f k (not_lt.1 hk)
  have hlow : lqNorm q (fun k => if k < M.jacksonStart then dyadicWeight s k * ‖f‖ₑ else 0) ≤
      W * ‖f‖ₑ := by
    refine (ENNReal.lqNorm_le_sum_of_eq_zero hq (range M.jacksonStart) fun k hk => by
      rw [mem_range] at hk; simp only [hk, ↓reduceIte]).trans_eq ?_
    rw [Finset.sum_mul]
    exact Finset.sum_congr rfl fun k hk => by rw [mem_range] at hk; simp only [hk, ↓reduceIte]
  calc A.approxNormDyadic s q f = ‖f‖ₑ + lqNorm q (A.approxSeqDyadic s f) := rfl
    _ ≤ ‖f‖ₑ + (W * ‖f‖ₑ + M.CJ * L) := by
        gcongr
        refine (ENNReal.lqNorm_mono hpt).trans ((ENNReal.lqNorm_add_le hq _ _).trans ?_)
        rw [ENNReal.lqNorm_const_mul]
        gcongr
    _ ≤ (1 + W + M.CJ) * (‖f‖ₑ + L) := by
        calc ‖f‖ₑ + (W * ‖f‖ₑ + M.CJ * L) = (1 + W) * ‖f‖ₑ + M.CJ * L := by ring
          _ ≤ ((1 + W) * ‖f‖ₑ + M.CJ * ‖f‖ₑ) + ((1 + W) * L + M.CJ * L) := by
              gcongr
              · exact le_self_add
              · exact le_add_self
          _ = (1 + W + M.CJ) * (‖f‖ₑ + L) := by ring

/-- The constant of the inverse direction,
`1 + 3 C₀ + C_B (3 + 6 · 4^θ) (1 - 2^(-(θ-s)))⁻¹`. -/
noncomputable def inverseConst (s : ℝ) : ℝ≥0∞ :=
  1 + 3 * M.C0 + M.CB * (3 + 6 * dyadicWeight θ 2) * (1 - (2 : ℝ≥0∞) ^ (-(θ - s)))⁻¹

/-- The constant of the inverse direction is finite for `s < θ`. -/
theorem inverseConst_ne_top (hsθ : s < θ) : M.inverseConst s ≠ ∞ := by
  have hr : (2 : ℝ≥0∞) ^ (-(θ - s)) < 1 := ENNReal.two_rpow_neg_lt_one (by linarith)
  unfold inverseConst
  refine ENNReal.add_ne_top.2 ⟨ENNReal.add_ne_top.2 ⟨ENNReal.one_ne_top,
    ENNReal.mul_ne_top (by norm_num) M.C0_ne_top⟩, ENNReal.mul_ne_top (ENNReal.mul_ne_top
      M.CB_ne_top (ENNReal.add_ne_top.2 ⟨by norm_num, ENNReal.mul_ne_top (by norm_num)
        (ENNReal.dyadicWeight_ne_top _ _)⟩)) (ENNReal.inv_ne_top.2 (tsub_pos_of_lt hr).ne')⟩

/-- **The modulus at one scale from near-best approximants**: for near-best approximants
`a_k ∈ A_{2^k}` of `f` with an antitone tolerance `t` and `t_0 = ‖f‖`, the telescoping
`f = (f - a_k) + a_0 + ∑_{j<k} (a_{j+1} - a_j)` and the inverse inequality give
`ω(f, 2^(-k)) ≤ C₀ (E_{2^k}(f) + t_k) + 3 C_B 2^(-kθ) ‖f‖
  + ∑_{j<k} 2 C_B 4^θ 2^(-(k-j)θ) (E_{2^j}(f) + t_j)`. -/
theorem modulus_le_of_dyadicApprox (hθ : 0 ≤ θ) {f : X} {t : ℕ → ℝ≥0∞}
    (D : A.DyadicApprox f t) (ht : Antitone t) (ht0 : t 0 = ‖f‖ₑ) (k : ℕ) :
    M.modulus f k ≤ M.C0 * (A.approxError f (2 ^ k) + t k) +
      M.CB * dyadicWeight (-θ) k * (3 * ‖f‖ₑ) + ∑ j ∈ range k,
        M.CB * (2 * dyadicWeight θ 2) * (dyadicWeight (-θ) (k - j) *
          (A.approxError f (2 ^ j) + t j)) := by
  have htel : f = (f - D.a k) + (D.a 0 + ∑ j ∈ range k, (D.a (j + 1) - D.a j)) := by
    rw [sum_range_sub (fun j => D.a j) k]; abel
  have h1 : M.modulus (f - D.a k) k ≤ M.C0 * (A.approxError f (2 ^ k) + t k) :=
    (M.le_enorm _ k).trans (by gcongr; exact D.eNorm_sub_le k)
  have h2 : M.modulus (D.a 0) k ≤ M.CB * dyadicWeight (-θ) k * (3 * ‖f‖ₑ) := by
    refine (M.inverse 0 k _ (by simpa using D.mem 0)).trans ?_
    rw [Nat.sub_zero]
    gcongr
    calc ‖D.a 0‖ₑ ≤ 2 * ‖f‖ₑ + t 0 := D.enorm_zero_le
      _ = 3 * ‖f‖ₑ := by rw [ht0]; ring
  have h3 : ∀ j ∈ range k, M.modulus (D.a (j + 1) - D.a j) k ≤
      M.CB * (2 * dyadicWeight θ 2) * (dyadicWeight (-θ) (k - j) *
        (A.approxError f (2 ^ j) + t j)) := fun j _ => by
    refine (M.inverse (j + 2) k _ (D.sub_mem j)).trans ?_
    calc M.CB * dyadicWeight (-θ) (k - (j + 2)) * ‖D.a (j + 1) - D.a j‖ₑ
        ≤ M.CB * (dyadicWeight θ 2 * dyadicWeight (-θ) (k - j)) *
            (2 * (A.approxError f (2 ^ j) + t j)) := by
          gcongr
          · rw [show k - (j + 2) = k - j - 2 by omega]
            exact ENNReal.dyadicWeight_neg_sub_two_le hθ (k - j)
          · exact D.enorm_sub_succ_le ht j
      _ = _ := by ring
  calc M.modulus f k
      = M.modulus ((f - D.a k) + (D.a 0 + ∑ j ∈ range k, (D.a (j + 1) - D.a j))) k := by
        rw [← htel]
    _ ≤ M.modulus (f - D.a k) k +
          (M.modulus (D.a 0) k + ∑ j ∈ range k, M.modulus (D.a (j + 1) - D.a j) k) :=
        (M.add_le _ _ k).trans (add_le_add le_rfl ((M.add_le _ _ k).trans
          (add_le_add le_rfl (M.modulus_sum_le _ _ k))))
    _ ≤ _ := by
        rw [← add_assoc]
        exact add_le_add (add_le_add h1 h2) (Finset.sum_le_sum h3)

/-- **The weighted modulus at one scale**: with `E_k = 2^(ks) (E_{2^k}(f) + t_k)` and
`α = θ - s`, `ModulusData.modulus_le_of_dyadicApprox` multiplied by `2^(ks)` reads
`2^(ks) ω(f, 2^(-k)) ≤ C₀ E_k + 3 C_B ‖f‖ 2^(-kα) + 2 C_B 4^θ 2^(-kα) ∑_{j ≤ k} 2^(jα) E_j`. -/
theorem dyadicWeight_mul_modulus_le_of_dyadicApprox (hθ : 0 ≤ θ) {f : X} {t : ℕ → ℝ≥0∞}
    (D : A.DyadicApprox f t) (ht : Antitone t) (ht0 : t 0 = ‖f‖ₑ) (k : ℕ) :
    dyadicWeight s k * M.modulus f k ≤
      M.C0 * (dyadicWeight s k * (A.approxError f (2 ^ k) + t k)) +
        M.CB * 3 * ‖f‖ₑ * dyadicWeight (-(θ - s)) k +
        M.CB * (2 * dyadicWeight θ 2) * (dyadicWeight (-(θ - s)) k *
          ∑ j ∈ range (k + 1), dyadicWeight (θ - s) j *
            (dyadicWeight s j * (A.approxError f (2 ^ j) + t j))) := by
  have hw : ∀ j ∈ range k, dyadicWeight s k * dyadicWeight (-θ) (k - j) =
      dyadicWeight (-(θ - s)) k * dyadicWeight (θ - s) j * dyadicWeight s j := fun j hj => by
    rw [ENNReal.dyadicWeight_mul_dyadicWeight_neg_sub s θ (Finset.mem_range.1 hj).le, mul_assoc,
      ← ENNReal.dyadicWeight_add, sub_add_cancel]
  have hw0 : dyadicWeight s k * dyadicWeight (-θ) k = dyadicWeight (-(θ - s)) k := by
    rw [← ENNReal.dyadicWeight_add]; congr 1; ring
  calc dyadicWeight s k * M.modulus f k
      ≤ dyadicWeight s k * (M.C0 * (A.approxError f (2 ^ k) + t k) +
          M.CB * dyadicWeight (-θ) k * (3 * ‖f‖ₑ) + ∑ j ∈ range k,
            M.CB * (2 * dyadicWeight θ 2) * (dyadicWeight (-θ) (k - j) *
              (A.approxError f (2 ^ j) + t j))) := by
        gcongr
        exact M.modulus_le_of_dyadicApprox hθ D ht ht0 k
    _ = M.C0 * (dyadicWeight s k * (A.approxError f (2 ^ k) + t k)) +
          M.CB * 3 * ‖f‖ₑ * (dyadicWeight s k * dyadicWeight (-θ) k) +
          M.CB * (2 * dyadicWeight θ 2) * ∑ j ∈ range k,
            (dyadicWeight s k * dyadicWeight (-θ) (k - j)) *
              (A.approxError f (2 ^ j) + t j) := by
        simp only [mul_add, Finset.mul_sum]; ring_nf
    _ ≤ _ := by
        rw [hw0, Finset.sum_congr rfl fun j hj => by rw [hw j hj]]
        have hsum : ∑ j ∈ range k, dyadicWeight (-(θ - s)) k * dyadicWeight (θ - s) j *
            dyadicWeight s j * (A.approxError f (2 ^ j) + t j) =
              dyadicWeight (-(θ - s)) k * ∑ j ∈ range k, dyadicWeight (θ - s) j *
                (dyadicWeight s j * (A.approxError f (2 ^ j) + t j)) := by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun j _ => ?_
          ring
        rw [hsum]
        exact add_le_add le_rfl (mul_le_mul_right (mul_le_mul_right
          (Finset.sum_le_sum_of_subset (Finset.range_mono (Nat.le_succ k))) _) _)

/-- **The inverse direction**: for `0 ≤ s < θ`, `‖f‖^ω_{s,q} ≤ K ‖f‖_{A^s_q}` with
`K = M.inverseConst s`. -/
theorem modNorm_le_approxNormDyadic (hq : 1 ≤ q) (hs : 0 ≤ s) (hsθ : s < θ) (f : X) :
    M.modNorm s q f ≤ M.inverseConst s * A.approxNormDyadic s q f := by
  have hθ : 0 ≤ θ := hs.trans hsθ.le
  rcases eq_or_ne f 0 with rfl | hf0
  · simp [modNorm, M.modulus_zero]
  set t := tolerance f s
  obtain ⟨D⟩ := A.exists_dyadicApprox f (fun k => tolerance_ne_zero hf0 s k)
  have ht : Antitone t := tolerance_anti f hs
  set N := A.approxNormDyadic s q f
  set E : ℕ → ℝ≥0∞ := fun k => dyadicWeight s k * (A.approxError f (2 ^ k) + t k)
  have hE : lqNorm q E ≤ N + 2 * ‖f‖ₑ := by
    calc lqNorm q E = lqNorm q (fun k => A.approxSeqDyadic s f k + dyadicWeight s k * t k) := by
          congr 1; funext k; simp only [E, approxSeqDyadic]; ring
      _ ≤ N + 2 * ‖f‖ₑ :=
          (lqNorm_approxSeqDyadic_add_tolerance_le hq f s).trans (add_le_add le_add_self le_rfl)
  -- pointwise bound for one scale
  set α := θ - s
  have hpt : ∀ k, dyadicWeight s k * M.modulus f k ≤
      M.C0 * E k + M.CB * 3 * ‖f‖ₑ * dyadicWeight (-α) k +
        M.CB * (2 * dyadicWeight θ 2) * (dyadicWeight (-α) k *
          ∑ j ∈ range (k + 1), dyadicWeight α j * E j) := fun k =>
    M.dyadicWeight_mul_modulus_le_of_dyadicApprox hθ D ht (tolerance_zero f s) k
  -- the ℓ_q norm
  have hr : (2 : ℝ≥0∞) ^ (-α) < 1 := ENNReal.two_rpow_neg_lt_one (by simp only [α]; linarith)
  have hgeo : lqNorm q (dyadicWeight (-α)) ≤ (1 - (2 : ℝ≥0∞) ^ (-α))⁻¹ :=
    ENNReal.lqNorm_dyadicWeight_neg_le hq α
  have hhardy := ENNReal.hardy_sum_le hq α (fun j => dyadicWeight α j * E j)
  have hcancel : (fun k => dyadicWeight (-α) k * (dyadicWeight α k * E k)) = E := by
    funext k; rw [← mul_assoc, ENNReal.dyadicWeight_neg_mul_self, one_mul]
  rw [hcancel] at hhardy
  have hfN : ‖f‖ₑ ≤ N := enorm_le_approxNormDyadic f
  calc M.modNorm s q f = ‖f‖ₑ + lqNorm q (fun k => dyadicWeight s k * M.modulus f k) := rfl
    _ ≤ ‖f‖ₑ + (M.C0 * lqNorm q E + M.CB * 3 * ‖f‖ₑ * lqNorm q (dyadicWeight (-α)) +
          M.CB * (2 * dyadicWeight θ 2) * lqNorm q (fun k => dyadicWeight (-α) k *
            ∑ j ∈ range (k + 1), dyadicWeight α j * E j)) := by
        gcongr
        refine (ENNReal.lqNorm_mono hpt).trans ?_
        refine (ENNReal.lqNorm_add_le hq _ _).trans ?_
        gcongr
        · refine (ENNReal.lqNorm_add_le hq _ _).trans ?_
          rw [ENNReal.lqNorm_const_mul, ENNReal.lqNorm_const_mul]
        · rw [ENNReal.lqNorm_const_mul]
    _ ≤ N + (M.C0 * (N + 2 * N) + M.CB * 3 * N * (1 - (2 : ℝ≥0∞) ^ (-α))⁻¹ +
          M.CB * (2 * dyadicWeight θ 2) * ((1 - (2 : ℝ≥0∞) ^ (-α))⁻¹ * (N + 2 * N))) := by
        gcongr
        · exact hE.trans (by gcongr)
        · exact hhardy.trans (by gcongr; exact hE.trans (by gcongr))
    _ = (1 + 3 * M.C0 + M.CB * (3 + 6 * dyadicWeight θ 2) * (1 - (2 : ℝ≥0∞) ^ (-α))⁻¹) * N := by
        ring
    _ = M.inverseConst s * N := rfl

/-- **The coincidence theorem**: for `0 ≤ s < θ` and `1 ≤ q ≤ ∞`, `f ∈ A^s_q` iff the classical
quasi-norm `‖f‖ + ‖(2^(ks) ω(f, 2^(-k)))_k‖_{ℓ_q}` is finite. -/
theorem memApprox_iff_modNorm_lt_top (hq : 1 ≤ q) (hs : 0 ≤ s) (hsθ : s < θ) (f : X) :
    A.MemApprox s q f ↔ M.modNorm s q f < ∞ := by
  rw [memApprox_iff_approxNormDyadic_lt_top hq hs]
  constructor
  · intro h
    exact (M.modNorm_le_approxNormDyadic hq hs hsθ f).trans_lt
      (ENNReal.mul_lt_top (M.inverseConst_ne_top hsθ).lt_top h)
  · intro h
    exact (M.approxNormDyadic_le_modNorm hq f).trans_lt
      (ENNReal.mul_lt_top (M.directConst_ne_top s).lt_top h)

/-! ### Interpolation of the classical spaces -/

variable {s₀ s₁ η : ℝ} {q₀ q₁ : ℝ≥0∞}

/-- The **couple of two classical spaces** of a modulus `ω` compatible with the scheme: the
classical quasi-norms `‖f‖ + ‖(2^(ks_i) ω(f, 2^(-k)))_k‖_{ℓ_{q_i}}`, `i = 0, 1`. -/
noncomputable def modCouple (s₀ : ℝ) (q₀ : ℝ≥0∞) (s₁ : ℝ) (q₁ : ℝ≥0∞) : InterpCouple X :=
  ⟨M.modNorm s₀ q₀, M.modNorm s₁ q₁⟩

/-- The first norm of the couple of two classical spaces is the classical quasi-norm of
smoothness `s₀`. -/
@[simp]
theorem modCouple_norm0 (f : X) : (M.modCouple s₀ q₀ s₁ q₁).norm0 f = M.modNorm s₀ q₀ f := rfl

/-- The second norm of the couple of two classical spaces is the classical quasi-norm of
smoothness `s₁`. -/
@[simp]
theorem modCouple_norm1 (f : X) : (M.modCouple s₀ q₀ s₁ q₁).norm1 f = M.modNorm s₁ q₁ f := rfl

/-- The **couple of `X` and a classical space** of a modulus `ω` compatible with the scheme: the
norm `‖f‖` of `X` and the classical quasi-norm `‖f‖ + ‖(2^(ks₁) ω(f, 2^(-k)))_k‖_{ℓ_{q₁}}`. -/
noncomputable def leftModCouple (s₁ : ℝ) (q₁ : ℝ≥0∞) : InterpCouple X :=
  ⟨fun f => ‖f‖ₑ, M.modNorm s₁ q₁⟩

/-- The first norm of the couple of `X` and a classical space is the norm of `X`. -/
@[simp]
theorem leftModCouple_norm0 (f : X) : (M.leftModCouple s₁ q₁).norm0 f = ‖f‖ₑ := rfl

/-- The second norm of the couple of `X` and a classical space is the classical quasi-norm. -/
@[simp]
theorem leftModCouple_norm1 (f : X) : (M.leftModCouple s₁ q₁).norm1 f = M.modNorm s₁ q₁ f := rfl

/-- **Classical spaces interpolate to approximation spaces**: for a modulus compatible with the
scheme of inverse order `θ`, `0 < s₀ < s₁ < θ`, `0 < η < 1` and `1 ≤ q₀, q₁, q ≤ ∞`, the real
interpolation space of the couple of the classical spaces of smoothness `s₀` and `s₁` is
`A^{(1-η)s₀+ηs₁}_q`.  The classical quasi-norms are equivalent to the dyadic quasi-norms
(`approxNormDyadic_le_modNorm`, `modNorm_le_approxNormDyadic`), so the sandwich principle
applies (`memKMethod_iff_memApprox_of_two_sandwiches`). -/
theorem memKMethod_modCouple_iff_memApprox (hs₀ : 0 < s₀) (hs : s₀ < s₁) (hs₁ : s₁ < θ)
    (hη : 0 < η) (hη' : η < 1) (hq₀ : 1 ≤ q₀) (hq₁ : 1 ≤ q₁) (hq : 1 ≤ q) {f : X} :
    (M.modCouple s₀ q₀ s₁ q₁).MemKMethod η q f ↔ A.MemApprox ((1 - η) * s₀ + η * s₁) q f :=
  memKMethod_iff_memApprox_of_two_sandwiches (M.inverseConst_ne_top (hs.trans hs₁))
    (M.directConst_ne_top s₀) (M.inverseConst_ne_top hs₁) (M.directConst_ne_top s₁) hq₀ hq₀ hq₁
    hq₁ hs₀ hs hη hη' hq (M.modNorm_le_approxNormDyadic hq₀ hs₀.le (hs.trans hs₁))
    (M.approxNormDyadic_le_modNorm hq₀)
    (M.modNorm_le_approxNormDyadic hq₁ (hs₀.trans hs).le hs₁) (M.approxNormDyadic_le_modNorm hq₁)

/-- **The interpolation spaces of two classical spaces**: for a modulus compatible with the
scheme of inverse order `θ`, `0 < s₀ < s₁ < θ`, `0 < η < 1` and `1 ≤ q₀, q₁, q ≤ ∞`, `f` lies in
the real interpolation space of the couple of the classical spaces of smoothness `s₀` and `s₁`
iff `‖f‖ + ‖(2^(ks) ω(f, 2^(-k)))_k‖_{ℓ_q} < ∞` with `s = (1-η)s₀ + ηs₁`. -/
theorem memKMethod_modCouple_iff (hs₀ : 0 < s₀) (hs : s₀ < s₁) (hs₁ : s₁ < θ) (hη : 0 < η)
    (hη' : η < 1) (hq₀ : 1 ≤ q₀) (hq₁ : 1 ≤ q₁) (hq : 1 ≤ q) {f : X} :
    (M.modCouple s₀ q₀ s₁ q₁).MemKMethod η q f ↔
      M.modNorm ((1 - η) * s₀ + η * s₁) q f < ∞ := by
  rw [M.memKMethod_modCouple_iff_memApprox hs₀ hs hs₁ hη hη' hq₀ hq₁ hq]
  exact M.memApprox_iff_modNorm_lt_top hq (reiterationExponent_pos hs₀ hs hη hη').le
    (reiterationExponent_lt hs hs₁ hη') f

/-- **`X` and a classical space interpolate to approximation spaces**: for a modulus compatible
with the scheme of inverse order `θ`, `0 < s₁ < θ`, `0 < η < 1` and `1 ≤ q₁, q ≤ ∞`, the real
interpolation space of the couple of `X` and the classical space of smoothness `s₁` is
`A^{ηs₁}_q` (`memKMethod_iff_memApprox_of_sandwich`). -/
theorem memKMethod_leftModCouple_iff_memApprox (hs₁ : 0 < s₁) (hs₁θ : s₁ < θ) (hη : 0 < η)
    (hη' : η < 1) (hq₁ : 1 ≤ q₁) (hq : 1 ≤ q) {f : X} :
    (M.leftModCouple s₁ q₁).MemKMethod η q f ↔ A.MemApprox (η * s₁) q f :=
  memKMethod_iff_memApprox_of_sandwich (M.inverseConst_ne_top hs₁θ) (M.directConst_ne_top s₁)
    hq₁ hq₁ hs₁ hη hη' hq (M.modNorm_le_approxNormDyadic hq₁ hs₁.le hs₁θ)
    (M.approxNormDyadic_le_modNorm hq₁)

/-- **The interpolation spaces of `X` and a classical space**: for a modulus compatible with the
scheme of inverse order `θ`, `0 < s₁ < θ`, `0 < η < 1` and `1 ≤ q₁, q ≤ ∞`, `f` lies in the real
interpolation space of the couple of `X` and the classical space of smoothness `s₁` iff
`‖f‖ + ‖(2^(kηs₁) ω(f, 2^(-k)))_k‖_{ℓ_q} < ∞`. -/
theorem memKMethod_leftModCouple_iff (hs₁ : 0 < s₁) (hs₁θ : s₁ < θ) (hη : 0 < η) (hη' : η < 1)
    (hq₁ : 1 ≤ q₁) (hq : 1 ≤ q) {f : X} :
    (M.leftModCouple s₁ q₁).MemKMethod η q f ↔ M.modNorm (η * s₁) q f < ∞ := by
  have hlt : η * s₁ < θ := by nlinarith
  rw [M.memKMethod_leftModCouple_iff_memApprox hs₁ hs₁θ hη hη' hq₁ hq]
  exact M.memApprox_iff_modNorm_lt_top hq (mul_pos hη hs₁).le hlt f

end ModulusData

end ApproximationScheme
