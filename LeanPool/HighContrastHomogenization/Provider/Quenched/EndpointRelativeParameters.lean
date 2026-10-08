/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.Quenched.RenormalizationParameterArithmetic

/-!
# High-contrast homogenization: Provider.Quenched.EndpointRelativeParameters

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# Arithmetic of endpoint-relative renormalization windows

The window index is the quotient of the endpoint-relative generation by a
fixed stride.  Both the recent window and the separation from its annealed
reference therefore grow linearly, while the reference generation itself
continues to move to infinity.
-/

namespace HCPolySupport.HighContrast.Quenched

noncomputable section

/-- Quotient index of the growing endpoint-relative window. -/
@[expose]
def endpointWindowIndex (L n : ℕ) : ℕ := n / L

/-- Recent-window length at generation `n`. -/
@[expose]
def endpointWindowLength (A L n : ℕ) : ℕ :=
  A * endpointWindowIndex L n

/-- Distance from generation `n` to its annealed reference generation. -/
@[expose]
def endpointReferenceOffset (A D L n : ℕ) : ℕ :=
  (A + D) * endpointWindowIndex L n

/-- Generation-dependent additive tolerance. -/
@[expose]
def endpointTolerance (delta eta : ℝ) (q0 L n : ℕ) : ℝ :=
  delta * (3 : ℝ) ^ (-eta * ((endpointWindowIndex L n - q0 : ℕ) : ℝ))

theorem endpointWindowIndex_mul_stride (L q : ℕ) (hL : 0 < L) :
    endpointWindowIndex L (L * q) = q := by
  rw [endpointWindowIndex, Nat.mul_comm, Nat.mul_div_left _ hL]

theorem endpointWindowIndex_mono {L q0 n : ℕ} (hL : 0 < L)
    (hn : L * q0 ≤ n) :
    q0 ≤ endpointWindowIndex L n := by
  rw [endpointWindowIndex]
  exact (Nat.le_div_iff_mul_le hL).2 (by simpa only [Nat.mul_comm] using hn)

theorem endpointReferenceOffset_le {A D L n : ℕ}
    (hL : L = A + D + 1) :
    endpointReferenceOffset A D L n ≤ n := by
  have hmul := Nat.div_mul_le_self n L
  rw [Nat.mul_comm] at hmul
  dsimp only [endpointReferenceOffset, endpointWindowIndex]
  have hcoef : A + D ≤ L := by omega
  exact (Nat.mul_le_mul_right (n / L) hcoef).trans hmul

theorem endpointWindowLength_le_referenceOffset (A D L n : ℕ) :
    endpointWindowLength A L n ≤ endpointReferenceOffset A D L n := by
  dsimp only [endpointWindowLength, endpointReferenceOffset]
  exact Nat.mul_le_mul_right _ (Nat.le_add_right A D)

theorem endpoint_reference_generation_ge_index {A D L n : ℕ}
    (hL : L = A + D + 1) :
    endpointWindowIndex L n ≤ n - endpointReferenceOffset A D L n := by
  have hmul := Nat.div_mul_le_self n L
  rw [Nat.mul_comm] at hmul
  have hsum : endpointReferenceOffset A D L n + endpointWindowIndex L n =
      L * endpointWindowIndex L n := by
    dsimp only [endpointReferenceOffset]
    rw [hL]
    ring
  rw [Nat.le_sub_iff_add_le (endpointReferenceOffset_le hL), Nat.add_comm, hsum]
  simpa only [endpointWindowIndex] using hmul

/-- Quotient growth loses at most one stride. -/
theorem endpointWindowIndex_sub_lower {L q0 n : ℕ} (hL : 0 < L)
    (hn : L * q0 ≤ n) :
    ((n : ℝ) - ((L * q0 : ℕ) : ℝ)) / (L : ℝ) - 1 <
      ((endpointWindowIndex L n - q0 : ℕ) : ℝ) := by
  have hupper : n < L * (n / L + 1) := Nat.lt_mul_div_succ n hL
  have hq0 : q0 ≤ n / L := (Nat.le_div_iff_mul_le hL).2
    (by simpa only [Nat.mul_comm] using hn)
  have hcast : ((endpointWindowIndex L n - q0 : ℕ) : ℝ) =
      ((n / L : ℕ) : ℝ) - (q0 : ℝ) := by
    dsimp only [endpointWindowIndex]
    rw [Nat.cast_sub hq0]
  have hLR : 0 < (L : ℝ) := by exact_mod_cast hL
  rw [hcast]
  have hu : (n : ℝ) < (L : ℝ) * ((n / L : ℕ) : ℝ) + (L : ℝ) := by
    exact_mod_cast hupper
  have hprod : (((L * q0 : ℕ) : ℝ)) = (L : ℝ) * (q0 : ℝ) := by
    push_cast
    ring
  rw [hprod]
  have hdiv : (n : ℝ) / (L : ℝ) - 1 < ((n / L : ℕ) : ℝ) := by
    apply (sub_lt_iff_lt_add).2
    apply (div_lt_iff₀ hLR).2
    nlinarith only [hu]
  calc
    ((n : ℝ) - (L : ℝ) * (q0 : ℝ)) / (L : ℝ) - 1 =
        (n : ℝ) / (L : ℝ) - 1 - (q0 : ℝ) := by
      field_simp
      ring
    _ < ((n / L : ℕ) : ℝ) - (q0 : ℝ) := sub_lt_sub_right hdiv _

theorem endpointTolerance_pos {delta eta : ℝ} {q0 L n : ℕ}
    (hdelta : 0 < delta) :
    0 < endpointTolerance delta eta q0 L n := by
  dsimp only [endpointTolerance]
  positivity

theorem endpointTolerance_le_delta {delta eta : ℝ} {q0 L n : ℕ}
    (hdelta : 0 ≤ delta) (heta : 0 ≤ eta) :
    endpointTolerance delta eta q0 L n ≤ delta := by
  dsimp only [endpointTolerance]
  have hexp : -eta * ((endpointWindowIndex L n - q0 : ℕ) : ℝ) ≤ 0 := by
    exact mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr heta) (Nat.cast_nonneg _)
  have hp : (3 : ℝ) ^ (-eta *
      ((endpointWindowIndex L n - q0 : ℕ) : ℝ)) ≤ 1 := by
    simpa only [Real.rpow_zero] using
      Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 3) hexp
  simpa only [mul_one] using mul_le_mul_of_nonneg_left hp hdelta

/-- Quotient decay implies decay in the physical generation, with one fixed
factor lost to integer rounding. -/
theorem endpointTolerance_le_generation_decay
    {delta eta : ℝ} {q0 L n : ℕ}
    (hdelta : 0 ≤ delta) (heta : 0 < eta) (hL : 0 < L)
    (hn : L * q0 ≤ n) :
    endpointTolerance delta eta q0 L n ≤
      (3 : ℝ) ^ eta * delta *
        (3 : ℝ) ^ (-(eta / (L : ℝ)) *
          ((n : ℝ) - ((L * q0 : ℕ) : ℝ))) := by
  have hidx := endpointWindowIndex_sub_lower hL hn
  have hLR : 0 < (L : ℝ) := by exact_mod_cast hL
  have hexp : -eta * ((endpointWindowIndex L n - q0 : ℕ) : ℝ) ≤
      eta - eta / (L : ℝ) *
        ((n : ℝ) - ((L * q0 : ℕ) : ℝ)) := by
    have hm := mul_lt_mul_of_neg_left hidx (by linarith only [heta] : -eta < 0)
    apply le_of_lt
    convert hm using 1
    all_goals (field_simp; ring)
  have hp := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 3) hexp
  dsimp only [endpointTolerance]
  calc
    delta * (3 : ℝ) ^
          (-eta * ((endpointWindowIndex L n - q0 : ℕ) : ℝ))
        ≤ delta * (3 : ℝ) ^
          (eta - eta / (L : ℝ) *
            ((n : ℝ) - ((L * q0 : ℕ) : ℝ))) :=
      mul_le_mul_of_nonneg_left hp hdelta
    _ = (3 : ℝ) ^ eta * delta *
        (3 : ℝ) ^ (-(eta / (L : ℝ)) *
          ((n : ℝ) - ((L * q0 : ℕ) : ℝ))) := by
      rw [show eta - eta / (L : ℝ) *
          ((n : ℝ) - ((L * q0 : ℕ) : ℝ)) =
        eta + (-(eta / (L : ℝ)) *
          ((n : ℝ) - ((L * q0 : ℕ) : ℝ))) by ring,
        Real.rpow_add (by norm_num : (0 : ℝ) < 3)]
      ring

/-- Annealed decay at the moving reference generation is absorbed by the
generation-dependent tolerance. -/
theorem annealed_error_le_endpointTolerance
    {delta eta alpha : ℝ} {q0 A D L n : ℕ}
    (hdelta : 0 ≤ delta) (heta : 0 ≤ eta) (hetaAlpha : eta ≤ alpha)
    (hL : L = A + D + 1) (hn : L * q0 ≤ n)
    (hstart : 6 * (3 : ℝ) ^ (-alpha * (q0 : ℝ)) ≤ delta) :
    6 * (3 : ℝ) ^
        (-alpha * ((n - endpointReferenceOffset A D L n : ℕ) : ℝ)) ≤
      endpointTolerance delta eta q0 L n := by
  have hLpos : 0 < L := by rw [hL]; omega
  have hq0 : q0 ≤ endpointWindowIndex L n := endpointWindowIndex_mono hLpos hn
  have href : endpointWindowIndex L n ≤
      n - endpointReferenceOffset A D L n := endpoint_reference_generation_ge_index hL
  have hmonoRef : (3 : ℝ) ^
      (-alpha * ((n - endpointReferenceOffset A D L n : ℕ) : ℝ)) ≤
      (3 : ℝ) ^ (-alpha * (endpointWindowIndex L n : ℝ)) := by
    apply Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 3)
    have halpha : 0 ≤ alpha := heta.trans hetaAlpha
    exact mul_le_mul_of_nonpos_left (by exact_mod_cast href) (neg_nonpos.mpr halpha)
  have hsplit : (3 : ℝ) ^ (-alpha * (endpointWindowIndex L n : ℝ)) =
      (3 : ℝ) ^ (-alpha * (q0 : ℝ)) *
        (3 : ℝ) ^ (-alpha *
          ((endpointWindowIndex L n - q0 : ℕ) : ℝ)) := by
    rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 3)]
    congr 1
    rw [Nat.cast_sub hq0]
    ring
  have hdecay : (3 : ℝ) ^ (-alpha *
      ((endpointWindowIndex L n - q0 : ℕ) : ℝ)) ≤
      (3 : ℝ) ^ (-eta *
        ((endpointWindowIndex L n - q0 : ℕ) : ℝ)) := by
    apply Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 3)
    exact mul_le_mul_of_nonneg_right (neg_le_neg hetaAlpha) (Nat.cast_nonneg _)
  dsimp only [endpointTolerance]
  calc
    6 * (3 : ℝ) ^
        (-alpha * ((n - endpointReferenceOffset A D L n : ℕ) : ℝ))
        ≤ 6 * (3 : ℝ) ^ (-alpha * (endpointWindowIndex L n : ℝ)) :=
      mul_le_mul_of_nonneg_left hmonoRef (by norm_num)
    _ = (6 * (3 : ℝ) ^ (-alpha * (q0 : ℝ))) *
        (3 : ℝ) ^ (-alpha *
          ((endpointWindowIndex L n - q0 : ℕ) : ℝ)) := by rw [hsplit]; ring
    _ ≤ delta * (3 : ℝ) ^ (-alpha *
          ((endpointWindowIndex L n - q0 : ℕ) : ℝ)) :=
      mul_le_mul_of_nonneg_right hstart (Real.rpow_nonneg (by norm_num) _)
    _ ≤ delta * (3 : ℝ) ^ (-eta *
          ((endpointWindowIndex L n - q0 : ℕ) : ℝ)) :=
      mul_le_mul_of_nonneg_left hdecay hdelta

/-- An old-cell calibration at the first family index propagates through the
growing window. -/
theorem old_cell_burn_le_endpointTolerance
    {C delta eta gap : ℝ} {q0 A L n : ℕ}
    (hdelta : 0 ≤ delta)
    (hetaGap : eta ≤ gap * (A : ℝ))
    (hL : 0 < L) (hn : L * q0 ≤ n)
    (hstart : C ≤ delta * (3 : ℝ) ^ (gap * (A * q0 : ℕ))) :
    C ≤ endpointTolerance delta eta q0 L n *
      (3 : ℝ) ^ (gap * (endpointWindowLength A L n : ℝ)) := by
  have hq0 : q0 ≤ endpointWindowIndex L n := endpointWindowIndex_mono hL hn
  let j : ℕ := endpointWindowIndex L n - q0
  have hidx : endpointWindowIndex L n = q0 + j := by
    dsimp only [j]
    omega
  have hgrowth : 1 ≤ (3 : ℝ) ^
      ((gap * (A : ℝ) - eta) * (j : ℝ)) :=
    Real.one_le_rpow (by norm_num)
      (mul_nonneg (sub_nonneg.mpr hetaGap) (Nat.cast_nonneg j))
  have hfactor : endpointTolerance delta eta q0 L n *
      (3 : ℝ) ^ (gap * (endpointWindowLength A L n : ℝ)) =
      (delta * (3 : ℝ) ^ (gap * (A * q0 : ℕ))) *
        (3 : ℝ) ^ ((gap * (A : ℝ) - eta) * (j : ℝ)) := by
    dsimp only [endpointTolerance, endpointWindowLength]
    rw [show endpointWindowIndex L n - q0 = j by rfl, hidx]
    have hexp : -eta * (j : ℝ) + gap * ((A * (q0 + j) : ℕ) : ℝ) =
        gap * ((A * q0 : ℕ) : ℝ) +
          (gap * (A : ℝ) - eta) * (j : ℝ) := by
      push_cast
      ring
    calc
      delta * (3 : ℝ) ^ (-eta * (j : ℝ)) *
          (3 : ℝ) ^ (gap * ((A * (q0 + j) : ℕ) : ℝ)) =
          delta * ((3 : ℝ) ^ (-eta * (j : ℝ)) *
            (3 : ℝ) ^ (gap * ((A * (q0 + j) : ℕ) : ℝ))) := by ring
      _ = delta * (3 : ℝ) ^ (-eta * (j : ℝ) +
            gap * ((A * (q0 + j) : ℕ) : ℝ)) := by
          rw [Real.rpow_add (by norm_num : (0 : ℝ) < 3)]
      _ = delta * (3 : ℝ) ^ (gap * ((A * q0 : ℕ) : ℝ) +
            (gap * (A : ℝ) - eta) * (j : ℝ)) := by rw [hexp]
      _ = delta * ((3 : ℝ) ^ (gap * ((A * q0 : ℕ) : ℝ)) *
            (3 : ℝ) ^ ((gap * (A : ℝ) - eta) * (j : ℝ))) := by
          rw [Real.rpow_add (by norm_num : (0 : ℝ) < 3)]
      _ = (delta * (3 : ℝ) ^ (gap * ((A * q0 : ℕ) : ℝ))) *
            (3 : ℝ) ^ ((gap * (A : ℝ) - eta) * (j : ℝ)) := by ring
  rw [hfactor]
  exact hstart.trans (by
    simpa only [mul_one] using mul_le_mul_of_nonneg_left hgrowth
      (mul_nonneg hdelta (Real.rpow_nonneg (by norm_num) _)))

/-- The renormalization base is monotone along the growing family once its
separation exponent dominates the tolerance decay. -/
theorem renormBase_endpointTolerance_mono
    {g nu mu Gain delta eta : ℝ} {q0 A D L n : ℕ}
    (hdelta : 0 ≤ delta) (hGain : 0 < Gain)
    (hetaD : eta ≤ mu * (D : ℝ))
    (hL : 0 < L) (hn : L * q0 ≤ n) :
    renormBase g nu mu delta Gain (D * q0) 0 ≤
      renormBase g nu mu (endpointTolerance delta eta q0 L n) Gain
        (endpointReferenceOffset A D L n) (endpointWindowLength A L n) := by
  have hq0 : q0 ≤ endpointWindowIndex L n := endpointWindowIndex_mono hL hn
  let j : ℕ := endpointWindowIndex L n - q0
  have hidx : endpointWindowIndex L n = q0 + j := by dsimp only [j]; omega
  have hfac : 1 ≤ (3 : ℝ) ^ ((mu * (D : ℝ) - eta) * (j : ℝ)) :=
    Real.one_le_rpow (by norm_num)
      (mul_nonneg (sub_nonneg.mpr hetaD) (Nat.cast_nonneg j))
  have hLHS : renormBase g nu mu delta Gain (D * q0) 0 =
      Gain⁻¹ * delta * (3 : ℝ) ^ ((g - nu) + mu * (D * q0 : ℕ)) := by
    rw [renormBase]; norm_num
  have hleft : 0 ≤ Gain⁻¹ * delta *
      (3 : ℝ) ^ ((g - nu) + mu * (D * q0 : ℕ)) := by positivity
  have hfactor : renormBase g nu mu (endpointTolerance delta eta q0 L n) Gain
      (endpointReferenceOffset A D L n) (endpointWindowLength A L n) =
      (Gain⁻¹ * delta * (3 : ℝ) ^ ((g - nu) + mu * (D * q0 : ℕ))) *
        (3 : ℝ) ^ ((mu * (D : ℝ) - eta) * (j : ℝ)) := by
    rw [renormBase]
    dsimp only [endpointTolerance, endpointReferenceOffset, endpointWindowLength]
    rw [show endpointWindowIndex L n - q0 = j by rfl, hidx]
    have hexp : -eta * (j : ℝ) +
        ((g - nu) + mu *
          ((((A + D) * (q0 + j) : ℕ) : ℝ) -
            ((A * (q0 + j) : ℕ) : ℝ))) =
        ((g - nu) + mu * ((D * q0 : ℕ) : ℝ)) +
          (mu * (D : ℝ) - eta) * (j : ℝ) := by
      push_cast
      ring
    calc
      Gain⁻¹ * (delta * (3 : ℝ) ^ (-eta * (j : ℝ))) *
          (3 : ℝ) ^ ((g - nu) + mu *
            ((((A + D) * (q0 + j) : ℕ) : ℝ) -
              ((A * (q0 + j) : ℕ) : ℝ))) =
          (Gain⁻¹ * delta) * ((3 : ℝ) ^ (-eta * (j : ℝ)) *
            (3 : ℝ) ^ ((g - nu) + mu *
              ((((A + D) * (q0 + j) : ℕ) : ℝ) -
                ((A * (q0 + j) : ℕ) : ℝ)))) := by ac_rfl
      _ = (Gain⁻¹ * delta) * (3 : ℝ) ^
          (-eta * (j : ℝ) + ((g - nu) + mu *
            ((((A + D) * (q0 + j) : ℕ) : ℝ) -
              ((A * (q0 + j) : ℕ) : ℝ)))) := by
          rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 3)]
      _ = (Gain⁻¹ * delta) * (3 : ℝ) ^
          (((g - nu) + mu * ((D * q0 : ℕ) : ℝ)) +
            (mu * (D : ℝ) - eta) * (j : ℝ)) := by rw [hexp]
      _ = (Gain⁻¹ * delta) *
          ((3 : ℝ) ^ ((g - nu) + mu * ((D * q0 : ℕ) : ℝ)) *
            (3 : ℝ) ^ ((mu * (D : ℝ) - eta) * (j : ℝ))) := by
          rw [Real.rpow_add (by norm_num : (0 : ℝ) < 3)]
      _ = Gain⁻¹ * delta *
          (3 : ℝ) ^ ((g - nu) + mu * ((D * q0 : ℕ) : ℝ)) *
            (3 : ℝ) ^ ((mu * (D : ℝ) - eta) * (j : ℝ)) := by ac_rfl
  rw [hLHS, hfactor]
  exact le_mul_of_one_le_right hleft hfac

/-- Once the net separation exponent is at least one, the moving
renormalization base gains at least one factor of three per quotient step. -/
theorem rpow_index_growth_le_renormBase_endpoint
    {g nu mu Gain delta eta : ℝ} {q0 A D L n : ℕ}
    (hnet : 1 ≤ mu * (D : ℝ) - eta)
    (hL : 0 < L) (hn : L * q0 ≤ n)
    (hbase : 1 ≤ renormBase g nu mu delta Gain (D * q0) 0) :
    (3 : ℝ) ^ ((endpointWindowIndex L n - q0 : ℕ) : ℝ) ≤
      renormBase g nu mu (endpointTolerance delta eta q0 L n) Gain
        (endpointReferenceOffset A D L n) (endpointWindowLength A L n) := by
  have hq0 : q0 ≤ endpointWindowIndex L n := endpointWindowIndex_mono hL hn
  let j : ℕ := endpointWindowIndex L n - q0
  have hidx : endpointWindowIndex L n = q0 + j := by dsimp only [j]; omega
  have hpow : (3 : ℝ) ^ (j : ℝ) ≤
      (3 : ℝ) ^ ((mu * (D : ℝ) - eta) * (j : ℝ)) := by
    apply Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 3)
    have hj : 0 ≤ (j : ℝ) := Nat.cast_nonneg j
    nlinarith only [hnet, hj]
  have hLHS : renormBase g nu mu delta Gain (D * q0) 0 =
      Gain⁻¹ * delta * (3 : ℝ) ^ ((g - nu) + mu * (D * q0 : ℕ)) := by
    rw [renormBase]; norm_num
  have hfactor : renormBase g nu mu (endpointTolerance delta eta q0 L n) Gain
      (endpointReferenceOffset A D L n) (endpointWindowLength A L n) =
      renormBase g nu mu delta Gain (D * q0) 0 *
        (3 : ℝ) ^ ((mu * (D : ℝ) - eta) * (j : ℝ)) := by
    rw [hLHS, renormBase]
    dsimp only [endpointTolerance, endpointReferenceOffset, endpointWindowLength]
    rw [show endpointWindowIndex L n - q0 = j by rfl, hidx]
    have hexp : -eta * (j : ℝ) +
        ((g - nu) + mu *
          ((((A + D) * (q0 + j) : ℕ) : ℝ) -
            ((A * (q0 + j) : ℕ) : ℝ))) =
        ((g - nu) + mu * ((D * q0 : ℕ) : ℝ)) +
          (mu * (D : ℝ) - eta) * (j : ℝ) := by
      push_cast
      ring
    calc
      Gain⁻¹ * (delta * (3 : ℝ) ^ (-eta * (j : ℝ))) *
          (3 : ℝ) ^ ((g - nu) + mu *
            ((((A + D) * (q0 + j) : ℕ) : ℝ) -
              ((A * (q0 + j) : ℕ) : ℝ))) =
          (Gain⁻¹ * delta) * ((3 : ℝ) ^ (-eta * (j : ℝ)) *
            (3 : ℝ) ^ ((g - nu) + mu *
              ((((A + D) * (q0 + j) : ℕ) : ℝ) -
                ((A * (q0 + j) : ℕ) : ℝ)))) := by ac_rfl
      _ = (Gain⁻¹ * delta) * (3 : ℝ) ^
            (-eta * (j : ℝ) + ((g - nu) + mu *
              ((((A + D) * (q0 + j) : ℕ) : ℝ) -
                ((A * (q0 + j) : ℕ) : ℝ)))) := by
            rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 3)]
      _ = (Gain⁻¹ * delta) * (3 : ℝ) ^
          (((g - nu) + mu * ((D * q0 : ℕ) : ℝ)) +
            (mu * (D : ℝ) - eta) * (j : ℝ)) := by rw [hexp]
      _ = Gain⁻¹ * delta *
          (3 : ℝ) ^ ((g - nu) + mu * ((D * q0 : ℕ) : ℝ)) *
            (3 : ℝ) ^ ((mu * (D : ℝ) - eta) * (j : ℝ)) := by
            rw [Real.rpow_add (by norm_num : (0 : ℝ) < 3)]
            ac_rfl
  rw [hfactor, show endpointWindowIndex L n - q0 = j by rfl]
  exact hpow.trans (le_mul_of_one_le_left (Real.rpow_nonneg (by norm_num) _) hbase)

/-- A triadic bracket controls every affine natural generation built from its
index, with the constant tail paid by the lower bound `3 ≤ base`. -/
theorem three_pow_affine_index_le
    {base : ℝ} {q C R : ℕ}
    (hbase : (3 : ℝ) ≤ base)
    (hq : (3 : ℝ) ^ (q : ℤ) ≤ base ^ (4 : ℕ)) :
    (3 : ℝ) ^ (C * q + R) ≤ base ^ ((4 * C + R : ℕ) : ℝ) := by
  have hq' : (3 : ℝ) ^ q ≤ base ^ (4 : ℕ) := by
    simpa only [zpow_natCast] using hq
  have hmain := pow_le_pow_left₀ (by positivity : (0 : ℝ) ≤ (3 : ℝ) ^ q)
    hq' C
  have htail := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 3)
    hbase R
  rw [Nat.mul_comm C q, pow_add, pow_mul]
  have hbasePos : 0 < base := (by norm_num : (0 : ℝ) < 3).trans_le hbase
  calc
    ((3 : ℝ) ^ q) ^ C * (3 : ℝ) ^ R ≤
        (base ^ (4 : ℕ)) ^ C * base ^ R :=
      mul_le_mul hmain htail (by positivity) (by positivity)
    _ = base ^ ((4 * C + R : ℕ) : ℝ) := by
      rw [← pow_mul, ← pow_add, ← Real.rpow_natCast]

private theorem log_renormCellCount_endpoint_le (d A q : ℕ)
    (hA : 1 ≤ A) (hq : 1 ≤ q) :
    Real.log (2 * renormCellCount d (A * q)) ≤
      (2 * (A : ℝ) + (d : ℝ) * (A : ℝ) * Real.log 3) * (q : ℝ) := by
  have hApos : 0 < A := Nat.zero_lt_one.trans_le hA
  have hqpos : 0 < q := Nat.zero_lt_one.trans_le hq
  have htwo : 0 < (2 : ℝ) * ((A * q : ℕ) : ℝ) := by positivity
  have hpow : 0 < (3 : ℝ) ^ (d * (A * q)) := by positivity
  rw [renormCellCount]
  rw [show (2 : ℝ) * (((A * q : ℕ) : ℝ) *
      (3 : ℝ) ^ (d * (A * q))) =
      (2 * ((A * q : ℕ) : ℝ)) * (3 : ℝ) ^ (d * (A * q)) by ring]
  rw [Real.log_mul (ne_of_gt htwo) (ne_of_gt hpow), Real.log_pow]
  have hlog := Real.log_le_sub_one_of_pos htwo
  have hcast : ((d * (A * q) : ℕ) : ℝ) =
      (d : ℝ) * (A : ℝ) * (q : ℝ) := by push_cast; ring
  rw [hcast]
  have hqreal : (1 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq
  have hbound : 2 * ((A * q : ℕ) : ℝ) - 1 ≤
      2 * (A : ℝ) * (q : ℝ) := by
    push_cast
    linarith only [hqreal]
  calc
    Real.log (2 * ((A * q : ℕ) : ℝ)) +
        (d : ℝ) * (A : ℝ) * (q : ℝ) * Real.log 3 ≤
      2 * (A : ℝ) * (q : ℝ) +
        (d : ℝ) * (A : ℝ) * (q : ℝ) * Real.log 3 := by
          linarith only [hlog, hbound]
    _ = (2 * (A : ℝ) + (d : ℝ) * (A : ℝ) * Real.log 3) *
        (q : ℝ) := by ring

private theorem one_add_mul_le_rpow_nat_endpoint {nu : ℝ}
    (hnu : 0 ≤ nu) (j : ℕ) :
    1 + (j : ℝ) * ((3 : ℝ) ^ nu - 1) ≤
      (3 : ℝ) ^ (nu * (j : ℝ)) := by
  have hpow : (3 : ℝ) ^ (nu * (j : ℝ)) = ((3 : ℝ) ^ nu) ^ j := by
    rw [Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 3), Real.rpow_natCast]
  have hone : (1 : ℝ) ≤ (3 : ℝ) ^ nu := by
    simpa only [← Real.rpow_zero (3 : ℝ)] using
      Real.rpow_le_rpow_of_exponent_le (by norm_num) hnu
  have hbern := one_add_mul_le_pow (a := (3 : ℝ) ^ nu - 1)
    (by linarith only [hone]) j
  have hbaseeq : 1 + ((3 : ℝ) ^ nu - 1) = (3 : ℝ) ^ nu := by ring
  rw [hbaseeq] at hbern
  rw [hpow]
  exact hbern

private theorem nat_add_one_le_nine_pow (j : ℕ) :
    (j : ℝ) + 1 ≤ (3 : ℝ) ^ (2 * (j : ℝ)) := by
  have hbern := one_add_mul_le_rpow_nat_endpoint (nu := (2 : ℝ))
    (by norm_num) j
  have hbase : (j : ℝ) + 1 ≤ 1 + (j : ℝ) * ((3 : ℝ) ^ (2 : ℝ) - 1) := by
    rw [show (3 : ℝ) ^ (2 : ℝ) = 9 by norm_num]
    have hj : 0 ≤ (j : ℝ) := Nat.cast_nonneg j
    linarith only [hj]
  exact hbase.trans (by simpa only [mul_comm] using hbern)

/-- The increasing renormalization base absorbs the cell count of every later
window while the radius tail keeps one fixed buffer. -/
theorem endpoint_varying_radius_buffer
    {d A B q0 q : ℕ} {mu baseNow : ℝ}
    (hA : 1 ≤ A) (hq0 : 1 ≤ q0) (hq : q0 ≤ q)
    (hmu : 0 < mu) (hB : 1 ≤ B)
    (hBbase :
      (2 * (A : ℝ) + (d : ℝ) * (A : ℝ) * Real.log 3) /
          frGaugeConst d + 1 ≤ (3 : ℝ) ^ (2 * mu * (B : ℝ)))
    (hbaseGrowth : (3 : ℝ) ^ ((q : ℝ) - (q0 : ℝ)) ≤ baseNow) :
    Real.log (2 * renormCellCount d (A * q)) ≤
      frGaugeConst d *
        (baseNow ^ 2 * (3 : ℝ) ^ (2 * mu * ((B * q0 : ℕ) : ℝ)) - 1) := by
  let C : ℝ := 2 * (A : ℝ) + (d : ℝ) * (A : ℝ) * Real.log 3
  let X : ℝ := (3 : ℝ) ^ (2 * mu * ((B * q0 : ℕ) : ℝ))
  let j : ℕ := q - q0
  have hqeq : q = q0 + j := by dsimp only [j]; omega
  have hcfr : 0 < frGaugeConst d := frGaugeConst_pos d
  have hC0 : 0 ≤ C := by
    dsimp only [C]
    have hlog : 0 ≤ Real.log 3 := Real.log_nonneg (by norm_num)
    positivity
  have hbase : C ≤ frGaugeConst d *
      ((3 : ℝ) ^ (2 * mu * (B : ℝ)) - 1) := by
    change C / frGaugeConst d + 1 ≤
      (3 : ℝ) ^ (2 * mu * (B : ℝ)) at hBbase
    have hmul := mul_le_mul_of_nonneg_left hBbase hcfr.le
    rw [mul_add, mul_div_cancel₀ _ hcfr.ne', mul_one] at hmul
    linarith only [hmul]
  have hlinear0 : C * (q0 : ℝ) ≤ frGaugeConst d * (X - 1) := by
    have hnu : 0 ≤ 2 * mu * (B : ℝ) := by positivity
    have hbern := one_add_mul_le_rpow_nat_endpoint hnu q0
    have hq0R : 0 ≤ (q0 : ℝ) := Nat.cast_nonneg q0
    have hmul := mul_le_mul_of_nonneg_right hbase hq0R
    have hcast : 2 * mu * ((B * q0 : ℕ) : ℝ) =
        (2 * mu * (B : ℝ)) * (q0 : ℝ) := by push_cast; ring
    dsimp only [X]
    rw [hcast]
    calc
      C * (q0 : ℝ) ≤
          (frGaugeConst d * ((3 : ℝ) ^ (2 * mu * (B : ℝ)) - 1)) *
            (q0 : ℝ) := hmul
      _ = frGaugeConst d *
          ((q0 : ℝ) * ((3 : ℝ) ^ (2 * mu * (B : ℝ)) - 1)) := by ring
      _ ≤ frGaugeConst d *
          ((3 : ℝ) ^ ((2 * mu * (B : ℝ)) * (q0 : ℝ)) - 1) := by
            apply mul_le_mul_of_nonneg_left _ hcfr.le
            linarith only [hbern]
  have hX1 : 1 ≤ X := by
    dsimp only [X]
    exact Real.one_le_rpow (by norm_num) (by positivity)
  have hC : C ≤ frGaugeConst d * (X - 1) := by
    have hqR : 1 ≤ (q0 : ℝ) := by exact_mod_cast hq0
    calc
      C = C * 1 := by ring
      _ ≤ C * (q0 : ℝ) := mul_le_mul_of_nonneg_left hqR hC0
      _ ≤ frGaugeConst d * (X - 1) := hlinear0
  have hlinear : C * (q : ℝ) ≤
      (3 : ℝ) ^ (2 * (j : ℝ)) * (frGaugeConst d * (X - 1)) := by
    rw [hqeq]
    push_cast
    have hsum : C * ((q0 : ℝ) + (j : ℝ)) ≤
        ((j : ℝ) + 1) * (frGaugeConst d * (X - 1)) := by
      have h0 := hlinear0
      have hj := mul_le_mul_of_nonneg_left hC (Nat.cast_nonneg j)
      nlinarith only [h0, hj]
    exact hsum.trans (mul_le_mul_of_nonneg_right (nat_add_one_le_nine_pow j)
      (mul_nonneg hcfr.le (sub_nonneg.mpr hX1)))
  have hbaseSq : (3 : ℝ) ^ (2 * (j : ℝ)) ≤ baseNow ^ 2 := by
    have hqcast : (q : ℝ) - (q0 : ℝ) = (j : ℝ) := by
      rw [hqeq]
      push_cast
      ring
    rw [hqcast] at hbaseGrowth
    have hnonneg : 0 ≤ (3 : ℝ) ^ (j : ℝ) := by positivity
    have hbase0 : 0 ≤ baseNow := hnonneg.trans hbaseGrowth
    have hsquare := mul_le_mul hbaseGrowth hbaseGrowth hnonneg hbase0
    have hleft : (3 : ℝ) ^ (j : ℝ) * (3 : ℝ) ^ (j : ℝ) =
        (3 : ℝ) ^ (2 * (j : ℝ)) := by
      rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 3)]
      congr 1
      ring
    simpa only [pow_two, hleft] using hsquare
  have hfinal : (3 : ℝ) ^ (2 * (j : ℝ)) * (X - 1) ≤
      baseNow ^ 2 * X - 1 := by
    have hpow1 : 1 ≤ (3 : ℝ) ^ (2 * (j : ℝ)) :=
      Real.one_le_rpow (by norm_num) (by positivity)
    have hfirst := mul_le_mul_of_nonneg_right hbaseSq (sub_nonneg.mpr hX1)
    have hbase1 : 1 ≤ baseNow ^ 2 := hpow1.trans hbaseSq
    calc
      (3 : ℝ) ^ (2 * (j : ℝ)) * (X - 1) ≤
          baseNow ^ 2 * (X - 1) := hfirst
      _ ≤ baseNow ^ 2 * X - 1 := by linarith only [hbase1]
  calc
    Real.log (2 * renormCellCount d (A * q)) ≤ C * (q : ℝ) :=
      log_renormCellCount_endpoint_le d A q hA (hq0.trans hq)
    _ ≤ (3 : ℝ) ^ (2 * (j : ℝ)) * (frGaugeConst d * (X - 1)) := hlinear
    _ = frGaugeConst d * ((3 : ℝ) ^ (2 * (j : ℝ)) * (X - 1)) := by ring
    _ ≤ frGaugeConst d * (baseNow ^ 2 * X - 1) :=
      mul_le_mul_of_nonneg_left hfinal hcfr.le

end

end HCPolySupport.HighContrast.Quenched
