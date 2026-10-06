/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.Regularity.FiniteAffineGradientExcessDecay

/-!
# High-contrast homogenization: Provider.Regularity.FiniteAffineGradientExcessRateSelection

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

namespace HCPolySupport

open scoped ENNReal

noncomputable section

namespace HighContrast

private theorem exists_nat_const_mul_pow_le_const_mul_pow_of_lt
    {a b A B : ℝ} (ha : 0 < a) (hb : 0 < b) (hab : a < b)
    (hA : 0 < A) (hB : 0 < B) :
    ∃ t : ℕ, A * a ^ t ≤ B * b ^ t := by
  have hratioPos : 0 < a / b := div_pos ha hb
  have hratioLt : a / b < 1 := (div_lt_one hb).mpr hab
  have heps : 0 < B / A := div_pos hB hA
  obtain ⟨t, ht⟩ := exists_pow_lt_of_lt_one heps hratioLt
  refine ⟨t, ?_⟩
  have hmul := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left ht.le hA.le) (pow_nonneg hb.le t)
  calc
    A * a ^ t = (A * (a / b) ^ t) * b ^ t := by
      rw [div_pow]
      field_simp [hb.ne']
    _ ≤ (A * (B / A)) * b ^ t := hmul
    _ = B * b ^ t := by field_simp [hA.ne']

/-- The integer-rate deterministic coefficient eventually beats the printed
real-exponent target whenever `eta` is below its effective rate. -/
theorem exists_nat_integer_rate_deterministic_le
    (depth p : ℕ) (hp : 0 < p) (eta C₀ Cc Ce : ℝ)
    (heta : eta < 1 - 1 / (2 * (p : ℝ)))
    (hC₀ : 0 < C₀) (hCc : 0 < Cc) (hCe : 0 < Ce) :
    ∃ t : ℕ,
      Cc * (C₀ * ((1 : ℝ) / 3) ^ ((2 * p - 1) * t) * Ce) ≤
        (1 / 4 : ℝ) * Real.rpow 3
          (-eta * ((depth + 2 * p * t + 4 : ℕ) : ℝ)) := by
  let a : ℝ := ((1 : ℝ) / 3) ^ (2 * p - 1)
  let b : ℝ := Real.rpow 3 (-eta * (2 * (p : ℝ)))
  let A : ℝ := Cc * C₀ * Ce
  let B : ℝ := (1 / 4 : ℝ) * Real.rpow 3
    (-eta * ((depth + 4 : ℕ) : ℝ))
  have ha : 0 < a := by dsimp [a]; positivity
  have hb : 0 < b := by dsimp [b]; positivity
  have hrate : (2 * (p : ℝ)) * eta < (2 * p - 1 : ℕ) := by
    have hpReal : (0 : ℝ) < 2 * p := by positivity
    have h := mul_lt_mul_of_pos_left heta hpReal
    field_simp [show (2 : ℝ) * p ≠ 0 by positivity] at h ⊢
    have hcast : (((2 * p - 1 : ℕ) : ℝ)) = 2 * (p : ℝ) - 1 := by
      rw [Nat.cast_sub (by omega : 1 ≤ 2 * p)]
      push_cast
      ring
    rw [hcast]
    exact h
  have hab : a < b := by
    have hexp : -((2 * p - 1 : ℕ) : ℝ) < -eta * (2 * (p : ℝ)) := by
      linarith only [hrate]
    have hpow := Real.rpow_lt_rpow_of_exponent_lt (by norm_num : (1 : ℝ) < 3) hexp
    have haeq : a = Real.rpow 3 (-((2 * p - 1 : ℕ) : ℝ)) := by
      dsimp [a]
      rw [Real.rpow_neg_eq_inv_rpow, Real.rpow_natCast]
      norm_num
    rw [haeq]
    exact hpow
  have hA : 0 < A := by dsimp [A]; positivity
  have hB : 0 < B := by dsimp [B]; positivity
  obtain ⟨t, ht⟩ :=
    exists_nat_const_mul_pow_le_const_mul_pow_of_lt ha hb hab hA hB
  refine ⟨t, ?_⟩
  have hleft :
      Cc * (C₀ * ((1 : ℝ) / 3) ^ ((2 * p - 1) * t) * Ce) =
        A * a ^ t := by
    dsimp [A, a]
    rw [pow_mul]
    ring
  have hright :
      B * b ^ t = (1 / 4 : ℝ) * Real.rpow 3
          (-eta * ((depth + 2 * p * t + 4 : ℕ) : ℝ)) := by
    dsimp [B, b]
    rw [← Real.rpow_mul_natCast (by norm_num : (0 : ℝ) ≤ 3)]
    rw [mul_assoc]
    rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 3)]
    congr 2
    push_cast
    ring
  rw [hleft, ← hright]
  exact ht

/-- The ruled best-fit Step-1 recurrence with the printed real exponent. -/
theorem exists_scalarIdentityFiniteAffineGradientExcessRateContractionConstants
    (d : ℕ) [NeZero d] (s eta : ℝ) (hs : 0 < s) (hs_lt : s < 1 / 2)
    (_heta0 : 0 ≤ eta) (heta1 : eta < 1) (C : ℝ) (hC : 1 ≤ C) :
    ∃ H : ℕ, 0 < H ∧ ∃ c : ℝ, 0 < c ∧
      ∀ (a : Book.Ch02.TriadicCoeffFamily d) (delta : ℝ)
        (n m : ℤ) (Q : ℤ → Mat d),
        delta ∈ Set.Ioc (0 : ℝ) c →
          ScalarIdentityGoodMaxOnInterval a s delta n m →
          IsFiniteAffineSlopeFamily a delta C n m Q →
          ∀ (k : ℤ) (_hk : k ∈ Finset.Icc n m)
            (_hr : k - (H : ℤ) ∈ Finset.Icc n m)
            (u : Book.Ch03.CubeSolution (originCube d m) a),
            finiteAffineGradientExcess a (k - (H : ℤ)) m u ≤
              ENNReal.ofReal ((1 / 2 : ℝ) * Real.rpow 3 (-eta * (H : ℝ))) *
                finiteAffineGradientExcess a k m u := by
  obtain ⟨p, hp, hetap⟩ :=
    CubeCalderonZygmund.exists_pos_nat_harmonic_integer_rate_gt heta1
  obtain ⟨depth, C₀, Cc, Ce, Ct, hC₀, hCc, hCe, hCt, hsteps⟩ :=
    exists_scalarIdentityFiniteAffineGradientExcessIntegerRateStepConstants
      d s hs hs_lt p hp
  obtain ⟨t, hdet⟩ :=
    exists_nat_integer_rate_deterministic_le depth p hp eta C₀ Cc Ce
      hetap hC₀ hCc hCe
  let N : ℕ := depth + 2 * p * t + 2
  let H : ℕ := N + 2
  obtain ⟨Cs, hCs, hstep⟩ := hsteps t
  let A : ℝ := ((((3 ^ d) ^ N : ℕ) : ℝ))
  let K : ℝ := Cc * (Cs + C * Ct * A)
  let T : ℝ := Real.rpow 3 (-eta * (H : ℝ))
  let c : ℝ := min 1 ((1 / 4 : ℝ) * T / K)
  have hN : 0 < N := by dsimp [N]; omega
  have hH : 0 < H := by dsimp [H]; omega
  have hA : 0 < A := by dsimp [A]; positivity
  have hK : 0 < K := by
    dsimp [K]
    exact mul_pos hCc (add_pos_of_pos_of_nonneg hCs
      (mul_nonneg (mul_nonneg (zero_le_one.trans hC) hCt.le) hA.le))
  have hT : 0 < T := by dsimp [T]; positivity
  have hc : 0 < c := by
    dsimp [c]
    exact lt_min zero_lt_one (div_pos (mul_pos (by norm_num) hT) hK)
  refine ⟨H, hH, c, hc, ?_⟩
  intro a delta n m Q hdelta hgood hfamily k hk hr u
  have hdelta0 : 0 ≤ delta := (Set.mem_Ioc.mp hdelta).1.le
  have hdeltaK : K * delta ≤ (1 / 4 : ℝ) * T := by
    have hdc : delta ≤ (1 / 4 : ℝ) * T / K :=
      (Set.mem_Ioc.mp hdelta).2.trans (min_le_right _ _)
    calc
      K * delta ≤ K * ((1 / 4 : ℝ) * T / K) :=
        mul_le_mul_of_nonneg_left hdc hK.le
      _ = (1 / 4 : ℝ) * T := by field_simp [hK.ne']
  have hrN : k - (N : ℤ) ∈ Finset.Icc n m := by
    have hb := Finset.mem_Icc.mp hr
    have hk' := Finset.mem_Icc.mp hk
    have hHN : (H : ℤ) = (N : ℤ) + 2 := by dsimp [H]
    exact Finset.mem_Icc.2 ⟨by rw [hHN] at hb; omega, by omega⟩
  have hraw := hstep a delta C n m Q hdelta0 hC hgood hfamily k hk hrN u
  let qcoef : ℝ := Cc *
    ((C₀ * ((1 : ℝ) / 3) ^ ((2 * p - 1) * t)) * Ce +
      Cs * delta + C * delta * Ct * A)
  have hpert : Cc * (Cs * delta + C * delta * Ct * A) = K * delta := by
    dsimp [K]
    ring
  have hdet' : Cc *
      ((C₀ * ((1 : ℝ) / 3) ^ ((2 * p - 1) * t)) * Ce) ≤
        (1 / 4 : ℝ) * T := by
    dsimp [T, H, N]
    have hNeq : depth + 2 * p * t + 2 + 2 = depth + 2 * p * t + 4 := by ring
    rw [hNeq]
    exact hdet
  have hqcoef : qcoef ≤ (1 / 2 : ℝ) * T := by
    calc
      qcoef = Cc *
          ((C₀ * ((1 : ℝ) / 3) ^ ((2 * p - 1) * t)) * Ce) +
            Cc * (Cs * delta + C * delta * Ct * A) := by
        dsimp [qcoef]
        ring
      _ = Cc *
          ((C₀ * ((1 : ℝ) / 3) ^ ((2 * p - 1) * t)) * Ce) +
            K * delta := by rw [hpert]
      _ ≤ (1 / 4 : ℝ) * T + (1 / 4 : ℝ) * T :=
        add_le_add hdet' hdeltaK
      _ = (1 / 2 : ℝ) * T := by ring
  have hindex : k - (H : ℤ) = k - (N : ℤ) - 2 := by
    dsimp [H]
    ring
  rw [hindex]
  calc
    finiteAffineGradientExcess a (k - (N : ℤ) - 2) m u ≤
        ENNReal.ofReal qcoef * finiteAffineGradientExcess a k m u := by
      simpa only [qcoef, A, N] using hraw
    _ ≤ ENNReal.ofReal ((1 / 2 : ℝ) * T) *
        finiteAffineGradientExcess a k m u :=
      mul_le_mul_left (ENNReal.ofReal_mono hqcoef) _
    _ = ENNReal.ofReal ((1 / 2 : ℝ) * Real.rpow 3 (-eta * (H : ℝ))) *
        finiteAffineGradientExcess a k m u := by rfl

/-- Caller-facing ruled-family Step 1 with the printed real exponent. -/
theorem exists_scalarIdentityFiniteAffineGradientExcessRateContractionProviderConstants
    (d : ℕ) [NeZero d] (s eta : ℝ) (hs : 0 < s) (hs_lt : s < 1 / 2)
    (heta0 : 0 ≤ eta) (heta1 : eta < 1) :
    ∃ C c : ℝ, 1 ≤ C ∧ 0 < c ∧ ∃ H : ℕ, 0 < H ∧
      ∀ (a : Book.Ch02.TriadicCoeffFamily d) (delta : ℝ) (n m : ℤ),
        n < m → delta ∈ Set.Ioc (0 : ℝ) c →
          ScalarIdentityGoodMaxOnInterval a s delta n m →
          ∃ Q : ℤ → Mat d,
            IsFiniteAffineSlopeFamily a delta C n m Q ∧
            ∀ (k : ℤ) (_hk : k ∈ Finset.Icc n m)
              (_hr : k - (H : ℤ) ∈ Finset.Icc n m)
              (u : Book.Ch03.CubeSolution (originCube d m) a),
              finiteAffineGradientExcess a (k - (H : ℤ)) m u ≤
                ENNReal.ofReal
                    ((1 / 2 : ℝ) * Real.rpow 3 (-eta * (H : ℝ))) *
                  finiteAffineGradientExcess a k m u := by
  obtain ⟨C, c₀, hC, hc₀, hfamily⟩ :=
    exists_scalarIdentityFiniteAffineSlopeFamilyConstants d s hs hs_lt
  obtain ⟨H, hH, c₁, hc₁, hcontract⟩ :=
    exists_scalarIdentityFiniteAffineGradientExcessRateContractionConstants
      d s eta hs hs_lt heta0 heta1 C hC
  let c : ℝ := min c₀ c₁
  have hc : 0 < c := lt_min hc₀.1 hc₁
  refine ⟨C, c, hC, hc, H, hH, ?_⟩
  intro a delta n m hnm hdelta hgood
  have hdelta₀ : delta ∈ Set.Ioc (0 : ℝ) c₀ :=
    ⟨(Set.mem_Ioc.mp hdelta).1,
      (Set.mem_Ioc.mp hdelta).2.trans (min_le_left _ _)⟩
  have hdelta₁ : delta ∈ Set.Ioc (0 : ℝ) c₁ :=
    ⟨(Set.mem_Ioc.mp hdelta).1,
      (Set.mem_Ioc.mp hdelta).2.trans (min_le_right _ _)⟩
  obtain ⟨Q, hQ⟩ := hfamily a delta n m hnm hdelta₀ hgood
  refine ⟨Q, hQ, ?_⟩
  intro k hk hr u
  exact hcontract a delta n m Q hdelta₁ hgood hQ k hk hr u

private theorem finite_gap_rate_contraction_iteration
    (E : ℤ → ℝ≥0∞) (m : ℤ) (H t : ℕ) (rho : ℝ≥0∞)
    (hstep : ∀ q : ℕ, q < t →
      E (m - (((q + 1) * H : ℕ) : ℤ)) ≤
        rho * E (m - ((q * H : ℕ) : ℤ))) :
    E (m - ((t * H : ℕ) : ℤ)) ≤ rho ^ t * E m := by
  induction t with
  | zero => simp
  | succ t ih =>
      have hlast := hstep t (by omega)
      have hprev := ih (fun q hq ↦ hstep q (by omega))
      calc
        E (m - (((t + 1) * H : ℕ) : ℤ)) ≤
            rho * E (m - ((t * H : ℕ) : ℤ)) := hlast
        _ ≤ rho * (rho ^ t * E m) := by
          simpa only [mul_comm] using mul_le_mul_left hprev rho
        _ = rho ^ (t + 1) * E m := by rw [pow_succ]; ac_rfl

private theorem rate_endpoint_real_coefficient_le
    (d H t R : ℕ) (eta : ℝ) (heta0 : 0 ≤ eta) (hRH : R < H) :
    (((((3 ^ d) ^ R : ℕ) : ℝ))) *
        (((1 / 2 : ℝ) * Real.rpow 3 (-eta * (H : ℝ))) ^ t) ≤
      Real.rpow 3 ((d + eta) * (H : ℝ)) *
        Real.rpow 3 (-eta * ((t * H + R : ℕ) : ℝ)) := by
  let x : ℝ := Real.rpow 3 (-eta * (H : ℝ))
  have hx : 0 < x := by dsimp [x]; positivity
  have hbase : (1 / 2 : ℝ) * x ≤ x := by nlinarith only [hx]
  have hpow : ((1 / 2 : ℝ) * x) ^ t ≤ x ^ t :=
    pow_le_pow_left₀ (mul_nonneg (by norm_num) hx.le) hbase t
  have hRle : (R : ℝ) ≤ H := by exact_mod_cast (Nat.le_of_lt hRH)
  have hexp : (d : ℝ) * R - eta * ((H : ℝ) * t) ≤
      ((d : ℝ) + eta) * H - eta * ((t : ℝ) * H + R) := by
    have hnonneg : 0 ≤ ((d : ℝ) + eta) * ((H : ℝ) - R) :=
      mul_nonneg (add_nonneg (Nat.cast_nonneg d) heta0) (sub_nonneg.mpr hRle)
    nlinarith only [hnonneg]
  have hrpow := Real.rpow_le_rpow_of_exponent_le
    (by norm_num : (1 : ℝ) ≤ 3) hexp
  calc
    (((((3 ^ d) ^ R : ℕ) : ℝ))) *
          (((1 / 2 : ℝ) * Real.rpow 3 (-eta * (H : ℝ))) ^ t) ≤
        (((((3 ^ d) ^ R : ℕ) : ℝ))) * x ^ t := by
      exact mul_le_mul_of_nonneg_left hpow (by positivity)
    _ = Real.rpow 3 ((d : ℝ) * R - eta * ((H : ℝ) * t)) := by
      dsimp [x]
      rw [← Real.rpow_mul_natCast (by norm_num : (0 : ℝ) ≤ 3)]
      rw [show (((((3 ^ d) ^ R : ℕ) : ℝ))) =
          Real.rpow 3 ((d : ℝ) * R) by
        calc
          (((((3 ^ d) ^ R : ℕ) : ℝ))) = (3 : ℝ) ^ (d * R) := by
            norm_cast
            rw [← pow_mul]
          _ = Real.rpow 3 (((d * R : ℕ) : ℝ)) :=
            (Real.rpow_natCast 3 (d * R)).symm
          _ = Real.rpow 3 ((d : ℝ) * R) := by
            congr 1
            push_cast
            ring]
      calc
        Real.rpow 3 ((d : ℝ) * R) *
            Real.rpow 3 (-eta * (H : ℝ) * t) =
          Real.rpow 3 ((d : ℝ) * R + (-eta * (H : ℝ) * t)) :=
            (Real.rpow_add (by norm_num : (0 : ℝ) < 3) _ _).symm
        _ = _ := by congr 1; ring
    _ ≤ Real.rpow 3
        (((d : ℝ) + eta) * H - eta * ((t : ℝ) * H + R)) := hrpow
    _ = Real.rpow 3 ((d + eta) * (H : ℝ)) *
        Real.rpow 3 (-eta * ((t * H + R : ℕ) : ℝ)) := by
      calc
        Real.rpow 3
            (((d : ℝ) + eta) * H - eta * ((t : ℝ) * H + R)) =
          Real.rpow 3 (((d : ℝ) + eta) * H +
            (-eta * ((t * H + R : ℕ) : ℝ))) := by
              congr 1
              push_cast
              ring
        _ = _ := Real.rpow_add (by norm_num : (0 : ℝ) < 3) _ _

/-- Arbitrary-gap Step-1 decay with the terminal remainder band explicit. -/
theorem exists_scalarIdentityFiniteAffineGradientExcessRateDiscreteDecayConstants
    (d : ℕ) [NeZero d] (s eta : ℝ) (hs : 0 < s) (hs_lt : s < 1 / 2)
    (heta0 : 0 ≤ eta) (heta1 : eta < 1) :
    ∃ C c : ℝ, 1 ≤ C ∧ 0 < c ∧ ∃ H : ℕ, 0 < H ∧
      ∀ (a : Book.Ch02.TriadicCoeffFamily d) (delta : ℝ) (n m : ℤ),
        n < m → delta ∈ Set.Ioc (0 : ℝ) c →
          ScalarIdentityGoodMaxOnInterval a s delta n m →
          ∃ Q : ℤ → Mat d,
            IsFiniteAffineSlopeFamily a delta C n m Q ∧
            ∀ u : Book.Ch03.CubeSolution (originCube d m) a,
              let gap := Int.toNat (m - n)
              let t := gap / H
              let R := gap % H
              finiteAffineGradientExcess a n m u ≤
                ENNReal.ofReal (((((3 ^ d) ^ R : ℕ) : ℝ))) *
                  (ENNReal.ofReal
                      ((1 / 2 : ℝ) * Real.rpow 3 (-eta * (H : ℝ))) ^ t *
                    finiteAffineGradientExcess a m m u) := by
  obtain ⟨C, c, hC, hc, H, hH, hprovider⟩ :=
    exists_scalarIdentityFiniteAffineGradientExcessRateContractionProviderConstants
      d s eta hs hs_lt heta0 heta1
  refine ⟨C, c, hC, hc, H, hH, ?_⟩
  intro a delta n m hnm hdelta hgood
  obtain ⟨Q, hQ, hcontract⟩ := hprovider a delta n m hnm hdelta hgood
  refine ⟨Q, hQ, ?_⟩
  intro u
  dsimp only
  let gap : ℕ := Int.toNat (m - n)
  let t : ℕ := gap / H
  let R : ℕ := gap % H
  let j : ℤ := m - ((t * H : ℕ) : ℤ)
  let rho : ℝ≥0∞ := ENNReal.ofReal
    ((1 / 2 : ℝ) * Real.rpow 3 (-eta * (H : ℝ)))
  have hgapCast : (gap : ℤ) = m - n := by
    dsimp [gap]
    rw [Int.toNat_of_nonneg (sub_nonneg.mpr hnm.le)]
  have hdiv : t * H + R = gap := by
    simpa only [t, R, Nat.mul_comm] using Nat.div_add_mod gap H
  have hdivCast : ((t * H : ℕ) : ℤ) + (R : ℤ) = m - n := by
    have h := congrArg (fun z : ℕ ↦ (z : ℤ)) hdiv
    push_cast at h
    simpa only [hgapCast] using! h
  have hj : j = n + (R : ℤ) := by dsimp [j]; omega
  have hjm : j ≤ m := by dsimp [j]; omega
  have hjmem : j ∈ Finset.Icc n m :=
    Finset.mem_Icc.2 ⟨by rw [hj]; omega, hjm⟩
  have hiter : finiteAffineGradientExcess a
      (m - ((t * H : ℕ) : ℤ)) m u ≤
        rho ^ t * finiteAffineGradientExcess a m m u := by
    apply finite_gap_rate_contraction_iteration
      (E := fun z ↦ finiteAffineGradientExcess a z m u)
      (m := m) (H := H) (t := t) (rho := rho)
    intro q hqt
    have hqNat : q * H ≤ t * H := Nat.mul_le_mul_right H (Nat.le_of_lt hqt)
    have hq1Nat : (q + 1) * H ≤ t * H :=
      Nat.mul_le_mul_right H (by omega)
    have hqInt : ((q * H : ℕ) : ℤ) ≤ ((t * H : ℕ) : ℤ) := by
      exact_mod_cast hqNat
    have hq1Int : (((q + 1) * H : ℕ) : ℤ) ≤ ((t * H : ℕ) : ℤ) := by
      exact_mod_cast hq1Nat
    have hkq : m - ((q * H : ℕ) : ℤ) ∈ Finset.Icc n m := by
      have hb := Finset.mem_Icc.mp hjmem
      exact Finset.mem_Icc.2 ⟨by omega, by omega⟩
    have hrq : m - (((q + 1) * H : ℕ) : ℤ) ∈ Finset.Icc n m := by
      have hb := Finset.mem_Icc.mp hjmem
      exact Finset.mem_Icc.2 ⟨by omega, by omega⟩
    have h := hcontract (m - ((q * H : ℕ) : ℤ)) hkq (by
      have hcast : (((q + 1) * H : ℕ) : ℤ) =
          ((q * H : ℕ) : ℤ) + (H : ℤ) := by push_cast; ring
      simpa only [hcast, sub_sub] using hrq) u
    have hindex : m - ((q * H : ℕ) : ℤ) - (H : ℤ) =
        m - (((q + 1) * H : ℕ) : ℤ) := by push_cast; ring
    simpa only [rho, hindex] using h
  have hiter' : finiteAffineGradientExcess a j m u ≤
      rho ^ t * finiteAffineGradientExcess a m m u := by simpa only [j] using hiter
  have hrestrict := finiteAffineGradientExcess_sub_nat_le a j m hjm R u
  have hjsub : j - (R : ℤ) = n := by rw [hj]; ring
  rw [hjsub] at hrestrict
  calc
    finiteAffineGradientExcess a n m u ≤
        ENNReal.ofReal (((((3 ^ d) ^ R : ℕ) : ℝ))) *
          finiteAffineGradientExcess a j m u := hrestrict
    _ ≤ ENNReal.ofReal (((((3 ^ d) ^ R : ℕ) : ℝ))) *
          (rho ^ t * finiteAffineGradientExcess a m m u) := by
      simpa only [mul_comm] using mul_le_mul_left hiter'
        (ENNReal.ofReal (((((3 ^ d) ^ R : ℕ) : ℝ))))
    _ = ENNReal.ofReal (((((3 ^ d) ^ R : ℕ) : ℝ))) *
          (ENNReal.ofReal
              ((1 / 2 : ℝ) * Real.rpow 3 (-eta * (H : ℝ))) ^ t *
            finiteAffineGradientExcess a m m u) := by rfl

/-- Full Step-1 decay in the printed real-exponent form, with the ruled
best-fit slope family produced in the same existential package. -/
theorem exists_scalarIdentityFiniteAffineGradientExcessRealRateDecayConstants
    (d : ℕ) [NeZero d] (s eta : ℝ) (hs : 0 < s) (hs_lt : s < 1 / 2)
    (heta0 : 0 ≤ eta) (heta1 : eta < 1) :
    ∃ Cfamily c Cdec : ℝ,
      1 ≤ Cfamily ∧ 0 < c ∧ 0 < Cdec ∧
      ∀ (a : Book.Ch02.TriadicCoeffFamily d) (delta : ℝ) (n m : ℤ),
        n < m → delta ∈ Set.Ioc (0 : ℝ) c →
          ScalarIdentityGoodMaxOnInterval a s delta n m →
          ∃ Q : ℤ → Mat d,
            IsFiniteAffineSlopeFamily a delta Cfamily n m Q ∧
            ∀ u : Book.Ch03.CubeSolution (originCube d m) a,
              finiteAffineGradientExcess a n m u ≤
                ENNReal.ofReal
                    (Cdec * Real.rpow 3 (-eta * ((m - n : ℤ) : ℝ))) *
                  finiteAffineGradientExcess a m m u := by
  obtain ⟨Cfamily, c, hCfamily, hc, H, hH, hdecay⟩ :=
    exists_scalarIdentityFiniteAffineGradientExcessRateDiscreteDecayConstants
      d s eta hs hs_lt heta0 heta1
  let Cdec : ℝ := Real.rpow 3 (((d : ℝ) + eta) * (H : ℝ))
  have hCdec : 0 < Cdec := by dsimp [Cdec]; positivity
  refine ⟨Cfamily, c, Cdec, hCfamily, hc, hCdec, ?_⟩
  intro a delta n m hnm hdelta hgood
  obtain ⟨Q, hQ, hbound⟩ := hdecay a delta n m hnm hdelta hgood
  refine ⟨Q, hQ, ?_⟩
  intro u
  let gap : ℕ := Int.toNat (m - n)
  let t : ℕ := gap / H
  let R : ℕ := gap % H
  let rho : ℝ := (1 / 2 : ℝ) * Real.rpow 3 (-eta * (H : ℝ))
  have hgapCast : (gap : ℤ) = m - n := by
    dsimp [gap]
    rw [Int.toNat_of_nonneg (sub_nonneg.mpr hnm.le)]
  have hdiv : t * H + R = gap := by
    simpa only [t, R, Nat.mul_comm] using Nat.div_add_mod gap H
  have hR : R < H := by
    exact Nat.mod_lt gap hH
  have hreal := rate_endpoint_real_coefficient_le d H t R eta heta0 hR
  have hreal' : (((((3 ^ d) ^ R : ℕ) : ℝ))) * rho ^ t ≤
      Cdec * Real.rpow 3 (-eta * ((m - n : ℤ) : ℝ)) := by
    have hcast : (((t * H + R : ℕ) : ℤ)) = m - n := by
      rw [hdiv, hgapCast]
    have hcastReal : (((t * H + R : ℕ) : ℝ)) = ((m - n : ℤ) : ℝ) := by
      exact_mod_cast hcast
    rw [hcastReal] at hreal
    simpa only [rho, Cdec] using hreal
  have hrho : 0 ≤ rho := by dsimp [rho]; positivity
  have hvolume : 0 ≤ (((((3 ^ d) ^ R : ℕ) : ℝ))) := by positivity
  have hcoef :
      ENNReal.ofReal (((((3 ^ d) ^ R : ℕ) : ℝ))) *
          ENNReal.ofReal rho ^ t ≤
        ENNReal.ofReal
          (Cdec * Real.rpow 3 (-eta * ((m - n : ℤ) : ℝ))) := by
    rw [← ENNReal.ofReal_pow hrho]
    rw [← ENNReal.ofReal_mul hvolume]
    exact ENNReal.ofReal_mono hreal'
  have hraw := hbound u
  dsimp only at hraw
  calc
    finiteAffineGradientExcess a n m u ≤
        ENNReal.ofReal (((((3 ^ d) ^ R : ℕ) : ℝ))) *
          (ENNReal.ofReal rho ^ t * finiteAffineGradientExcess a m m u) := by
      simpa only [gap, t, R, rho] using hraw
    _ = (ENNReal.ofReal (((((3 ^ d) ^ R : ℕ) : ℝ))) *
          ENNReal.ofReal rho ^ t) * finiteAffineGradientExcess a m m u := by
      ac_rfl
    _ ≤ ENNReal.ofReal
          (Cdec * Real.rpow 3 (-eta * ((m - n : ℤ) : ℝ))) *
        finiteAffineGradientExcess a m m u := mul_le_mul_left hcoef _

end HighContrast
end
end HCPolySupport
