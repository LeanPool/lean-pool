/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.Regularity.FiniteAffineBestFitInduction

/-!
# High-contrast homogenization: Provider.Regularity.FiniteAffineBestFitBounds

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# Finite affine best-fit slope bounds

This module packages the adjacent, all-pair, and terminal slope consequences
of the finite best-fit error induction.
-/

namespace HCPolySupport
namespace HighContrast

noncomputable section

private theorem euclideanNorm_le_add_sub
    {d : ℕ} (x y : Vec d) :
    euclideanNorm y ≤ euclideanNorm x + euclideanNorm (x - y) := by
  rw [euclideanNorm_eq_norm_ofVec, euclideanNorm_eq_norm_ofVec,
    euclideanNorm_eq_norm_ofVec]
  change ‖WithLp.toLp 2 y‖ ≤
    ‖WithLp.toLp 2 x‖ + ‖WithLp.toLp 2 (x - y)‖
  have h := norm_add_le (WithLp.toLp 2 x) (WithLp.toLp 2 (y - x))
  rw [← WithLp.toLp_add] at h
  have hsum : x + (y - x) = y := by abel
  rw [hsum] at h
  simpa only [show y - x = -(x - y) by abel, WithLp.toLp_neg, norm_neg] using h

private theorem finiteRealSequence_pow_bounds
    (p : ℤ → ℝ) (A : ℝ) (hA0 : 0 ≤ A) (hA1 : A ≤ 1)
    {j k : ℤ} (hjk : j ≤ k)
    (hlower : ∀ h : ℤ, j ≤ h → h < k → (1 - A) * p h ≤ p (h + 1))
    (hupper : ∀ h : ℤ, j ≤ h → h < k → p (h + 1) ≤ (1 + A) * p h) :
    (1 - A) ^ Int.toNat (k - j) * p j ≤ p k ∧
      p k ≤ (1 + A) ^ Int.toNat (k - j) * p j := by
  have hgap_nonneg : 0 ≤ k - j := sub_nonneg.mpr hjk
  let N : ℕ := Int.toNat (k - j)
  have hNcast : (N : ℤ) = k - j := Int.toNat_of_nonneg hgap_nonneg
  have hind : ∀ q : ℕ, q ≤ N →
      (1 - A) ^ q * p j ≤ p (j + (q : ℤ)) ∧
        p (j + (q : ℤ)) ≤ (1 + A) ^ q * p j := by
    intro q hq
    induction q with
    | zero => simp
    | succ q ih =>
        have hqN : q < N := by omega
        have hqle : q ≤ N := by omega
        have hjq : j ≤ j + (q : ℤ) := by omega
        have hjqk : j + (q : ℤ) < k := by omega
        obtain ⟨ihlow, ihup⟩ := ih hqle
        have hlow := hlower (j + (q : ℤ)) hjq hjqk
        have hup := hupper (j + (q : ℤ)) hjq hjqk
        constructor
        · calc
            (1 - A) ^ (q + 1) * p j =
                (1 - A) * ((1 - A) ^ q * p j) := by rw [pow_succ]; ring
            _ ≤ (1 - A) * p (j + (q : ℤ)) := by
              exact mul_le_mul_of_nonneg_left ihlow (sub_nonneg.mpr hA1)
            _ ≤ p (j + (q : ℤ) + 1) := hlow
            _ = p (j + ((q + 1 : ℕ) : ℤ)) := by push_cast; ring_nf
        · calc
            p (j + ((q + 1 : ℕ) : ℤ)) = p (j + (q : ℤ) + 1) := by
                push_cast; ring_nf
            _ ≤ (1 + A) * p (j + (q : ℤ)) := hup
            _ ≤ (1 + A) * ((1 + A) ^ q * p j) := by
              exact mul_le_mul_of_nonneg_left ihup (by linarith only [hA0])
            _ = (1 + A) ^ (q + 1) * p j := by rw [pow_succ]; ring
  obtain ⟨hlow, hup⟩ := hind N le_rfl
  rw [show j + (N : ℤ) = k by omega] at hlow hup
  simpa only [N] using And.intro hlow hup

private theorem relative_slope_difference_le_previous
    {d : ℕ} (previous next : Vec d) {amplitude : ℝ}
    (hamplitude : 0 ≤ amplitude) (hsmall : amplitude ≤ 1 / 4)
    (hdifference : euclideanNorm (next - previous) ≤ amplitude * euclideanNorm next) :
    euclideanNorm (next - previous) ≤ 2 * amplitude * euclideanNorm previous := by
  have hreverse : euclideanNorm (previous - next) =
      euclideanNorm (next - previous) := by
    rw [show previous - next = -(next - previous) by abel, euclideanNorm_neg]
  have htriangle := euclideanNorm_le_add_sub previous next
  rw [hreverse] at htriangle
  have hscaled := mul_le_mul_of_nonneg_right hsmall (euclideanNorm_nonneg next)
  have hnext : euclideanNorm next ≤ 2 * euclideanNorm previous := by
    nlinarith only [htriangle, hdifference, hscaled, euclideanNorm_nonneg previous]
  calc
    euclideanNorm (next - previous) ≤ amplitude * euclideanNorm next := hdifference
    _ ≤ amplitude * (2 * euclideanNorm previous) :=
      mul_le_mul_of_nonneg_left hnext hamplitude
    _ = 2 * amplitude * euclideanNorm previous := by ring

private theorem relative_slope_norm_step_bounds
    {d : ℕ} (previous next : Vec d) (amplitude : ℝ)
    (hdifference : euclideanNorm (next - previous) ≤ amplitude * euclideanNorm previous) :
    (1 - amplitude) * euclideanNorm previous ≤ euclideanNorm next ∧
      euclideanNorm next ≤ (1 + amplitude) * euclideanNorm previous := by
  have hlower := euclideanNorm_le_add_sub next previous
  have hupper := euclideanNorm_le_add_sub previous next
  rw [show previous - next = -(next - previous) by abel, euclideanNorm_neg] at hupper
  constructor <;> nlinarith only [hdifference, hlower, hupper]

private theorem product_le_inverse_of_inverse_cap
    {factor divisor value : ℝ} (hfactor : 0 < factor) (hdivisor : 0 < divisor)
    (hcap : value ≤ (divisor * factor)⁻¹) :
    factor * value ≤ divisor⁻¹ := by
  calc
    factor * value ≤ factor * (divisor * factor)⁻¹ :=
      mul_le_mul_of_nonneg_left hcap hfactor.le
    _ = divisor⁻¹ := by field_simp [hfactor.ne', hdivisor.ne']

/-- Shared constants for finite best-fit error, adjacent slope control,
all-pair multiplicative slope bounds, and terminal slope closeness. -/
theorem exists_scalarIdentityFiniteAffineBestFitInductionConstants
    (d : ℕ) [NeZero d] (s : ℝ) (hs : 0 < s) (hs_lt : s < 1 / 2) :
    ∃ C c : ℝ, 1 ≤ C ∧ c ∈ Set.Ioc (0 : ℝ) ((2 * C)⁻¹) ∧
      ∀ (a : Book.Ch02.TriadicCoeffFamily d) (delta : ℝ) (n m : ℤ),
        n < m → delta ∈ Set.Ioc (0 : ℝ) c →
          ScalarIdentityGoodMaxOnInterval a s delta n m →
          ∀ (k : ℤ) (hk : k ∈ Finset.Icc n m) (b : Vec d),
            finiteAffineBestFitError a k m (Finset.mem_Icc.mp hk).2 b ≤
                C * delta * euclideanNorm
                  (finiteAffineBestFitSlope a k m
                    (Finset.mem_Icc.mp hk).2 b) ∧
              (∀ hkm : k < m,
                euclideanNorm
                    (finiteAffineBestFitSlope a (k + 1) m (by omega) b -
                      finiteAffineBestFitSlope a k m
                        (Finset.mem_Icc.mp hk).2 b) ≤
                  C * delta * euclideanNorm
                    (finiteAffineBestFitSlope a k m
                      (Finset.mem_Icc.mp hk).2 b)) ∧
              (∀ (j : ℤ) (hj : j ∈ Finset.Icc n m), j ≤ k →
                (1 - C * delta) ^ Int.toNat (k - j) *
                    euclideanNorm
                      (finiteAffineBestFitSlope a j m
                        (Finset.mem_Icc.mp hj).2 b) ≤
                  euclideanNorm
                    (finiteAffineBestFitSlope a k m
                      (Finset.mem_Icc.mp hk).2 b) ∧
                euclideanNorm
                    (finiteAffineBestFitSlope a k m
                      (Finset.mem_Icc.mp hk).2 b) ≤
                  (1 + C * delta) ^ Int.toNat (k - j) *
                    euclideanNorm
                      (finiteAffineBestFitSlope a j m
                        (Finset.mem_Icc.mp hj).2 b)) ∧
              (k = m →
                euclideanNorm
                    (finiteAffineBestFitSlope a m m (le_refl m) b - b) ≤
                  C * delta * euclideanNorm b) := by
  obtain ⟨C₀, c₀, hC₀, hc₀, herror⟩ :=
    exists_scalarIdentityFiniteAffineBestFitErrorInductionConstants d s hs hs_lt
  obtain ⟨Ca, hCa, hadj⟩ := exists_finiteAffineBestFitAdjacentSlopeConstant d
  obtain ⟨Ct, hCt, hterminal⟩ :=
    exists_finiteAffineBestFitTerminalSlopeConstant d s hs hs_lt
  let C : ℝ := 1 + C₀ + 2 * Ca * C₀ + Ct
  let c : ℝ := min (1 / 2 : ℝ)
    (min c₀ (min ((2 * C)⁻¹) ((4 * Ca * C₀)⁻¹)))
  have hC : 1 ≤ C := by
    dsimp [C]
    have hCaC : 0 ≤ 2 * Ca * C₀ := by positivity
    linarith only [hC₀, hCt.le, hCaC]
  have hCpos : 0 < C := lt_of_lt_of_le zero_lt_one hC
  have hcapos : 0 < 4 * Ca * C₀ := by positivity
  have hcpos : 0 < c := by
    dsimp [c]
    exact lt_min (by norm_num) (lt_min hc₀.1 (lt_min
      (inv_pos.mpr (mul_pos (by norm_num) hCpos)) (inv_pos.mpr hcapos)))
  have hcC : c ≤ (2 * C)⁻¹ := by
    dsimp [c]
    exact (min_le_right _ _).trans
      ((min_le_right _ _).trans (min_le_left _ _))
  have hC₀C : C₀ ≤ C := by
    dsimp [C]
    have hnonneg : 0 ≤ 2 * Ca * C₀ := by positivity
    linarith only [hnonneg, hCt.le]
  have htwoC : 2 * Ca * C₀ ≤ C := by
    dsimp [C]
    linarith only [hC₀, hCt.le]
  have hCtC : Ct ≤ C := by
    dsimp [C]
    have hnonneg : 0 ≤ 2 * Ca * C₀ := by positivity
    linarith only [hC₀, hnonneg]
  refine ⟨C, c, hC, ⟨hcpos, hcC⟩, ?_⟩
  intro a delta n m hnm hdelta hgood k hk b
  have hdelta₀ : delta ∈ Set.Ioc (0 : ℝ) c₀ :=
    ⟨hdelta.1, hdelta.2.trans ((min_le_right _ _).trans (min_le_left _ _))⟩
  have hdelta_nonneg : 0 ≤ delta := hdelta.1.le
  have hdelta_one : delta ≤ 1 := by
    exact hdelta.2.trans ((min_le_left _ _).trans (by norm_num))
  have hxsmall : Ca * C₀ * delta ≤ 1 / 4 := by
    have hd : delta ≤ (4 * Ca * C₀)⁻¹ :=
      hdelta.2.trans ((min_le_right _ _).trans
        ((min_le_right _ _).trans (min_le_right _ _)))
    simpa only [mul_assoc, inv_eq_one_div] using product_le_inverse_of_inverse_cap
      (mul_pos hCa (lt_of_lt_of_le zero_lt_one hC₀)) (by norm_num : (0 : ℝ) < 4)
      (by simpa only [mul_assoc] using hd)
  have hCdelta : C * delta ≤ 1 / 2 := by
    have hd : delta ≤ (2 * C)⁻¹ :=
      hdelta.2.trans ((min_le_right _ _).trans
        ((min_le_right _ _).trans (min_le_left _ _)))
    simpa only [inv_eq_one_div] using product_le_inverse_of_inverse_cap
      hCpos (by norm_num : (0 : ℝ) < 2) hd
  have hE₀ := herror a delta n m hnm hdelta₀ hgood k hk b
  have hE : finiteAffineBestFitError a k m (Finset.mem_Icc.mp hk).2 b ≤
      C * delta * euclideanNorm
        (finiteAffineBestFitSlope a k m (Finset.mem_Icc.mp hk).2 b) := by
    exact hE₀.trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hC₀C hdelta_nonneg)
      (euclideanNorm_nonneg _))
  have hadjacent : ∀ hkm : k < m,
      euclideanNorm
          (finiteAffineBestFitSlope a (k + 1) m (by omega) b -
            finiteAffineBestFitSlope a k m (Finset.mem_Icc.mp hk).2 b) ≤
        C * delta * euclideanNorm
          (finiteAffineBestFitSlope a k m (Finset.mem_Icc.mp hk).2 b) := by
    intro hkm
    have hk1 : k + 1 ∈ Finset.Icc n m := Finset.mem_Icc.2 ⟨by
      exact (Finset.mem_Icc.mp hk).1.trans (by omega), by omega⟩
    have hE1 := herror a delta n m hnm hdelta₀ hgood (k + 1) hk1 b
    have ha := hadj a k m (by omega) b
    have hdiff : euclideanNorm
          (finiteAffineBestFitSlope a (k + 1) m (by omega) b -
            finiteAffineBestFitSlope a k m (Finset.mem_Icc.mp hk).2 b) ≤
        Ca * C₀ * delta * euclideanNorm
          (finiteAffineBestFitSlope a (k + 1) m (by omega) b) := by
      rw [show finiteAffineBestFitSlope a (k + 1) m (by omega) b -
          finiteAffineBestFitSlope a k m (Finset.mem_Icc.mp hk).2 b =
        -(finiteAffineBestFitSlope a k m (Finset.mem_Icc.mp hk).2 b -
          finiteAffineBestFitSlope a (k + 1) m (by omega) b) by abel,
        euclideanNorm_neg]
      exact ha.trans (by
        simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hE1 hCa.le)
    have hrelative := relative_slope_difference_le_previous
      (finiteAffineBestFitSlope a k m (Finset.mem_Icc.mp hk).2 b)
      (finiteAffineBestFitSlope a (k + 1) m (by omega) b)
      (mul_nonneg (mul_nonneg hCa.le (zero_le_one.trans hC₀)) hdelta_nonneg)
      hxsmall hdiff
    calc
      _ ≤ 2 * (Ca * C₀ * delta) * euclideanNorm
          (finiteAffineBestFitSlope a k m (Finset.mem_Icc.mp hk).2 b) := hrelative
      _ = (2 * Ca * C₀) * (delta * euclideanNorm
          (finiteAffineBestFitSlope a k m (Finset.mem_Icc.mp hk).2 b)) := by ring
      _ ≤ C * (delta * euclideanNorm
          (finiteAffineBestFitSlope a k m (Finset.mem_Icc.mp hk).2 b)) :=
        mul_le_mul_of_nonneg_right htwoC
          (mul_nonneg hdelta_nonneg (euclideanNorm_nonneg _))
      _ = C * delta * euclideanNorm
          (finiteAffineBestFitSlope a k m (Finset.mem_Icc.mp hk).2 b) := by ring
  have hpairs : ∀ (j : ℤ) (hj : j ∈ Finset.Icc n m), j ≤ k →
      (1 - C * delta) ^ Int.toNat (k - j) *
          euclideanNorm
            (finiteAffineBestFitSlope a j m (Finset.mem_Icc.mp hj).2 b) ≤
        euclideanNorm
          (finiteAffineBestFitSlope a k m (Finset.mem_Icc.mp hk).2 b) ∧
      euclideanNorm
          (finiteAffineBestFitSlope a k m (Finset.mem_Icc.mp hk).2 b) ≤
        (1 + C * delta) ^ Int.toNat (k - j) *
          euclideanNorm
            (finiteAffineBestFitSlope a j m (Finset.mem_Icc.mp hj).2 b) := by
    intro j hj hjk
    let p : ℤ → ℝ := fun r ↦ if hr : r ∈ Finset.Icc n m then
      euclideanNorm
        (finiteAffineBestFitSlope a r m (Finset.mem_Icc.mp hr).2 b) else 0
    have hlocal : ∀ r : ℤ, j ≤ r → r < k →
        ∀ hrm : r ≤ m, ∀ hr1m : r + 1 ≤ m,
          euclideanNorm
            (finiteAffineBestFitSlope a (r + 1) m hr1m b -
              finiteAffineBestFitSlope a r m hrm b) ≤
          C * delta * euclideanNorm
            (finiteAffineBestFitSlope a r m hrm b) := by
      intro r hjr hrk hrm hr1m
      have hnr : n ≤ r := (Finset.mem_Icc.mp hj).1.trans hjr
      have hnr1 : n ≤ r + 1 := hnr.trans (by omega)
      have hr : r ∈ Finset.Icc n m := Finset.mem_Icc.2 ⟨
        hnr, hrm⟩
      have hr1 : r + 1 ∈ Finset.Icc n m := Finset.mem_Icc.2 ⟨hnr1, hr1m⟩
      have hEr1 := herror a delta n m hnm hdelta₀ hgood (r + 1) hr1 b
      have ha := hadj a r m hr1m b
      have hdiff : euclideanNorm
            (finiteAffineBestFitSlope a (r + 1) m hr1m b -
              finiteAffineBestFitSlope a r m hrm b) ≤
          Ca * C₀ * delta * euclideanNorm
            (finiteAffineBestFitSlope a (r + 1) m hr1m b) := by
        rw [show finiteAffineBestFitSlope a (r + 1) m hr1m b -
              finiteAffineBestFitSlope a r m hrm b =
            -(finiteAffineBestFitSlope a r m (by omega) b -
              finiteAffineBestFitSlope a (r + 1) m hr1m b) by abel,
          euclideanNorm_neg]
        exact ha.trans (by
          simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hEr1 hCa.le)
      have hrelative := relative_slope_difference_le_previous
        (finiteAffineBestFitSlope a r m hrm b)
        (finiteAffineBestFitSlope a (r + 1) m hr1m b)
        (mul_nonneg (mul_nonneg hCa.le (zero_le_one.trans hC₀)) hdelta_nonneg)
        hxsmall hdiff
      calc
        _ ≤ 2 * (Ca * C₀ * delta) *
            euclideanNorm (finiteAffineBestFitSlope a r m hrm b) := hrelative
        _ = (2 * Ca * C₀) *
            (delta * euclideanNorm (finiteAffineBestFitSlope a r m hrm b)) := by ring
        _ ≤ C * (delta * euclideanNorm (finiteAffineBestFitSlope a r m hrm b)) :=
          mul_le_mul_of_nonneg_right htwoC
            (mul_nonneg hdelta_nonneg (euclideanNorm_nonneg _))
        _ = C * delta * euclideanNorm (finiteAffineBestFitSlope a r m hrm b) := by ring
    have hsteps : ∀ r : ℤ, j ≤ r → r < k →
        (1 - C * delta) * p r ≤ p (r + 1) ∧
          p (r + 1) ≤ (1 + C * delta) * p r := by
      intro r hjr hrk
      have hkmTop : k ≤ m := (Finset.mem_Icc.mp hk).2
      have hnr : n ≤ r := (Finset.mem_Icc.mp hj).1.trans hjr
      have hnr1 : n ≤ r + 1 := hnr.trans (by omega)
      have hrm : r ≤ m := (le_of_lt hrk).trans hkmTop
      have hr1m : r + 1 ≤ m := (by omega)
      have hr : r ∈ Finset.Icc n m := Finset.mem_Icc.2 ⟨hnr, hrm⟩
      have hr1 : r + 1 ∈ Finset.Icc n m := Finset.mem_Icc.2 ⟨hnr1, hr1m⟩
      have hd := hlocal r hjr hrk hrm hr1m
      simp only [p, dite_eq_left hr, dite_eq_left hr1]
      exact (relative_slope_norm_step_bounds
        (finiteAffineBestFitSlope a r m hrm b)
        (finiteAffineBestFitSlope a (r + 1) m hr1m b) (C * delta) hd)
    have hpw := finiteRealSequence_pow_bounds p (C * delta)
      (mul_nonneg hCpos.le hdelta_nonneg) (hCdelta.trans (by norm_num))
      hjk (fun r hjr hrk ↦ (hsteps r hjr hrk).1)
      (fun r hjr hrk ↦ (hsteps r hjr hrk).2)
    simpa only [p, dite_eq_left hj, dite_eq_left hk] using hpw
  have hterminal' : k = m →
      euclideanNorm (finiteAffineBestFitSlope a m m (le_refl m) b - b) ≤
        C * delta * euclideanNorm b := by
    intro hkm
    have herrm := hgood.weakError_le (Finset.mem_Icc.2 ⟨hnm.le, le_rfl⟩)
    have ht := hterminal a m b delta hdelta_nonneg hdelta_one herrm
    exact ht.trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hCtC hdelta_nonneg)
      (euclideanNorm_nonneg b))
  exact ⟨hE, hadjacent, hpairs, hterminal'⟩

end

end HighContrast
end HCPolySupport
