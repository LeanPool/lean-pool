/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.CoarseEllipticity.SuperposedFluxLowerAmplitude

/-!
# SuperposedFluxLowerSeries

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section

/-!
# Scale-series estimates for the sharp lower lane

This file sums the uniform depth amplitude against the rooted finite-exponent
weight and against the endpoint weight.  The only pole used below is the
rounded order-five pole already recorded for the lower lane.
-/

namespace Algsuperdiff.Section3.Provider.CoarseEllipticity

open MeasureTheory
open HCPolySupport HCPolySupport.Book HCPolySupport.IndependentSums
open Algsuperdiff.Frozen.Assumptions
open Algsuperdiff.Section3
open Algsuperdiff.Section3.Provider.Percolation

noncomputable section

variable {d : ℕ}

/-- Numerical cost of transporting the order-four polynomial from the
positive-gap grid weight to the endpoint weight and then to the frozen
window. -/
def superposedFluxLowerPoleConst : ℝ := 6912

theorem superposedFluxLowerPoleConst_pos : 0 < superposedFluxLowerPoleConst := by
  norm_num [superposedFluxLowerPoleConst]

theorem summable_poly_mul_endpointWeight (rho : ℝ) (hrho : 0 < rho) :
    Summable fun n : ℕ => (((n : ℝ) + 1) ^ (4 : ℕ)) * endpointWeight rho n := by
  have hgrid : Summable fun n : ℕ =>
      gridWeight rho n * (((n : ℝ) + 1) ^ (4 : ℕ)) := by
    simpa [mul_comm] using polyGridWeight_summable 4 hrho
  simpa [mul_comm] using summable_endpointWeight_mul hgrid

/-- The rounded order-five endpoint series, priced at the frozen window. -/
theorem tsum_poly_mul_endpointWeight_le_frozenPole
    {rho eps : ℝ} (hrho : 0 < rho) (hrhoTwo : rho ≤ 2)
    (heps : 0 < eps) (hepsOne : eps ≤ 1) (hwindow : 2 * eps ≤ rho) :
    ∑' n : ℕ, (((n : ℝ) + 1) ^ (4 : ℕ)) * endpointWeight rho n ≤
      superposedFluxLowerPoleConst * eps⁻¹ ^ (5 : ℕ) := by
  have hgrid := polyGridWeight_tsum_le 4 hrho
  have hinvPole := one_sub_rpow_neg_inv_le hrho
  have hinvPole0 : 0 ≤ (1 - (3 : ℝ) ^ (-rho))⁻¹ :=
    (inv_pos.mpr (one_sub_rpow_neg_pos hrho)).le
  have hpowPole :
      ((1 - (3 : ℝ) ^ (-rho))⁻¹) ^ (5 : ℕ) ≤
        (1 + rho⁻¹) ^ (5 : ℕ) :=
    pow_le_pow_left₀ hinvPole0 hinvPole 5
  have hgrid' :
      ∑' n : ℕ, (((n : ℝ) + 1) ^ (4 : ℕ)) * gridWeight rho n ≤
        24 * (1 + rho⁻¹) ^ (5 : ℕ) := by
    calc
      _ ≤ (Nat.factorial 4 : ℝ) *
          ((1 - (3 : ℝ) ^ (-rho))⁻¹) ^ (4 + 1) := hgrid
      _ ≤ (Nat.factorial 4 : ℝ) * (1 + rho⁻¹) ^ (5 : ℕ) := by
        have hmul := mul_le_mul_of_nonneg_left hpowPole
          (show (0 : ℝ) ≤ (24 : ℝ) by norm_num)
        simpa [Nat.factorial] using hmul
      _ = 24 * (1 + rho⁻¹) ^ (5 : ℕ) := by norm_num [Nat.factorial]
  have hgrid'' :
      ∑' n : ℕ, gridWeight rho n * (((n : ℝ) + 1) ^ (4 : ℕ)) ≤
        24 * (1 + rho⁻¹) ^ (5 : ℕ) := by
    simpa [mul_comm] using hgrid'
  have hend := tsum_endpointWeight_mul_le
    (rho := rho) (f := fun n : ℕ => (((n : ℝ) + 1) ^ (4 : ℕ))) hgrid''
  have hthree : ((3 : ℝ) ^ (-rho))⁻¹ ≤ 9 := by
    have hpow : (3 : ℝ) ^ rho ≤ (3 : ℝ) ^ (2 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le (by norm_num) hrhoTwo
    have heq : ((3 : ℝ) ^ (-rho))⁻¹ = (3 : ℝ) ^ rho := by
      rw [Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 3)]
      exact inv_inv _
    rw [heq]
    norm_num at hpow ⊢
    exact hpow
  have hpole := poleBracket_le (rho := rho) (eps := eps) (ctop := (0 : ℝ))
    4 heps hepsOne hwindow (by norm_num)
  have hpole' : 24 * (1 + rho⁻¹) ^ (5 : ℕ) ≤
      768 * eps⁻¹ ^ (5 : ℕ) := by
    norm_num [Nat.factorial] at hpole ⊢
    exact hpole
  have hleft0 : 0 ≤ 24 * (1 + rho⁻¹) ^ (5 : ℕ) := by
    have : 0 ≤ rho⁻¹ := (inv_pos.mpr hrho).le
    positivity
  have hright0 : 0 ≤ 768 * eps⁻¹ ^ (5 : ℕ) := by positivity
  calc
    ∑' n : ℕ, (((n : ℝ) + 1) ^ (4 : ℕ)) * endpointWeight rho n ≤
        ((3 : ℝ) ^ (-rho))⁻¹ *
          (24 * (1 + rho⁻¹) ^ (5 : ℕ)) := by
      simpa [mul_comm] using hend
    _ ≤ 9 * (768 * eps⁻¹ ^ (5 : ℕ)) :=
      mul_le_mul hthree hpole' hleft0 (by norm_num)
    _ = superposedFluxLowerPoleConst * eps⁻¹ ^ (5 : ℕ) := by
      unfold superposedFluxLowerPoleConst
      ring

/-- The source scale restriction upgrades the frozen inverse-square factor to
at least the output constant, using the output theorem's own exponential
admissibility gate. -/
theorem outputConst_le_invSq_mul_gammaInv_of_gate
    (M : ABKModel d) {C sigma E : ℝ}
    (hC : 0 ≤ C) (hsigma : 0 < sigma) (hsigmaHalf : sigma ≤ 1 / 2)
    (hE : 1 ≤ E) (hgate : Real.exp (C / sigma) ≤ E)
    (hgamma : M.gamma ≤ E ^ (-5 : ℤ)) :
    C ≤ E⁻¹ ^ 2 * M.gamma⁻¹ := by
  have hsigmaOne : sigma ≤ 1 := hsigmaHalf.trans (by norm_num)
  have hCdiv : C ≤ C / sigma := by
    rw [le_div_iff₀ hsigma]
    nlinarith
  have hCexp : C ≤ Real.exp (C / sigma) := by
    have hexp := Real.add_one_le_exp (C / sigma)
    linarith
  have hEcub : E ≤ E ^ (3 : ℕ) := by
    have hE0 : 0 ≤ E := le_trans zero_le_one hE
    have hE2 : (1 : ℝ) ≤ E ^ (2 : ℕ) := one_le_pow₀ hE
    calc
      E = E * 1 := by ring
      _ ≤ E * E ^ (2 : ℕ) := mul_le_mul_of_nonneg_left hE2 hE0
      _ = E ^ (3 : ℕ) := by ring
  exact hCexp.trans (hgate.trans (hEcub.trans
    (cube_le_invSq_mul_gammaInv M hE hgamma)))

/-- A fixed prefactor can be absorbed using the output constant itself as a
lower bound for `E⁻² gamma⁻¹`.  This is the large-parameter refinement of
the elementary exponential gate used for the final lower budget. -/
theorem prefactor_mul_exp_le_frozenRare_pow
    {K c C X : ℝ} {p : ℕ}
    (hK : 0 ≤ K) (hC : 0 < C) (hX : C ≤ X)
    (hchoice : K + (p : ℝ) ≤ c * C) :
    K * Real.exp (-(c * X)) ≤ Real.exp (-(C⁻¹ * X)) ^ p := by
  have hKexp : K ≤ Real.exp K := by
    linarith [Real.add_one_le_exp K]
  have hcoef : 0 ≤ c - (p : ℝ) * C⁻¹ := by
    have hpC : (p : ℝ) ≤ c * C := by linarith
    have hpdiv : (p : ℝ) / C ≤ c := (div_le_iff₀ hC).2 (by
      simpa [mul_comm] using hpC)
    rw [div_eq_mul_inv] at hpdiv
    linarith
  have hKC : K ≤ (c - (p : ℝ) * C⁻¹) * C := by
    have hCne : C ≠ 0 := ne_of_gt hC
    calc
      K ≤ c * C - (p : ℝ) := by linarith
      _ = (c - (p : ℝ) * C⁻¹) * C := by field_simp
  have hKX : K ≤ (c - (p : ℝ) * C⁻¹) * X :=
    hKC.trans (mul_le_mul_of_nonneg_left hX hcoef)
  have hexp : K - c * X ≤ -((p : ℝ) * C⁻¹ * X) := by
    linarith
  calc
    K * Real.exp (-(c * X)) ≤ Real.exp K * Real.exp (-(c * X)) :=
      mul_le_mul_of_nonneg_right hKexp (Real.exp_pos _).le
    _ = Real.exp (K - c * X) := by rw [← Real.exp_add]; ring_nf
    _ ≤ Real.exp (-((p : ℝ) * C⁻¹ * X)) := Real.exp_le_exp.mpr hexp
    _ = Real.exp (-(C⁻¹ * X)) ^ p := by
      rw [← Real.exp_nat_mul]
      congr 1
      ring

/-! ## Rooted finite-exponent and endpoint weights -/

theorem geometricWeight_rpow_two_div_eq_endpointWeight
    {s q : ℝ} (hsq : 0 ≤ s * q) (hq : q ≠ 0) (n : ℕ) :
    Book.Ch02.geometricWeight s q n ^ (2 / q) =
      gridSumConst s q * endpointWeight (2 * s) n := by
  cases n with
  | zero =>
      simpa [endpointWeight_zero] using geometricWeight_rpow_zero s q
  | succ k =>
      simpa [endpointWeight, gridWeight] using geometricWeight_rpow_succ hsq hq k

theorem gridSumConst_le_one {s q : ℝ} (hs : 0 < s) (hq : 0 < q) :
    gridSumConst s q ≤ 1 := by
  have hsq : 0 ≤ s * q := (mul_pos hs hq).le
  have hdisc0 : 0 ≤ Book.Ch02.geometricDiscount s q :=
    Book.Ch02.book_geometricDiscount_nonneg hsq
  have hdisc1 : Book.Ch02.geometricDiscount s q ≤ 1 := by
    unfold Book.Ch02.geometricDiscount
    exact sub_le_self 1 (Real.rpow_nonneg (by norm_num) _)
  exact Real.rpow_le_one hdisc0 hdisc1 (by positivity)

private theorem rootedWeight_mul_depthAmp_eq
    (M : ABKModel d) (E s q : ℝ) (n : ℕ)
    (hsq : 0 ≤ s * q) (hq : q ≠ 0) :
    Book.Ch02.geometricWeight s q n ^ (2 / q) *
        superposedFluxDepthAmpProfile M E n =
      (gridSumConst s q * superposedFluxDepthAmpConst d *
          Real.exp (-(superposedFluxBfaRate d * (E⁻¹ ^ 2 * M.gamma⁻¹)))) *
        ((((n : ℝ) + 1) ^ (4 : ℕ)) *
          endpointWeight (2 * s - M.gamma) n) := by
  have hcollar : endpointWeight (2 * s) n *
      (3 : ℝ) ^ (M.gamma * (n : ℝ)) =
        endpointWeight (2 * s - M.gamma) n := by
    rw [endpointWeight_eq_rpow]
    convert rpow_collar_eq_endpointWeight s M.gamma n using 1
    all_goals ring_nf
  rw [geometricWeight_rpow_two_div_eq_endpointWeight hsq hq]
  unfold superposedFluxDepthAmpProfile
  calc
    _ = (gridSumConst s q * superposedFluxDepthAmpConst d *
          Real.exp (-(superposedFluxBfaRate d * (E⁻¹ ^ 2 * M.gamma⁻¹))) *
          (((n : ℝ) + 1) ^ (4 : ℕ))) *
        (endpointWeight (2 * s) n *
          (3 : ℝ) ^ (M.gamma * (n : ℝ))) := by ring
    _ = (gridSumConst s q * superposedFluxDepthAmpConst d *
          Real.exp (-(superposedFluxBfaRate d * (E⁻¹ ^ 2 * M.gamma⁻¹))) *
          (((n : ℝ) + 1) ^ (4 : ℕ))) *
        endpointWeight (2 * s - M.gamma) n := by rw [hcollar]
    _ = _ := by ring

private theorem endpointWeight_mul_depthAmp_eq
    (M : ABKModel d) (E s : ℝ) (n : ℕ) :
    endpointWeight (2 * s) n * superposedFluxDepthAmpProfile M E n =
      (superposedFluxDepthAmpConst d *
          Real.exp (-(superposedFluxBfaRate d * (E⁻¹ ^ 2 * M.gamma⁻¹)))) *
        ((((n : ℝ) + 1) ^ (4 : ℕ)) *
          endpointWeight (2 * s - M.gamma) n) := by
  have hcollar : endpointWeight (2 * s) n *
      (3 : ℝ) ^ (M.gamma * (n : ℝ)) =
        endpointWeight (2 * s - M.gamma) n := by
    rw [endpointWeight_eq_rpow]
    convert rpow_collar_eq_endpointWeight s M.gamma n using 1
    all_goals ring_nf
  unfold superposedFluxDepthAmpProfile
  calc
    _ = (superposedFluxDepthAmpConst d *
          Real.exp (-(superposedFluxBfaRate d * (E⁻¹ ^ 2 * M.gamma⁻¹))) *
          (((n : ℝ) + 1) ^ (4 : ℕ))) *
        (endpointWeight (2 * s) n *
          (3 : ℝ) ^ (M.gamma * (n : ℝ))) := by ring
    _ = (superposedFluxDepthAmpConst d *
          Real.exp (-(superposedFluxBfaRate d * (E⁻¹ ^ 2 * M.gamma⁻¹))) *
          (((n : ℝ) + 1) ^ (4 : ℕ))) *
        endpointWeight (2 * s - M.gamma) n := by rw [hcollar]
    _ = _ := by ring

theorem summable_rootedWeight_mul_depthAmp
    (M : ABKModel d) (E : ℝ) {s q : ℝ}
    (hs : 0 < s) (hq : 0 < q) (hgap : 0 < 2 * s - M.gamma) :
    Summable fun n : ℕ =>
      Book.Ch02.geometricWeight s q n ^ (2 / q) *
        superposedFluxDepthAmpProfile M E n := by
  have hcore := summable_poly_mul_endpointWeight (2 * s - M.gamma) hgap
  have hscaled := hcore.mul_left
    (gridSumConst s q * superposedFluxDepthAmpConst d *
      Real.exp (-(superposedFluxBfaRate d * (E⁻¹ ^ 2 * M.gamma⁻¹))))
  exact hscaled.congr fun n =>
    (rootedWeight_mul_depthAmp_eq M E s q n (mul_pos hs hq).le hq.ne').symm

theorem summable_geometricWeight_rpow_two_div
    {s q : ℝ} (hs : 0 < s) (hq : 0 < q) :
    Summable fun n : ℕ => Book.Ch02.geometricWeight s q n ^ (2 / q) := by
  have hcore : Summable fun n : ℕ => endpointWeight (2 * s) n := by
    have hgrid : Summable fun n : ℕ => gridWeight (2 * s) n * (1 : ℝ) := by
      simpa using (gridWeight_summable (by linarith : 0 < 2 * s)).mul_right (1 : ℝ)
    simpa using summable_endpointWeight_mul hgrid
  have hscaled := hcore.mul_left (gridSumConst s q)
  exact hscaled.congr fun n =>
    (geometricWeight_rpow_two_div_eq_endpointWeight (mul_pos hs hq).le hq.ne' n).symm

theorem summable_endpointWeight_mul_depthAmp
    (M : ABKModel d) (E : ℝ) {s : ℝ}
    (hgap : 0 < 2 * s - M.gamma) :
    Summable fun n : ℕ =>
      endpointWeight (2 * s) n * superposedFluxDepthAmpProfile M E n := by
  have hcore := summable_poly_mul_endpointWeight (2 * s - M.gamma) hgap
  have hscaled := hcore.mul_left
    (superposedFluxDepthAmpConst d *
      Real.exp (-(superposedFluxBfaRate d * (E⁻¹ ^ 2 * M.gamma⁻¹))))
  exact hscaled.congr fun n => (endpointWeight_mul_depthAmp_eq M E s n).symm

/-- Uniform budget for either the rooted finite-exponent linear series or the
endpoint series. -/
theorem tsum_rootedWeight_mul_depthAmp_le
    (hd : 2 ≤ d) (M : ABKModel d) (E : ℝ) {s q eps : ℝ}
    (hs : 0 < s) (hsOne : s ≤ 1) (hq : 0 < q)
    (heps : 0 < eps) (hepsOne : eps ≤ 1)
    (hwindow : M.gamma / 2 + eps ≤ s) :
    ∑' n : ℕ, Book.Ch02.geometricWeight s q n ^ (2 / q) *
        superposedFluxDepthAmpProfile M E n ≤
      superposedFluxDepthAmpConst d * superposedFluxLowerPoleConst *
        Real.exp (-(superposedFluxBfaRate d * (E⁻¹ ^ 2 * M.gamma⁻¹))) *
        eps⁻¹ ^ (5 : ℕ) := by
  have hgap : 0 < 2 * s - M.gamma := by linarith
  have hgapTwo : 2 * s - M.gamma ≤ 2 := by
    linarith [M.shellPrefix.gamma_pos]
  have hwin : 2 * eps ≤ 2 * s - M.gamma := by linarith
  have hcore := tsum_poly_mul_endpointWeight_le_frozenPole hgap hgapTwo
    heps hepsOne hwin
  have hconst0 : 0 ≤ gridSumConst s q * superposedFluxDepthAmpConst d *
      Real.exp (-(superposedFluxBfaRate d * (E⁻¹ ^ 2 * M.gamma⁻¹))) :=
    mul_nonneg (mul_nonneg (gridSumConst_nonneg (mul_pos hs hq).le)
      (superposedFluxDepthAmpConst_pos hd).le) (Real.exp_pos _).le
  have heq :
      (∑' n : ℕ, Book.Ch02.geometricWeight s q n ^ (2 / q) *
          superposedFluxDepthAmpProfile M E n) =
        (gridSumConst s q * superposedFluxDepthAmpConst d *
          Real.exp (-(superposedFluxBfaRate d * (E⁻¹ ^ 2 * M.gamma⁻¹)))) *
          (∑' n : ℕ, (((n : ℝ) + 1) ^ (4 : ℕ)) *
            endpointWeight (2 * s - M.gamma) n) := by
    rw [← tsum_mul_left]
    exact tsum_congr fun n => rootedWeight_mul_depthAmp_eq M E s q n
      (mul_pos hs hq).le hq.ne'
  rw [heq]
  calc
    _ ≤ (gridSumConst s q * superposedFluxDepthAmpConst d *
          Real.exp (-(superposedFluxBfaRate d * (E⁻¹ ^ 2 * M.gamma⁻¹)))) *
        (superposedFluxLowerPoleConst * eps⁻¹ ^ (5 : ℕ)) :=
      mul_le_mul_of_nonneg_left hcore hconst0
    _ ≤ (1 * superposedFluxDepthAmpConst d *
          Real.exp (-(superposedFluxBfaRate d * (E⁻¹ ^ 2 * M.gamma⁻¹)))) *
        (superposedFluxLowerPoleConst * eps⁻¹ ^ (5 : ℕ)) := by
      have hrest0 : 0 ≤ superposedFluxDepthAmpConst d *
          Real.exp (-(superposedFluxBfaRate d * (E⁻¹ ^ 2 * M.gamma⁻¹))) *
          (superposedFluxLowerPoleConst * eps⁻¹ ^ (5 : ℕ)) := by
        exact mul_nonneg
          (mul_nonneg (superposedFluxDepthAmpConst_pos hd).le (Real.exp_pos _).le)
          (mul_nonneg superposedFluxLowerPoleConst_pos.le (by positivity))
      have hmass := mul_le_mul_of_nonneg_right (gridSumConst_le_one hs hq) hrest0
      calc
        (gridSumConst s q * superposedFluxDepthAmpConst d *
              Real.exp (-(superposedFluxBfaRate d * (E⁻¹ ^ 2 * M.gamma⁻¹)))) *
            (superposedFluxLowerPoleConst * eps⁻¹ ^ (5 : ℕ))
            = gridSumConst s q * (superposedFluxDepthAmpConst d *
                Real.exp (-(superposedFluxBfaRate d * (E⁻¹ ^ 2 * M.gamma⁻¹))) *
                (superposedFluxLowerPoleConst * eps⁻¹ ^ (5 : ℕ))) := by ring
        _ ≤ 1 * (superposedFluxDepthAmpConst d *
                Real.exp (-(superposedFluxBfaRate d * (E⁻¹ ^ 2 * M.gamma⁻¹))) *
                (superposedFluxLowerPoleConst * eps⁻¹ ^ (5 : ℕ))) := hmass
        _ = (1 * superposedFluxDepthAmpConst d *
              Real.exp (-(superposedFluxBfaRate d * (E⁻¹ ^ 2 * M.gamma⁻¹)))) *
            (superposedFluxLowerPoleConst * eps⁻¹ ^ (5 : ℕ)) := by ring
    _ = _ := by ring

theorem tsum_endpointWeight_mul_depthAmp_le
    (hd : 2 ≤ d) (M : ABKModel d) (E : ℝ) {s eps : ℝ}
    (hsOne : s ≤ 1) (heps : 0 < eps) (hepsOne : eps ≤ 1)
    (hwindow : M.gamma / 2 + eps ≤ s) :
    ∑' n : ℕ, endpointWeight (2 * s) n *
        superposedFluxDepthAmpProfile M E n ≤
      superposedFluxDepthAmpConst d * superposedFluxLowerPoleConst *
        Real.exp (-(superposedFluxBfaRate d * (E⁻¹ ^ 2 * M.gamma⁻¹))) *
        eps⁻¹ ^ (5 : ℕ) := by
  have hgap : 0 < 2 * s - M.gamma := by linarith
  have hgapTwo : 2 * s - M.gamma ≤ 2 := by
    linarith [M.shellPrefix.gamma_pos]
  have hwin : 2 * eps ≤ 2 * s - M.gamma := by linarith
  have hcore := tsum_poly_mul_endpointWeight_le_frozenPole hgap hgapTwo
    heps hepsOne hwin
  have hconst0 : 0 ≤ superposedFluxDepthAmpConst d *
      Real.exp (-(superposedFluxBfaRate d * (E⁻¹ ^ 2 * M.gamma⁻¹))) :=
    mul_nonneg (superposedFluxDepthAmpConst_pos hd).le (Real.exp_pos _).le
  have heq :
      (∑' n : ℕ, endpointWeight (2 * s) n *
          superposedFluxDepthAmpProfile M E n) =
        (superposedFluxDepthAmpConst d *
          Real.exp (-(superposedFluxBfaRate d * (E⁻¹ ^ 2 * M.gamma⁻¹)))) *
          (∑' n : ℕ, (((n : ℝ) + 1) ^ (4 : ℕ)) *
            endpointWeight (2 * s - M.gamma) n) := by
    rw [← tsum_mul_left]
    exact tsum_congr fun n => endpointWeight_mul_depthAmp_eq M E s n
  rw [heq]
  calc
    _ ≤ (superposedFluxDepthAmpConst d *
          Real.exp (-(superposedFluxBfaRate d * (E⁻¹ ^ 2 * M.gamma⁻¹)))) *
        (superposedFluxLowerPoleConst * eps⁻¹ ^ (5 : ℕ)) :=
      mul_le_mul_of_nonneg_left hcore hconst0
    _ = _ := by ring

end

end Algsuperdiff.Section3.Provider.CoarseEllipticity
