/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.ExcessDecay.CoarseAssemblyBudget
public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.ExcessDecay.EnnrealShell

/-!
# AssemblyArith

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


namespace Algsuperdiff.Section4.Provider.ExcessDecay

noncomputable section

/-! ## 1. The two `σ` square-root moves -/

/-- `√a · a⁻¹ = √(a⁻¹)`: the move that turns the boundary Caccioppoli
prefactor's `σ^{1/2}` against the datum pricing's `λ^{-1} ≤ K σ^{-1}` into the
force leg's `σ^{-1/2}`. -/
theorem sqrt_mul_inv_eq_sqrt_inv {a : ℝ} (ha : 0 < a) :
    Real.sqrt a * a⁻¹ = Real.sqrt a⁻¹ := by
  have hs : 0 < Real.sqrt a := Real.sqrt_pos.mpr ha
  have hsq : Real.sqrt a * a⁻¹ = Real.sqrt a * (Real.sqrt a * Real.sqrt a)⁻¹ := by
    rw [Real.mul_self_sqrt ha.le]
  rw [Real.sqrt_inv, hsq, mul_inv, ← mul_assoc, mul_inv_cancel₀ hs.ne', one_mul]

/-! ## 2. Two numerals -/

/-- `2^2 = 4`, read on `Real.rpow`. -/
theorem rpow_two_two_eq_four : Real.rpow (2 : ℝ) (2 : ℝ) = 4 := by
  rw [Real.rpow_eq_pow, show (2 : ℝ) = ((2 : ℕ) : ℝ) from by norm_num, Real.rpow_natCast]
  norm_num

/-- `2^3 = 8`, read on `Real.rpow`. -/
theorem rpow_two_three_eq_eight : Real.rpow (2 : ℝ) (3 : ℝ) = 8 := by
  rw [Real.rpow_eq_pow, show (3 : ℝ) = ((3 : ℕ) : ℝ) from by norm_num, Real.rpow_natCast]
  norm_num

/-- `2^{3/2} ≤ 3`.  Proved by squaring, with the transcendental atom made opaque
before the nonlinear step. -/
theorem rpow_two_threeHalves_le_three : Real.rpow (2 : ℝ) (3 / 2 : ℝ) ≤ 3 := by
  have hnn : (0 : ℝ) ≤ Real.rpow (2 : ℝ) (3 / 2 : ℝ) :=
    Real.rpow_nonneg (by norm_num) _
  have hsq : Real.rpow (2 : ℝ) (3 / 2 : ℝ) * Real.rpow (2 : ℝ) (3 / 2 : ℝ) = 8 := by
    rw [rpow_mul_rpow_of_add (by norm_num : (0 : ℝ) < 2) _ _ (3 : ℝ) (by norm_num),
      rpow_two_three_eq_eight]
  set t : ℝ := Real.rpow (2 : ℝ) (3 / 2 : ℝ) with ht
  clear_value t
  clear ht
  nlinarith only [hnn, hsq]

/-- `2^{1/2} ≤ 2`.  Same pattern. -/
theorem rpow_two_half_le_two : Real.rpow (2 : ℝ) (1 / 2 : ℝ) ≤ 2 := by
  have hnn : (0 : ℝ) ≤ Real.rpow (2 : ℝ) (1 / 2 : ℝ) :=
    Real.rpow_nonneg (by norm_num) _
  have hsq : Real.rpow (2 : ℝ) (1 / 2 : ℝ) * Real.rpow (2 : ℝ) (1 / 2 : ℝ) = 2 := by
    rw [rpow_mul_rpow_of_add (by norm_num : (0 : ℝ) < 2) _ _ (1 : ℝ) (by norm_num),
      Real.rpow_eq_pow, Real.rpow_one]
  set t : ℝ := Real.rpow (2 : ℝ) (1 / 2 : ℝ) with ht
  clear_value t
  clear ht
  nlinarith only [hnn, hsq]

/-! ## 3. The pin's canonical `s`-powers -/

/-- **Rows 4/5, canonical form.**  `(s/2)^{-3/2} · (s/2)^{-3/2} = 8 s^{-3}`;
against the envelope's `s^{-4}` this is the frozen force leg `s^{-7}`. -/
theorem pin_force_sq {s : ℝ} (hs : 0 < s) :
    Real.rpow (s / 2) (-(3 / 2 : ℝ)) * Real.rpow (s / 2) (-(3 / 2 : ℝ)) =
      8 * Real.rpow s (-(3 : ℝ)) := by
  have h32 := rpow_half_arg_neg hs.le (3 / 2 : ℝ)
  have htwo : Real.rpow (2 : ℝ) (3 / 2 : ℝ) * Real.rpow (2 : ℝ) (3 / 2 : ℝ) =
      Real.rpow (2 : ℝ) (3 : ℝ) :=
    rpow_mul_rpow_of_add (by norm_num) _ _ _ (by norm_num)
  have hsum : Real.rpow s (-(3 / 2 : ℝ)) * Real.rpow s (-(3 / 2 : ℝ)) =
      Real.rpow s (-(3 : ℝ)) := rpow_mul_rpow_of_add hs _ _ _ (by norm_num)
  calc Real.rpow (s / 2) (-(3 / 2 : ℝ)) * Real.rpow (s / 2) (-(3 / 2 : ℝ))
      = (Real.rpow (2 : ℝ) (3 / 2 : ℝ) * Real.rpow (2 : ℝ) (3 / 2 : ℝ)) *
          (Real.rpow s (-(3 / 2 : ℝ)) * Real.rpow s (-(3 / 2 : ℝ))) := by
        rw [h32]; ring
    _ = 8 * Real.rpow s (-(3 : ℝ)) := by
        rw [htwo, hsum, rpow_two_three_eq_eight]

/-- **Row 6, canonical form — the leg that fits the frozen display at
equality.**  `(s/2)^{-3/2} · (s/2)^{-1/2} = 4 s^{-2}`; against the envelope's
`s^{-4}` this is exactly `4 s^{-6}`, the frozen display's legs 4 and 5, with
**no slack in the exponent**. -/
theorem pin_gradh_prod {s : ℝ} (hs : 0 < s) :
    Real.rpow (s / 2) (-(3 / 2 : ℝ)) * Real.rpow (s / 2) (-(1 / 2 : ℝ)) =
      4 * Real.rpow s (-(2 : ℝ)) := by
  have h32 := rpow_half_arg_neg hs.le (3 / 2 : ℝ)
  have h12 := rpow_half_arg_neg hs.le (1 / 2 : ℝ)
  have htwo : Real.rpow (2 : ℝ) (3 / 2 : ℝ) * Real.rpow (2 : ℝ) (1 / 2 : ℝ) =
      Real.rpow (2 : ℝ) (2 : ℝ) :=
    rpow_mul_rpow_of_add (by norm_num) _ _ _ (by norm_num)
  have hsum : Real.rpow s (-(3 / 2 : ℝ)) * Real.rpow s (-(1 / 2 : ℝ)) =
      Real.rpow s (-(2 : ℝ)) := rpow_mul_rpow_of_add hs _ _ _ (by norm_num)
  calc Real.rpow (s / 2) (-(3 / 2 : ℝ)) * Real.rpow (s / 2) (-(1 / 2 : ℝ))
      = (Real.rpow (2 : ℝ) (3 / 2 : ℝ) * Real.rpow (2 : ℝ) (1 / 2 : ℝ)) *
          (Real.rpow s (-(3 / 2 : ℝ)) * Real.rpow s (-(1 / 2 : ℝ))) := by
        rw [h32, h12]; ring
    _ = 4 * Real.rpow s (-(2 : ℝ)) := by
        rw [htwo, hsum, rpow_two_two_eq_four]

/-- **Row 4, canonical form.**  `(s/2)^{-3} = 8 s^{-3}`. -/
theorem pin_force_cube {s : ℝ} (hs : 0 < s) :
    Real.rpow (s / 2) (-(3 : ℝ)) = 8 * Real.rpow s (-(3 : ℝ)) := by
  rw [rpow_half_arg_neg hs.le (3 : ℝ), rpow_two_three_eq_eight]

/-- **Row 2, canonical form (with slack).**  `(s/2)^{-3/2} ≤ 3 s^{-3}` on
`s ∈ (0,1]`. -/
theorem pin_force_half_le {s : ℝ} (hs : 0 < s) (hs1 : s ≤ 1) :
    Real.rpow (s / 2) (-(3 / 2 : ℝ)) ≤ 3 * Real.rpow s (-(3 : ℝ)) := by
  have h32 := rpow_half_arg_neg hs.le (3 / 2 : ℝ)
  have hmono : Real.rpow s (-(3 / 2 : ℝ)) ≤ Real.rpow s (-(3 : ℝ)) :=
    Real.rpow_le_rpow_of_exponent_ge hs hs1 (by norm_num)
  have hnn : (0 : ℝ) ≤ Real.rpow s (-(3 / 2 : ℝ)) := Real.rpow_nonneg hs.le _
  calc Real.rpow (s / 2) (-(3 / 2 : ℝ))
      = Real.rpow (2 : ℝ) (3 / 2 : ℝ) * Real.rpow s (-(3 / 2 : ℝ)) := h32
    _ ≤ 3 * Real.rpow s (-(3 / 2 : ℝ)) :=
        mul_le_mul_of_nonneg_right rpow_two_threeHalves_le_three hnn
    _ ≤ 3 * Real.rpow s (-(3 : ℝ)) := mul_le_mul_of_nonneg_left hmono (by norm_num)

/-- **Row 1, canonical form (with slack).**  `(s/2)^{-1/2} ≤ 2 s^{-2}` on
`s ∈ (0,1]`. -/
theorem pin_gradh_half_le {s : ℝ} (hs : 0 < s) (hs1 : s ≤ 1) :
    Real.rpow (s / 2) (-(1 / 2 : ℝ)) ≤ 2 * Real.rpow s (-(2 : ℝ)) := by
  have h12 := rpow_half_arg_neg hs.le (1 / 2 : ℝ)
  have hmono : Real.rpow s (-(1 / 2 : ℝ)) ≤ Real.rpow s (-(2 : ℝ)) :=
    Real.rpow_le_rpow_of_exponent_ge hs hs1 (by norm_num)
  have hnn : (0 : ℝ) ≤ Real.rpow s (-(1 / 2 : ℝ)) := Real.rpow_nonneg hs.le _
  calc Real.rpow (s / 2) (-(1 / 2 : ℝ))
      = Real.rpow (2 : ℝ) (1 / 2 : ℝ) * Real.rpow s (-(1 / 2 : ℝ)) := h12
    _ ≤ 2 * Real.rpow s (-(1 / 2 : ℝ)) :=
        mul_le_mul_of_nonneg_right rpow_two_half_le_two hnn
    _ ≤ 2 * Real.rpow s (-(2 : ℝ)) := mul_le_mul_of_nonneg_left hmono (by norm_num)

/-- **Row 3, canonical form (with slack).**  `s^{-1/2} ≤ s^{-2}`: the datum
pricing's crude datum leg proves inside the frozen display's fifth leg. -/
theorem rpow_neg_half_le_neg_two {s : ℝ} (hs : 0 < s) (hs1 : s ≤ 1) :
    Real.rpow s (-(1 / 2 : ℝ)) ≤ Real.rpow s (-(2 : ℝ)) :=
  Real.rpow_le_rpow_of_exponent_ge hs hs1 (by norm_num)

/-- `1 ≤ s^{-2}` on `s ∈ (0,1]`: the `s`-power-free data Poincaré leg proves inside
the frozen display's fifth leg. -/
theorem one_le_rpow_neg_two {s : ℝ} (hs : 0 < s) (hs1 : s ≤ 1) :
    (1 : ℝ) ≤ Real.rpow s (-(2 : ℝ)) := by
  have h := Real.rpow_le_rpow_of_exponent_ge hs hs1 (show (-(2 : ℝ)) ≤ (0 : ℝ) by norm_num)
  rwa [Real.rpow_zero] at h

/-- The envelope's `s^{-4}` against the canonical `s^{-2}`: the frozen
display's legs 4 and 5. -/
theorem rpow_neg_four_mul_neg_two {s : ℝ} (hs : 0 < s) :
    Real.rpow s (-(4 : ℝ)) * Real.rpow s (-(2 : ℝ)) = Real.rpow s (-(6 : ℝ)) :=
  rpow_mul_rpow_of_add hs _ _ _ (by norm_num)

/-! ## 4. The boundary energy assembly, on abstract letters -/

/-- **Raising a five-leg bound to a joint constant.** -/
theorem five_leg_bound {K c1 c2 c3 c4 c5 L1 L2 L3 L4 L5 T : ℝ}
    (hT : T ≤ c1 * L1 + c2 * L2 + c3 * L3 + c4 * L4 + c5 * L5)
    (h1 : c1 ≤ K) (h2 : c2 ≤ K) (h3 : c3 ≤ K) (h4 : c4 ≤ K) (h5 : c5 ≤ K)
    (hL1 : 0 ≤ L1) (hL2 : 0 ≤ L2) (hL3 : 0 ≤ L3) (hL4 : 0 ≤ L4) (hL5 : 0 ≤ L5) :
    T ≤ K * (L1 + L2 + L3 + L4 + L5) := by
  have e1 := mul_le_mul_of_nonneg_right h1 hL1
  have e2 := mul_le_mul_of_nonneg_right h2 hL2
  have e3 := mul_le_mul_of_nonneg_right h3 hL3
  have e4 := mul_le_mul_of_nonneg_right h4 hL4
  have e5 := mul_le_mul_of_nonneg_right h5 hL5
  have hexp : K * (L1 + L2 + L3 + L4 + L5) =
      K * L1 + K * L2 + K * L3 + K * L4 + K * L5 := by ring
  rw [hexp]
  linarith only [hT, e1, e2, e3, e4, e5]

/-- Cap one error-weighted leg and enlarge a joint five-leg constant. -/
theorem five_leg_bound_errorWeighted {K C E L1 L2 L3 L4 L5 T : ℝ}
    (hK : 0 ≤ K) (hE : E ≤ C)
    (hL1 : 0 ≤ L1) (hL2 : 0 ≤ L2) (hL3 : 0 ≤ L3) (hL4 : 0 ≤ L4) (hL5 : 0 ≤ L5)
    (hT : T ≤ K * (L1 + L2 + L3 + E * L4 + L5)) :
    T ≤ (K * max 1 C) * (L1 + L2 + L3 + L4 + L5) := by
  have hKmax : K ≤ K * max 1 C := by
    simpa only [mul_one] using mul_le_mul_of_nonneg_left (le_max_left (1 : ℝ) C) hK
  have hKEmax : K * E ≤ K * max 1 C :=
    mul_le_mul_of_nonneg_left (hE.trans (le_max_right 1 C)) hK
  have hT' : T ≤ K * L1 + K * L2 + K * L3 + (K * E) * L4 + K * L5 := by
    calc T ≤ K * (L1 + L2 + L3 + E * L4 + L5) := hT
      _ = _ := by ring
  exact five_leg_bound hT' hKmax hKmax hKmax hKEmax hKmax hL1 hL2 hL3 hL4 hL5

/-- **The boundary energy assembly's arithmetic.**

`T` is the square root of the boundary Caccioppoli's left-hand side, `alpha rs`
its prefactor after the two coarse caps, `beta` the direct Dirichlet-energy
prefactor, and the remaining letters are the atoms of the parent-`L²` pricing,
the composed datum pricing and the two Dirichlet-energy legs (all of them
nonnegative reals).  The conclusion prices `T` onto the five canonical legs

```text
  rs P2 X ,   rs P2 S ,   Sm3 ri Q3s Gs ,   Sm2 rs Q3s Hs ,   Sm2 rs H ,
```

which are exactly the shapes the `σ`-frame division turns into the frozen
display's first, scalar, force, `[∇h]` and `‖∇h‖` legs. -/
theorem boundary_energy_arith
    {T alpha beta rs ri sig sK KR CG1 CG2 CB2 gP dd D3 sd negC Cbg Cgw
      P2 Q3s Sm3 Sm2 X S H Gs Hs p32 p12 p3 low lamInv Bg Hn negf DirG DirB : ℝ}
    (halpha : 0 ≤ alpha) (hbeta : 0 ≤ beta) (hrs : 0 ≤ rs) (hri : 0 ≤ ri)
    (hsK : 0 ≤ sK) (hKR : 0 ≤ KR) (hCG1 : 0 ≤ CG1) (hCB2 : 0 ≤ CB2)
    (hgP : 0 ≤ gP) (hdd : 0 ≤ dd) (hD3 : 0 ≤ D3) (hsd : 0 ≤ sd)
    (hCbg : 0 ≤ Cbg) (hCgw : 0 ≤ Cgw) (hQ3s : 0 ≤ Q3s)
    (hSm2 : 0 ≤ Sm2) (hH : 0 ≤ H) (hGs : 0 ≤ Gs) (hHs : 0 ≤ Hs) (hp32 : 0 ≤ p32)
    (hp3 : 0 ≤ p3) (hBg0 : 0 ≤ Bg) (hHn0 : 0 ≤ Hn)
    (hDirG0 : 0 ≤ DirG) (hsig : 0 < sig)
    (hrsri : rs * ri = 1) (hrssig : rs * sig⁻¹ = ri) (hsKsq : sK * sK = KR)
    (hpp3 : p32 * p32 = 8 * Sm3) (hpp2 : p32 * p12 = 4 * Sm2)
    (hp3eq : p3 = 8 * Sm3) (hp32le : p32 ≤ 3 * Sm3) (hp12le : p12 ≤ 2 * Sm2)
    (hone : 1 ≤ Sm2)
    (hlowle : low ≤ sK * ri) (hlamInvle : lamInv ≤ KR * sig⁻¹)
    (hBgle : Bg ≤ Cbg * Q3s * (Cgw * Gs)) (hHnle : Hn ≤ sd * D3 * H)
    (hnegfle : negf ≤ negC * Sm2) (hnegC : 0 ≤ negC)
    (hDirGle : DirG ≤ CG2 * p32 * (sK * ri) * (Cbg * Q3s * (Cgw * Gs)) +
      CG2 * p12 * (sK * rs) * (sd * D3 * H + Cbg * Q3s * (Cgw * Hs)))
    (hDirBle : DirB ≤ CB2 * p32 * (sK * ri) * (Cbg * Q3s * (Cgw * Gs)) +
      CB2 * p12 * (sK * rs) * (sd * D3 * H + Cbg * Q3s * (Cgw * Hs)))
    (hmain : T ≤ alpha * rs * (P2 * (D3 * X) + P2 * S + gP * (dd * (D3 * H)) +
        CG1 * (p32 * low * DirG + p3 * lamInv * Bg + negf * Hn)) + beta * DirB) :
    T ≤ (alpha * D3) * (rs * P2 * X) + alpha * (rs * P2 * S) +
      (8 * alpha * CG1 * CG2 * KR * Cbg * Cgw + 8 * alpha * CG1 * KR * Cbg * Cgw +
          3 * beta * CB2 * sK * Cbg * Cgw) * (Sm3 * ri * Q3s * Gs) +
      (4 * alpha * CG1 * CG2 * KR * Cbg * Cgw + 2 * beta * CB2 * sK * Cbg * Cgw) *
          (Sm2 * rs * Q3s * Hs) +
      (alpha * gP * dd * D3 + 4 * alpha * CG1 * CG2 * KR * sd * D3 +
          negC * alpha * CG1 * sd * D3 + 2 * beta * CB2 * sK * sd * D3) *
          (Sm2 * rs * H) := by
  have hars : (0 : ℝ) ≤ alpha * rs := mul_nonneg halpha hrs
  have hsiginv : (0 : ℝ) ≤ sig⁻¹ := inv_nonneg.mpr hsig.le
  have hG0 : (0 : ℝ) ≤ Cbg * Q3s * (Cgw * Gs) :=
    mul_nonneg (mul_nonneg hCbg hQ3s) (mul_nonneg hCgw hGs)
  have hN0 : (0 : ℝ) ≤ sd * D3 * H + Cbg * Q3s * (Cgw * Hs) :=
    add_nonneg (mul_nonneg (mul_nonneg hsd hD3) hH)
      (mul_nonneg (mul_nonneg hCbg hQ3s) (mul_nonneg hCgw hHs))
  -- the data-Poincaré leg
  have h3 : alpha * rs * (gP * (dd * (D3 * H))) ≤
      (alpha * gP * dd * D3) * (Sm2 * rs * H) := by
    have hnn : (0 : ℝ) ≤ alpha * gP * dd * D3 * (rs * H) :=
      mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg halpha hgP) hdd) hD3)
        (mul_nonneg hrs hH)
    have hstep := mul_le_mul_of_nonneg_left hone hnn
    linarith only [hstep]
  have h5a : p3 * lamInv * Bg ≤ p3 * (KR * sig⁻¹) * (Cbg * Q3s * (Cgw * Gs)) :=
    mul_le_mul (mul_le_mul_of_nonneg_left hlamInvle hp3) hBgle hBg0
      (mul_nonneg hp3 (mul_nonneg hKR hsiginv))
  have h5 : alpha * rs * (CG1 * (p3 * lamInv * Bg)) ≤
      (8 * alpha * CG1 * KR * Cbg * Cgw) * (Sm3 * ri * Q3s * Gs) := by
    have hstep : alpha * rs * (CG1 * (p3 * lamInv * Bg)) ≤
        alpha * rs * (CG1 * (p3 * (KR * sig⁻¹) * (Cbg * Q3s * (Cgw * Gs)))) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left h5a hCG1) hars
    refine hstep.trans (le_of_eq ?_)
    have e1 : alpha * rs * (CG1 * (8 * Sm3 * (KR * sig⁻¹) * (Cbg * Q3s * (Cgw * Gs)))) =
        (8 * alpha * CG1 * KR * Cbg * Cgw * Sm3 * Q3s * Gs) * (rs * sig⁻¹) := by ring
    rw [hp3eq, e1, hrssig]
    ring
  have h6 : alpha * rs * (CG1 * (negf * Hn)) ≤
      (negC * alpha * CG1 * sd * D3) * (Sm2 * rs * H) := by
    have hstep : negf * Hn ≤ negC * Sm2 * (sd * D3 * H) :=
      mul_le_mul hnegfle hHnle hHn0 (mul_nonneg hnegC hSm2)
    have hstep2 : alpha * rs * (CG1 * (negf * Hn)) ≤
        alpha * rs * (CG1 * (negC * Sm2 * (sd * D3 * H))) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hstep hCG1) hars
    refine hstep2.trans (le_of_eq ?_)
    ring
  have h4a : p32 * low * DirG ≤
      p32 * (sK * ri) *
        (CG2 * p32 * (sK * ri) * (Cbg * Q3s * (Cgw * Gs)) +
          CG2 * p12 * (sK * rs) * (sd * D3 * H + Cbg * Q3s * (Cgw * Hs))) :=
    mul_le_mul (mul_le_mul_of_nonneg_left hlowle hp32) hDirGle hDirG0
      (mul_nonneg hp32 (mul_nonneg hsK hri))
  have h4 : alpha * rs * (CG1 * (p32 * low * DirG)) ≤
      (8 * alpha * CG1 * CG2 * KR * Cbg * Cgw) * (Sm3 * ri * Q3s * Gs) +
        (4 * alpha * CG1 * CG2 * KR * Cbg * Cgw) * (Sm2 * rs * Q3s * Hs) +
        (4 * alpha * CG1 * CG2 * KR * sd * D3) * (Sm2 * rs * H) := by
    have hstep : alpha * rs * (CG1 * (p32 * low * DirG)) ≤
        alpha * rs * (CG1 * (p32 * (sK * ri) *
          (CG2 * p32 * (sK * ri) * (Cbg * Q3s * (Cgw * Gs)) +
            CG2 * p12 * (sK * rs) * (sd * D3 * H + Cbg * Q3s * (Cgw * Hs))))) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left h4a hCG1) hars
    refine hstep.trans (le_of_eq ?_)
    have e1 : alpha * rs * (CG1 * (p32 * (sK * ri) *
          (CG2 * p32 * (sK * ri) * (Cbg * Q3s * (Cgw * Gs)) +
            CG2 * p12 * (sK * rs) * (sd * D3 * H + Cbg * Q3s * (Cgw * Hs))))) =
        (alpha * CG1 * CG2 * Cbg * Cgw * Q3s * Gs * ri) *
            ((sK * sK) * (p32 * p32) * (rs * ri)) +
          (alpha * CG1 * CG2 * sd * D3 * H * rs) *
            ((sK * sK) * (p32 * p12) * (rs * ri)) +
          (alpha * CG1 * CG2 * Cbg * Cgw * Q3s * Hs * rs) *
            ((sK * sK) * (p32 * p12) * (rs * ri)) := by ring
    rw [e1, hsKsq, hpp3, hpp2, hrsri]
    ring
  have h7 : beta * DirB ≤
      (3 * beta * CB2 * sK * Cbg * Cgw) * (Sm3 * ri * Q3s * Gs) +
        (2 * beta * CB2 * sK * Cbg * Cgw) * (Sm2 * rs * Q3s * Hs) +
        (2 * beta * CB2 * sK * sd * D3) * (Sm2 * rs * H) := by
    have hstep : beta * DirB ≤
        beta * (CB2 * p32 * (sK * ri) * (Cbg * Q3s * (Cgw * Gs)) +
          CB2 * p12 * (sK * rs) * (sd * D3 * H + Cbg * Q3s * (Cgw * Hs))) :=
      mul_le_mul_of_nonneg_left hDirBle hbeta
    refine hstep.trans ?_
    have hforce : beta * (CB2 * p32 * (sK * ri) * (Cbg * Q3s * (Cgw * Gs))) ≤
        (3 * beta * CB2 * sK * Cbg * Cgw) * (Sm3 * ri * Q3s * Gs) := by
      have hnn : (0 : ℝ) ≤ beta * CB2 * (sK * ri) * (Cbg * Q3s * (Cgw * Gs)) :=
        mul_nonneg (mul_nonneg (mul_nonneg hbeta hCB2) (mul_nonneg hsK hri)) hG0
      have h := mul_le_mul_of_nonneg_left hp32le hnn
      calc beta * (CB2 * p32 * (sK * ri) * (Cbg * Q3s * (Cgw * Gs)))
          = beta * CB2 * (sK * ri) * (Cbg * Q3s * (Cgw * Gs)) * p32 := by ring
        _ ≤ beta * CB2 * (sK * ri) * (Cbg * Q3s * (Cgw * Gs)) * (3 * Sm3) := h
        _ = (3 * beta * CB2 * sK * Cbg * Cgw) * (Sm3 * ri * Q3s * Gs) := by ring
    have hgrad : beta * (CB2 * p12 * (sK * rs) *
          (sd * D3 * H + Cbg * Q3s * (Cgw * Hs))) ≤
        (2 * beta * CB2 * sK * Cbg * Cgw) * (Sm2 * rs * Q3s * Hs) +
          (2 * beta * CB2 * sK * sd * D3) * (Sm2 * rs * H) := by
      have hnn : (0 : ℝ) ≤ beta * CB2 * (sK * rs) *
          (sd * D3 * H + Cbg * Q3s * (Cgw * Hs)) :=
        mul_nonneg (mul_nonneg (mul_nonneg hbeta hCB2) (mul_nonneg hsK hrs)) hN0
      have h := mul_le_mul_of_nonneg_left hp12le hnn
      calc beta * (CB2 * p12 * (sK * rs) * (sd * D3 * H + Cbg * Q3s * (Cgw * Hs)))
          = beta * CB2 * (sK * rs) * (sd * D3 * H + Cbg * Q3s * (Cgw * Hs)) * p12 := by
            ring
        _ ≤ beta * CB2 * (sK * rs) * (sd * D3 * H + Cbg * Q3s * (Cgw * Hs)) *
              (2 * Sm2) := h
        _ = (2 * beta * CB2 * sK * Cbg * Cgw) * (Sm2 * rs * Q3s * Hs) +
              (2 * beta * CB2 * sK * sd * D3) * (Sm2 * rs * H) := by ring
    linarith only [hforce, hgrad]
  linarith only [hmain, h3, h4, h5, h6, h7]

/-! ## 5. The five-summand absorption of the boundary composition -/

/-- **The boundary re-cut absorption.**

The composed boundary bound carries five legs: the flux-weighted `L²` leg `A`,
the force leg `B` (at the `σ_{n+3}` index), the two `∇h` legs `T3`, `T4`, and
the open scalar's leg `T5`.  The frozen display takes `A` inside its first
bracket (`A ≤ A'`, the bracket's companion being nonnegative), pays the `σ`
gap-3 factor `4` on the force leg, and carries `T3`, `T4` unchanged; `T5` is the
successor leg. -/
theorem boundary_absorb {Cf C A A' B B' T3 T4 T5 : ℝ} (hAA' : A ≤ A')
    (hA' : 0 ≤ A') (hBB' : B ≤ 4 * B') (hB' : 0 ≤ B') (hT3 : 0 ≤ T3)
    (hT4 : 0 ≤ T4) (hT5 : 0 ≤ T5) (hCf : 0 ≤ Cf) (h1 : Cf ≤ C)
    (h4 : 4 * Cf ≤ C) :
    Cf * (A + B + T3 + T4 + T5) ≤ C * (A' + B' + T3 + T4) + C * T5 := by
  have hC0 : 0 ≤ C := le_trans hCf h1
  have hstep1 : Cf * A ≤ C * A' := by
    have ha := mul_le_mul_of_nonneg_left hAA' hCf
    have hb := mul_le_mul_of_nonneg_right h1 hA'
    linarith only [ha, hb]
  have hstep2 : Cf * B ≤ C * B' := by
    have ha := mul_le_mul_of_nonneg_left hBB' hCf
    have hb := mul_le_mul_of_nonneg_right h4 hB'
    have hc : Cf * (4 * B') = 4 * Cf * B' := by ring
    rw [hc] at ha
    linarith only [ha, hb]
  have hstep3 : Cf * T3 ≤ C * T3 := mul_le_mul_of_nonneg_right h1 hT3
  have hstep4 : Cf * T4 ≤ C * T4 := mul_le_mul_of_nonneg_right h1 hT4
  have hstep5 : Cf * T5 ≤ C * T5 := mul_le_mul_of_nonneg_right h1 hT5
  have hexp : Cf * (A + B + T3 + T4 + T5) =
      Cf * A + Cf * B + Cf * T3 + Cf * T4 + Cf * T5 := by ring
  have hexp2 : C * (A' + B' + T3 + T4) + C * T5 =
      C * A' + C * B' + C * T3 + C * T4 + C * T5 := by ring
  rw [hexp, hexp2]
  linarith only [hstep1, hstep2, hstep3, hstep4, hstep5]

/-- Five-term frame estimate retaining the representative error in the flat leg. -/
theorem boundary_five_term_bound_errorWeighted :
    ∀ (CE KE kappa cg A1 : ℝ)
      (_ : A1 = cg * (216 : ℝ) * (kappa * KE)) (_ : (0 : ℝ) ≤ A1) (s : ℝ) (_ : (0 : ℝ) < s) (S
        Erep : ℝ)
      (_ : Erep ≤ CE * (1 / 2 : ℝ)) (_ : (0 : ℝ) ≤ Erep) (sig X Gs Hs Hn P2 Q3s Q1s R3n S4 S7 S6
        Sm3 Sm2 : ℝ)
      (_ : (0 : ℝ) ≤ X) (_ : (0 : ℝ) ≤ Gs) (_ : (0 : ℝ) ≤ Hs) (_ : (0 : ℝ) ≤ S) (_ : (0 : ℝ) ≤ Q3s)
      (_ : (0 : ℝ) ≤ R3n) (_ : (0 : ℝ) ≤ Sm3) (_ : (0 : ℝ) ≤ Sm2) (_ : (0 : ℝ) ≤ sig⁻¹)
      (_ : sig⁻¹ * sig = (1 : ℝ)) (_ : s⁻¹ ^ (4 : ℕ) = S4) (_ : S4 * Sm3 = S7) (_ : S4 * Sm2 = S6)
      (_ : R3n * P2 ≤ (1 : ℝ)) (_ : R3n * Q3s ≤ (9 : ℝ) * Q1s),
      sig⁻¹ * R3n *
          (cg *
            ((216 : ℝ) * s⁻¹ ^ (4 : ℕ) *
              (kappa * KE * Erep *
                (sig * (P2 * X) + sig * (P2 * S) + Sm3 * (Q3s * Gs) + Sm2 * (sig * (Q3s * Hs)) +
                  Sm2 * (sig * Hn))))) ≤
        A1 * (S4 * Erep * X) + (9 : ℝ) * (CE * (1 / 2 : ℝ)) * A1 * (S7 * sig⁻¹ * Q1s * Gs) +
              (9 : ℝ) * (CE * (1 / 2 : ℝ)) * A1 * (S6 * Q1s * Hs) +
            A1 * (S6 * Erep * R3n * Hn) +
          A1 * (S4 * Erep * S) := by
  intro CE KE kappa cg A1 hA1def hA1 s hs S Erep hErepCap hErep0 sig X Gs Hs Hn P2 Q3s Q1s R3n S4
    S7 S6 Sm3 Sm2 hX0 hGs0 hHs0 hS0 hQ3s0 hR3n0 hSm30 hSm20 hsiginv0 hsinv hS4eq hS4Sm3 hS4Sm2
      hRP2 hRQ3s
  have hsplit : (sig⁻¹ * R3n) * (cg * (216 * (s⁻¹) ^ (4 : ℕ) *
        (kappa * KE * Erep * (sig * (P2 * X) + sig * (P2 * S) + Sm3 * (Q3s * Gs) +
          Sm2 * (sig * (Q3s * Hs)) + Sm2 * (sig * Hn))))) =
      A1 * ((s⁻¹) ^ (4 : ℕ) * (Erep * ((sig⁻¹ * sig) * ((R3n * P2) * X)))) +
        A1 * ((s⁻¹) ^ (4 : ℕ) * (Erep * ((sig⁻¹ * sig) * ((R3n * P2) * S)))) +
        A1 * ((s⁻¹) ^ (4 : ℕ) * (Erep * (sig⁻¹ * ((R3n * Q3s) * (Sm3 * Gs))))) +
        A1 * ((s⁻¹) ^ (4 : ℕ) *
          (Erep * ((sig⁻¹ * sig) * (Sm2 * ((R3n * Q3s) * Hs))))) +
        A1 * ((s⁻¹) ^ (4 : ℕ) * (Erep * ((sig⁻¹ * sig) * (Sm2 * (R3n * Hn))))) := by
    rw [hA1def]; ring
  rw [hsplit, hsinv]
  have hsinv4 : (0 : ℝ) ≤ (s⁻¹) ^ (4 : ℕ) := pow_nonneg (inv_nonneg.mpr hs.le) 4
  have hi : A1 * ((s⁻¹) ^ (4 : ℕ) * (Erep * (1 * ((R3n * P2) * X)))) ≤
      A1 * (S4 * Erep * X) := by
    have h1 : (R3n * P2) * X ≤ X := by
      have h := mul_le_mul_of_nonneg_right hRP2 hX0
      linarith only [h]
    calc A1 * ((s⁻¹) ^ (4 : ℕ) * (Erep * (1 * ((R3n * P2) * X))))
        = A1 * ((s⁻¹) ^ (4 : ℕ) * (Erep * ((R3n * P2) * X))) := by ring
      _ ≤ A1 * ((s⁻¹) ^ (4 : ℕ) * (Erep * X)) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_left h1 hErep0) hsinv4) hA1
      _ = A1 * (S4 * Erep * X) := by rw [hS4eq]; ring
  have hii : A1 * ((s⁻¹) ^ (4 : ℕ) * (Erep * (1 * ((R3n * P2) * S)))) ≤
      A1 * (S4 * Erep * S) := by
    have h1 : (R3n * P2) * S ≤ S := by
      have h := mul_le_mul_of_nonneg_right hRP2 hS0
      linarith only [h]
    calc A1 * ((s⁻¹) ^ (4 : ℕ) * (Erep * (1 * ((R3n * P2) * S))))
        = A1 * ((s⁻¹) ^ (4 : ℕ) * (Erep * ((R3n * P2) * S))) := by ring
      _ ≤ A1 * ((s⁻¹) ^ (4 : ℕ) * (Erep * S)) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_left h1 hErep0) hsinv4) hA1
      _ = A1 * (S4 * Erep * S) := by rw [hS4eq]; ring
  have hiii : A1 * ((s⁻¹) ^ (4 : ℕ) *
      (Erep * (sig⁻¹ * ((R3n * Q3s) * (Sm3 * Gs))))) ≤
      (9 * (CE * (1 / 2)) * A1) * (S7 * sig⁻¹ * Q1s * Gs) := by
    have h2 : (R3n * Q3s) * (Sm3 * Gs) ≤ (9 * Q1s) * (Sm3 * Gs) :=
      mul_le_mul_of_nonneg_right hRQ3s (mul_nonneg hSm30 hGs0)
    have h2nn : (0 : ℝ) ≤ sig⁻¹ * ((R3n * Q3s) * (Sm3 * Gs)) :=
      mul_nonneg hsiginv0 (mul_nonneg (mul_nonneg hR3n0 hQ3s0)
        (mul_nonneg hSm30 hGs0))
    have hinner : Erep * (sig⁻¹ * ((R3n * Q3s) * (Sm3 * Gs))) ≤
        (CE * (1 / 2)) * (sig⁻¹ * ((9 * Q1s) * (Sm3 * Gs))) :=
      mul_le_mul hErepCap (mul_le_mul_of_nonneg_left h2 hsiginv0) h2nn
        (le_trans hErep0 hErepCap)
    calc A1 * ((s⁻¹) ^ (4 : ℕ) * (Erep * (sig⁻¹ * ((R3n * Q3s) * (Sm3 * Gs)))))
        ≤ A1 * ((s⁻¹) ^ (4 : ℕ) *
            ((CE * (1 / 2)) * (sig⁻¹ * ((9 * Q1s) * (Sm3 * Gs))))) :=
          mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_left hinner hsinv4) hA1
      _ = (9 * (CE * (1 / 2)) * A1) * (((s⁻¹) ^ (4 : ℕ) * Sm3) * sig⁻¹ * Q1s * Gs) := by
          ring
      _ = (9 * (CE * (1 / 2)) * A1) * (S7 * sig⁻¹ * Q1s * Gs) := by
          rw [hS4eq, hS4Sm3]
  have hiv : A1 * ((s⁻¹) ^ (4 : ℕ) *
      (Erep * (1 * (Sm2 * ((R3n * Q3s) * Hs))))) ≤
      (9 * (CE * (1 / 2)) * A1) * (S6 * Q1s * Hs) := by
    have h2 : Sm2 * ((R3n * Q3s) * Hs) ≤ Sm2 * ((9 * Q1s) * Hs) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hRQ3s hHs0) hSm20
    have h2nn : (0 : ℝ) ≤ Sm2 * ((R3n * Q3s) * Hs) :=
      mul_nonneg hSm20 (mul_nonneg (mul_nonneg hR3n0 hQ3s0) hHs0)
    have hinner : Erep * (Sm2 * ((R3n * Q3s) * Hs)) ≤
        (CE * (1 / 2)) * (Sm2 * ((9 * Q1s) * Hs)) :=
      mul_le_mul hErepCap h2 h2nn (le_trans hErep0 hErepCap)
    calc A1 * ((s⁻¹) ^ (4 : ℕ) * (Erep * (1 * (Sm2 * ((R3n * Q3s) * Hs)))))
        = A1 * ((s⁻¹) ^ (4 : ℕ) * (Erep * (Sm2 * ((R3n * Q3s) * Hs)))) := by ring
      _ ≤ A1 * ((s⁻¹) ^ (4 : ℕ) * ((CE * (1 / 2)) * (Sm2 * ((9 * Q1s) * Hs)))) :=
          mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_left hinner hsinv4) hA1
      _ = (9 * (CE * (1 / 2)) * A1) * (((s⁻¹) ^ (4 : ℕ) * Sm2) * Q1s * Hs) := by ring
      _ = (9 * (CE * (1 / 2)) * A1) * (S6 * Q1s * Hs) := by rw [hS4eq, hS4Sm2]
  -- The error-weighted delta: the flat leg keeps `𝓔`.
  have hv : A1 * ((s⁻¹) ^ (4 : ℕ) * (Erep * (1 * (Sm2 * (R3n * Hn))))) ≤
      A1 * (S6 * Erep * R3n * Hn) := by
    have hprod : (s⁻¹) ^ (4 : ℕ) * Sm2 = S6 := by rw [hS4eq]; exact hS4Sm2
    refine le_of_eq ?_
    rw [← hprod]; ring
  linarith only [hi, hii, hiii, hiv, hv]

/-- Capped specialization of the error-weighted five-term frame estimate. -/
theorem boundary_five_term_bound :
    ∀ (CE KE kappa cg A1 : ℝ) (_ : A1 = cg * (216 : ℝ) * (kappa * KE))
      (_ : (0 : ℝ) ≤ A1) (s : ℝ) (_ : (0 : ℝ) < s) (S Erep : ℝ) (_ : Erep ≤ CE * (1 / 2 : ℝ))
      (_ : (0 : ℝ) ≤ Erep) (sig X Gs Hs Hn P2 Q3s Q1s R3n S4 S7 S6 Sm3 Sm2 : ℝ) (_ : (0 : ℝ) ≤ X)
      (_ : (0 : ℝ) ≤ Gs) (_ : (0 : ℝ) ≤ Hs) (_ : (0 : ℝ) ≤ Hn) (_ : (0 : ℝ) ≤ S) (_ : (0 : ℝ) ≤ Q3s)
      (_ : (0 : ℝ) ≤ R3n) (_ : (0 : ℝ) ≤ Sm3) (_ : (0 : ℝ) ≤ Sm2) (_ : (0 : ℝ) ≤ sig⁻¹)
      (_ : sig⁻¹ * sig = (1 : ℝ)) (_ : s⁻¹ ^ (4 : ℕ) = S4) (_ : S4 * Sm3 = S7) (_ : S4 * Sm2 = S6)
      (_ : R3n * P2 ≤ (1 : ℝ)) (_ : R3n * Q3s ≤ (9 : ℝ) * Q1s),
      sig⁻¹ * R3n *
          (cg *
            ((216 : ℝ) * s⁻¹ ^ (4 : ℕ) *
              (kappa * KE * Erep *
                (sig * (P2 * X) + sig * (P2 * S) + Sm3 * (Q3s * Gs) + Sm2 * (sig * (Q3s * Hs)) +
                  Sm2 * (sig * Hn))))) ≤
        A1 * (S4 * Erep * X) + (9 : ℝ) * (CE * (1 / 2 : ℝ)) * A1 * (S7 * sig⁻¹ * Q1s * Gs) +
              (9 : ℝ) * (CE * (1 / 2 : ℝ)) * A1 * (S6 * Q1s * Hs) +
            CE * (1 / 2 : ℝ) * A1 * (S6 * R3n * Hn) +
          A1 * (S4 * Erep * S) := by
  intro CE KE kappa cg A1 hA1def hA1 s hs S Erep hErepCap hErep0 sig X Gs Hs Hn P2 Q3s Q1s R3n S4
    S7 S6 Sm3 Sm2 hX0 hGs0 hHs0 hHn0 hS0 hQ3s0 hR3n0 hSm30 hSm20 hsiginv0 hsinv hS4eq hS4Sm3
    hS4Sm2 hRP2 hRQ3s
  have hweighted := boundary_five_term_bound_errorWeighted CE KE kappa cg A1 hA1def hA1 s hs S
    Erep hErepCap hErep0 sig X Gs Hs Hn P2 Q3s Q1s R3n S4 S7 S6 Sm3 Sm2 hX0 hGs0 hHs0 hS0
    hQ3s0 hR3n0 hSm30 hSm20 hsiginv0 hsinv hS4eq hS4Sm3 hS4Sm2 hRP2 hRQ3s
  have hS60 : 0 ≤ S6 := by
    rw [← hS4Sm2, ← hS4eq]
    exact mul_nonneg (pow_nonneg (inv_nonneg.mpr hs.le) 4) hSm20
  have hcap : A1 * (S6 * Erep * R3n * Hn) ≤
      CE * (1 / 2 : ℝ) * A1 * (S6 * R3n * Hn) := by
    have h := mul_le_mul_of_nonneg_left hErepCap
      (mul_nonneg hA1 (mul_nonneg (mul_nonneg hS60 hR3n0) hHn0))
    convert h using 1 <;> ring
  exact hweighted.trans (add_le_add (add_le_add le_rfl hcap) le_rfl)

end

end Algsuperdiff.Section4.Provider.ExcessDecay
