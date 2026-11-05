/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.Proportion.LaneCertificates
public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.Proportion.ShiftedInterface

/-!
# ProportionArith

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# The arithmetic of the `§4.1` proportion assembly

ABK26, §4.1, `p.independence.between.scales`.  The three lane endpoints of
`ShiftedInterface` deliver, at every base `m₀`, a tail `exp(−c₁n)` for the
window `{m₀,…,m₀+n}`.  The `§4.1` display asks instead for `6·exp(−A(M_w+1))` at
a *specific* rate `A` read off the model.  Four pieces of arithmetic separate
the two, and they are collected here so that the assembly file carries only the
composition:

* **the window offset** (`exp_le_six_exp_of_one_le`, `exp_le_six_exp_of_zero`):
  running the lanes at `c₁ = 2A` gives `exp(−2A·M_w) ≤ 6·exp(−A(M_w+1))` for
  every `M_w ≥ 1`; the prefactor `6` of the printed display is exactly what pays
  for the `(M_w+1)`-versus-`M_w` offset, so it is not free.
* **the `M_w = 0` instance** (`setOf_scalePropFrom_zero_eq_compl`,
  `half_le_scaleProp_one_of_mem`): at `M_w = 0` the printed clause
  `avsum 𝟙{𝒢} ≤ 1 − θ` *is* the single bad event `𝒢(m₀)ᶜ`, whose mass the lane
  package does not bound at window `0` (the bound there is `1`).  A single bad
  scale inside the window `{m₀, m₀+1}` already carries density `½`, so the lane
  endpoint at window `1` bounds it as soon as the level is `< ½`.
* **the level split** (`couplingG0_at_split`, `honestG1_at_split`): the two
  proved lanes need `θ(r+1) < 1`, which the printed `θ ≤ ½` does not give once
  `r ≥ 2`.  Running them at `θ/(8L)`, `L = r+1`, costs one factor `L` in each
  coupling, and that factor is absorbed into the assembly's own constant — the
  anchor's constant enters both couplings linearly, so an `L`-fold split is free
  while a `C`-fold split would not be.
* **the anchor's clauses at a smaller constant** (`anchorRegime_shrink`,
  `anchorLevel_weaken`, `anchorNumerator_le`): the regime clause is used only
  through the first branch of its `min`; the `s⁻⁶` level clause implies the
  printed `s⁻⁴` one once the constant is lowered; and on the printed window
  `c⋆ ≤ 3/2`, `s, ε, θ ≤ ½` the numerator of the printed rate is at most `9/4`,
  which is what keeps the `𝒢₀` lane's rate ceiling non-binding.

## References

* ABK26, `p.independence.between.scales`; `d.good.event.for.lambda`.
-/

namespace Algsuperdiff.Section4.Provider.Proportion

open Algsuperdiff.Section4.Probability.IndicatorDensity

noncomputable section

/-! ## 1. The window offset -/

/-- **The rate match on the long windows.**  With the lanes run at `c₁ = 2A`, the
composed tail `exp(−2A·M_w)` sits under the printed `6·exp(−A(M_w+1))` for every
`M_w ≥ 1`: `2M_w ≥ M_w + 1` there.  The prefactor `6` is not consumed on this
branch, but the `(M_w+1)`-versus-`M_w` offset is. -/
theorem exp_le_six_exp_of_one_le {A : ℝ} (hA : 0 ≤ A) {Mw : ℕ} (hMw : 1 ≤ Mw) :
    Real.exp (-(2 * A) * (Mw : ℝ)) ≤ 6 * Real.exp (-(A * ((Mw : ℝ) + 1))) := by
  have hMwR : (1 : ℝ) ≤ (Mw : ℝ) := by exact_mod_cast hMw
  have hstep : A * ((Mw : ℝ) + 1) ≤ 2 * A * (Mw : ℝ) := by
    have h : (Mw : ℝ) + 1 ≤ 2 * (Mw : ℝ) := by linarith only [hMwR]
    have hmul := mul_le_mul_of_nonneg_left h hA
    linarith only [hmul]
  have hexp : Real.exp (-(2 * A) * (Mw : ℝ)) ≤ Real.exp (-(A * ((Mw : ℝ) + 1))) :=
    Real.exp_le_exp.2 (by linarith only [hstep])
  have hpos : (0 : ℝ) < Real.exp (-(A * ((Mw : ℝ) + 1))) := Real.exp_pos _
  linarith only [hexp, hpos]

/-- **The rate match at the single-scale window.**  At `M_w = 0` the assembly
reads the lane endpoint at window `1`, whose tail is `exp(−2A)`; the printed
right-hand side there is `6·exp(−A)`. -/
theorem exp_le_six_exp_of_zero {A : ℝ} (hA : 0 ≤ A) :
    Real.exp (-(2 * A) * ((1 : ℕ) : ℝ)) ≤ 6 * Real.exp (-(A * (((0 : ℕ) : ℝ) + 1))) := by
  have hexp : Real.exp (-(2 * A) * ((1 : ℕ) : ℝ))
      ≤ Real.exp (-(A * (((0 : ℕ) : ℝ) + 1))) := by
    refine Real.exp_le_exp.2 ?_
    have h0 : ((0 : ℕ) : ℝ) = 0 := Nat.cast_zero
    have h1 : ((1 : ℕ) : ℝ) = 1 := Nat.cast_one
    rw [h0, h1]
    linarith only [hA]
  have hpos : (0 : ℝ) < Real.exp (-(A * (((0 : ℕ) : ℝ) + 1))) := Real.exp_pos _
  linarith only [hexp, hpos]

/-! ## 2. The `M_w = 0` instance -/

variable {Ω : Type*}

/-- **The single-scale window reads the printed clause as one bad event.**  At
`M_w = 0` the average `avsum 𝟙{Ev}` over `{m₀}` is the indicator of `Ev m₀`, and
for `0 < θ ≤ 1` the clause `avsum 𝟙{Ev} ≤ 1 − θ` holds exactly on `(Ev m₀)ᶜ`. -/
theorem setOf_scalePropFrom_zero_eq_compl (Ev : ℤ → Set Ω) (m0 : ℤ) {theta : ℝ}
    (htheta0 : 0 < theta) (htheta1 : theta ≤ 1) :
    {omega | scalePropFrom Ev m0 0 omega ≤ 1 - theta} = (Ev m0)ᶜ := by
  classical
  have hval : ∀ omega : Ω, scalePropFrom Ev m0 0 omega
      = (if omega ∈ Ev m0 then (1 : ℝ) else 0) := by
    intro omega
    simp only [scalePropFrom, Nat.cast_zero, zero_add, Finset.range_one,
      Finset.sum_singleton, Nat.cast_zero, add_zero, Set.indicator_apply, div_one, one_mul]
  ext omega
  simp only [Set.mem_ofPred_eq, Set.mem_compl_iff, hval omega]
  constructor
  · intro h hmem
    rw [ite_eq_left hmem] at h
    linarith only [h, htheta0]
  · intro h
    rw [ite_eq_right h]
    linarith only [htheta1]

open scoped Classical in
/-- **One member scale already fills half of a two-scale window.**  If `ω ∈ F 0` then
the density of `F`-scales over `{0, 1}` is at least `½`.  Read at `F = fun k =>
(Ev (m₀+k))ᶜ`, this is the device that reaches the `M_w = 0` instance of the
printed display from the lane package: the level at which the lanes run is far
below `½`. -/
theorem half_le_scaleProp_one_of_mem (F : ℤ → Set Ω) (omega : Ω)
    (homega : omega ∈ F 0) :
    1 / 2 ≤ scaleProp F 1 omega := by
  have hmem : (0 : ℤ) ∈ Finset.Icc (0 : ℤ) (((1 : ℕ) : ℤ)) := by
    refine Finset.mem_Icc.2 ⟨le_refl (0 : ℤ), ?_⟩
    norm_num
  have hnn : ∀ m ∈ Finset.Icc (0 : ℤ) (((1 : ℕ) : ℤ)),
      (0 : ℝ) ≤ (if omega ∈ F m then (1 : ℝ) else 0) := by
    intro m _
    split_ifs <;> norm_num
  have hsingle : (if omega ∈ F 0 then (1 : ℝ) else 0)
      ≤ ∑ m ∈ Finset.Icc (0 : ℤ) (((1 : ℕ) : ℤ)),
          (if omega ∈ F m then (1 : ℝ) else 0) :=
    Finset.single_le_sum (f := fun m : ℤ => (if omega ∈ F m then (1 : ℝ) else 0)) hnn hmem
  rw [ite_eq_left homega] at hsingle
  have hcast : (((1 : ℕ) : ℝ) + 1) = 2 := by norm_num
  simp only [scaleProp, hcast]
  have hmul := mul_le_mul_of_nonneg_left hsingle (by norm_num : (0 : ℝ) ≤ 1 / 2)
  rw [mul_one] at hmul
  exact hmul

/-! ## 3. The level split -/

/-- **The `𝒢₀` coupling survives the level split.**  The frozen proportion
anchor's regime and level clauses, at any anchor constant `C_a ≥ (8LC₁)⁵`, give
the `𝒢₀` lane's coupling at the *split* level `θ/(8L)`.  The split factor `L`
enters the anchor constant polynomially, which is why absorbing `L = r+1` into
the assembly's `C(d)` is free. -/
theorem couplingG0_at_split {C1 L Ca cs s ep theta gamma : ℝ}
    (hC1 : 6 ≤ C1) (hL : 2 ≤ L) (hcs0 : 0 < cs) (hcs32 : cs ≤ 3 / 2)
    (hs0 : 0 < s) (hs12 : s ≤ 1 / 2) (hep0 : 0 < ep) (hep12 : ep ≤ 1 / 2)
    (hg0 : 0 < gamma) (hCa : (8 * L * C1) ^ (5 : ℕ) ≤ Ca)
    (hreg : gamma ≤ Ca⁻¹ * cs ^ (10 : ℕ))
    (hthetacond : Ca * (cs⁻¹) ^ (2 : ℕ) * (s⁻¹) ^ (4 : ℕ) * (ep⁻¹) ^ (2 : ℕ) * gamma
      ≤ theta) :
    C1 ^ (10 : ℕ) * gamma ^ (2 : ℕ) ≤ theta / (8 * L) * cs ^ (8 : ℕ) := by
  have hC10 : (0 : ℝ) < C1 := by linarith only [hC1]
  have h8L0 : (0 : ℝ) < 8 * L := by linarith only [hL]
  have h8L1 : (1 : ℝ) ≤ 8 * L := by linarith only [hL]
  have h6 : (6 : ℝ) ≤ 8 * L * C1 := by
    have hstep : (16 : ℝ) * C1 ≤ 8 * L * C1 :=
      mul_le_mul_of_nonneg_right (by linarith only [hL]) hC10.le
    linarith only [hstep, hC1]
  have hmain := couplingG0_of_anchor (C := 8 * L * C1) (Ca := Ca) h6 hcs0 hcs32
    hs0 hs12 hep0 hep12 hg0 hCa hreg hthetacond
  have hpow : 8 * L ≤ (8 * L) ^ (10 : ℕ) := by
    calc 8 * L = (8 * L) ^ (1 : ℕ) := (pow_one _).symm
      _ ≤ (8 * L) ^ (10 : ℕ) := pow_le_pow_right₀ h8L1 (by norm_num)
  rw [div_mul_eq_mul_div, le_div_iff₀ h8L0]
  calc C1 ^ (10 : ℕ) * gamma ^ (2 : ℕ) * (8 * L)
      = 8 * L * (C1 ^ (10 : ℕ) * gamma ^ (2 : ℕ)) := by ring
    _ ≤ (8 * L) ^ (10 : ℕ) * (C1 ^ (10 : ℕ) * gamma ^ (2 : ℕ)) :=
        mul_le_mul_of_nonneg_right hpow (by positivity)
    _ = (8 * L * C1) ^ (10 : ℕ) * gamma ^ (2 : ℕ) := by rw [mul_pow]; ring
    _ ≤ theta * cs ^ (8 : ℕ) := hmain

/-- **The honest `𝒢₁` condition survives the level split.**  If the honest `𝒢₁`
condition `C(1+2A)γ ≤ θ c⋆ s⁶ ε²` holds at a constant `C ≥ 8LC₁`, then the `𝒢₁`
lane's own coupling holds at the split level `θ/(8L)` with its constant `C₁`.
The split factor `L` enters the honest condition's constant linearly, so
absorbing `L = r+1` into the assembly's `C(d)` is free. -/
theorem honestG1_at_split {C1 L C A cs s ep theta gamma : ℝ}
    (hL : 2 ≤ L) (hC : 8 * L * C1 ≤ C) (hA0 : 0 ≤ A) (hg0 : 0 < gamma)
    (hhonest : C * (1 + 2 * A) * gamma ≤ theta * cs * s ^ (6 : ℕ) * ep ^ (2 : ℕ)) :
    C1 * (1 + 2 * A) * gamma ≤ theta / (8 * L) * cs * s ^ (6 : ℕ) * ep ^ (2 : ℕ) := by
  have h8L0 : (0 : ℝ) < 8 * L := by linarith only [hL]
  have hfac : (0 : ℝ) ≤ (1 + 2 * A) * gamma :=
    mul_nonneg (by linarith only [hA0]) hg0.le
  have hrw : theta / (8 * L) * cs * s ^ (6 : ℕ) * ep ^ (2 : ℕ)
      = theta * cs * s ^ (6 : ℕ) * ep ^ (2 : ℕ) / (8 * L) := by
    field_simp
  rw [hrw, le_div_iff₀ h8L0]
  calc C1 * (1 + 2 * A) * gamma * (8 * L) = 8 * L * C1 * ((1 + 2 * A) * gamma) := by ring
    _ ≤ C * ((1 + 2 * A) * gamma) := mul_le_mul_of_nonneg_right hC hfac
    _ = C * (1 + 2 * A) * gamma := by ring
    _ ≤ theta * cs * s ^ (6 : ℕ) * ep ^ (2 : ℕ) := hhonest

/-! ## 4. Reading the anchor's clauses at a smaller constant -/

/-- **The anchor's regime, read at a smaller constant and without the `min`.**
The `min` of the frozen regime clause is only ever used through its first
branch. -/
theorem anchorRegime_shrink {C0 Ca cs s ep gamma : ℝ}
    (hC00 : 0 < C0) (hle : C0 ≤ Ca)
    (hreg : gamma ≤ Ca⁻¹ *
      min (cs ^ (10 : ℕ)) (cs ^ (2 : ℕ) * s ^ (5 : ℕ) * ep ^ (2 : ℕ))) :
    gamma ≤ C0⁻¹ * cs ^ (10 : ℕ) := by
  have hcs10 : (0 : ℝ) ≤ cs ^ (10 : ℕ) := by positivity
  have hCa0 : (0 : ℝ) < Ca := lt_of_lt_of_le hC00 hle
  refine le_trans hreg ?_
  calc Ca⁻¹ * min (cs ^ (10 : ℕ)) (cs ^ (2 : ℕ) * s ^ (5 : ℕ) * ep ^ (2 : ℕ))
      ≤ Ca⁻¹ * cs ^ (10 : ℕ) :=
        mul_le_mul_of_nonneg_left (min_le_left _ _) (le_of_lt (inv_pos.2 hCa0))
    _ ≤ C0⁻¹ * cs ^ (10 : ℕ) :=
        mul_le_mul_of_nonneg_right (inv_anti₀ hC00 hle) hcs10

/-- **The `s⁻⁶` level clause implies the printed `s⁻⁴` one, at a smaller
constant.**  Two powers of `s⁻¹` are thrown away and the constant is lowered;
both directions are the easy ones, because `s ≤ ½` makes `s⁻¹ ≥ 1`. -/
theorem anchorLevel_weaken {C0 Ca cs s ep theta gamma : ℝ}
    (hC00 : 0 < C0) (hle : C0 ≤ Ca) (hs0 : 0 < s) (hs12 : s ≤ 1 / 2) (hg0 : 0 < gamma)
    (hlevel : Ca * (cs⁻¹) ^ (2 : ℕ) * (s⁻¹) ^ (6 : ℕ) * (ep⁻¹) ^ (2 : ℕ) * gamma
      ≤ theta) :
    C0 * (cs⁻¹) ^ (2 : ℕ) * (s⁻¹) ^ (4 : ℕ) * (ep⁻¹) ^ (2 : ℕ) * gamma ≤ theta := by
  have hsinv : (1 : ℝ) ≤ s⁻¹ := by
    rw [le_inv_comm₀ (by norm_num : (0 : ℝ) < 1) hs0, inv_one]
    linarith only [hs12]
  have hpow : (s⁻¹) ^ (4 : ℕ) ≤ (s⁻¹) ^ (6 : ℕ) := pow_le_pow_right₀ hsinv (by norm_num)
  have hepg : (0 : ℝ) ≤ (ep⁻¹) ^ (2 : ℕ) * gamma :=
    mul_nonneg (by positivity) hg0.le
  have hcsp : (0 : ℝ) ≤ (cs⁻¹) ^ (2 : ℕ) := by positivity
  have hs6 : (0 : ℝ) ≤ (s⁻¹) ^ (6 : ℕ) := by positivity
  refine le_trans ?_ hlevel
  have hstep1 : C0 * ((cs⁻¹) ^ (2 : ℕ) * ((s⁻¹) ^ (4 : ℕ) * ((ep⁻¹) ^ (2 : ℕ) * gamma)))
      ≤ C0 * ((cs⁻¹) ^ (2 : ℕ) * ((s⁻¹) ^ (6 : ℕ) * ((ep⁻¹) ^ (2 : ℕ) * gamma))) := by
    refine mul_le_mul_of_nonneg_left ?_ hC00.le
    refine mul_le_mul_of_nonneg_left ?_ hcsp
    exact mul_le_mul_of_nonneg_right hpow hepg
  have hstep2 : C0 * ((cs⁻¹) ^ (2 : ℕ) * ((s⁻¹) ^ (6 : ℕ) * ((ep⁻¹) ^ (2 : ℕ) * gamma)))
      ≤ Ca * ((cs⁻¹) ^ (2 : ℕ) * ((s⁻¹) ^ (6 : ℕ) * ((ep⁻¹) ^ (2 : ℕ) * gamma))) :=
    mul_le_mul_of_nonneg_right hle
      (mul_nonneg hcsp (mul_nonneg hs6 hepg))
  calc C0 * (cs⁻¹) ^ (2 : ℕ) * (s⁻¹) ^ (4 : ℕ) * (ep⁻¹) ^ (2 : ℕ) * gamma
      = C0 * ((cs⁻¹) ^ (2 : ℕ) * ((s⁻¹) ^ (4 : ℕ) * ((ep⁻¹) ^ (2 : ℕ) * gamma))) := by ring
    _ ≤ C0 * ((cs⁻¹) ^ (2 : ℕ) * ((s⁻¹) ^ (6 : ℕ) * ((ep⁻¹) ^ (2 : ℕ) * gamma))) := hstep1
    _ ≤ Ca * ((cs⁻¹) ^ (2 : ℕ) * ((s⁻¹) ^ (6 : ℕ) * ((ep⁻¹) ^ (2 : ℕ) * gamma))) := hstep2
    _ = Ca * (cs⁻¹) ^ (2 : ℕ) * (s⁻¹) ^ (6 : ℕ) * (ep⁻¹) ^ (2 : ℕ) * gamma := by ring

/-- **The numerator of the printed rate is bounded on the printed parameter
window.**  On `c⋆ ≤ 3/2`, `s, ε, θ ≤ ½` one has `c⋆²sⁿε²θ ≤ 9/4` for every `n`,
which is what makes the `𝒢₀` lane's rate ceiling `c₁γ ≤ 1` non-binding at the
anchor's parameters. -/
theorem anchorNumerator_le {cs s ep theta : ℝ} {n : ℕ}
    (hcs0 : 0 < cs) (hcs32 : cs ≤ 3 / 2) (hs0 : 0 < s) (hs12 : s ≤ 1 / 2)
    (hep0 : 0 < ep) (hep12 : ep ≤ 1 / 2) (htheta0 : 0 < theta) (htheta12 : theta ≤ 1 / 2) :
    cs ^ (2 : ℕ) * s ^ n * ep ^ (2 : ℕ) * theta ≤ 9 / 4 := by
  have hcs2 : cs ^ (2 : ℕ) ≤ 9 / 4 := by
    calc cs ^ (2 : ℕ) ≤ (3 / 2 : ℝ) ^ (2 : ℕ) := pow_le_pow_left₀ hcs0.le hcs32 2
      _ = 9 / 4 := by norm_num
  have hsn : s ^ n ≤ 1 := pow_le_one₀ hs0.le (by linarith only [hs12])
  have hep2 : ep ^ (2 : ℕ) ≤ 1 := pow_le_one₀ hep0.le (by linarith only [hep12])
  have h1 : cs ^ (2 : ℕ) * s ^ n ≤ 9 / 4 := by
    calc cs ^ (2 : ℕ) * s ^ n ≤ 9 / 4 * 1 :=
          mul_le_mul hcs2 hsn (by positivity) (by norm_num)
      _ = 9 / 4 := by norm_num
  have h2 : cs ^ (2 : ℕ) * s ^ n * ep ^ (2 : ℕ) ≤ 9 / 4 := by
    calc cs ^ (2 : ℕ) * s ^ n * ep ^ (2 : ℕ) ≤ 9 / 4 * 1 :=
          mul_le_mul h1 hep2 (by positivity) (by norm_num)
      _ = 9 / 4 := by norm_num
  calc cs ^ (2 : ℕ) * s ^ n * ep ^ (2 : ℕ) * theta ≤ 9 / 4 * 1 :=
        mul_le_mul h2 (by linarith only [htheta12]) htheta0.le (by norm_num)
    _ = 9 / 4 := by norm_num

end

end Algsuperdiff.Section4.Provider.Proportion
