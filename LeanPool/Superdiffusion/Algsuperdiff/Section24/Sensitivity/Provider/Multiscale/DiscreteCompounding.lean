/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

module

public import Mathlib.Analysis.Complex.Exponential
public import Mathlib.Analysis.SpecialFunctions.Sqrt

/-!
# DiscreteCompounding

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section

/-!
# Discrete compounding arithmetic for the Section 2.4 sensitivity estimates

The manuscript's Section 2.4 sensitivity proofs are written as differential
inequalities in the segment parameter `t` for `a + t h`.  The aggregate
coarse-grained quantities `lambda_{s,q}^{-1}` and `Lambda_{s,q}` are infinite
weighted aggregates of finite maxima of one-cube observables, so they are
*not* classically differentiable in `t`, and no such regularity may be
assumed.  Every `t`-derivative step of the source is therefore replaced here
by a purely discrete compounding argument along the path `a + (k/N) h`, `k =
0, …, N`.

This module contains only the gauge-free real-analysis arithmetic behind that
replacement:

* `riccati_step_le` — the discrete replacement for integrating the Riccati
  inequality `y' ≤ K y²` obtained at the self-referential gauge
  `(s,q) = (3/8,2)`, giving the source's `y 0 / (1 - K * y 0)` bound;
* `mul_sqrt_mul_sqrt_le_young`, `absorb_sqrt_self_bound`,
  `self_bound_le_closed` — the Young-inequality absorption turning `M ≤ J + c
  √E √M + r M` (with `r` small) into a closed bound, which is the arithmetic
  content of the display of ABK26.
-/

namespace Algsuperdiff.Section24.Sensitivity.Provider.Multiscale

open scoped BigOperators

/-! ## Elementary exponential comparisons -/

/-- `(1 - x)⁻¹ ≤ 1 + 2 x` on `[0, 1/2]`. -/
theorem inv_one_sub_le_one_add_two_mul {x : ℝ} (hx : 0 ≤ x) (hx' : x ≤ 1 / 2) :
    (1 - x)⁻¹ ≤ 1 + 2 * x := by
  have hpos : 0 < 1 - x := by linarith only [hx']
  have hkey : 0 ≤ x * (1 - 2 * x) := mul_nonneg hx (by linarith only [hx'])
  rw [inv_le_iff_one_le_mul₀ hpos]
  linarith only [hkey]

/-- `exp x ≤ 1 + 2 x` on `[0, 1/2]`. -/
theorem exp_le_one_add_two_mul {x : ℝ} (hx : 0 ≤ x) (hx' : x ≤ 1 / 2) :
    Real.exp x ≤ 1 + 2 * x := by
  have hpos : 0 < 1 - x := by linarith only [hx']
  have hlower : 1 - x ≤ Real.exp (-x) := by
    have h := Real.add_one_le_exp (-x)
    linarith only [h]
  have hexp : Real.exp x ≤ (1 - x)⁻¹ := by
    rw [le_inv_comm₀ (Real.exp_pos x) hpos]
    calc 1 - x ≤ Real.exp (-x) := hlower
      _ = (Real.exp x)⁻¹ := by rw [Real.exp_neg]
  exact hexp.trans (inv_one_sub_le_one_add_two_mul hx hx')

/-! ## The discrete Riccati step

At the self-referential gauge `(s,q) = (3/8,2)` the per-step ratio itself
involves the current value, so the compounding above is not directly available.
The source integrates the resulting Riccati inequality; the discrete analogue
below is exact and needs no differentiability. -/

/-- Discrete integration of the Riccati inequality
`y (k+1) ≤ (1 + (K/N) y k) y k`.  This is the discrete form of the source's
bound `y 0 / (1 - K y 0)`. -/
theorem riccati_step_le {y : ℕ → ℝ} {K : ℝ} (N : ℕ)
    (hy : ∀ k, 0 ≤ y k) (hK : 0 ≤ K) (hu : K * y 0 < 1)
    (hstep : ∀ k, k < N → y (k + 1) ≤ (1 + (K / N) * y k) * y k) :
    y N ≤ y 0 / (1 - K * y 0) := by
  rcases Nat.eq_zero_or_pos N with hN | hN
  · subst hN
    have h1 : 0 < 1 - K * y 0 := by linarith only [hu]
    rw [le_div_iff₀ h1]
    have hsq : 0 ≤ K * (y 0 * y 0) := mul_nonneg hK (mul_nonneg (hy 0) (hy 0))
    linarith only [hsq]
  · set u : ℝ := K * y 0 with hu_def
    have hu0 : 0 ≤ u := mul_nonneg hK (hy 0)
    have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
    -- Main invariant along the discrete path.
    have key : ∀ k, k ≤ N → (1 - ((k : ℝ) / (N : ℝ)) * u) * y k ≤ y 0 := by
      intro k
      induction k with
      | zero => intro _; simp
      | succ k ih =>
          intro hk
          have hkN : k < N := Nat.lt_of_succ_le hk
          have hkle : k ≤ N := le_of_lt hkN
          have ihk := ih hkle
          set α : ℝ := (k : ℝ) / (N : ℝ) with hα
          set β : ℝ := 1 / (N : ℝ) with hβ
          have hβpos : 0 < β := by positivity
          have hα0 : 0 ≤ α := by positivity
          have hαβ : ((k + 1 : ℕ) : ℝ) / (N : ℝ) = α + β := by
            rw [hα, hβ]; push_cast; ring
          have hαβle : α + β ≤ 1 := by
            rw [hα, hβ, ← add_div, div_le_one hNpos]
            exact_mod_cast hkN
          set c : ℝ := 1 - α * u with hc
          set c' : ℝ := 1 - (α + β) * u with hc'
          have hc'pos : 0 < c' := by
            have h : (α + β) * u ≤ u := mul_le_of_le_one_left hu0 hαβle
            rw [hc']; linarith only [h, hu]
          have hcpos : 0 < c := by
            have h : α * u ≤ (α + β) * u :=
              mul_le_mul_of_nonneg_right (by linarith only [hβpos]) hu0
            rw [hc]; rw [hc'] at hc'pos; linarith only [h, hc'pos]
          -- Bound the one-step growth factor using the induction hypothesis.
          have hKyk : K * y k * c ≤ u := by
            calc K * y k * c = K * (c * y k) := by ring
              _ ≤ K * y 0 := mul_le_mul_of_nonneg_left ihk hK
              _ = u := rfl
          have hfactor : (K / (N : ℝ)) * y k * c ≤ β * u := by
            have hrw : (K / (N : ℝ)) * y k * c = β * (K * y k * c) := by
              rw [hβ]; field_simp
            rw [hrw]
            exact mul_le_mul_of_nonneg_left hKyk hβpos.le
          have hstepk := hstep k hkN
          -- Combine: c' * y (k+1) ≤ y 0.
          have hyk := hy k
          have hmain : c' * y (k + 1) ≤ y 0 := by
            have h1 : c' * y (k + 1) ≤ c' * ((1 + (K / (N : ℝ)) * y k) * y k) :=
              mul_le_mul_of_nonneg_left hstepk hc'pos.le
            have h2 : c * (c' * ((1 + (K / (N : ℝ)) * y k) * y k))
                ≤ c * y 0 := by
              have hexp : c * (c' * ((1 + (K / (N : ℝ)) * y k) * y k))
                  = c' * ((c * y k) + ((K / (N : ℝ)) * y k * c) * y k) := by
                ring
              rw [hexp]
              have hbound : (c * y k) + ((K / (N : ℝ)) * y k * c) * y k
                  ≤ y 0 + (β * u) * y k := by
                have h := mul_le_mul_of_nonneg_right hfactor hyk
                linarith only [h, ihk]
              have hstep2 : c' * ((c * y k) + ((K / (N : ℝ)) * y k * c) * y k)
                  ≤ c' * (y 0 + (β * u) * y k) :=
                mul_le_mul_of_nonneg_left hbound hc'pos.le
              refine hstep2.trans ?_
              -- `c' * (y 0 + β u y k) ≤ c * y 0` since `c' = c - β u` and
              -- `c * y k ≤ y 0`.
              have hcc' : c' = c - β * u := by rw [hc, hc']; ring
              have hslack : 0 ≤ β * u * (y 0 - c * y k) :=
                mul_nonneg (mul_nonneg hβpos.le hu0) (by linarith only [ihk])
              have hsq : 0 ≤ (β * u) * (β * u) * y k := by positivity
              rw [hcc']
              linarith only [hslack, hsq]
            exact le_of_mul_le_mul_left
              (le_trans (mul_le_mul_of_nonneg_left h1 hcpos.le) h2) hcpos
          rw [hαβ]
          exact hmain
    have hfinal := key N le_rfl
    have hNN : ((N : ℝ) / (N : ℝ)) = 1 := div_self (ne_of_gt hNpos)
    rw [hNN, one_mul] at hfinal
    have h1 : 0 < 1 - u := by rw [hu_def]; linarith only [hu, hu_def]
    rw [le_div_iff₀ h1]
    linarith only [hfinal]

/-! ## Young absorption of a self-referential bound -/

/-- Young's inequality in the form used by the absorption step:
`c √E √M ≤ (δ/4) M + δ⁻¹ c² E`. -/
theorem mul_sqrt_mul_sqrt_le_young {c E M δ : ℝ}
    (hE : 0 ≤ E) (hM : 0 ≤ M) (hδ : 0 < δ) :
    c * Real.sqrt E * Real.sqrt M ≤ δ / 4 * M + δ⁻¹ * c ^ 2 * E := by
  have hsE : Real.sqrt E ^ 2 = E := Real.sq_sqrt hE
  have hsM : Real.sqrt M ^ 2 = M := Real.sq_sqrt hM
  have hsq : 0 ≤ (δ * Real.sqrt M - 2 * c * Real.sqrt E) ^ 2 := sq_nonneg _
  have hexp : (δ * Real.sqrt M - 2 * c * Real.sqrt E) ^ 2
      = δ ^ 2 * M + 4 * c ^ 2 * E
        - 4 * δ * (c * Real.sqrt E * Real.sqrt M) := by
    have hring : (δ * Real.sqrt M - 2 * c * Real.sqrt E) ^ 2
        = δ ^ 2 * Real.sqrt M ^ 2 + 4 * c ^ 2 * Real.sqrt E ^ 2
          - 4 * δ * (c * Real.sqrt E * Real.sqrt M) := by ring
    rw [hring, hsE, hsM]
  have hsq' : 0 ≤ δ ^ 2 * M + 4 * c ^ 2 * E
      - 4 * δ * (c * Real.sqrt E * Real.sqrt M) := hexp ▸ hsq
  have hrhs : 4 * δ * (δ / 4 * M + δ⁻¹ * c ^ 2 * E)
      = δ ^ 2 * M + 4 * c ^ 2 * E := by
    field_simp
  have hkey : 4 * δ * (c * Real.sqrt E * Real.sqrt M)
      ≤ 4 * δ * (δ / 4 * M + δ⁻¹ * c ^ 2 * E) := by
    rw [hrhs]; linarith only [hsq']
  exact le_of_mul_le_mul_left hkey (by linarith only [hδ])

/-- Absorption of the self-referential bound
`M ≤ J + c √E √M + r M` into `(1 - δ/4 - r) M ≤ J + δ⁻¹ c² E`. -/
theorem absorb_sqrt_self_bound {M J E c r δ : ℝ}
    (hM : 0 ≤ M) (hE : 0 ≤ E) (hδ : 0 < δ)
    (hbound : M ≤ J + c * Real.sqrt E * Real.sqrt M + r * M) :
    (1 - δ / 4 - r) * M ≤ J + δ⁻¹ * c ^ 2 * E := by
  have hyoung := mul_sqrt_mul_sqrt_le_young (c := c) hE hM hδ
  linarith only [hbound, hyoung]

/-- The closed form of the absorption step.
Under the smallness condition `r ≤ 1/4` and for `0 < δ ≤ 1`, a self-referential
bound `M ≤ J + c √E √M + r M` yields
`M ≤ (1 + δ + 2 r) J + 2 δ⁻¹ c² E`. -/
theorem self_bound_le_closed {M J E c r δ : ℝ}
    (hM : 0 ≤ M) (hJ : 0 ≤ J) (hE : 0 ≤ E)
    (hr : 0 ≤ r) (hr' : r ≤ 1 / 4)
    (hδ : 0 < δ) (hδ' : δ ≤ 1)
    (hbound : M ≤ J + c * Real.sqrt E * Real.sqrt M + r * M) :
    M ≤ (1 + δ + 2 * r) * J + 2 * δ⁻¹ * c ^ 2 * E := by
  have habs := absorb_sqrt_self_bound hM hE hδ hbound
  set u : ℝ := δ / 4 + r with hu
  have hu0 : 0 ≤ u := by positivity
  have hu' : u ≤ 1 / 2 := by rw [hu]; linarith only [hδ', hr']
  have hpos : 0 < 1 - u := by linarith only [hu']
  have habs' : (1 - u) * M ≤ J + δ⁻¹ * c ^ 2 * E := by
    have : (1 - δ / 4 - r) = 1 - u := by rw [hu]; ring
    rw [← this]; exact habs
  have hRnn : 0 ≤ J + δ⁻¹ * c ^ 2 * E := by positivity
  have hM' : M ≤ (1 - u)⁻¹ * (J + δ⁻¹ * c ^ 2 * E) := by
    rw [← le_div_iff₀' hpos] at habs'
    simpa [div_eq_inv_mul] using habs'
  have hfac : (1 - u)⁻¹ ≤ 1 + 2 * u := inv_one_sub_le_one_add_two_mul hu0 hu'
  have hstep : M ≤ (1 + 2 * u) * (J + δ⁻¹ * c ^ 2 * E) :=
    hM'.trans (mul_le_mul_of_nonneg_right hfac hRnn)
  have hEc : 0 ≤ δ⁻¹ * c ^ 2 * E := by positivity
  have h2u : 1 + 2 * u ≤ 2 := by rw [hu]; linarith only [hδ', hr']
  have hJfac : (1 + 2 * u) * J ≤ (1 + δ + 2 * r) * J := by
    refine mul_le_mul_of_nonneg_right ?_ hJ
    rw [hu]; linarith only [hδ]
  calc M ≤ (1 + 2 * u) * (J + δ⁻¹ * c ^ 2 * E) := hstep
    _ = (1 + 2 * u) * J + (1 + 2 * u) * (δ⁻¹ * c ^ 2 * E) := by ring
    _ ≤ (1 + δ + 2 * r) * J + 2 * (δ⁻¹ * c ^ 2 * E) :=
        add_le_add hJfac (mul_le_mul_of_nonneg_right h2u hEc)
    _ = (1 + δ + 2 * r) * J + 2 * δ⁻¹ * c ^ 2 * E := by ring

end Algsuperdiff.Section24.Sensitivity.Provider.Multiscale
