/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Frozen.Section3.InductionState
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.BadEvents.Definitions
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Stream.IncrementGauge

/-!
# IncrementOscillation

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section

/-!
# The literal increment oscillation gauge

ABK26's oscillation event `e.Bosc.def` is stated with the literal stream
increment `k_L - k_j`: `sup_{L >= j} 3^{2j} ||grad (k_L -
k_j)||_{W^{1,infinity}(z + square_j)}`.

That local measurability input is now proved.
`Algsuperdiff.Section3.Provider.Stream.shellIncrement`
is the increment as a genuine shell field (values literally `k_L - k_j`, by
`shellIncrement_apply_eq_cutoff_sub`), and this module measures it in exactly
the norm of `e.Bosc.def`:

`incrementOscGauge Q L = 3^{2j} ||grad (k_L - k_j)||_{W^{1,infinity}(z+square_j)}`
`  = max { 3^{2j} ||grad² (k_L - k_j)||_{L∞}, 3^{j} ||grad (k_L - k_j)||_{L∞} }`,

the same shape as `shellOscGauge` (ABK26, the volume-normalized Sobolev
norm; the factor `|U|^{-1/d}` of a cube of side `3^j` is `3^{-j}`).

## Main definitions

* `incrementOscGauge`: the literal `e.Bosc.def` gauge at the cube `Q` and
  scale `L`.

## Main results

* `incrementOscGauge_le_sum_shellOscGauge`: the `W^{1,infinity}` triangle
  inequality along the shell decomposition of the increment.
* `incrementOscGauge_le_oscThreshold`: the complement control of
  `e.Bosc.def`.  On the complement of `badOsc M Q`, for every `L >= Q.scale`,
  `3^{2j} ||grad (k_L - k_j)||_{W^{1,infinity}(z+square_j)} <=
   delta_osc c_star^{1/2} gamma^{-1/2} 3^{gamma j}`.
* `sqrt_cstar_mul_inv_sqrt_gamma_mul_rpow_le_two_mul_sigmaBar`: the constant
  chain of ABK26, consuming the induction-state clause `e.shom.h.bounds`:
  `c_star^{1/2} gamma^{-1/2} 3^{gamma m} <= 2 sigmabar_m`.

## References

* ABK26, `e.Bosc.def`, `e.BoscL.def`, `e.Bosc.decomp`.
* ABK26, `p.bfA.multiscalebound`, `e.we.can.apply.cg`.
* ABK26 (the volume-normalized Sobolev norms).
-/

namespace Algsuperdiff.Section3.Provider.BadEvents

open HCPolySupport HCPolySupport.Book
open Algsuperdiff.Frozen.Assumptions
open Algsuperdiff.Section3.Cutoff
open Algsuperdiff.Section3.Provider.Stream
open scoped BigOperators

noncomputable section

variable {d : ℕ}

/-! ## The literal increment gauge -/

/-- The literal left-hand side of `e.Bosc.def`:
`3^{2j} ||grad (k_L - k_j)||_{W^{1,infinity}(z + square_j)}` at the cube `Q`
with `j = Q.scale`, measured on the honest shell-field realization of the
increment `k_L - k_j`. -/
def incrementOscGauge (Q : TriadicCube d) (L : ℤ) : CutoffSample d → ℝ :=
  fun omega =>
    max
      ((3 : ℝ) ^ (2 * Q.scale) *
        localCubeSecondDerivNorm Q.scale
          (ShellField.translate (cubeBasePoint Q)
            (shellIncrement omega.1 Q.scale L)))
      ((3 : ℝ) ^ Q.scale *
        localCubeDerivNorm Q.scale
          (ShellField.translate (cubeBasePoint Q)
            (shellIncrement omega.1 Q.scale L)))

/-! ## The `W^{1,infinity}` triangle inequality along shells -/

/-- The literal increment gauge is bounded by the sum of the single-shell
gauges of `e.BoscL.def` over the shells that make up the increment. -/
theorem incrementOscGauge_le_sum_shellOscGauge (Q : TriadicCube d) (L : ℤ)
    (omega : CutoffSample d) :
    incrementOscGauge Q L omega ≤
      ∑ k ∈ Finset.Ioc Q.scale L, shellOscGauge Q k omega := by
  have h3 : (0 : ℝ) < (3 : ℝ) ^ Q.scale := zpow_pos (by norm_num) _
  have h32 : (0 : ℝ) < (3 : ℝ) ^ (2 * Q.scale) := zpow_pos (by norm_num) _
  refine max_le ?_ ?_
  · calc
      (3 : ℝ) ^ (2 * Q.scale) *
          localCubeSecondDerivNorm Q.scale
            (ShellField.translate (cubeBasePoint Q)
              (shellIncrement omega.1 Q.scale L))
          ≤ (3 : ℝ) ^ (2 * Q.scale) *
            ∑ k ∈ Finset.Ioc Q.scale L,
              localCubeSecondDerivNorm Q.scale
                (ShellField.translate (cubeBasePoint Q) (omega.1 k)) :=
        mul_le_mul_of_nonneg_left
          (localCubeSecondDerivNorm_translate_shellIncrement_le _ _ _ _ _) h32.le
      _ = ∑ k ∈ Finset.Ioc Q.scale L,
            (3 : ℝ) ^ (2 * Q.scale) *
              localCubeSecondDerivNorm Q.scale
                (ShellField.translate (cubeBasePoint Q) (omega.1 k)) :=
        Finset.mul_sum _ _ _
      _ ≤ ∑ k ∈ Finset.Ioc Q.scale L, shellOscGauge Q k omega :=
        Finset.sum_le_sum fun k _ => le_max_left _ _
  · calc
      (3 : ℝ) ^ Q.scale *
          localCubeDerivNorm Q.scale
            (ShellField.translate (cubeBasePoint Q)
              (shellIncrement omega.1 Q.scale L))
          ≤ (3 : ℝ) ^ Q.scale *
            ∑ k ∈ Finset.Ioc Q.scale L,
              localCubeDerivNorm Q.scale
                (ShellField.translate (cubeBasePoint Q) (omega.1 k)) :=
        mul_le_mul_of_nonneg_left
          (localCubeDerivNorm_translate_shellIncrement_le _ _ _ _ _) h3.le
      _ = ∑ k ∈ Finset.Ioc Q.scale L,
            (3 : ℝ) ^ Q.scale *
              localCubeDerivNorm Q.scale
                (ShellField.translate (cubeBasePoint Q) (omega.1 k)) :=
        Finset.mul_sum _ _ _
      _ ≤ ∑ k ∈ Finset.Ioc Q.scale L, shellOscGauge Q k omega :=
        Finset.sum_le_sum fun k _ => le_max_right _ _

/-! ## The complement control of `e.Bosc.def` -/

/-- Ascending reindexing of `(j, L]` by an initial block of naturals. -/
private theorem ioc_eq_range_map_asc {j L : ℤ} (hjL : j ≤ L) :
    Finset.Ioc j L =
      (Finset.range (L - j).toNat).map
        ⟨fun n : ℕ => j + 1 + (n : ℤ), by
          intro a b hab
          have hab' : j + 1 + (a : ℤ) = j + 1 + (b : ℤ) := hab
          have hcast : (a : ℤ) = (b : ℤ) := by omega
          exact_mod_cast hcast⟩ := by
  ext k
  simp only [Finset.mem_Ioc, Finset.mem_map, Finset.mem_range]
  constructor
  · rintro ⟨hlo, hhi⟩
    refine ⟨(k - j - 1).toNat, by omega, ?_⟩
    change j + 1 + ((k - j - 1).toNat : ℤ) = k
    have h1 : (0 : ℤ) ≤ k - j - 1 := by omega
    rw [Int.toNat_of_nonneg h1]
    omega
  · rintro ⟨n, hn, rfl⟩
    change j < j + 1 + (n : ℤ) ∧ j + 1 + (n : ℤ) ≤ L
    have h2 : (0 : ℤ) ≤ L - j := by omega
    have hn' : (n : ℤ) < ((L - j).toNat : ℤ) := by exact_mod_cast hn
    rw [Int.toNat_of_nonneg h2] at hn'
    omega

/-- The manuscript's `e.Bosc.def` complement control, now for the literal increment: on
the complement of `badOsc M Q`, for every scale `L >= Q.scale`,

`3^{2j} ||grad (k_L - k_j)||_{W^{1,infinity}(z + square_j)}
   <= delta_osc c_star^{1/2} gamma^{-1/2} 3^{gamma j}`. -/
theorem incrementOscGauge_le_oscThreshold (M : ABKModel d) (Q : TriadicCube d)
    {omega : CutoffSample d} (homega : omega ∉ badOsc M Q) {L : ℤ}
    (hL : Q.scale ≤ L) :
    incrementOscGauge Q L omega ≤ oscThreshold M Q.scale := by
  refine (incrementOscGauge_le_sum_shellOscGauge Q L omega).trans ?_
  rw [ioc_eq_range_map_asc hL, Finset.sum_map]
  exact oscGaugeSum_le_oscThreshold M Q homega (L - Q.scale).toNat

/-! ## The constant chain of ABK26 -/

/-- The induction-state clause `e.shom.h.bounds` gives
`c_star^{1/2} gamma^{-1/2} 3^{gamma m} <= 2 sigmabar_m`. -/
theorem sqrt_cstar_mul_inv_sqrt_gamma_mul_rpow_le_two_mul_sigmaBar
    (M : ABKModel d) {m0 : ℤ} {E : {E : ℝ // 1 ≤ E}}
    (hS : Algsuperdiff.Frozen.Section3.inductionState M m0 E) {m : ℤ}
    (hm : m ≤ m0) :
    Real.sqrt (Algsuperdiff.Section3.Disorder.cstar M) *
        (Real.sqrt M.gamma)⁻¹ * (3 : ℝ) ^ (M.gamma * (m : ℝ)) ≤
      2 * (Algsuperdiff.Section3.Annealed.sigmaBar M m : ℝ) := by
  have hgamma : 0 < M.gamma := M.shellPrefix.gamma_pos
  have hcstar : 0 < Algsuperdiff.Section3.Disorder.cstar M :=
    (Algsuperdiff.Section3.Disorder.cstar_characterization M).1
  have hsigma : 0 < (Algsuperdiff.Section3.Annealed.sigmaBar M m : ℝ) :=
    (Algsuperdiff.Section3.Annealed.sigmaBar_characterization M m).1
  set A : ℝ := Algsuperdiff.Section3.Disorder.cstar M * M.gamma⁻¹ *
    (3 : ℝ) ^ (2 * M.gamma * (m : ℝ)) with hA
  have hAnonneg : 0 ≤ A := by
    have h3 : (0 : ℝ) < (3 : ℝ) ^ (2 * M.gamma * (m : ℝ)) :=
      Real.rpow_pos_of_pos (by norm_num) _
    have : (0 : ℝ) < Algsuperdiff.Section3.Disorder.cstar M * M.gamma⁻¹ :=
      mul_pos hcstar (inv_pos.2 hgamma)
    exact (mul_pos this h3).le
  have hclause := (hS.1 m hm).1
  have hquarter : (1 / 4 : ℝ) * A ≤
      (Algsuperdiff.Section3.Annealed.sigmaBar M m : ℝ) ^ 2 :=
    le_trans (mul_le_mul_of_nonneg_left (le_max_left _ _) (by norm_num)) hclause
  have hsplit : Real.sqrt A =
      Real.sqrt (Algsuperdiff.Section3.Disorder.cstar M) *
        (Real.sqrt M.gamma)⁻¹ * (3 : ℝ) ^ (M.gamma * (m : ℝ)) := by
    have hrpow : (3 : ℝ) ^ (2 * M.gamma * (m : ℝ)) =
        ((3 : ℝ) ^ (M.gamma * (m : ℝ))) ^ (2 : ℕ) := by
      rw [← Real.rpow_natCast ((3 : ℝ) ^ (M.gamma * (m : ℝ))) 2,
        ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 3)]
      norm_num
      ring_nf
    rw [hA, hrpow,
      Real.sqrt_mul (mul_nonneg hcstar.le (inv_nonneg.2 hgamma.le)),
      Real.sqrt_sq (Real.rpow_nonneg (by norm_num) _),
      Real.sqrt_mul hcstar.le, Real.sqrt_inv]
  have hle : Real.sqrt A ≤ 2 * (Algsuperdiff.Section3.Annealed.sigmaBar M m : ℝ) := by
    rw [show (2 : ℝ) * (Algsuperdiff.Section3.Annealed.sigmaBar M m : ℝ) =
        Real.sqrt ((2 * (Algsuperdiff.Section3.Annealed.sigmaBar M m : ℝ)) ^ 2) from
      (Real.sqrt_sq (by positivity)).symm]
    exact Real.sqrt_le_sqrt (by nlinarith [hquarter])
  rwa [hsplit] at hle

end

end Algsuperdiff.Section3.Provider.BadEvents
