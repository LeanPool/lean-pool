/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section5.Provider.ExitTimeHomogenizationJoint
public import LeanPool.Superdiffusion.Algsuperdiff.Section5.Support.CutoffFieldLimitPointwise

/-!
# ExitTimeCutoffLimit

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# The good-cube exit-time bounds for the full stream field

The exit-time datum problem is `-∇·a∇w = 1` on `y + □_n` with zero boundary
values, written here at the linear datum `g(x) = x_i e_i`, whose divergence is
the constant one.  The good-cube estimates of the exit-time comparison are
proved for the truncated coefficient fields `a_L`, simultaneously for every
`L ≥ n` on one and the same sample event.

This module lets `L → ∞`.  The truncated solutions converge in `L²(y + □_n)` to
the solution for the full stream field (the coefficient distance is geometric in
`L` and the solution map is Lipschitz in the coefficient), and a bound valid for
every large `L` on the continuous representatives therefore holds at every point
of the cube for the continuous representative of the limit.  The event, the
constants, and the discrete scale `exitTimeScale M n` are unchanged.

## Main results

* `exists_isDirichletSolutionAt_linearAxisDatum_streamCoefficient` — the
  exit-time datum problem is solvable for the full field on every cube.
* `tendsto_l2_exitTime_cutoff` — `w_L → w` in `L²(y + □_n)`.
* `exit_time_bounds_on_good_cube_stream` — the two good-cube bounds for the full
  field's exit-time function, on the same event and with the same constants.

## References

* ABK26, the exit-time comparison of Section 5.2, and the passage `L → ∞` from
  the truncated fields `a_L` to `a`.
-/

namespace Algsuperdiff.Section5.Provider

open Algsuperdiff.Section3
open Algsuperdiff.Section5.Support
open HCPolySupport MeasureTheory Filter
open scoped Topology ENNReal

noncomputable section

variable {d : ℕ}

/-! ## 1. Solvability for the full field -/

/-- **The exit-time datum problem for the full stream field.**  The coefficient
field is elliptic on the cube with lower constant `ν`, and the linear datum is
`1/2`-Hölder there. -/
theorem exists_isDirichletSolutionAt_linearAxisDatum_streamCoefficient
    (M : ABKModel d) (omega : Field.FullSample d M.gamma) (y : Vec d) (n : ℤ)
    (i : Fin d) :
    ∃ u : H1Function (cubeSetAt y n),
      IsDirichletSolutionAt (Field.streamCoefficient M.nu omega) y n u
        (linearAxisDatum i) := by
  have : NeZero d := Algsuperdiff.Section3.Provider.Orlicz.neZero_of_model M
  obtain ⟨Lam, hEll⟩ := exists_isEllipticFieldOn_streamCoefficient M.nu_pos omega y n
  exact exists_isDirichletSolutionAt_of_isEllipticFieldOn hEll
    (Real.rpow_nonneg (by norm_num) _) (holderSeminormBoundOn_linearAxisDatum i y n)

/-! ## 2. The `L²` limit of the exit-time functions -/

/-- **`w_L → w` in `L²(y + □_n)`**: the exit-time functions of the truncated
fields converge to the exit-time function of the full field. -/
theorem tendsto_l2_exitTime_cutoff (M : ABKModel d)
    (omega : Field.FullSample d M.gamma) (y : Vec d) (n : ℤ) (i : Fin d)
    {u : ℤ → H1Function (cubeSetAt y n)} {v : H1Function (cubeSetAt y n)}
    (hu : ∀ L : ℤ, IsDirichletSolutionAt
      ((Cutoff.coefficientCutoff M.nu L omega.1).toCoeffField) y n (u L) (linearAxisDatum i))
    (hv : IsDirichletSolutionAt (Field.streamCoefficient M.nu omega) y n v
      (linearAxisDatum i)) :
    Tendsto (fun L : ℤ => Real.sqrt
        (∫ x in cubeSetAt y n, ((u L).toFun x - v.toFun x) ^ (2 : ℕ) ∂volume))
      atTop (𝓝 0) := by
  have : NeZero d := Algsuperdiff.Section3.Provider.Orlicz.neZero_of_model M
  obtain ⟨C, hC⟩ := Field.fullTailGood_sharp omega.2
  obtain ⟨ell, hell⟩ := exists_cubeSetAt_subset_openCubeSet y n
  have hgamma : M.gamma < 1 := by
    have := M.shellPrefix.gamma_le_quarter
    linarith only [this]
  exact tendsto_sqrt_integral_sq_sub_cutoff_atTop_zero M.nu_pos hgamma hC hell hu hv

/-! ## 3. The good-cube bounds for the full field -/

/-- **The good-cube exit-time bounds pass to the full stream field.**

On the same event `Q(y + □_n, ε)` and with the same constants as the truncated
statement, the continuous representative of the exit-time function of the full
field `a = ν I + k` is at most `C T(3^n)` at every point of `y + □_n`, and at
least `C⁻¹ T(3^n)` at every point of `y + □_{n-1}` once `ε ≤ c`.  The truncated
solutions `u_L` are required at every scale, and their representatives are the
ones the truncated estimate speaks about. -/
theorem exit_time_bounds_on_good_cube_stream (d : ℕ) (hdim : 2 ≤ d) (cstar : ℝ)
    (hcstar : 0 < cstar) (Creg : ℝ) (hCreg : 0 < Creg) :
    ∃ gamma0 Cev C c : ℝ, 0 < gamma0 ∧ 0 < Cev ∧ 0 < C ∧ 0 < c ∧
      ∀ M : ABKModel d, Disorder.cstar M = cstar → M.gamma ≤ gamma0 →
      ∀ ep : ℝ, ep ∈ Set.Ioc (0 : ℝ) (1 / 4) →
      ∀ n : ℤ,
      ∀ (y : Vec d) (i : Fin d),
      ∀ omega : Field.FullSample d M.gamma,
        omega.1 ∈ qEvent M Creg Cev n y ep →
      ∀ (u : ℤ → H1Function (cubeSetAt y n)) (uRep : ℤ → Vec d → ℝ)
        (v : H1Function (cubeSetAt y n)) (vRep : Vec d → ℝ)
        (w : H1Function (cubeSetAt y n)) (wRep : Vec d → ℝ),
        (∀ L : ℤ, IsDirichletSolutionAt
          ((Cutoff.coefficientCutoff M.nu L omega.1).toCoeffField) y n (u L)
            (linearAxisDatum i)) →
        (∀ L : ℤ, IsCubeRepresentative y n (u L) (uRep L)) →
        IsDirichletSolutionAt (fun _ => (Annealed.sigmaBar M n : ℝ) • (1 : Mat d)) y n v
            (linearAxisDatum i) →
        IsCubeRepresentative y n v vRep →
        IsDirichletSolutionAt (Field.streamCoefficient M.nu omega) y n w
            (linearAxisDatum i) →
        IsCubeRepresentative y n w wRep →
        (∀ x ∈ cubeSetAt y n, wRep x ≤ C * exitTimeScale M n) ∧
          (ep ≤ c → ∀ x ∈ cubeSetAt y (n - 1),
            C⁻¹ * exitTimeScale M n ≤ wRep x) := by
  obtain ⟨gamma0, Cev, C, c, hgamma0, hCev, hCpos, hcpos, hmain⟩ :=
    exit_time_bounds_on_good_cube d hdim cstar hcstar Creg hCreg
  refine ⟨gamma0, Cev, C, c, hgamma0, hCev, hCpos, hcpos, ?_⟩
  intro M hcs hgam ep hep n y i omega homega u uRep v vRep w wRep hu huRep hv hvRep
    hw hwRep
  have hTpos : 0 < exitTimeScale M n := exitTimeScale_pos M n
  have hlim := tendsto_l2_exitTime_cutoff M omega y n i hu hw
  have hsubcube : cubeSetAt y (n - 1) ⊆ cubeSetAt y n := by
    simpa using cubeSetAt_subset_cubeSetAt_succ y (n - 1)
  constructor
  · intro x hx
    refine le_on_open_subset_of_tendsto_l2 (isOpen_cubeSetAt y n) (subset_refl _)
      huRep hwRep ?_ hlim hx
    refine Filter.eventually_atTop.2 ⟨n, fun L hL z hz => ?_⟩
    have hbound := (hmain M hcs hgam ep hep n y i omega.1 homega L hL (u L) v
      (uRep L) vRep (fun t => ENNReal.ofReal (uRep L t)) (hu L) hv (huRep L) hvRep
      (fun _ _ => rfl)).1 z hz
    exact (ENNReal.ofReal_le_ofReal_iff (mul_nonneg hCpos.le hTpos.le)).1 hbound
  · intro hepc x hx
    refine ge_on_open_subset_of_tendsto_l2 (isOpen_cubeSetAt y (n - 1)) hsubcube
      huRep hwRep ?_ hlim hx
    refine Filter.eventually_atTop.2 ⟨n, fun L hL z hz => ?_⟩
    have hbound := (hmain M hcs hgam ep hep n y i omega.1 homega L hL (u L) v
      (uRep L) vRep (fun t => ENNReal.ofReal (uRep L t)) (hu L) hv (huRep L) hvRep
      (fun _ _ => rfl)).2 hepc z hz
    by_contra hcon
    push Not at hcon
    have hposC : (0 : ℝ) < C⁻¹ * exitTimeScale M n :=
      mul_pos (inv_pos.2 hCpos) hTpos
    have hlt : ENNReal.ofReal (uRep L z) <
        ENNReal.ofReal (C⁻¹ * exitTimeScale M n) :=
      (ENNReal.ofReal_lt_ofReal_iff hposC).2 hcon
    exact absurd hbound (not_le.2 hlt)

end

end Algsuperdiff.Section5.Provider
