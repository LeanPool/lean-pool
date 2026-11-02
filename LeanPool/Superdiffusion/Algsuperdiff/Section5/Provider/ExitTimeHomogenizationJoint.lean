/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section5.Provider.ExitTimeHomogenization
public import LeanPool.Superdiffusion.Algsuperdiff.Section5.Support.ExitTimeHomogenizationJointEvent

/-!
# ExitTimeHomogenizationJoint

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# The expected exit time from a good cube

For a bounded domain `U` the expected exit time `w(x) = E_x[τ(U)]` of the
diffusion is the solution of the Dirichlet problem `-∇·a∇w = 1` in `U`,
`w = 0` on `∂U`.  On the good cube event that problem was already compared, at
the linear datum `g(x) = x_i e_i` whose divergence is the constant one, with
the homogenized profile `w` of `-σ_n Δ w = 1`: the rough-field solution is
bounded by `C T(3^n)` on the whole cube and is at least half the homogenized
profile on the inner cube `y + □_{n-1}`, while the homogenized profile itself
is at least `T(3^n)/C` there.

Combining the two gives the two exit-time estimates of the early-exit bound: a
uniform upper bound for the expected exit time on the cube and a uniform lower
bound on the inner cube, both at the scale `T(3^n) = 3^{2n}/σ_n`.

The value `w` of the expected exit time enters through the hypothesis
`hident`, which says that `w` is the extended-real reading of the continuous
representative of the Dirichlet solution at every point of the cube.  That is
the identification of the expected exit time with the solution of the Dirichlet
problem; it is named here rather than assumed silently, and it is supplied for
the process of a coefficient field by the whole-space exit-time identity.

## Main results

* `exit_time_bounds_on_good_cube` — the uniform upper bound on the cube and the
  uniform lower bound on the inner cube.

## References

* ABK26, the exit-time comparison of Section 5.2.
-/

namespace Algsuperdiff.Section5.Provider

open Algsuperdiff.Section3
open Algsuperdiff.Section5.Support
open HCPolySupport MeasureTheory
open scoped ENNReal

noncomputable section

variable {d : ℕ}

/-- **The expected exit time from a good cube.**  Let `w` be a function on the
cube identified, through `hident`, with the continuous representative of the
Dirichlet solution of `-∇·a_m∇u = 1` on `y + □_n` with zero boundary values.
On the good cube event `Q(y + □_n, ε)` at the constant returned here, `w` is at
most `C T(3^n)` at every point of the cube, and, once `ε` is below the
threshold `c`, at least `C⁻¹ T(3^n)` at every point of the inner cube
`y + □_{n-1}`. -/
theorem exit_time_bounds_on_good_cube (d : ℕ) (hdim : 2 ≤ d) (cstar : ℝ)
    (hcstar : 0 < cstar) (Creg : ℝ) (hCreg : 0 < Creg) :
    ∃ gamma0 Cev C c : ℝ, 0 < gamma0 ∧ 0 < Cev ∧ 0 < C ∧ 0 < c ∧
      ∀ M : ABKModel d, Disorder.cstar M = cstar → M.gamma ≤ gamma0 →
      ∀ ep : ℝ, ep ∈ Set.Ioc (0 : ℝ) (1 / 4) →
      ∀ n : ℤ,
      ∀ (y : Vec d) (i : Fin d),
      ∀ omega ∈ qEvent M Creg Cev n y ep,
      ∀ m : ℤ, n ≤ m →
      ∀ (u v : H1Function (cubeSetAt y n)) (uRep vRep : Vec d → ℝ) (w : Vec d → ℝ≥0∞),
        IsDirichletSolutionAt ((Cutoff.coefficientCutoff M.nu m omega).toCoeffField) y n u
            (linearAxisDatum i) →
        IsDirichletSolutionAt (fun _ => (Annealed.sigmaBar M n : ℝ) • (1 : Mat d)) y n v
            (linearAxisDatum i) →
        IsCubeRepresentative y n u uRep →
        IsCubeRepresentative y n v vRep →
        (∀ x ∈ cubeSetAt y n, w x = ENNReal.ofReal (uRep x)) →
        (∀ x ∈ cubeSetAt y n, w x ≤ ENNReal.ofReal (C * exitTimeScale M n)) ∧
          (ep ≤ c → ∀ x ∈ cubeSetAt y (n - 1),
            ENNReal.ofReal (C⁻¹ * exitTimeScale M n) ≤ w x) := by
  obtain ⟨gamma0, Cev, C0, c0, hgamma0, hCev, hC0, hc0, hmain⟩ :=
    exit_time_homogenization_on_good_cube d hdim cstar hcstar Creg hCreg
  obtain ⟨C2, hC2, hbounds⟩ := homogenized_exit_time_bounds d hdim
  refine ⟨gamma0, Cev, max C0 (2 * C2), c0, hgamma0, hCev,
    lt_of_lt_of_le hC0 (le_max_left _ _), hc0, ?_⟩
  intro M hcs hgam ep hep n y i omega homega m hm u v uRep vRep w hu hv huRep hvRep hident
  have hTpos : 0 < exitTimeScale M n := exitTimeScale_pos M n
  set C : ℝ := max C0 (2 * C2) with hC_def
  have hCpos : 0 < C := lt_of_lt_of_le hC0 (le_max_left _ _)
  obtain ⟨-, uRep', huRep', -, hsup, hcomp⟩ :=
    hmain M hcs hgam ep hep n y i omega homega m hm u v vRep hu hv hvRep
  have hRep : Set.EqOn uRep uRep' (cubeSetAt y n) :=
    isCubeRepresentative_unique huRep huRep'
  obtain ⟨-, hvinf⟩ := hbounds M n y i v vRep hv hvRep
  constructor
  · intro x hx
    rw [hident x hx]
    refine ENNReal.ofReal_le_ofReal ?_
    have h1 : uRep x = uRep' x := hRep hx
    have h2 : |uRep' x| ≤ C0 * exitTimeScale M n := hsup x hx
    have h3 : C0 * exitTimeScale M n ≤ C * exitTimeScale M n :=
      mul_le_mul_of_nonneg_right (le_max_left _ _) hTpos.le
    have h4 := (abs_le.1 h2).2
    linarith only [h1, h3, h4]
  · intro hepc x hx
    have hsubcube : cubeSetAt y (n - 1) ⊆ cubeSetAt y n := by
      simpa using cubeSetAt_subset_cubeSetAt_succ y (n - 1)
    rw [hident x (hsubcube hx)]
    refine ENNReal.ofReal_le_ofReal ?_
    have h1 : uRep x = uRep' x := hRep (hsubcube hx)
    have h2 : (1 / 2 : ℝ) * vRep x ≤ uRep' x := (hcomp hepc x hx).1
    have h3 : exitTimeScale M n ≤ C2 * vRep x := hvinf x hx
    have h4 : 2 * C2 ≤ C := le_max_right _ _
    have hvpos : 0 < vRep x := by
      by_contra hcon
      push Not at hcon
      nlinarith only [h3, hTpos, hC2, hcon]
    have hinv : C⁻¹ * exitTimeScale M n ≤ (1 / 2 : ℝ) * vRep x := by
      rw [inv_mul_eq_div, div_le_iff₀ hCpos]
      nlinarith only [h3, h4, hvpos, hC2]
    linarith only [h1, h2, hinv]

end

end Algsuperdiff.Section5.Provider
