/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section5.Support.SolutionScaling

/-!
# LocalizedErrorScaling

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# The localized error read at a datum that is not normalized

The localized error `E(y+□_n)` is a supremum over the *normalized* forcing class
`[g]_{W^{1/2,∞}(y+□_n)} ≤ 1`, so on its own it says nothing about a solution
whose datum is not normalized.  The localized Dirichlet problem is homogeneous of
degree one in the pair (solution, datum), so the bound transfers to an arbitrary
datum of finite Hölder seminorm at the cost of the factor
`3^{n/2} [g]_{C^{0,1/2}(y+□_n)}`.  This is the companion, for the essential
supremum, of `localizedRegularity_apply_general`.

The degenerate branch `[g] = 0` is not a limiting case of the scaling: the datum
is then constant on the cube, both solutions vanish almost everywhere by the
uniqueness of the localized problem, and the essential supremum of their
difference vanishes outright.

## Main results

* `eLpNorm_top_sub_le_localizedError` — the homogeneous form.
* `eLpNorm_top_sub_le_of_mem_goodCubeEvent` — its reading on the good cube
  event, where the localized error is at most `ε`.

## References

* ABK26, the localized error of Section 5.1 and the triangle inequality closing
  the injection estimate.
-/

namespace Algsuperdiff.Section5.Provider

open Algsuperdiff.Section3
open Algsuperdiff.Section5.Support
open HCPolySupport MeasureTheory
open Algsuperdiff.Section4.Support
open Algsuperdiff.Section4.Provider.Schauder (rpow_three_pos)
open scoped ENNReal

noncomputable section

variable {d : ℕ}

/-! ## 1. The degenerate branch -/

/-- **A datum of vanishing Hölder seminorm forces the solution to vanish.**  On
the cube the datum is then constant, a constant datum pairs to zero against
every zero-trace gradient, and the almost-everywhere uniqueness of the localized
problem identifies the solution with zero. -/
theorem toFun_ae_zero_of_holderSeminormOn_eq_zero {y : Vec d} {n : ℤ} {a : CoeffField d}
    {lam Lam : ℝ} (hd : 0 < d) (hEll : IsEllipticFieldOn lam Lam (cubeSetAt y n) a)
    {g : Vec d → Vec d} (hg0 : holderSeminormOn (cubeSetAt y n) (1 / 2) g = 0)
    {u : H1Function (cubeSetAt y n)} (hu : IsDirichletSolutionAt a y n u g) :
    u.toFun =ᵐ[volume.restrict (cubeSetAt y n)] 0 := by
  have : IsFiniteMeasure (volumeMeasureOn (cubeSetAt y n)) :=
    (isOpenBoundedConvexDomain_cubeSetAt y n).isFiniteMeasure_restrict_volume
  have hbound : HolderSeminormBoundOn (cubeSetAt y n) (1 / 2) 0 g := by
    refine (holderSeminormOn_le_ofReal_iff le_rfl).1 ?_
    rw [hg0, ENNReal.ofReal_zero]
  have heqOn : Set.EqOn g (fun _ => g y) (cubeSetAt y n) := by
    intro x hx
    have h := hbound x hx y (mem_cubeSetAt_self y n)
    have hz : ‖g x - g y‖ ≤ 0 := by simpa using h
    have hzero : g x - g y = 0 := by
      simpa using le_antisymm hz (norm_nonneg _)
    exact sub_eq_zero.1 hzero
  have huconst : IsDirichletSolutionAt a y n u fun _ => g y :=
    (isDirichletSolutionAt_congr_eqOn heqOn).1 hu
  have hL2 : MemVectorL2 (cubeSetAt y n) fun _ : Vec d => g y := memLp_const _
  have huzero : IsDirichletSolutionAt a y n u fun _ => (0 : Vec d) := by
    simpa using isDirichletSolutionAt_sub_const hL2 (g y) huconst
  have hae := (isDirichletSolutionAt_ae_unique hd hEll huzero
    (isDirichletSolutionAt_zero a y n)).2
  filter_upwards [hae] with x hx
  show u.toFun x = 0
  rw [hx]
  rfl

/-! ## 2. The homogeneous form -/

private theorem rpow_three_half_mul' (n : ℤ) :
    Real.rpow 3 (-(n : ℝ) / 2) * Real.rpow 3 ((n : ℝ) / 2) = 1 := by
  have hsum : (-(n : ℝ) / 2) + ((n : ℝ) / 2) = 0 := by ring
  calc Real.rpow 3 (-(n : ℝ) / 2) * Real.rpow 3 ((n : ℝ) / 2)
      = Real.rpow 3 ((-(n : ℝ) / 2) + ((n : ℝ) / 2)) :=
        (Real.rpow_add (by norm_num : (0 : ℝ) < 3) _ _).symm
    _ = 1 := by rw [hsum]; exact Real.rpow_zero 3

private theorem eLpNorm_top_const_mul {U : Set (Vec d)} {t : ℝ} (ht : 0 ≤ t)
    (f : Vec d → ℝ) :
    eLpNorm (fun x => t * f x) ⊤ (volume.restrict U) =
      ENNReal.ofReal t * eLpNorm f ⊤ (volume.restrict U) := by
  have h : (fun x => t * f x) = t • f := rfl
  rw [h, eLpNorm_const_smul]
  simp [ENNReal.ofReal, Real.enorm_eq_ofReal ht]

/-- **The localized error bounds every pair of solutions, normalized or not.**

For a datum `g` of finite `1/2`-Hölder seminorm on `y + □_n`, a rough-field
solution `u` and a comparator solution `v` with that datum,

```text
  σ_n 3^{-n} ‖u - v‖_{L^∞(y+□_n)}
      ≤ E(y+□_n) · 3^{n/2} [g]_{C^{0,1/2}(y+□_n)} .
```
-/
theorem eLpNorm_top_sub_le_localizedError (M : ABKModel d) (n : ℤ) (y : Vec d)
    (omega : Cutoff.CutoffSample d) {g : Vec d → Vec d}
    (hg : holderSeminormOn (cubeSetAt y n) (1 / 2) g ≠ ⊤)
    {u v : H1Function (cubeSetAt y n)}
    (hu : IsDirichletSolutionAt ((Cutoff.coefficientCutoff M.nu n omega).toCoeffField)
      y n u g)
    (hv : IsDirichletSolutionAt (fun _ => (Annealed.sigmaBar M n : ℝ) • (1 : Mat d)) y n v g) :
    ENNReal.ofReal ((Annealed.sigmaBar M n : ℝ) * Real.rpow 3 (-(n : ℝ))) *
        eLpNorm (fun x => u.toFun x - v.toFun x) ⊤ (volume.restrict (cubeSetAt y n)) ≤
      localizedError M n y omega * ENNReal.ofReal (Real.rpow 3 ((n : ℝ) / 2)) *
        holderSeminormOn (cubeSetAt y n) (1 / 2) g := by
  set c : ℝ≥0∞ := ENNReal.ofReal ((Annealed.sigmaBar M n : ℝ) * Real.rpow 3 (-(n : ℝ)))
    with hcdef
  set A : ℝ≥0∞ := holderSeminormOn (cubeSetAt y n) (1 / 2) g with hAdef
  set N : ℝ≥0∞ := eLpNorm (fun x => u.toFun x - v.toFun x) ⊤ (volume.restrict (cubeSetAt y n))
    with hNdef
  have hd : 0 < d := Provider.Orlicz.dim_pos_of_model M
  rcases eq_or_ne A 0 with h0 | h0
  · obtain ⟨Lam, hEllu⟩ := exists_isEllipticFieldOn_cutoff M n n y omega
    have hau := toFun_ae_zero_of_holderSeminormOn_eq_zero hd hEllu h0 hu
    have hav := toFun_ae_zero_of_holderSeminormOn_eq_zero hd
      (isEllipticFieldOn_comparator M n y) h0 hv
    have hzero : N = 0 := by
      rw [hNdef]
      refine eLpNorm_eq_zero_of_ae_zero ?_
      filter_upwards [hau, hav] with x hx hx'
      show u.toFun x - v.toFun x = 0
      rw [hx, hx']
      simp
    rw [hzero, mul_zero]
    exact zero_le
  · have hApos : 0 < A.toReal := ENNReal.toReal_pos h0 hg
    set t : ℝ := Real.rpow 3 (-(n : ℝ) / 2) / A.toReal with htdef
    have htpos : 0 < t := div_pos (rpow_three_pos _) hApos
    have hscaled : holderSeminormOn (cubeSetAt y n) (1 / 2) (fun x => t • g x) =
        ENNReal.ofReal (Real.rpow 3 (-(n : ℝ) / 2)) := by
      rw [holderSeminormOn_const_smul _ _ htpos.le, ← hAdef, ← ENNReal.ofReal_toReal hg,
        ← ENNReal.ofReal_mul htpos.le, htdef, div_mul_cancel₀ _ hApos.ne']
    have hnorm : NormalizedForceAt y n fun x => t • g x := by
      refine (holderSeminormOn_le_ofReal_iff (rpow_three_pos _).le).1 ?_
      rw [hscaled]
    have hsolu := isDirichletSolutionAt_const_smul (a := _) t hu
    have hsolv := isDirichletSolutionAt_const_smul (a := _) t hv
    have hscale : eLpNorm (fun x => (t • u).toFun x - (t • v).toFun x) ⊤
        (volume.restrict (cubeSetAt y n)) = ENNReal.ofReal t * N := by
      have hfun : (fun x => (t • u).toFun x - (t • v).toFun x) =
          fun x => t * (u.toFun x - v.toFun x) := by
        funext x
        show t * u.toFun x - t * v.toFun x = t * (u.toFun x - v.toFun x)
        ring
      rw [hfun, eLpNorm_top_const_mul htpos.le, hNdef]
    have hle : ENNReal.ofReal t * (c * N) ≤ localizedError M n y omega := by
      have := le_localizedError M n y omega hnorm hsolu hsolv
      rw [hscale] at this
      calc ENNReal.ofReal t * (c * N) = c * (ENNReal.ofReal t * N) := by ring
        _ ≤ localizedError M n y omega := this
    have hne : ENNReal.ofReal t ≠ 0 := by
      rw [Ne, ENNReal.ofReal_eq_zero, not_le]; exact htpos
    have hfin : ENNReal.ofReal t ≠ ⊤ := ENNReal.ofReal_ne_top
    have hinv : c * N ≤ (ENNReal.ofReal t)⁻¹ * localizedError M n y omega := by
      calc c * N = (ENNReal.ofReal t)⁻¹ * (ENNReal.ofReal t * (c * N)) := by
            rw [← mul_assoc, ENNReal.inv_mul_cancel hne hfin, one_mul]
        _ ≤ (ENNReal.ofReal t)⁻¹ * localizedError M n y omega := by gcongr
    have hinvval : (ENNReal.ofReal t)⁻¹ = ENNReal.ofReal (Real.rpow 3 ((n : ℝ) / 2)) * A := by
      rw [← ENNReal.ofReal_inv_of_pos htpos, ← ENNReal.ofReal_toReal hg,
        ← ENNReal.ofReal_mul (rpow_three_pos _).le]
      congr 1
      rw [htdef, inv_div, div_eq_iff (rpow_three_pos ((-(n : ℝ) / 2))).ne']
      rw [mul_comm (Real.rpow 3 ((n : ℝ) / 2)) A.toReal, mul_assoc,
        mul_comm (Real.rpow 3 ((n : ℝ) / 2)), rpow_three_half_mul', mul_one]
    rw [hinvval] at hinv
    calc c * N ≤ ENNReal.ofReal (Real.rpow 3 ((n : ℝ) / 2)) * A * localizedError M n y omega :=
          hinv
      _ = localizedError M n y omega * ENNReal.ofReal (Real.rpow 3 ((n : ℝ) / 2)) * A := by ring

/-- **The reading on the good cube event.** -/
theorem eLpNorm_top_sub_le_of_mem_goodCubeEvent (M : ABKModel d) (Creg : ℝ) (n : ℤ)
    (y : Vec d) (ep : ℝ) {omega : Cutoff.CutoffSample d}
    (homega : omega ∈ goodCubeEvent M Creg n y ep) {g : Vec d → Vec d}
    (hg : holderSeminormOn (cubeSetAt y n) (1 / 2) g ≠ ⊤)
    {u v : H1Function (cubeSetAt y n)}
    (hu : IsDirichletSolutionAt ((Cutoff.coefficientCutoff M.nu n omega).toCoeffField)
      y n u g)
    (hv : IsDirichletSolutionAt (fun _ => (Annealed.sigmaBar M n : ℝ) • (1 : Mat d)) y n v g) :
    ENNReal.ofReal ((Annealed.sigmaBar M n : ℝ) * Real.rpow 3 (-(n : ℝ))) *
        eLpNorm (fun x => u.toFun x - v.toFun x) ⊤ (volume.restrict (cubeSetAt y n)) ≤
      ENNReal.ofReal ep * ENNReal.ofReal (Real.rpow 3 ((n : ℝ) / 2)) *
        holderSeminormOn (cubeSetAt y n) (1 / 2) g := by
  refine (eLpNorm_top_sub_le_localizedError M n y omega hg hu hv).trans ?_
  gcongr
  exact homega.1

end

end Algsuperdiff.Section5.Provider
