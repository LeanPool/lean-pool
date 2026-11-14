/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Frozen.Section5.InjectionInLInftyV2
public import LeanPool.Superdiffusion.Algsuperdiff.Section5.Support.HomogenizedExitTime

/-!
# ExitTimeHomogenization

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# Homogenization of the exit-time problem on a good cube

On the intersection of the good cube event and the large-scale event, the
injection estimate applied at the linear datum `g(x) = x_i e_i` compares the
rough-field solution of `-∇·a_m∇w = 1` on `y + □_n` with the homogenized profile
`w` of `-σ_n Δ w = 1`.  Inserting the two inputs of the previous modules — the
Hölder bound `[g]_{C^{0,1/2}(y+□_n)} ≤ 3^{n/2}` and the two-sided comparison of
`w` with the time scale `T(3^n) = 3^{2n}/σ_n` — turns the normalized estimate

```text
  σ_n 3^{-n} ‖w - w‖_{L^∞(y+□_n)} ≤ C ε 3^{n/2} [g]_{C^{0,1/2}(y+□_n)}
```

into `‖w - w‖_{L^∞(y+□_n)} ≤ C ε T(3^n)`, and then, once `ε` is below the
threshold `c(d,c⋆,C_reg)` returned by the injection estimate, into the two-sided
comparison `½ w ≤ w ≤ 2 w` on the inner cube `y + □_{n-1}` and the uniform
bound `‖w‖_{L^∞(y+□_n)} ≤ C T(3^n)`.

The `L^∞` norm of the difference is the honest essential supremum of the two
Sobolev functions.  The pointwise statements are read through continuous
representatives: the injection estimate's regularity clause bounds the
`1/2`-Hölder seminorm of a continuous representative of the rough-field
solution by a finite quantity at this datum, so such a representative exists,
and it is unique at every point of the cube.

## Main results

* `exit_time_homogenization_on_good_cube`.

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

private theorem rpow_three_neg_eq (n : ℤ) : Real.rpow 3 (-(n : ℝ)) = ((3 : ℝ) ^ n)⁻¹ := by
  change (3 : ℝ) ^ (-(n : ℝ)) = ((3 : ℝ) ^ n)⁻¹
  rw [Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 3)]
  congr 1
  exact Real.rpow_intCast 3 n

private theorem rpow_three_half_sq (n : ℤ) :
    Real.rpow 3 ((n : ℝ) / 2) * Real.rpow 3 ((n : ℝ) / 2) = (3 : ℝ) ^ n := by
  change (3 : ℝ) ^ ((n : ℝ) / 2) * (3 : ℝ) ^ ((n : ℝ) / 2) = (3 : ℝ) ^ n
  rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 3),
    show (n : ℝ) / 2 + (n : ℝ) / 2 = ((n : ℤ) : ℝ) by ring, Real.rpow_intCast]

/-- **Homogenization of the exit-time problem on a good cube.**  On the event of
the injection estimate, the rough-field solution of `-∇·a_m∇w = 1` on `y + □_n`
is within `C ε T(3^n)` of the homogenized profile in the uniform norm, is
bounded by `C T(3^n)`, and, once `ε` is below the threshold
`c(d,c⋆,C_reg)` returned by the injection estimate, is between half and twice
the homogenized profile on the inner cube. -/
theorem exit_time_homogenization_on_good_cube (d : ℕ) (hdim : 2 ≤ d) (cstar : ℝ)
    (hcstar : 0 < cstar) (Creg : ℝ) (hCreg : 0 < Creg) :
    ∃ gamma0 Cev C c : ℝ, 0 < gamma0 ∧ 0 < Cev ∧ 0 < C ∧ 0 < c ∧
      ∀ M : ABKModel d, Disorder.cstar M = cstar → M.gamma ≤ gamma0 →
      ∀ ep : ℝ, ep ∈ Set.Ioc (0 : ℝ) (1 / 4) →
      ∀ n : ℤ,
      ∀ (y : Vec d) (i : Fin d),
      ∀ omega ∈ goodCubeEvent M Creg n y ep ∩
          largeScaleEvent M n y (Cev⁻¹ * ep * (Real.sqrt M.gamma)⁻¹),
      ∀ m : ℤ, n ≤ m →
      ∀ (u v : H1Function (cubeSetAt y n)) (vRep : Vec d → ℝ),
        IsDirichletSolutionAt ((Cutoff.coefficientCutoff M.nu m omega).toCoeffField) y n u
            (linearAxisDatum i) →
        IsDirichletSolutionAt (fun _ => (Annealed.sigmaBar M n : ℝ) • (1 : Mat d)) y n v
            (linearAxisDatum i) →
        IsCubeRepresentative y n v vRep →
        eLpNorm (fun x => u.toFun x - v.toFun x) ⊤ (volume.restrict (cubeSetAt y n)) ≤
            ENNReal.ofReal (C * ep * exitTimeScale M n) ∧
          ∃ uRep : Vec d → ℝ, IsCubeRepresentative y n u uRep ∧
            (∀ x ∈ cubeSetAt y n, |uRep x - vRep x| ≤ C * ep * exitTimeScale M n) ∧
            (∀ x ∈ cubeSetAt y n, |uRep x| ≤ C * exitTimeScale M n) ∧
            (ep ≤ c → ∀ x ∈ cubeSetAt y (n - 1),
              (1 / 2 : ℝ) * vRep x ≤ uRep x ∧ uRep x ≤ 2 * vRep x) := by
  obtain ⟨gamma0, Cinj, hgamma0, hCinj, hseal⟩ :=
    Algsuperdiff.Frozen.Section5.injection_in_L_infty_v2 d cstar hcstar Creg hCreg
  obtain ⟨C2, hC2, hbounds⟩ := homogenized_exit_time_bounds d hdim
  refine ⟨gamma0, Cinj, max Cinj (C2 + Cinj / 4), min (1 / 4) (1 / (2 * Cinj * C2)),
    hgamma0, hCinj, lt_of_lt_of_le hCinj (le_max_left _ _),
    lt_min (by norm_num) (by positivity), ?_⟩
  intro M hcs hgam ep hep n y i omega homega m hm u v vRep hu hv hvRep
  have h3 : (0 : ℝ) < (3 : ℝ) ^ n := zpow_pos (by norm_num) n
  have hsig : (0 : ℝ) < (Annealed.sigmaBar M n : ℝ) := Provider.Orlicz.sigmaBar_pos M n
  have hTpos : 0 < exitTimeScale M n := exitTimeScale_pos M n
  have hepos : 0 < ep := hep.1
  set T : ℝ := exitTimeScale M n with hT_def
  set C : ℝ := max Cinj (C2 + Cinj / 4) with hC_def
  have hCpos : 0 < C := lt_of_lt_of_le hCinj (le_max_left _ _)
  -- the established estimate at the linear datum
  obtain ⟨hclause1, hclause2⟩ :=
    hseal M hcs hgam ep hep n y (linearAxisDatum i) omega homega m hm u v hu hv
  have hgbd : holderSeminormOn (cubeSetAt y n) (1 / 2) (linearAxisDatum i) ≤
      ENNReal.ofReal (Real.rpow 3 ((n : ℝ) / 2)) := holderSeminormOn_linearAxisDatum_le i y n
  have hrpos : (0 : ℝ) < Real.rpow 3 ((n : ℝ) / 2) := Real.rpow_pos_of_pos (by norm_num) _
  have hrneg : (0 : ℝ) < Real.rpow 3 (-(n : ℝ)) := Real.rpow_pos_of_pos (by norm_num) _
  -- the right-hand side of the first clause, evaluated at the datum
  have hprod : ENNReal.ofReal (Cinj * ep * Real.rpow 3 ((n : ℝ) / 2)) *
      holderSeminormOn (cubeSetAt y n) (1 / 2) (linearAxisDatum i) ≤
        ENNReal.ofReal ((Annealed.sigmaBar M n : ℝ) * Real.rpow 3 (-(n : ℝ))) *
          ENNReal.ofReal (Cinj * ep * T) := by
    refine le_trans (mul_le_mul_right hgbd _) ?_
    rw [← ENNReal.ofReal_mul (mul_nonneg (mul_nonneg hCinj.le hepos.le) hrpos.le),
      ← ENNReal.ofReal_mul (mul_nonneg hsig.le hrneg.le)]
    refine ENNReal.ofReal_le_ofReal (le_of_eq ?_)
    rw [rpow_three_neg_eq, hT_def, exitTimeScale]
    have : Real.rpow 3 ((n : ℝ) / 2) * Real.rpow 3 ((n : ℝ) / 2) = (3 : ℝ) ^ n :=
      rpow_three_half_sq n
    field_simp
    nlinarith only [this, h3, hsig]
  have hne0 : ENNReal.ofReal ((Annealed.sigmaBar M n : ℝ) * Real.rpow 3 (-(n : ℝ))) ≠ 0 := by
    rw [Ne, ENNReal.ofReal_eq_zero, not_le]
    exact mul_pos hsig hrneg
  have hnetop : ENNReal.ofReal ((Annealed.sigmaBar M n : ℝ) * Real.rpow 3 (-(n : ℝ))) ≠ ⊤ :=
    ENNReal.ofReal_ne_top
  have hLinf : eLpNorm (fun x => u.toFun x - v.toFun x) ⊤ (volume.restrict (cubeSetAt y n)) ≤
      ENNReal.ofReal (Cinj * ep * T) :=
    (ENNReal.mul_le_mul_iff_right hne0 hnetop).1 (le_trans hclause1 hprod)
  have hCinjC : Cinj * ep * T ≤ C * ep * T :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_max_left _ _) hepos.le) hTpos.le
  refine ⟨le_trans hLinf (ENNReal.ofReal_le_ofReal hCinjC), ?_⟩
  -- a continuous representative of the rough-field solution exists
  have hrepex : ∃ uRep : Vec d → ℝ, IsCubeRepresentative y n u uRep := by
    by_contra hno
    push Not at hno
    have hTop : (⨅ uRep : Vec d → ℝ, ⨅ _ : IsCubeRepresentative y n u uRep,
        ENNReal.ofReal ((Annealed.sigmaBar M n : ℝ) * Real.rpow 3 (-(n : ℝ) / 2)) *
          holderSeminormOn (cubeSetAt y n) (1 / 2) uRep) = ⊤ :=
      le_antisymm le_top (le_iInf fun r => le_iInf fun hr => absurd hr (hno r))
    rw [hTop] at hclause2
    have hfin : ENNReal.ofReal (Cinj * Real.rpow 3 ((n : ℝ) / 2)) *
        holderSeminormOn (cubeSetAt y n) (1 / 2) (linearAxisDatum i) ≠ ⊤ := by
      refine ne_top_of_le_ne_top ?_ (mul_le_mul_right hgbd _)
      rw [← ENNReal.ofReal_mul (mul_nonneg hCinj.le hrpos.le)]
      exact ENNReal.ofReal_ne_top
    exact hfin (top_le_iff.1 hclause2)
  obtain ⟨uRep, huRep⟩ := hrepex
  obtain ⟨hvsup, hvinf⟩ := hbounds M n y i v vRep hv hvRep
  -- the difference, pointwise on the cube
  have hae : (fun x => uRep x - vRep x)
      =ᵐ[volume.restrict (cubeSetAt y n)] fun x => u.toFun x - v.toFun x := by
    filter_upwards [huRep.1, hvRep.1] with x h1 h2
    rw [h1, h2]
  have hcont : ContinuousOn (fun x => uRep x - vRep x) (cubeSetAt y n) := huRep.2.sub hvRep.2
  have hsupeq : supNormOn (cubeSetAt y n) (fun x => uRep x - vRep x) =
      eLpNorm (fun x => u.toFun x - v.toFun x) ⊤ (volume.restrict (cubeSetAt y n)) :=
    (eLpNorm_top_restrict_eq_supNormOn_of_ae (isOpen_cubeSetAt y n) hae hcont).symm
  have hdiff : ∀ x ∈ cubeSetAt y n, |uRep x - vRep x| ≤ Cinj * ep * T := by
    intro x hx
    have hb : supNormOn (cubeSetAt y n) (fun x => uRep x - vRep x) ≤
        ENNReal.ofReal (Cinj * ep * T) := by rw [hsupeq]; exact hLinf
    have := (supNormOn_le_ofReal_iff
      (mul_nonneg (mul_nonneg hCinj.le hepos.le) hTpos.le)).1 hb x hx
    simpa [Real.norm_eq_abs] using this
  have hvbd : ∀ x ∈ cubeSetAt y n, |vRep x| ≤ C2 * T := by
    intro x hx
    have := (supNormOn_le_ofReal_iff (mul_nonneg hC2.le hTpos.le)).1 hvsup x hx
    simpa [Real.norm_eq_abs] using this
  refine ⟨uRep, huRep, fun x hx => le_trans (hdiff x hx) hCinjC, fun x hx => ?_, ?_⟩
  · have h1 := abs_le.1 (hdiff x hx)
    have h2 := abs_le.1 (hvbd x hx)
    have hep4 : ep ≤ 1 / 4 := hep.2
    have hkey : Cinj * ep * T + C2 * T ≤ C * T := by
      have hle : (C2 + Cinj / 4) * T ≤ C * T :=
        mul_le_mul_of_nonneg_right (le_max_right _ _) hTpos.le
      have hq : Cinj * ep * T ≤ Cinj * (1 / 4) * T :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hep4 hCinj.le) hTpos.le
      linarith only [hle, hq]
    refine abs_le.2 ⟨?_, ?_⟩
    · linarith only [h1.1, h2.1, hkey]
    · linarith only [h1.2, h2.2, hkey]
  · intro hepc x hx
    have hsubcube : cubeSetAt y (n - 1) ⊆ cubeSetAt y n := by
      simpa using cubeSetAt_subset_cubeSetAt_succ y (n - 1)
    have h1 := hdiff x (hsubcube hx)
    have h2 := hvinf x hx
    have hvpos : 0 < vRep x := by
      by_contra hcon
      push Not at hcon
      have : T ≤ C2 * vRep x := h2
      nlinarith only [this, hTpos, hC2, hcon]
    have hsmall : Cinj * ep * T ≤ (1 / 2 : ℝ) * vRep x := by
      have heple : ep ≤ 1 / (2 * Cinj * C2) := le_trans hepc (min_le_right _ _)
      have hTle : T ≤ C2 * vRep x := h2
      have hstep : Cinj * ep * T ≤ Cinj * ep * (C2 * vRep x) := by
        have : (0 : ℝ) ≤ Cinj * ep := by positivity
        nlinarith only [hTle, this]
      have hfac : Cinj * ep * (C2 * vRep x) ≤ (1 / 2 : ℝ) * vRep x := by
        have hfac0 : Cinj * ep * C2 ≤ 1 / 2 := by
          have hden : (0 : ℝ) < 2 * Cinj * C2 := by positivity
          rw [le_div_iff₀ hden] at heple
          nlinarith only [heple, hCinj, hC2]
        nlinarith only [hfac0, hvpos]
      linarith only [hstep, hfac]
    have habs := abs_le.1 h1
    constructor
    · linarith only [habs.1, hsmall]
    · linarith only [habs.2, hsmall, hvpos]

end

end Algsuperdiff.Section5.Provider
