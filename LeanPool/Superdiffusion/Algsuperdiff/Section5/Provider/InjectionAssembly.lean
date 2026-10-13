/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.BoundsEaL.SigmaBarLandmark
public import LeanPool.Superdiffusion.Algsuperdiff.Section5.Provider.IterationSeries
public import LeanPool.Superdiffusion.Algsuperdiff.Section5.Provider.LocalizedErrorScaling

/-!
# InjectionAssembly

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# The injection estimate on a good cube

On the intersection of the good cube event and the large-scale event, the
rough-field solution at any scale `m ≥ n` is close, on the cube `y + □_n`, to the
comparator solution at scale `n`, and inherits its `1/2`-Hölder regularity.

The proof is the perturbation iteration: the rough-field solution at scale `m`
is the sum of a series of increments, each obtained from the previous one by
solving a Laplace problem forced by `w_j ∇ · (k_m - k_n)` and then the
rough-field problem at scale `n` with the resulting gradient as datum.  The
large-scale event caps the size of `∇ · (k_m - k_n)` on the cube uniformly in
`m`; the good cube event caps the regularity of the solution map at scale `n`;
and the annealed normalization turns the product of the two caps into a factor
`≤ ε` once the threshold of the large-scale event is calibrated as
`C⁻¹ ε γ^{-1/2}`.  The series therefore converges geometrically in the
`1/2`-Hölder gauge, and converges in `L²` to the rough-field solution, so its
sum is that solution.  The supremum estimate follows from the Hölder estimate
because each increment has zero trace on the cube, and the triangle inequality
against the good event closes both conclusions.

The constant and the disorder regime are explicit:

```text
  C(d, c⋆, C_reg) = 1 + 3 C_reg + 96 d² C_step C_reg c⋆^{-1/2} ,
  γ₀(d, c⋆)       = C_land^{-10} c⋆^{10} ,
```

where `C_step` is the constant of one iteration step and `C_land` is the
constant of the annealed-gauge comparison `3^{γ j} σ_{j-1}^{-1} ≤ 16 c⋆^{-1/2}
γ^{1/2}`, whose regime is exactly `γ ≤ γ₀`.

## Main results

* `injection_in_L_infty_v2_provider`, at every scale `n : ℤ`.

## References

* ABK26, Proposition 5.1 (the injection estimate) and its proof.
-/

namespace Algsuperdiff.Section5.Provider

open Algsuperdiff.Section3
open Algsuperdiff.Section5.Support
open HCPolySupport MeasureTheory
open Algsuperdiff.Section4.Support
open Algsuperdiff.Section4.Provider.Schauder (rpow_three_pos)
open scoped ENNReal BigOperators

noncomputable section

variable {d : ℕ}

/-! ## 1. An arithmetic helper -/

private theorem rpow_three_mul (s t : ℝ) :
    Real.rpow 3 s * Real.rpow 3 t = Real.rpow 3 (s + t) := by
  show (3 : ℝ) ^ s * (3 : ℝ) ^ t = (3 : ℝ) ^ (s + t)
  rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 3)]

/-- **From the normalized gauge to a Hölder bound.**  The normalization factor
`σ_n 3^{-n/2}` is positive, so an `ℝ≥0∞` bound on the normalized gauge of a
function is a two-point bound with the reciprocal constant. -/
theorem holderSeminormBoundOn_of_sigmaBar_mul_le (M : ABKModel d) (n : ℤ) (y : Vec d)
    {r : Vec d → ℝ} {T : ℝ} (hT : 0 ≤ T)
    (h : ENNReal.ofReal ((Annealed.sigmaBar M n : ℝ) * Real.rpow 3 (-(n : ℝ) / 2)) *
        holderSeminormOn (cubeSetAt y n) (1 / 2) r ≤ ENNReal.ofReal T) :
    HolderSeminormBoundOn (cubeSetAt y n) (1 / 2)
      (((Annealed.sigmaBar M n : ℝ))⁻¹ * Real.rpow 3 ((n : ℝ) / 2) * T) r := by
  have hS : (0 : ℝ) < (Annealed.sigmaBar M n : ℝ) := Provider.Orlicz.sigmaBar_pos M n
  have hc : (0 : ℝ) < (Annealed.sigmaBar M n : ℝ) * Real.rpow 3 (-(n : ℝ) / 2) :=
    mul_pos hS (rpow_three_pos _)
  have hne : ENNReal.ofReal ((Annealed.sigmaBar M n : ℝ) * Real.rpow 3 (-(n : ℝ) / 2)) ≠ 0 := by
    rw [Ne, ENNReal.ofReal_eq_zero, not_le]
    exact hc
  have hinv : ((Annealed.sigmaBar M n : ℝ) * Real.rpow 3 (-(n : ℝ) / 2))⁻¹ =
      ((Annealed.sigmaBar M n : ℝ))⁻¹ * Real.rpow 3 ((n : ℝ) / 2) := by
    rw [mul_inv, rpow_three_neg_half_eq_inv, inv_inv]
  have hbd : holderSeminormOn (cubeSetAt y n) (1 / 2) r ≤
      ENNReal.ofReal (((Annealed.sigmaBar M n : ℝ))⁻¹ * Real.rpow 3 ((n : ℝ) / 2) * T) := by
    have hfold : ENNReal.ofReal ((Annealed.sigmaBar M n : ℝ) * Real.rpow 3 (-(n : ℝ) / 2)) *
        ENNReal.ofReal (((Annealed.sigmaBar M n : ℝ))⁻¹ * Real.rpow 3 ((n : ℝ) / 2) * T) =
        ENNReal.ofReal T := by
      rw [← ENNReal.ofReal_mul hc.le, ← hinv, mul_inv_cancel_left₀ hc.ne']
    rw [← ENNReal.mul_le_mul_iff_right hne ENNReal.ofReal_ne_top, hfold]
    exact h
  exact (holderSeminormOn_le_ofReal_iff
    (mul_nonneg (mul_nonneg (inv_nonneg.2 hS.le) (rpow_three_pos _).le) hT)).1 hbd

/-! ## 2. The injection estimate -/

/-- **Proposition 5.1.**  On the good cube event and the large-scale event with
threshold `C⁻¹ ε γ^{-1/2}`, the rough-field solution at any scale `m ≥ n` is
within `C ε 3^{n/2} [g]` of the comparator in the normalized `L^∞` gauge of the
cube, and its continuous representative obeys the normalized `1/2`-Hölder bound
`C 3^{n/2} [g]`.

The constant is `C(d, c⋆, C_reg)` and the disorder regime `γ ≤ γ₀(d, c⋆)` is the
one carried by the annealed-gauge comparison.

The scale `n` ranges over all of `ℤ`.  No step below uses a lower bound on it:
every power of `3` that occurs is a real power, the annealed gauge `σ_n` is
positive at every integer scale, and the cubes and the two events are defined
at every `n : ℤ`. -/
theorem injection_in_L_infty_v2_provider (d : ℕ) (cstar : ℝ) (_hcstar : 0 < cstar)
    (Creg : ℝ) (_hCreg : 0 < Creg) :
    ∃ gamma0 C : ℝ, 0 < gamma0 ∧ 0 < C ∧
      ∀ M : ABKModel d, Disorder.cstar M = cstar → M.gamma ≤ gamma0 →
      ∀ ep : ℝ, ep ∈ Set.Ioc (0 : ℝ) (1 / 4) →
      ∀ n : ℤ,
      ∀ (y : Vec d) (g : Vec d → Vec d),
      ∀ omega ∈ goodCubeEvent M Creg n y ep ∩
          largeScaleEvent M n y (C⁻¹ * ep * (Real.sqrt M.gamma)⁻¹),
      ∀ m : ℤ, n ≤ m →
      ∀ u v : H1Function (cubeSetAt y n),
        IsDirichletSolutionAt ((Cutoff.coefficientCutoff M.nu m omega).toCoeffField) y n u g →
        IsDirichletSolutionAt (fun _ => (Annealed.sigmaBar M n : ℝ) • (1 : Mat d)) y n v g →
        ENNReal.ofReal ((Annealed.sigmaBar M n : ℝ) * Real.rpow 3 (-(n : ℝ))) *
              eLpNorm (fun x => u.toFun x - v.toFun x) ⊤ (volume.restrict (cubeSetAt y n)) ≤
            ENNReal.ofReal (C * ep * Real.rpow 3 ((n : ℝ) / 2)) *
              holderSeminormOn (cubeSetAt y n) (1 / 2) g ∧
          (⨅ uRep : Vec d → ℝ, ⨅ _ : IsCubeRepresentative y n u uRep,
              ENNReal.ofReal ((Annealed.sigmaBar M n : ℝ) * Real.rpow 3 (-(n : ℝ) / 2)) *
                holderSeminormOn (cubeSetAt y n) (1 / 2) uRep) ≤
            ENNReal.ofReal (C * Real.rpow 3 ((n : ℝ) / 2)) *
              holderSeminormOn (cubeSetAt y n) (1 / 2) g := by
  by_cases hdim : 2 ≤ d
  swap
  · exact ⟨1, 1, one_pos, one_pos, fun M => absurd M.shellPrefix.dimension hdim⟩
  have hd : 0 < d := lt_of_lt_of_le (by norm_num) hdim
  obtain ⟨CL, hCL, hland⟩ :=
    Section4.Provider.BoundsEaL.exists_rpow_gamma_mul_inv_sigmaBar_sub_one_le d
  obtain ⟨CIter, hCIter, hseq⟩ := exists_iterationSequence hdim
  have hsqc : (0 : ℝ) < Real.sqrt cstar := Real.sqrt_pos.2 _hcstar
  have hCbig : (0 : ℝ) ≤ 96 * (d : ℝ) ^ 2 * CIter * Creg * (Real.sqrt cstar)⁻¹ :=
    mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) (sq_nonneg _)) hCIter.le)
      _hCreg.le) (inv_nonneg.2 hsqc.le)
  set C : ℝ := 1 + 3 * Creg + 96 * (d : ℝ) ^ 2 * CIter * Creg * (Real.sqrt cstar)⁻¹ with hCdef
  have hCpos : 0 < C := by rw [hCdef]; linarith only [hCbig, _hCreg]
  refine ⟨(CL⁻¹) ^ 10 * cstar ^ 10, C,
    mul_pos (pow_pos (inv_pos.2 hCL) 10) (pow_pos _hcstar 10), hCpos, ?_⟩
  intro M hcst hgam ep hep n y g omega homega m hnm u v hu hv
  have hep0 : 0 < ep := hep.1
  have hep4 : ep ≤ 1 / 4 := hep.2
  have hep1 : ep < 1 := by linarith only [hep4]
  have hd1 : (0 : ℝ) < 1 - ep := by linarith only [hep1]
  have hgpos : 0 < M.gamma := M.shellPrefix.gamma_pos
  have hsg : 0 < Real.sqrt M.gamma := Real.sqrt_pos.2 hgpos
  have hSpos : (0 : ℝ) < (Annealed.sigmaBar M n : ℝ) := Provider.Orlicz.sigmaBar_pos M n
  have hP : (0 : ℝ) < Real.rpow 3 ((n : ℝ) / 2) := rpow_three_pos _
  set theta : ℝ := C⁻¹ * ep * (Real.sqrt M.gamma)⁻¹ with hthetadef
  have hth0 : 0 < theta := by
    rw [hthetadef]
    exact mul_pos (mul_pos (inv_pos.2 hCpos) hep0) (inv_pos.2 hsg)
  have hmemG : omega ∈ goodCubeEvent M Creg n y ep := homega.1
  have hmemJ : omega ∈ largeScaleEvent M n y theta := homega.2
  rcases eq_or_ne (holderSeminormOn (cubeSetAt y n) (1 / 2) g) ⊤ with hgtop | hgne
  · have h1 : ENNReal.ofReal (C * ep * Real.rpow 3 ((n : ℝ) / 2)) ≠ 0 := by
      rw [Ne, ENNReal.ofReal_eq_zero, not_le]
      exact mul_pos (mul_pos hCpos hep0) hP
    have h2 : ENNReal.ofReal (C * Real.rpow 3 ((n : ℝ) / 2)) ≠ 0 := by
      rw [Ne, ENNReal.ofReal_eq_zero, not_le]
      exact mul_pos hCpos hP
    rw [hgtop, ENNReal.mul_top h1, ENNReal.mul_top h2]
    exact ⟨le_top, le_top⟩
  -- the datum, its Hölder constant and its square integrability
  set Kg : ℝ := (holderSeminormOn (cubeSetAt y n) (1 / 2) g).toReal with hKgdef
  have hKg0 : 0 ≤ Kg := ENNReal.toReal_nonneg
  have hgeq : holderSeminormOn (cubeSetAt y n) (1 / 2) g = ENNReal.ofReal Kg :=
    (ENNReal.ofReal_toReal hgne).symm
  have hKgb : HolderSeminormBoundOn (cubeSetAt y n) (1 / 2) Kg g :=
    (holderSeminormOn_le_ofReal_iff hKg0).1 (le_of_eq hgeq)
  have hgL2 : MemVectorL2 (cubeSetAt y n) g :=
    memVectorL2_of_holderSeminormBoundOn_cubeSetAt hKg0 (by norm_num) hKgb
  -- the perturbation field and its two sizes on the cube
  set kap : Vec d → Mat d :=
    fun z => Cutoff.cutoff m omega z - Cutoff.cutoff n omega z with hkapdef
  have hkC1 : ∀ p q : Fin d, ContDiff ℝ 1 fun x => kap x p q :=
    contDiff_one_cutoff_sub_entry omega hnm
  have hkskew : ∀ x : Vec d, matTranspose (kap x) = -kap x := matTranspose_cutoff_sub omega hnm
  set Sk : ℝ :=
    (d : ℝ) * (Real.sqrt d * (theta * Real.rpow 3 ((M.gamma - 1) * (n : ℝ)))) with hSkdef
  set Kk : ℝ := (d : ℝ) * (Real.sqrt 2 * ((d : ℝ) *
    (theta * Real.rpow 3 ((M.gamma - 3 / 2) * (n : ℝ))))) with hKkdef
  have hSk : ∀ x ∈ cubeSetAt y n, ‖matFieldDiv kap x‖ ≤ Sk := fun x hx =>
    norm_matFieldDiv_cutoff_sub_le hmemJ hth0.le hnm hx
  have hKk : HolderSeminormBoundOn (cubeSetAt y n) (1 / 2) Kk (matFieldDiv kap) :=
    holderSeminormBoundOn_matFieldDiv_cutoff_sub hmemJ hth0.le hnm
  -- the first increment
  obtain ⟨w0, hw0⟩ := exists_isDirichletSolutionAt_cutoff M n n y omega hKgb
  obtain ⟨w0Rep, hw0rep⟩ :=
    exists_isCubeRepresentative_of_mem_goodCubeEvent M Creg n y ep hmemG hgne hw0
  set K0 : ℝ := ((Annealed.sigmaBar M n : ℝ))⁻¹ * Real.rpow 3 ((n : ℝ) / 2) *
    (2 * Creg * Real.rpow 3 ((n : ℝ) / 2) * Kg) with hK0def
  have hCreg2 : (0 : ℝ) ≤ 2 * Creg := by linarith only [_hCreg]
  have hTnn : (0 : ℝ) ≤ 2 * Creg * Real.rpow 3 ((n : ℝ) / 2) * Kg :=
    mul_nonneg (mul_nonneg hCreg2 hP.le) hKg0
  have hK00 : 0 ≤ K0 := by
    rw [hK0def]
    exact mul_nonneg (mul_nonneg (inv_nonneg.2 hSpos.le) hP.le) hTnn
  have hw0K : HolderSeminormBoundOn (cubeSetAt y n) (1 / 2) K0 w0Rep := by
    refine holderSeminormBoundOn_of_sigmaBar_mul_le M n y hTnn ?_
    have h := holderSeminormOn_le_of_mem_goodCubeEvent M Creg n y ep hmemG hgne hw0 hw0rep
    refine h.trans (le_of_eq ?_)
    rw [hgeq, ← ENNReal.ofReal_mul hCreg2,
      ← ENNReal.ofReal_mul (mul_nonneg hCreg2 hP.le)]
  -- the contraction
  have hcontract : 2 * Creg * ((Annealed.sigmaBar M n : ℝ))⁻¹ * Real.rpow 3 (n : ℝ) * CIter *
      (Sk + Real.rpow 3 ((n : ℝ) / 2) * Kk) ≤ ep := by
    have hR1 : (0 : ℝ) < Real.rpow 3 ((M.gamma - 1) * (n : ℝ)) := rpow_three_pos _
    have hbase : (0 : ℝ) ≤ (d : ℝ) ^ 2 * (theta * Real.rpow 3 ((M.gamma - 1) * (n : ℝ))) :=
      mul_nonneg (sq_nonneg _) (mul_nonneg hth0.le hR1.le)
    have hKkrw : Real.rpow 3 ((n : ℝ) / 2) * Kk =
        Real.sqrt 2 * ((d : ℝ) ^ 2 * (theta * Real.rpow 3 ((M.gamma - 1) * (n : ℝ)))) := by
      have h : Real.rpow 3 ((n : ℝ) / 2) * Real.rpow 3 ((M.gamma - 3 / 2) * (n : ℝ)) =
          Real.rpow 3 ((M.gamma - 1) * (n : ℝ)) := by
        rw [rpow_three_mul]
        congr 1
        ring
      rw [hKkdef, show Real.rpow 3 ((n : ℝ) / 2) * ((d : ℝ) * (Real.sqrt 2 * ((d : ℝ) *
          (theta * Real.rpow 3 ((M.gamma - 3 / 2) * (n : ℝ)))))) =
          Real.sqrt 2 * ((d : ℝ) ^ 2 * (theta *
            (Real.rpow 3 ((n : ℝ) / 2) * Real.rpow 3 ((M.gamma - 3 / 2) * (n : ℝ))))) from by
          ring, h]
    have hSkle : Sk ≤ (d : ℝ) ^ 2 * (theta * Real.rpow 3 ((M.gamma - 1) * (n : ℝ))) := by
      rw [hSkdef]
      have hsd : Real.sqrt d ≤ (d : ℝ) := sqrt_dim_le_dim d
      have hnn : (0 : ℝ) ≤ theta * Real.rpow 3 ((M.gamma - 1) * (n : ℝ)) :=
        mul_nonneg hth0.le hR1.le
      calc (d : ℝ) * (Real.sqrt d * (theta * Real.rpow 3 ((M.gamma - 1) * (n : ℝ))))
          ≤ (d : ℝ) * ((d : ℝ) * (theta * Real.rpow 3 ((M.gamma - 1) * (n : ℝ)))) := by
            exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hsd hnn)
              (Nat.cast_nonneg d)
        _ = (d : ℝ) ^ 2 * (theta * Real.rpow 3 ((M.gamma - 1) * (n : ℝ))) := by ring
    have hs2 : Real.sqrt 2 ≤ 2 := by
      have h4 : Real.sqrt 4 = 2 := by
        rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 2)]
      calc Real.sqrt 2 ≤ Real.sqrt 4 := Real.sqrt_le_sqrt (by norm_num)
        _ = 2 := h4
    have hsum : Sk + Real.rpow 3 ((n : ℝ) / 2) * Kk ≤
        3 * ((d : ℝ) ^ 2 * (theta * Real.rpow 3 ((M.gamma - 1) * (n : ℝ)))) := by
      rw [hKkrw]
      have hmul : Real.sqrt 2 *
          ((d : ℝ) ^ 2 * (theta * Real.rpow 3 ((M.gamma - 1) * (n : ℝ)))) ≤
          2 * ((d : ℝ) ^ 2 * (theta * Real.rpow 3 ((M.gamma - 1) * (n : ℝ)))) :=
        mul_le_mul_of_nonneg_right hs2 hbase
      linarith only [hSkle, hmul]
    have hpref : (0 : ℝ) ≤ 2 * Creg * ((Annealed.sigmaBar M n : ℝ))⁻¹ *
        Real.rpow 3 (n : ℝ) * CIter :=
      mul_nonneg (mul_nonneg (mul_nonneg hCreg2 (inv_nonneg.2 hSpos.le))
        (rpow_three_pos _).le) hCIter.le
    have hstep1 := mul_le_mul_of_nonneg_left hsum hpref
    have hrw : 2 * Creg * ((Annealed.sigmaBar M n : ℝ))⁻¹ * Real.rpow 3 (n : ℝ) * CIter *
        (3 * ((d : ℝ) ^ 2 * (theta * Real.rpow 3 ((M.gamma - 1) * (n : ℝ))))) =
        6 * Creg * CIter * (d : ℝ) ^ 2 * theta *
          (Real.rpow 3 (M.gamma * (n : ℝ)) * ((Annealed.sigmaBar M n : ℝ))⁻¹) := by
      have hp : Real.rpow 3 (n : ℝ) * Real.rpow 3 ((M.gamma - 1) * (n : ℝ)) =
          Real.rpow 3 (M.gamma * (n : ℝ)) := by
        rw [rpow_three_mul]
        congr 1
        ring
      rw [show 2 * Creg * ((Annealed.sigmaBar M n : ℝ))⁻¹ * Real.rpow 3 (n : ℝ) * CIter *
          (3 * ((d : ℝ) ^ 2 * (theta * Real.rpow 3 ((M.gamma - 1) * (n : ℝ))))) =
          6 * Creg * CIter * (d : ℝ) ^ 2 * theta *
            ((Real.rpow 3 (n : ℝ) * Real.rpow 3 ((M.gamma - 1) * (n : ℝ))) *
              ((Annealed.sigmaBar M n : ℝ))⁻¹) from by ring, hp]
    have hlandn : Real.rpow 3 (M.gamma * (n : ℝ)) * ((Annealed.sigmaBar M n : ℝ))⁻¹ ≤
        16 * ((Real.sqrt cstar)⁻¹ * Real.sqrt M.gamma) := by
      have hreg : M.gamma ≤ (CL⁻¹) ^ 10 * (Disorder.cstar M) ^ 10 := by
        rw [hcst]; exact hgam
      have h := hland M hreg (n + 1)
      rw [show n + 1 - 1 = n by ring] at h
      have hcastr : (((n + 1 : ℤ)) : ℝ) = (n : ℝ) + 1 := by push_cast; ring
      rw [hcastr, hcst] at h
      have hmono : Real.rpow 3 (M.gamma * (n : ℝ)) ≤ Real.rpow 3 (M.gamma * ((n : ℝ) + 1)) := by
        show (3 : ℝ) ^ (M.gamma * (n : ℝ)) ≤ (3 : ℝ) ^ (M.gamma * ((n : ℝ) + 1))
        exact Real.rpow_le_rpow_of_exponent_le (by norm_num)
          (mul_le_mul_of_nonneg_left (by linarith only []) hgpos.le)
      have hmono' := mul_le_mul_of_nonneg_right hmono (inv_nonneg.2 hSpos.le)
      exact hmono'.trans h
    have hnn6 : (0 : ℝ) ≤ 6 * Creg * CIter * (d : ℝ) ^ 2 * theta :=
      mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) _hCreg.le) hCIter.le)
        (sq_nonneg _)) hth0.le
    have hstep2 := mul_le_mul_of_nonneg_left hlandn hnn6
    have hfinal : 6 * Creg * CIter * (d : ℝ) ^ 2 * theta *
        (16 * ((Real.sqrt cstar)⁻¹ * Real.sqrt M.gamma)) ≤ ep := by
      have hts : theta * Real.sqrt M.gamma = C⁻¹ * ep := by
        rw [hthetadef]
        field_simp
      have hAC : 96 * (d : ℝ) ^ 2 * CIter * Creg * (Real.sqrt cstar)⁻¹ ≤ C := by
        rw [hCdef]; linarith only [_hCreg]
      have hACinv : (96 * (d : ℝ) ^ 2 * CIter * Creg * (Real.sqrt cstar)⁻¹) * C⁻¹ ≤ 1 := by
        have h := mul_le_mul_of_nonneg_right hAC (inv_nonneg.2 hCpos.le)
        rwa [mul_inv_cancel₀ hCpos.ne'] at h
      rw [show 6 * Creg * CIter * (d : ℝ) ^ 2 * theta *
          (16 * ((Real.sqrt cstar)⁻¹ * Real.sqrt M.gamma)) =
          96 * (d : ℝ) ^ 2 * CIter * Creg * (Real.sqrt cstar)⁻¹ *
            (theta * Real.sqrt M.gamma) from by ring, hts]
      calc 96 * (d : ℝ) ^ 2 * CIter * Creg * (Real.sqrt cstar)⁻¹ * (C⁻¹ * ep)
          = 96 * (d : ℝ) ^ 2 * CIter * Creg * (Real.sqrt cstar)⁻¹ * C⁻¹ * ep := by ring
        _ ≤ 1 * ep := mul_le_mul_of_nonneg_right hACinv hep0.le
        _ = ep := one_mul ep
    calc 2 * Creg * ((Annealed.sigmaBar M n : ℝ))⁻¹ * Real.rpow 3 (n : ℝ) * CIter *
          (Sk + Real.rpow 3 ((n : ℝ) / 2) * Kk)
        ≤ 2 * Creg * ((Annealed.sigmaBar M n : ℝ))⁻¹ * Real.rpow 3 (n : ℝ) * CIter *
            (3 * ((d : ℝ) ^ 2 * (theta * Real.rpow 3 ((M.gamma - 1) * (n : ℝ))))) := hstep1
      _ = 6 * Creg * CIter * (d : ℝ) ^ 2 * theta *
            (Real.rpow 3 (M.gamma * (n : ℝ)) * ((Annealed.sigmaBar M n : ℝ))⁻¹) := hrw
      _ ≤ 6 * Creg * CIter * (d : ℝ) ^ 2 * theta *
            (16 * ((Real.sqrt cstar)⁻¹ * Real.sqrt M.gamma)) := hstep2
      _ ≤ ep := hfinal
  -- the iteration
  obtain ⟨w, wRep, lap, hw0eq, hrep, hzero, hKb, hlapsol, hlapsup, hlapnext⟩ :=
    hseq M Creg _hCreg.le n y ep omega hmemG kap hkC1 hkskew Kk Sk hKk hSk g w0 w0Rep K0 ep
      hK00 hep0.le hw0 hw0rep hw0K hcontract
  have hw0sol : IsDirichletSolutionAt ((Cutoff.coefficientCutoff M.nu n omega).toCoeffField)
      y n (w 0) g := by rw [hw0eq]; exact hw0
  have hwsucc : ∀ j, IsDirichletSolutionAt
      ((Cutoff.coefficientCutoff M.nu n omega).toCoeffField) y n (w (j + 1))
      fun x => matVecMul (kap x) ((w j).grad x) := fun j =>
    isDirichletSolutionAt_of_laplacianStep (hlapsol j) (hlapnext j)
  obtain ⟨Lam, hEll⟩ := exists_isEllipticFieldOn_cutoff M n n y omega
  have hB0 : (0 : ℝ) ≤ CIter * Real.rpow 3 ((n : ℝ) / 2) * K0 *
      (Sk + Real.rpow 3 ((n : ℝ) / 2) * Kk) := by
    have hSk0 : (0 : ℝ) ≤ Sk := le_trans (norm_nonneg _) (hSk y (mem_cubeSetAt_self y n))
    have hKk0 : (0 : ℝ) ≤ Kk := holderSeminormBoundOn_nonneg_cubeSetAt hd hKk
    exact mul_nonneg (mul_nonneg (mul_nonneg hCIter.le hP.le) hK00)
      (add_nonneg hSk0 (mul_nonneg hP.le hKk0))
  have hlimgrad := tendsto_sqrt_energy_grad_of_sup_bound hEll
    (G := fun j => (lap j).grad) (fun j => (lap j).grad_memVectorL2) hlapnext
    hB0 hep0.le hep1 hlapsup
  have hlimval :=
    (tendsto_sub_iterationPartialSum_cutoff M m n y omega hgL2 hw0sol hwsucc hu hlimgrad).2
  obtain ⟨uRep, huRep, huRepK, hutailK⟩ :=
    exists_isCubeRepresentative_of_tendsto hd hK00 hep0.le hep1 hrep hzero hKb hlimval
  -- the two conclusions
  constructor
  · -- the supremum estimate
    have hzeroU : ∃ z : H10Function (cubeSetAt y n),
        ∀ x, (u - w 0).toFun x = z.toH1Function.toFun x := by
      obtain ⟨z1, hz1, -⟩ := hu.1
      obtain ⟨z2, hz2, -⟩ := hw0sol.1
      refine ⟨z1 - z2, fun x => ?_⟩
      have h1 : (u - w 0).toFun x = u.toFun x - (w 0).toFun x := by
        rw [H1Function.sub_toFun]
      have h2 : ((z1 - z2).toH1Function).toFun x =
          z1.toH1Function.toFun x - z2.toH1Function.toFun x := by
        show (z1.toH1Function - z2.toH1Function).toFun x =
          z1.toH1Function.toFun x - z2.toH1Function.toFun x
        rw [H1Function.sub_toFun]
      rw [h1, h2, hz1, hz2]
    have hrepU : IsCubeRepresentative y n (u - w 0) fun x => uRep x - wRep 0 x :=
      isCubeRepresentative_sub huRep (hrep 0)
    have hKtail : (0 : ℝ) ≤ K0 * ep / (1 - ep) :=
      div_nonneg (mul_nonneg hK00 hep0.le) hd1.le
    have hsupU := sup_le_of_zeroTrace hd hKtail hzeroU hrepU hutailK
    have hE1 : eLpNorm (fun x => u.toFun x - (w 0).toFun x) ⊤
        (volume.restrict (cubeSetAt y n)) ≤
        ENNReal.ofReal (Real.rpow 3 ((n : ℝ) / 2) * (K0 * ep / (1 - ep))) := by
      rw [eLpNorm_top_sub_eq_supNormOn_sub huRep (hrep 0)]
      exact (supNormOn_le_ofReal_iff (mul_nonneg hP.le hKtail)).2 hsupU
    have hE2 := eLpNorm_top_sub_le_of_mem_goodCubeEvent M Creg n y ep hmemG hgne hw0sol hv
    have hsplit : eLpNorm (fun x => u.toFun x - v.toFun x) ⊤
        (volume.restrict (cubeSetAt y n)) ≤
        eLpNorm (fun x => u.toFun x - (w 0).toFun x) ⊤ (volume.restrict (cubeSetAt y n)) +
          eLpNorm (fun x => (w 0).toFun x - v.toFun x) ⊤
            (volume.restrict (cubeSetAt y n)) := by
      have hfun : (fun x => u.toFun x - v.toFun x) =
          (fun x => u.toFun x - (w 0).toFun x) + fun x => (w 0).toFun x - v.toFun x := by
        funext x
        show u.toFun x - v.toFun x = u.toFun x - (w 0).toFun x + ((w 0).toFun x - v.toFun x)
        ring
      rw [hfun]
      exact eLpNorm_add_le (show (1 : ℝ≥0∞) ≤ ⊤ by simp)
    have harith1 : (Annealed.sigmaBar M n : ℝ) * Real.rpow 3 (-(n : ℝ)) *
        (Real.rpow 3 ((n : ℝ) / 2) * (K0 * ep / (1 - ep))) +
          ep * Real.rpow 3 ((n : ℝ) / 2) * Kg ≤ C * ep * Real.rpow 3 ((n : ℝ) / 2) * Kg := by
      have hpow : Real.rpow 3 (-(n : ℝ)) * Real.rpow 3 ((n : ℝ) / 2) *
          Real.rpow 3 ((n : ℝ) / 2) * Real.rpow 3 ((n : ℝ) / 2) =
          Real.rpow 3 ((n : ℝ) / 2) := by
        rw [rpow_three_mul, rpow_three_mul, rpow_three_mul]
        congr 1
        ring
      have hSinv : (Annealed.sigmaBar M n : ℝ) * ((Annealed.sigmaBar M n : ℝ))⁻¹ = 1 :=
        mul_inv_cancel₀ hSpos.ne'
      have hexp : (Annealed.sigmaBar M n : ℝ) * Real.rpow 3 (-(n : ℝ)) *
          (Real.rpow 3 ((n : ℝ) / 2) * (K0 * ep / (1 - ep))) =
          Real.rpow 3 ((n : ℝ) / 2) * (2 * Creg * Kg * ep / (1 - ep)) := by
        rw [hK0def, show (Annealed.sigmaBar M n : ℝ) * Real.rpow 3 (-(n : ℝ)) *
            (Real.rpow 3 ((n : ℝ) / 2) * (((Annealed.sigmaBar M n : ℝ))⁻¹ *
              Real.rpow 3 ((n : ℝ) / 2) * (2 * Creg * Real.rpow 3 ((n : ℝ) / 2) * Kg) *
                ep / (1 - ep))) =
            (Annealed.sigmaBar M n : ℝ) * ((Annealed.sigmaBar M n : ℝ))⁻¹ *
              (Real.rpow 3 (-(n : ℝ)) * Real.rpow 3 ((n : ℝ) / 2) *
                Real.rpow 3 ((n : ℝ) / 2) * Real.rpow 3 ((n : ℝ) / 2)) *
              (2 * Creg * Kg * ep / (1 - ep)) from by ring, hSinv, hpow, one_mul]
      rw [hexp]
      have hPKg : (0 : ℝ) ≤ Real.rpow 3 ((n : ℝ) / 2) * Kg := mul_nonneg hP.le hKg0
      have hCKe : (0 : ℝ) ≤ 8 / 3 * Creg * Kg * ep :=
        mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) _hCreg.le) hKg0) hep0.le
      have h34 : (3 : ℝ) / 4 ≤ 1 - ep := by linarith only [hep4]
      have hfrac : 2 * Creg * Kg * ep / (1 - ep) ≤ 8 / 3 * Creg * Kg * ep := by
        rw [div_le_iff₀ hd1]
        have h := mul_le_mul_of_nonneg_left h34 hCKe
        linarith only [h]
      have hstep := mul_le_mul_of_nonneg_left hfrac hP.le
      have hCge : 8 / 3 * Creg + 1 ≤ C := by rw [hCdef]; linarith only [hCbig, _hCreg]
      have hnn : (0 : ℝ) ≤ ep * (Real.rpow 3 ((n : ℝ) / 2) * Kg) := mul_nonneg hep0.le hPKg
      have hlast := mul_le_mul_of_nonneg_right hCge hnn
      linarith only [hstep, hlast]
    calc ENNReal.ofReal ((Annealed.sigmaBar M n : ℝ) * Real.rpow 3 (-(n : ℝ))) *
          eLpNorm (fun x => u.toFun x - v.toFun x) ⊤ (volume.restrict (cubeSetAt y n))
        ≤ ENNReal.ofReal ((Annealed.sigmaBar M n : ℝ) * Real.rpow 3 (-(n : ℝ))) *
            (eLpNorm (fun x => u.toFun x - (w 0).toFun x) ⊤
                (volume.restrict (cubeSetAt y n)) +
              eLpNorm (fun x => (w 0).toFun x - v.toFun x) ⊤
                (volume.restrict (cubeSetAt y n))) := by gcongr
      _ = ENNReal.ofReal ((Annealed.sigmaBar M n : ℝ) * Real.rpow 3 (-(n : ℝ))) *
            eLpNorm (fun x => u.toFun x - (w 0).toFun x) ⊤
              (volume.restrict (cubeSetAt y n)) +
          ENNReal.ofReal ((Annealed.sigmaBar M n : ℝ) * Real.rpow 3 (-(n : ℝ))) *
            eLpNorm (fun x => (w 0).toFun x - v.toFun x) ⊤
              (volume.restrict (cubeSetAt y n)) := mul_add _ _ _
      _ ≤ ENNReal.ofReal ((Annealed.sigmaBar M n : ℝ) * Real.rpow 3 (-(n : ℝ))) *
            ENNReal.ofReal (Real.rpow 3 ((n : ℝ) / 2) * (K0 * ep / (1 - ep))) +
          ENNReal.ofReal ep * ENNReal.ofReal (Real.rpow 3 ((n : ℝ) / 2)) *
            ENNReal.ofReal Kg := by
            refine add_le_add ?_ ?_
            · gcongr
            · rwa [hgeq] at hE2
      _ = ENNReal.ofReal ((Annealed.sigmaBar M n : ℝ) * Real.rpow 3 (-(n : ℝ)) *
            (Real.rpow 3 ((n : ℝ) / 2) * (K0 * ep / (1 - ep))) +
              ep * Real.rpow 3 ((n : ℝ) / 2) * Kg) := by
            rw [← ENNReal.ofReal_mul (le_of_lt (mul_pos hSpos (rpow_three_pos _))),
              ← ENNReal.ofReal_mul hep0.le, ← ENNReal.ofReal_mul (mul_nonneg hep0.le hP.le),
              ← ENNReal.ofReal_add (mul_nonneg (le_of_lt (mul_pos hSpos (rpow_three_pos _)))
                (mul_nonneg hP.le (div_nonneg (mul_nonneg hK00 hep0.le) hd1.le)))
                (mul_nonneg (mul_nonneg hep0.le hP.le) hKg0)]
      _ ≤ ENNReal.ofReal (C * ep * Real.rpow 3 ((n : ℝ) / 2) * Kg) :=
            ENNReal.ofReal_le_ofReal harith1
      _ = ENNReal.ofReal (C * ep * Real.rpow 3 ((n : ℝ) / 2)) *
            holderSeminormOn (cubeSetAt y n) (1 / 2) g := by
            rw [hgeq, ← ENNReal.ofReal_mul
              (mul_nonneg (mul_nonneg hCpos.le hep0.le) hP.le)]
  · -- the Hölder estimate
    rw [iInf_isCubeRepresentative_holderSeminormOn huRep, hgeq,
      ← ENNReal.ofReal_mul (mul_nonneg hCpos.le hP.le)]
    have hb : holderSeminormOn (cubeSetAt y n) (1 / 2) uRep ≤
        ENNReal.ofReal (K0 / (1 - ep)) :=
      (holderSeminormOn_le_ofReal_iff (div_nonneg hK00 hd1.le)).2 huRepK
    have hkey : (Annealed.sigmaBar M n : ℝ) * Real.rpow 3 (-(n : ℝ) / 2) * K0 =
        2 * Creg * Real.rpow 3 ((n : ℝ) / 2) * Kg := by
      rw [hK0def, rpow_three_neg_half_eq_inv]
      field_simp
    have harith2 : (Annealed.sigmaBar M n : ℝ) * Real.rpow 3 (-(n : ℝ) / 2) *
        (K0 / (1 - ep)) ≤ C * Real.rpow 3 ((n : ℝ) / 2) * Kg := by
      have hrw : (Annealed.sigmaBar M n : ℝ) * Real.rpow 3 (-(n : ℝ) / 2) * (K0 / (1 - ep)) =
          2 * Creg * Real.rpow 3 ((n : ℝ) / 2) * Kg / (1 - ep) := by
        rw [← hkey]; ring
      rw [hrw, div_le_iff₀ hd1]
      have hPKg : (0 : ℝ) ≤ Real.rpow 3 ((n : ℝ) / 2) * Kg := mul_nonneg hP.le hKg0
      have h3C : 3 * Creg ≤ C := by rw [hCdef]; linarith only [hCbig, _hCreg]
      have h34 : (3 : ℝ) / 4 ≤ 1 - ep := by linarith only [hep4]
      have hCregPK : (0 : ℝ) ≤ Creg * (Real.rpow 3 ((n : ℝ) / 2) * Kg) :=
        mul_nonneg _hCreg.le hPKg
      have hprod : 3 * Creg * (3 / 4) ≤ C * (1 - ep) :=
        mul_le_mul h3C h34 (by norm_num) (le_trans (by linarith only [_hCreg]) h3C)
      have hfin := mul_le_mul_of_nonneg_right hprod hPKg
      linarith only [hfin, hCregPK]
    calc ENNReal.ofReal ((Annealed.sigmaBar M n : ℝ) * Real.rpow 3 (-(n : ℝ) / 2)) *
          holderSeminormOn (cubeSetAt y n) (1 / 2) uRep
        ≤ ENNReal.ofReal ((Annealed.sigmaBar M n : ℝ) * Real.rpow 3 (-(n : ℝ) / 2)) *
            ENNReal.ofReal (K0 / (1 - ep)) := by gcongr
      _ = ENNReal.ofReal ((Annealed.sigmaBar M n : ℝ) * Real.rpow 3 (-(n : ℝ) / 2) *
            (K0 / (1 - ep))) :=
          (ENNReal.ofReal_mul (le_of_lt (mul_pos hSpos (rpow_three_pos _)))).symm
      _ ≤ ENNReal.ofReal (C * Real.rpow 3 ((n : ℝ) / 2) * Kg) :=
          ENNReal.ofReal_le_ofReal harith2

end

end Algsuperdiff.Section5.Provider
