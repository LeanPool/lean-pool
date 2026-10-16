/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Frozen.Section4.GeneratorRenormalization
public import LeanPool.Superdiffusion.Algsuperdiff.Section5.Provider.CutoffLimitDatum

/-!
# GeneratorRenormalizationLimit

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# Renormalization of the generator for the coefficient field `a = nu I + k`

The renormalization estimate of the generator is proved for the infrared
truncations `a_L = nu I + k_L` of the coefficient field, uniformly in the
truncation scale `L` above the cube scale `m`.  This file removes the
truncation: the same effective diffusivity `sigmaBar_m` and the same random
error amplitude control the Dirichlet solutions of the full coefficient field
`a = nu I + k` itself, on the carrier of the full sample and under its law.

Two mechanisms are combined.  The probabilistic half is a transfer along the
inclusion of the full-sample carrier into the carrier of the truncations: the
moments of the error amplitude, its measurability, and the almost-sure clause
all move along that inclusion with no loss of constant.  The analytic half is
the limit `L -> infinity`.  For a datum `h` and a forcing `g` fixed once and
for all, the Dirichlet problem for `a_L` has a solution `u_L` with the same
datum at every scale, and the energy estimate for the difference of two
solutions bounds the gradient of `u_L - u` by the supremum distance of `a_L`
and `a` on the cube, which is geometric in `L`.  Hence `u_L -> u` in `H^1`, and
both clauses of the estimate are closed under that convergence: the uniform
clause because an almost-everywhere bound valid along an `L^2`-convergent
family passes to its limit, and the energy clause because the Dirichlet energy
is continuous along gradients converging in `L^2`.

No uniqueness of the Dirichlet solution is used: the solutions `u_L` are chosen
arbitrarily among those with the prescribed datum, and their difference with
the given solution `u` of the full-field problem is a function of zero trace,
which is all the energy estimate needs.

## Main results

* `abs_integral_vecNormSq_sub_le` — the Dirichlet energy is continuous in the
  gradient, with the Cauchy--Schwarz modulus.
* `tendsto_sqrt_energy_grad_cutoff_of_h10Diff` — the gradients of the truncated
  solutions converge in `L^2` to the gradient of the full-field solution.
* `clauses_stream_of_cutoff` — the two clauses of the renormalization estimate
  pass from the truncated fields to the full field.
* `generator_renormalization_provider` — the renormalization estimate for the
  coefficient field itself.

## References

* ABK26, Theorem B, and the passage `L -> infinity` from the truncated fields
  `a_L` to `a = nu I + k`.
-/

namespace Algsuperdiff.Section4.Provider.Introduction

open _root_.Algsuperdiff.Section3 _root_.Algsuperdiff.Section5.Field
open _root_.Algsuperdiff.Section5.Support _root_.Algsuperdiff.Section4.Support
open _root_.Algsuperdiff.Section4.Provider.Holder _root_.Algsuperdiff.Section4.Provider.Schauder
open _root_.Algsuperdiff.Section5.Provider
open _root_.Filter _root_.HCPolySupport _root_.MeasureTheory _root_.Topology
open scoped ENNReal

noncomputable section

variable {d : ℕ}

/-! ## 1. Continuity of the Dirichlet energy in the gradient -/

/-- The square of the norm of a square-integrable field is integrable. -/
private theorem integrableOn_sq_norm {U : Set (Vec d)} {F : Vec d → Vec d}
    (hF : MemVectorL2 U F) : IntegrableOn (fun x => ‖F x‖ ^ (2 : ℕ)) U := by
  have hn : MemLp (fun x => ‖F x‖) 2 (volume.restrict U) := hF.norm
  have h : Integrable (fun x => ‖F x‖ * ‖F x‖) (volume.restrict U) := hn.integrable_mul hn
  simpa only [pow_two] using! h

/-- **The Dirichlet energy is continuous in the gradient.**  Two square-integrable fields
have energies differing by at most the Cauchy--Schwarz modulus of their difference: expanding
`|F|² = |F - G|² + 2 (F - G) · G + |G|²` and integrating leaves the square of the `L²` distance
plus twice the pairing of that distance with the second field. -/
theorem abs_integral_vecNormSq_sub_le {U : Set (Vec d)} (hU : MeasurableSet U)
    {F G : Vec d → Vec d} (hF : MemVectorL2 U F) (hG : MemVectorL2 U G) :
    |(∫ x in U, vecNormSq (F x) ∂volume) - ∫ x in U, vecNormSq (G x) ∂volume| ≤
      (d : ℝ) * (Real.sqrt (∫ x in U, ‖F x - G x‖ ^ (2 : ℕ) ∂volume) *
          Real.sqrt (∫ x in U, ‖F x - G x‖ ^ (2 : ℕ) ∂volume)) +
        2 * ((d : ℝ) * (Real.sqrt (∫ x in U, ‖F x - G x‖ ^ (2 : ℕ) ∂volume) *
          Real.sqrt (∫ x in U, ‖G x‖ ^ (2 : ℕ) ∂volume))) := by
  have hD : MemVectorL2 U (fun x => F x - G x) := hF.sub hG
  have hInt1 : IntegrableOn (fun x => vecNormSq (F x - G x)) U :=
    integrableOn_vecDot_of_memVectorL2 hD hD
  have hInt2 : IntegrableOn (fun x => vecDot (F x - G x) (G x)) U :=
    integrableOn_vecDot_of_memVectorL2 hD hG
  have hIntG : IntegrableOn (fun x => vecNormSq (G x)) U :=
    integrableOn_vecDot_of_memVectorL2 hG hG
  have hid : ∀ x : Vec d, vecNormSq (F x) =
      vecNormSq (F x - G x) + 2 * vecDot (F x - G x) (G x) + vecNormSq (G x) := by
    intro x
    simp only [vecNormSq, vecDot, Pi.sub_apply, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    ring
  have hIntF : IntegrableOn (fun x => vecNormSq (F x)) U :=
    integrableOn_vecDot_of_memVectorL2 hF hF
  have hInt2' : IntegrableOn (fun x => 2 * vecDot (F x - G x) (G x)) U := hInt2.const_mul 2
  have heq : (∫ x in U, vecNormSq (F x) ∂volume) - (∫ x in U, vecNormSq (G x) ∂volume) =
      (∫ x in U, vecNormSq (F x - G x) ∂volume) +
        2 * (∫ x in U, vecDot (F x - G x) (G x) ∂volume) := by
    rw [← integral_sub hIntF hIntG]
    have e1 : (∫ x in U, (vecNormSq (F x) - vecNormSq (G x)) ∂volume) =
        ∫ x in U, (vecNormSq (F x - G x) + 2 * vecDot (F x - G x) (G x)) ∂volume :=
      integral_congr_ae (Filter.Eventually.of_forall fun x => by
        change vecNormSq (F x) - vecNormSq (G x) = _
        rw [hid x]; ring)
    rw [e1, integral_add hInt1 hInt2', integral_const_mul]
  have hA0 : (0 : ℝ) ≤ ∫ x in U, vecNormSq (F x - G x) ∂volume :=
    integral_nonneg fun x => vecNormSq_nonneg _
  have hDsq : Real.sqrt (∫ x in U, ‖F x - G x‖ ^ (2 : ℕ) ∂volume) *
      Real.sqrt (∫ x in U, ‖F x - G x‖ ^ (2 : ℕ) ∂volume) =
      ∫ x in U, ‖F x - G x‖ ^ (2 : ℕ) ∂volume :=
    Real.mul_self_sqrt (integral_nonneg fun _ => by positivity)
  have hbound1 : (∫ x in U, vecNormSq (F x - G x) ∂volume) ≤
      (d : ℝ) * (Real.sqrt (∫ x in U, ‖F x - G x‖ ^ (2 : ℕ) ∂volume) *
        Real.sqrt (∫ x in U, ‖F x - G x‖ ^ (2 : ℕ) ∂volume)) := by
    rw [hDsq, ← integral_const_mul]
    refine integral_mono hInt1 ((integrableOn_sq_norm hD).const_mul _)
      fun x => ?_
    exact vecNormSq_le_dim_mul_sq_norm (F x - G x)
  have hbound2 : |∫ x in U, vecDot (F x - G x) (G x) ∂volume| ≤
      (d : ℝ) * (Real.sqrt (∫ x in U, ‖F x - G x‖ ^ (2 : ℕ) ∂volume) *
        Real.sqrt (∫ x in U, ‖G x‖ ^ (2 : ℕ) ∂volume)) := by
    have hkey := abs_setIntegral_vecDot_le_of_norm_le U hU (c := 1) zero_le_one hD hG
      (fun x _ => by rw [one_mul])
    simpa using hkey
  rw [heq]
  calc |(∫ x in U, vecNormSq (F x - G x) ∂volume) +
          2 * (∫ x in U, vecDot (F x - G x) (G x) ∂volume)|
      ≤ |∫ x in U, vecNormSq (F x - G x) ∂volume| +
          |2 * (∫ x in U, vecDot (F x - G x) (G x) ∂volume)| := abs_add_le _ _
    _ = (∫ x in U, vecNormSq (F x - G x) ∂volume) +
          2 * |∫ x in U, vecDot (F x - G x) (G x) ∂volume| := by
        rw [abs_of_nonneg hA0, abs_mul, abs_of_nonneg (by norm_num : (0:ℝ) ≤ 2)]
    _ ≤ _ := by linarith only [hbound1, hbound2]

/-! ## 2. Convergence of the truncated solutions in the energy norm -/

/-- **The gradients of the truncated solutions converge in `L²` to the gradient of the
full-field solution**, for a common datum and a common forcing.  The difference of the two
solutions is a function of zero trace, so the energy estimate bounds its gradient by the
supremum distance of the two coefficient fields on the cube, which is geometric in the
truncation scale. -/
theorem tendsto_sqrt_energy_grad_cutoff_of_h10Diff (M : ABKModel d)
    (omega : FullSample d M.gamma)
    (y : Vec d) (n : ℤ) {h : H1Function (cubeSetAt y n)} {g : Vec d → Vec d}
    {u : ℤ → H1Function (cubeSetAt y n)} {v : H1Function (cubeSetAt y n)}
    (hu : ∀ L : ℤ, HasZeroTraceDifferenceOn (cubeSetAt y n) (u L) h)
    (huw : ∀ L : ℤ, IsDivFormWeakSolutionOn
      ((Cutoff.coefficientCutoff M.nu L omega.1).toCoeffField) (cubeSetAt y n) (u L) g)
    (hv : HasZeroTraceDifferenceOn (cubeSetAt y n) v h)
    (hvw : IsDivFormWeakSolutionOn (streamCoefficient M.nu omega) (cubeSetAt y n) v g) :
    Tendsto (fun L : ℤ =>
        Real.sqrt (∫ x in cubeSetAt y n, ‖(u L).grad x - v.grad x‖ ^ (2 : ℕ) ∂volume))
      atTop (𝓝 0) := by
  exact Algsuperdiff.Section5.Provider.tendsto_sqrt_energy_grad_cutoff_of_h10Diff
    M omega y n hu huw hv hvw

/-! ## 3. The two clauses pass to the full field -/

/-- **The two clauses of the renormalization estimate pass from the truncated coefficient
fields to the full stream field.**  The datum `h`, the homogenized solution `v` and the forcing
`g` are fixed; the hypothesis is that both clauses hold, with the same two right-hand sides, for
every solution of the truncated problem with that datum and that forcing at every truncation
scale above `m`.  The uniform clause passes to the limit because an almost-everywhere bound
along an `L²`-convergent family is inherited by the limit; the energy clause passes because the
Dirichlet energy is continuous along gradients converging in `L²`.  The cube is presented as an
arbitrary set equal to the cube centred at the origin, so that the estimate can be read on the
origin cube of the renormalization statement. -/
theorem clauses_stream_of_cutoff (M : ABKModel d) (omega : FullSample d M.gamma)
    (m : ℤ) (V : Set (Vec d)) (hV : cubeSetAt (0 : Vec d) m = V)
    {sigmaBarM Binf BE : ℝ} {u v h : H1Function V} {g : Vec d → Vec d}
    (hg : MemVectorL2 V g)
    (hren : ∀ L : ℤ, m ≤ L → ∀ uL : H1Function V,
      HasZeroTraceDifferenceOn V uL h →
      IsDivFormWeakSolutionOn ((Cutoff.coefficientCutoff M.nu L omega.1).toCoeffField) V uL g →
      (∀ᵐ x ∂(volume.restrict V),
          Real.rpow 3 (-(m : ℝ)) * |uL.toFun x - v.toFun x| ≤ Binf) ∧
        |volumeAverage V (fun y => M.nu * vecNormSq (uL.grad y)) -
            volumeAverage V (fun y => sigmaBarM * vecNormSq (v.grad y))| ≤ BE)
    (hzt : HasZeroTraceDifferenceOn V u h)
    (hw : IsDivFormWeakSolutionOn (streamCoefficient M.nu omega) V u g) :
    (∀ᵐ x ∂(volume.restrict V),
        Real.rpow 3 (-(m : ℝ)) * |u.toFun x - v.toFun x| ≤ Binf) ∧
      |volumeAverage V (fun y => M.nu * vecNormSq (u.grad y)) -
          volumeAverage V (fun y => sigmaBarM * vecNormSq (v.grad y))| ≤ BE := by
  subst hV
  have : NeZero d := Algsuperdiff.Section3.Provider.Orlicz.neZero_of_model M
  have hUmeas : MeasurableSet (cubeSetAt (0 : Vec d) m) := measurableSet_cubeSetAt 0 m
  have hUdom : IsOpenBoundedConvexDomain (cubeSetAt (0 : Vec d) m) :=
    isOpenBoundedConvexDomain_cubeSetAt 0 m
  have hUne : (cubeSetAt (0 : Vec d) m).Nonempty := cubeSetAt_nonempty 0 m
  -- the family of truncated solutions with the same datum and forcing
  have hex : ∀ L : ℤ, ∃ uL : H1Function (cubeSetAt (0 : Vec d) m),
      HasZeroTraceDifferenceOn (cubeSetAt (0 : Vec d) m) uL h ∧
        IsDivFormWeakSolutionOn ((Cutoff.coefficientCutoff M.nu L omega.1).toCoeffField)
          (cubeSetAt (0 : Vec d) m) uL g := by
    intro L
    obtain ⟨Lam, hEll⟩ := exists_isEllipticFieldOn_cutoff M L m 0 omega.1
    obtain ⟨w, hw'⟩ := exists_h10_isDivFormWeakSolutionOn_add hUdom hUne hEll h hg
    exact ⟨h + w.toH1Function, ⟨w, fun _ => rfl, fun _ => rfl⟩, hw'⟩
  choose uL huzt huw using hex
  have h3pos : (0 : ℝ) < Real.rpow 3 (m : ℝ) := Real.rpow_pos_of_pos (by norm_num) _
  have h3neg : (0 : ℝ) < Real.rpow 3 (-(m : ℝ)) := Real.rpow_pos_of_pos (by norm_num) _
  have hmul : Real.rpow 3 (m : ℝ) * Real.rpow 3 (-(m : ℝ)) = 1 := by
    change (3 : ℝ) ^ (m : ℝ) * (3 : ℝ) ^ (-(m : ℝ)) = 1
    rw [← Real.rpow_add (by norm_num : (0:ℝ) < 3)]
    simp
  constructor
  · -- the uniform clause
    have hbd : ∀ L : ℤ, m ≤ L → ∀ w : H1Function (cubeSetAt (0 : Vec d) m),
        HasZeroTraceDifferenceOn (cubeSetAt (0 : Vec d) m) w h →
        IsDivFormWeakSolutionOn ((Cutoff.coefficientCutoff M.nu L omega.1).toCoeffField)
          (cubeSetAt (0 : Vec d) m) w g →
        ∀ᵐ x ∂(volume.restrict (cubeSetAt (0 : Vec d) m)),
          |w.toFun x - v.toFun x| ≤ Real.rpow 3 (m : ℝ) * Binf := by
      intro L hL w hzt' hw'
      filter_upwards [(hren L hL w hzt' hw').1] with x hx
      calc |w.toFun x - v.toFun x|
          = Real.rpow 3 (m : ℝ) * (Real.rpow 3 (-(m : ℝ)) * |w.toFun x - v.toFun x|) := by
            rw [← mul_assoc, hmul, one_mul]
        _ ≤ Real.rpow 3 (m : ℝ) * Binf := mul_le_mul_of_nonneg_left hx h3pos.le
    have hres := ae_abs_sub_le_of_cutoff_bounds M omega 0 m h hg (f := v.toFun) v.memL2
      (K := Real.rpow 3 (m : ℝ) * Binf) (m₀ := m) hbd hzt hw
    filter_upwards [hres] with x hx
    calc Real.rpow 3 (-(m : ℝ)) * |u.toFun x - v.toFun x|
        ≤ Real.rpow 3 (-(m : ℝ)) * (Real.rpow 3 (m : ℝ) * Binf) :=
          mul_le_mul_of_nonneg_left hx h3neg.le
      _ = Binf := by rw [← mul_assoc, mul_comm (Real.rpow 3 (-(m : ℝ))), hmul, one_mul]
  · -- the energy clause
    have hVAeq : ∀ F : Vec d → Vec d,
        volumeAverage (cubeSetAt (0 : Vec d) m) (fun y => M.nu * vecNormSq (F y)) =
          (volume (cubeSetAt (0 : Vec d) m)).toReal⁻¹ * M.nu *
            ∫ x in cubeSetAt (0 : Vec d) m, vecNormSq (F x) ∂volume := by
      intro F
      change (volume (cubeSetAt (0 : Vec d) m)).toReal⁻¹ *
          ∫ x in cubeSetAt (0 : Vec d) m, M.nu * vecNormSq (F x) ∂volume = _
      rw [integral_const_mul]
      ring
    have hcnn : (0 : ℝ) ≤ (volume (cubeSetAt (0 : Vec d) m)).toReal⁻¹ * M.nu :=
      mul_nonneg (by positivity) M.nu_pos.le
    have hdiff : ∀ L : ℤ,
        |volumeAverage (cubeSetAt (0 : Vec d) m) (fun y => M.nu * vecNormSq ((uL L).grad y)) -
            volumeAverage (cubeSetAt (0 : Vec d) m) (fun y => M.nu * vecNormSq (u.grad y))| ≤
          (volume (cubeSetAt (0 : Vec d) m)).toReal⁻¹ * M.nu *
            ((d : ℝ) *
                (Real.sqrt (∫ x in cubeSetAt (0 : Vec d) m,
                    ‖(uL L).grad x - u.grad x‖ ^ (2 : ℕ) ∂volume) *
                  Real.sqrt (∫ x in cubeSetAt (0 : Vec d) m,
                    ‖(uL L).grad x - u.grad x‖ ^ (2 : ℕ) ∂volume)) +
              2 * ((d : ℝ) *
                (Real.sqrt (∫ x in cubeSetAt (0 : Vec d) m,
                    ‖(uL L).grad x - u.grad x‖ ^ (2 : ℕ) ∂volume) *
                  Real.sqrt (∫ x in cubeSetAt (0 : Vec d) m,
                    ‖u.grad x‖ ^ (2 : ℕ) ∂volume)))) := by
      intro L
      rw [hVAeq, hVAeq, ← mul_sub, abs_mul, abs_of_nonneg hcnn]
      exact mul_le_mul_of_nonneg_left
        (abs_integral_vecNormSq_sub_le hUmeas (uL L).grad_memVectorL2 u.grad_memVectorL2) hcnn
    have hDlim := tendsto_sqrt_energy_grad_cutoff_of_h10Diff M omega 0 m huzt huw hzt hw
    have hepslim : Tendsto (fun L : ℤ =>
        (volume (cubeSetAt (0 : Vec d) m)).toReal⁻¹ * M.nu *
          ((d : ℝ) *
              (Real.sqrt (∫ x in cubeSetAt (0 : Vec d) m,
                  ‖(uL L).grad x - u.grad x‖ ^ (2 : ℕ) ∂volume) *
                Real.sqrt (∫ x in cubeSetAt (0 : Vec d) m,
                  ‖(uL L).grad x - u.grad x‖ ^ (2 : ℕ) ∂volume)) +
            2 * ((d : ℝ) *
              (Real.sqrt (∫ x in cubeSetAt (0 : Vec d) m,
                  ‖(uL L).grad x - u.grad x‖ ^ (2 : ℕ) ∂volume) *
                Real.sqrt (∫ x in cubeSetAt (0 : Vec d) m,
                  ‖u.grad x‖ ^ (2 : ℕ) ∂volume))))) atTop (𝓝 0) := by
      have h1 := (((hDlim.mul hDlim).const_mul (d : ℝ)).add
        (((hDlim.mul_const (Real.sqrt (∫ x in cubeSetAt (0 : Vec d) m,
          ‖u.grad x‖ ^ (2 : ℕ) ∂volume))).const_mul (d : ℝ)).const_mul
            (2 : ℝ))).const_mul
              ((volume (cubeSetAt (0 : Vec d) m)).toReal⁻¹ * M.nu)
      simpa using h1
    have hVAlim : Tendsto (fun L : ℤ =>
        volumeAverage (cubeSetAt (0 : Vec d) m) (fun y => M.nu * vecNormSq ((uL L).grad y)))
        atTop (𝓝 (volumeAverage (cubeSetAt (0 : Vec d) m)
          (fun y => M.nu * vecNormSq (u.grad y)))) := by
      have hz : Tendsto (fun L : ℤ =>
          volumeAverage (cubeSetAt (0 : Vec d) m) (fun y => M.nu * vecNormSq ((uL L).grad y)) -
            volumeAverage (cubeSetAt (0 : Vec d) m) (fun y => M.nu * vecNormSq (u.grad y)))
          atTop (𝓝 0) :=
        squeeze_zero_norm (fun L => by simpa [Real.norm_eq_abs] using hdiff L) hepslim
      simpa using hz.add_const
        (volumeAverage (cubeSetAt (0 : Vec d) m) (fun y => M.nu * vecNormSq (u.grad y)))
    refine le_of_tendsto ((hVAlim.sub_const _).abs) ?_
    filter_upwards [eventually_ge_atTop m] with L hL
    exact (hren L hL (uL L) (huzt L) (huw L)).2

/-! ## 4. The transfers along the inclusion of the full-sample carrier -/

/-- An almost-sure statement about the truncation carrier is almost sure on the full-sample
carrier, whose law pushes forward to the law of the truncation carrier. -/
private theorem ae_comp_val {M : ABKModel d} {P : Cutoff.CutoffSample d → Prop}
    (hP : ∀ᵐ omega ∂(Cutoff.cutoffSampleLaw M).toMeasure, P omega) :
    ∀ᵐ omega ∂(fullSampleLaw M).toMeasure, P omega.1 := by
  rw [← map_fullSampleLaw_val M] at hP
  exact ae_of_ae_map measurable_subtype_coe.aemeasurable hP

/-- Moments of a functional of the truncation carrier are unchanged when it is read on the
full-sample carrier. -/
private theorem lintegral_comp_val (M : ABKModel d) {f : Cutoff.CutoffSample d → ℝ≥0∞}
    (hf : Measurable f) :
    ∫⁻ omega, f omega.1 ∂(fullSampleLaw M).toMeasure =
      ∫⁻ omega, f omega ∂(Cutoff.cutoffSampleLaw M).toMeasure := by
  rw [← map_fullSampleLaw_val M, lintegral_map hf measurable_subtype_coe]

/-! ## 5. The renormalization estimate for the coefficient field -/

/-- **Renormalization of the generator for the coefficient field `a = nu I + k`.**
At every scale `m` there are an effective diffusivity `sigmaBar_m`, close to
`sqrt (nu ^ 2 + cstar gamma⁻¹ 3 ^ (2 gamma m))` in the relative sense, and a
random error amplitude with Gaussian-type moments, such that on the cube `□_m`
the solution of the Dirichlet problem for the coefficient field and the
solution of the homogenized problem with the same datum and the same forcing
are close, both uniformly and in Dirichlet energy. -/
theorem generator_renormalization_provider
    (d : ℕ) (cstar : ℝ) (_hcstar : 0 < cstar) :
    ∃ gamma0 C : ℝ, 0 < gamma0 ∧ 0 < C ∧
      ∀ M : ABKModel d, Disorder.cstar M = cstar → M.gamma ≤ gamma0 →
        ∀ m : ℤ, ∃ sigmaBarM : ℝ, 0 < sigmaBarM ∧
          |sigmaBarM -
              Real.sqrt (M.nu ^ (2 : ℕ) +
                cstar * M.gamma⁻¹ * Real.rpow (3 : ℝ) (2 * M.gamma * (m : ℝ)))| ≤
            C * Real.sqrt M.gamma * |Real.log M.gamma| * sigmaBarM ∧
          ∃ EB : Algsuperdiff.Section5.Field.FullSample d M.gamma → ℝ,
            (∀ omega, 0 ≤ EB omega) ∧ Measurable EB ∧
            (∀ p : ℝ, 1 ≤ p → p ≤ C⁻¹ * M.gamma⁻¹ * |Real.log M.gamma|⁻¹ →
              (∫⁻ omega, ENNReal.ofReal (EB omega) ^ p
                  ∂(Algsuperdiff.Section5.Field.fullSampleLaw M).toMeasure) ≤
                ENNReal.ofReal
                    (C * (Real.sqrt p + Real.sqrt |Real.log M.gamma|) *
                      Real.sqrt M.gamma * |Real.log M.gamma| ^ (3 : ℕ)) ^ p) ∧
            ∀ᵐ omega ∂(Algsuperdiff.Section5.Field.fullSampleLaw M).toMeasure,
              ∀ (u v h : HCPolySupport.H1Function
                    (HCPolySupport.openCubeSet (HCPolySupport.originCube d m)))
                (g : HCPolySupport.Vec d → HCPolySupport.Vec d)
                (Kg Kh KhInf : ℝ),
                Algsuperdiff.Section4.Support.IsDirichletSolutionOn
                    (Algsuperdiff.Section5.Field.streamCoefficient M.nu omega)
                    (HCPolySupport.originCube d m) u h g →
                Algsuperdiff.Section4.Support.IsDirichletSolutionOn
                    (fun _ : HCPolySupport.Vec d => sigmaBarM • (1 : HCPolySupport.Mat d))
                    (HCPolySupport.originCube d m) v h g →
                Algsuperdiff.Section4.Support.HolderSeminormBoundOn
                    (HCPolySupport.openCubeSet (HCPolySupport.originCube d m))
                    (1 / 2) Kg g →
                Algsuperdiff.Section4.Support.HolderSeminormBoundOn
                    (HCPolySupport.openCubeSet (HCPolySupport.originCube d m))
                    (1 / 2) Kh h.grad →
                (∀ x ∈ HCPolySupport.openCubeSet (HCPolySupport.originCube d m),
                  ‖h.grad x‖ ≤ KhInf) →
                Algsuperdiff.Section4.Support.HasGradientOn
                    (HCPolySupport.openCubeSet (HCPolySupport.originCube d m))
                    h.toFun h.grad →
                (∀ᵐ x ∂(MeasureTheory.volume.restrict
                      (HCPolySupport.openCubeSet (HCPolySupport.originCube d m))),
                    Real.rpow (3 : ℝ) (-(m : ℝ)) * |u.toFun x - v.toFun x| ≤
                      EB omega *
                        (sigmaBarM⁻¹ * Real.rpow (3 : ℝ) ((m : ℝ) / 2) * Kg +
                          (KhInf + Real.rpow (3 : ℝ) ((m : ℝ) / 2) * Kh))) ∧
                  |HCPolySupport.volumeAverage
                        (HCPolySupport.openCubeSet (HCPolySupport.originCube d m))
                        (fun y => M.nu * HCPolySupport.vecNormSq (u.grad y)) -
                      HCPolySupport.volumeAverage
                        (HCPolySupport.openCubeSet (HCPolySupport.originCube d m))
                        (fun y => sigmaBarM * HCPolySupport.vecNormSq (v.grad y))| ≤
                    EB omega *
                      (Real.sqrt sigmaBarM⁻¹ * Real.rpow (3 : ℝ) ((m : ℝ) / 2) * Kg +
                          Real.sqrt sigmaBarM *
                            (KhInf + Real.rpow (3 : ℝ) ((m : ℝ) / 2) * Kh)) ^
                        (2 : ℕ)
    := by
  obtain ⟨gamma0, C, hgamma0, hC, hmain⟩ :=
    Algsuperdiff.Frozen.Section4.generator_renormalization d cstar _hcstar
  refine ⟨gamma0, C, hgamma0, hC, ?_⟩
  intro M hcs hgam m
  obtain ⟨sigmaBarM, hsigpos, hclose, EB, hEBnn, hEBmeas, hEBmom, hEBae⟩ := hmain M hcs hgam m
  have : NeZero d := Algsuperdiff.Section3.Provider.Orlicz.neZero_of_model M
  have hd0 : 0 < d := Nat.pos_of_ne_zero (NeZero.ne d)
  refine ⟨sigmaBarM, hsigpos, hclose, fun omega => EB omega.1, fun omega => hEBnn _,
    hEBmeas.comp measurable_subtype_coe, ?_, ?_⟩
  · intro p hp1 hp2
    have hmeas : Measurable fun w : Cutoff.CutoffSample d => ENNReal.ofReal (EB w) ^ p :=
      (ENNReal.measurable_ofReal.comp hEBmeas).pow_const p
    rw [lintegral_comp_val M hmeas]
    exact hEBmom p hp1 hp2
  · filter_upwards [ae_comp_val hEBae] with omega hom
    intro u v h g Kg Kh KhInf hu hv hKg hKh hKhInf hgrad
    have hKgnn : 0 ≤ Kg := holderSeminormBoundOn_nonneg_openCubeSet hd0 hKg
    have hgL2 : MemVectorL2 (openCubeSet (originCube d m)) g :=
      memVectorL2_of_holderSeminormBoundOn hKgnn (by norm_num) hKg
    refine clauses_stream_of_cutoff M omega m (openCubeSet (originCube d m))
      (cubeSetAt_zero_eq m) hgL2 ?_ hu.1 hu.2
    intro L hL uLf hztL hwL
    exact hom L hL uLf v h g Kg Kh KhInf ⟨hztL, hwL⟩ hv hKg hKh hKhInf hgrad

end

end Algsuperdiff.Section4.Provider.Introduction
