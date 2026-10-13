/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section5.Field.CutoffLimit
public import LeanPool.Superdiffusion.Algsuperdiff.Section5.Support.EnergyPoincare
public import LeanPool.Superdiffusion.Algsuperdiff.StochasticProcess.Common.Regularity.Freezing.ContinuousCoeffResolvent

/-!
# CutoffFieldLimit

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# The Dirichlet solutions of the cutoff fields converge to those of the full field

Three steps, on the cube `y + □_n`.

*The shift is invisible.*  The cutoff coefficient `a_L` and its origin
normalization `ã_L = a_L - k_L(0)` differ by a constant skew matrix, so they have
exactly the same divergence-form weak solutions
(`isDirichletSolutionAt_normalizedCoefficientCutoff_iff`).  This is the printed
step "the equation is unchanged if we replace `a_L` by `a_L - (k_L - k_m)`".

*The coefficient distance is geometric.*  On the cube the entrywise distance
between `ã_L` and the full field `a = ν I + k` is at most
`Field.cutoffLimitGap`, which vanishes geometrically in `L`.

*The solution map is Lipschitz in the coefficient.*  The energy estimate
`sqrt_energy_grad_sub_le` gives

```text
  ‖∇u_L - ∇u‖_{L²(y+□_n)} ≤ ν⁻¹ d² ‖ã_L - a‖_{L^∞(y+□_n)} ‖∇u‖_{L²(y+□_n)} ,
```

and the zero-trace Poincaré inequality upgrades it to the `L²` distance of the
values.  Both solutions carry the *same* forcing field `g`; `ν` is the symmetric
part of both coefficient fields.

## Main results

* `exists_isEllipticFieldOn_normalizedCoefficientCutoff`,
  `exists_isEllipticFieldOn_streamCoefficient` — ellipticity on the cube with
  lower constant `ν` for both families.
* `isDirichletSolutionAt_normalizedCoefficientCutoff_iff` — the constant skew
  shift does not change the Dirichlet problem.
* `sqrt_energy_grad_sub_normalizedCutoff_le` — the energy estimate with the
  explicit geometric coefficient distance.
* `exists_poincare_sub_of_isDirichletSolutionAt` — the `L²` distance of two
  solutions with the same forcing, from the distance of their gradients.
* `exists_l2_bound_cutoff_stream`,
  `tendsto_sqrt_integral_sq_sub_cutoff_atTop_zero` — the `L²` convergence
  `u_L → u`.

## References

* ABK26, the localized Dirichlet problems of Section 5.1, and the proof of the
  homogenization theorem, where the uniform-in-`L` estimates for `a_L` are
  passed to `a` by letting `L → ∞`.
-/

namespace Algsuperdiff.Section5.Support

open Algsuperdiff.Section3
open Algsuperdiff.StochasticProcess.Common.Regularity.Freezing
open HCPolySupport MeasureTheory
open Algsuperdiff.Section4.Support
open Filter
open scoped Topology

noncomputable section

variable {d : ℕ}

/-! ## 1. Ellipticity of the two coefficient families on the cube -/

/-- The normalized cutoff field is elliptic on `y + □_n`, with lower constant the
molecular diffusivity: its symmetric part is `ν I` and its skew part is
continuous, so compactness of the closed cube supplies the upper constant. -/
theorem exists_isEllipticFieldOn_normalizedCoefficientCutoff {nu : ℝ} (hnu : 0 < nu)
    (L : ℤ) (omega : Cutoff.CutoffSample d) (y : Vec d) (n : ℤ) :
    ∃ Lam : ℝ, IsEllipticFieldOn nu Lam (cubeSetAt y n)
      (Field.normalizedCoefficientCutoff nu L omega) :=
  ⟨_, isEllipticFieldOn_domainEllipticUpper (isOpenBoundedConvexDomain_cubeSetAt y n)
    hnu (Field.symmPart_normalizedCoefficientCutoff nu L omega)
    (Field.continuous_normalizedCoefficientCutoff_sub nu L omega).continuousOn⟩

/-- The full stream coefficient is elliptic on `y + □_n`, with the same lower
constant. -/
theorem exists_isEllipticFieldOn_streamCoefficient {nu gamma : ℝ} (hnu : 0 < nu)
    (omega : Field.FullSample d gamma) (y : Vec d) (n : ℤ) :
    ∃ Lam : ℝ, IsEllipticFieldOn nu Lam (cubeSetAt y n)
      (Field.streamCoefficient nu omega) := by
  have hcont : Continuous fun x : Vec d =>
      Field.streamCoefficient nu omega x - nu • (1 : Mat d) := by
    rw [show (fun x : Vec d => Field.streamCoefficient nu omega x - nu • (1 : Mat d)) =
        Field.streamField omega by
      funext x
      ext i j
      simp only [Field.streamCoefficient, Matrix.sub_apply, Matrix.add_apply]
      ring]
    exact Field.continuous_streamField omega
  exact ⟨_, isEllipticFieldOn_domainEllipticUpper (isOpenBoundedConvexDomain_cubeSetAt y n)
    hnu (Field.symmPart_streamCoefficient nu omega) hcont.continuousOn⟩

/-! ## 2. The constant skew shift does not change the Dirichlet problem -/

/-- The weak equation of the cutoff field and of its origin normalization are the
same equation. -/
theorem isDivFormWeakSolutionOn_normalizedCoefficientCutoff_iff (nu : ℝ) (L : ℤ)
    (omega : Cutoff.CutoffSample d) {U : Set (Vec d)} {u : H1Function U}
    {g : Vec d → Vec d} :
    IsDivFormWeakSolutionOn (Field.normalizedCoefficientCutoff nu L omega) U u g ↔
      IsDivFormWeakSolutionOn ((Cutoff.coefficientCutoff nu L omega).toCoeffField) U u g :=
  Section4.Provider.ExcessDecay.isDivFormWeakSolutionOn_sub_const_of_skew_iff
    (Field.cutoff_zero_skew L omega)

/-- **The constant skew shift is invisible to the Dirichlet problem.**  This is
the printed remark that the equation for `a_L` is unchanged when `a_L` is
replaced by `a_L` minus a constant skew matrix. -/
theorem isDirichletSolutionAt_normalizedCoefficientCutoff_iff (nu : ℝ) (L : ℤ)
    (omega : Cutoff.CutoffSample d) {y : Vec d} {n : ℤ}
    {u : H1Function (cubeSetAt y n)} {g : Vec d → Vec d} :
    IsDirichletSolutionAt (Field.normalizedCoefficientCutoff nu L omega) y n u g ↔
      IsDirichletSolutionAt ((Cutoff.coefficientCutoff nu L omega).toCoeffField) y n u g :=
  and_congr Iff.rfl (isDivFormWeakSolutionOn_normalizedCoefficientCutoff_iff nu L omega)

/-! ## 3. The energy estimate with the explicit geometric distance -/

/-- **Continuity of the solution map in the coefficient, along the cutoff
family.**  For the same forcing field `g`, the gradient of the cutoff solution
`u_L` differs from that of the full-field solution `u` by at most
`ν⁻¹ d² · gap(L) · ‖∇u‖_{L²}`, with `gap(L) = Field.cutoffLimitGap` the explicit
geometric coefficient distance. -/
theorem sqrt_energy_grad_sub_normalizedCutoff_le {nu gamma : ℝ} (hnu : 0 < nu)
    (hgamma : gamma < 1) {C : ℕ} {omega : Field.FullSample d gamma}
    (hC : Field.SharpTailBounded gamma C omega.1) {y : Vec d} {n ell L : ℤ}
    (hcube : cubeSetAt y n ⊆ openCubeSet (originCube d ell))
    {u v : H1Function (cubeSetAt y n)} {g : Vec d → Vec d}
    (hu : IsDirichletSolutionAt ((Cutoff.coefficientCutoff nu L omega.1).toCoeffField)
      y n u g)
    (hv : IsDirichletSolutionAt (Field.streamCoefficient nu omega) y n v g) :
    Real.sqrt (∫ x in cubeSetAt y n, ‖u.grad x - v.grad x‖ ^ (2 : ℕ) ∂volume) ≤
      nu⁻¹ * ((d : ℝ) * (d : ℝ) * Field.cutoffLimitGap d gamma C ell L) *
        Real.sqrt (∫ x in cubeSetAt y n, ‖v.grad x‖ ^ (2 : ℕ) ∂volume) := by
  obtain ⟨Lam, hEll⟩ :=
    exists_isEllipticFieldOn_normalizedCoefficientCutoff hnu L omega.1 y n
  obtain ⟨Lam', hEll'⟩ := exists_isEllipticFieldOn_streamCoefficient hnu omega y n
  have hab : ∀ x ∈ cubeSetAt y n, ∀ i j,
      |Field.normalizedCoefficientCutoff nu L omega.1 x i j -
        Field.streamCoefficient nu omega x i j| ≤
      Field.cutoffLimitGap d gamma C ell L := by
    intro x hx i j
    rw [abs_sub_comm]
    exact Field.abs_streamCoefficient_sub_normalizedCoefficientCutoff_le_gap nu hgamma
      omega hC ell L (hcube hx) i j
  have hbv : MemVectorL2 (cubeSetAt y n)
      fun x => matVecMul (Field.streamCoefficient nu omega x) (v.grad x) :=
    memVectorL2_matVecMul_of_isEllipticFieldOn hEll' v.grad_memVectorL2
  exact sqrt_energy_grad_sub_le (Field.cutoffLimitGap_nonneg d gamma C ell L) hEll hab
    hbv ((isDirichletSolutionAt_normalizedCoefficientCutoff_iff nu L omega.1).2 hu) hv

/-! ## 4. From the gradients to the values -/

private theorem h10FunctionSubToH1Function {U : Set (Vec d)} (v w : H10Function U) :
    (v - w).toH1Function = v.toH1Function - w.toH1Function := rfl

/-- Two solutions of Dirichlet problems with the same forcing field differ by a
zero-trace function. -/
theorem exists_h10Function_sub_of_isDirichletSolutionAt {a b : CoeffField d}
    {y : Vec d} {n : ℤ} {u v : H1Function (cubeSetAt y n)} {g : Vec d → Vec d}
    (hu : IsDirichletSolutionAt a y n u g) (hv : IsDirichletSolutionAt b y n v g) :
    ∃ w : H10Function (cubeSetAt y n),
      (∀ x, w.toH1Function.toFun x = u.toFun x - v.toFun x) ∧
        (∀ x, w.toH1Function.grad x = u.grad x - v.grad x) := by
  obtain ⟨w1, h1f, h1g⟩ := hu.1
  obtain ⟨w2, h2f, h2g⟩ := hv.1
  refine ⟨w1 - w2, fun x => ?_, fun x => ?_⟩
  · rw [h1f x, h2f x, h10FunctionSubToH1Function]
    simp only [H1Function.sub_toFun]
  · rw [h1g x, h2g x, h10FunctionSubToH1Function]
    simp only [H1Function.sub_grad]

/-- **The `L²` distance of two solutions with the same forcing field is
controlled by the `L²` distance of their gradients**, through the zero-trace
Poincaré inequality on the cube.  The constant depends only on the cube. -/
theorem exists_poincare_sub_of_isDirichletSolutionAt [NeZero d] (y : Vec d) (n : ℤ) :
    ∃ CP : ℝ, 0 ≤ CP ∧ ∀ (a b : CoeffField d) (u v : H1Function (cubeSetAt y n))
      (g : Vec d → Vec d), IsDirichletSolutionAt a y n u g →
      IsDirichletSolutionAt b y n v g →
      Real.sqrt (∫ x in cubeSetAt y n, (u.toFun x - v.toFun x) ^ (2 : ℕ) ∂volume) ≤
        CP * Real.sqrt (∫ x in cubeSetAt y n, ‖u.grad x - v.grad x‖ ^ (2 : ℕ) ∂volume) := by
  obtain ⟨CP, hCP, hbound⟩ :=
    exists_poincare_integral_constant (isOpenBoundedConvexDomain_cubeSetAt y n)
  refine ⟨CP, hCP, fun a b u v g hu hv => ?_⟩
  obtain ⟨w, hwf, hwg⟩ := exists_h10Function_sub_of_isDirichletSolutionAt hu hv
  have hval : (∫ x in cubeSetAt y n, (u.toFun x - v.toFun x) ^ (2 : ℕ) ∂volume) =
      ∫ x in cubeSetAt y n, w.toH1Function.toFun x ^ (2 : ℕ) ∂volume := by
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    show (u.toFun x - v.toFun x) ^ (2 : ℕ) = w.toH1Function.toFun x ^ (2 : ℕ)
    rw [hwf x]
  have hgrad : (∫ x in cubeSetAt y n, ‖u.grad x - v.grad x‖ ^ (2 : ℕ) ∂volume) =
      ∫ x in cubeSetAt y n, ‖w.toH1Function.grad x‖ ^ (2 : ℕ) ∂volume := by
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    show ‖u.grad x - v.grad x‖ ^ (2 : ℕ) = ‖w.toH1Function.grad x‖ ^ (2 : ℕ)
    rw [hwg x]
  rw [hval, hgrad]
  exact hbound w

/-! ## 5. `L²` convergence of the cutoff solutions -/

/-- **The `L²` bound on the distance between the cutoff solution and the
full-field solution**, uniform in `L` up to the explicit geometric factor. -/
theorem exists_l2_bound_cutoff_stream [NeZero d] {nu gamma : ℝ} (hnu : 0 < nu)
    (hgamma : gamma < 1) {C : ℕ} {omega : Field.FullSample d gamma}
    (hC : Field.SharpTailBounded gamma C omega.1) (y : Vec d) {n ell : ℤ}
    (hcube : cubeSetAt y n ⊆ openCubeSet (originCube d ell)) :
    ∃ CP : ℝ, 0 ≤ CP ∧ ∀ (L : ℤ) (u v : H1Function (cubeSetAt y n)) (g : Vec d → Vec d),
      IsDirichletSolutionAt ((Cutoff.coefficientCutoff nu L omega.1).toCoeffField) y n u g →
      IsDirichletSolutionAt (Field.streamCoefficient nu omega) y n v g →
      Real.sqrt (∫ x in cubeSetAt y n, (u.toFun x - v.toFun x) ^ (2 : ℕ) ∂volume) ≤
        CP * (nu⁻¹ * ((d : ℝ) * (d : ℝ) * Field.cutoffLimitGap d gamma C ell L) *
          Real.sqrt (∫ x in cubeSetAt y n, ‖v.grad x‖ ^ (2 : ℕ) ∂volume)) := by
  obtain ⟨CP, hCP, hpoin⟩ := exists_poincare_sub_of_isDirichletSolutionAt (d := d) y n
  refine ⟨CP, hCP, fun L u v g hu hv => ?_⟩
  refine (hpoin _ _ u v g hu hv).trans ?_
  exact mul_le_mul_of_nonneg_left
    (sqrt_energy_grad_sub_normalizedCutoff_le hnu hgamma hC hcube hu hv) hCP

/-- **`u_L → u` in `L²(y + □_n)`.**  The forcing field is the same at every
scale; only the coefficient field moves. -/
theorem tendsto_sqrt_integral_sq_sub_cutoff_atTop_zero [NeZero d] {nu gamma : ℝ}
    (hnu : 0 < nu) (hgamma : gamma < 1) {C : ℕ} {omega : Field.FullSample d gamma}
    (hC : Field.SharpTailBounded gamma C omega.1) {y : Vec d} {n ell : ℤ}
    (hcube : cubeSetAt y n ⊆ openCubeSet (originCube d ell))
    {u : ℤ → H1Function (cubeSetAt y n)} {v : H1Function (cubeSetAt y n)}
    {g : Vec d → Vec d}
    (hu : ∀ L : ℤ,
      IsDirichletSolutionAt ((Cutoff.coefficientCutoff nu L omega.1).toCoeffField) y n (u L) g)
    (hv : IsDirichletSolutionAt (Field.streamCoefficient nu omega) y n v g) :
    Tendsto (fun L : ℤ =>
        Real.sqrt (∫ x in cubeSetAt y n, ((u L).toFun x - v.toFun x) ^ (2 : ℕ) ∂volume))
      atTop (𝓝 0) := by
  obtain ⟨CP, hCP, hbound⟩ := exists_l2_bound_cutoff_stream hnu hgamma hC y hcube
  set E : ℝ := Real.sqrt (∫ x in cubeSetAt y n, ‖v.grad x‖ ^ (2 : ℕ) ∂volume) with hE_def
  have hEnn : 0 ≤ E := Real.sqrt_nonneg _
  have hlim : Tendsto (fun L : ℤ =>
      CP * (nu⁻¹ * ((d : ℝ) * (d : ℝ) * Field.cutoffLimitGap d gamma C ell L) * E))
      atTop (𝓝 0) := by
    have hgap := Field.tendsto_cutoffLimitGap_atTop d hgamma C ell
    have h1 : Tendsto (fun L : ℤ =>
        CP * (nu⁻¹ * ((d : ℝ) * (d : ℝ) * Field.cutoffLimitGap d gamma C ell L) * E))
        atTop (𝓝 (CP * (nu⁻¹ * ((d : ℝ) * (d : ℝ) * 0) * E))) := by
      exact ((((hgap.const_mul ((d : ℝ) * (d : ℝ))).const_mul nu⁻¹).mul_const E).const_mul CP)
    simpa using h1
  refine squeeze_zero (fun L => Real.sqrt_nonneg _) (fun L => ?_) hlim
  exact hbound L (u L) v g (hu L) hv

end

end Algsuperdiff.Section5.Support
