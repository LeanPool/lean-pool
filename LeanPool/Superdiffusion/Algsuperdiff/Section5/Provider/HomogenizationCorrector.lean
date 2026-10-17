/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Frozen.Section4.GeneratorRenormalization
public import LeanPool.Superdiffusion.Algsuperdiff.Section5.Provider.CutoffLimitDatum
public import LeanPool.Superdiffusion.Algsuperdiff.Section5.Provider.StoppedMomentsDatum
public import LeanPool.Superdiffusion.Algsuperdiff.Section5.Support.IntrinsicScale
public import LeanPool.Superdiffusion.Algsuperdiff.Section5.Support.RenormalizationFamilyCorrector

/-!
# HomogenizationCorrector

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# The corrector estimates of the displacement bounds at the stream field

The renormalization of the generator compares, at every truncation scale `L` above the cube
scale `m`, the Dirichlet solutions of the truncated coefficient field `a_L` on the origin cube
`□_m` with the solutions of the homogenized problem, almost everywhere on the cube.  The two
readings of that estimate at the linear datum `e ⬝ x` and at the quadratic datum `(e ⬝ x)²` are
stated in `StoppedMomentsDatum.lean`; this file carries them from the truncated fields to the
full stream field `a = ν I + k`, on the triadic cube centred at the origin.

Two ingredients are combined.  The renormalization families are assembled from the frozen
renormalization theorem with the corrector clause retained, so that the error random variable
whose moments are controlled is the same one the corrector clause is stated for.  And a bound
holding for every truncated solution uniformly in `L` passes to the full-field solution by the
`L²` convergence of the truncated solutions.

## Main results

* `exists_renormalizationFamily_corrector` — the renormalization families over the scales,
  with the corrector clause of the frozen theorem retained for the same error family.
* `affineH1`, `quadraticH1` — the two data as `H¹` functions of a triadic cube.
* `isDirichletSolutionOn_castH1_of_cubeSetAt_zero` — the Dirichlet problem on the cube centred
  at the origin, read on the origin cube.
* `ae_abs_sub_affineObservable_le_stream`, `ae_abs_sub_quadraticObservable_le_stream` — the two
  corrector estimates at the stream field, almost everywhere on the cube.

## References

* ABK26, Theorem B and Steps 1 and 3 of the superdiffusive displacement bounds of Section 5.4.
-/

namespace Algsuperdiff.Section5.Provider

open HCPolySupport MeasureTheory
open Algsuperdiff.Section3
open Algsuperdiff.Section4.Support Algsuperdiff.Section4.Provider.Holder
open Algsuperdiff.Section5.Field Algsuperdiff.Section5.Support
open scoped ENNReal

noncomputable section

variable {d : ℕ}

/-! ## 1. The renormalization families with the corrector clause retained -/

/-- **The renormalization families over the scales, with the corrector clause.**  For each
scale the frozen renormalization theorem supplies an effective diffusivity and an error random
variable; choice over the integers assembles them into two families.  The corrector clause of the
theorem is retained for that same error family, so that the estimate the displacement bounds
consume and the moments of the error are statements about one and the same random variable. -/
theorem exists_renormalizationFamily_corrector (d : ℕ) (cstar : ℝ) (hcstar : 0 < cstar) :
    ∃ gamma0 C : ℝ, 0 < gamma0 ∧ 0 < C ∧
      ∀ M : ABKModel d, Disorder.cstar M = cstar → M.gamma ≤ gamma0 →
        ∃ (sigmaBar : ℤ → ℝ) (EB : ℤ → Cutoff.CutoffSample d → ℝ),
          (∀ m : ℤ, 0 < sigmaBar m) ∧
          (∀ m : ℤ, |sigmaBar m -
              effectiveDiffusivity M.nu cstar M.gamma ((3 : ℝ) ^ m)| ≤
            C * Real.sqrt M.gamma * |Real.log M.gamma| * sigmaBar m) ∧
          (∀ m : ℤ, ∀ omega, 0 ≤ EB m omega) ∧
          (∀ m : ℤ, Measurable (EB m)) ∧
          (∀ m : ℤ, ∀ p : ℝ, 1 ≤ p → p ≤ C⁻¹ * M.gamma⁻¹ * |Real.log M.gamma|⁻¹ →
            (∫⁻ omega, ENNReal.ofReal (EB m omega) ^ p
                ∂(Cutoff.cutoffSampleLaw M).toMeasure) ≤
              ENNReal.ofReal (C * (Real.sqrt p + Real.sqrt |Real.log M.gamma|) *
                Real.sqrt M.gamma * |Real.log M.gamma| ^ (3 : ℕ)) ^ p) ∧
          ∀ m : ℤ, ∀ᵐ omega ∂(Cutoff.cutoffSampleLaw M).toMeasure,
            ∀ L : ℤ, m ≤ L →
              ∀ (u v h : H1Function (openCubeSet (originCube d m)))
                (g : Vec d → Vec d) (Kg Kh KhInf : ℝ),
                IsDirichletSolutionOn
                    (Cutoff.coefficientCutoff M.nu L omega).toCoeffField
                    (originCube d m) u h g →
                IsDirichletSolutionOn
                    (fun _ : Vec d => sigmaBar m • (1 : Mat d))
                    (originCube d m) v h g →
                HolderSeminormBoundOn (openCubeSet (originCube d m))
                    (1 / 2) Kg g →
                HolderSeminormBoundOn (openCubeSet (originCube d m))
                    (1 / 2) Kh h.grad →
                (∀ x ∈ openCubeSet (originCube d m), ‖h.grad x‖ ≤ KhInf) →
                HasGradientOn (openCubeSet (originCube d m)) h.toFun h.grad →
                ∀ᵐ x ∂(volume.restrict (openCubeSet (originCube d m))),
                    Real.rpow 3 (-(m : ℝ)) * |u.toFun x - v.toFun x| ≤
                      EB m omega *
                        ((sigmaBar m)⁻¹ * Real.rpow 3 ((m : ℝ) / 2) * Kg +
                          (KhInf + Real.rpow 3 ((m : ℝ) / 2) * Kh)) :=
  Algsuperdiff.Section5.Support.exists_renormalizationFamily_corrector d cstar hcstar

/-! ## 2. The two data as `H¹` functions of a triadic cube -/

/-- The linear observable is smooth. -/
theorem contDiff_affineObservable (n : WithTop ℕ∞) (e : Vec d) :
    ContDiff ℝ n (affineObservable e) := by
  have hshape : affineObservable e = fun x : Vec d ↦ (slopeCLM e) x := by
    funext x
    simp only [slopeCLM_apply, affineObservable]
  rw [hshape]
  exact (slopeCLM e).contDiff

/-- The quadratic observable is smooth. -/
theorem contDiff_quadraticObservable (n : WithTop ℕ∞) (e : Vec d) :
    ContDiff ℝ n (quadraticObservable e) := by
  have hshape : quadraticObservable e =
      fun x : Vec d ↦ (slopeCLM e) x * (slopeCLM e) x := by
    funext x
    simp only [slopeCLM_apply, quadraticObservable]
  rw [hshape]
  exact (slopeCLM e).contDiff.mul (slopeCLM e).contDiff

/-- The linear observable is continuous. -/
theorem continuous_affineObservable (e : Vec d) : Continuous (affineObservable e) :=
  (contDiff_affineObservable 1 e).continuous

/-- The quadratic observable is continuous. -/
theorem continuous_quadraticObservable (e : Vec d) : Continuous (quadraticObservable e) :=
  (contDiff_quadraticObservable 1 e).continuous

/-- The linear datum `e ⬝ x` as an `H¹` function of the cube `y + □_n`. -/
def affineH1 (y : Vec d) (n : ℤ) (e : Vec d) : H1Function (cubeSetAt y n) :=
  H1Function.ofContDiffOnIsOpenBoundedConvexDomain (isOpenBoundedConvexDomain_cubeSetAt y n)
    (contDiff_affineObservable 1 e)

/-- The quadratic datum `(e ⬝ x)²` as an `H¹` function of the cube `y + □_n`. -/
def quadraticH1 (y : Vec d) (n : ℤ) (e : Vec d) : H1Function (cubeSetAt y n) :=
  H1Function.ofContDiffOnIsOpenBoundedConvexDomain (isOpenBoundedConvexDomain_cubeSetAt y n)
    (contDiff_quadraticObservable 1 e)

theorem affineH1_grad (y : Vec d) (n : ℤ) (e : Vec d) :
    (affineH1 y n e).grad = affineGradient e := by
  funext x i
  change (fderiv ℝ (affineObservable e) x) (basisVec i) = affineGradient e x i
  have hder : HasFDerivAt (affineObservable e) (slopeCLM (affineGradient e x)) x :=
    hasFDerivWithinAt_univ.1 (hasGradientOn_affineObservable Set.univ e x (Set.mem_univ x))
  rw [hder.fderiv, slopeCLM_apply, vecDot_basisVec_right]

theorem quadraticH1_grad (y : Vec d) (n : ℤ) (e : Vec d) :
    (quadraticH1 y n e).grad = quadraticGradient e := by
  funext x i
  change (fderiv ℝ (quadraticObservable e) x) (basisVec i) = quadraticGradient e x i
  have hder : HasFDerivAt (quadraticObservable e) (slopeCLM (quadraticGradient e x)) x :=
    hasFDerivWithinAt_univ.1 (hasGradientOn_quadraticObservable Set.univ e x (Set.mem_univ x))
  rw [hder.fderiv, slopeCLM_apply, vecDot_basisVec_right]

/-! ## 3. The cube centred at the origin, read on the origin cube -/

/-- **The Dirichlet problem on the cube centred at the origin is the Dirichlet problem on the
origin cube.**  The two sets are equal, and the `H¹` functions are transported along that
equality with their values and gradients unchanged. -/
theorem isDirichletSolutionOn_castH1_of_cubeSetAt_zero {m : ℤ} {a : CoeffField d}
    {u h : H1Function (cubeSetAt (0 : Vec d) m)} {g : Vec d → Vec d}
    (hzt : HasZeroTraceDifferenceOn (cubeSetAt (0 : Vec d) m) u h)
    (hw : IsDivFormWeakSolutionOn a (cubeSetAt (0 : Vec d) m) u g) :
    IsDirichletSolutionOn a (originCube d m) (castH1 (cubeSetAt_zero_eq m) u)
      (castH1 (cubeSetAt_zero_eq m) h) g := by
  have key : ∀ (V : Set (Vec d)) (hV : V = openCubeSet (originCube d m)) (u h : H1Function V),
      HasZeroTraceDifferenceOn V u h → IsDivFormWeakSolutionOn a V u g →
      IsDirichletSolutionOn a (originCube d m) (castH1 hV u) (castH1 hV h) g := by
    intro V hV
    subst hV
    intro u h h1 h2
    exact ⟨h1, h2⟩
  exact key _ (cubeSetAt_zero_eq m) u h hzt hw

/-! ## 4. The corrector estimates at the stream field -/

/-- **The corrector estimate at the linear datum, for the stream field.**  On the triadic cube
centred at the origin, a weak solution of the homogeneous equation for the stream coefficient
with the trace of the linear datum `e ⬝ x` is almost everywhere within `3^m EB ‖e‖` of that
datum, provided the corrector clause of the renormalization theorem holds at the sample for the
scale `m` with the error value `EB` and the effective diffusivity `sigmaBarM`. -/
theorem ae_abs_sub_affineObservable_le_stream (M : ABKModel d) (omega : FullSample d M.gamma)
    (m : ℤ) {sigmaBarM EBm : ℝ}
    (hren : ∀ L : ℤ, m ≤ L →
      ∀ (u v h : H1Function (openCubeSet (originCube d m))) (g : Vec d → Vec d)
        (Kg Kh KhInf : ℝ),
        IsDirichletSolutionOn (Cutoff.coefficientCutoff M.nu L omega.1).toCoeffField
          (originCube d m) u h g →
        IsDirichletSolutionOn (fun _ : Vec d => sigmaBarM • (1 : Mat d)) (originCube d m) v h g →
        HolderSeminormBoundOn (openCubeSet (originCube d m)) (1 / 2) Kg g →
        HolderSeminormBoundOn (openCubeSet (originCube d m)) (1 / 2) Kh h.grad →
        (∀ x ∈ openCubeSet (originCube d m), ‖h.grad x‖ ≤ KhInf) →
        HasGradientOn (openCubeSet (originCube d m)) h.toFun h.grad →
        ∀ᵐ x ∂(volume.restrict (openCubeSet (originCube d m))),
          Real.rpow 3 (-(m : ℝ)) * |u.toFun x - v.toFun x| ≤
            EBm * (sigmaBarM⁻¹ * Real.rpow 3 ((m : ℝ) / 2) * Kg +
              (KhInf + Real.rpow 3 ((m : ℝ) / 2) * Kh)))
    (e : Vec d) {u : H1Function (cubeSetAt (0 : Vec d) m)}
    (hzt : HasZeroTraceDifferenceOn (cubeSetAt (0 : Vec d) m) u (affineH1 0 m e))
    (hw : IsDivFormWeakSolutionOn (streamCoefficient M.nu omega) (cubeSetAt (0 : Vec d) m) u
      fun _ => (0 : Vec d)) :
    ∀ᵐ x ∂(volume.restrict (cubeSetAt (0 : Vec d) m)),
      |u.toFun x - affineObservable e x| ≤ (3 : ℝ) ^ m * (EBm * ‖e‖) := by
  refine ae_abs_sub_le_of_cutoff_bounds M omega 0 m (affineH1 0 m e) (g := fun _ => (0 : Vec d))
    MemLp.zero (f := affineObservable e) (affineH1 0 m e).memL2 (m₀ := m) ?_ hzt hw
  intro L hL uL hztL hwL
  have hcast := isDirichletSolutionOn_castH1_of_cubeSetAt_zero hztL hwL
  have hae := ae_abs_sub_affineObservable_le (hren L hL) (e := e)
    (u := castH1 (cubeSetAt_zero_eq m) uL) (h := castH1 (cubeSetAt_zero_eq m) (affineH1 0 m e))
    (fun x => by rw [castH1_toFun]; rfl)
    (fun x => by rw [castH1_grad, affineH1_grad]) hcast
  simp only [castH1_toFun] at hae
  rw [← cubeSetAt_zero_eq m] at hae
  exact hae

/-- **The corrector estimate at the quadratic datum, for the stream field.**  On the triadic
cube centred at the origin, a weak solution of `-∇ · a ∇u = ∇ · g` for the stream coefficient,
with the forcing `g = -2 sigmaBarM (e ⬝ x) e` and the trace of the quadratic datum `(e ⬝ x)²`, is
almost everywhere within `5 (3^m)² EB ‖e‖ (∑ |e_i|)` of that datum, under the corrector clause of
the renormalization theorem at the sample for the scale `m`. -/
theorem ae_abs_sub_quadraticObservable_le_stream (M : ABKModel d)
    (omega : FullSample d M.gamma) (m : ℤ) {sigmaBarM EBm : ℝ} (hsigma : 0 < sigmaBarM)
    (hren : ∀ L : ℤ, m ≤ L →
      ∀ (u v h : H1Function (openCubeSet (originCube d m))) (g : Vec d → Vec d)
        (Kg Kh KhInf : ℝ),
        IsDirichletSolutionOn (Cutoff.coefficientCutoff M.nu L omega.1).toCoeffField
          (originCube d m) u h g →
        IsDirichletSolutionOn (fun _ : Vec d => sigmaBarM • (1 : Mat d)) (originCube d m) v h g →
        HolderSeminormBoundOn (openCubeSet (originCube d m)) (1 / 2) Kg g →
        HolderSeminormBoundOn (openCubeSet (originCube d m)) (1 / 2) Kh h.grad →
        (∀ x ∈ openCubeSet (originCube d m), ‖h.grad x‖ ≤ KhInf) →
        HasGradientOn (openCubeSet (originCube d m)) h.toFun h.grad →
        ∀ᵐ x ∂(volume.restrict (openCubeSet (originCube d m))),
          Real.rpow 3 (-(m : ℝ)) * |u.toFun x - v.toFun x| ≤
            EBm * (sigmaBarM⁻¹ * Real.rpow 3 ((m : ℝ) / 2) * Kg +
              (KhInf + Real.rpow 3 ((m : ℝ) / 2) * Kh)))
    (e : Vec d) {u : H1Function (cubeSetAt (0 : Vec d) m)}
    (hzt : HasZeroTraceDifferenceOn (cubeSetAt (0 : Vec d) m) u (quadraticH1 0 m e))
    (hw : IsDivFormWeakSolutionOn (streamCoefficient M.nu omega) (cubeSetAt (0 : Vec d) m) u
      (quadraticForcing sigmaBarM e)) :
    ∀ᵐ x ∂(volume.restrict (cubeSetAt (0 : Vec d) m)),
      |u.toFun x - quadraticObservable e x| ≤
        ((3 : ℝ) ^ m) ^ (2 : ℕ) * (5 * EBm * (‖e‖ * vecCoordSum e)) := by
  have hgL2 : MemVectorL2 (cubeSetAt (0 : Vec d) m) (quadraticForcing sigmaBarM e) := by
    have hcont : Continuous (quadraticForcing sigmaBarM e) := by
      refine continuous_pi fun i => ?_
      change Continuous fun x : Vec d => (-(2 * sigmaBarM) * vecDot e x) * e i
      exact ((continuous_const.mul (continuous_affineObservable e)).mul continuous_const)
    have hbd := isOpenBoundedConvexDomain_cubeSetAt (0 : Vec d) m
    refine MemLp.of_eval fun i => ?_
    exact memScalarL2_of_continuous_of_isBoundedDomain (measurableSet_cubeSetAt 0 m)
      hbd.isBoundedDomain ((continuous_apply i).comp hcont)
  refine ae_abs_sub_le_of_cutoff_bounds M omega 0 m (quadraticH1 0 m e) hgL2
    (f := quadraticObservable e) (quadraticH1 0 m e).memL2 (m₀ := m) ?_ hzt hw
  intro L hL uL hztL hwL
  have hcast := isDirichletSolutionOn_castH1_of_cubeSetAt_zero hztL hwL
  have hae := ae_abs_sub_quadraticObservable_le hsigma (hren L hL) (e := e)
    (u := castH1 (cubeSetAt_zero_eq m) uL)
    (h := castH1 (cubeSetAt_zero_eq m) (quadraticH1 0 m e))
    (fun x => by rw [castH1_toFun]; rfl)
    (fun x => by rw [castH1_grad, quadraticH1_grad]) hcast
  simp only [castH1_toFun] at hae
  rw [← cubeSetAt_zero_eq m] at hae
  exact hae

end

end Algsuperdiff.Section5.Provider
