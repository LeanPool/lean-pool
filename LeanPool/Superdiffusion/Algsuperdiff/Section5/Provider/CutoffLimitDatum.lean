/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.Holder.CubeTransport
public import LeanPool.Superdiffusion.Algsuperdiff.Section5.Provider.HomogenizationObservable
public import LeanPool.Superdiffusion.Algsuperdiff.Section5.Support.CutoffFieldLimitPointwise
public import LeanPool.Superdiffusion.Algsuperdiff.Section5.Support.DirichletSolvability

/-!
# CutoffLimitDatum

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# Uniform bounds on the truncated Dirichlet solutions with a datum pass to the full field

The renormalization estimate of the generator is stated for the Dirichlet solutions of the
truncated coefficient fields `a_L`, at every truncation scale `L` above the cube scale, while
the displacement bounds are read at the full stream field `a = ν I + k`.  This file transfers an
almost-everywhere bound, valid uniformly in `L` for the truncated solutions of a Dirichlet
problem with a prescribed `H¹` datum and a prescribed forcing, to the solution of the same
problem for the full field.

The mechanism is the one of the exit-time comparison, with the datum carried along.  Two
solutions of the same problem for two coefficient fields differ by a zero-trace function, and the
energy estimate bounds the gradient of that difference by the supremum distance of the two
coefficient fields times the energy of one solution; the zero-trace Poincaré inequality turns
this into an `L²` bound on the values; the distance between `a_L` (normalized at the origin, a
constant skew shift that does not change the equation) and `a` on a fixed cube is geometric in
`L`; and an almost-everywhere bound holding along an `L²`-convergent family passes to its
limit.

## Main results

* `sqrt_energy_grad_sub_le_of_h10Diff` — the energy estimate for two solutions of the same
  problem whose difference is a prescribed zero-trace function.
* `tendsto_l2_cutoff_of_h10Diff` — the truncated solutions converge in `L²` to the full-field
  solution, for a common datum and a common forcing.
* `ae_abs_sub_le_of_cutoff_bounds` — a uniform almost-everywhere bound on the truncated
  solutions holds for the full-field solution.

## References

* ABK26, the passage `L → ∞` from the truncated fields `a_L` to `a`, and the renormalization
  of the generator.
-/

namespace Algsuperdiff.Section5.Provider

open Filter HCPolySupport MeasureTheory Topology
open Algsuperdiff.Section3
open Algsuperdiff.Section4.Support Algsuperdiff.Section4.Provider.Holder
open Algsuperdiff.Section5.Field Algsuperdiff.Section5.Support
open scoped ENNReal

noncomputable section

variable {d : ℕ}

private theorem h10Sub_toH1Function {U : Set (Vec d)} (v w : H10Function U) :
    (v - w).toH1Function = v.toH1Function - w.toH1Function := rfl

/-! ## 1. The energy estimate for two solutions with the same datum -/

/-- **The energy estimate for two solutions of the same divergence-form problem for two
coefficient fields**, when their difference is a prescribed zero-trace function.  The gradient
of the difference is bounded by the supremum distance of the two coefficient fields, times the
energy of the second solution, divided by the lower ellipticity constant of the first field. -/
theorem sqrt_energy_grad_sub_le_of_h10Diff {y : Vec d} {n : ℤ} {a b : CoeffField d}
    {lam Lam delta : ℝ} (hdelta : 0 ≤ delta)
    (hEll : IsEllipticFieldOn lam Lam (cubeSetAt y n) a)
    (hab : ∀ x ∈ cubeSetAt y n, ∀ i j, |a x i j - b x i j| ≤ delta)
    {u v : H1Function (cubeSetAt y n)} {g : Vec d → Vec d}
    (hbv : MemVectorL2 (cubeSetAt y n) fun x => matVecMul (b x) (v.grad x))
    (w : H10Function (cubeSetAt y n)) (hwg : ∀ x, w.toH1Function.grad x = u.grad x - v.grad x)
    (hu : IsDivFormWeakSolutionOn a (cubeSetAt y n) u g)
    (hv : IsDivFormWeakSolutionOn b (cubeSetAt y n) v g) :
    Real.sqrt (∫ x in cubeSetAt y n, ‖u.grad x - v.grad x‖ ^ (2 : ℕ) ∂volume) ≤
      lam⁻¹ * ((d : ℝ) * (d : ℝ) * delta) *
        Real.sqrt (∫ x in cubeSetAt y n, ‖v.grad x‖ ^ (2 : ℕ) ∂volume) := by
  have hUmeas : MeasurableSet (cubeSetAt y n) := measurableSet_cubeSetAt y n
  have hlam : 0 < lam := (hEll.2 y (mem_cubeSetAt_self y n)).1
  have hwL2 : MemVectorL2 (cubeSetAt y n) w.toH1Function.grad :=
    w.toH1Function.grad_memVectorL2
  have hvL2 : MemVectorL2 (cubeSetAt y n) v.grad := v.grad_memVectorL2
  have hAw : MemVectorL2 (cubeSetAt y n) fun x => matVecMul (a x) (w.toH1Function.grad x) :=
    memVectorL2_matVecMul_of_isEllipticFieldOn hEll hwL2
  have hAu : MemVectorL2 (cubeSetAt y n) fun x => matVecMul (a x) (u.grad x) :=
    memVectorL2_matVecMul_of_isEllipticFieldOn hEll u.grad_memVectorL2
  have hAv : MemVectorL2 (cubeSetAt y n) fun x => matVecMul (a x) (v.grad x) :=
    memVectorL2_matVecMul_of_isEllipticFieldOn hEll hvL2
  -- the energy identity
  have hsplitW : ∀ x, matVecMul (a x) (w.toH1Function.grad x) =
      matVecMul (a x) (u.grad x) - matVecMul (a x) (v.grad x) := by
    intro x
    rw [hwg x, sub_eq_add_neg, matVecMul_add, matVecMul_neg, ← sub_eq_add_neg]
  have hsplitP : ∀ x, matVecMul (a x - b x) (v.grad x) =
      matVecMul (a x) (v.grad x) - matVecMul (b x) (v.grad x) := by
    intro x
    funext i
    simp only [matVecMul, Pi.sub_apply, Matrix.sub_apply, sub_mul, Finset.sum_sub_distrib]
  have hkey : ∫ x in cubeSetAt y n,
      vecDot (matVecMul (a x) (w.toH1Function.grad x)) (w.toH1Function.grad x) ∂volume =
      -∫ x in cubeSetAt y n,
        vecDot (matVecMul (a x - b x) (v.grad x)) (w.toH1Function.grad x) ∂volume := by
    rw [Section4.Provider.Schauder.integral_vecDot_sub_split hAu hAv hsplitW w,
      Section4.Provider.Schauder.integral_vecDot_sub_split hAv hbv hsplitP w,
      hu w, hv w]
    ring
  -- ellipticity on the left
  have hEnergyInt : IntegrableOn
      (fun x => vecDot (matVecMul (a x) (w.toH1Function.grad x)) (w.toH1Function.grad x))
      (cubeSetAt y n) := integrableOn_vecDot_of_memVectorL2 hAw hwL2
  have hSqInt : IntegrableOn (fun x => lam * vecNormSq (w.toH1Function.grad x))
      (cubeSetAt y n) :=
    (integrableOn_vecDot_of_memVectorL2 hwL2 hwL2).const_mul lam
  have hlower : ∫ x in cubeSetAt y n, lam * vecNormSq (w.toH1Function.grad x) ∂volume ≤
      ∫ x in cubeSetAt y n,
        vecDot (matVecMul (a x) (w.toH1Function.grad x)) (w.toH1Function.grad x) ∂volume := by
    refine integral_mono_ae hSqInt hEnergyInt ((ae_restrict_iff' hUmeas).2 ?_)
    refine Filter.Eventually.of_forall fun x hx => ?_
    change lam * vecNormSq (w.toH1Function.grad x) ≤
      vecDot (matVecMul (a x) (w.toH1Function.grad x)) (w.toH1Function.grad x)
    rw [vecDot_comm]
    exact (hEll.2 x hx).2.2.1 (w.toH1Function.grad x)
  -- the norm-square integral is dominated by the Euclidean energy
  have hNormInt : IntegrableOn (fun x => ‖w.toH1Function.grad x‖ ^ (2 : ℕ))
      (cubeSetAt y n) := by
    have hn : MemLp (fun x => ‖w.toH1Function.grad x‖) 2
        (volume.restrict (cubeSetAt y n)) := hwL2.norm
    have := hn.integrable_mul hn
    simpa [Pi.mul_apply, pow_two] using! this
  have hEucInt : IntegrableOn (fun x => vecNormSq (w.toH1Function.grad x))
      (cubeSetAt y n) := integrableOn_vecDot_of_memVectorL2 hwL2 hwL2
  have hcompare : ∫ x in cubeSetAt y n, ‖w.toH1Function.grad x‖ ^ (2 : ℕ) ∂volume ≤
      ∫ x in cubeSetAt y n, vecNormSq (w.toH1Function.grad x) ∂volume :=
    integral_mono hNormInt hEucInt fun x => sq_norm_le_vecNormSq _
  -- the right-hand side
  have hpert : ∀ x ∈ cubeSetAt y n,
      ‖matVecMul (a x - b x) (v.grad x)‖ ≤ ((d : ℝ) * delta) * ‖v.grad x‖ := by
    intro x hx
    exact norm_matVecMul_le_of_entry_bound hdelta
      (fun i j => by simpa [Matrix.sub_apply] using hab x hx i j) (v.grad x)
  have hupper := abs_setIntegral_vecDot_le_of_norm_le (cubeSetAt y n) hUmeas
    (by positivity : (0 : ℝ) ≤ (d : ℝ) * delta) hvL2 hwL2 hpert
  -- assemble
  have hSnn : (0 : ℝ) ≤ Real.sqrt (∫ x in cubeSetAt y n,
      ‖w.toH1Function.grad x‖ ^ (2 : ℕ) ∂volume) := Real.sqrt_nonneg _
  have hNormNonneg : (0 : ℝ) ≤ ∫ x in cubeSetAt y n,
      ‖w.toH1Function.grad x‖ ^ (2 : ℕ) ∂volume :=
    integral_nonneg fun x => by positivity
  have hchain : lam * (Real.sqrt (∫ x in cubeSetAt y n,
        ‖w.toH1Function.grad x‖ ^ (2 : ℕ) ∂volume)) ^ (2 : ℕ) ≤
      (d : ℝ) * ((d : ℝ) * delta) *
        (Real.sqrt (∫ x in cubeSetAt y n, ‖v.grad x‖ ^ (2 : ℕ) ∂volume) *
          Real.sqrt (∫ x in cubeSetAt y n,
            ‖w.toH1Function.grad x‖ ^ (2 : ℕ) ∂volume)) := by
    have hsq := Real.sq_sqrt hNormNonneg
    rw [hsq]
    have hmid : lam * ∫ x in cubeSetAt y n, ‖w.toH1Function.grad x‖ ^ (2 : ℕ) ∂volume ≤
        ∫ x in cubeSetAt y n, lam * vecNormSq (w.toH1Function.grad x) ∂volume := by
      rw [integral_const_mul]
      exact mul_le_mul_of_nonneg_left hcompare hlam.le
    refine le_trans hmid (le_trans hlower ?_)
    rw [hkey]
    exact le_trans (neg_le_abs _) hupper
  have hgrad : (∫ x in cubeSetAt y n, ‖u.grad x - v.grad x‖ ^ (2 : ℕ) ∂volume) =
      ∫ x in cubeSetAt y n, ‖w.toH1Function.grad x‖ ^ (2 : ℕ) ∂volume := by
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    change ‖u.grad x - v.grad x‖ ^ (2 : ℕ) = ‖w.toH1Function.grad x‖ ^ (2 : ℕ)
    rw [hwg x]
  rw [hgrad]
  rcases eq_or_lt_of_le hSnn with hzero | hpos
  · rw [← hzero]
    positivity
  · have hdiv : lam * Real.sqrt (∫ x in cubeSetAt y n,
        ‖w.toH1Function.grad x‖ ^ (2 : ℕ) ∂volume) ≤
        (d : ℝ) * ((d : ℝ) * delta) *
          Real.sqrt (∫ x in cubeSetAt y n, ‖v.grad x‖ ^ (2 : ℕ) ∂volume) := by
      have h := hchain
      rw [pow_two] at h
      have hmul : (lam * Real.sqrt (∫ x in cubeSetAt y n,
            ‖w.toH1Function.grad x‖ ^ (2 : ℕ) ∂volume)) *
            Real.sqrt (∫ x in cubeSetAt y n, ‖w.toH1Function.grad x‖ ^ (2 : ℕ) ∂volume) ≤
          ((d : ℝ) * ((d : ℝ) * delta) *
            Real.sqrt (∫ x in cubeSetAt y n, ‖v.grad x‖ ^ (2 : ℕ) ∂volume)) *
            Real.sqrt (∫ x in cubeSetAt y n,
              ‖w.toH1Function.grad x‖ ^ (2 : ℕ) ∂volume) := by
        linarith only [h]
      exact le_of_mul_le_mul_right hmul hpos
    rw [inv_mul_eq_div, div_mul_eq_mul_div, le_div_iff₀ hlam]
    linarith only [hdiv]

/-! ## 2. `L²` convergence of the truncated solutions -/

/-- **The truncated solutions of a Dirichlet problem with a datum converge in `L²` to the
full-field solution.**  The datum `h` and the forcing `g` are the same at every scale; only the
coefficient field moves. -/
theorem tendsto_l2_cutoff_of_h10Diff (M : ABKModel d) (omega : FullSample d M.gamma)
    (y : Vec d) (n : ℤ) {h : H1Function (cubeSetAt y n)} {g : Vec d → Vec d}
    {u : ℤ → H1Function (cubeSetAt y n)} {v : H1Function (cubeSetAt y n)}
    (hu : ∀ L : ℤ, HasZeroTraceDifferenceOn (cubeSetAt y n) (u L) h)
    (huw : ∀ L : ℤ, IsDivFormWeakSolutionOn
      ((Cutoff.coefficientCutoff M.nu L omega.1).toCoeffField) (cubeSetAt y n) (u L) g)
    (hv : HasZeroTraceDifferenceOn (cubeSetAt y n) v h)
    (hvw : IsDivFormWeakSolutionOn (streamCoefficient M.nu omega) (cubeSetAt y n) v g) :
    Tendsto (fun L : ℤ =>
        Real.sqrt (∫ x in cubeSetAt y n, ((u L).toFun x - v.toFun x) ^ (2 : ℕ) ∂volume))
      atTop (𝓝 0) := by
  have : NeZero d := Algsuperdiff.Section3.Provider.Orlicz.neZero_of_model M
  obtain ⟨C, hC⟩ := fullTailGood_sharp omega.2
  obtain ⟨ell, hell⟩ := exists_cubeSetAt_subset_openCubeSet y n
  have hgamma : M.gamma < 1 := by
    have := M.shellPrefix.gamma_le_quarter
    linarith only [this]
  obtain ⟨CP, hCP, hpoin⟩ :=
    exists_poincare_integral_constant (isOpenBoundedConvexDomain_cubeSetAt y n)
  obtain ⟨Lam', hEll'⟩ := exists_isEllipticFieldOn_streamCoefficient M.nu_pos omega y n
  have hbv : MemVectorL2 (cubeSetAt y n)
      fun x => matVecMul (streamCoefficient M.nu omega x) (v.grad x) :=
    memVectorL2_matVecMul_of_isEllipticFieldOn hEll' v.grad_memVectorL2
  obtain ⟨wv, hwvf, hwvg⟩ := hv
  set E : ℝ := Real.sqrt (∫ x in cubeSetAt y n, ‖v.grad x‖ ^ (2 : ℕ) ∂volume) with hE_def
  have hbound : ∀ L : ℤ,
      Real.sqrt (∫ x in cubeSetAt y n, ((u L).toFun x - v.toFun x) ^ (2 : ℕ) ∂volume) ≤
        CP * (M.nu⁻¹ * ((d : ℝ) * (d : ℝ) * cutoffLimitGap d M.gamma C ell L) * E) := by
    intro L
    obtain ⟨wL, hwLf, hwLg⟩ := hu L
    have hwf : ∀ x, (wL - wv).toH1Function.toFun x = (u L).toFun x - v.toFun x := by
      intro x
      rw [h10Sub_toH1Function, H1Function.sub_toFun]
      change wL.toH1Function.toFun x - wv.toH1Function.toFun x = _
      rw [hwLf x, hwvf x]
      ring
    have hwg : ∀ x, (wL - wv).toH1Function.grad x = (u L).grad x - v.grad x := by
      intro x
      rw [h10Sub_toH1Function, H1Function.sub_grad]
      change wL.toH1Function.grad x - wv.toH1Function.grad x = _
      rw [hwLg x, hwvg x]
      abel
    have hval : (∫ x in cubeSetAt y n, ((u L).toFun x - v.toFun x) ^ (2 : ℕ) ∂volume) =
        ∫ x in cubeSetAt y n, (wL - wv).toH1Function.toFun x ^ (2 : ℕ) ∂volume := by
      refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
      change ((u L).toFun x - v.toFun x) ^ (2 : ℕ) = (wL - wv).toH1Function.toFun x ^ (2 : ℕ)
      rw [hwf x]
    have hgrad : (∫ x in cubeSetAt y n, ‖(u L).grad x - v.grad x‖ ^ (2 : ℕ) ∂volume) =
        ∫ x in cubeSetAt y n, ‖(wL - wv).toH1Function.grad x‖ ^ (2 : ℕ) ∂volume := by
      refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
      change ‖(u L).grad x - v.grad x‖ ^ (2 : ℕ) = ‖(wL - wv).toH1Function.grad x‖ ^ (2 : ℕ)
      rw [hwg x]
    obtain ⟨Lam, hEll⟩ :=
      exists_isEllipticFieldOn_normalizedCoefficientCutoff M.nu_pos L omega.1 y n
    have hab : ∀ x ∈ cubeSetAt y n, ∀ i j,
        |normalizedCoefficientCutoff M.nu L omega.1 x i j -
          streamCoefficient M.nu omega x i j| ≤ cutoffLimitGap d M.gamma C ell L := by
      intro x hx i j
      rw [abs_sub_comm]
      exact abs_streamCoefficient_sub_normalizedCoefficientCutoff_le_gap M.nu hgamma omega hC
        ell L (hell hx) i j
    have huw' : IsDivFormWeakSolutionOn (normalizedCoefficientCutoff M.nu L omega.1)
        (cubeSetAt y n) (u L) g :=
      (isDivFormWeakSolutionOn_normalizedCoefficientCutoff_iff M.nu L omega.1).2 (huw L)
    have henergy := sqrt_energy_grad_sub_le_of_h10Diff (cutoffLimitGap_nonneg d M.gamma C ell L)
      hEll hab hbv (wL - wv) hwg huw' hvw
    rw [hval]
    calc Real.sqrt (∫ x in cubeSetAt y n, (wL - wv).toH1Function.toFun x ^ (2 : ℕ) ∂volume)
        ≤ CP * Real.sqrt (∫ x in cubeSetAt y n,
            ‖(wL - wv).toH1Function.grad x‖ ^ (2 : ℕ) ∂volume) := hpoin (wL - wv)
      _ ≤ CP * (M.nu⁻¹ * ((d : ℝ) * (d : ℝ) * cutoffLimitGap d M.gamma C ell L) * E) := by
          refine mul_le_mul_of_nonneg_left ?_ hCP
          rw [← hgrad]
          exact henergy
  have hlim : Tendsto (fun L : ℤ =>
      CP * (M.nu⁻¹ * ((d : ℝ) * (d : ℝ) * cutoffLimitGap d M.gamma C ell L) * E))
      atTop (𝓝 0) := by
    have hgap := tendsto_cutoffLimitGap_atTop d hgamma C ell
    have h1 : Tendsto (fun L : ℤ =>
        CP * (M.nu⁻¹ * ((d : ℝ) * (d : ℝ) * cutoffLimitGap d M.gamma C ell L) * E))
        atTop (𝓝 (CP * (M.nu⁻¹ * ((d : ℝ) * (d : ℝ) * 0) * E))) :=
      ((((hgap.const_mul ((d : ℝ) * (d : ℝ))).const_mul M.nu⁻¹).mul_const E).const_mul CP)
    simpa using h1
  exact squeeze_zero (fun L => Real.sqrt_nonneg _) hbound hlim

/-! ## 3. Uniform bounds on the truncated solutions pass to the full field -/

/-- **A uniform almost-everywhere bound on the truncated solutions holds for the full-field
solution.**  If every solution of the Dirichlet problem with datum `h` and forcing `g` for the
truncated field `a_L`, at every truncation scale `L ≥ m₀`, is almost everywhere within `K` of a
square-integrable function `f` on the cube, then so is every solution of the same problem for
the full stream field. -/
theorem ae_abs_sub_le_of_cutoff_bounds (M : ABKModel d) (omega : FullSample d M.gamma)
    (y : Vec d) (n : ℤ) (h : H1Function (cubeSetAt y n)) {g : Vec d → Vec d}
    (hg : MemVectorL2 (cubeSetAt y n) g) {f : Vec d → ℝ} (hf : MemL2On (cubeSetAt y n) f)
    {K : ℝ} {m₀ : ℤ}
    (hbound : ∀ L : ℤ, m₀ ≤ L → ∀ uL : H1Function (cubeSetAt y n),
      HasZeroTraceDifferenceOn (cubeSetAt y n) uL h →
      IsDivFormWeakSolutionOn ((Cutoff.coefficientCutoff M.nu L omega.1).toCoeffField)
        (cubeSetAt y n) uL g →
      ∀ᵐ x ∂(volume.restrict (cubeSetAt y n)), |uL.toFun x - f x| ≤ K)
    {v : H1Function (cubeSetAt y n)} (hv : HasZeroTraceDifferenceOn (cubeSetAt y n) v h)
    (hvw : IsDivFormWeakSolutionOn (streamCoefficient M.nu omega) (cubeSetAt y n) v g) :
    ∀ᵐ x ∂(volume.restrict (cubeSetAt y n)), |v.toFun x - f x| ≤ K := by
  have : NeZero d := Algsuperdiff.Section3.Provider.Orlicz.neZero_of_model M
  have hU := isOpenBoundedConvexDomain_cubeSetAt y n
  have hne := cubeSetAt_nonempty y n
  have hex : ∀ L : ℤ, ∃ uL : H1Function (cubeSetAt y n),
      HasZeroTraceDifferenceOn (cubeSetAt y n) uL h ∧
        IsDivFormWeakSolutionOn ((Cutoff.coefficientCutoff M.nu L omega.1).toCoeffField)
          (cubeSetAt y n) uL g := by
    intro L
    obtain ⟨Lam, hEll⟩ := exists_isEllipticFieldOn_cutoff M L n y omega.1
    obtain ⟨w, hw⟩ := exists_h10_isDivFormWeakSolutionOn_add hU hne hEll h hg
    exact ⟨h + w.toH1Function, ⟨w, fun _ => rfl, fun _ => rfl⟩, hw⟩
  choose u hu huw using hex
  have hlim := tendsto_l2_cutoff_of_h10Diff M omega y n hu huw hv hvw
  have hUfin : volume (cubeSetAt y n) ≠ ⊤ := volume_cubeSetAt_ne_top y n
  have hfL : ∀ L : ℤ,
      MemLp (fun x => (u L).toFun x - f x) 2 (volume.restrict (cubeSetAt y n)) :=
    fun L => (u L).memL2.sub hf
  have hgv : MemLp (fun x => v.toFun x - f x) 2 (volume.restrict (cubeSetAt y n)) :=
    v.memL2.sub hf
  have hlim' : Tendsto (fun L : ℤ => Real.sqrt (∫ x in cubeSetAt y n,
      (((u L).toFun x - f x) - (v.toFun x - f x)) ^ (2 : ℕ) ∂volume)) atTop (𝓝 0) := by
    refine hlim.congr fun L => ?_
    congr 1
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    ring
  have hev : ∀ᶠ L : ℤ in atTop, m₀ ≤ L := eventually_ge_atTop m₀
  have hupper : ∀ᵐ x ∂(volume.restrict (cubeSetAt y n)), v.toFun x - f x ≤ K := by
    refine ae_le_of_tendsto_l2 hUfin hfL hgv ?_ hlim'
    filter_upwards [hev] with L hL
    filter_upwards [hbound L hL (u L) (hu L) (huw L)] with x hx
    exact (abs_le.1 hx).2
  have hlower : ∀ᵐ x ∂(volume.restrict (cubeSetAt y n)), -K ≤ v.toFun x - f x := by
    refine ae_ge_of_tendsto_l2 hUfin hfL hgv ?_ hlim'
    filter_upwards [hev] with L hL
    filter_upwards [hbound L hL (u L) (hu L) (huw L)] with x hx
    exact (abs_le.1 hx).1
  filter_upwards [hupper, hlower] with x hx1 hx2
  exact abs_le.2 ⟨hx2, hx1⟩

end

end Algsuperdiff.Section5.Provider
