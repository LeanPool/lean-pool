/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Stream.CutoffSecondMoment
public import LeanPool.HighContrastHomogenization.Support.Book.Ch02.Response
public import Mathlib.MeasureTheory.Integral.Prod

/-!
# CutoffL2Expectation

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section

/-!
# ABK26's `e.km.L2.expectation`

The source display (ABK26) is

`| E[ ‖k_m‖²_{L²(cu_l)} ] − ½ c⁺ γ⁻¹ 3^{2γm} | ≤ 2 c⁺ 3^{2γm}`  for every `l ∈ ℤ`.

Here `‖k_m‖²_{L²(cu_l)}` is the volume-normalized square
`⨍_{cu_l} ‖k_m(x)‖_F² dx`, represented by
`Book.Ch02.average (Book.Ch02.cubeDomain (originCube d l))`
of `x ↦ matrixFrobeniusNormSq (cutoff m ω x)`, and `c⁺` is the Frobenius
origin-mass constant `Algsuperdiff.Section3.Disorder.cstarPlus`, normalized by
`E[‖j_0(0)‖_F²] = c⁺ log 3`.  This is the constant that the source's
non-degeneracy input `⨍ j_k : j_k = c⁺ (log 3) 3^{2γk}` refers to.

The proof is exactly the source's: the pointwise second moment is constant in
`x` (`integral_frobeniusMass_cutoff`), so Fubini turns the cube average into
that constant, and `Kgamma_bounds` (`e.K.cgamma.ineq`, `0 ≤ K_γ − γ⁻¹ ≤ 4`)
converts `c⁺ K_γ 3^{2γm} / 2` into the source's `½ c⁺ γ⁻¹ 3^{2γm}` with the
stated error `2 c⁺ 3^{2γm}`.

## Main results

* `integral_average_frobeniusMass_cutoff`: the exact expectation
  `E[‖k_m‖²_{L²(cu_l)}] = c⁺ K_γ 3^{2γm} / 2`, for every `l`.
* `integral_average_frobeniusMass_finiteShellIncrement`: the corresponding
  exact expectation `E[‖k_m − k_n‖²_{L²(cu_l)}] = c⁺ (log 3) ∑_{k ∈ (n,m]} 3^{2γk}`,
  which is the deterministic main term of `e.km.kn.L2.bound`.

## References

* ABK26, `e.km.L2.expectation`.
* ABK26, `e.K.cgamma.def`, `e.K.cgamma.ineq`.
* ABK26, `e.km.kn.L2.bound`.
-/

namespace Algsuperdiff.Section3.Provider.Stream

open Filter MeasureTheory
open HCPolySupport
open HCPolySupport.Book.Ch02
open Algsuperdiff.Frozen.Assumptions
open Algsuperdiff.Section3.Cutoff

noncomputable section

variable {d : ℕ}

/-! ## Measurability of the cutoff Frobenius mass -/

/-- The Frobenius mass of the genuine cutoff at a fixed point is measurable in
the sample. -/
theorem measurable_frobeniusMass_cutoff (m : ℤ) (x : Vec d) :
    Measurable (fun omega : CutoffSample d =>
      matrixFrobeniusNormSq (cutoff m omega x)) := by
  change Measurable fun omega : CutoffSample d =>
    ∑ i : Fin d, ∑ l : Fin d, cutoff m omega x i l ^ 2
  exact Finset.univ.measurable_sum fun i _ =>
    Finset.univ.measurable_sum fun l _ =>
      (measurable_cutoff_apply_entry m x i l).pow_const 2

/-- The Frobenius mass of the genuine cutoff is continuous in the point. -/
theorem continuous_frobeniusMass_cutoff (m : ℤ) (omega : CutoffSample d) :
    Continuous (fun x : Vec d => matrixFrobeniusNormSq (cutoff m omega x)) := by
  change Continuous fun x : Vec d =>
    ∑ i : Fin d, ∑ l : Fin d, cutoff m omega x i l ^ 2
  exact continuous_finsetSum _ fun i _ =>
    continuous_finsetSum _ fun l _ =>
      (continuous_cutoff_entry m omega i l).pow 2

/-- Carathéodory joint measurability of the cutoff Frobenius mass in the point
and the sample: it is continuous in the point and measurable in the sample. -/
theorem measurable_uncurry_frobeniusMass_cutoff (m : ℤ) :
    Measurable (Function.uncurry (fun (x : Vec d) (omega : CutoffSample d) =>
      matrixFrobeniusNormSq (cutoff m omega x))) :=
  measurable_uncurry_of_continuous_of_measurable
    (fun omega => continuous_frobeniusMass_cutoff m omega)
    (fun x => measurable_frobeniusMass_cutoff m x)

/-! ## Pointwise integrability -/

/-- The Frobenius mass of the genuine cutoff at a point of an origin cube is
integrable, being dominated by the proved cutoff envelope of that cube. -/
theorem integrable_frobeniusMass_cutoff (M : ABKModel d) (ell m : ℤ)
    {x : Vec d} (hx : x ∈ openCubeSet (originCube d ell)) :
    Integrable
      (fun omega : CutoffSample d => matrixFrobeniusNormSq (cutoff m omega x))
      (cutoffSampleLaw M).toMeasure := by
  refine Integrable.mono'
    ((integrable_cutoffLocalControl_pow M ell m 2).const_mul ((d : ℝ) ^ 2))
    (measurable_frobeniusMass_cutoff m x).aestronglyMeasurable ?_
  filter_upwards with omega
  rw [Real.norm_eq_abs,
    abs_of_nonneg (matrixFrobeniusNormSq_nonneg (cutoff m omega x))]
  exact matrixFrobeniusNormSq_le_of_abs_entry_le fun i l =>
    abs_cutoff_entry_le_cutoffLocalControl ell m omega hx i l

/-! ## The cube average -/

/-- The exact expectation of the volume-normalized `L²` mass of `k_m` on any
origin cube.  Since the pointwise second moment is independent of the base
point, Fubini reduces the cube average to that constant. -/
theorem integral_average_frobeniusMass_cutoff (M : ABKModel d) (l m : ℤ) :
    ∫ omega : CutoffSample d,
        Book.Ch02.average (Book.Ch02.cubeDomain (originCube d l))
          (fun x => matrixFrobeniusNormSq (cutoff m omega x))
        ∂(cutoffSampleLaw M).toMeasure =
      Disorder.cstarPlus M * Kgamma M.gamma / 2 *
        (3 : ℝ) ^ (2 * M.gamma * (m : ℝ)) := by
  let : Fact (volume (openCubeSet (originCube d l)) < ⊤) :=
    ⟨volume_openCubeSet_lt_top (originCube d l)⟩
  have hUmeas : MeasurableSet (openCubeSet (originCube d l)) :=
    measurableSet_openCubeSet (originCube d l)
  have hVpos : (0 : ℝ) < (volume (openCubeSet (originCube d l))).toReal := by
    rw [volume_openCubeSet_toReal]
    exact cubeVolume_pos (originCube d l)
  have hnorm : ∀ x : Vec d,
      (∫ omega : CutoffSample d, ‖matrixFrobeniusNormSq (cutoff m omega x)‖
        ∂(cutoffSampleLaw M).toMeasure) =
        Disorder.cstarPlus M * Kgamma M.gamma / 2 *
          (3 : ℝ) ^ (2 * M.gamma * (m : ℝ)) := by
    intro x
    rw [← integral_frobeniusMass_cutoff M m x]
    refine integral_congr_ae ?_
    filter_upwards with omega
    rw [Real.norm_eq_abs,
      abs_of_nonneg (matrixFrobeniusNormSq_nonneg (cutoff m omega x))]
  have hprod : Integrable
      (Function.uncurry (fun (x : Vec d) (omega : CutoffSample d) =>
        matrixFrobeniusNormSq (cutoff m omega x)))
      ((volume.restrict (openCubeSet (originCube d l))).prod
        (cutoffSampleLaw M).toMeasure) := by
    refine (integrable_prod_iff
      (measurable_uncurry_frobeniusMass_cutoff m).aestronglyMeasurable).mpr
      ⟨?_, ?_⟩
    · rw [ae_restrict_iff' hUmeas]
      filter_upwards with x hxU
      exact integrable_frobeniusMass_cutoff M l m hxU
    · refine (integrable_const
        (Disorder.cstarPlus M * Kgamma M.gamma / 2 *
          (3 : ℝ) ^ (2 * M.gamma * (m : ℝ)))).congr ?_
      filter_upwards with x
      exact (hnorm x).symm
  have hswap := integral_integral_swap hprod
  calc ∫ omega : CutoffSample d,
        Book.Ch02.average (Book.Ch02.cubeDomain (originCube d l))
          (fun x => matrixFrobeniusNormSq (cutoff m omega x))
        ∂(cutoffSampleLaw M).toMeasure
      = ∫ omega : CutoffSample d,
          (volume (openCubeSet (originCube d l))).toReal⁻¹ *
            (∫ x in openCubeSet (originCube d l),
              matrixFrobeniusNormSq (cutoff m omega x) ∂volume)
          ∂(cutoffSampleLaw M).toMeasure := by
        simp only [Book.Ch02.average, Book.Ch02.cubeDomain_coe]
    _ = (volume (openCubeSet (originCube d l))).toReal⁻¹ *
          ∫ omega : CutoffSample d,
            (∫ x in openCubeSet (originCube d l),
              matrixFrobeniusNormSq (cutoff m omega x) ∂volume)
            ∂(cutoffSampleLaw M).toMeasure := integral_const_mul _ _
    _ = (volume (openCubeSet (originCube d l))).toReal⁻¹ *
          ∫ x in openCubeSet (originCube d l),
            (∫ omega : CutoffSample d, matrixFrobeniusNormSq (cutoff m omega x)
              ∂(cutoffSampleLaw M).toMeasure) ∂volume := by
        rw [hswap]
    _ = (volume (openCubeSet (originCube d l))).toReal⁻¹ *
          ((volume (openCubeSet (originCube d l))).toReal •
            (Disorder.cstarPlus M * Kgamma M.gamma / 2 *
              (3 : ℝ) ^ (2 * M.gamma * (m : ℝ)))) := by
        simp only [integral_frobeniusMass_cutoff M m, setIntegral_const,
          measureReal_def]
    _ = Disorder.cstarPlus M * Kgamma M.gamma / 2 *
          (3 : ℝ) ^ (2 * M.gamma * (m : ℝ)) := by
        rw [smul_eq_mul, inv_mul_cancel_left₀ (ne_of_gt hVpos)]

/-! ## The increment mean term of `e.km.kn.L2.bound` -/

/-- The Frobenius mass of a finite stream increment is continuous in the
point. -/
theorem continuous_frobeniusMass_finiteShellIncrement (n m : ℤ)
    (omega : ShellSeq d) :
    Continuous
      (fun x : Vec d => matrixFrobeniusNormSq (finiteShellIncrement omega n m x)) := by
  change Continuous fun x : Vec d =>
    ∑ i : Fin d, ∑ l : Fin d, finiteShellIncrement omega n m x i l ^ 2
  refine continuous_finsetSum _ fun i _ => continuous_finsetSum _ fun l _ => ?_
  have hentry : Continuous
      (fun x : Vec d => finiteShellIncrement omega n m x i l) := by
    simp only [finiteShellIncrement_apply_entry]
    exact continuous_finsetSum _ fun k _ =>
      (continuous_apply l).comp ((continuous_apply i).comp (omega k).1.1.continuous)
  exact hentry.pow 2

/-- The Frobenius mass of a finite stream increment at a fixed point is
measurable in the sample. -/
theorem measurable_frobeniusMass_finiteShellIncrement (n m : ℤ) (x : Vec d) :
    Measurable (fun omega : ShellSeq d =>
      matrixFrobeniusNormSq (finiteShellIncrement omega n m x)) := by
  change Measurable fun omega : ShellSeq d =>
    ∑ i : Fin d, ∑ l : Fin d, finiteShellIncrement omega n m x i l ^ 2
  refine Finset.univ.measurable_sum fun i _ =>
    Finset.univ.measurable_sum fun l _ => ?_
  have hentry : Measurable
      (fun omega : ShellSeq d => finiteShellIncrement omega n m x i l) := by
    simp only [finiteShellIncrement_apply_entry]
    exact Finset.measurable_sum _ fun k _ =>
      (ShellField.measurable_eval_entry x i l).comp (measurable_pi_apply k)
  exact hentry.pow_const 2

/-- Carathéodory joint measurability for the finite stream increment. -/
theorem measurable_uncurry_frobeniusMass_finiteShellIncrement (n m : ℤ) :
    Measurable (Function.uncurry (fun (x : Vec d) (omega : ShellSeq d) =>
      matrixFrobeniusNormSq (finiteShellIncrement omega n m x))) :=
  measurable_uncurry_of_continuous_of_measurable
    (fun omega => continuous_frobeniusMass_finiteShellIncrement n m omega)
    (fun x => measurable_frobeniusMass_finiteShellIncrement n m x)

/-- The Frobenius mass of a finite stream increment is integrable: it is a
finite sum of squares of `L²` shell entries. -/
theorem integrable_frobeniusMass_finiteShellIncrement (M : ABKModel d) (n m : ℤ)
    (x : Vec d) :
    Integrable (fun omega : ShellSeq d =>
      matrixFrobeniusNormSq (finiteShellIncrement omega n m x)) M.P.toMeasure := by
  have hmem : ∀ i l : Fin d, MemLp
      (fun omega : ShellSeq d => ∑ k ∈ Finset.Ioc n m, (omega k) x i l) 2
      M.P.toMeasure :=
    fun i l => memLp_finsetSum _ fun k _ => memLp_two_shell_entry M k x i l
  have hbase : Integrable (fun omega : ShellSeq d =>
      ∑ i : Fin d, ∑ l : Fin d,
        (∑ k ∈ Finset.Ioc n m, (omega k) x i l) ^ 2) M.P.toMeasure := by
    refine integrable_finsetSum _ fun i _ => integrable_finsetSum _ fun l _ => ?_
    exact (memLp_two_iff_integrable_sq (hmem i l).aestronglyMeasurable).mp (hmem i l)
  refine hbase.congr (Filter.Eventually.of_forall fun omega => ?_)
  change (∑ i : Fin d, ∑ l : Fin d,
      (∑ k ∈ Finset.Ioc n m, (omega k) x i l) ^ 2) =
    ∑ i : Fin d, ∑ l : Fin d, finiteShellIncrement omega n m x i l ^ 2
  simp only [finiteShellIncrement_apply_entry]

/-- The exact expectation of the volume-normalized `L²` mass of the stream
increment `k_m - k_n` on any origin cube.  This is the deterministic main term
of ABK26's `e.km.kn.L2.bound`; the source's remaining `O_{Γ₁}` term is a
fluctuation statement, not part of this expectation. -/
theorem integral_average_frobeniusMass_finiteShellIncrement (M : ABKModel d)
    (l n m : ℤ) :
    ∫ omega : ShellSeq d,
        Book.Ch02.average (Book.Ch02.cubeDomain (originCube d l))
          (fun x => matrixFrobeniusNormSq (finiteShellIncrement omega n m x))
        ∂M.P.toMeasure =
      ∑ k ∈ Finset.Ioc n m, (3 : ℝ) ^ (2 * M.gamma * (k : ℝ)) *
        (Disorder.cstarPlus M * Real.log 3) := by
  let : Fact (volume (openCubeSet (originCube d l)) < ⊤) :=
    ⟨volume_openCubeSet_lt_top (originCube d l)⟩
  have hVpos : (0 : ℝ) < (volume (openCubeSet (originCube d l))).toReal := by
    rw [volume_openCubeSet_toReal]
    exact cubeVolume_pos (originCube d l)
  have hnorm : ∀ x : Vec d,
      (∫ omega : ShellSeq d,
        ‖matrixFrobeniusNormSq (finiteShellIncrement omega n m x)‖
        ∂M.P.toMeasure) =
        ∑ k ∈ Finset.Ioc n m, (3 : ℝ) ^ (2 * M.gamma * (k : ℝ)) *
          (Disorder.cstarPlus M * Real.log 3) := by
    intro x
    rw [← integral_frobeniusMass_finiteShellIncrement M n m x]
    refine integral_congr_ae ?_
    filter_upwards with omega
    rw [Real.norm_eq_abs,
      abs_of_nonneg (matrixFrobeniusNormSq_nonneg
        (finiteShellIncrement omega n m x))]
  have hprod : Integrable
      (Function.uncurry (fun (x : Vec d) (omega : ShellSeq d) =>
        matrixFrobeniusNormSq (finiteShellIncrement omega n m x)))
      ((volume.restrict (openCubeSet (originCube d l))).prod M.P.toMeasure) := by
    refine (integrable_prod_iff
      (measurable_uncurry_frobeniusMass_finiteShellIncrement n
        m).aestronglyMeasurable).mpr ⟨?_, ?_⟩
    · filter_upwards with x
      exact integrable_frobeniusMass_finiteShellIncrement M n m x
    · refine (integrable_const
        (∑ k ∈ Finset.Ioc n m, (3 : ℝ) ^ (2 * M.gamma * (k : ℝ)) *
          (Disorder.cstarPlus M * Real.log 3))).congr ?_
      filter_upwards with x
      exact (hnorm x).symm
  have hswap := integral_integral_swap hprod
  calc ∫ omega : ShellSeq d,
        Book.Ch02.average (Book.Ch02.cubeDomain (originCube d l))
          (fun x => matrixFrobeniusNormSq (finiteShellIncrement omega n m x))
        ∂M.P.toMeasure
      = ∫ omega : ShellSeq d,
          (volume (openCubeSet (originCube d l))).toReal⁻¹ *
            (∫ x in openCubeSet (originCube d l),
              matrixFrobeniusNormSq (finiteShellIncrement omega n m x) ∂volume)
          ∂M.P.toMeasure := by
        simp only [Book.Ch02.average, Book.Ch02.cubeDomain_coe]
    _ = (volume (openCubeSet (originCube d l))).toReal⁻¹ *
          ∫ omega : ShellSeq d,
            (∫ x in openCubeSet (originCube d l),
              matrixFrobeniusNormSq (finiteShellIncrement omega n m x) ∂volume)
            ∂M.P.toMeasure := integral_const_mul _ _
    _ = (volume (openCubeSet (originCube d l))).toReal⁻¹ *
          ∫ x in openCubeSet (originCube d l),
            (∫ omega : ShellSeq d,
              matrixFrobeniusNormSq (finiteShellIncrement omega n m x)
              ∂M.P.toMeasure) ∂volume := by
        rw [hswap]
    _ = (volume (openCubeSet (originCube d l))).toReal⁻¹ *
          ((volume (openCubeSet (originCube d l))).toReal •
            ∑ k ∈ Finset.Ioc n m, (3 : ℝ) ^ (2 * M.gamma * (k : ℝ)) *
              (Disorder.cstarPlus M * Real.log 3)) := by
        simp only [integral_frobeniusMass_finiteShellIncrement M n m,
          setIntegral_const, measureReal_def]
    _ = ∑ k ∈ Finset.Ioc n m, (3 : ℝ) ^ (2 * M.gamma * (k : ℝ)) *
          (Disorder.cstarPlus M * Real.log 3) := by
        rw [smul_eq_mul, inv_mul_cancel_left₀ (ne_of_gt hVpos)]

end

end Algsuperdiff.Section3.Provider.Stream
