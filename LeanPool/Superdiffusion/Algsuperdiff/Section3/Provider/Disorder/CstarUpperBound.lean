/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Disorder.Cstar
public import Mathlib.Analysis.Complex.ExponentialBounds
public import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
public import Mathlib.MeasureTheory.Integral.Layercake

/-!
# CstarUpperBound

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section

/-!
# An absolute upper bound on the shell constant `cstar`

ABK26 states, immediately after assumption (J4), that the normalized Gaussian
tail `e.kn.reg.ass` of (J2) and the non-degeneracy identity `e.nondeg` of (J4)
"together imply `c_star <= 1`".  This module proves the corresponding Lean bound
from the two frozen assumptions alone.

## The argument

`e.nondeg` says that `c_star (log 3)` is the second moment of the *potential
part* of the origin forcing `j_0 e`.  Orthogonal projections are norm
contractions, so

```
c_star (log 3) <= E[ |j_0(0) e|^2 ] <= E[ ||j_0(0)||_op^2 ] <= E[ X^2 ] ,
```

where `X` is the exact J2 observable
`||j_0||_{L^inf(cu_0)} + sqrt d ||grad j_0||_{L^inf(cu_0)} + d ||grad^2 j_0||_{L^inf(cu_0)}`.
The J2 tail `P[X > t] <= exp(-t^2)` for `t >= 1` gives, by the layer-cake
formula,

```
E[X^2] = int_0^inf P[X^2 > t] dt <= 1 + int_1^inf exp(-t) dt = 1 + e^{-1} ,
```

whence `c_star <= (1 + e^{-1}) / log 3 = 1.2451...`, in particular the clean
absolute bound `c_star <= 3/2`.

The constant obtained here is absolute: it depends on neither the dimension nor
any model parameter.  It is slightly weaker than the manuscript's own `c_star
<= 1`; sharpening it to `1` would need more than the frozen tail (the tail is
only assumed above level one, and `E[X^2] <= 1 + e^{-1}` is sharp for that
information).

## Main results

* `integral_sq_le_of_gaussian_tail`: the second-moment bound `E[X^2] <= 1 + e^{-1}`
  for any nonnegative observable with the normalized J2 tail.
* `cstar_mul_log_three_le`: `c_star (log 3) <= 1 + e^{-1}`, the sharp form.
* `cstar_le_three_halves`: the absolute bound `c_star <= 3/2`.

## References

* ABK26, `e.kn.reg.ass`, `e.nondeg` and the remark.
-/

namespace Algsuperdiff.Section3.Provider.Disorder

open MeasureTheory Set
open HCPolySupport
open Algsuperdiff.Frozen.Assumptions
open scoped ENNReal

noncomputable section

variable {d : ℕ}

/-! ## The second moment of a normalized Gaussian tail -/

/-- The J2 tail of a nonnegative observable, transferred to its square: for
`t >= 1`, `P[X^2 > t] <= exp(-t)`. -/
private theorem measure_sq_gt_le_of_gaussian_tail {Omega : Type*}
    [MeasurableSpace Omega] {mu : Measure Omega} {X : Omega → ℝ}
    (hXnonneg : ∀ omega, 0 ≤ X omega)
    (htail : ∀ t : ℝ, 1 ≤ t →
      mu {omega | t < X omega} ≤ ENNReal.ofReal (Real.exp (-(t ^ 2))))
    (t : ℝ) (ht : 1 ≤ t) :
    mu {omega | t < X omega ^ 2} ≤ ENNReal.ofReal (Real.exp (-t)) := by
  calc
    mu {omega | t < X omega ^ 2} ≤ mu {omega | Real.sqrt t < X omega} := by
      apply measure_mono
      intro omega homega
      change t < X omega ^ 2 at homega
      change Real.sqrt t < X omega
      rw [Real.sqrt_lt (by linarith) (hXnonneg omega)]
      exact homega
    _ ≤ ENNReal.ofReal (Real.exp (-Real.sqrt t ^ 2)) := by
      apply htail
      rw [← Real.sqrt_one]
      exact Real.sqrt_le_sqrt ht
    _ = ENNReal.ofReal (Real.exp (-t)) := by
      rw [Real.sq_sqrt (by linarith)]

/-- **The second-moment bound behind `c_star <= 1`.**  A nonnegative measurable
observable on a probability space whose upper tail obeys the normalized
Gaussian bound `P[X > t] <= exp(-t^2)` for `t >= 1` has second moment at most
`1 + e^{-1}`.

The two contributions are the trivial one below level one and the layer-cake
integral `int_1^inf exp(-t) dt = e^{-1}` above it. -/
theorem integral_sq_le_of_gaussian_tail {Omega : Type*} [MeasurableSpace Omega]
    {mu : Measure Omega} [IsProbabilityMeasure mu] {X : Omega → ℝ}
    (hXmeas : Measurable X) (hXnonneg : ∀ omega, 0 ≤ X omega)
    (htail : ∀ t : ℝ, 1 ≤ t →
      mu {omega | t < X omega} ≤ ENNReal.ofReal (Real.exp (-(t ^ 2)))) :
    ∫ omega, X omega ^ 2 ∂mu ≤ 1 + Real.exp (-1) := by
  have hXsq_meas : Measurable fun omega ↦ X omega ^ 2 := hXmeas.pow_const 2
  have hnonneg : 0 ≤ᵐ[mu] fun omega ↦ X omega ^ 2 :=
    Filter.Eventually.of_forall fun omega ↦ sq_nonneg (X omega)
  -- the layer-cake representation of the second moment
  have hlayer : (∫⁻ omega, ENNReal.ofReal (X omega ^ 2) ∂mu) =
      ∫⁻ t in Ioi (0 : ℝ), mu {omega | t < X omega ^ 2} :=
    lintegral_eq_lintegral_meas_lt mu hnonneg hXsq_meas.aemeasurable
  -- below level one
  have hsmall : (∫⁻ t in Ioc (0 : ℝ) 1, mu {omega | t < X omega ^ 2}) ≤ 1 := by
    calc
      (∫⁻ t in Ioc (0 : ℝ) 1, mu {omega | t < X omega ^ 2}) ≤
          ∫⁻ _t in Ioc (0 : ℝ) 1, (1 : ℝ≥0∞) :=
        setLIntegral_mono measurable_const fun _t _ ↦ prob_le_one
      _ = 1 := by
        simp only [lintegral_one, Measure.restrict_apply, MeasurableSet.univ,
          univ_inter, Real.volume_Ioc]
        norm_num
  -- above level one
  have hlarge : (∫⁻ t in Ioi (1 : ℝ), mu {omega | t < X omega ^ 2}) ≤
      ENNReal.ofReal (Real.exp (-1)) := by
    calc
      (∫⁻ t in Ioi (1 : ℝ), mu {omega | t < X omega ^ 2}) ≤
          ∫⁻ t in Ioi (1 : ℝ), ENNReal.ofReal (Real.exp (-t)) := by
        refine setLIntegral_mono ?_ fun t ht ↦
          measure_sq_gt_le_of_gaussian_tail hXnonneg htail t ht.le
        exact (Real.continuous_exp.comp continuous_neg).measurable.ennreal_ofReal
      _ = ENNReal.ofReal (Real.exp (-1)) := by
        rw [← ofReal_integral_eq_lintegral_ofReal (integrableOn_exp_neg_Ioi 1)
          (Filter.Eventually.of_forall fun t ↦ (Real.exp_pos (-t)).le)]
        rw [integral_exp_neg_Ioi]
  have hsplit : Ioi (0 : ℝ) = Ioc 0 1 ∪ Ioi 1 :=
    (Ioc_union_Ioi_eq_Ioi (by norm_num : (0 : ℝ) ≤ 1)).symm
  have htotal : (∫⁻ omega, ENNReal.ofReal (X omega ^ 2) ∂mu) ≤
      ENNReal.ofReal (1 + Real.exp (-1)) := by
    rw [hlayer, hsplit, lintegral_union measurableSet_Ioi (Ioc_disjoint_Ioi le_rfl)]
    rw [ENNReal.ofReal_add (by norm_num) (Real.exp_pos (-1)).le, ENNReal.ofReal_one]
    exact add_le_add hsmall hlarge
  rw [integral_eq_lintegral_of_nonneg_ae hnonneg hXsq_meas.aestronglyMeasurable]
  exact ENNReal.toReal_le_of_le_ofReal (by positivity) htotal

/-! ## The origin forcing energy -/

/-- The `L²` energy of the origin forcing is the raw expectation of the squared
J2 observable, up to the operator-norm comparison of `j_0(0) e` with the value
part of that observable. -/
private theorem sq_norm_zeroShellForcingL2_le (M : ABKModel d) (e : Vec d)
    (he : HCPolySupport.Book.Ch02.vecNorm e = 1)
    (hmem : MemLp (ShellField.originForcing e) 2
      (ShellField.zeroShellRegLaw M.P).toMeasure) :
    ‖ShellField.zeroShellForcingL2 M.P e hmem‖ ^ 2 ≤
      ∫ F : ℤ → ShellField d, ShellField.j2Observable d (F 0) ^ 2 ∂M.P.toMeasure := by
  let f : RegCoeffField d → ℝ := fun a ↦ ‖ShellField.originForcing e a‖ ^ 2
  have hXmeas : Measurable fun F : ℤ → ShellField d ↦ ShellField.j2Observable d (F 0) :=
    (ShellField.j2Observable_measurable d).comp ShellField.measurable_zeroShellMap
  have hXnonneg : ∀ F : ℤ → ShellField d, 0 ≤ ShellField.j2Observable d (F 0) :=
    fun F ↦ ShellField.j2Observable_nonneg d (F 0)
  have hXmem : MemLp (fun F : ℤ → ShellField d ↦ ShellField.j2Observable d (F 0)) 2
      M.P.toMeasure :=
    Algsuperdiff.Probability.memLp_two_of_gaussian_tail hXmeas hXnonneg M.J2.gaussian_tail
  have hXsq : Integrable
      (fun F : ℤ → ShellField d ↦ ShellField.j2Observable d (F 0) ^ 2) M.P.toMeasure :=
    (memLp_two_iff_integrable_sq hXmeas.aestronglyMeasurable).mp hXmem
  calc
    ‖ShellField.zeroShellForcingL2 M.P e hmem‖ ^ 2 =
        ∫ a, f a ∂(ShellField.zeroShellRegLaw M.P).toMeasure := by
      rw [← real_inner_self_eq_norm_sq, MeasureTheory.L2.inner_def]
      apply integral_congr_ae
      filter_upwards [ShellField.coeFn_zeroShellForcingL2 M.P e hmem] with a ha
      rw [ha]
      exact real_inner_self_eq_norm_sq _
    _ = ∫ F : ℤ → ShellField d, f (ShellField.forgetShell (F 0)) ∂M.P.toMeasure := by
      have hfmeas : AEStronglyMeasurable f
          (ShellField.zeroShellRegLaw M.P).toMeasure := by
        change AEStronglyMeasurable
          (fun a ↦ ‖ShellField.originForcing e a‖ ^ 2)
          (ShellField.zeroShellRegLaw M.P).toMeasure
        exact hmem.aestronglyMeasurable.norm.pow 2
      change ∫ a, f a ∂Measure.map
          (ShellField.forgetShell ∘ fun F : ℤ → ShellField d ↦ F 0) M.P.toMeasure = _
      exact integral_map
        (ShellField.measurable_zeroShellRegMap (d := d)).aemeasurable hfmeas
    _ ≤ ∫ F : ℤ → ShellField d,
        ShellField.j2Observable d (F 0) ^ 2 ∂M.P.toMeasure := by
      refine integral_mono_of_nonneg
        (Filter.Eventually.of_forall fun F ↦ sq_nonneg _) hXsq ?_
      filter_upwards with F
      have hunit : ShellField.unitCubeValueNorm (F 0) ≤ ShellField.j2Observable d (F 0) := by
        calc
          ShellField.unitCubeValueNorm (F 0) ≤
              ShellField.unitCubeValueNorm (F 0) +
                Real.sqrt d * ShellField.unitCubeDerivNorm (F 0) :=
            le_add_of_nonneg_right (mul_nonneg (Real.sqrt_nonneg _)
              (ShellField.unitCubeDerivNorm_nonneg (F 0)))
          _ ≤ ShellField.unitCubeValueNorm (F 0) +
                Real.sqrt d * ShellField.unitCubeDerivNorm (F 0) +
                (d : ℝ) * ShellField.unitCubeSecondDerivNorm (F 0) :=
            le_add_of_nonneg_right (mul_nonneg (Nat.cast_nonneg d)
              (ShellField.unitCubeSecondDerivNorm_nonneg (F 0)))
          _ = ShellField.j2Observable d (F 0) := rfl
      have hchain : ‖ShellField.originForcing e (ShellField.forgetShell (F 0))‖ ≤
          ShellField.j2Observable d (F 0) := by
        calc
          ‖ShellField.originForcing e (ShellField.forgetShell (F 0))‖ ≤
              HCPolySupport.Book.Ch02.matrixOperatorNorm
                ((ShellField.forgetShell (F 0)) 0) :=
            ShellField.norm_originForcing_le_matrixOperatorNorm e
              (ShellField.forgetShell (F 0)) he
          _ = HCPolySupport.Book.Ch02.matrixOperatorNorm ((F 0) 0) := rfl
          _ ≤ ShellField.unitCubeValueNorm (F 0) :=
            ShellField.matrixOperatorNorm_zero_le_unitCubeValueNorm (F 0)
          _ ≤ ShellField.j2Observable d (F 0) := hunit
      exact (sq_le_sq₀ (norm_nonneg _) (hXnonneg F)).mpr hchain

/-- Orthogonal projections contract the norm, so the J4 corrector energy is at
most the raw forcing energy. -/
private theorem sq_norm_zeroShellPotentialCorrector_le (M : ABKModel d)
    (hstationary : ∀ z : Vec d,
      Measure.map (HCPolySupport.translateReg z)
          (ShellField.zeroShellRegLaw M.P).toMeasure =
        (ShellField.zeroShellRegLaw M.P).toMeasure)
    (e : Vec d)
    (hmem : MemLp (ShellField.originForcing e) 2
      (ShellField.zeroShellRegLaw M.P).toMeasure) :
    ‖ShellField.zeroShellPotentialCorrector M.P hstationary e hmem‖ ^ 2 ≤
      ‖ShellField.zeroShellForcingL2 M.P e hmem‖ ^ 2 := by
  let := ShellField.zeroShellRegLaw_vaddInvariant M.P hstationary
  have hnorm :=
    Submodule.norm_starProjection_apply_le
      (Algsuperdiff.Probability.Stationary.stationaryPotentialSubspace
        (μ := (ShellField.zeroShellRegLaw M.P).toMeasure) (d := d))
      (ShellField.zeroShellForcingL2 M.P e hmem)
  have hsq := (sq_le_sq₀ (norm_nonneg _)
    (norm_nonneg (ShellField.zeroShellForcingL2 M.P e hmem))).mpr hnorm
  simpa only [ShellField.zeroShellPotentialCorrector,
    ShellField.zeroShellProjectedForcing, ShellField.zeroShellPotentialSubspace,
    norm_neg] using! hsq

/-! ## The bound -/

private theorem vecNorm_single_eq_one (i : Fin d) :
    HCPolySupport.Book.Ch02.vecNorm (Pi.single i 1 : Vec d) = 1 := by
  have hsq : vecNormSq (Pi.single i 1 : Vec d) = 1 := by
    rw [vecNormSq, vecDot, Finset.sum_eq_single i]
    · norm_num
    · intro j _ hji
      simp [Pi.single_eq_of_ne hji]
    · simp
  apply (sq_eq_sq₀
    (HCPolySupport.Book.Ch02.vecNorm_nonneg (Pi.single i 1 : Vec d))
    (by norm_num)).mp
  rw [HCPolySupport.Book.Ch02.vecNorm_sq_eq_vecNormSq, hsq]
  norm_num

/-- **The sharp form of the manuscript's remark.**  The J4 normalization
`c_star (log 3)` of `e.nondeg` is at most the second moment `1 + e^{-1}`
allowed by the J2 tail `e.kn.reg.ass`. -/
theorem cstar_mul_log_three_le (M : ABKModel d) :
    Algsuperdiff.Section3.Disorder.cstar M * Real.log 3 ≤ 1 + Real.exp (-1) := by
  have hd : 0 < d := lt_of_lt_of_le (by norm_num) M.shellPrefix.dimension
  let i : Fin d := ⟨0, hd⟩
  let e : Vec d := Pi.single i 1
  have he : HCPolySupport.Book.Ch02.vecNorm e = 1 := vecNorm_single_eq_one i
  have hstationary :=
    ShellField.zeroShellRegLaw_stationary_of_zeroShellLaw_stationary M.P M.J1.stationary
  have hmem : MemLp (ShellField.originForcing e) 2
      (ShellField.zeroShellRegLaw M.P).toMeasure :=
    ShellField.memLp_originForcing_of_j2_tail M.P M.J2.gaussian_tail e he
  have hXmeas : Measurable fun F : ℤ → ShellField d ↦ ShellField.j2Observable d (F 0) :=
    (ShellField.j2Observable_measurable d).comp ShellField.measurable_zeroShellMap
  calc
    Algsuperdiff.Section3.Disorder.cstar M * Real.log 3 =
        ‖ShellField.zeroShellPotentialCorrector M.P hstationary e hmem‖ ^ 2 :=
      ((Algsuperdiff.Section3.Disorder.cstar_characterization M).2.1 ⟨e, he⟩).symm
    _ ≤ ‖ShellField.zeroShellForcingL2 M.P e hmem‖ ^ 2 :=
      sq_norm_zeroShellPotentialCorrector_le M hstationary e hmem
    _ ≤ ∫ F : ℤ → ShellField d,
        ShellField.j2Observable d (F 0) ^ 2 ∂M.P.toMeasure :=
      sq_norm_zeroShellForcingL2_le M e he hmem
    _ ≤ 1 + Real.exp (-1) :=
      integral_sq_le_of_gaussian_tail hXmeas
        (fun F ↦ ShellField.j2Observable_nonneg d (F 0)) M.J2.gaussian_tail

private theorem exp_neg_one_le_half : Real.exp (-1) ≤ 1 / 2 := by
  have hprod : Real.exp (-1) * Real.exp 1 = 1 := by
    rw [← Real.exp_add]
    norm_num
  have htwo : (2 : ℝ) ≤ Real.exp 1 := by
    have h := Real.add_one_le_exp (1 : ℝ)
    linarith
  have hkey : 0 ≤ Real.exp (-1) * (Real.exp 1 - 2) :=
    mul_nonneg (Real.exp_pos (-1)).le (by linarith)
  nlinarith [hprod, hkey]

private theorem one_le_log_three : (1 : ℝ) ≤ Real.log 3 := by
  have h : Real.exp 1 < 2.7182818286 := Real.exp_one_lt_d9
  rw [Real.le_log_iff_exp_le (by norm_num : (0 : ℝ) < 3)]
  norm_num at h
  linarith

/-- **The dimension-free gate constant.**  The shell constant of any standing
ABK model is at most `3/2`; the manuscript's own remark asserts the sharper
`c_star <= 1`, which the frozen tail alone does not deliver. -/
theorem cstar_le_three_halves (M : ABKModel d) :
    Algsuperdiff.Section3.Disorder.cstar M ≤ 3 / 2 := by
  have hpos : 0 < Algsuperdiff.Section3.Disorder.cstar M :=
    (Algsuperdiff.Section3.Disorder.cstar_characterization M).1
  have hgap : 0 ≤ Algsuperdiff.Section3.Disorder.cstar M * (Real.log 3 - 1) :=
    mul_nonneg hpos.le (by linarith [one_le_log_three])
  have hmain := cstar_mul_log_three_le M
  nlinarith [exp_neg_one_le_half, hgap, hmain]

end

end Algsuperdiff.Section3.Provider.Disorder
