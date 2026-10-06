/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/

module

public import LeanPool.CaffarelliKohnNirenberg.Core.Step2.MorreyFormFixedScale
public import LeanPool.CIVAxisymmetric.Regularity.UniformMorreyDecayTop
public import LeanPool.CIVAxisymmetric.Regularity.TopCylinderContainment
public import LeanPool.CIVAxisymmetric.Statements.ForceC2Bounded
public import LeanPool.CIVAxisymmetric.Setting.EnergyClassLemmas
public import Mathlib.MeasureTheory.Integral.Lebesgue.Add
public import Mathlib.MeasureTheory.Function.StronglyMeasurable.AEStronglyMeasurable
public import Mathlib.Order.Directed
public import LeanPool.CIVAxisymmetric.Setting.SuitableWeakSolutionClass

/-!
# Top-cylinder Theorem A smallness

The last step of the uniform interior route to `CIV.timeZeroSingularSetNull`: from the uniform
interior
Morrey decay of `CIV.uniform_morrey_decay_of_top_gradient_small`, together with the fixed-scale
Sobolev display and the pointwise-bounded force, the dimensionless Theorem A quantity is small on
a top-boundary cylinder at every interior centre, for a single fixed radius, uniformly in the
base time. The proof applies the fixed-scale display at each interior time on a shrinking window
below the top slice, then passes to the limit along an increasing sequence of base times using
continuity of the Lebesgue integral from below on the resulting monotone family of sets.
-/

public section

open MeasureTheory Set Filter
open scoped ENNReal
open CKN.Foundation.Parabolic CKN CKN.Foundation.Parabolic.Integration


noncomputable section

namespace CIV

/-! ### A scale small enough for one power-law bound -/

/-- Given a nonnegative coefficient, a positive target and a positive exponent, there is a
scale at most `1` making the power-law quantity `C * ρ ^ e` fall below the target. Used three
times below, once for each of the velocity, pressure and force smallness thresholds. -/
theorem exists_rho_le_of_rpow_bound {C B e : ℝ} (hC : 0 ≤ C) (hB : 0 < B) (he : 0 < e) :
    ∃ ρ : ℝ, 0 < ρ ∧ ρ ≤ 1 ∧ C * ρ ^ e ≤ B := by
  rcases hC.lt_or_eq with hCpos | hC0
  · set ρ₀ : ℝ := (B / C) ^ (e⁻¹) with hρ₀def
    have hBC : 0 < B / C := div_pos hB hCpos
    have hρ₀pos : 0 < ρ₀ := Real.rpow_pos_of_pos hBC _
    set ρ : ℝ := min 1 ρ₀ with hρdef
    have hρpos : 0 < ρ := lt_min one_pos hρ₀pos
    have hρle1 : ρ ≤ 1 := min_le_left _ _
    have hρleρ₀ : ρ ≤ ρ₀ := min_le_right _ _
    refine ⟨ρ, hρpos, hρle1, ?_⟩
    have hpow_le : ρ ^ e ≤ ρ₀ ^ e := Real.rpow_le_rpow hρpos.le hρleρ₀ he.le
    have hρ₀e : ρ₀ ^ e = B / C := by
      rw [hρ₀def, ← Real.rpow_mul hBC.le, inv_mul_cancel₀ he.ne', Real.rpow_one]
    have hfinal : ρ ^ e ≤ B / C := hρ₀e ▸ hpow_le
    have hmul := mul_le_mul_of_nonneg_left hfinal hCpos.le
    rwa [mul_div_cancel₀ B hCpos.ne'] at hmul
  · refine ⟨1, one_pos, le_refl 1, ?_⟩
    rw [← hC0]
    have : (0 : ℝ) * (1 : ℝ) ^ e = 0 := by ring
    rw [this]
    exact hB.le

/-! ### The volume of the top-boundary cylinder and of the backward cylinder -/

/-- The volume of the top-boundary cylinder `vec3Ball x ρ ×ˢ Ioo (-(ρ ^ 2)) 0`, computed by the
same product-measure display used for the parabolic ball, since the base time interval has the
same length `ρ ^ 2` as the backward cylinder's. -/
theorem volume_topCylinder (x : Vec3) (ρ : ℝ) (hρ : 0 ≤ ρ) :
    volume (vec3Ball x ρ ×ˢ Ioo (-(ρ ^ 2)) (0 : ℝ)) =
      ENNReal.ofReal (4 * Real.pi / 3 * ρ ^ 5) := by
  have hstep : volume (vec3Ball x ρ ×ˢ Ioo (-(ρ ^ 2)) (0 : ℝ)) =
      volume (vec3Ball x ρ) * ENNReal.ofReal (ρ ^ 2) := by
    change (Measure.prod (volume : Measure Vec3) (volume : Measure ℝ))
        (vec3Ball x ρ ×ˢ Ioo (-(ρ ^ 2)) (0 : ℝ)) =
      volume (vec3Ball x ρ) * ENNReal.ofReal (ρ ^ 2)
    rw [Measure.prod_prod, Real.volume_Ioo]
    congr 2
    ring
  rw [hstep, volume_vec3Ball_eq, ← ENNReal.ofReal_pow hρ,
    ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity)]
  congr 1
  ring

/-- The volume of a backward parabolic cylinder in the closed-form display `(4π/3) r ^ 5`. -/
theorem volume_parabolicCylinder_eq (x : Vec3) (t r : ℝ) (hr : 0 ≤ r) :
    volume (parabolicCylinder x t r) = ENNReal.ofReal (4 * Real.pi / 3 * r ^ 5) := by
  rw [volume_parabolicCylinder, volume_vec3Ball_eq, ← ENNReal.ofReal_pow hr,
    ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity)]
  congr 1
  ring

/-! ### The force term is bounded by a pointwise multiple of the cylinder's volume -/

/-- On any measurable subset of the unit cylinder where the force is bounded in Euclidean norm
by `M`, the scale-invariant force integrand is dominated by a constant multiple of the volume of
that subset, with the constant depending only on `ρ`, `q` and `M`. -/
theorem lintegral_force_term_le {f : ParabolicPoint → Vec3} {M : ℝ} (hM0 : 0 ≤ M)
    (hMbound : ∀ z ∈ unitCylinder, vec3EuclideanNorm (f z) ≤ M)
    {S : Set ParabolicPoint} (hSmeas : MeasurableSet S) (hS : S ⊆ unitCylinder)
    {ρ q : ℝ} (hρ : 0 ≤ ρ) (hq : 0 < q) :
    (∫⁻ z in S, ENNReal.ofReal (ρ ^ (3 * q - 3)) *
        ENNReal.ofReal (vec3EuclideanNorm (f z)) ^ q) ≤
      ENNReal.ofReal (ρ ^ (3 * q - 3) * M ^ q) * volume S := by
  have hpt : ∀ z ∈ S, ENNReal.ofReal (ρ ^ (3 * q - 3)) *
      ENNReal.ofReal (vec3EuclideanNorm (f z)) ^ q ≤
      ENNReal.ofReal (ρ ^ (3 * q - 3) * M ^ q) := by
    intro z hz
    have hzu : z ∈ unitCylinder := hS hz
    have hfz : vec3EuclideanNorm (f z) ≤ M := hMbound z hzu
    have h1 : ENNReal.ofReal (vec3EuclideanNorm (f z)) ^ q ≤ ENNReal.ofReal M ^ q :=
      ENNReal.rpow_le_rpow (ENNReal.ofReal_le_ofReal hfz) hq.le
    have h2 : ENNReal.ofReal (ρ ^ (3 * q - 3)) * ENNReal.ofReal (vec3EuclideanNorm (f z)) ^ q ≤
        ENNReal.ofReal (ρ ^ (3 * q - 3)) * ENNReal.ofReal M ^ q :=
      mul_le_mul_of_nonneg_left h1 (by positivity)
    have h3 : ENNReal.ofReal (ρ ^ (3 * q - 3)) * ENNReal.ofReal M ^ q =
        ENNReal.ofReal (ρ ^ (3 * q - 3) * M ^ q) := by
      rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_rpow_of_nonneg hM0 hq.le]
    rw [← h3]
    exact h2
  calc (∫⁻ z in S, ENNReal.ofReal (ρ ^ (3 * q - 3)) *
      ENNReal.ofReal (vec3EuclideanNorm (f z)) ^ q) ≤
      ∫⁻ _z in S, ENNReal.ofReal (ρ ^ (3 * q - 3) * M ^ q) := setLIntegral_mono' hSmeas hpt
    _ = ENNReal.ofReal (ρ ^ (3 * q - 3) * M ^ q) * volume S := setLIntegral_const _ _

/-! ### Splitting the combined integrand into its three terms -/

/-- On a fixed measurable set where the velocity and pressure are almost-everywhere strongly
measurable, the integral of the combined velocity-cube, pressure and force integrand splits into
the sum of the three separate integrals. -/
theorem lintegral_velocity_pressure_force_split
    {u : ParabolicPoint → Vec3} {p : ParabolicPoint → ℝ} {f : ParabolicPoint → Vec3}
    {S : Set ParabolicPoint} {ρ q : ℝ}
    (hum : AEStronglyMeasurable u (volume.restrict S))
    (hpm : AEStronglyMeasurable p (volume.restrict S)) :
    (∫⁻ z in S, ENNReal.ofReal (vec3EuclideanNorm (u z)) ^ (3 : ℝ) +
        ENNReal.ofReal |p z| ^ (3 / 2 : ℝ) +
        ENNReal.ofReal (ρ ^ (3 * q - 3)) * ENNReal.ofReal (vec3EuclideanNorm (f z)) ^ q) =
      (∫⁻ z in S, ENNReal.ofReal (vec3EuclideanNorm (u z)) ^ (3 : ℝ)) +
        (∫⁻ z in S, ENNReal.ofReal |p z| ^ (3 / 2 : ℝ)) +
        (∫⁻ z in S, ENNReal.ofReal (ρ ^ (3 * q - 3)) *
          ENNReal.ofReal (vec3EuclideanNorm (f z)) ^ q) := by
  have hF1meas : AEMeasurable (fun z => ENNReal.ofReal (vec3EuclideanNorm (u z)) ^ (3 : ℝ))
      (volume.restrict S) := by
    have hcont : Continuous (fun v : Vec3 => ENNReal.ofReal (vec3EuclideanNorm v) ^ (3 : ℝ)) :=
      ENNReal.continuous_rpow_const.comp
        (ENNReal.continuous_ofReal.comp CKN.Foundation.Parabolic.continuous_vec3EuclideanNorm)
    exact (hcont.comp_aestronglyMeasurable hum).aemeasurable
  have hF2meas : AEMeasurable (fun z => ENNReal.ofReal |p z| ^ (3 / 2 : ℝ))
      (volume.restrict S) := by
    have hcont : Continuous (fun v : ℝ => ENNReal.ofReal |v| ^ (3 / 2 : ℝ)) :=
      ENNReal.continuous_rpow_const.comp (ENNReal.continuous_ofReal.comp continuous_abs)
    exact (hcont.comp_aestronglyMeasurable hpm).aemeasurable
  have hrw : (fun z => ENNReal.ofReal (vec3EuclideanNorm (u z)) ^ (3 : ℝ) +
        ENNReal.ofReal |p z| ^ (3 / 2 : ℝ) +
        ENNReal.ofReal (ρ ^ (3 * q - 3)) * ENNReal.ofReal (vec3EuclideanNorm (f z)) ^ q) =
      (fun z => ENNReal.ofReal (vec3EuclideanNorm (u z)) ^ (3 : ℝ) +
        (ENNReal.ofReal |p z| ^ (3 / 2 : ℝ) +
        ENNReal.ofReal (ρ ^ (3 * q - 3)) * ENNReal.ofReal (vec3EuclideanNorm (f z)) ^ q)) := by
    funext z; ring
  rw [hrw, lintegral_add_left' hF1meas, lintegral_add_left' hF2meas, add_assoc]

/-! ### Local measurability of the velocity and the pressure -/

/-- On a backward cylinder whose closure sits inside the unit cylinder, the velocity is almost
everywhere strongly measurable for the restricted volume measure, via the compactly-contained
local box the suitable weak-solution class supplies at that closure. -/
theorem aestronglyMeasurable_velocity_of_closure_subset
    {q : ℝ} {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
    {p : ParabolicPoint → ℝ} {f : ParabolicPoint → Vec3}
    (hsol : IsSuitableWeakSolution (vec3Ball 0 1) (Ioo (-1) 0) q u Du p f)
    {x : Vec3} {t r : ℝ} (hr : 0 < r)
    (hsub : closure (parabolicCylinder x t r) ⊆ spaceTimeSet (vec3Ball 0 1) (Ioo (-1) 0)) :
    AEStronglyMeasurable u (volume.restrict (parabolicCylinder x t r)) := by
  obtain ⟨hΩopen, hIopen, -, -, -, hMeasAll, -, -, -⟩ := hsol
  obtain ⟨Ω', J, hbox, hcyl⟩ := exists_localBox_of_closure_subset hΩopen hIopen hr hsub
  obtain ⟨hum, -, -, -, -, -, -, -, -⟩ := hMeasAll Ω' J hbox
  exact hum.mono_set hcyl

/-- On any subset of the unit cylinder, the pressure is almost everywhere strongly measurable for
the restricted volume measure, directly from the global energy class's `L^{3/2}` membership. -/
theorem aestronglyMeasurable_pressure_of_subset
    {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3} {p : ParabolicPoint → ℝ}
    (henergy : GlobalEnergyClass u Du p) {S : Set ParabolicPoint} (hS : S ⊆ unitCylinder) :
    AEStronglyMeasurable p (volume.restrict S) :=
  henergy.2.2.aestronglyMeasurable.mono_set hS

/-! ### The force term's radius algebra -/

/-- The real-number identity turning the raw force-integral bound (a pointwise bound times the
cylinder's volume) into the same power of `ρ` used by the force-smallness threshold, times
`ρ ^ 2`. -/
theorem force_scale_real_fixed {ρ q : ℝ} (hρ : 0 < ρ) :
    ρ ^ (3 * q - 3) * (4 * Real.pi / 3 * ρ ^ 5) = 4 * Real.pi / 3 * ρ ^ (3 * q) * ρ ^ 2 := by
  have hρ5 : (ρ : ℝ) ^ (5 : ℕ) = ρ ^ (5 : ℝ) := by norm_num [Real.rpow_natCast]
  have hρ2 : (ρ : ℝ) ^ (2 : ℕ) = ρ ^ (2 : ℝ) := by norm_num [Real.rpow_natCast]
  rw [hρ5, show ρ ^ (3 * q - 3) * (4 * Real.pi / 3 * ρ ^ (5 : ℝ)) =
      4 * Real.pi / 3 * (ρ ^ (3 * q - 3) * ρ ^ (5 : ℝ)) by ring,
    ← Real.rpow_add hρ, show (3 * q - 3) + (5 : ℝ) = 3 * q + 2 by ring,
    Real.rpow_add hρ, hρ2]
  ring

/-! ### The combined bound on one fixed backward cylinder -/

/-- At a fixed interior time `s` and a fixed radius `ρ` satisfying the uniform Morrey decay of
`CIV.uniform_morrey_decay_of_top_gradient_small`, the fixed-scale display
`CKN.step2_fixed_scale_integrals` bounds the velocity and pressure integrals, the pointwise force
bound bounds the force integral, and once `ρ` is small enough for each of the three
scale-invariant smallness thresholds, their sum over the backward cylinder is at most
`ε₀ * ρ ^ 2`. -/
theorem lintegral_combined_le_of_scale_small
    {q : ℝ} {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
    {p : ParabolicPoint → ℝ} {f : ParabolicPoint → Vec3}
    (hsol : IsSuitableWeakSolution (vec3Ball 0 1) (Ioo (-1) 0) q u Du p f)
    (henergy : GlobalEnergyClass u Du p)
    {Mf : ℝ} (hMf0 : 0 ≤ Mf) (hMbound : ∀ z ∈ unitCylinder, vec3EuclideanNorm (f z) ≤ Mf)
    {x : Vec3} {s ρ M₁ ε₀ : ℝ} (hρ : 0 < ρ) (hM₁ : 1 ≤ M₁) (hq : 0 < q) (hε₀ : 0 < ε₀)
    (hsub2 : closure (parabolicCylinder x s (2 * ρ)) ⊆ spaceTimeSet (vec3Ball 0 1) (Ioo (-1) 0))
    (hdec : max (max (alpha u (x, s) ρ) (beta u Du (x, s) ρ)) (delta p (x, s) ρ ^ 2) ≤
      M₁ * ρ ^ (2 / 5 : ℝ))
    (hv : ρ ^ 2 * (2 * gagliardoConstant * (M₁ * ρ ^ (2 / 5 : ℝ))) ^ 3 ≤ ε₀ / 3 * ρ ^ 2)
    (hpr : M₁ ^ (3 / 2 : ℝ) * ρ ^ (13 / 5 : ℝ) ≤ ε₀ / 3 * ρ ^ 2)
    (hf : 4 * Real.pi / 3 * Mf ^ q * ρ ^ (3 * q) ≤ ε₀ / 3) :
    (∫⁻ w in parabolicCylinder x s ρ, ENNReal.ofReal (vec3EuclideanNorm (u w)) ^ (3 : ℝ) +
        ENNReal.ofReal |p w| ^ (3 / 2 : ℝ) +
        ENNReal.ofReal (ρ ^ (3 * q - 3)) * ENNReal.ofReal (vec3EuclideanNorm (f w)) ^ q) ≤
      ENNReal.ofReal (ε₀ * ρ ^ 2) := by
  have hρle2ρ : ρ ≤ 2 * ρ := by linarith only [hρ]
  have hsubρ : closure (parabolicCylinder x s ρ) ⊆ spaceTimeSet (vec3Ball 0 1) (Ioo (-1) 0) :=
    (closure_mono (parabolicCylinder_mono hρ.le hρle2ρ)).trans hsub2
  have hSunit : parabolicCylinder x s ρ ⊆ unitCylinder :=
    (subset_closure).trans hsubρ
  have hSmeas : MeasurableSet (parabolicCylinder x s ρ) := measurableSet_parabolicCylinder x s ρ
  have hstep2 := step2_fixed_scale_integrals (Ω := vec3Ball (0 : Vec3) 1) (I := Ioo (-1 : ℝ) 0)
    (isSuitableWeakSolutionIntegrable_of_isSuitableWeakSolution hsol) (z := (x, s)) hρ hM₁ hsub2
      hdec
  have hvel := hstep2.1
  have hpress := hstep2.2.2
  have hpow2 : ρ ^ (2 : ℝ) = ρ ^ 2 := by norm_num [Real.rpow_natCast]
  rw [hpow2] at hvel
  have hvel' : (∫⁻ w in parabolicCylinder x s ρ,
      ENNReal.ofReal (vec3EuclideanNorm (u w)) ^ (3 : ℝ)) ≤ ENNReal.ofReal (ε₀ / 3 * ρ ^ 2) :=
    hvel.trans (ENNReal.ofReal_le_ofReal hv)
  have hpress' : (∫⁻ w in parabolicCylinder x s ρ, ENNReal.ofReal |p w| ^ (3 / 2 : ℝ)) ≤
      ENNReal.ofReal (ε₀ / 3 * ρ ^ 2) :=
    hpress.trans (ENNReal.ofReal_le_ofReal hpr)
  have hforce := lintegral_force_term_le hMf0 hMbound hSmeas hSunit hρ.le hq (ρ := ρ) (f := f)
  have hvolcyl : volume (parabolicCylinder x s ρ) = ENNReal.ofReal (4 * Real.pi / 3 * ρ ^ 5) :=
    volume_parabolicCylinder_eq x s ρ hρ.le
  rw [hvolcyl] at hforce
  have hcombine : ENNReal.ofReal (ρ ^ (3 * q - 3) * Mf ^ q) *
      ENNReal.ofReal (4 * Real.pi / 3 * ρ ^ 5) =
      ENNReal.ofReal (ρ ^ (3 * q - 3) * (4 * Real.pi / 3 * ρ ^ 5) * Mf ^ q) := by
    rw [← ENNReal.ofReal_mul (by positivity)]
    congr 1
    ring
  rw [hcombine, force_scale_real_fixed hρ] at hforce
  have hforce' : (∫⁻ w in parabolicCylinder x s ρ, ENNReal.ofReal (ρ ^ (3 * q - 3)) *
      ENNReal.ofReal (vec3EuclideanNorm (f w)) ^ q) ≤ ENNReal.ofReal (ε₀ / 3 * ρ ^ 2) := by
    refine hforce.trans (ENNReal.ofReal_le_ofReal ?_)
    have hmul := mul_le_mul_of_nonneg_right hf (by positivity : (0:ℝ) ≤ ρ ^ 2)
    nlinarith only [hmul]
  have hum := aestronglyMeasurable_velocity_of_closure_subset hsol hρ hsubρ
  have hpm := aestronglyMeasurable_pressure_of_subset henergy hSunit
  rw [lintegral_velocity_pressure_force_split hum hpm]
  have hsum : ENNReal.ofReal (ε₀ / 3 * ρ ^ 2) + ENNReal.ofReal (ε₀ / 3 * ρ ^ 2) +
      ENNReal.ofReal (ε₀ / 3 * ρ ^ 2) = ENNReal.ofReal (ε₀ * ρ ^ 2) := by
    rw [← ENNReal.ofReal_add (by positivity) (by positivity),
      ← ENNReal.ofReal_add (by positivity) (by positivity)]
    congr 1
    ring
  calc (∫⁻ z in parabolicCylinder x s ρ, ENNReal.ofReal (vec3EuclideanNorm (u z)) ^ (3 : ℝ)) +
      (∫⁻ z in parabolicCylinder x s ρ, ENNReal.ofReal |p z| ^ (3 / 2 : ℝ)) +
      (∫⁻ z in parabolicCylinder x s ρ, ENNReal.ofReal (ρ ^ (3 * q - 3)) *
        ENNReal.ofReal (vec3EuclideanNorm (f z)) ^ q) ≤
        ENNReal.ofReal (ε₀ / 3 * ρ ^ 2) + ENNReal.ofReal (ε₀ / 3 * ρ ^ 2) +
          ENNReal.ofReal (ε₀ / 3 * ρ ^ 2) :=
      add_le_add (add_le_add hvel' hpress') hforce'
    _ = ENNReal.ofReal (ε₀ * ρ ^ 2) := hsum

/-! ### An increasing sequence of base times approaching the top slice -/

/-- A strictly increasing sequence of base times inside `(-σ, 0)`, tending to the top slice, whose
associated off-centre cylinders increase to the top-boundary cylinder. -/
theorem exists_increasing_seq_topCylinder (x : Vec3) (ρ σ : ℝ) (hσ : 0 < σ) :
    ∃ s : ℕ → ℝ, (∀ n, s n ∈ Ioo (-σ) (0 : ℝ)) ∧ Monotone s ∧
      (⋃ n, (vec3Ball x ρ ×ˢ Ioo (-(ρ ^ 2)) (s n) : Set (Vec3 × ℝ))) =
        (vec3Ball x ρ ×ˢ Ioo (-(ρ ^ 2)) (0 : ℝ) : Set (Vec3 × ℝ)) := by
  set s : ℕ → ℝ := fun n => -(σ / ((n : ℝ) + 2)) with hsdef
  have hdenpos : ∀ n : ℕ, (0 : ℝ) < (n : ℝ) + 2 := fun n => by positivity
  have hsmem : ∀ n, s n ∈ Ioo (-σ) (0 : ℝ) := by
    intro n
    have hpos : 0 < σ / ((n : ℝ) + 2) := div_pos hσ (hdenpos n)
    have hlt : σ / ((n : ℝ) + 2) < σ := by
      rw [div_lt_iff₀ (hdenpos n)]
      nlinarith only [hσ, hdenpos n]
    refine ⟨by rw [hsdef]; dsimp only; linarith only [hlt], by rw [hsdef]; dsimp only; linarith
      only [hpos]⟩
  have hsmono : Monotone s := by
    intro i j hij
    have hij' : (i : ℝ) ≤ (j : ℝ) := by exact_mod_cast hij
    have hle : σ / ((j : ℝ) + 2) ≤ σ / ((i : ℝ) + 2) := by
      apply div_le_div_of_nonneg_left hσ.le (hdenpos i)
      linarith only [hij']
    change -(σ / ((i : ℝ) + 2)) ≤ -(σ / ((j : ℝ) + 2))
    linarith only [hle]
  refine ⟨s, hsmem, hsmono, ?_⟩
  apply Set.Subset.antisymm
  · refine iUnion_subset fun n => Set.prod_mono (le_refl _) ?_
    exact Ioo_subset_Ioo (le_refl _) (hsmem n).2.le
  · rintro ⟨y, τ⟩ ⟨hy, hτ1, hτ2⟩
    obtain ⟨n, hn⟩ := exists_nat_gt (σ / (-τ))
    have hτpos : 0 < -τ := by linarith only [hτ2]
    have hn' : σ / (-τ) < (n : ℝ) := hn
    have hmul : σ < (n : ℝ) * (-τ) := by
      rw [div_lt_iff₀ hτpos] at hn'
      linarith only [hn']
    have hmul2 : σ < ((n : ℝ) + 2) * (-τ) := by nlinarith only [hmul, hτpos]
    have hslt : σ / ((n : ℝ) + 2) < -τ := by
      rw [div_lt_iff₀ (hdenpos n)]
      linarith only [hmul2]
    have hτlt : τ < s n := by
      change τ < -(σ / ((n : ℝ) + 2))
      linarith only [hslt]
    exact mem_iUnion.2 ⟨n, hy, hτ1, hτlt⟩

/-! ### Passing to the top time slice -/

/-- If a nonnegative integrand's integral over every off-centre cylinder based at a time in
`(-σ, 0)` is at most `C`, then its integral over the top-boundary cylinder is at most `C` as
well, by continuity of the Lebesgue integral from below along the increasing family of
off-centre cylinders of `CIV.exists_increasing_seq_topCylinder`. -/
theorem lintegral_topCylinder_le_of_forall_lt (x : Vec3) (ρ σ : ℝ) (hσ : 0 < σ)
    (F : Vec3 × ℝ → ℝ≥0∞) (C : ℝ≥0∞)
    (hbound : ∀ s ∈ Ioo (-σ) (0 : ℝ),
      (∫⁻ z in vec3Ball x ρ ×ˢ Ioo (-(ρ ^ 2)) s, F z) ≤ C) :
    (∫⁻ z in vec3Ball x ρ ×ˢ Ioo (-(ρ ^ 2)) (0 : ℝ), F z) ≤ C := by
  obtain ⟨s, hsmem, hsmono, hsunion⟩ := exists_increasing_seq_topCylinder x ρ σ hσ
  have hmono : Monotone (fun n => vec3Ball x ρ ×ˢ Ioo (-(ρ ^ 2)) (s n)) := by
    intro i j hij
    exact Set.prod_mono (le_refl _) (Ioo_subset_Ioo (le_refl _) (hsmono hij))
  have hdir : Directed (· ⊆ ·) (fun n => vec3Ball x ρ ×ˢ Ioo (-(ρ ^ 2)) (s n)) :=
    hmono.directed_le
  rw [← hsunion, setLIntegral_iUnion_of_directed F hdir]
  exact iSup_le fun n => hbound (s n) (hsmem n)

/-! ### Monotonicity and the velocity/pressure scale algebra -/

/-- A power-law quantity with a fixed nonnegative coefficient and a fixed nonnegative exponent is
monotone in its base. -/
theorem rpow_mul_le_of_le {C a b e : ℝ} (hC : 0 ≤ C) (ha : 0 ≤ a) (hab : a ≤ b) (he : 0 ≤ e) :
    C * a ^ e ≤ C * b ^ e :=
  mul_le_mul_of_nonneg_left (Real.rpow_le_rpow ha hab he) hC

/-- The real-number identity turning a bound on the velocity-smallness coefficient
`(2 * gagliardoConstant * M₁) ^ 3 * ρ ^ (6/5)` into the fixed-scale display's own velocity bound
`ρ ^ 2 * (2 * gagliardoConstant * (M₁ * ρ ^ (2/5))) ^ 3`, both times `ρ ^ 2`. -/
theorem velocity_smallness_of_rpow_bound {M₁ ρ ε₀ : ℝ} (hρ : 0 < ρ)
    (h : (2 * gagliardoConstant * M₁) ^ 3 * ρ ^ (6 / 5 : ℝ) ≤ ε₀ / 3) :
    ρ ^ 2 * (2 * gagliardoConstant * (M₁ * ρ ^ (2 / 5 : ℝ))) ^ 3 ≤ ε₀ / 3 * ρ ^ 2 := by
  have hpow : (ρ ^ (2 / 5 : ℝ)) ^ 3 = ρ ^ (6 / 5 : ℝ) := by
    rw [show (ρ ^ (2 / 5 : ℝ)) ^ 3 = (ρ ^ (2 / 5 : ℝ)) ^ (3 : ℝ) by norm_num [Real.rpow_natCast],
      ← Real.rpow_mul hρ.le]
    norm_num
  have heq : ρ ^ 2 * (2 * gagliardoConstant * (M₁ * ρ ^ (2 / 5 : ℝ))) ^ 3 =
      (2 * gagliardoConstant * M₁) ^ 3 * ρ ^ (6 / 5 : ℝ) * ρ ^ 2 := by
    rw [mul_pow, mul_pow, mul_pow, hpow]
    ring
  rw [heq]
  exact mul_le_mul_of_nonneg_right h (by positivity)

/-- The real-number identity turning a bound on the pressure-smallness coefficient
`M₁ ^ (3/2) * ρ ^ (3/5)` into the fixed-scale display's own pressure bound
`M₁ ^ (3/2) * ρ ^ (13/5)`, both times `ρ ^ 2`. -/
theorem pressure_smallness_of_rpow_bound {M₁ ρ ε₀ : ℝ} (hρ : 0 < ρ)
    (h : M₁ ^ (3 / 2 : ℝ) * ρ ^ (3 / 5 : ℝ) ≤ ε₀ / 3) :
    M₁ ^ (3 / 2 : ℝ) * ρ ^ (13 / 5 : ℝ) ≤ ε₀ / 3 * ρ ^ 2 := by
  have heq : M₁ ^ (3 / 2 : ℝ) * ρ ^ (13 / 5 : ℝ) =
      M₁ ^ (3 / 2 : ℝ) * ρ ^ (3 / 5 : ℝ) * ρ ^ 2 := by
    have hpow2 : ρ ^ (2 : ℝ) = ρ ^ 2 := by norm_num [Real.rpow_natCast]
    rw [mul_assoc, ← hpow2, ← Real.rpow_add hρ]
    norm_num
  rw [heq]
  exact mul_le_mul_of_nonneg_right h (by positivity)

/-! ### The entrance containment at the top time slice -/

/-- An off-centre cylinder based at the top slice `0` and truncated at a base time `s ≤ 0` sits
inside the backward parabolic cylinder of the same radius based at `s`. -/
theorem topSlice_subset_parabolicCylinder (x : Vec3) (s ρ : ℝ) (hs : s ≤ 0) :
    vec3Ball x ρ ×ˢ Ioo (-(ρ ^ 2)) s ⊆ parabolicCylinder x s ρ := by
  rintro ⟨y, τ⟩ ⟨hy, hτ1, hτ2⟩
  exact ⟨hy, by linarith only [hτ1, hs], hτ2.le⟩

/-! ### Main theorem -/

/-- Top-cylinder Theorem A smallness: given the uniform interior Morrey decay constant `C₂₇` of
`CIV.uniform_morrey_decay_of_top_gradient_small`, for every interior centre where the spatial
gradient's top-boundary integral is uniformly small up to a base scale `r₀`, there is a radius
`ρ ≤ r₀` at which the combined velocity, pressure and force integrand of the Theorem A smallness
condition is at most `ε₀ * ρ ^ 2` on the top-boundary cylinder based at that centre. The three
smallness thresholds are met by shrinking `ρ`; the top-boundary integral itself is reached from
the fixed-scale display on backward cylinders by continuity of the Lebesgue integral from below,
along an increasing sequence of base times approaching the top slice. -/
theorem top_cylinder_smallness_of_gradient_small (q : ℝ) (hq : 5 / 2 < q) (ε₀ : ℝ) (hε₀ : 0 < ε₀) :
    ∃ C₂₇ : ℝ, 0 < C₂₇ ∧
      ∀ (u : ParabolicPoint → Vec3) (Du : ParabolicPoint → Fin 3 → Vec3)
        (p : ParabolicPoint → ℝ) (f : ParabolicPoint → Vec3),
        IsSuitableWeakSolution (vec3Ball 0 1) (Ioo (-1) 0) q u Du p f →
        GlobalEnergyClass u Du p → ForceC2Bounded f →
        ∀ (x : Vec3) (r₀ : ℝ), 0 < r₀ → r₀ ≤ 1 → vec3Ball x r₀ ⊆ vec3Ball 0 1 →
        (∀ r : ℝ, 0 < r → r ≤ r₀ →
          (∫⁻ w in vec3Ball x r ×ˢ Ioo (-(r ^ 2)) 0,
            ENNReal.ofReal (spatialGradientSq u Du w)) ≤
            ENNReal.ofReal (iterationEpsilonStar C₂₇ ^ (2 : ℕ) / 4 * r)) →
        ∃ ρ : ℝ, 0 < ρ ∧ ρ ≤ r₀ ∧
          (∫⁻ z in vec3Ball x ρ ×ˢ Ioo (-(ρ ^ 2)) 0,
              ENNReal.ofReal (vec3EuclideanNorm (u z)) ^ (3 : ℝ) +
                ENNReal.ofReal |p z| ^ (3 / 2 : ℝ) +
                ENNReal.ofReal (ρ ^ (3 * q - 3)) *
                  ENNReal.ofReal (vec3EuclideanNorm (f z)) ^ q) ≤
            ENNReal.ofReal (ε₀ * ρ ^ 2) := by
  obtain ⟨C₂₇, hC₂₇, hur5⟩ := uniform_morrey_decay_of_top_gradient_small q hq
  refine ⟨C₂₇, hC₂₇, ?_⟩
  intro u Du p f hsol henergy hforce x r₀ hr₀pos hr₀le1 hballr0 hgrad
  obtain ⟨r₅, M₁, σ, hr₅pos, hM₁ge1, hσpos, hMorrey⟩ :=
    hur5 u Du p f hsol henergy hforce x r₀ hr₀pos hr₀le1 hballr0 hgrad
  obtain ⟨Mf, hMf0, hMbound⟩ := exists_bound_of_forceC2Bounded hforce
  have hqpos : (0 : ℝ) < q := by linarith only [hq]
  have hM₁nonneg : (0 : ℝ) ≤ M₁ := by linarith only [hM₁ge1]
  have hgCnonneg : 0 ≤ gagliardoConstant := by unfold gagliardoConstant; positivity
  have hCv0 : 0 ≤ (2 * gagliardoConstant * M₁) ^ 3 :=
    pow_nonneg (mul_nonneg (mul_nonneg (by norm_num) hgCnonneg) hM₁nonneg) 3
  have hCp0 : 0 ≤ M₁ ^ (3 / 2 : ℝ) := Real.rpow_nonneg hM₁nonneg _
  have hCf0 : 0 ≤ 4 * Real.pi / 3 * Mf ^ q := mul_nonneg (by positivity) (Real.rpow_nonneg hMf0 q)
  obtain ⟨ρv, hρvpos, hρvle1, hρv⟩ :=
    exists_rho_le_of_rpow_bound (C := (2 * gagliardoConstant * M₁) ^ 3) (B := ε₀ / 3) (e := 6 / 5)
      hCv0 (by positivity) (by norm_num)
  obtain ⟨ρp, hρppos, hρple1, hρp⟩ :=
    exists_rho_le_of_rpow_bound (C := M₁ ^ (3 / 2 : ℝ)) (B := ε₀ / 3) (e := 3 / 5)
      hCp0 (by positivity) (by norm_num)
  obtain ⟨ρf, hρfpos, hρfle1, hρf⟩ :=
    exists_rho_le_of_rpow_bound (C := 4 * Real.pi / 3 * Mf ^ q) (B := ε₀ / 3) (e := 3 * q)
      hCf0 (by positivity) (by positivity)
  set M : ℝ := min r₅ (min r₀ (min ρv (min ρp ρf))) with hMdef
  have hMpos : 0 < M := lt_min hr₅pos (lt_min hr₀pos (lt_min hρvpos (lt_min hρppos hρfpos)))
  have hMler5 : M ≤ r₅ := min_le_left _ _
  have hMler0 : M ≤ r₀ := (min_le_right _ _).trans (min_le_left _ _)
  have hMleρv : M ≤ ρv := (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
  have hMleρp : M ≤ ρp :=
    (min_le_right _ _).trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))
  have hMleρf : M ≤ ρf :=
    (min_le_right _ _).trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _
      _)))
  set ρ : ℝ := M / 4 with hρdef
  have hρpos : 0 < ρ := by rw [hρdef]; linarith only [hMpos]
  have hρler5 : ρ ≤ r₅ := by rw [hρdef]; linarith only [hMler5, hMpos]
  have hρler0quarter : ρ ≤ r₀ / 4 := by rw [hρdef]; linarith only [hMler0]
  have hρler0 : ρ ≤ r₀ := by linarith only [hρler0quarter, hr₀pos]
  have hρleρv : ρ ≤ ρv := by rw [hρdef]; linarith only [hMleρv, hMpos]
  have hρleρp : ρ ≤ ρp := by rw [hρdef]; linarith only [hMleρp, hMpos]
  have hρleρf : ρ ≤ ρf := by rw [hρdef]; linarith only [hMleρf, hMpos]
  have hρlequarter : ρ ≤ 1 / 4 := by linarith only [hρler0quarter, hr₀le1]
  have hv : ρ ^ 2 * (2 * gagliardoConstant * (M₁ * ρ ^ (2 / 5 : ℝ))) ^ 3 ≤ ε₀ / 3 * ρ ^ 2 :=
    velocity_smallness_of_rpow_bound hρpos
      ((rpow_mul_le_of_le hCv0 hρpos.le hρleρv (by norm_num)).trans hρv)
  have hpr : M₁ ^ (3 / 2 : ℝ) * ρ ^ (13 / 5 : ℝ) ≤ ε₀ / 3 * ρ ^ 2 :=
    pressure_smallness_of_rpow_bound hρpos
      ((rpow_mul_le_of_le hCp0 hρpos.le hρleρp (by norm_num)).trans hρp)
  have hf : 4 * Real.pi / 3 * Mf ^ q * ρ ^ (3 * q) ≤ ε₀ / 3 :=
    (rpow_mul_le_of_le (e := 3 * q) hCf0 hρpos.le hρleρf (by positivity)).trans hρf
  have h1minus4ρsqpos : 0 < 1 - 4 * ρ ^ 2 := by nlinarith only [hρlequarter, hρpos]
  set σ' : ℝ := min σ ((1 - 4 * ρ ^ 2) / 2) with hσ'def
  have hσ'pos : 0 < σ' := lt_min hσpos (by linarith only [h1minus4ρsqpos])
  have hσ'leσ : σ' ≤ σ := min_le_left _ _
  have hσ'lefrac : σ' ≤ (1 - 4 * ρ ^ 2) / 2 := min_le_right _ _
  have hbound : ∀ s ∈ Ioo (-σ') (0 : ℝ),
      (∫⁻ z in vec3Ball x ρ ×ˢ Ioo (-(ρ ^ 2)) s,
          ENNReal.ofReal (vec3EuclideanNorm (u z)) ^ (3 : ℝ) +
            ENNReal.ofReal |p z| ^ (3 / 2 : ℝ) +
            ENNReal.ofReal (ρ ^ (3 * q - 3)) * ENNReal.ofReal (vec3EuclideanNorm (f z)) ^ q) ≤
        ENNReal.ofReal (ε₀ * ρ ^ 2) := by
    intro s hs
    have hsneg : s < 0 := hs.2
    have hsσ' : -σ' < s := hs.1
    have hsσ : -σ < s := lt_of_le_of_lt (neg_le_neg hσ'leσ) hsσ'
    have hρsqle : ρ ^ 2 ≤ 1 / 16 := by
      have hh : ρ * ρ ≤ (1 / 4 : ℝ) * (1 / 4) := mul_le_mul hρlequarter hρlequarter hρpos.le
        (by norm_num)
      nlinarith only [hh]
    have hslow : -1 < s - (2 * ρ) ^ 2 := by
      have hexpand : (2 * ρ) ^ 2 = 4 * ρ ^ 2 := by ring
      rw [hexpand]
      linarith only [hsσ', hσ'lefrac, hρsqle]
    have hball2 : ∀ y : Vec3, vec3EuclideanNorm (y - x) ≤ 2 * ρ → vec3EuclideanNorm (y - 0) < 1
      := by
      intro y hy
      have hy' : vec3EuclideanNorm (y - x) < r₀ :=
        lt_of_le_of_lt hy (by linarith only [hρler0quarter, hr₀pos])
      have hymem : y ∈ vec3Ball x r₀ := hy'
      simpa using hballr0 hymem
    have hsub2 : closure (parabolicCylinder x s (2 * ρ)) ⊆
        spaceTimeSet (vec3Ball 0 1) (Ioo (-1) 0) :=
      CIV.closure_parabolicCylinder_subset_unitCylinder x s (2 * ρ) (by positivity) hsneg hslow
        hball2
    have hdec : max (max (alpha u (x, s) ρ) (beta u Du (x, s) ρ)) (delta p (x, s) ρ ^ 2) ≤
        M₁ * ρ ^ (2 / 5 : ℝ) := hMorrey s ⟨hsσ, hsneg⟩ ρ hρpos hρler5
    have hcombined := lintegral_combined_le_of_scale_small hsol henergy hMf0 hMbound hρpos hM₁ge1
      hqpos hε₀ hsub2 hdec hv hpr hf
    have hentrance : vec3Ball x ρ ×ˢ Ioo (-(ρ ^ 2)) s ⊆ parabolicCylinder x s ρ :=
      topSlice_subset_parabolicCylinder x s ρ hsneg.le
    exact (lintegral_mono_set hentrance).trans hcombined
  have hfinal := lintegral_topCylinder_le_of_forall_lt x ρ σ' hσ'pos
    (fun z => ENNReal.ofReal (vec3EuclideanNorm (u z)) ^ (3 : ℝ) +
      ENNReal.ofReal |p z| ^ (3 / 2 : ℝ) +
      ENNReal.ofReal (ρ ^ (3 * q - 3)) * ENNReal.ofReal (vec3EuclideanNorm (f z)) ^ q)
    (ENNReal.ofReal (ε₀ * ρ ^ 2)) hbound
  exact ⟨ρ, hρpos, hρler0, hfinal⟩

end CIV
