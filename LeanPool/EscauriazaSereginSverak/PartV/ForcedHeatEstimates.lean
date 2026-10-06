/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.EscauriazaSereginSverak.PartV.ForcedHeatNorms

/-!
# The zero-data forced heat estimates for smooth tensors

For a smooth compactly supported tensor `G` supported in positive times, the
forced heat response `Z = forcedHeat G` satisfies on every slab
`Q_τ = ℝ³ × (0,τ)`, with an absolute constant `C`:

* `‖Z(t)‖₂ ≤ C ‖G‖_{L²(Q_τ)}` for `0 ≤ t ≤ τ` and `‖∇Z‖_{L²(Q_τ)} ≤ C ‖G‖_{L²(Q_τ)}`;
* `‖Z(t)‖₃ ≤ C ‖G‖_{L^{5/2}(Q_τ)}` for `0 ≤ t ≤ τ` and
  `‖Z‖_{L⁵(Q_τ)} ≤ C ‖G‖_{L^{5/2}(Q_τ)}`;
* `‖Z‖_{L⁴(Q_τ)} ≤ C (‖G‖_{L^{5/2}(Q_τ)} + ‖G‖_{L²(Q_τ)})`.

These are the smooth-data forms of `eq:pv-stokes-energy`, `eq:pv-stokes-l5` and
`eq:pv-stokes-l4` in `lem:pv-stokes`, for the scalar heat reformulation with the
pressure folded into the tensor.
-/

public section

open CKN

open MeasureTheory Set Filter
open scoped ENNReal
open CKN.Foundation.Heat CKN.Foundation.Parabolic


noncomputable section

namespace ESS

/-- Real forms of the `L²` and `L^{5/2}` norms of a smooth compactly supported
tensor on a time window, and their comparison with the Frobenius integrals used
in the smooth-data estimates. -/
theorem tensor_window_norms {G : Fin 3 → Fin 3 → ParabolicPoint → ℝ}
    (hG : ∀ i j, ContDiff ℝ (⊤ : ℕ∞) (fun p : Vec3 × ℝ => G i j p))
    (hGc : ∀ i j, HasCompactSupport (fun p : Vec3 × ℝ => G i j p)) (τ : ℝ) :
    ∃ a₂ a₅₂ : ℝ, 0 ≤ a₂ ∧ 0 ≤ a₅₂ ∧
      eLpNorm (fun p : Vec3 × ℝ => fun i j => G i j p) (ENNReal.ofReal 2)
          ((volume : Measure Vec3).prod (volume.restrict (Ioc 0 τ))) = ENNReal.ofReal a₂ ∧
      eLpNorm (fun p : Vec3 × ℝ => fun i j => G i j p) (ENNReal.ofReal (5 / 2))
          ((volume : Measure Vec3).prod (volume.restrict (Ioc 0 τ))) = ENNReal.ofReal a₅₂ ∧
      ∫ p, ∑ i : Fin 3, ∑ j : Fin 3, (G i j p) ^ 2
          ∂((volume : Measure Vec3).prod (volume.restrict (Ioc 0 τ))) ≤ 9 * a₂ ^ 2 ∧
      (∫ p, (∑ i : Fin 3, ∑ j : Fin 3, (G i j p) ^ 2) ^ (5 / 4 : ℝ)
          ∂((volume : Measure Vec3).prod (volume.restrict (Ioc 0 τ)))) ^ (2 / 5 : ℝ) ≤
        3 * a₅₂ := by
  set μ := (volume : Measure Vec3).prod (volume.restrict (Ioc (0 : ℝ) τ))
  let Gv : Vec3 × ℝ → Fin 3 → Fin 3 → ℝ := fun p i j => G i j p
  have hGvc : Continuous Gv := continuous_pi fun i => continuous_pi fun j => (hG i j).continuous
  have hGvs : HasCompactSupport Gv := by
    have hsum := HasCompactSupport.finset_sum (s := Finset.univ)
      (f := fun (ij : Fin 3 × Fin 3) (p : Vec3 × ℝ) =>
        (Pi.single ij.1 (Pi.single ij.2 (G ij.1 ij.2 p)) : Fin 3 → Fin 3 → ℝ))
      fun ij _ => (hGc ij.1 ij.2).comp_left (g := fun y : ℝ =>
        (Pi.single ij.1 (Pi.single ij.2 y) : Fin 3 → Fin 3 → ℝ)) (by simp)
    convert hsum using 1
    funext p i j
    simp only [Finset.sum_apply, Gv]
    rw [Finset.sum_eq_single (i, j)]
    · simp
    · intro b _ hb
      by_cases hbi : b.1 = i
      · subst hbi
        have hbj : b.2 ≠ j := fun h => hb (Prod.ext rfl h)
        simp [hbj]
      · simp [Ne.symm hbi]
    · simp
  obtain ⟨hint2, heq2⟩ := eLpNorm_eq_ofReal_of_hasCompactSupport (μ := μ) hGvc hGvs
    (by norm_num : (0 : ℝ) < 2)
  obtain ⟨hint52, heq52⟩ := eLpNorm_eq_ofReal_of_hasCompactSupport (μ := μ) hGvc hGvs
    (by norm_num : (0 : ℝ) < 5 / 2)
  set I2 : ℝ := ∫ q, ‖Gv q‖ ^ (2 : ℝ) ∂μ
  set I52 : ℝ := ∫ q, ‖Gv q‖ ^ (5 / 2 : ℝ) ∂μ
  have hI2 : 0 ≤ I2 := integral_nonneg fun q => by positivity
  have hI52 : 0 ≤ I52 := integral_nonneg fun q => by positivity
  refine ⟨I2 ^ (1 / 2 : ℝ), I52 ^ (1 / (5 / 2) : ℝ), by positivity, by positivity, heq2, heq52,
    ?_, ?_⟩
  · have hpt (p : Vec3 × ℝ) : ∑ i : Fin 3, ∑ j : Fin 3, (G i j p) ^ 2 ≤
        9 * ‖Gv p‖ ^ (2 : ℝ) := by
      rw [Real.rpow_two]
      exact tensor_sum_sq_le (Gv p)
    have hS : Integrable (fun p => ∑ i : Fin 3, ∑ j : Fin 3, (G i j p) ^ 2) μ :=
      (hint2.const_mul 9).mono' (continuous_finsetSum _ fun i _ => continuous_finsetSum _
        fun j _ => (hG i j).continuous.pow 2).aestronglyMeasurable
        (Eventually.of_forall fun p => by
          rw [Real.norm_eq_abs, abs_of_nonneg (Finset.sum_nonneg fun i _ =>
            Finset.sum_nonneg fun j _ => sq_nonneg _)]
          exact hpt p)
    calc
      _ ≤ ∫ p, 9 * ‖Gv p‖ ^ (2 : ℝ) ∂μ := integral_mono hS (hint2.const_mul 9) hpt
      _ = 9 * (I2 ^ (1 / 2 : ℝ)) ^ 2 := by
        rw [integral_const_mul, ← Real.rpow_natCast, ← Real.rpow_mul hI2]
        norm_num
        simp only [I2, Real.rpow_two]
  · have hpt (p : Vec3 × ℝ) : (∑ i : Fin 3, ∑ j : Fin 3, (G i j p) ^ 2) ^ (5 / 4 : ℝ) ≤
        (9 : ℝ) ^ (5 / 4 : ℝ) * ‖Gv p‖ ^ (5 / 2 : ℝ) := by
      have h9 := tensor_sum_sq_le (Gv p)
      calc
        _ ≤ (9 * ‖Gv p‖ ^ 2) ^ (5 / 4 : ℝ) :=
          Real.rpow_le_rpow (Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ =>
            sq_nonneg _) h9 (by norm_num)
        _ = _ := by
          rw [Real.mul_rpow (by norm_num) (by positivity), ← Real.rpow_natCast,
            ← Real.rpow_mul (norm_nonneg _)]
          norm_num
    have hS : Integrable (fun p => (∑ i : Fin 3, ∑ j : Fin 3, (G i j p) ^ 2) ^ (5 / 4 : ℝ)) μ :=
      (hint52.const_mul _).mono' ((continuous_finsetSum _ fun i _ => continuous_finsetSum _
        fun j _ => (hG i j).continuous.pow 2).rpow_const
          fun _ => Or.inr (by norm_num)).aestronglyMeasurable
        (Eventually.of_forall fun p => by
          rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (Finset.sum_nonneg fun i _ =>
            Finset.sum_nonneg fun j _ => sq_nonneg _) _)]
          exact hpt p)
    have hB : ∫ p, (∑ i : Fin 3, ∑ j : Fin 3, (G i j p) ^ 2) ^ (5 / 4 : ℝ) ∂μ ≤
        (9 : ℝ) ^ (5 / 4 : ℝ) * I52 := by
      rw [← integral_const_mul]
      exact integral_mono hS (hint52.const_mul _) hpt
    have hB0 : 0 ≤ ∫ p, (∑ i : Fin 3, ∑ j : Fin 3, (G i j p) ^ 2) ^ (5 / 4 : ℝ) ∂μ :=
      integral_nonneg fun p => Real.rpow_nonneg (Finset.sum_nonneg fun i _ =>
        Finset.sum_nonneg fun j _ => sq_nonneg _) _
    calc
      _ ≤ ((9 : ℝ) ^ (5 / 4 : ℝ) * I52) ^ (2 / 5 : ℝ) := Real.rpow_le_rpow hB0 hB (by norm_num)
      _ = 3 * I52 ^ (1 / (5 / 2) : ℝ) := by
        rw [Real.mul_rpow (by positivity) hI52, ← Real.rpow_mul (by norm_num)]
        have h9 : (9 : ℝ) ^ (5 / 4 * (2 / 5) : ℝ) = 3 := by
          rw [show (5 / 4 * (2 / 5) : ℝ) = 1 / 2 by norm_num, ← Real.sqrt_eq_rpow,
            show (9 : ℝ) = 3 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
        rw [h9]
        norm_num

/-- The sup norm of a tensor is at most the square root of its sum of squares. -/
theorem tensor_norm_le_sqrt_sum_sq (T : Fin 3 → Fin 3 → ℝ) :
    ‖T‖ ≤ (∑ i : Fin 3, ∑ j : Fin 3, T i j ^ 2) ^ (1 / 2 : ℝ) := by
  have hS : 0 ≤ ∑ i : Fin 3, ∑ j : Fin 3, T i j ^ 2 :=
    Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => sq_nonneg _
  refine (pi_norm_le_iff_of_nonneg (Real.rpow_nonneg hS _)).2 fun i =>
    (pi_norm_le_iff_of_nonneg (Real.rpow_nonneg hS _)).2 fun j => ?_
  rw [Real.norm_eq_abs, ← Real.sqrt_eq_rpow]
  apply Real.abs_le_sqrt
  calc
    T i j ^ 2 ≤ ∑ j' : Fin 3, T i j' ^ 2 :=
      Finset.single_le_sum (f := fun j' => T i j' ^ 2) (fun j' _ => sq_nonneg _)
        (Finset.mem_univ j)
    _ ≤ ∑ i' : Fin 3, ∑ j' : Fin 3, T i' j' ^ 2 :=
      Finset.single_le_sum (f := fun i' => ∑ j' : Fin 3, T i' j' ^ 2)
        (fun i' _ => Finset.sum_nonneg fun j' _ => sq_nonneg _) (Finset.mem_univ i)

/-- An `L^r` bound from a pointwise bound by a square root: if `‖f‖ ≤ Q^{1/2}`
with `Q ≥ 0` and `Q^{r/2}` integrable, then `‖f‖_r ≤ (∫ Q^{r/2})^{1/r}`. -/
theorem eLpNorm_le_of_norm_le_sqrt {α E : Type*} [MeasurableSpace α] {μ : Measure α}
    [NormedAddCommGroup E] {f : α → E} {Q : α → ℝ} {r : ℝ} (hr : 0 < r)
    (hf : AEStronglyMeasurable f μ) (hQm : AEStronglyMeasurable Q μ) (hQ0 : ∀ a, 0 ≤ Q a)
    (hfQ : ∀ a, ‖f a‖ ≤ Q a ^ (1 / 2 : ℝ)) (hint : Integrable (fun a => Q a ^ (r / 2)) μ) :
    eLpNorm f (ENNReal.ofReal r) μ ≤ ENNReal.ofReal ((∫ a, Q a ^ (r / 2) ∂μ) ^ (1 / r)) := by
  have hpow (a : α) : (Q a ^ (1 / 2 : ℝ)) ^ r = Q a ^ (r / 2) := by
    rw [← Real.rpow_mul (hQ0 a)]
    ring_nf
  have hint' : Integrable (fun a => (Q a ^ (1 / 2 : ℝ)) ^ r) μ := by
    simp_rw [hpow]
    exact hint
  refine (eLpNorm_mono_real hf hfQ).trans (le_of_eq ?_)
  rw [eLpNorm_eq_ofReal_integral_rpow hr (hQm.aemeasurable.pow_const _).aestronglyMeasurable
    (fun a => Real.rpow_nonneg (hQ0 a) _) hint']
  simp_rw [hpow]

private theorem forcedHeat_square_root_bound {X a : ℝ}
    (hX : X ≤ 9 * a ^ 2) (ha : 0 ≤ a) : X ^ (1 / 2 : ℝ) ≤ 3 * a := by
  rw [← Real.sqrt_eq_rpow]
  calc
    Real.sqrt X ≤ Real.sqrt ((3 * a) ^ 2) := Real.sqrt_le_sqrt (by linarith only [hX])
    _ = 3 * a := Real.sqrt_sq (by positivity)

private theorem forcedHeat_constant_bounds {Kc K4 : ℝ}
    (hKc : 0 ≤ Kc) (hK4 : 0 ≤ K4) :
    let C : ℝ := 3 + 3 * Kc ^ (1 / 3 : ℝ) + 3 * Kc ^ (1 / 5 : ℝ) +
      3 * K4 ^ (1 / 4 : ℝ)
    3 ≤ C ∧ 3 * Kc ^ (1 / 3 : ℝ) ≤ C ∧
      3 * Kc ^ (1 / 5 : ℝ) ≤ C ∧ 3 * K4 ^ (1 / 4 : ℝ) ≤ C := by
  dsimp only
  have hthird : 0 ≤ 3 * Kc ^ (1 / 3 : ℝ) := by positivity
  have hfifth : 0 ≤ 3 * Kc ^ (1 / 5 : ℝ) := by positivity
  have hfourth : 0 ≤ 3 * K4 ^ (1 / 4 : ℝ) := by positivity
  exact ⟨by linarith only [hthird, hfifth, hfourth],
    by linarith only [hfifth, hfourth], by linarith only [hthird, hfourth],
    by linarith only [hthird, hfifth]⟩

private theorem forcedHeat_fourth_root_bound
    {I K4 E2 B a₂ a₅₂ C : ℝ}
    (hK4 : 0 ≤ K4) (hB0 : 0 ≤ B) (ha₂ : 0 ≤ a₂) (ha₅₂ : 0 ≤ a₅₂)
    (hE2 : E2 ≤ 9 * a₂ ^ 2) (hB25 : B ^ (2 / 5 : ℝ) ≤ 3 * a₅₂)
    (hI0 : 0 ≤ I) (hL4 : I ≤ K4 * E2 * B ^ (4 / 5 : ℝ))
    (hC4 : 3 * K4 ^ (1 / 4 : ℝ) ≤ C) :
    I ^ (1 / 4 : ℝ) ≤ C * (a₅₂ + a₂) := by
  have hB45 : B ^ (4 / 5 : ℝ) ≤ 9 * a₅₂ ^ 2 := by
    calc
      B ^ (4 / 5 : ℝ) = (B ^ (2 / 5 : ℝ)) ^ 2 := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul hB0]
        norm_num
      _ ≤ (3 * a₅₂) ^ 2 := pow_le_pow_left₀ (Real.rpow_nonneg hB0 _) hB25 2
      _ = 9 * a₅₂ ^ 2 := by ring
  have hprod : K4 * E2 * B ^ (4 / 5 : ℝ) ≤ 81 * K4 * (a₅₂ + a₂) ^ 4 := by
    have h1 : E2 * B ^ (4 / 5 : ℝ) ≤ (9 * a₂ ^ 2) * (9 * a₅₂ ^ 2) :=
      mul_le_mul hE2 hB45 (Real.rpow_nonneg hB0 _) (by positivity)
    have h2 : a₂ ^ 2 * a₅₂ ^ 2 ≤ (a₅₂ + a₂) ^ 4 := by
      have h3 : a₂ * a₅₂ ≤ (a₅₂ + a₂) ^ 2 := by nlinarith only [ha₂, ha₅₂]
      calc
        a₂ ^ 2 * a₅₂ ^ 2 = (a₂ * a₅₂) ^ 2 := by ring
        _ ≤ ((a₅₂ + a₂) ^ 2) ^ 2 :=
          pow_le_pow_left₀ (mul_nonneg ha₂ ha₅₂) h3 2
        _ = (a₅₂ + a₂) ^ 4 := by ring
    calc
      K4 * E2 * B ^ (4 / 5 : ℝ) = K4 * (E2 * B ^ (4 / 5 : ℝ)) := by ring
      _ ≤ K4 * ((9 * a₂ ^ 2) * (9 * a₅₂ ^ 2)) := mul_le_mul_of_nonneg_left h1 hK4
      _ = 81 * K4 * (a₂ ^ 2 * a₅₂ ^ 2) := by ring
      _ ≤ 81 * K4 * (a₅₂ + a₂) ^ 4 := mul_le_mul_of_nonneg_left h2 (by positivity)
  calc
    I ^ (1 / 4 : ℝ) ≤ (81 * K4 * (a₅₂ + a₂) ^ 4) ^ (1 / 4 : ℝ) :=
      Real.rpow_le_rpow hI0 (hL4.trans hprod) (by norm_num)
    _ = 3 * K4 ^ (1 / 4 : ℝ) * (a₅₂ + a₂) := by
      rw [Real.mul_rpow (by positivity) (by positivity),
        Real.mul_rpow (by norm_num) hK4, ← Real.rpow_natCast (a₅₂ + a₂) 4,
        ← Real.rpow_mul (by positivity)]
      have h81 : (81 : ℝ) ^ (1 / 4 : ℝ) = 3 := by
        rw [show (81 : ℝ) = 3 ^ (4 : ℝ) by norm_num, ← Real.rpow_mul (by norm_num)]
        norm_num
      rw [h81]
      norm_num
    _ ≤ C * (a₅₂ + a₂) := mul_le_mul_of_nonneg_right hC4 (by positivity)

/-- The zero-data forced heat estimates for smooth compactly supported tensors
supported in positive times, with an absolute constant: the smooth-data form of
`lem:pv-stokes` for the componentwise heat reformulation. -/
theorem forcedHeat_smooth_estimates :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ G : Fin 3 → Fin 3 → ParabolicPoint → ℝ,
      (∀ i j, ContDiff ℝ (⊤ : ℕ∞) (fun p : Vec3 × ℝ => G i j p)) →
      (∀ i j, HasCompactSupport (fun p : Vec3 × ℝ => G i j p)) →
      (∀ i j, tsupport (fun p : Vec3 × ℝ => G i j p) ⊆ {p | 0 < p.2}) →
      ∀ τ : ℝ, 0 < τ →
        (∀ t ∈ Icc 0 τ, eLpNorm (fun x : Vec3 => forcedHeat G (x, t)) 2 volume ≤
          ENNReal.ofReal C * eLpNorm (fun z => fun i j => G i j z) 2
            (volume.restrict (CKN.spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 τ)))) ∧
        eLpNorm (fun z => fun i j => CKN.spatialPartial (fun w => forcedHeat G w i) j z) 2
            (volume.restrict (CKN.spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 τ))) ≤
          ENNReal.ofReal C * eLpNorm (fun z => fun i j => G i j z) 2
            (volume.restrict (CKN.spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 τ))) ∧
        (∀ t ∈ Icc 0 τ, eLpNorm (fun x : Vec3 => forcedHeat G (x, t)) 3 volume ≤
          ENNReal.ofReal C * eLpNorm (fun z => fun i j => G i j z) (ENNReal.ofReal (5 / 2))
            (volume.restrict (CKN.spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 τ)))) ∧
        eLpNorm (forcedHeat G) 5
            (volume.restrict (CKN.spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 τ))) ≤
          ENNReal.ofReal C * eLpNorm (fun z => fun i j => G i j z) (ENNReal.ofReal (5 / 2))
            (volume.restrict (CKN.spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 τ))) ∧
        eLpNorm (forcedHeat G) 4
            (volume.restrict (CKN.spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 τ))) ≤
          ENNReal.ofReal C *
            (eLpNorm (fun z => fun i j => G i j z) (ENNReal.ofReal (5 / 2))
              (volume.restrict (CKN.spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 τ))) +
            eLpNorm (fun z => fun i j => G i j z) 2
              (volume.restrict (CKN.spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 τ)))) := by
  set Kc : ℝ := criticalResponseConstant
  set K4 : ℝ := responseL4Constant
  have hKc : 0 ≤ Kc := criticalResponseConstant_nonneg
  have hK4 : 0 ≤ K4 := responseL4Constant_nonneg
  refine ⟨3 + 3 * Kc ^ (1 / 3 : ℝ) + 3 * Kc ^ (1 / 5 : ℝ) + 3 * K4 ^ (1 / 4 : ℝ),
    by positivity, ?_⟩
  intro G hG hGc hGpos τ hτ
  set C : ℝ := 3 + 3 * Kc ^ (1 / 3 : ℝ) + 3 * Kc ^ (1 / 5 : ℝ) + 3 * K4 ^ (1 / 4 : ℝ) with hC
  set g : Fin 3 → Fin 3 → Vec3 × ℝ → ℝ := fun i j p => G i j p
  set μ := (volume : Measure Vec3).prod (volume.restrict (Ioc (0 : ℝ) τ))
  obtain ⟨a₂, a₅₂, ha₂, ha₅₂, hn2, hn52, hE2, hB⟩ := tensor_window_norms hG hGc τ
  have h2eq : (2 : ℝ≥0∞) = ENNReal.ofReal 2 := by norm_num
  have hGnorm2 : eLpNorm (fun z => fun i j => G i j z) 2
      (volume.restrict (CKN.spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 τ))) = ENNReal.ofReal a₂ := by
    rw [eLpNorm_spaceTimeSet_eq_window, h2eq]
    exact hn2
  have hGnorm52 : eLpNorm (fun z => fun i j => G i j z) (ENNReal.ofReal (5 / 2))
      (volume.restrict (CKN.spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 τ))) =
        ENNReal.ofReal a₅₂ := by
    rw [eLpNorm_spaceTimeSet_eq_window]
    exact hn52
  rw [hGnorm2, hGnorm52]
  have hfinal {X c a : ℝ} (hX : X ≤ c * a) (hc : c ≤ C) (ha : 0 ≤ a) :
      ENNReal.ofReal X ≤ ENNReal.ofReal C * ENNReal.ofReal a := by
    rw [← ENNReal.ofReal_mul (by positivity)]
    exact ENNReal.ofReal_le_ofReal (hX.trans (mul_le_mul_of_nonneg_right hc ha))
  -- the response and its basic facts
  have hZfun : forcedHeat G = fun z : ParabolicPoint => responseVec g z :=
    funext fun z => forcedHeat_eq_responseVec hG hGc z
  obtain ⟨M, hM, hq⟩ := response_sq_decay hG hGc
  have hT : ContDiff ℝ 1 (heatRegTest 1) := (heatRegTest_contDiff one_pos).of_le (by simp)
  obtain ⟨hZc, hGrc, _⟩ := response_continuity hG hGc hT
  let q : Vec3 × ℝ → ℝ := fun p => ∑ i : Fin 3, (responseVec g p i) ^ 2
  have hq0 (p : Vec3 × ℝ) : 0 ≤ q p := Finset.sum_nonneg fun i _ => sq_nonneg _
  have hqc : Continuous q := continuous_finsetSum _ fun i _ =>
    ((continuous_apply i).comp hZc).pow 2
  have hqM (p : Vec3 × ℝ) : q p ≤ M ^ 2 := by
    have hn := (hq p).1
    have hsq := vec3EuclideanNorm_sq (responseVec g p)
    nlinarith only [hn, hsq, vec3EuclideanNorm_nonneg (responseVec g p)]
  have hZq (p : Vec3 × ℝ) : ‖responseVec g p‖ ≤ q p ^ (1 / 2 : ℝ) :=
    norm_le_sqrt_sum_sq _
  set E2 : ℝ := ∫ p, ∑ i : Fin 3, ∑ j : Fin 3, (g i j p) ^ 2 ∂μ
  set B : ℝ := ∫ p, (∑ i : Fin 3, ∑ j : Fin 3, (g i j p) ^ 2) ^ (5 / 4 : ℝ) ∂μ
  have hE20 : 0 ≤ E2 := integral_nonneg fun p =>
    Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => sq_nonneg _
  have hB0 : 0 ≤ B := integral_nonneg fun p => Real.rpow_nonneg
    (Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => sq_nonneg _) _
  obtain ⟨hAint, hBint, _⟩ := response_sq_window_integrable hG hGc 0 τ
  have hconstantBounds := forcedHeat_constant_bounds hKc hK4
  have hC3 : (3 : ℝ) ≤ C := hconstantBounds.1
  -- slice quantities
  have hslice (t : ℝ) (ht : t ∈ Icc 0 τ) :
      Integrable (fun x : Vec3 => q (x, t)) ∧ ∫ x, q (x, t) ≤ E2 := by
    have hsc : Continuous (fun x : Vec3 => ((x, t) : Vec3 × ℝ)) :=
      continuous_id.prodMk continuous_const
    refine ⟨integrable_of_abs_le_decay_six' hM (hqc.comp hsc) fun x => ?_, ?_⟩
    · rw [abs_of_nonneg (hq0 _)]
      exact (hq (x, t)).2
    · have henergy := response_energy_le hG hGc hGpos ht.1
      have hwin := window_integral_mono ht.2 hBint fun p =>
        Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => sq_nonneg (g i j p)
      have hgrad0 : 0 ≤ ∫ p, ∑ i : Fin 3, ∑ j : Fin 3, (responseGrad g j p i) ^ 2
          ∂((volume : Measure Vec3).prod (volume.restrict (Ioc 0 t))) :=
        integral_nonneg fun p => Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ =>
          sq_nonneg _
      change ∫ x, ∑ i : Fin 3, (responseVec g (x, t) i) ^ 2 ≤ E2
      linarith only [henergy, hwin, hgrad0]
  have hB25 : B ^ (2 / 5 : ℝ) ≤ 3 * a₅₂ := hB
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · -- slice `L²`
    intro t ht
    obtain ⟨hqint, hqle⟩ := hslice t ht
    have hsc : Continuous (fun x : Vec3 => ((x, t) : Vec3 × ℝ)) :=
      continuous_id.prodMk continuous_const
    have hbound := eLpNorm_le_of_norm_le_sqrt (μ := volume) (r := 2) (by norm_num)
      (f := fun x : Vec3 => responseVec g (x, t)) (Q := fun x => q (x, t))
      (hZc.comp hsc).aestronglyMeasurable (hqc.comp hsc).aestronglyMeasurable
      (fun x => hq0 _) (fun x => hZq _) (by
        simp_rw [show (2 : ℝ) / 2 = 1 by norm_num, Real.rpow_one]
        exact hqint)
    simp_rw [show (2 : ℝ) / 2 = 1 by norm_num, Real.rpow_one] at hbound
    rw [hZfun, h2eq]
    refine hbound.trans (hfinal ?_ hC3 ha₂)
    exact forcedHeat_square_root_bound (hqle.trans hE2) ha₂
  · -- gradient `L²`
    rw [eLpNorm_spaceTimeSet_eq_window, h2eq]
    have hfun : (fun q : Vec3 × ℝ => fun i j =>
        CKN.spatialPartial (fun w => forcedHeat G w i) j q) =
        fun q => fun i j => responseGrad g j q i := by
      funext q i j
      exact spatialPartial_forcedHeat_eq hG hGc i j q
    rw [hfun]
    let S : Vec3 × ℝ → ℝ := fun p => ∑ i : Fin 3, ∑ j : Fin 3, (responseGrad g j p i) ^ 2
    have hS0 (p : Vec3 × ℝ) : 0 ≤ S p :=
      Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => sq_nonneg _
    have hTc : Continuous (fun q : Vec3 × ℝ => fun i j => responseGrad g j q i) :=
      continuous_pi fun i => continuous_pi fun j => (continuous_apply i).comp (hGrc j)
    have hbound := eLpNorm_le_of_norm_le_sqrt (μ := μ) (r := 2) (by norm_num)
      (f := fun q : Vec3 × ℝ => fun i j => responseGrad g j q i) (Q := S)
      hTc.aestronglyMeasurable hAint.aestronglyMeasurable hS0
      (fun p => tensor_norm_le_sqrt_sum_sq _) (by
        simp_rw [show (2 : ℝ) / 2 = 1 by norm_num, Real.rpow_one]
        exact hAint)
    simp_rw [show (2 : ℝ) / 2 = 1 by norm_num, Real.rpow_one] at hbound
    refine hbound.trans (hfinal ?_ hC3 ha₂)
    have henergy := response_energy_le hG hGc hGpos hτ.le
    have hL20 : 0 ≤ ∫ x, ∑ i : Fin 3, (responseVec g (x, τ) i) ^ 2 :=
      integral_nonneg fun x => Finset.sum_nonneg fun i _ => sq_nonneg _
    have hSle : ∫ p, S p ∂μ ≤ E2 := by linarith only [henergy, hL20]
    exact forcedHeat_square_root_bound (hSle.trans hE2) ha₂
  · -- slice `L³`
    intro t ht
    obtain ⟨hqint, _⟩ := hslice t ht
    have hsc : Continuous (fun x : Vec3 => ((x, t) : Vec3 × ℝ)) :=
      continuous_id.prodMk continuous_const
    have hq32 (x : Vec3) : q (x, t) ^ (3 / 2 : ℝ) ≤ (M ^ 2) ^ (1 / 2 : ℝ) * q (x, t) := by
      calc
        q (x, t) ^ (3 / 2 : ℝ) = q (x, t) ^ (1 / 2 : ℝ) * q (x, t) ^ (1 : ℝ) := by
          rw [← Real.rpow_add' (hq0 _) (by norm_num)]
          norm_num
        _ ≤ (M ^ 2) ^ (1 / 2 : ℝ) * q (x, t) := by
          rw [Real.rpow_one]
          exact mul_le_mul_of_nonneg_right
            (Real.rpow_le_rpow (hq0 _) (hqM _) (by norm_num)) (hq0 _)
    have hq32int : Integrable (fun x : Vec3 => q (x, t) ^ (3 / 2 : ℝ)) :=
      (hqint.const_mul _).mono' ((hqc.comp hsc).rpow_const
        fun _ => Or.inr (by norm_num)).aestronglyMeasurable
        (Eventually.of_forall fun x => by
          rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (hq0 _) _)]
          exact hq32 x)
    have hbound := eLpNorm_le_of_norm_le_sqrt (μ := volume) (r := 3) (by norm_num)
      (f := fun x : Vec3 => responseVec g (x, t)) (Q := fun x => q (x, t))
      (hZc.comp hsc).aestronglyMeasurable (hqc.comp hsc).aestronglyMeasurable
      (fun x => hq0 _) (fun x => hZq _) hq32int
    rw [hZfun, show (3 : ℝ≥0∞) = ENNReal.ofReal 3 by norm_num]
    refine hbound.trans (hfinal (c := 3 * Kc ^ (1 / 3 : ℝ)) ?_ ?_ ha₅₂)
    · have hcrit := (response_critical_estimate hG hGc hGpos hτ.le).2 t ht
      have hI0 : 0 ≤ ∫ x, q (x, t) ^ (3 / 2 : ℝ) := integral_nonneg fun x =>
        Real.rpow_nonneg (hq0 _) _
      calc
        (∫ x, q (x, t) ^ (3 / 2 : ℝ)) ^ (1 / 3 : ℝ) ≤ (Kc * B ^ (6 / 5 : ℝ)) ^ (1 / 3 : ℝ) :=
          Real.rpow_le_rpow hI0 hcrit (by norm_num)
        _ = Kc ^ (1 / 3 : ℝ) * B ^ (2 / 5 : ℝ) := by
          rw [Real.mul_rpow hKc (by positivity), ← Real.rpow_mul hB0]
          norm_num
        _ ≤ Kc ^ (1 / 3 : ℝ) * (3 * a₅₂) := mul_le_mul_of_nonneg_left hB25 (by positivity)
        _ = 3 * Kc ^ (1 / 3 : ℝ) * a₅₂ := by ring
    · exact hconstantBounds.2.1
  · -- space-time `L⁵`
    obtain ⟨h5int, _⟩ := response_rpow_five_le hG hGc hGpos hτ.le
    rw [eLpNorm_spaceTimeSet_eq_window, show (5 : ℝ≥0∞) = ENNReal.ofReal 5 by norm_num]
    change eLpNorm (fun p : Vec3 × ℝ => forcedHeat G p) (ENNReal.ofReal 5) μ ≤ _
    simp_rw [hZfun]
    have hbound := eLpNorm_le_of_norm_le_sqrt (μ := μ) (r := 5) (by norm_num)
      (f := fun p : Vec3 × ℝ => responseVec g p) (Q := q)
      hZc.aestronglyMeasurable hqc.aestronglyMeasurable hq0 hZq h5int
    refine hbound.trans (hfinal (c := 3 * Kc ^ (1 / 5 : ℝ)) ?_ ?_ ha₅₂)
    · have hcrit := (response_critical_estimate hG hGc hGpos hτ.le).1
      have hI0 : 0 ≤ ∫ p, q p ^ (5 / 2 : ℝ) ∂μ := integral_nonneg fun p =>
        Real.rpow_nonneg (hq0 _) _
      calc
        (∫ p, q p ^ (5 / 2 : ℝ) ∂μ) ^ (1 / 5 : ℝ) ≤ (Kc * B ^ 2) ^ (1 / 5 : ℝ) :=
          Real.rpow_le_rpow hI0 hcrit (by norm_num)
        _ = Kc ^ (1 / 5 : ℝ) * B ^ (2 / 5 : ℝ) := by
          rw [Real.mul_rpow hKc (by positivity), ← Real.rpow_natCast, ← Real.rpow_mul hB0]
          norm_num
        _ ≤ Kc ^ (1 / 5 : ℝ) * (3 * a₅₂) := mul_le_mul_of_nonneg_left hB25 (by positivity)
        _ = 3 * Kc ^ (1 / 5 : ℝ) * a₅₂ := by ring
    · exact hconstantBounds.2.2.1
  · -- space-time `L⁴`
    rw [eLpNorm_spaceTimeSet_eq_window, show (4 : ℝ≥0∞) = ENNReal.ofReal 4 by norm_num]
    change eLpNorm (fun p : Vec3 × ℝ => forcedHeat G p) (ENNReal.ofReal 4) μ ≤ _
    simp_rw [hZfun]
    have hq2 (p : Vec3 × ℝ) : q p ^ (4 / 2 : ℝ) = q p ^ 2 := by
      rw [show (4 : ℝ) / 2 = (2 : ℕ) by norm_num, Real.rpow_natCast]
    have hq2int : Integrable (fun p => q p ^ (4 / 2 : ℝ)) μ := by
      simp_rw [hq2]
      refine integrable_window_of_decay (C := M ^ 2 * M) (hqc.pow 2) (by positivity)
        fun x t _ => ?_
      rw [abs_of_nonneg (sq_nonneg _), sq]
      calc
        q (x, t) * q (x, t) ≤ M ^ 2 * (M / (1 + vec3EuclideanNorm x) ^ 6) :=
          mul_le_mul (hqM _) (hq (x, t)).2 (hq0 _) (by positivity)
        _ = _ := by ring
    have hbound := eLpNorm_le_of_norm_le_sqrt (μ := μ) (r := 4) (by norm_num)
      (f := fun p : Vec3 × ℝ => responseVec g p) (Q := q)
      hZc.aestronglyMeasurable hqc.aestronglyMeasurable hq0 hZq hq2int
    simp_rw [hq2] at hbound
    refine hbound.trans ?_
    rw [← ENNReal.ofReal_add ha₅₂ ha₂, ← ENNReal.ofReal_mul (by positivity)]
    apply ENNReal.ofReal_le_ofReal
    have hL4 := response_L4_estimate hG hGc hGpos hτ.le
    change ∫ p, q p ^ 2 ∂μ ≤ K4 * E2 * B ^ (4 / 5 : ℝ) at hL4
    have hI0 : 0 ≤ ∫ p, q p ^ 2 ∂μ := integral_nonneg fun p => sq_nonneg _
    have hC4 : 3 * K4 ^ (1 / 4 : ℝ) ≤ C := hconstantBounds.2.2.2
    exact forcedHeat_fourth_root_bound hK4 hB0 ha₂ ha₅₂ hE2 hB25 hI0 hL4 hC4



end ESS

end
