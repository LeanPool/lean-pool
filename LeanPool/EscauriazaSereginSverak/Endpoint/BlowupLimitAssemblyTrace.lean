/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.EscauriazaSereginSverak.Endpoint.VorticityTopTrace
public import LeanPool.EscauriazaSereginSverak.Endpoint.BlowupLimitAssemblyModulus
public import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp
public import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-!
# The terminal slice of the blow-up limit

The pairing modulus of `prop:blowup-limit` is uniform up to time zero and the
rescaled terminal slices vanish in local L². Together with the
convergence of every negative-time slice this gives the zero distributional
terminal trace of the limit (the terminal-slice step).
-/

public section


open MeasureTheory Set Filter
open scoped ENNReal
open CKN CKN.Foundation.Parabolic

noncomputable section

namespace ESS

/-- Fields vanishing in L² on every unit ball have vanishing pairings with
every compactly supported continuous test. -/
theorem blowupLimitAssembly_pairing_tendsto_zero_of_unit_balls
    (g : ℕ → Vec3 → Vec3) (hg : ∀ k, AEStronglyMeasurable (g k) volume)
    (hloc : ∀ c : Vec3, Tendsto (fun k => eLpNorm (g k) 2
      (volume.restrict (vec3Ball c 1))) atTop (nhds 0))
    (ψ : Vec3 → Vec3) (hψ : Continuous ψ) (hψc : HasCompactSupport ψ) :
    Tendsto (fun k => ∫ x, ∑ i : Fin 3, g k x i * ψ x i) atTop (nhds 0) := by
  set K : Set Vec3 := tsupport ψ
  have hK : IsCompact K := hψc
  obtain ⟨S, -, hS⟩ := hK.elim_nhds_subcover (fun c => vec3Ball c 1)
    (fun c _ => (isOpen_vec3Ball c 1).mem_nhds (by
      rw [mem_vec3Ball, sub_self, vec3EuclideanNorm_zero]
      norm_num))
  obtain ⟨Cψ, hCψ⟩ := hψc.exists_bound_of_continuous hψ
  set C : ℝ := max Cψ 0
  have hC : 0 ≤ C := le_max_right _ _
  have hψle : ∀ x i, |ψ x i| ≤ C := fun x i =>
    ((norm_le_pi_norm (ψ x) i).trans (hCψ x)).trans (le_max_left _ _)
  have hball : ∀ c : Vec3, volume (vec3Ball c 1) < ⊤ := fun c =>
    lt_of_le_of_lt (measure_mono subset_closure)
      (measure_closure_vec3Ball_lt_top (by norm_num))
  -- the majorant
  let b : ℕ → ℝ≥0∞ := fun k => ENNReal.ofReal (3 * C) *
    ∑ c ∈ S, eLpNorm (g k) 2 (volume.restrict (vec3Ball c 1)) *
      (volume (vec3Ball c 1)) ^ (1 / 2 : ℝ)
  have hb : Tendsto b atTop (nhds 0) := by
    have hsum : Tendsto (fun k => ∑ c ∈ S, eLpNorm (g k) 2
        (volume.restrict (vec3Ball c 1)) * (volume (vec3Ball c 1)) ^ (1 / 2 : ℝ))
        atTop (nhds 0) := by
      have h := tendsto_finsetSum S (fun c _ =>
        ENNReal.Tendsto.mul_const (hloc c)
          (Or.inr (ENNReal.rpow_lt_top_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2)
            (hball c).ne).ne))
      simp only [zero_mul, Finset.sum_const_zero] at h
      exact h
    have h := ENNReal.Tendsto.const_mul (a := ENNReal.ofReal (3 * C)) hsum
      (Or.inr ENNReal.ofReal_ne_top)
    rw [mul_zero] at h
    exact h
  have hpoint : ∀ k x, ‖∑ i : Fin 3, g k x i * ψ x i‖ₑ ≤
      K.indicator (fun x => ENNReal.ofReal (3 * C) * ‖g k x‖ₑ) x := by
    intro k x
    by_cases hx : x ∈ K
    · rw [indicator_of_mem hx]
      rw [← ofReal_norm, ← ofReal_norm, ← ENNReal.ofReal_mul (by positivity)]
      apply ENNReal.ofReal_le_ofReal
      rw [Real.norm_eq_abs]
      calc
        |∑ i : Fin 3, g k x i * ψ x i| ≤ ∑ i : Fin 3, |g k x i * ψ x i| :=
          Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ _i : Fin 3, ‖g k x‖ * C := by
          apply Finset.sum_le_sum
          intro i _
          rw [abs_mul]
          exact mul_le_mul ((Real.norm_eq_abs _).symm.le.trans (norm_le_pi_norm _ i))
            (hψle x i) (abs_nonneg _) (norm_nonneg _)
        _ = 3 * C * ‖g k x‖ := by
          simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
            nsmul_eq_mul]
          ring
    · have hψ0 : ψ x = 0 := image_eq_zero_of_notMem_tsupport hx
      simp [hψ0]
  have hbound : ∀ k, ‖∫ x, ∑ i : Fin 3, g k x i * ψ x i‖ₑ ≤ b k := by
    intro k
    calc
      ‖∫ x, ∑ i : Fin 3, g k x i * ψ x i‖ₑ ≤ ∫⁻ x, ‖∑ i : Fin 3, g k x i * ψ x i‖ₑ :=
        enorm_integral_le_lintegral_enorm _
      _ ≤ ∫⁻ x, K.indicator (fun x => ENNReal.ofReal (3 * C) * ‖g k x‖ₑ) x :=
        lintegral_mono (hpoint k)
      _ = ∫⁻ x in K, ENNReal.ofReal (3 * C) * ‖g k x‖ₑ :=
        lintegral_indicator hK.measurableSet _
      _ ≤ ∫⁻ x in ⋃ c : S, vec3Ball (c : Vec3) 1,
            ENNReal.ofReal (3 * C) * ‖g k x‖ₑ := by
        apply lintegral_mono_set
        intro x hx
        obtain ⟨c, hc, hxc⟩ := mem_iUnion₂.1 (hS hx)
        exact mem_iUnion.2 ⟨⟨c, hc⟩, hxc⟩
      _ ≤ ∑' c : S, ∫⁻ x in vec3Ball (c : Vec3) 1,
            ENNReal.ofReal (3 * C) * ‖g k x‖ₑ :=
        lintegral_iUnion_le _ _
      _ = ∑ c ∈ S, ∫⁻ x in vec3Ball c 1, ENNReal.ofReal (3 * C) * ‖g k x‖ₑ := by
        rw [tsum_fintype]
        exact Finset.sum_coe_sort S
          (fun c => ∫⁻ x in vec3Ball c 1, ENNReal.ofReal (3 * C) * ‖g k x‖ₑ)
      _ ≤ b k := by
        simp only [b, Finset.mul_sum]
        apply Finset.sum_le_sum
        intro c _
        rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
        refine mul_le_mul_of_nonneg_left ?_ zero_le
        calc
          (∫⁻ x in vec3Ball c 1, ‖g k x‖ₑ) =
              eLpNorm (g k) 1 (volume.restrict (vec3Ball c 1)) :=
            (eLpNorm_one_eq_lintegral_enorm (hg k).restrict).symm
          _ ≤ eLpNorm (g k) 2 (volume.restrict (vec3Ball c 1)) *
                (volume.restrict (vec3Ball c 1)) univ ^
                  (1 / (1 : ℝ≥0∞).toReal - 1 / (2 : ℝ≥0∞).toReal) :=
            eLpNorm_le_eLpNorm_mul_rpow_measure_univ (by norm_num) (hg k).restrict
          _ = eLpNorm (g k) 2 (volume.restrict (vec3Ball c 1)) *
                (volume (vec3Ball c 1)) ^ (1 / 2 : ℝ) := by
            rw [Measure.restrict_apply_univ]
            norm_num
  have hreal : Tendsto (fun k => (b k).toReal) atTop (nhds 0) := by
    have h := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp hb
    rw [ENNReal.toReal_zero] at h
    exact h
  apply squeeze_zero_norm' _ hreal
  have hfin : ∀ᶠ k in atTop, b k < ⊤ :=
    hb.eventually (gt_mem_nhds ENNReal.zero_lt_top)
  filter_upwards [hfin] with k hk
  have := hbound k
  rw [← ofReal_norm] at this
  exact (ENNReal.ofReal_le_iff_le_toReal hk.ne).1 this

/-- Convergence of every negative-time slice pairing, a uniform modulus up
to time zero, and vanishing terminal pairings give a zero distributional
terminal trace. -/
theorem blowupLimitAssembly_zero_trace
    (U : ParabolicPoint → Vec3) (V : ℕ → ParabolicPoint → Vec3)
    (hslices : ∀ t : ℝ, t < 0 → ∀ ψ : Vec3 → Vec3, ContDiff ℝ (⊤ : ℕ∞) ψ →
      HasCompactSupport ψ →
      Integrable (fun x => ∑ i : Fin 3, U (x,t) i * ψ x i) ∧
      Tendsto (fun k => ∫ x : Vec3, ∑ i : Fin 3, V k (x,t) i * ψ x i)
        atTop (nhds (∫ x : Vec3, ∑ i : Fin 3, U (x,t) i * ψ x i)))
    (hmod : ∀ ψ : Vec3 → Vec3, ContDiff ℝ (⊤ : ℕ∞) ψ → HasCompactSupport ψ →
      ∃ A B θ : ℝ, 0 ≤ A ∧ 0 ≤ B ∧ 0 < θ ∧ ∀ᶠ k in atTop,
        ∀ s t, s ∈ Icc (-1 : ℝ) 0 → t ∈ Icc (-1 : ℝ) 0 →
          |(∫ x : Vec3, ∑ i : Fin 3, V k (x,t) i * ψ x i) -
            (∫ x : Vec3, ∑ i : Fin 3, V k (x,s) i * ψ x i)| ≤
            A * dist t s + B * (dist t s) ^ θ)
    (hterm : ∀ ψ : Vec3 → Vec3, ContDiff ℝ (⊤ : ℕ∞) ψ → HasCompactSupport ψ →
      Tendsto (fun k => ∫ x : Vec3, ∑ i : Fin 3, V k (x,0) i * ψ x i)
        atTop (nhds 0)) :
    HasZeroDistributionalVelocityTrace U := by
  intro ψ hψ hψc
  refine ⟨fun t ht => (hslices t ht ψ hψ hψc).1, ?_⟩
  obtain ⟨A, B, θ, hA, hB, hθ, hmodψ⟩ := hmod ψ hψ hψc
  let G : ℝ → ℝ := fun t => ∫ x : Vec3, ∑ i : Fin 3, U (x,t) i * ψ x i
  have hupper : ∀ t ∈ Ioo (-1 : ℝ) 0, |G t| ≤ A * dist t 0 + B * (dist t 0) ^ θ := by
    intro t ht
    have hlim : Tendsto (fun k =>
        (∫ x : Vec3, ∑ i : Fin 3, V k (x,t) i * ψ x i) -
          ∫ x : Vec3, ∑ i : Fin 3, V k (x,0) i * ψ x i) atTop (nhds (G t)) := by
      simpa using (hslices t ht.2 ψ hψ hψc).2.sub (hterm ψ hψ hψc)
    have habs := (continuous_abs.tendsto _).comp hlim
    apply le_of_tendsto habs
    filter_upwards [hmodψ] with k hk
    exact hk 0 t ⟨by norm_num, le_rfl⟩ ⟨ht.1.le, ht.2.le⟩
  have hdist : Tendsto (fun t : ℝ => dist t 0) (nhdsWithin 0 (Iio 0)) (nhds 0) := by
    have h := ((continuous_id.dist
      (continuous_const : Continuous fun _ : ℝ => (0 : ℝ))).tendsto (0 : ℝ)).mono_left
      (nhdsWithin_le_nhds (s := Iio (0 : ℝ)))
    simp only [id, dist_self] at h
    exact h
  have hmaj : Tendsto (fun t : ℝ => A * dist t 0 + B * (dist t 0) ^ θ)
      (nhdsWithin 0 (Iio 0)) (nhds 0) := by
    have hpow : Tendsto (fun t : ℝ => (dist t 0) ^ θ) (nhdsWithin 0 (Iio 0)) (nhds 0) := by
      have h := (Real.continuousAt_rpow_const 0 θ (Or.inr hθ.le)).tendsto.comp hdist
      rw [Real.zero_rpow hθ.ne'] at h
      exact h
    simpa using (hdist.const_mul A).add (hpow.const_mul B)
  have hev : ∀ᶠ t in nhdsWithin 0 (Iio 0), t ∈ Ioo (-1 : ℝ) 0 := by
    filter_upwards [(eventually_gt_nhds (by norm_num : (-1 : ℝ) < 0)).filter_mono
      nhdsWithin_le_nhds, self_mem_nhdsWithin] with t h1 h2
    exact ⟨h1, h2⟩
  apply squeeze_zero_norm' _ hmaj
  filter_upwards [hev] with t ht
  rw [Real.norm_eq_abs]
  exact hupper t ht

end ESS

end
