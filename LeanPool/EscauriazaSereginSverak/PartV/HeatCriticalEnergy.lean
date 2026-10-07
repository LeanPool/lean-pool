/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.EscauriazaSereginSverak.PartV.HeatCriticalSmooth
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.DerivIntegrable

/-!
# The quadratic heat energy for smooth compact data

For smooth compactly supported data the Gaussian heat orbit satisfies the
energy identity `d/dt ∫ |h|² = -2 ∫ |∇h|²`.  Integrating it in time gives the
energy bounds used for the `L^{10/3}` part of `lem:pv-heat-critical`.
-/

public section

open MeasureTheory Filter Set
open scoped ENNReal
open CKN CKN.Foundation.Parabolic CKN.Foundation.Heat


noncomputable section

namespace ESS

private theorem heat_one_le_weight (x : Vec3) : 1 ≤ 1 + vec3EuclideanNorm x := by
  linarith only [vec3EuclideanNorm_nonneg x]

private theorem heat_weight_pos (x : Vec3) : 0 < 1 + vec3EuclideanNorm x := by
  have hn := vec3EuclideanNorm_nonneg x
  positivity

private theorem heat_cubic_mul_cubic_le {a c A B : ℝ} {x : Vec3}
    (ha : |a| ≤ A / (1 + vec3EuclideanNorm x) ^ 3)
    (hc : |c| ≤ B / (1 + vec3EuclideanNorm x) ^ 3) :
    |a * c| ≤ A * B / (1 + vec3EuclideanNorm x) ^ 6 := by
  rw [abs_mul]
  have hA : 0 ≤ A / (1 + vec3EuclideanNorm x) ^ 3 := (abs_nonneg a).trans ha
  calc
    |a| * |c| ≤ (A / (1 + vec3EuclideanNorm x) ^ 3) *
        (B / (1 + vec3EuclideanNorm x) ^ 3) :=
      mul_le_mul ha hc (abs_nonneg c) hA
    _ = A * B / (1 + vec3EuclideanNorm x) ^ 6 := by
      rw [div_mul_div_comm, ← pow_add]

private theorem heat_cubic_product_integrable {f g : Vec3 → ℝ}
    (hf : Continuous f) (hg : Continuous g) {A B : ℝ}
    (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hfdecay : ∀ x, |f x| ≤ A / (1 + vec3EuclideanNorm x) ^ 3)
    (hgdecay : ∀ x, |g x| ≤ B / (1 + vec3EuclideanNorm x) ^ 3) :
    Integrable (fun x => f x * g x) volume :=
  heat_integrable_of_decay_six (hf.mul hg) (mul_nonneg hA hB)
    (fun x => heat_cubic_mul_cubic_le (hfdecay x) (hgdecay x))

private theorem heatConvVec3_profile_contDiff {b : Vec3 → Vec3}
    (hb : ∀ i : Fin 3, ContDiff ℝ (⊤ : ℕ∞) (fun x => b x i))
    (hbc : ∀ i : Fin 3, HasCompactSupport (fun x => b x i))
    {t : ℝ} (ht : 0 < t) (i : Fin 3) :
    ContDiff ℝ (⊤ : ℕ∞) (fun x => heatConvVec3 t b x i) := by
  simpa [heatConvVec3] using heatConv_smooth_input (hb i) (hbc i) ht

private theorem heatConvVec3_component_decay {b : Vec3 → Vec3}
    (hb : ∀ i : Fin 3, ContDiff ℝ (⊤ : ℕ∞) (fun x => b x i))
    (hbc : ∀ i : Fin 3, HasCompactSupport (fun x => b x i)) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ {t : ℝ}, 0 < t → ∀ x i,
      |heatConvVec3 t b x i| ≤ M / (1 + vec3EuclideanNorm x) ^ 3 := by
  obtain ⟨M, hM, htail⟩ := heatConvVec3_norm_decay hb hbc
  exact ⟨M, hM, fun ht x i =>
    (abs_apply_le_vec3EuclideanNorm _ i).trans (htail ht x)⟩

/-- The quadratic energy of a smooth compact vector heat orbit differentiates
in time with the heat-equation derivative, as used in `lem:pv-heat-critical`. -/
theorem heatConvVec3_sq_integral_hasDerivAt {b : Vec3 → Vec3}
    (hb : ∀ i : Fin 3, ContDiff ℝ (⊤ : ℕ∞) (fun x => b x i))
    (hbc : ∀ i : Fin 3, HasCompactSupport (fun x => b x i))
    {t : ℝ} (ht : 0 < t) :
    HasDerivAt (fun s : ℝ => ∫ x : Vec3, ∑ i : Fin 3, (heatConvVec3 s b x i) ^ 2)
      (∫ x : Vec3, ∑ i : Fin 3, 2 * heatConvVec3 t b x i *
        heatConv t (CKN.spatialLaplacian (fun y => b y i)) x) t := by
  let bLap : Vec3 → Vec3 := fun x i => CKN.spatialLaplacian (fun y => b y i) x
  have hbLap (i : Fin 3) : ContDiff ℝ (⊤ : ℕ∞) (fun x => bLap x i) :=
    CKN.contDiff_spatialLaplacian_smooth (hb i)
  have hbcLap (i : Fin 3) : HasCompactSupport (fun x => bLap x i) :=
    CKN.hasCompactSupport_spatialLaplacian (hbc i)
  obtain ⟨M, hM, hMtail⟩ := heatConvVec3_component_decay hb hbc
  obtain ⟨N, hN, hNtail⟩ := heatConvVec3_component_decay hbLap hbcLap
  let S : Set ℝ := Ioo (t / 2) (2 * t)
  have hS : S ∈ nhds t := by
    have hmem : t ∈ Ioo (t / 2) (2 * t) := by
      constructor <;> linarith only [ht]
    exact isOpen_Ioo.mem_nhds hmem
  have hSpos {s : ℝ} (hs : s ∈ S) : 0 < s := by
    have h1 := hs.1
    linarith only [h1, ht]
  let F : ℝ → Vec3 → ℝ := fun s x => ∑ i : Fin 3, (heatConvVec3 s b x i) ^ 2
  let F' : ℝ → Vec3 → ℝ := fun s x => ∑ i : Fin 3,
    2 * heatConvVec3 s b x i * heatConvVec3 s bLap x i
  have hFcont {s : ℝ} (hs : 0 < s) : Continuous (F s) := by
    have hc (i : Fin 3) := (heatConvVec3_profile_contDiff hb hbc hs i).continuous
    exact continuous_finsetSum _ fun i _ => (hc i).pow 2
  have hF'cont : Continuous (F' t) := by
    have hc (i : Fin 3) := (heatConvVec3_profile_contDiff hb hbc ht i).continuous
    have hd (i : Fin 3) :=
      (heatConvVec3_profile_contDiff hbLap hbcLap ht i).continuous
    exact continuous_finsetSum _ fun i _ =>
      (continuous_const.mul (hc i)).mul (hd i)
  have hFmeas : ∀ᶠ s in nhds t, AEStronglyMeasurable (F s) volume := by
    filter_upwards [hS] with s hs
    exact (hFcont (hSpos hs)).aestronglyMeasurable
  have hFint : Integrable (F t) volume := by
    apply heat_integrable_of_decay_six (hFcont ht) (C := 3 * (M * M))
      (by positivity)
    intro x
    calc
      |F t x| ≤ ∑ i : Fin 3, |(heatConvVec3 t b x i) ^ 2| :=
        Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _i : Fin 3, M * M / (1 + vec3EuclideanNorm x) ^ 6 := by
        apply Finset.sum_le_sum
        intro i _
        rw [pow_two]
        exact heat_cubic_mul_cubic_le (hMtail ht x i) (hMtail ht x i)
      _ = 3 * (M * M) / (1 + vec3EuclideanNorm x) ^ 6 := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        ring
  let bound : Vec3 → ℝ := fun x => 6 * (M * N) / (1 + vec3EuclideanNorm x) ^ 6
  have hbound_int : Integrable bound volume := by
    simpa [bound] using heat_decay_six_integrable (6 * (M * N)) (by positivity)
  have hF'bound : ∀ᵐ x : Vec3 ∂volume, ∀ s ∈ S, ‖F' s x‖ ≤ bound x := by
    filter_upwards [] with x s hs
    have hs' := hSpos hs
    rw [Real.norm_eq_abs]
    calc
      |F' s x| ≤ ∑ i : Fin 3,
          |2 * heatConvVec3 s b x i * heatConvVec3 s bLap x i| :=
        Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _i : Fin 3, 2 * (M * N / (1 + vec3EuclideanNorm x) ^ 6) := by
        apply Finset.sum_le_sum
        intro i _
        rw [mul_assoc, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
        exact mul_le_mul_of_nonneg_left
          (heat_cubic_mul_cubic_le (hMtail hs' x i) (hNtail hs' x i))
          (by norm_num)
      _ = bound x := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        dsimp [bound]
        ring
  have hderiv : ∀ᵐ x : Vec3 ∂volume, ∀ s ∈ S,
      HasDerivAt (fun r => F r x) (F' s x) s := by
    filter_upwards [] with x s hs
    have hs' := hSpos hs
    have hcomp (i : Fin 3) : HasDerivAt (fun r => (heatConvVec3 r b x i) ^ 2)
        (2 * heatConvVec3 s b x i * heatConvVec3 s bLap x i) s := by
      have h := (heatConvVec3_component_hasDerivAt_laplacianInput
        hb hbc hs' x i).pow 2
      convert h using 1
      simp [heatConvVec3, bLap]
    have hsum := HasDerivAt.fun_sum (u := Finset.univ) (fun i _ => hcomp i)
    simpa [F, F'] using hsum
  have hmain := hasDerivAt_integral_of_dominated_loc_of_deriv_le hS hFmeas hFint
    hF'cont.aestronglyMeasurable hF'bound hbound_int hderiv
  simpa [F, F', heatConvVec3, bLap] using hmain.2

/-- Spatial integration by parts identifies the quadratic energy derivative
with minus twice the Dirichlet energy, as used in `lem:pv-heat-critical`. -/
theorem heatConvVec3_sq_integral_derivative_eq {b : Vec3 → Vec3}
    (hb : ∀ i : Fin 3, ContDiff ℝ (⊤ : ℕ∞) (fun x => b x i))
    (hbc : ∀ i : Fin 3, HasCompactSupport (fun x => b x i))
    {t : ℝ} (ht : 0 < t) :
    (∫ x : Vec3, ∑ i : Fin 3, 2 * heatConvVec3 t b x i *
        heatConv t (CKN.spatialLaplacian (fun y => b y i)) x) =
      -(2 * ∑ i : Fin 3, ∑ j : Fin 3, ∫ x : Vec3,
        (CKN.spatialDeriv (fun y => heatConvVec3 t b y i) j x) ^ 2) := by
  obtain ⟨M, hM, hMtail⟩ := heatConvVec3_component_decay hb hbc
  obtain ⟨D, hD, hDtail⟩ := heatConvVec3_firstDeriv_uniform_decay hb hbc
  obtain ⟨D₂, hD₂, hD₂tail⟩ := heatConvVec3_diagSecondDeriv_uniform_decay hb hbc
  let g : Fin 3 → Vec3 → ℝ := fun i x => heatConvVec3 t b x i
  have hgSmooth (i : Fin 3) : ContDiff ℝ (⊤ : ℕ∞) (g i) :=
    heatConvVec3_profile_contDiff hb hbc ht i
  have hfg (i j : Fin 3) : Integrable
      (fun x : Vec3 => g i x * CKN.spatialDeriv (g i) j x) volume :=
    heat_cubic_product_integrable (hgSmooth i).continuous
      (CKN.contDiff_spatialDeriv_smooth (hgSmooth i) j).continuous hM hD
      (fun x => hMtail ht x i) (fun x => hDtail ht x i j)
  have hfg' (i j : Fin 3) : Integrable
      (fun x : Vec3 => g i x *
        CKN.spatialDeriv (fun y => CKN.spatialDeriv (g i) j y) j x) volume :=
    heat_cubic_product_integrable (hgSmooth i).continuous
      (CKN.contDiff_spatialDeriv_smooth
        (CKN.contDiff_spatialDeriv_smooth (hgSmooth i) j) j).continuous hM hD₂
      (fun x => hMtail ht x i) (fun x => hD₂tail ht x i j)
  have hf'g (i j : Fin 3) : Integrable
      (fun x : Vec3 => CKN.spatialDeriv (g i) j x *
        CKN.spatialDeriv (g i) j x) volume :=
    heat_cubic_product_integrable
      (CKN.contDiff_spatialDeriv_smooth (hgSmooth i) j).continuous
      (CKN.contDiff_spatialDeriv_smooth (hgSmooth i) j).continuous hD hD
      (fun x => hDtail ht x i j) (fun x => hDtail ht x i j)
  have hLapEq (i : Fin 3) (x : Vec3) : CKN.spatialLaplacian (g i) x =
      heatConv t (CKN.spatialLaplacian (fun y => b y i)) x := by
    simpa [g, heatConvVec3] using
      (heatConvVec3_component_spatialLaplacian_input hb hbc ht x i)
  have hleftInt (i : Fin 3) : Integrable
      (fun x : Vec3 => g i x * CKN.spatialLaplacian (g i) x) volume := by
    have hsum : Integrable (fun x : Vec3 => ∑ j : Fin 3,
        g i x * CKN.spatialDeriv
          (fun y => CKN.spatialDeriv (g i) j y) j x) volume :=
      integrable_finsetSum Finset.univ (fun j _ => hfg' i j)
    refine hsum.congr (Filter.Eventually.of_forall fun x => ?_)
    change ∑ j : Fin 3, g i x * CKN.spatialDeriv
      (fun y => CKN.spatialDeriv (g i) j y) j x = g i x *
        CKN.spatialLaplacian (g i) x
    rw [CKN.spatialLaplacian, Finset.mul_sum]
  have hcomponentInt (i : Fin 3) : Integrable
      (fun x : Vec3 => 2 * heatConvVec3 t b x i *
        heatConv t (CKN.spatialLaplacian (fun y => b y i)) x) volume := by
    refine ((hleftInt i).const_mul 2).congr
      (Filter.Eventually.of_forall fun x => ?_)
    change 2 * (g i x * CKN.spatialLaplacian (g i) x) = _
    rw [hLapEq i x]
    ring
  have hcomponent (i : Fin 3) :
      ∫ x : Vec3, 2 * heatConvVec3 t b x i *
          heatConv t (CKN.spatialLaplacian (fun y => b y i)) x =
        -(2 * ∑ j : Fin 3, ∫ x : Vec3,
          (CKN.spatialDeriv (fun y => heatConvVec3 t b y i) j x) ^ 2) := by
    have hibp := integral_scalar_spatialLaplacian_ibp (hgSmooth i) (hgSmooth i)
      (fun j => hfg i j) (fun j => hfg' i j) (fun j => hf'g i j)
    have hrw : (fun x : Vec3 => 2 * heatConvVec3 t b x i *
        heatConv t (CKN.spatialLaplacian (fun y => b y i)) x) =
        fun x => 2 * (g i x * CKN.spatialLaplacian (g i) x) := by
      funext x
      rw [hLapEq i x]
      ring
    rw [hrw, integral_const_mul, hibp]
    have hsq (j : Fin 3) : (∫ x : Vec3, CKN.spatialDeriv (g i) j x *
        CKN.spatialDeriv (g i) j x) = ∫ x : Vec3,
          (CKN.spatialDeriv (fun y => heatConvVec3 t b y i) j x) ^ 2 := by
      apply integral_congr_ae
      filter_upwards [] with x
      change CKN.spatialDeriv (g i) j x * CKN.spatialDeriv (g i) j x =
        (CKN.spatialDeriv (g i) j x) ^ 2
      ring
    simp only [hsq]
    ring
  rw [integral_finsetSum Finset.univ (fun i _ => hcomponentInt i)]
  simp only [hcomponent]
  rw [Finset.sum_neg_distrib, Finset.mul_sum]

/-- The quadratic energy of a smooth compact vector heat orbit converges to
its initial value as time decreases to zero. -/
theorem heatConvVec3_sq_integral_tendsto_initial {b : Vec3 → Vec3}
    (hb : ∀ i : Fin 3, ContDiff ℝ (⊤ : ℕ∞) (fun x => b x i))
    (hbc : ∀ i : Fin 3, HasCompactSupport (fun x => b x i)) :
    Tendsto (fun t : ℝ => ∫ x : Vec3, ∑ i : Fin 3, (heatConvVec3 t b x i) ^ 2)
      (nhdsWithin (0 : ℝ) (Ioi (0 : ℝ)))
      (nhds (∫ x : Vec3, ∑ i : Fin 3, (b x i) ^ 2)) := by
  obtain ⟨M, hM, hMtail⟩ := heatConvVec3_component_decay hb hbc
  let bound : Vec3 → ℝ := fun x => 3 * (M * M) / (1 + vec3EuclideanNorm x) ^ 6
  have hbound_int : Integrable bound volume := by
    simpa [bound] using heat_decay_six_integrable (3 * (M * M)) (by positivity)
  apply tendsto_integral_filter_of_dominated_convergence bound
  · filter_upwards [self_mem_nhdsWithin] with s hs
    have hs' : 0 < s := hs
    have hc (i : Fin 3) := (heatConvVec3_profile_contDiff hb hbc hs' i).continuous
    exact (continuous_finsetSum _ fun i _ => (hc i).pow 2).aestronglyMeasurable
  · filter_upwards [self_mem_nhdsWithin] with s hs
    have hs' : 0 < s := hs
    filter_upwards [] with x
    rw [Real.norm_eq_abs]
    calc
      |∑ i : Fin 3, (heatConvVec3 s b x i) ^ 2| ≤
          ∑ i : Fin 3, |(heatConvVec3 s b x i) ^ 2| :=
        Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _i : Fin 3, M * M / (1 + vec3EuclideanNorm x) ^ 6 := by
        apply Finset.sum_le_sum
        intro i _
        rw [pow_two]
        exact heat_cubic_mul_cubic_le (hMtail hs' x i) (hMtail hs' x i)
      _ = bound x := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        dsimp [bound]
        ring
  · exact hbound_int
  · filter_upwards [] with x
    apply tendsto_finsetSum
    intro i _
    exact ((heatConv_tendsto_self_nhdsWithin_zero_smooth (hb i) (hbc i) x).pow 2)

/-- Time integration of the quadratic energy identity: the energy does not
increase and twice the Dirichlet energy integrated over `(0, τ)` is bounded by
the initial energy, as used in `lem:pv-heat-critical`. -/
theorem heatConvVec3_energy_bound {b : Vec3 → Vec3}
    (hb : ∀ i : Fin 3, ContDiff ℝ (⊤ : ℕ∞) (fun x => b x i))
    (hbc : ∀ i : Fin 3, HasCompactSupport (fun x => b x i))
    {τ : ℝ} (hτ : 0 < τ) :
    (∫ x : Vec3, ∑ i : Fin 3, (heatConvVec3 τ b x i) ^ 2) ≤
        ∫ x : Vec3, ∑ i : Fin 3, (b x i) ^ 2 ∧
      (∫⁻ t in Ioo 0 τ, ENNReal.ofReal (2 * ∑ i : Fin 3, ∑ j : Fin 3,
          ∫ x : Vec3, (CKN.spatialDeriv (fun y => heatConvVec3 t b y i) j x) ^ 2)) ≤
        ENNReal.ofReal (∫ x : Vec3, ∑ i : Fin 3, (b x i) ^ 2) := by
  let e : ℝ → ℝ := fun s => ∫ x : Vec3, ∑ i : Fin 3, (heatConvVec3 s b x i) ^ 2
  let e₀ : ℝ := ∫ x : Vec3, ∑ i : Fin 3, (b x i) ^ 2
  let D : ℝ → ℝ := fun t => 2 * ∑ i : Fin 3, ∑ j : Fin 3,
    ∫ x : Vec3, (CKN.spatialDeriv (fun y => heatConvVec3 t b y i) j x) ^ 2
  let g : ℝ → ℝ := fun s => -(if s ≤ 0 then e₀ else e s)
  have hderiv (s : ℝ) (hs : 0 < s) : HasDerivAt e (-D s) s := by
    have h1 := heatConvVec3_sq_integral_hasDerivAt hb hbc hs
    rw [heatConvVec3_sq_integral_derivative_eq hb hbc hs] at h1
    exact h1
  have hgderiv (s : ℝ) (hs : 0 < s) : HasDerivAt g (D s) s := by
    have hloc : g =ᶠ[nhds s] fun r => -e r := by
      filter_upwards [lt_mem_nhds hs] with r hr
      simp [g, not_le.mpr hr]
    have h := (hderiv s hs).neg
    rw [neg_neg] at h
    exact h.congr_of_eventuallyEq hloc
  have hDnonneg (s : ℝ) : 0 ≤ D s := by
    dsimp [D]
    apply mul_nonneg (by norm_num)
    exact Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ =>
      integral_nonneg fun x => sq_nonneg _
  have hcont : ContinuousOn g (Icc 0 τ) := by
    intro s hs
    rcases eq_or_lt_of_le hs.1 with h0 | hpos
    · subst h0
      have hlim := (heatConvVec3_sq_integral_tendsto_initial hb hbc).neg
      have heq : (fun r => -e r) =ᶠ[nhdsWithin 0 (Ioi 0)] g := by
        filter_upwards [self_mem_nhdsWithin] with r hr
        have hr' : 0 < r := hr
        simp [g, not_le.mpr hr']
      have hright : ContinuousWithinAt g (Ioi 0) 0 := by
        have h := (tendsto_congr' heq).1 hlim
        have hg0 : g 0 = -e₀ := by simp [g]
        rw [ContinuousWithinAt, hg0]
        exact h
      rw [continuousWithinAt_Ioi_iff_Ici] at hright
      exact hright.mono Icc_subset_Ici_self
    · exact (hgderiv s hpos).continuousAt.continuousWithinAt
  have hint : IntegrableOn D (Ioc 0 τ) :=
    intervalIntegral.integrableOn_deriv_of_nonneg hcont
      (fun s hs => hgderiv s hs.1) (fun s _ => hDnonneg s)
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hτ.le hcont
    (fun s hs => hgderiv s hs.1)
    ((intervalIntegrable_iff_integrableOn_Ioc_of_le hτ.le).2 hint)
  have heτ : 0 ≤ e τ :=
    integral_nonneg fun x => Finset.sum_nonneg fun i _ => sq_nonneg _
  have hIntNonneg : 0 ≤ ∫ t in (0 : ℝ)..τ, D t :=
    intervalIntegral.integral_nonneg hτ.le (fun s _ => hDnonneg s)
  have hgτ : g τ = -e τ := by simp [g, not_le.mpr hτ]
  have hg0 : g 0 = -e₀ := by simp [g]
  rw [hgτ, hg0] at hFTC
  refine ⟨?_, ?_⟩
  · change e τ ≤ e₀
    linarith only [hFTC, hIntNonneg]
  · have hIoo : ∫⁻ t in Ioo 0 τ, ENNReal.ofReal (D t) =
        ENNReal.ofReal (∫ t in Ioo 0 τ, D t) :=
      (ofReal_integral_eq_lintegral_ofReal (hint.mono_set Ioo_subset_Ioc_self)
        (Filter.Eventually.of_forall hDnonneg)).symm
    have hsame : (∫ t in Ioo 0 τ, D t) = ∫ t in (0 : ℝ)..τ, D t := by
      rw [intervalIntegral.integral_of_le hτ.le, integral_Ioc_eq_integral_Ioo]
    change ∫⁻ t in Ioo 0 τ, ENNReal.ofReal (D t) ≤ ENNReal.ofReal e₀
    rw [hIoo, hsame]
    apply ENNReal.ofReal_le_ofReal
    linarith only [hFTC, heτ]

end ESS

end
