/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.EscauriazaSereginSverak.PartV.HeatCriticalEnergy
public import LeanPool.EscauriazaSereginSverak.PartV.HeatCriticalMeasurable

/-!
# The energy-level space-time bound for smooth heat data

For smooth compactly supported data the heat energy bound and the
Gagliardo–Nirenberg inequality `eq:gn-ten-thirds` of the CKN manuscript, applied at each time, give
`‖S(·)b‖_{L^{10/3}(Q_τ)} ≤ C ‖b‖₂` with `C` independent of `τ`.  This is the
`L²` input of the second estimate in `lem:pv-heat-critical`.
-/

public section

open MeasureTheory Filter Set
open scoped ENNReal
open CKN CKN.Foundation.Parabolic CKN.Foundation.Heat


noncomputable section

namespace ESS

/-- On positive times the extended smooth heat orbit is the heat orbit. -/
theorem heatConvVec3SmoothExt_of_pos {b : Vec3 → Vec3} {t : ℝ} (ht : 0 < t)
    (x : Vec3) : heatConvVec3SmoothExt b t x = heatConvVec3 t b x := by
  funext i
  simp [heatConvVec3SmoothExt, heatConvSmoothExt, heatConvVec3, not_le.mpr ht]

/-- The heat orbit of smooth compact data is almost everywhere strongly
measurable on every slab of positive times, as used in `lem:pv-heat-critical`. -/
theorem heatOrbit_aestronglyMeasurable_smooth {b : Vec3 → Vec3}
    (hb : ∀ i : Fin 3, ContDiff ℝ (⊤ : ℕ∞) (fun x => b x i))
    (hbc : ∀ i : Fin 3, HasCompactSupport (fun x => b x i)) (τ : ℝ) :
    AEStronglyMeasurable (heatOrbit b)
      (volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 τ))) := by
  have hmeas : Measurable (fun z : ParabolicPoint =>
      heatConvVec3SmoothExt b z.2 z.1) :=
    (heatConvVec3SmoothExt_joint_measurable hb hbc).comp measurable_swap
  refine hmeas.aestronglyMeasurable.congr ?_
  have hQ : MeasurableSet (spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 τ)) :=
    MeasurableSet.univ.prod measurableSet_Ioo
  filter_upwards [ae_restrict_mem hQ] with z hz
  have hz2 : 0 < z.2 := hz.2.1
  change heatConvVec3SmoothExt b z.2 z.1 = heatConvVec3 z.2 b z.1
  exact heatConvVec3SmoothExt_of_pos hz2 z.1

/-- Tonelli on a slab `ℝ³ × I`: the space-time integral is the time integral of
the spatial integrals. -/
theorem lintegral_spaceTimeSet_univ_eq {I : Set ℝ} {F : ParabolicPoint → ℝ≥0∞}
    (hF : AEMeasurable F (volume.restrict (spaceTimeSet (Set.univ : Set Vec3) I))) :
    ∫⁻ z in spaceTimeSet (Set.univ : Set Vec3) I, F z =
      ∫⁻ t in I, ∫⁻ x : Vec3, F (x, t) := by
  have hFprod : AEMeasurable (fun z : Vec3 × ℝ => F (z.1, z.2))
      ((volume.restrict (Set.univ : Set Vec3)).prod (volume.restrict I)) := by
    rw [Measure.prod_restrict]
    exact hF
  change (∫⁻ z : Vec3 × ℝ in (Set.univ : Set Vec3) ×ˢ I,
    F (z.1, z.2) ∂((volume : Measure Vec3).prod (volume : Measure ℝ))) = _
  rw [← Measure.prod_restrict, lintegral_prod_symm _ hFprod, Measure.restrict_univ]

/-- The squared `L²` norm of a square-integrable real function is the
extended real of its square integral. -/
theorem eLpNorm_two_rpow_two_eq_ofReal_integral {f : Vec3 → ℝ}
    (hf : MemLp f 2 volume) :
    eLpNorm f 2 volume ^ (2 : ℝ) = ENNReal.ofReal (∫ x : Vec3, f x ^ 2) := by
  rw [hf.eLpNorm_eq_integral_rpow_norm (by norm_num) (by norm_num)]
  have htwo : (2 : ℝ≥0∞).toReal = 2 := by norm_num
  simp only [htwo]
  have hnn : 0 ≤ ∫ x : Vec3, ‖f x‖ ^ (2 : ℝ) :=
    integral_nonneg fun x => by positivity
  rw [ENNReal.ofReal_rpow_of_nonneg (by positivity) (by norm_num),
    ← Real.rpow_mul hnn]
  have hexp : (2 : ℝ)⁻¹ * 2 = 1 := by norm_num
  rw [hexp, Real.rpow_one]
  congr 1
  apply integral_congr_ae
  filter_upwards [] with x
  rw [Real.rpow_two, Real.norm_eq_abs, sq_abs]

/-- The `H¹` slice of one component of a smooth compact heat orbit. -/
@[expose] def heatComponentH1 {b : Vec3 → Vec3}
    (hb : ∀ i : Fin 3, ContDiff ℝ (⊤ : ℕ∞) (fun x => b x i))
    (hbc : ∀ i : Fin 3, HasCompactSupport (fun x => b x i))
    {t : ℝ} (ht : 0 < t) (i : Fin 3) :
    CKN.H1Function (Set.univ : Set Vec3) where
  toFun := fun x => heatConvVec3 t b x i
  grad := fun x j => CKN.spatialDeriv (fun y => heatConvVec3 t b y i) j x
  memL2 := by
    have hmem : MemLp (fun x => heatConvVec3 t b x i) 2 volume := by
      simpa [heatConvVec3] using heatConv_memLp_two_smooth (hb i) (hbc i) ht
    simpa [CKN.MemL2On, CKN.MemLpOn, CKN.volumeOn, Measure.restrict_univ] using hmem
  gradMemL2 := by
    intro j
    have hdS : ContDiff ℝ (⊤ : ℕ∞) (CKN.spatialDeriv (fun y => b y i) j) :=
      CKN.contDiff_spatialDeriv_smooth (hb i) j
    have hdC : HasCompactSupport (CKN.spatialDeriv (fun y => b y i) j) := by
      change HasCompactSupport (fun z => (fderiv ℝ (fun y => b y i) z) (CKN.basisVec j))
      exact (hbc i).fderiv_apply (𝕜 := ℝ) (CKN.basisVec j)
    have hmem := heatConv_memLp_two_smooth hdS hdC ht
    have heq : (fun x => CKN.spatialDeriv (fun y => heatConvVec3 t b y i) j x) =
        heatConv t (CKN.spatialDeriv (fun y => b y i) j) := by
      funext x
      change fderiv ℝ (heatConv t (fun y => b y i)) x (CKN.basisVec j) = _
      exact heatConv_fderiv (hb i) (hbc i) ht x (CKN.basisVec j)
    have hmem' : MemLp (fun x => CKN.spatialDeriv
        (fun y => heatConvVec3 t b y i) j x) 2 volume := by
      rw [heq]
      exact hmem
    simpa [CKN.GradMemL2On, CKN.MemL2On, CKN.MemLpOn, CKN.volumeOn,
      Measure.restrict_univ] using hmem'
  hasWeakGradient := by
    have hg : ContDiff ℝ 1 (fun x => heatConvVec3 t b x i) := by
      have h : ContDiff ℝ (⊤ : ℕ∞) (fun x => heatConvVec3 t b x i) := by
        simpa [heatConvVec3] using heatConv_smooth_input (hb i) (hbc i) ht
      exact h.of_le (by norm_num)
    exact CKN.HasWeakGradientOn.of_contDiff (U := Set.univ) hg

/-- A bound on the `p`-th power integral converts into an `Lᵖ` bound. -/
theorem eLpNorm_ofReal_le_of_lintegral_le {α E : Type*} [MeasurableSpace α]
    [NormedAddCommGroup E] {μ : Measure α} {f : α → E} {p : ℝ} (hp : 0 < p)
    (hf : AEStronglyMeasurable f μ) {K Y : ℝ≥0∞}
    (h : ∫⁻ x, ‖f x‖ₑ ^ p ∂μ ≤ K * Y ^ p) :
    eLpNorm f (ENNReal.ofReal p) μ ≤ K ^ (1 / p) * Y := by
  rw [eLpNorm_eq_eLpNorm' (by simpa using hp) ENNReal.ofReal_ne_top hf,
    eLpNorm'_eq_lintegral_enorm, ENNReal.toReal_ofReal hp.le]
  calc
    (∫⁻ x, ‖f x‖ₑ ^ p ∂μ) ^ (1 / p) ≤ (K * Y ^ p) ^ (1 / p) :=
      ENNReal.rpow_le_rpow h (by positivity)
    _ = K ^ (1 / p) * Y := by
      rw [ENNReal.mul_rpow_of_nonneg _ _ (by positivity), ← ENNReal.rpow_mul,
        mul_one_div_cancel hp.ne', ENNReal.rpow_one]

/-- The Gagliardo–Nirenberg inequality `eq:gn-ten-thirds` of the CKN manuscript for one component of
a smooth compact heat orbit at a positive time. -/
theorem heatComponent_tenThirds_slice {b : Vec3 → Vec3}
    (hb : ∀ i : Fin 3, ContDiff ℝ (⊤ : ℕ∞) (fun x => b x i))
    (hbc : ∀ i : Fin 3, HasCompactSupport (fun x => b x i))
    {t : ℝ} (ht : 0 < t) (i : Fin 3) :
    ∫⁻ x : Vec3, ‖heatConvVec3 t b x i‖ₑ ^ (10 / 3 : ℝ) ≤
      gagliardoNirenbergSobolevConstant ^ (2 : ℝ) *
        ENNReal.ofReal (∫ x : Vec3, (heatConvVec3 t b x i) ^ 2) ^ (2 / 3 : ℝ) *
        ENNReal.ofReal (∑ j : Fin 3, ∫ x : Vec3,
          (CKN.spatialDeriv (fun y => heatConvVec3 t b y i) j x) ^ 2) := by
  let H := heatComponentH1 hb hbc ht i
  have hGN := h1_gagliardoNirenberg_tenThirds H
  have hsmooth : ContDiff ℝ (⊤ : ℕ∞) (fun x => heatConvVec3 t b x i) := by
    simpa [heatConvVec3] using heatConv_smooth_input (hb i) (hbc i) ht
  have hmeas : AEStronglyMeasurable H.toFun volume :=
    hsmooth.continuous.aestronglyMeasurable
  have hmem : MemLp H.toFun 2 volume :=
    heatConv_memLp_two_smooth (hb i) (hbc i) ht
  have hgradMem (j : Fin 3) : MemLp (fun x => H.grad x j) 2 volume := by
    simpa [CKN.GradMemL2On, CKN.MemL2On, CKN.MemLpOn, CKN.volumeOn,
      Measure.restrict_univ] using H.gradMemL2 j
  have hgradCont (j : Fin 3) : Continuous (fun x => H.grad x j) :=
    (CKN.contDiff_spatialDeriv_smooth hsmooth j).continuous
  have hgradSq (j : Fin 3) : Integrable (fun x => (H.grad x j) ^ 2) volume :=
    (memLp_two_iff_integrable_sq (hgradMem j).aestronglyMeasurable).1 (hgradMem j)
  have heuclMem : MemLp (fun x => vec3EuclideanNorm (H.grad x)) 2 volume := by
    have hcont : Continuous (fun x => vec3EuclideanNorm (H.grad x)) :=
      continuous_vec3EuclideanNorm.comp (continuous_pi hgradCont)
    refine (memLp_two_iff_integrable_sq hcont.aestronglyMeasurable).2 ?_
    refine (integrable_finsetSum Finset.univ (fun j _ => hgradSq j)).congr
      (Filter.Eventually.of_forall fun x => ?_)
    change ∑ j : Fin 3, (H.grad x j) ^ 2 = vec3EuclideanNorm (H.grad x) ^ 2
    rw [vec3EuclideanNorm_sq]
  have hL : ∫⁻ x : Vec3, ‖heatConvVec3 t b x i‖ₑ ^ (10 / 3 : ℝ) =
      eLpNorm H.toFun (ENNReal.ofReal (10 / 3 : ℝ)) volume ^ (10 / 3 : ℝ) := by
    rw [eLpNorm_eq_eLpNorm' (by norm_num) ENNReal.ofReal_ne_top hmeas,
      eLpNorm'_eq_lintegral_enorm, ENNReal.toReal_ofReal (by norm_num),
      ← ENNReal.rpow_mul]
    norm_num
    rfl
  have h2 : eLpNorm H.toFun 2 volume ^ (2 : ℝ) =
      ENNReal.ofReal (∫ x : Vec3, (heatConvVec3 t b x i) ^ 2) :=
    eLpNorm_two_rpow_two_eq_ofReal_integral hmem
  have hg2 : eLpNorm (fun x => vec3EuclideanNorm (H.grad x)) 2 volume ^ (2 : ℝ) =
      ENNReal.ofReal (∑ j : Fin 3, ∫ x : Vec3,
        (CKN.spatialDeriv (fun y => heatConvVec3 t b y i) j x) ^ 2) := by
    rw [eLpNorm_two_rpow_two_eq_ofReal_integral heuclMem]
    congr 1
    have hsum : (∑ j : Fin 3, ∫ x : Vec3,
        (CKN.spatialDeriv (fun y => heatConvVec3 t b y i) j x) ^ 2) =
        ∫ x : Vec3, ∑ j : Fin 3, (H.grad x j) ^ 2 :=
      (integral_finsetSum Finset.univ (fun j _ => hgradSq j)).symm
    rw [hsum]
    apply integral_congr_ae
    filter_upwards [] with x
    rw [vec3EuclideanNorm_sq]
  set S := gagliardoNirenbergSobolevConstant
  set A := eLpNorm H.toFun 2 volume
  set B := eLpNorm (fun x => vec3EuclideanNorm (H.grad x)) 2 volume
  rw [hL]
  calc
    eLpNorm H.toFun (ENNReal.ofReal (10 / 3 : ℝ)) volume ^ (10 / 3 : ℝ) ≤
        (S ^ (3 / 5 : ℝ) * A ^ (2 / 5 : ℝ) * B ^ (3 / 5 : ℝ)) ^ (10 / 3 : ℝ) :=
      ENNReal.rpow_le_rpow hGN (by norm_num)
    _ = S ^ (2 : ℝ) * (A ^ (2 : ℝ)) ^ (2 / 3 : ℝ) * B ^ (2 : ℝ) := by
      rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num),
        ENNReal.mul_rpow_of_nonneg _ _ (by norm_num),
        ← ENNReal.rpow_mul, ← ENNReal.rpow_mul, ← ENNReal.rpow_mul,
        ← ENNReal.rpow_mul]
      norm_num
    _ = _ := by rw [h2, hg2]

/-- The extended power integral is the corresponding power of the `Lᵖ` norm. -/
theorem lintegral_enorm_rpow_eq_eLpNorm_rpow {α E : Type*} [MeasurableSpace α]
    [NormedAddCommGroup E] {μ : Measure α} {f : α → E} {p : ℝ} (hp : 0 < p)
    (hf : AEStronglyMeasurable f μ) :
    ∫⁻ x, ‖f x‖ₑ ^ p ∂μ = eLpNorm f (ENNReal.ofReal p) μ ^ p := by
  rw [eLpNorm_eq_eLpNorm' (by simpa using hp) ENNReal.ofReal_ne_top hf,
    eLpNorm'_eq_lintegral_enorm, ENNReal.toReal_ofReal hp.le, ← ENNReal.rpow_mul,
    one_div_mul_cancel hp.ne', ENNReal.rpow_one]

private theorem enorm_rpow_le_sum_component (v : Vec3) (r : ℝ) :
    ‖v‖ₑ ^ r ≤ ∑ i : Fin 3, ‖v i‖ₑ ^ r := by
  obtain ⟨k, -, hk⟩ := Finset.exists_mem_eq_sup Finset.univ Finset.univ_nonempty
    (fun i => ‖v i‖₊)
  have hv : ‖v‖ₑ = ‖v k‖ₑ := by
    rw [enorm_eq_nnnorm, enorm_eq_nnnorm, Pi.nnnorm_def, hk]
  rw [hv]
  exact Finset.single_le_sum (f := fun i => ‖v i‖ₑ ^ r)
    (fun i _ => bot_le) (Finset.mem_univ k)

/-- The sum of squared components of a smooth compact field is bounded by three
times the squared `L²` norm. -/
theorem ofReal_integral_sum_sq_le_eLpNorm_two {b : Vec3 → Vec3}
    (hb : ∀ i : Fin 3, ContDiff ℝ (⊤ : ℕ∞) (fun x => b x i))
    (hbc : ∀ i : Fin 3, HasCompactSupport (fun x => b x i)) :
    ENNReal.ofReal (∫ x : Vec3, ∑ i : Fin 3, (b x i) ^ 2) ≤
      3 * eLpNorm b 2 volume ^ (2 : ℝ) := by
  have hcont : Continuous b := continuous_pi fun i => (hb i).continuous
  have hint : Integrable (fun x : Vec3 => ∑ i : Fin 3, (b x i) ^ 2) volume :=
    integrable_finsetSum Finset.univ fun i _ =>
      ((hb i).continuous.pow 2).integrable_of_hasCompactSupport
        (by simpa only [pow_two] using (hbc i).mul_right)
  rw [ofReal_integral_eq_lintegral_ofReal hint
      (Filter.Eventually.of_forall fun x => Finset.sum_nonneg fun i _ => sq_nonneg _),
    show (2 : ℝ≥0∞) = ENNReal.ofReal 2 by norm_num,
    ← lintegral_enorm_rpow_eq_eLpNorm_rpow (by norm_num) hcont.aestronglyMeasurable,
    ← lintegral_const_mul' _ _ (by norm_num)]
  apply lintegral_mono
  intro x
  have hpoint : ∑ i : Fin 3, (b x i) ^ 2 ≤ 3 * ‖b x‖ ^ 2 := by
    calc
      ∑ i : Fin 3, (b x i) ^ 2 ≤ ∑ _i : Fin 3, ‖b x‖ ^ 2 := by
        apply Finset.sum_le_sum
        intro i _
        rw [← sq_abs]
        exact pow_le_pow_left₀ (abs_nonneg _)
          (by simpa [Real.norm_eq_abs] using norm_le_pi_norm (b x) i) 2
      _ = 3 * ‖b x‖ ^ 2 := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        norm_num
  calc
    ENNReal.ofReal (∑ i : Fin 3, (b x i) ^ 2) ≤ ENNReal.ofReal (3 * ‖b x‖ ^ 2) :=
      ENNReal.ofReal_le_ofReal hpoint
    _ = 3 * ‖b x‖ₑ ^ (2 : ℝ) := by
      rw [ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_pow (norm_nonneg _),
        ofReal_norm]
      norm_num

/-- The energy-level space-time bound for smooth compact data: the
`L^{10/3}(Q_τ)` integral is controlled by the initial energy, uniformly in
`τ`, as used in `lem:pv-heat-critical`. -/
theorem heatOrbit_tenThirds_lintegral_smooth {b : Vec3 → Vec3}
    (hb : ∀ i : Fin 3, ContDiff ℝ (⊤ : ℕ∞) (fun x => b x i))
    (hbc : ∀ i : Fin 3, HasCompactSupport (fun x => b x i))
    {τ : ℝ} (hτ : 0 < τ) :
    ∫⁻ z in spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 τ),
        ‖heatOrbit b z‖ₑ ^ (10 / 3 : ℝ) ≤
      3 * gagliardoNirenbergSobolevConstant ^ (2 : ℝ) *
        ENNReal.ofReal (∫ x : Vec3, ∑ i : Fin 3, (b x i) ^ 2) ^ (5 / 3 : ℝ) := by
  set Q := spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 τ)
  set S := gagliardoNirenbergSobolevConstant
  set e₀ := ∫ x : Vec3, ∑ i : Fin 3, (b x i) ^ 2
  have hS : S ≠ ∞ := (Classical.choose_spec CKN.sobolev_L6_global).1
  have hm := heatOrbit_aestronglyMeasurable_smooth hb hbc τ
  have hcomp (i : Fin 3) : AEMeasurable
      (fun z => ‖heatOrbit b z i‖ₑ ^ (10 / 3 : ℝ)) (volume.restrict Q) :=
    ((continuous_apply i).comp_aestronglyMeasurable hm).aemeasurable.enorm.pow_const _
  have hsqInt {t : ℝ} (ht : 0 < t) (k : Fin 3) :
      Integrable (fun x => (heatConvVec3 t b x k) ^ 2) volume := by
    have hmem : MemLp (fun x => heatConvVec3 t b x k) 2 volume :=
      heatConv_memLp_two_smooth (hb k) (hbc k) ht
    exact (memLp_two_iff_integrable_sq hmem.aestronglyMeasurable).1 hmem
  have hcompBound (i : Fin 3) :
      ∫⁻ z in Q, ‖heatOrbit b z i‖ₑ ^ (10 / 3 : ℝ) ≤
        S ^ (2 : ℝ) * ENNReal.ofReal e₀ ^ (2 / 3 : ℝ) * ENNReal.ofReal e₀ := by
    rw [lintegral_spaceTimeSet_univ_eq (hcomp i)]
    calc
      (∫⁻ t in Ioo 0 τ, ∫⁻ x : Vec3, ‖heatOrbit b (x, t) i‖ₑ ^ (10 / 3 : ℝ)) ≤
          ∫⁻ t in Ioo 0 τ, S ^ (2 : ℝ) * ENNReal.ofReal e₀ ^ (2 / 3 : ℝ) *
            ENNReal.ofReal (2 * ∑ k : Fin 3, ∑ j : Fin 3, ∫ x : Vec3,
              (CKN.spatialDeriv (fun y => heatConvVec3 t b y k) j x) ^ 2) := by
        apply setLIntegral_mono' measurableSet_Ioo
        intro t ht
        have hslice := heatComponent_tenThirds_slice hb hbc ht.1 i
        refine hslice.trans ?_
        have hL2 : ENNReal.ofReal (∫ x : Vec3, (heatConvVec3 t b x i) ^ 2) ≤
            ENNReal.ofReal e₀ := by
          apply ENNReal.ofReal_le_ofReal
          refine le_trans ?_ (heatConvVec3_energy_bound hb hbc ht.1).1
          apply integral_mono (hsqInt ht.1 i)
            (integrable_finsetSum Finset.univ fun k _ => hsqInt ht.1 k)
          intro x
          exact Finset.single_le_sum (f := fun k => (heatConvVec3 t b x k) ^ 2)
            (fun k _ => sq_nonneg _) (Finset.mem_univ i)
        have hgrad : ENNReal.ofReal (∑ j : Fin 3, ∫ x : Vec3,
              (CKN.spatialDeriv (fun y => heatConvVec3 t b y i) j x) ^ 2) ≤
            ENNReal.ofReal (2 * ∑ k : Fin 3, ∑ j : Fin 3, ∫ x : Vec3,
              (CKN.spatialDeriv (fun y => heatConvVec3 t b y k) j x) ^ 2) := by
          apply ENNReal.ofReal_le_ofReal
          have hT (k : Fin 3) : 0 ≤ ∑ j : Fin 3, ∫ x : Vec3,
              (CKN.spatialDeriv (fun y => heatConvVec3 t b y k) j x) ^ 2 :=
            Finset.sum_nonneg fun j _ => integral_nonneg fun x => sq_nonneg _
          have hsingle := Finset.single_le_sum (f := fun k => ∑ j : Fin 3,
            ∫ x : Vec3, (CKN.spatialDeriv (fun y => heatConvVec3 t b y k) j x) ^ 2)
            (fun k _ => hT k) (Finset.mem_univ i)
          have hsum := Finset.sum_nonneg (s := Finset.univ) fun k _ => hT k
          linarith only [hsingle, hsum]
        gcongr
      _ = S ^ (2 : ℝ) * ENNReal.ofReal e₀ ^ (2 / 3 : ℝ) *
          ∫⁻ t in Ioo 0 τ, ENNReal.ofReal (2 * ∑ k : Fin 3, ∑ j : Fin 3,
            ∫ x : Vec3, (CKN.spatialDeriv (fun y => heatConvVec3 t b y k) j x) ^ 2) :=
        lintegral_const_mul' _ _ (by
          apply ENNReal.mul_ne_top (ENNReal.rpow_ne_top_of_nonneg (by norm_num) hS)
          exact ENNReal.rpow_ne_top_of_nonneg (by norm_num) ENNReal.ofReal_ne_top)
      _ ≤ S ^ (2 : ℝ) * ENNReal.ofReal e₀ ^ (2 / 3 : ℝ) * ENNReal.ofReal e₀ := by
        gcongr
        exact (heatConvVec3_energy_bound hb hbc hτ).2
  calc
    ∫⁻ z in Q, ‖heatOrbit b z‖ₑ ^ (10 / 3 : ℝ) ≤
        ∫⁻ z in Q, ∑ i : Fin 3, ‖heatOrbit b z i‖ₑ ^ (10 / 3 : ℝ) :=
      lintegral_mono fun z => enorm_rpow_le_sum_component _ _
    _ = ∑ i : Fin 3, ∫⁻ z in Q, ‖heatOrbit b z i‖ₑ ^ (10 / 3 : ℝ) :=
      lintegral_finsetSum' _ fun i _ => hcomp i
    _ ≤ ∑ _i : Fin 3,
        S ^ (2 : ℝ) * ENNReal.ofReal e₀ ^ (2 / 3 : ℝ) * ENNReal.ofReal e₀ :=
      Finset.sum_le_sum fun i _ => hcompBound i
    _ = 3 * S ^ (2 : ℝ) * ENNReal.ofReal e₀ ^ (5 / 3 : ℝ) := by
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
        show (5 / 3 : ℝ) = 2 / 3 + 1 by norm_num,
        ENNReal.rpow_add_of_nonneg _ _ (by norm_num) (by norm_num), ENNReal.rpow_one]
      norm_num
      ring

/-- The energy-level space-time estimate `‖S(·)b‖_{L^{10/3}(Q_τ)} ≤ C‖b‖₂` for
smooth compact data, with `C` independent of `τ`, as used in
`lem:pv-heat-critical`. -/
theorem heatOrbit_tenThirds_smooth :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (b : Vec3 → Vec3),
      (∀ i : Fin 3, ContDiff ℝ (⊤ : ℕ∞) (fun x => b x i)) →
      (∀ i : Fin 3, HasCompactSupport (fun x => b x i)) → ∀ τ : ℝ, 0 < τ →
      eLpNorm (heatOrbit b) (ENNReal.ofReal (10 / 3 : ℝ))
          (volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 τ))) ≤
        ENNReal.ofReal C * eLpNorm b 2 volume := by
  set S := gagliardoNirenbergSobolevConstant
  have hS : S ≠ ∞ := (Classical.choose_spec CKN.sobolev_L6_global).1
  set K : ℝ≥0∞ := 3 * S ^ (2 : ℝ) * 3 ^ (5 / 3 : ℝ)
  have hK : K ≠ ∞ := by
    apply ENNReal.mul_ne_top (ENNReal.mul_ne_top (by norm_num)
      (ENNReal.rpow_ne_top_of_nonneg (by norm_num) hS))
    exact ENNReal.rpow_ne_top_of_nonneg (by norm_num) (by norm_num)
  have hKp : K ^ (1 / (10 / 3 : ℝ)) ≠ ∞ :=
    ENNReal.rpow_ne_top_of_nonneg (by norm_num) hK
  refine ⟨(K ^ (1 / (10 / 3 : ℝ))).toReal, ENNReal.toReal_nonneg, ?_⟩
  intro b hb hbc τ hτ
  rw [ENNReal.ofReal_toReal hKp]
  apply eLpNorm_ofReal_le_of_lintegral_le (by norm_num)
    (heatOrbit_aestronglyMeasurable_smooth hb hbc τ)
  refine (heatOrbit_tenThirds_lintegral_smooth hb hbc hτ).trans ?_
  have he := ofReal_integral_sum_sq_le_eLpNorm_two hb hbc
  calc
    3 * S ^ (2 : ℝ) * ENNReal.ofReal (∫ x : Vec3, ∑ i : Fin 3, (b x i) ^ 2) ^
        (5 / 3 : ℝ) ≤ 3 * S ^ (2 : ℝ) * (3 * eLpNorm b 2 volume ^ (2 : ℝ)) ^
          (5 / 3 : ℝ) := by gcongr
    _ = K * eLpNorm b 2 volume ^ (10 / 3 : ℝ) := by
      rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num), ← ENNReal.rpow_mul,
        show (2 : ℝ) * (5 / 3) = 10 / 3 by norm_num]
      simp only [K]
      ring

end ESS

end
