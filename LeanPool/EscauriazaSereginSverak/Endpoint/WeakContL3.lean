/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.CaffarelliKohnNirenberg.Leray.Support.WeakContL3Support
public import LeanPool.EscauriazaSereginSverak.Endpoint.WeakContL3Norming
public import LeanPool.CaffarelliKohnNirenberg.Leray.Support.LocalEnergyCylinderL4
public import LeanPool.CaffarelliKohnNirenberg.Leray.Support.LocalEnergyWeakGradient
public import LeanPool.CaffarelliKohnNirenberg.Leray.Support.LocalEnergyMollifiedData
public import LeanPool.CaffarelliKohnNirenberg.Leray.Support.PressureSplitTensor
public import LeanPool.CaffarelliKohnNirenberg.Foundation.WeakDerivOneDim
public import LeanPool.CaffarelliKohnNirenberg.Foundation.ParabolicMeasure
public import LeanPool.CaffarelliKohnNirenberg.Leray.CompactnessWeak
public import Mathlib.Analysis.Normed.Lp.SmoothApprox
public import Mathlib.MeasureTheory.Function.L2Space
public import Mathlib.Analysis.Normed.Operator.Extend
public import Mathlib.Analysis.InnerProductSpace.Dual
public import LeanPool.CaffarelliKohnNirenberg.Foundation.Harmonic.InteriorSupSmoothBoundSupport
public import LeanPool.CaffarelliKohnNirenberg.Core.Endgame.UniformCutoffFamilySeparated
public import LeanPool.CaffarelliKohnNirenberg.Pressure.SpatialDerivSupport
public import LeanPool.CaffarelliKohnNirenberg.Pressure.LeibnizLaplacian

/-!
# Weak continuity of the local velocity

The momentum identity gives a weakly continuous representative of the velocity in
`L^3` through the terminal time, as in `lem:weak-cont-L3`.
-/

public section

open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology BigOperators
open CKN CKN.Foundation.Parabolic

local instance : Fact (1 ≤ (2 : ℝ≥0∞)) := ⟨by norm_num⟩

noncomputable section

namespace ESS

@[expose] instance weakContL3SpatialBall_isFiniteMeasure_local :
    IsFiniteMeasure (volume.restrict weakContL3SpatialBall) := by
  refine ⟨?_⟩
  rw [Measure.restrict_apply_univ]
  exact CKN.Foundation.Parabolic.Integration.volume_vec3Ball_lt_top

private theorem weakContL3_momentum_trace_exists
    {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
    {p : ParabolicPoint → ℝ}
    (hS3 : ∀ Φ : ParabolicPoint → Vec3,
      Φ ∈ spaceTimeTestFunction (V := Vec3)
        weakContL3SpatialBall (Ioo (-1 : ℝ) 0) →
      ∫ z in spaceTimeSet weakContL3SpatialBall (Ioo (-1 : ℝ) 0),
        (-(∑ i : Fin 3, u z i * timePartial (fun y => Φ y i) z)
          - ∑ i : Fin 3, ∑ j : Fin 3,
              u z i * u z j * spatialPartial (fun y => Φ y i) j z
          + ∑ i : Fin 3, ∑ j : Fin 3,
              Du z i j * spatialPartial (fun y => Φ y i) j z
          - p z * ∑ i : Fin 3, spatialPartial (fun y => Φ y i) i z) ∂volume = 0)
    {χ : Vec3 → ℝ} (hχsmooth : ContDiff ℝ (⊤ : ℕ∞) χ)
    (hχcompact : HasCompactSupport χ)
    (hχsupport : tsupport χ ⊆ weakContL3SpatialBall)
    (φ : weakContL3SmoothTest)
    (hF : Integrable (weakContL3MomentumPairing u χ φ)
      ((volume.restrict weakContL3SpatialBall).prod
        (volume.restrict (Ioo (-1 : ℝ) 0))))
    (hG : Integrable (weakContL3MomentumFlux u Du p χ φ)
      ((volume.restrict weakContL3SpatialBall).prod
        (volume.restrict (Ioo (-1 : ℝ) 0)))) :
    ∃ ell : ℝ → ℝ, Continuous ell ∧
      ∀ᵐ t ∂(volume.restrict (Ioo (-1 : ℝ) 0)),
        (∫ x, weakContL3MomentumPairing u χ φ (x, t)
          ∂(volume.restrict weakContL3SpatialBall)) = ell t := by
  have hweak := weakContL3_momentum_gives_productWeak
    hS3 hχsmooth hχcompact hχsupport φ
  obtain ⟨hfLoc, hgInt, hderiv⟩ :=
    weakContL3_productWeakDeriv
      (μx := volume.restrict weakContL3SpatialBall)
      (a := (-1 : ℝ)) (b := 0)
      hF hG hweak
  obtain ⟨ell, hellContinuous, hellAE⟩ :=
    weakContL3_scalarTrace_exists (a := (-1 : ℝ)) (b := 0)
      (t₀ := (-1 / 2 : ℝ)) (by norm_num) (by norm_num)
      hfLoc hgInt hderiv
  refine ⟨ell, hellContinuous, ?_⟩
  filter_upwards [ae_restrict_mem measurableSet_Ioo,
    ae_restrict_of_ae hellAE] with t ht ht'
  exact ht' ht

private theorem weakContL3_scalarTrace_unique
    {f g : ℝ → ℝ}
    (hf : Continuous f) (hg : Continuous g)
    (hfu : f =ᵐ[volume.restrict (Ioo (-1 : ℝ) 0)] g) :
    EqOn f g (Icc (-(3 / 4 : ℝ) ^ 2) 0) := by
  have hEqOpen : EqOn f g (Ioo (-1 : ℝ) 0) :=
    Measure.eqOn_open_of_ae_eq hfu isOpen_Ioo hf.continuousOn hg.continuousOn
  have hEqClosed : IsClosed {t : ℝ | f t = g t} :=
    isClosed_eq hf hg
  intro t ht
  have hclosure : t ∈ closure (Ioo (-1 : ℝ) 0) := by
    rw [closure_Ioo (by norm_num : (-1 : ℝ) ≠ 0)]
    exact ⟨by dsimp [Icc] at ht ⊢; linarith only [ht.1], ht.2⟩
  have hsub : Ioo (-1 : ℝ) 0 ⊆ {s : ℝ | f s = g s} := by
    intro s hs
    exact hEqOpen hs
  exact closure_minimal hsub hEqClosed hclosure

private theorem weakContL3_continuous_of_dense_pairing
    {T F : Type*} [PseudoMetricSpace T] [NormedAddCommGroup F]
    (P : T → F → ℝ) (S : Set F) (hS : Dense S)
    (C : ℝ) (hC : 0 ≤ C)
    (hbound : ∀ t x y, |P t x - P t y| ≤ C * ‖x - y‖)
    (hcontinuous : ∀ x ∈ S, Continuous (fun t => P t x)) :
    ∀ x, Continuous (fun t => P t x) := by
  intro x
  rw [continuous_iff_continuousAt]
  intro t₀
  rw [Metric.continuousAt_iff]
  intro ε hε
  let δ : ℝ := ε / (3 * (C + 1))
  have hδ : 0 < δ := by dsimp [δ]; positivity
  obtain ⟨y, hy⟩ := hS.exists_dist_lt x hδ
  have hyS : y ∈ S := hy.1
  have hxy : dist x y < δ := hy.2
  obtain ⟨η, hη, hmiddle⟩ :=
    Metric.continuousAt_iff.mp (hcontinuous y hyS).continuousAt (ε / 3) (by positivity)
  have hfrac : C / (3 * (C + 1)) ≤ (1 / 3 : ℝ) := by
    apply (div_le_iff₀ (by positivity)).2
    nlinarith only [hC]
  have hsmall : C * dist x y ≤ ε / 3 := by
    calc
      C * dist x y ≤ C * δ := mul_le_mul_of_nonneg_left hxy.le hC
      _ = ε * (C / (3 * (C + 1))) := by dsimp [δ]; ring
      _ ≤ ε * (1 / 3) := mul_le_mul_of_nonneg_left hfrac hε.le
      _ = ε / 3 := by ring
  have hleft (t : T) : dist (P t x) (P t y) ≤ C * dist x y := by
    simpa [dist_eq_norm, Real.norm_eq_abs] using hbound t x y
  have hright : dist (P t₀ y) (P t₀ x) ≤ C * dist x y := by
    calc
      dist (P t₀ y) (P t₀ x) = dist (P t₀ x) (P t₀ y) := dist_comm _ _
      _ ≤ C * dist x y := hleft t₀
  refine ⟨η, hη, fun t ht => ?_⟩
  calc
    dist (P t x) (P t₀ x) ≤
        dist (P t x) (P t y) +
          (dist (P t y) (P t₀ y) + dist (P t₀ y) (P t₀ x)) := by
            calc
              dist (P t x) (P t₀ x) ≤
                  dist (P t x) (P t y) + dist (P t y) (P t₀ x) := dist_triangle _ _ _
              _ ≤ _ := by gcongr; exact dist_triangle _ _ _
    _ < ε / 3 + (ε / 3 + ε / 3) := by
      apply add_lt_add_of_le_of_lt (hleft t |>.trans hsmall)
      apply add_lt_add_of_lt_of_le _ (hright.trans hsmall)
      exact hmiddle ht
    _ = ε := by ring

/-- The essential upper bound for the local cubic velocity moment. -/
@[expose] def weakContL3MomentSup {u : ParabolicPoint → Vec3} : ℝ≥0∞ :=
  essSup (fun t : ℝ => ∫⁻ x in weakContL3SpatialBall,
    ENNReal.ofReal (vec3EuclideanNorm (u (x, t))) ^ (3 : ℝ))
    (volume.restrict (Ioo (-1 : ℝ) 0))

/-- The local `L³` bound obtained from the essential cubic moment. -/
@[expose] def weakContL3MomentBound {u : ParabolicPoint → Vec3} : ℝ≥0∞ :=
  weakContL3MomentSup (u := u) ^ (1 / 3 : ℝ)

private theorem weakContL3_slice_bound_ae
    {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
    (hu : AEStronglyMeasurable u
      (volume.restrict
        (spaceTimeSet weakContL3SpatialBall (Ioo (-1 : ℝ) 0))))
    (hDu : AEStronglyMeasurable Du
      (volume.restrict
        (spaceTimeSet weakContL3SpatialBall (Ioo (-1 : ℝ) 0))))
    (henergy : (∫⁻ z in spaceTimeSet weakContL3SpatialBall (Ioo (-1 : ℝ) 0),
      ‖u z‖ₑ ^ (2 : ℝ) + ‖Du z‖ₑ ^ (2 : ℝ)) < ⊤) :
    ∀ᵐ t ∂(volume.restrict (Ioo (-1 : ℝ) 0)),
      eLpNorm (fun x : Vec3 => WithLp.toLp 2 (u (x, t))) 3
        (volume.restrict weakContL3SpatialBall) ≤ weakContL3MomentBound (u := u) := by
  let μx : Measure Vec3 := volume.restrict weakContL3SpatialBall
  let μt : Measure ℝ := volume.restrict (Ioo (-1 : ℝ) 0)
  have henergyLp := energyL2_components_memLp hu hDu henergy
  have hu2Product : MemLp (fun z : Vec3 × ℝ => u z) 2
      ((volume : Measure (Vec3 × ℝ)).restrict
        (weakContL3SpatialBall ×ˢ Ioo (-1 : ℝ) 0)) :=
    localEnergy_memLp_parabolic_to_product henergyLp.1
  have hmeasure : μx.prod μt =
      (volume : Measure (Vec3 × ℝ)).restrict
        (weakContL3SpatialBall ×ˢ Ioo (-1 : ℝ) 0) := by
    rw [Measure.prod_restrict, ← Measure.volume_eq_prod Vec3 ℝ]
  rw [← hmeasure] at hu2Product
  have hsliceMeas : ∀ᵐ t ∂μt,
      AEStronglyMeasurable (fun x : Vec3 => WithLp.toLp 2 (u (x, t))) μx := by
    have h := hu2Product.aestronglyMeasurable.prodMk_right
    filter_upwards [h] with t ht
    exact weakContL3VecToLp.continuous.comp_aestronglyMeasurable ht
  have hsup := ENNReal.ae_le_essSup (μ := μt)
    (fun t : ℝ => ∫⁻ x in weakContL3SpatialBall,
      ENNReal.ofReal (vec3EuclideanNorm (u (x, t))) ^ (3 : ℝ))
  filter_upwards [hsup, hsliceMeas] with t hsup_t htMeas
  have hformula := eLpNorm_three_pow_eq_lintegral
    (μ := μx) (f := fun x : Vec3 => WithLp.toLp 2 (u (x, t))) htMeas
  have hpoint (x : Vec3) :
      ‖WithLp.toLp 2 (u (x, t))‖ₑ ^ (3 : ℝ) =
        ENNReal.ofReal (vec3EuclideanNorm (u (x, t))) ^ (3 : ℝ) := by
    congr 1
    rw [← ofReal_norm, vec3EuclideanNorm_eq_l2]
  have hInt : (∫⁻ x, ‖WithLp.toLp 2 (u (x, t))‖ₑ ^ (3 : ℝ) ∂μx) ≤
      ∫⁻ x in weakContL3SpatialBall,
        ENNReal.ofReal (vec3EuclideanNorm (u (x, t))) ^ (3 : ℝ) := by
    calc
      (∫⁻ x, ‖WithLp.toLp 2 (u (x, t))‖ₑ ^ (3 : ℝ) ∂μx) =
          ∫⁻ x, ENNReal.ofReal (vec3EuclideanNorm (u (x, t))) ^ (3 : ℝ)
            ∂μx := lintegral_congr_ae (Eventually.of_forall hpoint)
      _ ≤ ∫⁻ x in weakContL3SpatialBall,
          ENNReal.ofReal (vec3EuclideanNorm (u (x, t))) ^ (3 : ℝ) := by
        rfl
  have hroot : eLpNorm (fun x : Vec3 => WithLp.toLp 2 (u (x, t))) 3 μx =
      (∫⁻ x, ‖WithLp.toLp 2 (u (x, t))‖ₑ ^ (3 : ℝ) ∂μx) ^ (1 / 3 : ℝ) := by
    calc
      _ = (eLpNorm (fun x : Vec3 => WithLp.toLp 2 (u (x, t))) 3 μx ^
          (3 : ℝ)) ^ (1 / 3 : ℝ) := by
            rw [← ENNReal.rpow_mul]
            norm_num
      _ = _ := congrArg (fun a : ℝ≥0∞ => a ^ (1 / 3 : ℝ)) hformula
  calc
    eLpNorm (fun x : Vec3 => WithLp.toLp 2 (u (x, t))) 3 μx =
        (∫⁻ x, ‖WithLp.toLp 2 (u (x, t))‖ₑ ^ (3 : ℝ) ∂μx) ^
          (1 / 3 : ℝ) := hroot
    _ ≤ (∫⁻ x in weakContL3SpatialBall,
        ENNReal.ofReal (vec3EuclideanNorm (u (x, t))) ^ (3 : ℝ)) ^
          (1 / 3 : ℝ) := ENNReal.rpow_le_rpow hInt (by norm_num)
    _ ≤ weakContL3MomentBound (u := u) := by
      exact ENNReal.rpow_le_rpow hsup_t (by norm_num)

private theorem weakContL3_trace_family
    {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
    {p : ParabolicPoint → ℝ}
    (hS3 : ∀ Φ : ParabolicPoint → Vec3,
      Φ ∈ spaceTimeTestFunction (V := Vec3)
        weakContL3SpatialBall (Ioo (-1 : ℝ) 0) →
      ∫ z in spaceTimeSet weakContL3SpatialBall (Ioo (-1 : ℝ) 0),
        (-(∑ i : Fin 3, u z i * timePartial (fun y => Φ y i) z)
          - ∑ i : Fin 3, ∑ j : Fin 3,
              u z i * u z j * spatialPartial (fun y => Φ y i) j z
          + ∑ i : Fin 3, ∑ j : Fin 3,
              Du z i j * spatialPartial (fun y => Φ y i) j z
          - p z * ∑ i : Fin 3, spatialPartial (fun y => Φ y i) i z)
          ∂volume = 0)
    {χ : Vec3 → ℝ} (hχsmooth : ContDiff ℝ (⊤ : ℕ∞) χ)
    (hχcompact : HasCompactSupport χ)
    (hχsupport : tsupport χ ⊆ weakContL3SpatialBall)
    (hU4 : MemLp (fun z : Vec3 × ℝ => u (parabolicHomeomorph.symm z)) 4
      ((volume.restrict weakContL3SpatialBall).prod
        (volume.restrict (Ioo (-1 : ℝ) 0))))
    (hDu2 : MemLp (fun z : Vec3 × ℝ => Du (parabolicHomeomorph.symm z)) 2
      ((volume.restrict weakContL3SpatialBall).prod
        (volume.restrict (Ioo (-1 : ℝ) 0))))
    (hp : MemLp (fun z : Vec3 × ℝ => p (parabolicHomeomorph.symm z))
      (ENNReal.ofReal (3 / 2 : ℝ))
      ((volume.restrict weakContL3SpatialBall).prod
        (volume.restrict (Ioo (-1 : ℝ) 0)))) :
    ∃ ψ : ℕ → Vec3 → L2Vec3,
      ∃ hψsmooth : ∀ n, HasCompactSupport (ψ n) ∧ ContDiff ℝ (⊤ : ℕ∞) (ψ n),
      ∃ hψ : ∀ n, MemLp (ψ n) 2 (volume.restrict weakContL3SpatialBall),
        DenseRange (fun n => (hψ n).toLp) ∧
        ∃ ell : ℕ → ℝ → ℝ,
          (∀ n, Continuous (ell n)) ∧
          ∀ᵐ t ∂(volume.restrict (Ioo (-1 : ℝ) 0)), ∀ n,
            (∫ x, weakContL3MomentumPairing u χ
              (⟨ψ n, (hψsmooth n).1, (hψsmooth n).2⟩ :
                weakContL3SmoothTest) (x, t)
              ∂(volume.restrict weakContL3SpatialBall)) = ell n t := by
  obtain ⟨ψ, hψsmooth, hψ⟩ :=
    weakContL3_exists_countable_dense_tests (volume.restrict weakContL3SpatialBall)
  obtain ⟨hψ, hψdense⟩ := hψ
  let φ : ℕ → weakContL3SmoothTest := fun n =>
    ⟨ψ n, (hψsmooth n).1, (hψsmooth n).2⟩
  have hterms (n : ℕ) := weakContL3_momentumTerms_integrable
    hU4 hDu2 hp hχsmooth hχcompact (φ n)
  have htraces (n : ℕ) := weakContL3_momentum_trace_exists
    hS3 hχsmooth hχcompact hχsupport (φ n) (hterms n).1 (hterms n).2
  let ell : ℕ → ℝ → ℝ := fun n => Classical.choose (htraces n)
  have hell : ∀ n, Continuous (ell n) := fun n =>
    (Classical.choose_spec (htraces n)).1
  refine ⟨ψ, hψsmooth, hψ, hψdense, ell, hell, ?_⟩
  apply ae_all_iff.mpr
  intro n
  exact (Classical.choose_spec (htraces n)).2

private theorem weakContL3_cutoff_pairing_eq_inner
    {u : ParabolicPoint → Vec3} {χ : Vec3 → ℝ}
    (φ : weakContL3SmoothTest) (t : ℝ)
    (hχu : MemLp (fun x : Vec3 =>
      χ x • WithLp.toLp 2 (u (parabolicHomeomorph.symm (x, t)))) 2
      (volume.restrict weakContL3SpatialBall)) :
    inner ℝ (hχu.toLp _) ((φ.property.2.continuous.memLp_of_hasCompactSupport
      φ.property.1).toLp φ) =
      ∫ x, weakContL3MomentumPairing u χ φ (x, t)
        ∂(volume.restrict weakContL3SpatialBall) := by
  rw [MeasureTheory.L2.inner_def]
  have hpoint (x : Vec3) :
      inner ℝ (χ x • WithLp.toLp 2
        (u (parabolicHomeomorph.symm (x, t)))) ((φ : Vec3 → L2Vec3) x) =
        weakContL3MomentumPairing u χ φ (x, t) := by
    simp [weakContL3MomentumPairing, weakContL3CutoffTest,
      weakContL3OfLp, PiLp.inner_apply,
      parabolicHomeomorph_symm_apply]
    apply Finset.sum_congr rfl
    intro i hi
    ring
  apply integral_congr_ae
  filter_upwards [hχu.coeFn_toLp,
    (φ.property.2.continuous.memLp_of_hasCompactSupport
      φ.property.1).coeFn_toLp] with x h₁ h₂
  rw [h₁, h₂]
  exact hpoint x

private theorem weakContL3_exists_good_near
    {good : ℝ → Prop}
    (hgood : ∀ᵐ s ∂(volume.restrict (Ioo (-1 : ℝ) 0)), good s)
    {t ε : ℝ} (ht : t ∈ Icc (-(3 / 4 : ℝ) ^ 2) 0) (hε : 0 < ε) :
    ∃ s, s ∈ Ioo (-1 : ℝ) 0 ∧ good s ∧ dist s t < ε := by
  let J : Set ℝ := Ioo (max (-1 : ℝ) (t - ε)) (min 0 (t + ε))
  have htlo : -1 < t := by
    dsimp [Icc] at ht
    nlinarith only [ht.1]
  have hthi : t ≤ 0 := ht.2
  have hleft : max (-1 : ℝ) (t - ε) < t :=
    max_lt_iff.mpr ⟨htlo, by linarith only [hε]⟩
  have hright : t ≤ min 0 (t + ε) := le_min hthi (by linarith only [hε])
  have hJnonempty : max (-1 : ℝ) (t - ε) < min 0 (t + ε) := lt_of_lt_of_le hleft hright
  have hJsubset : J ⊆ Ioo (-1 : ℝ) 0 := by
    intro s hs
    refine ⟨lt_of_le_of_lt (le_max_left _ _) hs.1, lt_of_lt_of_le hs.2 (min_le_left _ _)⟩
  have hJmeas : MeasurableSet J := isOpen_Ioo.measurableSet
  have hJpos : (volume.restrict (Ioo (-1 : ℝ) 0)) J > 0 := by
    rw [Measure.restrict_apply hJmeas]
    rw [Set.inter_eq_left.mpr hJsubset, Real.volume_Ioo]
    exact ENNReal.ofReal_pos.mpr (sub_pos.mpr hJnonempty)
  have hbad : (volume.restrict (Ioo (-1 : ℝ) 0)) {s | ¬ good s} = 0 := ae_iff.mp hgood
  have hexists : ∃ s ∈ J, good s := by
    by_contra h
    have hsub : J ⊆ {s | ¬ good s} := by
      intro s hs
      by_contra hgs
      exact h ⟨s, hs, not_not.mp hgs⟩
    have hzero := measure_mono_null hsub hbad
    exact (ne_of_gt hJpos) hzero
  obtain ⟨s, hsJ, hgs⟩ := hexists
  refine ⟨s, hJsubset hsJ, hgs, ?_⟩
  rw [Real.dist_eq, abs_lt]
  constructor
  · have hεs : t - ε < s := lt_of_le_of_lt (le_max_right _ _) hsJ.1
    linarith only [hεs]
  · have hsε : s < t + ε := lt_of_lt_of_le hsJ.2 (min_le_right _ _)
    linarith only [hsε]

/-- An all-time weakly continuous local `L²` representative with a scale-aware
`L²` bound and the `L³`-controlled pairing estimate. -/
theorem weakContL3_l2Representative
    {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
    {p : ParabolicPoint → ℝ}
    (hu : AEStronglyMeasurable u
      (volume.restrict
        (spaceTimeSet weakContL3SpatialBall (Ioo (-1 : ℝ) 0))))
    (hDu : AEStronglyMeasurable Du
      (volume.restrict
        (spaceTimeSet weakContL3SpatialBall (Ioo (-1 : ℝ) 0))))
    (henergy : (∫⁻ z in spaceTimeSet weakContL3SpatialBall (Ioo (-1 : ℝ) 0),
      ‖u z‖ₑ ^ (2 : ℝ) + ‖Du z‖ₑ ^ (2 : ℝ)) < ⊤)
    (hL3 : weakContL3MomentSup (u := u) < ⊤)
    (hp : MemLp p (ENNReal.ofReal (3 / 2 : ℝ))
      (volume.restrict
        (spaceTimeSet weakContL3SpatialBall (Ioo (-1 : ℝ) 0))))
    (hgrad : ∀ᵐ t ∂(volume.restrict (Ioo (-1 : ℝ) 0)), ∀ i : Fin 3,
      HasWeakGradientOn weakContL3SpatialBall
        (fun x => u (x, t) i) (fun x => Du (x, t) i))
    (hS3 : ∀ Φ : ParabolicPoint → Vec3,
      Φ ∈ spaceTimeTestFunction (V := Vec3)
        weakContL3SpatialBall (Ioo (-1 : ℝ) 0) →
      ∫ z in spaceTimeSet weakContL3SpatialBall (Ioo (-1 : ℝ) 0),
        (-(∑ i : Fin 3, u z i * timePartial (fun y => Φ y i) z)
          - ∑ i : Fin 3, ∑ j : Fin 3,
              u z i * u z j * spatialPartial (fun y => Φ y i) j z
          + ∑ i : Fin 3, ∑ j : Fin 3,
              Du z i j * spatialPartial (fun y => Φ y i) j z
          - p z * ∑ i : Fin 3, spatialPartial (fun y => Φ y i) i z)
          ∂volume = 0) :
    ∃ v : Icc (-(3 / 4 : ℝ) ^ 2) 0 →
        Lp L2Vec3 2 (volume.restrict weakContL3SpatialBall),
      (∀ t, ‖v t‖ ≤
        (weakContL3MomentBound (u := u) *
          (volume.restrict weakContL3SpatialBall Set.univ) ^ (1 / 6 : ℝ)).toReal) ∧
      (∀ w : Lp L2Vec3 2 (volume.restrict weakContL3SpatialBall),
        Continuous (fun t => inner ℝ (v t) w)) ∧
      (∀ t w, |inner ℝ (v t) w| ≤
        (weakContL3MomentBound (u := u)).toReal *
          ‖weakContL3L2ToLThreeHalves
            (volume.restrict weakContL3SpatialBall) w‖) ∧
      (∀ᵐ t ∂(volume.restrict (Ioo (-(3 / 4 : ℝ) ^ 2) 0)),
        ∃ ht : t ∈ Icc (-(3 / 4 : ℝ) ^ 2) 0,
          ∃ hm : MemLp (fun x : Vec3 =>
            (Classical.choose (weakContL3_cutoff_exists)) x •
              WithLp.toLp 2 (u (parabolicHomeomorph.symm (x, t)))) 2
              (volume.restrict weakContL3SpatialBall),
              v ⟨t, ht⟩ = hm.toLp _) ∧
      ∀ᵐ t ∂(volume.restrict (Ioo (-(3 / 4 : ℝ) ^ 2) 0)),
        t ∈ Icc (-(3 / 4 : ℝ) ^ 2) 0 ∧
          MemLp (fun x : Vec3 => WithLp.toLp 2 (u (x, t))) 3
            (volume.restrict (vec3Ball (0 : Vec3) (3 / 4 : ℝ))) ∧
          eLpNorm (fun x : Vec3 => WithLp.toLp 2 (u (x, t))) 3
            (volume.restrict (vec3Ball (0 : Vec3) (3 / 4 : ℝ))) ≤
              weakContL3MomentBound (u := u) := by
  classical
  let χ : Vec3 → ℝ := Classical.choose weakContL3_cutoff_exists
  let μx : Measure Vec3 := volume.restrict weakContL3SpatialBall
  let μt : Measure ℝ := volume.restrict (Ioo (-1 : ℝ) 0)
  let M : ℝ≥0∞ := weakContL3MomentBound (u := u)
  let B : ℝ≥0∞ := M * μx Set.univ ^ (1 / 6 : ℝ)
  have hM : M < ⊤ := by
    dsimp [M, weakContL3MomentBound, weakContL3MomentSup]
    exact ENNReal.rpow_lt_top_of_nonneg (by norm_num) hL3.ne
  have hχdata := Classical.choose_spec weakContL3_cutoff_exists
  rcases hχdata with ⟨hχsmooth, hχcompact, hχsupport, hχrange, hχone⟩
  obtain ⟨ψ, hψsmooth, hψ, hψdense, ell, hell, htrace⟩ :=
    weakContL3_trace_family hS3 hχsmooth hχcompact hχsupport
      (by
        have hu4 := velocity_memLp_four_unit_of_essLocalData
          (u := u) (Du := Du) hu hDu henergy hL3 hgrad
        have hprod := localEnergy_memLp_parabolic_to_product hu4
        rw [Measure.prod_restrict, ← Measure.volume_eq_prod Vec3 ℝ]
        simpa [weakContL3SpatialBall, parabolicHomeomorph_symm_apply] using hprod)
      (by
        have hDuLp := energyL2_components_memLp hu hDu henergy
        have hprod := localEnergy_memLp_parabolic_to_product hDuLp.2
        rw [Measure.prod_restrict, ← Measure.volume_eq_prod Vec3 ℝ]
        simpa [weakContL3SpatialBall, parabolicHomeomorph_symm_apply] using hprod)
      (by
        have hprod := localEnergy_memLp_parabolic_to_product hp
        rw [Measure.prod_restrict, ← Measure.volume_eq_prod Vec3 ℝ]
        simpa [weakContL3SpatialBall, parabolicHomeomorph_symm_apply] using hprod)
  have hslice3 := weakContL3_slice_bound_ae hu hDu henergy
  have henergyLp := energyL2_components_memLp hu hDu henergy
  have hu2Product : MemLp (fun z : Vec3 × ℝ => u z) 2
      ((volume : Measure (Vec3 × ℝ)).restrict
        (weakContL3SpatialBall ×ˢ Ioo (-1 : ℝ) 0)) :=
    localEnergy_memLp_parabolic_to_product henergyLp.1
  have hproductMeasure : μx.prod μt =
      (volume : Measure (Vec3 × ℝ)).restrict
        (weakContL3SpatialBall ×ˢ Ioo (-1 : ℝ) 0) := by
    rw [Measure.prod_restrict, ← Measure.volume_eq_prod Vec3 ℝ]
  rw [← hproductMeasure] at hu2Product
  have huSliceMeas : ∀ᵐ t ∂μt,
      AEStronglyMeasurable (fun x : Vec3 => WithLp.toLp 2 (u (x, t))) μx := by
    have hs := hu2Product.aestronglyMeasurable.prodMk_right
    filter_upwards [hs] with t ht
    exact weakContL3VecToLp.continuous.comp_aestronglyMeasurable ht
  have hgood : ∀ᵐ t ∂μt,
      t ∈ Ioo (-1 : ℝ) 0 ∧
      AEStronglyMeasurable (fun x : Vec3 => χ x • WithLp.toLp 2 (u (x, t))) μx ∧
      eLpNorm (fun x : Vec3 => χ x • WithLp.toLp 2 (u (x, t))) 3 μx ≤ M ∧
      ∀ n, (∫ x, weakContL3MomentumPairing u χ
        (⟨ψ n, (hψsmooth n).1, (hψsmooth n).2⟩ : weakContL3SmoothTest)
        (x, t) ∂μx) = ell n t := by
    filter_upwards [ae_restrict_mem measurableSet_Ioo, huSliceMeas,
      hslice3, htrace] with t ht hmeas h3 hpair
    have hχmeas : AEStronglyMeasurable χ μx := hχsmooth.continuous.aestronglyMeasurable
    have hcutmeas := hχmeas.smul hmeas
    have hcutnorm (x : Vec3) :
        ‖χ x • WithLp.toLp 2 (u (x, t))‖ ≤
          ‖WithLp.toLp 2 (u (x, t))‖ := by
      rw [norm_smul]
      have hχabs : ‖χ x‖ ≤ 1 := by
        rw [Real.norm_eq_abs, abs_of_nonneg (hχrange x).1]
        exact (hχrange x).2
      calc
        ‖χ x‖ * ‖WithLp.toLp 2 (u (x, t))‖ ≤
            1 * ‖WithLp.toLp 2 (u (x, t))‖ :=
              mul_le_mul_of_nonneg_right hχabs (norm_nonneg _)
        _ = _ := one_mul _
    have hcut3 : eLpNorm (fun x : Vec3 => χ x • WithLp.toLp 2 (u (x, t))) 3 μx ≤ M := by
      exact (eLpNorm_mono hcutmeas hcutnorm).trans h3
    exact ⟨ht, hcutmeas, hcut3, hpair⟩
  have hBtop : B < ⊤ := by
    dsimp [B]
    exact ENNReal.mul_lt_top hM (ENNReal.rpow_lt_top_of_nonneg (by norm_num)
      (by finiteness))
  have hC : 0 ≤ B.toReal := ENNReal.toReal_nonneg
  have hCμ : IsFiniteMeasure μx := by infer_instance
  have hCutMemLp (t : ℝ) (htgood : AEStronglyMeasurable
      (fun x : Vec3 => χ x • WithLp.toLp 2 (u (x, t))) μx)
      (h3t : eLpNorm (fun x : Vec3 => χ x • WithLp.toLp 2 (u (x, t))) 3 μx ≤ M) :
      MemLp (fun x : Vec3 => χ x • WithLp.toLp 2 (u (x, t))) 2 μx := by
    have h3mem : MemLp (fun x : Vec3 => χ x • WithLp.toLp 2 (u (x, t))) 3 μx := by
      rw [memLp_iff]
      exact lt_of_le_of_lt h3t hM
    exact h3mem.mono_exponent (by norm_num)
  let C : ℝ := B.toReal
  have hCnonneg : 0 ≤ C := by simp [C]
  have hBmeasure : μx Set.univ < ⊤ := by finiteness
  have hBoundSlice (t : ℝ) (hmeas : AEStronglyMeasurable
      (fun x : Vec3 => χ x • WithLp.toLp 2 (u (x, t))) μx)
      (h3t : eLpNorm (fun x : Vec3 => χ x • WithLp.toLp 2 (u (x, t))) 3 μx ≤ M) :
      ‖(hCutMemLp t hmeas h3t).toLp _‖ ≤ C := by
    rw [Lp.norm_toLp]
    apply ENNReal.toReal_mono hBtop.ne
    calc
      eLpNorm (fun x : Vec3 => χ x • WithLp.toLp 2 (u (x, t))) 2 μx ≤
          eLpNorm (fun x : Vec3 => χ x • WithLp.toLp 2 (u (x, t))) 3 μx *
            μx Set.univ ^ (1 / 6 : ℝ) := by
              have hcompare := eLpNorm_le_eLpNorm_mul_rpow_measure_univ
                (p := (2 : ℝ≥0∞)) (q := 3) (by norm_num) hmeas
              have hexp : 1 / ENNReal.toReal (2 : ℝ≥0∞) -
                  1 / ENNReal.toReal (3 : ℝ≥0∞) = 1 / 6 := by norm_num
              rw [← hexp]
              exact hcompare
      _ ≤ B := by
        dsimp [B, M]
        exact mul_le_mul_of_nonneg_right h3t (by positivity)
  have hgoodAE : ∀ᵐ t ∂μt,
      t ∈ Ioo (-1 : ℝ) 0 ∧
      AEStronglyMeasurable (fun x : Vec3 => χ x • WithLp.toLp 2 (u (x, t))) μx ∧
      eLpNorm (fun x : Vec3 => χ x • WithLp.toLp 2 (u (x, t))) 3 μx ≤ M ∧
      ∀ n, (∫ x, weakContL3MomentumPairing u χ
        (⟨ψ n, (hψsmooth n).1, (hψsmooth n).2⟩ : weakContL3SmoothTest)
        (x, t) ∂μx) = ell n t := hgood
  let sample : (t : Icc (-(3 / 4 : ℝ) ^ 2) 0) → ℕ → ℝ := fun t n =>
    Classical.choose (weakContL3_exists_good_near hgoodAE
      (t := t) (ε := 1 / (n + 1 : ℝ)) t.property (by positivity))
  have hsample (t : Icc (-(3 / 4 : ℝ) ^ 2) 0) (n : ℕ) :
      sample t n ∈ Ioo (-1 : ℝ) 0 ∧
        (sample t n ∈ Ioo (-1 : ℝ) 0 ∧
          AEStronglyMeasurable (fun x : Vec3 =>
            χ x • WithLp.toLp 2 (u (x, sample t n))) μx ∧
          eLpNorm (fun x : Vec3 =>
            χ x • WithLp.toLp 2 (u (x, sample t n))) 3 μx ≤ M ∧
          (∀ m, (∫ x, weakContL3MomentumPairing u χ
            (⟨ψ m, (hψsmooth m).1, (hψsmooth m).2⟩ : weakContL3SmoothTest)
            (x, sample t n) ∂μx) = ell m (sample t n))) ∧
        dist (sample t n) t < 1 / (n + 1 : ℝ) :=
    Classical.choose_spec
      (weakContL3_exists_good_near hgoodAE
        (t := t) (ε := 1 / (n + 1 : ℝ)) t.property (by positivity))
  let slice (t : Icc (-(3 / 4 : ℝ) ^ 2) 0) (n : ℕ) :
      Lp L2Vec3 2 μx :=
    (hCutMemLp (sample t n) (hsample t n).2.1.2.1
      (hsample t n).2.1.2.2.1).toLp _
  have hsliceBound (t : Icc (-(3 / 4 : ℝ) ^ 2) 0) (n : ℕ) :
      ‖slice t n‖ ≤ C := by
    exact hBoundSlice (sample t n) (hsample t n).2.1.2.1
      (hsample t n).2.1.2.2.1
  have hinverse (m : ℕ) :
      (hψ m).toLp (ψ m) =
        (weakContL3_smoothTest_memLp
          (⟨ψ m, (hψsmooth m).1, (hψsmooth m).2⟩ : weakContL3SmoothTest)).toLp
            (⟨ψ m, (hψsmooth m).1, (hψsmooth m).2⟩ : weakContL3SmoothTest) := by
    apply Lp.ext
    filter_upwards [(hψ m).coeFn_toLp,
      (weakContL3_smoothTest_memLp
        (⟨ψ m, (hψsmooth m).1, (hψsmooth m).2⟩ : weakContL3SmoothTest)).coeFn_toLp]
      with x h₁ h₂
    exact h₁.trans h₂.symm
  have hpairTendsto (t : Icc (-(3 / 4 : ℝ) ^ 2) 0) (m : ℕ) :
      Tendsto (fun n => inner ℝ (slice t n) ((hψ m).toLp (ψ m))) atTop
        (nhds (ell m t)) := by
    have htest (n : ℕ) : inner ℝ (slice t n) ((hψ m).toLp (ψ m)) =
        ell m (sample t n) := by
      calc
        inner ℝ (slice t n) ((hψ m).toLp (ψ m)) =
            inner ℝ (slice t n)
              ((weakContL3_smoothTest_memLp
                (⟨ψ m, (hψsmooth m).1, (hψsmooth m).2⟩ :
                  weakContL3SmoothTest)).toLp
                (⟨ψ m, (hψsmooth m).1, (hψsmooth m).2⟩ :
                  weakContL3SmoothTest)) := by rw [hinverse m]
        _ = ∫ x, weakContL3MomentumPairing u χ
              (⟨ψ m, (hψsmooth m).1, (hψsmooth m).2⟩ :
                weakContL3SmoothTest) (x, sample t n) ∂μx :=
              weakContL3_cutoff_pairing_eq_inner
                (⟨ψ m, (hψsmooth m).1, (hψsmooth m).2⟩ :
                  weakContL3SmoothTest) (sample t n)
                (hCutMemLp (sample t n) (hsample t n).2.1.2.1
                  (hsample t n).2.1.2.2.1)
        _ = ell m (sample t n) := (hsample t n).2.1.2.2.2 m
    have hsampleTendsto : Tendsto (sample t) atTop (nhds t) := by
      have hrecip : Tendsto (fun n : ℕ => (1 : ℝ) / (n + 1)) atTop (nhds 0) := by
        simpa using (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
      apply Metric.tendsto_nhds.mpr
      intro ε hε
      filter_upwards [hrecip.eventually (isOpen_Iio.mem_nhds hε)] with n hn
      exact (hsample t n).2.2.trans hn
    have hcont := (hell m).continuousAt.tendsto.comp hsampleTendsto
    exact hcont.congr' (Filter.Eventually.of_forall fun n => (htest n).symm)
  have hweakExists (t : Icc (-(3 / 4 : ℝ) ^ 2) 0) :
      ∃ w : Lp L2Vec3 2 μx, ∀ x,
        Tendsto (fun n => inner ℝ (slice t n) x) atTop (nhds (inner ℝ w x)) := by
    exact CKN.Leray.exists_weak_limit_of_tendsto_pairings_on_dense_range
      (slice t) C hCnonneg (hsliceBound t) (fun n => (hψ n).toLp (ψ n))
      hψdense (fun m => ⟨ell m t, hpairTendsto t m⟩)
  let v : Icc (-(3 / 4 : ℝ) ^ 2) 0 → Lp L2Vec3 2 μx :=
    fun t => Classical.choose (hweakExists t)
  have hvweak (t : Icc (-(3 / 4 : ℝ) ^ 2) 0) (x : Lp L2Vec3 2 μx) :
      Tendsto (fun n => inner ℝ (slice t n) x) atTop (nhds (inner ℝ (v t) x)) :=
    Classical.choose_spec (hweakExists t) x
  have hvbound (t : Icc (-(3 / 4 : ℝ) ^ 2) 0) : ‖v t‖ ≤ C :=
    CKN.Leray.norm_le_of_weak_tendsto_of_uniform_bound
      hCnonneg (hsliceBound t) (hvweak t)
  have htestval (t : Icc (-(3 / 4 : ℝ) ^ 2) 0) (m : ℕ) :
      inner ℝ (v t) ((hψ m).toLp (ψ m)) = ell m t :=
    tendsto_nhds_unique (hvweak t ((hψ m).toLp (ψ m))) (hpairTendsto t m)
  have hpairDenseBound (t : Icc (-(3 / 4 : ℝ) ^ 2) 0) (m : ℕ) :
      |inner ℝ (v t) ((hψ m).toLp (ψ m))| ≤
        M.toReal * ‖weakContL3L2ToLThreeHalves μx ((hψ m).toLp (ψ m))‖ := by
    let φ : weakContL3SmoothTest :=
      ⟨ψ m, (hψsmooth m).1, (hψsmooth m).2⟩
    have hseq (n : ℕ) :
        |inner ℝ (slice t n) ((hψ m).toLp (ψ m))| ≤
          M.toReal * ‖weakContL3L2ToLThreeHalves μx ((hψ m).toLp (ψ m))‖ := by
      have hcut2 := hCutMemLp (sample t n) (hsample t n).2.1.2.1
        (hsample t n).2.1.2.2.1
      have hcut3 : MemLp (fun x : Vec3 => χ x •
          WithLp.toLp 2 (u (x, sample t n))) 3 μx := by
        rw [memLp_iff]
        exact lt_of_le_of_lt (hsample t n).2.1.2.2.1 hM
      have hψ₃₂ : MemLp (ψ m) (ENNReal.ofReal (3 / 2 : ℝ)) μx :=
        (hψsmooth m).2.continuous.memLp_of_hasCompactSupport (hψsmooth m).1
      have hholder := weakContL3_inner_holder hcut2 (hψ m) hcut3 hψ₃₂
      have hMreal : (eLpNorm (fun x : Vec3 => χ x •
          WithLp.toLp 2 (u (x, sample t n))) 3 μx).toReal ≤ M.toReal :=
        ENNReal.toReal_mono hM.ne (hsample t n).2.1.2.2.1
      have hnormTest :
          (eLpNorm (ψ m) (ENNReal.ofReal (3 / 2 : ℝ)) μx).toReal =
            ‖weakContL3L2ToLThreeHalves μx ((hψ m).toLp (ψ m))‖ := by
        change (eLpNorm (ψ m) (ENNReal.ofReal (3 / 2 : ℝ)) μx).toReal =
          ‖((Lp.memLp ((hψ m).toLp (ψ m))).mono_exponent
            (p := ENNReal.ofReal (3 / 2 : ℝ)) (q := (2 : ℝ≥0∞))
            (by norm_num)).toLp ((hψ m).toLp (ψ m))‖
        rw [Lp.norm_toLp, eLpNorm_congr_ae (hψ m).coeFn_toLp]
      calc
        |inner ℝ (slice t n) ((hψ m).toLp (ψ m))| ≤
            (eLpNorm (fun x : Vec3 => χ x •
              WithLp.toLp 2 (u (x, sample t n))) 3 μx).toReal *
              (eLpNorm (ψ m) (ENNReal.ofReal (3 / 2 : ℝ)) μx).toReal := by
                exact hholder
        _ ≤ M.toReal *
              (eLpNorm (ψ m) (ENNReal.ofReal (3 / 2 : ℝ)) μx).toReal :=
                mul_le_mul_of_nonneg_right hMreal ENNReal.toReal_nonneg
        _ = _ := by rw [hnormTest]
    have hlim := (continuous_abs.continuousAt.tendsto).comp (hpairTendsto t m)
    have hlimitBound := le_of_tendsto' hlim hseq
    simpa [htestval t m] using hlimitBound
  have hpairBound (t : Icc (-(3 / 4 : ℝ) ^ 2) 0) :
      ∀ w : Lp L2Vec3 2 μx,
        |inner ℝ (v t) w| ≤ M.toReal * ‖weakContL3L2ToLThreeHalves μx w‖ :=
    weakContL3_pairing_bound_of_dense μx (fun m => (hψ m).toLp (ψ m))
      hψdense (v t) M.toReal (hpairDenseBound t)
  have hvabs (t : Icc (-(3 / 4 : ℝ) ^ 2) 0) (w : Lp L2Vec3 2 μx) :
      |inner ℝ (v t) w| ≤ C * ‖w‖ := by
    exact (abs_real_inner_le_norm (v t) w).trans
      (mul_le_mul_of_nonneg_right (hvbound t) (norm_nonneg _))
  have hcontinuous (w : Lp L2Vec3 2 μx) :
      Continuous (fun t : Icc (-(3 / 4 : ℝ) ^ 2) 0 => inner ℝ (v t) w) := by
    have hdensecont (m : ℕ) :
        Continuous (fun t : Icc (-(3 / 4 : ℝ) ^ 2) 0 =>
          inner ℝ (v t) ((hψ m).toLp (ψ m))) := by
      have heq : (fun t : Icc (-(3 / 4 : ℝ) ^ 2) 0 =>
          inner ℝ (v t) ((hψ m).toLp (ψ m))) =
          (fun t : Icc (-(3 / 4 : ℝ) ^ 2) 0 => ell m (t : ℝ)) := by
        funext t
        exact htestval t m
      rw [heq]
      exact (hell m).comp continuous_subtype_val
    exact (CKN.Leray.continuous_inner_of_dense_test_continuous v
      (fun m => (hψ m).toLp (ψ m)) hψdense C hCnonneg hvabs hdensecont) w
  refine ⟨v, hvbound, hcontinuous, ?_, ?_, ?_⟩
  · exact hpairBound
  have hsmallsubset : Ioo (-(3 / 4 : ℝ) ^ 2) 0 ⊆ Ioo (-1 : ℝ) 0 := by
    intro t ht
    refine ⟨?_, ht.2⟩
    dsimp [Ioo] at ht ⊢
    linarith only [ht.1]
  have hgoodSmall := ae_restrict_of_ae_restrict_of_subset hsmallsubset hgoodAE
  filter_upwards [hgoodSmall, ae_restrict_mem measurableSet_Ioo] with t htgood htI
  have htT : t ∈ Icc (-(3 / 4 : ℝ) ^ 2) 0 := ⟨le_of_lt htI.1, le_of_lt htI.2⟩
  let hm : MemLp (fun x : Vec3 => χ x • WithLp.toLp 2 (u (x, t))) 2 μx :=
    hCutMemLp t htgood.2.1 htgood.2.2.1
  have heqtest (n : ℕ) :
      inner ℝ (v ⟨t, htT⟩) ((hψ n).toLp (ψ n)) =
        inner ℝ (hm.toLp _) ((hψ n).toLp (ψ n)) := by
    calc
      inner ℝ (v ⟨t, htT⟩) ((hψ n).toLp (ψ n)) = ell n t := by
        exact htestval ⟨t, htT⟩ n
      _ = ∫ x, weakContL3MomentumPairing u χ
            (⟨ψ n, (hψsmooth n).1, (hψsmooth n).2⟩ : weakContL3SmoothTest)
            (x, t) ∂μx := (htgood.2.2.2 n).symm
      _ = inner ℝ (hm.toLp _) ((hψ n).toLp (ψ n)) := by
        rw [hinverse n]
        symm
        simpa [parabolicHomeomorph_symm_apply] using
          (weakContL3_cutoff_pairing_eq_inner
            (⟨ψ n, (hψsmooth n).1, (hψsmooth n).2⟩ : weakContL3SmoothTest) t hm)
  have hvEq : v ⟨t, htT⟩ = hm.toLp _ := by
    exact DenseRange.eq_of_inner_left ℝ hψdense (fun n => heqtest n)
  exact ⟨htT, hm, hvEq⟩
  have hsmallballsub : vec3Ball (0 : Vec3) (3 / 4 : ℝ) ⊆
      weakContL3SpatialBall := by
    intro x hx
    have hxnorm : vec3EuclideanNorm (x - 0) < 3 / 4 := by
      simpa [mem_vec3Ball] using hx
    change vec3EuclideanNorm (x - 0) < 1
    exact lt_trans hxnorm (by norm_num)
  have hsmallballMeasure :
      volume.restrict (vec3Ball (0 : Vec3) (3 / 4 : ℝ)) ≤ μx :=
    (volume : Measure Vec3).restrict_mono_set hsmallballsub
  have hsmallsubset' : Ioo (-(3 / 4 : ℝ) ^ 2) 0 ⊆ Ioo (-1 : ℝ) 0 := by
    intro t ht
    refine ⟨?_, ht.2⟩
    dsimp [Ioo] at ht ⊢
    linarith only [ht.1]
  have hslice3Small :=
    ae_restrict_of_ae_restrict_of_subset hsmallsubset' hslice3
  filter_upwards [hslice3Small, ae_restrict_mem measurableSet_Ioo] with t h3 htI
  have htT : t ∈ Icc (-(3 / 4 : ℝ) ^ 2) 0 := ⟨le_of_lt htI.1, le_of_lt htI.2⟩
  have hmem3 : MemLp (fun x : Vec3 => WithLp.toLp 2 (u (x, t))) 3 μx := by
    rw [memLp_iff]
    exact lt_of_le_of_lt h3 hM
  refine ⟨htT, ?_, ?_⟩
  · rw [← Measure.restrict_restrict_of_subset hsmallballsub]
    exact hmem3.restrict (vec3Ball (0 : Vec3) (3 / 4 : ℝ))
  · exact (eLpNorm_mono_measure _ hsmallballMeasure).trans h3

end ESS
