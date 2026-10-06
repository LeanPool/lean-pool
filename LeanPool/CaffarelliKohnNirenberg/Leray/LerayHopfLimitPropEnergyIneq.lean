/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Leray.LerayHopfLimitPropTransport
public import LeanPool.CaffarelliKohnNirenberg.Leray.RegUniformEnergy
public import LeanPool.CaffarelliKohnNirenberg.Foundation.Parabolic.Vec3Norm
public import LeanPool.CaffarelliKohnNirenberg.Statements.SpatialGradientSq

/-!
# The energy inequality for the Leray–Hopf limit

This is the energy clause (LH4) of `def:leray-hopf` in the proof of
`prop:leray-hopf-limit`. The regularized energy equality of
`thm:regularised` bounds the slice energy plus twice the dissipation by the
energy of the mollified data, hence by the energy of the data. The weak
convergence of the slices and of the gradients then passes this bound to the
limit by weak lower semicontinuity of the two Hilbert norms, in the form of
the elementary inequality `2ab - b² ≤ a²`.
-/

public section

open MeasureTheory Filter Set
open scoped ENNReal Topology
open CKN CKN.Foundation.Parabolic

noncomputable section

namespace CKN.Leray

/-- The squared Euclidean energy of a square-integrable coordinate field. -/
theorem lerayHopfLimit_lintegral_euclidean_sq
    {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {g : α → Vec3} (hg : MemLp g 2 μ) :
    ∫⁻ x, ENNReal.ofReal (vec3EuclideanNorm (g x)) ^ (2 : ℝ) ∂μ =
      ENNReal.ofReal (∑ i : Fin 3, ∫ x, g x i ^ 2 ∂μ) := by
  have hint : ∀ i, Integrable (fun x => g x i ^ 2) μ := fun i => (hg.eval i).integrable_sq
  have hpt : ∀ x, ENNReal.ofReal (vec3EuclideanNorm (g x)) ^ (2 : ℝ) =
      ENNReal.ofReal (∑ i : Fin 3, g x i ^ 2) := by
    intro x
    have hnn : 0 ≤ vec3EuclideanNorm (g x) := Real.sqrt_nonneg _
    rw [ENNReal.ofReal_rpow_of_nonneg hnn (by norm_num : (0 : ℝ) ≤ 2)]
    congr 1
    rw [vec3EuclideanNorm, Real.rpow_two, Real.sq_sqrt
      (Finset.sum_nonneg (fun i _ => sq_nonneg _))]
  simp only [hpt]
  rw [← integral_finsetSum _ (fun i _ => hint i)]
  rw [ofReal_integral_eq_lintegral_ofReal (integrable_finsetSum _ (fun i _ => hint i))
    (Filter.Eventually.of_forall (fun x => Finset.sum_nonneg (fun i _ => sq_nonneg _)))]

/-- The squared `L²` norm of the Euclidean representative of a coordinate
field. -/
theorem lerayHopfLimit_eLpNorm_toLp_sq
    {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {g : α → Vec3} (hg : MemLp g 2 μ) :
    eLpNorm (fun x => (WithLp.toLp 2 (g x) : L2Vec3)) 2 μ ^ (2 : ℕ) =
      ENNReal.ofReal (∑ i : Fin 3, ∫ x, g x i ^ 2 ∂μ) := by
  rw [← lerayHopfLimit_lintegral_euclidean_sq hg]
  have hmeas : AEStronglyMeasurable (fun x => (WithLp.toLp 2 (g x) : L2Vec3)) μ :=
    (hg.continuousLinearMap_comp
      (PiLp.continuousLinearEquiv 2 ℝ
        (fun _ : Fin 3 => ℝ)).symm.toContinuousLinearMap).aestronglyMeasurable
  have h := eLpNorm_nnreal_pow_eq_lintegral (p := (2 : NNReal)) (by norm_num) hmeas
  have hcast : ((2 : NNReal) : ℝ) = ((2 : ℕ) : ℝ) := by norm_num
  rw [hcast, ENNReal.rpow_natCast] at h
  have hcoe : ((2 : NNReal) : ℝ≥0∞) = 2 := rfl
  rw [hcoe] at h
  rw [h]
  congr 1
  funext x
  rw [← ofReal_norm, ← vec3EuclideanNorm_eq_l2]
  norm_num

/-- The Euclidean `L²` norm of a coordinate field is unchanged by passing to
the Euclidean carrier of the spatial variable. -/
theorem lerayHopfLimit_eLpNorm_spatialField
    {f : Vec3 → Vec3} (hf : MemLp f 2 volume) :
    eLpNorm (regUniformSpatialField f) 2 volume =
      eLpNorm (fun x => (WithLp.toLp 2 (f x) : L2Vec3)) 2 volume := by
  have hS : MemLp (regUniformSpatialField f) 2 volume := by
    have hcoord : MemLp (fun x : L2Vec3 => f (WithLp.ofLp x)) 2 volume :=
      hf.comp_measurePreserving (PiLp.volume_preserving_ofLp (Fin 3))
    exact hcoord.continuousLinearMap_comp
      (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 3 => ℝ)).symm.toContinuousLinearMap
  exact (eLpNorm_comp_measurePreserving hS.aestronglyMeasurable
    vec3ToL2Vec3_measurePreserving).symm

/-- The regularized dissipation up to time t₀ is the dissipation integral
over the slab `ℝ³ × (0,t₀)`. -/
theorem lerayHopfLimit_dissipation_eq_setLIntegral
    (U : ParabolicPoint → Vec3) (D : ParabolicPoint → Fin 3 → Vec3) (t₀ : ℝ) :
    regUniformDissipation U D t₀ =
      ∫⁻ z in spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 t₀),
        ENNReal.ofReal (spatialGradientSq U D z) := by
  have hB : MeasurableSet {z : ParabolicPoint | z.2 < t₀} := by
    change MeasurableSet {z : Vec3 × ℝ | z.2 < t₀}
    exact measurableSet_lt measurable_snd measurable_const
  have hind : (fun z : ParabolicPoint =>
      if z.2 < t₀ then ENNReal.ofReal (spatialGradientSq U D z) else 0) =
      {z : ParabolicPoint | z.2 < t₀}.indicator
        (fun z => ENNReal.ofReal (spatialGradientSq U D z)) := by
    funext z
    by_cases h : z.2 < t₀
    · rw [Set.indicator_of_mem (show z ∈ {z : ParabolicPoint | z.2 < t₀} from h)]
      exact ite_eq_left_of_eq_true _ _ (eq_true h)
    · rw [Set.indicator_of_notMem (show z ∉ {z : ParabolicPoint | z.2 < t₀} from h)]
      exact ite_eq_right_of_eq_false _ _ (eq_false h)
  have hset : {z : ParabolicPoint | z.2 < t₀} ∩
      spaceTimeSet (Set.univ : Set Vec3) (Ioi 0) =
      spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 t₀) := by
    ext z
    constructor
    · rintro ⟨hlt, _, hpos⟩
      exact ⟨mem_univ _, hpos, hlt⟩
    · rintro ⟨_, hpos, hlt⟩
      exact ⟨hlt, mem_univ _, hpos⟩
  unfold regUniformDissipation regUniformPositiveTimeMeasure
  rw [hind, lintegral_indicator hB, Measure.restrict_restrict hB, hset]

/-- Measurability on every positive-time slab gives measurability on the slab
reaching the initial time. -/
theorem lerayHopfLimit_aestronglyMeasurable_of_slabs
    {f : ParabolicPoint → ℝ} {t₀ : ℝ} (ht₀ : 0 < t₀)
    (h : ∀ δ : ℝ, 0 < δ → δ < t₀ →
      AEStronglyMeasurable f (volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioo δ t₀)))) :
    AEStronglyMeasurable f
      (volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 t₀))) := by
  let δ : ℕ → ℝ := fun k => t₀ / (k + 2)
  have hδpos : ∀ k, 0 < δ k := fun k => by positivity
  have hδlt : ∀ k, δ k < t₀ := by
    intro k
    have hk : (1 : ℝ) < k + 2 := by
      have := (Nat.cast_nonneg k : (0 : ℝ) ≤ k)
      linarith only [this]
    exact (div_lt_self ht₀ hk)
  have hunion : spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 t₀) =
      ⋃ k : ℕ, spaceTimeSet (Set.univ : Set Vec3) (Ioo (δ k) t₀) := by
    ext z
    constructor
    · rintro ⟨-, hz0, hzt⟩
      obtain ⟨k, hk⟩ := exists_nat_gt (t₀ / z.2)
      refine mem_iUnion.mpr ⟨k, mem_univ _, ?_, hzt⟩
      have hk2 : t₀ / z.2 < k + 2 := by linarith only [hk]
      have hpos : (0 : ℝ) < k + 2 := by positivity
      rw [div_lt_iff₀ hz0] at hk2
      change t₀ / (k + 2) < z.2
      rw [div_lt_iff₀ hpos]
      linarith only [hk2]
    · intro hz
      obtain ⟨k, hk⟩ := mem_iUnion.mp hz
      exact ⟨mem_univ _, lt_trans (hδpos k) hk.2.1, hk.2.2⟩
  rw [hunion, aestronglyMeasurable_iUnion_iff]
  exact fun k => h (δ k) (hδpos k) (hδlt k)

/-- The elementary weak lower semicontinuity inequality `2 ∫ f g - ∫ g² ≤ ∫ f²`,
together with the integrability of f g. -/
theorem lerayHopfLimit_two_mul_integral_sub_le
    {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {f g : α → ℝ} (hf : MemLp f 2 μ) (hg : MemLp g 2 μ) :
    Integrable (fun x => f x * g x) μ ∧
      2 * (∫ x, f x * g x ∂μ) - ∫ x, g x ^ 2 ∂μ ≤ ∫ x, f x ^ 2 ∂μ := by
  have hf2 := hf.integrable_sq
  have hg2 := hg.integrable_sq
  have hsum : Integrable (fun x => (f x ^ 2 + g x ^ 2) / 2) μ := (hf2.add hg2).div_const 2
  have hint : Integrable (fun x => f x * g x) μ := by
    refine hsum.mono (hf.aestronglyMeasurable.mul hg.aestronglyMeasurable) ?_
    refine Filter.Eventually.of_forall (fun x => ?_)
    rw [Real.norm_eq_abs, Real.norm_eq_abs]
    have h1 : |f x * g x| ≤ (f x ^ 2 + g x ^ 2) / 2 := by
      rw [abs_le]
      constructor <;> nlinarith only [sq_nonneg (f x - g x), sq_nonneg (f x + g x)]
    exact h1.trans (le_abs_self _)
  refine ⟨hint, ?_⟩
  have hmono : ∫ x, (2 * (f x * g x) - g x ^ 2) ∂μ ≤ ∫ x, f x ^ 2 ∂μ := by
    refine integral_mono ((hint.const_mul 2).sub hg2) hf2 (fun x => ?_)
    nlinarith only [sq_nonneg (f x - g x)]
  rw [integral_sub (hint.const_mul 2) hg2, integral_const_mul] at hmono
  exact hmono

/-- The energy inequality of the limit at a positive time, in real form: the
slice energy plus twice the dissipation up to that time is bounded by the
energy of the data. -/
theorem lerayHopfLimit_energy_real
    (t₀ : ℝ) (Useq : ℕ → ParabolicPoint → Vec3) (u : ParabolicPoint → Vec3)
    (Du : ParabolicPoint → Fin 3 → Vec3) (a : Vec3 → Vec3)
    (hUn : ∀ n, MemLp (fun x => Useq n (x, t₀)) 2 volume)
    (hu : MemLp (fun x => u (x, t₀)) 2 volume)
    (hweak : Tendsto (fun n => ∫ x, ∑ i : Fin 3, Useq n (x, t₀) i * u (x, t₀) i) atTop
      (𝓝 (∫ x, ∑ i : Fin 3, u (x, t₀) i * u (x, t₀) i)))
    (hDmeas : ∀ n i j, AEStronglyMeasurable
      (fun z => spatialPartial (fun y => Useq n y i) j z)
      (volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 t₀))))
    (hDu : ∀ i j, MemLp (fun z => Du z i j) 2
      (volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 t₀))))
    (hDweak : ∀ i j, Tendsto (fun n => ∫ z in spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 t₀),
        spatialPartial (fun y => Useq n y i) j z * Du z i j) atTop
      (𝓝 (∫ z in spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 t₀), Du z i j * Du z i j)))
    (ha : MemLp a 2 volume)
    (hR5 : ∀ n, eLpNorm (regUniformVelocitySlice (Useq n) t₀) 2 volume ^ (2 : ℕ) +
        2 * regUniformDissipation (Useq n)
          (fun z i j => spatialPartial (fun y => Useq n y i) j z) t₀ ≤
      eLpNorm (regUniformSpatialField a) 2 volume ^ (2 : ℕ)) :
    (∑ i : Fin 3, ∫ x, u (x, t₀) i ^ 2) +
        2 * (∑ i : Fin 3, ∑ j : Fin 3,
          ∫ z in spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 t₀), Du z i j ^ 2) ≤
      ∑ i : Fin 3, ∫ x, a x i ^ 2 := by
  set μt : Measure ParabolicPoint :=
    volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 t₀)) with hμt
  let Dn : ℕ → Fin 3 → Fin 3 → ParabolicPoint → ℝ := fun n i j z =>
    spatialPartial (fun y => Useq n y i) j z
  set Aa : ℝ := ∑ i : Fin 3, ∫ x, a x i ^ 2 with hAa
  have hAa0 : 0 ≤ Aa := Finset.sum_nonneg (fun i _ => integral_nonneg (fun x => sq_nonneg _))
  have hAeq : eLpNorm (regUniformSpatialField a) 2 volume ^ (2 : ℕ) = ENNReal.ofReal Aa := by
    rw [lerayHopfLimit_eLpNorm_spatialField ha, lerayHopfLimit_eLpNorm_toLp_sq ha]
  have hDiss_lt : ∀ n, regUniformDissipation (Useq n)
      (fun z i j => spatialPartial (fun y => Useq n y i) j z) t₀ < ⊤ := by
    intro n
    have h := hR5 n
    rw [hAeq] at h
    have h2 := lt_of_le_of_lt (le_trans le_add_self h) ENNReal.ofReal_lt_top
    exact ENNReal.lt_top_of_mul_ne_top_right h2.ne two_ne_zero
  have hpt_le : ∀ n i j z, Dn n i j z ^ 2 ≤ spatialGradientSq (Useq n)
      (fun z i j => spatialPartial (fun y => Useq n y i) j z) z := by
    intro n i j z
    unfold spatialGradientSq
    exact (Finset.single_le_sum (f := fun j' => Dn n i j' z ^ 2)
      (fun _ _ => sq_nonneg _) (Finset.mem_univ j)).trans
      (Finset.single_le_sum (f := fun i' => ∑ j' : Fin 3, Dn n i' j' z ^ 2)
        (fun _ _ => Finset.sum_nonneg (fun _ _ => sq_nonneg _)) (Finset.mem_univ i))
  have hDnmem : ∀ n i j, MemLp (Dn n i j) 2 μt := by
    intro n i j
    rw [memLp_two_iff_integrable_sq (hDmeas n i j)]
    refine ⟨(hDmeas n i j).pow 2, ?_⟩
    rw [hasFiniteIntegral_iff_ofReal (Filter.Eventually.of_forall (fun z => sq_nonneg _))]
    refine lt_of_le_of_lt ?_ (hDiss_lt n)
    rw [lerayHopfLimit_dissipation_eq_setLIntegral]
    exact lintegral_mono (fun z => ENNReal.ofReal_le_ofReal (hpt_le n i j z))
  have hDissEq : ∀ n, regUniformDissipation (Useq n)
      (fun z i j => spatialPartial (fun y => Useq n y i) j z) t₀ =
      ENNReal.ofReal (∑ i : Fin 3, ∑ j : Fin 3, ∫ z, Dn n i j z ^ 2 ∂μt) := by
    intro n
    have hint : ∀ i j, Integrable (fun z => Dn n i j z ^ 2) μt :=
      fun i j => (hDnmem n i j).integrable_sq
    have hsum : (∑ i : Fin 3, ∑ j : Fin 3, ∫ z, Dn n i j z ^ 2 ∂μt) =
        ∫ z, spatialGradientSq (Useq n)
          (fun z i j => spatialPartial (fun y => Useq n y i) j z) z ∂μt := by
      unfold spatialGradientSq
      rw [integral_finsetSum _ (fun i _ => integrable_finsetSum _ (fun j _ => hint i j))]
      refine Finset.sum_congr rfl (fun i _ => ?_)
      rw [integral_finsetSum _ (fun j _ => hint i j)]
    rw [lerayHopfLimit_dissipation_eq_setLIntegral, hsum,
      ofReal_integral_eq_lintegral_ofReal]
    · unfold spatialGradientSq
      exact integrable_finsetSum _ (fun i _ => integrable_finsetSum _ (fun j _ => hint i j))
    · refine Filter.Eventually.of_forall (fun z => ?_)
      unfold spatialGradientSq
      exact Finset.sum_nonneg (fun _ _ => Finset.sum_nonneg (fun _ _ => sq_nonneg _))
  have hXn : ∀ n, eLpNorm (regUniformVelocitySlice (Useq n) t₀) 2 volume ^ (2 : ℕ) =
      ENNReal.ofReal (∑ i : Fin 3, ∫ x, Useq n (x, t₀) i ^ 2) := by
    intro n
    have heq : regUniformVelocitySlice (Useq n) t₀ =
        regUniformSpatialField (fun x => Useq n (x, t₀)) := rfl
    rw [heq, lerayHopfLimit_eLpNorm_spatialField (hUn n),
      lerayHopfLimit_eLpNorm_toLp_sq (hUn n)]
  have hEn : ∀ n, (∑ i : Fin 3, ∫ x, Useq n (x, t₀) i ^ 2) +
      2 * (∑ i : Fin 3, ∑ j : Fin 3, ∫ z, Dn n i j z ^ 2 ∂μt) ≤ Aa := by
    intro n
    have h := hR5 n
    rw [hXn n, hDissEq n, hAeq] at h
    have hX0 : 0 ≤ ∑ i : Fin 3, ∫ x, Useq n (x, t₀) i ^ 2 :=
      Finset.sum_nonneg (fun i _ => integral_nonneg (fun x => sq_nonneg _))
    have hG0 : 0 ≤ ∑ i : Fin 3, ∑ j : Fin 3, ∫ z, Dn n i j z ^ 2 ∂μt :=
      Finset.sum_nonneg (fun i _ => Finset.sum_nonneg (fun j _ =>
        integral_nonneg (fun z => sq_nonneg _)))
    have h2 : (2 : ℝ≥0∞) * ENNReal.ofReal (∑ i : Fin 3, ∑ j : Fin 3, ∫ z, Dn n i j z ^ 2 ∂μt) =
        ENNReal.ofReal (2 * ∑ i : Fin 3, ∑ j : Fin 3, ∫ z, Dn n i j z ^ 2 ∂μt) := by
      rw [ENNReal.ofReal_mul (by norm_num)]
      norm_num
    rw [h2, ← ENNReal.ofReal_add hX0 (by positivity)] at h
    exact (ENNReal.ofReal_le_ofReal_iff hAa0).mp h
  have hslice : ∀ n i, Integrable (fun x => Useq n (x, t₀) i * u (x, t₀) i) ∧
      2 * (∫ x, Useq n (x, t₀) i * u (x, t₀) i) - ∫ x, u (x, t₀) i ^ 2 ≤
        ∫ x, Useq n (x, t₀) i ^ 2 :=
    fun n i => lerayHopfLimit_two_mul_integral_sub_le ((hUn n).eval i) (hu.eval i)
  have hgrad : ∀ n i j, Integrable (fun z => Dn n i j z * Du z i j) μt ∧
      2 * (∫ z, Dn n i j z * Du z i j ∂μt) - ∫ z, Du z i j ^ 2 ∂μt ≤
        ∫ z, Dn n i j z ^ 2 ∂μt :=
    fun n i j => lerayHopfLimit_two_mul_integral_sub_le (hDnmem n i j) (hDu i j)
  let L : ℕ → ℝ := fun n =>
    (2 * (∫ x, ∑ i : Fin 3, Useq n (x, t₀) i * u (x, t₀) i) -
        ∑ i : Fin 3, ∫ x, u (x, t₀) i ^ 2) +
      2 * ∑ i : Fin 3, ∑ j : Fin 3,
        (2 * (∫ z, Dn n i j z * Du z i j ∂μt) - ∫ z, Du z i j ^ 2 ∂μt)
  have hLle : ∀ n, L n ≤ Aa := by
    intro n
    have hsplit : ∫ x, ∑ i : Fin 3, Useq n (x, t₀) i * u (x, t₀) i =
        ∑ i : Fin 3, ∫ x, Useq n (x, t₀) i * u (x, t₀) i :=
      integral_finsetSum _ (fun i _ => (hslice n i).1)
    have h1 : 2 * (∑ i : Fin 3, ∫ x, Useq n (x, t₀) i * u (x, t₀) i) -
        ∑ i : Fin 3, ∫ x, u (x, t₀) i ^ 2 ≤ ∑ i : Fin 3, ∫ x, Useq n (x, t₀) i ^ 2 := by
      rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
      exact Finset.sum_le_sum (fun i _ => (hslice n i).2)
    have h2 : (∑ i : Fin 3, ∑ j : Fin 3,
        (2 * (∫ z, Dn n i j z * Du z i j ∂μt) - ∫ z, Du z i j ^ 2 ∂μt)) ≤
        ∑ i : Fin 3, ∑ j : Fin 3, ∫ z, Dn n i j z ^ 2 ∂μt :=
      Finset.sum_le_sum (fun i _ => Finset.sum_le_sum (fun j _ => (hgrad n i j).2))
    have h3 := hEn n
    change (2 * (∫ x, ∑ i : Fin 3, Useq n (x, t₀) i * u (x, t₀) i) -
        ∑ i : Fin 3, ∫ x, u (x, t₀) i ^ 2) +
      2 * ∑ i : Fin 3, ∑ j : Fin 3,
        (2 * (∫ z, Dn n i j z * Du z i j ∂μt) - ∫ z, Du z i j ^ 2 ∂μt) ≤ Aa
    rw [hsplit]
    linarith only [h1, h2, h3]
  have hXlim : ∫ x, ∑ i : Fin 3, u (x, t₀) i * u (x, t₀) i =
      ∑ i : Fin 3, ∫ x, u (x, t₀) i ^ 2 := by
    rw [integral_finsetSum _ (fun i _ => (hu.eval i).integrable_sq.congr
      (Filter.Eventually.of_forall (fun x => pow_two _)))]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    congr 1
    funext x
    rw [pow_two]
  have hGlim : ∀ i j, ∫ z in spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 t₀), Du z i j * Du z i j =
      ∫ z, Du z i j ^ 2 ∂μt := by
    intro i j
    congr 1
    funext z
    rw [pow_two]
  have hLlim : Tendsto L atTop (𝓝 ((2 * (∑ i : Fin 3, ∫ x, u (x, t₀) i ^ 2) -
        ∑ i : Fin 3, ∫ x, u (x, t₀) i ^ 2) +
      2 * ∑ i : Fin 3, ∑ j : Fin 3,
        (2 * (∫ z, Du z i j ^ 2 ∂μt) - ∫ z, Du z i j ^ 2 ∂μt))) := by
    refine ((hXlim ▸ hweak).const_mul 2 |>.sub tendsto_const_nhds).add
      (Tendsto.const_mul 2 (tendsto_finsetSum _ (fun i _ => tendsto_finsetSum _ (fun j _ =>
        ?_))))
    have h := (hDweak i j).const_mul 2
    rw [hGlim i j] at h
    exact h.sub tendsto_const_nhds
  have hfinal := le_of_tendsto' hLlim hLle
  have hsimp : ∀ i j, 2 * (∫ z, Du z i j ^ 2 ∂μt) - ∫ z, Du z i j ^ 2 ∂μt =
      ∫ z, Du z i j ^ 2 ∂μt := fun i j => by ring
  simp only [hsimp] at hfinal
  linarith only [hfinal]

/-- The real energy inequality gives the energy clause (LH4) at a positive
time. -/
theorem lerayHopfLimit_energy_ennreal
    (t₀ : ℝ) (u : ParabolicPoint → Vec3) (Du : ParabolicPoint → Fin 3 → Vec3)
    (a : Vec3 → Vec3)
    (hu : MemLp (fun x => u (x, t₀)) 2 volume)
    (hDu : ∀ i j, MemLp (fun z => Du z i j) 2
      (volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 t₀))))
    (ha : MemLp a 2 volume)
    (hreal : (∑ i : Fin 3, ∫ x, u (x, t₀) i ^ 2) +
        2 * (∑ i : Fin 3, ∑ j : Fin 3,
          ∫ z in spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 t₀), Du z i j ^ 2) ≤
      ∑ i : Fin 3, ∫ x, a x i ^ 2) :
    ENNReal.ofReal (1 / 2 : ℝ) *
        (∫⁻ x : Vec3, ENNReal.ofReal (vec3EuclideanNorm (u (x, t₀))) ^ (2 : ℝ))
      + ∫⁻ z in spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 t₀),
          ENNReal.ofReal (spatialGradientSq u Du z)
      ≤ ENNReal.ofReal (1 / 2 : ℝ) *
        (∫⁻ x : Vec3, ENNReal.ofReal (vec3EuclideanNorm (a x)) ^ (2 : ℝ)) := by
  set μt : Measure ParabolicPoint :=
    volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 t₀)) with hμt
  have hint : ∀ i j, Integrable (fun z => Du z i j ^ 2) μt := fun i j => (hDu i j).integrable_sq
  have hdiss : ∫⁻ z in spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 t₀),
      ENNReal.ofReal (spatialGradientSq u Du z) =
      ENNReal.ofReal (∑ i : Fin 3, ∑ j : Fin 3, ∫ z, Du z i j ^ 2 ∂μt) := by
    have hsum : (∑ i : Fin 3, ∑ j : Fin 3, ∫ z, Du z i j ^ 2 ∂μt) =
        ∫ z, spatialGradientSq u Du z ∂μt := by
      unfold spatialGradientSq
      rw [integral_finsetSum _ (fun i _ => integrable_finsetSum _ (fun j _ => hint i j))]
      refine Finset.sum_congr rfl (fun i _ => ?_)
      rw [integral_finsetSum _ (fun j _ => hint i j)]
    rw [hsum, ofReal_integral_eq_lintegral_ofReal]
    · unfold spatialGradientSq
      exact integrable_finsetSum _ (fun i _ => integrable_finsetSum _ (fun j _ => hint i j))
    · refine Filter.Eventually.of_forall (fun z => ?_)
      unfold spatialGradientSq
      exact Finset.sum_nonneg (fun _ _ => Finset.sum_nonneg (fun _ _ => sq_nonneg _))
  rw [lerayHopfLimit_lintegral_euclidean_sq hu, lerayHopfLimit_lintegral_euclidean_sq ha, hdiss]
  set X := ∑ i : Fin 3, ∫ x, u (x, t₀) i ^ 2
  set G := ∑ i : Fin 3, ∑ j : Fin 3, ∫ z, Du z i j ^ 2 ∂μt
  set Aa := ∑ i : Fin 3, ∫ x, a x i ^ 2
  have hX0 : 0 ≤ X := Finset.sum_nonneg (fun i _ => integral_nonneg (fun x => sq_nonneg _))
  have hG0 : 0 ≤ G := Finset.sum_nonneg (fun i _ => Finset.sum_nonneg (fun j _ =>
    integral_nonneg (fun z => sq_nonneg _)))
  rw [← ENNReal.ofReal_mul (by norm_num), ← ENNReal.ofReal_mul (by norm_num),
    ← ENNReal.ofReal_add (by positivity) hG0]
  apply ENNReal.ofReal_le_ofReal
  linarith only [hreal]

/-- The initial trace clause (LH5): the energy bound and weak continuity at
the initial time give strong `L²` convergence to the data. -/
theorem lerayHopfLimit_initialTrace
    (T : ℝ) (hT : 0 < T) (u : ParabolicPoint → Vec3) (a : Vec3 → Vec3)
    (hu0 : ∀ x, u (x, 0) = a x) (ha : MemLp a 2 volume)
    (hslice : ∀ t, 0 < t → MemLp (fun x => u (x, t)) 2 volume)
    (henergy : ∀ t, 0 < t → t ≤ T →
      ∑ i : Fin 3, ∫ x, u (x, t) i ^ 2 ≤ ∑ i : Fin 3, ∫ x, a x i ^ 2)
    (hcont : ContinuousOn (fun t => ∫ x, ∑ i : Fin 3, u (x, t) i * a x i) (Icc 0 T)) :
    Tendsto (fun t : ℝ => ∫⁻ x : Vec3,
        ENNReal.ofReal (vec3EuclideanNorm (u (x, t) - a x)) ^ (2 : ℝ))
      (𝓝[>] 0) (𝓝 0) := by
  set Aa := ∑ i : Fin 3, ∫ x, a x i ^ 2
  let P : ℝ → ℝ := fun t => ∫ x, ∑ i : Fin 3, u (x, t) i * a x i
  have hP0 : P 0 = Aa := by
    change ∫ x, ∑ i : Fin 3, u (x, 0) i * a x i = Aa
    simp only [hu0]
    rw [integral_finsetSum _ (fun i _ => (ha.eval i).integrable_sq.congr
      (Filter.Eventually.of_forall (fun x => pow_two _)))]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    congr 1
    funext x
    rw [pow_two]
  have hPlim : Tendsto P (𝓝[>] 0) (𝓝 Aa) := by
    rw [← hP0]
    have hc : ContinuousWithinAt P (Icc 0 T) 0 := hcont 0 ⟨le_rfl, hT.le⟩
    have hmem : Icc 0 T ∈ 𝓝[>] (0 : ℝ) :=
      mem_of_superset (Ioc_mem_nhdsGT hT) Ioc_subset_Icc_self
    exact (hc.mono_of_mem_nhdsWithin hmem).tendsto
  have hupper : Tendsto (fun t => ENNReal.ofReal (2 * Aa - 2 * P t)) (𝓝[>] 0) (𝓝 0) := by
    have h := ((hPlim.const_mul 2).const_sub (2 * Aa))
    have h' := ENNReal.tendsto_ofReal h
    rw [show 2 * Aa - 2 * Aa = (0 : ℝ) by ring, ENNReal.ofReal_zero] at h'
    exact h'
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hupper
    (Filter.Eventually.of_forall (fun _ => bot_le)) ?_
  filter_upwards [Ioc_mem_nhdsGT hT] with t ht
  have hut := hslice t ht.1
  have hdiff : MemLp (fun x => u (x, t) - a x) 2 volume := hut.sub ha
  rw [lerayHopfLimit_lintegral_euclidean_sq hdiff]
  apply ENNReal.ofReal_le_ofReal
  have hcross : ∀ i, Integrable (fun x => u (x, t) i * a x i) :=
    fun i => (lerayHopfLimit_two_mul_integral_sub_le (hut.eval i) (ha.eval i)).1
  have hexp : ∀ i, ∫ x, (u (x, t) - a x) i ^ 2 =
      (∫ x, u (x, t) i ^ 2) - 2 * (∫ x, u (x, t) i * a x i) + ∫ x, a x i ^ 2 := by
    intro i
    have hpt : (fun x => (u (x, t) - a x) i ^ 2) =
        fun x => (u (x, t) i ^ 2 - 2 * (u (x, t) i * a x i)) + a x i ^ 2 := by
      funext x
      simp only [Pi.sub_apply]
      ring
    have h1 : Integrable (fun x => u (x, t) i ^ 2 - 2 * (u (x, t) i * a x i)) :=
      (hut.eval i).integrable_sq.sub ((hcross i).const_mul 2)
    have h2 : Integrable (fun x => 2 * (u (x, t) i * a x i)) := (hcross i).const_mul 2
    rw [hpt, integral_add h1 (ha.eval i).integrable_sq,
      integral_sub (hut.eval i).integrable_sq h2, integral_const_mul]
  have hPt : P t = ∑ i : Fin 3, ∫ x, u (x, t) i * a x i :=
    integral_finsetSum _ (fun i _ => hcross i)
  simp only [hexp]
  rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum, ← hPt]
  have hE := henergy t ht.1 ht.2
  linarith only [hE]

end CKN.Leray

end
