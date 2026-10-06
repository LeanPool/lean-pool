/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Leray.ForcedLerayLimitPropEveryTime
public import LeanPool.CaffarelliKohnNirenberg.Leray.ForcedLerayLimitPropJ
public import LeanPool.CaffarelliKohnNirenberg.Leray.LerayLimitSpaceTime
public import LeanPool.CaffarelliKohnNirenberg.Leray.LerayLimitTailLimit
public import LeanPool.CaffarelliKohnNirenberg.Leray.LerayLimitTenThirdsVector
public import LeanPool.CaffarelliKohnNirenberg.Leray.ForcedLerayLimitTenThirds
public import LeanPool.CaffarelliKohnNirenberg.Leray.ForcedRegularisedEnergyForm

/-!
# The strong convergence clauses of `prop:forced-limit`

On every finite slab `ℝ³ × (0,T)`, the forced regularized velocities along the
subsequence of the compactness step converge strongly to the limit in `L²`, in
every `L^q` with `2 ≤ q < 10/3`, and in `L³`, and their spatial mollifications
converge in `L³` to the same limit. The local strong convergence on compact
subsets of `ℝ³ × (0,∞)` comes from the compactness step; the uniform spatial
tails (`lem:forced-tails`, in the form of a hypothesis supplied by the tail
estimate) and the uniform slice energy of `lem:forced-energy-bounds` control
the complement of large compact cylinders; the uniform `L^{10/3}` bound
`eq:forced-ten-thirds` gives the intermediate exponents.
-/

public section

open MeasureTheory Filter Set
open scoped ENNReal Topology
open CKN CKN.Foundation.Parabolic

noncomputable section

namespace CKN.Leray

/-- The compact cylinder `B̄_R × [δ, T - δ]` of the slab. -/
@[expose]
def forcedLerayLimitStrongCylinder (T R δ : ℝ) : Set ParabolicPoint :=
  spaceTimeSet (Metric.closedBall (0 : Vec3) R) (Icc δ (T - δ))

private theorem forcedLerayLimitStrong_enorm_sq_eq (y : Vec3) :
    ENNReal.ofReal (vec3EuclideanNorm y) ^ (2 : ℝ) =
      ‖(WithLp.toLp 2 y : L2Vec3)‖ₑ ^ (2 : ℝ) := by
  rw [vec3EuclideanNorm_eq_l2, ofReal_norm]

/-- The integral over the slab of a density off the cylinder `B̄_R × [δ,T-δ]`
is bounded by the exterior spatial tails on `(0,T)` and the slice integrals
near the two ends of the time interval. -/
private theorem forcedLerayLimitStrong_complement_lintegral_le
    (T R δ : ℝ) (hδ : 0 ≤ δ) (Φ : ParabolicPoint → ℝ≥0∞) (hΦ : Measurable Φ)
    (S A : ℝ≥0∞)
    (htail : ∀ t ∈ Ioo 0 T,
      (∫⁻ x in {x : Vec3 | R < vec3EuclideanNorm x}, Φ (x, t)) ≤ S)
    (hslice : ∀ t ∈ Ioo 0 T, (∫⁻ x : Vec3, Φ (x, t)) ≤ A) :
    (∫⁻ z in spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 T),
      (forcedLerayLimitStrongCylinder T R δ)ᶜ.indicator Φ z) ≤
      ENNReal.ofReal T * S + ENNReal.ofReal (2 * δ) * A := by
  classical
  let E : Set Vec3 := {x : Vec3 | R < vec3EuclideanNorm x}
  let I : Set ℝ := Icc δ (T - δ)
  have hEmeas : MeasurableSet E :=
    measurableSet_lt measurable_const
      CKN.Foundation.Parabolic.continuous_vec3EuclideanNorm.measurable
  have hImeas : MeasurableSet I := measurableSet_Icc
  let g₁ : Vec3 × ℝ → ℝ≥0∞ := fun z => E.indicator (fun x => Φ (x, z.2)) z.1
  let g₂ : Vec3 × ℝ → ℝ≥0∞ := fun z => Iᶜ.indicator (fun t => Φ (z.1, t)) z.2
  have hg₁ : Measurable g₁ := by
    have : g₁ = (Prod.fst ⁻¹' E).indicator (fun z : Vec3 × ℝ => Φ z) := by
      funext z
      by_cases hz : z.1 ∈ E <;> simp [g₁, hz, Set.indicator]
    rw [this]
    exact (hΦ.indicator (measurable_fst hEmeas))
  have hg₂ : Measurable g₂ := by
    have : g₂ = (Prod.snd ⁻¹' Iᶜ).indicator (fun z : Vec3 × ℝ => Φ z) := by
      funext z
      by_cases hz : z.2 ∈ Iᶜ <;> simp [g₂, Set.indicator]
    rw [this]
    exact (hΦ.indicator (measurable_snd hImeas.compl))
  have hpt : ∀ z : ParabolicPoint,
      (forcedLerayLimitStrongCylinder T R δ)ᶜ.indicator Φ z ≤ g₁ z + g₂ z := by
    intro z
    by_cases hz : z ∈ forcedLerayLimitStrongCylinder T R δ
    · simp [hz]
    · rw [Set.indicator_of_mem (show z ∈ (forcedLerayLimitStrongCylinder T R δ)ᶜ from hz)]
      have hz' : z.1 ∉ Metric.closedBall (0 : Vec3) R ∨ z.2 ∉ I := by
        by_contra hcon
        push Not at hcon
        exact hz ⟨hcon.1, hcon.2⟩
      rcases hz' with h1 | h2
      · have hx : z.1 ∈ E := by
          have hR : R < ‖z.1‖ := by
            simpa [Metric.mem_closedBall, dist_zero_right] using h1
          exact lt_of_lt_of_le hR (norm_le_vec3EuclideanNorm z.1)
        have : g₁ z = Φ z := by simp only [g₁, Set.indicator_of_mem hx]; rfl
        rw [this]
        exact le_self_add
      · have : g₂ z = Φ z := by
          simp only [g₂]
          rw [Set.indicator_of_mem (show z.2 ∈ Iᶜ from h2)]
          rfl
        rw [this]
        exact le_add_self
  have hsplit : (∫⁻ z in spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 T),
      (forcedLerayLimitStrongCylinder T R δ)ᶜ.indicator Φ z) ≤
      (∫⁻ z in spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 T), g₁ z) +
        ∫⁻ z in spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 T), g₂ z := by
    calc _ ≤ ∫⁻ z in spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 T), (g₁ z + g₂ z) :=
          lintegral_mono hpt
      _ = _ := lintegral_add_left (f := fun z : ParabolicPoint => g₁ z) hg₁ _
  refine hsplit.trans (add_le_add ?_ ?_)
  · rw [lintegral_slab_eq_prod g₁ (Ioo 0 T), lintegral_prod_symm' g₁ hg₁]
    have hin : ∀ t ∈ Ioo (0 : ℝ) T, (∫⁻ x, g₁ (x, t)) ≤ S := by
      intro t ht
      have : (∫⁻ x, g₁ (x, t)) = ∫⁻ x in E, Φ (x, t) := by
        simp only [g₁]
        exact lintegral_indicator hEmeas _
      rw [this]
      exact htail t ht
    calc (∫⁻ t in Ioo 0 T, ∫⁻ x, g₁ (x, t))
        ≤ ∫⁻ _t in Ioo 0 T, S := setLIntegral_mono measurable_const hin
      _ = ENNReal.ofReal T * S := by
          rw [setLIntegral_const, Real.volume_Ioo, sub_zero, mul_comm]
  · rw [lintegral_slab_eq_prod g₂ (Ioo 0 T), lintegral_prod_symm' g₂ hg₂]
    have hin : ∀ t ∈ Ioo (0 : ℝ) T,
        (∫⁻ x, g₂ (x, t)) ≤ Iᶜ.indicator (fun _ => A) t := by
      intro t ht
      by_cases htI : t ∈ Iᶜ
      · have : (fun x => g₂ (x, t)) = fun x => Φ (x, t) := by
          funext x
          simp only [g₂]
          rw [Set.indicator_of_mem htI]
        rw [this, Set.indicator_of_mem htI]
        exact hslice t ht
      · have : (fun x => g₂ (x, t)) = fun _ => 0 := by
          funext x
          simp only [g₂]
          rw [Set.indicator_of_notMem htI]
        rw [this, lintegral_zero]
        exact zero_le
    calc (∫⁻ t in Ioo 0 T, ∫⁻ x, g₂ (x, t))
        ≤ ∫⁻ t in Ioo 0 T, Iᶜ.indicator (fun _ => A) t :=
          setLIntegral_mono (measurable_const.indicator hImeas.compl) hin
      _ = A * volume (Iᶜ ∩ Ioo 0 T) := by
          rw [lintegral_indicator hImeas.compl, Measure.restrict_restrict hImeas.compl,
            setLIntegral_const]
      _ ≤ A * ENNReal.ofReal (2 * δ) := by
          gcongr
          calc volume (Iᶜ ∩ Ioo 0 T) ≤ volume (Ioo 0 δ ∪ Ioo (T - δ) T) := by
                apply measure_mono
                intro t ht
                obtain ⟨htI, ht0, htT⟩ := ht
                simp only [I, mem_compl_iff, mem_Icc, not_and_or, not_le] at htI
                rcases htI with h | h
                · exact Or.inl ⟨ht0, h⟩
                · exact Or.inr ⟨h, htT⟩
            _ ≤ volume (Ioo 0 δ) + volume (Ioo (T - δ) T) := measure_union_le _ _
            _ = ENNReal.ofReal (2 * δ) := by
                rw [Real.volume_Ioo, Real.volume_Ioo, ← ENNReal.ofReal_add
                  (by linarith only [hδ]) (by linarith only [hδ])]
                congr 1
                ring
      _ = ENNReal.ofReal (2 * δ) * A := mul_comm _ _

/-- The `L²` seminorm of a vector field is at most the square root of the
integral of the square of its Euclidean norm. -/
private theorem forcedLerayLimitStrong_eLpNorm_le
    {μ : Measure ParabolicPoint} (F : ParabolicPoint → Vec3)
    (hF : AEStronglyMeasurable F μ) :
    eLpNorm F 2 μ ≤
      (∫⁻ z, ‖(WithLp.toLp 2 (F z) : L2Vec3)‖ₑ ^ (2 : ℝ) ∂μ) ^ (1 / 2 : ℝ) := by
  have hG : AEStronglyMeasurable (fun z => (WithLp.toLp 2 (F z) : L2Vec3)) μ :=
    (PiLp.continuous_toLp 2 _).comp_aestronglyMeasurable hF
  calc eLpNorm F 2 μ ≤ eLpNorm (fun z => (WithLp.toLp 2 (F z) : L2Vec3)) 2 μ := by
        refine eLpNorm_mono_ae hF (Eventually.of_forall fun z => ?_)
        rw [← vec3EuclideanNorm_eq_l2]
        exact norm_le_vec3EuclideanNorm _
    _ = _ := by
        rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num) hG]
        simp only [ENNReal.toReal_ofNat]

/-- The strong convergence clauses of `prop:forced-limit` on one slab
`ℝ³ × (0,T)`. The hypotheses are the local strong convergence and the limit
slice bound of `CKN.Leray.forcedLerayLimit_local_compactness` (its second and
fifth outputs, verbatim), the positive-time identification of `u` with the
compactness limit `v`, and the uniform spatial tails `htails` of the forced
regularized velocities and of `v` on `(0,T)`. The conclusion is the strong
convergence part of the forced compactness statement: `u ∈ L² ∩ L³` on the
slab, `U_n → u` in `L²` and in every `L^q` with `2 ≤ q < 10/3`, `U_n ∈ L³`,
and the spatial mollifications `J_n U_n` lie in `L³` and converge to `u` in
`L³`. -/
theorem forcedLerayLimit_strong_clauses
    (ρ : RegMollifierProfile) (a : Vec3 → Vec3) (ha : IsInJ a)
    (f : ParabolicPoint → Vec3) (hf : IsLocallySquareIntegrableForce f)
    (εseq : ℕ → ℝ) (hseq : ∀ n, 0 < εseq n ∧ εseq n ≤ 1)
    (σ : ℕ → ℕ) (hεsub : Tendsto (fun n => εseq (σ n)) atTop (𝓝 0))
    (v : Vec3 × ℝ → Vec3) (hv : Measurable v)
    (u : ParabolicPoint → Vec3)
    (huv : ∀ (x : Vec3) (t : ℝ), 0 < t → u (x, t) = v (x, t))
    (hstrong : ∀ Q : Set (Vec3 × ℝ), IsCompact Q → Q ⊆
        (Set.univ : Set Vec3) ×ˢ Ioi (0 : ℝ) →
        Tendsto (fun k => eLpNorm
          ((fun z : Vec3 × ℝ => (WithLp.toLp 2
              (forcedRegVelocity ρ a ha f hf (εseq (σ k)) (z.1,z.2)) : L2Vec3)) -
            (fun z : Vec3 × ℝ => (WithLp.toLp 2 (v z) : L2Vec3))) 2
          (volume.restrict Q)) atTop (nhds 0))
    (hSliceBound : ∀ C : Set Vec3, IsCompact C →
        ∀ b₁ b₂ : ℝ, Icc b₁ b₂ ⊆ Ioi (0 : ℝ) →
        ∀ M : ℝ≥0∞, M < ⊤ →
          (∀ n t, t ∈ Icc b₁ b₂ →
            (∫⁻ x in C, ENNReal.ofReal
              (vec3EuclideanNorm
                (forcedRegVelocity ρ a ha f hf (εseq n) (x,t))) ^ (2 : ℝ)
              ∂volume) ≤ M) →
          ∀ t ∈ Icc b₁ b₂,
            (∫⁻ x in C, ENNReal.ofReal (vec3EuclideanNorm (v (x,t))) ^ (2 : ℝ)
              ∂volume) ≤ M)
    (T : ℝ) (hT : 0 < T)
    (htails : ∃ S : ℕ → ℝ≥0∞, Tendsto S atTop (𝓝 0) ∧
      (∀ (m n : ℕ) (t : ℝ), t ∈ Ioo 0 T →
        (∫⁻ x in {x : Vec3 | 2 * ((m : ℝ) + 1) < vec3EuclideanNorm x},
          ‖(WithLp.toLp 2
            (forcedRegVelocity ρ a ha f hf (εseq (σ n)) (x,t)) : L2Vec3)‖ₑ ^ (2 : ℝ)
          ∂volume) ≤ S m) ∧
      (∀ (m : ℕ) (t : ℝ), t ∈ Ioo 0 T →
        (∫⁻ x in {x : Vec3 | 2 * ((m : ℝ) + 1) < vec3EuclideanNorm x},
          ‖(WithLp.toLp 2 (v (x,t)) : L2Vec3)‖ₑ ^ (2 : ℝ) ∂volume) ≤ S m)) :
    let μ : Measure ParabolicPoint :=
      volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 T))
    let U : ℕ → ParabolicPoint → Vec3 :=
      fun n => forcedRegVelocity ρ a ha f hf (εseq (σ n))
    let J : ℕ → ParabolicPoint → Vec3 := fun n =>
      CKN.Leray.regUniformMollifiedVelocity ρ (εseq (σ n))
        (by exact (hseq (σ n)).1) (U n)
    AEStronglyMeasurable u μ ∧ MemLp u 2 μ ∧
    Tendsto (fun n => eLpNorm (U n - u) 2 μ) atTop (nhds 0) ∧
    (∀ q : ℝ, 2 ≤ q → q < 10 / 3 →
      Tendsto (fun n => eLpNorm (U n - u) (ENNReal.ofReal q) μ)
        atTop (nhds 0)) ∧
    (∀ n, MemLp (U n) 3 μ) ∧
    (∀ n, MemLp (J n) 3 μ) ∧ MemLp u 3 μ ∧
    Tendsto (fun n => eLpNorm (J n - u) 3 μ) atTop (nhds 0) := by
  intro μ U J
  classical
  obtain ⟨S, hS0, hStailU, hStailV⟩ := htails
  have hslabMeas : MeasurableSet (spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 T)) :=
    MeasurableSet.univ.prod measurableSet_Ioo
  -- regularity of the regularized velocities
  have hUmeas : ∀ n, Measurable (U n) := by
    intro n
    have hε := (hseq (σ n)).1
    change Measurable (forcedRegVelocity ρ a ha f hf (εseq (σ n)))
    rw [forcedRegVelocity_eq ρ ha hf hε]
    exact (forcedRegRep_stronglyMeasurable ρ (εseq (σ n)) hε ha hf).measurable
  have hUslab := fun n => forcedRegVelocity_memLp_slab ρ a ha f hf (εseq (σ n))
    (hseq (σ n)).1 T hT
  have hU2 : ∀ n, MemLp (U n) 2 μ := fun n => (hUslab n).1
  have hU3 : ∀ n, MemLp (U n) 3 μ := fun n => (hUslab n).2.2.1
  -- the slice energy on `(0,T]`
  obtain ⟨-, hEnergyLocal⟩ :=
    forcedLerayLimit_slice_energy_local ρ a ha f hf εseq (fun n => (hseq n).1)
  obtain ⟨A, hA, hAslice⟩ := hEnergyLocal T hT
  have hA2 : A ^ (2 : ℕ) < ⊤ := ENNReal.pow_lt_top hA
  -- the slice energy of the limit on `(0,T]`
  have hVslice : ∀ t ∈ Ioo (0 : ℝ) T,
      (∫⁻ x : Vec3, ‖(WithLp.toLp 2 (v (x, t)) : L2Vec3)‖ₑ ^ (2 : ℝ)) ≤ A ^ (2 : ℕ) := by
    intro t ht
    let K : ℕ → Set Vec3 := fun k => Metric.closedBall (0 : Vec3) (k : ℝ)
    have hK : AECover ((volume : Measure Vec3).restrict Set.univ) atTop K := by
      simpa only [Measure.restrict_univ] using
        (aecover_closedBall tendsto_natCast_atTop_atTop :
          AECover (volume : Measure Vec3) atTop K)
    have hbound := lerayLimit_lintegral_bound_of_compactExhaustion
      (μ := (volume : Measure Vec3)) Set.univ K hK
      (fun n x => (WithLp.toLp 2 (forcedRegVelocity ρ a ha f hf (εseq n) (x, t)) : L2Vec3))
      (fun x => (WithLp.toLp 2 (v (x, t)) : L2Vec3)) (A ^ (2 : ℕ))
      (fun m n => by
        rw [Measure.restrict_univ]
        exact (setLIntegral_le_lintegral _ _).trans (hAslice n t ht.1 ht.2.le))
      (fun m hsrc => by
        rw [Measure.restrict_univ] at hsrc ⊢
        have h := hSliceBound (K m) (isCompact_closedBall _ _) t t
          (fun r hr => lt_of_lt_of_le ht.1 hr.1) (A ^ (2 : ℕ)) hA2
          (fun n r hr => by
            have hrt : r = t := le_antisymm hr.2 hr.1
            subst hrt
            simp only [forcedLerayLimitStrong_enorm_sq_eq]
            exact hsrc n) t ⟨le_rfl, le_rfl⟩
        simpa only [forcedLerayLimitStrong_enorm_sq_eq] using h)
      ((PiLp.continuous_toLp 2 _).measurable.comp
        (hv.comp (measurable_prodMk_right (m := (inferInstance : MeasurableSpace Vec3))))).aemeasurable
    simpa only [Measure.restrict_univ] using hbound
  -- the exhausting cylinders
  let δ : ℕ → ℝ := fun m => T / ((m : ℝ) + 2)
  have hδpos : ∀ m, 0 < δ m := fun m => by positivity
  have hδlim : Tendsto δ atTop (𝓝 0) := by
    have h := tendsto_const_div_atTop_nhds_zero_nat T
    have hshift : Tendsto (fun m : ℕ => T / (((m + 2 : ℕ) : ℝ))) atTop (𝓝 0) :=
      h.comp (tendsto_add_atTop_nat 2)
    refine hshift.congr fun m => ?_
    push_cast
    ring
  let R : ℕ → ℝ := fun m => 2 * ((m : ℝ) + 1)
  let K : ℕ → Set ParabolicPoint := fun m => forcedLerayLimitStrongCylinder T (R m) (δ m)
  have hKmeas : ∀ m, MeasurableSet (K m) := fun m =>
    Metric.isClosed_closedBall.measurableSet.prod measurableSet_Icc
  have hKslab : ∀ m, K m ⊆ spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 T) := by
    intro m z hz
    have hd := hδpos m
    refine ⟨Set.mem_univ _, lt_of_lt_of_le hd hz.2.1, ?_⟩
    exact lt_of_le_of_lt hz.2.2 (by linarith only [hd])
  have hKcompact : ∀ m, IsCompact ((Metric.closedBall (0 : Vec3) (R m) ×ˢ
      Icc (δ m) (T - δ m)) : Set (Vec3 × ℝ)) := fun m =>
    (isCompact_closedBall _ _).prod isCompact_Icc
  have hKpos : ∀ m, ((Metric.closedBall (0 : Vec3) (R m) ×ˢ
      Icc (δ m) (T - δ m)) : Set (Vec3 × ℝ)) ⊆ (Set.univ : Set Vec3) ×ˢ Ioi (0 : ℝ) :=
    fun m z hz => ⟨Set.mem_univ _, lt_of_lt_of_le (hδpos m) hz.2.1⟩
  -- local strong convergence on the cylinders
  have hlocal : ∀ m, Tendsto (fun n => eLpNorm (U n - u) 2
      (((volume : Measure ParabolicPoint).restrict
        (spaceTimeSet Set.univ (Ioo 0 T))).restrict (K m))) atTop (𝓝 0) := by
    intro m
    have hrestr : ((volume : Measure ParabolicPoint).restrict
        (spaceTimeSet Set.univ (Ioo 0 T))).restrict (K m) =
        (volume : Measure ParabolicPoint).restrict (K m) := by
      rw [Measure.restrict_restrict (hKmeas m), inter_eq_left.2 (hKslab m)]
    rw [hrestr]
    have hs := hstrong _ (hKcompact m) (hKpos m)
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hs
      (fun n => zero_le) (fun n => ?_)
    have hae : (U n - u) =ᵐ[(volume : Measure ParabolicPoint).restrict (K m)]
        fun z => U n z - v z := by
      filter_upwards [ae_restrict_mem (hKmeas m)] with z hz
      have hz0 : 0 < z.2 := lt_of_lt_of_le (hδpos m) hz.2.1
      change U n z - u (z.1, z.2) = U n z - v z
      rw [huv z.1 z.2 hz0]
      rfl
    rw [eLpNorm_congr_ae hae]
    change eLpNorm (fun z : Vec3 × ℝ => U n z - v z) 2
        ((volume : Measure (Vec3 × ℝ)).restrict _) ≤ _
    refine eLpNorm_mono_ae
      (((hUmeas n).sub hv).aestronglyMeasurable) (Eventually.of_forall fun z => ?_)
    change ‖U n z - v z‖ ≤ ‖(WithLp.toLp 2 (U n z) : L2Vec3) - WithLp.toLp 2 (v z)‖
    rw [← WithLp.toLp_sub, ← vec3EuclideanNorm_eq_l2]
    exact norm_le_vec3EuclideanNorm _
  -- the uniform tails off the cylinders
  let b : ℕ → ℝ≥0∞ := fun m =>
    (ENNReal.ofReal T * S m + ENNReal.ofReal (2 * δ m) * A ^ (2 : ℕ)) ^ (1 / 2 : ℝ)
  have hb : Tendsto b atTop (𝓝 0) := by
    have h1 : Tendsto (fun m => ENNReal.ofReal T * S m) atTop (𝓝 0) := by
      have h := ENNReal.Tendsto.const_mul (a := ENNReal.ofReal T) hS0
        (Or.inr ENNReal.ofReal_ne_top)
      simpa using h
    have h2 : Tendsto (fun m => ENNReal.ofReal (2 * δ m) * A ^ (2 : ℕ)) atTop (𝓝 0) := by
      have h := ENNReal.Tendsto.mul_const (b := A ^ (2 : ℕ))
        (ENNReal.tendsto_ofReal (hδlim.const_mul 2)) (Or.inr hA2.ne)
      simpa using h
    have h3 := h1.add h2
    rw [add_zero] at h3
    have h4 := ((ENNReal.continuous_rpow_const (y := (1 / 2 : ℝ))).tendsto 0).comp h3
    simpa [Function.comp_def, b, ENNReal.zero_rpow_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]
      using h4
  have hbev : ∀ ε : ℝ≥0∞, 0 < ε → ∀ᶠ m : ℕ in atTop, b m ≤ ε :=
    fun ε hε => (ENNReal.tendsto_nhds_zero.mp hb) ε hε
  have hindicator : ∀ (m : ℕ) (F : ParabolicPoint → Vec3),
      (fun z => ‖(WithLp.toLp 2 (((K m)ᶜ.indicator F) z) : L2Vec3)‖ₑ ^ (2 : ℝ)) =
        (K m)ᶜ.indicator (fun z => ‖(WithLp.toLp 2 (F z) : L2Vec3)‖ₑ ^ (2 : ℝ)) := by
    intro m F
    funext z
    by_cases hz : z ∈ (K m)ᶜ
    · simp only [Set.indicator_of_mem hz]
    · simp only [Set.indicator_of_notMem hz, WithLp.toLp_zero, enorm_zero]
      exact ENNReal.zero_rpow_of_pos (by norm_num)
  have hFtail : ∀ ε : ℝ≥0∞, 0 < ε → ∀ᶠ m : ℕ in atTop,
      ∀ n, eLpNorm ((K m)ᶜ.indicator (U n)) 2
        ((volume : Measure ParabolicPoint).restrict
          (spaceTimeSet Set.univ (Ioo 0 T))) ≤ ε := by
    intro ε hε
    filter_upwards [hbev ε hε] with m hm n
    refine le_trans (forcedLerayLimitStrong_eLpNorm_le _
      (((hUmeas n).indicator (hKmeas m).compl).aestronglyMeasurable)) (le_trans ?_ hm)
    rw [hindicator m (U n)]
    refine ENNReal.rpow_le_rpow ?_ (by norm_num)
    refine forcedLerayLimitStrong_complement_lintegral_le T (R m) (δ m) (hδpos m).le
      _ ?_ (S m) (A ^ (2 : ℕ)) (fun t ht => hStailU m n t ht)
      (fun t ht => hAslice (σ n) t ht.1 ht.2.le)
    exact ((PiLp.continuous_toLp 2 _).measurable.comp (hUmeas n)).enorm.pow_const _
  have huTail : ∀ ε : ℝ≥0∞, 0 < ε → ∀ᶠ m : ℕ in atTop,
      eLpNorm ((K m)ᶜ.indicator u) 2
        ((volume : Measure ParabolicPoint).restrict
          (spaceTimeSet Set.univ (Ioo 0 T))) ≤ ε := by
    intro ε hε
    filter_upwards [hbev ε hε] with m hm
    have hae : (K m)ᶜ.indicator u =ᵐ[(volume : Measure ParabolicPoint).restrict
        (spaceTimeSet Set.univ (Ioo 0 T))] (K m)ᶜ.indicator (fun z => v z) := by
      filter_upwards [ae_restrict_mem hslabMeas] with z hz
      have hz0 : 0 < z.2 := hz.2.1
      by_cases hzK : z ∈ (K m)ᶜ
      · rw [Set.indicator_of_mem hzK, Set.indicator_of_mem hzK]
        exact huv z.1 z.2 hz0
      · rw [Set.indicator_of_notMem hzK, Set.indicator_of_notMem hzK]
    rw [eLpNorm_congr_ae hae]
    refine le_trans (forcedLerayLimitStrong_eLpNorm_le _
      ((hv.indicator (hKmeas m).compl).aestronglyMeasurable)) (le_trans ?_ hm)
    rw [hindicator m (fun z => v z)]
    refine ENNReal.rpow_le_rpow ?_ (by norm_num)
    refine forcedLerayLimitStrong_complement_lintegral_le T (R m) (δ m) (hδpos m).le
      _ ?_ (S m) (A ^ (2 : ℕ)) (fun t ht => hStailV m t ht) (fun t ht => hVslice t ht)
    exact ((PiLp.continuous_toLp 2 _).measurable.comp hv).enorm.pow_const _
  -- the energy-space and `L^{10/3}` bounds
  have hEnergy : ∀ n, MemLp (U n) (ENNReal.ofReal 2)
      ((volume : Measure ParabolicPoint).restrict (spaceTimeSet Set.univ (Ioo 0 T))) := by
    intro n
    rw [ENNReal.ofReal_ofNat]
    exact hU2 n
  have hTenThirds : ∃ B : ℝ≥0∞, B < ⊤ ∧ ∀ n,
      eLpNorm (U n) (ENNReal.ofReal (10 / 3 : ℝ))
        ((volume : Measure ParabolicPoint).restrict
          (spaceTimeSet Set.univ (Ioo 0 T))) ≤ B := by
    let E : ℝ := Real.exp T * ((∑ i : Fin 3, ∫ x : Vec3, a x i ^ 2) +
      ∑ i : Fin 3, ∫ z in spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 T), f z i ^ 2)
    let G : ℝ := ((∑ i : Fin 3, ∫ x : Vec3, a x i ^ 2) +
      (∑ i : Fin 3, ∫ z in spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 T), f z i ^ 2) +
      T * E) / 2
    let Cst : ℝ≥0∞ := (CKN.gagliardoNirenbergSobolevConstant ^ (3 / 5 : ℝ)) ^ (10 / 3 : ℝ) *
      ENNReal.ofReal (Real.sqrt E) ^ (4 / 3 : ℝ) * ENNReal.ofReal G
    have hCst : Cst < ⊤ := by
      have hGN : (CKN.gagliardoNirenbergSobolevConstant ^ (3 / 5 : ℝ)) ^ (10 / 3 : ℝ) < ⊤ :=
        ENNReal.rpow_lt_top_of_nonneg (by norm_num) (ENNReal.rpow_lt_top_of_nonneg
          (by norm_num) gagliardoNirenbergSobolevConstant_ne_top).ne
      exact ENNReal.mul_lt_top (ENNReal.mul_lt_top hGN
        (ENNReal.rpow_lt_top_of_nonneg (by norm_num) ENNReal.ofReal_ne_top))
        ENNReal.ofReal_lt_top
    have hcomp : ∀ n (i : Fin 3), eLpNorm (fun z : ParabolicPoint => U n z i)
        (ENNReal.ofReal (10 / 3 : ℝ)) μ ≤ Cst ^ (3 / 10 : ℝ) := by
      intro n i
      have h := (hUslab n).2.2.2 i
      have h' := ENNReal.rpow_le_rpow h (by norm_num : (0 : ℝ) ≤ 3 / 10)
      rw [← ENNReal.rpow_mul] at h'
      norm_num at h'
      exact h'
    have hvec := lerayLimit_vector_tenThirds_of_component_bounds μ U (Cst ^ (3 / 10 : ℝ))
      (fun n i => ((hUslab n).2.1).eval i) hcomp
    refine ⟨3 * Cst ^ (3 / 10 : ℝ), ENNReal.mul_lt_top (by norm_num)
      (ENNReal.rpow_lt_top_of_nonneg (by norm_num) hCst.ne), fun n => (hvec n).2⟩
  -- the whole-slab strong convergence
  have hLq := lerayLimit_spaceTime_strongLp_of_local_compactness_and_tails
    T U u K hKmeas hlocal hFtail huTail hEnergy hTenThirds
  have hL2 : Tendsto (fun n => eLpNorm (U n - u) 2 μ) atTop (𝓝 0) := by
    have h := hLq 2 le_rfl (by norm_num)
    rwa [ENNReal.ofReal_ofNat] at h
  have hL3 : Tendsto (fun n => eLpNorm (U n - u) (ENNReal.ofReal (3 : ℝ)) μ)
      atTop (𝓝 0) := hLq 3 (by norm_num) (by norm_num)
  have hu2 : MemLp u 2 μ := by
    obtain ⟨n, hn⟩ := ((ENNReal.tendsto_nhds_zero.mp hL2) (1 / 2 : ℝ≥0∞)
      (by norm_num)).exists
    have hdiff : MemLp (U n - u) 2 μ := lt_of_le_of_lt hn (by norm_num)
    have heq : u = U n - (U n - u) := by
      funext z
      change u z = U n z - (U n z - u z)
      abel
    rw [heq]
    exact (hU2 n).sub hdiff
  -- the mollified transport fields
  have hUslice : ∀ n, ∀ t : ℝ, 0 ≤ t → MemLp (fun x : Vec3 => U n (x, t)) 2 volume := by
    intro n t ht
    obtain ⟨⟨hSlice, -⟩, -⟩ := forcedRegularised ρ a ha f hf (εseq (σ n)) (hseq (σ n)).1
    exact hSlice t ht
  obtain ⟨hJ3, hu3, hJconv⟩ := forcedLerayLimit_mollified_convergence_of_strong_three ρ T
    (fun n => εseq (σ n)) (fun n => (hseq (σ n)).1) hεsub U u hUmeas hUslice hU3 hL3
  exact ⟨hu2.aestronglyMeasurable, hu2, hL2, hLq, hU3, hJ3, hu3, hJconv⟩

end CKN.Leray

end
