/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Leray.ForcedLerayLimitPropStrong

/-!
# Strong convergence on a slab in `prop:leray-limit`

Local strong `L²` convergence on compact subsets of positive time, a uniform
slice energy bound and uniform spatial tails give strong `L²` convergence on
the whole slab `ℝ³ × (0,T)`. The sequence is only assumed continuous at
positive times; its measurable extension by zero agrees with it on the slab.
The file also records the transfer of a slice energy bound to a local weak
limit and the interpolation of `Lᵖ` membership between two exponents.
-/

public section

open MeasureTheory Filter Set
open scoped ENNReal Topology
open CKN CKN.Foundation.Parabolic

noncomputable section

namespace CKN.Leray

/-- Membership in `Lᵖ` and in `Lʳ` gives membership in `L^q` for every
`p ≤ q ≤ r`. -/
theorem lerayLimit_memLp_of_exponent_between
    {α E : Type*} [MeasurableSpace α] [NormedAddCommGroup E]
    {μ : Measure α} {f : α → E} {p q r : ℝ} (hp : 0 < p) (hpq : p ≤ q) (hqr : q ≤ r)
    (hfp : MemLp f (ENNReal.ofReal p) μ) (hfr : MemLp f (ENNReal.ofReal r) μ) :
    MemLp f (ENNReal.ofReal q) μ := by
  have hq : 0 < q := lt_of_lt_of_le hp hpq
  have hr : 0 < r := lt_of_lt_of_le hq hqr
  have hintp : Integrable (fun x => ‖f x‖ ^ p) μ := by
    have h := hfp.integrable_norm_rpow (by simp [hp]) ENNReal.ofReal_ne_top
    rwa [ENNReal.toReal_ofReal hp.le] at h
  have hintr : Integrable (fun x => ‖f x‖ ^ r) μ := by
    have h := hfr.integrable_norm_rpow (by simp [hr]) ENNReal.ofReal_ne_top
    rwa [ENNReal.toReal_ofReal hr.le] at h
  have hmeas : AEStronglyMeasurable (fun x => ‖f x‖ ^ q) μ :=
    (continuous_norm.comp_aestronglyMeasurable hfp.aestronglyMeasurable).aemeasurable.pow_const
      _ |>.aestronglyMeasurable
  have hint : Integrable (fun x => ‖f x‖ ^ q) μ := by
    refine (hintp.add hintr).mono' hmeas (Eventually.of_forall fun x => ?_)
    have hy : 0 ≤ ‖f x‖ := norm_nonneg _
    rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg hy q)]
    by_cases h1 : ‖f x‖ ≤ 1
    · have h := Real.rpow_le_rpow_of_exponent_ge' hy h1 hp.le hpq
      have h' : 0 ≤ ‖f x‖ ^ r := Real.rpow_nonneg hy r
      change ‖f x‖ ^ q ≤ ‖f x‖ ^ p + ‖f x‖ ^ r
      linarith only [h, h']
    · have h := Real.rpow_le_rpow_of_exponent_le (le_of_lt (not_le.mp h1)) hqr
      have h' : 0 ≤ ‖f x‖ ^ p := Real.rpow_nonneg hy p
      change ‖f x‖ ^ q ≤ ‖f x‖ ^ p + ‖f x‖ ^ r
      linarith only [h, h']
  have h := (integrable_norm_rpow_iff hfp.aestronglyMeasurable (p := ENNReal.ofReal q)
    (by simp [hq]) ENNReal.ofReal_ne_top).1
  rw [ENNReal.toReal_ofReal hq.le] at h
  exact h hint

/-- A slice bound for a sequence at a positive time passes to its local weak
limit, given the transfer of slice bounds on compact sets from the
compactness step. -/
theorem lerayLimit_limit_slice_le_of_compact_transfer
    (G : ℕ → Vec3 × ℝ → Vec3) (v : Vec3 × ℝ → Vec3) (hv : Measurable v)
    (M : ℝ≥0∞) (hM : M < ⊤) (t : ℝ) (ht : 0 < t)
    (hGslice : ∀ n,
      (∫⁻ x : Vec3, ‖(WithLp.toLp 2 (G n (x, t)) : L2Vec3)‖ₑ ^ (2 : ℝ)) ≤ M)
    (hSliceBound : ∀ C : Set Vec3, IsCompact C → C ⊆ (Set.univ : Set Vec3) →
        ∀ b₁ b₂ : ℝ, Icc b₁ b₂ ⊆ Ioi (0 : ℝ) →
        ∀ M : ℝ≥0∞, M < ⊤ →
          (∀ n s, s ∈ Icc b₁ b₂ →
            (∫⁻ x in C, ENNReal.ofReal
              (vec3EuclideanNorm (G n (x, s))) ^ (2 : ℝ) ∂volume) ≤ M) →
          ∀ s ∈ Icc b₁ b₂,
            (∫⁻ x in C, ENNReal.ofReal (vec3EuclideanNorm (v (x, s))) ^ (2 : ℝ)
              ∂volume) ≤ M) :
    (∫⁻ x : Vec3, ‖(WithLp.toLp 2 (v (x, t)) : L2Vec3)‖ₑ ^ (2 : ℝ)) ≤ M := by
  have hsq : ∀ y : Vec3, ENNReal.ofReal (vec3EuclideanNorm y) ^ (2 : ℝ) =
      ‖(WithLp.toLp 2 y : L2Vec3)‖ₑ ^ (2 : ℝ) := fun y => by
    rw [vec3EuclideanNorm_eq_l2, ofReal_norm]
  let K : ℕ → Set Vec3 := fun k => Metric.closedBall (0 : Vec3) (k : ℝ)
  have hK : AECover ((volume : Measure Vec3).restrict Set.univ) atTop K := by
    simpa only [Measure.restrict_univ] using
      (aecover_closedBall tendsto_natCast_atTop_atTop :
        AECover (volume : Measure Vec3) atTop K)
  have hbound := lerayLimit_lintegral_bound_of_compactExhaustion
    (μ := (volume : Measure Vec3)) Set.univ K hK
    (fun n x => (WithLp.toLp 2 (G n (x, t)) : L2Vec3))
    (fun x => (WithLp.toLp 2 (v (x, t)) : L2Vec3)) M
    (fun m n => by
      rw [Measure.restrict_univ]
      exact (setLIntegral_le_lintegral _ _).trans (hGslice n))
    (fun m hsrc => by
      rw [Measure.restrict_univ] at hsrc ⊢
      have h := hSliceBound (K m) (isCompact_closedBall _ _) (Set.subset_univ _) t t
        (fun r hr => lt_of_lt_of_le ht hr.1) M hM
        (fun n r hr => by
          have hrt : r = t := le_antisymm hr.2 hr.1
          subst hrt
          simp only [hsq]
          exact hsrc n) t ⟨le_rfl, le_rfl⟩
      simpa only [hsq] using h)
    ((PiLp.continuous_toLp 2 _).measurable.comp
      (hv.comp
        (measurable_prodMk_right (m := (inferInstance : MeasurableSpace Vec3))))).aemeasurable
  simpa only [Measure.restrict_univ] using hbound

/-- The integral over the slab `ℝ³ × (0,T)` of a density off the compact
cylinder `closedBall(0,R) × [δ, T - δ]` is bounded by the exterior spatial tails on
`(0,T)` and the slice integrals near the two ends of the time interval. -/
private theorem lerayLimitFinal_complement_lintegral_le
    (T R δ : ℝ) (hδ : 0 ≤ δ) (Φ : ParabolicPoint → ℝ≥0∞) (hΦ : Measurable Φ)
    (S A : ℝ≥0∞)
    (htail : ∀ t ∈ Ioo 0 T,
      (∫⁻ x in {x : Vec3 | R < vec3EuclideanNorm x}, Φ (x, t)) ≤ S)
    (hslice : ∀ t ∈ Ioo 0 T, (∫⁻ x : Vec3, Φ (x, t)) ≤ A) :
    (∫⁻ z in spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 T),
      (spaceTimeSet (Metric.closedBall (0 : Vec3) R) (Icc δ (T - δ)))ᶜ.indicator Φ z) ≤
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
      (spaceTimeSet (Metric.closedBall (0 : Vec3) R) (Icc δ (T - δ)))ᶜ.indicator Φ z ≤
        g₁ z + g₂ z := by
    intro z
    by_cases hz : z ∈ spaceTimeSet (Metric.closedBall (0 : Vec3) R) (Icc δ (T - δ))
    · simp [hz]
    · rw [Set.indicator_of_mem (show z ∈
        (spaceTimeSet (Metric.closedBall (0 : Vec3) R) (Icc δ (T - δ)))ᶜ from hz)]
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
      (spaceTimeSet (Metric.closedBall (0 : Vec3) R) (Icc δ (T - δ)))ᶜ.indicator Φ z) ≤
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

/-- The `L²` seminorm of a vector field on any measure space is at most the
square root of the integral of the square of its Euclidean norm. -/
private theorem lerayLimitFinal_eLpNorm_le_sqrt
    {α : Type*} [MeasurableSpace α] {μ : Measure α} (F : α → Vec3)
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

/-- Strong `L²` convergence on the slab `ℝ³ × (0,T)` in `prop:leray-limit`.
The sequence `F n` is continuous at positive times and agrees there with the
sequence `G n` of the compactness step; `G n → v` strongly in `L²` on compact
subsets of positive time; `u = v` at positive times; the slices of `F n` and
of `v` are bounded by `A²` on `(0,T)`; and their exterior slice energies beyond
the radius `2(m+1)` are bounded on `(0,T)` by one sequence `S m → 0`. Then
`F n` and `u` are square integrable on the slab and `F n → u` in `L²`. -/
theorem lerayLimit_slab_strongL2_of_local_and_tails
    (T : ℝ) (hT : 0 < T)
    (F : ℕ → ParabolicPoint → Vec3) (G : ℕ → Vec3 × ℝ → Vec3)
    (hFcont : ∀ n (i : Fin 3), ContinuousOn (fun z => F n z i)
      (spaceTimeSet (Set.univ : Set Vec3) (Ioi 0)))
    (hGF : ∀ n (x : Vec3) (t : ℝ), 0 < t → G n (x, t) = F n (x, t))
    (v : Vec3 × ℝ → Vec3) (hv : Measurable v)
    (u : ParabolicPoint → Vec3)
    (huv : ∀ (x : Vec3) (t : ℝ), 0 < t → u (x, t) = v (x, t))
    (hstrong : ∀ Q : Set (Vec3 × ℝ), IsCompact Q → Q ⊆
        (Set.univ : Set Vec3) ×ˢ Ioi (0 : ℝ) →
        Tendsto (fun k => eLpNorm
          ((fun z : Vec3 × ℝ => (WithLp.toLp 2 (G k z) : L2Vec3)) -
            (fun z : Vec3 × ℝ => (WithLp.toLp 2 (v z) : L2Vec3))) 2
          (volume.restrict Q)) atTop (nhds 0))
    (A : ℝ≥0∞) (hA : A < ⊤)
    (hFslice : ∀ n (t : ℝ), t ∈ Ioo 0 T →
      (∫⁻ x : Vec3, ‖(WithLp.toLp 2 (F n (x, t)) : L2Vec3)‖ₑ ^ (2 : ℝ)) ≤ A ^ (2 : ℕ))
    (hvslice : ∀ t ∈ Ioo (0 : ℝ) T,
      (∫⁻ x : Vec3, ‖(WithLp.toLp 2 (v (x, t)) : L2Vec3)‖ₑ ^ (2 : ℝ)) ≤ A ^ (2 : ℕ))
    (htails : ∃ S : ℕ → ℝ≥0∞, Tendsto S atTop (𝓝 0) ∧
      (∀ (m n : ℕ) (t : ℝ), t ∈ Ioo 0 T →
        (∫⁻ x in {x : Vec3 | 2 * ((m : ℝ) + 1) < vec3EuclideanNorm x},
          ‖(WithLp.toLp 2 (F n (x, t)) : L2Vec3)‖ₑ ^ (2 : ℝ) ∂volume) ≤ S m) ∧
      (∀ (m : ℕ) (t : ℝ), t ∈ Ioo 0 T →
        (∫⁻ x in {x : Vec3 | 2 * ((m : ℝ) + 1) < vec3EuclideanNorm x},
          ‖(WithLp.toLp 2 (v (x, t)) : L2Vec3)‖ₑ ^ (2 : ℝ) ∂volume) ≤ S m)) :
    let μ : Measure ParabolicPoint :=
      volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 T))
    (∀ n, MemLp (F n) 2 μ) ∧ MemLp u 2 μ ∧
      Tendsto (fun n => eLpNorm (F n - u) 2 μ) atTop (𝓝 0) := by
  intro μ
  classical
  obtain ⟨S, hS0, hStailF, hStailV⟩ := htails
  have hA2 : A ^ (2 : ℕ) < ⊤ := ENNReal.pow_lt_top hA
  have hslabMeas : MeasurableSet (spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 T)) :=
    MeasurableSet.univ.prod measurableSet_Ioo
  -- the measurable extension by zero of the sequence
  let P : Set ParabolicPoint := spaceTimeSet (Set.univ : Set Vec3) (Ioi 0)
  have hPmeas : MeasurableSet P := MeasurableSet.univ.prod measurableSet_Ioi
  let Fc : ℕ → ParabolicPoint → Vec3 := fun n => P.piecewise (F n) 0
  have hFcmeas : ∀ n, Measurable (Fc n) := fun n =>
    (continuousOn_pi.mpr (hFcont n)).measurable_piecewise continuousOn_const hPmeas
  have hFcpos : ∀ n (z : ParabolicPoint), 0 < z.2 → Fc n z = F n z := fun n z hz =>
    piecewise_eq_of_mem _ _ _ (show z ∈ P from ⟨Set.mem_univ _, hz⟩)
  have hFcae : ∀ n, Fc n =ᵐ[μ] F n := by
    intro n
    filter_upwards [ae_restrict_mem hslabMeas] with z hz
    exact hFcpos n z hz.2.1
  have hFcslice : ∀ n (t : ℝ), t ∈ Ioo 0 T →
      (∫⁻ x : Vec3, ‖(WithLp.toLp 2 (Fc n (x, t)) : L2Vec3)‖ₑ ^ (2 : ℝ)) ≤ A ^ (2 : ℕ) := by
    intro n t ht
    have hfun : (fun x : Vec3 => ‖(WithLp.toLp 2 (Fc n (x, t)) : L2Vec3)‖ₑ ^ (2 : ℝ)) =
        fun x => ‖(WithLp.toLp 2 (F n (x, t)) : L2Vec3)‖ₑ ^ (2 : ℝ) := by
      funext x
      rw [hFcpos n (x, t) ht.1]
    rw [hfun]
    exact hFslice n t ht
  have hFctail : ∀ (m n : ℕ) (t : ℝ), t ∈ Ioo 0 T →
      (∫⁻ x in {x : Vec3 | 2 * ((m : ℝ) + 1) < vec3EuclideanNorm x},
        ‖(WithLp.toLp 2 (Fc n (x, t)) : L2Vec3)‖ₑ ^ (2 : ℝ) ∂volume) ≤ S m := by
    intro m n t ht
    have hfun : (fun x : Vec3 => ‖(WithLp.toLp 2 (Fc n (x, t)) : L2Vec3)‖ₑ ^ (2 : ℝ)) =
        fun x => ‖(WithLp.toLp 2 (F n (x, t)) : L2Vec3)‖ₑ ^ (2 : ℝ) := by
      funext x
      rw [hFcpos n (x, t) ht.1]
    rw [hfun]
    exact hStailF m n t ht
  -- square integrability of the sequence on the slab
  have hFc2 : ∀ n, MemLp (Fc n) 2 μ := by
    intro n
    refine lt_of_le_of_lt (lerayLimitFinal_eLpNorm_le_sqrt (Fc n)
      (hFcmeas n).aestronglyMeasurable) ?_
    let Φ : Vec3 × ℝ → ℝ≥0∞ := fun z => ‖(WithLp.toLp 2 (Fc n z) : L2Vec3)‖ₑ ^ (2 : ℝ)
    have hΦ : Measurable Φ :=
      ((PiLp.continuous_toLp 2 _).measurable.comp (hFcmeas n)).enorm.pow_const _
    have hle : (∫⁻ z, ‖(WithLp.toLp 2 (Fc n z) : L2Vec3)‖ₑ ^ (2 : ℝ) ∂μ) ≤
        ENNReal.ofReal T * A ^ (2 : ℕ) := by
      change (∫⁻ z in spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 T), Φ z) ≤ _
      rw [lintegral_slab_eq_prod Φ (Ioo 0 T), lintegral_prod_symm' Φ hΦ]
      calc (∫⁻ t in Ioo 0 T, ∫⁻ x, ‖(WithLp.toLp 2 (Fc n (x, t)) : L2Vec3)‖ₑ ^ (2 : ℝ))
          ≤ ∫⁻ _t in Ioo 0 T, A ^ (2 : ℕ) :=
            setLIntegral_mono measurable_const (fun t ht => hFcslice n t ht)
        _ = ENNReal.ofReal T * A ^ (2 : ℕ) := by
            rw [setLIntegral_const, Real.volume_Ioo, sub_zero, mul_comm]
    exact ENNReal.rpow_lt_top_of_nonneg (by norm_num)
      (lt_of_le_of_lt hle (ENNReal.mul_lt_top ENNReal.ofReal_lt_top hA2)).ne
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
  let K : ℕ → Set ParabolicPoint := fun m =>
    spaceTimeSet (Metric.closedBall (0 : Vec3) (R m)) (Icc (δ m) (T - δ m))
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
  have hlocal : ∀ m, Tendsto (fun n => eLpNorm (Fc n - u) 2
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
    have hae : (Fc n - u) =ᵐ[(volume : Measure ParabolicPoint).restrict (K m)]
        fun z => Fc n z - v z := by
      filter_upwards [ae_restrict_mem (hKmeas m)] with z hz
      have hz0 : 0 < z.2 := lt_of_lt_of_le (hδpos m) hz.2.1
      change Fc n z - u (z.1, z.2) = Fc n z - v z
      rw [huv z.1 z.2 hz0]
      rfl
    rw [eLpNorm_congr_ae hae]
    change eLpNorm (fun z : Vec3 × ℝ => Fc n z - v z) 2
        ((volume : Measure (Vec3 × ℝ)).restrict _) ≤ _
    refine eLpNorm_mono_ae (((hFcmeas n).sub hv).aestronglyMeasurable) ?_
    filter_upwards [ae_restrict_mem (hKmeas m)] with z hz
    have hz0 : 0 < z.2 := lt_of_lt_of_le (hδpos m) hz.2.1
    have hGz : G n z = Fc n z := by
      have h := hGF n z.1 z.2 hz0
      rw [Prod.mk.eta] at h
      rw [h, hFcpos n z hz0]
    change ‖Fc n z - v z‖ ≤ ‖(WithLp.toLp 2 (G n z) : L2Vec3) - WithLp.toLp 2 (v z)‖
    rw [hGz, ← WithLp.toLp_sub, ← vec3EuclideanNorm_eq_l2]
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
  have hindicator : ∀ (m : ℕ) (H : ParabolicPoint → Vec3),
      (fun z => ‖(WithLp.toLp 2 (((K m)ᶜ.indicator H) z) : L2Vec3)‖ₑ ^ (2 : ℝ)) =
        (K m)ᶜ.indicator (fun z => ‖(WithLp.toLp 2 (H z) : L2Vec3)‖ₑ ^ (2 : ℝ)) := by
    intro m H
    funext z
    by_cases hz : z ∈ (K m)ᶜ
    · simp only [Set.indicator_of_mem hz]
    · simp only [Set.indicator_of_notMem hz, WithLp.toLp_zero, enorm_zero]
      exact ENNReal.zero_rpow_of_pos (by norm_num)
  have hFtail : ∀ ε : ℝ≥0∞, 0 < ε → ∀ᶠ m : ℕ in atTop,
      ∀ n, eLpNorm ((K m)ᶜ.indicator (Fc n)) 2
        ((volume : Measure ParabolicPoint).restrict
          (spaceTimeSet Set.univ (Ioo 0 T))) ≤ ε := by
    intro ε hε
    filter_upwards [hbev ε hε] with m hm n
    refine le_trans (lerayLimitFinal_eLpNorm_le_sqrt _
      (((hFcmeas n).indicator (hKmeas m).compl).aestronglyMeasurable)) (le_trans ?_ hm)
    rw [hindicator m (Fc n)]
    refine ENNReal.rpow_le_rpow ?_ (by norm_num)
    refine lerayLimitFinal_complement_lintegral_le T (R m) (δ m) (hδpos m).le
      _ ?_ (S m) (A ^ (2 : ℕ)) (fun t ht => hFctail m n t ht)
      (fun t ht => hFcslice n t ht)
    exact ((PiLp.continuous_toLp 2 _).measurable.comp (hFcmeas n)).enorm.pow_const _
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
    refine le_trans (lerayLimitFinal_eLpNorm_le_sqrt _
      ((hv.indicator (hKmeas m).compl).aestronglyMeasurable)) (le_trans ?_ hm)
    rw [hindicator m (fun z => v z)]
    refine ENNReal.rpow_le_rpow ?_ (by norm_num)
    refine lerayLimitFinal_complement_lintegral_le T (R m) (δ m) (hδpos m).le
      _ ?_ (S m) (A ^ (2 : ℕ)) (fun t ht => hStailV m t ht) (fun t ht => hvslice t ht)
    exact ((PiLp.continuous_toLp 2 _).measurable.comp hv).enorm.pow_const _
  -- the whole-slab strong convergence
  have hL2c : Tendsto (fun n => eLpNorm (Fc n - u) 2 μ) atTop (𝓝 0) :=
    lerayLimit_eLpNorm_tendsto_of_local_and_uniform_tails Fc u K hKmeas hlocal hFtail huTail
  have hL2 : Tendsto (fun n => eLpNorm (F n - u) 2 μ) atTop (𝓝 0) := by
    refine hL2c.congr fun n => eLpNorm_congr_ae ?_
    filter_upwards [hFcae n] with z hz
    change Fc n z - u z = F n z - u z
    rw [hz]
  have hF2 : ∀ n, MemLp (F n) 2 μ := fun n => (memLp_congr_ae (hFcae n)).1 (hFc2 n)
  have hu2 : MemLp u 2 μ := by
    obtain ⟨n, hn⟩ := ((ENNReal.tendsto_nhds_zero.mp hL2) (1 / 2 : ℝ≥0∞)
      (by norm_num)).exists
    have hdiff : MemLp (F n - u) 2 μ := lt_of_le_of_lt hn (by norm_num)
    have heq : u = F n - (F n - u) := by
      funext z
      change u z = F n z - (F n z - u z)
      abel
    rw [heq]
    exact (hF2 n).sub hdiff
  exact ⟨hF2, hu2, hL2⟩

end CKN.Leray

end
