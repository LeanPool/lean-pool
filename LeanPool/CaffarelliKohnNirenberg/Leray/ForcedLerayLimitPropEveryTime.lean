/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Leray.LerayLimitEveryTime
public import LeanPool.CaffarelliKohnNirenberg.Leray.ForcedLerayLimitCompactnessInputs
public import LeanPool.CaffarelliKohnNirenberg.Leray.CompactnessLocalPairing
public import LeanPool.CaffarelliKohnNirenberg.Statements.SpaceTimeSet
public import Mathlib.MeasureTheory.Integral.IntegralEqImproper

/-!
# Weak convergence of every positive-time slice, with time-local energy bounds

In `prop:forced-limit` the forced regularized velocities converge weakly in
`L²` on every positive-time slice, tested against every global `L²` field. As
in `prop:leray-limit`, the local compactness step gives this on compact
spatial sets and the energy bound extends it to global tests. The forced
energy bound of `lem:forced-energy-bounds` is uniform only on bounded time
intervals, and the forced regularized velocities are only measurable, so the
energy and regularity inputs here are the time-local and measurable versions
of those in `CKN.Leray.lerayLimit_everyTime_pairing_tendsto`.
-/

public section

open MeasureTheory Filter Set
open scoped ENNReal Topology
open CKN CKN.Foundation.Parabolic

noncomputable section

namespace CKN.Leray

/-- Every-time weak convergence with time-local energy bounds, as used in
`prop:forced-limit`: the local every-time weak convergence on compact spatial
sets from the compactness step, the transfer of compact slice bounds to the
limit, measurable positive-time slices, and a slice energy bound uniform on
each bounded time interval give convergence of the coordinate pairings of
every positive-time slice with every global `L²` field. -/
theorem lerayLimit_everyTime_pairing_tendsto_of_local_energy
    (F : ℕ → ParabolicPoint → Vec3) (G : ℕ → Vec3 × ℝ → Vec3) (σ : ℕ → ℕ)
    (v : Vec3 × ℝ → Vec3) (u : ParabolicPoint → Vec3)
    (hFmeas : ∀ n (t : ℝ), 0 < t → Measurable (fun x : Vec3 => F n (x, t)))
    (hv : Measurable v)
    (hGF : ∀ n (x : Vec3) (t : ℝ), 0 < t → G n (x, t) = F n (x, t))
    (huv : ∀ (x : Vec3) (t : ℝ), 0 < t → u (x, t) = v (x, t))
    (hEnergy : ∀ T : ℝ, 0 < T → ∃ A : ℝ≥0∞, A < ⊤ ∧
      ∀ n (t : ℝ), 0 < t → t ≤ T →
        (∫⁻ x : Vec3, ‖WithLp.toLp 2 (F n (x, t))‖ₑ ^ (2 : ℝ) ∂volume) ≤
          A ^ (2 : ℕ))
    (hlocal : ∀ t : Set.Ioi (0 : ℝ), ∀ C : Set Vec3, IsCompact C →
      C ⊆ (Set.univ : Set Vec3) →
      ∃ hs : ∀ k, MemLp
        (fun x : Vec3 => (WithLp.toLp 2 (G (σ k) (x, t.1)) : L2Vec3))
        2 (volume.restrict C),
      ∃ hl : MemLp
        (fun x : Vec3 => (WithLp.toLp 2 (v (x, t.1)) : L2Vec3))
        2 (volume.restrict C),
      ∀ w : Lp L2Vec3 2 (volume.restrict C),
        Tendsto (fun k => inner ℝ ((hs k).toLp
          (fun x => (WithLp.toLp 2 (G (σ k) (x, t.1)) : L2Vec3))) w)
          atTop (nhds (inner ℝ (hl.toLp
            (fun x => (WithLp.toLp 2 (v (x, t.1)) : L2Vec3))) w)))
    (hSliceBound : ∀ C : Set Vec3, IsCompact C → C ⊆ (Set.univ : Set Vec3) →
      ∀ b₁ b₂ : ℝ, Icc b₁ b₂ ⊆ Ioi (0 : ℝ) →
      ∀ M : ℝ≥0∞, M < ⊤ →
        (∀ n t, t ∈ Icc b₁ b₂ →
          (∫⁻ x in C, ENNReal.ofReal
            (vec3EuclideanNorm (G n (x, t))) ^ (2 : ℝ) ∂volume) ≤ M) →
        ∀ t ∈ Icc b₁ b₂,
          (∫⁻ x in C, ENNReal.ofReal
            (vec3EuclideanNorm (v (x, t))) ^ (2 : ℝ) ∂volume) ≤ M) :
    ∀ t : ℝ, 0 < t → ∀ w : Vec3 → Vec3, MemLp w 2 volume →
      Tendsto (fun n => ∫ x : Vec3, ∑ i : Fin 3, F (σ n) (x, t) i * w x i)
        atTop (𝓝 (∫ x : Vec3, ∑ i : Fin 3, u (x, t) i * w x i)) := by
  classical
  intro t ht w hw
  obtain ⟨A, hA, hEnergyT⟩ := hEnergy t ht
  let F' : ℕ → ℝ → Vec3 → Vec3 := fun n s x =>
    if 0 < s ∧ s ≤ t then F (σ n) (x, s) else 0
  let u' : ℝ → Vec3 → Vec3 := fun s x => if s ≤ t then v (x, s) else 0
  let K : ℕ → Set Vec3 := fun k => Metric.closedBall (0 : Vec3) (k : ℝ)
  have hK : AECover (volume : Measure Vec3) atTop K :=
    aecover_closedBall tendsto_natCast_atTop_atTop
  let C : ℝ := A.toReal
  have hC : 0 ≤ C := ENNReal.toReal_nonneg
  have hCA : ENNReal.ofReal C = A := ENNReal.ofReal_toReal hA.ne
  have henorm (y : Vec3) :
      ENNReal.ofReal (vec3EuclideanNorm y) = ‖(WithLp.toLp 2 y : L2Vec3)‖ₑ := by
    rw [vec3EuclideanNorm_eq_l2, ofReal_norm]
  have hF'meas : ∀ n s, Measurable (fun x : Vec3 => F' n s x) := by
    intro n s
    by_cases hs : 0 < s ∧ s ≤ t
    · simp only [F', hs, and_self, ↓reduceIte]
      exact hFmeas (σ n) s hs.1
    · simp only [F', hs, ↓reduceIte]
      exact measurable_const
  have humeas : ∀ s, Measurable (fun x : Vec3 => u' s x) := by
    intro s
    by_cases hst : s ≤ t
    · simp only [u', hst, ↓reduceIte]
      exact hv.comp (measurable_prodMk_right (m := (inferInstance : MeasurableSpace Vec3)))
    · simp only [u', hst, ↓reduceIte]
      exact measurable_const
  have hFbound : ∀ s n k,
      (∫⁻ x in K k, ENNReal.ofReal (vec3EuclideanNorm (F' n s x)) ^ (2 : ℝ)
        ∂volume) ≤ ENNReal.ofReal C ^ (2 : ℕ) := by
    intro s n k
    rw [hCA]
    by_cases hs : 0 < s ∧ s ≤ t
    · simp only [F', hs, and_self, ↓reduceIte, henorm]
      exact (setLIntegral_le_lintegral _ _).trans (hEnergyT (σ n) s hs.1 hs.2)
    · have hzero : ∀ x, ENNReal.ofReal (vec3EuclideanNorm (F' n s x)) ^ (2 : ℝ) = 0 := by
        intro x
        simp only [F', hs, ↓reduceIte, henorm, WithLp.toLp_zero, enorm_zero]
        exact ENNReal.zero_rpow_of_pos (by norm_num)
      simp only [hzero, lintegral_zero]
      exact zero_le
  have hubound : ∀ s, 0 < s → ∀ k,
      (∫⁻ x in K k, ENNReal.ofReal (vec3EuclideanNorm (u' s x)) ^ (2 : ℝ)
        ∂volume) ≤ ENNReal.ofReal C ^ (2 : ℕ) := by
    intro s hs k
    rw [hCA]
    by_cases hst : s ≤ t
    swap
    · have hzero : ∀ x, ENNReal.ofReal (vec3EuclideanNorm (u' s x)) ^ (2 : ℝ) = 0 := by
        intro x
        simp only [u', hst, ↓reduceIte, henorm, WithLp.toLp_zero, enorm_zero]
        exact ENNReal.zero_rpow_of_pos (by norm_num)
      simp only [hzero, lintegral_zero]
      exact zero_le
    simp only [u', hst, ↓reduceIte]
    refine hSliceBound (K k) (isCompact_closedBall _ _) (Set.subset_univ _) s s
      (fun r hr => lt_of_lt_of_le hs hr.1) (A ^ (2 : ℕ))
      (ENNReal.pow_ne_top hA.ne).lt_top ?_ s ⟨le_rfl, le_rfl⟩
    intro n r hr
    have hrs : r = s := le_antisymm hr.2 hr.1
    subst hrs
    have hfun : (fun x : Vec3 =>
        ENNReal.ofReal (vec3EuclideanNorm (G n (x, r))) ^ (2 : ℝ)) =
        fun x : Vec3 => ‖(WithLp.toLp 2 (F n (x, r)) : L2Vec3)‖ₑ ^ (2 : ℝ) := by
      funext x
      rw [hGF n x r hs, henorm]
    rw [hfun]
    exact (setLIntegral_le_lintegral _ _).trans (hEnergyT n r hs hst)
  have hlocal' : ∀ s, 0 < s → ∀ (w' : Vec3 → L2Vec3),
      HasCompactSupport w' → Continuous w' → (hw' : MemLp w' 2 volume) →
      ∀ (hF : ∀ n, MemLp
          (fun x : Vec3 => (WithLp.toLp 2 (F' n s x) : L2Vec3)) 2 volume)
        (hu : MemLp
          (fun x : Vec3 => (WithLp.toLp 2 (u' s x) : L2Vec3)) 2 volume),
      Tendsto
        (fun n => inner ℝ
          ((hF n).toLp (fun x => WithLp.toLp 2 (F' n s x)))
          (hw'.toLp w')) atTop
        (𝓝 (inner ℝ
          (hu.toLp (fun x => WithLp.toLp 2 (u' s x)))
          (hw'.toLp w'))) := by
    intro s hs w' hw'c _ hw' hF hu
    by_cases hst : s ≤ t
    swap
    · have hleft0 (n : ℕ) :
          inner ℝ ((hF n).toLp (fun x => WithLp.toLp 2 (F' n s x)))
            (hw'.toLp w') = 0 := by
        rw [inner_toLp_vec3_eq_integral_dot_measure]
        simp [F', hst]
      have hright0 :
          inner ℝ (hu.toLp (fun x => WithLp.toLp 2 (u' s x))) (hw'.toLp w') = 0 := by
        rw [inner_toLp_vec3_eq_integral_dot_measure]
        simp [u', hst]
      simp only [hleft0, hright0]
      exact tendsto_const_nhds
    obtain ⟨hsC, hlC, hconvC⟩ :=
      hlocal ⟨s, hs⟩ (tsupport w') hw'c (Set.subset_univ _)
    have hwC : MemLp w' 2 (volume.restrict (tsupport w')) := hw'.restrict _
    have hc := hconvC (hwC.toLp w')
    have hzero (f : Vec3 → L2Vec3) :
        ∀ x ∉ tsupport w', ∑ i : Fin 3, f x i * w' x i = 0 := by
      intro x hx
      rw [image_eq_zero_of_notMem_tsupport hx]
      simp
    have hleft (n : ℕ) :
        inner ℝ ((hF n).toLp (fun x => WithLp.toLp 2 (F' n s x)))
            (hw'.toLp w') =
          inner ℝ ((hsC n).toLp
            (fun x => (WithLp.toLp 2 (G (σ n) (x, s)) : L2Vec3)))
            (hwC.toLp w') := by
      rw [inner_toLp_vec3_eq_integral_dot_measure,
        inner_toLp_vec3_eq_integral_dot_measure,
        setIntegral_eq_integral_of_forall_compl_eq_zero
          (hzero (fun x => (WithLp.toLp 2 (G (σ n) (x, s)) : L2Vec3)))]
      congr 1
      funext x
      simp only [F', hs, hst, and_self, ↓reduceIte, hGF (σ n) x s hs]
    have hright :
        inner ℝ (hu.toLp (fun x => WithLp.toLp 2 (u' s x))) (hw'.toLp w') =
          inner ℝ (hlC.toLp
            (fun x => (WithLp.toLp 2 (v (x, s)) : L2Vec3)))
            (hwC.toLp w') := by
      rw [inner_toLp_vec3_eq_integral_dot_measure,
        inner_toLp_vec3_eq_integral_dot_measure,
        setIntegral_eq_integral_of_forall_compl_eq_zero
          (hzero (fun x => (WithLp.toLp 2 (v (x, s)) : L2Vec3)))]
      simp only [u', hst, ↓reduceIte]
    rw [hright]
    exact hc.congr (fun n => (hleft n).symm)
  obtain ⟨hF, hu, -, -, hweak⟩ :=
    lerayLimit_globalSlices_of_localWeak F' u' K hK C hC hF'meas humeas
      hFbound hubound hlocal' t ht
  let w' : Vec3 → L2Vec3 := fun x => WithLp.toLp 2 (w x)
  have hw' : MemLp w' 2 volume :=
    hw.continuousLinearMap_comp
      (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 3 => ℝ)).symm.toContinuousLinearMap
  have hc := hweak w' hw'
  have hleft (n : ℕ) :
      inner ℝ ((hF n).toLp (fun x => WithLp.toLp 2 (F' n t x))) (hw'.toLp w') =
        ∫ x : Vec3, ∑ i : Fin 3, F (σ n) (x, t) i * w x i := by
    rw [inner_toLp_vec3_eq_integral_dot_measure]
    congr 1
    funext x
    simp only [F', ht, le_refl, and_self, ↓reduceIte, w']
  have hright :
      inner ℝ (hu.toLp (fun x => WithLp.toLp 2 (u' t x))) (hw'.toLp w') =
        ∫ x : Vec3, ∑ i : Fin 3, u (x, t) i * w x i := by
    rw [inner_toLp_vec3_eq_integral_dot_measure]
    congr 1
    funext x
    simp only [u', w', le_refl, ↓reduceIte, huv x t ht]
  rw [← hright]
  exact hc.congr hleft

/-- The forced regularized velocities have measurable positive-time slices
and, on every bounded time interval, a slice energy bound uniform in `ε`, from
`lem:forced-energy-bounds`. -/
theorem forcedLerayLimit_slice_energy_local
    (ρ : RegMollifierProfile) (a : Vec3 → Vec3) (ha : IsInJ a)
    (f : ParabolicPoint → Vec3) (hf : IsLocallySquareIntegrableForce f)
    (εseq : ℕ → ℝ) (hseq : ∀ n, 0 < εseq n) :
    (∀ n (t : ℝ), Measurable (fun x : Vec3 =>
      forcedRegVelocity ρ a ha f hf (εseq n) (x, t))) ∧
    ∀ T : ℝ, 0 < T → ∃ A : ℝ≥0∞, A < ⊤ ∧
      ∀ n (t : ℝ), 0 < t → t ≤ T →
        (∫⁻ x : Vec3, ‖WithLp.toLp 2
          (forcedRegVelocity ρ a ha f hf (εseq n) (x, t))‖ₑ ^ (2 : ℝ) ∂volume) ≤
          A ^ (2 : ℕ) := by
  constructor
  · intro n t
    have hε := hseq n
    have hm : Measurable (forcedRegVelocity ρ a ha f hf (εseq n)) := by
      rw [forcedRegVelocity_eq ρ ha hf hε]
      exact (forcedRegRep_stronglyMeasurable ρ (εseq n) hε ha hf).measurable
    exact hm.comp (measurable_prodMk_right (m := (inferInstance : MeasurableSpace Vec3)))
  intro T hT
  let E : ℝ := Real.exp T * ((∑ i : Fin 3, ∫ x : Vec3, a x i ^ 2) +
    ∑ i : Fin 3, ∫ z in spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 T), f z i ^ 2)
  refine ⟨ENNReal.ofReal (Real.sqrt (max E 0)), ENNReal.ofReal_lt_top, ?_⟩
  intro n t ht htT
  have hε := hseq n
  obtain ⟨⟨hSlice, hcont, -, -⟩, -, hR2, -, hE⟩ := forcedRegularised ρ a ha f hf (εseq n) hε
  obtain ⟨hkin, -⟩ := forcedLerayLimit_energy_bounds ρ (εseq n) hε a ha.1 f hf
    (forcedRegVelocity ρ a ha f hf (εseq n)) (forcedRegGradient ρ a ha f hf (εseq n))
    hSlice hcont (fun S hS => (forcedRegVelocity_memLp_slab ρ a ha f hf (εseq n) hε S hS).1)
    (fun S hS => (hR2 S hS).1) (fun t ht => (hE t ht).2) T hT
  have hmem := hSlice t ht.le
  have hpt : ∀ x : Vec3, ‖(WithLp.toLp 2
      (forcedRegVelocity ρ a ha f hf (εseq n) (x, t)) : L2Vec3)‖ₑ ^ (2 : ℝ) =
      ENNReal.ofReal (∑ i : Fin 3, forcedRegVelocity ρ a ha f hf (εseq n) (x, t) i ^ 2) := by
    intro x
    rw [← ofReal_norm, ← vec3EuclideanNorm_eq_l2]
    have hnn : 0 ≤ vec3EuclideanNorm (forcedRegVelocity ρ a ha f hf (εseq n) (x, t)) :=
      Real.sqrt_nonneg _
    rw [ENNReal.ofReal_rpow_of_nonneg hnn (by norm_num)]
    congr 1
    rw [vec3EuclideanNorm, show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast,
      Real.sq_sqrt (Finset.sum_nonneg fun i _ => sq_nonneg _)]
  have hint : Integrable (fun x : Vec3 =>
      ∑ i : Fin 3, forcedRegVelocity ρ a ha f hf (εseq n) (x, t) i ^ 2) :=
    integrable_finsetSum _ fun i _ => (hmem.eval i).integrable_sq
  calc (∫⁻ x : Vec3, ‖WithLp.toLp 2
        (forcedRegVelocity ρ a ha f hf (εseq n) (x, t))‖ₑ ^ (2 : ℝ) ∂volume)
      = ENNReal.ofReal (∫ x, ∑ i : Fin 3,
          forcedRegVelocity ρ a ha f hf (εseq n) (x, t) i ^ 2) := by
        simp only [hpt]
        exact (ofReal_integral_eq_lintegral_ofReal hint
          (Eventually.of_forall fun x => Finset.sum_nonneg fun i _ => sq_nonneg _)).symm
    _ ≤ ENNReal.ofReal (max E 0) := by
        refine ENNReal.ofReal_le_ofReal ?_
        rw [integral_finsetSum _ fun i _ => (hmem.eval i).integrable_sq]
        exact (hkin t ⟨ht.le, htT⟩).trans (le_max_left _ _)
    _ = ENNReal.ofReal (Real.sqrt (max E 0)) ^ (2 : ℕ) := by
        rw [← ENNReal.ofReal_pow (Real.sqrt_nonneg _),
          Real.sq_sqrt (le_max_right _ _)]

/-- The every-time slice clause of `prop:forced-limit`: along the subsequence
and limit of the forced local compactness theorem (forcedLerayLimit_local_compactness), the forced
regularized velocities converge weakly in `L²` on every positive-time slice,
tested against every global `L²` field. -/
theorem forcedLerayLimit_everyTimePairings
    (ρ : RegMollifierProfile) (a : Vec3 → Vec3) (ha : IsInJ a)
    (f : ParabolicPoint → Vec3) (hf : IsLocallySquareIntegrableForce f)
    (εseq : ℕ → ℝ) (hseq : ∀ n, 0 < εseq n ∧ εseq n ≤ 1)
    (σ : ℕ → ℕ) (v : Vec3 × ℝ → Vec3) (u : ParabolicPoint → Vec3)
    (hv : Measurable v)
    (huv : ∀ (x : Vec3) (t : ℝ), 0 < t → u (x, t) = v (x, t))
    (hlocal : ∀ t : ℝ, 0 < t → ∀ C : Set Vec3, IsCompact C →
      ∃ hs : ∀ k, MemLp
        (fun x : Vec3 => (WithLp.toLp 2
          (forcedRegVelocity ρ a ha f hf (εseq (σ k)) (x, t)) : L2Vec3))
        2 (volume.restrict C),
      ∃ hvC : MemLp
        (fun x : Vec3 => (WithLp.toLp 2 (v (x, t)) : L2Vec3))
        2 (volume.restrict C),
      ∀ w : Lp L2Vec3 2 (volume.restrict C),
        Tendsto (fun k => inner ℝ ((hs k).toLp
          (fun x => (WithLp.toLp 2
            (forcedRegVelocity ρ a ha f hf (εseq (σ k)) (x, t)) : L2Vec3))) w)
          atTop (𝓝 (inner ℝ (hvC.toLp
            (fun x => (WithLp.toLp 2 (v (x, t)) : L2Vec3))) w)))
    (hSliceBound : ∀ C : Set Vec3, IsCompact C →
      ∀ b₁ b₂ : ℝ, Icc b₁ b₂ ⊆ Ioi (0 : ℝ) →
      ∀ M : ℝ≥0∞, M < ⊤ →
        (∀ n t, t ∈ Icc b₁ b₂ →
          (∫⁻ x in C, ENNReal.ofReal
            (vec3EuclideanNorm
              (forcedRegVelocity ρ a ha f hf (εseq n) (x, t))) ^ (2 : ℝ)
            ∂volume) ≤ M) →
        ∀ t ∈ Icc b₁ b₂,
          (∫⁻ x in C, ENNReal.ofReal (vec3EuclideanNorm (v (x, t))) ^ (2 : ℝ)
            ∂volume) ≤ M) :
    ∀ t : ℝ, 0 < t → ∀ w : Vec3 → Vec3, MemLp w 2 volume →
      Tendsto (fun n => ∫ x : Vec3, ∑ i : Fin 3,
          forcedRegVelocity ρ a ha f hf (εseq (σ n)) (x, t) i * w x i) atTop
        (𝓝 (∫ x : Vec3, ∑ i : Fin 3, u (x, t) i * w x i)) := by
  obtain ⟨hmeas, henergy⟩ :=
    forcedLerayLimit_slice_energy_local ρ a ha f hf εseq (fun n => (hseq n).1)
  exact lerayLimit_everyTime_pairing_tendsto_of_local_energy
    (fun n => forcedRegVelocity ρ a ha f hf (εseq n))
    (fun n z => forcedRegVelocity ρ a ha f hf (εseq n) z) σ v u
    (fun n t _ => hmeas n t) hv (fun _ _ _ _ => rfl) huv henergy
    (fun t C hC _ => hlocal t.1 t.2 C hC)
    (fun C hC _ b₁ b₂ hI M hM hsrc => hSliceBound C hC b₁ b₂ hI M hM hsrc)

end CKN.Leray

end
