/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Leray.ForcedHopfSlab
public import LeanPool.CaffarelliKohnNirenberg.Leray.LerayHopfLimitPropEnergyIneq
public import LeanPool.CaffarelliKohnNirenberg.Leray.LerayHopfLimitPropEnergy
public import LeanPool.CaffarelliKohnNirenberg.Leray.ForcedAssemblySupport

/-!
# The forced energy inequality in the limit

These are the energy steps in the proof of `thm:leray-forced`. The energy
inequality `eq:reg-energy-forced` of each forced regularized solution is put in
real form; the work term converges by strong `L²` convergence, the kinetic
energy and the dissipation are weakly lower semicontinuous, and the limit
satisfies the forced energy inequality (FLH2). Its small-time form and weak
continuity at `0` give the strong initial trace (LH5).
-/

public section

open MeasureTheory Filter Set
open scoped ENNReal Topology
open CKN CKN.Foundation.Parabolic

noncomputable section

namespace CKN.Leray

/-- The square of the `L²` norm of a Euclidean field is the sum of its
coordinate square integrals. -/
theorem forcedHopf_norm_toLp_sq {g : Vec3 → Vec3} (hg : MemLp g 2 volume) :
    ‖(lerayHopfLimit_toLp_memLp hg).toLp (fun x => (WithLp.toLp 2 (g x) : L2Vec3))‖ ^ 2 =
      ∑ i : Fin 3, ∫ x, g x i ^ 2 := by
  rw [Lp.norm_toLp, ← ENNReal.toReal_pow, lerayHopfLimit_eLpNorm_toLp_sq hg,
    ENNReal.toReal_ofReal (Finset.sum_nonneg (fun i _ => integral_nonneg (fun x => sq_nonneg _)))]

/-- The dissipation of a field with a square-integrable weak gradient on the
slab `(0,t)` is the sum of the coordinate square integrals. -/
theorem forcedHopf_dissipation_eq_ofReal (U : ParabolicPoint → Vec3)
    (D : ParabolicPoint → Fin 3 → Vec3) (t₀ : ℝ)
    (hD : MemLp D 2 (volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 t₀)))) :
    regUniformDissipation U D t₀ =
      ENNReal.ofReal (∑ i : Fin 3, ∑ j : Fin 3,
        ∫ z in spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 t₀), D z i j ^ 2) := by
  have hint : ∀ i j, Integrable (fun z => D z i j ^ 2)
      (volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 t₀))) :=
    fun i j => ((hD.eval i).eval j).integrable_sq
  have hsum : (∑ i : Fin 3, ∑ j : Fin 3,
      ∫ z in spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 t₀), D z i j ^ 2) =
      ∫ z in spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 t₀), spatialGradientSq U D z := by
    unfold spatialGradientSq
    rw [integral_finsetSum _ (fun i _ => integrable_finsetSum _ (fun j _ => hint i j))]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [integral_finsetSum _ (fun j _ => hint i j)]
  rw [lerayHopfLimit_dissipation_eq_setLIntegral, hsum, ofReal_integral_eq_lintegral_ofReal]
  · unfold spatialGradientSq
    exact integrable_finsetSum _ (fun i _ => integrable_finsetSum _ (fun j _ => hint i j))
  · refine Filter.Eventually.of_forall (fun z => ?_)
    unfold spatialGradientSq
    exact Finset.sum_nonneg (fun _ _ => Finset.sum_nonneg (fun _ _ => sq_nonneg _))

/-- The energy inequality `eq:reg-energy-forced` of a forced regularized
solution at a positive time, in real form, with the mollified datum bounded
by the datum. -/
theorem forcedHopf_energy_real_of_regularised
    (ρ : RegMollifierProfile) (ε : ℝ) (hε : 0 < ε)
    (a : Vec3 → Vec3) (ha : MemLp a 2 volume)
    (U f : ParabolicPoint → Vec3) (D : ParabolicPoint → Fin 3 → Vec3)
    (t₀ : ℝ) (hslice : MemLp (fun x => U (x, t₀)) 2 volume)
    (hD : MemLp D 2 (volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 t₀))))
    (henergy : (eLpNorm (regUniformVelocitySlice U t₀) 2 volume ^ (2 : ℕ) +
        2 * regUniformDissipation U D t₀).toReal ≤
      (eLpNorm (regMollifyVector ρ ε hε (regUniformSpatialField a)) 2 volume ^ (2 : ℕ)).toReal +
        2 * ∫ z in spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 t₀), ∑ i : Fin 3, f z i * U z i) :
    (∑ i : Fin 3, ∫ x, U (x, t₀) i ^ 2) +
        2 * (∑ i : Fin 3, ∑ j : Fin 3,
          ∫ z in spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 t₀), D z i j ^ 2) ≤
      (∑ i : Fin 3, ∫ x, a x i ^ 2) +
        2 * ∫ z in spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 t₀), ∑ i : Fin 3, f z i * U z i := by
  set X := ∑ i : Fin 3, ∫ x, U (x, t₀) i ^ 2
  set G := ∑ i : Fin 3, ∑ j : Fin 3,
    ∫ z in spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 t₀), D z i j ^ 2
  set Aa := ∑ i : Fin 3, ∫ x, a x i ^ 2
  have hX0 : 0 ≤ X := Finset.sum_nonneg (fun i _ => integral_nonneg (fun x => sq_nonneg _))
  have hG0 : 0 ≤ G := Finset.sum_nonneg (fun i _ => Finset.sum_nonneg (fun j _ =>
    integral_nonneg (fun z => sq_nonneg _)))
  have hA : MemLp (regUniformSpatialField a) 2 volume := lerayHopfLimit_initialField_memLp a ha
  have hAeq : eLpNorm (regUniformSpatialField a) 2 volume ^ (2 : ℕ) = ENNReal.ofReal Aa := by
    rw [lerayHopfLimit_eLpNorm_spatialField ha, lerayHopfLimit_eLpNorm_toLp_sq ha]
  have hXeq : eLpNorm (regUniformVelocitySlice U t₀) 2 volume ^ (2 : ℕ) = ENNReal.ofReal X := by
    have heq : regUniformVelocitySlice U t₀ =
        regUniformSpatialField (fun x => U (x, t₀)) := rfl
    rw [heq, lerayHopfLimit_eLpNorm_spatialField hslice,
      lerayHopfLimit_eLpNorm_toLp_sq hslice]
  have hlhs : (eLpNorm (regUniformVelocitySlice U t₀) 2 volume ^ (2 : ℕ) +
      2 * regUniformDissipation U D t₀).toReal = X + 2 * G := by
    rw [hXeq, forcedHopf_dissipation_eq_ofReal U D t₀ hD]
    rw [show (2 : ℝ≥0∞) * ENNReal.ofReal G = ENNReal.ofReal (2 * G) by
      rw [ENNReal.ofReal_mul (by norm_num)]; norm_num,
      ← ENNReal.ofReal_add hX0 (by positivity), ENNReal.toReal_ofReal (by positivity)]
  have hrhs : (eLpNorm (regMollifyVector ρ ε hε (regUniformSpatialField a)) 2 volume ^
      (2 : ℕ)).toReal ≤ Aa := by
    have hle : eLpNorm (regMollifyVector ρ ε hε (regUniformSpatialField a)) 2 volume ^ (2 : ℕ) ≤
        ENNReal.ofReal Aa := by
      rw [← hAeq]
      exact pow_le_pow_left₀ bot_le (regMollifyVector_eLpNorm_two_le ρ ε hε hA) 2
    calc _ ≤ (ENNReal.ofReal Aa).toReal := ENNReal.toReal_mono ENNReal.ofReal_ne_top hle
      _ = Aa := ENNReal.toReal_ofReal (Finset.sum_nonneg (fun i _ =>
          integral_nonneg (fun x => sq_nonneg _)))
  rw [hlhs] at henergy
  linarith only [henergy, hrhs]

/-- Weak lower semicontinuity of the kinetic energy and the dissipation: if
the approximating energies are bounded by convergent real numbers, the limit
energy is bounded by their limit. -/
theorem forcedHopf_energy_limit_real
    (t₀ : ℝ) (Useq : ℕ → ParabolicPoint → Vec3) (u : ParabolicPoint → Vec3)
    (Dseq : ℕ → ParabolicPoint → Fin 3 → Vec3) (Du : ParabolicPoint → Fin 3 → Vec3)
    (R : ℕ → ℝ) (Rlim : ℝ)
    (hUn : ∀ n, MemLp (fun x => Useq n (x, t₀)) 2 volume)
    (hu : MemLp (fun x => u (x, t₀)) 2 volume)
    (hweak : Tendsto (fun n => ∫ x, ∑ i : Fin 3, Useq n (x, t₀) i * u (x, t₀) i) atTop
      (𝓝 (∫ x, ∑ i : Fin 3, u (x, t₀) i * u (x, t₀) i)))
    (hDn : ∀ n i j, MemLp (fun z => Dseq n z i j) 2
      (volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 t₀))))
    (hDu : ∀ i j, MemLp (fun z => Du z i j) 2
      (volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 t₀))))
    (hDweak : ∀ i j, Tendsto (fun n => ∫ z in spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 t₀),
        Dseq n z i j * Du z i j) atTop
      (𝓝 (∫ z in spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 t₀), Du z i j * Du z i j)))
    (hEn : ∀ n, (∑ i : Fin 3, ∫ x, Useq n (x, t₀) i ^ 2) +
        2 * (∑ i : Fin 3, ∑ j : Fin 3,
          ∫ z in spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 t₀), Dseq n z i j ^ 2) ≤ R n)
    (hR : Tendsto R atTop (𝓝 Rlim)) :
    (∑ i : Fin 3, ∫ x, u (x, t₀) i ^ 2) +
        2 * (∑ i : Fin 3, ∑ j : Fin 3,
          ∫ z in spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 t₀), Du z i j ^ 2) ≤ Rlim := by
  set μt : Measure ParabolicPoint :=
    volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 t₀)) with hμt
  have hslice : ∀ n i, Integrable (fun x => Useq n (x, t₀) i * u (x, t₀) i) ∧
      2 * (∫ x, Useq n (x, t₀) i * u (x, t₀) i) - ∫ x, u (x, t₀) i ^ 2 ≤
        ∫ x, Useq n (x, t₀) i ^ 2 :=
    fun n i => lerayHopfLimit_two_mul_integral_sub_le ((hUn n).eval i) (hu.eval i)
  have hgrad : ∀ n i j, Integrable (fun z => Dseq n z i j * Du z i j) μt ∧
      2 * (∫ z, Dseq n z i j * Du z i j ∂μt) - ∫ z, Du z i j ^ 2 ∂μt ≤
        ∫ z, Dseq n z i j ^ 2 ∂μt :=
    fun n i j => lerayHopfLimit_two_mul_integral_sub_le (hDn n i j) (hDu i j)
  let L : ℕ → ℝ := fun n =>
    (2 * (∫ x, ∑ i : Fin 3, Useq n (x, t₀) i * u (x, t₀) i) -
        ∑ i : Fin 3, ∫ x, u (x, t₀) i ^ 2) +
      2 * ∑ i : Fin 3, ∑ j : Fin 3,
        (2 * (∫ z, Dseq n z i j * Du z i j ∂μt) - ∫ z, Du z i j ^ 2 ∂μt)
  have hLle : ∀ n, L n ≤ R n := by
    intro n
    have hsplit : ∫ x, ∑ i : Fin 3, Useq n (x, t₀) i * u (x, t₀) i =
        ∑ i : Fin 3, ∫ x, Useq n (x, t₀) i * u (x, t₀) i :=
      integral_finsetSum _ (fun i _ => (hslice n i).1)
    have h1 : 2 * (∑ i : Fin 3, ∫ x, Useq n (x, t₀) i * u (x, t₀) i) -
        ∑ i : Fin 3, ∫ x, u (x, t₀) i ^ 2 ≤ ∑ i : Fin 3, ∫ x, Useq n (x, t₀) i ^ 2 := by
      rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
      exact Finset.sum_le_sum (fun i _ => (hslice n i).2)
    have h2 : (∑ i : Fin 3, ∑ j : Fin 3,
        (2 * (∫ z, Dseq n z i j * Du z i j ∂μt) - ∫ z, Du z i j ^ 2 ∂μt)) ≤
        ∑ i : Fin 3, ∑ j : Fin 3, ∫ z, Dseq n z i j ^ 2 ∂μt :=
      Finset.sum_le_sum (fun i _ => Finset.sum_le_sum (fun j _ => (hgrad n i j).2))
    have h3 := hEn n
    change (2 * (∫ x, ∑ i : Fin 3, Useq n (x, t₀) i * u (x, t₀) i) -
        ∑ i : Fin 3, ∫ x, u (x, t₀) i ^ 2) +
      2 * ∑ i : Fin 3, ∑ j : Fin 3,
        (2 * (∫ z, Dseq n z i j * Du z i j ∂μt) - ∫ z, Du z i j ^ 2 ∂μt) ≤ R n
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
  have hfinal := le_of_tendsto_of_tendsto' hLlim hR hLle
  have hsimp : ∀ i j, 2 * (∫ z, Du z i j ^ 2 ∂μt) - ∫ z, Du z i j ^ 2 ∂μt =
      ∫ z, Du z i j ^ 2 ∂μt := fun i j => by ring
  simp only [hsimp] at hfinal
  linarith only [hfinal]

/-- The real forced energy inequality gives the energy clause (FLH2) at a
positive time. -/
theorem forcedHopf_energy_ennreal
    (t₀ : ℝ) (u f : ParabolicPoint → Vec3) (Du : ParabolicPoint → Fin 3 → Vec3)
    (a : Vec3 → Vec3)
    (hu : MemLp (fun x => u (x, t₀)) 2 volume)
    (hDu : MemLp Du 2 (volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 t₀))))
    (ha : MemLp a 2 volume)
    (hreal : (∑ i : Fin 3, ∫ x, u (x, t₀) i ^ 2) +
        2 * (∑ i : Fin 3, ∑ j : Fin 3,
          ∫ z in spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 t₀), Du z i j ^ 2) ≤
      (∑ i : Fin 3, ∫ x, a x i ^ 2) +
        2 * ∫ z in spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 t₀), ∑ i : Fin 3, f z i * u z i) :
    (ENNReal.ofReal (1 / 2 : ℝ) *
          (∫⁻ x : Vec3, ENNReal.ofReal (vec3EuclideanNorm (u (x, t₀))) ^ (2 : ℝ))
        + ∫⁻ z in spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 t₀),
            ENNReal.ofReal (spatialGradientSq u Du z)) < ⊤ ∧
      ((ENNReal.ofReal (1 / 2 : ℝ) *
          (∫⁻ x : Vec3, ENNReal.ofReal (vec3EuclideanNorm (u (x, t₀))) ^ (2 : ℝ))
        + ∫⁻ z in spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 t₀),
            ENNReal.ofReal (spatialGradientSq u Du z))).toReal ≤
        ((ENNReal.ofReal (1 / 2 : ℝ) *
          (∫⁻ x : Vec3, ENNReal.ofReal (vec3EuclideanNorm (a x)) ^ (2 : ℝ)))).toReal +
          ∫ z in spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 t₀), ∑ i : Fin 3, f z i * u z i := by
  have hdiss := forcedHopf_dissipation_eq_ofReal u Du t₀ hDu
  rw [lerayHopfLimit_dissipation_eq_setLIntegral] at hdiss
  rw [lerayHopfLimit_lintegral_euclidean_sq hu, lerayHopfLimit_lintegral_euclidean_sq ha, hdiss]
  set X := ∑ i : Fin 3, ∫ x, u (x, t₀) i ^ 2
  set G := ∑ i : Fin 3, ∑ j : Fin 3,
    ∫ z in spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 t₀), Du z i j ^ 2
  set Aa := ∑ i : Fin 3, ∫ x, a x i ^ 2
  have hX0 : 0 ≤ X := Finset.sum_nonneg (fun i _ => integral_nonneg (fun x => sq_nonneg _))
  have hG0 : 0 ≤ G := Finset.sum_nonneg (fun i _ => Finset.sum_nonneg (fun j _ =>
    integral_nonneg (fun z => sq_nonneg _)))
  have hA0 : 0 ≤ Aa := Finset.sum_nonneg (fun i _ => integral_nonneg (fun x => sq_nonneg _))
  rw [← ENNReal.ofReal_mul (by norm_num), ← ENNReal.ofReal_mul (by norm_num),
    ← ENNReal.ofReal_add (by positivity) hG0]
  refine ⟨ENNReal.ofReal_lt_top, ?_⟩
  rw [ENNReal.toReal_ofReal (by positivity), ENNReal.toReal_ofReal (by positivity)]
  linarith only [hreal]

/-- The strong initial trace (LH5) from weak continuity at `0` and an energy
bound whose excess over the initial energy vanishes as `t ↓ 0`. -/
theorem forcedHopf_initialTrace
    (T : ℝ) (hT : 0 < T) (u : ParabolicPoint → Vec3) (a : Vec3 → Vec3)
    (hu0 : ∀ x, u (x, 0) = a x) (ha : MemLp a 2 volume)
    (hslice : ∀ t, 0 < t → MemLp (fun x => u (x, t)) 2 volume)
    (e : ℝ → ℝ) (he : Tendsto e (𝓝[>] 0) (𝓝 0))
    (henergy : ∀ t, 0 < t → t ≤ T →
      ∑ i : Fin 3, ∫ x, u (x, t) i ^ 2 ≤ (∑ i : Fin 3, ∫ x, a x i ^ 2) + e t)
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
  have hupper : Tendsto (fun t => ENNReal.ofReal (2 * Aa - 2 * P t + e t)) (𝓝[>] 0)
      (𝓝 0) := by
    have h := ((hPlim.const_mul 2).const_sub (2 * Aa)).add he
    have h' := ENNReal.tendsto_ofReal h
    rw [show 2 * Aa - 2 * Aa + 0 = (0 : ℝ) by ring, ENNReal.ofReal_zero] at h'
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

/-- The work pairings converge under strong `L²` convergence of the
velocities; the approximations are square integrable from some index on. -/
theorem forcedHopf_work_tendsto {μ : Measure ParabolicPoint}
    (U : ℕ → ParabolicPoint → Vec3) (u f : ParabolicPoint → Vec3)
    (hmeas : ∀ n, AEStronglyMeasurable (U n) μ)
    (hu : MemLp u 2 μ) (hf : MemLp f 2 μ)
    (hconv : Tendsto (fun n => eLpNorm (U n - u) 2 μ) atTop (𝓝 0)) :
    Tendsto (fun n => ∫ z, ∑ i : Fin 3, f z i * U n z i ∂μ) atTop
      (𝓝 (∫ z, ∑ i : Fin 3, f z i * u z i ∂μ)) := by
  obtain ⟨N, hN⟩ := eventually_atTop.mp
    ((tendsto_order.mp hconv).2 1 (zero_lt_one : (0 : ℝ≥0∞) < 1))
  have hmem : ∀ n, MemLp (U (n + N)) 2 μ := by
    intro n
    have hdiff : MemLp (U (n + N) - u) 2 μ :=
      (hN (n + N) (Nat.le_add_left N n)).trans ENNReal.one_lt_top
    have h := hdiff.add hu
    rwa [sub_add_cancel] at h
  refine (tendsto_add_atTop_iff_nat N).mp ?_
  have hsum : ∀ (V : ParabolicPoint → Vec3), MemLp V 2 μ →
      ∫ z, ∑ i : Fin 3, f z i * V z i ∂μ = ∑ i : Fin 3, ∫ z, V z i * f z i ∂μ := by
    intro V hV
    refine (integral_finsetSum (f := fun i z => f z i * V z i) Finset.univ
      (fun i _ => (hf.eval i).integrable_mul (hV.eval i))).trans ?_
    exact Finset.sum_congr rfl (fun i _ => integral_congr_ae
      (ae_of_all _ fun z => mul_comm _ _))
  simp only [hsum _ (hmem _), hsum u hu]
  refine tendsto_finsetSum _ (fun i _ => ?_)
  refine forcedAssembly_pairing_tendsto_of_strong_two μ (fun n z => U (n + N) z i)
    (fun z => u z i) (fun z => f z i) (fun n => (hmem n).eval i) (hf.eval i) ?_
  have hconvN := (tendsto_add_atTop_iff_nat N).mpr hconv
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hconvN
    (fun _ => bot_le) (fun n => eLpNorm_mono ?_ (fun z => ?_))
  · exact (continuous_apply i).comp_aestronglyMeasurable
      ((hmeas (n + N)).sub hu.aestronglyMeasurable)
  · simpa only [Pi.sub_apply] using norm_le_pi_norm ((U (n + N) - u) z) i

/-- A real sequence bounded from some index on is bounded. -/
theorem forcedHopf_exists_bound_of_eventually_le {x : ℕ → ℝ} {B : ℝ}
    (h : ∀ᶠ n in atTop, x n ≤ B) : ∃ B' : ℝ, 0 ≤ B' ∧ ∀ n, x n ≤ B' := by
  obtain ⟨N, hN⟩ := eventually_atTop.mp h
  have hS : 0 ≤ ∑ n ∈ Finset.range N, |x n| := Finset.sum_nonneg (fun n _ => abs_nonneg _)
  refine ⟨|B| + ∑ n ∈ Finset.range N, |x n|, by positivity, fun n => ?_⟩
  rcases lt_or_ge n N with hn | hn
  · have h1 : |x n| ≤ ∑ n ∈ Finset.range N, |x n| :=
      Finset.single_le_sum (f := fun n => |x n|) (fun n _ => abs_nonneg _)
        (Finset.mem_range.mpr hn)
    linarith only [le_abs_self (x n), h1, abs_nonneg B]
  · linarith only [hN n hn, le_abs_self B, hS]

end CKN.Leray

end
