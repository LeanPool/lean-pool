/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.EscauriazaSereginSverak.PartV.StokesPressure
public import LeanPool.EscauriazaSereginSverak.PartV.LocalSolutionContraction
public import LeanPool.EscauriazaSereginSverak.PartV.LocalSolutionIteration
public import LeanPool.EscauriazaSereginSverak.PartV.LocalSolutionBundleForce

/-!
# The pressure and the heat forcing of the zero-data Stokes problem

For a tensor `F ∈ L^{5/2}(Q_τ) ∩ L²(Q_τ)`, `lem:pv-stokes` takes the pressure
`q = -P[F]`, with `P` the canonical double Riesz transform of
`def:riesz-pressure` applied to `F` extended by zero. The Stokes system
`∂ₜz - Δz = div F - ∇q` (with `(div F)_j = ∑_i ∂_i F_ij`) is the componentwise
heat system `∂ₜz_i - Δz_i = ∑_j ∂_j G_ij` for `G = Fᵀ - q I` on `Q_τ`. This file
records the integrability and bounds of `q` and `G` and the double-divergence
identity `∑_ij ∂_i ∂_j G_ij = 0`, which is `Δq = div div F`.
-/

public section

open MeasureTheory Set Filter
open scoped ENNReal Topology
open CKN CKN.Foundation.Heat CKN.Foundation.Parabolic


noncomputable section

namespace ESS

open scoped Classical in
/-- The pressure `q = -P[F]` of `lem:pv-stokes` on the slab `Q_τ`, where `F` is
extended by zero outside `Q_τ` and `P` is the canonical double Riesz transform at
exponent two; it is cut off to the slab. -/
@[expose] def pvStokesPressureSlab (τ : ℝ) (F : Fin 3 → Fin 3 → ParabolicPoint → ℝ) :
    ParabolicPoint → ℝ :=
  (spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 τ)).indicator fun z =>
    if h : ∀ i j, MemLp ((spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 τ)).indicator (F i j))
        (ENNReal.ofReal 2) volume then
      pvStokesPressure 2 (by norm_num)
        (fun i j => (spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 τ)).indicator (F i j)) h z
    else 0

/-- The heat forcing `G = Fᵀ - q I` of the Stokes system of `lem:pv-stokes`, cut off
to the slab: `∂ₜz_i - Δz_i = ∑_j ∂_j G_ij` is `∂ₜz - Δz = div F - ∇q`. -/
@[expose] def pvStokesForce (τ : ℝ) (F : Fin 3 → Fin 3 → ParabolicPoint → ℝ) :
    Fin 3 → Fin 3 → ParabolicPoint → ℝ :=
  fun i j => (spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 τ)).indicator
    fun z => F j i z - if i = j then pvStokesPressureSlab τ F z else 0

section

variable {τ : ℝ} {F : Fin 3 → Fin 3 → ParabolicPoint → ℝ}

theorem pvStokes_slab_measurableSet (τ : ℝ) :
    MeasurableSet (spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 τ)) :=
  MeasurableSet.univ.prod measurableSet_Ioo

/-- The zero extension of a slab tensor. -/
theorem pvStokes_ext_memLp {r : ℝ≥0∞}
    (hF : ∀ i j, MemLp (F i j) r (volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 τ))))
    (i j : Fin 3) :
    MemLp ((spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 τ)).indicator (F i j)) r volume :=
  (memLp_indicator_iff_restrict (pvStokes_slab_measurableSet τ)).2 (hF i j)

theorem pvStokesPressureSlab_eq_zero {z : ParabolicPoint}
    (hz : z ∉ spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 τ)) : pvStokesPressureSlab τ F z = 0 :=
  indicator_of_notMem hz _

theorem pvStokesForce_eq_zero {z : ParabolicPoint}
    (hz : z ∉ spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 τ)) (i j : Fin 3) :
    pvStokesForce τ F i j z = 0 :=
  indicator_of_notMem hz _

/-- On the slab, the pressure is minus the canonical Riesz pressure of the zero
extension, at any exponent `r > 1` at which the extension is integrable. -/
theorem pvStokesPressureSlab_ae_eq {r : ℝ} (hr : 1 < r)
    (h2 : ∀ i j, MemLp ((spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 τ)).indicator (F i j))
      (ENNReal.ofReal 2) volume)
    (hr' : ∀ i j, MemLp ((spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 τ)).indicator (F i j))
      (ENNReal.ofReal r) volume) :
    pvStokesPressureSlab τ F =ᵐ[volume]
      (spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 τ)).indicator
        (-CKN.Leray.rieszPressureSpaceTime r hr
          (fun i j => (spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 τ)).indicator (F i j)) hr') := by
  have hdef : pvStokesPressureSlab τ F = (spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 τ)).indicator
      (-CKN.Leray.rieszPressureSpaceTime 2 (by norm_num)
        (fun i j => (spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 τ)).indicator (F i j)) h2) := by
    unfold pvStokesPressureSlab
    congr 1
    funext z
    split_ifs with h
    · rfl
    · exact absurd h2 h
  rw [hdef]
  have h := CKN.Leray.rieszPressureSpaceTime_ae_eq_of_memLp_common 2 (by norm_num) r hr
    (fun i j => (spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 τ)).indicator (F i j)) h2 hr'
  filter_upwards [h] with z hz
  unfold Set.indicator
  split_ifs
  · exact congrArg Neg.neg hz
  · rfl

/-- The pressure lies in `L^r` with the Riesz bound, for `r > 1` at which the
extension is integrable. -/
theorem pvStokesPressureSlab_memLp {r : ℝ} (hr : 1 < r)
    (h2 : ∀ i j, MemLp ((spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 τ)).indicator (F i j))
      (ENNReal.ofReal 2) volume)
    (hr' : ∀ i j, MemLp ((spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 τ)).indicator (F i j))
      (ENNReal.ofReal r) volume) :
    MemLp (pvStokesPressureSlab τ F) (ENNReal.ofReal r) volume ∧
      eLpNorm (pvStokesPressureSlab τ F) (ENNReal.ofReal r) volume ≤
        ENNReal.ofReal (CKN.Leray.rieszPressureOperatorBound r hr) *
          ∑ i : Fin 3, ∑ j : Fin 3,
            eLpNorm ((spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 τ)).indicator (F i j))
              (ENNReal.ofReal r) volume := by
  set Q := spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 τ)
  set Ft : Fin 3 → Fin 3 → ParabolicPoint → ℝ := fun i j => Q.indicator (F i j)
  set R := CKN.Leray.rieszPressureSpaceTime r hr Ft hr'
  have hae := pvStokesPressureSlab_ae_eq hr h2 hr'
  have hR := CKN.Leray.rieszPressureSpaceTime_memLp r hr Ft hr'
  refine ⟨(memLp_congr_ae hae).2 (hR.neg.indicator (pvStokes_slab_measurableSet τ)), ?_⟩
  have h0 : CKN.Leray.rieszPressureSpaceTime r hr (fun _ _ => (0 : Vec3 × ℝ → ℝ))
      (fun _ _ => MemLp.zero) =ᵐ[volume] 0 :=
    rieszPressureSpaceTime_ae_zero r hr _ _ fun _ _ => EventuallyEq.rfl
  have hsub := rieszPressureSpaceTime_sub_eLpNorm_le r hr Ft (fun _ _ => 0) hr'
    (fun _ _ => MemLp.zero)
  have hRR : R =ᵐ[volume] R - CKN.Leray.rieszPressureSpaceTime r hr
      (fun _ _ => (0 : Vec3 × ℝ → ℝ)) (fun _ _ => MemLp.zero) := by
    filter_upwards [h0] with z hz
    rw [Pi.sub_apply, hz, Pi.zero_apply, sub_zero]
  calc
    eLpNorm (pvStokesPressureSlab τ F) (ENNReal.ofReal r) volume =
        eLpNorm (Q.indicator (-R)) (ENNReal.ofReal r) volume := eLpNorm_congr_ae hae
    _ ≤ eLpNorm (-R) (ENNReal.ofReal r) volume :=
        eLpNorm_indicator_le _ (pvStokes_slab_measurableSet τ)
    _ = eLpNorm R (ENNReal.ofReal r) volume := eLpNorm_neg _ _ _
    _ = eLpNorm (R - CKN.Leray.rieszPressureSpaceTime r hr
          (fun _ _ => (0 : Vec3 × ℝ → ℝ)) (fun _ _ => MemLp.zero)) (ENNReal.ofReal r) volume :=
        eLpNorm_congr_ae hRR
    _ ≤ _ := hsub
    _ = ENNReal.ofReal (CKN.Leray.rieszPressureOperatorBound r hr) *
          ∑ i : Fin 3, ∑ j : Fin 3, eLpNorm (Ft i j) (ENNReal.ofReal r) volume := by
        congr 1
        refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
        exact congrArg (fun f => eLpNorm f (ENNReal.ofReal r) volume) (sub_zero (Ft i j))

/-- A tensor entry is bounded by the tensor norm. -/
theorem pvStokes_entry_eLpNorm_le {μ : Measure ParabolicPoint} {r : ℝ≥0∞}
    {H : Fin 3 → Fin 3 → ParabolicPoint → ℝ} (i j : Fin 3) :
    eLpNorm (H i j) r μ ≤ eLpNorm (fun z => fun k l => H k l z) r μ := by
  by_cases hm : AEStronglyMeasurable (fun z => fun k l => H k l z) μ
  · have hij : AEStronglyMeasurable (H i j) μ :=
      (continuous_apply j).comp_aestronglyMeasurable
        ((continuous_apply i).comp_aestronglyMeasurable hm)
    refine eLpNorm_mono hij fun z => ?_
    exact (norm_le_pi_norm (fun l => H i l z) j).trans (norm_le_pi_norm (fun k l => H k l z) i)
  · rw [eLpNorm_of_not_aestronglyMeasurable hm]
    exact le_top

/-- The sum of the entries' norms of the zero extension is at most nine times the
tensor norm on the slab. -/
theorem pvStokes_ext_sum_le {r : ℝ≥0∞} :
    ∑ i : Fin 3, ∑ j : Fin 3,
        eLpNorm ((spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 τ)).indicator (F i j)) r volume ≤
      9 * eLpNorm (fun z => fun i j => F i j z) r
        (volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 τ))) := by
  have h (i j : Fin 3) :
      eLpNorm ((spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 τ)).indicator (F i j)) r volume ≤
        eLpNorm (fun z => fun i j => F i j z) r
          (volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 τ))) := by
    rw [eLpNorm_indicator_eq_eLpNorm_restrict (pvStokes_slab_measurableSet τ)]
    exact pvStokes_entry_eLpNorm_le i j
  calc
    ∑ i : Fin 3, ∑ j : Fin 3,
        eLpNorm ((spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 τ)).indicator (F i j)) r volume ≤
        ∑ _i : Fin 3, ∑ _j : Fin 3, eLpNorm (fun z => fun i j => F i j z) r
          (volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 τ))) :=
      Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => h i j
    _ = 9 * eLpNorm (fun z => fun i j => F i j z) r
          (volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 τ))) := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      norm_num
      ring

theorem pvStokesForce_of_mem {z : ParabolicPoint}
    (hz : z ∈ spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 τ)) (i j : Fin 3) :
    pvStokesForce τ F i j z = F j i z - if i = j then pvStokesPressureSlab τ F z else 0 :=
  indicator_of_mem hz _

/-- The forcing lies in `L^r` when the slab tensor lies in `L² ∩ L^r`. -/
theorem pvStokesForce_memLp {r : ℝ} (hr : 1 < r)
    (h2 : ∀ i j, MemLp (F i j) (ENNReal.ofReal 2)
      (volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 τ))))
    (hr' : ∀ i j, MemLp (F i j) (ENNReal.ofReal r)
      (volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 τ))))
    (i j : Fin 3) : MemLp (pvStokesForce τ F i j) (ENNReal.ofReal r) volume := by
  have hq := (pvStokesPressureSlab_memLp hr (pvStokes_ext_memLp h2) (pvStokes_ext_memLp hr')).1
  have heq : pvStokesForce τ F i j =
      (spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 τ)).indicator (F j i) -
        if i = j then pvStokesPressureSlab τ F else 0 := by
    funext z
    unfold pvStokesForce
    by_cases hz : z ∈ spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 τ)
    · rw [indicator_of_mem hz, Pi.sub_apply, indicator_of_mem hz]
      split_ifs <;> rfl
    · rw [indicator_of_notMem hz, Pi.sub_apply, indicator_of_notMem hz]
      split_ifs
      · rw [pvStokesPressureSlab_eq_zero hz, sub_zero]
      · simp
  rw [heq]
  refine (pvStokes_ext_memLp hr' j i).sub ?_
  split_ifs
  · exact hq
  · exact MemLp.zero

/-- The forcing's tensor norm on the slab is bounded by the tensor norm of `F`
plus the norm of the pressure. -/
theorem pvStokesForce_eLpNorm_le {r : ℝ} (hr : 1 < r)
    (h2 : ∀ i j, MemLp (F i j) (ENNReal.ofReal 2)
      (volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 τ))))
    (hr' : ∀ i j, MemLp (F i j) (ENNReal.ofReal r)
      (volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 τ)))) :
    eLpNorm (fun z => fun i j => pvStokesForce τ F i j z) (ENNReal.ofReal r)
        (volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 τ))) ≤
      (1 + 9 * ENNReal.ofReal (CKN.Leray.rieszPressureOperatorBound r hr)) *
        eLpNorm (fun z => fun i j => F i j z) (ENNReal.ofReal r)
          (volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 τ))) := by
  set Q := spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 τ)
  set μQ : Measure ParabolicPoint := volume.restrict Q
  set q := pvStokesPressureSlab τ F
  set K := ENNReal.ofReal (CKN.Leray.rieszPressureOperatorBound r hr)
  have hr1 : (1 : ℝ≥0∞) ≤ ENNReal.ofReal r := one_le_ofReal_of_one_le hr.le
  obtain ⟨hq, hqb⟩ := pvStokesPressureSlab_memLp hr (pvStokes_ext_memLp h2) (pvStokes_ext_memLp hr')
  have hFm : AEStronglyMeasurable (fun z => fun i j => F i j z) μQ :=
    (memLp_pi_iff.2 fun i => memLp_pi_iff.2 fun j => hr' i j).aestronglyMeasurable
  have hGm : AEStronglyMeasurable (fun z => fun i j => pvStokesForce τ F i j z) μQ :=
    (memLp_pi_iff.2 fun i => memLp_pi_iff.2 fun j =>
      (pvStokesForce_memLp hr h2 hr' i j).restrict Q).aestronglyMeasurable
  have hpt : ∀ᵐ z ∂μQ, ‖fun i j => pvStokesForce τ F i j z‖ ≤
      ‖‖(fun i j => F i j z)‖ + ‖q z‖‖ := by
    filter_upwards [ae_restrict_mem (pvStokes_slab_measurableSet τ)] with z hz
    rw [Real.norm_of_nonneg (by positivity)]
    refine (pi_norm_le_iff_of_nonneg (by positivity)).2 fun i => ?_
    refine (pi_norm_le_iff_of_nonneg (by positivity)).2 fun j => ?_
    rw [pvStokesForce_of_mem hz]
    refine (norm_sub_le _ _).trans (add_le_add ?_ ?_)
    · exact (norm_le_pi_norm (fun l => F j l z) i).trans (norm_le_pi_norm (fun k l => F k l z) j)
    · split_ifs
      · exact le_rfl
      · simp
  calc
    eLpNorm (fun z => fun i j => pvStokesForce τ F i j z) (ENNReal.ofReal r) μQ ≤
        eLpNorm (fun z => ‖(fun i j => F i j z)‖ + ‖q z‖) (ENNReal.ofReal r) μQ :=
      eLpNorm_mono_ae hGm hpt
    _ ≤ eLpNorm (fun z => ‖(fun i j => F i j z)‖) (ENNReal.ofReal r) μQ +
        eLpNorm (fun z => ‖q z‖) (ENNReal.ofReal r) μQ := eLpNorm_add_le hr1
    _ = eLpNorm (fun z => fun i j => F i j z) (ENNReal.ofReal r) μQ +
        eLpNorm q (ENNReal.ofReal r) μQ := by
      rw [eLpNorm_norm _ hFm, eLpNorm_norm _ hq.aestronglyMeasurable.restrict]
    _ ≤ eLpNorm (fun z => fun i j => F i j z) (ENNReal.ofReal r) μQ +
        K * (9 * eLpNorm (fun z => fun i j => F i j z) (ENNReal.ofReal r) μQ) := by
      gcongr
      exact (eLpNorm_restrict_le _ _ _ _).trans (hqb.trans (by gcongr; exact pvStokes_ext_sum_le))
    _ = (1 + 9 * K) * eLpNorm (fun z => fun i j => F i j z) (ENNReal.ofReal r) μQ := by ring

/-- The forcing is double-divergence free on almost every time slice:
`∑_ij ∂_i ∂_j G_ij = ∂_i ∂_j F_ij - Δq = 0`, the divergence of the Stokes system. -/
theorem pvStokesForce_doubleDiv
    (h2 : ∀ i j, MemLp (F i j) (ENNReal.ofReal 2)
      (volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 τ)))) :
    ∀ᵐ s ∂(volume : Measure ℝ), ∀ φ : Vec3 → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ →
      HasCompactSupport φ →
      ∑ i : Fin 3, ∑ j : Fin 3, ∫ y : Vec3, pvStokesForce τ F i j (y, s) *
        CKN.mixedSecond φ i j y = 0 := by
  set Q := spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 τ)
  set Ft : Fin 3 → Fin 3 → ParabolicPoint → ℝ := fun i j => Q.indicator (F i j)
  have hFt := pvStokes_ext_memLp h2
  set R := CKN.Leray.rieszPressureSpaceTime 2 (by norm_num) Ft hFt
  set q := pvStokesPressureSlab τ F
  have e2 : ENNReal.ofReal 2 = 2 := by simp
  have hFt2 (i j : Fin 3) : MemLp (Ft i j) 2 volume := by
    rw [← e2]
    exact hFt i j
  have hq2 : MemLp q 2 volume := by
    rw [← e2]
    exact (pvStokesPressureSlab_memLp (by norm_num : (1 : ℝ) < 2) hFt hFt).1
  have hqR : q = Q.indicator (-R) := by
    unfold q pvStokesPressureSlab
    congr 1
    funext z
    split_ifs with h
    · rfl
    · exact absurd hFt h
  have hFs := tensor_slice_memLp_two_ae (τ := τ) hFt2 fun i j z hz => indicator_of_notMem hz _
  have hqs := tensor_slice_memLp_two_ae (τ := τ) (G := fun _ _ => q) (fun _ _ => hq2)
    fun _ _ z hz => pvStokesPressureSlab_eq_zero hz
  have hR := CKN.Leray.rieszPressureSpaceTime_slice_laplacian_identity 2 (by norm_num) Ft hFt
  filter_upwards [hFs, hqs, hR] with s hFs hqs hR
  intro φ hφ hφc
  have hm := mixedSecond_continuous_hasCompactSupport hφ hφc
  by_cases hs : s ∈ Ioo 0 τ
  · have hmem (y : Vec3) : (y, s) ∈ Q := ⟨mem_univ y, hs⟩
    have hqRs (y : Vec3) : q (y, s) = -R (y, s) := by
      rw [hqR]
      exact indicator_of_mem (hmem y) _
    have hFi (i j k l : Fin 3) : Integrable (fun y => Ft i j (y, s) * CKN.mixedSecond φ k l y) :=
      integrable_mul_of_memLp_two_of_hasCompactSupport (hFs i j) (hm k l).1 (hm k l).2
    have hqi (i j : Fin 3) : Integrable (fun y => q (y, s) * CKN.mixedSecond φ i j y) :=
      integrable_mul_of_memLp_two_of_hasCompactSupport (hqs i j) (hm i j).1 (hm i j).2
    have hGij (i j : Fin 3) : ∫ y : Vec3, pvStokesForce τ F i j (y, s) * CKN.mixedSecond φ i j y =
        (∫ y, Ft j i (y, s) * CKN.mixedSecond φ i j y) -
          if i = j then ∫ y, q (y, s) * CKN.mixedSecond φ i j y else 0 := by
      have hpt : (fun y : Vec3 => pvStokesForce τ F i j (y, s) * CKN.mixedSecond φ i j y) =
          fun y => Ft j i (y, s) * CKN.mixedSecond φ i j y -
            (if i = j then q (y, s) * CKN.mixedSecond φ i j y else 0) := by
        funext y
        rw [pvStokesForce_of_mem (hmem y)]
        have hF' : Ft j i (y, s) = F j i (y, s) := indicator_of_mem (hmem y) _
        rw [hF']
        split_ifs <;> ring
      rw [hpt]
      split_ifs
      · exact integral_sub (hFi j i i j) (hqi i j)
      · simp only [sub_zero]
    have hswap (i j : Fin 3) : ∫ y, Ft j i (y, s) * CKN.mixedSecond φ i j y =
        ∫ y, Ft j i (y, s) * CKN.mixedSecond φ j i y := by
      congr 1
      funext y
      rw [mixedSecond_swap hφ i j y]
    have hL : ∫ x, R (x, s) * (-CKN.spatialLaplacian φ x) =
        ∑ i : Fin 3, ∫ x, q (x, s) * CKN.mixedSecond φ i i x := by
      rw [← integral_finsetSum _ fun i _ => hqi i i]
      congr 1
      funext x
      change R (x, s) * -(∑ i : Fin 3, CKN.mixedSecond φ i i x) = _
      rw [mul_neg, Finset.mul_sum, ← Finset.sum_neg_distrib]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [hqRs x]
      ring
    have hrow (i : Fin 3) : ∑ j : Fin 3, ∫ y : Vec3, pvStokesForce τ F i j (y, s) *
        CKN.mixedSecond φ i j y = (∑ j : Fin 3, ∫ y, Ft j i (y, s) * CKN.mixedSecond φ j i y) -
          ∫ y, q (y, s) * CKN.mixedSecond φ i i y := by
      have h1 : ∑ j : Fin 3, ∫ y : Vec3, pvStokesForce τ F i j (y, s) *
          CKN.mixedSecond φ i j y = (∑ j : Fin 3, ∫ y, Ft j i (y, s) * CKN.mixedSecond φ j i y) -
            ∑ j : Fin 3, (if i = j then ∫ y, q (y, s) * CKN.mixedSecond φ i j y else 0) := by
        rw [← Finset.sum_sub_distrib]
        exact Finset.sum_congr rfl fun j _ => by rw [hGij, hswap]
      rw [h1, Finset.sum_ite_eq]
      simp only [Finset.mem_univ, ite_true]
    rw [Finset.sum_congr rfl fun i _ => hrow i, Finset.sum_sub_distrib, ← hL, hR φ hφ hφc,
      Finset.sum_comm]
    ring
  · have hzero (i j : Fin 3) (y : Vec3) : pvStokesForce τ F i j (y, s) = 0 :=
      pvStokesForce_eq_zero (fun hmem => hs hmem.2) i j
    simp [hzero]

end

end ESS

end
