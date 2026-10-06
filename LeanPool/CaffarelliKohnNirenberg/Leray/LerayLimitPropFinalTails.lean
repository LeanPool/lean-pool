/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Leray.LerayLimitTailSource
public import LeanPool.CaffarelliKohnNirenberg.Leray.LerayLimitAssemblySupport
public import LeanPool.CaffarelliKohnNirenberg.Leray.LerayLimitTailLimit
public import LeanPool.CaffarelliKohnNirenberg.Leray.CompactnessEnergyLower

/-!
# Uniform spatial tails in `prop:leray-limit`

The exterior estimate for the regularized solutions of `thm:regularised`
(the hypothesis `hregTails`, in the form of `lem:reg-tails`) bounds the
exterior slice energies `∫_{|x| > 2(m+1)} |u_ε(x,t)|²` on every finite time
interval by one sequence tending to zero. Weak lower semicontinuity on a
compact exhaustion of the exterior transfers the bound to every local weak
limit of the slices.
-/

public section

open MeasureTheory Filter Set
open scoped ENNReal Topology
open CKN CKN.Foundation.Parabolic

noncomputable section

namespace CKN.Leray

/-- The compact pieces `{R + 1/(k+1) ≤ |x|} ∩ closedBall(0,k)` exhausting the Euclidean
exterior `{R < |x|}`. -/
@[expose]
def lerayLimitFinalExteriorPiece (R : ℝ) (k : ℕ) : Set Vec3 :=
  {x : Vec3 | R + ((k : ℝ) + 1)⁻¹ ≤ vec3EuclideanNorm x} ∩
    Metric.closedBall (0 : Vec3) (k : ℝ)

private theorem lerayLimitFinalExteriorPiece_isCompact (R : ℝ) (k : ℕ) :
    IsCompact (lerayLimitFinalExteriorPiece R k) :=
  (isCompact_closedBall (0 : Vec3) (k : ℝ)).of_isClosed_subset
    ((isClosed_le continuous_const
      CKN.Foundation.Parabolic.continuous_vec3EuclideanNorm).inter Metric.isClosed_closedBall)
    inter_subset_right

private theorem lerayLimitFinalExteriorPiece_subset (R : ℝ) (k : ℕ) :
    lerayLimitFinalExteriorPiece R k ⊆ {x : Vec3 | R < vec3EuclideanNorm x} := by
  intro x hx
  have hk : 0 < ((k : ℝ) + 1)⁻¹ := by positivity
  have hRk : R < R + ((k : ℝ) + 1)⁻¹ := by linarith only [hk]
  exact lt_of_lt_of_le hRk hx.1

/-- A bound on the exterior energy `∫_{|x|>R} |F_n|²` uniform in `n` passes
to a measurable field `G` that is the weak `L²` limit of `F_n` on every
compact set. -/
theorem lerayLimit_exterior_lintegral_le_of_local_weak
    (R : ℝ) (F : ℕ → Vec3 → Vec3) (G : Vec3 → Vec3) (hGmeas : Measurable G)
    (B : ℝ≥0∞) (hB : B < ⊤)
    (hFbound : ∀ n, (∫⁻ x in {x : Vec3 | R < vec3EuclideanNorm x},
      ‖(WithLp.toLp 2 (F n x) : L2Vec3)‖ₑ ^ (2 : ℝ)) ≤ B)
    (hlocal : ∀ C : Set Vec3, IsCompact C → C ⊆ (Set.univ : Set Vec3) →
      ∃ hF : ∀ n, MemLp (fun x : Vec3 => (WithLp.toLp 2 (F n x) : L2Vec3))
        2 (volume.restrict C),
      ∃ hG : MemLp (fun x : Vec3 => (WithLp.toLp 2 (G x) : L2Vec3))
        2 (volume.restrict C),
      ∀ w : Lp L2Vec3 2 (volume.restrict C),
        Tendsto (fun n => inner ℝ
          ((hF n).toLp (fun x => (WithLp.toLp 2 (F n x) : L2Vec3))) w) atTop
          (nhds (inner ℝ (hG.toLp (fun x => (WithLp.toLp 2 (G x) : L2Vec3))) w))) :
    (∫⁻ x in {x : Vec3 | R < vec3EuclideanNorm x},
      ‖(WithLp.toLp 2 (G x) : L2Vec3)‖ₑ ^ (2 : ℝ)) ≤ B := by
  let E : Set Vec3 := {x : Vec3 | R < vec3EuclideanNorm x}
  let K : ℕ → Set Vec3 := lerayLimitFinalExteriorPiece R
  have hEmeas : MeasurableSet E :=
    measurableSet_lt measurable_const
      CKN.Foundation.Parabolic.continuous_vec3EuclideanNorm.measurable
  have hK : AECover (volume.restrict E) atTop K := by
    refine aecover_restrict_of_ae_imp hEmeas ?_ ?_
    · filter_upwards [] with x hx
      have hx' : 0 < vec3EuclideanNorm x - R := by
        have : R < vec3EuclideanNorm x := hx
        linarith only [this]
      have hinv : Tendsto (fun k : ℕ => ((k : ℝ) + 1)⁻¹) atTop (𝓝 0) := by
        simpa only [one_div] using (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
      have h1 : ∀ᶠ k : ℕ in atTop, ((k : ℝ) + 1)⁻¹ < vec3EuclideanNorm x - R :=
        hinv.eventually (gt_mem_nhds hx')
      have h2 : ∀ᶠ k : ℕ in atTop, ‖x‖ ≤ (k : ℝ) :=
        tendsto_natCast_atTop_atTop.eventually_ge_atTop _
      filter_upwards [h1, h2] with k hk1 hk2
      refine ⟨?_, ?_⟩
      · change R + ((k : ℝ) + 1)⁻¹ ≤ vec3EuclideanNorm x
        linarith only [hk1]
      · rw [Metric.mem_closedBall, dist_zero_right]
        exact hk2
    · intro k
      exact (lerayLimitFinalExteriorPiece_isCompact R k).measurableSet
  have hrestr : ∀ k, (volume.restrict E).restrict (K k) = volume.restrict (K k) :=
    fun k => Measure.restrict_restrict_of_subset (lerayLimitFinalExteriorPiece_subset R k)
  have hFK : ∀ k n, (∫⁻ x in K k, ‖(WithLp.toLp 2 (F n x) : L2Vec3)‖ₑ ^ (2 : ℝ)
      ∂(volume.restrict E)) ≤ B := by
    intro k n
    rw [hrestr k]
    exact (lintegral_mono_set (lerayLimitFinalExteriorPiece_subset R k)).trans (hFbound n)
  have htransfer : ∀ k,
      (∀ n, (∫⁻ x in K k, ‖(WithLp.toLp 2 (F n x) : L2Vec3)‖ₑ ^ (2 : ℝ)
        ∂(volume.restrict E)) ≤ B) →
      (∫⁻ x in K k, ‖(WithLp.toLp 2 (G x) : L2Vec3)‖ₑ ^ (2 : ℝ)
        ∂(volume.restrict E)) ≤ B := by
    intro k hk
    obtain ⟨hF, hG, hweak⟩ := hlocal (K k) (lerayLimitFinalExteriorPiece_isCompact R k)
      (Set.subset_univ _)
    have hsource : ∀ n, (∫⁻ x, ‖(WithLp.toLp 2 (F n x) : L2Vec3)‖ₑ ^ (2 : ℝ)
        ∂(volume.restrict (K k))) ≤ B := by
      intro n
      have h := hk n
      rw [hrestr k] at h
      exact h
    have hlim := lintegral_enorm_sq_le_of_weak_l2_bounded
      (μ := volume.restrict (K k))
      (f := fun n x => (WithLp.toLp 2 (F n x) : L2Vec3))
      (g := hG.toLp (fun x => WithLp.toLp 2 (G x)))
      (hf := hF) (hweak := hweak) (B := B) (hB := hB) (hbound := hsource)
    rw [hrestr k]
    calc (∫⁻ x, ‖(WithLp.toLp 2 (G x) : L2Vec3)‖ₑ ^ (2 : ℝ) ∂(volume.restrict (K k)))
        = ∫⁻ x, ‖hG.toLp (fun x => WithLp.toLp 2 (G x)) x‖ₑ ^ (2 : ℝ)
            ∂(volume.restrict (K k)) := by
          apply lintegral_congr_ae
          filter_upwards [hG.coeFn_toLp] with x hx
          rw [← hx]
      _ ≤ B := hlim
  have hGae : AEMeasurable (fun x : Vec3 => (WithLp.toLp 2 (G x) : L2Vec3))
      (volume.restrict E) :=
    ((PiLp.continuous_toLp 2 _).measurable.comp hGmeas).aemeasurable
  exact lerayLimit_lintegral_bound_of_compactExhaustion (μ := volume) E K hK
    (fun n x => (WithLp.toLp 2 (F n x) : L2Vec3))
    (fun x => (WithLp.toLp 2 (G x) : L2Vec3)) B hFK htransfer hGae

/-- The uniform spatial tails in `prop:leray-limit`: under the exterior
estimate `hregTails` of `lem:reg-tails`, for a sequence `G` agreeing with the
regularized velocities at positive times and a subsequence `σ` along which
`v` is the local weak limit of the positive-time slices of `G`, the exterior slice energies beyond
the radius `2(m+1)` of the regularized velocities and of `v` are bounded on
`(0,T)` by one sequence `S m → 0`. -/
theorem lerayLimit_regularised_spatialTails_with_limit
    (ρ : RegMollifierProfile)
    (uε : (a : Vec3 → Vec3) → IsInJ a → ℝ → ParabolicPoint → Vec3)
    (hregTails : ∃ C : ℝ, 0 ≤ C ∧
      ∀ (a : Vec3 → Vec3) (ha : IsInJ a) (ε : ℝ) (hε : 0 < ε)
        (_hεone : ε ≤ 1),
        (∀ R1 R2 t : ℝ, 0 < R1 → R1 < R2 → 0 ≤ t →
          (∫ x in {x : Vec3 | R2 < vec3EuclideanNorm x},
            (vec3EuclideanNorm (uε a ha ε (x, t))) ^ (2 : ℕ)) ≤
            (∫ x in {x : Vec3 | R1 < vec3EuclideanNorm x},
              (vec3EuclideanNorm
                (regUniformMollifiedInitial ρ ε hε a x)) ^ (2 : ℕ)) +
              C * (((eLpNorm a 2 volume).toReal) ^ (2 : ℕ) * t ^ (1 / 2 : ℝ) +
                ((eLpNorm a 2 volume).toReal) ^ (3 : ℕ) * t ^ (1 / 4 : ℝ)) /
                (R2 - R1)) ∧
        (∀ R1 : ℝ, 0 < R1 →
          (∫ x in {x : Vec3 | R1 < vec3EuclideanNorm x},
            (vec3EuclideanNorm (regUniformMollifiedInitial ρ ε hε a x)) ^
              (2 : ℕ)) ≤
            ∫ x in {x : Vec3 | R1 - 1 < vec3EuclideanNorm x},
              (vec3EuclideanNorm (a x)) ^ (2 : ℕ)))
    (a : Vec3 → Vec3) (ha : IsInJ a)
    (εseq : ℕ → ℝ) (hseq : ∀ n, 0 < εseq n ∧ εseq n ≤ 1)
    (hSlice : ∀ n (t : ℝ), 0 ≤ t →
      MemLp (fun x : Vec3 => uε a ha (εseq n) (x, t)) 2 volume)
    (G : ℕ → Vec3 × ℝ → Vec3)
    (hGu : ∀ n (x : Vec3) (t : ℝ), 0 < t → G n (x, t) = uε a ha (εseq n) (x, t))
    (σ : ℕ → ℕ) (v : Vec3 × ℝ → Vec3) (hv : Measurable v)
    (T : ℝ)
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
            (fun x => (WithLp.toLp 2 (v (x, t.1)) : L2Vec3))) w))) :
    ∃ S : ℕ → ℝ≥0∞, Tendsto S atTop (𝓝 0) ∧
      (∀ (m n : ℕ) (t : ℝ), t ∈ Ioo 0 T →
        (∫⁻ x in {x : Vec3 | 2 * ((m : ℝ) + 1) < vec3EuclideanNorm x},
          ‖(WithLp.toLp 2 (uε a ha (εseq (σ n)) (x, t)) : L2Vec3)‖ₑ ^ (2 : ℝ)
          ∂volume) ≤ S m) ∧
      (∀ (m : ℕ) (t : ℝ), t ∈ Ioo 0 T →
        (∫⁻ x in {x : Vec3 | 2 * ((m : ℝ) + 1) < vec3EuclideanNorm x},
          ‖(WithLp.toLp 2 (v (x, t)) : L2Vec3)‖ₑ ^ (2 : ℝ) ∂volume) ≤ S m) := by
  obtain ⟨b, hb, hbound⟩ :=
    lerayLimit_regularised_tail_tendsto ρ uε hregTails a ha εseq hseq T
  let S : ℕ → ℝ≥0∞ := fun m => ENNReal.ofReal (b m)
  have hseqS : ∀ (m n : ℕ) (t : ℝ), t ∈ Ioo 0 T →
      (∫⁻ x in {x : Vec3 | 2 * ((m : ℝ) + 1) < vec3EuclideanNorm x},
        ‖(WithLp.toLp 2 (uε a ha (εseq (σ n)) (x, t)) : L2Vec3)‖ₑ ^ (2 : ℝ)
        ∂volume) ≤ S m := by
    intro m n t ht
    have htail := hbound (σ n) m t ⟨ht.1.le, ht.2.le⟩
    exact lerayLimit_lintegral_spatial_tail_of_real_bound
      (fun x => uε a ha (εseq (σ n)) (x, t)) _ (b m)
      (hSlice (σ n) t ht.1.le) htail
  refine ⟨S, ?_, hseqS, fun m t ht => ?_⟩
  · have h := ENNReal.tendsto_ofReal hb
    simpa [S] using h
  · refine lerayLimit_exterior_lintegral_le_of_local_weak (2 * ((m : ℝ) + 1))
      (fun n x => G (σ n) (x, t)) (fun x => v (x, t))
      (hv.comp (measurable_prodMk_right (m := (inferInstance : MeasurableSpace Vec3))))
      (S m) ENNReal.ofReal_lt_top (fun n => ?_)
      (fun Cset hCset hCU => hlocal ⟨t, ht.1⟩ Cset hCset hCU)
    have hfun : (fun x : Vec3 => ‖(WithLp.toLp 2 (G (σ n) (x, t)) : L2Vec3)‖ₑ ^ (2 : ℝ)) =
        fun x => ‖(WithLp.toLp 2 (uε a ha (εseq (σ n)) (x, t)) : L2Vec3)‖ₑ ^ (2 : ℝ) := by
      funext x
      rw [hGu (σ n) x t ht.1]
    rw [hfun]
    exact hseqS m n t ht

end CKN.Leray

end
