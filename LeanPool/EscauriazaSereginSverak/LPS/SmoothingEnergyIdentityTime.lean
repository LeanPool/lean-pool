/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.CaffarelliKohnNirenberg.Foundation.WeakDerivMollify
public import LeanPool.CaffarelliKohnNirenberg.Foundation.WeakDerivOneDim
public import LeanPool.EscauriazaSereginSverak.PartV.SerrinCutoff
public import LeanPool.EscauriazaSereginSverak.LPS.SmoothingSliceTest
public import LeanPool.EscauriazaSereginSverak.LPS.H1EstimateTestField

/-!
# The time derivative of the kinetic energy on a whole-space slab

For a field with square-integrable space-time weak derivatives on `ℝ³ × (c, d)`,
the kinetic energy `t ↦ ∫ |v(x, t)|² dx` has the weak time derivative
`2 ∫ v · ∂ₜv dx` on `(c, d)` (`prop:lps-smoothing`). The localized time
identity for `|v|²` is tested against `χ(t) ζₙ(x)` with spatial cutoffs `ζₙ`
increasing to one, and the cutoffs are removed by dominated convergence.
-/

public section

open MeasureTheory Set Filter
open scoped Topology
open CKN CKN.Foundation.Parabolic


noncomputable section

namespace ESS

/-- A component of the zero extension of a field on a whole-space slab, in
product coordinates. -/
private theorem lps_slab_indicator_component {c d : ℝ} (F : ParabolicPoint → Vec3)
    (i : Fin 3) (q : Vec3 × ℝ) :
    ((spaceTimeSet (Set.univ : Set Vec3) (Ioo c d)).indicator F
        (parabolicHomeomorph.symm q)) i =
      ((Set.univ : Set Vec3) ×ˢ Ioo c d).indicator
        (fun y => F (parabolicHomeomorph.symm y) i) q := by
  by_cases hq : q ∈ (Set.univ : Set Vec3) ×ˢ Ioo c d
  · rw [indicator_of_mem hq, indicator_of_mem (show parabolicHomeomorph.symm q ∈
      spaceTimeSet (Set.univ : Set Vec3) (Ioo c d) from hq)]
  · rw [indicator_of_notMem hq, indicator_of_notMem (show parabolicHomeomorph.symm q ∉
      spaceTimeSet (Set.univ : Set Vec3) (Ioo c d) from hq)]
    rfl

/-- Fubini on a whole-space slab for a sum of products of zero-extended `L²`
fields against a bounded continuous time weight, time outside. -/
private theorem lps_slab_sum_indicator_integral {c d : ℝ} {f g : Fin 3 → Vec3 × ℝ → ℝ}
    (hf : ∀ i, MemLp (f i) 2 ((volume : Measure Vec3).prod (volume.restrict (Ioo c d))))
    (hg : ∀ i, MemLp (g i) 2 ((volume : Measure Vec3).prod (volume.restrict (Ioo c d))))
    {θ : ℝ → ℝ} (hθ : Continuous θ) {C : ℝ} (hC : ∀ t, ‖θ t‖ ≤ C) :
    ∑ i, ∫ q, ((Set.univ : Set Vec3) ×ˢ Ioo c d).indicator (f i) q *
        ((Set.univ : Set Vec3) ×ˢ Ioo c d).indicator (g i) q * θ q.2 =
      ∫ t in Ioo c d, (∫ x, ∑ i, f i (x, t) * g i (x, t)) * θ t := by
  set ν : Measure (Vec3 × ℝ) := (volume : Measure Vec3).prod (volume.restrict (Ioo c d))
    with hν
  set P : Set (Vec3 × ℝ) := (Set.univ : Set Vec3) ×ˢ Ioo c d with hP
  have hPm : MeasurableSet P := MeasurableSet.univ.prod measurableSet_Ioo
  have hfg (i : Fin 3) : Integrable (fun q => f i q * g i q) ν := (hf i).integrable_mul (hg i)
  have hH (i : Fin 3) : Integrable (fun q => f i q * g i q * θ q.2) ν :=
    (hfg i).mul_bdd (hθ.comp continuous_snd).aestronglyMeasurable
      (ae_of_all _ fun q => hC q.2)
  have hpt (i : Fin 3) (q : Vec3 × ℝ) :
      P.indicator (f i) q * P.indicator (g i) q * θ q.2 =
        P.indicator (fun q => f i q * g i q * θ q.2) q := by
    by_cases hq : q ∈ P
    · simp only [indicator_of_mem hq]
    · simp only [indicator_of_notMem hq, zero_mul]
  have hstep (i : Fin 3) :
      ∫ q, P.indicator (f i) q * P.indicator (g i) q * θ q.2 =
        ∫ t in Ioo c d, ∫ x, f i (x, t) * g i (x, t) * θ t := by
    simp only [hpt]
    rw [integral_indicator hPm, lps_measure_slab_eq_prod, integral_prod_symm _ (hH i)]
  simp only [hstep]
  rw [← integral_finsetSum _ fun i _ => (hH i).integral_prod_right]
  refine integral_congr_ae ?_
  have hae : ∀ᵐ t ∂(volume.restrict (Ioo c d)), ∀ i : Fin 3,
      Integrable (fun x => f i (x, t) * g i (x, t)) volume := by
    rw [ae_all_iff]
    intro i
    exact (hfg i).prod_left_ae
  filter_upwards [hae] with t ht
  rw [integral_finsetSum _ fun i _ => ht i, Finset.sum_mul]
  refine Finset.sum_congr rfl fun i _ => ?_
  exact integral_mul_const _ _

/-- The kinetic energy of a field with square-integrable space-time weak derivatives on
`ℝ³ × (c, d)` has weak time derivative `2 ∫ v · ∂ₜv dx` on `(c, d)`
(`prop:lps-smoothing`). -/
theorem lps_kineticEnergy_hasWeakDerivOn {c d : ℝ}
    {v : ParabolicPoint → Vec3} {Dv : ParabolicPoint → Fin 3 → Vec3}
    {D2v : ParabolicPoint → Fin 3 → Fin 3 → Vec3} {Dtv : ParabolicPoint → Vec3}
    (hderiv : HasSpaceTimeWeakDerivs (Set.univ : Set Vec3) (Ioo c d) v Dv D2v Dtv)
    (hv : MemLp v 2 (volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioo c d))))
    (hDtv : MemLp Dtv 2 (volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioo c d)))) :
    HasWeakDerivOn (Ioo c d) (fun t => ∫ x : Vec3, ∑ i, (v (x, t) i) ^ 2)
      (fun t => 2 * ∫ x : Vec3, ∑ i, v (x, t) i * Dtv (x, t) i) := by
  intro χ hχ
  obtain ⟨hχs, hχc, hχsupp⟩ := hχ
  set ν : Measure (Vec3 × ℝ) := (volume : Measure Vec3).prod (volume.restrict (Ioo c d))
    with hν
  set P : Set (Vec3 × ℝ) := (Set.univ : Set Vec3) ×ˢ Ioo c d with hP
  have hPm : MeasurableSet P := MeasurableSet.univ.prod measurableSet_Ioo
  have hPν : (volume : Measure (Vec3 × ℝ)).restrict P = ν := lps_measure_slab_eq_prod c d
  -- product-coordinate components and their zero extensions
  let V : Fin 3 → Vec3 × ℝ → ℝ := fun i q => v (parabolicHomeomorph.symm q) i
  let G : Fin 3 → Vec3 × ℝ → ℝ := fun i q => Dtv (parabolicHomeomorph.symm q) i
  have hV (i : Fin 3) : MemLp (V i) 2 ν := (memLp_pi_iff.1 (lps_memLp_slab_to_prod hv)) i
  have hG (i : Fin 3) : MemLp (G i) 2 ν := (memLp_pi_iff.1 (lps_memLp_slab_to_prod hDtv)) i
  have hW (i : Fin 3) : MemLp (P.indicator (V i)) 2 volume :=
    (memLp_indicator_iff_restrict hPm).2 (by rw [hPν]; exact hV i)
  have hT (i : Fin 3) : MemLp (P.indicator (G i)) 2 volume :=
    (memLp_indicator_iff_restrict hPm).2 (by rw [hPν]; exact hG i)
  -- bounds for the time weight
  have hχ'cont : Continuous (deriv χ) := hχs.continuous_deriv (by simp)
  obtain ⟨C1, hC1⟩ := hχ'cont.bounded_above_of_compact_support hχc.deriv
  obtain ⟨C0, hC0⟩ := hχs.continuous.bounded_above_of_compact_support hχc
  -- the separated tests `χ(t) ζₙ(x)` and their buffer
  obtain ⟨δ, hδ, hδsub⟩ := hχc.isCompact.exists_cthickening_subset_open isOpen_Ioo hχsupp
  let Φ : ℕ → Vec3 × ℝ → ℝ := fun n q => χ q.2 * serrinCutoff n q.1
  have hΦmem (n : ℕ) : Φ n ∈ spaceTimeTestFunction (V := ℝ) (Set.univ : Set Vec3) (Ioo c d) :=
    lps_separated_test_mem hχs hχc hχsupp (serrinCutoff_contDiff n)
      (serrinCutoff_hasCompactSupport n)
  have hbuffer (n : ℕ) : ∀ q ∈ tsupport (Φ n),
      Metric.closedBall q (4 * (δ / 4)) ⊆ (Set.univ : Set Vec3) ×ˢ Ioo c d := by
    intro q hq p hp
    have hq2 : q.2 ∈ tsupport χ := (lps_separated_tsupport_subset hq).2
    have hdist : dist p q ≤ δ := by
      rw [Metric.mem_closedBall] at hp
      linarith only [hp]
    have hdist2 : dist p.2 q.2 ≤ δ := by
      rw [Prod.dist_eq] at hdist
      exact (le_max_right _ _).trans hdist
    exact ⟨mem_univ _, hδsub (Metric.mem_cthickening_of_dist_le _ _ _ _ hq2 hdist2)⟩
  have hfd (n : ℕ) (q : Vec3 × ℝ) :
      (fderiv ℝ (Φ n) q) (0, 1) = deriv χ q.2 * serrinCutoff n q.1 := by
    have hdiff : DifferentiableAt ℝ (Φ n) q := ((hΦmem n).1.differentiable (by simp)) q
    have hγ : HasDerivAt (fun s : ℝ => ((q.1, s) : Vec3 × ℝ)) ((0 : Vec3), (1 : ℝ)) q.2 :=
      (hasDerivAt_const _ _).prodMk (hasDerivAt_id _)
    have h1 : HasDerivAt ((Φ n) ∘ fun s : ℝ => ((q.1, s) : Vec3 × ℝ))
        ((fderiv ℝ (Φ n) q) (0, 1)) q.2 :=
      (hdiff.hasFDerivAt : HasFDerivAt (Φ n) (fderiv ℝ (Φ n) q) (q.1, q.2)).comp_hasDerivAt
        q.2 hγ
    have h2 : HasDerivAt (fun s : ℝ => χ s * serrinCutoff n q.1)
        (deriv χ q.2 * serrinCutoff n q.1) q.2 :=
      ((hχs.differentiable (by simp)) q.2).hasDerivAt.mul_const (serrinCutoff n q.1)
    exact h1.unique h2
  -- the localized identity for each cutoff
  have hn (n : ℕ) : ∑ i, ∫ q, P.indicator (V i) q * P.indicator (V i) q *
        (deriv χ q.2 * serrinCutoff n q.1) =
      -(2 * ∑ i, ∫ q, P.indicator (V i) q * P.indicator (G i) q *
        (χ q.2 * serrinCutoff n q.1)) := by
    have hL2w (i : Fin 3) : MemLp (fun q : Vec3 × ℝ =>
        ((spaceTimeSet (Set.univ : Set Vec3) (Ioo c d)).indicator v
          (parabolicHomeomorph.symm q)) i) 2 (volume : Measure (Vec3 × ℝ)) := by
      simp only [lps_slab_indicator_component]
      exact hW i
    have hL2t (i : Fin 3) : MemLp (fun q : Vec3 × ℝ =>
        ((spaceTimeSet (Set.univ : Set Vec3) (Ioo c d)).indicator Dtv
          (parabolicHomeomorph.symm q)) i) 2 (volume : Measure (Vec3 × ℝ)) := by
      simp only [lps_slab_indicator_component]
      exact hT i
    have h := weak_time_derivative_sq isOpen_univ isOpen_Ioo hderiv hL2w hL2t
      (hΦmem n).1 (hΦmem n).2.1 (by positivity : 0 < δ / 4) (hbuffer n)
    simp only [lps_slab_indicator_component, hfd, sq] at h
    exact h
  -- removing the cutoffs
  have hlimL (i : Fin 3) : Tendsto (fun n : ℕ => ∫ q, P.indicator (V i) q * P.indicator (V i) q *
      (deriv χ q.2 * serrinCutoff n q.1)) atTop
      (𝓝 (∫ q, P.indicator (V i) q * P.indicator (V i) q * deriv χ q.2)) := by
    refine tendsto_integral_of_dominated_convergence
      (fun q => ‖P.indicator (V i) q * P.indicator (V i) q‖ * C1) (fun n => ?_) ?_
      (fun n => ?_) ?_
    · exact ((hW i).aestronglyMeasurable.mul (hW i).aestronglyMeasurable).mul
        ((hχ'cont.comp continuous_snd).mul
          ((serrinCutoff_contDiff n).continuous.comp continuous_fst)).aestronglyMeasurable
    · exact ((hW i).integrable_mul (hW i)).norm.mul_const C1
    · refine ae_of_all _ fun q => ?_
      rw [norm_mul]
      refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
      rw [norm_mul]
      calc ‖deriv χ q.2‖ * ‖serrinCutoff n q.1‖ ≤ C1 * 1 :=
            mul_le_mul (hC1 _) (by rw [Real.norm_eq_abs]; exact serrinCutoff_abs_le_one n q.1)
              (norm_nonneg _) ((norm_nonneg _).trans (hC1 q.2))
        _ = C1 := mul_one _
    · refine ae_of_all _ fun q => ?_
      have h := ((serrinCutoff_tendsto_one q.1).const_mul (deriv χ q.2)).const_mul
        (P.indicator (V i) q * P.indicator (V i) q)
      simpa only [mul_one] using h
  have hlimR (i : Fin 3) : Tendsto (fun n : ℕ => ∫ q, P.indicator (V i) q * P.indicator (G i) q *
      (χ q.2 * serrinCutoff n q.1)) atTop
      (𝓝 (∫ q, P.indicator (V i) q * P.indicator (G i) q * χ q.2)) := by
    refine tendsto_integral_of_dominated_convergence
      (fun q => ‖P.indicator (V i) q * P.indicator (G i) q‖ * C0) (fun n => ?_) ?_
      (fun n => ?_) ?_
    · exact ((hW i).aestronglyMeasurable.mul (hT i).aestronglyMeasurable).mul
        ((hχs.continuous.comp continuous_snd).mul
          ((serrinCutoff_contDiff n).continuous.comp continuous_fst)).aestronglyMeasurable
    · exact ((hW i).integrable_mul (hT i)).norm.mul_const C0
    · refine ae_of_all _ fun q => ?_
      rw [norm_mul]
      refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
      rw [norm_mul]
      calc ‖χ q.2‖ * ‖serrinCutoff n q.1‖ ≤ C0 * 1 :=
            mul_le_mul (hC0 _) (by rw [Real.norm_eq_abs]; exact serrinCutoff_abs_le_one n q.1)
              (norm_nonneg _) ((norm_nonneg _).trans (hC0 q.2))
        _ = C0 := mul_one _
    · refine ae_of_all _ fun q => ?_
      have h := ((serrinCutoff_tendsto_one q.1).const_mul (χ q.2)).const_mul
        (P.indicator (V i) q * P.indicator (G i) q)
      simpa only [mul_one] using h
  have hlim : ∑ i, ∫ q, P.indicator (V i) q * P.indicator (V i) q * deriv χ q.2 =
      -(2 * ∑ i, ∫ q, P.indicator (V i) q * P.indicator (G i) q * χ q.2) := by
    have hL := tendsto_finsetSum Finset.univ (fun i _ => hlimL i)
    have hR := ((tendsto_finsetSum Finset.univ (fun i _ => hlimR i)).const_mul 2).neg
    have hEq : (fun n : ℕ => ∑ i, ∫ q, P.indicator (V i) q * P.indicator (V i) q *
        (deriv χ q.2 * serrinCutoff n q.1)) =
        (fun n : ℕ => -(2 * ∑ i, ∫ q, P.indicator (V i) q * P.indicator (G i) q *
          (χ q.2 * serrinCutoff n q.1))) := funext hn
    rw [hEq] at hL
    exact tendsto_nhds_unique hL hR
  -- Fubini: back to time integrals of spatial integrals
  have hLF := lps_slab_sum_indicator_integral hV hV hχ'cont hC1
  have hRF := lps_slab_sum_indicator_integral hV hG hχs.continuous hC0
  rw [hLF, hRF] at hlim
  have hcongrL : (∫ t in Ioo c d, (∫ x : Vec3, ∑ i, (v (x, t) i) ^ 2) * deriv χ t) =
      ∫ t in Ioo c d, (∫ x, ∑ i, V i (x, t) * V i (x, t)) * deriv χ t := by
    simp only [V, parabolicHomeomorph_symm_apply, sq]
  have hcongrR : (∫ t in Ioo c d, (2 * ∫ x : Vec3, ∑ i, v (x, t) i * Dtv (x, t) i) * χ t) =
      2 * ∫ t in Ioo c d, (∫ x, ∑ i, V i (x, t) * G i (x, t)) * χ t := by
    rw [← integral_const_mul]
    simp only [V, G, parabolicHomeomorph_symm_apply, mul_assoc]
  show (∫ t in Ioo c d, (∫ x : Vec3, ∑ i, (v (x, t) i) ^ 2) * deriv χ t) =
    -(∫ t in Ioo c d, (2 * ∫ x : Vec3, ∑ i, v (x, t) i * Dtv (x, t) i) * χ t)
  rw [hcongrL, hcongrR, hlim]

end ESS
