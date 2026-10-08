/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Leray.LerayLimitSliceBridge
public import LeanPool.CaffarelliKohnNirenberg.Leray.CompactnessLocalPairing
public import LeanPool.CaffarelliKohnNirenberg.Statements.SpaceTimeSet
public import Mathlib.MeasureTheory.Integral.IntegralEqImproper

/-!
# Weak convergence of every positive-time slice

In `prop:leray-limit` the regularized velocities converge weakly in `L²` on
every positive-time slice, tested against every global `L²` field. The local
compactness step gives this on compact spatial sets; the uniform energy bound
extends it to global tests, and the Hilbert pairing is then written as the
coordinate dot-product integral.
-/

public section

open MeasureTheory Filter Set
open scoped ENNReal Topology
open CKN CKN.Foundation.Parabolic

noncomputable section

namespace CKN.Leray

/-- Every-time weak convergence in `prop:leray-limit`: the local every-time
weak convergence on compact spatial sets from the compactness step, the
transfer of compact slice bounds to the limit, and the uniform slice energy
bound give convergence of the coordinate pairings of every positive-time slice
with every global `L²` field. -/
theorem lerayLimit_everyTime_pairing_tendsto
    (F : ℕ → ParabolicPoint → Vec3) (G : ℕ → Vec3 × ℝ → Vec3) (σ : ℕ → ℕ)
    (v : Vec3 × ℝ → Vec3) (u : ParabolicPoint → Vec3)
    (hFcont : ∀ n, ∀ i : Fin 3, ContinuousOn (fun z => F n z i)
      (spaceTimeSet (Set.univ : Set Vec3) (Ioi 0)))
    (hv : Measurable v)
    (hGF : ∀ n (x : Vec3) (t : ℝ), 0 < t → G n (x, t) = F n (x, t))
    (huv : ∀ (x : Vec3) (t : ℝ), 0 < t → u (x, t) = v (x, t))
    (A : ℝ≥0∞) (hA : A < ⊤)
    (hEnergy : ∀ n (t : ℝ), 0 < t →
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
  let F' : ℕ → ℝ → Vec3 → Vec3 := fun n s x =>
    if 0 < s then F (σ n) (x, s) else 0
  let u' : ℝ → Vec3 → Vec3 := fun s x => v (x, s)
  let K : ℕ → Set Vec3 := fun k => Metric.closedBall (0 : Vec3) (k : ℝ)
  have hK : AECover (volume : Measure Vec3) atTop K :=
    aecover_closedBall tendsto_natCast_atTop_atTop
  let C : ℝ := A.toReal
  have hC : 0 ≤ C := ENNReal.toReal_nonneg
  have hCA : ENNReal.ofReal C = A := ENNReal.ofReal_toReal hA.ne
  have henorm (y : Vec3) :
      ENNReal.ofReal (vec3EuclideanNorm y) = ‖(WithLp.toLp 2 y : L2Vec3)‖ₑ := by
    rw [vec3EuclideanNorm_eq_l2, ofReal_norm]
  have hsliceCont (n : ℕ) (s : ℝ) (hs : 0 < s) :
      Continuous (fun x : Vec3 => F n (x, s)) := by
    have hmap : Continuous (fun x : Vec3 => parabolicHomeomorph.symm (x, s)) :=
      parabolicHomeomorph.symm.continuous.comp (Continuous.prodMk_left s)
    exact (continuousOn_pi.mpr (hFcont n)).comp_continuous hmap
      (fun x => ⟨Set.mem_univ _, hs⟩)
  have hFmeas : ∀ n s, Measurable (fun x : Vec3 => F' n s x) := by
    intro n s
    by_cases hs : 0 < s
    · simp only [F', hs, ↓reduceIte]
      exact (hsliceCont (σ n) s hs).measurable
    · simp only [F', hs, ↓reduceIte]
      exact measurable_const
  have humeas : ∀ s, Measurable (fun x : Vec3 => u' s x) := fun s =>
    hv.comp (measurable_prodMk_right (m := (inferInstance : MeasurableSpace Vec3)))
  have hFbound : ∀ s n k,
      (∫⁻ x in K k, ENNReal.ofReal (vec3EuclideanNorm (F' n s x)) ^ (2 : ℝ)
        ∂volume) ≤ ENNReal.ofReal C ^ (2 : ℕ) := by
    intro s n k
    rw [hCA]
    by_cases hs : 0 < s
    · simp only [F', hs, ↓reduceIte, henorm]
      exact (setLIntegral_le_lintegral _ _).trans (hEnergy (σ n) s hs)
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
    exact (setLIntegral_le_lintegral _ _).trans (hEnergy n r hs)
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
      simp only [F', hs, ↓reduceIte, hGF (σ n) x s hs]
    have hright :
        inner ℝ (hu.toLp (fun x => WithLp.toLp 2 (u' s x))) (hw'.toLp w') =
          inner ℝ (hlC.toLp
            (fun x => (WithLp.toLp 2 (v (x, s)) : L2Vec3)))
            (hwC.toLp w') := by
      rw [inner_toLp_vec3_eq_integral_dot_measure,
        inner_toLp_vec3_eq_integral_dot_measure,
        setIntegral_eq_integral_of_forall_compl_eq_zero
          (hzero (fun x => (WithLp.toLp 2 (v (x, s)) : L2Vec3)))]
    rw [hright]
    exact hc.congr (fun n => (hleft n).symm)
  obtain ⟨hF, hu, -, -, hweak⟩ :=
    lerayLimit_globalSlices_of_localWeak F' u' K hK C hC hFmeas humeas
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
    simp only [F', ht, ↓reduceIte, w']
  have hright :
      inner ℝ (hu.toLp (fun x => WithLp.toLp 2 (u' t x))) (hw'.toLp w') =
        ∫ x : Vec3, ∑ i : Fin 3, u (x, t) i * w x i := by
    rw [inner_toLp_vec3_eq_integral_dot_measure]
    congr 1
    funext x
    simp only [u', w', huv x t ht]
  rw [← hright]
  exact hc.congr hleft

end CKN.Leray

end
