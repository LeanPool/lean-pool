/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Leray.CompactnessRepresentativeWeak
public import LeanPool.CaffarelliKohnNirenberg.Leray.CompactnessWeakCore
public import LeanPool.CaffarelliKohnNirenberg.Leray.CompactnessLocalPairing
public import LeanPool.CaffarelliKohnNirenberg.Leray.LerayHopfLimitPropTransport

/-!
# Every positive-time slice of the Leray limit is square integrable

The limit field of `prop:leray-limit` is defined at positive times by the
iterated mollified limits of `eq:leray-limit-representative`. At a fixed
positive time, the regularized slices are bounded in `L²` and converge weakly
against every `L²` field, so this representative agrees almost everywhere
with the weak `L²` limit. In particular every positive-time slice of the
limit is square integrable, as used in the proof of `prop:leray-hopf-limit`.
-/

public section

open MeasureTheory Filter Set Metric
open scoped ENNReal Topology
open CKN CKN.Foundation.Parabolic

noncomputable section

namespace CKN.Leray

/-- The pairing of two coordinate `L²` fields through their Euclidean
representatives. -/
theorem lerayHopfLimit_inner_toLp_eq
    {f g : Vec3 → Vec3} (hf : MemLp f 2 volume) (hg : MemLp g 2 volume) :
    inner ℝ ((lerayHopfLimit_toLp_memLp hf).toLp (fun x => (WithLp.toLp 2 (f x) : L2Vec3)))
        ((lerayHopfLimit_toLp_memLp hg).toLp (fun x => (WithLp.toLp 2 (g x) : L2Vec3))) =
      ∫ x, ∑ i : Fin 3, f x i * g x i := by
  simpa using inner_toLp_vec3_eq_integral_dot_measure volume
    (fun x => (WithLp.toLp 2 (f x) : L2Vec3)) (fun x => WithLp.toLp 2 (g x))
    (lerayHopfLimit_toLp_memLp hf) (lerayHopfLimit_toLp_memLp hg)

/-- A slice of the iterated mollified limit is square integrable when the
regularized slices at that time are uniformly bounded in `L²` and converge
weakly to it against every `L²` field. -/
theorem lerayHopfLimit_slice_memLp_of_representative
    (Useq : ℕ → Vec3 × ℝ → Vec3) (σ : ℕ → ℕ) (hσ : Tendsto σ atTop atTop)
    (u : ParabolicPoint → Vec3) (t : ℝ)
    (hrep : ∀ x : Vec3, u (x, t) = compactnessMollifiedLimit Useq σ (x, t))
    (hslice : ∀ n, MemLp (fun x => Useq n (x, t)) 2 volume)
    (B : ℝ) (hB : 0 ≤ B)
    (hbound : ∀ n, ‖(lerayHopfLimit_toLp_memLp (hslice n)).toLp
      (fun x => (WithLp.toLp 2 (Useq n (x, t)) : L2Vec3))‖ ≤ B)
    (hweak : ∀ w : Vec3 → Vec3, MemLp w 2 volume →
      Tendsto (fun n => ∫ x, ∑ i : Fin 3, Useq n (x, t) i * w x i) atTop
        (𝓝 (∫ x, ∑ i : Fin 3, u (x, t) i * w x i))) :
    MemLp (fun x : Vec3 => u (x, t)) 2 volume := by
  let F : ℕ → Lp L2Vec3 2 (volume : Measure Vec3) := fun n =>
    (lerayHopfLimit_toLp_memLp (hslice n)).toLp
      (fun x => (WithLp.toLp 2 (Useq n (x, t)) : L2Vec3))
  -- pairing with an arbitrary Hilbert element
  have hpairAll : ∀ y : Lp L2Vec3 2 (volume : Measure Vec3),
      ∃ c : ℝ, Tendsto (fun n => inner ℝ (F n) y) atTop (𝓝 c) := by
    intro y
    let w : Vec3 → Vec3 := fun x => WithLp.ofLp (y x)
    have hw : MemLp w 2 volume :=
      (Lp.memLp y).continuousLinearMap_comp
        (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 3 => ℝ)).toContinuousLinearMap
    refine ⟨∫ x, ∑ i : Fin 3, u (x, t) i * w x i, ?_⟩
    have hyeq : (lerayHopfLimit_toLp_memLp hw).toLp
        (fun x => (WithLp.toLp 2 (w x) : L2Vec3)) = y := by
      refine Lp.ext ?_
      filter_upwards [(lerayHopfLimit_toLp_memLp hw).coeFn_toLp] with x hx
      rw [hx]
    have heq : ∀ n, inner ℝ (F n) y = ∫ x, ∑ i : Fin 3, Useq n (x, t) i * w x i := by
      intro n
      rw [← hyeq]
      exact lerayHopfLimit_inner_toLp_eq (hslice n) hw
    simp only [heq]
    exact hweak w hw
  obtain ⟨ψ, _, hψ, hψdense⟩ := exists_countable_dense_smooth_compact_vector_tests
  obtain ⟨v, hv⟩ := exists_weak_limit_of_tendsto_pairings_on_dense_range F B hB hbound
    (fun m => (hψ m).toLp (ψ m)) hψdense (fun m => hpairAll _)
  -- the representative agrees with the weak limit on every ball
  let I : Set ℝ := {t}
  let χ : Vec3 → ℝ := fun _ => 1
  have hmem : ∀ n (s : I), MemLp
      (fun y => χ y • (WithLp.toLp 2 (Useq n (y, s.1)) : L2Vec3)) 2 volume := by
    intro n s
    have hs : s.1 = t := s.2
    rw [hs]
    simpa only [χ, one_smul] using lerayHopfLimit_toLp_memLp (hslice n)
  have hFeq : ∀ n (s : I), (hmem n s).toLp
      (fun y => χ y • (WithLp.toLp 2 (Useq n (y, s.1)) : L2Vec3)) = F n := by
    intro n s
    have hs : s.1 = t := s.2
    refine Lp.ext ?_
    filter_upwards [(hmem n s).coeFn_toLp,
      (lerayHopfLimit_toLp_memLp (hslice n)).coeFn_toLp] with x hx hx'
    change _ = ((lerayHopfLimit_toLp_memLp (hslice n)).toLp
      (fun x => (WithLp.toLp 2 (Useq n (x, t)) : L2Vec3))) x
    rw [hx, hx', hs]
    simp only [χ, one_smul]
  have hweakV : ∀ (s : I) (y : Lp L2Vec3 2 (volume : Measure Vec3)),
      Tendsto (fun k => inner ℝ ((hmem (σ k) s).toLp
        (fun y => χ y • (WithLp.toLp 2 (Useq (σ k) (y, s.1)) : L2Vec3))) y) atTop
        (𝓝 (inner ℝ v y)) := by
    intro s y
    simp only [hFeq]
    exact (hv y).comp hσ
  have hball : ∀ R : ℕ, ∀ᵐ x ∂(volume.restrict (closedBall (0 : Vec3) R)),
      u (x, t) = WithLp.ofLp (v x) := by
    intro R
    have h := compactnessMollifiedLimit_ae_eq_weak_slice (I := I)
      (isCompact_closedBall (0 : Vec3) R) isOpen_univ (subset_univ _) Useq σ χ
      (fun _ _ => rfl) hmem (fun _ => v) hweakV ⟨t, rfl⟩
    filter_upwards [h] with x hx
    rw [hrep x]
    exact hx
  have hall : ∀ᵐ x ∂(volume : Measure Vec3), u (x, t) = WithLp.ofLp (v x) := by
    have h := (ae_restrict_iUnion_iff (fun R : ℕ => closedBall (0 : Vec3) R)
      (fun x => u (x, t) = WithLp.ofLp (v x))).mpr hball
    rwa [iUnion_closedBall_nat, Measure.restrict_univ] at h
  have hvmem : MemLp (fun x => WithLp.ofLp (v x)) 2 volume :=
    (Lp.memLp v).continuousLinearMap_comp
      (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 3 => ℝ)).toContinuousLinearMap
  exact hvmem.ae_eq (hall.mono (fun x hx => hx.symm))

end CKN.Leray

end
