/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Leray.ForcedLerayLimitPropStrong
public import LeanPool.CaffarelliKohnNirenberg.Leray.ForcedLerayLimitPropGradientConcrete
public import LeanPool.CaffarelliKohnNirenberg.Leray.ForcedLerayLimitPropCompactness

/-!
# The compactness statement `prop:forced-limit`

For the forced regularized solutions of `lem:regularised-forced`, every
sequence `ε_n → 0` in `(0,1]` has a subsequence along which the velocities
converge to a limit `u` with weak gradient `Du` in all the senses used by the
proof of `thm:leray-forced`. The subsequence, the limit fields and their local
convergence come from the compactness step
`CKN.Leray.forcedLerayLimit_local_compactness`; the whole-slab statements come
from the uniform spatial tails of `lem:forced-tails`, which enter as the
hypothesis `htails`. The limit velocity is the compactness limit at positive
times and the datum at time zero; its value at every positive time is the
iterated limit of spatial mollifications along the subsequence.
-/

public section

open MeasureTheory Filter Set
open scoped ENNReal Topology
open CKN CKN.Foundation.Parabolic

noncomputable section

namespace CKN.Leray

/-- The iterated mollified limit along `σ` of a subsequence `F ∘ σ` agrees
with the one of `F` at a point where the mollifications of `F ∘ σ` converge at
every scale. -/
theorem compactnessMollifiedLimit_comp_eq_of_tendsto
    (F : ℕ → Vec3 × ℝ → Vec3) (σ : ℕ → ℕ) (hσ : Tendsto σ atTop atTop)
    (z : Vec3 × ℝ)
    (hconv : ∀ (i : Fin 3) (m : ℕ), ∃ L : ℝ, Tendsto (fun k =>
      CKN.mollify (fun y : Vec3 => F (σ k) (y, z.2) i)
        (CKN.sliceRadius m) (CKN.sliceRadius_pos m) z.1) atTop (𝓝 L)) :
    compactnessMollifiedLimit (fun n => F (σ n)) σ z =
      compactnessMollifiedLimit F σ z := by
  funext i
  unfold compactnessMollifiedLimit
  congr 1
  funext m
  obtain ⟨L, hL⟩ := hconv i m
  exact (hL.comp hσ).limUnder_eq.trans hL.limUnder_eq.symm

/-- `prop:forced-limit` for the forced regularized solutions with the
mollifier profile `ρ`, given the uniform spatial tails of `lem:forced-tails`
along the subsequence of the compactness step (`htails`). -/
theorem forcedLerayLimit_of_spatialTails
    (ρ : RegMollifierProfile)
    (htails : ∀ (a : Vec3 → Vec3) (ha : IsInJ a)
      (f : ParabolicPoint → Vec3) (hf : IsLocallySquareIntegrableForce f)
      (εseq : ℕ → ℝ) (hseq : ∀ n, 0 < εseq n ∧ εseq n ≤ 1)
      (σ : ℕ → ℕ)
      (v : Vec3 × ℝ → Vec3) (hv : Measurable v)
      (T : ℝ) (hT : 0 < T)
      (hlocal : ∀ t : ℝ, 0 < t → ∀ C : Set Vec3, IsCompact C →
        ∃ hs : ∀ k, MemLp
          (fun x : Vec3 => (WithLp.toLp 2
            (forcedRegVelocity ρ a ha f hf (εseq (σ k)) (x,t)) : L2Vec3))
          2 (volume.restrict C),
        ∃ hvC : MemLp (fun x : Vec3 => (WithLp.toLp 2 (v (x,t)) : L2Vec3))
          2 (volume.restrict C),
        ∀ w : Lp L2Vec3 2 (volume.restrict C),
          Tendsto (fun k => inner ℝ ((hs k).toLp
            (fun x => (WithLp.toLp 2
              (forcedRegVelocity ρ a ha f hf (εseq (σ k)) (x,t)) : L2Vec3))) w)
            atTop (nhds (inner ℝ (hvC.toLp
              (fun x => (WithLp.toLp 2 (v (x,t)) : L2Vec3))) w))),
      ∃ S : ℕ → ℝ≥0∞, Tendsto S atTop (𝓝 0) ∧
        (∀ (m n : ℕ) (t : ℝ), t ∈ Ioo 0 T →
          (∫⁻ x in {x : Vec3 | 2 * ((m : ℝ) + 1) < vec3EuclideanNorm x},
            ‖(WithLp.toLp 2
              (forcedRegVelocity ρ a ha f hf (εseq (σ n)) (x,t)) : L2Vec3)‖ₑ ^ (2 : ℝ)
            ∂volume) ≤ S m) ∧
        (∀ (m : ℕ) (t : ℝ), t ∈ Ioo 0 T →
          (∫⁻ x in {x : Vec3 | 2 * ((m : ℝ) + 1) < vec3EuclideanNorm x},
            ‖(WithLp.toLp 2 (v (x,t)) : L2Vec3)‖ₑ ^ (2 : ℝ) ∂volume) ≤ S m)) :
    ∀ (a : Vec3 → Vec3) (ha : IsInJ a)
    (f : ParabolicPoint → Vec3) (hf : IsLocallySquareIntegrableForce f)
    (εseq : ℕ → ℝ) (hseq : ∀ n, 0 < εseq n ∧ εseq n ≤ 1)
    (_hεseq : Tendsto εseq atTop (nhds 0)),
    ∃ σ : ℕ → ℕ, ∃ u : ParabolicPoint → Vec3,
      ∃ Du : ParabolicPoint → Fin 3 → Vec3,
      StrictMono σ ∧ Tendsto σ atTop atTop ∧
      Tendsto (fun n => εseq (σ n)) atTop (nhds 0) ∧
      (∀ x : Vec3, u (x, 0) = a x) ∧
      (∀ T : ℝ, 0 < T →
        let μ : Measure ParabolicPoint :=
          volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 T))
        let U : ℕ → ParabolicPoint → Vec3 :=
          fun n => forcedRegVelocity ρ a ha f hf (εseq (σ n))
        let J : ℕ → ParabolicPoint → Vec3 := fun n =>
          CKN.Leray.regUniformMollifiedVelocity ρ (εseq (σ n))
            (by exact (hseq (σ n)).1) (U n)
        let Dseq : ℕ → ParabolicPoint → Fin 3 → Vec3 := fun n =>
          forcedRegGradient ρ a ha f hf (εseq (σ n))
        AEStronglyMeasurable u μ ∧ AEStronglyMeasurable Du μ ∧
        MemLp u 2 μ ∧ MemLp Du 2 μ ∧
        Tendsto (fun n => eLpNorm (U n - u) 2 μ) atTop (nhds 0) ∧
        (∀ i j, ∀ w : ParabolicPoint → ℝ, MemLp w 2 μ →
          Tendsto (fun n => ∫ z in spaceTimeSet
              (Set.univ : Set Vec3) (Ioo 0 T), Dseq n z i j * w z)
            atTop (nhds (∫ z in spaceTimeSet
              (Set.univ : Set Vec3) (Ioo 0 T), Du z i j * w z))) ∧
        (∀ q : ℝ, 2 ≤ q → q < 10 / 3 →
          Tendsto (fun n => eLpNorm (U n - u) (ENNReal.ofReal q) μ)
            atTop (nhds 0)) ∧
        (∀ n, MemLp (U n) 3 μ) ∧
        (∀ n, MemLp (J n) 3 μ) ∧ MemLp u 3 μ ∧
        Tendsto (fun n => eLpNorm (J n - u) 3 μ) atTop (nhds 0) ∧
        (∀ t : ℝ, 0 < t → ∀ w : Vec3 → Vec3,
          MemLp w 2 volume →
          Tendsto (fun n => ∫ x : Vec3, ∑ i : Fin 3,
              U n (x, t) i * w x i) atTop
            (nhds (∫ x : Vec3, ∑ i : Fin 3, u (x, t) i * w x i))) ∧
        (∀ᵐ t ∂(volume.restrict (Ioi (0 : ℝ))), ∀ i : Fin 3,
          HasWeakGradientOn (Set.univ : Set Vec3)
            (fun x => u (x, t) i) (fun x => Du (x, t) i))) ∧
      (∀ z : Vec3 × ℝ, 0 < z.2 →
        u (parabolicHomeomorph.symm z) =
          CKN.Leray.compactnessMollifiedLimit
            (fun n => fun y =>
              forcedRegVelocity ρ a ha f hf (εseq (σ n))
                (parabolicHomeomorph.symm y)) σ z) := by
  intro a ha f hf εseq hseq hεseq
  obtain ⟨σ, hσ, v, g, hv, hg, hlocal, hstrong, hgrad, hae, hslice, hgbound, hrep⟩ :=
    forcedLerayLimit_local_compactness ρ a ha f hf εseq hseq
  let u : ParabolicPoint → Vec3 := fun z =>
    if 0 < z.2 then v (parabolicHomeomorph z) else a z.1
  let Du : ParabolicPoint → Fin 3 → Vec3 := fun z i j =>
    WithLp.ofLp (g (parabolicHomeomorph z) i) j
  have huv : ∀ (x : Vec3) (t : ℝ), 0 < t → u (x, t) = v (x, t) := fun x t ht => by
    simp [u, ht]
  have hσtop : Tendsto σ atTop atTop := hσ.tendsto_atTop
  have hεsub : Tendsto (fun n => εseq (σ n)) atTop (𝓝 0) := hεseq.comp hσtop
  have hevery := forcedLerayLimit_everyTimePairings ρ a ha f hf εseq hseq σ v u hv huv
    hlocal hslice
  refine ⟨σ, u, Du, hσ, hσtop, hεsub, fun x => by simp [u], fun T hT => ?_, ?_⟩
  · obtain ⟨hum, hu2, hL2, hLq, hU3, hJ3, hu3, hJ⟩ :=
      forcedLerayLimit_strong_clauses ρ a ha f hf εseq hseq σ hεsub v hv u huv
        hstrong hslice T hT (htails a ha f hf εseq hseq σ v hv T hT hlocal)
    obtain ⟨hDm, hD2, hDw⟩ :=
      forcedLerayLimit_gradient_clauses ρ a ha f hf εseq hseq σ g hgrad T hT
    have haeu : ∀ᵐ t ∂(volume.restrict (Ioi (0 : ℝ))), ∀ i : Fin 3,
        HasWeakGradientOn (Set.univ : Set Vec3)
          (fun x => u (x, t) i) (fun x => Du (x, t) i) := by
      filter_upwards [hae, ae_restrict_mem measurableSet_Ioi] with t ht htpos
      intro i
      have hfun : (fun x : Vec3 => u (x, t) i) = fun x => v (x, t) i := by
        funext x
        rw [huv x t htpos]
      rw [hfun]
      exact ht i
    exact ⟨hum, hDm, hu2, hD2, hL2, hDw, hLq, hU3, hJ3, hu3, hJ, hevery, haeu⟩
  · intro z hz
    have hu : u (parabolicHomeomorph.symm z) = v z := by
      change u (z.1, z.2) = v z
      rw [huv z.1 z.2 hz]
    rw [hu, hrep z]
    symm
    refine compactnessMollifiedLimit_comp_eq_of_tendsto
      (fun n => forcedRegVelocity ρ a ha f hf (εseq n)) σ hσtop z ?_
    intro i m
    let r := CKN.sliceRadius m
    let hr := CKN.sliceRadius_pos m
    let w : Vec3 → Vec3 := fun y => Pi.single i (CKN.mollifier (d := 3) r hr (z.1 - y))
    have hw : MemLp w 2 volume :=
      (memLp_reflected_mollifier_coordinate m z.1 i).continuousLinearMap_comp
        (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 3 => ℝ)).toContinuousLinearMap
    have hpair : ∀ G : Vec3 → Vec3,
        CKN.mollify (fun y => G y i) r hr z.1 = ∫ y, ∑ j : Fin 3, G y j * w y j := by
      intro G
      rw [← CKN.integral_mul_mollifier_sub]
      congr 1
      funext y
      simp [w, Pi.single_apply]
    refine ⟨∫ y, ∑ j : Fin 3, u (y, z.2) j * w y j, ?_⟩
    have h := hevery z.2 hz w hw
    refine h.congr (fun k => ?_)
    exact (hpair _).symm

end CKN.Leray

end
