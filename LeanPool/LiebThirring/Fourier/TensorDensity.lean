/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

-- Imported from upstream commit 8bf4656f07f5aaa227b0b850d77b16976915bbd4.
-- Imports adapted for Lean Pool.

public import Mathlib.Analysis.Distribution.SchwartzSpace.Basic
public import LeanPool.LiebThirring.Kinetic.ContractionState

/-!
# Density of smooth one-particle tensors

Continuous linear maps out of a finite-spin normed-space-valued `L²` space are determined by their
values on elementary tensors.

Applying a linear isometry componentwise to the normed factor of an elementary tensor
is the same as applying it before insertion.
-/

public section

open MeasureTheory
open scoped ENNReal SchwartzMap

namespace LiebThirring

variable {ι α H K : Type*} [Fintype ι] [MeasurableSpace α]
  [NormedAddCommGroup H] [NormedSpace ℂ H]
  [NormedAddCommGroup K] [NormedSpace ℂ K]
  {μ : Measure α}

/-- Continuous linear maps out of a finite-spin normed-space-valued `L²` space are
determined by their values on elementary tensors. -/
theorem continuousLinearMap_ext_tensorInsertion
    (A B : Lp (PiLp 2 (fun _ : ι => H)) 2 μ →L[ℂ] K)
    (h : ∀ (f : Lp (EuclideanSpace ℂ ι) 2 μ) (v : H),
      A (tensorInsertion (ι := ι) (H := H) f v) =
        B (tensorInsertion (ι := ι) (H := H) f v)) :
    A = B := by
  classical
  apply ContinuousLinearMap.ext
  intro g
  apply Lp.induction (p := (2 : ℝ≥0∞)) (μ := μ) (by norm_num)
    (fun g => A g = B g)
  · intro c s hs hμs
    let f (j : ι) : Lp (EuclideanSpace ℂ ι) 2 μ :=
      indicatorConstLp 2 hs hμs.ne (EuclideanSpace.single j (1 : ℂ))
    have hg : Lp.simpleFunc.indicatorConst 2 hs hμs.ne c =
        ∑ j : ι, tensorInsertion (ι := ι) (H := H) (f j) (c j) := by
      rw [Lp.simpleFunc.coe_indicatorConst]
      apply Lp.ext
      have hc : ∀ᵐ x ∂μ,
          (indicatorConstLp 2 hs hμs.ne c : Lp (PiLp 2 (fun _ : ι => H)) 2 μ) x =
            s.indicator (fun _ => c) x := indicatorConstLp_coeFn
      filter_upwards [hc,
        eventually_countable_forall.mpr (fun j =>
          tensorInsertion_apply_ae (ι := ι) (H := H) (f j) (c j)),
        eventually_countable_forall.mpr (fun j =>
          show ∀ᵐ x ∂μ, f j x = s.indicator
            (fun _ => EuclideanSpace.single j (1 : ℂ)) x from indicatorConstLp_coeFn),
        Lp.coeFn_finsetSum Finset.univ (fun j =>
          tensorInsertion (ι := ι) (H := H) (f j) (c j))]
        with x hx ht hfi hsum
      rw [hx]
      rw [hsum]
      apply PiLp.ext
      intro k
      simp only [Finset.sum_apply]
      by_cases hxs : x ∈ s
      · rw [Set.indicator_of_mem hxs]
        simp [ht, hfi, hxs, EuclideanSpace.single]
      · rw [Set.indicator_of_notMem hxs]
        simp [ht, hfi, hxs, EuclideanSpace.single]
    rw [hg, map_sum, map_sum]
    apply Finset.sum_congr rfl
    intro j _
    exact h (f j) (c j)
  · intro f g hf hg hd hAf hAg
    simpa only [map_add] using congrArg₂ (· + ·) hAf hAg
  · exact isClosed_eq A.continuous B.continuous

/-- Applying a linear isometry componentwise to the normed-space-valued factor of
an elementary tensor is the same as applying it before insertion. -/
theorem piLpCongrRight_compLp_tensorInsertion
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [NormedAddCommGroup F] [NormedSpace ℂ F]
    (T : E ≃ₗᵢ[ℂ] F) (f : Lp (EuclideanSpace ℂ ι) 2 μ) (v : E) :
    (LinearIsometryEquiv.piLpCongrRight 2
      (fun _ : ι => T)).toContinuousLinearEquiv.toContinuousLinearMap.compLp
        (tensorInsertion (ι := ι) (H := E) f v) =
      tensorInsertion (ι := ι) (H := F) f (T v) := by
  apply Lp.ext
  filter_upwards [
    (LinearIsometryEquiv.piLpCongrRight 2
      (fun _ : ι => T)).toContinuousLinearEquiv.toContinuousLinearMap.coeFn_compLp
        (tensorInsertion (ι := ι) (H := E) f v),
    tensorInsertion_apply_ae (ι := ι) (H := E) f v,
    tensorInsertion_apply_ae (ι := ι) (H := F) f (T v)] with x hx hE hF
  rw [hx]
  apply PiLp.ext
  intro s
  change T (tensorInsertion (ι := ι) (H := E) f v x s) =
    tensorInsertion (ι := ι) (H := F) f (T v) x s
  rw [hE s, hF s, map_smul]

/-- Continuous linear maps out of the state space are determined by
one-particle insertions whose two factors are Schwartz maps. -/
theorem continuousLinearMap_ext_oneParticleInsertion_schwartz {N q : ℕ} (i : Fin N)
    (A B : State N q →L[ℂ] K)
    (h : ∀ (f : SchwartzMap Position (EuclideanSpace ℂ (Fin q)))
      (v : SchwartzMap (OtherConfiguration i)
        (EuclideanSpace ℂ (OtherSpinLabels i q))),
      A (oneParticleInsertion i (f.toLp 2 volume) (v.toLp 2 volume)) =
        B (oneParticleInsertion i (f.toLp 2 volume) (v.toLp 2 volume))) :
    A = B := by
  let C : Lp (PiLp 2 (fun _ : Fin q => RestState i q)) 2
      (volume : Measure Position) →L[ℂ] State N q :=
    (oneParticleCurryingLinearIsometryEquiv (q := q) i).symm.toContinuousLinearEquiv
      |>.toContinuousLinearMap
  have hAB : A.comp C = B.comp C := by
    apply continuousLinearMap_ext_tensorInsertion
    intro f v
    have hv : A (oneParticleInsertion i f v) = B (oneParticleInsertion i f v) := by
      apply DenseRange.induction_on
        (p := fun v : RestState i q =>
          A (oneParticleInsertion i f v) = B (oneParticleInsertion i f v))
        (SchwartzMap.denseRange_toLpCLM
          (E := OtherConfiguration i) (F := EuclideanSpace ℂ (OtherSpinLabels i q))
          (p := 2) (μ := (volume : Measure (OtherConfiguration i))) ENNReal.ofNat_ne_top) v
      · exact isClosed_eq (A.continuous.comp (oneParticleInsertion i f).continuous)
          (B.continuous.comp (oneParticleInsertion i f).continuous)
      · intro w
        apply DenseRange.induction_on
          (p := fun f : Lp (EuclideanSpace ℂ (Fin q)) 2 (volume : Measure Position) =>
            A (oneParticleInsertion i f (w.toLp 2 volume)) =
              B (oneParticleInsertion i f (w.toLp 2 volume)))
          (SchwartzMap.denseRange_toLpCLM
            (E := Position) (F := EuclideanSpace ℂ (Fin q)) (p := 2)
            (μ := (volume : Measure Position)) ENNReal.ofNat_ne_top) f
        · let J : Lp (EuclideanSpace ℂ (Fin q)) 2 (volume : Measure Position) →L[ℂ]
              Lp (PiLp 2 (fun _ : Fin q => RestState i q)) 2 volume :=
            (tensorInsertionBilinear (ι := Fin q) (H := RestState i q)).compLpL₂
              2 volume (w.toLp 2 volume)
          exact isClosed_eq (A.continuous.comp (C.continuous.comp J.continuous))
            (B.continuous.comp (C.continuous.comp J.continuous))
        · intro g
          exact h g w
    exact hv
  apply ContinuousLinearMap.ext
  intro ψ
  have hψ := congrArg (fun T :
      Lp (PiLp 2 (fun _ : Fin q => RestState i q)) 2 volume →L[ℂ] K =>
        T (oneParticleCurryingLinearIsometryEquiv i ψ)) hAB
  change A (C (oneParticleCurryingLinearIsometryEquiv i ψ)) =
    B (C (oneParticleCurryingLinearIsometryEquiv i ψ)) at hψ
  have hc : C (oneParticleCurryingLinearIsometryEquiv i ψ) = ψ :=
    (oneParticleCurryingLinearIsometryEquiv i).symm_apply_apply ψ
  rw [hc] at hψ
  exact hψ

end LiebThirring

end
