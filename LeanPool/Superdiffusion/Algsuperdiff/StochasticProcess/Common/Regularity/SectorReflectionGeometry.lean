/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.ExcessDecay.OneStepOddPackaging

/-!
# SectorReflectionGeometry

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# Euclidean ball sectors and their partial reflections

This file supplies the finite-face geometry needed to reuse the Section 4 odd-reflection
machinery on a Euclidean ball.  A finite set `S` records the coordinate hyperplanes through the
centre `x₀`; `sigma i = 1` selects the lower half-space and `sigma i = -1` the upper half-space.
The intermediate domain `partialReflectedBallSector x₀ r S sigma T` retains precisely the face
constraints in `S \ T`.  It is the original sector at `T = ∅` and the full Euclidean ball at
`T = S`.
-/

namespace Algsuperdiff.StochasticProcess.Common.Regularity

open HCPolySupport MeasureTheory
open Algsuperdiff.Section4.Provider.ExcessDecay

noncomputable section

variable {d : ℕ}

/-! ## The finite coordinate-reflection group -/

/-- Reflection in precisely the coordinate hyperplanes indexed by `J`, all of which pass through
`x₀`. -/
def sectorReflection (x₀ : Vec d) (J : Finset (Fin d)) : Vec d → Vec d :=
  fun y i => if i ∈ J then 2 * x₀ i - y i else y i

/-- The linear action induced on gradients by `sectorReflection`. -/
def sectorReflectionLinear (J : Finset (Fin d)) : Vec d → Vec d :=
  fun v i => if i ∈ J then -v i else v i

/-- The parity sign of a reflection-group element. -/
def sectorReflectionSign (J : Finset (Fin d)) : ℝ :=
  (-1 : ℝ) ^ J.card

@[simp] theorem sectorReflection_empty (x₀ y : Vec d) :
    sectorReflection x₀ ∅ y = y := by
  funext i
  simp [sectorReflection]

@[simp] theorem sectorReflectionLinear_empty (v : Vec d) :
    sectorReflectionLinear ∅ v = v := by
  funext i
  simp [sectorReflectionLinear]

@[simp] theorem sectorReflectionSign_empty : sectorReflectionSign (∅ : Finset (Fin d)) = 1 := by
  simp [sectorReflectionSign]

/-- The ball sector obtained by retaining the face constraints in `S \ T`. -/
def partialReflectedBallSector (x₀ : Vec d) (r : ℝ) (S : Finset (Fin d))
    (sigma : Fin d → ℝ) (T : Finset (Fin d)) : Set (Vec d) :=
  euclideanBall x₀ r ∩
    ⋂ i ∈ S \ T, {y : Vec d | 0 < sigma i * (x₀ i - y i)}

/-- The unreflected Euclidean ball sector. -/
def ballSector (x₀ : Vec d) (r : ℝ) (S : Finset (Fin d))
    (sigma : Fin d → ℝ) : Set (Vec d) :=
  partialReflectedBallSector x₀ r S sigma ∅

theorem mem_partialReflectedBallSector_iff {x₀ : Vec d} {r : ℝ}
    {S : Finset (Fin d)} {sigma : Fin d → ℝ} {T : Finset (Fin d)} {y : Vec d} :
    y ∈ partialReflectedBallSector x₀ r S sigma T ↔
      y ∈ euclideanBall x₀ r ∧
        ∀ i ∈ S, i ∉ T → 0 < sigma i * (x₀ i - y i) := by
  simp only [partialReflectedBallSector, Set.mem_inter_iff, Set.mem_iInter,
    Set.mem_ofPred_eq, Finset.mem_sdiff]
  aesop

theorem mem_ballSector_iff {x₀ : Vec d} {r : ℝ} {S : Finset (Fin d)}
    {sigma : Fin d → ℝ} {y : Vec d} :
    y ∈ ballSector x₀ r S sigma ↔
      y ∈ euclideanBall x₀ r ∧
        ∀ i ∈ S, 0 < sigma i * (x₀ i - y i) := by
  rw [ballSector, mem_partialReflectedBallSector_iff]
  constructor
  · rintro ⟨hyB, hy⟩
    exact ⟨hyB, fun i hiS => hy i hiS (Finset.notMem_empty i)⟩
  · rintro ⟨hyB, hy⟩
    exact ⟨hyB, fun i hiS _hi => hy i hiS⟩

theorem partialReflectedBallSector_self (x₀ : Vec d) (r : ℝ)
    (S : Finset (Fin d)) (sigma : Fin d → ℝ) :
    partialReflectedBallSector x₀ r S sigma S = euclideanBall x₀ r := by
  ext y
  simp only [mem_partialReflectedBallSector_iff]
  exact and_iff_left_of_imp fun _ i hiS hiS' => absurd hiS hiS'

theorem partialReflectedBallSector_subset_of_subset (x₀ : Vec d) (r : ℝ)
    (S : Finset (Fin d)) (sigma : Fin d → ℝ) {T T' : Finset (Fin d)}
    (hTT' : T ⊆ T') :
    partialReflectedBallSector x₀ r S sigma T ⊆
      partialReflectedBallSector x₀ r S sigma T' := by
  intro y hy
  rw [mem_partialReflectedBallSector_iff] at hy ⊢
  refine ⟨hy.1, fun i hiS hiT' => hy.2 i hiS ?_⟩
  exact fun hiT => hiT' (hTT' hiT)

theorem ballSector_subset_partialReflectedBallSector (x₀ : Vec d) (r : ℝ)
    (S : Finset (Fin d)) (sigma : Fin d → ℝ) (T : Finset (Fin d)) :
    ballSector x₀ r S sigma ⊆ partialReflectedBallSector x₀ r S sigma T := by
  rw [ballSector]
  exact partialReflectedBallSector_subset_of_subset x₀ r S sigma (Finset.empty_subset T)

theorem isOpen_partialReflectedBallSector (x₀ : Vec d) (r : ℝ)
    (S : Finset (Fin d)) (sigma : Fin d → ℝ) (T : Finset (Fin d)) :
    IsOpen (partialReflectedBallSector x₀ r S sigma T) := by
  apply (isOpen_euclideanBall x₀ r).inter
  apply isOpen_biInter_finset
  intro i _hi
  exact isOpen_lt continuous_const
    (continuous_const.mul (continuous_const.sub (continuous_apply i)))

theorem convex_partialReflectedBallSector (x₀ : Vec d) (r : ℝ)
    (S : Finset (Fin d)) (sigma : Fin d → ℝ) (T : Finset (Fin d)) :
    Convex ℝ (partialReflectedBallSector x₀ r S sigma T) := by
  apply (convex_euclideanBall x₀ r).inter
  apply convex_iInter
  intro i
  apply convex_iInter
  intro _hi
  have hlin : IsLinearMap ℝ fun y : Vec d => sigma i * y i :=
    ⟨fun y z => by simp only [Pi.add_apply]; ring,
      fun c y => by simp only [Pi.smul_apply, smul_eq_mul]; ring⟩
  have hset : {y : Vec d | 0 < sigma i * (x₀ i - y i)} =
      {y : Vec d | (fun z : Vec d => sigma i * z i) y < sigma i * x₀ i} := by
    ext y
    simp only [Set.mem_ofPred_eq]
    constructor <;> intro h
    · have heq : sigma i * (x₀ i - y i) = sigma i * x₀ i - sigma i * y i := by ring
      linarith only [h, heq.le, heq.symm.le]
    · have heq : sigma i * (x₀ i - y i) = sigma i * x₀ i - sigma i * y i := by ring
      linarith only [h, heq.le, heq.symm.le]
  rw [hset]
  exact convex_halfSpace_lt hlin (sigma i * x₀ i)

private theorem euclideanBall_subset_metricBall (x₀ : Vec d) {r : ℝ} (hr : 0 < r) :
    euclideanBall x₀ r ⊆ Metric.ball x₀ r := by
  intro y hy
  rw [Metric.mem_ball, dist_eq_norm, pi_norm_lt_iff hr]
  intro i
  rw [Real.norm_eq_abs]
  apply abs_lt_of_sq_lt_sq _ hr.le
  exact (sq_coord_sub_le_euclideanSqDist y x₀ i).trans_lt hy

theorem isBoundedDomain_partialReflectedBallSector (x₀ : Vec d) {r : ℝ} (hr : 0 < r)
    (S : Finset (Fin d)) (sigma : Fin d → ℝ) (T : Finset (Fin d)) :
    IsBoundedDomain (partialReflectedBallSector x₀ r S sigma T) := by
  apply Bornology.IsBounded.isBoundedDomain
  exact Metric.isBounded_ball.subset fun y hy =>
    euclideanBall_subset_metricBall x₀ hr
      ((mem_partialReflectedBallSector_iff.mp hy).1)

theorem isOpenBoundedConvexDomain_partialReflectedBallSector
    (x₀ : Vec d) {r : ℝ} (hr : 0 < r) (S : Finset (Fin d))
    (sigma : Fin d → ℝ) (T : Finset (Fin d)) :
    IsOpenBoundedConvexDomain (partialReflectedBallSector x₀ r S sigma T) :=
  ⟨isOpen_partialReflectedBallSector x₀ r S sigma T,
    isBoundedDomain_partialReflectedBallSector x₀ hr S sigma T,
    convex_partialReflectedBallSector x₀ r S sigma T⟩

theorem euclideanSqDist_coordFaceReflection_center (x₀ y : Vec d) (i : Fin d) :
    euclideanSqDist (coordFaceReflection (x₀ i) i y) x₀ = euclideanSqDist y x₀ := by
  unfold euclideanSqDist vecNormSq vecDot
  apply Finset.sum_congr rfl
  intro j _hj
  rw [Pi.sub_apply, Pi.sub_apply, HCPolySupport.coordFaceReflection_apply]
  by_cases hji : j = i
  · subst hji
    rw [ite_eq_left rfl]
    ring
  · rw [ite_eq_right hji]

theorem mem_euclideanBall_coordFaceReflection_center_iff
    (x₀ : Vec d) (r : ℝ) (i : Fin d) (y : Vec d) :
    coordFaceReflection (x₀ i) i y ∈ euclideanBall x₀ r ↔ y ∈ euclideanBall x₀ r := by
  change euclideanSqDist (coordFaceReflection (x₀ i) i y) x₀ < r ^ 2 ↔
    euclideanSqDist y x₀ < r ^ 2
  rw [euclideanSqDist_coordFaceReflection_center]

/-- Once face `i` has been unfolded, its intermediate sector is invariant under reflection in
that face. -/
theorem mem_partialReflectedBallSector_coordFaceReflection_iff
    {x₀ : Vec d} {r : ℝ} {S : Finset (Fin d)} {sigma : Fin d → ℝ}
    {T : Finset (Fin d)} {i : Fin d} (hiT : i ∈ T) (y : Vec d) :
    coordFaceReflection (x₀ i) i y ∈ partialReflectedBallSector x₀ r S sigma T ↔
      y ∈ partialReflectedBallSector x₀ r S sigma T := by
  rw [mem_partialReflectedBallSector_iff, mem_partialReflectedBallSector_iff,
    mem_euclideanBall_coordFaceReflection_center_iff]
  constructor
  · rintro ⟨hyB, hy⟩
    refine ⟨hyB, fun j hjS hjT => ?_⟩
    have hji : j ≠ i := fun h => hjT (h ▸ hiT)
    have := hy j hjS hjT
    rwa [HCPolySupport.coordFaceReflection_apply, ite_eq_right hji] at this
  · rintro ⟨hyB, hy⟩
    refine ⟨hyB, fun j hjS hjT => ?_⟩
    have hji : j ≠ i := fun h => hjT (h ▸ hiT)
    rw [HCPolySupport.coordFaceReflection_apply, ite_eq_right hji]
    exact hy j hjS hjT

/-- Adding `i` to the unfolded set removes exactly the `i`-half-space constraint. -/
theorem faceHalf_partialReflectedBallSector_insert
    {x₀ : Vec d} {r : ℝ} {S : Finset (Fin d)} {sigma : Fin d → ℝ}
    {T : Finset (Fin d)} {i : Fin d} (hiS : i ∈ S) (hiT : i ∉ T) :
    faceHalf (partialReflectedBallSector x₀ r S sigma (insert i T))
      i (x₀ i) (sigma i) = partialReflectedBallSector x₀ r S sigma T := by
  ext y
  rw [mem_faceHalf_iff, mem_partialReflectedBallSector_iff,
    mem_partialReflectedBallSector_iff]
  constructor
  · rintro ⟨⟨hyB, hy⟩, hyi⟩
    refine ⟨hyB, fun j hjS hjT => ?_⟩
    by_cases hji : j = i
    · subst hji
      exact hyi
    · exact hy j hjS (by simpa [Finset.mem_insert, hji] using hjT)
  · rintro ⟨hyB, hy⟩
    refine ⟨⟨hyB, fun j hjS hjins => hy j hjS ?_⟩, hy i hiS hiT⟩
    exact fun hjT => hjins (Finset.mem_insert_of_mem hjT)

end

end Algsuperdiff.StochasticProcess.Common.Regularity
