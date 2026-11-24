/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.Surface.Defs
import Mathlib.Analysis.Convex.PathConnected

/-!
# Topological Properties of Closed and Open Discs

This file proves the foundational topological properties of closed discs (`ClosedUnitDisc`,
`IsClosedDisc`) and open discs (`OpenUnitDisc`, `IsOpenDisc`) used in Graph Minors VI and XI:
- Convexity and path-connectedness of `ClosedUnitDisc` and `OpenUnitDisc` (via `convex_closedBall`
  and `convex_ball` in `Mathlib.Analysis.Convex.PathConnected`).
- Straight-line homotopy in `ClosedUnitDisc`: any two curves in a closed disc $\Delta$ with the
  same endpoints are homotopic in $\Delta$ (`CurvesHomotopicIn`), and every closed curve in a
  closed or open disc is null-homotopic (`ClosedCurveIsNullHomotopicIn`, `IsSimplyConnectedSet`).
- Equivariance of drawings, regions, and curve homotopy under homeomorphisms of surfaces.
-/

@[expose] public section

namespace GraphMinor.Surface

open Set Function Metric Topology unitInterval

universe u v

/-! ## 1. Convexity and Path-Connectedness of Standard Discs -/

/-- The closed unit disc `ClosedUnitDisc` in $\mathbb{R}^2$ is convex.
Route: `convex_closedBall` from `Mathlib.Analysis.Convex.NormedSpace`. -/
theorem convex_closedUnitDisc : Convex ℝ ClosedUnitDisc :=
  convex_closedBall 0 1

/-- The open unit disc `OpenUnitDisc` in $\mathbb{R}^2$ is convex.
Route: `convex_ball` from `Mathlib.Analysis.Convex.NormedSpace`. -/
theorem convex_openUnitDisc : Convex ℝ OpenUnitDisc :=
  convex_ball 0 1

/-- The origin $0$ lies in `ClosedUnitDisc`. -/
theorem zero_mem_closedUnitDisc : (0 : EuclideanPlane) ∈ ClosedUnitDisc :=
  mem_closedBall_self zero_le_one

/-- The origin $0$ lies in `OpenUnitDisc`. -/
theorem zero_mem_openUnitDisc : (0 : EuclideanPlane) ∈ OpenUnitDisc :=
  mem_ball_self zero_lt_one

/-- `ClosedUnitDisc` is path-connected.
Route: `Convex.isPathConnected` applied to `convex_closedUnitDisc`. -/
theorem isPathConnected_closedUnitDisc : IsPathConnected ClosedUnitDisc :=
  convex_closedUnitDisc.isPathConnected ⟨0, zero_mem_closedUnitDisc⟩

/-- `OpenUnitDisc` is path-connected.
Route: `Convex.isPathConnected` applied to `convex_openUnitDisc`. -/
theorem isPathConnected_openUnitDisc : IsPathConnected OpenUnitDisc :=
  convex_openUnitDisc.isPathConnected ⟨0, zero_mem_openUnitDisc⟩

/-- Every closed disc $\Delta \subseteq S$ is path-connected.
Route: homeomorphic image of `ClosedUnitDisc` via `IsInducing.subtypeVal.isPathConnected_iff`. -/
theorem IsClosedDisc.isPathConnected {S : Type u} [TopologicalSpace S] {Δ : Set S}
    (hΔ : IsClosedDisc Δ) : IsPathConnected Δ := by
  rcases hΔ with ⟨h⟩
  have hpc : PathConnectedSpace ClosedUnitDisc :=
    isPathConnected_iff_pathConnectedSpace.mp isPathConnected_closedUnitDisc
  have hpc' : PathConnectedSpace Δ := h.surjective.pathConnectedSpace h.continuous
  exact isPathConnected_iff_pathConnectedSpace.mpr hpc'

/-- Every open disc $\Lambda \subseteq S$ is path-connected.
Route: homeomorphic image of `OpenUnitDisc`. -/
theorem IsOpenDisc.isPathConnected {S : Type u} [TopologicalSpace S] {Λ : Set S}
    (hΛ : IsOpenDisc Λ) : IsPathConnected Λ := by
  rcases hΛ with ⟨_, ⟨h⟩⟩
  have hpc : PathConnectedSpace OpenUnitDisc :=
    isPathConnected_iff_pathConnectedSpace.mp isPathConnected_openUnitDisc
  have hpc' : PathConnectedSpace Λ := h.surjective.pathConnectedSpace h.continuous
  exact isPathConnected_iff_pathConnectedSpace.mpr hpc'

/-! ## 2. Straight-Line Homotopy and Simple Connectivity of Discs -/

/-- Any two curves in a convex subset $Z \subseteq \mathbb{R}^2$ that share the same initial point
and the same terminal point are homotopic in $Z$.
Route: straight-line interpolation $(x, t) \mapsto (1 - t) \phi_0(x) + t \phi_1(x)$. -/
theorem curvesHomotopicIn_of_convex {Z : Set EuclideanPlane} (hZ : Convex ℝ Z)
    {φ₀ φ₁ : Curve EuclideanPlane}
    (hφ₀ : range φ₀ ⊆ Z) (hφ₁ : range φ₁ ⊆ Z)
    (h0 : φ₀ 0 = φ₁ 0) (h1 : φ₀ 1 = φ₁ 1) :
    CurvesHomotopicIn Z φ₀ φ₁ := by
  refine ⟨⟨fun p => (1 - (p.2 : ℝ)) • φ₀ p.1 + (p.2 : ℝ) • φ₁ p.1, by fun_prop⟩,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro p
    exact hZ (hφ₀ (mem_range_self p.1)) (hφ₁ (mem_range_self p.1))
      (sub_nonneg.mpr p.2.2.2) p.2.2.1 (sub_add_cancel 1 (p.2 : ℝ))
  · intro x
    simp
  · intro x
    simp
  · intro y
    calc (1 - (y : ℝ)) • φ₀ 0 + (y : ℝ) • φ₁ 0
      _ = (1 - (y : ℝ)) • φ₀ 0 + (y : ℝ) • φ₀ 0 := by rw [h0]
      _ = ((1 - (y : ℝ)) + (y : ℝ)) • φ₀ 0 := (add_smul _ _ _).symm
      _ = φ₀ 0 := by simp
  · intro y
    calc (1 - (y : ℝ)) • φ₀ 0 + (y : ℝ) • φ₁ 0
      _ = (1 - (y : ℝ)) • φ₁ 0 + (y : ℝ) • φ₁ 0 := by rw [h0]
      _ = ((1 - (y : ℝ)) + (y : ℝ)) • φ₁ 0 := (add_smul _ _ _).symm
      _ = φ₁ 0 := by simp
  · intro y
    calc (1 - (y : ℝ)) • φ₀ 1 + (y : ℝ) • φ₁ 1
      _ = (1 - (y : ℝ)) • φ₀ 1 + (y : ℝ) • φ₀ 1 := by rw [h1]
      _ = ((1 - (y : ℝ)) + (y : ℝ)) • φ₀ 1 := (add_smul _ _ _).symm
      _ = φ₀ 1 := by simp
  · intro y
    calc (1 - (y : ℝ)) • φ₀ 1 + (y : ℝ) • φ₁ 1
      _ = (1 - (y : ℝ)) • φ₁ 1 + (y : ℝ) • φ₁ 1 := by rw [h1]
      _ = ((1 - (y : ℝ)) + (y : ℝ)) • φ₁ 1 := (add_smul _ _ _).symm
      _ = φ₁ 1 := by simp

/-- Any two curves in a closed disc $\Delta \subseteq S$ with the same endpoints are homotopic in
$\Delta$.
Graph Minors VI, Section 4 (page 123): on a disc, all routes between a given pair of boundary
points are homotopic.
Route: pull back to `ClosedUnitDisc` via the defining homeomorphism and apply straight-line
homotopy `curvesHomotopicIn_of_convex`. -/
theorem IsClosedDisc.curvesHomotopicIn {S : Type u} [TopologicalSpace S] {Δ : Set S}
    (hΔ : IsClosedDisc Δ) {φ₀ φ₁ : Curve S}
    (hφ₀ : range φ₀ ⊆ Δ) (hφ₁ : range φ₁ ⊆ Δ)
    (h0 : φ₀ 0 = φ₁ 0) (h1 : φ₀ 1 = φ₁ 1) :
    CurvesHomotopicIn Δ φ₀ φ₁ := by
  rcases hΔ with ⟨e⟩
  let lift0 : C(unitInterval, ClosedUnitDisc) :=
    ⟨fun x => e.symm ⟨φ₀ x, hφ₀ (mem_range_self x)⟩,
      e.symm.continuous.comp ( φ₀.continuous.subtype_mk _ )⟩
  let lift1 : C(unitInterval, ClosedUnitDisc) :=
    ⟨fun x => e.symm ⟨φ₁ x, hφ₁ (mem_range_self x)⟩,
      e.symm.continuous.comp ( φ₁.continuous.subtype_mk _ )⟩
  let c0 : Curve EuclideanPlane := ⟨fun x => (lift0 x).1, continuous_subtype_val.comp
    lift0.continuous⟩
  let c1 : Curve EuclideanPlane := ⟨fun x => (lift1 x).1, continuous_subtype_val.comp
    lift1.continuous⟩
  have hc0 : range c0 ⊆ ClosedUnitDisc := by rintro _ ⟨x, rfl⟩; exact (lift0 x).2
  have hc1 : range c1 ⊆ ClosedUnitDisc := by rintro _ ⟨x, rfl⟩; exact (lift1 x).2
  have hc01_0 : c0 0 = c1 0 := by
    change (e.symm ⟨φ₀ 0, _⟩).1 = (e.symm ⟨φ₁ 0, _⟩).1
    congr 1; exact congrArg e.symm (Subtype.ext h0)
  have hc01_1 : c0 1 = c1 1 := by
    change (e.symm ⟨φ₀ 1, _⟩).1 = (e.symm ⟨φ₁ 1, _⟩).1
    congr 1; exact congrArg e.symm (Subtype.ext h1)
  rcases curvesHomotopicIn_of_convex convex_closedUnitDisc hc0 hc1 hc01_0 hc01_1 with
    ⟨ψ, hψZ, hψ0, hψ1, hψy0, hψy0', hψy1, hψy1'⟩
  let Ψ : C(unitInterval × unitInterval, S) :=
    ⟨fun p => (e ⟨ψ p, hψZ p⟩).1,
      continuous_subtype_val.comp (e.continuous.comp (ψ.continuous.subtype_mk hψZ))⟩
  refine ⟨Ψ, fun p => (e ⟨ψ p, hψZ p⟩).2, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro x
    have hx : (⟨ψ (x, 0), hψZ (x, 0)⟩ : ClosedUnitDisc) = lift0 x := Subtype.ext (hψ0 x)
    change (e ⟨ψ (x, 0), hψZ (x, 0)⟩).1 = φ₀ x
    rw [hx]
    exact congrArg Subtype.val (e.apply_symm_apply _)
  · intro x
    have hx : (⟨ψ (x, 1), hψZ (x, 1)⟩ : ClosedUnitDisc) = lift1 x := Subtype.ext (hψ1 x)
    change (e ⟨ψ (x, 1), hψZ (x, 1)⟩).1 = φ₁ x
    rw [hx]
    exact congrArg Subtype.val (e.apply_symm_apply _)
  · intro y
    have hy : (⟨ψ (0, y), hψZ (0, y)⟩ : ClosedUnitDisc) = lift0 0 := Subtype.ext (hψy0 y)
    change (e ⟨ψ (0, y), hψZ (0, y)⟩).1 = φ₀ 0
    rw [hy]
    exact congrArg Subtype.val (e.apply_symm_apply _)
  · intro y
    have hy : (⟨ψ (0, y), hψZ (0, y)⟩ : ClosedUnitDisc) = lift1 0 := Subtype.ext (hψy0' y)
    change (e ⟨ψ (0, y), hψZ (0, y)⟩).1 = φ₁ 0
    rw [hy]
    exact congrArg Subtype.val (e.apply_symm_apply _)
  · intro y
    have hy : (⟨ψ (1, y), hψZ (1, y)⟩ : ClosedUnitDisc) = lift0 1 := Subtype.ext (hψy1 y)
    change (e ⟨ψ (1, y), hψZ (1, y)⟩).1 = φ₀ 1
    rw [hy]
    exact congrArg Subtype.val (e.apply_symm_apply _)
  · intro y
    have hy : (⟨ψ (1, y), hψZ (1, y)⟩ : ClosedUnitDisc) = lift1 1 := Subtype.ext (hψy1' y)
    change (e ⟨ψ (1, y), hψZ (1, y)⟩).1 = φ₁ 1
    rw [hy]
    exact congrArg Subtype.val (e.apply_symm_apply _)

/-- Every closed disc $\Delta \subseteq S$ is simply connected (`IsSimplyConnectedSet`).
Graph Minors XI, Section 3 (page 76).
Route: straight-line contraction to the image of the origin $0 \in \text{ClosedUnitDisc}$. -/
theorem IsClosedDisc.isSimplyConnectedSet {S : Type u} [TopologicalSpace S] {Δ : Set S}
    (hΔ : IsClosedDisc Δ) : IsSimplyConnectedSet Δ := by
  refine ⟨hΔ.isPathConnected, fun φ hφ => ?_⟩
  rcases hΔ with ⟨e⟩
  let c0 : ClosedUnitDisc := ⟨0, zero_mem_closedUnitDisc⟩
  refine ⟨(e c0).1, (e c0).2, ?_⟩
  let lift : C(Circle, ClosedUnitDisc) :=
    ⟨fun x => e.symm ⟨φ x, hφ (mem_range_self x)⟩,
      e.symm.continuous.comp (φ.continuous.subtype_mk _)⟩
  have hmem : ∀ p : Circle × unitInterval,
      (1 - (p.2 : ℝ)) • (lift p.1).1 + (p.2 : ℝ) • (0 : EuclideanPlane) ∈ ClosedUnitDisc := by
    intro p
    exact convex_closedUnitDisc (lift p.1).2 zero_mem_closedUnitDisc
      (sub_nonneg.mpr p.2.2.2) p.2.2.1 (sub_add_cancel 1 (p.2 : ℝ))
  let Ψ : C(Circle × unitInterval, S) :=
    ⟨fun p => (e ⟨(1 - (p.2 : ℝ)) • (lift p.1).1 + (p.2 : ℝ) • 0, hmem p⟩).1,
      continuous_subtype_val.comp (e.continuous.comp
        ((Continuous.add
          (Continuous.smul (continuous_const.sub (continuous_subtype_val.comp continuous_snd))
            (continuous_subtype_val.comp (lift.continuous.comp continuous_fst)))
          (Continuous.smul (continuous_subtype_val.comp continuous_snd)
            continuous_const)).subtype_mk
          hmem))⟩
  refine ⟨Ψ, fun p => (e ⟨_, hmem p⟩).2, ?_, ?_⟩
  · intro x
    have hx : (⟨(1 - ((x, (0 : unitInterval)).2 : ℝ)) • (lift (x, (0 : unitInterval)).1).1 +
        ((x, (0 : unitInterval)).2 : ℝ) • 0, hmem (x, 0)⟩ : ClosedUnitDisc) = lift x := by
      ext; simp
    change (e ⟨_, hmem (x, 0)⟩).1 = φ x
    rw [hx]
    exact congrArg Subtype.val (e.apply_symm_apply _)
  · intro x
    have hx : (⟨(1 - ((x, (1 : unitInterval)).2 : ℝ)) • (lift (x, (1 : unitInterval)).1).1 +
        ((x, (1 : unitInterval)).2 : ℝ) • 0, hmem (x, 1)⟩ : ClosedUnitDisc) = c0 := by
      ext; simp [c0]
    change (e ⟨_, hmem (x, 1)⟩).1 = (e c0).1
    rw [hx]

/-- Every open disc $\Lambda \subseteq S$ is simply connected (`IsSimplyConnectedSet`).
Graph Minors XI, Section 3 (page 76).
Route: straight-line contraction to the image of the origin $0 \in \text{OpenUnitDisc}$. -/
theorem IsOpenDisc.isSimplyConnectedSet {S : Type u} [TopologicalSpace S] {Λ : Set S}
    (hΛ : IsOpenDisc Λ) : IsSimplyConnectedSet Λ := by
  refine ⟨hΛ.isPathConnected, fun φ hφ => ?_⟩
  rcases hΛ with ⟨_, ⟨e⟩⟩
  let c0 : OpenUnitDisc := ⟨0, zero_mem_openUnitDisc⟩
  refine ⟨(e c0).1, (e c0).2, ?_⟩
  let lift : C(Circle, OpenUnitDisc) :=
    ⟨fun x => e.symm ⟨φ x, hφ (mem_range_self x)⟩,
      e.symm.continuous.comp (φ.continuous.subtype_mk _)⟩
  have hmem : ∀ p : Circle × unitInterval,
      (1 - (p.2 : ℝ)) • (lift p.1).1 + (p.2 : ℝ) • (0 : EuclideanPlane) ∈ OpenUnitDisc := by
    intro p
    exact convex_openUnitDisc (lift p.1).2 zero_mem_openUnitDisc
      (sub_nonneg.mpr p.2.2.2) p.2.2.1 (sub_add_cancel 1 (p.2 : ℝ))
  let Ψ : C(Circle × unitInterval, S) :=
    ⟨fun p => (e ⟨(1 - (p.2 : ℝ)) • (lift p.1).1 + (p.2 : ℝ) • 0, hmem p⟩).1,
      continuous_subtype_val.comp (e.continuous.comp
        ((Continuous.add
          (Continuous.smul (continuous_const.sub (continuous_subtype_val.comp continuous_snd))
            (continuous_subtype_val.comp (lift.continuous.comp continuous_fst)))
          (Continuous.smul (continuous_subtype_val.comp continuous_snd)
            continuous_const)).subtype_mk
          hmem))⟩
  refine ⟨Ψ, fun p => (e ⟨_, hmem p⟩).2, ?_, ?_⟩
  · intro x
    have hx : (⟨(1 - ((x, (0 : unitInterval)).2 : ℝ)) • (lift (x, (0 : unitInterval)).1).1 +
        ((x, (0 : unitInterval)).2 : ℝ) • 0, hmem (x, 0)⟩ : OpenUnitDisc) = lift x := by
      ext; simp
    change (e ⟨_, hmem (x, 0)⟩).1 = φ x
    rw [hx]
    exact congrArg Subtype.val (e.apply_symm_apply _)
  · intro x
    have hx : (⟨(1 - ((x, (1 : unitInterval)).2 : ℝ)) • (lift (x, (1 : unitInterval)).1).1 +
        ((x, (1 : unitInterval)).2 : ℝ) • 0, hmem (x, 1)⟩ : OpenUnitDisc) = c0 := by
      ext; simp [c0]
    change (e ⟨_, hmem (x, 1)⟩).1 = (e c0).1
    rw [hx]

end GraphMinor.Surface
