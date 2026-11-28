/-
Copyright (c) 2026 Mario Ullrich. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Ullrich
-/
module

public import LeanPool.FunctionSpaces.Domains.Lipschitz.BoundedLipschitz
public import LeanPool.FunctionSpaces.Domains.Lipschitz.GraphParametrization

/-
Modified for Lean Pool: module names and imports adapted.
-/

/-!
# Bounded Lipschitz domains from local Lipschitz graphs

The usual definition of a bounded Lipschitz domain is a condition on a set. A set `Ω ⊆ V` is
**Lipschitz near `z`** (`Rd.IsLipschitzDomainAt`) if there are `r > 0`, a unit vector `ν` and a
Lipschitz function `φ` on the hyperplane `ν^⊥` with
`Ω ∩ B(z, r) = {x : φ(P(x - z)) < ⟪ν, x - z⟫} ∩ B(z, r)`, `P` the orthogonal projection onto
`ν^⊥`; `Ω` is a **bounded Lipschitz set** (`Rd.IsBoundedLipschitzDomain`) if it is open, bounded
and Lipschitz near each point of its frontier.

* A local graph is a Lipschitz graph domain (`Rd.LipschitzGraph.ofLocal`,
  `Rd.LipschitzGraph.domain_ofLocal`), and every Lipschitz graph domain is a local graph around
  every point (`Rd.LipschitzGraph.domain_eq_localPhi`), so being Lipschitz near `z` means agreeing
  with a Lipschitz graph domain on a ball around `z` (`Rd.isLipschitzDomainAt_iff`); this depends
  only on the set near `z` (`Rd.IsLipschitzDomainAt.congr_ball`). Both constructions keep the
  graph functions `C^n` (`Rd.LipschitzGraph.contDiff_phi_ofLocal`,
  `Rd.LipschitzGraph.contDiff_localPhi`). A function
  that is Lipschitz only on the ball of radius `r` of `ν^⊥` suffices, by McShane's extension
  (`Rd.isLipschitzDomainAt_of_lipschitzOnWith`).
* In finite dimension, compactness of the frontier gives finitely many balls out of any family
  of charts at the frontier points, and these charts form a `Rd.BoundedLipschitzDomain` with
  carrier `Ω` (`Rd.BoundedLipschitzDomain.ofCharts`, whose graph domains belong to the family);
  for the chosen charts of a bounded Lipschitz set this is
  `Rd.BoundedLipschitzDomain.ofIsBoundedLipschitzDomain`. Conversely the carrier of every
  `Rd.BoundedLipschitzDomain` is a bounded Lipschitz set
  (`Rd.BoundedLipschitzDomain.isBoundedLipschitzDomain`, `Rd.isBoundedLipschitzDomain_iff_exists`).
* Every open ball `B(c, R)` is a bounded Lipschitz set (`Rd.isBoundedLipschitzDomain_ball`): near
  a point `z` of the sphere, with the inward normal `ν = (c - z)/R`, it lies above the graph of the
  `1`-Lipschitz function `y ↦ R - √(R² - min(‖y‖, R/2)²)` (`Rd.sphereProfile`) on the ball of
  radius `R/2`, the proof of the `quadratic-forms-sobolev-lean` project
  (https://github.com/dbenbenn/quadratic-forms-sobolev-lean). Hence
  `Rd.BoundedLipschitzDomain.ball`.
-/

@[expose] public section

open Metric Set
open scoped NNReal

namespace Rd

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

/-! ### The local condition -/

/-- A set `Ω` is **Lipschitz near the point `z`** if there are a radius `r > 0`, a unit vector `ν`
and an `L`-Lipschitz function `φ` on the hyperplane `ν^⊥` with
`Ω ∩ B(z, r) = {x : φ(P(x - z)) < ⟪ν, x - z⟫} ∩ B(z, r)`, where `P` is the orthogonal projection
onto `ν^⊥`: near `z`, `Ω` is the region above the graph of `φ` in the direction `ν`. This is the
local condition of Grisvard, Definition 1.2.1.1, with the rotation of coordinates replaced by the
direction `ν` and balls in place of hypercubes. Charts in cylinders, as in TauCeti's
`Set.IsLipschitzChart`, give the same sets: at a boundary point `φ(0) = 0`, so a small cylinder
around `z` lies in the ball and a small ball lies in each cylinder. -/
def IsLipschitzDomainAt (Ω : Set V) (z : V) : Prop :=
  ∃ r : ℝ, 0 < r ∧ ∃ ν : V, ‖ν‖ = 1 ∧ ∃ (L : ℝ≥0) (φ : (ℝ ∙ ν)ᗮ → ℝ), LipschitzWith L φ ∧
    Ω ∩ ball z r =
      {x | φ ((ℝ ∙ ν)ᗮ.orthogonalProjectionOnto (x - z)) < inner ℝ ν (x - z)} ∩ ball z r

/-- A **bounded Lipschitz set**: an open bounded set that is Lipschitz near each point of its
frontier (`Rd.IsLipschitzDomainAt`), the usual definition of a bounded Lipschitz domain. In
finite dimension these are exactly the carriers of `Rd.BoundedLipschitzDomain`
(`Rd.isBoundedLipschitzDomain_iff_exists`). -/
def IsBoundedLipschitzDomain (Ω : Set V) : Prop :=
  IsOpen Ω ∧ Bornology.IsBounded Ω ∧ ∀ z ∈ frontier Ω, IsLipschitzDomainAt Ω z

/-! ### The projection onto a hyperplane -/

/-- **Pythagoras along `ν`**: for a unit vector `ν`, `w ∈ V` and `a ∈ ℝ`,
`‖w - a ν‖² = ‖P w‖² + (⟪ν, w⟫ - a)²` for the projection `P` onto `ν^⊥`, since
`w - a ν = P w + (⟪ν, w⟫ - a) ν` with `P w = w - ⟪ν, w⟫ ν ⊥ ν`
(`Rd.coe_orthogonalProjectionOnto_orthogonalComplement_singleton`). -/
theorem norm_sub_smul_sq_eq_norm_orthogonalProjectionOnto_sq_add {ν : V} (hν : ‖ν‖ = 1) (w : V)
    (a : ℝ) :
    ‖w - a • ν‖ ^ 2 =
      ‖((ℝ ∙ ν)ᗮ.orthogonalProjectionOnto w : V)‖ ^ 2 + (inner ℝ ν w - a) ^ 2 := by
  rw [coe_orthogonalProjectionOnto_orthogonalComplement_singleton hν]
  have hνν : inner ℝ ν ν = (1 : ℝ) := by rw [real_inner_self_eq_norm_sq, hν, one_pow]
  have horth : inner ℝ (w - inner ℝ ν w • ν) ((inner ℝ ν w - a) • ν) = (0 : ℝ) := by
    rw [real_inner_smul_right, inner_sub_left, real_inner_smul_left, hνν, real_inner_comm]
    ring
  have hdec : w - a • ν = (w - inner ℝ ν w • ν) + (inner ℝ ν w - a) • ν := by
    rw [sub_smul]
    abel
  rw [hdec, norm_add_sq_real, horth, norm_smul, hν, Real.norm_eq_abs, mul_one, sq_abs]
  ring

/-! ### Local graphs and Lipschitz graph domains -/

namespace LipschitzGraph

/-- **A local graph as a Lipschitz graph domain**: for a point `z`, a unit vector `ν` and an
`L`-Lipschitz `φ` on `ν^⊥`, the Lipschitz graph domain with direction `ν`, constant `L` and graph
function `x ↦ ⟪z, ν⟫ + φ(P(x - z))`. It is constant along `ν` since `P ν = 0` (Mathlib's
`Submodule.orthogonalProjectionOnto_orthogonalComplement_singleton_eq_zero`), and `L`-Lipschitz
since `‖P y‖ ≤ ‖y‖`. -/
noncomputable def ofLocal (z ν : V) (hν : ‖ν‖ = 1) {L : ℝ≥0} (φ : (ℝ ∙ ν)ᗮ → ℝ)
    (hφ : LipschitzWith L φ) : LipschitzGraph V where
  e := ν
  norm_e := hν
  M := L
  M_nonneg := L.2
  phi x := inner ℝ z ν + φ ((ℝ ∙ ν)ᗮ.orthogonalProjectionOnto (x - z))
  lipschitz x y := by
    have h := hφ.dist_le_mul ((ℝ ∙ ν)ᗮ.orthogonalProjectionOnto (x - z))
      ((ℝ ∙ ν)ᗮ.orthogonalProjectionOnto (y - z))
    rw [Real.dist_eq, dist_eq_norm, ← map_sub, sub_sub_sub_cancel_right] at h
    rw [add_sub_add_left_eq_sub]
    exact h.trans (mul_le_mul_of_nonneg_left
      (Submodule.norm_orthogonalProjectionOnto_apply_le _ _) L.2)
  const x t := by
    rw [add_sub_right_comm, map_add, map_smul,
      Submodule.orthogonalProjectionOnto_orthogonalComplement_singleton_eq_zero, smul_zero,
      add_zero]

/-- The Lipschitz graph domain of a local graph is `{x : φ(P(x - z)) < ⟪ν, x - z⟫}`. -/
theorem domain_ofLocal (z ν : V) (hν : ‖ν‖ = 1) {L : ℝ≥0} (φ : (ℝ ∙ ν)ᗮ → ℝ)
    (hφ : LipschitzWith L φ) :
    (ofLocal z ν hν φ hφ).domain =
      {x | φ ((ℝ ∙ ν)ᗮ.orthogonalProjectionOnto (x - z)) < inner ℝ ν (x - z)} := by
  ext x
  change inner ℝ z ν + φ _ < inner ℝ x ν ↔ _
  rw [Set.mem_ofPred_eq, inner_sub_right, real_inner_comm ν x, real_inner_comm ν z]
  constructor <;> intro h <;> linarith

/-- **A smooth local graph has a smooth graph function**: if `φ` is `C^n` on `ν^⊥`, then so is
the graph function `x ↦ ⟪z, ν⟫ + φ(P(x - z))` of `Rd.LipschitzGraph.ofLocal`, since the orthogonal
projection `P` is continuous linear. -/
theorem contDiff_phi_ofLocal (z ν : V) (hν : ‖ν‖ = 1) {L : ℝ≥0} {φ : (ℝ ∙ ν)ᗮ → ℝ}
    (hφ : LipschitzWith L φ) {n : WithTop ℕ∞} (hφn : ContDiff ℝ n φ) :
    ContDiff ℝ n (ofLocal z ν hν φ hφ).phi :=
  contDiff_const.add (hφn.comp ((ℝ ∙ ν)ᗮ.orthogonalProjectionOnto.contDiff.comp
    (contDiff_id.sub contDiff_const)))

variable (G : LipschitzGraph V)

/-- The graph function of a Lipschitz graph domain seen from the point `z`:
`φ_z(y) = φ(z + y) - ⟪z, e⟫` for `y` in the hyperplane `e^⊥`. -/
def localPhi (z : V) (y : G.hyperplane) : ℝ := G.phi (z + y) - inner ℝ z G.e

/-- The graph function seen from `z` is `M`-Lipschitz. -/
theorem lipschitzWith_localPhi (z : V) : LipschitzWith ⟨G.M, G.M_nonneg⟩ (G.localPhi z) :=
  LipschitzWith.of_dist_le_mul fun y y' => by
    rw [Real.dist_eq, localPhi, localPhi, sub_sub_sub_cancel_right, Subtype.dist_eq,
      dist_eq_norm]
    have h := G.lipschitz (z + y) (z + y')
    rwa [add_sub_add_left_eq_sub] at h

/-- If the graph function `φ` is `C^n`, then so is the graph function seen from `z`,
`y ↦ φ(z + y) - ⟪z, e⟫`. -/
theorem contDiff_localPhi (z : V) {n : WithTop ℕ∞} (hG : ContDiff ℝ n G.phi) :
    ContDiff ℝ n (G.localPhi z) :=
  (hG.comp (contDiff_const.add G.hyperplane.subtypeL.contDiff)).sub contDiff_const

/-- **Every Lipschitz graph domain is a local graph around every point**:
`Ω = {x : φ_z(P(x - z)) < ⟪e, x - z⟫}`, since `φ(x) = φ(z + P(x - z))` by the constancy of `φ`
along `e`. -/
theorem domain_eq_localPhi (z : V) :
    G.domain = {x | G.localPhi z (G.proj (x - z)) < inner ℝ G.e (x - z)} := by
  ext x
  have hphi : G.phi (z + (G.proj (x - z) : V)) = G.phi x := by
    rw [G.coe_proj, ← G.const (z + (x - z - inner ℝ (x - z) G.e • G.e)) (inner ℝ (x - z) G.e)]
    congr 1
    abel
  change G.phi x < inner ℝ x G.e ↔ G.phi (z + _) - inner ℝ z G.e < inner ℝ G.e (x - z)
  rw [hphi, inner_sub_right, real_inner_comm G.e x, real_inner_comm G.e z]
  constructor <;> intro h <;> linarith

end LipschitzGraph

/-- **Agreeing with a Lipschitz graph domain on a ball** around `z` makes a set Lipschitz near `z`,
by `Rd.LipschitzGraph.domain_eq_localPhi`. -/
theorem isLipschitzDomainAt_of_ball_inter_eq {Ω : Set V} {z : V} {r : ℝ} (hr : 0 < r)
    (G : LipschitzGraph V) (h : ball z r ∩ Ω = ball z r ∩ G.domain) : IsLipschitzDomainAt Ω z := by
  refine ⟨r, hr, G.e, G.norm_e, ⟨G.M, G.M_nonneg⟩, G.localPhi z, G.lipschitzWith_localPhi z, ?_⟩
  rw [inter_comm, h, G.domain_eq_localPhi z, inter_comm]
  rfl

/-- **A set Lipschitz near `z` agrees with a Lipschitz graph domain on a ball** around `z`: the
graph domain of the local graph (`Rd.LipschitzGraph.ofLocal`). -/
theorem IsLipschitzDomainAt.exists_ball_inter_eq {Ω : Set V} {z : V}
    (h : IsLipschitzDomainAt Ω z) :
    ∃ r : ℝ, 0 < r ∧ ∃ G : LipschitzGraph V, ball z r ∩ Ω = ball z r ∩ G.domain := by
  obtain ⟨r, hr, ν, hν, L, φ, hφ, hΩ⟩ := h
  refine ⟨r, hr, LipschitzGraph.ofLocal z ν hν φ hφ, ?_⟩
  rw [LipschitzGraph.domain_ofLocal, inter_comm, hΩ, inter_comm]

/-- **Lipschitz near `z` means agreeing with a Lipschitz graph domain on a ball** around `z`. -/
theorem isLipschitzDomainAt_iff {Ω : Set V} {z : V} :
    IsLipschitzDomainAt Ω z ↔
      ∃ r : ℝ, 0 < r ∧ ∃ G : LipschitzGraph V, ball z r ∩ Ω = ball z r ∩ G.domain :=
  ⟨IsLipschitzDomainAt.exists_ball_inter_eq, fun ⟨_, hr, G, h⟩ =>
    isLipschitzDomainAt_of_ball_inter_eq hr G h⟩

/-- **Being Lipschitz near `z` depends only on the set near `z`**: if `Ω` and `Ω'` agree on a ball
`B(z, ρ)` with `ρ > 0` and `Ω'` is Lipschitz near `z`, then so is `Ω`, with the radius shrunk to
`min r ρ` (`Rd.isLipschitzDomainAt_iff`). -/
theorem IsLipschitzDomainAt.congr_ball {Ω Ω' : Set V} {z : V} {ρ : ℝ} (hρ : 0 < ρ)
    (h : ball z ρ ∩ Ω = ball z ρ ∩ Ω') (h' : IsLipschitzDomainAt Ω' z) :
    IsLipschitzDomainAt Ω z := by
  obtain ⟨r, hr, G, hG⟩ := h'.exists_ball_inter_eq
  have h1 : ball z (min r ρ) ∩ ball z ρ = ball z (min r ρ) :=
    inter_eq_left.2 (ball_subset_ball (min_le_right _ _))
  have h2 : ball z (min r ρ) ∩ ball z r = ball z (min r ρ) :=
    inter_eq_left.2 (ball_subset_ball (min_le_left _ _))
  refine isLipschitzDomainAt_of_ball_inter_eq (lt_min hr hρ) G ?_
  calc ball z (min r ρ) ∩ Ω = ball z (min r ρ) ∩ (ball z ρ ∩ Ω) := by rw [← inter_assoc, h1]
    _ = ball z (min r ρ) ∩ (ball z r ∩ Ω') := by rw [h, ← inter_assoc, h1, ← inter_assoc, h2]
    _ = ball z (min r ρ) ∩ G.domain := by rw [hG, ← inter_assoc, h2]

/-- **A local graph depends only on its function near the origin**: if `φ = ψ` on the ball of
radius `ρ` of `ν^⊥`, then the regions above the graphs of `φ` and `ψ` agree on `B(z, ρ)`, since
`‖P(x - z)‖ ≤ ‖x - z‖ < ρ` there (Mathlib's `Submodule.norm_orthogonalProjectionOnto_apply_le`). -/
theorem localGraph_inter_ball_eq_of_eqOn {z ν : V} {ρ : ℝ} {φ ψ : (ℝ ∙ ν)ᗮ → ℝ}
    (h : EqOn φ ψ (ball 0 ρ)) :
    {x | φ ((ℝ ∙ ν)ᗮ.orthogonalProjectionOnto (x - z)) < inner ℝ ν (x - z)} ∩ ball z ρ =
      {x | ψ ((ℝ ∙ ν)ᗮ.orthogonalProjectionOnto (x - z)) < inner ℝ ν (x - z)} ∩ ball z ρ := by
  ext x
  refine ⟨fun ⟨hx, hxb⟩ => ⟨?_, hxb⟩, fun ⟨hx, hxb⟩ => ⟨?_, hxb⟩⟩
  all_goals
    have hP : (ℝ ∙ ν)ᗮ.orthogonalProjectionOnto (x - z) ∈ ball (0 : (ℝ ∙ ν)ᗮ) ρ := by
      rw [mem_ball_zero_iff]
      exact (Submodule.norm_orthogonalProjectionOnto_apply_le _ _).trans_lt
        (by rwa [← dist_eq_norm, ← mem_ball])
  · change ψ _ < _
    rw [← h hP]
    exact hx
  · change φ _ < _
    rw [h hP]
    exact hx

/-- **A local graph that is Lipschitz only near the origin suffices**: if `φ` is `L`-Lipschitz on
the ball of radius `r` of `ν^⊥` (the image of `B(z, r)` under `x ↦ P(x - z)`) and
`Ω ∩ B(z, r) = {x : φ(P(x - z)) < ⟪ν, x - z⟫} ∩ B(z, r)`, then `Ω` is Lipschitz near `z`: McShane's
extension (Mathlib's `LipschitzOnWith.extend_real`) gives an `L`-Lipschitz function on `ν^⊥` that
agrees with `φ` on that ball (`Rd.localGraph_inter_ball_eq_of_eqOn`). -/
theorem isLipschitzDomainAt_of_lipschitzOnWith {Ω : Set V} {z ν : V} {r : ℝ} (hr : 0 < r)
    (hν : ‖ν‖ = 1) {L : ℝ≥0} {φ : (ℝ ∙ ν)ᗮ → ℝ} (hφ : LipschitzOnWith L φ (ball 0 r))
    (hΩ : Ω ∩ ball z r =
      {x | φ ((ℝ ∙ ν)ᗮ.orthogonalProjectionOnto (x - z)) < inner ℝ ν (x - z)} ∩ ball z r) :
    IsLipschitzDomainAt Ω z := by
  obtain ⟨ψ, hψ, heq⟩ := hφ.extend_real
  exact ⟨r, hr, ν, hν, L, ψ, hψ, by rw [hΩ, localGraph_inter_ball_eq_of_eqOn heq]⟩

/-! ### The constructor from a family of charts -/

section Charts

variable [FiniteDimensional ℝ V] {Ω : Set V}

/-- **Finitely many chart balls cover the frontier**: for a bounded set `Ω` and radii `r(z) > 0` at
its frontier points, finitely many of the balls `B(z, r(z))` cover the frontier, which is compact
in finite dimension (`Rd.isCompact_frontier_of_isBounded`, `IsCompact.elim_finite_subcover`). -/
theorem exists_finset_cover_frontier (hb : Bornology.IsBounded Ω) (r : frontier Ω → ℝ)
    (hr : ∀ z, 0 < r z) : ∃ t : Finset (frontier Ω), frontier Ω ⊆ ⋃ z ∈ t, ball (z : V) (r z) :=
  (isCompact_frontier_of_isBounded hb).elim_finite_subcover
    (fun z : frontier Ω => ball (z : V) (r z)) (fun _ => isOpen_ball)
    fun x hx => mem_iUnion.2 ⟨⟨x, hx⟩, mem_ball_self (hr _)⟩

/-- A chosen finite set of frontier points whose balls `B(z, r(z))` cover the frontier
(`Rd.exists_finset_cover_frontier`). -/
noncomputable def frontierCenters (hb : Bornology.IsBounded Ω) (r : frontier Ω → ℝ)
    (hr : ∀ z, 0 < r z) : Finset (frontier Ω) :=
  Classical.choose (exists_finset_cover_frontier hb r hr)

/-- The balls `B(z, r(z))` of the chosen centres cover the frontier. -/
theorem frontier_subset_frontierCenters (hb : Bornology.IsBounded Ω) (r : frontier Ω → ℝ)
    (hr : ∀ z, 0 < r z) : frontier Ω ⊆ ⋃ z ∈ frontierCenters hb r hr, ball (z : V) (r z) :=
  Classical.choose_spec (exists_finset_cover_frontier hb r hr)

/-- The `j`-th chosen centre, for the numbering `Fin N` of the chosen centres
(`Finset.equivFin`). -/
noncomputable def frontierCenterAt (hb : Bornology.IsBounded Ω) (r : frontier Ω → ℝ)
    (hr : ∀ z, 0 < r z) (j : Fin (frontierCenters hb r hr).card) : frontier Ω :=
  ((frontierCenters hb r hr).equivFin.symm j : frontier Ω)

/-- **The bounded Lipschitz domain of a family of charts**: let `Ω` be open and bounded, and let
each frontier point `z` carry a radius `r(z) > 0` and a Lipschitz graph domain `G(z)` that agrees
with `Ω` on `B(z, r(z))`. The charts at the finitely many chosen centres
(`Rd.frontierCenters`) form a `Rd.BoundedLipschitzDomain` with carrier `Ω`, and each of its graph
domains is one of the `G(z)` (`Rd.BoundedLipschitzDomain.exists_graph_ofCharts_eq`). -/
noncomputable def BoundedLipschitzDomain.ofCharts (ho : IsOpen Ω) (hb : Bornology.IsBounded Ω)
    (r : frontier Ω → ℝ) (hr : ∀ z, 0 < r z) (G : frontier Ω → LipschitzGraph V)
    (hG : ∀ z : frontier Ω, ball (z : V) (r z) ∩ Ω = ball (z : V) (r z) ∩ (G z).domain) :
    BoundedLipschitzDomain V where
  carrier := Ω
  isOpen := ho
  isBounded := hb
  N := (frontierCenters hb r hr).card
  center j := (frontierCenterAt hb r hr j : V)
  radius j := r (frontierCenterAt hb r hr j)
  radius_pos j := hr _
  center_mem j := (frontierCenterAt hb r hr j).2
  graph j := G (frontierCenterAt hb r hr j)
  frontier_subset x hx := by
    obtain ⟨z, hz, hxz⟩ := mem_iUnion₂.1 (frontier_subset_frontierCenters hb r hr hx)
    refine mem_iUnion.2 ⟨(frontierCenters hb r hr).equivFin ⟨z, hz⟩, ?_⟩
    simp only [frontierCenterAt, Equiv.symm_apply_apply]
    exact hxz
  ball_inter j := hG _

/-- The carrier of `Rd.BoundedLipschitzDomain.ofCharts` is `Ω`. -/
@[simp]
theorem BoundedLipschitzDomain.carrier_ofCharts (ho : IsOpen Ω) (hb : Bornology.IsBounded Ω)
    (r : frontier Ω → ℝ) (hr : ∀ z, 0 < r z) (G : frontier Ω → LipschitzGraph V)
    (hG : ∀ z : frontier Ω, ball (z : V) (r z) ∩ Ω = ball (z : V) (r z) ∩ (G z).domain) :
    (BoundedLipschitzDomain.ofCharts ho hb r hr G hG).carrier = Ω :=
  rfl

/-- **The graph domains of `Rd.BoundedLipschitzDomain.ofCharts` come from the family**: each is
`G(z)` for some frontier point `z`, so every property shared by all `G(z)`, such as smoothness
of the graph functions, passes to the bounded Lipschitz domain. -/
theorem BoundedLipschitzDomain.exists_graph_ofCharts_eq (ho : IsOpen Ω)
    (hb : Bornology.IsBounded Ω) (r : frontier Ω → ℝ) (hr : ∀ z, 0 < r z)
    (G : frontier Ω → LipschitzGraph V)
    (hG : ∀ z : frontier Ω, ball (z : V) (r z) ∩ Ω = ball (z : V) (r z) ∩ (G z).domain)
    (j : Fin (BoundedLipschitzDomain.ofCharts ho hb r hr G hG).N) :
    ∃ z, (BoundedLipschitzDomain.ofCharts ho hb r hr G hG).graph j = G z :=
  ⟨_, rfl⟩

end Charts

/-! ### The constructor from the set-level definition -/

namespace IsBoundedLipschitzDomain

variable {Ω : Set V}

/-- **A chart at each frontier point**: a radius `r > 0` and a Lipschitz graph domain that agrees
with `Ω` on `B(z, r)` (`Rd.IsLipschitzDomainAt.exists_ball_inter_eq`). -/
theorem exists_chart (h : IsBoundedLipschitzDomain Ω) (z : frontier Ω) :
    ∃ q : ℝ × LipschitzGraph V, 0 < q.1 ∧ ball (z : V) q.1 ∩ Ω = ball (z : V) q.1 ∩ q.2.domain := by
  obtain ⟨r, hr, G, hG⟩ := (h.2.2 z z.2).exists_ball_inter_eq
  exact ⟨(r, G), hr, hG⟩

/-- A chosen chart at the frontier point `z`: its radius and its Lipschitz graph domain. -/
noncomputable def chart (h : IsBoundedLipschitzDomain Ω) (z : frontier Ω) : ℝ × LipschitzGraph V :=
  Classical.choose (h.exists_chart z)

/-- The radius of the chosen chart is positive. -/
theorem chart_fst_pos (h : IsBoundedLipschitzDomain Ω) (z : frontier Ω) : 0 < (h.chart z).1 :=
  (Classical.choose_spec (h.exists_chart z)).1

/-- On the ball of the chosen chart, `Ω` is its Lipschitz graph domain. -/
theorem ball_inter_chart (h : IsBoundedLipschitzDomain Ω) (z : frontier Ω) :
    ball (z : V) (h.chart z).1 ∩ Ω = ball (z : V) (h.chart z).1 ∩ (h.chart z).2.domain :=
  (Classical.choose_spec (h.exists_chart z)).2

end IsBoundedLipschitzDomain

namespace BoundedLipschitzDomain

variable [FiniteDimensional ℝ V] {Ω : Set V}

/-- **The bounded Lipschitz domain of a bounded Lipschitz set**: the chosen charts at the frontier
points (`Rd.IsBoundedLipschitzDomain.chart`) form a family of charts, and
`Rd.BoundedLipschitzDomain.ofCharts` gives a `Rd.BoundedLipschitzDomain` with carrier `Ω`. -/
noncomputable def ofIsBoundedLipschitzDomain (h : IsBoundedLipschitzDomain Ω) :
    BoundedLipschitzDomain V :=
  ofCharts h.1 h.2.1 (fun z => (h.chart z).1) h.chart_fst_pos (fun z => (h.chart z).2)
    h.ball_inter_chart

/-- The carrier of `Rd.BoundedLipschitzDomain.ofIsBoundedLipschitzDomain h` is `Ω`. -/
@[simp]
theorem carrier_ofIsBoundedLipschitzDomain (h : IsBoundedLipschitzDomain Ω) :
    (ofIsBoundedLipschitzDomain h).carrier = Ω :=
  rfl

omit [FiniteDimensional ℝ V] in
/-- **A bounded Lipschitz domain is a graph domain near each frontier point**: a frontier point `z`
lies in some chart ball `B(c_j, ρ_j)`, the smaller ball `B(z, ρ_j - ‖z - c_j‖)` lies inside it,
and there the domain is the graph domain `Ω_j`. -/
theorem exists_ball_inter_eq_graph (D : BoundedLipschitzDomain V) {z : V}
    (hz : z ∈ frontier D.carrier) :
    ∃ j : Fin D.N, ∃ ρ : ℝ, 0 < ρ ∧ ball z ρ ∩ D.carrier = ball z ρ ∩ (D.graph j).domain := by
  obtain ⟨j, hj⟩ := mem_iUnion.1 (D.frontier_subset hz)
  have hr : 0 < D.radius j - dist z (D.center j) := sub_pos.2 hj
  have hsub : ball z (D.radius j - dist z (D.center j)) ⊆ ball (D.center j) (D.radius j) :=
    ball_subset_ball' (by linarith)
  refine ⟨j, _, hr, ?_⟩
  rw [← inter_eq_left.2 hsub, inter_assoc, D.ball_inter j, ← inter_assoc]

omit [FiniteDimensional ℝ V] in
/-- **A bounded Lipschitz domain is Lipschitz near each frontier point**, by
`Rd.BoundedLipschitzDomain.exists_ball_inter_eq_graph`. -/
theorem isLipschitzDomainAt (D : BoundedLipschitzDomain V) {z : V}
    (hz : z ∈ frontier D.carrier) : IsLipschitzDomainAt D.carrier z := by
  obtain ⟨j, ρ, hρ, h⟩ := D.exists_ball_inter_eq_graph hz
  exact isLipschitzDomainAt_of_ball_inter_eq hρ (D.graph j) h

omit [FiniteDimensional ℝ V] in
/-- **The carrier of a bounded Lipschitz domain is a bounded Lipschitz set.** -/
theorem isBoundedLipschitzDomain (D : BoundedLipschitzDomain V) :
    IsBoundedLipschitzDomain D.carrier :=
  ⟨D.isOpen, D.isBounded, fun _ hz => D.isLipschitzDomainAt hz⟩

end BoundedLipschitzDomain

/-- **The set-level definition and the structure agree**: in finite dimension a set is a bounded
Lipschitz set iff it is the carrier of some `Rd.BoundedLipschitzDomain`. -/
theorem isBoundedLipschitzDomain_iff_exists [FiniteDimensional ℝ V] {Ω : Set V} :
    IsBoundedLipschitzDomain Ω ↔ ∃ D : BoundedLipschitzDomain V, D.carrier = Ω :=
  ⟨fun h => ⟨BoundedLipschitzDomain.ofIsBoundedLipschitzDomain h, rfl⟩,
    fun ⟨D, hD⟩ => hD ▸ D.isBoundedLipschitzDomain⟩

/-! ### The ball -/

/-- The **sphere profile**, the profile of the sphere of radius `R` seen from one of its points:
`g_R(s) = R - √(R² - min(s, R/2)²)`. Near a point `z` of the sphere `‖x - c‖ = R`, the ball is the
region above the graph of `y ↦ g_R(‖y‖)` over the tangent hyperplane. -/
noncomputable def sphereProfile (R s : ℝ) : ℝ := R - Real.sqrt (R ^ 2 - min s (R / 2) ^ 2)

/-- For `R > 0`, on `[0, R/2]` the function `s ↦ √(R² - s²)` is `1`-Lipschitz: with `a, b` the two
square roots, `a, b ≥ R/2` and `|a - b| (a + b) = |s₁ - s₂| (s₁ + s₂) ≤ R |s₁ - s₂|`; dividing by
`a + b ≥ R` gives the bound (the argument of the `quadratic-forms-sobolev-lean` project). -/
theorem abs_sqrt_sq_sub_sq_sub_le {R s₁ s₂ : ℝ} (hR : 0 < R) (h₁ : 0 ≤ s₁) (h₁' : s₁ ≤ R / 2)
    (h₂ : 0 ≤ s₂) (h₂' : s₂ ≤ R / 2) :
    |Real.sqrt (R ^ 2 - s₁ ^ 2) - Real.sqrt (R ^ 2 - s₂ ^ 2)| ≤ |s₁ - s₂| := by
  have ha : R / 2 ≤ Real.sqrt (R ^ 2 - s₁ ^ 2) := Real.le_sqrt_of_sq_le (by nlinarith)
  have hb : R / 2 ≤ Real.sqrt (R ^ 2 - s₂ ^ 2) := Real.le_sqrt_of_sq_le (by nlinarith)
  have ha2 : Real.sqrt (R ^ 2 - s₁ ^ 2) ^ 2 = R ^ 2 - s₁ ^ 2 := Real.sq_sqrt (by nlinarith)
  have hb2 : Real.sqrt (R ^ 2 - s₂ ^ 2) ^ 2 = R ^ 2 - s₂ ^ 2 := Real.sq_sqrt (by nlinarith)
  generalize Real.sqrt (R ^ 2 - s₁ ^ 2) = a at ha ha2 ⊢
  generalize Real.sqrt (R ^ 2 - s₂ ^ 2) = b at hb hb2 ⊢
  have hab : 0 < a + b := by linarith
  have key : |a - b| * (a + b) = |s₁ - s₂| * (s₁ + s₂) := by
    rw [← abs_of_pos hab, ← abs_mul,
      show (a - b) * (a + b) = -((s₁ - s₂) * (s₁ + s₂)) by linear_combination ha2 - hb2,
      abs_neg, abs_mul, abs_of_nonneg (by linarith : (0 : ℝ) ≤ s₁ + s₂)]
  by_contra hcon
  have hlt : |s₁ - s₂| < |a - b| := lt_of_not_ge hcon
  nlinarith [abs_nonneg (s₁ - s₂)]

/-- For `R > 0` the sphere profile is `1`-Lipschitz on `[0, ∞)`:
`|g_R(s₁) - g_R(s₂)| ≤ |s₁ - s₂|` for `s₁, s₂ ≥ 0`, by `Rd.abs_sqrt_sq_sub_sq_sub_le` and since
`s ↦ min(s, R/2)` is `1`-Lipschitz. -/
theorem abs_sphereProfile_sub_le {R s₁ s₂ : ℝ} (hR : 0 < R) (h₁ : 0 ≤ s₁) (h₂ : 0 ≤ s₂) :
    |sphereProfile R s₁ - sphereProfile R s₂| ≤ |s₁ - s₂| := by
  have h := abs_sqrt_sq_sub_sq_sub_le hR (le_min h₁ (by positivity)) (min_le_right _ _)
    (le_min h₂ (by positivity)) (min_le_right s₂ (R / 2))
  have hmin : |min s₁ (R / 2) - min s₂ (R / 2)| ≤ |s₁ - s₂| := by
    refine (abs_min_sub_min_le_max _ _ _ _).trans ?_
    rw [sub_self, abs_zero, max_eq_left (abs_nonneg _)]
  rw [sphereProfile, sphereProfile, sub_sub_sub_cancel_left, abs_sub_comm]
  exact h.trans hmin

/-- For `R > 0` and on any normed group, `y ↦ g_R(‖y‖)` is `1`-Lipschitz
(`Rd.abs_sphereProfile_sub_le` and the reverse triangle inequality). -/
theorem lipschitzWith_sphereProfile_norm {E : Type*} [SeminormedAddCommGroup E] {R : ℝ}
    (hR : 0 < R) : LipschitzWith 1 (fun y : E => sphereProfile R ‖y‖) :=
  LipschitzWith.of_dist_le_mul fun y y' => by
    rw [Real.dist_eq, NNReal.coe_one, one_mul, dist_eq_norm]
    exact (abs_sphereProfile_sub_le hR (norm_nonneg y) (norm_nonneg y')).trans
      (abs_norm_sub_norm_le y y')

/-- **The ball near a point of its sphere is the region above the profile**: let `‖ν‖ = 1`,
`c - z = R ν` and `‖x - z‖ < R/2`. Then `x ∈ B(c, R)` iff `g_R(‖P(x - z)‖) < ⟪ν, x - z⟫`, since
`‖x - c‖² = ‖P(x - z)‖² + (⟪ν, x - z⟫ - R)²`
(`Rd.norm_sub_smul_sq_eq_norm_orthogonalProjectionOnto_sq_add`) and both `‖P(x - z)‖ < R/2` and
`⟪ν, x - z⟫ < R/2`. -/
theorem mem_ball_iff_sphereProfile_lt {R : ℝ} (hR : 0 < R) {ν c z x : V} (hν : ‖ν‖ = 1)
    (hc : c - z = R • ν) (hxz : ‖x - z‖ < R / 2) :
    x ∈ ball c R ↔
      sphereProfile R ‖((ℝ ∙ ν)ᗮ.orthogonalProjectionOnto (x - z) : V)‖ < inner ℝ ν (x - z) := by
  have hxc : x - c = (x - z) - R • ν := by rw [← hc]; abel
  have hnx := norm_sub_smul_sq_eq_norm_orthogonalProjectionOnto_sq_add hν (x - z) R
  have hnw := norm_sub_smul_sq_eq_norm_orthogonalProjectionOnto_sq_add hν (x - z) 0
  rw [← hxc] at hnx
  rw [zero_smul, sub_zero, sub_zero] at hnw
  generalize ((ℝ ∙ ν)ᗮ.orthogonalProjectionOnto (x - z) : V) = p at hnx hnw ⊢
  generalize inner ℝ ν (x - z) = t at hnx hnw ⊢
  have hw2 : ‖x - z‖ ^ 2 < (R / 2) ^ 2 := pow_lt_pow_left₀ hxz (norm_nonneg _) two_ne_zero
  have hp : ‖p‖ < R / 2 := by nlinarith [norm_nonneg p, sq_nonneg t]
  have ht : t < R / 2 := by nlinarith [sq_nonneg ‖p‖, sq_nonneg (t - R / 2)]
  have hRt : 0 ≤ R - t := by linarith
  rw [sphereProfile, min_eq_left hp.le, mem_ball, dist_eq_norm, sub_lt_comm,
    Real.lt_sqrt hRt, ← sq_lt_sq₀ (norm_nonneg _) hR.le]
  constructor <;> intro h <;> nlinarith

/-- **The inward unit normal of a sphere**: for `R > 0` and a point `z` with `‖z - c‖ = R`, the
vector `(c - z)/R` has norm `1`. -/
theorem norm_inv_smul_sub_eq_one {c z : V} {R : ℝ} (hR : 0 < R) (hz : dist z c = R) :
    ‖R⁻¹ • (c - z)‖ = 1 := by
  rw [norm_smul, norm_inv, Real.norm_eq_abs, abs_of_pos hR, ← dist_eq_norm, dist_comm, hz,
    inv_mul_cancel₀ hR.ne']

/-- **The ball near a point of its sphere, as a set**: for `R > 0` and `‖z - c‖ = R`, with the
inward normal `ν = (c - z)/R`,
`B(c, R) ∩ B(z, R/2) = {x : g_R(‖P(x - z)‖) < ⟪ν, x - z⟫} ∩ B(z, R/2)`
(`Rd.mem_ball_iff_sphereProfile_lt`). -/
theorem inter_ball_eq_sphereProfile (c : V) {R : ℝ} (hR : 0 < R) {z : V} (hz : dist z c = R) :
    ball c R ∩ ball z (R / 2) =
      {x | sphereProfile R ‖((ℝ ∙ R⁻¹ • (c - z))ᗮ.orthogonalProjectionOnto (x - z) : V)‖ <
        inner ℝ (R⁻¹ • (c - z)) (x - z)} ∩ ball z (R / 2) := by
  have hνn := norm_inv_smul_sub_eq_one hR hz
  have hc : c - z = R • (R⁻¹ • (c - z)) := by rw [smul_smul, mul_inv_cancel₀ hR.ne', one_smul]
  ext x
  refine ⟨fun ⟨hx, hxb⟩ => ⟨?_, hxb⟩, fun ⟨hx, hxb⟩ => ⟨?_, hxb⟩⟩
  · exact (mem_ball_iff_sphereProfile_lt hR hνn hc (by rwa [← dist_eq_norm, ← mem_ball])).1 hx
  · exact (mem_ball_iff_sphereProfile_lt hR hνn hc (by rwa [← dist_eq_norm, ← mem_ball])).2 hx

/-- **The ball is Lipschitz near each point of its sphere**: at `z` with `‖z - c‖ = R`, with the
inward normal `ν = (c - z)/R`, radius `R/2` and the `1`-Lipschitz function
`y ↦ g_R(‖y‖)` (`Rd.inter_ball_eq_sphereProfile`). -/
theorem isLipschitzDomainAt_ball (c : V) {R : ℝ} (hR : 0 < R) {z : V} (hz : dist z c = R) :
    IsLipschitzDomainAt (ball c R) z :=
  ⟨R / 2, by positivity, R⁻¹ • (c - z), norm_inv_smul_sub_eq_one hR hz, 1,
    fun y => sphereProfile R ‖(y : V)‖, lipschitzWith_sphereProfile_norm hR,
    inter_ball_eq_sphereProfile c hR hz⟩

/-- **Every open ball is a bounded Lipschitz set**: for `R > 0` by `Rd.isLipschitzDomainAt_ball`
at the points of the sphere, which contains the frontier (Mathlib's
`Metric.frontier_ball_subset_sphere`); for `R ≤ 0` the ball is empty. -/
theorem isBoundedLipschitzDomain_ball (c : V) (R : ℝ) : IsBoundedLipschitzDomain (ball c R) := by
  rcases le_or_gt R 0 with hR | hR
  · rw [ball_eq_empty.2 hR]
    exact ⟨isOpen_empty, Bornology.isBounded_empty, fun _ hz => by simp at hz⟩
  · exact ⟨isOpen_ball, isBounded_ball, fun _ hz =>
      isLipschitzDomainAt_ball c hR (mem_sphere.1 (frontier_ball_subset_sphere hz))⟩

/-- **The ball as a bounded Lipschitz domain**: `B(c, R)`, from
`Rd.isBoundedLipschitzDomain_ball`. The name is protected, so that `ball` keeps meaning
`Metric.ball` inside the namespace `Rd.BoundedLipschitzDomain`. -/
protected noncomputable def BoundedLipschitzDomain.ball [FiniteDimensional ℝ V] (c : V) (R : ℝ) :
    BoundedLipschitzDomain V :=
  BoundedLipschitzDomain.ofIsBoundedLipschitzDomain (isBoundedLipschitzDomain_ball c R)

/-- The carrier of `Rd.BoundedLipschitzDomain.ball c R` is the ball `B(c, R)`. -/
@[simp]
theorem BoundedLipschitzDomain.carrier_ball [FiniteDimensional ℝ V] (c : V) (R : ℝ) :
    (BoundedLipschitzDomain.ball c R).carrier = ball c R :=
  rfl

end Rd
