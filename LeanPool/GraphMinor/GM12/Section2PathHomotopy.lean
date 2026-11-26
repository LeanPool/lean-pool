/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.Surface.Defs
public import Mathlib.Topology.Homotopy.Path
import LeanPool.GraphMinor.GM11.Section3
import Mathlib.AlgebraicTopology.FundamentalGroupoid.Basic
public import Mathlib.Topology.Subpath

/-!
# Cancelling the approach to an entry vertex

For XII's entry-edge definition, page 243, entry curves follow a common
approach to the vertex and then a radial spoke. A homotopy of the entry
curves therefore gives a homotopy of the spokes after cancelling the
common approach. The lemmas here also let the approach start at different
points: its earlier part stays in the open-disc region.
-/

public section

namespace GraphMinor.GM12

open Set Topology Surface

/-- The paper's relative-endpoint curve homotopy agrees with a path
homotopy in the subspace containing its image. -/
theorem paths_homotopic_of_curvesHomotopicIn {S : Type*} [TopologicalSpace S]
    {Z : Set S} {x y : Z} (p q : Path x y)
    (h : CurvesHomotopicIn Z
      ⟨fun t => (p t).val, continuous_subtype_val.comp p.continuous⟩
      ⟨fun t => (q t).val, continuous_subtype_val.comp q.continuous⟩) : p.Homotopic q := by
  obtain ⟨H, hZ, h0, h1, hleft, _, hright, _⟩ := h
  refine ⟨{
    toFun := fun z => ⟨H (z.2, z.1), hZ (z.2, z.1)⟩
    continuous_toFun := (H.continuous.comp (continuous_snd.prodMk continuous_fst)).subtype_mk _
    map_zero_left := fun t => Subtype.ext (h0 t)
    map_one_left := fun t => Subtype.ext (h1 t)
    prop' := ?_ }⟩
  intro t s hs
  rcases hs with rfl | hs
  · exact Subtype.ext (hleft t)
  · have hs1 : s = 1 := mem_singleton_iff.mp hs
    subst s
    exact Subtype.ext (hright t)

/-- Read a subspace path homotopy as the paper's relative-endpoint
homotopy of ambient curves. -/
theorem curvesHomotopicIn_of_paths_homotopic {S : Type*} [TopologicalSpace S]
    {Z : Set S} {x y : Z} {p q : Path x y} (h : p.Homotopic q) :
    CurvesHomotopicIn Z
      ⟨fun t => (p t).val, continuous_subtype_val.comp p.continuous⟩
      ⟨fun t => (q t).val, continuous_subtype_val.comp q.continuous⟩ := by
  obtain ⟨H⟩ := h
  refine ⟨⟨fun z => (H (z.2, z.1)).val,
    continuous_subtype_val.comp (H.continuous.comp (continuous_snd.prodMk continuous_fst))⟩,
    fun z => (H (z.2, z.1)).property, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro t
    exact congrArg Subtype.val (H.apply_zero t)
  · intro t
    exact congrArg Subtype.val (H.apply_one t)
  · intro t
    exact congrArg Subtype.val (H.eq_fst t (Or.inl rfl))
  · intro t
    exact congrArg Subtype.val (H.eq_snd t (Or.inl rfl))
  · intro t
    exact congrArg Subtype.val (H.eq_fst t (Or.inr (mem_singleton 1)))
  · intro t
    exact congrArg Subtype.val (H.eq_snd t (Or.inr (mem_singleton 1)))

/-- Path homotopies can be cancelled on the left. The inverse approach
followed by the approach contracts, leaving the two terminal paths. -/
theorem path_homotopic_cancel_left {X : Type*} [TopologicalSpace X] {a b c : X}
    (r : Path a b) (p q : Path b c) (h : (r.trans p).Homotopic (r.trans q)) :
    p.Homotopic q := by
  have reduce : ∀ s : Path b c, (r.symm.trans (r.trans s)).Homotopic s := by
    intro s
    exact (Path.Homotopic.trans_assoc r.symm r s).symm.trans
      (((Path.Homotopic.symm_trans r).hcomp (Path.Homotopic.refl s)).trans
        (Path.Homotopic.refl_trans s))
  exact (reduce p).symm.trans (((Path.Homotopic.refl r.symm).hcomp h).trans (reduce q))

/-- Paths contained in a simply-connected subset with the same ends are
homotopic in the ambient space. Lift both paths to the subset first. -/
theorem paths_homotopic_of_range_in_simplyConnected {X : Type*} [TopologicalSpace X]
    {R : Set X} (hR : IsSimplyConnectedSet R) {x y : X} (p q : Path x y)
    (hp : ∀ t, p t ∈ R) (hq : ∀ t, q t ∈ R) : p.Homotopic q := by
  have hx : x ∈ R := p.source ▸ hp 0
  have hy : y ∈ R := p.target ▸ hp 1
  let pR : Path (⟨x, hx⟩ : R) ⟨y, hy⟩ := {
    toFun := fun t => ⟨p t, hp t⟩
    continuous_toFun := p.continuous.subtype_mk _
    source' := Subtype.ext p.source
    target' := Subtype.ext p.target }
  let qR : Path (⟨x, hx⟩ : R) ⟨y, hy⟩ := {
    toFun := fun t => ⟨q t, hq t⟩
    continuous_toFun := q.continuous.subtype_mk _
    source' := Subtype.ext q.source
    target' := Subtype.ext q.target }
  have h := (hR.pathsHomotopic pR qR).map (⟨Subtype.val, continuous_subtype_val⟩ : C(R, X))
  exact h

/-- The normalized entry curves may start at different times along one
approach. If each is homotopic to a path in a simply-connected region,
their terminal spokes are homotopic. This is the common-approach step in
the omitted entry-edge uniqueness argument of XII, page 243. -/
theorem terminal_paths_homotopic_of_entries {X : Type*} [TopologicalSpace X]
    {R : Set X} (hR : IsSimplyConnectedSet R) {a b c : X} (F : Path a b)
    (hF : ∀ t : unitInterval, t < 1 → F t ∈ R)
    (p q : Path (F 1) c) {s t : unitInterval} (hs : s < 1) (ht : t < 1)
    (ρ : Path (F s) c) (σ : Path (F t) c)
    (hρ : ∀ u, ρ u ∈ R) (hσ : ∀ u, σ u ∈ R)
    (hp : ((F.subpath s 1).trans p).Homotopic ρ)
    (hq : ((F.subpath t 1).trans q).Homotopic σ) : p.Homotopic q := by
  have prepend : ∀ (u : unitInterval) (r : Path (F 1) c) (τ : Path (F u) c),
      ((F.subpath u 1).trans r).Homotopic τ →
      ((F.subpath 0 1).trans r).Homotopic ((F.subpath 0 u).trans τ) := by
    intro u r τ h
    exact ((Path.Homotopic.subpath_trans_subpath F 0 u 1).hcomp
      (Path.Homotopic.refl r)).symm.trans
      ((Path.Homotopic.trans_assoc _ _ _).trans ((Path.Homotopic.refl _).hcomp h))
  have initial : ∀ (u : unitInterval), u < 1 → ∀ z, (F.subpath 0 u) z ∈ R := by
    intro u hu z
    apply hF
    change Icc.convexComb 0 u z < 1
    apply lt_of_le_of_lt (show Icc.convexComb 0 u z ≤ u from ?_) hu
    change (1 - (z : ℝ)) * 0 + z * u ≤ u
    simp only [mul_zero, zero_add]
    exact mul_le_of_le_one_left u.property.1 z.property.2
  have hleft := prepend s p ρ hp
  have hright := prepend t q σ hq
  have hmiddle : ((F.subpath 0 s).trans ρ).Homotopic ((F.subpath 0 t).trans σ) := by
    apply paths_homotopic_of_range_in_simplyConnected hR
    · intro z
      rw [Path.trans_apply]
      split_ifs
      · exact initial s hs _
      · exact hρ _
    · intro z
      rw [Path.trans_apply]
      split_ifs
      · exact initial t ht _
      · exact hσ _
  exact path_homotopic_cancel_left _ p q (hleft.trans (hmiddle.trans hright.symm))

/-- Split a path at one time and read the two pieces with their original
endpoints. The concatenation is homotopic to the original path. -/
theorem split_path_homotopic {X : Type*} [TopologicalSpace X] {a b : X}
    (P : Path a b) (s : unitInterval) (α : Path a (P s)) (β : Path (P s) b)
    (hα : ∀ t, α t = (P.subpath 0 s) t)
    (hβ : ∀ t, β t = (P.subpath s 1) t) : (α.trans β).Homotopic P := by
  have h := (Path.Homotopic.subpath_trans_subpath P 0 s 1).pathCast
    P.source.symm P.target.symm
  have hleft : (((P.subpath 0 s).trans (P.subpath s 1)).cast
      P.source.symm P.target.symm) = α.trans β := by
    ext t
    change ((P.subpath 0 s).trans (P.subpath s 1)) t = (α.trans β) t
    simp only [Path.trans_apply]
    split_ifs
    · exact (hα _).symm
    · exact (hβ _).symm
  have hright : (P.subpath 0 1).cast P.source.symm P.target.symm = P := by
    ext t
    simp only [Path.subpath_zero_one, Path.cast_coe]
  rw [hleft, hright] at h
  exact h

/-- An open disc contained in a larger set is also an open disc in that
subspace. Its parametrization is unchanged, with the extra membership
proof attached to each point. -/
theorem openDisc_in_subspace {S : Type*} [TopologicalSpace S] {r Z : Set S}
    (hr : IsOpenDisc r) (hsub : r ⊆ Z) :
    IsOpenDisc ((Subtype.val : Z → S) ⁻¹' r) := by
  let R : Set Z := (Subtype.val : Z → S) ⁻¹' r
  let e : r ≃ₜ R := {
    toFun := fun x => ⟨⟨x.val, hsub x.property⟩, x.property⟩
    invFun := fun x => ⟨x.val.val, x.property⟩
    left_inv := fun _ => rfl
    right_inv := fun _ => rfl
    continuous_toFun := (continuous_subtype_val.subtype_mk _).subtype_mk _
    continuous_invFun := (continuous_subtype_val.comp continuous_subtype_val).subtype_mk _ }
  refine ⟨hr.1.preimage continuous_subtype_val, ?_⟩
  obtain ⟨f⟩ := hr.2
  exact ⟨f.trans e⟩

/-- An entry comparison at one point of the approach gives a comparison
at every earlier or later point before the vertex. Extend both comparisons
to the start of the approach and cancel that initial segment. -/
theorem terminal_entry_from_any_time {X : Type*} [TopologicalSpace X]
    {R : Set X} (hR : IsSimplyConnectedSet R) {a b c : X} (F : Path a b)
    (hF : ∀ u : unitInterval, u < 1 → F u ∈ R) (hc : c ∈ R)
    (p : Path (F 1) c) {s t : unitInterval} (hs : s < 1) (ht : t < 1)
    (ρ : Path (F s) c) (hρ : ∀ u, ρ u ∈ R)
    (hp : ((F.subpath s 1).trans p).Homotopic ρ) :
    ∃ σ : Path (F t) c, (∀ u, σ u ∈ R) ∧
      ((F.subpath t 1).trans p).Homotopic σ := by
  obtain ⟨σ, hσ⟩ := hR.1.joinedIn (F t) (hF t ht) c hc
  have initial : ∀ (u : unitInterval), u < 1 → ∀ z, (F.subpath 0 u) z ∈ R := by
    intro u hu z
    apply hF
    change Icc.convexComb 0 u z < 1
    apply lt_of_le_of_lt (show Icc.convexComb 0 u z ≤ u from ?_) hu
    change (1 - z.val) * 0 + z.val * u.val ≤ u.val
    simp only [mul_zero, zero_add]
    exact mul_le_of_le_one_left u.property.1 z.property.2
  have hfirst : ((F.subpath 0 1).trans p).Homotopic ((F.subpath 0 s).trans ρ) :=
    ((Path.Homotopic.subpath_trans_subpath F 0 s 1).hcomp
      (Path.Homotopic.refl p)).symm.trans
      ((Path.Homotopic.trans_assoc _ _ _).trans ((Path.Homotopic.refl _).hcomp hp))
  have hsecond : ((F.subpath 0 1).trans p).Homotopic
      ((F.subpath 0 t).trans ((F.subpath t 1).trans p)) :=
    ((Path.Homotopic.subpath_trans_subpath F 0 t 1).hcomp
      (Path.Homotopic.refl p)).symm.trans (Path.Homotopic.trans_assoc _ _ _)
  have hmiddle : ((F.subpath 0 s).trans ρ).Homotopic ((F.subpath 0 t).trans σ) := by
    apply paths_homotopic_of_range_in_simplyConnected hR
    · intro z
      rw [Path.trans_apply]
      split_ifs
      · exact initial s hs _
      · exact hρ _
    · intro z
      rw [Path.trans_apply]
      split_ifs
      · exact initial t ht _
      · exact hσ _
  exact ⟨σ, hσ, path_homotopic_cancel_left _ _ _
    (hsecond.symm.trans (hfirst.trans hmiddle))⟩

end GraphMinor.GM12
