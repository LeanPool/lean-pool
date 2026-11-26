/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.Surface.Defs
public import Mathlib.Analysis.SpecialFunctions.Complex.Circle

/-!
# Topological Circle, Circular Order, and Crossing Pairs

This file establishes the topological and combinatorial properties of the unit circle `Circle`
and of points ordered around a circle that are used in Graph Minors VI, Section 2–5:
- Open arcs on `Circle` (`Circle.openArc`) and the decomposition of `Circle \ {x, y}` for $x \ne y$
  into two disjoint open path-connected arcs (via `Circle.path` from
  `Mathlib.Analysis.SpecialFunctions.Complex.Circle`).
- Circular coordinate embeddings `CircleCoord` (with the canonical instance on `Circle` given by
  `Complex.arg : Circle → ℝ`), the betweenness relation `onOpenArc`, and the crossing relation
  `circleCrosses` ("$\{a, c\}$ crosses $\{b, d\}$", Graph Minors VI, Section 2, page 117).
- Symmetry, disjointness, non-crossing equivalence transitivity, and the four-point crossing
  lemma used in Graph Minors VI, (2.1)–(2.4).
-/

@[expose] public section

namespace GraphMinor.Surface

open Set Function Complex Real Topology

universe u

/-- An `O`-arc contains infinitely many points. -/
theorem IsOArc.infinite {S : Type u} [TopologicalSpace S] {F : Set S} (hF : IsOArc F) :
    F.Infinite := by
  obtain ⟨f⟩ := hF
  have hinj : InjOn (fun t => (f (Circle.exp t)).1) (Ico (0 : ℝ) (2 * Real.pi)) := by
    intro s hs t ht h
    exact Circle.exp_injOn_Ico (by simp) hs ht (f.injective (Subtype.ext h))
  refine ((Set.Ico_infinite Real.two_pi_pos).image hinj).mono ?_
  rintro _ ⟨t, _, rfl⟩
  exact (f (Circle.exp t)).2

/-! ## 1. Open Arcs on `Circle` -/

/-- The open counterclockwise arc on `Circle` from $x$ to $y$, defined as the image of $(0, 1)$
under `Circle.path x y`.
Route: `Circle.path` in `Mathlib.Analysis.SpecialFunctions.Complex.Circle`. -/
noncomputable def circleOpenArc (x y : Circle) : Set Circle :=
  Circle.path x y '' Ioo 0 1

/-- For $x \ne y$ on `Circle`, the two open arcs `circleOpenArc x y` and `circleOpenArc y x` are
disjoint.
Route: `Circle.disjoint_path_image_Ioc` from Mathlib. -/
theorem disjoint_circleOpenArc {x y : Circle} (h : x ≠ y) :
    Disjoint (circleOpenArc x y) (circleOpenArc y x) := by
  refine (Circle.disjoint_path_image_Ioc h).mono ?_ ?_ <;>
    exact image_mono Ioo_subset_Ioc_self

/-- For $x \ne y$ on `Circle`, the complement of the closed arc `range (Circle.path x y)` is
the reverse open arc `circleOpenArc y x`.
Route: `Circle.compl_range_path` from Mathlib. -/
theorem compl_range_circlePath {x y : Circle} (h : x ≠ y) :
    (range (Circle.path x y))ᶜ = circleOpenArc y x :=
  Circle.compl_range_path h

/-- For $x \ne y$ on `Circle`, `circleOpenArc x y` is open in `Circle`.
Route: its complement is the compact (hence closed) set `range (Circle.path y x)`. -/
theorem isOpen_circleOpenArc {x y : Circle} (h : x ≠ y) :
    IsOpen (circleOpenArc x y) := by
  rw [← compl_range_circlePath h.symm, isOpen_compl_iff]
  exact (isCompact_range (Circle.path y x).continuous).isClosed

/-- For $x \ne y$ on `Circle`, `circleOpenArc x y` is nonempty. -/
theorem nonempty_circleOpenArc {x y : Circle} (h : x ≠ y) :
    (circleOpenArc x y).Nonempty := by
  rw [← compl_range_circlePath h.symm, nonempty_compl]
  exact (Circle.range_path_ssubset_univ y x).ne

/-- For $x \ne y$ on `Circle`, `circleOpenArc x y` is path-connected.
Route: continuous image of the convex (hence path-connected) interval `Ioo (0 : unitInterval) 1`. -/
theorem isPathConnected_circleOpenArc (x y : Circle) :
    IsPathConnected (circleOpenArc x y) := by
  have hIoo : (Ioo (0 : unitInterval) 1).Nonempty := by
    refine ⟨⟨2⁻¹, by constructor <;> linarith⟩, ?_⟩
    simp only [mem_Ioo, ← unitInterval.coe_pos, ← unitInterval.coe_lt_one]
    constructor <;> linarith
  have hconv : Convex ℝ (Subtype.val '' (Ioo (0 : unitInterval) 1)) := by
    have heq : Subtype.val '' (Ioo (0 : unitInterval) 1) = Ioo (0 : ℝ) 1 := by
      ext r
      simp only [mem_image, mem_Ioo, Subtype.exists]
      exact ⟨fun ⟨a, ⟨h0, h1⟩, ⟨ha0, ha1⟩, hr⟩ => hr ▸ ⟨ha0, ha1⟩,
        fun ⟨hr0, hr1⟩ => ⟨r, ⟨hr0.le, hr1.le⟩, ⟨hr0, hr1⟩, rfl⟩⟩
    rw [heq]
    exact convex_Ioo 0 1
  have hpc : IsPathConnected (Ioo (0 : unitInterval) 1) := by
    rw [IsInducing.subtypeVal.isPathConnected_iff]
    exact hconv.isPathConnected (hIoo.image _)
  exact hpc.image (Circle.path x y).continuous

/-- For $x \ne y$ on `Circle`, `({x, y} : Set Circle)ᶜ` is the union of `circleOpenArc x y` and
`circleOpenArc y x`.
Route: `Circle.compl_range_path` and `Circle.range_path_inter_range_path` from Mathlib. -/
theorem compl_pair_eq_union_circleOpenArc {x y : Circle} (h : x ≠ y) :
    ({x, y} : Set Circle)ᶜ = circleOpenArc x y ∪ circleOpenArc y x := by
  rw [← Circle.range_path_inter_range_path h, compl_inter,
    compl_range_circlePath h, compl_range_circlePath h.symm, union_comm]

/-! ## 2. Circular Coordinates and Crossing Pairs on a Circle -/

/-- A circular coordinate on a type $C$ is an injective map $\alpha \colon C \to \mathbb{R}$,
representing the angular order on $C \setminus \{c_0\}$ (or `Complex.arg` on `Circle`). -/
structure CircleCoord (C : Type u) where
  /-- The injective coordinate map into $\mathbb{R}$. -/
  angle : C → ℝ
  /-- Distinct points of $C$ have distinct coordinates. -/
  injective : Injective angle

/-- The canonical `CircleCoord` on `Circle` given by `Complex.arg : Circle → (-π, π]`.
Route: `Circle.injective_arg` from `Mathlib.Analysis.SpecialFunctions.Complex.Circle`. -/
noncomputable def circleStdCoord : CircleCoord Circle where
  angle z := arg (z : ℂ)
  injective := Circle.injective_arg

/-- Transfer a `CircleCoord` along an equivalence $e \colon C' \simeq C$. -/
def CircleCoord.comap {C C' : Type*} (coord : CircleCoord C) (e : C' ≃ C) : CircleCoord C' where
  angle x := coord.angle (e x)
  injective := coord.injective.comp e.injective

/-- Given a `CircleCoord` $\alpha$ on $C$, a point $x \in C$ lies on the open coordinate arc
between $a$ and $c$ if $\min(\alpha(a), \alpha(c)) < \alpha(x) < \max(\alpha(a), \alpha(c))$. -/
def onOpenArc {C : Type u} (coord : CircleCoord C) (a c x : C) : Prop :=
  min (coord.angle a) (coord.angle c) < coord.angle x ∧
    coord.angle x < max (coord.angle a) (coord.angle c)

noncomputable instance {C : Type u} (coord : CircleCoord C) (a c x : C) :
    Decidable (onOpenArc coord a c x) := by
  unfold onOpenArc
  infer_instance

theorem onOpenArc_comm {C : Type u} (coord : CircleCoord C) (a c x : C) :
    onOpenArc coord a c x ↔ onOpenArc coord c a x := by
  simp [onOpenArc, min_comm, max_comm]

theorem not_onOpenArc_left {C : Type u} (coord : CircleCoord C) (a c : C) :
    ¬ onOpenArc coord a c a := by
  intro ⟨h1, h2⟩
  rcases le_total (coord.angle a) (coord.angle c) with hac | hca
  · rw [min_eq_left hac] at h1
    exact lt_irrefl _ h1
  · rw [max_eq_left hca] at h2
    exact lt_irrefl _ h2

theorem not_onOpenArc_right {C : Type u} (coord : CircleCoord C) (a c : C) :
    ¬ onOpenArc coord a c c := by
  rw [onOpenArc_comm]
  exact not_onOpenArc_left coord c a

theorem not_onOpenArc_self {C : Type u} (coord : CircleCoord C) (a x : C) :
    ¬ onOpenArc coord a a x := by
  intro ⟨h1, h2⟩
  rw [min_self] at h1
  rw [max_self] at h2
  exact lt_irrefl _ (h1.trans h2)

/-- Four points $a, b, c, d \in C$ satisfy '$\{a, c\}$ *crosses* $\{b, d\}$' if $a, b, c, d$ are
all distinct and $b, d$ lie in different components of $C \setminus \{a, c\}$ (one lies in the
open arc between $a$ and $c$, and the other lies outside).
Graph Minors VI, Section 2 (page 117): "If $a, b, c, d$ are distinct points of $C$ occurring in
that order, we say that $\{a, c\}$ *crosses* $\{b, d\}$." -/
def circleCrosses {C : Type u} (coord : CircleCoord C) (a c b d : C) : Prop :=
  a ≠ c ∧ b ≠ d ∧ a ≠ b ∧ a ≠ d ∧ c ≠ b ∧ c ≠ d ∧
    (onOpenArc coord a c b ↔ ¬ onOpenArc coord a c d)

noncomputable instance {C : Type u} [DecidableEq C] (coord : CircleCoord C) (a c b d : C) :
    Decidable (circleCrosses coord a c b d) := by
  unfold circleCrosses
  infer_instance

theorem circleCrosses_symm_left {C : Type u} (coord : CircleCoord C) (a c b d : C) :
    circleCrosses coord a c b d ↔ circleCrosses coord c a b d := by
  simp only [circleCrosses, ne_comm (a := a) (b := c), onOpenArc_comm coord a c]
  tauto

theorem circleCrosses_symm_right {C : Type u} (coord : CircleCoord C) (a c b d : C) :
    circleCrosses coord a c b d ↔ circleCrosses coord a c d b := by
  simp only [circleCrosses, ne_comm (a := b) (b := d)]
  constructor <;> rintro ⟨h1, h2, h3, h4, h5, h6, h7⟩ <;>
    refine ⟨h1, h2, ?_, ?_, ?_, ?_, ?_⟩ <;> tauto

private lemma onOpenArc_iff_lt {C : Type u} (coord : CircleCoord C) {a c x : C} :
    onOpenArc coord a c x ↔
      (coord.angle a < coord.angle x ∧ coord.angle x < coord.angle c) ∨
      (coord.angle c < coord.angle x ∧ coord.angle x < coord.angle a) := by
  unfold onOpenArc
  rcases le_total (coord.angle a) (coord.angle c) with hac | hca
  · rw [min_eq_left hac, max_eq_right hac]
    constructor
    · intro ⟨h1, h2⟩; exact Or.inl ⟨h1, h2⟩
    · rintro (⟨h1, h2⟩ | ⟨h1, h2⟩)
      · exact ⟨h1, h2⟩
      · exact absurd (h1.trans h2) (not_lt_of_ge hac)
  · rw [min_eq_right hca, max_eq_left hca]
    constructor
    · intro ⟨h1, h2⟩; exact Or.inr ⟨h1, h2⟩
    · rintro (⟨h1, h2⟩ | ⟨h1, h2⟩)
      · exact absurd (h1.trans h2) (not_lt_of_ge hca)
      · exact ⟨h1, h2⟩

/-- Crossing on a circle is symmetric between the two pairs: $\{a, c\}$ crosses $\{b, d\}$ if and
only if $\{b, d\}$ crosses $\{a, c\}$.
Graph Minors VI, Section 2 (page 117). -/
theorem circleCrosses_comm {C : Type u} (coord : CircleCoord C) (a c b d : C) :
    circleCrosses coord a c b d ↔ circleCrosses coord b d a c := by
  suffices ∀ a c b d : C, circleCrosses coord a c b d → circleCrosses coord b d a c by
    exact ⟨this a c b d, this b d a c⟩
  intro a c b d ⟨hac, hbd, hab, had, hcb, hcd, hcross⟩
  refine ⟨hbd, hac, hab.symm, hcb.symm, had.symm, hcd.symm, ?_⟩
  have ha_ne_c : coord.angle a ≠ coord.angle c := coord.injective.ne hac
  have hb_ne_d : coord.angle b ≠ coord.angle d := coord.injective.ne hbd
  have ha_ne_b : coord.angle a ≠ coord.angle b := coord.injective.ne hab
  have ha_ne_d : coord.angle a ≠ coord.angle d := coord.injective.ne had
  have hc_ne_b : coord.angle c ≠ coord.angle b := coord.injective.ne hcb
  have hc_ne_d : coord.angle c ≠ coord.angle d := coord.injective.ne hcd
  simp only [onOpenArc_iff_lt] at hcross ⊢
  rcases lt_or_gt_of_ne ha_ne_c with hac' | hca' <;>
  rcases lt_or_gt_of_ne hb_ne_d with hbd' | hdb' <;>
  rcases lt_or_gt_of_ne ha_ne_b with hab' | hba' <;>
  rcases lt_or_gt_of_ne ha_ne_d with had' | hda' <;>
  rcases lt_or_gt_of_ne hc_ne_b with hcb' | hbc' <;>
  rcases lt_or_gt_of_ne hc_ne_d with hcd' | hdc' <;>
  grind

/-- If $v_1, v_2$ are disjoint from $\{u_1, u_2, u_3\}$, and $\{v_1, v_2\}$ crosses neither
$\{u_1, u_2\}$ nor $\{u_2, u_3\}$, then $\{v_1, v_2\}$ does not cross $\{u_1, u_3\}$.
This is the transitivity of the equivalence relation defining $\Delta^*$ in Graph Minors VI,
Section 2 (page 117). -/
theorem not_circleCrosses_trans {C : Type u} (coord : CircleCoord C)
    {v₁ v₂ u₁ u₂ u₃ : C}
    (hv₁u₂ : v₁ ≠ u₂) (hv₂u₂ : v₂ ≠ u₂)
    (h12 : ¬ circleCrosses coord v₁ v₂ u₁ u₂)
    (h23 : ¬ circleCrosses coord v₁ v₂ u₂ u₃) :
    ¬ circleCrosses coord v₁ v₂ u₁ u₃ := by
  intro ⟨hv, hu13, hv1u1, hv1u3, hv2u1, hv2u3, hcross13⟩
  rcases eq_or_ne u₁ u₂ with rfl | hu12
  · exact h23 ⟨hv, hu13, hv1u1, hv1u3, hv2u1, hv2u3, hcross13⟩
  rcases eq_or_ne u₂ u₃ with rfl | hu23
  · exact h12 ⟨hv, hu13, hv1u1, hv1u3, hv2u1, hv2u3, hcross13⟩
  have h12' : ¬ (onOpenArc coord v₁ v₂ u₁ ↔ ¬ onOpenArc coord v₁ v₂ u₂) := fun h =>
    h12 ⟨hv, hu12, hv1u1, hv₁u₂, hv2u1, hv₂u₂, h⟩
  have h23' : ¬ (onOpenArc coord v₁ v₂ u₂ ↔ ¬ onOpenArc coord v₁ v₂ u₃) := fun h =>
    h23 ⟨hv, hu23, hv₁u₂, hv1u3, hv₂u₂, hv2u3, h⟩
  tauto

/-- Four-point crossing lemma on a circle: if $\{u_1, u_3\}$ crosses $\{u_2, u_4\}$ and
$\{v_1, v_2\}$ crosses $\{u_1, u_2\}$ with $\{v_1, v_2\} \cap \{u_1, u_2, u_3, u_4\} = \emptyset$,
then $\{v_1, v_2\}$ must cross either $\{u_1, u_3\}$ or $\{u_2, u_4\}$.
Graph Minors VI, Section 2, proof of (2.1) (page 117): "But $\{v_1, v_2\}$ crosses neither
$\{u_1, u_3\}$ nor $\{u_2, u_4\}$, and that is impossible." -/
theorem four_point_circleCrosses {C : Type u} (coord : CircleCoord C)
    {u₁ u₂ u₃ u₄ v₁ v₂ : C}
    (hu : circleCrosses coord u₁ u₃ u₂ u₄)
    (hv12 : circleCrosses coord v₁ v₂ u₁ u₂)
    (hv1u3 : v₁ ≠ u₃) (hv2u3 : v₂ ≠ u₃)
    (hv1u4 : v₁ ≠ u₄) (hv2u4 : v₂ ≠ u₄) :
    circleCrosses coord v₁ v₂ u₁ u₃ ∨ circleCrosses coord v₁ v₂ u₂ u₄ := by
  by_contra! h
  rcases h with ⟨h13, h24⟩
  rcases hu with ⟨hu13, hu24, hu12, hu14, hu32, hu34, hucross⟩
  rcases hv12 with ⟨hv, _, hv1u1, hv1u2, hv2u1, hv2u2, hvcross12⟩
  have hnc13 : ¬ (onOpenArc coord v₁ v₂ u₁ ↔ ¬ onOpenArc coord v₁ v₂ u₃) := fun hc =>
    h13 ⟨hv, hu13, hv1u1, hv1u3, hv2u1, hv2u3, hc⟩
  have hnc24 : ¬ (onOpenArc coord v₁ v₂ u₂ ↔ ¬ onOpenArc coord v₁ v₂ u₄) := fun hc =>
    h24 ⟨hv, hu24, hv1u2, hv1u4, hv2u2, hv2u4, hc⟩
  have hsame13 : onOpenArc coord v₁ v₂ u₁ ↔ onOpenArc coord v₁ v₂ u₃ := by tauto
  have hsame24 : onOpenArc coord v₁ v₂ u₂ ↔ onOpenArc coord v₁ v₂ u₄ := by tauto
  simp only [onOpenArc_iff_lt] at hucross hvcross12 hsame13 hsame24
  have hv_ne : coord.angle v₁ ≠ coord.angle v₂ := coord.injective.ne hv
  have hu1_ne_u3 : coord.angle u₁ ≠ coord.angle u₃ := coord.injective.ne hu13
  have hu2_ne_u4 : coord.angle u₂ ≠ coord.angle u₄ := coord.injective.ne hu24
  rcases lt_or_gt_of_ne hv_ne with hv' | hv' <;>
  rcases lt_or_gt_of_ne hu1_ne_u3 with hu13' | hu31' <;>
  rcases lt_or_gt_of_ne hu2_ne_u4 with hu24' | hu42' <;>
  grind

/-! ## 3. Topological Characterization of Circle Arcs and Crossing via `angleDiff` -/

/-- If $F = A \cup B$ is the union of two disjoint open preconnected subsets $A, B \subseteq X$,
then for every $z \in A$, the connected component of $F$ containing $z$ is $A$.
Route: $A$ is preconnected in $F$ and clopen in $F$. -/
theorem connectedComponentIn_eq_left_of_union_disjoint_open {X : Type*} [TopologicalSpace X]
    {A B : Set X} (hA_open : IsOpen A) (hB_open : IsOpen B)
    (hdisj : Disjoint A B) (hA_conn : IsPreconnected A) {z : X} (hz : z ∈ A) :
    connectedComponentIn (A ∪ B) z = A := by
  apply Subset.antisymm
  · have hcc_conn : IsPreconnected (connectedComponentIn (A ∪ B) z) :=
      isPreconnected_connectedComponentIn
    have hcc_sub : connectedComponentIn (A ∪ B) z ⊆ A ∪ B :=
      connectedComponentIn_subset (A ∪ B) z
    have hz_cc : z ∈ connectedComponentIn (A ∪ B) z :=
      mem_connectedComponentIn (Or.inl hz)
    by_contra hnot
    obtain ⟨w, hw_cc, hw_notA⟩ := not_subset.mp hnot
    have hw_B : w ∈ B := (hcc_sub hw_cc).resolve_left hw_notA
    rcases hcc_conn A B hA_open hB_open hcc_sub ⟨z, hz_cc, hz⟩ ⟨w, hw_cc, hw_B⟩ with
      ⟨u, _, huA, huB⟩
    exact hdisj.ne_of_mem huA huB rfl
  · exact hA_conn.subset_connectedComponentIn hz subset_union_left

/-- For $x \ne y$ on `Circle` and $z \in \operatorname{circleOpenArc} x y$, the connected component
of `({x, y} : Set Circle)ᶜ` containing $z$ is `circleOpenArc x y`. -/
theorem connectedComponentIn_compl_pair_eq_left {x y z : Circle} (hxy : x ≠ y)
    (hz : z ∈ circleOpenArc x y) :
    connectedComponentIn ({x, y} : Set Circle)ᶜ z = circleOpenArc x y := by
  rw [compl_pair_eq_union_circleOpenArc hxy]
  exact connectedComponentIn_eq_left_of_union_disjoint_open
    (isOpen_circleOpenArc hxy) (isOpen_circleOpenArc hxy.symm)
    (disjoint_circleOpenArc hxy) (isPathConnected_circleOpenArc x y).isConnected.isPreconnected hz

/-- For $x \ne y$ on `Circle` and $z \in \operatorname{circleOpenArc} y x$, the connected component
of `({x, y} : Set Circle)ᶜ` containing $z$ is `circleOpenArc y x`. -/
theorem connectedComponentIn_compl_pair_eq_right {x y z : Circle} (hxy : x ≠ y)
    (hz : z ∈ circleOpenArc y x) :
    connectedComponentIn ({x, y} : Set Circle)ᶜ z = circleOpenArc y x := by
  have heq : ({x, y} : Set Circle) = {y, x} := pair_comm x y
  rw [heq]
  exact connectedComponentIn_compl_pair_eq_left hxy.symm hz

/-- For any basepoint $c \in \text{Circle}$, `Circle.angleDiff c : Circle → [0, 2π)` is injective
and defines a circular coordinate `circleCoordFrom c`.
Route: `Circle.exp_angleDiff_mul`. -/
noncomputable def circleCoordFrom (c : Circle) : CircleCoord Circle where
  angle z := c.angleDiff z
  injective z₁ z₂ h := by
    have h1 := congrArg (fun θ => Circle.exp θ * c) h
    simpa only [Circle.exp_angleDiff_mul] using h1

@[simp]
theorem circleCoordFrom_self (c : Circle) : (circleCoordFrom c).angle c = 0 := by
  change c.angleDiff c = 0
  simp [Circle.angleDiff]

theorem circleCoordFrom_pos {c z : Circle} (h : c ≠ z) :
    0 < (circleCoordFrom c).angle z :=
  Circle.angleDiff_pos h

theorem circleCoordFrom_lt_two_pi (c z : Circle) :
    (circleCoordFrom c).angle z < 2 * π :=
  Circle.angleDiff_lt_two_pi c z

/-- A point $z \in \text{Circle}$ lies in the open counterclockwise arc `circleOpenArc x y`
($x \ne y$) if and only if $0 < x.\operatorname{angleDiff}(z) < x.\operatorname{angleDiff}(y)$.
Route: explicit affine parameter $t = x.\operatorname{angleDiff}(z) / x.\operatorname{angleDiff}(y)$
along `Circle.path x y` combined with `disjoint_circleOpenArc`. -/
theorem mem_circleOpenArc_iff_angleDiff {x y z : Circle} (hxy : x ≠ y) :
    z ∈ circleOpenArc x y ↔ 0 < x.angleDiff z ∧ x.angleDiff z < x.angleDiff y := by
  have haux : ∀ {a b w : Circle} (hab : a ≠ b),
      0 < a.angleDiff w → a.angleDiff w < a.angleDiff b → w ∈ circleOpenArc a b := by
    intro a b w hab hpos hlt
    have hab_pos : 0 < a.angleDiff b := Circle.angleDiff_pos hab
    let t_real : ℝ := a.angleDiff w / a.angleDiff b
    have ht0 : 0 < t_real := div_pos hpos hab_pos
    have ht1 : t_real < 1 := (div_lt_one hab_pos).mpr hlt
    let t : unitInterval := ⟨t_real, ht0.le, ht1.le⟩
    refine ⟨t, ⟨unitInterval.coe_pos.mp ht0, unitInterval.coe_lt_one.mp ht1⟩, ?_⟩
    rw [Circle.path_apply]
    have hseg : Path.segment a.val.arg (a.angleDiff b + a.val.arg) t =
        a.angleDiff w + a.val.arg := by
      simp only [Path.segment, Path.coe_mk_mk, AffineMap.lineMap_apply,
        vsub_eq_sub, smul_eq_mul, vadd_eq_add]
      have hmul : (t : ℝ) * a.angleDiff b = a.angleDiff w := div_mul_cancel₀ _ hab_pos.ne'
      linarith
    rw [hseg, Circle.exp_add, Circle.exp_arg, Circle.exp_angleDiff_mul]
  constructor
  · intro hz
    have hzx : x ≠ z := by
      rintro rfl
      have hnot : x ∉ circleOpenArc x y := by
        rw [← compl_range_circlePath hxy.symm, mem_compl_iff, not_not]
        exact (Circle.path y x).target_mem_range
      exact hnot hz
    have hzy : y ≠ z := by
      rintro rfl
      have hnot : y ∉ circleOpenArc x y := by
        rw [← compl_range_circlePath hxy.symm, mem_compl_iff, not_not]
        exact (Circle.path y x).source_mem_range
      exact hnot hz
    refine ⟨Circle.angleDiff_pos hzx, ?_⟩
    by_contra! hle
    have hlt : x.angleDiff y < x.angleDiff z :=
      lt_of_le_of_ne hle ((circleCoordFrom x).injective.ne hzy)
    have hyz_pos : 0 < y.angleDiff z := Circle.angleDiff_pos hzy
    have hyz_lt : y.angleDiff z < y.angleDiff x := by
      grind [Circle.angleDiff, Circle.arg_eq_arg,
        Complex.neg_pi_lt_arg x.val, Complex.arg_le_pi x.val,
        Complex.neg_pi_lt_arg y.val, Complex.arg_le_pi y.val,
        Complex.neg_pi_lt_arg z.val, Complex.arg_le_pi z.val]
    have hz_yx : z ∈ circleOpenArc y x := haux hxy.symm hyz_pos hyz_lt
    exact (disjoint_circleOpenArc hxy).ne_of_mem hz hz_yx rfl
  · rintro ⟨hpos, hlt⟩
    exact haux hxy hpos hlt

theorem onOpenArc_circleStdCoord_iff_angleDiff {a c b : Circle}
    (hab : a ≠ b) (hcb : c ≠ b) :
    onOpenArc circleStdCoord a c b ↔
      (if a.val.arg ≤ c.val.arg then a.angleDiff b < a.angleDiff c
       else a.angleDiff c < a.angleDiff b) := by
  rw [onOpenArc_iff_lt]
  dsimp only [circleStdCoord]
  grind [Circle.angleDiff, Circle.arg_eq_arg,
    Complex.neg_pi_lt_arg a.val, Complex.arg_le_pi a.val,
    Complex.neg_pi_lt_arg c.val, Complex.arg_le_pi c.val,
    Complex.neg_pi_lt_arg b.val, Complex.arg_le_pi b.val]

theorem angleDiff_eq_of_angleDiff {x a b : Circle} :
    a.angleDiff b =
      if x.angleDiff a ≤ x.angleDiff b then x.angleDiff b - x.angleDiff a
      else 2 * Real.pi + x.angleDiff b - x.angleDiff a := by
  grind [Circle.angleDiff, Circle.arg_eq_arg,
    Complex.neg_pi_lt_arg x.val, Complex.arg_le_pi x.val,
    Complex.neg_pi_lt_arg a.val, Complex.arg_le_pi a.val,
    Complex.neg_pi_lt_arg b.val, Complex.arg_le_pi b.val]

theorem onOpenArc_circleCoordFrom_iff_angleDiff {x a c b : Circle}
    (hac : a ≠ c) (hab : a ≠ b) (hcb : c ≠ b) :
    onOpenArc (circleCoordFrom x) a c b ↔
      (if x.angleDiff a ≤ x.angleDiff c then a.angleDiff b < a.angleDiff c
       else a.angleDiff c < a.angleDiff b) := by
  rw [onOpenArc_iff_lt]
  dsimp only [circleCoordFrom]
  have hab_eq := angleDiff_eq_of_angleDiff (x := x) (a := a) (b := b)
  have hac_eq := angleDiff_eq_of_angleDiff (x := x) (a := a) (b := c)
  have hxa_lt := Circle.angleDiff_lt_two_pi x a
  have hxc_lt := Circle.angleDiff_lt_two_pi x c
  have hxb_lt := Circle.angleDiff_lt_two_pi x b
  have hxa_ge := Circle.angleDiff_nonneg x a
  have hxc_ge := Circle.angleDiff_nonneg x c
  have hxb_ge := Circle.angleDiff_nonneg x b
  have hac_ne : x.angleDiff a ≠ x.angleDiff c := (circleCoordFrom x).injective.ne hac
  have hab_ne : x.angleDiff a ≠ x.angleDiff b := (circleCoordFrom x).injective.ne hab
  have hcb_ne : x.angleDiff c ≠ x.angleDiff b := (circleCoordFrom x).injective.ne hcb
  grind [-Circle.angleDiff]

theorem circleCrosses_circleStdCoord_iff_angleDiff {a c b d : Circle} :
    circleCrosses circleStdCoord a c b d ↔
      a ≠ c ∧ b ≠ d ∧ a ≠ b ∧ a ≠ d ∧ c ≠ b ∧ c ≠ d ∧
      (a.angleDiff b < a.angleDiff c ↔ ¬ a.angleDiff d < a.angleDiff c) := by
  simp only [circleCrosses]
  constructor <;> rintro ⟨hac, hbd, hab, had, hcb, hcd, hcross⟩ <;>
    refine ⟨hac, hbd, hab, had, hcb, hcd, ?_⟩
  · rw [onOpenArc_circleStdCoord_iff_angleDiff hab hcb,
      onOpenArc_circleStdCoord_iff_angleDiff had hcd] at hcross
    have hcb_ne : a.angleDiff c ≠ a.angleDiff b := (circleCoordFrom a).injective.ne hcb
    have hcd_ne : a.angleDiff c ≠ a.angleDiff d := (circleCoordFrom a).injective.ne hcd
    grind [-Circle.angleDiff]
  · rw [onOpenArc_circleStdCoord_iff_angleDiff hab hcb,
      onOpenArc_circleStdCoord_iff_angleDiff had hcd]
    have hcb_ne : a.angleDiff c ≠ a.angleDiff b := (circleCoordFrom a).injective.ne hcb
    have hcd_ne : a.angleDiff c ≠ a.angleDiff d := (circleCoordFrom a).injective.ne hcd
    grind [-Circle.angleDiff]

/-- For any basepoint $c \in \text{Circle}$, `circleCrosses (circleCoordFrom c)` agrees with
`circleCrosses circleStdCoord`. -/
theorem circleCrosses_circleCoordFrom_iff {c a c' b d : Circle} :
    circleCrosses (circleCoordFrom c) a c' b d ↔ circleCrosses circleStdCoord a c' b d := by
  rw [circleCrosses_circleStdCoord_iff_angleDiff]
  simp only [circleCrosses]
  constructor <;> rintro ⟨hac, hbd, hab, had, hcb, hcd, hcross⟩ <;>
    refine ⟨hac, hbd, hab, had, hcb, hcd, ?_⟩
  · rw [onOpenArc_circleCoordFrom_iff_angleDiff (x := c) hac hab hcb,
      onOpenArc_circleCoordFrom_iff_angleDiff (x := c) hac had hcd] at hcross
    have hcb_ne : a.angleDiff c' ≠ a.angleDiff b := (circleCoordFrom a).injective.ne hcb
    have hcd_ne : a.angleDiff c' ≠ a.angleDiff d := (circleCoordFrom a).injective.ne hcd
    grind [-Circle.angleDiff]
  · rw [onOpenArc_circleCoordFrom_iff_angleDiff (x := c) hac hab hcb,
      onOpenArc_circleCoordFrom_iff_angleDiff (x := c) hac had hcd]
    have hcb_ne : a.angleDiff c' ≠ a.angleDiff b := (circleCoordFrom a).injective.ne hcb
    have hcd_ne : a.angleDiff c' ≠ a.angleDiff d := (circleCoordFrom a).injective.ne hcd
    grind [-Circle.angleDiff]

/-- On `Circle`, four distinct points $a, b, c, d$ have $b$ and $d$ in different connected
components of `({a, c} : Set Circle)ᶜ` if and only if `circleCrosses circleStdCoord a c b d`. -/
theorem connectedComponentIn_compl_pair_ne_iff_circleCrosses {a c b d : Circle}
    (hac : a ≠ c) (hbd : b ≠ d) (hab : a ≠ b) (had : a ≠ d) (hcb : c ≠ b) (hcd : c ≠ d) :
    connectedComponentIn ({a, c} : Set Circle)ᶜ b ≠
      connectedComponentIn ({a, c} : Set Circle)ᶜ d ↔
      circleCrosses circleStdCoord a c b d := by
  have hb_mem : b ∈ circleOpenArc a c ∪ circleOpenArc c a := by
    rw [← compl_pair_eq_union_circleOpenArc hac]
    simp [hab.symm, hcb.symm]
  have hd_mem : d ∈ circleOpenArc a c ∪ circleOpenArc c a := by
    rw [← compl_pair_eq_union_circleOpenArc hac]
    simp [had.symm, hcd.symm]
  have hne_arcs : circleOpenArc a c ≠ circleOpenArc c a := by
    obtain ⟨z, hz⟩ := nonempty_circleOpenArc hac
    intro heq
    exact (disjoint_circleOpenArc hac).ne_of_mem hz (heq ▸ hz) rfl
  have hcc_iff : (connectedComponentIn ({a, c} : Set Circle)ᶜ b ≠
      connectedComponentIn ({a, c} : Set Circle)ᶜ d) ↔
      (b ∈ circleOpenArc a c ↔ d ∉ circleOpenArc a c) := by
    rcases hb_mem with hb1 | hb2 <;> rcases hd_mem with hd1 | hd2
    · rw [connectedComponentIn_compl_pair_eq_left hac hb1,
        connectedComponentIn_compl_pair_eq_left hac hd1]
      simp [hb1, hd1]
    · rw [connectedComponentIn_compl_pair_eq_left hac hb1,
        connectedComponentIn_compl_pair_eq_right hac hd2]
      have hd1 : d ∉ circleOpenArc a c :=
        fun h => (disjoint_circleOpenArc hac).ne_of_mem h hd2 rfl
      simp [hne_arcs, hb1, hd1]
    · rw [connectedComponentIn_compl_pair_eq_right hac hb2,
        connectedComponentIn_compl_pair_eq_left hac hd1]
      have hb1 : b ∉ circleOpenArc a c :=
        fun h => (disjoint_circleOpenArc hac).ne_of_mem h hb2 rfl
      simp [hne_arcs.symm, hb1, hd1]
    · rw [connectedComponentIn_compl_pair_eq_right hac hb2,
        connectedComponentIn_compl_pair_eq_right hac hd2]
      have hb1 : b ∉ circleOpenArc a c :=
        fun h => (disjoint_circleOpenArc hac).ne_of_mem h hb2 rfl
      have hd1 : d ∉ circleOpenArc a c :=
        fun h => (disjoint_circleOpenArc hac).ne_of_mem h hd2 rfl
      simp [hb1, hd1]
  rw [hcc_iff, mem_circleOpenArc_iff_angleDiff hac, mem_circleOpenArc_iff_angleDiff hac,
    circleCrosses_circleStdCoord_iff_angleDiff]
  have hb_pos := Circle.angleDiff_pos hab
  have hd_pos := Circle.angleDiff_pos had
  grind [-Circle.angleDiff]

/-- A topological embedding commutes with `connectedComponentIn`. -/
theorem isEmbedding_image_connectedComponentIn {X Y : Type*} [TopologicalSpace X]
    [TopologicalSpace Y] {f : X → Y} (hf : IsEmbedding f) {s : Set X} {x : X} (hx : x ∈ s) :
    f '' connectedComponentIn s x = connectedComponentIn (f '' s) (f x) := by
  refine (hf.continuous.continuousOn.image_connectedComponentIn_subset hx).antisymm ?_
  let K := connectedComponentIn (f '' s) (f x)
  have hK_sub : K ⊆ f '' s := connectedComponentIn_subset (f '' s) (f x)
  have hK_range : K ⊆ range f := hK_sub.trans (image_subset_range f s)
  have hK_eq : f '' (f ⁻¹' K) = K := image_preimage_eq_of_subset hK_range
  have hpre_conn : IsPreconnected (f ⁻¹' K) := by
    rw [← hf.isInducing.isPreconnected_image, hK_eq]
    exact isPreconnected_connectedComponentIn
  have hx_pre : x ∈ f ⁻¹' K := mem_connectedComponentIn (mem_image_of_mem f hx)
  have hpre_sub : f ⁻¹' K ⊆ s := by
    rw [← preimage_image_eq s hf.injective]
    exact preimage_mono hK_sub
  change K ⊆ _
  rw [← hK_eq]
  exact image_mono (hpre_conn.subset_connectedComponentIn hx_pre hpre_sub)

/-! ## 4. Segments of `Circle` with respect to a Finite Set -/

/-- For $V \subseteq \text{Circle}$ and $v \in V$, `nextSegment V v` is the open segment of
$\text{Circle} \setminus V$ immediately following $v$ in the counterclockwise direction. -/
def nextSegment (V : Set Circle) (v : Circle) : Set Circle :=
  {z : Circle | z ≠ v ∧ ∀ w ∈ V \ {v}, v.angleDiff z < v.angleDiff w}

/-- For $V \subseteq \text{Circle}$ and $v \in V$, `prevSegment V v` is the open segment of
$\text{Circle} \setminus V$ immediately preceding $v$ in the counterclockwise direction. -/
def prevSegment (V : Set Circle) (v : Circle) : Set Circle :=
  {z : Circle | z ≠ v ∧ ∀ w ∈ V \ {v}, z.angleDiff v < w.angleDiff v}

theorem nextSegment_subset_compl {V : Set Circle} {v : Circle} :
    nextSegment V v ⊆ Vᶜ := by
  intro z ⟨hzv, hzw⟩ hzV
  have hmem : z ∈ V \ {v} := ⟨hzV, hzv⟩
  exact lt_irrefl _ (hzw z hmem)

theorem prevSegment_subset_compl {V : Set Circle} {v : Circle} :
    prevSegment V v ⊆ Vᶜ := by
  intro z ⟨hzv, hzw⟩ hzV
  have hmem : z ∈ V \ {v} := ⟨hzV, hzv⟩
  exact lt_irrefl _ (hzw z hmem)

theorem nextSegment_singleton (v : Circle) : nextSegment {v} v = {v}ᶜ := by
  ext z
  simp [nextSegment]

theorem prevSegment_singleton (v : Circle) : prevSegment {v} v = {v}ᶜ := by
  ext z
  simp [prevSegment]

theorem exists_min_on_finite {S : Set Circle} (hS : S.Finite) (hne : S.Nonempty)
    (f : Circle → ℝ) : ∃ m ∈ S, ∀ w ∈ S, f m ≤ f w := by
  obtain ⟨m, hm, hmin⟩ := hS.toFinset.exists_min_image f (hS.toFinset_nonempty.mpr hne)
  exact ⟨m, hS.mem_toFinset.mp hm, fun w hw => hmin w (hS.mem_toFinset.mpr hw)⟩

theorem exists_max_on_finite {S : Set Circle} (hS : S.Finite) (hne : S.Nonempty)
    (f : Circle → ℝ) : ∃ m ∈ S, ∀ w ∈ S, f w ≤ f m := by
  obtain ⟨m, hm, hmax⟩ := hS.toFinset.exists_max_image f (hS.toFinset_nonempty.mpr hne)
  exact ⟨m, hS.mem_toFinset.mp hm, fun w hw => hmax w (hS.mem_toFinset.mpr hw)⟩

theorem nextSegment_eq_circleOpenArc_of_min {V : Set Circle} {v v_next : Circle}
    (hv_next : v_next ∈ V \ {v})
    (hmin : ∀ w ∈ V \ {v}, v.angleDiff v_next ≤ v.angleDiff w) :
    nextSegment V v = circleOpenArc v v_next := by
  have hne : v ≠ v_next := Ne.symm hv_next.2
  ext z
  rw [mem_circleOpenArc_iff_angleDiff hne]
  simp only [nextSegment, mem_ofPred_eq]
  constructor
  · rintro ⟨hzv, hzw⟩
    exact ⟨Circle.angleDiff_pos (Ne.symm hzv), hzw v_next hv_next⟩
  · rintro ⟨hpos, hlt⟩
    refine ⟨?_, fun w hw => lt_of_lt_of_le hlt (hmin w hw)⟩
    rintro rfl
    simp [Circle.angleDiff] at hpos

theorem nextSegment_nonempty {V : Set Circle} (hV : V.Finite) {v : Circle} (hv : v ∈ V) :
    (nextSegment V v).Nonempty := by
  rcases (V \ {v}).eq_empty_or_nonempty with hemp | hne
  · have hV_eq : V = {v} := Subset.antisymm (sdiff_eq_empty.mp hemp) (singleton_subset_iff.mpr hv)
    rw [hV_eq, nextSegment_singleton]
    exact ⟨-v, Circle.neg_ne_self v⟩
  · obtain ⟨v_next, hv_next, hmin⟩ := exists_min_on_finite (hV.sdiff) hne (Circle.angleDiff v)
    rw [nextSegment_eq_circleOpenArc_of_min hv_next hmin]
    exact nonempty_circleOpenArc (Ne.symm hv_next.2)

theorem connectedComponentIn_compl_eq_nextSegment {V : Set Circle} (hV : V.Finite)
    {v z : Circle} (hv : v ∈ V) (hz : z ∈ nextSegment V v) :
    connectedComponentIn Vᶜ z = nextSegment V v := by
  rcases (V \ {v}).eq_empty_or_nonempty with hemp | hne
  · have hV_eq : V = {v} := Subset.antisymm (sdiff_eq_empty.mp hemp) (singleton_subset_iff.mpr hv)
    rw [hV_eq, nextSegment_singleton] at hz ⊢
    exact (Circle.isPathConnected_compl_singleton
      v).isConnected.isPreconnected.connectedComponentIn hz
  · obtain ⟨v_next, hv_next, hmin⟩ := exists_min_on_finite (hV.sdiff) hne (Circle.angleDiff v)
    have hne_v : v ≠ v_next := Ne.symm hv_next.2
    have hseg_eq := nextSegment_eq_circleOpenArc_of_min hv_next hmin
    rw [hseg_eq] at hz ⊢
    have hA_sub : circleOpenArc v v_next ⊆ Vᶜ := hseg_eq ▸ nextSegment_subset_compl
    have hcompl_union : Vᶜ = circleOpenArc v v_next ∪ (Vᶜ ∩ circleOpenArc v_next v) := by
      ext x
      constructor
      · intro hxV
        have hxv : x ≠ v := fun h => hxV (h ▸ hv)
        have hxv' : x ≠ v_next := fun h => hxV (h ▸ hv_next.1)
        have hx_pair : x ∈ ({v, v_next} : Set Circle)ᶜ := by simp [hxv, hxv']
        rw [compl_pair_eq_union_circleOpenArc hne_v] at hx_pair
        rcases hx_pair with hx1 | hx2
        · exact Or.inl hx1
        · exact Or.inr ⟨hxV, hx2⟩
      · rintro (hx1 | ⟨hxV, _⟩)
        · exact hA_sub hx1
        · exact hxV
    rw [hcompl_union]
    exact connectedComponentIn_eq_left_of_union_disjoint_open
      (isOpen_circleOpenArc hne_v)
      (hV.isClosed.isOpen_compl.inter (isOpen_circleOpenArc hne_v.symm))
      ((disjoint_circleOpenArc hne_v).mono_right inter_subset_right)
      (isPathConnected_circleOpenArc v v_next).isConnected.isPreconnected
      hz

theorem exists_unique_nextSegment_of_mem_compl {V : Set Circle} (hV : V.Finite)
    (hne : V.Nonempty) {z : Circle} (hz : z ∈ Vᶜ) :
    ∃! v, v ∈ V ∧ z ∈ nextSegment V v := by
  obtain ⟨v, hv, hmin⟩ := exists_min_on_finite hV hne (fun w => w.angleDiff z)
  have hzv : z ≠ v := fun h => hz (h ▸ hv)
  have hz_mem : z ∈ nextSegment V v := by
    refine ⟨hzv, fun w hw => ?_⟩
    by_contra! hle
    have hwz : w ≠ z := fun h => hz (h ▸ hw.1)
    have hvw_pos : 0 < v.angleDiff w := Circle.angleDiff_pos (Ne.symm hw.2)
    have hmin_w : v.angleDiff z ≤ w.angleDiff z := hmin w hw.1
    have heq := angleDiff_eq_of_angleDiff (x := v) (a := w) (b := z)
    grind [-Circle.angleDiff]
  refine ⟨v, ⟨hv, hz_mem⟩, ?_⟩
  rintro v' ⟨hv', hzv', hzw'⟩
  by_contra hne'
  have h1 : v.angleDiff z < v.angleDiff v' := hz_mem.2 v' ⟨hv', hne'⟩
  have h2 : v'.angleDiff z < v'.angleDiff v := hzw' v ⟨hv, Ne.symm hne'⟩
  have hzv_pos := Circle.angleDiff_pos hzv.symm
  have hsum := Circle.angleDiff_add_angleDiff (Ne.symm hne')
  have heq := angleDiff_eq_of_angleDiff (x := v) (a := v') (b := z)
  grind [-Circle.angleDiff]

theorem mem_prevSegment_iff {V : Set Circle} {v z : Circle} :
    z ∈ prevSegment V v ↔ z ≠ v ∧ ∀ w ∈ V \ {v}, v.angleDiff w < v.angleDiff z := by
  simp only [prevSegment, mem_ofPred_eq]
  refine and_congr_right fun hzv => forall₂_congr fun w hw => ?_
  have h1 := Circle.angleDiff_add_angleDiff hzv
  have h2 := Circle.angleDiff_add_angleDiff hw.2
  constructor <;> intro h <;> linarith

theorem prevSegment_eq_nextSegment_of_max {V : Set Circle} {v v_prev : Circle}
    (hv : v ∈ V) (hv_prev : v_prev ∈ V \ {v})
    (hmax : ∀ w ∈ V \ {v}, v.angleDiff w ≤ v.angleDiff v_prev) :
    prevSegment V v = nextSegment V v_prev := by
  ext z
  rw [mem_prevSegment_iff]
  simp only [nextSegment, mem_ofPred_eq]
  have hvv' : v_prev ≠ v := hv_prev.2
  have hsum_vv' := Circle.angleDiff_add_angleDiff hvv'
  have hvp_pos := Circle.angleDiff_pos hvv'.symm
  constructor
  · rintro ⟨hzv, hzw⟩
    have hlt : v.angleDiff v_prev < v.angleDiff z := hzw v_prev hv_prev
    have hzv_prev : z ≠ v_prev := by
      rintro rfl
      exact lt_irrefl _ hlt
    have hzv_lt := Circle.angleDiff_lt_two_pi v z
    have heq_z := angleDiff_eq_of_angleDiff (x := v) (a := v_prev) (b := z)
    refine ⟨hzv_prev, fun w hw => ?_⟩
    rcases eq_or_ne w v with rfl | hwv
    · grind [-Circle.angleDiff]
    · have hw_mem : w ∈ V \ {v} := ⟨hw.1, hwv⟩
      have hle_w := hmax w hw_mem
      have hw_pos := Circle.angleDiff_pos hwv.symm
      have heq_w := angleDiff_eq_of_angleDiff (x := v) (a := v_prev) (b := w)
      have hlt_w : v.angleDiff w < v.angleDiff v_prev :=
        lt_of_le_of_ne hle_w ((circleCoordFrom v).injective.ne hw.2)
      grind [-Circle.angleDiff]
  · rintro ⟨hzv_prev, hzw⟩
    have hlt_v : v_prev.angleDiff z < v_prev.angleDiff v :=
      hzw v ⟨hv, hvv'.symm⟩
    have hzv : z ≠ v := by
      rintro rfl
      exact lt_irrefl _ hlt_v
    have hzp_pos := Circle.angleDiff_pos hzv_prev.symm
    have hzv_pos := Circle.angleDiff_pos hzv.symm
    have heq_z := angleDiff_eq_of_angleDiff (x := v) (a := v_prev) (b := z)
    have hgt : v.angleDiff v_prev < v.angleDiff z := by grind [-Circle.angleDiff]
    exact ⟨hzv, fun w hw => lt_of_le_of_lt (hmax w hw) hgt⟩

theorem exists_nextSegment_eq_prevSegment {V : Set Circle} (hV : V.Finite)
    {v : Circle} (hv : v ∈ V) :
    ∃ v_prev ∈ V, prevSegment V v = nextSegment V v_prev := by
  rcases (V \ {v}).eq_empty_or_nonempty with hemp | hne
  · have hV_eq : V = {v} := Subset.antisymm (sdiff_eq_empty.mp hemp) (singleton_subset_iff.mpr hv)
    refine ⟨v, hv, ?_⟩
    rw [hV_eq, prevSegment_singleton, nextSegment_singleton]
  · obtain ⟨v_prev, hv_prev, hmax⟩ := exists_max_on_finite (hV.sdiff) hne (Circle.angleDiff v)
    exact ⟨v_prev, hv_prev.1, prevSegment_eq_nextSegment_of_max hv hv_prev hmax⟩

theorem exists_unique_prevSegment_of_mem_compl {V : Set Circle} (hV : V.Finite)
    (hne : V.Nonempty) {z : Circle} (hz : z ∈ Vᶜ) :
    ∃! v, v ∈ V ∧ z ∈ prevSegment V v := by
  obtain ⟨v, hv, hmin⟩ := exists_min_on_finite hV hne (fun w => z.angleDiff w)
  have hzv : z ≠ v := fun h => hz (h ▸ hv)
  have hz_mem : z ∈ prevSegment V v := by
    refine ⟨hzv, fun w hw => ?_⟩
    by_contra! hle
    have hwv : v ≠ w := Ne.symm hw.2
    have hmin_w : z.angleDiff v ≤ z.angleDiff w := hmin w hw.1
    have hzv_ne_zw : z.angleDiff v ≠ z.angleDiff w := (circleCoordFrom z).injective.ne hwv
    have hzv_lt_zw : z.angleDiff v < z.angleDiff w := lt_of_le_of_ne hmin_w hzv_ne_zw
    have hzw_lt := Circle.angleDiff_lt_two_pi z w
    have hsum_zv := Circle.angleDiff_add_angleDiff hzv
    have hsum_wv := Circle.angleDiff_add_angleDiff hw.2
    have heq := angleDiff_eq_of_angleDiff (x := z) (a := w) (b := v)
    grind [-Circle.angleDiff]
  refine ⟨v, ⟨hv, hz_mem⟩, ?_⟩
  rintro v' ⟨hv', hzv', hzw'⟩
  by_contra hne'
  have h1 : z.angleDiff v < v'.angleDiff v := hz_mem.2 v' ⟨hv', hne'⟩
  have h2 : z.angleDiff v' < v.angleDiff v' := hzw' v ⟨hv, Ne.symm hne'⟩
  have hzv_pos := Circle.angleDiff_pos hzv
  have hsum := Circle.angleDiff_add_angleDiff (Ne.symm hne')
  have heq := angleDiff_eq_of_angleDiff (x := z) (a := v) (b := v')
  grind [-Circle.angleDiff]

theorem angleDiff_exp_mul {v : Circle} {θ : ℝ} (h0 : 0 < θ) (h2pi : θ < 2 * Real.pi) :
    v.angleDiff (Circle.exp θ * v) = θ := by
  let z := Circle.exp θ * v
  have hexp : Circle.exp (v.angleDiff z) = Circle.exp θ :=
    mul_right_cancel (Circle.exp_angleDiff_mul (x := v) (y := z))
  have hinj := Circle.exp_injOn_Ioc (a := 0) (b := 2 * Real.pi) (by linarith)
  have hzv : v ≠ z := by
    intro h
    have h1 : Circle.exp θ = Circle.exp (2 * Real.pi) := by
      rw [Circle.exp_two_pi, ← mul_left_inj v, one_mul]
      exact h.symm
    have hθ_mem : θ ∈ Ioc 0 (2 * Real.pi) := ⟨h0, h2pi.le⟩
    have h2pi_mem : 2 * Real.pi ∈ Ioc 0 (2 * Real.pi) := ⟨Real.two_pi_pos, le_rfl⟩
    exact h2pi.ne (hinj hθ_mem h2pi_mem h1)
  have hz_mem : v.angleDiff z ∈ Ioc 0 (2 * Real.pi) :=
    ⟨Circle.angleDiff_pos hzv, (Circle.angleDiff_lt_two_pi v z).le⟩
  have hθ_mem : θ ∈ Ioc 0 (2 * Real.pi) := ⟨h0, h2pi.le⟩
  exact hinj hz_mem hθ_mem hexp

/-- The open arc of length $L \in (0, 2\pi]$ starting at $v \in \text{Circle}$. -/
def arcOfLength (v : Circle) (L : ℝ) : Set Circle :=
  {z : Circle | 0 < v.angleDiff z ∧ v.angleDiff z < L}

/-- Any open arc `arcOfLength v L` with $0 < L \le 2\pi$ is homeomorphic to `Ioo (0 : ℝ) 1`. -/
noncomputable def homeomorphIooArcOfLength (v : Circle) {L : ℝ} (hL0 : 0 < L)
    (hL2pi : L ≤ 2 * Real.pi) : Ioo (0 : ℝ) 1 ≃ₜ arcOfLength v L where
  toFun t := ⟨Circle.exp (L * t.1) * v, by
    have ht0 : 0 < L * t.1 := mul_pos hL0 t.2.1
    have htL : L * t.1 < L := by nlinarith [t.2.2]
    have ht2pi : L * t.1 < 2 * Real.pi := htL.trans_le hL2pi
    simp only [arcOfLength, mem_ofPred_eq, angleDiff_exp_mul ht0 ht2pi]
    exact ⟨ht0, htL⟩⟩
  invFun z := ⟨v.angleDiff z.1 / L,
    div_pos z.2.1 hL0, (div_lt_one hL0).mpr z.2.2⟩
  left_inv t := by
    ext
    have ht0 : 0 < L * t.1 := mul_pos hL0 t.2.1
    have htL : L * t.1 < L := by nlinarith [t.2.2]
    have ht2pi : L * t.1 < 2 * Real.pi := htL.trans_le hL2pi
    dsimp only
    rw [angleDiff_exp_mul ht0 ht2pi, mul_div_cancel_left₀ t.1 hL0.ne']
  right_inv z := by
    ext
    dsimp only
    rw [mul_div_cancel₀ _ hL0.ne', Circle.exp_angleDiff_mul]
  continuous_toFun := by
    refine Continuous.subtype_mk ?_ _
    exact (Circle.exp.continuous.comp (continuous_const.mul continuous_subtype_val)).mul
      continuous_const
  continuous_invFun := by
    rw [continuous_def]
    intro U hU
    let e : Ioo (0 : ℝ) 1 ≃ arcOfLength v L :=
      { toFun := fun t => ⟨Circle.exp (L * t.1) * v, by
          have ht0 : 0 < L * t.1 := mul_pos hL0 t.2.1
          have htL : L * t.1 < L := by nlinarith [t.2.2]
          have ht2pi : L * t.1 < 2 * Real.pi := htL.trans_le hL2pi
          simp only [arcOfLength, mem_ofPred_eq, angleDiff_exp_mul ht0 ht2pi]
          exact ⟨ht0, htL⟩⟩
        invFun := fun z => ⟨v.angleDiff z.1 / L,
          div_pos z.2.1 hL0, (div_lt_one hL0).mpr z.2.2⟩
        left_inv := fun t => by
          ext
          have ht0 : 0 < L * t.1 := mul_pos hL0 t.2.1
          have htL : L * t.1 < L := by nlinarith [t.2.2]
          have ht2pi : L * t.1 < 2 * Real.pi := htL.trans_le hL2pi
          dsimp only
          rw [angleDiff_exp_mul ht0 ht2pi, mul_div_cancel_left₀ t.1 hL0.ne']
        right_inv := fun z => by
          ext
          dsimp only
          rw [mul_div_cancel₀ _ hL0.ne', Circle.exp_angleDiff_mul] }
    change IsOpen (e.symm ⁻¹' U)
    rw [← Equiv.image_eq_preimage_symm]
    have hU_real : IsOpen (Subtype.val '' U) := isOpen_Ioo.isOpenMap_subtype_val U hU
    have hU_mul : IsOpen ((fun t : ℝ => L * t) '' (Subtype.val '' U)) :=
      (Homeomorph.mulLeft₀ L hL0.ne').isOpenMap _ hU_real
    have hU_exp : IsOpen (Circle.exp '' ((fun t : ℝ => L * t) '' (Subtype.val '' U))) :=
      isLocalHomeomorph_circleExp.isOpenMap _ hU_mul
    have hU_rot : IsOpen ((fun z : Circle => z * v) ''
        (Circle.exp '' ((fun t : ℝ => L * t) '' (Subtype.val '' U)))) :=
      (Homeomorph.mulRight v).isOpenMap _ hU_exp
    have heq : e '' U = Subtype.val ⁻¹' ((fun z : Circle => z * v) ''
        (Circle.exp '' ((fun t : ℝ => L * t) '' (Subtype.val '' U)))) := by
      ext z
      simp only [mem_image, Subtype.exists, mem_preimage, exists_and_right, exists_eq_right]
      constructor
      · rintro ⟨t, htIoo, htU, htz⟩
        refine ⟨Circle.exp (L * t), ⟨L * t, ⟨t, ⟨htIoo, htU⟩, rfl⟩, rfl⟩, ?_⟩
        exact congrArg Subtype.val htz
      · rintro ⟨_, ⟨_, ⟨t, ⟨htIoo, htU⟩, rfl⟩, rfl⟩, htz⟩
        refine ⟨t, htIoo, htU, Subtype.ext htz⟩
    rw [heq]
    exact hU_rot.preimage continuous_subtype_val

theorem nonempty_homeomorph_Ioo_nextSegment {V : Set Circle} (hV : V.Finite) {v : Circle}
    (hv : v ∈ V) : Nonempty (Ioo (0 : ℝ) 1 ≃ₜ nextSegment V v) := by
  rcases (V \ {v}).eq_empty_or_nonempty with hemp | hne
  · have hV_eq : V = {v} := Subset.antisymm (sdiff_eq_empty.mp hemp) (singleton_subset_iff.mpr hv)
    have hseg : nextSegment V v = arcOfLength v (2 * Real.pi) := by
      rw [hV_eq, nextSegment_singleton]
      ext z
      simp only [mem_compl_iff, mem_singleton_iff, arcOfLength, mem_ofPred_eq]
      exact ⟨fun h => ⟨Circle.angleDiff_pos (Ne.symm h), Circle.angleDiff_lt_two_pi v z⟩,
        fun ⟨hpos, _⟩ h => by subst h; simp [Circle.angleDiff] at hpos⟩
    rw [hseg]
    exact ⟨homeomorphIooArcOfLength v Real.two_pi_pos le_rfl⟩
  · obtain ⟨v_next, hv_next, hmin⟩ := exists_min_on_finite (hV.sdiff) hne (Circle.angleDiff v)
    have hne_v : v ≠ v_next := Ne.symm hv_next.2
    have hseg : nextSegment V v = arcOfLength v (v.angleDiff v_next) := by
      rw [nextSegment_eq_circleOpenArc_of_min hv_next hmin]
      ext z
      rw [mem_circleOpenArc_iff_angleDiff hne_v]
      rfl
    rw [hseg]
    exact ⟨homeomorphIooArcOfLength v (Circle.angleDiff_pos hne_v)
      (Circle.angleDiff_lt_two_pi v v_next).le⟩

end GraphMinor.Surface
