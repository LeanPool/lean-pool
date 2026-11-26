/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM19.Section2
public import LeanPool.GraphMinor.GM19.Lens
public import LeanPool.GraphMinor.GM19.PushSide
public import LeanPool.GraphMinor.GM19.RadialExists
public import LeanPool.GraphMinor.GM20.Section10j
public import Mathlib.Analysis.Convex.Strict
public import Mathlib.Analysis.Normed.Module.Convex

/-!
# The narrow painting in the proof of Graph Minors XIX, (2.1)

Each edge `c` of size 3 of a painting `Γ` is replaced by the arcs of its boundary and a small disc
`Δ(c)`
that meets the boundary of `cBar` in `cTilde` only. We show that the result is a painting. Its edges
are the edges of
the 1-skeleton, and the sets `Δ(c) \ cTilde`.
-/

@[expose] public section

namespace GraphMinor.GM19

open Set Topology Metric GraphMinor.Surface

variable {S : Type} [TopologicalSpace S] [T2Space S]

/-! ### Arc components from pieces -/

omit [T2Space S] in
/-- If a set is cut into finitely many disjoint path connected pieces, each closed in the set, then
the
pieces are its arc-wise components. -/
theorem arcComponentsIn_of_pieces {W : Set S} {P : Set (Set S)} (hP : P.Finite)
    (hpc : ∀ p ∈ P, IsPathConnected p) (hd : ∀ p ∈ P, ∀ q ∈ P, p ≠ q → Disjoint p q)
    (hcl : ∀ p ∈ P, closure p ∩ W ⊆ p) (hW : W = ⋃₀ P) : arcComponentsIn W = P := by
  have hsub : ∀ p ∈ P, p ⊆ W := fun p hp ↦ hW ▸ subset_sUnion_of_mem hp
  have hmem : ∀ p ∈ P, p ∈ arcComponentsIn W := by
    intro p hp
    refine ⟨(hpc p hp).nonempty, hsub p hp, hpc p hp, fun D hD hDc hpD ↦ ?_⟩
    let Q : Set S := ⋃ q ∈ P \ {p}, closure q
    have hQ : IsClosed Q := (hP.subset sdiff_subset).isClosed_biUnion fun _ _ ↦ isClosed_closure
    have hcov : D ⊆ closure p ∪ Q := fun x hx ↦ by
      have hxW := hD hx
      rw [hW] at hxW
      obtain ⟨q, hq, hxq⟩ := hxW
      by_cases hqp : q = p
      · exact Or.inl (subset_closure (hqp ▸ hxq))
      · exact Or.inr (mem_biUnion (show q ∈ P \ {p} from ⟨hq, hqp⟩) (subset_closure hxq))
    refine Subset.antisymm (fun x hx ↦ ?_) hpD
    by_contra hxp
    have hxQ : x ∈ Q := (hcov hx).resolve_left fun h ↦ hxp (hcl p hp ⟨h, hD hx⟩)
    obtain ⟨y₀, hy₀⟩ := (hpc p hp).nonempty
    obtain ⟨y, hyD, hy₁, hy₂⟩ := isPreconnected_closed_iff.mp hDc.isConnected.isPreconnected _ _
      isClosed_closure hQ hcov ⟨y₀, hpD hy₀, subset_closure hy₀⟩ ⟨x, hx, hxQ⟩
    have hyp := hcl p hp ⟨hy₁, hD hyD⟩
    obtain ⟨q, hq, hyq⟩ := mem_iUnion₂.mp hy₂
    have hyq' := hcl q hq.1 ⟨hyq, hD hyD⟩
    exact disjoint_left.mp (hd p hp q hq.1 (Ne.symm hq.2)) hyp hyq'
  ext C
  refine ⟨fun hC ↦ ?_, hmem C⟩
  obtain ⟨x, hx⟩ := hC.1
  have hxW := hC.2.1 hx
  rw [hW] at hxW
  obtain ⟨p, hp, hxp⟩ := hxW
  rw [arcComp_eq_of_mem hC (hmem p hp) hx hxp]
  exact hp

/-! ### A disc without finitely many boundary points -/

omit [T2Space S] in
theorem isPathConnected_disc_sdiff {D T : Set S} (hD : IsClosedDisc D) (hT : T ⊆ discBd D) :
    IsPathConnected (D \ T) := by
  obtain ⟨h, g, c⟩ := hD.exists_isChart
  let B : Set ℂ := closedBall 0 1 \ h '' T
  have hTs : h '' T ⊆ sphere 0 1 := c.bd ▸ image_mono hT
  have hB : Convex ℝ B := by
    intro x hx y hy a b ha hb hab
    by_cases hxy : x = y
    · have : a • x + b • y = x := by
        rw [← hxy, ← add_smul, hab, one_smul]
      rwa [this]
    rcases eq_or_lt_of_le ha with rfl | ha'
    · have hb1 : b = 1 := by linarith
      subst hb1
      simpa using hy
    rcases eq_or_lt_of_le hb with rfl | hb'
    · have ha1 : a = 1 := by linarith
      subst ha1
      simpa using hx
    have hin := (strictConvex_closedBall ℝ (0 : ℂ) 1) hx.1 hy.1 hxy ha' hb' hab
    rw [interior_closedBall _ one_ne_zero] at hin
    refine ⟨ball_subset_closedBall hin, fun hmem ↦ ?_⟩
    have := hTs hmem
    rw [mem_sphere_zero_iff_norm] at this
    rw [mem_ball_zero_iff] at hin
    linarith
  have hB0 : (0 : ℂ) ∈ B := ⟨by simp, fun hmem ↦ by
    have := hTs hmem
    simp at this⟩
  have heq : D \ T = g '' B := by
    ext x
    constructor
    · rintro ⟨hx, hxT⟩
      refine ⟨h x, ⟨c.hm hx, ?_⟩, c.gh hx⟩
      rintro ⟨y, hy, he⟩
      have hyD := discBd_subset _ (hT hy)
      exact hxT (by rw [← c.gh hx, ← he, c.gh hyD]; exact hy)
    · rintro ⟨z, ⟨hz, hzT⟩, rfl⟩
      refine ⟨c.gm hz, fun hg ↦ hzT ⟨_, hg, c.hg hz⟩⟩
  rw [heq]
  exact (hB.isPathConnected ⟨0, hB0⟩).image' (c.gc.mono sdiff_subset)

theorem closure_disc_sdiff {D T : Set S} (hD : IsClosedDisc D) (hT : T ⊆ discBd D) :
    closure (D \ T) = D := by
  obtain ⟨h, g, c⟩ := hD.exists_isChart
  have hcl : IsClosed D := hD.isClosed
  refine Subset.antisymm (closure_minimal sdiff_subset hcl) ?_
  have hTs : h '' T ⊆ sphere 0 1 := c.bd ▸ image_mono hT
  have hsub : g '' ball 0 1 ⊆ D \ T := by
    rintro _ ⟨z, hz, rfl⟩
    have hz' := ball_subset_closedBall hz
    refine ⟨c.gm hz', fun hg ↦ ?_⟩
    have := hTs ⟨_, hg, c.hg hz'⟩
    rw [mem_sphere_zero_iff_norm] at this
    rw [mem_ball_zero_iff] at hz
    linarith
  intro x hx
  have hz := c.hm hx
  have hzc : h x ∈ closure (ball (0 : ℂ) 1) := by
    rw [closure_ball _ one_ne_zero]
    exact hz
  have : g (h x) ∈ closure (g '' ball 0 1) :=
    ((c.gc _ hz).mono ball_subset_closedBall).mem_closure_image hzc
  rw [c.gh hx] at this
  exact closure_mono hsub this

omit [T2Space S] in
/-- An `O`-arc in an `O`-arc is all of it: otherwise the first one would embed in the real line. -/
theorem not_oArc_subset {E F : Set S} (hE : IsOArc E) (hF : IsOArc F) (hEF : E ⊆ F) {w : S}
    (hw : w ∈ F) (hwE : w ∉ E) : False := by
  obtain ⟨ψ⟩ := hE
  obtain ⟨φ⟩ := hF
  let z₀ : Circle := φ.symm ⟨w, hw⟩
  let u : Circle → Circle := fun t ↦ φ.symm ⟨(ψ t).1, hEF (ψ t).2⟩
  have hu : Continuous u :=
    φ.symm.continuous.comp ((continuous_subtype_val.comp ψ.continuous).subtype_mk _)
  have hne : ∀ t, u t ≠ z₀ := fun t he ↦ by
    have : (⟨(ψ t).1, hEF (ψ t).2⟩ : F) = ⟨w, hw⟩ := φ.symm.injective he
    have h : (ψ t).1 = w := congrArg Subtype.val this
    exact hwE (h ▸ (ψ t).2)
  let v : Circle → Circle := fun t ↦ Circle.exp Real.pi * (u t * z₀⁻¹)
  have hv : Continuous v := by fun_prop
  have hvne : ∀ t, v t ≠ Circle.exp Real.pi := fun t he ↦ by
    have h1 : u t * z₀⁻¹ = 1 := mul_left_cancel (he.trans (mul_one _).symm)
    exact hne t (mul_inv_eq_one.mp h1)
  have hvi : Function.Injective v := fun a b he ↦ by
    have h1 : u a = u b := mul_right_cancel (mul_left_cancel he)
    have h2 := φ.symm.injective h1
    have h3 : (ψ a).1 = (ψ b).1 := Subtype.mk.inj h2
    exact ψ.injective (Subtype.ext h3)
  refine not_injective_circle_real (f := fun t ↦ Complex.arg (v t)) ?_
    (Circle.injective_arg.comp hvi)
  refine continuous_iff_continuousAt.mpr fun t ↦ ?_
  have hslit : (v t : ℂ) ∈ Complex.slitPlane := by
    rw [Complex.mem_slitPlane_iff_arg]
    refine ⟨fun h ↦ hvne t ?_, (v t).coe_ne_zero⟩
    rw [← Circle.exp_arg (v t), h]
  exact ContinuousAt.comp (f := fun t ↦ (v t : ℂ)) (Complex.continuousAt_arg hslit)
    (continuous_subtype_val.comp hv).continuousAt

/-! ### The 1-skeleton -/

namespace Painting

variable (Γ : Painting S)

omit [T2Space S] in
theorem bd_subset_skU : bd S ⊆ Γ.skU := by
  intro x hx
  by_cases hV : x ∈ Γ.V
  · exact Or.inl (Or.inl hV)
  have hm : x ∈ Γ.U \ Γ.V := ⟨Γ.bd_subset hx, hV⟩
  have hc : pathComponentIn (Γ.U \ Γ.V) x ∈ Γ.E := Surface.mem_arcComponentsIn_of_mem hm
  have hxc : x ∈ pathComponentIn (Γ.U \ Γ.V) x := mem_pathComponentIn_self hm
  have h2 := size_two_of_border Γ hc ⟨x, hxc, hx⟩
  exact Or.inl (Or.inr (mem_iUnion₂.2 ⟨_, ⟨hc, h2⟩, hxc⟩))

theorem isClosed_skU : IsClosed Γ.skU := by
  obtain ⟨D, h₁, -⟩ := Γ.exists_skDrawing
  exact h₁ ▸ D.isClosed_U

omit [T2Space S] in
/-- An edge of size 2 is an arc-wise component of the 1-skeleton without the vertices. -/
theorem two_mem_sk {e : Set S} (he : e ∈ Γ.E) (h2 : (tilde e).ncard = 2) :
    e ∈ arcComponentsIn (Γ.skU \ Γ.V) := by
  refine ⟨he.1, fun x hx ↦ ⟨Or.inl (Or.inr (mem_iUnion₂.2 ⟨e, ⟨he, h2⟩, hx⟩)), Γ.disjoint_V he hx⟩,
    he.2.2.1, fun D hD hc hsub ↦ ?_⟩
  exact he.2.2.2 D (hD.trans (sdiff_subset_sdiff_left Γ.skU_subset)) hc hsub

omit [T2Space S] in
theorem sk_cases {e : Set S} (he : e ∈ arcComponentsIn (Γ.skU \ Γ.V)) :
    (e ∈ Γ.E ∧ (tilde e).ncard = 2) ∨
      ∃ c ∈ Γ.E, (tilde c).ncard = 3 ∧ e ⊆ c ∧ e ⊆ discBd (closure c) := by
  obtain ⟨c, hc, hsub⟩ := exists_arcComp_superset he.2.2.1
    (he.2.1.trans (sdiff_subset_sdiff_left Γ.skU_subset))
  rcases Γ.size_cases hc with h2 | h3
  · left
    have heq : e = c := arcComp_eq_of_mem he (Γ.two_mem_sk hc h2) (he.1.some_mem)
      (hsub he.1.some_mem)
    exact heq ▸ ⟨hc, h2⟩
  · exact Or.inr ⟨c, hc, h3, hsub, fun x hx ↦ Γ.mem_discBd_of_skU hc h3 (hsub hx) (he.2.1 hx).1⟩

/-- An edge of the 1-skeleton is the inside of a line with two vertices as its ends. -/
theorem sk_line {e : Set S} (he : e ∈ arcComponentsIn (Γ.skU \ Γ.V)) :
    ∃ u v, u ≠ v ∧ tilde e = {u, v} ∧ tilde e ⊆ Γ.V ∧ IsLineWithEnds (closure e) u v := by
  obtain ⟨D, hU, hV⟩ := Γ.exists_skDrawing
  have he' : e ∈ arcComponentsIn (D.U \ D.V) := by rw [hU, hV]; exact he
  have hline : ∃ u v, u ≠ v ∧ closure e ∩ Γ.V = {u, v} ∧ IsLineWithEnds (closure e) u v := by
    rcases D.edge_cond e he' with ⟨u, v, h₁, h₂, h₃⟩ | ⟨u, h₁, h₂⟩
    · exact ⟨u, v, h₁, hV ▸ h₂, h₃⟩
    · exfalso
      rw [hV] at h₁
      rcases Γ.sk_cases he with ⟨h, h2⟩ | ⟨c, hc, h3, hsub, hbd⟩
      · have := h₁ ▸ Γ.closure_inter_V h
        have hcard : ({u} : Set S).ncard = 2 := by rw [this]; exact h2
        simp at hcard
      · obtain ⟨hdisc, hT, hfin⟩ := Γ.isDisc_of_three hc h3
        have hF := hdisc.isOArc_discBd
        have hsub' : closure e ⊆ discBd (closure c) :=
          closure_minimal hbd (IsOArc.isCompact hF).isClosed
        obtain ⟨w, hw, hne⟩ : ∃ w ∈ tilde c, w ≠ u := by
          by_contra hn
          push Not at hn
          have : tilde c ⊆ {u} := hn
          have := ncard_le_ncard this (finite_singleton u)
          simp at this
          omega
        refine not_oArc_subset h₂ hF hsub' (hT hw) fun hwe ↦ hne ?_
        have : w ∈ closure e ∩ Γ.V := ⟨hwe, Γ.tilde_subset_V hc hw⟩
        rw [h₁] at this
        exact this
  obtain ⟨u, v, huv, hset, hL⟩ := hline
  suffices h : tilde e = {u, v} from
    ⟨u, v, huv, h, by rw [h, ← hset]; exact inter_subset_right, hL⟩
  obtain ⟨-, hpc, -, -⟩ := GM20.line_facts hL
  have hsub : e ⊆ closure e \ {u, v} := fun x hx ↦ ⟨subset_closure hx, fun hm ↦ by
    rw [← hset] at hm
    exact (he.2.1 hx).2 hm.2⟩
  have hin : closure e \ {u, v} ⊆ Γ.skU \ Γ.V := fun x hx ↦ by
    refine ⟨closure_minimal (he.2.1.trans sdiff_subset) Γ.isClosed_skU hx.1, fun hV' ↦ hx.2 ?_⟩
    rw [← hset]
    exact ⟨hx.1, hV'⟩
  have heq : closure e \ {u, v} = e := he.2.2.2 _ hin hpc hsub
  rw [tilde, ← hset]
  ext x
  constructor
  · rintro ⟨hx, hxe⟩
    by_contra hn
    exact hxe (heq ▸ ⟨hx, fun h ↦ hn (hset ▸ h)⟩)
  · rintro ⟨hx, hxV⟩
    exact ⟨hx, fun h ↦ (he.2.1 h).2 hxV⟩

theorem sk_size {e : Set S} (he : e ∈ arcComponentsIn (Γ.skU \ Γ.V)) :
    (tilde e).ncard = 2 ∧ (tilde e).Finite := by
  obtain ⟨u, v, huv, ht, -, -⟩ := Γ.sk_line he
  exact ⟨by rw [ht, ncard_pair huv], by rw [ht]; exact (finite_singleton v).insert u⟩

end Painting

/-! ### The small discs -/

/-- `Δ` picks a small disc in each edge of size 3 (Graph Minors XIX, page 330: "choose a disc
$\Delta\subseteq \bar{e}$ with $\Delta\cap bd(\bar{e})=\tilde{e}$"). -/
def IsCore (Γ : Painting S) (Δ : Set S → Set S) : Prop :=
  ∀ c ∈ Γ.E, (tilde c).ncard = 3 → IsClosedDisc (Δ c) ∧ Δ c ⊆ closure c ∧ tilde c ⊆ discBd (Δ c) ∧
    Δ c ∩ discBd (closure c) = tilde c

/-- The new edge inside `c`. -/
def core (Δ : Set S → Set S) (c : Set S) : Set S := Δ c \ tilde c

/-- The march of a line: any order of its ends. -/
noncomputable def anyMarch (e : Set S) : List S :=
  open Classical in if h : (tilde e).Finite then h.toFinset.toList else []

omit [T2Space S] in
theorem anyMarch_set {e : Set S} (h : (tilde e).Finite) : {v | v ∈ anyMarch e} = tilde e := by
  ext x
  simp [anyMarch, h]

omit [T2Space S] in
theorem anyMarch_nodup (e : Set S) : (anyMarch e).Nodup := by
  classical
  unfold anyMarch
  split_ifs
  · exact Finset.nodup_toList _
  · exact List.nodup_nil

section Thin

variable {Γ : Painting S} {Δ : Set S → Set S}

omit [T2Space S] in
theorem IsCore.core_subset (hΔ : IsCore Γ Δ) {c : Set S} (hc : c ∈ Γ.E) (h3 : (tilde c).ncard = 3) :
    core Δ c ⊆ c := by
  rintro x ⟨hx, hn⟩
  by_contra hxc
  exact hn ⟨(hΔ c hc h3).2.1 hx, hxc⟩

omit [T2Space S] in
theorem IsCore.isPathConnected (hΔ : IsCore Γ Δ) {c : Set S} (hc : c ∈ Γ.E)
    (h3 : (tilde c).ncard = 3) : IsPathConnected (core Δ c) :=
  isPathConnected_disc_sdiff (hΔ c hc h3).1 (hΔ c hc h3).2.2.1

theorem IsCore.closure_core (hΔ : IsCore Γ Δ) {c : Set S} (hc : c ∈ Γ.E)
    (h3 : (tilde c).ncard = 3) : closure (core Δ c) = Δ c :=
  closure_disc_sdiff (hΔ c hc h3).1 (hΔ c hc h3).2.2.1

theorem IsCore.tilde_core (hΔ : IsCore Γ Δ) {c : Set S} (hc : c ∈ Γ.E)
    (h3 : (tilde c).ncard = 3) : tilde (core Δ c) = tilde c := by
  rw [tilde, hΔ.closure_core hc h3]
  ext x
  constructor
  · rintro ⟨hx, hn⟩
    by_contra hxc
    exact hn ⟨hx, hxc⟩
  · intro hx
    exact ⟨discBd_subset _ ((hΔ c hc h3).2.2.1 hx), fun h ↦ h.2 hx⟩

/-- The pieces of the narrow painting. -/
def pieces (Γ : Painting S) (Δ : Set S → Set S) : Set (Set S) :=
  arcComponentsIn (Γ.skU \ Γ.V) ∪ core Δ '' {c ∈ Γ.E | (tilde c).ncard = 3}

/-- The closed set of the narrow painting. -/
def thinU (Γ : Painting S) (Δ : Set S → Set S) : Set S :=
  Γ.skU ∪ ⋃ c ∈ {c ∈ Γ.E | (tilde c).ncard = 3}, Δ c

theorem finite_pieces : (pieces Γ Δ).Finite := by
  obtain ⟨D, hU, hV⟩ := Γ.exists_skDrawing
  have hfinite : {c ∈ Γ.E | (tilde c).ncard = 3}.Finite :=
    Γ.finite_edges.subset fun _ h => h.1
  refine Finite.union ?_ (hfinite.image _)
  have := D.finite_edges
  rwa [hU, hV] at this

omit [T2Space S] in
theorem disjoint_sk_core (hΔ : IsCore Γ Δ) {e c : Set S} (he : e ∈ arcComponentsIn (Γ.skU \ Γ.V))
    (hc : c ∈ Γ.E) (h3 : (tilde c).ncard = 3) : Disjoint e (core Δ c) := by
  refine disjoint_left.mpr fun x hxe hxc ↦ ?_
  have hb := Γ.mem_discBd_of_skU hc h3 (hΔ.core_subset hc h3 hxc) (he.2.1 hxe).1
  have : x ∈ Δ c ∩ discBd (closure c) := ⟨hxc.1, hb⟩
  rw [(hΔ c hc h3).2.2.2] at this
  exact hxc.2 this

theorem pieces_eq (hΔ : IsCore Γ Δ) : arcComponentsIn (thinU Γ Δ \ Γ.V) = pieces Γ Δ := by
  have hpc : ∀ p ∈ pieces Γ Δ, IsPathConnected p := by
    rintro p (hp | ⟨c, hc, rfl⟩)
    · exact hp.2.2.1
    · exact hΔ.isPathConnected hc.1 hc.2
  refine arcComponentsIn_of_pieces finite_pieces hpc ?_ ?_ ?_
  · rintro p (hp | ⟨c, hc, rfl⟩) q (hq | ⟨c', hc', rfl⟩) hne
    · exact disjoint_iff_forall_ne.mpr fun x hx y hy he ↦ hne
        (arcComp_eq_of_mem hp hq hx (he ▸ hy))
    · exact disjoint_sk_core hΔ hp hc'.1 hc'.2
    · exact (disjoint_sk_core hΔ hq hc.1 hc.2).symm
    · refine disjoint_iff_forall_ne.mpr fun x hx y hy he ↦ hne ?_
      have := arcComp_eq_of_mem hc.1 hc'.1 (hΔ.core_subset hc.1 hc.2 hx)
        (hΔ.core_subset hc'.1 hc'.2 (he ▸ hy))
      rw [this]
  · rintro p (hp | ⟨c, hc, rfl⟩) x ⟨hx, hxW⟩
    · obtain ⟨u, v, -, -, htl, -⟩ := Γ.sk_line hp
      by_contra hn
      exact hxW.2 (htl ⟨hx, hn⟩)
    · rw [hΔ.closure_core hc.1 hc.2] at hx
      exact ⟨hx, fun h ↦ hxW.2 (Γ.tilde_subset_V hc.1 h)⟩
  · ext x
    constructor
    · rintro ⟨hx | hx, hV⟩
      · exact ⟨_, Or.inl (Surface.mem_arcComponentsIn_of_mem ⟨hx, hV⟩),
          mem_pathComponentIn_self ⟨hx, hV⟩⟩
      · obtain ⟨c, hc, hxc⟩ := mem_iUnion₂.mp hx
        exact ⟨_, Or.inr ⟨c, hc, rfl⟩, hxc, fun h ↦ hV (Γ.tilde_subset_V hc.1 h)⟩
    · rintro ⟨p, hp | ⟨c, hc, rfl⟩, hx⟩
      · exact ⟨Or.inl (hp.2.1 hx).1, (hp.2.1 hx).2⟩
      · exact ⟨Or.inr (mem_biUnion hc hx.1), Γ.disjoint_V hc.1 (hΔ.core_subset hc.1 hc.2 hx)⟩

/-- The march of an edge of the narrow painting. On edges of size 3 and edges of `Γ` it is what we
want. -/
noncomputable def thinγ (Γ : Painting S) (Δ : Set S → Set S) (g : Set S → List S)
  (e : Set S) : List S :=
  open Classical in
  if h : ∃ c ∈ Γ.E, (tilde c).ncard = 3 ∧ core Δ c = e then Γ.γ h.choose
  else if e ∈ Γ.E then g e else anyMarch e

omit [T2Space S] in
theorem core_injOn (hΔ : IsCore Γ Δ) : InjOn (core Δ) {c ∈ Γ.E | (tilde c).ncard = 3} := by
  intro c hc c' hc' he
  obtain ⟨x, hx⟩ := (hΔ.isPathConnected hc.1 hc.2).nonempty
  exact arcComp_eq_of_mem hc.1 hc'.1 (hΔ.core_subset hc.1 hc.2 hx)
    (hΔ.core_subset hc'.1 hc'.2 (he ▸ hx))

omit [T2Space S] in
theorem thinγ_core (hΔ : IsCore Γ Δ) (g : Set S → List S) {c : Set S} (hc : c ∈ Γ.E)
    (h3 : (tilde c).ncard = 3) : thinγ Γ Δ g (core Δ c) = Γ.γ c := by
  have h : ∃ c' ∈ Γ.E, (tilde c').ncard = 3 ∧ core Δ c' = core Δ c := ⟨c, hc, h3, rfl⟩
  rw [thinγ, dite_eq_left h]
  obtain ⟨h₁, h₂, h₃⟩ := h.choose_spec
  rw [core_injOn hΔ ⟨h₁, h₂⟩ ⟨hc, h3⟩ h₃]

omit [T2Space S] in
theorem not_core_of_two (hΔ : IsCore Γ Δ) {e : Set S} (he : e ∈ arcComponentsIn (Γ.skU \ Γ.V)) :
    ¬ ∃ c ∈ Γ.E, (tilde c).ncard = 3 ∧ core Δ c = e := by
  rintro ⟨c, hc, h3, rfl⟩
  obtain ⟨x, hx⟩ := (hΔ.isPathConnected hc h3).nonempty
  exact disjoint_left.mp (disjoint_sk_core hΔ he hc h3) hx hx

omit [T2Space S] in
theorem thinγ_two (hΔ : IsCore Γ Δ) (g : Set S → List S) {e : Set S} (he : e ∈ Γ.E)
    (h2 : (tilde e).ncard = 2) : thinγ Γ Δ g e = g e := by
  rw [thinγ, dite_eq_right (not_core_of_two hΔ (Γ.two_mem_sk he h2)), ite_eq_left he]

omit [T2Space S] in
theorem thinγ_new (hΔ : IsCore Γ Δ) (g : Set S → List S) {e : Set S}
    (he : e ∈ arcComponentsIn (Γ.skU \ Γ.V)) (hn : e ∉ Γ.E) : thinγ Γ Δ g e = anyMarch e := by
  rw [thinγ, dite_eq_right (not_core_of_two hΔ he), ite_eq_right hn]

/-- The narrow painting of `Γ`, with march `g` on edges of size 2 that stay. -/
noncomputable def thinP (hΔ : IsCore Γ Δ) (g : Set S → List S)
    (hg : ∀ e ∈ Γ.E, (tilde e).ncard = 2 → g e = Γ.γ e ∨ g e = (Γ.γ e).reverse) : Painting S where
  U := thinU Γ Δ
  V := Γ.V
  γ := thinγ Γ Δ g
  isClosed_U := by
    refine Γ.isClosed_skU.union ?_
    have hfinite : {c ∈ Γ.E | (tilde c).ncard = 3}.Finite :=
      Γ.finite_edges.subset fun _ h => h.1
    refine hfinite.isClosed_biUnion fun c hc ↦ ?_
    exact (hΔ c hc.1 hc.2).1.isClosed
  V_subset := fun x hx ↦ Or.inl (Or.inl (Or.inl hx))
  finite_V := Γ.finite_V
  bd_subset := fun x hx ↦ Or.inl (Γ.bd_subset_skU hx)
  finite_edges := by
    rw [pieces_eq hΔ]
    exact finite_pieces
  edge_shape := by
    rw [pieces_eq hΔ]
    rintro e (he | ⟨c, hc, rfl⟩)
    · obtain ⟨u, v, huv, ht, -, hL⟩ := Γ.sk_line he
      left
      obtain ⟨f, hf⟩ := id hL
      refine ⟨by rw [ht, ncard_pair huv], by rw [ht]; exact (finite_singleton v).insert u, ⟨f⟩, ?_⟩
      rw [ht]
      exact (GM20.line_facts hL).2.2.2
    · right
      rw [hΔ.tilde_core hc.1 hc.2, hΔ.closure_core hc.1 hc.2]
      exact ⟨hc.2, (Γ.isDisc_of_three hc.1 hc.2).2.2, (hΔ c hc.1 hc.2).1, (hΔ c hc.1 hc.2).2.2.1⟩
  γ_nodup := by
    rw [pieces_eq hΔ]
    rintro e (he | ⟨c, hc, rfl⟩)
    · by_cases hE : e ∈ Γ.E
      · rw [thinγ_two hΔ g hE (Γ.sk_size he).1]
        rcases hg e hE (Γ.sk_size he).1 with h | h
        · exact h ▸ Γ.γ_nodup e hE
        · exact h ▸ List.nodup_reverse.mpr (Γ.γ_nodup e hE)
      · rw [thinγ_new hΔ g he hE]
        exact anyMarch_nodup _
    · rw [thinγ_core hΔ g hc.1 hc.2]
      exact Γ.γ_nodup c hc.1
  γ_set := by
    rw [pieces_eq hΔ]
    rintro e (he | ⟨c, hc, rfl⟩)
    · by_cases hE : e ∈ Γ.E
      · rw [thinγ_two hΔ g hE (Γ.sk_size he).1]
        rcases hg e hE (Γ.sk_size he).1 with h | h
        · rw [h]
          exact Γ.γ_set e hE
        · rw [h]
          simpa using Γ.γ_set e hE
      · rw [thinγ_new hΔ g he hE]
        exact anyMarch_set (Γ.sk_size he).2
    · rw [thinγ_core hΔ g hc.1 hc.2, hΔ.tilde_core hc.1 hc.2]
      exact Γ.γ_set c hc.1
  border_edge := by
    rw [pieces_eq hΔ]
    rintro e (he | ⟨c, hc, rfl⟩) hb
    · refine ⟨(Γ.sk_size he).1, ?_⟩
      obtain ⟨x, hxe, hxb⟩ := id hb
      rcases Γ.sk_cases he with ⟨h, -⟩ | ⟨c, hc, h3, hsub, -⟩
      · exact (Γ.border_edge e h hb).2
      · have := size_two_of_border Γ hc ⟨x, hsub hxe, hxb⟩
        omega
    · obtain ⟨x, hxe, hxb⟩ := id hb
      have := size_two_of_border Γ hc.1 ⟨x, hΔ.core_subset hc.1 hc.2 hxe, hxb⟩
      have := hc.2
      omega

end Thin

end GraphMinor.GM19
