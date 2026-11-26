/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM07.NetExistsGlue
public import LeanPool.GraphMinor.GM07.NetExistsHole
public import LeanPool.GraphMinor.GM07.NetExistsFamily

/-!
# From a cut surface to one polygon

`IsNetCut` is the surface `Y` got by cutting `S` along finitely many paths. Each component of `Y`
has a polygon whose free sides are the
lifts of the paths (`exists_comp_word`). Give the two lifts of a path one label. These polygons
present `S`, and each point of the
open paths is on an open side with such a label. Then `exists_off_word` pastes them into one polygon
whose sides avoid a given set of
points of the open paths (`exists_off_word_of_cut`). These are steps 1 to 3 of the sketch in Graph
Minors VII, page 216.
-/

@[expose] public section

namespace GraphMinor.GM07

open Set Topology Metric GraphMinor.Surface

universe u

/-- `ψ : Y → S` cuts `S` along the paths `a κ`, and `ξ κ`, `η κ` are the two lifts of the path `a
κ`. A path that is not inner has one lift.
The paths may be closed. A point inside a path is on no other path, and it is not an end of its own
path. -/
structure IsNetCut {S Y κ : Type*} [TopologicalSpace S] [TopologicalSpace Y] (a : κ → ℝ → S)
  (inner : κ → Prop) (ψ : Y → S) (ξ η : κ → ℝ → Y) : Prop where
  cont : Continuous ψ
  surj : Function.Surjective ψ
  cξ : ∀ k, ContinuousOn (ξ k) (Icc 0 1)
  cη : ∀ k, ContinuousOn (η k) (Icc 0 1)
  hξ : ∀ k, ∀ u ∈ Icc (0 : ℝ) 1, ψ (ξ k u) = a k u
  hη : ∀ k, ∀ u ∈ Icc (0 : ℝ) 1, ψ (η k u) = a k u
  bdξ : ∀ k, ∀ u ∈ Icc (0 : ℝ) 1, ξ k u ∈ bd Y
  bdη : ∀ k, ∀ u ∈ Icc (0 : ℝ) 1, η k u ∈ bd Y
  ne : ∀ k, inner k → ∀ u ∈ Ioo (0 : ℝ) 1, ξ k u ≠ η k u
  eqb : ∀ k, ¬ inner k → ∀ u ∈ Icc (0 : ℝ) 1, η k u = ξ k u
  cover : ∀ y ∈ bd Y, ∃ k, ∃ u ∈ Icc (0 : ℝ) 1, y = ξ k u ∨ y = η k u
  fib : ∀ y y', ψ y = ψ y' → Relation.EqvGen (fun p q ↦ ∃ k, ∃ u ∈ Icc (0 : ℝ) 1, p = ξ k u ∧ q
    = η k u) y y'
  inj : ∀ k, InjOn (a k) (Ioo 0 1)
  meet : ∀ k k', k ≠ k' → ∀ u ∈ Ioo (0 : ℝ) 1, ∀ v ∈ Icc (0 : ℝ) 1, a k u ≠ a k' v
  self : ∀ k, ∀ u ∈ Ioo (0 : ℝ) 1, a k u ≠ a k 0 ∧ a k u ≠ a k 1

/-- The lifts of the paths, with one lift for a path that is not inner. -/
abbrev NetArc {κ : Type*} (inner : κ → Prop) := {x : κ × Bool // x.2 = true ∨ inner x.1}

/-- The lift with index `x`. -/
def netL {κ Y : Type*} {inner : κ → Prop} (ξ η : κ → ℝ → Y) (x : NetArc inner) (u : ℝ) : Y
  := if x.1.2 then ξ x.1.1 u else η x.1.1 u

section cut

variable {S Y κ : Type*} [TopologicalSpace S] [TopologicalSpace Y] {a : κ → ℝ → S} {inner : κ
  → Prop} {ψ : Y → S} {ξ η : κ → ℝ → Y}

theorem IsNetCut.ψ_netL (h : IsNetCut a inner ψ ξ η) (x : NetArc inner) {u : ℝ} (hu : u ∈ Icc
  (0 : ℝ) 1) : ψ (netL ξ η x u) = a x.1.1 u := by
  obtain ⟨⟨k, _ | _⟩, hx⟩ := x
  · exact h.hη k u hu
  · exact h.hξ k u hu

theorem IsNetCut.isArcFamily (h : IsNetCut a inner ψ ξ η) : IsArcFamily (netL ξ η (inner := inner))
  := by
  have h0 : (0 : ℝ) ∈ Icc (0 : ℝ) 1 := by simp
  have h1 : (1 : ℝ) ∈ Icc (0 : ℝ) 1 := by simp
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rintro ⟨⟨k, _ | _⟩, hx⟩
    · exact h.cη k
    · exact h.cξ k
  · intro x u hu v hv he
    refine h.inj x.1.1 hu hv ?_
    rw [← h.ψ_netL x ⟨hu.1.le, hu.2.le⟩, ← h.ψ_netL x ⟨hv.1.le, hv.2.le⟩, he]
  · rintro ⟨⟨k, _ | _⟩, hx⟩ u hu
    · exact h.bdη k u hu
    · exact h.bdξ k u hu
  · intro x y hne u hu v hv he
    have h2 : a x.1.1 u = a y.1.1 v := by
      rw [← h.ψ_netL x ⟨hu.1.le, hu.2.le⟩, ← h.ψ_netL y ⟨hv.1.le, hv.2.le⟩, he]
    obtain ⟨⟨k, b⟩, hx⟩ := x
    obtain ⟨⟨k', b'⟩, hy⟩ := y
    simp only at h2
    obtain rfl : k = k' := by
      by_contra hk
      exact h.meet k k' hk u hu v ⟨hv.1.le, hv.2.le⟩ h2
    obtain rfl := h.inj k hu hv h2
    cases b <;> cases b'
    · exact hne rfl
    · exact h.ne k (hx.resolve_left (by simp)) u hu he.symm
    · exact h.ne k (hy.resolve_left (by simp)) u hu he
    · exact hne rfl
  · intro x y u hu
    have key : ∀ v ∈ ({0, 1} : Set ℝ), netL ξ η x u ≠ netL ξ η y v := by
      intro v hv he
      have hv' : v ∈ Icc (0 : ℝ) 1 := by
        rcases hv with rfl | rfl
        · exact h0
        · exact h1
      have h2 : a x.1.1 u = a y.1.1 v := by
        rw [← h.ψ_netL x ⟨hu.1.le, hu.2.le⟩, ← h.ψ_netL y hv', he]
      by_cases hk : x.1.1 = y.1.1
      · rw [← hk] at h2
        rcases hv with rfl | rfl
        · exact (h.self _ u hu).1 h2
        · exact (h.self _ u hu).2 h2
      · exact h.meet _ _ hk u hu v hv' h2
    exact ⟨key 0 (by simp), key 1 (by simp)⟩
  · intro y hy
    obtain ⟨k, u, hu, rfl | rfl⟩ := h.cover y hy
    · exact ⟨⟨(k, true), .inl rfl⟩, u, hu, rfl⟩
    · by_cases hi : inner k
      · exact ⟨⟨(k, false), .inr hi⟩, u, hu, rfl⟩
      · exact ⟨⟨(k, true), .inl rfl⟩, u, hu, h.eqb k hi u hu⟩

/-- Over a point inside a path there are only the two lifts. -/
theorem IsNetCut.over_interior (h : IsNetCut a inner ψ ξ η) {k : κ} {u : ℝ} (hu : u ∈ Ioo
  (0 : ℝ) 1) {y : Y} (hy : ψ y = a k u) :
    y = ξ k u ∨ y = η k u := by
  have hu' : u ∈ Icc (0 : ℝ) 1 := ⟨hu.1.le, hu.2.le⟩
  have hsame : ∀ k' (u' : ℝ), u' ∈ Icc (0 : ℝ) 1 → a k' u' = a k u → k' = k ∧ u' = u := by
    intro k' u' h1 h2
    obtain rfl : k' = k := by
      by_contra hne
      exact h.meet k k' (Ne.symm hne) u hu u' h1 h2.symm
    refine ⟨rfl, ?_⟩
    rcases eq_or_lt_of_le h1.1 with rfl | h3
    · exact absurd h2.symm (h.self k' u hu).1
    rcases eq_or_lt_of_le h1.2 with rfl | h4
    · exact absurd h2.symm (h.self k' u hu).2
    exact h.inj k' ⟨h3, h4⟩ hu h2
  have key : ∀ p q, Relation.EqvGen (fun p q ↦ ∃ k, ∃ u ∈ Icc (0 : ℝ) 1, p = ξ k u ∧ q = η k u) p q
    →
      ((p = ξ k u ∨ p = η k u) ↔ (q = ξ k u ∨ q = η k u)) := by
    intro p q hr
    induction hr with
    | rel p q hs =>
      obtain ⟨k', u', h1, rfl, rfl⟩ := hs
      constructor
      · intro hp
        have h2 : a k' u' = a k u := by
          rw [← h.hξ k' u' h1]
          rcases hp with hp | hp
          · rw [hp, h.hξ k u hu']
          · rw [hp, h.hη k u hu']
        obtain ⟨rfl, rfl⟩ := hsame k' u' h1 h2
        exact .inr rfl
      · intro hp
        have h2 : a k' u' = a k u := by
          rw [← h.hη k' u' h1]
          rcases hp with hp | hp
          · rw [hp, h.hξ k u hu']
          · rw [hp, h.hη k u hu']
        obtain ⟨rfl, rfl⟩ := hsame k' u' h1 h2
        exact .inl rfl
    | refl _ => rfl
    | symm _ _ _ ih => exact ih.symm
    | trans _ _ _ _ _ h1 h2 => exact h1.trans h2
  exact (key _ _ (h.fib (ξ k u) y (by rw [h.hξ k u hu', hy]))).mp (.inl rfl)

end cut

theorem exists_comp_reps {Y : Type u} [TopologicalSpace Y] (hY : IsSurface Y) (y₀ : Y) : ∃ (r : ℕ)
  (rep : ℕ → Y), 0 < r ∧
    (∀ i j, i < r → j < r → i ≠ j → Disjoint (connectedComponent (rep i)) (connectedComponent
      (rep j))) ∧
    ∀ y, ∃ j < r, y ∈ connectedComponent (rep j) := by
  classical
  have : LocallyConnectedSpace Y := hY.locallyConnected
  have : CompactSpace Y := hY.1
  have hfin : Finite (ConnectedComponents Y) := by
    obtain ⟨T, hT⟩ := isCompact_univ.elim_finite_subcover (fun x : Y ↦ connectedComponent x)
      (fun x ↦ isOpen_connectedComponent) (fun x _ ↦ mem_iUnion.mpr ⟨x, mem_connectedComponent⟩)
    refine Finite.of_surjective (fun t : T ↦ (ConnectedComponents.mk t.1 : ConnectedComponents Y))
      fun c ↦ ?_
    obtain ⟨z, rfl⟩ := ConnectedComponents.surjective_coe c
    obtain ⟨t, ht, hzt⟩ := mem_iUnion₂.mp (hT (mem_univ z))
    exact ⟨⟨t, ht⟩, ConnectedComponents.coe_eq_coe'.2 hzt |>.symm⟩
  obtain ⟨r, ⟨e⟩⟩ := Finite.exists_equiv_fin (ConnectedComponents Y)
  have hsurj := ConnectedComponents.surjective_coe (α := Y)
  set rep : ℕ → Y := fun j => if h : j < r then Function.surjInv hsurj
    (e.symm ⟨j, h⟩) else y₀ with hrep
  have hmk : ∀ j (h : j < r), ConnectedComponents.mk (rep j) = e.symm ⟨j, h⟩ := fun j h => by
    simp only [hrep, dite_eq_left h]
    exact Function.surjInv_eq hsurj _
  refine ⟨r, rep, (e (ConnectedComponents.mk y₀)).2.pos, fun i j hi hj hij => ?_, fun y => ?_⟩
  · refine connectedComponent_disjoint fun he => hij ?_
    have h1 := ConnectedComponents.coe_eq_coe.mpr he
    rw [hmk i hi, hmk j hj] at h1
    simpa using e.symm.injective h1
  · have hj := (e (ConnectedComponents.mk y)).2
    refine ⟨_, hj, ?_⟩
    have h1 := hmk _ hj
    rw [Equiv.symm_apply_apply] at h1
    rw [ConnectedComponents.coe_eq_coe.mp h1]
    exact mem_connectedComponent

theorem relab_sW (r : ℕ → ℕ) (w : List Letter) : relab r (sW w) = sW (w.map fun l => (r l.1, l.2))
  := by
  funext i
  by_cases hi : i = 0
  · subst hi
    simp [relab, sW_zero]
  · simp [relab, sW, hi, nW]

theorem cnt_map_inj {r : ℕ → ℕ} (hr : Function.Injective r) (w : List Letter) (k : ℕ) : cnt
  (w.map fun l => (r l.1, l.2)) (r k) = cnt w k := by
  induction w with
  | nil => rfl
  | cons x w ih =>
    rw [List.map_cons, cnt_cons, cnt_cons, ih]
    simp only [hr.eq_iff]

section comp

variable {Y : Type u} [TopologicalSpace Y] [T2Space Y] {ι : Type*} [Finite ι] {ℓ : ι → ℝ → Y}

/-- The polygon of a component of a surface. Its labels are coded with the number `M`, so that
polygons of different components have no
label in common. -/
theorem exists_comp_word (hY : IsSurface Y) (hfam : IsArcFamily ℓ) {C : Set Y} (hC : IsClopen C)
  (hconn : IsConnected C) (M : ℕ) :
    ∃ (w : List Letter) (g : ℕ × ℂ → Y), 2 ≤ w.length ∧ Good w ∧ (∀ l ∈ w, (Nat.unpair l.1).1 = M)
      ∧ ContinuousOn g (Dsk (sW w)) ∧
      g '' Dsk (sW w) = C ∧ (∀ a ∈ Dsk (sW w), ∀ b ∈ Dsk (sW w), g a = g b ↔ PRel (sW w) a b) ∧
      ∀ α, ℓ α 0 ∈ C → ∃ k σ, cnt w k = 1 ∧ SideVal (sW w) g k (fun u => ℓ α (ofs σ u)) := by
  classical
  have hsub : ∀ α : {α // ℓ α 0 ∈ C}, ∀ u ∈ Icc (0 : ℝ) 1, ℓ α.1 u ∈ C := fun α u hu => by
    have h1 : IsPreconnected (ℓ α.1 '' Icc 0 1) := isPreconnected_Icc.image _ (hfam.cont α.1)
    exact h1.subset_isClopen hC ⟨_, ⟨0, by simp, rfl⟩, α.2⟩ ⟨u, hu, rfl⟩
  set ℓ' : {α // ℓ α 0 ∈ C} → ℝ → C := fun α u => if h : ℓ α.1 u ∈ C then ⟨_, h⟩ else ⟨_, α.2⟩ with
    hℓ'
  have hval : ∀ α, ∀ u ∈ Icc (0 : ℝ) 1, (ℓ' α u).1 = ℓ α.1 u := fun α u hu => by
    simp only [hℓ', dite_eq_left (hsub α u hu)]
  have h0 : (0 : ℝ) ∈ Icc (0 : ℝ) 1 := by simp
  have h1 : (1 : ℝ) ∈ Icc (0 : ℝ) 1 := by simp
  have hIoo : ∀ {u : ℝ}, u ∈ Ioo (0 : ℝ) 1 → u ∈ Icc (0 : ℝ) 1 := fun hu => ⟨hu.1.le, hu.2.le⟩
  have hfam' : IsArcFamily ℓ' := by
    refine ⟨fun α => ?_, fun α u hu v hv he => ?_, fun α u hu => ?_, fun α β hne u hu v hv he
      => ?_, fun α β u hu => ⟨fun he => ?_, fun he => ?_⟩, fun x hx => ?_⟩
    · rw [IsEmbedding.subtypeVal.isInducing.continuousOn_iff]
      exact (hfam.cont α.1).congr fun u hu => hval α u hu
    · refine hfam.inj α.1 hu hv ?_
      rw [← hval α u (hIoo hu), ← hval α v (hIoo hv), he]
    · rw [mem_bd_sub hC.isOpen, hval α u hu]
      exact hfam.mem _ _ hu
    · refine hfam.disj α.1 β.1 (fun h => hne (Subtype.ext h)) u hu v hv ?_
      rw [← hval α u (hIoo hu), ← hval β v (hIoo hv), he]
    · refine (hfam.off α.1 β.1 u hu).1 ?_
      rw [← hval α u (hIoo hu), ← hval β 0 h0, he]
    · refine (hfam.off α.1 β.1 u hu).2 ?_
      rw [← hval α u (hIoo hu), ← hval β 1 h1, he]
    · obtain ⟨α, u, hu, he⟩ := hfam.cover x.1 ((mem_bd_sub hC.isOpen).mp hx)
      have hm : ℓ α 0 ∈ C := by
        have h2 : IsPreconnected (ℓ α '' Icc 0 1) := isPreconnected_Icc.image _ (hfam.cont α)
        exact h2.subset_isClopen hC ⟨x.1, ⟨u, hu, he.symm⟩, x.2⟩ ⟨0, h0, rfl⟩
      exact ⟨⟨α, hm⟩, u, hu, Subtype.ext (by rw [hval ⟨α, hm⟩ u hu, he])⟩
  have : ConnectedSpace C := isConnected_iff_connectedSpace.mp hconn
  obtain ⟨w', g', h2, h3, h4, h5⟩ := exists_hole_word (isSurface_sub hY hC) hfam'
  have hr : Function.Injective (Nat.pair M) := fun x y h => (Nat.pair_eq_pair.mp h).2
  set w := w'.map fun l => (Nat.pair M l.1, l.2) with hw
  have h4' : Presents (sW w) g' := by
    rw [hw, ← relab_sW]
    exact (presents_relab (fun _ _ _ _ _ _ h => hr h) g').mp h4
  have hget : ∀ {p k : ℕ} {e : Bool}, w'[p]? = some (k, e) → w[p]? = some (Nat.pair M k, e)
    := fun {p k e} h => by
    rw [hw, List.getElem?_map, h]
    rfl
  have hlen : w.length = w'.length := by simp [hw]
  refine ⟨w, Subtype.val ∘ g', by omega, fun c => ?_, fun l hl => ?_,
    continuous_subtype_val.comp_continuousOn h4'.1, ?_, fun a ha b hb => ?_, fun α hα => ?_⟩
  · by_cases hc : ∃ k, Nat.pair M k = c
    · obtain ⟨k, rfl⟩ := hc
      rw [hw, cnt_map_inj hr]
      exact h3 k
    · have : cnt w c = 0 := noLab_iff_cnt.mp fun l hl he => by
        obtain ⟨l', -, rfl⟩ := List.mem_map.mp hl
        exact hc ⟨_, he⟩
      omega
  · obtain ⟨l', -, rfl⟩ := List.mem_map.mp hl
    simp
  · rw [image_comp, h4'.2.1, image_univ, Subtype.range_coe]
  · rw [← h4'.2.2 a ha b hb]
    exact Subtype.val_injective.eq_iff
  · obtain ⟨k, σ, h6, i, p, h7, h8⟩ := h5 ⟨α, hα⟩
    obtain ⟨rfl, h9⟩ := sW_get h7
    rw [sW_zero] at h8
    have hcount : cnt w (Nat.pair M k) = 1 := by
      rw [hw, cnt_map_inj hr]
      exact h6
    have hget' : (sW w 0)[p]? = some (Nat.pair M k, true) := by
      rw [sW_zero]
      exact hget h9
    refine ⟨Nat.pair M k, σ, hcount, 0, p, hget', fun u hu => ?_⟩
    rw [sW_zero, hlen, Function.comp, h8 u hu]
    exact hval _ _ (ofs_mem hu)

end comp

theorem cnt_netW {R : ℕ → ℕ × Bool} {c : ℕ} {P : Finset ℕ} (hP : ∀ k, (R k).1 = c ↔ k ∈ P) (W : ℕ
  → List Letter) (i : ℕ) :
    cnt (netW R W i) c = ∑ k ∈ P, cnt (W i) k := by
  classical
  simp only [netW]
  induction W i with
  | nil => simp [cnt]
  | cons x l ih =>
    rw [List.map_cons, cnt_cons, ih]
    simp only [cnt_cons, Finset.sum_add_distrib, Finset.sum_ite_eq]
    by_cases hx : x.1 ∈ P
    · rw [ite_eq_left ((hP _).mpr hx), ite_eq_left hx]
    · rw [ite_eq_right (fun h => hx ((hP _).mp h)), ite_eq_right hx]

theorem netFl_true (s : Bool) : netFl s true = s := by
  cases s <;> rfl

private theorem matching_word_side_labels
    {S : Type u}
    {Y : Type u}
    {κ : Type*}
    [TopologicalSpace S]
    [TopologicalSpace Y]
    {a : κ → ℝ → S}
    {inner : κ → Prop}
    {ψ : Y → S}
    {ξ : κ → ℝ → Y}
    {η : κ → ℝ → Y}
    (h : IsNetCut a inner ψ ξ η)
    (W : ℕ → List Letter)
    (G : ℕ × ℂ → Y)
    (s : NetArc inner → ℕ)
    (lb : NetArc inner → ℕ)
    (σ : NetArc inner → Bool)
    (pos : NetArc inner → ℕ)
    (hloc : ∀ (i p k : ℕ) (e : Bool), (W i)[p]? = some (k, e) → ∀ (α : NetArc inner), k = lb α → i
      = s α ∧ p = pos α ∧ e = true)
    (idx : κ → ℕ)
    (idxinj : ∀ (k k' : κ), idx k = idx k' → k = k')
    (K : NetArc inner → ℕ)
    (hK : K = fun α => 2 * idx α.1.1)
    (R : ℕ → ℕ × Bool)
    (hRlb : ∀ (α : NetArc inner), R (lb α) = (K α, σ α))
    (hRo : ∀ (k : ℕ), (∀ (α : NetArc inner), lb α ≠ k) → R k = (2 * k + 1, true))
    (hGval : ∀ (α : NetArc inner), ∀ u ∈ Icc 0 1, G (s α, sdPt (W (s α)).length (pos α) (σ α) u) =
      netL ξ η α u)
    (hcase : ∀ (k : ℕ), (∃ α, lb α = k) ∨ ∀ (α : NetArc inner), lb α ≠ k) :
    ∀ (i j p q k k' : ℕ) (e e' : Bool) (t : ℝ), (W i)[p]? = some (k, e) → (W j)[q]? = some (k',
      e') → k ≠ k' → (R k).1 = (R k').1 → t ∈ Icc 0 1 → ψ (G (i, sdPt (W i).length p (netFl (R
      k).2 e) t)) = ψ (G (j, sdPt (W j).length q (netFl (R k').2 e') t)) := by
  intro i j p q k k' e e' t h1 h2 h3 h4 ht
  rcases hcase k with ⟨α, rfl⟩ | h5 <;> rcases hcase k' with ⟨β, rfl⟩ | h6
  · obtain ⟨rfl, rfl, rfl⟩ := hloc _ _ _ _ h1 α rfl
    obtain ⟨rfl, rfl, rfl⟩ := hloc _ _ _ _ h2 β rfl
    rw [hRlb, hRlb] at h4 ⊢
    simp only [netFl_true]
    rw [hGval α t ht, hGval β t ht, h.ψ_netL α ht, h.ψ_netL β ht]
    have h7 : α.1.1 = β.1.1 := idxinj _ _ (by simpa [hK] using h4)
    rw [h7]
  · rw [hRlb, hRo _ h6] at h4
    simp only [hK] at h4
    omega
  · rw [hRlb, hRo _ h5] at h4
    simp only [hK] at h4
    omega
  · rw [hRo _ h5, hRo _ h6] at h4
    simp only at h4
    omega

private theorem cut_lift_fiber_equivalence
    {S : Type u}
    {Y : Type u}
    {κ : Type*}
    [TopologicalSpace S]
    [TopologicalSpace Y]
    {a : κ → ℝ → S}
    {inner : κ → Prop}
    {ψ : Y → S}
    {ξ : κ → ℝ → Y}
    {η : κ → ℝ → Y}
    (h : IsNetCut a inner ψ ξ η)
    (W : ℕ → List Letter)
    (G : ℕ × ℂ → Y)
    (s : NetArc inner → ℕ)
    (lb : NetArc inner → ℕ)
    (σ : NetArc inner → Bool)
    (pos : NetArc inner → ℕ)
    (hWs : ∀ (α : NetArc inner), (W (s α))[pos α]? = some (lb α, true))
    (lbinj : ∀ (α β : NetArc inner), lb α = lb β → α = β)
    (idx : κ → ℕ)
    (R : ℕ → ℕ × Bool)
    (hnet : ∀ (α : NetArc inner), (netW R W (s α))[pos α]? = some (2 * idx α.1.1, σ α))
    (hGval : ∀ (α : NetArc inner), ∀ u ∈ Icc 0 1, G (s α, sdPt (W (s α)).length (pos α) (σ α) u) =
      netL ξ η α u) :
    ∀ (y y' : Y), ψ y = ψ y' → Relation.EqvGen (fun u v => u = v ∨ ∃ a b, G a = u ∧ G b = v ∧ Stp
      (netW R W) a b) y y' := by
  intro y y' he
  suffices hmono : ∀ p q, (∃ k, ∃ u ∈ Icc (0 : ℝ) 1, p = ξ k u ∧ q = η k u) → (p = q ∨ ∃ a b, G a
    = p ∧ G b = q ∧ Stp (netW R W) a b) by
    have hr := h.fib y y' he
    clear he
    induction hr with
    | rel p q hs => exact .rel _ _ (hmono p q hs)
    | refl _ => exact .refl _
    | symm _ _ _ ih => exact .symm _ _ ih
    | trans _ _ _ _ _ h1 h2 => exact .trans _ _ _ h1 h2
  rintro _ _ ⟨k, u, hu, rfl, rfl⟩
  by_cases hi : inner k
  · refine .inr ⟨(s ⟨(k, true), .inl rfl⟩, _), (s ⟨(k, false), .inr hi⟩, _), hGval ⟨(k, true),
      .inl rfl⟩ u hu, hGval ⟨(k, false), .inr hi⟩ u hu,
      s ⟨(k, true), .inl rfl⟩, s ⟨(k, false), .inr hi⟩, pos ⟨(k, true), .inl rfl⟩, pos ⟨(k,
        false), .inr hi⟩, 2 * idx k, _, _, u, hnet ⟨(k, true), .inl rfl⟩,
      hnet ⟨(k, false), .inr hi⟩, ?_, hu,
      by rw [netW_length], by rw [netW_length]⟩
    intro he'
    obtain ⟨h1, h2⟩ := Prod.mk.inj he'
    have h3 := hWs ⟨(k, true), .inl rfl⟩
    have h4 := hWs ⟨(k, false), .inr hi⟩
    rw [← h1, ← h2] at h4
    have h5 := h3.symm.trans h4
    simp only [Option.some.injEq, Prod.mk.injEq, and_true] at h5
    have := lbinj _ _ h5
    simp at this
  · exact .inl (h.eqb k hi u hu).symm

private theorem relabeled_word_count_bound
    {κ : Type*}
    {inner : κ → Prop}
    (r : ℕ)
    (lb : NetArc inner → ℕ)
    (idx : κ → ℕ)
    (idxinj : ∀ (k k' : κ), idx k = idx k' → k = k')
    (K : NetArc inner → ℕ)
    (hK : K = fun α => 2 * idx α.1.1)
    (R : ℕ → ℕ × Bool)
    (W₁ : ℕ → List Letter)
    (L : ℕ → ℕ)
    (hL2 : ∀ (k : ℕ), L k ≤ 2)
    (hL1 : ∀ (α : NetArc inner), L (lb α) = 1)
    (hT : ∀ (P : Finset ℕ) (c : ℕ), (∀ (k : ℕ), (R k).1 = c ↔ k ∈ P) → ∑ i ∈ Finset.range r, cnt
      (W₁ i) c = ∑ k ∈ P, L k)
    (hRiff : ∀ (k c : ℕ), (R k).1 = c ↔ (∃ α, lb α = k ∧ K α = c) ∨ (∀ (α : NetArc inner), lb α ≠
      k) ∧ 2 * k + 1 = c)
    (hTi : ∀ (k : κ), inner k → ∑ i ∈ Finset.range r, cnt (W₁ i) (2 * idx k) = 2) :
    ∀ (c : ℕ), ∑ i ∈ Finset.range r, cnt (W₁ i) c ≤ 2 := by
  intro c
  by_cases h1 : ∃ α, K α = c
  · obtain ⟨⟨⟨k, b⟩, hb⟩, rfl⟩ := h1
    by_cases hi : inner k
    · simpa only [hK] using (hTi k hi).le
    · have hP' : ∀ x, (R x).1 = 2 * idx k ↔ x ∈ ({lb ⟨(k, true), .inl rfl⟩} : Finset ℕ) := by
        intro x
        rw [hRiff]
        simp only [Finset.mem_singleton]
        constructor
        · rintro (⟨⟨⟨k', b'⟩, h2⟩, rfl, h3⟩ | ⟨-, h3⟩)
          · obtain rfl : k' = k := idxinj _ _ (by simpa [hK] using h3)
            cases b'
            · exact absurd (h2.resolve_left (by simp)) hi
            · rfl
          · omega
        · rintro rfl
          exact .inl ⟨_, rfl, by simp only [hK]⟩
      rw [hK]
      simp only
      rw [hT _ _ hP', Finset.sum_singleton, hL1]
      omega
  · push Not at h1
    by_cases h2 : ∃ x, 2 * x + 1 = c ∧ ∀ α, lb α ≠ x
    · obtain ⟨x, rfl, h3⟩ := h2
      have hP' : ∀ y, (R y).1 = 2 * x + 1 ↔ y ∈ ({x} : Finset ℕ) := by
        intro y
        rw [hRiff]
        simp only [Finset.mem_singleton]
        constructor
        · rintro (⟨α, -, h4⟩ | ⟨-, h4⟩)
          · exact absurd h4 (h1 α)
          · omega
        · rintro rfl
          exact .inr ⟨h3, rfl⟩
      rw [hT _ _ hP', Finset.sum_singleton]
      exact hL2 x
    · push Not at h2
      have hP' : ∀ y, (R y).1 = c ↔ y ∈ (∅ : Finset ℕ) := by
        intro y
        rw [hRiff]
        simp only [Finset.notMem_empty, iff_false]
        rintro (⟨α, -, h4⟩ | ⟨h4, h5⟩)
        · exact h1 α h4
        · obtain ⟨α, h6⟩ := h2 y h5
          exact h4 α h6
      rw [hT _ _ hP', Finset.sum_empty]
      omega

private theorem relabeled_word_boundary_arcs
    {S : Type u}
    {Y : Type u}
    {κ : Type*}
    [TopologicalSpace S]
    [TopologicalSpace Y]
    {a : κ → ℝ → S}
    {inner : κ → Prop}
    {ψ : Y → S}
    {ξ : κ → ℝ → Y}
    {η : κ → ℝ → Y}
    (h : IsNetCut a inner ψ ξ η)
    {B : Set S}
    (hB : ∀ x ∈ B, ∃ k, inner k ∧ ∃ u ∈ Ioo 0 1, x = a k u)
    (W : ℕ → List Letter)
    (G : ℕ × ℂ → Y)
    (hP : Presents W G)
    (s : NetArc inner → ℕ)
    (lb : NetArc inner → ℕ)
    (σ : NetArc inner → Bool)
    (pos : NetArc inner → ℕ)
    (hloc : ∀ (i p k : ℕ) (e : Bool), (W i)[p]? = some (k, e) → ∀ (α : NetArc inner), k = lb α → i
      = s α ∧ p = pos α ∧ e = true)
    (hWs : ∀ (α : NetArc inner), (W (s α))[pos α]? = some (lb α, true))
    (idx : κ → ℕ)
    (K : NetArc inner → ℕ)
    (hK : K = fun α => 2 * idx α.1.1)
    (R : ℕ → ℕ × Bool)
    (W₁ : ℕ → List Letter)
    (hW₁ : W₁ = netW R W)
    (hnet : ∀ (α : NetArc inner), (W₁ (s α))[pos α]? = some (K α, σ α))
    (hGval : ∀ (α : NetArc inner), ∀ u ∈ Icc 0 1, G (s α, sdPt (W (s α)).length (pos α) (σ α) u) =
      netL ξ η α u)
    (hpair : IsPaired W)
    : OnBad ((fun k => 2 * idx k) '' {k | inner k}) B W₁ (ψ ∘ G) := by
  intro b hb hbB
  rw [hW₁, dsk_netW] at hb
  obtain ⟨k, hi, u, hu, he⟩ := hB _ hbB
  obtain ⟨α, h1, h2⟩ : ∃ α : NetArc inner, α.1.1 = k ∧ G b = netL ξ η α u := by
    rcases h.over_interior hu (y := G b) he with h3 | h3
    · exact ⟨⟨(k, true), .inl rfl⟩, rfl, h3⟩
    · exact ⟨⟨(k, false), .inr hi⟩, rfl, h3⟩
  have hu' : u ∈ Icc (0 : ℝ) 1 := ⟨hu.1.le, hu.2.le⟩
  set v := ofs (σ α) u with hv
  have hvI : v ∈ Ioo (0 : ℝ) 1 := ofs_mem_Ioo _ hu
  have hspt : spt W (s α) (pos α) v = (s α, sdPt (W (s α)).length (pos α) (σ α) u) := by
    rw [spt, hv]
    cases σ α <;> simp [sdPt, ofs]
  have hmem : spt W (s α) (pos α) v ∈ Dsk W := spt_mem (List.getElem?_eq_some_iff.mp (hWs α)).1 v
  have h3 : PRel W (spt W (s α) (pos α) v) b := (hP.2.2 _ hmem _ hb).mp
    (by rw [hspt, hGval α u hu', h2])
  have h4 : b = spt W (s α) (pos α) v := by
    rcases PRel.eq_or_stp hpair (hWs α) hvI h3 with h5 | h5
    · exact h5
    · obtain ⟨j, q, e', h6, h7, -⟩ := stp_of_side hpair (hWs α) hvI h5
      obtain ⟨rfl, rfl, -⟩ := hloc _ _ _ _ h6 α rfl
      exact absurd rfl h7
  refine ⟨s α, pos α, K α, σ α, v, hnet α, ⟨k, hi, by simp only [hK, h1]⟩, hvI, ?_⟩
  rw [h4]
  simp [spt, hW₁, netW_length]

private theorem occurring_label_determines_word
    (r : ℕ)
    (w : ℕ → List Letter)
    (W : ℕ → List Letter)
    (hWi : ∀ {i : ℕ}, i < r → W i = w i)
    (hWn : ∀ {i : ℕ}, W i ≠ [] → i < r)
    (hl : ∀ (i j : ℕ), i ≠ j → ∀ l ∈ w i, ∀ l' ∈ w j, l.1 ≠ l'.1) :
    ∀ (k i j : ℕ), cnt (W i) k ≠ 0 → cnt (W j) k ≠ 0 → i = j := by
  intro k i j h1 h2
  obtain ⟨l, h3, h4⟩ := List.countP_pos_iff.mp (Nat.pos_of_ne_zero h1)
  obtain ⟨l', h5, h6⟩ := List.countP_pos_iff.mp (Nat.pos_of_ne_zero h2)
  have hi : i < r := hWn fun he => by simp [he] at h3
  have hj : j < r := hWn fun he => by simp [he] at h5
  rw [hWi hi] at h3
  rw [hWi hj] at h5
  by_contra hne'
  exact hl i j hne' l h3 l' h5 (by simp only [beq_iff_eq] at h4 h6; rw [h4, h6])

/-- **The polygons of a cut.** Let `Y` be a surface that cuts the connected space `S` along finitely
many paths, and let each point of `B`
lie inside an inner path. Then `S` has one polygon with no point of `B` on its boundary. This is the
end of the three steps of the
sketch on page 216: each component of `Y` is a polygon, the polygons are cut into sectors and pasted
along the paths. -/
theorem exists_off_word_of_cut {S Y : Type u} {κ : Type*} [TopologicalSpace S] [T2Space S]
  [ConnectedSpace S] [TopologicalSpace Y] [T2Space Y] [Finite κ]
    {a : κ → ℝ → S} {inner : κ → Prop} {ψ : Y → S} {ξ η : κ → ℝ → Y} (h : IsNetCut a inner ψ ξ η)
      (hY : IsSurface Y) {B : Set S}
    (hB : ∀ x ∈ B, ∃ k, inner k ∧ ∃ u ∈ Ioo (0 : ℝ) 1, x = a k u) :
    ∃ (w : List Letter) (g : ℕ × ℂ → S), 2 ≤ w.length ∧ Good w ∧ Presents (sW w) g ∧ ∀ z ∈ sphere
      (0 : ℂ) 1, g (0, z) ∉ B := by
  classical
  have hfam := h.isArcFamily
  set ℓ := netL ξ η (inner := inner) with hℓ
  obtain ⟨y₀, -⟩ := h.surj (Classical.arbitrary S)
  have : LocallyConnectedSpace Y := hY.locallyConnected
  obtain ⟨r, rep, hr, hdisj, hcov⟩ := exists_comp_reps hY y₀
  have hcomp := fun j => exists_comp_word hY hfam (isClopen_connectedComponent (x
    := rep j)) isConnected_connectedComponent j
  choose w g c1 c2 c3 c4 c5 c6 c7 using hcomp
  set W : ℕ → List Letter := fun i => if i < r then w i else [] with hW
  set G : ℕ × ℂ → Y := fun a => g a.1 (0, a.2) with hG
  have hWi : ∀ {i}, i < r → W i = w i := fun h => ite_eq_left h
  have hWn : ∀ {i}, W i ≠ [] → i < r := fun {i} h => by
    by_contra hi
    exact h (ite_eq_right hi)
  have hne : ∀ j, w j ≠ [] := fun j he => by
    have := c1 j
    simp [he] at this
  have hl : ∀ i j, i ≠ j → ∀ l ∈ w i, ∀ l' ∈ w j, l.1 ≠ l'.1 := fun i j hij l hl' l' hl'' he =>
    hij (by rw [← c3 i l hl', ← c3 j l' hl'', he])
  have hP : Presents W G := presents_family (Z := fun j => connectedComponent (rep j)) hdisj hcov
    (fun j _ => hne j)
    (fun i j _ _ hij => hl i j hij) (fun j _ => c4 j) (fun j _ => c5 j) (fun j _ => c6 j)
  have hA : ∀ α : NetArc inner, ∃ j, j < r ∧ ∃ k σ, cnt (w j) k = 1 ∧ SideVal (sW (w j)) (g j) k
    (fun u => ℓ α (ofs σ u)) := fun α => by
    obtain ⟨j, hj, hy⟩ := hcov (ℓ α 0)
    exact ⟨j, hj, c7 j α hy⟩
  choose s hs lb σ hcnt hside using hA
  have hp : ∀ α, ∃ p, (w (s α))[p]? = some (lb α, true) ∧ ∀ u ∈ Icc (0 : ℝ) 1, g (s α) (0, sdPt (w
    (s α)).length p true u) = ℓ α (ofs (σ α) u) := fun α => by
    obtain ⟨i, p, h1, h2⟩ := hside α
    obtain ⟨rfl, h3⟩ := sW_get h1
    rw [sW_zero] at h2
    exact ⟨p, h3, h2⟩
  choose pos hpos hval using hp
  have hloc : ∀ i p k e, (W i)[p]? = some (k, e) → ∀ α, k = lb α → i = s α ∧ p = pos α ∧ e = true
    := by
    intro i p k e h1 α hk
    have hi : i < r := hWn fun he => by simp [he] at h1
    rw [hWi hi] at h1
    obtain rfl : i = s α := by
      by_contra hne'
      exact hl i _ hne' _ (List.mem_of_getElem? h1) _ (List.mem_of_getElem? (hpos α)) hk
    subst hk
    obtain rfl := unique_of_cnt (hcnt α) h1 (hpos α)
    have := h1.symm.trans (hpos α)
    simp only [Option.some.injEq, Prod.mk.injEq, true_and] at this
    exact ⟨rfl, rfl, this⟩
  have hhalf : (1 / 2 : ℝ) ∈ Ioo (0 : ℝ) 1 := by norm_num
  have hhalf' : (1 / 2 : ℝ) ∈ Icc (0 : ℝ) 1 := by norm_num
  have hWs : ∀ α, (W (s α))[pos α]? = some (lb α, true) := fun α => by
    rw [hWi (hs α)]
    exact hpos α
  have lbinj : ∀ α β, lb α = lb β → α = β := by
    intro α β he
    obtain ⟨h1, h2, -⟩ := hloc _ _ _ _ (hWs β) α he.symm
    by_contra hne'
    have h3 := hval α _ hhalf'
    have h4 := hval β _ hhalf'
    rw [h1, h2] at h4
    exact hfam.disj α β hne' _ (ofs_mem_Ioo _ hhalf) _ (ofs_mem_Ioo _ hhalf) (h3.symm.trans h4)
  obtain ⟨n, ⟨e⟩⟩ := Finite.exists_equiv_fin κ
  set idx : κ → ℕ := fun k => (e k).1 with hidx
  have idxinj : ∀ k k', idx k = idx k' → k = k' := fun k k' he => e.injective (Fin.ext he)
  set K : NetArc inner → ℕ := fun α => 2 * idx α.1.1 with hK
  set R : ℕ → ℕ × Bool := fun k => if h : ∃ α, lb α = k then (K h.choose, σ h.choose) else
    (2 * k + 1, true) with hR
  have hRlb : ∀ α, R (lb α) = (K α, σ α) := fun α => by
    have h1 : ∃ β, lb β = lb α := ⟨α, rfl⟩
    have h2 := lbinj _ _ h1.choose_spec
    simp only [hR, dite_eq_left h1, h2]
  have hRo : ∀ k, (∀ α, lb α ≠ k) → R k = (2 * k + 1, true) := fun k hk => by
    simp only [hR]
    rw [dite_eq_right (by push Not; exact hk)]
  set W₁ := netW R W with hW₁
  have hnet : ∀ α, (W₁ (s α))[pos α]? = some (K α, σ α) := fun α => by
    rw [hW₁, netW_get (hWs α), hRlb, netFl_true]
  have hGval : ∀ α, ∀ u ∈ Icc (0 : ℝ) 1, G (s α, sdPt (W (s α)).length (pos α) (σ α) u) = ℓ α u
    := fun α u hu => by
    have h1 := hval α _ (ofs_mem (e := σ α) hu)
    rw [ofs_ofs, ← sdPt_netFl, netFl_true] at h1
    simp only [hG, hWi (hs α)]
    exact h1
  have hcase : ∀ k, (∃ α, lb α = k) ∨ ∀ α, lb α ≠ k := fun k => by
    by_cases h1 : ∃ α, lb α = k
    · exact .inl h1
    · exact .inr (by push Not at h1; exact h1)
  have hmatch : ∀ i j p q k k' e e' (t : ℝ), (W i)[p]? = some (k, e) → (W j)[q]? = some (k', e')
    → k ≠ k' → (R k).1 = (R k').1 → t ∈ Icc (0 : ℝ) 1 →
      ψ (G (i, sdPt (W i).length p (netFl (R k).2 e) t)) = ψ (G (j, sdPt (W j).length q (netFl
        (R k').2 e') t)) := by
    exact matching_word_side_labels (S := S) (Y := Y) (κ := κ) (a := a) (inner := inner) (ψ := ψ)
      (ξ := ξ) (η := η) h W G s lb σ pos hloc idx idxinj K hK R hRlb hRo hGval hcase
  have hfib : ∀ y y', ψ y = ψ y' → Relation.EqvGen (fun u v => u = v ∨ ∃ a b, G a = u ∧ G b = v
    ∧ Stp (netW R W) a b) y y' := by
    exact cut_lift_fiber_equivalence (S := S) (Y := Y) (κ := κ) (a := a) (inner := inner) (ψ := ψ)
      (ξ := ξ) (η := η) h W G s lb σ pos hWs lbinj idx R (by simpa only [hW₁, hK] using hnet) hGval
  have hP₁ : Presents W₁ (ψ ∘ G) := presents_paste hP h.cont h.surj hmatch hfib
  have hS₀ : ∀ i, i ∉ Finset.range r → W i = [] := fun i hi => by
    simp only [hW, ite_eq_right_iff]
    exact fun h1 => absurd (Finset.mem_range.mpr h1) hi
  have hS₁ : ∀ i, i ∉ Finset.range r → W₁ i = [] := fun i hi => by
    simp [hW₁, netW, hS₀ i hi]
  have hslot : ∀ k i j, cnt (W i) k ≠ 0 → cnt (W j) k ≠ 0 → i = j := by
    exact occurring_label_determines_word r w W hWi hWn hl
  set L : ℕ → ℕ := fun k => ∑ i ∈ Finset.range r, cnt (W i) k with hL
  have hL2 : ∀ k, L k ≤ 2 := fun k => by
    by_cases h1 : ∃ i ∈ Finset.range r, cnt (W i) k ≠ 0
    · obtain ⟨i, hi, h2⟩ := h1
      have h3 : L k = cnt (W i) k := Finset.sum_eq_single_of_mem i hi fun j _ hj => by
        by_contra h4
        exact hj (hslot k j i h4 h2)
      rw [h3, hWi (Finset.mem_range.mp hi)]
      exact c2 i k
    · push Not at h1
      simp only [hL]
      rw [Finset.sum_eq_zero h1]
      omega
  have hL1 : ∀ α, L (lb α) = 1 := fun α => by
    have h1 : cnt (W (s α)) (lb α) = 1 := by rw [hWi (hs α)]; exact hcnt α
    have h3 : L (lb α) = cnt (W (s α)) (lb α) := Finset.sum_eq_single_of_mem _
      (Finset.mem_range.mpr (hs α)) fun j _ hj => by
      by_contra h4
      exact hj (hslot _ j _ h4 (by omega))
    rw [h3, h1]
  have hT : ∀ (P : Finset ℕ) (c : ℕ), (∀ k, (R k).1 = c ↔ k ∈ P) → ∑ i ∈ Finset.range r, cnt
    (W₁ i) c = ∑ k ∈ P, L k := fun P c h1 => by
    simp only [hW₁, cnt_netW h1, hL]
    exact Finset.sum_comm
  have hRiff : ∀ k c, (R k).1 = c ↔ (∃ α, lb α = k ∧ K α = c) ∨ ((∀ α, lb α ≠ k) ∧ 2 * k + 1 = c)
    := fun k c => by
    rcases hcase k with ⟨α, rfl⟩ | h1
    · rw [hRlb]
      constructor
      · rintro rfl
        exact .inl ⟨α, rfl, rfl⟩
      · rintro (⟨β, h2, rfl⟩ | ⟨h2, -⟩)
        · rw [lbinj _ _ h2]
        · exact absurd rfl (h2 α)
    · rw [hRo k h1]
      constructor
      · rintro rfl
        exact .inr ⟨h1, rfl⟩
      · rintro (⟨β, h2, -⟩ | ⟨-, rfl⟩)
        · exact absurd h2 (h1 β)
        · rfl
  have hinnerP : ∀ k (hi : inner k), ∀ x, (R x).1 = 2 * idx k ↔ x ∈
      ({lb ⟨(k, true), .inl rfl⟩, lb ⟨(k, false), .inr hi⟩} : Finset ℕ) := by
    intro k hi x
    rw [hRiff]
    simp only [Finset.mem_insert, Finset.mem_singleton]
    constructor
    · rintro (⟨⟨⟨k', b⟩, h1⟩, rfl, h2⟩ | ⟨-, h2⟩)
      · obtain rfl : k' = k := idxinj _ _ (by simpa [hK] using h2)
        cases b
        · exact .inr rfl
        · exact .inl rfl
      · omega
    · rintro (rfl | rfl)
      · exact .inl ⟨_, rfl, rfl⟩
      · exact .inl ⟨_, rfl, rfl⟩
  have hTi : ∀ k, inner k → ∑ i ∈ Finset.range r, cnt (W₁ i) (2 * idx k) = 2 := fun k hi => by
    have hne' : lb ⟨(k, true), .inl rfl⟩ ≠ lb ⟨(k, false), .inr hi⟩ := fun he => by
      have := lbinj _ _ he
      simp at this
    rw [hT _ _ (hinnerP k hi), Finset.sum_pair hne', hL1, hL1]
  have hsum : ∀ c, ∑ i ∈ Finset.range r, cnt (W₁ i) c ≤ 2 := by
    exact relabeled_word_count_bound (κ := κ) (inner := inner) r lb idx idxinj K hK R W₁ L hL2
      hL1 hT hRiff hTi
  have hsumW : ∀ c, ∑ i ∈ Finset.range r, cnt (W i) c ≤ 2 := hL2
  have hpair : IsPaired W := isPaired_of_sum hS₀ hsumW
  set Bad : Set ℕ := (fun k => 2 * idx k) '' {k | inner k} with hBad
  have hBadfin : Bad.Finite := (Set.toFinite _).image _
  have hon : OnBad Bad B W₁ (ψ ∘ G) := by
    exact relabeled_word_boundary_arcs (S := S) (Y := Y) (κ := κ) (a := a) (inner := inner) (ψ :=
      ψ) (ξ := ξ) (η := η) h (B := B) hB W G hP s lb σ pos hloc hWs idx K hK R W₁ hW₁ hnet hGval
      hpair
  refine exists_off_word hBadfin (Finset.range r) ?_ ?_ hP₁ hon ?_ hS₁ hsum ?_
  · refine (Finset.finite_toSet (Finset.range r)).subset fun i hi => ?_
    by_contra h1
    exact hi (hS₁ i h1)
  · intro he
    have h1 := netW_length R W 0
    rw [← hW₁, he, hWi hr] at h1
    have := c1 0
    simp only [List.length_nil] at h1
    omega
  · intro i hi
    have h1 : i < r := by
      by_contra h2
      exact hi (hS₁ i (by simpa using h2))
    rw [hW₁, netW_length, hWi h1]
    exact c1 i
  · rintro _ ⟨k, hi, rfl⟩
    simp only
    rw [hTi k hi]
    omega

end GraphMinor.GM07
