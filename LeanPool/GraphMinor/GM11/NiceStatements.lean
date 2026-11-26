/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM11.Restraints
public import LeanPool.GraphMinor.GM11.Section7b
public import LeanPool.GraphMinor.GM11.OArcCircuit

/-!
# Nice sets

`Nice31Statement` and `Nice73Statement` are (3.1) and (7.3) of Graph Minors XI for closed `Γ`-nice
sets. The
paper's (3.1) needs a tameness condition (see the correction to (3.1) in `corrections/GM11.md`), and
closed nice sets satisfy it. Section 8 uses them through these statements.

The lemmas here show that sets are nice. `isGammaNice_of_frontier` is the main one: a set whose
frontier
lies in a subdrawing, which it contains, is nice.
-/

@[expose] public section

namespace GraphMinor.GM11

open Set Topology GraphMinor.Surface unitInterval

universe u

/-- (3.1) of Graph Minors XI (page 76), for closed nice sets. -/
def Nice31Statement : Prop :=
  ∀ (S : Type u) [TopologicalSpace S] [T2Space S] [ConnectedSpace S], IsClosedSurface S →
    ∀ (Γ : Drawing S) (X Y : Set S), IsClosed X → IsClosed Y → IsGammaNice Γ X → IsGammaNice Γ Y →
      IsSimplyConnectedSet X → IsPathConnected (X ∩ Y) → CanPush X Y

/-- (7.3) of Graph Minors XI (page 93), for closed nice sets: "If $Z \subseteq \Sigma$ is nice and
$\phi \colon S^1 \to Z$ is continuous and not
null-homotopic in $Z$, then there is an $O$-arc $F \subseteq |\phi|$ which is not
null-homotopic in $Z$." -/
def Nice73Statement : Prop :=
  ∀ (S : Type u) [TopologicalSpace S] [T2Space S] [ConnectedSpace S], IsClosedSurface S →
    ∀ (Γ : Drawing S) (Z : Set S), IsClosed Z → IsGammaNice Γ Z →
      ∀ φ : C(Circle, S), range φ ⊆ Z → ¬ ClosedCurveIsNullHomotopicIn Z φ →
        ∃ F : Set S, IsOArc F ∧ F ⊆ range φ ∧ ¬ IsNullHomotopicOArcIn Z F

variable {S : Type u} [TopologicalSpace S] [T2Space S] {Γ : Drawing S}

omit [T2Space S] in
/-- A closed disc is the closure of its interior: each boundary point is a limit of inner points. -/
theorem discBd_subset_closure {Δ : Set S} (hΔ : IsClosedDisc Δ) {y : S} (hy : y ∈ discBd Δ) :
    y ∈ closure (Δ \ discBd Δ) := by
  obtain ⟨φ⟩ := hΔ
  have hbd := disc_boundary Δ φ
  rw [hbd] at hy
  obtain ⟨z, hz, rfl⟩ := hy
  have hz1 : ‖z.1‖ = 1 := by simpa [UnitCircle] using hz
  let c : ℕ → ClosedUnitDisc := fun n => ⟨(1 - 1 / ((n : ℝ) + 2)) • z.1, by
    have h₁ : (0 : ℝ) < 1 / ((n : ℝ) + 2) := by positivity
    have h₂ : 1 / ((n : ℝ) + 2) ≤ 1 / 2 := by
      apply one_div_le_one_div_of_le (by norm_num)
      linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
    simp only [ClosedUnitDisc, Metric.mem_closedBall, dist_zero_right, norm_smul, hz1,
      mul_one, Real.norm_eq_abs]
    rw [abs_of_nonneg (by linarith)]
    linarith⟩
  have hlim : Filter.Tendsto c Filter.atTop (𝓝 z) := by
    rw [tendsto_subtype_rng]
    have h₁ : Filter.Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 2)) Filter.atTop (𝓝 0) := by
      have := tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)
      have h₂ := (Filter.tendsto_add_atTop_iff_nat 1).mpr this
      refine h₂.congr fun n => ?_
      push_cast
      ring_nf
    have h₂ : Filter.Tendsto (fun n : ℕ => (1 - 1 / ((n : ℝ) + 2)) • z.1) Filter.atTop
        (𝓝 ((1 - 0 : ℝ) • z.1)) := (tendsto_const_nhds.sub h₁).smul_const z.1
    rw [sub_zero, one_smul] at h₂
    exact h₂
  have hlim' := (continuous_subtype_val.comp φ.continuous).tendsto z |>.comp hlim
  refine mem_closure_of_tendsto hlim' (Filter.Eventually.of_forall fun n => ?_)
  refine ⟨(φ (c n)).2, ?_⟩
  rw [hbd]
  rintro ⟨w, hw, hwc⟩
  have hw' := φ.injective (Subtype.ext hwc)
  have hn : ‖(c n).1‖ = 1 := by
    rw [← hw']
    simpa [UnitCircle] using hw
  have h₁ : (0 : ℝ) < 1 / ((n : ℝ) + 2) := by positivity
  have h₂ : 1 / ((n : ℝ) + 2) ≤ 1 / 2 := by
    apply one_div_le_one_div_of_le (by norm_num)
    linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
  have h₃ : ‖(c n).1‖ = 1 - 1 / ((n : ℝ) + 2) := by
    change ‖(1 - 1 / ((n : ℝ) + 2)) • z.1‖ = _
    rw [norm_smul, hz1, mul_one, Real.norm_eq_abs, abs_of_nonneg (by linarith)]
  linarith

omit [T2Space S] in
/-- Each point of the surface lies in a vertex, an edge or a region. -/
theorem exists_atom (Γ : Drawing S) (x : S) : ∃ a ∈ Γ.A, x ∈ a := by
  by_cases hV : x ∈ Γ.V
  · exact ⟨{x}, Or.inl (Or.inl ⟨x, hV, rfl⟩), rfl⟩
  by_cases hU : x ∈ Γ.U
  · obtain ⟨e, he, hx⟩ := Γ.exists_edge_of_mem hU hV
    exact ⟨e, Or.inl (Or.inr he), hx⟩
  · obtain ⟨r, hr, hx⟩ := exists_region_of_notMem hU
    exact ⟨r, Or.inr hr, hx⟩

omit [T2Space S] in
/-- A set that contains each atom it meets is nice. -/
theorem isGammaNice_of_sat {X : Set S} (h : ∀ a ∈ Γ.A, (a ∩ X).Nonempty → a ⊆ X) : IsGammaNice Γ X
  := by
  refine ⟨{a | a ∈ Γ.A ∧ (a ∩ X).Nonempty}, fun a ha => ha.1, subset_antisymm (fun x hx => ?_) ?_⟩
  · obtain ⟨a, ha, hxa⟩ := exists_atom Γ x
    exact mem_sUnion.mpr ⟨a, ⟨ha, x, hxa, hx⟩, hxa⟩
  · refine sUnion_subset fun a ha => h a ha.1 ha.2

omit [T2Space S] in
theorem IsGammaNice.union {X Y : Set S} (hX : IsGammaNice Γ X) (hY : IsGammaNice Γ Y) :
    IsGammaNice Γ (X ∪ Y) := by
  refine isGammaNice_of_sat fun a ha hne => ?_
  obtain ⟨x, hxa, hx | hx⟩ := hne
  · exact (nice_atom hX ha ⟨x, hxa, hx⟩).trans subset_union_left
  · exact (nice_atom hY ha ⟨x, hxa, hx⟩).trans subset_union_right

omit [T2Space S] in
theorem IsGammaNice.inter {X Y : Set S} (hX : IsGammaNice Γ X) (hY : IsGammaNice Γ Y) :
    IsGammaNice Γ (X ∩ Y) := by
  refine isGammaNice_of_sat fun a ha hne => ?_
  obtain ⟨x, hxa, hx, hy⟩ := hne
  exact subset_inter (nice_atom hX ha ⟨x, hxa, hx⟩) (nice_atom hY ha ⟨x, hxa, hy⟩)

omit [T2Space S] in
/-- An atom is preconnected. -/
theorem isPreconnected_atom {a : Set S} (ha : a ∈ Γ.A) : IsPreconnected a
  := by
  rcases ha with (⟨v, -, rfl⟩ | he) | hr
  · exact isPreconnected_singleton
  · exact he.2.2.1.isConnected.isPreconnected
  · exact region_isPreconnected hr

omit [T2Space S] in
/-- A preconnected set that meets a set and its complement meets the frontier of the set. -/
theorem meets_frontier {a T : Set S} (ha : IsPreconnected a) (h₁ : (a ∩ T).Nonempty)
    {z : S} (hza : z ∈ a) (hzT : z ∉ T) : ∃ y ∈ a, y ∈ frontier T := by
  by_contra hno
  push Not at hno
  have hin : ∀ y ∈ a, y ∈ T → y ∈ interior T := fun y hy hyT => by
    by_contra hni
    exact hno y hy ⟨subset_closure hyT, hni⟩
  have hout : ∀ y ∈ a, y ∉ T → y ∈ (closure T)ᶜ := fun y hy hyT hcl =>
    hno y hy ⟨hcl, fun hi => hyT (interior_subset hi)⟩
  obtain ⟨x, hxa, hxT⟩ := h₁
  obtain ⟨y, -, hy₁, hy₂⟩ := ha (interior T) (closure T)ᶜ isOpen_interior
    isClosed_closure.isOpen_compl
    (fun y hy => by
      by_cases hyT : y ∈ T
      · exact Or.inl (hin y hy hyT)
      · exact Or.inr (hout y hy hyT))
    ⟨x, hxa, hin x hxa hxT⟩ ⟨z, hza, hout z hza hzT⟩
  exact hy₂ (subset_closure (interior_subset hy₁))

omit [T2Space S] in
/-- **A set with its frontier in a subdrawing that it contains is nice.** -/
theorem isGammaNice_of_frontier {N : Drawing S} {T : Set S}
    (hN : N.IsSubdrawing Γ) (hNT : N.U ⊆ T) (hf : frontier T ⊆ N.U) : IsGammaNice Γ T := by
  refine isGammaNice_of_sat fun a ha hne => ?_
  by_contra hnot
  obtain ⟨z, hza, hzT⟩ := not_subset.mp hnot
  obtain ⟨y, hya, hyf⟩ := meets_frontier (isPreconnected_atom ha) hne hza hzT
  have hyU : y ∈ N.U := hf hyf
  rcases ha with (⟨v, -, rfl⟩ | he) | hr
  · have h₁ : y = v := hya
    have h₂ : z = v := hza
    exact hzT (h₂.trans h₁.symm ▸ hNT hyU)
  · have hyV : y ∉ N.V := fun h => (he.2.1 hya).2 (hN.1 h)
    obtain ⟨e', he', hye'⟩ := N.exists_edge_of_mem hyU hyV
    obtain rfl := Γ.edge_eq_of_mem he (hN.2 he') hya hye'
    exact hzT (hNT (N.closure_subset_U he' (subset_closure hza)))
  · exact region_subset hr hya (hN.U_subset hyU)

/-- The closure of an edge is path-connected. -/
theorem isPathConnected_closure_edge [ConnectedSpace S] {e : Set S} (he : e ∈ Γ.E) :
    IsPathConnected (closure e) := by
  obtain ⟨γ, hγ⟩ := exists_edgePar Γ
  have hcl : closure e = range (γ e) := by
    apply subset_antisymm
    · refine closure_minimal ?_ (isCompact_range (hγ.cont e he)).isClosed
      intro y hy
      obtain ⟨t, -, rfl⟩ := (hγ.image e he).superset hy
      exact mem_range_self t
    · rintro _ ⟨t, rfl⟩
      have ht : t ∈ closure (Ioo (0 : I) 1) := by
        rw [closure_Ioo (zero_ne_one' I)]
        exact ⟨t.2.1, t.2.2⟩
      have := image_closure_subset_closure_image (hγ.cont e he) (mem_image_of_mem _ ht)
      rwa [hγ.image e he] at this
  rw [hcl]
  have hI : PathConnectedSpace I := isPathConnected_iff_pathConnectedSpace.mp
    ((convex_Icc (0 : ℝ) 1).isPathConnected ⟨0, by simp⟩)
  rw [← image_univ]
  exact isPathConnected_univ.image (hγ.cont e he)

/-- The point set of a walk is path-connected. -/
theorem isPathConnected_walk_U [ConnectedSpace S] {u v : S} (W : GraphWalk Γ.toGraph u v) :
    IsPathConnected {x | x ∈ W.support ∨ ∃ e ∈ W.edges, x ∈ closure e} := by
  induction W with
  | @nil a ha =>
    have heq : {x | x ∈ (GraphWalk.nil ha : GraphWalk Γ.toGraph a a).support ∨
        ∃ e ∈ (GraphWalk.nil ha : GraphWalk Γ.toGraph a a).edges, x ∈ closure e} = {a} := by
      ext x
      simp [GraphWalk.support, GraphWalk.edges]
    rw [heq]
    exact isPathConnected_singleton a
  | @cons a b c e hlink rest ih =>
    have hab : a ∈ closure e ∧ b ∈ closure e := by
      have h : a ∈ closure e ∩ Γ.V ∧ b ∈ closure e ∩ Γ.V := by
        rw [hlink.2.2.2]
        exact ⟨Or.inl rfl, Or.inr rfl⟩
      exact ⟨h.1.1, h.2.1⟩
    have heq : {z | z ∈ (GraphWalk.cons hlink rest).support ∨
        ∃ f ∈ (GraphWalk.cons hlink rest).edges, z ∈ closure f} =
        closure e ∪ {z | z ∈ rest.support ∨ ∃ f ∈ rest.edges, z ∈ closure f} := by
      ext z
      simp only [GraphWalk.support, GraphWalk.edges, List.mem_cons, mem_ofPred_eq, mem_union]
      constructor
      · rintro ((rfl | h) | ⟨f, (rfl | hf), hz⟩)
        · exact Or.inl hab.1
        · exact Or.inr (Or.inl h)
        · exact Or.inl hz
        · exact Or.inr (Or.inr ⟨f, hf, hz⟩)
      · rintro (h | h | ⟨f, hf, hz⟩)
        · exact Or.inr ⟨e, Or.inl rfl, h⟩
        · exact Or.inl (Or.inr h)
        · exact Or.inr ⟨f, Or.inr hf, hz⟩
    rw [heq]
    refine (isPathConnected_closure_edge hlink.1).union ih ⟨b, hab.2, Or.inl rest.start_mem_support⟩

end GraphMinor.GM11
