/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM11.Section810
public import LeanPool.GraphMinor.GM14.Defs

/-!
# Graph Minors XI, (9.1)

The paper defines `d` on the atoms of a drawing `Γ` with a slope. `theorem_9_1` is its inequality
(9.1), for
`twiceDistance`. `tangleMetric_triangle` is the same inequality for the metric of a respectful
tangle, which later
papers use: there the slope lives in the radial drawing `K` of `H`, and each atom of `H` has a
corresponding atom
of `K`. `tangleMetric_le_one` is the fact that a vertex and a region at it have distance at most
one.
-/

@[expose] public section

namespace GraphMinor.GM11

open Set Topology GraphMinor.Surface unitInterval
open GraphMinor.GM14 (IsCorrespondingAtom tangleMetric HasTangleMetric)

universe u

variable {S : Type u} [TopologicalSpace S] [T2Space S] [ConnectedSpace S] {Γ : Drawing S}
  {K : ℕ} {ins : Drawing S → Set S}

/-- Two restraints that meet lie in a restraint with length at most the sum of their lengths. This
is the
step of (9.1), after the two restraints are replaced by extreme ones. -/
theorem exists_restraint_union (hS : IsClosedSurface S)
    (hs : IsSlope Γ K ins) {X Y : Set S} (hX : IsRestraint Γ ins K X) (hY : IsRestraint Γ ins K Y)
    (hne : (X ∩ Y).Nonempty) (hl : perimeterWalkLength Γ X + perimeterWalkLength Γ Y < K) :
    ∃ T, IsRestraint Γ ins K T ∧ X ⊆ T ∧ Y ⊆ T ∧
      perimeterWalkLength Γ T ≤ perimeterWalkLength Γ X + perimeterWalkLength Γ Y := by
  obtain ⟨X', eX, sX, lX⟩ := exists_extreme hS hX
  obtain ⟨Y', eY, sY, lY⟩ := exists_extreme hS hY
  have hne' : (X' ∩ Y').Nonempty := hne.mono (inter_subset_inter sX sY)
  obtain ⟨hinter, hunion⟩ := theorem_8_8_proof hS hs eX eY hne'
  have hu : X' ∪ Y' ≠ univ := by
    have := theorem_8_4_proof hS hs eX.1 eY.1 eY.1
    rwa [union_assoc, union_self] at this
  have h2 := perimeterWalkLength_union_inter hS eX.1 eY.1 hinter hunion hne' hu
  have hle : perimeterWalkLength Γ (X' ∪ Y') ≤ perimeterWalkLength Γ X + perimeterWalkLength Γ Y
    := by omega
  exact ⟨X' ∪ Y', theorem_8_6_proof hS hs eX.1 eY.1 hunion (lt_of_le_of_lt hle hl),
    sX.trans subset_union_left, sY.trans subset_union_right, hle⟩

/-- **(9.1)** of Graph Minors XI (page 104): "If $a, b, c \in A(\Gamma)$ then $d(a, b) + d(b, c) \ge
d(a, c)$." Here
`twiceDistance` is `2d`. -/
theorem theorem_9_1_proof (hS : IsClosedSurface S)
    (hs : IsSlope Γ K ins) {a b c : Set S} (hb : b.Nonempty) :
    twiceDistance Γ ins K a c ≤ twiceDistance Γ ins K a b + twiceDistance Γ ins K b c := by
  classical
  have hle : ∀ x y, twiceDistance Γ ins K x y ≤ K := by
    intro x y
    unfold twiceDistance
    split_ifs with h₁ h₂
    · exact Nat.zero_le _
    · obtain ⟨X, hX, hx, hy⟩ := h₂
      have : sInf {t | ∃ X, IsRestraint Γ ins K X ∧ x ⊆ X ∧ y ⊆ X ∧ perimeterWalkLength Γ X = t} ≤
          perimeterWalkLength Γ X := Nat.sInf_le ⟨X, hX, hx, hy, rfl⟩
      exact this.trans hX.length_lt.le
    · exact le_rfl
  by_cases hac : a = c
  · subst hac
    simp [twiceDistance]
  by_cases hab : a = b
  · subst hab
    simp [twiceDistance]
  by_cases hbc : b = c
  · subst hbc
    simp [twiceDistance]
  by_cases h₁ : ∃ X, IsRestraint Γ ins K X ∧ a ⊆ X ∧ b ⊆ X
  swap
  · have : twiceDistance Γ ins K a b = K := by
      simp [twiceDistance, hab, h₁]
    rw [this]
    exact (hle a c).trans (Nat.le_add_right _ _)
  by_cases h₂ : ∃ X, IsRestraint Γ ins K X ∧ b ⊆ X ∧ c ⊆ X
  swap
  · have : twiceDistance Γ ins K b c = K := by
      simp [twiceDistance, hbc, h₂]
    rw [this]
    exact (hle a c).trans (Nat.le_add_left _ _)
  have hmem₁ := Nat.sInf_mem (s := {t | ∃ X, IsRestraint Γ ins K X ∧ a ⊆ X ∧ b ⊆ X
    ∧ perimeterWalkLength Γ X = t})
    (by obtain ⟨X, h, h', h''⟩ := h₁; exact ⟨_, X, h, h', h'', rfl⟩)
  have hmem₂ := Nat.sInf_mem (s := {t | ∃ X, IsRestraint Γ ins K X ∧ b ⊆ X ∧ c ⊆ X
    ∧ perimeterWalkLength Γ X = t})
    (by obtain ⟨X, h, h', h''⟩ := h₂; exact ⟨_, X, h, h', h'', rfl⟩)
  have e₁ : twiceDistance Γ ins K a b =
      sInf {t | ∃ X, IsRestraint Γ ins K X ∧ a ⊆ X ∧ b ⊆ X ∧ perimeterWalkLength Γ X = t} := by
    simp [twiceDistance, hab, h₁]
  have e₂ : twiceDistance Γ ins K b c =
      sInf {t | ∃ X, IsRestraint Γ ins K X ∧ b ⊆ X ∧ c ⊆ X ∧ perimeterWalkLength Γ X = t} := by
    simp [twiceDistance, hbc, h₂]
  rw [e₁, e₂]
  obtain ⟨X, hX, hxa, hxb, hlX⟩ := hmem₁
  obtain ⟨Y, hY, hyb, hyc, hlY⟩ := hmem₂
  rw [← hlX, ← hlY]
  by_cases hlt : perimeterWalkLength Γ X + perimeterWalkLength Γ Y < K
  swap
  · exact (hle a c).trans (by omega)
  obtain ⟨z, hz⟩ := hb
  obtain ⟨T, hT, hXT, hYT, hl⟩ := exists_restraint_union hS hs hX hY ⟨z, hxb hz, hyb hz⟩ hlt
  refine le_trans ?_ hl
  have hex : ∃ T', IsRestraint Γ ins K T' ∧ a ⊆ T' ∧ c ⊆ T' :=
    ⟨T, hT, hxa.trans hXT, hyc.trans hYT⟩
  have e₃ : twiceDistance Γ ins K a c =
      sInf {t | ∃ X, IsRestraint Γ ins K X ∧ a ⊆ X ∧ c ⊆ X ∧ perimeterWalkLength Γ X = t} := by
    simp [twiceDistance, hac, hex]
  rw [e₃]
  exact Nat.sInf_le ⟨T, hT, hxa.trans hXT, hyc.trans hYT, rfl⟩

/-! ## The metric of a respectful tangle -/

section Tangle

variable {H D : Drawing S} {θ k : ℕ} {x y : Set S}

omit [T2Space S] [ConnectedSpace S] in
/-- A walk in a radial drawing has even length if its ends are on the same side of the bipartition.
-/
theorem even_length_of_preRadial (hrad : (PaintingOrDrawing.drawing H).IsPreRadialDrawing D) {u v :
  S}
    (W : GraphWalk D.toGraph u v) : (u ∈ H.V ↔ v ∈ H.V) ↔ Even W.length := by
  have hb := bipartite_of_preRadial hrad
  induction W with
  | nil _ => simp [GraphWalk.length, GraphWalk.edges]
  | @cons x y z e hl r ih =>
    have hlen : (GraphWalk.cons hl r).length = r.length + 1 := rfl
    have hx : x ∈ H.V ↔ y ∉ H.V := hb _ _ _ hl
    have key : (x ∈ H.V ↔ z ∈ H.V) ↔ ¬ (y ∈ H.V ↔ z ∈ H.V) := by tauto
    rw [hlen, Nat.even_add_one]
    exact key.trans (not_congr ih)

omit [T2Space S] [ConnectedSpace S] in
theorem even_length_of_closed (hrad : (PaintingOrDrawing.drawing H).IsPreRadialDrawing D) {u : S}
    (W : GraphWalk D.toGraph u u) : Even W.length := (even_length_of_preRadial hrad W).mp Iff.rfl

/-- The pairs of the definition of `tangleMetric`. -/
def MetricWitness (H D : Drawing S) (ins : Drawing S → Set S) (θ : ℕ) (x y : Set S) (k : ℕ) : Prop
  :=
  ∃ (u : S) (W : GraphWalk D.toGraph u u) (x' y' : Set S),
    IsCorrespondingAtom H D x x' ∧ IsCorrespondingAtom H D y y' ∧
      W.length < 2 * θ ∧ W.length = 2 * k ∧ x' ⊆ insWalk ins D W ∧ y' ⊆ insWalk ins D W

omit [T2Space S] [ConnectedSpace S] in
/-- A short closed walk whose interior contains both radial atoms bounds their distance. -/
theorem tangleMetric_le_of_walk [T1Space S] {u : S} (W : GraphWalk D.toGraph u u)
    {x' y' : Set S} (hx : IsCorrespondingAtom H D x x') (hy : IsCorrespondingAtom H D y y')
    (hl : W.length < 2 * θ) (hk : W.length = 2 * k)
    (hxW : x' ⊆ insWalk ins D W) (hyW : y' ⊆ insWalk ins D W) :
    tangleMetric H D ins θ x y ≤ k := by
  classical
  unfold tangleMetric
  split_ifs with hxy hw
  · exact Nat.zero_le _
  · exact Nat.sInf_le ⟨u, W, x', y', hx, hy, hl, hk, hxW, hyW⟩
  · exact (hw ⟨u, W, x', y', hx, hy, hl, hxW, hyW⟩).elim

omit [ConnectedSpace S] in
theorem tangleMetric_le (hk : MetricWitness H D ins θ x y k) : tangleMetric H D ins θ x y ≤ k := by
  obtain ⟨u, W, x', y', hx, hy, hl, heven, hxW, hyW⟩ := hk
  exact tangleMetric_le_of_walk W hx hy hl heven hxW hyW

omit [ConnectedSpace S] in
/-- The metric is `θ`, or it comes from a closed walk. -/
theorem tangleMetric_cases (hrad : (PaintingOrDrawing.drawing H).IsPreRadialDrawing D) {x y : Set S}
    (hne : x ≠ y) : tangleMetric H D ins θ x y = θ ∨
      (tangleMetric H D ins θ x y < θ ∧
        MetricWitness H D ins θ x y (tangleMetric H D ins θ x y)) := by
  classical
  unfold tangleMetric
  simp only [hne, ite_false]
  split_ifs with h₁
  · right
    have hset : {k : ℕ | MetricWitness H D ins θ x y k}.Nonempty := by
      obtain ⟨u, W, x', y', hx, hy, hl, h₃, h₄⟩ := h₁
      obtain ⟨k, hk⟩ := even_length_of_closed hrad W
      exact ⟨k, u, W, x', y', hx, hy, hl, by omega, h₃, h₄⟩
    have hm := Nat.sInf_mem hset
    refine ⟨?_, hm⟩
    obtain ⟨u, W, x', y', hx, hy, hl, hk, -, -⟩ := hm
    have heq : sInf {k : ℕ | MetricWitness H D ins θ x y k} = _ := rfl
    change sInf {k : ℕ | MetricWitness H D ins θ x y k} < θ
    omega
  · exact Or.inl rfl

omit [ConnectedSpace S] in
theorem tangleMetric_le_order (hrad : (PaintingOrDrawing.drawing H).IsPreRadialDrawing D)
  (x y : Set S) :
    tangleMetric H D ins θ x y ≤ θ := by
  by_cases hne : x = y
  · simp [tangleMetric, hne]
  · rcases tangleMetric_cases (ins := ins) (θ := θ) hrad hne with h | h
    · exact h.le
    · exact h.1.le

omit [T2Space S] [ConnectedSpace S] in
/-- Two atoms that correspond to one atom meet. -/
theorem corresponding_meet (hrad : (PaintingOrDrawing.drawing H).IsPreRadialDrawing D) {x x₁ x₂ :
  Set S}
    (h₁ : IsCorrespondingAtom H D x x₁) (h₂ : IsCorrespondingAtom H D x x₂) : (x₁ ∩ x₂).Nonempty
      := by
  have hne : ∀ r ∈ H.R, ∀ w ∈ r, w ∉ H.U := fun r hr w hw => region_subset hr hw
  obtain ⟨-, -, h₁⟩ := h₁
  obtain ⟨-, -, h₂⟩ := h₂
  rcases h₁ with ⟨v, hv, rfl, rfl⟩ | ⟨he, -, hsub⟩ | ⟨hr, w, hw, rfl⟩ <;>
    rcases h₂ with ⟨v', hv', h₃, rfl⟩ | ⟨he', -, hsub'⟩ | ⟨hr', w', hw', rfl⟩
  · exact ⟨v, rfl, by simpa using singleton_eq_singleton_iff.mp h₃⟩
  · exact ((he'.2.1 (rfl : v ∈ ({v} : Set S))).2 hv).elim
  · exact (hne _ hr' v rfl (H.V_subset_U hv)).elim
  · exact ((he.2.1 (h₃ ▸ rfl : v' ∈ x)).2 hv').elim
  · obtain ⟨z, hz⟩ := he.1
    exact ⟨z, hsub hz, hsub' hz⟩
  · obtain ⟨z, hz⟩ := he.1
    exact (hne _ hr' z hz (he.2.1 hz).1).elim
  · exact (hne _ hr v' (h₃ ▸ rfl) (H.V_subset_U hv')).elim
  · obtain ⟨z, hz⟩ := he'.1
    exact (hne _ hr z hz (he'.2.1 hz).1).elim
  · obtain ⟨c, -, hu⟩ := hrad.2.2.1 x hr
    have h₃ : w = c := hu w ⟨hw.2, hw.1⟩
    have h₄ : w' = c := hu w' ⟨hw'.2, hw'.1⟩
    exact ⟨w, rfl, by rw [h₃, ← h₄]; rfl⟩

/-- **(9.1)** of Graph Minors XI (page 104), for the metric of a respectful tangle. -/
theorem tangleMetric_triangle (hS : IsClosedSurface S)
    (hrad : (PaintingOrDrawing.drawing H).IsPreRadialDrawing D) (hs : IsSlope D (2 * θ) ins)
      (a b c : Set S) :
    tangleMetric H D ins θ a c ≤ tangleMetric H D ins θ a b + tangleMetric H D ins θ b c := by
  by_cases hac : a = c
  · simp [tangleMetric, hac]
  by_cases hab : a = b
  · subst hab
    simp [tangleMetric]
  by_cases hbc : b = c
  · subst hbc
    simp [tangleMetric]
  have hle := tangleMetric_le_order (ins := ins) (θ := θ) hrad a c
  rcases tangleMetric_cases (ins := ins) (θ := θ) hrad hab with h₁ | ⟨-, W₁⟩
  · omega
  rcases tangleMetric_cases (ins := ins) (θ := θ) hrad hbc with h₂ | ⟨-, W₂⟩
  · omega
  set k₁ := tangleMetric H D ins θ a b
  set k₂ := tangleMetric H D ins θ b c
  by_cases hlt : θ ≤ k₁ + k₂
  · omega
  obtain ⟨u₁, W₁, a', b₁, ha₁, hb₁, hl₁, hk₁, hsa, hsb₁⟩ := W₁
  obtain ⟨u₂, W₂, b₂, c', hb₂, hc₂, hl₂, hk₂, hsb₂, hsc⟩ := W₂
  obtain ⟨hX, lX⟩ := theorem_8_5_proof hS hs W₁ hl₁
  obtain ⟨hY, lY⟩ := theorem_8_5_proof hS hs W₂ hl₂
  obtain ⟨z, hz₁, hz₂⟩ := corresponding_meet hrad hb₁ hb₂
  obtain ⟨T, hT, hXT, hYT, hl⟩ := exists_restraint_union hS hs hX hY
    ⟨z, hsb₁ hz₁, hsb₂ hz₂⟩ (by omega)
  obtain ⟨u, W, -, hlen, hlK, -, hd⟩ := hT.exists_walk hS
  have hins := insWalk_eq hS hs hT hd
  obtain ⟨k, hk⟩ := even_length_of_closed hrad W
  have hwit : MetricWitness H D ins θ a c k :=
    ⟨u, W, a', c', ha₁, hc₂, hlK, by omega, by rw [hins]; exact hsa.trans hXT, by
      rw [hins]; exact hsc.trans hYT⟩
  have := tangleMetric_le hwit
  omega

/-- A vertex and a region at it have distance at most one, if there is an edge. -/
theorem tangleMetric_le_one (hS : IsClosedSurface S) (hrad : (PaintingOrDrawing.drawing
  H).IsRadialDrawing D)
    (hE : H.E.Nonempty) {v : S} {r : Set S} (hv : v ∈ H.V) (hr : r ∈ H.R)
    (hvr : v ∈ closure r) : tangleMetric H D ins θ {v} r ≤ 1 := by
  have hP := hrad.2.1
  by_cases hθ2 : θ ≤ 1
  · exact (tangleMetric_le_order hP _ _).trans hθ2
  obtain ⟨c, ⟨hcr, hcV⟩, -⟩ := hP.2.2.1 r hr
  obtain ⟨e, he, hcap⟩ := exists_spoke_at ⟨hrad.1, hP⟩ hrad.2.2 hS hE hr hcr hcV hv hvr
  have hvD : v ∈ D.V := hP.2.1 hv
  have hl : D.toGraph.IsLink e v c := ⟨he, hvD, hcV, hcap⟩
  have hl' : D.toGraph.IsLink e c v := ⟨he, hcV, hvD, by rw [Set.pair_comm]; exact hcap⟩
  let W : GraphWalk D.toGraph v v := GraphWalk.cons hl (GraphWalk.cons hl' (GraphWalk.nil hvD))
  have hU : ∀ y ∈ W.support, y ∈ insWalk ins D W := fun y hy =>
    Or.inl ((mem_walkDrawing_U D W).mpr (Or.inl hy))
  refine tangleMetric_le ⟨v, W, {v}, {c}, ⟨Or.inl (Or.inl ⟨v, hv, rfl⟩), Or.inl (Or.inl ⟨v, hvD,
    rfl⟩),
    Or.inl ⟨v, hv, rfl, rfl⟩⟩, ⟨Or.inr hr, Or.inl (Or.inl ⟨c, hcV, rfl⟩),
    Or.inr (Or.inr ⟨hr, c, ⟨hcV, hcr⟩, rfl⟩)⟩, ?_, rfl, ?_, ?_⟩
  · change 2 < 2 * θ
    omega
  · rintro y rfl
    exact hU _ (by simp [W, GraphWalk.support])
  · rintro y rfl
    exact hU _ (by simp [W, GraphWalk.support])

end Tangle

end GraphMinor.GM11
