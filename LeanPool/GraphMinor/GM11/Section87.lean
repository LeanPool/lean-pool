/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM11.Section85
public import LeanPool.GraphMinor.GM11.CollarCut

/-!
# Graph Minors XI, (8.7)

`theorem_8_7` says that a walk `P` outside an extreme restraint `X`, between two points of `bd(X)`,
is longer
than some walk of `Γ ∩ bd(X)` between the same points.

We follow the proof in the paper. `exists_split_perimeter` cuts a shortest perimeter walk at the
ends of `P`.
It gives the walks `W₁, W₂` of the paper and the components `Δ₁, Δ₂`, by means of `exists_cut`.
`ins_side` is the step that `ins(P + W⁻¹)` includes one of `Δ₁, Δ₂`, and `no_cover` is the step that
it does
not include the far one.
-/

@[expose] public section

namespace GraphMinor.GM11

open Set Topology GraphMinor.Surface unitInterval

universe u

variable {S : Type u} [TopologicalSpace S] {Γ : Drawing S}

/-- The point set `U(Γ | W)` of a walk. -/
def walkPts {u v : S} (W : GraphWalk Γ.toGraph u v) : Set S :=
  {x | x ∈ W.support ∨ ∃ e ∈ W.edges, x ∈ closure e}

theorem mem_walkPts_append {u v w : S} (A : GraphWalk Γ.toGraph u v) (B : GraphWalk Γ.toGraph v w)
  {x : S} :
    x ∈ walkPts (A.append B) ↔ x ∈ walkPts A ∨ x ∈ walkPts B := by
  simp only [walkPts, mem_ofPred_eq, GraphWalk.mem_support_append, GraphWalk.edges_append,
    List.mem_append]
  constructor
  · rintro ((h | h) | ⟨e, he | he, hx⟩)
    · exact Or.inl (Or.inl h)
    · exact Or.inr (Or.inl h)
    · exact Or.inl (Or.inr ⟨e, he, hx⟩)
    · exact Or.inr (Or.inr ⟨e, he, hx⟩)
  · rintro ((h | ⟨e, he, hx⟩) | (h | ⟨e, he, hx⟩))
    · exact Or.inl (Or.inl h)
    · exact Or.inr ⟨e, Or.inl he, hx⟩
    · exact Or.inl (Or.inr h)
    · exact Or.inr ⟨e, Or.inr he, hx⟩

theorem mem_walkPts_reverse {u v : S} (A : GraphWalk Γ.toGraph u v) {x : S} :
    x ∈ walkPts A.reverse ↔ x ∈ walkPts A := by
  simp [walkPts, GraphWalk.support_reverse, GraphWalk.edges_reverse]

/-- A walk along a curve splits at each time at which the curve is at a vertex. -/
theorem runs_split {φ : ℝ → S} {u v : S} (W : GraphWalk Γ.toGraph u v) :
    ∀ {a b : ℝ}, RunsAlongOn Γ φ a b W → ∀ t ∈ Icc a b, φ t ∈ Γ.V →
      ∃ (x : S) (W₁ : GraphWalk Γ.toGraph u x) (W₂ : GraphWalk Γ.toGraph x v), φ t = x ∧
        W = W₁.append W₂ ∧ RunsAlongOn Γ φ a t W₁ ∧ RunsAlongOn Γ φ t b W₂ := by
  induction W with
  | @nil u hv =>
    rintro a b ⟨rfl, hu⟩ t ⟨h₁, h₂⟩ -
    obtain rfl : t = a := le_antisymm h₂ h₁
    exact ⟨u, .nil hv, .nil hv, hu, rfl, ⟨rfl, hu⟩, ⟨rfl, hu⟩⟩
  | @cons u y v e hlink rest ih =>
    rintro a b ⟨c, hac, hu, hin, him, hrest⟩ t ht hV
    rcases lt_or_ge t c with htc | htc
    · rcases eq_or_lt_of_le ht.1 with rfl | hat
      · exact ⟨u, .nil hlink.2.1, .cons hlink rest, hu, rfl, ⟨rfl, hu⟩, ⟨c, hac, hu, hin, him,
          hrest⟩⟩
      · have hm : φ t ∈ e := him ▸ mem_image_of_mem φ ⟨hat, htc⟩
        exact ((hlink.1.2.1 hm).2 hV).elim
    · obtain ⟨x, W₁, W₂, hx, rfl, h₁, h₂⟩ := ih hrest t ⟨htc, ht.2⟩ hV
      exact ⟨x, .cons hlink W₁, W₂, hx, rfl, ⟨c, hac, hu, hin, him, h₁⟩, h₂⟩

/-- A curve along a walk visits the vertices at finitely many times. -/
theorem runs_finite {φ : ℝ → S} {u v : S} (W : GraphWalk Γ.toGraph u v) :
    ∀ {a b : ℝ}, RunsAlongOn Γ φ a b W → {t | t ∈ Icc a b ∧ φ t ∈ Γ.V}.Finite := by
  induction W with
  | nil hv =>
    rintro a b ⟨rfl, -⟩
    refine (finite_singleton a).subset ?_
    rintro t ⟨⟨h₁, h₂⟩, -⟩
    exact le_antisymm h₂ h₁
  | @cons u y v e hlink rest ih =>
    rintro a b ⟨c, hac, hu, hin, him, hrest⟩
    refine ((ih hrest).insert a).subset ?_
    rintro t ⟨ht, hV⟩
    rcases lt_or_ge t c with htc | htc
    · rcases eq_or_lt_of_le ht.1 with rfl | hat
      · exact Or.inl rfl
      · have hm : φ t ∈ e := him ▸ mem_image_of_mem φ ⟨hat, htc⟩
        exact ((hlink.1.2.1 hm).2 hV).elim
    · exact Or.inr ⟨⟨htc, ht.2⟩, hV⟩

/-- A point of a curve along a walk is a point of the walk. -/
theorem runs_pts {φ : ℝ → S} {u v : S} (W : GraphWalk Γ.toGraph u v) {a b : ℝ}
    (h : RunsAlongOn Γ φ a b W) {t : ℝ} (ht : t ∈ Icc a b) : φ t ∈ walkPts W := by
  by_cases hV : φ t ∈ Γ.V
  · exact Or.inl (runs_vertex W h t ht hV)
  · obtain ⟨e, he, hm⟩ := runs_mem W h t ht hV
    exact Or.inr ⟨e, he, subset_closure hm⟩

theorem mem_V_of_mem_U' {D : Drawing S} (hD : D.IsSubdrawing Γ) {x : S} (hxU : x ∈ D.U)
    (hxV : x ∈ Γ.V) : x ∈ D.V := by
  rw [D.U_eq] at hxU
  rcases hxU with h | h
  · exact h
  · obtain ⟨g, hg, hxg⟩ := mem_iUnion₂.mp h
    exact (hD.closure_inter_V hg ▸ (⟨hxg, hxV⟩ : x ∈ closure g ∩ Γ.V) : x ∈ closure g ∩ D.V).2

variable [T2Space S]

/-- **The split of a perimeter walk.** Let `ψ` be a path outside `X` from `a` to `b`, with `a ≠ b`
in `bd(X)`.
Then there are walks `R₁, R₂` from `a` to `b` in `bd(X)`, of total length `l(X)`, as in the proof of
(8.7),
and two components of `Σ − (X ∪ L)`. The boundary `bd(X)` lies in the points of `R₁` and the closure
of the
second component, and it also lies in the points of `R₂` and the closure of the first. Each
component with a
limit point in `X − L` is one of the two. -/
theorem exists_split_perimeter [ConnectedSpace S] (hS : IsClosedSurface S)
    {X : Set S} (hXc : IsClosed X) (hXn : IsGammaNice Γ X)
    (hXs : IsSimplyConnectedSet X) (hne : X.Nonempty) (hu : X ≠ univ) {a b : S} (hab : a ≠ b)
    (haV : a ∈ Γ.V) (hbV : b ∈ Γ.V) {ψ : I → S} (hψ : Continuous ψ) (hψ0 : ψ 0 = a) (hψ1 : ψ 1 = b)
    (ha : a ∈ frontier X) (hb : b ∈ frontier X) (hψX : ∀ t ∈ Ioo (0 : I) 1, ψ t ∉ X) :
    ∃ (R₁ R₂ : GraphWalk Γ.toGraph a b) (y₁ y₂ : S), y₁ ∈ (X ∪ range ψ)ᶜ ∧ y₂ ∈ (X ∪ range ψ)ᶜ ∧
      R₁.length + R₂.length = perimeterWalkLength Γ X ∧
      walkPts R₁ ⊆ frontier X ∧ walkPts R₂ ⊆ frontier X ∧
      (∀ e ∈ R₁.edges, e ⊆ frontier X) ∧ (∀ e ∈ R₂.edges, e ⊆ frontier X) ∧
      frontier X ⊆ walkPts R₁ ∪ closure (connectedComponentIn (X ∪ range ψ)ᶜ y₂) ∧
      frontier X ⊆ walkPts R₂ ∪ closure (connectedComponentIn (X ∪ range ψ)ᶜ y₁) ∧
      ∀ y ∈ (X ∪ range ψ)ᶜ, ∀ x ∈ closure (connectedComponentIn (X ∪ range ψ)ᶜ y), x ∈ X
        → x ∉ range ψ →
        connectedComponentIn (X ∪ range ψ)ᶜ y = connectedComponentIn (X ∪ range ψ)ᶜ y₁ ∨
        connectedComponentIn (X ∪ range ψ)ᶜ y = connectedComponentIn (X ∪ range ψ)ᶜ y₂ := by
  classical
  obtain ⟨u₀, W, hper, hlen, -, hcount⟩ := exists_minimal_perimeterWalk hS hXc hXn hXs hne hu
  have hwd := walkDrawing_eq hS hXc hXn hper hcount
  obtain ⟨h, hinj, hoff, hrng, hop, hrun⟩ := hper
  rw [subBd_eq_frontier] at hrng
  have hbot : ∀ z, h (z, 0) ∈ X := fun z => hXc.frontier_subset (hrng ▸ mem_range_self z)
  have hrun' : RunsAlongOn Γ (collarCurve h) 0 1 W := by
    rcases hrun with ⟨-, hc⟩ | ⟨-, hr⟩
    · exfalso
      obtain ⟨z₁, hz₁⟩ := hrng.superset ha
      obtain ⟨z₂, hz₂⟩ := hrng.superset hb
      exact hab (hz₁.symm.trans ((hc z₁).trans ((hc z₂).symm.trans hz₂)))
    · exact hr
  let φ : ℝ → S := collarCurve h
  have hφ : ∀ t, φ t = h (circlePt t, 0) := fun _ => rfl
  have hperiod : ∀ t, φ (t + 1) = φ t := fun t => by
    simp only [hφ, circlePt]
    congr 2
    rw [mul_add, mul_one, Circle.exp_add, Circle.exp_two_pi, mul_one]
  have hfinite : ∀ v ∈ Γ.V, {z : Circle | h (z, 0) = v}.Finite := by
    intro v hv
    refine ((runs_finite W hrun').image circlePt).subset ?_
    intro z hz
    obtain ⟨t, ht, rfl⟩ := exists_circlePt_time 0 z
    have hz' : φ t = v := hz
    refine ⟨t, ⟨⟨ht.1, by linarith [ht.2]⟩, ?_⟩, rfl⟩
    rwa [show collarCurve h t = v from hz']
  have haX : a ∈ X := hXc.frontier_subset ha
  have hbX : b ∈ X := hXc.frontier_subset hb
  have hsymI : ∀ {t : I}, t ∈ Ioo (0 : I) 1 → unitInterval.symm t ∈ Ioo (0 : I) 1 := by
    intro t ht
    have h₁ : (0 : ℝ) < t := ht.1
    have h₂ : (t : ℝ) < 1 := ht.2
    constructor
    · change (0 : ℝ) < 1 - t
      linarith
    · change 1 - (t : ℝ) < 1
      linarith
  obtain ⟨z₀, hz₀, hl₀⟩ := exists_end_limit hinj hoff hbot hop hψ hψX (by rw [hψ0]; exact haX)
    (by rw [hψ0]; exact hfinite a haV)
  obtain ⟨z₁, hz₁, hl₁'⟩ := exists_end_limit (ψ := ψ ∘ unitInterval.symm) hinj hoff hbot hop
    (hψ.comp continuous_symm)
    (fun t ht => hψX _ (hsymI ht))
    (by simpa [hψ1] using hbX) (by simpa [hψ1] using hfinite b hbV)
  have hz₁' : h (z₁, 0) = b := by simpa [hψ1] using hz₁
  rw [hψ0] at hz₀
  have hl₁ : ∀ N ∈ 𝓝 ((z₁, 0) : Circle × I), ∃ s : I, s < 1 ∧ ∀ s' ∈ Ioo s (1 : I),
      collarInv h (ψ s') ∈ N := by
    intro N hN
    obtain ⟨s, hs, hsub⟩ := hl₁' N hN
    have hs₁ : (0 : ℝ) < s := hs
    refine ⟨unitInterval.symm s, ?_, fun s' hs' => ?_⟩
    · change 1 - (s : ℝ) < 1
      linarith
    · have h₁ : 1 - (s : ℝ) < s' := hs'.1
      have h₂ : (s' : ℝ) < 1 := hs'.2
      have := hsub (unitInterval.symm s') ⟨by
        change (0 : ℝ) < 1 - s'
        linarith, by
        change 1 - (s' : ℝ) < s
        linarith⟩
      simpa using this
  obtain ⟨τ₀, hτ₀, rfl⟩ := exists_circlePt_time 0 z₀
  obtain ⟨τ₁, hτ₁, rfl⟩ := exists_circlePt_time 0 z₁
  have hτ : τ₀ ≠ τ₁ := by
    rintro rfl
    exact hab (hz₀.symm.trans hz₁')
  have hφ₀ : φ τ₀ = a := hz₀
  have hφ₁ : φ τ₁ = b := hz₁'
  have hsplit : ∀ (lo hi : ℝ) (x y : S), 0 ≤ lo → lo < hi → hi < 1 → φ lo = x → φ hi = y → x ∈ Γ.V
    → y ∈ Γ.V →
      ∃ (B : GraphWalk Γ.toGraph x y) (D : GraphWalk Γ.toGraph y x), B.length + D.length = W.length
        ∧
        (∀ z, z ∈ walkPts B → z ∈ walkPts W) ∧ (∀ z, z ∈ walkPts D → z ∈ walkPts W) ∧
        (∀ e ∈ B.edges, e ∈ W.edges) ∧ (∀ e ∈ D.edges, e ∈ W.edges) ∧
        (∀ t ∈ Icc lo hi, φ t ∈ walkPts B) ∧ (∀ t ∈ Icc hi (lo + 1), φ t ∈ walkPts D) := by
    intro lo hi x y hlo hlh hhi hx hy hxV hyV
    subst hx hy
    obtain ⟨x', A, rest, hx', heq, hA, hrest⟩ := runs_split W hrun' lo ⟨hlo, by linarith⟩ hxV
    obtain rfl : x' = φ lo := hx'.symm
    obtain ⟨y', B, D, hy', heq₂, hB, hD⟩ := runs_split rest hrest hi ⟨hlh.le, hhi.le⟩ hyV
    obtain rfl : y' = φ hi := hy'.symm
    subst heq₂
    refine ⟨B, D.append A, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [heq]
      simp only [GraphWalk.length_append]
      omega
    · intro z hz
      rw [heq, mem_walkPts_append, mem_walkPts_append]
      exact Or.inr (Or.inl hz)
    · intro z hz
      rw [heq, mem_walkPts_append, mem_walkPts_append]
      rcases (mem_walkPts_append _ _).mp hz with h' | h'
      · exact Or.inr (Or.inr h')
      · exact Or.inl h'
    · intro e he
      rw [heq]
      simp [GraphWalk.edges_append, he]
    · intro e he
      rw [heq]
      rw [GraphWalk.edges_append, List.mem_append] at he
      simp only [GraphWalk.edges_append, List.mem_append]
      tauto
    · exact fun t ht => runs_pts B hB ht
    · intro t ht
      rw [mem_walkPts_append]
      rcases le_total t 1 with h₁ | h₁
      · exact Or.inl (runs_pts D hD ⟨ht.1, h₁⟩)
      · refine Or.inr ?_
        have := runs_pts A hA (t := t - 1) ⟨by linarith, by linarith [ht.2]⟩
        have heqp : φ (t - 1) = φ t := by
          have h₂ := hperiod (t - 1)
          rwa [sub_add_cancel, eq_comm] at h₂
        have h₃ : φ (t - 1) ∈ walkPts A := this
        rwa [heqp] at h₃
  have hWf : ∀ z ∈ walkPts W, z ∈ frontier X := by
    intro z hz
    have h₁ : z ∈ (walkDrawing Γ W).U := (mem_walkDrawing_U Γ W).mpr hz
    rw [hwd] at h₁
    exact interSet_U_subset isClosed_frontier h₁
  have hWe : ∀ e ∈ W.edges, e ⊆ frontier X := by
    intro e he
    have h₁ : e ∈ (walkDrawing Γ W).E := by
      rw [walkDrawing_E]
      exact he
    rw [hwd] at h₁
    change e ∈ (Γ.span _ _).E at h₁
    rw [Γ.span_E] at h₁
    exact h₁.1.2
  have hcov : ∀ lo hi : ℝ, lo < hi → hi < lo + 1 → ∀ {A₁ A₂ : Set S},
      (∀ t ∈ Icc lo hi, φ t ∈ A₁) → (∀ t ∈ Icc hi (lo + 1), φ t ∈ A₂) → frontier X ⊆ A₁ ∪ A₂ := by
    intro lo hi h₁ h₂ A₁ A₂ ha₁ ha₂ x hx
    obtain ⟨z, rfl⟩ := hrng.superset hx
    obtain ⟨t, ht, rfl⟩ := exists_circlePt_time lo z
    rcases le_total t hi with h' | h'
    · exact Or.inl (ha₁ t ⟨ht.1, h'⟩)
    · exact Or.inr (ha₂ t ⟨h', ht.2.le⟩)
  have hψr₀ : h (circlePt τ₀, 0) ∈ range ψ := ⟨0, by rw [hψ0]; exact hz₀.symm⟩
  have hψr₁ : h (circlePt τ₁, 0) ∈ range ψ := ⟨1, by rw [hψ1]; exact hz₁'.symm⟩
  have hl₁₁ : (0 : ℝ) ≤ τ₀ ∧ τ₀ < 1 ∧ 0 ≤ τ₁ ∧ τ₁ < 1 := ⟨hτ₀.1, by linarith [hτ₀.2], hτ₁.1, by
    linarith [hτ₁.2]⟩
  have hψ0X : ψ 0 ∈ X := by rw [hψ0]; exact haX
  have hψ1X : ψ 1 ∈ X := by rw [hψ1]; exact hbX
  rcases lt_or_gt_of_ne hτ with hlt | hlt
  · obtain ⟨y₁, hy₁, y₂, hy₂, hc₁, hc₂, hcomp⟩ := exists_cut hinj hoff hbot hop hψ hψX hψ0X hψ1X
      hl₀ hl₁
      hψr₀ hψr₁ hlt (by linarith [hl₁₁.2.2.2, hl₁₁.1]) (Or.inl ⟨rfl, rfl⟩)
    obtain ⟨B, D, hlenBD, hB, hD, hBe, hDe, hB₁, hD₁⟩ := hsplit τ₀ τ₁ a b hl₁₁.1 hlt hl₁₁.2.2.2 hφ₀
      hφ₁ haV hbV
    refine ⟨B, D.reverse, y₁, y₂, hy₁, hy₂, ?_, fun z hz => hWf z (hB z hz), fun z hz => hWf z (hD z
      ((mem_walkPts_reverse D).mp hz)), fun e he => hWe e (hBe e he), fun e he => hWe e
        (hDe e ?_), ?_, ?_, hcomp⟩
    · rw [GraphWalk.length_reverse, hlenBD, hlen]
    · rw [GraphWalk.edges_reverse] at he
      exact List.mem_reverse.mp he
    · exact hcov τ₀ τ₁ hlt (by linarith [hl₁₁.2.2.2, hl₁₁.1]) hB₁ hc₂
    · refine (hcov τ₀ τ₁ hlt (by linarith [hl₁₁.2.2.2, hl₁₁.1]) hc₁
        (fun t ht => (mem_walkPts_reverse D).mpr (hD₁ t ht))).trans ?_
      rw [union_comm]
  · obtain ⟨y₁, hy₁, y₂, hy₂, hc₁, hc₂, hcomp⟩ := exists_cut hinj hoff hbot hop hψ hψX hψ0X hψ1X
      hl₀ hl₁
      hψr₀ hψr₁ hlt (by linarith [hl₁₁.2.1, hl₁₁.2.2.1]) (Or.inr ⟨rfl, rfl⟩)
    obtain ⟨B, D, hlenBD, hB, hD, hBe, hDe, hB₁, hD₁⟩ := hsplit τ₁ τ₀ b a hl₁₁.2.2.1 hlt hl₁₁.2.1
      hφ₁ hφ₀ hbV haV
    refine ⟨B.reverse, D, y₁, y₂, hy₁, hy₂, ?_, fun z hz => hWf z (hB z
      ((mem_walkPts_reverse B).mp hz)), fun z hz => hWf z (hD z hz), fun e he => hWe e (hBe e ?_),
      fun e he => hWe e (hDe e he), ?_, ?_, hcomp⟩
    · rw [GraphWalk.length_reverse, hlenBD, hlen]
    · rw [GraphWalk.edges_reverse] at he
      exact List.mem_reverse.mp he
    · exact hcov τ₁ τ₀ hlt (by linarith [hl₁₁.2.1, hl₁₁.2.2.1])
        (fun t ht => (mem_walkPts_reverse B).mpr (hB₁ t ht)) hc₂
    · refine (hcov τ₁ τ₀ hlt (by linarith [hl₁₁.2.1, hl₁₁.2.2.1]) hc₁ hD₁).trans ?_
      rw [union_comm]

/-- `walkPts` is the point set of the walk's drawing. -/
theorem walkPts_eq {u v : S} (W : GraphWalk Γ.toGraph u v) : walkPts W = (walkDrawing Γ W).U := by
  ext x
  exact (mem_walkDrawing_U Γ W).symm

omit [T2Space S] in
theorem length_pos_of_ne {u v : S} (W : GraphWalk Γ.toGraph u v) (h : u ≠ v) : 0 < W.length := by
  cases W with
  | nil _ => exact absurd rfl h
  | cons _ _ => simp [GraphWalk.length, GraphWalk.edges]

omit [T2Space S] in
theorem exists_support_eq {u v : S} (W : GraphWalk Γ.toGraph u v) : ∃ l, W.support = u :: l := by
  cases W with
  | nil _ => exact ⟨[], rfl⟩
  | cons _ r => exact ⟨r.support, rfl⟩

omit [T2Space S] in
/-- A point in the closure of a component of an open set, inside the open set, is in the component.
-/
theorem mem_comp_of_closure [LocallyConnectedSpace S] {Y : Set S} (hY : IsOpen Y) {q x : S}
    (hx : x ∈ closure (connectedComponentIn Y q)) (hxY : x ∈ Y) : x ∈ connectedComponentIn Y q := by
  obtain ⟨t, ht₁, ht₂⟩ := mem_closure_iff.mp hx _ hY.connectedComponentIn
    (mem_connectedComponentIn hxY)
  rw [connectedComponentIn_eq ht₂, ← connectedComponentIn_eq ht₁]
  exact mem_connectedComponentIn hxY

variable {k : ℕ} {ins : Drawing S → Set S}

/-- **The step that `ins(P + W⁻¹)` includes a component.** Let `P` be a simple walk from `a` to `b`
outside
`X`, and `R` a walk from `a` to `b` in `X`. Let `y` be a point of `U(P)` outside `X`. Then each
neighbourhood
of `y` contains a point `q` of `Σ − (X ∪ U(P))` whose component is in `ins(P + R⁻¹)`, and this
component has a
limit point in `X − U(P)`. -/
theorem ins_side (hS : IsClosedSurface S) (hs : IsSlope Γ k ins) {X : Set S}
    (hXc : IsClosed X) {a b : S} (hab : a ≠ b) {P R : GraphWalk Γ.toGraph a b}
    (hP : P.IsSimple) (hPe : ∀ e ∈ P.edges, ¬ e ⊆ X) (hPv : ∀ x ∈ P.support, x ∈ X → x = a ∨ x = b)
    (hRX : walkPts R ⊆ X) (hRe : ∀ e ∈ R.edges, e ⊆ X) (hlen : (P.append R.reverse).length < k)
    {y : S} (hyL : y ∈ walkPts P) (hyX : y ∉ X) {O : Set S} (hO : IsOpen O) (hyO : y ∈ O) :
    ∃ q ∈ O, q ∈ (X ∪ walkPts P)ᶜ ∧
      connectedComponentIn (X ∪ walkPts P)ᶜ q ⊆ insWalk ins Γ (P.append R.reverse) ∧
      ∃ x ∈ closure (connectedComponentIn (X ∪ walkPts P)ᶜ q), x ∈ X ∧ x ∉ walkPts P := by
  classical
  have hlc : LocallyConnectedSpace S := IsClosedSurface.locallyConnectedSpace hS
  obtain ⟨R', hR's, hR'v, hR'e⟩ := GraphWalk.exists_isSimple R
  have hR'pts : ∀ x ∈ walkPts R', x ∈ walkPts R := by
    rintro x (hx | ⟨e, he, hx⟩)
    · exact Or.inl (hR'v x hx)
    · exact Or.inr ⟨e, hR'e e he, hx⟩
  let Q := P.append R'.reverse
  have hRpos : 0 < R'.length := length_pos_of_ne R' hab
  have hQs : Q.IsSimpleClosed := by
    obtain ⟨l₁, hl₁⟩ := exists_support_eq P
    obtain ⟨l₂, hl₂⟩ := exists_support_eq R'.reverse
    have hPn : (a :: l₁).Nodup := hl₁ ▸ hP
    have hRn : (b :: l₂).Nodup := hl₂ ▸ hR's.reverse
    refine ⟨?_, ?_⟩
    · rw [GraphWalk.support_append, hl₁, hl₂]
      change (l₁ ++ l₂).Nodup
      refine List.nodup_append.mpr ⟨(List.nodup_cons.mp hPn).2, (List.nodup_cons.mp hRn).2, ?_⟩
      intro x hx y' hy' hxy
      subst hxy
      have hxP : x ∈ P.support := by
        rw [hl₁]
        exact List.mem_cons_of_mem _ hx
      have hxR : x ∈ walkPts R := by
        refine hR'pts x (Or.inl ?_)
        have : x ∈ R'.reverse.support := by
          rw [hl₂]
          exact List.mem_cons_of_mem _ hy'
        rw [GraphWalk.support_reverse] at this
        exact List.mem_reverse.mp this
      rcases hPv x hxP (hRX hxR) with rfl | rfl
      · exact (List.nodup_cons.mp hPn).1 hx
      · exact (List.nodup_cons.mp hRn).1 hy'
    · rw [GraphWalk.edges_append]
      refine List.nodup_append.mpr ⟨hP.edges_nodup, hR's.reverse.edges_nodup, ?_⟩
      intro e he e' he' hee
      subst hee
      rw [GraphWalk.edges_reverse] at he'
      exact hPe e he (hRe e (hR'e e (List.mem_reverse.mp he')))
  have hQpos : 0 < Q.length := by
    rw [GraphWalk.length_append, GraphWalk.length_reverse]
    omega
  let G := walkDrawing Γ (P.append R.reverse)
  have hG : G.IsSubdrawing Γ := walkDrawing_isSubdrawing Γ _
  have hconf : IsConfined k G := isConfined_walk _ hlen
  have hCG : (walkDrawing Γ Q).IsSubdrawing G := by
    constructor
    · change _ ⊆ (walkDrawing Γ (P.append R.reverse)).V
      rw [walkDrawing_V, walkDrawing_V]
      intro x hx
      change x ∈ (P.append R.reverse).support
      rcases (GraphWalk.mem_support_append _ _).mp hx with h | h
      · exact (GraphWalk.mem_support_append _ _).mpr (Or.inl h)
      · refine (GraphWalk.mem_support_append _ _).mpr (Or.inr ?_)
        rw [GraphWalk.support_reverse] at h ⊢
        exact List.mem_reverse.mpr (hR'v x (List.mem_reverse.mp h))
    · change _ ⊆ (walkDrawing Γ (P.append R.reverse)).E
      rw [walkDrawing_E, walkDrawing_E]
      intro e he
      change e ∈ (P.append R.reverse).edges
      have he' : e ∈ Q.edges := he
      simp only [Q, GraphWalk.edges_append, List.mem_append, GraphWalk.edges_reverse,
        List.mem_reverse] at he' ⊢
      exact he'.imp id (hR'e e)
  have hC : (walkDrawing Γ Q).IsCircuit := isCircuit_walkDrawing Γ hQs hQpos
  let C := walkDrawing Γ Q
  have hl := hconf C hC hCG
  have hCΓ : C.IsSubdrawing Γ := hCG.trans hG
  have hd := hs.isClosedDisc C hC hCΓ hl
  obtain ⟨hf, hCins, -⟩ := ins_slope_facts hS hs hC hCΓ hl
  have hbd : discBd (ins C) = C.U := by
    rw [← IsClosedDisc.frontier_eq_discBd hS hd, hf]
  have hCU : C.U = walkPts Q := (walkPts_eq Q).symm
  have hLC : walkPts P ⊆ discBd (ins C) := by
    rw [hbd, hCU]
    exact fun x hx => (mem_walkPts_append _ _).mpr (Or.inl hx)
  have hCXL : discBd (ins C) ⊆ X ∪ walkPts P := by
    rw [hbd, hCU]
    intro x hx
    rcases (mem_walkPts_append _ _).mp hx with h | h
    · exact Or.inr h
    · exact Or.inl (hRX (hR'pts x ((mem_walkPts_reverse R').mp h)))
  have hLc : IsClosed (walkPts P) := by
    rw [walkPts_eq]
    exact Drawing.isClosed_U _
  have hYo : IsOpen (X ∪ walkPts P)ᶜ := (hXc.union hLc).isOpen_compl
  have hint := interior_eq_sdiff_discBd hS hd
  have hIo : IsOpen (ins C \ discBd (ins C)) := hint ▸ isOpen_interior
  have hIc := discBd_subset_closure hd (hLC hyL)
  obtain ⟨w, ⟨hwO, hwX⟩, hwI⟩ := mem_closure_iff.mp hIc _ (hO.inter hXc.isOpen_compl) ⟨hyO, hyX⟩
  obtain ⟨q, ⟨⟨hqO, hqX⟩, hqI⟩, hqU⟩ := exists_notMem_U (Γ := walkDrawing Γ P) hS
    ((hO.inter hXc.isOpen_compl).inter hIo) ⟨w, ⟨hwO, hwX⟩, hwI⟩
  rw [← walkPts_eq] at hqU
  have hqY : q ∈ (X ∪ walkPts P)ᶜ := fun h => h.elim hqX hqU
  have hQ'o := hYo.connectedComponentIn (x := q)
  have hQ'Y : connectedComponentIn (X ∪ walkPts P)ᶜ q ⊆ (X ∪ walkPts P)ᶜ
    := connectedComponentIn_subset _ _
  have hQ'p : IsPreconnected (connectedComponentIn (X ∪ walkPts P)ᶜ q)
    := isPreconnected_connectedComponentIn
  have hsubI : connectedComponentIn (X ∪ walkPts P)ᶜ q ⊆ ins C \ discBd (ins C) := by
    refine hQ'p.subset_left_of_subset_union hIo hd.isCompact.isClosed.isOpen_compl
      (disjoint_left.mpr fun x hx hx' => hx' hx.1) (fun x hx => ?_)
      ⟨q, mem_connectedComponentIn hqY, hqI⟩
    by_cases hxi : x ∈ ins C
    · exact Or.inl ⟨hxi, fun hb => hQ'Y hx (hCXL hb)⟩
    · exact Or.inr hxi
  have hinsZ : ins C ⊆ insWalk ins Γ (P.append R.reverse) := fun x hx =>
    Or.inr (mem_iUnion₂.mpr ⟨C, ⟨hC, hCG⟩, hx⟩)
  refine ⟨q, hqO, hqY, fun x hx => hinsZ (hsubI hx).1, ?_⟩
  by_contra hno
  push Not at hno
  have hIp : IsPreconnected (ins C \ discBd (ins C)) :=
    (isOpenDisc_interior hS hd).isPathConnected.isConnected.isPreconnected
  have hIQ : ins C \ discBd (ins C) ⊆ connectedComponentIn (X ∪ walkPts P)ᶜ q := by
    refine hIp.subset_of_closure_inter_subset hQ'o ⟨q, hqI, mem_connectedComponentIn hqY⟩ ?_
    rintro x ⟨hx₁, hx₂⟩
    have hxL : x ∉ walkPts P := fun h => hx₂.2 (hLC h)
    have hxX : x ∉ X := fun h => hxL (hno x hx₁ h)
    exact mem_comp_of_closure hYo hx₁ (fun h => h.elim hxX hxL)
  -- A point of an edge of `R'`.
  obtain ⟨e, he⟩ : ∃ e, e ∈ R'.edges := by
    by_contra hn
    push Not at hn
    have hnil : R'.edges = [] := List.eq_nil_iff_forall_not_mem.mpr hn
    have : R'.length = 0 := by simp [GraphWalk.length, hnil]
    omega
  have heΓ := mem_E_of_mem_edges R' he
  obtain ⟨r, hr⟩ := heΓ.1
  have hrX : r ∈ X := hRe e (hR'e e he) hr
  have hrC : r ∈ discBd (ins C) := by
    rw [hbd, hCU]
    refine (mem_walkPts_append _ _).mpr (Or.inr ((mem_walkPts_reverse R').mpr (Or.inr ⟨e, he,
      subset_closure hr⟩)))
  have hrL : r ∉ walkPts P := by
    have hrV : r ∉ Γ.V := (heΓ.2.1 hr).2
    rintro (h | ⟨f, hf, hrf⟩)
    · exact hrV (mem_V_of_mem_support P h)
    · have hfΓ := mem_E_of_mem_edges P hf
      have hrf' : r ∈ f := by
        rw [← Γ.closure_diff_V hfΓ]
        exact ⟨hrf, hrV⟩
      obtain rfl := Γ.edge_eq_of_mem heΓ hfΓ hr hrf'
      exact hPe e hf (hRe e (hR'e e he))
  exact hrL (hno r (closure_mono hIQ (discBd_subset_closure hd hrC)) hrX)

/-- A restraint `X` such that each restraint `Y ⊇ X` with `l(Y) + d ≤ l(X)` is `X`. With `d = 0`
this says that `X`
is extreme. With `d = 1` it says that no restraint `Y ⊇ X` has `l(Y) < l(X)`, which is the
hypothesis of (8.13). -/
def IsNearExtreme (Γ : Drawing S) (ins : Drawing S → Set S) (k d : ℕ) (X : Set S) : Prop :=
  IsRestraint Γ ins k X ∧ ∀ Y : Set S, IsRestraint Γ ins k Y → X ⊆ Y →
    perimeterWalkLength Γ Y + d ≤ perimeterWalkLength Γ X → Y = X

theorem IsExtremeRestraint.near {X : Set S} (h : IsExtremeRestraint Γ ins k X) :
    IsNearExtreme Γ ins k 0 X := h

theorem IsExtremeRestraint.near_one {X : Set S} (h : IsExtremeRestraint Γ ins k X) :
    IsNearExtreme Γ ins k 1 X :=
  ⟨h.1, fun Y hY hXY hl => h.2 Y hY hXY (by omega)⟩

/-- **The step that `ins(P + W⁻¹)` does not include the far component.** If a restraint `X₁` with
`l(X₁) ≤ l(X)`
contains `bd(X)` and a point outside the extreme restraint `X`, then we have a contradiction. -/
theorem no_cover [ConnectedSpace S] (hS : IsClosedSurface S)
    (hs : IsSlope Γ k ins) {X X₁ : Set S} {d : ℕ}
    (hX : IsNearExtreme Γ ins k d X) (hX₁ : IsRestraint Γ ins k X₁)
    (hl : perimeterWalkLength Γ X₁ + d ≤ perimeterWalkLength Γ X) (hbd : frontier X ⊆ X₁) {y : S}
    (hy : y ∈ X₁) (hyX : y ∉ X) : False := by
  have hr := hX.1
  have h₄ := theorem_8_4_proof hS hs hr hX₁ hX₁
  obtain ⟨w, hw⟩ := (ne_univ_iff_exists_notMem _).mp h₄
  have hwX : w ∉ X := fun h => hw (Or.inl (Or.inl h))
  have hwX₁ : w ∉ X₁ := fun h => hw (Or.inr h)
  have hc := isConnected_compl hS hX₁.isClosed hX₁.isGammaNice hX₁.isSimplyConnected hX₁.nonempty
    hX₁.ne_univ
  have hsub : X₁ᶜ ⊆ (closure X)ᶜ := by
    refine hc.isPreconnected.subset_right_of_subset_union isOpen_interior
      isClosed_closure.isOpen_compl
      (disjoint_left.mpr fun x hx hx' => hx' (subset_closure (interior_subset hx))) (fun x hx => ?_)
      ⟨w, hwX₁, ?_⟩
    · by_cases hxc : x ∈ closure X
      · refine Or.inl ?_
        by_contra hni
        exact hx (hbd ⟨hxc, hni⟩)
      · exact Or.inr hxc
    · rw [hr.isClosed.closure_eq]
      exact hwX
  have hXX₁ : X ⊆ X₁ := by
    intro x hx
    by_contra hn
    exact hsub hn (subset_closure hx)
  have heq := hX.2 X₁ hX₁ hXX₁ hl
  exact hyX (heq ▸ hy)

private theorem walk_points_inter_nice_set
    {S : Type u}
    [TopologicalSpace S]
    {Γ : Drawing S}
    [T2Space S]
    {X : Set S}
    {a : S}
    {b : S}
    (hXn : IsGammaNice Γ X)
    (P₁ : GraphWalk Γ.toGraph a b)
    (hP₁e' : ∀ e ∈ P₁.edges, ¬e ⊆ X)
    (hPv₁ : ∀ x ∈ P₁.support, x ∈ X → x = a ∨ x = b) :
    ∀ z ∈ walkPts P₁, z ∈ X → z = a ∨ z = b := by
  rintro z (hz | ⟨g, hg, hzg⟩) hzX
  · exact hPv₁ z hz hzX
  · by_cases hzV : z ∈ Γ.V
    · have hzU : z ∈ (walkDrawing Γ P₁).U := (mem_walkDrawing_U Γ P₁).mpr (Or.inr ⟨g, hg, hzg⟩)
      have hzD := mem_V_of_mem_U' (walkDrawing_isSubdrawing Γ P₁) hzU hzV
      rw [walkDrawing_V] at hzD
      exact hPv₁ z hzD hzX
    · have hgΓ := mem_E_of_mem_edges P₁ hg
      have hz' : z ∈ g := by
        rw [← Γ.closure_diff_V hgΓ]
        exact ⟨hzg, hzV⟩
      exact (hP₁e' g hg (nice_atom hXn (Or.inl (Or.inr hgΓ)) ⟨z, hz', hzX⟩)).elim

/-- The proof of (8.7) for a restraint `X` with `IsNearExtreme Γ ins k d X`. It finds a walk with
length less than the length of `P` plus `d`. -/
theorem exists_walk_near [ConnectedSpace S] (hS : IsClosedSurface S)
    (hs : IsSlope Γ k ins) {X : Set S} {d : ℕ} (hX : IsNearExtreme Γ ins k d X) {a b : S}
    (ha : a ∈ (Γ.interSet (subBd X)).V) (hb : b ∈ (Γ.interSet (subBd X)).V) (hab : a ≠ b)
    (P : GraphWalk Γ.toGraph a b) (hPe : ∀ e ∈ P.edges, ¬ e ⊆ X)
    (hPv : ∀ x ∈ P.support, x ∈ X → x = a ∨ x = b) :
    ∃ R : GraphWalk (Γ.interSet (subBd X)).toGraph a b, R.length < P.length + d := by
  classical
  have hlc : LocallyConnectedSpace S := IsClosedSurface.locallyConnectedSpace hS
  have hr := hX.1
  have hXc := hr.isClosed
  have hXn := hr.isGammaNice
  have hsb := subBd_eq_frontier X
  rw [hsb] at ha hb ⊢
  have hH : (Γ.interSet (frontier X)).IsSubdrawing Γ := Drawing.span_isSubdrawing Γ _ _
  have haV := hH.1 ha
  have hbV := hH.1 hb
  have haf : a ∈ frontier X := interSet_U_subset isClosed_frontier (Drawing.V_subset_U _ ha)
  have hbf : b ∈ frontier X := interSet_U_subset isClosed_frontier (Drawing.V_subset_U _ hb)
  have haX := hXc.frontier_subset haf
  have hbX := hXc.frontier_subset hbf
  obtain ⟨P₁, hP₁, hP₁v, hP₁e⟩ := GraphWalk.exists_isSimple P
  have hlen₁ : P₁.length ≤ P.length := (hP₁.edges_nodup.subperm hP₁e).length_le
  have hP₁e' : ∀ e ∈ P₁.edges, ¬ e ⊆ X := fun e he => hPe e (hP₁e e he)
  have hPv₁ : ∀ x ∈ P₁.support, x ∈ X → x = a ∨ x = b := fun x hx => hPv x (hP₁v x hx)
  have hline : IsLineWithEnds (walkPts P₁) a b := by
    have := walk_isLine Γ P₁ hP₁ hab
    have heq : walkPts P₁ = {x | x ∈ P₁.support} ∪ ⋃ e ∈ {e | e ∈ P₁.edges}, closure e := by
      ext x
      simp [walkPts]
    rwa [heq]
  have hLX : ∀ z ∈ walkPts P₁, z ∈ X → z = a ∨ z = b := by
    exact walk_points_inter_nice_set (S := S) (Γ := Γ) (X := X) (a := a) (b := b) hXn P₁ hP₁e'
      hPv₁
  obtain ⟨f, hf0, hf1⟩ := id hline
  let ψ : I → S := fun t => (f t).1
  have hψc : Continuous ψ := continuous_subtype_val.comp f.continuous
  have hrψ : range ψ = walkPts P₁ := by
    ext y
    exact ⟨by rintro ⟨t, rfl⟩; exact (f t).2, fun hy => ⟨f.symm ⟨y, hy⟩, by simp [ψ]⟩⟩
  have hψinj : Function.Injective ψ := fun s t h => f.injective (Subtype.ext h)
  have hψX : ∀ t ∈ Ioo (0 : I) 1, ψ t ∉ X := by
    intro t ht hm
    rcases hLX (ψ t) (hrψ ▸ mem_range_self t) hm with h | h
    · exact ht.1.ne' (hψinj (h.trans hf0.symm))
    · exact ht.2.ne (hψinj (h.trans hf1.symm))
  obtain ⟨R₁, R₂, y₁, y₂, hy₁, hy₂, hsum, hR₁f, hR₂f, hR₁e, hR₂e, hcov₁, hcov₂, hcomp⟩ :=
    exists_split_perimeter hS hXc hXn hr.isSimplyConnected hr.nonempty hr.ne_univ hab haV hbV hψc
      hf0 hf1
      haf hbf hψX
  rw [hrψ] at hy₁ hy₂ hcov₁ hcov₂ hcomp
  have htrans : ∀ R : GraphWalk Γ.toGraph a b, walkPts R ⊆ frontier X →
    (∀ e ∈ R.edges, e ⊆ frontier X) →
      R.length < P.length + d →
        ∃ R' : GraphWalk (Γ.interSet (frontier X)).toGraph a b, R'.length < P.length + d := by
    intro R hf he hl
    obtain ⟨R', -, hR'⟩ := hH.exists_walk_down R
      (fun x hx => Or.inl ⟨⟨mem_V_of_mem_support R hx, hf (Or.inl hx)⟩, mem_V_of_mem_support R hx⟩)
      (fun e hee => by
        change e ∈ (Γ.span _ _).E
        rw [Γ.span_E]
        have heΓ := mem_E_of_mem_edges R hee
        exact ⟨⟨heΓ, he e hee⟩, heΓ⟩)
    refine ⟨R', ?_⟩
    rw [GraphWalk.length, hR']
    exact hl
  by_cases h₁ : R₁.length < P₁.length + d
  · exact htrans R₁ hR₁f hR₁e (by omega)
  by_cases h₂ : R₂.length < P₁.length + d
  · exact htrans R₂ hR₂f hR₂e (by omega)
  exfalso
  push Not at h₁ h₂
  have hlk := hr.length_lt
  let Y := (X ∪ walkPts P₁)ᶜ
  have hLc : IsClosed (walkPts P₁) := by
    rw [walkPts_eq]
    exact Drawing.isClosed_U _
  have hYo : IsOpen Y := (hXc.union hLc).isOpen_compl
  -- The main step, for each of `R₁`, `R₂`.
  have hgen : ∀ (R : GraphWalk Γ.toGraph a b) (d₁ d₂ : Set S), walkPts R ⊆ frontier X →
      (∀ e ∈ R.edges, e ⊆ frontier X) → P₁.length + R.length + d ≤ perimeterWalkLength Γ X →
      frontier X ⊆ walkPts R ∪ closure d₂ →
      (∀ q ∈ Y, ∀ x ∈ closure (connectedComponentIn Y q), x ∈ X → x ∉ walkPts P₁ →
        connectedComponentIn Y q = d₁ ∨ connectedComponentIn Y q = d₂) →
      IsRestraint Γ ins k (insWalk ins Γ (P₁.append R.reverse)) ∧
      ∀ y ∈ walkPts P₁, y ∉ X → ∀ O : Set S, IsOpen O → y ∈ O →
        ∃ q ∈ O, q ∈ Y ∧ connectedComponentIn Y q = d₁ ∧ connectedComponentIn Y q ≠ d₂ ∧
          connectedComponentIn Y q ⊆ insWalk ins Γ (P₁.append R.reverse) := by
    intro R d₁ d₂ hRf hRe hlenR hcov hdich
    have hlw₀ : (P₁.append R.reverse).length + d ≤ perimeterWalkLength Γ X := by
      rw [GraphWalk.length_append, GraphWalk.length_reverse]
      exact hlenR
    have hlw : (P₁.append R.reverse).length ≤ perimeterWalkLength Γ X := by omega
    obtain ⟨hrw, hlr⟩ := theorem_8_5_proof hS hs (P₁.append R.reverse) (hlw.trans_lt hlk)
    refine ⟨hrw, fun y hyL hyX O hO hyO => ?_⟩
    obtain ⟨q, hqO, hqY, hsub, x, hx, hxX, hxL⟩ := ins_side hS hs hXc hab hP₁ hP₁e' hPv₁
      (hRf.trans hXc.frontier_subset) (fun e he => (hRe e he).trans hXc.frontier_subset)
      (hlw.trans_lt hlk) hyL hyX hO hyO
    have hUsub : ∀ z ∈ walkPts (P₁.append R.reverse), z ∈ insWalk ins Γ (P₁.append R.reverse)
      := fun z hz =>
      Or.inl ((walkPts_eq _).subset hz)
    have hne : connectedComponentIn Y q ≠ d₂ := by
      intro he
      have hcl : closure d₂ ⊆ insWalk ins Γ (P₁.append R.reverse) :=
        closure_minimal (he ▸ hsub) hrw.isClosed
      refine no_cover hS hs hX hrw (by omega) (fun z hz => ?_)
        (hUsub y ((mem_walkPts_append _ _).mpr (Or.inl hyL))) hyX
      rcases hcov hz with h' | h'
      · exact hUsub z ((mem_walkPts_append _ _).mpr (Or.inr ((mem_walkPts_reverse R).mpr h')))
      · exact hcl h'
    rcases hdich q hqY x hx hxX hxL with h' | h'
    · exact ⟨q, hqO, hqY, h', hne, hsub⟩
    · exact (hne h').elim
  obtain ⟨hr₁, hg₁⟩ := hgen R₁ _ _ hR₁f hR₁e (by omega) hcov₁ hcomp
  obtain ⟨hr₂, hg₂⟩ := hgen R₂ _ _ hR₂f hR₂e (by omega) hcov₂ fun q hq x hx hxX hxL =>
    (hcomp q hq x hx hxX hxL).symm
  -- A point of the line outside `X`.
  let t₀ : I := ⟨1 / 2, by norm_num, by norm_num⟩
  have ht₀ : t₀ ∈ Ioo (0 : I) 1 := ⟨by
    change (0 : ℝ) < 1 / 2
    norm_num, by
    change (1 / 2 : ℝ) < 1
    norm_num⟩
  have hy₀L : ψ t₀ ∈ walkPts P₁ := hrψ ▸ mem_range_self t₀
  have hy₀X := hψX t₀ ht₀
  obtain ⟨q₁, -, hq₁Y, hq₁, -, hq₁s⟩ := hg₁ _ hy₀L hy₀X univ isOpen_univ (mem_univ _)
  obtain ⟨q₂, -, hq₂Y, hq₂, -, hq₂s⟩ := hg₂ _ hy₀L hy₀X univ isOpen_univ (mem_univ _)
  have h₄ := theorem_8_4_proof hS hs hr hr₁ hr₂
  obtain ⟨w, hw⟩ := (ne_univ_iff_exists_notMem _).mp h₄
  have hwX : w ∉ X := fun h => hw (Or.inl (Or.inl h))
  have hwX₁ : w ∉ insWalk ins Γ (P₁.append R₁.reverse) := fun h => hw (Or.inl (Or.inr h))
  have hwX₂ : w ∉ insWalk ins Γ (P₁.append R₂.reverse) := fun h => hw (Or.inr h)
  have hwL : w ∉ walkPts P₁ := fun h =>
    hwX₁ (Or.inl ((walkPts_eq _).subset ((mem_walkPts_append _ _).mpr (Or.inl h))))
  have hwY : w ∈ Y := fun h => h.elim hwX hwL
  have hwQ : w ∈ connectedComponentIn Y w := mem_connectedComponentIn hwY
  have hne₁ : connectedComponentIn Y w ≠ connectedComponentIn Y y₁ := fun he =>
    hwX₁ (hq₁s (hq₁ ▸ he ▸ hwQ))
  have hne₂ : connectedComponentIn Y w ≠ connectedComponentIn Y y₂ := fun he =>
    hwX₂ (hq₂s (hq₂ ▸ he ▸ hwQ))
  have hno : ∀ x ∈ closure (connectedComponentIn Y w), x ∈ X → x ∈ walkPts P₁ := by
    intro x hx hxX
    by_contra hxL
    exact (hcomp w hwY x hx hxX hxL).elim hne₁ hne₂
  have hM := isConnected_compl hS hXc hXn hr.isSimplyConnected hr.nonempty hr.ne_univ
  have hQo : IsOpen (connectedComponentIn Y w) := hYo.connectedComponentIn
  obtain ⟨y', hy'c, hy'X, hy'Q⟩ : ∃ y' ∈ closure (connectedComponentIn Y w), y' ∉ X ∧
      y' ∉ connectedComponentIn Y w := by
    by_contra hall
    push Not at hall
    have hsub := hM.isPreconnected.subset_of_closure_inter_subset hQo ⟨w, hwX, hwQ⟩
      fun x hx => hall x hx.1 hx.2
    exact connectedComponentIn_subset _ _ (hsub hy₀X) (Or.inr hy₀L)
  have hy'L : y' ∈ walkPts P₁ := by
    by_contra hn
    exact hy'Q (mem_comp_of_closure hYo hy'c (fun h => h.elim hy'X hn))
  -- The two sides of the line near `y'`.
  have he₀ : walkPts P₁ \ {a, b} ∈ (lineDrawing hline hab).E := by
    rw [lineDrawing_E]
    rfl
  have hy'e : y' ∈ walkPts P₁ \ {a, b} := ⟨hy'L, by
    rintro (rfl | rfl)
    · exact hy'X haX
    · exact hy'X hbX⟩
  obtain ⟨W', A₁, A₂, -, -, hW'o, hy'W', -, hcover, hA₁p, hA₂p, hA₁U, hA₂U, -, -, -, -, -, -, -, -,
    hA₁X, hA₂X⟩ :=
    exists_edge_sides_off hS (lineDrawing hline hab) he₀ hy'e hXc hy'X
  have hAY : ∀ {A : Set S}, Disjoint A (lineDrawing hline hab).U → Disjoint A X → A ⊆ Y := by
    intro A h₁ h₂ x hx hm
    rcases hm with hm | hm
    · exact disjoint_left.mp h₂ hx hm
    · exact disjoint_left.mp h₁ hx hm
  have hside : ∀ q ∈ W', q ∈ Y → (q ∈ A₁ ∧ A₁ ⊆ connectedComponentIn Y q) ∨
      (q ∈ A₂ ∧ A₂ ⊆ connectedComponentIn Y q) := by
    intro q hqW hqY
    have hqL : q ∉ (lineDrawing hline hab).U := fun h => hqY (Or.inr h)
    rcases hcover ⟨hqW, hqL⟩ with h' | h'
    · exact Or.inl ⟨h', hA₁p.subset_connectedComponentIn h' (hAY hA₁U hA₁X)⟩
    · exact Or.inr ⟨h', hA₂p.subset_connectedComponentIn h' (hAY hA₂U hA₂X)⟩
  obtain ⟨q₀, hq₀W, hq₀Q⟩ := mem_closure_iff.mp hy'c W' hW'o hy'W'
  have hq₀Y : q₀ ∈ Y := connectedComponentIn_subset _ _ hq₀Q
  have hq₀e := connectedComponentIn_eq hq₀Q
  obtain ⟨q₃, hq₃W, hq₃Y, hq₃, hq₃n, -⟩ := hg₁ _ hy'L hy'X W' hW'o hy'W'
  obtain ⟨q₄, hq₄W, hq₄Y, hq₄, hq₄n, -⟩ := hg₂ _ hy'L hy'X W' hW'o hy'W'
  have hsame : ∀ {A : Set S} {q q' : S}, A.Nonempty → A ⊆ connectedComponentIn Y q →
      A ⊆ connectedComponentIn Y q' → connectedComponentIn Y q = connectedComponentIn Y q' := by
    rintro A q q' ⟨x, hx⟩ h₁ h₂
    exact (connectedComponentIn_eq (h₁ hx)).trans (connectedComponentIn_eq (h₂ hx)).symm
  have hn₀₃ : connectedComponentIn Y q₀ ≠ connectedComponentIn Y q₃ := by
    rw [← hq₀e, hq₃]
    exact hne₁
  have hn₀₄ : connectedComponentIn Y q₀ ≠ connectedComponentIn Y q₄ := by
    rw [← hq₀e, hq₄]
    exact hne₂
  have hn₃₄ : connectedComponentIn Y q₃ ≠ connectedComponentIn Y q₄ := by
    rw [hq₄]
    exact hq₃n
  rcases hside q₀ hq₀W hq₀Y with ⟨m₀, s₀⟩ | ⟨m₀, s₀⟩ <;>
    rcases hside q₃ hq₃W hq₃Y with ⟨m₃, s₃⟩ | ⟨m₃, s₃⟩ <;>
    rcases hside q₄ hq₄W hq₄Y with ⟨m₄, s₄⟩ | ⟨m₄, s₄⟩ <;>
    first
    | exact hn₀₃ (hsame ⟨_, m₀⟩ s₀ s₃)
    | exact hn₀₄ (hsame ⟨_, m₀⟩ s₀ s₄)
    | exact hn₃₄ (hsame ⟨_, m₃⟩ s₃ s₄)

/-- **(8.7)** of Graph Minors XI (page 98): "Let $X$ be an extreme restraint, and let $a, b \in
V(\Gamma \cap bd(X))$ be distinct. Let
$P$ be a walk in $\Gamma$ from $a$ to $b$, such that no edge or internal vertex of $P$ is in
$X$. Then there is a walk of $\Gamma \cap bd(X)$ from $a$ to $b$ which is shorter than $P$." -/
theorem theorem_8_7_proof [ConnectedSpace S] (hS : IsClosedSurface S)
    (hs : IsSlope Γ k ins) {X : Set S} (hX : IsExtremeRestraint Γ ins k X) {a b : S}
    (ha : a ∈ (Γ.interSet (subBd X)).V) (hb : b ∈ (Γ.interSet (subBd X)).V) (hab : a ≠ b)
    (P : GraphWalk Γ.toGraph a b) (hPe : ∀ e ∈ P.edges, ¬ e ⊆ X)
    (hPv : ∀ x ∈ P.support, x ∈ X → x = a ∨ x = b) :
    ∃ R : GraphWalk (Γ.interSet (subBd X)).toGraph a b, R.length < P.length :=
  exists_walk_near hS hs hX.near ha hb hab P hPe hPv

/-- (8.7), with `bd(X)` written as the frontier of `X`, for `IsNearExtreme`. -/
theorem exists_walk_near' [ConnectedSpace S] (hS : IsClosedSurface S)
    (hs : IsSlope Γ k ins) {X : Set S} {d : ℕ} (hX : IsNearExtreme Γ ins k d X) {a b : S}
    (ha : a ∈ (Γ.interSet (frontier X)).V) (hb : b ∈ (Γ.interSet (frontier X)).V) (hab : a ≠ b)
    (P : GraphWalk Γ.toGraph a b) (hPe : ∀ e ∈ P.edges, ¬ e ⊆ X)
    (hPv : ∀ x ∈ P.support, x ∈ X → x = a ∨ x = b) :
    ∃ R : GraphWalk (Γ.interSet (frontier X)).toGraph a b, R.length < P.length + d := by
  have := exists_walk_near hS hs hX (by rwa [subBd_eq_frontier]) (by rwa [subBd_eq_frontier])
    hab P hPe hPv
  rwa [subBd_eq_frontier] at this

end GraphMinor.GM11
