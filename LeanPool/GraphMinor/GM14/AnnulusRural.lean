/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM09.Section3a
public import LeanPool.GraphMinor.GM14.SegregationDrawing
public import LeanPool.GraphMinor.GM16.AnnulusPresentation
public import LeanPool.GraphMinor.GM16.DiscPlaneCoordinates

/-!
# A drawing between two discs is a rural neighbourhood

Let `Y` be a drawing of `G` between two closed discs `D₀ ⊆ D`, and let `Ω`, `Ω₀` be natural orders
of the vertices on `bd(D)` and on `bd(D₀)`. Then `(G, Ω, Ω₀)` is rural, and nested circuits around
`D₀` give a nest. In (8.4) the graph is not a drawing with vertices in `S`, and the orders are
given.
So we state this for an abstract graph, and keep the given orders.
-/


@[expose] public section

namespace GraphMinor.GM14

open Set Topology Graph GraphMinor GraphMinor.GM09 GraphMinor.Surface GraphMinor.GM11
  GraphMinor.GM16

universe u v w

variable {α : Type u} {β : Type v} {S : Type w} [TopologicalSpace S] [T2Space S] [CompactSpace S]
  [Nonempty S]

omit [T2Space S] [CompactSpace S] [Nonempty S] in
/-- A natural order depends only on the points of its vertices. -/
theorem IsNaturalOrderFrom.congr {ν ν' : α → S} {Ω : CyclicPerm α} {F : Set S}
    (h : IsNaturalOrderFrom ν Ω F) (he : ∀ v ∈ Ω.bar, ν' v = ν v) :
    IsNaturalOrderFrom ν' Ω F := by
  obtain ⟨hF, φ, hm, hc⟩ := h
  refine ⟨hF, φ, fun v hv => he v hv ▸ hm v hv, fun v₁ v₂ v₃ h₃ => ?_⟩
  obtain ⟨t₁, t₂, t₃, h₁₂, h₂₃, h₃₁, e₁, e₂, e₃⟩ := hc v₁ v₂ v₃ h₃
  have hm₃ := (Ω.isClockwise3_iff.mp h₃).2.2.2
  exact ⟨t₁, t₂, t₃, h₁₂, h₂₃, h₃₁, e₁.trans (he v₁ hm₃.1).symm, e₂.trans (he v₂ hm₃.2.1).symm,
    e₃.trans (he v₃ hm₃.2.2.1).symm⟩

/-! ### Reversing a cyclic permutation (`Ω⁻¹`) and invariance of crooked transactions -/

@[simp]
theorem reverse_bar (Ω : CyclicPerm α) : Ω⁻¹.bar = Ω.bar := rfl

theorem iterate_invFunBar_toFun (Ω : CyclicPerm α) (n : ℕ) {z : α} (hz : z ∈ Ω.bar) :
    (Ω.invFunBar^[n]) ((Ω.toFun^[n]) z) = z := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [Function.iterate_succ_apply, Function.iterate_succ_apply',
      Ω.invFunBar_toFun (Ω.iterate_mem n hz)]
    exact ih

theorem iterate_toFun_invFunBar (Ω : CyclicPerm α) (n : ℕ) {z : α} (hz : z ∈ Ω.bar) :
    (Ω.toFun^[n]) ((Ω.invFunBar^[n]) z) = z := by
  induction n with
  | zero => rfl
  | succ n ih =>
    have hmem : (Ω.invFunBar^[n]) z ∈ Ω.bar := Ω⁻¹.iterate_mem n hz
    rw [Function.iterate_succ_apply, Function.iterate_succ_apply', Ω.toFun_invFunBar hmem]
    exact ih

theorem iterate_invFunBar_sub (Ω : CyclicPerm α) {k j : ℕ} (hj : j ≤ k) {x : α}
    (hx : x ∈ Ω.bar) :
    (Ω.invFunBar^[j]) ((Ω.toFun^[k]) x) = (Ω.toFun^[k - j]) x := by
  have hk : k = j + (k - j) := (Nat.add_sub_of_le hj).symm
  conv_lhs => rw [hk, Function.iterate_add_apply]
  exact iterate_invFunBar_toFun Ω j (Ω.iterate_mem (k - j) hx)

theorem firstHitIn_reverse_of_firstHitIn {Ω : CyclicPerm α} {X : Set α} {x y : α}
    (hx : x ∈ Ω.bar) (hxX : x ∈ X) (h : Ω.FirstHitIn X x y) :
    Ω⁻¹.FirstHitIn X y x := by
  rcases h with ⟨k, hk1, rfl, hyX, hmin⟩
  refine ⟨k, hk1, iterate_invFunBar_toFun Ω k hx, hxX, fun j hj1 hjlt => ?_⟩
  change (Ω.invFunBar^[j]) ((Ω.toFun^[k]) x) ∉ X
  rw [iterate_invFunBar_sub Ω (le_of_lt hjlt) hx]
  exact hmin (k - j) (Nat.le_sub_of_add_le (by omega)) (Nat.sub_lt (by omega) (by omega))

theorem firstHitIn_of_firstHitIn_reverse {Ω : CyclicPerm α} {X : Set α} {x y : α}
    (hy : y ∈ Ω.bar) (hyX : y ∈ X) (h : Ω⁻¹.FirstHitIn X y x) :
    Ω.FirstHitIn X x y := by
  rcases h with ⟨k, hk1, hky, hxX, hmin⟩
  change (Ω.invFunBar^[k]) y = x at hky
  subst hky
  have hsub : ∀ {j : ℕ}, j ≤ k → (Ω.toFun^[j]) ((Ω.invFunBar^[k]) y) = (Ω.invFunBar^[k - j]) y := by
    intro j hj
    have hk : k = j + (k - j) := (Nat.add_sub_of_le hj).symm
    have hmem : (Ω.invFunBar^[k - j]) y ∈ Ω.bar := Ω⁻¹.iterate_mem (k - j) hy
    conv_lhs => rw [hk, Function.iterate_add_apply]
    exact iterate_toFun_invFunBar Ω j hmem
  refine ⟨k, hk1, ?_, hyX, fun j hj1 hjlt => ?_⟩
  · rw [hsub (le_refl k), Nat.sub_self, Function.iterate_zero_apply]
  · rw [hsub (le_of_lt hjlt)]
    exact hmin (k - j) (Nat.le_sub_of_add_le (by omega)) (Nat.sub_lt (by omega) (by omega))

theorem isClockwise3_reverse_iff {Ω : CyclicPerm α} {v₁ v₂ v₃ : α} :
    Ω⁻¹.IsClockwise3 v₁ v₂ v₃ ↔ Ω.IsClockwise3 v₁ v₃ v₂ := by
  rw [CyclicPerm.isClockwise3_iff, CyclicPerm.isClockwise3_iff]
  have hset : ({v₁, v₃, v₂} : Set α) = {v₁, v₂, v₃} := by ext x; simp [or_comm]
  rw [hset]
  simp only [reverse_bar]
  refine ⟨fun ⟨h12, h13, h23, hv1, hv2, hv3, hhit12, hhit23, hhit31⟩ =>
    ⟨h13, h12, h23.symm, hv1, hv3, hv2,
      firstHitIn_of_firstHitIn_reverse hv3 (by simp) hhit31,
      firstHitIn_of_firstHitIn_reverse hv2 (by simp) hhit23,
      firstHitIn_of_firstHitIn_reverse hv1 (by simp) hhit12⟩,
    fun ⟨h13, h12, h32, hv1, hv3, hv2, hhit13, hhit32, hhit21⟩ =>
    ⟨h12, h13, h32.symm, hv1, hv2, hv3,
      firstHitIn_reverse_of_firstHitIn hv2 (by simp) hhit21,
      firstHitIn_reverse_of_firstHitIn hv3 (by simp) hhit32,
      firstHitIn_reverse_of_firstHitIn hv1 (by simp) hhit13⟩⟩

theorem interval_reverse (Ω : CyclicPerm α) (a b : α) :
    Ω⁻¹.interval a b = Ω.interval b a := by
  ext v
  simp only [CyclicPerm.interval, reverse_bar, mem_ofPred_eq, mem_sdiff, mem_insert_iff,
    mem_singleton_iff, isClockwise3_reverse_iff]
  refine ⟨fun ⟨⟨hv, hne⟩, hcw⟩ => ⟨⟨hv, by tauto⟩, Ω.isClockwise3_rotate hcw⟩,
    fun ⟨⟨hv, hne⟩, hcw⟩ => ⟨⟨hv, by tauto⟩, Ω.isClockwise3_rotate (Ω.isClockwise3_rotate hcw)⟩⟩

theorem crosses_reverse_iff (Ω : CyclicPerm α) {a₁ b₁ a₂ b₂ : α} :
    Ω⁻¹.Crosses a₁ b₁ a₂ b₂ ↔ Ω.Crosses a₁ b₁ a₂ b₂ := by
  rw [Ω⁻¹.crosses_iff_interval, Ω.crosses_iff_interval, interval_reverse, interval_reverse]
  tauto

theorem isFence_reverse_iff (Ω : CyclicPerm α) {A B : Set α} :
    Ω⁻¹.IsFence A B ↔ Ω.IsFence A B := by
  simp only [CyclicPerm.IsFence, reverse_bar, crosses_reverse_iff]

theorem isOmegaPathWithEnds_of_eq_or_reverse {S₁ S₂ : Society α β} (hG : S₁.G = S₂.G)
    (hΩ : S₁.Ω = S₂.Ω ∨ S₁.Ω = S₂.Ω⁻¹) {P : Graph α β} {a b : α} :
    S₁.IsOmegaPathWithEnds P a b ↔ S₂.IsOmegaPathWithEnds P a b := by
  have hbar : S₁.Ω.bar = S₂.Ω.bar := by rcases hΩ with h | h <;> simp [h]
  simp only [Society.IsOmegaPathWithEnds, hG, hbar]

theorem transactionEnds_of_eq_or_reverse {S₁ S₂ : Society α β} (hG : S₁.G = S₂.G)
    (hΩ : S₁.Ω = S₂.Ω ∨ S₁.Ω = S₂.Ω⁻¹) (P_set : Set (Graph α β)) :
    S₁.transactionEnds P_set = S₂.transactionEnds P_set := by
  ext v
  simp only [Society.transactionEnds, mem_ofPred_eq, isOmegaPathWithEnds_of_eq_or_reverse hG hΩ]

theorem isCrookedTransaction_of_eq_or_reverse {S₁ S₂ : Society α β} (hG : S₁.G = S₂.G)
    (hΩ : S₁.Ω = S₂.Ω ∨ S₁.Ω = S₂.Ω⁻¹) {P_set : Set (Graph α β)} :
    S₁.IsCrookedTransaction P_set ↔ S₂.IsCrookedTransaction P_set := by
  have hpath : ∀ {P a b}, S₁.IsOmegaPathWithEnds P a b ↔ S₂.IsOmegaPathWithEnds P a b :=
    isOmegaPathWithEnds_of_eq_or_reverse hG hΩ
  have hop : ∀ {P}, S₁.IsOmegaPath P ↔ S₂.IsOmegaPath P := by
    intro P; simp only [Society.IsOmegaPath, hpath]
  have hdisj : S₁.IsDisjointOmegaPathSet P_set ↔ S₂.IsDisjointOmegaPathSet P_set := by
    simp only [Society.IsDisjointOmegaPathSet, hop]
  have hfe : ∀ {A B}, S₁.Ω.IsFence A B ↔ S₂.Ω.IsFence A B := by
    intro A B
    rcases hΩ with h | h
    · rw [h]
    · rw [h, isFence_reverse_iff]
  have hff : ∀ {A B}, S₁.IsFenceFor P_set A B ↔ S₂.IsFenceFor P_set A B := by
    intro A B; simp only [Society.IsFenceFor, hdisj, hfe, hpath]
  have htr : S₁.IsTransaction P_set ↔ S₂.IsTransaction P_set := by
    simp only [Society.IsTransaction, hff]
  have hends : S₁.transactionEnds P_set = S₂.transactionEnds P_set :=
    transactionEnds_of_eq_or_reverse hG hΩ P_set
  have hper : ∀ {P}, S₁.IsPeripheralIn P_set P ↔ S₂.IsPeripheralIn P_set P := by
    intro P
    rcases hΩ with h | h
    · simp only [Society.IsPeripheralIn, hpath, hends, h]
    · simp only [Society.IsPeripheralIn, hpath, hends, h, interval_reverse, or_comm]
  simp only [Society.IsCrookedTransaction, htr, hper]

omit [T2Space S] [CompactSpace S] [Nonempty S] in
/-- Reversing a cyclic permutation preserves `IsNaturalOrderFrom` (by reversing the circle). -/
theorem IsNaturalOrderFrom.reverse {ν : α → S} {Ω : CyclicPerm α} {F : Set S}
    (h : IsNaturalOrderFrom ν Ω F) :
    IsNaturalOrderFrom ν Ω⁻¹ F := by
  obtain ⟨hF, φ, hm, hc⟩ := h
  let φ' : Circle ≃ₜ F := (Homeomorph.inv Circle).trans φ
  have hφ' : ∀ w : Circle, (φ' w).1 = (φ w⁻¹).1 := fun _ => rfl
  refine ⟨hF, φ', fun v hv => hm v hv, fun v₁ v₂ v₃ hcw => ?_⟩
  rw [isClockwise3_reverse_iff] at hcw
  obtain ⟨t₁, t₃, t₂, ht13, ht32, ht21, e₁, e₃, e₂⟩ := hc v₁ v₃ v₂ hcw
  refine ⟨-t₁, -t₂ + 2 * Real.pi, -t₃ + 2 * Real.pi,
    by linarith, by linarith, by linarith, ?_, ?_, ?_⟩
  · rw [hφ', ← Circle.exp_neg, neg_neg, e₁]
  · have hexp : (Circle.exp (-t₂ + 2 * Real.pi))⁻¹ = Circle.exp t₂ := by
      rw [← Circle.exp_neg, show -(-t₂ + 2 * Real.pi) = t₂ - 2 * Real.pi by ring,
        ← Surface.exp_add_two_pi' (t₂ - 2 * Real.pi), sub_add_cancel]
    rw [hφ', hexp, e₂]
  · have hexp : (Circle.exp (-t₃ + 2 * Real.pi))⁻¹ = Circle.exp t₃ := by
      rw [← Circle.exp_neg, show -(-t₃ + 2 * Real.pi) = t₃ - 2 * Real.pi by ring,
        ← Surface.exp_add_two_pi' (t₃ - 2 * Real.pi), sub_add_cancel]
    rw [hφ', hexp, e₃]

theorem drawingAgreesWithOArcHomeo_inv {G : Graph α β} {Γ : GraphDrawing G EuclideanPlane}
    {Ω : CyclicPerm α} {C : Set EuclideanPlane} {φ : Circle ≃ₜ C}
    (h : DrawingAgreesWithOArcHomeo Γ Ω C φ) :
    DrawingAgreesWithOArcHomeo Γ Ω⁻¹ C ((Homeomorph.inv Circle).trans φ) := by
  let φ' : Circle ≃ₜ C := (Homeomorph.inv Circle).trans φ
  have hφ' : ∀ w : Circle, (φ' w).1 = (φ w⁻¹).1 := fun _ => rfl
  refine ⟨fun v hv => h.1 v hv, fun v₁ v₂ v₃ hcw => ?_⟩
  rw [isClockwise3_reverse_iff] at hcw
  obtain ⟨t₁, t₃, t₂, ht13, ht32, ht21, e₁, e₃, e₂⟩ := h.2 v₁ v₃ v₂ hcw
  refine ⟨-t₁, -t₂ + 2 * Real.pi, -t₃ + 2 * Real.pi,
    by linarith, by linarith, by linarith, ?_, ?_, ?_⟩
  · rw [hφ', ← Circle.exp_neg, neg_neg]
    exact e₁
  · have hexp : (Circle.exp (-t₂ + 2 * Real.pi))⁻¹ = Circle.exp t₂ := by
      rw [← Circle.exp_neg, show -(-t₂ + 2 * Real.pi) = t₂ - 2 * Real.pi by ring,
        ← Surface.exp_add_two_pi' (t₂ - 2 * Real.pi), sub_add_cancel]
    rw [hφ', hexp]
    exact e₂
  · have hexp : (Circle.exp (-t₃ + 2 * Real.pi))⁻¹ = Circle.exp t₃ := by
      rw [← Circle.exp_neg, show -(-t₃ + 2 * Real.pi) = t₃ - 2 * Real.pi by ring,
        ← Surface.exp_add_two_pi' (t₃ - 2 * Real.pi), sub_add_cancel]
    rw [hφ', hexp]
    exact e₃

omit [Nonempty S] in
/-- Plane disc coordinates for `D` chosen (reflecting by `conjPlane` if necessary) so that a given
boundary parametrization `φ : Circle ≃ₜ discBd D` transports to a clockwise boundary homeomorphism
on `subBd (f '' D)`. -/
theorem exists_clockwise_plane_disc_coordinates {D : Set S} (hD : IsClosedDisc D)
    (φ : Circle ≃ₜ discBd D) :
    ∃ (f : S → EuclideanPlane) (g : EuclideanPlane → S) (φ' : Circle ≃ₜ subBd (f '' D)),
      Continuous f ∧ InjOn f D ∧ ContinuousOn g (f '' D) ∧ LeftInvOn g f D ∧
      (∀ E ⊆ D, IsClosedDisc E → IsClosedDisc (f '' E) ∧ subBd (f '' E) = f '' discBd E) ∧
      IsClockwiseDiscHomeo (f '' D) φ' ∧ ∀ t : Circle, (φ' t).1 = f (φ t).1 := by
  classical
  obtain ⟨f₀, g₀, hf₀, hi₀, hg₀, hgf₀, hdisc₀⟩ := exists_plane_disc_coordinates hD
  obtain ⟨hΔ₀_disc, hbd₀⟩ := hdisc₀ D Subset.rfl hD
  obtain ⟨φ'₀, hφ'₀⟩ := transport_circle_parametrization hf₀.continuousOn hg₀ hgf₀
    (GraphMinor.GM11.discBd_subset D) hbd₀ φ
  by_cases hcw : IsClockwiseDiscHomeo (f₀ '' D) φ'₀
  · exact ⟨f₀, g₀, φ'₀, hf₀, hi₀, hg₀, hgf₀, hdisc₀, hcw, hφ'₀⟩
  · let f : S → EuclideanPlane := conjPlane ∘ f₀
    let g : EuclideanPlane → S := g₀ ∘ conjPlane.symm
    have hf : Continuous f := conjPlane.continuous.comp hf₀
    have hi : InjOn f D := conjPlane.injective.comp_injOn hi₀
    have hg : ContinuousOn g (f '' D) := by
      refine hg₀.comp conjPlane.symm.continuous.continuousOn ?_
      rintro _ ⟨x, hx, rfl⟩
      exact ⟨x, hx, by simp [f]⟩
    have hgf : LeftInvOn g f D := fun x hx => by simp [f, g, hgf₀ hx]
    have hdisc : ∀ E ⊆ D, IsClosedDisc E →
        IsClosedDisc (f '' E) ∧ subBd (f '' E) = f '' discBd E := by
      intro E hED hE
      obtain ⟨hEd, hEb⟩ := hdisc₀ E hED hE
      have himg : f '' E = conjPlane '' (f₀ '' E) := Set.image_comp conjPlane f₀ E
      refine ⟨himg ▸ isClosedDisc_image_conjPlane hEd, ?_⟩
      rw [himg, subBd_image_conjPlane, hEb, ← Set.image_comp]
    obtain ⟨φ', hφ'⟩ := transport_circle_parametrization hf.continuousOn hg hgf
      (GraphMinor.GM11.discBd_subset D) (hdisc D Subset.rfl hD).2 φ
    have hcw' : IsClockwiseDiscHomeo (f '' D) φ' := by
      have hcw_conj := isClockwiseDiscHomeo_conjPlane_of_not hΔ₀_disc rfl hcw
      have himg : f '' D = conjPlane '' (f₀ '' D) := Set.image_comp conjPlane f₀ D
      intro x hx
      rw [himg] at hx
      have h1 := hcw_conj x hx
      have hfun : (fun w : Circle => complexPlane.symm (φ' w).1) =
          (fun w : Circle => complexPlane.symm
            ((φ'₀.trans (conjPlane.toHomeomorph.image (subBd (f₀ '' D)))) w).1) := by
        ext w
        exact congrArg complexPlane.symm ((hφ' w).trans (congrArg conjPlane (hφ'₀ w).symm))
      rwa [hfun]
    exact ⟨f, g, φ', hf, hi, hg, hgf, hdisc, hcw', hφ'⟩

/-- Given two nested closed discs `D₀ ⊆ D` on a surface `S` with natural orders `Ω` on `discBd D`
and `Ω₀` on `discBd D₀`, there is a choice of `Ω₀' ∈ {Ω₀, Ω₀⁻¹}` whose orientation is compatible
with `Ω`, so that any drawing between `D` and `D₀` with boundary orders `Ω` and `Ω₀'` has a
presentation. -/
theorem exists_presentation_of_drawing {D D₀ : Set S} (hD : IsClosedDisc D) (hD₀ : IsClosedDisc D₀)
    (hD₀D : D₀ ⊆ D) {ν : α → S} {Ω Ω₀ : CyclicPerm α}
    (hnat : IsNaturalOrderFrom ν Ω (discBd D)) (hnat₀ : IsNaturalOrderFrom ν Ω₀ (discBd D₀)) :
    ∃ Ω₀' : CyclicPerm α, (Ω₀' = Ω₀ ∨ Ω₀' = Ω₀⁻¹) ∧ Ω₀'.bar = Ω₀.bar ∧
      IsNaturalOrderFrom ν Ω₀' (discBd D₀) ∧
      ∀ (N : Neighborhood α β) (Y : GraphDrawing N.G S),
        N.Ω = Ω → N.Ω₀ = Ω₀' →
        Y.drawing.U ⊆ D \ discInt D₀ →
        (∀ v : V(N.G), (Y.iso.vertexEquiv v).1 = ν v.1) →
        (∀ v ∈ V(N.G), ν v ∈ discBd D ↔ v ∈ N.Ω.bar) →
        (∀ v ∈ V(N.G), ν v ∈ discBd D₀ ↔ v ∈ N.Ω₀.bar) →
        ∃ (P : Presentation N) (f : S → EuclideanPlane), Continuous f ∧ InjOn f D ∧
          P.Δ = f '' D ∧ P.Δ₀ = f '' D₀ ∧
          (∀ E ⊆ D, IsClosedDisc E → IsClosedDisc (f '' E) ∧ subBd (f '' E) = f '' discBd E) ∧
          ∀ J, graphDrawingSubgraphU P.Γ J = f '' graphDrawingSubgraphU Y J := by
  classical
  obtain ⟨-, φ, hm, hc⟩ := hnat
  obtain ⟨-, φ₀, hm₀, hc₀⟩ := id hnat₀
  obtain ⟨f, g, φ', hf, hi, hg, hgf, hdisc, hcw_D, hφ'⟩ :=
    exists_clockwise_plane_disc_coordinates hD φ
  obtain ⟨hΔ, hbd⟩ := hdisc D Subset.rfl hD
  obtain ⟨hΔ₀, hbd₀⟩ := hdisc D₀ hD₀D hD₀
  obtain ⟨φ₀', hφ₀'⟩ := transport_circle_parametrization hf.continuousOn hg hgf
    ((GraphMinor.GM11.discBd_subset D₀).trans hD₀D) hbd₀ φ₀
  let Ω₀' : CyclicPerm α := if IsClockwiseDiscHomeo (f '' D₀) φ₀' then Ω₀ else Ω₀⁻¹
  have hΩ₀'_or : Ω₀' = Ω₀ ∨ Ω₀' = Ω₀⁻¹ := by
    by_cases h : IsClockwiseDiscHomeo (f '' D₀) φ₀' <;> simp [Ω₀', h]
  have hΩ₀'_bar : Ω₀'.bar = Ω₀.bar := by
    rcases hΩ₀'_or with h | h <;> simp [h]
  have hnat₀' : IsNaturalOrderFrom ν Ω₀' (discBd D₀) := by
    rcases hΩ₀'_or with h | h
    · rw [h]; exact hnat₀
    · rw [h]; exact hnat₀.reverse
  refine ⟨Ω₀', hΩ₀'_or, hΩ₀'_bar, hnat₀', ?_⟩
  intro N Y hNΩ hNΩ₀ hY hν hbar hbar₀
  have hUD : Y.drawing.U ⊆ D := fun x hx => (hY hx).1
  have hUc : IsCompact Y.drawing.U := hD.isCompact.of_isClosed_subset Y.drawing.isClosed_U hUD
  obtain ⟨Γ, hU, hV, hv, hvs, -, hsub⟩ := GM09.GraphDrawing.transportOn Y hUc hf.continuousOn
    (hi.mono hUD)
  have hvss : ∀ v (hv' : v ∈ V(N.G)), graphDrawingVertexSet Γ v = {f (ν v)} := fun v hv' => by
    rw [graphDrawingVertexSet_eq_singleton Γ hv', hv ⟨v, hv'⟩, hν ⟨v, hv'⟩]
  have hνD : ∀ v ∈ V(N.G), ν v ∈ D := fun v hv' => by
    have := Y.drawing.V_subset_U (Y.iso.vertexEquiv ⟨v, hv'⟩).2
    rw [hν ⟨v, hv'⟩] at this
    exact hUD this
  have hagree_of : ∀ {E : Set S} {Ω_E : CyclicPerm α} {φ_E : Circle ≃ₜ discBd E}
      {φ'_E : Circle ≃ₜ subBd (f '' E)},
      E ⊆ D → subBd (f '' E) = f '' discBd E → Ω_E.bar ⊆ V(N.G) →
      (∀ v ∈ Ω_E.bar, ν v ∈ discBd E) →
      (∀ v₁ v₂ v₃ : α, Ω_E.IsClockwise3 v₁ v₂ v₃ →
        ∃ t₁ t₂ t₃ : ℝ, t₁ < t₂ ∧ t₂ < t₃ ∧ t₃ < t₁ + 2 * Real.pi ∧
          (φ_E (Circle.exp t₁)).1 = ν v₁ ∧
          (φ_E (Circle.exp t₂)).1 = ν v₂ ∧
          (φ_E (Circle.exp t₃)).1 = ν v₃) →
      (∀ t : Circle, (φ'_E t).1 = f (φ_E t).1) →
      DrawingAgreesWithOArcHomeo Γ Ω_E (subBd (f '' E)) φ'_E := by
    intro E Ω_E φ_E φ'_E _ hb hΩ_sub hm_E hc_E hφ'_E
    refine ⟨fun v hv' => ?_, fun v₁ v₂ v₃ h₃ => ?_⟩
    · rw [hvss v (hΩ_sub hv'), singleton_subset_iff, hb]
      exact mem_image_of_mem f (hm_E v hv')
    · obtain ⟨t₁, t₂, t₃, h₁₂, h₂₃, h₃₁, e₁, e₂, e₃⟩ := hc_E v₁ v₂ v₃ h₃
      have hm₃ := (Ω_E.isClockwise3_iff.mp h₃).2.2.2
      refine ⟨t₁, t₂, t₃, h₁₂, h₂₃, h₃₁, ?_, ?_, ?_⟩
      · rw [hvss v₁ (hΩ_sub hm₃.1), hφ'_E, e₁]; rfl
      · rw [hvss v₂ (hΩ_sub hm₃.2.1), hφ'_E, e₂]; rfl
      · rw [hvss v₃ (hΩ_sub hm₃.2.2.1), hφ'_E, e₃]; rfl
  have hbetween : Γ.drawing.U ⊆ f '' D \ interior (f '' D₀) := by
    rw [hU]
    rintro _ ⟨x, hxQ, rfl⟩
    have hxD := (hY hxQ).1
    refine ⟨mem_image_of_mem f hxD, fun hxint => ?_⟩
    obtain ⟨y, hy, hyx⟩ := interior_subset hxint
    have hyx' : y = x := hi (hD₀D hy) hxD hyx
    have hxD₀ : x ∈ D₀ := hyx' ▸ hy
    have hxnotbd : x ∉ discBd D₀ := by
      intro hxb
      have hfb : f x ∈ subBd (f '' D₀) := hbd₀.symm ▸ mem_image_of_mem f hxb
      rw [subBd_eq_frontier] at hfb
      exact hfb.2 hxint
    exact (hY hxQ).2 ⟨hxD₀, hxnotbd⟩
  have hiff : ∀ (E : Set S), E ⊆ D → subBd (f '' E) = f '' discBd E → ∀ v ∈ V(N.G),
      graphDrawingVertexSet Γ v ⊆ subBd (f '' E) ↔ ν v ∈ discBd E := by
    intro E hED hbdE v hv'
    rw [hvss v hv', singleton_subset_iff, hbdE]
    constructor
    · rintro ⟨y, hy, heq⟩
      exact hi (hED (GraphMinor.GM11.discBd_subset E hy)) (hνD v hv') heq ▸ hy
    · exact mem_image_of_mem f
  have hφ_agree : DrawingAgreesWithOArcHomeo Γ N.Ω (subBd (f '' D)) φ' := by
    rw [hNΩ]
    exact hagree_of Subset.rfl hbd (hNΩ ▸ N.bar_subset) hm hc hφ'
  have hΩ₀_sub : Ω₀.bar ⊆ V(N.G) := by
    rw [← hΩ₀'_bar, ← hNΩ₀]
    exact N.bar₀_subset
  have hφ₀_agree_base : DrawingAgreesWithOArcHomeo Γ Ω₀ (subBd (f '' D₀)) φ₀' :=
    hagree_of hD₀D hbd₀ hΩ₀_sub hm₀ hc₀ hφ₀'
  have hinner : ∃ φ₀'' : Circle ≃ₜ subBd (f '' D₀),
      IsClockwiseDiscHomeo (f '' D₀) φ₀'' ∧
      DrawingAgreesWithOArcHomeo Γ N.Ω₀ (subBd (f '' D₀)) φ₀'' := by
    rw [hNΩ₀]
    by_cases hcw₀ : IsClockwiseDiscHomeo (f '' D₀) φ₀'
    · have hΩ₀'_eq : Ω₀' = Ω₀ := ite_eq_left hcw₀
      rw [hΩ₀'_eq]
      exact ⟨φ₀', hcw₀, hφ₀_agree_base⟩
    · have hΩ₀'_eq : Ω₀' = Ω₀⁻¹ := ite_eq_right hcw₀
      rw [hΩ₀'_eq]
      exact ⟨(Homeomorph.inv Circle).trans φ₀',
        (isClockwiseDiscHomeo_or_inv hΔ₀ rfl φ₀').resolve_left hcw₀,
        drawingAgreesWithOArcHomeo_inv hφ₀_agree_base⟩
  obtain ⟨φ₀'', hcw₀'', hφ₀''_agree⟩ := hinner
  refine ⟨⟨Γ, f '' D, f '' D₀, hΔ, image_mono hD₀D, hbetween,
    fun v hv' => (hiff D Subset.rfl hbd v hv').trans (hbar v hv'),
    fun v hv' => (hiff D₀ hD₀D hbd₀ v hv').trans (hbar₀ v hv'),
    ⟨φ', hcw_D, hφ_agree⟩, Or.inr ⟨hΔ₀, φ₀'', hcw₀'', hφ₀''_agree⟩⟩, f, hf, hi, rfl, rfl, hdisc,
      hsub⟩

omit [T2Space S] [CompactSpace S] [Nonempty S] in
/-- Nested circuits around the inner disc give a nest. -/
theorem hasBreadthGe_of_presentation {N : Neighborhood α β} (P : Presentation N)
    (Y : GraphDrawing N.G S) {D D₀ : Set S} {f : S → EuclideanPlane}
    (hΔ : P.Δ = f '' D) (hΔ₀ : P.Δ₀ = f '' D₀)
    (hdisc : ∀ E ⊆ D, IsClosedDisc E → IsClosedDisc (f '' E) ∧ subBd (f '' E) = f '' discBd E)
    (hpoints : ∀ J, graphDrawingSubgraphU P.Γ J = f '' graphDrawingSubgraphU Y J)
    {s : ℕ} (K : Fin s → Graph α β) (E : Fin s → Set S)
    (hK : ∀ i, IsGraphCircuit N.G (K i))
    (hDis : Pairwise (fun i j => Disjoint V(K i) V(K j)))
    (hE : ∀ i, IsClosedDisc (E i) ∧ discBd (E i) = graphDrawingSubgraphU Y (K i) ∧
      D₀ ⊆ E i ∧ E i ⊆ D)
    (hNest : ∀ i j, i ≤ j → E i ⊆ E j) : N.HasBreadthGe s := by
  refine ⟨P, K, hK, hDis, fun i => f '' E i, ?_, ?_, ?_⟩
  · intro i
    obtain ⟨hEi, hBd, _, hED⟩ := hE i
    obtain ⟨hFi, hFb⟩ := hdisc (E i) hED hEi
    exact ⟨hFi, by rw [hFb, hBd, hpoints]⟩
  · intro i
    rw [hΔ₀, hΔ]
    exact ⟨image_mono (hE i).2.2.1, image_mono (hE i).2.2.2⟩
  · intro i j hij
    exact image_mono (hNest i j hij)

end GraphMinor.GM14
