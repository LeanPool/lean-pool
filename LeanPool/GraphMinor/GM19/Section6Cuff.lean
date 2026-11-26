/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM19.Section6Tau
public import LeanPool.GraphMinor.GM19.FrameExists
public import LeanPool.GraphMinor.GM19.CuffPieces

/-!
# Graph Minors XIX, proof of (6.2): connected sets and edges on a cuff

In the proof of (6.2), page 343, the paper says that the paths `P₁, …, P_t` and the edges `σ'(e_i)`
go
around the circuit `C₂`, and that the direction of an edge on a cuff is kept. Here are the facts
about
`O`-arcs behind this. In `no_three_arcs`: a connected subset `A` of an `O`-arc is touched by at most
two
disjoint connected subsets outside `A`, if one of them has its ends on the `O`-arc. In
`precedes_of_dirAgrees`: an edge and a smaller edge in one side of a frame, directed along the side,
run
the same way around the cuff.
-/

@[expose] public section

namespace GraphMinor.GM19

open Set Topology GraphMinor.Surface GraphMinor.GM11

local notation "𝕀" => unitInterval

variable {X : Type} [TopologicalSpace X] [T2Space X]

/-! ### Intervals -/

theorem order_helper {I₀ I₁ I₂ : Set 𝕀} (h₀ : I₀.OrdConnected) (h₂ : I₂.OrdConnected) (h0 : 0 ∈ I₀)
    (h01 : Disjoint I₀ I₁) (h12 : Disjoint I₁ I₂) {p₁ p₂ x₂ : 𝕀} (hp₁ : p₁ ∈ I₁) (hp₂ : p₂ ∈ I₂)
    (hlt : p₁ < p₂) (hx₂ : x₂ ∈ I₀) (hcl : x₂ ∈ closure I₂) : False := by
  have hp₁₀ : p₁ ∉ I₀ := fun h => disjoint_left.mp h01 h hp₁
  have hx : x₂ < p₁ := by
    refine lt_of_not_ge fun hle => hp₁₀ (h₀.out h0 hx₂ ⟨?_, hle⟩)
    exact unitInterval.nonneg p₁
  obtain ⟨q, hq, hqI⟩ := mem_closure_iff.mp hcl (Iio p₁) isOpen_Iio hx
  exact disjoint_left.mp h12 hp₁ (h₂.out hqI hp₂ ⟨le_of_lt hq, le_of_lt hlt⟩)

/-- If `I₀` is an interval starting at `0`, there is no room for two disjoint intervals touching it.
-/
theorem order_three {I₀ I₁ I₂ : Set 𝕀} (h₀ : I₀.OrdConnected) (h₁ : I₁.OrdConnected)
    (h₂ : I₂.OrdConnected) (h0 : 0 ∈ I₀) (h01 : Disjoint I₀ I₁) (h02 : Disjoint I₀ I₂)
    (h12 : Disjoint I₁ I₂) (hn₁ : I₁.Nonempty) (hn₂ : I₂.Nonempty) {x₁ x₂ : 𝕀} (hx₁ : x₁ ∈ I₀)
    (hc₁ : x₁ ∈ closure I₁) (hx₂ : x₂ ∈ I₀) (hc₂ : x₂ ∈ closure I₂) : False := by
  obtain ⟨p₁, hp₁⟩ := hn₁
  obtain ⟨p₂, hp₂⟩ := hn₂
  rcases lt_trichotomy p₁ p₂ with h | h | h
  · exact order_helper h₀ h₂ h0 h01 h12 hp₁ hp₂ h hx₂ hc₂
  · exact disjoint_left.mp h12 hp₁ (h ▸ hp₂)
  · exact order_helper h₀ h₁ h0 h02 h12.symm hp₂ hp₁ h hx₁ hc₁

omit [T2Space X] in
theorem preimage_ordConnected {φ : 𝕀 → X} (hφ : IsEmbedding φ) {A : Set X} (hA : IsPreconnected A)
    (hAr : A ⊆ range φ) : (φ ⁻¹' A).OrdConnected := by
  have h : IsPreconnected (φ ⁻¹' A) := by
    rw [← hφ.isInducing.isPreconnected_image, image_preimage_eq_of_subset hAr]
    exact hA
  exact h.ordConnected

omit [T2Space X] in
theorem mem_closure_preimage {φ : 𝕀 → X} (hφ : IsEmbedding φ) {A : Set X}
  (hAr : A ⊆ range φ) {t : 𝕀}
    (ht : φ t ∈ closure A) : t ∈ closure (φ ⁻¹' A) := by
  rw [hφ.closure_eq_preimage_closure_image, image_preimage_eq_of_subset hAr]
  exact ht

omit [T2Space X] in
/-- A connected subset of a line with ends two points of the line is the part between them. -/
theorem eq_image_Ioo {φ : 𝕀 → X} (hφ : IsEmbedding φ) {e : Set X} (he : IsPreconnected e)
    (hr : e ⊆ range φ) {a b : 𝕀} (hab : a < b) (ht : tilde e = {φ a, φ b}) : e = φ '' Ioo a b := by
  have hI := preimage_ordConnected hφ he hr
  have ha : φ a ∈ tilde e := ht ▸ .inl rfl
  have hb : φ b ∈ tilde e := ht ▸ .inr rfl
  have hca := mem_closure_preimage hφ hr ha.1
  have hcb := mem_closure_preimage hφ hr hb.1
  have hmem : ∀ {x}, a < x → x < b → x ∈ φ ⁻¹' e := by
    intro x hax hxb
    obtain ⟨q, hq, hqI⟩ := mem_closure_iff.mp hca (Iio x) isOpen_Iio hax
    obtain ⟨q', hq', hqI'⟩ := mem_closure_iff.mp hcb (Ioi x) isOpen_Ioi hxb
    exact hI.out hqI hqI' ⟨le_of_lt hq, le_of_lt hq'⟩
  refine Subset.antisymm (fun y hy => ?_) (image_subset_iff.mpr fun x hx => hmem hx.1 hx.2)
  obtain ⟨t, rfl⟩ := hr hy
  refine ⟨t, ⟨?_, ?_⟩, rfl⟩
  · by_contra hn
    have hle : t ≤ a := not_lt.mp hn
    obtain ⟨q, hq, hqI⟩ := mem_closure_iff.mp hcb (Ioi a) isOpen_Ioi hab
    exact ha.2 (hI.out hy hqI ⟨hle, le_of_lt hq⟩)
  · by_contra hn
    have hle : b ≤ t := not_lt.mp hn
    obtain ⟨q, hq, hqI⟩ := mem_closure_iff.mp hca (Iio b) isOpen_Iio hab
    exact hb.2 (hI.out hqI hy ⟨le_of_lt hq, hle⟩)

/-! ### Cutting an `O`-arc along an edge -/

theorem isClosed_of_cuffLine {L : Set X} {a b : X} (h : IsLineWithEnds L a b) : IsClosed L := by
  obtain ⟨g, -, -⟩ := h
  have : CompactSpace L := g.compactSpace
  exact (isCompact_iff_compactSpace.mpr this).isClosed

omit [T2Space X] in
/-- The embedding of the unit interval given by a line. -/
theorem exists_line_emb {L : Set X} {a b : X} (h : IsLineWithEnds L a b) :
    ∃ φ : 𝕀 → X, IsEmbedding φ ∧ range φ = L ∧ φ 0 = a ∧ φ 1 = b := by
  obtain ⟨g, h0, h1⟩ := h
  refine ⟨fun t => (g t).1, IsEmbedding.subtypeVal.comp g.isEmbedding, ?_, h0, h1⟩
  ext x
  constructor
  · rintro ⟨t, rfl⟩
    exact (g t).2
  · intro hx
    exact ⟨g.symm ⟨x, hx⟩, by simp⟩

omit [T2Space X] in
/-- A connected set inside the closed line `L`, avoiding an interior point, stays on one side. -/
theorem line_filled {L f : Set X} {a b : X} (hL : IsLineWithEnds L a b) (hf : IsPreconnected f)
    (hfL : f ⊆ L) (ha : a ∈ closure f) (hb : b ∈ closure f) {x : X} (hx : x ∈ L) (hxa : x ≠ a)
    (hxb : x ≠ b) : x ∈ f := by
  obtain ⟨φ, hφ, hr, h0, h1⟩ := exists_line_emb hL
  subst h0 h1
  have hfr : f ⊆ range φ := hr ▸ hfL
  have hI := preimage_ordConnected hφ hf hfr
  have hca := mem_closure_preimage hφ hfr ha
  have hcb := mem_closure_preimage hφ hfr hb
  obtain ⟨t, rfl⟩ : x ∈ range φ := hr ▸ hx
  have ht0 : 0 < t := lt_of_le_of_ne (unitInterval.nonneg t) fun h => hxa (h ▸ rfl)
  have ht1 : t < 1 := lt_of_le_of_ne (unitInterval.le_one t) fun h => hxb (h ▸ rfl)
  obtain ⟨q, hq, hqI⟩ := mem_closure_iff.mp hca (Iio t) isOpen_Iio ht0
  obtain ⟨q', hq', hqI'⟩ := mem_closure_iff.mp hcb (Ioi t) isOpen_Ioi ht1
  exact hI.out hqI hqI' ⟨le_of_lt hq, le_of_lt hq'⟩

/-- An edge `f` of an `O`-arc `F`, with ends `a, b`, and the rest of `F`: there is a line `L` in `F`
with
ends `a, b`, disjoint from `f`, that holds every point of `F` outside `f`. -/
theorem exists_rest_line {F f : Set X} {a b : X} (hF : IsOArc F) (hab : a ≠ b)
    (hf : IsPreconnected f) (hfF : f ⊆ F) (hcl : closure f ⊆ F) (ht : tilde f = {a, b}) :
    ∃ L, IsLineWithEnds L a b ∧ F \ f ⊆ L ∧ L ⊆ F ∧ Disjoint L f := by
  have ha : a ∈ tilde f := ht ▸ .inl rfl
  have hb : b ∈ tilde f := ht ▸ .inr rfl
  obtain ⟨A₁, A₂, h₁, h₂, hU, hI⟩ := hF.lines (hcl ha.1) (hcl hb.1) hab
  have hnot : ∀ {x}, x ∈ f → x ∉ ({a, b} : Set X) := fun {x} hxf hx => by
    rw [← ht] at hx
    exact hx.2 hxf
  have hmain : ∀ {A₁ A₂ : Set X}, IsLineWithEnds A₁ a b → IsLineWithEnds A₂ a b → F = A₁ ∪ A₂ →
      A₁ ∩ A₂ = {a, b} → f ⊆ A₁ → F \ f ⊆ A₂ ∧ A₂ ⊆ F ∧ Disjoint A₂ f := by
    intro A₁ A₂ h₁ h₂ hU hI hsub
    refine ⟨fun x hx => ?_, hU ▸ subset_union_right, disjoint_left.mpr fun x hx hxf =>
      hnot hxf (hI ▸ ⟨hsub hxf, hx⟩)⟩
    rcases (hU ▸ hx.1 : x ∈ A₁ ∪ A₂) with h | h
    · by_cases hxa : x = a
      · obtain ⟨g, h0, -⟩ := h₂
        exact hxa ▸ h0 ▸ (g 0).2
      by_cases hxb : x = b
      · obtain ⟨g, -, h0⟩ := h₂
        exact hxb ▸ h0 ▸ (g 1).2
      exact absurd (line_filled h₁ hf hsub ha.1 hb.1 h hxa hxb) hx.2
    · exact h
  have hsub : f ⊆ A₁ ∪ A₂ := hU ▸ hfF
  have hcase := (isPreconnected_closed_iff.mp hf) A₁ A₂ (isClosed_of_cuffLine h₁)
    (isClosed_of_cuffLine h₂) hsub
  by_cases hA : (f ∩ A₁).Nonempty
  · by_cases hB : (f ∩ A₂).Nonempty
    · obtain ⟨x, hxf, hx⟩ := hcase hA hB
      exact absurd (hI ▸ hx) (hnot hxf)
    · refine ⟨A₂, h₂, hmain h₁ h₂ hU.symm hI fun x hx => ?_⟩
      rcases hsub hx with h | h
      · exact h
      · exact absurd ⟨x, hx, h⟩ hB
  · refine ⟨A₁, h₁, hmain h₂ h₁ (by rw [← hU, union_comm]) (by rw [inter_comm, hI]) fun x hx => ?_⟩
    rcases hsub hx with h | h
    · exact absurd ⟨x, hx, h⟩ hA
    · exact h

/-- The closure of an open arc of an `O`-arc is not all of it. -/
theorem exists_notMem_closure {F f : Set X} {a b : X} (hF : IsOArc F) (hab : a ≠ b)
    (hf : IsPreconnected f) (hfF : f ⊆ F) (hcl : closure f ⊆ F) (ht : tilde f = {a, b}) :
    ∃ p ∈ F, p ∉ closure f := by
  obtain ⟨L, hL, -, hLF, hd⟩ := exists_rest_line hF hab hf hfF hcl ht
  obtain ⟨φ, hφ, hr, h0, h1⟩ := exists_line_emb hL
  let m : 𝕀 := ⟨1 / 2, by norm_num, by norm_num⟩
  have hm : φ m ∈ L := hr ▸ mem_range_self m
  refine ⟨φ m, hLF hm, fun hc => ?_⟩
  have htl : φ m ∉ tilde f := by
    rw [ht]
    rintro (h | h)
    · have := hφ.injective (h.trans h0.symm)
      have h' := congrArg Subtype.val this
      norm_num [m] at h'
    · have := hφ.injective (h.trans h1.symm)
      have h' := congrArg Subtype.val this
      norm_num [m] at h'
  exact disjoint_left.mp hd hm (by_contra fun h => htl ⟨hc, h⟩)

theorem no_three_arcs_aux {F A f₁ f₂ f₃ : Set X} {a b : X} (hF : IsOArc F) (hab : a ≠ b)
    (hA : IsPreconnected A) (hAF : A ⊆ F) (h₁ : IsPreconnected f₁) (h₂ : IsPreconnected f₂)
    (h₃ : IsPreconnected f₃) (hn₁ : f₁.Nonempty) (hn₂ : f₂.Nonempty)
    (hF₁ : f₁ ⊆ F) (hF₂ : f₂ ⊆ F) (hF₃ : f₃ ⊆ F) (hcl₃ : closure f₃ ⊆ F)
    (hd₁ : Disjoint A f₁) (hd₂ : Disjoint A f₂) (hd₃ : Disjoint A f₃)
    (h12 : Disjoint f₁ f₂) (h13 : Disjoint f₁ f₃) (h23 : Disjoint f₂ f₃)
    (hc₁ : (closure f₁ ∩ A).Nonempty) (hc₂ : (closure f₂ ∩ A).Nonempty)
    (ht : tilde f₃ = {a, b}) (haA : a ∈ A) : False := by
  obtain ⟨L, hL, hrest, -, -⟩ := exists_rest_line hF hab h₃ hF₃ hcl₃ ht
  obtain ⟨φ, hφ, hr, h0, -⟩ := exists_line_emb hL
  have hsub : ∀ {B : Set X}, B ⊆ F → Disjoint B f₃ → B ⊆ range φ := fun hB hd x hx =>
    hr ▸ hrest ⟨hB hx, disjoint_left.mp hd hx⟩
  have hA' := hsub hAF hd₃
  have h₁' := hsub hF₁ h13
  have h₂' := hsub hF₂ h23
  have himg : ∀ {B C : Set X}, Disjoint B C → Disjoint (φ ⁻¹' B) (φ ⁻¹' C) := fun h => h.preimage φ
  have hne : ∀ {B : Set X}, B.Nonempty → B ⊆ range φ → (φ ⁻¹' B).Nonempty := by
    rintro B ⟨x, hx⟩ h
    obtain ⟨t, rfl⟩ := h hx
    exact ⟨t, hx⟩
  obtain ⟨x₁, hx₁, hxA₁⟩ := hc₁
  obtain ⟨x₂, hx₂, hxA₂⟩ := hc₂
  obtain ⟨s₁, rfl⟩ := hA' hxA₁
  obtain ⟨s₂, rfl⟩ := hA' hxA₂
  exact order_three (preimage_ordConnected hφ hA hA') (preimage_ordConnected hφ h₁ h₁')
    (preimage_ordConnected hφ h₂ h₂') (by change φ 0 ∈ A; rw [h0]; exact haA) (himg hd₁) (himg hd₂)
    (himg h12) (hne hn₁ h₁') (hne hn₂ h₂') hxA₁ (mem_closure_preimage hφ h₁' hx₁) hxA₂
    (mem_closure_preimage hφ h₂' hx₂)

/-- **At most two connected sets touch a connected subset of an `O`-arc.** Let `A` be a connected
subset of the `O`-arc `F`, and let `f₁, f₂, f₃` be connected, pairwise disjoint, and disjoint from
`A`,
inside `F`. Let `f₃` be an open arc of `F` with ends `a, b`, one of them in `A`. Then `f₁` and `f₂`
do not
both touch `A`. -/
theorem no_three_arcs {F A f₁ f₂ f₃ : Set X} {a b : X} (hF : IsOArc F) (hab : a ≠ b)
    (hA : IsPreconnected A) (hAF : A ⊆ F) (h₁ : IsPreconnected f₁) (h₂ : IsPreconnected f₂)
    (h₃ : IsPreconnected f₃) (hn₁ : f₁.Nonempty) (hn₂ : f₂.Nonempty)
    (hF₁ : f₁ ⊆ F) (hF₂ : f₂ ⊆ F) (hF₃ : f₃ ⊆ F) (hcl₃ : closure f₃ ⊆ F)
    (hd₁ : Disjoint A f₁) (hd₂ : Disjoint A f₂) (hd₃ : Disjoint A f₃)
    (h12 : Disjoint f₁ f₂) (h13 : Disjoint f₁ f₃) (h23 : Disjoint f₂ f₃)
    (hc₁ : (closure f₁ ∩ A).Nonempty) (hc₂ : (closure f₂ ∩ A).Nonempty)
    (ht : tilde f₃ = {a, b}) (hend : a ∈ A ∨ b ∈ A) : False := by
  rcases hend with h | h
  · exact no_three_arcs_aux hF hab hA hAF h₁ h₂ h₃ hn₁ hn₂ hF₁ hF₂ hF₃ hcl₃ hd₁ hd₂ hd₃ h12 h13 h23
      hc₁ hc₂ ht h
  · exact no_three_arcs_aux hF hab.symm hA hAF h₁ h₂ h₃ hn₁ hn₂ hF₁ hF₂ hF₃ hcl₃ hd₁ hd₂ hd₃ h12 h13
      h23 hc₁ hc₂ (by rw [ht, pair_comm]) h

/-! ### Angles on a cuff -/

section Angle

variable {Θ : Set X} (f : Circle ≃ₜ Θ)

omit [T2Space X] in
/-- A map into `Θ` that misses the point of angle `α` has a continuous angle in `(α, α + 2π)`. -/
theorem exists_cuff_angle {Y : Type} [TopologicalSpace Y] {g : Y → X} (hg : Continuous g)
  (hgΘ : ∀ y, g y ∈ Θ)
    {α : ℝ} (hp : ∀ y, g y ≠ cuffPoint f α) :
    ∃ θ : Y → ℝ, Continuous θ ∧ (∀ y, θ y ∈ Ioo α (α + 2 * Real.pi)) ∧ ∀ y, cuffPoint f (θ y) = g y
      := by
  let c : Y → Circle := fun y => f.symm ⟨g y, hgΘ y⟩
  have hc : Continuous c := f.symm.continuous.comp (hg.subtype_mk hgΘ)
  have hf : ∀ y, ((f (c y)).1 : X) = g y := fun y => by simp [c]
  let u : Y → Circle := fun y => c y * Circle.exp (-(α + Real.pi))
  have hu : Continuous u := hc.mul continuous_const
  have hcu : ∀ y, Circle.exp (α + Real.pi) * u y = c y := fun y => by
    simp only [u, Circle.exp_neg]
    rw [mul_comm, mul_assoc, inv_mul_cancel, mul_one]
  have harg : ∀ y, Complex.arg (u y) ≠ Real.pi := by
    intro y h
    have h1 : Circle.exp (Complex.arg (u y)) = u y := Circle.exp_arg _
    rw [h] at h1
    have h2 : c y = Circle.exp α := by
      rw [← hcu y, ← h1, ← Circle.exp_add]
      exact Circle.exp_eq_exp.mpr ⟨1, by push_cast; ring⟩
    exact hp y (by rw [← hf y, h2]; rfl)
  refine ⟨fun y => α + Real.pi + Complex.arg (u y), ?_, fun y => ⟨?_, ?_⟩, fun y => ?_⟩
  · refine continuous_const.add (continuous_iff_continuousAt.mpr fun y => ?_)
    have hs : (u y : ℂ) ∈ Complex.slitPlane :=
      Complex.mem_slitPlane_iff_arg.mpr ⟨harg y, Circle.coe_ne_zero _⟩
    exact ContinuousAt.comp (g := Complex.arg) (f := fun y => ((u y : Circle) : ℂ))
      (Complex.continuousAt_arg hs)
      (continuous_subtype_val.comp hu).continuousAt
  · linarith [Complex.neg_pi_lt_arg (u y : ℂ)]
  · linarith [lt_of_le_of_ne (Complex.arg_le_pi (u y : ℂ)) (harg y)]
  · change (f (Circle.exp _)).1 = g y
    rw [Circle.exp_add, Circle.exp_arg, hcu y]
    exact hf y

omit [T2Space X] in
theorem angle_inj {α s t : ℝ} (hs : s ∈ Ioo α (α + 2 * Real.pi)) (ht : t ∈ Ioo α (α + 2 * Real.pi))
    (h : cuffPoint f s = cuffPoint f t) : s = t :=
  cuffPoint_injOn f le_rfl ⟨hs.1.le, hs.2⟩ ⟨ht.1.le, ht.2⟩ h

omit [T2Space X] in
/-- Between two points of the line, the angle fills the interval. -/
theorem image_Ioo_angle {θ : 𝕀 → ℝ} (hc : Continuous θ) (hm : StrictMono θ) {g : 𝕀 → X}
    (hg : ∀ t, cuffPoint f (θ t) = g t) {a b : 𝕀} (hab : a ≤ b) :
    g '' Ioo a b = cuffPoint f '' Ioo (θ a) (θ b) := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨θ x, ⟨hm hx.1, hm hx.2⟩, hg x⟩
  · rintro ⟨w, hw, rfl⟩
    have hconn : IsPreconnected (Icc a b) := ordConnected_Icc.isPreconnected
    obtain ⟨x, hx, rfl⟩ := hconn.intermediate_value (left_mem_Icc.mpr hab) (right_mem_Icc.mpr hab)
      hc.continuousOn ⟨hw.1.le, hw.2.le⟩
    have h1 : a ≠ x := fun h => hw.1.ne (by rw [h])
    have h2 : x ≠ b := fun h => hw.2.ne (by rw [h])
    exact ⟨x, ⟨lt_of_le_of_ne hx.1 h1, lt_of_le_of_ne hx.2 h2⟩, (hg x).symm⟩

omit [T2Space X] in
/-- **Directions along a side agree around the cuff.** Let `s` be a set with closure in the cuff
`Θ`,
missing the point `p` of `Θ`. If `e, e'` lie in `s` and are directed along `s` by `DirAgrees`, and
the
tail of `e` immediately precedes `e` in an orientation of `Θ`, then the tail of `e'` immediately
precedes
`e'` in the same orientation. -/
theorem precedes_of_dirAgrees {s e e' : Set X} {γs γe γe' : List X} (hs : closure s ⊆ Θ) {p : X}
    (hpΘ : p ∈ Θ) (hp : p ∉ closure s) (hd : DirAgrees s γs e γe) (hd' : DirAgrees s γs e' γe')
    (he : IsPreconnected e) (he' : IsPreconnected e')
    (ht : ∀ a b, γe.head? = some a → γe.getLast? = some b → tilde e = {a, b})
    (ht' : ∀ a b, γe'.head? = some a → γe'.getLast? = some b → tilde e' = {a, b})
    {n n' : X} (hn : γe.head? = some n) (hn' : γe'.head? = some n')
    (hpre : ImmediatelyPrecedes f n e) : ImmediatelyPrecedes f n' e' := by
  obtain ⟨g, t₁, t₂, ht12, hes, h0, h1, ha, hb⟩ := hd
  obtain ⟨g', t₃, t₄, ht34, hes', h0', h1', ha', hb'⟩ := hd'
  have hpi := Real.pi_pos
  obtain ⟨α, hα⟩ : ∃ α, cuffPoint f α = p := by
    refine ⟨Complex.arg (f.symm ⟨p, hpΘ⟩), ?_⟩
    change (f (Circle.exp _)).1 = p
    rw [Circle.exp_arg]
    simp
  let φ : 𝕀 → X := fun t => (g t).1
  let φ' : 𝕀 → X := fun t => (g' t).1
  have hφ : IsEmbedding φ := IsEmbedding.subtypeVal.comp g.isEmbedding
  have hφ' : IsEmbedding φ' := IsEmbedding.subtypeVal.comp g'.isEmbedding
  have hrange : ∀ {g₀ : 𝕀 ≃ₜ closure s}, s ⊆ range fun t => (g₀ t).1 := by
    intro g₀ x hx
    exact ⟨g₀.symm ⟨x, subset_closure hx⟩, by simp⟩
  obtain ⟨θ, hθc, hθr, hθ⟩ := exists_cuff_angle f hφ.continuous (fun t => hs (g t).2) (α := α)
    fun t h => hp (by rw [← hα, ← h]; exact (g t).2)
  obtain ⟨θ', hθc', hθr', hθ'⟩ := exists_cuff_angle f hφ'.continuous (fun t => hs (g' t).2) (α := α)
    fun t h => hp (by rw [← hα, ← h]; exact (g' t).2)
  have hinj : Function.Injective θ := fun x y h => hφ.injective (by rw [← hθ, ← hθ, h])
  have hinj' : Function.Injective θ' := fun x y h => hφ'.injective (by rw [← hθ', ← hθ', h])
  have he0 : θ 0 = θ' 0 := by
    refine angle_inj f (hθr _) (hθr' _) ?_
    rw [hθ, hθ']
    exact Option.some.inj (h0.symm.trans h0')
  have he1 : θ 1 = θ' 1 := by
    refine angle_inj f (hθr _) (hθr' _) ?_
    rw [hθ, hθ']
    exact Option.some.inj (h1.symm.trans h1')
  have h01 : (0 : 𝕀) < 1 := by
    change ((0 : ℝ)) < 1
    exact one_pos
  have hn₀ : n = φ t₁ := Option.some.inj (hn.symm.trans ha)
  have hn₀' : n' = φ' t₃ := Option.some.inj (hn'.symm.trans ha')
  have heq : e = φ '' Ioo t₁ t₂ := eq_image_Ioo hφ he (hes.trans hrange) ht12 (ht _ _ ha hb)
  have heq' : e' = φ' '' Ioo t₃ t₄ := eq_image_Ioo hφ' he' (hes'.trans hrange) ht34
    (ht' _ _ ha' hb')
  have hup : StrictMono θ := by
    refine (Continuous.strictMono_of_inj hθc hinj).resolve_right fun hanti => ?_
    obtain ⟨t₀, t₁', hlt, -, hc, heq₀⟩ := hpre
    have hc' : cuffPoint f t₀ = cuffPoint f (θ t₁) := by rw [hc, hθ, hn₀]
    obtain ⟨m, hm⟩ := cuffPoint_eq f hc'
    have hy := hθr t₁
    set ε := min (t₁' - t₀) (α + 2 * Real.pi - θ t₁) / 2 with hε
    have hm₁ : min (t₁' - t₀) (α + 2 * Real.pi - θ t₁) ≤ t₁' - t₀ := min_le_left _ _
    have hm₂ : min (t₁' - t₀) (α + 2 * Real.pi - θ t₁) ≤ α + 2 * Real.pi - θ t₁ := min_le_right _ _
    have hm₃ : 0 < min (t₁' - t₀) (α + 2 * Real.pi - θ t₁) :=
      lt_min (by linarith) (by linarith [hy.2])
    have hz : cuffPoint f (t₀ + ε) ∈ e := by
      rw [heq₀]
      exact ⟨_, ⟨by linarith, by linarith⟩, rfl⟩
    rw [heq] at hz
    obtain ⟨x, hx, hxe⟩ := hz
    have hshift : t₀ + ε = (θ t₁ + ε) + m * (2 * Real.pi) := by rw [hm]; ring
    have hzz : cuffPoint f (θ x) = cuffPoint f (θ t₁ + ε) := by
      rw [hθ, hxe, hshift, cuffPoint_shift]
    have hle : θ x < θ t₁ := hanti hx.1
    have := angle_inj f (hθr x) ⟨by linarith [hy.1], by linarith⟩ hzz
    linarith
  have hup' : StrictMono θ' := by
    refine (Continuous.strictMono_of_inj hθc' hinj').resolve_right fun hanti => ?_
    have h₁ := hup h01
    have h₂ := hanti h01
    rw [he0, he1] at h₁
    exact lt_asymm h₁ h₂
  refine ⟨θ' t₃, θ' t₄, hup' ht34, ?_, ?_, ?_⟩
  · linarith [(hθr' t₃).1, (hθr' t₄).2]
  · rw [hθ', hn₀']
  · rw [heq']
    exact image_Ioo_angle f hθc' hup' hθ' ht34.le

end Angle

end GraphMinor.GM19
