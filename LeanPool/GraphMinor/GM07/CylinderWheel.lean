/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM07.DiscPlace
public import LeanPool.GraphMinor.GM07.Slit
public import LeanPool.GraphMinor.GM11.OArcCircuit
public import LeanPool.GraphMinor.GM11.RadialChord
public import LeanPool.GraphMinor.GM11.RadialBasics

/-!
# Wheels in the caps

The uncrossing of Graph Minors III, (4.1), needs an inner and an outer circuit that the nest does
not touch, while (5.8) has only the cuffs, which the nest may touch. So inside each
cap we draw a smaller circle, with one spoke from each vertex on the cuff to the circle
(`exists_wheel`). This changes nothing in the cylinder.
-/

@[expose] public section

namespace GraphMinor.GM07

open Set Topology Function Metric GraphMinor.Surface GraphMinor.GM11

local notation "I" => unitInterval

variable {T : Type*} [TopologicalSpace T] [T2Space T]

/-- A smaller circle in a disc, with disjoint spokes from given points of the boundary. -/
theorem exists_wheel {D : Set T} (hD : IsClosedDisc D) {A : Set T} (hAD : A ⊆ discBd D) :
    ∃ (E : Set T) (q : T → T) (ℓ : T → Set T), IsClosedDisc E ∧ E ⊆ discInt D ∧
      (∀ x ∈ A, q x ∈ discBd E ∧ IsLineWithEnds (ℓ x) x (q x) ∧ x ≠ q x ∧ ℓ x ⊆ D ∧ ℓ x ∩ discBd D
        = {x} ∧ ℓ x ∩ E = {q x}) ∧
      ∀ x ∈ A, ∀ y ∈ A, x ≠ y → Disjoint (ℓ x) (ℓ y) := by
  obtain ⟨h, g, c⟩ := hD.exists_isChart
  have hunit : ∀ x ∈ A, ‖h x‖ = 1 := fun x hx => by
    have : h x ∈ h '' discBd D := ⟨x, hAD hx, rfl⟩
    rw [c.bd] at this
    simpa using this
  have hxD : ∀ x ∈ A, x ∈ D := fun x hx => Surface.discBd_subset _ (hAD hx)
  have hgh : ∀ x ∈ A, g (h x) = x := fun x hx => c.gh (hxD x hx)
  let ray : T → I → ℂ := fun x t => ((1 - (t : ℝ) / 2 : ℝ) : ℂ) * h x
  have hnorm : ∀ x ∈ A, ∀ t : I, ‖ray x t‖ = 1 - (t : ℝ) / 2 := fun x hx t => by
    have h1 : (0 : ℝ) ≤ 1 - (t : ℝ) / 2 := by linarith [t.2.2]
    simp only [ray, norm_mul, hunit x hx, mul_one, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg h1]
  have hball : ∀ x ∈ A, ∀ t, ray x t ∈ closedBall (0 : ℂ) 1 := fun x hx t => by
    simp only [mem_closedBall, dist_zero_right, hnorm x hx]
    linarith [t.2.1]
  have hcont : ∀ x, Continuous (ray x) := fun x => by
    simp only [ray]
    fun_prop
  have hinj : ∀ x ∈ A, ∀ y ∈ A, ∀ t t', g (ray x t) = g (ray y t') → x = y ∧ t = t'
    := fun x hx y hy t t' he => by
    have h1 := c.injOn (hball x hx t) (hball y hy t') he
    have h2 := congrArg norm h1
    rw [hnorm x hx, hnorm y hy] at h2
    have htt : t = t' := Subtype.ext (by linarith)
    subst htt
    have h3 : ((1 - (t : ℝ) / 2 : ℝ) : ℂ) ≠ 0 := by
      have : (1 - (t : ℝ) / 2 : ℝ) ≠ 0 := by linarith [t.2.2]
      exact_mod_cast this
    have h4 : h x = h y := mul_left_cancel₀ h3 h1
    refine ⟨?_, rfl⟩
    rw [← hgh x hx, ← hgh y hy, h4]
  let arc : T → I → T := fun x t => g (ray x t)
  have harc : ∀ x ∈ A, IsArcMap (arc x) := fun x hx =>
    ⟨c.gc.comp_continuous (hcont x) (hball x hx), fun t t' he => (hinj x hx x hx t t' he).2⟩
  have harc0 : ∀ x ∈ A, arc x 0 = x := fun x hx => by
    simp only [arc, ray, Set.Icc.coe_zero, zero_div, sub_zero, Complex.ofReal_one, one_mul]
    exact hgh x hx
  have hs : closedBall (0 : ℂ) (1 / 2) ⊆ closedBall 0 1 := closedBall_subset_closedBall
    (by norm_num)
  obtain ⟨hb1, hb2⟩ := closedBall_disc (s := 1 / 2) (by norm_num)
  obtain ⟨hE, hbE⟩ := c.disc_g hs hb1
  rw [hb2] at hbE
  refine ⟨g '' closedBall 0 (1 / 2), fun x => arc x 1, fun x => range (arc x), hE, ?_,
    fun x hx => ⟨?_, ?_, ?_, ?_, ?_, ?_⟩, fun x hx y hy hne => ?_⟩
  · rw [c.discInt_eq]
    exact image_mono fun z hz => by
      simp only [mem_closedBall, dist_zero_right, mem_ball] at hz ⊢
      linarith
  · rw [hbE]
    refine ⟨ray x 1, ?_, rfl⟩
    simp only [mem_sphere, dist_zero_right, hnorm x hx, Set.Icc.coe_one]
    norm_num
  · have := isLineWithEnds_range_of_arc (harc x hx)
    rwa [harc0 x hx] at this
  · intro he
    exact zero_ne_one ((harc x hx).2 ((harc0 x hx).trans he))
  · rintro _ ⟨t, rfl⟩
    exact c.gm (hball x hx t)
  · ext z
    constructor
    · rintro ⟨⟨t, rfl⟩, hz⟩
      rw [← c.g_sphere] at hz
      obtain ⟨w, hw, he⟩ := hz
      have h1 : w = ray x t := c.injOn (sphere_subset_closedBall hw) (hball x hx t) he
      have h2 : ‖ray x t‖ = 1 := by
        rw [← h1]
        simpa using hw
      rw [hnorm x hx] at h2
      have h3 : t = 0 := Subtype.ext (by
        have : (t : ℝ) = 0 := by linarith
        simpa using this)
      rw [h3, mem_singleton_iff, harc0 x hx]
    · rintro rfl
      exact ⟨⟨0, harc0 _ hx⟩, hAD hx⟩
  · ext z
    constructor
    · rintro ⟨⟨t, rfl⟩, w, hw, he⟩
      have h1 : w = ray x t := c.injOn (hs hw) (hball x hx t) he
      have h2 : ‖ray x t‖ ≤ 1 / 2 := by
        rw [← h1]
        simpa using hw
      rw [hnorm x hx] at h2
      have h3 : t = 1 := Subtype.ext (by
        have : (1 : ℝ) ≤ (t : ℝ) := by linarith
        have h4 : (t : ℝ) ≤ 1 := t.2.2
        simpa using le_antisymm h4 this)
      rw [h3]
      rfl
    · rintro rfl
      refine ⟨⟨1, rfl⟩, ray x 1, ?_, rfl⟩
      simp only [mem_closedBall, dist_zero_right, hnorm x hx, Set.Icc.coe_one]
      norm_num
  · refine disjoint_left.mpr ?_
    rintro _ ⟨t, rfl⟩ ⟨t', he⟩
    exact hne (hinj y hy x hx t' t he).1.symm

/-- Add disjoint lines between vertices to a drawing. -/
theorem exists_add_lines (Γ : Drawing T) (s : Finset T) (ℓ : T → Set T) (a b : T → T)
    (hl : ∀ x ∈ s, IsLineWithEnds (ℓ x) (a x) (b x) ∧ a x ≠ b x ∧ a x ∈ Γ.V ∧ b x ∈ Γ.V
      ∧ ℓ x ∩ Γ.U ⊆ {a x, b x})
    (hd : ∀ x ∈ s, ∀ y ∈ s, x ≠ y → Disjoint (ℓ x) (ℓ y)) :
    ∃ H : Drawing T, H.U = Γ.U ∪ ⋃ x ∈ s, ℓ x ∧ H.V = Γ.V ∧ H.E = Γ.E ∪ (fun x
      => ℓ x \ {a x, b x}) '' s := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨Γ, by simp, rfl, by simp⟩
  | insert x s hx ih =>
    obtain ⟨H, h1, h2, h3⟩ := ih (fun y hy => hl y (Finset.mem_insert_of_mem hy))
      (fun y hy z hz => hd y (Finset.mem_insert_of_mem hy) z (Finset.mem_insert_of_mem hz))
    obtain ⟨hL, hne, ha, hb, hcap⟩ := hl x (Finset.mem_insert_self x s)
    have hsub : H.U ∩ (lineDrawing hL hne).U ⊆ H.V ∩ (lineDrawing hL hne).V := by
      rintro z ⟨hz, hzL⟩
      change z ∈ ℓ x at hzL
      rw [h1] at hz
      rcases hz with hz | hz
      · have h4 := hcap ⟨hzL, hz⟩
        refine ⟨?_, h4⟩
        rw [h2]
        rcases h4 with rfl | rfl
        · exact ha
        · exact hb
      · obtain ⟨y, hy, hzy⟩ := mem_iUnion₂.mp hz
        have hxy : x ≠ y := fun h => hx (h ▸ hy)
        exact absurd hzy (disjoint_left.mp (hd x (Finset.mem_insert_self x s) y
          (Finset.mem_insert_of_mem hy) hxy) hzL)
    refine ⟨H.glue (lineDrawing hL hne) hsub, ?_, ?_, ?_⟩
    · change H.U ∪ ℓ x = _
      rw [h1, Finset.set_biUnion_insert, union_assoc, union_comm (⋃ y ∈ s, ℓ y)]
    · change H.V ∪ {a x, b x} = _
      rw [h2]
      exact union_eq_left.mpr (insert_subset ha (singleton_subset_iff.mpr hb))
    · rw [Drawing.glue_E, lineDrawing_E, h3, Finset.coe_insert, image_insert_eq, union_assoc,
        union_singleton]

/-- A drawing with an `O`-arc as point set and at least one vertex is a circuit. -/
theorem isCircuit_of_isOArc_U [ConnectedSpace T] {C : Drawing T} (hC : IsOArc C.U) : C.IsCircuit
  := by
  obtain ⟨C', h1, h2, h3⟩ := exists_circuit_of_oArc hC (Subset.refl C.U)
  have hV : C'.V = C.V := by
    refine subset_antisymm h2.1 fun x hx => ?_
    by_contra hn
    obtain ⟨e, he, hxe⟩ := C'.exists_edge_of_mem (h3.symm ▸ C.V_subset_U hx) hn
    exact (h2.2 he).2.1 hxe |>.2 hx
  have : C' = C := by
    cases C
    cases C'
    simp only at h3 hV
    subst h3 hV
    rfl
  exact this ▸ h1

/-- `H` is `Γ` with a wheel added in each of the discs `D₁` and `D₂`. The circle `Cᵢ` bounds the
disc `Eᵢ`, and `ℓ x` is the spoke from a vertex `x` of `Γ` on `Dᵢ` to `q x` on the circle. -/
structure IsWheeled (Γ H C₁ C₂ : Drawing T) (D₁ D₂ E₁ E₂ : Set T) (q : T → T) (ℓ : T
  → Set T) : Prop where
  sub : Γ.IsSubdrawing H
  sub₁ : C₁.IsSubdrawing H
  sub₂ : C₂.IsSubdrawing H
  circ₁ : C₁.IsCircuit
  circ₂ : C₂.IsCircuit
  disc₁ : IsClosedDisc E₁
  disc₂ : IsClosedDisc E₂
  in₁ : E₁ ⊆ discInt D₁
  in₂ : E₂ ⊆ discInt D₂
  bd₁ : discBd E₁ = C₁.U
  bd₂ : discBd E₂ = C₂.U
  V : H.V = Γ.V ∪ C₁.V ∪ C₂.V
  U : H.U = Γ.U ∪ C₁.U ∪ C₂.U ∪ ⋃ x ∈ Γ.V ∩ (D₁ ∪ D₂), ℓ x
  E : ∀ e ∈ H.E, e ∈ Γ.E ∨ e ∈ C₁.E ∨ e ∈ C₂.E ∨ ∃ x ∈ Γ.V ∩ (D₁ ∪ D₂), e = ℓ x \ {x, q x}
  q₁ : ∀ x ∈ Γ.V ∩ D₁, q x ∈ C₁.V
  q₂ : ∀ x ∈ Γ.V ∩ D₂, q x ∈ C₂.V
  line : ∀ x ∈ Γ.V ∩ (D₁ ∪ D₂), IsLineWithEnds (ℓ x) x (q x) ∧ x ≠ q x ∧ ℓ x \ {x, q x} ∈ H.E
  cap₁ : ∀ x ∈ Γ.V ∩ D₁, ℓ x ⊆ D₁ ∧ ℓ x ∩ discBd D₁ = {x} ∧ ℓ x ∩ E₁ = {q x}
  cap₂ : ∀ x ∈ Γ.V ∩ D₂, ℓ x ⊆ D₂ ∧ ℓ x ∩ discBd D₂ = {x} ∧ ℓ x ∩ E₂ = {q x}
  disj : ∀ x ∈ Γ.V ∩ (D₁ ∪ D₂), ∀ y ∈ Γ.V ∩ (D₁ ∪ D₂), x ≠ y → Disjoint (ℓ x) (ℓ y)

/-- Wheels exist. -/
theorem exists_wheeled [ConnectedSpace T] (Γ : Drawing T) {D₁ D₂ : Set T} (h₁ : IsClosedDisc D₁)
  (h₂ : IsClosedDisc D₂) (hd : Disjoint D₁ D₂)
    (hi₁ : Disjoint Γ.U (discInt D₁)) (hi₂ : Disjoint Γ.U (discInt D₂)) :
    ∃ (H C₁ C₂ : Drawing T) (E₁ E₂ : Set T) (q : T → T) (ℓ : T → Set T), IsWheeled Γ H C₁ C₂ D₁ D₂
      E₁ E₂ q ℓ := by
  classical
  have hbdA : ∀ {D : Set T}, Disjoint Γ.U (discInt D) → Γ.V ∩ D ⊆ discBd D := fun {D} hi x hx => by
    by_contra hn
    exact disjoint_left.mp hi (Γ.V_subset_U hx.1) ⟨hx.2, hn⟩
  obtain ⟨E₁, q₁, ℓ₁, hE₁, hE₁D, hw₁, hd₁⟩ := exists_wheel h₁ (hbdA hi₁)
  obtain ⟨E₂, q₂, ℓ₂, hE₂, hE₂D, hw₂, hd₂⟩ := exists_wheel h₂ (hbdA hi₂)
  have hcircle : ∀ {E : Set T} {q : T → T} {A : Set T}, IsClosedDisc E → A.Finite →
    (∀ x ∈ A, q x ∈ discBd E) → ∃ C : Drawing T, C.U = discBd E ∧ q '' A ⊆ C.V
      := fun {E q A} hE hA hq => by
    obtain ⟨z, hz⟩ := isOArc_nonempty hE.isOArc_discBd
    obtain ⟨C, c1, c2⟩ := exists_drawing_on_oArc hE.isOArc_discBd ((hA.image q).union
      (finite_singleton z)) ⟨z, .inr rfl⟩
      (union_subset (by rintro _ ⟨x, hx, rfl⟩; exact hq x hx) (singleton_subset_iff.mpr hz))
    exact ⟨C, c1, c2 ▸ subset_union_left⟩
  have hA₁ : (Γ.V ∩ D₁).Finite := Γ.finite_V.subset inter_subset_left
  have hA₂ : (Γ.V ∩ D₂).Finite := Γ.finite_V.subset inter_subset_left
  obtain ⟨C₁, c1U, c1q⟩ := hcircle hE₁ hA₁ fun x hx => (hw₁ x hx).1
  obtain ⟨C₂, c2U, c2q⟩ := hcircle hE₂ hA₂ fun x hx => (hw₂ x hx).1
  have hc₁ : C₁.IsCircuit := isCircuit_of_isOArc_U (c1U.symm ▸ hE₁.isOArc_discBd)
  have hc₂ : C₂.IsCircuit := isCircuit_of_isOArc_U (c2U.symm ▸ hE₂.isOArc_discBd)
  have hE₁₁ : E₁ ⊆ D₁ := hE₁D.trans sdiff_subset
  have hE₂₂ : E₂ ⊆ D₂ := hE₂D.trans sdiff_subset
  have hΓE₁ : ∀ z ∈ Γ.U, z ∉ E₁ := fun z hz h => disjoint_left.mp hi₁ hz (hE₁D h)
  have hΓE₂ : ∀ z ∈ Γ.U, z ∉ E₂ := fun z hz h => disjoint_left.mp hi₂ hz (hE₂D h)
  have hC₁E : C₁.U ⊆ E₁ := c1U ▸ Surface.discBd_subset _
  have hC₂E : C₂.U ⊆ E₂ := c2U ▸ Surface.discBd_subset _
  have hEE : ∀ z, z ∈ E₁ → z ∈ E₂ → False := fun z h3 h4 => disjoint_left.mp hd (hE₁₁ h3) (hE₂₂ h4)
  have g1 : Γ.U ∩ C₁.U ⊆ Γ.V ∩ C₁.V := fun z hz => absurd (hC₁E hz.2) (hΓE₁ z hz.1)
  let G₁ := Γ.glue C₁ g1
  have g2 : G₁.U ∩ C₂.U ⊆ G₁.V ∩ C₂.V := by
    rintro z ⟨h3 | h3, h4⟩
    · exact absurd (hC₂E h4) (hΓE₂ z h3)
    · exact (hEE z (hC₁E h3) (hC₂E h4)).elim
  let G := G₁.glue C₂ g2
  let q : T → T := fun x => if x ∈ D₁ then q₁ x else q₂ x
  let ℓ : T → Set T := fun x => if x ∈ D₁ then ℓ₁ x else ℓ₂ x
  have hq1 : ∀ {x}, x ∈ D₁ → q x = q₁ x ∧ ℓ x = ℓ₁ x := fun {x} hx => by simp [q, ℓ, hx]
  have hq2 : ∀ {x}, x ∈ D₂ → q x = q₂ x ∧ ℓ x = ℓ₂ x := fun {x} hx => by
    have : x ∉ D₁ := fun h => disjoint_left.mp hd h hx
    simp [q, ℓ, this]
  have hGU : ∀ {z}, z ∈ G.U → z ∈ Γ.U ∨ z ∈ C₁.U ∨ z ∈ C₂.U := fun {z} hz => by
    rcases hz with (h | h) | h
    · exact .inl h
    · exact .inr (.inl h)
    · exact .inr (.inr h)
  have hcap1 : ∀ x ∈ Γ.V ∩ D₁, ℓ₁ x ∩ G.U ⊆ {x, q₁ x} := fun x hx z ⟨hz, hzG⟩ => by
    obtain ⟨-, -, -, h3, h4, h5⟩ := hw₁ x hx
    rcases hGU hzG with h | h | h
    · have hb : z ∈ discBd D₁ := by
        by_contra hn
        exact disjoint_left.mp hi₁ h ⟨h3 hz, hn⟩
      have : z ∈ ℓ₁ x ∩ discBd D₁ := ⟨hz, hb⟩
      rw [h4] at this
      exact .inl this
    · have : z ∈ ℓ₁ x ∩ E₁ := ⟨hz, hC₁E h⟩
      rw [h5] at this
      exact .inr this
    · exact (disjoint_left.mp hd (h3 hz) (hE₂₂ (hC₂E h))).elim
  have hcap2 : ∀ x ∈ Γ.V ∩ D₂, ℓ₂ x ∩ G.U ⊆ {x, q₂ x} := fun x hx z ⟨hz, hzG⟩ => by
    obtain ⟨-, -, -, h3, h4, h5⟩ := hw₂ x hx
    rcases hGU hzG with h | h | h
    · have hb : z ∈ discBd D₂ := by
        by_contra hn
        exact disjoint_left.mp hi₂ h ⟨h3 hz, hn⟩
      have : z ∈ ℓ₂ x ∩ discBd D₂ := ⟨hz, hb⟩
      rw [h4] at this
      exact .inl this
    · exact (disjoint_left.mp hd (hE₁₁ (hC₁E h)) (h3 hz)).elim
    · have : z ∈ ℓ₂ x ∩ E₂ := ⟨hz, hC₂E h⟩
      rw [h5] at this
      exact .inr this
  have hfin : (Γ.V ∩ (D₁ ∪ D₂)).Finite := Γ.finite_V.subset inter_subset_left
  have hdisj : ∀ x ∈ Γ.V ∩ (D₁ ∪ D₂), ∀ y ∈ Γ.V ∩ (D₁ ∪ D₂), x ≠ y → Disjoint (ℓ x) (ℓ y) := by
    rintro x ⟨hxV, hx | hx⟩ y ⟨hyV, hy | hy⟩ hne
    · rw [(hq1 hx).2, (hq1 hy).2]
      exact hd₁ x ⟨hxV, hx⟩ y ⟨hyV, hy⟩ hne
    · rw [(hq1 hx).2, (hq2 hy).2]
      exact hd.mono (hw₁ x ⟨hxV, hx⟩).2.2.2.1 (hw₂ y ⟨hyV, hy⟩).2.2.2.1
    · rw [(hq2 hx).2, (hq1 hy).2]
      exact hd.symm.mono (hw₂ x ⟨hxV, hx⟩).2.2.2.1 (hw₁ y ⟨hyV, hy⟩).2.2.2.1
    · rw [(hq2 hx).2, (hq2 hy).2]
      exact hd₂ x ⟨hxV, hx⟩ y ⟨hyV, hy⟩ hne
  have hq₁V : ∀ x ∈ Γ.V ∩ D₁, q x ∈ C₁.V := fun x hx => by
    rw [(hq1 hx.2).1]
    exact c1q ⟨x, hx, rfl⟩
  have hq₂V : ∀ x ∈ Γ.V ∩ D₂, q x ∈ C₂.V := fun x hx => by
    rw [(hq2 hx.2).1]
    exact c2q ⟨x, hx, rfl⟩
  have hl : ∀ x ∈ hfin.toFinset, IsLineWithEnds (ℓ x) (id x) (q x) ∧ id x ≠ q x ∧ id x ∈ G.V
    ∧ q x ∈ G.V ∧ ℓ x ∩ G.U ⊆ {id x, q x} := fun x hx => by
    rw [Finite.mem_toFinset] at hx
    obtain ⟨hxV, hx1 | hx2⟩ := hx
    · obtain ⟨-, h3, h4, -⟩ := hw₁ x ⟨hxV, hx1⟩
      have h5 := hq₁V x ⟨hxV, hx1⟩
      rw [(hq1 hx1).1, (hq1 hx1).2] at *
      exact ⟨h3, h4, .inl (.inl hxV), .inl (.inr h5), hcap1 x ⟨hxV, hx1⟩⟩
    · obtain ⟨-, h3, h4, -⟩ := hw₂ x ⟨hxV, hx2⟩
      have h5 := hq₂V x ⟨hxV, hx2⟩
      rw [(hq2 hx2).1, (hq2 hx2).2] at *
      exact ⟨h3, h4, .inl (.inl hxV), .inr h5, hcap2 x ⟨hxV, hx2⟩⟩
  obtain ⟨H, hHU, hHV, hHE⟩ := exists_add_lines G hfin.toFinset ℓ id q hl (fun x hx y hy hne
    => hdisj x (hfin.mem_toFinset.mp hx) y (hfin.mem_toFinset.mp hy) hne)
  have hGE : G.E = Γ.E ∪ C₁.E ∪ C₂.E := by
    rw [Drawing.glue_E, Drawing.glue_E]
  have hEsub : G.E ⊆ H.E := hHE ▸ subset_union_left
  refine ⟨H, C₁, C₂, E₁, E₂, q, ℓ, ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩, hc₁, hc₂, hE₁, hE₂, hE₁D, hE₂D,
    c1U.symm, c2U.symm, hHV, ?_, ?_, hq₁V, hq₂V, ?_, ?_, ?_, hdisj⟩⟩
  · exact fun x hx => hHV ▸ .inl (.inl hx)
  · exact fun e he => hEsub (hGE ▸ .inl (.inl he))
  · exact fun x hx => hHV ▸ .inl (.inr hx)
  · exact fun e he => hEsub (hGE ▸ .inl (.inr he))
  · exact fun x hx => hHV ▸ .inr hx
  · exact fun e he => hEsub (hGE ▸ .inr he)
  · rw [hHU]
    simp only [Finite.mem_toFinset]
    rfl
  · intro e he
    rw [hHE, hGE] at he
    rcases he with ((h | h) | h) | ⟨x, hx, rfl⟩
    · exact .inl h
    · exact .inr (.inl h)
    · exact .inr (.inr (.inl h))
    · exact .inr (.inr (.inr ⟨x, hfin.mem_toFinset.mp hx, rfl⟩))
  · intro x hx
    obtain ⟨h3, h4, -⟩ := hl x (hfin.mem_toFinset.mpr hx)
    refine ⟨h3, h4, ?_⟩
    rw [hHE]
    exact .inr ⟨x, hfin.mem_toFinset.mpr hx, rfl⟩
  · intro x hx
    rw [(hq1 hx.2).1, (hq1 hx.2).2]
    exact (hw₁ x hx).2.2.2
  · intro x hx
    rw [(hq2 hx.2).1, (hq2 hx.2).2]
    exact (hw₂ x hx).2.2.2

end GraphMinor.GM07
